/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain
public import CatCrypt.Crypto.Hax.LowCTToNF

/-!
# The scalar fragment of LowCT as an entry into `NFProg nfDialect`

`lowCTEntry N L` is the scalar fragment of `LowCT` as an `NFEntry`: its source programs are
pairs of a result name and a command, its translation is `lowCTToNF` at the parameters
`abiEntry σ` of the layout, and its soundness is `lowCTToNF_sim`.

A layout reads a LowCT state off an entry state through `AbiLayout.StateOf`: an environment
the layout reads off the entry state (`AbiLayout.EnvOf`) whose bindings are the integers of
the scalar heap. Every value such an environment binds is an integer, so `StateOf` holds
only at layouts whose parameters are scalars and whose constants are integers.

## Main definitions

* `AbiLayout.StateOf` — the scalar heap of a LowCT state holds the values a layout reads off
  an entry state.
* `lowCTRuns` — the source semantics: an in-range run of the command from a state the layout
  reads off the entry state, with the scalar of the result name as value.
* `lowCTEntry` — the entry.

## Main results

* `entryVals_of_le` — `EntryVals` is monotone in the source environment.
* `AbiLayout.StateOf.entryVals` — a state the layout reads off the entry state gives an
  environment and a valuation of the parameters that the environment and the scalar heap
  both hold.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.Hax.ImpToNF (enc PDenP entryCtx EntryVals EntryTyped entryVals_of_typed)
open CatCrypt.Crypto.Hax.LowCTToNF (stEnv StateVals RunInRange lowCTToNF lowCTToNF_sim)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open Ctxt (Var Valuation)
open _root_.Hax (Value Env Builtins)

/-! ## The layout reads a LowCT state -/

/-- `EntryVals` is monotone in the source environment: a valuation whose encodings `env`
    holds at the parameters is held by every environment that agrees with `env` where `env`
    is bound. -/
theorem entryVals_of_le {env env' : Env} (hle : ∀ x v, env x = some v → env' x = some v) :
    ∀ {ps : List (String × NfTy)} {V : Valuation (entryCtx ps)}, EntryVals env ps V →
      EntryVals env' ps V
  | [], _, _ => trivial
  | (_, _) :: _, .cons _ _, h => And.intro (hle _ _ h.1) (entryVals_of_le hle h.2)

/-- **The layout reads the LowCT state `rs` off the entry state `sa`**: an environment `σ`
    reads off `sa` binds every name to the integer of its scalar slot in `rs`. -/
def AbiLayout.StateOf (σ : AbiLayout) (sa : AState) (rs : RustState) : Prop :=
  ∃ env : Env, σ.EnvOf sa env ∧ ∀ x v, env x = some v → v = .int (rs.rsScalar x)

/-- A state the layout reads off the entry state gives an environment the layout reads off
    the entry state and a valuation of the parameters whose encodings the environment and
    the scalar heap of the state both hold. -/
theorem AbiLayout.StateOf.entryVals {σ : AbiLayout} {sa : AState} {rs : RustState}
    (h : σ.StateOf sa rs) :
    ∃ (env : Env) (V : Valuation (entryCtx (abiEntry σ))), σ.EnvOf sa env ∧
      EntryVals env (abiEntry σ) V ∧ StateVals rs (abiEntry σ) V := by
  obtain ⟨env, henv, hint⟩ := h
  obtain ⟨V, hV⟩ := entryVals_of_typed (entryTyped_abiEntry henv)
  exact ⟨env, V, henv, hV, entryVals_of_le (fun x v hx => by rw [stEnv, ← hint x v hx]) hV⟩

/-! ## The entry -/

/-- **The source semantics of the scalar fragment of LowCT** at the fuel `N` and the leaf
    specification `L`: the command `s.2` runs in range (`RunInRange`) from a state the
    layout reads off the entry state, and the value is the scalar of the result name `s.1`
    in the final state. -/
def lowCTRuns (N : Nat) (L : LeafSpec) (σ : AbiLayout) (s : String × LowCT) (sa : AState)
    (v : Value) : Prop :=
  ∃ rs rs' : RustState, σ.StateOf sa rs ∧ RustExec N L s.2 rs rs' ∧ RunInRange N L s.2 rs ∧
    v = .int (rs'.rsScalar s.1)

/-- **The scalar fragment of LowCT as an entry**: pairs of a result name and a command with
    the source semantics `lowCTRuns N L`, the translation `lowCTToNF` at the parameters of
    the layout, the table `hax64WExit` at every source program and fuel, no declared
    procedure, and the export names `nfAbiNames`. Its soundness is `lowCTToNF_sim` at the
    valuation of `AbiLayout.StateOf.entryVals`; the table answers the tagged field heads by
    their arms (`fieldCalls_hax64WExit`) and is the `u64` table at the wide tagged heads
    (`fieldCallsWideEq_hax64WExit`). -/
def lowCTEntry (N : Nat) (L : LeafSpec) : NFEntry where
  Src := String × LowCT
  Runs := lowCTRuns N L
  names := nfAbiNames
  toNF σ s := lowCTToNF (abiEntry σ) s.1 s.2
  bi _ _ := CatCrypt.Crypto.Hax.hax64WExit
  sound σ s q hq sa v _ hrun := by
    obtain ⟨rs, rs', hst, hex, hr, rfl⟩ := hrun
    obtain ⟨env, V, henv, hV, hrel⟩ := hst.entryVals
    obtain ⟨y, hp, hy⟩ := lowCTToNF_sim CatCrypt.Crypto.Hax.hax64WExit 0 hq hex hrel hr
    exact ⟨0, [], env, V, y, fun _ _ _ => rfl, CatCrypt.Crypto.Hax.hax64WExit_subTable,
      CatCrypt.Crypto.Hax.NFToCat.extAgree_nil _ _, henv, hV, ⟨0, le_rfl, hp⟩, hy.symm⟩
  fieldCalls _ _ _ _ _ := fieldCalls_hax64WExit
  fieldCallsWide _ _ _ _ _ := fieldCallsWideEq_hax64WExit

end CatCrypt.Crypto.SecureCompilation.Haxc
