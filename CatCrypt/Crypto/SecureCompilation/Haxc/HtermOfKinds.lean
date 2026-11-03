/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality
public import CatCrypt.Crypto.SecureCompilation.Haxc.RCInstance

@[expose] public section

set_option autoImplicit false

/-!
# The run hypothesis of the joint theorems from the kind checker

The joint theorems `haxc_gate_proved_all`, `haxc_rc_proved_all` (`Haxc/RCInstance.lean`) and
`haxc_correct_auto_ct_proved_all` (`Haxc/ComposeCTStraight.lean`) take the run hypothesis
`hterm`: the body the front reads runs to a value from the entry environment of every
valuation the layout reads off an entry state. This module derives it, for a module without
callees and without linked functions, from one run of the kind checker
`Hax.Total.KindSig.check` at the signature `CTTotality.wKindSig` of `u64` word programs, in the
context `entryKinds σ` that gives each scalar parameter the word kind and each array
parameter of `n` words the array kind of `n` words. The checker accepts straight-line word
code and loops whose bounds it reads as ranges (literal bounds, or ranges the code computes
from literals), and returns a fuel bound; the run hypothesis then holds at every fuel at
least that bound. A loop whose bound is a scalar parameter needs the range of that
parameter, which the word kind does not give; it is not covered here.

The proof is `KindSig.denote'_run_val_of_check` with the soundness `CTTotality.wKindSig_sound`
and the fact that every entry environment binds each parameter to a value of its kind
(`envOK_entryEnvOf`), which holds for every valuation, so neither the regions condition nor
the reading of the entry state is used.

## Main definitions

* `nfWKind`, `entryKinds` — the kind of a parameter type, and the kinds of the parameters of
  the entry of a layout.

## Main results

* `envOK_entryEnvOf` — the entry environment of every valuation binds the parameters at
  their kinds.
* `run_val_of_check` — the run hypothesis from the checker, at every fuel at least its bound.
* `haxc_gate_proved_all_of_check`, `haxc_rc_proved_all_of_check`,
  `haxc_correct_auto_ct_proved_all_of_check` — the joint theorems with `hterm` replaced by
  the checker run, at a module without callees and linked functions.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality (WKind wKindSig wOfKind wKindSig_sound
  wOfKind_bv wOfKind_arr)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.CT
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnvOf crateBi)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.RCGate
open _root_.Hax (Value denote')
open _root_.Hax.Total (KindSig)
open CatCrypt.Crypto.Hax (HaxModule hax64WExit)

/-! ## The kinds of the entry parameters -/

/-- The kind of a parameter type: an array of `n` entries has the array kind of `n` words,
    every other type the word kind. -/
def nfWKind : NfTy → WKind
  | .arr n _ => .arr n
  | _ => .word

/-- The kinds of the parameters of the entry of the layout `σ`, in the order of the entry. -/
def entryKinds (σ : AbiLayout) : List (String × WKind) :=
  (abiEntry σ).map fun p => (p.1, nfWKind p.2)

/-- **The entry environment binds the parameters at their kinds**: for parameters of the types
    of System V parameters (`abiKindArr`), the environment `entryEnvOf ps V` of every
    valuation `V` binds each parameter to a value of its kind. -/
theorem envOK_entryEnvOf : ∀ (ps : List (String × NfTy)),
    (∀ p ∈ ps, ∃ k, p.2 = abiKindArr k) →
    ∀ V : Ctxt.Valuation (entryCtx ps),
      KindSig.EnvOK wOfKind (ps.map fun p => (p.1, nfWKind p.2)) (entryEnvOf ps V)
  | [], _, _ => fun _ _ h => by simp at h
  | (x, t) :: ps, h, .cons y V => by
      have ih := envOK_entryEnvOf ps (fun p hp => h p (List.mem_cons_of_mem _ hp)) V
      refine KindSig.envOK_extend ih ?_
      obtain ⟨_ | n, ht⟩ := h (x, t) List.mem_cons_self
      · subst ht
        exact wOfKind_bv y
      · subst ht
        exact wOfKind_arr y

/-! ## The run hypothesis -/

/-- **The run hypothesis from the kind checker.** Let the module `m` have no callee and no
    linked function, and let the checker at `wKindSig` accept the body the front reads in the
    context `entryKinds σ` with the fuel bound `B`. Then at every callee fuel and every fuel
    `F ≥ B`, the body runs to a value from the entry environment of every valuation of the
    parameters, at the builtins of the module. -/
theorem run_val_of_check {m : HaxModule} {σ : AbiLayout} (hfns : m.fns = [])
    (hlk : m.linked = []) {ko : Option WKind} {B : Nat}
    (hc : wKindSig.check (entryKinds σ) (nfBody (bindConsts σ.consts m.entry)) = some (ko, B))
    (fuelC : Nat) {F : Nat} (hF : B ≤ F) (V : Ctxt.Valuation (entryCtx (abiEntry σ))) :
    ∃ v env', (denote' (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth) F
      (nfBody (bindConsts σ.consts m.entry))).run (entryEnvOf (abiEntry σ) V) =
        (.val v, env') := by
  rw [crateBi_prepared_of_fns_nil hfns, HaxModule.linkTable_of_linked_nil hlk]
  exact KindSig.denote'_run_val_of_check wKindSig_sound hc hF
    (envOK_entryEnvOf _ (abiEntry_kinds σ) V)

/-! ## The joint theorems without `hterm` -/

/-- **The gate conclusion of `compileA` from the kind checker.** `haxc_gate_proved_all` at a
    module without callees and linked functions, with the run hypothesis `hterm` replaced by
    the run `hcheck` of the kind checker on the body of the pair stage. -/
theorem haxc_gate_proved_all_of_check (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : m.fns = []) (hlk : m.linked = []) {ko : Option WKind} {B : Nat}
    (hcheck : wKindSig.check (entryKinds (pairStage m σ).2)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, B))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
      (haxcLeakRun prog) :=
  haxc_gate_proved_all s m σ fname P bytes hc hck B 0
    (fun _ V _ _ => run_val_of_check
      (by unfold pairStage; split <;> exact hfns)
      ((pairStage_linked m σ).trans hlk) hcheck 0 le_rfl V)
    hL hnds hd (by simp [hlk]) (by simp [hlk]) (by simp [hlk])

/-- **Robust compilation for the hax compiler from the kind checker.** `haxc_rc_proved_all` at
    a module without callees and linked functions, with the run hypothesis `hterm` replaced
    by the run `hcheck` of the kind checker on the body of the pair stage. -/
theorem haxc_rc_proved_all_of_check (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : m.fns = []) (hlk : m.linked = []) {ko : Option WKind} {B : Nat}
    (hcheck : wKindSig.check (entryKinds (pairStage m σ).2)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, B))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
        (haxcLeakRun prog) ∧
      RobustCompilation 0
        (realObs (Pre := σ.Regions) (srcRun := haxcSrcRun m σ) (leakRun := haxcLeakRun prog)
          (haxcTgtRes σ prog))
        (idealObs (pubOf σ)) :=
  haxc_rc_proved_all s m σ fname P bytes hc hck B 0
    (fun _ V _ _ => run_val_of_check
      (by unfold pairStage; split <;> exact hfns)
      ((pairStage_linked m σ).trans hlk) hcheck 0 le_rfl V)
    hL hnds hd (by simp [hlk]) (by simp [hlk]) (by simp [hlk])

/-- **Value correctness and constant time of `compileA` from the kind checker.**
    `haxc_correct_auto_ct_proved_all` at a module without callees and linked functions, with
    the run hypothesis `hterm` replaced by the run `hcheck` of the kind checker on the body of
    the pair stage, at every precondition `Pre`. -/
theorem haxc_correct_auto_ct_proved_all_of_check (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : m.fns = []) (hlk : m.linked = []) {ko : Option WKind} {B : Nat}
    (hcheck : wKindSig.check (entryKinds (pairStage m σ).2)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, B))
    (Pre : AState → Prop)
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : haxRuns σ m sa v) :
    ∃ prog, decodeLprog bytes = some prog
      ∧ (∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
      ∧ ConstantTimeRel
          (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
            ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
          (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  haxc_correct_auto_ct_proved_all s m σ fname P bytes hc hck B 0 Pre
    (fun _ V _ _ _ => run_val_of_check
      (by unfold pairStage; split <;> exact hfns)
      ((pairStage_linked m σ).trans hlk) hcheck 0 le_rfl V)
    hL hnds sa hsep v hrun (by simp [hlk]) (by simp [hlk]) (by simp [hlk])

end CatCrypt.Crypto.SecureCompilation.Haxc
