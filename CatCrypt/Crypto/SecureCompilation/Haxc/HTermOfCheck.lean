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
# The run hypothesis from the totality check, on call-free modules

The joint theorems of value correctness, constant time and robust compilation
(`haxc_correct_auto_ct_proved_all`, `haxc_gate_proved_all`, `haxc_rc_proved_all`) take the
run hypothesis `hterm`: the body the front prepares runs to a value from the entry
environment of every valuation the layout reads off an entry state. On a module without
functions and without linked functions this module derives `hterm` from the totality checker
`Hax.Total.KindSig.check` at the kind signature `CTTotality.wKindSig` of word programs and a
kind context read off the layout alone: each scalar parameter is a word and each array
parameter of `n` words an array of `n` words (`abiKindCtx`). The checker accepts straight-line
bodies and counted loops whose trip count has a range in the context, and returns a fuel
bound; the joint theorems hold at that fuel. Every entry environment is in the kinds of the
context whatever the entry state (`envOK_abiKindCtx`), so no condition on the entry state is
needed.

## Main definitions

* `wKindOfArg`, `abiKindCtx` — the kinds of the parameters of a layout.

## Main results

* `envOK_abiKindCtx` — the entry environment of every valuation is in the kinds of the
  layout.
* `hterm_of_wKindCheck` — the run hypothesis from the checker, on a call-free module.
* `haxc_rc_proved_all_of_check`, `haxc_correct_auto_ct_proved_all_of_check` — the joint
  theorems with `hterm` discharged by the checker.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.HTermOfCheck

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.RCGate
open CatCrypt.Crypto.SecureCompilation.VIR (Ctxt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnvOf crateBi enc)
open _root_.Hax (Value Env denote')
open _root_.Hax.Total (KindSig)
open CatCrypt.Crypto.Hax (hax64WExit HaxModule)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower (mapLabels)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)

/-- The kind of a parameter: a scalar is a word, an array of `n` words an array of `n`
    words. -/
def wKindOfArg : ArgKind → WKind
  | .scalar => .word
  | .words n => .arr n

/-- The kinds of the parameters of a layout, in the order of `abiEntry`. -/
def abiKindCtx (σ : AbiLayout) : List (String × WKind) :=
  (σ.args.map fun a => (a.name, wKindOfArg a.kind)).reverse

/-- The encoding of a value of the type of a parameter is of the kind of the parameter. -/
theorem wOfKind_enc (k : ArgKind) (y : (abiKindArr k).denote) :
    wOfKind (wKindOfArg k) (enc (abiKindArr k) y) := by
  cases k with
  | scalar => exact wOfKind_bv y
  | words n =>
      have := wOfKind_arr (n := n) y
      simpa [enc, abiKindArr, wKindOfArg, Function.comp_def] using this

theorem envOK_map : ∀ (q : List AbiArg)
    (V : Ctxt.Valuation (entryCtx (q.map fun a => (a.name, abiKindArr a.kind)))),
    KindSig.EnvOK wOfKind (q.map fun a => (a.name, wKindOfArg a.kind))
      (entryEnvOf (q.map fun a => (a.name, abiKindArr a.kind)) V)
  | [], _ => by
      intro x k hx
      simp at hx
  | a :: q, .cons y V =>
      KindSig.envOK_extend (envOK_map q V) (wOfKind_enc a.kind y)

/-- **The entry environment of every valuation is in the kinds of the layout.** -/
theorem envOK_abiKindCtx (σ : AbiLayout) (V : Ctxt.Valuation (entryCtx (abiEntry σ))) :
    KindSig.EnvOK wOfKind (abiKindCtx σ) (entryEnvOf (abiEntry σ) V) := by
  have e1 : abiEntry σ = σ.args.reverse.map fun a => (a.name, abiKindArr a.kind) := by
    simp [abiEntry, abiParamsArr, List.map_reverse]
  have e2 : abiKindCtx σ = σ.args.reverse.map fun a => (a.name, wKindOfArg a.kind) := by
    simp [abiKindCtx, List.map_reverse]
  rw [e2]
  revert V
  rw [e1]
  exact envOK_map σ.args.reverse

/-- **The run hypothesis from the totality check, on a call-free module.** On a module
    `m` without functions and without linked functions, when the checker accepts the body
    the front prepares at the kinds of the layout `σ` with the fuel bound `f`, the body runs
    to a value at every fuel `F ≥ f` and every callee fuel, from the entry environment of
    every valuation. -/
theorem hterm_of_wKindCheck {m : HaxModule} {σ : AbiLayout} (hfns : m.fns = [])
    (hlk : m.linked = []) {ko : Option WKind} {f F : Nat}
    (hc : wKindSig.check (abiKindCtx σ) (nfBody (bindConsts σ.consts m.entry)) = some (ko, f))
    (hF : f ≤ F) (fuelC : Nat) (V : Ctxt.Valuation (entryCtx (abiEntry σ))) :
    ∃ v env', (denote' (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth) F
      (nfBody (bindConsts σ.consts m.entry))).run (entryEnvOf (abiEntry σ) V) = (.val v, env') := by
  rw [crateBi_prepared_of_fns_nil hfns, HaxModule.linkTable_of_linked_nil hlk]
  exact KindSig.denote'_run_val_of_check wKindSig_sound hc hF (envOK_abiKindCtx σ V)

/-- **Robust compilation on a call-free module, with the run hypothesis from the checker.**
    `haxc_gate_proved_all` and `haxc_rc_proved_all` at the fuel bound `f` of the checker,
    whose acceptance of the prepared body of the pair stage at the kinds of its layout
    (`abiKindCtx`) replaces the run hypothesis `hterm`, on a pair stage without functions and
    without linked functions. -/
theorem haxc_rc_proved_all_of_check (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : (pairStage m σ).1.fns = []) (hlk : (pairStage m σ).1.linked = [])
    {ko : Option WKind} {f : Nat}
    (hchk : wKindSig.check (abiKindCtx (pairStage m σ).2)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, f))
    (fuelC : Nat)
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    GateConclusion σ.Regions σ.PubAgree (haxcSrcRun m σ) (haxcTgtRes σ prog)
        (haxcLeakRun prog) ∧
      RobustCompilation 0
        (realObs (Pre := σ.Regions) (srcRun := haxcSrcRun m σ) (leakRun := haxcLeakRun prog)
          (haxcTgtRes σ prog))
        (idealObs (pubOf σ)) :=
  haxc_rc_proved_all s m σ fname P bytes hc hck f fuelC
    (fun _ V _ _ => hterm_of_wKindCheck hfns hlk hchk le_rfl fuelC V) hL hnds hd hnd hk

/-- **The joint value and constant-time theorem on a call-free module, with the run
    hypothesis from the checker.** `haxc_correct_auto_ct_proved_all` at the fuel bound `f` of
    the checker, at every precondition `Pre`, on a pair stage without functions and without
    linked functions whose prepared body the checker accepts at the kinds of its layout. -/
theorem haxc_correct_auto_ct_proved_all_of_check (s : _root_.Hax.FnSecrecy) (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : (pairStage m σ).1.fns = []) (hlk : (pairStage m σ).1.linked = [])
    {ko : Option WKind} {f : Nat}
    (hchk : wKindSig.check (abiKindCtx (pairStage m σ).2)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, f))
    (fuelC : Nat) (Pre : AState → Prop)
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup)
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : haxRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog
      ∧ (∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
      ∧ ConstantTimeRel
          (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ Pre s₁ ∧ Pre s₂
            ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
          (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  haxc_correct_auto_ct_proved_all s m σ fname P bytes hc hck f fuelC Pre
    (fun _ V _ _ _ => hterm_of_wKindCheck hfns hlk hchk le_rfl fuelC V) hL hnds sa hsep v hrun
    hnd hk

end CatCrypt.Crypto.SecureCompilation.Haxc.HTermOfCheck
