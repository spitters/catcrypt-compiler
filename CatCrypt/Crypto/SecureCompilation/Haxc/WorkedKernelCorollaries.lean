/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCInstance
public import CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect
public import CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality

@[expose] public section

set_option autoImplicit false

/-!
# The constant-time theorems of `compileA` on `mpn_and_n` and `ltu`

Instances of the constant-time and robust-compilation theorems of `compileA`
(`haxc_rc_proved_all`, `haxc_correct_auto_ct_proved_all`) on two limb kernels of the
`mpn-hax` crate: the looped `mpn_and_n` under the layout `andAbi4` and the straight-line
comparison `ltu` under the layout `ltuAbi`. The run hypotheses are `CTTotality.and_hterm` and
`CTTotality.ltu_hterm`.

## Main definitions

* `AndNCorrect.andSecrecy` — the secrecy record of `mpn_and_n`.
* `LtuCorrect.ltuSecrecy` — the secrecy record of `ltu`.

## Main results

* `AndNCorrect.mpn_and_n_rc_proved`, `LtuCorrect.ltu_rc_proved` — robust compilation on
  `mpn_and_n` and on `ltu`.
* `AndNCorrect.mpn_and_n_correct_auto_ct_regions` — the joint value and constant-time
  theorem on `mpn_and_n`.
-/

/-! ## 1. `mpn_and_n` -/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.RCGate
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality (and_hterm)

/-- The secrecy record of `mpn_and_n`: the count `n` public, the three arrays secret. -/
def andSecrecy : _root_.Hax.FnSecrecy where
  fn := "mpn_and_n"
  params := [("rp", .secret), ("up", .secret), ("vp", .secret), ("n", .pub)]
  ret := .secret

/-- The secrecy record of `mpn_and_n` marks public only the count, which `andAbi4` bounds. -/
theorem and_pubLabelsB : pubLabelsB andSecrecy andAbi4 = true := by decide

/-- The names of `andAbi4` are pairwise distinct. -/
theorem and_envNames_nodup : andAbi4.envNames.Nodup := by decide

/-- **Robust compilation on `mpn_and_n` from the proved chain**: `haxc_rc_proved_all` for
    `compileA` on `mpn_and_n` under `andAbi4` at the secrecy record `andSecrecy`, with the
    run hypothesis `and_hterm` at the fuel `4`. -/
theorem mpn_and_n_rc_proved (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA Mpn.mpn_and_n_texpr andAbi4 "mpn_and_n" = some (P, bytes))
    (hck : haxToNFCTB andSecrecy andAbi4 Mpn.mpn_and_n_texpr = true)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    GateConclusion andAbi4.Regions andAbi4.PubAgree (haxcSrcRun Mpn.mpn_and_n_texpr andAbi4)
        (haxcTgtRes andAbi4 prog) (haxcLeakRun prog) ∧
      RobustCompilation 0
        (realObs (Pre := andAbi4.Regions) (srcRun := haxcSrcRun Mpn.mpn_and_n_texpr andAbi4)
          (leakRun := haxcLeakRun prog) (haxcTgtRes andAbi4 prog))
        (idealObs (pubOf andAbi4)) :=
  haxc_rc_proved_all andSecrecy Mpn.mpn_and_n_texpr andAbi4 "mpn_and_n" P bytes hc
    (haxToNFCTBL_of_haxToNFCTB rfl hck) 4 0
    (by
      rw [CatCrypt.Crypto.Hax.HaxModule.linkTable_of_linked_nil
        ((pairStage_linked _ _).trans rfl)]
      exact fun sa V hR hV => and_hterm (fun _ => True) 0 le_rfl sa V hR trivial hV)
    (pubLabelsOK_of_pubLabelsB and_pubLabelsB) and_envNames_nodup hd

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts) in
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL) in
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine) in
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState) in
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel) in
open _root_.Hax (Value Env) in
open _root_.Hax.InlineLocalClosures (denoteSpine) in
open CatCrypt.Crypto.Hax (hax64WExit) in
/-- **The joint value and constant-time theorem at `mpn_and_n`, for every run from a
    separated entry state, from the proved chain**: `haxc_correct_auto_ct_proved_all` for
    `compileA` on `mpn_and_n` under `andAbi4` at the secrecy record `andSecrecy`. Any two
    runs of the decoded program from entry states satisfying `andAbi4.Regions` and agreeing
    on `%rsp`, the three array pointers and the count, from the first of which `mpn_and_n`
    has a source run, have equal leakage traces. The run hypothesis is `and_hterm` at the
    fuel `4`. -/
theorem mpn_and_n_correct_auto_ct_regions (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA Mpn.mpn_and_n_texpr andAbi4 "mpn_and_n" = some (P, bytes))
    (hck : haxToNFCTB andSecrecy andAbi4 Mpn.mpn_and_n_texpr = true)
    (sa : AState) (hsep : andAbi4.Regions sa) (env : Env) (henv : andAbi4.EnvOf sa env)
    (fuel : Nat) (v : Value) (env' : Env)
    (hrun : (denoteSpine hax64WExit fuel Mpn.mpn_and_n_texpr.erase).run env = (.val v, env')) :
    ∃ prog, decodeLprog bytes = some prog
      ∧ (∃ sa', Halts aMachine prog 0 sa sa' ∧ andAbi4.ResultOf sa sa' v)
      ∧ ConstantTimeRel
          (fun s₁ s₂ => andAbi4.PubAgree s₁ s₂ ∧ andAbi4.Regions s₁ ∧ andAbi4.Regions s₂
            ∧ ∃ v, haxRuns andAbi4 Mpn.mpn_and_n_texpr s₁ v)
          (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  obtain ⟨prog, hd, hval, hct⟩ := haxc_correct_auto_ct_proved_all andSecrecy
    Mpn.mpn_and_n_texpr andAbi4 "mpn_and_n" P bytes hc (haxToNFCTBL_of_haxToNFCTB rfl hck) 4 0
    (fun _ => True)
    (by
      rw [CatCrypt.Crypto.Hax.HaxModule.linkTable_of_linked_nil
        ((pairStage_linked _ _).trans rfl)]
      exact and_hterm (fun _ => True) 0 le_rfl)
    (pubLabelsOK_of_pubLabelsB and_pubLabelsB) and_envNames_nodup sa hsep v
    ((haxRuns_single andAbi4 Mpn.mpn_and_n_texpr sa v).mpr ⟨env, fuel, env', henv, hrun,
      isControlFlow_false_of_wordResult
        (.inl (by rw [and_bindConsts]; exact and_wordArrResult)) hsep henv hrun⟩)
  exact ⟨prog, hd, hval, fun s₁ s₂ t₁ t₂ h h₁ h₂ =>
    hct s₁ s₂ t₁ t₂ ⟨h.1, h.2.1, h.2.2.1, trivial, trivial, h.2.2.2, .inl rfl⟩ h₁ h₂⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect

/-! ## 2. `ltu` -/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.RCGate
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)

/-- The secrecy record of `ltu`: both operands and the result secret. -/
def ltuSecrecy : _root_.Hax.FnSecrecy where
  fn := "ltu"
  params := [("x", .secret), ("y", .secret)]
  ret := .secret

/-- The secrecy record of `ltu` marks no parameter public. -/
theorem ltu_pubLabelsB : pubLabelsB ltuSecrecy ltuAbi = true := by decide

/-- The names of `ltuAbi` are pairwise distinct. -/
theorem ltu_envNames_nodup : ltuAbi.envNames.Nodup := by decide

/-- **Robust compilation on `ltu` from the proved chain**: `haxc_rc_proved_all` for
    `compileA` on `ltu` under `ltuAbi` at the secrecy record `ltuSecrecy`, with the run
    hypothesis `ltu_hterm`. -/
theorem ltu_rc_proved (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA Mpn.ltu_texpr ltuAbi "ltu" = some (P, bytes))
    (hck : haxToNFCTB ltuSecrecy ltuAbi Mpn.ltu_texpr = true)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    GateConclusion ltuAbi.Regions ltuAbi.PubAgree (haxcSrcRun Mpn.ltu_texpr ltuAbi)
        (haxcTgtRes ltuAbi prog) (haxcLeakRun prog) ∧
      RobustCompilation 0
        (realObs (Pre := ltuAbi.Regions) (srcRun := haxcSrcRun Mpn.ltu_texpr ltuAbi)
          (leakRun := haxcLeakRun prog) (haxcTgtRes ltuAbi prog))
        (idealObs (pubOf ltuAbi)) :=
  haxc_rc_proved_all ltuSecrecy Mpn.ltu_texpr ltuAbi "ltu" P bytes hc
    (haxToNFCTBL_of_haxToNFCTB rfl hck) 0 0
    (by
      rw [CatCrypt.Crypto.Hax.HaxModule.linkTable_of_linked_nil
        ((pairStage_linked _ _).trans rfl)]
      exact fun sa V hR hV => CTTotality.ltu_hterm (fun _ => True) 0 0 sa V hR trivial hV)
    (pubLabelsOK_of_pubLabelsB ltu_pubLabelsB) ltu_envNames_nodup hd

end CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect
