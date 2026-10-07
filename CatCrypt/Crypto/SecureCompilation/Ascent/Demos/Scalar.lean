/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed-kernel weld reduces the front (`translateDialectControl`,
-- `semScalar`) by `rfl`/`decide`; under the module system that reduction needs
-- the front closure imported with `all`, and `Nat.repr` (the front's slot
-- names) exposed through `Init.Data.Repr`.
import all Init.Data.Repr
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCTSyntax
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public import CatCrypt.Crypto.SecureCompilation.Ascent.RotateLeaf
public import CatCrypt.Crypto.Jasmin.LowCTNotation

/-!
# Demo: `corres_solve_scalar` over straight-line `LowCT` word kernels

Route: a straight-line `RSeq` / `RScalarSetExpr` kernel run by `semScalar`
refines the left fold of its per-statement `wordStep`s through the identity
`BitVec 64` relation `SRwordBV` (`Corres`). `corres_solve_scalar` walks the
tree, applies `corres_setExprWord` at each leaf and discharges the `srcClean`
side conditions. A fixed-count rotate enters as the derived leaf `corres_rotl`,
sequenced by `corres_seq`.

Tactic: `corres_solve_scalar` (`Ascent/CorresScalar.lean`); leaf `corres_rotl`
(`Ascent/RotateLeaf.lean`).

## Main results

* `qrFrag_refines`: a quarter-round fragment (`a += b; d ^= a; d <<= 16`)
  refines its `wordStep` fold under `SRwordBV`.
* `xor_rotl_refines`: an xor followed by a fixed-count rotate refines the
  sequenced `wordStep` and `rotlWord` steps.
* `qrClosed_frontDenote`: the fragment behind three literal writes, front-compiled
  from `VarMap.empty`, denotes the `Corres` fold at `d` — the weld
  `corresScalar_frontDenote_two` on a closed kernel, with the front run at the
  empty environment and the `Corres` result at a zero-word environment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-- A ChaCha-style quarter-round fragment: `a := a + b; d := d ^^^ a; d := d <<< 16`. -/
def qrFrag : LowCT := lowct% a := a + b; d := d ^ a; d := d << 16

/-- The fragment refines the fold of its three `wordStep`s, in program order. -/
theorem qrFrag_refines :
    Corres SRwordBV (fun _ => True)
      (fun a => wordStep (.RScalarSetExpr "d" (.SShl (.SVar "d") (.SLit 16)))
        (wordStep (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
          (wordStep (.RScalarSetExpr "a" (.SAdd (.SVar "a") (.SVar "b"))) a)))
      qrFrag := by
  unfold qrFrag
  corres_solve_scalar

/-- A mix followed by a rotate: `d := d ^^^ a`, then the three-statement chain
    `rotlProg` that rotates `d` left by 16 through the scratch slots `lo`, `hi`.
    The xor leaf comes from `corres_setExprWord`, the rotate from `corres_rotl`,
    sequenced by `corres_seq`; the destination holds `rotlWord (d ^^^ a) 16`. -/
theorem xor_rotl_refines :
    Corres SRwordBV (fun _ => True)
      (fun a =>
        (fun (a : String → BitVec 64) s =>
          if s = "d" then rotlWord (a "d") 16
          else if s = "hi" then (a "d") >>> (64 - 16)
          else if s = "lo" then (a "d") <<< 16
          else a s)
        ((fun (a : String → BitVec 64) s =>
          if s = "d" then SExpr.evalBV a (.SXor (.SVar "d") (.SVar "a")) else a s) a))
      (.RSeq (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
        (rotlProg "d" "lo" "hi" "d" 16)) :=
  corres_seq SRwordBV
    (corres_setExprWord "d" (.SXor (.SVar "d") (.SVar "a"))
      ⟨notTmp_of_short "d" (by decide), notTmp_of_short "a" (by decide)⟩)
    (corres_rotl "d" "lo" "hi" "d" 16 (by decide)
      (notTmp_of_short "d" (by decide)) (notTmp_of_short "lo" (by decide))
      (notTmp_of_short "hi" (by decide)) (by decide) (by decide))
    (fun _ _ => trivial)

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.qrFrag_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qrFrag_refines
/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.xor_rotl_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xor_rotl_refines

/-! ## The weld on a closed kernel

`qrClosed` writes `a := 1; b := 2; d := 5` as literals and then runs `qrFrag`.
It is closed, so `semScalar` runs it from the empty environment, which is the
entry `translateDialectControl VarMap.empty` is consistent with
(`consistentS_empty`), and its output word at `d` is the same from any entry
environment. The `Corres` result runs at the zero-word environment `qrEntry`;
the agreement `qrHAgree` between the two runs is decided. -/

/-- The quarter-round fragment behind three literal writes. -/
def qrClosed : LowCT := lowct% a := lit 1; b := lit 2; d := lit 5; ↑qrFrag

theorem qrFrag_coveredS : IsCoveredS qrFrag :=
  .rSeq (.rScalarSetExpr _ _ ⟨notTmp_of_short "a" (by decide), notTmp_of_short "b" (by decide)⟩)
    (.rSeq (.rScalarSetExpr _ _ ⟨notTmp_of_short "d" (by decide), notTmp_of_short "a" (by decide)⟩)
      (.rScalarSetExpr _ _ ⟨notTmp_of_short "d" (by decide), (by decide : (16 : Nat) < 2 ^ 64)⟩))

theorem qrClosed_covered : IsCoveredSCtl qrClosed :=
  .ofStraight (.rSeq (.rScalarSet "a" 1)
    (.rSeq (.rScalarSet "b" 2) (.rSeq (.rScalarSet "d" 5) qrFrag_coveredS)))

/-- The abstract step of `qrClosed`: the three literal writes, then the
    `qrFrag` fold. -/
def qrFa : (String → BitVec 64) → (String → BitVec 64) := fun a =>
  (fun a =>
    (fun a =>
      (fun a => wordStep (.RScalarSetExpr "d" (.SShl (.SVar "d") (.SLit 16)))
        (wordStep (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
          (wordStep (.RScalarSetExpr "a" (.SAdd (.SVar "a") (.SVar "b"))) a)))
      ((fun a s => if s = "d" then BitVec.ofNat 64 5 else a s) a))
    ((fun a s => if s = "b" then BitVec.ofNat 64 2 else a s) a))
  ((fun a s => if s = "a" then BitVec.ofNat 64 1 else a s) a)

theorem qrClosed_corres : Corres SRwordBV (fun _ => True) qrFa qrClosed := by
  have h := corres_seq SRwordBV (corres_setScalar_BV "a" 1)
    (corres_seq SRwordBV (corres_setScalar_BV "b" 2)
      (corres_seq SRwordBV (corres_setScalar_BV "d" 5) qrFrag_refines (fun _ _ => trivial))
      (fun _ _ => trivial))
    (fun _ _ => trivial)
  exact h

/-! ### Front translation, semantics, output tracking -/

theorem qrTransSome : (translateDialectControl VarMap.empty qrClosed).isSome := by rfl

noncomputable def qrO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty qrClosed).get qrTransSome

theorem qrHTrans : translateDialectControl VarMap.empty qrClosed = some qrO :=
  (Option.some_get qrTransSome).symm

theorem qrSemSome : (semScalar qrClosed (fun _ => none)).isSome := by rfl

/-- The environment `semScalar` leaves from the empty entry. -/
noncomputable def qrEnv : SEnvScalar := (semScalar qrClosed (fun _ => none)).get qrSemSome

theorem qrHSem : semScalar qrClosed (fun _ => none) = some qrEnv :=
  (Option.some_get qrSemSome).symm

theorem qrNameSome : (qrO.vm.lookup "d").isSome := by rfl

theorem qrNameTy : ((qrO.vm.lookup "d").get qrNameSome).1 = .sword 64 := by decide

/-- The tracked output slot for `d`. -/
noncomputable def qrW : CVar qrO.Γ' (.sword 64) :=
  cast (congrArg (CVar qrO.Γ') qrNameTy) ((qrO.vm.lookup "d").get qrNameSome).2

theorem qrHName : qrO.vm.lookup "d" = some ⟨.sword 64, qrW⟩ := by decide

theorem qrValSome : (qrEnv "d").isSome := by rfl

theorem qrValTy : ((qrEnv "d").get qrValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `d` from the empty entry. -/
noncomputable def qrVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote qrValTy) ((qrEnv "d").get qrValSome).2

theorem qrHVal : qrEnv "d" = some ⟨.sword 64, qrVal⟩ :=
  envSlot_eq_some_sword _ _ qrValSome qrValTy qrVal rfl

theorem qrRetSome : (qrO.cont (Com.ret (toVIRVar qrW))).isSome := by rfl

/-- The front prefix closed by returning the `d` slot. -/
noncomputable def qrCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (qrO.cont (Com.ret (toVIRVar qrW))).get qrRetSome

theorem qrHRet : qrO.cont (Com.ret (toVIRVar qrW)) = some qrCom :=
  (Option.some_get qrRetSome).symm

/-! ### The `Corres` entry and the agreement between the two runs -/

/-- The zero-word entry environment of the `Corres` run. -/
def qrEntry : SEnvScalar := fun _ => some ⟨.sword 64, (0 : BitVec 64)⟩

theorem qrEntry_SR : SRwordBV qrEntry (fun _ => 0) := fun _ _ => rfl

theorem qrEntrySemSome : (semScalar qrClosed qrEntry).isSome := by rfl

/-- The `Corres` run from the zero-word entry leaves the same word at `d` as the
    run from the empty entry: the kernel is closed. -/
theorem qrHAgree : ∀ e, semScalar qrClosed qrEntry = some e → e "d" = some ⟨.sword 64, qrVal⟩ := by
  intro e he
  rw [← Option.some_get qrEntrySemSome] at he
  obtain rfl := Option.some.inj he
  exact envSlot_eq_some_sword _ _ (by decide) (by decide) qrVal (by decide)

/-! ### The weld -/

/-- The front-compiled closed kernel, from `VarMap.empty` at the empty
    valuation, denotes the `Corres` fold `qrFa` at `d` from the zero abstract
    state. -/
theorem qrClosed_frontDenote : qrCom.denote .nil = qrFa (fun _ => 0) "d" :=
  corresScalar_frontDenote_two qrClosed_covered qrClosed_corres VarMap.empty .nil
    (fun _ => none) qrEnv consistentS_empty qrHSem qrEntry (fun _ => 0) qrEntry_SR
    "d" (notTmp_of_short "d" (by decide)) qrVal qrHVal qrHAgree
    qrO qrHTrans qrW qrHName qrCom qrHRet

/-- The fold at `d` evaluates to `(5 ^^^ (1 + 2)) <<< 16`. -/
theorem qrClosed_frontDenote_val : qrCom.denote .nil = 393216#64 := by
  rw [qrClosed_frontDenote]
  exact (by decide : qrFa (fun _ => 0) "d" = 393216#64)

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.qrClosed_frontDenote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qrClosed_frontDenote
/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.qrClosed_frontDenote_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qrClosed_frontDenote_val
end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
