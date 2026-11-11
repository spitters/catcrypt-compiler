/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCallShape

/-!
# The sum and the difference of the wide templates bind no high-word multiplication

The blocks of a wide template for the sum and the difference are the addition and the
subtraction blocks of the limb generators: a carry chain of `addCarryLo` and `addCarryHi`, a
trial addition or subtraction of the modulus held as register constants, and a select by the
final carry. None of them binds the high word `mulhi` of a widening multiplication. The
lowered body of a call of a tagged head of the sum or the difference, at a modulus without a
narrow representation and with a wide template, adds to that block only loads and stores at
constant indices and casts that are returns, so it binds no `mulhi` either.

## Main definitions

* `noMulhiB`: an operation that is not the high word of a widening multiplication.
* `AddSubOp`: a field expression of a sum or a difference.

## Main results

* `montAddBlk_hi`, `montSubBlk_hi`: the addition and the subtraction blocks bind no `mulhi`.
* `fieldBodyOf_hi`: the lowered field program over word arrays of a program of sums and
  differences binds no `mulhi`.
* `wideTemplateOf_addSub_hi`, `wideBlockOf_addSub_hi`: the blocks of the sum and the
  difference of a registered wide template bind no `mulhi`.
* `fieldBodyD_addSub_hi`: the lowered body of a tagged head of the sum or the difference at a
  modulus without a narrow representation and with a wide template binds no `mulhi`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom coveredCom_rename)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (CoveredM)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC bindK adcR selR xorR constsK addK)
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldInlineOps (allOps_ofCom)
open Ctxt (Var)

/-! ## 1. Operations other than the high word of a multiplication -/

/-- **An operation that is not the high word `mulhi` of a widening multiplication.** -/
def noMulhiB : JasminOp → Bool
  | .mulhi _ => false
  | _ => true

/-- The Jasmin expressions whose operation is not `mulhi`. -/
local notation "exprHi" => fun e => noMulhiB (Expr.op e) = true

/-! ## 2. The limb generators -/

section Gen

theorem bindK_hi {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (he : noMulhiB e.op = true)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ t → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (x : Var Δ t),
      CoveredM exprHi (k r x)) :
    CoveredM exprHi (bindK e k) :=
  ⟨he, hk _ _⟩

theorem adcR_hi : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (xs ys : List (Var Γ w64)) (c : Var Δ w1)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out c',
      CoveredM exprHi (k r out c')) →
      CoveredM exprHi (adcR ren xs ys c k)
  | _, _, _, _, _ :: xs, _ :: ys, _, _, hk => by
      rw [adcR]
      exact bindK_hi _ rfl fun _ _ => bindK_hi _ rfl fun _ _ =>
        adcR_hi _ xs ys _ fun _ _ _ => hk _ _ _
  | _, _, _, _, [], _, _, _, hk => by rw [adcR]; exact hk _ _ _
  | _, _, _, _, _ :: _, [], _, _, hk => by rw [adcR]; exact hk _ _ _

theorem selR_hi : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (c : Var Δ w1) (xs ys : List (Var Γ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out,
      CoveredM exprHi (k r out)) →
      CoveredM exprHi (selR ren c xs ys k)
  | _, _, _, _, _, _ :: xs, _ :: ys, _, hk => by
      rw [selR]
      exact bindK_hi _ rfl fun _ _ => selR_hi _ _ xs ys fun _ _ => hk _ _
  | _, _, _, _, _, [], _, _, hk => by rw [selR]; exact hk _ _
  | _, _, _, _, _, _ :: _, [], _, hk => by rw [selR]; exact hk _ _

theorem xorR_hi : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (m : Var Δ w64) (xs : List (Var Γ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out,
      CoveredM exprHi (k r out)) →
      CoveredM exprHi (xorR ren m xs k)
  | _, _, _, _, _, _ :: xs, _, hk => by
      rw [xorR]
      exact bindK_hi _ rfl fun _ _ => xorR_hi _ _ xs fun _ _ => hk _ _
  | _, _, _, _, _, [], _, hk => by rw [xorR]; exact hk _ _

theorem constsK_hi : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ns : List Nat)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts},
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprHi (k r out)) →
      CoveredM exprHi (constsK ns k)
  | _, _, [], _, hk => by rw [constsK]; exact hk _ _
  | _, _, _ :: ns, _, hk => by
      rw [constsK]
      exact bindK_hi _ rfl fun _ _ => constsK_hi ns fun _ _ => hk _ _

theorem addK_hi {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → Var Δ w1 → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out c,
      CoveredM exprHi (k r out c)) :
    CoveredM exprHi (addK xs ys k) := by
  rw [addK]
  exact bindK_hi _ rfl fun _ _ => adcR_hi _ _ _ _ fun _ _ _ => hk _ _ _

variable {n : Nat} (P : LimbParams n)

theorem csubPCK_hi {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprHi (k r out)) :
    CoveredM exprHi (Mont.csubPCK P xs k) := by
  rw [Mont.csubPCK]
  exact constsK_hi _ fun _ _ => addK_hi _ _ fun _ _ _ => selR_hi _ _ _ _ fun _ _ => hk _ _

theorem addMK_hi {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprHi (k r out)) :
    CoveredM exprHi (Mont.addMK P xs ys k) := by
  rw [Mont.addMK]
  exact bindK_hi _ rfl fun _ _ => addK_hi _ _ fun _ _ _ =>
    csubPCK_hi P _ fun _ _ => hk _ _

theorem subMK_hi {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprHi (k r out)) :
    CoveredM exprHi (Mont.subMK P xs ys k) := by
  rw [Mont.subMK]
  exact bindK_hi _ rfl fun _ _ => xorR_hi _ _ _ fun _ _ => bindK_hi _ rfl fun _ _ =>
    adcR_hi _ _ _ _ fun _ _ _ => constsK_hi _ fun _ _ => addK_hi _ _ fun _ _ _ =>
    selR_hi _ _ _ _ fun _ _ => hk _ _

end Gen

/-! ## 3. The addition and the subtraction blocks -/

section Blocks

variable {n : Nat} (P : LimbParams n) {Γ : Ctxt jasminDialect}

theorem retN_hi (k : Nat) (xs : List (Var Γ w64)) :
    CoveredM exprHi (Mont.retN k xs) := by
  cases xs with
  | nil => exact ⟨rfl, trivial⟩
  | cons a as => trivial

theorem montConstBlk_hi (k v : Nat) :
    CoveredM exprHi (Mont.constBlk (Γ := Γ) k v) := by
  rw [Mont.constBlk]
  exact constsK_hi _ fun _ _ => retN_hi _ _

/-- **The addition block binds no `mulhi`.** -/
theorem montAddBlk_hi (xs ys : List (Var Γ w64)) :
    CoveredM exprHi (Mont.addBlk P xs ys) := by
  rw [Mont.addBlk]
  exact addMK_hi P _ _ fun _ _ => retN_hi _ _

/-- **The subtraction block binds no `mulhi`.** -/
theorem montSubBlk_hi (xs ys : List (Var Γ w64)) :
    CoveredM exprHi (Mont.subBlk P xs ys) := by
  rw [Mont.subBlk]
  exact subMK_hi P _ _ fun _ _ => retN_hi _ _

end Blocks

/-! ## 4. The lowering of sums and differences -/

section Lower

open MultiBlockLowering (spliceMultiK MultiBlockLoweringData)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-- **A field expression of a sum or a difference**, at any modulus. -/
def AddSubOp {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) : Prop :=
  ∃ q, e.op = .fAdd q ∨ e.op = .fSub q

theorem rename_hi {Γ Γ' : Ctxt jasminDialect} {ts : List JasminTy}
    (h : Ctxt.Hom Γ Γ') (m : MC Γ ts) (hm : CoveredM exprHi m) :
    CoveredM exprHi (MultiReturnCom.rename h m) := by
  induction m generalizing Γ' with
  | ret => trivial
  | var e body ih =>
      obtain ⟨op, rfl, args⟩ := e
      exact ⟨hm.1, ih h.lift hm.2⟩

theorem spliceMultiK_hi : ∀ {Γ : Ctxt jasminDialect} {ts bs : List JasminTy} (blk : MC Γ ts)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → HVector (fun u => Var Δ u) ts → MC Δ bs},
    CoveredM exprHi blk →
    (∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ) res,
      CoveredM exprHi (k ren res)) →
      CoveredM exprHi (spliceMultiK blk k)
  | _, _, _, .ret _, _, _, hk => hk _ _
  | _, _, _, .var _ blk, _, hb, hk => ⟨hb.1, spliceMultiK_hi blk hb.2 fun _ _ => hk _ _⟩

theorem lowerR_hi {d : Dialect} [DialectSignature d]
    (L : MultiBlockLoweringData d jasminDialect)
    {Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop}
    (hB : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      CoveredM exprHi (L.exprBlock e)) :
    ∀ {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt jasminDialect} {bs : List JasminTy}
      (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (c : Com d Γ t)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        HVector (fun u => Var Δ' u) (L.mapTys t) → MC Δ' bs},
      CoveredCom Good c →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') vs,
        CoveredM exprHi (k r vs)) →
      CoveredM exprHi (L.lowerR ren c k)
  | _, _, _, _, _, .ret _, _, _, hk => by rw [MultiBlockLoweringData.lowerR]; exact hk _ _
  | _, _, _, _, ren, .var e body, _, hc, hk => by
      rw [MultiBlockLoweringData.lowerR, MultiBlockLoweringData.lowerBind]
      exact spliceMultiK_hi _ (rename_hi _ _ (hB e hc.1)) fun _ _ =>
        lowerR_hi L hB _ body hc.2 fun _ _ => hk _ _

variable {n : Nat}

open FieldToJasminLimbs (arrTy loadLimbs loadArgs storeLimbs)

theorem loadLimbs_hi {bs : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (a : Var Δ (arrTy n))
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Mont.Rn m) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h,
        CoveredM exprHi (k r h)) →
      CoveredM exprHi (loadLimbs m j a k)
  | _, 0, _, _, _, hk => by rw [loadLimbs]; exact hk _ _
  | _, m + 1, j, a, _, hk => by
      rw [loadLimbs]
      exact bindK_hi _ rfl fun _ _ => bindK_hi _ rfl fun _ _ =>
        loadLimbs_hi m (j + 1) _ fun _ _ => hk _ _

theorem loadArgs_hi {bs : List JasminTy} :
    ∀ (Γ : Ctxt fieldDialect) {Δ : Ctxt jasminDialect}
      (src : Ctxt.Hom (FieldToJasminLimbs.arrCtx n Γ) Δ)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (MultiBlockLowering.ctxFlat (FieldToJasminLimbs.mapTysL n) Γ) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h,
        CoveredM exprHi (k r h)) →
      CoveredM exprHi (loadArgs Γ src k)
  | [], _, _, _, hk => by rw [loadArgs]; exact hk _ _
  | _ :: Γ, _, _, _, hk => by
      rw [loadArgs]
      exact loadLimbs_hi _ _ _ fun _ _ => loadArgs_hi Γ _ fun _ _ => hk _ _

theorem storeLimbs_hi :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy n))
      (h : Ctxt.Hom (Mont.Rn m) Δ),
      CoveredM exprHi (storeLimbs m j o h)
  | _, 0, _, _, _ => by rw [storeLimbs]; trivial
  | _, m + 1, j, o, h => by
      rw [storeLimbs]
      exact bindK_hi _ rfl fun _ _ => bindK_hi _ rfl fun _ _ =>
        storeLimbs_hi m (j + 1) _ _

/-- **The lowered field program over word arrays of a covered program binds no `mulhi`**,
    when the block of every covered expression binds none. -/
theorem fieldBodyOf_hi (lo : FieldToJasminLimbs.LimbBlocks n)
    {Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop}
    (hB : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t), Good e →
        CoveredM exprHi ((FieldToJasminLimbs.loweringOf lo).exprBlock e))
    {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) (hc : CoveredCom Good c) :
    CoveredM exprHi (FieldToJasminLimbs.fieldBodyOf lo c) := by
  rw [FieldToJasminLimbs.fieldBodyOf]
  exact loadArgs_hi Γ _ fun _ _ =>
    lowerR_hi _ hB _ c hc fun _ _ => storeLimbs_hi _ _ _ _

/-- The single-result projection of a multi-result program binds no `mulhi` when the program
    binds none. -/
theorem toComHead_hi :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy} (m : MC Γ (t :: ts)),
      CoveredM exprHi m → CoveredCom exprHi m.toComHead
  | _, _, _, .ret (.cons _ _), _ => by rw [MultiReturnCom.toComHead]; trivial
  | _, _, _, .var _ body, hm => by
      rw [MultiReturnCom.toComHead]
      exact ⟨hm.1, toComHead_hi body hm.2⟩

end Lower

/-! ## 5. The blocks of the sum and the difference of a wide template -/

section Wide

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open FieldWideInline
open _root_.Hax.FieldTag (FieldMethod)

variable {n : Nat}

/-- The Montgomery limb block of a sum or a difference binds no `mulhi`. -/
theorem montExprBlock_hi (P : LimbParams n) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) (he : AddSubOp e) :
    CoveredM exprHi
      ((FieldToJasminLimbs.loweringOf (FieldToJasminLimbs.lowerOpL P)).exprBlock e) := by
  obtain ⟨op, rfl, args⟩ := e
  obtain ⟨q, hq | hq⟩ := he <;> (simp only at hq; subst hq)
  · change CoveredM exprHi (FieldToJasminLimbs.lowerOpL P (.fAdd q))
    rw [FieldToJasminLimbs.lowerOpL]
    split
    · exact montAddBlk_hi P _ _
    · exact montConstBlk_hi _ _
  · change CoveredM exprHi (FieldToJasminLimbs.lowerOpL P (.fSub q))
    rw [FieldToJasminLimbs.lowerOpL]
    split
    · exact montSubBlk_hi P _ _
    · exact montConstBlk_hi _ _

/-- The Solinas limb block of a sum or a difference binds no `mulhi`. -/
theorem solinasExprBlock_hi (S : Solinas.SolinasParams n) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (e : Expr fieldDialect Γ t) (he : AddSubOp e) :
    CoveredM exprHi
      ((FieldToJasminLimbs.loweringOf (FieldToJasminLimbsSolinas.lowerOpL S)).exprBlock e) := by
  obtain ⟨op, rfl, args⟩ := e
  obtain ⟨q, hq | hq⟩ := he <;> (simp only at hq; subst hq)
  · change CoveredM exprHi (FieldToJasminLimbsSolinas.lowerOpL S (.fAdd q))
    rw [FieldToJasminLimbsSolinas.lowerOpL]
    split
    · rw [Solinas.addBlk]
      exact addMK_hi (Solinas.lp S) _ _ fun _ _ => retN_hi _ _
    · exact montConstBlk_hi _ _
  · change CoveredM exprHi (FieldToJasminLimbsSolinas.lowerOpL S (.fSub q))
    rw [FieldToJasminLimbsSolinas.lowerOpL]
    split
    · exact montSubBlk_hi (Solinas.lp S) _ _
    · exact montConstBlk_hi _ _

/-- The sum and the difference are the methods whose field operation is a sum or a
    difference. -/
def AddSubM (m : FieldMethod) : Prop := m = .add ∨ m = .sub

/-- The program of one operation of a sum or a difference is covered by `AddSubOp`. -/
theorem opCom_addSub {m : FieldMethod} (hm : AddSubM m) (p : Nat) :
    CoveredCom AddSubOp (FieldLower.opCom (fieldOpOf m p)) := by
  rcases hm with rfl | rfl
  · exact ⟨⟨p, Or.inl rfl⟩, trivial⟩
  · exact ⟨⟨p, Or.inr rfl⟩, trivial⟩

/-- **The blocks of the sum and the difference of a wide template bind no `mulhi`.** -/
def WideHi {p k : Nat} (W : WideTemplate p k) : Prop :=
  ∀ m : FieldMethod, AddSubM m →
    CoveredCom exprHi (@FieldLower.FieldLowerTemplate.block W.α k W.inst W.P (fieldOpOf m p))

theorem castN_hi {p k : Nat} (h : n = k) {W : WideTemplate p n} (hW : WideHi W) :
    WideHi (W.castN h) := by
  subst h
  exact hW

theorem castP_hi {p q : Nat} (h : p = q)
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (hW : WideHi W) :
    WideHi (W.castP h) := by
  subst h
  exact hW

/-- The blocks of the sum and the difference of the canonical Montgomery template bind no
    `mulhi`. -/
theorem ofMont_hi (P : LimbParams n) (hn : n < 2 ^ 64) : WideHi (WideTemplate.ofMont P hn) := by
  intro m hm
  change CoveredCom exprHi
    (FieldToJasminLimbs.fieldComOf (FieldToJasminLimbs.lowerOpL P) (twistOp n (fieldOpOf m _)))
  rw [FieldToJasminLimbs.fieldComOf]
  refine toComHead_hi _ (fieldBodyOf_hi _ (montExprBlock_hi P) _ ?_)
  rcases hm with rfl | rfl
  · exact ⟨⟨_, Or.inl rfl⟩, trivial⟩
  · exact ⟨⟨_, Or.inr rfl⟩, trivial⟩

/-- The blocks of the sum and the difference of the Solinas template of a record bind no
    `mulhi`. -/
theorem ofSolinasAt_hi (S : Solinas.SolinasParams n)
    (hn : n = _root_.Hax.FieldTag.fieldLimbs (Solinas.p S)) (h64 : n < 2 ^ 64) :
    WideHi (WideTemplate.ofSolinasAt S hn h64) := by
  refine castN_hi hn fun m hm => ?_
  change CoveredCom exprHi
    (FieldToJasminLimbs.fieldComOf (FieldToJasminLimbsSolinas.lowerOpL S)
      (FieldLower.opCom (fieldOpOf m _)))
  rw [FieldToJasminLimbs.fieldComOf]
  exact toComHead_hi _ (fieldBodyOf_hi _ (solinasExprBlock_hi S) _ (opCom_addSub hm _))

/-- **The blocks of the sum and the difference of a registered wide template bind no
    `mulhi`.** -/
theorem wideTemplateOf_addSub_hi {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W) :
    WideHi W := by
  rcases wideTemplateOf_cases h with ⟨_, S, hn, h64, hp, rfl⟩ | ⟨_, _, hn, rfl⟩
  · exact castP_hi hp (ofSolinasAt_hi S hn h64)
  · exact ofMont_hi _ hn

/-- **The body of a call of the sum or the difference at a registered wide template binds no
    `mulhi`.** -/
theorem wideBlockOf_addSub_hi {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W)
    {m : FieldMethod} (hm : AddSubM m) : (wideBlockOf W m).allOps noMulhiB = true :=
  allOps_ofCom (d := jasminDialect) noMulhiB _
    (coveredCom_rename (d := jasminDialect) noMulhiB _ _ (wideTemplateOf_addSub_hi h m hm))

end Wide

/-! ## 6. The lowered bodies of the sum and the difference -/

section Lowered

open CatCrypt.Crypto.SecureCompilation.Algebraic (ModArithLimbTemplate)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.ModArithLimbs (canonTemplateOf ofWide optTy
  ofWordsBlock? toWordsBlock? bodyBlock?)
open _root_.Hax.FieldTag (fieldLimbs FieldMethod)

/-- **The cast block from words of the wide template binds nothing.** -/
theorem ofWordsBlock?_wide_hi {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    {hw : wideTemplateOf p = some W} {Δ : Ctxt jasminDialect}
    (o : Option (ModArithLimbTemplate p .canon))
    (ho : o = some (ofWide W hw)) (w k : Nat) (a : Var Δ (.stackArr w k))
    {blk : Com jasminDialect Δ (optTy o)} (hb : ofWordsBlock? o w k a = some blk) :
    CoveredCom exprHi blk := by
  subst ho
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
  change ModArithLimbs.arrOfWords (fieldLimbs p) w k = some c at hc
  unfold ModArithLimbs.arrOfWords at hc
  split at hc
  · rename_i h
    cases hc
    injection h with h1 h2
    subst h1 h2
    exact coveredCom_rename (d := jasminDialect) noMulhiB _ (.ret _) trivial
  · cases hc

/-- **The block of the sum or the difference of the wide template binds no `mulhi`.** -/
theorem bodyBlock?_wide_hi {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    {hw : wideTemplateOf p = some W} {Δ : Ctxt jasminDialect}
    (o : Option (ModArithLimbTemplate p .canon)) (ho : o = some (ofWide W hw))
    {m : FieldMethod} (hm : AddSubM m)
    (args : HVector (fun t => Var Δ t)
      (Algebraic.ModArithLimbTemplate.limbSig (ModArithLimbs.optTy o) m))
    {blk : Com jasminDialect Δ (optTy o)} (hb : bodyBlock? o m args = some blk) :
    CoveredCom exprHi blk := by
  subst ho
  cases hb
  refine coveredCom_rename (d := jasminDialect) noMulhiB _ _ ?_
  rcases hm with rfl | rfl
  · exact coveredCom_rename (d := jasminDialect) noMulhiB _ _
      (wideTemplateOf_addSub_hi hw _ (Or.inl rfl))
  · exact coveredCom_rename (d := jasminDialect) noMulhiB _ _
      (wideTemplateOf_addSub_hi hw _ (Or.inr rfl))

set_option hygiene false in
/-- The splice of a cast block from words of the wide template. -/
local macro "hi_cast_in_tac" : tactic => `(tactic| (
  obtain ⟨b, hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  refine JasminImageOps.allOps_spliceNF? noMulhiB _ _
    (coveredCom_rename (d := jasminDialect) noMulhiB _ _ (ofWordsBlock?_wide_hi _ hc _ _ _ hb))
    (fun ren' res q' hq' => ?_) _ hq'))

set_option hygiene false in
/-- The splice of the block of the sum or the difference before the cast to words and the
    return. -/
local macro "hi_op_tail_tac" : tactic => `(tactic| (
  obtain ⟨b, hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  have h3 : CoveredCom exprHi b := by
    simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?, Expr.rename,
      ModArithLimbs.limbOpBlock?, ModArithLimbs.modBlock?] at hb
    first
      | exact bodyBlock?_wide_hi _ hc (by first | exact Or.inl rfl | exact Or.inr rfl) _ hb
      | (split at hb <;>
          exact bodyBlock?_wide_hi _ hc (by first | exact Or.inl rfl | exact Or.inr rfl) _ hb)
  refine JasminImageOps.allOps_spliceNF? noMulhiB _ _
    (coveredCom_rename (d := jasminDialect) noMulhiB _ _ h3) (fun ren' res q' hq' => ?_) _ hq'
  obtain ⟨b4, hb4, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?, Expr.rename,
    ModArithLimbs.limbOpBlock?, ModArithLimbs.limbCastBlock?] at hb4
  obtain ⟨h4, rfl⟩ := toWordsBlock?_wide_ret _ hc _ _ _ hb4
  simp only [Com.rename, NFProg.spliceNF?, Option.some.injEq] at hq'
  subst hq'
  rfl))

/-- **The raised body of the sum or the difference on arrays, lowered to `mod_arith` and to the
    wide template, binds no `mulhi`.** -/
theorem lowerArr_hi {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W)
    {m : FieldMethod} (hm : AddSubM m) {r₂ r₃}
    (h : NFProg.map? FieldToModArithChain.fieldToModArithJ FieldToModArithChain.regionTypes
      (FieldRaise.arrBody m p (fieldLimbs p)) (fun v => v) = some r₂)
    (h₃ : NFProg.map? ModArithLimbs.modArithLimbsJ ModArithLimbs.modArithLimbsJ_regionTypes r₂
      (fun v => v) = some r₃) : r₃.allOps noMulhiB = true := by
  have hc := canonTemplateOf_wide hn hw
  rcases hm with rfl | rfl <;>
  simp only [NFProg.map?, FieldRaise.arrBody, FieldRaise.arrBody2,
    FieldToModArithChain.fieldToModArithJ,
    FieldToModArithChain.lowerBlock?, FieldToModArithChain.opBlock?, FieldRaise.fromE,
    FieldRaise.toE, FieldRaise.opE, FieldToModArithChain.castBlock?, FieldToModArithChain.pfBlock?,
    FieldChainDialect.FieldRepr.Admits, ↓reduceIte, Option.bind_some, FieldToModArithChain.opB,
    Com.rename, NFProg.spliceNF?, Option.map_some] at h <;>
  obtain rfl := Option.some.inj h <;>
  have hq' := h₃ <;>
  simp only [NFProg.map?] at hq'
  · hi_cast_in_tac; hi_cast_in_tac; hi_op_tail_tac
  · hi_cast_in_tac; hi_cast_in_tac; hi_op_tail_tac

/-- **The lowered body of a tagged head of the sum or the difference, at a modulus without a
    narrow representation and with a wide template, binds no `mulhi`.** -/
theorem fieldBodyD_addSub_hi {f : String} {m : FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : _root_.Hax.FieldTag.fieldTag? f = some (m, p))
    (hm : AddSubM m) (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W)
    {as rs : List JasminTy} {b : NFProg jasminDialect as rs}
    (hb : FieldDialectStep.fieldBodyD f as rs = some b) : b.allOps noMulhiB = true := by
  obtain ⟨-, r₁, hr₁, hb⟩ := FieldDialectStep.fieldBodyD_some hb
  unfold FieldRaise.raiseBody at hr₁
  rw [ht] at hr₁
  simp only [hn, hw] at hr₁
  unfold FieldRaise.raiseArr at hr₁
  split at hr₁
  · rename_i hs
    obtain ⟨has, hrs⟩ := hs
    obtain rfl := List.map_injective_iff.mpr Sum.inl_injective has
    obtain rfl : rs = [JasminTy.stackArr 64 (fieldLimbs p)] :=
      List.map_injective_iff.mpr Sum.inl_injective (hrs.trans rfl)
    cases hr₁
    obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
    refine FieldDialectStep.allOps_dce _ _ ?_
    unfold NFFwdLoad1.fwdLoad1
    refine FieldDialectStep.allOps_fwdLoad1Go _ _ ?_ _ _
    rw [FieldDialectStep.allOps_castNF]
    exact lowerArr_hi hn hw hm hs₂ hs₃
  · cases hr₁

end Lowered

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
