/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyCompleteProbe
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyArrays

/-!
# The complete direction of the reading of `reifyAeneas%`

`AeneasFront/ReifyCompleteProbe.lean` defines the complete direction `CompleteE`, `CompleteG`
of the judgements `ReifyE`, `ReifyG`: a value of the reading of `p` is the image of a value of
the Aeneas computation. This module gives the complete twin of every congruence lemma the
reader `reifyAeneas%` applies outside the `while` loop, the twins of the exact expression
instances, and the elaborator `completeAeneas%`.

## Twins

A twin has the arguments of its congruence lemma in the same order, with each judgement
`ReifyE`, `ReifyG` replaced by `CompleteE`, `CompleteG` and each passing condition
`∀ y, m = .ok y → S ∧ k = .ok y` (`pass_massert`, `pass_iteFailElse`, `pass_iteFail`) replaced
by its converse `S → m = k` (`massert_pass`, `iteFailElse_pass`, `iteFail_pass`). A judgement
of a value `ok y` is complete by determinism of the reading (`completeG_of_ok`,
`completeE_of_ok`), which covers the values of variables, units, Booleans and the wrapping
operations. The range and indexed loops are complete by induction on the trip list
(`foldRange_complete`).

## The elaborator

`completeAeneas% R`, for a value `R : Reified S` of `reifyAeneas% f`, walks the proof term of
`R.sound` and replaces each node by its twin (`CompleteMeta.twinOf`), or a judgement of a value
by `completeG_of_ok`. A definition `R` of another module holds `R.sound` as an auxiliary
theorem whose body is not exported; the elaborator then runs the reader again on the function
`f` of the statement of `R` and walks the proof term it returns. Its result has the type
`∀ xs, CompleteG E (f xs) V R.prog`. A node with
no twin is refused with its name: the `while` loop `Reify.loop` and the signed checked
operations of `AeneasFront/Signed.lean`, read as wrapping, whose reading has values where the
Aeneas operation fails.

## Main results

* `Complete.of_eq`, `Complete.letE`, `Complete.letLit`, `Complete.bindLit`, `Complete.okLit`,
  `Complete.iteLt`, `Complete.guard`, `Complete.plug`, `Complete.iteBit`, `Complete.guardP`,
  `Complete.guardS`, `Complete.iteFailElse`, `Complete.iteFail`, `Complete.argBit`: the
  congruence twins
* `Complete.rangeForLoop`, `Complete.indexedForLoop`: the counted loops
* `complete_sub`, `complete_mul`, `complete_band`, `complete_bor`, `complete_bxor`,
  `complete_index`, `complete_update`: the expression twins
* `completeAeneas%`: the elaborator
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyComplete

open HaxLean.Aeneas.Std
open _root_.Hax (Value)
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## Values -/

/-- **A value is complete.** The reading of a judgement at `ok y` has the one value `E y`. -/
theorem completeG_of_ok {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {V : Valuation Γ} {p : NFProg nfDialect Γ ts} {y : α}
    (r : ReifyG E (.ok y) V p) : CompleteG E (.ok y) V p := by
  intro W hW
  rw [r.sound y rfl] at hW
  cases hW
  exact ⟨y, rfl, rfl⟩

/-- **A value of an expression is complete.** -/
theorem completeE_of_ok {α : Type} [AeVal α] {Γ : Ctxt nfDialect} {V : Valuation Γ}
    {e : Expr nfDialect Γ (AeVal.nty α)} {y : α} (r : ReifyE (.ok y) V e) :
    CompleteE (.ok y) V e := by
  intro w hw
  rw [r.sound y rfl] at hw
  cases hw
  exact ⟨y, rfl, rfl⟩

/-! ## Expression twins -/

/-- The checked subtraction, complete direction. -/
theorem complete_sub {ty : UScalarTy} [CheckedTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    CompleteE (x - y) V (callE2 (checkedName .sub ty) (.word 64) va vb) :=
  complete_call2 _ (AOp.aen .sub) (aeCall2_checked .sub rfl) x y V va vb hx.eq hy.eq

/-- The checked multiplication, complete direction. -/
theorem complete_mul {ty : UScalarTy} [CheckedTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    CompleteE (x * y) V (callE2 (checkedName .mul ty) (.word 64) va vb) :=
  complete_call2 _ (AOp.aen .mul) (aeCall2_checked .mul rfl) x y V va vb hx.eq hy.eq

/-- The bitwise conjunction, complete direction. -/
theorem complete_band {ty : UScalarTy} [h : TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    CompleteE (lift (x &&& y)) V (callE2 (opName .band ++ uTag ty) (.word 64) va vb) :=
  complete_call2 _ (WordOp.aen .band) (aeCall2_word (by simp [wordAt, h.table])) x y V va vb
    hx.eq hy.eq

/-- The bitwise disjunction, complete direction. -/
theorem complete_bor {ty : UScalarTy} [h : TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    CompleteE (lift (x ||| y)) V (callE2 (opName .bor ++ uTag ty) (.word 64) va vb) :=
  complete_call2 _ (WordOp.aen .bor) (aeCall2_word (by simp [wordAt, h.table])) x y V va vb
    hx.eq hy.eq

/-- The bitwise exclusive disjunction, complete direction. -/
theorem complete_bxor {ty : UScalarTy} [h : TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    CompleteE (lift (x ^^^ y)) V (callE2 (opName .bxor ++ uTag ty) (.word 64) va vb) :=
  complete_call2 _ (WordOp.aen .bxor) (aeCall2_word (by simp [wordAt, h.table])) x y V va vb
    hx.eq hy.eq

/-- `Array.index_usize`, complete direction: the call `index` fails when the index does. -/
theorem complete_index {ty : UScalarTy} [Le64 ty] {n : Usize} {Γ : Ctxt nfDialect}
    (a : HaxLean.Aeneas.Std.Array (UScalar ty) n) (i : Usize) (V : Valuation Γ)
    {va : Var Γ (.arr n.val (.word 64))} {vi : Var Γ (.word 64)}
    [ha : Lookup V (embA a) va] [hi : Lookup V (embW i) vi] :
    CompleteE (a.index_usize i) V
      ⟨.call "index" [.arr n.val (.word 64), .word 64] (.word 64), rfl,
        .cons va (.cons vi .nil)⟩ := by
  intro w hw
  change aeOp (.call "index" [.arr n.val (.word 64), .word 64] (.word 64))
    (.cons (va.lookup V) (.cons (vi.lookup V) .nil)) = .ok w at hw
  unfold aeOp at hw
  rw [nfDenoteOp] at hw
  unfold aeTable at hw
  simp only [encAll] at hw
  rw [ha.eq, hi.eq, enc_embA, enc_embW, aeCallV, aeCall2_index] at hw
  split at hw
  · rename_i w' hd
    cases hw
    split at hd
    · rename_i v hv
      obtain ⟨z, hz, hv⟩ := rustM_bind_ok hv
      cases hv
      rw [dec_wordV] at hd
      cases hd
      exact ⟨z, hz, rfl⟩
    · cases hd
  · cases hw

/-- `Array.update`, complete direction: the call `array_update` fails when the update does. -/
theorem complete_update {ty : UScalarTy} [Le64 ty] {n : Usize} {Γ : Ctxt nfDialect}
    (a : HaxLean.Aeneas.Std.Array (UScalar ty) n) (i : Usize) (x : UScalar ty) (V : Valuation Γ)
    {va : Var Γ (.arr n.val (.word 64))} {vi vx : Var Γ (.word 64)}
    [ha : Lookup V (embA a) va] [hi : Lookup V (embW i) vi] [hx : Lookup V (embW x) vx] :
    CompleteE (a.update i x) V
      ⟨.call "array_update" [.arr n.val (.word 64), .word 64, .word 64] (.arr n.val (.word 64)),
        rfl, .cons va (.cons vi (.cons vx .nil))⟩ := by
  intro w hw
  change aeOp (.call "array_update" [.arr n.val (.word 64), .word 64, .word 64]
    (.arr n.val (.word 64)))
    (.cons (va.lookup V) (.cons (vi.lookup V) (.cons (vx.lookup V) .nil))) = .ok w at hw
  unfold aeOp at hw
  rw [nfDenoteOp] at hw
  unfold aeTable at hw
  simp only [encAll] at hw
  rw [ha.eq, hi.eq, hx.eq, enc_embA, enc_embW, enc_embW, aeCallV, aeCall3_update] at hw
  split at hw
  · rename_i w' hd
    cases hw
    split at hd
    · rename_i v hv
      obtain ⟨z, hz, hv⟩ := rustM_bind_ok hv
      cases hv
      rw [dec_arrV] at hd
      cases hd
      exact ⟨z, hz, rfl⟩
    · cases hd
  · cases hw

/-! ## Congruence twins -/

/-- The twin of `ReifyG.of_eq`. -/
theorem Complete.of_eq {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {m m' : RustM α} {Γ : Ctxt nfDialect} {V : Valuation Γ} {p : NFProg nfDialect Γ ts}
    (h : m = m') (r : CompleteG E m' V p) : CompleteG E m V p :=
  h ▸ r

/-- The twin of `Reify.letE`. -/
theorem Complete.letE {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {t : NfTy} {e : Expr nfDialect Γ t} {p : NFProg nfDialect (t :: Γ) ts}
    (m : RustM α) (V : Valuation Γ) (a : t.denote) (he : aeExpr e V = .ok a)
    (h : CompleteG E m (HVector.cons a V) p) : CompleteG E m V (.var e p) := by
  intro W hW
  rw [nfToRustM, he, bind_tc_ok, extend_eq] at hW
  exact h W hW

/-- The twin of `Reify.letLit`. -/
theorem Complete.letLit {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty] {p : NFProg nfDialect (.word 64 :: Γ) ts}
    (c : UScalar ty) (m : RustM α) (V : Valuation Γ) (h : CompleteG E m (vCons c V) p) :
    CompleteG E m V (.var (litE c) p) :=
  Complete.letE m V (embW c) (aeExpr_litE c V) h

/-- The twin of `Reify.bindLit`. -/
theorem Complete.bindLit {α β : Type} [AeVal α] {ts : List NfTy}
    {E : β → Valuation (d := nfDialect) ts} {Γ : Ctxt nfDialect} {ty : UScalarTy}
    [Le64 ty] {e : Expr nfDialect (.word 64 :: Γ) (AeVal.nty α)}
    {p : NFProg nfDialect (AeVal.nty α :: .word 64 :: Γ) ts}
    (c : UScalar ty) (m : RustM α) (k : α → RustM β) (V : Valuation Γ)
    (he : CompleteE m (vCons c V) e) (hk : ∀ x, CompleteG E (k x) (vCons x (vCons c V)) p) :
    CompleteG E (m >>= k) V (.var (litE c) (.var e p)) :=
  Complete.letLit c _ V (complete_bind m k (vCons c V) he hk)

/-- The twin of `Reify.okLit`. -/
theorem Complete.okLit {α : Type} [AeVal α] {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty]
    {e : Expr nfDialect (.word 64 :: Γ) (AeVal.nty α)} (c : UScalar ty) (m : RustM α)
    (V : Valuation Γ) (he : CompleteE m (vCons c V) e) :
    CompleteG single m V (.var (litE c) (.var e (.ret (.cons .here .nil)))) :=
  Complete.letLit c m V (complete_okExpr m (vCons c V) he)

/-- The twin of `Reify.iteLt`. -/
theorem Complete.iteLt {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty]
    {va vb : Var Γ (.word 64)} {pa pb : NFProg nfDialect (.bit :: Γ) ts}
    (x y : UScalar ty) (a b : RustM α) (V : Valuation Γ)
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb]
    (ha : CompleteG E a (vCons (CmpOp.aen .lt x y) V) pa)
    (hb : CompleteG E b (vCons (CmpOp.aen .lt x y) V) pb) :
    CompleteG E (if x < y then a else b) V
      (.var (callE2 (CmpOp.name .lt) .bit va vb)
        (.ifThenElse .here pa pb (.ret (prefixVars ts _)))) := by
  intro W hW
  have hc : aeExpr (callE2 (CmpOp.name .lt) .bit va vb) V = .ok (CmpOp.aen .lt x y) :=
    aeExpr_callE2 _ _ va vb V x y hx.eq hy.eq (aeCall2_cmp .lt x y) rfl
  rw [nfToRustM, hc, bind_tc_ok, nfToRustM] at hW
  obtain ⟨r, hr, hW⟩ := rustM_bind_ok hW
  rw [nfToRustM, lookupArgs_prefixVars] at hW
  cases hW
  have hl : HasBoolBit.toBool (d := nfDialect)
      ((Ctxt.Var.here (Γ := Γ)).lookup (Valuation.extend V (CmpOp.aen .lt x y))) =
        CmpOp.aen .lt x y := rfl
  have hiff : CmpOp.aen .lt x y = true ↔ x < y := by
    simp only [CmpOp.aen, decide_eq_true_eq]
    exact Iff.rfl
  rw [hl, extend_eq] at hr
  by_cases hxy : x < y
  · rw [ite_eq_left (hiff.mpr hxy)] at hr
    simp only [hxy, ite_true]
    exact ha W hr
  · rw [ite_eq_right (fun h => hxy (hiff.mp h))] at hr
    simp only [hxy, ite_false]
    exact hb W hr

/-- The twin of `Reify.guard`: when the bit `c` of the failing case is `false`, `m` is `k`. -/
theorem Complete.guard {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {pk : NFProg nfDialect (.bit :: Γ) ts}
    (m k : RustM α) (c : Bool) (V : Valuation Γ) (he : aeExpr e V = .ok c)
    (hm : c = false → m = k) (hk : CompleteG E k (vCons c V) pk) :
    CompleteG E m V (.var e (.ifThenElse .here abortArm (.ret .nil) pk)) := by
  intro W hW
  rw [nfToRustM, he, bind_tc_ok, extend_eq, nfToRustM] at hW
  cases c
  · rw [hm rfl]
    exact hk W hW
  · simp only [nfToRustM_abortArm] at hW
    cases hW

/-- The twin of `ReifyG.plug`. -/
theorem Complete.plug {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ Δ : Ctxt nfDialect} {p : NFPre nfDialect Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    {q : NFProg nfDialect Δ ts} (m : RustM α) (hp : preReads p V W) (h : CompleteG E m W q) :
    CompleteG E m V (p.plug q) :=
  fun X hX => h X ((nfToRustM_plug p q hp).symm.trans hX)

/-- The twin of `Reify.iteBit`. -/
theorem Complete.iteBit {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ Δ : Ctxt nfDialect} {p : NFPre nfDialect Γ Δ} {W : Valuation Δ} {v : Var Δ .bit}
    {pa pb : NFProg nfDialect Δ ts} (c : Prop) [Decidable c] (a b : RustM α)
    (V : Valuation Γ) [hs : ReadBit (decide c) V Δ p W v] (ha : CompleteG E a W pa)
    (hb : CompleteG E b W pb) :
    CompleteG E (if c then a else b) V
      (p.plug (.ifThenElse v pa pb (.ret (prefixVars ts Δ)))) := by
  refine Complete.plug _ hs.reads ?_
  intro X hX
  rw [nfToRustM] at hX
  obtain ⟨r, hr, hX⟩ := rustM_bind_ok hX
  rw [nfToRustM, lookupArgs_prefixVars] at hX
  cases hX
  have hl : HasBoolBit.toBool (d := nfDialect) (v.lookup W) = decide c := hs.bit
  rw [hl] at hr
  by_cases hc : c
  · simp only [hc, decide_true, ite_true] at hr ⊢
    exact ha X hr
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at hr ⊢
    exact hb X hr

/-- The twin of `Reify.guardP`: the passing condition `S → m = k`. -/
theorem Complete.guardP {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ Δ : Ctxt nfDialect} {p : NFPre nfDialect Γ Δ} {W : Valuation Δ} {v : Var Δ .bit}
    {pk : NFProg nfDialect (.bit :: Δ) ts}
    (S : Prop) [Decidable S] (m k : RustM α) (V : Valuation Γ)
    [hs : ReadBit (decide S) V Δ p W v]
    (hpass : S → m = k) (hk : CompleteG E k (vCons (!decide S) W) pk) :
    CompleteG E m V (p.plug (.var (notE v) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  Complete.plug m hs.reads (Complete.guard m k (!decide S) W (aeExpr_notE v W _ hs.bit)
    (fun h => hpass (by simpa using h)) hk)

-- The `Decidable S` argument keeps the argument list of `Reify.guardS` for the walk.
set_option linter.unusedDecidableInType false in
/-- The twin of `Reify.guardS`. -/
theorem Complete.guardS {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (S : Prop) [Decidable S] (m k : RustM α) (V : Valuation Γ) [ReadCond S V b e]
    (hpass : S → m = k) (hk : CompleteG E k (vCons (!b) (vCons b V)) pk) :
    CompleteG E m V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  complete_guardS S m k V hpass hk

/-- The twin of `Reify.iteFailElse`. -/
theorem Complete.iteFailElse {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (c : Prop) [Decidable c] (k : RustM α) (err : Error) (V : Valuation Γ) [ReadCond c V b e]
    (hk : CompleteG E k (vCons (!b) (vCons b V)) pk) :
    CompleteG E (if c then k else .fail err) V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  complete_guardS c _ k V (iteFailElse_pass c k err) hk

/-- The twin of `Reify.iteFail`. -/
theorem Complete.iteFail {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (c : Prop) [Decidable c] (err : Error) (k : RustM α) (V : Valuation Γ)
    [ReadCond (¬ c) V b e] (hk : CompleteG E k (vCons (!b) (vCons b V)) pk) :
    CompleteG E (if c then .fail err else k) V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  complete_guardS (¬ c) _ k V (iteFail_pass c err k) hk

/-- The twin of `Reify.argBit`. -/
theorem Complete.argBit {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {v : Var Γ (.word 64)} {p : NFProg nfDialect (.bit :: .word 64 :: Γ) ts}
    (b : Bool) (m : RustM α) (V : Valuation Γ) [hv : Lookup V (boolW b) v]
    (h : CompleteG E m (vCons b (vCons zeroU V)) p) :
    CompleteG E m V
      (.var (litE zeroU) (.var (callE2 (CmpOp.name .ne) .bit v.there .here) p)) :=
  Complete.letLit zeroU m V (Complete.letE m _ b
    (aeExpr_callE2 _ _ v.there .here (vCons zeroU V) (boolU b) zeroU
      (hv.eq.trans (embW_boolU b).symm) rfl (aeCall2_cmp .ne _ _)
      (by rw [aen_ne_boolU]; rfl)) h)

/-! ## Counted loops -/

/-- **The fold of a range, complete direction.** A value of the fold of the reading of `pb`
    over the trip indices `s, …, s + k - 1` is the image of a value of `foldRangeAux f k s`. -/
theorem foldRange_complete {σ : Type} [AeVal σ] {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (pb : NFProg nfDialect (AeVal.nty σ :: .word 64 :: Γ) [AeVal.nty σ])
    (f : σ → Usize → RustM σ)
    (hb : ∀ (i : Usize) (acc : σ), CompleteG single (f acc i) (vCons acc (vCons i V)) pb) :
    ∀ (k s : Nat) (acc : σ) (W : Valuation (d := nfDialect) [AeVal.nty σ]),
      s + k ≤ 2 ^ UScalarTy.Usize.numBits →
      (List.range' s k).foldlM
          (fun a i => nfToRustM pb (hvAppend a (.cons (HasWord64.ofNat (d := nfDialect) i) V)))
          (single acc) = .ok W →
      ∃ y, HaxBackend.foldRangeAux f k s acc = .ok y ∧ single y = W
  | 0, _, acc, W, _, h => by
    cases h
    exact ⟨acc, rfl, rfl⟩
  | k + 1, s, acc, W, hk, h => by
    rw [List.range'_succ, List.foldlM_cons] at h
    obtain ⟨a, ha, h⟩ := rustM_bind_ok h
    have he : AeVal.emb (⟨BitVec.ofNat _ s⟩ : Usize) = HasWord64.ofNat (d := nfDialect) s :=
      embW_usize_ofNat (by omega)
    rw [show hvAppend (single acc) (.cons (HasWord64.ofNat (d := nfDialect) s) V) =
      vCons acc (vCons (⟨BitVec.ofNat _ s⟩ : Usize) V) by
        unfold vCons
        rw [he]
        rfl] at ha
    obtain ⟨acc', h1, rfl⟩ := hb _ acc a ha
    obtain ⟨y, hy, hW⟩ := foldRange_complete V pb f hb k (s + 1) acc' W (by omega) h
    refine ⟨y, ?_, hW⟩
    rw [HaxBackend.foldRangeAux, h1, bind_tc_ok]
    exact hy

/-- The twin of `Reify.rangeForLoop`. -/
theorem Complete.rangeForLoop {σ : Type} [AeVal σ] {Γ : Ctxt nfDialect}
    {v : Var Γ (AeVal.nty σ)}
    {pb : NFProg nfDialect (AeVal.nty σ :: .word 64 :: .word 64 :: Γ) [AeVal.nty σ]}
    (F : core.ops.range.Range Usize × σ →
      RustM (HaxLean.Aeneas.Std.ControlFlow (core.ops.range.Range Usize × σ) σ))
    (n : Usize) (init : σ) (f : σ → Usize → RustM σ) (V : Valuation Γ)
    [hi : Lookup V (AeVal.emb init) v]
    (hF : ∀ (s : Usize) (acc : σ), F ({ start := s, «end» := n }, acc) =
      if s.val < n.val then
        f acc s >>= fun acc' =>
          .ok (.cont ({ start := ⟨BitVec.ofNat _ (s.val + 1)⟩, «end» := n }, acc'))
      else .ok (.done acc))
    (hb : ∀ (i : Usize) (acc : σ),
      CompleteG single (f acc i) (vCons acc (vCons i (vCons n V))) pb) :
    CompleteG single (HaxLean.Aeneas.Std.loop F ({ start := 0#usize, «end» := n }, init)) V
      (.var (litE n) (.forLoop .here (.cons v.there .nil) pb (.ret (.cons .here .nil)))) := by
  intro W hW
  have hn : n.val < 2 ^ 64 := lt64 n
  rw [nfToRustM, aeExpr_litE, bind_tc_ok, nfToRustM] at hW
  have hc : HasWord64.toNat (d := nfDialect)
      ((Ctxt.Var.here (Γ := Γ)).lookup
        (Valuation.extend (t := NfTy.word 64) V (embW n))) = n.val := by
    change (BitVec.ofNat 64 n.val).toNat = n.val
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hinit : Expr.lookupArgs (HVector.cons v.there HVector.nil)
      (Valuation.extend (t := NfTy.word 64) V (embW n)) = single init := by
    change HVector.cons (v.lookup V) HVector.nil = _
    rw [hi.eq]
  rw [hc, hinit, List.range_eq_range', extend_eq] at hW
  obtain ⟨acc, hacc, hW⟩ := rustM_bind_ok hW
  obtain ⟨y, hy, rfl⟩ := foldRange_complete (vCons n V) pb f hb n.val 0 init acc
    (by have := n.bv.isLt; simp only [UScalar.val] at this ⊢; omega) hacc
  rw [nfToRustM] at hW
  cases hW
  refine ⟨y, ?_, rfl⟩
  rw [loop_range F f n hF (n.val - (0#usize : Usize).val) 0#usize init rfl]
  exact hy

/-- The twin of `Reify.indexedForLoop`. -/
theorem Complete.indexedForLoop {I Item σ : Type} [AeVal σ] {Γ : Ctxt nfDialect}
    {v : Var Γ (AeVal.nty σ)}
    {pb : NFProg nfDialect (AeVal.nty σ :: .word 64 :: .word 64 :: Γ) [AeVal.nty σ]}
    {next : I → RustM (Option Item × I)} {st₀ : I} {cnt : Usize}
    (it : IndexedIter next st₀ cnt)
    (F : I × σ → RustM (HaxLean.Aeneas.Std.ControlFlow (I × σ) σ))
    (K : σ → Option Item × I → RustM (HaxLean.Aeneas.Std.ControlFlow (I × σ) σ))
    (f : σ → Usize → RustM σ) (init : σ) (V : Valuation Γ)
    [hi : Lookup V (AeVal.emb init) v]
    (hF : ∀ st acc, F (st, acc) = next st >>= K acc)
    (hnone : ∀ acc r, K acc (none, r) = .ok (.done acc))
    (hsome : ∀ acc i r, (it.item i >>= fun x => K acc (some x, r)) =
      f acc i >>= fun a => .ok (.cont (r, a)))
    (hb : ∀ (i : Usize) (acc : σ),
      CompleteG single (f acc i) (vCons acc (vCons i (vCons cnt V))) pb) :
    CompleteG single (HaxLean.Aeneas.Std.loop F (st₀, init)) V
      (.var (litE cnt) (.forLoop .here (.cons v.there .nil) pb (.ret (.cons .here .nil)))) := by
  intro W hW
  have hn : cnt.val < 2 ^ 64 := lt64 cnt
  rw [nfToRustM, aeExpr_litE, bind_tc_ok, nfToRustM] at hW
  have hc : HasWord64.toNat (d := nfDialect)
      ((Ctxt.Var.here (Γ := Γ)).lookup
        (Valuation.extend (t := NfTy.word 64) V (embW cnt))) = cnt.val := by
    change (BitVec.ofNat 64 cnt.val).toNat = cnt.val
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hinit : Expr.lookupArgs (HVector.cons v.there HVector.nil)
      (Valuation.extend (t := NfTy.word 64) V (embW cnt)) = single init := by
    change HVector.cons (v.lookup V) HVector.nil = _
    rw [hi.eq]
  rw [hc, hinit, List.range_eq_range', extend_eq] at hW
  obtain ⟨acc, hacc, hW⟩ := rustM_bind_ok hW
  obtain ⟨y, hy, rfl⟩ := foldRange_complete (vCons cnt V) pb f hb cnt.val 0 init acc
    (by have := cnt.bv.isLt; simp only [UScalar.val] at this ⊢; omega) hacc
  rw [nfToRustM] at hW
  cases hW
  refine ⟨y, ?_, rfl⟩
  rw [← it.h0, loop_indexed it F K f hF hnone hsome cnt.val 0 init (by omega)]
  exact hy

/-! ## The elaborator -/

namespace CompleteMeta

open Lean Meta Elab Term

/-- The complete twin of a node of the reader's proof terms: the congruence lemmas, the passing
    conditions and the exact expression instances. -/
meta def twinOf (c : Name) : Option Name :=
  [(``ReifyG.of_eq, ``Complete.of_eq),
   (``Reify.bind, ``complete_bind),
   (``Reify.bindLit, ``Complete.bindLit),
   (``Reify.okLit, ``Complete.okLit),
   (``Reify.okExpr, ``complete_okExpr),
   (``Reify.letE, ``Complete.letE),
   (``Reify.letLit, ``Complete.letLit),
   (``Reify.iteLt, ``Complete.iteLt),
   (``Reify.iteBit, ``Complete.iteBit),
   (``Reify.guardP, ``Complete.guardP),
   (``Reify.guardS, ``Complete.guardS),
   (``Reify.assert, ``complete_assert),
   (``Reify.iteFailElse, ``Complete.iteFailElse),
   (``Reify.iteFail, ``Complete.iteFail),
   (``Reify.argBit, ``Complete.argBit),
   (``Reify.rangeForLoop, ``Complete.rangeForLoop),
   (``Reify.indexedForLoop, ``Complete.indexedForLoop),
   (``pass_massert, ``massert_pass),
   (``pass_iteFailElse, ``iteFailElse_pass),
   (``pass_iteFail, ``iteFail_pass),
   (``reifyE_add, ``complete_add),
   (``reifyE_sub, ``complete_sub),
   (``reifyE_mul, ``complete_mul),
   (``reifyE_band, ``complete_band),
   (``reifyE_bor, ``complete_bor),
   (``reifyE_bxor, ``complete_bxor),
   (``reifyE_index, ``complete_index),
   (``reifyE_update, ``complete_update)].lookup c

/-- The judgement a proof proves, under its binders: `some true` for `ReifyG`, `some false`
    for `ReifyE`, `none` for any other proposition. -/
meta def judgementOf (t : Expr) : MetaM (Option Bool) := do
  forallTelescope (← inferType t) fun _ b => do
    let b ← whnfR b
    if b.isAppOfArity ``ReifyG 7 then return some true
    if b.isAppOfArity ``ReifyE 6 then return some false
    return none

/-- The head constant of a term under its binders. -/
meta def headConst? (t : Expr) : MetaM (Option Name) :=
  lambdaTelescope t fun _ b => return b.getAppFn.constName?

/-- **The walk.** The complete twin of a proof `t` of a judgement or a passing condition:
    under binders, the twin of its head applied to the arguments, each judgement or passing
    condition among them replaced by its twin; a judgement at a value `ok y` by
    `completeG_of_ok` or `completeE_of_ok`; an auxiliary theorem unfolded. Any other node is a
    refusal naming it. -/
meta partial def toComplete (t : Expr) : MetaM Expr := do
  let t ← instantiateMVars t
  if t.isLambda then
    return ← lambdaTelescope t fun xs b => do mkLambdaFVars xs (← toComplete b)
  let t := t.headBeta
  let fn := t.getAppFn
  let some c := fn.constName? |
    throwError "completeAeneas%: no complete twin of the node{indentExpr t}"
  if c == ``Reify.loop then
    throwError "completeAeneas%: the while loop `Reify.loop` has no complete twin"
  if let some c' := twinOf c then
    let args ← t.getAppArgs.mapM fun a => do
      if (← judgementOf a).isSome then return ← toComplete a
      if let some h ← headConst? a then
        if (twinOf h).isSome then return ← toComplete a
      return a
    return mkAppN (mkConst c' fn.constLevels!) args
  let ty ← whnfR (← inferType t)
  if ty.isAppOfArity ``ReifyG 7 || ty.isAppOfArity ``ReifyE 6 then
    let m ← whnfR (if ty.isAppOfArity ``ReifyG 7 then ty.getArg! 3 else ty.getArg! 2)
    if m.isAppOfArity ``HaxLean.Aeneas.Std.RustM.ok 2 then
      return ← mkAppM (if ty.isAppOfArity ``ReifyG 7 then ``completeG_of_ok
        else ``completeE_of_ok) #[t]
  throwError "completeAeneas%: no complete twin of the node `{c}`{indentExpr t}"

/-- The Aeneas function `f` of the soundness statement `S` of `reifyAeneas% f`: the head of
    the computation of the judgement under the binders of `S`. -/
meta def fnOfStatement (S : Expr) : MetaM Name :=
  lambdaTelescope S fun _ b => forallTelescope b fun _ j => do
    let j ← whnfR j
    unless j.isAppOfArity ``ReifyG 7 do
      throwError "completeAeneas%: not a soundness statement of `reifyAeneas%`{indentExpr j}"
    let some f := (j.getArg! 3).getAppFn.constName? |
      throwError "completeAeneas%: no function in the statement{indentExpr j}"
    return f

/-- `completeAeneas% R`: for the value `R` of `reifyAeneas% f`, the proof of
    `∀ xs, CompleteG E (f xs) V R.prog` by the twins of the nodes of the proof of `R.sound`.
    When that proof is an auxiliary theorem whose body is not available (a definition of
    another module), the reader is run again on `f` and its proof term is walked. -/
elab "completeAeneas% " R:term : term => do
  let r ← instantiateMVars (← elabTerm R none)
  let rv ← whnf r
  unless rv.isAppOfArity ``Reified.mk 5 do
    throwError "completeAeneas%: not a value of `reifyAeneas%`{indentExpr rv}"
  let sound ← instantiateMVars (rv.getArg! 4)
  let sound ← if sound.isLambda then pure sound else do
    let f ← fnOfStatement (rv.getArg! 2)
    let fresh ← whnf (← instantiateMVars
      (← elabTerm (← `(reifyAeneas% $(mkCIdent f))) none))
    unless fresh.isAppOfArity ``Reified.mk 5 do
      throwError "completeAeneas%: the reader returned no value{indentExpr fresh}"
    instantiateMVars (fresh.getArg! 4)
  let prf ← toComplete sound
  let prog ← mkAppM ``Reified.prog #[r]
  let ty ← forallTelescope (← inferType prf) fun xs b => do
    mkForallFVars xs (mkApp b.appFn! prog)
  let prf ← mkExpectedTypeHint prf ty
  check prf
  return prf

end CompleteMeta

end CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyComplete
