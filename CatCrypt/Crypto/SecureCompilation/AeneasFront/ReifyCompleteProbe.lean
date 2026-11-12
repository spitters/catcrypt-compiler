/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify

/-!
# The complete direction of the reading of `reifyAeneas%`

The judgements `ReifyE` and `ReifyG` of `AeneasFront/Reify.lean` state soundness: a value of
the Aeneas computation `m` is, mapped to NF values, the value of the reading. This module states
the converse, `CompleteE` and `CompleteG`: a value `W` of the reading is the image of a value
of `m`. With the converse, a value of the reading (as an NF range checker establishes it)
gives `∃ y, m = .ok y`. The converse is proved here at the two shapes that carry the two kinds
of failure of the reader: a guard (`complete_guardS`, the abort arm has no value) and a checked
operation (`complete_add`, through `complete_call2`, the table call fails exactly when the
Aeneas operation does), with the bind and the result step that connect them.

## The `complete` field

The field of `ReifyE m V e` would be `complete : ∀ w, aeExpr e V = .ok w → ∃ y, m = .ok y ∧
AeVal.emb y = w`, and that of `ReifyG E m V p` would be `complete : ∀ W, nfToRustM p V = .ok W →
∃ y, m = .ok y ∧ E y = W`. Since the reader proves soundness at every value, `E y = W` follows
from soundness and determinism once `m = .ok y` is known; the content of the field is the
existence of `y`.

The congruence lemmas that need a converse hypothesis are the guards: `Reify.guard`,
`Reify.guardP` and `Reify.guardS` take `S → m = k` in place of the passing condition
`m = .ok y → S ∧ k = .ok y`, proved for the three shapes by `massert_pass`, `iteFailElse_pass`
and `iteFail_pass`. The conditions (`ReadCond`, `ReadBit`, `ReadWord`) are equations and need
no converse. The expression instances need none either: a law `aeCall2 f .. = op x y >>= ..`
is an equation, and `complete_call2` covers every instance of `reifyE_call2` (checked,
bitwise and wrapping operations); the calls of one and three arguments and `index`,
`array_update` are the same argument at their arity. The loops need the converse of the loop
equations: `Reify.rangeForLoop` and `Reify.indexedForLoop` by induction on the trip list of
`foldlM` (`foldRange_reify`, `loop_indexed`); `Reify.loop` (`whileLoop`) needs an induction on
the termination of the partial fixpoint `loop`, and the checker refuses `whileLoop` programs.

## Readings that accept more than their Aeneas term

The signed checked operations `reifyE_iadd`, `reifyE_isub`, `reifyE_imul` of
`AeneasFront/Signed.lean` read `x + y`, `x - y`, `x * y` at `IScalar ity` as the wrapping calls
`wrapping_add#w`, `wrapping_sub#w`, `wrapping_mul#w`. At `i8`, `x = 127` and `y = 1`, the
Aeneas `x + y` fails with an overflow, and the reading returns the word `128`, the pattern of
`-128`. `CompleteE` is false there. For the converse at these operations the reader reads the
overflow: the wrapping call `z`, a bit `ovf` of the signed overflow computed by table calls
(for the addition, the sign bit of `(x ^^^ z) &&& (y ^^^ z)`; for the multiplication, a
comparison of the widened product with the bounds of the width), and the guard of
`Reify.guardP` on `ovf`. The judgement of the operation is then a `ReifyG` prefix instead of
one `ReifyE` expression. The table has no checked signed name.

No other reading accepts more than its Aeneas term: the literals (`litE`, `LitOf`, the signed
literal `toU c`), the casts of the table, the signed comparisons through `sflip`, the wrapping
operations (Aeneas `ok` of the wrapped value), `index` and `array_update` (both fail exactly
when the Aeneas operation does) have readings that fail where the term fails. A literal or
value with several preimages under the embedding does not affect the converse, which asks only
for the existence of a value of `m`.

## Estimate of the converse over `Reify.lean` and `ReifyArrays.lean`

The two shapes, the bind and the result step take 15 lines each or fewer; `complete_call2`
covers about twenty instances at once. The converse as a family of classes beside `ReifyE` and
`ReifyG`, resolved on the program the reader returned, leaves `Reify.lean` unchanged. Parts:
expression laws at the arities 1, 2, 3 and `index`, `array_update`: 0.15 units; the congruence
lemmas without loops (binds, results, branches, guards, prefixes, Boolean arguments and
results, structures): 0.35; range and indexed loops: 0.3; the entry statement that composes
the two judgements: 0.2; the signed overflow guard in the reader with its soundness and
converse: 0.4. Total 1.4 units, of which 1.0 without the signed operations, whose functions the
checker then refuses.

## Main results

* `CompleteE`, `CompleteG`: the complete direction of the judgements
* `complete_call2`, `complete_add`: a call of two words, the checked addition
* `complete_guardS`, `complete_assert`: the guard, the assertion
* `complete_bind`, `complete_okExpr`: the bind, the value of an operation
* `massert_pass`, `iteFailElse_pass`, `iteFail_pass`: the converses of the passing conditions
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyComplete

open Aeneas.Std
open _root_.Hax (Value)
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

/-- The complete direction of `ReifyG`: a value of the reading of `p` at `V` is, by `E`, the
    image of a value of `m`. -/
def CompleteG {α : Type} {ts : List NfTy} (E : α → Valuation (d := nfDialect) ts)
    (m : RustM α) {Γ : Ctxt nfDialect} (V : Valuation Γ) (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ W, nfToRustM p V = .ok W → ∃ y, m = .ok y ∧ E y = W

/-- The complete direction of `ReifyE`: a value of the reading of `e` at `V` is the embedding
    of a value of `m`. -/
def CompleteE {α : Type} [AeVal α] (m : RustM α) {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (e : Expr nfDialect Γ (AeVal.nty α)) : Prop :=
  ∀ w, aeExpr e V = .ok w → ∃ y, m = .ok y ∧ AeVal.emb y = w

/-- **A call of two words with an operation law, complete direction.** A value of the reading
    of the call is the embedding of a value of the operation. -/
theorem complete_call2 {ty : UScalarTy} [Le64 ty] {Γ : Ctxt nfDialect} (f : String)
    (op : UScalar ty → UScalar ty → RustM (UScalar ty))
    (hf : ∀ x y, aeCall2 f (wordV x) (wordV y) = (op x y >>= fun z => .ok (wordV z)))
    (x y : UScalar ty) (V : Valuation Γ) (va vb : Var Γ (.word 64))
    (hx : va.lookup V = embW x) (hy : vb.lookup V = embW y) :
    CompleteE (op x y) V (callE2 f (.word 64) va vb) := by
  intro w hw
  change aeOp (.call f [.word 64, .word 64] (.word 64))
    (.cons (va.lookup V) (.cons (vb.lookup V) .nil)) = .ok w at hw
  unfold aeOp at hw
  rw [nfDenoteOp] at hw
  unfold aeTable at hw
  simp only [encAll] at hw
  rw [hx, hy, enc_embW, enc_embW, aeCallV, hf] at hw
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

/-- **The checked addition, complete direction**: `complete_call2` at the law
    `aeCall2_checked .add` of `reifyE_add`. -/
theorem complete_add {ty : UScalarTy} [CheckedTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    CompleteE (x + y) V (callE2 (checkedName .add ty) (.word 64) va vb) :=
  complete_call2 _ (AOp.aen .add) (aeCall2_checked .add rfl) x y V va vb hx.eq hy.eq

/-- **Bind, complete direction.** -/
theorem complete_bind {α β : Type} [AeVal α] {ts : List NfTy}
    {E : β → Valuation (d := nfDialect) ts} {Γ : Ctxt nfDialect}
    {e : Expr nfDialect Γ (AeVal.nty α)} {p : NFProg nfDialect (AeVal.nty α :: Γ) ts}
    (m : RustM α) (k : α → RustM β) (V : Valuation Γ) (he : CompleteE m V e)
    (hk : ∀ x, CompleteG E (k x) (vCons x V) p) :
    CompleteG E (m >>= k) V (.var e p) := by
  intro W hW
  rw [nfToRustM] at hW
  obtain ⟨a, ha, hW⟩ := rustM_bind_ok hW
  obtain ⟨x, hx, rfl⟩ := he a ha
  obtain ⟨y, hy, hE⟩ := hk x W hW
  exact ⟨y, by rw [hx, bind_tc_ok, hy], hE⟩

/-- **A value of an operation, complete direction.** -/
theorem complete_okExpr {α : Type} [AeVal α] {Γ : Ctxt nfDialect} (m : RustM α)
    (V : Valuation Γ) {e : Expr nfDialect Γ (AeVal.nty α)} (he : CompleteE m V e) :
    CompleteG single m V (.var e (.ret (.cons .here .nil))) := by
  intro W hW
  rw [nfToRustM] at hW
  obtain ⟨a, ha, hW⟩ := rustM_bind_ok hW
  obtain ⟨y, hy, rfl⟩ := he a ha
  rw [nfToRustM] at hW
  cases hW
  exact ⟨y, hy, rfl⟩

/-- **The guard on a condition read as one expression, complete direction.** When the guard
    passes under `S` (`m` is `k` under `S`), a value of the reading of the guard is a value of
    the reading of `k`, and the reading's abort arm returns no value. -/
theorem complete_guardS {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (S : Prop) (m k : RustM α) (V : Valuation Γ) [hs : ReadCond S V b e]
    (hpass : S → m = k) (hk : CompleteG E k (vCons (!b) (vCons b V)) pk) :
    CompleteG E m V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) := by
  intro W hW
  rw [nfToRustM, hs.sound, bind_tc_ok, extend_eq, nfToRustM,
    aeExpr_notE .here _ b rfl, bind_tc_ok, extend_eq, nfToRustM] at hW
  cases b
  · simp only [Bool.not_false, nfToRustM_abortArm] at hW
    cases hW
  · rw [hpass (hs.iff.mp rfl)]
    exact hk W hW

/-- The converse of `pass_massert`: under `P`, `massert P >>= k` is `k ()`. -/
theorem massert_pass {α : Type} (P : Prop) [Decidable P] (k : Unit → RustM α) (h : P) :
    (massert P >>= k) = k () := by
  simp only [massert, h, ite_true, bind_tc_ok]

/-- The converse of `pass_iteFailElse`. -/
theorem iteFailElse_pass {α : Type} (c : Prop) [Decidable c] (k : RustM α) (err : Error)
    (h : c) : (if c then k else .fail err) = k := by
  grind

/-- The converse of `pass_iteFail`. -/
theorem iteFail_pass {α : Type} (c : Prop) [Decidable c] (err : Error) (k : RustM α)
    (h : ¬ c) : (if c then .fail err else k) = k := by
  grind

/-- **An assertion `massert P`, complete direction**: `complete_guardS` at `massert_pass`. -/
theorem complete_assert {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (P : Prop) [Decidable P] (k : Unit → RustM α) (V : Valuation Γ) [ReadCond P V b e]
    (hk : CompleteG E (k ()) (vCons (!b) (vCons b V)) pk) :
    CompleteG E (massert P >>= k) V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  complete_guardS P _ (k ()) V (massert_pass P k) hk

end CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyComplete
