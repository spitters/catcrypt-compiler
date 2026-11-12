/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyArrays
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.EntryStruct

/-!
# `reifyAeneas%` at structures of scalars

A structure of scalars is held in the NF program as one variable per field. `reifyAeneas%`
binds the fields of a structure argument `s` as `vCons (S.f₁ s) (… V)`, so that a projection
`S.fᵢ s` in the body is a variable by the `Lookup` instances. A structure result is the array
of its field words, written into an out-region of `k` words, the ghost first argument `out` of
the reading: the result map `structRes` sends a structure value to the array of its field
words (`wordsArr`), and the value `ok y` is read by `Reify.okStruct` as the program
`storeFields` that writes the field words of `y` into `out` by `array_update` at the literal
indices `0, …, k - 1` and returns it.

## Main definitions

* `LookupAll`: variables holding a list of words
* `updE`, `storeFields`: the update of an array at a variable index, the stores of a list of
  words from an index on
* `setFrom`: the Aeneas array with its entries from an index on replaced
* `structRes`: the result map of a structure result

## Main results

* `usz_val_small`: a `usize` literal below `2 ^ 32` has its value
* `aeExpr_updE`, `nfToRustM_storeFields`: the reading of the stores
* `setFrom_zero`: the stores of `k` words into an array of `k` words give the array of the
  words
* `Reify.okStruct`: the value `ok y` of a structure result
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

/-- A `usize` literal below `2 ^ 32` has its value. -/
theorem usz_val_small {j : Nat} (h : j < 2 ^ 32) : (usz j).val = j := by
  apply usz_val
  rcases System.Platform.numBits_eq with h' | h' <;> simp [UScalarTy.numBits, h'] <;> omega

/-- The variables `vs` hold the words `ws` at `V`. -/
class LookupAll {Γ : Ctxt nfDialect} (V : Valuation Γ) (ws : List (BitVec 64))
    (vs : outParam (List (Var Γ (.word 64)))) : Prop where
  /-- The variables read the words. -/
  eq : vs.map (fun v => v.lookup V) = ws

instance lookupAllNil {Γ : Ctxt nfDialect} (V : Valuation Γ) : LookupAll V [] [] := ⟨rfl⟩

instance lookupAllCons {Γ : Ctxt nfDialect} (V : Valuation Γ) (w : BitVec 64)
    (ws : List (BitVec 64)) {v : Var Γ (.word 64)} {vs : List (Var Γ (.word 64))}
    [h : Lookup (t := .word 64) V w v] [hs : LookupAll V ws vs] :
    LookupAll V (w :: ws) (v :: vs) := ⟨by rw [List.map_cons, hs.eq, h.eq]⟩

/-! ## The stores -/

/-- The call `array_update` of an array, an index and a word, at variables. -/
def updE {Γ : Ctxt nfDialect} {n : Nat} (va : Var Γ (.arr n (.word 64)))
    (vi vx : Var Γ (.word 64)) : Expr nfDialect Γ (.arr n (.word 64)) :=
  ⟨.call "array_update" [.arr n (.word 64), .word 64, .word 64] (.arr n (.word 64)), rfl,
    .cons va (.cons vi (.cons vx .nil))⟩

/-- The stores of the words of the variables `vs` into the array of the variable `o` at the
    indices from `i` on, each index bound as a literal, and the return of the array. -/
def storeFields {n : Usize} : {Γ : Ctxt nfDialect} → Var Γ (.arr n.val (.word 64)) →
    List (Var Γ (.word 64)) → Nat → NFProg nfDialect Γ [.arr n.val (.word 64)]
  | _, o, [], _ => .ret (.cons o .nil)
  | _, o, v :: vs, i =>
      .var (litE (usz i)) (.var (updE o.there .here v.there)
        (storeFields .here (vs.map fun w => w.there.there) (i + 1)))
termination_by _ _ vs _ => vs.length
decreasing_by simp only [List.length_map, List.length_cons]; omega

/-- The Aeneas array `a` with the entries from the index `i` on replaced by `xs`. -/
def setFrom {n : Usize} : Aeneas.Std.Array U64 n → Nat → List U64 → Aeneas.Std.Array U64 n
  | a, _, [] => a
  | a, i, x :: xs => setFrom (a.set (usz i) x) (i + 1) xs

/-- An update at an index below the length is the array with the entry replaced. -/
theorem arrUpdate_eq_set {n : Usize} (a : Aeneas.Std.Array U64 n) (i : Usize) (x : U64)
    (h : i.val < n.val) : a.update i x = .ok (a.set i x) := by
  have hl : i.val < a.val.length := by rw [a.property]; exact h
  unfold Aeneas.Std.Array.update
  rw [Aeneas.Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem hl]
  rfl

/-- The update of an array at an index below its length. -/
theorem aeExpr_updE {Γ : Ctxt nfDialect} {n : Usize} (va : Var Γ (.arr n.val (.word 64)))
    (vi vx : Var Γ (.word 64)) (V : Valuation Γ) (a : Aeneas.Std.Array U64 n) (i : Usize)
    (x : U64)
    (ha : va.lookup V = embA a) (hi : vi.lookup V = embW i) (hx : vx.lookup V = embW x)
    (hlt : i.val < n.val) : aeExpr (updE va vi vx) V = .ok (embA (a.set i x)) :=
  (@reifyE_update .U64 _ n Γ a i x V va vi vx ⟨ha⟩ ⟨hi⟩ ⟨hx⟩).sound _
    (arrUpdate_eq_set a i x hlt)

theorem embW_mk (b : BitVec 64) : embW (⟨b⟩ : U64) = b := by
  unfold embW
  simp_all

/-- **The reading of the stores**: at variables holding an array `a` and words `bs`, the
    stores from the index `i` return the array `a` with the entries from `i` on replaced by
    `bs`. -/
theorem nfToRustM_storeFields {n : Usize} : ∀ {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (o : Var Γ (.arr n.val (.word 64))) (a : Aeneas.Std.Array U64 n) (vs : List (Var Γ (.word 64)))
    (bs : List (BitVec 64)) (i : Nat), o.lookup V = embA a →
    vs.map (fun v => v.lookup V) = bs → i + bs.length ≤ n.val →
    nfToRustM (storeFields o vs i) V =
      .ok (.cons (embA (setFrom a i (bs.map fun b => ⟨b⟩))) .nil)
  | _, V, o, a, [], bs, i, ho, hvs, _ => by
    subst hvs
    rw [storeFields, nfToRustM]
    change RustM.ok (HVector.cons (o.lookup V) HVector.nil) = _
    rw [ho]
    rfl
  | _, V, o, a, v :: vs, bs, i, ho, hvs, hi => by
    cases bs with
    | nil => simp at hvs
    | cons b bs =>
      rw [List.map_cons, List.cons.injEq] at hvs
      obtain ⟨hv, hvs⟩ := hvs
      simp only [List.length_cons] at hi
      have hi' : i < n.val := by omega
      have hiu : (usz i).val = i := usz_val (lt_trans hi' (UScalar.hBounds n))
      have hu := aeExpr_updE
        (show Var (d := nfDialect) (NfTy.word 64 :: _) (NfTy.arr n.val (.word 64)) from o.there)
        .here v.there
        (HVector.cons (embW (usz i)) V) a (usz i) ⟨b⟩ ho rfl
        (by change v.lookup V = _; rw [hv, embW_mk]) (by rw [hiu]; exact hi')
      rw [storeFields, nfToRustM, aeExpr_litE, bind_tc_ok, extend_eq, nfToRustM, hu,
        bind_tc_ok, extend_eq]
      exact nfToRustM_storeFields _ .here (a.set (usz i) ⟨b⟩) _ bs (i + 1) rfl
        (by rw [List.map_map]; exact hvs) (by omega)
termination_by _ _ _ _ vs => vs.length
decreasing_by simp only [List.length_map, List.length_cons]; omega

theorem setFrom_val {n : Usize} : ∀ (a : Aeneas.Std.Array U64 n) (i : Nat) (xs : List U64),
    i + xs.length = a.val.length → (setFrom a i xs).val = a.val.take i ++ xs
  | a, i, [], h => by
    simp only [setFrom, List.length_nil, Nat.add_zero] at h ⊢
    rw [h, List.take_length, List.append_nil]
  | a, i, x :: xs, h => by
    have hi : i < a.val.length := by simp only [List.length_cons] at h; omega
    have hn : (usz i).val = i :=
      usz_val (lt_of_lt_of_le hi (by rw [a.property]; exact (UScalar.hBounds n).le))
    have hl : i + 1 + xs.length = (a.set (usz i) x).val.length := by
      simp only [Aeneas.Std.Array.set_val_eq, List.length_set, List.length_cons] at h ⊢
      omega
    rw [setFrom, setFrom_val _ _ _ hl, Aeneas.Std.Array.set_val_eq, hn,
      List.set_eq_take_append_cons_drop, ite_eq_left hi]
    simp [List.take_append, Nat.le_of_lt hi]

/-- The stores of `k` words from the index `0` into an array of `k` words give the array of
    the words. -/
theorem setFrom_zero {k : Nat} (hk : k < 2 ^ 32) (a : Aeneas.Std.Array U64 (usz k))
    (bs : List (BitVec 64)) (h : bs.length = k) :
    setFrom a 0 (bs.map fun b => ⟨b⟩) = wordsArr (usz k) bs (h.trans (usz_val_small hk).symm) := by
  apply Subtype.ext
  rw [setFrom_val _ _ _ (by rw [a.property, usz_val_small hk, List.length_map, h, Nat.zero_add])]
  simp [wordsArr]

/-! ## Structure results -/

/-- **The result map of a structure result** of `k` fields with the field words `ws`: the array
    of the field words. The out-region `out` is the ghost argument of the reading into which
    the program writes the words; the value does not depend on it. -/
def structRes {S : Type} (k : Nat) (hk : k < 2 ^ 32) (out : Aeneas.Std.Array U64 (usz k))
    (ws : S → List (BitVec 64)) (hws : ∀ y, (ws y).length = k) (y : S) :
    Valuation (d := nfDialect) [.arr (usz k).val (.word 64)] :=
  have _ := out
  .cons (embA (wordsArr (usz k) (ws y) ((hws y).trans (usz_val_small hk).symm))) .nil

/-- **A value of a structure result**: the stores of its field words into the out-region,
    from the index `0`. -/
instance Reify.okStruct {S : Type} {Γ : Ctxt nfDialect} (k : Nat) (hk : k < 2 ^ 32)
    (out : Aeneas.Std.Array U64 (usz k)) (ws : S → List (BitVec 64))
    (hws : ∀ y, (ws y).length = k) (y : S) (V : Valuation Γ)
    {o : Var Γ (.arr (usz k).val (.word 64))} {vs : List (Var Γ (.word 64))}
    [ho : Lookup V (embA out) o] [hvs : LookupAll V (ws y) vs] :
    ReifyG (structRes k hk out ws hws) (.ok y) V (storeFields o vs 0) where
  sound r hr := by
    cases hr
    rw [nfToRustM_storeFields V o out vs (ws y) 0 ho.eq hvs.eq
      (by rw [Nat.zero_add, hws y, usz_val_small hk]), setFrom_zero hk out (ws y) (hws y)]
    rfl

end CatCrypt.Crypto.SecureCompilation.AeneasFront
