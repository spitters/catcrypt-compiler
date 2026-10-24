/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.TileBridge
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF

/-!
# Elementwise loop bodies and their lane form

The body of a counted loop over `jasminDialect` is elementwise when it is straight-line, reads
arrays only by `stackLoad` at the trip index, writes arrays only by `stackStore` at the trip
index, and computes the stored values from the loaded values and loop-invariant variables.
`stripBody n w` maps such a body to a program of `jasminTileMem` that performs `n` consecutive
iterations at once: a load becomes `tileLoad` at the index of the first of the `n` iterations,
a store becomes `tileStore`, and the bindings between them (the kernel) are lifted to the lanes
of tiles of `n` lanes of `w` bits with the leaves of `LaneMapNF` (`tileOp?`, `scArgs`).

The translation runs along an environment `SEnv` that gives each source variable its forms in
the target context: the scalar and tile forms of `LaneMapNF.LVar`, an array form that records
the array variable of the entry context the array descends from and whether it was stored, and
the mark of the trip index.

* The trip index has no scalar and no tile form, so it occurs only as the index of a load or a
  store.
* A load reads an array that was not stored in the body; a store writes one.
* A lane operation with one tile operand and one loop-invariant scalar operand binds the
  `tileSplat` of the scalar first.
* An operation whose operands all have scalar forms is kept in the scalar summand.
* The body returns, at each carried position, the carried array or an array stored from it.
* A counted loop, a branch, an exit-flag loop and a call are refused.

## Main definitions

* `ArrForm`, `SForm`, `SEnv` — the forms of a source variable and environments.
* `outOk`, `TupRel` — the relation of the arrays a scalar iteration and the lane form return.
* `SRel` — the relation of a scalar valuation at lane `j` to a target valuation.
* `loadOf?`, `storeOf?`, `splatOf?`, `stripBody` — the translation.
* `bodyEnv`, `laneBody` — the environment at the entry of a loop body, and the lane form of a
  body.
* `Elemwise`, `elemwise?` — the recognition of a counted loop with an elementwise body.
* `ArrAddr` — the leakage models in which a load and a store emit their index.
* `evCount` — the number of events of a straight-line program.

## Main results

* `stripBody_lane` — for every lane `j`, the scalar body at the index `B + j` and the lane
  form at the index `B` both run; the arrays the scalar body returns are its entry arrays
  written at `B + j` with the elements the lane form's arrays hold there; the lane form's arrays
  equal their entry arrays outside the residues of `B, …, B + n - 1`; at lane `0` the events
  are equal; and the scalar events number `evCount`.
* `bodyEnv_rel` — the entry environment relates the entry valuations.
* `Elemwise.prog_eq`, `Elemwise.lifted` — a recognised program is the counted loop of the
  parts returned, and the returned lane form is `laneBody` of its body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneStripKernel

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.TileBridge
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
  (hvAppend inlHom inrHom lookup_inlHom lookup_inrHom)
open Ctxt (Var Valuation)

attribute [local instance] jasminTileDenote jasminTileMemDenote

/-- A variable of `jasminTileDialect` read as a variable of `jasminTileMem`. -/
abbrev memVar {Δ : Ctxt jasminTileDialect} {t : jasminTileDialect.Ty}
    (v : Var (d := jasminTileDialect) Δ t) : Var (d := jasminTileMem) Δ t :=
  castVar v

/-- Looking up a variable read in `jasminTileMem` gives its lookup. -/
theorem lookup_memVar {Δ : Ctxt jasminTileDialect} {t : jasminTileDialect.Ty}
    (v : Var (d := jasminTileDialect) Δ t) (W : Valuation (d := jasminTileDialect) Δ) :
    (memVar v).lookup (d := jasminTileMem) W = v.lookup W :=
  lookup_castVar v W

/-- An argument vector of `jasminTileDialect` read in `jasminTileMem`. -/
abbrev memArgs {Δ : Ctxt jasminTileDialect} {ts : List jasminTileDialect.Ty}
    (vs : HVector (fun t => Var (d := jasminTileDialect) Δ t) ts) :
    HVector (fun t => Var (d := jasminTileMem) Δ t) ts :=
  castArgs vs

/-- Resolving arguments read in `jasminTileMem` gives their resolution. -/
theorem lookupArgs_memArgs {Δ : Ctxt jasminTileDialect} {ts : List jasminTileDialect.Ty}
    (vs : HVector (fun t => Var (d := jasminTileDialect) Δ t) ts)
    (W : Valuation (d := jasminTileDialect) Δ) :
    Expr.lookupArgs (d := jasminTileMem) (memArgs vs) W = Expr.lookupArgs vs W :=
  lookupArgs_castArgs vs W

/-! ## 1. Stack arrays -/

/-- Writing at a position the element read there leaves the array unchanged. -/
theorem stackSet_stackGet_self {w N : Nat} (a : Fin N → BitVec w) (k : Nat) :
    stackSet a k (stackGet a k) = a := by
  cases N with
  | zero => exact funext fun p => p.elim0
  | succ m =>
      funext p
      simp only [stackSet, stackGet]
      split
      · rename_i hp
        rw [hp]
      · rfl

/-- The element read at a position depends on its residue only. -/
theorem stackGet_congr_mod {w N : Nat} (a : Fin N → BitVec w) {k k' : Nat}
    (h : k % N = k' % N) : stackGet a k = stackGet a k' := by
  cases N with
  | zero => rfl
  | succ m =>
      simp only [stackGet]
      exact congrArg a (Fin.ext h)

/-- Two arrays with the same element at every position are equal. -/
theorem stackArr_ext {w N : Nat} (a b : Fin N → BitVec w)
    (h : ∀ k, stackGet a k = stackGet b k) : a = b :=
  funext fun p => by rw [← stackGet_id a p, ← stackGet_id b p]; exact h p.val

/-! ## 2. Forms and environments -/

section Forms

variable (n w : Nat)

/-- The array form of a source variable of type `t`: its variable in the target context, the
    array variable of the entry context `Γ₀` it descends from, and whether it is the result of
    a store. -/
structure ArrForm (Γ₀ : Ctxt jasminDialect) (Δ : Ctxt jasminTileDialect) (t : JasminTy) where
  /-- The variable of the target context. -/
  tv : Var Δ (Sum.inl t)
  /-- The array of the entry context the variable descends from. -/
  org : Var Γ₀ t
  /-- Whether the variable is the result of a store. -/
  stored : Bool

/-- The forms of a source variable of type `t` in the target context `Δ`: the scalar and tile
    forms, an array form, and the mark of the trip index. -/
structure SForm (Γ₀ : Ctxt jasminDialect) (Δ : Ctxt jasminTileDialect) (t : JasminTy) where
  /-- The scalar and tile forms. -/
  lv : LVar n w Δ t
  /-- The array form. -/
  arr : Option (ArrForm Γ₀ Δ t)
  /-- The mark of the trip index. -/
  isIdx : Bool

/-- An environment: the forms of every variable of `Γ` in `Δ`. -/
abbrev SEnv (Γ₀ Γ : Ctxt jasminDialect) (Δ : Ctxt jasminTileDialect) : Type :=
  ∀ t : JasminTy, Var Γ t → SForm n w Γ₀ Δ t

variable {n w}
variable {Γ₀ Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} {t : JasminTy}

/-- An array form under one more binding of the target context. -/
def ArrForm.wk (u : jasminTileDialect.Ty) (a : ArrForm Γ₀ Δ t) : ArrForm Γ₀ (u :: Δ) t :=
  ⟨.there a.tv, a.org, a.stored⟩

/-- The forms of a variable under one more binding of the target context. -/
def SForm.wk (u : jasminTileDialect.Ty) (x : SForm n w Γ₀ Δ t) : SForm n w Γ₀ (u :: Δ) t :=
  ⟨x.lv.wk u, x.arr.map (ArrForm.wk u), x.isIdx⟩

/-- The tile form alone. -/
def SForm.tile (x : Var Δ (Sum.inr (TileTy.tile n w))) : SForm n w Γ₀ Δ t :=
  ⟨⟨none, some x⟩, none, false⟩

/-- The scalar form alone. -/
def SForm.scalar (x : Var Δ (Sum.inl t)) : SForm n w Γ₀ Δ t :=
  ⟨⟨some x, none⟩, none, false⟩

/-- The array form alone. -/
def SForm.array (a : ArrForm Γ₀ Δ t) : SForm n w Γ₀ Δ t :=
  ⟨⟨none, none⟩, some a, false⟩

/-- The trip index: no form, and the mark. -/
def SForm.index : SForm n w Γ₀ Δ t :=
  ⟨⟨none, none⟩, none, true⟩

/-- No form. -/
def SForm.absent : SForm n w Γ₀ Δ t :=
  ⟨⟨none, none⟩, none, false⟩

/-- The environment under one more binding of the target context. -/
def SEnv.wk (σ : SEnv n w Γ₀ Γ Δ) (u : jasminTileDialect.Ty) : SEnv n w Γ₀ Γ (u :: Δ) :=
  fun t v => (σ t v).wk u

/-- The environment under a source binding with the forms `f` over one more binding of the
    target context. -/
def SEnv.bind (σ : SEnv n w Γ₀ Γ Δ) (u : jasminTileDialect.Ty)
    (f : SForm n w Γ₀ (u :: Δ) t) : SEnv n w Γ₀ (t :: Γ) (u :: Δ)
  | _, .here => f
  | _, .there v => (σ _ v).wk u

/-- The scalar and tile forms of an environment. -/
def SEnv.lane (σ : SEnv n w Γ₀ Γ Δ) : Env n w Γ Δ :=
  fun t v => (σ t v).lv

end Forms

/-! ## 3. The relations -/

section Rel

variable {n w : Nat}

/-- An array type with at least `n` elements. -/
def laneFits (n : Nat) : JasminTy → Prop
  | .stackArr _ N => n ≤ N
  | _ => False

/-- The entry arrays `O` of a scalar iteration at lane `j` and `O'` of the lane form have the
    same element at the position `B + j`. -/
def arrAt (j : Fin n) (B : Nat) : (t : JasminTy) → ⟦t⟧ → ⟦t⟧ → Prop
  | .stackArr _ _, O, O' => stackGet O (B + j.val) = stackGet O' (B + j.val)
  | _, _, _ => True

/-- The arrays returned at one carried position. `S`, returned by the scalar iteration at lane
    `j`, is its entry array `O` written at `B + j` with the element `S'` holds there; `S'`,
    returned by the lane form, has the elements of its entry array `O'` outside the residues
    of `B, …, B + n - 1`; and the array has at least `n` elements. -/
def outOk (j : Fin n) (B : Nat) : (t : JasminTy) → ⟦t⟧ → ⟦t⟧ → ⟦t⟧ → ⟦t⟧ → Prop
  | .stackArr _ N, O, O', S, S' =>
      n ≤ N ∧ S = stackSet O (B + j.val) (stackGet S' (B + j.val)) ∧
        ∀ k, (∀ i : Fin n, (B + i.val) % N ≠ k % N) → stackGet S' k = stackGet O' k
  | _, _, _, _, _ => False

/-- The relation of an array form: a stored array satisfies `outOk`, and an array that was not
    stored is its entry array on both sides. -/
def arrOk (j : Fin n) (B : Nat) (t : JasminTy) (stored : Bool) (S S' O O' : ⟦t⟧) : Prop :=
  if stored then outOk j B t O O' S S' else laneFits n t ∧ S = O ∧ S' = O'

/-- An array form whose entry arrays agree at `B + j` satisfies `outOk`. -/
theorem outOk_of_arrOk {j : Fin n} {B : Nat} {t : JasminTy} {b : Bool} {S S' O O' : ⟦t⟧}
    (hO : arrAt j B t O O') (h : arrOk j B t b S S' O O') : outOk j B t O O' S S' := by
  cases b with
  | true => exact h
  | false =>
      obtain ⟨hf, rfl, rfl⟩ := h
      cases t with
      | stackArr w' N =>
          refine ⟨hf, ?_, fun _ _ => rfl⟩
          have h1 : stackGet S (B + j.val) = stackGet S' (B + j.val) := hO
          rw [← h1, stackSet_stackGet_self]
      | reg _ => exact hf
      | inlineInt => exact hf
      | bool => exact hf

/-- The relation of the tuples a scalar iteration at lane `j` and the lane form return, by
    position, with the entry arrays given by position. -/
def TupRel (j : Fin n) (B : Nat) : (ts : List JasminTy) →
    (∀ t, Var (d := jasminDialect) ts t → ⟦t⟧) → (∀ t, Var (d := jasminDialect) ts t → ⟦t⟧) →
    Valuation (d := jasminDialect) ts →
    Valuation (d := jasminTileDialect) (ts.map (Sum.inl (β := TileTy))) → Prop
  | [], _, _, _, _ => True
  | t :: ts, o, o', S, S' =>
      outOk j B t (o t .here) (o' t .here) S.head S'.head ∧
        TupRel j B ts (fun t x => o t (.there x)) (fun t x => o' t (.there x)) S.tail S'.tail

variable {Γ₀ Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}

/-- The forms `f` of a variable hold of the scalar value `y` at lane `j` in the target
    valuation `W`: a scalar form reads `y`, lane `j` of a tile form is `y`, an array form
    satisfies `arrOk` at the entry arrays `O` and `O'`, and the trip index is `B + j`. -/
def FormOk (j : Fin n) (B : Nat) (O O' : ∀ t, Var Γ₀ t → ⟦t⟧) {t : JasminTy}
    (f : SForm n w Γ₀ Δ t) (y : ⟦t⟧) (W : Valuation Δ) : Prop :=
  (∀ v', f.lv.sc = some v' → v'.lookup W = y) ∧
  (∀ v', f.lv.ln = some v' → laneRd j t (v'.lookup W) = y) ∧
  (∀ a, f.arr = some a → arrOk j B t a.stored y (a.tv.lookup W) (O t a.org) (O' t a.org)) ∧
  (f.isIdx = true → HEq y (BitVec.ofNat 64 (B + j.val)))

/-- A source valuation `V` at lane `j` and a target valuation `W` are related along `σ`. -/
def SRel (j : Fin n) (B : Nat) (O O' : ∀ t, Var Γ₀ t → ⟦t⟧) (σ : SEnv n w Γ₀ Γ Δ)
    (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  ∀ (t : JasminTy) (v : Var Γ t), FormOk j B O O' (σ t v) (v.lookup V) W

variable {j : Fin n} {B : Nat} {O O' : ∀ t, Var Γ₀ t → ⟦t⟧}

theorem FormOk.wk {t : JasminTy} {f : SForm n w Γ₀ Δ t} {y : ⟦t⟧} {W : Valuation Δ}
    (h : FormOk j B O O' f y W) (u : jasminTileDialect.Ty) (x : ⟦u⟧) :
    FormOk j B O O' (f.wk u) y (Valuation.extend (d := jasminTileDialect) W x) := by
  refine ⟨fun v' hv => ?_, fun v' hv => ?_, fun a ha => ?_, h.2.2.2⟩
  · obtain ⟨v0, h0, rfl⟩ := Option.map_eq_some_iff.mp hv
    exact h.1 v0 h0
  · obtain ⟨v0, h0, rfl⟩ := Option.map_eq_some_iff.mp hv
    exact h.2.1 v0 h0
  · obtain ⟨a0, h0, rfl⟩ := Option.map_eq_some_iff.mp ha
    exact h.2.2.1 a0 h0

theorem SRel.wk {σ : SEnv n w Γ₀ Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (h : SRel j B O O' σ V W) (u : jasminTileDialect.Ty) (x : ⟦u⟧) :
    SRel j B O O' (σ.wk u) V (Valuation.extend (d := jasminTileDialect) W x) :=
  fun t v => (h t v).wk u x

theorem SRel.bind {σ : SEnv n w Γ₀ Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (h : SRel j B O O' σ V W) (u : jasminTileDialect.Ty) (x : ⟦u⟧) {t : JasminTy}
    (f : SForm n w Γ₀ (u :: Δ) t) (y : ⟦t⟧)
    (hf : FormOk j B O O' f y (Valuation.extend (d := jasminTileDialect) W x)) :
    SRel j B O O' (σ.bind u f) (V.extend y)
      (Valuation.extend (d := jasminTileDialect) W x) := by
  intro t' v
  cases v with
  | here => exact hf
  | there v => exact (h _ v).wk u x

theorem SRel.lane {σ : SEnv n w Γ₀ Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (h : SRel j B O O' σ V W) : EnvRel j σ.lane V W :=
  fun t v => ⟨(h t v).1, (h t v).2.1⟩

/-- The tile form alone holds of a value that is lane `j` of the tile. -/
theorem FormOk.tile {t : JasminTy} (x : Var Δ (Sum.inr (TileTy.tile n w))) (y : ⟦t⟧)
    (W : Valuation Δ) (h : laneRd j t (x.lookup W) = y) :
    FormOk j B O O' (SForm.tile (Γ₀ := Γ₀) (t := t) x) y W := by
  unfold FormOk
  refine ⟨fun _ hv => ?_, fun _ hv => ?_, fun _ ha => ?_, fun hi => ?_⟩
  · cases hv
  · cases hv
    exact h
  · cases ha
  · cases hi

/-- The scalar form alone holds of the value it reads. -/
theorem FormOk.scalar {t : JasminTy} (x : Var Δ (Sum.inl t)) (y : ⟦t⟧) (W : Valuation Δ)
    (h : x.lookup W = y) : FormOk (w := w) j B O O' (SForm.scalar (Γ₀ := Γ₀) x) y W := by
  unfold FormOk
  refine ⟨fun _ hv => ?_, fun _ hv => ?_, fun _ ha => ?_, fun hi => ?_⟩
  · cases hv
    exact h
  · cases hv
  · cases ha
  · cases hi

/-- The array form alone holds of values that satisfy `arrOk`. -/
theorem FormOk.array {t : JasminTy} (a : ArrForm Γ₀ Δ t) (y : ⟦t⟧) (W : Valuation Δ)
    (h : arrOk j B t a.stored y (a.tv.lookup W) (O t a.org) (O' t a.org)) :
    FormOk (w := w) j B O O' (SForm.array a) y W := by
  unfold FormOk
  refine ⟨fun _ hv => ?_, fun _ hv => ?_, fun _ ha => ?_, fun hi => ?_⟩
  · cases hv
  · cases hv
  · cases ha
    exact h
  · cases hi

/-- No form holds of every value. -/
theorem FormOk.absent {t : JasminTy} (y : ⟦t⟧) (W : Valuation Δ) :
    FormOk (w := w) j B O O' (SForm.absent (Γ₀ := Γ₀) (t := t)) y W := by
  unfold FormOk
  refine ⟨fun _ hv => ?_, fun _ hv => ?_, fun _ ha => ?_, fun hi => ?_⟩
  · cases hv
  · cases hv
  · cases ha
  · cases hi

/-- The mark of the trip index holds of the value `B + j`. -/
theorem FormOk.index (W : Valuation Δ) :
    FormOk (w := w) j B O O' (SForm.index (Γ₀ := Γ₀) (t := JasminTy.reg 64))
      (BitVec.ofNat 64 (B + j.val)) W := by
  unfold FormOk
  refine ⟨fun _ hv => ?_, fun _ hv => ?_, fun _ ha => ?_, fun _ => HEq.rfl⟩
  · cases hv
  · cases hv
  · cases ha

end Rel

/-! ## 4. The translation -/

section Translate

variable (n w : Nat)
variable {Γ₀ Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}

/-- The `tileLoad` of a `stackLoad` at the trip index from an array that was not stored, at
    the index variable `bv` of the first lane. -/
def loadOf? (σ : SEnv n w Γ₀ Γ Δ) (bv : Var Δ (Sum.inl (JasminTy.reg 64))) :
    (op : JasminOp) → HVector (fun t => Var Γ t) (DialectSignature.sig op) →
    Option (Expr jasminTileMem Δ (Sum.inr (TileTy.tile n w)))
  | .stackLoad w' N, args =>
      if h : w' = w then
        if (σ _ args.tail.head).isIdx then
          match (σ _ args.head).arr with
          | some a =>
              if a.stored then none
              else
                some (h ▸ (⟨.inr (.tileLoad n w' N), rfl,
                  .cons (castVar a.tv) (.cons (castVar bv) .nil)⟩ :
                    Expr jasminTileMem Δ (Sum.inr (TileTy.tile n w'))))
          | none => none
        else none
      else none
  | _, _ => none

/-- The `tileStore` of a `stackStore` at the trip index of a value with a tile form into an
    array that was not stored, with the entry array the written array descends from. -/
def storeOf? (σ : SEnv n w Γ₀ Γ Δ) (bv : Var Δ (Sum.inl (JasminTy.reg 64))) :
    (op : JasminOp) → HVector (fun t => Var Γ t) (DialectSignature.sig op) →
    Option (Expr jasminTileMem Δ (Sum.inl (DialectSignature.ret (d := jasminDialect) op)) ×
      Var Γ₀ (DialectSignature.ret (d := jasminDialect) op))
  | .stackStore w' N, args =>
      if h : w' = w then
        if (σ _ args.tail.head).isIdx then
          match (σ _ args.head).arr, (σ _ args.tail.tail.head).lv.ln with
          | some a, some x =>
              if a.stored then none
              else
                some (⟨.inr (.tileStore n w' N), rfl,
                  .cons (castVar a.tv) (.cons (castVar bv)
                    (.cons (castVar (h ▸ x : Var Δ (Sum.inr (TileTy.tile n w')))) .nil))⟩,
                  a.org)
          | _, _ => none
        else none
      else none
  | _, _ => none

/-- The tile variables of two operands of which one has a tile form and the other a scalar
    form only, under the binding of the `tileSplat` of the scalar, with that `tileSplat`. -/
def lanePair? (σ : SEnv n w Γ₀ Γ Δ) (x y : Var Γ (JasminTy.reg w)) :
    Option (Expr jasminTileMem Δ (Sum.inr (TileTy.tile n w)) ×
      Var (d := jasminTileDialect) (Sum.inr (TileTy.tile n w) :: Δ)
        (Sum.inr (TileTy.tile n w)) ×
      Var (d := jasminTileDialect) (Sum.inr (TileTy.tile n w) :: Δ)
        (Sum.inr (TileTy.tile n w))) :=
  match (σ _ x).lv.ln, (σ _ y).lv.ln, (σ _ x).lv.sc, (σ _ y).lv.sc with
  | some a, none, _, some s =>
      some (⟨.inr (.tileSplat n w), rfl, .cons (castVar s) .nil⟩, .there a, .here)
  | none, some b, some s, _ =>
      some (⟨.inr (.tileSplat n w), rfl, .cons (castVar s) .nil⟩, .here, .there b)
  | _, _, _, _ => none

/-- The `tileSplat` of the scalar operand and the tile expression of a binary lane operation
    of which one operand has a tile form and the other a scalar form only. -/
def splatOf? (σ : SEnv n w Γ₀ Γ Δ) :
    (op : JasminOp) → HVector (fun t => Var Γ t) (DialectSignature.sig op) →
    Option (Expr jasminTileMem Δ (Sum.inr (TileTy.tile n w)) ×
      Expr jasminTileMem (Sum.inr (TileTy.tile n w) :: Δ) (Sum.inr (TileTy.tile n w)))
  | .regArith bop w', args =>
      if h : w' = w then
        (lanePair? n w σ (h ▸ args.head : Var Γ (JasminTy.reg w))
          (h ▸ args.tail.head : Var Γ (JasminTy.reg w))).map fun r =>
          (r.1, ⟨.inl (.inr (.tileBin bop n w)), rfl,
            .cons (castVar r.2.1) (.cons (castVar r.2.2) .nil)⟩)
      else none
  | .mulhi w', args =>
      if h : w' = w then
        (lanePair? n w σ (h ▸ args.head : Var Γ (JasminTy.reg w))
          (h ▸ args.tail.head : Var Γ (JasminTy.reg w))).map fun r =>
          (r.1, ⟨.inl (.inr (.tileMulhu n w)), rfl,
            .cons (castVar r.2.1) (.cons (castVar r.2.2) .nil)⟩)
      else none
  | _, _ => none

/-- The position of a variable in its context. -/
def vidx {d : Dialect} {Γ : Ctxt d} {t : d.Ty} : Var Γ t → Nat
  | .here => 0
  | .there v => vidx v + 1

/-- Two variables of the same type at the same position are equal. -/
theorem vidx_inj {d : Dialect} : ∀ {Γ : Ctxt d} {t : d.Ty} (a b : Var Γ t),
    vidx a = vidx b → a = b
  | _, _, .here, .here, _ => rfl
  | _, _, .here, .there _, h => nomatch h
  | _, _, .there _, .here, h => nomatch h
  | _, _, .there a, .there b, h => congrArg Var.there (vidx_inj a b (Nat.succ.inj h))

/-- The target variables of a returned tuple whose variable at each position has an array
    form that descends from the entry array `org` gives for that position. -/
def retArrs (σ : SEnv n w Γ₀ Γ Δ) : {ts : List JasminTy} →
    (∀ t, Var (d := jasminDialect) ts t → Var Γ₀ t) → HVector (fun t => Var Γ t) ts →
    Option (HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy))))
  | [], _, .nil => some .nil
  | _ :: _, org, .cons v vs =>
      (σ _ v).arr.bind fun a =>
        if vidx a.org = vidx (org _ .here) then
          (retArrs σ (fun t x => org t (.there x)) vs).map (.cons a.tv)
        else none

/-- **The lane form of a straight-line body** along an environment, at the index variable
    `bv` of the first lane and the entry arrays `org` of the returned positions; `none` where
    the body is refused. -/
def stripBody : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
    {Δ : Ctxt jasminTileDialect} → SEnv n w Γ₀ Γ Δ → Var Δ (Sum.inl (JasminTy.reg 64)) →
    (∀ t, Var (d := jasminDialect) ts t → Var Γ₀ t) →
    Option (NFProg jasminTileMem Δ (ts.map (Sum.inl (β := TileTy))))
  | _, _, .ret vs, _, σ, _, org => (retArrs n w σ org vs).map fun r => .ret (castArgs r)
  | _, _, .var e k, _, σ, bv, org =>
      match loadOf? n w σ bv e.op e.args with
      | some e' => (stripBody k (σ.bind _ (.tile .here)) (.there bv) org).map (.var e')
      | none =>
        match storeOf? n w σ bv e.op e.args with
        | some r =>
            (stripBody k (σ.bind _ (.array ⟨.here, e.retTy_eq ▸ r.2, true⟩)) (.there bv)
              org).map
              (.var ⟨r.1.op, r.1.retTy_eq.trans (congrArg Sum.inl e.retTy_eq), r.1.args⟩)
        | none =>
          match tileOp? n w σ.lane e.op e.args with
          | some e' =>
              (stripBody k (σ.bind _ (.tile .here)) (.there bv) org).map
                (.var (embedExpr jasminDialect e'))
          | none =>
            match splatOf? n w σ e.op e.args with
            | some r =>
                (stripBody k ((σ.wk _).bind _ (.tile .here)) (.there (.there bv)) org).map
                  fun q => .var r.1 (.var r.2 q)
            | none =>
                (scArgs n w σ.lane e.args).bind fun as =>
                  (stripBody k (σ.bind _ (.scalar .here)) (.there bv) org).map
                    (.var ⟨.inl (.inl e.op), congrArg Sum.inl e.retTy_eq, castArgs as⟩)
  | _, _, _, _, _, _, _ => none

end Translate

/-! ## 5. Events of straight-line programs -/

/-- The number of events of an operation of the class `k`. -/
def kindLen : LeakKind → Nat
  | .quiet => 0
  | _ => 1

/-- An operation emits `kindLen` events of its class. -/
theorem length_opLeak (M : LeakModel jasminDialect) (op : JasminOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op)) :
    (opLeak M op vals).length = kindLen (M.kind op) := by
  unfold opLeak
  cases M.kind op <;> rfl

/-- The number of events of the let-bindings of a program up to its first region. -/
def evCount (M : LeakModel jasminDialect) : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Nat
  | _, _, .var e k => kindLen (M.kind e.op) + evCount M k
  | _, _, _ => 0

/-- The leakage models in which a load and a store emit one address event, the reading of
    their index. -/
def ArrAddr (M : LeakModel jasminDialect) : Prop :=
  ∀ w N, M.kind (.stackLoad w N) = .addrAt 1 ∧ M.kind (.stackStore w N) = .addrAt 1

/-- The leakage run of a let-binding whose expression denotes `x` and whose continuation
    runs to `r`. -/
theorem leakRunM_var_some {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] (M : LeakModel d) (fuel : Nat)
    {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty} (e : Expr d Γ t) (k : NFProg d (t :: Γ) ts)
    (V : Valuation Γ) (x : ⟦t⟧) (r : Valuation ts × List CTLeak)
    (he : e.denoteM (M := Option) V = some x)
    (hk : NFProg.leakRunM M fuel k (V.extend x) = some r) :
    NFProg.leakRunM M fuel (.var e k) V = some (r.1, Expr.ctLeak M e V ++ r.2) := by
  show (e.denoteM (M := Option) V).bind _ = _
  rw [he]
  show Option.map _ (NFProg.leakRunM M fuel k (V.extend x)) = _
  rw [hk]
  rfl

/-! ## 6. Preservation at a lane -/

section Sound

variable {n w : Nat} {Γ₀ Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
  {j : Fin n} {B : Nat} {O O' : ∀ t, Var Γ₀ t → ⟦t⟧} {σ : SEnv n w Γ₀ Γ Δ}
  {V : Valuation Γ} {W : Valuation Δ}

theorem loadOf?_sound (M : LeakModel jasminDialect) (hA : ArrAddr M)
    (hσ : SRel j B O O' σ V W) (hO : ∀ t v, arrAt j B t (O t v) (O' t v))
    (hB : B + j.val < 2 ^ 64) {bv : Var Δ (Sum.inl (JasminTy.reg 64))}
    (hb : bv.lookup W = BitVec.ofNat 64 B) (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig op))
    (e' : Expr jasminTileMem Δ (Sum.inr (TileTy.tile n w)))
    (h : loadOf? n w σ bv op args = some e') :
    ∃ x' : Fin n → BitVec w, e'.denoteM (M := Option) W = some x' ∧
      laneRd j (DialectSignature.ret (d := jasminDialect) op) x' =
        DialectDenote.denote op (Expr.lookupArgs args V) ∧
      (j.val = 0 → Expr.ctLeak (tileMemLeak jasminDialect M) e' W =
        opLeak M op (Expr.lookupArgs args V)) := by
  cases op <;> simp only [loadOf?] at h <;> try cases h
  case stackLoad w' N =>
    split at h
    · rename_i hw
      subst hw
      split at h
      · rename_i hidx
        split at h
        · rename_i a ha
          split at h
          · cases h
          · rename_i hst
            cases h
            cases args with
            | cons x rest =>
              cases rest with
              | cons y rest2 =>
                cases rest2
                have h3 := (hσ _ x).2.2.1 a ha
                have h4 : y.lookup V = BitVec.ofNat 64 (B + j.val) :=
                  eq_of_heq ((hσ _ y).2.2.2 hidx)
                rw [(Bool.not_eq_true _).mp hst] at h3
                obtain ⟨-, hS, hS'⟩ : laneFits n (JasminTy.stackArr w' N) ∧
                    x.lookup V = O _ a.org ∧ a.tv.lookup W = O' _ a.org := h3
                have hbt : (BitVec.ofNat 64 B).toNat = B := by
                  rw [BitVec.toNat_ofNat]
                  exact Nat.mod_eq_of_lt (by omega)
                have hjt : (BitVec.ofNat 64 (B + j.val)).toNat = B + j.val := by
                  rw [BitVec.toNat_ofNat]
                  exact Nat.mod_eq_of_lt hB
                have hO1 : stackGet (O _ a.org) (B + j.val) = stackGet (O' _ a.org) (B + j.val) :=
                  hO _ a.org
                dsimp only
                refine ⟨fun i => stackGet (a.tv.lookup W) (B + i.val), ?_, ?_, ?_⟩
                · show some (laneLoad jasminDialect n (w := w') (N := N)
                    ((memVar a.tv).lookup (d := jasminTileMem) W)
                    (BitVec.toNat ((memVar bv).lookup (d := jasminTileMem) W))) = _
                  rw [lookup_memVar, lookup_memVar, hb, hbt]
                  rfl
                · show laneRd j (JasminTy.reg w') _ = _
                  rw [laneRd_reg]
                  show _ = stackGet (x.lookup V) (y.lookup V).toNat
                  rw [h4, hjt, hS, hS', hO1]
                · intro hj
                  show opLeak (tileMemLeak jasminDialect M) (.inr (.tileLoad n w' N))
                    (.cons _ (.cons _ .nil)) = _
                  rw [tileMem_opLeak_tileLoad, lookup_castVar]
                  unfold opLeak
                  rw [(hA w' N).1]
                  show [CTLeak.addr "" ((M.valNat (JasminTy.reg 64) (bv.lookup W) : Nat) : Int)] =
                    [CTLeak.addr "" ((M.valNat (JasminTy.reg 64) (y.lookup V) : Nat) : Int)]
                  rw [hb, h4, hj, Nat.add_zero]
        · cases h
      · cases h
    · cases h

theorem storeOf?_sound (M : LeakModel jasminDialect) (hA : ArrAddr M)
    (hσ : SRel j B O O' σ V W) (hB : B + j.val < 2 ^ 64)
    {bv : Var Δ (Sum.inl (JasminTy.reg 64))} (hb : bv.lookup W = BitVec.ofNat 64 B)
    (op : JasminOp) (args : HVector (fun t => Var Γ t) (DialectSignature.sig op))
    (r : Expr jasminTileMem Δ (Sum.inl (DialectSignature.ret (d := jasminDialect) op)) ×
      Var Γ₀ (DialectSignature.ret (d := jasminDialect) op))
    (h : storeOf? n w σ bv op args = some r) :
    ∃ S' : ⟦DialectSignature.ret (d := jasminDialect) op⟧,
      r.1.denoteM (M := Option) W = some S' ∧
      arrOk j B _ true (DialectDenote.denote op (Expr.lookupArgs args V)) S' (O _ r.2)
        (O' _ r.2) ∧
      (j.val = 0 → Expr.ctLeak (tileMemLeak jasminDialect M) r.1 W =
        opLeak M op (Expr.lookupArgs args V)) := by
  cases op <;> simp only [storeOf?] at h <;> try cases h
  case stackStore w' N =>
    split at h
    · rename_i hw
      subst hw
      split at h
      · rename_i hidx
        split at h
        · rename_i a x ha hx
          split at h
          · cases h
          · rename_i hst
            cases h
            cases args with
            | cons xa rest =>
              cases rest with
              | cons y rest2 =>
                cases rest2 with
                | cons z rest3 =>
                  cases rest3
                  have h3 := (hσ _ xa).2.2.1 a ha
                  have h4 : y.lookup V = BitVec.ofNat 64 (B + j.val) :=
                    eq_of_heq ((hσ _ y).2.2.2 hidx)
                  have h5 := (hσ _ z).2.1 x hx
                  rw [laneRd_reg] at h5
                  rw [(Bool.not_eq_true _).mp hst] at h3
                  obtain ⟨hf, hS, hS'⟩ : laneFits n (JasminTy.stackArr w' N) ∧
                      xa.lookup V = O _ a.org ∧ a.tv.lookup W = O' _ a.org := h3
                  have hbt : (BitVec.ofNat 64 B).toNat = B := by
                    rw [BitVec.toNat_ofNat]
                    exact Nat.mod_eq_of_lt (by omega)
                  have hjt : (BitVec.ofNat 64 (B + j.val)).toNat = B + j.val := by
                    rw [BitVec.toNat_ofNat]
                    exact Nat.mod_eq_of_lt hB
                  dsimp only
                  refine ⟨jasminLaneStore (a.tv.lookup W) B (x.lookup W), ?_, ?_, ?_⟩
                  · show some (laneStore jasminDialect (L := n) (w := w') (N := N)
                      ((memVar a.tv).lookup (d := jasminTileMem) W)
                      (BitVec.toNat ((memVar bv).lookup (d := jasminTileMem) W))
                      ((memVar x).lookup (d := jasminTileMem) W)) = _
                    rw [lookup_memVar, lookup_memVar, lookup_memVar, hb, hbt]
                  · show outOk j B (JasminTy.stackArr w' N) _ _
                      (stackSet (xa.lookup V) (y.lookup V).toNat (z.lookup V)) _
                    refine ⟨hf, ?_, fun k hk => ?_⟩
                    · rw [h4, hjt, hS, jasmin_laneStore_inside hf _ B _ j, h5]
                      rfl
                    · rw [jasmin_laneStore_outside _ B _ k hk, hS']
                      rfl
                  · intro hj
                    show opLeak (tileMemLeak jasminDialect M) (.inr (.tileStore n w' N))
                      (.cons _ (.cons _ (.cons _ .nil))) = _
                    rw [tileMem_opLeak_tileStore, lookup_castVar]
                    unfold opLeak
                    rw [(hA w' N).2]
                    show [CTLeak.addr "" ((M.valNat (JasminTy.reg 64) (bv.lookup W) : Nat) : Int)]
                      = [CTLeak.addr "" ((M.valNat (JasminTy.reg 64) (y.lookup V) : Nat) : Int)]
                    rw [hb, h4, hj, Nat.add_zero]
        · cases h
      · cases h
    · cases h

theorem lanePair?_sound (M : LeakModel jasminDialect) (hσ : SRel j B O O' σ V W)
    (x y : Var Γ (JasminTy.reg w))
    (r : Expr jasminTileMem Δ (Sum.inr (TileTy.tile n w)) ×
      Var (d := jasminTileDialect) (Sum.inr (TileTy.tile n w) :: Δ)
        (Sum.inr (TileTy.tile n w)) ×
      Var (d := jasminTileDialect) (Sum.inr (TileTy.tile n w) :: Δ)
        (Sum.inr (TileTy.tile n w)))
    (h : lanePair? n w σ x y = some r) :
    ∃ xs : Fin n → BitVec w, r.1.denoteM (M := Option) W = some xs ∧
      (r.2.1.lookup (Valuation.extend (d := jasminTileDialect) W xs) : Fin n → BitVec w) j =
        x.lookup V ∧
      (r.2.2.lookup (Valuation.extend (d := jasminTileDialect) W xs) : Fin n → BitVec w) j =
        y.lookup V ∧
      Expr.ctLeak (tileMemLeak jasminDialect M) r.1 W = [] := by
  unfold lanePair? at h
  split at h
  · rename_i a s ha _ hs
    cases h
    have h1 := (hσ _ x).2.1 a ha
    have h2 := (hσ _ y).1 s hs
    rw [laneRd_reg] at h1
    refine ⟨fun _ => s.lookup W, ?_, h1, h2, rfl⟩
    show some (laneSplat jasminDialect n (w := w) ((memVar s).lookup (d := jasminTileMem) W))
      = _
    rw [lookup_memVar]
    rfl
  · rename_i b s _ hb' hs
    cases h
    have h1 := (hσ _ y).2.1 b hb'
    have h2 := (hσ _ x).1 s hs
    rw [laneRd_reg] at h1
    refine ⟨fun _ => s.lookup W, ?_, h2, h1, rfl⟩
    show some (laneSplat jasminDialect n (w := w) ((memVar s).lookup (d := jasminTileMem) W))
      = _
    rw [lookup_memVar]
    rfl
  · cases h

theorem splatOf?_sound (M : LeakModel jasminDialect) (hσ : SRel j B O O' σ V W)
    (op : JasminOp) (args : HVector (fun t => Var Γ t) (DialectSignature.sig op))
    (r : Expr jasminTileMem Δ (Sum.inr (TileTy.tile n w)) ×
      Expr jasminTileMem (Sum.inr (TileTy.tile n w) :: Δ) (Sum.inr (TileTy.tile n w)))
    (h : splatOf? n w σ op args = some r) :
    isLaneOp w op = true ∧ ∃ xs x' : Fin n → BitVec w,
      r.1.denoteM (M := Option) W = some xs ∧
      r.2.denoteM (M := Option) (Valuation.extend (d := jasminTileDialect) W xs) = some x' ∧
      laneRd j (DialectSignature.ret (d := jasminDialect) op) x' =
        DialectDenote.denote op (Expr.lookupArgs args V) ∧
      Expr.ctLeak (tileMemLeak jasminDialect M) r.1 W = [] ∧
      Expr.ctLeak (tileMemLeak jasminDialect M) r.2
        (Valuation.extend (d := jasminTileDialect) W xs) = [] := by
  cases op <;> simp only [splatOf?] at h <;> try cases h
  case regArith bop w' =>
    split at h
    · rename_i hw
      subst hw
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest2 =>
          cases rest2
          obtain ⟨xs, h1, h2, h3, h4⟩ := lanePair?_sound M hσ x y p hp
          refine ⟨by simp [isLaneOp], xs, _, h1, rfl, ?_, h4, rfl⟩
          show laneRd j (JasminTy.reg w') (tileBinApply bop
            ((memVar p.2.1).lookup (d := jasminTileMem) _)
            ((memVar p.2.2).lookup (d := jasminTileMem) _)) = bop.apply (x.lookup V) (y.lookup V)
          rw [laneRd_reg, lookup_memVar, lookup_memVar]
          show bop.apply _ _ = _
          rw [h2, h3]
    · cases h
  case mulhi w' =>
    split at h
    · rename_i hw
      subst hw
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest2 =>
          cases rest2
          obtain ⟨xs, h1, h2, h3, h4⟩ := lanePair?_sound M hσ x y p hp
          refine ⟨by simp [isLaneOp], xs, _, h1, rfl, ?_, h4, rfl⟩
          show laneRd j (JasminTy.reg w') (tileMulhuApply
            ((memVar p.2.1).lookup (d := jasminTileMem) _)
            ((memVar p.2.2).lookup (d := jasminTileMem) _)) = mulHiW (x.lookup V) (y.lookup V)
          rw [laneRd_reg, lookup_memVar, lookup_memVar]
          show laneMulhu _ _ = _
          rw [h2, h3]
          rfl
    · cases h

theorem retArrs_sound (hσ : SRel j B O O' σ V W) (hO : ∀ t v, arrAt j B t (O t v) (O' t v)) :
    {ts : List JasminTy} → (org : ∀ t, Var (d := jasminDialect) ts t → Var Γ₀ t) →
    (vs : HVector (fun t => Var Γ t) ts) →
    (r : HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy)))) →
    retArrs n w σ org vs = some r →
    TupRel j B ts (fun t x => O t (org t x)) (fun t x => O' t (org t x))
      (Expr.lookupArgs vs V) (Expr.lookupArgs r W)
  | [], _, .nil, _, _ => trivial
  | t :: ts, org, .cons v vs, r, h => by
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      by_cases hix : vidx a.org = vidx (org _ .here)
      · rw [ite_eq_left hix] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
        have horg : a.org = org _ .here := vidx_inj _ _ hix
        refine ⟨?_, retArrs_sound hσ hO (fun t x => org t (.there x)) vs r' hr'⟩
        show outOk j B t (O t (org t .here)) (O' t (org t .here)) (v.lookup V) (a.tv.lookup W)
        rw [← horg]
        exact outOk_of_arrOk (hO _ _) ((hσ _ v).2.2.1 a ha)
      · rw [ite_eq_right hix] at h
        cases h

/-- **The lane form at a lane.** For a body `stripBody` accepts along `σ`, a leakage model in
    which the lifted operations are quiet and a load and a store emit their index, a lane `j`
    with `B + j < 2 ^ 64`, valuations related at lane `j`, and entry arrays that agree at
    `B + j`: the scalar body and the lane form both run; the returned tuples satisfy `TupRel`;
    at lane `0` the events are equal; and the scalar events number `evCount`. -/
theorem stripBody_lane (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (hA : ArrAddr M)
    (fuel : Nat) (j : Fin n) (B : Nat) (hB : B + j.val < 2 ^ 64)
    (O O' : ∀ t, Var Γ₀ t → ⟦t⟧) (hO : ∀ t v, arrAt j B t (O t v) (O' t v))
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminTileDialect} (σ : SEnv n w Γ₀ Γ Δ)
      (bv : Var Δ (Sum.inl (JasminTy.reg 64)))
      (org : ∀ t, Var (d := jasminDialect) ts t → Var Γ₀ t)
      (q : NFProg jasminTileMem Δ (ts.map (Sum.inl (β := TileTy)))),
      stripBody n w p σ bv org = some q → ∀ (V : Valuation Γ) (W : Valuation Δ),
      SRel j B O O' σ V W → bv.lookup W = BitVec.ofNat 64 B →
      ∃ (o : Valuation (d := jasminDialect) ts) (ev : List CTLeak)
        (o' : Valuation (d := jasminTileDialect) (ts.map (Sum.inl (β := TileTy))))
        (ev' : List CTLeak),
        NFProg.leakRunM M fuel p V = some (o, ev) ∧
        tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel q W
          = some (o', ev') ∧
        TupRel j B ts (fun t x => O t (org t x)) (fun t x => O' t (org t x)) o o' ∧
        (j.val = 0 → ev = ev') ∧ ev.length = evCount M p := by
  induction p with
  | ret vs =>
      intro Δ σ bv org q hq V W hσ hb
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hq
      refine ⟨_, _, _, _, rfl, rfl, ?_, fun _ => rfl, rfl⟩
      rw [lookupArgs_memArgs]
      exact retArrs_sound hσ hO org vs r hr
  | var e k ih =>
      intro Δ σ bv org q hq V W hσ hb
      obtain ⟨op, rfl, args⟩ := e
      simp only [stripBody] at hq
      have hlen : ∀ (ev : List CTLeak), ev.length = evCount M k →
          (opLeak M op (Expr.lookupArgs args V) ++ ev).length =
            evCount M (.var ⟨op, rfl, args⟩ k) := by
        intro ev hev
        rw [List.length_append, length_opLeak, hev]
        rfl
      split at hq
      · rename_i e' he
        obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
        obtain ⟨x', hx', hlane, hev⟩ := loadOf?_sound M hA hσ hO hB hb op args e' he
        obtain ⟨o, ev, o', ev', h1, h2, hT, hE, hl⟩ := ih _ _ _ q' hq' _ _
          (hσ.bind (Sum.inr (TileTy.tile n w)) x' _ _ (FormOk.tile .here _ _ hlane)) hb
        refine ⟨o, _, o', _,
          leakRunM_var_some M fuel _ k V _ (o, ev) (Expr.denoteM_option_eq_some _ V) h1,
          leakRunM_var_some (tileMemLeak jasminDialect M) fuel e' q' W x' (o', ev') hx' h2,
          hT, fun hj => ?_, hlen ev hl⟩
        show Expr.ctLeak M _ V ++ ev = Expr.ctLeak (tileMemLeak jasminDialect M) e' W ++ ev'
        rw [hev hj, hE hj]
        rfl
      · split at hq
        · rename_i r hr
          obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
          obtain ⟨S', hS', hok, hev⟩ := storeOf?_sound M hA hσ hB hb op args r hr
          obtain ⟨o, ev, o', ev', h1, h2, hT, hE, hl⟩ := ih _ _ _ q' hq' _ _
            (hσ.bind (Sum.inl (DialectSignature.ret (d := jasminDialect) op)) S' _
              (DialectDenote.denote op (Expr.lookupArgs args V))
              (FormOk.array ⟨.here, r.2, true⟩ _ _ hok)) hb
          refine ⟨o, _, o', _,
            leakRunM_var_some M fuel _ k V _ (o, ev) (Expr.denoteM_option_eq_some _ V) h1,
            leakRunM_var_some (tileMemLeak jasminDialect M) fuel r.1 q' W S' (o', ev') hS' h2,
            hT, fun hj => ?_, hlen ev hl⟩
          show Expr.ctLeak M _ V ++ ev = Expr.ctLeak (tileMemLeak jasminDialect M) r.1 W ++ ev'
          rw [hev hj, hE hj]
          rfl
        · split at hq
          · rename_i e' he
            obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
            obtain ⟨hlo, x', hx', hlane, hleak⟩ := tileOp?_sound M hσ.lane op args e' he
            have hsrc : opLeak M op (Expr.lookupArgs args V) = [] := by
              unfold opLeak
              rw [hM _ hlo]
            obtain ⟨o, ev, o', ev', h1, h2, hT, hE, hl⟩ := ih _ _ _ q' hq' _ _
              (hσ.bind (Sum.inr (TileTy.tile n w)) x' _ _ (FormOk.tile .here _ _ hlane)) hb
            refine ⟨o, _, o', _,
              leakRunM_var_some M fuel _ k V _ (o, ev) (Expr.denoteM_option_eq_some _ V) h1,
              leakRunM_var_some (tileMemLeak jasminDialect M) fuel (embedExpr jasminDialect e')
                q' W x' (o', ev')
                ((embedExpr_denoteM jasminDialect _ e' W).trans hx') h2,
              hT, fun hj => ?_, hlen ev hl⟩
            show opLeak M op _ ++ ev = Expr.ctLeak _ (embedExpr jasminDialect e') W ++ ev'
            rw [hsrc, embedExpr_ctLeak, hleak, hE hj]
          · split at hq
            · rename_i r hr
              obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
              obtain ⟨hlo, xs, x', h1s, h2s, hlane, hl1, hl2⟩ :=
                splatOf?_sound M hσ op args r hr
              have hsrc : opLeak M op (Expr.lookupArgs args V) = [] := by
                unfold opLeak
                rw [hM _ hlo]
              obtain ⟨o, ev, o', ev', h1, h2, hT, hE, hl⟩ := ih _ _ _ q' hq' _ _
                ((hσ.wk (Sum.inr (TileTy.tile n w)) xs).bind (Sum.inr (TileTy.tile n w)) x'
                  _ _ (FormOk.tile .here _ _ hlane)) hb
              refine ⟨o, _, o', _,
                leakRunM_var_some M fuel _ k V _ (o, ev) (Expr.denoteM_option_eq_some _ V) h1,
                leakRunM_var_some (tileMemLeak jasminDialect M) fuel r.1 (.var r.2 q') W xs _
                  h1s (leakRunM_var_some (tileMemLeak jasminDialect M) fuel r.2 q' _ x'
                    (o', ev') h2s h2),
                hT, fun hj => ?_, hlen ev hl⟩
              show opLeak M op _ ++ ev = Expr.ctLeak _ r.1 W ++ (Expr.ctLeak _ r.2 _ ++ ev')
              rw [hsrc, hl1, hE hj]
              exact (congrArg (· ++ ev') hl2).symm
            · obtain ⟨as, has, hq⟩ := Option.bind_eq_some_iff.mp hq
              obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
              have hargs := scArgs_sound hσ.lane args as has
              have hden : Expr.denoteM (M := Option)
                  (⟨.inl (.inl op), rfl, memArgs as⟩ : Expr jasminTileMem Δ
                    (Sum.inl (DialectSignature.ret (d := jasminDialect) op))) W =
                  some (DialectDenote.denote op (Expr.lookupArgs args V)) := by
                rw [← hargs, ← lookupArgs_memArgs as W]
                rfl
              have hlk : Expr.ctLeak (tileMemLeak jasminDialect M)
                  (⟨.inl (.inl op), rfl, memArgs as⟩ : Expr jasminTileMem Δ
                    (Sum.inl (DialectSignature.ret (d := jasminDialect) op))) W =
                  opLeak M op (Expr.lookupArgs args V) := by
                show opLeak (tileMemLeak jasminDialect M) (.inl (.inl op))
                  (Expr.lookupArgs (d := jasminTileMem) (memArgs as) W) = _
                rw [tileMem_opLeak_scalar, lookupArgs_memArgs, hargs]
              obtain ⟨o, ev, o', ev', h1, h2, hT, hE, hl⟩ := ih _ _ _ q' hq' _ _
                (hσ.bind (Sum.inl (DialectSignature.ret (d := jasminDialect) op))
                  (DialectDenote.denote op (Expr.lookupArgs args V)) _
                  (DialectDenote.denote op (Expr.lookupArgs args V))
                  (FormOk.scalar .here _ _ rfl)) hb
              refine ⟨o, _, o', _,
                leakRunM_var_some M fuel _ k V _ (o, ev) (Expr.denoteM_option_eq_some _ V) h1,
                leakRunM_var_some (tileMemLeak jasminDialect M) fuel _ q' W _ (o', ev') hden h2,
                hT, fun hj => ?_, hlen ev hl⟩
              show Expr.ctLeak M _ V ++ ev = Expr.ctLeak (tileMemLeak jasminDialect M) _ W ++ ev'
              rw [hlk, hE hj]
              rfl
  | forLoop count inits body k _ _ =>
      intro Δ σ bv org q hq
      cases hq
  | ifThenElse cond thn els k _ _ _ =>
      intro Δ σ bv org q hq
      cases hq
  | whileLoop inits body k _ _ =>
      intro Δ σ bv org q hq
      cases hq
  | call f args k _ =>
      intro Δ σ bv org q hq
      cases hq

end Sound

/-! ## 7. The entry of a loop body -/

section Entry

variable (n w : Nat)
variable {Γ₀ Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}

/-- The forms of a variable of the entry context with the target variable `tv`: an array of
    at least `n` elements has the array form of an array that was not stored, a smaller array
    no form, and a variable of another type the scalar form unless it is carried. -/
def SForm.entry (t : JasminTy) (tv : Var Δ (Sum.inl t)) (org : Var Γ₀ t) (carried : Bool) :
    SForm n w Γ₀ Δ t :=
  match t, tv, org with
  | .stackArr _ N, tv, org => if n ≤ N then .array ⟨tv, org, false⟩ else .absent
  | _, tv, _ => if carried then .absent else .scalar tv

/-- The environment of loop-invariant variables along a renaming `ren` into the target
    context, with their variables `org` in the entry context. -/
def envInv (ren : ∀ t, Var Γ t → Var Δ (Sum.inl t)) (org : ∀ t, Var Γ t → Var Γ₀ t) :
    SEnv n w Γ₀ Γ Δ :=
  fun t v => SForm.entry n w t (ren t v) (org t v) false

/-- The environment under the carried tuple `cs`, bound at the same types in the target. -/
def SEnv.carry (σ : SEnv n w Γ₀ Γ Δ) : (cs : List JasminTy) →
    (∀ t, Var (d := jasminDialect) cs t → Var Γ₀ t) →
    SEnv n w Γ₀ (cs ++ Γ) (cs.map (Sum.inl (β := TileTy)) ++ Δ)
  | [], _ => σ
  | t :: cs, org =>
      (SEnv.carry σ cs (fun t x => org t (.there x))).bind (Sum.inl t)
        (SForm.entry n w t .here (org t .here) true)

/-- The environment at the entry of the lane form of a loop body. The source context is the
    carried tuple, the trip index and the loop-invariant variables; the target context is the
    index of the first lane, the carried tuple, the block counter and the context `Δ` the
    loop-invariant variables are renamed into. -/
def bodyEnv (cs : List JasminTy) (ren : ∀ t, Var Γ t → Var Δ (Sum.inl t)) :
    SEnv n w (cs ++ JasminTy.reg 64 :: Γ) (cs ++ JasminTy.reg 64 :: Γ)
      (Sum.inl (JasminTy.reg 64) ::
        (cs.map (Sum.inl (β := TileTy)) ++ Sum.inl (JasminTy.reg 64) :: Δ)) :=
  (SEnv.carry n w
    ((envInv n w ren (fun _ v => inrHom cs (.there v))).bind (Sum.inl (JasminTy.reg 64))
      SForm.index)
    cs (fun _ x => inlHom _ x)).wk _

/-- **The lane form of a loop body**: `stripBody` at the entry environment. -/
def laneBody {cs : List JasminTy}
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    (ren : ∀ t, Var Γ t → Var Δ (Sum.inl t)) :
    Option (NFProg jasminTileMem
      (Sum.inl (JasminTy.reg 64) ::
        (cs.map (Sum.inl (β := TileTy)) ++ Sum.inl (JasminTy.reg 64) :: Δ))
      (cs.map (Sum.inl (β := TileTy)))) :=
  stripBody n w body (bodyEnv n w cs ren) .here (fun _ x => inlHom _ x)

/-- The parts of a counted loop with an elementwise body: the loop `p` is
    `forLoop count inits body k`, and `vbody` is the lane form of `body`. -/
structure Elemwise {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (ren : ∀ t, Var Γ t → Var Δ (Sum.inl t)) where
  /-- The carried tuple. -/
  cs : List JasminTy
  /-- The trip count. -/
  count : Var Γ (JasminTy.reg 64)
  /-- The initial values of the carried tuple. -/
  inits : HVector (fun t => Var Γ t) cs
  /-- The loop body. -/
  body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs
  /-- The continuation. -/
  k : NFProg jasminDialect (cs ++ Γ) ts
  /-- The lane form of the body. -/
  vbody : NFProg jasminTileMem
    (Sum.inl (JasminTy.reg 64) ::
      (cs.map (Sum.inl (β := TileTy)) ++ Sum.inl (JasminTy.reg 64) :: Δ))
    (cs.map (Sum.inl (β := TileTy)))
  /-- The program is the counted loop of the parts. -/
  prog_eq : p = NFProg.forLoop count inits body k
  /-- `vbody` is the lane form of `body`. -/
  lifted : laneBody n w body ren = some vbody

/-- **Recognition of a counted loop with an elementwise body**: the parts of `p` when it is a
    counted loop whose body `laneBody` accepts, `none` otherwise. -/
def elemwise? {ts : List JasminTy} (ren : ∀ t, Var Γ t → Var Δ (Sum.inl t)) :
    (p : NFProg jasminDialect Γ ts) → Option (Elemwise n w p ren)
  | .forLoop count inits body k =>
      match h : laneBody n w body ren with
      | some vb => some ⟨_, count, inits, body, k, vb, rfl, h⟩
      | none => none
  | _ => none

variable {n w}
variable {j : Fin n} {B : Nat} {O O' : ∀ t, Var Γ₀ t → ⟦t⟧}

/-- The entry forms hold of a value that is its entry array on both sides, or that the scalar
    form reads. -/
theorem FormOk.entry (t : JasminTy) (tv : Var Δ (Sum.inl t)) (org : Var Γ₀ t) (c : Bool)
    (y : ⟦t⟧) (W : Valuation Δ) (hsc : c = false → tv.lookup W = y) (hO : y = O t org)
    (hO' : tv.lookup W = O' t org) :
    FormOk j B O O' (SForm.entry n w t tv org c) y W := by
  cases t with
  | stackArr w' N =>
      by_cases hN : n ≤ N
      · have h : SForm.entry n w (JasminTy.stackArr w' N) tv org c =
            SForm.array ⟨tv, org, false⟩ := ite_eq_left hN
        rw [h]
        exact FormOk.array _ _ _
          (show laneFits n (JasminTy.stackArr w' N) ∧ y = O _ org ∧ tv.lookup W = O' _ org from
            ⟨hN, hO, hO'⟩)
      · have h : SForm.entry n w (JasminTy.stackArr w' N) tv org c = SForm.absent :=
          ite_eq_right hN
        rw [h]
        exact FormOk.absent _ _
  | reg w' =>
      cases c with
      | false => exact FormOk.scalar _ _ _ (hsc rfl)
      | true => exact FormOk.absent _ _
  | inlineInt =>
      cases c with
      | false => exact FormOk.scalar _ _ _ (hsc rfl)
      | true => exact FormOk.absent _ _
  | bool =>
      cases c with
      | false => exact FormOk.scalar _ _ _ (hsc rfl)
      | true => exact FormOk.absent _ _

theorem SRel.carry {σ : SEnv n w Γ₀ Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (h : SRel j B O O' σ V W) : (cs : List JasminTy) →
    (org : ∀ t, Var (d := jasminDialect) cs t → Var Γ₀ t) →
    (A : Valuation (d := jasminDialect) cs) →
    (A' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy)))) →
    (∀ t (x : Var (d := jasminDialect) cs t), O t (org t x) = x.lookup A) →
    (∀ t (x : Var (d := jasminDialect) cs t),
      O' t (org t x) = x.lookup (unmapInl (d := jasminDialect) (e := tileDialect) A')) →
    SRel j B O O' (σ.carry n w cs org) (hvAppend A V) (hvAppend (d := jasminTileDialect) A' W)
  | [], _, .nil, .nil, _, _ => h
  | t :: cs, org, .cons a A, .cons a' A', h1, h2 =>
      SRel.bind
        (SRel.carry h cs (fun t x => org t (.there x)) A A' (fun t x => h1 t (.there x))
          (fun t x => h2 t (.there x)))
        (Sum.inl t) a' _ a
        (FormOk.entry t .here (org t .here) true a _ (fun hc => nomatch hc) (h1 t .here).symm
          (h2 t .here).symm)

/-- **The entry environment relates the entry valuations.** At lane `j` of the block at `B`,
    the scalar entry valuation is the carried tuple `A`, the index `B + j` and `V`; the target
    entry valuation is an index `bw`, the carried tuple `A'`, a block counter `blk` and a
    valuation `W` that reads `V` along `ren`. The entry arrays are those of the two
    valuations. -/
theorem bodyEnv_rel (j : Fin n) (B : Nat) (cs : List JasminTy)
    (ren : ∀ t, Var Γ t → Var Δ (Sum.inl t)) (V : Valuation Γ) (W : Valuation Δ)
    (hren : ∀ t v, (ren t v).lookup W = v.lookup V) (A : Valuation (d := jasminDialect) cs)
    (A' : Valuation (d := jasminTileDialect) (cs.map (Sum.inl (β := TileTy))))
    (bw blk : BitVec 64) :
    SRel j B
      (fun _ v => v.lookup (hvAppend A
        (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + j.val)))))
      (fun _ v => v.lookup (hvAppend (unmapInl (d := jasminDialect) (e := tileDialect) A')
        (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + j.val)))))
      (bodyEnv n w cs ren)
      (hvAppend A (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + j.val))))
      (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64))
        (hvAppend (d := jasminTileDialect) A'
          (Valuation.extend (d := jasminTileDialect) (t := Sum.inl (JasminTy.reg 64)) W blk))
        bw) := by
  have h1 : SRel (w := w) j B
      (fun _ v => v.lookup (hvAppend A
        (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + j.val)))))
      (fun _ v => v.lookup (hvAppend (unmapInl (d := jasminDialect) (e := tileDialect) A')
        (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + j.val)))))
      (envInv n w ren (fun _ v => inrHom cs (Var.there v))) V W := by
    intro t v
    refine FormOk.entry t (ren t v) _ false (v.lookup V) W (fun _ => hren t v) ?_ ?_
    · exact (lookup_inrHom
        (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + j.val))) A
        (Var.there v)).symm
    · exact (hren t v).trans
        (lookup_inrHom (Valuation.extend (t := JasminTy.reg 64) V (BitVec.ofNat 64 (B + j.val)))
          (unmapInl (d := jasminDialect) (e := tileDialect) A') (Var.there v)).symm
  have h2 := h1.bind (Sum.inl (JasminTy.reg 64)) blk (t := JasminTy.reg 64) SForm.index
    (BitVec.ofNat 64 (B + j.val)) (FormOk.index _)
  have h3 := h2.carry cs (fun _ x => inlHom _ x) A A' (fun t x => lookup_inlHom _ x A)
    (fun t x => lookup_inlHom _ x (unmapInl (d := jasminDialect) (e := tileDialect) A'))
  exact h3.wk (Sum.inl (JasminTy.reg 64)) bw

end Entry

end CatCrypt.Crypto.SecureCompilation.VIR.LaneStripKernel
