/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MergeCom
import CatCrypt.Crypto.Optimizer.Lattice.NttLayerComDenote
import CatCrypt.Crypto.Optimizer.Lattice.ConcreteRecursiveNtt

/-!
# The full `Com` layer-fold for the whole ML-KEM NTT, tied to `nttIter`/`dft`

## Scope

`NttLayerComDenote.lean` builds ONE denotable radix-2 NTT merge layer as a
`VIR.Com` (`nttLayerCom e`) and proves `nttLayerCom_denote_eq_nttIter`: its
`Com.denote`, on the two already-transformed contiguous halves and the geometric
twiddle vector, equals one full `nttIter (e+1)` layer under the negacyclic root
condition `ω^(2^e) = -1`. Its "Scope" names the remaining work: a **layer-fold
`Com`** sequencing the layers across all widths `e = 7,…,0`, threading each
layer's output into the next, discharging each per-layer `ω^(2^e) = -1` from the
ML-KEM primitive root `17`; and the **bit-reversal** front permutation tying the
fold to `dft`.

This file closes that **semantic full-NTT tie**. It builds:

* a denotable dialect `nttFoldDialect` over `vec e` (`⟦vec e⟧ = Fin (2^e) → ZMod
  3329`) with three ops — `loOp`/`hiOp` (the contiguous lower/upper half gather,
  denoting `lowerHalf`/`upperHalf`) and `mrgOp e ω` (the merge layer, denoting
  `mergeLayer e ω`, twiddles `ω^k` baked in);
* `nttFoldCom ω e : Com nttFoldDialect [vec e] (vec e)` — a single, genuinely
  recursive `VIR.Com`: at width `e+1` it gathers the two halves, recurses the
  fold at `ω²` on each, then applies the merge op. This is the whole layer-fold
  as ONE denotable program;
* `nttFoldCom_denote_eq_nttIter` — the **full-fold tie**:
  `(nttFoldCom ω e).denote (encode x) = nttIter e ω x`, by induction on `e`,
  reusing `mergeLayer_eq_nttIter` at every layer. The per-layer negacyclic
  obligation is supplied by the hypothesis bundle `NegacyclicTower`
  (`∀ d ≤ e, (ω^(2^d))^(2^(e-1-d)) = -1` collapses to one root power);
* `mlkemNttFoldCom`, the ML-KEM instantiation at `e = 8`, `ω = 17`, with the
  tower discharged from `(17 : ZMod 3329)^128 = -1`
  (`mlkem_negacyclic_128`, `native_decide`);
* `mlkemNttFoldCom_denote_eq_dft` — the full-fold Com, **pre-composed with the
  `bitrevPerm` reindex**, denotes to the length-256 `dft` at the ML-KEM
  parameters, via `IterativeNttEqRec.mlkem_nttIter_eq_dft`.

So the deliverable is a denotable `Com` for the WHOLE ML-KEM NTT whose
denotation (on the bit-reversed input) is `nttIter 8 17 = dft`.

### The Com-vs-jazz-vs-bytes boundary (read carefully — do NOT overclaim)

As in `NttLayerComDenote`/`NttButterflyComDenote`, three distinct objects and two
distinct gaps:

* **(this file) `nttFoldCom`/`mlkemNttFoldCom`** — a `VIR.Com nttFoldDialect`
  with a real `Com.denote`. We prove its denotation equals the genuine
  `nttIter`/`dft`. This is a Com-denotation ⟷ spec equality.
* **the `.jazz`-rendered §6b kernel** (`LatticeNttEmit.emitMlkemNttFull16wayJazz`)
  — a `String` over `BitVec` AVX2 lanes. **We do not prove `nttFoldCom` equals
  that emitted `.jazz` text.** The renderer has no `Com.denote`.
* **the emitted machine bytes** — tied to the spec only via the C byte-KAT
  against `PQCLEAN_MLKEM768_CLEAN_ntt`. **NOT proven here.**

This file closes the *semantic* full-NTT gap (a denotable Com for the whole
transform whose meaning is `dft`); it does **not** close the Com-↔-jazz-text gap
nor the jazz-↔-bytes (machine) gap.

### Cross-layer Montgomery accounting

The fiddly cross-layer Montgomery question (twiddles in Montgomery form `ω·R`
threaded across all layers) is the per-multiply bridge `montMulBridge` from
`NttLayerComDenote`, applied once per merge multiply; `nttFoldCom` uses plain
(non-Montgomery) twiddles `ω^k` baked into `mrgOp`, and `montMulBridge` is the
ingredient a Montgomery-domain refinement of `mrgOp` would discharge per multiply
(`montRed (a · montRepr ω) = a · ω`). Threading the Montgomery domain through the
op set is a representation change of `mrgOp`, not a change to the fold's meaning.

The only thing "trusted" here is nothing beyond Lean's kernel: `nttFoldDialect`
is a toy denotable dialect over `ZMod 3329`; the fold's denotation is closed by
the per-layer `mergeLayer_eq_nttIter` and a generic `Com.rename` denotation
lemma. `native_decide` appears once, for the concrete root fact
`(17 : ZMod 3329)^128 = -1` (the same style as the already-proven
`ConcreteNttRoots` order facts). No machine model, no `jasminc_preserves_ct`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NttFullFoldComDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec
open CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric (bitrevPerm)
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass (dft)
open CatCrypt.Crypto.Optimizer.Lattice.NttButterflyComDenote (q)
open CatCrypt.Crypto.Optimizer.Lattice.NttLayerComDenote
  (mergeLayer mergeLayer_eq_nttIter)

/-! ## 0. A generic `Com.rename` denotation lemma

`MergeCom.lean` defines `Com.rename`/`Ctxt.Hom` but proves the rename
denotation-preservation lemma only for specific dialects (`ComInline.lean` for
`jasminDialect`). The recursive `nttFoldCom` below renames the fold's two
recursive sub-`Com`s into the extended layer context, so we need that lemma
generically. We reprove the standard de-Bruijn substitution laws — `pullV`,
`lookup_rename`, `lookupArgs_rename`, `Expr.denote_rename`, `Com.denote_rename`
— for an arbitrary dialect with the four denotation typeclasses. -/

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-- Pullback of a `Valuation Γ'` along a context hom `h : Γ → Γ'`. -/
def pullV : {Γ : Ctxt d} → {Γ' : Ctxt d} →
    Ctxt.Hom Γ Γ' → Ctxt.Valuation Γ' → Ctxt.Valuation Γ
  | [], _, _, _ => HVector.nil
  | _ :: _, _, h, V =>
      HVector.cons ((h Ctxt.Var.here).lookup V)
        (pullV (fun v => h (.there v)) V)

omit [DialectSignature d] [DialectDenote d] in
/-- `pullV` depends on `h, V` only through `fun w => (h w).lookup V`. The single
master congruence from which the `lift`/`subst`/`weaken` pullbacks below all
follow. -/
theorem pullV_congr : {Γ : Ctxt d} → {Γ' Γ'' : Ctxt d} →
    (h₁ : Ctxt.Hom Γ Γ') → (h₂ : Ctxt.Hom Γ Γ'') →
    (V₁ : Ctxt.Valuation Γ') → (V₂ : Ctxt.Valuation Γ'') →
    (∀ {t : d.Ty} (w : Ctxt.Var Γ t), (h₁ w).lookup V₁ = (h₂ w).lookup V₂) →
    pullV h₁ V₁ = pullV h₂ V₂
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, _, _, h₁, h₂, V₁, V₂, hcong => by
    show HVector.cons _ _ = HVector.cons _ _
    congr 1
    · exact hcong Ctxt.Var.here
    · exact pullV_congr (fun w => h₁ (.there w)) (fun w => h₂ (.there w)) V₁ V₂
        (fun w => hcong (.there w))

omit [DialectSignature d] [DialectDenote d] in
/-- Looking up a renamed variable equals looking up the original in the
pullback. -/
theorem lookup_rename {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') {t : d.Ty}
    (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ') :
    (h v).lookup V = v.lookup (pullV h V) := by
  induction v with
  | here => rfl
  | @there Γ₀ t s w ih =>
    simp only [pullV]
    exact ih (fun v => h (.there v))

omit [DialectSignature d] [DialectDenote d] in
/-- `pullV (Hom.id Γ) V = V`. -/
theorem pullV_id {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
    pullV (Ctxt.Hom.id Γ) V = V := by
  induction Γ with
  | nil => cases V; rfl
  | cons s Γ₀ ih =>
    cases V with
    | cons a V₀ =>
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      -- tail: pullV (fun w => Hom.id (.there w)) (cons a V₀) = V₀
      rw [pullV_congr (h₁ := fun w => Ctxt.Hom.id _ (.there w))
            (h₂ := Ctxt.Hom.id Γ₀) (V₁ := HVector.cons a V₀) (V₂ := V₀)
            (fun w => rfl)]
      exact ih V₀

omit [DialectSignature d] [DialectDenote d] in
/-- **`pullV` commutes with `lift`.** Pulling back an extended valuation
`cons a V` along `h.lift` extends the pullback of `V` along `h` by `a`. -/
theorem pullV_lift {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') {s : d.Ty}
    (a : ⟦s⟧) (V : Ctxt.Valuation Γ') :
    pullV h.lift (HVector.cons a V) = HVector.cons a (pullV h V) := by
  show HVector.cons _ _ = HVector.cons _ _
  congr 1
  -- tail: pullV (fun w => h.lift (.there w)) (cons a V) = pullV h V
  exact pullV_congr (h₁ := fun w => h.lift (.there w)) (h₂ := h)
    (V₁ := HVector.cons a V) (V₂ := V) (fun w => rfl)

omit [DialectSignature d] [DialectDenote d] in
/-- Renaming an args-HVector and looking up equals looking up the original
against the pulled-back valuation. -/
theorem lookupArgs_rename {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') :
    {tys : List d.Ty} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    (V : Ctxt.Valuation Γ') →
    Expr.lookupArgs (HVector.renameVars h args) V
      = Expr.lookupArgs args (pullV h V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
    show HVector.cons _ _ = HVector.cons _ _
    congr 1
    · exact lookup_rename h v V
    · exact lookupArgs_rename h rest V

/-- Renaming an `Expr` and denoting it equals denoting the original against the
pulled-back valuation. -/
theorem Expr.denote_rename {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') {t : d.Ty}
    (e : Expr d Γ t) (V : Ctxt.Valuation Γ') :
    (e.rename h).denote V = e.denote (pullV h V) := by
  cases e with
  | mk op retTy_eq args =>
    simp only [Expr.rename, Expr.denote]
    rw [lookupArgs_rename h args V]

/-- **Generic `Com.rename` denotation preservation.** Denoting a renamed `Com`
on `V` equals denoting the original on the pulled-back valuation. -/
theorem Com.denote_rename : {Γ Γ' : Ctxt d} → {τ : d.Ty} →
    (h : Ctxt.Hom Γ Γ') → (c : Com d Γ τ) → (V : Ctxt.Valuation Γ') →
    (c.rename h).denote V = c.denote (pullV h V)
  | _, _, _, h, .ret v, V => lookup_rename h v V
  | _, _, _, h, .var (t := bs) e body, V => by
    show (Com.var (e.rename h) (body.rename h.lift)).denote V
        = (Com.var e body).denote (pullV h V)
    simp only [Com.denote, Ctxt.Valuation.extend]
    rw [Expr.denote_rename h e V]
    rw [Com.denote_rename h.lift body (.cons (e.denote (pullV h V)) V)]
    rw [pullV_lift]

/-! ## 1b. A generic single-return `Com.bind` (let-insertion)

The single-input-context ANF `Com` has `.ret`/`.var` but no combinator to feed
one `Com`'s result into a continuation. The recursive fold needs exactly that:
splice the fold-recursed-on-a-half `Com` and continue. We define a generic
let-insertion `Com.bind c body` and prove its denotation is the obvious
sequencing. -/

/-- The substitution hom `t :: Γ → Γ` sending the head `.here ↦ v` and every
`.there w ↦ w`. -/
def substHom {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t) : Ctxt.Hom (t :: Γ) Γ :=
  fun {_} w => match w with
    | .here => v
    | .there u => u

/-- **Single-return let-insertion.** Run `c`'s bindings, bind its result, then
run `body` with that result in scope. -/
def Com.bind : {Γ : Ctxt d} → {t s : d.Ty} →
    Com d Γ t → Com d (t :: Γ) s → Com d Γ s
  | _, _, _, .ret v, body => body.rename (substHom v)
  | _, _, _, .var (t := t') e c', body =>
      .var e (Com.bind c' (body.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ t'))))

omit [DialectSignature d] [DialectDenote d] in
/-- `pullV (substHom v) V` extends `V` by `v.lookup V` at the head. -/
theorem pullV_substHom {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ) :
    pullV (substHom v) V = HVector.cons (v.lookup V) V := by
  show HVector.cons _ _ = HVector.cons _ _
  congr 1
  -- tail: pullV (fun w => substHom v (.there w)) V = V; the tail of substHom is
  -- the identity hom.
  rw [pullV_congr (h₁ := fun w => substHom v (.there w))
        (h₂ := Ctxt.Hom.id Γ) (V₁ := V) (V₂ := V) (fun w => rfl)]
  exact pullV_id V

omit [DialectSignature d] [DialectDenote d] in
/-- `pullV (lift (weakenOne Γ t')) (cons a (cons b V)) = cons a V` — the
lift-of-weaken pulls back to dropping the freshly inserted binding `b`. -/
theorem pullV_lift_weakenOne {Γ : Ctxt d} {t' s : d.Ty}
    (a : ⟦s⟧) (b : ⟦t'⟧) (V : Ctxt.Valuation Γ) :
    pullV (Ctxt.Hom.lift (Ctxt.Hom.weakenOne Γ t'))
        (HVector.cons a (HVector.cons b V))
      = HVector.cons a V := by
  rw [pullV_lift]
  congr 1
  -- pullV (weakenOne Γ t') (cons b V) = V
  rw [pullV_congr (h₁ := Ctxt.Hom.weakenOne Γ t') (h₂ := Ctxt.Hom.id Γ)
        (V₁ := HVector.cons b V) (V₂ := V) (fun w => rfl)]
  exact pullV_id V

/-- **`Com.bind` denotation.** `(Com.bind c body).denote V` equals running `body`
with `c.denote V` bound at the head. -/
theorem Com.bind_denote : {Γ : Ctxt d} → {t s : d.Ty} →
    (c : Com d Γ t) → (body : Com d (t :: Γ) s) → (V : Ctxt.Valuation Γ) →
    (Com.bind c body).denote V = body.denote (HVector.cons (c.denote V) V)
  | _, _, _, .ret v, body, V => by
    show (body.rename (substHom v)).denote V = _
    rw [Com.denote_rename, pullV_substHom]
    rfl
  | _, _, _, .var (t := t') e c', body, V => by
    show (Com.var e
        (Com.bind c' (body.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ t'))))).denote V
      = _
    simp only [Com.denote, Ctxt.Valuation.extend]
    rw [Com.bind_denote c' _ (HVector.cons (e.denote V) V)]
    rw [Com.denote_rename]
    rw [pullV_lift_weakenOne]

/-- The hom `[t] → Γ` sending the single var `.here ↦ v`. -/
def oneVarHom {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t) :
    Ctxt.Hom [t] Γ :=
  fun {_} w => match w with
    | .here => v
    | .there u => nomatch u

/-- Run a single-input `Com [t] s` on the value held by variable `v` in `Γ`. -/
def Com.applyTo {Γ : Ctxt d} {t s : d.Ty} (c : Com d [t] s)
    (v : Ctxt.Var Γ t) : Com d Γ s :=
  c.rename (oneVarHom v)

omit [DialectSignature d] [DialectDenote d] in
/-- `pullV (oneVarHom v) V = cons (v.lookup V) nil` — the one-variable
valuation a single-input Com sees when applied to `v`. -/
theorem pullV_oneVarHom {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ) :
    pullV (oneVarHom v) V = HVector.cons (v.lookup V) HVector.nil := by
  show HVector.cons _ _ = HVector.cons _ _
  rfl

/-- **`Com.applyTo` denotation.** Running `c : Com [t] s` on `v` denotes to `c`'s
denotation on the singleton valuation `[v.lookup V]`. -/
theorem Com.applyTo_denote {Γ : Ctxt d} {t s : d.Ty} (c : Com d [t] s)
    (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ) :
    (Com.applyTo c v).denote V
      = c.denote (HVector.cons (v.lookup V) HVector.nil) := by
  show (c.rename (oneVarHom v)).denote V = _
  rw [Com.denote_rename, pullV_oneVarHom]

/-! ## 1. The fold dialect: vector type, half-gather ops, merge op -/

/-- The fold dialect's value-type alphabet: a length-`2^e` `ZMod 3329` vector. -/
inductive FTy where
  | vec (e : ℕ)
  deriving DecidableEq

/-- `vec e ↦ (Fin (2^e) → ZMod 3329)`. -/
@[reducible] def FTy.denote : FTy → Type
  | .vec e => Fin (2 ^ e) → ZMod q

instance : TyDenote FTy where
  denote := FTy.denote

/-- The fold dialect's ops: contiguous lower/upper half gather, and one merge
layer with the twiddle base `ω` baked in. -/
inductive FOp where
  | loOp (e : ℕ)
  | hiOp (e : ℕ)
  | mrgOp (e : ℕ) (ω : ZMod q)
  deriving DecidableEq

/-- The NTT layer-fold dialect. -/
@[reducible] def nttFoldDialect : Dialect :=
  { Op := FOp, Ty := FTy }

instance : DialectSignature nttFoldDialect where
  sig op := match op with
    | .loOp e => [FTy.vec (e + 1)]
    | .hiOp e => [FTy.vec (e + 1)]
    | .mrgOp e _ => [FTy.vec e, FTy.vec e]
  ret op := match op with
    | .loOp e => FTy.vec e
    | .hiOp e => FTy.vec e
    | .mrgOp e _ => FTy.vec (e + 1)

noncomputable instance nttFoldDenote : DialectDenote nttFoldDialect where
  denote op := match op with
    | .loOp e => fun args =>
        let x : Fin (2 ^ (e + 1)) → ZMod q := args.head
        lowerHalf e x
    | .hiOp e => fun args =>
        let x : Fin (2 ^ (e + 1)) → ZMod q := args.head
        upperHalf e x
    | .mrgOp e ω => fun args =>
        let L : Fin (2 ^ e) → ZMod q := args.head
        let U : Fin (2 ^ e) → ZMod q := args.tail.head
        mergeLayer e ω L U

/-! ## 2. The recursive fold `Com` -/

/-- A single-input layer context `[vec e]`. -/
abbrev Γfold (e : ℕ) : Ctxt nttFoldDialect := [FTy.vec e]

/-- `loOp e` applied to a `vec (e+1)` variable. -/
def loExpr (e : ℕ) {Γ : Ctxt nttFoldDialect} (x : Ctxt.Var Γ (FTy.vec (e + 1))) :
    Expr nttFoldDialect Γ (FTy.vec e) :=
  { op := .loOp e, retTy_eq := rfl, args := .cons x .nil }

/-- `hiOp e` applied to a `vec (e+1)` variable. -/
def hiExpr (e : ℕ) {Γ : Ctxt nttFoldDialect} (x : Ctxt.Var Γ (FTy.vec (e + 1))) :
    Expr nttFoldDialect Γ (FTy.vec e) :=
  { op := .hiOp e, retTy_eq := rfl, args := .cons x .nil }

/-- `mrgOp e ω` applied to two `vec e` variables `L`, `U`. -/
def mrgExpr (e : ℕ) (ω : ZMod q) {Γ : Ctxt nttFoldDialect}
    (L U : Ctxt.Var Γ (FTy.vec e)) :
    Expr nttFoldDialect Γ (FTy.vec (e + 1)) :=
  { op := .mrgOp e ω, retTy_eq := rfl, args := .cons L (.cons U .nil) }

/-- **The whole-NTT layer-fold as ONE recursive `VIR.Com`.** Input context
`[vec e]`. At width `0` it is the identity (`ret`). At width `e+1`:

1. `lo := loOp e input`, `hi := hiOp e input` (the two contiguous halves);
2. `L := (nttFoldCom ω² e) lo`, `U := (nttFoldCom ω² e) hi` — the fold recursed
   at the squared twiddle on each half, spliced in by renaming each recursive
   sub-`Com` into the extended layer context;
3. `mrgOp e ω L U` — the radix-2 merge layer.

This is the genuine layer-fold: every width from `e` down to `0` is sequenced as
`Com` bindings threading each layer's output into the next. -/
def nttFoldCom (ω : ZMod q) : (e : ℕ) → Com nttFoldDialect (Γfold e) (FTy.vec e)
  | 0 => .ret .here
  | (e + 1) =>
    -- Γ₀ = [vec (e+1)]: .here = input
    .var (loExpr e .here)
      -- Γ₁ = [vec e, vec (e+1)]: .here = lo, .there .here = input
      (.var (hiExpr e (.there .here))
        -- Γ₂ = [vec e, vec e, vec (e+1)]: .here = hi, .there .here = lo
        (Com.bind
          -- L := fold(ω²) recursed on the lower half (the `lo` slot)
          (Com.applyTo (nttFoldCom (ω ^ 2) e) (.there .here))
          -- Γ₃ = [vec e (=L), vec e (=hi), vec e (=lo), vec (e+1)]
          (Com.bind
            -- U := fold(ω²) recursed on the upper half (the `hi` slot, now
            -- shifted past L)
            (Com.applyTo (nttFoldCom (ω ^ 2) e) (.there .here))
            -- Γ₄ = [vec e (=U), vec e (=L), vec e (=hi), vec e (=lo), vec(e+1)]
            (.var (mrgExpr e ω (.there .here) .here) (.ret .here)))))

/-- The single-input valuation `[x]` for `Γfold e`. -/
def encodeFold (e : ℕ) (x : Fin (2 ^ e) → ZMod q) :
    Ctxt.Valuation (Γfold e) :=
  .cons x .nil

/-! ## 3. The negacyclic tower and the full-fold tie -/

/-- **The per-layer negacyclic obligation bundle.** `NegTower ω e` holds the
negacyclic root condition for *every* layer the fold at twiddle base `ω`, depth
`e`, traverses: the top layer needs `ω^(2^(e-1)) = -1`, and the two recursive
sub-folds at `ω²` need `NegTower (ω²) (e-1)`. (Unfolded for a concrete `ω₀`, each
conjunct collapses to the single root power `ω₀^(2^(e-1)) = -1`.) -/
def NegTower (ω : ZMod q) : (e : ℕ) → Prop
  | 0 => True
  | (e + 1) => ω ^ (2 ^ e) = -1 ∧ NegTower (ω ^ 2) e

/-- **The full-fold tie.** The denotation of the whole layer-fold `Com`
`nttFoldCom ω e` on the single input `x` equals the iterative DIT transform
`nttIter e ω x`. Proof by induction on `e`: at width `e+1` the `Com` denotation
unfolds (via `Com.bind_denote`/`Com.applyTo_denote` and the dialect op
denotations) to `mergeLayer e ω L U` with `L`/`U` the two recursive sub-fold
denotations; the IH at twiddle `ω²` rewrites those to `nttIter e ω² (lowerHalf
x)` / `nttIter e ω² (upperHalf x)`, and `mergeLayer_eq_nttIter` (fed the top
conjunct `ω^(2^e) = -1` of `NegTower`) closes the layer. -/
theorem nttFoldCom_denote_eq_nttIter : (e : ℕ) → (ω : ZMod q) →
    (x : Fin (2 ^ e) → ZMod q) → NegTower ω e →
    (nttFoldCom ω e).denote (encodeFold e x) = nttIter e ω x
  | 0, ω, x, _ => rfl
  | (e + 1), ω, x, htower => by
    -- The whole `(e+1)`-layer Com denotes to `mergeLayer e ω L U` with the two
    -- recursive sub-fold denotations as halves. This unfold is definitional:
    -- the two `.var`/`Com.bind` peels and the dialect op denotations reduce by
    -- `rfl` (the inner `applyTo` lookups pick out `lowerHalf`/`upperHalf x`).
    have hunfold :
        (nttFoldCom ω (e + 1)).denote (encodeFold (e + 1) x)
          = mergeLayer e ω
              ((nttFoldCom (ω ^ 2) e).denote (encodeFold e (lowerHalf e x)))
              ((nttFoldCom (ω ^ 2) e).denote (encodeFold e (upperHalf e x))) := by
      conv_lhs => rw [nttFoldCom]
      -- peel the two outer `.var` (lo, hi) bindings
      simp only [Com.denote, Ctxt.Valuation.extend]
      -- now the two `Com.bind`s and the inner `applyTo`s are exposed
      rw [Com.bind_denote, Com.bind_denote, Com.applyTo_denote,
        Com.applyTo_denote]
      rfl
    rw [hunfold,
      nttFoldCom_denote_eq_nttIter e (ω ^ 2) (lowerHalf e x) htower.2,
      nttFoldCom_denote_eq_nttIter e (ω ^ 2) (upperHalf e x) htower.2]
    exact mergeLayer_eq_nttIter e ω x htower.1

/-! ## 4. ML-KEM instantiation (`e = 8`, `ω = 17`) and the `dft` tie -/

/-- `(17 : ZMod 3329)^128 = -1`: the single negacyclic root power for ML-KEM.
Every layer's negacyclic condition collapses to this fact. -/
theorem mlkem_negacyclic_128 : (17 : ZMod q) ^ 128 = -1 := by native_decide

/-- **The ML-KEM negacyclic tower.** Each of the eight layers' negacyclic
conditions collapses to the single root power `17^128 = -1` (using
`(ω²)^(2^d) = ω^(2^(d+1))`); we close each concrete `ZMod 3329` power directly. -/
theorem mlkem_negTower : NegTower (17 : ZMod q) 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- **The full ML-KEM NTT layer-fold Com denotes to `nttIter 8 17`.** The whole
256-point ML-KEM forward NTT, as ONE denotable `VIR.Com`, has denotation equal to
the iterative DIT transform at the ML-KEM parameters. -/
theorem mlkemNttFoldCom_denote_eq_nttIter (x : Fin (2 ^ 8) → ZMod q) :
    (nttFoldCom (17 : ZMod q) 8).denote (encodeFold 8 x)
      = nttIter 8 (17 : ZMod q) x :=
  nttFoldCom_denote_eq_nttIter 8 (17 : ZMod q) x mlkem_negTower

/-- **The full ML-KEM NTT layer-fold Com, pre-composed with the bit-reversal
reindex, denotes to the length-256 `dft`.** Feeding the fold the bit-reversed
input `fun j => x (bitrevPerm 8 j)` makes the whole denotable Com compute the
definitional length-256 transform `dft` at the ML-KEM parameters — the full
semantic NTT tie, bit-reversal front permutation included. Chains
`mlkemNttFoldCom_denote_eq_nttIter` with
`IterativeNttEqRec.mlkem_nttIter_eq_dft`. -/
theorem mlkemNttFoldCom_denote_eq_dft (x : Fin (2 ^ 8) → ZMod q)
    (k : Fin (2 ^ 8)) :
    (nttFoldCom (17 : ZMod q) 8).denote
        (encodeFold 8 (fun j => x ((bitrevPerm 8) j))) k
      = dft (2 ^ 8) (17 : ZMod q) x k := by
  rw [mlkemNttFoldCom_denote_eq_nttIter]
  exact mlkem_nttIter_eq_dft x k

end CatCrypt.Crypto.Optimizer.Lattice.NttFullFoldComDenote
