/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MergeComDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldMultiReturn

/-!
# A Cooley–Tukey stage schema at arbitrary width and stage index

`VIR/NttStageFieldMultiReturn.lean` carries stage `1` of a four-point transform
as a hand-written `MultiReturnCom fieldDialect` with seven spelled-out bindings.
This file carries the schema it is an instance of: for a width `n`, a stage
index, and a twiddle base, a `MultiReturnCom fieldDialect` on `n` input lanes
returning `n` output lanes, together with its denotation against `CompPoly`'s
`butterflyStageSpec`.

## Main definitions

* `Com.foldVarN` — emit the first `m` of a family of single-return schedules one
  after another and hand their result variables, as an `HVector`, to a
  continuation.
* `Com.concatN` — the `MultiReturnCom` returning the results of the first `m`
  schedules of a family, in index order.
* `Com.denoteN` — the values those schedules denote to.
* `hvGetD`, `hvToList` — a replicated-type denotation read by index and as a
  list.
* `Ctxn` — the `n`-lane context `List.replicate n (fp q)`.
* `laneVar`, `arrVal` — the variable at lane `i` of an `n`-lane context, and the
  valuation reading an `Array (ZMod q)` from a starting offset.
* `laneProg` — the single-return schedule of one output lane: the twiddle as an
  `fConst`, the twiddle product, then one `fAdd` or `fSub`.
* `stageLane` — the value of output lane `i` of a stage.
* `stageLaneProg`, `stageProg` — the schedule of output lane `i`, and the
  `n`-output stage program as the concatenation of those `n` schedules.
* `innerRun`, `blockRun` — the two `Nat.rec`s of `butterflyStageSpec` as
  structural definitions.

## Main results

* `Com.foldVarN_denote`, `Com.concatN_denote` — the continuation-passing
  specification of `Com.foldVarN` and the denotation of `Com.concatN`.
* `innerRun_spec`, `blockStep_getD` — the entry at index `i` after `m` butterfly
  steps, and after one whole block: unchanged outside the window stepped so far,
  and the two butterfly lanes inside it.
* `butterflyStageSpec_getD` — the same, lane by lane, for an entire stage, at
  arbitrary width and stage index.
* `stageProg_denote` — lane `i` of `stageProg` denotes to the same value.
* `stageProg_denote_spec` — on an array of the domain's size,
  `butterflyStageSpec D stage` equals the `stageProg` denotation read back as an
  array.
* `stageProg4_lanes` — the schema's four lanes at width four and half-width two.
* `stage1Prog_eq_stageProg` — at width four and stage `1`, the hand-written
  program of `VIR/NttStageFieldMultiReturn.lean` and the schema denote alike.
* `stage1_denote_of_schema` — the stage-`1` statement of
  `VIR/NttStageFieldMultiReturn.lean`, re-derived from the schema.

## Scope

`stageProg` emits the two output lanes of a butterfly as independent schedules,
so each binds the shared twiddle product once per lane.  `Com.mergeTwo` peels a
shared prefix of two schedules and `MergeComDenote.Com.mergeTwo_denote` shows
the peel leaves the denotation alone, so the sharing is a program-level
transformation that this file's results are stated across.

`stageProg` is indexed by a twiddle base and a half-width rather than by a
`Domain`, and `butterflyStageSpec` is met at `half = 2 ^ stage` with
`stage < D.logN`, the range in which a stage's blocks tile the domain exactly.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (pullV_comp)
open CatCrypt.Crypto.SecureCompilation.VIR.MergeComDenote (Com.foldVar_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldMultiReturn
  (F constE addE subE mulE)
open CompPoly.CPolynomial.NTT (Domain)
open CompPoly.CPolynomial.NTT.Transform (butterflyStageSpec butterflyBlockStep butterflyInnerStep)

/-! ## 1. Emitting a family of schedules

`MergeComDenote` proves the denotation of `Com.foldVar`, which emits one
schedule's bindings and hands its result variable to a continuation, and of
`Com.concat2`, which chains two of those.  The same chaining at arbitrary length
is `Com.foldVarN`: the continuation receives one variable per schedule.

The schedules are kept over a fixed context `Γ₀` and carried into the growing
context by an accumulated renaming, so the recursion is on the count alone and
the return list is `List.replicate` of it. -/

/-- Emit the first `m` schedules of `f`, renamed into the current context, and
hand their result variables to `k`. -/
def Com.foldVarN {d : Dialect} [DialectSignature d] {ts : List d.Ty} {τ : d.Ty} :
    {Γ₀ : Ctxt d} → (m : Nat) → (Nat → Com d Γ₀ τ) → {Γ : Ctxt d} → Ctxt.Hom Γ₀ Γ →
    (∀ {Γ' : Ctxt d}, Ctxt.Hom Γ Γ' →
      HVector (fun t => Var Γ' t) (List.replicate m τ) →
      MultiReturnCom d Γ' ts) →
    MultiReturnCom d Γ ts
  | _, 0, _, _, _, k => k (Ctxt.Hom.id _) .nil
  | _, m + 1, f, _, h₀, k =>
      Com.foldVar (Com.rename h₀ (f 0)) (fun {_} h v =>
        Com.foldVarN m (fun i => f (i + 1)) (Ctxt.Hom.comp h h₀) (fun {_} h' vs =>
          k (Ctxt.Hom.comp h' h) (.cons (h' v) vs)))

/-- The values the first `m` schedules of `f` denote to, in index order. -/
def Com.denoteN {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] {Γ : Ctxt d} {τ : d.Ty} :
    (m : Nat) → (Nat → Com d Γ τ) → Valuation Γ → ListDenote (List.replicate m τ)
  | 0, _, _ => .nil
  | m + 1, f, V => .cons ((f 0).denote V) (Com.denoteN m (fun i => f (i + 1)) V)

/-- The continuation of `Com.foldVarN m f h₀ k` is called at an extension `Γ'`
of `Γ`, at a valuation pulling back to `V`, and at variables holding the values
the schedules denote to.  A continuation that produces `r` under those two facts
makes the fold produce `r`. -/
theorem Com.foldVarN_denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] {ts : List d.Ty} {τ : d.Ty} :
    ∀ {Γ₀ : Ctxt d} (m : Nat) (f : Nat → Com d Γ₀ τ) {Γ : Ctxt d}
      (h₀ : Ctxt.Hom Γ₀ Γ) (V : Valuation Γ)
      (k : ∀ {Γ' : Ctxt d}, Ctxt.Hom Γ Γ' →
        HVector (fun t => Var Γ' t) (List.replicate m τ) →
        MultiReturnCom d Γ' ts)
      (r : ListDenote ts),
      (∀ {Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ')
          (vs : HVector (fun t => Var Γ' t) (List.replicate m τ))
          (V' : Valuation Γ'),
          pullV h V' = V →
          MultiReturnCom.lookupVars vs V' = Com.denoteN m f (pullV h₀ V) →
          (k h vs).denote V' = r) →
      (Com.foldVarN m f h₀ k).denote V = r
  | _, 0, _, _, _, V, k, r, hk => by
      simp only [Com.foldVarN]
      exact hk (Ctxt.Hom.id _) .nil V (pullV_id V) rfl
  | _, m + 1, f, _, h₀, V, k, r, hk => by
      simp only [Com.foldVarN]
      refine Com.foldVar_denote (Com.rename h₀ (f 0)) V _ r ?_
      intro Γ' h v V' hV hv
      refine Com.foldVarN_denote m (fun i => f (i + 1)) (Ctxt.Hom.comp h h₀) V' _ r ?_
      intro Γ'' h' vs V'' hV'' hvs
      have hVV : pullV (Ctxt.Hom.comp h' h) V'' = V := by
        show pullV (fun v => h' (h v)) V'' = V
        rw [pullV_comp h h' V'', hV'', hV]
      refine hk (Ctxt.Hom.comp h' h) (.cons (h' v) vs) V'' hVV ?_
      have hcomp : pullV (Ctxt.Hom.comp h h₀) V' = pullV h₀ V := by
        show pullV (fun v => h (h₀ v)) V' = pullV h₀ V
        rw [pullV_comp h₀ h V', hV]
      rw [hcomp] at hvs
      show HVector.cons ((h' v).lookup V'') (MultiReturnCom.lookupVars vs V'')
        = HVector.cons ((f 0).denote (pullV h₀ V))
            (Com.denoteN m (fun i => f (i + 1)) (pullV h₀ V))
      rw [hvs, FieldDialectBlockDescent.Var.lookup_rename h' v V'', hV'', hv,
        FieldDialectBlockDescent.Com.denote_rename h₀ (f 0) V]

/-- The `MultiReturnCom` returning the results of the first `m` schedules of
`f`, in index order. -/
def Com.concatN {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {τ : d.Ty}
    (m : Nat) (f : Nat → Com d Γ τ) : MultiReturnCom d Γ (List.replicate m τ) :=
  Com.foldVarN m f (Ctxt.Hom.id Γ) (fun {_} _ vs => .ret vs)

/-- `Com.concatN m f` denotes to the values of the first `m` schedules of `f`. -/
theorem Com.concatN_denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] {Γ : Ctxt d} {τ : d.Ty} (m : Nat) (f : Nat → Com d Γ τ)
    (V : Valuation Γ) :
    (Com.concatN m f).denote V = Com.denoteN m f V := by
  refine Com.foldVarN_denote m f (Ctxt.Hom.id Γ) V _ _ ?_
  intro Γ' h vs V' _ hvs
  show MultiReturnCom.lookupVars vs V' = Com.denoteN m f V
  rw [hvs]
  show Com.denoteN m f (pullV (fun v => v) V) = Com.denoteN m f V
  rw [pullV_id]

/-- The `i`-th entry of a replicated-type denotation, and `0` past its end. -/
def hvGetD {q : Nat} : {m : Nat} → ListDenote (List.replicate m (F q)) → Nat → ZMod q
  | 0, _, _ => 0
  | _ + 1, .cons x _, 0 => x
  | _ + 1, .cons _ r, i + 1 => hvGetD r i

/-- A replicated-type denotation as a list, in index order. -/
def hvToList {q : Nat} : {m : Nat} → ListDenote (List.replicate m (F q)) → List (ZMod q)
  | 0, _ => []
  | _ + 1, .cons x r => x :: hvToList r

/-- `hvToList` has one entry per return type. -/
theorem hvToList_length {q : Nat} :
    ∀ {m : Nat} (hv : ListDenote (List.replicate m (F q))), (hvToList hv).length = m
  | 0, _ => rfl
  | _ + 1, .cons _ r => congrArg (· + 1) (hvToList_length r)

/-- Reading `hvToList` by index is `hvGetD`. -/
theorem hvToList_getD {q : Nat} :
    ∀ {m : Nat} (hv : ListDenote (List.replicate m (F q))) (i : Nat),
      (hvToList hv).getD i 0 = hvGetD hv i
  | 0, _, _ => rfl
  | _ + 1, .cons _ _, 0 => rfl
  | _ + 1, .cons _ r, i + 1 => hvToList_getD r i

/-- Reading `Com.denoteN` by index is the denotation of the schedule at that
index. -/
theorem hvGetD_denoteN {Γ : Ctxt fieldDialect} {q : Nat} :
    ∀ (m : Nat) (f : Nat → Com fieldDialect Γ (F q)) (V : Valuation Γ) (i : Nat),
      i < m → hvGetD (Com.denoteN m f V) i = PolyToField.fpDenote (f i) V
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, _, 0, _ => rfl
  | m + 1, f, V, i + 1, h =>
      hvGetD_denoteN m (fun j => f (j + 1)) V i (Nat.lt_of_succ_lt_succ h)

/-! ## 2. Lanes of a width-`n` field context

A stage's `n` lanes are `n` separate `fp q` bindings, so the input context is
`List.replicate n (fp q)` and a lane is fixed by its de Bruijn index.  `laneVar`
names the variable at an index of an `n+1`-lane context, clamping an index past
the end to lane `0`; `arrVal` reads an `Array (ZMod q)` into such a context from
a starting offset. -/

/-- The `n+1`-lane context. -/
abbrev Ctxn (q n : Nat) : Ctxt fieldDialect := List.replicate n (F q)

/-- The variable at lane `i` of an `n+1`-lane context. -/
def laneVar (q : Nat) : (n i : Nat) → Var (Ctxn q (n + 1)) (F q)
  | _, 0 => .here
  | 0, _ + 1 => .here
  | n + 1, i + 1 => .there (laneVar q n i)

/-- The valuation reading `a` from index `off` into an `n`-lane context. -/
def arrVal (q : Nat) (a : Array (ZMod q)) : (n off : Nat) → Valuation (Ctxn q n)
  | 0, _ => .nil
  | n + 1, off => .cons (a.getD off 0) (arrVal q a n (off + 1))

/-- A variable's value at type `ZMod q`. -/
def fpv {q : Nat} {Γ : Ctxt fieldDialect} (v : Var Γ (F q)) (V : Valuation Γ) :
    ZMod q := v.lookup V

/-- Lane `i` of `arrVal` holds entry `off + i` of the array. -/
theorem laneVar_lookup (q : Nat) (a : Array (ZMod q)) :
    ∀ (n i off : Nat), i ≤ n → fpv (laneVar q n i) (arrVal q a (n + 1) off)
      = a.getD (off + i) 0
  | _, 0, off, _ => by
      simp only [fpv, laneVar, arrVal, Nat.add_zero]
      rfl
  | 0, _ + 1, _, h => absurd h (by omega)
  | n + 1, i + 1, off, h => by
      show fpv (laneVar q n i) (arrVal q a (n + 1) (off + 1)) = a.getD (off + (i + 1)) 0
      rw [laneVar_lookup q a n i (off + 1) (by omega)]
      congr 1
      omega

/-! ## 3. The schedule of one output lane

An output lane of a stage is one operand of a butterfly: the twiddle as an
`fConst`, the twiddle product, then one `fAdd` (the lower operand of the pair)
or one `fSub` (the upper).  `laneProg` at width `0` has no lane to read and is
the twiddle constant alone; it is unreachable from a stage, whose lane indices
are below the width. -/

/-- The schedule of one output lane at width `n`: the twiddle `w`, the product
`w · a[ib]`, then `a[ia] + w · a[ib]` when `up`, and `a[ia] − w · a[ib]`
otherwise. -/
def laneProg (q : Nat) : (n : Nat) → ZMod q → Nat → Nat → Bool →
    Com fieldDialect (Ctxn q n) (F q)
  | 0, w, _, _, _ => .var (constE w) (.ret .here)
  | n + 1, w, ia, ib, up =>
      .var (constE w)
        (.var (mulE .here (.there (laneVar q n ib)))
          (.var (if up then addE (.there (.there (laneVar q n ia))) .here
                 else subE (.there (.there (laneVar q n ia))) .here)
            (.ret .here)))

/-- The lane schedule denotes to the butterfly operand it schedules. -/
theorem laneProg_denote (q n : Nat) (w : ZMod q) (ia ib : Nat) (up : Bool)
    (V : Valuation (Ctxn q (n + 1))) :
    PolyToField.fpDenote (laneProg q (n + 1) w ia ib up) V
      = if up then fpv (laneVar q n ia) V + w * fpv (laneVar q n ib) V
        else fpv (laneVar q n ia) V - w * fpv (laneVar q n ib) V := by
  cases up <;> rfl

/-! ## 4. The stage schema

A stage with half-width `half` and twiddle base `wm` pairs lane `i` with the
lane `half` away inside its block of `2·half` lanes: the block offset
`i % (half + half)` decides which of the two operands `i` is, and the running
twiddle at that offset is `wm` raised to it. -/

/-- The value of output lane `i` of a stage with half-width `half` and twiddle
base `wm`, on input lanes `a`. -/
def stageLane (q half : Nat) (wm : ZMod q) (a : Array (ZMod q)) (i : Nat) : ZMod q :=
  if i % (half + half) < half then
    a.getD i 0 + wm ^ (i % (half + half)) * a.getD (i + half) 0
  else
    a.getD (i - half) 0 - wm ^ (i % (half + half) - half) * a.getD i 0

/-- The schedule of output lane `i` of a stage of width `n`. -/
def stageLaneProg (q n half : Nat) (wm : ZMod q) (i : Nat) :
    Com fieldDialect (Ctxn q n) (F q) :=
  if i % (half + half) < half then
    laneProg q n (wm ^ (i % (half + half))) i (i + half) true
  else
    laneProg q n (wm ^ (i % (half + half) - half)) (i - half) i false

/-- One Cooley–Tukey stage of width `n`, half-width `half` and twiddle base
`wm`, as an `n`-input `n`-output `fieldDialect` program. -/
def stageProg (q n half : Nat) (wm : ZMod q) :
    MultiReturnCom fieldDialect (Ctxn q n) (List.replicate n (F q)) :=
  Com.concatN n (stageLaneProg q n half wm)

/-- The schedule of output lane `i` denotes to `stageLane` at `i`. -/
theorem stageLaneProg_denote (q n half : Nat) (wm : ZMod q) (a : Array (ZMod q))
    (i : Nat) (hi : i < n) (hh : 0 < half)
    (hup : i % (half + half) < half → i + half < n) :
    PolyToField.fpDenote (stageLaneProg q n half wm i) (arrVal q a n 0)
      = stageLane q half wm a i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [stageLaneProg, stageLane]
  split
  · next hlt =>
    rw [laneProg_denote, if_pos rfl, laneVar_lookup q a m i 0 (by omega),
      laneVar_lookup q a m (i + half) 0 (by have := hup hlt; omega)]
    simp
  · next hlt =>
    rw [laneProg_denote, if_neg (by simp), laneVar_lookup q a m (i - half) 0 (by omega),
      laneVar_lookup q a m i 0 (by omega)]
    simp

/-- Output lane `i` of `stageProg` denotes to `stageLane` at `i`. -/
theorem stageProg_denote (q n half : Nat) (wm : ZMod q) (a : Array (ZMod q))
    (hh : 0 < half) (hup : ∀ j, j < n → j % (half + half) < half → j + half < n)
    (i : Nat) (hi : i < n) :
    hvGetD ((stageProg q n half wm).denote (arrVal q a n 0)) i
      = stageLane q half wm a i := by
  rw [stageProg, Com.concatN_denote, hvGetD_denoteN n _ _ i hi]
  exact stageLaneProg_denote q n half wm a i hi hh (hup i hi)

/-! ## 5. `butterflyStageSpec` lane by lane

`butterflyStageSpec` writes its stage into an array with `Array.set!`, through
two nested `Nat.rec`s: an inner one over the `half` butterflies of a block and
an outer one over the blocks.  `innerRun` and `blockRun` are those two
recursions as ordinary structural definitions, and their specifications read
each recursion's array entry by entry: the indices one step writes are the two
lanes of its butterfly, every other index is left alone, and the windows of
distinct steps and distinct blocks are disjoint.

`Fact (Nat.Prime q)` supplies the `Field (ZMod q)` instance `butterflyInnerStep`
is stated over. -/

section Spec

variable {q : Nat} [Fact (Nat.Prime q)]

/-- Reading back the index a `set!` wrote. -/
theorem getD_set!_self (A : Array (ZMod q)) (j : Nat) (x : ZMod q)
    (h : j < A.size) : (A.set! j x).getD j 0 = x := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt h]
  rfl

/-- Reading back an index a `set!` did not write. -/
theorem getD_set!_ne (A : Array (ZMod q)) (j i : Nat) (x : ZMod q)
    (h : j ≠ i) : (A.set! j x).getD i 0 = A.getD i 0 := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne h, ← Array.getD_eq_getD_getElem?]

/-- An index inside a block reduces to its offset in that block. -/
theorem mod_eq_sub_of_block (half B i : Nat)
    (h1 : B * (half + half) ≤ i) (h2 : i < B * (half + half) + (half + half)) :
    i % (half + half) = i - B * (half + half) := by
  have hcomm : B * (half + half) = (half + half) * B := Nat.mul_comm _ _
  conv_lhs => rw [show i = (i - B * (half + half)) + (half + half) * B from by omega]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- The array and running twiddle after `m` butterfly steps of one block. -/
def innerRun (bs half : Nat) (wm : ZMod q) (block : Nat) (acc : Array (ZMod q)) :
    Nat → Array (ZMod q) × ZMod q
  | 0 => (acc, 1)
  | m + 1 => butterflyInnerStep bs half wm block m (innerRun bs half wm block acc m)

/-- `innerRun` is the inner `Nat.rec` of `butterflyBlockStep`. -/
theorem rec_eq_innerRun (bs half : Nat) (wm : ZMod q) (block : Nat)
    (acc : Array (ZMod q)) :
    ∀ m, (Nat.rec (motive := fun _ => Array (ZMod q) × ZMod q) (acc, (1 : ZMod q))
        (fun j st => butterflyInnerStep bs half wm block j st) m)
      = innerRun bs half wm block acc m
  | 0 => rfl
  | m + 1 => by
      simp only [innerRun]
      exact congrArg (butterflyInnerStep bs half wm block m)
        (rec_eq_innerRun bs half wm block acc m)

/-- One block of a stage is `half` butterfly steps. -/
theorem blockStep_eq_innerRun (bs half : Nat) (wm : ZMod q) (block : Nat)
    (acc : Array (ZMod q)) :
    butterflyBlockStep bs half wm block acc = (innerRun bs half wm block acc half).1 := by
  simp only [butterflyBlockStep]
  exact congrArg Prod.fst (rec_eq_innerRun bs half wm block acc half)

/-- After `m` butterfly steps of one block: the running twiddle is `wm ^ m`, the
array keeps its size, and its entries are the lower and upper butterfly lanes at
the `m` offsets already stepped and the input entry everywhere else. -/
theorem innerRun_spec (bs half : Nat) (hbs : bs = half + half) (hh : 0 < half)
    (wm : ZMod q) (block : Nat) (acc : Array (ZMod q))
    (hb : block * bs + bs ≤ acc.size) :
    ∀ m, m ≤ half →
      (innerRun bs half wm block acc m).2 = wm ^ m ∧
      (innerRun bs half wm block acc m).1.size = acc.size ∧
      ∀ i, (innerRun bs half wm block acc m).1.getD i 0 =
        if block * bs ≤ i ∧ i < block * bs + m then
          acc.getD i 0 + wm ^ (i - block * bs) * acc.getD (i + half) 0
        else if block * bs + half ≤ i ∧ i < block * bs + half + m then
          acc.getD (i - half) 0 - wm ^ (i - block * bs - half) * acc.getD i 0
        else acc.getD i 0 := by
  intro m
  induction m with
  | zero =>
      intro _
      refine ⟨(pow_zero wm).symm, rfl, fun i => ?_⟩
      rw [if_neg (by omega), if_neg (by omega)]
      rfl
  | succ m ih =>
      intro hm
      obtain ⟨h2, hsz, hget⟩ := ih (by omega)
      have hmh : m < half := by omega
      have hstep : innerRun bs half wm block acc (m + 1)
          = butterflyInnerStep bs half wm block m (innerRun bs half wm block acc m) := rfl
      have hu : (innerRun bs half wm block acc m).1.getD (block * bs + m) 0
          = acc.getD (block * bs + m) 0 := by
        rw [hget, if_neg (by omega), if_neg (by omega)]
      have hv : (innerRun bs half wm block acc m).1.getD (block * bs + m + half) 0
          = acc.getD (block * bs + m + half) 0 := by
        rw [hget, if_neg (by omega), if_neg (by omega)]
      have hres : (innerRun bs half wm block acc (m + 1)).1
          = ((innerRun bs half wm block acc m).1.set! (block * bs + m)
                (acc.getD (block * bs + m) 0
                  + wm ^ m * acc.getD (block * bs + m + half) 0)).set!
              (block * bs + m + half)
                (acc.getD (block * bs + m) 0
                  - wm ^ m * acc.getD (block * bs + m + half) 0) := by
        rw [hstep]
        simp only [butterflyInnerStep, hu, hv, h2]
      have hsz' : (innerRun bs half wm block acc (m + 1)).1.size = acc.size := by
        rw [hres]
        simp [hsz]
      refine ⟨?_, hsz', fun i => ?_⟩
      · rw [hstep]
        simp only [butterflyInnerStep, h2]
        rw [pow_succ]
      · rw [hres]
        by_cases h1 : i = block * bs + m + half
        · subst h1
          rw [getD_set!_self _ _ _ (by simp [hsz]; omega), if_neg (by omega),
            if_pos (by omega),
            show block * bs + m + half - half = block * bs + m from by omega,
            show block * bs + m + half - block * bs - half = m from by omega]
        · by_cases h0 : i = block * bs + m
          · subst h0
            rw [getD_set!_ne _ _ _ _ (by omega),
              getD_set!_self _ _ _ (by rw [hsz]; omega), if_pos (by omega),
              show block * bs + m - block * bs = m from by omega]
          · rw [getD_set!_ne _ _ _ _ (Ne.symm h1), getD_set!_ne _ _ _ _ (Ne.symm h0),
              hget i]
            split_ifs <;> first | rfl | omega

/-- One block of a stage: the two butterfly lanes inside the block's window, and
the input entry outside it. -/
theorem blockStep_getD (half : Nat) (hh : 0 < half) (wm : ZMod q) (block : Nat)
    (A : Array (ZMod q))
    (hb : block * (half + half) + (half + half) ≤ A.size) (i : Nat) :
    (butterflyBlockStep (half + half) half wm block A).getD i 0 =
      if block * (half + half) ≤ i ∧ i < block * (half + half) + half then
        A.getD i 0 + wm ^ (i - block * (half + half)) * A.getD (i + half) 0
      else if block * (half + half) + half ≤ i
          ∧ i < block * (half + half) + half + half then
        A.getD (i - half) 0 - wm ^ (i - block * (half + half) - half) * A.getD i 0
      else A.getD i 0 := by
  rw [blockStep_eq_innerRun]
  exact (innerRun_spec (half + half) half rfl hh wm block A hb half le_rfl).2.2 i

/-- The array after the first `B` blocks of a stage. -/
def blockRun (bs half : Nat) (wm : ZMod q) (acc : Array (ZMod q)) :
    Nat → Array (ZMod q)
  | 0 => acc
  | b + 1 => butterflyBlockStep bs half wm b (blockRun bs half wm acc b)

/-- `blockRun` is the outer `Nat.rec` of `butterflyStageSpec`. -/
theorem rec_eq_blockRun (bs half : Nat) (wm : ZMod q) (acc : Array (ZMod q)) :
    ∀ B, (Nat.rec (motive := fun _ => Array (ZMod q)) acc
        (fun block acc => butterflyBlockStep bs half wm block acc) B)
      = blockRun bs half wm acc B
  | 0 => rfl
  | B + 1 => by
      simp only [blockRun]
      exact congrArg (butterflyBlockStep bs half wm B) (rec_eq_blockRun bs half wm acc B)

/-- Blocks preserve the array's size. -/
theorem blockRun_size (bs half : Nat) (wm : ZMod q) (acc : Array (ZMod q)) :
    ∀ B, (blockRun bs half wm acc B).size = acc.size
  | 0 => rfl
  | B + 1 => by
      simp only [blockRun, CompPoly.CPolynomial.NTT.Transform.size_butterflyBlockStep]
      exact blockRun_size bs half wm acc B

/-- After the first `B` blocks of a stage, the entries below `B · 2·half` are
their stage lanes and the rest are unchanged. -/
theorem blockRun_spec (half : Nat) (hh : 0 < half) (wm : ZMod q)
    (acc : Array (ZMod q)) :
    ∀ B, B * (half + half) ≤ acc.size → ∀ i,
      (blockRun (half + half) half wm acc B).getD i 0 =
        if i < B * (half + half) then stageLane q half wm acc i else acc.getD i 0 := by
  intro B
  induction B with
  | zero => intro _ i; rw [if_neg (by omega)]; rfl
  | succ B ih =>
      intro hB i
      have hsucc : (B + 1) * (half + half) = B * (half + half) + (half + half) := by ring
      have IH := ih (by omega)
      have hsz : (blockRun (half + half) half wm acc B).size = acc.size :=
        blockRun_size (half + half) half wm acc B
      have hb : B * (half + half) + (half + half)
          ≤ (blockRun (half + half) half wm acc B).size := by rw [hsz]; omega
      have hstep : blockRun (half + half) half wm acc (B + 1)
          = butterflyBlockStep (half + half) half wm B
              (blockRun (half + half) half wm acc B) := rfl
      rw [hstep, blockStep_getD half hh wm B _ hb i]
      by_cases hc1 : B * (half + half) ≤ i ∧ i < B * (half + half) + half
      · have hmod : i % (half + half) = i - B * (half + half) :=
          mod_eq_sub_of_block half B i (by omega) (by omega)
        rw [if_pos hc1, IH i, IH (i + half), if_neg (by omega), if_neg (by omega),
          if_pos (by omega), stageLane, hmod, if_pos (by omega)]
      · by_cases hc2 : B * (half + half) + half ≤ i
            ∧ i < B * (half + half) + half + half
        · have hmod : i % (half + half) = i - B * (half + half) :=
            mod_eq_sub_of_block half B i (by omega) (by omega)
          rw [if_neg hc1, if_pos hc2, IH i, IH (i - half), if_neg (by omega),
            if_neg (by omega), if_pos (by omega), stageLane, hmod, if_neg (by omega)]
        · rw [if_neg hc1, if_neg hc2, IH i]
          by_cases hlt : i < B * (half + half)
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]

/-- Every lane of `butterflyStageSpec` on a domain-sized array, at any stage
index below the domain's `logN`. -/
theorem butterflyStageSpec_getD (D : Domain (ZMod q)) (stage : Nat)
    (hstage : stage < D.logN) (a : Array (ZMod q)) (ha : a.size = D.n)
    (i : Nat) (hi : i < D.n) :
    (butterflyStageSpec D stage a).getD i 0
      = stageLane q (2 ^ stage) (D.omega ^ (D.n / (2 ^ stage + 2 ^ stage))) a i := by
  have hpos : 0 < (2 : Nat) ^ stage := Nat.two_pow_pos stage
  have hbs : (2 : Nat) ^ (stage + 1) = 2 ^ stage + 2 ^ stage := by
    rw [pow_succ]; omega
  have hdvd : (2 : Nat) ^ stage + 2 ^ stage ∣ D.n := by
    rw [← hbs]
    simpa [Domain.n] using pow_dvd_pow 2 (Nat.succ_le_of_lt hstage)
  have hmul : D.n / (2 ^ stage + 2 ^ stage) * (2 ^ stage + 2 ^ stage) = D.n :=
    Nat.div_mul_cancel hdvd
  have hrun : butterflyStageSpec D stage a
      = blockRun (2 ^ stage + 2 ^ stage) (2 ^ stage)
          (D.omega ^ (D.n / (2 ^ stage + 2 ^ stage))) a
          (D.n / (2 ^ stage + 2 ^ stage)) := by
    rw [butterflyStageSpec, hbs]
    exact rec_eq_blockRun _ _ _ a _
  rw [hrun, blockRun_spec (2 ^ stage) hpos _ a _ (by omega) i, if_pos (by omega)]

/-- Lane `i + half` of a stage is inside the domain whenever lane `i` is the
lower operand of its butterfly. -/
theorem stage_partner_lt (D : Domain (ZMod q)) (stage : Nat) (hstage : stage < D.logN)
    (j : Nat) (hj : j < D.n) (hr : j % (2 ^ stage + 2 ^ stage) < 2 ^ stage) :
    j + 2 ^ stage < D.n := by
  have hpos : 0 < (2 : Nat) ^ stage := Nat.two_pow_pos stage
  have hbs : (2 : Nat) ^ (stage + 1) = 2 ^ stage + 2 ^ stage := by
    rw [pow_succ]; omega
  have hdvd : (2 : Nat) ^ stage + 2 ^ stage ∣ D.n := by
    rw [← hbs]
    simpa [Domain.n] using pow_dvd_pow 2 (Nat.succ_le_of_lt hstage)
  have hmul : D.n / (2 ^ stage + 2 ^ stage) * (2 ^ stage + 2 ^ stage) = D.n :=
    Nat.div_mul_cancel hdvd
  have hdm := Nat.div_add_mod j (2 ^ stage + 2 ^ stage)
  have hlt : j / (2 ^ stage + 2 ^ stage) < D.n / (2 ^ stage + 2 ^ stage) :=
    Nat.div_lt_div_of_lt_of_dvd hdvd hj
  have hle : (j / (2 ^ stage + 2 ^ stage) + 1) * (2 ^ stage + 2 ^ stage)
      ≤ D.n / (2 ^ stage + 2 ^ stage) * (2 ^ stage + 2 ^ stage) :=
    Nat.mul_le_mul_right _ hlt
  have hring : (j / (2 ^ stage + 2 ^ stage) + 1) * (2 ^ stage + 2 ^ stage)
      = (2 ^ stage + 2 ^ stage) * (j / (2 ^ stage + 2 ^ stage))
        + (2 ^ stage + 2 ^ stage) := by ring
  omega

/-! ## 6. The stage schema against `butterflyStageSpec` -/

/-- On an array of the domain's size, one stage of the transform is the
denotation of `stageProg` at that width, half-width and twiddle base. -/
theorem stageProg_denote_spec (D : Domain (ZMod q)) (stage : Nat)
    (hstage : stage < D.logN) (a : Array (ZMod q)) (ha : a.size = D.n) :
    butterflyStageSpec D stage a
      = (hvToList ((stageProg q D.n (2 ^ stage)
          (D.omega ^ (D.n / (2 ^ stage + 2 ^ stage)))).denote (arrVal q a D.n 0))).toArray := by
  have hpos : 0 < (2 : Nat) ^ stage := Nat.two_pow_pos stage
  have hsizeL : (butterflyStageSpec D stage a).size = D.n := by
    rw [CompPoly.CPolynomial.NTT.Transform.size_butterflyStageSpec, ha]
  have hsizeR : ((hvToList ((stageProg q D.n (2 ^ stage)
      (D.omega ^ (D.n / (2 ^ stage + 2 ^ stage)))).denote (arrVal q a D.n 0))).toArray).size
      = D.n := by
    rw [List.size_toArray, hvToList_length]
  have hentry : ∀ i, i < D.n →
      (butterflyStageSpec D stage a).getD i 0
        = (hvToList ((stageProg q D.n (2 ^ stage)
            (D.omega ^ (D.n / (2 ^ stage + 2 ^ stage)))).denote
            (arrVal q a D.n 0))).getD i 0 := by
    intro i hi
    rw [butterflyStageSpec_getD D stage hstage a ha i hi, hvToList_getD,
      stageProg_denote q D.n (2 ^ stage) _ a hpos
        (fun j hj hr => stage_partner_lt D stage hstage j hj hr) i hi]
  refine Array.ext (by rw [hsizeL, hsizeR]) (fun i h1 h2 => ?_)
  rw [Array.getElem_eq_getD (0 : ZMod q), List.getElem_toArray,
    List.getElem_eq_getD (0 : ZMod q), hentry i (by omega)]

/-- At width four and half-width two, the schema's four lanes are the two
butterflies on the lane pairs `(0, 2)` and `(1, 3)`, at twiddles `z ^ 0` and
`z ^ 1`. -/
theorem stageProg4_lanes (z x0 x1 x2 x3 : ZMod q) :
    hvToList ((stageProg q 4 2 z).denote (arrVal q #[x0, x1, x2, x3] 4 0))
      = [x0 + z ^ 0 * x2, x1 + z ^ 1 * x3, x0 - z ^ 0 * x2, x1 - z ^ 1 * x3] := by
  have hup : ∀ j, j < 4 → j % (2 + 2) < 2 → j + 2 < 4 := by decide
  rw [stageProg, Com.concatN_denote]
  simp only [Com.denoteN]
  have e0 := stageLaneProg_denote q 4 2 z #[x0, x1, x2, x3] 0 (by omega) (by omega) (hup 0 (by omega))
  have e1 := stageLaneProg_denote q 4 2 z #[x0, x1, x2, x3] 1 (by omega) (by omega) (hup 1 (by omega))
  have e2 := stageLaneProg_denote q 4 2 z #[x0, x1, x2, x3] 2 (by omega) (by omega) (hup 2 (by omega))
  have e3 := stageLaneProg_denote q 4 2 z #[x0, x1, x2, x3] 3 (by omega) (by omega) (hup 3 (by omega))
  simp only [PolyToField.fpDenote] at e0 e1 e2 e3
  rw [e0, e1, e2, e3]
  simp [stageLane]
  rfl

/-- At width four and stage `1`, the hand-written program of
`VIR/NttStageFieldMultiReturn.lean` and the schema denote alike. -/
theorem stage1Prog_eq_stageProg (D : Domain (ZMod q)) (hlog : D.logN = 2)
    (x0 x1 x2 x3 : ZMod q) :
    NttStageFieldMultiReturn.toArray4
        ((NttStageFieldMultiReturn.stage1Prog (q := q)).denote
          (NttStageFieldMultiReturn.stageVal D.omega x0 x1 x2 x3))
      = (hvToList ((stageProg q D.n (2 ^ 1)
          (D.omega ^ (D.n / (2 ^ 1 + 2 ^ 1)))).denote
          (arrVal q #[x0, x1, x2, x3] D.n 0))).toArray := by
  rw [← NttStageFieldMultiReturn.stage1_denote D hlog x0 x1 x2 x3]
  exact stageProg_denote_spec D 1 (by omega) #[x0, x1, x2, x3] (by simp [hlog])

/-- The stage-`1` statement of `VIR/NttStageFieldMultiReturn.lean` re-derived
from the schema: at `logN = 2`, `butterflyStageSpec D 1` is the hand-written
program's output. -/
theorem stage1_denote_of_schema (D : Domain (ZMod q)) (hlog : D.logN = 2)
    (x0 x1 x2 x3 : ZMod q) :
    butterflyStageSpec D 1 #[x0, x1, x2, x3]
      = NttStageFieldMultiReturn.toArray4
          ((NttStageFieldMultiReturn.stage1Prog (q := q)).denote
            (NttStageFieldMultiReturn.stageVal D.omega x0 x1 x2 x3)) := by
  obtain ⟨logN, ω, prim, nz⟩ := D
  subst hlog
  have h := stageProg_denote_spec (D := ⟨2, ω, prim, nz⟩) 1 (by norm_num)
    #[x0, x1, x2, x3] (by simp)
  norm_num at h
  rw [show (⟨2, ω, prim, nz⟩ : Domain (ZMod q)).n = 4 from rfl] at h
  rw [NttStageFieldMultiReturn.stage1Prog_denote, h, stageProg4_lanes]
  simp

end Spec

end CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral
