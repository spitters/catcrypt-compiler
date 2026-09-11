/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.ForNToyDialect
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

@[expose] public section

set_option autoImplicit false

/-!
# Milestone 2 of the lean-mlir backend: the region + dynamic-memref model computes `mpn_add_n`

**EXPERIMENTAL / SELF-CONTAINED FILE.**  This is the *second verified milestone*
of the lean-mlir backend for the verified-GMP project.  Milestone 1
(`ForNToyDialect.lean`) isolated the two genuinely-new verification obligations
of the `scf.for` lowering — a region-carrying bounded loop `forN` (with
`agree_forN` / `forN_invariant`) and a dynamic-length memref `DynArr` (with the
conditional `loadDyn`/`storeDyn` agreement lemmas) — and proved an end-to-end
`dynLoop ≈ staticLoop` for a *no-carry* toy body.

This file **connects that region + dynamic-memref model to the actual
`mpn_add_n` semantics**.  The toy body of milestone 1 added a constant `c`
limb-by-limb with no carry; here the body is the genuine **ADC carry chain**
(`adcStep` from `Mpn.AddPrototype.lean`), threading a loop-carried carry bit
alongside the output array.  We prove that the `forN` loop's denotation computes
exactly the pure reference `mpnAddN`, and hence — composing with the
already-proved `mpnAddN_spec` — that it satisfies the multi-precision addition
identity

> `toNat (output limbs) + (2^64)^n · carry-out = toNat as + toNat bs`.

So the region + dynamic-memref MLIR model **provably computes multi-precision
add**.  The committed `scf.while` emission in `Mpn.MLIRBackend.lean` mirrors this
exact loop shape.

## What is proved here (all axiom-clean, no `sorry`)

* §1  The carry-chain body `addBody` (the ADC specialization of milestone 1's
  `dynStep`): read `a[i]`, `b[i]` via `loadDyn`, `adcStep`, write `out[i]` via
  `storeDyn`, thread the carry.  Plus `arrOfList`/`dynToList` to move between
  limb lists and `DynArr`s.
* §2  The single-step agreement `addBody_step` (the same conditional `loadDyn`/
  `storeDyn` in-bounds reasoning as ForNToyDialect's `agree_loadDyn`/
  `agree_storeDyn`), and the offset-threading induction
  `addBody_forN_offset` (the `mpn_add_n` analogue of milestone 1's
  `dynLoop_agree_offset`): the loop's accumulator after the limb-list recursion
  is `mpnAddN` of the consumed limbs.
* §3  `mpnAddN_forN_compute`: the loop computes `mpnAddN as bs false` (output
  array limbs and carry).  And the headline theorem `mpnAddN_forN`: the
  region + dynamic-memref model satisfies the multi-precision addition identity,
  by composing `mpnAddN_forN_compute` with `mpnAddN_spec`.

## Honest scope (what remains for the REAL verified MLIR lowering)

This is still the **toy dialect**, not VIR's `Com`:

1. `forN` and `DynArr` are Lean functions, not `VIR.Op` constructors wired
   through `Com.denote`.  The verified VIR `Com`
   (`SecureCompilation/VIR/Core.lean`) is A-normal form with no regions and no
   loops; closing this gap is the *shared-VIR-core* work (a region-carrying loop
   op + a dynamic memref in the real IR).
2. The `scf.while` text emitter in `Mpn.MLIRBackend.lean` is a **separate,
   unverified `String` formatter**.  It is *mirrored by* this structured loop,
   but it renders to text by hand.  Closing that gap means having the emitter
   render from this structured term (so the `String` it prints is provably the
   serialization of the `forN`/`DynArr` term proved correct here) — again the
   shared-VIR-core work.

What this file *does* establish, axiom-clean, is the denotational core: in the
region + dynamic-memref model, the `mpn_add_n` loop's denotation equals
`mpnAddN`, which satisfies the multi-precision addition spec.  That is
milestone 2.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.AddMLIRDenote

open CatCrypt.Crypto.Jasmin.Examples.ForNToyDialect
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

/-! ## §1  The ADC carry-chain body and list ↔ `DynArr` conversions

Milestone 1's `dynStep` did `out[i] := out[i] + c` (no carry).  The `mpn_add_n`
body reads *two* input arrays `a`, `b`, runs the genuine `adcStep` carry add, and
threads the carry bit alongside the output array in the loop-carried
accumulator.  The accumulator type is therefore `Option (DynArr × Bool)`: the
output array plus the running carry (the `Option` propagates an out-of-bounds
access, exactly as in milestone 1). -/

/-- Build a `DynArr` of length `|ws|` from a limb list, reading the `i`-th limb
    `ws[i]` at index `i`.  This is `ofStatic |ws| (fun i => ws.get i)` — the
    dynamic view of the input limb array `memref<?xi64>`. -/
def arrOfList (ws : List (BitVec 64)) : DynArr :=
  ofStatic ws.length (fun i => ws.get i)

@[simp] theorem arrOfList_len (ws : List (BitVec 64)) :
    (arrOfList ws).len = ws.length := rfl

/-- Read a `DynArr` back as a limb list (its in-bounds entries in index order).
    `dynToList (arrOfList ws) = ws`; for the loop output it recovers the result
    limb list whose `toNat` the spec talks about. -/
def dynToList (a : DynArr) : List (BitVec 64) :=
  (List.finRange a.len).map a.get

@[simp] theorem dynToList_len (a : DynArr) : (dynToList a).length = a.len := by
  simp only [dynToList, List.length_map, List.length_finRange]

theorem dynToList_getElem (a : DynArr) (i : Nat) (hi : i < (dynToList a).length) :
    (dynToList a)[i] = a.get ⟨i, by rw [dynToList_len] at hi; exact hi⟩ := by
  simp only [dynToList, List.getElem_map, List.getElem_finRange, Fin.cast_mk]

/-- `dynToList (arrOfList ws) = ws`: the round-trip on input limb lists. -/
@[simp] theorem dynToList_arrOfList (ws : List (BitVec 64)) :
    dynToList (arrOfList ws) = ws := by
  apply List.ext_getElem
  · simp only [dynToList_len, arrOfList_len]
  · intro i h1 h2
    rw [dynToList_getElem]
    simp only [arrOfList, ofStatic, List.get_eq_getElem]

/-- The ADC carry-chain loop body — the `mpn_add_n` specialization of milestone
    1's `dynStep`.  At index `i`, over input arrays `aArr`, `bArr` (closed over):
    load `a[i]`, `b[i]` (`loadDyn`, conditional on `i < len`), run `adcStep` with
    the loop-carried carry, write the sum to `out[i]` (`storeDyn`), and thread the
    new carry.  Propagates `none` (out of bounds), exactly as `dynStep`.

    The `scf.for` body that lowers to two `memref.load`s + the `#ADC_64`
    intrinsic + a `memref.store`, with the carry as an `iter_arg`. -/
def addBody (aArr bArr : DynArr) (i : Nat) (acc : Option (DynArr × Bool)) :
    Option (DynArr × Bool) := do
  let (out, carry) ← acc
  let wa ← loadDyn aArr i
  let wb ← loadDyn bArr i
  let (r, carry') := adcStep wa wb carry
  let out' ← storeDyn out i r
  some (out', carry')

/-! ## §2  Single-step agreement and the offset-threading induction

`addBody_step` is the `mpn_add_n` analogue of milestone 1's `dynStep_agree`: it
discharges the `i < len` in-bounds guards of `loadDyn`/`storeDyn` — the same
conditional-access reasoning that ForNToyDialect's `agree_loadDyn`/`agree_storeDyn`
package (here inlined on an arbitrary `DynArr` rather than an `ofStatic` view) —
and computes the exact one-limb ADC effect.

`addBody_forN_offset` is the analogue of milestone 1's `dynLoop_agree_offset`: a
base-offset induction over the consumed limb lists.  At write position `base`,
running `forN m` over input arrays that read `as'`/`bs'` at offset `base + i`
produces the output array updated on positions `base .. base + m - 1` with
`(mpnAddN as' bs' cin).1`, and carry `(mpnAddN as' bs' cin).2`.  The crux: the
per-iteration invariant ties the `forN` accumulator after `k` steps to
`mpnAddN (take k …) (take k …)` — here threaded as the head-peeling recursion of
`mpnAddN` itself (each step consumes one head limb, `adcStep_spec` is the
per-limb arithmetic, the carry threads forward). -/

/-- **Single-step agreement (consumes `agree_loadDyn`/`agree_storeDyn`).**  Under
    `i < aArr.len`, `i < bArr.len`, `i < out.len`, one `addBody` on
    `some (out, carry)` loads `aArr.get`/`bArr.get`, runs `adcStep`, stores the
    sum at `out[i]`, and yields the new carry.  The dynamic accesses succeed
    exactly because of the bounds (the only place the `i < len` side condition is
    discharged). -/
theorem addBody_step (aArr bArr out : DynArr) (i : Nat) (carry : Bool)
    (hia : i < aArr.len) (hib : i < bArr.len) (hio : i < out.len) :
    addBody aArr bArr i (some (out, carry))
      = some
          ({ len := out.len,
             get := fun j =>
               if j.val = i then (adcStep (aArr.get ⟨i, hia⟩) (bArr.get ⟨i, hib⟩) carry).1
               else out.get j },
           (adcStep (aArr.get ⟨i, hia⟩) (bArr.get ⟨i, hib⟩) carry).2) := by
  simp only [addBody, bind, Option.bind]
  -- Load `a[i]`: in-bounds (`agree_loadDyn` on the `ofStatic` view of `aArr`).
  rw [show loadDyn aArr i = some (aArr.get ⟨i, hia⟩) by
        simp only [loadDyn, hia, dif_pos]]
  dsimp only []
  -- Load `b[i]`: in-bounds.
  rw [show loadDyn bArr i = some (bArr.get ⟨i, hib⟩) by
        simp only [loadDyn, hib, dif_pos]]
  dsimp only []
  -- Store the sum at `out[i]`: in-bounds (`agree_storeDyn`).
  rw [show storeDyn out i (adcStep (aArr.get ⟨i, hia⟩) (bArr.get ⟨i, hib⟩) carry).1
        = some { len := out.len,
                 get := fun j =>
                   if j.val = i then (adcStep (aArr.get ⟨i, hia⟩) (bArr.get ⟨i, hib⟩) carry).1
                   else out.get j } by
        simp only [storeDyn, hio, dif_pos]]

/-- The result limb list of `mpnAddN` has the same length as the (equal-length)
    inputs.  By induction on the limb list; needed to index into
    `(mpnAddN …).1` in the per-position output characterization below. -/
theorem mpnAddN_length :
    ∀ (as bs : List (BitVec 64)) (cin : Bool),
      as.length = bs.length → (mpnAddN as bs cin).1.length = as.length := by
  intro as
  induction as with
  | nil => intro bs cin _; simp [mpnAddN]
  | cons a as ih =>
    intro bs cin hlen
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [mpnAddN, List.length_cons]
      rw [ih bs (adcStep a b cin).2 hlen']

/-- `DynArr.get` depends only on the index value: equal-value indices give equal
    entries.  Lets us realign `⟨(base+1)+i⟩` to `⟨base+(i+1)⟩` without a
    dependent rewrite into the `Fin` bounds proof. -/
theorem dynArr_get_congr (arr : DynArr) (i j : Nat) (hi : i < arr.len)
    (hj : j < arr.len) (h : i = j) : arr.get ⟨i, hi⟩ = arr.get ⟨j, hj⟩ := by
  subst h; rfl

/-- Reading back the array after a single in-bounds `storeDyn`-style head update
    (set position `pos` to `v`, leave the rest) is the `List.set` of the original
    array's list view.  Used to relate `dynToList out1` (after the head store) to
    `dynToList out0`. -/
theorem dynToList_setEntry (out0 : DynArr) (pos : Nat) (v : BitVec 64) :
    dynToList { len := out0.len, get := fun j => if j.val = pos then v else out0.get j }
      = (dynToList out0).set pos v := by
  apply List.ext_getElem
  · simp only [dynToList_len, List.length_set]
  · intro i h1 h2
    rw [dynToList_getElem]
    simp only [dynToList_len] at h1
    by_cases hip : i = pos
    · subst hip
      rw [List.getElem_set_self (by simpa using h2)]
      simp
    · rw [List.getElem_set_of_ne (Ne.symm hip) v (by simpa using h2), dynToList_getElem]
      simp only [if_neg hip]

/-- **Offset-threading induction (the `mpn_add_n` analogue of
    `dynLoop_agree_offset`).**  Run `forN m` with the body indexing at `base + i`,
    over input arrays `aArr`, `bArr` whose entries at the reached positions hold
    the limbs `as'`, `bs'` (hypotheses `hagree_a`/`hagree_b`), and an output array
    `out0` long enough (`base + m ≤ out0.len`).  Then the loop succeeds and:

    * the output array's entry at position `base + i` (for `i < m`) holds the
      `i`-th result limb `(mpnAddN as' bs' cin).1[i]`;
    * positions outside `base .. base + m - 1` are unchanged;
    * the carry is `(mpnAddN as' bs' cin).2`.

    Proof: induction on the consumed limb lists (lockstep `as'`, `bs'`, equal
    length).  The head step is `addBody_step` (one `adcStep`, the `i < len`
    bounds from `base + m ≤ len`); the recursion advances `base` to `base + 1`
    and threads the carry forward — exactly `mpnAddN`'s head-peeling recursion.
    `mpnAddN (a::as') (b::bs') cin` peels `adcStep a b cin` then recurses on the
    tails with the carry-out, which is what the loop does. -/
theorem addBody_forN_offset (aArr bArr : DynArr) :
    ∀ (as' bs' : List (BitVec 64)) (base : Nat) (cin : Bool) (out0 : DynArr)
      (hlen : as'.length = bs'.length)
      (hbound : base + as'.length ≤ out0.len)
      (hba : out0.len ≤ aArr.len) (hbb : out0.len ≤ bArr.len),
      (∀ i, (hi : i < as'.length) →
        aArr.get ⟨base + i, by omega⟩ = as'.get ⟨i, hi⟩) →
      (∀ i, (hi : i < bs'.length) →
        bArr.get ⟨base + i, by omega⟩ = bs'.get ⟨i, hi⟩) →
      ∃ out',
        forN as'.length (fun i acc => addBody aArr bArr (base + i) acc)
            (some (out0, cin))
          = some (out', (mpnAddN as' bs' cin).2) ∧
        out'.len = out0.len ∧
        dynToList out'
          = (dynToList out0).take base ++ (mpnAddN as' bs' cin).1
              ++ (dynToList out0).drop (base + as'.length) := by
  intro as'
  induction as' with
  | nil =>
    intro bs' base cin out0 _ _ _ _ _ _
    -- Empty: the loop does nothing; `mpnAddN [] _ cin = ([], cin)`.
    refine ⟨out0, by simp [mpnAddN], rfl, ?_⟩
    -- `take base l ++ [] ++ drop base l = l`.
    simp only [mpnAddN, List.length_nil, Nat.add_zero, List.append_nil]
    rw [List.take_append_drop]
  | cons a as' ih =>
    intro bs' base cin out0 hlen hbound hba hbb hagree_a hagree_b
    cases bs' with
    | nil => simp at hlen
    | cons b bs' =>
      have hlen' : as'.length = bs'.length := by simpa using hlen
      -- Bounds for the head limb (position `base`).
      have hia : base < aArr.len := by
        have : base < out0.len := by simp only [List.length_cons] at hbound; omega
        omega
      have hib : base < bArr.len := by
        have : base < out0.len := by simp only [List.length_cons] at hbound; omega
        omega
      have hio : base < out0.len := by simp only [List.length_cons] at hbound; omega
      -- The head input limbs read off as `a`, `b`.
      have hahead : aArr.get ⟨base, hia⟩ = a := by
        have := hagree_a 0 (by simp); simpa using this
      have hbhead : bArr.get ⟨base, hib⟩ = b := by
        have := hagree_b 0 (by simp); simpa using this
      -- Unfold one `forN` step: body at index `base + 0 = base`.
      rw [show (a :: as').length = as'.length + 1 from List.length_cons .., forN_succ]
      simp only [Nat.add_zero]
      -- The head `addBody` step (`addBody_step`), with the head limbs resolved.
      have hstep := addBody_step aArr bArr out0 base cin hia hib hio
      rw [hahead, hbhead] at hstep
      -- Name the one-limb ADC result and the array after the head store.
      set hd := adcStep a b cin with hhd
      set out1 : DynArr :=
        { len := out0.len,
          get := fun j => if j.val = base then hd.1 else out0.get j } with hout1
      rw [hstep]
      -- Shift the remaining bodies from `base + (i+1)` to `(base+1) + i`.
      have hshift :
          (fun i acc => addBody aArr bArr (base + (i + 1)) acc)
            = (fun i acc => addBody aArr bArr ((base + 1) + i) acc) := by
        funext i acc; rw [show base + (i + 1) = (base + 1) + i by omega]
      rw [hshift]
      have hbcons : (a :: as').length = as'.length + 1 := List.length_cons ..
      -- Re-establish the agreement hypotheses at the advanced base `base + 1`.
      -- The `aArr`/`bArr` index `(base+1)+i` equals `base+(i+1)`; rewrite the
      -- *goal* index to that form (`get` depends only on `.val`), then apply the
      -- shifted original hypothesis and the cons-get on the RHS.
      have hagree_a' : ∀ i, (hi : i < as'.length) →
          aArr.get ⟨(base + 1) + i, by omega⟩ = as'.get ⟨i, hi⟩ := by
        intro i hi
        have hkey := hagree_a (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.get_cons_succ] at hkey
        rw [dynArr_get_congr aArr ((base + 1) + i) (base + (i + 1))
          (by omega) (by omega) (by omega)]
        exact hkey
      have hagree_b' : ∀ i, (hi : i < bs'.length) →
          bArr.get ⟨(base + 1) + i, by omega⟩ = bs'.get ⟨i, hi⟩ := by
        intro i hi
        have hkey := hagree_b (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.get_cons_succ] at hkey
        rw [dynArr_get_congr bArr ((base + 1) + i) (base + (i + 1))
          (by omega) (by omega) (by omega)]
        exact hkey
      -- Recurse on the tails with carry `hd.2`, output `out1`.
      have hout1len : out1.len = out0.len := by rw [hout1]
      have hbound' : (base + 1) + as'.length ≤ out1.len := by
        rw [hout1len]; simp only [List.length_cons] at hbound; omega
      have hba' : out1.len ≤ aArr.len := by rw [hout1len]; exact hba
      have hbb' : out1.len ≤ bArr.len := by rw [hout1len]; exact hbb
      obtain ⟨out', hloop, hlen2, hget⟩ :=
        ih bs' (base + 1) hd.2 out1 hlen' hbound' hba' hbb' hagree_a' hagree_b'
      -- Assemble: carry component, length, per-position output.
      refine ⟨out', ?_, ?_, ?_⟩
      · -- Carry: `(mpnAddN (a::as') (b::bs') cin).2 = (mpnAddN as' bs' hd.2).2`.
        rw [hloop]
        simp only [mpnAddN, ← hhd]
      · -- Length: preserved through both the head store and the recursion.
        rw [hlen2, hout1len]
      · -- List-append output characterization.
        rw [hget]
        -- The result limbs of `mpnAddN (a::as') (b::bs') cin`, head-peeled.
        have hmlist : (mpnAddN (a :: as') (b :: bs') cin).1
            = hd.1 :: (mpnAddN as' bs' hd.2).1 := by
          simp only [mpnAddN, ← hhd]
        -- `dynToList out1 = (dynToList out0).set base hd.1` (the head store).
        have hd1list : dynToList out1 = (dynToList out0).set base hd.1 := by
          rw [hout1]; exact dynToList_setEntry out0 base hd.1
        -- `base < |dynToList out0|` (the head position is in bounds).
        have hbaselt : base < (dynToList out0).length := by rw [dynToList_len]; exact hio
        rw [hd1list, hmlist]
        -- (1) `take (base+1) (l.set base hd.1) = (take base l) ++ [hd.1]`.
        have htake : ((dynToList out0).set base hd.1).take (base + 1)
            = (dynToList out0).take base ++ [hd.1] := by
          apply List.ext_getElem
          · simp only [List.length_take, List.length_set, List.length_append,
              List.length_singleton]
            omega
          · intro i h1 h2
            simp only [List.length_take, List.length_set] at h1
            rw [List.getElem_take]
            by_cases hib : i < base
            · -- i < base: both sides read the unchanged `l[i]`.
              rw [List.getElem_set_of_ne (by omega) hd.1, List.getElem_append_left
                (by rw [List.length_take]; omega), List.getElem_take]
            · -- i = base: both sides read `hd.1`.
              have hieq : i = base := by omega
              subst hieq
              rw [List.getElem_set_self (by simpa using hbaselt),
                List.getElem_append_right (by rw [List.length_take]; omega)]
              simp only [List.length_take, Nat.min_eq_left (le_of_lt hbaselt), Nat.sub_self,
                List.getElem_singleton]
        -- (2) `drop ((base+1)+|as'|) (l.set base hd.1) = drop ((base+1)+|as'|) l`.
        have hdrop : ((dynToList out0).set base hd.1).drop ((base + 1) + as'.length)
            = (dynToList out0).drop ((base + 1) + as'.length) := by
          rw [List.drop_set, if_pos (by omega)]
        -- Reassemble: `(take base l ++ [hd.1]) ++ tail = take base l ++ (hd.1 :: tail)`.
        rw [htake, hdrop]
        simp only [List.append_assoc, List.cons_append, List.nil_append,
          show base + (as'.length + 1) = (base + 1) + as'.length by omega]

/-! ## §3  The headline theorems: the region + dynamic-memref model computes `mpnAddN`

`mpnAddN_forN_compute` specializes the offset induction to `base = 0`, with the
input arrays being the `arrOfList` views of the limb lists and a fresh output
array of length `n = |as| = |bs|`.  The loop succeeds, its carry is
`(mpnAddN as bs false).2`, and reading the output array back as a list
(`dynToList`) gives `(mpnAddN as bs false).1` exactly.

`mpnAddN_forN` then composes with `Mpn.AddPrototype.mpnAddN_spec` (the carry-chain
arithmetic, already proved there by induction on the limb list) to conclude the
multi-precision addition identity on the loop's *denotation* — the region +
dynamic-memref model provably computes multi-precision add. -/

/-- The loop over the `arrOfList` views, run on a fresh zero-length-free output
    array, computes `mpnAddN`: the output array read back as a list is
    `(mpnAddN as bs false).1`, and the carry is `(mpnAddN as bs false).2`. -/
theorem mpnAddN_forN_compute (as bs : List (BitVec 64))
    (hlen : as.length = bs.length) (out0 : DynArr) (hout0 : out0.len = as.length) :
    ∃ out',
      forN as.length
          (fun i acc => addBody (arrOfList as) (arrOfList bs) (0 + i) acc)
          (some (out0, false))
        = some (out', (mpnAddN as bs false).2) ∧
      dynToList out' = (mpnAddN as bs false).1 := by
  -- Instantiate the offset induction at `base = 0`.
  obtain ⟨out', hloop, hlen2, hget⟩ :=
    addBody_forN_offset (arrOfList as) (arrOfList bs) as bs 0 false out0 hlen
      (by rw [hout0]; omega)
      (le_of_eq (by rw [arrOfList_len, hout0]))
      (le_of_eq (by rw [arrOfList_len, hout0, hlen]))
      (by intro i hi; simp only [Nat.zero_add, arrOfList, ofStatic, List.get_eq_getElem])
      (by intro i hi; simp only [Nat.zero_add, arrOfList, ofStatic, List.get_eq_getElem])
  refine ⟨out', hloop, ?_⟩
  -- At `base = 0` with `|dynToList out0| = as.length`, the surrounding
  -- `take 0`/`drop as.length` slices are both empty, so the list equality
  -- collapses to `dynToList out' = (mpnAddN as bs false).1`.
  rw [hget]
  have hlist0 : (dynToList out0).length = as.length := by rw [dynToList_len, hout0]
  simp only [Nat.zero_add, List.take_zero, List.nil_append,
    List.drop_eq_nil_of_le (by rw [hlist0]), List.append_nil]

/-- **Milestone 2 — the region + dynamic-memref MLIR model computes
    `mpn_add_n`.**

    Expressing `mpn_add_n` as a `forN` loop in the toy dialect over dynamic-length
    memrefs (`addBody`, the ADC carry-chain body), its denotation satisfies the
    multi-precision addition identity: for equal-length limb lists `as`, `bs`
    (with horizon `n = |as| = |bs|`), the loop produces an output `DynArr` and a
    carry bit such that

    > `toNat (output limbs) + (2^64)^n · carry = toNat as + toNat bs`.

    The proof composes `mpnAddN_forN_compute` (the loop's denotation equals the
    pure reference `mpnAddN`, via `forN_succ` and the base-offset induction
    `addBody_forN_offset`, plus the conditional `loadDyn`/`storeDyn` agreement
    lemmas from milestone 1) with
    `Mpn.AddPrototype.mpnAddN_spec` (the carry-chain arithmetic, proved by
    induction on the limb list).  The `i < len` bounds that the dynamic memref
    accesses need come from the loop horizon `n = len`, threaded through the
    offset induction exactly as in milestone 1's `dynLoop_agree_offset`.

    The committed `scf.while` emission in `Mpn.MLIRBackend.lean` mirrors this loop
    shape.  This is the denotational core of the verified `scf.for`/`scf.while`
    lowering of `mpn_add_n`; see the closing docstring for what remains to make
    it the real verified MLIR lowering. -/
theorem mpnAddN_forN (as bs : List (BitVec 64)) (hlen : as.length = bs.length)
    (out0 : DynArr) (hout0 : out0.len = as.length) :
    ∃ out' : DynArr, ∃ carry : Bool,
      forN as.length
          (fun i acc => addBody (arrOfList as) (arrOfList bs) (0 + i) acc)
          (some (out0, false))
        = some (out', carry) ∧
      toNat (dynToList out') + (2 ^ 64) ^ as.length * carryNat carry
        = toNat as + toNat bs := by
  obtain ⟨out', hloop, hlist⟩ := mpnAddN_forN_compute as bs hlen out0 hout0
  refine ⟨out', (mpnAddN as bs false).2, hloop, ?_⟩
  rw [hlist]
  -- The carry-chain arithmetic identity, from `Mpn.AddPrototype.mpnAddN_spec`.
  exact mpnAddN_spec_carryIn_false as bs hlen

/-! ## §4  Honest note on what remains for the REAL verified MLIR lowering

`mpnAddN_forN` is axiom-clean: in the region + dynamic-memref model, the
`mpn_add_n` loop's denotation provably equals `mpnAddN` and hence satisfies the
multi-precision addition spec.  But this is still the **toy dialect**, not the
real verified chain.  Two gaps remain, both pointing at the same
*shared-VIR-core* work:

1. **Toy dialect ≠ VIR `Com`.**  `forN` (the region-carrying loop) and `DynArr`
   (the dynamic-length memref) are Lean functions, not `VIR.Op` constructors
   wired through `Com.denote`.  The verified VIR `Com`
   (`SecureCompilation/VIR/Core.lean`) is A-normal form with **no regions and no
   loops**.  Closing this means adding a region-carrying loop op and a dynamic
   memref to the real IR, with `Com.denote` extended accordingly — then
   re-proving `addBody`/`addBody_forN_offset` against those constructors instead
   of against the standalone Lean model here.

2. **The `scf.while` text emitter is a separate, unverified `String`
   formatter.**  `Mpn.MLIRBackend.lean` *renders* the `scf.while` loop to MLIR
   text by hand; this loop term is what that text *mirrors*, but there is no
   proof that the printed `String` is the serialization of this verified term.
   Closing that gap means having the emitter render *from this structured term*
   (so the emitted text is provably the serialization of the `forN`/`DynArr`
   loop proved correct here) — again the shared-VIR-core work, where the emitter
   pretty-prints the real IR rather than formatting strings independently.

So milestone 2 establishes the **denotational core** — the loop's denotation in
the region + dynamic-memref model equals `mpnAddN`, which satisfies the
multi-precision addition spec.  The remaining work is structural: lift the model
into VIR `Com` and drive the text emitter from the same structured term. -/

end CatCrypt.Crypto.Jasmin.Mpn.AddMLIRDenote
