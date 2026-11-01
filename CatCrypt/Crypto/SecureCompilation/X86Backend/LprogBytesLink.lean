/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT

/-!
# Linking at the byte level: appended streams and relocated runs

A linked object is one byte stream: a block of code followed by further blocks,
with branch and call displacements fixed at encoding time. This module gives the
two facts about `LprogBytesDecode.decodeLprog` and the machine of
`RInstrSemantics` that such a layout needs.

## Target resolution in the decoder

`decodeAt` tags every decoded instruction with its start and end byte offsets.
`resolveAll ctx` replaces the displacement `d` of a branch or call ending at
offset `e` by the index of the first entry of `ctx` whose start offset is
`e + d`, and fails when `ctx` has no such entry. `decodeLprog` resolves the
layout of a stream against itself. `resolveEntry` is the resolution of one
entry, and `resolveAll_eq_some_iff` states `resolveAll` entrywise.

## Appended streams

The first stream is given by an item list whose positions satisfy `ItemOK`, the
form in which `LprogBytesDecode` states that an instruction decodes in front of
every continuation; the second stream is any stream `decodeLprog` accepts. The
layout of the concatenation is the layout of the first stream followed by the
layout of the second with its offsets raised by the byte length of the first
(`decodeAt_items_append`, `decodeAt_offset`).

* `decodeLprog_append`: when both streams decode, the concatenation decodes to
  the first program followed by the second with every branch and call target
  raised by the instruction count of the first (`shiftProg`).
* `decodeLprog_append_resolved`: the same conclusion when the first stream's
  targets are resolved against the layout of the whole stream, which covers a
  first stream that calls into the second.
* `resolveEntry_call_cross`: a call of the first stream whose displacement lands
  on byte offset `o` of the second stream resolves to the instruction count of
  the first stream plus the index that offset `o` has in the second.

## Relocated runs

`shiftProg k p` adds `k` to every branch and call target of `p`. A run of `p`
from index `pc` is a run of `pre ++ shiftProg pre.length p ++ post` from index
`pre.length + pc`.

* `reaches_relocated`, `halts_relocated`: call-free runs relocate with the same
  states.
* `haltsC_relocated_rel`: a run through calls relocates up to a relation on
  states that satisfies `ShiftSim`. The relation is needed because a `call` at
  index `pc` stores the return index `pc + 1` in memory (`callOps`), and the
  relocated call stores `pre.length + pc + 1`.
* `haltsC_relocated`: for a block without `call` the relation is equality.
* `runL_relocated`: for a block without `call` the leakage trace of
  `DecodedCT.RunL` is unchanged.
* `haltsC_call_relocated`: a `call` in the linked program to the first index of
  a relocated call-free block runs that block as the callee and continues at the
  index after the call.

## Main results

* `decodeLprog_append`, `decodeLprog_append_resolved`: the program of an appended
  stream.
* `haltsC_relocated`, `haltsC_relocated_rel`, `runL_relocated`: runs and leakage of
  a block placed at an offset.
* `haltsC_call_relocated`: a call into a relocated block.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. Shifted targets and shifted offsets -/

/-- An instruction with its branch or call target raised by `k`. -/
def shiftInstr (k : Nat) : RInstr → RInstr
  | .jcc cc t => .jcc cc (k + t)
  | .call t => .call (k + t)
  | x => x

/-- A program with every branch and call target raised by `k`. -/
def shiftProg (k : Nat) (p : List RInstr) : List RInstr := p.map (shiftInstr k)

@[simp] theorem shiftProg_length (k : Nat) (p : List RInstr) :
    (shiftProg k p).length = p.length := by
  simp [shiftProg]

/-- The shift of a concatenation is the concatenation of the shifts. -/
theorem shiftProg_append (k : Nat) (p q : List RInstr) :
    shiftProg k (p ++ q) = shiftProg k p ++ shiftProg k q := by
  simp [shiftProg]

/-- Two shifts of an instruction are one shift by the sum. -/
theorem shiftInstr_shiftInstr (k j : Nat) (x : RInstr) :
    shiftInstr k (shiftInstr j x) = shiftInstr (k + j) x := by
  cases x <;> simp [shiftInstr, Nat.add_assoc]

/-- Two shifts of a program are one shift by the sum. -/
theorem shiftProg_shiftProg (k j : Nat) (p : List RInstr) :
    shiftProg k (shiftProg j p) = shiftProg (k + j) p := by
  simp [shiftProg, Function.comp_def, shiftInstr_shiftInstr]

/-- The shift by `0` is the identity. -/
theorem shiftProg_zero (p : List RInstr) : shiftProg 0 p = p := by
  have h : ∀ x, shiftInstr 0 x = x := fun x => by cases x <;> simp [shiftInstr]
  unfold shiftProg
  exact (List.map_congr_left fun x _ => h x).trans (List.map_id p)

/-- A layout entry with its start and end offsets raised by `c`. -/
def offsetEntry (c : Nat) (y : Nat × Nat × DInstr) : Nat × Nat × DInstr :=
  (y.1 + c, y.2.1 + c, y.2.2)

/-- A layout with every offset raised by `c`. -/
def offsetLayout (c : Nat) (xs : List (Nat × Nat × DInstr)) : List (Nat × Nat × DInstr) :=
  xs.map (offsetEntry c)

/-! ## 2. The stream decoder on an appended stream

The three lemmas of this section are about `LprogBytesDecode.decodeAt` and
belong beside it. -/

/-- A decoding that succeeds with some fuel succeeds with one more unit. -/
theorem decodeAt_fuel_succ :
    ∀ (n off : Nat) (bs : List (BitVec 8)) (xs : List (Nat × Nat × DInstr)),
      decodeAt n off bs = some xs → decodeAt (n + 1) off bs = some xs := by
  intro n
  induction n with
  | zero =>
    intro off bs xs h
    simp only [decodeAt] at h ⊢
    split at h
    · rename_i he; simp [he, h]
    · exact absurd h (by simp)
  | succ n ih =>
    intro off bs xs h
    rw [decodeAt] at h ⊢
    split
    · rename_i he; simpa [he] using h
    · rename_i he
      simp only [he] at h
      cases hd : decodeLinstr bs with
      | none => simp [hd] at h
      | some q =>
        obtain ⟨x, r⟩ := q
        simp only [hd] at h ⊢
        cases hys : decodeAt n (off + (bs.length - r.length)) r with
        | none => simp [hys] at h
        | some ys =>
          rw [hys] at h
          rw [ih _ _ _ hys]
          exact h

/-- A decoding that succeeds with some fuel succeeds with more. -/
theorem decodeAt_fuel_mono {n m off : Nat} {bs : List (BitVec 8)}
    {xs : List (Nat × Nat × DInstr)} (h : decodeAt n off bs = some xs) (hnm : n ≤ m) :
    decodeAt m off bs = some xs := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact decodeAt_fuel_succ _ _ _ _ ih

/-- Decoding from a start offset raised by `c` raises every offset of the layout by `c`. -/
theorem decodeAt_offset (c : Nat) :
    ∀ (n off : Nat) (bs : List (BitVec 8)),
      decodeAt n (off + c) bs = (decodeAt n off bs).map (offsetLayout c) := by
  intro n
  induction n with
  | zero => intro off bs; simp only [decodeAt]; split <;> simp [offsetLayout]
  | succ n ih =>
    intro off bs
    simp only [decodeAt]
    split
    · simp [offsetLayout]
    · cases hd : decodeLinstr bs with
      | none => simp
      | some q =>
        obtain ⟨x, r⟩ := q
        simp only [Option.map_map]
        rw [show off + c + (bs.length - r.length) = off + (bs.length - r.length) + c by omega,
          ih]
        simp only [Option.map_map]
        congr 1

/-- The number of decoded instructions of an item list is at most its byte length. -/
theorem decCount_le_length (items : List Item) (hok : ∀ it ∈ items, ItemOK it) :
    decCount items ≤ (itemBytes items).length := by
  induction items with
  | nil => simp [decCount]
  | cons it rest ih =>
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    have hbs : itemBytes (it :: rest) = it.bytes ++ itemBytes rest := by simp [itemBytes]
    unfold ItemOK at hit
    cases hdec : it.dec with
    | none => simp [decCount, hdec, hbs]; omega
    | some x =>
      rw [hdec] at hit
      have hpos : 0 < it.bytes.length := List.length_pos_iff.mpr hit.1
      simp [decCount, hdec, hbs]; omega

/-- Every start offset of the layout of an item list lies before the end of its bytes. -/
theorem layoutAt_start_lt (items : List Item) (hok : ∀ it ∈ items, ItemOK it) :
    ∀ off y, y ∈ layoutAt off items → y.1 < off + (itemBytes items).length := by
  induction items with
  | nil => intro off y hy; simp [layoutAt] at hy
  | cons it rest ih =>
    intro off y hy
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    have hbs : (itemBytes (it :: rest)).length = it.bytes.length + (itemBytes rest).length := by
      simp [itemBytes]
    unfold ItemOK at hit
    cases hdec : it.dec with
    | none =>
      simp only [layoutAt, hdec] at hy
      have := ih' _ y hy; omega
    | some x =>
      rw [hdec] at hit
      have hpos : 0 < it.bytes.length := List.length_pos_iff.mpr hit.1
      simp only [layoutAt, hdec, List.mem_cons] at hy
      rcases hy with rfl | hy
      · show off < _; omega
      · have := ih' _ y hy; omega

/-- **Layout of an appended stream.** The stream of an item list followed by a stream
    that decodes from the offset after it decodes to the layout of the items followed
    by the layout of the second stream. -/
theorem decodeAt_items_append (items : List Item) (hok : ∀ it ∈ items, ItemOK it)
    (bs₂ : List (BitVec 8)) (m : Nat) :
    ∀ (n off : Nat) (xs₂ : List (Nat × Nat × DInstr)),
      decodeAt m (off + (itemBytes items).length) bs₂ = some xs₂ →
      (layoutAt off items).length + m ≤ n →
      decodeAt n off (itemBytes items ++ bs₂) = some (layoutAt off items ++ xs₂) := by
  induction items with
  | nil =>
    intro n off xs₂ h hn
    simp only [layoutAt, itemBytes, List.flatMap_nil, List.length_nil, Nat.add_zero,
      List.nil_append, Nat.zero_add] at h hn ⊢
    exact decodeAt_fuel_mono h hn
  | cons it rest ih =>
    intro n off xs₂ h hn
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    have hbs : itemBytes (it :: rest) = it.bytes ++ itemBytes rest := by simp [itemBytes]
    rw [hbs, List.length_append, ← Nat.add_assoc] at h
    unfold ItemOK at hit
    cases hdec : it.dec with
    | none =>
      rw [hdec] at hit
      simp only [layoutAt, hdec, hit, List.length_nil, Nat.add_zero] at h hn ⊢
      simpa [hbs, hit] using ih' n off xs₂ h hn
    | some x =>
      rw [hdec] at hit
      obtain ⟨hne, hdecode⟩ := hit
      simp only [layoutAt, hdec, List.length_cons] at hn ⊢
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hemp : (it.bytes ++ (itemBytes rest ++ bs₂)).isEmpty = false := by
        cases hb : it.bytes with
        | nil => exact absurd hb hne
        | cons b t => rfl
      have hlen : (it.bytes ++ (itemBytes rest ++ bs₂)).length - (itemBytes rest ++ bs₂).length
          = it.bytes.length := by
        rw [List.length_append]; omega
      rw [hbs, List.append_assoc, decodeAt, hemp]
      simp only [Bool.false_eq_true, ite_false, hdecode, hlen]
      rw [ih' k (off + it.bytes.length) xs₂ h (by omega)]
      rfl

/-! ## 3. Target resolution entry by entry -/

/-- The resolution of one layout entry against the layout `ctx`: a branch or call ending
    at offset `e` with displacement `d` receives the index of the first entry of `ctx`
    that starts at `e + d`. -/
def resolveEntry (ctx : List (Nat × Nat × DInstr)) (y : Nat × Nat × DInstr) : Option RInstr :=
  match y.2.2 with
  | .op i => some (.op i)
  | .ret => some .ret
  | .push r => some (.push r)
  | .pop r => some (.pop r)
  | .jcc cc d =>
      (ctx.findIdx? fun z => decide ((z.1 : Int) = (y.2.1 : Int) + d)).map (.jcc cc)
  | .call d =>
      (ctx.findIdx? fun z => decide ((z.1 : Int) = (y.2.1 : Int) + d)).map .call

/-- `resolveAll ctx` succeeds exactly when every entry resolves against `ctx`, and its
    result lists the resolved entries. -/
theorem resolveAll_eq_some_iff (ctx : List (Nat × Nat × DInstr)) :
    ∀ (rest : List (Nat × Nat × DInstr)) (p : List RInstr),
      resolveAll ctx rest = some p ↔
        List.Forall₂ (fun y r => resolveEntry ctx y = some r) rest p := by
  intro rest
  induction rest with
  | nil => intro p; simp [resolveAll, eq_comm]
  | cons y rest ih =>
    intro p
    obtain ⟨s, e, x⟩ := y
    cases x <;>
      simp only [resolveAll, resolveEntry, List.forall₂_cons_left_iff, Option.map_eq_some_iff,
        ih, Option.some.injEq] <;>
      aesop

/-- The first entry of `xs₁ ++ offsetLayout c xs₂` that starts at `c + o`, when every
    entry of `xs₁` starts before `c`, is the first entry of `xs₂` that starts at `o`. -/
theorem findIdx?_offset_append (xs₁ xs₂ : List (Nat × Nat × DInstr)) (c o j : Nat) (q : Int)
    (hlt : ∀ z ∈ xs₁, z.1 < c) (hq : q = ((c + o : Nat) : Int))
    (h : xs₂.findIdx? (fun z => decide (z.1 = o)) = some j) :
    (xs₁ ++ offsetLayout c xs₂).findIdx? (fun z => decide ((z.1 : Int) = q))
      = some (xs₁.length + j) := by
  have h1 : xs₁.findIdx? (fun z => decide ((z.1 : Int) = q)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro z hz
    have := hlt z hz
    simp only [decide_eq_false_iff_not, hq]
    omega
  have h2 : ((fun z : Nat × Nat × DInstr => decide ((z.1 : Int) = q)) ∘ offsetEntry c)
      = fun z => decide (z.1 = o) := by
    funext z
    simp only [Function.comp, offsetEntry, hq, decide_eq_decide]
    omega
  simp only [offsetLayout, List.findIdx?_append, List.findIdx?_map, h1, h2, h, Option.none_or,
    Option.map_some, Nat.add_comm]

/-- The target of a branch that resolves inside `xs₂` resolves, after `xs₂` is placed
    behind `xs₁` with its offsets raised by `c`, to the same entry. -/
theorem findIdx?_target_shift (xs₁ xs₂ : List (Nat × Nat × DInstr)) (c e j : Nat) (d : Int)
    (hlt : ∀ z ∈ xs₁, z.1 < c)
    (h : xs₂.findIdx? (fun z => decide ((z.1 : Int) = (e : Int) + d)) = some j) :
    (xs₁ ++ offsetLayout c xs₂).findIdx?
        (fun z => decide ((z.1 : Int) = ((e + c : Nat) : Int) + d))
      = some (xs₁.length + j) := by
  have hnn : 0 ≤ (e : Int) + d := by
    by_contra hneg
    have hnone : xs₂.findIdx? (fun z => decide ((z.1 : Int) = (e : Int) + d)) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro z _
      simp only [decide_eq_false_iff_not]
      omega
    rw [hnone] at h
    exact absurd h (by simp)
  obtain ⟨o, ho⟩ := Int.eq_ofNat_of_zero_le hnn
  have hp : (fun z : Nat × Nat × DInstr => decide ((z.1 : Int) = (e : Int) + d))
      = fun z => decide (z.1 = o) := by
    funext z
    simp only [decide_eq_decide]
    omega
  rw [hp] at h
  exact findIdx?_offset_append xs₁ xs₂ c o j _ hlt (by push_cast; omega) h

/-- An entry that resolves against `xs₁` resolves to the same instruction against
    `xs₁` followed by any layout. -/
theorem resolveEntry_append_left (xs₁ ys : List (Nat × Nat × DInstr)) (y : Nat × Nat × DInstr)
    (r : RInstr) (h : resolveEntry xs₁ y = some r) : resolveEntry (xs₁ ++ ys) y = some r := by
  obtain ⟨s, e, x⟩ := y
  cases x with
  | op i => exact h
  | ret => exact h
  | push r => exact h
  | pop r => exact h
  | jcc cc d =>
    simp only [resolveEntry, Option.map_eq_some_iff] at h ⊢
    obtain ⟨j, hj, rfl⟩ := h
    exact ⟨j, by simp [List.findIdx?_append, hj], rfl⟩
  | call d =>
    simp only [resolveEntry, Option.map_eq_some_iff] at h ⊢
    obtain ⟨j, hj, rfl⟩ := h
    exact ⟨j, by simp [List.findIdx?_append, hj], rfl⟩

/-- An entry that resolves against `xs₂` resolves, with its offsets raised by `c`,
    against `xs₁ ++ offsetLayout c xs₂` to the same instruction with its target raised
    by the length of `xs₁`, when every entry of `xs₁` starts before `c`. -/
theorem resolveEntry_append_right (xs₁ xs₂ : List (Nat × Nat × DInstr)) (c : Nat)
    (y : Nat × Nat × DInstr) (r : RInstr) (hlt : ∀ z ∈ xs₁, z.1 < c)
    (h : resolveEntry xs₂ y = some r) :
    resolveEntry (xs₁ ++ offsetLayout c xs₂) (offsetEntry c y)
      = some (shiftInstr xs₁.length r) := by
  obtain ⟨s, e, x⟩ := y
  cases x with
  | op i => simp only [resolveEntry, Option.some.injEq] at h; subst h; rfl
  | ret => simp only [resolveEntry, Option.some.injEq] at h; subst h; rfl
  | push r => simp only [resolveEntry, Option.some.injEq] at h; subst h; rfl
  | pop r => simp only [resolveEntry, Option.some.injEq] at h; subst h; rfl
  | jcc cc d =>
    simp only [resolveEntry, Option.map_eq_some_iff] at h
    obtain ⟨j, hj, rfl⟩ := h
    exact congrArg (Option.map (RInstr.jcc cc)) (findIdx?_target_shift xs₁ xs₂ c e j d hlt hj)
  | call d =>
    simp only [resolveEntry, Option.map_eq_some_iff] at h
    obtain ⟨j, hj, rfl⟩ := h
    exact congrArg (Option.map RInstr.call) (findIdx?_target_shift xs₁ xs₂ c e j d hlt hj)

/-- **A call across the seam.** A call ending at offset `e` whose displacement lands on
    offset `c + o`, resolved against `xs₁ ++ offsetLayout c xs₂` with every entry of
    `xs₁` starting before `c`, receives the length of `xs₁` plus the index of the first
    entry of `xs₂` that starts at `o`. -/
theorem resolveEntry_call_cross (xs₁ xs₂ : List (Nat × Nat × DInstr)) (c s e o j : Nat)
    (d : Int) (hlt : ∀ z ∈ xs₁, z.1 < c) (hland : (e : Int) + d = ((c + o : Nat) : Int))
    (h : xs₂.findIdx? (fun z => decide (z.1 = o)) = some j) :
    resolveEntry (xs₁ ++ offsetLayout c xs₂) (s, e, .call d)
      = some (.call (xs₁.length + j)) := by
  simp only [resolveEntry]
  rw [findIdx?_offset_append xs₁ xs₂ c o j _ hlt hland h]
  rfl

/-! ## 4. The program of an appended stream -/

/-- **Decoding of an appended stream, targets resolved in the whole.** Let `items`
    satisfy `ItemOK`, let `bs₂` decode to the layout `xs₂` and the program `p₂`, and let
    the layout of `items` resolve to `p₁` against the layout of the whole stream. Then
    `itemBytes items ++ bs₂` decodes to `p₁` followed by `p₂` with its targets raised by
    the instruction count of `items`. The first stream may branch or call into the
    second. -/
theorem decodeLprog_append_resolved (items : List Item) (hok : ∀ it ∈ items, ItemOK it)
    (bs₂ : List (BitVec 8)) (xs₂ : List (Nat × Nat × DInstr)) (p₁ p₂ : List RInstr)
    (hd : decodeAt bs₂.length 0 bs₂ = some xs₂) (h₂ : resolveAll xs₂ xs₂ = some p₂)
    (h₁ : resolveAll (layoutAt 0 items ++ offsetLayout (itemBytes items).length xs₂)
      (layoutAt 0 items) = some p₁) :
    decodeLprog (itemBytes items ++ bs₂) = some (p₁ ++ shiftProg (decCount items) p₂) := by
  have hd' : decodeAt bs₂.length (0 + (itemBytes items).length) bs₂
      = some (offsetLayout (itemBytes items).length xs₂) := by
    rw [decodeAt_offset, hd]; rfl
  have hall := decodeAt_items_append items hok bs₂ bs₂.length
    (itemBytes items ++ bs₂).length 0 _ hd' (by
      rw [layoutAt_length, List.length_append]
      have := decCount_le_length items hok
      omega)
  have hlt : ∀ z ∈ layoutAt 0 items, z.1 < (itemBytes items).length := fun z hz => by
    simpa using layoutAt_start_lt items hok 0 z hz
  unfold decodeLprog
  rw [hall, Option.bind_some, resolveAll_eq_some_iff]
  rw [resolveAll_eq_some_iff] at h₁ h₂
  refine List.rel_append h₁ (List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
    (h₂.imp fun y r hy => ?_)))
  rw [← layoutAt_length items 0]
  exact resolveEntry_append_right _ _ _ y r hlt hy

/-- **Decoding of an appended stream.** When the stream of an `ItemOK` item list decodes
    to `p₁` and `bs₂` decodes to `p₂`, their concatenation decodes to `p₁` followed by
    `p₂` with every branch and call target raised by the length of `p₁`. The targets of
    `p₁` are unchanged. -/
theorem decodeLprog_append (items : List Item) (hok : ∀ it ∈ items, ItemOK it)
    (bs₂ : List (BitVec 8)) (p₁ p₂ : List RInstr)
    (h₁ : decodeLprog (itemBytes items) = some p₁) (h₂ : decodeLprog bs₂ = some p₂) :
    decodeLprog (itemBytes items ++ bs₂) = some (p₁ ++ shiftProg p₁.length p₂) := by
  unfold decodeLprog at h₁ h₂
  rw [decodeAt_items items hok _ 0 (by
    rw [layoutAt_length]; exact decCount_le_length items hok), Option.bind_some] at h₁
  obtain ⟨xs₂, hd, hr⟩ := Option.bind_eq_some_iff.mp h₂
  have hlen : p₁.length = decCount items := by
    rw [← layoutAt_length items 0]
    exact ((resolveAll_eq_some_iff _ _ _).mp h₁).length_eq.symm
  rw [hlen]
  refine decodeLprog_append_resolved items hok bs₂ xs₂ p₁ p₂ hd hr ?_
  rw [resolveAll_eq_some_iff] at h₁ ⊢
  exact h₁.imp fun y r hy => resolveEntry_append_left _ _ y r hy

/-! ## 5. Relocated runs -/

variable {σ : Type}

/-- The instruction at index `pre.length + pc` of the relocated program is the
    instruction of `p` at `pc` with its target raised by `pre.length`. -/
theorem getElem?_relocated (pre p post : List RInstr) {pc : Nat} {x : RInstr}
    (h : p[pc]? = some x) :
    (pre ++ shiftProg pre.length p ++ post)[pre.length + pc]?
      = some (shiftInstr pre.length x) := by
  have hlt : pc < p.length := (List.getElem?_eq_some_iff.mp h).1
  rw [getElem?_segment pre _ post pc (by simpa using hlt)]
  simp [shiftProg, h]

/-- A continuing step of `p` at `pc` is a continuing step of the relocated program at
    `pre.length + pc`, to the program counter raised by `pre.length` and the same state. -/
theorem step_relocated (M : Machine σ) (pre p post : List RInstr) {pc pc' : Nat} {s s' : σ}
    (h : RInstrSemantics.step M p pc s = some (.go pc' s')) :
    RInstrSemantics.step M (pre ++ shiftProg pre.length p ++ post) (pre.length + pc) s
      = some (.go (pre.length + pc') s') := by
  unfold RInstrSemantics.step at h ⊢
  cases hx : p[pc]? with
  | none => simp [hx] at h
  | some x =>
    rw [getElem?_relocated pre p post hx]
    rw [hx] at h
    cases x with
    | op i =>
      simp only [Option.some.injEq, Next.go.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | ret => simp at h
    | push r =>
      simp only [Option.some.injEq, Next.go.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | pop r =>
      simp only [Option.some.injEq, Next.go.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | call t => simp at h
    | jcc cc t =>
      cases hc : condtOfNibble cc with
      | none => simp [hc] at h
      | some c =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        simp only [shiftInstr, hc, Option.map_some, Option.some.injEq]
        split at h <;> simp only [Next.go.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
          simp_all [Nat.add_assoc]

/-- **Relocation of call-free paths.** A path of `p` is a path of the relocated program
    with both program counters raised by `pre.length` and the same states. -/
theorem reaches_relocated (M : Machine σ) (pre p post : List RInstr) {pc pc' : Nat} {s s' : σ}
    (h : Reaches M p pc s pc' s') :
    Reaches M (pre ++ shiftProg pre.length p ++ post) (pre.length + pc) s
      (pre.length + pc') s' := by
  induction h with
  | refl => exact .refl _ _
  | next hs _ ih => exact .next (step_relocated M pre p post hs) ih

/-- **Relocation of call-free halting runs.** A halting run of `p` from `pc` is a halting
    run of the relocated program from `pre.length + pc` with the same final state. -/
theorem halts_relocated (M : Machine σ) (pre p post : List RInstr) {pc : Nat} {s s' : σ}
    (h : HaltsNoCall M p pc s s') :
    HaltsNoCall M (pre ++ shiftProg pre.length p ++ post) (pre.length + pc) s s' := by
  obtain ⟨pc', hr, hret⟩ := h
  exact ⟨pre.length + pc', reaches_relocated M pre p post hr,
    getElem?_relocated pre p post hret⟩

/-- A relation between the states of a run of `p` and of its copy relocated by `k`:
    it is preserved by every instruction, related states have the same conditions on
    their views, and it relates the state after a `call` of `p` at `pc` stores the
    return index `pc + 1` to the state after the relocated call stores `k + (pc + 1)`. -/
structure ShiftSim (M : Machine σ) (p : List RInstr) (k : Nat) (R : σ → σ → Prop) :
    Prop where
  /-- One instruction preserves the relation. -/
  exec : ∀ s t i, R s t → R (M.exec s i) (M.exec t i)
  /-- Related states agree on every branch condition. -/
  cond : ∀ s t c, R s t → (M.view s).condB c = (M.view t).condB c
  /-- The two stores of a return index preserve the relation. -/
  call : ∀ pc tg s t, p[pc]? = some (.call tg) → R s t →
    R ((callOps (pc + 1)).foldl M.exec s) ((callOps (k + (pc + 1))).foldl M.exec t)

/-- A straight-line block preserves a relation that each instruction preserves. -/
theorem ShiftSim.foldl {M : Machine σ} {p : List RInstr} {k : Nat} {R : σ → σ → Prop}
    (hS : ShiftSim M p k R) :
    ∀ (ops : List (JInstr 64)) (s t : σ), R s t → R (ops.foldl M.exec s) (ops.foldl M.exec t)
  | [], _, _, h => h
  | i :: is, _, _, h => hS.foldl is _ _ (hS.exec _ _ i h)

/-- Equality is a `ShiftSim` for a block without `call`. -/
theorem shiftSim_eq (M : Machine σ) (p : List RInstr) (k : Nat)
    (hp : ∀ tg, RInstr.call tg ∉ p) : ShiftSim M p k Eq where
  exec := fun _ _ _ h => by rw [h]
  cond := fun _ _ _ h => by rw [h]
  call := fun _ tg _ _ h _ => absurd (List.mem_of_getElem? h) (hp tg)

/-- A continuing step of `p` is matched from a related state by a step of the relocated
    program to a related state. -/
theorem step_relocated_rel {M : Machine σ} {pre p post : List RInstr} {R : σ → σ → Prop}
    (hS : ShiftSim M p pre.length R) {pc pc' : Nat} {s s' t : σ}
    (h : RInstrSemantics.step M p pc s = some (.go pc' s')) (hR : R s t) :
    ∃ t', RInstrSemantics.step M (pre ++ shiftProg pre.length p ++ post) (pre.length + pc) t
        = some (.go (pre.length + pc') t') ∧ R s' t' := by
  unfold RInstrSemantics.step at h ⊢
  cases hx : p[pc]? with
  | none => simp [hx] at h
  | some x =>
    rw [getElem?_relocated pre p post hx]
    rw [hx] at h
    cases x with
    | op i =>
      simp only [Option.some.injEq, Next.go.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hS.exec _ _ i hR⟩
    | ret => simp at h
    | push r =>
      simp only [Option.some.injEq, Next.go.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hS.foldl _ _ _ hR⟩
    | pop r =>
      simp only [Option.some.injEq, Next.go.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hS.foldl _ _ _ hR⟩
    | call tg => simp at h
    | jcc cc tg =>
      cases hc : condtOfNibble cc with
      | none => simp [hc] at h
      | some c =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        simp only [shiftInstr, hc, Option.map_some, Option.some.injEq, ← hS.cond s t c hR]
        split at h <;> simp only [Next.go.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
          simp_all [Nat.add_assoc]

/-- **Relocation of runs through calls.** Let `R` satisfy `ShiftSim` for `p` and
    `pre.length`. A run of `p` through calls from `pc` and `s` to `s'` is matched, from
    every state related to `s`, by a run of `pre ++ shiftProg pre.length p ++ post`
    from `pre.length + pc` to a state related to `s'`. -/
theorem haltsC_relocated_rel {M : Machine σ} {pre p post : List RInstr} {R : σ → σ → Prop}
    (hS : ShiftSim M p pre.length R) {pc : Nat} {s s' : σ} (h : HaltsC M p pc s s') :
    ∀ t, R s t → ∃ t', HaltsC M (pre ++ shiftProg pre.length p ++ post) (pre.length + pc) t t'
      ∧ R s' t' := by
  induction h with
  | ret hret => exact fun t hR => ⟨t, .ret (getElem?_relocated pre p post hret), hR⟩
  | go hs _ ih =>
    intro t hR
    obtain ⟨t₁, hs', hR₁⟩ := step_relocated_rel (post := post) hS hs hR
    obtain ⟨t', hh, hR'⟩ := ih t₁ hR₁
    exact ⟨t', .go hs' hh, hR'⟩
  | call hcall _ _ ihc ihr =>
    intro t hR
    obtain ⟨tc, hhc, hRc⟩ := ihc _ (hS.call _ _ _ _ hcall hR)
    obtain ⟨t', hhr, hR'⟩ := ihr _ (hS.foldl retOps _ _ hRc)
    exact ⟨t', .call (getElem?_relocated pre p post hcall) hhc hhr, hR'⟩

/-- **Relocation of runs of a block without `call`.** Such a run from `pc` is a run of
    the relocated program from `pre.length + pc` with the same final state. -/
theorem haltsC_relocated (M : Machine σ) (pre p post : List RInstr)
    (hp : ∀ tg, RInstr.call tg ∉ p) {pc : Nat} {s s' : σ} (h : HaltsC M p pc s s') :
    HaltsC M (pre ++ shiftProg pre.length p ++ post) (pre.length + pc) s s' := by
  obtain ⟨t', ht, rfl⟩ :=
    haltsC_relocated_rel (post := post) (shiftSim_eq M p pre.length hp) h s rfl
  exact ht

/-- **Relocation of runs with leakage.** A `RunL` of a block without `call` from `pc` is
    a `RunL` of the relocated program from `pre.length + pc` with the same trace and
    final state. -/
theorem runL_relocated {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    (pre p post : List RInstr) (hp : ∀ tg, RInstr.call tg ∉ p) {pc : Nat} {sa : AState}
    {t : List CTLeak} {sa' : AState} (h : RunL r ok p pc sa t sa') :
    RunL r ok (pre ++ shiftProg pre.length p ++ post) (pre.length + pc) sa t sa' := by
  induction h with
  | ret h => exact .ret (getElem?_relocated pre p post h)
  | op h hok _ ih => exact .op (getElem?_relocated pre p post h) hok ih
  | @jcc pc sa cc tgt c t sa' h hc _ ih =>
    refine .jcc (getElem?_relocated pre p post h) hc ?_
    have hpc : (if sa.view.condB c then pre.length + tgt else pre.length + pc + 1)
        = pre.length + (if sa.view.condB c then tgt else pc + 1) := by
      split <;> rfl
    rw [hpc]
    exact ih
  | @stack pc sa ri ops t sa' h hops hok _ ih =>
    refine .stack (getElem?_relocated pre p post h) ?_ hok ih
    cases ri <;> simp_all [shiftInstr, RInstr.stackOps?]
  | call h => exact absurd (List.mem_of_getElem? h) (hp _)

/-! ## 6. A call to a relocated block -/

/-- **A call to a relocated block.** In `pre ++ shiftProg pre.length q ++ post`, let
    index `pc` hold a `call` to `pre.length`, the first index of the copy of a block `q`
    without `call`. If `q` runs from index `0`, on the state after the call stores its
    return index, to `sc`, and the linked program runs from `pc + 1`, on `sc` after the
    return pops that index, to `s''`, then the linked program runs from `pc` to `s''`. -/
theorem haltsC_call_relocated (M : Machine σ) (pre q post : List RInstr)
    (hq : ∀ tg, RInstr.call tg ∉ q) {pc : Nat} {s sc s'' : σ}
    (hcall : (pre ++ shiftProg pre.length q ++ post)[pc]? = some (.call pre.length))
    (hc : HaltsC M q 0 ((callOps (pc + 1)).foldl M.exec s) sc)
    (hr : HaltsC M (pre ++ shiftProg pre.length q ++ post) (pc + 1)
      (retOps.foldl M.exec sc) s'') :
    HaltsC M (pre ++ shiftProg pre.length q ++ post) pc s s'' :=
  .call hcall (haltsC_relocated M pre q post hq hc) hr

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
