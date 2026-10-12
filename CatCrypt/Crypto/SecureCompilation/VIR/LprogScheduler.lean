/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN

/-!
# `scheduleBody`: verified intra-block instruction scheduling on the linear `Lprog` body

A `Lcmd → Lcmd` transform (`Lcmd = List Linstr`) that **reorders independent
straight-line `Lopn`s** of an owned-backend linear-jasmin body to shorten the
critical data-dependence path and fill latency shadows — the classic list
scheduler, here on the **virtual (pre-RA, SSA-named) body** that
`comToLfundef` produces, where reordering freedom still exists (after `physBody`
register allocation collapses everything onto the reused `k[]` / physical-register
file the freedom is gone).

This is the `Lprog`-IR sibling of
`CatCrypt/Crypto/Optimizer/SchedulerPass.lean` (the `LowCT` scheduler) and
`CatCrypt/Crypto/Optimizer/RandomizedScheduleSearch.lean` (the x86 `JInstr`
CryptOpt loop). It follows the same discipline: every reorder move is an
**adjacent transposition of two footprint-disjoint instructions**, the only
sound move, and the pass is gated on `indep` so it never makes an unsound swap.

## What we prove

Structurally:

1. `scheduleBody_perm` — the scheduled body is a **permutation** of the input
   (no instruction is dropped, duplicated, or invented; only reordered).
   `scheduleBody_attr_perm` transports that to an arbitrary per-instruction
   attribute, so no mnemonic — and hence no rendered operand width — is
   rewritten.
2. `bubble_only_indep_swaps` — every adjacent transposition the pass performs is
   between **footprint-disjoint** `Lopn`s (`indep = true`): distinct write
   targets (no WAW), neither reads what the other writes (no RAW / WAR) —
   including the condition flags and the implicit `%rdx` read of `mulx` — and
   neither is a binding marker or a call (`indep_eq_footprint_and_hazards`).

Semantically, against both linear machines:

3. `scheduleBody_lsemStraight` — under `JasminLsem.lsemStraight` (uniform word
   width, `applyOpn`'s binary-arithmetic and single-source-move fragment) the
   scheduled body reaches the same state as the input from any start state.
4. `scheduleBody_lsemStraightN` — under `JasminLsemWidthN.lsemStraightN` (the
   width-tagged store, whose modeled arms are the two-source register binop, the
   three-source `CMOV`, and the immediate `MOV`) the same equality holds.

The two coverages differ: the uniform-width machine models a
single-register-source move that the width-tagged one has no arm for, while the
width-tagged one tracks each register's width. Both go through
`lsemStraight_swap` / `lsemStraightN_swap`, the adjacent-transposition
commutation law for an `indep` pair, lifted along `bubble` by `bubble_run`.
The `JInstr` analogue at the x86 layer is
`X86Backend.RescheduleEquivalence.jinstr_bbSwap_exec`.

The non-`Lopn` linstrs (`Lret`, `Llabel`, `Lgoto`, …) are control flow and are
**never moved**: they pin block boundaries. The scheduler reorders only inside
maximal runs of `Lopn`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. Operand footprints

An operand touches a *footprint token*: a register `reg n` touches `n`, an array
element `arr b i` touches `b ++ "#" ++ toString i` (so `k[5]` and `k[6]` are
distinct tokens, but a store and a load of `k[5]` collide). Immediates touch
nothing. This is finer than `LOperand.regName?` (which drops `arr`), which is
exactly what we need to keep a store/load of the same `k[]` slot a hazard. -/

/-- The footprint token an operand touches (none for immediates). A runtime-indexed
    `arrIdx` access touches an *unknown* element of its base array through an index
    register; the per-element token model cannot pin which element, so its array
    footprint is reported as the bare base (it does not collide with the per-element
    `b#i` tokens). Soundness for `arrIdx` does **not** rely on this token — the
    `indep` arrIdx barrier (`hasArrIdx`) keeps any `arrIdx`-bearing op immovable. -/
def opTok : LOperand → Option String
  | .reg n        => some n
  | .arr b i      => some (b ++ "#" ++ toString i)
  | .arrIdx b _ _ => some b
  | .imm _        => none

/-- The write footprint of a `linstr_r`: the tokens its destinations touch.
    Only `Lopn` writes register/array state; control flow writes nothing here. -/
def writeToks : LinstrR → List String
  | .Lopn dsts _ _ => dsts.filterMap opTok
  | _              => []

/-- The read footprint of a `linstr_r`: the tokens its sources touch. -/
def readToks : LinstrR → List String
  | .Lopn _ _ srcs => srcs.filterMap opTok
  | _              => []

/-- The store key a source operand is read at, as a total function. An immediate
    reads nothing and is given the empty string, which is also the key
    `JasminLsemWidthN.operandName` produces for every non-register operand. -/
def srcTok : LOperand → String
  | .reg n        => n
  | .arr b i      => b ++ "#" ++ toString i
  | .arrIdx b _ _ => b
  | .imm _        => ""

/-- Every store key an `Lopn` reads. The three-source `Lopn` arm of
    `JasminLsemWidthN.lsemStepN` reads its condition slot by name through
    `operandName`, which is the empty string for a non-register operand, so the
    empty string belongs to the read set of every `Lopn`. -/
def readToksSem : LinstrR → List String
  | .Lopn _ _ srcs => "" :: srcs.map srcTok
  | _              => []

/-- Whether a linstr is a reorderable straight-line op (an `Lopn`). Control flow
    is never moved. -/
def isOpn : LinstrR → Bool
  | .Lopn _ _ _ => true
  | _           => false

/-- Whether any operand is a runtime-indexed (`arrIdx`) access. -/
def opIsArrIdx : LOperand → Bool
  | .arrIdx _ _ _ => true
  | _             => false

/-- Whether a linstr contains a runtime-indexed (`arrIdx`) operand. Such an op
    touches an unknown array element through a runtime index register, which the
    per-element footprint model cannot track precisely (and, as a destination,
    also *reads* the index register the token model would mis-classify as a write).
    `indep` therefore treats any `arrIdx`-bearing op as a scheduling barrier: it is
    never swapped, so nothing is reordered across it. -/
def hasArrIdx : LinstrR → Bool
  | .Lopn dsts _ srcs => dsts.any opIsArrIdx || srcs.any opIsArrIdx
  | _                 => false

/-! ## 1b. Mnemonic keys and the cells no operand names

`JasminLprogExport` spells mnemonics in upper case, appends the width tag as a
`":64"` suffix, and carries a shift-immediate's count inside the mnemonic
(`"SHR:3:64"`). `mnemKey` reduces a mnemonic to the form the recognisers match:
the width tag stripped and the letters upper-cased.

The condition flags are a machine cell no operand names, and neither
`JasminLsem.Lstate` nor `JasminLsemWidthN.LstateN` has a slot for them, so a
reordering that clobbers a live flag is invisible to both machines. They are
modelled here as a footprint token (`flagsTok`) placed in the hazard write and
read sets of every instruction outside the flag-free list, which lets
`disjointL` reject a flag hazard by the same test it applies to registers. The
classification is a whitelist of the flag-free mnemonics (`flagFree`): a
mnemonic the exporter grows later is a flags barrier until it is listed, rather
than silently schedulable.

A rendered instruction can also touch a register no operand names — `mulx` takes
its first multiplicand from `%rdx`. `implicitReads` adds those registers, under
their physical names so they alias the explicit operands, to the read footprint.
Two further shapes are not hazards between named cells at all and are handled by
refusing to move them: a binding marker, whose value is the side effect of its
producer and which must stay adjacent to it, and a call, whose clobber set no
operand names (`isBarrierOp`). -/

/-- The mnemonic key a recogniser matches: the width tag removed and the
    remaining letters upper-cased. -/
def mnemKey (opn : String) : List Char :=
  (stripWidthTag opn).toList.map Char.toUpper

/-- Whether the mnemonic key of `opn` starts with `p`. -/
def keyStartsWith (p opn : String) : Bool :=
  p.toList.isPrefixOf (mnemKey opn)

/-- Mnemonics that leave the condition flags untouched: the moves (`MOV`,
    `MOVQ`), the loads and stores (`LOAD`, `LOADIDX`, `LOADSYM`, `STORE`,
    `STOREIDX`), `LEA`, the BMI2 `MULX` family (`MULX`, `MULXHI`, `MULXMEM`),
    the width casts (`ZEROEXT`, `TRUNC`), the vector ops (every `V`-leading
    mnemonic), and the two synthetic pins (`FRAME`, `LIVEPIN`). -/
def flagFree (opn : String) : Bool :=
  keyStartsWith "MOV" opn || keyStartsWith "LOAD" opn || keyStartsWith "STORE" opn
    || keyStartsWith "LEA" opn || keyStartsWith "MULX" opn
    || keyStartsWith "ZEROEXT" opn || keyStartsWith "TRUNC" opn
    || keyStartsWith "V" opn || keyStartsWith "FRAME" opn || keyStartsWith "LIVEPIN" opn

/-- The condition-flags cell as a footprint token. The `%` prefix is the
    exporter's synthetic-pin convention (`%livepin`), which `isHwRegName` and the
    SSA namer (`regName d = "r" ++ toString d`) never produce. -/
def flagsTok : String := "%flags"

/-- Whether an instruction touches the condition flags. Control flow carries no
    flag token: `indep` rejects it on the `isOpn` ground alone. -/
def touchesFlags : LinstrR → Bool
  | .Lopn _ opn _ => !flagFree opn
  | _             => false

/-- The flag token an instruction touches, as a footprint list. -/
def flagToks (i : LinstrR) : List String :=
  if touchesFlags i then [flagsTok] else []

/-- The hazard write footprint: the register and array tokens the instruction
    writes, together with the flags cell when it touches the flags. -/
def hazardWrites (i : LinstrR) : List String := writeToks i ++ flagToks i

/-- The registers a mnemonic reads without naming them as operands. The BMI2
    widening multiply takes its first multiplicand from `%rdx`
    (`LprogAsmPrinter`'s `MULX` / `MULXMEM` arm prints `mulx src2, dstLo, dstHi`
    and `fuseMulHiLprog` pins the multiplicand with a preceding `MOV:64 RDX,
    s1`), so `RDX` — the physical name, which aliases every explicit `%rdx`
    operand — belongs to its read footprint. -/
def implicitReads : LinstrR → List String
  | .Lopn _ opn _ => if keyStartsWith "MULX" opn then ["RDX"] else []
  | _             => []

/-- Mnemonics that are never reordered at all.

    `MULXHI`, `ADCXHI` and `ADOXHI` are *binding markers*: they name a value that
    is the side effect of the adjacent producer (`LprogAsmPrinter.isMulHiBinding`
    / `isCarryOutBinding` drop them, and `fuseMulHiLprog` / `fuseAdxChain`
    consume the producer-marker pair), so separating a marker from its producer
    loses the value rather than reordering it.

    A call clobbers every caller-saved register, which no operand of the
    `CALL:` / `CALLN:` / `CALLW:` shadow names. -/
def isBarrierOp : LinstrR → Bool
  | .Lopn _ opn _ =>
      keyStartsWith "MULXHI" opn || keyStartsWith "ADCXHI" opn
        || keyStartsWith "ADOXHI" opn || keyStartsWith "CALL" opn
  | _ => false

/-- The hazard read footprint: every store key the instruction reads, its
    implicit register reads, and the flags cell when it touches the flags. -/
def hazardReads (i : LinstrR) : List String :=
  readToksSem i ++ implicitReads i ++ flagToks i

/-! ## 2. Independence (no RAW / WAR / WAW hazard)

`indep i1 i2` holds iff both are `Lopn`s with disjoint hazard footprints:
no common write (WAW), and neither reads what the other writes (RAW / WAR).
The footprints carry the condition flags, so a pair that both touch the flags is
dependent whatever its registers do — the flags are a single cell, and the
adjacent transposition of two flag-touchers changes which of them the following
`ADCX` / `SETC` / `Lcond` sees.
Two non-`Lopn`s, or a mix with control flow, are conservatively **dependent**
(`false`) so control flow is never reordered. -/

/-- The list-disjointness test: no element of `xs` appears in `ys`. -/
def disjointL (xs ys : List String) : Bool :=
  xs.all (fun x => ys.all (fun y => x != y))

/-- `disjointL` is symmetric. -/
theorem disjointL_comm (xs ys : List String) : disjointL xs ys = disjointL ys xs := by
  simp only [disjointL]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, bne_iff_ne]
  constructor <;> intro h a ha b hb <;> exact (h b hb a ha).symm

/-- Two linstrs are independent (safe to swap when adjacent): both `Lopn`,
    distinct writes, and neither reads the other's writes, over footprints that
    carry the condition flags. -/
def indep (i1 i2 : LinstrR) : Bool :=
  isOpn i1 && isOpn i2 &&
  -- runtime-indexed accesses are scheduling barriers (footprint model can't track them)
  !hasArrIdx i1 && !hasArrIdx i2 &&
  -- binding markers and calls are never moved
  !isBarrierOp i1 && !isBarrierOp i2 &&
  -- WAW: no shared write target
  disjointL (hazardWrites i1) (hazardWrites i2) &&
  -- WAR: i2 must not read what i1 writes
  disjointL (hazardWrites i1) (hazardReads i2) &&
  -- RAW: i1 must not read what i2 writes
  disjointL (hazardWrites i2) (hazardReads i1)

/-- Independence over the register and array footprints alone, with the
    condition flags out of the model. -/
def indepFootprint (i1 i2 : LinstrR) : Bool :=
  isOpn i1 && isOpn i2 &&
  !hasArrIdx i1 && !hasArrIdx i2 &&
  disjointL (writeToks i1) (writeToks i2) &&
  disjointL (writeToks i1) (readToksSem i2) &&
  disjointL (writeToks i2) (readToksSem i1)

/-- `indep` is symmetric: hazard freedom does not depend on order. -/
theorem indep_symm (i1 i2 : LinstrR) : indep i1 i2 = indep i2 i1 := by
  simp only [indep]
  rw [disjointL_comm (hazardWrites i1) (hazardWrites i2)]
  rw [Bool.and_comm (isOpn i1) (isOpn i2)]
  ac_rfl

/-- Membership characterisation of `disjointL`. -/
theorem disjointL_iff (xs ys : List String) :
    disjointL xs ys = true ↔ ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y := by
  simp [disjointL]

/-- A `disjointL` hit gives an inequality of members. -/
theorem disjointL_ne {xs ys : List String} (h : disjointL xs ys = true) {x y : String}
    (hx : x ∈ xs) (hy : y ∈ ys) : x ≠ y := (disjointL_iff xs ys).1 h x hx y hy

/-- The footprint read set is contained in the semantic read set. -/
theorem mem_readToksSem_of_mem_readToks {i : LinstrR} {r : String} (h : r ∈ readToks i) :
    r ∈ readToksSem i := by
  cases i with
  | Lopn dsts opn srcs =>
    simp only [readToks, List.mem_filterMap] at h
    obtain ⟨o, ho, hs⟩ := h
    simp only [readToksSem, List.mem_cons, List.mem_map]
    exact Or.inr ⟨o, ho, by cases o <;> simp_all [srcTok, opTok]⟩
  | _ => simp [readToks] at h

/-- Away from the empty name the two read sets coincide. -/
theorem mem_readToks_of_mem_readToksSem {i : LinstrR} {r : String} (hr : r ≠ "")
    (h : r ∈ readToksSem i) : r ∈ readToks i := by
  cases i with
  | Lopn dsts opn srcs =>
    simp only [readToksSem, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨o, ho, hs⟩
    · exact absurd rfl hr
    · simp only [readToks, List.mem_filterMap]
      exact ⟨o, ho, by cases o <;> simp_all [srcTok, opTok]⟩
  | _ => simp [readToksSem] at h

/-- A write set that does not contain the empty name is disjoint from the
    semantic read set exactly when it is disjoint from the footprint read set:
    `indep` gates the same pairs on any body whose destinations are named
    registers. -/
theorem disjointL_readToksSem (ws : List String) (i : LinstrR) (h0 : "" ∉ ws) :
    disjointL ws (readToksSem i) = true ↔ disjointL ws (readToks i) = true := by
  simp only [disjointL_iff]
  constructor
  · intro h x hx y hy
    exact h x hx y (mem_readToksSem_of_mem_readToks hy)
  · intro h x hx y hy
    by_cases hy0 : y = ""
    · subst hy0
      intro hxe
      exact h0 (hxe ▸ hx)
    · exact h x hx y (mem_readToks_of_mem_readToksSem hy0 hy)

/-- Disjointness is antitone in both arguments. -/
theorem disjointL_mono {xs ys xs' ys' : List String} (h : disjointL xs ys = true)
    (hx : ∀ x ∈ xs', x ∈ xs) (hy : ∀ y ∈ ys', y ∈ ys) : disjointL xs' ys' = true :=
  (disjointL_iff xs' ys').2 fun x hx' y hy' => disjointL_ne h (hx x hx') (hy y hy')

/-- Disjointness splits over a concatenated left argument. -/
theorem disjointL_append_left (xs ys zs : List String) :
    disjointL (xs ++ ys) zs = (disjointL xs zs && disjointL ys zs) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, disjointL_iff, List.mem_append]
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x (Or.inl hx) y hy, fun x hx y hy => h x (Or.inr hx) y hy⟩
  · rintro ⟨h1, h2⟩ x (hx | hx) y hy
    · exact h1 x hx y hy
    · exact h2 x hx y hy

/-- Disjointness splits over a concatenated right argument. -/
theorem disjointL_append_right (xs ys zs : List String) :
    disjointL xs (ys ++ zs) = (disjointL xs ys && disjointL xs zs) := by
  rw [disjointL_comm, disjointL_append_left, disjointL_comm ys xs, disjointL_comm zs xs]

/-- A token list that misses the flags cell is disjoint from any flag
    footprint. -/
theorem disjointL_flagToks_right {xs : List String} (i : LinstrR) (h : flagsTok ∉ xs) :
    disjointL xs (flagToks i) = true := by
  refine (disjointL_iff _ _).2 fun x hx y hy => ?_
  simp only [flagToks] at hy
  split at hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    exact fun hxe => h (hxe ▸ hx)
  · simp at hy

/-- The mirrored form of `disjointL_flagToks_right`. -/
theorem disjointL_flagToks_left {xs : List String} (i : LinstrR) (h : flagsTok ∉ xs) :
    disjointL (flagToks i) xs = true := by
  rw [disjointL_comm]; exact disjointL_flagToks_right i h

/-- Two flag footprints are disjoint exactly when at most one of the
    instructions touches the flags. -/
theorem disjointL_flagToks (i1 i2 : LinstrR) :
    disjointL (flagToks i1) (flagToks i2) = !(touchesFlags i1 && touchesFlags i2) := by
  cases h1 : touchesFlags i1 <;> cases h2 : touchesFlags i2 <;>
    simp [flagToks, h1, h2, disjointL]

/-- The only member of a flag footprint is the flags token. -/
theorem mem_flagToks {i : LinstrR} {x : String} (h : x ∈ flagToks i) : x = flagsTok := by
  simp only [flagToks] at h; split at h <;> simp_all

/-- The only member of an implicit-read footprint is `RDX`. -/
theorem mem_implicitReads {j : LinstrR} {y : String} (h : y ∈ implicitReads j) : y = "RDX" := by
  cases j with
  | Lopn _ opn _ => simp only [implicitReads] at h; split at h <;> simp_all
  | _ => simp [implicitReads] at h

/-- The flags cell is not a register name, so it never meets an implicit read. -/
theorem disjointL_flagToks_implicitReads (i j : LinstrR) :
    disjointL (flagToks i) (implicitReads j) = true :=
  (disjointL_iff _ _).2 fun _ hx _ hy => by
    rw [mem_flagToks hx, mem_implicitReads hy]; decide

/-- **The pairs the hazard model rejects.** On a pair whose operands do not name
    the flags token, `indep` is footprint independence conjoined with three
    tests, so the pairs it rejects beyond `indepFootprint` are exactly: either
    instruction a barrier op, both instructions touching the flags, and one
    writing a register the other reads implicitly. -/
theorem indep_eq_footprint_and_hazards (i1 i2 : LinstrR)
    (w1 : flagsTok ∉ writeToks i1) (w2 : flagsTok ∉ writeToks i2)
    (r1 : flagsTok ∉ readToksSem i1) (r2 : flagsTok ∉ readToksSem i2) :
    indep i1 i2 =
      (indepFootprint i1 i2 && !isBarrierOp i1 && !isBarrierOp i2
        && !(touchesFlags i1 && touchesFlags i2)
        && disjointL (writeToks i1) (implicitReads i2)
        && disjointL (writeToks i2) (implicitReads i1)) := by
  simp only [indep, indepFootprint, hazardWrites, hazardReads,
    disjointL_append_left, disjointL_append_right,
    disjointL_flagToks_right i2 w1, disjointL_flagToks_right i1 w2,
    disjointL_flagToks_left i1 w2, disjointL_flagToks_left i1 r2,
    disjointL_flagToks_left i2 r1,
    disjointL_flagToks_implicitReads i1 i2, disjointL_flagToks_implicitReads i2 i1,
    disjointL_flagToks, Bool.and_comm (touchesFlags i2) (touchesFlags i1),
    Bool.and_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  tauto

/-- Component projections of `indep`. -/
theorem indep_ww {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    disjointL (writeToks i1) (writeToks i2) = true := by
  simp only [indep, Bool.and_eq_true] at h
  exact disjointL_mono (xs := hazardWrites i1) (ys := hazardWrites i2) (by tauto)
    (fun x hx => by simp [hazardWrites, hx]) (fun y hy => by simp [hazardWrites, hy])

/-- The write set of the first instruction misses the second's reads. -/
theorem indep_wr {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    disjointL (writeToks i1) (readToksSem i2) = true := by
  simp only [indep, Bool.and_eq_true] at h
  exact disjointL_mono (xs := hazardWrites i1) (ys := hazardReads i2) (by tauto)
    (fun x hx => by simp [hazardWrites, hx]) (fun y hy => by simp [hazardReads, hy])

/-- The write set of the second instruction misses the first's reads. -/
theorem indep_rw {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    disjointL (writeToks i2) (readToksSem i1) = true := by
  simp only [indep, Bool.and_eq_true] at h
  exact disjointL_mono (xs := hazardWrites i2) (ys := hazardReads i1) (by tauto)
    (fun x hx => by simp [hazardWrites, hx]) (fun y hy => by simp [hazardReads, hy])

/-- An independent pair carries no runtime-indexed operand on the left. -/
theorem indep_arrIdx_left {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    hasArrIdx i1 = false := by
  simp only [indep, Bool.and_eq_true, Bool.not_eq_true'] at h; tauto

/-- An independent pair carries no runtime-indexed operand on the right. -/
theorem indep_arrIdx_right {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    hasArrIdx i2 = false := by
  simp only [indep, Bool.and_eq_true, Bool.not_eq_true'] at h; tauto

/-- An independent pair is an `Lopn` on the left. -/
theorem indep_isOpn_left {i1 i2 : LinstrR} (h : indep i1 i2 = true) : isOpn i1 = true := by
  simp only [indep, Bool.and_eq_true] at h; tauto

/-- An independent pair is an `Lopn` on the right. -/
theorem indep_isOpn_right {i1 i2 : LinstrR} (h : indep i1 i2 = true) : isOpn i2 = true := by
  simp only [indep, Bool.and_eq_true] at h; tauto

/-- The empty name is a read key of every `Lopn`. -/
theorem empty_mem_readToksSem {i : LinstrR} (h : isOpn i = true) : "" ∈ readToksSem i := by
  cases i <;> simp_all [isOpn, readToksSem]

/-- The footprint form of `indep_wr`. -/
theorem indep_wr_readToks {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    disjointL (writeToks i1) (readToks i2) = true := by
  refine (disjointL_readToksSem _ i2 ?_).1 (indep_wr h)
  intro hc
  exact (disjointL_ne (indep_wr h) hc (empty_mem_readToksSem (indep_isOpn_right h))) rfl

/-- The footprint form of `indep_rw`. -/
theorem indep_rw_readToks {i1 i2 : LinstrR} (h : indep i1 i2 = true) :
    disjointL (writeToks i2) (readToks i1) = true := by
  refine (disjointL_readToksSem _ i1 ?_).1 (indep_rw h)
  intro hc
  exact (disjointL_ne (indep_rw h) hc (empty_mem_readToksSem (indep_isOpn_left h))) rfl

/-! ## 3. Latency priority (the ILP heuristic)

A producer-latency estimate (higher = scheduled earlier) read off the mnemonic
key (§1b): the multiply family scores `4`, the shifts and rotates `2`, every
other op `1` (`latencyPrio_binOpName`).

Correctness does not depend on these numbers — the perm / indep-swap / semantic
theorems hold for any priority function. The numbers decide only which
independent pairs the pass reorders; a body on which the priority is constant is
left untouched (`scheduleBody_id_of_uniform_prio`). Of the long-latency ops only
the `MULX` family is flag-free, so it is the one that hoists past a carry
chain. -/

/-- Producer-latency estimate of one linstr (rough Zen/Skylake ballpark): `4` for
    the multiply family (`MUL`, `MULXHI`, `IMUL`), `2` for the shifts and rotates
    (`SHL`, `SHR`, `SAR`, `ROR`, `ROL`, including the shift-immediate forms that
    carry their count after a colon), `1` for every other op and for control
    flow. -/
def latencyPrio : LinstrR → Nat
  | .Lopn _ opn _ =>
      if keyStartsWith "MUL" opn || keyStartsWith "IMUL" opn then 4
      else if keyStartsWith "SHL" opn || keyStartsWith "SHR" opn
              || keyStartsWith "SAR" opn || keyStartsWith "ROR" opn
              || keyStartsWith "ROL" opn then 2
      else 1
  | _ => 1

/-! ## 4. The bubble pass

One left-bubble pass: at each adjacent pair `(i1, i2)`, pull the
longer-latency *independent* `i2` ahead of `i1`. Every swap is gated on `indep`,
so the result is a hazard-respecting permutation (`bubble_perm`,
`bubble_indep`). -/

/-- One left-bubble pass over the body. -/
def bubble : List Linstr → List Linstr
  | []  => []
  | [i] => [i]
  | i1 :: i2 :: rest =>
      if indep i1.li_i i2.li_i && (latencyPrio i1.li_i < latencyPrio i2.li_i) then
        i2 :: bubble (i1 :: rest)
      else
        i1 :: bubble (i2 :: rest)

/-- One bubble pass is a permutation of its input. -/
theorem bubble_perm : ∀ (b : List Linstr), (bubble b).Perm b := by
  intro b
  induction b using bubble.induct with
  | case1 => simp [bubble]
  | case2 i => simp [bubble]
  | case3 i1 i2 rest hcond ih =>
      simp only [bubble, if_pos hcond]
      -- bubble (i1::i2::rest) = i2 :: bubble (i1::rest)
      refine (List.Perm.cons i2 ih).trans ?_
      exact List.Perm.swap i1 i2 rest
  | case4 i1 i2 rest hcond ih =>
      simp only [bubble, if_neg hcond]
      exact List.Perm.cons i1 ih

/-- Iterate `bubble` `k` times. -/
def bubbleN : Nat → List Linstr → List Linstr
  | 0,     b => b
  | k + 1, b => bubbleN k (bubble b)

/-- `bubbleN` is a permutation of its input. -/
theorem bubbleN_perm : ∀ (k : Nat) (b : List Linstr), (bubbleN k b).Perm b := by
  intro k
  induction k with
  | zero => intro b; simp [bubbleN]
  | succ k ih => intro b; simp only [bubbleN]; exact (ih (bubble b)).trans (bubble_perm b)

/-! ### Early-exit iteration

A `bubble` pass that performs no swap returns its input, and every further pass
is then the identity. `bubbleNEarly` stops as soon as a pass would swap nothing,
detected by `noSwap` through the same guard `bubble` uses, and computes the same
body as `bubbleN` (`bubbleNEarly_eq_bubbleN`) with the trailing no-op passes
skipped. -/

/-- Whether one `bubble` pass would perform no swap: the swap guard fails at every
    adjacent pair. When this holds `bubble` is the identity (`noSwap_bubble_id`). -/
def noSwap : List Linstr → Bool
  | []  => true
  | [_] => true
  | i1 :: i2 :: rest =>
      !(indep i1.li_i i2.li_i && (latencyPrio i1.li_i < latencyPrio i2.li_i))
        && noSwap (i2 :: rest)

/-- A pass that swaps nothing leaves the body unchanged. -/
theorem noSwap_bubble_id : ∀ (b : List Linstr), noSwap b = true → bubble b = b := by
  intro b
  induction b using bubble.induct with
  | case1 => intro _; simp [bubble]
  | case2 i => intro _; simp [bubble]
  | case3 i1 i2 rest hcond _ =>
      intro hns
      simp [noSwap, hcond] at hns
  | case4 i1 i2 rest hcond ih =>
      intro hns
      simp only [bubble, if_neg hcond]
      have hns' : noSwap (i2 :: rest) = true := by
        simp only [noSwap] at hns
        cases hg : (indep i1.li_i i2.li_i && (latencyPrio i1.li_i < latencyPrio i2.li_i)) with
        | true => exact absurd hg hcond
        | false => rw [hg] at hns; simpa using hns
      rw [ih hns']

/-- Once one pass is the identity, every iterated pass is too. -/
theorem bubbleN_of_bubble_id {b : List Linstr} (h : bubble b = b) :
    ∀ k, bubbleN k b = b := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [bubbleN, h]; exact ih

/-- Iterate `bubble`, stopping as soon as a pass would swap nothing. -/
def bubbleNEarly : Nat → List Linstr → List Linstr
  | 0,     b => b
  | k + 1, b => if noSwap b then b else bubbleNEarly k (bubble b)

/-- The early-exit iteration computes the same body as the fixed-count iteration:
    the skipped passes are all no-ops. -/
theorem bubbleNEarly_eq_bubbleN : ∀ (k : Nat) (b : List Linstr),
    bubbleNEarly k b = bubbleN k b := by
  intro k
  induction k with
  | zero => intro b; rfl
  | succ k ih =>
    intro b
    simp only [bubbleNEarly, bubbleN]
    by_cases h : noSwap b = true
    · rw [if_pos h]
      have hf : bubble b = b := noSwap_bubble_id b h
      rw [hf]
      exact (bubbleN_of_bubble_id hf k).symm
    · rw [if_neg h]
      exact ih (bubble b)

/-! ## 5. The scheduler -/

/-- **The Lprog body scheduler.** Reorder a straight-line body for ILP by
    latency-priority bubble passes, iterated until a pass makes no swap and
    bounded by `length`-many passes. Every move is an adjacent footprint-disjoint
    swap, so the result is a hazard-respecting permutation (`scheduleBody_perm`). -/
def scheduleBody (b : List Linstr) : List Linstr :=
  bubbleNEarly b.length b

/-- The scheduler is the fixed-count bubble iteration: the early exit only skips
    no-op passes. Consumers reason through this equality, so their statements
    stay phrased over `scheduleBody`. -/
theorem scheduleBody_eq_bubbleN (b : List Linstr) :
    scheduleBody b = bubbleN b.length b :=
  bubbleNEarly_eq_bubbleN b.length b

/-- **Permutation preservation.** The scheduled body is a permutation of the
    input: no instruction is dropped, duplicated, or invented — only reordered. -/
theorem scheduleBody_perm (b : List Linstr) : (scheduleBody b).Perm b := by
  rw [scheduleBody_eq_bubbleN]; exact bubbleN_perm b.length b

/-- The scheduled body has the same length (immediate corollary — the rendered
    `.s` has exactly as many instructions, the emit just reorders them). -/
theorem scheduleBody_length (b : List Linstr) : (scheduleBody b).length = b.length :=
  (scheduleBody_perm b).length_eq

/-- The scheduled body has the same instruction multiset
    (`li_i` projections), so the emitted op counts are identical. -/
theorem scheduleBody_instr_multiset (b : List Linstr) :
    ((scheduleBody b).map Linstr.li_i).Perm (b.map Linstr.li_i) :=
  (scheduleBody_perm b).map Linstr.li_i

/-! ## 6. Every swap the pass makes is footprint-disjoint

`bubble` only ever transposes an adjacent pair when `indep i1.li_i i2.li_i =
true`. We expose that gate as a theorem: whenever the head pair is swapped, the
pair was independent. This is the soundness witness — the pass cannot reorder two
hazardous instructions. -/

/-- **Soundness gate.** For *every* adjacent transposition the schedule performs,
    the two instructions are footprint-disjoint (`indep = true`): distinct
    writes, and neither reads the other's writes. This is the structural
    soundness witness for the scheduler: the only branch of `bubble` that
    changes order is guarded by `indep`, so the pass can never reorder two
    hazardous instructions.

    `indep = true` is the syntactic footprint-disjointness witness; §9 and §10
    turn it into the semantic commutation laws `lsemStraight_swap` and
    `lsemStraightN_swap`. The same discipline over the `BBStmt`/`RustState` IR is
    `Optimizer.SchedulerPass.scheduleBlock_denote_eq`. -/
theorem bubble_only_indep_swaps (i1 i2 : Linstr) (rest : List Linstr) :
    (∃ tail, bubble (i1 :: i2 :: rest) = i2 :: tail ∧ i1.li_i ≠ i2.li_i) →
    indep i1.li_i i2.li_i = true := by
  rintro ⟨tail, hb, hne⟩
  by_cases hcond : indep i1.li_i i2.li_i && (latencyPrio i1.li_i < latencyPrio i2.li_i)
  · simp only [Bool.and_eq_true] at hcond; exact hcond.1
  · -- non-swap branch: bubble emits i1 first, contradicting the head = i2 hypo
    -- unless i1 = i2 at the linstr_r level (excluded by hne).
    exfalso
    simp only [bubble, if_neg hcond] at hb
    -- hb : i1 :: bubble (i2 :: rest) = i2 :: tail  ⟹  i1 = i2
    have : i1 = i2 := (List.cons.injEq _ _ _ _).mp hb |>.1
    exact hne (this ▸ rfl)

/-! ## 6b. Tail-preserving schedule (ABI output-staging barrier)

`Com.toLprogPhysAbi` stores the **last `n` bindings'** results to the output
pointer (`firstOutIdx = numBindings - n` in `physBodyWithStores`). So the
scheduler must not disturb the output-staging tail: the last `keepTail`
instructions stay fixed, and only the prefix is reordered. `scheduleBodyTail`
schedules `body.take (len - keepTail)` and re-appends `body.drop (len -
keepTail)` verbatim. -/

/-- Schedule the body but keep the last `keepTail` instructions in place (the
    ABI output-staging barrier). -/
def scheduleBodyTail (keepTail : Nat) (b : List Linstr) : List Linstr :=
  let cut := b.length - keepTail
  scheduleBody (b.take cut) ++ b.drop cut

/-- The tail-preserving schedule is a permutation of the input. -/
theorem scheduleBodyTail_perm (keepTail : Nat) (b : List Linstr) :
    (scheduleBodyTail keepTail b).Perm b := by
  simp only [scheduleBodyTail]
  refine (List.Perm.append_right _ (scheduleBody_perm (b.take _))).trans ?_
  rw [List.take_append_drop]

/-- The tail-preserving schedule preserves length. -/
theorem scheduleBodyTail_length (keepTail : Nat) (b : List Linstr) :
    (scheduleBodyTail keepTail b).length = b.length :=
  (scheduleBodyTail_perm keepTail b).length_eq

/-- The last `keepTail` instructions are untouched (the output-staging tail is a
    verbatim suffix of the scheduled body). -/
theorem scheduleBodyTail_drop (keepTail : Nat) (b : List Linstr) :
    (scheduleBodyTail keepTail b).drop (b.length - keepTail) = b.drop (b.length - keepTail) := by
  simp only [scheduleBodyTail]
  have hlen : (scheduleBody (b.take (b.length - keepTail))).length = b.length - keepTail := by
    rw [scheduleBody_length, List.length_take]; omega
  rw [List.drop_append_of_le_length (Nat.le_of_eq hlen.symm),
    List.drop_eq_nil_of_le (Nat.le_of_eq hlen), List.nil_append]

/-! ## 7. Applying the schedule to an `Lprog`

Schedule the body of every function in an `Lprog`. The wrapper preserves all
other `Lfundef` / `Lprog` fields (args, types, result, frame) — only `lfd_body`
is reordered. -/

/-- Schedule one function's body, leaving every other field intact. -/
def scheduleLfundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := scheduleBody f.lfd_body }

/-- Schedule every function body in an `Lprog`. -/
def scheduleLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun (n, f) => (n, scheduleLfundef f)) }

/-- Scheduling preserves the per-function body length (instruction count). -/
theorem scheduleLfundef_body_length (f : Lfundef) :
    (scheduleLfundef f).lfd_body.length = f.lfd_body.length := by
  simp only [scheduleLfundef]; exact scheduleBody_length f.lfd_body

/-- Scheduling preserves the function signature (args / types / result). -/
theorem scheduleLfundef_sig (f : Lfundef) :
    (scheduleLfundef f).lfd_arg = f.lfd_arg ∧
    (scheduleLfundef f).lfd_tyin = f.lfd_tyin ∧
    (scheduleLfundef f).lfd_res = f.lfd_res ∧
    (scheduleLfundef f).lfd_tyout = f.lfd_tyout := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## 8. Scheduled ABI emit (the wired entry point)

`comToLfundefPhysAbiScheduled` mirrors `JasminLprogExport.comToLfundefPhysAbi`
but schedules the **virtual (pre-RA) body** with `scheduleBodyTail nOut` before
register allocation. The last `nOut` bindings (the output-staging moves) are kept
in place so the ABI epilogue still stores the right bindings
(`physBodyWithStores`'s `firstOutIdx = numBindings - nOut`). RA, two-address
lowering, prologue/epilogue, and inline stores then run exactly as in the
unscheduled path — over the *scheduled* body, so the linear scan adapts to the
new order. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The ABI-wrapped physical `Lfundef` for a `Com`, with the virtual body
    ILP-scheduled before register allocation, keeping the last `nOut` virtual-body
    **list elements** fixed. For an ABI emit those must cover the output-staging
    bindings the epilogue stores (`firstOutIdx = numBindings - storeMap.length`)
    plus the trailing `Lret` `comToBody` appends — e.g. `nOut = 25 + 1` for the
    25-lane Keccak/SHA-3 output. A drop-in for `comToLfundefPhysAbi`. -/
def comToLfundefPhysAbiScheduled {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (nOut : Nat)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    Lfundef :=
  let virt0 := comToLfundef com immSlotMap
  -- Schedule the virtual body for ILP, keeping the output-staging tail fixed.
  let scheduledBody := scheduleBodyTail nOut virt0.lfd_body
  let virt := { virt0 with lfd_body := scheduledBody }
  let tr := bodyTrace virt.lfd_body
  let tbl := physTable tr
  let prologue := buildPrologue virt tbl inLoadMap
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  let bodyWithInlineStores := physBodyWithStores shiftImm' virt.lfd_body
    inLoadMap reloadScratch2 outStoreMap reloadScratch2
  let bodyWithRestore := insertEpilogue bodyWithInlineStores calleeSaveRestoreEpilogue
  { virt with
    lfd_body := prologue ++ bodyWithRestore
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := [] }

/-- Export a `Com` to a 2-pointer-ABI physical `Lprog` with the virtual body
    ILP-scheduled before RA. A drop-in for `Com.toLprogPhysAbi`. -/
def Com.toLprogPhysAbiScheduled {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (nOut : Nat)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, comToLfundefPhysAbiScheduled com nOut shiftImm immSlotMap inLoadMap
                 outStoreMap abiArgs abiTyin)] }

/-! ## 9. Adjacent-swap commutation at uniform word width

`JasminLsem.lsemStep` writes at most the single register `writeToks` names and
reads its sources through `evalOperand`, which consults `lvm` at a `.reg`
operand's name and `lmem` at an array cell.  A step therefore splits into an
optional register write (`stepEffU`) applied to the incoming state
(`applyEffU`), and writes to distinct registers commute.  Memory is read but
never written by this machine, so an array source is invariant under any write. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-- Write a word-addressed memory cell `(base, off)`, leaving the registers and
    the pc unchanged. The `lmem`-update dual of `Lstate.setReg`: the runtime
    store `STOREIDX` performs, addressed by base name and byte offset. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem.Lstate.setMem {w : Nat}
    (s : Lstate w) (base : String) (off : Int) (v : BitVec w) : Lstate w :=
  { s with lmem := fun b o => if b = base then (if o = off then v else s.lmem b o) else s.lmem b o }

@[simp] theorem Lstate.lvm_setMem {w : Nat} (s : Lstate w) (base : String) (off : Int)
    (v : BitVec w) : (s.setMem base off v).lvm = s.lvm := rfl

@[simp] theorem Lstate.lpc_setMem {w : Nat} (s : Lstate w) (base : String) (off : Int)
    (v : BitVec w) : (s.setMem base off v).lpc = s.lpc := rfl

/-- The store effect of one modeled uniform-width step: an optional register
    write and an optional word-addressed memory write, each applied before the pc
    advance. The register component is the single-destination `Lopn` write; the
    memory component is the runtime-indexed store (the `STOREIDX` cell), `none`
    for every op that touches no memory. The two components address disjoint state
    (`lvm` versus `lmem`), which is why a register write and a memory write always
    commute. -/
structure OpEffU (w : Nat) where
  /-- The register write, `none` when the step writes no register. -/
  reg : Option (String × BitVec w) := none
  /-- The memory write `(base, offset, value)`, `none` when the step writes no
      memory cell. -/
  mem : Option (String × Int × BitVec w) := none

/-- The register write a uniform-width step performs: `none` for a step the
    machine does not model, the default (both components `none`) for a step that
    only advances the pc, and a register-component write for a modeled `Lopn`.
    The memory component is `none` on every currently modeled op. -/
def stepEffU {w : Nat} (i : LinstrR) (s : Lstate w) : Option (OpEffU w) :=
  match i with
  | .Lopn [.reg dst] opn (.arrIdx base idx scale :: rest) =>
      let off : Int := Int.ofNat (scale * (s.lvm idx).toNat)
      if opn = "LOADIDX" then some { reg := some (dst, s.lmem base off) }
      else if opn = "STOREIDX" then
        match rest with
        | [val] => some { mem := some (base, off, evalOperand s val) }
        | _ => none
      else
        match applyOpn (stripWidthTag opn)
            ((LOperand.arrIdx base idx scale :: rest).map (evalOperand s)) with
        | some v => some { reg := some (dst, v) }
        | none => none
  | .Lopn [.reg dst] opn srcs =>
      match applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
      | some v => some { reg := some (dst, v) }
      | none => none
  | .Lopn _ _ _ => none
  | .Lalign => some {}
  | .Llabel _ _ => some {}
  | .Lgoto _ => none
  | .Lcond _ _ => none
  | .Ligoto _ => none
  | .Lcall _ _ => none
  | .Lret => none
  | .LstoreLabel _ _ => none
  | .Lsyscall _ => none

/-- Apply a uniform-width step's write — its register component then its memory
    component — and advance the pc. -/
def applyEffU {w : Nat} (s : Lstate w) (e : OpEffU w) : Lstate w :=
  let s1 := match e.reg with | none => s | some (d, v) => s.setReg d v
  let s2 := match e.mem with | none => s1 | some (b, o, v) => s1.setMem b o v
  s2.nextPc

/-- The register a step's write targets, `none` when it writes no register. -/
def effNameU {w : Nat} (e : OpEffU w) : Option String := e.reg.map Prod.fst

/-- On a single-register destination whose sources carry no runtime index, the
    store effect reduces to the plain register-write arm: the runtime-store arm
    (`LOADIDX` / `STOREIDX`) is guarded by a runtime-indexed source, so it is not
    taken here. -/
theorem stepEffU_reg_of_noArrIdx {w : Nat} (dst opn : String) (srcs : List LOperand)
    (s : Lstate w) (hsrc : ∀ o ∈ srcs, opIsArrIdx o = false) :
    stepEffU (LinstrR.Lopn [.reg dst] opn srcs) s =
      (match applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
       | some v => some { reg := some (dst, v) }
       | none => none) := by
  cases srcs with
  | nil => rfl
  | cons o rest =>
    cases o with
    | arrIdx b idx sc => exact absurd (hsrc (.arrIdx b idx sc) (by simp)) (by simp [opIsArrIdx])
    | _ => rfl

/-- A step with no runtime-indexed source writes no memory cell: the memory
    component of `stepEffU` is `none` there. The runtime store (`STOREIDX`) is
    the only op making this component `some`, and it carries a runtime-indexed
    source, so `hasArrIdx i = false` excludes it. -/
theorem stepEffU_mem_none {w : Nat} (i : LinstrR) (s : Lstate w) {e : OpEffU w}
    (hidx : hasArrIdx i = false) (h : stepEffU i s = some e) : e.mem = none := by
  cases i with
  | Lopn dsts opn srcs =>
    cases dsts with
    | nil => exact absurd h (by simp [stepEffU])
    | cons hd tl =>
      cases tl with
      | cons _ _ => exact absurd h (by simp [stepEffU])
      | nil =>
        cases hd with
        | reg dst =>
          have hsrc : ∀ o ∈ srcs, opIsArrIdx o = false := by
            simp only [hasArrIdx, Bool.or_eq_false_iff, List.any_eq_false] at hidx
            exact fun o ho => by simpa using hidx.2 o ho
          rw [stepEffU_reg_of_noArrIdx dst opn srcs s hsrc] at h
          cases hop : applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
          | none => rw [hop] at h; simp at h
          | some v => rw [hop] at h; obtain rfl := Option.some.inj h; rfl
        | arr a b => exact absurd h (by simp [stepEffU])
        | imm n => exact absurd h (by simp [stepEffU])
        | arrIdx a b c => exact absurd h (by simp [stepEffU])
  | Lalign => obtain rfl := Option.some.inj h; rfl
  | Llabel a b => obtain rfl := Option.some.inj h; rfl
  | _ => exact absurd h (by simp [stepEffU])

/-- `lsemStep` is its store effect applied to the incoming state. -/
theorem lsemStep_eq_applyEffU {w : Nat} (i : LinstrR) (s : Lstate w) :
    lsemStep i s = (stepEffU i s).map (applyEffU s) := by
  cases i with
  | Lopn dsts opn srcs =>
    match dsts with
    | [] => rfl
    | [.arr _ _] => rfl
    | [.imm _] => rfl
    | [.arrIdx _ _ _] => rfl
    | x :: _ :: _ => cases x <;> rfl
    | [.reg dst] =>
      cases srcs with
      | nil =>
        simp only [lsemStep, stepEffU]
        cases applyOpn (stripWidthTag opn) (List.map (evalOperand s) []) <;> rfl
      | cons hd tl =>
        cases hd with
        | reg r =>
          simp only [lsemStep, stepEffU]
          cases applyOpn (stripWidthTag opn) (List.map (evalOperand s) (.reg r :: tl)) <;> rfl
        | imm n =>
          simp only [lsemStep, stepEffU]
          cases applyOpn (stripWidthTag opn) (List.map (evalOperand s) (.imm n :: tl)) <;> rfl
        | arr a b =>
          simp only [lsemStep, stepEffU]
          cases applyOpn (stripWidthTag opn) (List.map (evalOperand s) (.arr a b :: tl)) <;> rfl
        | arrIdx base idx scale =>
          by_cases hL : opn = "LOADIDX"
          · subst hL
            simp only [lsemStep, stepEffU]
            rfl
          · by_cases hS : opn = "STOREIDX"
            · subst hS
              cases tl with
              | nil => simp only [lsemStep, stepEffU]; rfl
              | cons val rest =>
                cases rest with
                | nil =>
                  simp only [lsemStep, stepEffU]
                  rfl
                | cons _ _ => simp only [lsemStep, stepEffU]; rfl
            · simp only [lsemStep, stepEffU, if_neg hL, if_neg hS]
              cases applyOpn (stripWidthTag opn)
                  (List.map (evalOperand s) (.arrIdx base idx scale :: tl)) <;> rfl
  | _ => rfl

/-- A non-runtime-indexed operand evaluates the same in two states that agree on
    memory and on the register the operand's token names. -/
theorem evalOperand_congrU {w : Nat} {s1 s2 : Lstate w} (o : LOperand)
    (hmem : s1.lmem = s2.lmem) (hidx : opIsArrIdx o = false)
    (hreg : ∀ r, opTok o = some r → s1.lvm r = s2.lvm r) :
    evalOperand s1 o = evalOperand s2 o := by
  cases o <;> simp_all [evalOperand, opTok, opIsArrIdx]

/-- A step's register write depends on the state only through memory and the
    registers its read footprint names. -/
theorem stepEffU_congr {w : Nat} (i : LinstrR) (s1 s2 : Lstate w)
    (hmem : s1.lmem = s2.lmem) (hidx : hasArrIdx i = false)
    (hreg : ∀ r ∈ readToks i, s1.lvm r = s2.lvm r) :
    stepEffU i s1 = stepEffU i s2 := by
  cases i with
  | Lopn dsts opn srcs =>
    cases dsts with
    | nil => rfl
    | cons hd tl =>
      cases tl with
      | cons _ _ => cases hd <;> rfl
      | nil =>
        cases hd with
        | reg dst =>
          have hsrc : ∀ o ∈ srcs, opIsArrIdx o = false := by
            simp only [hasArrIdx, Bool.or_eq_false_iff, List.any_eq_false] at hidx
            exact fun o ho => by simpa using hidx.2 o ho
          have hev : ∀ o ∈ srcs, evalOperand s1 o = evalOperand s2 o := by
            intro o ho
            refine evalOperand_congrU o hmem (hsrc o ho) ?_
            intro r hr
            exact hreg r (by simp only [readToks, List.mem_filterMap]; exact ⟨o, ho, hr⟩)
          rw [stepEffU_reg_of_noArrIdx dst opn srcs s1 hsrc,
              stepEffU_reg_of_noArrIdx dst opn srcs s2 hsrc, List.map_congr_left hev]
        | arr a b => rfl
        | imm n => rfl
        | arrIdx a b c => rfl
  | _ => rfl

/-- The write footprint of a step, named through the register its store effect
    targets: a step whose effect writes register `d` is a single-register
    destination `Lopn` on `d`, so its write footprint is `[d]`. -/
theorem stepEffU_writeToks_of_effName {w : Nat} {i : LinstrR} {s : Lstate w}
    {e : OpEffU w} {d : String}
    (hidx : hasArrIdx i = false)
    (h : stepEffU i s = some e) (hd : effNameU e = some d) : writeToks i = [d] := by
  cases i with
  | Lopn dsts opn srcs =>
    cases dsts with
    | nil => exact absurd h (by simp [stepEffU])
    | cons hd' tl =>
      cases tl with
      | cons _ _ => exact absurd h (by simp [stepEffU])
      | nil =>
        cases hd' with
        | reg dst =>
          have hsrc : ∀ o ∈ srcs, opIsArrIdx o = false := by
            simp only [hasArrIdx, Bool.or_eq_false_iff, List.any_eq_false] at hidx
            exact fun o ho => by simpa using hidx.2 o ho
          rw [stepEffU_reg_of_noArrIdx dst opn srcs s hsrc] at h
          cases hop : applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
          | none => rw [hop] at h; simp at h
          | some v' =>
            rw [hop] at h
            obtain rfl := Option.some.inj h
            simp only [effNameU, Option.map_some] at hd
            obtain rfl := Option.some.inj hd
            simp [writeToks, opTok]
        | arr a b => exact absurd h (by simp [stepEffU])
        | imm n => exact absurd h (by simp [stepEffU])
        | arrIdx a b c => exact absurd h (by simp [stepEffU])
  | Lalign => rw [show stepEffU .Lalign s = some {} from rfl] at h
              obtain rfl := Option.some.inj h; simp [effNameU] at hd
  | Llabel a b => rw [show stepEffU (.Llabel a b) s = some {} from rfl] at h
                  obtain rfl := Option.some.inj h; simp [effNameU] at hd
  | _ => exact absurd h (by simp [stepEffU])

/-- A step whose memory component is `none` leaves memory unchanged. Every
    currently modeled step has `mem = none` (`stepEffU_mem_none`). -/
theorem applyEffU_lmem {w : Nat} (s : Lstate w) (e : OpEffU w) (hmem : e.mem = none) :
    (applyEffU s e).lmem = s.lmem := by
  simp only [applyEffU, hmem]
  cases e.reg with
  | none => rfl
  | some p => obtain ⟨d, v⟩ := p; rfl

/-- A step leaves every register but its (register-effect) target unchanged; the
    memory component of the effect never touches the register map. -/
theorem applyEffU_lvm_of_ne {w : Nat} (s : Lstate w) (e : OpEffU w)
    (r : String) (h : effNameU e ≠ some r) : (applyEffU s e).lvm r = s.lvm r := by
  have key : ∀ t : Lstate w,
      (match e.mem with | none => t | some (b, o, v) => t.setMem b o v).lvm r = t.lvm r := by
    intro t; cases e.mem with
    | none => rfl
    | some p => obtain ⟨b, o, v⟩ := p; rfl
  simp only [applyEffU, Lstate.lvm_nextPc, key]
  cases hreg : e.reg with
  | none => rfl
  | some p =>
    obtain ⟨d, v⟩ := p
    have h' : ¬ (r = d) := fun e' => h (by simp [effNameU, hreg, e'])
    simp [Lstate.setReg, h']

/-- Register writes to distinct registers commute, on effects that write no
    memory. This is the case the scheduler needs: it never reorders a
    memory-touching op (`indep` treats any runtime-indexed operand as a barrier),
    so both effects in an independent swap have `mem = none`. -/
theorem applyEffU_comm {w : Nat} (s : Lstate w) (e1 e2 : OpEffU w)
    (hm1 : e1.mem = none) (hm2 : e2.mem = none)
    (h : ∀ d1 ∈ effNameU e1, ∀ d2 ∈ effNameU e2, d1 ≠ d2) :
    applyEffU (applyEffU s e1) e2 = applyEffU (applyEffU s e2) e1 := by
  simp only [applyEffU, hm1, hm2]
  cases hr1 : e1.reg with
  | none => cases hr2 : e2.reg with
    | none => rfl
    | some p2 => obtain ⟨d2, v2⟩ := p2; rfl
  | some p1 =>
    obtain ⟨d1, v1⟩ := p1
    cases hr2 : e2.reg with
    | none => rfl
    | some p2 =>
      obtain ⟨d2, v2⟩ := p2
      have hne : d1 ≠ d2 :=
        h d1 (by simp [effNameU, hr1]) d2 (by simp [effNameU, hr2])
      obtain ⟨m, mem, p⟩ := s
      simp only [Lstate.setReg, Lstate.nextPc]
      congr 1
      funext r
      by_cases g1 : r = d1 <;> by_cases g2 : r = d2 <;> simp_all

/-- A register write and a memory write commute: they address disjoint state
    (`lvm` versus `lmem`), so the order never matters. The register-versus-memory
    half of the first-class store algebra. -/
theorem Lstate.setReg_setMem_comm {w : Nat} (s : Lstate w) (d : String) (v : BitVec w)
    (b : String) (o : Int) (u : BitVec w) :
    (s.setReg d v).setMem b o u = (s.setMem b o u).setReg d v := by
  cases s; rfl

/-- Memory writes to distinct cells commute. The memory-versus-memory half of the
    first-class store algebra, and the hazard the scheduler's `indep` already
    tracks: two `STOREIDX`s at different `(base, offset)` cells may be reordered. -/
theorem Lstate.setMem_comm {w : Nat} (s : Lstate w) (b1 : String) (o1 : Int) (v1 : BitVec w)
    (b2 : String) (o2 : Int) (v2 : BitVec w) (h : (b1, o1) ≠ (b2, o2)) :
    (s.setMem b1 o1 v1).setMem b2 o2 v2 = (s.setMem b2 o2 v2).setMem b1 o1 v1 := by
  cases s
  simp only [Lstate.setMem, Lstate.mk.injEq, true_and, and_true]
  funext b o
  by_cases hb1 : b = b1 <;> by_cases hb2 : b = b2 <;>
    by_cases ho1 : o = o1 <;> by_cases ho2 : o = o2 <;>
    simp_all [Prod.ext_iff]

/-- An instruction whose read footprint misses another's write target computes
    the same write before and after that other step. -/
theorem stepEffU_after {w : Nat} (i j : LinstrR) (s : Lstate w)
    (e : OpEffU w) (hj : stepEffU j s = some e)
    (hidx : hasArrIdx i = false) (hidxj : hasArrIdx j = false)
    (hd : disjointL (writeToks j) (readToks i) = true) :
    stepEffU i (applyEffU s e) = stepEffU i s := by
  refine stepEffU_congr i _ s (applyEffU_lmem s e (stepEffU_mem_none j s hidxj hj)) hidx ?_
  intro r hr
  refine applyEffU_lvm_of_ne s e r ?_
  intro hcon
  have hw : writeToks j = [r] := stepEffU_writeToks_of_effName hidxj hj hcon
  exact (disjointL_ne hd (by rw [hw]; simp) hr) rfl

/-- **Adjacent-transposition commutation at uniform word width.**  Swapping an
    independent adjacent pair leaves `lsemStraight` unchanged. -/
theorem lsemStraight_swap {w : Nat} (i1 i2 : LinstrR) (rest : List LinstrR) (s : Lstate w)
    (h : indep i1 i2 = true) :
    lsemStraight (i1 :: i2 :: rest) s = lsemStraight (i2 :: i1 :: rest) s := by
  have hww := indep_ww h
  have hwr := indep_wr_readToks h
  have hrw := indep_rw_readToks h
  have hx1 := indep_arrIdx_left h
  have hx2 := indep_arrIdx_right h
  rcases h1 : stepEffU i1 s with _ | e1 <;> rcases h2 : stepEffU i2 s with _ | e2
  · simp [lsemStraight, lsemStep_eq_applyEffU, h1, h2]
  · simp [lsemStraight, lsemStep_eq_applyEffU, h1, h2,
      stepEffU_after i1 i2 s e2 h2 hx1 hx2 hrw]
  · simp [lsemStraight, lsemStep_eq_applyEffU, h1, h2,
      stepEffU_after i2 i1 s e1 h1 hx2 hx1 hwr]
  · have hne : ∀ d1 ∈ effNameU e1, ∀ d2 ∈ effNameU e2, d1 ≠ d2 := by
      intro d1 hd1 d2 hd2
      have w1 : writeToks i1 = [d1] := stepEffU_writeToks_of_effName hx1 h1 hd1
      have w2 : writeToks i2 = [d2] := stepEffU_writeToks_of_effName hx2 h2 hd2
      exact disjointL_ne hww (by rw [w1]; simp) (by rw [w2]; simp)
    have hm1 := stepEffU_mem_none i1 s hx1 h1
    have hm2 := stepEffU_mem_none i2 s hx2 h2
    simp only [lsemStraight, lsemStep_eq_applyEffU, h1, h2, Option.map_some,
      stepEffU_after i2 i1 s e1 h1 hx2 hx1 hwr,
      stepEffU_after i1 i2 s e2 h2 hx1 hx2 hrw]
    rw [applyEffU_comm s e1 e2 hm1 hm2 hne]

/-! ## 10. Adjacent-swap commutation at width-tagged store

`JasminLsemWidthN.lsemStepN` models the two-source register binop, the
three-source `CMOV`, the immediate `MOV`, and the one-source `NEG` and
register `MOV`; each writes one register, at the width its data source carries.
The same decomposition into an optional write and an application gives the
commutation law over the width-tagged store. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN

/-- A width-tagged read at a register the two states agree on. -/
theorem getW_congr {s1 s2 : LstateN} {r : String} (h : s1.lvm r = s2.lvm r) (w : Nat) :
    s1.getW r w = s2.getW r w := by
  unfold LstateN.getW; rw [h]

/-- `readReg` agrees on two states that agree at the operand's read key. -/
theorem readReg_congr {s1 s2 : LstateN} (o : LOperand)
    (h : s1.lvm (srcTok o) = s2.lvm (srcTok o)) : readReg s1 o = readReg s2 o := by
  cases o with
  | reg n => simp only [srcTok] at h; simp only [readReg, h]
  | _ => rfl

/-- `evalOperandN` agrees on two states that agree at the operand's read key. -/
theorem evalOperandN_congr {s1 s2 : LstateN} (o : LOperand)
    (h : s1.lvm (srcTok o) = s2.lvm (srcTok o)) (w : Nat) :
    evalOperandN s1 w o = evalOperandN s2 w o := by
  cases o with
  | reg n => simp only [srcTok] at h; exact getW_congr h w
  | _ => rfl

/-- The condition slot of a three-source `Lopn` is read at the operand's register
    name, or at the empty string when the operand is not a register. -/
theorem getW_operandName_congr {s1 s2 : LstateN} (o : LOperand)
    (h : s1.lvm (srcTok o) = s2.lvm (srcTok o)) (h0 : s1.lvm "" = s2.lvm "") (w : Nat) :
    s1.getW (operandName o) w = s2.getW (operandName o) w := by
  cases o with
  | reg n => simp only [srcTok] at h; exact getW_congr h w
  | _ => exact getW_congr h0 w

/-- A register name paired with the width-tagged word written to it. -/
abbrev Cell := String × Σ w, BitVec w

/-- The write a width-tagged step performs: `none` for a step the machine does
    not model, `some none` for a step that only advances the pc, and
    `some (some (d, c))` for a step that writes the cell `c` to register `d`. -/
def stepEff (i : LinstrR) (s : LstateN) : Option (Option Cell) :=
  match i with
  | .Lopn [.reg dst] opn [c, a, b] =>
      if stripWidthTag opn = "CMOV" then
        match s.getW (operandName c) 1, readReg s a with
        | some cond, some ⟨wa, va⟩ =>
            match evalOperandN s wa b with
            | some vb => some (some (dst, ⟨wa, selectW cond va vb⟩))
            | none => none
        | _, _ => none
      else none
  | .Lopn [.reg dst] opn [a, b] =>
      match readReg s a with
      | some ⟨wa, va⟩ =>
          match evalOperandN s wa b with
          | some vb =>
              match applyOpnN wa (stripWidthTag opn) [va, vb] with
              | some v => some (some (dst, ⟨wa, v⟩))
              | none =>
                  match cmpOfName? (stripWidthTag opn) with
                  | some c => some (some (dst, ⟨1, cmpBit c va vb⟩))
                  | none => none
          | none => none
      | none =>
          match a with
          | .imm n =>
              match evalOperandN s (widthFromTag opn) b with
              | some vb =>
                  match applyOpnN (widthFromTag opn) (stripWidthTag opn)
                      [BitVec.ofNat _ n, vb] with
                  | some v => some (some (dst, ⟨widthFromTag opn, v⟩))
                  | none => none
              | none => none
          | _ => none
  | .Lopn [.reg dst] opn [.imm n] =>
      if stripWidthTag opn = "MOV" then
        some (some (dst, ⟨widthFromTag opn, BitVec.ofNat (widthFromTag opn) n⟩))
      else none
  | .Lopn [.reg dst] opn [.reg a] =>
      if stripWidthTag opn = "NEG" then
        match readReg s (.reg a) with
        | some ⟨wa, va⟩ =>
            match applyOpnN wa "NEG" [va] with
            | some v => some (some (dst, ⟨wa, v⟩))
            | none => none
        | none => none
      else
        if stripWidthTag opn = "MOV" then
          match readReg s (.reg a) with
          | some ⟨wa, va⟩ =>
              match applyOpnN wa "MOV" [va] with
              | some v => some (some (dst, ⟨wa, v⟩))
              | none => none
          | none => none
        else
          match JasminImmShiftMnem.immShiftMnem? opn with
          | some (m, k) =>
              match readReg s (.reg a) with
              | some ⟨wa, va⟩ =>
                  match applyImmShiftN wa m k va with
                  | some v => some (some (dst, ⟨wa, v⟩))
                  | none => none
              | none => none
          | none => none
  | .Lopn [.reg dst] opn [.arrIdx b x sc] =>
      if stripWidthTag opn = "LEA" then
        match s.getW b 64, s.getW x 64 with
        | some p, some vi => some (some (dst, ⟨64, p + BitVec.ofNat 64 (sc * vi.toNat)⟩))
        | _, _ => none
      else none
  | .Lopn _ _ _ => none
  | .Lalign => some none
  | .Llabel _ _ => some none
  | .Lgoto _ => none
  | .Lcond _ _ => none
  | .Ligoto _ => none
  | .Lcall _ _ => none
  | .Lret => none
  | .LstoreLabel _ _ => none
  | .Lsyscall _ => none

/-- Apply a width-tagged step's write and advance the pc. -/
def applyEff (s : LstateN) : Option Cell → LstateN
  | none => s.nextPc
  | some (d, ⟨_, v⟩) => (s.setReg d v).nextPc

/-- The register a width-tagged step's write targets. -/
def effName : Option Cell → Option String
  | none => none
  | some (d, _) => some d

/-- An unmodeled width-tagged step is unmodeled by the machine. -/
theorem stepEff_eq_none (i : LinstrR) (s : LstateN) (h : stepEff i s = none) :
    lsemStepN i s = none := by
  unfold stepEff at h
  repeat' split at h
  all_goals simp_all [lsemStepN, immFirstN]

/-- A modeled width-tagged step is its write applied to the incoming state. -/
theorem stepEff_eq_some (i : LinstrR) (s : LstateN) (e : Option Cell)
    (h : stepEff i s = some e) : lsemStepN i s = some (applyEff s e) := by
  unfold stepEff at h
  repeat' split at h
  all_goals simp_all [lsemStepN, applyEff, immFirstN]
  all_goals (subst h; rfl)

/-- `lsemStepN` is its write applied to the incoming state. -/
theorem lsemStepN_eq_applyEff (i : LinstrR) (s : LstateN) :
    lsemStepN i s = (stepEff i s).map (applyEff s) := by
  cases h : stepEff i s with
  | none => simp [stepEff_eq_none i s h]
  | some e => simp [stepEff_eq_some i s e h]

/-- A width-tagged step's write depends on the store only at its read keys. -/
theorem stepEff_congr (i : LinstrR) (s1 s2 : LstateN) (hai : hasArrIdx i = false)
    (h : ∀ r ∈ readToksSem i, s1.lvm r = s2.lvm r) : stepEff i s1 = stepEff i s2 := by
  unfold stepEff
  split
  · rename_i dst opn c a b
    have h0 : s1.lvm "" = s2.lvm "" := h "" (by simp [readToksSem])
    have hc := getW_operandName_congr c (h _ (by simp [readToksSem])) h0
    have ha := readReg_congr a (h _ (by simp [readToksSem]))
    have hb := evalOperandN_congr b (h _ (by simp [readToksSem]))
    simp only [hc, ha, hb]
  · rename_i dst opn a b
    have ha := readReg_congr a (h _ (by simp [readToksSem]))
    have hb := evalOperandN_congr b (h _ (by simp [readToksSem]))
    simp only [ha, hb]
  · rfl
  · rename_i dst opn a
    have ha := readReg_congr (.reg a) (h _ (by simp [readToksSem]))
    simp only [ha]
  · simp [hasArrIdx, opIsArrIdx] at hai
  all_goals rfl

/-- A width-tagged step that writes is a single-register-destination `Lopn`
    targeting that register. -/
theorem stepEff_dst (i : LinstrR) (s : LstateN) (d : String) (c : Σ w, BitVec w)
    (h : stepEff i s = some (some (d, c))) : ∃ opn srcs, i = .Lopn [.reg d] opn srcs := by
  unfold stepEff at h
  repeat' split at h
  all_goals simp_all

/-- A width-tagged step's write footprint is its write target alone. -/
theorem stepEff_writeToks (i : LinstrR) (s : LstateN) (d : String) (c : Σ w, BitVec w)
    (h : stepEff i s = some (some (d, c))) : writeToks i = [d] := by
  obtain ⟨opn, srcs, rfl⟩ := stepEff_dst i s d c h
  rfl

/-- The write footprint of a width-tagged step, named through its write
    target. -/
theorem stepEff_writeToks_of_effName {i : LinstrR} {s : LstateN} {e : Option Cell}
    {d : String} (h : stepEff i s = some e) (hd : effName e = some d) :
    writeToks i = [d] := by
  cases e with
  | none => simp [effName] at hd
  | some p =>
    obtain ⟨d', c⟩ := p
    simp only [effName, Option.some.injEq] at hd
    subst hd
    exact stepEff_writeToks i s d' c h

/-- A width-tagged step leaves every register but its target unchanged. -/
theorem applyEff_lvm_of_ne (s : LstateN) (e : Option Cell) (r : String)
    (h : effName e ≠ some r) : (applyEff s e).lvm r = s.lvm r := by
  cases e with
  | none => rfl
  | some p =>
    obtain ⟨d, w, v⟩ := p
    simp only [effName, ne_eq, Option.some.injEq] at h
    have h' : ¬ (r = d) := fun e => h e.symm
    simp [applyEff, LstateN.setReg, LstateN.nextPc, h']

/-- Width-tagged writes to distinct registers commute. -/
theorem applyEff_comm (s : LstateN) (e1 e2 : Option Cell)
    (h : ∀ d1 ∈ effName e1, ∀ d2 ∈ effName e2, d1 ≠ d2) :
    applyEff (applyEff s e1) e2 = applyEff (applyEff s e2) e1 := by
  cases e1 with
  | none => cases e2 with
    | none => rfl
    | some p2 => obtain ⟨d2, w2, v2⟩ := p2; rfl
  | some p1 =>
    obtain ⟨d1, w1, v1⟩ := p1
    cases e2 with
    | none => rfl
    | some p2 =>
      obtain ⟨d2, w2, v2⟩ := p2
      have hne : d1 ≠ d2 := h d1 rfl d2 rfl
      obtain ⟨m, p⟩ := s
      simp only [applyEff, LstateN.setReg, LstateN.nextPc]
      congr 1
      funext r
      by_cases h1 : r = d1 <;> by_cases h2 : r = d2 <;> simp_all

/-- An instruction whose read keys miss another's write target computes the same
    write before and after that other step. -/
theorem stepEff_after (i j : LinstrR) (s : LstateN) (e : Option Cell)
    (hai : hasArrIdx i = false) (hj : stepEff j s = some e)
    (hd : disjointL (writeToks j) (readToksSem i) = true) :
    stepEff i (applyEff s e) = stepEff i s := by
  refine stepEff_congr i _ s hai ?_
  intro r hr
  refine applyEff_lvm_of_ne s e r ?_
  intro hcon
  have hw : writeToks j = [r] := stepEff_writeToks_of_effName hj hcon
  exact (disjointL_ne hd (by rw [hw]; simp) hr) rfl

/-- **Adjacent-transposition commutation over the width-tagged store.**  Swapping
    an independent adjacent pair leaves `lsemStraightN` unchanged. -/
theorem lsemStraightN_swap (i1 i2 : LinstrR) (rest : List LinstrR) (s : LstateN)
    (h : indep i1 i2 = true) :
    lsemStraightN (i1 :: i2 :: rest) s = lsemStraightN (i2 :: i1 :: rest) s := by
  have hww := indep_ww h
  have hwr := indep_wr h
  have hrw := indep_rw h
  have ha1 := indep_arrIdx_left h
  have ha2 := indep_arrIdx_right h
  rcases h1 : stepEff i1 s with _ | e1 <;> rcases h2 : stepEff i2 s with _ | e2
  · simp [lsemStraightN, lsemStepN_eq_applyEff, h1, h2]
  · simp [lsemStraightN, lsemStepN_eq_applyEff, h1, h2,
      stepEff_after i1 i2 s e2 ha1 h2 hrw]
  · simp [lsemStraightN, lsemStepN_eq_applyEff, h1, h2,
      stepEff_after i2 i1 s e1 ha2 h1 hwr]
  · have hne : ∀ d1 ∈ effName e1, ∀ d2 ∈ effName e2, d1 ≠ d2 := by
      intro d1 hd1 d2 hd2
      have w1 : writeToks i1 = [d1] := stepEff_writeToks_of_effName h1 hd1
      have w2 : writeToks i2 = [d2] := stepEff_writeToks_of_effName h2 hd2
      exact disjointL_ne hww (by rw [w1]; simp) (by rw [w2]; simp)
    simp only [lsemStraightN, lsemStepN_eq_applyEff, h1, h2, Option.map_some,
      stepEff_after i2 i1 s e1 ha2 h1 hwr,
      stepEff_after i1 i2 s e2 ha1 h2 hrw]
    rw [applyEff_comm s e1 e2 hne]

/-! ## 11. Lifting a commutation law along the schedule

`bubble` performs only adjacent transpositions of `indep` pairs, so any
execution function that composes over list concatenation and is invariant under
one such transposition is invariant under the whole schedule. -/

/-- One bubble pass preserves any concatenation-composing execution function
    that an independent adjacent transposition leaves unchanged. -/
theorem bubble_run {S : Type} {run : List LinstrR → S → Option S}
    (happ : ∀ (l1 l2 : List LinstrR) (s : S), run (l1 ++ l2) s = (run l1 s).bind (run l2))
    (hswap : ∀ (i1 i2 : LinstrR) (rest : List LinstrR) (s : S),
        indep i1 i2 = true → run (i1 :: i2 :: rest) s = run (i2 :: i1 :: rest) s) :
    ∀ (b : List Linstr) (s : S),
      run ((bubble b).map Linstr.li_i) s = run (b.map Linstr.li_i) s := by
  have hcong : ∀ (i : LinstrR) (l1 l2 : List LinstrR), (∀ s, run l1 s = run l2 s) →
      ∀ s, run (i :: l1) s = run (i :: l2) s := by
    intro i l1 l2 hl s
    have e1 : (i :: l1) = [i] ++ l1 := rfl
    have e2 : (i :: l2) = [i] ++ l2 := rfl
    rw [e1, e2, happ, happ, funext hl]
  intro b
  induction b using bubble.induct with
  | case1 => intro s; simp [bubble]
  | case2 i => intro s; simp [bubble]
  | case3 i1 i2 rest hcond ih =>
      intro s
      have hind : indep i1.li_i i2.li_i = true := by
        simp only [Bool.and_eq_true] at hcond; exact hcond.1
      simp only [bubble, if_pos hcond, List.map_cons]
      rw [hcong i2.li_i _ _ ih s]
      simp only [List.map_cons]
      exact (hswap i1.li_i i2.li_i (rest.map Linstr.li_i) s hind).symm
  | case4 i1 i2 rest hcond ih =>
      intro s
      simp only [bubble, if_neg hcond, List.map_cons]
      exact hcong i1.li_i _ _ ih s

/-- Iterated bubble passes preserve such an execution function. -/
theorem bubbleN_run {S : Type} {run : List LinstrR → S → Option S}
    (happ : ∀ (l1 l2 : List LinstrR) (s : S), run (l1 ++ l2) s = (run l1 s).bind (run l2))
    (hswap : ∀ (i1 i2 : LinstrR) (rest : List LinstrR) (s : S),
        indep i1 i2 = true → run (i1 :: i2 :: rest) s = run (i2 :: i1 :: rest) s) :
    ∀ (k : Nat) (b : List Linstr) (s : S),
      run ((bubbleN k b).map Linstr.li_i) s = run (b.map Linstr.li_i) s := by
  intro k
  induction k with
  | zero => intro b s; rfl
  | succ k ih =>
    intro b s
    simp only [bubbleN]
    rw [ih (bubble b) s]
    exact bubble_run happ hswap b s

/-- The schedule preserves such an execution function. -/
theorem scheduleBody_run {S : Type} {run : List LinstrR → S → Option S}
    (happ : ∀ (l1 l2 : List LinstrR) (s : S), run (l1 ++ l2) s = (run l1 s).bind (run l2))
    (hswap : ∀ (i1 i2 : LinstrR) (rest : List LinstrR) (s : S),
        indep i1 i2 = true → run (i1 :: i2 :: rest) s = run (i2 :: i1 :: rest) s)
    (b : List Linstr) (s : S) :
    run ((scheduleBody b).map Linstr.li_i) s = run (b.map Linstr.li_i) s := by
  rw [scheduleBody_eq_bubbleN]; exact bubbleN_run happ hswap b.length b s

/-- The tail-preserving schedule preserves such an execution function. -/
theorem scheduleBodyTail_run {S : Type} {run : List LinstrR → S → Option S}
    (happ : ∀ (l1 l2 : List LinstrR) (s : S), run (l1 ++ l2) s = (run l1 s).bind (run l2))
    (hswap : ∀ (i1 i2 : LinstrR) (rest : List LinstrR) (s : S),
        indep i1 i2 = true → run (i1 :: i2 :: rest) s = run (i2 :: i1 :: rest) s)
    (keepTail : Nat) (b : List Linstr) (s : S) :
    run ((scheduleBodyTail keepTail b).map Linstr.li_i) s = run (b.map Linstr.li_i) s := by
  simp only [scheduleBodyTail, List.map_append]
  rw [happ, scheduleBody_run happ hswap, ← happ, ← List.map_append, List.take_append_drop]

/-- **Schedule soundness at uniform word width.** -/
theorem scheduleBody_lsemStraight {w : Nat} (b : List Linstr) (s : Lstate w) :
    lsemStraight ((scheduleBody b).map Linstr.li_i) s = lsemStraight (b.map Linstr.li_i) s :=
  scheduleBody_run (run := fun l s => lsemStraight (w := w) l s)
    (fun l1 l2 s => lsemStraight_append l1 l2 s)
    (fun i1 i2 rest s hi => lsemStraight_swap i1 i2 rest s hi) b s

/-- **Schedule soundness over the width-tagged store.** -/
theorem scheduleBody_lsemStraightN (b : List Linstr) (s : LstateN) :
    lsemStraightN ((scheduleBody b).map Linstr.li_i) s = lsemStraightN (b.map Linstr.li_i) s :=
  scheduleBody_run (run := lsemStraightN)
    (fun l1 l2 s => lsemStraightN_append l1 l2 s)
    (fun i1 i2 rest s hi => lsemStraightN_swap i1 i2 rest s hi) b s

/-- **Tail-preserving schedule soundness at uniform word width.** -/
theorem scheduleBodyTail_lsemStraight {w : Nat} (keepTail : Nat) (b : List Linstr)
    (s : Lstate w) :
    lsemStraight ((scheduleBodyTail keepTail b).map Linstr.li_i) s
      = lsemStraight (b.map Linstr.li_i) s :=
  scheduleBodyTail_run (run := fun l s => lsemStraight (w := w) l s)
    (fun l1 l2 s => lsemStraight_append l1 l2 s)
    (fun i1 i2 rest s hi => lsemStraight_swap i1 i2 rest s hi) keepTail b s

/-- **Tail-preserving schedule soundness over the width-tagged store.** -/
theorem scheduleBodyTail_lsemStraightN (keepTail : Nat) (b : List Linstr) (s : LstateN) :
    lsemStraightN ((scheduleBodyTail keepTail b).map Linstr.li_i) s
      = lsemStraightN (b.map Linstr.li_i) s :=
  scheduleBodyTail_run (run := lsemStraightN)
    (fun l1 l2 s => lsemStraightN_append l1 l2 s)
    (fun i1 i2 rest s hi => lsemStraightN_swap i1 i2 rest s hi) keepTail b s

/-- Per-function schedule soundness at uniform word width. -/
theorem scheduleLfundef_lsemStraight {w : Nat} (f : Lfundef) (s : Lstate w) :
    lsemStraight ((scheduleLfundef f).lfd_body.map Linstr.li_i) s
      = lsemStraight (f.lfd_body.map Linstr.li_i) s :=
  scheduleBody_lsemStraight f.lfd_body s

/-- Every function of the scheduled program is the scheduled function of the
    source program under the same name. -/
theorem scheduleLprog_funcs (p : Lprog) :
    (scheduleLprog p).lp_funcs
      = p.lp_funcs.map (fun nf => (nf.1, scheduleLfundef nf.2)) := rfl

/-- Any per-instruction attribute of the scheduled body is a permutation of the
    same attribute of the input: the pass rewrites no mnemonic, hence no
    rendered operand width. -/
theorem scheduleBody_attr_perm {α : Type} (attr : Linstr → α) (b : List Linstr) :
    ((scheduleBody b).map attr).Perm (b.map attr) :=
  (scheduleBody_perm b).map attr

-- A pair the schedule reorders keeps both `:64` width tags.
#guard ((scheduleBody [⟨0, .Lopn [.reg "a"] (withWidthTag 64 (binOpName .xor)) [.reg "b", .reg "c"]⟩,
                       ⟨0, .Lopn [.reg "lo", .reg "hi"] (withWidthTag 64 "MULX") [.reg "s"]⟩]).map
          (fun i => match i.li_i with | .Lopn _ m _ => m | _ => ""))
        == ["MULX:64", "XOR:64"]

-- The pass reorders an exporter-spelled body: `r2` reads `r1`, so the `ADD`/`XOR`
-- pair is a dependence chain the pass keeps in order, while the flag-free
-- `MULX` is hoisted ahead of both.
#guard ((scheduleBody
          [ ⟨0, .Lopn [.reg "r1"] (withWidthTag 64 (binOpName .add)) [.reg "a", .reg "b"]⟩
          , ⟨0, .Lopn [.reg "r2"] (withWidthTag 64 (binOpName .xor)) [.reg "r1", .reg "c"]⟩
          , ⟨0, .Lopn [.reg "lo", .reg "hi"] (withWidthTag 64 "MULX") [.reg "s"]⟩ ]).map
          (fun i => match i.li_i with | .Lopn _ m _ => m | _ => ""))
        == ["MULX:64", "ADD:64", "XOR:64"]

-- The `mulx` multiplicand pin: `fuseMulHiLprog` emits `MOV:64 RDX, s1` ahead of
-- the `MULX` that reads `%rdx`. The register footprints alone permit hoisting
-- the multiply over its own pin; the implicit read forbids it.
#guard (indepFootprint (.Lopn [.reg "RDX"] (withWidthTag 64 "MOV") [.reg "RBP"])
                       (.Lopn [.reg "r1", .reg "r2"] (withWidthTag 64 "MULX") [.reg "RSI"]))
        == true

#guard (indep (.Lopn [.reg "RDX"] (withWidthTag 64 "MOV") [.reg "RBP"])
              (.Lopn [.reg "r1", .reg "r2"] (withWidthTag 64 "MULX") [.reg "RSI"]))
        == false

#guard ((scheduleBody
          [ ⟨0, .Lopn [.reg "RDX"] (withWidthTag 64 "MOV") [.reg "RBP"]⟩
          , ⟨0, .Lopn [.reg "r1", .reg "r2"] (withWidthTag 64 "MULX") [.reg "RSI"]⟩ ]).map
          (fun i => match i.li_i with | .Lopn _ m _ => m | _ => ""))
        == ["MOV:64", "MULX:64"]

-- A binding marker names a value its producer computes as a side effect, so it
-- is never moved, whatever the registers say.
#guard (indepFootprint (.Lopn [.reg "r1"] (withWidthTag 64 (binOpName .add)) [.reg "a", .reg "b"])
                       (.Lopn [.reg "r3"] (withWidthTag 64 "MULXHI") [.reg "d", .reg "e"]))
        == true

#guard (indep (.Lopn [.reg "r1"] (withWidthTag 64 (binOpName .add)) [.reg "a", .reg "b"])
              (.Lopn [.reg "r3"] (withWidthTag 64 "MULXHI") [.reg "d", .reg "e"]))
        == false

-- The carry-chain hazard: an `ADCX` and a shift with disjoint registers, which
-- the register footprints alone permit swapping and the flags cell forbids —
-- the shift writes the flags the `ADCX` reads.
#guard (indepFootprint (.Lopn [.reg "r1"] (withWidthTag 64 "ADCX") [.reg "r2", .reg "r3"])
                       (.Lopn [.reg "r4"] (withWidthTag 64 ("SHL:" ++ toString 3)) [.reg "r5"]))
        == true

#guard (indep (.Lopn [.reg "r1"] (withWidthTag 64 "ADCX") [.reg "r2", .reg "r3"])
              (.Lopn [.reg "r4"] (withWidthTag 64 ("SHL:" ++ toString 3)) [.reg "r5"]))
        == false

#guard ((scheduleBody
          [ ⟨0, .Lopn [.reg "r1"] (withWidthTag 64 "ADCX") [.reg "r2", .reg "r3"]⟩
          , ⟨0, .Lopn [.reg "r4"] (withWidthTag 64 ("SHL:" ++ toString 3)) [.reg "r5"]⟩ ]).map
          (fun i => match i.li_i with | .Lopn _ m _ => m | _ => ""))
        == ["ADCX:64", "SHL:3:64"]

-- The `MULX` family touches no flags, so a carry chain does not pin it: a
-- `MULX` whose multiplicand register the `ADCX` does not write still hoists
-- ahead of it.
#guard ((scheduleBody
          [ ⟨0, .Lopn [.reg "r1"] (withWidthTag 64 "ADCX") [.reg "r2", .reg "r3"]⟩
          , ⟨0, .Lopn [.reg "r4", .reg "r5"] (withWidthTag 64 "MULX") [.reg "r6"]⟩ ]).map
          (fun i => match i.li_i with | .Lopn _ m _ => m | _ => ""))
        == ["MULX:64", "ADCX:64"]

/-! ## 12. The leakage trace

`JasminLsemRobust.linstrLeak` emits one `LLeak.opn` event per `Lopn`, carrying
the opcode and the operand shapes; it reads no register value, no address, and no
branch outcome. Constant-timeness at this model is therefore independence of the
start state, which `lsemLeak_of_run` shows every completing body has and the pass
keeps (`scheduleBody_lsemLeak_state_indep`).

Every `Lopn` leaks, so *any* adjacent transposition moves an event and changes
the trace: leakage-trace **equality** is not available for an instruction
scheduler under this model, and the two `#guard`s below exhibit a body whose
trace changes length under `scheduleBody`.

What holds instead is conditional on the priorities. On a body whose
instructions all carry the same latency priority the strict `<` in `bubble`'s
guard fails at every pair, so `scheduleBody` is the identity
(`scheduleBody_id_of_uniform_prio`) and the trace is preserved exactly
(`scheduleBody_lsemLeak_of_uniform_prio`). A body that mixes a multiply or a
shift with plain ALU ops carries two priorities and is reordered; the two
`#guard`s below exhibit such a body, whose trace changes length. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-- **The pass keeps constant-timeness at this model.**  Whenever the scheduled
    body runs to completion from two start states, it leaks the same trace from
    both. -/
theorem scheduleBody_lsemLeak_state_indep {w : Nat} (b : List Linstr)
    (s t s₂ t₂ : Lstate w)
    (hs : lsemStraight ((scheduleBody b).map Linstr.li_i) s = some s₂)
    (ht : lsemStraight ((scheduleBody b).map Linstr.li_i) t = some t₂) :
    lsemLeak ((scheduleBody b).map Linstr.li_i) s
      = lsemLeak ((scheduleBody b).map Linstr.li_i) t := by
  rw [lsemLeak_of_run _ s s₂ hs, lsemLeak_of_run _ t t₂ ht]

/-- The latency the recogniser assigns to each mnemonic the exporter emits for a
    register binop, at either width: the multiply is the long-latency op, the two
    shifts are short, and the remaining ALU ops carry the base latency. -/
theorem latencyPrio_binOpName (bop : JasminBinOp) (w : Nat) (dsts srcs : List LOperand) :
    latencyPrio (.Lopn dsts (withWidthTag w (binOpName bop)) srcs)
      = match bop with
        | .mul => 4
        | .shl => 2
        | .shr => 2
        | _ => 1 := by
  cases bop <;> unfold withWidthTag <;> split <;> simp only [latencyPrio] <;> decide +kernel

/-- One bubble pass is the identity on a body whose instructions all carry the
    same latency priority: the swap branch is gated on a strict increase. -/
theorem bubble_id_of_uniform_prio (k : Nat) : ∀ (b : List Linstr),
    (∀ i ∈ b, latencyPrio i.li_i = k) → bubble b = b := by
  intro b
  induction b using bubble.induct with
  | case1 => intro _; simp [bubble]
  | case2 i => intro _; simp [bubble]
  | case3 i1 i2 rest hcond _ =>
      intro hall
      exfalso
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have h1 := hall i1 (by simp)
      have h2 := hall i2 (by simp)
      omega
  | case4 i1 i2 rest hcond ih =>
      intro hall
      simp only [bubble, if_neg hcond]
      rw [ih (fun i hi => hall i (List.mem_cons_of_mem i1 hi))]

/-- Iterated bubble passes are the identity on a uniform-priority body. -/
theorem bubbleN_id_of_uniform_prio (k : Nat) : ∀ (n : Nat) (b : List Linstr),
    (∀ i ∈ b, latencyPrio i.li_i = k) → bubbleN n b = b := by
  intro n
  induction n with
  | zero => intro b _; rfl
  | succ n ih =>
    intro b hall
    simp only [bubbleN, bubble_id_of_uniform_prio k b hall]
    exact ih b hall

/-- The schedule is the identity on a uniform-priority body. -/
theorem scheduleBody_id_of_uniform_prio (k : Nat) (b : List Linstr)
    (hall : ∀ i ∈ b, latencyPrio i.li_i = k) : scheduleBody b = b := by
  rw [scheduleBody_eq_bubbleN]; exact bubbleN_id_of_uniform_prio k b.length b hall

/-- **Leakage preservation where the pass applies.**  On a uniform-priority body
    the schedule leaves the leakage trace unchanged. -/
theorem scheduleBody_lsemLeak_of_uniform_prio {w : Nat} (k : Nat) (b : List Linstr)
    (hall : ∀ i ∈ b, latencyPrio i.li_i = k) (s : Lstate w) :
    lsemLeak ((scheduleBody b).map Linstr.li_i) s = lsemLeak (b.map Linstr.li_i) s := by
  rw [scheduleBody_id_of_uniform_prio k b hall]

-- An `indep` pair the schedule does reorder: the trace has two events before the
-- schedule and one after, so leakage-trace equality fails in general.
#guard
  (lsemLeak ([(⟨0, .Lopn [.reg "a"] "XOR:64" [.reg "b", .reg "c"]⟩ : Linstr),
              ⟨0, .Lopn [.reg "lo", .reg "hi"] "MULX:64" [.reg "s"]⟩].map Linstr.li_i)
      ({ lvm := fun _ => 0 } : Lstate 64)).length == 2

#guard
  (lsemLeak ((scheduleBody [(⟨0, .Lopn [.reg "a"] "XOR:64" [.reg "b", .reg "c"]⟩ : Linstr),
                            ⟨0, .Lopn [.reg "lo", .reg "hi"] "MULX:64" [.reg "s"]⟩]).map
        Linstr.li_i) ({ lvm := fun _ => 0 } : Lstate 64)).length == 1

end CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
