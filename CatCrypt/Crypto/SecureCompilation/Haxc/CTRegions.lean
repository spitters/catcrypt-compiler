/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.CTPub

@[expose] public section

set_option autoImplicit false

/-!
# The constant-time gate without the separation side condition

`AbiLayout.ctGateB_sound` states constant time for the runs of the decoded program whose
steps satisfy `DecodedCT.FrameSep`: no store through a base other than `%rsp` overlaps a
frame word of the certificate. This module discharges that condition for every run from an
entry state satisfying `σ.Regions`, by a second Boolean check on the decoded program.

## The region analysis

An abstract state `RegionSep.MA` describes a machine state relative to the entry state
`s0` of the run (`RegionSep.Inv`): the stack pointer is the entry stack pointer plus `sp`;
a register holds the entry value of a register (`ent`) or the word `0` (`zero`); a stack
word at offset `e` from the entry stack pointer, inside the frame range of `σ`, holds the
entry value of a register (`slot`); for a pair of registers `(x, c)` the sum of their
values is at most a bound (`le`); a register is nonzero (`nz`); the zero flag reports
whether a register is zero (`zf`); a register holds a constant (`cst`). `RegionSep.trans`
is the abstract effect of an instruction, under which a register copy (`RegionSep.copyOf`:
a move, an operation with a register holding `0`, a shift by `0`) carries the facts of its
source, the addition of `1`, of a register holding a constant or of a register with an upper bound
(`RegionSep.ubOf`) raises the bounds of the sums with the destination, the multiplication
`d := y · v` by an immediate `v ≥ 1` turns a fact `y + c ≤ B` into `d + c ≤ v · B`, or
`d + c ≤ v · B - (v - 1)` for a nonzero `c` (`RegionSep.mulLe`), a register holding `0` and a register holding a constant `n`
have a sum of at most `n` (`RegionSep.norm`), and
`RegionSep.jccOut` is that of a branch. `RegionSep.cellAddrOK` checks that a store through a base other than `%rsp` writes a word of a pointer region of `σ`: the base
holds the entry pointer of the region, and either the displacement is a word offset below
the region length or the index register is below it by an `le` fact. `RegionSep.memCheck`
checks a certificate (an abstract state per index) and `RegionSep.inferM` computes one by
forward iteration.

## The gate

The certificate of the constant-time checker is trimmed (`RegionSep.trimCert`): a frame
word is kept when, at every index that stores through another base, it lies inside the
frame range of `σ`. `AbiLayout.ctCheckR` is the constant-time decision on the trimmed
certificate (`DecodedCT.fastCheckWith`) together with `memCheck` for its frame words
`AbiLayout.ctFrameR`; `AbiLayout.ctGateR` decodes the bytes first.

## Main results

* `RegionSep.memCheck_sound` — under a passing `memCheck`, every run from an entry state
  satisfying `σ.Regions` satisfies `FrameSep F` at every step.
* `RegionSep.fastCheckWith_sound` — soundness of the constant-time decision on any
  certificate.
* `RegionSep.stepW_sound` — soundness of the facts on stack words (`RegionSep.MW`): constants,
  sums and nonzero words of a loop whose index and count live in stack words, and pointers
  `lea d (b, x, 8)` with a bounded index.
* `AbiLayout.pubAS_agree` — the stack words of public stack parameters agree at entry.
* `AbiLayout.ctGateR_sound` — bytes that pass `ctGateR` decode to a program whose runs,
  with no side condition, from entry states satisfying `σ.Regions` and agreeing on the
  public data of `σ`, have equal leakage traces.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.CT

namespace RegionSep

/-! ## 1. Abstract states -/

/-- The facts on the stack words of the frame range, each word named by its offset from the
    entry stack pointer, and on the registers a loop with spilled counters computes from them:
    a loop that calls a callee clobbering every register keeps its index and its count in
    stack words. -/
structure MW where
  /-- `(e, n)`: the stack word at offset `e` holds the word `n`. -/
  cst : List (Int × Nat) := []
  /-- Offsets of stack words holding a nonzero word. -/
  nz : List Int := []
  /-- `(e, e', B)`: the values of the stack words at the offsets `e` and `e'` sum to at most
      `B`. -/
  le : List (Int × Int × Int) := []
  /-- `(r, e, B)`: the values of the register `r` and of the stack word at offset `e` sum to
      at most `B`. -/
  rle : List (String × Int × Int) := []
  /-- `(r, e)`: the register `r` holds the value of the stack word at offset `e`. -/
  same : List (String × Int) := []
  /-- `(r, x, n)`: the register `r` holds the entry value of the register `x` plus `8 j` for
      some `j < n`. -/
  ptr : List (String × String × Nat) := []
  deriving DecidableEq, Repr, Inhabited

/-- The facts of `w` on the registers that satisfy `k`, with all the facts on stack words. -/
def MW.keepRegs (w : MW) (k : String → Bool) : MW :=
  { w with
    rle := w.rle.filter fun f => k f.1
    same := w.same.filter fun p => k p.1
    ptr := w.ptr.filter fun p => k p.1 }

/-- The facts of `w` on the stack words that satisfy `k`, with all the facts on registers
    alone. -/
def MW.keepWords (w : MW) (k : Int → Bool) : MW :=
  { w with
    cst := w.cst.filter fun p => k p.1
    nz := w.nz.filter k
    le := w.le.filter fun f => k f.1 && k f.2.1
    rle := w.rle.filter fun f => k f.2.1
    same := w.same.filter fun p => k p.2 }

/-- The facts of `a` and the facts of `b`. -/
def MW.union (a b : MW) : MW :=
  { cst := a.cst ++ b.cst
    nz := a.nz ++ b.nz
    le := a.le ++ b.le
    rle := a.rle ++ b.rle
    same := a.same ++ b.same
    ptr := a.ptr ++ b.ptr }

/-- Every fact of `b` is a fact of `o`. -/
def MW.leW (b o : MW) : Bool :=
  b.cst.all o.cst.contains && b.nz.all o.nz.contains && b.le.all o.le.contains
    && b.rle.all o.rle.contains && b.same.all o.same.contains && b.ptr.all o.ptr.contains

/-- The facts common to `a` and `b`. -/
def MW.meet (a b : MW) : MW :=
  { cst := a.cst.filter b.cst.contains
    nz := a.nz.filter b.nz.contains
    le := a.le.filter b.le.contains
    rle := a.rle.filter b.rle.contains
    same := a.same.filter b.same.contains
    ptr := a.ptr.filter b.ptr.contains }

/-- An abstract machine state relative to the entry state of a run. -/
structure MA where
  /-- The offset of the stack pointer from its entry value. -/
  sp : Int
  /-- `(r, x)`: the register `r` holds the entry value of the register `x`. -/
  ent : List (String × String)
  /-- Registers holding the word `0`. -/
  zero : List String
  /-- `(e, x)`: the stack word at offset `e` from the entry stack pointer holds the entry
      value of the register `x`. -/
  slot : List (Int × String)
  /-- `(x, c, B)`: the values of `x` and `c` sum to at most `B`. -/
  le : List (String × String × Int)
  /-- Registers holding a nonzero word. -/
  nz : List String
  /-- The register whose being zero the zero flag reports. -/
  zf : Option String
  /-- `(r, n)`: the register `r` holds the word `n`. -/
  cst : List (String × Nat) := []
  /-- The facts on stack words and on registers computed from them. -/
  w : MW := {}
  deriving DecidableEq, Repr, Inhabited

/-- The offset `e` from the entry stack pointer lies in the frame range of `σ`. -/
def inW (σ : AbiLayout) (e : Int) : Bool := decide (σ.frameLo ≤ e) && decide (e ≤ σ.frameHi)

/-- The stack word at offset `e` from the entry stack pointer of `s0`, in the state `s`. -/
def wdAt (s0 s : AState) (e : Int) : BitVec 64 :=
  read64 s.mem (s0.regs "%rsp" + BitVec.ofInt 64 e)

/-- The facts `w` describe the machine state `s` of a run from the entry state `s0`; the
    stack words they name lie in the frame range of `σ`. -/
structure InvW (σ : AbiLayout) (s0 : AState) (w : MW) (s : AState) : Prop where
  cst : ∀ p ∈ w.cst, inW σ p.1 = true ∧ wdAt s0 s p.1 = BitVec.ofNat 64 p.2
  nz : ∀ e ∈ w.nz, inW σ e = true ∧ wdAt s0 s e ≠ 0
  le : ∀ f ∈ w.le, inW σ f.1 = true ∧ inW σ f.2.1 = true ∧
    ((wdAt s0 s f.1).toNat : Int) + (wdAt s0 s f.2.1).toNat ≤ f.2.2
  rle : ∀ f ∈ w.rle, inW σ f.2.1 = true ∧
    ((s.regs f.1).toNat : Int) + (wdAt s0 s f.2.1).toNat ≤ f.2.2
  same : ∀ p ∈ w.same, inW σ p.2 = true ∧ s.regs p.1 = wdAt s0 s p.2
  ptr : ∀ p ∈ w.ptr, ∃ j, j < p.2.2 ∧ s.regs p.1 = s0.regs p.2.1 + BitVec.ofNat 64 (8 * j)

/-- The abstract state `m` describes the machine state `s` of a run from the entry state
    `s0` under the layout `σ`. -/
structure Inv (σ : AbiLayout) (s0 : AState) (m : MA) (s : AState) : Prop where
  sp : s.regs "%rsp" = s0.regs "%rsp" + BitVec.ofInt 64 m.sp
  ent : ∀ p ∈ m.ent, s.regs p.1 = s0.regs p.2
  zero : ∀ r ∈ m.zero, s.regs r = 0
  slot : ∀ e ∈ m.slot, inW σ e.1 = true ∧
    read64 s.mem (s0.regs "%rsp" + BitVec.ofInt 64 e.1) = s0.regs e.2
  le : ∀ f ∈ m.le, ((s.regs f.1).toNat : Int) + (s.regs f.2.1).toNat ≤ f.2.2
  nz : ∀ r ∈ m.nz, s.regs r ≠ 0
  zf : ∀ c, m.zf = some c → s.view.condB .e = decide (s.regs c = 0)
  cst : ∀ p ∈ m.cst, s.regs p.1 = BitVec.ofNat 64 p.2
  w : InvW σ s0 m.w s

/-- Every fact of `b` is a fact of `o`, at the same stack offset. -/
def leM (b o : MA) : Bool :=
  b.sp == o.sp && b.ent.all o.ent.contains && b.zero.all o.zero.contains
    && b.slot.all o.slot.contains && b.le.all o.le.contains && b.nz.all o.nz.contains
    && (b.zf.isNone || b.zf == o.zf) && b.cst.all o.cst.contains && MW.leW b.w o.w

theorem InvW.of_leW {σ : AbiLayout} {s0 : AState} {b o : MW} {s : AState}
    (h : MW.leW b o = true) (hI : InvW σ s0 o s) : InvW σ s0 b s := by
  simp only [MW.leW, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨hc, hn⟩, hl⟩, hr⟩, hs⟩, hp⟩ := h
  exact ⟨fun p h => hI.cst p (hc p h), fun p h => hI.nz p (hn p h), fun p h => hI.le p (hl p h),
    fun p h => hI.rle p (hr p h), fun p h => hI.same p (hs p h), fun p h => hI.ptr p (hp p h)⟩

theorem Inv.of_leM {σ : AbiLayout} {s0 : AState} {b o : MA} {s : AState} (h : leM b o = true)
    (hI : Inv σ s0 o s) : Inv σ s0 b s := by
  simp only [leM, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsp, hent⟩, hzero⟩, hslot⟩, hle⟩, hnz⟩, hzf⟩, hcst⟩, hw⟩ := h
  refine ⟨hsp ▸ hI.sp, fun p hp => hI.ent p (hent p hp), fun r hr => hI.zero r (hzero r hr),
    fun e he => hI.slot e (hslot e he), fun f hf => hI.le f (hle f hf),
    fun r hr => hI.nz r (hnz r hr), fun c hc => ?_, fun p hp => hI.cst p (hcst p hp),
    InvW.of_leW hw hI.w⟩
  rcases hzf with hzf | hzf
  · simp [hzf] at hc
  · exact hI.zf c (hzf ▸ hc)

/-! ## 2. The abstract effect of an instruction -/

/-- Drop the facts about the registers `ds` and the zero-flag fact. -/
def MA.kill (m : MA) (ds : List String) : MA :=
  { m with
    ent := m.ent.filter fun p => !ds.contains p.1
    zero := m.zero.filter fun r => !ds.contains r
    le := m.le.filter fun f => !ds.contains f.1 && !ds.contains f.2.1
    nz := m.nz.filter fun r => !ds.contains r
    zf := none
    cst := m.cst.filter fun p => !ds.contains p.1
    w := m.w.keepRegs fun x => !ds.contains x }

/-- The `le` facts after `d := y`. -/
def copyLe (d y : String) (f : String × String × Int) : Option (String × String × Int) :=
  if f.1 = y ∧ f.2.1 ≠ d then some (d, f.2.1, f.2.2)
  else if f.2.1 = y ∧ f.1 ≠ d then some (f.1, d, f.2.2)
  else none

/-- The `le` facts after `d := d + 1`. -/
def incLe (d : String) (f : String × String × Int) : Option (String × String × Int) :=
  if (f.1 = d ∨ f.2.1 = d) ∧ f.1 ≠ f.2.1 ∧ f.2.2 + 1 < 2 ^ 64 then some (f.1, f.2.1, f.2.2 + 1)
  else none

/-- The `le` facts after `d := d + n`. -/
def incLeBy (d : String) (n : Nat) (f : String × String × Int) :
    Option (String × String × Int) :=
  if (f.1 = d ∨ f.2.1 = d) ∧ f.1 ≠ f.2.1 ∧ f.2.2 + n < 2 ^ 64 then some (f.1, f.2.1, f.2.2 + n)
  else none

/-- The `le` facts after `d := d - 1`, for a nonzero `d`. -/
def decLe (d : String) (f : String × String × Int) : Option (String × String × Int) :=
  if (f.1 = d ∨ f.2.1 = d) ∧ f.1 ≠ f.2.1 then some (f.1, f.2.1, f.2.2 - 1) else none

/-- The partner and the bound of an `le` fact on `x`: `(c, B)` for a fact `(x, c, B)` or
    `(c, x, B)` with `c ≠ x`. -/
def partOf (x : String) (f : String × String × Int) : Option (String × Int) :=
  if f.1 = x ∧ f.2.1 ≠ x then some (f.2.1, f.2.2)
  else if f.2.1 = x ∧ f.1 ≠ x then some (f.1, f.2.2)
  else none

/-- The upper bound of the value of `y` that an `le` fact of `m` gives: `B - 1` for a fact
    `(y, c, B)` or `(c, y, B)` with `c` nonzero, and `B` for such a fact with another `c`. -/
def bndOf (m : MA) (y : String) (f : String × String × Int) : Option Int :=
  if f.1 = y then some (if m.nz.contains f.2.1 then f.2.2 - 1 else f.2.2)
  else if f.2.1 = y then some (if m.nz.contains f.1 then f.2.2 - 1 else f.2.2)
  else none

/-- The least upper bound of the value of `y` that the `le` facts of `m` give. -/
def ubOf (m : MA) (y : String) : Option Int := (m.le.filterMap (bndOf m y)).min?

/-- The `le` facts after `d := d + y` for a register `y ≠ d` whose value is at most `b`:
    `(d, c, B + b)` for each fact on `d` with partner `c` and bound `B`. -/
def addLeBy (d : String) (b : Int) (p : String × Int) : Option (String × String × Int) :=
  if p.2 + b < 2 ^ 64 then some (d, p.1, p.2 + b) else none

/-- The bound of `x · v + c` from a fact `x + c ≤ B`, for `1 ≤ v`: `v · B - (v - 1)` when
    `c` is nonzero, and `v · B` otherwise. -/
def mulBound (m : MA) (v : Nat) (p : String × Int) : Int :=
  if m.nz.contains p.1 then (v : Int) * p.2 - ((v : Int) - 1) else (v : Int) * p.2

/-- The `le` facts after `d := y · v`: `(d, c, mulBound m v (c, B))` for each fact
    `y + c ≤ B` with `c ≠ d` and `v · B < 2 ^ 64`. -/
def mulLe (m : MA) (d : String) (v : Nat) (p : String × Int) :
    Option (String × String × Int) :=
  if p.1 ≠ d ∧ (v : Int) * p.2 < 2 ^ 64 then some (d, p.1, mulBound m v p) else none

/-- The stack-word facts after a store of `src` at offset `e` from the entry stack
    pointer. -/
def storeSlot (σ : AbiLayout) (m : MA) (e : Int) (src : JOperand) : List (Int × String) :=
  (m.slot.filter fun q => far e q.1) ++
    match src with
    | .reg y => if inW σ e then (m.ent.filter fun p => p.1 = y).map fun p => (e, p.2) else []
    | .imm _ => []

/-- The stack-word facts after `i`. -/
def slotAfter (σ : AbiLayout) (m : MA) : JInstr 64 → List (Int × String)
  | .storeMem b off src => if b = "%rsp" then storeSlot σ m (m.sp + off) src else m.slot
  | .storeMemIdx b _ _ _ => if b = "%rsp" then [] else m.slot
  | .addToMem b _ _ => if b = "%rsp" then [] else m.slot
  | _ => m.slot

/-- The register copies: `copyOf m i = some (d, y)` when `i` writes only `d`, with the value
    `y` held before it: a register move, or an operation with a register holding `0`, or a
    shift by `0`, which keeps the value of `d`. -/
def copyOf (m : MA) : JInstr 64 → Option (String × String)
  | .mov d (.reg y) => some (d, y)
  | .add d (.reg z) => if m.zero.contains z && z != d then some (d, d) else none
  | .sub d (.reg z) => if m.zero.contains z && z != d then some (d, d) else none
  | .or_ d (.reg z) => if m.zero.contains z && z != d then some (d, d) else none
  | .xor_ d (.reg z) => if m.zero.contains z && z != d then some (d, d) else none
  | .shl d (.imm 0) => some (d, d)
  | .shr d (.imm 0) => some (d, d)
  | .sar d (.imm 0) => some (d, d)
  | _ => none

/-- The `ent` facts `i` adds. -/
def entAdd (m : MA) (i : JInstr 64) : List (String × String) :=
  match copyOf m i with
  | some (d, y) => (m.ent.filter fun p => p.1 = y).map fun p => (d, p.2)
  | none =>
    match i with
    | .loadMem d b off =>
        if b = "%rsp" then (m.slot.filter fun q => q.1 = m.sp + off).map fun q => (d, q.2)
        else []
    | _ => []

/-- The `zero` facts `i` adds. -/
def zeroAdd (m : MA) (i : JInstr 64) : List String :=
  match copyOf m i with
  | some (d, y) => if m.zero.contains y then [d] else []
  | none =>
    match i with
    | .mov d (.imm 0) => [d]
    | .xor_ d (.reg y) => if y = d then [d] else []
    | _ => []

/-- The `le` facts `i` adds. -/
def leAdd (m : MA) (i : JInstr 64) : List (String × String × Int) :=
  match copyOf m i with
  | some (d, y) => m.le.filterMap (copyLe d y)
  | none =>
    match i with
    | .add d (.imm 1) => m.le.filterMap (incLe d)
    | .add d (.reg z) =>
        if z != d then
          match m.cst.lookup z with
          | some n => m.le.filterMap (incLeBy d n)
          | none =>
              match ubOf m z with
              | some b => (m.le.filterMap (partOf d)).filterMap (addLeBy d b)
              | none => []
        else []
    | .sub d (.imm 1) => if m.nz.contains d then m.le.filterMap (decLe d) else []
    | .imulri d y v =>
        if 1 ≤ v ∧ v < 2 ^ 64 then (m.le.filterMap (partOf y)).filterMap (mulLe m d v)
        else []
    | _ => []

/-- The `cst` facts `i` adds: a copy carries the constant of its source, and a move of an
    immediate records it. -/
def cstAdd (m : MA) (i : JInstr 64) : List (String × Nat) :=
  match copyOf m i with
  | some (d, y) => (m.cst.filter fun p => p.1 = y).map fun p => (d, p.2)
  | none =>
    match i with
    | .mov d (.imm n) => [(d, n)]
    | _ => []

/-- The `nz` facts `i` adds. -/
def nzAdd (m : MA) (i : JInstr 64) : List String :=
  match copyOf m i with
  | some (d, y) => if m.nz.contains y then [d] else []
  | none => []

/-- The zero-flag fact after `i`. -/
def zfAfter : JInstr 64 → Option String
  | .cmp c (.imm 0) => some c
  | _ => none

/-- Add the `le` facts `(r, c, b)` for a register `r` holding `0` and a register `c` holding
    the entry value of a register with bound `b` in `σ`, and the `le` facts `(r, c, n)` for a
    register `r` holding `0` and a register `c` holding the constant `n`. -/
def norm (σ : AbiLayout) (m : MA) : MA :=
  { m with
    le := (m.le ++ (m.zero.flatMap fun r => m.ent.flatMap fun p =>
      σ.bounds.filterMap fun b =>
        if b.1 = p.2 ∧ r ≠ p.1 then some (r, p.1, (b.2 : Int)) else none)
      ++ m.zero.flatMap fun r => m.cst.filterMap fun p =>
        if r ≠ p.1 then some (r, p.1, (p.2 : Int)) else none).eraseDups }

/-- The stack words a store of `i` leaves unchanged, at the stack offset `sp`: a store through
    `%rsp` at a displacement keeps the words far from its target; an indexed or accumulating
    store through `%rsp` keeps none; a store through another base keeps the words of the frame
    range, and the other instructions keep every word. -/
def wordKeep (sp : Int) : JInstr 64 → Int → Bool
  | .storeMem b off _, e => b != "%rsp" || far (sp + off) e
  | .addToMem b _ _, _ => b != "%rsp"
  | .storeMemIdx b _ _ _, _ => b != "%rsp"
  | _, _ => true

/-- The fact that the stack words at `e` and `e'` sum to at most `B`, with the lesser offset
    first: a sum has one form, so the meet at a loop head compares the facts of its two
    edges whatever the order of the stores that made them. -/
def leCanon (e e' B : Int) : Int × Int × Int := if e ≤ e' then (e, e', B) else (e', e, B)

/-- The sums the store of the word `n` at offset `e` starts: with `n = 0`, the sum with each
    stack word of `kw` holding a positive constant; with `n > 0`, the sum with each stack word
    of `kw` holding `0`. These are the entry states of a loop with an index and a count. -/
def seedLe (e : Int) (n : Nat) (kw : List (Int × Nat)) : List (Int × Int × Int) :=
  (if n = 0 then (kw.filter fun p => 0 < p.2).map fun p => leCanon e p.1 p.2 else [])
    ++ (if 0 < n then (kw.filter fun p => p.2 = 0).map fun p => leCanon p.1 e n else [])

/-- The stack-word facts a store of the immediate `n` at offset `e` adds. -/
def genStoreImm (m : MA) (e : Int) (n : Nat) : MW :=
  { cst := [(e, n)]
    le := seedLe e n (m.w.cst.filter fun p => far e p.1) }

/-- The stack-word facts a store of the register `y` at offset `e` adds. -/
def genStoreReg (m : MA) (e : Int) (y : String) : MW :=
  { cst := (m.cst.filter fun p => p.1 = y).map fun p => (e, p.2)
    nz := if m.nz.contains y then [e] else []
    le := ((m.w.rle.filter fun f => f.1 = y && far e f.2.1).map fun f => leCanon e f.2.1 f.2.2)
      ++ (m.cst.filter fun p => p.1 = y).flatMap fun p =>
        seedLe e p.2 (m.w.cst.filter fun q => far e q.1)
    same := [(y, e)] }

/-- The `rle` fact of a load `d` of the stack word `e`, from a sum over that word. -/
def loadLe (d : String) (e : Int) (f : Int × Int × Int) : Option (String × Int × Int) :=
  if f.1 = e then some (d, f.2.1, f.2.2)
  else if f.2.1 = e then some (d, f.1, f.2.2)
  else none

/-- The upper bounds, exclusive, on the value of the register `x` that the facts of `m` give:
    `B` for a fact `x + c ≤ B` with `c` a nonzero stack word or register, and `n + 1` for a
    register holding the constant `n`. -/
def idxBounds (m : MA) (x : String) : List Nat :=
  ((m.w.rle.filter fun f => f.1 = x && m.w.nz.contains f.2.1).map fun f => f.2.2.toNat)
    ++ ((m.le.filter fun f => f.1 = x && m.nz.contains f.2.1).map fun f => f.2.2.toNat)
    ++ (m.cst.filter fun p => p.1 = x).map fun p => p.2 + 1

/-- The constant value of the operand `src` under the facts of `m`. -/
def cstOf (m : MA) : JOperand → Option Nat
  | .imm n => some n
  | .reg y => m.cst.lookup y

/-- The `rle` facts after `d := d + src`: a constant added to `d` raises the bound of each sum
    over `d`, and a constant `d` plus a register `z` gives `d` the sums over `z` raised by
    that constant. The second is the index `C + k` of a loop index `k`. -/
def addRle (m : MA) (d : String) (src : JOperand) : List (String × Int × Int) :=
  (match cstOf m src with
    | some k => (m.w.rle.filter fun f => f.1 = d && decide (f.2.2 + (k : Int) < 2 ^ 64)).map
        fun f => (d, f.2.1, f.2.2 + (k : Int))
    | none => [])
  ++ match src with
    | .reg z =>
      match m.cst.lookup d with
      | some a => (m.w.rle.filter fun f => f.1 = z && decide (f.2.2 + (a : Int) < 2 ^ 64)).map
          fun f => (d, f.2.1, f.2.2 + (a : Int))
      | none => []
    | .imm _ => []

/-- The facts of `i` on stack words and on registers computed from them: a store through
    `%rsp`, a load through `%rsp`, a step of a register by one, and the computation
    `lea d (b, x, 8)` of a pointer from a region base and a bounded index. -/
def genW (σ : AbiLayout) (m : MA) : JInstr 64 → MW
  | .storeMem b off src =>
    if b = "%rsp" ∧ inW σ (m.sp + off) = true then
      match src with
      | .imm n => genStoreImm m (m.sp + off) n
      | .reg y => genStoreReg m (m.sp + off) y
    else {}
  | .loadMem d b off =>
    if b = "%rsp" ∧ inW σ (m.sp + off) = true then
      { rle := m.w.le.filterMap (loadLe d (m.sp + off))
        same := [(d, m.sp + off)] }
    else {}
  | .add d src => { rle := addRle m d src }
  | .sub d src =>
    if src = .imm 1 ∧ m.nz.contains d = true then
      { rle := (m.w.rle.filter fun f => f.1 = d).map fun f => (d, f.2.1, f.2.2 - 1) }
    else {}
  | .lea d b x sc k =>
    if sc = 8 ∧ k = 0 then
      { ptr := (m.ent.filter fun p => p.1 = b).flatMap fun p =>
          (idxBounds m x).map fun n => (d, p.2, n) }
    else {}
  | _ => {}

/-- The facts on stack words after `i`. -/
def stepW (σ : AbiLayout) (m : MA) (i : JInstr 64) : MW :=
  (genW σ m i).union ((m.kill (dstRegs i)).w.keepWords (wordKeep m.sp i))

/-- The `cst` facts of a load of a stack word holding a constant, and of an addition, a
    subtraction without borrow and a right shift of constants. -/
def wCstAdd (m : MA) : JInstr 64 → List (String × Nat)
  | .loadMem d b off =>
    if b = "%rsp" then (m.w.cst.filter fun p => p.1 = m.sp + off).map fun p => (d, p.2) else []
  | .add d src =>
    match m.cst.lookup d, cstOf m src with
    | some a, some k => [(d, a + k)]
    | _, _ => []
  | .sub d src =>
    match m.cst.lookup d, cstOf m src with
    | some a, some k => if k ≤ a then [(d, a - k)] else []
    | _, _ => []
  | .shr d src =>
    match m.cst.lookup d, src with
    | some a, .imm k => if k < 64 then [(d, (a % 2 ^ 64) >>> k)] else []
    | _, _ => []
  | _ => []

/-- The `nz` facts of a load of a nonzero stack word. -/
def wNzAdd (m : MA) : JInstr 64 → List String
  | .loadMem d b off => if b = "%rsp" ∧ m.w.nz.contains (m.sp + off) = true then [d] else []
  | _ => []

/-- The abstract state after an instruction that does not write `%rsp`. -/
def step1 (σ : AbiLayout) (m : MA) (i : JInstr 64) : MA :=
  let m0 := m.kill (dstRegs i)
  { sp := m.sp
    ent := entAdd m i ++ m0.ent
    zero := zeroAdd m i ++ m0.zero
    slot := slotAfter σ m i
    le := leAdd m i ++ m0.le
    nz := wNzAdd m i ++ (nzAdd m i ++ m0.nz)
    zf := zfAfter i
    cst := wCstAdd m i ++ (cstAdd m i ++ m0.cst)
    w := stepW σ m i }

/-- **The abstract effect of an instruction**: the frame adjustment `lea k(%rsp), %rsp`
    moves the stack offset; another write of `%rsp` is refused. -/
def trans (σ : AbiLayout) (m : MA) (i : JInstr 64) : Option MA :=
  match rspShift i with
  | some k => some { m.kill ["%rsp"] with sp := m.sp + k }
  | none => if (dstRegs i).contains "%rsp" then none else some (norm σ (step1 σ m i))

/-- The abstract state on an outcome of a branch on `c`. -/
def jccOut (m : MA) (c : Condt) (taken : Bool) : MA :=
  match m.zf with
  | some r =>
      if (c == .ne && taken) || (c == .e && !taken) then
        { m with
          nz := r :: m.nz
          w := { m.w with nz := (m.w.same.filter fun p => p.1 = r).map (·.2) ++ m.w.nz } }
      else m
  | none => m

/-! ## 3. The stores -/

/-- A store through `b` at displacement `off` writes a word of a pointer region. -/
def constCell (σ : AbiLayout) (m : MA) (b : String) (off : Int) : Bool :=
  m.ent.any fun p => p.1 == b && σ.regions.any fun q =>
    q.1 == p.2 && decide (0 ≤ off) && off % 8 == 0 && decide (off / 8 < q.2)

/-- An indexed store through `b` with index `x` and scale `8` writes a word of a pointer
    region. -/
def idxCell (σ : AbiLayout) (m : MA) (b x : String) : Bool :=
  m.ent.any fun p => p.1 == b && σ.regions.any fun q => q.1 == p.2 && m.le.any fun f =>
    f.1 == x && ((m.nz.contains f.2.1 && decide (f.2.2 ≤ q.2)) || decide (f.2.2 < q.2))

/-- A store through `b` at displacement `0` writes a word of a pointer region: `b` holds a
    pointer into the region, with an index below its length. -/
def ptrCell (σ : AbiLayout) (m : MA) (b : String) (off : Int) : Bool :=
  off == 0 && m.w.ptr.any fun p => p.1 == b && σ.regions.any fun q =>
    q.1 == p.2.1 && decide (p.2.2 ≤ q.2)

/-- A store of `i` through a base other than `%rsp` writes a word of a pointer region. -/
def cellAddrOK (σ : AbiLayout) (m : MA) : JInstr 64 → Bool
  | .storeMem b off _ => b == "%rsp" || constCell σ m b off || ptrCell σ m b off
  | .addToMem b off _ => b == "%rsp" || constCell σ m b off || ptrCell σ m b off
  | .storeMemIdx b x sc _ => b == "%rsp" || (sc == 8 && idxCell σ m b x)
  | _ => true

/-- Every frame word `o ∈ F` lies, at the stack offset of `m`, inside the frame range. -/
def frameOK (σ : AbiLayout) (F : List Int) (m : MA) : Bool := F.all fun o => inW σ (m.sp + o)

/-- The store check of `i`: a store through another base writes a pointer region, and the
    frame words lie in the frame range. -/
def safeW (σ : AbiLayout) (F : List Int) (m : MA) (i : JInstr 64) : Bool :=
  cellAddrOK σ m i && (!sepWrite i || frameOK σ F m)

/-! ## 4. The certificate check -/

/-- The certificate assigns index `s` an abstract state below `o`. -/
def succOkM (M : Array (Option MA)) (s : Nat) (o : MA) : Bool :=
  match M.getD s none with
  | some b => leM b o
  | none => false

/-- The check at index `pc`. -/
def checkAtM (σ : AbiLayout) (F : List Int) (prog : List RInstr) (M : Array (Option MA))
    (pc : Nat) : Bool :=
  match M.getD pc none with
  | none => true
  | some m =>
    match prog[pc]? with
    | some (.op i) =>
        safeW σ F m i && match trans σ m i with
          | some o => succOkM M (pc + 1) o
          | none => false
    | some (.jcc cc t) =>
        match condtOfNibble cc with
        | some c => succOkM M t (jccOut m c true) && succOkM M (pc + 1) (jccOut m c false)
        | none => false
    | some .ret => true
    | some _ => false
    | none => true

/-- The stack words of the frame range holding a parameter of `σ` that passes `P` at entry:
    `(8 k, a.reg)` for a parameter `a` with the carrier name `stackArgReg k`. -/
def stackSlots (σ : AbiLayout) (P : AbiArg → Bool) : List (Int × String) :=
  (List.range (σ.frameHi.toNat / 8 + 1)).flatMap fun k =>
    (σ.args.filter fun a => a.reg == stackArgReg k && P a && inW σ (8 * (k : Int))).map
      fun a => (8 * (k : Int), a.reg)

/-- The abstract entry state: each parameter register holds its entry value, and each stack
    word holding a stack parameter holds the entry value of its carrier name. -/
def init (σ : AbiLayout) : MA :=
  norm σ
    { sp := 0
      ent := σ.args.map fun a => (a.reg, a.reg)
      zero := []
      slot := stackSlots σ fun _ => true
      le := []
      nz := []
      zf := none }

/-- **The certificate check**: the entry index is below `init σ` and every index passes
    `checkAtM`. -/
def memCheck (σ : AbiLayout) (F : List Int) (prog : List RInstr) (M : Array (Option MA)) :
    Bool :=
  succOkM M 0 (init σ) && (List.range prog.length).all (checkAtM σ F prog M)

/-! ## 5. Inference -/

/-- The facts common to two abstract states at one stack offset. -/
def meetM (a b : MA) : MA :=
  if a.sp = b.sp then
    { sp := a.sp
      ent := a.ent.filter b.ent.contains
      zero := a.zero.filter b.zero.contains
      slot := a.slot.filter b.slot.contains
      le := a.le.filter b.le.contains
      nz := a.nz.filter b.nz.contains
      zf := if a.zf = b.zf then a.zf else none
      cst := a.cst.filter b.cst.contains
      w := MW.meet a.w b.w }
  else a

/-- Meet `o` into the certificate at index `s`, reporting a change. -/
def meetIntoM (M : Array (Option MA)) (s : Nat) (o : MA) : Array (Option MA) × Bool :=
  if s < M.size then
    match M.getD s none with
    | none => (M.set! s (some o), true)
    | some a => let a' := meetM a o; (M.set! s (some a'), a' != a)
  else (M, false)

/-- One forward sweep over the program. -/
def sweepM (σ : AbiLayout) (prog : List RInstr) (M : Array (Option MA)) :
    Array (Option MA) × Bool :=
  (List.range prog.length).foldl (fun (acc : Array (Option MA) × Bool) pc =>
    match acc.1.getD pc none, prog[pc]? with
    | some m, some (.op i) =>
        match trans σ m i with
        | some o => let r := meetIntoM acc.1 (pc + 1) o; (r.1, acc.2 || r.2)
        | none => acc
    | some m, some (.jcc cc t) =>
        match condtOfNibble cc with
        | some c =>
            let r1 := meetIntoM acc.1 t (jccOut m c true)
            let r2 := meetIntoM r1.1 (pc + 1) (jccOut m c false)
            (r2.1, acc.2 || r1.2 || r2.2)
        | none => acc
    | _, _ => acc) (M, false)

/-- Sweeps until no change, at most `n` times. -/
def fixM (σ : AbiLayout) (prog : List RInstr) : Nat → Array (Option MA) → Array (Option MA)
  | 0, M => M
  | n + 1, M =>
    let r := sweepM σ prog M
    if r.2 then fixM σ prog n r.1 else r.1

/-- The inferred certificate of the region analysis. -/
def inferM (σ : AbiLayout) (prog : List RInstr) : Array (Option MA) :=
  fixM σ prog (prog.length + 2) ((Array.replicate prog.length none).set! 0 (some (init σ)))

/-! ## 6. The trimmed constant-time certificate -/

/-- The stack offsets of the certificate `M` at the indices that store through a base
    other than `%rsp`. -/
def storeSps (prog : List RInstr) (M : Array (Option MA)) : List Int :=
  (List.range prog.length).filterMap fun pc =>
    match prog[pc]?, M.getD pc none with
    | some (RInstr.op i), some m => if sepWrite i then some m.sp else none
    | _, _ => none

/-- The certificate `A` with each frame word kept when it lies inside the frame range of
    `σ` at every stack offset of `sps`. -/
def trimCert (σ : AbiLayout) (sps : List Int) (A : Array (Option PubA)) :
    Array (Option PubA) :=
  A.map (Option.map fun a =>
    { a with cells := a.cells.filter (fun o => sps.all (fun sp => inW σ (sp + o))) })

/-! ## 7. Soundness of the region analysis -/

section Soundness

variable {σ : AbiLayout} {s0 : AState}

theorem eval_mov_reg (s : AState) (d y : String) :
    (evalInstrA s (.mov d (.reg y))).regs d = s.regs y := by
  simp [evalInstrA, evalInstr, JState.setReg, x86_MOV, AState.view]

theorem eval_mov_imm (s : AState) (d : String) (n : Nat) :
    (evalInstrA s (.mov d (.imm n))).regs d = BitVec.ofNat 64 n := by
  simp [evalInstrA, evalInstr, JState.setReg, x86_MOV, AState.view]

theorem eval_loadMem (s : AState) (d b : String) (off : Int) :
    (evalInstrA s (.loadMem d b off)).regs d
      = read64 s.mem (s.regs b + BitVec.ofInt 64 off) := by
  simp [evalInstrA, evalInstr, JState.setReg, x86_MOV, AState.view, JState.load]

theorem eval_add_one (s : AState) (d : String) :
    (evalInstrA s (.add d (.imm 1))).regs d = s.regs d + 1 := by
  simp [evalInstrA, evalInstr, JState.writeB5W, x86_ADD, rflags_of_aluop, AState.view]

theorem eval_add_reg (s : AState) (d y : String) :
    (evalInstrA s (.add d (.reg y))).regs d = s.regs d + s.regs y := by
  simp [evalInstrA, evalInstr, JState.writeB5W, x86_ADD, rflags_of_aluop, AState.view]

theorem toNat_add_ofNat_of {x : BitVec 64} {n : Nat} (h : x.toNat + n < 2 ^ 64)
    (hn : n < 2 ^ 64) : (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  omega

theorem mem_of_lookup_cst {l : List (String × Nat)} {k : String} {v : Nat}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (k == a) = false := by simp [hk]
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem eval_sub_one (s : AState) (d : String) :
    (evalInstrA s (.sub d (.imm 1))).regs d = s.regs d - 1 := by
  simp [evalInstrA, evalInstr, JState.writeB5W, x86_SUB, AState.view]

theorem eval_cmp_zero (s : AState) (c : String) :
    (evalInstrA s (.cmp c (.imm 0))).view.condB .e = decide (s.regs c = 0) := by
  simp [evalInstrA, evalInstr, JState.writeB5, x86_CMP, x86_SUB, AState.view, JState.condB,
    JState.flagB, x86_eval_cond, ZF_of_word]
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)
  · intro h
    simp [h]

theorem mem_of_writeAddr_none {s : AState} {i : JInstr 64} (h : writeAddr s i = none) :
    (evalInstrA s i).mem = s.mem := by
  simp [evalInstrA, h]

theorem ofInt_add_assoc (p : BitVec 64) (a b : Int) :
    p + BitVec.ofInt 64 a + BitVec.ofInt 64 b = p + BitVec.ofInt 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofInt_add]

theorem toNat_pos_of_ne {x : BitVec 64} (h : x ≠ 0) : 0 < x.toNat := by
  rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
  · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
  · exact h0

/-- A store that `cellAddrOK` accepts, through a base other than `%rsp`, writes a word of a
    pointer region of `σ`. -/
theorem cell_of_cellAddrOK {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s)
    (hc : cellAddrOK σ m i = true) (hfw : frameWrite i = false) {a : BitVec 64}
    (ha : writeAddr s i = some a) :
    ∃ q ∈ σ.regions, ∃ k, k < q.2 ∧ a = s0.regs q.1 + BitVec.ofNat 64 (8 * k) := by
  have hconst : ∀ b off, (constCell σ m b off || ptrCell σ m b off) = true →
      ∃ q ∈ σ.regions, ∃ k, k < q.2 ∧ s.regs b + BitVec.ofInt 64 off
        = s0.regs q.1 + BitVec.ofNat 64 (8 * k) := by
    intro b off h
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · simp only [constCell, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      obtain ⟨p, hp, rfl, q, hq, ⟨⟨hq1, h0⟩, h8⟩, hlt⟩ := h
      refine ⟨q, hq, (off / 8).toNat, by omega, ?_⟩
      rw [hI.ent p hp, ← hq1]
      congr 1
      generalize hk : (off / 8).toNat = k
      have h' : off = ((8 * k : Nat) : Int) := by omega
      subst h'
      rw [BitVec.ofInt_natCast]
    · simp only [ptrCell, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      obtain ⟨rfl, p, hp, rfl, q, hq, hq1, hle⟩ := h
      obtain ⟨j, hj, hr⟩ := hI.w.ptr p hp
      refine ⟨q, hq, j, by omega, ?_⟩
      rw [hr, hq1]
      simp
  cases i with
  | storeMem b off src =>
    simp only [frameWrite, beq_eq_false_iff_ne, ne_eq] at hfw
    simp only [cellAddrOK, Bool.or_eq_true, beq_iff_eq, hfw, false_or] at hc
    simp only [writeAddr, Option.some.injEq] at ha
    subst ha
    exact hconst b off (by simpa only [Bool.or_eq_true] using hc)
  | addToMem b off src =>
    simp only [frameWrite, beq_eq_false_iff_ne, ne_eq] at hfw
    simp only [cellAddrOK, Bool.or_eq_true, beq_iff_eq, hfw, false_or] at hc
    simp only [writeAddr, Option.some.injEq] at ha
    subst ha
    exact hconst b off (by simpa only [Bool.or_eq_true] using hc)
  | storeMemIdx b x sc src =>
    simp only [frameWrite, beq_eq_false_iff_ne, ne_eq] at hfw
    simp only [cellAddrOK, Bool.or_eq_true, beq_iff_eq, hfw, false_or, Bool.and_eq_true]
      at hc
    obtain ⟨rfl, hc⟩ := hc
    simp only [writeAddr, Option.some.injEq] at ha
    subst ha
    simp only [idxCell, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
      List.contains_iff_mem, decide_eq_true_eq] at hc
    obtain ⟨p, hp, rfl, q, hq, hq1, f, hf, rfl, hb⟩ := hc
    have hle := hI.le f hf
    refine ⟨q, hq, (s.regs f.1).toNat, ?_, ?_⟩
    · rcases hb with ⟨hnz, hB⟩ | hB
      · have := toNat_pos_of_ne (hI.nz _ hnz)
        omega
      · omega
    · rw [hI.ent p hp, ← hq1, BitVec.ofInt_natCast]
  | _ => simp [writeAddr] at ha

/-- A store that `cellAddrOK` accepts, through a base other than `%rsp`, writes a word
    disjoint from every stack word in the frame range of `σ`. -/
theorem disj_of_cellAddrOK {m : MA} {s : AState} {i : JInstr 64} (hR : σ.Regions s0)
    (hI : Inv σ s0 m s) (hc : cellAddrOK σ m i = true) (hfw : frameWrite i = false)
    {a : BitVec 64} (ha : writeAddr s i = some a) {o : Int} (ho : inW σ o = true) :
    Disjoint8 a (s0.regs "%rsp" + BitVec.ofInt 64 o) := by
  obtain ⟨q, hq, k, hk, rfl⟩ := cell_of_cellAddrOK hI hc hfw ha
  simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at ho
  exact (hR.2.2.1 q hq k hk o ho.1 ho.2).symm

/-- **A checked step satisfies the separation condition.** -/
theorem frameSep_of_safeW {F : List Int} {m : MA} {s : AState} {i : JInstr 64}
    (hR : σ.Regions s0) (hI : Inv σ s0 m s) (hs : safeW σ F m i = true) : FrameSep F s i := by
  intro hfw a ha o ho
  simp only [safeW, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hs
  obtain ⟨hc, hF⟩ := hs
  have hsw := sepWrite_of_writeAddr ha hfw
  rcases hF with hF | hF
  · simp [hsw] at hF
  · simp only [frameOK, List.all_eq_true] at hF
    rw [hI.sp, ofInt_add_assoc]
    exact disj_of_cellAddrOK hR hI hc hfw ha (hF o ho)

theorem regs_ne {s : AState} {i : JInstr 64} {d x : String} (hd : dstRegs i = [d])
    (hx : x ≠ d) : (evalInstrA s i).regs x = s.regs x :=
  evalInstrA_regs_of_not_dst _ _ _ (by simp [hd, hx])

theorem copyOf_sound {m : MA} {s : AState} {i : JInstr 64} {d y : String}
    (hI : Inv σ s0 m s) (h : copyOf m i = some (d, y)) :
    dstRegs i = [d] ∧ (evalInstrA s i).regs d = s.regs y := by
  have hz : ∀ z d', (m.zero.contains z && z != d') = true → s.regs z = 0 := by
    intro z d' hz
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hz
    exact hI.zero z hz.1
  cases i with
  | mov d' src =>
    cases src with
    | reg y' =>
      simp only [copyOf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, eval_mov_reg _ _ _⟩
    | imm n => simp [copyOf] at h
  | add d' src =>
    cases src with
    | reg z =>
      simp only [copyOf] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp [evalInstrA, evalInstr, JState.writeB5W, x86_ADD, rflags_of_aluop, AState.view,
          hz _ _ hc]
      · simp at h
    | imm n => simp [copyOf] at h
  | sub d' src =>
    cases src with
    | reg z =>
      simp only [copyOf] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp [evalInstrA, evalInstr, JState.writeB5W, x86_SUB, AState.view, hz _ _ hc]
      · simp at h
    | imm n => simp [copyOf] at h
  | or_ d' src =>
    cases src with
    | reg z =>
      simp only [copyOf] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp [evalInstrA, evalInstr, JState.writeB5W, x86_OR, rflags_of_bwop, AState.view,
          hz _ _ hc]
      · simp at h
    | imm n => simp [copyOf] at h
  | xor_ d' src =>
    cases src with
    | reg z =>
      simp only [copyOf] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp [evalInstrA, evalInstr, JState.writeB5W, x86_XOR, rflags_of_bwop, AState.view,
          hz _ _ hc]
      · simp at h
    | imm n => simp [copyOf] at h
  | shl d' src =>
    cases src with
    | reg z => simp [copyOf] at h
    | imm n =>
      cases n with
      | zero =>
        simp only [copyOf, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp [evalInstrA, evalInstr, JState.writeB5W, x86_SHL, shiftCount, rflags_None,
          AState.view]
      | succ n => simp [copyOf] at h
  | shr d' src =>
    cases src with
    | reg z => simp [copyOf] at h
    | imm n =>
      cases n with
      | zero =>
        simp only [copyOf, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp [evalInstrA, evalInstr, JState.writeB5W, x86_SHR, shiftCount, rflags_None,
          AState.view]
      | succ n => simp [copyOf] at h
  | sar d' src =>
    cases src with
    | reg z => simp [copyOf] at h
    | imm n =>
      cases n with
      | zero =>
        simp only [copyOf, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp [evalInstrA, evalInstr, JState.writeB5W, x86_SAR, shiftCount, rflags_None,
          AState.view]
      | succ n => simp [copyOf] at h
  | _ => simp [copyOf] at h

theorem entAdd_sound {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s) :
    ∀ p ∈ entAdd m i, (evalInstrA s i).regs p.1 = s0.regs p.2 := by
  intro p hp
  unfold entAdd at hp
  split at hp
  · rename_i d y hcp
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
    obtain ⟨q, ⟨hq, hy⟩, rfl⟩ := hp
    dsimp only
    rw [(copyOf_sound hI hcp).2, ← hy, hI.ent q hq]
  · cases i with
    | loadMem d b off =>
      simp only at hp
      split at hp
      · rename_i hb
        subst hb
        simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
        obtain ⟨q, ⟨hq, he⟩, rfl⟩ := hp
        dsimp only
        rw [eval_loadMem, hI.sp, ofInt_add_assoc, ← he]
        exact (hI.slot q hq).2
      · simp at hp
    | _ => simp at hp

theorem zeroAdd_sound {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s) :
    ∀ r ∈ zeroAdd m i, (evalInstrA s i).regs r = 0 := by
  intro r hr
  unfold zeroAdd at hr
  split at hr
  · rename_i d y hcp
    simp only [List.contains_iff_mem] at hr
    split at hr
    · rename_i hy
      simp only [List.mem_singleton] at hr
      subst hr
      rw [(copyOf_sound hI hcp).2, hI.zero y hy]
    · simp at hr
  · cases i with
    | mov d src =>
      cases src with
      | reg y => simp at hr
      | imm n =>
        cases n with
        | zero =>
          simp only [List.mem_singleton] at hr
          subst hr
          rw [eval_mov_imm]
          rfl
        | succ n => simp at hr
    | xor_ d src =>
      cases src with
      | reg y =>
        simp only at hr
        split at hr
        · rename_i hy
          subst hy
          simp only [List.mem_singleton] at hr
          subst hr
          simp [evalInstrA, evalInstr, JState.writeB5W, x86_XOR, rflags_of_bwop, AState.view]
        · simp at hr
      | imm n => simp at hr
    | _ => simp at hr

theorem nzAdd_sound {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s) :
    ∀ r ∈ nzAdd m i, (evalInstrA s i).regs r ≠ 0 := by
  intro r hr
  unfold nzAdd at hr
  split at hr
  · rename_i d y hcp
    simp only [List.contains_iff_mem] at hr
    split at hr
    · rename_i hy
      simp only [List.mem_singleton] at hr
      subst hr
      rw [(copyOf_sound hI hcp).2]
      exact hI.nz y hy
    · simp at hr
  · simp at hr

theorem cstAdd_sound {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s) :
    ∀ p ∈ cstAdd m i, (evalInstrA s i).regs p.1 = BitVec.ofNat 64 p.2 := by
  intro p hp
  unfold cstAdd at hp
  split at hp
  · rename_i d y hcp
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
    obtain ⟨q, ⟨hq, hqy⟩, rfl⟩ := hp
    rw [(copyOf_sound hI hcp).2, ← hqy]
    exact hI.cst q hq
  · cases i with
    | mov d src =>
      cases src with
      | reg y => simp at hp
      | imm n =>
        simp only [List.mem_singleton] at hp
        subst hp
        exact eval_mov_imm s d n
    | _ => simp at hp

theorem zfAfter_sound {s : AState} {i : JInstr 64} :
    ∀ c, zfAfter i = some c → (evalInstrA s i).view.condB .e
      = decide ((evalInstrA s i).regs c = 0) := by
  intro c hc
  cases i with
  | cmp a src =>
    cases src with
    | reg y => simp [zfAfter] at hc
    | imm n =>
      cases n with
      | zero =>
        simp only [zfAfter, Option.some.injEq] at hc
        subst hc
        rw [eval_cmp_zero, evalInstrA_regs_of_not_dst _ _ _ (by simp [dstRegs])]
      | succ n => simp [zfAfter] at hc
  | _ => simp [zfAfter] at hc

theorem toNat_add_one_of {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add]
  rw [show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem toNat_sub_one_of {x : BitVec 64} (h : x ≠ 0) : (x - 1).toNat = x.toNat - 1 := by
  have := toNat_pos_of_ne h
  have := x.isLt
  rw [BitVec.toNat_sub]
  rw [show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem eval_imulri (s : AState) (d y : String) (v : Nat) :
    (evalInstrA s (.imulri d y v)).regs d = s.regs y * BitVec.ofNat 64 v := by
  simp [evalInstrA, evalInstr, JState.writeB5W, x86_IMULt, rflags_of_mul, AState.view]

/-- A fact on `x` with partner `c` bounds the sum of the values of `x` and `c`. -/
theorem partOf_sound {m : MA} {s : AState} (hI : Inv σ s0 m s) {x : String}
    {f : String × String × Int} (hf : f ∈ m.le) {p : String × Int} (h : partOf x f = some p) :
    p.1 ≠ x ∧ ((s.regs x).toNat : Int) + (s.regs p.1).toNat ≤ p.2 := by
  have hle := hI.le f hf
  unfold partOf at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2⟩ := hc
    exact ⟨h2, h1 ▸ hle⟩
  · split at h
    · rename_i _ hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := hc
      refine ⟨h2, ?_⟩
      rw [← h1]
      dsimp only
      omega
    · simp at h

/-- A bound of `bndOf` bounds the value of `y`. -/
theorem bndOf_sound {m : MA} {s : AState} (hI : Inv σ s0 m s) {y : String}
    {f : String × String × Int} (hf : f ∈ m.le) {b : Int} (h : bndOf m y f = some b) :
    ((s.regs y).toNat : Int) ≤ b := by
  have hle := hI.le f hf
  unfold bndOf at h
  split at h
  · rename_i h1
    simp only [Option.some.injEq] at h
    subst h1
    split at h
    · rename_i hnz
      have := toNat_pos_of_ne (hI.nz _ (List.contains_iff_mem.mp hnz))
      omega
    · omega
  · split at h
    · rename_i _ h1
      simp only [Option.some.injEq] at h
      subst h1
      split at h
      · rename_i hnz
        have := toNat_pos_of_ne (hI.nz _ (List.contains_iff_mem.mp hnz))
        omega
      · omega
    · simp at h

/-- The bound `ubOf m y` bounds the value of `y`. -/
theorem ubOf_sound {m : MA} {s : AState} (hI : Inv σ s0 m s) {y : String} {b : Int}
    (h : ubOf m y = some b) : ((s.regs y).toNat : Int) ≤ b := by
  have hm := List.min?_mem h
  obtain ⟨f, hf, hfb⟩ := List.mem_filterMap.mp hm
  exact bndOf_sound hI hf hfb

theorem leAdd_sound {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s) :
    ∀ f ∈ leAdd m i, (((evalInstrA s i).regs f.1).toNat : Int)
      + ((evalInstrA s i).regs f.2.1).toNat ≤ f.2.2 := by
  intro f hf
  unfold leAdd at hf
  split at hf
  · rename_i d y hcp
    obtain ⟨hd, hv⟩ := copyOf_sound hI hcp
    simp only [List.mem_filterMap] at hf
    obtain ⟨g, hg, hgf⟩ := hf
    have hle := hI.le g hg
    unfold copyLe at hgf
    split at hgf
    · rename_i h
      simp only [Option.some.injEq] at hgf
      subst hgf
      dsimp only
      rw [hv, regs_ne hd h.2, ← h.1]
      exact hle
    · split at hgf
      · rename_i _ h
        simp only [Option.some.injEq] at hgf
        subst hgf
        dsimp only
        rw [hv, regs_ne hd h.2, ← h.1]
        exact hle
      · simp at hgf
  · cases i with
    | add d src =>
      cases src with
      | reg y =>
        simp only [bne_iff_ne, ne_eq, ite_not] at hf
        split at hf
        · simp at hf
        · rename_i hyd
          split at hf
          · rename_i n hn
            simp only [List.mem_filterMap] at hf
            obtain ⟨g, hg, hgf⟩ := hf
            have hle := hI.le g hg
            have hyv : s.regs y = BitVec.ofNat 64 n := hI.cst (y, n) (mem_of_lookup_cst hn)
            have hd : dstRegs (JInstr.add (w := 64) d (.reg y)) = [d] := rfl
            unfold incLeBy at hgf
            split at hgf
            · rename_i h
              simp only [Option.some.injEq] at hgf
              subst hgf
              dsimp only
              obtain ⟨hor, hne, hB⟩ := h
              have h0a := (s.regs g.1).isLt
              have h0b := (s.regs g.2.1).isLt
              have hn64 : n < 2 ^ 64 := by omega
              rcases hor with h1 | h1
              · subst h1
                rw [eval_add_reg, regs_ne hd (Ne.symm hne), hyv,
                  toNat_add_ofNat_of (by omega) hn64]
                push_cast
                omega
              · subst h1
                rw [eval_add_reg, regs_ne hd hne, hyv, toNat_add_ofNat_of (by omega) hn64]
                push_cast
                omega
            · simp at hgf
          · split at hf
            · rename_i b hb
              have hyb := ubOf_sound hI hb
              simp only [List.mem_filterMap] at hf
              obtain ⟨p, ⟨g, hg, hgp⟩, hpf⟩ := hf
              obtain ⟨hcd, hle⟩ := partOf_sound hI hg hgp
              have hd : dstRegs (JInstr.add (w := 64) d (.reg y)) = [d] := rfl
              unfold addLeBy at hpf
              split at hpf
              · rename_i hB
                simp only [Option.some.injEq] at hpf
                subst hpf
                dsimp only
                have hC0 : (0 : Int) ≤ (s.regs p.1).toNat := Int.natCast_nonneg _
                have hsum : (s.regs d + s.regs y).toNat = (s.regs d).toNat + (s.regs y).toNat := by
                  rw [BitVec.toNat_add]
                  apply Nat.mod_eq_of_lt
                  omega
                rw [eval_add_reg, regs_ne hd hcd, hsum]
                push_cast
                omega
              · simp at hpf
            · simp at hf
      | imm n =>
        cases n with
        | zero => simp at hf
        | succ n =>
          cases n with
          | succ n => simp at hf
          | zero =>
            simp only [List.mem_filterMap] at hf
            obtain ⟨g, hg, hgf⟩ := hf
            have hle := hI.le g hg
            have hd : dstRegs (JInstr.add (w := 64) d (.imm 1)) = [d] := rfl
            unfold incLe at hgf
            split at hgf
            · rename_i h
              simp only [Option.some.injEq] at hgf
              subst hgf
              dsimp only
              obtain ⟨hor, hne, hB⟩ := h
              rcases hor with h1 | h1
              · subst h1
                rw [eval_add_one, regs_ne hd (Ne.symm hne), toNat_add_one_of (by omega)]
                push_cast
                omega
              · subst h1
                rw [eval_add_one, regs_ne hd hne, toNat_add_one_of (by omega)]
                push_cast
                omega
            · simp at hgf
    | sub d src =>
      cases src with
      | reg y => simp at hf
      | imm n =>
        cases n with
        | zero => simp at hf
        | succ n =>
          cases n with
          | succ n => simp at hf
          | zero =>
            simp only [List.contains_iff_mem] at hf
            split at hf
            · rename_i hnz
              simp only [List.mem_filterMap] at hf
              obtain ⟨g, hg, hgf⟩ := hf
              have hle := hI.le g hg
              have h0 := toNat_pos_of_ne (hI.nz d hnz)
              have hd : dstRegs (JInstr.sub (w := 64) d (.imm 1)) = [d] := rfl
              unfold decLe at hgf
              split at hgf
              · rename_i h
                simp only [Option.some.injEq] at hgf
                subst hgf
                dsimp only
                obtain ⟨hor, hne⟩ := h
                rcases hor with h1 | h1
                · subst h1
                  rw [eval_sub_one, regs_ne hd (Ne.symm hne), toNat_sub_one_of (hI.nz _ hnz)]
                  omega
                · subst h1
                  rw [eval_sub_one, regs_ne hd hne, toNat_sub_one_of (hI.nz _ hnz)]
                  omega
              · simp at hgf
            · simp at hf
    | imulri d y v =>
      simp only at hf
      split at hf
      · rename_i hv
        obtain ⟨hv1, hv64⟩ := hv
        simp only [List.mem_filterMap] at hf
        obtain ⟨p, ⟨g, hg, hgp⟩, hpf⟩ := hf
        obtain ⟨hcy, hle⟩ := partOf_sound hI hg hgp
        have hd : dstRegs (JInstr.imulri (w := 64) d y v) = [d] := rfl
        unfold mulLe at hpf
        split at hpf
        · rename_i h
          simp only [Option.some.injEq] at hpf
          subst hpf
          obtain ⟨hcd, hB⟩ := h
          dsimp only
          have hY := (s.regs y).isLt
          have hC0 : (0 : Int) ≤ (s.regs p.1).toNat := Int.natCast_nonneg _
          have hYB : ((s.regs y).toNat : Int) ≤ p.2 := by omega
          have hprod : ((s.regs y).toNat : Int) * v ≤ p.2 * v :=
            Int.mul_le_mul_of_nonneg_right hYB (Int.natCast_nonneg _)
          have hlt : (s.regs y).toNat * v < 2 ^ 64 := by
            have : (((s.regs y).toNat * v : Nat) : Int) < 2 ^ 64 := by
              push_cast
              rw [Int.mul_comm (v : Int) p.2] at hB
              omega
            exact_mod_cast this
          have hmul : (s.regs y * BitVec.ofNat 64 v).toNat = (s.regs y).toNat * v := by
            rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv64,
              Nat.mod_eq_of_lt hlt]
          rw [eval_imulri, regs_ne hd hcd, hmul]
          push_cast
          unfold mulBound
          split
          · rename_i hnz
            have h1 : (1 : Int) ≤ (s.regs p.1).toNat := by
              have := toNat_pos_of_ne (hI.nz _ (List.contains_iff_mem.mp hnz))
              omega
            have hv1' : (1 : Int) ≤ v := by exact_mod_cast hv1
            nlinarith
          · have hv1' : (1 : Int) ≤ v := by exact_mod_cast hv1
            nlinarith
        · simp at hpf
      · simp at hf
    | _ => simp at hf

theorem slot_keep {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s)
    (hd : ∀ a, writeAddr s i = some a → ∀ e ∈ m.slot,
      Disjoint8 a (s0.regs "%rsp" + BitVec.ofInt 64 e.1)) :
    ∀ e ∈ m.slot, inW σ e.1 = true ∧
      read64 (evalInstrA s i).mem (s0.regs "%rsp" + BitVec.ofInt 64 e.1) = s0.regs e.2 := by
  intro e he
  refine ⟨(hI.slot e he).1, ?_⟩
  simp only [evalInstrA]
  split
  · rename_i a ha
    rw [read64_write64_of_disjoint _ _ _ _ (hd a ha e he)]
    exact (hI.slot e he).2
  · exact (hI.slot e he).2

theorem slotAfter_sound {m : MA} {s : AState} {i : JInstr 64} (hR : σ.Regions s0)
    (hI : Inv σ s0 m s) (hc : cellAddrOK σ m i = true) :
    ∀ e ∈ slotAfter σ m i, inW σ e.1 = true ∧
      read64 (evalInstrA s i).mem (s0.regs "%rsp" + BitVec.ofInt 64 e.1) = s0.regs e.2 := by
  have hsep : frameWrite i = false → ∀ a, writeAddr s i = some a → ∀ e ∈ m.slot,
      Disjoint8 a (s0.regs "%rsp" + BitVec.ofInt 64 e.1) := fun hfw a ha e he =>
    disj_of_cellAddrOK hR hI hc hfw ha (hI.slot e he).1
  cases i with
  | storeMem b off src =>
    simp only [slotAfter]
    split
    · rename_i hb
      subst hb
      have ha : writeAddr s (.storeMem "%rsp" off src)
          = some (s0.regs "%rsp" + BitVec.ofInt 64 (m.sp + off)) := by
        simp only [writeAddr, hI.sp, ofInt_add_assoc]
      intro e he
      simp only [storeSlot, List.mem_append, List.mem_filter] at he
      rcases he with ⟨he, hfar⟩ | he
      · refine ⟨(hI.slot e he).1, ?_⟩
        simp only [far, Bool.and_eq_true, decide_eq_true_eq] at hfar
        simp only [evalInstrA, ha]
        rw [read64_write64_of_disjoint _ _ _ _
          (disjoint8_add_ofInt _ _ _ hfar.1 hfar.2)]
        exact (hI.slot e he).2
      · cases src with
        | imm n => simp at he
        | reg y =>
          simp only at he
          split at he
          · rename_i hw
            simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at he
            obtain ⟨p, ⟨hp, hpy⟩, rfl⟩ := he
            refine ⟨hw, ?_⟩
            simp only [evalInstrA, ha, read64_write64_same]
            simp [writeVal, AState.view, ← hpy, hI.ent p hp]
          · simp at he
    · rename_i hb
      exact slot_keep hI fun a ha => hsep (by simp [frameWrite, hb]) a ha
  | addToMem b off src =>
    simp only [slotAfter]
    split
    · simp
    · rename_i hb
      exact slot_keep hI fun a ha => hsep (by simp [frameWrite, hb]) a ha
  | storeMemIdx b x sc src =>
    simp only [slotAfter]
    split
    · simp
    · rename_i hb
      exact slot_keep hI fun a ha => hsep (by simp [frameWrite, hb]) a ha
  | _ => exact slot_keep hI fun a ha => by simp [writeAddr] at ha

theorem kill_mem {m : MA} {ds : List String} :
    (∀ p ∈ (m.kill ds).ent, p ∈ m.ent ∧ p.1 ∉ ds) ∧ (∀ r ∈ (m.kill ds).zero, r ∈ m.zero ∧ r ∉ ds)
      ∧ (∀ f ∈ (m.kill ds).le, f ∈ m.le ∧ f.1 ∉ ds ∧ f.2.1 ∉ ds)
      ∧ (∀ r ∈ (m.kill ds).nz, r ∈ m.nz ∧ r ∉ ds) := by
  refine ⟨fun p hp => ?_, fun r hr => ?_, fun f hf => ?_, fun r hr => ?_⟩ <;>
    simp_all [MA.kill]

/-- The facts of `w` on registers satisfying `kr` and stack words satisfying `kw` describe a
    state `s'` in which those registers and those stack words of the frame range are
    unchanged. -/
theorem InvW.frame {w : MW} {s s' : AState} (h : InvW σ s0 w s) {kr : String → Bool}
    {kw : Int → Bool} (hreg : ∀ x, kr x = true → s'.regs x = s.regs x)
    (hw : ∀ e, kw e = true → inW σ e = true → wdAt s0 s' e = wdAt s0 s e) :
    InvW σ s0 ((w.keepRegs kr).keepWords kw) s' := by
  refine ⟨fun p hp => ?_, fun e he => ?_, fun f hf => ?_, fun f hf => ?_, fun p hp => ?_,
    fun p hp => ?_⟩
  · simp only [MW.keepWords, MW.keepRegs, List.mem_filter] at hp
    obtain ⟨hin, hv⟩ := h.cst p hp.1
    exact ⟨hin, by rw [hw _ hp.2 hin, hv]⟩
  · simp only [MW.keepWords, MW.keepRegs, List.mem_filter] at he
    obtain ⟨hin, hv⟩ := h.nz e he.1
    exact ⟨hin, by rw [hw _ he.2 hin]; exact hv⟩
  · simp only [MW.keepWords, MW.keepRegs, List.mem_filter, Bool.and_eq_true] at hf
    obtain ⟨h1, h2, hv⟩ := h.le f hf.1
    exact ⟨h1, h2, by rw [hw _ hf.2.1 h1, hw _ hf.2.2 h2]; exact hv⟩
  · simp only [MW.keepWords, MW.keepRegs, List.mem_filter] at hf
    obtain ⟨h1, hv⟩ := h.rle f hf.1.1
    exact ⟨h1, by rw [hreg _ hf.1.2, hw _ hf.2 h1]; exact hv⟩
  · simp only [MW.keepWords, MW.keepRegs, List.mem_filter] at hp
    obtain ⟨h1, hv⟩ := h.same p hp.1.1
    exact ⟨h1, by rw [hreg _ hp.1.2, hw _ hp.2 h1, hv]⟩
  · simp only [MW.keepWords, MW.keepRegs, List.mem_filter] at hp
    obtain ⟨j, hj, hv⟩ := h.ptr p hp.1
    exact ⟨j, hj, by rw [hreg _ hp.2, hv]⟩

/-- The facts of `w` on registers satisfying `kr` describe a state with the same memory in
    which those registers are unchanged. -/
theorem InvW.frameRegs {w : MW} {s s' : AState} (h : InvW σ s0 w s) {kr : String → Bool}
    (hreg : ∀ x, kr x = true → s'.regs x = s.regs x) (hmem : s'.mem = s.mem) :
    InvW σ s0 (w.keepRegs kr) s' := by
  have := h.frame (kw := fun _ => true) hreg fun e _ _ => by simp only [wdAt, hmem]
  simpa [MW.keepWords] using this

/-- The union of two sets of facts describing a state describes it. -/
theorem InvW.union {a b : MW} {s : AState} (ha : InvW σ s0 a s) (hb : InvW σ s0 b s) :
    InvW σ s0 (a.union b) s := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_,
    fun p hp => ?_⟩ <;> simp only [MW.union, List.mem_append] at hp
  · exact hp.elim (ha.cst p) (hb.cst p)
  · exact hp.elim (ha.nz p) (hb.nz p)
  · exact hp.elim (ha.le p) (hb.le p)
  · exact hp.elim (ha.rle p) (hb.rle p)
  · exact hp.elim (ha.same p) (hb.same p)
  · exact hp.elim (ha.ptr p) (hb.ptr p)

/-- The stack words that `wordKeep` keeps in the frame range are unchanged by `i`. -/
theorem wdAt_keep {m : MA} {s : AState} {i : JInstr 64} (hR : σ.Regions s0) (hI : Inv σ s0 m s)
    (hc : cellAddrOK σ m i = true) {e : Int} (hk : wordKeep m.sp i e = true)
    (he : inW σ e = true) : wdAt s0 (evalInstrA s i) e = wdAt s0 s e := by
  simp only [wdAt, evalInstrA]
  split
  · rename_i a ha
    refine read64_write64_of_disjoint _ _ _ _ ?_
    cases hfw : frameWrite i
    · exact disj_of_cellAddrOK hR hI hc hfw ha he
    · cases i with
      | storeMem b off src =>
        simp only [frameWrite, beq_iff_eq] at hfw
        subst hfw
        simp only [wordKeep, bne_self_eq_false, Bool.false_or, far, Bool.and_eq_true,
          decide_eq_true_eq] at hk
        simp only [writeAddr, hI.sp, ofInt_add_assoc, Option.some.injEq] at ha
        subst ha
        exact disjoint8_add_ofInt _ _ _ hk.1 hk.2
      | addToMem b off src =>
        simp only [frameWrite, beq_iff_eq] at hfw
        subst hfw
        simp [wordKeep] at hk
      | storeMemIdx b x sc src =>
        simp only [frameWrite, beq_iff_eq] at hfw
        subst hfw
        simp [wordKeep] at hk
      | _ => simp [writeAddr] at ha
  · rfl

/-- The word a load through `%rsp` reads is the stack word at the stack offset of `m` plus the
    displacement. -/
theorem read_rsp {m : MA} {s : AState} (hI : Inv σ s0 m s) (off : Int) :
    read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 off) = wdAt s0 s (m.sp + off) := by
  rw [hI.sp, ofInt_add_assoc, wdAt]

theorem wNzAdd_sound {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s) :
    ∀ r ∈ wNzAdd m i, (evalInstrA s i).regs r ≠ 0 := by
  intro r hr
  cases i with
  | loadMem d b off =>
    simp only [wNzAdd] at hr
    split at hr
    · rename_i h
      obtain ⟨rfl, hz⟩ := h
      simp only [List.mem_singleton] at hr
      subst hr
      rw [eval_loadMem, read_rsp hI]
      exact (hI.w.nz _ (List.contains_iff_mem.mp hz)).2
    · simp at hr
  | _ => simp [wNzAdd] at hr

theorem eval_add_op (s : AState) (d : String) (src : JOperand) :
    (evalInstrA s (.add d src)).regs d = s.regs d + src.eval s.view := by
  simp [evalInstrA, evalInstr, JState.writeB5W, x86_ADD, rflags_of_aluop, AState.view]

theorem eval_sub_op (s : AState) (d : String) (src : JOperand) :
    (evalInstrA s (.sub d src)).regs d = s.regs d - src.eval s.view := by
  simp [evalInstrA, evalInstr, JState.writeB5W, x86_SUB, AState.view]

theorem eval_shr_imm (s : AState) (d : String) {k : Nat} (hk : k < 64) :
    (evalInstrA s (.shr d (.imm k))).regs d = s.regs d >>> k := by
  have hc : shiftCount (BitVec.ofNat 64 k) = k := by
    simp only [shiftCount, VIR.shiftMask, BitVec.toNat_ofNat]
    grind
  by_cases h0 : k = 0
  · subst h0
    simp [evalInstrA, evalInstr, JState.writeB5W, x86_SHR, AState.view, rflags_None, shiftCount,
      VIR.shiftMask, JState.get]
  · have hm : min 64 k = k := by omega
    simp [evalInstrA, evalInstr, JState.writeB5W, x86_SHR, AState.view, hc, h0, rflags_OF, wshr,
      hm, JState.get]

theorem cstOf_sound {m : MA} {s : AState} (hI : Inv σ s0 m s) {src : JOperand} {k : Nat}
    (h : cstOf m src = some k) : src.eval s.view = BitVec.ofNat 64 k := by
  cases src with
  | imm n =>
    simp only [cstOf, Option.some.injEq] at h
    subst h
    rfl
  | reg y => exact hI.cst (y, k) (mem_of_lookup_cst h)

theorem wCstAdd_sound {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s) :
    ∀ p ∈ wCstAdd m i, (evalInstrA s i).regs p.1 = BitVec.ofNat 64 p.2 := by
  intro p hp
  cases i with
  | loadMem d b off =>
    simp only [wCstAdd] at hp
    split at hp
    · rename_i h
      subst h
      simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
      obtain ⟨q, ⟨hq, hqe⟩, rfl⟩ := hp
      rw [eval_loadMem, read_rsp hI, ← hqe]
      exact (hI.w.cst q hq).2
    · simp at hp
  | add d src =>
    simp only [wCstAdd] at hp
    split at hp
    · rename_i a k ha hk
      simp only [List.mem_singleton] at hp
      subst hp
      rw [eval_add_op, hI.cst (d, a) (mem_of_lookup_cst ha), cstOf_sound hI hk]
      exact (BitVec.ofNat_add _ _).symm
    · simp at hp
  | sub d src =>
    simp only [wCstAdd] at hp
    split at hp
    · rename_i a k ha hk
      split at hp
      · rename_i hle
        simp only [List.mem_singleton] at hp
        subst hp
        rw [eval_sub_op, hI.cst (d, a) (mem_of_lookup_cst ha), cstOf_sound hI hk]
        have h : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - k) + BitVec.ofNat 64 k := by
          rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
        rw [h, BitVec.add_sub_cancel]
      · simp at hp
    · simp at hp
  | shr d src =>
    simp only [wCstAdd] at hp
    split at hp
    · rename_i a k ha
      split at hp
      · rename_i hk
        simp only [List.mem_singleton] at hp
        subst hp
        rw [eval_shr_imm s d hk, hI.cst (d, a) (mem_of_lookup_cst ha)]
        apply BitVec.eq_of_toNat_eq
        have hlt : (a % 2 ^ 64) >>> k < 2 ^ 64 := by
          rw [Nat.shiftRight_eq_div_pow]
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
        simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hlt]
      · simp at hp
    · simp at hp
  | _ => simp [wCstAdd] at hp

/-- A sum over two stack words holds in the form `leCanon` gives it. -/
theorem leCanon_spec {P : Int → Prop} {w : Int → BitVec 64} {e e' B : Int} (h1 : P e) (h2 : P e')
    (h : ((w e).toNat : Int) + (w e').toNat ≤ B) :
    P (leCanon e e' B).1 ∧ P (leCanon e e' B).2.1 ∧
      ((w (leCanon e e' B).1).toNat : Int) + (w (leCanon e e' B).2.1).toNat
        ≤ (leCanon e e' B).2.2 := by
  unfold leCanon
  split
  · exact ⟨h1, h2, h⟩
  · exact ⟨h2, h1, by dsimp only; omega⟩

/-- A store through `%rsp` of a word at the offset `e`, with the word in the stack word at `e`
    and the stack words far from `e` unchanged, makes the facts of `seedLe` hold. -/
theorem seedLe_sound {e : Int} {n : Nat} {kw : List (Int × Nat)} {w : Int → BitVec 64}
    {P : Int → Prop} (hPe : P e) (hPk : ∀ p ∈ kw, P p.1)
    (hn : w e = BitVec.ofNat 64 n) (hk : ∀ p ∈ kw, w p.1 = BitVec.ofNat 64 p.2) :
    ∀ f ∈ seedLe e n kw, P f.1 ∧ P f.2.1 ∧ ((w f.1).toNat : Int) + (w f.2.1).toNat ≤ f.2.2 := by
  intro f hf
  have hmod : ∀ k : Nat, (BitVec.ofNat 64 k).toNat ≤ k := fun k => by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_le _ _
  simp only [seedLe, List.mem_append] at hf
  rcases hf with hf | hf
  · split at hf
    · rename_i h0
      simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hf
      obtain ⟨p, ⟨hp, -⟩, rfl⟩ := hf
      refine leCanon_spec hPe (hPk p hp) ?_
      have := hmod p.2
      simp only [hn, hk p hp, h0]
      simp
      omega
    · simp at hf
  · split at hf
    · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hf
      obtain ⟨p, ⟨hp, hp0⟩, rfl⟩ := hf
      refine leCanon_spec (hPk p hp) hPe ?_
      have := hmod n
      simp only [hn, hk p hp, hp0]
      simp
      omega
    · simp at hf

/-- The stack word at the target of a store through `%rsp` holds the stored word. -/
theorem wdAt_store_same {m : MA} {s : AState} (hI : Inv σ s0 m s) (off : Int) (src : JOperand) :
    wdAt s0 (evalInstrA s (.storeMem "%rsp" off src)) (m.sp + off)
      = writeVal s.view (.storeMem "%rsp" off src) := by
  simp only [wdAt, evalInstrA, writeAddr, hI.sp, ofInt_add_assoc, read64_write64_same]

/-- A stack word far from the target of a store through `%rsp` is unchanged. -/
theorem wdAt_store_far {m : MA} {s : AState} (hI : Inv σ s0 m s) (off : Int) (src : JOperand)
    {e : Int} (he : far (m.sp + off) e = true) :
    wdAt s0 (evalInstrA s (.storeMem "%rsp" off src)) e = wdAt s0 s e := by
  simp only [far, Bool.and_eq_true, decide_eq_true_eq] at he
  simp only [wdAt, evalInstrA, writeAddr, hI.sp, ofInt_add_assoc]
  exact read64_write64_of_disjoint _ _ _ _ (disjoint8_add_ofInt _ _ _ he.1 he.2)

/-- An instruction that writes no memory leaves every stack word unchanged. -/
theorem wdAt_of_none {s : AState} {i : JInstr 64} (h : writeAddr s i = none) (e : Int) :
    wdAt s0 (evalInstrA s i) e = wdAt s0 s e := by
  simp only [wdAt, mem_of_writeAddr_none h]

/-- The bounds of `idxBounds` are exclusive upper bounds on the register. -/
theorem idxBounds_sound {m : MA} {s : AState} (hI : Inv σ s0 m s) {x : String} {n : Nat}
    (hn : n ∈ idxBounds m x) : (s.regs x).toNat < n := by
  simp only [idxBounds, List.mem_append, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, List.contains_iff_mem] at hn
  rcases hn with (⟨f, ⟨hf, rfl, hnz⟩, rfl⟩ | ⟨f, ⟨hf, rfl, hnz⟩, rfl⟩) | ⟨p, ⟨hp, rfl⟩, rfl⟩
  · have hv := (hI.w.rle f hf).2
    have := toNat_pos_of_ne (hI.w.nz _ hnz).2
    omega
  · have hv := hI.le f hf
    have := toNat_pos_of_ne (hI.nz _ hnz)
    omega
  · rw [hI.cst p hp, BitVec.toNat_ofNat]
    exact Nat.lt_succ_of_le (Nat.mod_le _ _)

/-- **Soundness of the facts of `i` on stack words.** -/
theorem genW_sound {m : MA} {s : AState} {i : JInstr 64} (hI : Inv σ s0 m s)
    (hrsp : "%rsp" ∉ dstRegs i) : InvW σ s0 (genW σ m i) (evalInstrA s i) := by
  have hempty : ∀ s' : AState, InvW σ s0 ({} : MW) s' := fun _ =>
    ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
  cases i with
  | storeMem b off src =>
    simp only [genW]
    split
    · rename_i h
      obtain ⟨rfl, hin⟩ := h
      have hval := wdAt_store_same hI off src
      have hfar := fun e => wdAt_store_far (e := e) hI off src
      have hkw : ∀ p ∈ m.w.cst.filter (fun p => far (m.sp + off) p.1),
          inW σ p.1 = true ∧ wdAt s0 (evalInstrA s (.storeMem "%rsp" off src)) p.1
            = BitVec.ofNat 64 p.2 := by
        intro p hp
        obtain ⟨hp, hf⟩ := List.mem_filter.mp hp
        obtain ⟨h1, h2⟩ := hI.w.cst p hp
        exact ⟨h1, by rw [hfar _ hf, h2]⟩
      cases src with
      | imm n =>
        have hv : wdAt s0 (evalInstrA s (.storeMem "%rsp" off (.imm n))) (m.sp + off)
            = BitVec.ofNat 64 n := by
          rw [hval]
          simp [writeVal]
        refine ⟨?_, by simp [genStoreImm], ?_, by simp [genStoreImm], by simp [genStoreImm],
          by simp [genStoreImm]⟩
        · intro p hp
          simp only [genStoreImm, List.mem_singleton] at hp
          subst hp
          exact ⟨hin, hv⟩
        · exact seedLe_sound (P := fun e => inW σ e = true) hin (fun p hp => (hkw p hp).1) hv
            fun p hp => (hkw p hp).2
      | reg y =>
        have hregs : ∀ x, (evalInstrA s (.storeMem "%rsp" off (.reg y))).regs x = s.regs x :=
          fun x => evalInstrA_regs_of_not_dst _ _ _ (by simp [dstRegs])
        have hv : wdAt s0 (evalInstrA s (.storeMem "%rsp" off (.reg y))) (m.sp + off)
            = s.regs y := by
          rw [hval]
          simp [writeVal, AState.view, JState.get]
        refine ⟨?_, ?_, ?_, by simp [genStoreReg], ?_, by simp [genStoreReg]⟩
        · intro p hp
          simp only [genStoreReg, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
          obtain ⟨q, ⟨hq, hqy⟩, rfl⟩ := hp
          exact ⟨hin, by rw [hv, ← hqy]; exact hI.cst q hq⟩
        · intro e he
          simp only [genStoreReg] at he
          split at he
          · rename_i hy
            simp only [List.mem_singleton] at he
            subst he
            exact ⟨hin, by rw [hv]; exact hI.nz y (List.contains_iff_mem.mp hy)⟩
          · simp at he
        · intro f hf
          simp only [genStoreReg, List.mem_append, List.mem_map, List.mem_filter,
            Bool.and_eq_true, decide_eq_true_eq, List.mem_flatMap] at hf
          rcases hf with ⟨g, ⟨hg, rfl, hfr⟩, rfl⟩ | ⟨q, ⟨hq, hqy⟩, hf⟩
          · obtain ⟨h1, h2⟩ := hI.w.rle g hg
            exact leCanon_spec (P := fun e => inW σ e = true)
              (w := wdAt s0 (evalInstrA s (.storeMem "%rsp" off (.reg g.1)))) hin h1
              (by rw [hv, hfar _ hfr]; exact h2)
          · exact seedLe_sound (P := fun e => inW σ e = true) hin (fun p hp => (hkw p hp).1)
              (by rw [hv, ← hqy]; exact hI.cst q hq) (fun p hp => (hkw p hp).2) f hf
        · intro p hp
          simp only [genStoreReg, List.mem_singleton] at hp
          subst hp
          exact ⟨hin, by rw [hregs, hv]⟩
    · exact hempty _
  | loadMem d b off =>
    simp only [genW]
    split
    · rename_i h
      obtain ⟨rfl, hin⟩ := h
      have hd : (evalInstrA s (.loadMem d "%rsp" off)).regs d = wdAt s0 s (m.sp + off) := by
        rw [eval_loadMem, read_rsp hI]
      have hw := fun e => wdAt_of_none (s0 := s0) (s := s) (i := .loadMem d "%rsp" off) rfl e
      refine ⟨by simp, by simp, by simp, ?_, ?_, by simp⟩
      · intro f hf
        simp only [List.mem_filterMap, loadLe] at hf
        obtain ⟨g, hg, hf⟩ := hf
        obtain ⟨h1, h2, h3⟩ := hI.w.le g hg
        split at hf
        · rename_i h
          simp only [Option.some.injEq] at hf
          subst hf
          exact ⟨h2, by rw [hd, hw, ← h]; exact h3⟩
        · split at hf
          · rename_i h
            simp only [Option.some.injEq] at hf
            subst hf
            refine ⟨h1, ?_⟩
            rw [hd, hw, ← h]
            dsimp only
            omega
          · simp at hf
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨hin, by rw [hd, hw]⟩
    · exact hempty _
  | add d src =>
    simp only [genW]
    have hw := fun e => wdAt_of_none (s0 := s0) (s := s) (i := .add d src) rfl e
    refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro f hf
    simp only [addRle, List.mem_append] at hf
    rcases hf with hf | hf
    · split at hf
      · rename_i k hk
        simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hf
        obtain ⟨g, ⟨hg, rfl, hB⟩, rfl⟩ := hf
        obtain ⟨h1, h2⟩ := hI.w.rle g hg
        refine ⟨h1, ?_⟩
        have hn : k < 2 ^ 64 := by omega
        have hx : (s.regs g.1).toNat + k < 2 ^ 64 := by omega
        rw [eval_add_op, cstOf_sound hI hk, toNat_add_ofNat_of hx hn, hw]
        push_cast
        omega
      · simp at hf
    · cases src with
      | imm n => simp at hf
      | reg z =>
        simp only at hf
        split at hf
        · rename_i a ha
          simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hf
          obtain ⟨g, ⟨hg, rfl, hB⟩, rfl⟩ := hf
          obtain ⟨h1, h2⟩ := hI.w.rle g hg
          refine ⟨h1, ?_⟩
          have hn : a < 2 ^ 64 := by omega
          have hx : (s.regs g.1).toNat + a < 2 ^ 64 := by omega
          have hval : (evalInstrA s (.add d (.reg g.1))).regs d
              = s.regs g.1 + BitVec.ofNat 64 a := by
            rw [eval_add_reg, hI.cst (d, a) (mem_of_lookup_cst ha), BitVec.add_comm]
          rw [hval, toNat_add_ofNat_of hx hn, hw]
          push_cast
          omega
        · simp at hf
  | sub d src =>
    simp only [genW]
    split
    · rename_i h
      obtain ⟨rfl, hnz⟩ := h
      have hw := fun e => wdAt_of_none (s0 := s0) (s := s) (i := .sub d (.imm 1)) rfl e
      refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
      intro f hf
      simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hf
      obtain ⟨g, ⟨hg, rfl⟩, rfl⟩ := hf
      obtain ⟨h1, h2⟩ := hI.w.rle g hg
      refine ⟨h1, ?_⟩
      have hne := hI.nz _ (List.contains_iff_mem.mp hnz)
      have hp := toNat_pos_of_ne hne
      rw [eval_sub_one, toNat_sub_one_of hne, hw]
      grind
    · exact hempty _
  | lea d b x sc k =>
    simp only [genW]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, by simp, by simp, by simp, by simp, ?_⟩
      intro p hp
      simp only [List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
      obtain ⟨q, ⟨hq, hqb⟩, n, hn, rfl⟩ := hp
      refine ⟨(s.regs x).toNat, idxBounds_sound hI hn, ?_⟩
      have hd : (evalInstrA s (.lea d b x 8 0)).regs d
          = s.regs b + s.regs x * BitVec.ofNat 64 8 := by
        simp [evalInstrA, evalInstr, JState.setReg, JState.get, x86_LEA, AState.view]
      rw [hd, ← hqb, hI.ent q hq]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_mul, Nat.mul_comm]
    · exact hempty _
  | _ => exact hempty _

/-- **Soundness of the facts on stack words after `i`.** -/
theorem stepW_sound {m : MA} {s : AState} {i : JInstr 64} (hR : σ.Regions s0)
    (hI : Inv σ s0 m s) (hc : cellAddrOK σ m i = true) (hrsp : "%rsp" ∉ dstRegs i) :
    InvW σ s0 (stepW σ m i) (evalInstrA s i) := by
  refine (genW_sound hI hrsp).union ?_
  refine hI.w.frame (fun x hx => ?_) fun e hk he => wdAt_keep hR hI hc hk he
  refine evalInstrA_regs_of_not_dst _ _ _ fun hm => ?_
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hx
  exact hx hm

/-- **Soundness of the abstract effect** of an instruction that does not write `%rsp`. -/
theorem step1_sound {m : MA} {s : AState} {i : JInstr 64} (hR : σ.Regions s0)
    (hI : Inv σ s0 m s) (hrsp : "%rsp" ∉ dstRegs i) (hc : cellAddrOK σ m i = true) :
    Inv σ s0 (step1 σ m i) (evalInstrA s i) := by
  have hk := kill_mem (m := m) (ds := dstRegs i)
  have hreg := evalInstrA_regs_of_not_dst s i
  refine ⟨?_, ?_, ?_, slotAfter_sound hR hI hc, ?_, ?_, zfAfter_sound, ?_, ?_⟩
  · rw [hreg _ hrsp]
    exact hI.sp
  · intro p hp
    simp only [step1, List.mem_append] at hp
    rcases hp with hp | hp
    · exact entAdd_sound hI p hp
    · obtain ⟨hp, hn⟩ := hk.1 p hp
      rw [hreg _ hn]
      exact hI.ent p hp
  · intro r hr
    simp only [step1, List.mem_append] at hr
    rcases hr with hr | hr
    · exact zeroAdd_sound hI r hr
    · obtain ⟨hr, hn⟩ := hk.2.1 r hr
      rw [hreg _ hn]
      exact hI.zero r hr
  · intro f hf
    simp only [step1, List.mem_append] at hf
    rcases hf with hf | hf
    · exact leAdd_sound hI f hf
    · obtain ⟨hf, hn1, hn2⟩ := hk.2.2.1 f hf
      rw [hreg _ hn1, hreg _ hn2]
      exact hI.le f hf
  · intro r hr
    simp only [step1, List.mem_append] at hr
    rcases hr with hr | hr | hr
    · exact wNzAdd_sound hI r hr
    · exact nzAdd_sound hI r hr
    · obtain ⟨hr, hn⟩ := hk.2.2.2 r hr
      rw [hreg _ hn]
      exact hI.nz r hr
  · intro p hp
    simp only [step1, List.mem_append] at hp
    rcases hp with hp | hp | hp
    · exact wCstAdd_sound hI p hp
    · exact cstAdd_sound hI p hp
    · simp only [MA.kill, List.mem_filter, Bool.not_eq_true'] at hp
      have hn : p.1 ∉ dstRegs i := fun hm => by
        rw [List.contains_iff_mem.mpr hm] at hp
        exact Bool.noConfusion hp.2
      rw [hreg _ hn]
      exact hI.cst p hp.1
  · exact stepW_sound hR hI hc hrsp

theorem norm_sound {m : MA} {s : AState} (hR : σ.Regions s0) (hI : Inv σ s0 m s) :
    Inv σ s0 (norm σ m) s := by
  refine ⟨hI.sp, hI.ent, hI.zero, hI.slot, ?_, hI.nz, hI.zf, hI.cst, hI.w⟩
  intro f hf
  simp only [norm, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_filterMap] at hf
  rcases hf with (hf | ⟨r, hr, p, hp, b, hb, hbf⟩) | ⟨r, hr, p, hp, hpf⟩
  · exact hI.le f hf
  · split at hbf
    · rename_i h
      simp only [Option.some.injEq] at hbf
      subst hbf
      dsimp only
      rw [hI.zero r hr, hI.ent p hp, ← h.1]
      have := hR.1 b hb
      rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega
    · simp at hbf
  · split at hpf
    · simp only [Option.some.injEq] at hpf
      subst hpf
      dsimp only
      rw [hI.zero r hr, hI.cst p hp, BitVec.toNat_ofNat,
        show (0 : BitVec 64).toNat = 0 from rfl]
      have := Nat.mod_le p.2 (2 ^ 64)
      omega
    · simp at hpf

/-- **Soundness of `trans`.** -/
theorem trans_sound {m o : MA} {s : AState} {i : JInstr 64} (hR : σ.Regions s0)
    (hI : Inv σ s0 m s) (hc : cellAddrOK σ m i = true) (ht : trans σ m i = some o) :
    Inv σ s0 o (evalInstrA s i) := by
  unfold trans at ht
  split at ht
  · rename_i k hk
    obtain ⟨x, rfl⟩ := rspShift_eq hk
    simp only [Option.some.injEq] at ht
    subst ht
    have hk := kill_mem (m := m) (ds := ["%rsp"])
    have hreg : ∀ y, y ≠ "%rsp" →
        (evalInstrA s (.lea "%rsp" "%rsp" x 0 k)).regs y = s.regs y :=
      fun y hy => regs_ne rfl hy
    have hmem : (evalInstrA s (.lea "%rsp" "%rsp" x 0 k)).mem = s.mem :=
      mem_of_writeAddr_none rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 8
    · exact hI.w.frameRegs (kr := fun x => !(List.contains ["%rsp"] x))
        (fun y hy => hreg y (by simpa using hy)) hmem
    · rw [evalInstrA_rsp_lea, hI.sp, ofInt_add_assoc]
    · intro p hp
      obtain ⟨hp, hn⟩ := hk.1 p hp
      rw [hreg _ (by simpa using hn)]
      exact hI.ent p hp
    · intro r hr
      obtain ⟨hr, hn⟩ := hk.2.1 r hr
      rw [hreg _ (by simpa using hn)]
      exact hI.zero r hr
    · intro e he
      rw [hmem]
      exact hI.slot e he
    · intro f hf
      obtain ⟨hf, hn1, hn2⟩ := hk.2.2.1 f hf
      rw [hreg _ (by simpa using hn1), hreg _ (by simpa using hn2)]
      exact hI.le f hf
    · intro r hr
      obtain ⟨hr, hn⟩ := hk.2.2.2 r hr
      rw [hreg _ (by simpa using hn)]
      exact hI.nz r hr
    · intro c hc
      simp [MA.kill] at hc
    · intro p hp
      simp only [MA.kill, List.mem_filter, Bool.not_eq_true', List.contains_cons,
        List.contains_nil, Bool.or_false, beq_eq_false_iff_ne, ne_eq] at hp
      rw [hreg _ hp.2]
      exact hI.cst p hp.1
  · split at ht
    · simp at ht
    · rename_i hrsp
      simp only [Option.some.injEq] at ht
      subst ht
      exact norm_sound hR (step1_sound hR hI (by simpa using hrsp) hc)

theorem condB_ne_eq (s : AState) : s.view.condB .ne = !s.view.condB .e := by
  simp [JState.condB, x86_eval_cond]

/-- **Soundness of the abstract branch.** -/
theorem jccOut_sound {m : MA} {s : AState} {c : Condt} {b : Bool} (hI : Inv σ s0 m s)
    (hb : s.view.condB c = b) : Inv σ s0 (jccOut m c b) s := by
  unfold jccOut
  split
  · rename_i r hr
    split
    · rename_i hcond
      have hne : s.regs r ≠ 0 := by
        have hz := hI.zf r hr
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
        intro h0
        have he : s.view.condB .e = true := by simp [hz, h0]
        rcases hcond with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [condB_ne_eq, he] at hb
          simp at hb
        · rw [he] at hb
          simp at hb
      refine ⟨hI.sp, hI.ent, hI.zero, hI.slot, hI.le, ?_, hI.zf, hI.cst,
        ⟨hI.w.cst, ?_, hI.w.le, hI.w.rle, hI.w.same, hI.w.ptr⟩⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hne
        · exact hI.nz x hx
      · intro e he
        simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
        rcases he with ⟨p, ⟨hp, hpr⟩, rfl⟩ | he
        · obtain ⟨hin, hv⟩ := hI.w.same p hp
          exact ⟨hin, by rw [← hv, hpr]; exact hne⟩
        · exact hI.w.nz e he
    · exact hI
  · exact hI

theorem succOkM_spec {M : Array (Option MA)} {s : Nat} {o : MA} (h : succOkM M s o = true) :
    ∃ b, M.getD s none = some b ∧ leM b o = true := by
  unfold succOkM at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · simp at h

/-- **Every step of a run satisfies the separation condition.** Under a passing check at
    every index, a run from an index whose abstract state describes the current state, for
    an entry state satisfying `σ.Regions`, is a run whose steps satisfy `FrameSep F`. -/
theorem run_frameSep {r : DoitRegime} {F : List Int} {prog : List RInstr}
    {M : Array (Option MA)} (hc : (List.range prog.length).all (checkAtM σ F prog M) = true)
    (hR : σ.Regions s0) {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState}
    (h : RunL r (fun _ _ => True) prog pc s t s') :
    ∀ m, M.getD pc none = some m → Inv σ s0 m s → RunL r (FrameSep F) prog pc s t s' := by
  have hat : ∀ {pc : Nat} {x : RInstr}, prog[pc]? = some x → checkAtM σ F prog M pc = true :=
    fun hx => List.all_eq_true.mp hc _
      (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hx).1)
  induction h with
  | ret h => exact fun _ _ _ => .ret h
  | @op pc s i t s' h _ _ ih =>
    intro m hm hI
    have hck := hat h
    simp only [checkAtM, hm, h, Bool.and_eq_true] at hck
    obtain ⟨hs, ht⟩ := hck
    split at ht
    · rename_i o ho
      obtain ⟨b, hb, hle⟩ := succOkM_spec ht
      have hcell : cellAddrOK σ m i = true := by
        simp only [safeW, Bool.and_eq_true] at hs
        exact hs.1
      exact .op h (frameSep_of_safeW hR hI hs)
        (ih b hb (Inv.of_leM hle (trans_sound hR hI hcell ho)))
    · simp at ht
  | @jcc pc s cc tgt c t s' h hcc _ ih =>
    intro m hm hI
    have hck := hat h
    simp only [checkAtM, hm, h, hcc, Bool.and_eq_true] at hck
    refine .jcc h hcc ?_
    cases hcb : s.view.condB c
    · obtain ⟨b, hb, hle⟩ := succOkM_spec hck.2
      have := ih b (by simpa [hcb] using hb) (Inv.of_leM hle (jccOut_sound hI hcb))
      simpa [hcb] using this
    · obtain ⟨b, hb, hle⟩ := succOkM_spec hck.1
      have := ih b (by simpa [hcb] using hb) (Inv.of_leM hle (jccOut_sound hI hcb))
      simpa [hcb] using this
  | @stack pc s ri ops t s' h hops _ _ _ =>
    intro m hm _
    have hck := hat h
    cases ri <;> simp only [RInstr.stackOps?, reduceCtorEq] at hops <;>
      simp [checkAtM, hm, h] at hck
  | call h _ _ _ _ _ _ =>
    intro m hm _
    have hck := hat h
    simp [checkAtM, hm, h] at hck

/-- A stack word of `stackSlots` lies in the frame range and holds, at an entry state
    satisfying `σ.Regions`, the entry value of its carrier name. -/
theorem stackSlots_sound (hR : σ.Regions s0) {P : AbiArg → Bool} :
    ∀ e ∈ stackSlots σ P, inW σ e.1 = true ∧
      read64 s0.mem (s0.regs "%rsp" + BitVec.ofInt 64 e.1) = s0.regs e.2 := by
  intro e he
  simp only [stackSlots, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    beq_iff_eq] at he
  obtain ⟨k, -, a, ⟨ha, ⟨hk, -⟩, hin⟩, rfl⟩ := he
  refine ⟨hin, ?_⟩
  have h := hR.stackIn a ha k hk
  rw [show (8 * (k : Int)) = ((8 * k : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast]
  exact h.symm

theorem inv_init (hR : σ.Regions s0) : Inv σ s0 (init σ) s0 :=
  norm_sound hR ⟨by simp, fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨a, -, rfl⟩ := hp
    rfl, by simp, stackSlots_sound hR, by simp, by simp, by simp, by simp,
    ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩⟩

/-- **Soundness of the certificate check.** Under a passing `memCheck σ F prog M`, every run
    of `prog` from index `0` and an entry state satisfying `σ.Regions` satisfies `FrameSep F`
    at every step. -/
theorem memCheck_sound {r : DoitRegime} {F : List Int} {prog : List RInstr}
    {M : Array (Option MA)} (hc : memCheck σ F prog M = true) (hR : σ.Regions s0)
    {t : List CTLeak} {s' : AState} (h : RunL r (fun _ _ => True) prog 0 s0 t s') :
    RunL r (FrameSep F) prog 0 s0 t s' := by
  simp only [memCheck, Bool.and_eq_true] at hc
  obtain ⟨b, hb, hle⟩ := succOkM_spec hc.1
  exact run_frameSep hc.2 hR h b hb (Inv.of_leM hle (inv_init hR))

end Soundness

/-- **Soundness of the constant-time decision on a given certificate.** If
    `fastCheckWith r P prog A K` holds, two runs of `prog` from index `0` from states
    agreeing on `P`, whose steps satisfy `FrameSep (fastFrame prog A K)`, have equal leakage
    traces. -/
theorem fastCheckWith_sound {r : DoitRegime} {P : PubA} {prog : List RInstr}
    {A : Array (Option PubA)} {K : PresCtx} (h : fastCheckWith r P prog A K = true) :
    ConstantTimeRel P.Agree
      (fun sa t => ∃ sa', RunL r (FrameSep (fastFrame prog A K)) prog 0 sa t sa') := by
  intro s₁ s₂ t₁ t₂ hag ⟨_, h₁⟩ ⟨_, h₂⟩
  simp only [fastCheckWith, Bool.and_eq_true, succOkA_eq, checkCertA_eq] at h
  obtain ⟨⟨h0, hp⟩, hc⟩ := h
  obtain ⟨b, hb, hle⟩ := succOk_spec h0
  exact (checkCert_sound hc hp h₁ hb (PubA.agree_of_le hle hag) h₂).1

end RegionSep

namespace AbiLayout

open RegionSep

/-- The public entry set of the checker with the stack words of the public stack parameters:
    `pubA` with the frame word `8 k` for a public parameter with the carrier name
    `stackArgReg k`. -/
def pubAS (σ : AbiLayout) : PubA :=
  { σ.pubA with cells := (stackSlots σ σ.argPub).map (·.1) }

/-- Agreement on the public data of the layout, at entry states satisfying `σ.Regions`, implies
    agreement on `pubAS`: a stack parameter's word is the entry value of its carrier name. -/
theorem pubAS_agree {σ : AbiLayout} {s₁ s₂ : AState} (h : σ.PubAgree s₁ s₂)
    (hR₁ : σ.Regions s₁) (hR₂ : σ.Regions s₂) : σ.pubAS.Agree s₁ s₂ := by
  obtain ⟨hr, -, hf, hw⟩ := pubA_agree_of_pubAgree h
  refine ⟨hr, fun o ho => ?_, hf, hw⟩
  simp only [pubAS, List.mem_map] at ho
  obtain ⟨e, he, rfl⟩ := ho
  have h1 := (stackSlots_sound hR₁ e he).2
  have h2 := (stackSlots_sound hR₂ e he).2
  simp only [stackSlots, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true] at he
  obtain ⟨k, -, a, ⟨ha, ⟨-, hp⟩, -⟩, rfl⟩ := he
  simp only [X86Backend.DecodedCT.cellAt]
  rw [h1, h2]
  exact h.regs a ha hp

/-- The trimmed certificate of the gate on `prog`: the inferred constant-time certificate,
    each frame word kept when it lies in the frame range of `σ` at every store through
    another base. -/
def ctCertR (σ : AbiLayout) (prog : List RInstr) : Array (Option PubA) :=
  trimCert σ (storeSps prog (inferM σ prog)) (fastCert prog σ.pubA).1

/-- The frame words of the trimmed certificate. -/
def ctFrameR (σ : AbiLayout) (prog : List RInstr) : List Int :=
  fastFrame prog (σ.ctCertR prog) (fastCert prog σ.pubA).2

/-- **The constant-time decision with the region analysis**: the decision on the trimmed
    certificate, and the region check for its frame words. -/
def ctCheckR (σ : AbiLayout) (prog : List RInstr) : Bool :=
  fastCheckWith ctRegime σ.pubA prog (σ.ctCertR prog) (fastCert prog σ.pubA).2
    && memCheck σ (σ.ctFrameR prog) prog (inferM σ prog)

/-- **The constant-time gate on bytes with the region analysis**: the bytes decode and
    `ctCheckR` accepts the decoded program. -/
def ctGateR (σ : AbiLayout) (bytes : List (BitVec 8)) : Bool :=
  match decodeLprog bytes with
  | some prog => σ.ctCheckR prog
  | none => false

/-- **Soundness of `ctCheckR`.** Two runs of `prog` from index `0`, with no side condition,
    from entry states satisfying `σ.Regions` and agreeing on the public data of `σ`, have
    equal leakage traces under `ctRegime`. -/
theorem ctCheckR_sound {σ : AbiLayout} {prog : List RInstr} (h : σ.ctCheckR prog = true) :
    ConstantTimeRel (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂)
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  intro s₁ s₂ t₁ t₂ ⟨hag, hR₁, hR₂⟩ ⟨s₁', h₁⟩ ⟨s₂', h₂⟩
  simp only [ctCheckR, Bool.and_eq_true] at h
  exact fastCheckWith_sound h.1 s₁ s₂ t₁ t₂ (pubA_agree_of_pubAgree hag)
    ⟨s₁', memCheck_sound h.2 hR₁ h₁⟩ ⟨s₂', memCheck_sound h.2 hR₂ h₂⟩

/-- **Soundness of the gate.** Bytes that pass `σ.ctGateR` decode to a program `prog` whose
    runs from index `0`, with no side condition, from entry states satisfying `σ.Regions` and
    agreeing on the public data of `σ`, have equal leakage traces. -/
theorem ctGateR_sound {σ : AbiLayout} {bytes : List (BitVec 8)} (h : σ.ctGateR bytes = true) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ConstantTimeRel (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂)
        (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  unfold ctGateR at h
  split at h
  · rename_i prog hd
    exact ⟨prog, hd, ctCheckR_sound h⟩
  · cases h

end AbiLayout

end CatCrypt.Crypto.SecureCompilation.Haxc

