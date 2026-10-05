/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
public import CatCrypt.Crypto.SecureCompilation.CT.IsaRegime
public import CatCrypt.Crypto.SecureCompilation.Ascent.FootprintEA

/-!
# Address leakage of `JInstr 64` over effective-address operands

The leak model of decoded programs (`DecodedCT.opLeak`) emits one address event per memory
access of an instruction, resolved in the address machine state. This module states that
address channel over the effective-address operands of `EffAddr`: the address events of an
instruction are the addresses `EffAddr.eaVal` of the operand it reads (`EffAddr.readEA`)
followed by the operand it writes (`EffAddr.writeEA`).

The statement holds for every constructor of `JInstr 64` with the same order and
multiplicity on both sides. The forms with a base and a displacement emit one event, at
`eaVal` of `EA.cell`; `addToMem` reads and writes one word and emits two events at that
address; `loadMemIdx` and `storeMemIdx` emit one event at `eaVal` of `EA.indexed`. `lea`
and `loadSym` compute an address without a memory access: they have no `readEA` or
`writeEA` operand and emit no event.

## Main definitions

* `EA.regs`: the registers an operand mentions.
* `instrEAs`: the operands an instruction reads, then writes.
* `eaLeak`: the addresses of the words an instruction reads, then writes, in a state.
* `addrEv`: the address event of the flat memory at an address.
* `blockEaLeak`: `eaLeak` along the run of a straight-line block.

## Main results

* `instrLeak_resolve`: the resolved events of `instrLeak` are `eaLeak`.
* `addrEvents_opLeak`: the address channel of `opLeak` is `eaLeak`, under every regime.
* `addrEvents_opLeak_eq_iff`: two states emit the same address events exactly when their
  `eaLeak` agree.
* `eaVal_of_agree`, `eaLeak_congr`, `addrEvents_opLeak_congr`: states that agree on the
  registers the operands mention emit the same address events.
* `eaVal_of_base`, `eaLeak_congr_region`, `addrEvents_opLeak_congr_region`: operands whose
  base register holds the base of the same range in both states, with equal index
  registers, emit the same address events.
* `eaLeak_map_word`, `eaLeak_eq_iff_ranges`: `eaLeak` against the word ranges
  `FootprintEA.instrReadsEA` and `FootprintEA.instrWritesEA`.
* `addrEvents_blockLeakA`: the address channel of a straight-line block is `blockEaLeak`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EffAddrLeak

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.EffAddr
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Footprint
open CatCrypt.Crypto.SecureCompilation.Ascent.FootprintEA
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## The addresses an instruction accesses -/

/-- The registers an operand mentions: its base, and its index if any. -/
def EA.regs (e : EA) : List String := e.base :: e.index.toList.map Prod.fst

/-- The operands an instruction accesses: the one it reads, then the one it writes. -/
def instrEAs (i : JInstr 64) : List EA := (readEA i).toList ++ (writeEA i).toList

/-- The addresses of the words an instruction reads, then writes, in the state `sa`. -/
def eaLeak (sa : AState) (i : JInstr 64) : List (BitVec 64) := (instrEAs i).map (eaVal sa)

/-- The address event of an access to the flat memory at address `a`. -/
def addrEv (a : BitVec 64) : CTLeak := .addr "" (a.toNat : Int)

theorem addrEv_injective : Function.Injective addrEv := by
  intro a b h
  simp only [addrEv, CTLeak.addr.injEq, true_and, Int.natCast_inj] at h
  exact BitVec.eq_of_toNat_eq h

theorem addrEvents_map_addrEv (l : List (BitVec 64)) :
    addrEvents (l.map addrEv) = l.map addrEv := by
  simp [addrEvents, addrEv, CTLeak.isAddr]

/-! ## The address channel of one instruction -/

/-- The events of `instrLeak`, resolved in `sa`, are the address events of `eaLeak`: one
    per operand read or written, in that order. -/
theorem instrLeak_resolve (sa : AState) (i : JInstr 64) :
    (instrLeak sa.view i).map (resolveEv sa) = (eaLeak sa i).map addrEv := by
  cases i <;>
    simp [instrLeak, resolveEv, eaLeak, instrEAs, readEA, writeEA, readKey, writeKey, addrEv,
      eaVal_indexed, AState.view]

/-- The address channel of the leakage of one instruction is `eaLeak`, under every
    regime. -/
theorem addrEvents_opLeak (r : DoitRegime) (sa : AState) (i : JInstr 64) :
    addrEvents (opLeak r sa i) = (eaLeak sa i).map addrEv := by
  rw [opLeak, addrEvents_append, instrLeak_resolve, addrEvents_map_addrEv]
  split <;> simp [addrEvents, CTLeak.isAddr]

/-- Two states emit the same address events for `i` exactly when the addresses `eaLeak`
    agree. -/
theorem addrEvents_opLeak_eq_iff (r r' : DoitRegime) (sa sb : AState) (i : JInstr 64) :
    addrEvents (opLeak r sa i) = addrEvents (opLeak r' sb i) ↔ eaLeak sa i = eaLeak sb i := by
  rw [addrEvents_opLeak, addrEvents_opLeak]
  exact (List.map_injective_iff.mpr addrEv_injective).eq_iff

/-! ## Congruence in the registers of the operands -/

/-- An operand denotes the same address in two states that agree on the registers it
    mentions. -/
theorem eaVal_of_agree (sa sb : AState) (e : EA)
    (h : ∀ x ∈ EA.regs e, sa.regs x = sb.regs x) : eaVal sa e = eaVal sb e := by
  obtain ⟨b, idx, d⟩ := e
  cases idx with
  | none => simp [eaVal, EA.idxVal, h b (by simp [EA.regs])]
  | some p =>
    obtain ⟨x, sc⟩ := p
    simp [eaVal, EA.idxVal, h b (by simp [EA.regs]), h x (by simp [EA.regs])]

/-- Two states that agree on the registers the operands of `i` mention access the same
    addresses. -/
theorem eaLeak_congr (sa sb : AState) (i : JInstr 64)
    (h : ∀ e ∈ instrEAs i, ∀ x ∈ EA.regs e, sa.regs x = sb.regs x) :
    eaLeak sa i = eaLeak sb i :=
  List.map_congr_left fun e he => eaVal_of_agree sa sb e (h e he)

/-- Two states that agree on the registers the operands of `i` mention emit the same
    address events, whatever their memories, flags, other registers and regimes. -/
theorem addrEvents_opLeak_congr (r r' : DoitRegime) (sa sb : AState) (i : JInstr 64)
    (h : ∀ e ∈ instrEAs i, ∀ x ∈ EA.regs e, sa.regs x = sb.regs x) :
    addrEvents (opLeak r sa i) = addrEvents (opLeak r' sb i) :=
  (addrEvents_opLeak_eq_iff r r' sa sb i).mpr (eaLeak_congr sa sb i h)

/-! ## Operands into a range with a public base -/

/-- An operand whose base register holds the base of the range `R` denotes the address at
    the offset of its scaled index and displacement in `R`. -/
theorem eaVal_of_base (sa : AState) (e : EA) (R : Rng) (hb : sa.regs e.base = R.base) :
    eaVal sa e = R.base + (EA.idxVal sa.regs e.index + BitVec.ofInt 64 e.disp) := by
  rw [eaVal, hb, BitVec.add_assoc]

/-- Each operand of `i` has its base register at the base of a range `R e` in both
    states, and the two states agree on its index register: the addresses accessed are
    equal. The base registers need not be equal as names or hold equal values elsewhere;
    the range is the same for the two states. -/
theorem eaLeak_congr_region (sa sb : AState) (i : JInstr 64) (R : EA → Rng)
    (ha : ∀ e ∈ instrEAs i, sa.regs e.base = (R e).base)
    (hb : ∀ e ∈ instrEAs i, sb.regs e.base = (R e).base)
    (hx : ∀ e ∈ instrEAs i, ∀ p, e.index = some p → sa.regs p.1 = sb.regs p.1) :
    eaLeak sa i = eaLeak sb i := by
  refine List.map_congr_left fun e he => ?_
  rw [eaVal_of_base sa e (R e) (ha e he), eaVal_of_base sb e (R e) (hb e he)]
  cases hidx : e.index with
  | none => rfl
  | some p =>
    obtain ⟨x, sc⟩ := p
    simp only [EA.idxVal, hx e he (x, sc) hidx]

/-- The address events of `i` are equal in two states where each operand has its base
    register at the base of the same range and an index register of equal value. -/
theorem addrEvents_opLeak_congr_region (r r' : DoitRegime) (sa sb : AState) (i : JInstr 64)
    (R : EA → Rng) (ha : ∀ e ∈ instrEAs i, sa.regs e.base = (R e).base)
    (hb : ∀ e ∈ instrEAs i, sb.regs e.base = (R e).base)
    (hx : ∀ e ∈ instrEAs i, ∀ p, e.index = some p → sa.regs p.1 = sb.regs p.1) :
    addrEvents (opLeak r sa i) = addrEvents (opLeak r' sb i) :=
  (addrEvents_opLeak_eq_iff r r' sa sb i).mpr (eaLeak_congr_region sa sb i R ha hb hx)

/-! ## The word ranges of the footprint -/

/-- The words at the addresses of `eaLeak` are the ranges the instruction reads, then
    writes. -/
theorem eaLeak_map_word (sa : AState) (i : JInstr 64) :
    (eaLeak sa i).map Rng.word = instrReadsEA sa i ++ instrWritesEA sa i := by
  simp only [eaLeak, instrEAs, instrReadsEA, instrWritesEA, List.map_append, List.map_map]
  rfl

theorem word_injective : Function.Injective Rng.word := by
  intro a b h
  simpa [Rng.word] using h

/-- Two states access the same addresses in `i` exactly when the word ranges `i` reads and
    writes are the same in both. -/
theorem eaLeak_eq_iff_ranges (sa sb : AState) (i : JInstr 64) :
    eaLeak sa i = eaLeak sb i ↔
      instrReadsEA sa i ++ instrWritesEA sa i = instrReadsEA sb i ++ instrWritesEA sb i := by
  rw [← eaLeak_map_word, ← eaLeak_map_word]
  exact (List.map_injective_iff.mpr word_injective).eq_iff.symm

/-! ## Straight-line blocks -/

/-- The addresses the run of a straight-line block accesses, in order, the state threaded
    by `evalInstrA`. -/
def blockEaLeak (sa : AState) : List (JInstr 64) → List (BitVec 64)
  | [] => []
  | i :: is => eaLeak sa i ++ blockEaLeak (evalInstrA sa i) is

/-- The address channel of the leakage of a straight-line block is `blockEaLeak`, under
    every regime. -/
theorem addrEvents_blockLeakA (r : DoitRegime) (ops : List (JInstr 64)) :
    ∀ sa : AState, addrEvents (blockLeakA r sa ops) = (blockEaLeak sa ops).map addrEv := by
  induction ops with
  | nil => intro sa; rfl
  | cons i is ih =>
    intro sa
    rw [blockLeakA, addrEvents_append, addrEvents_opLeak, ih, blockEaLeak, List.map_append]

end CatCrypt.Crypto.SecureCompilation.X86Backend.EffAddrLeak
