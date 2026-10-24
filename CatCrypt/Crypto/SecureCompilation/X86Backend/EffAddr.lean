/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-!
# Effective-address operands of `JInstr 64`

An x86 memory operand is `disp(base, index, scale)`: a base register, an optional index
register with a scale, and a displacement. `EA` is that operand, and `eaVal sa e` is the
address it denotes in the address machine state `sa`, computed in `BitVec 64`.

The memory constructors of `JInstr` carry two operand shapes: a base with a displacement
(`loadMem`, `storeMem`, `mulxMem`, the ALU forms with a memory operand), and a base with a
scaled index and no displacement (`loadMemIdx`, `storeMemIdx`). `lea` carries the full
shape. `readEA`, `writeEA` and `leaEA` give the operand of each constructor as an `EA`, and
the step `AddrMem.evalInstrA` is characterised through them: it writes the word at
`eaVal sa e` for `writeEA i = some e` and no other byte, and its registers, flags and
stored word depend on memory only through the word at `eaVal sa e` for `readEA i = some e`.

## Alignment

`Aligned8 a` states that `a` is a multiple of eight. The byte memory `AddrMem.AMem` has no
alignment requirement: `read64` and `write64` are defined at every address and
`AddrMem.read64_write64_same` holds at every address, which matches the general-purpose
`MOV`, `ADD`, `ADCX`, `ADOX`, `MULX`, `IMUL`, `CMP` and `CMOVcc` forms of `JInstr`, none of
which faults on an unaligned operand. Alignment gives two properties of the model: an
aligned word does not wrap around the address space (`aligned8_no_wrap`), and two aligned
words coincide or share no byte (`aligned8_eq_or_disjoint8`), so separation of aligned
words is disequality of their addresses.

## Main definitions

* `EA`, `EA.wfB`: the operand; scale in `{1, 2, 4, 8}` and a signed 32-bit displacement.
* `EA.cell`, `EA.indexed`, `EA.sib`: the three operand shapes of `JInstr`.
* `eaVal`: the address `regs base + regs index * scale + disp`.
* `readEA`, `writeEA`, `leaEA`: the operand a `JInstr 64` reads, writes, or computes.
* `Aligned8`: an address that is a multiple of eight.

## Main results

* `writeAddr_eq_eaVal`, `readEA_eq`, `writeEA_eq`: the operands agree with
  `AddrMem.writeAddr`, `AddrMem.readKey` and `AddrMem.writeKey`.
* `evalInstrA_mem`, `evalInstrA_mem_of_not_inRange`, `evalInstrA_read_written`: the step
  writes the word at `eaVal` and leaves every byte outside it unchanged.
* `evalInstr_view_congr_ea`, `evalInstrA_congr_ea`: the step reads memory only in the word
  at `eaVal`.
* `evalInstrA_loadMem_regs`, `evalInstrA_loadMemIdx_regs`, `evalInstrA_storeMem_mem`,
  `evalInstrA_storeMemIdx_mem`, `evalInstrA_lea_regs`: the load, store and `lea` forms.
* `aligned8_no_wrap`, `aligned8_eq_or_disjoint8`, `read64_write64_of_aligned_ne`,
  `eaVal_aligned`: alignment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EffAddr

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-! ## The operand -/

/-- An effective-address operand `disp(base, index, scale)`. -/
structure EA where
  /-- The base register. -/
  base : String
  /-- The index register and its scale, if any. -/
  index : Option (String × Nat) := none
  /-- The displacement. -/
  disp : Int := 0
  deriving DecidableEq, Repr

namespace EA

/-- The operand is encodable: the scale is `1`, `2`, `4` or `8`, and the displacement is a
    signed 32-bit integer. -/
def wfB (e : EA) : Bool :=
  (match e.index with
    | none => true
    | some (_, sc) => sc == 1 || sc == 2 || sc == 4 || sc == 8) &&
  decide (-2 ^ 31 ≤ e.disp) && decide (e.disp < 2 ^ 31)

/-- The operand `off(base)`. -/
def cell (b : String) (off : Int) : EA := ⟨b, none, off⟩

/-- The operand `(base, index, scale)`. -/
def indexed (b x : String) (sc : Nat) : EA := ⟨b, some (x, sc), 0⟩

/-- The operand `off(base, index, scale)`, with scale `0` read as the absence of an index,
    the convention of `JInstr.lea`. -/
def sib (b x : String) (sc : Nat) (off : Int) : EA :=
  ⟨b, if sc = 0 then none else some (x, sc), off⟩

/-- The contribution of the index to the address. -/
def idxVal (regs : String → BitVec 64) : Option (String × Nat) → BitVec 64
  | none => 0
  | some (x, sc) => regs x * BitVec.ofNat 64 sc

end EA

/-- The address an operand denotes: `regs base + regs index * scale + disp` in
    `BitVec 64`. -/
def eaVal (sa : AState) (e : EA) : BitVec 64 :=
  sa.regs e.base + EA.idxVal sa.regs e.index + BitVec.ofInt 64 e.disp

theorem eaVal_congr (sa sb : AState) (e : EA) (hr : sa.regs = sb.regs) :
    eaVal sb e = eaVal sa e := by
  simp only [eaVal, hr]

@[simp] theorem eaVal_cell (sa : AState) (b : String) (off : Int) :
    eaVal sa (.cell b off) = sa.regs b + BitVec.ofInt 64 off := by
  simp [eaVal, EA.cell, EA.idxVal]

theorem ofInt_scale (x : BitVec 64) (sc : Nat) :
    BitVec.ofInt 64 ((sc * x.toNat : Nat) : Int) = x * BitVec.ofNat 64 sc := by
  rw [BitVec.ofInt_natCast, Nat.mul_comm, BitVec.ofNat_mul, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem ofInt_scale' (x : BitVec 64) (sc : Nat) :
    BitVec.ofInt 64 ((sc : Int) * (x.toNat : Int)) = x * BitVec.ofNat 64 sc := by
  rw [← ofInt_scale]; push_cast; rfl

/-- The address of `(base, index, scale)` in the form `AddrMem.writeAddr` uses. -/
theorem eaVal_indexed (sa : AState) (b x : String) (sc : Nat) :
    eaVal sa (.indexed b x sc) =
      sa.regs b + BitVec.ofInt 64 ((sc * (sa.regs x).toNat : Nat) : Int) := by
  rw [ofInt_scale]
  simp [eaVal, EA.indexed, EA.idxVal]

theorem eaVal_sib (sa : AState) (b x : String) (sc : Nat) (off : Int) :
    eaVal sa (.sib b x sc off) =
      sa.regs b + sa.regs x * BitVec.ofNat 64 sc + BitVec.ofInt 64 off := by
  by_cases h : sc = 0
  · subst h
    simp [eaVal, EA.sib, EA.idxVal]
  · simp only [eaVal, EA.sib, ite_eq_right h, EA.idxVal]

/-! ## The operands of an instruction -/

/-- The operand an instruction reads from memory. -/
def readEA : JInstr 64 → Option EA
  | .loadMemIdx _ b x sc => some (.indexed b x sc)
  | i => (readKey i).map fun k => .cell k.1 k.2

/-- The operand an instruction writes to memory. -/
def writeEA : JInstr 64 → Option EA
  | .storeMemIdx b x sc _ => some (.indexed b x sc)
  | i => (writeKey i).map fun k => .cell k.1 k.2

/-- The operand whose address `lea` computes. -/
def leaEA : JInstr 64 → Option EA
  | .lea _ b x sc off => some (.sib b x sc off)
  | _ => none

theorem readEA_eq (i : JInstr 64) (hf : addrFormB i = true) :
    readEA i = (readKey i).map fun k => .cell k.1 k.2 := by
  cases i <;> simp only [addrFormB, Bool.false_eq_true] at hf <;> rfl

theorem writeEA_eq (i : JInstr 64) (hf : addrFormB i = true) :
    writeEA i = (writeKey i).map fun k => .cell k.1 k.2 := by
  cases i <;> simp only [addrFormB, Bool.false_eq_true] at hf <;> rfl

/-- The address `AddrMem.writeAddr` gives is `eaVal` at `writeEA`. -/
theorem writeAddr_eq_eaVal (sa : AState) (i : JInstr 64) :
    writeAddr sa i = (writeEA i).map (eaVal sa) := by
  cases i <;>
    simp only [writeAddr, writeEA, writeKey, Option.map_some, Option.map_none, eaVal_cell,
      eaVal_indexed]

/-! ## The step writes the word at `eaVal` -/

/-- The memory after one step: the stored word at the address of `writeEA`, and the memory
    unchanged for an instruction with no memory destination. -/
theorem evalInstrA_mem (sa : AState) (i : JInstr 64) :
    (evalInstrA sa i).mem = match writeEA i with
      | some e => write64 sa.mem (eaVal sa e) (writeVal sa.view i)
      | none => sa.mem := by
  simp only [evalInstrA, writeAddr_eq_eaVal]
  cases writeEA i <;> rfl

/-- A byte outside the eight bytes at the address of `writeEA` keeps its value. -/
theorem evalInstrA_mem_of_not_inRange (sa : AState) (i : JInstr 64) (x : BitVec 64)
    (h : ∀ e, writeEA i = some e → ¬ InRange8 (eaVal sa e) x) :
    (evalInstrA sa i).mem x = sa.mem x := by
  rw [evalInstrA_mem]
  cases hw : writeEA i with
  | none => rfl
  | some e => exact write64_of_not_inRange _ _ _ _ (h e hw)

/-- The word at the address of `writeEA` after the step is the stored word. -/
theorem evalInstrA_read_written (sa : AState) (i : JInstr 64) (e : EA)
    (hw : writeEA i = some e) :
    read64 (evalInstrA sa i).mem (eaVal sa e) = writeVal sa.view i := by
  rw [evalInstrA_mem, hw]
  exact read64_write64_same _ _ _

/-- A word disjoint from the one at the address of `writeEA` reads back unchanged. -/
theorem evalInstrA_read_of_disjoint (sa : AState) (i : JInstr 64) (b : BitVec 64)
    (h : ∀ e, writeEA i = some e → Disjoint8 (eaVal sa e) b) :
    read64 (evalInstrA sa i).mem b = read64 sa.mem b := by
  rw [evalInstrA_mem]
  cases hw : writeEA i with
  | none => rfl
  | some e => exact read64_write64_of_disjoint _ _ _ _ (h e hw)

/-! ## The step reads the word at `eaVal` -/

/-- `evalInstr` on the view reads memory only in the word at the address of `readEA`: two
    address states with equal registers and flags and equal words there compute equal
    registers, flags and stored word. -/
theorem evalInstr_view_congr_ea (sa sb : AState) (i : JInstr 64) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hm : ∀ e, readEA i = some e → read64 sb.mem (eaVal sa e) = read64 sa.mem (eaVal sa e)) :
    (evalInstr sb.view i).regs = (evalInstr sa.view i).regs ∧
      (evalInstr sb.view i).flags = (evalInstr sa.view i).flags ∧
      writeVal sb.view i = writeVal sa.view i := by
  by_cases hform : addrFormB i = true
  · refine evalInstr_congr sb.view sa.view i hform hr.symm hf.symm (fun k hk => ?_)
    have h := hm (.cell k.1 k.2) (by rw [readEA_eq i hform, hk]; rfl)
    rw [eaVal_cell] at h
    simp only [AState.view, ← hr]
    exact h
  · obtain ⟨R, F, M⟩ := sa
    obtain ⟨R', F', M'⟩ := sb
    simp only at hr hf
    subst hr hf
    cases i <;> simp only [addrFormB, not_true_eq_false] at hform
    · rename_i d b idx sc
      have e := hm _ rfl
      rw [eaVal_indexed, ofInt_scale] at e
      refine ⟨?_, rfl, rfl⟩
      simp only [evalInstr, JState.setReg, JState.loadIdx, JState.load, JState.get,
        AState.view, x86_MOV, ofInt_scale', e]
    · rename_i b idx sc src
      refine ⟨rfl, rfl, ?_⟩
      cases src <;> rfl
    · exact ⟨rfl, rfl, rfl⟩

/-- One step from two states with equal registers and flags and equal words at the address
    of `readEA`: equal registers and flags, and the same word stored at the same address. -/
theorem evalInstrA_congr_ea (sa sb : AState) (i : JInstr 64) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hm : ∀ e, readEA i = some e → read64 sb.mem (eaVal sa e) = read64 sa.mem (eaVal sa e)) :
    (evalInstrA sb i).regs = (evalInstrA sa i).regs ∧
      (evalInstrA sb i).flags = (evalInstrA sa i).flags ∧
      (evalInstrA sb i).mem = match writeEA i with
        | some e => write64 sb.mem (eaVal sa e) (writeVal sa.view i)
        | none => sb.mem := by
  obtain ⟨h1, h2, h3⟩ := evalInstr_view_congr_ea sa sb i hr hf hm
  refine ⟨h1, h2, ?_⟩
  rw [evalInstrA_mem, h3]
  cases writeEA i with
  | none => rfl
  | some e => simp only [eaVal_congr sa sb e hr]

/-! ## The load, store and `lea` forms -/

/-- `loadMem d b off` writes to `d` the word at `off(b)`. -/
theorem evalInstrA_loadMem_regs (sa : AState) (d b : String) (off : Int) :
    (evalInstrA sa (.loadMem d b off)).regs d = read64 sa.mem (eaVal sa (.cell b off)) := by
  simp [evalInstrA, evalInstr, JState.setReg, AState.view, x86_MOV]

/-- `loadMemIdx d b x sc` writes to `d` the word at `(b, x, sc)`. -/
theorem evalInstrA_loadMemIdx_regs (sa : AState) (d b x : String) (sc : Nat) :
    (evalInstrA sa (.loadMemIdx d b x sc)).regs d =
      read64 sa.mem (eaVal sa (.indexed b x sc)) := by
  simp [evalInstrA, evalInstr, JState.setReg, JState.loadIdx, JState.get, AState.view, x86_MOV,
    eaVal, EA.indexed, EA.idxVal, ofInt_scale']

/-- `storeMem b off src` writes the value of `src` at `off(b)`. -/
theorem evalInstrA_storeMem_mem (sa : AState) (b : String) (off : Int) (src : JOperand) :
    (evalInstrA sa (.storeMem b off src)).mem =
      write64 sa.mem (eaVal sa (.cell b off)) (src.eval sa.view) := by
  rw [evalInstrA_mem]; rfl

/-- `storeMemIdx b x sc src` writes the value of `src` at `(b, x, sc)`. -/
theorem evalInstrA_storeMemIdx_mem (sa : AState) (b x : String) (sc : Nat) (src : JOperand) :
    (evalInstrA sa (.storeMemIdx b x sc src)).mem =
      write64 sa.mem (eaVal sa (.indexed b x sc)) (src.eval sa.view) := by
  rw [evalInstrA_mem]; rfl

/-- `lea d b x sc off` writes to `d` the address of `off(b, x, sc)`, and no memory. -/
theorem evalInstrA_lea_regs (sa : AState) (d b x : String) (sc : Nat) (off : Int) :
    (evalInstrA sa (.lea d b x sc off)).regs d = eaVal sa (.sib b x sc off) ∧
      (evalInstrA sa (.lea d b x sc off)).mem = sa.mem := by
  refine ⟨?_, by rw [evalInstrA_mem]; rfl⟩
  rw [eaVal_sib]
  simp [evalInstrA, evalInstr, JState.setReg, JState.get, AState.view, x86_LEA]

/-! ## Alignment -/

/-- The address is a multiple of eight. -/
def Aligned8 (a : BitVec 64) : Prop := a.toNat % 8 = 0

instance (a : BitVec 64) : Decidable (Aligned8 a) :=
  inferInstanceAs (Decidable (a.toNat % 8 = 0))

/-- The eight bytes of an aligned word do not wrap around the address space. -/
theorem aligned8_no_wrap {a : BitVec 64} (ha : Aligned8 a) : a.toNat + 8 ≤ 2 ^ 64 := by
  have := a.isLt
  simp only [Aligned8] at ha
  omega

/-- Two aligned words coincide or share no byte. -/
theorem aligned8_eq_or_disjoint8 {a b : BitVec 64} (ha : Aligned8 a) (hb : Aligned8 b) :
    a = b ∨ Disjoint8 a b := by
  by_cases h : a = b
  · exact Or.inl h
  · right
    have hne : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    have := a.isLt
    have := b.isLt
    simp only [Aligned8] at ha hb
    simp only [Disjoint8, BitVec.toNat_sub]
    constructor <;> omega

/-- A write to an aligned word leaves every other aligned word unchanged. -/
theorem read64_write64_of_aligned_ne (m : AMem) {a b : BitVec 64} (v : BitVec 64)
    (ha : Aligned8 a) (hb : Aligned8 b) (h : a ≠ b) :
    read64 (write64 m a v) b = read64 m b :=
  read64_write64_of_disjoint m a b v ((aligned8_eq_or_disjoint8 ha hb).resolve_left h)

theorem aligned8_add {a b : BitVec 64} (ha : Aligned8 a) (hb : Aligned8 b) :
    Aligned8 (a + b) := by
  simp only [Aligned8, BitVec.toNat_add] at *
  omega

/-- An operand with an aligned base, scale `8` on its index and a displacement that is a
    multiple of eight denotes an aligned address. -/
theorem eaVal_aligned (sa : AState) (e : EA) (hb : Aligned8 (sa.regs e.base))
    (hi : ∀ p, e.index = some p → p.2 = 8) (hd : e.disp % 8 = 0) :
    Aligned8 (eaVal sa e) := by
  refine aligned8_add (aligned8_add hb ?_) ?_
  · cases hx : e.index with
    | none => simp [EA.idxVal, Aligned8]
    | some p =>
      obtain ⟨x, sc⟩ := p
      have hsc : sc = 8 := hi _ hx
      subst hsc
      simp only [EA.idxVal, Aligned8, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
  · simp only [Aligned8, BitVec.toNat_ofInt]
    omega

end CatCrypt.Crypto.SecureCompilation.X86Backend.EffAddr
