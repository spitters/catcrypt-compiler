/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# An address-memory machine for `JInstr 64` and its simulation of `runBlock`

`runBlock` keys memory by the name of the base register: `JState.mem b o` is the word at
`[b + o]` whatever address `b` holds, so two names are two separate banks and a register
copy does not move a bank. This module defines a machine whose memory is addressed by
value, and relates the two machines.

`runBlockA` runs a block over `AState`: registers and flags as in `JState`, and a byte
memory `AMem = BitVec 64 → BitVec 8`. A memory operand `[b + o]` addresses the eight
bytes from `regs b + o`, read and written little-endian (`read64`, `write64`). Registers
and flags are computed by `evalInstr` on `AState.view`, the name-keyed state whose bank
`b` is the memory seen from the current value of `b`, so the two machines share one
instruction semantics; the stored word of a memory write goes to the addressed bytes.
`loadSym` has no address meaning in this machine: it writes the marker word that
`evalInstr` writes, and the discipline below rejects it.

## The discipline

`disciplinedB bank blk` is a static check over a pointer map `bank`, which sends a bank
name to the entry register whose value is that bank's base address. It tracks, for each
register, the entry register whose value the register still holds (a `TagMap`:
`mov d, s` copies the tag of `s` to `d`, and any other write to `d` clears it). It accepts
the block when every memory operand is a compile-time displacement `[b + o]` whose base
`b` holds, at that instruction, the entry value `bank b` names. Under it, each access
addresses `keyAddr bank P (b, o) = P (bank b) + o` for the entry registers `P`
(`TagInv`).

`readsBeforeWritesFromB K false blk` accepts a block in which every memory read either
precedes every memory write or reads a cell in `K`. With `K = []` it states that all
reads precede all writes (`readsPrecedeWritesB`); with `K = writeKeys blk`
(`readsBeforeWritesB`) it also admits a block that reads back a cell it writes.

## Main definitions

* `read64`, `write64`, `InRange8`, `Disjoint8`: eight-byte little-endian access, and
  membership in and disjointness of eight-byte ranges modulo `2^64`.
* `AState`, `AState.view`, `evalInstrA`, `runBlockA`: the address-memory machine.
* `readKey`, `writeKey`, `writeKeys`, `footprint`, `dsts`: the memory cells an instruction
  or a block reads and writes, as `(base, offset)` pairs, and the registers an instruction
  may write.
* `TagMap`, `stepTags`, `disciplinedB`, `readsBeforeWritesFromB`, `readsBeforeWritesB`,
  `readsPrecedeWritesB`: the decidable conditions.
* `absMem`, `jOf`, `keyAddr`, `Separated`: the name-keyed view of an address memory at
  the entry pointers, the name-keyed state it induces, the address of a cell, and pairwise
  disjointness of a set of cells.

## Main results

* `read64_write64_same`, `read64_write64_of_disjoint`: the byte-memory laws.
* `runBlockA_sim_on`: under the discipline, for a pairwise separated cell set `K` that
  contains every written cell and every cell read after the first write,
  `runBlockA sa blk` and `runBlock (jOf bank sa) blk` end with equal registers and flags,
  and every cell of `K` reads back through `absMem` as the name-keyed run leaves it.
* `runBlockA_sim`: the case `K = footprint blk`, for a block whose accessed cells are
  pairwise separated.
* `runBlockA_sim_readsBeforeWrites`: the case `K = writeKeys blk`. Only the written cells
  need to be separated from one another; an input cell may coincide with or partly overlap
  an output cell.
* `runBlockA_mem_frame`: under the discipline, a byte outside every written range keeps
  its value.
* `separated_sameBase`: cells at one base with offsets at least eight apart are separated.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## Byte memory -/

/-- A byte memory over the 64-bit address space. -/
abbrev AMem := BitVec 64 → BitVec 8

/-- The little-endian word stored in the eight bytes from address `a`. -/
def read64 (m : AMem) (a : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((m a).toNat + 2 ^ 8 * (m (a + BitVec.ofNat 64 1)).toNat
    + 2 ^ 16 * (m (a + BitVec.ofNat 64 2)).toNat + 2 ^ 24 * (m (a + BitVec.ofNat 64 3)).toNat
    + 2 ^ 32 * (m (a + BitVec.ofNat 64 4)).toNat + 2 ^ 40 * (m (a + BitVec.ofNat 64 5)).toNat
    + 2 ^ 48 * (m (a + BitVec.ofNat 64 6)).toNat + 2 ^ 56 * (m (a + BitVec.ofNat 64 7)).toNat)

/-- `x` lies in the eight bytes from `a`, modulo `2^64`. -/
def InRange8 (a x : BitVec 64) : Prop := (x - a).toNat < 8

instance (a x : BitVec 64) : Decidable (InRange8 a x) :=
  inferInstanceAs (Decidable ((x - a).toNat < 8))

/-- Store the word `v` little-endian in the eight bytes from address `a`: the byte at
    `a + k` is byte `k` of `v`. -/
def write64 (m : AMem) (a v : BitVec 64) : AMem := fun x =>
  if InRange8 a x then BitVec.ofNat 8 (v.toNat / 2 ^ (8 * (x - a).toNat)) else m x

/-- The eight-byte ranges from `a` and from `b` are disjoint modulo `2^64`. -/
def Disjoint8 (a b : BitVec 64) : Prop := 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat

theorem write64_of_not_inRange (m : AMem) (a v x : BitVec 64) (h : ¬ InRange8 a x) :
    write64 m a v x = m x := by
  simp only [write64, ite_eq_right h]

theorem toNat_add_sub_self (a : BitVec 64) (k : Nat) (hk : k < 8) :
    (a + BitVec.ofNat 64 k - a).toNat = k := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem write64_add (m : AMem) (a v : BitVec 64) (k : Nat) (hk : k < 8) :
    write64 m a v (a + BitVec.ofNat 64 k) = BitVec.ofNat 8 (v.toNat / 2 ^ (8 * k)) := by
  simp only [write64, InRange8, toNat_add_sub_self a k hk, ite_eq_left hk]

/-- Reading back the eight bytes just written returns the stored word. -/
theorem read64_write64_same (m : AMem) (a v : BitVec 64) : read64 (write64 m a v) a = v := by
  have h0 : write64 m a v a = BitVec.ofNat 8 (v.toNat / 2 ^ (8 * 0)) := by
    simpa using write64_add m a v 0 (by decide)
  simp only [read64, h0, write64_add m a v 1 (by decide), write64_add m a v 2 (by decide),
    write64_add m a v 3 (by decide), write64_add m a v 4 (by decide),
    write64_add m a v 5 (by decide), write64_add m a v 6 (by decide),
    write64_add m a v 7 (by decide)]
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp only [BitVec.toNat_ofNat, Nat.reduceMul, Nat.reducePow, Nat.div_one]
  omega

theorem not_inRange_of_disjoint (a b : BitVec 64) (k : Nat) (h : Disjoint8 a b) (hk : k < 8) :
    ¬ InRange8 a (b + BitVec.ofNat 64 k) := by
  obtain ⟨h1, h2⟩ := h
  simp only [InRange8, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h1 h2 ⊢
  have := a.isLt
  have := b.isLt
  omega

/-- A write to a disjoint eight-byte range does not change the word read at `b`. -/
theorem read64_write64_of_disjoint (m : AMem) (a b v : BitVec 64) (h : Disjoint8 a b) :
    read64 (write64 m a v) b = read64 m b := by
  have h0 : ¬ InRange8 a b := by
    simpa using not_inRange_of_disjoint a b 0 h (by decide)
  simp only [read64, write64_of_not_inRange _ _ _ _ h0,
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 1 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 2 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 3 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 4 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 5 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 6 h (by decide)),
    write64_of_not_inRange _ _ _ _ (not_inRange_of_disjoint a b 7 h (by decide))]

theorem Disjoint8.symm {a b : BitVec 64} (h : Disjoint8 a b) : Disjoint8 b a := ⟨h.2, h.1⟩

/-- Two displacements from one base, at least eight apart and at most `2^64 - 8` apart,
    give disjoint eight-byte ranges. -/
theorem disjoint8_add_ofInt (p : BitVec 64) (o o' : Int) (h : 8 ≤ (o - o').natAbs)
    (h' : (o - o').natAbs ≤ 2 ^ 64 - 8) :
    Disjoint8 (p + BitVec.ofInt 64 o) (p + BitVec.ofInt 64 o') := by
  have := p.isLt
  simp only [Disjoint8, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt]
  constructor <;> omega

/-! ## The address-memory machine -/

/-- A machine state with address-keyed byte memory: registers and flags as in `JState`. -/
structure AState where
  /-- The register file. -/
  regs : String → BitVec 64
  /-- The five flags. -/
  flags : RFlags := {}
  /-- The byte memory. -/
  mem : AMem

/-- The name-keyed state an address state presents to `evalInstr`: bank `b` at offset `o`
    is the word at address `regs b + o`. -/
def AState.view (sa : AState) : JState 64 :=
  { regs := sa.regs
    flags := sa.flags
    mem := fun b o => read64 sa.mem (sa.regs b + BitVec.ofInt 64 o) }

/-- The word a memory-writing instruction stores; `0` for the others. -/
def writeVal (s : JState 64) : JInstr 64 → BitVec 64
  | .storeMem _ _ src => src.eval s
  | .storeMemIdx _ _ _ src => src.eval s
  | .addToMem b o src => (x86_ADD (s.load b o) (src.eval s)).word
  | _ => 0

/-- The address a memory-writing instruction stores to, from the current registers. -/
def writeAddr (sa : AState) : JInstr 64 → Option (BitVec 64)
  | .storeMem b o _ => some (sa.regs b + BitVec.ofInt 64 o)
  | .addToMem b o _ => some (sa.regs b + BitVec.ofInt 64 o)
  | .storeMemIdx b idx sc _ =>
      some (sa.regs b + BitVec.ofInt 64 ((sc * (sa.regs idx).toNat : Nat) : Int))
  | _ => none

/-- One instruction over address memory: registers and flags as `evalInstr` computes them
    on the view, and the stored word written to the addressed eight bytes. -/
def evalInstrA (sa : AState) (i : JInstr 64) : AState :=
  { regs := (evalInstr sa.view i).regs
    flags := (evalInstr sa.view i).flags
    mem := match writeAddr sa i with
      | some a => write64 sa.mem a (writeVal sa.view i)
      | none => sa.mem }

/-- `runBlockA`: the straight-line fold of `evalInstrA`. -/
def runBlockA (sa : AState) : List (JInstr 64) → AState
  | [] => sa
  | i :: is => runBlockA (evalInstrA sa i) is

@[simp] theorem runBlockA_nil (sa : AState) : runBlockA sa [] = sa := rfl

@[simp] theorem runBlockA_cons (sa : AState) (i : JInstr 64) (is : List (JInstr 64)) :
    runBlockA sa (i :: is) = runBlockA (evalInstrA sa i) is := rfl

theorem runBlockA_append (sa : AState) (xs ys : List (JInstr 64)) :
    runBlockA sa (xs ++ ys) = runBlockA (runBlockA sa xs) ys := by
  induction xs generalizing sa with
  | nil => rfl
  | cons i is ih => exact ih (evalInstrA sa i)

/-! ## Memory cells and register writes of an instruction -/

/-- The cell `(base, offset)` an instruction reads at a compile-time displacement. -/
def readKey : JInstr 64 → Option (String × Int)
  | .loadMem _ b o => some (b, o)
  | .mulxMem _ _ _ b o => some (b, o)
  | .addMem _ b o => some (b, o)
  | .addToMem b o _ => some (b, o)
  | .adcxMem _ b o => some (b, o)
  | .adoxMem _ b o => some (b, o)
  | .imulMem _ b o => some (b, o)
  | .imulriMem _ b o _ => some (b, o)
  | .cmpMem _ b o => some (b, o)
  | .cmovccMem _ _ b o => some (b, o)
  | .aluMem _ _ b o => some (b, o)
  | .andnMem _ _ b o => some (b, o)
  | _ => none

/-- The cell `(base, offset)` an instruction writes at a compile-time displacement. -/
def writeKey : JInstr 64 → Option (String × Int)
  | .storeMem b o _ => some (b, o)
  | .addToMem b o _ => some (b, o)
  | _ => none

/-- The instruction's memory operands, if any, are compile-time displacements: the
    indexed forms and `loadSym` are excluded. -/
def addrFormB : JInstr 64 → Bool
  | .loadMemIdx .. => false
  | .storeMemIdx .. => false
  | .loadSym .. => false
  | _ => true

/-- The cells a block writes, in order. -/
def writeKeys (blk : List (JInstr 64)) : List (String × Int) := blk.filterMap writeKey

/-- The cells a block reads or writes. -/
def footprint (blk : List (JInstr 64)) : List (String × Int) :=
  blk.filterMap readKey ++ writeKeys blk

/-- The registers an instruction may write. -/
def dsts : JInstr 64 → List String
  | .mov d _ | .add d _ | .sub d _ | .adc d _ | .sbb d _ | .imul d _ | .neg d | .setc d
  | .and_ d _ | .not_ d | .andn d _ _ | .rol d _ | .ror d _ | .rorx d _ _ | .shlx d _ _
  | .shrx d _ _ | .sarx d _ _ | .movzx d _ _ | .movsx d _ _ | .lea d _ _ _ _ | .or_ d _
  | .xor_ d _ | .shl d _ | .shr d _ | .sar d _ | .cmove d _ | .cmovne d _ | .cmovb d _
  | .adcx d _ | .adox d _ | .loadMem d _ _ | .loadMemIdx d _ _ _ | .loadSym d _ | .inc d
  | .dec d | .imulri d _ _ | .shld d _ _ | .shrd d _ _ | .rcl d _ | .rcr d _
  | .cmovcc _ d _ | .setcc _ d | .btr d _ | .bts d _ | .addMem d _ _ | .adcxMem d _ _
  | .adoxMem d _ _ | .imulMem d _ _ | .imulriMem d _ _ _ | .cmovccMem _ d _ _ | .bzhi d _ _
  | .aluMem _ d _ _ | .andnMem d _ _ _ => [d]
  | .mulx h l _ _ | .mulxMem h l _ _ _ | .xchg h l | .mul h l _ | .imulWide h l _ => [h, l]
  | .test .. | .cmp .. | .testN .. | .bt .. | .clc | .stc | .storeMem .. | .storeMemIdx ..
  | .addToMem .. | .cmpMem .. => []

/-- The source register of a register-to-register `mov`. -/
def movSrc : JInstr 64 → Option (String × String)
  | .mov d (.reg s) => some (d, s)
  | _ => none

theorem eq_of_movSrc {i : JInstr 64} {d s : String} (h : movSrc i = some (d, s)) :
    i = .mov d (.reg s) := by
  cases i <;> simp_all [movSrc]
  split at h <;> simp_all

/-- A register outside `dsts i` keeps its value. -/
theorem evalInstr_regs_of_not_mem_dsts (s : JState 64) (i : JInstr 64) (r : String)
    (h : r ∉ dsts i) : (evalInstr s i).regs r = s.regs r := by
  cases i <;> simp_all [dsts, evalInstr, JState.setReg, JState.writeB5W, JState.writeB2W,
    JState.writeB4W, JState.writeB5W2, JState.writeCFW, JState.writeB5, JState.writeB5N,
    JState.writeB5Mem, JState.setRegMerge, JState.storeIdx, JState.store, JState.get,
    x86_XCHG]

/-- `evalInstr` reads memory only at `readKey`: two states agreeing on registers, flags
    and that cell agree on the resulting registers, flags and stored word. -/
theorem evalInstr_congr (s s' : JState 64) (i : JInstr 64) (hf : addrFormB i = true)
    (hr : s.regs = s'.regs) (hfl : s.flags = s'.flags)
    (hm : ∀ k, readKey i = some k → s.mem k.1 k.2 = s'.mem k.1 k.2) :
    (evalInstr s i).regs = (evalInstr s' i).regs ∧
      (evalInstr s i).flags = (evalInstr s' i).flags ∧ writeVal s i = writeVal s' i := by
  obtain ⟨R, F, M⟩ := s
  obtain ⟨R', F', M'⟩ := s'
  simp only at hr hfl
  subst hr hfl
  cases i <;> simp only [addrFormB, readKey, Option.some.injEq, forall_eq',
      Bool.false_eq_true] at hf hm <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | (refine ⟨?_, ?_, ?_⟩ <;> simp only [evalInstr, writeVal, JState.load, hm] <;> rfl)

/-- The name-keyed memory after an instruction: the stored word at `writeKey`, and the
    memory unchanged otherwise. -/
theorem evalInstr_mem (s : JState 64) (i : JInstr 64) (hf : addrFormB i = true) :
    (evalInstr s i).mem = match writeKey i with
      | some k => fun b o => if b = k.1 ∧ o = k.2 then writeVal s i else s.mem b o
      | none => s.mem := by
  cases i <;> simp only [addrFormB, Bool.false_eq_true] at hf <;> rfl

theorem writeAddr_eq (sa : AState) (i : JInstr 64) (hf : addrFormB i = true) :
    writeAddr sa i = (writeKey i).map (fun k => sa.regs k.1 + BitVec.ofInt 64 k.2) := by
  cases i <;> simp only [addrFormB, Bool.false_eq_true] at hf <;> rfl

/-! ## Pointer tags and the discipline -/

/-- For each listed register, the entry register whose value it holds (`some e`) or no
    tracked value (`none`); a register not listed holds its own entry value. -/
abbrev TagMap := List (String × Option String)

/-- The tag of register `r`. -/
def TagMap.get : TagMap → String → Option String
  | [], r => some r
  | (k, v) :: t, r => if r = k then v else TagMap.get t r

/-- Set the tag of register `d`, dropping its earlier entry. -/
def TagMap.set (t : TagMap) (d : String) (v : Option String) : TagMap :=
  (d, v) :: t.filter (fun p => p.1 != d)

theorem TagMap.get_filter (t : TagMap) (d r : String) (h : r ≠ d) :
    TagMap.get (t.filter (fun p => p.1 != d)) r = TagMap.get t r := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = d
    · subst hk
      have hrk : r ≠ k := h
      simp [List.filter, TagMap.get, hrk, ih]
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      simp only [TagMap.get, ih]

theorem TagMap.get_set (t : TagMap) (d r : String) (v : Option String) :
    (t.set d v).get r = if r = d then v else t.get r := by
  by_cases h : r = d
  · simp [TagMap.set, TagMap.get, h]
  · simp only [TagMap.set, TagMap.get, ite_eq_right h]
    exact TagMap.get_filter t d r h

/-- Clear the tags of the registers `ds`. -/
def TagMap.killAll (t : TagMap) (ds : List String) : TagMap :=
  ds.foldl (fun t d => t.set d none) t

theorem TagMap.get_killAll (ds : List String) (t : TagMap) (r : String) :
    (t.killAll ds).get r = if r ∈ ds then none else t.get r := by
  induction ds generalizing t with
  | nil => simp [TagMap.killAll]
  | cons d ds ih =>
    have e : (t.killAll (d :: ds)) = (t.set d none).killAll ds := rfl
    rw [e, ih, TagMap.get_set]
    by_cases h1 : r ∈ ds <;> by_cases h2 : r = d <;> simp [h1, h2]

/-- The tags after an instruction: `mov d, s` gives `d` the tag of `s`; every other
    register the instruction may write loses its tag. -/
def stepTags (t : TagMap) (i : JInstr 64) : TagMap :=
  match movSrc i with
  | some (d, s) => t.set d (t.get s)
  | none => t.killAll (dsts i)

/-- The base `b` is a bank of `bank` and holds, under the tags `t`, the entry value that
    `bank b` names. -/
def baseOKB (bank : String → Option String) (t : TagMap) (b : String) : Bool :=
  (bank b).isSome && decide (bank b = t.get b)

/-- `baseOKB` for the base of an optional cell. -/
def keyOKB (bank : String → Option String) (t : TagMap) : Option (String × Int) → Bool
  | some k => baseOKB bank t k.1
  | none => true

/-- The instruction's memory operands are compile-time displacements through bases that
    satisfy `baseOKB`. -/
def accessOKB (bank : String → Option String) (t : TagMap) (i : JInstr 64) : Bool :=
  addrFormB i && keyOKB bank t (readKey i) && keyOKB bank t (writeKey i)

/-- `accessOKB` at every instruction, with the tags propagated by `stepTags`. -/
def disciplinedFromB (bank : String → Option String) : TagMap → List (JInstr 64) → Bool
  | _, [] => true
  | t, i :: is => accessOKB bank t i && disciplinedFromB bank (stepTags t i) is

/-- The discipline from the entry state, where every register holds its own entry value. -/
def disciplinedB (bank : String → Option String) (blk : List (JInstr 64)) : Bool :=
  disciplinedFromB bank [] blk

/-- A read of cell `k` is admitted when no write has occurred (`seen = false`) or
    `k ∈ K`. -/
def readOKB (K : List (String × Int)) (seen : Bool) : Option (String × Int) → Bool
  | some k => !seen || decide (k ∈ K)
  | none => true

/-- Every memory read of the block either precedes every memory write (counting from a
    state where a write has occurred iff `seen`) or reads a cell in `K`. An instruction
    that reads and writes one cell reads it first. -/
def readsBeforeWritesFromB (K : List (String × Int)) : Bool → List (JInstr 64) → Bool
  | _, [] => true
  | seen, i :: is =>
      readOKB K seen (readKey i) && readsBeforeWritesFromB K (seen || (writeKey i).isSome) is

/-- Every memory read precedes every memory write or reads a cell the block writes. -/
def readsBeforeWritesB (blk : List (JInstr 64)) : Bool :=
  readsBeforeWritesFromB (writeKeys blk) false blk

/-- Every memory read precedes every memory write. -/
def readsPrecedeWritesB (blk : List (JInstr 64)) : Bool :=
  readsBeforeWritesFromB [] false blk

theorem readsBeforeWritesFromB_mono {K K' : List (String × Int)} (hK : ∀ k ∈ K, k ∈ K') :
    ∀ (blk : List (JInstr 64)) (seen : Bool),
      readsBeforeWritesFromB K seen blk = true → readsBeforeWritesFromB K' seen blk = true := by
  intro blk
  induction blk with
  | nil => intro _ _; rfl
  | cons i is ih =>
    intro seen h
    simp only [readsBeforeWritesFromB, Bool.and_eq_true] at h ⊢
    refine ⟨?_, ih _ h.2⟩
    have h1 := h.1
    cases hr : readKey i with
    | none => rfl
    | some k =>
      rw [hr] at h1
      simp only [readOKB, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_true_eq] at h1 ⊢
      exact h1.imp_right (hK k)

theorem readsBeforeWritesB_of_readsPrecedeWritesB (blk : List (JInstr 64))
    (h : readsPrecedeWritesB blk = true) : readsBeforeWritesB blk = true :=
  readsBeforeWritesFromB_mono (by simp) blk false h

theorem readsBeforeWritesFromB_of_reads {K : List (String × Int)} :
    ∀ (blk : List (JInstr 64)), (∀ k ∈ blk.filterMap readKey, k ∈ K) →
      ∀ seen, readsBeforeWritesFromB K seen blk = true := by
  intro blk
  induction blk with
  | nil => intro _ _; rfl
  | cons i is ih =>
    intro h seen
    simp only [readsBeforeWritesFromB, Bool.and_eq_true]
    refine ⟨?_, ih (fun k hk => h k (List.mem_filterMap.2 ?_)) _⟩
    · cases hr : readKey i with
      | none => rfl
      | some k =>
        have : k ∈ K := h k (by simp [hr])
        simp [readOKB, this]
    · obtain ⟨j, hj, hjk⟩ := List.mem_filterMap.1 hk
      exact ⟨j, List.mem_cons_of_mem _ hj, hjk⟩

/-! ## The name-keyed view of an address memory -/

/-- Under the tags `t`, every register tagged `e` holds the entry value `P e`. -/
def TagInv (t : TagMap) (P R : String → BitVec 64) : Prop :=
  ∀ r e, t.get r = some e → R r = P e

theorem tagInv_nil (P : String → BitVec 64) : TagInv [] P P := by
  intro r e h
  simp only [TagMap.get, Option.some.injEq] at h
  rw [h]

/-- The base address of bank `b`: the entry value of the register `bank b` names. -/
def basePtr (bank : String → Option String) (P : String → BitVec 64) (b : String) :
    BitVec 64 :=
  match bank b with
  | some e => P e
  | none => 0

/-- The address of the cell `(b, o)`. -/
def keyAddr (bank : String → Option String) (P : String → BitVec 64) (k : String × Int) :
    BitVec 64 :=
  basePtr bank P k.1 + BitVec.ofInt 64 k.2

/-- The name-keyed memory an address memory presents at the entry pointers: bank `b` at
    offset `o` is the word at `keyAddr bank P (b, o)`. -/
def absMem (bank : String → Option String) (P : String → BitVec 64) (m : AMem) : JMem 64 :=
  fun b o => read64 m (keyAddr bank P (b, o))

/-- The name-keyed state of an address state, with the entry pointers read from its own
    registers. -/
def jOf (bank : String → Option String) (sa : AState) : JState 64 :=
  { regs := sa.regs, flags := sa.flags, mem := absMem bank sa.regs sa.mem }

/-- Distinct cells of `K` occupy disjoint eight-byte ranges. -/
def Separated (bank : String → Option String) (P : String → BitVec 64)
    (K : List (String × Int)) : Prop :=
  ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → Disjoint8 (keyAddr bank P k) (keyAddr bank P k')

theorem regs_eq_basePtr {bank : String → Option String} {t : TagMap}
    {P R : String → BitVec 64} {b : String} (hb : baseOKB bank t b = true)
    (hinv : TagInv t P R) : R b = basePtr bank P b := by
  simp only [baseOKB, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hs, heq⟩ := hb
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hs
  rw [basePtr, he]
  exact hinv b e (heq ▸ he)

/-- `stepTags` preserves the tag invariant across one instruction. -/
theorem tagInv_step (t : TagMap) (P : String → BitVec 64) (s : JState 64) (i : JInstr 64)
    (h : TagInv t P s.regs) : TagInv (stepTags t i) P (evalInstr s i).regs := by
  intro r e hr
  unfold stepTags at hr
  cases hm : movSrc i with
  | some ds =>
    obtain ⟨d, src⟩ := ds
    simp only [hm, TagMap.get_set] at hr
    rw [eq_of_movSrc hm]
    by_cases hrd : r = d
    · rw [ite_eq_left hrd] at hr
      subst hrd
      simp only [evalInstr, JState.setReg, x86_MOV, JOperand.eval, JState.get, ite_eq_left]
      exact h _ _ hr
    · rw [ite_eq_right hrd] at hr
      simp only [evalInstr, JState.setReg, ite_eq_right hrd]
      exact h _ _ hr
  | none =>
    simp only [hm, TagMap.get_killAll] at hr
    split at hr
    · simp at hr
    · rw [evalInstr_regs_of_not_mem_dsts s i r ‹_›]
      exact h _ _ hr

theorem view_mem_eq {bank : String → Option String} {t : TagMap} {P : String → BitVec 64}
    {sa : AState} {b : String} (o : Int) (hb : baseOKB bank t b = true)
    (hinv : TagInv t P sa.regs) : sa.view.mem b o = absMem bank P sa.mem b o := by
  simp only [AState.view, absMem, keyAddr, regs_eq_basePtr hb hinv]

theorem absMem_write (bank : String → Option String) (P : String → BitVec 64) (m : AMem)
    (v : BitVec 64) {K : List (String × Int)} (hsep : Separated bank P K)
    {k k' : String × Int} (hk : k ∈ K) (hk' : k' ∈ K) :
    absMem bank P (write64 m (keyAddr bank P k) v) k'.1 k'.2 =
      if k' = k then v else absMem bank P m k'.1 k'.2 := by
  by_cases h : k' = k
  · subst h
    simp only [absMem, ite_eq_left]
    exact read64_write64_same m _ v
  · rw [ite_eq_right h]
    exact read64_write64_of_disjoint _ _ _ _ (hsep k hk k' hk' (Ne.symm h))

theorem mem_writeKeys_cons {i : JInstr 64} {is : List (JInstr 64)} {k : String × Int} :
    k ∈ writeKeys (i :: is) ↔ writeKey i = some k ∨ k ∈ writeKeys is := by
  simp only [writeKeys, List.filterMap_cons]
  cases writeKey i <;> simp [eq_comm]

/-! ## The simulation -/

/-- The simulation invariant carried through a block: equal registers and flags, the tag
    invariant, agreement on the cells of `K`, and, before the first write, equal
    memories. -/
theorem runBlockA_sim_core (bank : String → Option String) (P : String → BitVec 64)
    (K : List (String × Int)) (hsep : Separated bank P K) :
    ∀ (blk : List (JInstr 64)) (t : TagMap) (seen : Bool) (sa : AState) (js : JState 64),
      disciplinedFromB bank t blk = true → readsBeforeWritesFromB K seen blk = true →
      (∀ k ∈ writeKeys blk, k ∈ K) →
      sa.regs = js.regs → sa.flags = js.flags → TagInv t P sa.regs →
      (∀ k ∈ K, absMem bank P sa.mem k.1 k.2 = js.mem k.1 k.2) →
      (seen = false → js.mem = absMem bank P sa.mem) →
      (runBlockA sa blk).regs = (runBlock js blk).regs ∧
        (runBlockA sa blk).flags = (runBlock js blk).flags ∧
        ∀ k ∈ K, absMem bank P (runBlockA sa blk).mem k.1 k.2 = (runBlock js blk).mem k.1 k.2 := by
  intro blk
  induction blk with
  | nil => intro _ _ _ _ _ _ _ hr hf _ hK _; exact ⟨hr, hf, hK⟩
  | cons i is ih =>
    intro t seen sa js hd hrw hW hr hf hinv hK hpre
    simp only [disciplinedFromB, accessOKB, Bool.and_eq_true] at hd
    obtain ⟨⟨⟨hform, hrk⟩, hwk⟩, hd⟩ := hd
    simp only [readsBeforeWritesFromB, Bool.and_eq_true] at hrw
    obtain ⟨hrd, hrw⟩ := hrw
    have hW' : ∀ k ∈ writeKeys is, k ∈ K := fun k hk => hW k (mem_writeKeys_cons.2 (Or.inr hk))
    have hread : ∀ k, readKey i = some k → sa.view.mem k.1 k.2 = js.mem k.1 k.2 := by
      intro k hk
      rw [hk] at hrk hrd
      rw [view_mem_eq k.2 hrk hinv]
      cases seen with
      | false => rw [hpre rfl]
      | true =>
        simp only [readOKB, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hrd
        exact hK k hrd
    obtain ⟨hcr, hcf, hcw⟩ := evalInstr_congr sa.view js i hform hr hf hread
    simp only [runBlockA_cons, runBlock_cons]
    refine ih (stepTags t i) _ (evalInstrA sa i) (evalInstr js i) hd hrw hW' hcr hcf
      (tagInv_step t P sa.view i hinv) ?_ ?_
    · intro k' hk'
      rw [evalInstr_mem js i hform]
      simp only [evalInstrA, writeAddr_eq sa i hform]
      cases hwi : writeKey i with
      | none => exact hK k' hk'
      | some k =>
        have hkK : k ∈ K := hW k (mem_writeKeys_cons.2 (Or.inl hwi))
        rw [hwi] at hwk
        simp only [keyOKB] at hwk
        simp only [Option.map_some]
        rw [regs_eq_basePtr hwk hinv, hcw]
        change absMem bank P (write64 sa.mem (keyAddr bank P k) (writeVal js i)) k'.1 k'.2 = _
        rw [absMem_write bank P sa.mem _ hsep hkK hk']
        by_cases h : k' = k
        · subst h
          simp
        · have h' : ¬ (k'.1 = k.1 ∧ k'.2 = k.2) := fun ⟨h1, h2⟩ => h (Prod.ext h1 h2)
          rw [ite_eq_right h, ite_eq_right h']
          exact hK k' hk'
    · intro hs
      simp only [Bool.or_eq_false_iff] at hs
      obtain ⟨rfl, hnw⟩ := hs
      have hnone : writeKey i = none := Option.not_isSome_iff_eq_none.1 (by simp [hnw])
      rw [evalInstr_mem js i hform]
      simp only [evalInstrA, writeAddr_eq sa i hform, hnone, Option.map_none]
      exact hpre rfl

/-- **Simulation on a cell set.** Under the discipline, let `K` be a pairwise separated set
    of cells that contains every cell the block writes and every cell the block reads after
    its first write. Then `runBlockA sa blk` and `runBlock (jOf bank sa) blk` end with equal
    registers and flags, and every cell of `K` reads back, at the entry pointers, as the
    name-keyed run leaves it. -/
theorem runBlockA_sim_on (bank : String → Option String) (blk : List (JInstr 64))
    (K : List (String × Int)) (hd : disciplinedB bank blk = true)
    (hrw : readsBeforeWritesFromB K false blk = true) (hW : ∀ k ∈ writeKeys blk, k ∈ K)
    (sa : AState) (hsep : Separated bank sa.regs K) :
    (runBlockA sa blk).regs = (runBlock (jOf bank sa) blk).regs ∧
      (runBlockA sa blk).flags = (runBlock (jOf bank sa) blk).flags ∧
      ∀ k ∈ K, absMem bank sa.regs (runBlockA sa blk).mem k.1 k.2 =
        (runBlock (jOf bank sa) blk).mem k.1 k.2 :=
  runBlockA_sim_core bank sa.regs K hsep blk [] false sa (jOf bank sa) hd hrw hW rfl rfl
    (tagInv_nil sa.regs) (fun _ _ => rfl) (fun _ => rfl)

/-- **Simulation for a separated footprint.** Under the discipline, when the cells the
    block reads or writes occupy pairwise disjoint ranges, the address machine and the
    name-keyed machine end with equal registers and flags, and agree on every cell of the
    footprint. -/
theorem runBlockA_sim (bank : String → Option String) (blk : List (JInstr 64))
    (hd : disciplinedB bank blk = true) (sa : AState)
    (hsep : Separated bank sa.regs (footprint blk)) :
    (runBlockA sa blk).regs = (runBlock (jOf bank sa) blk).regs ∧
      (runBlockA sa blk).flags = (runBlock (jOf bank sa) blk).flags ∧
      ∀ k ∈ footprint blk, absMem bank sa.regs (runBlockA sa blk).mem k.1 k.2 =
        (runBlock (jOf bank sa) blk).mem k.1 k.2 :=
  runBlockA_sim_on bank blk _ hd
    (readsBeforeWritesFromB_of_reads blk (fun _ hk => List.mem_append_left _ hk) false)
    (fun _ hk => List.mem_append_right _ hk) sa hsep

/-- **Simulation when reads come first.** Under the discipline, for a block whose memory
    reads all precede its memory writes or read cells it writes, only the written cells
    need to be separated from one another. Input cells may coincide with or partly overlap
    output cells: the address machine ends with the registers and flags of the name-keyed
    run on the entry memory, and every written cell holds what that run stores there. -/
theorem runBlockA_sim_readsBeforeWrites (bank : String → Option String)
    (blk : List (JInstr 64)) (hd : disciplinedB bank blk = true)
    (hrw : readsBeforeWritesB blk = true) (sa : AState)
    (hsep : Separated bank sa.regs (writeKeys blk)) :
    (runBlockA sa blk).regs = (runBlock (jOf bank sa) blk).regs ∧
      (runBlockA sa blk).flags = (runBlock (jOf bank sa) blk).flags ∧
      ∀ k ∈ writeKeys blk, absMem bank sa.regs (runBlockA sa blk).mem k.1 k.2 =
        (runBlock (jOf bank sa) blk).mem k.1 k.2 :=
  runBlockA_sim_on bank blk _ hd hrw (fun _ hk => hk) sa hsep

theorem runBlockA_mem_frame_core (bank : String → Option String) (P : String → BitVec 64)
    (x : BitVec 64) :
    ∀ (blk : List (JInstr 64)) (t : TagMap) (sa : AState),
      disciplinedFromB bank t blk = true → TagInv t P sa.regs →
      (∀ k ∈ writeKeys blk, ¬ InRange8 (keyAddr bank P k) x) →
      (runBlockA sa blk).mem x = sa.mem x := by
  intro blk
  induction blk with
  | nil => intro _ _ _ _ _; rfl
  | cons i is ih =>
    intro t sa hd hinv hx
    simp only [disciplinedFromB, accessOKB, Bool.and_eq_true] at hd
    obtain ⟨⟨⟨hform, -⟩, hwk⟩, hd⟩ := hd
    simp only [runBlockA_cons]
    rw [ih (stepTags t i) (evalInstrA sa i) hd (tagInv_step t P sa.view i hinv)
      (fun k hk => hx k (mem_writeKeys_cons.2 (Or.inr hk)))]
    simp only [evalInstrA, writeAddr_eq sa i hform]
    cases hwi : writeKey i with
    | none => rfl
    | some k =>
      rw [hwi] at hwk
      simp only [keyOKB] at hwk
      simp only [Option.map_some]
      rw [regs_eq_basePtr hwk hinv]
      exact write64_of_not_inRange _ _ _ _ (hx k (mem_writeKeys_cons.2 (Or.inl hwi)))

/-- **Frame.** Under the discipline, a byte outside the range of every written cell keeps
    its value. -/
theorem runBlockA_mem_frame (bank : String → Option String) (blk : List (JInstr 64))
    (hd : disciplinedB bank blk = true) (sa : AState) (x : BitVec 64)
    (hx : ∀ k ∈ writeKeys blk, ¬ InRange8 (keyAddr bank sa.regs k) x) :
    (runBlockA sa blk).mem x = sa.mem x :=
  runBlockA_mem_frame_core bank sa.regs x blk [] sa hd (tagInv_nil sa.regs) hx

/-- The offsets of `L` are pairwise equal or at least eight and at most `2^64 - 8`
    apart. -/
def spreadB (L : List Int) : Bool :=
  L.all fun o => L.all fun o' => o == o' || (decide (8 ≤ (o - o').natAbs) &&
    decide ((o - o').natAbs ≤ 2 ^ 64 - 8))

/-- Cells at one base with offsets satisfying `spreadB` are separated. -/
theorem separated_sameBase (bank : String → Option String) (P : String → BitVec 64)
    (b : String) (L : List Int) (hL : spreadB L = true) :
    Separated bank P (L.map fun o => (b, o)) := by
  intro k hk k' hk' hne
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hk
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hk'
  have hoo : o ≠ o' := fun h => hne (h ▸ rfl)
  simp only [spreadB, List.all_eq_true] at hL
  have := hL o ho o' ho'
  simp only [Bool.or_eq_true, beq_iff_eq, hoo, false_or, Bool.and_eq_true,
    decide_eq_true_eq] at this
  exact disjoint8_add_ofInt _ o o' this.1 this.2

end CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
