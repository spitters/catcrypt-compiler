/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.X86State
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame

/-!
# The separation logic over the address machine `fstepA`

The state of one step of the address machine `JasminLsemAddrMem.fstepA` is a pair
`LstateA × Bool`: the register file, the memory, the carry and overflow flags, and the zero
flag that the step takes and returns beside the state. Its locations (`Addr.Loc`) are the
registers of the register file by name, the program counter, the three flags and the memory
bytes; two states agree on a set of locations when they hold equal values there
(`Footprinted.ofGet Addr.loc`).

## Write footprint and read locality of one step

`storeA? frame i r` is the address of the eight-byte store of a step of `i` from the
registers `r`: an indexed store `STOREIDX`, a store into a cell (`STORE:64` or `MOV:64` into
`mem.B.off`), and a store into a frame slot (a move, a carry-chain destination, an immediate
move, a select destination). `writesA frame i s` holds the destination registers of `i`
(`JasminLsemStepFrame.dstNames`), the program counter, the three flags and the eight bytes at
the store address. `loadsA frame i r` lists the word addresses a step may read: the frame
addresses of the instruction's names, the address of an indexed load and the address of a
cell load. `readsA frame i s` holds the registers the step reads
(`JasminLsemAddrCongr.readsI`) and the destination registers, the program counter, the three
flags, and the bytes of the words of `loadsA`. The destination registers are in the read set
because a step may leave a destination register unchanged.

## Main definitions

* `Addr.Flag`, `Addr.Loc`, `Addr.loc`: the locations of `LstateA × Bool` and their values.
* `Addr.regPts`, `Addr.pcPts`, `Addr.flagPts`, `Addr.memPts`, `Addr.arrPts`: points-to
  assertions.
* `Addr.storeA?`, `Addr.loadsA`, `Addr.writesA`, `Addr.readsA`: the footprint of one step.

## Main results

* `Addr.fstepA_memStep`: a step from two states with equal registers and flags whose
  memories agree on the words of `loadsA` succeeds in both or in neither; the results have
  equal registers and flags, keep every register off `dstNames`, and keep the memory or store
  one word at `storeA?`.
* `Addr.fstepA_writesIn`: a step agrees with its start outside `writesA`.
* `Addr.fstepA_local`: two states that agree on `readsA` step alike; the results agree on
  `writesA` and each agrees with its start outside it.
* `Addr.fstepA_frame`: a step preserves an assertion whose footprint avoids `writesA`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic.Addr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames fstepF_frame_dst)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AMem read64 write64 InRange8
  write64_of_not_inRange)
open Footprinted SAssert

/-! ## Locations -/

/-- The three flags of the address machine: carry, overflow and zero. -/
inductive Flag
  | cf
  | of
  | zf
  deriving DecidableEq

/-- The value of a flag. -/
def Flag.get (s : LstateA × Bool) : Flag → Bool
  | .cf => s.1.cf
  | .of => s.1.of
  | .zf => s.2

/-- A location of `LstateA × Bool`: a register by name, the program counter, a flag, or a
    memory byte. -/
inductive Loc
  | reg (r : String)
  | pc
  | flag (f : Flag)
  | mem (a : BitVec 64)
  deriving DecidableEq

/-- The type of the value held at a location. -/
abbrev Loc.Val : Loc → Type
  | .reg _ => Σ w, BitVec w
  | .pc => Nat
  | .flag _ => Bool
  | .mem _ => BitVec 8

/-- The value of a location in a state. -/
def loc (s : LstateA × Bool) : (l : Loc) → l.Val
  | .reg r => s.1.reg.lvm r
  | .pc => s.1.reg.lpc
  | .flag f => f.get s
  | .mem a => s.1.mem a

instance : Footprinted (LstateA × Bool) Loc := Footprinted.ofGet loc

theorem agreeOn_iff {S : Set Loc} {s t : LstateA × Bool} :
    AgreeOn S s t ↔ ∀ l ∈ S, loc s l = loc t l := Iff.rfl

/-! ## Points-to assertions -/

/-- The register `r` holds the width-tagged value `v`. -/
def regPts (r : String) (v : Σ w, BitVec w) : SAssert (LstateA × Bool) Loc where
  fp := {.reg r}
  holds s := s.1.reg.lvm r = v
  supp s t h hs := (show s.1.reg.lvm r = t.1.reg.lvm r from h (.reg r) rfl).symm.trans hs

/-- The program counter holds `n`. -/
def pcPts (n : Nat) : SAssert (LstateA × Bool) Loc where
  fp := {.pc}
  holds s := s.1.reg.lpc = n
  supp s t h hs := (show s.1.reg.lpc = t.1.reg.lpc from h .pc rfl).symm.trans hs

/-- The flag `f` holds `b`. -/
def flagPts (f : Flag) (b : Bool) : SAssert (LstateA × Bool) Loc where
  fp := {.flag f}
  holds s := f.get s = b
  supp s t h hs := (show f.get s = f.get t from h (.flag f) rfl).symm.trans hs

/-- The memory projection and the memory locations are compatible. -/
theorem projCompat_mem : ProjCompat (fun s : LstateA × Bool => (s.1.mem : MemW 64)) Loc.mem :=
  fun _ _ _ h a ha => h (.mem a) ⟨a, ha, rfl⟩

theorem loc_mem_injective : Function.Injective Loc.mem := fun _ _ h => Loc.mem.inj h

/-- The `n` memory bytes at `a` hold `v` little-endian. -/
def memPts (n : Nat) (a : BitVec 64) (v : BitVec (8 * n)) : SAssert (LstateA × Bool) Loc :=
  (ptsLE n a v).comap _ Loc.mem projCompat_mem

/-- The array of `n`-byte cells `xs` lies in memory from `a`. -/
def arrPts (n : Nat) (a : BitVec 64) (xs : List (BitVec (8 * n))) :
    SAssert (LstateA × Bool) Loc :=
  (arrAt n a xs).comap _ Loc.mem projCompat_mem

@[simp] theorem holds_regPts (r : String) (v : Σ w, BitVec w) (s : LstateA × Bool) :
    (regPts r v).holds s ↔ s.1.reg.lvm r = v := Iff.rfl

@[simp] theorem holds_pcPts (n : Nat) (s : LstateA × Bool) :
    (pcPts n).holds s ↔ s.1.reg.lpc = n := Iff.rfl

@[simp] theorem holds_flagPts (f : Flag) (b : Bool) (s : LstateA × Bool) :
    (flagPts f b).holds s ↔ f.get s = b := Iff.rfl

@[simp] theorem holds_memPts (n : Nat) (a : BitVec 64) (v : BitVec (8 * n))
    (s : LstateA × Bool) : (memPts n a v).holds s ↔ readLE n s.1.mem a = v := Iff.rfl

/-- The eight-byte points-to assertion reads the word of `AddrMem`. -/
theorem holds_memPts_eight (a v : BitVec 64) (s : LstateA × Bool) :
    (memPts 8 a v).holds s ↔ read64 s.1.mem a = v := by
  rw [holds_memPts, X86.readLE_eight_eq_addrMem_read64]

/-! ## The footprint of one step -/

/-- The memory locations of the eight bytes from `a`. -/
def wordLocs (a : BitVec 64) : Set Loc := Loc.mem '' (⟨a, 8⟩ : Rng 64).toSet

/-- The address of an indexed load `LOADIDX dst, (base, idx, sc)` from the registers `r`. -/
def idxAddr? (x : LinstrR) (r : LstateN) : Option (BitVec 64) :=
  match loadIdxA? x with
  | some (_, base, idx, sc) =>
      match r.getW base 64, r.getW idx 64 with
      | some p, some vi => some (p + BitVec.ofNat 64 (sc * vi.toNat))
      | _, _ => none
  | none => none

/-- The address of a cell load `LOAD:64 d, mem.B.off` (or `MOV:64 d, mem.B.off`) from the
    registers `r`. -/
def cellLdAddr? (x : LinstrR) (r : LstateN) : Option (BitVec 64) :=
  match cellA? x with
  | some (.ld _ b off) => (r.getW b 64).map fun p => p + BitVec.ofNat 64 off
  | _ => none

/-- The word addresses one step of `i` from the registers `r` may read: the frame addresses
    of the instruction's names, the address of an indexed load and the address of a cell
    load. -/
def loadsA (frame : String → Option (BitVec 64)) (i : LinstrRM) (r : LstateN) :
    List (BitVec 64) :=
  (instrNames i.1).filterMap frame ++ (idxAddr? i.1 r).toList ++ (cellLdAddr? i.1 r).toList

/-- The address of the eight-byte store of one step of `i` from the registers `r`, in the
    order of the arms of `fstepA`: an indexed store, a move into a frame slot from a name that
    is no frame slot, a store into a cell, a carry-chain destination in a frame slot, an
    immediate move into a frame slot, and a select destination in a frame slot. -/
def storeA? (frame : String → Option (BitVec 64)) (i : LinstrRM) (r : LstateN) :
    Option (BitVec 64) :=
  match i.2 with
  | .store _ _ =>
      match storeIdxA? i.1 with
      | some (base, idx, sc, _) =>
          match r.getW base 64, r.getW idx 64 with
          | some p, some vi => some (p + BitVec.ofNat 64 (sc * vi.toNat))
          | _, _ => none
      | none => none
  | .reg _ =>
      match slotMov? i.1 with
      | some (dst, src) =>
          match frame src with
          | some _ => none
          | none => frame dst
      | none =>
          match slotCmp? i.1 with
          | some _ => none
          | none =>
              match cellA? i.1 with
              | some (.st b off _) => (r.getW b 64).map fun p => p + BitVec.ofNat 64 off
              | some _ => none
              | none =>
                  match slotCarry? frame i.1 with
                  | some (_, d, _, _, _) => frame d
                  | none =>
                      match slotImm? frame i.1 with
                      | some (a, _) => some a
                      | none =>
                          match slotCmov? frame i.1 with
                          | some (d, _, _, _) => frame d
                          | none => none
  | _ => none

/-- The locations one step of `i` from `s` may write: the destination registers, the program
    counter, the three flags and the bytes of the word at `storeA?`. -/
def writesA (frame : String → Option (BitVec 64)) (i : LinstrRM) (s : LstateA) : Set Loc :=
  fun l => match l with
    | .reg r => r ∈ dstNames i.1
    | .pc => True
    | .flag _ => True
    | .mem x => ∃ a, storeA? frame i s.reg = some a ∧ x ∈ (⟨a, 8⟩ : Rng 64)

/-- The locations one step of `i` from `s` may read: the registers of `readsI` and the
    destination registers, the program counter, the three flags and the bytes of the words of
    `loadsA`. -/
def readsA (frame : String → Option (BitVec 64)) (i : LinstrRM) (s : LstateA) : Set Loc :=
  fun l => match l with
    | .reg r => readsI i.1 r ∨ r ∈ dstNames i.1
    | .pc => True
    | .flag _ => True
    | .mem x => ∃ a ∈ loadsA frame i s.reg, x ∈ (⟨a, 8⟩ : Rng 64)

/-! ## Steps from states that differ in memory -/

/-- The results `p`, `q` of one step of `i` from `s` and `t`, two states with equal registers
    and flags: equal registers, flags and zero flags; every register off `dstNames` as in `s`;
    the memories of `s` and `t`, or the two memories with one word stored at `storeA?`. -/
def MemStep (frame : String → Option (BitVec 64)) (i : LinstrRM) (s t : LstateA)
    (p q : LstateA × Bool) : Prop :=
  p.1.reg = q.1.reg ∧ p.1.cf = q.1.cf ∧ p.1.of = q.1.of ∧ p.2 = q.2 ∧
    (∀ x, x ∉ dstNames i.1 → p.1.reg.lvm x = s.reg.lvm x) ∧
    match storeA? frame i s.reg with
    | none => p.1.mem = s.mem ∧ q.1.mem = t.mem
    | some a => ∃ v, p.1.mem = write64 s.mem a v ∧ q.1.mem = write64 t.mem a v

/-- The relation of two register-file results: equal registers and flags, every register off
    the names `D` as in the registers `r`, and the memories `m`, `m'`. -/
def RegRes (D : List String) (r : LstateN) (m m' : AMem) (p q : LstateA × Bool) : Prop :=
  p.1.reg = q.1.reg ∧ p.1.cf = q.1.cf ∧ p.1.of = q.1.of ∧ p.2 = q.2 ∧
    (∀ x, x ∉ D → p.1.reg.lvm x = r.lvm x) ∧ p.1.mem = m ∧ q.1.mem = m'

/-- The register-file step reads no memory and keeps it. -/
theorem regStepA_mem (i : LinstrRM) (r : LstateN) (m m' : AMem) (c o zf : Bool) :
    ORel (RegRes (dstNames i.1) r m m') (regStepA i ⟨r, m, c, o⟩ zf)
      (regStepA i ⟨r, m', c, o⟩ zf) := by
  unfold regStepA
  cases h : JasminLsemMemFlagNestJoin.fstepF i { reg := r, cf := c, of := o } zf with
  | none => exact ORel.none
  | some b =>
    obtain ⟨b, z⟩ := b
    exact ORel.some ⟨rfl, rfl, rfl, rfl, fun x hx => (fstepF_frame_dst h hx).1, rfl, rfl⟩

/-- `bitStepA` from two states with equal registers and flags whose words and bits of the
    instruction's names agree. -/
theorem bitStepA_mem (frame : String → Option (BitVec 64)) (w : LinstrR) (r : LstateN)
    (m m' : AMem) (c o zf : Bool)
    (hw : ∀ x ∈ instrNames w, wordA frame ⟨r, m', c, o⟩ x = wordA frame ⟨r, m, c, o⟩ x)
    (hb : ∀ x ∈ instrNames w, bitA frame ⟨r, m', c, o⟩ x = bitA frame ⟨r, m, c, o⟩ x) :
    ORel (RegRes (dstNames w) r m m') (bitStepA frame w ⟨r, m, c, o⟩ zf)
      (bitStepA frame w ⟨r, m', c, o⟩ zf) := by
  unfold bitStepA
  split
  · rename_i d op a s' c'
    simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hw hb
    rw [hw.2.1, hw.2.2.1, hw.2.2.2, hb.2.1, hb.2.2.2]
    repeat' split
    all_goals first
      | exact ORel.none
      | exact ORel.some ⟨rfl, rfl, rfl, rfl, fun x hx => by
          simp_all [dstNames, opNames, LstateN.setReg, LstateN.nextPc], rfl, rfl⟩
  · exact ORel.none

/-! ### The names of the recognised forms -/

theorem slotMov?_names {w : LinstrR} {d s : String} (h : slotMov? w = some (d, s)) :
    d ∈ dstNames w ∧ s ∈ instrNames w := by
  unfold slotMov? at h
  recog h
  simp [dstNames, instrNames, opNames]

theorem cellA?_ld_names {w : LinstrR} {d b : String} {off : Nat}
    (h : cellA? w = some (.ld d b off)) : d ∈ dstNames w := by
  unfold cellA? at h
  split at h
  · split_ifs at h <;> (try split at h) <;> simp_all [dstNames, opNames]
  · simp at h

theorem cellA?_lea_names {w : LinstrR} {d b : String} {off : Nat}
    (h : cellA? w = some (.lea d b off)) : d ∈ dstNames w := by
  unfold cellA? at h
  split at h
  · split_ifs at h <;> (try split at h) <;> simp_all [dstNames, opNames]
  · simp at h

theorem slotCarry?_names {frame : String → Option (BitVec 64)} {w : LinstrR} {lo : Bool}
    {d a s c : String} (h : slotCarry? frame w = some (lo, d, a, s, c)) :
    d ∈ dstNames w ∧ a ∈ instrNames w ∧ s ∈ instrNames w ∧ c ∈ instrNames w := by
  unfold slotCarry? at h
  split at h
  · split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h
    simp [dstNames, instrNames, opNames]
  · simp at h

theorem slotCmov?_names {frame : String → Option (BitVec 64)} {w : LinstrR}
    {d c a b : String} (h : slotCmov? frame w = some (d, c, a, b)) :
    d ∈ dstNames w ∧ c ∈ instrNames w ∧ a ∈ instrNames w ∧ b ∈ instrNames w := by
  unfold slotCmov? at h
  split at h
  · split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp [dstNames, instrNames, opNames]
  · simp at h

theorem slotImm?_names {frame : String → Option (BitVec 64)} {w : LinstrR} {a : BitVec 64}
    {v : Nat} (h : slotImm? frame w = some (a, v)) :
    ∃ q ∈ instrNames w, frame q = some a := by
  unfold slotImm? at h
  split at h
  · rename_i q o v'
    split_ifs at h
    obtain ⟨⟨a', v''⟩, ha, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact ⟨q, by simp [instrNames, opNames], ha⟩
  · simp at h

theorem memStep_of_regRes {frame : String → Option (BitVec 64)} {i : LinstrRM}
    {s t : LstateA} (hs : storeA? frame i s.reg = none) {p q : LstateA × Bool}
    (h : RegRes (dstNames i.1) s.reg s.mem t.mem p q) : MemStep frame i s t p q := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rw [hs]
  exact ⟨h6, h7⟩

/-- A step that writes the register `d` of `dstNames` and stores nothing. -/
theorem memStep_reg {frame : String → Option (BitVec 64)} {i : LinstrRM} {r : LstateN}
    {m m' : AMem} {c o : Bool} (hs : storeA? frame i r = none) {d : String}
    (hd : d ∈ dstNames i.1) {wd : Nat} (v : BitVec wd) (zf : Bool) :
    MemStep frame i ⟨r, m, c, o⟩ ⟨r, m', c, o⟩ (⟨(r.setReg d v).nextPc, m, c, o⟩, zf)
      (⟨(r.setReg d v).nextPc, m', c, o⟩, zf) := by
  refine memStep_of_regRes hs ⟨rfl, rfl, rfl, rfl, fun x hx => ?_, rfl, rfl⟩
  have : x ≠ d := fun e => hx (e ▸ hd)
  simp [LstateN.setReg, this]

/-- A step that stores the word `v` at `storeA?` and writes no register. -/
theorem memStep_store {frame : String → Option (BitVec 64)} {i : LinstrRM} {r : LstateN}
    {m m' : AMem} {c o : Bool} {a : BitVec 64} (hs : storeA? frame i r = some a)
    (v : BitVec 64) (zf : Bool) :
    MemStep frame i ⟨r, m, c, o⟩ ⟨r, m', c, o⟩ (⟨r.nextPc, write64 m a v, c, o⟩, zf)
      (⟨r.nextPc, write64 m' a v, c, o⟩, zf) := by
  refine ⟨rfl, rfl, rfl, rfl, fun x _ => rfl, ?_⟩
  show match storeA? frame i r with
    | none => _ | some a => _
  rw [hs]
  exact ⟨v, rfl, rfl⟩

theorem fstepA_memStep (frame : String → Option (BitVec 64)) (i : LinstrRM) (r : LstateN)
    (m m' : AMem) (c o : Bool) (hm : ∀ a ∈ loadsA frame i r, read64 m' a = read64 m a)
    (zf : Bool) :
    ORel (MemStep frame i ⟨r, m, c, o⟩ ⟨r, m', c, o⟩)
      (fstepA frame i ⟨r, m, c, o⟩ zf) (fstepA frame i ⟨r, m', c, o⟩ zf) := by
  obtain ⟨w, tag⟩ := i
  have hname : ∀ x ∈ instrNames w, ∀ a, frame x = some a → read64 m' a = read64 m a :=
    fun x hx a ha => hm a (List.mem_append_left _ (List.mem_append_left _
      (List.mem_filterMap.2 ⟨x, hx, ha⟩)))
  have hword : ∀ x ∈ instrNames w,
      wordA frame ⟨r, m', c, o⟩ x = wordA frame ⟨r, m, c, o⟩ x := by
    intro x hx
    unfold wordA
    split
    · rename_i a ha
      rw [hname x hx a ha]
    · rfl
  have hbit : ∀ x ∈ instrNames w,
      bitA frame ⟨r, m', c, o⟩ x = bitA frame ⟨r, m, c, o⟩ x := by
    intro x hx
    unfold bitA
    split
    · rename_i a ha
      rw [hname x hx a ha]
    · rfl
  unfold fstepA
  cases tag with
  | load wd n =>
    simp only
    cases hx : loadIdxA? w with
    | none => exact ORel.none
    | some p =>
      obtain ⟨dst, base, idx, sc⟩ := p
      simp only
      cases hb : r.getW base 64 with
      | none => exact ORel.none
      | some pb =>
        cases hi : r.getW idx 64 with
        | none => exact ORel.none
        | some vi =>
          simp only
          rw [hm _ (by simp [loadsA, idxAddr?, hx, hb, hi])]
          unfold loadIdxA? at hx
          recog hx
          exact ORel.some (memStep_reg (by simp [storeA?]) (by simp [dstNames, opNames]) _ zf)
  | store wd n =>
    simp only
    cases hx : storeIdxA? w with
    | none => exact ORel.none
    | some p =>
      obtain ⟨base, idx, sc, val⟩ := p
      simp only
      cases hb : r.getW base 64 with
      | none => exact ORel.none
      | some pb =>
        cases hi : r.getW idx 64 with
        | none => exact ORel.none
        | some vi =>
          cases hv : r.getW val 64 with
          | none => exact ORel.none
          | some v =>
            exact ORel.some (memStep_store (by simp [storeA?, hx, hb, hi]) v zf)
  | reg cd =>
    simp only
    cases hs : slotMov? w with
    | some p =>
      obtain ⟨dst, src⟩ := p
      obtain ⟨hd, hsrc⟩ := slotMov?_names hs
      simp only
      cases hfs : frame src with
      | some a =>
        simp only
        rw [hname src hsrc a hfs]
        exact ORel.some (memStep_reg (by simp [storeA?, hs, hfs]) hd _ zf)
      | none =>
        cases hfd : frame dst with
        | some a =>
          simp only
          cases hv : r.getW src 64 with
          | some v => exact ORel.some (memStep_store (by simp [storeA?, hs, hfs, hfd]) v zf)
          | none =>
            simp only
            cases hv1 : r.getW src 1 with
            | some b =>
              exact ORel.some (memStep_store (by simp [storeA?, hs, hfs, hfd]) _ zf)
            | none => exact ORel.none
        | none =>
          simp only
          exact (regStepA_mem _ r m m' c o zf).mono fun p q h =>
            memStep_of_regRes (by simp [storeA?, hs, hfs, hfd]) h
    | none =>
      simp only
      cases hk : slotCmp? w with
      | some p =>
        obtain ⟨d, x, q⟩ := p
        simp only
        cases hq : frame q with
        | some a =>
          simp only
          have hqn : q ∈ instrNames w := by
            unfold slotCmp? at hk
            recog hk
            simp [instrNames, opNames]
          have hdn : dstNames w = [d] := by
            unfold slotCmp? at hk
            recog hk
            simp [dstNames, opNames]
          rw [hname q hqn a hq]
          refine (regStepA_mem _ r m m' c o zf).mono fun p q h => memStep_of_regRes
            (by simp [storeA?, hs, hk]) ?_
          rw [show (w, MemTag.reg cd).1 = w from rfl, hdn]
          simpa [dstNames, opNames] using h
        | none =>
          simp only
          exact (regStepA_mem _ r m m' c o zf).mono fun p q h =>
            memStep_of_regRes (by simp [storeA?, hs, hk]) h
      | none =>
        simp only
        cases hcl : cellA? w with
        | some op =>
          cases op with
          | ld d b off =>
            simp only
            cases hb : r.getW b 64 with
            | none => exact ORel.none
            | some pb =>
              simp only
              rw [hm _ (by simp [loadsA, cellLdAddr?, hcl, hb])]
              exact ORel.some (memStep_reg (by simp [storeA?, hs, hk, hcl])
                (cellA?_ld_names hcl) _ zf)
          | st b off v =>
            simp only
            cases hb : r.getW b 64 with
            | none => exact ORel.none
            | some pb =>
              cases hv : r.getW v 64 with
              | some x =>
                exact ORel.some (memStep_store (by simp [storeA?, hs, hk, hcl, hb]) x zf)
              | none =>
                simp only
                cases hv1 : r.getW v 1 with
                | some x =>
                  exact ORel.some (memStep_store (by simp [storeA?, hs, hk, hcl, hb]) _ zf)
                | none => exact ORel.none
          | lea d b off =>
            simp only
            cases hb : r.getW b 64 with
            | none => exact ORel.none
            | some pb =>
              exact ORel.some (memStep_reg (by simp [storeA?, hs, hk, hcl])
                (cellA?_lea_names hcl) _ zf)
        | none =>
          simp only
          cases hsc : slotCarry? frame w with
          | some p =>
            obtain ⟨lo, d, a, s', c'⟩ := p
            obtain ⟨hd, ha, hs', hc'⟩ := slotCarry?_names hsc
            simp only
            rw [hword a ha, hword s' hs', hbit c' hc']
            cases hfd : frame d <;> cases lo <;>
              simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;>
              first
              | exact ORel.none
              | exact ORel.some (memStep_store (by simp [storeA?, hs, hk, hcl, hsc, hfd]) _ zf)
              | exact ORel.some (memStep_reg (by simp [storeA?, hs, hk, hcl, hsc, hfd]) hd _ zf)
          | none =>
            simp only
            cases hsi : slotImm? frame w with
            | some p =>
              obtain ⟨a, v⟩ := p
              obtain ⟨q, hq, hfq⟩ := slotImm?_names hsi
              simp only
              rw [hname q hq a hfq]
              exact ORel.some (memStep_store (by simp [storeA?, hs, hk, hcl, hsc, hsi]) _ zf)
            | none =>
              simp only
              cases hsv : slotCmov? frame w with
              | some p =>
                obtain ⟨d, c', a, b⟩ := p
                obtain ⟨hd, hc', ha, hb⟩ := slotCmov?_names hsv
                simp only
                rw [hbit c' hc', hword a ha, hword b hb]
                cases hfd : frame d <;> simp only <;> split <;>
                  first
                  | exact ORel.none
                  | exact ORel.some
                      (memStep_store (by simp [storeA?, hs, hk, hcl, hsc, hsi, hsv, hfd]) _ zf)
                  | exact ORel.some
                      (memStep_reg (by simp [storeA?, hs, hk, hcl, hsc, hsi, hsv, hfd]) hd _ zf)
              | none =>
                simp only
                have hst : storeA? frame (w, .reg cd) r = none := by
                  simp [storeA?, hs, hk, hcl, hsc, hsi, hsv]
                have h1 := regStepA_mem (w, .reg cd) r m m' c o zf
                have h2 := bitStepA_mem frame w r m m' c o zf hword hbit
                revert h1
                cases regStepA (w, .reg cd) ⟨r, m, c, o⟩ zf <;>
                  cases regStepA (w, .reg cd) ⟨r, m', c, o⟩ zf <;> intro h1
                · exact h2.mono fun p q h => memStep_of_regRes hst h
                · cases h1
                · cases h1
                · exact h1.mono fun p q h => memStep_of_regRes hst h
  | _ => exact ORel.none

/-! ## The write footprint of one step -/

/-- The base register of a cell store is read. -/
theorem cellA?_st_reads {w : LinstrR} {b : String} {off : Nat} {v : String}
    (h : cellA? w = some (.st b off v)) : readsI w b := by
  unfold cellA? at h
  split at h
  · split_ifs at h
    · simp at h
    · obtain ⟨⟨b', off'⟩, hp, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      exact cell_reads (by simp) hp
    · simp at h
    · split at h
      · rename_i p hp
        obtain ⟨b', off'⟩ := p
        cases h
        exact cell_reads (by simp) hp
      · simp at h
  · simp at h

/-- The store address of a step depends only on the registers the step reads. -/
theorem storeA?_congr (frame : String → Option (BitVec 64)) (i : LinstrRM) {r r' : LstateN}
    (h : NAgree (readsI i.1) r r') : storeA? frame i r = storeA? frame i r' := by
  obtain ⟨w, tag⟩ := i
  unfold storeA?
  cases tag with
  | store wd n =>
    simp only
    cases hx : storeIdxA? w with
    | none => rfl
    | some p =>
      obtain ⟨base, idx, sc, val⟩ := p
      unfold storeIdxA? at hx
      recog hx
      simp only
      reads_rw h
  | reg cd =>
    simp only
    cases hs : slotMov? w with
    | some p => rfl
    | none =>
      simp only
      cases hk : slotCmp? w with
      | some p => rfl
      | none =>
        simp only
        cases hcl : cellA? w with
        | some op =>
          cases op with
          | st b off v =>
            simp only
            rw [getW_congr h (cellA?_st_reads hcl)]
          | _ => rfl
        | none => rfl
  | _ => rfl

/-- **The write footprint of one step.** A successful step of `fstepA` agrees with its start
    outside `writesA`. -/
theorem fstepA_writesIn (frame : String → Option (BitVec 64)) (i : LinstrRM) {s : LstateA}
    {zf : Bool} {p : LstateA × Bool} (h : fstepA frame i s zf = some p) :
    AgreeOn (writesA frame i s)ᶜ (s, zf) p := by
  obtain ⟨r, m, c, o⟩ := s
  have hM := fstepA_memStep frame i r m m c o (fun _ _ => rfl) zf
  rw [h] at hM
  cases hM with
  | some hpq =>
    obtain ⟨-, -, -, -, hreg, hmem⟩ := hpq
    intro l hl
    cases l with
    | reg x => exact (hreg x hl).symm
    | pc => exact absurd trivial hl
    | flag f => exact absurd trivial hl
    | mem x =>
      show m x = p.1.mem x
      have hl' : ¬ ∃ a, storeA? frame i r = some a ∧ x ∈ (⟨a, 8⟩ : Rng 64) := hl
      simp only at hmem
      split at hmem
      · exact (congrFun hmem.1 x).symm
      · rename_i a hst
        obtain ⟨v, hv, -⟩ := hmem
        rw [hv]
        exact (write64_of_not_inRange _ _ _ _ fun hx => hl' ⟨a, hst, hx⟩).symm

/-- A step preserves an assertion whose footprint avoids the step's write footprint. -/
theorem fstepA_frame (frame : String → Option (BitVec 64)) (i : LinstrRM) {s : LstateA}
    {zf : Bool} {p : LstateA × Bool} (h : fstepA frame i s zf = some p)
    (R : SAssert (LstateA × Bool) Loc) (hd : Disjoint R.fp (writesA frame i s))
    (hR : R.holds (s, zf)) : R.holds p :=
  R.supp _ _ (agreeOn_anti (fun _ hl hw => Set.disjoint_left.1 hd hl hw)
    (fstepA_writesIn frame i h)) hR

/-! ## Read locality of one step -/

/-- **Read locality of one step.** Two states that agree on the read footprint of `i` at `s`
    both step or both fail; the two results agree on the write footprint and each agrees
    with its start outside it. -/
theorem fstepA_local (frame : String → Option (BitVec 64)) (i : LinstrRM) {s t : LstateA}
    {zf zt : Bool} (h : AgreeOn (readsA frame i s) (s, zf) (t, zt)) :
    ORel (fun p q => AgreeOn (writesA frame i s) p q ∧ AgreeOn (writesA frame i s)ᶜ (s, zf) p ∧
        AgreeOn (writesA frame i s)ᶜ (t, zt) q)
      (fstepA frame i s zf) (fstepA frame i t zt) := by
  obtain ⟨r, m, c, o⟩ := s
  obtain ⟨r', m', c', o'⟩ := t
  have hpc : r.lpc = r'.lpc := h .pc trivial
  have hcf : c = c' := h (.flag .cf) trivial
  have hof : o = o' := h (.flag .of) trivial
  have hzf : zf = zt := h (.flag .zf) trivial
  have hreg : ∀ x, readsI i.1 x ∨ x ∈ dstNames i.1 → r.lvm x = r'.lvm x :=
    fun x hx => h (.reg x) hx
  have hmem : ∀ a ∈ loadsA frame i r, read64 m' a = read64 m a := by
    intro a ha
    have e : ∀ k, k < 8 → m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k) :=
      fun k hk => (h (.mem _) ⟨a, ha, by
        show ((a + BitVec.ofNat 64 k) - a).toNat < 8
        rw [Ascent.AddrMem.toNat_add_sub_self a k hk]
        exact hk⟩).symm
    have e0 : m' a = m a := by simpa using e 0 (by decide)
    simp only [read64, e0, e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
      e 5 (by decide), e 6 (by decide), e 7 (by decide)]
  subst hcf hof hzf
  have hN : NAgree (readsI i.1) r r' := ⟨hpc, fun x hx => hreg x (Or.inl hx)⟩
  have hM := fstepA_memStep frame i r m m' c o hmem zf
  have hC := fstepA_congr frame i (s := ⟨r, m', c, o⟩) (t := ⟨r', m', c, o⟩)
    ⟨hN, rfl, rfl, rfl⟩ zf
  have hWs : ∀ p, fstepA frame i ⟨r, m, c, o⟩ zf = some p →
      AgreeOn (writesA frame i ⟨r, m, c, o⟩)ᶜ (⟨r, m, c, o⟩, zf) p :=
    fun _ hp => fstepA_writesIn frame i hp
  have hWt : ∀ q, fstepA frame i ⟨r', m', c, o⟩ zf = some q →
      AgreeOn (writesA frame i ⟨r', m', c, o⟩)ᶜ (⟨r', m', c, o⟩, zf) q :=
    fun _ hq => fstepA_writesIn frame i hq
  have hst : storeA? frame i r' = storeA? frame i r := (storeA?_congr frame i hN).symm
  have hWeq : writesA frame i ⟨r', m', c, o⟩ = writesA frame i ⟨r, m, c, o⟩ := by
    funext l
    cases l <;> simp only [writesA, hst]
  revert hM hC hWs hWt
  cases fstepA frame i ⟨r, m, c, o⟩ zf <;> cases fstepA frame i ⟨r, m', c, o⟩ zf <;>
    cases fstepA frame i ⟨r', m', c, o⟩ zf <;> intro hM hC hWs hWt
  · exact ORel.none
  all_goals try (cases hM; done)
  all_goals try (cases hC; done)
  rename_i p q' q
  cases hM with
  | some hpq =>
  cases hC with
  | some hqq =>
  obtain ⟨e1, e2, e3, e4, -, e6⟩ := hpq
  obtain ⟨n1, n2, n3, n4, n5⟩ := hqq
  refine ORel.some ⟨?_, hWs p rfl, hWeq ▸ hWt q rfl⟩
  intro l hl
  cases l with
  | reg x =>
    show p.1.reg.lvm x = q.1.reg.lvm x
    rw [e1]
    rcases n1.2 x with e | ⟨e, e'⟩
    · exact e
    · rw [e, e']
      exact hreg x (Or.inr hl)
  | pc =>
    show p.1.reg.lpc = q.1.reg.lpc
    rw [e1]
    exact n1.1
  | flag f =>
    cases f
    · exact e2.trans n3
    · exact e3.trans n4
    · exact e4.trans n5
  | mem x =>
    show p.1.mem x = q.1.mem x
    obtain ⟨a, ha, hx⟩ := hl
    have ha' : storeA? frame i r = some a := ha
    rw [← n2]
    simp only [ha'] at e6
    obtain ⟨v, hv, hv'⟩ := e6
    rw [hv, hv']
    simp only [write64, if_pos (show InRange8 a x from hx)]

end CatCrypt.Crypto.SecureCompilation.SepLogic.Addr
