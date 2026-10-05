/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Footprint
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EffAddr

/-!
# Footprints through effective addresses

The footprint of a run of `AddrMem.runBlockA`, stated on the effective-address operands of
`EffAddr`. `eaRng sa w e` is the range of `w` bytes at the address the operand `e` denotes
in the state `sa`. The ranges an instruction reads and writes are the eight-byte ranges of
`EffAddr.readEA` and `EffAddr.writeEA`, and `readsEA blk sa`, `writesEA blk sa` collect
them along the run, each operand evaluated at the registers the run holds at its
instruction.

`EffAddr.readEA` and `EffAddr.writeEA` are defined on every constructor of `JInstr 64`, the
indexed forms included, so the footprint in operands is the footprint `Footprint.reads`,
`Footprint.writes` for every block, with no side condition on the instruction forms.

## Main definitions

* `eaRng`: the byte range an operand denotes in a state, at an access width.
* `instrReadsEA`, `instrWritesEA`: the ranges one instruction reads and writes.
* `readsEA`, `writesEA`, `footprintEA`: the footprint of a run in operands.

## Main results

* `readAddr_eq_eaVal`: the address `Footprint.readAddr` gives is `eaVal` at `readEA`.
* `reads_eq_readsEA`, `writes_eq_writesEA`, `footprint_eq_footprintEA`: the two footprints
  of a run coincide.
* `writesEA_sound`: a byte outside every written operand range keeps its value.
* `read64_runBlockA_of_disj`, `read_frame_ea`, `read_frame_ea_exit`: a word whose range is
  disjoint from every written operand range reads back unchanged after the run.
* `runBlockA_local_ea`, `frame_rule_ea`: locality of a run and the frame rule, with the
  read and written ranges given by operands.
* `footCheckFrom_rangesEA`, `footCheckFrom_frame_ea`: under the one-pass check
  `Footprint.footCheckFrom`, every operand range of the run is the word range of a checked
  cell, and a word disjoint from the checked cells reads back unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.FootprintEA

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.EffAddr
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Footprint

/-! ## The range of an operand -/

/-- The `w` bytes at the address the operand `e` denotes in `sa`. -/
def eaRng (sa : AState) (w : Nat) (e : EA) : Rng := ⟨eaVal sa e, w⟩

/-- At width eight the range of an operand is the word range of its address. -/
theorem eaRng_word (sa : AState) (e : EA) : eaRng sa 8 e = Rng.word (eaVal sa e) := rfl

theorem eaRng_congr (sa sb : AState) (w : Nat) (e : EA) (hr : sa.regs = sb.regs) :
    eaRng sb w e = eaRng sa w e := by
  simp only [eaRng, eaVal_congr sa sb e hr]

/-- Disjointness of the word ranges of two operands is `AddrMem.Disjoint8` of their
    addresses. -/
theorem eaRng_disj_iff (sa : AState) (e e' : EA) :
    (eaRng sa 8 e).Disj (eaRng sa 8 e') ↔ Disjoint8 (eaVal sa e) (eaVal sa e') := Iff.rfl

/-! ## The footprint of a run in operands -/

/-- The range an instruction reads: the word of its `readEA` operand. -/
def instrReadsEA (sa : AState) (i : JInstr 64) : List Rng :=
  (readEA i).toList.map (eaRng sa 8)

/-- The range an instruction writes: the word of its `writeEA` operand. -/
def instrWritesEA (sa : AState) (i : JInstr 64) : List Rng :=
  (writeEA i).toList.map (eaRng sa 8)

/-- The operand ranges the run of a block reads, in order. -/
def readsEA : List (JInstr 64) → AState → List Rng
  | [], _ => []
  | i :: is, sa => instrReadsEA sa i ++ readsEA is (evalInstrA sa i)

/-- The operand ranges the run of a block writes, in order. -/
def writesEA : List (JInstr 64) → AState → List Rng
  | [], _ => []
  | i :: is, sa => instrWritesEA sa i ++ writesEA is (evalInstrA sa i)

/-- The footprint of the run of `blk` from `sa`, in operands. -/
def footprintEA (blk : List (JInstr 64)) (sa : AState) : Foot :=
  ⟨readsEA blk sa, writesEA blk sa⟩

theorem mem_instrReadsEA {r : Rng} {sa : AState} {i : JInstr 64} :
    r ∈ instrReadsEA sa i ↔ ∃ e, readEA i = some e ∧ r = eaRng sa 8 e := by
  cases h : readEA i <;> simp [instrReadsEA, h]

theorem mem_instrWritesEA {r : Rng} {sa : AState} {i : JInstr 64} :
    r ∈ instrWritesEA sa i ↔ ∃ e, writeEA i = some e ∧ r = eaRng sa 8 e := by
  cases h : writeEA i <;> simp [instrWritesEA, h]

theorem mem_readsEA_cons {r : Rng} {i : JInstr 64} {is : List (JInstr 64)} {sa : AState} :
    r ∈ readsEA (i :: is) sa ↔
      (∃ e, readEA i = some e ∧ r = eaRng sa 8 e) ∨ r ∈ readsEA is (evalInstrA sa i) := by
  simp only [readsEA, List.mem_append, mem_instrReadsEA]

theorem mem_writesEA_cons {r : Rng} {i : JInstr 64} {is : List (JInstr 64)} {sa : AState} :
    r ∈ writesEA (i :: is) sa ↔
      (∃ e, writeEA i = some e ∧ r = eaRng sa 8 e) ∨ r ∈ writesEA is (evalInstrA sa i) := by
  simp only [writesEA, List.mem_append, mem_instrWritesEA]

/-! ## Agreement with the footprint in addresses -/

/-- The address `Footprint.readAddr` gives is `eaVal` at `readEA`. -/
theorem readAddr_eq_eaVal (sa : AState) (i : JInstr 64) :
    readAddr sa i = (readEA i).map (eaVal sa) := by
  cases i <;>
    simp only [readAddr, readEA, readKey, Option.map_some, Option.map_none, eaVal_cell,
      eaVal_indexed]

/-- The ranges a run reads are the ranges of its read operands. -/
theorem reads_eq_readsEA (blk : List (JInstr 64)) :
    ∀ sa : AState, reads blk sa = readsEA blk sa := by
  induction blk with
  | nil => intro _; rfl
  | cons i is ih =>
    intro sa
    simp only [reads, readsEA, instrReadsEA, readAddr_eq_eaVal, ih]
    cases readEA i <;> rfl

/-- The ranges a run writes are the ranges of its written operands. -/
theorem writes_eq_writesEA (blk : List (JInstr 64)) :
    ∀ sa : AState, writes blk sa = writesEA blk sa := by
  induction blk with
  | nil => intro _; rfl
  | cons i is ih =>
    intro sa
    simp only [writes, writesEA, instrWritesEA, writeAddr_eq_eaVal, ih]
    cases writeEA i <;> rfl

/-- The footprint of a run is its footprint in operands. -/
theorem footprint_eq_footprintEA (blk : List (JInstr 64)) (sa : AState) :
    Footprint.footprint blk sa = footprintEA blk sa := by
  simp only [Footprint.footprint, footprintEA, reads_eq_readsEA, writes_eq_writesEA]

/-! ## Frame rules on operands -/

/-- **Frame of a run, in operands.** A byte outside every written operand range keeps its
    value. -/
theorem writesEA_sound (blk : List (JInstr 64)) (sa : AState) (x : BitVec 64)
    (h : ∀ r ∈ writesEA blk sa, x ∉ r) : (runBlockA sa blk).mem x = sa.mem x :=
  writes_sound blk sa x (by rw [writes_eq_writesEA]; exact h)

/-- A word whose range is disjoint from every written operand range reads back unchanged
    after the run. -/
theorem read64_runBlockA_of_disj (blk : List (JInstr 64)) :
    ∀ (sa : AState) (b : BitVec 64), (∀ w ∈ writesEA blk sa, w.Disj (Rng.word b)) →
      read64 (runBlockA sa blk).mem b = read64 sa.mem b := by
  induction blk with
  | nil => intro _ _ _; rfl
  | cons i is ih =>
    intro sa b h
    rw [runBlockA_cons, ih (evalInstrA sa i) b (fun w hw => h w (mem_writesEA_cons.2 (Or.inr hw)))]
    exact evalInstrA_read_of_disjoint sa i b
      (fun e he => Rng.disj_word_iff_disjoint8.1 (h _ (mem_writesEA_cons.2 (Or.inl ⟨e, he, rfl⟩))))

/-- **Frame rule for a read through an operand.** The word at the address the operand `e`
    denotes at entry, when its range is disjoint from every written operand range of the
    run, is unchanged by the run. -/
theorem read_frame_ea (blk : List (JInstr 64)) (sa : AState) (e : EA)
    (h : ∀ w ∈ writesEA blk sa, w.Disj (eaRng sa 8 e)) :
    read64 (runBlockA sa blk).mem (eaVal sa e) = read64 sa.mem (eaVal sa e) :=
  read64_runBlockA_of_disj blk sa (eaVal sa e) h

/-- **Frame rule for a read through an operand, at exit.** When the run also leaves the
    address of `e` unchanged, the read through `e` after the run is the read through `e`
    before it. -/
theorem read_frame_ea_exit (blk : List (JInstr 64)) (sa : AState) (e : EA)
    (h : ∀ w ∈ writesEA blk sa, w.Disj (eaRng sa 8 e))
    (he : eaVal (runBlockA sa blk) e = eaVal sa e) :
    read64 (runBlockA sa blk).mem (eaVal (runBlockA sa blk) e) = read64 sa.mem (eaVal sa e) := by
  rw [he]
  exact read_frame_ea blk sa e h

/-- **Locality of a run, in operands.** `Footprint.runBlockA_local` with the read and
    written ranges given by operands. -/
theorem runBlockA_local_ea (blk : List (JInstr 64)) (sa sb : AState) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hm : ∀ r ∈ readsEA blk sa, ∀ x, x ∈ r → sb.mem x = sa.mem x) :
    (runBlockA sb blk).regs = (runBlockA sa blk).regs ∧
      (runBlockA sb blk).flags = (runBlockA sa blk).flags ∧
      (∀ x, sb.mem x = sa.mem x → (runBlockA sb blk).mem x = (runBlockA sa blk).mem x) ∧
      (∀ r ∈ writesEA blk sa, ∀ x, x ∈ r →
        (runBlockA sb blk).mem x = (runBlockA sa blk).mem x) ∧
      readsEA blk sb = readsEA blk sa ∧ writesEA blk sb = writesEA blk sa := by
  simp only [← reads_eq_readsEA, ← writes_eq_writesEA] at hm ⊢
  exact runBlockA_local blk sa sb hr hf hm

/-- **The frame rule, in operands.** Let `Q` hold after the run from `sa` and depend only
    on registers, flags and the ranges `S`. Let `sb` have the registers and flags of `sa`
    and agree with it on every read operand range and on every byte of `S` the run does not
    write. Then `Q` holds after the run from `sb`, and a read through an operand `e` whose
    range is disjoint from every written operand range is unchanged by that run. -/
theorem frame_rule_ea (blk : List (JInstr 64)) (sa sb : AState) {S : List Rng}
    {Q : AState → Prop} (hQ : LocalOn S Q) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hreads : ∀ r ∈ readsEA blk sa, ∀ x, x ∈ r → sb.mem x = sa.mem x)
    (hS : ∀ r ∈ S, ∀ x, x ∈ r → sb.mem x = sa.mem x ∨ ∃ w ∈ writesEA blk sa, x ∈ w)
    (h : Q (runBlockA sa blk)) :
    Q (runBlockA sb blk) ∧
      ∀ e : EA, (∀ w ∈ writesEA blk sa, w.Disj (eaRng sa 8 e)) →
        read64 (runBlockA sb blk).mem (eaVal sb e) = read64 sb.mem (eaVal sb e) := by
  simp only [← reads_eq_readsEA, ← writes_eq_writesEA] at hreads hS ⊢
  obtain ⟨hq, hfr⟩ := frame_rule blk sa sb hQ hr hf hreads hS h
  refine ⟨hq, fun e hd => ?_⟩
  rw [eaVal_congr sa sb e hr]
  exact read64_congr_word _ _ _ (fun x hx => hfr x (fun w hw hxw => (hd w hw).not_mem hxw hx))

/-! ## The one-pass check -/

/-- **Soundness of the one-pass check, in operands.** When `footCheckFrom` accepts the
    block from the entry state and the cells that satisfy `Pc` are separated at the entry
    registers, every operand range the run reads or writes is the word range of a cell that
    satisfies `Pc`. -/
theorem footCheckFrom_rangesEA {bank : String → Option String} {Pc : String × Int → Bool}
    {blk : List (JInstr 64)} (h : footCheckFrom bank Pc {} blk = true) (sa : AState)
    (hsep : ∀ k k', Pc k = true → Pc k' = true → k ≠ k' →
      Disjoint8 (keyAddr bank sa.regs k) (keyAddr bank sa.regs k')) :
    (∀ r ∈ readsEA blk sa, ∃ k, Pc k = true ∧ r = cellRng bank sa.regs k) ∧
      ∀ r ∈ writesEA blk sa, ∃ k, Pc k = true ∧ r = cellRng bank sa.regs k := by
  obtain ⟨F, hF, hrd, hw⟩ := cellFootprint_of_footCheck h
  obtain ⟨er, ew⟩ := footprint_cells hF sa
    (fun k hk k' hk' hne => hsep k k' (hw k hk) (hw k' hk') hne)
  rw [reads_eq_readsEA] at er
  rw [writes_eq_writesEA] at ew
  constructor
  · intro r hr
    rw [er] at hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    exact ⟨k, hrd k hk, rfl⟩
  · intro r hr
    rw [ew] at hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    exact ⟨k, hw k hk, rfl⟩

/-- **The one-pass check gives the frame rule on operands.** Under the hypotheses of
    `footCheckFrom_rangesEA`, a read through an operand whose range is disjoint from the
    word range of every cell that satisfies `Pc` is unchanged by the run. -/
theorem footCheckFrom_frame_ea {bank : String → Option String} {Pc : String × Int → Bool}
    {blk : List (JInstr 64)} (h : footCheckFrom bank Pc {} blk = true) (sa : AState)
    (hsep : ∀ k k', Pc k = true → Pc k' = true → k ≠ k' →
      Disjoint8 (keyAddr bank sa.regs k) (keyAddr bank sa.regs k'))
    (e : EA) (hd : ∀ k, Pc k = true → (cellRng bank sa.regs k).Disj (eaRng sa 8 e)) :
    read64 (runBlockA sa blk).mem (eaVal sa e) = read64 sa.mem (eaVal sa e) := by
  refine read_frame_ea blk sa e (fun w hw => ?_)
  obtain ⟨k, hk, rfl⟩ := (footCheckFrom_rangesEA h sa hsep).2 w hw
  exact hd k hk

end CatCrypt.Crypto.SecureCompilation.Ascent.FootprintEA
