/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RescheduleEquivalence

/-!
# Read and write footprints of `JInstr 64`, and the commutation of independent instructions

Every instruction of `JInstr 64` gets a read footprint `rdLocs` and a write footprint
`wrLocs`, lists of locations of the machine state `JState 64`: a register, one of the five
flags, a memory cell `(base, off)`, or the whole memory bank of a base name (for the accesses
whose offset is computed at run time, `loadMemIdx` and `storeMemIdx`, and for `loadSym`, which
copies a bank). The registers are those of `SpillingRegAlloc.writtenNames` and `readNames`, the
flags those of `RescheduleEquivalence.flagWrites` and `flagReads`, and the memory locations
are given here for every memory form.

The footprints are justified by two facts about `evalInstr`, proved for every instruction:

* `evalInstr_frame`: a location covered by no write location keeps its value;
* `evalInstr_dep`: on the locations covered by a write location, the result depends only on
  the values at the read locations.

From these two facts alone, `evalInstr_comm_of_indepF` proves that two instructions whose
footprints are disjoint (`indepF`: no write of either overlaps a write or a read of the
other) commute on every state, and `runBlock_perm_eqF` that a sequence of adjacent
transpositions certified by `indepF` preserves `runBlock` on every state.

The semantics is that of `runBlock`: memory is keyed by the base register's name, so two
cells with different base names are different cells. On the machine this is the case when
the regions named by distinct bases do not overlap, which the layouts of the compiler
state for their arrays. A base register is a read location of every access through it, so
an instruction that writes a base register is never moved across an access through it.

## Main definitions

* `Loc`, `Atom`, `Loc.covers`, `Loc.overlap`: locations, the atomic locations of a state, and
  the two relations between them.
* `rdLocs`, `wrLocs`: the footprints.
* `indepF`: disjointness of two footprints.
* `checkSwapF`, `checkAdjTranspositionsF`: the certificate check of a sequence of adjacent
  transpositions under `indepF`.
* `indepSeg`, `swapSeg`, `checkSwapSeg`, `checkSegSwaps`: the same for segments, lists of
  instructions such as the machine instructions of one instruction of a printed body.

## Main results

* `evalInstr_frame`, `evalInstr_dep`: the two facts above.
* `evalInstr_comm_of_indepF`: independent instructions commute.
* `runBlock_swap_of_indepF`, `runBlock_perm_eqF`: the block-level forms.
* `runBlock_seg_comm`, `runBlock_swapSeg`, `runBlock_segSwaps`: the segment forms.

## Elaboration cost

`evalInstr_frame` and the dependence lemmas at a flag and at a memory cell are case analyses
over the constructors of `JInstr`, one `simp_all` per case. `evalInstr_dep_reg` closes each
group of constructors with one lemma about the written register file (`regs_ite_dep`,
`regs_ite₂_dep`) and one rewrite by the agreement lemmas of its inputs. The cost is per
constructor and does not grow with any block.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc (writtenNames readNames runBlock_append)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RescheduleEquivalence
  (FlagId flagWrites flagReads applySwap applySwaps)

/-! ## 1. Locations -/

/-- A location of the machine state: a register, a flag, the memory cell `(base, off)`, or
    every cell of the bank `base`. -/
inductive Loc where
  | reg (r : String)
  | flag (f : FlagId)
  | cell (base : String) (off : Int)
  | bank (base : String)
  deriving DecidableEq, Repr

/-- An atomic location: a register, a flag or a memory cell. -/
inductive Atom where
  | reg (r : String)
  | flag (f : FlagId)
  | cell (base : String) (off : Int)
  deriving DecidableEq, Repr

/-- The flag of `RFlags` named by a `FlagId`. -/
def flagGet : FlagId → RFlags → JFlag
  | .CF, f => f.cf
  | .PF, f => f.pf
  | .ZF, f => f.zf
  | .SF, f => f.sf
  | .OF, f => f.of

/-- The atomic locations a location stands for. -/
def Loc.covers : Loc → Atom → Bool
  | .reg r, .reg r' => r == r'
  | .flag f, .flag f' => f == f'
  | .cell b o, .cell b' o' => b == b' && o == o'
  | .bank b, .cell b' _ => b == b'
  | _, _ => false

/-- Two locations overlap: they cover a common atomic location. -/
def Loc.overlap : Loc → Loc → Bool
  | .reg r, .reg r' => r == r'
  | .flag f, .flag f' => f == f'
  | .cell b o, .cell b' o' => b == b' && o == o'
  | .cell b _, .bank b' => b == b'
  | .bank b, .cell b' _ => b == b'
  | .bank b, .bank b' => b == b'
  | _, _ => false

/-- Two locations that cover a common atomic location overlap. -/
theorem Loc.overlap_of_covers {l m : Loc} {x : Atom} (hl : l.covers x = true)
    (hm : m.covers x = true) : l.overlap m = true := by
  cases l <;> cases m <;> cases x <;> simp_all [Loc.covers, Loc.overlap]

/-- Two states agree at an atomic location. -/
def AgreeAt (s t : JState 64) : Atom → Prop
  | .reg r => s.regs r = t.regs r
  | .flag f => flagGet f s.flags = flagGet f t.flags
  | .cell b o => s.mem b o = t.mem b o

theorem AgreeAt.symm {s t : JState 64} {x : Atom} (h : AgreeAt s t x) : AgreeAt t s x := by
  cases x <;> simp only [AgreeAt] at h ⊢ <;> exact h.symm

theorem AgreeAt.trans {s t u : JState 64} {x : Atom} (h₁ : AgreeAt s t x)
    (h₂ : AgreeAt t u x) : AgreeAt s u x := by
  cases x <;> simp only [AgreeAt] at h₁ h₂ ⊢ <;> exact h₁.trans h₂

/-- Two states that agree at every atomic location are equal. -/
theorem eq_of_agreeAt {s t : JState 64} (h : ∀ x, AgreeAt s t x) : s = t := by
  obtain ⟨rs, ⟨c, p, z, sg, o⟩, ms⟩ := s
  obtain ⟨rt, ⟨c', p', z', sg', o'⟩, mt⟩ := t
  have hr : rs = rt := funext fun r => by simpa only [AgreeAt] using h (.reg r)
  have hm : ms = mt := funext fun b => funext fun o => by simpa only [AgreeAt] using h (.cell b o)
  have h1 := h (.flag .CF)
  have h2 := h (.flag .PF)
  have h3 := h (.flag .ZF)
  have h4 := h (.flag .SF)
  have h5 := h (.flag .OF)
  simp only [AgreeAt, flagGet] at h1 h2 h3 h4 h5
  subst hr hm h1 h2 h3 h4 h5
  rfl

/-- The atomic location `x` is covered by a location of `L`. -/
def Covered (L : List Loc) (x : Atom) : Prop := ∃ l ∈ L, l.covers x = true

/-! ## 2. The footprints -/

/-- The memory locations an instruction reads. A partial write of a bank (`storeMemIdx`)
    reads the bank, because the cells it does not write keep their values. -/
def memRd : JInstr 64 → List Loc
  | .loadMem _ base off => [.cell base off]
  | .mulxMem _ _ _ base off => [.cell base off]
  | .loadMemIdx _ base _ _ => [.bank base]
  | .storeMemIdx base _ _ _ => [.bank base]
  | .loadSym _ sym => [.bank sym]
  | .addMem _ base off | .adcxMem _ base off | .adoxMem _ base off
  | .imulMem _ base off => [.cell base off]
  | .imulriMem _ base off _ => [.cell base off]
  | .addToMem base off _ => [.cell base off]
  | .cmpMem _ base off => [.cell base off]
  | .cmovccMem _ _ base off => [.cell base off]
  | .aluMem _ _ base off => [.cell base off]
  | .andnMem _ _ base off => [.cell base off]
  | _ => []

/-- The memory locations an instruction writes. `loadSym dst sym` points the bank of `dst`
    at the bank of `sym`, so it writes the bank of `dst`. -/
def memWr : JInstr 64 → List Loc
  | .storeMem base off _ => [.cell base off]
  | .storeMemIdx base _ _ _ => [.bank base]
  | .loadSym dst _ => [.bank dst]
  | .addToMem base off _ => [.cell base off]
  | _ => []

/-- The read footprint: registers, flags and memory. -/
def rdLocs (i : JInstr 64) : List Loc :=
  (readNames i).map Loc.reg ++ (flagReads i).map Loc.flag ++ memRd i

/-- The write footprint: registers, flags and memory. -/
def wrLocs (i : JInstr 64) : List Loc :=
  (writtenNames i).map Loc.reg ++ (flagWrites i).map Loc.flag ++ memWr i

/-- No location of `L` overlaps a location of `M`. -/
def disjointLocs (L M : List Loc) : Bool :=
  L.all fun l => M.all fun m => !l.overlap m

/-- **Independence**: no write of either instruction overlaps a write or a read of the
    other. -/
def indepF (a b : JInstr 64) : Bool :=
  disjointLocs (wrLocs a) (wrLocs b) && disjointLocs (wrLocs a) (rdLocs b)
    && disjointLocs (rdLocs a) (wrLocs b)

theorem not_covered_of_disjointLocs {L M : List Loc} (h : disjointLocs L M = true) {x : Atom}
    (hx : Covered L x) : ¬ Covered M x := by
  rintro ⟨m, hm, hmx⟩
  obtain ⟨l, hl, hlx⟩ := hx
  have := (List.all_eq_true.mp ((List.all_eq_true.mp h) l hl)) m hm
  simp [Loc.overlap_of_covers hlx hmx] at this

/-! ## 3. The frame and dependence facts -/

theorem covered_cons {l : Loc} {L : List Loc} {x : Atom} :
    Covered (l :: L) x ↔ l.covers x = true ∨ Covered L x := by
  simp [Covered]

theorem covered_nil {x : Atom} : ¬ Covered [] x := by
  simp [Covered]

theorem covered_append {L M : List Loc} {x : Atom} :
    Covered (L ++ M) x ↔ Covered L x ∨ Covered M x := by
  simp only [Covered, List.mem_append]
  constructor
  · rintro ⟨l, hl | hl, h⟩
    · exact .inl ⟨l, hl, h⟩
    · exact .inr ⟨l, hl, h⟩
  · rintro (⟨l, hl, h⟩ | ⟨l, hl, h⟩)
    · exact ⟨l, .inl hl, h⟩
    · exact ⟨l, .inr hl, h⟩

/-- **Frame.** An atomic location covered by no write location of `i` keeps its value. -/
theorem evalInstr_frame (s : JState 64) (i : JInstr 64) (x : Atom)
    (hx : ¬ Covered (wrLocs i) x) : AgreeAt (evalInstr s i) s x := by
  cases i <;> cases x <;>
    simp_all [wrLocs, memWr, writtenNames, flagWrites, covered_cons,
      covered_nil, Loc.covers, AgreeAt, flagGet, evalInstr, JState.setReg,
      JState.writeB5W, JState.writeB5, JState.writeB2W, JState.writeB4W, JState.writeB5W2,
      JState.writeB5N, JState.writeCFW, JState.writeB5Mem, JState.setRegMerge,
      JState.store, JState.storeIdx, x86_XCHG] <;>
    first
      | (rename_i f; cases f <;> simp_all)
      | grind

/-- The read hypotheses of `evalInstr_dep`, per kind of location. -/
theorem agree_reg {i : JInstr 64} {s t : JState 64}
    (h : ∀ x, Covered (rdLocs i) x → AgreeAt s t x) {r : String}
    (hr : Loc.reg r ∈ rdLocs i) : s.regs r = t.regs r :=
  h (.reg r) ⟨_, hr, by simp [Loc.covers]⟩

theorem agree_flag {i : JInstr 64} {s t : JState 64}
    (h : ∀ x, Covered (rdLocs i) x → AgreeAt s t x) {f : FlagId}
    (hf : Loc.flag f ∈ rdLocs i) : flagGet f s.flags = flagGet f t.flags :=
  h (.flag f) ⟨_, hf, by simp [Loc.covers]⟩

theorem agree_cell {i : JInstr 64} {s t : JState 64}
    (h : ∀ x, Covered (rdLocs i) x → AgreeAt s t x) {b : String} {o : Int}
    (hc : Loc.cell b o ∈ rdLocs i) : s.mem b o = t.mem b o :=
  h (.cell b o) ⟨_, hc, by simp [Loc.covers]⟩

theorem agree_bank {i : JInstr 64} {s t : JState 64}
    (h : ∀ x, Covered (rdLocs i) x → AgreeAt s t x) {b : String}
    (hc : Loc.bank b ∈ rdLocs i) (o : Int) : s.mem b o = t.mem b o :=
  h (.cell b o) ⟨_, hc, by simp [Loc.covers]⟩

/-- The read hypotheses of `evalInstr_dep` at an operand. -/
theorem eval_agree {s t : JState 64} (src : JOperand)
    (hs : ∀ r ∈ AsmPrinter.srcNames src, s.regs r = t.regs r) : src.eval s = src.eval t := by
  cases src <;> simp_all [AsmPrinter.srcNames, JOperand.eval]

/-- The hypotheses of the dependence lemmas: the two states agree at the read locations of
    `i`, split by kind of location. -/
structure ReadLocsAgree (i : JInstr 64) (s t : JState 64) : Prop where
  reg : ∀ r, Loc.reg r ∈ rdLocs i → s.regs r = t.regs r
  flag : ∀ f, Loc.flag f ∈ rdLocs i → flagGet f s.flags = flagGet f t.flags
  cell : ∀ b o, Loc.cell b o ∈ rdLocs i → s.mem b o = t.mem b o
  bank : ∀ b, Loc.bank b ∈ rdLocs i → ∀ o, s.mem b o = t.mem b o

theorem ReadLocsAgree.of {i : JInstr 64} {s t : JState 64}
    (h : ∀ x, Covered (rdLocs i) x → AgreeAt s t x) : ReadLocsAgree i s t :=
  ⟨fun _ hr => agree_reg h hr, fun _ hf => agree_flag h hf, fun _ _ hc => agree_cell h hc,
    fun _ hb => agree_bank h hb⟩

/-- The read hypotheses of `evalInstr_dep` at a condition. -/
theorem condB_agree {s t : JState 64} (c : Condt)
    (h : ∀ f ∈ RescheduleEquivalence.condFlagReads c, flagGet f s.flags = flagGet f t.flags) :
    s.condB c = t.condB c := by
  cases c <;>
    simp_all [RescheduleEquivalence.condFlagReads, JState.condB, x86_eval_cond, JState.flagB,
      flagGet, Id.run]

/-! ### Dependence at a register

`evalInstr_dep_reg` is proved by the way each instruction reads its inputs and writes its
registers. A register covered by the write footprint is a written name
(`mem_writtenNames_of_covered`). The register file after an instruction that writes one
register `d` is `fun r ↦ if r = d then v else s.regs r`, and after one that writes two it has
two such tests; `regs_ite_dep` and `regs_ite₂_dep` reduce the goal to the agreement of the
written values. The read hypotheses give that agreement from the agreement of the inputs, one
lemma per kind of input: a register (`ReadLocsAgree.get`), an operand (`ReadLocsAgree.eval`), a flag
(`ReadLocsAgree.flagB_cf` and its two siblings), a condition (`ReadLocsAgree.condB`), a memory cell
(`ReadLocsAgree.load`) and a register-indexed cell (`ReadLocsAgree.loadIdx`). The constructors are
grouped by the inputs they read, and each group is closed by one rewrite with these lemmas. -/

/-- `memWr` holds no register. -/
theorem reg_not_mem_memWr (i : JInstr 64) (r : String) : Loc.reg r ∉ memWr i := by
  cases i <;> simp [memWr]

/-- A register covered by the write footprint is a written name. -/
theorem mem_writtenNames_of_covered {i : JInstr 64} {r : String}
    (hx : Covered (wrLocs i) (.reg r)) : r ∈ writtenNames i := by
  obtain ⟨l, hl, hc⟩ := hx
  simp only [wrLocs, List.mem_append, List.mem_map] at hl
  rcases hl with (⟨x, hx, rfl⟩ | ⟨f, -, rfl⟩) | hm
  · simp only [Loc.covers, beq_iff_eq] at hc
    exact hc ▸ hx
  · simp [Loc.covers] at hc
  · cases l with
    | reg x =>
      simp only [Loc.covers, beq_iff_eq] at hc
      exact absurd (hc ▸ hm) (reg_not_mem_memWr i r)
    | _ => simp [Loc.covers] at hc

namespace ReadLocsAgree

variable {i : JInstr 64} {s t : JState 64}

/-- Agreement at a read register. -/
theorem get (h : ReadLocsAgree i s t) {x : String} (hx : x ∈ readNames i) : s.get x = t.get x :=
  h.reg x (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx)))

/-- Agreement at an operand whose registers are read. -/
theorem eval (h : ReadLocsAgree i s t) {o : JOperand} (ho : AsmPrinter.srcNames o ⊆ readNames i) :
    o.eval s = o.eval t :=
  eval_agree o fun _ hx => h.get (ho hx)

/-- Agreement at a read flag. -/
theorem flag' (h : ReadLocsAgree i s t) {f : FlagId} (hf : f ∈ flagReads i) :
    flagGet f s.flags = flagGet f t.flags :=
  h.flag f (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hf)))

/-- Agreement at the carry flag, when it is read. -/
theorem flagB_cf (h : ReadLocsAgree i s t) (hf : FlagId.CF ∈ flagReads i) :
    s.flagB (·.cf) = t.flagB (·.cf) := by
  simp only [JState.flagB]
  rw [show s.flags.cf = t.flags.cf from h.flag' hf]

/-- Agreement at the overflow flag, when it is read. -/
theorem flagB_of (h : ReadLocsAgree i s t) (hf : FlagId.OF ∈ flagReads i) :
    s.flagB (·.of) = t.flagB (·.of) := by
  simp only [JState.flagB]
  rw [show s.flags.of = t.flags.of from h.flag' hf]

/-- Agreement at the zero flag, when it is read. -/
theorem flagB_zf (h : ReadLocsAgree i s t) (hf : FlagId.ZF ∈ flagReads i) :
    s.flagB (·.zf) = t.flagB (·.zf) := by
  simp only [JState.flagB]
  rw [show s.flags.zf = t.flags.zf from h.flag' hf]

/-- Agreement at a condition whose flags are read. -/
theorem condB (h : ReadLocsAgree i s t) {c : Condt}
    (hc : RescheduleEquivalence.condFlagReads c ⊆ flagReads i) : s.condB c = t.condB c :=
  condB_agree c fun _ hf => h.flag' (hc hf)

/-- Agreement at a read memory cell. -/
theorem load (h : ReadLocsAgree i s t) {b : String} {o : Int} (hc : Loc.cell b o ∈ memRd i) :
    s.load b o = t.load b o :=
  h.cell b o (List.mem_append_right _ hc)

/-- Agreement at a register-indexed cell of a read bank, with a read index register. -/
theorem loadIdx (h : ReadLocsAgree i s t) {b x : String} {sc : Nat} (hb : Loc.bank b ∈ memRd i)
    (hx : x ∈ readNames i) : s.loadIdx b x sc = t.loadIdx b x sc := by
  unfold JState.loadIdx
  rw [h.get hx]
  exact h.bank b (List.mem_append_right _ hb) _

end ReadLocsAgree

/-- One register written: the register files agree at `r = d` when the written values do. -/
theorem regs_ite_dep {s t : JState 64} {d r : String} {v v' : BitVec 64} (hr : r = d)
    (hv : v = v') : (if r = d then v else s.regs r) = (if r = d then v' else t.regs r) := by
  simp [hr, hv]

/-- Two registers written, `a` last: the register files agree at `r = a` and at `r = b` when
    the written values do. -/
theorem regs_ite₂_dep {s t : JState 64} {a b r : String} {u u' v v' : BitVec 64}
    (hr : r = a ∨ r = b) (hu : u = u') (hv : v = v') :
    (if r = a then u else if r = b then v else s.regs r)
      = (if r = a then u' else if r = b then v' else t.regs r) := by
  subst hu hv
  rcases hr with rfl | rfl <;> simp

/-- Dependence at a register. -/
theorem evalInstr_dep_reg (s t : JState 64) (i : JInstr 64) (h : ReadLocsAgree i s t)
    (r : String) (hx : Covered (wrLocs i) (.reg r)) :
    (evalInstr s i).regs r = (evalInstr t i).regs r := by
  have hw := mem_writtenNames_of_covered hx
  cases i with
  -- no register written
  | test _ _ | cmp _ _ | storeMem _ _ _ | storeMemIdx _ _ _ _ | clc | stc | testN _ _ _ | bt _ _
  | addToMem _ _ _ | cmpMem _ _ _ => exact absurd hw List.not_mem_nil
  -- `dst` and an operand read
  | add _ _ | sub _ _ | imul _ _ | and_ _ _ | or_ _ _ | xor_ _ _ | shl _ _ | shr _ _ | sar _ _
  | rol _ _ | ror _ _ | btr _ _ | bts _ _ | rorx _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.eval (List.subset_cons_self _ _)])
  -- `dst`, an operand and the carry flag read
  | adc _ _ | sbb _ _ | rcl _ _ | rcr _ _ | adcx _ _ | cmovb _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.eval (List.subset_cons_self _ _),
        h.flagB_cf List.mem_cons_self])
  | adox _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.eval (List.subset_cons_self _ _),
        h.flagB_of List.mem_cons_self])
  | cmove _ _ | cmovne _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.eval (List.subset_cons_self _ _),
        h.flagB_zf List.mem_cons_self])
  -- an operand read
  | mov _ _ => exact regs_ite_dep (List.mem_singleton.mp hw) (by rw [h.eval (List.Subset.refl _)])
  -- the carry flag read
  | setc _ => exact regs_ite_dep (List.mem_singleton.mp hw) (by rw [h.flagB_cf List.mem_cons_self])
  -- one register read
  | neg _ | not_ _ | inc _ | dec _ | movzx _ _ _ | movsx _ _ _ | imulri _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw) (by rw [h.get List.mem_cons_self])
  -- two registers read
  | andn _ _ _ | shlx _ _ _ | shrx _ _ _ | sarx _ _ _ | bzhi _ _ _ | lea _ _ _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.get (List.mem_cons_of_mem _ List.mem_cons_self)])
  -- `dst`, a register and an operand read
  | shld _ _ _ | shrd _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.get (List.mem_cons_of_mem _ List.mem_cons_self),
        h.eval (List.subset_cons_of_subset _ (List.subset_cons_self _ _))])
  -- a condition, `dst` and an operand read
  | cmovcc _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.eval (List.subset_cons_self _ _),
        h.condB (List.Subset.refl _)])
  | setcc _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.condB (List.Subset.refl _)])
  -- a memory cell read
  | loadMem _ _ _ | imulriMem _ _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw) (by rw [h.load List.mem_cons_self])
  -- a register and a memory cell read
  | addMem _ _ _ | imulMem _ _ _ | aluMem _ _ _ _ | andnMem _ _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.load List.mem_cons_self])
  | adcxMem _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.load List.mem_cons_self, h.flagB_cf List.mem_cons_self])
  | adoxMem _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.load List.mem_cons_self, h.flagB_of List.mem_cons_self])
  | cmovccMem _ _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.get List.mem_cons_self, h.load List.mem_cons_self, h.condB (List.Subset.refl _)])
  -- a register-indexed cell read
  | loadMemIdx _ _ _ _ =>
    exact regs_ite_dep (List.mem_singleton.mp hw)
      (by rw [h.loadIdx List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)])
  -- no input: the address marker of `loadSym`
  | loadSym _ _ => exact regs_ite_dep (List.mem_singleton.mp hw) rfl
  -- two registers written
  | mulx _ _ a b =>
    have he : x86_MULX_lo_hi (a.eval s) (b.eval s) = x86_MULX_lo_hi (a.eval t) (b.eval t) := by
      rw [h.eval (List.subset_append_left _ _), h.eval (List.subset_append_right _ _)]
    exact regs_ite₂_dep ((List.mem_cons.mp hw).imp_right List.mem_singleton.mp)
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  | mulxMem _ _ _ _ _ =>
    have he := congrArg₂ x86_MULX_lo_hi (h.eval (List.subset_cons_self _ _))
      (h.load List.mem_cons_self)
    exact regs_ite₂_dep ((List.mem_cons.mp hw).imp_right List.mem_singleton.mp)
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  | xchg _ _ =>
    have he := congrArg₂ x86_XCHG (h.get List.mem_cons_self)
      (h.get (List.mem_cons_of_mem _ List.mem_cons_self))
    exact regs_ite₂_dep ((List.mem_cons.mp hw).imp_right List.mem_singleton.mp).symm
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  | mul _ _ _ | imulWide _ _ _ =>
    exact regs_ite₂_dep ((List.mem_cons.mp hw).imp_right List.mem_singleton.mp).symm
      (by rw [h.get List.mem_cons_self, h.get (List.mem_cons_of_mem _ List.mem_cons_self)])
      (by rw [h.get List.mem_cons_self, h.get (List.mem_cons_of_mem _ List.mem_cons_self)])

/-- Dependence at a flag. -/
theorem evalInstr_dep_flag (s t : JState 64) (i : JInstr 64) (h : ReadLocsAgree i s t)
    (f : FlagId) (hx : Covered (wrLocs i) (.flag f)) :
    flagGet f (evalInstr s i).flags = flagGet f (evalInstr t i).flags := by
  obtain ⟨hR, hF, hC, hB⟩ := h
  have hop := @eval_agree s t
  cases i <;>
    first
      | (simp [wrLocs, writtenNames, flagWrites, memWr, covered_cons, covered_nil,
          Loc.covers] at hx; done)
      | (simp_all [rdLocs, wrLocs, memRd, memWr, readNames, writtenNames, flagReads,
          flagWrites, covered_cons, covered_nil, Loc.covers, evalInstr,
          JState.writeB5W, JState.writeB5, JState.writeB2W, JState.writeB4W,
          JState.writeB5W2, JState.writeB5N, JState.writeCFW, JState.writeB5Mem,
          JState.store, JState.flagB]
         all_goals cases f <;> simp_all [flagGet])

/-- Dependence at a memory cell. -/
theorem evalInstr_dep_cell (s t : JState 64) (i : JInstr 64) (h : ReadLocsAgree i s t)
    (b : String) (o : Int) (hx : Covered (wrLocs i) (.cell b o)) :
    (evalInstr s i).mem b o = (evalInstr t i).mem b o := by
  obtain ⟨hR, hF, hC, hB⟩ := h
  have hop := @eval_agree s t
  cases i <;>
    first
      | (simp [wrLocs, writtenNames, flagWrites, memWr, covered_cons, covered_nil,
          Loc.covers] at hx; done)
      | simp_all [rdLocs, wrLocs, memRd, memWr, readNames, writtenNames, flagReads, flagWrites,
          covered_cons, covered_nil, Loc.covers, evalInstr, JState.writeB5Mem, JState.store,
          JState.storeIdx]

/-- **Dependence.** Two states that agree at the read locations of `i` give results that
    agree at its write locations. -/
theorem evalInstr_dep (s t : JState 64) (i : JInstr 64)
    (h : ∀ x, Covered (rdLocs i) x → AgreeAt s t x) (x : Atom)
    (hx : Covered (wrLocs i) x) : AgreeAt (evalInstr s i) (evalInstr t i) x := by
  cases x with
  | reg r => exact evalInstr_dep_reg s t i (.of h) r hx
  | flag f => exact evalInstr_dep_flag s t i (.of h) f hx
  | cell b o => exact evalInstr_dep_cell s t i (.of h) b o hx

/-! ## 4. Commutation -/

/-- **Independent instructions commute** on every state. -/
theorem evalInstr_comm_of_indepF (s : JState 64) (a b : JInstr 64) (h : indepF a b = true) :
    evalInstr (evalInstr s a) b = evalInstr (evalInstr s b) a := by
  simp only [indepF, Bool.and_eq_true] at h
  obtain ⟨⟨hww, hwr⟩, hrw⟩ := h
  apply eq_of_agreeAt
  intro x
  by_cases hb : Covered (wrLocs b) x
  · -- `x` is written by `b`, so not by `a`.
    have hna : ¬ Covered (wrLocs a) x := fun ha => not_covered_of_disjointLocs hww ha hb
    have h1 : AgreeAt (evalInstr (evalInstr s a) b) (evalInstr s b) x :=
      evalInstr_dep _ _ b (fun y hy => evalInstr_frame s a y
        (fun ha => not_covered_of_disjointLocs hwr ha hy)) x hb
    exact h1.trans (evalInstr_frame _ a x hna).symm
  · by_cases ha : Covered (wrLocs a) x
    · have h1 : AgreeAt (evalInstr (evalInstr s b) a) (evalInstr s a) x :=
        evalInstr_dep _ _ a (fun y hy => evalInstr_frame s b y
          (fun hb' => not_covered_of_disjointLocs hrw hy hb')) x ha
      exact (evalInstr_frame _ b x hb).trans h1.symm
    · exact ((evalInstr_frame _ b x hb).trans (evalInstr_frame s a x ha)).trans
        ((evalInstr_frame _ a x ha).trans (evalInstr_frame s b x hb)).symm

/-- The block form: an `indepF` adjacent pair can be transposed anywhere in a block. -/
theorem runBlock_swap_of_indepF (s : JState 64) (pre post : List (JInstr 64))
    (a b : JInstr 64) (h : indepF a b = true) :
    runBlock s (pre ++ a :: b :: post) = runBlock s (pre ++ b :: a :: post) := by
  induction pre generalizing s with
  | nil => simp only [List.nil_append, runBlock_cons, evalInstr_comm_of_indepF s a b h]
  | cons i pre ih => simp only [List.cons_append, runBlock_cons, ih]

/-! ## 5. The certificate check of a swap sequence -/

/-- The transposition at position `k` is certified by `indepF`. -/
def checkSwapF (k : Nat) (block : List (JInstr 64)) : Bool :=
  match k, block with
  | 0, i1 :: i2 :: _ => indepF i1 i2
  | k + 1, _ :: rest => checkSwapF k rest
  | _, _ => false

/-- A certified transposition preserves `runBlock`. -/
theorem runBlock_applySwap_eqF (s : JState 64) (k : Nat) (block : List (JInstr 64))
    (h : checkSwapF k block = true) :
    runBlock s (applySwap k block) = runBlock s block := by
  induction k generalizing s block with
  | zero =>
    match block with
    | [] | [_] => simp [checkSwapF] at h
    | i1 :: i2 :: rest =>
      simp only [checkSwapF] at h
      simp only [applySwap, runBlock_cons, evalInstr_comm_of_indepF s i1 i2 h]
  | succ k ih =>
    match block with
    | [] | [_] => simp [checkSwapF] at h
    | x :: y :: rest =>
      simp only [checkSwapF] at h
      simp only [applySwap, runBlock_cons]
      exact ih (evalInstr s x) (y :: rest) h

/-- Every transposition of `swaps`, applied left to right, is certified by `indepF` against
    the block it acts on. -/
def checkAdjTranspositionsF : List Nat → List (JInstr 64) → Bool
  | [], _ => true
  | k :: ks, b => checkSwapF k b && checkAdjTranspositionsF ks (applySwap k b)

/-- **Soundness of the certificate check**: a certified swap sequence preserves `runBlock` on
    every state. -/
theorem runBlock_perm_eqF (s : JState 64) (swaps : List Nat) (block : List (JInstr 64))
    (h : checkAdjTranspositionsF swaps block = true) :
    runBlock s (applySwaps swaps block) = runBlock s block := by
  induction swaps generalizing block with
  | nil => rfl
  | cons k ks ih =>
    simp only [checkAdjTranspositionsF, Bool.and_eq_true] at h
    have happ : applySwaps (k :: ks) block = applySwaps ks (applySwap k block) := rfl
    rw [happ, ih _ h.2, runBlock_applySwap_eqF s k block h.1]

/-! ## 6. Segments

A segment is a list of instructions, for example the machine instructions of one
instruction of a printed body. Two segments are independent when every instruction of the
one is independent of every instruction of the other; independent adjacent segments can be
transposed. -/

/-- Every instruction of `u` is independent of every instruction of `v`. -/
def indepSeg (u v : List (JInstr 64)) : Bool :=
  u.all fun a => v.all fun b => indepF a b

/-- An instruction independent of every instruction of `v` moves past `v`. -/
theorem runBlock_move_past (s : JState 64) (a : JInstr 64) (v w : List (JInstr 64))
    (h : ∀ b ∈ v, indepF a b = true) :
    runBlock s (a :: (v ++ w)) = runBlock s (v ++ a :: w) := by
  induction v generalizing s with
  | nil => rfl
  | cons b v ih =>
    have hb := h b List.mem_cons_self
    simp only [List.cons_append, runBlock_cons]
    rw [evalInstr_comm_of_indepF s a b hb, ← runBlock_cons]
    exact ih _ fun c hc => h c (List.mem_cons_of_mem _ hc)

/-- **Independent segments commute.** -/
theorem runBlock_seg_comm (s : JState 64) (u v w : List (JInstr 64))
    (h : indepSeg u v = true) : runBlock s (u ++ v ++ w) = runBlock s (v ++ u ++ w) := by
  induction u generalizing s with
  | nil => simp
  | cons a u ih =>
    simp only [indepSeg, List.all_cons, Bool.and_eq_true, List.all_eq_true] at h
    have hu : indepSeg u v = true := by
      simp only [indepSeg, List.all_eq_true]
      exact h.2
    simp only [List.cons_append, runBlock_cons, List.append_assoc] at ih ⊢
    rw [ih _ hu, ← runBlock_cons]
    have := runBlock_move_past s a v (u ++ w) h.1
    simpa only [List.append_assoc, List.cons_append] using this

/-- Transpose the segments at positions `k` and `k + 1`. -/
def swapSeg : Nat → List (List (JInstr 64)) → List (List (JInstr 64))
  | 0, u :: v :: rest => v :: u :: rest
  | k + 1, x :: rest => x :: swapSeg k rest
  | _, xs => xs

/-- The transposition of the segments at `k` and `k + 1` is certified by `indepSeg`. -/
def checkSwapSeg : Nat → List (List (JInstr 64)) → Bool
  | 0, u :: v :: _ => indepSeg u v
  | k + 1, _ :: rest => checkSwapSeg k rest
  | _, _ => false

/-- A certified segment transposition preserves `runBlock` of the concatenation. -/
theorem runBlock_swapSeg (s : JState 64) (k : Nat) (segs : List (List (JInstr 64)))
    (h : checkSwapSeg k segs = true) :
    runBlock s (swapSeg k segs).flatten = runBlock s segs.flatten := by
  induction k generalizing s segs with
  | zero =>
    match segs with
    | [] | [_] => simp [checkSwapSeg] at h
    | u :: v :: rest =>
      simp only [checkSwapSeg] at h
      simp only [swapSeg, List.flatten_cons, ← List.append_assoc]
      exact (runBlock_seg_comm s u v _ h).symm
  | succ k ih =>
    match segs with
    | [] | [_] => simp [checkSwapSeg] at h
    | x :: y :: rest =>
      simp only [checkSwapSeg] at h
      simp only [swapSeg, List.flatten_cons]
      rw [runBlock_append (s := s) x, runBlock_append (s := s) x]
      simpa only [List.flatten_cons] using ih (runBlock s x) (y :: rest) h

/-- Every segment transposition of `swaps`, applied left to right, is certified. -/
def checkSegSwaps : List Nat → List (List (JInstr 64)) → Bool
  | [], _ => true
  | k :: ks, b => checkSwapSeg k b && checkSegSwaps ks (swapSeg k b)

/-- Apply segment transpositions left to right. -/
def applySegSwaps (swaps : List Nat) (segs : List (List (JInstr 64))) :
    List (List (JInstr 64)) :=
  swaps.foldl (fun b k => swapSeg k b) segs

/-- **Soundness of the segment certificate**: a certified sequence of segment
    transpositions preserves `runBlock` of the concatenation on every state. -/
theorem runBlock_segSwaps (s : JState 64) (swaps : List Nat) (segs : List (List (JInstr 64)))
    (h : checkSegSwaps swaps segs = true) :
    runBlock s (applySegSwaps swaps segs).flatten = runBlock s segs.flatten := by
  induction swaps generalizing segs with
  | nil => rfl
  | cons k ks ih =>
    simp only [checkSegSwaps, Bool.and_eq_true] at h
    have happ : applySegSwaps (k :: ks) segs = applySegSwaps ks (swapSeg k segs) := rfl
    rw [happ, ih _ h.2, runBlock_swapSeg s k segs h.1]

end CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint
