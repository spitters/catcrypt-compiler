/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Liveness-based general-purpose register re-allocation on `Lprog` bodies

An `Lprog → Lprog` pass over the physical-register body the exporter produces.
Each maximal run of instructions in the fragment `fragOf?` accepts is re-allocated
as a whole: every definition of a general-purpose register or of a frame cell
`k.N` starts a web, a two-address instruction ties its destination web to the
web of its first source, and the webs are coloured with the pool registers or kept at
their own name. The register file is a trailing parameter `abi : IsaAbi` with default
`x86Abi`: the pool is `abi.allocPool` (at `x86Abi` the thirteen registers of
`gpRegNames`; `R14`/`R15` stay the printer's scratch registers), the general-purpose
registers are `gpRegs abi`, and the registers live at a return are `abi.calleeSaved` and
`abi.retRegs`. The fragment alphabet is a trailing parameter `recog` with default the x86
alphabet `isRecognizedOpn`; `isaRecognized I` is the alphabet of an instruction set `I`,
which excludes every mnemonic with an implicit register read in `I.implicitReads`. The
shape tests `movClass`, `freeUnary`, `tiedOpn` and `isCopy64` are x86 mnemonic tests.
The colouring prefers, for a 64-bit copy whose source dies at the copy, the source's colour, so the copy becomes a self-move and is dropped; a frame cell
whose web fits in a free register is promoted to that register. A move whose
destination is dead is dropped.

The allocator is untrusted. Its decisions (one location per instruction) are
passed to `goAcc`, which checks them in one forward pass against the backward
liveness `annotate` computes and materializes the renamed run; a run whose
decisions fail the check is emitted unchanged. The check is evaluated by the
emitter on every run.

## The check

At every instruction, with `m` the current name-to-location map and `la` the
names live after it:

* the base register of every `mem.<B>.<off>` operand is mapped to itself;
* the location `c` of a written name `d` is a pool register or `d` itself;
* `c` differs from the location of every other name live after the instruction;
* a tied two-address instruction writes the location its first source is in; an
  instruction outside the shapes the printer renders from any register choice
  keeps its destination and reads its sources at their own names;
* at the end of the run every live-out name is at its own location.

## Semantics

`runWith sem` runs a fragment list over `JasminLsem.Lstate` for an arbitrary
interpretation `sem` of the mnemonics; `lsemStraight` is the instance
`semL` (`lsemStraight_map_toR`). The soundness theorem holds for every `sem`
that interprets the two 64-bit copy mnemonics as the identity, so it covers the
array-ABI spellings `LOAD:64`/`STORE:64` read as the moves they print as. Memory
cells are `lvm` names in this model; the base check keeps every address
register at its own location, so a renamed program addresses the same memory.

## Main results

* `goAcc_sound`: a checked materialization, started in a related state, ends in
  a state that agrees with the source run on memory, on every name that is not
  a location and on every live-out name.
* `reallocRun_sound`, `reallocRun_lsemStraight`: the same for the pass on one
  run, whatever the decisions.
* `reallocLprog`: the pass on every function body, split at the instructions
  outside the fragment. A run's live-out set is the frame cells named after it
  (every frame cell of the body when the body has a label, since a jump back to
  it reaches a run from below), with the callee-saved, return and result
  registers (`retLive`) when a return follows it and all fifteen
  general-purpose registers otherwise.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi IsaData)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (stripAbiTag x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP physGPs nameReads isRecognizedOpn lsemStep_reg_nonmem)

/-! ## 1. Names

Every definition that names a register takes the register file and calling convention
`abi : IsaAbi` as a trailing parameter with default `x86Abi`. -/

/-- The general-purpose registers of a register file: the allocation pool followed by the
    scratch registers, the primary scratch last. At `x86Abi` this is
    `LcmdCopyPropagate.physGPs` (`gpRegs_x86`). -/
def gpRegs (abi : IsaAbi := x86Abi) : List String := abi.allocPool ++ abi.scratch.reverse

/-- A general-purpose register of the register file. -/
def isGP (n : String) (abi : IsaAbi := x86Abi) : Bool := (gpRegs abi).contains n

/-- A location: a general-purpose register or a frame cell `k.N`. -/
def isLoc (n : String) (abi : IsaAbi := x86Abi) : Bool := isGP n abi || "k.".isPrefixOf n

/-- A frame cell `k.N`. -/
def isFrame (n : String) : Bool := "k.".isPrefixOf n

/-- A pool register: a register of the allocation pool `abi.allocPool`, which excludes the
    scratch registers. -/
def isPool (n : String) (abi : IsaAbi := x86Abi) : Bool := abi.allocPool.contains n

/-- The x86 general-purpose registers are the fifteen of `LcmdCopyPropagate.physGPs`, in
    the same order. -/
theorem gpRegs_x86 : gpRegs = physGPs := rfl

/-- At `x86Abi` a general-purpose register is one of `LcmdCopyPropagate.physGPs`. -/
theorem isGP_x86 (n : String) : isGP n = isPhysGP n := rfl

/-- At `x86Abi` a location is one of the fifteen general-purpose registers or a frame
    cell. -/
theorem isLoc_x86 (n : String) : isLoc n = (isPhysGP n || "k.".isPrefixOf n) := rfl

/-- At `x86Abi` a pool register is a general-purpose register other than the scratch
    registers `R14` and `R15`. -/
theorem isPool_x86 (n : String) : isPool n = (isPhysGP n && n != "R14" && n != "R15") := by
  by_cases h14 : n = "R14"
  · subst h14; decide
  · by_cases h15 : n = "R15"
    · subst h15; decide
    · have e14 : (n != "R14") = true := by simpa using h14
      have e15 : (n != "R15") = true := by simpa using h15
      simp [isPool, isPhysGP, physGPs, gpRegNames, h14, h15, e14, e15]

theorem isLoc_of_isPool {n : String} {abi : IsaAbi} (h : isPool n abi = true) :
    isLoc n abi = true := by
  have hm : n ∈ abi.allocPool := by simpa [isPool] using h
  simp [isLoc, isGP, gpRegs, hm]

/-- The general-purpose registers a register-name string reads as an address:
    `LcmdCopyPropagate.nameReads` over the register file `abi`. -/
def nameReadsAt (n : String) (abi : IsaAbi := x86Abi) : List String :=
  if isGP n abi then [n]
  else if "mem.".isPrefixOf n then
    match ((n.drop 4).toString).splitOn "." with
    | [base, _] => if isGP base abi then [base] else []
    | _ => []
  else []

/-- At `x86Abi`, `nameReadsAt` is `LcmdCopyPropagate.nameReads`. -/
theorem nameReadsAt_x86 (n : String) : nameReadsAt n = nameReads n := rfl

/-- The address registers of a memory-cell name `mem.<B>.<off>`. -/
def baseRegs (n : String) (abi : IsaAbi := x86Abi) : List String :=
  if "mem.".isPrefixOf n then nameReadsAt n abi else []

/-- At `x86Abi` the address registers are those `LcmdCopyPropagate.nameReads` gives. -/
theorem baseRegs_x86 (n : String) :
    baseRegs n = if "mem.".isPrefixOf n then nameReads n else [] := rfl

/-! ## 2. The fragment -/

/-- An instruction `Lopn [.reg d] opn srcs` of the fragment, with its position tag. -/
structure FI where
  /-- The position tag of the `Linstr`. -/
  ii : Nat
  /-- The destination name. -/
  d : String
  /-- The mnemonic. -/
  opn : String
  /-- The source operands. -/
  srcs : List LOperand
  deriving Inhabited, Repr

/-- The instruction an `FI` stands for. -/
def FI.toR (i : FI) : LinstrR := .Lopn [.reg i.d] i.opn i.srcs

/-- The `Linstr` an `FI` stands for. -/
def FI.toL (i : FI) : Linstr := ⟨i.ii, i.toR⟩

/-- A register or immediate operand. -/
def regOrImm : LOperand → Bool
  | .reg _ => true
  | .imm _ => true
  | _ => false

/-- Register and immediate sources only, and not a runtime-indexed memory opcode. -/
def FI.wf (i : FI) : Bool :=
  i.srcs.all regOrImm && i.opn != "LOADIDX" && i.opn != "STOREIDX"

/-- The fragment view of an instruction: a single-destination `Lopn` with register and
    immediate sources whose mnemonic the alphabet `recog` accepts. The default alphabet is
    `LcmdCopyPropagate.isRecognizedOpn`, the x86 alphabet, which excludes the mnemonics
    with an implicit register read. -/
def fragOf? (li : Linstr) (recog : String → Bool := isRecognizedOpn) : Option FI :=
  match li.li_i with
  | .Lopn [.reg d] opn srcs =>
      let i : FI := ⟨li.li_ii, d, opn, srcs⟩
      if recog opn && i.wf then some i else none
  | _ => none

/-- The fragment alphabet of an instruction set `I`: a recognised mnemonic that reads no
    register implicitly according to `I.implicitReads`. -/
def isaRecognized (I : IsaData) (opn : String) : Bool :=
  (I.implicitReads opn).isEmpty && isRecognizedOpn opn

/-- A mnemonic of the alphabet of `I` has no implicit register read in `I`. -/
theorem implicitReads_of_isaRecognized {I : IsaData} {opn : String}
    (h : isaRecognized I opn = true) : I.implicitReads opn = [] := by
  simp only [isaRecognized, Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.1

/-- An instruction of the fragment over the alphabet of `I` has no implicit register read
    in `I`: every register it reads is among its operands. -/
theorem fragOf?_implicitReads {I : IsaData} {li : Linstr} {i : FI}
    (h : fragOf? li (isaRecognized I) = some i) : I.implicitReads i.opn = [] := by
  unfold fragOf? at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact implicitReads_of_isaRecognized hc.1
    · cases h
  · cases h

/-- The locations an operand reads: itself, or the address register of a memory cell. -/
def opReads : LOperand → (abi : IsaAbi := x86Abi) → List String
  | .reg n, abi => if isLoc n abi then [n] else baseRegs n abi
  | _, _ => []

/-- The address registers an operand names. -/
def opBases : LOperand → (abi : IsaAbi := x86Abi) → List String
  | .reg n, abi => baseRegs n abi
  | _, _ => []

/-- The locations an instruction reads, address registers included. -/
def FI.reads (i : FI) (abi : IsaAbi := x86Abi) : List String :=
  i.srcs.flatMap (fun o => opReads o abi) ++ baseRegs i.d abi

/-- The address registers an instruction names. -/
def FI.bases (i : FI) (abi : IsaAbi := x86Abi) : List String :=
  i.srcs.flatMap (fun o => opBases o abi) ++ baseRegs i.d abi

/-! ## 3. Liveness -/

/-- Add the names of `xs` absent from `L`. -/
def addNew (xs L : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) L

theorem mem_addNew (xs : List String) :
    ∀ (L : List String) (n : String), n ∈ addNew xs L ↔ n ∈ xs ∨ n ∈ L := by
  induction xs with
  | nil => intro L n; simp [addNew]
  | cons x xs ih =>
    intro L n
    show n ∈ addNew xs (if L.contains x then L else x :: L) ↔ _
    rw [ih]
    by_cases hx : L.contains x = true
    · simp only [hx, if_true, List.mem_cons]
      have : x ∈ L := by simpa using hx
      constructor
      · rintro (h | h) <;> simp [h]
      · rintro ((rfl | h) | h) <;> simp_all
    · simp only [Bool.not_eq_true] at hx
      simp only [hx, Bool.false_eq_true, if_false, List.mem_cons]
      tauto

/-- The names live before an instruction, from those live after it. -/
def liveBefore (i : FI) (la : List String) (abi : IsaAbi := x86Abi) : List String :=
  addNew (i.reads abi) (la.filter (fun n => n != i.d))

theorem reads_mem_liveBefore {abi : IsaAbi} {i : FI} {la : List String} {n : String}
    (h : n ∈ i.reads abi) : n ∈ liveBefore i la abi :=
  (mem_addNew _ _ _).2 (Or.inl h)

theorem mem_liveBefore {abi : IsaAbi} {i : FI} {la : List String} {n : String} (h : n ∈ la)
    (hd : n ≠ i.d) : n ∈ liveBefore i la abi :=
  (mem_addNew _ _ _).2 (Or.inr (List.mem_filter.2 ⟨h, by simpa using hd⟩))

/-- Each instruction paired with the names live after it, and the names live at the
    start, for the live-out set `lend`. -/
def annotate (lend : List String) (is : List FI) (abi : IsaAbi := x86Abi) :
    List (FI × List String) × List String :=
  is.foldr (fun i p => ((i, p.2) :: p.1, liveBefore i p.2 abi)) ([], lend)

theorem annotate_cons {abi : IsaAbi} (lend : List String) (i : FI) (is : List FI) :
    annotate lend (i :: is) abi =
      ((i, (annotate lend is abi).2) :: (annotate lend is abi).1,
        liveBefore i (annotate lend is abi).2 abi) :=
  rfl

/-! ## 4. The check and the materialization -/

/-- The current location of every name; a name without an entry is at itself. -/
abbrev Cur := Std.HashMap String String

/-- The location of `n`. -/
def look (m : Cur) (n : String) : String := m.getD n n

theorem look_insert (m : Cur) (k v n : String) :
    look (m.insert k v) n = if k = n then v else look m n := by
  simp [look, Std.HashMap.getD_insert]

theorem look_empty (n : String) : look ({} : Cur) n = n := by
  simp [look]

/-- Rename a location operand to its current location. -/
def renOp (m : Cur) : LOperand → (abi : IsaAbi := x86Abi) → LOperand
  | .reg n, abi => if isLoc n abi then .reg (look m n) else .reg n
  | o, _ => o

/-- The 64-bit register copy mnemonics. -/
def isCopy64 (opn : String) : Bool := opn == "MOV:64" || opn == "MOVQ"

/-- A move: a register, memory or immediate move that writes no flag. -/
def movClass (opn : String) : Bool :=
  let b := stripAbiTag opn
  b == "MOV" || b == "MOVQ" || b == "LOAD"

/-- A single-source instruction the printer renders correctly whatever registers
    its destination and source are in. -/
def freeUnary (opn : String) : Bool :=
  movClass opn || stripAbiTag opn == "STORE" || (parseImmShiftMnem opn).isSome

/-- The two-address arithmetic mnemonics, printed `op src, dst`. -/
def tiedOpn (opn : String) : Bool :=
  match stripAbiTag opn with
  | "ADD" | "SUB" | "AND" | "OR" | "XOR" | "ADC" | "SBB" | "MUL" | "SHL" | "SHR" | "SAR" =>
      true
  | _ => false

/-- How the printer constrains an instruction's registers. -/
inductive Shape where
  /-- Any destination location. -/
  | free
  /-- The destination location is the first source's. -/
  | tied
  /-- Every location is the name itself. -/
  | fixed
  deriving DecidableEq, Inhabited

/-- The shape of an instruction. -/
def shapeOf (i : FI) : Shape :=
  if freeUnary i.opn && i.srcs.length == 1 then .free
  else if stripAbiTag i.opn == "ANDN" && i.srcs.length == 2 then .free
  else if tiedOpn i.opn && i.srcs.head? == some (.reg i.d) then .tied
  else .fixed

/-- The allowed locations of a web of `d`: a pool register or `d`. -/
def okLoc (d c : String) (abi : IsaAbi := x86Abi) : Bool := isPool c abi || c == d

/-- No name live after the write, other than `d`, is at `c`. -/
def noClobber (m : Cur) (la : List String) (d c : String) : Bool :=
  la.all (fun n => n == d || look m n != c)

/-- Every address register is at its own location. -/
def basesOk (m : Cur) (i : FI) (abi : IsaAbi := x86Abi) : Bool :=
  (i.bases abi).all (fun b => look m b == b)

/-- The printer shape is respected by the destination location `c`. -/
def shapeOk (m : Cur) (i : FI) (c : String) (abi : IsaAbi := x86Abi) : Bool :=
  match shapeOf i with
  | .free => true
  | .tied => c == look m i.d
  | .fixed => c == i.d && (i.reads abi).all (fun x => look m x == x)

/-- Check the decisions `cs` against the annotated run and materialize it, the
    output accumulated in reverse in `acc`. `none` when a check fails. -/
def goAcc (lend : List String) : Cur → List (FI × List String) → List String → List FI →
    (abi : IsaAbi := x86Abi) → Option (List FI)
  | m, [], [], acc, _ => if lend.all (fun n => look m n == n) then some acc.reverse else none
  | m, (i, la) :: rest, c :: cs, acc, abi =>
      if basesOk m i abi then
        if isLoc i.d abi then
          if okLoc i.d c abi && shapeOk m i c abi then
            if isCopy64 i.opn && i.srcs.map (fun o => renOp m o abi) == [.reg c] then
              goAcc lend (m.insert i.d c) rest cs acc abi
            else if movClass i.opn && !la.contains i.d then
              goAcc lend m rest cs acc abi
            else if noClobber m la i.d c then
              goAcc lend (m.insert i.d c) rest cs
                (⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o abi)⟩ :: acc) abi
            else none
          else none
        else if shapeOk m i i.d abi then
          goAcc lend m rest cs
            (⟨i.ii, i.d, i.opn, i.srcs.map (fun o => renOp m o abi)⟩ :: acc) abi
        else none
      else none
  | _, _, _, _, _ => none

/-! ## 5. Semantics -/

/-- One fragment instruction under the interpretation `sem`. -/
def stepWith {w : Nat} (sem : String → List (BitVec w) → Option (BitVec w)) (i : FI)
    (s : Lstate w) : Option (Lstate w) :=
  match sem i.opn (i.srcs.map (evalOperand s)) with
  | some v => some ((s.setReg i.d v).nextPc)
  | none => none

/-- A fragment list under the interpretation `sem`. -/
def runWith {w : Nat} (sem : String → List (BitVec w) → Option (BitVec w)) :
    List FI → Lstate w → Option (Lstate w)
  | [], s => some s
  | i :: is, s =>
      match stepWith sem i s with
      | some s' => runWith sem is s'
      | none => none

theorem runWith_append {w : Nat} (sem : String → List (BitVec w) → Option (BitVec w))
    (a b : List FI) (s : Lstate w) :
    runWith sem (a ++ b) s = (runWith sem a s).bind (runWith sem b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i a ih =>
    simp only [List.cons_append, runWith]
    cases stepWith sem i s with
    | none => rfl
    | some s' => exact ih s'

/-- The interpretation of `lsemStep`. -/
def semL {w : Nat} (opn : String) (vs : List (BitVec w)) : Option (BitVec w) :=
  applyOpn (stripWidthTag opn) vs

theorem semL_copy {w : Nat} (opn : String) (a : BitVec w) (h : isCopy64 opn = true) :
    semL opn [a] = some a := by
  simp only [isCopy64, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · rw [semL, show stripWidthTag "MOV:64" = "MOV" from by decide +kernel]; rfl
  · rw [semL, show stripWidthTag "MOVQ" = "MOVQ" from by decide +kernel]; rfl

theorem lsemStep_toR {w : Nat} (i : FI) (hwf : i.wf = true) (s : Lstate w) :
    lsemStep i.toR s = stepWith semL i s := by
  simp only [FI.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hwf
  rw [FI.toR, lsemStep_reg_nonmem _ _ _ _ ⟨hwf.1.2, hwf.2⟩]
  rfl

theorem lsemStraight_map_toR {w : Nat} (is : List FI) (hwf : ∀ i ∈ is, i.wf = true)
    (s : Lstate w) : lsemStraight (is.map FI.toR) s = runWith semL is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, lsemStraight_cons, runWith]
    rw [lsemStep_toR i (hwf i (by simp))]
    cases stepWith semL i s with
    | none => rfl
    | some s' => exact ih (fun j hj => hwf j (by simp [hj])) s'

/-! ## 6. Soundness of the check -/

/-- The relation between a source state `σ` and a renamed state `τ`: equal memory,
    equal non-location names, and every live location name `n` holding its source
    value at its location `look m n`. -/
def Rel {w : Nat} (m : Cur) (L : List String) (σ τ : Lstate w) (abi : IsaAbi := x86Abi) :
    Prop :=
  τ.lmem = σ.lmem ∧ (∀ x, isLoc x abi = false → τ.lvm x = σ.lvm x) ∧
    ∀ n ∈ L, isLoc n abi = true → isLoc (look m n) abi = true ∧ τ.lvm (look m n) = σ.lvm n

/-- Agreement at the end of a run: equal memory and equal values on every name that
    is not a location or is live out. -/
def Final {w : Nat} (lend : List String) (σ τ : Lstate w) (abi : IsaAbi := x86Abi) : Prop :=
  τ.lmem = σ.lmem ∧ ∀ x, (isLoc x abi = false ∨ x ∈ lend) → τ.lvm x = σ.lvm x

theorem Rel.empty {w : Nat} {abi : IsaAbi} (L : List String) (σ : Lstate w) :
    Rel {} L σ σ abi :=
  ⟨rfl, fun _ _ => rfl, fun n _ hn => by simp [look_empty, hn]⟩

theorem renOp_regOrImm {abi : IsaAbi} (m : Cur) (o : LOperand) (h : regOrImm o = true) :
    regOrImm (renOp m o abi) = true := by
  cases o with
  | reg n => by_cases hn : isLoc n abi = true <;> simp [renOp, hn, regOrImm]
  | imm _ => rfl
  | _ => simp [regOrImm] at h

/-- The renamed sources evaluate in `τ` to the source values in `σ`. -/
theorem eval_renOp {w : Nat} {abi : IsaAbi} {m : Cur} {L : List String} {σ τ : Lstate w}
    {i : FI} (hR : Rel m L σ τ abi) (hL : ∀ n ∈ i.reads abi, n ∈ L)
    (hwf : i.srcs.all regOrImm = true) {o : LOperand} (ho : o ∈ i.srcs) :
    evalOperand τ (renOp m o abi) = evalOperand σ o := by
  have hro : regOrImm o = true := List.all_eq_true.1 hwf o ho
  cases o with
  | reg n =>
    by_cases hn : isLoc n abi = true
    · have hr : n ∈ i.reads abi := by
        simp only [FI.reads, List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨.reg n, ho, by simp [opReads, hn]⟩
      simp only [renOp, hn, if_true, evalOperand]
      exact (hR.2.2 n (hL n hr) hn).2
    · simp only [Bool.not_eq_true] at hn
      simp only [renOp, hn, Bool.false_eq_true, if_false, evalOperand]
      exact hR.2.1 n hn
  | imm _ => rfl
  | _ => simp [regOrImm] at hro

theorem map_eval_renOp {w : Nat} {abi : IsaAbi} {m : Cur} {L : List String}
    {σ τ : Lstate w} {i : FI} (hR : Rel m L σ τ abi) (hL : ∀ n ∈ i.reads abi, n ∈ L)
    (hwf : i.srcs.all regOrImm = true) :
    (i.srcs.map (fun o => renOp m o abi)).map (evalOperand τ) =
      i.srcs.map (evalOperand σ) := by
  rw [List.map_map]
  exact List.map_congr_left (fun o ho => eval_renOp hR hL hwf ho)

theorem wf_of_srcs {i : FI} (hwf : i.wf = true) : i.srcs.all regOrImm = true := by
  simp only [FI.wf, Bool.and_eq_true] at hwf
  exact hwf.1.1

theorem wf_rename {abi : IsaAbi} (m : Cur) (i : FI) (c : String) (hwf : i.wf = true) :
    FI.wf ⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o abi)⟩ = true := by
  simp only [FI.wf, Bool.and_eq_true] at hwf ⊢
  refine ⟨⟨?_, hwf.1.2⟩, hwf.2⟩
  simp only [List.all_map, List.all_eq_true, Function.comp_apply]
  exact fun o ho => renOp_regOrImm m o (List.all_eq_true.1 hwf.1.1 o ho)

/-- **Soundness of the check.** When `goAcc` accepts decisions `cs` for the annotated
    run of `is`, and the source run from `σ` ends in `σ'`, the materialized run from
    any `τ` related to `σ` on the names live at the start ends in a state that agrees
    with `σ'` on memory, on every non-location name and on every live-out name. Every
    materialized instruction is in the fragment. -/
theorem goAcc_sound {w : Nat} {abi : IsaAbi}
    (sem : String → List (BitVec w) → Option (BitVec w))
    (hcopy : ∀ (opn : String) (a : BitVec w), isCopy64 opn = true → sem opn [a] = some a)
    (lend : List String) :
    ∀ (is : List FI) (m : Cur) (cs : List String) (acc out : List FI) (σ σ' τ : Lstate w),
      (∀ i ∈ is, i.wf = true) →
      goAcc lend m (annotate lend is abi).1 cs acc abi = some out →
      Rel m (annotate lend is abi).2 σ τ abi →
      runWith sem is σ = some σ' →
      ∃ rest τ', out = acc.reverse ++ rest ∧ (∀ j ∈ rest, j.wf = true) ∧
        runWith sem rest τ = some τ' ∧ Final lend σ' τ' abi := by
  intro is
  induction is with
  | nil =>
    intro m cs acc out σ σ' τ _ hgo hR hrun
    cases cs with
    | cons _ _ => simp [annotate, goAcc] at hgo
    | nil =>
      simp only [annotate, List.foldr_nil, goAcc] at hgo hR
      split at hgo
      · rename_i hall
        simp only [Option.some.injEq] at hgo
        simp only [runWith, Option.some.injEq] at hrun
        subst hgo hrun
        refine ⟨[], τ, by simp, by simp, rfl, hR.1, fun x hx => ?_⟩
        by_cases hl : isLoc x abi = true
        · have hxl : x ∈ lend := by
            rcases hx with h | h
            · simp [hl] at h
            · exact h
          have h1 := (hR.2.2 x hxl hl).2
          have h2 : look m x = x := by simpa using List.all_eq_true.1 hall x hxl
          rw [h2] at h1
          exact h1
        · exact hR.2.1 x (by simpa using hl)
      · exact absurd hgo (by simp)
  | cons i is ih =>
    intro m cs acc out σ σ' τ hwf hgo hR hrun
    have hwfi : i.wf = true := hwf i (by simp)
    have hwfs : ∀ j ∈ is, j.wf = true := fun j hj => hwf j (by simp [hj])
    have hsrc := wf_of_srcs hwfi
    rw [annotate_cons] at hgo hR
    set la := (annotate lend is abi).2 with hla
    simp only [runWith] at hrun
    cases hstep : stepWith sem i σ with
    | none => rw [hstep] at hrun; exact absurd hrun (by simp)
    | some σ1 =>
    rw [hstep] at hrun
    unfold stepWith at hstep
    cases hv : sem i.opn (i.srcs.map (evalOperand σ)) with
    | none => rw [hv] at hstep; exact absurd hstep (by simp)
    | some v =>
    rw [hv] at hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only at hrun
    have hreads : ∀ n ∈ i.reads abi, n ∈ liveBefore i la abi :=
      fun n hn => reads_mem_liveBefore hn
    have hev := map_eval_renOp hR hreads hsrc
    cases cs with
    | nil => simp [goAcc] at hgo
    | cons c cs =>
    simp only [goAcc] at hgo
    by_cases hb : basesOk m i abi = true
    · rw [if_pos hb] at hgo
      by_cases hd : isLoc i.d abi = true
      · rw [if_pos hd] at hgo
        by_cases hok : (okLoc i.d c abi && shapeOk m i c abi) = true
        · rw [if_pos hok] at hgo
          have hc : isLoc c abi = true := by
            simp only [Bool.and_eq_true, okLoc, Bool.or_eq_true, beq_iff_eq] at hok
            rcases hok.1 with h | h
            · exact isLoc_of_isPool h
            · rw [h]; exact hd
          by_cases hcp :
              (isCopy64 i.opn && i.srcs.map (fun o => renOp m o abi) == [.reg c]) = true
          · -- a self-copy: dropped
            rw [if_pos hcp] at hgo
            simp only [Bool.and_eq_true, beq_iff_eq] at hcp
            obtain ⟨hcopyi, hmap⟩ := hcp
            obtain ⟨o, hso, hro⟩ : ∃ o, i.srcs = [o] ∧ renOp m o abi = .reg c := by
              rcases hs : i.srcs with _ | ⟨o, _ | ⟨o2, t⟩⟩ <;> rw [hs] at hmap <;> simp at hmap
              exact ⟨o, rfl, hmap⟩
            have hτc : τ.lvm c = evalOperand σ o := by
              have := eval_renOp hR hreads hsrc (o := o) (by simp [hso])
              rw [hro] at this
              exact this
            rw [hso] at hv
            simp only [List.map_cons, List.map_nil] at hv
            rw [hcopy _ _ hcopyi] at hv
            simp only [Option.some.injEq] at hv
            subst hv
            refine ih (m.insert i.d c) cs acc out ((σ.setReg i.d (evalOperand σ o)).nextPc) σ' τ
              hwfs hgo ⟨hR.1, ?_, ?_⟩ hrun
            · intro x hx
              have hxd : x ≠ i.d := fun h => by rw [h, hd] at hx; exact absurd hx (by simp)
              simp [Lstate.setReg, hxd, hR.2.1 x hx]
            · intro n hn hnl
              rw [look_insert]
              by_cases hnd : n = i.d
              · subst hnd
                simp [hc, Lstate.setReg, hτc]
              · rw [if_neg (Ne.symm hnd)]
                have := hR.2.2 n (mem_liveBefore hn hnd) hnl
                refine ⟨this.1, ?_⟩
                simp [Lstate.setReg, hnd, this.2]
          · rw [if_neg hcp] at hgo
            by_cases hdead : (movClass i.opn && !la.contains i.d) = true
            · -- a dead move: dropped
              rw [if_pos hdead] at hgo
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdead
              refine ih m cs acc out ((σ.setReg i.d v).nextPc) σ' τ hwfs hgo ⟨hR.1, ?_, ?_⟩ hrun
              · intro x hx
                have hxd : x ≠ i.d := fun h => by rw [h, hd] at hx; exact absurd hx (by simp)
                simp [Lstate.setReg, hxd, hR.2.1 x hx]
              · intro n hn hnl
                have hnd : n ≠ i.d := fun h => by
                  rw [h] at hn
                  have := hdead.2
                  simp_all
                have := hR.2.2 n (mem_liveBefore hn hnd) hnl
                refine ⟨this.1, ?_⟩
                simp [Lstate.setReg, hnd, this.2]
            · rw [if_neg hdead] at hgo
              by_cases hnc : noClobber m la i.d c = true
              · -- a kept write at `c`
                rw [if_pos hnc] at hgo
                let i' : FI := ⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o abi)⟩
                have hstep' : stepWith sem i' τ = some ((τ.setReg c v).nextPc) := by
                  simp only [stepWith, i', hev, hv]
                have hR' : Rel (m.insert i.d c) la ((σ.setReg i.d v).nextPc)
                    ((τ.setReg c v).nextPc) abi := by
                  refine ⟨hR.1, ?_, ?_⟩
                  · intro x hx
                    have hxd : x ≠ i.d := fun h => by rw [h, hd] at hx; exact absurd hx (by simp)
                    have hxc : x ≠ c := fun h => by rw [h, hc] at hx; exact absurd hx (by simp)
                    simp [Lstate.setReg, hxd, hxc, hR.2.1 x hx]
                  · intro n hn hnl
                    rw [look_insert]
                    by_cases hnd : n = i.d
                    · subst hnd
                      simp [hc, Lstate.setReg]
                    · rw [if_neg (Ne.symm hnd)]
                      have := hR.2.2 n (mem_liveBefore hn hnd) hnl
                      have hne : look m n ≠ c := by
                        have h1 := List.all_eq_true.1 hnc n hn
                        simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
                        rcases h1 with h1 | h1
                        · exact absurd h1 hnd
                        · exact h1
                      refine ⟨this.1, ?_⟩
                      simp [Lstate.setReg, hnd, hne, this.2]
                obtain ⟨rest, τ', hout, hwr, hr', hfin⟩ :=
                  ih (m.insert i.d c) cs (i' :: acc) out _ σ' _ hwfs hgo hR' hrun
                refine ⟨i' :: rest, τ', by simp [hout], ?_, ?_, hfin⟩
                · intro j hj
                  rcases List.mem_cons.1 hj with rfl | hj
                  · exact wf_rename m i c hwfi
                  · exact hwr j hj
                · simp only [runWith, hstep']
                  exact hr'
              · rw [if_neg hnc] at hgo; exact absurd hgo (by simp)
        · rw [if_neg hok] at hgo; exact absurd hgo (by simp)
      · -- a write to a non-location name
        rw [if_neg hd] at hgo
        simp only [Bool.not_eq_true] at hd
        by_cases hsh : shapeOk m i i.d abi = true
        · rw [if_pos hsh] at hgo
          let i' : FI := ⟨i.ii, i.d, i.opn, i.srcs.map (fun o => renOp m o abi)⟩
          have hstep' : stepWith sem i' τ = some ((τ.setReg i.d v).nextPc) := by
            simp only [stepWith, i', hev, hv]
          have hR' : Rel m la ((σ.setReg i.d v).nextPc) ((τ.setReg i.d v).nextPc) abi := by
            refine ⟨hR.1, ?_, ?_⟩
            · intro x hx
              by_cases hxd : x = i.d
              · simp [Lstate.setReg, hxd]
              · simp [Lstate.setReg, hxd, hR.2.1 x hx]
            · intro n hn hnl
              have hnd : n ≠ i.d := fun h => by rw [h, hd] at hnl; exact absurd hnl (by simp)
              have := hR.2.2 n (mem_liveBefore hn hnd) hnl
              have hne : look m n ≠ i.d := fun h => by
                rw [h, hd] at this; exact absurd this.1 (by simp)
              refine ⟨this.1, ?_⟩
              simp [Lstate.setReg, hnd, hne, this.2]
          obtain ⟨rest, τ', hout, hwr, hr', hfin⟩ :=
            ih m cs (i' :: acc) out _ σ' _ hwfs hgo hR' hrun
          refine ⟨i' :: rest, τ', by simp [hout], ?_, ?_, hfin⟩
          · intro j hj
            rcases List.mem_cons.1 hj with rfl | hj
            · exact wf_rename m i i.d hwfi
            · exact hwr j hj
          · simp only [runWith, hstep']
            exact hr'
        · rw [if_neg hsh] at hgo; exact absurd hgo (by simp)
    · rw [if_neg hb] at hgo; exact absurd hgo (by simp)

/-! ## 7. The allocator

The allocator is untrusted: its decisions reach the output only through `goAcc`.
`buildWebs` splits every location into webs (a definition and its uses) in one
forward pass, ties the web a two-address instruction defines to the web of its
destination's previous value, and marks a web fixed at its own name when it is
live on entry, live out, an address register, or touched by an instruction of
fixed shape. `colorClasses` colours the tie classes in order of their start. -/

/-- A web: the definition of `name` at `start` and its uses up to `stop`. -/
structure Web where
  /-- The location the web belongs to in the source. -/
  name : String
  /-- The position of the definition (`0` for a value live on entry). -/
  start : Nat
  /-- The position of the last use. -/
  stop : Nat
  /-- The tie class. -/
  cls : Nat
  /-- The web keeps its own name. -/
  fixed : Bool
  /-- The web of the source of the 64-bit copy that defines this web. -/
  hint : Option Nat
  /-- The web a 64-bit copy of this web defines. -/
  sink : Option Nat := none
  deriving Inhabited

/-- The state of `buildWebs`. -/
structure AllocSt where
  /-- The webs, in order of creation. -/
  webs : Array Web := #[]
  /-- The current web of every location. -/
  curWeb : Std.HashMap String Nat := {}
  /-- The web each instruction defines. -/
  defWeb : Array (Option Nat) := #[]
  /-- The number of tie classes. -/
  nCls : Nat := 0
  deriving Inhabited

/-- Record a use of `x` at position `p`, creating a web live on entry when `x` has
    none. -/
def AllocSt.touch (st : AllocSt) (x : String) (p : Nat) (fix : Bool) : AllocSt :=
  match st.curWeb.get? x with
  | some wi =>
      let w := st.webs[wi]!
      { st with webs := st.webs.set! wi { w with stop := Nat.max w.stop p, fixed := w.fixed || fix } }
  | none =>
      { st with
        webs := st.webs.push ⟨x, 0, p, st.nCls, true, none, none⟩
        curWeb := st.curWeb.insert x st.webs.size
        nCls := st.nCls + 1 }

/-- The webs of an annotated run (positions from `1`). -/
def buildWebs (lend : List String) (ann : Array (FI × List String))
    (abi : IsaAbi := x86Abi) : AllocSt := Id.run do
  let mut st : AllocSt := {}
  for h : k in [0:ann.size] do
    let (i, la) := ann[k]
    let p := k + 1
    let sh := shapeOf i
    let fixAll := sh == .fixed
    let bs := i.bases abi
    for x in i.reads abi do
      st := st.touch x p (fixAll || bs.contains x)
    if isLoc i.d abi && !(movClass i.opn && !la.contains i.d) then
      let tied : Option Nat :=
        if sh == .tied then (st.curWeb.get? i.d).map (fun wi => st.webs[wi]!.cls) else none
      let hint : Option Nat :=
        if isCopy64 i.opn then
          match i.srcs with
          | [.reg s] => if isLoc s abi then st.curWeb.get? s else none
          | _ => none
        else none
      let cls := tied.getD st.nCls
      let nCls := if tied.isSome then st.nCls else st.nCls + 1
      let webs := match hint with
        | some hw => st.webs.modify hw (fun w => { w with sink := some st.webs.size })
        | none => st.webs
      st := { st with
        webs := webs.push ⟨i.d, p, p, cls, fixAll, hint, none⟩
        curWeb := st.curWeb.insert i.d st.webs.size
        nCls := nCls
        defWeb := st.defWeb.push (some st.webs.size) }
    else
      st := { st with defWeb := st.defWeb.push none }
  for x in lend do
    st := st.touch x (ann.size + 1) true
  return st

/-- The first index `≥ j` of a start-sorted list of disjoint intervals whose end is
    past `st`. -/
def advance (iv : Array (Nat × Nat)) (st : Nat) (j : Nat) : Nat :=
  if h : j < iv.size then
    if iv[j].2 ≤ st then advance iv st (j + 1) else j
  else j
termination_by iv.size - j

/-- The pool registers in allocation order: `abi.allocPool`. -/
def poolOrder (abi : IsaAbi := x86Abi) : List String := abi.allocPool

/-- The x86 pool in allocation order: the thirteen registers of `gpRegNames`. -/
theorem poolOrder_x86 :
    poolOrder =
      ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "R8", "R9", "R10", "R11", "R12",
        "R13"] := rfl

/-- Colour the tie classes: a fixed class keeps its name; the other classes, in order
    of their start, take the first free colour among the colour of the source of the
    copy that starts them, the colour of a fixed class a copy at their end defines,
    their own name and the pool registers (the pool first for a frame cell when
    `promote`).
    `none` when a class finds no free colour. -/
def colorClasses (st : AllocSt) (promote : Bool) (abi : IsaAbi := x86Abi) :
    Option (Array String) := Id.run do
  let n := st.nCls
  let mut cName : Array String := Array.replicate n ""
  let mut cStart : Array Nat := Array.replicate n 0
  let mut cStop : Array Nat := Array.replicate n 0
  let mut cFixed : Array Bool := Array.replicate n false
  let mut cFirst : Array Nat := Array.replicate n 0
  let mut cSink : Array (Option Nat) := Array.replicate n none
  let mut seen : Array Bool := Array.replicate n false
  for h : wi in [0:st.webs.size] do
    let w := st.webs[wi]
    let c := w.cls
    if w.sink.isSome && w.stop ≥ cStop[c]! then cSink := cSink.set! c w.sink
    if seen[c]! then
      cStop := cStop.set! c (Nat.max cStop[c]! w.stop)
      cFixed := cFixed.set! c (cFixed[c]! || w.fixed)
    else
      seen := seen.set! c true
      cName := cName.set! c w.name
      cStart := cStart.set! c w.start
      cStop := cStop.set! c w.stop
      cFixed := cFixed.set! c w.fixed
      cFirst := cFirst.set! c wi
  let mut fixedIv : Std.HashMap String (Array (Nat × Nat)) := {}
  for c in [0:n] do
    if cFixed[c]! then
      fixedIv := fixedIv.insert cName[c]! ((fixedIv.getD cName[c]! #[]).push (cStart[c]!, cStop[c]!))
  let mut color : Array String := cName
  let mut lastEnd : Std.HashMap String Nat := {}
  let mut ptr : Std.HashMap String Nat := {}
  let mut ok := true
  for c in [0:n] do
    if ok && !cFixed[c]! then
      let s0 := cStart[c]!
      let en := cStop[c]!
      let nm := cName[c]!
      let hintCol : List String :=
        match st.webs[cFirst[c]!]!.hint with
        | some hw =>
            let hc := st.webs[hw]!.cls
            if cStop[hc]! ≤ s0 then [color[hc]!] else []
        | none => []
      let sinkCol : List String :=
        match cSink[c]! with
        | some sw =>
            let sc := st.webs[sw]!.cls
            if cFixed[sc]! && cStart[sc]! ≥ en then [cName[sc]!] else []
        | none => []
      let rest : List String :=
        if isFrame nm then (if promote then poolOrder abi ++ [nm] else [nm])
        else nm :: poolOrder abi
      let mut chosen : Option String := none
      for col in hintCol ++ sinkCol ++ rest do
        if chosen.isNone && okLoc nm col abi && (promote || !isFrame nm || col == nm) then
          let iv := fixedIv.getD col #[]
          let j := advance iv s0 (ptr.getD col 0)
          ptr := ptr.insert col j
          let fixedFree := if h : j < iv.size then en ≤ iv[j].1 else true
          if lastEnd.getD col 0 ≤ s0 && fixedFree then chosen := some col
      match chosen with
      | some col =>
          color := color.set! c col
          lastEnd := lastEnd.insert col (Nat.max (lastEnd.getD col 0) en)
      | none => ok := false
  return if ok then some color else none

/-- The decisions of a colouring: the colour of the web each instruction defines, the
    destination itself where it defines none. -/
def decisionsOf (st : AllocSt) (color : Array String) (ann : Array (FI × List String)) :
    List String :=
  (List.range ann.size).map (fun k =>
    match st.defWeb[k]! with
    | some wi => color[st.webs[wi]!.cls]!
    | none => ann[k]!.1.d)

/-! ## 8. The pass -/

/-- The first decision list that passes the check, materialized; the run itself when
    none does. -/
def reallocWith (lend : List String) (is : List FI) (cands : List (List String))
    (abi : IsaAbi := x86Abi) : List FI :=
  match cands.findSome? (fun cs => goAcc lend {} (annotate lend is abi).1 cs [] abi) with
  | some out => out
  | none => is

theorem reallocWith_sound {w : Nat} {abi : IsaAbi}
    (sem : String → List (BitVec w) → Option (BitVec w))
    (hcopy : ∀ (opn : String) (a : BitVec w), isCopy64 opn = true → sem opn [a] = some a)
    (lend : List String) (is : List FI) (cands : List (List String))
    (hwf : ∀ i ∈ is, i.wf = true) (σ σ' : Lstate w) (h : runWith sem is σ = some σ') :
    (∀ j ∈ reallocWith lend is cands abi, j.wf = true) ∧
      ∃ τ', runWith sem (reallocWith lend is cands abi) σ = some τ' ∧
        Final lend σ' τ' abi := by
  unfold reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨rest, τ', hout, hwr, hr, hfin⟩ :=
      goAcc_sound sem hcopy lend is {} cs [] out σ σ' σ hwf hcs (Rel.empty _ σ) h
    simp only [List.reverse_nil, List.nil_append] at hout
    subst hout
    exact ⟨hwr, τ', hr, hfin⟩
  · exact ⟨hwf, σ', h, rfl, fun _ _ => rfl⟩

/-- The candidate decisions for one run with live-out set `lend`: the colourings with
    and without frame-cell promotion, then the identity decisions. -/
def runCands (lend : List String) (is : List FI) (abi : IsaAbi := x86Abi) :
    List (List String) :=
  let ann := (annotate lend is abi).1.toArray
  let st := buildWebs lend ann abi
  let dec (promote : Bool) : List String :=
    match colorClasses st promote abi with
    | some col => decisionsOf st col ann
    | none => []
  [dec true, dec false, is.map FI.d]

/-- The pass on one run with live-out set `lend`. -/
def reallocRun (lend : List String) (is : List FI) (abi : IsaAbi := x86Abi) : List FI :=
  reallocWith lend is (runCands lend is abi) abi

/-- **The pass on one run is sound for every interpretation** that reads the 64-bit
    copies as the identity, at every register file `abi`. -/
theorem reallocRun_sound {w : Nat} {abi : IsaAbi}
    (sem : String → List (BitVec w) → Option (BitVec w))
    (hcopy : ∀ (opn : String) (a : BitVec w), isCopy64 opn = true → sem opn [a] = some a)
    (lend : List String) (is : List FI) (hwf : ∀ i ∈ is, i.wf = true) (σ σ' : Lstate w)
    (h : runWith sem is σ = some σ') :
    ∃ τ', runWith sem (reallocRun lend is abi) σ = some τ' ∧ Final lend σ' τ' abi :=
  (reallocWith_sound sem hcopy lend is _ hwf σ σ' h).2

/-- **The pass on one run under `lsemStraight`**, at every register file `abi`. -/
theorem reallocRun_lsemStraight {w : Nat} {abi : IsaAbi} (lend : List String) (is : List FI)
    (hwf : ∀ i ∈ is, i.wf = true) (σ σ' : Lstate w)
    (h : lsemStraight (is.map FI.toR) σ = some σ') :
    ∃ τ', lsemStraight ((reallocRun lend is abi).map FI.toR) σ = some τ' ∧
      Final lend σ' τ' abi := by
  rw [lsemStraight_map_toR is hwf] at h
  obtain ⟨hwr, τ', hr, hfin⟩ :=
    reallocWith_sound (abi := abi) semL (fun opn a hc => semL_copy opn a hc) lend is
      (runCands lend is abi) hwf σ σ' h
  exact ⟨τ', by rw [reallocRun, lsemStraight_map_toR _ hwr]; exact hr, hfin⟩

/-- A body split into runs of fragment instructions and the instructions between. -/
inductive Piece where
  /-- A maximal run of fragment instructions. -/
  | run (is : List FI)
  /-- An instruction outside the fragment. -/
  | bar (li : Linstr)

/-- Split a body into pieces, the fragment taken over the alphabet `recog`. -/
def pieces (body : Lcmd) (recog : String → Bool := isRecognizedOpn) : List Piece :=
  body.foldr (fun li acc =>
    match fragOf? li recog with
    | some i =>
        match acc with
        | Piece.run is :: rest => Piece.run (i :: is) :: rest
        | _ => Piece.run [i] :: acc
    | none => Piece.bar li :: acc) []

/-- The frame cells an operand names. -/
def opFrames : LOperand → List String
  | .reg n => if isFrame n then [n] else []
  | .arrIdx b x _ => [b, x].filter isFrame
  | .arr b _ => if isFrame b then [b] else []
  | .imm _ => []

/-- The frame cells an instruction names, including the operand of a conditional
    branch (a branch that reads a frame cell keeps that cell live). -/
def instrFrames : LinstrR → List String
  | .Lopn dsts _ srcs => dsts.flatMap opFrames ++ srcs.flatMap opFrames
  | .Lcond c _ => opFrames c
  | _ => []

/-- The frame cells a piece names. -/
def Piece.frames : Piece → List String
  | .run is => is.flatMap (fun i => instrFrames i.toR)
  | .bar li => instrFrames li.li_i

/-- The registers live at a return: the callee-saved registers `abi.calleeSaved`, the
    return registers `abi.retRegs`, and the function's result registers `res`. -/
def retLive (res : List String) (abi : IsaAbi := x86Abi) : List String :=
  abi.calleeSaved ++ abi.retRegs ++ res.filter (fun x => isLoc x abi)

/-- At `x86Abi` the registers live at a return are the SysV callee-saved registers, the
    return registers `RAX` and `RDX`, and the result registers. -/
theorem retLive_x86 (res : List String) :
    retLive res =
      ["RBX", "RBP", "R12", "R13", "R14", "R15", "RAX", "RDX"] ++ res.filter (isLoc ·) :=
  rfl

/-- The frame cells live out of every run of a body with a label: every frame
    cell the body names. A jump to a label can reach a run that precedes the jump,
    so a cell the body names anywhere may be read after any run; a body without a
    label runs in program order and starts from no cell. -/
def labelLiveFrames (body : Lcmd) : Std.HashSet String :=
  if body.any (fun li => match li.li_i with | .Llabel _ _ => true | _ => false) then
    ({} : Std.HashSet String).insertMany (body.flatMap (fun li => instrFrames li.li_i))
  else {}

/-- The pass on one body with result registers `res`: every run is re-allocated
    with live-out set the frame cells named after it (every frame cell of the body
    when it has a label, `labelLiveFrames`) together with `retLive res abi` when a
    return follows the run and the general-purpose registers `gpRegs abi` otherwise
    (at `x86Abi`, the fifteen of `physGPs`); every other instruction is kept. The fragment
    is taken over the alphabet `recog`. -/
def reallocBody (res : List String) (body : Lcmd) (abi : IsaAbi := x86Abi)
    (recog : String → Bool := isRecognizedOpn) : Lcmd :=
  let r := (pieces body recog).foldr (fun p (acc : Lcmd × Std.HashSet String) =>
    let out : Lcmd :=
      match p with
      | .run is =>
          let regs := match acc.1 with
            | ⟨_, .Lret⟩ :: _ => retLive res abi
            | _ => gpRegs abi
          (reallocRun (regs ++ acc.2.toList) is abi).map FI.toL ++ acc.1
      | .bar li => li :: acc.1
    (out, acc.2.insertMany p.frames)) ([], labelLiveFrames body)
  r.1

/-- The pass on every function body of a program, at the register file `abi` and the
    fragment alphabet `recog`. The defaults are the x86 register file `x86Abi` and the x86
    alphabet `isRecognizedOpn`; an instruction set `I : IsaData` is passed as `I.toIsaAbi`
    and `isaRecognized I`. -/
def reallocLprog (p : Lprog) (abi : IsaAbi := x86Abi)
    (recog : String → Bool := isRecognizedOpn) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun f =>
      (f.1, { f.2 with lfd_body := reallocBody f.2.lfd_res f.2.lfd_body abi recog })) }

/-- The pass at an instruction set `I`: the register file of `I` and the alphabet
    `isaRecognized I`, which excludes every mnemonic `I.implicitReads` gives a register. -/
def reallocLprogIsa (I : IsaData) (p : Lprog) : Lprog :=
  reallocLprog p I.toIsaAbi (isaRecognized I)

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
