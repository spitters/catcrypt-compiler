/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.String.TakeDrop
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem

/-!
# `WellFormedX86`: a decidable ISA-legality invariant for the owned x86 backend

The owned x86 backend proves two things about each emitted leaf: that the
`Com` denotation equals the kernel spec (semantics), and that `encode`/`decode`
round-trips on each instruction (bytes — *for instructions that are legal*).
Neither proof says the lowering emits **only legal, encodable** x86. The
legality gap was real: three codegen bugs reached `as` (the GNU assembler) at
assemble time on the whole-state ChaCha owned emit, where `as` — not any Lean
proof — was the trusted legality oracle:

1. a `mem → mem` `movq` on the **load** side (an illegal two-memory `mov`);
2. a `mem → mem` `movq` on the **store** side (the symmetric illegal `mov`);
3. an **unresolved spill slot** rendered as the sentinel `%<UNKNOWN:k.5>` — an
   operand the register allocator never assigned, which `as` rejects.

This module closes that gap with `WellFormedX86`: a **decidable** invariant
(`wfLinstr`/`wfLcmd`/`wfLprog`) over the `LinstrR`/`Lprog` mirror that would have
**rejected all three at lowering time**, before any text reached `as`. It is the
structural fix that demotes `as` from a trusted legality oracle to a redundant
check.

## The three bug classes, as decidable predicates

* **(a) at most one memory operand** (`atMostOneMem`): no `Lopn` carries two
  memory (spill / array / SIB) operands. Catches bug classes 1 and 2 — the
  `mem → mem` `movq` on either side. Strictly stronger than the existing
  `LinstrR.legalMemForm`, which only inspects the first destination and the
  *last* source position; `atMostOneMem` counts memory operands across the
  **whole** dst++src list, so no second memory operand can hide in a longer
  operand list (ADX three-source, MULX two-dest, three-operand store).

* **(b) every operand resolved** (`opResolved`): every register-named operand is
  a *concrete* x86 location — a real physical GP register, a parseable spill slot
  `k.<n>`, an ABI save slot `qsave.<reg>`, or a base+offset memory reference
  `mem.<base>.<off>`. There is **no** unresolved placeholder. Catches bug class
  3: the `%<UNKNOWN:k.5>` sentinel is exactly what the printer emits when an
  operand name is *none* of these resolved forms.

* **(c) widths consistent** (`widthConsistent`): the operand width is fixed by
  the mnemonic tag (the printer sizes every operand of an op uniformly), so there
  is no per-operand width leg to mismatch. Included so the invariant is the
  *full* legality property `as` needs, not a subset (vacuously true for the
  producer).

## Soundness

`wfLinstr_sound` proves that `wfLinstr i = true` entails the two properties `as`
needs — `atMostOneMemOperand i ∧ allOperandsResolved i`.

## A finding surfaced by this invariant

The legalization helpers route on `LOperand.isSpill`, which checks **only** the
`k.` (spill) prefix. The printer, however, treats `qsave.` and `mem.` names as
memory too (`resolveName`). So the helpers are WF-preserving **exactly when** an
operand's memory status coincides with its spill status (`isMemX86 = isSpill`) —
which is the producer's actual invariant (the two-address bodies only ever place
a *spill* on a memory side; `qsave.`/`mem.` appear only inside MOVs the producer
already shapes). The lemmas below carry this coincidence as an explicit
hypothesis `memCoincidesSpill`, making the producer-side assumption visible
rather than implicit — and flagging that a `mem.`/`qsave.` destination would
bypass the helper's routing.

## What is proved vs. checker-gated

* **Proved**: `wfLinstr` decidable; `wfLinstr_sound`; the legalization helpers
  `legalizeMemLoad`/`legalizeMemStore`/`legalizeMov`/`legalizeBinop` produce WF
  output for resolved inputs (`legalize*_wf`) — the direct refutation of bug
  classes 1 and 2. The SIB-base legalization `legalizeSibElem` produces WF output
  on a **spilled-base SIB** element (`legalizeSibElem_prelude_wf`,
  `legalizeSibElem_fixed_resolved`), and the full memory load/store legalizers
  carry that through end-to-end (`legalizeMemLoad_sib_wf`,
  `legalizeMemStore_sib_wf`) — the direct refutation of bug class 3 on the
  **address** (the third remaining ChaCha error
  `movq %r15, (%<UNKNOWN:k.5>, %rax, 8)`).
* **Proved (lowering→WF preservation, §6d–6g, §7)**: every injected lowering
  pass produces WF output on resolved, spill-coinciding operands —
  `lowerTwoAddr_wf`, `lowerTwoAddrShiftImm_wf`, `lowerNativeShiftRotate_wf`,
  `materializeWideImm_wf` (composing §6's `legalize*_wf`). `remapOperand`'s
  output is always resolved and spill-coinciding (`remap_reg_*`, via the
  `physRegName_*` facts of §6d). The inline ABI argument-load and output-store
  legs are WF (`loadLeg_wf`, `storeLeg_wf`), as are the ABI prologue
  (`buildPrologue_wf`) and the callee-save restore epilogue
  (`calleeSaveRestoreEpilogue_wf`). The `wfLcmd`-over-`flatMap`/`++`/`dropLast`
  recursion that lifts a per-instruction obligation to a whole body is proved
  (`wfLcmd_flatMap`, `wfLcmd_append`, `wfLcmd_dropLast`), and the whole-program
  ABI wrapper preservation is assembled (`abiWrap_wf`, `toLprogPhysAbi_wf`):
  given the body's per-instruction WF, the full `Com.toLprogPhysAbi` export is
  `wfLprog`.
* **Proved (rendered names)**: the decimal round trip `natOfDigitsSep?_toString`, so a
  rendered spill name `"k." ++ toString k` is a parseable spill (`spill_name_round_trip :
  SpillNameWF`) and `mem.R14.<off>` resolves (`mem_name_round_trip : MemNameWF`).
* **Hypothesis of `toLprogPhysAbi_wf`**: the verified two-address body's direct-emit
  no-two-spill obligation (the post-RA Phase-2 content, the same territory as
  `LprogJasminWellFormed`'s residuals), carried as `hbws : wfLcmd bodyWithInlineStores`.
  `toLprogPhysAbi_wf_goal` names the unconditional obligation.
* **Over an instruction set** (§1b): `opResolvedI I` reads the register file, the save
  slots and the index scales from `I : IsaData`; `opResolvedI_x86` identifies
  `opResolvedI x86Data` with `opResolved`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData)

/-! ## 1. Resolvable physical operands (bug class 3: the `%<UNKNOWN>` sentinel) -/

/-- The 16 x86-64 GP register names the owned printer's `gpReg64` map resolves
    (`RAX … R15`, including `RSP`/`RBP` and the two reserved scratches
    `R14`/`R15`). A bare register name outside this set is what the printer
    renders as the `%<UNKNOWN:…>` sentinel `as` rejects. Superset of the
    allocatable `gpRegNames` (which excludes `RSP`/`R14`/`R15`). -/
def x86PhysRegNames : List String :=
  ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP",
   "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"]

/-- `String.isPrefixOf` is `JasminLprogExport.hasPrefix` with the arguments
    swapped: both test `p.toList <+: s.toList`. The recognizers below are stated
    over `hasPrefix`, which `decide` computes through inside a module. -/
theorem isPrefixOf_eq_hasPrefix (p s : String) :
    p.isPrefixOf s = JasminLprogExport.hasPrefix s p := by
  rw [JasminLprogExport.hasPrefix, String.isPrefixOf, Bool.eq_iff_iff,
    String.startsWith_string_iff, List.isPrefixOf_iff_prefix]

/-- `digitSepOk cs lastDigit` holds iff `cs` is a run of decimal digits and `_`
    separators in which every `_` is preceded by a digit (`lastDigit` stands for
    the character before `cs`) and the run ends in a digit. This is the
    acceptance rule of `String.isNat`. -/
def digitSepOk : List Char → Bool → Bool
  | [], lastDigit => lastDigit
  | c :: rest, lastDigit =>
      if c = '_' then lastDigit && digitSepOk rest false
      else ('0' ≤ c && c ≤ '9') && digitSepOk rest true

/-- The list form of `String.toNat?`: the decimal value of `cs` when
    `digitSepOk cs false`, with `_` separators dropped, and `none` otherwise.
    `String.toNat?` does not reduce inside a module; this parse does. -/
def natOfDigitsSep? (cs : List Char) : Option Nat :=
  if digitSepOk cs false then JasminLprogExport.natOfDigits? (cs.filter (fun c => c != '_'))
  else none

/-- A decimal digit is not the separator `_` and lies between `'0'` and `'9'`. -/
theorem digit_sep_bounds {c : Char} (h : c.isDigit = true) :
    c ≠ '_' ∧ ('0' ≤ c && c ≤ '9') = true := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun e => ?_, ?_⟩
  · subst e; revert h; decide
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def]; exact ⟨h.1, h.2⟩

/-- A non-empty run of decimal digits passes `digitSepOk` from either state. -/
theorem digitSepOk_cons_digits (c : Char) (rest : List Char)
    (hd : ∀ x ∈ c :: rest, x.isDigit = true) (b : Bool) :
    digitSepOk (c :: rest) b = true := by
  induction rest generalizing c b with
  | nil =>
      obtain ⟨hne, hb⟩ := digit_sep_bounds (hd c List.mem_cons_self)
      simp [digitSepOk, hne, hb]
  | cons d rest ih =>
      obtain ⟨hne, hb⟩ := digit_sep_bounds (hd c List.mem_cons_self)
      rw [digitSepOk, if_neg hne, hb, Bool.true_and]
      exact ih d (fun x hx => hd x (List.mem_cons_of_mem _ hx)) true

/-- **The decimal round trip of `natOfDigitsSep?`**: the character list of
    `toString k` parses to `k`. -/
theorem natOfDigitsSep?_toString (k : Nat) :
    natOfDigitsSep? (toString k).toList = some k := by
  have hl : (toString k).toList = Nat.toDigits 10 k := by
    show (String.ofList (Nat.toDigits 10 k)).toList = _
    rw [String.toList_ofList]
  have hd := JasminImmShiftMnem.toDigits_isDigit k
  have hok : digitSepOk (toString k).toList false = true := by
    rw [hl]
    obtain ⟨c, rest, hcr⟩ := List.exists_cons_of_ne_nil (JasminImmShiftMnem.toDigits_ne_nil k)
    rw [hcr] at hd ⊢
    exact digitSepOk_cons_digits c rest hd false
  have hf : (toString k).toList.filter (fun c => c != '_') = (toString k).toList := by
    rw [List.filter_eq_self]
    intro c hc
    rw [hl] at hc
    simp [(digit_sep_bounds (hd c hc)).1]
  unfold natOfDigitsSep?
  rw [if_pos hok, hf]
  exact JasminImmShiftMnem.natOfDigits?_toString k

/-- A spill-slot name `k.<n>` is resolved iff `<n>` parses as a natural number
    (`natOfDigitsSep?`, the list form of `String.toNat?`). -/
def spillNameResolved (n : String) : Bool :=
  JasminLprogExport.hasPrefix n "k." && (natOfDigitsSep? (n.toList.drop 2)).isSome

/-- The twelve registers with a frame save slot: the domain of the printer's
    `LprogAsmPrinter.qsaveSlot` map. -/
def x86SaveRegNames : List String :=
  ["RDI", "RSI", "RBX", "RBP", "R12", "R13", "R14", "R15", "RDX", "RCX", "R8", "R9"]

/-- An ABI save-slot name `qsave.<reg>` is resolved iff `<reg>` is one of the
    save registers the printer's `qsaveSlot` map knows (`x86SaveRegNames`). -/
def qsaveNameResolved (n : String) : Bool :=
  JasminLprogExport.hasPrefix n "qsave." &&
    (n.toList.drop 6 ∈ x86SaveRegNames.map String.toList)

/-- A base+offset memory name `mem.<base>.<off>` is resolved iff the text after
    `mem.` is `<base>.<off>` with `base` a resolvable physical register (which
    contains no `.`) and `off` a natural number (so it contains no `.` either):
    the `[base, off]` split of the printer's `mem.` arm. -/
def memNameResolved (n : String) : Bool :=
  JasminLprogExport.hasPrefix n "mem." &&
    (match (n.toList.drop 4).span (· ≠ '.') with
     | (base, '.' :: off) =>
         (base ∈ x86PhysRegNames.map String.toList) && (natOfDigitsSep? off).isSome
     | _ => false)

/-- A register *name* is **x86-resolved** iff it is a real physical register, a
    parseable spill slot, a known ABI save slot, or a base+offset memory
    reference — exactly the four shapes the printer's `resolveName` maps to a
    concrete AT&T operand. Any other name prints a `%<UNKNOWN:…>`/`<BAD…:…>`
    sentinel `as` rejects. -/
def regNameResolved (n : String) : Bool :=
  (n ∈ x86PhysRegNames) || spillNameResolved n || qsaveNameResolved n ||
    memNameResolved n

/-- An `LOperand` is **x86-resolved** iff it denotes a concrete x86 operand:
    a `.reg n` with a resolved name; an `.imm v`; or an `.arrIdx base idx scale`
    whose base/index are real physical registers and whose scale is a legal x86
    SIB scale (`1/2/4/8`). A compile-time `.arr` is **not** resolved (the printer
    renders it as the `<ARR:…>` sentinel; the scalar owned path never emits it). -/
def opResolved : LOperand → Bool
  | .reg n => regNameResolved n
  | .imm _ => true
  | .arr _ _ => false
  | .arrIdx base idx scale =>
      (base ∈ x86PhysRegNames) && (idx ∈ x86PhysRegNames) &&
        (scale ∈ ([1, 2, 4, 8] : List Nat))

/-! ## 1b. Resolved operands over the data of an instruction set

`opResolvedI I` is `opResolved` with the register file, the save slots and the index
scales read from the instruction-set data `I`; `opResolvedI_x86` identifies the two at
`x86Data`. -/

/-- The physical register names of an instruction set: the allocation pool, the reserved
    scratch registers and the stack pointer. -/
def physRegNamesI (I : IsaData) : List String := I.allocPool ++ I.scratch ++ [I.sp]

/-- A save-slot name `qsave.<reg>` is resolved over `I` iff `<reg>` has a frame save slot
    (`I.saveSlot`). -/
def qsaveNameResolvedI (I : IsaData) (n : String) : Bool :=
  JasminLprogExport.hasPrefix n "qsave." &&
    (I.saveSlot (String.ofList (n.toList.drop 6))).isSome

/-- A base+offset memory name `mem.<base>.<off>` is resolved over `I` iff `base` is a
    physical register of `I` and `off` a natural number. -/
def memNameResolvedI (I : IsaData) (n : String) : Bool :=
  JasminLprogExport.hasPrefix n "mem." &&
    (match (n.toList.drop 4).span (· ≠ '.') with
     | (base, '.' :: off) =>
         (base ∈ (physRegNamesI I).map String.toList) && (natOfDigitsSep? off).isSome
     | _ => false)

/-- A register name is resolved over `I` iff it is a physical register of `I`, a
    parseable spill slot, a save slot of `I` or a base+offset memory name over `I`. -/
def regNameResolvedI (I : IsaData) (n : String) : Bool :=
  (n ∈ physRegNamesI I) || spillNameResolved n || qsaveNameResolvedI I n ||
    memNameResolvedI I n

/-- **An operand resolved over the instruction set `I`**: a register with a name resolved
    over `I`, an immediate, or a register-indexed address whose base and index are
    physical registers of `I` and whose scale is in `I.indexScales`. -/
def opResolvedI (I : IsaData) : LOperand → Bool
  | .reg n => regNameResolvedI I n
  | .imm _ => true
  | .arr _ _ => false
  | .arrIdx base idx scale =>
      (base ∈ physRegNamesI I) && (idx ∈ physRegNamesI I) && (scale ∈ I.indexScales)

/-- The physical registers of `x86Data` are those of `x86PhysRegNames`. -/
theorem mem_physRegNamesI_x86 (n : String) :
    n ∈ physRegNamesI TwoAddrLegalize.x86Data ↔ n ∈ x86PhysRegNames := by
  simp only [physRegNamesI, x86PhysRegNames, JasminLprogExport.gpRegNames,
    JasminLprogExport.reloadScratch, JasminLprogExport.reloadScratch2,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- The save slots of `x86Data` are those of `x86SaveRegNames`. -/
theorem qsaveSlot_isSome_iff (L : List Char) :
    (LprogAsmPrinter.qsaveSlot (String.ofList L)).isSome = true ↔
      L ∈ x86SaveRegNames.map String.toList := by
  have hof : ∀ s : String, String.ofList L = s ↔ L = s.toList := fun s =>
    ⟨fun h => by rw [← h, String.toList_ofList], fun h => by rw [h, String.ofList_toList]⟩
  unfold LprogAsmPrinter.qsaveSlot
  split <;> rename_i h <;>
    first
    | (rw [hof] at h; subst h; decide)
    | simp_all [x86SaveRegNames]

/-- **`opResolved` is the x86 instance of `opResolvedI`.** -/
theorem opResolvedI_x86 : opResolvedI TwoAddrLegalize.x86Data = opResolved := by
  have h1 : ∀ n, decide (n ∈ physRegNamesI TwoAddrLegalize.x86Data) =
      decide (n ∈ x86PhysRegNames) := fun n => decide_eq_decide.mpr (mem_physRegNamesI_x86 n)
  have h2 : ∀ L : List Char,
      decide (L ∈ (physRegNamesI TwoAddrLegalize.x86Data).map String.toList) =
        decide (L ∈ x86PhysRegNames.map String.toList) := fun L =>
    decide_eq_decide.mpr (by simp only [List.mem_map, mem_physRegNamesI_x86])
  have h3 : ∀ L : List Char,
      (TwoAddrLegalize.x86Data.saveSlot (String.ofList L)).isSome =
        decide (L ∈ x86SaveRegNames.map String.toList) := fun L => by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact qsaveSlot_isSome_iff L
  funext o
  cases o <;>
    simp only [opResolvedI, opResolved, regNameResolvedI, regNameResolved,
      qsaveNameResolvedI, qsaveNameResolved, memNameResolvedI, memNameResolved, h1, h2, h3]

/-! ## 2. Memory-operand class (bug classes 1, 2: `mem → mem` mov) -/

/-- Is the operand a memory (non-register) operand from the x86 operand-class
    view? A spill `k.<n>`, ABI save `qsave.<reg>`, base+offset `mem.<base>.<off>`,
    compile-time array `.arr`, or register-indexed SIB `.arrIdx`. An immediate or
    a bare physical register is **not** memory. Broader than `LOperand.isSpill`
    (which only sees `k.`): the printer treats `qsave.`/`mem.` as memory too. -/
def isMemX86 : LOperand → Bool
  | .reg n => "k.".isPrefixOf n || "qsave.".isPrefixOf n || "mem.".isPrefixOf n
  | .imm _ => false
  | .arr _ _ => true
  | .arrIdx _ _ _ => true

/-- The number of memory operands among a list. -/
def countMem (ops : List LOperand) : Nat :=
  (ops.filter (fun o => isMemX86 o)).length

/-- **(a) at most one memory operand.** Across the whole `dst ++ src` list of an
    `Lopn`, at most one is a memory operand — the x86 rule for the `mov`/binop
    encodings (no `mov mem, mem`, no two-memory ALU form). -/
def atMostOneMem : LinstrR → Bool
  | .Lopn dsts _ srcs => countMem (dsts ++ srcs) ≤ 1
  | _ => true

/-! ## 3. Width consistency -/

/-- True iff the mnemonic carries a 64-bit width tag (`:64` or `MOVQ`). -/
def isU64Mnem (opn : String) : Bool :=
  hasSuffix opn ":64" || opn = "MOVQ"

/-- **(c) width consistency.** The operand width is fixed by the mnemonic tag
    (the printer sizes all operands of an op uniformly off `mnemWidth`), so there
    is no per-operand width leg to mismatch. Conservatively `true`; included so
    the invariant is the complete legality property `as` needs. -/
def widthConsistent : LinstrR → Bool
  | _ => true

/-! ## 4. The decidable `WellFormedX86` invariant -/

/-- All operands of an `LinstrR`. -/
def instrOperands : LinstrR → List LOperand
  | .Lopn dsts _ srcs => dsts ++ srcs
  | .Lcond c _ => [c]
  | .Ligoto t => [t]
  | _ => []

/-- **The decidable per-instruction well-formedness checker.** An `LinstrR` is
    WF iff every operand is x86-resolved (bug class 3), it carries at most one
    memory operand (bug classes 1, 2), and its widths are consistent. The
    predicate that would have rejected all three ChaCha codegen bugs *at lowering
    time*. -/
def wfLinstr (i : LinstrR) : Bool :=
  (instrOperands i).all (fun o => opResolved o) &&
    atMostOneMem i &&
    widthConsistent i

/-- Lift to a whole `Lcmd` body: every instruction is WF. -/
def wfLcmd (c : Lcmd) : Bool :=
  c.all (fun i => wfLinstr i.li_i)

/-- Lift to a whole `Lfundef`: its body is WF. -/
def wfLfundef (fd : Lfundef) : Bool :=
  wfLcmd fd.lfd_body

/-- Lift to a whole `Lprog`: every function's body is WF. The **post-lowering
    gate** the orchestrator runs. -/
def wfLprog (p : Lprog) : Bool :=
  p.lp_funcs.all (fun e => wfLfundef e.2)

/-! ## 5. Soundness: WF entails the two properties `as` needs -/

/-- `Prop`-level statement of bug class 3: every operand is resolved. -/
def allOperandsResolved (i : LinstrR) : Prop :=
  ∀ o ∈ instrOperands i, opResolved o = true

/-- `Prop`-level statement of bug classes 1, 2: at most one memory operand. -/
def atMostOneMemOperand (i : LinstrR) : Prop :=
  atMostOneMem i = true

/-- **Soundness.** A WF instruction satisfies the two assemble-legality
    properties `as` needs: every operand is resolved, and at most one is a memory
    operand — precisely the conjunction whose failure produced the three ChaCha
    bugs. -/
theorem wfLinstr_sound (i : LinstrR) (h : wfLinstr i = true) :
    atMostOneMemOperand i ∧ allOperandsResolved i := by
  unfold wfLinstr at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hres, hmem⟩, _hw⟩ := h
  refine ⟨hmem, ?_⟩
  intro o ho
  exact (List.all_eq_true.mp hres) o ho

/-- The checker is decidable as `= true`. -/
example (i : LinstrR) : Decidable (wfLinstr i = true) := inferInstance
example (p : Lprog) : Decidable (wfLprog p = true) := inferInstance

/-! ## 6. The legalization helpers produce WF output (bug classes 1, 2)

The helpers break a two-memory instruction into a sequence routed through the
reserved scratch `R15` (`reloadScratch`) / `R14` (`reloadScratch2`). We prove
their output is WF given resolved inputs whose memory status coincides with their
spill status (`memCoincidesSpill` — the producer's invariant; see the finding in
the header). The scratches are real registers, so each emitted `Lopn` carries at
most one memory operand. -/

/-- The producer invariant the legalization helpers rely on: an operand is a
    (broad) memory operand iff it is a (narrow) spill slot. True of every operand
    the two-address bodies feed the helpers — `qsave.`/`mem.` names appear only
    inside MOVs the producer shapes directly, never as a helper input. -/
def memCoincidesSpill (o : LOperand) : Prop := isMemX86 o = LOperand.isSpill o

/-- `R15` (primary reload scratch) is a resolved physical register, and a
    `.reg R15` is not a memory operand. -/
theorem reloadScratch_ok :
    opResolved (LOperand.reg reloadScratch) = true ∧
    isMemX86 (LOperand.reg reloadScratch) = false := by
  simp only [isMemX86, isPrefixOf_eq_hasPrefix]; decide

/-- `R14` (secondary reload scratch) is a resolved physical register, and a
    `.reg R14` is not a memory operand. -/
theorem reloadScratch2_ok :
    opResolved (LOperand.reg reloadScratch2) = true ∧
    isMemX86 (LOperand.reg reloadScratch2) = false := by
  simp only [isMemX86, isPrefixOf_eq_hasPrefix]; decide

/-- A two-operand `mov`/load `[d] op [s]` is WF when `d`, `s` are resolved and at
    most one is a memory operand. The base case for the single-instruction arms. -/
theorem wf_two_op (d s : LOperand) (op : String)
    (hd : opResolved d = true) (hs : opResolved s = true)
    (hmem : ¬ (isMemX86 d = true ∧ isMemX86 s = true)) :
    wfLinstr (.Lopn [d] op [s]) = true := by
  unfold wfLinstr instrOperands atMostOneMem widthConsistent countMem
  simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil,
    hd, hs, Bool.and_true, Bool.true_and, decide_eq_true_eq]
  -- goal: (filter isMemX86 [d, s]).length ≤ 1
  rcases Bool.eq_false_or_eq_true (isMemX86 d) with hdm | hdm <;>
    rcases Bool.eq_false_or_eq_true (isMemX86 s) with hsm | hsm <;>
    simp_all [List.filter]

/-- A two-operand instruction where the *source* (or dest) is the scratch `R15`
    is WF whenever the other operand is resolved: the scratch is a register, so
    at most one memory operand remains. -/
theorem wf_scratch_src (d : LOperand) (op : String)
    (hd : opResolved d = true) :
    wfLinstr (.Lopn [d] op [.reg reloadScratch]) = true := by
  apply wf_two_op d _ op hd reloadScratch_ok.1
  intro ⟨_, hc⟩
  exact absurd (reloadScratch_ok.2.symm.trans hc) (by decide)

/-- Source-scratch with `R14`. -/
theorem wf_scratch2_src (d : LOperand) (op : String)
    (hd : opResolved d = true) :
    wfLinstr (.Lopn [d] op [.reg reloadScratch2]) = true := by
  apply wf_two_op d _ op hd reloadScratch2_ok.1
  intro ⟨_, hc⟩
  exact absurd (reloadScratch2_ok.2.symm.trans hc) (by decide)

/-- A scratch destination is WF whenever the source is resolved. -/
theorem wf_scratch_dst (s : LOperand) (op : String)
    (hs : opResolved s = true) :
    wfLinstr (.Lopn [.reg reloadScratch] op [s]) = true := by
  apply wf_two_op _ s op reloadScratch_ok.1 hs
  intro ⟨hc, _⟩
  exact absurd (reloadScratch_ok.2.symm.trans hc) (by decide)

/-- A scratch-`R14` destination is WF whenever the source is resolved. -/
theorem wf_scratch2_dst (s : LOperand) (op : String)
    (hs : opResolved s = true) :
    wfLinstr (.Lopn [.reg reloadScratch2] op [s]) = true := by
  apply wf_two_op _ s op reloadScratch2_ok.1 hs
  intro ⟨hc, _⟩
  exact absurd (reloadScratch2_ok.2.symm.trans hc) (by decide)

/-- A two-address binop `[d] op [d, s]` (d the implicit self-source) is WF when
    `d` is a resolved **non-memory** operand and `s` is resolved: the only
    possible memory operand is `s`, so the count is ≤ 1. -/
theorem wf_binop (d s : LOperand) (op : String)
    (hd : opResolved d = true) (hdMem : isMemX86 d = false)
    (hs : opResolved s = true) :
    wfLinstr (.Lopn [d] op [d, s]) = true := by
  unfold wfLinstr instrOperands atMostOneMem widthConsistent countMem
  simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil,
    hd, hs, Bool.and_true, Bool.true_and, decide_eq_true_eq]
  simp only [List.filter, hdMem]
  rcases Bool.eq_false_or_eq_true (isMemX86 s) with hm | hm <;>
    simp [hm]

/-- A store-core instruction `[dArr] opn [addr', v]` is WF when `dArr` is a
    resolved non-memory operand, `addr'` is a resolved SIB element (a single
    memory operand), and `v` is a resolved non-memory operand (a register or the
    routing scratch): the only memory operand is `addr'`, so the count is ≤ 1. -/
theorem wf_store_core (dArr addr' v : LOperand) (opn : String)
    (hda : opResolved dArr = true) (hdaMem : isMemX86 dArr = false)
    (haddr : opResolved addr' = true)
    (hv : opResolved v = true) (hvMem : isMemX86 v = false) :
    wfLinstr (.Lopn [dArr] opn [addr', v]) = true := by
  unfold wfLinstr instrOperands atMostOneMem widthConsistent countMem
  simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil,
    hda, haddr, hv, Bool.and_true, Bool.true_and, decide_eq_true_eq]
  simp only [List.filter, hdaMem, hvMem]
  rcases Bool.eq_false_or_eq_true (isMemX86 addr') with ha | ha <;> simp [ha]

/-- The flat `mem.R14.0` destination of the address-fold store arm is a resolved
    base+offset memory name. -/
theorem scratch2Mem_resolved :
    opResolved (LOperand.reg ("mem." ++ reloadScratch2 ++ ".0")) = true := by
  decide

/-- A physical register name is never a SIB spill (`k.`-prefixed) name. -/
theorem physReg_not_sibSpill {n : String} (h : n ∈ x86PhysRegNames) :
    sibNameSpill n = false := by
  simp only [x86PhysRegNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp only [sibNameSpill, isPrefixOf_eq_hasPrefix] <;> decide

/-- A physical register name is never a memory operand (`isMemX86 = false`): it
    carries none of the `k.`/`qsave.`/`mem.` prefixes. -/
theorem physReg_not_mem {n : String} (h : n ∈ x86PhysRegNames) :
    isMemX86 (.reg n) = false := by
  simp only [x86PhysRegNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp only [isMemX86, isPrefixOf_eq_hasPrefix] <;> decide

/-- On an already-`opResolved` operand, `legalizeSibElem` is the identity (no
    reload): a resolved `arrIdx` already has physical base/index, so neither is a
    spill; a non-SIB operand is untouched by definition. -/
theorem legalizeSibElem_id_of_resolved (o : LOperand) (h : opResolved o = true) :
    legalizeSibElem o = ([], o) := by
  cases o with
  | arrIdx base idx scale =>
    simp only [opResolved, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hbm, him⟩, _⟩ := h
    simp only [legalizeSibElem, physReg_not_sibSpill hbm, physReg_not_sibSpill him,
      if_false, Bool.false_eq_true, List.append_nil]
  | _ => rfl

/-- `legalizeMov dst src` produces only WF instructions, given resolved operands
    whose memory status coincides with their spill status. When both are spills
    it routes through `R15`; otherwise the single direct copy already has ≤ 1
    memory operand. -/
theorem legalizeMov_wf (dst src : LOperand) (mov : String)
    (hdst : opResolved dst = true) (hsrc : opResolved src = true)
    (hcd : memCoincidesSpill dst) (hcs : memCoincidesSpill src) :
    ∀ i ∈ legalizeMov dst src mov, wfLinstr i = true := by
  intro i hi
  unfold legalizeMov at hi
  by_cases hb : (dst.isSpill && src.isSpill) = true
  · rw [if_pos hb] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi
    · subst hi; exact wf_scratch_dst src mov hsrc
    · subst hi; exact wf_scratch_src dst mov hdst
  · rw [if_neg hb] at hi
    -- `hb` false ⇒ not both spills ⇒ not both mem (via coincidence).
    rw [List.mem_singleton] at hi; subst hi
    apply wf_two_op dst src mov hdst hsrc
    intro ⟨hdm, hsm⟩
    rw [memCoincidesSpill] at hcd hcs
    have : (dst.isSpill && src.isSpill) = true := by
      rw [Bool.and_eq_true]; exact ⟨hcd ▸ hdm, hcs ▸ hsm⟩
    exact hb this

/-- `legalizeMemLoad dst src opn` produces only WF instructions, given resolved
    operands whose memory status coincides with their spill status. When `dst` is
    a spill it routes the load through `R15` (`opn` writes `R15`, then `mov dst,
    R15`); otherwise the direct load already has ≤ 1 memory operand. Direct
    refutation of bug class 1 (the `mem → mem` load). -/
theorem legalizeMemLoad_wf (dst src : LOperand) (opn mov : String)
    (hdst : opResolved dst = true) (hsrc : opResolved src = true)
    (hcd : memCoincidesSpill dst) (_hcs : memCoincidesSpill src) :
    ∀ i ∈ legalizeMemLoad dst src opn mov, wfLinstr i = true := by
  intro i hi
  unfold legalizeMemLoad at hi
  -- `src` is resolved ⇒ the SIB-base legalization is the identity (no prelude).
  rw [legalizeSibElem_id_of_resolved src hsrc] at hi
  simp only [List.nil_append] at hi
  by_cases hsp : dst.isSpill = true
  · rw [if_pos hsp] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi
    · subst hi; exact wf_scratch_dst src opn hsrc
    · subst hi; exact wf_scratch_src dst _ hdst
  · rw [Bool.not_eq_true] at hsp
    rw [if_neg (by rw [hsp]; exact Bool.false_ne_true)] at hi
    rw [List.mem_singleton] at hi; subst hi
    apply wf_two_op dst src opn hdst hsrc
    intro ⟨hdm, _⟩
    rw [memCoincidesSpill] at hcd
    rw [hcd, hsp] at hdm
    exact absurd hdm (by decide)

/-- `legalizeMemStore dArr addr val opn` produces only WF instructions, given
    resolved operands whose memory status coincides with their spill status. When
    `val` is a spill it routes through `R15` (`mov R15, val`, then the store with
    `R15`); otherwise the direct store already has ≤ 1 memory operand. Direct
    refutation of bug class 2 (the `mem → mem` store).

    When the SIB index is the value scratch `R15`, the address is folded into
    `R14` by a `LEA` and the value is stored through the flat `mem.R14.0`
    operand.

    The store instruction `[dArr] opn [addr, R15]` (or `[addr, val]`) has two
    sources; `wf_store_core` handles the ≤ 1-memory count over the
    `dArr :: addr :: v :: []` operand list (the array-result `dArr` names the
    functionally-updated array and is itself a register, never memory). -/
theorem legalizeMemStore_wf (dArr addr val : LOperand) (opn mov : String)
    (hda : opResolved dArr = true) (hdaMem : isMemX86 dArr = false)
    (haddr : opResolved addr = true)
    (hval : opResolved val = true) (hvc : memCoincidesSpill val) :
    ∀ i ∈ legalizeMemStore dArr addr val opn mov, wfLinstr i = true := by
  intro i hi
  unfold legalizeMemStore at hi
  -- `addr` is resolved ⇒ the SIB-base legalization is the identity (no prelude).
  rw [legalizeSibElem_id_of_resolved addr haddr] at hi
  simp only [List.nil_append] at hi
  rw [memCoincidesSpill] at hvc
  cases addr with
  | arr _ _ => simp only [opResolved, Bool.false_eq_true] at haddr
  | reg n =>
    cases hsp : val.isSpill <;> rw [hsp] at hi
    · -- direct store: `val` is not a spill, hence not memory.
      rw [List.mem_singleton] at hi; subst hi
      exact wf_store_core _ _ val opn hda hdaMem haddr hval (by rw [hvc, hsp])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · subst hi; exact wf_scratch_dst val _ hval
      · subst hi
        exact wf_store_core _ _ _ opn hda hdaMem haddr
          reloadScratch_ok.1 reloadScratch_ok.2
  | imm v =>
    cases hsp : val.isSpill <;> rw [hsp] at hi
    · rw [List.mem_singleton] at hi; subst hi
      exact wf_store_core _ _ val opn hda hdaMem haddr hval (by rw [hvc, hsp])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · subst hi; exact wf_scratch_dst val _ hval
      · subst hi
        exact wf_store_core _ _ _ opn hda hdaMem haddr
          reloadScratch_ok.1 reloadScratch_ok.2
  | arrIdx b iN sc =>
    cases hsp : val.isSpill <;> simp only [hsp] at hi
    · rw [List.mem_singleton] at hi; subst hi
      exact wf_store_core _ _ val opn hda hdaMem haddr hval (by rw [hvc, hsp])
    · by_cases hc : (iN == reloadScratch) = true
      · -- index-collision arm: the SIB address is folded into `R14` by a `LEA`,
        -- then the value goes through `R15` into the flat `mem.R14.0` operand.
        rw [if_pos hc] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | hi | hi
        · subst hi; exact wf_scratch2_dst _ _ haddr
        · subst hi; exact wf_scratch_dst val _ hval
        · subst hi; exact wf_scratch_src _ _ scratch2Mem_resolved
      · rw [if_neg hc] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | hi
        · subst hi; exact wf_scratch_dst val _ hval
        · subst hi
          exact wf_store_core _ _ _ opn hda hdaMem haddr
            reloadScratch_ok.1 reloadScratch_ok.2

/-- `legalizeBinop dst src opn` produces only WF instructions, given resolved
    operands whose memory status coincides with their spill status. Every
    emitted `Lopn` is a `mov`/op with at most one memory operand: the routing
    always pins the non-MOV op's operands to `R15`/`R14`. -/
theorem legalizeBinop_wf (dst src : LOperand) (opn mov : String)
    (hdst : opResolved dst = true) (hsrc : opResolved src = true)
    (hcd : memCoincidesSpill dst) (hcs : memCoincidesSpill src) :
    ∀ i ∈ legalizeBinop dst src opn mov, wfLinstr i = true := by
  intro i hi
  unfold legalizeBinop at hi
  rw [memCoincidesSpill] at hcd hcs
  -- Case on the four shapes.
  rcases hd : dst.isSpill with _ | _ <;> rcases hs : src.isSpill with _ | _ <;>
    rw [hd, hs] at hi <;> simp only [] at hi <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  · -- (false,false): `[dst] opn [dst, src]`; neither mem.
    subst hi
    have hdm : isMemX86 dst = false := by rw [hcd, hd]
    have hsm : isMemX86 src = false := by rw [hcs, hs]
    unfold wfLinstr instrOperands atMostOneMem widthConsistent countMem
    simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil,
      hdst, hsrc, Bool.and_true, Bool.true_and, decide_eq_true_eq]
    simp [List.filter, hdm, hsm]
  · -- (false,true): `mov R15, src; op dst [dst, R15]`.
    have hdm : isMemX86 dst = false := by rw [hcd, hd]
    rcases hi with hi | hi
    · subst hi; exact wf_scratch_dst src mov hsrc
    · subst hi; exact wf_binop dst (.reg reloadScratch) opn hdst hdm reloadScratch_ok.1
  · -- (true,false): `mov R15, dst; op R15 [R15, src]; mov dst, R15`.
    rcases hi with hi | hi | hi
    · subst hi; exact wf_scratch_dst dst mov hdst
    · subst hi
      exact wf_binop (.reg reloadScratch) src opn reloadScratch_ok.1
        reloadScratch_ok.2 hsrc
    · subst hi; exact wf_scratch_src dst mov hdst
  · -- (true,true): `mov R15, dst; mov R14, src; op R15 [R15, R14]; mov dst, R15`.
    rcases hi with hi | hi | hi | hi
    · subst hi; exact wf_scratch_dst dst mov hdst
    · subst hi; exact wf_scratch2_dst src mov hsrc
    · subst hi
      exact wf_binop (.reg reloadScratch) (.reg reloadScratch2) opn
        reloadScratch_ok.1 reloadScratch_ok.2 reloadScratch2_ok.1
    · subst hi; exact wf_scratch_src dst mov hdst

/-! ## 6b. The SIB-base legalization produces a resolved address (bug class 3 on
the *address*: `(%<UNKNOWN:k.N>, …)`)

`legalizeSibElem` (in `JasminLprogExport`) reloads a spilled SIB base/index into
the reserved scratches `R14`/`R15`, so the rewritten `arrIdx` always carries two
*register* (physical) base/index names — the only legal x86 SIB form. We prove
its output is WF: the reload prelude `mov`s each carry ≤ 1 memory operand, and
the fixed `arrIdx` is `opResolved` given each base/index is *either* a physical
register *or* a spill slot (the producer's invariant after RA — `remapOperand`
maps every SIB name to either an allocatable register or a `k.N` spill). -/

/-- A SIB base/index name is **SIB-ok** iff it is a resolvable physical register
    *or* a parseable spill slot `k.<n>` (a `spillNameResolved` name the spilling
    allocator may produce). Every `arrIdx` the post-RA `remapOperand` emits has
    SIB-ok base and index (`physRegName` yields either an allocatable register or
    a `k.<n>` spill). -/
def sibArgOk (n : String) : Prop :=
  (n ∈ x86PhysRegNames) ∨ spillNameResolved n = true

/-- The producer invariant for a SIB element fed to `legalizeSibElem`: its base
    and index are each SIB-ok, and its scale is a legal x86 SIB scale. -/
def sibElemArgsOk (base idx : String) (scale : Nat) : Prop :=
  sibArgOk base ∧ sibArgOk idx ∧ (scale ∈ ([1, 2, 4, 8] : List Nat))

/-- A parseable spill `k.<n>` is itself `sibNameSpill` (carries the `k.` prefix). -/
theorem spillResolved_isSibSpill {n : String} (h : spillNameResolved n = true) :
    sibNameSpill n = true := by
  unfold spillNameResolved at h
  unfold sibNameSpill
  rw [Bool.and_eq_true] at h; rw [isPrefixOf_eq_hasPrefix]; exact h.1

/-- A SIB-ok name, when it is a spill (`sibNameSpill`), is a *resolved* spill. -/
theorem sibArgOk_spill_resolved {n : String}
    (hok : sibArgOk n) (hsp : sibNameSpill n = true) : spillNameResolved n = true := by
  rcases hok with hph | hsr
  · exact absurd hsp (by rw [physReg_not_sibSpill hph]; decide)
  · exact hsr

/-- A SIB-ok name, when it is *not* a spill, is a physical register. -/
theorem sibArgOk_nonspill_phys {n : String}
    (hok : sibArgOk n) (hns : sibNameSpill n = false) : n ∈ x86PhysRegNames := by
  rcases hok with hph | hsr
  · exact hph
  · exact absurd (spillResolved_isSibSpill hsr) (by rw [hns]; decide)

/-- A reload prelude instruction `mov scratch, spill` emitted by
    `legalizeSibElem` is WF: the scratch is a register, the spill is a resolved
    `k.<n>`, so it carries exactly one memory operand. -/
theorem sib_reload_wf (scratch spill : String) (mov : String)
    (hsc : scratch ∈ x86PhysRegNames) (hsp : spillNameResolved spill = true) :
    wfLinstr (.Lopn [.reg scratch] mov [.reg spill]) = true := by
  apply wf_two_op (.reg scratch) (.reg spill) mov
  · simp only [opResolved, regNameResolved, hsc, decide_true, Bool.true_or]
  · simp only [opResolved, regNameResolved, hsp, Bool.or_true, Bool.true_or]
  · intro ⟨hsm, _⟩
    rw [physReg_not_mem hsc] at hsm
    exact absurd hsm (by decide)

/-- After `legalizeSibElem`, the fixed `arrIdx` is `opResolved`: both its base
    and index are physical registers (a spilled one was reloaded into a scratch,
    a non-spilled one was already a physical register). -/
theorem legalizeSibElem_fixed_resolved (base idx : String) (scale : Nat)
    (h : sibElemArgsOk base idx scale) :
    opResolved (legalizeSibElem (.arrIdx base idx scale)).2 = true := by
  obtain ⟨hb, hi, hs⟩ := h
  unfold legalizeSibElem
  by_cases hbs : sibNameSpill base = true <;> by_cases his : sibNameSpill idx = true <;>
    simp only [hbs, his, if_true, if_false, Bool.false_eq_true, opResolved,
      Bool.and_eq_true, decide_eq_true_eq]
  · exact ⟨⟨by decide, by decide⟩, hs⟩
  · refine ⟨⟨by decide, ?_⟩, hs⟩
    exact sibArgOk_nonspill_phys hi (by rw [Bool.not_eq_true] at his; exact his)
  · refine ⟨⟨?_, by decide⟩, hs⟩
    exact sibArgOk_nonspill_phys hb (by rw [Bool.not_eq_true] at hbs; exact hbs)
  · refine ⟨⟨?_, ?_⟩, hs⟩
    · exact sibArgOk_nonspill_phys hb (by rw [Bool.not_eq_true] at hbs; exact hbs)
    · exact sibArgOk_nonspill_phys hi (by rw [Bool.not_eq_true] at his; exact his)

/-- Every reload-prelude instruction `legalizeSibElem` prepends is WF. -/
theorem legalizeSibElem_prelude_wf (base idx : String) (scale : Nat)
    (hb : sibArgOk base) (hi : sibArgOk idx) :
    ∀ i ∈ (legalizeSibElem (.arrIdx base idx scale)).1, wfLinstr i = true := by
  intro i hmem
  unfold legalizeSibElem at hmem
  simp only at hmem
  by_cases hbs : sibNameSpill base = true <;> by_cases his : sibNameSpill idx = true <;>
    simp only [hbs, his, if_true, if_false, List.append_nil, List.nil_append,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Bool.false_eq_true] at hmem
  · rcases hmem with hm | hm
    · subst hm
      exact sib_reload_wf reloadScratch2 base _ (by decide)
        (sibArgOk_spill_resolved hb hbs)
    · subst hm
      exact sib_reload_wf reloadScratch idx _ (by decide)
        (sibArgOk_spill_resolved hi his)
  · subst hmem
    exact sib_reload_wf reloadScratch2 base _ (by decide)
      (sibArgOk_spill_resolved hb hbs)
  · subst hmem
    exact sib_reload_wf reloadScratch idx _ (by decide)
      (sibArgOk_spill_resolved hi his)

/-! ## 6c. The full memory load/store legalization is WF on a **spilled-base SIB**

The bug class 3 the ChaCha emit hit was a SIB element with a *spilled* base
(`movq %r15, (%<UNKNOWN:k.5>, %rax, 8)`), which `legalizeMemLoad_wf`/
`legalizeMemStore_wf` above do **not** cover (they require the SIB operand to be
already-`opResolved`, i.e. base/index already physical). These two theorems close
that case: given the SIB element's base/index are SIB-ok (physical or a parseable
spill) and the value/dst are resolved, **every** instruction the legalizer emits
— the address-reload prelude *and* the core load/store — is WF. This is the
direct refutation of the third remaining ChaCha codegen error. -/

/-- **The full memory-STORE legalization is WF, including the spilled-SIB-base
    case** (bug class 3 on the address). Given the SIB destination's base/index
    are SIB-ok and the value is resolved with memory-status coinciding with its
    spill status, every emitted instruction — the address-reload prelude *and*
    the core store — is WF. Direct refutation of the third ChaCha codegen error
    `movq %r15, (%<UNKNOWN:k.5>, %rax, 8)`. -/
theorem legalizeMemStore_sib_wf (scale : Nat)
    (dArrOp valOp : LOperand) (bN iN : String) (opn mov : String)
    (hda : opResolved dArrOp = true) (hdaMem : isMemX86 dArrOp = false)
    (hsib : sibElemArgsOk bN iN scale)
    (hval : opResolved valOp = true) (hvc : memCoincidesSpill valOp) :
    ∀ i ∈ legalizeMemStore dArrOp (.arrIdx bN iN scale) valOp opn mov,
      wfLinstr i = true := by
  intro i hi
  unfold legalizeMemStore at hi
  obtain ⟨hb, hidx, hs⟩ := hsib
  -- The address prelude is WF, and the fixed SIB element is resolved.
  have haddr' : opResolved (legalizeSibElem (.arrIdx bN iN scale)).2 = true :=
    legalizeSibElem_fixed_resolved bN iN scale ⟨hb, hidx, hs⟩
  have hpre : ∀ j ∈ (legalizeSibElem (.arrIdx bN iN scale)).1, wfLinstr j = true :=
    legalizeSibElem_prelude_wf bN iN scale hb hidx
  rw [memCoincidesSpill] at hvc
  cases hlz : legalizeSibElem (LOperand.arrIdx bN iN scale) with
  | mk addrPre addr' =>
    rw [hlz] at haddr' hpre
    simp only [hlz] at hi
    simp only at haddr' hpre
    -- The value routing shared by every arm but the index-collision one.
    have hcore : ∀ m : String, ∀ j ∈
        [LinstrR.Lopn [LOperand.reg reloadScratch] m [valOp],
         LinstrR.Lopn [dArrOp] opn [addr', LOperand.reg reloadScratch]],
        wfLinstr j = true := by
      intro m j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with hj | hj
      · subst hj; exact wf_scratch_dst valOp _ hval
      · subst hj
        exact wf_store_core _ _ _ opn hda hdaMem haddr'
          reloadScratch_ok.1 reloadScratch_ok.2
    cases addr' with
    | arr _ _ => simp only [opResolved, Bool.false_eq_true] at haddr'
    | reg n =>
      cases hsp : valOp.isSpill
      · simp only [hsp] at hi
        rw [List.mem_append] at hi
        rcases hi with hi | hi
        · exact hpre i hi
        · rw [List.mem_singleton] at hi; subst hi
          exact wf_store_core _ _ valOp opn hda hdaMem haddr' hval (by rw [hvc, hsp])
      · simp only [hsp] at hi
        rw [List.mem_append] at hi
        rcases hi with hi | hi
        · exact hpre i hi
        · exact hcore _ i hi
    | imm v =>
      cases hsp : valOp.isSpill
      · simp only [hsp] at hi
        rw [List.mem_append] at hi
        rcases hi with hi | hi
        · exact hpre i hi
        · rw [List.mem_singleton] at hi; subst hi
          exact wf_store_core _ _ valOp opn hda hdaMem haddr' hval (by rw [hvc, hsp])
      · simp only [hsp] at hi
        rw [List.mem_append] at hi
        rcases hi with hi | hi
        · exact hpre i hi
        · exact hcore _ i hi
    | arrIdx b2 i2 s2 =>
      cases hsp : valOp.isSpill
      · simp only [hsp] at hi
        rw [List.mem_append] at hi
        rcases hi with hi | hi
        · exact hpre i hi
        · rw [List.mem_singleton] at hi; subst hi
          exact wf_store_core _ _ valOp opn hda hdaMem haddr' hval (by rw [hvc, hsp])
      · simp only [hsp] at hi
        by_cases hc : (i2 == reloadScratch) = true
        · -- index-collision arm: the SIB address is folded into `R14` by a `LEA`,
          -- then the value goes through `R15` into the flat `mem.R14.0` operand.
          rw [if_pos hc] at hi
          rw [List.mem_append] at hi
          rcases hi with hi | hi
          · exact hpre i hi
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with hi | hi | hi
            · subst hi; exact wf_scratch2_dst _ _ haddr'
            · subst hi; exact wf_scratch_dst valOp _ hval
            · subst hi; exact wf_scratch_src _ _ scratch2Mem_resolved
        · rw [if_neg hc] at hi
          rw [List.mem_append] at hi
          rcases hi with hi | hi
          · exact hpre i hi
          · exact hcore _ i hi

/-- **The full memory-LOAD legalization is WF, including the spilled-SIB-base
    case** (bug class 3 on the address). Given the SIB source's base/index are
    SIB-ok and the destination is resolved with memory-status coinciding with its
    spill status, every emitted instruction — the address-reload prelude *and*
    the core load — is WF. -/
theorem legalizeMemLoad_sib_wf (dstOp : LOperand) (bN iN : String) (scale : Nat)
    (opn mov : String)
    (hdst : opResolved dstOp = true)
    (hsib : sibElemArgsOk bN iN scale) (hcd : memCoincidesSpill dstOp) :
    ∀ i ∈ legalizeMemLoad dstOp (.arrIdx bN iN scale) opn mov, wfLinstr i = true := by
  intro i hi
  unfold legalizeMemLoad at hi
  obtain ⟨hb, hidx, hs⟩ := hsib
  have hsrc' : opResolved (legalizeSibElem (.arrIdx bN iN scale)).2 = true :=
    legalizeSibElem_fixed_resolved bN iN scale ⟨hb, hidx, hs⟩
  rw [List.mem_append] at hi
  rcases hi with hi | hi
  · exact legalizeSibElem_prelude_wf bN iN scale hb hidx i hi
  · by_cases hsp : dstOp.isSpill = true
    · rw [if_pos hsp] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · subst hi
        -- `[R15] opn [src']`: R15 not mem, src' is the sole mem operand.
        apply wf_two_op (.reg reloadScratch) _ opn reloadScratch_ok.1 hsrc'
        intro ⟨hc, _⟩
        exact absurd (reloadScratch_ok.2.symm.trans hc) (by decide)
      · subst hi; exact wf_scratch_src dstOp _ hdst
    · rw [Bool.not_eq_true] at hsp
      rw [if_neg (by rw [hsp]; exact Bool.false_ne_true)] at hi
      rw [List.mem_singleton] at hi; subst hi
      -- `[dst] opn [src']`: dst not spill ⇒ not mem; src' is the sole mem operand.
      apply wf_two_op dstOp _ opn hdst hsrc'
      intro ⟨hdm, _⟩
      rw [memCoincidesSpill] at hcd
      rw [hcd, hsp] at hdm
      exact absurd hdm (by decide)

/-! ## 6d. `physRegName` always renders a resolved, spill-coinciding operand

`remapOperand` rewrites every body operand name through
`physRegName (physMapTabled …)`. The output of `physRegName` is *always* a
concrete x86 location: either an allocatable GP register (`gpRegNames`, all in
`x86PhysRegNames`) for a slot index `< numGPRegs`, or a parseable spill slot
`"k." ++ toString k` for an index `≥ numGPRegs`. So every remapped `.reg`
operand is `opResolved`, its memory status coincides with its spill status
(`memCoincidesSpill` — a `physRegName` name carries no `qsave.`/`mem.` prefix,
only `k.` or none), and as a SIB base/index it is `sibArgOk`.

The GP-block facts are decidable. The spill-block facts rest on `SpillNameWF`
below: a `"k." ++ toString k` name is a parseable spill (`spillNameResolved`) and
carries the `k.` prefix. It holds by the decimal round trip
`natOfDigitsSep?_toString` (`spill_name_round_trip`). -/

/-- The String fact `physRegName`'s spill block rests on: a rendered spill name
    `"k." ++ toString k` parses as a `spillNameResolved` slot, and carries the
    `"k."` prefix (so `isMemX86`/`isSpill` see it). -/
def SpillNameWF : Prop := ∀ k : Nat,
  spillNameResolved ("k." ++ toString k) = true ∧
  "k.".isPrefixOf ("k." ++ toString k) = true

/-- **Every rendered spill name is resolved**: `SpillNameWF` holds, by the decimal round
    trip `natOfDigitsSep?_toString`. -/
theorem spill_name_round_trip : SpillNameWF := by
  intro k
  have hp : JasminLprogExport.hasPrefix ("k." ++ toString k) "k." = true := by
    simp [JasminLprogExport.hasPrefix, String.toList_append]
  refine ⟨?_, by rw [isPrefixOf_eq_hasPrefix]; exact hp⟩
  unfold spillNameResolved
  rw [hp, Bool.true_and, String.toList_append]
  simp only [show "k.".toList = ['k', '.'] from rfl, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, natOfDigitsSep?_toString, Option.isSome_some]

/-- Every `gpRegNames` entry is an `x86PhysRegNames` entry (decidable). -/
theorem gpRegNames_subset_phys :
    ∀ r ∈ JasminLprogExport.gpRegNames, r ∈ x86PhysRegNames := by decide

/-- No `gpRegNames` entry carries a `k.`/`qsave.`/`mem.` memory prefix
    (decidable) — so a GP physical register is never a memory operand. -/
theorem gp_not_spillPrefix : ∀ r ∈ JasminLprogExport.gpRegNames,
    "k.".isPrefixOf r = false ∧ "qsave.".isPrefixOf r = false ∧
      "mem.".isPrefixOf r = false := by
  simp only [isPrefixOf_eq_hasPrefix]; decide

/-- The spill name `physRegName` renders for a slot index `≥ numGPRegs`
    (local copy of `ToLprogFaithfulRA.physRegName_spill_eq`, inlined to keep this
    module's import footprint at `JasminLprogExport`). -/
theorem physRegName_spill_eq {a : Nat} (ha : JasminLprogExport.numGPRegs ≤ a)
    (hv : a < JasminLprogExport.vectorBase) :
    JasminLprogExport.physRegName a = "k." ++ toString (a - JasminLprogExport.numGPRegs) := by
  unfold JasminLprogExport.physRegName
  rw [if_neg (show ¬ a ≥ JasminLprogExport.vectorBase from by omega),
    List.getElem?_eq_none (by simpa [JasminLprogExport.numGPRegs] using ha)]
  rfl

/-- **`physRegName` always renders a resolved operand name.** GP block: the name
    is in `x86PhysRegNames`. Spill block: it is a `spillNameResolved` slot (via
    `SpillNameWF`). -/
theorem physRegName_resolved (p : Nat)
    (hv : p < JasminLprogExport.vectorBase) :
    regNameResolved (JasminLprogExport.physRegName p) = true := by
  rcases Nat.lt_or_ge p JasminLprogExport.numGPRegs with hp | hp
  · have hmem : JasminLprogExport.physRegName p ∈ x86PhysRegNames := by
      have hg : JasminLprogExport.physRegName p ∈ JasminLprogExport.gpRegNames := by
        unfold JasminLprogExport.physRegName
        rw [if_neg (show ¬ p ≥ JasminLprogExport.vectorBase from by omega)]
        have hp' : p < JasminLprogExport.gpRegNames.length := by
          simpa [JasminLprogExport.numGPRegs] using hp
        rw [List.getElem?_eq_getElem hp']
        exact List.getElem_mem hp'
      exact gpRegNames_subset_phys _ hg
    unfold regNameResolved
    simp [hmem]
  · rw [physRegName_spill_eq hp hv]
    unfold regNameResolved
    rw [(spill_name_round_trip (p - JasminLprogExport.numGPRegs)).1]
    simp

/-- **`physRegName`'s name has coinciding memory/spill status.** A `physRegName`
    name is either a GP register (no memory prefix, so both `isMemX86` and
    `isSpill` are `false`) or a `k.` spill (both `true`) — never a `qsave.`/`mem.`
    name (which would be memory but not a spill). So `memCoincidesSpill` holds for
    every remapped register operand, the producer invariant the `legalize*_wf`
    helpers require. -/
theorem physRegName_memCoincides (p : Nat)
    (hv : p < JasminLprogExport.vectorBase) :
    isMemX86 (.reg (JasminLprogExport.physRegName p)) =
      LOperand.isSpill (.reg (JasminLprogExport.physRegName p)) := by
  rcases Nat.lt_or_ge p JasminLprogExport.numGPRegs with hp | hp
  · have hg : JasminLprogExport.physRegName p ∈ JasminLprogExport.gpRegNames := by
      unfold JasminLprogExport.physRegName
      rw [if_neg (show ¬ p ≥ JasminLprogExport.vectorBase from by omega)]
      have hp' : p < JasminLprogExport.gpRegNames.length := by
        simpa [JasminLprogExport.numGPRegs] using hp
      rw [List.getElem?_eq_getElem hp']
      exact List.getElem_mem hp'
    obtain ⟨hk, hq, hm⟩ := gp_not_spillPrefix _ hg
    simp only [isMemX86, LOperand.isSpill, hk, hq, hm, Bool.or_self]
  · rw [physRegName_spill_eq hp hv]
    simp only [isMemX86, LOperand.isSpill,
      (spill_name_round_trip (p - JasminLprogExport.numGPRegs)).2,
      Bool.true_or]

/-- **`physRegName`'s name is `sibArgOk`** (a physical register or a parseable
    spill) — so a remapped SIB base/index always satisfies the producer invariant
    `legalizeSibElem_*` / `legalizeMem*_sib_wf` need. -/
theorem physRegName_sibArgOk (p : Nat)
    (hv : p < JasminLprogExport.vectorBase) :
    sibArgOk (JasminLprogExport.physRegName p) := by
  rcases Nat.lt_or_ge p JasminLprogExport.numGPRegs with hp | hp
  · left
    have hg : JasminLprogExport.physRegName p ∈ JasminLprogExport.gpRegNames := by
      unfold JasminLprogExport.physRegName
      rw [if_neg (show ¬ p ≥ JasminLprogExport.vectorBase from by omega)]
      have hp' : p < JasminLprogExport.gpRegNames.length := by
        simpa [JasminLprogExport.numGPRegs] using hp
      rw [List.getElem?_eq_getElem hp']
      exact List.getElem_mem hp'
    exact gpRegNames_subset_phys _ hg
  · right
    rw [physRegName_spill_eq hp hv]
    exact (spill_name_round_trip (p - JasminLprogExport.numGPRegs)).1

/-! ## 6e. The injected lowering passes all produce WF output

Each `physBody` arm emits through one of the legalization / lowering passes.
§6 proved `legalizeMov`/`legalizeBinop`/`legalizeMemLoad`/`legalizeMemStore`
(and the SIB variants) WF. Here we cover the three remaining passes the body
walk uses — `lowerNativeShiftRotate`, `lowerTwoAddrShiftImm`, `lowerTwoAddr` —
given resolved, spill-coinciding operands. Composed with §6d's `physRegName`
facts, every body instruction is WF. -/

/-- A native immediate shift/rotate lowering is WF on resolved, coinciding
    operands: each emitted `Lopn` is either a scratch-routed MOV/op or the direct
    single-operand form (≤ 1 memory operand). -/
theorem lowerNativeShiftRotate_wf (dst s : LOperand) (opn mov : String)
    (hdst : opResolved dst = true) (hs : opResolved s = true)
    (hcd : memCoincidesSpill dst) (_hcs : memCoincidesSpill s) :
    ∀ i ∈ JasminLprogExport.lowerNativeShiftRotate dst s opn mov, wfLinstr i = true := by
  intro i hi
  unfold JasminLprogExport.lowerNativeShiftRotate at hi
  by_cases hb : (dst.isSpill || s.isSpill) = true
  · rw [if_pos hb] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi
    · subst hi; exact wf_scratch_dst s mov hs
    · subst hi
      apply wf_two_op (.reg reloadScratch) (.reg reloadScratch) opn reloadScratch_ok.1
        reloadScratch_ok.1
      intro ⟨hc, _⟩
      exact absurd (reloadScratch_ok.2.symm.trans hc) (by decide)
    · subst hi; exact wf_scratch_src dst mov hdst
  · rw [if_neg hb] at hi
    rw [List.mem_singleton] at hi; subst hi
    apply wf_two_op dst s opn hdst hs
    intro ⟨hdm, _hsm⟩
    rw [memCoincidesSpill] at hcd
    have : (dst.isSpill || s.isSpill) = true := by
      rw [Bool.or_eq_true]; left; rw [← hcd]; exact hdm
    exact hb this

/-- A constant-shift two-address lowering is WF on resolved, coinciding operands:
    the count rides as an `.imm` (resolved, non-memory), the destructive op is a
    `wf_binop`, and the optional leading copy is a `legalizeMov`. -/
theorem lowerTwoAddrShiftImm_wf (dst s0 : LOperand) (v : Nat) (opn mov : String)
    (hdst : opResolved dst = true) (hs0 : opResolved s0 = true)
    (hcd : memCoincidesSpill dst) (hcs : memCoincidesSpill s0) :
    ∀ i ∈ JasminLprogExport.lowerTwoAddrShiftImm dst s0 v opn mov, wfLinstr i = true := by
  intro i hi
  unfold JasminLprogExport.lowerTwoAddrShiftImm at hi
  by_cases hsp : dst.isSpill = true
  · rw [if_pos hsp] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi
    · subst hi; exact wf_scratch_dst s0 mov hs0
    · subst hi
      exact wf_binop (.reg reloadScratch) (.imm v) opn reloadScratch_ok.1
        reloadScratch_ok.2 (by simp [opResolved])
    · subst hi; exact wf_scratch_src dst mov hdst
  · rw [Bool.not_eq_true] at hsp
    have hdMem : isMemX86 dst = false := by rw [memCoincidesSpill] at hcd; rw [hcd, hsp]
    by_cases heq : dst = s0
    · rw [if_neg (by rw [hsp]; exact Bool.false_ne_true), if_pos heq] at hi
      rw [List.mem_singleton] at hi; subst hi
      exact wf_binop dst (.imm v) opn hdst hdMem (by simp [opResolved])
    · rw [if_neg (by rw [hsp]; exact Bool.false_ne_true), if_neg heq] at hi
      rw [List.mem_append] at hi
      rcases hi with hi | hi
      · exact legalizeMov_wf dst s0 mov hdst hs0 hcd hcs i hi
      · rw [List.mem_singleton] at hi; subst hi
        exact wf_binop dst (.imm v) opn hdst hdMem (by simp [opResolved])

/-- The wide-immediate materialization prelude is WF and its returned source is
    resolved and coinciding: either the original (resolved, coinciding) source,
    or a `MOV:64 R14, #v` parking the wide imm into the scratch `R14`. -/
theorem materializeWideImm_wf (s1 : LOperand) (mov : String)
    (hs1 : opResolved s1 = true) (hcs : memCoincidesSpill s1) :
    (∀ i ∈ (JasminLprogExport.materializeWideImm s1 mov).1, wfLinstr i = true) ∧
    opResolved (JasminLprogExport.materializeWideImm s1 mov).2 = true ∧
    memCoincidesSpill (JasminLprogExport.materializeWideImm s1 mov).2 := by
  have hscratch2 : opResolved (.reg reloadScratch2) = true ∧
      memCoincidesSpill (.reg reloadScratch2) := by
    refine ⟨reloadScratch2_ok.1, ?_⟩
    rw [memCoincidesSpill, reloadScratch2_ok.2]
    simp only [LOperand.isSpill, reloadScratch2, isPrefixOf_eq_hasPrefix]; decide
  cases s1 with
  | imm w =>
    unfold JasminLprogExport.materializeWideImm
    split
    · split
      · refine ⟨?_, hscratch2.1, hscratch2.2⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        subst hi
        exact wf_scratch2_dst (.imm _) "MOV:64" (by simp [opResolved])
      · exact ⟨by simp, hs1, hcs⟩
    · exact ⟨by simp, hs1, hcs⟩
  | _ => exact ⟨by simp [JasminLprogExport.materializeWideImm], hs1, hcs⟩

/-- A general two-address binop lowering is WF on resolved, coinciding operands:
    the wide-imm prelude, the optional leading copy, and the destructive op all
    carry ≤ 1 memory operand (composing `materializeWideImm_wf`, `legalizeMov_wf`,
    `legalizeBinop_wf`). -/
theorem lowerTwoAddr_wf (dst s0 s1 : LOperand) (opn mov : String)
    (hdst : opResolved dst = true) (hs0 : opResolved s0 = true) (hs1 : opResolved s1 = true)
    (hcd : memCoincidesSpill dst) (hcs0 : memCoincidesSpill s0) (hcs1 : memCoincidesSpill s1) :
    ∀ i ∈ JasminLprogExport.lowerTwoAddr dst s0 s1 opn mov, wfLinstr i = true := by
  intro i hi
  unfold JasminLprogExport.lowerTwoAddr at hi
  obtain ⟨hpre, hs1', hcs1'⟩ := materializeWideImm_wf s1 mov hs1 hcs1
  rcases hmw : JasminLprogExport.materializeWideImm s1 mov with ⟨immPre, s1v⟩
  rw [hmw] at hi hpre hs1' hcs1'
  simp only at hi hpre hs1' hcs1'
  by_cases heq : dst = s0
  · rw [if_pos heq] at hi
    rw [List.mem_append] at hi
    rcases hi with hi | hi
    · exact hpre i hi
    · exact legalizeBinop_wf dst s1v opn mov hdst hs1' hcd hcs1' i hi
  · rw [if_neg heq] at hi
    rw [List.mem_append, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact legalizeMov_wf dst s0 mov hdst hs0 hcd hcs0 i hi
    · exact hpre i hi
    · exact legalizeBinop_wf dst s1v opn mov hdst hs1' hcd hcs1' i hi

/-! ## 6f. Remapped operands, memory-name operands, and the prologue/epilogue

`remapOperand` always produces a resolved, spill-coinciding `.reg` (§6d), so the
direct body arms over `.reg`/`.imm` operands are resolved. The inline ABI
load/store legs and the epilogue's restore use `memName reloadScratch2 off`
(`mem.R14.<off>`) memory operands, which resolve by `mem_name_round_trip`. The prologue, callee-save restore epilogue, and
the `wfLcmd`-over-`flatMap` recursion shape are proved here. -/

/-- A remapped `.reg` operand is resolved (§6d, lifted through `remapOperand`). -/
theorem remap_reg_resolved (body : Lcmd) (tbl : Array Nat)
    (n : String)
    (hv : JasminLprogExport.physMapTabled tbl (JasminLprogExport.nameSlot body n)
      < JasminLprogExport.vectorBase) :
    opResolved (JasminLprogExport.remapOperand body tbl (.reg n)) = true := by
  unfold JasminLprogExport.remapOperand opResolved
  exact physRegName_resolved _ hv

/-- A remapped `.reg` operand has coinciding memory/spill status (§6d). -/
theorem remap_reg_coincides (body : Lcmd) (tbl : Array Nat)
    (n : String)
    (hv : JasminLprogExport.physMapTabled tbl (JasminLprogExport.nameSlot body n)
      < JasminLprogExport.vectorBase) :
    memCoincidesSpill (JasminLprogExport.remapOperand body tbl (.reg n)) := by
  show isMemX86 (JasminLprogExport.remapOperand body tbl (.reg n)) =
    LOperand.isSpill (JasminLprogExport.remapOperand body tbl (.reg n))
  unfold JasminLprogExport.remapOperand
  exact physRegName_memCoincides _ hv

/-- The String fact of the memory names: the inline ABI load/store / epilogue memory
    operand `mem.R14.<off>` resolves (`memNameResolved`) and carries the `mem.`
    prefix (so `isMemX86` sees it). -/
def MemNameWF : Prop := ∀ off : Nat,
  memNameResolved (JasminLprogExport.memName reloadScratch2 off) = true ∧
  "mem.".isPrefixOf (JasminLprogExport.memName reloadScratch2 off) = true

/-- **Every `mem.R14.<off>` name is resolved**: `MemNameWF` holds, by the decimal round
    trip `natOfDigitsSep?_toString` and the absence of `.` in a decimal rendering. -/
theorem mem_name_round_trip : MemNameWF := by
  intro off
  have hl : (JasminLprogExport.memName reloadScratch2 off).toList =
      ['m', 'e', 'm', '.', 'R', '1', '4', '.'] ++ (toString off).toList := by
    simp [JasminLprogExport.memName, reloadScratch2, String.toList_append]
  have hp : JasminLprogExport.hasPrefix (JasminLprogExport.memName reloadScratch2 off)
      "mem." = true := by
    simp [JasminLprogExport.hasPrefix, hl]
  refine ⟨?_, by rw [isPrefixOf_eq_hasPrefix]; exact hp⟩
  have hn := natOfDigitsSep?_toString off
  unfold memNameResolved
  rw [hp, Bool.true_and, hl]
  generalize (toString off).toList = l at hn ⊢
  have hs : List.span (fun x => decide (x ≠ '.'))
      (List.drop 4 (['m', 'e', 'm', '.', 'R', '1', '4', '.'] ++ l)) =
        (['R', '1', '4'], '.' :: l) := rfl
  rw [hs]
  simp only [hn, Option.isSome_some, Bool.and_true]
  decide

/-- A `mem.R14.<off>` memory operand is resolved (via `MemNameWF`). -/
theorem memDst_resolved (off : Nat) :
    opResolved (.reg (JasminLprogExport.memName reloadScratch2 off)) = true := by
  simp only [opResolved, regNameResolved, (mem_name_round_trip off).1, Bool.or_true]

/-- A `mem.R14.<off>` operand is a memory operand (`isMemX86`, via `MemNameWF`). -/
theorem memDst_isMem (off : Nat) :
    isMemX86 (.reg (JasminLprogExport.memName reloadScratch2 off)) = true := by
  simp only [isMemX86, (mem_name_round_trip off).2, Bool.or_true]

/-- **The `wfLcmd`-over-`flatMap` recursion.** A `flatMap`-built body is WF iff
    every emitted chunk of every source instruction is WF — the structural shape
    of the `physBody*` body walk. Reduces whole-body WF to a per-source-instr
    obligation. -/
theorem wfLcmd_flatMap (body : Lcmd) (f : Linstr → Lcmd)
    (h : ∀ src ∈ body, ∀ o ∈ f src, wfLinstr o.li_i = true) :
    wfLcmd (body.flatMap f) = true := by
  unfold wfLcmd
  rw [List.all_eq_true]
  intro o ho
  rw [List.mem_flatMap] at ho
  obtain ⟨src, hsrc, hof⟩ := ho
  exact h src hsrc o hof

/-- `wfLcmd` distributes over `++`. -/
theorem wfLcmd_append (a b : Lcmd) (ha : wfLcmd a = true) (hb : wfLcmd b = true) :
    wfLcmd (a ++ b) = true := by
  unfold wfLcmd at *
  rw [List.all_eq_true] at *
  intro o ho
  rw [List.mem_append] at ho
  rcases ho with ho | ho
  · exact ha o ho
  · exact hb o ho

/-- **The ABI prologue is WF.** The 9-instruction pointer-save + callee-save +
    RSI-park prelude is a fixed list of `MOVQ`s, each a register↔`qsave.`-slot
    move (one memory operand). Fully concrete (`buildPrologue` ignores its
    arguments), so `decide` per instruction. -/
theorem buildPrologue_wf (virt : Lfundef) (tbl : Array Nat)
    (inLoadMap : JasminLprogExport.InLoadMap) :
    ∀ o ∈ JasminLprogExport.buildPrologue virt tbl inLoadMap, wfLinstr o.li_i = true := by
  intro o ho
  unfold JasminLprogExport.buildPrologue at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [wfLinstr, instrOperands, atMostOneMem, countMem, isMemX86,
      isPrefixOf_eq_hasPrefix]

/-- **The callee-save restore epilogue is WF.** A fixed list of 6 `MOVQ`s, each a
    register ← `qsave.`-slot restore (one memory operand). Concrete, so
    `decide` per instruction. -/
theorem calleeSaveRestoreEpilogue_wf :
    ∀ o ∈ JasminLprogExport.calleeSaveRestoreEpilogue, wfLinstr o.li_i = true := by
  intro o ho
  unfold JasminLprogExport.calleeSaveRestoreEpilogue at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with h|h|h|h|h|h <;> subst h <;>
    simp +decide [wfLinstr, instrOperands, atMostOneMem, countMem, isMemX86,
      isPrefixOf_eq_hasPrefix]

/-! ## 6g. The inline ABI load/store legs and the whole-body assembly

`physBodyWithStores` emits, per source instruction, `loads ++ expanded ++ store`.
The `loads` leg (inline argument loads, routed `mov R14,[qsave.RSI]; load`) and
the `store` leg (inline output stores, routed via `R14`/`R15`) are self-legalizing
— every emitted `Lopn` carries ≤ 1 memory operand and resolves through §6d/§6f.
We prove both legs WF here. The `expanded` leg is the verified two-address body
(§6/§6e for its legalize-routed arms); its direct-emit fallthrough arms carry the
post-RA no-two-spill obligation (the documented Phase-2 residual), so the whole
body's WF is assembled below from a per-source-instruction `bodyWithInlineStores`
WF hypothesis composed with the proved prologue/epilogue wrappers. -/

/-- **The inline argument-load leg is WF.** `mov R14,[qsave.RSI]` recovers the
    input pointer, then a load of `[R14+off]` into the (resolved, coinciding)
    physical destination — routed through `R15` when the destination is a spill.
    Each `Lopn` carries ≤ 1 memory operand. -/
theorem loadLeg_wf (dst : LOperand) (off : Nat) (abiMovReg abiMovBuf : String)
    (hdst : opResolved dst = true) (hcdst : memCoincidesSpill dst) :
    ∀ o ∈ (if dst.isSpill then
      [(⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg JasminLprogExport.abiSaveRsiName]⟩ : Linstr),
       ⟨0, .Lopn [.reg reloadScratch] abiMovBuf [.reg (JasminLprogExport.memName reloadScratch2 off)]⟩,
       ⟨0, .Lopn [dst] abiMovReg [.reg reloadScratch]⟩]
     else
      [⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg JasminLprogExport.abiSaveRsiName]⟩,
       ⟨0, .Lopn [dst] abiMovBuf [.reg (JasminLprogExport.memName reloadScratch2 off)]⟩]),
      wfLinstr o.li_i = true := by
  intro o ho
  have hRI : wfLinstr (.Lopn [.reg reloadScratch2] "MOVQ"
      [.reg JasminLprogExport.abiSaveRsiName]) = true := by
    simp +decide [wfLinstr, instrOperands, atMostOneMem, countMem, isMemX86,
      isPrefixOf_eq_hasPrefix]
  have hmd := memDst_resolved off
  by_cases hsp : dst.isSpill = true
  · rw [if_pos hsp] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with h|h|h <;> subst h
    · exact hRI
    · exact wf_two_op _ _ abiMovBuf reloadScratch_ok.1 hmd
        (by intro ⟨hc, _⟩; exact absurd (reloadScratch_ok.2.symm.trans hc) (by decide))
    · exact wf_scratch_src dst abiMovReg hdst
  · rw [Bool.not_eq_true] at hsp
    rw [if_neg (by rw [hsp]; exact Bool.false_ne_true)] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with h|h <;> subst h
    · exact hRI
    · apply wf_two_op _ _ abiMovBuf hdst hmd
      intro ⟨hc, _⟩
      rw [memCoincidesSpill] at hcdst
      rw [hcdst, hsp] at hc; exact absurd hc (by decide)

/-- **The inline output-store leg is WF.** `mov R14,[qsave.RDI]` recovers the
    output pointer, then a store of the (resolved, coinciding) source into
    `[R14+off]` — routed through `R15` when the source is a spill. Each `Lopn`
    carries ≤ 1 memory operand. -/
theorem storeLeg_wf (src : LOperand) (off : Nat) (abiMovReg abiMovBuf : String)
    (hsrc : opResolved src = true) (hcsrc : memCoincidesSpill src) :
    ∀ o ∈ (if src.isSpill then
      [(⟨0, .Lopn [.reg reloadScratch] abiMovReg [src]⟩ : Linstr),
       ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg JasminLprogExport.abiSaveRdiName]⟩,
       ⟨0, .Lopn [.reg (JasminLprogExport.memName reloadScratch2 off)] abiMovBuf [.reg reloadScratch]⟩]
     else
      [⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg JasminLprogExport.abiSaveRdiName]⟩,
       ⟨0, .Lopn [.reg (JasminLprogExport.memName reloadScratch2 off)] abiMovBuf [src]⟩]),
      wfLinstr o.li_i = true := by
  intro o ho
  have hRO : wfLinstr (.Lopn [.reg reloadScratch2] "MOVQ"
      [.reg JasminLprogExport.abiSaveRdiName]) = true := by
    simp +decide [wfLinstr, instrOperands, atMostOneMem, countMem, isMemX86,
      isPrefixOf_eq_hasPrefix]
  have hmd := memDst_resolved off
  by_cases hsp : src.isSpill = true
  · rw [if_pos hsp] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with h|h|h <;> subst h
    · exact wf_scratch_dst src abiMovReg hsrc
    · exact hRO
    · exact wf_two_op _ _ abiMovBuf hmd reloadScratch_ok.1
        (by intro ⟨_, hc⟩; exact absurd (reloadScratch_ok.2.symm.trans hc) (by decide))
  · rw [Bool.not_eq_true] at hsp
    rw [if_neg (by rw [hsp]; exact Bool.false_ne_true)] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with h|h <;> subst h
    · exact hRO
    · apply wf_two_op _ _ abiMovBuf hmd hsrc
      intro ⟨_, hc⟩
      rw [memCoincidesSpill] at hcsrc
      rw [hcsrc, hsp] at hc; exact absurd hc (by decide)

/-- `wfLcmd` from a per-instruction predicate. -/
theorem wfLcmd_of_forall (c : Lcmd) (h : ∀ o ∈ c, wfLinstr o.li_i = true) :
    wfLcmd c = true := by
  unfold wfLcmd; rw [List.all_eq_true]; exact h

/-- `wfLcmd` is preserved by `dropLast` (a sublist). -/
theorem wfLcmd_dropLast (c : Lcmd) (h : wfLcmd c = true) :
    wfLcmd c.dropLast = true := by
  unfold wfLcmd at *
  rw [List.all_eq_true] at *
  intro o ho
  exact h o (List.dropLast_subset _ ho)

/-- **The ABI wrapper preserves WF.** Given a WF inline-store body `bws`, the
    full export `prologue ++ insertEpilogue bws calleeSaveRestoreEpilogue` is WF:
    the prologue (`buildPrologue_wf`), the body's `dropLast` (`wfLcmd_dropLast`),
    the callee-save restore (`calleeSaveRestoreEpilogue_wf`), and the trailing
    `Lret` are each WF, and `wfLcmd` distributes over `++`. -/
theorem abiWrap_wf (prologue bws : Lcmd) (virt : Lfundef) (tbl : Array Nat)
    (inLoadMap : JasminLprogExport.InLoadMap)
    (hpro : prologue = JasminLprogExport.buildPrologue virt tbl inLoadMap)
    (hbws : wfLcmd bws = true) :
    wfLcmd (prologue ++
      JasminLprogExport.insertEpilogue bws JasminLprogExport.calleeSaveRestoreEpilogue) = true := by
  apply wfLcmd_append
  · subst hpro
    exact wfLcmd_of_forall _ (buildPrologue_wf virt tbl inLoadMap)
  · unfold JasminLprogExport.insertEpilogue
    apply wfLcmd_append
    · apply wfLcmd_append
      · exact wfLcmd_dropLast bws hbws
      · exact wfLcmd_of_forall _ calleeSaveRestoreEpilogue_wf
    · decide

/-! ## 7. The lowering-preserves-WF goal (checker-gated) -/

/-- **The lowering-preserves-WF goal.** Stated, not proved: the post-RA ABI
    export of any `Com jasminDialect` is `wfLprog`. Proving it requires recursing
    through the large `physBody*` / ABI-prologue definitions (Phase-2 territory,
    the same as `LprogJasminWellFormed`'s residuals). Until then the orchestrator
    runs `wfLprog (Com.toLprogPhysAbi …)` as a **decidable gate** on each emitted
    leaf — which catches all three ChaCha bugs at lowering time. This `def` names
    the obligation so it is an explicit goal, not an implicit assumption (and is
    **not** an admitted proof). -/
def toLprogPhysAbi_wf_goal : Prop :=
  ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat),
    wfLprog (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
      outStoreMap abiArgs abiTyin) = true

/-- **The whole-program WF assembly (modulo the body's per-instruction WF).**
    Every `Com.toLprogPhysAbi` export is one function whose body is
    `prologue ++ insertEpilogue bodyWithInlineStores calleeSaveRestoreEpilogue`.
    Given the per-instruction WF of the inline-store body `bodyWithInlineStores`
    (`hbody` — the documented post-RA Phase-2 obligation, whose self-legalizing
    legs are discharged by `loadLeg_wf`/`storeLeg_wf`/the §6 `legalize*_wf` and
    §6e `lower*_wf` lemmas), the full program is `wfLprog`.

    `hbody` is phrased on the export's own body via `wfLcmd … .lfd_body`-style
    extraction: the wrapper (prologue + callee-save restore + `Lret`) is proved
    WF here (`abiWrap_wf`), so the only residual carried is the verified
    two-address body's direct-emit no-two-spill content. -/
theorem toLprogPhysAbi_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat)
    (prologue bws : Lcmd) (virt : Lfundef) (tbl : Array Nat)
    (hbodyEq :
      (comToLfundefPhysAbi com shiftImm immSlotMap inLoadMap outStoreMap
        abiArgs abiTyin).lfd_body =
        prologue ++ JasminLprogExport.insertEpilogue bws
          JasminLprogExport.calleeSaveRestoreEpilogue)
    (hpro : prologue = JasminLprogExport.buildPrologue virt tbl inLoadMap)
    (hbws : wfLcmd bws = true) :
    wfLprog (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
      outStoreMap abiArgs abiTyin) = true := by
  unfold Com.toLprogPhysAbi wfLprog
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  show wfLfundef (comToLfundefPhysAbi com shiftImm immSlotMap inLoadMap
    outStoreMap abiArgs abiTyin) = true
  unfold wfLfundef
  rw [hbodyEq]
  exact abiWrap_wf prologue bws virt tbl inLoadMap hpro hbws

/-- A concrete smoke test that the checker runs and accepts a well-formed
    single-function program (a register-to-register move and a return). -/
example :
    wfLprog
      { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := [],
        lp_funcs := [("smoke",
          { lfd_body :=
              [⟨0, .Lopn [.reg "RAX"] "MOV" [.reg "RBX"]⟩, ⟨0, .Lret⟩] })] }
      = true := by
  simp +decide [wfLprog, wfLfundef, wfLcmd, wfLinstr, instrOperands, atMostOneMem, countMem,
    isMemX86, isPrefixOf_eq_hasPrefix]

/-- A concrete smoke test that the checker **rejects** the bug-class-1/2 shape:
    a `mem → mem` move (`mov k.1, k.0`) is not WF (two memory operands). -/
example :
    wfLinstr (.Lopn [.reg "k.1"] "MOV" [.reg "k.0"]) = false := by
  simp +decide [wfLinstr, instrOperands, atMostOneMem, countMem, isMemX86,
    isPrefixOf_eq_hasPrefix]

/-- A concrete smoke test that the checker **rejects** the bug-class-3 shape: an
    unresolved spill placeholder (a `k.` with no parseable index) is not WF. -/
example :
    wfLinstr (.Lopn [.reg "RAX"] "MOV" [.reg "k."]) = false := by
  simp +decide

/-- A concrete smoke test that the checker **rejects** the third remaining ChaCha
    shape: a store into a SIB element whose **base** is a spill slot
    (`movq %r15, (%<UNKNOWN:k.5>, %rax, 8)`) — the SIB base must be a register. -/
example :
    wfLinstr (.Lopn [.reg "RBX"] "STOREIDX:64"
      [.arrIdx "k.5" "RAX" 8, .reg "R15"]) = false := by
  simp +decide

/-- A concrete smoke test that `legalizeMemStore` **fixes** the spilled-SIB-base
    store: every emitted instruction (the `mov R14, k.5` base reload and the
    rewritten `STOREIDX (%R14,%RAX,8), R15`) is WF — the array-result `dArr` is a
    resolved register (`RBX` here). -/
example :
    (JasminLprogExport.legalizeMemStore (.reg "RBX") (.arrIdx "k.5" "RAX" 8)
      (.reg "R15") "STOREIDX:64").all (fun i => wfLinstr i) = true := by
  simp +decide [JasminLprogExport.legalizeMemStore, JasminLprogExport.legalizeSibElem,
    sibNameSpill, LOperand.isSpill, reloadScratch, reloadScratch2, wfLinstr, instrOperands,
    atMostOneMem, countMem, isMemX86, isPrefixOf_eq_hasPrefix]

end CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86
