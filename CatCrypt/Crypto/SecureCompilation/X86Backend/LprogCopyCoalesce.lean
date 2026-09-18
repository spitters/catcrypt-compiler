/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront

/-!
# Register copy coalescing on Lprog bodies

An opt-in `Lprog → Lprog` pass over the owned-RA linear body
(`JasminLprogExport.Lcmd`). The LowCT front computes every scalar binding into a
scratch register and then copies it into the register that holds the binding,
through a `MOV:64` or a register rebind `SHL:0:64` (which `LprogAsmPrinter`
prints as `movq`). The pass removes such a copy by computing the value in the
copy's destination in the first place.

## The rewrites

The rewrites act within one sweep over the body, left to right.

* **Coalescing.** At a copy `k = Lopn [d] c [s]` (`c` is `MOV:64`, `MOVQ`, or a
  64-bit immediate `shl` by `0`; `s ≠ d` are pool registers), the pass looks
  backwards for the nearest instruction `x` that fully defines `s`
  (`defOk`: a recognised write-only op of width at least 32 whose sources do not
  name `d`). Every instruction strictly between `x` and `k` must pass `midOk`:
  a recognised, non-runtime-indexed `Lopn` that names `d` nowhere (not as a
  register, not as the base of a `mem.<base>.<off>` or SIB operand) and names
  `s` only as a bare register operand. When additionally `s` is dead after `k`
  (`deadAt`), the pass retargets `x` to write `d`, renames `s` to `d` in every
  instruction between, and drops `k`. Renaming is uniform, so a two-address
  instruction `Lopn [s] op [s, t]` becomes `Lopn [d] op [d, t]` and keeps the
  tie between its destination and first source that the printer relies on.
  An immediate definition `x = MOV:64 s, $k` is a special case.
* **Identity ALU ops.** `Lopn [r] op [r, $0]` with `op` one of `XOR:64`,
  `ADD:64`, `SUB:64`, `OR:64` is dropped when `flagsDeadAfter` holds: scanning
  forward, an instruction that writes every arithmetic flag without reading one
  (`ADD`, `SUB`, `AND`, `OR`, `XOR`, `CMP`, `TEST`) occurs before any other
  instruction than a flag-silent move.
* **Rebind normalisation.** A copy the sweep keeps whose mnemonic is a 64-bit
  `shl` by `0` between two distinct pool registers is rewritten to `MOV:64`
  (`normCopy`). Both print as `movq`; the `MOV:64` form is the move shape
  `LcmdCopyPropagate` forwards and deletes.

`coalesceRounds` alternates the sweep with
`LprogOptPipeline.optimizeLprogBasicBlocks`: copy propagation there folds the
immediate of a coalesced `mov $k` into its consumer and forwards the copies the
sweep normalised, which exposes further coalescing.

## Barriers and flags

Control flow and every mnemonic outside `LcmdCopyPropagate.isRecognizedOpn`
stop the backward search (`findDef`) and the liveness scan (`deadAt`); the
end of the body keeps every register live. `isRecognizedOpn` excludes the
mnemonics with an implicit register operand (the `MULX` family), so every
register an instruction in the window reads is named in its operands.

The linear model `JasminLsem.lsemStraight` has no flags. Coalescing keeps the
instruction sequence and every opcode, renames registers only, and deletes a
`mov`, which writes no flag; so the flag dataflow of the rendered text is
unchanged. An identity op is dropped only when the next flag event forward of
it is a write of all flags, so no instruction reads the flags it set. When a
later identity op is dropped in turn, its own check covers the stretch after
it, so the stretch from the first dropped op to the next remaining flag write
contains no flag reader.

## Main results

* `coalesceBody`, `coalesceFundef`, `coalesceLprog`: the pass.
* `coalesceSite_stateStore`: one coalescing rewrite preserves the store image
  of `lsemStraight` on every start state.
* `coalesceBody_stateStore`, `coalesceBody_lsem`, `coalesceFundef_stateStore`:
  the pass preserves the store image of `lsemStraight` (register map and
  memory, program counter excluded) on every body and every start state; the
  liveness and shape conditions are the pass's own Boolean checks.
* `combSelectCoalescedAsmN`: the owned rendering of the front-generated
  Ed25519 comb select after `ConstIndexFold.constIndexFold`, `spellLprog`, the
  basic-block pipeline and two rounds of `coalesceRounds`;
  `combSelectCoalescedLines` and `combSelectCoalescedClean` are its line count
  and the absence of an `UNHANDLED` printer sentinel.

## Semantics

The preservation theorems are stated over `JasminLsem.lsemStraight`, the model
`LcmdCopyPropagate.copyPropagateBody_stateStore` and
`LcmdReloadElim.reloadElimBody_lsem` use: a uniform word width, no flags, and
every named cell (`mem.<base>.<off>` included) a register of the store. The
width conditions (a 64-bit copy, a full-width definition, 64-bit identity ops)
and the address-register conditions of `operandOk` are what the rendered x86
text additionally needs and the model does not distinguish.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (stripAbiTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP physGPs nameReads operandReads isRecognizedOpn isDstWriteOnly effWidth
   instrUses fullDefsOf regDefsOf regDefsOf_singleton LiveAgree lsemStep_liveAgree
   lsemStep_reg_nonmem lsemStep_isSome_indep contains_instrUses_of_src
   contains_fullDefsOf_false)

/-! ## 1. Instruction shapes -/

/-- A 64-bit immediate `shl` by `0`: a `:64`-tagged mnemonic whose tag-stripped
    base is an immediate left shift with count `0` and is none of the literal
    single-source opcodes of `applyOpn`. `LprogAsmPrinter` prints it as `movq`
    (or nothing, for a self-copy). -/
def isShlZero64 (opn : String) : Bool :=
  hasSuffix opn ":64" && stripWidthTag opn != "MOV" && stripWidthTag opn != "MOVQ"
    && stripWidthTag opn != "MOV:8" && stripWidthTag opn != "MOV:16"
    && stripWidthTag opn != "LOADIDX" && stripWidthTag opn != "STOREIDX"
    && (match parseImmShiftMnem (stripWidthTag opn) with
        | some (att, k, _) => att == "shl" && k == 0
        | none => false)

/-- The 64-bit register copy mnemonics: `MOV:64`, `MOVQ` and a 64-bit `shl` by
    `0`. -/
def isCopyOpn (opn : String) : Bool :=
  opn == "MOV:64" || opn == "MOVQ" || isShlZero64 opn

/-- A register copy `Lopn [d] c [s]` between two distinct pool registers,
    returned as `(d, s)`. -/
def copyShape (i : Linstr) : Option (String × String) :=
  match i.li_i with
  | .Lopn [.reg d] opn [.reg s] =>
      if isCopyOpn opn && isPhysGP d && isPhysGP s && d != s then some (d, s) else none
  | _ => none

/-- A register rebind (a 64-bit `shl` by `0`) between two distinct pool
    registers is rewritten to the `MOV:64` copy it prints as, so that the move
    analyses of `LcmdCopyPropagate` recognise it; every other instruction is
    kept. -/
def normCopy (i : Linstr) : Linstr :=
  match i.li_i with
  | .Lopn [.reg d] opn [.reg s] =>
      if isShlZero64 opn && isPhysGP d && isPhysGP s && d != s then
        { i with li_i := .Lopn [.reg d] "MOV:64" [.reg s] }
      else i
  | _ => i

/-- The mnemonic is neither of the two runtime-indexed memory opcodes. -/
def notIdx (opn : String) : Bool := opn != "LOADIDX" && opn != "STOREIDX"

/-- Does the operand read register `r`, as a bare register or as an address
    register? -/
def mentions (r : String) (o : LOperand) : Bool := (operandReads o).contains r

/-- The operand names `s` at most as the bare register `.reg s`. -/
def onlyBare (s : String) : LOperand → Bool
  | .reg n => n == s || !(nameReads n).contains s
  | o => !(operandReads o).contains s

/-- An operand of an instruction between the definition and the copy: it does
    not name `d` and names `s` only as a bare register. -/
def operandOk (s d : String) (o : LOperand) : Bool := !mentions d o && onlyBare s o

/-- The definition a coalescing retargets: a recognised, non-runtime-indexed
    `Lopn [s] opn srcs` whose destination is written in full (write-only, width
    at least 32). For the three-source select `CMOV`, whose printed form writes
    its destination before it tests the condition, the sources do not name `d`;
    every other write-only form reads its sources before it writes. -/
def defOk (s d : String) (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg x] opn srcs =>
      x == s && isRecognizedOpn opn && notIdx opn && isDstWriteOnly opn
        && decide (32 ≤ effWidth opn)
        && (stripAbiTag opn != "CMOV" || srcs.all (fun o => !mentions d o))
  | _ => false

/-- An instruction between the definition and the copy: a recognised,
    non-runtime-indexed `Lopn` all of whose operands pass `operandOk`. -/
def midOk (s d : String) (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn dsts opn srcs =>
      isRecognizedOpn opn && notIdx opn && dsts.all (operandOk s d)
        && srcs.all (operandOk s d)
  | _ => false

/-! ## 2. Renaming -/

/-- Rename register name `s` to `d`. -/
def renameName (s d n : String) : String := if n = s then d else n

/-- Rename a bare register operand `s` to `d`; every other operand is kept. -/
def renameOperand (s d : String) : LOperand → LOperand
  | .reg n => .reg (renameName s d n)
  | o => o

/-- Rename `s` to `d` in every operand of an `Lopn`. -/
def renameInstr (s d : String) (i : Linstr) : Linstr :=
  match i.li_i with
  | .Lopn dsts opn srcs =>
      { i with li_i := .Lopn (dsts.map (renameOperand s d)) opn (srcs.map (renameOperand s d)) }
  | _ => i

/-- Rename `s` to `d` in the destinations of an `Lopn`, keeping its sources. -/
def retargetDef (s d : String) (i : Linstr) : Linstr :=
  match i.li_i with
  | .Lopn dsts opn srcs => { i with li_i := .Lopn (dsts.map (renameOperand s d)) opn srcs }
  | _ => i

/-! ## 3. The analyses -/

/-- Split a reversed window `rev` (nearest instruction first) at the nearest
    instruction passing `defOk s d`, every instruction before it passing
    `midOk s d`: `some (revMid, x, revPre)` with `rev = revMid ++ x :: revPre`. -/
def findDef (s d : String) : Lcmd → Option (Lcmd × Linstr × Lcmd)
  | [] => none
  | i :: rest =>
      if defOk s d i then some ([], i, rest)
      else if midOk s d i then
        match findDef s d rest with
        | some (m, x, p) => some (i :: m, x, p)
        | none => none
      else none

/-- Register `r` is dead at the head of the instruction list: a recognised `Lopn`
    that fully defines `r` occurs before any instruction that reads `r`, before
    any unrecognised or control-flow instruction, and before the end. -/
def deadAt (r : String) : Lcmd → Bool
  | [] => false
  | i :: rest =>
      match i.li_i with
      | .Lopn dsts opn srcs =>
          if isRecognizedOpn opn && !(instrUses dsts opn srcs).contains r then
            (fullDefsOf dsts opn).contains r || deadAt r rest
          else false
      | _ => false

/-- The 64-bit ALU mnemonics for which `op r, $0` leaves `r` unchanged. -/
def identityOpn (opn : String) : Bool :=
  opn == "XOR:64" || opn == "ADD:64" || opn == "SUB:64" || opn == "OR:64"

/-- An identity ALU instruction `Lopn [r] op [r, $0]` on a pool register. -/
def isIdentityOp (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg x] opn [.reg y, .imm k] => x == y && k == 0 && isPhysGP x && identityOpn opn
  | _ => false

/-- A mnemonic whose x86 instruction writes all six arithmetic flags and reads
    none. -/
def flagWriter (opn : String) : Bool :=
  match stripAbiTag opn with
  | "ADD" | "SUB" | "AND" | "OR" | "XOR" | "CMP" | "TEST" => true
  | _ => false

/-- A mnemonic whose x86 rendering is a sequence of moves: it neither reads nor
    writes a flag. -/
def flagSilent (opn : String) : Bool :=
  (match stripAbiTag opn with
   | "MOV" | "MOVQ" | "LOAD" | "STORE" | "LOADIDX" | "STOREIDX" | "LEA" => true
   | _ => false) || isShlZero64 opn

/-- The flags are dead at the head of the instruction list: a flag writer occurs
    after only flag-silent moves. -/
def flagsDeadAfter : Lcmd → Bool
  | [] => false
  | i :: rest =>
      match i.li_i with
      | .Lopn _ opn _ =>
          if flagWriter opn then true
          else if flagSilent opn then flagsDeadAfter rest
          else false
      | _ => false

/-! ## 4. The pass -/

/-- One left-to-right sweep. `rev` is the processed prefix, reversed; the body
    the sweep stands for is `rev.reverse ++ post`. -/
def coalesceGo : Lcmd → Lcmd → Lcmd
  | rev, [] => rev.reverse
  | rev, k :: post =>
      match copyShape k with
      | some (d, s) =>
          if deadAt s post then
            match findDef s d rev with
            | some (m, x, p) =>
                coalesceGo (m.map (renameInstr s d) ++ retargetDef s d x :: p) post
            | none => coalesceGo (normCopy k :: rev) post
          else coalesceGo (normCopy k :: rev) post
      | none =>
          if isIdentityOp k && flagsDeadAfter post then coalesceGo rev post
          else coalesceGo (normCopy k :: rev) post

/-- Copy coalescing and identity-op removal on one owned-RA body. -/
def coalesceBody (body : Lcmd) : Lcmd := coalesceGo [] body

/-- The pass on one `Lfundef` (body only). -/
def coalesceFundef (f : Lfundef) : Lfundef := { f with lfd_body := coalesceBody f.lfd_body }

/-- The pass on every function body of an `Lprog`. -/
def coalesceLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) => (n, coalesceFundef f) }

/-! ### Static pins of the rewrites

Each `#guard` below pins whether one rule fires on a four-instruction body in the
front's shapes; they are static checks of the rule set, evaluated at elaboration
in well under a second. -/

/-- A scratch computation copied into its home register, the scratch dead after
    the copy: the computation is retargeted and the copy dropped. -/
def demoCoalesce : Lcmd :=
  [ ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "R10"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "SHL:0:64" [.reg "R9"]⟩,
    ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RDX"]⟩ ]

#guard coalesceBody demoCoalesce =
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "XOR:64" [.reg "RAX", .reg "R10"]⟩,
    ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RDX"]⟩ ]

/-- The scratch is read after the copy: the copy stays, rewritten from the
    rebind to `MOV:64`. -/
def demoLive : Lcmd :=
  [ ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "R10"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "SHL:0:64" [.reg "R9"]⟩,
    ⟨0, .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "R9"]⟩ ]

#guard coalesceBody demoLive =
  [ ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "R10"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "R9"]⟩,
    ⟨0, .Lopn [.reg "R11"] "XOR:64" [.reg "R11", .reg "R9"]⟩ ]

/-- The copy's destination is read between the definition and the copy: the
    body is kept. -/
def demoDestRead : Lcmd :=
  [ ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "R9"]⟩,
    ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RDX"]⟩ ]

#guard coalesceBody demoDestRead = demoDestRead

/-- An identity `xor $0` is dropped before a flag-writing `sub` and kept before
    a flag-reading `adc`. -/
def demoIdentity (next : String) : Lcmd :=
  [ ⟨0, .Lopn [.reg "R9"] "XOR:64" [.reg "R9", .imm 0]⟩,
    ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "R9"]⟩,
    ⟨0, .Lopn [.reg "R8"] next [.reg "R8", .reg "RAX"]⟩ ]

#guard coalesceBody (demoIdentity "SUB:64") = (demoIdentity "SUB:64").drop 1
#guard coalesceBody (demoIdentity "ADC:64") = demoIdentity "ADC:64"

/-! ## 5. The Ed25519 comb select -/

/-- `n` rounds of `coalesceLprog` each followed by the basic-block pipeline
    `LprogOptPipeline.optimizeLprogBasicBlocks`, whose copy propagation folds
    the immediates and forwards the copies a coalescing exposes. -/
def coalesceRounds : Nat → Lprog → Lprog
  | 0, p => p
  | n + 1, p => coalesceRounds n (LprogOptPipeline.optimizeLprogBasicBlocks (coalesceLprog p))

/-- The exported front-generated `N`-entry comb select after
    `ConstIndexFold.constIndexFold`, `ConstIndexFold.spellLprog`, the basic-block
    pipeline and two rounds of `coalesceRounds`. -/
def combSelectCoalescedLprog (name : String) (N : Nat) : Option Lprog :=
  (CombSelectFront.combSelectLprog name N).map (fun lp =>
    coalesceRounds 2 (LprogOptPipeline.optimizeLprogBasicBlocks
      (ConstIndexFold.spellLprog (ConstIndexFold.constIndexFold lp))))

/-- The owned AT&T rendering of `combSelectCoalescedLprog` (the pure printer
    `renderLprogAtt`; the last round already ran the basic-block pipeline). -/
def combSelectCoalescedAsmN (name : String) (N : Nat) : Option String :=
  (combSelectCoalescedLprog name N).map (fun p => LprogAsmPrinter.renderLprogAtt p)

/-- The number of newline characters of a rendering. -/
def lineCount (t : String) : Nat := t.toList.count '\n'

/-- The rendering contains a printer `UNHANDLED` sentinel. -/
def hasUnhandled (t : String) : Bool := (t.splitOn "UNHANDLED").length != 1

/-- The line count of the coalesced `N`-entry select. -/
def combSelectCoalescedLines (N : Nat) : Option Nat :=
  (combSelectCoalescedAsmN "ed25519_comb_select_x86_from_lean" N).map lineCount

/-- The coalesced `N`-entry select renders, in at most `bound` lines. -/
def combSelectCoalescedLinesLe (N bound : Nat) : Bool :=
  match combSelectCoalescedLines N with
  | some n => decide (n ≤ bound)
  | none => false

/-- The coalesced `N`-entry select renders without an `UNHANDLED` sentinel. -/
def combSelectCoalescedClean (N : Nat) : Bool :=
  match combSelectCoalescedAsmN "ed25519_comb_select_x86_from_lean" N with
  | some t => !hasUnhandled t
  | none => false

/-! ## 6. Store congruence -/

/-- A straight-line run from two states with equal register map and memory
    reaches equal store images. -/
theorem lsemStraight_store_congr {w : Nat} (is : List LinstrR) :
    ∀ (σ τ : Lstate w), σ.lvm = τ.lvm → σ.lmem = τ.lmem →
      Option.map stateStore (lsemStraight is σ) = Option.map stateStore (lsemStraight is τ) := by
  induction is with
  | nil => intro σ τ hv hm; simp [stateStore, hv, hm]
  | cons i is ih =>
    intro σ τ hv hm
    have h := lsemStep_archAgree i (s := σ) (t := τ) ⟨hv, hm⟩
    simp only [lsemStraight_cons]
    cases h1 : lsemStep i σ with
    | none =>
      cases h2 : lsemStep i τ with
      | none => rfl
      | some _ => rw [h1, h2] at h; exact (h : False).elim
    | some σ₁ =>
      cases h2 : lsemStep i τ with
      | none => rw [h1, h2] at h; exact (h : False).elim
      | some τ₁ =>
        rw [h1, h2] at h
        exact ih σ₁ τ₁ h.1 h.2

/-- Binding two store-image-equal continuations to one result. -/
theorem store_bind_congr {w : Nat} (o : Option (Lstate w))
    (f g : Lstate w → Option (Lstate w))
    (h : ∀ st, Option.map stateStore (f st) = Option.map stateStore (g st)) :
    Option.map stateStore (o.bind f) = Option.map stateStore (o.bind g) := by
  cases o with
  | none => rfl
  | some st => exact h st

/-! ## 7. The copy, the rebind and the identity op in the model -/

/-- A copy mnemonic is neither runtime-indexed memory opcode. -/
theorem copyOpn_notIdx {opn : String} (h : isCopyOpn opn = true) :
    opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" := by
  constructor <;> (rintro rfl; exact absurd h (by decide))

/-- A copy mnemonic applied to one word returns it. -/
theorem applyOpn_copy {w : Nat} {opn : String} (h : isCopyOpn opn = true) (a : BitVec w) :
    applyOpn (stripWidthTag opn) [a] = some a := by
  unfold isCopyOpn at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | h
  · rw [show stripWidthTag "MOV:64" = "MOV" from by decide +kernel]; rfl
  · rw [stripWidthTag_MOVQ]; rfl
  · unfold isShlZero64 at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hp⟩ := h
    generalize stripWidthTag opn = m at h1 h2 h3 h4 h5 h6 hp ⊢
    split at hp
    · rename_i att k x heq
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      unfold applyOpn
      split <;> simp_all
    · exact absurd hp (by simp)

/-- A recognised copy writes its source word to its destination. -/
theorem copyShape_spec {i : Linstr} {d s : String} (h : copyShape i = some (d, s)) :
    isPhysGP d = true ∧ isPhysGP s = true ∧ d ≠ s ∧
      ∀ {w : Nat} (σ : Lstate w), lsemStep i.li_i σ = some ((σ.setReg d (σ.lvm s)).nextPc) := by
  unfold copyShape at h
  split at h
  · rename_i d' opn s' hi
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      obtain ⟨⟨⟨hcopy, hd⟩, hs⟩, hne⟩ := hc
      refine ⟨hd, hs, hne, fun σ => ?_⟩
      rw [hi, lsemStep_reg_nonmem _ _ _ _ (copyOpn_notIdx hcopy)]
      simp only [List.map_cons, List.map_nil, evalOperand, applyOpn_copy hcopy]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `normCopy` does not change the step. -/
theorem normCopy_step {w : Nat} (i : Linstr) (σ : Lstate w) :
    lsemStep (normCopy i).li_i σ = lsemStep i.li_i σ := by
  unfold normCopy
  split
  · rename_i d opn s hi
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      have hcopy : isCopyOpn opn = true := by simp [isCopyOpn, hc.1.1.1]
      show lsemStep (LinstrR.Lopn [.reg d] "MOV:64" [.reg s]) σ = lsemStep i.li_i σ
      rw [hi, lsemStep_reg_nonmem _ _ _ _ (copyOpn_notIdx hcopy),
        lsemStep_reg_nonmem _ _ _ _ ⟨by decide, by decide⟩]
      simp only [List.map_cons, List.map_nil, evalOperand, applyOpn_copy hcopy]
      rw [show stripWidthTag "MOV:64" = "MOV" from by decide +kernel]; rfl
    · rfl
  · rfl

/-- An identity ALU op steps to a state with the same register map and memory. -/
theorem identity_step {w : Nat} {i : Linstr} (h : isIdentityOp i = true) (σ : Lstate w) :
    ∃ σ', lsemStep i.li_i σ = some σ' ∧ σ'.lvm = σ.lvm ∧ σ'.lmem = σ.lmem := by
  unfold isIdentityOp at h
  split at h
  · rename_i x opn y k hi
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hxy, hk⟩, _⟩, hop⟩ := h
    subst hxy hk
    unfold identityOpn at hop
    simp only [Bool.or_eq_true, beq_iff_eq] at hop
    have hnm : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" := by
      rcases hop with ((rfl | rfl) | rfl) | rfl <;> decide
    have key : applyOpn (stripWidthTag opn) [σ.lvm x, BitVec.ofNat w 0] = some (σ.lvm x) := by
      rcases hop with ((rfl | rfl) | rfl) | rfl
      · rw [show stripWidthTag "XOR:64" = "XOR" from by decide +kernel]; simp [applyOpn]
      · rw [show stripWidthTag "ADD:64" = "ADD" from by decide +kernel]; simp [applyOpn]
      · rw [show stripWidthTag "SUB:64" = "SUB" from by decide +kernel]; simp [applyOpn]
      · rw [show stripWidthTag "OR:64" = "OR" from by decide +kernel]; simp [applyOpn]
    rw [hi, lsemStep_reg_nonmem _ _ _ _ hnm]
    simp only [List.map_cons, List.map_nil, evalOperand, key]
    refine ⟨_, rfl, ?_, rfl⟩
    funext r
    simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
    split
    · rename_i hr; rw [hr]
    · rfl
  · exact absurd h (by simp)

/-! ## 8. The renaming simulation -/

/-- The relation between the input run (`σ`) and the renamed run (`τ`) inside a
    coalesced range: memory agrees, `τ`'s `d` holds `σ`'s `s`, and every other
    register agrees. -/
def RenRel {w : Nat} (s d : String) (σ τ : Lstate w) : Prop :=
  σ.lmem = τ.lmem ∧ τ.lvm d = σ.lvm s ∧ ∀ r, r ≠ s → r ≠ d → τ.lvm r = σ.lvm r

/-- A register operand that does not mention the pool register `d` is not `d`. -/
theorem ne_of_not_mentions_reg {n d : String} (hd : isPhysGP d = true)
    (h : mentions d (.reg n) = false) : n ≠ d := by
  rintro rfl
  simp [mentions, operandReads, nameReads, hd] at h

/-- Under `RenRel`, a renamed operand that passes `operandOk` evaluates to the
    word the original operand evaluates to. -/
theorem evalOperand_rename {w : Nat} {s d : String} {σ τ : Lstate w} (hR : RenRel s d σ τ)
    (hs : isPhysGP s = true) (hd : isPhysGP d = true) (o : LOperand)
    (hok : operandOk s d o = true) :
    evalOperand τ (renameOperand s d o) = evalOperand σ o := by
  simp only [operandOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨hm, hb⟩ := hok
  cases o with
  | reg n =>
    simp only [renameOperand, renameName, evalOperand]
    by_cases hn : n = s
    · rw [if_pos hn, hn]; exact hR.2.1
    · rw [if_neg hn]; exact hR.2.2 n hn (ne_of_not_mentions_reg hd hm)
  | imm v => rfl
  | arr b i => simp only [renameOperand, evalOperand, hR.1]
  | arrIdx b i sc =>
    have hi1 : i ≠ d := by
      rintro rfl; simp [mentions, operandReads, hd] at hm
    have hi2 : i ≠ s := by
      rintro rfl; simp [onlyBare, operandReads, hs] at hb
    simp only [renameOperand, evalOperand, hR.1, hR.2.2 i hi2 hi1]

/-- One step of an instruction and of its renamed form, whose source lists
    evaluate to the same words: both are stuck, or both write the same word, to
    the destination and to its renamed form. -/
theorem step_rel {w : Nat} (s d : String) {σ τ : Lstate w} {dsts : List LOperand}
    {opn : String} {srcs srcs' : List LOperand} (hnm : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX")
    (heval : srcs'.map (evalOperand τ) = srcs.map (evalOperand σ)) :
    (lsemStep (.Lopn dsts opn srcs) σ = none ∧
      lsemStep (.Lopn (dsts.map (renameOperand s d)) opn srcs') τ = none) ∨
    ∃ x v, dsts = [.reg x] ∧ lsemStep (.Lopn dsts opn srcs) σ = some ((σ.setReg x v).nextPc) ∧
      lsemStep (.Lopn (dsts.map (renameOperand s d)) opn srcs') τ =
        some ((τ.setReg (renameName s d x) v).nextPc) := by
  match dsts with
  | [] => exact Or.inl ⟨by simp [lsemStep], by simp [lsemStep]⟩
  | [.reg x] =>
    simp only [List.map_cons, List.map_nil, renameOperand]
    rw [lsemStep_reg_nonmem _ _ _ _ hnm, lsemStep_reg_nonmem _ _ _ _ hnm, heval]
    cases applyOpn (w := w) (stripWidthTag opn) (srcs.map (evalOperand σ)) with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some v => exact Or.inr ⟨x, v, rfl, rfl, rfl⟩
  | [.imm _] => exact Or.inl ⟨by simp [lsemStep], by simp [lsemStep, renameOperand]⟩
  | [.arr _ _] => exact Or.inl ⟨by simp [lsemStep], by simp [lsemStep, renameOperand]⟩
  | [.arrIdx _ _ _] => exact Or.inl ⟨by simp [lsemStep], by simp [lsemStep, renameOperand]⟩
  | _ :: _ :: _ => exact Or.inl ⟨by simp [lsemStep], by simp [lsemStep]⟩

/-- `RenRel` is kept by a write of one word to a destination other than `d` and
    to its renamed form. -/
theorem RenRel.step {w : Nat} {s d : String} {σ τ : Lstate w} (hR : RenRel s d σ τ)
    {x : String} (hx : x ≠ d) (v : BitVec w) :
    RenRel s d ((σ.setReg x v).nextPc) ((τ.setReg (renameName s d x) v).nextPc) := by
  refine ⟨hR.1, ?_, ?_⟩
  · simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, renameName]
    by_cases hxs : x = s
    · subst hxs; simp
    · rw [if_neg hxs, if_neg (Ne.symm hx), if_neg (Ne.symm hxs)]; exact hR.2.1
  · intro r hrs hrd
    simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, renameName]
    by_cases hxs : x = s
    · subst hxs; rw [if_pos rfl, if_neg hrd, if_neg hrs]; exact hR.2.2 r hrs hrd
    · rw [if_neg hxs]
      split
      · rfl
      · exact hR.2.2 r hrs hrd

/-- The renamed range simulates the original under `RenRel`: both runs are
    stuck, or both complete in `RenRel`-related states. -/
theorem mid_sim {w : Nat} {s d : String} (hs : isPhysGP s = true) (hd : isPhysGP d = true) :
    ∀ (mid : Lcmd), mid.all (midOk s d) = true → ∀ (σ τ : Lstate w), RenRel s d σ τ →
      (lsemStraight (mid.map Linstr.li_i) σ = none ∧
        lsemStraight ((mid.map (renameInstr s d)).map Linstr.li_i) τ = none) ∨
      ∃ σ' τ', lsemStraight (mid.map Linstr.li_i) σ = some σ' ∧
        lsemStraight ((mid.map (renameInstr s d)).map Linstr.li_i) τ = some τ' ∧
        RenRel s d σ' τ' := by
  intro mid
  induction mid with
  | nil => intro _ σ τ hR; exact Or.inr ⟨σ, τ, rfl, rfl, hR⟩
  | cons k rest ih =>
    intro hall σ τ hR
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hk, hrest⟩ := hall
    unfold midOk at hk
    split at hk
    · rename_i dsts opn srcs hki
      simp only [notIdx, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hk
      obtain ⟨⟨⟨-, hn1, hn2⟩, hdsts⟩, hsrcs⟩ := hk
      have hren : (renameInstr s d k).li_i
          = .Lopn (dsts.map (renameOperand s d)) opn (srcs.map (renameOperand s d)) := by
        simp only [renameInstr, hki]
      have heval : (srcs.map (renameOperand s d)).map (evalOperand τ)
          = srcs.map (evalOperand σ) := by
        rw [List.map_map]
        exact List.map_congr_left (fun o ho => evalOperand_rename hR hs hd o (hsrcs o ho))
      simp only [List.map_cons, lsemStraight_cons, hki, hren]
      rcases step_rel s d ⟨hn1, hn2⟩ heval with ⟨h1, h2⟩ | ⟨x, v, hdx, h1, h2⟩
      · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
      · rw [h1, h2]
        have hxok : operandOk s d (.reg x) = true := hdsts _ (by rw [hdx]; simp)
        simp only [operandOk, Bool.and_eq_true, Bool.not_eq_true'] at hxok
        exact ih hrest _ _ (hR.step (ne_of_not_mentions_reg hd hxok.1) v)
    · exact absurd hk (by simp)

/-! ## 9. Dead registers -/

/-- Two states agree on memory and on every register other than `r`. -/
def AgreeOff {w : Nat} (r : String) (σ τ : Lstate w) : Prop :=
  σ.lmem = τ.lmem ∧ ∀ x, x ≠ r → σ.lvm x = τ.lvm x

/-- Every register a register name reads is a pool register. -/
theorem nameReads_phys {n x : String} (h : (nameReads n).contains x = true) :
    isPhysGP x = true := by
  unfold nameReads at h
  split at h
  · rename_i hn
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at h
    rw [h]; exact hn
  · split at h
    · split at h
      · rename_i base _ _
        split at h
        · rename_i hb
          simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at h
          rw [h]; exact hb
        · simp at h
      · simp at h
    · simp at h

/-- Every register an operand reads is a pool register. -/
theorem operandReads_phys {o : LOperand} {x : String} (h : (operandReads o).contains x = true) :
    isPhysGP x = true := by
  cases o with
  | reg n => exact nameReads_phys h
  | arrIdx b i _ =>
    simp only [operandReads, List.contains_append, Bool.or_eq_true] at h
    rcases h with h | h
    · split at h
      · rename_i hb
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at h
        rw [h]; exact hb
      · simp at h
    · split at h
      · rename_i hi
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at h
        rw [h]; exact hi
      · simp at h
  | imm _ => simp [operandReads] at h
  | arr _ _ => simp [operandReads] at h

/-- From states agreeing off a pool register `r` that is dead at the head of
    `post`, the runs of `post` reach equal store images. -/
theorem deadAt_store {w : Nat} {r : String} (hr : isPhysGP r = true) :
    ∀ (post : Lcmd), deadAt r post = true → ∀ (σ τ : Lstate w), AgreeOff r σ τ →
      Option.map stateStore (lsemStraight (post.map Linstr.li_i) σ)
        = Option.map stateStore (lsemStraight (post.map Linstr.li_i) τ) := by
  intro post
  induction post with
  | nil => intro h; simp [deadAt] at h
  | cons k rest ih =>
    intro h σ τ hA
    unfold deadAt at h
    split at h
    · rename_i dsts opn srcs hki
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        have hnu := hc.2
        simp only [List.map_cons, lsemStraight_cons, hki]
        have hLive : LiveAgree (physGPs.filter (fun x => x != r)) σ τ := by
          refine ⟨hA.1, fun x hx => hA.2 x ?_⟩
          rintro rfl
          rcases hx with hx | hx
          · rw [hr] at hx; exact absurd hx (by simp)
          · simp at hx
        have hcov : ∀ o ∈ srcs, ∀ x, (operandReads o).contains x = true →
            (physGPs.filter (fun x => x != r)).contains x = true := by
          intro o ho x hx
          have hu := contains_instrUses_of_src (dsts := dsts) (opn := opn) ho hx
          have hxr : x ≠ r := by rintro rfl; rw [hu] at hnu; exact absurd hnu (by simp)
          have hp := operandReads_phys hx
          simp only [isPhysGP] at hp
          simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_filter, bne_iff_ne,
            ne_eq] at hp ⊢
          exact ⟨hp, hxr⟩
        cases hst : lsemStep (.Lopn dsts opn srcs) σ with
        | none =>
          have hi := lsemStep_isSome_indep (.Lopn dsts opn srcs) σ τ
          rw [hst] at hi
          cases htt : lsemStep (.Lopn dsts opn srcs) τ with
          | none => rfl
          | some _ => rw [htt] at hi; exact absurd hi (by simp)
        | some σ₁ =>
          obtain ⟨dst, hdst, hcase⟩ := lsemStep_liveAgree hLive hcov hst
          rcases hcase with ⟨v, hs1, hts⟩ | ⟨t₁, hts, hl1, hl2, hm, hfd⟩
          · rw [hts]
            subst hs1
            by_cases hdr : dst = r
            · subst hdr
              apply lsemStraight_store_congr
              · funext x
                simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
                split
                · rfl
                · rename_i hx; exact hA.2 x hx
              · exact hA.1
            · have hfd : (fullDefsOf dsts opn).contains r = false := by
                rw [hdst]; exact contains_fullDefsOf_false (Ne.symm hdr)
              rw [hfd, Bool.false_or] at h
              refine ih h _ _ ⟨hA.1, fun x hx => ?_⟩
              simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
              split
              · rfl
              · exact hA.2 x hx
          · rw [hts]
            rw [hfd] at h
            simp only [List.contains_nil, Bool.false_or] at h
            exact ih h _ _ ⟨hm, fun x hx => by rw [hl1, hl2]; exact hA.2 x hx⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-! ## 10. Preservation -/

/-- A successful `findDef` splits the window into a range passing `midOk` and a
    definition passing `defOk`. -/
theorem findDef_spec {s d : String} : ∀ {rev m p : Lcmd} {x : Linstr},
    findDef s d rev = some (m, x, p) →
      rev = m ++ x :: p ∧ m.all (midOk s d) = true ∧ defOk s d x = true := by
  intro rev
  induction rev with
  | nil => intro m p x h; simp [findDef] at h
  | cons i rest ih =>
    intro m p x h
    unfold findDef at h
    split at h
    · rename_i hdef
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hdef⟩
    · split at h
      · rename_i hmid
        split at h
        · rename_i m' x' p' hf
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3⟩ := ih hf
          exact ⟨by rw [h1]; rfl, by simp [List.all_cons, hmid, h2], h3⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- **One coalescing rewrite preserves the store.** For a definition `x` of `s`
    passing `defOk`, a range `mid` passing `midOk`, a copy `k` of `s` into `d`
    and a suffix `post` at whose head `s` is dead, retargeting `x` to `d`,
    renaming `s` to `d` in `mid` and dropping `k` leaves the store image of
    `lsemStraight` unchanged on every start state. -/
theorem coalesceSite_stateStore {w : Nat} {s d : String} (x : Linstr) (mid : Lcmd)
    (k : Linstr) (post : Lcmd) (hx : defOk s d x = true) (hmid : mid.all (midOk s d) = true)
    (hk : copyShape k = some (d, s)) (hdead : deadAt s post = true) (st : Lstate w) :
    Option.map stateStore (lsemStraight
        ((retargetDef s d x :: (mid.map (renameInstr s d) ++ post)).map Linstr.li_i) st)
      = Option.map stateStore (lsemStraight ((x :: (mid ++ k :: post)).map Linstr.li_i) st) := by
  obtain ⟨hd, hs, hne, hstep⟩ := copyShape_spec hk
  unfold defOk at hx
  split at hx
  · rename_i x' opn srcs hxi
    simp only [notIdx, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hx
    obtain ⟨⟨⟨⟨⟨rfl, -⟩, hn1, hn2⟩, -⟩, -⟩, -⟩ := hx
    have hret : (retargetDef x' d x).li_i = .Lopn ([LOperand.reg x'].map (renameOperand x' d)) opn srcs := by
      simp only [retargetDef, hxi]
    simp only [List.map_cons, List.map_nil, List.map_append, lsemStraight_cons, hxi, hret]
    rcases step_rel (dsts := [LOperand.reg x']) (srcs := srcs) (srcs' := srcs) (σ := st) (τ := st)
        x' d ⟨hn1, hn2⟩ rfl with ⟨h1, h2⟩ | ⟨x₀, v, hdx, h1, h2⟩
    · simp only [List.map_cons, List.map_nil] at h2
      rw [h1, h2]
    · simp only [List.cons.injEq, LOperand.reg.injEq, and_true] at hdx
      subst hdx
      simp only [List.map_cons, List.map_nil] at h1 h2
      rw [h1, h2]
      dsimp only
      rw [lsemStraight_append, lsemStraight_append]
      have hR : RenRel x' d ((st.setReg x' v).nextPc)
          ((st.setReg (renameName x' d x') v).nextPc) := by
        refine ⟨rfl, ?_, fun r h1 h2 => ?_⟩
        · simp [renameName]
        · simp [renameName, h1, h2]
      rcases mid_sim hs hd mid hmid _ _ hR with ⟨m1, m2⟩ | ⟨σm, τm, m1, m2, hRm⟩
      · rw [m1, m2]; rfl
      · rw [m1, m2]
        simp only [Option.bind_some, lsemStraight_cons, hstep σm]
        symm
        refine deadAt_store hs post hdead _ _ ⟨hRm.1, fun y hy => ?_⟩
        simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
        split
        · rename_i hyd; rw [hyd]; exact hRm.2.1.symm
        · rename_i hyd; exact (hRm.2.2 y hy hyd).symm
  · exact absurd hx (by simp)

/-- **The sweep preserves the store.** `coalesceGo rev post` has the store image
    of `rev.reverse ++ post` on every start state. -/
theorem coalesceGo_stateStore {w : Nat} : ∀ (post rev : Lcmd) (st : Lstate w),
    Option.map stateStore (lsemStraight ((coalesceGo rev post).map Linstr.li_i) st)
      = Option.map stateStore (lsemStraight ((rev.reverse ++ post).map Linstr.li_i) st) := by
  intro post
  induction post with
  | nil => intro rev st; simp [coalesceGo]
  | cons k post ih =>
    intro rev st
    have hpush : Option.map stateStore
          (lsemStraight (((normCopy k :: rev).reverse ++ post).map Linstr.li_i) st)
        = Option.map stateStore (lsemStraight ((rev.reverse ++ k :: post).map Linstr.li_i) st) := by
      rw [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append,
        List.map_append, lsemStraight_append, lsemStraight_append]
      apply store_bind_congr
      intro st'
      simp only [List.map_cons, lsemStraight_cons, normCopy_step]
    rw [coalesceGo]
    split
    · rename_i d s hk
      split
      · rename_i hdead
        split
        · rename_i m x p hf
          rw [ih]
          obtain ⟨hrev, hm, hx⟩ := findDef_spec hf
          subst hrev
          have e1 : (m.map (renameInstr s d) ++ retargetDef s d x :: p).reverse ++ post
              = p.reverse ++ (retargetDef s d x :: (m.reverse.map (renameInstr s d) ++ post)) := by
            simp [List.reverse_append, List.map_reverse]
          have e2 : (m ++ x :: p).reverse ++ k :: post
              = p.reverse ++ (x :: (m.reverse ++ k :: post)) := by
            simp
          rw [e1, e2, List.map_append, List.map_append, lsemStraight_append, lsemStraight_append]
          apply store_bind_congr
          intro st'
          exact coalesceSite_stateStore x m.reverse k post hx (by simpa using hm) hk hdead st'
        · rw [ih]; exact hpush
      · rw [ih]; exact hpush
    · split
      · rename_i hid
        rw [ih]
        simp only [Bool.and_eq_true] at hid
        rw [List.map_append, List.map_append, lsemStraight_append, lsemStraight_append]
        apply store_bind_congr
        intro st'
        obtain ⟨σ', h1, h2, h3⟩ := identity_step hid.1 st'
        simp only [List.map_cons, lsemStraight_cons, h1]
        exact lsemStraight_store_congr _ _ _ h2.symm h3.symm
      · rw [ih]; exact hpush

/-- **The pass preserves the store.** On every body and every start state, the
    coalesced body's `lsemStraight` result has the store image (register map and
    memory) of the input's: both runs are stuck, or both complete with the same
    store. -/
theorem coalesceBody_stateStore {w : Nat} (body : Lcmd) (st : Lstate w) :
    Option.map stateStore (lsemStraight ((coalesceBody body).map Linstr.li_i) st)
      = Option.map stateStore (lsemStraight (body.map Linstr.li_i) st) := by
  simpa [coalesceBody] using coalesceGo_stateStore body [] st

/-- `coalesceBody_stateStore` in the `ArchAgreeOpt` form. -/
theorem coalesceBody_lsem {w : Nat} (body : Lcmd) (st : Lstate w) :
    ArchAgreeOpt (lsemStraight ((coalesceBody body).map Linstr.li_i) st)
      (lsemStraight (body.map Linstr.li_i) st) :=
  (archAgreeOpt_iff_stateStore _ _).mpr (coalesceBody_stateStore body st)

/-- The pass on one `Lfundef` preserves the store of its body. -/
theorem coalesceFundef_stateStore {w : Nat} (f : Lfundef) (st : Lstate w) :
    Option.map stateStore (lsemStraight ((coalesceFundef f).lfd_body.map Linstr.li_i) st)
      = Option.map stateStore (lsemStraight (f.lfd_body.map Linstr.li_i) st) :=
  coalesceBody_stateStore f.lfd_body st

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce
