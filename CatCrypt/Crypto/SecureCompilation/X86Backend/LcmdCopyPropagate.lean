/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-!
# Move propagation + dead-move elimination on the owned-RA `Lcmd`

A conservative pre-render `Lcmd → Lcmd` pass over the owned-RA linear body
(`JasminLprogExport.Lcmd`, the physical-register two-address IR the AT&T
printer `LprogAsmPrinter.renderLcmd` consumes). The front's per-`SLit`
`regConst` + per-statement rebind pattern threads nearly every SSA value
through an extra `MOV dst, src` (reg→reg `movq`): in the FriFold owned `.s`,
~3020 of 7217 instructions are such copies. A per-instruction printer peephole
cannot remove them (dropping a copy needs *liveness* — the destination must be
provably overwritten before any read); this pass is the right site: it runs on
the `Lcmd` where the instruction list is visible, BEFORE rendering.

## Design: straight-line segments only, two phases

Any `Llabel` / `Lgoto` / `Lcond` / `Lcall` / `Lsyscall` / `Ligoto` /
`LstoreLabel` / `Lret` / `Lalign` — and any `Lopn` whose mnemonic is not in
the recognized alphabet below — is a **barrier**. Barriers are never touched,
copy facts are cleared at every barrier, and the liveness scan treats every
register as live across one. Control flow can only enter a segment at its top
(jump targets are `Llabel`s, themselves barriers), so within a segment
execution is strictly linear and no fixpoint/loop analysis is needed.

* **Phase 1 (forward move propagation).** A recognized move
  `Lopn [.reg d] MOV/MOVQ/MOV:64 [src]` with `d` a bare physical GP and `src`
  either a bare physical GP or a small immediate records the fact
  `d ↦ (src, w)` (`w` = 32 or 64, the move's `mnemWidth`). Until `d` or a
  register named in `src` is redefined (or a barrier), any *rewritable* source
  operand `.reg d` is replaced by `src`. Facts chain transitively (the move's
  own source is rewritten first, so `MOV b,a; MOV c,b` yields `c ↦ a` and
  `MOV d,$1; MOV e,d` yields `e ↦ $1`).
* **Phase 2 (backward dead-move elimination).** One right fold computes an
  over-approximate live set (all 15 GPs at every barrier and at the body
  end). A move whose destination is not live — i.e. it is *fully* overwritten
  before any read, within the same segment — is dropped, as is a 64-bit
  self-copy `MOVQ d, d`. `mov` writes no flags, so dropping one never
  perturbs the CF/OF/ZF dataflow of a surrounding compare/carry chain.

## Conservatism (exactly what blocks propagation / deletion)

1. **Bare physical GPs and small immediates only.** A fact's destination is
   one of the 15 RA-pool names `RAX … R15` (never `RSP`); its source is one
   of those names or an immediate `≤ 2³¹ - 1`. Spill (`k.N`), ABI-save
   (`qsave.X`), memory (`mem.<base>.<off>`), sentinel (`__cfflag`, `reg 1`)
   and array operands never participate — a move touching any of them is
   left alone (this keeps the prologue/epilogue qsave stash/restore and every
   ABI boundary MOV byte-identical). The immediate bound is the signed-`imm32`
   field every ALU immediate form encodes: a larger constant is materialised
   into a register by `movabs`, and folding it into an `addq`/`xorq` would be
   a value the instruction cannot carry.
   An immediate fact additionally rewrites a source operand only where an
   immediate operand is legal: the consuming mnemonic is in `isImmFoldable`
   (`MOV`/`MOVQ` and the two-address ALU class
   `ADD`/`SUB`/`AND`/`OR`/`XOR`/`ADC`/`SBB`/`CMP`/`TEST`, at width 32 or 64)
   and the instruction has a single bare-physical-GP destination. The
   register-only forms (`CMOV`cc, `ANDN`, `ZEROEXT`/`TRUNC`, the SIB address
   ops, the variable-count shifts) and the narrow `:16`/`:8` ABI moves keep
   their register sources.
2. **Two-address self-sources are never rewritten.** In the destructive form
   `Lopn [d] OP [d, s]` the first source *is* the destination's old value
   (the printer renders `op s, d`, reading `d`); rewriting it would let
   phase 2 believe `d` is unread. Any source operand equal to the (single)
   destination register is skipped.
3. **Width gate.** An untagged `MOV` is the 32-bit `movl` (zero-extending),
   so its fact only guarantees low-32 agreement: a 32-bit fact rewrites only
   operands of instructions whose effective width is ≤ 32; a 64-bit fact
   (`MOVQ` / `MOV:64`) rewrites at any width. `LOADIDX`/`STOREIDX`/`LEA`
   read at SIB/address width, so their effective width is pinned to 64.
4. **Implicit-register / flag-carrying ops are barriers.** `MULX`/`MULXMEM`
   (implicit `RDX` multiplicand), the ADX family `ADCX`/`ADOX` and the
   phantom carry/high bindings `ADCXHI`/`ADOXHI`/`MULXHI` (whose write
   physically happens at the paired data op, and whose source lists are
   vestigial), `VPACK` (ZMM), and every mnemonic outside the recognized
   alphabet clear all facts and force all-live. `SETC` (explicit full write,
   reads only CF) and `CMOVcc` (explicit self-source) are recognized.

   For the implicit-**register** case this is enforced rather than observed:
   `implicitReads` names the registers a mnemonic reads without listing them
   (only the `MULX` family, reading `RDX`), `isRecognizedOpn` consults it first,
   and `isRecognizedOpn_eq_false_of_implicitReads` closes the loop. `instrUses`
   also carries the implicit reads, so the liveness read set is correct on its
   own terms and a later widening of the alphabet cannot resurrect the hazard.

   The implicit-**flag** case (`ADC`/`SBB` read CF, `SETC` reads CF, `CMOVcc`
   reads the compare flags) is not modelled, and does not need to be. The pass
   does exactly two things to a body: it rewrites a source operand of a
   recognized op to an operand denoting the same word, and it deletes a
   `MOV`/`MOVQ` whose destination is dead. The first keeps the opcode and the
   operand values, so the instruction sets exactly the flags it set before; the
   second removes an instruction that writes no flag. So the flag a later `ADC`
   reads is the flag it read before, and folding an immediate into an
   `adcq`/`sbbq` changes neither its carry-in nor its carry-out.
5. **Memory operands: exact-match never crossed.** Registers named inside
   `mem.<base>.<off>` / `.arrIdx base idx scale` operands are counted as
   *reads* (they are address registers) but never rewritten.
6. **Read-modify-write destinations count as uses.** For every recognized op
   that is not in the write-only-destination class (`MOV`/`MOVQ`, `LOAD`,
   `LOADIDX`, `LEA`, immediate shifts/rotates, `SETC`, 3-source `CMOV`,
   `ZEROEXT`/`TRUNC`, `ANDN`), the destination register is also a use
   (two-address `ADD d, s` reads `d`; `CMP`/`TEST` conservatively too), and
   only write-only destinations of width ≥ 32 (full 64-bit determination via
   `movl`-zero-extension or a 64-bit write) count as *killing* definitions
   for deletion. Narrow (`:16`/`:8`) writes are partial: use + non-killing
   def.
7. **End-of-body and barriers keep everything live**, so ABI result
   registers and callee-saved restores are never victims.

## Preservation argument

On a straight-line segment, phase 1 maintains the invariant: a fact
`d ↦ (src, w)` holds at program point `p` iff a recognized move `MOV_w d, src`
executed at some `p₀ < p` in the same segment, and no instruction in
`(p₀, p)` wrote `d` or the register `src` names (every recognized op writes
registers only through its explicit `.reg` destinations — ops with implicit
register writes are outside the alphabet and barrier the segment). Hence at
`p` the machine satisfies `d = src` (w = 64) or `low32 d = low32 src`
(w = 32, and then `high32 d = 0`). Rewriting a read source operand of
effective width ≤ w therefore reads the *identical value*, so the rewritten
instruction computes the same result and sets the same flags; skipped
positions (self-sources, address registers) keep the rendered text's read set
intact.
Phase 2's live set over-approximates "may be read before being fully
overwritten" forward from each point (all-live at barriers/end; RMW and
partial-write destinations, address registers and all explicit sources are
uses; only ≥32-bit write-only destinations kill). A dropped copy's
destination is thus fully overwritten before any read on every path that
observes it, and `mov` is flag-silent, so the register state at every read of
every register — and the entire flag dataflow — is unchanged. The concrete
demos at the bottom pin the intended firing/non-firing on the real emitted
shapes (`by rfl`, kernel-evaluated); the end-to-end check for a kernel flip
is, as always, the external byte-KAT.

## Ordering with the other post-passes

Run this pass after any structural fuser (`AdxChainFuse.fuseAdxChain`,
`FuseMulHi.fuseMulHiLprog`): those match exact operand patterns
that a rewrite could break (their families are barriers here, so running
after them is also *safe*, merely less effective if run before). The one pass
that consumes this one's output is `LcmdLea.leaLprog`, which folds a
register rebind and a `d += $k` into a `LEA:64` and therefore needs the
immediate this pass folds into the add. Wiring pattern (per-emitter opt-in,
byte-KAT before wider adoption):

```
def kernelAsm : String :=
  renderLprogAtt (LcmdCopyPropagate.copyPropagateLprog kernelLprog)
```
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (mnemWidth stripAbiTag)

/-! ## 1. Register classification -/

/-- The 15 RA-pool physical GP names (`RSP` excluded — never allocated).
    Facts, rewrites and deletions are restricted to these; every other
    operand name (spill `k.N`, `qsave.X`, `mem.*`, sentinels) is opaque. -/
def physGPs : List String :=
  ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP",
   "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"]

/-- Is `n` a bare RA-pool physical GP name? -/
def isPhysGP (n : String) : Bool := physGPs.contains n

/-- The physical GP registers *read as an address* by a register-name string:
    a `mem.<base>.<off>` operand reads its base register; a bare GP name reads
    itself; spill/qsave names are `%rsp`-relative (no pool register read). -/
def nameReads (n : String) : List String :=
  if isPhysGP n then [n]
  else if "mem.".isPrefixOf n then
    match ((n.drop 4).toString).splitOn "." with
    | [base, _] => if isPhysGP base then [base] else []
    | _ => []
  else []

/-- All physical GP registers a source-position operand reads. A SIB
    `arrIdx base idx scale` reads both address registers. -/
def operandReads : LOperand → List String
  | .reg n => nameReads n
  | .arrIdx b i _ =>
      (if isPhysGP b then [b] else []) ++ (if isPhysGP i then [i] else [])
  | _ => []

/-! ## 2. Mnemonic classification -/

/-- The physical GP registers an instruction reads WITHOUT naming them in its
    operand list. The BMI2 `MULX` family (`MULX`, `MULXHI`, `MULXMEM`) reads its
    multiplier from `RDX`, which appears in no `Lopn` source; the prefix test
    matches the whole family, the same key `LprogScheduler.flagFree` and
    `SpillingRegAlloc.mulxMultReg` use.

    Every other mnemonic this backend emits names all of its register inputs.
    The variable-count shifts render as the BMI2 three-operand
    `shlx`/`shrx`/`sarx`, not the `CL` form, so no shift reads `RCX` implicitly;
    and no `DIV`/`IDIV`/`CQO`/`CDQ` mnemonic exists, so the `RDX:RAX` pair is
    never an implicit operand here.

    Implicit FLAG inputs (`ADC`/`SBB` read CF, `SETC` reads CF, `CMOVcc` reads
    the compare flags) are deliberately absent from this list — the flag channel
    is argued separately in the module docstring, and listing them here would
    make every carry chain a barrier for no gain. -/
def implicitReads (opn : String) : List String :=
  if "MULX".isPrefixOf (stripAbiTag opn) then ["RDX"] else []

/-- The recognized (non-barrier) `Lopn` mnemonic alphabet: the exact set whose
    operand read/write behaviour under `renderLopn` is modeled here. Everything
    else — `MULX`/`MULXMEM`/`MULXHI` (implicit `RDX`),
    `ADCX`/`ADOX`/`ADCXHI`/`ADOXHI` (flag-threaded / phantom bindings), `VPACK`,
    unknowns — is a barrier. Immediate shifts/rotates (`SHL:n[:64]` …) are
    recognized via `parseImmShiftMnem` (checked FIRST: the count separator `:`
    collides with the `:8`/`:16`/`:64` width tags, the Hawk `SHR:16` pitfall).

    A mnemonic with an implicit register operand is excluded **by construction**
    (`implicitReads` is consulted first), so the barrier property of the `MULX`
    family is a structural guarantee rather than a coincidence of the listed
    alphabet — `isRecognizedOpn_eq_false_of_implicitReads`. Adding such a
    mnemonic to the list below cannot make it recognized. -/
def isRecognizedOpn (opn : String) : Bool :=
  (implicitReads opn).isEmpty &&
  ((parseImmShiftMnem opn).isSome ||
  (match stripAbiTag opn with
   | "MOV" | "MOVQ" | "LOAD" | "STORE" | "LOADIDX" | "STOREIDX" | "LEA"
   | "ADD" | "SUB" | "MUL" | "AND" | "OR" | "XOR" | "ADC" | "SBB"
   | "SHL" | "SHR" | "SAR" | "CMP" | "TEST" | "ANDN" | "SETC"
   | "CMOVE" | "CMOVNE" | "CMOVB" | "CMOVAE" | "CMOVL" | "CMOVGE"
   | "CMOV" | "ZEROEXT" | "TRUNC" => true
   | _ => false))

/-- A mnemonic with an implicit register operand is never recognized, so phase 1
    clears its facts and phase 2 seeds the all-live set at it. This is what makes
    an implicit read safe without modelling it in `instrUses`. -/
theorem isRecognizedOpn_eq_false_of_implicitReads {opn : String}
    (h : implicitReads opn ≠ []) : isRecognizedOpn opn = false := by
  have he : (implicitReads opn).isEmpty = false := by
    cases hx : implicitReads opn with
    | nil => exact absurd hx h
    | cons _ _ => rfl
  simp only [isRecognizedOpn, he, Bool.false_and]

/-- The `MULX` family carries the implicit `RDX` read, so it is a barrier. -/
theorem isRecognizedOpn_MULX {opn : String}
    (h : "MULX".isPrefixOf (stripAbiTag opn) = true) : isRecognizedOpn opn = false := by
  refine isRecognizedOpn_eq_false_of_implicitReads ?_
  simp [implicitReads, h]

/-- The effective operand width (bits) at which a recognized op reads its
    rewritable register sources. Immediate shifts carry the count in the
    mnemonic (parse first — `mnemWidth` would misread `SHL:16`); the SIB /
    address ops read at 64-bit regardless of the mnemonic tag. -/
def effWidth (opn : String) : Nat :=
  match parseImmShiftMnem opn with
  | some (_, _, w) => w
  | none =>
      match stripAbiTag opn with
      | "LOADIDX" | "STOREIDX" | "LEA" => 64
      | _ => mnemWidth opn

/-- Does this recognized op accept an **immediate** in a rewritable source
    position? The two-address ALU class and the plain moves render an immediate
    operand as `$v` and encode it through the sign-extended `imm32` forms; the
    register-only forms (`CMOV`cc, `ANDN`, `ZEROEXT`/`TRUNC`, the SIB address
    ops `LOAD`/`STORE`/`LOADIDX`/`STOREIDX`/`LEA`, `SETC`, the variable-count
    shifts and the immediate shifts, whose count is carried in the mnemonic) do
    not. The two-source `SET<cc>` comparisons render their second operand as the
    immediate of a `cmp`. The narrow `:16`/`:8` ABI moves are excluded with the
    width gate. -/
def isImmFoldable (opn : String) : Bool :=
  (parseImmShiftMnem opn).isNone
    && (mnemWidth opn == 32 || mnemWidth opn == 64)
    && (match stripAbiTag opn with
        | "MOV" | "MOVQ" | "ADD" | "SUB" | "AND" | "OR" | "XOR"
        | "ADC" | "SBB" | "CMP" | "TEST"
        | "SETE" | "SETNE" | "SETB" | "SETBE" | "SETA" | "SETAE" => true
        | _ => false)

/-- Is the (single) destination of this recognized op **write-only** — i.e.
    the rendered instruction never reads the destination's old value? The
    two-address ALU class (`ADD` … `CMOVcc`) reads its destination
    (`op s, d`), so it is NOT in this class; `CMP`/`TEST` are kept out
    conservatively. The 3-source select `CMOV` fully writes its destination
    (its self-alias cases are explicit source operands). A materialised
    comparison `SET<cc>` is printed `cmp y, x ; mov $0, d ; set<cc> d`: both
    operands are read before `d` is zeroed, so `d` is write-only. -/
def isDstWriteOnly (opn : String) : Bool :=
  match stripAbiTag opn with
  | "STOREIDX" => false
  | m =>
    (parseImmShiftMnem opn).isSome ||
    (match m with
     | "MOV" | "MOVQ" | "LOAD" | "LOADIDX" | "LEA" | "SETC" | "CMOV"
     | "SETE" | "SETNE" | "SETB" | "SETBE" | "SETA" | "SETAE"
     | "ZEROEXT" | "TRUNC" | "ANDN" => true
     | _ => false)

/-- The physical GP registers named as bare-register destinations. -/
def regDefsOf (dsts : List LOperand) : List String :=
  dsts.filterMap fun o =>
    match o with
    | .reg n => if isPhysGP n then some n else none
    | _ => none

/-- A **killing** (full-width) definition: a write-only destination written at
    width ≥ 32 determines all 64 architectural bits (`movl` zero-extends;
    `movq`/`shlq …` write all 64). Narrow (`:16`/`:8`) writes are partial and
    kill nothing. -/
def fullDefsOf (dsts : List LOperand) (opn : String) : List String :=
  if isDstWriteOnly opn && 32 ≤ effWidth opn then regDefsOf dsts else []

/-- Every physical GP an `Lopn dsts opn srcs` may READ: all source reads
    (incl. SIB/mem address registers), address registers of memory-class
    destinations, the destination itself when the op is read-modify-write or its
    write is partial (< 32 bits), and the registers the mnemonic reads without
    naming them (`implicitReads`).

    The implicit component is redundant while every mnemonic carrying one is a
    barrier (`isRecognizedOpn_eq_false_of_implicitReads`), since a barrier seeds
    the all-live set anyway. It is here so that the read set is correct on its
    own terms: a later widening of the recognized alphabet cannot turn an
    unmodelled implicit read into a dropped definition. -/
def instrUses (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    List String :=
  let srcReads := srcs.flatMap operandReads
  let dstAddrReads := dsts.flatMap fun o =>
    match o with
    | .reg n => if isPhysGP n then [] else nameReads n
    | o => operandReads o
  let rmwReads :=
    if isDstWriteOnly opn && 32 ≤ effWidth opn then [] else regDefsOf dsts
  srcReads ++ dstAddrReads ++ rmwReads ++ implicitReads opn

/-! ## 3. The move shape -/

/-- The largest immediate a fact may carry: the signed-`imm32` field the ALU
    immediate forms encode. -/
def immFoldMax : Nat := 2147483647

/-- The source operands a move fact may carry: a bare physical GP, or an
    immediate within the signed-`imm32` field. -/
def isFactSrc : LOperand → Bool
  | .reg s => isPhysGP s
  | .imm v => v ≤ immFoldMax
  | _ => false

/-- Does a fact source name the register `r`? An immediate names none. -/
def factSrcNames (o : LOperand) (r : String) : Bool :=
  match o with
  | .reg n => n == r
  | _ => false

/-- Is this operand an immediate? -/
def isImmOperand : LOperand → Bool
  | .imm _ => true
  | _ => false

/-- Recognise a candidate move `Lopn [.reg d] MOV/MOVQ/MOV:64 [src]`, with `d`
    a bare physical GP, `src` a bare physical GP or a small immediate, and
    width 32 or 64. Returns `(d, src, w)`. Narrow ABI MOVs (`MOV:16`/`MOV:8`,
    partial writes) and any move touching a spill/qsave/mem/sentinel name are
    excluded. -/
def moveShape (i : Linstr) : Option (String × LOperand × Nat) :=
  match i.li_i with
  | .Lopn [.reg d] opn [src] =>
      if (parseImmShiftMnem opn).isNone
          && (stripAbiTag opn == "MOV" || stripAbiTag opn == "MOVQ")
          && isPhysGP d && isFactSrc src then
        let w := mnemWidth opn
        if w == 32 || w == 64 then some (d, src, w) else none
      else none
  | _ => none

/-! ## 4. Phase 1: forward move propagation -/

/-- A move fact `(d, src, w)`: register `d` currently holds the value the
    operand `src` denotes, at width `w` (64 ⇒ full equality; 32 ⇒ low-32
    agreement and `d`'s high half zero). -/
abbrev MoveFact := String × LOperand × Nat

/-- Drop every fact whose destination is `r` or whose source names `r`
    (`r` was redefined). -/
def killFacts (facts : List MoveFact) (r : String) : List MoveFact :=
  facts.filter fun f => f.1 != r && !(factSrcNames f.2.1 r)

/-- Look up the propagation target for register `u`. -/
def lookupFact (facts : List MoveFact) (u : String) : Option (LOperand × Nat) :=
  facts.findSome? fun f => if f.1 == u then some f.2 else none

/-- Rewrite one rewritable source operand: a bare physical GP `u` (not the
    instruction's own destination — the two-address self-source, rule 2) with
    a width-compatible fact `u ↦ (v, fw)` becomes `v`. Width gate (rule 3):
    a 64-bit fact rewrites anywhere; a 32-bit fact only where the consuming
    op's effective width is ≤ 32. An immediate fact additionally needs
    `allowImm` (rule 1: the consuming mnemonic takes an immediate operand and
    writes a bare physical GP). All other operands pass through untouched
    (rule 5: never inside `mem.*`/`arrIdx`). -/
def rewriteOperand (facts : List MoveFact) (w : Nat) (allowImm : Bool)
    (dstSelf : Option String) : LOperand → LOperand
  | .reg u =>
      if isPhysGP u && dstSelf != some u then
        match lookupFact facts u with
        | some (v, fw) =>
            if (fw == 64 || (fw == 32 && w ≤ 32)) && (allowImm || !(isImmOperand v)) then v
            else .reg u
        | none => .reg u
      else .reg u
  | op => op

/-- Forward propagation over one body. Barriers (control flow, unrecognized
    mnemonics) clear all facts and pass through untouched; recognized `Lopn`s
    have their sources rewritten, then kill the facts of every register they
    define, then (if a move) record their — already chained — fact. -/
def propagateAux : List MoveFact → Lcmd → Lcmd
  | _, [] => []
  | facts, i :: rest =>
      match i.li_i with
      | .Lopn dsts opn srcs =>
          if isRecognizedOpn opn then
            let dstSelf : Option String :=
              match dsts with
              | [.reg d] => if isPhysGP d then some d else none
              | _ => none
            let allowImm := isImmFoldable opn && dstSelf.isSome
            let srcs' := srcs.map (rewriteOperand facts (effWidth opn) allowImm dstSelf)
            let i' : Linstr := { i with li_i := .Lopn dsts opn srcs' }
            let facts₁ := (regDefsOf dsts).foldl killFacts facts
            let facts₂ :=
              match moveShape i' with
              | some (d, src, w) =>
                  if src == LOperand.reg d then facts₁ else (d, src, w) :: facts₁
              | none => facts₁
            i' :: propagateAux facts₂ rest
          else
            i :: propagateAux [] rest
      | _ => i :: propagateAux [] rest

/-! ## 5. Phase 2: backward dead-move elimination -/

/-- Add registers to a (duplicate-free, ≤ 15 entry) live set. -/
def addRegs (live : List String) (rs : List String) : List String :=
  rs.foldl (fun l r => if l.contains r then l else r :: l) live

/-- One backward step of the liveness fold. State: `(live, acc)` where `live`
    over-approximates the registers whose current value may still be read
    (forward of this point) and `acc` is the already-processed suffix.

    * A barrier forces all-live (rule 7).
    * A candidate move is dropped iff it is a 64-bit self-copy (`movq d, d`,
      a pure no-op) or its destination is not live; a *kept* move uses its
      source and kills its destination like any other recognized op.
    * Every kept recognized op: `live := (live \ fullDefs) ∪ uses`. -/
def deadElimStep (i : Linstr) : List String × Lcmd → List String × Lcmd
  | (live, acc) =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        if isRecognizedOpn opn then
          let drop :=
            match moveShape i with
            | some (d, src, w) =>
                (w == 64 && src == LOperand.reg d) || !(live.contains d)
            | none => false
          if drop then (live, acc)
          else
            let live' :=
              addRegs (live.filter fun r => !((fullDefsOf dsts opn).contains r))
                (instrUses dsts opn srcs)
            (live', i :: acc)
        else (physGPs, i :: acc)
    | _ => (physGPs, i :: acc)

/-- Backward dead-move elimination over one body (all registers live at the
    body end — ABI results and callee-saved restores are never victims). -/
def deadElimBody (body : Lcmd) : Lcmd :=
  (body.foldr deadElimStep (physGPs, [])).2

/-! ## 6. The pass -/

/-- Move propagation + dead-move elimination on one owned-RA body:
    forward propagation (phase 1), then backward dead-move drop (phase 2).
    Conservative and barrier-segmented — see the module docstring for the
    exact conservatism list and the preservation argument. -/
def copyPropagateBody (body : Lcmd) : Lcmd :=
  deadElimBody (propagateAux [] body)

/-- The pass on one `Lfundef` (body only; ABI metadata untouched). -/
def copyPropagateFundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := copyPropagateBody f.lfd_body }

/-- The pass on a whole `Lprog` (every function body). Emitters opt in
    EXPLICITLY, immediately before `renderLprogAtt`, and AFTER any structural
    fuser (`fuseAdxChain` / `fuseMulHiLprog`) — see the module docstring.
    Every flip must be re-validated by its external byte-KAT. -/
def copyPropagateLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) => (n, copyPropagateFundef f) }

/-- Count the candidate moves in a body (the orchestrator's before/after
    measurement hook). -/
def countMoveCandidates (body : Lcmd) : Nat :=
  (body.filter fun i => (moveShape i).isSome).length

/-- Total candidate moves across an `Lprog`. -/
def countMoveCandidatesLprog (p : Lprog) : Nat :=
  (p.lp_funcs.map fun (_, f) => countMoveCandidates f.lfd_body).foldl (· + ·) 0

/-! ## 7. Firing / non-firing demos (`#guard`, evaluated at elaboration)

Each demo pins one clause of the conservatism list on the exact emitted
shapes (`MOV:64` rebinds, `XOR:64` two-address bodies, `SHL:n:64` immediate
shifts, `STORE:64` to a `mem.*` slot, `Llabel` barriers). `#guard` (not
`by rfl`/`by decide`): the printer helpers this pass reuses go through
`String.splitOn`, which is well-founded-recursive and does not reduce in the
kernel; `#guard` evaluates in the elaborator and fails the build on any
regression, with no axiom cost. -/

-- Structural equality on the instruction AST (`JasminLprogExport` derives
-- only `Repr`); needed to evaluate the demo equalities (the `AdxChainFuse`
-- precedent).
deriving instance DecidableEq for LinstrR
deriving instance DecidableEq for Linstr

/-- Rebind chain (the FriFold front pattern): both copies collapse and the
    consumer reads the chain root. -/
def demoChain : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RBX"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "XOR:64" [.reg "RDX", .reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RDI"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "MOV:64" [.reg "RDI"]⟩ ]

-- **Chain collapse fires:** the two rebind copies are dropped, the `XOR`
-- reads the chain root `RBX`, the two live redefinitions survive.
#guard copyPropagateBody demoChain =
  [ (⟨0, .Lopn [.reg "RDX"] "XOR:64" [.reg "RDX", .reg "RBX"]⟩ : Linstr),
    ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RDI"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "MOV:64" [.reg "RDI"]⟩ ]

/-- An immediate shift is a killing (write-only, full-width) definition: the
    copy into `R8` is dead once `R8` is fully overwritten by `SHL:2:64`. -/
def demoShiftKill : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "R9"]⟩,
    ⟨0, .Lopn [.reg "R10"] "XOR:64" [.reg "R10", .reg "R8"]⟩,
    ⟨0, .Lopn [.reg "R8"] "SHL:2:64" [.reg "R11"]⟩ ]

#guard copyPropagateBody demoShiftKill =
      [ ⟨0, .Lopn [.reg "R10"] "XOR:64" [.reg "R10", .reg "R9"]⟩,
        ⟨0, .Lopn [.reg "R8"] "SHL:2:64" [.reg "R11"]⟩ ]

/-- **Self-source conservatism (rule 2):** the two-address `ADD` reads its
    destination, so the copy feeding it is live and `srcs[0]` is untouched. -/
def demoRmw : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RBX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .reg "RCX"]⟩ ]

#guard copyPropagateBody demoRmw = demoRmw

/-- **Barrier conservatism (rule 4/7):** a label clears facts and forces
    all-live — the copy survives and the cross-label use is not rewritten. -/
def demoBarrier : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RBX"]⟩,
    ⟨0, .Llabel .internal 3⟩,
    ⟨0, .Lopn [.reg "RCX"] "XOR:64" [.reg "RCX", .reg "RAX"]⟩ ]

#guard copyPropagateBody demoBarrier = demoBarrier

/-- **Width gate (rule 3):** an untagged (32-bit) `MOV` fact must not rewrite
    a 64-bit use. -/
def demoWidth : Lcmd :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV" [.reg "RBX"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "XOR:64" [.reg "RCX", .reg "RAX"]⟩ ]

#guard copyPropagateBody demoWidth = demoWidth

/-- **Memory address registers are uses (rule 5):** the `STORE` through
    `mem.RSI.0` reads `RSI`, so the copy into `RSI` is live even though `RSI`
    is later fully redefined. -/
def demoMemAddr : Lcmd :=
  [ ⟨0, .Lopn [.reg "RSI"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "mem.RSI.0"] "STORE:64" [.reg "RBX"]⟩,
    ⟨0, .Lopn [.reg "RSI"] "MOV:64" [.reg "RDX"]⟩ ]

#guard copyPropagateBody demoMemAddr = demoMemAddr

/-- Control for `demoMemAddr`: without the address use, the same copy is
    dead (fully redefined before any read) and drops. -/
def demoMemAddrCtl : Lcmd :=
  [ ⟨0, .Lopn [.reg "RSI"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "RSI"] "MOV:64" [.reg "RDX"]⟩ ]

#guard copyPropagateBody demoMemAddrCtl =
      [ ⟨0, .Lopn [.reg "RSI"] "MOV:64" [.reg "RDX"]⟩ ]

/-- **ADX family is a barrier (rule 4):** nothing around an `ADCX` chain is
    touched (its carry-in source lists and phantom `ADCXHI` bindings must
    stay byte-exact for `AdxChainFuse` and the printer). -/
def demoAdxBarrier : Lcmd :=
  [ ⟨0, .Lopn [.reg "R13"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R13"] "ADCX:64" [.reg "R13", .reg "R8", .reg "R12"]⟩,
    ⟨0, .Lopn [.reg "k.0"] "ADCXHI:64" [.reg "R13", .reg "R8", .reg "R12"]⟩ ]

-- **ADX family is a barrier (rule 4):** the pass is the identity on the whole
-- demo — the `MOV R13, RAX` copy is kept (R13 is live into the `ADCX` barrier),
-- nothing is propagated into the `ADCX`/`ADCXHI` operands, and the phantom
-- `ADCXHI` binding stays byte-exact.
#guard copyPropagateBody demoAdxBarrier = demoAdxBarrier

/-- The front's index-increment shape: a materialised `$1`, a rebind of the
    index, the two-address add, and the rebind of the sum. -/
def demoConstFold : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.imm 1]⟩,
    ⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .reg "RDX"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "R8"]⟩ ]

-- **Constant fold fires:** the immediate reaches the two-address `ADD` and the
-- materialising move is dead (`RDX` is fully overwritten before any read).
#guard copyPropagateBody demoConstFold =
  [ (⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "RAX"]⟩ : Linstr),
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .imm 1]⟩,
    ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "R8"]⟩ ]

/-- A constant chains through a further move and reaches the consumer; both
    materialising moves are dead. -/
def demoConstChain : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.imm 3]⟩,
    ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RDX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "OR:64" [.reg "R8", .reg "R9"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RAX"]⟩ ]

#guard copyPropagateBody demoConstChain =
  [ (⟨0, .Lopn [.reg "R8"] "OR:64" [.reg "R8", .imm 3]⟩ : Linstr),
    ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RAX"]⟩ ]

/-- **Immediate bound (rule 1):** a constant outside the signed-`imm32` field
    records no fact, so the `movabs` that materialises it survives and the
    consumer keeps its register source. -/
def demoWideImm : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] "MOV:64" [.imm 18446744073709551615]⟩,
    ⟨0, .Lopn [.reg "R10"] "XOR:64" [.reg "R10", .reg "R8"]⟩ ]

#guard copyPropagateBody demoWideImm = demoWideImm

/-- **Immediate alphabet (rule 1):** `CMOV`cc has no immediate source form, so
    a constant fact does not reach it. -/
def demoImmAlphabet : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.imm 7]⟩,
    ⟨0, .Lopn [.reg "R8"] "CMOVE:64" [.reg "R8", .reg "RDX"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "RAX"]⟩ ]

#guard copyPropagateBody demoImmAlphabet = demoImmAlphabet

/-- **Width gate on a constant fact (rule 3):** an untagged (32-bit) `MOV`
    immediate does not rewrite a 64-bit use. -/
def demoImmWidth : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDX"] "MOV" [.imm 5]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .reg "RDX"]⟩ ]

#guard copyPropagateBody demoImmWidth = demoImmWidth

/-- **Implicit `RDX` (rule 4):** the `mpn_mul_1` multiply setup. `mulx` reads its
    multiplicand from `RDX`, which no source operand names, so the `MOV` that
    loads it must survive even though nothing later *lists* `RDX`. Transcribed
    from `bench/mpn_mul_1_front_compare/gen_com/mpn_mul_1_rt_owned.s`. -/
def demoMulxRdx : Lcmd :=
  [ ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "RDX"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "RBP"]⟩,
    ⟨0, .Lopn [.reg "k.0"] "MOV:64" [.reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "RCX", .reg "R8"] "MULX:64" [.reg "RSI"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "MOV:64" [.reg "k.0"]⟩ ]

#guard copyPropagateBody demoMulxRdx = demoMulxRdx

/-- The same setup after a scheduler has sunk the `RDX` read below the `mulx`:
    the load of the multiplicand still survives. -/
def demoMulxRdxSunk : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "RBP"]⟩,
    ⟨0, .Lopn [.reg "k.0"] "MOV:64" [.reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "RCX", .reg "R8"] "MULX:64" [.reg "RSI"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "MOV:64" [.reg "k.0"]⟩,
    ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "RDX"]⟩ ]

#guard copyPropagateBody demoMulxRdxSunk = demoMulxRdxSunk

-- The whole `MULX` family is outside the recognized alphabet, by construction.
#guard (implicitReads "MULX:64" == ["RDX"]) && (implicitReads "MULXHI:64" == ["RDX"])
  && (implicitReads "MULXMEM:64" == ["RDX"]) && (implicitReads "ADD:64" == [])
#guard !(isRecognizedOpn "MULX:64") && !(isRecognizedOpn "MULXHI:64")
  && !(isRecognizedOpn "MULXMEM:64")

/-! ## 8. Instruction-shape invariants

The part of an instruction the pass never rewrites: its position tag, an
`Lopn`'s destination list and mnemonic, and a non-`Lopn` instruction in full.
Phase 1 preserves this shape at every position and phase 2 deletes whole
instructions, so every output mnemonic is an input mnemonic — the property that
keeps a `MOV:64` from being emitted as a zero-extending 32-bit `MOV`. -/

/-- The position tag, an `Lopn`'s destinations and mnemonic, and a non-`Lopn`
    instruction in full. Source operands are excluded. -/
def instrShape (i : Linstr) : Nat × Option (List LOperand × String) × Option LinstrR :=
  (i.li_ii,
   (match i.li_i with | .Lopn dsts opn _ => some (dsts, opn) | _ => none),
   (match i.li_i with | .Lopn _ _ _ => none | c => some c))

/-- The mnemonic of an `Lopn`; `none` for a control-flow instruction. -/
def instrMnem (i : Linstr) : Option String :=
  match i.li_i with
  | .Lopn _ opn _ => some opn
  | _ => none

/-- The mnemonic is a projection of `instrShape`. -/
theorem instrMnem_of_shape (i : Linstr) :
    instrMnem i = (instrShape i).2.1.map Prod.snd := by
  cases hi : i.li_i <;> simp [instrMnem, instrShape, hi]

/-- Phase 1 rewrites only source operands: at every position the output
    instruction carries the input's position tag, destination list and
    mnemonic. -/
theorem propagateAux_shape (facts : List MoveFact) (body : Lcmd) :
    (propagateAux facts body).map instrShape = body.map instrShape := by
  induction body generalizing facts with
  | nil => rfl
  | cons i rest ih =>
    rw [propagateAux]
    split
    · rename_i dsts opn srcs hi
      split
      · simp only [List.map_cons, ih]
        congr 1
        simp only [instrShape, hi]
      · simp only [List.map_cons, ih]
    · simp only [List.map_cons, ih]

/-! ## 9. Semantics: the linear machine `JasminLsem.lsemStraight`

`JasminLsem.lsemStep` evaluates an `Lopn [.reg dst] opn srcs` by reading the
sources out of the store, applying `applyOpn` to the width-tag-stripped
mnemonic, writing `dst` and advancing the pc; `applyOpn "MOV" [a] = some a` and
`applyOpn "MOVQ" [a] = some a` are the reg→reg copy this pass recognises. The
store is uniform-width (`lvm : String → BitVec w`), so the model pins the value
a rewritten operand reads and does not distinguish the `:64` from the `:32`
operand width; the width axis is carried by §8. -/

/-- The only single-source opcodes `applyOpn` models are the copies `MOV` and
    `MOVQ`, so a successful application of one of them returns its argument. -/
theorem applyOpn_singleton {w : Nat} {mn : String} {a v : BitVec w}
    (hmov : mn = "MOV" ∨ mn = "MOVQ") (h : applyOpn mn [a] = some v) : v = a := by
  rcases hmov with rfl | rfl <;> (simp only [applyOpn] at h; exact (Option.some.inj h).symm)

/-- Reducer for a bare-register destination and a non-runtime-indexed opcode:
    `lsemStep` collapses to the word-op arm (`applyOpn` on the evaluated sources)
    for **any** source list, `.arrIdx`-headed or not, once the opcode is neither
    of the two runtime-indexed memory opcodes. An `.arrIdx`-headed source under
    such an opcode falls through the memory arm to the same word-op path. -/
theorem lsemStep_reg_nonmem {w : Nat} (dst opn : String) (srcs : List LOperand)
    (s : Lstate w) (hnm : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX") :
    lsemStep (.Lopn [LOperand.reg dst] opn srcs) s
      = match applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) with
        | some v => some ((s.setReg dst v).nextPc)
        | none => none := by
  by_cases harr : ∃ base idx scale rest,
      srcs = LOperand.arrIdx base idx scale :: rest
  · obtain ⟨base, idx, scale, rest, rfl⟩ := harr
    simp only [lsemStep]
    rw [ite_eq_right hnm.1, ite_eq_right hnm.2]
    rfl
  · exact lsemStep_reg_srcs dst opn srcs s
      (fun base idx scale rest heq => harr ⟨base, idx, scale, rest, heq⟩)

/-- A successful non-runtime-indexed `Lopn` step has exactly one bare-register
    destination, its `applyOpn` succeeded on the evaluated sources, and it wrote
    that register and advanced the pc. The `LOADIDX`/`STOREIDX` runtime-indexed
    memory opcodes are excluded (they are a register load and a memory write with
    a different step shape). -/
theorem lsemStep_Lopn_inv {w : Nat} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {s s₁ : Lstate w}
    (hnm : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX")
    (h : lsemStep (.Lopn dsts opn srcs) s = some s₁) :
    ∃ dst v, dsts = [LOperand.reg dst]
      ∧ applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) = some v
      ∧ s₁ = (s.setReg dst v).nextPc := by
  cases dsts with
  | nil => simp [lsemStep] at h
  | cons d ds =>
    cases ds with
    | cons _ _ => simp [lsemStep] at h
    | nil =>
      cases d with
      | reg dst =>
        rw [lsemStep_reg_nonmem dst opn srcs s hnm] at h
        cases hv : applyOpn (w := w) (stripWidthTag opn) (srcs.map (evalOperand s)) with
        | none => rw [hv] at h; simp at h
        | some v => rw [hv] at h; exact ⟨dst, v, rfl, rfl, (Option.some.inj h).symm⟩
      | imm _ => simp [lsemStep] at h
      | arr _ _ => simp [lsemStep] at h
      | arrIdx _ _ _ => simp [lsemStep] at h

/-- `rewriteOperand` fixes an `.arrIdx` operand: register-indexed sources are
    never rewritten (only bare registers are). -/
theorem rewriteOperand_arrIdx (facts : List MoveFact) (ew : Nat) (ai : Bool)
    (dstSelf : Option String) (base idx : String) (scale : Nat) :
    rewriteOperand facts ew ai dstSelf (LOperand.arrIdx base idx scale)
      = LOperand.arrIdx base idx scale := rfl

/-- The phase-1 invariant: every fact names a physical GP holding, in `s`, the
    word its recorded source operand denotes. -/
def FactsOk {w : Nat} (facts : List MoveFact) (s : Lstate w) : Prop :=
  ∀ f ∈ facts, isPhysGP f.1 = true ∧ isFactSrc f.2.1 = true
    ∧ s.lvm f.1 = evalOperand s f.2.1

/-- A successful lookup comes from a fact in the list. -/
theorem lookupFact_mem {facts : List MoveFact} {u : String} {v : LOperand} {fw : Nat}
    (h : lookupFact facts u = some (v, fw)) : (u, v, fw) ∈ facts := by
  induction facts with
  | nil => exact absurd h (by simp [lookupFact])
  | cons f rest ih =>
    unfold lookupFact List.findSome? at h
    split at h
    · rename_i b hb
      split at hb
      · rename_i hu
        have hb2 : f.2 = b := Option.some.inj hb
        have hv : b = (v, fw) := Option.some.inj h
        have hf : f = (u, v, fw) := by
          obtain ⟨f1, f2⟩ := f
          simp_all
        exact hf ▸ List.mem_cons_self
      · exact absurd hb (by simp)
    · exact List.mem_cons_of_mem _ (ih h)

/-- A surviving fact was already a fact and mentions neither side of the kill. -/
theorem mem_killFacts {facts : List MoveFact} {r : String} {f : MoveFact}
    (h : f ∈ killFacts facts r) :
    f ∈ facts ∧ f.1 ≠ r ∧ factSrcNames f.2.1 r = false := by
  unfold killFacts at h
  obtain ⟨hm, hp⟩ := List.mem_filter.mp h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hp
  exact ⟨hm, hp.1, hp.2⟩

/-- A fact source naming a physical GP never names a non-pool register. -/
theorem factSrcNames_of_isFactSrc {o : LOperand} {r : String}
    (hok : isFactSrc o = true) (hr : isPhysGP r = false) : factSrcNames o r = false := by
  cases o with
  | reg n =>
    have hn : isPhysGP n = true := hok
    simp only [factSrcNames, beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he, hr] at hn
    exact absurd hn (by simp)
  | imm _ => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

/-- A fact source distinct from `.reg d` does not name `d`. -/
theorem factSrcNames_of_ne {o : LOperand} {d : String}
    (h : (o == LOperand.reg d) = false) : factSrcNames o d = false := by
  cases o with
  | reg n =>
    simp only [factSrcNames, beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he] at h
    simp at h
  | imm _ => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

/-- A fact source that does not name `r` denotes the same word after `r` is
    written. -/
theorem evalOperand_setReg_of_not_names {w : Nat} {s : Lstate w} {r : String}
    {v : BitVec w} {o : LOperand} (hok : isFactSrc o = true)
    (h : factSrcNames o r = false) :
    evalOperand ((s.setReg r v).nextPc) o = evalOperand s o := by
  cases o with
  | reg n =>
    have hn : n ≠ r := by simpa [factSrcNames] using h
    simp only [evalOperand, Lstate.lvm_nextPc, Lstate.lvm_setReg]
    rw [ite_eq_right hn]
  | imm _ => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => exact absurd hok (by simp [isFactSrc])

/-- The register definitions of a single bare-register destination. -/
theorem regDefsOf_singleton (dst : String) :
    regDefsOf [LOperand.reg dst] = if isPhysGP dst then [dst] else [] := by
  unfold regDefsOf
  by_cases h : isPhysGP dst = true <;> simp [h]

/-- Under a valid fact set, rewriting an operand does not change the word it
    evaluates to. -/
theorem evalOperand_rewriteOperand {w : Nat} {facts : List MoveFact} {s : Lstate w}
    (hok : FactsOk facts s) (ew : Nat) (ai : Bool) (dstSelf : Option String)
    (op : LOperand) :
    evalOperand s (rewriteOperand facts ew ai dstSelf op) = evalOperand s op := by
  cases op with
  | reg u =>
    simp only [rewriteOperand]
    split
    · split
      · rename_i v fw hp
        split
        · simp only [evalOperand]
          exact (hok _ (lookupFact_mem hp)).2.2.symm
        · rfl
      · rfl
    · rfl
  | imm _ => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

/-- The rewritten source list evaluates to the original words. -/
theorem map_evalOperand_rewrite {w : Nat} {facts : List MoveFact} {s : Lstate w}
    (hok : FactsOk facts s) (ew : Nat) (ai : Bool) (dstSelf : Option String)
    (srcs : List LOperand) :
    (srcs.map (rewriteOperand facts ew ai dstSelf)).map (evalOperand s)
      = srcs.map (evalOperand s) := by
  induction srcs with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons, evalOperand_rewriteOperand hok, ih]

/-- `rewriteOperand` never produces an `.arrIdx` from a non-`.arrIdx` operand: a
    bare register is replaced only by a fact source (a register or immediate,
    never `.arrIdx`, by `FactsOk`), and every other operand passes through. -/
theorem rewriteOperand_ne_arrIdx {w : Nat} {facts : List MoveFact} {s : Lstate w}
    (hok : FactsOk facts s) (ew : Nat) (ai : Bool) (dstSelf : Option String)
    {o : LOperand} (h : ∀ base idx scale, o ≠ LOperand.arrIdx base idx scale) :
    ∀ base idx scale,
      rewriteOperand facts ew ai dstSelf o ≠ LOperand.arrIdx base idx scale := by
  intro base idx scale
  cases o with
  | reg u =>
    simp only [rewriteOperand]
    split
    · split
      · rename_i v fw hp
        split
        · have hfs : isFactSrc v = true := (hok _ (lookupFact_mem hp)).2.1
          cases v with
          | arrIdx _ _ _ => simp [isFactSrc] at hfs
          | reg _ => exact fun he => LOperand.noConfusion he
          | imm _ => exact fun he => LOperand.noConfusion he
          | arr _ _ => exact fun he => LOperand.noConfusion he
        · exact fun he => LOperand.noConfusion he
      · exact fun he => LOperand.noConfusion he
    · exact fun he => LOperand.noConfusion he
  | imm _ => exact fun he => LOperand.noConfusion he
  | arr _ _ => exact fun he => LOperand.noConfusion he
  | arrIdx b i sc => exact absurd rfl (h b i sc)

/-- Killing the facts of a written register restores the invariant in the state
    after the write. -/
theorem FactsOk_write {w : Nat} {facts : List MoveFact} {s : Lstate w}
    {dst : String} {v : BitVec w} (hok : FactsOk facts s) :
    FactsOk ((regDefsOf [LOperand.reg dst]).foldl killFacts facts)
      ((s.setReg dst v).nextPc) := by
  rw [regDefsOf_singleton]
  by_cases hp : isPhysGP dst = true
  · rw [ite_eq_left hp]
    simp only [List.foldl_cons, List.foldl_nil]
    intro f hf
    obtain ⟨hm, h1, h2⟩ := mem_killFacts hf
    obtain ⟨p1, p2, p3⟩ := hok f hm
    refine ⟨p1, p2, ?_⟩
    rw [evalOperand_setReg_of_not_names p2 h2]
    simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
    rw [ite_eq_right h1]
    exact p3
  · rw [ite_eq_right hp]
    simp only [List.foldl_nil]
    intro f hf
    obtain ⟨p1, p2, p3⟩ := hok f hf
    refine ⟨p1, p2, ?_⟩
    have h1 : f.1 ≠ dst := fun he => hp (he ▸ p1)
    have h2 : factSrcNames f.2.1 dst = false :=
      factSrcNames_of_isFactSrc p2 (by simpa using hp)
    rw [evalOperand_setReg_of_not_names p2 h2]
    simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
    rw [ite_eq_right h1]
    exact p3

/-- Recording a true move fact preserves the invariant. -/
theorem FactsOk_cons {w : Nat} {facts : List MoveFact} {s : Lstate w}
    {d : String} {src : LOperand} {fw : Nat} (hok : FactsOk facts s)
    (hd : isPhysGP d = true) (hs : isFactSrc src = true)
    (h : s.lvm d = evalOperand s src) :
    FactsOk ((d, src, fw) :: facts) s := by
  intro f hf
  rcases List.mem_cons.mp hf with he | hm
  · exact he ▸ ⟨hd, hs, h⟩
  · exact hok f hm

/-- A fact source (a register or immediate) evaluates identically in two states
    with the same register map. -/
theorem evalOperand_lvm_eq {w : Nat} {s s₁ : Lstate w} (hlvm : s₁.lvm = s.lvm)
    {o : LOperand} (ho : isFactSrc o = true) :
    evalOperand s₁ o = evalOperand s o := by
  cases o with
  | reg r => simp only [evalOperand, hlvm]
  | imm v => rfl
  | arr _ _ => simp [isFactSrc] at ho
  | arrIdx _ _ _ => simp [isFactSrc] at ho

/-- `FactsOk` depends on the state only through the register map: a step leaving
    `lvm` unchanged (a pure memory write) preserves every fact, so the
    killed-fact subset still holds afterwards. -/
theorem FactsOk_lvm_eq {w : Nat} {facts : List MoveFact} {s s₁ : Lstate w}
    (hok : FactsOk facts s) (hlvm : s₁.lvm = s.lvm) (dst : String) :
    FactsOk ((regDefsOf [LOperand.reg dst]).foldl killFacts facts) s₁ := by
  have hsub : FactsOk facts s₁ := by
    intro f hf
    obtain ⟨p1, p2, p3⟩ := hok f hf
    refine ⟨p1, p2, ?_⟩
    rw [hlvm, evalOperand_lvm_eq hlvm p2]; exact p3
  rw [regDefsOf_singleton]
  by_cases hp : isPhysGP dst = true
  · rw [ite_eq_left hp]; simp only [List.foldl_cons, List.foldl_nil]
    intro f hf; exact hsub f (mem_killFacts hf).1
  · rw [ite_eq_right hp]; simp only [List.foldl_nil]; exact hsub

/-- The runtime-indexed opcode names carry no width tag, so `stripWidthTag`
    leaves them unchanged and `applyOpn` — which models neither — returns `none`
    on every argument list. -/
theorem applyOpn_LOADIDX {w : Nat} (l : List (BitVec w)) :
    applyOpn (stripWidthTag "LOADIDX") l = none := by
  rw [show stripWidthTag "LOADIDX" = "LOADIDX" from by decide +kernel]; rfl

theorem applyOpn_STOREIDX {w : Nat} (l : List (BitVec w)) :
    applyOpn (stripWidthTag "STOREIDX") l = none := by
  rw [show stripWidthTag "STOREIDX" = "STOREIDX" from by decide +kernel]; rfl

/-- A runtime-indexed memory step (`LOADIDX`/`STOREIDX`) preserves the fact set:
    `LOADIDX` writes a register, so killing its facts restores the invariant;
    `STOREIDX` leaves the register map unchanged, so every fact survives. -/
theorem FactsOk_mem_step {w : Nat} {facts : List MoveFact} {s s₁ : Lstate w}
    (hok : FactsOk facts s) {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} (hmem : opn = "LOADIDX" ∨ opn = "STOREIDX")
    (hstep : lsemStep (.Lopn dsts opn srcs) s = some s₁) :
    FactsOk ((regDefsOf dsts).foldl killFacts facts) s₁ := by
  cases dsts with
  | nil => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
  | cons d ds =>
    cases ds with
    | cons _ _ => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
    | nil =>
      cases d with
      | imm _ => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
      | arr _ _ => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
      | arrIdx _ _ _ => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
      | reg dst =>
        by_cases harr : ∃ base idx scale rest,
            srcs = LOperand.arrIdx base idx scale :: rest
        · obtain ⟨base, idx, scale, rest, rfl⟩ := harr
          rcases hmem with rfl | rfl
          · simp only [lsemStep, reduceIte] at hstep
            have hs : s₁ = (s.setReg dst
                (s.lmem base (Int.ofNat (scale * (s.lvm idx).toNat)))).nextPc :=
              (Option.some.inj hstep).symm
            rw [hs]; exact FactsOk_write hok
          · cases rest with
            | nil => simp [lsemStep] at hstep
            | cons val vs =>
              cases vs with
              | cons _ _ => simp [lsemStep] at hstep
              | nil =>
                simp only [lsemStep,
                  ite_eq_right (show ("STOREIDX" : String) ≠ "LOADIDX" from by decide),
                  reduceIte] at hstep
                have hlvm : s₁.lvm = s.lvm := by
                  rw [← Option.some.inj hstep]; simp [Lstate.lvm_nextPc]
                exact FactsOk_lvm_eq hok hlvm dst
        · have hna : ∀ base idx scale rest,
              srcs ≠ LOperand.arrIdx base idx scale :: rest :=
            fun base idx scale rest h => harr ⟨base, idx, scale, rest, h⟩
          rw [lsemStep_reg_srcs dst opn srcs s hna] at hstep
          rcases hmem with rfl | rfl
          · rw [applyOpn_LOADIDX] at hstep; simp at hstep
          · rw [applyOpn_STOREIDX] at hstep; simp at hstep

/-- Two suffixes of one list with equal length are equal. -/
theorem suffix_eq_of_length {α : Type} {l₁ l₂ L : List α} (h₁ : l₁ <:+ L) (h₂ : l₂ <:+ L)
    (hl : l₁.length = l₂.length) : l₁ = l₂ := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  have heq : t₁ ++ l₁ = t₂ ++ l₂ := ht₁.trans ht₂.symm
  have hlen : t₁.length = t₂.length := by
    have hc := congrArg List.length heq
    simp only [List.length_append, hl] at hc; omega
  exact (List.append_inj heq hlen).2

/-- A mnemonic carrying the narrow `:16` width tag does not also carry `:64`. -/
theorem endsWith_16_not_64 (s : String) (h : hasSuffix s ":16" = true) :
    hasSuffix s ":64" = false := by
  unfold hasSuffix at h ⊢
  rw [List.isSuffixOf_iff_suffix] at h
  rw [Bool.eq_false_iff, ne_eq, List.isSuffixOf_iff_suffix]
  intro h64; exact absurd (suffix_eq_of_length h h64 (by decide)) (by decide)

/-- A mnemonic carrying the narrow `:8` width tag does not also carry `:64`. -/
theorem endsWith_8_not_64 (s : String) (h : hasSuffix s ":8" = true) :
    hasSuffix s ":64" = false := by
  unfold hasSuffix at h ⊢
  rw [List.isSuffixOf_iff_suffix] at h
  rw [Bool.eq_false_iff, ne_eq, List.isSuffixOf_iff_suffix]
  intro h64
  obtain ⟨t₁, ht₁⟩ := h
  obtain ⟨t₂, ht₂⟩ := h64
  have heq : t₁ ++ ":8".toList = t₂ ++ ":64".toList := ht₁.trans ht₂.symm
  have hr := congrArg List.reverse heq
  simp only [List.reverse_append] at hr
  rw [show (":8".toList).reverse = ['8', ':'] from by decide,
      show (":64".toList).reverse = ['4', '6', ':'] from by decide] at hr
  simp only [List.cons_append] at hr
  exact absurd (List.head_eq_of_cons_eq hr) (by decide)

/-- A recognised move's width gate forces its base opcode into `{MOV, MOVQ}`.
    `moveShape` checks `stripAbiTag opn ∈ {MOV, MOVQ}` and `mnemWidth opn ∈
    {32, 64}`; the base `stripWidthTag opn` that `applyOpn` reads is then one of
    the two copy opcodes, because the width gate excludes the narrow `:16`/`:8`
    tags on which `stripAbiTag` and `stripWidthTag` differ. -/
theorem stripWidthTag_mov_of_moveShape (opn : String)
    (hmn : (stripAbiTag opn == "MOV" || stripAbiTag opn == "MOVQ") = true)
    (hw : (mnemWidth opn == 32 || mnemWidth opn == 64) = true) :
    stripWidthTag opn = "MOV" ∨ stripWidthTag opn = "MOVQ" := by
  by_cases e16 : hasSuffix opn ":16" = true
  · exfalso
    have e64 := endsWith_16_not_64 opn e16
    have hq : opn ≠ "MOVQ" := by
      rintro rfl
      rw [show (hasSuffix "MOVQ" ":16") = false from by decide +kernel] at e16
      exact absurd e16 (by simp)
    have hmw : mnemWidth opn = 16 := by unfold mnemWidth; simp [e64, e16, hq]
    rw [hmw] at hw; simp at hw
  · by_cases e8 : hasSuffix opn ":8" = true
    · exfalso
      have e64 := endsWith_8_not_64 opn e8
      have hq : opn ≠ "MOVQ" := by
        rintro rfl
        rw [show (hasSuffix "MOVQ" ":8") = false from by decide +kernel] at e8
        exact absurd e8 (by simp)
      have e16f : hasSuffix opn ":16" = false := by simpa using e16
      have hmw : mnemWidth opn = 8 := by unfold mnemWidth; simp [e64, e8, e16f, hq]
      rw [hmw] at hw; simp at hw
    · simp only [Bool.not_eq_true] at e16 e8
      have heq : stripAbiTag opn = stripWidthTag opn := by unfold stripAbiTag; simp [e16, e8]
      rw [heq] at hmn
      rcases (Bool.or_eq_true _ _).mp hmn with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)

/-- A recognised move is an `Lopn` with one bare-GP destination and one
    fact-eligible source, whose stripped base opcode is a `MOV`/`MOVQ` copy. -/
theorem moveShape_inv {i : Linstr} {d : String} {src : LOperand} {ww : Nat}
    (h : moveShape i = some (d, src, ww)) :
    ∃ opn, i.li_i = .Lopn [LOperand.reg d] opn [src]
      ∧ isPhysGP d = true ∧ isFactSrc src = true
      ∧ (stripWidthTag opn = "MOV" ∨ stripWidthTag opn = "MOVQ") := by
  unfold moveShape at h
  split at h
  · rename_i d' opn' s' hi
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      have h' : (if (mnemWidth opn' == 32 || mnemWidth opn' == 64) = true
          then some (d', s', mnemWidth opn') else none) = some (d, src, ww) := h
      split at h'
      · rename_i hw
        have he := Option.some.inj h'
        refine ⟨opn', ?_, ?_, ?_, ?_⟩
        · rw [hi]
          simp_all
        · simp_all
        · simp_all
        · exact stripWidthTag_mov_of_moveShape opn' hc.1.1.2 hw
      · exact absurd h' (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Rewriting the sources of a recognised op leaves the step unchanged. On a
    register-indexed (`.arrIdx`-headed) source the head is preserved verbatim and
    the trailing operands evaluate to the same words, so the memory arms agree;
    on any other source list the word-op arm reads the same evaluated words. -/
theorem lsemStep_rewrite_eq {w : Nat} {facts : List MoveFact} {s : Lstate w}
    (hok : FactsOk facts s) (dsts : List LOperand) (opn : String) (srcs : List LOperand)
    (ew : Nat) (ai : Bool) (dstSelf : Option String) :
    lsemStep (.Lopn dsts opn (srcs.map (rewriteOperand facts ew ai dstSelf))) s
      = lsemStep (.Lopn dsts opn srcs) s := by
  cases dsts with
  | nil => rfl
  | cons d ds =>
    cases ds with
    | cons _ _ => cases d <;> rfl
    | nil =>
      cases d with
      | imm _ => rfl
      | arr _ _ => rfl
      | arrIdx _ _ _ => rfl
      | reg dst =>
        by_cases harr : ∃ base idx scale rest,
            srcs = LOperand.arrIdx base idx scale :: rest
        · obtain ⟨base, idx, scale, rest, rfl⟩ := harr
          simp only [List.map_cons, rewriteOperand_arrIdx, lsemStep]
          by_cases hl : opn = "LOADIDX"
          · simp [hl]
          · by_cases hst : opn = "STOREIDX"
            · simp only [ite_eq_right hl, ite_eq_left hst]
              cases rest with
              | nil => simp
              | cons val vs =>
                cases vs with
                | nil =>
                  simp only [List.map_cons, List.map_nil]
                  rw [evalOperand_rewriteOperand hok]
                | cons _ _ => simp
            · simp only [ite_eq_right hl, ite_eq_right hst, map_evalOperand_rewrite hok]
        · have hna : ∀ base idx scale rest,
              srcs ≠ LOperand.arrIdx base idx scale :: rest :=
            fun base idx scale rest heq => harr ⟨base, idx, scale, rest, heq⟩
          have hna' : ∀ base idx scale rest,
              srcs.map (rewriteOperand facts ew ai dstSelf)
                ≠ LOperand.arrIdx base idx scale :: rest := by
            cases srcs with
            | nil => intro base idx scale rest heq; simp at heq
            | cons o os =>
              intro base idx scale rest heq
              simp only [List.map_cons, List.cons.injEq] at heq
              exact rewriteOperand_ne_arrIdx hok ew ai dstSelf
                (fun b i sc hh => hna b i sc os (by rw [hh])) base idx scale heq.1
          rw [lsemStep_reg_srcs dst opn _ s hna',
              lsemStep_reg_srcs dst opn srcs s hna,
              map_evalOperand_rewrite hok]

/-- `moveShape` never recognises a runtime-indexed memory opcode as a move: the
    move gate requires `stripAbiTag opn ∈ {MOV, MOVQ}`, which `LOADIDX`/`STOREIDX`
    fail. -/
theorem moveShape_none_of_mem {i' : Linstr} {dsts : List LOperand} {opn : String}
    {srcs' : List LOperand} (hi' : i'.li_i = .Lopn dsts opn srcs')
    (hmem : opn = "LOADIDX" ∨ opn = "STOREIDX") :
    moveShape i' = none := by
  unfold moveShape
  rw [hi']
  split
  · rename_i d opn' src heq
    obtain ⟨_, hopn, _⟩ := LinstrR.Lopn.inj heq
    subst hopn
    rcases hmem with rfl | rfl <;>
      simp only [show (stripAbiTag "LOADIDX" == "MOV"
                    || stripAbiTag "LOADIDX" == "MOVQ") = false from by decide +kernel,
                 show (stripAbiTag "STOREIDX" == "MOV"
                    || stripAbiTag "STOREIDX" == "MOVQ") = false from by decide +kernel,
                 Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false]
  · rfl

/-- The fact set `propagateAux` carries past a recognised op is valid in the
    state that op steps to. -/
theorem FactsOk_step {w : Nat} {facts : List MoveFact} {s s₁ : Lstate w}
    (hok : FactsOk facts s) {i' : Linstr} {dsts : List LOperand} {opn : String}
    {srcs' : List LOperand} (hi' : i'.li_i = .Lopn dsts opn srcs')
    (hstep : lsemStep i'.li_i s = some s₁) :
    FactsOk (match moveShape i' with
             | some (d, src, ww) =>
                 if src == LOperand.reg d then (regDefsOf dsts).foldl killFacts facts
                 else (d, src, ww) :: (regDefsOf dsts).foldl killFacts facts
             | none => (regDefsOf dsts).foldl killFacts facts) s₁ := by
  rw [hi'] at hstep
  by_cases hmem : opn = "LOADIDX" ∨ opn = "STOREIDX"
  · rw [moveShape_none_of_mem hi' hmem]
    exact FactsOk_mem_step hok hmem hstep
  have hnm : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" :=
    ⟨fun h => hmem (Or.inl h), fun h => hmem (Or.inr h)⟩
  obtain ⟨dst, v, hdsts, happ, hs₁⟩ := lsemStep_Lopn_inv hnm hstep
  have hf1 : FactsOk ((regDefsOf dsts).foldl killFacts facts) s₁ := by
    rw [hdsts, hs₁]; exact FactsOk_write hok
  cases hcs : moveShape i' with
  | none => exact hf1
  | some p =>
    obtain ⟨d, q⟩ := p
    obtain ⟨src, ww⟩ := q
    obtain ⟨opn2, hi2, hd, hsr, hmov2⟩ := moveShape_inv hcs
    rw [hi'] at hi2
    have hdsts2 : dsts = [LOperand.reg d] := by injection hi2
    have hsrcs2 : srcs' = [src] := by injection hi2 with _ _ h3
    show FactsOk (if (src == LOperand.reg d) = true
                  then (regDefsOf dsts).foldl killFacts facts
                  else (d, src, ww) :: (regDefsOf dsts).foldl killFacts facts) s₁
    by_cases hds : (src == LOperand.reg d) = true
    · rw [ite_eq_left hds]; exact hf1
    · rw [ite_eq_right hds]
      refine FactsOk_cons hf1 hd hsr ?_
      have hnames : factSrcNames src d = false :=
        factSrcNames_of_ne (by simpa using hds)
      have hdd : dst = d := by
        rw [hdsts2] at hdsts
        injection hdsts with h1 _
        injection h1 with h2
        exact h2.symm
      have hv : v = evalOperand s src := by
        rw [hsrcs2] at happ
        simp only [List.map_cons, List.map_nil] at happ
        have hoo : opn = opn2 := by injection hi2
        have hmovA : stripWidthTag opn = "MOV" ∨ stripWidthTag opn = "MOVQ" := by
          rw [hoo]; exact hmov2
        exact applyOpn_singleton hmovA happ
      subst hdd
      rw [hs₁, evalOperand_setReg_of_not_names hsr hnames]
      show ((s.setReg dst v).nextPc).lvm dst = evalOperand s src
      simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
      exact hv

/-- **Phase 1 preserves the machine state exactly.** Under a valid fact set,
    forward propagation leaves `lsemStraight` unchanged on every start state. -/
theorem propagateAux_lsemStraight {w : Nat} (body : Lcmd) :
    ∀ (facts : List MoveFact) (s : Lstate w), FactsOk facts s →
      lsemStraight ((propagateAux facts body).map Linstr.li_i) s
        = lsemStraight (body.map Linstr.li_i) s := by
  have hnil : ∀ (t : Lstate w), FactsOk ([] : List MoveFact) t := by
    intro t f hf; exact absurd hf (by simp)
  induction body with
  | nil => intro facts s _; rfl
  | cons i rest ih =>
    intro facts s hok
    rw [propagateAux]
    split
    · rename_i dsts opn srcs hi
      split
      · rename_i hrec
        simp only [List.map_cons, lsemStraight_cons]
        rw [hi]
        rw [lsemStep_rewrite_eq hok dsts opn srcs (effWidth opn) _ _]
        cases hst : lsemStep (w := w) (.Lopn dsts opn srcs) s with
        | none => rfl
        | some s₁ =>
          refine ih _ s₁ ?_
          refine FactsOk_step hok rfl ?_
          rw [lsemStep_rewrite_eq hok dsts opn srcs (effWidth opn) _ _]
          exact hst
      · simp only [List.map_cons, lsemStraight_cons]
        cases hst : lsemStep (w := w) i.li_i s with
        | none => rfl
        | some s₁ => exact ih [] s₁ (hnil s₁)
    · simp only [List.map_cons, lsemStraight_cons]
      cases hst : lsemStep (w := w) i.li_i s with
      | none => rfl
      | some s₁ => exact ih [] s₁ (hnil s₁)

/-- Phase 1 from the empty fact set, on every body and every start state. -/
theorem propagate_lsemStraight {w : Nat} (body : Lcmd) (s : Lstate w) :
    lsemStraight ((propagateAux [] body).map Linstr.li_i) s
      = lsemStraight (body.map Linstr.li_i) s :=
  propagateAux_lsemStraight body [] s (fun f hf => absurd hf (by simp))

/-- Two states agree on memory and on every register outside the physical GPs
    that `L` omits. The phase-2 simulation relation; the program counter is not
    part of it, since a deletion shifts it. -/
def LiveAgree {w : Nat} (L : List String) (s t : Lstate w) : Prop :=
  s.lmem = t.lmem ∧ ∀ r, (isPhysGP r = false ∨ L.contains r = true) → s.lvm r = t.lvm r

theorem LiveAgree.refl {w : Nat} (L : List String) (s : Lstate w) : LiveAgree L s s :=
  ⟨rfl, fun _ _ => rfl⟩

/-- At the all-live set the relation is equality of the register map and of
    memory. -/
theorem LiveAgree.full {w : Nat} {s t : Lstate w} (h : LiveAgree physGPs s t) :
    s.lvm = t.lvm ∧ s.lmem = t.lmem := by
  refine ⟨funext fun r => h.2 r ?_, h.1⟩
  by_cases hp : isPhysGP r = true
  · exact Or.inr hp
  · exact Or.inl (by simpa using hp)

/-- At the all-live set `LiveAgree` is `JasminLsemRobust.ArchAgree`: the
    live-relativised relation collapses to agreement on the whole register map
    and memory. -/
theorem LiveAgree.archAgree {w : Nat} {s t : Lstate w} (h : LiveAgree physGPs s t) :
    ArchAgree s t := h.full

theorem addRegs_cons (l : List String) (a : String) (as : List String) :
    addRegs l (a :: as) = addRegs (if l.contains a then l else a :: l) as := by
  simp [addRegs]

/-- `addRegs` keeps everything already in the live set. -/
theorem contains_addRegs_left {r : String} : ∀ (rs l : List String),
    l.contains r = true → (addRegs l rs).contains r = true := by
  intro rs
  induction rs with
  | nil => intro l h; exact h
  | cons a as ih =>
    intro l h
    rw [addRegs_cons]
    refine ih _ ?_
    by_cases ha : l.contains a = true
    · rw [ite_eq_left ha]; exact h
    · rw [ite_eq_right ha]; simp only [List.contains_cons, h, Bool.or_true]

/-- `addRegs` adds everything in its second argument. -/
theorem contains_addRegs_right {r : String} : ∀ (rs l : List String),
    rs.contains r = true → (addRegs l rs).contains r = true := by
  intro rs
  induction rs with
  | nil => intro l h; simp at h
  | cons a as ih =>
    intro l h
    rw [addRegs_cons]
    simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with he | hm
    · refine contains_addRegs_left as _ ?_
      by_cases ha : l.contains a = true
      · rw [ite_eq_left ha, he]; exact ha
      · rw [ite_eq_right ha]; simp [he]
    · exact ih _ hm

/-- An operand whose physical-GP reads are all live evaluates equally in two
    `LiveAgree` states. -/
theorem evalOperand_liveAgree {w : Nat} {L : List String} {s t : Lstate w}
    (h : LiveAgree L s t) (o : LOperand)
    (hcov : ∀ r, (operandReads o).contains r = true → L.contains r = true) :
    evalOperand s o = evalOperand t o := by
  cases o with
  | reg n =>
    simp only [evalOperand]
    refine h.2 n ?_
    by_cases hp : isPhysGP n = true
    · exact Or.inr (hcov n (by simp [operandReads, nameReads, hp]))
    · exact Or.inl (by simpa using hp)
  | imm _ => rfl
  | arr b idx => simp only [evalOperand, h.1]
  | arrIdx b idx sc =>
    have hi : s.lvm idx = t.lvm idx := by
      refine h.2 idx ?_
      by_cases hp : isPhysGP idx = true
      · exact Or.inr (hcov idx (by simp [operandReads, hp]))
      · exact Or.inl (by simpa using hp)
    simp only [evalOperand, h.1, hi]

/-- `STOREIDX` is not a destination-write-only opcode (it writes memory, not its
    nominal destination register), so it kills no register in the live analysis.
    `isDstWriteOnly` routes through `parseImmShiftMnem`, whose `String.splitOn`
    the kernel does not reduce; `native_decide` evaluates the closed Boolean. -/
theorem isDstWriteOnly_storeidx : isDstWriteOnly "STOREIDX" = false := by
  decide +kernel

/-- An op all of whose physical-GP source reads are live steps in lockstep from
    two `LiveAgree` states. A word op or a `LOADIDX` register load writes the same
    word to the destination in both states (left disjunct); a `STOREIDX` leaves
    the register map untouched and writes equal memory (right disjunct). -/
theorem lsemStep_liveAgree {w : Nat} {L : List String} {s t : Lstate w}
    (h : LiveAgree L s t) {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hcov : ∀ o ∈ srcs, ∀ r, (operandReads o).contains r = true → L.contains r = true)
    {s₁ : Lstate w} (hstep : lsemStep (.Lopn dsts opn srcs) s = some s₁) :
    ∃ dst, dsts = [LOperand.reg dst] ∧
      ((∃ v, s₁ = (s.setReg dst v).nextPc
            ∧ lsemStep (.Lopn dsts opn srcs) t = some ((t.setReg dst v).nextPc))
       ∨ (∃ t₁, lsemStep (.Lopn dsts opn srcs) t = some t₁
            ∧ s₁.lvm = s.lvm ∧ t₁.lvm = t.lvm ∧ s₁.lmem = t₁.lmem
            ∧ fullDefsOf dsts opn = [])) := by
  have hmap : srcs.map (evalOperand s) = srcs.map (evalOperand t) :=
    List.map_congr_left fun o ho => evalOperand_liveAgree h o (hcov o ho)
  by_cases hmem : opn = "LOADIDX" ∨ opn = "STOREIDX"
  · cases dsts with
    | nil => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
    | cons d ds =>
      cases ds with
      | cons _ _ => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
      | nil =>
        cases d with
        | imm _ => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
        | arr _ _ => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
        | arrIdx _ _ _ => rcases hmem with rfl | rfl <;> simp [lsemStep] at hstep
        | reg dst =>
          by_cases harr : ∃ base idx scale rest,
              srcs = LOperand.arrIdx base idx scale :: rest
          · obtain ⟨base, idx, scale, rest, rfl⟩ := harr
            have hidx : s.lvm idx = t.lvm idx := by
              refine h.2 idx ?_
              by_cases hp : isPhysGP idx = true
              · exact Or.inr (hcov (LOperand.arrIdx base idx scale) (by simp) idx
                  (by simp [operandReads, hp]))
              · exact Or.inl (by simpa using hp)
            have hhead : evalOperand s (LOperand.arrIdx base idx scale)
                = evalOperand t (LOperand.arrIdx base idx scale) := by
              simp only [List.map_cons, List.cons.injEq] at hmap; exact hmap.1
            rcases hmem with rfl | rfl
            · refine ⟨dst, rfl, Or.inl
                ⟨s.lmem base (Int.ofNat (scale * (s.lvm idx).toNat)), ?_, ?_⟩⟩
              · simp only [lsemStep, reduceIte] at hstep
                exact (Option.some.inj hstep).symm
              · simp only [lsemStep, reduceIte]
                simp only [evalOperand] at hhead
                rw [hhead]
            · cases rest with
              | nil => simp [lsemStep] at hstep
              | cons val vs =>
                cases vs with
                | cons _ _ => simp [lsemStep] at hstep
                | nil =>
                  have hval : evalOperand s val = evalOperand t val :=
                    evalOperand_liveAgree h val (hcov val (by simp))
                  have htstep := lsemStep_storeidx dst base idx scale val t
                  refine ⟨dst, rfl, Or.inr ⟨_, htstep,
                    lsemStep_storeidx_lvm dst base idx scale val s s₁ hstep,
                    lsemStep_storeidx_lvm dst base idx scale val t _ htstep, ?_, ?_⟩⟩
                  · rw [lsemStep_storeidx] at hstep
                    rw [← Option.some.inj hstep]
                    simp only [Lstate.lmem_nextPc, hidx, hval, h.1]
                  · rw [show fullDefsOf [LOperand.reg dst] "STOREIDX" = [] from by
                      simp [fullDefsOf, isDstWriteOnly_storeidx]]
          · exfalso
            have hna : ∀ base idx scale rest,
                srcs ≠ LOperand.arrIdx base idx scale :: rest :=
              fun base idx scale rest heq => harr ⟨base, idx, scale, rest, heq⟩
            rw [lsemStep_reg_srcs dst opn srcs s hna] at hstep
            rcases hmem with rfl | rfl
            · rw [applyOpn_LOADIDX] at hstep; simp at hstep
            · rw [applyOpn_STOREIDX] at hstep; simp at hstep
  · have hnm : opn ≠ "LOADIDX" ∧ opn ≠ "STOREIDX" :=
      ⟨fun h => hmem (Or.inl h), fun h => hmem (Or.inr h)⟩
    obtain ⟨dst, v, hd, happ, hs₁⟩ := lsemStep_Lopn_inv hnm hstep
    refine ⟨dst, hd, Or.inl ⟨v, hs₁, ?_⟩⟩
    subst hd
    rw [hmap] at happ
    rw [lsemStep_reg_nonmem dst opn srcs t hnm, happ]

/-- On states with equal register map and memory, every instruction steps to
    states with equal register map and memory. -/
theorem lsemStep_congr_full {w : Nat} (i : LinstrR) {s t : Lstate w}
    (hv : s.lvm = t.lvm) (hm : s.lmem = t.lmem) {s₁ : Lstate w}
    (hst : lsemStep i s = some s₁) :
    ∃ t₁, lsemStep i t = some t₁ ∧ s₁.lvm = t₁.lvm ∧ s₁.lmem = t₁.lmem :=
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust.lsemStep_congr_of_archAgree
    i hv hm hst

/-- A barrier is kept and forces all registers live. -/
theorem deadElimStep_barrier (i : Linstr) (live : List String) (acc : Lcmd)
    (h : ∀ dsts opn srcs, i.li_i = .Lopn dsts opn srcs → isRecognizedOpn opn = false) :
    deadElimStep i (live, acc) = (physGPs, i :: acc) := by
  cases hi : i.li_i with
  | Lopn dsts opn srcs =>
    simp only [deadElimStep, hi, h dsts opn srcs hi, Bool.false_eq_true, ite_false]
  | _ => simp only [deadElimStep, hi]

/-- The dropping branch: a self-copy or a move whose destination is not live. -/
theorem deadElimStep_drop {i : Linstr} (live : List String) (acc : Lcmd)
    {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn dsts opn srcs) (hrec : isRecognizedOpn opn = true)
    {d : String} {src : LOperand} {ww : Nat} (hcs : moveShape i = some (d, src, ww))
    (hdrop : ((ww == 64 && src == LOperand.reg d) || !(live.contains d)) = true) :
    deadElimStep i (live, acc) = (live, acc) := by
  simp only [deadElimStep, hi, hrec, ite_true, hcs, hdrop]

/-- The keeping branch for a non-move recognised op. -/
theorem deadElimStep_keep_none {i : Linstr} (live : List String) (acc : Lcmd)
    {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn dsts opn srcs) (hrec : isRecognizedOpn opn = true)
    (hcs : moveShape i = none) :
    deadElimStep i (live, acc) =
      (addRegs (live.filter fun r => !((fullDefsOf dsts opn).contains r))
        (instrUses dsts opn srcs), i :: acc) := by
  simp only [deadElimStep, hi, hrec, ite_true, hcs, Bool.false_eq_true, ite_false]

/-- The keeping branch for a live move. -/
theorem deadElimStep_keep_some {i : Linstr} (live : List String) (acc : Lcmd)
    {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn dsts opn srcs) (hrec : isRecognizedOpn opn = true)
    {d : String} {src : LOperand} {ww : Nat} (hcs : moveShape i = some (d, src, ww))
    (hdrop : ((ww == 64 && src == LOperand.reg d) || !(live.contains d)) = false) :
    deadElimStep i (live, acc) =
      (addRegs (live.filter fun r => !((fullDefsOf dsts opn).contains r))
        (instrUses dsts opn srcs), i :: acc) := by
  simp only [deadElimStep, hi, hrec, ite_true, hcs, hdrop, Bool.false_eq_true, ite_false]

/-- Every physical GP a source operand reads is an instruction use. -/
theorem contains_instrUses_of_src {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {o : LOperand} {r : String} (ho : o ∈ srcs)
    (hr : (operandReads o).contains r = true) :
    (instrUses dsts opn srcs).contains r = true := by
  simp only [instrUses, List.contains_eq_mem, decide_eq_true_eq] at hr ⊢
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨o, ho, hr⟩)))

/-- Every register the mnemonic reads implicitly is an instruction use. -/
theorem contains_instrUses_of_implicit {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {r : String}
    (hr : (implicitReads opn).contains r = true) :
    (instrUses dsts opn srcs).contains r = true := by
  simp only [instrUses, List.contains_eq_mem, decide_eq_true_eq] at hr ⊢
  exact List.mem_append_right _ hr

/-- A single-destination op kills no register other than its destination. -/
theorem contains_fullDefsOf_false {dst r : String} {opn : String} (hne : r ≠ dst) :
    (fullDefsOf [LOperand.reg dst] opn).contains r = false := by
  unfold fullDefsOf
  by_cases hc : (isDstWriteOnly opn && 32 ≤ effWidth opn) = true
  · rw [ite_eq_left hc, regDefsOf_singleton]
    by_cases hp : isPhysGP dst = true
    · simp [hp, hne]
    · simp [hp]
  · rw [ite_eq_right hc]; rfl

/-- **Phase 2 is a forward simulation up to the live set.** From states agreeing
    off the computed live-in set, a body that runs to completion is matched by the
    swept body, ending in states agreeing off the end live set. -/
theorem deadElim_sim {w : Nat} (body : Lcmd) :
    ∀ (Lend : List String) (s t : Lstate w),
      LiveAgree (body.foldr deadElimStep (Lend, [])).1 s t →
      ∀ s₂, lsemStraight (body.map Linstr.li_i) s = some s₂ →
        ∃ t₂, lsemStraight ((body.foldr deadElimStep (Lend, [])).2.map Linstr.li_i) t = some t₂
          ∧ LiveAgree Lend s₂ t₂ := by
  induction body with
  | nil =>
    intro Lend s t h s₂ hrun
    refine ⟨t, rfl, ?_⟩
    simp only [List.map_nil, lsemStraight_nil, Option.some.injEq] at hrun
    exact hrun ▸ h
  | cons i rest ih =>
    intro Lend s t h s₂ hrun
    simp only [List.map_cons, lsemStraight_cons] at hrun
    have ih' := ih Lend
    obtain ⟨Lr, outR, hP⟩ : ∃ a b, rest.foldr deadElimStep (Lend, []) = (a, b) := ⟨_, _, rfl⟩
    rw [hP] at ih'
    rw [List.foldr_cons, hP] at h ⊢
    cases hst : lsemStep (w := w) i.li_i s with
    | none => rw [hst] at hrun; exact absurd hrun (by simp)
    | some s₁ =>
      rw [hst] at hrun
      have hcases :
          (∃ dsts opn srcs, i.li_i = LinstrR.Lopn dsts opn srcs ∧ isRecognizedOpn opn = true)
          ∨ (∀ (live : List String) (acc : Lcmd),
              deadElimStep i (live, acc) = (physGPs, i :: acc)) := by
        cases hLi : i.li_i with
        | Lopn dsts opn srcs =>
          by_cases hr : isRecognizedOpn opn = true
          · exact Or.inl ⟨dsts, opn, srcs, rfl, hr⟩
          · refine Or.inr (fun live acc => deadElimStep_barrier i live acc ?_)
            intro d o sc he
            rw [hLi] at he
            injection he with _ h2 _
            rw [← h2]
            simpa using hr
        | _ =>
          exact Or.inr (fun live acc => deadElimStep_barrier i live acc (by
            intro d o sc he; rw [hLi] at he; exact absurd he (by simp)))
      rcases hcases with ⟨dsts, opn, srcs, hLi, hrec⟩ | hbar
      · cases hcs : moveShape i with
        | none =>
          rw [deadElimStep_keep_none Lr outR hLi hrec hcs] at h ⊢
          have h' : LiveAgree (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
              (instrUses dsts opn srcs)) s t := h
          have hcov : ∀ o ∈ srcs, ∀ r, (operandReads o).contains r = true →
              (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
                (instrUses dsts opn srcs)).contains r = true :=
            fun o ho r hr => contains_addRegs_right _ _ (contains_instrUses_of_src ho hr)
          rw [hLi] at hst
          obtain ⟨dst, hd2, hcase⟩ := lsemStep_liveAgree h' hcov hst
          rcases hcase with ⟨v, hs₁, hts⟩ | ⟨t₁, hts, hsv, htv, hmemeq, hfd⟩
          · show ∃ t₂, lsemStraight ((i :: outR).map Linstr.li_i) t = some t₂
              ∧ LiveAgree Lend s₂ t₂
            simp only [List.map_cons, lsemStraight_cons, hLi, hts]
            refine ih' s₁ _ ⟨?_, ?_⟩ s₂ hrun
            · rw [hs₁]; exact h'.1
            · intro r hr
              rw [hs₁]
              simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
              by_cases hrd : r = dst
              · rw [ite_eq_left hrd, ite_eq_left hrd]
              · rw [ite_eq_right hrd, ite_eq_right hrd]
                refine h'.2 r ?_
                rcases hr with hp | hm
                · exact Or.inl hp
                · refine Or.inr (contains_addRegs_left _ _ ?_)
                  have hmem : r ∈ Lr := by simpa using hm
                  have hpred : (!((fullDefsOf dsts opn).contains r)) = true := by
                    rw [hd2, contains_fullDefsOf_false hrd]; rfl
                  have hfil : r ∈ Lr.filter (fun x => !((fullDefsOf dsts opn).contains x)) :=
                    List.mem_filter.mpr ⟨hmem, hpred⟩
                  simpa using hfil
          · show ∃ t₂, lsemStraight ((i :: outR).map Linstr.li_i) t = some t₂
              ∧ LiveAgree Lend s₂ t₂
            simp only [List.map_cons, lsemStraight_cons, hLi, hts]
            refine ih' s₁ t₁ ⟨hmemeq, ?_⟩ s₂ hrun
            intro r hr
            rw [hsv, htv]
            refine h'.2 r ?_
            rcases hr with hp | hm
            · exact Or.inl hp
            · refine Or.inr (contains_addRegs_left _ _ ?_)
              have hmem : r ∈ Lr := by simpa using hm
              have hpred : (!((fullDefsOf dsts opn).contains r)) = true := by
                simp [hfd]
              have hfil : r ∈ Lr.filter (fun x => !((fullDefsOf dsts opn).contains x)) :=
                List.mem_filter.mpr ⟨hmem, hpred⟩
              simpa using hfil
        | some q =>
          obtain ⟨d, src, ww⟩ := q
          by_cases hdr : ((ww == 64 && src == LOperand.reg d) || !(Lr.contains d)) = true
          · rw [deadElimStep_drop Lr outR hLi hrec hcs hdr] at h ⊢
            have h' : LiveAgree Lr s t := h
            obtain ⟨opn2, hi2, hd, hsr, hmov2⟩ := moveShape_inv hcs
            have hnm : opn2 ≠ "LOADIDX" ∧ opn2 ≠ "STOREIDX" :=
              ⟨fun hc => by rw [moveShape_none_of_mem hi2 (Or.inl hc)] at hcs
                            simp at hcs,
               fun hc => by rw [moveShape_none_of_mem hi2 (Or.inr hc)] at hcs
                            simp at hcs⟩
            rw [hi2] at hst
            obtain ⟨dst, v, hdd, happ, hs₁⟩ := lsemStep_Lopn_inv hnm hst
            have hdst : dst = d := by
              injection hdd with h1 _; injection h1 with h2; exact h2.symm
            subst hdst
            have hv : v = evalOperand s src := by
              simp only [List.map_cons, List.map_nil] at happ
              exact applyOpn_singleton hmov2 happ
            show ∃ t₂, lsemStraight (outR.map Linstr.li_i) t = some t₂ ∧ LiveAgree Lend s₂ t₂
            refine ih' s₁ t ⟨?_, ?_⟩ s₂ hrun
            · rw [hs₁]; exact h'.1
            · intro r hr
              rw [hs₁]
              simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
              by_cases hrd : r = dst
              · rcases (Bool.or_eq_true _ _).mp hdr with hself | hdead
                · have hds : src = LOperand.reg dst :=
                    eq_of_beq ((Bool.and_eq_true _ _).mp hself).2
                  rw [ite_eq_left hrd, hv, hds]
                  simp only [evalOperand]
                  rw [← hrd]
                  exact h'.2 r hr
                · exfalso
                  have hnc : Lr.contains dst = false := by simpa using hdead
                  rcases hr with hp | hm
                  · rw [hrd] at hp; rw [hp] at hd; exact absurd hd (by simp)
                  · rw [hrd, hnc] at hm; exact absurd hm (by simp)
              · rw [ite_eq_right hrd]; exact h'.2 r hr
          · rw [deadElimStep_keep_some Lr outR hLi hrec hcs (by simpa using hdr)] at h ⊢
            have h' : LiveAgree (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
                (instrUses dsts opn srcs)) s t := h
            have hcov : ∀ o ∈ srcs, ∀ r, (operandReads o).contains r = true →
                (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
                  (instrUses dsts opn srcs)).contains r = true :=
              fun o ho r hr => contains_addRegs_right _ _ (contains_instrUses_of_src ho hr)
            rw [hLi] at hst
            obtain ⟨dst, hd2, hcase⟩ := lsemStep_liveAgree h' hcov hst
            rcases hcase with ⟨v, hs₁, hts⟩ | ⟨t₁, hts, hsv, htv, hmemeq, hfd⟩
            · show ∃ t₂, lsemStraight ((i :: outR).map Linstr.li_i) t = some t₂
                ∧ LiveAgree Lend s₂ t₂
              simp only [List.map_cons, lsemStraight_cons, hLi, hts]
              refine ih' s₁ _ ⟨?_, ?_⟩ s₂ hrun
              · rw [hs₁]; exact h'.1
              · intro r hr
                rw [hs₁]
                simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
                by_cases hrd : r = dst
                · rw [ite_eq_left hrd, ite_eq_left hrd]
                · rw [ite_eq_right hrd, ite_eq_right hrd]
                  refine h'.2 r ?_
                  rcases hr with hp | hm
                  · exact Or.inl hp
                  · refine Or.inr (contains_addRegs_left _ _ ?_)
                    have hmem : r ∈ Lr := by simpa using hm
                    have hpred : (!((fullDefsOf dsts opn).contains r)) = true := by
                      rw [hd2, contains_fullDefsOf_false hrd]; rfl
                    have hfil : r ∈ Lr.filter (fun x => !((fullDefsOf dsts opn).contains x)) :=
                      List.mem_filter.mpr ⟨hmem, hpred⟩
                    simpa using hfil
            · show ∃ t₂, lsemStraight ((i :: outR).map Linstr.li_i) t = some t₂
                ∧ LiveAgree Lend s₂ t₂
              simp only [List.map_cons, lsemStraight_cons, hLi, hts]
              refine ih' s₁ t₁ ⟨hmemeq, ?_⟩ s₂ hrun
              intro r hr
              rw [hsv, htv]
              refine h'.2 r ?_
              rcases hr with hp | hm
              · exact Or.inl hp
              · refine Or.inr (contains_addRegs_left _ _ ?_)
                have hmem : r ∈ Lr := by simpa using hm
                have hpred : (!((fullDefsOf dsts opn).contains r)) = true := by
                  simp [hfd]
                have hfil : r ∈ Lr.filter (fun x => !((fullDefsOf dsts opn).contains x)) :=
                  List.mem_filter.mpr ⟨hmem, hpred⟩
                simpa using hfil
      · rw [hbar Lr outR] at h ⊢
        have h' : LiveAgree physGPs s t := h
        obtain ⟨hvv, hmm⟩ := h'.full
        obtain ⟨t₁, hts, htv, htm⟩ := lsemStep_congr_full i.li_i hvv hmm hst
        show ∃ t₂, lsemStraight ((i :: outR).map Linstr.li_i) t = some t₂
          ∧ LiveAgree Lend s₂ t₂
        simp only [List.map_cons, lsemStraight_cons, hts]
        exact ih' s₁ t₁ ⟨htm, fun r _ => congrFun htv r⟩ s₂ hrun

/-- **The pass preserves the machine state.** On every body and every start
    state from which the original runs to completion, the propagated body runs to
    completion and reaches a state with the same register map and the same memory.
    The program counter is lower by the number of deleted instructions. No side
    condition: the end live set is all 15 physical GPs, so the final agreement is
    total. -/
theorem copyPropagateBody_lsemStraight {w : Nat} (body : Lcmd) (s s₂ : Lstate w)
    (hrun : lsemStraight (body.map Linstr.li_i) s = some s₂) :
    ∃ t₂, lsemStraight ((copyPropagateBody body).map Linstr.li_i) s = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem := by
  have h1 : lsemStraight ((propagateAux [] body).map Linstr.li_i) s = some s₂ := by
    rw [propagate_lsemStraight]; exact hrun
  obtain ⟨t₂, ht, hag⟩ :=
    deadElim_sim (propagateAux [] body) physGPs s s (LiveAgree.refl _ s) s₂ h1
  exact ⟨t₂, ht, hag.full.1.symm, hag.full.2.symm⟩

/-- The pass on one `Lfundef` preserves the machine state. -/
theorem copyPropagateFundef_lsemStraight {w : Nat} (f : Lfundef) (s s₂ : Lstate w)
    (hrun : lsemStraight (f.lfd_body.map Linstr.li_i) s = some s₂) :
    ∃ t₂, lsemStraight ((copyPropagateFundef f).lfd_body.map Linstr.li_i) s = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem :=
  copyPropagateBody_lsemStraight f.lfd_body s s₂ hrun

/-! ## 9a. Store-image agreement on every start state

`copyPropagateBody_lsemStraight` states the forward direction (whenever the input
runs to completion the output does too, with the same store). The store-image
form the verified pipeline composes — an `ArchAgreeOpt` between the two
`lsemStraight` results, equivalently `Option.map stateStore`-equality — also
covers the stuck case, which needs two facts about the model: a single step's
definedness depends on the opcode and source arity but not on the register
values, and a dropped move (`applyOpn "MOV"`/`"MOVQ"`) always steps. -/

/-- `applyOpn` on one source word succeeds or fails by opcode alone. -/
theorem applyOpn_isSome_congr_one {w : Nat} (mn : String) (a c : BitVec w) :
    (applyOpn mn [a]).isSome = (applyOpn mn [c]).isSome := by
  simp only [applyOpn]; split <;> first | rfl | (split <;> simp_all)

/-- `applyOpn` on two source words succeeds or fails by opcode alone. -/
theorem applyOpn_isSome_congr_two {w : Nat} (mn : String) (a b c d : BitVec w) :
    (applyOpn mn [a, b]).isSome = (applyOpn mn [c, d]).isSome := by
  simp only [applyOpn]; split <;> simp_all

/-- `applyOpn` on three source words succeeds or fails by opcode alone. -/
theorem applyOpn_isSome_congr_three {w : Nat} (mn : String) (a b e c d f : BitVec w) :
    (applyOpn mn [a, b, e]).isSome = (applyOpn mn [c, d, f]).isSome := by
  simp only [applyOpn]; split <;> first | rfl | (split <;> simp_all)

/-- `applyOpn` succeeds or fails by opcode and source arity, never by the source
    words: on two same-length argument lists its `isSome` is the same. -/
theorem applyOpn_isSome_congr_length {w : Nat} (mn : String) :
    ∀ (l₁ l₂ : List (BitVec w)), l₁.length = l₂.length →
      (applyOpn mn l₁).isSome = (applyOpn mn l₂).isSome := by
  intro l₁
  match l₁ with
  | [] => intro l₂ h; cases l₂ with
      | nil => rfl
      | cons _ _ => simp at h
  | [a] => intro l₂ h; match l₂, h with
      | [c], _ => exact applyOpn_isSome_congr_one mn a c
  | a :: b :: l₁' => intro l₂ h; match l₂, h with
      | c :: d :: l₂', h =>
          cases l₁' with
          | nil => cases l₂' with
              | nil => exact applyOpn_isSome_congr_two mn a b c d
              | cons _ _ => simp at h
          | cons _ tl => cases l₂' with
              | nil => simp at h
              | cons _ tl2 =>
                  cases tl with
                  | nil => cases tl2 with
                      | nil => exact applyOpn_isSome_congr_three mn _ _ _ _ _ _
                      | cons _ _ => simp at h
                  | cons _ _ => cases tl2 with
                      | nil => simp at h
                      | cons _ _ => simp only [applyOpn]; split <;> simp_all

/-- A single step's definedness is a function of the instruction alone: `lsemStep`
    succeeds on `s` iff it succeeds on `t`, for any two states. -/
theorem lsemStep_isSome_indep {w : Nat} (i : LinstrR) (s t : Lstate w) :
    (lsemStep i s).isSome = (lsemStep i t).isSome := by
  cases i with
  | Lopn dsts opn srcs =>
    cases dsts with
    | nil => rfl
    | cons d ds =>
      cases ds with
      | cons _ _ => cases d <;> rfl
      | nil =>
        cases d with
        | reg dst =>
          by_cases harr : ∃ base idx scale rest,
              srcs = LOperand.arrIdx base idx scale :: rest
          · obtain ⟨base, idx, scale, rest, rfl⟩ := harr
            simp only [lsemStep]
            by_cases hl : opn = "LOADIDX"
            · simp [hl]
            · by_cases hs : opn = "STOREIDX"
              · simp only [ite_eq_right hl, ite_eq_left hs]
                cases rest with
                | nil => simp
                | cons v vs => cases vs with
                  | nil => simp
                  | cons _ _ => simp
              · simp only [ite_eq_right hl, ite_eq_right hs]
                have hlen := applyOpn_isSome_congr_length (stripWidthTag opn)
                  ((LOperand.arrIdx base idx scale :: rest).map (evalOperand s))
                  ((LOperand.arrIdx base idx scale :: rest).map (evalOperand t)) (by simp)
                cases h1 : applyOpn (stripWidthTag opn)
                    ((LOperand.arrIdx base idx scale :: rest).map (evalOperand s)) <;>
                cases h2 : applyOpn (stripWidthTag opn)
                    ((LOperand.arrIdx base idx scale :: rest).map (evalOperand t)) <;>
                simp_all
          · have harr' : ∀ base idx scale rest,
                srcs ≠ LOperand.arrIdx base idx scale :: rest :=
              fun base idx scale rest heq => harr ⟨base, idx, scale, rest, heq⟩
            rw [lsemStep_reg_srcs dst opn srcs s harr',
                lsemStep_reg_srcs dst opn srcs t harr']
            have hlen := applyOpn_isSome_congr_length (stripWidthTag opn)
              (srcs.map (evalOperand s)) (srcs.map (evalOperand t)) (by simp)
            cases h1 : applyOpn (stripWidthTag opn) (srcs.map (evalOperand s)) <;>
            cases h2 : applyOpn (stripWidthTag opn) (srcs.map (evalOperand t)) <;>
            simp_all
        | imm _ => rfl
        | arr _ _ => rfl
        | arrIdx _ _ _ => rfl
  | Lalign => rfl
  | Llabel _ _ => rfl
  | Lgoto _ => rfl
  | Lcond _ _ => rfl
  | Ligoto _ => rfl
  | Lcall _ _ => rfl
  | Lret => rfl
  | LstoreLabel _ _ => rfl
  | Lsyscall _ => rfl

/-- A move `moveShape` recognises always steps: `applyOpn` on its `MOV`/`MOVQ`
    base opcode returns the copied word, so the step is defined on every state. -/
theorem moveShape_lsemStep_isSome {w : Nat} {i : Linstr} {q : String × LOperand × Nat}
    (h : moveShape i = some q) (s : Lstate w) : (lsemStep i.li_i s).isSome = true := by
  unfold moveShape at h
  split at h
  · rename_i d opn src hi
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨_, hmn⟩, _⟩, hfs⟩ := hc
      by_cases hwcond : (mnemWidth opn == 32 || mnemWidth opn == 64) = true
      · have hsw := stripWidthTag_mov_of_moveShape opn hmn hwcond
        have hna : ∀ base idx scale rest,
            [src] ≠ LOperand.arrIdx base idx scale :: rest := by
          intro base idx scale rest heq
          simp only [List.cons.injEq] at heq
          obtain ⟨rfl, _⟩ := heq
          simp [isFactSrc] at hfs
        rw [hi, lsemStep_reg_srcs d opn [src] s hna]
        rcases hsw with hsw | hsw <;> simp [hsw, applyOpn, List.map_cons, List.map_nil]
      · exfalso
        rw [Bool.not_eq_true] at hwcond
        simp only [hwcond] at h
        exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Phase 2 preserves a stuck run: if the input body gets stuck (`lsemStraight =
    none`) from `s`, the swept body gets stuck from any `t`. Every dropped
    instruction is a move that always steps, so a deletion never removes the
    stuck point. -/
theorem deadElim_none {w : Nat} (body : Lcmd) :
    ∀ (Lend : List String) (s t : Lstate w),
      lsemStraight (body.map Linstr.li_i) s = none →
      lsemStraight ((body.foldr deadElimStep (Lend, [])).2.map Linstr.li_i) t = none := by
  induction body with
  | nil =>
    intro Lend s t h
    simp only [List.map_nil, lsemStraight_nil] at h; exact absurd h (by simp)
  | cons i rest ih =>
    intro Lend s t h
    obtain ⟨Lr, outR, hP⟩ : ∃ a b, rest.foldr deadElimStep (Lend, []) = (a, b) := ⟨_, _, rfl⟩
    rw [List.foldr_cons, hP]
    simp only [List.map_cons, lsemStraight_cons] at h
    have hstep_t : (lsemStep i.li_i s).isSome = (lsemStep i.li_i t).isSome :=
      lsemStep_isSome_indep _ s t
    have keepClose : ∀ s₁, lsemStep i.li_i s = some s₁ →
        lsemStraight (i.li_i :: outR.map Linstr.li_i) t = none := by
      intro s₁ hst
      simp only [lsemStraight_cons]
      rw [hst] at h
      have ht1 : (lsemStep i.li_i t).isSome = true := by rw [← hstep_t, hst]; rfl
      obtain ⟨t₁, htt⟩ := Option.isSome_iff_exists.mp ht1
      rw [htt]
      simpa only [hP] using ih Lend s₁ t₁ h
    have noneClose : lsemStep i.li_i s = none →
        lsemStraight (i.li_i :: outR.map Linstr.li_i) t = none := by
      intro hst
      simp only [lsemStraight_cons]
      cases htt : lsemStep i.li_i t with
      | none => rfl
      | some t₁ => rw [hst, htt] at hstep_t; simp at hstep_t
    have hcases :
        (∃ dsts opn srcs, i.li_i = LinstrR.Lopn dsts opn srcs ∧ isRecognizedOpn opn = true)
        ∨ (∀ (live : List String) (acc : Lcmd),
            deadElimStep i (live, acc) = (physGPs, i :: acc)) := by
      cases hLi : i.li_i with
      | Lopn dsts opn srcs =>
        by_cases hr : isRecognizedOpn opn = true
        · exact Or.inl ⟨dsts, opn, srcs, rfl, hr⟩
        · refine Or.inr (fun live acc => deadElimStep_barrier i live acc ?_)
          intro d o sc he; rw [hLi] at he; injection he with _ h2 _; rw [← h2]; simpa using hr
      | _ => exact Or.inr (fun live acc => deadElimStep_barrier i live acc (by
          intro d o sc he; rw [hLi] at he; exact absurd he (by simp)))
    rcases hcases with ⟨dsts, opn, srcs, hLi, hrec⟩ | hbar
    · cases hcs : moveShape i with
      | none =>
        rw [deadElimStep_keep_none Lr outR hLi hrec hcs]
        simp only [List.map_cons]
        cases hst : lsemStep i.li_i s with
        | none => exact noneClose hst
        | some s₁ => exact keepClose s₁ hst
      | some q =>
        by_cases hdr : ((q.2.2 == 64 && q.2.1 == LOperand.reg q.1) || !(Lr.contains q.1)) = true
        · obtain ⟨d, src, ww⟩ := q
          rw [deadElimStep_drop Lr outR hLi hrec hcs (by simpa using hdr)]
          cases hst : lsemStep i.li_i s with
          | none =>
            exfalso; have := moveShape_lsemStep_isSome hcs s; rw [hst] at this; simp at this
          | some s₁ =>
            rw [hst] at h
            simpa only [hP] using ih Lend s₁ t h
        · obtain ⟨d, src, ww⟩ := q
          rw [deadElimStep_keep_some Lr outR hLi hrec hcs (by simpa using hdr)]
          simp only [List.map_cons]
          cases hst : lsemStep i.li_i s with
          | none => exact noneClose hst
          | some s₁ => exact keepClose s₁ hst
    · rw [hbar Lr outR]
      simp only [List.map_cons]
      cases hst : lsemStep i.li_i s with
      | none => exact noneClose hst
      | some s₁ => exact keepClose s₁ hst

/-- **The pass preserves the store on every start state.** The propagated body's
    `lsemStraight` result agrees with the original's on the register map and on
    memory, whether or not the run completes: on a stuck run both are `none`, on a
    completed run both write the same store. This is the `ArchAgreeOpt` shape the
    verified sub-pipeline composes, matching `reloadElimBody_lsem`. -/
theorem copyPropagateBody_lsem {w : Nat} (body : Lcmd) (s : Lstate w) :
    ArchAgreeOpt (lsemStraight ((copyPropagateBody body).map Linstr.li_i) s)
      (lsemStraight (body.map Linstr.li_i) s) := by
  cases horig : lsemStraight (body.map Linstr.li_i) s with
  | some s₂ =>
    obtain ⟨t₂, ht, hlvm, hlmem⟩ := copyPropagateBody_lsemStraight body s s₂ horig
    rw [ht]; exact ⟨hlvm, hlmem⟩
  | none =>
    have h1 : lsemStraight ((propagateAux [] body).map Linstr.li_i) s = none := by
      rw [propagate_lsemStraight]; exact horig
    have hopt : lsemStraight ((copyPropagateBody body).map Linstr.li_i) s = none := by
      simp only [copyPropagateBody, deadElimBody]
      exact deadElim_none (propagateAux [] body) physGPs s s h1
    rw [hopt]; trivial

/-- The store-image equality (`Option.map stateStore ∘ lsemStraight`) the verified
    pipeline chains through `archAgreeOpt_iff_stateStore`. -/
theorem copyPropagateBody_stateStore {w : Nat} (body : Lcmd) (s : Lstate w) :
    Option.map stateStore (lsemStraight ((copyPropagateBody body).map Linstr.li_i) s)
      = Option.map stateStore (lsemStraight (body.map Linstr.li_i) s) :=
  (archAgreeOpt_iff_stateStore _ _).mp (copyPropagateBody_lsem body s)

/-- The pass on one `Lfundef` preserves the store on every start state. -/
theorem copyPropagateFundef_lsem {w : Nat} (f : Lfundef) (s : Lstate w) :
    ArchAgreeOpt (lsemStraight ((copyPropagateFundef f).lfd_body.map Linstr.li_i) s)
      (lsemStraight (f.lfd_body.map Linstr.li_i) s) :=
  copyPropagateBody_lsem f.lfd_body s

/-! ## 10. Deletion is a sublist, and the mnemonic guarantee -/

/-- Phase 2 either drops the instruction or keeps it at the head. -/
theorem deadElimStep_snd (i : Linstr) (live : List String) (acc : Lcmd) :
    (deadElimStep i (live, acc)).2 = acc ∨ (deadElimStep i (live, acc)).2 = i :: acc := by
  cases hLi : i.li_i with
  | Lopn dsts opn srcs =>
    by_cases hrec : isRecognizedOpn opn = true
    · cases hcs : moveShape i with
      | none => exact Or.inr (by rw [deadElimStep_keep_none live acc hLi hrec hcs])
      | some q =>
        obtain ⟨d, src, ww⟩ := q
        by_cases hdr : ((ww == 64 && src == LOperand.reg d) || !(live.contains d)) = true
        · exact Or.inl (by rw [deadElimStep_drop live acc hLi hrec hcs hdr])
        · exact Or.inr (by
            rw [deadElimStep_keep_some live acc hLi hrec hcs (by simpa using hdr)])
    · exact Or.inr (by
        rw [deadElimStep_barrier i live acc (by
          intro d o sc he; rw [hLi] at he; injection he with _ h2 _; rw [← h2]
          simpa using hrec)])
  | _ => exact Or.inr (by
      rw [deadElimStep_barrier i live acc (by
        intro d o sc he; rw [hLi] at he; exact absurd he (by simp))])

theorem deadElim_foldr_sublist (body : Lcmd) : ∀ (Lend : List String) (acc : Lcmd),
    ∃ pre, (body.foldr deadElimStep (Lend, acc)).2 = pre ++ acc ∧ pre.Sublist body := by
  induction body with
  | nil => intro Lend acc; exact ⟨[], rfl, List.Sublist.refl _⟩
  | cons i rest ih =>
    intro Lend acc
    obtain ⟨pre, hpre, hsub⟩ := ih Lend acc
    obtain ⟨L1, A1, hP⟩ : ∃ a b, rest.foldr deadElimStep (Lend, acc) = (a, b) := ⟨_, _, rfl⟩
    rw [hP] at hpre
    rw [List.foldr_cons, hP]
    rcases deadElimStep_snd i L1 A1 with hd | hd
    · exact ⟨pre, by rw [hd]; exact hpre, hsub.cons _⟩
    · refine ⟨i :: pre, ?_, hsub.cons_cons _⟩
      have hA : A1 = pre ++ acc := hpre
      rw [hd, hA]
      rfl

/-- Phase 2 only deletes: its output is a sublist of its input. -/
theorem deadElimBody_sublist (body : Lcmd) : (deadElimBody body).Sublist body := by
  obtain ⟨pre, hpre, hsub⟩ := deadElim_foldr_sublist body physGPs []
  have hb : deadElimBody body = pre := by rw [deadElimBody, hpre, List.append_nil]
  rw [hb]; exact hsub

/-- The instruction shapes of the output are a sublist of those of the input. -/
theorem copyPropagateBody_sublist_shape (body : Lcmd) :
    ((copyPropagateBody body).map instrShape).Sublist (body.map instrShape) := by
  have h1 := (deadElimBody_sublist (propagateAux [] body)).map instrShape
  rw [propagateAux_shape] at h1
  exact h1

/-- **The pass never widens or narrows an instruction.** The output mnemonics are
    a sublist of the input mnemonics, so every mnemonic the pass emits occurs in
    the input, in order: a `MOV:64` can never leave the pass as a `MOV`. -/
theorem copyPropagateBody_mnems (body : Lcmd) :
    ((copyPropagateBody body).map instrMnem).Sublist (body.map instrMnem) := by
  have h1 := (copyPropagateBody_sublist_shape body).map (fun sh => sh.2.1.map Prod.snd)
  simpa only [List.map_map, Function.comp_def, ← instrMnem_of_shape] using h1

/-- The pass never lengthens a body. -/
theorem copyPropagateBody_length_le (body : Lcmd) :
    (copyPropagateBody body).length ≤ body.length := by
  have h := (copyPropagateBody_sublist_shape body).length_le
  simpa using h

/-! ## 11. Leakage

`JasminLsemRobust.linstrLeak` emits, per instruction, the opcode together with
the *operand shapes* — `operandShape (.reg r) = .regShape r` carries the register
name — and nothing for `Lalign`/`Llabel`/`Lret`. The trace of a body that runs to
completion is therefore the concatenation of the per-instruction leaks, a
function of the instruction list alone. Trace equality between input and output
does not hold, because deleting a copy removes its `LLeak.opn` event and
rewriting a source changes the `regShape` inside one; the `#guard` at the end of
this section checks that on `demoChain`. -/

/-- The leakage trace of the propagated body is the concatenation of its
    per-instruction leaks. -/
theorem copyPropagateBody_lsemLeak_eq_syntactic {w : Nat} (body : Lcmd) (s s₂ : Lstate w)
    (hrun : lsemStraight (body.map Linstr.li_i) s = some s₂) :
    lsemLeak ((copyPropagateBody body).map Linstr.li_i) s
      = ((copyPropagateBody body).map Linstr.li_i).flatMap linstrLeak := by
  obtain ⟨t₂, ht, _, _⟩ := copyPropagateBody_lsemStraight body s s₂ hrun
  exact lsemLeak_of_run _ s t₂ ht

-- The pass changes the leakage trace: on `demoChain` two `MOV:64` events are
-- dropped and the surviving `XOR:64` event carries `regShape "RBX"` where the
-- input carried `regShape "RCX"`.
#guard ((copyPropagateBody demoChain).map Linstr.li_i).flatMap linstrLeak
    ≠ (demoChain.map Linstr.li_i).flatMap linstrLeak

end CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
