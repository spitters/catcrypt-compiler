/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Reg→reg copy propagation + dead-copy elimination on the owned-RA `Lcmd`

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

* **Phase 1 (forward copy propagation).** A recognized reg→reg copy
  `Lopn [.reg d] MOV/MOVQ/MOV:64 [.reg s]` (both bare physical GP names)
  records the fact `d ↦ (s, w)` (`w` = 32 or 64, the copy's `mnemWidth`).
  Until `d` or `s` is redefined (or a barrier), any *rewritable* source
  operand `.reg d` is replaced by `.reg s`. Facts chain transitively (the
  copy's own source is rewritten first, so `MOV b,a; MOV c,b` yields
  `c ↦ a`).
* **Phase 2 (backward dead-copy elimination).** One right fold computes an
  over-approximate live set (all 15 GPs at every barrier and at the body
  end). A copy whose destination is not live — i.e. it is *fully* overwritten
  before any read, within the same segment — is dropped, as is a 64-bit
  self-copy `MOVQ d, d`. `mov` writes no flags, so dropping one never
  perturbs the CF/OF/ZF dataflow of a surrounding compare/carry chain.

## Conservatism (exactly what blocks propagation / deletion)

1. **Bare physical GPs only.** Facts are created and consulted only for the
   15 RA-pool names `RAX … R15` (never `RSP`). Spill (`k.N`), ABI-save
   (`qsave.X`), memory (`mem.<base>.<off>`), sentinel (`__cfflag`, `reg 1`)
   and array operands never participate — a copy touching any of them is
   left alone (this keeps the prologue/epilogue qsave stash/restore and every
   ABI boundary MOV byte-identical).
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
   (implicit `%rdx` multiplicand), the ADX family `ADCX`/`ADOX` and the
   phantom carry/high bindings `ADCXHI`/`ADOXHI`/`MULXHI` (whose write
   physically happens at the paired data op, and whose source lists are
   vestigial), `VPACK` (ZMM), and every mnemonic outside the recognized
   alphabet clear all facts and force all-live. `SETC` (explicit full write,
   reads only CF) and `CMOVcc` (explicit self-source) are recognized.
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
`d ↦ (s, w)` holds at program point `p` iff a recognized copy `MOV_w d, s`
executed at some `p₀ < p` in the same segment, and no instruction in
`(p₀, p)` wrote `d` or `s` (every recognized op writes registers only through
its explicit `.reg` destinations — ops with implicit register writes are
outside the alphabet and barrier the segment). Hence at `p` the machine
satisfies `d = s` (w = 64) or `low32 d = low32 s` (w = 32, and then
`high32 d = 0`). Rewriting a read source operand of effective
width ≤ w therefore reads the *identical value*, so the rewritten instruction
computes the same result and sets the same flags; skipped positions
(self-sources, address registers) keep the rendered text's read set intact.
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

Run this pass LAST, after any structural fuser (`AdxChainFuse.fuseAdxChain`,
`FheMontMulEmit.fuseMulHiLprog`): those match exact operand patterns
that a rewrite could break (their families are barriers here, so running
after them is also *safe*, merely less effective if run before). Wiring
pattern (per-emitter opt-in, byte-KAT before wider adoption):

```
def kernelAsm : String :=
  renderLprogAtt (LcmdCopyPropagate.copyPropagateLprog kernelLprog)
```
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (mnemWidth stripAbiTag parseImmShiftMnem)

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

/-- The recognized (non-barrier) `Lopn` mnemonic alphabet: the exact set whose
    operand read/write behaviour under `renderLopn` is modeled here. Everything
    else — `MULX`/`MULXMEM` (implicit `%rdx`), `ADCX`/`ADOX`/`ADCXHI`/`ADOXHI`/
    `MULXHI` (flag-threaded / phantom bindings), `VPACK`, unknowns — is a
    barrier. Immediate shifts/rotates (`SHL:n[:64]` …) are recognized via
    `parseImmShiftMnem` (checked FIRST: the count separator `:` collides with
    the `:8`/`:16`/`:64` width tags, the Hawk `SHR:16` pitfall). -/
def isRecognizedOpn (opn : String) : Bool :=
  (parseImmShiftMnem opn).isSome ||
  (match stripAbiTag opn with
   | "MOV" | "MOVQ" | "LOAD" | "STORE" | "LOADIDX" | "STOREIDX" | "LEA"
   | "ADD" | "SUB" | "MUL" | "AND" | "OR" | "XOR" | "ADC" | "SBB"
   | "SHL" | "SHR" | "SAR" | "CMP" | "TEST" | "ANDN" | "SETC"
   | "CMOVE" | "CMOVNE" | "CMOVB" | "CMOVAE" | "CMOVL" | "CMOVGE"
   | "CMOV" | "ZEROEXT" | "TRUNC" => true
   | _ => false)

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

/-- Is the (single) destination of this recognized op **write-only** — i.e.
    the rendered instruction never reads the destination's old value? The
    two-address ALU class (`ADD` … `CMOVcc`) reads its destination
    (`op s, d`), so it is NOT in this class; `CMP`/`TEST` are kept out
    conservatively. The 3-source select `CMOV` fully writes its destination
    (its self-alias cases are explicit source operands). -/
def isDstWriteOnly (opn : String) : Bool :=
  (parseImmShiftMnem opn).isSome ||
  (match stripAbiTag opn with
   | "MOV" | "MOVQ" | "LOAD" | "LOADIDX" | "LEA" | "SETC" | "CMOV"
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
    destinations, plus the destination itself when the op is read-modify-write
    or its write is partial (< 32 bits). -/
def instrUses (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    List String :=
  let srcReads := srcs.flatMap operandReads
  let dstAddrReads := dsts.flatMap fun o =>
    match o with
    | .reg n => if isPhysGP n then [] else nameReads n
    | o => operandReads o
  let rmwReads :=
    if isDstWriteOnly opn && 32 ≤ effWidth opn then [] else regDefsOf dsts
  srcReads ++ dstAddrReads ++ rmwReads

/-! ## 3. The copy shape -/

/-- Recognise a candidate reg→reg copy: `Lopn [.reg d] MOV/MOVQ/MOV:64
    [.reg s]` with both names bare physical GPs and width 32 or 64. Returns
    `(d, s, w)`. Narrow ABI MOVs (`MOV:16`/`MOV:8`, partial writes) and any
    copy touching a spill/qsave/mem/sentinel name are excluded. -/
def copyShape (i : Linstr) : Option (String × String × Nat) :=
  match i.li_i with
  | .Lopn [.reg d] opn [.reg s] =>
      if (parseImmShiftMnem opn).isNone
          && (stripAbiTag opn == "MOV" || stripAbiTag opn == "MOVQ")
          && isPhysGP d && isPhysGP s then
        let w := mnemWidth opn
        if w == 32 || w == 64 then some (d, s, w) else none
      else none
  | _ => none

/-! ## 4. Phase 1: forward copy propagation -/

/-- A copy fact `(d, s, w)`: register `d` currently holds the value copied
    from `s` at width `w` (64 ⇒ full equality; 32 ⇒ low-32 agreement and
    `d`'s high half zero). -/
abbrev CopyFact := String × String × Nat

/-- Drop every fact whose destination OR source is `r` (r was redefined). -/
def killFacts (facts : List CopyFact) (r : String) : List CopyFact :=
  facts.filter fun f => f.1 != r && f.2.1 != r

/-- Look up the propagation target for register `u`. -/
def lookupFact (facts : List CopyFact) (u : String) : Option (String × Nat) :=
  facts.findSome? fun f => if f.1 == u then some f.2 else none

/-- Rewrite one rewritable source operand: a bare physical GP `u` (not the
    instruction's own destination — the two-address self-source, rule 2) with
    a width-compatible fact `u ↦ (v, fw)` becomes `v`. Width gate (rule 3):
    a 64-bit fact rewrites anywhere; a 32-bit fact only where the consuming
    op's effective width is ≤ 32. All other operands pass through untouched
    (rule 5: never inside `mem.*`/`arrIdx`). -/
def rewriteOperand (facts : List CopyFact) (w : Nat) (dstSelf : Option String) :
    LOperand → LOperand
  | .reg u =>
      if isPhysGP u && dstSelf != some u then
        match lookupFact facts u with
        | some (v, fw) =>
            if fw == 64 || (fw == 32 && w ≤ 32) then .reg v else .reg u
        | none => .reg u
      else .reg u
  | op => op

/-- Forward propagation over one body. Barriers (control flow, unrecognized
    mnemonics) clear all facts and pass through untouched; recognized `Lopn`s
    have their sources rewritten, then kill the facts of every register they
    define, then (if a reg→reg copy) record their — already chained — fact. -/
def propagateAux : List CopyFact → Lcmd → Lcmd
  | _, [] => []
  | facts, i :: rest =>
      match i.li_i with
      | .Lopn dsts opn srcs =>
          if isRecognizedOpn opn then
            let dstSelf : Option String :=
              match dsts with
              | [.reg d] => if isPhysGP d then some d else none
              | _ => none
            let srcs' := srcs.map (rewriteOperand facts (effWidth opn) dstSelf)
            let i' : Linstr := { i with li_i := .Lopn dsts opn srcs' }
            let facts₁ := (regDefsOf dsts).foldl killFacts facts
            let facts₂ :=
              match copyShape i' with
              | some (d, s, w) => if d == s then facts₁ else (d, s, w) :: facts₁
              | none => facts₁
            i' :: propagateAux facts₂ rest
          else
            i :: propagateAux [] rest
      | _ => i :: propagateAux [] rest

/-! ## 5. Phase 2: backward dead-copy elimination -/

/-- Add registers to a (duplicate-free, ≤ 15 entry) live set. -/
def addRegs (live : List String) (rs : List String) : List String :=
  rs.foldl (fun l r => if l.contains r then l else r :: l) live

/-- One backward step of the liveness fold. State: `(live, acc)` where `live`
    over-approximates the registers whose current value may still be read
    (forward of this point) and `acc` is the already-processed suffix.

    * A barrier forces all-live (rule 7).
    * A candidate copy is dropped iff it is a 64-bit self-copy (`movq d, d`,
      a pure no-op) or its destination is not live; a *kept* copy uses its
      source and kills its destination like any other recognized op.
    * Every kept recognized op: `live := (live \ fullDefs) ∪ uses`. -/
def deadElimStep (i : Linstr) : List String × Lcmd → List String × Lcmd
  | (live, acc) =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        if isRecognizedOpn opn then
          let drop :=
            match copyShape i with
            | some (d, s, w) => (w == 64 && d == s) || !(live.contains d)
            | none => false
          if drop then (live, acc)
          else
            let live' :=
              addRegs (live.filter fun r => !((fullDefsOf dsts opn).contains r))
                (instrUses dsts opn srcs)
            (live', i :: acc)
        else (physGPs, i :: acc)
    | _ => (physGPs, i :: acc)

/-- Backward dead-copy elimination over one body (all registers live at the
    body end — ABI results and callee-saved restores are never victims). -/
def deadElimBody (body : Lcmd) : Lcmd :=
  (body.foldr deadElimStep (physGPs, [])).2

/-! ## 6. The pass -/

/-- Reg→reg copy propagation + dead-copy elimination on one owned-RA body:
    forward propagation (phase 1), then backward dead-copy drop (phase 2).
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

/-- Count the candidate reg→reg copies in a body (the orchestrator's
    before/after measurement hook). -/
def countRegRegCopies (body : Lcmd) : Nat :=
  (body.filter fun i => (copyShape i).isSome).length

/-- Total candidate reg→reg copies across an `Lprog`. -/
def countRegRegCopiesLprog (p : Lprog) : Nat :=
  (p.lp_funcs.map fun (_, f) => countRegRegCopies f.lfd_body).foldl (· + ·) 0

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

end CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
