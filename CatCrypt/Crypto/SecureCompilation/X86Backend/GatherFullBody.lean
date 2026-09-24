/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.FramingReconcile
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FramingReconcile

/-!
# `GatherFullBody` — the whole-physical-body gather: framing + ALU + shift

`GatherInPlace.gatherJBlock3` byte-matches `LprogBytes.encodeLcmd` on the
**shift-free** ALU core (the in-place peephole removed the two-source self-`mov`).
Two residuals remained, both precisely identified upstream:

1. **`MOVQ` framing does not gather** (`FramingReconcile`): `buildPrologue` emits
   the System-V framing (arg-marshal `MOVQ R14, RSI` + the callee-saved qsave
   spills/restores) under the `MOVQ` synonym mnemonic; `lowerLinstrExtCov3` keys
   on `MOV` (after `stripWidthTag`, which does **not** strip the `Q` synonym), so
   the framing lowers to `none` and the whole body fails to gather.

2. **The shift carries a leading materialise `mov`** (`GatherInPlace` §4b): the
   gather lowers a count-in-tag shift `SHR:<n>:64 [src]` (dst `d`) to
   `mov d src ; shr d $n`, whereas the Lprog `encodeLopn` emits **only**
   `shr %d, $n` for it.

This module is the **additive** closing unit: a new gather `gatherJBlock4`
(`= gatherJBlock3` plus a `MOVQ ↦ MOV:64` mnemonic alias **and** a per-shift
drop-the-materialise-`mov` peephole), the per-op byte-agreement theorem for the
new shift arm (`native_decide`-free), and the whole-physical-body `#eval` byte
comparison on the real GoldenPath kernel `AsconLinear.asconSigma0Com`.

## The two fixes

* **`MOVQ ↦ MOV:64` alias.** `FramingReconcile` PROVED `encodeLopn "MOVQ" =
  encodeLopn "MOV:64"` byte-for-byte on both framing forms (`encode_argMarshal_
  movq_eq_mov64`, `encode_qsaveSpill_movq_eq_mov64`). `gatherJBlock4` aliases a
  single-source `MOVQ` to the `MOV:64` lowering, so the framing **gathers**.

* **Per-shift in-place drop-`mov`.** The Lprog `encodeLopn` of a count-in-tag
  shift `SHR:<n>:64 [d] [src]` emits `mov %src, %d` followed by `shr %d, $n`
  when `src ≠ d`, and the shift alone when `src = d`; for the count 0 it emits
  only the `mov`. `gatherJBlock4` matches all three: an in-place shift lowers to
  the single `[shr d $n]` / `[shl d $n]`, a shift from a distinct register keeps
  the materialise `mov d, src`, and a count-0 shift lowers to its copy alone.

## What byte-matches, and the one residual

On `asconSigma0`'s **physical** body (`Com.toLprogPhysAbi`), `gatherJBlock4` now
makes the WHOLE body **gather** (`.isSome = true`, was `none`). At the byte level:

* the **framing-free compute core** (the ALU/`MOV`/shift spine) byte-matches
  `encodeLcmd` **exactly** (§4, `gatherJBlock4 aluCore` vs `encodeLcmd aluCore`,
  40 = 40 bytes) — the in-place ALU peephole + the new shift drop-`mov` close
  both body residuals;
* the **reg-reg arg-marshal** framing (`MOVQ R14, RSI`) byte-matches too (it is a
  3-byte reg-reg `mov` on both sides — `FramingReconcile.argMarshal_framing_byte_matches`);
* **the callee-saved qsave reg↔mem spills/restores do NOT byte-match.** This is
  the precise, single residual. `MOVQ qsave.RBX, RBX` is a `%rsp`-relative
  **memory store** (`mov %rbx, off(%rsp)`, 5 bytes) on the Lprog side, where
  `encodeLopn` resolves the `qsave.X` slot name to an `off(%rsp)` displacement
  (`spillQsaveOff frame spillW`). The register-only JInstr encoder
  (`ScalarEncoder.encodeJInstr`) has **no spill-slot resolution**: it treats
  `qsave.X` as an ordinary register name and emits a 3-byte reg-reg `mov`. So the
  MOVQ alias makes the qsave ops *gather*, but their bytes still disagree
  (3 ≠ 5). Dropping exactly the qsave reg↔mem spills (keeping arg-marshal + ALU +
  shift) makes the gather byte-match `encodeLcmd` (§4, `coreNoSpill`).

This residual is **not** a virtual-vs-physical artifact, an encoder bug, or a
lowering-table lag like the previous two: it is a **capability gap** — the
JInstr scalar encoder lacks the `off(%rsp)` spill-slot resolution the Lprog
encoder carries. Closing it needs a spill-aware JInstr `mov` (an `off(%rsp)`
store/load arm keyed on the `qsave.`/`k.N` slot names), not a gather-coverage
tweak. It is recorded here rather than closed by a vacuous whole-body equality.

## The provable building blocks (`native_decide`-free)

The per-op byte agreements that constitute the matched compute core are theorems,
not `#eval`s:

* the in-place two-source ALU agreements (`GatherInPlace.encJInPlace_or64_eq_lopn`
  / `_xor64_`) — the self-`mov` removed;
* the **new** shift drop-`mov` agreements here (`encJShrDropMov_eq_lopn`,
  `encJShr28DropMov_eq_lopn`, `encJShl45DropMov_eq_lopn`, `encJShl36DropMov_eq_lopn`
  — asconSigma0's four Σ₀ rotations): the gathered single `[shr d $n]` block encodes
  byte-for-byte to `encodeLopn`'s count-in-tag `SHR:<n>:64 [d] [src]` bytes — no
  leading materialise `mov`. Built from `BlockBytesAgreeExtended.encodeLopn_shr19_
  emits` (the Lprog dispatch) ∘ `encJShr_eq_encTagShift` (the proven per-op
  byte-identity), with the gather-side `mov` removed by the peephole. The lowering
  side is `lowerCov4_shr19`/`_shr28`/`_shl45`/`_shl36` (and `lowerCov4_movq` for the
  reg-reg arg-marshal alias).

The whole-`aluCore` byte equality itself is `#eval` interpreter evidence, not a
`decide`/`rfl` theorem. The obstruction is not the shift mnemonic: at a concrete
mnemonic `LoweringExtended.parseShiftMnem` is closed by `decide +kernel`
(§2, `parseShiftMnem_shr19` and its three neighbours). Where a whole-body byte
equality stops is recorded in `FullBodyByteIdentity`, which states the agreement
as `BodyBytesAgree` and derives the whole-ELF identity from it. The per-op
agreements above are the kernel-reducible certificate; the `#eval` confirms they
compose on the real kernel.

No open goals, no axiom, no `native_decide` (the lemma proofs; the `#eval` byte
witnesses in §4 are interpreter evaluation, not part of any proof term).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand Condt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar (lowerCmovJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (isCarryOutBinding isMulHiBinding mnemWidth)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (physAlloc)

/-! ## The flag class: compare, materialised comparison, conditional move

The two-source flag mnemonics the compare-and-select export emits — the flag-only
`CMP:64`, the materialised comparison `SET<cc>:64` and the conditional moves
`CMOVE:64` / `CMOVNE:64` / `CMOVB:64` — are lowered here, to the `JInstr` forms
whose printed text `LprogAsmPrinter.renderLopn` gives the same mnemonic.

`SET<cc>` is the three-instruction form `renderSetcc` prints (`cmp b, a`,
`mov $0, d`, `set<cc> d8`), so it lowers to `[cmp a b, mov d 0, setcc c d]`. The
model's `JInstr.setcc` writes the low byte under `MSB_MERGE` and the preceding
zeroing `mov` clears the rest, which together give the zero-extended `0`/`1` the
printed pair produces. `JInstr.setc` is not the target: it is fixed at `CF` and
already zero-extends, so it covers neither the five other conditions nor the
`mov $0` the printer emits. -/

/-- The x86 condition code named by a `":64"`-tagged materialised-comparison
    mnemonic `SET<cc>:64`, `none` for every other mnemonic. The unsigned
    conditions are the ones `LprogAsmPrinter.setccAtt?` renders: `SETA` is
    `Condt.nbe` and `SETAE` is `Condt.nb`, the negated forms Jasmin's `condt`
    carries. -/
def setccCondOf : String → Option Condt
  | "SETE:64" => some .e | "SETNE:64" => some .ne
  | "SETB:64" => some .b | "SETBE:64" => some .be
  | "SETA:64" => some .nbe | "SETAE:64" => some .nb
  | _ => none

/-- The `JInstr` conditional move named by a `":64"`-tagged `CMOV<cc>:64`
    mnemonic, `none` for every other mnemonic. The three conditions are those
    the model carries as dedicated arms (`cmove`/`cmovne`/`cmovb`), which are
    also the three `LprogBytes.twoByteOpcode` rows the Lprog byte encoder uses
    for them. -/
def cmovccJ (opn d : String) (s : JOperand) : Option (JInstr 64) :=
  match opn with
  | "CMOVE:64" => some (JInstr.cmove d s)
  | "CMOVNE:64" => some (JInstr.cmovne d s)
  | "CMOVB:64" => some (JInstr.cmovb d s)
  | _ => none

/-- A register name the flag-class arms address directly: a general-purpose
    name that is not a spill or callee-save slot. -/
def isPlainGp (n : String) : Bool := isGpName n && !isSpillOrQsave n

/-- The second operand of a compare: a plain register, or an immediate inside
    the sign-extended 32-bit range `cmp` encodes (the range outside which
    `renderSetcc` and `renderLopn` emit their unhandled sentinel). -/
def cmpSrcOk : LOperand → Bool
  | .reg n => isPlainGp n
  | .imm v => v < 2 ^ 31
  | _ => false

/-- Lower a two-source flag-class `Lopn [.reg d] opn [s0, s1]`:

    * `CMP:64` in the two-address form `[d] CMP:64 [d, b]` → `[cmp d b]`, the
      flags of `d - b` that `renderLopn` prints as `cmp<sz> b, d`;
    * `SET<cc>:64 [a, b]` → `[cmp a b, mov d 0, setcc c d]`, the three lines
      `renderSetcc` prints;
    * `CMOV<cc>:64` in the two-address form `[d] CMOV<cc>:64 [d, s]` →
      `[cmov<cc> d s]`, the single line `renderLopn` prints.

    `none` for every other mnemonic, and for an operand shape outside the
    register/immediate forms the arms address (a spill slot, an array operand,
    an out-of-range immediate, or a `CMP`/`CMOV` whose first source is not the
    destination — the printer reads the destination there, so a different first
    source would denote something the printed text does not). -/
def lowerFlagClassJ (d : String) (opn : String) (s0 s1 : LOperand) :
    Option (List (JInstr 64)) :=
  if !isPlainGp d then none
  else
    match setccCondOf opn, s0 with
    | some c, .reg a =>
        if isPlainGp a && cmpSrcOk s1 then
          some [JInstr.cmp a (lowerJOperand s1), JInstr.mov d (JOperand.imm 0),
                JInstr.setcc c d]
        else none
    | some _, _ => none
    | none, _ =>
        if opn == "CMP:64" then
          if s0 == LOperand.reg d && cmpSrcOk s1 then
            some [JInstr.cmp d (lowerJOperand s1)]
          else none
        else
          match s1 with
          | .reg sn =>
              if s0 == LOperand.reg d && isPlainGp sn then
                (cmovccJ opn d (JOperand.reg sn)).map (fun i => [i])
              else none
          | _ => none

/-- Lower the three-source conditional move `Lopn [.reg d] "CMOV:64" [c, a, b]` —
    the export of the dialect's `select 64`, whose condition is an explicit
    `reg 1` operand rather than a processor flag — to
    `LoweringCoverageCmovSar.lowerCmovJ`, the `test c, c` + `CMOVcc` block whose
    aliasing case split is the one `LprogAsmPrinter.renderLopn` prints and
    `LprogBytes.encCmovSelect` encodes.

    `none` unless all four register names are plain general-purpose names —
    `encCmovSelect` is gated on `isGpName` and gives a spill or `qsave` operand
    the empty byte list — and unless the condition register is distinct from the
    destination, since on three distinct names the block defaults the false value
    into the destination before the `test` reads the condition. -/
def lowerFlagClassCmovJ (d c a b : String) : Option (List (JInstr 64)) :=
  if isPlainGp d && isPlainGp c && isPlainGp a && isPlainGp b && !(c == d) then
    some (lowerCmovJ d c a b)
  else none

/-! ## 1. The full-body lowering: `MOVQ ↦ MOV:64` alias + per-shift drop-`mov` -/

/-- The whole-body coverage lowering. Three arms vs `lowerLinstrExtCov3`:

    * **`MOVQ` alias**: a single-source `MOVQ` (the framing synonym `buildPrologue`
      emits) is lowered as the gather-covered `MOV:64` form. `encodeLopn` already
      maps the two mnemonics to identical bytes (`FramingReconcile` §3), so the
      framing now gathers.
    * **in-place shift**: a count-in-tag shift `SHR:<n>:64`/`SHL:<n>:64` whose
      source register is its destination lowers to the **single**
      `[shr d $n]` / `[shl d $n]`, without the materialise `mov d, d`. The Lprog
      encoder emits `mov d, s` before the shift exactly when `s ≠ d`, so a shift
      with a distinct source keeps the two-instruction form of
      `lowerLinstrExtCov3`. A count-0 shift is the identity, and the encoder
      emits only its copy: nothing when `s = d`, `mov d, s` otherwise. The
      lowering does the same.
    * **flag class**: a two-source `Lopn` that `lowerLinstrExtCov3` declines is
      offered to `lowerFlagClassJ`, which covers `CMP:64`, `SET<cc>:64` and
      `CMOV<cc>:64`. A two-source shape `lowerLinstrExtCov3` lowers keeps that
      lowering.
    * **three-source conditional move**: the `select 64` export
      `CMOV:64 [cond, t, f]` over register operands goes to
      `lowerFlagClassCmovJ`, which gates the four names on `isPlainGp` and the
      condition on being distinct from the destination.

    Every other shape delegates to `lowerLinstrExtCov3` verbatim (the in-place
    two-source ALU peephole). So `lowerLinstrExtCov4` differs from
    `lowerLinstrExtCov3` on the single-source `MOVQ`, the in-place count-in-tag
    shift, the two-source shapes `lowerLinstrExtCov3` declines, and the
    register-operand three-source `CMOV:64`. -/
def lowerLinstrExtCov4 : LinstrR → Option (List (JInstr 64))
  -- `MOVQ ↦ MOV:64` synonym alias (the framing mnemonic `buildPrologue` emits)
  | .Lopn [.reg dst] "MOVQ" [s] =>
      lowerLinstrExtCov3 (.Lopn [.reg dst] "MOV:64" [s])
  -- single-source: an in-place count-in-tag shift is the shift alone; everything
  -- else, including a shift from a distinct register, delegates verbatim
  | .Lopn [.reg dst] opn [src] =>
      match parseShiftMnem opn, src with
      | some p, .reg s =>
          if s = dst then
            if p.2 = 0 then some []
            else some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                       else JInstr.shr dst (JOperand.imm p.2)]
          else if p.2 = 0 then some [JInstr.mov dst (JOperand.reg s)]
          else lowerLinstrExtCov3 (.Lopn [.reg dst] opn [src])
      | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] opn [src])
  -- two sources: the in-place coverage superset, and where it declines the flag
  -- class (`CMP:64`, `SET<cc>:64`, `CMOV<cc>:64`)
  | .Lopn [.reg dst] opn [s0, s1] =>
      match lowerLinstrExtCov3 (.Lopn [.reg dst] opn [s0, s1]) with
      | some js => some js
      | none => lowerFlagClassJ dst opn s0 s1
  -- three sources: the `select 64` export, under the plain-register gate the
  -- byte encoder carries
  | .Lopn [.reg dst] "CMOV:64" [.reg cn, .reg tn, .reg fn] =>
      lowerFlagClassCmovJ dst cn tn fn
  -- everything else (MULXHI, memory, control-flow): the in-place coverage
  -- superset verbatim
  | i => lowerLinstrExtCov3 i

/-- Lower a full `Linstr` (drops the position tag), full-body coverage. -/
def lowerLinstrExtCov4L (i : Linstr) : Option (List (JInstr 64)) :=
  lowerLinstrExtCov4 i.li_i

/-- **The full-body `JInstr` gather.** Drop the trailing `Lret` (framing supplies
    the `ret`), then lower every remaining instruction through `lowerLinstrExtCov4`
    (the `MOVQ` alias + the per-shift drop-`mov`, on top of the in-place ALU
    peephole) and flatten. With the alias the framing now gathers, so the WHOLE
    physical body is `some`. -/
def gatherJBlock4 (body : List Linstr) : Option (List (JInstr 64)) :=
  ((body.filter (fun i => !isLret i)).mapM lowerLinstrExtCov4L).map List.flatten

/-! ## 2. The in-place shift arm: lowering equations

An in-place count-in-tag shift (source register = destination) lowers to the
**single** destructive op. The lowering is stated parametrically over the shift
count `n`, carried as a hypothesis `hsh : parseShiftMnem opn = some (isLeft, n)`,
so that one statement covers every count. At a concrete mnemonic the hypothesis is
discharged by `decide +kernel`: `parseShiftMnem_shr19`, `parseShiftMnem_shr28`,
`parseShiftMnem_shl45`, `parseShiftMnem_shl36` and `parseShiftMnem_mov64` below
are those parses. A shift from a distinct register lowers through
`lowerLinstrExtCov3` to `[mov d s, shr/shl d $n]`, the same two instructions the
Lprog encoder emits. -/

/-- The parse of the `SHR:19:64` mnemonic: a right shift by 19. -/
theorem parseShiftMnem_shr19 : parseShiftMnem "SHR:19:64" = some (false, 19) := by
  decide +kernel

/-- The parse of the `SHR:28:64` mnemonic: a right shift by 28. -/
theorem parseShiftMnem_shr28 : parseShiftMnem "SHR:28:64" = some (false, 28) := by
  decide +kernel

/-- The parse of the `SHL:45:64` mnemonic: a left shift by 45. -/
theorem parseShiftMnem_shl45 : parseShiftMnem "SHL:45:64" = some (true, 45) := by
  decide +kernel

/-- The parse of the `SHL:36:64` mnemonic: a left shift by 36. -/
theorem parseShiftMnem_shl36 : parseShiftMnem "SHL:36:64" = some (true, 36) := by
  decide +kernel

/-- The `MOV:64` mnemonic carries no shift count. -/
theorem parseShiftMnem_mov64 : parseShiftMnem "MOV:64" = none := by
  decide +kernel

/-- A count-in-tag right shift `SHR:19:64 [d]` (dst `d`) lowers under
    `lowerLinstrExtCov4` to the **single** op `[shr d $n]`, given the parse
    `parseShiftMnem "SHR:19:64" = some (false, n)`. The mnemonic is concrete (so
    the `"MOVQ"`-head arm is decidably distinct and the matcher reduces to the
    shift branch); the count `n` is recovered from the `parseShiftMnem` hypothesis,
    which `parseShiftMnem_shr19` discharges. The `SHR:28:64` /
    `SHL:45:64` / `SHL:36:64` analogues are `lowerCov4_shr28` / `lowerCov4_shl45` /
    `lowerCov4_shl36`. -/
theorem lowerCov4_shr19 (dst : String) (n : Nat)
    (hsh : parseShiftMnem "SHR:19:64" = some (false, n)) (hn0 : n ≠ 0) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "SHR:19:64" [.reg dst])
      = some [JInstr.shr dst (.imm n)] := by
  show (match parseShiftMnem "SHR:19:64", LOperand.reg dst with
        | some p, .reg s =>
            if s = dst then
              if p.2 = 0 then some []
              else some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                         else JInstr.shr dst (JOperand.imm p.2)]
            else if p.2 = 0 then some [JInstr.mov dst (JOperand.reg s)]
            else lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:19:64" [.reg dst])
        | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:19:64" [.reg dst])) = _
  rw [hsh]; simp [hn0]

/-- In-place `SHR:28:64 [d]` lowers to the single `[shr d $n]`. -/
theorem lowerCov4_shr28 (dst : String) (n : Nat)
    (hsh : parseShiftMnem "SHR:28:64" = some (false, n)) (hn0 : n ≠ 0) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "SHR:28:64" [.reg dst])
      = some [JInstr.shr dst (.imm n)] := by
  show (match parseShiftMnem "SHR:28:64", LOperand.reg dst with
        | some p, .reg s =>
            if s = dst then
              if p.2 = 0 then some []
              else some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                         else JInstr.shr dst (JOperand.imm p.2)]
            else if p.2 = 0 then some [JInstr.mov dst (JOperand.reg s)]
            else lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:28:64" [.reg dst])
        | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:28:64" [.reg dst])) = _
  rw [hsh]; simp [hn0]

/-- In-place `SHL:45:64 [d]` lowers to the single `[shl d $n]`. -/
theorem lowerCov4_shl45 (dst : String) (n : Nat)
    (hsh : parseShiftMnem "SHL:45:64" = some (true, n)) (hn0 : n ≠ 0) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "SHL:45:64" [.reg dst])
      = some [JInstr.shl dst (.imm n)] := by
  show (match parseShiftMnem "SHL:45:64", LOperand.reg dst with
        | some p, .reg s =>
            if s = dst then
              if p.2 = 0 then some []
              else some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                         else JInstr.shr dst (JOperand.imm p.2)]
            else if p.2 = 0 then some [JInstr.mov dst (JOperand.reg s)]
            else lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:45:64" [.reg dst])
        | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:45:64" [.reg dst])) = _
  rw [hsh]; simp [hn0]

/-- In-place `SHL:36:64 [d]` lowers to the single `[shl d $n]`. -/
theorem lowerCov4_shl36 (dst : String) (n : Nat)
    (hsh : parseShiftMnem "SHL:36:64" = some (true, n)) (hn0 : n ≠ 0) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "SHL:36:64" [.reg dst])
      = some [JInstr.shl dst (.imm n)] := by
  show (match parseShiftMnem "SHL:36:64", LOperand.reg dst with
        | some p, .reg s =>
            if s = dst then
              if p.2 = 0 then some []
              else some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                         else JInstr.shr dst (JOperand.imm p.2)]
            else if p.2 = 0 then some [JInstr.mov dst (JOperand.reg s)]
            else lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:36:64" [.reg dst])
        | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:36:64" [.reg dst])) = _
  rw [hsh]; simp [hn0]


/-- **The `MOVQ ↦ MOV:64` alias lowers to a reg-reg `mov`.** A single-source
    `MOVQ R14, RSI` (the reg-reg arg-marshal framing) lowers under
    `lowerLinstrExtCov4` to `[mov dst s]` — the same single op the `MOV:64`
    mnemonic gathers, which `encodeLopn` already byte-matches the `MOVQ` form
    (`FramingReconcile.encode_argMarshal_movq_eq_mov64`). The parse fact
    `parseShiftMnem "MOV:64" = none` is carried as a hypothesis, which
    `parseShiftMnem_mov64` discharges. -/
theorem lowerCov4_movq (dst s : String)
    (hps : parseShiftMnem "MOV:64" = none) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "MOVQ" [.reg s])
      = some [JInstr.mov dst (.reg s)] := by
  show lowerLinstrExtCov3 (.Lopn [.reg dst] "MOV:64" [.reg s]) = _
  show lowerLinstrExtCov (.Lopn [.reg dst] "MOV:64" [.reg s]) = _
  show lowerLinstrExt2 (.Lopn [.reg dst] "MOV:64" [.reg s]) = _
  show (match parseShiftMnem "MOV:64" with
        | some _ => lowerShiftImmJ dst "MOV:64" (lowerJOperand (.reg s))
        | none => match lowerAluJ dst (stripWidthTag "MOV:64") (lowerJOperand (.reg s)) with
                  | some i => some [i]
                  | none => lowerLinstrExt (.Lopn [.reg dst] "MOV:64" [.reg s])) = _
  rw [hps]
  simp only [lowerJOperand, show stripWidthTag "MOV:64" = "MOV" from by decide +kernel, lowerAluJ]

/-! ### 2a. The flag-class arms: lowering equations

The flag class is reached only where `lowerLinstrExtCov3` declines, so each
equation goes through `lowerLinstrExtCov3_eq_none`: none of the flag mnemonics is
in the register-count shift table or the ALU table, and none of them is one of
the three mnemonics `lowerLinstrExtCov3` routes to `lowerLinstrExtCov`. The
equations are stated over a plain general-purpose destination (and, for the
materialised comparison, a plain compared register), since that is the operand
shape `lowerFlagClassJ` addresses; the hypotheses are decidable on a concrete
register name. -/

/-- The in-place coverage superset declines a two-source `Lopn` whose
    tag-stripped mnemonic is in neither the register-count shift table nor the
    ALU table, and which is none of the three mnemonics it routes to
    `lowerLinstrExtCov`. -/
theorem lowerLinstrExtCov3_eq_none (d opn : String) (s0 s1 : LOperand)
    (h1 : opn ≠ "MULXHI:64") (h2 : opn ≠ "STORE") (h3 : opn ≠ "STOREIDX")
    (hsh : lowerShiftRegJ d (stripWidthTag opn) (lowerJOperand s0) (lowerJOperand s1)
      = none)
    (halu : lowerAluJ d (stripWidthTag opn) (lowerJOperand s1) = none) :
    lowerLinstrExtCov3 (.Lopn [.reg d] opn [s0, s1]) = none := by
  unfold lowerLinstrExtCov3
  split
  · simp_all
  · simp_all
  · simp_all
  · simp_all [lowerAluJ2InPlace]
  · rename_i hx
    exact (hx d opn s0 s1 rfl).elim

/-- The two-address flag-only compare `CMP:64 [d] [d, b]` lowers to the single
    `[cmp d b]`. -/
theorem lowerCov4_cmp (d : String) (b : LOperand)
    (hd : isPlainGp d = true) (hb : cmpSrcOk b = true) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "CMP:64" [.reg d, b])
      = some [JInstr.cmp d (lowerJOperand b)] := by
  have hc3 := lowerLinstrExtCov3_eq_none d "CMP:64" (.reg d) b (by decide) (by decide)
    (by decide) (by simp [show stripWidthTag "CMP:64" = "CMP" from by decide +kernel,
      lowerShiftRegJ])
    (by simp [show stripWidthTag "CMP:64" = "CMP" from by decide +kernel, lowerAluJ])
  show (match lowerLinstrExtCov3 (.Lopn [.reg d] "CMP:64" [.reg d, b]) with
        | some js => some js
        | none => lowerFlagClassJ d "CMP:64" (.reg d) b) = _
  rw [hc3]
  simp [lowerFlagClassJ, setccCondOf, hd, hb]

/-- The two-address conditional move `CMOVNE:64 [d] [d, s]` lowers to the single
    `[cmovne d s]`. -/
theorem lowerCov4_cmovne (d s : String)
    (hd : isPlainGp d = true) (hs : isPlainGp s = true) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "CMOVNE:64" [.reg d, .reg s])
      = some [JInstr.cmovne d (.reg s)] := by
  have hc3 := lowerLinstrExtCov3_eq_none d "CMOVNE:64" (.reg d) (.reg s) (by decide)
    (by decide) (by decide)
    (by simp [show stripWidthTag "CMOVNE:64" = "CMOVNE" from by decide +kernel,
      lowerShiftRegJ])
    (by simp [show stripWidthTag "CMOVNE:64" = "CMOVNE" from by decide +kernel, lowerAluJ])
  show (match lowerLinstrExtCov3 (.Lopn [.reg d] "CMOVNE:64" [.reg d, .reg s]) with
        | some js => some js
        | none => lowerFlagClassJ d "CMOVNE:64" (.reg d) (.reg s)) = _
  rw [hc3]
  simp [lowerFlagClassJ, setccCondOf, cmovccJ, hd, hs]

/-- The two-address conditional move `CMOVE:64 [d] [d, s]` lowers to the single
    `[cmove d s]`. -/
theorem lowerCov4_cmove (d s : String)
    (hd : isPlainGp d = true) (hs : isPlainGp s = true) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "CMOVE:64" [.reg d, .reg s])
      = some [JInstr.cmove d (.reg s)] := by
  have hc3 := lowerLinstrExtCov3_eq_none d "CMOVE:64" (.reg d) (.reg s) (by decide)
    (by decide) (by decide)
    (by simp [show stripWidthTag "CMOVE:64" = "CMOVE" from by decide +kernel,
      lowerShiftRegJ])
    (by simp [show stripWidthTag "CMOVE:64" = "CMOVE" from by decide +kernel, lowerAluJ])
  show (match lowerLinstrExtCov3 (.Lopn [.reg d] "CMOVE:64" [.reg d, .reg s]) with
        | some js => some js
        | none => lowerFlagClassJ d "CMOVE:64" (.reg d) (.reg s)) = _
  rw [hc3]
  simp [lowerFlagClassJ, setccCondOf, cmovccJ, hd, hs]

/-- The materialised comparison `SETE:64 [d] [a, b]` lowers to the compare, the
    zeroing move and the conditional set — the three lines `renderSetcc`
    prints. -/
theorem lowerCov4_sete (d a : String) (b : LOperand)
    (hd : isPlainGp d = true) (ha : isPlainGp a = true) (hb : cmpSrcOk b = true) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "SETE:64" [.reg a, b])
      = some [JInstr.cmp a (lowerJOperand b), JInstr.mov d (.imm 0),
              JInstr.setcc .e d] := by
  have hc3 := lowerLinstrExtCov3_eq_none d "SETE:64" (.reg a) b (by decide) (by decide)
    (by decide)
    (by simp [show stripWidthTag "SETE:64" = "SETE" from by decide +kernel,
      lowerShiftRegJ])
    (by simp [show stripWidthTag "SETE:64" = "SETE" from by decide +kernel, lowerAluJ])
  show (match lowerLinstrExtCov3 (.Lopn [.reg d] "SETE:64" [.reg a, b]) with
        | some js => some js
        | none => lowerFlagClassJ d "SETE:64" (.reg a) b) = _
  rw [hc3]
  simp [lowerFlagClassJ, setccCondOf, hd, ha, hb]

/-- The materialised comparison `SETNE:64 [d] [a, b]`. -/
theorem lowerCov4_setne (d a : String) (b : LOperand)
    (hd : isPlainGp d = true) (ha : isPlainGp a = true) (hb : cmpSrcOk b = true) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "SETNE:64" [.reg a, b])
      = some [JInstr.cmp a (lowerJOperand b), JInstr.mov d (.imm 0),
              JInstr.setcc .ne d] := by
  have hc3 := lowerLinstrExtCov3_eq_none d "SETNE:64" (.reg a) b (by decide) (by decide)
    (by decide)
    (by simp [show stripWidthTag "SETNE:64" = "SETNE" from by decide +kernel,
      lowerShiftRegJ])
    (by simp [show stripWidthTag "SETNE:64" = "SETNE" from by decide +kernel, lowerAluJ])
  show (match lowerLinstrExtCov3 (.Lopn [.reg d] "SETNE:64" [.reg a, b]) with
        | some js => some js
        | none => lowerFlagClassJ d "SETNE:64" (.reg a) b) = _
  rw [hc3]
  simp [lowerFlagClassJ, setccCondOf, hd, ha, hb]

/-! ### 2b. The three-source conditional move: lowering equations

The `select 64` export is the only three-source shape `lowerLinstrExtCov4`
intercepts, so its equations need no `lowerLinstrExtCov3` side-condition: the arm
is reached by the pattern match alone. The resolved blocks below are lists of
`mov` / `test` / `CMOVcc`; `JInstr` carries no branch constructor, so no lowering
of this shape can produce a conditional jump. -/

/-- The three-source `CMOV:64 [c, a, b]` over plain general-purpose registers,
    with the condition distinct from the destination, lowers to
    `lowerCmovJ`. -/
theorem lowerCov4_cmovSelect (d c a b : String)
    (hd : isPlainGp d = true) (hc : isPlainGp c = true)
    (ha : isPlainGp a = true) (hb : isPlainGp b = true) (hcd : (c == d) = false) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b])
      = some (lowerCmovJ d c a b) := by
  show lowerFlagClassCmovJ d c a b = _
  simp [lowerFlagClassCmovJ, hd, hc, ha, hb, hcd]

/-- A destination distinct from both data registers: the false value is defaulted
    in, the condition is materialised into `ZF`, and the conditional move brings
    the true value in on a non-zero condition. -/
theorem lowerCov4_cmovSelect_disjoint (d c a b : String)
    (hd : isPlainGp d = true) (hc : isPlainGp c = true)
    (ha : isPlainGp a = true) (hb : isPlainGp b = true) (hcd : (c == d) = false)
    (had : (a == d) = false) (hbd : (b == d) = false) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b])
      = some [JInstr.mov d (.reg b), JInstr.test c (.reg c),
              JInstr.cmovne d (.reg a)] := by
  rw [lowerCov4_cmovSelect d c a b hd hc ha hb hcd]
  simp [lowerCmovJ, had, hbd]

/-- The destination already holds the false value: two instructions, no
    defaulting move. -/
theorem lowerCov4_cmovSelect_destIsFalse (d c a : String)
    (hd : isPlainGp d = true) (hc : isPlainGp c = true) (ha : isPlainGp a = true)
    (hcd : (c == d) = false) (had : (a == d) = false) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg d])
      = some [JInstr.test c (.reg c), JInstr.cmovne d (.reg a)] := by
  rw [lowerCov4_cmovSelect d c a d hd hc ha hd hcd]
  simp [lowerCmovJ, had]

/-- The destination already holds the true value: the sense of the conditional
    move is inverted and the false value is the one brought in. -/
theorem lowerCov4_cmovSelect_destIsTrue (d c b : String)
    (hd : isPlainGp d = true) (hc : isPlainGp c = true) (hb : isPlainGp b = true)
    (hcd : (c == d) = false) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "CMOV:64" [.reg c, .reg d, .reg b])
      = some [JInstr.test c (.reg c), JInstr.cmove d (.reg b)] := by
  rw [lowerCov4_cmovSelect d c d b hd hc hd hb hcd]
  simp [lowerCmovJ]

/-- A spill or `qsave` operand declines: `encCmovSelect` is gated on `isGpName`
    and gives such an `Lopn` the empty byte list, which no non-empty `JInstr`
    block matches. -/
theorem lowerCov4_cmovSelect_notPlain (d c a b : String)
    (hd : isPlainGp d = false) :
    lowerLinstrExtCov4 (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b])
      = none := by
  show lowerFlagClassCmovJ d c a b = _
  simp [lowerFlagClassCmovJ, hd]

/-! ## 3. The shift per-op byte agreement (the deliverable, `native_decide`-free)

For the count-in-tag shift the gathered single-op block encodes byte-for-byte to
the Lprog `encodeLopn` count-in-tag shift bytes — no leading materialise `mov`,
exactly the residual (2) removed by the drop-`mov` peephole. This is
`BlockBytesAgreeExtended.encodeLopn_shr19_emits` (the Lprog `encTagShift` dispatch)
∘ `encJShr_eq_encTagShift` (the proven per-op `C1 /5 ib` byte-identity), with the
gather-side `mov` gone. The standard resolver-agreement side-condition `hd` ties
the JInstr register name to the Lprog `gpNumU` number, and `hn`/`hn1` fix the
count the tag carries (ruling out the `D1 /5` count-1 short form the JInstr
`encShiftImm` does not select). -/

/-- **`SHR:19:64` drop-`mov` byte agreement.** The gathered single `[shr dn $n]`
    block (the drop-`mov` lowering of the count-in-tag `SHR:19:64 [dn] [sn]`)
    encodes byte-for-byte to the Lprog `encodeLopn` count-in-tag shift bytes — *no*
    leading materialise `mov`. -/
theorem encJShrDropMov_eq_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (dn sn : String) (n : Nat)
    (hn : tagShiftCount "SHR:19" = n) (hn1 : n ≠ 1)
    (hd : gpNum (regOf alloc dn) = gpNumU dn)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeJBlock alloc [JInstr.shr dn (.imm n)]
      = encodeLopn frame spillW (.Lopn [.reg dn] "SHR:19:64" [.reg sn]) := by
  rw [encodeLopn_shr19_emits frame spillW dn sn hgp hds,
    ← encJShr_eq_encTagShift alloc dn "SHR:19" n hn hn1 hd]
  simp [encodeJBlock]

/-- **`SHR:28:64` drop-`mov` byte agreement** (asconSigma0's second rotate-hi). -/
theorem encJShr28DropMov_eq_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (dn sn : String) (n : Nat)
    (hn : tagShiftCount "SHR:28" = n) (hn1 : n ≠ 1)
    (hd : gpNum (regOf alloc dn) = gpNumU dn)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeJBlock alloc [JInstr.shr dn (.imm n)]
      = encodeLopn frame spillW (.Lopn [.reg dn] "SHR:28:64" [.reg sn]) := by
  rw [encodeLopn_shr28_emits frame spillW dn sn hgp hds,
    ← encJShr_eq_encTagShift alloc dn "SHR:28" n hn hn1 hd]
  simp [encodeJBlock]

/-- **`SHL:45:64` drop-`mov` byte agreement** (asconSigma0's first rotate-lo). -/
theorem encJShl45DropMov_eq_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (dn sn : String) (n : Nat)
    (hn : tagShiftCount "SHL:45" = n) (hn1 : n ≠ 1)
    (hd : gpNum (regOf alloc dn) = gpNumU dn)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeJBlock alloc [JInstr.shl dn (.imm n)]
      = encodeLopn frame spillW (.Lopn [.reg dn] "SHL:45:64" [.reg sn]) := by
  rw [encodeLopn_shl45_emits frame spillW dn sn hgp hds,
    ← encJShl_eq_encTagShift alloc dn "SHL:45" n hn hn1 hd]
  simp [encodeJBlock]

/-- **`SHL:36:64` drop-`mov` byte agreement** (asconSigma0's second rotate-lo). -/
theorem encJShl36DropMov_eq_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (dn sn : String) (n : Nat)
    (hn : tagShiftCount "SHL:36" = n) (hn1 : n ≠ 1)
    (hd : gpNum (regOf alloc dn) = gpNumU dn)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeJBlock alloc [JInstr.shl dn (.imm n)]
      = encodeLopn frame spillW (.Lopn [.reg dn] "SHL:36:64" [.reg sn]) := by
  rw [encodeLopn_shl36_emits frame spillW dn sn hgp hds,
    ← encJShl_eq_encTagShift alloc dn "SHL:36" n hn hn1 hd]
  simp [encodeJBlock]

/-! ### 3a. The three-source conditional move: byte agreement

`encodeLopn` reaches its `CMOV` arm past the carry-out/`MULXHI` bindings, the two
`MULX` names and the ADX prefixes, on the three-source destination/source shape.
The bytes are `encCmovSelect` at the width bit the mnemonic's `:64` tag fixes,
and the gathered `JInstr` block encodes to the same three (or two) opcodes. -/

/-- **The three-source `CMOV` dispatch.** `Lopn [.reg dn] mnem [.reg cn, .reg tn,
    .reg fn]` reduces to `encCmovSelect` at the mnemonic's width, given that the
    mnemonic is no carry-out or high-word binding, is neither `MULX` name, carries
    no ADX prefix, and strips to `CMOV`. -/
theorem dispatch_cmov_three (frame spillW w : Nat) (mnem base : String)
    (dn cn tn fn : String) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hw : rexW (mnemWidth mnem) = w)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (hcmov : (base == "CMOV") = true)
    (hgp : (isGpName dn && isGpName cn && isGpName tn && isGpName fn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg cn, .reg tn, .reg fn]) qsaveB
      = encCmovSelect w (gpNumU dn) (gpNumU cn) (gpNumU tn) (gpNumU fn) := by
  simp only [encodeLopn, hbind, hstrip, hw, hmulx, hmulxmem, hadx, hcmov, hgp,
    Bool.false_eq_true, if_false, if_true]

/-- `CMOV:64` (`w = 1`) dispatches to `encCmovSelect`. -/
theorem encodeLopn_cmov64_emits (frame spillW : Nat) (dn cn tn fn : String)
    (qsaveB : Nat)
    (hgp : (isGpName dn && isGpName cn && isGpName tn && isGpName fn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "CMOV:64" [.reg cn, .reg tn, .reg fn])
        qsaveB
      = encCmovSelect 1 (gpNumU dn) (gpNumU cn) (gpNumU tn) (gpNumU fn) :=
  dispatch_cmov_three frame spillW 1 "CMOV:64" "CMOV" dn cn tn fn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hgp

/-- `gpNumU` is injective on the sixteen names `isGpName` accepts: it is the
    identity on the table read as numbers, and the `0` fall-through is reached by
    no accepted name but `RAX`. -/
theorem gpNumU_inj {x y : String} (hx : isGpName x = true) (hy : isGpName y = true)
    (h : gpNumU x = gpNumU y) : x = y := by
  unfold isGpName at hx hy
  split at hx <;> split at hy <;> simp_all [gpNumU]

/-- The `encCmovSelect` aliasing test on register numbers is the `lowerCmovJ`
    aliasing test on register names, on names `isGpName` accepts. -/
theorem gpNumU_beq_of_isGpName {x y : String} (hx : isGpName x = true)
    (hy : isGpName y = true) : (gpNumU x == gpNumU y) = (y == x) := by
  rcases Decidable.em (y = x) with h | h
  · subst h; simp
  · have hne : gpNumU x ≠ gpNumU y := fun hh => h (gpNumU_inj hx hy hh).symm
    simp [hne, h]

/-- **The three-source `CMOV:64` byte agreement.** The gathered block encodes
    byte-for-byte to the `encodeLopn` bytes of the same `Lopn`, in each of the
    three aliasing cases: the `test` is a reg-reg `85 /r` on the condition
    register, the conditional move a `0F 44`/`0F 45` reg-reg, and the defaulting
    copy an `89 /r`. The `hd`/`hc`/`ht`/`hf` side-conditions tie the `JInstr`
    register names to the `gpNumU` numbers the Lprog encoder resolves. -/
theorem encJCmovSelect_eq_lopn (alloc : GpAlloc) (frame spillW : Nat)
    (dn cn tn fn : String) (qsaveB : Nat)
    (hd : gpNum (regOf alloc dn) = gpNumU dn)
    (hc : gpNum (regOf alloc cn) = gpNumU cn)
    (ht : gpNum (regOf alloc tn) = gpNumU tn)
    (hf : gpNum (regOf alloc fn) = gpNumU fn)
    (hgp : (isGpName dn && isGpName cn && isGpName tn && isGpName fn) = true) :
    encodeJBlock alloc (lowerCmovJ dn cn tn fn)
      = encodeLopn frame spillW
          (.Lopn [.reg dn] "CMOV:64" [.reg cn, .reg tn, .reg fn]) qsaveB := by
  rw [encodeLopn_cmov64_emits frame spillW dn cn tn fn qsaveB hgp]
  simp only [Bool.and_eq_true] at hgp
  obtain ⟨⟨⟨hDn, hCn⟩, hTn⟩, hFn⟩ := hgp
  simp only [encCmovSelect, lowerCmovJ, gpNumU_beq_of_isGpName hDn hTn,
    gpNumU_beq_of_isGpName hDn hFn]
  by_cases htd : (tn == dn) = true
  · simp [htd, encodeJBlock, encodeJInstr, hd, hc, hf,
      LprogJInstrBytesAgree.encAluRRw_one, LprogJInstrBytesAgree.enc0FRRw_one]
  · by_cases hfd : (fn == dn) = true
    · simp [htd, hfd, encodeJBlock, encodeJInstr, hd, hc, ht,
        LprogJInstrBytesAgree.encAluRRw_one, LprogJInstrBytesAgree.enc0FRRw_one]
    · simp [htd, hfd, encodeJBlock, encodeJInstr, hd, hc, ht, hf,
        LprogJInstrBytesAgree.encAluRRw_one, LprogJInstrBytesAgree.enc0FRRw_one]

/-! ## 4. `#eval` verification on asconSigma0's full physical body

The `#eval` byte-compares on the real GoldenPath kernel
`AsconLinear.asconSigma0Com` (whole-body gather coverage, the framing-free
compute-core byte-match `gatherJBlock4 aluCore == encodeLcmd aluCore`, the
whole-body qsave residual, and the `coreNoSpill` byte-match) are re-homed in
`GoldenPathByteIdentityDemo` (above the chain) so this file is GoldenPath-free.
The full-body lowering `gatherJBlock4` and the per-op drop-`mov` shift
agreement theorems (§3) — all kernel-independent — stay here. -/

/-! ## 5. The real-kernel byte-identity bridge: status

`ComToFramedJInstrLeaq.framedLeaqText_eq_lprog` is the theorem that
turns a body byte-agreement into a whole-`.text` byte identity: its `hbody`
hypothesis is `encodeJBlock f.alloc f.body = encodeLcmd body`, and its framing
hypotheses (`hpush` / `hmar` / `hpop`) model the System-V framing as **separate**
`pushq` / `popq` + ret segments around the body, with an **empty** arg-marshal.

§4b establishes the `hbody`-shaped agreement on the **compute body** (the ALU /
`MOV` / shift core): `encodeJBlock physAlloc (gatherJBlock4 aluCore).get =
encodeLcmd aluCore`, byte-for-byte. So the body half of the bridge is met for the
compute spine, and §3 gives the kernel-reducible per-op certificates
(`encJInPlace_*_eq_lopn`, `encJSh*DropMov_eq_lopn`).

But `framedLeaqText_eq_lprog` **cannot be instantiated as-is** on asconSigma0's
physical export, for a structural reason `FramingReconcile` already flagged: the
physical export (`Com.toLprogPhysAbi`) puts the **entire** System-V framing
*inside* `lfd_body` as ordinary `MOVQ` instructions — there is no separate
`pushq`/`popq` segment, and the arg-marshal is non-empty. So
`framedLeaqText_eq_lprog`'s `hpush`/`hmar`/`hpop` framing model does not describe
the physical export's framing. Reconciling the framing on the physical path needs
the in-body `MOVQ` qsave spills to byte-match `encodeLcmd` — and §4c shows they do
**not**: the JInstr scalar encoder has no `off(%rsp)` spill-slot resolution, so the
qsave reg↔mem stores diverge (3-byte reg-reg vs 5-byte `off(%rsp)` store).

**Net status.** With `gatherJBlock4` the whole physical body GATHERS, and
the framing-free compute core (ALU + shift) plus the reg-reg arg-marshal byte-match
`encodeLcmd` exactly (§4b, §4c `coreNoSpill`). The remaining gap to a literal
whole-physical-body byte identity — hence to a clean `framedLeaqText_eq_lprog`
instantiation — is a **single, named capability**: a spill-slot-aware JInstr `mov`
(an `off(%rsp)` store/load keyed on the `qsave.`/`k.N` slot names), so the qsave
framing byte-matches the Lprog `off(%rsp)` resolution. That is the precondition
for re-pointing real kernels off `encodeLprog`; it is an encoder capability, not a
gather-coverage or peephole item, and is recorded here rather than papered over
with a vacuous equality. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
