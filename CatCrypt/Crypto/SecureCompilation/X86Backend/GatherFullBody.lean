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
  when `src ≠ d`, and the shift alone when `src = d`. `gatherJBlock4` matches
  both: an in-place shift lowers to the single `[shr d $n]` / `[shl d $n]`, and
  a shift from a distinct register keeps the materialise `mov d, src`.

## What byte-matches, and the one residual (honest)

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
lowering-table lag like the previous two: it is a genuine **capability gap** — the
JInstr scalar encoder lacks the `off(%rsp)` spill-slot resolution the Lprog
encoder carries. Closing it needs a spill-aware JInstr `mov` (an `off(%rsp)`
store/load arm keyed on the `qsave.`/`k.N` slot names), not a gather-coverage
tweak. We state it honestly here rather than force a vacuous whole-body equality.

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

The whole-`aluCore` byte equality itself is `#eval` interpreter evidence (not a
`decide`/`rfl` theorem): `LoweringExtended.parseShiftMnem` dispatches the shift
arm via `String.startsWith`, which does not kernel-reduce in Lean 4.29 (only the
compiled `#eval` evaluator runs it) — the same status `PhysBodyGather` /
`GatherInPlace` record for their body `#eval`s. The per-op agreements above are
the kernel-reducible certificate; the `#eval` confirms they compose on the real
kernel.

No `sorry`, no axiom, no `native_decide` (the lemma proofs; the `#eval` byte
witnesses in §4 are interpreter evaluation, not part of any proof term).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
open CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (physAlloc)

/-! ## 1. The full-body lowering: `MOVQ ↦ MOV:64` alias + per-shift drop-`mov` -/

/-- The whole-body coverage lowering. Two arms vs `lowerLinstrExtCov3`:

    * **`MOVQ` alias**: a single-source `MOVQ` (the framing synonym `buildPrologue`
      emits) is lowered as the gather-covered `MOV:64` form. `encodeLopn` already
      maps the two mnemonics to identical bytes (`FramingReconcile` §3), so the
      framing now gathers.
    * **in-place shift**: a count-in-tag shift `SHR:<n>:64`/`SHL:<n>:64` whose
      source register is its destination lowers to the **single**
      `[shr d $n]` / `[shl d $n]`, without the materialise `mov d, d`. The Lprog
      encoder emits `mov d, s` before the shift exactly when `s ≠ d`, so a shift
      with a distinct source keeps the two-instruction form of
      `lowerLinstrExtCov3`.

    Every other shape delegates to `lowerLinstrExtCov3` verbatim (the in-place
    two-source ALU peephole). So `lowerLinstrExtCov4` differs from
    `lowerLinstrExtCov3` only on the single-source `MOVQ` and the in-place
    count-in-tag shift shapes. -/
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
            some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                  else JInstr.shr dst (JOperand.imm p.2)]
          else lowerLinstrExtCov3 (.Lopn [.reg dst] opn [src])
      | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] opn [src])
  -- everything else (two-source ALU, MULXHI, memory, control-flow): the in-place
  -- coverage superset verbatim
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
count `n` (carried as a hypothesis `hsh : parseShiftMnem opn = some (isLeft, n)`),
because `parseShiftMnem` dispatches via `String.startsWith`, which does not
kernel-reduce — the count value `n` is recovered from the hypothesis, not by
reduction. A shift from a distinct register lowers through `lowerLinstrExtCov3`
to `[mov d s, shr/shl d $n]`, the same two instructions the Lprog encoder emits. -/

/-- A count-in-tag right shift `SHR:19:64 [d]` (dst `d`) lowers under
    `lowerLinstrExtCov4` to the **single** op `[shr d $n]`, given the parse
    `parseShiftMnem "SHR:19:64" = some (false, n)`. The mnemonic is concrete (so
    the `"MOVQ"`-head arm is decidably distinct and the matcher reduces to the
    shift branch); the count `n` is recovered from the `parseShiftMnem` hypothesis
    (it is not kernel-reducible — `String.startsWith`). The `SHR:28:64` /
    `SHL:45:64` / `SHL:36:64` analogues are `lowerCov4_shr28` / `lowerCov4_shl45` /
    `lowerCov4_shl36`. -/
theorem lowerCov4_shr19 (dst : String) (n : Nat)
    (hsh : parseShiftMnem "SHR:19:64" = some (false, n)) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "SHR:19:64" [.reg dst])
      = some [JInstr.shr dst (.imm n)] := by
  show (match parseShiftMnem "SHR:19:64", LOperand.reg dst with
        | some p, .reg s =>
            if s = dst then
              some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                    else JInstr.shr dst (JOperand.imm p.2)]
            else lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:19:64" [.reg dst])
        | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:19:64" [.reg dst])) = _
  rw [hsh]; simp

/-- In-place `SHR:28:64 [d]` lowers to the single `[shr d $n]`. -/
theorem lowerCov4_shr28 (dst : String) (n : Nat)
    (hsh : parseShiftMnem "SHR:28:64" = some (false, n)) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "SHR:28:64" [.reg dst])
      = some [JInstr.shr dst (.imm n)] := by
  show (match parseShiftMnem "SHR:28:64", LOperand.reg dst with
        | some p, .reg s =>
            if s = dst then
              some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                    else JInstr.shr dst (JOperand.imm p.2)]
            else lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:28:64" [.reg dst])
        | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:28:64" [.reg dst])) = _
  rw [hsh]; simp

/-- In-place `SHL:45:64 [d]` lowers to the single `[shl d $n]`. -/
theorem lowerCov4_shl45 (dst : String) (n : Nat)
    (hsh : parseShiftMnem "SHL:45:64" = some (true, n)) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "SHL:45:64" [.reg dst])
      = some [JInstr.shl dst (.imm n)] := by
  show (match parseShiftMnem "SHL:45:64", LOperand.reg dst with
        | some p, .reg s =>
            if s = dst then
              some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                    else JInstr.shr dst (JOperand.imm p.2)]
            else lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:45:64" [.reg dst])
        | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:45:64" [.reg dst])) = _
  rw [hsh]; simp

/-- In-place `SHL:36:64 [d]` lowers to the single `[shl d $n]`. -/
theorem lowerCov4_shl36 (dst : String) (n : Nat)
    (hsh : parseShiftMnem "SHL:36:64" = some (true, n)) :
    lowerLinstrExtCov4 (.Lopn [.reg dst] "SHL:36:64" [.reg dst])
      = some [JInstr.shl dst (.imm n)] := by
  show (match parseShiftMnem "SHL:36:64", LOperand.reg dst with
        | some p, .reg s =>
            if s = dst then
              some [if p.1 then JInstr.shl dst (JOperand.imm p.2)
                    else JInstr.shr dst (JOperand.imm p.2)]
            else lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:36:64" [.reg dst])
        | _, _ => lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:36:64" [.reg dst])) = _
  rw [hsh]; simp


/-- **The `MOVQ ↦ MOV:64` alias lowers to a reg-reg `mov`.** A single-source
    `MOVQ R14, RSI` (the reg-reg arg-marshal framing) lowers under
    `lowerLinstrExtCov4` to `[mov dst s]` — the same single op the `MOV:64`
    mnemonic gathers, which `encodeLopn` already byte-matches the `MOVQ` form
    (`FramingReconcile.encode_argMarshal_movq_eq_mov64`). The parse fact
    `parseShiftMnem "MOV:64" = none` is carried as a hypothesis (it is only
    `native_decide`-reducible — `String.startsWith` — so it stays out of the proof
    term). -/
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

/-! ## 4. `#eval` verification on asconSigma0's full physical body

The `#eval` byte-compares on the real GoldenPath kernel
`AsconLinear.asconSigma0Com` (whole-body gather coverage, the framing-free
compute-core byte-match `gatherJBlock4 aluCore == encodeLcmd aluCore`, the
whole-body qsave residual, and the `coreNoSpill` byte-match) are re-homed in
`GoldenPathByteIdentityDemo` (above the chain) so this file is GoldenPath-free.
The full-body lowering `gatherJBlock4` and the per-op drop-`mov` shift
agreement theorems (§3) — all kernel-independent — stay here. -/

/-! ## 5. The real-kernel byte-identity bridge: status (honest)

`ComToFramedJInstrLeaq.framedLeaqText_eq_lprog` is the load-bearing theorem that
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

**Net status (honest).** With `gatherJBlock4` the whole physical body GATHERS, and
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
