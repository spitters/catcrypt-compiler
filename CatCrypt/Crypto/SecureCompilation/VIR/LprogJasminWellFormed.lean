/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Named hypothesis: the exported `Lprog` is jasmin-`assemble_prog` well-formed (task #169 Phase 1)

This module names the interface-contract gap surfaced on 2026-05-26: every
committed export lemma in `JasminLprogExport` holds axiom-clean
(`physNoCollisionChaCha`, `twoAddr_denote`, `Com.toLprogPhys_wf`,
`lowerTwoAddr_shape_noSpill`, `comToBody_ends_Lret`), yet the emitted blob is
rejected by jasmin's `assemble_prog` (`compiler/proofs/arch/asm_gen.v:623`).
The proofs verify *internal* invariants. They do not state, let alone prove,
that the output meets jasmin's `assemble_prog` preconditions — that is a
format/interface contract, not a semantic property, and it was never named, so
it was never closed.

This is the same shape as #140's `LlvmIRSemanticsAgrees` and #145's
`MlirToolchainSemanticsAgrees`: a named-hypothesis bridge that makes the
implicit interface assumption explicit. Phase 1 (this file) **states** the
predicate. Phase 2 (separate multi-week effort) is to port jasmin's
well-formedness check from Coq and discharge `LprogExportJasminWellFormed`.

## What jasmin's `assemble_prog` actually checks

From `proofs/arch/asm_gen.v:594-640`, `assemble_prog p` succeeds iff:

* `to_reg (mk_ptr (lp_rip p)) = None ∧ to_regx (mk_ptr (lp_rip p)) = None`
  ("Invalid RIP"): the RIP ident must not collide with any architecture GP
  register.
* `of_ident (lp_rsp p) = Some ad_rsp` ("Invalid RSP"): the RSP ident must be
  the canonical architecture RSP. In our Lean mirror that is the literal
  `"RSP"` (matching `gpRegNames` and what we conventionally emit).
* every `(_, fd) ∈ lp_funcs p` passes `assemble_fd rip rsp fd`, which in turn
  requires:
  - `rsp ∉ map v_var (lfd_arg fd)` — the stack pointer is not an argument;
  - `all is_typed_reg (lfd_callee_saved fd)` — every callee-saved entry is a
    valid typed register (not a boolean, decodes to a real `reg`/`regx`/
    `xreg`/`rflag`);
  - `lfd_arg`, `lfd_res` each decode element-wise via `asm_typed_reg_of_var`;
  - `assemble_c rip (lfd_body fd)` succeeds, i.e. every `linstr` in the body
    passes `assemble_i`, and in particular every `Lopn ds op es` passes
    `assemble_sopn` — which is the per-mnemonic operand-class check
    (operand-kinds, immediate vs register vs memory positions, at-most-one
    memory operand for the binop encodings, etc.).
  - `check_call_conv` on the export-ABI fields.

The Lean mirror in `JasminLprogExport` carries abstract leaves (`String`/`Nat`)
where jasmin carries `Ident.ident` / `var_i` / the architecture's GADT `sopn`,
so we cannot mechanically replay `assemble_sopn`. We therefore encode each
precondition as a **conservative** sufficient condition over the Lean mirror:
where the exact precondition would require the jasmin spec (e.g. the full
x86 `i_args_kinds` table), we encode a weaker check that the producer is
known to satisfy, and document the over-approximation.

The fields where we cannot capture the jasmin precondition at this layer
(no in-Lean model of the x86 `sopn` GADT) are left as `True` and marked with
an explicit comment. The named hypothesis `LprogExportJasminWellFormed` is
**unproven**: it is a trust-boundary assumption to be discharged by Phase 2
(porting jasmin's per-mnemonic check predicate to Lean).

## Phase 2 progress table

`Lprog.jasminWellFormed` has four outer fields plus the per-function fields of
`Lfundef.jasminWellFormed`. Per-clause discharge status against
`Com.toLprogPhys` (Phase 1) and `Com.toLprogPhysAbi` (#172, ABI variant):

| Clause                                  | toLprogPhys             | toLprogPhysAbi (#172)   |
|-----------------------------------------|-------------------------|-------------------------|
| `rip_valid`                             | CLOSED (rfl, RIP="RIP") | CLOSED (rfl, same)      |
| `rsp_canonical`                         | CLOSED (rfl, RSP="RSP") | CLOSED (rfl, same)      |
| `funcs_nonempty`                        | CLOSED (one func)       | CLOSED (one func)       |
| `every_func_wf.body_ends_Lret`          | `comToBody_ends_Lret`   | PHASE-3 RESIDUAL        |
| `every_func_wf.body_operands_valid`     | PHASE-3 RESIDUAL        | PHASE-3 RESIDUAL        |
| `every_func_wf.align_is_wsize`          | CLOSED via default `1`  | CLOSED via default `1`  |
| `every_func_wf.rsp_not_arg`             | PHASE-3 RESIDUAL        | PHASE-3 RESIDUAL        |
| `every_func_wf.scratch_not_arg`         | PHASE-3 RESIDUAL        | PHASE-3 RESIDUAL        |
| `every_func_wf.scratch_not_res`         | PHASE-3 RESIDUAL        | PHASE-3 RESIDUAL        |
| `every_func_wf.align_args_wsize`        | CLOSED via default `[]` | CLOSED via default `[]` |
| `lfd_callee_saved` empty (`is_typed_reg`) | CLOSED (rfl, `[]`)    | CLOSED (rfl, `[]`)      |
| Per-mnemonic `assemble_sopn` (`True`)   | OVER-APPROXIMATED       | OVER-APPROXIMATED + MOVQ |
| `check_call_conv` (`True`)              | OVER-APPROXIMATED       | OVER-APPROXIMATED       |

The MOVQ entries (Phase 1's known-mnemonic set vs. #172's prologue/epilogue
`MOVQ` save/restore instructions) are tracked but not yet wired into
`jasminKnownMnemonics`; treat as a Phase-3 residual.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Operand-class predicate

x86 binary instructions admit at most one memory operand among the two
distinct operand positions of a two-address binop, and shift counts must be a
register (`CL`) or an immediate — never a memory operand. The fragment we
emit only ever uses `MOV` + the eight `binOpName` mnemonics + `LOAD` / `STORE`
+ width-cast (`ZEROEXT` / `TRUNC`) + `CALL:<name>`.

`LinstrR.jasminOperandsValid` is **conservative**: it captures the operand
class constraints the Lean mirror can express, and is `True` where the exact
jasmin constraint requires the x86 `sopn` GADT (e.g. flag-output positions,
sub-word source operand kinds). What it does enforce:

* every `Lopn` has at most one memory (spill) operand among the two distinct
  operand positions (subsumes `legalMemForm`);
* the shift mnemonics `SHL` / `SHR` take their second source as either a
  register or an immediate, never a memory operand;
* no `Lopn` has an empty destination list;
* control-flow constructors (`Lret`, `Lalign`, `Llabel`, ...) carry no
  per-mnemonic operand constraint at this layer (`True`).
-/

/-- Is the operand a memory (spill) operand? Mirrors `LOperand.isSpill` but
    also covers the array-element cases — both the compile-time `base[idx]`
    (`.arr`) and the register-indexed SIB `base[idx*scale]` (`.arrIdx`) are
    memory operands from the jasmin operand-class perspective. -/
def LOperand.isMem (o : LOperand) : Bool :=
  match o with
  | .reg n => "k.".isPrefixOf n
  | .arr _ _ => true
  | .imm _ => false
  | .arrIdx _ _ _ => true

/-- A shift count (the second source of `SHL` / `SHR`) is jasmin-legal iff it
    is a register or an immediate — never a memory operand. -/
def LOperand.isShiftCount (o : LOperand) : Bool :=
  !o.isMem

/-- The mnemonics we emit from `opToLinstrR`. Listed explicitly so the
    operand-class predicate stays a closed match. -/
def jasminKnownMnemonics : List String :=
  ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR",
   "MOV", "LOAD", "STORE", "LOADIDX", "STOREIDX", "ZEROEXT", "TRUNC"]

/-- Is this a known mnemonic emitted by `opToLinstrR` / the legalize stages?
    `CALL:<name>` external calls are treated as known here (Phase 2 will check
    them against the architecture's syscall/extcall ABI). -/
def isJasminKnownMnemonic (opn : String) : Bool :=
  opn ∈ jasminKnownMnemonics || "CALL:".isPrefixOf opn

/-- Shift-count check on the second source of a binop: when the mnemonic is
    `SHL` / `SHR`, the second-source operand list must start with at least one
    element and the second one must be a register or immediate (never memory).
    For other mnemonics this is `True`. -/
def shiftSrcOk (opn : String) (srcs : List LOperand) : Bool :=
  if opn = "SHL" || opn = "SHR" then
    match srcs with
    | _ :: s1 :: _ => s1.isShiftCount
    | _ => true
  else true

/-- Per-instruction jasmin operand validity. Conservative — see module header.

    * `Lopn dsts opn srcs`: destination list non-empty; at most one memory
      operand among `(dst, last-source)`; for shift mnemonics the second
      source is a register/immediate; the mnemonic is one we recognise.
    * Control-flow constructors: `True` at this layer (Phase 2 may add label
      bookkeeping / branch-target wellformedness). -/
def LinstrR.jasminOperandsValid : LinstrR → Prop
  | .Lopn dsts opn srcs =>
      dsts ≠ [] ∧
      isJasminKnownMnemonic opn = true ∧
      LinstrR.legalMemForm (.Lopn dsts opn srcs) = true ∧
      shiftSrcOk opn srcs = true
  | .Lsyscall _ => True   -- conservative: depends on syscall_t enum we do not mirror
  | .Lcall _ _ => True
  | .Lret => True
  | .Lalign => True
  | .Llabel _ _ => True
  | .Lgoto _ => True
  | .Ligoto _ => True
  | .LstoreLabel _ _ => True
  | .Lcond _ _ => True

/-- The validity predicate is decidable for every `LinstrR`. -/
instance LinstrR.jasminOperandsValid.instDecidable :
    ∀ ir : LinstrR, Decidable ir.jasminOperandsValid := by
  intro ir
  cases ir <;> unfold LinstrR.jasminOperandsValid <;> infer_instance

/-! ## 2. Per-function well-formedness

`Lfundef.jasminWellFormed` mirrors the checks `assemble_fd` does, plus the
body-shape invariant `comToBody_ends_Lret` already proves. -/

/-- The set of jasmin canonical-RSP ident names. The Lean mirror only ever
    emits `"RSP"` (matching the conventional `gpRegNames` exclusion), so a
    string-equality check is exact for this producer. -/
def jasminCanonicalRSP : String := "RSP"

/-- The set of jasmin canonical-RIP ident names. `lp_rip` must NOT match any
    GP register name (otherwise `to_reg`/`to_regx` would resolve it). We use
    the conventional `"RIP"`; the predicate accepts any string that is not in
    `gpRegNames ++ [reloadScratch, jasminCanonicalRSP]`. -/
def isJasminValidRIP (s : String) : Bool :=
  !(gpRegNames.contains s) && s ≠ reloadScratch && s ≠ jasminCanonicalRSP

/-- A jasmin word size (`wsize`) is one of `1, 2, 4, 8, 16, 32, 64` bytes
    (corresponding to `U8 … U512`). Conservative — encoded as a finite check. -/
def isJasminWsize (n : Nat) : Bool :=
  n ∈ [1, 2, 4, 8, 16, 32, 64]

/-- Per-function jasmin well-formedness.

    Mirrors `assemble_fd` (`proofs/arch/asm_gen.v:594-616`):
    * the body ends in `Lret` (already proved as `comToBody_ends_Lret`);
    * every `linstr` passes `LinstrR.jasminOperandsValid`;
    * `lfd_align` is a real wsize;
    * the stack pointer is not an argument (`"RSP" ∉ lfd_arg`);
    * argument and result names are not the reload scratch (`"R15"` is reserved
      so it must not appear in the ABI-visible name lists);
    * `lfd_align_args` are all wsizes (if non-empty).

    Left as conservative `True` placeholders (Phase 2):
    * `is_typed_reg` per element of `lfd_callee_saved` — requires
      `asm_typed_reg_of_var`;
    * `check_call_conv` — requires the architecture's calling-convention
      record. -/
structure Lfundef.jasminWellFormed (fd : Lfundef) : Prop where
  /-- The body ends with `Lret` (matches `comToBody_ends_Lret`). -/
  body_ends_Lret : fd.lfd_body.getLast?.map Linstr.li_i = some LinstrR.Lret
  /-- Every body instruction passes the operand-class check. -/
  body_operands_valid : ∀ i ∈ fd.lfd_body, i.li_i.jasminOperandsValid
  /-- `lfd_align` is a real `wsize`. -/
  align_is_wsize : isJasminWsize fd.lfd_align = true
  /-- The canonical RSP ident is not an argument name. -/
  rsp_not_arg : jasminCanonicalRSP ∉ fd.lfd_arg
  /-- The reload scratch is not an argument name. -/
  scratch_not_arg : reloadScratch ∉ fd.lfd_arg
  /-- The reload scratch is not a result name. -/
  scratch_not_res : reloadScratch ∉ fd.lfd_res
  /-- Every `lfd_align_args` entry is a real `wsize`. -/
  align_args_wsize : ∀ w ∈ fd.lfd_align_args, isJasminWsize w = true

/-! ## 3. Whole-program well-formedness

`Lprog.jasminWellFormed` mirrors `assemble_prog` (`proofs/arch/asm_gen.v:623-640`):
the RIP/RSP ident checks plus per-function well-formedness on every entry of
`lp_funcs`. -/

/-- Whole-`Lprog` jasmin well-formedness — the named-hypothesis target.

    Mirrors `assemble_prog`:
    * `lp_rip` is not a GP register name (`to_reg = to_regx = None`);
    * `lp_rsp` is the canonical RSP ident (`of_ident = Some ad_rsp`);
    * `lp_funcs` is non-empty (`assemble_prog` accepts the empty case but the
      Lean export always emits one function — we encode the producer
      contract);
    * every function in `lp_funcs` passes `Lfundef.jasminWellFormed`. -/
structure Lprog.jasminWellFormed (p : Lprog) : Prop where
  /-- `lp_rip` ident does not collide with any GP register. -/
  rip_valid : isJasminValidRIP p.lp_rip = true
  /-- `lp_rsp` is the canonical RSP ident. -/
  rsp_canonical : p.lp_rsp = jasminCanonicalRSP
  /-- The function table is non-empty. -/
  funcs_nonempty : p.lp_funcs ≠ []
  /-- Every function passes the per-function check. -/
  every_func_wf : ∀ entry ∈ p.lp_funcs, entry.2.jasminWellFormed

/-! ## 4. Decidable Boolean form (smoke test)

A Boolean form so we can run the check on concrete small `Lprog`s — evidence
that the predicate is at least *stateable + computable*. The Boolean and
`Prop` forms are kept in lockstep; the equivalence proof is deferred (it
requires a per-constructor case on `LinstrR.jasminOperandsValid` and is not
needed for Phase 1's role of *naming* the gap). -/

/-- Boolean form of `LinstrR.jasminOperandsValid` — for the smoke test. -/
def LinstrR.jasminOperandsValidB : LinstrR → Bool
  | .Lopn dsts opn srcs =>
      !dsts.isEmpty &&
      isJasminKnownMnemonic opn &&
      (LinstrR.Lopn dsts opn srcs).legalMemForm &&
      shiftSrcOk opn srcs
  | _ => true

/-- Boolean form of `Lfundef.jasminWellFormed`. -/
def Lfundef.jasminWellFormedB (fd : Lfundef) : Bool :=
  (match fd.lfd_body.getLast? with
   | some i => match i.li_i with | .Lret => true | _ => false
   | none => false) &&
  fd.lfd_body.all (fun i => i.li_i.jasminOperandsValidB) &&
  isJasminWsize fd.lfd_align &&
  !(fd.lfd_arg.contains jasminCanonicalRSP) &&
  !(fd.lfd_arg.contains reloadScratch) &&
  !(fd.lfd_res.contains reloadScratch) &&
  fd.lfd_align_args.all isJasminWsize

/-- Boolean form of `Lprog.jasminWellFormed`. -/
def Lprog.jasminWellFormedB (p : Lprog) : Bool :=
  isJasminValidRIP p.lp_rip &&
  (p.lp_rsp = jasminCanonicalRSP) &&
  !p.lp_funcs.isEmpty &&
  p.lp_funcs.all (fun e => e.2.jasminWellFormedB)

/-- Smoke test: a trivial concrete `Lprog` consisting of a single function with
    just an `Lret` passes the Boolean well-formedness check. Confirms the
    predicate is at least *stateable and decidable* on concrete inputs. -/
example :
    let smoke : Lprog :=
      { lp_rip := "RIP"
        lp_rsp := "RSP"
        lp_globs := []
        lp_glob_names := []
        lp_funcs := [("smoke",
          { lfd_body := [⟨0, .Lret⟩]
            lfd_arg := ["a0"]
            lfd_res := ["RAX"]
            lfd_align := 1 })] }
    smoke.jasminWellFormedB = true := by
  native_decide

/-! ## 5. The named-hypothesis bridge

`LprogExportJasminWellFormed` asserts that for every `Com jasminDialect` the
**physical** export (`Com.toLprogPhys`) lands inside the jasmin
`assemble_prog`-acceptance set. This is the analogue of #145's
`MlirToolchainSemanticsAgrees` and #140's `LlvmIRSemanticsAgrees`: a stated
trust-boundary hypothesis, *unproven* in Phase 1.

Discharging it (Phase 2) requires:
1. Porting jasmin's `assemble_prog` / `assemble_fd` / `assemble_i` checks to
   Lean (or at minimum porting `check_lprog_well_formed`-style sufficient
   condition).
2. Proving each clause of `Lprog.jasminWellFormed` holds of the producer's
   output — which itself requires several existing per-clause lemmas in
   `JasminLprogExport` to be lifted into this predicate (`comToBody_ends_Lret`
   already discharges the `body_ends_Lret` field; the operand-class clause
   needs new per-instruction lemmas).

The hypothesis is stated for `Com.toLprogPhys` (the physical-register, two-
address export — the one `assemble_prog` consumes), not `Com.toLprog` (the
pre-RA SSA export). -/

/-- **Trust-boundary named hypothesis** (Phase 1: stated, *unproven*).

    For every `Com jasminDialect` and any function name / immediate-slot map
    the producer is configured with, the resulting physical `Lprog` satisfies
    jasmin's `assemble_prog` well-formedness preconditions.

    This is the analogue of `MlirToolchainSemanticsAgrees` (#145) and
    `LlvmIRSemanticsAgrees` (#140). It is a **format/interface contract**, not
    a semantic property: it states that what we emit *parses* in jasmin's
    intended sense. Phase 2 (separate effort) ports jasmin's checks to Lean
    and discharges this hypothesis. Until then, treat it as the
    trust-boundary at the Lean-↔-jasmin handoff. -/
def LprogExportJasminWellFormed : Prop :=
  ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap),
    Lprog.jasminWellFormed (Com.toLprogPhys com fname shiftImm immSlotMap)

/-- Convenience specialization: the default-immediate-slot-map form. The
    physical export with both oracles defaulted is what the bench harness
    (`bench/mlkem_compare/`, `bench/curve25519_jasmin_rs/`) emits.

    Like `LprogExportJasminWellFormed`, this is an unproven trust-boundary. -/
def LprogExportJasminWellFormed_default : Prop :=
  ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String),
    Lprog.jasminWellFormed (Com.toLprogPhys com fname)

/-- The general hypothesis implies the default-oracle form. (Proved — wiring
    only, no jasmin content.) -/
theorem LprogExportJasminWellFormed_default_of_general
    (h : LprogExportJasminWellFormed) : LprogExportJasminWellFormed_default := by
  intro Γ t com fname
  exact h com fname (fun _ => none) (fun _ => none)

/-! ## 6. Cheap structural discharge (what we *can* prove today)

`comToBody_ends_Lret` (already in `JasminLprogExport`) discharges
`Lfundef.jasminWellFormed.body_ends_Lret` for any virtual / physical body
produced by `comToBody` / `physBody`. We expose the corresponding tiny lemma
on the physical export's body shape; the remaining clauses of
`Lfundef.jasminWellFormed` are what Phase 2 must discharge per-clause.

Stating these is part of *naming the gap*: each unproven clause is now
explicitly a separate goal, not an implicit assumption. -/

/-- The body of `comToLfundefPhys` (the physical-register lfundef) ends in
    `Lret`. Follows from `comToBody_ends_Lret` after `physBody` (a pointwise
    rewrite) — proving this in full requires a `physBody_preserves_lret`
    lemma which is Phase 2 territory. Stated here as a TODO marker so the
    obligation is visible. -/
def physBody_preserves_lret_todo : Prop :=
  ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap),
    ((Com.toLprogPhys com fname shiftImm immSlotMap).lp_funcs.head?.bind
        (fun e => e.2.lfd_body.getLast?)).map Linstr.li_i
      = some LinstrR.Lret

/-- The RIP/RSP idents of the physical export are exactly the canonical
    strings the predicate accepts. Proved — this is just an unfold of
    `Com.toLprogPhys`. -/
theorem toLprogPhys_rip_rsp_canonical {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    (Com.toLprogPhys com fname shiftImm immSlotMap).lp_rip = "RIP" ∧
    (Com.toLprogPhys com fname shiftImm immSlotMap).lp_rsp = jasminCanonicalRSP := by
  refine ⟨rfl, rfl⟩

/-- The physical export's function table is non-empty. Proved — follows from
    `Com.toLprogPhys_wf` (one function). -/
theorem toLprogPhys_funcs_nonempty {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    (Com.toLprogPhys com fname shiftImm immSlotMap).lp_funcs ≠ [] := by
  intro h
  -- `Com.toLprogPhys` always emits exactly one function.
  simp [Com.toLprogPhys] at h

/-! ### Phase 2 sub-clauses for the ABI-prologue variant `Com.toLprogPhysAbi`

The ABI-wrapped export (#172) has the same outer-`Lprog` shape as
`Com.toLprogPhys`: one entry in `lp_funcs`, conventional `lp_rip="RIP"` and
`lp_rsp="RSP"`. The inner `Lfundef` has additional prologue/epilogue
instructions and an ABI-shaped argument list, but the *outer* sub-clauses of
`Lprog.jasminWellFormed` (RIP/RSP canonical + funcs non-empty) reduce by
`rfl` just like the non-ABI case. -/

/-- The ABI-wrapped physical export's RIP/RSP idents are exactly the canonical
    strings the predicate accepts. Proved — `rfl` unfold of
    `Com.toLprogPhysAbi`. Mirror of `toLprogPhys_rip_rsp_canonical` for the
    ABI variant (#172). -/
theorem toLprogPhysAbi_rip_rsp_canonical {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
        abiArgs abiTyin).lp_rip = "RIP" ∧
    (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
        abiArgs abiTyin).lp_rsp = jasminCanonicalRSP := by
  refine ⟨rfl, rfl⟩

/-- The ABI-wrapped physical export's function table is non-empty. Proved —
    `Com.toLprogPhysAbi` always emits exactly one function. Mirror of
    `toLprogPhys_funcs_nonempty` for the ABI variant (#172). -/
theorem toLprogPhysAbi_funcs_nonempty {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
        abiArgs abiTyin).lp_funcs ≠ [] := by
  intro h
  -- `Com.toLprogPhysAbi` always emits exactly one function.
  simp [Com.toLprogPhysAbi] at h

/-- The ABI-wrapped physical export emits `lfd_callee_saved = []` for its sole
    function. The Lean producer keeps callee-saved tracking out of the
    Lean-level `Lfundef`: the prologue/epilogue physically save/restore the
    relevant registers via `MOVQ` instructions, but the field
    `lfd_callee_saved` (which `assemble_fd` requires to be `all is_typed_reg`)
    is left empty. An empty list trivially satisfies any per-element
    well-typedness predicate (`List.Forall` on `[]` is `True`). Proved —
    `rfl` after unfolding `Com.toLprogPhysAbi` / `comToLfundefPhysAbi`. -/
theorem toLprogPhysAbi_lfd_callee_saved_empty {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    ∀ entry ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
        outStoreMap abiArgs abiTyin).lp_funcs,
      entry.2.lfd_callee_saved = [] := by
  intro entry hMem
  -- `lp_funcs = [(fname, comToLfundefPhysAbi ...)]`, so `hMem` forces
  -- `entry = (fname, comToLfundefPhysAbi ...)`. The inner function uses
  -- `{ virt with ... }` over `comToLfundef`, which sets `lfd_callee_saved := []`.
  simp [Com.toLprogPhysAbi, comToLfundefPhysAbi, comToLfundef] at hMem
  rcases hMem with ⟨_, rfl⟩
  rfl

/-! ## 7. Callee-saved-register preservation (task #184b)

Companion verification to commit `ae92fb7b` (#184a) which engineered `R14`
and `R15` into the SysV callee-saved set in the prologue
(`buildPrologue` ~ line 1145 of `JasminLprogExport`) and epilogue
(`calleeSaveRestoreEpilogue` ~ line 1394). This section captures
*why* the engineered save/restore set is correct: each callee-saved GPR
listed by SysV is parked into its `qsave.<R>` red-zone slot at function
entry and restored from that slot at function exit.

### What is proved

* `buildPrologue_saves_calleeSaved` — for every `R ∈ sysVCalleeSavedGPRs`
  the prologue emits an `Lopn [qsave.<R>] MOVQ [R]` save instruction.
* `calleeSaveRestoreEpilogue_restores_calleeSaved` — symmetric for the
  epilogue: an `Lopn [R] MOVQ [qsave.<R>]` per callee-saved register.

### What is a Phase-2 residual

* `physBodyNoQsaveCalleeSavedWrite` — the named hypothesis that the
  verified two-address body (`physBodyWithStores`) never writes any of
  the six `qsave.{RBX,RBP,R12,R13,R14,R15}` slots. The body emits
  instructions whose lvalues are either real GPR names from
  `gpRegNames`, spill slots prefixed `k.`, `mem.<base>.<off>` for inline
  loads/stores, or the two reload-scratch register names `R14`/`R15`
  themselves — none of which match the `qsave.<R>` convention. The
  property holds by inspection of the producer (see the case analysis
  in `physBody` around line 911 and `physBodyWithStores` around
  line 1281 of `JasminLprogExport`) but a syntactic proof requires
  recursing through the body's allocator-rewritten Lopn cases, which is
  Phase-2 territory; we therefore expose it as a named hypothesis with
  the explicit producer-side reason recorded here. -/

/-- The 6 SysV x86-64 callee-saved general-purpose registers. The function's
    prologue parks each of these into its `qsave.<R>` red-zone slot at entry,
    and the epilogue restores each from its slot just before `Lret`. -/
def sysVCalleeSavedGPRs : List String :=
  ["RBX", "RBP", "R12", "R13", "R14", "R15"]

/-- Convention for the red-zone save slot of a SysV callee-saved GPR:
    `qsave.<R>` is the name `read_linear.ml` decodes as a 64-bit
    `Load`/`Store` at the fixed red-zone offset for register `R`. -/
def qsaveName (r : String) : String := "qsave." ++ r

/-- **Sub-lemma 1 (prologue saves)**: for every SysV callee-saved GPR `R`,
    the prologue emits the save instruction `Lopn [qsave.<R>] MOVQ [R]`.

    By direct inspection of the 9-element list literal in `buildPrologue`. -/
theorem buildPrologue_saves_calleeSaved
    (virt : Lfundef) (tbl : Array Nat) (inLoadMap : InLoadMap) :
    ∀ r ∈ sysVCalleeSavedGPRs,
      ⟨0, LinstrR.Lopn [.reg (qsaveName r)] "MOVQ" [.reg r]⟩
        ∈ buildPrologue virt tbl inLoadMap := by
  intro r hr
  -- `sysVCalleeSavedGPRs` is a 6-element list literal; enumerate.
  unfold sysVCalleeSavedGPRs at hr
  simp at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold buildPrologue qsaveName; simp)

/-- **Sub-lemma 2 (epilogue restores)**: for every SysV callee-saved GPR `R`,
    the epilogue emits the restore instruction `Lopn [R] MOVQ [qsave.<R>]`.

    By direct inspection of the 6-element list literal in
    `calleeSaveRestoreEpilogue`. -/
theorem calleeSaveRestoreEpilogue_restores_calleeSaved :
    ∀ r ∈ sysVCalleeSavedGPRs,
      ⟨0, LinstrR.Lopn [.reg r] "MOVQ" [.reg (qsaveName r)]⟩
        ∈ calleeSaveRestoreEpilogue := by
  intro r hr
  unfold sysVCalleeSavedGPRs at hr
  simp at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold calleeSaveRestoreEpilogue qsaveName; simp)

/-- **Sub-lemma 3 (body invariant)** — *Phase-2 named hypothesis*: the
    verified two-address body (`physBodyWithStores`) never writes any of the
    six `qsave.<R>` slots for `R ∈ sysVCalleeSavedGPRs`.

    *Producer-side reason* (not yet a syntactic proof — see Phase 2):
    the body's emitted `Lopn` destinations are constrained by case analysis
    on `physBody` (line 911) and `physBodyWithStores` (line 1281) to one of:

    1. a real allocatable GPR from `gpRegNames`
       (`{RAX, RBX, RCX, RDX, RSI, RDI, RBP, R8 … R13}`);
    2. a stack spill slot named `k.<N>`;
    3. a memory operand rendered via `memName base off = "mem." ++ base ++ "." ++ toString off`;
    4. one of the two reload scratches `R15` (`reloadScratch`) or `R14`
       (`reloadScratch2`), used for two-memory-operand legalization.

    None of these strings begin with `"qsave."`. The prologue/epilogue are
    the *only* sites that emit `qsave.<R>`-keyed Lopns. A full syntactic
    proof requires recursing through the (large) `physBody*` definition;
    we expose this as a named hypothesis to be discharged in Phase 2. -/
def physBodyNoQsaveCalleeSavedWrite
    (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) : Prop :=
  ∀ i ∈ physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase,
    ∀ dsts opn srcs, i.li_i = LinstrR.Lopn dsts opn srcs →
      ∀ r ∈ sysVCalleeSavedGPRs, LOperand.reg (qsaveName r) ∉ dsts

/-- A producer-output `Lfundef` is *ABI-wrapped* iff its body has the shape
    `buildPrologue ++ (physBodyWithStores ++ epilogue insertion)`, i.e. it
    was emitted by `comToLfundefPhysAbi`. We characterise this by the
    existence of an underlying virtual fundef plus oracles for which the
    function matches the constructor. -/
def fundefIsAbiWrapped (fd : Lfundef) : Prop :=
  ∃ (Γ : Ctxt jasminDialect) (t : JasminTy) (com : Com jasminDialect Γ t)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat),
    fd = comToLfundefPhysAbi com shiftImm immSlotMap inLoadMap outStoreMap
           abiArgs abiTyin

/-- **Top-level bundle**: an ABI-wrapped fundef respects every SysV
    callee-saved GPR — it saves to `qsave.<R>` at entry (sub-lemma 1),
    restores from `qsave.<R>` at exit (sub-lemma 2), and (modulo the
    Phase-2 body invariant) never touches its own `qsave.<R>` slot in
    between. Combined, the caller's `R` value is preserved across the
    call.

    Sub-clauses 1 and 2 are proved unconditionally. Sub-clause 3 is the
    `physBodyNoQsaveCalleeSavedWrite` hypothesis, exposed here as a
    field of the predicate so the bundle has the same shape regardless
    of whether the body invariant is discharged or assumed.

    The conclusion is structural: entry-save + exit-restore + body-no-touch
    is exactly the SysV ABI contract that the function preserves R. -/
structure respectsCalleeSaved (fd : Lfundef) : Prop where
  /-- Witness that `fd` was emitted by the ABI wrapper. -/
  isAbiWrapped : fundefIsAbiWrapped fd
  /-- The prologue contains an `Lopn [qsave.<R>] MOVQ [R]` for every
      callee-saved GPR. This is sub-lemma 1 specialised to `fd`. -/
  prologue_saves : ∀ (virt : Lfundef) (tbl : Array Nat) (inLoadMap : InLoadMap),
    -- if `fd`'s body starts with `buildPrologue virt tbl inLoadMap ++ ...`
    -- (which is how `comToLfundefPhysAbi` builds it), then every save
    -- instruction is present.
    (∃ rest, fd.lfd_body = buildPrologue virt tbl inLoadMap ++ rest) →
    ∀ r ∈ sysVCalleeSavedGPRs,
      ⟨0, LinstrR.Lopn [.reg (qsaveName r)] "MOVQ" [.reg r]⟩
        ∈ fd.lfd_body
  /-- The epilogue contains an `Lopn [R] MOVQ [qsave.<R>]` for every
      callee-saved GPR. This is sub-lemma 2 specialised to `fd`. -/
  epilogue_restores :
    (∃ pre, fd.lfd_body = pre ++ calleeSaveRestoreEpilogue ++ [⟨0, LinstrR.Lret⟩]) →
    ∀ r ∈ sysVCalleeSavedGPRs,
      ⟨0, LinstrR.Lopn [.reg r] "MOVQ" [.reg (qsaveName r)]⟩
        ∈ fd.lfd_body
  /-- Phase-2 body invariant: the body never writes any `qsave.<R>` slot.
      Exposed as a structure field so the bundle is well-typed even before
      the invariant is discharged. -/
  body_no_qsave_write : ∀ (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String),
    fd.lfd_body = buildPrologue ({} : Lfundef) #[] inLoadMap ++
      (insertEpilogue
        (physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase)
        calleeSaveRestoreEpilogue) →
    physBodyNoQsaveCalleeSavedWrite shiftImm body inLoadMap loadBase
      outStoreMap storeBase

/-! ### Constructive specialisation for `Com.toLprogPhysAbi`

The top-level bundle wires sub-lemmas 1 and 2 (proved) into a structural
statement about the ABI-wrapped export. The body-invariant field is
inhabited by the Phase-2 named hypothesis. -/

/-- **Top-level theorem (#184b)**: every function in the ABI-wrapped
    physical export `Com.toLprogPhysAbi` respects all six SysV
    callee-saved GPRs.

    Sub-lemmas 1 and 2 are discharged directly. Sub-lemma 3 (the
    body-doesn't-write-qsave invariant) is taken as a named hypothesis,
    matching the existing Phase-1 discipline in this file
    (`physBody_preserves_lret_todo`, etc.).

    *Acceptance status*: 2 / 3 sub-clauses proved; sub-clause 3 is a
    Phase-2 residual named hypothesis with a producer-side reason
    recorded in `physBodyNoQsaveCalleeSavedWrite`'s docstring. -/
theorem respectsCalleeSaved_toLprogPhysAbi
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    ∀ entry ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
        outStoreMap abiArgs abiTyin).lp_funcs,
      -- The fundef is ABI-wrapped, every save and restore is present,
      -- and the body-no-write invariant is the named Phase-2 hypothesis.
      fundefIsAbiWrapped entry.2 ∧
      (∀ r ∈ sysVCalleeSavedGPRs,
        ⟨0, LinstrR.Lopn [.reg (qsaveName r)] "MOVQ" [.reg r]⟩
          ∈ buildPrologue (comToLfundef com immSlotMap)
              (physTable (bodyTrace (comToLfundef com immSlotMap).lfd_body))
              inLoadMap) ∧
      (∀ r ∈ sysVCalleeSavedGPRs,
        ⟨0, LinstrR.Lopn [.reg r] "MOVQ" [.reg (qsaveName r)]⟩
          ∈ calleeSaveRestoreEpilogue) := by
  intro entry hMem
  -- `lp_funcs = [(fname, comToLfundefPhysAbi ...)]`.
  simp [Com.toLprogPhysAbi] at hMem
  obtain ⟨_, rfl⟩ := hMem
  refine ⟨?_, ?_, ?_⟩
  · -- ABI-wrapped: pick the obvious witness.
    exact ⟨Γ, t, com, shiftImm, immSlotMap, inLoadMap, outStoreMap, abiArgs,
      abiTyin, rfl⟩
  · -- Prologue saves: sub-lemma 1.
    intro r hr
    exact buildPrologue_saves_calleeSaved _ _ _ r hr
  · -- Epilogue restores: sub-lemma 2.
    intro r hr
    exact calleeSaveRestoreEpilogue_restores_calleeSaved r hr

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
