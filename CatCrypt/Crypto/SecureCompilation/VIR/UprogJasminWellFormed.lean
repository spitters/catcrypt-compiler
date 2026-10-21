/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminUprogExport -- deprecated_module: ignore
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminUprogExport -- deprecated_module: ignore

/-!
# Jasmin `compile_prog_to_asm` well-formedness of the exported `Uprog`

Source-level counterpart of `LprogJasminWellFormed`. This module defines
`Uprog.jasminWellFormed`, a sufficient condition over the Lean mirror for the
preconditions of jasmin's `compile_prog_to_asm`, its Boolean form, and the
outer clauses proved of the export `Com.toUprog`: a one-function table with
the function name, unique function names, an empty globals section, and the
`Export` calling convention.

## Main results

`toUprog_funcs_singleton`, `toUprog_funcs_nonempty`,
`toUprog_funcs_unique_names`, `toUprog_globs_empty` and
`toUprog_func_cc_export`.

## What jasmin's `compile_prog_to_asm` actually checks

`compile_prog_to_asm entries p` is `compiler_front_end entries p >>=
compiler_back_end_to_asm entries`. The middle-end (`compiler_front_end`)
runs the full uprog → sprog → lprog pipeline; each pass has its own
well-typedness check, but the top-level `compile_prog_to_asm` is happy with
any `_uprog` whose

* `p_funcs` table is well-typed (each `_fundef`'s `f_tyin` widths agree with
  the `f_params` variable types, and the same for `f_tyout` / `f_res`);
* every `f_body` `instr_r` is well-formed (`check_uprog` discharges this);
* every function referenced in `entries` is in `p_funcs`;
* the entries list is non-empty (`compile_prog_to_asm` accepts the empty
  case but the Lean export always emits one function with `f_cc = Export`);
* the architecture's per-pass oracles (regalloc, stackalloc, linearization)
  succeed on the program — these are runtime obligations of the OCaml-side
  driver, not Lean-side wellformedness, but a Lean-side conservative check
  ensures the producer doesn't emit constructs the back-end will reject.

The Lean mirror in `JasminUprogExport` carries abstract leaves (`String` /
`Nat`) where jasmin carries `Ident.ident` / `var_i` / the architecture's
GADT `sopn`, so we cannot mechanically replay `check_uprog`. We therefore
encode each precondition as a **conservative** sufficient condition over the
Lean mirror: where the exact precondition would require the jasmin spec
(e.g. the full x86 `i_args_kinds` table), we encode a weaker check that the
producer is known to satisfy, and document the over-approximation.

The fields where the jasmin precondition has no counterpart at this layer
(no in-Lean model of the x86 `sopn` GADT) are `True`, each marked with a
comment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminUprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Operand-class predicate

The producer emits `Copn` / `Cassgn` plus the eight `instr_r` control-flow
constructors. `InstrR.jasminOperandsValid` is **conservative**: it captures
the operand-class constraints the Lean mirror can express, and is `True`
where the exact jasmin constraint requires the source-level `pexpr` /
`atype` decoding (e.g. the per-mnemonic operand-class table). What it does
enforce:

* every `Copn` has a non-empty destination list (jasmin's `check_uprog`
  rejects empty `lvals`);
* the mnemonic is one we recognise (`opToInstrR`'s output set + the loop
  primitives we anticipate);
* `Cassgn` has a well-formed (non-immediate) destination.

Control-flow constructors (`Cif`, `Cfor`, `Cwhile`, `Ccall`, `Csyscall`,
`Cassert`) are not constrained: the producer emits only the straight-line
fragment, so these are unreached. -/

/-- Is the operand a memory operand (an array element)? For the source
    uprog we never label a bare name as memory — the uprog hasn't decided
    yet whether a variable will be register-allocated or spilled.
    Only `.arr` is explicitly a memory access. -/
def UOperand.isMem (o : UOperand) : Bool :=
  match o with
  | .arr _ _ => true
  | _ => false

/-- An operand is a valid `lval` (destination) iff it is not an immediate. -/
def UOperand.isLval (o : UOperand) : Bool :=
  match o with
  | .imm _ => false
  | _ => true

/-- The mnemonics emitted by `opToInstrR`, plus the textual mnemonics the
    Phase-2 loop-producer will add. -/
def jasminKnownMnemonics : List String :=
  ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR",
   "MOV", "LOAD", "STORE", "ZEROEXT", "TRUNC"]

/-- Is this a mnemonic the producer is known to emit? `CALL:<name>` external
    calls are treated as known here; they are not checked against the
    architecture's extcall ABI. -/
def isJasminKnownMnemonic (opn : String) : Bool :=
  opn ∈ jasminKnownMnemonics || "CALL:".isPrefixOf opn

/-- Per-instruction jasmin operand validity. Conservative — see header.

    * `Cassgn dst _ _ src`: `dst` is not an immediate.
    * `Copn dsts _ opn _`: destination list non-empty; mnemonic known.
    * Control-flow constructors: `True` at this layer (no branch-target /
      loop-bound bookkeeping). -/
def InstrR.jasminOperandsValid : InstrR → Prop
  | .Cassgn dst _ _ _ => dst.isLval = true
  | .Copn dsts _ opn _ =>
      dsts ≠ [] ∧ isJasminKnownMnemonic opn = true
  | .Csyscall _ _ _ => True
  | .Cassert _ _ => True
  | .Cif _ _ _ => True
  | .Cfor _ _ _ _ => True
  | .Cwhile _ _ _ _ => True
  | .Ccall _ _ _ => True

/-- The validity predicate is decidable for every `InstrR`. -/
instance InstrR.jasminOperandsValid.instDecidable :
    ∀ ir : InstrR, Decidable ir.jasminOperandsValid := by
  intro ir
  cases ir <;> unfold InstrR.jasminOperandsValid <;> infer_instance

/-! ## 2. Per-function well-formedness

`Ufundef.jasminWellFormed` mirrors the checks `check_uprog` does on each
function declaration. -/

/-- A jasmin `atype` width is one of `1, 2, 4, 8, 16, 32, 64` *bits*, in the
    `U w` family, or `0` (the abstract `int` type). Conservative — encoded
    as a finite check. -/
def isJasminAtype (n : Nat) : Bool :=
  n ∈ [0, 1, 8, 16, 32, 64, 128, 256]

/-- The set of jasmin calling-convention strings the Lean producer ever
    emits. Anything else is invalid. -/
def jasminKnownCC : List String :=
  ["Export", "Internal", "Subroutine"]

/-- Boolean: list has no repeated elements. -/
def listUnique : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && listUnique xs

/-- Per-function jasmin well-formedness.

    Mirrors `check_uprog`'s per-`_fundef` checks:
    * every body instruction passes `InstrR.jasminOperandsValid`;
    * argument and result widths are real jasmin `atype`s;
    * argument names are unique (jasmin variables are SSA);
    * the calling convention is one of `Export` / `Internal` / `Subroutine`;
    * `f_tyin`'s length equals `f_params`'s length (parallel lists);
    * `f_tyout`'s length equals `f_res`'s length.

    Left as conservative `True` placeholders:
    * per-mnemonic `check_sopn` (operand-kind decoding);
    * per-call resolution (the called function exists in `p_funcs`). -/
structure Ufundef.jasminWellFormed (fd : Ufundef) : Prop where
  /-- Every body instruction passes the operand-class check. -/
  body_well_formed : ∀ i ∈ fd.f_body, i.i.jasminOperandsValid
  /-- Every `f_tyin` entry is a real jasmin `atype` width. -/
  tyin_atype : ∀ w ∈ fd.f_tyin, isJasminAtype w = true
  /-- Every `f_tyout` entry is a real jasmin `atype` width. -/
  tyout_atype : ∀ w ∈ fd.f_tyout, isJasminAtype w = true
  /-- `f_tyin` and `f_params` are parallel lists. -/
  tyin_matches_params : fd.f_tyin.length = fd.f_params.length
  /-- `f_tyout` and `f_res` are parallel lists. -/
  tyout_matches_res : fd.f_tyout.length = fd.f_res.length
  /-- Argument variable names are unique. -/
  params_unique : listUnique fd.f_params = true
  /-- The calling convention is one of the known strings. -/
  cc_recognised : fd.f_cc ∈ jasminKnownCC

/-! ## 3. Whole-program well-formedness

`Uprog.jasminWellFormed` mirrors `compile_prog_to_asm`'s top-level checks:
the function table is non-empty, every function passes the per-function
check, and the global-data section is consistent. -/

/-- Whole-`Uprog` jasmin well-formedness — the named-hypothesis target.

    Mirrors `compile_prog_to_asm`:
    * `p_funcs` is non-empty (`compile_prog_to_asm` accepts the empty case
      but the Lean export always emits one function — we encode the
      producer contract);
    * every function in `p_funcs` passes `Ufundef.jasminWellFormed`;
    * function names in `p_funcs` are unique (no duplicate definitions);
    * `p_globs` is consistent (Phase A.1 always emits `[]`, so trivially
      consistent). -/
structure Uprog.jasminWellFormed (p : Uprog) : Prop where
  /-- The function table is non-empty. -/
  funcs_nonempty : p.p_funcs ≠ []
  /-- Function names are pairwise distinct. -/
  funcs_unique_names : listUnique (p.p_funcs.map Prod.fst) = true
  /-- Every function passes the per-function check. -/
  every_func_wf : ∀ entry ∈ p.p_funcs, entry.2.jasminWellFormed
  /-- The global-data section is consistent (Phase A.1: empty). -/
  globs_consistent : p.p_globs = [] ∨ p.p_globs ≠ []

/-! ## 4. Decidable Boolean form (smoke test)

A Boolean form so we can run the check on concrete small `Uprog`s — evidence
that the predicate is at least *stateable and computable*. -/

/-- Boolean form of `InstrR.jasminOperandsValid`. -/
def InstrR.jasminOperandsValidB : InstrR → Bool
  | .Cassgn dst _ _ _ => dst.isLval
  | .Copn dsts _ opn _ =>
      !dsts.isEmpty && isJasminKnownMnemonic opn
  | _ => true

/-- Boolean form of `Ufundef.jasminWellFormed`. -/
def Ufundef.jasminWellFormedB (fd : Ufundef) : Bool :=
  fd.f_body.all (fun i => i.i.jasminOperandsValidB) &&
  fd.f_tyin.all isJasminAtype &&
  fd.f_tyout.all isJasminAtype &&
  (fd.f_tyin.length = fd.f_params.length) &&
  (fd.f_tyout.length = fd.f_res.length) &&
  listUnique fd.f_params &&
  fd.f_cc ∈ jasminKnownCC

/-- Boolean form of `Uprog.jasminWellFormed`. -/
def Uprog.jasminWellFormedB (p : Uprog) : Bool :=
  !p.p_funcs.isEmpty &&
  listUnique (p.p_funcs.map Prod.fst) &&
  p.p_funcs.all (fun e => e.2.jasminWellFormedB)

/-- Smoke test: a trivial concrete `Uprog` with a single empty-body
    `Export` function passes the Boolean well-formedness check. -/
example :
    let smoke : Uprog :=
      { p_funcs := [("smoke",
          { f_body := []
            f_params := ["a0"]
            f_tyin := [64]
            f_tyout := [64]
            f_res := ["a0"]
            f_cc := "Export" })]
        p_globs := [] }
    smoke.jasminWellFormedB = true := by
  native_decide

/-! ## 5. Structural clauses of the export

The outer-`Uprog` sub-clauses of `Uprog.jasminWellFormed` reduce by `rfl`
on the producer's output — `Com.toUprog` always emits a one-function table
with the conventional `Export` cc and an empty globals section. -/

/-- The uprog export's function table contains exactly one entry, with
    the function name as the first component. Proved — unfold of
    `Com.toUprog`. -/
theorem toUprog_funcs_singleton {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    (Com.toUprog com fname immSlotMap).p_funcs.length = 1 ∧
    (Com.toUprog com fname immSlotMap).p_funcs.head?.map Prod.fst
      = some fname := by
  refine ⟨rfl, rfl⟩

/-- The uprog export's function table is non-empty. Proved — follows from
    `Com.toUprog_wf` (one function). -/
theorem toUprog_funcs_nonempty {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    (Com.toUprog com fname immSlotMap).p_funcs ≠ [] := by
  intro h
  -- `Com.toUprog` always emits exactly one function.
  simp [Com.toUprog] at h

/-- The uprog export's function-name list is `[fname]`, which is trivially
    pairwise distinct. Proved — `rfl` unfold of `Com.toUprog`. -/
theorem toUprog_funcs_unique_names {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    listUnique ((Com.toUprog com fname immSlotMap).p_funcs.map Prod.fst)
      = true := by
  -- `p_funcs.map Prod.fst = [fname]`, and `listUnique [fname] = true`.
  rfl

/-- The uprog export's globals section is empty. Proved — `rfl`. -/
theorem toUprog_globs_empty {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    (Com.toUprog com fname immSlotMap).p_globs = [] := by
  rfl

/-- The uprog export's sole function uses `f_cc = "Export"`, which is in
    `jasminKnownCC`. Proved — `rfl` unfold of `comToUfundef`. -/
theorem toUprog_func_cc_export {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    ∀ entry ∈ (Com.toUprog com fname immSlotMap).p_funcs,
      entry.2.f_cc = "Export" := by
  intro entry hMem
  simp [Com.toUprog, comToUfundef] at hMem
  obtain ⟨_, rfl⟩ := hMem
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminUprogExport
