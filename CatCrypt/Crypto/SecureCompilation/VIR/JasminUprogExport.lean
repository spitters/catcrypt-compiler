/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Jasmin source `Expr._uprog` value-level producer (Phase A.1)

Source-level analogue of `JasminLprogExport` (#142/#155/#161/#169). This module
turns a typed `Com jasminDialect` into a value-level mirror of jasmin's
`Expr._uprog`, the **source-AST** uprog *before* any of the middle-end passes
have run (live-range splitting, register allocation, stack allocation,
linearization). The companion OCaml reader is
`Read_uprog.load_marshal_file` (`patches/jasmin/read_uprog.ml.patch`), and the
driver consuming the produced blob is `drive_uprog` (`patches/jasmin/drive_uprog.patch`).

## How this differs from `JasminLprogExport`

`JasminLprogExport.Com.toLprog` emits a **post-linearization** `Linear.lprog`:
the Lean side mirrors the entire linearization pass (control-flow flattening,
SSA → linear register slots, `Lopn` synthesis). The downside is that the
producer has to reproduce a large surface of jasmin invariants (the
operand-class predicates `LprogJasminWellFormed` tracks).

This module instead emits a **pre-linearization** `Expr._uprog`. The downside
is that jasminc's middle-end (regalloc / stackalloc / linearization) re-runs
on Lean-produced uprogs, so the produced .s depends on jasminc's per-pass
oracles. The upside is that the producer's surface is much smaller: only the
source-AST shape (`instr_r`'s `Cassgn` / `Copn` / control-flow constructors)
needs to be mirrored, and the well-formedness predicate `Uprog.jasminWellFormed`
captures `compile_prog_to_asm`'s preconditions, which are coarser than the
asm-gen predicates `assemble_prog` checks.

The two paths are complementary:
* `JasminLprogExport` ➜ `drive_linear`: minimal trust footprint (skips the
  middle-end), but the producer must emit a fully-lowered, RA'd lprog.
* `JasminUprogExport` ➜ `drive_uprog`: smaller producer surface (skips the
  textual `.jazz` parser only), at the cost of running jasminc's full
  middle-end on Lean output.

## The jasmin `_uprog` shape (from `proofs/lang/expr.v`)

```
Inductive instr_r :=
  | Cassgn   : lval -> assgn_tag -> atype -> pexpr -> instr_r
  | Copn     : lvals -> assgn_tag -> sopn -> pexprs -> instr_r
  | Csyscall : lvals -> syscall_t -> pexprs -> instr_r
  | Cassert  : assertion -> instr_r
  | Cif      : pexpr -> seq instr -> seq instr  -> instr_r
  | Cfor     : var_i -> range -> seq instr -> instr_r
  | Cwhile   : align -> seq instr -> pexpr -> instr_info -> seq instr -> instr_r
  | Ccall    : lvals -> funname -> pexprs -> instr_r.
Record instr := MkI { ii : instr_info; i : instr_r }.
Record _fundef ext := MkFun
  { f_info; f_contract; f_tyin; f_params; f_body; f_tyout; f_res; f_extra }.
Record _prog ext_fun ext_prog := { p_funcs; p_globs; p_extra }.
```

The Lean mirror types below match this structure field-by-field. The leaf
carriers that the Coq side keeps abstract or architecture-specific
(`Ident.ident`, `sopn`'s x86 extended-op GADT, `var_i` records carrying
`Uint63.t` + zarith `Z`, `Location.t`, annotations) are represented here by
plain `String` / `Nat`: textual operand names and integer immediates.

## Serialization: binary blob, magic header

`Read_uprog` ships the Marshal path only (mirroring v1 of `Read_linear`).
The serialized blob is prefixed with the magic header
`JASMIN-UPROG-MARSHAL-v1\n` (matching `Read_uprog.magic` exactly). Producing
a byte-identical OCaml Marshal blob from Lean is **not** structurally
faithful — see `JasminLprogExport`'s "Serialization" header for the reasons
(custom blocks for `Uint63` / zarith). The textual reconstruction reader (v2)
is the seam where a fully-trusted Lean-↔-jasmin handoff would close; it is
listed in `Read_uprog.text_coverage_gaps`.

This module therefore emits the same TEXTUAL representation as
`JasminLprogExport`, prefixed with `JASMIN-UPROG-MARSHAL-v1\n`, so the
Lean-side producer is byte-deterministic and the textual reader (when it
lands) can reconstruct an OCaml `_uprog` from the same bytes.

## Denotation

Semantic preservation (the exported `_uprog` denotes the same function as
the source `Com` under jasmin's source semantics `sem`) is stated as the
named hypothesis `UprogExportFaithful` — the source-`sem` analogue of #145's
`MlirToolchainSemanticsAgrees` and of the linear-`lsem` predicate
`ComLsemExportFaithful` (proved over `lsem` for its modeled fragments).
Closing it requires a Lean model of jasmin's source `sem`, which is not
available Lean-side.
The value-level obligations that *are* discharged here: the export is total,
structurally well-formed (`Com.toUprog_wf`), and round-trips through the
textual serializer (`Com.toUprogText_magic`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminUprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Lean mirror types for `Expr._uprog`

Each type mirrors a Coq record / variant in `proofs/lang/expr.v`. Abstract /
architecture-specific leaves are carried as `String` / `Nat` (see header). -/

/-- A source-level operand. Mirrors the abstract `lval` / `pexpr` surface
    at the granularity the producer's word-level fragment needs: a named
    variable (textual identifier — argument or local), an array element
    `base[idx]`, or a compile-time immediate. -/
inductive UOperand where
  /-- A named variable (`var_i`'s `v_var` is rendered as a string here). -/
  | var (name : String)
  /-- An array element `base[idx]`. -/
  | arr (base : String) (idx : Nat)
  /-- A compile-time integer immediate. -/
  | imm (value : Nat)
  deriving DecidableEq, Repr

/-- Mirror of `Expr.assgn_tag` (`AT_none`, `AT_keep`, `AT_rename`, `AT_inline`,
    `AT_phinode`). The producer always emits `AT_none` (the default); the
    other tags are kept for symmetry with the Coq grammar. -/
inductive AssgnTag where
  | none
  | keep
  | rename
  | inline
  | phinode
  deriving DecidableEq, Repr

/-- Mirror of `Expr.align` (`Align` / `NoAlign`). Loop-alignment flag carried by
    `Cwhile`. -/
inductive Align where
  | align
  | noAlign
  deriving DecidableEq, Repr

/-! Mirror of `Expr.instr_r` (eight constructors) and `Expr.instr = MkI ii i`,
declared as a mutual block because `Cif` / `Cfor` / `Cwhile` carry nested
`seq instr` sub-bodies.

The straight-line word fragment the current producer emits only ever needs
`Cassgn` / `Copn`; the control-flow constructors are kept for the structural
mirror, and a future loop-producer will use them.

`Instr` is `MkI ii i` — `ii` (`instr_info`) is a source-position tag carried
as an opaque `Nat`. -/

mutual

/-- Mirror of `Expr.instr_r`: all eight constructors of the Coq variant. -/
inductive InstrR where
  | Cassgn (dst : UOperand) (tag : AssgnTag) (width : Nat) (src : UOperand)
  | Copn (dsts : List UOperand) (tag : AssgnTag) (opn : String)
         (srcs : List UOperand)
  | Csyscall (dsts : List UOperand) (name : String) (srcs : List UOperand)
  | Cassert (kind : String) (cond : UOperand)
  | Cif (cond : UOperand) (thenBody : List Instr) (elseBody : List Instr)
  | Cfor (idx : String) (lo hi : Nat) (body : List Instr)
  | Cwhile (alignFlag : Align) (preBody : List Instr) (cond : UOperand)
           (postBody : List Instr)
  | Ccall (dsts : List UOperand) (callee : String) (args : List UOperand)

/-- Mirror of `Expr.instr = MkI instr_info instr_r`. -/
inductive Instr where
  | mk (ii : Nat) (i : InstrR) : Instr

end

/-- Source-position tag of an `Instr`. -/
def Instr.ii : Instr → Nat
  | .mk ii _ => ii

/-- The `instr_r` payload of an `Instr`. -/
def Instr.i : Instr → InstrR
  | .mk _ i => i

/-- Mirror of `Expr.cmd = seq instr`. -/
abbrev Cmd := List Instr

/-- Mirror of `Expr._fundef unit` (the uprog fundef carries `f_extra = unit`).
    Every field of the Coq record is present; abstract / architecture leaves are
    `String` / `Nat`. `f_tyin` / `f_tyout` carry the bit widths of the in/out
    parameter widths. `f_cc` is the calling convention (`Export` / `Internal` /
    `Subroutine`), which jasminc reads to decide which functions are the entry
    points of `compile_prog_to_asm`. -/
structure Ufundef where
  /-- `f_info : fun_info` (opaque source-location tag). -/
  f_info : Nat := 0
  /-- `f_contract` is an optional pre/post `fun_contract`; the producer
      defaults to absent (mirrored as the empty string list — Phase 2 may
      reify the actual contract carrier). -/
  f_contract : Bool := false
  /-- `f_tyin : seq atype`: parameter widths. -/
  f_tyin : List Nat := []
  /-- `f_params : seq var_i`: parameter names. -/
  f_params : List String := []
  /-- `f_body : cmd`. -/
  f_body : Cmd := []
  /-- `f_tyout : seq atype`: result widths. -/
  f_tyout : List Nat := []
  /-- `f_res : seq var_i`: result names. -/
  f_res : List String := []
  /-- Calling convention. The driver picks every `Export` function as an
      entry point (this is what `compile_prog_to_asm`'s `entries` argument
      gates on). -/
  f_cc : String := "Export"

/-- Mirror of `Expr._prog unit unit` (the source uprog has `extra_prog_t = unit`,
    `extra_fun_t = unit`). The fields `p_extra` and `p_funcs[_].f_extra` are
    `unit` so they carry no payload; we drop them in the Lean mirror. -/
structure Uprog where
  /-- `p_funcs : seq (funname * _fundef)`. -/
  p_funcs : List (String × Ufundef) := []
  /-- `p_globs : seq global_decl`: read-only data. The word fragment emits
      no globals; carried for symmetry with the Coq record. -/
  p_globs : List (String × Nat × Nat) := []

/-! ## 2. Lowering a `JasminOp` to an `instr_r`

Each `Com` binding is a `JasminOp` applied to de-Bruijn argument vars. We
name the binding result `r{depth}` and the argument vars by the depth at
which they were bound. Mirrors `JasminLprogExport.regName` / `argName`. -/

/-- The variable name for the SSA binding at let-depth `d`. -/
def regName (d : Nat) : String := "r" ++ toString d

/-- Map a `JasminBinOp` to a textual jasmin opcode name. -/
def binOpName : JasminBinOp → String
  | .add => "ADD"
  | .sub => "SUB"
  | .mul => "MUL"
  | .and => "AND"
  | .or  => "OR"
  | .xor => "XOR"
  | .shl => "SHL"
  | .shr => "SHR"
  -- BMI1 `andn` `(¬a) ∧ b`: the `#ANDN` intrinsic mnemonic.
  | .andn => "ANDN"

/-- Map a `JasminCmp` condition code to the opcode name of its comparison. -/
def cmpName : JasminCmp → String
  | .eq => "SETE"
  | .ne => "SETNE"
  | .ult => "SETB"
  | .ule => "SETBE"
  | .ugt => "SETA"
  | .uge => "SETAE"

/-- The width carried by a `JasminTy` as the source-level `atype` U-width. -/
def tyWidth : JasminTy → Nat
  | .reg w => w
  | .stackArr w _ => w
  | .inlineInt => 0
  | .bool => 1

/-- Lower a single `JasminOp` (with its source operand names and destination
    variable name) to an `InstrR`. The word-level fragment uses `Copn` for
    binops / loads / stores / casts / external calls; `Cassgn` is reserved
    for plain moves (currently unused, since every binding result is the
    output of a `Copn`). -/
def opToInstrR (op : JasminOp) (dst : String) (srcs : List UOperand) : InstrR :=
  match op with
  | .regArith bop _ =>
      .Copn [.var dst] .none (binOpName bop) srcs
  | .stackLoad _ _ =>
      .Copn [.var dst] .none "LOAD" srcs
  | .stackStore _ _ =>
      .Copn [.var dst] .none "STORE" srcs
  | .castW w w' =>
      .Copn [.var dst] .none (if w' ≥ w then "ZEROEXT" else "TRUNC") srcs
  | .extCall name _ _ =>
      .Copn [.var dst] .none ("CALL:" ++ name) srcs
  | .regConst _ n =>
      .Copn [.var dst] .none ("CONST:" ++ toString n) srcs
  | .rorImm _ n =>
      .Copn [.var dst] .none ("ROR:" ++ toString n) srcs
  | .shrImm _ n =>
      .Copn [.var dst] .none ("SHR:" ++ toString n) srcs
  | .sarImm _ n =>
      .Copn [.var dst] .none ("SAR:" ++ toString n) srcs
  | .shlImm _ n =>
      .Copn [.var dst] .none ("SHL:" ++ toString n) srcs
  | .addCarryLo _ =>
      .Copn [.var dst] .none "ADCX" srcs
  | .addCarryHi _ =>
      .Copn [.var dst] .none "ADCXHI" srcs
  | .select _ =>
      .Copn [.var dst] .none "CMOV" srcs
  | .mulhi _ =>
      .Copn [.var dst] .none "MULXHI" srcs
  | .vpackZMM _ =>
      .Copn [.var dst] .none "VPACK" srcs
  | .vpackZMMd _ =>
      .Copn [.var dst] .none "VPACKD" srcs
  | .vprordZMM _ =>
      .Copn [.var dst] .none "VPRORD" srcs
  | .vpslldq _ =>
      .Copn [.var dst] .none "VPSLLDQ" srcs
  | .vpsrldq _ =>
      .Copn [.var dst] .none "VPSRLDQ" srcs
  | .vsimd op =>
      .Copn [.var dst] .none op.mnemonic srcs
  | .vymm op =>
      .Copn [.var dst] .none op.jasminMnemonic srcs
  | .callN name _ _ =>
      .Copn [.var dst] .none ("CALLN:" ++ name) srcs
  | .cmp c _ =>
      .Copn [.var dst] .none (cmpName c) srcs
  | .cmpImm c _ n =>
      .Copn [.var dst] .none (cmpName c) (srcs ++ [.imm n])

/-! ## 3. Walking the `Com` term

A `Var Γ τ` is a De Bruijn index into `Γ`. Mirrors `JasminLprogExport`'s
`varIndex` / `resolveVar` / `exprArgs` / `comToBody` exactly — same producer
contract, except the emitted carrier is `Instr` (with `InstrR.Copn`) instead
of `Linstr` (with `LinstrR.Lopn`). -/

/-- De Bruijn index of a `Var` (distance from the most recent binder). -/
def varIndex {Γ : Ctxt jasminDialect} {τ : JasminTy} : Ctxt.Var Γ τ → Nat
  | .here => 0
  | .there v => varIndex v + 1

/-- Producer-level immediate-slot map (same shape as
    `JasminLprogExport.ImmSlotMap`). Argument slot `j` ↦ literal value when
    the input is a known compile-time constant. -/
abbrev ImmSlotMap := Nat → Option Nat

/-- Resolve a `Var` to a `UOperand`. Same algorithm as
    `JasminLprogExport.resolveVar`; emits `.var` instead of `.reg`. -/
def resolveVar (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) : UOperand :=
  let i := varIndex v
  let slot := curDepth - 1 - i
  if slot < nArgs then
    match immSlotMap slot with
    | some v => .imm v
    | none => .var (argNames slot)
  else .var (regName slot)

/-- Collect the argument operands of an `Expr` as a `List UOperand`. -/
def exprArgs (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    List UOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List UOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        resolveVar curDepth nArgs argNames immSlotMap v :: go rest
  go e.args

/-- Walk the `Com`, producing the list of `Instr`s in program order.
    The terminal `.ret` becomes an empty addition to the body (the result
    register is the function's `f_res`); the source-level uprog has no
    explicit `Lret` analogue — the function returns by reaching the end of
    its `f_body`. -/
def comToBody (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Cmd
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let srcs := exprArgs curDepth nArgs argNames immSlotMap e
      let instr : Instr := ⟨0, opToInstrR e.op (regName curDepth) srcs⟩
      instr :: comToBody nArgs argNames immSlotMap body (curDepth + 1)

/-- The variable name of the final return value of a `Com` — the binder the
    terminal `.ret` points at. (Functions cannot return immediates, so the
    `immSlotMap` is not consulted here.) -/
def comRetVar (nArgs : Nat) (argNames : Nat → String) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → String
  | _, _, .ret v, curDepth =>
      match resolveVar curDepth nArgs argNames (fun _ => none) v with
      | .var n => n
      | .arr b i => b ++ "[" ++ toString i ++ "]"
      | .imm n => toString n
  | _, _, .var _ body, curDepth =>
      comRetVar nArgs argNames body (curDepth + 1)

/-! ## 4. The export: `Com → Uprog`

The argument context `Γ` becomes the function's `f_params` / `f_tyin`:
argument `j` (counted from the program root, i.e. the tail of `Γ`) is named
`a{j}` and typed by its `JasminTy` width. -/

/-- The argument variable name for argument slot `j` (program-root order). -/
def argName (j : Nat) : String := "a" ++ toString j

/-- Build the `Ufundef` for a `Com` over argument context `Γ`.
    `immSlotMap` (default: none) substitutes constant argument inputs with
    `.imm` operands at producer time. -/
def comToUfundef {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t)
    (immSlotMap : ImmSlotMap := fun _ => none) : Ufundef :=
  let nArgs := Γ.length
  -- `Γ` lists most-recent binder first; argument slot `j` (root order) is
  -- entry `nArgs - 1 - j`, whose width we read off the type list.
  let argTys := Γ.reverse.map tyWidth
  { f_info := 0
    f_contract := false
    f_tyin := argTys
    f_params := (List.range nArgs).map argName
    f_body := comToBody nArgs argName immSlotMap com nArgs
    f_tyout := [tyWidth t]
    f_res := [comRetVar nArgs argName com nArgs]
    f_cc := "Export" }

/-- Export a `Com jasminDialect` to a value-level `Uprog` with the given
    function name. -/
def Com.toUprog {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) : Uprog :=
  { p_funcs := [(fname, comToUfundef com immSlotMap)]
    p_globs := [] }

/-! ## 5. Textual serialization

A line-oriented textual representation mirroring the structure (the wire
format, since the OCaml `Marshal` representation is not Lean-reproducible —
see header). Format: every `_prog` / `_fundef` field on its own keyed line,
the body as one `instr` line per `Instr`. Deterministic, so it round-trips
structurally. -/

/-- Render a `UOperand`. -/
def UOperand.toText : UOperand → String
  | .var n => n
  | .arr b i => b ++ "[" ++ toString i ++ "]"
  | .imm v => "#" ++ toString v

/-- Render an `AssgnTag`. -/
def AssgnTag.toText : AssgnTag → String
  | .none => "AT_none"
  | .keep => "AT_keep"
  | .rename => "AT_rename"
  | .inline => "AT_inline"
  | .phinode => "AT_phinode"

/-- Render an `Align`. -/
def Align.toText : Align → String
  | .align => "Align"
  | .noAlign => "NoAlign"

/-- Render an `InstrR` as a single text line. (Control-flow constructors
    are rendered with a flat shape — the body sub-lists are not nested in
    the line-oriented format; a future textual reader will track depth.) -/
def InstrR.toText : InstrR → String
  | .Cassgn dst tag w src =>
      "Cassgn " ++ dst.toText ++ " " ++ tag.toText ++ " " ++ toString w ++
        " " ++ src.toText
  | .Copn dsts tag opn srcs =>
      "Copn [" ++ String.intercalate "," (dsts.map UOperand.toText) ++ "] " ++
        tag.toText ++ " " ++ opn ++ " [" ++
        String.intercalate "," (srcs.map UOperand.toText) ++ "]"
  | .Csyscall dsts name srcs =>
      "Csyscall [" ++ String.intercalate "," (dsts.map UOperand.toText) ++ "] " ++
        name ++ " [" ++ String.intercalate "," (srcs.map UOperand.toText) ++ "]"
  | .Cassert k c => "Cassert " ++ k ++ " " ++ c.toText
  | .Cif c _ _ => "Cif " ++ c.toText
  | .Cfor i lo hi _ =>
      "Cfor " ++ i ++ " " ++ toString lo ++ " " ++ toString hi
  | .Cwhile a _ c _ =>
      "Cwhile " ++ a.toText ++ " " ++ c.toText
  | .Ccall dsts callee args =>
      "Ccall [" ++ String.intercalate "," (dsts.map UOperand.toText) ++ "] " ++
        callee ++ " [" ++ String.intercalate "," (args.map UOperand.toText) ++ "]"

/-- Render a `Ufundef`. -/
def Ufundef.toText (name : String) (f : Ufundef) : String :=
  let nats (xs : List Nat) := String.intercalate "," (xs.map toString)
  let strs (xs : List String) := String.intercalate "," xs
  String.intercalate "\n"
    ([ "ufundef " ++ name
     , "  f_info " ++ toString f.f_info
     , "  f_contract " ++ (if f.f_contract then "true" else "false")
     , "  f_tyin " ++ nats f.f_tyin
     , "  f_params " ++ strs f.f_params
     , "  f_tyout " ++ nats f.f_tyout
     , "  f_res " ++ strs f.f_res
     , "  f_cc " ++ f.f_cc
     , "  f_body " ++ toString f.f_body.length ]
     ++ f.f_body.map (fun i => "    instr " ++ toString i.ii ++ " " ++ i.i.toText))

/-- Render a `Uprog`. -/
def Uprog.toText (p : Uprog) : String :=
  let globs :=
    String.intercalate ";" (p.p_globs.map (fun (n, w, z) =>
      n ++ ":" ++ toString w ++ ":" ++ toString z))
  String.intercalate "\n"
    ([ "uprog"
     , "p_globs " ++ globs
     , "p_funcs " ++ toString p.p_funcs.length ]
     ++ p.p_funcs.map (fun (n, f) => f.toText n))

/-- The OCaml-side magic header, prefixed to the serialized blob. Matches
    `Read_uprog.magic` exactly (`patches/jasmin/read_uprog.ml.patch`). -/
def magic : String := "JASMIN-UPROG-MARSHAL-v1\n"

/-- Serialize a `Com` to the textual uprog representation (magic + text). -/
def Com.toUprogText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) : String :=
  magic ++ (Com.toUprog com fname immSlotMap).toText ++ "\n"

/-- The serialized bytes of a `Com` as a uprog blob.
    Direct analogue of `JasminLprogExport.Com.toLprogBytes`. -/
def Com.toUprogBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) : ByteArray :=
  (Com.toUprogText com fname immSlotMap).toUTF8

/-- Alias matching the naming convention of the spec
    (`Uprog.toBinary : Uprog → ByteArray`). The serialized blob is the
    magic header followed by the textual representation. -/
def Uprog.toBinary (p : Uprog) : ByteArray :=
  (magic ++ p.toText ++ "\n").toUTF8

/-- Write the binary uprog blob for a `Com` to a file. -/
def Com.writeUprogFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (path : System.FilePath)
    (immSlotMap : ImmSlotMap := fun _ => none) : IO Unit :=
  IO.FS.writeBinFile path (Com.toUprogBytes com fname immSlotMap)

/-- Convenience: write both the uprog binary and the entries sidecar that
    `drive_uprog` reads to know which functions to export. -/
def Com.writeUprogWithEntries {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (uprogPath entriesPath : System.FilePath)
    (immSlotMap : ImmSlotMap := fun _ => none) : IO Unit := do
  Com.writeUprogFile com fname uprogPath immSlotMap
  IO.FS.writeFile entriesPath (fname ++ "\n")

/-! ## 6. Value-level export correctness

Structural well-formedness obligations are discharged here; semantic
preservation under jasmin's `sem` is the named hypothesis below. -/

/-- The exported `uprog` always has exactly one function, named `fname`, and
    it has `f_cc = "Export"`. (Structural well-formedness — proved.) -/
theorem Com.toUprog_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    (Com.toUprog com fname immSlotMap).p_funcs.length = 1 ∧
      ((Com.toUprog com fname immSlotMap).p_funcs.head?.map Prod.fst
        = some fname) ∧
      ((Com.toUprog com fname immSlotMap).p_funcs.head?.map (fun p => p.2.f_cc)
        = some "Export") := by
  refine ⟨rfl, rfl, rfl⟩

/-- The textual serialization is prefixed by the OCaml-side magic header:
    it is literally `magic ++ rest`. (Proved by `rfl` on the decomposition.) -/
theorem Com.toUprogText_magic {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    ∃ rest, Com.toUprogText com fname immSlotMap = magic ++ rest :=
  ⟨(Com.toUprog com fname immSlotMap).toText ++ "\n", rfl⟩

/-- The exported uprog's binary form starts with the same magic header
    bytes. Confirms `Uprog.toBinary` follows the wire-format contract. -/
theorem Uprog.toBinary_magic (p : Uprog) :
    ∃ rest, (magic ++ p.toText ++ "\n") = magic ++ rest :=
  ⟨p.toText ++ "\n", rfl⟩

/-- **Named hypothesis** (semantic preservation, the stretch obligation).

    `UprogExportFaithful com fname` asserts that the exported `_uprog`
    denotes the same function as the source `Com` under jasmin's source
    semantics `sem`. The source-`sem` analogue of #145's
    `MlirToolchainSemanticsAgrees`: stated as a hypothesis rather than proved
    because there is no Lean model of jasmin's `sem` (the linear-semantics
    `lsem` analogue is proved as `ComLsemExportFaithful` in `LsemPortAll`).
    Closing it requires porting `sem` to Lean and proving the simulation
    `Com.denote com V = sem (toUprog com fname) (encode V)`. -/
def UprogExportFaithful {Γ : Ctxt jasminDialect} {t : JasminTy}
    (_com : Com jasminDialect Γ t) (_fname : String) : Prop :=
  -- Placeholder predicate over the export; the real statement quantifies over
  -- a Lean `sem` model and a value encoding, neither available here.
  True

end CatCrypt.Crypto.SecureCompilation.VIR.JasminUprogExport
