/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Std.Data.HashMap

/-!
# Mirror types of jasmin's `Linear.lprog`

The Lean value-level mirror of the linear IR of jasmin (`proofs/lang/linear.v`):
labels, operands, instructions, function definitions and programs. Register and
opcode names are carried as `String`, labels and sizes as `Nat`.

## Main definitions

* `LOperand`, `LinstrR`, `Linstr`, `Lcmd`: operands, instructions and bodies.
* `Lfundef`: a linear function definition (`lfundef`).
* `Lprog`: a linear program (`lprog`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Lean mirror types for `Linear.lprog`

Each type mirrors a Coq record/variant in `proofs/lang/linear.v`. Abstract /
architecture-specific leaves are carried as `String`/`Nat` (see module header). -/

/-- Mirror of jasmin `label` (a positive index) and `label_kind`. -/
abbrev LLabel := Nat

/-- Mirror of `label_kind` (`InternalLabel` / `ExternalLabel`). -/
inductive LabelKind where
  | internal
  | external
  deriving DecidableEq, Repr

/-- A simple register/expression operand. The Coq `lexpr`/`rexpr`/`fexpr` ASTs
    are far richer (memory operands, sub-words, conditions); the word-level
    two-address `JasminOp` fragment only ever needs a named register, an array
    element, or an immediate, so we carry that surface here. -/
inductive LOperand where
  /-- A named register, e.g. `"RAX"`, `"w0"`. -/
  | reg (name : String)
  /-- An array element `base[idx]`, e.g. `k[3]`. -/
  | arr (base : String) (idx : Nat)
  /-- A compile-time immediate. -/
  | imm (value : Nat)
  /-- A **register-indexed (SIB) array element** `base[idx*scale]`, where both
      `base` and `idx` name registers and `scale` is the compile-time element
      stride in bytes (the x86 `(%base,%idx,scale)` effective address). This is
      the runtime-index image of `stackLoad`/`stackStore`: the array element
      whose offset is a *register* (`Pvar idx`) scaled by the element width,
      rather than a compile-time `Nat` (`.arr`). The reader materialises it as
      the x86 base+index*scale memory reference. -/
  | arrIdx (base idx : String) (scale : Nat)
  deriving DecidableEq, Repr

/-- Mirror of `Linear.linstr_r`: all ten constructors of the Coq variant.

    `Lopn` carries the destinations (`lexprs`), the operation name (a textual
    stand-in for the `sopn` x86 extended-op value), and the sources (`rexprs`).
    The control-flow constructors carry the same payload shape as Coq, with
    abstract leaves as `String`/`Nat`. -/
inductive LinstrR where
  /-- `Lopn lexprs sopn rexprs`: write `dsts`, applying op `opn` to `srcs`. -/
  | Lopn (dsts : List LOperand) (opn : String) (srcs : List LOperand)
  /-- `Lsyscall syscall_t`. -/
  | Lsyscall (name : String)
  /-- `Lcall (option var_i) remote_label`. -/
  | Lcall (ra : Option String) (target : String × LLabel)
  /-- `Lret`. -/
  | Lret
  /-- `Lalign`. -/
  | Lalign
  /-- `Llabel label_kind label`. -/
  | Llabel (kind : LabelKind) (lbl : LLabel)
  /-- `Lgoto remote_label`. -/
  | Lgoto (target : String × LLabel)
  /-- `Ligoto rexpr`: absolute indirect jump. -/
  | Ligoto (target : LOperand)
  /-- `LstoreLabel var label`. -/
  | LstoreLabel (dst : String) (lbl : LLabel)
  /-- `Lcond fexpr label`. -/
  | Lcond (cond : LOperand) (lbl : LLabel)
  deriving Repr

/-- Mirror of `Linear.linstr = MkLI { li_ii ; li_i }`. `li_ii` (`instr_info`)
    is a source-position tag; we carry it as an opaque `Nat`. -/
structure Linstr where
  li_ii : Nat
  li_i : LinstrR
  deriving Repr

/-- Mirror of `Linear.lcmd = seq linstr`. -/
abbrev Lcmd := List Linstr

/-- Mirror of `Linear.lfundef`. Every field of the Coq record is present;
    abstract/architecture leaves are `String`/`Nat`. `lfd_tyin`/`lfd_tyout`
    carry the bit widths of the in/out registers (the `ltype` `U w` cases). -/
structure Lfundef where
  /-- `lfd_info : fun_info` (opaque position tag). -/
  lfd_info : Nat := 0
  /-- `lfd_align : wsize` (alignment, as a byte count). -/
  lfd_align : Nat := 1
  /-- `lfd_tyin : seq ltype` (argument register widths). -/
  lfd_tyin : List Nat := []
  /-- `lfd_arg : seq var_i` (argument register names). -/
  lfd_arg : List String := []
  /-- `lfd_body : lcmd`. -/
  lfd_body : Lcmd := []
  /-- `lfd_tyout : seq ltype` (result register widths). -/
  lfd_tyout : List Nat := []
  /-- `lfd_res : seq var_i` (result register names). -/
  lfd_res : List String := []
  /-- `lfd_export : bool`. -/
  lfd_export : Bool := true
  /-- `lfd_callee_saved : seq var`. -/
  lfd_callee_saved : List String := []
  /-- `lfd_stk_max : Z`. -/
  lfd_stk_max : Nat := 0
  /-- `lfd_frame_size : Z`. -/
  lfd_frame_size : Nat := 0
  /-- `lfd_align_args : seq wsize`. -/
  lfd_align_args : List Nat := []
  deriving Repr

/-- Mirror of `Linear.lprog`. `lp_rip`/`lp_rsp` are `Ident.ident` in Coq
    (abstract); the conventional register names are `"RIP"`/`"RSP"`. -/
structure Lprog where
  /-- `lp_rip : Ident.ident`. -/
  lp_rip : String := "RIP"
  /-- `lp_rsp : Ident.ident`. -/
  lp_rsp : String := "RSP"
  /-- `lp_globs : seq u8`. -/
  lp_globs : List Nat := []
  /-- `lp_glob_names : seq (var * wsize * Z)`. -/
  lp_glob_names : List (String × Nat × Nat) := []
  /-- `lp_funcs : seq (funname * lfundef)`. -/
  lp_funcs : List (String × Lfundef) := []
  deriving Repr

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
