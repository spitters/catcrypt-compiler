/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Model
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Lowering the scalar `lprog` `Lopn` fragment to the x86 model (#148 POC)

We lower *from* jasmin's `Linear.lprog` (`VIR/JasminLprogExport.lean`), the
already-linearized two-address IR, rather than from the Veir/MLIR scalar
subset. Rationale:

* `lprog` is the **last IR before machine code** in the verified pipeline; its
  operands are already named registers / immediates (`LOperand.reg`/`.imm`),
  and its `Lopn`s are emitted in destructive two-address form
  (`Com.toLprogPhys`'s `mov dst,src0; op dst,src1`). The map to x86 two-address
  instructions is essentially the identity on opcodes.
* Its arithmetic carrier is `JasminBinOp` with the clean `BitVec` denotation
  `JasminBinOp.apply`, giving a direct source semantics to match against.
* The Veir/MLIR scalar subset is one lowering step further from the machine and
  would re-introduce the SSA→two-address step we want to keep upstream.

## What this lowers

A two-address `Lopn [reg dst] opn [src]` (the destination is implicitly also
source 0) maps to the matching `Instr` arm; an `Lopn [reg dst] "MOV"/"LOAD"
[src]` to `mov`. We translate operands `LOperand.reg/.imm` to `Operand`
directly. `LOperand.arr` (memory) and the control-flow `LinstrR` constructors
are out of scope (returned as `none`) — see `README.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- Translate an `lprog` operand to an x86 operand. Memory (`arr`) is not
    modeled, so it falls back to a `reg` named `base ++ "[" ++ idx ++ "]"`
    (a placeholder; memory lowering is out of scope for the POC). -/
def lowerOperand : LOperand → Operand
  | .reg name => .reg name
  | .imm v => .imm v
  | .arr base idx => .reg (base ++ "[" ++ toString idx ++ "]")
  | .arrIdx base idx scale => .reg (base ++ "[" ++ idx ++ "*" ++ toString scale ++ "]")

/-- Lower a single two-address `LinstrR` to an x86 `Instr` at width `w`, when it
    is in the modeled scalar subset. `none` for unmodeled shapes (memory ops,
    control flow, the `LOAD`/`STORE`/`CALL` pseudo-ops). The destination is the
    sole `dsts` register; the source is the sole `srcs` operand (two-address:
    `dst := dst ⊕ src`). -/
def lowerLinstrR (w : Nat) : LinstrR → Option (Instr w)
  | .Lopn [.reg dst] opn [src] =>
      let s := lowerOperand src
      match opn with
      | "ADD" => some (.add dst s)
      | "SUB" => some (.sub dst s)
      | "MUL" => some (.mul dst s)
      | "AND" => some (.and_ dst s)
      | "OR"  => some (.or_ dst s)
      | "XOR" => some (.xor_ dst s)
      | "SHL" => some (.shl dst s)
      | "SHR" => some (.shr dst s)
      | "MOV" => some (.mov dst s)
      | _     => none
  | _ => none

/-- Lower a full `Linstr` (drops the position tag). -/
def lowerLinstr (w : Nat) (i : Linstr) : Option (Instr w) :=
  lowerLinstrR w i.li_i

/-- Lower an `lcmd` body, keeping only the modeled instructions, in order.
    (A faithful backend must reject — not silently drop — unmodeled
    instructions; the POC's `lowerLcmd` is the optimistic version used by the
    preservation theorems, which quantify over single modeled instructions.) -/
def lowerLcmd (w : Nat) (body : Lcmd) : List (Instr w) :=
  body.filterMap (lowerLinstr w)

end CatCrypt.Crypto.SecureCompilation.X86Backend
