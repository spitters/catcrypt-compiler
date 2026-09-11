/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel
public import Mathlib.Data.BitVec
public import Mathlib.Tactic.NormNum

/-!
# Sail refinement for RV64 branch comparisons (`BCmp` vs Sail `BTYPE`)

The RV64 backend emits branches only as **structural, public-trip-count loops**
(`runBoundedLoopR`; the one emitted branch is the `BNE ctr, x0` back-edge), so there is no
data-dependent branch-condition *value* in the operational model — `BCmp`'s meaning lived only
in its `funct3` docstrings (`RiscvModel.BCmp`). This file makes that meaning precise and proves
it equals the `taken` computation of the Sail `execute_BTYPE` clause, as held in-file.

We paste only the **`taken` computation** of `execute_BTYPE` (`LeanRV64D/InstsEnd.lean:71722`)
as the pure `btypeTaken`; the PC/`jump_to` control-flow tail is not part of the comparison
semantics. That paste is an in-file excerpt of the sail-riscv-lean generated output
(commit `9eba3f07`; upstream not vendored, and the transcription is not machine-checked) —
provenance/discipline as in the sibling refinement files.

## Status

Standalone: nothing in this repo imports this file or consumes `bcmp_taken_eq` —
it is not wired into `SailRiscvDecoder.lean`'s `roundtrip_bcc`/`riscvDecodeB` or
into any executable-semantics proof. It fixes `BCmp`'s meaning against the
transcribed Sail `BTYPE` clause on its own, ahead of being consumed elsewhere.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvBranchRef

/-! ## Vendored Sail comparison ops (`Prelude.lean:370–399`) and the `BTYPE` `taken` -/

def zopz0zI_s (x y : BitVec 64) : Bool := decide (x.toInt < y.toInt)
def zopz0zKzJ_s (x y : BitVec 64) : Bool := decide (x.toInt ≥ y.toInt)
def zopz0zI_u (x y : BitVec 64) : Bool := decide ((x.toNat : Int) < (y.toNat : Int))
def zopz0zKzJ_u (x y : BitVec 64) : Bool := decide ((x.toNat : Int) ≥ (y.toNat : Int))

inductive bop where | BEQ | BNE | BLT | BGE | BLTU | BGEU

/-- The `taken` value the Sail `execute_BTYPE` clause computes (`InstsEnd.lean:71722`). -/
def btypeTaken : bop → BitVec 64 → BitVec 64 → Bool
  | .BEQ, a, b => a == b
  | .BNE, a, b => a != b
  | .BLT, a, b => zopz0zI_s a b
  | .BGE, a, b => zopz0zKzJ_s a b
  | .BLTU, a, b => zopz0zI_u a b
  | .BGEU, a, b => zopz0zKzJ_u a b

/-! ## Our `BCmp` denotation and the equivalence -/

/-- The natural denotation of `RiscvModel.BCmp` (the `funct3` docstring spec): `beq/bne` via
    equality, `blt/bge` signed, `bltu/bgeu` unsigned. This is the meaning the backend's
    branch alphabet intends. -/
def bcmpTaken : BCmp → BitVec 64 → BitVec 64 → Bool
  | .beq, a, b => a == b
  | .bne, a, b => a != b
  | .blt, a, b => a.slt b
  | .bge, a, b => !(a.slt b)
  | .bltu, a, b => a.ult b
  | .bgeu, a, b => !(a.ult b)

/-- `BCmp → bop` (matching `funct3`). -/
def toBop : BCmp → bop
  | .beq => .BEQ | .bne => .BNE | .blt => .BLT | .bge => .BGE | .bltu => .BLTU | .bgeu => .BGEU

/-- Each `BCmp`'s denotation equals Sail's `BTYPE` `taken` for the corresponding `bop`. -/
theorem bcmp_taken_eq (c : BCmp) (a b : BitVec 64) :
    bcmpTaken c a b = btypeTaken (toBop c) a b := by
  cases c <;>
    simp only [bcmpTaken, btypeTaken, toBop, zopz0zI_s, zopz0zKzJ_s, zopz0zI_u, zopz0zKzJ_u,
      BitVec.slt, BitVec.ult, ← decide_not, decide_eq_decide] <;>
    omega

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvBranchRef
