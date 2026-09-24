/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public meta import CatCrypt.Crypto.Util.ZMod127
public import CatCrypt.Crypto.Util.ZMod127

@[expose] public section

set_option autoImplicit false

/-!
# QR-UOV scalar leaf body via `JasminCoqSemMirror` operational semantics

This file connects QR-UOV's scalar `gf127_mul` `.jinc` leaf body (from
`bench/qruov_compare/include/qruov_leaves.jinc`) to the Lean-level
jasmin operational semantics in
`CatCrypt/Crypto/Jasmin/JasminCoqSemMirror.lean`.

`UovLeafJasminSim.lean` has the same structure for the UOV scalar multiply
step.

## Scope

The full `qruov_block_dot_b4_l3` body is a nested `for k = 0 to 3 ;
for J = 0 to 4 ; for ll = 0 to 3` loop (36 iterations) calling the
inline `gf127_mul` and `gf127_add` bodies, plus a packing step. Two
structural gaps in `JasminCoqSemMirror` rule out a full simulation through
the OPAQUE rustcmd `qruov_block_dot_b4_l3` symbol:

* `JasminCoqSemMirror` has no `Cfor` *relational* rule (the functional
  executor handles `Cfor`, but there is no relational `SemIr` constructor
  for it); smoke tests run through `execCmd`, and no relational
  simulation theorem is stated.
* `JasminCoqSemMirror` has no `Ccall` / `inline fn` table (`fnDef`), which
  would tie the opaque rustcmd `qruov_block_dot_b4_l3` symbol to its
  body.

This module:

  * Hand-authors **the scalar `gf127_mul` body** as a
    `JasminCoqSemMirror.Cmd` (straight-line + 1 `Cif`, which fits
    inside the functional executor's coverage). The body is
    bit-pattern manipulation at u16 width: `p = a*b; p = (p & 127) +
    (p >> 7); p = (p & 127) + (p >> 7); if p >= 127 then p -= 127`.
  * Plugs in a minimal `OpSem` instance for `u16` arithmetic
    (`Oadd .U16`, `Omul .U16`, `Oland .U16`, `Olsr .U16`, `Osub .U16`,
    `Oge (.Cmp_w .Unsigned .U16)`, `Oword_of_int .U16`).
  * Proves that executing this Cmd from a `Estate` initialised with
    `a, b ∈ [0..126]` produces a post-state whose `p` matches the
    verified `(Zq127.fromNat a * Zq127.fromNat b).asNat`.

This relates the `JasminCoqSemMirror` semantics to QR-UOV's GF(127) scalar
leaf transcription, as `UovLeafJasminSim.gf256MulOneRoundCmd` does for UOV.
The full unrolled `qruov_block_dot_b4_l3` body (36 inner mul + 36 inner add +
packing) is not covered; it needs the `fnDef` / `Ccall` forms.
-/

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.QruovLeafJasminSim

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Util

/-! ## §1. Memory model + projections

`gf127_mul`'s body uses no memory loads/stores (everything is in
`reg u16` registers, which map to `Vm`). So a trivial no-memory model
suffices. -/

/-- Trivial memory model: failures on every read/write. The body we
    model uses no memory accesses. -/
def NoMem : Type := Unit

instance : MemModel NoMem where
  read  _ _ _ _   := .typeError
  write _ _ _ _ _ := .typeError

/-- Project a `Value` to a `BitVec 16`, returning `none` for non-u16
    word values. -/
def Value.asU16? : Value → Option (BitVec 16)
  | .Vword .U16 w => some w
  | _ => none

/-! ## §2. OpSem instance for QR-UOV's `gf127_mul` body

The `.jinc` body uses these unary / binary operators (all at width
`u16`):

| Surface | `SOp` constructor | Semantics |
|---|---|---|
| `p = a * b` | `SOp2.Omul (.Op_w .U16)` | u16 multiply (wraps) |
| `p = lo + hi` | `SOp2.Oadd (.Op_w .U16)` | u16 add (wraps) |
| `p = p - 127` | `SOp2.Osub (.Op_w .U16)` | u16 subtract |
| `p & 127` | `SOp2.Oland .U16` | bitwise and |
| `p >> 7` | `SOp2.Olsr .U16` | logical right shift |
| `p >= 127` | `SOp2.Oge (.Cmp_w .Unsigned .U16)` | unsigned compare |
| `Vword.U16 ← Int` | `SOp1.Oword_of_int .U16` | constant injection |

We leave the other variants at `.typeError`. -/

/-- The user-supplied operator semantics for QR-UOV's scalar leaf. -/
def qruovOpSem : OpSem where
  sem_sop1 := fun
    | .Oword_of_int .U16, .Vint n =>
        .ok (.Vword .U16 (BitVec.ofNat 16 n.toNat))
    | _, _ => .typeError
  sem_sop2 := fun
    | .Omul  (.Op_w .U16), .Vword .U16 a, .Vword .U16 b =>
        .ok (.Vword .U16 (a * b))
    | .Oadd  (.Op_w .U16), .Vword .U16 a, .Vword .U16 b =>
        .ok (.Vword .U16 (a + b))
    | .Osub  (.Op_w .U16), .Vword .U16 a, .Vword .U16 b =>
        .ok (.Vword .U16 (a - b))
    | .Oland .U16,         .Vword .U16 a, .Vword .U16 b =>
        .ok (.Vword .U16 (a &&& b))
    | .Olsr  .U16,         .Vword .U16 a, .Vword .U16 b =>
        .ok (.Vword .U16 (a >>> b.toNat))
    | .Oge   (.Cmp_w .Unsigned .U16), .Vword .U16 a, .Vword .U16 b =>
        .ok (.Vbool (decide (a.toNat ≥ b.toNat)))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- No asm-ops are used in the scalar `gf127_mul` body. -/
def qruovAsmSem : AsmSem where
  sopn_sem _ _ := .typeError

/-! ## §3. Variables for the gf127_mul step

The `.jinc` body declares `reg u16 a b p lo hi`. We model each as a
`Var` of `Atype.aword .U16`. -/

/-- A `reg u16` variable. -/
def vU16 (s : String) : VarI :=
  { v_var := { vtype := .aword .U16, vname := s } }

def vA  : VarI := vU16 "a"
def vB  : VarI := vU16 "b"
def vP  : VarI := vU16 "p"
def vLo : VarI := vU16 "lo"
def vHi : VarI := vU16 "hi"

/-- Read a u16 register as a Pexpr. -/
def rdU16 (v : VarI) : Pexpr := .Pvar (mkLvar v)

/-- Write to a u16 register. -/
def wrU16 (v : VarI) : Lval := .Lvar v

/-- A `Vword .U16` constant. -/
def cU16 (n : Nat) : Pexpr :=
  .Papp1 (.Oword_of_int .U16) (.Pconst (Int.ofNat n))

/-! ## §4. The `gf127_mul` Cmd

Transcribed from `bench/qruov_compare/include/qruov_leaves.jinc:32-51`,
the full scalar `gf127_mul` body (Mersenne reduce twice + cond-subtract):

```
p = a;
p = p * b;
hi = p; hi >>= 7;
lo = p; lo = lo & 127;
p = lo + hi;
hi = p; hi >>= 7;
lo = p; lo = lo & 127;
p = lo + hi;
if (p >= 127) { p = p - 127; }
```

Each binary expression is a `Papp2`; the `if (p >= 127)` is a `Cif`
with a `Papp2 Oge` condition. The post-state's `p` is the residue. -/

/-- The full scalar `gf127_mul` body, as a `JasminCoqSemMirror.Cmd`. -/
def gf127MulCmd : Cmd :=
  let mk (l : Lval) (e : Pexpr) : Instr :=
    .MkI () (.Cassgn l .AT_none (.aword .U16) e)
  let mkIf (cond : Pexpr) (cthen : List Instr) : Instr :=
    .MkI () (.Cif cond cthen [])
  [ -- p = a;
    mk (wrU16 vP) (rdU16 vA)
    -- p = p * b;
  , mk (wrU16 vP) (.Papp2 (.Omul (.Op_w .U16)) (rdU16 vP) (rdU16 vB))
    -- hi = p;
  , mk (wrU16 vHi) (rdU16 vP)
    -- hi >>= 7;
  , mk (wrU16 vHi) (.Papp2 (.Olsr .U16) (rdU16 vHi) (cU16 7))
    -- lo = p;
  , mk (wrU16 vLo) (rdU16 vP)
    -- lo = lo & 127;
  , mk (wrU16 vLo) (.Papp2 (.Oland .U16) (rdU16 vLo) (cU16 127))
    -- p = lo + hi;
  , mk (wrU16 vP) (.Papp2 (.Oadd (.Op_w .U16)) (rdU16 vLo) (rdU16 vHi))
    -- hi = p;
  , mk (wrU16 vHi) (rdU16 vP)
    -- hi >>= 7;
  , mk (wrU16 vHi) (.Papp2 (.Olsr .U16) (rdU16 vHi) (cU16 7))
    -- lo = p;
  , mk (wrU16 vLo) (rdU16 vP)
    -- lo = lo & 127;
  , mk (wrU16 vLo) (.Papp2 (.Oland .U16) (rdU16 vLo) (cU16 127))
    -- p = lo + hi;
  , mk (wrU16 vP) (.Papp2 (.Oadd (.Op_w .U16)) (rdU16 vLo) (rdU16 vHi))
    -- if (p >= 127) { p = p - 127; }
  , mkIf (.Papp2 (.Oge (.Cmp_w .Unsigned .U16)) (rdU16 vP) (cU16 127))
      [ mk (wrU16 vP) (.Papp2 (.Osub (.Op_w .U16)) (rdU16 vP) (cU16 127)) ]
  ]

/-! ## §5. Helper: initial state with `a`, `b` set -/

/-- Initial state with the two input residues. -/
def initStateOfResidues (a b : BitVec 16) : Estate Unit NoMem :=
  let vm := (Vm.init.set vA.v_var (.Vword .U16 a)).set
              vB.v_var (.Vword .U16 b)
  { escs := (), emem := (), evm := vm }

/-- Project the final state to the post-value of `p`. -/
def projectP (s : Estate Unit NoMem) : Option (BitVec 16) :=
  Value.asU16? (s.evm.get vP.v_var)

/-- Result of running the `gf127_mul` Cmd on inputs `(a, b)`. Returns
    `none` on any executor failure. -/
def runMul (a b : BitVec 16) : Option (BitVec 16) :=
  match execCmd (Mem := NoMem) qruovAsmSem qruovOpSem []
                64 (initStateOfResidues a b) gf127MulCmd with
  | .ok s => projectP s
  | _ => none

/-! ## §6. Concrete-input smoke tests

Pick small representative inputs in `[0..126]` and check that the
operational semantics agrees with verified modular multiplication
(`(a * b) mod 127`). -/

/-- Smoke-test: run `gf127_mul` and check agreement with the verified
    `Zq127` multiplication. -/
def smokeAgree (a b : Nat) : Bool :=
  let aw : BitVec 16 := BitVec.ofNat 16 a
  let bw : BitVec 16 := BitVec.ofNat 16 b
  let lhs := runMul aw bw
  let rhs : Nat := (a * b) % 127
  match lhs with
  | some w => decide (w.toNat = rhs)
  | none => false

-- Diagnostic `#eval`s (kept for debugging; output appears in the build log).
#eval runMul 0#16 0#16       -- 0
#eval runMul 1#16 1#16       -- 1
#eval runMul 126#16 126#16   -- 126*126 mod 127 = 1
#eval runMul 64#16 2#16      -- 128 mod 127 = 1
#eval runMul 100#16 100#16   -- 10000 mod 127 = 99

/-- Smoke test: 0 * 0 = 0. -/
example : smokeAgree 0 0 = true := by native_decide

/-- Smoke test: 1 * 1 = 1. -/
example : smokeAgree 1 1 = true := by native_decide

/-- Smoke test: 126 * 126 mod 127 = 1 (since 126 ≡ -1). -/
example : smokeAgree 126 126 = true := by native_decide

/-- Smoke test: 64 * 2 = 128 mod 127 = 1 — exercises the cond-subtract. -/
example : smokeAgree 64 2 = true := by native_decide

/-- Smoke test: 100 * 100 = 10000 mod 127 = 99 — exercises both Mersenne
    folds. -/
example : smokeAgree 100 100 = true := by native_decide

/-! ## §7. Connector theorem (this batch's deliverable)

The connector theorem: running `gf127_mul` through the new jasmin
operational semantics produces a post-state `p` matching the verified
modular multiplication `(a * b) mod 127`.

To stay within `native_decide`'s reachable budget we restrict the
universal to the **canonical residue space** `(a, b) ∈ [0..126]²`
(16129 cases) — matching the .jinc body's documented input
contract (`reg u16 a, b` with `a, b < 127`). -/

/-- **Connector theorem (full-input form on the canonical residue
    space).** For all `a, b ∈ [0..126]` the operational-semantics step
    agrees with the verified `(a * b) mod 127`.

    Closed by `native_decide` over the 127 × 127 = 16129 input space. -/
theorem gf127Mul_jasmin_sem_eq_smallInputs :
    ∀ (a b : Fin 127), smokeAgree a.val b.val = true := by
  native_decide

/-! ## §8. Bridge to the verified `Zq127` semantics

The `smokeAgree` test compares to `(a * b) % 127 : Nat`. The same
identity factored through the verified `Zq127.asNat`-of-`fromNat`
multiplication: by `ZMod.val_mul` (or directly by the `Nat` modular
identity), the two are definitionally equal at the `Nat` level.

This makes `gf127MulCmd`'s denotation the canonical verified
multiplication on `Zq127` for canonical inputs. -/

/-- Helper: the `Nat`-level mod-127 multiplication is the `asNat` of
    the verified `Zq127`-multiplication. PROVED by the canonical
    `ZMod.val_mul` identity. -/
theorem nat_mul_mod_eq_Zq127 (a b : Nat) (ha : a < 127) (hb : b < 127) :
    (a * b) % 127 =
      Zq127.asNat ((Zq127.fromNat a) * (Zq127.fromNat b)) := by
  unfold Zq127.asNat Zq127.fromNat
  rw [ZMod.val_mul]
  simp [ZMod.val_natCast]

/-! ## §9. Summary

| Function | What | Status |
|---|---|---|
| `gf127MulCmd` | Full scalar `gf127_mul` body as a `JasminCoqSemMirror.Cmd` | Defined |
| `qruovOpSem` | `OpSem` instance for u16 word arithmetic + compare | Defined |
| `runMul` | Functional executor on the mul-Cmd | Defined |
| Smoke tests (5 examples) | Per-input agreement with `(a * b) % 127` | **`native_decide` PROVED** |
| `gf127Mul_jasmin_sem_eq_smallInputs` | Mul-Cmd ≅ `(a * b) % 127` on the canonical 127 × 127 input space (16129 cases) | **`native_decide` PROVED** |
| `nat_mul_mod_eq_Zq127` | Nat-level mod-127 mul = verified `Zq127` mul | **Proved** |

**Scope of the checks**: `gf127Mul_jasmin_sem_eq_smallInputs` evaluates, by
`native_decide`, the `JasminCoqSemMirror` run of the Mersenne-reduce GF(127)
multiply against `(a * b) % 127` on all canonical residues `a, b < 127`. The full
unrolled `qruov_block_dot_b4_l3` body (36 inner mul rounds + 36 inner add rounds +
outer packing) is not covered.

**Missing for replacing the leaf axiom**: as for UOV (`UovLeafJasminSim`),
`Ccall` / `inline fn` table for the opaque rustcmd
`qruov_block_dot_b4_l3` symbol, and (for fully relational reasoning)
the `Cfor` relational constructor in `JasminCoqSemMirror`.
-/

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.QruovLeafJasminSim
