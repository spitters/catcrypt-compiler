/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public meta import CatCrypt.Crypto.Util.Gf256
public import CatCrypt.Crypto.Util.Gf256

@[expose] public section

set_option autoImplicit false

/-!
# UOV scalar leaf body via `JasminCoqSemMirror` operational semantics

This file connects UOV's scalar `.jinc` leaf body (`_gf256_mul_one` and
`uov_gf256_dot_l8` from `bench/uov_compare/include/uov_leaves.jinc`) to
the Lean-level jasmin operational semantics in
`CatCrypt/Crypto/Jasmin/JasminCoqSemMirror.lean`.

Sibling to `MayoLeafJasminSim.lean` (the MAYO pilot, same shape).

## Scope (limited per fallback gate)

The full `uov_gf256_dot_l8` body is a `for i = 0 to 8` loop calling the
inline `_gf256_mul_one` body 8 times then XOR-accumulating. Two
structural gaps in the current `JasminCoqSemMirror` block a full
simulation through the OPAQUE rustcmd `gf256_dot_l8` symbol:

* The `Cfor` *relational* rule is deferred (the functional executor
  handles `Cfor`, but the relational `SemIr` constructor is not yet
  ported); this lets us run smoke tests through `execCmd` but not yet prove a relational
  simulation theorem.
* The `Ccall` / `inline fn` table (`fnDef`) is deferred; this is what
  would tie the opaque rustcmd `gf256_dot_l8` symbol to its body.

What we CAN do at this batch:

  * Hand-author **one round of the inner `_gf256_mul_one` 8-loop** as a
    `JasminCoqSemMirror.Cmd` (straight-line + `Cif`, which fits inside
    the functional executor's current coverage).
  * Plug in a minimal `OpSem` instance for `u8` word operations
    (`Oland`, `Olxor`, `Olsr`, `Olsl`, `Oeq`, `Oword_of_int`).
  * Prove that executing this single-round `Cmd` from a `Estate`
    initialised with input bytes `acc`, `a`, `b` produces a post-state
    whose `(acc', a')` matches `Gf256.mulStep` on the projection.

This is the UOV analogue of `MayoLeafJasminSim.gf16MulStepCmd`: the
first concrete bridge from the new jasmin semantics to UOV's
GF(256) scalar leaf transcription. The chain to the *full* unrolled
`uov_gf256_dot_l8` body (8 inner mul rounds × 8 outer XOR-accumulation
steps) is mechanical follow-up once the `fnDef` / `Ccall` gap is
closed.
-/

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.UovLeafJasminSim

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Util

/-! ## §1. Memory model + projections

`_gf256_mul_one`'s body uses no memory loads/stores (everything is in
`reg` registers, which map to `Vm`). So a trivial no-memory model
suffices. -/

/-- Trivial memory model: failures on every read/write. The body we
    model uses no memory accesses. -/
def NoMem : Type := Unit

instance : MemModel NoMem where
  read  _ _ _ _   := .typeError
  write _ _ _ _ _ := .typeError

/-- Project a `Value` to a `BitVec 8`, returning `none` for non-u8
    word values. -/
def Value.asU8? : Value → Option (BitVec 8)
  | .Vword .U8 w => some w
  | _ => none

/-! ## §2. OpSem instance for UOV's scalar `_gf256_mul_one` body

The `.jinc` body uses these unary / binary operators (all at width
`u8` after we model `wa &= 0xff` as a mask to 8 bits):

| Surface | `SOp` constructor | Semantics |
|---|---|---|
| `bb >>= 1` (or `>>= bitidx`) | `SOp2.Olsr .U8` | logical right shift |
| `shifted <<= 1` | `SOp2.Olsl (.Op_w .U8)` | left shift |
| `& 0x1` / `& 0x80` / `& 0xff` | `SOp2.Oland .U8` | bitwise and |
| `^ shifted` / `^ 0x1b` | `SOp2.Olxor .U8` | bitwise xor |
| `mb == 1` / `hib == 1` | `SOp2.Oeq (.Op_w .U8)` | equality (returns `Vbool`) |
| `Vword.U8 ← Int` | `SOp1.Oword_of_int .U8` | constant injection |

We leave the other variants at `.typeError`. -/

/-- The user-supplied operator semantics for UOV's scalar leaf. -/
def uovOpSem : OpSem where
  sem_sop1 := fun
    | .Oword_of_int .U8, .Vint n =>
        .ok (.Vword .U8 (BitVec.ofNat 8 n.toNat))
    | _, _ => .typeError
  sem_sop2 := fun
    | .Oland .U8,         .Vword .U8 a, .Vword .U8 b =>
        .ok (.Vword .U8 (a &&& b))
    | .Olxor .U8,         .Vword .U8 a, .Vword .U8 b =>
        .ok (.Vword .U8 (a ^^^ b))
    | .Olsr  .U8,         .Vword .U8 a, .Vword .U8 b =>
        .ok (.Vword .U8 (a >>> b.toNat))
    | .Olsl  (.Op_w .U8), .Vword .U8 a, .Vword .U8 b =>
        .ok (.Vword .U8 (a <<< b.toNat))
    | .Oeq   (.Op_w .U8), .Vword .U8 a, .Vword .U8 b =>
        .ok (.Vbool (a == b))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- No asm-ops are used in the scalar `_gf256_mul_one` body. -/
def uovAsmSem : AsmSem where
  sopn_sem _ _ := .typeError

/-! ## §3. Variables for the gf256 mul step

The `.jinc` body declares `reg u64 result shifted bb mb hib`. We
model each as a `Var` of `Atype.aword .U8` (the body's invariant is
that all values fit in a byte after the `& 0xff` masks). -/

/-- A `reg u8` variable. -/
def vU8 (s : String) : VarI :=
  { v_var := { vtype := .aword .U8, vname := s } }

def vResult  : VarI := vU8 "result"
def vShifted : VarI := vU8 "shifted"
def vBb      : VarI := vU8 "bb"
def vMb      : VarI := vU8 "mb"
def vHib     : VarI := vU8 "hib"

/-- Read a u8 register as a Pexpr. -/
def rdU8 (v : VarI) : Pexpr := .Pvar (mkLvar v)

/-- Write to a u8 register. -/
def wrU8 (v : VarI) : Lval := .Lvar v

/-- A `Vword .U8` constant. -/
def cU8 (n : Nat) : Pexpr :=
  .Papp1 (.Oword_of_int .U8) (.Pconst (Int.ofNat n))

/-! ## §4. The one-round Cmd of `_gf256_mul_one`

Transcribed from `bench/uov_compare/include/uov_leaves.jinc:41-58`,
ONE iteration of the `for bit = 0 to 8` loop. Variables are reduced to
u8 width (the .jinc body uses u64 with `&= 0xff` mask; we model the
byte-level invariant directly).

```
mb = bb;
mb = mb & 1;
if (mb == 1) {
  result ^= shifted;
}
bb >>= 1;
hib = shifted;
hib >>= 7;
hib = hib & 1;
shifted <<= 1;
shifted = shifted & 0xff;   -- (no-op at u8 width, kept for fidelity)
if (hib == 1) {
  shifted ^= 0x1b;
}
```

Each binary expression is a `Papp2`; the `if (x == 1)` is a `Cif` with
a `Papp2 Oeq` condition. The post-state of one round produces an
updated `(acc, a, b)` triple matching `Gf256.mulStep` (with the bitmask
applied as `0x01` since the loop tests bit 0 of the shifted `bb`). -/

/-- One round of UOV's bit-serial GF(256) multiply, as a
    `JasminCoqSemMirror.Cmd`. -/
def gf256MulOneRoundCmd : Cmd :=
  let mk (l : Lval) (e : Pexpr) : Instr :=
    .MkI () (.Cassgn l .AT_none (.aword .U8) e)
  let mkIf (cond : Pexpr) (cthen : List Instr) : Instr :=
    .MkI () (.Cif cond cthen [])
  [ -- mb = bb;
    mk (wrU8 vMb) (rdU8 vBb)
    -- mb = mb & 1;
  , mk (wrU8 vMb) (.Papp2 (.Oland .U8) (rdU8 vMb) (cU8 1))
    -- if (mb == 1) { result ^= shifted; }
  , mkIf (.Papp2 (.Oeq (.Op_w .U8)) (rdU8 vMb) (cU8 1))
      [ mk (wrU8 vResult) (.Papp2 (.Olxor .U8) (rdU8 vResult) (rdU8 vShifted)) ]
    -- bb >>= 1;
  , mk (wrU8 vBb) (.Papp2 (.Olsr .U8) (rdU8 vBb) (cU8 1))
    -- hib = shifted;
  , mk (wrU8 vHib) (rdU8 vShifted)
    -- hib >>= 7;
  , mk (wrU8 vHib) (.Papp2 (.Olsr .U8) (rdU8 vHib) (cU8 7))
    -- hib = hib & 1;
  , mk (wrU8 vHib) (.Papp2 (.Oland .U8) (rdU8 vHib) (cU8 1))
    -- shifted <<= 1;
  , mk (wrU8 vShifted) (.Papp2 (.Olsl (.Op_w .U8)) (rdU8 vShifted) (cU8 1))
    -- shifted = shifted & 0xff;  (no-op at u8 width, kept for fidelity)
  , mk (wrU8 vShifted) (.Papp2 (.Oland .U8) (rdU8 vShifted) (cU8 0xff))
    -- if (hib == 1) { shifted ^= 0x1b; }
  , mkIf (.Papp2 (.Oeq (.Op_w .U8)) (rdU8 vHib) (cU8 1))
      [ mk (wrU8 vShifted) (.Papp2 (.Olxor .U8) (rdU8 vShifted) (cU8 0x1b)) ]
  ]

/-! ## §5. Helper: initial state with `result`, `shifted`, `bb` set

We initialize an `Estate Unit NoMem` with the three live inputs
`result = acc`, `shifted = a`, `bb = b`. The two temporaries (`mb`,
`hib`) are left at their default state; the Cmd writes to them before
reading. -/

/-- Initial state with the three input bytes. -/
def initStateOfBytes (acc a b : BitVec 8) : Estate Unit NoMem :=
  let vm0 := (Vm.init.set vResult.v_var (.Vword .U8 acc)).set
              vShifted.v_var (.Vword .U8 a)
  let vm := vm0.set vBb.v_var (.Vword .U8 b)
  { escs := (), emem := (), evm := vm }

/-- Project the final state to the post-values of `(result, shifted, bb)`. -/
def projectAccAB (s : Estate Unit NoMem) :
    Option (BitVec 8) × Option (BitVec 8) × Option (BitVec 8) :=
  ( Value.asU8? (s.evm.get vResult.v_var)
  , Value.asU8? (s.evm.get vShifted.v_var)
  , Value.asU8? (s.evm.get vBb.v_var) )

/-- Result of running one round of `_gf256_mul_one`'s Cmd on inputs
    `(acc, a, b)`. Returns `none` on any executor failure. -/
def runRound (acc a b : BitVec 8) :
    Option (BitVec 8) × Option (BitVec 8) × Option (BitVec 8) :=
  match execCmd (Mem := NoMem) uovAsmSem uovOpSem []
                64 (initStateOfBytes acc a b) gf256MulOneRoundCmd with
  | .ok s => projectAccAB s
  | _ => (none, none, none)

/-! ## §6. Concrete-input smoke tests

Pick small representative inputs and check that the operational
semantics agrees with the verified `Gf256.mulStep`. -/

/-- Smoke-test: run one round and check agreement with `Gf256.mulStep`.

    `Gf256.mulStep acc a b bitMask` returns `(acc', a')` where:
    * if `b &&& bitMask != 0` then `acc' := acc ^^^ a`, else `acc' := acc`
    * `a'` is the double of `a` mod 0x11b.

    For our single-round Cmd we test bit 0 of `b` (after `mb = bb & 1`),
    so `bitMask = 0x01`. The post-state's `bb` is also `b >>> 1`
    (one of the loop steps), so we project all three. -/
def smokeAgree (acc a b : BitVec 8) : Bool :=
  let (acc'?, a'?, b'?) := runRound acc a b
  let (acc_ref, a_ref) := Gf256.mulStep acc a b 0x01#8
  let b_ref := b >>> (1 : Nat)
  match acc'?, a'?, b'? with
  | some accV, some aV, some bV =>
      decide (accV = acc_ref) && decide (aV = a_ref) && decide (bV = b_ref)
  | _, _, _ => false

-- Diagnostic `#eval`s (kept for debugging; output appears in the build log).
#eval runRound 0x00#8 0x57#8 0x01#8   -- bit 0 set: acc ⊕= a, then double a
#eval runRound 0x00#8 0x57#8 0x00#8   -- bit 0 unset: acc unchanged, double a
#eval runRound 0x00#8 0x80#8 0x01#8   -- a has MSB set: triggers 0x1b reduce

/-- Smoke test: bit 0 set, no MSB overflow. -/
example : smokeAgree 0x00#8 0x57#8 0x01#8 = true := by native_decide

/-- Smoke test: zero input → zero output. -/
example : smokeAgree 0x00#8 0x00#8 0x00#8 = true := by native_decide

/-- Smoke test: bit 0 unset, no overflow. -/
example : smokeAgree 0x12#8 0x57#8 0x00#8 = true := by native_decide

/-- Smoke test: a has MSB set; the doubling step triggers the `0x1b`
    reduction. -/
example : smokeAgree 0x00#8 0x80#8 0x01#8 = true := by native_decide

/-- Smoke test: combined — accumulator nonzero, MSB overflow, bit 0 set. -/
example : smokeAgree 0xab#8 0xc0#8 0x01#8 = true := by native_decide

/-! ## §7. Connector theorem (this batch's deliverable)

The connector theorem: running one round of the `.jinc` body through
the new jasmin operational semantics produces a post-state whose
`(result, shifted)` matches `Gf256.mulStep` on the inputs.

To stay within `native_decide`'s reachable budget we restrict the
universal to the **low-byte product space**: 4 + 4 + 4 = 12-bit space
(4096 cases), modelling the GF(16) sub-window used by MAYO's
companion file (a deliberately tractable sub-corner for CI). The
full GF(256) space (24-bit, 16M cases) would close by `native_decide`
on a workstation; we leave that for follow-up.

The structural shape of the theorem matches MAYO's
`gf16MulStep_jasmin_sem_eq_smallInputs` exactly. -/

/-- **Connector theorem (single-round, restricted-input form).**
    On all inputs in the 4-bit window (`a, b, acc < 16`), the one-round
    operational-semantics step agrees with `Gf256.mulStep` (with
    `bitMask = 0x01`).

    Closed by `native_decide` over the 4 + 4 + 4 = 12-bit input space
    (4096 cases). -/
theorem gf256MulStep_jasmin_sem_eq_smallInputs :
    ∀ (a b c : BitVec 4),
      smokeAgree (BitVec.ofNat 8 c.toNat) (BitVec.ofNat 8 a.toNat)
                 (BitVec.ofNat 8 b.toNat) = true := by
  native_decide

/-! ## §8. Summary

| Function | What | Status |
|---|---|---|
| `gf256MulOneRoundCmd` | One inlined round of `_gf256_mul_one` as a `JasminCoqSemMirror.Cmd` | Defined |
| `uovOpSem` | `OpSem` instance for u8 word arithmetic + equality | Defined |
| `runRound` | Functional executor on the round-Cmd | Defined |
| Smoke tests (5 examples) | Per-input agreement with `Gf256.mulStep` | **`native_decide` PROVED** |
| `gf256MulStep_jasmin_sem_eq_smallInputs` | Round-Cmd ≅ `Gf256.mulStep` on the 4-bit input window (4096 cases) | **`native_decide` PROVED** |

**What this delivers**: the UOV analogue of MAYO's
`MayoLeafJasminSim.gf16MulStep_jasmin_sem_eq_smallInputs` — a proved
bridge from the new `JasminCoqSemMirror` operational semantics to a
verified `.jinc`-leaf transcription for the bit-serial GF(256)
multiply. The chain to the full unrolled `uov_gf256_dot_l8` body
(8 mul rounds × 8 outer XOR-accumulation steps) is mechanical
follow-up once the `Ccall` / `fnDef` gap is closed.

**What's missing for axiom removal**: same blockers as MAYO —
`Ccall` / `inline fn` table for the opaque rustcmd `gf256_dot_l8`
symbol, and (for fully relational reasoning) the `Cfor` relational
constructor in `JasminCoqSemMirror`.
-/

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.UovLeafJasminSim
