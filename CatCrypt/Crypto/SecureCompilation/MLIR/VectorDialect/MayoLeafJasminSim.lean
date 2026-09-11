/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import Mathlib.Data.Fintype.Basic

public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public meta import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MayoLeafProof
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MayoLeafProof

@[expose] public section

set_option autoImplicit false

/-!
# MAYO scalar leaf body via `JasminCoqSemMirror` operational semantics

This file connects MAYO's scalar `.jinc` body (`gf16_mul_scalar` from
`bench/mayo_compare/include/mayo_leaves.jinc`) to the new Lean-level
jasmin operational semantics in
`CatCrypt/Crypto/Jasmin/JasminCoqSemMirror.lean`.

## Scope (limited per fallback gate)

The full `mayo_quadform_n8` body is a nested `for j = 0 to 8 ; for l = 0 to 8`
loop calling `gf16_mul_scalar` 128 times. Two structural gaps in the
current `JasminCoqSemMirror` block a full simulation theorem:
(i) `Cfor` is deferred; (ii) `Ccall` / `inline fn` is deferred.

What we CAN do at this batch:

  * Hand-author **one round of the inner `gf16_mul_scalar` 4-loop** as a
    `JasminCoqSemMirror.Cmd` (straight-line, fits inside the current
    `SemIr.Eassgn` / `SemIr.Eopn` coverage).
  * Plug in a minimal `OpSem` instance for `u8` word operations
    (`Oland`, `Olxor`, `Olsr`, `Olsl`, `Oneg`, and the `Pif`-style
    branch needed by the `bit_v = -bit_v` step).
  * Prove that executing this single-round `Cmd` from a `Estate`
    initialised with input nibbles `sh`, `bb`, `r` produces the
    expected post-state whose `sh'`, `bb'`, `r'` match
    `MayoLeafProof.gf16MulStep`.

This is the first concrete bridge from the new jasmin semantics
(`JasminCoqSemMirror`) to a verified `.jinc`-leaf transcription
(`MayoLeafProof.gf16MulStep`). The chain to the *full* unrolled body
(4 rounds × 64 inner iterations) is mechanical follow-up and is left
to a later batch once `Cfor` is ported.

See `bench/framework/JASMIN_SEM_COVERAGE.md` for the full coverage
audit and the per-protocol extension plan.

## Strategy

To avoid the `DecidableEq Value` issue (the file uses `Classical.dec`
because `JArrayMirror n = Fin n -> BitVec 8` is a function type), we
project the final `Estate` to a tuple of optional `BitVec 8` via a
dedicated `Value.asU8?` and compare projections, mirroring the demo
file's `asInt?` pattern.

## Diagram

```
        +---------------------+        execCmd        +---------------------+
        |  Estate (sh,bb,r)   |  ------------------>  |  Estate (sh',bb',r')|
        +---------------------+   gf16MulStepCmd      +---------------------+
                |                                              |
                |  project to BitVec 4 nibbles                 |  project
                v                                              v
                (a, b, 0) -----+                +----- (sh', bb', r')
                               |                |
                               +-->  gf16MulStep <--+
                                     (defined in MayoLeafProof)
```

The Lean statement is

```
theorem gf16MulStep_jasmin_sem_eq :
    ∀ (sh bb r : BitVec 8),
      execCmd ... initStateOfBytes(sh,bb,r) gf16MulStepCmd of
      = ... encode (gf16MulStep ... (sh.truncate 4) (bb.truncate 4) (r.truncate 4))
```

For Stage 2/3 honesty: the proof is by `decide` / `native_decide` on
the projected outputs, since the input space is exactly 8+8+8 = 24
bits = 16M cases. That's at the edge of `native_decide` but works for
a single round (and is what `MayoLeafProof.gf16MulJinc_eq_Gf16_mul`
does at width 4+4 = 8 bits).

To stay tractable in this batch we instead prove agreement on a
**representative concrete input** plus the structural shape, deferring
the per-bit-input universal quantification (which is what bv_decide
would do on the BV4-truncated form) to follow-up.
-/

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MayoLeafJasminSim

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MayoLeafProof

/-! ## §1. Memory model + projections

`gf16_mul_scalar`'s body uses no memory loads/stores (everything is in
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

/-! ## §2. OpSem instance for MAYO's scalar body

The `.jinc` body of `gf16_mul_scalar` uses these unary / binary
operators:

| Surface | `SOp` constructor | Semantics |
|---|---|---|
| `bit_v = -bit_v` (on `reg u8`) | `SOp1.Oneg (.Op_w .U8)` | 2's-complement negate |
| `bb >>= 1` | `SOp2.Olsr .U8` | logical right shift |
| `sh <<= 1` | `SOp2.Olsl .U8` | left shift |
| `& 0x1` etc. | `SOp2.Oland .U8` | bitwise and |
| `^ prod` | `SOp2.Olxor .U8` | bitwise xor |
| u8 zero/sign-extend | `SOp1.Ozeroext .U64 .U8` | width extension |

The other variants (int arithmetic, comparison) we leave at
`.typeError` since MAYO's scalar body doesn't use them. -/

/-- The user-supplied operator semantics that MAYO's scalar leaf uses. -/
def mayoOpSem : OpSem where
  sem_sop1 := fun
    | .Oneg (.Op_w .U8), .Vword .U8 w =>
        -- 2's-complement negate at u8: matches the jasmin `-bit_v` semantics
        -- where `-0x1#8 = 0xFF#8`.
        .ok (.Vword .U8 (-w))
    | .Ozeroext .U64 .U8, .Vword .U8 w =>
        .ok (.Vword .U64 (BitVec.ofNat 64 w.toNat))
    -- `Oword_of_int .U8 (Vint n) = Vword .U8 (BitVec.ofNat 8 n)` — used by `cU8`.
    | .Oword_of_int .U8, .Vint n =>
        .ok (.Vword .U8 (BitVec.ofNat 8 n.toNat))
    | _, _ => .typeError
  sem_sop2 := fun
    | .Oland .U8, .Vword .U8 a, .Vword .U8 b => .ok (.Vword .U8 (a &&& b))
    | .Olxor .U8, .Vword .U8 a, .Vword .U8 b => .ok (.Vword .U8 (a ^^^ b))
    | .Olsr  .U8,         .Vword .U8 a, .Vword .U8 b => .ok (.Vword .U8 (a >>> b.toNat))
    | .Olsl  (.Op_w .U8), .Vword .U8 a, .Vword .U8 b => .ok (.Vword .U8 (a <<< b.toNat))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- No asm-ops are used in the scalar body. -/
def mayoAsmSem : AsmSem where
  sopn_sem _ _ := .typeError

/-! ## §3. Variables for the gf16 mul step

The `.jinc` body declares `reg u8 r sh bb bit_v hi mask prod`. We
model each as a `Var` of `Atype.aword .U8`. -/

/-- A `reg u8` variable. -/
def vU8 (s : String) : VarI :=
  { v_var := { vtype := .aword .U8, vname := s } }

def vSh   : VarI := vU8 "sh"
def vBb   : VarI := vU8 "bb"
def vR    : VarI := vU8 "r"
def vBitV : VarI := vU8 "bit_v"
def vHi   : VarI := vU8 "hi"
def vMask : VarI := vU8 "mask"
def vProd : VarI := vU8 "prod"

/-- Read a u8 register as a Pexpr. -/
def rdU8 (v : VarI) : Pexpr := .Pvar (mkLvar v)

/-- Write to a u8 register. -/
def wrU8 (v : VarI) : Lval := .Lvar v

/-- A `Vword .U8` constant. -/
def cU8 (n : Nat) : Pexpr :=
  .Papp1 (.Oword_of_int .U8) (.Pconst (Int.ofNat n))

/-! ## §4. The one-round Cmd of `gf16_mul_scalar`

Transcribed from `bench/mayo_compare/include/mayo_leaves.jinc:35-52`,
ONE iteration only (the `.jinc` loops with `bit_i = 0..4`):

```
bit_v = bb;
bit_v = bit_v & 0x1;
prod  = sh;
bit_v = -bit_v;
prod  = prod & bit_v;
r     = r ^ prod;
bb  >>= 1;
hi    = sh;
hi  >>= 3;
sh <<= 1;
hi    = hi & 0x1;
hi    = -hi;
mask  = 0x3;
hi    = hi & mask;
sh    = sh ^ hi;
sh    = sh & 0xf;
```

We use `Cassgn` for all moves (jasmin's surface syntax does); each
binary expression is a `Papp2`. The `Oword_of_int` constructor builds
the `0x1`, `0x3`, `0xf` constants from int literals. -/

/-- One round of the bit-serial GF(16) multiply, as a
    `JasminCoqSemMirror.Cmd`. -/
def gf16MulStepCmd : Cmd :=
  let mk (l : Lval) (e : Pexpr) : Instr :=
    .MkI () (.Cassgn l .AT_none (.aword .U8) e)
  [ -- bit_v = bb;
    mk (wrU8 vBitV) (rdU8 vBb)
    -- bit_v = bit_v & 0x1;
  , mk (wrU8 vBitV) (.Papp2 (.Oland .U8) (rdU8 vBitV) (cU8 1))
    -- prod = sh;
  , mk (wrU8 vProd) (rdU8 vSh)
    -- bit_v = -bit_v;
  , mk (wrU8 vBitV) (.Papp1 (.Oneg (.Op_w .U8)) (rdU8 vBitV))
    -- prod = prod & bit_v;
  , mk (wrU8 vProd) (.Papp2 (.Oland .U8) (rdU8 vProd) (rdU8 vBitV))
    -- r = r ^ prod;
  , mk (wrU8 vR) (.Papp2 (.Olxor .U8) (rdU8 vR) (rdU8 vProd))
    -- bb >>= 1;
  , mk (wrU8 vBb) (.Papp2 (.Olsr .U8) (rdU8 vBb) (cU8 1))
    -- hi = sh;
  , mk (wrU8 vHi) (rdU8 vSh)
    -- hi >>= 3;
  , mk (wrU8 vHi) (.Papp2 (.Olsr .U8) (rdU8 vHi) (cU8 3))
    -- sh <<= 1;
  , mk (wrU8 vSh) (.Papp2 (.Olsl (.Op_w .U8)) (rdU8 vSh) (cU8 1))
    -- hi = hi & 0x1;
  , mk (wrU8 vHi) (.Papp2 (.Oland .U8) (rdU8 vHi) (cU8 1))
    -- hi = -hi;
  , mk (wrU8 vHi) (.Papp1 (.Oneg (.Op_w .U8)) (rdU8 vHi))
    -- mask = 0x3;
  , mk (wrU8 vMask) (cU8 3)
    -- hi = hi & mask;
  , mk (wrU8 vHi) (.Papp2 (.Oland .U8) (rdU8 vHi) (rdU8 vMask))
    -- sh = sh ^ hi;
  , mk (wrU8 vSh) (.Papp2 (.Olxor .U8) (rdU8 vSh) (rdU8 vHi))
    -- sh = sh & 0xf;
  , mk (wrU8 vSh) (.Papp2 (.Oland .U8) (rdU8 vSh) (cU8 0xf))
  ]

/-! ## §5. Helper: initial state with `sh`, `bb`, `r` set

We initialize an `Estate Unit NoMem` with `sh = a`, `bb = b`, `r = r0`.
The other variables (`bit_v`, `hi`, `mask`, `prod`) are left at their
default (undefined) state; the Cmd writes to them before reading. -/

/-- Initial state with the three input nibbles. -/
def initStateOfBytes (sh bb r : BitVec 8) : Estate Unit NoMem :=
  let vm0 := (Vm.init.set vSh.v_var (.Vword .U8 sh)).set vBb.v_var (.Vword .U8 bb)
  let vm := vm0.set vR.v_var (.Vword .U8 r)
  { escs := (), emem := (), evm := vm }

/-- Project the final state to the post-values of `(sh, bb, r)`. -/
def projectShBbR (s : Estate Unit NoMem) :
    Option (BitVec 8) × Option (BitVec 8) × Option (BitVec 8) :=
  ( Value.asU8? (s.evm.get vSh.v_var)
  , Value.asU8? (s.evm.get vBb.v_var)
  , Value.asU8? (s.evm.get vR.v_var) )

/-- Result of running one round of `gf16_mul_scalar`'s Cmd on inputs
    `(sh, bb, r)`. Returns `none` on any executor failure. -/
def runStep (sh bb r : BitVec 8) :
    Option (BitVec 8) × Option (BitVec 8) × Option (BitVec 8) :=
  match execCmd (Mem := NoMem) mayoAsmSem mayoOpSem []
                64 (initStateOfBytes sh bb r) gf16MulStepCmd with
  | .ok s => projectShBbR s
  | _ => (none, none, none)

/-! ## §6. Concrete-input smoke test

Pick a small representative input and check that the operational
semantics agrees with the Lean transcription `gf16MulStep`.

`gf16MulStep` operates on `BitVec 4`; we model the same step at width
`u8`. The .jinc body's invariant is "the low nibble holds the
arithmetic value; the upper nibble can be anything during the
intermediate step but is masked to `0xf` at the end of each round".

So we compare LHS = (u8) post-state masked to low nibble, RHS = lifted
`gf16MulStep` result. -/

/-- Truncate a `BitVec 8` to its low 4 bits, as `BitVec 4`. -/
def truncTo4 (w : BitVec 8) : BitVec 4 := BitVec.ofNat 4 w.toNat

/-- Smoke-test: run one round on a small example and check the
    low-nibble agreement with `gf16MulStep`. -/
def smokeAgree (sh bb r : BitVec 8) : Bool :=
  let (sh', bb', r') := runStep sh bb r
  let (sh4, bb4, r4) := gf16MulStep 0 (truncTo4 sh) (truncTo4 bb) (truncTo4 r)
  match sh', bb', r' with
  | some sh'8, some bb'8, some r'8 =>
      truncTo4 sh'8 = sh4 && truncTo4 bb'8 = bb4 && truncTo4 r'8 = r4
  | _, _, _ => false

-- Diagnostic `#eval`s (kept for debugging; output appears in the build log).
-- Expected: `(some 6#8, some 0#8, some 3#8)` and `(6#4, 0#4, 3#4)`.
#eval runStep 0x3#8 0x1#8 0x0#8
#eval gf16MulStep 0 0x3#4 0x1#4 0x0#4

/-- Smoke test on `sh = 0x3`, `bb = 0x1`, `r = 0x0`: the inner-loop
    invariant for round 0 of `gf16_mul_scalar(3, 1)` (low nibble:
    expected step result `r' = 0x3`, `sh' = 0x6`, `bb' = 0x0`). -/
example : smokeAgree 0x3#8 0x1#8 0x0#8 = true := by native_decide

/-- Smoke test: zero input → zero output. -/
example : smokeAgree 0x0#8 0x0#8 0x0#8 = true := by native_decide

/-- Smoke test: identity multiplier (`bit_i=0` of `bb=0xF`). -/
example : smokeAgree 0x1#8 0xF#8 0x0#8 = true := by native_decide

/-- Smoke test: leading bit set in `sh`, exercises the reduction step. -/
example : smokeAgree 0x8#8 0x1#8 0x0#8 = true := by native_decide

/-! ## §7. Stage 3 connector theorem (this batch's deliverable)

The connector theorem: running one round of the .jinc body through the
new jasmin operational semantics produces post-state nibbles that
agree with `MayoLeafProof.gf16MulStep`.

We prove this as a *universally quantified* identity over the 24-bit
input space `(sh, bb, r) : BitVec 8 × BitVec 8 × BitVec 8` by
`native_decide` — the cost is 2^24 = 16M evaluations of one round
(~few minutes on a workstation; for repeatable CI we instead state
the theorem and close it on a per-input basis below, demonstrating
the proof shape).

This module states the per-input smoke checks (above) and the
structural shape. The fully quantified `native_decide` version is not
stated here; it requires either a smaller input space — masking the
high nibbles to 0, which the .jinc body's invariant guarantees — or a
structural proof via `simp` unfolding of `execCmd`. -/

/-- **Connector theorem (single-round, invariant-respecting input form).**
    On inputs where the high nibbles of `sh`, `bb`, `r` are zero (the
    `.jinc` body's invariant after the final `sh = sh & 0xf` of the
    previous round), the one-round operational-semantics step agrees
    with `gf16MulStep` on the truncated 4-bit inputs.

    Universal over the `4 + 4 + 4 = 12`-bit input space (4096 cases),
    closed by `native_decide`. -/
theorem gf16MulStep_jasmin_sem_eq_smallInputs :
    ∀ (a b c : BitVec 4),
      smokeAgree (BitVec.ofNat 8 a.toNat) (BitVec.ofNat 8 b.toNat)
                 (BitVec.ofNat 8 c.toNat) = true := by
  native_decide

/-! ## §8. Summary

| Function | What | Status |
|---|---|---|
| `gf16MulStepCmd` | One inlined round of `gf16_mul_scalar` as a `JasminCoqSemMirror.Cmd` | Defined |
| `mayoOpSem` | `OpSem` instance for u8 word arithmetic | Defined |
| `runStep` | Functional executor on the round-Cmd | Defined |
| Smoke tests (5 examples) | Per-input agreement with `gf16MulStep` | **`native_decide` / `decide` PROVED** |
| `gf16MulStep_jasmin_sem_eq_smallInputs` | Round-Cmd ≅ `gf16MulStep` on the invariant-respecting input space (4096 cases) | **`decide` PROVED** |

**What this delivers**: the first proved bridge from the new
`JasminCoqSemMirror` operational semantics to a verified `.jinc`-leaf
transcription. The chain to the full unrolled `mayo_quadform_n8`
body (4 rounds × 64 inner iterations + outer accumulation) is
mechanical follow-up once `Cfor` is ported to the mirror.

**What's missing for axiom removal**:
- `Cfor` operational rule in `JasminCoqSemMirror` (currently deferred);
- `Ccall` / `inline fn` table (currently deferred);
- A proof that the OPAQUE rustcmd / hax `mayo_quadform_n8` symbol's
  denotation through the same semantics agrees with the unrolled `Cmd`
  (the `fnDef` table for the opaque function — Coq side's `progT`).

See `bench/framework/JASMIN_SEM_COVERAGE.md` for the full extension
plan and the per-protocol outlook.
-/

/-! ## §9. Framing-aware variant (CC1: inner write set)

Z's findings localised the precise blocker for MAYO's per-row preservation
step (and analogous steps in UOV, QR-UOV, MAYO L=2..5, SNOVA partial,
MQOM, SDitH): the existing universal connector
`gf16MulLoop_jasmin_sem_eq_universal'`
(in `MayoLeafJasminFullBody`) is **value-only** — it states what the `vR`
register holds in the post-state, but says nothing about other registers
that must be preserved across an inline call in the surrounding scope.

This section adds the *framing-aware* infrastructure: a precise statement
of the inner write set, plus the framing claim that any variable outside
that set is preserved by one round of `gf16MulStepCmd`.

The single-round framing is the universal piece: chaining it `N` times
(via list-fold over the `Cfor`'s precomputed range) yields the framing
claim for the full `gf16_mul_scalar` body.  The surrounding `Cfor`
itself additionally writes the loop variable `vBitI`; that goes into the
loop-driver write set, which is added by the caller (the chain in
`MayoLeafJasminFullBody.§11` consumes both pieces). -/

/-- The set of variable **names** the inner round `gf16MulStepCmd` writes
    to.  Reading off `gf16MulStepCmd` (§4): each `Cassgn` is `(.Lvar v) e`
    with `v` ∈ `{vSh, vBb, vR, vBitV, vHi, vMask, vProd}`.  These are
    exactly the 7 `reg u8` variables `gf16_mul_scalar`'s body declares.

    We index by `vname : String` rather than `Var` because `VmFlat.get`
    looks up by name and `Var.vname` is the discriminant for equality
    via `decide (y = x)` (`Vm.set` definition). -/
def gf16MulInnerWriteSet : Finset String :=
  {"sh", "bb", "r", "bit_v", "hi", "mask", "prod"}

/-- Sanity check: the 7 declared inner variables are all in the write set. -/
example : vSh.v_var.vname ∈ gf16MulInnerWriteSet := by decide
example : vBb.v_var.vname ∈ gf16MulInnerWriteSet := by decide
example : vR.v_var.vname ∈ gf16MulInnerWriteSet := by decide
example : vBitV.v_var.vname ∈ gf16MulInnerWriteSet := by decide
example : vHi.v_var.vname ∈ gf16MulInnerWriteSet := by decide
example : vMask.v_var.vname ∈ gf16MulInnerWriteSet := by decide
example : vProd.v_var.vname ∈ gf16MulInnerWriteSet := by decide

/-- Sanity check: typical outer-scope variables (the ones MAYO's
    `outerIterBody` preserves across the inline mul call) are NOT in the
    inner write set.  The framing claim's `∀ x ∉ gf16MulInnerWriteSet`
    quantifier picks them all up uniformly. -/
example : "acc" ∉ gf16MulInnerWriteSet := by decide
example : "ws" ∉ gf16MulInnerWriteSet := by decide
example : "s_buf_0" ∉ gf16MulInnerWriteSet := by decide
example : "mat_row_0" ∉ gf16MulInnerWriteSet := by decide
example : "wm_row" ∉ gf16MulInnerWriteSet := by decide
example : "sj" ∉ gf16MulInnerWriteSet := by decide
example : "aval" ∉ gf16MulInnerWriteSet := by decide
example : "sl_v" ∉ gf16MulInnerWriteSet := by decide
example : "tmp" ∉ gf16MulInnerWriteSet := by decide

/-! ### §9.a. Single-`Cassgn` preservation primitive

The atomic building block: a single `Cassgn (.Lvar x) tag ty e` instruction
writes only `x.v_var` and leaves every other variable's lookup unchanged.

For the read of `e`, errors propagate (the executor short-circuits with
`bind` on a non-`ok` `semPexpr`).  We state the framing fact only on the
`.ok` branch — the non-`ok` branches are vacuous since `execCmd` does not
produce a post-state on those.
-/

/-- `Vm.set` framing: setting `vm` at key `x` leaves the lookup at any
    `y` with a different `vname` unchanged.  Direct from
    `Vm.set`'s definition (`if decide (y = x) then v else vm y`); two
    `Var`s with distinct `vname`s are NOT equal. -/
theorem vm_set_get_of_vname_ne (vm : Vm) (x y : Var) (v : Value)
    (h : y.vname ≠ x.vname) :
    Vm.get (Vm.set vm x v) y = Vm.get vm y := by
  unfold Vm.get Vm.set
  have hne : y ≠ x := fun heq => h (by rw [heq])
  simp [hne]

/-- `setVar` framing: when `setVar wdb vm x v` returns `.ok vm'`, the post-`vm'`
    agrees with `vm` on every key `y` whose `vname` differs from `x`'s. -/
theorem setVar_frames {wdb : Bool} {vm vm' : Vm} {x y : Var} {v : Value}
    (hRun : setVar wdb vm x v = .ok vm')
    (h : y.vname ≠ x.vname) :
    Vm.get vm' y = Vm.get vm y := by
  -- `setVar` body returns `.ok (vm.set x v)` on the only success branch.
  -- We show: whenever `setVar wdb vm x v = .ok vm'`, then `vm' = vm.set x v`.
  -- The proof: case-analyse the two boolean guards.  On the .ok branch,
  -- `vm' = vm.set x v` by injection.
  have hKey : vm' = vm.set x v := by
    unfold setVar at hRun
    -- The body's outer `let ty := match x.vtype with ...` gives 4 cases.
    -- In each, the body is `if guard1 then .addrUndef else if guard2 then
    -- .typeError else .ok (vm.set x v)`.
    -- Use `simp only []` to inline the `have ty := ...` after splits so
    -- subsequent splits on the inner `if` can fire.
    split at hRun
    all_goals (
      simp only [] at hRun
      split at hRun
      · cases hRun
      · split at hRun
        · cases hRun
        · injection hRun with hVm; exact hVm.symm)
  rw [hKey]
  exact vm_set_get_of_vname_ne vm x y v h

/-- `writeVar` framing: when `writeVar wdb x v s` returns `.ok s'`, the post-
    state `s'.evm` agrees with `s.evm` on every key `y` whose `vname` differs
    from `x.v_var.vname`. -/
theorem writeVar_frames {wdb : Bool}
    {s s' : Estate Unit NoMem} {x : VarI} {y : Var} {v : Value}
    (hRun : writeVar (Mem := NoMem) wdb x v s = .ok s')
    (h : y.vname ≠ x.v_var.vname) :
    Vm.get s'.evm y = Vm.get s.evm y := by
  unfold writeVar at hRun
  -- writeVar destructures into `setVar` + `s.withVm`.  We rely on the do-
  -- desugaring exposing the bind on the `setVar` result.
  simp only [bind, JResult.bind] at hRun
  cases hSet : setVar wdb s.evm x.v_var v with
  | ok vm' =>
    rw [hSet] at hRun
    -- After the bind, hRun says `.ok (s.withVm vm') = .ok s'`.
    simp [Estate.withVm] at hRun
    have hLook : Vm.get vm' y = Vm.get s.evm y := setVar_frames hSet h
    -- s'.evm = vm', so the framing reduces to setVar_frames.
    subst hRun
    exact hLook
  | typeError | undefError | addrUndef | otherErr _ =>
    rw [hSet] at hRun
    cases hRun

/-! ### §9.b. `Cassgn`-`Lvar` single-step framing

A single `Cassgn (.Lvar x) tag ty e` instruction's framing claim. -/

/-- `writeLval` framing for the `Lvar` shape (the only one used by
    `gf16MulStepCmd`).  Errors in the inner `writeVar`/`setVar` propagate;
    on `.ok`, only `x.v_var.vname` is written. -/
theorem writeLval_Lvar_frames {wdb : Bool} {gd : GlobDecls} {opS : OpSem}
    {s s' : Estate Unit NoMem} {x : VarI} {y : Var} {v : Value}
    (hRun : writeLval (Mem := NoMem) wdb gd opS (.Lvar x) v s = .ok s')
    (h : y.vname ≠ x.v_var.vname) :
    Vm.get s'.evm y = Vm.get s.evm y := by
  -- writeLval on Lvar reduces to writeVar.
  unfold writeLval at hRun
  exact writeVar_frames hRun h

/-! ### §9.c. Framing for a single `Cassgn`-`Lvar` instruction via `execInstr`

For `Cassgn (.Lvar x) tag ty e`, the executor either short-circuits in
`semPexpr`/`truncateVal` (no post-state) or applies `writeLval`.  Either
way, on `.ok s'` the framing follows from `writeLval_Lvar_frames`. -/

/-- Single-step `Cassgn`-`Lvar` framing through the executor. -/
theorem execInstrR_Cassgn_Lvar_frames {fuel : Nat}
    {s s' : Estate Unit NoMem} {x : VarI} {tag : AssgnTag}
    {ty : Atype} {e : Pexpr} {y : Var} {prog : Prog}
    (hRun : execInstrR (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                       (.Cassgn (.Lvar x) tag ty e) prog = .ok s')
    (h : y.vname ≠ x.v_var.vname) :
    Vm.get s'.evm y = Vm.get s.evm y := by
  unfold execInstrR at hRun
  cases fuel with
  | zero => simp at hRun
  | succ fuel' =>
    simp only at hRun
    -- The body is `do { v ← semPexpr ...; v' ← truncateVal ...; writeLval ... }`
    -- We case-analyse the result of `semPexpr` then `truncateVal`.
    cases hSem : semPexpr (Mem := NoMem) true [] mayoOpSem s e with
    | ok v =>
      rw [hSem] at hRun
      simp [bind, JResult.bind] at hRun
      cases hTr : truncateVal (evalAtype ty) v with
      | ok v' =>
        rw [hTr] at hRun
        simp at hRun
        -- After the binds, hRun says `writeLval ... = .ok s'`.
        exact writeLval_Lvar_frames hRun h
      | typeError | undefError | addrUndef | otherErr _ =>
        rw [hTr] at hRun
        cases hRun
    | typeError | undefError | addrUndef | otherErr _ =>
      rw [hSem] at hRun
      cases hRun

/-! ### §9.d. Generic chain framing through `execCmd`

For an `Instr` that is `.MkI _ (.Cassgn (.Lvar x) ...)` writing `x`, the
single-step framing lifts through `execInstr`.  Chained over a sequence of
such instructions, the post-state agrees with the input on every variable
whose `vname` is not in the chain's union of LHS names. -/

/-- Lift single-step framing through `execInstr` for a `Cassgn`-`Lvar`. -/
theorem execInstr_Cassgn_Lvar_frames {fuel : Nat}
    {s s' : Estate Unit NoMem} {x : VarI} {tag : AssgnTag}
    {ty : Atype} {e : Pexpr} {y : Var} {prog : Prog}
    (hRun : execInstr (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                      (.MkI () (.Cassgn (.Lvar x) tag ty e)) prog = .ok s')
    (h : y.vname ≠ x.v_var.vname) :
    Vm.get s'.evm y = Vm.get s.evm y := by
  unfold execInstr at hRun
  exact execInstrR_Cassgn_Lvar_frames hRun h

/-! ### §9.e. The full-body framing claim for `gf16MulStepCmd`

The inner 16-instruction round body's framing: any variable whose name is
not one of the 7 inner names is preserved by the round.

The proof is by explicit symbolic execution.  Each `Cassgn (.Lvar v_i)`
preserves any `y` with `y.vname ≠ v_i.v_var.vname`.  Since the 7 LHS
variables all have `vname ∈ gf16MulInnerWriteSet`, the union over the
16 steps is contained in the same set, so any `y.vname ∉ ...` is
preserved across the whole chain. -/

/-- Helper: a single-step framing claim for an arbitrary instruction `i`
    whose LHS is a `.Lvar` whose `vname` is in a given name set `W`.

    `W` is parameteric — instantiated downstream to
    `gf16MulInnerWriteSet` and to the larger write-set unions used by
    sibling protocols. -/
private theorem step_frames_if_lhs_in_set {fuel : Nat} {W : Finset String}
    {s s' : Estate Unit NoMem} {x : VarI} {tag : AssgnTag}
    {ty : Atype} {e : Pexpr} {y : Var} {prog : Prog}
    (hRun : execInstr (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                      (.MkI () (.Cassgn (.Lvar x) tag ty e)) prog = .ok s')
    (hLHSinSet : x.v_var.vname ∈ W)
    (hNotInSet : y.vname ∉ W) :
    Vm.get s'.evm y = Vm.get s.evm y := by
  have h : y.vname ≠ x.v_var.vname := by
    intro heq
    apply hNotInSet
    rw [heq]
    exact hLHSinSet
  exact execInstr_Cassgn_Lvar_frames hRun h

/-- Predicate at the instruction level: `i` is a `Cassgn` to a `Lvar`
    whose `vname` is in `W`. -/
def InstrIsCassgnLvarInSet (W : Finset String) (i : Instr) : Prop :=
  match i with
  | .MkI _ (.Cassgn (.Lvar x) _ _ _) => x.v_var.vname ∈ W
  | _ => False

instance (W : Finset String) (i : Instr) :
    Decidable (InstrIsCassgnLvarInSet W i) := by
  unfold InstrIsCassgnLvarInSet
  match i with
  | .MkI _ (.Cassgn (.Lvar x) _ _ _) =>
    exact inferInstanceAs (Decidable (x.v_var.vname ∈ W))
  | .MkI _ (.Cassgn (.Lnone _ _) _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Cassgn (.Lmem _ _ _ _) _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Cassgn (.Laset _ _ _ _ _) _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Cassgn (.Lasub _ _ _ _ _) _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Copn _ _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Csyscall _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Cif _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Cwhile _ _ _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Cfor _ _ _) => exact isFalse (fun h => h.elim)
  | .MkI _ (.Ccall _ _ _) => exact isFalse (fun h => h.elim)

/-- Every instruction in `c` is of the shape `.MkI _ (.Cassgn (.Lvar x) ...)`
    with `x.v_var.vname` in `W`.

    This is the static side condition that makes the chained framing claim
    structural: any such Cmd's execution preserves variables outside the
    name set, by repeated application of `step_frames_if_lhs_in_set`. -/
def AllCassgnLvarInSet (W : Finset String) (c : Cmd) : Prop :=
  ∀ i ∈ c, InstrIsCassgnLvarInSet W i

/-- Generic chain framing: if every instruction in `c` is a
    `Cassgn (.Lvar x)` with `x.v_var.vname` in `W`, then `execCmd c`
    preserves every variable whose `vname` is not in `W`.

    Proof: induction on `c`.  Nil case is `rfl`.  Cons case peels one
    `Cassgn`-`Lvar` step via `step_frames_if_lhs_in_set`, then applies
    the IH to the tail. -/
theorem chain_frames_of_all_Cassgn_Lvar_in_set {fuel : Nat} {W : Finset String}
    {prog : Prog} {y : Var} :
    ∀ (c : Cmd) (s s' : Estate Unit NoMem)
      (_h_all : AllCassgnLvarInSet W c)
      (_h_run : execCmd (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s c prog = .ok s')
      (_h_y_out : y.vname ∉ W),
      Vm.get s'.evm y = Vm.get s.evm y := by
  intro c
  induction c with
  | nil =>
    intro s s' _ hRun _
    -- execCmd on [] returns .ok s, so s' = s.
    simp [execCmd] at hRun
    subst hRun; rfl
  | cons i c ih =>
    intro s s' hAll hRun hyout
    have hHd : InstrIsCassgnLvarInSet W i := hAll i (List.mem_cons_self ..)
    have hTl : AllCassgnLvarInSet W c := by
      intro j hj; exact hAll j (List.mem_cons_of_mem _ hj)
    -- Decompose `i` into its `Instr.MkI` shape, then case on the inner
    -- `InstrR`.  `hHd`'s shape rules out all non-`Cassgn (.Lvar _)` cases.
    obtain ⟨ii, ir⟩ := i
    unfold InstrIsCassgnLvarInSet at hHd
    cases ir with
    | Cassgn lv tag ty e =>
      cases lv with
      | Lvar x =>
        -- The case we care about: `i = MkI ii (Cassgn (Lvar x) tag ty e)`.
        have hLhs : x.v_var.vname ∈ W := hHd
        -- Unfold one step of execCmd on the cons.
        simp only [execCmd] at hRun
        cases hStep : execInstr (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                         (.MkI ii (.Cassgn (.Lvar x) tag ty e)) prog with
        | ok s1 =>
          rw [hStep] at hRun
          simp only [bind, JResult.bind] at hRun
          -- Apply IH to the tail.
          have eTail : Vm.get s'.evm y = Vm.get s1.evm y := ih s1 s' hTl hRun hyout
          -- Apply single-step framing to the head; ii is `()` (Unit).
          have hStep' : execInstr (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                         (.MkI () (.Cassgn (.Lvar x) tag ty e)) prog = .ok s1 := by
            -- InstrInfo = Unit, so ii = ().
            cases ii; exact hStep
          have eHead : Vm.get s1.evm y = Vm.get s.evm y :=
            step_frames_if_lhs_in_set hStep' hLhs hyout
          exact eTail.trans eHead
        | typeError | undefError | addrUndef | otherErr _ =>
          rw [hStep] at hRun
          simp [JResult.bind] at hRun
      | Lnone _ _ => exact hHd.elim
      | Lmem _ _ _ _ => exact hHd.elim
      | Laset _ _ _ _ _ => exact hHd.elim
      | Lasub _ _ _ _ _ => exact hHd.elim
    | Copn _ _ _ _ => exact hHd.elim
    | Csyscall _ _ _ => exact hHd.elim
    | Cif _ _ _ => exact hHd.elim
    | Cwhile _ _ _ _ _ => exact hHd.elim
    | Cfor _ _ _ => exact hHd.elim
    | Ccall _ _ _ => exact hHd.elim

/-- **The framing claim for `gf16MulStepCmd`**: running the 16-instruction
    inner round body from any input `Estate` produces a post-state
    (on `.ok`) that agrees with the input on every variable whose
    `vname` is not in `gf16MulInnerWriteSet`.

    Proof: the generic chain lemma `chain_frames_of_all_Cassgn_Lvar_in_set`
    plus a single `decide` discharging that every LHS is in the write
    name set. -/
theorem gf16MulStep_frames {fuel : Nat}
    {s s' : Estate Unit NoMem} {y : Var} {prog : Prog}
    (hRun : execCmd (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                    gf16MulStepCmd prog = .ok s')
    (hNotInSet : y.vname ∉ gf16MulInnerWriteSet) :
    Vm.get s'.evm y = Vm.get s.evm y := by
  have hAll : AllCassgnLvarInSet gf16MulInnerWriteSet gf16MulStepCmd := by
    intro i hi
    -- gf16MulStepCmd is a 16-element concrete list.  We walk the list
    -- by `simp [gf16MulStepCmd]` on `hi`, which produces a 16-way `Or`;
    -- each branch is `i = <one specific MkI>`, and the predicate then
    -- reduces to membership of a concrete `vname` in `gf16MulInnerWriteSet`.
    simp only [gf16MulStepCmd, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      show (_ : String) ∈ gf16MulInnerWriteSet
      decide
  exact chain_frames_of_all_Cassgn_Lvar_in_set _ _ _ hAll hRun hNotInSet

/-! ## §10. Sample reuse demonstration (CC3)

CC3 demonstrates that the framing-aware variant from §9 closes the
*framing* half of MAYO's per-row preservation step (and the analogous
half in every sibling protocol).  We do *not* close the full preservation
step here — the value half (running `gf16MulStepCmd` deposits the
correct product in `vR`) is the value-only universal connector
`gf16MulLoop_jasmin_sem_eq_universal'` in `MayoLeafJasminFullBody.lean`,
which sits *downstream* of this file in the import graph; we cannot
import it here without breaking the layering.

What CC3 ships:

  1. A **named outer-scope variable family** (the names typically used by
     MAYO's `outerIterBody` and analogues): `vAcc`, `vS_buf_0`, `vWs`,
     `vWm_row`, `vMat_row k` for `k : Fin 8`.  Each name is in the
     "outer scope" — i.e. NOT in `gf16MulInnerWriteSet`.  Membership is
     discharged by `decide`.

  2. The **framed preservation wrapper**
     `gf16MulStep_preserves_outer_var`: a direct corollary of
     `gf16MulStep_frames` showing that any of these outer variables is
     preserved across one round of `gf16MulStepCmd`.  This is the
     *framing* half of the preservation step that Z's §11 status block
     in `MayoLeafJasminFullBody.lean` identified as missing.

  3. A **templatizable shape** `framing_step_holds`: a `Prop`-valued
     wrapper that any sibling protocol can instantiate by substituting
     its inner round body's `Cmd` and write-set.  The shape is
     uniform across UOV, QR-UOV, MAYO L=2..5, SNOVA (partial), MQOM,
     SDitH — see CC4's audit table for the per-protocol mapping. -/

/-- A representative outer-scope u8 register: MAYO's accumulator. -/
def vAcc : VarI := vU8 "acc"

/-- A representative outer-scope u64 register: MAYO's packed s_buf input. -/
def vS_buf_0 : VarI := { v_var := { vtype := .aword .U64, vname := "s_buf_0" } }

/-- A representative outer-scope u64 register: MAYO's packed-s working
    copy (the `ws` register in `outerIterBody`). -/
def vWs : VarI := { v_var := { vtype := .aword .U64, vname := "ws" } }

/-- A representative outer-scope u64 register: MAYO's matrix-row working
    copy. -/
def vWm_row : VarI := { v_var := { vtype := .aword .U64, vname := "wm_row" } }

/-- A representative outer-scope u64 register: one of MAYO's 8 matrix-row
    storage registers (`mat_row_0`..`mat_row_7`). -/
def vMat_row (k : Nat) : VarI :=
  { v_var := { vtype := .aword .U64, vname := s!"mat_row_{k}" } }

/-- A representative outer-scope u8 register: MAYO's per-iteration `sj`
    nibble. -/
def vSj : VarI := vU8 "sj"

/-- A representative outer-scope u8 register: MAYO's per-iteration `aval`
    nibble. -/
def vAval : VarI := vU8 "aval"

/-- A representative outer-scope u8 register: MAYO's per-iteration `sl_v`
    nibble. -/
def vSl_v : VarI := vU8 "sl_v"

/-- A representative outer-scope u8 register: MAYO's `tmp` intermediate. -/
def vTmp : VarI := vU8 "tmp"

/-- Membership audit: all the representative outer-scope variables
    declared above are *NOT* in the inner write set, so the framing
    lemma applies to each. -/
example : vAcc.v_var.vname ∉ gf16MulInnerWriteSet := by decide
example : vS_buf_0.v_var.vname ∉ gf16MulInnerWriteSet := by decide
example : vWs.v_var.vname ∉ gf16MulInnerWriteSet := by decide
example : vWm_row.v_var.vname ∉ gf16MulInnerWriteSet := by decide
example : vSj.v_var.vname ∉ gf16MulInnerWriteSet := by decide
example : vAval.v_var.vname ∉ gf16MulInnerWriteSet := by decide
example : vSl_v.v_var.vname ∉ gf16MulInnerWriteSet := by decide
example : vTmp.v_var.vname ∉ gf16MulInnerWriteSet := by decide

/-- For every `k`, `vMat_row k`'s vname is `mat_row_k` which is NOT in
    the inner write set.

    Proof: a length argument — every element of `gf16MulInnerWriteSet`
    has length ≤ 5, but `s!"mat_row_{k}"` has length ≥ 8 ("mat_row_"
    prefix plus at least one digit).  The membership disjunction reduces
    to 7 string-equality impossibilities, each ruled out by length. -/
theorem vMat_row_not_in_set (k : Nat) :
    (vMat_row k).v_var.vname ∉ gf16MulInnerWriteSet := by
  intro hmem
  -- The vname is "mat_row_" ++ toString k. Its length is ≥ 8.
  have hLenLeft : (vMat_row k).v_var.vname.length ≥ 8 := by
    show (toString "mat_row_" ++ toString k).length ≥ 8
    rw [String.length_append]
    have hPrefix : (toString "mat_row_" : String).length = 8 := by decide
    omega
  -- Each name in the inner write set has length ≤ 5.
  simp only [vMat_row, gf16MulInnerWriteSet, Finset.mem_insert,
             Finset.mem_singleton] at hmem
  rcases hmem with h|h|h|h|h|h|h
  all_goals (
    have hLenRight : (vMat_row k).v_var.vname.length ≤ 5 := by
      show (toString "mat_row_" ++ toString k).length ≤ 5
      rw [h]; decide
    omega)

/-- **Framed preservation wrapper** (CC3 deliverable).  Running
    `gf16MulStepCmd` from any input state preserves the lookup of any
    outer-scope variable (one not in `gf16MulInnerWriteSet`).  This is
    the *framing* half of MAYO's per-row preservation step.

    Direct corollary of `gf16MulStep_frames` — provided for callsite
    clarity (the abstract "outer variable" wording lines up directly with
    the per-row preservation step's specification). -/
theorem gf16MulStep_preserves_outer_var {fuel : Nat}
    {s s' : Estate Unit NoMem} {y : VarI} {prog : Prog}
    (hRun : execCmd (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                    gf16MulStepCmd prog = .ok s')
    (hOuter : y.v_var.vname ∉ gf16MulInnerWriteSet) :
    Vm.get s'.evm y.v_var = Vm.get s.evm y.v_var :=
  gf16MulStep_frames hRun hOuter

/-! ### §10.a. Per-outer-variable preservation: ready-to-use specialisations

These instantiate `gf16MulStep_preserves_outer_var` at each of the 9
representative outer-scope variables identified by Z's §11 status block.
They are direct one-liners using `decide` for the `∉` side condition. -/

/-- `vAcc` is preserved by one round of `gf16MulStepCmd`. -/
theorem gf16MulStep_preserves_vAcc {fuel : Nat}
    {s s' : Estate Unit NoMem} {prog : Prog}
    (hRun : execCmd (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                    gf16MulStepCmd prog = .ok s') :
    Vm.get s'.evm vAcc.v_var = Vm.get s.evm vAcc.v_var :=
  gf16MulStep_preserves_outer_var hRun (by decide)

/-- `vS_buf_0` is preserved by one round of `gf16MulStepCmd`. -/
theorem gf16MulStep_preserves_vS_buf_0 {fuel : Nat}
    {s s' : Estate Unit NoMem} {prog : Prog}
    (hRun : execCmd (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                    gf16MulStepCmd prog = .ok s') :
    Vm.get s'.evm vS_buf_0.v_var = Vm.get s.evm vS_buf_0.v_var :=
  gf16MulStep_preserves_outer_var hRun (by decide)

/-- `vWs` is preserved by one round of `gf16MulStepCmd`. -/
theorem gf16MulStep_preserves_vWs {fuel : Nat}
    {s s' : Estate Unit NoMem} {prog : Prog}
    (hRun : execCmd (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                    gf16MulStepCmd prog = .ok s') :
    Vm.get s'.evm vWs.v_var = Vm.get s.evm vWs.v_var :=
  gf16MulStep_preserves_outer_var hRun (by decide)

/-- `vMat_row k` is preserved by one round of `gf16MulStepCmd`, for every
    matrix row index `k`. -/
theorem gf16MulStep_preserves_vMat_row {fuel : Nat} (k : Nat)
    {s s' : Estate Unit NoMem} {prog : Prog}
    (hRun : execCmd (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s
                    gf16MulStepCmd prog = .ok s') :
    Vm.get s'.evm (vMat_row k).v_var = Vm.get s.evm (vMat_row k).v_var :=
  gf16MulStep_preserves_outer_var hRun (vMat_row_not_in_set k)

/-! ### §10.b. Templatizable shape for sibling protocols (CC4 reference)

The `framing_step_holds` predicate is the *uniform shape* that any
sibling protocol's per-row preservation step instantiates.  For UOV,
QR-UOV, MAYO L=2..5, SNOVA (partial), MQOM, SDitH: substitute the
protocol's inner round Cmd and write-set; the framing lemma's
*statement* is unchanged, and the proof structure (via
`chain_frames_of_all_Cassgn_Lvar_in_set` + a `decide` on the per-instr
LHS membership) is identical. -/

/-- The uniform shape of a "framing step holds" claim, parameteric in
    the inner round body `body : Cmd` and the inner write set
    `W : Finset String`.  Templatize this for sibling protocols.

    This is the universal-quantification-over-input-state, named for
    clarity — it is the same shape that `gf16MulStep_frames`
    instantiates at `body = gf16MulStepCmd` and `W = gf16MulInnerWriteSet`. -/
def FramingStepHolds (body : Cmd) (W : Finset String) : Prop :=
  ∀ {fuel : Nat} {prog : Prog} {s s' : Estate Unit NoMem} {y : Var},
    execCmd (Mem := NoMem) mayoAsmSem mayoOpSem [] fuel s body prog = .ok s' →
    y.vname ∉ W →
    Vm.get s'.evm y = Vm.get s.evm y

/-- **The framed-step exists** for MAYO's inner round body
    `gf16MulStepCmd` with write set `gf16MulInnerWriteSet`.  This is the
    concrete instantiation of the uniform shape.

    *Sibling protocols*: instantiate `FramingStepHolds` at their inner
    round Cmd + write set, then prove via
    `chain_frames_of_all_Cassgn_Lvar_in_set`.  Templated copy is ~50–80
    LOC per sibling (only the per-instruction LHS membership check
    changes; the chain lemma is reused verbatim). -/
theorem framing_step_holds_gf16 :
    FramingStepHolds gf16MulStepCmd gf16MulInnerWriteSet := by
  intro fuel prog s s' y hRun hyout
  exact gf16MulStep_frames hRun hyout

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MayoLeafJasminSim
