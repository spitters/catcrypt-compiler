/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# A Lean AArch64 (ARM64) machine model for the scalar GP-ALU subset (#533)

`X86Backend/Model.lean` (scalar) and `X86Backend/Vec128Model.lean` (packed-u32
SIMD) are the owned x86 machine layers; this module is their **AArch64 (A64)**
analogue at the scalar 32-bit-word GP-ALU shape that a ChaCha20 quarter-round
needs (`add`/`eor`/`ror`, plus `mov`/`sub`/`and`/`orr`/`lsl`/`lsr` and
`ldr`/`str`). It adds a named general-purpose register file (`AState`) over the
A64 word registers (`w0…w30`, the 32-bit views of `x0…x30`, plus `wzr`) and the
per-instruction semantics (`evalAInst` / `runABlock`) of that subset.

`ArmLowering.lean` lifts a register-named op alphabet (`AOp`) onto this model
with the block-lowering denotation theorem `armBlock_lowering_denote` (the A64
analogue of `Vec128Lowering.vec128Block_lowering_denote`, proved by induction
with no new custom axioms); `ArmAsmPrinter.lean` renders the lowered `AInst`
block to GAS AArch64 assembly text with a linear-scan GP allocator.

## The honest anchor (same posture as the x86 owned model)

This sub-1 stands up the *framework*: a Lean A64 GP-ALU machine + verified
lowering + GAS printer, with one scalar primitive (the RFC 8439 §2.1.1 ChaCha
quarter-round) emitted and the in-Lean KAT pinned. As with the x86 SIMD model,
the **lowering** `AOp → AInst → AState transform` is verified down to this model
(`ArmLowering.armBlock_lowering_denote`, no new custom axioms); the **model's
per-instruction semantics** is written to be obviously the integer op the A64
mnemonic computes (Arm ARM `ADD`/`EOR`/`ROR`/… on 32-bit `W` registers,
auditable by eye), and is differentially validated against the RFC 8439 KAT.

**Landed in sub-2**: the machine-code byte `Encoder` (`ArmEncoder.lean`) +
`decode(encode i) = i` against the hand-transcribed `rems-project/sail-arm`
`decode64` tables (`SailArmDecoder.lean` — upstream is not vendored in this repo
and the transcription is not machine-checked; the A64 analogue of
`SailX86Decoder`), axiom-clean
and gas-differential-pinned. **Deferred to sub-3**: NEON/SVE SIMD (the A64
`Vec128` analogue) and the `FEAT_SHA3` Keccak extension. This module deliberately
covers only the scalar 32-bit-`W` GP-ALU subset.

## The A64 scalar ops we model (the GP-ALU subset ChaCha emits)

| mnemonic | shape          | op (32-bit `W`)                       |
|----------|----------------|---------------------------------------|
| `MOV`    | `Wd, Wn`       | `Wd := Wn`                            |
| `ADD`    | `Wd, Wn, Wm`   | `Wd := Wn + Wm`  (wrapping 32-bit)    |
| `SUB`    | `Wd, Wn, Wm`   | `Wd := Wn - Wm`  (wrapping 32-bit)    |
| `AND`    | `Wd, Wn, Wm`   | `Wd := Wn &&& Wm`                     |
| `ORR`    | `Wd, Wn, Wm`   | `Wd := Wn ||| Wm`                     |
| `EOR`    | `Wd, Wn, Wm`   | `Wd := Wn ^^^ Wm`                     |
| `LSL`    | `Wd, Wn, #imm` | `Wd := Wn <<< imm`  (logical shl)     |
| `LSR`    | `Wd, Wn, #imm` | `Wd := Wn >>> imm`  (logical shr)     |
| `ROR`    | `Wd, Wn, #imm` | `Wd := Wn rotr imm` (rotate right)    |

A64 has a native `ROR` (rotate-right by immediate), so the ChaCha
rotate-**left** by `n` is a single `ROR Wd, Wn, #(32-n)` — unlike the x86 SIMD
path which synthesizes it from `shl ; shr ; or`. We model `ROR` directly.
`LDR`/`STR` (the load/store the function prologue/epilogue uses to read args and
write the result) are modeled as identity register moves at this scalar level
(they touch the named register file, not a separate memory model) — the verified
straight-line body is register-to-register; memory traffic is trusted scaffolding,
exactly the x86 `renderLeafFn` posture.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. The A64 word type and register state

We model the 32-bit `W` registers (the lower halves of `x0…x30`), which is the
lane width ChaCha20 operates on. A register is a `BitVec 32`; the file is a
`String → BitVec 32` function keyed by register name. An absent name (and the
zero register `wzr`) reads as `0`. -/

/-- A 32-bit A64 `W` register value. -/
abbrev W32 : Type := BitVec 32

/-- The A64 GP register file: a name → `W32` function. An absent name (e.g. an
    uninitialised temporary, or the zero register `wzr`) reads as `0`. -/
structure AState where
  /-- The `W` register file (`w0 … w30`, named by string). -/
  regs : String → W32

namespace AState

/-- Read a `W` register. The zero register `wzr`/`wzr32` and any absent name
    read as `0`. -/
@[simp] def get (s : AState) (r : String) : W32 :=
  if r = "wzr" then 0 else s.regs r

/-- Write a `W` register, leaving the others unchanged. Writes to `wzr` are
    discarded (the A64 zero register is write-ignored). -/
def set (s : AState) (r : String) (v : W32) : AState :=
  if r = "wzr" then s else { regs := fun r' => if r' = r then v else s.regs r' }

@[simp] theorem get_set_same (s : AState) (r : String) (v : W32) (h : r ≠ "wzr") :
    (s.set r v).get r = v := by simp [set, get, h]

@[simp] theorem get_set_other (s : AState) (r r' : String) (v : W32)
    (h : r' ≠ r) : (s.set r v).get r' = s.get r' := by
  by_cases hz : r' = "wzr"
  · simp [get, hz]
  · simp only [get, hz, if_false, set]
    by_cases hr : r = "wzr"
    · simp [hr]
    · simp [hr, h]

end AState

/-! ## 2. Per-op 32-bit-word A64 ALU semantics

Each op is the obvious 32-bit integer op over `BitVec 32` — auditable against
the Arm Architecture Reference Manual by eye. -/

/-- `ADD` op: wrapping 32-bit add. -/
@[simp] def opAdd (a b : W32) : W32 := a + b

/-- `SUB` op: wrapping 32-bit subtract. -/
@[simp] def opSub (a b : W32) : W32 := a - b

/-- `AND` op: bitwise and. -/
@[simp] def opAnd (a b : W32) : W32 := a &&& b

/-- `ORR` op: bitwise or. -/
@[simp] def opOrr (a b : W32) : W32 := a ||| b

/-- `EOR` op: bitwise xor. -/
@[simp] def opEor (a b : W32) : W32 := a ^^^ b

/-- `LSL` op: logical left shift by an immediate count. -/
@[simp] def opLsl (a : W32) (m : Nat) : W32 := a <<< m

/-- `LSR` op: logical right shift by an immediate count. -/
@[simp] def opLsr (a : W32) (m : Nat) : W32 := a >>> m

/-- `ROR` op: rotate right by an immediate count (the native A64 rotate). -/
@[simp] def opRor (a : W32) (m : Nat) : W32 := BitVec.rotateRight a m

/-! ## 3. The A64 scalar instruction set

The GP-ALU subset the ChaCha quarter-round emits. Each arm names its
destination + source `W` registers (or an immediate count, for the shifts/rotate).
The machine-level analogue of `Vec128Model.VInst`, at 32-bit scalar shape. -/

/-- A single scalar A64 instruction over named `W` registers. -/
inductive AInst where
  /-- `ADD Wd, Wn, Wm` — 32-bit add. -/
  | add (d a b : String)
  /-- `SUB Wd, Wn, Wm` — 32-bit subtract. -/
  | sub (d a b : String)
  /-- `AND Wd, Wn, Wm` — bitwise and. -/
  | and (d a b : String)
  /-- `ORR Wd, Wn, Wm` — bitwise or. -/
  | orr (d a b : String)
  /-- `EOR Wd, Wn, Wm` — bitwise xor. -/
  | eor (d a b : String)
  /-- `LSL Wd, Wn, #imm` — logical shift-left by immediate. -/
  | lsl (d a : String) (imm : Nat)
  /-- `LSR Wd, Wn, #imm` — logical shift-right by immediate. -/
  | lsr (d a : String) (imm : Nat)
  /-- `ROR Wd, Wn, #imm` — rotate-right by immediate. -/
  | ror (d a : String) (imm : Nat)
  /-- `MOV Wd, Wn` — register move. -/
  | mov (d s : String)
  deriving Repr, DecidableEq

/-! ### A64 branch / control-flow instructions (the looped-emission alphabet, #551)

The straight-line `AInst` set above carries no control flow. A bounded counter
loop's back-edge needs three A64 branch forms, each a single 32-bit word with a
PC-relative immediate offset to a label:

* `B label` — unconditional branch (`PC := PC + imm26·4`);
* `B.cond label` — conditional branch on the NZCV condition the preceding
  `SUBS`/`CMP` set (`imm19·4` offset);
* `CBNZ Wt, label` — compare-and-branch-if-`Wt`-non-zero (`imm19·4` offset);
  the counter-loop back-edge: decrement the loop counter, `CBNZ` to the top while
  it is non-zero. (`CBZ` is its `=0` dual.)

A `Label` is a function-local symbol; the looped emission threads one fresh label
per loop. The branch alphabet is a *separate* inductive from `AInst` (the
straight-line model carries no PC), used by the printer/encoder; the loop
*semantics* is `runBoundedLoopA` above (the body's counter decrement + the
back-edge collapse to "run the body `n` times"). -/

/-- A function-local branch label (a string symbol). -/
abbrev ALabel : Type := String

/-- The A64 condition codes a `B.cond` back-edge / forward guard selects on (the
    NZCV flags a `SUBS`/`CMP` set). `ne`/`eq` are the counter-loop conditions
    (`Z=0` ⇒ counter ≠ 0). -/
inductive BCond where
  /-- `NE` — not equal (`Z = 0`); the loop-while-counter-nonzero back-edge. -/
  | ne
  /-- `EQ` — equal (`Z = 1`). -/
  | eq
  /-- `CC`/`LO` — carry clear / unsigned `<`. -/
  | cc
  /-- `CS`/`HS` — carry set / unsigned `≥`. -/
  | cs
  deriving Repr, DecidableEq

/-- The 4-bit A64 condition-code number (Arm ARM C1.2.4): `EQ=0`, `NE=1`,
    `CS/HS=2`, `CC/LO=3`. -/
def BCond.num : BCond → Nat
  | .eq => 0
  | .ne => 1
  | .cs => 2
  | .cc => 3

/-- A single A64 branch / control-flow instruction (or a label definition). The
    looped-emission control-flow alphabet, distinct from the straight-line
    `AInst`. -/
inductive ABranch where
  /-- `label:` — a function-local label definition (no machine word; the assembler
      resolves the PC-relative offsets of branches that target it). -/
  | label (l : ALabel)
  /-- `B label` — unconditional branch. -/
  | b (l : ALabel)
  /-- `B.cond label` — conditional branch on the NZCV condition. -/
  | bcond (c : BCond) (l : ALabel)
  /-- `CBNZ Wt, label` — branch if `Wt ≠ 0` (the counter back-edge). -/
  | cbnz (t : String) (l : ALabel)
  /-- `CBZ Wt, label` — branch if `Wt = 0`. -/
  | cbz (t : String) (l : ALabel)
  deriving Repr, DecidableEq

/-- The semantics of one A64 instruction: read source register(s), apply the
    op, write the destination. The analogue of `Vec128Model.evalVInst`. -/
def evalAInst (s : AState) : AInst → AState
  | .add d a b => s.set d (opAdd (s.get a) (s.get b))
  | .sub d a b => s.set d (opSub (s.get a) (s.get b))
  | .and d a b => s.set d (opAnd (s.get a) (s.get b))
  | .orr d a b => s.set d (opOrr (s.get a) (s.get b))
  | .eor d a b => s.set d (opEor (s.get a) (s.get b))
  | .lsl d a m => s.set d (opLsl (s.get a) m)
  | .lsr d a m => s.set d (opLsr (s.get a) m)
  | .ror d a m => s.set d (opRor (s.get a) m)
  | .mov d a   => s.set d (s.get a)

/-- `runABlock`: a straight-line fold of `evalAInst`, the A64 analogue of
    `Vec128Model.runVBlock`. -/
def runABlock (s : AState) : List AInst → AState
  | [] => s
  | i :: is => runABlock (evalAInst s i) is

@[simp] theorem runABlock_nil (s : AState) : runABlock s [] = s := rfl

@[simp] theorem runABlock_cons (s : AState) (i : AInst) (is : List AInst) :
    runABlock s (i :: is) = runABlock (evalAInst s i) is := rfl

@[simp] theorem runABlock_append (s : AState) (xs ys : List AInst) :
    runABlock s (xs ++ ys) = runABlock (runABlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runABlock_cons, ih]

/-! ## 3b. A64 bounded counter loop semantics (the looped-emission backbone, #551)

`ArmControlFlow.lean` lowers a **bounded counter loop** — `for k in 0..n { body }`
— to a single body copy wrapped in an A64 back-edge `label: <body> ; CBNZ <ctr>,
label`, instead of unrolling the body `n` times. The machine semantics of that
looped form is `runBoundedLoopA s n body`: the `evalAInst`-fold of `body` run `n`
times, the A64 analogue of `X86Backend/LoopUnroll.runBoundedLoop`. We give the
semantics here (it lives at the model level, no control-flow `AInst` needed: the
body is assumed to perform its own counter decrement, so the looped emission and
the semantics agree on the register state) and prove its denotation in
`ArmControlFlow.lean`. -/

/-- `runBoundedLoopA s n body`: the machine semantics of a bounded counter loop
    that runs the straight-line `body` exactly `n` times over the `AState` model.
    The A64 analogue of `X86Backend/LoopUnroll.runBoundedLoop`; `body` is assumed
    to perform its own counter decrement (so the looped emission's `CBNZ` back-edge
    tests the just-decremented counter). -/
def runBoundedLoopA (s : AState) (n : Nat) (body : List AInst) : AState :=
  match n with
  | 0 => s
  | k + 1 => runBoundedLoopA (runABlock s body) k body

@[simp] theorem runBoundedLoopA_zero (s : AState) (body : List AInst) :
    runBoundedLoopA s 0 body = s := rfl

@[simp] theorem runBoundedLoopA_succ (s : AState) (k : Nat) (body : List AInst) :
    runBoundedLoopA s (k + 1) body = runBoundedLoopA (runABlock s body) k body := rfl

/-- The straight-line **unrolled** block of the same loop: `body` replicated `n`
    times. The A64 analogue of `X86Backend/LoopUnroll.unrollBounded`. -/
def unrollABounded (n : Nat) (body : List AInst) : List AInst :=
  match n with
  | 0 => []
  | k + 1 => body ++ unrollABounded k body

/-- **The bounded loop equals running the unrolled block.** `runBoundedLoopA s n
    body = runABlock s (unrollABounded n body)` — the looped semantics is exactly
    what running the `n`-copy unrolled straight-line block computes, by induction
    (the A64 analogue of `runBoundedLoop_eq_runBlock_unroll`). -/
theorem runBoundedLoopA_eq_runABlock_unroll (s : AState) (n : Nat) (body : List AInst) :
    runBoundedLoopA s n body = runABlock s (unrollABounded n body) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp only [runBoundedLoopA_succ, unrollABounded, runABlock_append, ih]

/-! ## 4. Differential-validation pins (the scalar A64 anchor)

Unit-level witnesses for the ops; the integration witness is the ChaCha
quarter-round KAT (`ArmLowering.qr_rfc_kat`, RFC 8439 §2.1.1). -/

/-- `ADD` pin: wrapping 32-bit add, `(2³²-1) + 3 = 2`. -/
example : opAdd (BitVec.allOnes 32) (3 : BitVec 32) = 2 := by native_decide

/-- `EOR` pin: `0xff00ff00 ^ 0x00ff00ff = 0xffffffff`. -/
example : opEor (BitVec.ofNat 32 0xff00ff00) (BitVec.ofNat 32 0x00ff00ff)
    = BitVec.allOnes 32 := by native_decide

/-- `ROR` pin realizes the ChaCha rotate-left-16 as `ROR #16`: on
    `x = 0x12345678`, `rotr(x, 16) = 0x56781234` (= `rotl(x, 16)`). -/
example : opRor (BitVec.ofNat 32 0x12345678) 16 = BitVec.ofNat 32 0x56781234 := by
  native_decide

/-! ## 5. The 64-bit `X`-register bignum/field machine (#547)

The GP-ALU subset above is the 32-bit `W`-register lane width ChaCha needs. The
**bignum/field hot path** (the s2n-bignum-class kernels: 256-bit add-mod-p, 4×64
Montgomery multiply) runs on the 64-bit `X` registers and is driven by the
multi-precision carry chain that AArch64 — unlike RISC-V — exposes as *real*
NZCV flags: `ADDS`/`ADCS` (flag-setting add, carry in/out via `C`), `SUBS`/`SBCS`
(flag-setting subtract, borrow via `C`), the widening `MUL`/`UMULH` (64×64→128
low/high halves, no flags), and the conditional-select `CSEL`/`CSET` that realises
the constant-time conditional-subtract reduce. This is the A64 analogue of the
x86 `JasminModel` ADX carry-chain layer (`X86Backend/BignumMontMulKernel.lean`).

We model a 64-bit register file `BState` carrying the **carry flag** `C` (the
only NZCV bit the carry chain reads: ADCS reads `C` as carry-in, SBCS reads `C`
as `¬borrow`; CSEL on `cc`/`cs` reads `C`). The semantics of each flag-setting op
is the obvious 65-bit-truncated `BitVec 64` computation, with `C` set to the
65th (carry/borrow) bit — auditable against the Arm ARM `AddWithCarry` pseudocode
by eye, the same posture as the 32-bit ops above. -/

/-- A 64-bit A64 `X` register value. -/
abbrev X64 : Type := BitVec 64

/-- The 64-bit A64 machine state: the `X` register file (`x0 … x30`, named by
    string; absent names and the zero register `xzr` read as `0`) plus the carry
    flag `C` (the NZCV `C` bit). We track only `C` because it is the only flag the
    modelled bignum carry chain reads (`ADCS` carry-in, `SBCS` `¬borrow`, `CSEL`
    on `cc`/`cs`). -/
structure BState where
  /-- The `X` register file (`x0 … x30`, named by string). -/
  regs : String → X64
  /-- The NZCV carry flag `C`. -/
  cf : Bool

namespace BState

/-- Read an `X` register. The zero register `xzr` and any absent name read `0`. -/
@[simp] def get (s : BState) (r : String) : X64 :=
  if r = "xzr" then 0 else s.regs r

/-- Write an `X` register, leaving the others (and the flag) unchanged. Writes to
    `xzr` are discarded (the A64 zero register is write-ignored). -/
def set (s : BState) (r : String) (v : X64) : BState :=
  if r = "xzr" then s
  else { s with regs := fun r' => if r' = r then v else s.regs r' }

/-- Write an `X` register *and* set the carry flag (the flag-setting form). -/
def setC (s : BState) (r : String) (v : X64) (c : Bool) : BState :=
  if r = "xzr" then { s with cf := c }
  else { regs := fun r' => if r' = r then v else s.regs r', cf := c }

@[simp] theorem get_set_same (s : BState) (r : String) (v : X64) (h : r ≠ "xzr") :
    (s.set r v).get r = v := by simp [set, get, h]

@[simp] theorem get_setC_same (s : BState) (r : String) (v : X64) (c : Bool)
    (h : r ≠ "xzr") : (s.setC r v c).get r = v := by simp [setC, get, h]

@[simp] theorem cf_setC (s : BState) (r : String) (v : X64) (c : Bool) :
    (s.setC r v c).cf = c := by simp [setC]; split <;> rfl

end BState

/-! ### The widening multiply and the `AddWithCarry` primitives

`MUL`/`UMULH` form the 64×64→128 product; `addWithCarry`/`subWithBorrow` are the
65-bit-truncated flag-setting add/subtract the Arm ARM `AddWithCarry` pseudocode
computes (result is the low 64 bits, `C` is the carry/borrow out). -/

/-- `MUL` op: the low 64 bits of the 64×64 product. -/
@[simp] def opMul (a b : X64) : X64 := a * b

/-- `UMULH` op: the high 64 bits of the *unsigned* 64×64 product. -/
@[simp] def opUmulh (a b : X64) : X64 :=
  BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)

/-- `AND` op: bitwise conjunction (64-bit, the `BInst` analogue of `AInst.and`). -/
@[simp] def opAnd64 (a b : X64) : X64 := a &&& b

/-- `ORR` op: bitwise disjunction (64-bit). -/
@[simp] def opOrr64 (a b : X64) : X64 := a ||| b

/-- `EOR` op: bitwise exclusive-or (64-bit). -/
@[simp] def opEor64 (a b : X64) : X64 := a ^^^ b

/-- `LSR` op: logical shift-right by an immediate count (64-bit). -/
@[simp] def opLsr64 (a : X64) (m : Nat) : X64 := a >>> m

/-- `LSL` op: logical shift-left by an immediate count (64-bit). -/
@[simp] def opLsl64 (a : X64) (m : Nat) : X64 := a <<< m

/-- `AddWithCarry`: 64-bit add of `a`, `b` and a carry-in bit; returns the
    low-64 result and the carry-out `C` (the 65th bit), matching the Arm ARM
    `AddWithCarry` pseudocode for the add direction. -/
def addWithCarry (a b : X64) (cin : Bool) : X64 × Bool :=
  let s : Nat := a.toNat + b.toNat + (if cin then 1 else 0)
  (BitVec.ofNat 64 s, s ≥ 2 ^ 64)

/-- `AddWithCarry` for subtract: `a - b - ¬cin = a + ¬b + cin` (A64 `SUBS`/`SBCS`
    semantics: the borrow flag `C` is `1` when there is **no** borrow). With
    `cin = C`, this is the Arm ARM `AddWithCarry(a, NOT(b), C)`. -/
def subWithBorrow (a b : X64) (cin : Bool) : X64 × Bool :=
  addWithCarry a (~~~ b) cin

/-! ### The 64-bit bignum/field instruction set

The hot-path subset: flag-setting add/sub with carry (`ADDS`/`ADCS`/`SUBS`/`SBCS`,
plus the plain `ADD`/`SUB` and `ADC`/`SBC` non-flag-setting forms used to fold
the top carry word), the widening `MUL`/`UMULH`, the conditional select/set
(`CSEL`/`CSET`), the wide-immediate `MOVZ`/`MOVK` constant load, and `MOV` /
`LDP`/`STP` modelled as register moves (memory traffic is trusted scaffolding,
the same posture as the 32-bit `LDR`/`STR`). The condition codes we need are
`cc` (carry clear, `C=0`) / `cs` (carry set, `C=1`) — the ones the
conditional-subtract reduce selects on. -/

/-- The A64 condition codes the conditional-select reduce uses. -/
inductive ACond where
  /-- `CC`/`LO` — carry clear (`C = 0`), i.e. unsigned `<` after a `SUBS`. -/
  | cc
  /-- `CS`/`HS` — carry set (`C = 1`), i.e. unsigned `≥` after a `SUBS`. -/
  | cs
  deriving Repr, DecidableEq

/-- Evaluate a condition code against the carry flag. -/
@[simp] def ACond.holds : ACond → Bool → Bool
  | .cc, c => !c
  | .cs, c => c

/-- A single 64-bit A64 bignum/field instruction over named `X` registers. -/
inductive BInst where
  /-- `ADD Xd, Xn, Xm` — 64-bit add, no flags. -/
  | add (d a b : String)
  /-- `SUB Xd, Xn, Xm` — 64-bit subtract, no flags. -/
  | sub (d a b : String)
  /-- `ADDS Xd, Xn, Xm` — add, set `C` (starts a carry chain). -/
  | adds (d a b : String)
  /-- `ADCS Xd, Xn, Xm` — add with carry-in `C`, set `C` (continues a chain). -/
  | adcs (d a b : String)
  /-- `ADC Xd, Xn, Xm` — add with carry-in `C`, no flags (folds top carry). -/
  | adc (d a b : String)
  /-- `SUBS Xd, Xn, Xm` — subtract, set `C` (`C=1` ⇔ no borrow). -/
  | subs (d a b : String)
  /-- `SBCS Xd, Xn, Xm` — subtract with borrow `C`, set `C`. -/
  | sbcs (d a b : String)
  /-- `SBC Xd, Xn, Xm` — subtract with borrow `C`, no flags. -/
  | sbc (d a b : String)
  /-- `MUL Xd, Xn, Xm` — low 64 bits of the product (= `MADD Xd,Xn,Xm,XZR`). -/
  | mul (d a b : String)
  /-- `UMULH Xd, Xn, Xm` — high 64 bits of the unsigned product. -/
  | umulh (d a b : String)
  /-- `AND Xd, Xn, Xm` — 64-bit bitwise conjunction. -/
  | and (d a b : String)
  /-- `ORR Xd, Xn, Xm` — 64-bit bitwise disjunction. -/
  | orr (d a b : String)
  /-- `EOR Xd, Xn, Xm` — 64-bit bitwise exclusive-or. -/
  | eor (d a b : String)
  /-- `CSEL Xd, Xn, Xm, cond` — `Xd := cond ? Xn : Xm`. -/
  | csel (d a b : String) (c : ACond)
  /-- `MOVZ Xd, #imm16` — zero-extended 16-bit immediate (clears the register). -/
  | movz (d : String) (imm16 : Nat)
  /-- `MOVK Xd, #imm16, LSL #(16·hw)` — insert 16-bit immediate into `Xd[hw]`. -/
  | movk (d : String) (imm16 hw : Nat)
  /-- `MOV Xd, Xn` — register move (`ORR Xd, XZR, Xn`). -/
  | mov (d s : String)
  /-- `LSR Xd, Xn, #imm` — logical shift-right by immediate (`UBFM` alias). -/
  | lsr (d a : String) (imm : Nat)
  /-- `LSL Xd, Xn, #imm` — logical shift-left by immediate (`UBFM` alias). -/
  | lsl (d a : String) (imm : Nat)
  deriving Repr, DecidableEq

/-- Insert the 16-bit immediate `imm16` into the `hw`-th 16-bit lane of `old`
    (the `MOVK` field write), leaving the other lanes unchanged. -/
def movkInsert (old : X64) (imm16 hw : Nat) : X64 :=
  let lo := hw * 16
  let mask : X64 := BitVec.ofNat 64 (0xffff <<< lo)
  (old &&& ~~~ mask) ||| (BitVec.ofNat 64 ((imm16 % 0x10000) <<< lo))

/-- The semantics of one 64-bit A64 instruction: read source register(s) (and the
    carry flag where relevant), apply the op, write the destination (and the
    flag, for the `S`-forms). -/
def evalBInst (s : BState) : BInst → BState
  | .add d a b => s.set d (s.get a + s.get b)
  | .sub d a b => s.set d (s.get a - s.get b)
  | .adds d a b =>
      let (v, c) := addWithCarry (s.get a) (s.get b) false
      s.setC d v c
  | .adcs d a b =>
      let (v, c) := addWithCarry (s.get a) (s.get b) s.cf
      s.setC d v c
  | .adc d a b =>
      let (v, _) := addWithCarry (s.get a) (s.get b) s.cf
      s.set d v
  | .subs d a b =>
      let (v, c) := subWithBorrow (s.get a) (s.get b) true
      s.setC d v c
  | .sbcs d a b =>
      let (v, c) := subWithBorrow (s.get a) (s.get b) s.cf
      s.setC d v c
  | .sbc d a b =>
      let (v, _) := subWithBorrow (s.get a) (s.get b) s.cf
      s.set d v
  | .mul d a b => s.set d (opMul (s.get a) (s.get b))
  | .umulh d a b => s.set d (opUmulh (s.get a) (s.get b))
  | .and d a b => s.set d (opAnd64 (s.get a) (s.get b))
  | .orr d a b => s.set d (opOrr64 (s.get a) (s.get b))
  | .eor d a b => s.set d (opEor64 (s.get a) (s.get b))
  | .csel d a b c => s.set d (if c.holds s.cf then s.get a else s.get b)
  | .movz d imm16 => s.set d (BitVec.ofNat 64 (imm16 % 0x10000))
  | .movk d imm16 hw => s.set d (movkInsert (s.get d) imm16 hw)
  | .mov d a => s.set d (s.get a)
  | .lsr d a m => s.set d (opLsr64 (s.get a) m)
  | .lsl d a m => s.set d (opLsl64 (s.get a) m)

/-- `runBBlock`: a straight-line fold of `evalBInst` (the 64-bit analogue of
    `runABlock`). -/
def runBBlock (s : BState) : List BInst → BState
  | [] => s
  | i :: is => runBBlock (evalBInst s i) is

@[simp] theorem runBBlock_nil (s : BState) : runBBlock s [] = s := rfl

@[simp] theorem runBBlock_cons (s : BState) (i : BInst) (is : List BInst) :
    runBBlock s (i :: is) = runBBlock (evalBInst s i) is := rfl

/-! ### Differential-validation pins for the bignum/field ops

Unit witnesses for the new 64-bit ops; the integration witness is the
`bignum_add_p256` KAT (`ArmBignumKernel.addp256_kat`). -/

/-- `MUL`/`UMULH` pin: `0xffffffffffffffff² = 0xfffffffffffffffe_0000000000000001`
    so `MUL = 1` (low), `UMULH = 0xfffffffffffffffe` (high). -/
example : opMul (BitVec.allOnes 64) (BitVec.allOnes 64) = 1
    ∧ opUmulh (BitVec.allOnes 64) (BitVec.allOnes 64)
        = BitVec.ofNat 64 0xfffffffffffffffe := by native_decide

/-- `ADDS` carry-out pin: `(2⁶⁴-1) + 1` wraps to `0` and sets `C`. -/
example : addWithCarry (BitVec.allOnes 64) (1 : BitVec 64) false = (0, true) := by
  native_decide

/-- `SUBS` borrow pin: `0 - 1` underflows, result `0xff…ff`, `C = 0` (borrow). -/
example : subWithBorrow (0 : BitVec 64) (1 : BitVec 64) true
    = (BitVec.allOnes 64, false) := by native_decide

/-- `MOVK` pin: inserting `0xffff` into lane 3 (`LSL #48`) of `0x…0001` gives
    `0xffff000000000001` — one step of building a 64-bit reduction constant. -/
example :
    movkInsert (BitVec.ofNat 64 0x0000000000000001) 0xffff 3
      = BitVec.ofNat 64 0xffff000000000001 := by native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend
