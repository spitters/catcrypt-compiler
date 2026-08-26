/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxBlockedPrototype

set_option autoImplicit false

/-!
# `BLOCK = 4` variant of the ADCX/ADOX/MULX `mpn_addmul_1`

**EXPERIMENTAL FILE.**  Companion to `Mpn.AddMul1AdxBlockedPrototype.lean`
(which pins `BLOCK = 8`).  Same structure, smaller block.

## Why a smaller block

The `BLOCK = 8` variant's per-iteration register live-set is the same 8-limb
ADX dual-chain the unrolled `n = 8` body uses:

    cy, zero, op, ap, b, cf, of                         (7 ABI / state regs)
  + r0..r7                                              (8 accumulator regs)
  + t0..t7, hi0..hi7, lo0..lo7                          (24 transient regs)
  = 39 u64 GPRs live per block

which fits jasminc's allocator alone but is uncomfortable in the
`mul_basecase` Cwhile cascade.  When the outer Cwhile schedules the blocked
addmul as a `Ccall` target, jasminc's register allocator has to thread
caller-saved registers (the column-iterator state — `op_col`, `bp_col`,
`col_left`, the cross-call carry) on top of the callee's per-block live-set.
At ~39 GPRs in-flight per call, the cross-call slack is tight; the v64-BEST
Cwhile cascade work has been observing intermittent spill/reload churn.

`BLOCK = 4` halves the transient block-local count:

    cy, zero, op, ap, b, cf, of                         (7 ABI / state regs)
  + r0..r3                                              (4 accumulator regs)
  + t0..t3, hi0..hi3, lo0..lo3                          (12 transient regs)
  = 23 u64 GPRs live per block

giving the outer cascade ~16 caller-saved GPRs of headroom (vs ~9 at
BLOCK=8).  Per-block accounting overhead increases (2× as many block
folds per `n` limbs), but the per-iteration cost of the inner block is
the same `MULX + ADCX + ADOX` triplet pattern as BLOCK=8 — so the per-limb
cost in the inner block is identical.

The Lean change is one-token: pin `BLOCK = 4` instead of `BLOCK = 8`.  All
the per-block-body builders (`adxLimbStepBlk`, `adxLoadOpLimbsBlk`, etc.)
in the parent `MpnAddMul1AdxBlockedPrototype` are already `BLOCK`-generic.

## Spec equivalence

The pure-functional spec is `mpnAddmul1` — same as the `BLOCK = 8` variant
and same as the limb-by-limb single-chain reference.  Block size is
purely an emit-level concern; it does NOT change what each per-limb step
computes.

## Emit support

`mpnAddMul1AdxBlocked4Fd numBlocks` emits a `.jazz` symbol
`mpn_addmul_1_adx_blk4_<n>` where `n = numBlocks · 4`.  The bench-side
support sizes are `n ∈ {16, 32, 64, 128}` (matching the BLOCK=8 file).

## Cross-call ABI

The `BLOCK = 4` body has the same ABI shape as the BLOCK=8 body:
parameters `(op, ap, b)`; cross-block carry through register `cy`.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxBlocked4Prototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxBlockedPrototype

/-! ## §1  Block parameter — pin BLOCK = 4 -/

/-- Block size in u64 limbs (BLOCK = 4 variant). -/
def BLOCK : Nat := 4

/-! ## §2  Pure-functional reference

Identical to the `BLOCK = 8` parent: this is just `mpnAddmul1`.  Block size
is an emit detail; it doesn't change the per-limb arithmetic. -/

/-- Pure-functional spec of the BLOCK=4 blocked variant.  Definitionally
    equal to `mpnAddmul1` and to `mpnAddMul1AdxBlockedPrototype.mpnAddmul1Adx_blocked`. -/
def mpnAddmul1Adx_blocked4 (out a : List (BitVec 64)) (b cy : BitVec 64) :
    List (BitVec 64) × BitVec 64 :=
  mpnAddmul1 out a b cy

/-- The BLOCK=4 spec equals the limb-by-limb reference (`rfl`). -/
theorem mpnAddmul1Adx_blocked4_eq_mpnAddmul1
    (out a : List (BitVec 64)) (b cy : BitVec 64) :
    mpnAddmul1Adx_blocked4 out a b cy = mpnAddmul1 out a b cy := rfl

/-- The BLOCK=4 spec equals the BLOCK=8 spec (`rfl`). -/
theorem mpnAddmul1Adx_blocked4_eq_blocked8
    (out a : List (BitVec 64)) (b cy : BitVec 64) :
    mpnAddmul1Adx_blocked4 out a b cy =
    Mpn.AddMul1AdxBlockedPrototype.mpnAddmul1Adx_blocked out a b cy := rfl

/-- Empty input. -/
theorem mpnAddmul1Adx_blocked4_nil (a : List (BitVec 64)) (b cy : BitVec 64) :
    mpnAddmul1Adx_blocked4 [] a b cy = ([], cy) := by
  simp [mpnAddmul1Adx_blocked4, mpnAddmul1]

/-- Spec inherited from `mpnAddmul1_spec`. -/
theorem mpnAddmul1Adx_blocked4_spec
    (out a : List (BitVec 64)) (hlen : out.length = a.length)
    (b cy : BitVec 64) :
    toNat (mpnAddmul1Adx_blocked4 out a b cy).1
      + (2 ^ 64) ^ a.length * (mpnAddmul1Adx_blocked4 out a b cy).2.toNat
    = toNat out + toNat a * b.toNat + cy.toNat := by
  rw [mpnAddmul1Adx_blocked4_eq_mpnAddmul1]
  exact mpnAddmul1_spec out a hlen b cy

/-- Concrete sanity: `n = 8` (two BLOCK=4 blocks). -/
example : (mpnAddmul1Adx_blocked4
    (List.replicate 8 (0 : BitVec 64))
    (List.replicate 8 (1 : BitVec 64))
    (5 : BitVec 64) (0 : BitVec 64)).1
    = List.replicate 8 (5 : BitVec 64) := by native_decide

/-- Concrete sanity: `n = 16` (four BLOCK=4 blocks). -/
example : (mpnAddmul1Adx_blocked4
    (List.replicate 16 (10 : BitVec 64))
    (List.replicate 16 (3 : BitVec 64))
    (4 : BitVec 64) (0 : BitVec 64)).1
    = List.replicate 16 (22 : BitVec 64) := by native_decide

/-! ## §3  The BLOCK=4 Jasmin body

We reuse the parent file's BLOCK-generic builders (`adxLimbStepBlk`,
`adxLoadOpLimbsBlk`, `adxStoreOpLimbsBlk`, `adxFinalFoldBlk`) verbatim;
only the BLOCK constant differs.  Per-block work:

```
xor of, cf, _, _, _, zero
for i = 0 to 4 { load r_i }                           # 4 loads
for i = 0 to 4 { load t_i; mulx; adcx; adox }        # 4 limb steps
adcx hi3, hi3, zero, cf                                # final fold cf
adox hi3, hi3, zero, of                                # final fold of
cy = hi3                                                # publish carry
for i = 0 to 4 { store r_i }                          # 4 stores
op += 32; ap += 32
```

Inner-block live-set: ~23 u64 GPRs.  Half the BLOCK=8 budget — gives the
outer Cwhile cascade ~16 caller-saved GPRs of headroom (vs ~9 at BLOCK=8). -/

/-- ADX dual-chain per-limb body for BLOCK=4.  Same as the parent
    `adxLimbStepBlk` (which is BLOCK-generic): the only block-size
    dependency is the `hiName (BLOCK - 1)` final fold below. -/
def adxLimbStepBlk4 (i : Nat) : List InstrR :=
  Mpn.AddMul1AdxBlockedPrototype.adxLimbStepBlk i

/-- Per-limb body with the input load interleaved. -/
def adxLimbFullBlk4 (i : Nat) : List InstrR :=
  Mpn.AddMul1AdxBlockedPrototype.adxLimbFullBlk i

/-- The block's unrolled BLOCK=4 limb sequence. -/
def adxLimbSeqBlk4 : Nat → List InstrR
  | 0     => []
  | n + 1 => adxLimbSeqBlk4 n ++ adxLimbFullBlk4 n

/-- Pre-load 4 op-limbs from `[op + 0 .. op + 24]`. -/
def adxLoadOpLimbsBlk4 : Nat → List InstrR
  | 0     => []
  | n + 1 => adxLoadOpLimbsBlk4 n ++ [load64Off (rName n) "op" (8 * Int.ofNat n)]

/-- Store the 4 r-limbs back to `[op + 0 .. op + 24]`. -/
def adxStoreOpLimbsBlk4 : Nat → List InstrR
  | 0     => []
  | n + 1 => adxStoreOpLimbsBlk4 n ++ [store64Off "op" (8 * Int.ofNat n) (rName n)]

/-- Final fold for one BLOCK=4 block.  Same idiom as the parent's
    `adxFinalFoldBlk` but at index `BLOCK - 1 = 3` instead of `7`. -/
def adxFinalFoldBlk4 : List InstrR :=
  [ adcxCopn "cf" (hiName (BLOCK - 1)) (hiName (BLOCK - 1)) "zero" "cf"
  , adoxCopn "of" (hiName (BLOCK - 1)) (hiName (BLOCK - 1)) "zero" "of"
  , .Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64)
      (.Pvar { gv := { var := vr (hiName (BLOCK - 1)) }, gs := false }) ]

/-- The per-block body for BLOCK=4. -/
def perBlockBody4 : List InstrR :=
  [ xorClearFlags "of" "cf" "zero" ]
  ++ adxLoadOpLimbsBlk4 BLOCK
  ++ adxLimbSeqBlk4 BLOCK
  ++ adxFinalFoldBlk4
  ++ adxStoreOpLimbsBlk4 BLOCK
  ++ [ binImm "op" (.Oadd .U64) (8 * Int.ofNat BLOCK)
     , binImm "ap" (.Oadd .U64) (8 * Int.ofNat BLOCK) ]

/-- The full BLOCK=4 blocked body for `n = numBlocks · BLOCK` limbs.

    Prologue: `cy := 0`; XOR-clear flags + zero scratch.
    Main: `Cfor i = 0 to numBlocks { perBlockBody4 }`. -/
def bodyAddMul1AdxBlocked4 (numBlocks : Nat) : List InstrR :=
  [ assignConst "cy" 0
  , xorClearFlags "of" "cf" "zero" ]
  ++ [ .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := numBlocks }
              perBlockBody4 ]

/-- The BLOCK=4 blocked function declaration. -/
def mpnAddMul1AdxBlocked4Fd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_addmul_1_adx_blk4_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "b" }⟩]
  body := bodyAddMul1AdxBlocked4 numBlocks
  results := []

/-- Carry-returning BLOCK=4 wrapper.  Same body, exposes `cy` as a result.
    Used by the mul_basecase Cwhile cascade as a `Ccall` target. -/
def mpnAddMul1AdxBlk4CyFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_addmul_1_adx_blk4_cy_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "b" }⟩]
  body := bodyAddMul1AdxBlocked4 numBlocks
  results := [{ var := vr "cy" }]

/-- Emitted `.jazz` for `n = 16` (numBlocks = 4). -/
def emitted16 : Option String := emitFunDecl (mpnAddMul1AdxBlocked4Fd 4)

/-- Emitted `.jazz` for `n = 32` (numBlocks = 8). -/
def emitted32 : Option String := emitFunDecl (mpnAddMul1AdxBlocked4Fd 8)

/-- Emitted `.jazz` for `n = 64` (numBlocks = 16). -/
def emitted64 : Option String := emitFunDecl (mpnAddMul1AdxBlocked4Fd 16)

/-- Emitted `.jazz` for `n = 128` (numBlocks = 32). -/
def emitted128 : Option String := emitFunDecl (mpnAddMul1AdxBlocked4Fd 32)

/-- All four emits are non-`none` (the AST is well-formed at every size). -/
example : emitted16.isSome := by native_decide
example : emitted32.isSome := by native_decide
example : emitted64.isSome := by native_decide
example : emitted128.isSome := by native_decide

/-- Carry-returning wrappers also emit. -/
example : (emitFunDecl (mpnAddMul1AdxBlk4CyFd 4)).isSome := by native_decide

/-- And via the `#[returnaddress=stack]` subroutine emit path. -/
example : (emitFunDeclRastack (mpnAddMul1AdxBlk4CyFd 4)).isSome := by native_decide

-- Diagnostic eyeball-check at n=16.
#eval match emitted16 with | some s => s | none => "EMIT FAILED"

/-! ## §4  Refinement statement (mirrors the BLOCK=8 parent)

For BLOCK=4 the refinement statement has the same shape as the BLOCK=8
file's `MpnAddMul1AdxBlockedRefinesStmt`, with `BLOCK = 4` in place of
`BLOCK = 8`.  Reduces to the same `mpnAddmul1` reference via the same
chain of equivalences.  The `numBlocks = 0` base case is proved directly;
the general case mirrors the BLOCK=8 parent's structural residual. -/

/-- Refinement statement for the BLOCK=4 emit at fixed `n = numBlocks · BLOCK`. -/
def MpnAddMul1AdxBlocked4RefinesStmt (numBlocks : Nat) : Prop :=
  ∀ (s : BignumState) (out as : List (BitVec 64)),
    out.length = numBlocks * BLOCK →
    as.length = numBlocks * BLOCK →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (numBlocks * BLOCK)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * (numBlocks * BLOCK))) →
    ∃ s', ∃ fuel, bignumExecFuel emptyRegistry fuel
            (bodyAddMul1AdxBlocked4 numBlocks) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnAddmul1Adx_blocked4 out as (s.regs "b") 0).1 ∧
      s'.regs "cy" = (mpnAddmul1Adx_blocked4 out as (s.regs "b") 0).2

/-- For `numBlocks = 0` the body executes `cy := 0; xor zero, zero; Cfor _ {0,0} _`
    and an empty Cfor unrolls to `[]`.  Output limbs are `[]` and `cy = 0`. -/
theorem bodyAddMul1AdxBlocked4_zero :
    bodyAddMul1AdxBlocked4 0 =
      [ assignConst "cy" 0
      , xorClearFlags "of" "cf" "zero"
      , .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := 0 } perBlockBody4 ] := by
  unfold bodyAddMul1AdxBlocked4
  rfl

/-- The BLOCK=4 variant at `numBlocks = 0`: empty output, zero carry. -/
theorem mpnAddmul1Adx_blocked4_zero (a : List (BitVec 64)) (b : BitVec 64) :
    mpnAddmul1Adx_blocked4 [] a b 0 = ([], 0) :=
  mpnAddmul1Adx_blocked4_nil a b 0

/-- `numBlocks = 0` base case for the BLOCK=4 refinement.  Mirrors
    the BLOCK=8 parent's `MpnAddMul1AdxBlockedJasminRefines_zero`. -/
theorem MpnAddMul1AdxBlocked4JasminRefines_zero :
    MpnAddMul1AdxBlocked4RefinesStmt 0 := by
  intro s out as hout has _ _ _
  have h0 : (0 : Nat) * BLOCK = 0 := by simp
  rw [h0] at hout has
  have hout_nil : out = [] := List.length_eq_zero_iff.mp hout
  have has_nil : as = [] := List.length_eq_zero_iff.mp has
  subst hout_nil
  subst has_nil
  have hSpecNil : mpnAddmul1Adx_blocked4 [] [] (s.regs "b") 0 = ([], 0) :=
    mpnAddmul1Adx_blocked4_nil [] (s.regs "b") 0
  refine ⟨setReg (setReg (setReg
            (setReg s "cy" 0) "of" 0) "cf" 0) "zero" 0, 8, ?_, ?_, ?_⟩
  · rw [bodyAddMul1AdxBlocked4_zero]
    simp only [bignumExecFuel, execInstr, evalPExpr, assignConst, xorClearFlags,
               vr, pv, unrollFor, bind, Option.bind, writeXorBundle,
               List.flatMap, List.range, List.range.loop, List.append_nil,
               List.map_nil, List.flatten_nil,
               show BitVec.ofInt 64 0 = (0 : BitVec 64) from rfl,
               show ((setReg s "cy" 0).regs "zero" ^^^
                     (setReg s "cy" 0).regs "zero" : BitVec 64) = 0 from by bv_decide]
  · rw [hSpecNil]
    simp [memHoldsLimbs]
  · rw [hSpecNil]
    simp [setReg]

/-! ## §5  Constant-time-shape (same as BLOCK=8) -/

example : perBlockBody4.all (fun i => match i with
    | .Cassgn _ _ _ _ => true
    | .Copn _ _ _ _ => true
    | _ => false) = true := by decide

/-- The outer BLOCK=4 body has exactly one Cfor (and two Cassgn/Copn
    pre-instructions). -/
example : (bodyAddMul1AdxBlocked4 4).length = 3 := by decide

end CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxBlocked4Prototype
