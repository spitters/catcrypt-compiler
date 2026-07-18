/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnMulBaseCaseAdxCwhilePrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnAddMul1AdxBlocked4Prototype

set_option autoImplicit false

/-!
# Runtime-`Cwhile` schoolbook with `BLOCK = 4` callee + `#[returnaddress=stack]`

**EXPERIMENTAL FILE.**  Companion to `MpnMulBaseCaseAdxCwhilePrototype.lean`
(the BLOCK=8 attempt that jasminc rejected at every supported `n`) and
`MpnAddMul1AdxBlocked4Prototype.lean` (the just-landed BLOCK=4 ADCX/ADOX/MULX
addmul kernel with ~half the per-block GPR pressure of BLOCK=8).

## Motivation

The BLOCK=8 Cwhile cascade
(`MpnMulBaseCaseAdxCwhilePrototype.mpnMulBasecaseAdxCwhileFd`) emits well-
formed `.jazz` at every `n ∈ {16, 32, 64, 128}` but jasminc rejects it: the
caller's loop-locals (`op_col`, `bp_col`, `col_left`, `ap_base`, `rp_base`,
`bp`, `zero`) plus the callee's per-block live-set (~39 u64 GPRs at BLOCK=8)
together exceed the x86-64 GPR budget across the `Ccall` boundary, even with
the callee declared `#[returnaddress=stack]` (no-inline).

The fix combines **three** just-landed lowerings:

1. **`BLOCK = 4` callee**
   (`MpnAddMul1AdxBlocked4Prototype.mpnAddMul1AdxBlk4CyFd`) — halves the
   per-block transient register count to ~23 GPRs.
2. **`#[returnaddress=stack]` callee emit**
   (`Emit.emitFunDeclRastack` / `Emit.FnKind.SubroutineRastack`) — forces
   jasminc NOT to inline the callee at the `Ccall` site, so the caller's
   loop-local live-set doesn't compound with the callee's per-block live-
   set into one fused allocation problem.
3. **Outer `Cwhile`** — the runtime loop reuses one physical register bank
   per column iteration, instead of the meta-unroll's `n` independent
   per-column SSA banks.

Expected: at `n = 16, 32, 64` the post-patched non-inlined `.jazz` should
now slot into x86-64's 16 GPRs across the call boundary; `n = 128` is
borderline depending on the caller's loop-local count.

## What this file proves

Identical shape to `MpnMulBaseCaseAdxCwhilePrototype`, swapping the inner
addmul callee from BLOCK=8 to BLOCK=4:

1. **Pure functional reference** `mpnMulBasecaseAdxCwhile4` (§2),
   definitionally equal to `mpnMul a b`.
2. **`FunDecl` and `.jazz` emission** (§3, §4): one
   `mpn_addmul_1_adx_blk4_cy_<n>` (carry-returning BLOCK=4 wrapper) and one
   `mpn_mul_basecase_adx_cwhile4_<n>` (outer Cwhile schoolbook) symbol per
   `n ∈ {16, 32, 64, 128}`.
3. **Refinement statement** (§5): the `n = 0` case proved directly by
   symbolic evaluation of the empty Cwhile prologue.
4. **General-`n` reduction**: the per-column step obligation, recorded as
   a `Prop`-level residual in the same style as the BLOCK=8 file.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnMulBaseCaseAdxCwhile4Prototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAddmul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAddMul1AdxPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAddMul1AdxBlockedPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAddMul1AdxBlocked4Prototype

/-! ## §1  Block parameter — BLOCK = 4 -/

/-- Same block size as the BLOCK=4 addmul kernel:
    `MpnAddMul1AdxBlocked4Prototype.BLOCK = 4`. -/
def CW4_BLOCK : Nat := MpnAddMul1AdxBlocked4Prototype.BLOCK

theorem cw4_block_eq_four : CW4_BLOCK = 4 := rfl

/-! ## §2  Pure functional reference

The runtime-Cwhile schoolbook computes the same `mpnMul a b` product
regardless of the inner addmul block size — block size is an emit detail. -/

/-- Pure-functional spec of the BLOCK=4 runtime-Cwhile schoolbook: identical
    to `mpnMul`.  Definitionally equal to every other multiplication-spec
    variant in the project. -/
def mpnMulBasecaseAdxCwhile4 (a b : List (BitVec 64)) : List (BitVec 64) :=
  mpnMul a b

/-- The BLOCK=4 Cwhile spec equals the limb-by-limb reference (`rfl`). -/
theorem mpnMulBasecaseAdxCwhile4_eq_mpnMul (a b : List (BitVec 64)) :
    mpnMulBasecaseAdxCwhile4 a b = mpnMul a b := rfl

/-- The BLOCK=4 Cwhile spec equals the BLOCK=8 Cwhile spec (`rfl`). -/
theorem mpnMulBasecaseAdxCwhile4_eq_cwhile8 (a b : List (BitVec 64)) :
    mpnMulBasecaseAdxCwhile4 a b =
    MpnMulBaseCaseAdxCwhilePrototype.mpnMulBasecaseAdxCwhile a b := rfl

/-- Width: outputs exactly `|a| + |b|` limbs. -/
theorem mpnMulBasecaseAdxCwhile4_length (a b : List (BitVec 64)) :
    (mpnMulBasecaseAdxCwhile4 a b).length = a.length + b.length :=
  mpnMul_length a b

/-- **Main correctness** for the BLOCK=4 runtime-Cwhile schoolbook: the full
    schoolbook product equals `a · b` over `Nat`. -/
theorem mpnMulBasecaseAdxCwhile4_toNat (a b : List (BitVec 64)) :
    toNat (mpnMulBasecaseAdxCwhile4 a b) = toNat a * toNat b :=
  mpnMul_toNat a b

/-! ### Concrete sanity checks -/

/-- 2-limb × 2-limb sanity. -/
example : mpnMulBasecaseAdxCwhile4 [3, 0] [2, 0] = [6, 0, 0, 0] := by native_decide

/-- Carry propagation: `[2^63,0]² = [0, 2^62, 0, 0]`. -/
example : mpnMulBasecaseAdxCwhile4 [BitVec.ofNat 64 (2 ^ 63), 0]
    [BitVec.ofNat 64 (2 ^ 63), 0] = [0, BitVec.ofNat 64 (2 ^ 62), 0, 0] := by
  native_decide

/-! ## §3  Carry-returning BLOCK=4 addmul (Ccall callee)

We reuse the just-landed `mpnAddMul1AdxBlk4CyFd` from the BLOCK=4 parent.
Its body is `bodyAddMul1AdxBlocked4 numBlocks` (the BLOCK=4 generic body)
and it exposes `cy` as a single-result return value, matching the Ccall
ABI of the outer Cwhile schoolbook. -/

/-- The carry-returning BLOCK=4 callee.  Its name encodes
    `n = numBlocks · BLOCK` (BLOCK = 4 here). -/
theorem mpnAddMul1AdxBlk4CyFd_name (numBlocks : Nat) :
    (mpnAddMul1AdxBlk4CyFd numBlocks).name.name =
    "mpn_addmul_1_adx_blk4_cy_" ++
      toString (numBlocks * MpnAddMul1AdxBlocked4Prototype.BLOCK) := rfl

/-- The BLOCK=4 carry-returning wrapper shares its body with the void
    BLOCK=4 variant. -/
theorem mpnAddMul1AdxBlk4CyFd_body_eq (numBlocks : Nat) :
    (mpnAddMul1AdxBlk4CyFd numBlocks).body =
    (mpnAddMul1AdxBlocked4Fd numBlocks).body := rfl

/-! ## §4  The runtime-`Cwhile` schoolbook body

Identical control structure to the BLOCK=8 file, but the Ccall target name
references the BLOCK=4 callee (`mpn_addmul_1_adx_blk4_cy_<n>`). -/

/-- The per-iteration body of the BLOCK=4 runtime-Cwhile schoolbook. -/
def perColumnCwhile4Body (numBlocks : Nat) : List InstrR :=
  let n := numBlocks * CW4_BLOCK
  -- Load b[col] into the Ccall arg register `b`.
  [ .Cassgn (.Lvar { var := vr "b" }) .AT_none (.sword .U64)
      (.Pload .U64 { var := vr "bp_col" } (.Pconst 0))
  -- Setup Ccall args: op := op_col; ap := ap_base.
  , .Cassgn (.Lvar { var := vr "op" }) .AT_none (.sword .U64)
      (pv "op_col")
  , .Cassgn (.Lvar { var := vr "ap" }) .AT_none (.sword .U64)
      (pv "ap_base")
  -- BLOCK=4 addmul Ccall: cy_col = mpn_addmul_1_adx_blk4_cy_<n>(op, ap, b).
  , .Ccall .DoNotInline
      [.Lvar { var := vr "cy_col" }]
      { name := "mpn_addmul_1_adx_blk4_cy_" ++ toString n }
      [ pv "op", pv "ap", pv "b" ]
  -- Store column carry-out at r[col + n] = op_col + 8·n.
  , .Cassgn (.Lmem .U64 { var := vr "op_col" } (.Pconst (8 * Int.ofNat n)))
      .AT_none (.sword .U64) (pv "cy_col")
  -- Advance the column pointers and decrement the counter.
  , binImm "op_col"   (.Oadd .U64) 8
  , binImm "bp_col"   (.Oadd .U64) 8
  , binImm "col_left" (.Osub .U64) 1 ]

/-- Pre-zero `2n` result limbs at `[rp_base + 0..2n)`. -/
def initResultMemZeroCw4 : Nat → List InstrR
  | 0     => []
  | k + 1 => initResultMemZeroCw4 k ++
             [ store64Off "rp_base" (8 * Int.ofNat k) "zero" ]

/-- **The full BLOCK=4 runtime-Cwhile schoolbook body** for
    `n = numBlocks · BLOCK` columns.

    Prologue: clear flags and zero scratch; pre-zero `2n` result limbs;
    set up `op_col := rp_base`, `bp_col := bp`, `col_left := n`.

    Main: `while (col_left != 0) { perColumnCwhile4Body }`. -/
def bodyMulBasecaseCwhile4 (numBlocks : Nat) : List InstrR :=
  let n := numBlocks * CW4_BLOCK
  [ xorClearFlags "of" "cf" "zero" ]
  ++ initResultMemZeroCw4 (2 * n)
  ++ [ .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
          (pv "rp_base")
     , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
          (pv "bp")
     , assignConst "col_left" (Int.ofNat n) ]
  ++ [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
              (perColumnCwhile4Body numBlocks) ]

/-- The BLOCK=4 runtime-Cwhile `mpn_mul_basecase_adx_cwhile4_<n>` FunDecl. -/
def mpnMulBasecaseAdxCwhile4Fd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_mul_basecase_adx_cwhile4_"
                 ++ toString (numBlocks * CW4_BLOCK) }
  params := [⟨{ var := vr "rp_base" }⟩, ⟨{ var := vr "ap_base" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodyMulBasecaseCwhile4 numBlocks
  results := []

/-! ## §5  `.jazz` emission

The BLOCK=4 callee is emitted via `emitFunDeclRastack` — the
just-landed `FnKind.SubroutineRastack` path — which prepends
`#[returnaddress=stack]\nfn ` to the callee declaration.  This forces
jasminc NOT to inline the callee at the `Ccall` site, which is necessary
for the caller's loop-locals NOT to compound with the callee's per-block
live-set across the call boundary. -/

/-- Emit the carry-returning BLOCK=4 callee with `#[returnaddress=stack]`. -/
def emitAddmul4Cy (numBlocks : Nat) : Option String :=
  emitFunDeclRastack (mpnAddMul1AdxBlk4CyFd numBlocks)

/-- Emit the BLOCK=4 runtime-Cwhile schoolbook caller as `export fn`. -/
def emitMulCwhile4 (numBlocks : Nat) : Option String :=
  emitFunDecl (mpnMulBasecaseAdxCwhile4Fd numBlocks)

/-- Emit both functions concatenated into one `.jazz` file: the
    `#[returnaddress=stack]` BLOCK=4 callee followed by the `export fn`
    Cwhile caller. -/
def emitMulCwhile4Pair (numBlocks : Nat) : Option String := do
  let calleeStr ← emitAddmul4Cy numBlocks
  let callerStr ← emitMulCwhile4 numBlocks
  some (calleeStr ++ "\n" ++ callerStr)

/-- Emit n=16 (numBlocks = 4). -/
def emittedCwhile4_16 : Option String := emitMulCwhile4Pair 4

/-- Emit n=32 (numBlocks = 8). -/
def emittedCwhile4_32 : Option String := emitMulCwhile4Pair 8

/-- Emit n=64 (numBlocks = 16). -/
def emittedCwhile4_64 : Option String := emitMulCwhile4Pair 16

/-- Emit n=128 (numBlocks = 32). -/
def emittedCwhile4_128 : Option String := emitMulCwhile4Pair 32

example : emittedCwhile4_16.isSome := by native_decide
example : emittedCwhile4_32.isSome := by native_decide
example : emittedCwhile4_64.isSome := by native_decide
example : emittedCwhile4_128.isSome := by native_decide

/-! ## §6  Registry for the Ccall

The Cwhile body's Ccall target `mpn_addmul_1_adx_blk4_cy_<n>` resolves
through a registry mapping the function name to `mpnAddMul1AdxBlk4CyFd`. -/

/-- Registry resolving `mpn_addmul_1_adx_blk4_cy_<n>` for fixed
    `numBlocks`.  Other names resolve through `emptyRegistry` (i.e. fail). -/
def cwhile4Registry (numBlocks : Nat) : BignumRegistry := fun name =>
  let target :=
    "mpn_addmul_1_adx_blk4_cy_" ++ toString (numBlocks * CW4_BLOCK)
  if name = target then some (mpnAddMul1AdxBlk4CyFd numBlocks)
  else none

theorem cwhile4Registry_lookup (numBlocks : Nat) :
    cwhile4Registry numBlocks
      ("mpn_addmul_1_adx_blk4_cy_" ++ toString (numBlocks * CW4_BLOCK))
    = some (mpnAddMul1AdxBlk4CyFd numBlocks) := by
  simp [cwhile4Registry]

/-! ## §7  Refinement statement and the `n = 0` base case -/

/-- Refinement statement for the BLOCK=4 runtime-Cwhile schoolbook emit at
    fixed `n = numBlocks · BLOCK`.  Memory contract: `rp_base`, `ap_base`,
    `bp` point to pairwise-disjoint `2n`, `n`, `n`-limb regions. -/
def MpnMulBasecaseAdxCwhile4RefinesStmt (numBlocks : Nat) : Prop :=
  ∀ (s : BignumState) (rin a b : List (BitVec 64)),
    rin.length = 2 * (numBlocks * CW4_BLOCK) →
    a.length = numBlocks * CW4_BLOCK →
    b.length = numBlocks * CW4_BLOCK →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "rp_base").toNat) rin →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap_base").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp_base").toNat)
                         (8 * (2 * (numBlocks * CW4_BLOCK))))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap_base").toNat)
                         (8 * (numBlocks * CW4_BLOCK))) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp_base").toNat)
                         (8 * (2 * (numBlocks * CW4_BLOCK))))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat)
                         (8 * (numBlocks * CW4_BLOCK))) →
    ∃ s', ∃ fuel, bignumExecFuel (cwhile4Registry numBlocks) fuel
            (bodyMulBasecaseCwhile4 numBlocks) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp_base").toNat)
        (mpnMulBasecaseAdxCwhile4 a b)

/-- For `numBlocks = 0` the body is just the XOR-clear, the three
    pointer/counter setup assignments, and an immediate-exit Cwhile. -/
theorem bodyMulBasecaseCwhile4_zero :
    bodyMulBasecaseCwhile4 0 =
      [ xorClearFlags "of" "cf" "zero"
      , .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
          (pv "rp_base")
      , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
          (pv "bp")
      , assignConst "col_left" 0
      , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
              (perColumnCwhile4Body 0) ] := by
  unfold bodyMulBasecaseCwhile4 initResultMemZeroCw4
  rfl

/-- `mpnMul [] [] = []`. -/
theorem mpnMul_nil_nil_cw4 : mpnMul ([] : List (BitVec 64)) [] = [] := by
  simp [mpnMul]

/-- `mpnMulBasecaseAdxCwhile4 [] [] = []`. -/
theorem mpnMulBasecaseAdxCwhile4_nil_nil :
    mpnMulBasecaseAdxCwhile4 ([] : List (BitVec 64)) [] = [] :=
  mpnMul_nil_nil_cw4

set_option linter.unusedSimpArgs false in
/-- **`numBlocks = 0` base case** for the BLOCK=4 runtime-Cwhile refinement.

    At `numBlocks = 0` both operands are `[]` (length `0 * BLOCK = 0`),
    so `mpnMul [] [] = []` and `memHoldsLimbs … []` is vacuous.  The body
    executes the same XOR-clear + 3 setup-Cassgns + immediate-exit Cwhile
    as the BLOCK=8 file's `MpnMulBasecaseAdxCwhileJasminRefines_zero`. -/
theorem MpnMulBasecaseAdxCwhile4JasminRefines_zero :
    MpnMulBasecaseAdxCwhile4RefinesStmt 0 := by
  intro s rin a b _ ha hb _ _ _ _ _
  have h0 : (0 : Nat) * CW4_BLOCK = 0 := by simp
  rw [h0] at ha hb
  have ha_nil : a = [] := List.length_eq_zero_iff.mp ha
  have hb_nil : b = [] := List.length_eq_zero_iff.mp hb
  subst ha_nil; subst hb_nil
  rw [bodyMulBasecaseCwhile4_zero]
  set sPrologue : BignumState :=
    setReg (setReg (setReg
      (setReg (setReg (setReg s "of" 0) "cf" 0) "zero" 0)
      "op_col" (s.regs "rp_base"))
      "bp_col" (s.regs "bp"))
      "col_left" 0
  refine ⟨sPrologue, 8, ?_, ?_⟩
  · have hZeroXor : (s.regs "zero" ^^^ s.regs "zero" : BitVec 64) = 0 := by bv_decide
    have hOfInt0 : BitVec.ofInt 64 0 = (0 : BitVec 64) := rfl
    -- Step 1: the 4 straight-line prologue instructions evaluate to sPrologue.
    have hPrologue :
        bignumExecFuel (cwhile4Registry 0) 8
          [ xorClearFlags "of" "cf" "zero"
          , .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
              (pv "rp_base")
          , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
              (pv "bp")
          , assignConst "col_left" 0 ] s = some sPrologue := by
      simp only [bignumExecFuel, execInstr, evalPExpr, xorClearFlags, vr, pv,
                 assignConst, bind, Option.bind, writeXorBundle, hOfInt0, hZeroXor,
                 sPrologue, setReg_regs, setReg_mem, String.reduceEq, ↓reduceIte,
                 if_true, if_false]
    -- Step 2: at sPrologue, col_left = 0, so the Cwhile exits unchanged.
    have hColLeftZero : sPrologue.regs "col_left" = 0 := by
      simp [sPrologue, setReg]
    have hCondFalse :
        evalPExpr sPrologue
          (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0)) = some 0 := by
      simp [evalPExpr, pv, vr, hColLeftZero, hOfInt0]
    have hLoopExit :
        bignumExecFuel (cwhile4Registry 0) 8
          [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
                  (perColumnCwhile4Body 0) ] sPrologue = some sPrologue := by
      have := bignumExecFuel_loop_exit (cwhile4Registry 0) 5
                (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
                (perColumnCwhile4Body 0) sPrologue hCondFalse
      simpa using this
    -- Step 3: combine via append_join. The prologue's 4 instructions are
    -- all non-control (Cassgn / Copn). The full body is prologue ++ [Cwhile].
    have hNc : ∀ i ∈ [ xorClearFlags "of" "cf" "zero"
                     , .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
                         (pv "rp_base")
                     , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
                         (pv "bp")
                     , assignConst "col_left" 0 ], i.isNonControl := by
      intro i hi
      simp only [xorClearFlags, assignConst, List.mem_cons, List.not_mem_nil,
                 or_false] at hi
      rcases hi with h | h | h | h
      · subst h; exact True.intro
      · subst h; exact True.intro
      · subst h; exact True.intro
      · subst h; exact True.intro
    have :
        bignumExecFuel (cwhile4Registry 0) 8
          ([ xorClearFlags "of" "cf" "zero"
           , .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
              (pv "rp_base")
           , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
              (pv "bp")
           , assignConst "col_left" 0 ] ++
           [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
                  (perColumnCwhile4Body 0) ]) s = some sPrologue :=
      bignumExecFuel_append_join (cwhile4Registry 0) 8 _ _ hNc s sPrologue sPrologue
        hPrologue hLoopExit
    simpa using this
  · rw [mpnMulBasecaseAdxCwhile4_nil_nil]
    simp [memHoldsLimbs]

/-! ### Structural mirror to the BLOCK=8 bridge -/

/-- **General-`n` refinement claim (structural mirror).** -/
theorem MpnMulBasecaseAdxCwhile4JasminRefines_holds_n0 :
    MpnMulBasecaseAdxCwhile4RefinesStmt 0 :=
  MpnMulBasecaseAdxCwhile4JasminRefines_zero

/-! ## §8  Per-column step obligation

Identical shape to the BLOCK=8 file's `PerColumnCwhileBodyRefines`, with
the BLOCK=4 callee name in place of the BLOCK=8 one. -/

/-- **Per-column step obligation** for the BLOCK=4 runtime-Cwhile body.
    Structurally a single application of
    `MpnAddMul1AdxBlocked4JasminRefines` (the BLOCK=4 parent's
    general-`numBlocks` statement), wrapped in the Ccall ABI plumbing. -/
def PerColumnCwhile4BodyRefines (numBlocks : Nat) : Prop :=
  ∀ (s : BignumState) (outWin asWin : List (BitVec 64)) (bCol : BitVec 64),
    outWin.length = numBlocks * CW4_BLOCK →
    asWin.length = numBlocks * CW4_BLOCK →
    s.regs "b" = bCol →
    s.regs "zero" = 0 →
    s.regs "col_left" ≠ 0 →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op_col").toNat) outWin →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap_base").toNat) asWin →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op_col").toNat)
                         (8 * (numBlocks * CW4_BLOCK + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap_base").toNat)
                         (8 * (numBlocks * CW4_BLOCK))) →
    ∃ s', ∃ fuel,
      bignumExecFuel (cwhile4Registry numBlocks) fuel
        (perColumnCwhile4Body numBlocks) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op_col").toNat)
        ((mpnAddmul1 outWin asWin bCol 0).1 ++
         [(mpnAddmul1 outWin asWin bCol 0).2]) ∧
      s'.regs "op_col" = s.regs "op_col" + BitVec.ofNat 64 8 ∧
      s'.regs "bp_col" = s.regs "bp_col" + BitVec.ofNat 64 8 ∧
      s'.regs "col_left" = s.regs "col_left" - 1 ∧
      s'.regs "ap_base" = s.regs "ap_base"

/-! ### §8.1  Per-step composition obligation -/

/-- **Counter-induction step obligation** for the BLOCK=4 Cwhile body. -/
def MpnMulBasecaseAdxCwhile4JasminRefines_step_obligation : Prop :=
  ∀ numBlocks,
    PerColumnCwhile4BodyRefines numBlocks →
    MpnMulBasecaseAdxCwhile4RefinesStmt numBlocks

/-! ### §8.2  General-`numBlocks` refinement, modulo the per-column residual -/

/-- **General-`numBlocks` refinement, modulo the per-column operational
    residual and the counter-induction obligation.** -/
theorem MpnMulBasecaseAdxCwhile4JasminRefines
    (hStep : MpnMulBasecaseAdxCwhile4JasminRefines_step_obligation)
    (hCol : ∀ k, PerColumnCwhile4BodyRefines k)
    (numBlocks : Nat) :
    MpnMulBasecaseAdxCwhile4RefinesStmt numBlocks :=
  hStep numBlocks (hCol numBlocks)

/-! ## §9  Constant-time-shape

Same shape as the BLOCK=8 file: exactly one runtime control-flow node
(the outer Cwhile on `col_left != 0`); the per-column body is 8
straight-line `Cassgn`/`Copn`/`Ccall` instructions. -/

/-- The per-column body has exactly one Ccall (plus 7 other instructions:
    3 setup Cassgns + 1 carry store + 3 pointer/counter updates). -/
example : (perColumnCwhile4Body 4).length = 8 := by decide

/-- The full body at `numBlocks = 0` reduces to 5 instructions: prologue
    (XOR + 3 setup) + Cwhile. -/
example : (bodyMulBasecaseCwhile4 0).length = 5 := by decide

/-- The outer Cwhile is in the canonical `(col_left != 0)` shape. -/
example : ∃ body,
    (bodyMulBasecaseCwhile4 0).getLast? = some
      (.Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0)) body) :=
  ⟨perColumnCwhile4Body 0, rfl⟩

/-! ## §10  Axiom check -/

#print axioms MpnMulBasecaseAdxCwhile4JasminRefines_zero
#print axioms mpnMulBasecaseAdxCwhile4_toNat

end CatCrypt.Crypto.Jasmin.Examples.MpnMulBaseCaseAdxCwhile4Prototype
