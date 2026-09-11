/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

@[expose] public section

set_option autoImplicit false

/-!
# The secp256k1 field-multiply runBlock reduce, byte-completed with a `loadConsts` prologue

## The census gap this closes

The EC field-op path emits its Montgomery field multiply as
`EcFieldOpsFull.feMulFrameAtFull = feMulFrameAt (256×256 schoolbook product) ++
reduceStoreBlockMul`, where `reduceStoreBlockMul = emitMontRedc4Block ++
emitCondSubP ++ storeSlot4` reuses the two shipped reduce bricks from
`Curve4MontMulProvenEmit`. Both of those bricks *read* the prime-limb registers
`p0..p3` (`0xfffffffefffffc2f`, `0xffffffffffffffff × 3`) and the Montgomery
constant register `np` (`n' = 0xd838091dd2253531`) — **but nothing on the EC path
initialises them**. Only the standalone `Curve4MontMulProvenEmit.montMulProvenBlock`
carries a `loadConsts` prologue that materialises those constants. So the EC-path
reduce, taken in isolation, is not byte-executable: `emitCondSubP`'s trial
subtract compares against uninitialised `p0..p3`.

This module byte-completes that reduce. It assembles the **same** reduce bricks
the jacAdd multiply uses (`emitMontRedc4Block`, `emitCondSubP`, imported verbatim
from `Curve4MontMulProvenEmit`) but preceded by the `loadConsts` prologue, so the
reduce reads real prime-limb constants. The result is definitionally the proven
parametric block `montMulProvenBlock secp256k1LimbImms secp256k1NPrime`, hence
carries the same product/reduce cores (`emitProductBlock4`'s proven `runBlock =
x·y`; `emitMontRedcStep`'s proven per-word `runBlock`), the same MULX/ADX
legalisation, and the same verified spilling allocator. The constants land in the
`%rbp` spill frame (see the emitted `.s`), where the reduce's trial subtract reads
them.

## What is proved here

* `secpFeMulRunBlock_eq` — the completed block is definitionally the proven
  parametric `montMulProvenBlock` (so no new emit scaffolding is introduced;
  the reduce bricks are the EC-path ones).
* `loadConsts_secp_p_correct` — the `loadConsts` prologue, over `runBlock`, leaves
  `p0..p3` and `np` holding exactly the secp256k1 prime limbs and `n'`. This is
  the cheap prologue-const proof: the reduce that follows reads those
  constants. (The fused `montRedc4_runBlock` value proof is a SEPARATE task; this
  module is the bytes-side prerequisite only.)
* `secpLimbImms_pin` — pins the four modulus immediates to the secp256k1
  prime limbs.

## The byte-correctness gate (external, GMP)

`secpFeMulRunBlockAsm` renders the completed block to
`bench/bytes_direct_secp256k1_femul_runblock/gen/secp256k1_femul_runblock.s`
(symbol `secp256k1_femul_runblock`, System-V
`void secp256k1_femul_runblock(uint64_t *z, const uint64_t *x, const uint64_t *y)`).
Because the reduce divides out one `R = 2^256` (CIOS 4-limb Montgomery reduce),
the block computes the field multiply `z = x·y·R^{-1} mod p` — the exact
Montgomery-domain field product the Montgomery-form Jacobian add consumes. The KAT
(`bench/bytes_direct_secp256k1_femul_runblock/femul_runblock_kat.c`) checks it
byte-for-byte against an INDEPENDENT GMP `x·y·R^{-1} mod p` oracle over 300k
random pairs + corners (incl. `(p−1)²` and the `p−1`/`p−2` edges that straddle the
final conditional subtract). A runBlock-level *value* proof of the fused reduce is
a separate task.

**0 sorries.**
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcFeMulReduceComplete

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock (emitProductBlock4)

/-! ## 1. The completed block: EC-path reduce bricks + `loadConsts` prologue -/

/-- The completed secp256k1 field-multiply `runBlock` block. The reduce bricks
    `emitMontRedc4Block` and `emitCondSubP` are the *same* ones the EC-path
    `EcFieldOpsFull.reduceStoreBlockMul` uses; here they are preceded by the
    `loadConsts` prologue that materialises the prime limbs `p0..p3` and the
    Montgomery constant `np`, so the reduce reads real constants. -/
def secpFeMulRunBlock : List (JInstr 64) :=
  loadInputs
    ++ loadConsts secp256k1LimbImms secp256k1NPrime
    ++ clearAccs
    ++ emitProductBlock4 accNames xNames yNames hiName loName
    ++ emitMontRedc4Block
    ++ emitCondSubP
    ++ storeOutputs

/-- The completed block is definitionally the proven parametric Montgomery
    multiply block instantiated at secp256k1 — so it inherits its product/reduce
    cores, MULX/ADX legalisation, and spilling allocator unchanged. -/
theorem secpFeMulRunBlock_eq :
    secpFeMulRunBlock = montMulProvenBlock secp256k1LimbImms secp256k1NPrime := rfl

/-! ## 2. The modulus-immediate pin -/

/-- The four modulus immediates loaded by `loadConsts` are the secp256k1
    prime limbs `p = 2^256 − 2^32 − 977`: `p0 = 0xfffffffefffffc2f`,
    `p1 = p2 = p3 = 0xffffffffffffffff`. -/
theorem secpLimbImms_pin :
    secp256k1LimbImms.getD 0 0 = 0xfffffffefffffc2f ∧
    secp256k1LimbImms.getD 1 0 = 0xffffffffffffffff ∧
    secp256k1LimbImms.getD 2 0 = 0xffffffffffffffff ∧
    secp256k1LimbImms.getD 3 0 = 0xffffffffffffffff := by
  native_decide

/-! ## 3. The `loadConsts` prologue leaves `p0..p3`, `np` correct (over `runBlock`)

The reduce bricks read the prime-limb registers `p0..p3` and the Montgomery
constant `np`. This is the cheap prologue proof the census gap asks for: after the
`loadConsts` prologue, `runBlock` has those five registers holding exactly the
secp256k1 prime limbs and `n'` — so the trailing `emitMontRedc4Block ++
emitCondSubP` reads those constants, not uninitialised registers. -/

/-- After the `loadConsts` prologue, `p0..p3` hold the secp256k1 prime limbs and
    `np` holds `n' = 0xd838091dd2253531`, over `runBlock`. -/
theorem loadConsts_secp_p_correct (s : JState 64) :
    (runBlock s (loadConsts secp256k1LimbImms secp256k1NPrime)).get "p0"
        = BitVec.ofNat 64 (secp256k1LimbImms.getD 0 0)
      ∧ (runBlock s (loadConsts secp256k1LimbImms secp256k1NPrime)).get "p1"
        = BitVec.ofNat 64 (secp256k1LimbImms.getD 1 0)
      ∧ (runBlock s (loadConsts secp256k1LimbImms secp256k1NPrime)).get "p2"
        = BitVec.ofNat 64 (secp256k1LimbImms.getD 2 0)
      ∧ (runBlock s (loadConsts secp256k1LimbImms secp256k1NPrime)).get "p3"
        = BitVec.ofNat 64 (secp256k1LimbImms.getD 3 0)
      ∧ (runBlock s (loadConsts secp256k1LimbImms secp256k1NPrime)).get "np"
        = BitVec.ofNat 64 secp256k1NPrime := by
  simp only [loadConsts, pNames, npName, List.range, List.range.loop, List.map,
    List.getD_cons_zero, List.getD_cons_succ, List.cons_append, List.nil_append,
    runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval,
    JState.get_setReg_same, JState.get_setReg_other, ne_eq,
    not_false_eq_true, String.reduceEq, and_self]

/-! ## 4. The rendered leaf and its emit driver -/

/-- The completed block rendered as a System-V leaf `.s`, symbol
    `secp256k1_femul_runblock`. Reuses `Curve4MontMulProvenEmit.provenAsm`'s
    legalisation + spilling + printing pipeline. -/
def secpFeMulRunBlockAsm : String :=
  provenAsm "secp256k1_femul_runblock" secp256k1LimbImms secp256k1NPrime

/-- Emit driver: write the completed-block `.s` into the bytes-direct bench dir. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bytes_direct_secp256k1_femul_runblock/gen"
  IO.FS.writeFile
    "bench/bytes_direct_secp256k1_femul_runblock/gen/secp256k1_femul_runblock.s"
    secpFeMulRunBlockAsm
  IO.println
    "wrote bench/bytes_direct_secp256k1_femul_runblock/gen/secp256k1_femul_runblock.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcFeMulReduceComplete
