/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
public meta import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec

/-!
# Poseidon2 BabyBear — AVX-512 MDS add through the **verified jasmin chain**

[`Poseidon2Avx512.lean`](Poseidon2Avx512.lean) re-targets the Poseidon2
`VectorOp` lane ops to AVX-512 (`zmm`, 8×u64) via the `x86vector` MLIR
lowering, but its own docstring records the limitation that the *jasmin*
backend "cannot emit ZMM — its Rocq word model caps at U256". In this chain the
AST `WSize` carries `U512`, and the verified Jasmin VIR
dialect ([`JasminDialect.lean`](JasminDialect.lean)) carries a `vpackZMM` op —
the 8×u64 packed-lane register op (the verified-chain image of `#VPADD_8u64` /
`#VPSUB_8u64` / `#VPMULL_8u64` / `#VPSRL_8u64`).

This module routes **one** AVX-512 Poseidon2 lane op — the MDS / round-constant
linear-layer add (`#VPADD_8u64`) — end-to-end through the verified jasmin chain:

1. **A `Com jasminDialect` over two `reg 512` ZMM inputs** (`mdsAddZmmCom`) whose
   single op is `vpackZMM .add`. This is a closed program in the *verified*
   dialect (the one `JasminPrint` lowers and `JasminPrintSemCorrect` proves
   denotation-preserving), not the owned x86 backend.

2. **Differential validation** (`mdsAddZmm_eq_avx512_model`): the verified-chain
   `Com.denote` equals the AVX-512 functional model `denoteVPaddQ8` (8-lane packed
   u64 add, a model-free lane add over `zmmLane`) — definitionally the same
   per-lane add the AVX2 + ADX arms were validated against.

3. **Poseidon2 per-lane meaning** (`mdsAddZmm_eq_poseidon2_padd`): each lane of
   the verified-chain result is the Poseidon2 `padd` (`Poseidon2LaneVec.padd`) of
   the corresponding input lanes — the *same* per-lane add the AVX2 consumer
   chain has; only the lane count (8 vs 4) and emit width differ.

4. **The emitted `.jazz`** (`mdsAddZmm_jazz_has_*`): the chain prints a
   `reg u512` function whose body is the `#VPADD_8u64` intrinsic — the U512
   register type prints without truncation to `u256`.

5. **The store-threaded evaluator agrees** (`mdsAddZmm_runProg_eq`): running the
   *emitted instruction list* (`JasminPrintSemCorrect.runProg`) on the seeded
   parameter store computes the same packed add — the denotation-preservation
   theorem of the verified chain, instantiated at the ZMM op.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Avx512Jasmin`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Avx512Jasmin

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec (padd)

/-- Model-free 8-lane packed u64 add (the AVX-512 `VPADDQ zmm` functional model):
    lane `k` is `lane_k(a) + lane_k(b)` over the `zmmLane` (little-endian 64-bit)
    view, i.e. `vpaddq_lane = (· + ·)` on each `extractLsb'` lane. The model
    lives here, free of any machine backend. -/
def denoteVPaddQ8 (a b : BitVec 512) (k : Fin 8) : BitVec 64 :=
  zmmLane a k + zmmLane b k

/-! ## 0. ZMM lane round-trip (needs `BitVec` append/extract; kept here, where
    Mathlib is in scope — `JasminDialect`/`Core` is import-light). -/

/-- Reading lane `k` of an assembled ZMM register recovers the `k`-th lane
    function value: `zmmLane (zmmOfLanes f) k = f k`. The little-endian
    concatenation places `f k` at bits `[64k, 64k+64)`, which is exactly what
    `zmmLane` extracts. -/
theorem zmmOfLanes_zmmLane (f : Fin 8 → BitVec 64) (k : Fin 8) :
    zmmLane (zmmOfLanes f) k = f k := by
  fin_cases k <;>
    · apply BitVec.eq_of_getLsbD_eq
      intro i
      by_cases hi : i < 64
      · -- in range: exactly the matching lane's slice carries bit `i`.
        simp only [zmmLane, zmmOfLanes, Fin.isValue, BitVec.getLsbD_extractLsb',
          BitVec.getLsbD_append, decide_eq_true_eq.mpr hi, Bool.true_and,
          Nat.add_sub_cancel, Nat.mul_comm, Nat.zero_mul, Nat.zero_add,
          Nat.add_sub_cancel_left]
        split_ifs with h₀ h₁ h₂ h₃ h₄ h₅ h₆ <;>
          (intro _
           first
             | omega
             | exact congrArg _ (by omega : _ = i))
      · -- out of range (`i ≥ 64`): the `eq_of_getLsbD_eq` obligation carries the
        -- antecedent `i < 64`, which contradicts `hi`; the goal is vacuous.
        intro h
        exact absurd h hi

/-! ## 1. The verified-chain Poseidon2 MDS-add ZMM program -/

/-- The Poseidon2 MDS / RC-add linear-layer step as a closed `Com` in the
    **verified** Jasmin VIR dialect: two `reg 512` ZMM inputs, one `vpackZMM .add`
    op (8×u64 packed add, the `#VPADD_8u64` image), return the result. The
    De Bruijn args pick input 0 (`.here`) and input 1 (`.there .here`). -/
def mdsAddZmmCom : Com jasminDialect [.reg 512, .reg 512] (.reg 512) :=
  .var (.mk (.vpackZMM .add) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-! ## 2. Differential validation against the AVX-512 functional model

The verified-chain denotation of the program is the dialect's `zmmPackQ .add`,
which is *definitionally* the 8-lane packed add. We pin it equal to the
model-free AVX-512 model `denoteVPaddQ8` (above). Lane `k` of either side is
`lane_k(a) + lane_k(b)` over the same `zmmLane` (`extractLsb'`) view. -/

/-- The verified-chain `Com.denote` of `mdsAddZmmCom` is the dialect ZMM packed
    add. -/
theorem mdsAddZmm_denote (a b : BitVec 512) :
    mdsAddZmmCom.denote (.cons a (.cons b .nil)) = zmmPackQ .add a b := rfl

/-- **Differential validation.** Each lane of the verified-chain result equals
    the corresponding lane of the AVX-512 functional model `denoteVPaddQ8`
    (8-way packed u64 add). Both lanes are the `zmmLane` `extractLsb'` view, and
    the lane op is `+` on both sides. -/
theorem mdsAddZmm_eq_avx512_model (a b : BitVec 512) (k : Fin 8) :
    zmmLane (mdsAddZmmCom.denote (.cons a (.cons b .nil))) k
      = denoteVPaddQ8 a b k := by
  rw [mdsAddZmm_denote]
  show zmmLane (zmmOfLanes _) k = _
  rw [zmmOfLanes_zmmLane]
  rfl

/-! ## 3. Poseidon2 per-lane meaning

The Poseidon2 consumer (`Poseidon2LaneVec`) uses `padd x y = x + y` per lane.
Each lane of the verified-chain ZMM add is exactly that — the same scalar add
the AVX2 4-lane chain carries, over 8 lanes. -/

/-- **Poseidon2 lane meaning.** Lane `k` of the verified-chain MDS-add result is
    the Poseidon2 `padd` of the input lanes. The verified jasmin chain realizes
    the *same* per-lane semantics as the Poseidon2 abstract `VectorOp.add padd`,
    only over 8 `zmm` lanes. -/
theorem mdsAddZmm_eq_poseidon2_padd (a b : BitVec 512) (k : Fin 8) :
    zmmLane (mdsAddZmmCom.denote (.cons a (.cons b .nil))) k
      = padd (zmmLane a k) (zmmLane b k) := by
  rw [mdsAddZmm_denote]
  show zmmLane (zmmOfLanes _) k = _
  rw [zmmOfLanes_zmmLane]
  rfl

/-! ## 4. The emitted `.jazz`: a `reg u512` function over `#VPADD_8u64` -/

/-- The emitted `.jazz` text contains the `#VPADD_8u64` packed-add mnemonic. -/
theorem mdsAddZmm_jazz_has_vpadd8 :
    ((JasminPrint.emitJazz "poseidon2_mds_add_zmm" mdsAddZmmCom).splitOn "#VPADD_8u64").length
      ≥ 2 := by native_decide

/-- The emitted `.jazz` text declares a `u512` register (the ZMM register type
    prints; a `reg 512` does not saturate to `u256`). -/
theorem mdsAddZmm_jazz_has_u512 :
    ((JasminPrint.emitJazz "poseidon2_mds_add_zmm" mdsAddZmmCom).splitOn "u512").length
      ≥ 2 := by native_decide

/-! ## 5. The store-threaded evaluator (emitted-instruction semantics) agrees

`JasminPrintSemCorrect.runProg` seeds the parameter store and runs the *emitted*
instruction list. By the verified chain's denotation-preservation theorem
(`lowerComToProg_sem_eq`), it computes `Com.denote com V` for the ZMM packed
add, given the standard side conditions (leaf agreement — vacuous, no `extCall`;
fresh-name and parameter-name injectivity). -/

/-- The free context of the demonstrator: two `reg 512` ZMM inputs. -/
abbrev zmmCtx : Ctxt jasminDialect := [JasminTy.reg 512, JasminTy.reg 512]

/-- `mdsAddZmmCom` is straight-line: its single binder (`vpackZMM .add`) is not a
    `stackStore`. -/
theorem mdsAddZmmCom_straightLine :
    JasminPrintSemCorrect.StraightLine mdsAddZmmCom := by
  refine ⟨?_, trivial⟩
  intro w n h
  exact absurd h (by simp [mdsAddZmmCom])

/-- **Denotation preservation through the emitted instructions.** For any leaf
    semantics agreeing with `jasminExtSem`, injective fresh-name and parameter
    resolvers, running the emitted MDS-add program (`runProg`) on the seeded
    parameter store computes the same value as `Com.denote V`. Instantiates
    `JasminPrintSemCorrect.lowerComToProg_sem_eq` at the ZMM `vpackZMM .add`
    program. -/
theorem mdsAddZmm_runProg_eq {leafSem : JasminPrintSemCorrect.LeafSem}
    (hLeaf : JasminPrintSemCorrect.LeafAgrees leafSem)
    (hInj : Function.Injective JasminPrintSemCorrect.freshName)
    (hPinj : ∀ (t t' : jasminDialect.Ty)
                (v : Ctxt.Var zmmCtx t) (v' : Ctxt.Var zmmCtx t'),
                (JasminPrint.paramsAndMap zmmCtx).2 t v
                  = (JasminPrint.paramsAndMap zmmCtx).2 t' v' →
                (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation zmmCtx) :
    JasminPrintSemCorrect.runProg leafSem mdsAddZmmCom V = mdsAddZmmCom.denote V :=
  JasminPrintSemCorrect.lowerComToProg_sem_eq hLeaf hInj mdsAddZmmCom
    mdsAddZmmCom_straightLine hPinj V

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Avx512Jasmin
