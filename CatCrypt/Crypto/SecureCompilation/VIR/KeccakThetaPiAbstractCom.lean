/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom
public import CatCrypt.Crypto.Primitives.Keccak
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.BitVec

/-!
# Abstract FIPS-202 θ/π ties for the unified-`Com` Keccak block (model-free)

`KeccakThetaPiCom.lean` migrated the cross-lane Keccak θ/π SIMD block off the
bespoke `Avx512Model` (`ZInstr`/`ZState`/`runZBlock`) machine onto the unified
`Com jasminDialect`, and pinned the denotations of `parityCom`/`dCom`/`piCom` to
packed `zmmPackQ` (8×u64) expressions over `BitVec 512` — but it stopped at the
packed-`BitVec` level: it does NOT tie those packed expressions back to the
abstract FIPS-202 spec `Primitives.Keccak.theta` / `pi`.

The bespoke realization `KeccakThetaPiRealization.lean` *does* carry those
abstract ties (`paritySpec_eq_abstract_C`, `dSpec_lane_eq_abstract_D`,
`thetaCell_eq_abstract`, `piCell_eq_abstract_pi`), but only over the bespoke
`ZState` machine — so deleting that file (to clear an `Avx512Model` importer)
would lose the abstract content. This module is the **equal-strength successor**:
it reproduces the same abstract θ/π ties on the *packed `Com` denotations*, with
no dependence on the bespoke machine model (imports only `KeccakThetaPiCom` +
`Primitives.Keccak` + Mathlib's `BitVec` lane lemmas — NO `Avx512Model`).

## The 8-way batched lane view

A `reg 512` ZMM register holds 8 × u64 lanes (`zmmLane`/`zmmOfLanes`, `JasminDialect`).
In the standard 8-way batched Keccak packing, the eight sub-lanes carry eight
independent Keccak states. A Keccak state is supplied here as a function
`reg : Fin 5 → Fin 5 → BitVec 512` (lane `(x,y)`'s ZMM register), and
`stateAt reg k : KState` reads off the `k`-th batched state — sub-lane `k` of each
register. Every abstract tie is stated through `stateAt`, so a packed-`Com`
denotation equality becomes a FIPS-202 equality on each of the 8 sub-lanes.

## What is proved (the abstract θ/π ties)

* `zmmOfLanes_zmmLane'` / `zmmPackQ_lane` — the 8×u64 lane round-trip and the
  per-lane characterization of `zmmPackQ` (lane `k` of a packed op is the scalar
  `JasminBinOp.apply` of the input lanes). The qword analogues of `ZmmDwordLane`'s
  dword lemmas; reproved locally so this file imports no AVX-512 model.
* `parityCom_lane_eq_abstract_C` — lane `k` of `parityCom`'s denotation equals the
  abstract θ column parity `C[x] = a[x,0] ⊕ … ⊕ a[x,4]` of `stateAt reg k`.
* `dCom_lane_eq_abstract_D` — lane `k` of `dCom`'s denotation (with `one`/`c63`
  broadcasting `1`/`63`) equals `cm_k ⊕ rotl(cp_k, 1)`, the abstract θ diffusion
  mix; the explicit `(≪1)|||(≫63)` shift-decomposition equals the 64-bit
  `rotateLeft 1`.
* `thetaCell_eq_abstract` — feeding `dCom` the parities `C[x-1]`/`C[x+1]` of
  `stateAt reg k` and xoring `a[x,y]` reproduces `Primitives.Keccak.theta` at cell
  `(x,y)`, per sub-lane: the cross-lane assembly closed on the `Com` form.
* `piCell_eq_abstract_pi` — `piCom` (the `vmov` rename) realizes
  `Primitives.Keccak.pi` per sub-lane, when fed the source register
  `lreg ((x+3y) mod 5) x`: an index-permutation equality.
* `keccakThetaPiCom_eq_abstract` — the conjunction, packaged as the equal-strength
  successor of the bespoke `KeccakThetaPiRealization` abstract ties.

There is no `runZBlock` / `ZInstr` / `jasminc` / `jasminc_preserves_ct` in any
theorem's `#print axioms`: the tie is between the verified `Com jasminDialect`
denotation and the abstract FIPS-202 spec.

## References
* FIPS 202 — SHA-3 Standard (θ §3.2.1, π §3.2.3).

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom
open CatCrypt.Crypto.Primitives.Keccak

/-! ## 0. The 8×u64 ZMM lane round-trip and per-lane `zmmPackQ`

The qword analogues of `ZmmDwordLane`'s dword lemmas, reproved locally so this
module imports no AVX-512 model — only `JasminDialect`'s lane defs and Mathlib. -/

/-- Reading lane `k` (a 64-bit qword) of an assembled 8-lane ZMM register recovers
    the `k`-th lane function value: `zmmLane (zmmOfLanes f) k = f k`. The
    little-endian concatenation places `f k` at bits `[64k, 64k+64)`, exactly what
    `zmmLane` extracts. (Qword analogue of `zmmOfLanes32_zmmLane32`.) -/
theorem zmmOfLanes_zmmLane' (f : Fin 8 → BitVec 64) (k : Fin 8) :
    zmmLane (zmmOfLanes f) k = f k := by
  fin_cases k <;>
    (unfold zmmLane zmmOfLanes
     norm_num [Fin.val_ofNat, BitVec.extractLsb'_append_eq_of_le,
       BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_right,
       BitVec.extractLsb'_append_eq_left]) <;>
    rfl

/-- Lane `k` of `zmmPackQ bop a b` is `bop.apply (zmmLane a k) (zmmLane b k)`: each
    packed qword op acts on lane `k` of the two inputs independently. (Qword
    analogue of `zmmPackD_lane`.) -/
theorem zmmPackQ_lane (bop : JasminBinOp) (a b : BitVec 512) (k : Fin 8) :
    zmmLane (zmmPackQ bop a b) k = bop.apply (zmmLane a k) (zmmLane b k) := by
  unfold zmmPackQ
  rw [zmmOfLanes_zmmLane']

/-! ## 1. The batched-state view

A Keccak state per sub-lane is read from the per-lane ZMM registers: lane `(x,y)`
is sub-lane `k` of register `reg x y`. -/

/-- The `k`-th batched Keccak `KState` carried by the per-lane ZMM registers
    `reg : Fin 5 → Fin 5 → BitVec 512`: lane `(x,y)` is sub-lane `k` of
    `reg x y`. The abstract view through which every packed-`Com` denotation
    equality becomes a FIPS-202 statement. -/
def stateAt (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) : KState :=
  fun x y => zmmLane (reg x y) k

/-! ## 2. θ column parity tie -/

/-- **θ column-parity tie (per sub-lane).** Lane `k` of `parityCom`'s denotation on
    the five column registers `c0 … c4` equals the abstract θ column parity
    `a[x,0] ⊕ a[x,1] ⊕ a[x,2] ⊕ a[x,3] ⊕ a[x,4]` of `stateAt` — exactly `theta`'s
    `C[x]`, with `cⱼ = reg x j`. Successor of the bespoke `paritySpec_eq_abstract_C`. -/
theorem parityCom_lane_eq_abstract_C
    (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) (x : Fin 5) :
    zmmLane
        (parityCom.denote
          (.cons (reg x 0) (.cons (reg x 1) (.cons (reg x 2)
            (.cons (reg x 3) (.cons (reg x 4) .nil)))))) k
      = (stateAt reg k) x 0 ^^^ (stateAt reg k) x 1 ^^^ (stateAt reg k) x 2
          ^^^ (stateAt reg k) x 3 ^^^ (stateAt reg k) x 4 := by
  rw [parityCom_denote, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane]
  simp only [JasminBinOp.apply, stateAt]

/-! ## 3. θ diffusion tie -/

/-- The broadcast constant ZMM register holding `m` in every 64-bit lane. -/
def constZmm (m : Nat) : BitVec 512 := zmmOfLanes (fun _ => BitVec.ofNat 64 m)

/-- **θ diffusion tie (per sub-lane).** Lane `k` of `dCom`'s denotation, with `one`
    `=` broadcast `1` and `c63` `=` broadcast `63`, equals
    `(zmmLane cm k) ⊕ (zmmLane cp k).rotateLeft 1` — the abstract θ diffusion mix
    `C[x-1] ⊕ rotl(C[x+1], 1)` (once `cm = C[x-1]`, `cp = C[x+1]`). The explicit
    `(cp ≪ 1) ||| (cp ≫ 63)` shift-decomposition equals the 64-bit
    `rotateLeft 1`. Successor of the bespoke `dSpec_lane_eq_abstract_D`. -/
theorem dCom_lane_eq_abstract_D (cm cp : BitVec 512) (k : Fin 8) :
    zmmLane
        (dCom.denote (.cons cm (.cons cp (.cons (constZmm 1) (.cons (constZmm 63) .nil))))) k
      = (zmmLane cm k) ^^^ (zmmLane cp k).rotateLeft 1 := by
  rw [dCom_denote, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane]
  have hone : zmmLane (constZmm 1) k = BitVec.ofNat 64 1 := by
    unfold constZmm; rw [zmmOfLanes_zmmLane']
  have h63 : zmmLane (constZmm 63) k = BitVec.ofNat 64 63 := by
    unfold constZmm; rw [zmmOfLanes_zmmLane']
  simp only [JasminBinOp.apply, hone, h63]
  have h1 : (BitVec.ofNat 64 1).toNat = 1 := by decide
  have h63' : (BitVec.ofNat 64 63).toNat = 63 := by decide
  rw [h1, h63']
  rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt (by decide : (1 : Nat) < 64)]
  unfold BitVec.rotateLeftAux
  rfl

/-! ## 4. θ full lane update — the cross-lane assembly closed -/

/-- `theta` at cell `(x,y)` decomposed into the per-lane data the `Com` block
    assembles: `a[x,y] ⊕ (C[x-1] ⊕ rotl(C[x+1], 1))`. -/
theorem theta_cell_decomp (a : KState) (x y : Fin 5) :
    theta a x y
      = a x y
          ^^^ ((a ⟨(x.val + 4) % 5, by omega⟩ 0 ^^^ a ⟨(x.val + 4) % 5, by omega⟩ 1
                  ^^^ a ⟨(x.val + 4) % 5, by omega⟩ 2 ^^^ a ⟨(x.val + 4) % 5, by omega⟩ 3
                  ^^^ a ⟨(x.val + 4) % 5, by omega⟩ 4)
                ^^^ (a ⟨(x.val + 1) % 5, by omega⟩ 0 ^^^ a ⟨(x.val + 1) % 5, by omega⟩ 1
                  ^^^ a ⟨(x.val + 1) % 5, by omega⟩ 2 ^^^ a ⟨(x.val + 1) % 5, by omega⟩ 3
                  ^^^ a ⟨(x.val + 1) % 5, by omega⟩ 4).rotateLeft 1) := by
  unfold theta
  rfl

/-- **θ cross-lane assembly closed (per sub-lane).** Feed `dCom` the parities
    `C[x-1]` / `C[x+1]` of `stateAt reg k` (each `parityCom`'s lane, per §2), and
    xor `a[x,y]` with the diffusion-block output lane; the result reproduces
    `Primitives.Keccak.theta (stateAt reg k) x y` exactly. The cross-lane column
    parity + two-column rotate mix is the FIPS-202 θ, assembled on the
    unified `Com`. Successor of the bespoke `thetaCell_eq_abstract`. -/
theorem thetaCell_eq_abstract
    (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) (x y : Fin 5) :
    (stateAt reg k) x y
        ^^^ zmmLane
              (dCom.denote
                (.cons
                  (parityCom.denote
                    (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 0)
                      (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 1)
                        (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 2)
                          (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 3)
                            (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 4) .nil))))))
                  (.cons
                    (parityCom.denote
                      (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 0)
                        (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 1)
                          (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 2)
                            (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 3)
                              (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 4) .nil))))))
                    (.cons (constZmm 1) (.cons (constZmm 63) .nil)))))
              k
      = theta (stateAt reg k) x y := by
  rw [theta_cell_decomp, dCom_lane_eq_abstract_D,
    parityCom_lane_eq_abstract_C, parityCom_lane_eq_abstract_C]

/-! ## 5. π lane permutation tie -/

/-- **π tie (per sub-lane).** Lane `k` of `piCom`'s denotation, fed the source
    register `reg ((x+3y) mod 5) x`, is exactly `Primitives.Keccak.pi (stateAt reg k) x y`
    — the FIPS-202 lane permutation `a[x,y] ↦ a[(x+3y) mod 5, x]`. π is pure
    movement, so this is an index-permutation equality. Successor of the bespoke
    `piCell_eq_abstract_pi`. -/
theorem piCell_eq_abstract_pi
    (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) (x y : Fin 5) :
    zmmLane (piCom.denote (.cons (reg ⟨(x.val + 3 * y.val) % 5, by omega⟩ x) .nil)) k
      = pi (stateAt reg k) x y := by
  rw [piCom_denote]
  unfold pi stateAt
  rfl

/-! ## 6. The abstract θ/π ties packaged -/

/-- **The abstract FIPS-202 θ/π ties for the unified-`Com` Keccak block.** The
    conjunction of the column-parity, diffusion, full-θ-cell, and π ties — each a
    per-sub-lane equality between a packed `Com jasminDialect` denotation and the
    abstract `Primitives.Keccak.theta` / `pi`. The equal-strength successor of the
    bespoke `KeccakThetaPiRealization`'s abstract ties, with no dependence on
    the `Avx512Model` (`ZInstr`/`runZBlock`) machine. -/
theorem keccakThetaPiCom_eq_abstract
    (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) (x y : Fin 5) :
    -- θ column parity
    (zmmLane
        (parityCom.denote
          (.cons (reg x 0) (.cons (reg x 1) (.cons (reg x 2)
            (.cons (reg x 3) (.cons (reg x 4) .nil)))))) k
      = (stateAt reg k) x 0 ^^^ (stateAt reg k) x 1 ^^^ (stateAt reg k) x 2
          ^^^ (stateAt reg k) x 3 ^^^ (stateAt reg k) x 4)
    -- θ full lane update reproduces FIPS-202 theta
    ∧ ((stateAt reg k) x y
        ^^^ zmmLane
              (dCom.denote
                (.cons
                  (parityCom.denote
                    (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 0)
                      (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 1)
                        (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 2)
                          (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 3)
                            (.cons (reg ⟨(x.val + 4) % 5, by omega⟩ 4) .nil))))))
                  (.cons
                    (parityCom.denote
                      (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 0)
                        (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 1)
                          (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 2)
                            (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 3)
                              (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ 4) .nil))))))
                    (.cons (constZmm 1) (.cons (constZmm 63) .nil)))))
              k
      = theta (stateAt reg k) x y)
    -- π permutation reproduces FIPS-202 pi
    ∧ (zmmLane (piCom.denote (.cons (reg ⟨(x.val + 3 * y.val) % 5, by omega⟩ x) .nil)) k
      = pi (stateAt reg k) x y) :=
  ⟨parityCom_lane_eq_abstract_C reg k x,
   thetaCell_eq_abstract reg k x y,
   piCell_eq_abstract_pi reg k x y⟩

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom
