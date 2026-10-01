/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvBytesProof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519MulProof

/-!
# The RV64 Curve25519 multiply and square, carried to their encoded bytes

`RiscvFe25519MulProof.feMul_correct` and `feSqr_correct` are stated over lowered blocks with
symbolic register names. This module states them over the bytes of physical blocks, by the
construction of `RiscvBytesProof` (allocation `KAlloc` checked against `allocLive64`,
liveness by `renGo`, decode round trip by `MInstOKb`, transport by `runM64_phys`).

## ABI

| kernel | inputs | output | instructions |
|---|---|---|---|
| `feMul` | `x` in `a0..a3`, `y` in `a4..a7` | `a0..a3` | 1033 |
| `feSqr` | `x` in `a0..a3` | `a0..a3` | 1037 |

Both allocations use all of `s0..s11` as scratch without restoring them, so, like the field
blocks of `RiscvBytesProof`, they are not RISC-V psABI leaf functions as they stand.

## Main results

* `feMulBytes_correct`: the bytes of `feMulPhys` decode to a block leaving
  `x · y mod p25519` in `a0..a3`, for every machine state;
* `feSqrBytes_correct`: the same for `feSqrPhys` and `x · x mod p25519`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvMulBytesProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvBytesProof
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519MulProof

/-- The allocation of `feMulBlock`. -/
def feMulAlloc : List (String × String) :=
  [("u0", "t0"), ("q0", "a0"), ("u1", "a0"), ("q1", "a1"), ("u2", "t1"), ("q2", "a2"),
    ("u3", "t2"), ("q3", "a3"), ("v0", "t3"), ("y0", "a4"), ("v1", "a4"), ("y1", "a5"),
    ("v2", "a5"), ("y2", "a6"), ("v3", "a6"), ("y3", "a7"), ("acc0", "a7"), ("acc1", "t4"),
    ("acc2", "t5"), ("acc3", "t6"), ("acc4", "s0"), ("acc5", "s1"), ("acc6", "s2"),
    ("acc7", "s3"), ("lo__", "s4"), ("hi__", "s5"), ("sum__", "s6"), ("cra", "s7"),
    ("tt__", "s8"), ("c1__", "s9"), ("c2__", "s10"), ("crb", "s11"), ("c38", "a4"),
    ("rl4", "a0"), ("rh4", "a5"), ("rl5", "a6"), ("rh5", "t0"), ("rl6", "t1"), ("rh6", "t2"),
    ("rl7", "t3"), ("rh7", "s0"), ("j0", "s1"), ("j1", "a0"), ("j2", "a1"), ("j3", "a2"),
    ("q4", "a3"), ("j4", "a3"), ("r1", "a5"), ("t0", "a6"), ("r2", "a0"), ("t1", "a5"),
    ("r3", "a0"), ("t2", "a7"), ("r4", "a0"), ("t3", "t0"), ("r5", "a0"), ("t4", "a0"),
    ("fl", "t1"), ("cy1", "a1"), ("z0", "a0"), ("cy2", "a2"), ("z1", "a1"), ("cy3", "a3"),
    ("z2", "a2"), ("cy", "a5"), ("z3", "a3"), ("cz1", "a4"), ("cz2", "a4"), ("cz3", "a4"),
    ("cz4", "a4"), ("pp0", "a4"), ("pp1", "a5"), ("pp2", "a6"), ("pp3", "a7"), ("bo1", "t0"),
    ("m0", "t1"), ("b1__", "t2"), ("b2__", "t3"), ("dif__", "t4"), ("bo2", "t5"), ("m1", "t6"),
    ("bo3", "s0"), ("m2", "s1"), ("bo", "s2"), ("m3", "s3"), ("one", "s4"), ("cond", "s5"),
    ("mask", "s6"), ("csm__", "s7")]

theorem feMulAlloc_eq :
    allocLive64 fePins physPool (lowerRBlock64 feMulBlock) ["z0", "z1", "z2", "z3"]
      = feMulAlloc := by decide +kernel

theorem feMul_renGo :
    (renGo (nameOf feMulAlloc) (lowerRBlock64 feMulBlock)
      ["z0", "z1", "z2", "z3"]).isSome = true := by decide +kernel

/-- The physical `feMul` block. -/
def feMulPhys : List MInst64 :=
  expandLi (renameRBlock64 (nameOf feMulAlloc) (lowerRBlock64 feMulBlock))

theorem feMulPhys_ok : feMulPhys.all MInstOKb = true := by decide +kernel

theorem feMulPhys_length : feMulPhys.length = 1033 := by decide +kernel

theorem feMulPhys_correct (t : RState64) :
    limbs4 (runM64 t feMulPhys).get "a0" "a1" "a2" "a3"
      = limbs4 t.get "a0" "a1" "a2" "a3" * limbs4 t.get "a4" "a5" "a6" "a7" % p25519 := by
  obtain ⟨Lin, hLin⟩ := Option.isSome_iff_exists.1 feMul_renGo
  have hp := limbs4_pull (nameOf feMulAlloc) rfl rfl t
  have h := feMul_correct (pull (nameOf feMulAlloc) t)
  rw [← limbs4_phys (nameOf feMulAlloc) rfl rfl _ _ Lin hLin t _ _ _ _ (by decide), hp, hp] at h
  exact h

/-- **The encoded field multiplication.** Its bytes decode as 1033 instructions `c` such
    that, for every machine state with `x` in `a0..a3` and `y` in `a4..a7`, running `c`
    leaves `x · y mod p25519` in `a0..a3`. -/
theorem feMulBytes_correct :
    ∃ c, decodeMStream64 1033 (encodeMBlock64 feMulPhys) = some c ∧
      ∀ t : RState64,
        limbs4 (runM64 t c).get "a0" "a1" "a2" "a3"
          = limbs4 t.get "a0" "a1" "a2" "a3" * limbs4 t.get "a4" "a5" "a6" "a7" % p25519 :=
  ⟨feMulPhys, feMulPhys_length ▸ decodeMStream64_encode_b _ feMulPhys_ok, feMulPhys_correct⟩

/-- The allocation of `feSqrBlock`. -/
def feSqrAlloc : List (String × String) :=
  [("y0", "a4"), ("q0", "a0"), ("y1", "a5"), ("q1", "a1"), ("y2", "a6"), ("q2", "a2"),
    ("y3", "a7"), ("q3", "a3"), ("u0", "t0"), ("u1", "a0"), ("u2", "t1"), ("u3", "t2"),
    ("v0", "t3"), ("v1", "a4"), ("v2", "a5"), ("v3", "a6"), ("acc0", "a7"), ("acc1", "t4"),
    ("acc2", "t5"), ("acc3", "t6"), ("acc4", "s0"), ("acc5", "s1"), ("acc6", "s2"),
    ("acc7", "s3"), ("lo__", "s4"), ("hi__", "s5"), ("sum__", "s6"), ("cra", "s7"),
    ("tt__", "s8"), ("c1__", "s9"), ("c2__", "s10"), ("crb", "s11"), ("c38", "a4"),
    ("rl4", "a0"), ("rh4", "a5"), ("rl5", "a6"), ("rh5", "t0"), ("rl6", "t1"), ("rh6", "t2"),
    ("rl7", "t3"), ("rh7", "s0"), ("j0", "s1"), ("j1", "a0"), ("j2", "a1"), ("j3", "a2"),
    ("q4", "a3"), ("j4", "a3"), ("r1", "a5"), ("t0", "a6"), ("r2", "a0"), ("t1", "a5"),
    ("r3", "a0"), ("t2", "a7"), ("r4", "a0"), ("t3", "t0"), ("r5", "a0"), ("t4", "a0"),
    ("fl", "t1"), ("cy1", "a1"), ("z0", "a0"), ("cy2", "a2"), ("z1", "a1"), ("cy3", "a3"),
    ("z2", "a2"), ("cy", "a5"), ("z3", "a3"), ("cz1", "a4"), ("cz2", "a4"), ("cz3", "a4"),
    ("cz4", "a4"), ("pp0", "a4"), ("pp1", "a5"), ("pp2", "a6"), ("pp3", "a7"), ("bo1", "t0"),
    ("m0", "t1"), ("b1__", "t2"), ("b2__", "t3"), ("dif__", "t4"), ("bo2", "t5"), ("m1", "t6"),
    ("bo3", "s0"), ("m2", "s1"), ("bo", "s2"), ("m3", "s3"), ("one", "s4"), ("cond", "s5"),
    ("mask", "s6"), ("csm__", "s7")]

theorem feSqrAlloc_eq :
    allocLive64 fePins physPool (lowerRBlock64 feSqrBlock) ["z0", "z1", "z2", "z3"]
      = feSqrAlloc := by decide +kernel

theorem feSqr_renGo :
    (renGo (nameOf feSqrAlloc) (lowerRBlock64 feSqrBlock)
      ["z0", "z1", "z2", "z3"]).isSome = true := by decide +kernel

/-- The physical `feSqr` block. -/
def feSqrPhys : List MInst64 :=
  expandLi (renameRBlock64 (nameOf feSqrAlloc) (lowerRBlock64 feSqrBlock))

theorem feSqrPhys_ok : feSqrPhys.all MInstOKb = true := by decide +kernel

theorem feSqrPhys_length : feSqrPhys.length = 1037 := by decide +kernel

theorem feSqrPhys_correct (t : RState64) :
    limbs4 (runM64 t feSqrPhys).get "a0" "a1" "a2" "a3"
      = limbs4 t.get "a0" "a1" "a2" "a3" * limbs4 t.get "a0" "a1" "a2" "a3" % p25519 := by
  obtain ⟨Lin, hLin⟩ := Option.isSome_iff_exists.1 feSqr_renGo
  have hp := limbs4_pull (nameOf feSqrAlloc) rfl rfl t
  have h := feSqr_correct (pull (nameOf feSqrAlloc) t)
  rw [← limbs4_phys (nameOf feSqrAlloc) rfl rfl _ _ Lin hLin t _ _ _ _ (by decide), hp] at h
  exact h

/-- **The encoded field squaring.** Its bytes decode as 1037 instructions `c` such that,
    for every machine state with `x` in `a0..a3`, running `c` leaves `x · x mod p25519` in
    `a0..a3`. -/
theorem feSqrBytes_correct :
    ∃ c, decodeMStream64 1037 (encodeMBlock64 feSqrPhys) = some c ∧
      ∀ t : RState64,
        limbs4 (runM64 t c).get "a0" "a1" "a2" "a3"
          = limbs4 t.get "a0" "a1" "a2" "a3" * limbs4 t.get "a0" "a1" "a2" "a3" % p25519 :=
  ⟨feSqrPhys, feSqrPhys_length ▸ decodeMStream64_encode_b _ feSqrPhys_ok, feSqrPhys_correct⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvMulBytesProof.feMulBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feMulBytes_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvMulBytesProof
