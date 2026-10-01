/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvAddP256Proof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64

/-!
# The RV64 kernels, carried to their encoded bytes

`RiscvAddP256Proof.addp256_correct` and the results of `RiscvFe25519AddSubProof`
(`feAdd_correct`, `feSub_correct`, `feMul121666_correct`, `cswap_correct`) are stated
over lowered blocks whose register names are symbolic (`d0`, `cy1`, `sum__`, …). This
module states them over the bytes of physical blocks: the kernel with every name replaced by an RV64 register and every `li`
expanded to `addi`/`slli` (`RiscvBytes64.expandLi`), encoded by
`RiscvBytes64.encodeMBlock64`.

## Construction, per kernel `K`

* `KAlloc` is a literal association list from symbolic names to registers. It is the
  output of `RiscvRename64.allocLive64` on `K` with the inputs pinned to `a0..a7`, and
  `KAlloc_eq` checks that by `decide +kernel`.
* `K_renGo`: the liveness checker `renGo` accepts `nameOf KAlloc` on `K`, with the
  outputs live out. `KPhys` is `expandLi (renameRBlock64 (nameOf KAlloc) K)`.
* `KPhys_ok`: every instruction of `KPhys` meets the side conditions of the decode
  round trip (`MInstOKb`), so `decodeMStream64_encode_b` decodes the bytes back to
  `KPhys`.
* `KPhys_correct` transports the symbolic result through `runM64_phys`, from the state
  `pull (nameOf KAlloc) t` that reads each name at its register.

## ABI

| kernel | inputs | output | instructions |
|---|---|---|---|
| `addp256` | `x` in `a0..a3`, `y` in `a4..a7` | `a0..a3` | 83 |
| `feAdd` | `x` in `a0..a3`, `y` in `a4..a7` | `a0..a3` | 186 |
| `feSub` | `x` in `a0..a3`, `y` in `a4..a7` | `a0..a3` | 216 |
| `feMul121666` | `x` in `a0..a3` | `a0..a3` | 195 |
| `cswap` | `a0..a3`, `a4..a7`, swap word in `t0` | `a0..a3`, `a4..a7` | 52 |

## Trust points

* That `decodeMStream64` and `runM64` agree with an RV64 processor on these instructions
  is not proved here. `SailRiscv64Refinement` relates the value each instruction writes
  to the Sail model, one instruction at a time.
* There is no prologue or epilogue: the kernels read and write registers only (the RV64
  model has no memory). The three field blocks use the callee-saved registers
  `s0..s8` as scratch and do not restore them, so they are not RISC-V psABI leaf functions
  as they stand.

## Main results

* `limbs4_pull`, `limbs4_phys`: the transport for four-limb values.
* `addp256Bytes_correct`, `feAddBytes_correct`, `feSubBytes_correct`,
  `feMul121666Bytes_correct`, `cswapBytes_correct`: the byte theorems, each from the
  matching `KPhys_correct` over the physical block.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvBytesProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros

/-! ## 1. Transport of four-limb values -/

theorem limbs4_pull (ρ : String → String) (hz : ρ "zero" = "zero") (hx0 : ρ "x0" = "x0")
    (t : RState64) (a0 a1 a2 a3 : String) :
    limbs4 (pull ρ t).get a0 a1 a2 a3 = limbs4 t.get (ρ a0) (ρ a1) (ρ a2) (ρ a3) := by
  simp only [limbs4, pull_get ρ hz hx0]

theorem limbs4_phys (ρ : String → String) (hz : ρ "zero" = "zero") (hx0 : ρ "x0" = "x0")
    (b : List RInst64) (L Lin : List String) (hok : renGo ρ b L = some Lin) (t : RState64)
    (a0 a1 a2 a3 : String) (h : a0 ∈ L ∧ a1 ∈ L ∧ a2 ∈ L ∧ a3 ∈ L) :
    limbs4 (runM64 t (expandLi (renameRBlock64 ρ b))).get (ρ a0) (ρ a1) (ρ a2) (ρ a3)
      = limbs4 (runRBlock64 (pull ρ t) b).get a0 a1 a2 a3 := by
  simp only [limbs4, runM64_phys ρ hz hx0 b L Lin hok t _ h.1, runM64_phys ρ hz hx0 b L Lin hok t _ h.2.1,
    runM64_phys ρ hz hx0 b L Lin hok t _ h.2.2.1, runM64_phys ρ hz hx0 b L Lin hok t _ h.2.2.2]

/-- The registers the allocator draws from: `a0..a7`, `t0..t6`, `s0..s11`. -/
def physPool : List String :=
  ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "t0", "t1", "t2", "t3", "t4", "t5", "t6",
    "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]

/-! ## 2. `bignum_add_p256` -/

section AddP256

open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBignumKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvAddP256Proof
open CatCrypt.Crypto.SecureCompilation.FieldSpecs (p256)

/-- `x` (`d0..d3`, also the output) in `a0..a3`, `y` (`n0..n3`) in `a4..a7`. -/
def addp256Pins : List (String × String) :=
  [("d0", "a0"), ("d1", "a1"), ("d2", "a2"), ("d3", "a3"),
    ("n0", "a4"), ("n1", "a5"), ("n2", "a6"), ("n3", "a7")]

def addp256Alloc : List (String × String) :=
  [("sum__", "t0"), ("d0", "a0"), ("n0", "a4"), ("cy1", "a4"), ("tt", "t1"),
    ("d1", "a1"), ("n1", "a5"), ("c1__", "a5"), ("c2__", "a4"), ("cy2", "t2"),
    ("d2", "a2"), ("n2", "a6"), ("cy3", "a6"), ("d3", "a3"), ("n3", "a7"), ("cy", "a6"),
    ("p0", "a4"), ("p1", "a5"), ("p3", "a7"), ("bo1", "t0"), ("m0", "t2"),
    ("b1__", "a4"), ("b2__", "a5"), ("dif__", "t3"), ("bo2", "t0"), ("m1", "t4"),
    ("bo3", "t0"), ("m2", "t5"), ("bo4", "a7"), ("m3", "t0"), ("bo", "a6"),
    ("boF", "a4"), ("one", "a4"), ("cond", "a5"), ("mask", "a4"), ("csm__", "a6")]

theorem addp256Alloc_eq :
    allocLive64 addp256Pins physPool (lowerRBlock64 addp256Block64) ["d0", "d1", "d2", "d3"]
      = addp256Alloc := by decide +kernel

theorem addp256_renGo :
    (renGo (nameOf addp256Alloc) (lowerRBlock64 addp256Block64)
      ["d0", "d1", "d2", "d3"]).isSome = true := by decide +kernel

/-- The physical `addp256` block. -/
def addp256Phys : List MInst64 :=
  expandLi (renameRBlock64 (nameOf addp256Alloc) (lowerRBlock64 addp256Block64))

theorem addp256Phys_ok : addp256Phys.all MInstOKb = true := by decide +kernel

theorem addp256Phys_length : addp256Phys.length = 83 := by decide +kernel

/-- The physical block leaves `(x + y) mod p256` in `a0..a3`. -/
theorem addp256Phys_correct (t : RState64)
    (hx : limbs4 t.get "a0" "a1" "a2" "a3" < p256)
    (hy : limbs4 t.get "a4" "a5" "a6" "a7" < p256) :
    limbs4 (runM64 t addp256Phys).get "a0" "a1" "a2" "a3"
      = (limbs4 t.get "a0" "a1" "a2" "a3" + limbs4 t.get "a4" "a5" "a6" "a7") % p256 := by
  obtain ⟨Lin, hLin⟩ := Option.isSome_iff_exists.1 addp256_renGo
  have hp := limbs4_pull (nameOf addp256Alloc) rfl rfl t
  have h := addp256_correct (pull (nameOf addp256Alloc) t) (by rw [hp]; exact hx)
    (by rw [hp]; exact hy)
  rw [← limbs4_phys (nameOf addp256Alloc) rfl rfl _ _ Lin hLin t _ _ _ _ (by decide), hp, hp] at h
  exact h

/-- **The encoded `bignum_add_p256` block.** Its bytes decode as 83 instructions `c`
    such that, for every machine state with `x` in `a0..a3` and `y` in `a4..a7`, both
    below `p256`, running `c` leaves `(x + y) mod p256` in `a0..a3`. -/
theorem addp256Bytes_correct :
    ∃ c, decodeMStream64 83 (encodeMBlock64 addp256Phys) = some c ∧
      ∀ t : RState64,
        limbs4 t.get "a0" "a1" "a2" "a3" < p256 →
        limbs4 t.get "a4" "a5" "a6" "a7" < p256 →
        limbs4 (runM64 t c).get "a0" "a1" "a2" "a3"
          = (limbs4 t.get "a0" "a1" "a2" "a3" + limbs4 t.get "a4" "a5" "a6" "a7") % p256 :=
  ⟨addp256Phys, addp256Phys_length ▸ decodeMStream64_encode_b _ addp256Phys_ok,
    addp256Phys_correct⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvBytesProof.addp256Bytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addp256Bytes_correct

end AddP256

/-! ## 3. The Curve25519 field blocks -/

section Fe25519

open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof

/-- `x` (`q0..q3`) in `a0..a3`, `y` (`y0..y3`) in `a4..a7`, the result (`z0..z3`) in
    `a0..a3`. -/
def fePins : List (String × String) :=
  [("q0", "a0"), ("q1", "a1"), ("q2", "a2"), ("q3", "a3"),
    ("y0", "a4"), ("y1", "a5"), ("y2", "a6"), ("y3", "a7"),
    ("z0", "a0"), ("z1", "a1"), ("z2", "a2"), ("z3", "a3")]

/-- The allocation of `feAddBlock`. -/
def feAddAlloc : List (String × String) :=
  [("sum__", "t0"), ("q0", "a0"), ("y0", "a4"), ("e1", "a4"), ("d0", "a0"),
    ("tt__", "t1"), ("q1", "a1"), ("y1", "a5"), ("c1__", "a5"), ("c2__", "a4"),
    ("e2", "a1"), ("d1", "t2"), ("q2", "a2"), ("y2", "a6"), ("e3", "a1"), ("d2", "a2"),
    ("q3", "a3"), ("y3", "a7"), ("d4", "a1"), ("d3", "a3"), ("c38", "a6"), ("fl", "a7"),
    ("cy1", "a1"), ("z0", "a0"), ("cy2", "t2"), ("z1", "a1"), ("cy3", "t2"),
    ("z2", "a2"), ("cy", "t2"), ("z3", "a3"), ("cz1", "a6"), ("cz2", "a6"),
    ("cz3", "a6"), ("cz4", "a6"), ("pp0", "a4"), ("pp1", "a5"), ("pp2", "a6"),
    ("pp3", "a7"), ("bo1", "t0"), ("m0", "t2"), ("b1__", "t3"), ("b2__", "t4"),
    ("dif__", "t5"), ("bo2", "t6"), ("m1", "s0"), ("bo3", "s1"), ("m2", "s2"),
    ("bo", "s3"), ("m3", "s4"), ("one", "s5"), ("cond", "s6"), ("mask", "s7"),
    ("csm__", "s8")]

theorem feAddAlloc_eq :
    allocLive64 fePins physPool (lowerRBlock64 feAddBlock) ["z0", "z1", "z2", "z3"] = feAddAlloc := by decide +kernel

theorem feAdd_renGo :
    (renGo (nameOf feAddAlloc) (lowerRBlock64 feAddBlock) ["z0", "z1", "z2", "z3"]).isSome = true := by decide +kernel

def feAddPhys : List MInst64 :=
  expandLi (renameRBlock64 (nameOf feAddAlloc) (lowerRBlock64 feAddBlock))

theorem feAddPhys_ok : feAddPhys.all MInstOKb = true := by decide +kernel

theorem feAddPhys_length : feAddPhys.length = 186 := by decide +kernel

theorem feAddPhys_correct (t : RState64) :
    limbs4 (runM64 t feAddPhys).get "a0" "a1" "a2" "a3" = (limbs4 t.get "a0" "a1" "a2" "a3" + limbs4 t.get "a4" "a5" "a6" "a7") % p25519 := by
  obtain ⟨Lin, hLin⟩ := Option.isSome_iff_exists.1 feAdd_renGo
  have hp := limbs4_pull (nameOf feAddAlloc) rfl rfl t
  have h := feAdd_correct (pull (nameOf feAddAlloc) t)
  rw [← limbs4_phys (nameOf feAddAlloc) rfl rfl _ _ Lin hLin t _ _ _ _ (by decide), hp, hp] at h
  exact h

/-- **The encoded field addition.** Its bytes decode as 186 instructions `c` such that, for
    every machine state with `x` in `a0..a3` and `y` in `a4..a7`, running `c` leaves
    `(x + y) mod p25519` in `a0..a3`. -/
theorem feAddBytes_correct :
    ∃ c, decodeMStream64 186 (encodeMBlock64 feAddPhys) = some c ∧
      ∀ t : RState64,
        limbs4 (runM64 t c).get "a0" "a1" "a2" "a3" = (limbs4 t.get "a0" "a1" "a2" "a3" + limbs4 t.get "a4" "a5" "a6" "a7") % p25519 :=
  ⟨feAddPhys, feAddPhys_length ▸ decodeMStream64_encode_b _ feAddPhys_ok,
    feAddPhys_correct⟩

/-- The allocation of `feSubBlock`. -/
def feSubAlloc : List (String × String) :=
  [("tp0", "t0"), ("tp1", "t1"), ("tp2", "t2"), ("tp3", "t3"), ("sum__", "t4"),
    ("q0", "a0"), ("f1", "t0"), ("a0", "a0"), ("tt__", "t5"), ("q1", "a1"),
    ("c1__", "t1"), ("c2__", "t0"), ("f2", "a1"), ("a1", "t6"), ("q2", "a2"),
    ("f3", "a1"), ("a2", "a2"), ("q3", "a3"), ("a4", "a1"), ("a3", "a3"), ("g1", "t2"),
    ("y0", "a4"), ("b1__", "a4"), ("y1", "a5"), ("b2__", "a5"), ("dif__", "t3"),
    ("g2", "t2"), ("y2", "a6"), ("g3", "a6"), ("y3", "a7"), ("g4", "a6"), ("gF", "a6"),
    ("c38", "a6"), ("fl", "a7"), ("cy1", "a1"), ("z0", "a0"), ("cy2", "t2"),
    ("z1", "a1"), ("cy3", "t2"), ("z2", "a2"), ("cy", "t2"), ("z3", "a3"), ("cz1", "a6"),
    ("cz2", "a6"), ("cz3", "a6"), ("cz4", "a6"), ("pp0", "a6"), ("pp1", "a7"),
    ("pp2", "t0"), ("pp3", "t1"), ("bo1", "t2"), ("m0", "t4"), ("bo2", "t6"),
    ("m1", "s0"), ("bo3", "s1"), ("m2", "s2"), ("bo", "s3"), ("m3", "s4"), ("one", "s5"),
    ("cond", "s6"), ("mask", "s7"), ("csm__", "s8")]

theorem feSubAlloc_eq :
    allocLive64 fePins physPool (lowerRBlock64 feSubBlock) ["z0", "z1", "z2", "z3"] = feSubAlloc := by decide +kernel

theorem feSub_renGo :
    (renGo (nameOf feSubAlloc) (lowerRBlock64 feSubBlock) ["z0", "z1", "z2", "z3"]).isSome = true := by decide +kernel

def feSubPhys : List MInst64 :=
  expandLi (renameRBlock64 (nameOf feSubAlloc) (lowerRBlock64 feSubBlock))

theorem feSubPhys_ok : feSubPhys.all MInstOKb = true := by decide +kernel

theorem feSubPhys_length : feSubPhys.length = 216 := by decide +kernel

theorem feSubPhys_correct (t : RState64)
    (hy : limbs4 t.get "a4" "a5" "a6" "a7" ≤ limbs4 t.get "a0" "a1" "a2" "a3" + 2 * p25519) :
    limbs4 (runM64 t feSubPhys).get "a0" "a1" "a2" "a3" = (limbs4 t.get "a0" "a1" "a2" "a3" + 2 * p25519 - limbs4 t.get "a4" "a5" "a6" "a7") % p25519 := by
  obtain ⟨Lin, hLin⟩ := Option.isSome_iff_exists.1 feSub_renGo
  have hp := limbs4_pull (nameOf feSubAlloc) rfl rfl t
  have h := feSub_correct (pull (nameOf feSubAlloc) t) (by rw [hp, hp]; exact hy)
  rw [← limbs4_phys (nameOf feSubAlloc) rfl rfl _ _ Lin hLin t _ _ _ _ (by decide), hp, hp] at h
  exact h

/-- **The encoded field subtraction.** Its bytes decode as 216 instructions `c` such that,
    for every machine state with `x` in `a0..a3` and `y ≤ x + 2·p25519` in `a4..a7`,
    running `c` leaves `(x + 2·p25519 − y) mod p25519` in `a0..a3`. -/
theorem feSubBytes_correct :
    ∃ c, decodeMStream64 216 (encodeMBlock64 feSubPhys) = some c ∧
      ∀ t : RState64,
        limbs4 t.get "a4" "a5" "a6" "a7" ≤ limbs4 t.get "a0" "a1" "a2" "a3" + 2 * p25519 →
        limbs4 (runM64 t c).get "a0" "a1" "a2" "a3" = (limbs4 t.get "a0" "a1" "a2" "a3" + 2 * p25519 - limbs4 t.get "a4" "a5" "a6" "a7") % p25519 :=
  ⟨feSubPhys, feSubPhys_length ▸ decodeMStream64_encode_b _ feSubPhys_ok,
    feSubPhys_correct⟩

/-- The allocation of `feMul121666Block`. -/
def feMul121666Alloc : List (String × String) :=
  [("cc", "t0"), ("l0", "a4"), ("q0", "a0"), ("h0", "a5"), ("l1", "a0"), ("q1", "a1"),
    ("h1", "a6"), ("l2", "a1"), ("q2", "a2"), ("h2", "a7"), ("l3", "a2"), ("q3", "a3"),
    ("h3", "t1"), ("a0", "a3"), ("sum__", "a4"), ("p1", "a0"), ("a1", "a5"),
    ("tt__", "t0"), ("c1__", "t2"), ("c2__", "a6"), ("p2", "a0"), ("a2", "t3"),
    ("p3", "a0"), ("a3", "a7"), ("p4", "a0"), ("a4", "a0"), ("c38", "t1"), ("fl", "t4"),
    ("cy1", "a1"), ("z0", "a0"), ("cy2", "a2"), ("z1", "a1"), ("cy3", "a3"),
    ("z2", "a2"), ("cy", "a5"), ("z3", "a3"), ("cz1", "a5"), ("cz2", "a5"),
    ("cz3", "a5"), ("cz4", "a5"), ("pp0", "a4"), ("pp1", "a5"), ("pp2", "a6"),
    ("pp3", "a7"), ("bo1", "t1"), ("m0", "t2"), ("b1__", "t3"), ("b2__", "t4"),
    ("dif__", "t5"), ("bo2", "t6"), ("m1", "s0"), ("bo3", "s1"), ("m2", "s2"),
    ("bo", "s3"), ("m3", "s4"), ("one", "s5"), ("cond", "s6"), ("mask", "s7"),
    ("csm__", "s8")]

theorem feMul121666Alloc_eq :
    allocLive64 fePins physPool (lowerRBlock64 feMul121666Block) ["z0", "z1", "z2", "z3"] = feMul121666Alloc := by decide +kernel

theorem feMul121666_renGo :
    (renGo (nameOf feMul121666Alloc) (lowerRBlock64 feMul121666Block) ["z0", "z1", "z2", "z3"]).isSome = true := by decide +kernel

def feMul121666Phys : List MInst64 :=
  expandLi (renameRBlock64 (nameOf feMul121666Alloc) (lowerRBlock64 feMul121666Block))

theorem feMul121666Phys_ok : feMul121666Phys.all MInstOKb = true := by decide +kernel

theorem feMul121666Phys_length : feMul121666Phys.length = 195 := by decide +kernel

theorem feMul121666Phys_correct (t : RState64) :
    limbs4 (runM64 t feMul121666Phys).get "a0" "a1" "a2" "a3" = 121666 * limbs4 t.get "a0" "a1" "a2" "a3" % p25519 := by
  obtain ⟨Lin, hLin⟩ := Option.isSome_iff_exists.1 feMul121666_renGo
  have hp := limbs4_pull (nameOf feMul121666Alloc) rfl rfl t
  have h := feMul121666_correct (pull (nameOf feMul121666Alloc) t)
  rw [← limbs4_phys (nameOf feMul121666Alloc) rfl rfl _ _ Lin hLin t _ _ _ _ (by decide), hp] at h
  exact h

/-- **The encoded multiplication by `121666`.** Its bytes decode as 195 instructions `c`
    such that, for every machine state with `x` in `a0..a3`, running `c` leaves
    `121666 · x mod p25519` in `a0..a3`. -/
theorem feMul121666Bytes_correct :
    ∃ c, decodeMStream64 195 (encodeMBlock64 feMul121666Phys) = some c ∧
      ∀ t : RState64,
        limbs4 (runM64 t c).get "a0" "a1" "a2" "a3" = 121666 * limbs4 t.get "a0" "a1" "a2" "a3" % p25519 :=
  ⟨feMul121666Phys, feMul121666Phys_length ▸ decodeMStream64_encode_b _ feMul121666Phys_ok,
    feMul121666Phys_correct⟩

/-- The two inputs of `cswapBlock` stay in place (`a0..a3`, `b0..b3` in `a4..a7`); the
    swap word is in `t0`. -/
def cswapPins : List (String × String) :=
  [("a0", "a0"), ("a1", "a1"), ("a2", "a2"), ("a3", "a3"),
    ("b0", "a4"), ("b1", "a5"), ("b2", "a6"), ("b3", "a7"), ("swap", "t0")]

/-- The allocation of `cswapBlock`. -/
def cswapAlloc : List (String × String) :=
  [("s0", "t1"), ("a0", "a0"), ("mask", "t2"), ("swap", "t0"), ("tt__", "t3"),
    ("b0", "a4"), ("csm__", "t4"), ("s1", "t1"), ("a1", "a1"), ("b1", "a5"),
    ("s2", "t1"), ("a2", "a2"), ("b2", "a6"), ("s3", "t1"), ("a3", "a3"), ("b3", "a7")]

theorem cswapAlloc_eq :
    allocLive64 cswapPins physPool (lowerRBlock64 cswapBlock) ["a0", "a1", "a2", "a3", "b0", "b1", "b2", "b3"] = cswapAlloc := by decide +kernel

theorem cswap_renGo :
    (renGo (nameOf cswapAlloc) (lowerRBlock64 cswapBlock) ["a0", "a1", "a2", "a3", "b0", "b1", "b2", "b3"]).isSome = true := by decide +kernel

def cswapPhys : List MInst64 :=
  expandLi (renameRBlock64 (nameOf cswapAlloc) (lowerRBlock64 cswapBlock))

theorem cswapPhys_ok : cswapPhys.all MInstOKb = true := by decide +kernel

theorem cswapPhys_length : cswapPhys.length = 52 := by decide +kernel

theorem cswapPhys_correct (t : RState64)
    (hsw : (t.get "t0").toNat ≤ 1) :
    limbs4 (runM64 t cswapPhys).get "a0" "a1" "a2" "a3" = (if (t.get "t0").toNat = 1 then limbs4 t.get "a4" "a5" "a6" "a7" else limbs4 t.get "a0" "a1" "a2" "a3") ∧
      limbs4 (runM64 t cswapPhys).get "a4" "a5" "a6" "a7" = (if (t.get "t0").toNat = 1 then limbs4 t.get "a0" "a1" "a2" "a3" else limbs4 t.get "a4" "a5" "a6" "a7") := by
  obtain ⟨Lin, hLin⟩ := Option.isSome_iff_exists.1 cswap_renGo
  have hp := limbs4_pull (nameOf cswapAlloc) rfl rfl t
  have h := cswap_correct (pull (nameOf cswapAlloc) t) (by rw [pull_get _ rfl rfl]; exact hsw)
  rw [← limbs4_phys (nameOf cswapAlloc) rfl rfl _ _ Lin hLin t "a0" "a1" "a2" "a3" (by decide),
    ← limbs4_phys (nameOf cswapAlloc) rfl rfl _ _ Lin hLin t "b0" "b1" "b2" "b3" (by decide),
    hp, hp, pull_get _ rfl rfl] at h
  exact h

/-- **The encoded conditional swap.** Its bytes decode as 52 instructions `c` such that,
    for every machine state with a swap word `0` or `1` in `t0`, running `c` exchanges
    `a0..a3` and `a4..a7` when the word is `1` and leaves them when it is `0`. -/
theorem cswapBytes_correct :
    ∃ c, decodeMStream64 52 (encodeMBlock64 cswapPhys) = some c ∧
      ∀ t : RState64,
        (t.get "t0").toNat ≤ 1 →
        limbs4 (runM64 t c).get "a0" "a1" "a2" "a3" = (if (t.get "t0").toNat = 1 then limbs4 t.get "a4" "a5" "a6" "a7" else limbs4 t.get "a0" "a1" "a2" "a3") ∧
      limbs4 (runM64 t c).get "a4" "a5" "a6" "a7" = (if (t.get "t0").toNat = 1 then limbs4 t.get "a0" "a1" "a2" "a3" else limbs4 t.get "a4" "a5" "a6" "a7") :=
  ⟨cswapPhys, cswapPhys_length ▸ decodeMStream64_encode_b _ cswapPhys_ok,
    cswapPhys_correct⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvBytesProof.feSubBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feSubBytes_correct

end Fe25519

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvBytesProof
