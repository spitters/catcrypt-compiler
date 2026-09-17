/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Proof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontsqrP384

/-!
# `bignum_montmul_p384` over address memory

`S2nMontmulP384Proof.s2nMontmulP384_correct` is stated over `runBlock`, whose memory is
keyed by base-register names. This module restates it over `AddrMem.runBlockA`, where
memory is a byte map from 64-bit addresses and an operand `[b + o]` addresses the value of
`b` plus `o`.

The pointer map `montBank` sends the banks `%rsi`, `%rcx`, `%rdi` of the block to the
entry registers `%rsi`, `%rdx`, `%rdi`. The block satisfies the address discipline for this
map (`s2nMontmulP384Block_disciplined`): at every memory access `%rsi` and `%rdi` hold
their entry values and `%rcx` holds the entry value of `%rdx`, copied by
`movq %rdx, %rcx`. Every memory read of the block precedes every memory write
(`s2nMontmulP384Block_readsPrecedeWrites`), and the
written cells `[%rdi + 0], …, [%rdi + 40]` are pairwise disjoint. By
`AddrMem.runBlockA_sim_readsBeforeWrites` the address run therefore stores what the
name-keyed run on the entry memory stores, whatever the overlap between the output buffer
and the input buffers.

`s2nMontmulP384_correct_addr` has no hypothesis relating the pointers `px`, `py`, `pz`:
disjoint buffers, `pz = px`, `pz = py`, `px = py` and partial overlaps of the 48-byte
ranges are all covered. The in-place and squaring instances are stated separately.

`s2nMontsqrP384Block` satisfies the discipline for the same map and satisfies
`readsBeforeWritesB` but not `readsPrecedeWritesB`: it stores a word at `[%rdi + 0]` and
reads it back before its final stores. Its address run agrees with its name-keyed run on
registers, flags and the written cells (`s2nMontsqrP384_sim_addr`).

## Main results

* `s2nMontmulP384_correct_addr`: the six words at `pz` after `runBlockA` hold `z < p384`
  with `z = x · y · (2^384)⁻¹` in `ZMod p384`, for the six words `x` at `px` and `y` at
  `py` before the run with `x · y ≤ 2^384 · p384`.
* `s2nMontmulP384_correct_addr_inplace_x`, `s2nMontmulP384_correct_addr_inplace_y`,
  `s2nMontmulP384_correct_addr_sqr`: the instances `pz = px`, `pz = py`, `px = py`.
* `s2nMontmulP384_frame_addr`: bytes outside `[pz, pz + 48)` keep their values.
* `s2nMontmulP384Block_disciplined`, `s2nMontmulP384Block_readsPrecedeWrites`,
  `s2nMontsqrP384Block_disciplined`, `s2nMontsqrP384Block_readsBeforeWrites`,
  `s2nMontsqrP384Block_not_readsPrecedeWrites`: the decidable conditions, by kernel
  evaluation.
* `s2nMontsqrP384_sim_addr`: the address run of the montsqr block agrees with its
  name-keyed run on registers, flags and written cells.
-/

@[expose] public section

set_option autoImplicit false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Addr

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
  (s2nMontmulP384Block mem6 p384 s2nMontmulP384_correct)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontsqrP384 (s2nMontsqrP384Block)

/-- The pointer map of s2n-bignum's P-384 kernels: the banks `%rsi`, `%rcx`, `%rdi` have
    the entry values of `%rsi`, `%rdx`, `%rdi` as base addresses. -/
def montBank (b : String) : Option String :=
  if b = "%rsi" then some "%rsi"
  else if b = "%rcx" then some "%rdx"
  else if b = "%rdi" then some "%rdi"
  else none

/-! ## The decidable conditions for the montmul block -/

theorem s2nMontmulP384Block_disciplined : disciplinedB montBank s2nMontmulP384Block = true := by
  decide +kernel

theorem s2nMontmulP384Block_readsPrecedeWrites :
    readsPrecedeWritesB s2nMontmulP384Block = true := by
  decide +kernel

theorem s2nMontmulP384Block_readsBeforeWrites :
    readsBeforeWritesB s2nMontmulP384Block = true :=
  readsBeforeWritesB_of_readsPrecedeWritesB _ s2nMontmulP384Block_readsPrecedeWrites

theorem s2nMontmulP384Block_writeKeys :
    writeKeys s2nMontmulP384Block = [0, 8, 16, 24, 32, 40].map fun o => ("%rdi", o) := by
  decide +kernel

theorem s2nMontmulP384Block_writes_separated (P : String → BitVec 64) :
    Separated montBank P (writeKeys s2nMontmulP384Block) := by
  rw [s2nMontmulP384Block_writeKeys]
  exact separated_sameBase _ _ _ _ (by decide)

/-! ## Six-word values at an address -/

/-- The value of the six little-endian words at `p, p + 8, …, p + 40`. -/
def limbs6 (m : AMem) (p : BitVec 64) : Nat :=
  (read64 m p).toNat + 2 ^ 64 * (read64 m (p + 8)).toNat + 2 ^ 128 * (read64 m (p + 16)).toNat
    + 2 ^ 192 * (read64 m (p + 24)).toNat + 2 ^ 256 * (read64 m (p + 32)).toNat
    + 2 ^ 320 * (read64 m (p + 40)).toNat

theorem mem6_absMem (P : String → BitVec 64) (m : AMem) (b : String) :
    mem6 (absMem montBank P m) b = limbs6 m (basePtr montBank P b) := by
  have h0 : ∀ p : BitVec 64, p + BitVec.ofInt 64 0 = p := fun p => by simp
  have h8 : BitVec.ofInt 64 8 = 8 := rfl
  have h16 : BitVec.ofInt 64 16 = 16 := rfl
  have h24 : BitVec.ofInt 64 24 = 24 := rfl
  have h32 : BitVec.ofInt 64 32 = 32 := rfl
  have h40 : BitVec.ofInt 64 40 = 40 := rfl
  simp only [mem6, absMem, keyAddr, limbs6, h0, h8, h16, h24, h32, h40]

theorem basePtr_rsi (P : String → BitVec 64) : basePtr montBank P "%rsi" = P "%rsi" := by
  simp [basePtr, montBank]

theorem basePtr_rcx (P : String → BitVec 64) : basePtr montBank P "%rcx" = P "%rdx" := by
  simp [basePtr, montBank]

theorem basePtr_rdi (P : String → BitVec 64) : basePtr montBank P "%rdi" = P "%rdi" := by
  simp [basePtr, montBank]

/-- The six words at the entry `%rdi` after the address run are the six words the
    name-keyed run stores in bank `%rdi`. -/
theorem s2nMontmulP384_out_eq (sa : AState) :
    limbs6 (runBlockA sa s2nMontmulP384Block).mem (sa.regs "%rdi") =
      mem6 (runBlock (jOf montBank sa) s2nMontmulP384Block).mem "%rdi" := by
  obtain ⟨-, -, hw⟩ := runBlockA_sim_readsBeforeWrites montBank _
    s2nMontmulP384Block_disciplined s2nMontmulP384Block_readsBeforeWrites sa
    (s2nMontmulP384Block_writes_separated _)
  rw [s2nMontmulP384Block_writeKeys] at hw
  generalize runBlockA sa s2nMontmulP384Block = fa at hw ⊢
  generalize runBlock (jOf montBank sa) s2nMontmulP384Block = fj at hw ⊢
  have e : ∀ o : Int, o ∈ [0, 8, 16, 24, 32, 40] →
      absMem montBank sa.regs fa.mem "%rdi" o = fj.mem "%rdi" o := fun o ho =>
    hw ("%rdi", o) (List.mem_map_of_mem ho)
  rw [← basePtr_rdi sa.regs, ← mem6_absMem]
  simp only [mem6, e 0 (by simp), e 8 (by simp), e 16 (by simp), e 24 (by simp),
    e 32 (by simp), e 40 (by simp)]

theorem s2nMontmulP384_in_x (sa : AState) :
    mem6 (jOf montBank sa).mem "%rsi" = limbs6 sa.mem (sa.regs "%rsi") := by
  rw [jOf, mem6_absMem, basePtr_rsi]

theorem s2nMontmulP384_in_y (sa : AState) :
    mem6 (jOf montBank sa).mem "%rcx" = limbs6 sa.mem (sa.regs "%rdx") := by
  rw [jOf, mem6_absMem, basePtr_rcx]

/-! ## The machine-level results over address memory -/

/-- **`bignum_montmul_p384` as imported computes the Montgomery product over address
    memory, for any placement of the buffers.** Let `%rsi`, `%rdx`, `%rdi` hold `px`, `py`,
    `pz`, and let the six words at `px` and at `py` hold `x` and `y` with
    `x · y ≤ 2^384 · p384`. After `runBlockA`, the six words at `pz` hold `z < p384` with
    `z = x · y · (2^384)⁻¹` in `ZMod p384`. No relation between `px`, `py` and `pz` is
    assumed. -/
theorem s2nMontmulP384_correct_addr (sa : AState) (px py pz : BitVec 64)
    (hx : sa.regs "%rsi" = px) (hy : sa.regs "%rdx" = py) (hz : sa.regs "%rdi" = pz)
    (hxy : limbs6 sa.mem px * limbs6 sa.mem py ≤ 2 ^ 384 * p384) :
    limbs6 (runBlockA sa s2nMontmulP384Block).mem pz < p384 ∧
      ((limbs6 (runBlockA sa s2nMontmulP384Block).mem pz : Nat) : ZMod p384)
        = (limbs6 sa.mem px : ZMod p384) * (limbs6 sa.mem py : Nat)
          * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ := by
  subst hx hy hz
  have h := s2nMontmulP384_correct (jOf montBank sa)
    (by rw [s2nMontmulP384_in_x, s2nMontmulP384_in_y]; exact hxy)
  rw [s2nMontmulP384_in_x, s2nMontmulP384_in_y] at h
  rw [s2nMontmulP384_out_eq]
  exact h

/-- **Frame.** The block changes no byte outside the 48 bytes from `pz`. -/
theorem s2nMontmulP384_frame_addr (sa : AState) (pz x : BitVec 64)
    (hz : sa.regs "%rdi" = pz) (hx : 48 ≤ (x - pz).toNat) :
    (runBlockA sa s2nMontmulP384Block).mem x = sa.mem x := by
  refine runBlockA_mem_frame montBank _ s2nMontmulP384Block_disciplined sa x ?_
  rw [s2nMontmulP384Block_writeKeys]
  intro k hk
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hk
  simp only [keyAddr, basePtr_rdi, hz, InRange8]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  have := x.isLt
  have := pz.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt] at hx ⊢
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- The in-place instance `pz = px`: the result overwrites `x`. -/
theorem s2nMontmulP384_correct_addr_inplace_x (sa : AState) (p py : BitVec 64)
    (hx : sa.regs "%rsi" = p) (hy : sa.regs "%rdx" = py) (hz : sa.regs "%rdi" = p)
    (hxy : limbs6 sa.mem p * limbs6 sa.mem py ≤ 2 ^ 384 * p384) :
    limbs6 (runBlockA sa s2nMontmulP384Block).mem p < p384 ∧
      ((limbs6 (runBlockA sa s2nMontmulP384Block).mem p : Nat) : ZMod p384)
        = (limbs6 sa.mem p : ZMod p384) * (limbs6 sa.mem py : Nat)
          * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ :=
  s2nMontmulP384_correct_addr sa p py p hx hy hz hxy

/-- The in-place instance `pz = py`: the result overwrites `y`. -/
theorem s2nMontmulP384_correct_addr_inplace_y (sa : AState) (px p : BitVec 64)
    (hx : sa.regs "%rsi" = px) (hy : sa.regs "%rdx" = p) (hz : sa.regs "%rdi" = p)
    (hxy : limbs6 sa.mem px * limbs6 sa.mem p ≤ 2 ^ 384 * p384) :
    limbs6 (runBlockA sa s2nMontmulP384Block).mem p < p384 ∧
      ((limbs6 (runBlockA sa s2nMontmulP384Block).mem p : Nat) : ZMod p384)
        = (limbs6 sa.mem px : ZMod p384) * (limbs6 sa.mem p : Nat)
          * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ :=
  s2nMontmulP384_correct_addr sa px p p hx hy hz hxy

/-- The squaring instance `px = py`: both inputs are the six words at `p`. -/
theorem s2nMontmulP384_correct_addr_sqr (sa : AState) (p pz : BitVec 64)
    (hx : sa.regs "%rsi" = p) (hy : sa.regs "%rdx" = p) (hz : sa.regs "%rdi" = pz)
    (hxx : limbs6 sa.mem p * limbs6 sa.mem p ≤ 2 ^ 384 * p384) :
    limbs6 (runBlockA sa s2nMontmulP384Block).mem pz < p384 ∧
      ((limbs6 (runBlockA sa s2nMontmulP384Block).mem pz : Nat) : ZMod p384)
        = (limbs6 sa.mem p : ZMod p384) * (limbs6 sa.mem p : Nat)
          * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ :=
  s2nMontmulP384_correct_addr sa p p pz hx hy hz hxx

/-! ## The montsqr block -/

theorem s2nMontsqrP384Block_disciplined : disciplinedB montBank s2nMontsqrP384Block = true := by
  decide +kernel

theorem s2nMontsqrP384Block_readsBeforeWrites : readsBeforeWritesB s2nMontsqrP384Block = true := by
  decide +kernel

/-- The montsqr block reads `[%rdi + 0]` after storing to it. -/
theorem s2nMontsqrP384Block_not_readsPrecedeWrites :
    readsPrecedeWritesB s2nMontsqrP384Block = false := by
  decide +kernel

theorem s2nMontsqrP384Block_writeKeys :
    writeKeys s2nMontsqrP384Block = [0, 0, 8, 16, 24, 32, 40].map fun o => ("%rdi", o) := by
  decide +kernel

/-- The address run of the montsqr block ends with the registers and flags of its
    name-keyed run on the entry memory, and each written cell holds what that run stores,
    for any placement of the input and output buffers. -/
theorem s2nMontsqrP384_sim_addr (sa : AState) :
    (runBlockA sa s2nMontsqrP384Block).regs =
        (runBlock (jOf montBank sa) s2nMontsqrP384Block).regs ∧
      (runBlockA sa s2nMontsqrP384Block).flags =
        (runBlock (jOf montBank sa) s2nMontsqrP384Block).flags ∧
      ∀ k ∈ writeKeys s2nMontsqrP384Block,
        absMem montBank sa.regs (runBlockA sa s2nMontsqrP384Block).mem k.1 k.2 =
          (runBlock (jOf montBank sa) s2nMontsqrP384Block).mem k.1 k.2 :=
  runBlockA_sim_readsBeforeWrites montBank _ s2nMontsqrP384Block_disciplined
    s2nMontsqrP384Block_readsBeforeWrites sa
    (by rw [s2nMontsqrP384Block_writeKeys]; exact separated_sameBase _ _ _ _ (by decide))

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Addr
