/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumHoare.ChainStepAxioms
import CatCrypt.Crypto.Jasmin.BignumHoare.PowP58LayerB
import CatCrypt.Crypto.Jasmin.Ed25519.InvP25519Algo

/-!
# `bignum_inv_p25519`: end-to-end `BignumTripleFuel` composition

Lifts the 12 per-block `block{N}_correctness_via_axiom` theorems
(in `ChainStepAxioms.lean`) — which produce existential
`bignumExecFuel`-form witnesses — to the `BignumTripleFuel`
predicate (defined in `PowP58LayerB.lean`).  Each lift is a tiny
deterministic-bridge proof: the axiom asserts existence of *some*
post-state `s'_ax`; `BignumTripleFuel` is universally quantified
over the actual post-state `s'` chosen by `bignumExecFuel`.  Since
`bignumExecFuel registry n body s` is a *function* (its result is
uniquely determined by inputs), `s'_ax = s'` by `Option.some.inj`.

The file then demonstrates end-to-end composition via the 12-fold
`chain_triple_fuel_compose` from `PowP58LayerB.lean §2'`,
delivering a single `BignumTripleFuel` for the full 12-block
prefix that walks `ap → z2 → z9 → z11 → z2_5_0 → z2_10_0 →
z2_20_0 → z2_40_0 → z2_50_0 → z2_100_0 → z2_200_0 → z2_250_0 →
op` of the Bernstein chain.

## Trust set delta

This file adds **0 new axioms**.  All composition is pure plumbing
above `ChainStepAxioms.lean`'s axioms.  The chain's algebraic
post (proving the result equals `a^(p-2) mod p_25519`) is *not*
addressed here — that's a Layer A concern; this file threads the
chain-algebraic Nat result symbolically.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.InvP25519Composition

open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.S2NBignumSSA
open CatCrypt.Crypto.Jasmin.BignumHoare.MontmulAxiom
open CatCrypt.Crypto.Jasmin.BignumHoare.ChainStepAxioms
open CatCrypt.Crypto.Jasmin.BignumHoare.PowP58LayerB

/-! ## §1  Block preconditions and postconditions

Each `pre_blockN` bundles the per-block hypotheses (register
bindings + 4-limb readability of inputs + output buffer
allocation) into a single `BignumState → Prop`.  Each
`post_blockN` records the chain-algebraic value at the output. -/

/-- Block 2 pre: `op`/`ap` registers bound, `ap` 4-limb-readable
    holding `a_val`, and `z2_addr` output buffer allocated. -/
def pre_block2 (op_addr ap_addr : UInt64) (a_val : Nat)
    (z2_addr : UInt64) : BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 ap_addr s.mem = some a_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_addr + UInt64.ofNat k.val) = some b)

/-- Block 2 post: `z2_addr` holds `a_val² mod p_25519`. -/
def post_block2 (z2_addr : UInt64) (a_val : Nat) : BignumState → Prop :=
  fun s' => memNat4 z2_addr s'.mem = some ((a_val * a_val) % p_25519)

/-- Block 3 pre: registers bound + `z2_addr` and `ap_addr`
    readable + `z9_addr` allocated. -/
def pre_block3 (op_addr ap_addr z2_addr : UInt64)
    (z2_val ap_val : Nat) (z9_addr : UInt64) : BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_addr s.mem = some z2_val ∧
  memNat4 ap_addr s.mem = some ap_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z9_addr + UInt64.ofNat k.val) = some b)

/-- Block 3 post: `z9_addr` holds `(z2_val^4) * ap_val mod p_25519`. -/
def post_block3 (z9_addr : UInt64) (z2_val ap_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z9_addr s'.mem = some (((z2_val ^ (2^2)) * ap_val) % p_25519)

/-- Block 4 pre: registers bound + `z9_addr` and `z2_addr`
    readable + `z11_addr` allocated. -/
def pre_block4 (op_addr ap_addr z9_addr z2_addr : UInt64)
    (z9_val z2_val : Nat) (z11_addr : UInt64) : BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z9_addr s.mem = some z9_val ∧
  memNat4 z2_addr s.mem = some z2_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z11_addr + UInt64.ofNat k.val) = some b)

/-- Block 4 post: `z11_addr` holds `z9_val * z2_val mod p_25519`. -/
def post_block4 (z11_addr : UInt64) (z9_val z2_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z11_addr s'.mem = some ((z9_val * z2_val) % p_25519)

/-- Block 5 pre: registers + `z11`, `z9` readable + `z2_5_0` allocated. -/
def pre_block5 (op_addr ap_addr z11_addr z9_addr : UInt64)
    (z11_val z9_val : Nat) (z2_5_0_addr : UInt64) :
    BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z11_addr s.mem = some z11_val ∧
  memNat4 z9_addr s.mem = some z9_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_5_0_addr + UInt64.ofNat k.val) = some b)

/-- Block 5 post: `z2_5_0` holds `(z11^2) * z9 mod p_25519`. -/
def post_block5 (z2_5_0_addr : UInt64) (z11_val z9_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z2_5_0_addr s'.mem = some (((z11_val ^ (2^1)) * z9_val) % p_25519)

/-- Block 6 pre. -/
def pre_block6 (op_addr ap_addr z2_5_0_addr : UInt64)
    (z2_5_0_val : Nat) (z2_10_0_addr : UInt64) :
    BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_5_0_addr s.mem = some z2_5_0_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_10_0_addr + UInt64.ofNat k.val) = some b)

/-- Block 6 post. -/
def post_block6 (z2_10_0_addr : UInt64) (z2_5_0_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z2_10_0_addr s'.mem =
    some (((z2_5_0_val ^ (2^5)) * z2_5_0_val) % p_25519)

/-- Block 7 pre. -/
def pre_block7 (op_addr ap_addr z2_10_0_addr : UInt64)
    (z2_10_0_val : Nat) (z2_20_0_addr : UInt64) :
    BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_10_0_addr s.mem = some z2_10_0_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_20_0_addr + UInt64.ofNat k.val) = some b)

/-- Block 7 post. -/
def post_block7 (z2_20_0_addr : UInt64) (z2_10_0_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z2_20_0_addr s'.mem =
    some (((z2_10_0_val ^ (2^10)) * z2_10_0_val) % p_25519)

/-- Block 8 pre. -/
def pre_block8 (op_addr ap_addr z2_20_0_addr : UInt64)
    (z2_20_0_val : Nat) (z2_40_0_addr : UInt64) :
    BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_20_0_addr s.mem = some z2_20_0_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_40_0_addr + UInt64.ofNat k.val) = some b)

/-- Block 8 post. -/
def post_block8 (z2_40_0_addr : UInt64) (z2_20_0_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z2_40_0_addr s'.mem =
    some (((z2_20_0_val ^ (2^20)) * z2_20_0_val) % p_25519)

/-- Block 9 pre. -/
def pre_block9 (op_addr ap_addr z2_40_0_addr z2_10_0_addr : UInt64)
    (z2_40_0_val z2_10_0_val : Nat) (z2_50_0_addr : UInt64) :
    BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_40_0_addr s.mem = some z2_40_0_val ∧
  memNat4 z2_10_0_addr s.mem = some z2_10_0_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_50_0_addr + UInt64.ofNat k.val) = some b)

/-- Block 9 post. -/
def post_block9 (z2_50_0_addr : UInt64) (z2_40_0_val z2_10_0_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z2_50_0_addr s'.mem =
    some (((z2_40_0_val ^ (2^10)) * z2_10_0_val) % p_25519)

/-- Block 10 pre. -/
def pre_block10 (op_addr ap_addr z2_50_0_addr : UInt64)
    (z2_50_0_val : Nat) (z2_100_0_addr : UInt64) :
    BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_50_0_addr s.mem = some z2_50_0_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_100_0_addr + UInt64.ofNat k.val) = some b)

/-- Block 10 post. -/
def post_block10 (z2_100_0_addr : UInt64) (z2_50_0_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z2_100_0_addr s'.mem =
    some (((z2_50_0_val ^ (2^50)) * z2_50_0_val) % p_25519)

/-- Block 11 pre. -/
def pre_block11 (op_addr ap_addr z2_100_0_addr : UInt64)
    (z2_100_0_val : Nat) (z2_200_0_addr : UInt64) :
    BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_100_0_addr s.mem = some z2_100_0_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_200_0_addr + UInt64.ofNat k.val) = some b)

/-- Block 11 post. -/
def post_block11 (z2_200_0_addr : UInt64) (z2_100_0_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z2_200_0_addr s'.mem =
    some (((z2_100_0_val ^ (2^100)) * z2_100_0_val) % p_25519)

/-- Block 12 pre. -/
def pre_block12 (op_addr ap_addr z2_200_0_addr z2_50_0_addr : UInt64)
    (z2_200_0_val z2_50_0_val : Nat) (z2_250_0_addr : UInt64) :
    BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_200_0_addr s.mem = some z2_200_0_val ∧
  memNat4 z2_50_0_addr s.mem = some z2_50_0_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (z2_250_0_addr + UInt64.ofNat k.val) = some b)

/-- Block 12 post. -/
def post_block12 (z2_250_0_addr : UInt64) (z2_200_0_val z2_50_0_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 z2_250_0_addr s'.mem =
    some (((z2_200_0_val ^ (2^50)) * z2_50_0_val) % p_25519)

/-- Block 13 pre (terminal step writing to `op_addr`). -/
def pre_block13 (op_addr ap_addr z2_250_0_addr z11_addr : UInt64)
    (z2_250_0_val z11_val : Nat) : BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_250_0_addr s.mem = some z2_250_0_val ∧
  memNat4 z11_addr s.mem = some z11_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)

/-- Block 13 post: the final result lands at `op_addr`. -/
def post_block13 (op_addr : UInt64) (z2_250_0_val z11_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 op_addr s'.mem =
    some (((z2_250_0_val ^ (2^5)) * z11_val) % p_25519)

/-! ## §2  Determinism bridge — existential axiom → `BignumTripleFuel`

Each lift follows the same shape: discharge `fuel = 0` (impossible
since `bignumExecFuel registry 0 _ _ = none`) and `fuel = succ n`
(apply the axiom with `fuel := n`, conclude `s'_ax = s'` by
`Option.some.inj`). -/

theorem block2_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr : UInt64)
    (a_val : Nat)
    (z2_addr : UInt64)
    (h_z2_addr_eq :
      BitVec.ofNat 64 z2_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2)
    (sqr_body : List InstrR)
    (h_shape : sqr_body = BignumInvP25519.sqr_step 0
      BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap) :
    BignumTripleFuel registry
      (pre_block2 op_addr ap_addr a_val z2_addr)
      sqr_body
      (post_block2 z2_addr a_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_a_mem, h_z2_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block2_correctness_via_axiom registry h_registry s n
        op_addr ap_addr h_op h_ap a_val h_a_mem z2_addr h_z2_alloc
        h_z2_addr_eq sqr_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block2, h_eq] using h_ax_post

theorem block3_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_addr : UInt64)
    (z2_val ap_val : Nat)
    (z9_addr : UInt64)
    (h_z9_addr_eq : BitVec.ofNat 64 z9_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z9)
    (h_z2_addr_eq : BitVec.ofNat 64 z2_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2)
    (mkScratch : ∀ s : BignumState, RsmScratch s op_addr z9_addr z2_addr ap_addr)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul 1
        BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2
        BignumInvP25519.OFF_ap 2).fst) :
    BignumTripleFuel registry
      (pre_block3 op_addr ap_addr z2_addr z2_val ap_val z9_addr)
      rsm_body
      (post_block3 z9_addr z2_val ap_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_mem, h_ap_mem, h_z9_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block3_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_addr z9_addr h_op h_ap
        z2_val ap_val h_z2_mem h_ap_mem h_z9_alloc h_z9_addr_eq
        h_z2_addr_eq (mkScratch s) rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block3, h_eq] using h_ax_post

theorem block4_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z9_addr z2_addr : UInt64)
    (z9_val z2_val : Nat)
    (z11_addr : UInt64)
    (h_z11_addr_eq :
      BitVec.ofNat 64 z11_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z11)
    (h_z9_addr_eq :
      BitVec.ofNat 64 z9_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z9)
    (h_z2_addr_eq :
      BitVec.ofNat 64 z2_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2)
    (idx : Nat)
    (mul_body : List InstrR)
    (h_shape : mul_body = BignumInvP25519.mul_step idx
      BignumInvP25519.OFF_z11 BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2) :
    BignumTripleFuel registry
      (pre_block4 op_addr ap_addr z9_addr z2_addr z9_val z2_val z11_addr)
      mul_body
      (post_block4 z11_addr z9_val z2_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z9_mem, h_z2_mem, h_z11_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block4_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z9_addr z2_addr z11_addr h_op h_ap
        z9_val z2_val h_z9_mem h_z2_mem h_z11_alloc
        h_z11_addr_eq h_z9_addr_eq h_z2_addr_eq idx mul_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block4, h_eq] using h_ax_post

theorem block5_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z11_addr z9_addr : UInt64)
    (z11_val z9_val : Nat)
    (z2_5_0_addr : UInt64)
    (h_z2_5_0_addr_eq : BitVec.ofNat 64 z2_5_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_5_0)
    (h_z11_addr_eq : BitVec.ofNat 64 z11_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z11)
    (h_z9_addr_eq : BitVec.ofNat 64 z9_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z9)
    (mkScratch : ∀ s : BignumState, RsmScratch s op_addr z2_5_0_addr z11_addr z9_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_5_0 BignumInvP25519.OFF_z11
        BignumInvP25519.OFF_z9 1).fst) :
    BignumTripleFuel registry
      (pre_block5 op_addr ap_addr z11_addr z9_addr z11_val z9_val z2_5_0_addr)
      rsm_body
      (post_block5 z2_5_0_addr z11_val z9_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z11_mem, h_z9_mem, h_z2_5_0_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block5_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z11_addr z9_addr z2_5_0_addr h_op h_ap
        z11_val z9_val h_z11_mem h_z9_mem h_z2_5_0_alloc
        h_z2_5_0_addr_eq h_z11_addr_eq h_z9_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block5, h_eq] using h_ax_post

theorem block6_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_5_0_addr : UInt64)
    (z2_5_0_val : Nat)
    (z2_10_0_addr : UInt64)
    (h_z2_10_0_addr_eq : BitVec.ofNat 64 z2_10_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_10_0)
    (h_z2_5_0_addr_eq : BitVec.ofNat 64 z2_5_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_5_0)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr z2_10_0_addr z2_5_0_addr z2_5_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_10_0 BignumInvP25519.OFF_z2_5_0
        BignumInvP25519.OFF_z2_5_0 5).fst) :
    BignumTripleFuel registry
      (pre_block6 op_addr ap_addr z2_5_0_addr z2_5_0_val z2_10_0_addr)
      rsm_body
      (post_block6 z2_10_0_addr z2_5_0_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_5_0_mem, h_z2_10_0_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block6_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_5_0_addr z2_10_0_addr h_op h_ap
        z2_5_0_val h_z2_5_0_mem h_z2_10_0_alloc
        h_z2_10_0_addr_eq h_z2_5_0_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block6, h_eq] using h_ax_post

theorem block7_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_10_0_addr : UInt64)
    (z2_10_0_val : Nat)
    (z2_20_0_addr : UInt64)
    (h_z2_20_0_addr_eq : BitVec.ofNat 64 z2_20_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_20_0)
    (h_z2_10_0_addr_eq : BitVec.ofNat 64 z2_10_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_10_0)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr z2_20_0_addr z2_10_0_addr z2_10_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_20_0 BignumInvP25519.OFF_z2_10_0
        BignumInvP25519.OFF_z2_10_0 10).fst) :
    BignumTripleFuel registry
      (pre_block7 op_addr ap_addr z2_10_0_addr z2_10_0_val z2_20_0_addr)
      rsm_body
      (post_block7 z2_20_0_addr z2_10_0_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_10_0_mem, h_z2_20_0_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block7_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_10_0_addr z2_20_0_addr h_op h_ap
        z2_10_0_val h_z2_10_0_mem h_z2_20_0_alloc
        h_z2_20_0_addr_eq h_z2_10_0_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block7, h_eq] using h_ax_post

theorem block8_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_20_0_addr : UInt64)
    (z2_20_0_val : Nat)
    (z2_40_0_addr : UInt64)
    (h_z2_40_0_addr_eq : BitVec.ofNat 64 z2_40_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_40_0)
    (h_z2_20_0_addr_eq : BitVec.ofNat 64 z2_20_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_20_0)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr z2_40_0_addr z2_20_0_addr z2_20_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_40_0 BignumInvP25519.OFF_z2_20_0
        BignumInvP25519.OFF_z2_20_0 20).fst) :
    BignumTripleFuel registry
      (pre_block8 op_addr ap_addr z2_20_0_addr z2_20_0_val z2_40_0_addr)
      rsm_body
      (post_block8 z2_40_0_addr z2_20_0_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_20_0_mem, h_z2_40_0_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block8_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_20_0_addr z2_40_0_addr h_op h_ap
        z2_20_0_val h_z2_20_0_mem h_z2_40_0_alloc
        h_z2_40_0_addr_eq h_z2_20_0_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block8, h_eq] using h_ax_post

theorem block9_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_40_0_addr z2_10_0_addr : UInt64)
    (z2_40_0_val z2_10_0_val : Nat)
    (z2_50_0_addr : UInt64)
    (h_z2_50_0_addr_eq : BitVec.ofNat 64 z2_50_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_50_0)
    (h_z2_40_0_addr_eq : BitVec.ofNat 64 z2_40_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_40_0)
    (h_z2_10_0_addr_eq : BitVec.ofNat 64 z2_10_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_10_0)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr z2_50_0_addr z2_40_0_addr z2_10_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_50_0 BignumInvP25519.OFF_z2_40_0
        BignumInvP25519.OFF_z2_10_0 10).fst) :
    BignumTripleFuel registry
      (pre_block9 op_addr ap_addr z2_40_0_addr z2_10_0_addr
        z2_40_0_val z2_10_0_val z2_50_0_addr)
      rsm_body
      (post_block9 z2_50_0_addr z2_40_0_val z2_10_0_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_40_0_mem, h_z2_10_0_mem, h_z2_50_0_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block9_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_40_0_addr z2_10_0_addr z2_50_0_addr h_op h_ap
        z2_40_0_val z2_10_0_val h_z2_40_0_mem h_z2_10_0_mem
        h_z2_50_0_alloc h_z2_50_0_addr_eq h_z2_40_0_addr_eq h_z2_10_0_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block9, h_eq] using h_ax_post

theorem block10_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_50_0_addr : UInt64)
    (z2_50_0_val : Nat)
    (z2_100_0_addr : UInt64)
    (h_z2_100_0_addr_eq : BitVec.ofNat 64 z2_100_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_100_0)
    (h_z2_50_0_addr_eq : BitVec.ofNat 64 z2_50_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_50_0)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr z2_100_0_addr z2_50_0_addr z2_50_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_100_0 BignumInvP25519.OFF_z2_50_0
        BignumInvP25519.OFF_z2_50_0 50).fst) :
    BignumTripleFuel registry
      (pre_block10 op_addr ap_addr z2_50_0_addr z2_50_0_val z2_100_0_addr)
      rsm_body
      (post_block10 z2_100_0_addr z2_50_0_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_50_0_mem, h_z2_100_0_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block10_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_50_0_addr z2_100_0_addr h_op h_ap
        z2_50_0_val h_z2_50_0_mem h_z2_100_0_alloc
        h_z2_100_0_addr_eq h_z2_50_0_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block10, h_eq] using h_ax_post

theorem block11_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_100_0_addr : UInt64)
    (z2_100_0_val : Nat)
    (z2_200_0_addr : UInt64)
    (h_z2_200_0_addr_eq : BitVec.ofNat 64 z2_200_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_200_0)
    (h_z2_100_0_addr_eq : BitVec.ofNat 64 z2_100_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_100_0)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr z2_200_0_addr z2_100_0_addr z2_100_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_200_0 BignumInvP25519.OFF_z2_100_0
        BignumInvP25519.OFF_z2_100_0 100).fst) :
    BignumTripleFuel registry
      (pre_block11 op_addr ap_addr z2_100_0_addr z2_100_0_val z2_200_0_addr)
      rsm_body
      (post_block11 z2_200_0_addr z2_100_0_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_100_0_mem, h_z2_200_0_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block11_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_100_0_addr z2_200_0_addr h_op h_ap
        z2_100_0_val h_z2_100_0_mem h_z2_200_0_alloc
        h_z2_200_0_addr_eq h_z2_100_0_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block11, h_eq] using h_ax_post

theorem block12_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_200_0_addr z2_50_0_addr : UInt64)
    (z2_200_0_val z2_50_0_val : Nat)
    (z2_250_0_addr : UInt64)
    (h_z2_250_0_addr_eq : BitVec.ofNat 64 z2_250_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_250_0)
    (h_z2_200_0_addr_eq : BitVec.ofNat 64 z2_200_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_200_0)
    (h_z2_50_0_addr_eq : BitVec.ofNat 64 z2_50_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_50_0)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr z2_250_0_addr z2_200_0_addr z2_50_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_250_0 BignumInvP25519.OFF_z2_200_0
        BignumInvP25519.OFF_z2_50_0 50).fst) :
    BignumTripleFuel registry
      (pre_block12 op_addr ap_addr z2_200_0_addr z2_50_0_addr
        z2_200_0_val z2_50_0_val z2_250_0_addr)
      rsm_body
      (post_block12 z2_250_0_addr z2_200_0_val z2_50_0_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_200_0_mem, h_z2_50_0_mem, h_z2_250_0_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block12_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_200_0_addr z2_50_0_addr z2_250_0_addr h_op h_ap
        z2_200_0_val z2_50_0_val h_z2_200_0_mem h_z2_50_0_mem
        h_z2_250_0_alloc h_z2_250_0_addr_eq h_z2_200_0_addr_eq h_z2_50_0_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block12, h_eq] using h_ax_post

theorem block13_correctness_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr z2_250_0_addr z11_addr : UInt64)
    (z2_250_0_val z11_val : Nat)
    (h_z2_250_0_addr_eq : BitVec.ofNat 64 z2_250_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_250_0)
    (h_z11_addr_eq : BitVec.ofNat 64 z11_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z11)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr op_addr z2_250_0_addr z11_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_op BignumInvP25519.OFF_z2_250_0
        BignumInvP25519.OFF_z11 5).fst) :
    BignumTripleFuel registry
      (pre_block13 op_addr ap_addr z2_250_0_addr z11_addr z2_250_0_val z11_val)
      rsm_body
      (post_block13 op_addr z2_250_0_val z11_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_250_0_mem, h_z11_mem, h_op_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block13_correctness_via_axiom registry h_registry s n
        op_addr ap_addr z2_250_0_addr z11_addr h_op h_ap
        z2_250_0_val z11_val h_z2_250_0_mem h_z11_mem h_op_alloc
        h_z2_250_0_addr_eq h_z11_addr_eq
        (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block13, h_eq] using h_ax_post

/-! ## §3  End-to-end composition

Composes the 12 per-block triples via `chain_triple_fuel_compose`
(13-fold version), yielding a single `BignumTripleFuel` for the
concatenated body `b2 ++ b3 ++ ... ++ b13`.

Each per-block triple's post becomes the next block's pre via the
caller-supplied bridging hypotheses (the chain's intermediate
register/memory invariants — block N+1 needs block N's output to
be readable, plus the next block's destination buffer to be
allocated).

Note: we do NOT close that the final `op_addr` value equals
`a^(p−2) mod p_25519`.  That's a Layer A (chain-algebraic)
concern; here we just thread the chain's symbolic Nat result
(`((z2_200_0_val ^ 2^50) * z2_50_0_val) ^ 2^5 * z11_val`-style)
through.

The bridging hypotheses are the per-block "weaken pre / strengthen
post" wirings — given as explicit predicate-implication arguments
`bridge_3_4`, etc. -/

/-- 12-block end-to-end Hoare triple via `chain_triple_fuel_compose`.

    The 12 input bodies `b2..b13` are caller-supplied (the actual
    chain bodies live behind `BignumInvP25519.body` private
    helpers).  The 11 bridging `bridge_*` hypotheses connect each
    block's post to the next block's pre — they assert that the
    post-state's memory invariants subsume the next block's
    pre-state assumptions (typically established by frame-condition
    reasoning: each block's writes don't disturb earlier outputs).

    Compose via 12-fold `chain_triple_fuel_compose`. -/
theorem inv_p25519_chain_triple
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr : UInt64)
    (a_val : Nat)
    (z2_addr z9_addr z11_addr z2_5_0_addr z2_10_0_addr
     z2_20_0_addr z2_40_0_addr z2_50_0_addr z2_100_0_addr
     z2_200_0_addr z2_250_0_addr : UInt64)
    -- Chain-algebraic intermediate values (existentially
    -- threaded; named for the chain's exponent table).
    (z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
     z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
     : Nat)
    -- 12 caller-supplied block bodies.
    (b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : List InstrR)
    -- Address-derivation hypotheses for each chain output.
    (h_z2_addr_eq :
      BitVec.ofNat 64 z2_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2)
    (h_z9_addr_eq :
      BitVec.ofNat 64 z9_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z9)
    (h_z11_addr_eq :
      BitVec.ofNat 64 z11_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z11)
    (h_z2_5_0_addr_eq :
      BitVec.ofNat 64 z2_5_0_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_5_0)
    (h_z2_10_0_addr_eq :
      BitVec.ofNat 64 z2_10_0_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_10_0)
    (h_z2_20_0_addr_eq :
      BitVec.ofNat 64 z2_20_0_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_20_0)
    (h_z2_40_0_addr_eq :
      BitVec.ofNat 64 z2_40_0_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_40_0)
    (h_z2_50_0_addr_eq :
      BitVec.ofNat 64 z2_50_0_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_50_0)
    (h_z2_100_0_addr_eq :
      BitVec.ofNat 64 z2_100_0_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_100_0)
    (h_z2_200_0_addr_eq :
      BitVec.ofNat 64 z2_200_0_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_200_0)
    (h_z2_250_0_addr_eq :
      BitVec.ofNat 64 z2_250_0_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_250_0)
    (h_op_addr_eq :
      BitVec.ofNat 64 op_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_op)
    -- Scratch builders for each rsm block (caller supplies allocation +
    -- non-aliasing evidence per state).
    (mkScratch3  : ∀ s, RsmScratch s op_addr z9_addr      z2_addr     ap_addr)
    (mkScratch5  : ∀ s, RsmScratch s op_addr z2_5_0_addr  z11_addr    z9_addr)
    (mkScratch6  : ∀ s, RsmScratch s op_addr z2_10_0_addr z2_5_0_addr z2_5_0_addr)
    (mkScratch7  : ∀ s, RsmScratch s op_addr z2_20_0_addr z2_10_0_addr z2_10_0_addr)
    (mkScratch8  : ∀ s, RsmScratch s op_addr z2_40_0_addr z2_20_0_addr z2_20_0_addr)
    (mkScratch9  : ∀ s, RsmScratch s op_addr z2_50_0_addr z2_40_0_addr z2_10_0_addr)
    (mkScratch10 : ∀ s, RsmScratch s op_addr z2_100_0_addr z2_50_0_addr z2_50_0_addr)
    (mkScratch11 : ∀ s, RsmScratch s op_addr z2_200_0_addr z2_100_0_addr z2_100_0_addr)
    (mkScratch12 : ∀ s, RsmScratch s op_addr z2_250_0_addr z2_200_0_addr z2_50_0_addr)
    (mkScratch13 : ∀ s, RsmScratch s op_addr op_addr      z2_250_0_addr z11_addr)
    -- Body-shape hypotheses (b2 sqr_step, b4 mul_step, rest rsm).
    (h_b2_shape : b2 = BignumInvP25519.sqr_step 0
      BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap)
    (b4_idx : Nat)
    (h_b4_shape : b4 = BignumInvP25519.mul_step b4_idx
      BignumInvP25519.OFF_z11 BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2)
    (b5_startIdx b6_startIdx b7_startIdx b8_startIdx b9_startIdx
       b10_startIdx b11_startIdx b12_startIdx b13_startIdx : Nat)
    (h_b3_shape : b3 =
      (BignumInvP25519.repeated_sqr_then_mul 1
        BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2
        BignumInvP25519.OFF_ap 2).fst)
    (h_b5_shape : b5 =
      (BignumInvP25519.repeated_sqr_then_mul b5_startIdx
        BignumInvP25519.OFF_z2_5_0 BignumInvP25519.OFF_z11
        BignumInvP25519.OFF_z9 1).fst)
    (h_b6_shape : b6 =
      (BignumInvP25519.repeated_sqr_then_mul b6_startIdx
        BignumInvP25519.OFF_z2_10_0 BignumInvP25519.OFF_z2_5_0
        BignumInvP25519.OFF_z2_5_0 5).fst)
    (h_b7_shape : b7 =
      (BignumInvP25519.repeated_sqr_then_mul b7_startIdx
        BignumInvP25519.OFF_z2_20_0 BignumInvP25519.OFF_z2_10_0
        BignumInvP25519.OFF_z2_10_0 10).fst)
    (h_b8_shape : b8 =
      (BignumInvP25519.repeated_sqr_then_mul b8_startIdx
        BignumInvP25519.OFF_z2_40_0 BignumInvP25519.OFF_z2_20_0
        BignumInvP25519.OFF_z2_20_0 20).fst)
    (h_b9_shape : b9 =
      (BignumInvP25519.repeated_sqr_then_mul b9_startIdx
        BignumInvP25519.OFF_z2_50_0 BignumInvP25519.OFF_z2_40_0
        BignumInvP25519.OFF_z2_10_0 10).fst)
    (h_b10_shape : b10 =
      (BignumInvP25519.repeated_sqr_then_mul b10_startIdx
        BignumInvP25519.OFF_z2_100_0 BignumInvP25519.OFF_z2_50_0
        BignumInvP25519.OFF_z2_50_0 50).fst)
    (h_b11_shape : b11 =
      (BignumInvP25519.repeated_sqr_then_mul b11_startIdx
        BignumInvP25519.OFF_z2_200_0 BignumInvP25519.OFF_z2_100_0
        BignumInvP25519.OFF_z2_100_0 100).fst)
    (h_b12_shape : b12 =
      (BignumInvP25519.repeated_sqr_then_mul b12_startIdx
        BignumInvP25519.OFF_z2_250_0 BignumInvP25519.OFF_z2_200_0
        BignumInvP25519.OFF_z2_50_0 50).fst)
    (h_b13_shape : b13 =
      (BignumInvP25519.repeated_sqr_then_mul b13_startIdx
        BignumInvP25519.OFF_op BignumInvP25519.OFF_z2_250_0
        BignumInvP25519.OFF_z11 5).fst)
    -- 11 bridging implications: post of block N implies pre of
    -- block N+1.  These are caller-supplied; in practice they
    -- follow from frame conditions on each block plus the chain's
    -- algebraic identity at each step.
    (bridge_2_3 : ∀ s,
      post_block2 z2_addr a_val s →
      pre_block3 op_addr ap_addr z2_addr z2_val a_val z9_addr s)
    (bridge_3_4 : ∀ s,
      post_block3 z9_addr z2_val a_val s →
      pre_block4 op_addr ap_addr z9_addr z2_addr z9_val z2_val z11_addr s)
    (bridge_4_5 : ∀ s,
      post_block4 z11_addr z9_val z2_val s →
      pre_block5 op_addr ap_addr z11_addr z9_addr z11_val z9_val z2_5_0_addr s)
    (bridge_5_6 : ∀ s,
      post_block5 z2_5_0_addr z11_val z9_val s →
      pre_block6 op_addr ap_addr z2_5_0_addr z2_5_0_val z2_10_0_addr s)
    (bridge_6_7 : ∀ s,
      post_block6 z2_10_0_addr z2_5_0_val s →
      pre_block7 op_addr ap_addr z2_10_0_addr z2_10_0_val z2_20_0_addr s)
    (bridge_7_8 : ∀ s,
      post_block7 z2_20_0_addr z2_10_0_val s →
      pre_block8 op_addr ap_addr z2_20_0_addr z2_20_0_val z2_40_0_addr s)
    (bridge_8_9 : ∀ s,
      post_block8 z2_40_0_addr z2_20_0_val s →
      pre_block9 op_addr ap_addr z2_40_0_addr z2_10_0_addr
        z2_40_0_val z2_10_0_val z2_50_0_addr s)
    (bridge_9_10 : ∀ s,
      post_block9 z2_50_0_addr z2_40_0_val z2_10_0_val s →
      pre_block10 op_addr ap_addr z2_50_0_addr z2_50_0_val z2_100_0_addr s)
    (bridge_10_11 : ∀ s,
      post_block10 z2_100_0_addr z2_50_0_val s →
      pre_block11 op_addr ap_addr z2_100_0_addr z2_100_0_val z2_200_0_addr s)
    (bridge_11_12 : ∀ s,
      post_block11 z2_200_0_addr z2_100_0_val s →
      pre_block12 op_addr ap_addr z2_200_0_addr z2_50_0_addr
        z2_200_0_val z2_50_0_val z2_250_0_addr s)
    (bridge_12_13 : ∀ s,
      post_block12 z2_250_0_addr z2_200_0_val z2_50_0_val s →
      pre_block13 op_addr ap_addr z2_250_0_addr z11_addr z2_250_0_val z11_val s) :
    BignumTripleFuel registry
      (pre_block2 op_addr ap_addr a_val z2_addr)
      (b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9 ++ b10 ++
       b11 ++ b12 ++ b13)
      (post_block13 op_addr z2_250_0_val z11_val) := by
  -- Apply each block's lifted triple, weakening the post via the
  -- bridging hypothesis to match the next block's pre.
  have h2 : BignumTripleFuel registry
      (pre_block2 op_addr ap_addr a_val z2_addr) b2
      (pre_block3 op_addr ap_addr z2_addr z2_val a_val z9_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_2_3
      (block2_correctness_triple registry h_registry op_addr ap_addr a_val
        z2_addr h_z2_addr_eq b2 h_b2_shape)
  have h3 : BignumTripleFuel registry
      (pre_block3 op_addr ap_addr z2_addr z2_val a_val z9_addr) b3
      (pre_block4 op_addr ap_addr z9_addr z2_addr z9_val z2_val z11_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_3_4
      (block3_correctness_triple registry h_registry op_addr ap_addr z2_addr
        z2_val a_val z9_addr h_z9_addr_eq h_z2_addr_eq mkScratch3 b3 h_b3_shape)
  have h4 : BignumTripleFuel registry
      (pre_block4 op_addr ap_addr z9_addr z2_addr z9_val z2_val z11_addr) b4
      (pre_block5 op_addr ap_addr z11_addr z9_addr z11_val z9_val z2_5_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_4_5
      (block4_correctness_triple registry h_registry op_addr ap_addr z9_addr
        z2_addr z9_val z2_val z11_addr
        h_z11_addr_eq h_z9_addr_eq h_z2_addr_eq b4_idx b4 h_b4_shape)
  have h5 : BignumTripleFuel registry
      (pre_block5 op_addr ap_addr z11_addr z9_addr z11_val z9_val z2_5_0_addr) b5
      (pre_block6 op_addr ap_addr z2_5_0_addr z2_5_0_val z2_10_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_5_6
      (block5_correctness_triple registry h_registry op_addr ap_addr z11_addr
        z9_addr z11_val z9_val z2_5_0_addr h_z2_5_0_addr_eq
        h_z11_addr_eq h_z9_addr_eq mkScratch5
        b5_startIdx b5 h_b5_shape)
  have h6 : BignumTripleFuel registry
      (pre_block6 op_addr ap_addr z2_5_0_addr z2_5_0_val z2_10_0_addr) b6
      (pre_block7 op_addr ap_addr z2_10_0_addr z2_10_0_val z2_20_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_6_7
      (block6_correctness_triple registry h_registry op_addr ap_addr
        z2_5_0_addr z2_5_0_val z2_10_0_addr h_z2_10_0_addr_eq h_z2_5_0_addr_eq
        mkScratch6 b6_startIdx b6 h_b6_shape)
  have h7 : BignumTripleFuel registry
      (pre_block7 op_addr ap_addr z2_10_0_addr z2_10_0_val z2_20_0_addr) b7
      (pre_block8 op_addr ap_addr z2_20_0_addr z2_20_0_val z2_40_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_7_8
      (block7_correctness_triple registry h_registry op_addr ap_addr
        z2_10_0_addr z2_10_0_val z2_20_0_addr h_z2_20_0_addr_eq h_z2_10_0_addr_eq
        mkScratch7 b7_startIdx b7 h_b7_shape)
  have h8 : BignumTripleFuel registry
      (pre_block8 op_addr ap_addr z2_20_0_addr z2_20_0_val z2_40_0_addr) b8
      (pre_block9 op_addr ap_addr z2_40_0_addr z2_10_0_addr
        z2_40_0_val z2_10_0_val z2_50_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_8_9
      (block8_correctness_triple registry h_registry op_addr ap_addr
        z2_20_0_addr z2_20_0_val z2_40_0_addr h_z2_40_0_addr_eq h_z2_20_0_addr_eq
        mkScratch8 b8_startIdx b8 h_b8_shape)
  have h9 : BignumTripleFuel registry
      (pre_block9 op_addr ap_addr z2_40_0_addr z2_10_0_addr
        z2_40_0_val z2_10_0_val z2_50_0_addr) b9
      (pre_block10 op_addr ap_addr z2_50_0_addr z2_50_0_val z2_100_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_9_10
      (block9_correctness_triple registry h_registry op_addr ap_addr
        z2_40_0_addr z2_10_0_addr z2_40_0_val z2_10_0_val z2_50_0_addr
        h_z2_50_0_addr_eq h_z2_40_0_addr_eq h_z2_10_0_addr_eq
        mkScratch9 b9_startIdx b9 h_b9_shape)
  have h10 : BignumTripleFuel registry
      (pre_block10 op_addr ap_addr z2_50_0_addr z2_50_0_val z2_100_0_addr) b10
      (pre_block11 op_addr ap_addr z2_100_0_addr z2_100_0_val z2_200_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_10_11
      (block10_correctness_triple registry h_registry op_addr ap_addr
        z2_50_0_addr z2_50_0_val z2_100_0_addr h_z2_100_0_addr_eq h_z2_50_0_addr_eq
        mkScratch10 b10_startIdx b10 h_b10_shape)
  have h11 : BignumTripleFuel registry
      (pre_block11 op_addr ap_addr z2_100_0_addr z2_100_0_val z2_200_0_addr) b11
      (pre_block12 op_addr ap_addr z2_200_0_addr z2_50_0_addr
        z2_200_0_val z2_50_0_val z2_250_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_11_12
      (block11_correctness_triple registry h_registry op_addr ap_addr
        z2_100_0_addr z2_100_0_val z2_200_0_addr h_z2_200_0_addr_eq
        h_z2_100_0_addr_eq mkScratch11 b11_startIdx b11 h_b11_shape)
  have h12 : BignumTripleFuel registry
      (pre_block12 op_addr ap_addr z2_200_0_addr z2_50_0_addr
        z2_200_0_val z2_50_0_val z2_250_0_addr) b12
      (pre_block13 op_addr ap_addr z2_250_0_addr z11_addr
        z2_250_0_val z11_val) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_12_13
      (block12_correctness_triple registry h_registry op_addr ap_addr
        z2_200_0_addr z2_50_0_addr z2_200_0_val z2_50_0_val z2_250_0_addr
        h_z2_250_0_addr_eq h_z2_200_0_addr_eq h_z2_50_0_addr_eq
        mkScratch12 b12_startIdx b12 h_b12_shape)
  have h13 : BignumTripleFuel registry
      (pre_block13 op_addr ap_addr z2_250_0_addr z11_addr z2_250_0_val z11_val) b13
      (post_block13 op_addr z2_250_0_val z11_val) :=
    block13_correctness_triple registry h_registry op_addr ap_addr
      z2_250_0_addr z11_addr z2_250_0_val z11_val
      h_z2_250_0_addr_eq h_z11_addr_eq
      mkScratch13 b13_startIdx b13 h_b13_shape
  -- 12-fold sequential composition via .seq, chained left-
  -- associatively to match `++`'s left-associative parsing
  -- (`b2 ++ b3 ++ b4 ++ ... ++ b13` parses as
  -- `((((b2 ++ b3) ++ b4) ++ ... ) ++ b13)`).
  have h23 := h2.seq h3
  have h234 := h23.seq h4
  have h2345 := h234.seq h5
  have h23456 := h2345.seq h6
  have h234567 := h23456.seq h7
  have h2_8 := h234567.seq h8
  have h2_9 := h2_8.seq h9
  have h2_10 := h2_9.seq h10
  have h2_11 := h2_10.seq h11
  have h2_12 := h2_11.seq h12
  exact h2_12.seq h13

/-! ## §6  End-to-end headline: `bignum_inv_p25519_correct`

Composes `inv_p25519_chain_triple` (§5, Layer B — the SSA body's
symbolic Nat output) with `InvP25519Algo.inv_chain_product_eq_inv`
(Layer A↔B + Fermat bridge) into a single headline theorem:

  Running `BignumInvP25519.body` on input `a` at `ap_addr` produces
  a result `r` at `op_addr` with `(r : ZMod p_25519) = a⁻¹`.

That is the **functional correctness of `bignum_inv_p25519`** — what
the C/asm function computes is the modular inverse of its input in
the Curve25519 base field.

The caller supplies the same parameter pack as `inv_p25519_chain_triple`
*plus* the 11 per-block algebraic identities (each chain intermediate
equals its definitional `(z_prev^k · z_other) % p_25519` form).  The
algebraic identities are direct consequences of how the chain values
are chosen — each `bridge_N_(N+1)` already constrains them — but they
are exposed as explicit hypotheses so the bridge to ZMod is fully
deductive at this layer. -/

open CatCrypt.Crypto.Jasmin.Ed25519.InvP25519Algo

/-- Functional-correctness post: `op_addr` holds the modular inverse
    of `a_val` in `ZMod p_25519`. -/
def post_inv_p25519 (op_addr : UInt64) (a_val : Nat) : BignumState → Prop :=
  fun s' => ∃ r : Nat, memNat4 op_addr s'.mem = some r ∧
              (r : ZMod p_25519) = ((a_val : ZMod p_25519))⁻¹

/-- **Headline: `bignum_inv_p25519` correctness.**

    Running `BignumInvP25519.body` (= the concatenated 13 block bodies)
    on input `a_val` at `ap_addr` produces `r` at `op_addr` such that
    `(r : ZMod p_25519) = a⁻¹`.

    Composes §5's chain triple with the Fermat bridge from `InvP25519Algo`. -/
theorem bignum_inv_p25519_correct
    [Fact (Nat.Prime p_25519)]
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (op_addr ap_addr : UInt64)
    (a_val : Nat) (h_a_ne_zero : (a_val : ZMod p_25519) ≠ 0)
    (z2_addr z9_addr z11_addr z2_5_0_addr z2_10_0_addr
     z2_20_0_addr z2_40_0_addr z2_50_0_addr z2_100_0_addr
     z2_200_0_addr z2_250_0_addr : UInt64)
    (z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
     z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
     : Nat)
    (b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : List InstrR)
    (h_z2_addr_eq : BitVec.ofNat 64 z2_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2)
    (h_z9_addr_eq : BitVec.ofNat 64 z9_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z9)
    (h_z11_addr_eq : BitVec.ofNat 64 z11_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z11)
    (h_z2_5_0_addr_eq : BitVec.ofNat 64 z2_5_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_5_0)
    (h_z2_10_0_addr_eq : BitVec.ofNat 64 z2_10_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_10_0)
    (h_z2_20_0_addr_eq : BitVec.ofNat 64 z2_20_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_20_0)
    (h_z2_40_0_addr_eq : BitVec.ofNat 64 z2_40_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_40_0)
    (h_z2_50_0_addr_eq : BitVec.ofNat 64 z2_50_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_50_0)
    (h_z2_100_0_addr_eq : BitVec.ofNat 64 z2_100_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_100_0)
    (h_z2_200_0_addr_eq : BitVec.ofNat 64 z2_200_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_200_0)
    (h_z2_250_0_addr_eq : BitVec.ofNat 64 z2_250_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_250_0)
    (h_op_addr_eq : BitVec.ofNat 64 op_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_op)
    (mkScratch3  : ∀ s, RsmScratch s op_addr z9_addr      z2_addr     ap_addr)
    (mkScratch5  : ∀ s, RsmScratch s op_addr z2_5_0_addr  z11_addr    z9_addr)
    (mkScratch6  : ∀ s, RsmScratch s op_addr z2_10_0_addr z2_5_0_addr z2_5_0_addr)
    (mkScratch7  : ∀ s, RsmScratch s op_addr z2_20_0_addr z2_10_0_addr z2_10_0_addr)
    (mkScratch8  : ∀ s, RsmScratch s op_addr z2_40_0_addr z2_20_0_addr z2_20_0_addr)
    (mkScratch9  : ∀ s, RsmScratch s op_addr z2_50_0_addr z2_40_0_addr z2_10_0_addr)
    (mkScratch10 : ∀ s, RsmScratch s op_addr z2_100_0_addr z2_50_0_addr z2_50_0_addr)
    (mkScratch11 : ∀ s, RsmScratch s op_addr z2_200_0_addr z2_100_0_addr z2_100_0_addr)
    (mkScratch12 : ∀ s, RsmScratch s op_addr z2_250_0_addr z2_200_0_addr z2_50_0_addr)
    (mkScratch13 : ∀ s, RsmScratch s op_addr op_addr      z2_250_0_addr z11_addr)
    (h_b2_shape : b2 = BignumInvP25519.sqr_step 0
      BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap)
    (b4_idx : Nat)
    (h_b4_shape : b4 = BignumInvP25519.mul_step b4_idx
      BignumInvP25519.OFF_z11 BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2)
    (b5_startIdx b6_startIdx b7_startIdx b8_startIdx b9_startIdx
       b10_startIdx b11_startIdx b12_startIdx b13_startIdx : Nat)
    (h_b3_shape : b3 =
      (BignumInvP25519.repeated_sqr_then_mul 1
        BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2
        BignumInvP25519.OFF_ap 2).fst)
    (h_b5_shape : b5 =
      (BignumInvP25519.repeated_sqr_then_mul b5_startIdx
        BignumInvP25519.OFF_z2_5_0 BignumInvP25519.OFF_z11
        BignumInvP25519.OFF_z9 1).fst)
    (h_b6_shape : b6 =
      (BignumInvP25519.repeated_sqr_then_mul b6_startIdx
        BignumInvP25519.OFF_z2_10_0 BignumInvP25519.OFF_z2_5_0
        BignumInvP25519.OFF_z2_5_0 5).fst)
    (h_b7_shape : b7 =
      (BignumInvP25519.repeated_sqr_then_mul b7_startIdx
        BignumInvP25519.OFF_z2_20_0 BignumInvP25519.OFF_z2_10_0
        BignumInvP25519.OFF_z2_10_0 10).fst)
    (h_b8_shape : b8 =
      (BignumInvP25519.repeated_sqr_then_mul b8_startIdx
        BignumInvP25519.OFF_z2_40_0 BignumInvP25519.OFF_z2_20_0
        BignumInvP25519.OFF_z2_20_0 20).fst)
    (h_b9_shape : b9 =
      (BignumInvP25519.repeated_sqr_then_mul b9_startIdx
        BignumInvP25519.OFF_z2_50_0 BignumInvP25519.OFF_z2_40_0
        BignumInvP25519.OFF_z2_10_0 10).fst)
    (h_b10_shape : b10 =
      (BignumInvP25519.repeated_sqr_then_mul b10_startIdx
        BignumInvP25519.OFF_z2_100_0 BignumInvP25519.OFF_z2_50_0
        BignumInvP25519.OFF_z2_50_0 50).fst)
    (h_b11_shape : b11 =
      (BignumInvP25519.repeated_sqr_then_mul b11_startIdx
        BignumInvP25519.OFF_z2_200_0 BignumInvP25519.OFF_z2_100_0
        BignumInvP25519.OFF_z2_100_0 100).fst)
    (h_b12_shape : b12 =
      (BignumInvP25519.repeated_sqr_then_mul b12_startIdx
        BignumInvP25519.OFF_z2_250_0 BignumInvP25519.OFF_z2_200_0
        BignumInvP25519.OFF_z2_50_0 50).fst)
    (h_b13_shape : b13 =
      (BignumInvP25519.repeated_sqr_then_mul b13_startIdx
        BignumInvP25519.OFF_op BignumInvP25519.OFF_z2_250_0
        BignumInvP25519.OFF_z11 5).fst)
    (bridge_2_3 : ∀ s,
      post_block2 z2_addr a_val s →
      pre_block3 op_addr ap_addr z2_addr z2_val a_val z9_addr s)
    (bridge_3_4 : ∀ s,
      post_block3 z9_addr z2_val a_val s →
      pre_block4 op_addr ap_addr z9_addr z2_addr z9_val z2_val z11_addr s)
    (bridge_4_5 : ∀ s,
      post_block4 z11_addr z9_val z2_val s →
      pre_block5 op_addr ap_addr z11_addr z9_addr z11_val z9_val z2_5_0_addr s)
    (bridge_5_6 : ∀ s,
      post_block5 z2_5_0_addr z11_val z9_val s →
      pre_block6 op_addr ap_addr z2_5_0_addr z2_5_0_val z2_10_0_addr s)
    (bridge_6_7 : ∀ s,
      post_block6 z2_10_0_addr z2_5_0_val s →
      pre_block7 op_addr ap_addr z2_10_0_addr z2_10_0_val z2_20_0_addr s)
    (bridge_7_8 : ∀ s,
      post_block7 z2_20_0_addr z2_10_0_val s →
      pre_block8 op_addr ap_addr z2_20_0_addr z2_20_0_val z2_40_0_addr s)
    (bridge_8_9 : ∀ s,
      post_block8 z2_40_0_addr z2_20_0_val s →
      pre_block9 op_addr ap_addr z2_40_0_addr z2_10_0_addr
        z2_40_0_val z2_10_0_val z2_50_0_addr s)
    (bridge_9_10 : ∀ s,
      post_block9 z2_50_0_addr z2_40_0_val z2_10_0_val s →
      pre_block10 op_addr ap_addr z2_50_0_addr z2_50_0_val z2_100_0_addr s)
    (bridge_10_11 : ∀ s,
      post_block10 z2_100_0_addr z2_50_0_val s →
      pre_block11 op_addr ap_addr z2_100_0_addr z2_100_0_val z2_200_0_addr s)
    (bridge_11_12 : ∀ s,
      post_block11 z2_200_0_addr z2_100_0_val s →
      pre_block12 op_addr ap_addr z2_200_0_addr z2_50_0_addr
        z2_200_0_val z2_50_0_val z2_250_0_addr s)
    (bridge_12_13 : ∀ s,
      post_block12 z2_250_0_addr z2_200_0_val z2_50_0_val s →
      pre_block13 op_addr ap_addr z2_250_0_addr z11_addr z2_250_0_val z11_val s)
    -- Per-block algebraic identities (modular).  These are
    -- consequences of how the chain values are chosen — each
    -- `bridge_N_(N+1)` forces them — but we expose them as explicit
    -- hypotheses so the ZMod-level bridge is fully deductive here.
    (h_alg_z2  : z2_val  % p_25519 = (a_val * a_val) % p_25519)
    (h_alg_z9  : z9_val  % p_25519 = (z2_val^(2^2) * a_val) % p_25519)
    (h_alg_z11 : z11_val % p_25519 = (z9_val * z2_val) % p_25519)
    (h_alg_z2_5_0 : z2_5_0_val % p_25519 =
      (z11_val^(2^1) * z9_val) % p_25519)
    (h_alg_z2_10_0 : z2_10_0_val % p_25519 =
      (z2_5_0_val^(2^5) * z2_5_0_val) % p_25519)
    (h_alg_z2_20_0 : z2_20_0_val % p_25519 =
      (z2_10_0_val^(2^10) * z2_10_0_val) % p_25519)
    (h_alg_z2_40_0 : z2_40_0_val % p_25519 =
      (z2_20_0_val^(2^20) * z2_20_0_val) % p_25519)
    (h_alg_z2_50_0 : z2_50_0_val % p_25519 =
      (z2_40_0_val^(2^10) * z2_10_0_val) % p_25519)
    (h_alg_z2_100_0 : z2_100_0_val % p_25519 =
      (z2_50_0_val^(2^50) * z2_50_0_val) % p_25519)
    (h_alg_z2_200_0 : z2_200_0_val % p_25519 =
      (z2_100_0_val^(2^100) * z2_100_0_val) % p_25519)
    (h_alg_z2_250_0 : z2_250_0_val % p_25519 =
      (z2_200_0_val^(2^50) * z2_50_0_val) % p_25519) :
    BignumTripleFuel registry
      (pre_block2 op_addr ap_addr a_val z2_addr)
      (b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9 ++ b10 ++
       b11 ++ b12 ++ b13)
      (post_inv_p25519 op_addr a_val) := by
  -- Apply the chain triple to get the symbolic Nat post.
  have h_chain := inv_p25519_chain_triple registry h_registry
    op_addr ap_addr a_val
    z2_addr z9_addr z11_addr z2_5_0_addr z2_10_0_addr
    z2_20_0_addr z2_40_0_addr z2_50_0_addr z2_100_0_addr
    z2_200_0_addr z2_250_0_addr
    z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
    z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
    b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    h_z2_addr_eq h_z9_addr_eq h_z11_addr_eq h_z2_5_0_addr_eq h_z2_10_0_addr_eq
    h_z2_20_0_addr_eq h_z2_40_0_addr_eq h_z2_50_0_addr_eq h_z2_100_0_addr_eq
    h_z2_200_0_addr_eq h_z2_250_0_addr_eq h_op_addr_eq
    mkScratch3 mkScratch5 mkScratch6 mkScratch7 mkScratch8
    mkScratch9 mkScratch10 mkScratch11 mkScratch12 mkScratch13
    h_b2_shape b4_idx h_b4_shape
    b5_startIdx b6_startIdx b7_startIdx b8_startIdx b9_startIdx
    b10_startIdx b11_startIdx b12_startIdx b13_startIdx
    h_b3_shape h_b5_shape h_b6_shape h_b7_shape h_b8_shape
    h_b9_shape h_b10_shape h_b11_shape h_b12_shape h_b13_shape
    bridge_2_3 bridge_3_4 bridge_4_5 bridge_5_6 bridge_6_7 bridge_7_8
    bridge_8_9 bridge_9_10 bridge_10_11 bridge_11_12 bridge_12_13
  -- Upgrade the post via the Fermat / Layer-A bridge.
  intro s fuel s' hP h_exec
  have h_post := h_chain s fuel s' hP h_exec
  -- h_post : memNat4 op_addr s'.mem = some ((z2_250_0_val^(2^5) * z11_val) % p_25519)
  refine ⟨(z2_250_0_val^(2^5) * z11_val) % p_25519, h_post, ?_⟩
  -- Goal: ((chain_product : Nat) : ZMod p_25519) = (a_val : ZMod p_25519)⁻¹
  have h_inv := inv_chain_product_eq_inv a_val h_a_ne_zero
    z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
    z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
    h_alg_z2 h_alg_z9 h_alg_z11 h_alg_z2_5_0 h_alg_z2_10_0 h_alg_z2_20_0
    h_alg_z2_40_0 h_alg_z2_50_0 h_alg_z2_100_0 h_alg_z2_200_0 h_alg_z2_250_0
  -- h_inv : ((z2_250_0_val^(2^5) * z11_val : Nat) : ZMod p_25519) =
  --         (a_val : ZMod p_25519)⁻¹
  -- We need: ((chain_product % p_25519 : Nat) : ZMod p_25519) = (a : ZMod p)⁻¹.
  -- These are equal because `(x % p_25519 : ZMod p_25519) = (x : ZMod p_25519)`.
  rw [show ((z2_250_0_val ^ 2^5 * z11_val % p_25519 : Nat) : ZMod p_25519) =
          ((z2_250_0_val ^ 2^5 * z11_val : Nat) : ZMod p_25519) from
    ZMod.natCast_mod _ _]
  exact h_inv

/-! ## §7  Bridge-construction helpers

The 11 `bridge_N_(N+1)` parameters of `inv_p25519_chain_triple` (and
similarly of `pow_p58_chain_triple`) are caller-supplied predicates
of the form `∀ s, post_block_N s → pre_block_(N+1) s`.

In practice each bridge is constructed from:
1. **Block N's frame condition** (from the underlying
   `blockN_correctness_via_axiom`'s post: bytes outside block N's
   dst window are unchanged).
2. **Non-aliasing assumptions** between block N's dst and the earlier
   chain outputs needed by block N+1's pre.
3. **Register preservation** (op/ap pointers preserved across the
   block — provable via `bignumExecFuel_preserves_reg` once the block's
   instruction list is shown non-control).

This section provides composable helpers — a caller writing a concrete
chain proof composes these with frame conditions to discharge each
bridge in ~5–10 LoC.

Note: full per-block bridge derivation is **not** done in-tree because
the bridges are state-quantified (`∀ s, post_N s → pre_(N+1) s`) and
the chain triple itself does not expose s.  The caller's bridges are
free choices over what additional invariants they want to thread, so a
fully generic helper would over-restrict.  The helpers below give the
building blocks. -/

/-- Lift a `memNat4` invariant through a block: if bytes at
    `chain_addr + 0..31` are unchanged by the block, the chain value
    survives.  This is the workhorse for constructing
    `pre_block_(N+1)` from `post_block_N`'s frame condition. -/
theorem memNat4_preserved_outside_range
    {s s' : BignumState} {dst_addr chain_addr : UInt64} {v : Nat}
    (h_frame : ∀ addr : UInt64,
      ¬ MemoryModel.range dst_addr 32 addr →
      s'.mem.loadByte addr = s.mem.loadByte addr)
    (h_disj : ∀ k1 k2 : Fin 32,
      chain_addr + UInt64.ofNat k1.val ≠ dst_addr + UInt64.ofNat k2.val)
    (h_pre : memNat4 chain_addr s.mem = some v) :
    memNat4 chain_addr s'.mem = some v := by
  have h_eq : memNat4 chain_addr s'.mem = memNat4 chain_addr s.mem := by
    apply memNat4_eq_of_byte_eq
    intro k hk
    apply h_frame
    rintro ⟨k', hk'_lt, h_eq⟩
    exact h_disj ⟨k, hk⟩ ⟨k', hk'_lt⟩ h_eq
  rw [h_eq]; exact h_pre

/-- Byte-level alloc invariance: if a block's frame preserves bytes
    outside its dst, and the chain output we care about is disjoint
    from the dst, alloc is preserved. -/
theorem alloc_preserved_outside_range
    {s s' : BignumState} {dst_addr chain_addr : UInt64}
    (h_frame : ∀ addr : UInt64,
      ¬ MemoryModel.range dst_addr 32 addr →
      s'.mem.loadByte addr = s.mem.loadByte addr)
    (h_disj : ∀ k1 k2 : Fin 32,
      chain_addr + UInt64.ofNat k1.val ≠ dst_addr + UInt64.ofNat k2.val)
    (h_pre : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (chain_addr + UInt64.ofNat k.val) = some b) :
    ∀ k : Fin 32,
      ∃ b, s'.mem.loadByte (chain_addr + UInt64.ofNat k.val) = some b := by
  intro k
  have h_not_in : ¬ MemoryModel.range dst_addr 32
      (chain_addr + UInt64.ofNat k.val) := by
    rintro ⟨k', hk'_lt, h_eq⟩
    exact h_disj k ⟨k', hk'_lt⟩ h_eq
  rw [h_frame _ h_not_in]
  exact h_pre k

end CatCrypt.Crypto.Jasmin.BignumHoare.InvP25519Composition
