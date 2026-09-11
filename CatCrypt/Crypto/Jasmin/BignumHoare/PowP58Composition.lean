/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.BignumHoare.ChainStepAxioms
public import CatCrypt.Crypto.Jasmin.BignumHoare.PowP58LayerB
public import CatCrypt.Crypto.Jasmin.BignumHoare.InvP25519Composition
public import CatCrypt.Crypto.Jasmin.Ed25519.PowP58Algo

/-!
# `bignum_pow_p25519_p58`: end-to-end `BignumTripleFuel` composition

Sister composition file for `bignum_pow_p25519_p58`.  Since the
`BignumPowP58P25519.body` chain shares blocks 2–12 with the inv
chain (same `BignumInvP25519` helpers), blocks 2–12 of the p58
composition reuse the existing `blockN_correctness_triple` lemmas
from `InvP25519Composition.lean`.

Only block 13b differs:
* inv chain block 13:  `op := (z2_250_0)^(2⁵) · z11` (n = 5)
* p58 chain block 13b: `op := (z2_250_0)^(2²) · ap`  (n = 2,
                                                      otherOff = -1)

This file:
1. Adds `pre_block13b` / `post_block13b` predicates for the p58
   tail.
2. Lifts `block13b_correctness_via_axiom` (in
   `ChainStepAxioms.lean`) to a `BignumTripleFuel` triple via the
   same deterministic-bridge pattern as the inv composition.

The full 13-block sequential composition for p58 (analogous to
`inv_p25519_chain_triple`) is left as future plumbing — it follows
the same 12-fold `.seq` pattern but with `block13b_correctness_triple`
swapped in for the tail.

## Trust set delta

This file adds **0 new axioms**.  All work is plumbing above
`ChainStepAxioms.lean`'s zero-axiom contracts, parametric over the
`MontmulCallFacts registry` hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.PowP58Composition

open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.S2NBignumSSA
open CatCrypt.Crypto.Jasmin.BignumHoare.MontmulAxiom
open CatCrypt.Crypto.Jasmin.BignumHoare.ChainStepAxioms
open CatCrypt.Crypto.Jasmin.BignumHoare.PowP58LayerB

/-! ## §1  Block 13b pre/post predicates -/

/-- p58 block 13b pre: registers + `z2_250_0_addr` readable
    holding `z2_250_0_val` + `ap_addr` readable holding `ap_val`
    + `op_addr` output buffer allocated. -/
def pre_block13b (op_addr ap_addr z2_250_0_addr : UInt64)
    (z2_250_0_val ap_val : Nat) : BignumState → Prop := fun s =>
  s.regs "op" = BitVec.ofNat 64 op_addr.toNat ∧
  s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat ∧
  memNat4 z2_250_0_addr s.mem = some z2_250_0_val ∧
  memNat4 ap_addr s.mem = some ap_val ∧
  (∀ k : Fin 32, ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)

/-- p58 block 13b post: `op_addr` holds
    `(z2_250_0_val^4 · ap_val) mod p_25519 = ap_val^((p-5)/8) mod p`. -/
def post_block13b (op_addr : UInt64) (z2_250_0_val ap_val : Nat) :
    BignumState → Prop := fun s' =>
  memNat4 op_addr s'.mem =
    some (((z2_250_0_val ^ (2^2)) * ap_val) % p_25519)

/-! ## §2  Lifted triple for block 13b -/

/-- Lifted block 13b correctness to `BignumTripleFuel`.

    Pattern matches the inv-chain block triples: destructure the
    existential `bignumExecFuel`-witness from
    `block13b_correctness_via_axiom`, observe that
    `bignumExecFuel` is deterministic, then transport the post via
    `Option.some.inj`. -/
theorem block13b_correctness_triple
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (op_addr ap_addr z2_250_0_addr : UInt64)
    (z2_250_0_val ap_val : Nat)
    (h_z2_250_0_addr_eq : BitVec.ofNat 64 z2_250_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat +
         BitVec.ofInt 64 BignumInvP25519.OFF_z2_250_0)
    (mkScratch : ∀ s : BignumState,
      RsmScratch s op_addr op_addr z2_250_0_addr ap_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_op BignumInvP25519.OFF_z2_250_0
        BignumInvP25519.OFF_ap 2).fst) :
    BignumTripleFuel registry
      (pre_block13b op_addr ap_addr z2_250_0_addr z2_250_0_val ap_val)
      rsm_body
      (post_block13b op_addr z2_250_0_val ap_val) := by
  intro s fuel s' hP h_exec
  obtain ⟨h_op, h_ap, h_z2_250_0_mem, h_ap_mem, h_op_alloc⟩ := hP
  cases fuel with
  | zero => simp [bignumExecFuel] at h_exec
  | succ n =>
    obtain ⟨s_ax, h_ax_exec, h_ax_post, _h_ax_frame⟩ :=
      block13b_correctness_via_axiom registry hAx s n
        op_addr ap_addr z2_250_0_addr h_op h_ap
        z2_250_0_val ap_val h_z2_250_0_mem h_ap_mem h_op_alloc
        h_z2_250_0_addr_eq (mkScratch s) startIdx rsm_body h_shape
    have : some s_ax = some s' := h_ax_exec ▸ h_exec
    have h_eq : s_ax = s' := Option.some.inj this
    simpa [post_block13b, h_eq] using! h_ax_post

/-! ## §3  Full p58 chain triple

Composes the 12 shared prefix block triples (reused from
`InvP25519Composition`) with the new `block13b_correctness_triple`
above, via the same 12-fold `.seq` chain + 11 bridging hypotheses
as `InvP25519Composition.inv_p25519_chain_triple`.

The shape is identical to `inv_p25519_chain_triple` except:
* the tail block uses `block13b` (n = 2, otherOff = -1) instead of
  block 13 (n = 5, otherOff = OFF_z11),
* the final post is `post_block13b` instead of `post_block13`. -/

open CatCrypt.Crypto.Jasmin.BignumHoare.InvP25519Composition

/-- 13-block end-to-end Hoare triple for `bignum_pow_p25519_p58`.
    Shares blocks 2–12 with `inv_p25519_chain_triple`; block 13b is
    the p58-specific tail (`op := z2_250_0^4 · ap`). -/
theorem pow_p58_chain_triple
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (op_addr ap_addr : UInt64)
    (a_val : Nat)
    (z2_addr z9_addr z11_addr z2_5_0_addr z2_10_0_addr
     z2_20_0_addr z2_40_0_addr z2_50_0_addr z2_100_0_addr
     z2_200_0_addr z2_250_0_addr : UInt64)
    (z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
     z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
     : Nat)
    -- 12 caller-supplied block bodies; b13b is the p58 tail.
    (b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13b : List InstrR)
    -- Address-derivation hypotheses.
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
    -- Scratch builders.  Blocks 3, 5-12 same as inv; block 13b takes
    -- z2_250_0 as src, ap as other (the p58 tail).
    (mkScratch3  : ∀ s, RsmScratch s op_addr z9_addr      z2_addr     ap_addr)
    (mkScratch5  : ∀ s, RsmScratch s op_addr z2_5_0_addr  z11_addr    z9_addr)
    (mkScratch6  : ∀ s, RsmScratch s op_addr z2_10_0_addr z2_5_0_addr z2_5_0_addr)
    (mkScratch7  : ∀ s, RsmScratch s op_addr z2_20_0_addr z2_10_0_addr z2_10_0_addr)
    (mkScratch8  : ∀ s, RsmScratch s op_addr z2_40_0_addr z2_20_0_addr z2_20_0_addr)
    (mkScratch9  : ∀ s, RsmScratch s op_addr z2_50_0_addr z2_40_0_addr z2_10_0_addr)
    (mkScratch10 : ∀ s, RsmScratch s op_addr z2_100_0_addr z2_50_0_addr z2_50_0_addr)
    (mkScratch11 : ∀ s, RsmScratch s op_addr z2_200_0_addr z2_100_0_addr z2_100_0_addr)
    (mkScratch12 : ∀ s, RsmScratch s op_addr z2_250_0_addr z2_200_0_addr z2_50_0_addr)
    (mkScratch13b : ∀ s, RsmScratch s op_addr op_addr z2_250_0_addr ap_addr)
    -- Body-shape hypotheses (b2 sqr_step, b4 mul_step, b13b is p58 tail).
    (h_b2_shape : b2 = BignumInvP25519.sqr_step 0
      BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap)
    (b4_idx : Nat)
    (h_b4_shape : b4 = BignumInvP25519.mul_step b4_idx
      BignumInvP25519.OFF_z11 BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2)
    (b5_startIdx b6_startIdx b7_startIdx b8_startIdx b9_startIdx
       b10_startIdx b11_startIdx b12_startIdx b13b_startIdx : Nat)
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
    (h_b13b_shape : b13b =
      (BignumInvP25519.repeated_sqr_then_mul b13b_startIdx
        BignumInvP25519.OFF_op BignumInvP25519.OFF_z2_250_0
        BignumInvP25519.OFF_ap 2).fst)
    -- 11 bridging implications: post of block N ⇒ pre of block N+1.
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
    -- The p58-specific bridge: block 12's post (z2_250_0 ready) →
    -- block 13b's pre (z2_250_0 + ap readable, op allocated).
    (bridge_12_13b : ∀ s,
      post_block12 z2_250_0_addr z2_200_0_val z2_50_0_val s →
      pre_block13b op_addr ap_addr z2_250_0_addr z2_250_0_val a_val s) :
    BignumTripleFuel registry
      (pre_block2 op_addr ap_addr a_val z2_addr)
      (b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9 ++ b10 ++
       b11 ++ b12 ++ b13b)
      (post_block13b op_addr z2_250_0_val a_val) := by
  -- Blocks 2-12: same as inv chain.
  have h2 : BignumTripleFuel registry
      (pre_block2 op_addr ap_addr a_val z2_addr) b2
      (pre_block3 op_addr ap_addr z2_addr z2_val a_val z9_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_2_3
      (block2_correctness_triple registry hAx op_addr ap_addr a_val
        z2_addr h_z2_addr_eq b2 h_b2_shape)
  have h3 : BignumTripleFuel registry
      (pre_block3 op_addr ap_addr z2_addr z2_val a_val z9_addr) b3
      (pre_block4 op_addr ap_addr z9_addr z2_addr z9_val z2_val z11_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_3_4
      (block3_correctness_triple registry hAx op_addr ap_addr z2_addr
        z2_val a_val z9_addr h_z9_addr_eq h_z2_addr_eq mkScratch3 b3 h_b3_shape)
  have h4 : BignumTripleFuel registry
      (pre_block4 op_addr ap_addr z9_addr z2_addr z9_val z2_val z11_addr) b4
      (pre_block5 op_addr ap_addr z11_addr z9_addr z11_val z9_val z2_5_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_4_5
      (block4_correctness_triple registry hAx op_addr ap_addr z9_addr
        z2_addr z9_val z2_val z11_addr
        h_z11_addr_eq h_z9_addr_eq h_z2_addr_eq b4_idx b4 h_b4_shape)
  have h5 : BignumTripleFuel registry
      (pre_block5 op_addr ap_addr z11_addr z9_addr z11_val z9_val z2_5_0_addr) b5
      (pre_block6 op_addr ap_addr z2_5_0_addr z2_5_0_val z2_10_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_5_6
      (block5_correctness_triple registry hAx op_addr ap_addr z11_addr
        z9_addr z11_val z9_val z2_5_0_addr h_z2_5_0_addr_eq
        h_z11_addr_eq h_z9_addr_eq mkScratch5
        b5_startIdx b5 h_b5_shape)
  have h6 : BignumTripleFuel registry
      (pre_block6 op_addr ap_addr z2_5_0_addr z2_5_0_val z2_10_0_addr) b6
      (pre_block7 op_addr ap_addr z2_10_0_addr z2_10_0_val z2_20_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_6_7
      (block6_correctness_triple registry hAx op_addr ap_addr
        z2_5_0_addr z2_5_0_val z2_10_0_addr h_z2_10_0_addr_eq h_z2_5_0_addr_eq
        mkScratch6 b6_startIdx b6 h_b6_shape)
  have h7 : BignumTripleFuel registry
      (pre_block7 op_addr ap_addr z2_10_0_addr z2_10_0_val z2_20_0_addr) b7
      (pre_block8 op_addr ap_addr z2_20_0_addr z2_20_0_val z2_40_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_7_8
      (block7_correctness_triple registry hAx op_addr ap_addr
        z2_10_0_addr z2_10_0_val z2_20_0_addr h_z2_20_0_addr_eq h_z2_10_0_addr_eq
        mkScratch7 b7_startIdx b7 h_b7_shape)
  have h8 : BignumTripleFuel registry
      (pre_block8 op_addr ap_addr z2_20_0_addr z2_20_0_val z2_40_0_addr) b8
      (pre_block9 op_addr ap_addr z2_40_0_addr z2_10_0_addr
        z2_40_0_val z2_10_0_val z2_50_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_8_9
      (block8_correctness_triple registry hAx op_addr ap_addr
        z2_20_0_addr z2_20_0_val z2_40_0_addr h_z2_40_0_addr_eq h_z2_20_0_addr_eq
        mkScratch8 b8_startIdx b8 h_b8_shape)
  have h9 : BignumTripleFuel registry
      (pre_block9 op_addr ap_addr z2_40_0_addr z2_10_0_addr
        z2_40_0_val z2_10_0_val z2_50_0_addr) b9
      (pre_block10 op_addr ap_addr z2_50_0_addr z2_50_0_val z2_100_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_9_10
      (block9_correctness_triple registry hAx op_addr ap_addr
        z2_40_0_addr z2_10_0_addr z2_40_0_val z2_10_0_val z2_50_0_addr
        h_z2_50_0_addr_eq h_z2_40_0_addr_eq h_z2_10_0_addr_eq
        mkScratch9 b9_startIdx b9 h_b9_shape)
  have h10 : BignumTripleFuel registry
      (pre_block10 op_addr ap_addr z2_50_0_addr z2_50_0_val z2_100_0_addr) b10
      (pre_block11 op_addr ap_addr z2_100_0_addr z2_100_0_val z2_200_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_10_11
      (block10_correctness_triple registry hAx op_addr ap_addr
        z2_50_0_addr z2_50_0_val z2_100_0_addr h_z2_100_0_addr_eq h_z2_50_0_addr_eq
        mkScratch10 b10_startIdx b10 h_b10_shape)
  have h11 : BignumTripleFuel registry
      (pre_block11 op_addr ap_addr z2_100_0_addr z2_100_0_val z2_200_0_addr) b11
      (pre_block12 op_addr ap_addr z2_200_0_addr z2_50_0_addr
        z2_200_0_val z2_50_0_val z2_250_0_addr) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_11_12
      (block11_correctness_triple registry hAx op_addr ap_addr
        z2_100_0_addr z2_100_0_val z2_200_0_addr h_z2_200_0_addr_eq
        h_z2_100_0_addr_eq mkScratch11 b11_startIdx b11 h_b11_shape)
  have h12 : BignumTripleFuel registry
      (pre_block12 op_addr ap_addr z2_200_0_addr z2_50_0_addr
        z2_200_0_val z2_50_0_val z2_250_0_addr) b12
      (pre_block13b op_addr ap_addr z2_250_0_addr z2_250_0_val a_val) :=
    BignumTripleFuel.consequence (fun _ h => h) bridge_12_13b
      (block12_correctness_triple registry hAx op_addr ap_addr
        z2_200_0_addr z2_50_0_addr z2_200_0_val z2_50_0_val z2_250_0_addr
        h_z2_250_0_addr_eq h_z2_200_0_addr_eq h_z2_50_0_addr_eq
        mkScratch12 b12_startIdx b12 h_b12_shape)
  -- Tail: block 13b (p58-specific).
  have h13b : BignumTripleFuel registry
      (pre_block13b op_addr ap_addr z2_250_0_addr z2_250_0_val a_val) b13b
      (post_block13b op_addr z2_250_0_val a_val) :=
    block13b_correctness_triple registry hAx op_addr ap_addr
      z2_250_0_addr z2_250_0_val a_val
      h_z2_250_0_addr_eq mkScratch13b b13b_startIdx b13b h_b13b_shape
  -- 12-fold sequential composition (left-associative to match ++).
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
  exact h2_12.seq h13b

/-! ## §4  End-to-end headline: `bignum_pow_p25519_p58_correct`

Composes `pow_p58_chain_triple` (§3) with the Layer A↔B bridge from
`PowP58Algo.pow_p58_chain_product_eq_pow_p58` into a single headline:

  Running `BignumPowP58P25519.body` on input `a` at `ap_addr` produces
  `r` at `op_addr` with `r ≡ a^((p − 5)/8) (mod p_25519)`.

That's the **functional correctness of `bignum_pow_p25519_p58`** —
what the C/asm function computes is the `(p − 5)/8`-th power in the
Curve25519 base field. -/

open CatCrypt.Crypto.Jasmin.Ed25519.PowP58Algo

/-- Functional-correctness post: `op_addr` holds a Nat congruent to
    `a^((p − 5)/8)` modulo `p_25519`. -/
def post_pow_p58 (op_addr : UInt64) (a_val : Nat) : BignumState → Prop :=
  fun s' => ∃ r : Nat, memNat4 op_addr s'.mem = some r ∧
              r % p_25519 = a_val^((p_25519 - 5) / 8) % p_25519

/-- **Headline: `bignum_pow_p25519_p58` correctness.**

    Running `BignumPowP58P25519.body` (= 12 inv-shared prefix blocks
    + block 13b) on input `a_val` at `ap_addr` produces `r` at
    `op_addr` such that `r ≡ a^((p − 5)/8) (mod p_25519)`. -/
theorem bignum_pow_p25519_p58_correct
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (op_addr ap_addr : UInt64)
    (a_val : Nat)
    (z2_addr z9_addr z11_addr z2_5_0_addr z2_10_0_addr
     z2_20_0_addr z2_40_0_addr z2_50_0_addr z2_100_0_addr
     z2_200_0_addr z2_250_0_addr : UInt64)
    (z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
     z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
     : Nat)
    (b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13b : List InstrR)
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
    (mkScratch3  : ∀ s, RsmScratch s op_addr z9_addr      z2_addr     ap_addr)
    (mkScratch5  : ∀ s, RsmScratch s op_addr z2_5_0_addr  z11_addr    z9_addr)
    (mkScratch6  : ∀ s, RsmScratch s op_addr z2_10_0_addr z2_5_0_addr z2_5_0_addr)
    (mkScratch7  : ∀ s, RsmScratch s op_addr z2_20_0_addr z2_10_0_addr z2_10_0_addr)
    (mkScratch8  : ∀ s, RsmScratch s op_addr z2_40_0_addr z2_20_0_addr z2_20_0_addr)
    (mkScratch9  : ∀ s, RsmScratch s op_addr z2_50_0_addr z2_40_0_addr z2_10_0_addr)
    (mkScratch10 : ∀ s, RsmScratch s op_addr z2_100_0_addr z2_50_0_addr z2_50_0_addr)
    (mkScratch11 : ∀ s, RsmScratch s op_addr z2_200_0_addr z2_100_0_addr z2_100_0_addr)
    (mkScratch12 : ∀ s, RsmScratch s op_addr z2_250_0_addr z2_200_0_addr z2_50_0_addr)
    (mkScratch13b : ∀ s, RsmScratch s op_addr op_addr z2_250_0_addr ap_addr)
    (h_b2_shape : b2 = BignumInvP25519.sqr_step 0
      BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap)
    (b4_idx : Nat)
    (h_b4_shape : b4 = BignumInvP25519.mul_step b4_idx
      BignumInvP25519.OFF_z11 BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2)
    (b5_startIdx b6_startIdx b7_startIdx b8_startIdx b9_startIdx
       b10_startIdx b11_startIdx b12_startIdx b13b_startIdx : Nat)
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
    (h_b13b_shape : b13b =
      (BignumInvP25519.repeated_sqr_then_mul b13b_startIdx
        BignumInvP25519.OFF_op BignumInvP25519.OFF_z2_250_0
        BignumInvP25519.OFF_ap 2).fst)
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
    (bridge_12_13b : ∀ s,
      post_block12 z2_250_0_addr z2_200_0_val z2_50_0_val s →
      pre_block13b op_addr ap_addr z2_250_0_addr z2_250_0_val a_val s)
    -- Per-block algebraic identities (shared with the inv-chain bridge).
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
       b11 ++ b12 ++ b13b)
      (post_pow_p58 op_addr a_val) := by
  have h_chain := pow_p58_chain_triple registry hAx
    op_addr ap_addr a_val
    z2_addr z9_addr z11_addr z2_5_0_addr z2_10_0_addr
    z2_20_0_addr z2_40_0_addr z2_50_0_addr z2_100_0_addr
    z2_200_0_addr z2_250_0_addr
    z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
    z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
    b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13b
    h_z2_addr_eq h_z9_addr_eq h_z11_addr_eq h_z2_5_0_addr_eq h_z2_10_0_addr_eq
    h_z2_20_0_addr_eq h_z2_40_0_addr_eq h_z2_50_0_addr_eq h_z2_100_0_addr_eq
    h_z2_200_0_addr_eq h_z2_250_0_addr_eq
    mkScratch3 mkScratch5 mkScratch6 mkScratch7 mkScratch8
    mkScratch9 mkScratch10 mkScratch11 mkScratch12 mkScratch13b
    h_b2_shape b4_idx h_b4_shape
    b5_startIdx b6_startIdx b7_startIdx b8_startIdx b9_startIdx
    b10_startIdx b11_startIdx b12_startIdx b13b_startIdx
    h_b3_shape h_b5_shape h_b6_shape h_b7_shape h_b8_shape
    h_b9_shape h_b10_shape h_b11_shape h_b12_shape h_b13b_shape
    bridge_2_3 bridge_3_4 bridge_4_5 bridge_5_6 bridge_6_7 bridge_7_8
    bridge_8_9 bridge_9_10 bridge_10_11 bridge_11_12 bridge_12_13b
  intro s fuel s' hP h_exec
  have h_post := h_chain s fuel s' hP h_exec
  -- h_post : memNat4 op_addr s'.mem = some ((z2_250_0_val^(2^2) * a_val) % p_25519)
  refine ⟨(z2_250_0_val^(2^2) * a_val) % p_25519, h_post, ?_⟩
  -- Bridge to a^((p-5)/8) % p via PowP58Algo.
  rw [Nat.mod_mod]
  exact pow_p58_chain_product_eq_pow_p58 a_val
    z2_val z9_val z11_val z2_5_0_val z2_10_0_val z2_20_0_val
    z2_40_0_val z2_50_0_val z2_100_0_val z2_200_0_val z2_250_0_val
    h_alg_z2 h_alg_z9 h_alg_z11 h_alg_z2_5_0 h_alg_z2_10_0 h_alg_z2_20_0
    h_alg_z2_40_0 h_alg_z2_50_0 h_alg_z2_100_0 h_alg_z2_200_0 h_alg_z2_250_0

end CatCrypt.Crypto.Jasmin.BignumHoare.PowP58Composition
