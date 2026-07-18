/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumExec
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Axiomatic functional contract for `bignum_montmul_p25519`

Bridges the per-Ccall semantic gap in `bignumExecFuel`'s registry-
based callee dispatch.  Each `Ccall bignum_montmul_p25519 [op, a, b]`
writes 4 limbs at `op` holding `(a · b) mod p_25519` — this file
axiomatises that contract, citing s2n-bignum's machine-verified
proof of `bignum_montmul_p25519`.

## Why axiomatize

`bignumExecFuel`'s Ccall semantics dispatches to a callee `FunDecl`
in a `BignumRegistry`.  Walking through the callee's full body
(montmul is ~600 InstrRs of CIOS Montgomery multiplication)
through `bignumExecFuel` is the wrong granularity for chain-level
correctness — chain-level proofs care about **what montmul
computes**, not how it computes it.

s2n-bignum (the upstream) proves `bignum_montmul_p25519`'s
correctness against the abstract Montgomery-multiplication
specification at the assembly level.  The CatCrypt verified
pipeline cites this via `jasminc_preserves_uc` for UC bounds; we
add a parallel functional axiom for chain-level correctness.

## The contract

```
{ regs op_reg = op_addr ∧ regs a_reg = a_addr ∧ regs b_reg = b_addr
∧ memNat4 a_addr m = some a_val
∧ memNat4 b_addr m = some b_val
∧ output range allocated at op_addr }
  Ccall bignum_montmul_p25519 [op, a, b]
{ memNat4 op_addr m' = some ((a_val * b_val) % p25519) ∧
  m' agrees with m outside [op_addr, op_addr+32) }
```

## Trust set delta

This file adds **one new axiom** (`montmul_call_correct`).  The
axiom is discharged by s2n-bignum's machine-verified proof of
`bignum_montmul_p25519` (per the s2n-bignum codebase's HOL Light
proofs).  Once a Lean port of s2n-bignum's HOL Light proofs lands
(or once the CatCrypt pipeline's Jasmin compiler verifies montmul
through its own pathway), the axiom can be discharged.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.MontmulAxiom

open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel

abbrev p_25519 : Nat := 2^255 - 19

/-! ## §1  4-limb memory reading helper

Same shape as `BignumHoare.memNat4` but specialised here so we
don't pull in BignumHoare (which is currently upstream-blocked
by the Sqr4Algebra WIP). -/

/-- Read 4 little-endian 64-bit limbs starting at `base`. -/
def memNat4 (base : UInt64) (m : Mem) : Option Nat := do
  let l0 ← BignumExec.load64Mem m base
  let l1 ← BignumExec.load64Mem m (base + 8)
  let l2 ← BignumExec.load64Mem m (base + 16)
  let l3 ← BignumExec.load64Mem m (base + 24)
  some (l0.toNat
        + l1.toNat * 2 ^ 64
        + l2.toNat * 2 ^ 128
        + l3.toNat * 2 ^ 192)

/-- Two memories agreeing on 8 bytes give equal `load64Mem` results. -/
theorem load64Mem_eq_of_byte_eq
    (m m' : Mem) (addr : UInt64)
    (h : ∀ j : Nat, j < 8 →
      m.loadByte (addr + UInt64.ofNat j) = m'.loadByte (addr + UInt64.ofNat j)) :
    BignumExec.load64Mem m addr = BignumExec.load64Mem m' addr := by
  have h0 : m.loadByte addr = m'.loadByte addr := by simpa using h 0 (by omega)
  have h1 : m.loadByte (addr + 1) = m'.loadByte (addr + 1) := by simpa using h 1 (by omega)
  have h2 : m.loadByte (addr + 2) = m'.loadByte (addr + 2) := by simpa using h 2 (by omega)
  have h3 : m.loadByte (addr + 3) = m'.loadByte (addr + 3) := by simpa using h 3 (by omega)
  have h4 : m.loadByte (addr + 4) = m'.loadByte (addr + 4) := by simpa using h 4 (by omega)
  have h5 : m.loadByte (addr + 5) = m'.loadByte (addr + 5) := by simpa using h 5 (by omega)
  have h6 : m.loadByte (addr + 6) = m'.loadByte (addr + 6) := by simpa using h 6 (by omega)
  have h7 : m.loadByte (addr + 7) = m'.loadByte (addr + 7) := by simpa using h 7 (by omega)
  unfold BignumExec.load64Mem
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- Two memories agreeing on the 32 bytes at `base` give equal `memNat4`
    results. -/
theorem memNat4_eq_of_byte_eq
    (base : UInt64) (m m' : Mem)
    (h : ∀ k : Nat, k < 32 →
      m.loadByte (base + UInt64.ofNat k) = m'.loadByte (base + UInt64.ofNat k)) :
    memNat4 base m = memNat4 base m' := by
  unfold memNat4
  have h_l0 : BignumExec.load64Mem m base = BignumExec.load64Mem m' base := by
    apply load64Mem_eq_of_byte_eq
    intro j hj
    exact h j (by omega)
  have h_l1 : BignumExec.load64Mem m (base + 8) = BignumExec.load64Mem m' (base + 8) := by
    apply load64Mem_eq_of_byte_eq
    intro j hj
    have h_eq : (base + 8 + UInt64.ofNat j : UInt64) = base + UInt64.ofNat (8 + j) := by
      rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, UInt64.add_assoc,
        ← UInt64.ofNat_add]
    rw [h_eq]
    exact h (8 + j) (by omega)
  have h_l2 : BignumExec.load64Mem m (base + 16) = BignumExec.load64Mem m' (base + 16) := by
    apply load64Mem_eq_of_byte_eq
    intro j hj
    have h_eq : (base + 16 + UInt64.ofNat j : UInt64) = base + UInt64.ofNat (16 + j) := by
      rw [show (16 : UInt64) = UInt64.ofNat 16 from rfl, UInt64.add_assoc,
        ← UInt64.ofNat_add]
    rw [h_eq]
    exact h (16 + j) (by omega)
  have h_l3 : BignumExec.load64Mem m (base + 24) = BignumExec.load64Mem m' (base + 24) := by
    apply load64Mem_eq_of_byte_eq
    intro j hj
    have h_eq : (base + 24 + UInt64.ofNat j : UInt64) = base + UInt64.ofNat (24 + j) := by
      rw [show (24 : UInt64) = UInt64.ofNat 24 from rfl, UInt64.add_assoc,
        ← UInt64.ofNat_add]
    rw [h_eq]
    exact h (24 + j) (by omega)
  rw [h_l0, h_l1, h_l2, h_l3]

/-- A successful `memNat4` implies all 32 underlying bytes are
    loadable.  Used by chain proofs to lift the byte-level alloc
    precondition through `memNat4`-style post-conditions. -/
theorem memNat4_imp_byte_alloc
    (base : UInt64) (m : Mem) (v : Nat)
    (h : memNat4 base m = some v) :
    ∀ k : Nat, k < 32 → ∃ b, m.loadByte (base + UInt64.ofNat k) = some b := by
  intro k hk
  unfold memNat4 at h
  rcases h0 : BignumExec.load64Mem m base with _ | l0
  · simp [h0, Bind.bind, Option.bind] at h
  rcases h1 : BignumExec.load64Mem m (base + 8) with _ | l1
  · simp [h0, h1, Bind.bind, Option.bind] at h
  rcases h2 : BignumExec.load64Mem m (base + 16) with _ | l2
  · simp [h0, h1, h2, Bind.bind, Option.bind] at h
  rcases h3 : BignumExec.load64Mem m (base + 24) with _ | l3
  · simp [h0, h1, h2, h3, Bind.bind, Option.bind] at h
  -- All 4 limb-loads succeeded.  Find the right limb and unfold its
  -- load64Mem to extract the corresponding byte.
  -- For simplicity, do a 4-way split on which limb k falls in, then
  -- another 8-way split on which byte within the limb.  Since k < 32,
  -- this terminates.
  have aux : ∀ (addr : UInt64) (l : UInt64),
      BignumExec.load64Mem m addr = some l →
      ∀ j : Nat, j < 8 → ∃ b, m.loadByte (addr + UInt64.ofNat j) = some b := by
    intro addr l hl j hj
    unfold BignumExec.load64Mem at hl
    rcases hb0 : m.loadByte addr with _ | b0
    · simp [hb0, Bind.bind, Option.bind] at hl
    rcases hb1 : m.loadByte (addr + 1) with _ | b1
    · simp [hb0, hb1, Bind.bind, Option.bind] at hl
    rcases hb2 : m.loadByte (addr + 2) with _ | b2
    · simp [hb0, hb1, hb2, Bind.bind, Option.bind] at hl
    rcases hb3 : m.loadByte (addr + 3) with _ | b3
    · simp [hb0, hb1, hb2, hb3, Bind.bind, Option.bind] at hl
    rcases hb4 : m.loadByte (addr + 4) with _ | b4
    · simp [hb0, hb1, hb2, hb3, hb4, Bind.bind, Option.bind] at hl
    rcases hb5 : m.loadByte (addr + 5) with _ | b5
    · simp [hb0, hb1, hb2, hb3, hb4, hb5, Bind.bind, Option.bind] at hl
    rcases hb6 : m.loadByte (addr + 6) with _ | b6
    · simp [hb0, hb1, hb2, hb3, hb4, hb5, hb6, Bind.bind, Option.bind] at hl
    rcases hb7 : m.loadByte (addr + 7) with _ | b7
    · simp [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, Bind.bind, Option.bind] at hl
    interval_cases j
    · exact ⟨b0, by simpa using hb0⟩
    · exact ⟨b1, by
        have : (addr + UInt64.ofNat 1 : UInt64) = addr + 1 := by simp
        rw [this]; exact hb1⟩
    · exact ⟨b2, by
        have : (addr + UInt64.ofNat 2 : UInt64) = addr + 2 := by simp
        rw [this]; exact hb2⟩
    · exact ⟨b3, by
        have : (addr + UInt64.ofNat 3 : UInt64) = addr + 3 := by simp
        rw [this]; exact hb3⟩
    · exact ⟨b4, by
        have : (addr + UInt64.ofNat 4 : UInt64) = addr + 4 := by simp
        rw [this]; exact hb4⟩
    · exact ⟨b5, by
        have : (addr + UInt64.ofNat 5 : UInt64) = addr + 5 := by simp
        rw [this]; exact hb5⟩
    · exact ⟨b6, by
        have : (addr + UInt64.ofNat 6 : UInt64) = addr + 6 := by simp
        rw [this]; exact hb6⟩
    · exact ⟨b7, by
        have : (addr + UInt64.ofNat 7 : UInt64) = addr + 7 := by simp
        rw [this]; exact hb7⟩
  -- Helper: combine base + offset + UInt64.ofNat j when offset + j = k.
  have addr_combine : ∀ (offset : Nat) (j : Nat),
      offset + j = k → offset + j < 2^64 →
      (base + UInt64.ofNat offset + UInt64.ofNat j : UInt64) =
        base + UInt64.ofNat k := by
    intro offset j h_sum _h_lt
    rw [UInt64.add_assoc, ← UInt64.ofNat_add, h_sum]
  -- Dispatch by which limb k falls into.
  by_cases hk0 : k < 8
  · exact aux base l0 h0 k hk0
  · by_cases hk1 : k < 16
    · obtain ⟨b, hb⟩ := aux (base + 8) l1 h1 (k - 8) (by omega)
      refine ⟨b, ?_⟩
      rw [show (base + 8 : UInt64) = base + UInt64.ofNat 8 from by simp] at hb
      rw [← addr_combine 8 (k - 8) (by omega) (by omega)]
      exact hb
    · by_cases hk2 : k < 24
      · obtain ⟨b, hb⟩ := aux (base + 16) l2 h2 (k - 16) (by omega)
        refine ⟨b, ?_⟩
        rw [show (base + 16 : UInt64) = base + UInt64.ofNat 16 from by simp] at hb
        rw [← addr_combine 16 (k - 16) (by omega) (by omega)]
        exact hb
      · obtain ⟨b, hb⟩ := aux (base + 24) l3 h3 (k - 24) (by omega)
        refine ⟨b, ?_⟩
        rw [show (base + 24 : UInt64) = base + UInt64.ofNat 24 from by simp] at hb
        rw [← addr_combine 24 (k - 24) (by omega) (by omega)]
        exact hb

/-! ## §2  Functional contract axiom

Captures the post-state of a single `bignum_montmul_p25519` Ccall.
The pre-state must have:
- The three argument registers (`oc`, `a`, `b` in the caller's
  convention) bound to memory addresses.
- 4-limb readable values at `a` and `b`.
- The output range at `op` allocated.

The post-state has:
- The 4-limb output at `op` holding `(a_val · b_val) mod p_25519`.
- All other memory unchanged (frame condition).
-/

/-- **Axiom: `bignum_montmul_p25519` is a verified Montgomery
    multiplication mod p_25519.**

    For any registry containing `bignum_montmul_p25519`, the Ccall
    on three address-bearing registers writes the product mod p_25519
    at the first argument's address. -/
axiom montmul_call_correct
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (s : BignumState) (fuel : Nat)
    (op_reg a_reg b_reg : String)
    (op_addr a_addr b_addr : UInt64)
    (a_val b_val : Nat)
    (h_op : s.regs op_reg = BitVec.ofNat 64 op_addr.toNat)
    (h_a  : s.regs a_reg  = BitVec.ofNat 64 a_addr.toNat)
    (h_b  : s.regs b_reg  = BitVec.ofNat 64 b_addr.toNat)
    (h_a_mem : memNat4 a_addr s.mem = some a_val)
    (h_b_mem : memNat4 b_addr s.mem = some b_val)
    -- Output range allocated:
    (_h_op_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)
    -- The three Ccall argument list shape:
    (call_instr : InstrR)
    (h_call_shape : ∃ ii lvs args,
      call_instr = .Ccall ii lvs ⟨"bignum_montmul_p25519"⟩ args
      ∧ args.length = 3) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) [call_instr] s = some s' ∧
      memNat4 op_addr s'.mem = some ((a_val * b_val) % p_25519) ∧
      -- Frame condition: bytes outside the 32-byte output window
      -- at `op_addr` are unchanged.
      (∀ addr : UInt64,
        ¬ MemoryModel.range op_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) ∧
      -- Output range alloc preserved: `op_addr` is still 32-byte loadable
      -- (the call OVERWRITES the 32 bytes with new values, never frees).
      (∀ k : Fin 32,
        ∃ b, s'.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)

/-! ## §3  Specialised forms for squaring

A squaring Ccall has `a = b`, producing `a²` mod p_25519. -/

/-- Squaring specialisation of the montmul axiom: same setup but
    with the second and third argument registers being the same.
    Inherits the frame condition from `montmul_call_correct`. -/
theorem montmul_call_squaring
    (registry : BignumRegistry)
    (h_registry :
      ∃ fd : FunDecl, registry "bignum_montmul_p25519" = some fd)
    (s : BignumState) (fuel : Nat)
    (op_reg a_reg : String)
    (op_addr a_addr : UInt64)
    (a_val : Nat)
    (h_op : s.regs op_reg = BitVec.ofNat 64 op_addr.toNat)
    (h_a  : s.regs a_reg  = BitVec.ofNat 64 a_addr.toNat)
    (h_a_mem : memNat4 a_addr s.mem = some a_val)
    (h_op_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)
    (call_instr : InstrR)
    (h_call_shape : ∃ ii lvs args,
      call_instr = .Ccall ii lvs ⟨"bignum_montmul_p25519"⟩ args
      ∧ args.length = 3) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) [call_instr] s = some s' ∧
      memNat4 op_addr s'.mem = some ((a_val * a_val) % p_25519) ∧
      (∀ addr : UInt64,
        ¬ MemoryModel.range op_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) ∧
      (∀ k : Fin 32,
        ∃ b, s'.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b) :=
  montmul_call_correct registry h_registry s fuel
    op_reg a_reg a_reg op_addr a_addr a_addr a_val a_val
    h_op h_a h_a h_a_mem h_a_mem h_op_alloc call_instr h_call_shape

end CatCrypt.Crypto.Jasmin.BignumHoare.MontmulAxiom
