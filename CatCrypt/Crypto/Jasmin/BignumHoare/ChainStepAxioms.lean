/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.BignumHoare.MontmulAxiom
public import CatCrypt.Crypto.Jasmin.S2NBignumSSA
public import CatCrypt.Tactics.PreservationCombinator

/-!
# Chain-step contracts: granularity for per-block discharge

Higher-level contracts that abstract whole `sqr_step` /
`mul_step` / `repeated_sqr_then_mul` operations (rather than
individual Ccalls).  This is the natural granularity for chain-
level proofs.

Each contract captures the post-state of running a complete chain
step (3 addrInits + 1 Ccall) starting from a state with `op`/`ap`
bound and 4-limb-readable inputs at the source offsets.

## Trust set delta

This file declares **0 axioms**.  Every theorem takes the
`MontmulCallFacts registry` hypothesis structure (`MontmulAxiom.lean`)
and is discharged from its `call_correct` field plus the
deterministic `addrInit` walk codified in §0a/§0b.

## Discharge path

`chain_sqr_step_correct` is discharged by:
1. The `addrInit` instruction sequences are deterministic;
   `bignumExecFuel` on them produces predictable register
   updates (lemmas in §0b: `addrInit_uses_op`, `addrInit_uses_ap`,
   `addrInit_uses_op_offset`).
2. After the 3 addrInits, the registers `oc`, `a`, `b` hold the
   intended addresses; memory is unchanged.
3. The single `Ccall` then reduces to `MontmulCallFacts.call_correct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.ChainStepAxioms

open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.S2NBignumSSA
open CatCrypt.Crypto.Jasmin.BignumHoare.MontmulAxiom

/-! ## §0a  Forward sequencing for `bignumExecFuel`

`bignumExec_append` (in `BignumExec.lean`) is a *destructor* — given a
successful run of `body1 ++ body2`, it splits into two sub-runs.
For the discharge of `chain_sqr_step_correct`, we want the *constructor*
direction: from two successful sub-runs, build one successful run on
the appended body.  For straight-line `Cassgn` instructions this is
purely structural. -/

/-- Forward sequencing for straight-line `bignumExecFuel` runs:
    if `body1` (only `Cassgn`s) succeeds and `body2` succeeds, then so
    does `body1 ++ body2`.  Specialised to bodies whose every
    instruction is a `Cassgn`. -/
theorem bignumExecFuel_append_cassgn
    (registry : BignumRegistry) (fuel : Nat) (body1 body2 : List InstrR)
    (h_cassgn : ∀ i ∈ body1, ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs)
    (s s_mid s' : BignumState)
    (h1 : bignumExecFuel registry (fuel + 1) body1 s = some s_mid)
    (h2 : bignumExecFuel registry (fuel + 1) body2 s_mid = some s') :
    bignumExecFuel registry (fuel + 1) (body1 ++ body2) s = some s' := by
  induction body1 generalizing s s_mid with
  | nil =>
    simp only [bignumExecFuel] at h1
    simp only [List.nil_append]
    cases h1
    exact h2
  | cons i is ih =>
    obtain ⟨lv, tag, ty, rhs, h_eq⟩ := h_cassgn i (List.mem_cons_self ..)
    subst h_eq
    -- Step on the head Cassgn.
    simp only [bignumExecFuel] at h1
    -- Now h1 : (match execInstr s (Cassgn lv tag ty rhs) with ...) = some s_mid
    cases h_step : execInstr s (.Cassgn lv tag ty rhs) with
    | none => simp [h_step] at h1
    | some s1 =>
      simp only [h_step] at h1
      simp only [List.cons_append, bignumExecFuel, h_step]
      have h_tail : ∀ j ∈ is, ∃ lv tag ty rhs, j = .Cassgn lv tag ty rhs :=
        fun j hj => h_cassgn j (List.mem_cons_of_mem _ hj)
      exact ih h_tail s1 s_mid h1 h2

/-! ## §0b  Single-step `addrInit` semantics

`BignumInvP25519.addrInit name k` produces 1 instruction when
`k = 0` (alias `op`) or `k = -1` (alias `ap`), else 2 instructions
(`name := op; name := name + k`).  We characterise each case's
post-state. -/

/-- Specialised `addrInit "name" 0`: `name := op`.  Only register
    `name` is changed (set to the value of `op`); memory is
    untouched. -/
theorem addrInit_zero_succ
    (registry : BignumRegistry) (fuel : Nat) (s : BignumState)
    (lvalName : String) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit lvalName 0) s = some s' ∧
      s'.regs lvalName = s.regs "op" ∧
      s'.mem = s.mem ∧
      ∀ r, r ≠ lvalName → s'.regs r = s.regs r := by
  -- Unfold to the single-Cassgn body.
  refine ⟨setReg s lvalName (s.regs "op"), ?_, ?_, ?_, ?_⟩
  · simp only [BignumInvP25519.addrInit, if_true,
      bignumExecFuel, execInstr]
    rfl
  · simp [setReg]
  · rfl
  · intro r hr
    simp [setReg, hr]

/-- Specialised `addrInit "name" (-1)`: `name := ap`.  Only register
    `name` is changed (set to the value of `ap`); memory is
    untouched. -/
theorem addrInit_negOne_succ
    (registry : BignumRegistry) (fuel : Nat) (s : BignumState)
    (lvalName : String) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit lvalName (-1)) s = some s' ∧
      s'.regs lvalName = s.regs "ap" ∧
      s'.mem = s.mem ∧
      ∀ r, r ≠ lvalName → s'.regs r = s.regs r := by
  -- Unfold; the if-branch on `(-1) = 0` is false; the inner `(-1) = -1`
  -- is true, so we land in the second-arm one-instruction body.
  refine ⟨setReg s lvalName (s.regs "ap"), ?_, ?_, ?_, ?_⟩
  · simp only [BignumInvP25519.addrInit, show ((-1 : Int) = 0) = False from
      by decide, if_false, if_true,
      bignumExecFuel, execInstr]
    rfl
  · simp [setReg]
  · rfl
  · intro r hr
    simp [setReg, hr]

/-- Generic `addrInit "name" k` with `k ≠ 0` and `k ≠ -1`: emits
    `name := op; name := name + k`, so the post-state has
    `name = op + k`.  Memory is unchanged.  Registers other than
    `name` are unchanged. -/
theorem addrInit_generic_succ
    (registry : BignumRegistry) (fuel : Nat) (s : BignumState)
    (lvalName : String) (k : Int) (hk0 : k ≠ 0) (hkm1 : k ≠ -1) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit lvalName k) s = some s' ∧
      s'.regs lvalName = s.regs "op" + BitVec.ofInt 64 k ∧
      s'.mem = s.mem ∧
      ∀ r, r ≠ lvalName → s'.regs r = s.regs r := by
  -- The two-Cassgn body executes deterministically.
  -- Step 1: `name := op` → `setReg s name (s.regs "op")`.
  -- Step 2: `name := name + k` (over the *new* state) →
  --         `setReg ... name ((s.regs "op") + BitVec.ofInt 64 k)`.
  let s2 : BignumState :=
    setReg (setReg s lvalName (s.regs "op")) lvalName
      (s.regs "op" + BitVec.ofInt 64 k)
  refine ⟨s2, ?_, ?_, ?_, ?_⟩
  · -- Reduce both Cassgns explicitly.
    simp only [BignumInvP25519.addrInit, if_neg hk0, if_neg hkm1,
      bignumExecFuel, execInstr]
    -- After 1st Cassgn: state = setReg s lvalName (s.regs "op")
    -- The 2nd Cassgn reads `pv lvalName` which is `Pvar` of lvalName.
    -- evalPExpr (setReg s lvalName _) on Pvar of lvalName = s.regs "op";
    -- evalPExpr on Pconst k = BitVec.ofInt 64 k.
    -- Papp2 Oadd → sum.
    -- Then setReg again → s2.
    -- Reduce the inner state's `regs lvalName`:
    show some _ = some s2
    congr 1
    show setReg (setReg s lvalName (s.regs "op")) lvalName _ = s2
    show setReg (setReg s lvalName (s.regs "op")) lvalName
        ((setReg s lvalName (s.regs "op")).regs lvalName +
          BitVec.ofInt 64 k) = s2
    simp [setReg, s2]
  · simp [s2, setReg]
  · simp [s2, setReg]
  · intro r hr
    simp [s2, setReg, hr]

/-! ## §0c  Re-export of chain-step body shapes

`BignumInvP25519`'s `sqr_step` constructs `addrInit "oc" dstOff ++
addrInit "a" srcOff ++ addrInit "b" srcOff ++ [Ccall ...]`.  For a
single squaring chain step that is *block2-shaped* (generic `dstOff`
≠ {0, −1}, special `srcOff = −1`) we walk through all four sub-pieces
in sequence. -/

/-! ## §1  Single-step theorems -/

/-- Block2-shaped `sqr_step` (generic `dstOff`, alias `srcOff = −1`):
    running `BignumInvP25519.sqr_step idx dstOff (-1)` computes
    `dst := ap² mod p_25519`, where `dst_addr.toNat` matches the
    bitvector arithmetic that `addrInit` performs (`op + dstOff`).

    Discharged from:
    * `addrInit_generic_succ` (for `oc := op + dstOff` with `dstOff ≠ {0,−1}`),
    * `addrInit_negOne_succ` (twice, for `a := ap` and `b := ap`),
    * `MontmulCallFacts.call_correct` (for the Ccall),
    * straight-line composition via `bignumExecFuel_append_cassgn`. -/
theorem chain_sqr_step_correct
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr : UInt64) (ap_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    -- The chain step's source: aliased `ap` (matches `OFF_ap = -1`).
    (src_addr : UInt64)
    (h_src_eq : src_addr = ap_addr)
    (a_val : Nat)
    (h_a_mem : memNat4 src_addr s.mem = some a_val)
    -- The chain step's destination: `op_addr + dstOff` cast back to UInt64.
    (dst_addr : UInt64)
    (h_dst_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b)
    -- Shape: the body is the public `sqr_step` constructor's output.
    (idx : Nat) (dstOff : Int)
    (h_dstOff_ne_zero : dstOff ≠ 0) (h_dstOff_ne_negOne : dstOff ≠ -1)
    (h_dst_addr_eq :
      BitVec.ofNat 64 dst_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 dstOff)
    (sqr_body : List InstrR)
    (h_shape : sqr_body = BignumInvP25519.sqr_step idx dstOff (-1)) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) sqr_body s = some s' ∧
      memNat4 dst_addr s'.mem = some ((a_val * a_val) % p_25519) ∧
      -- Frame: bytes outside the 32-byte dst window are unchanged.
      (∀ addr : UInt64,
        ¬ MemoryModel.range dst_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) := by
  -- Unfold sqr_body's shape into the four pieces.
  subst h_shape
  -- Get post-state of `addrInit "oc" dstOff` (generic case).
  obtain ⟨s_oc, h_oc_run, h_oc_reg, h_oc_mem, h_oc_other⟩ :=
    addrInit_generic_succ registry fuel s "oc" dstOff
      h_dstOff_ne_zero h_dstOff_ne_negOne
  -- Get post-state of `addrInit "a" (-1)` from s_oc.
  obtain ⟨s_a, h_a_run, h_a_reg, h_a_mem_eq, h_a_other⟩ :=
    addrInit_negOne_succ registry fuel s_oc "a"
  -- Get post-state of `addrInit "b" (-1)` from s_a.
  obtain ⟨s_b, h_b_run, h_b_reg, h_b_mem_eq, h_b_other⟩ :=
    addrInit_negOne_succ registry fuel s_a "b"
  -- After three addrInits, we have:
  -- * s_b.regs "oc" = s.regs "op" + BitVec.ofInt 64 dstOff = BitVec.ofNat 64 dst_addr.toNat
  -- * s_b.regs "a" = s_a.regs "ap" = s_oc.regs "ap" = s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat
  -- * s_b.regs "b" = s_a.regs "ap" = ... = BitVec.ofNat 64 ap_addr.toNat
  -- * s_b.mem = s.mem
  have h_oc_at_b : s_b.regs "oc" = BitVec.ofNat 64 dst_addr.toNat := by
    rw [h_b_other "oc" (by decide), h_a_other "oc" (by decide), h_oc_reg, h_op]
    exact h_dst_addr_eq.symm
  have h_a_at_b : s_b.regs "a" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [h_b_other "a" (by decide), h_a_reg, h_oc_other "ap" (by decide), h_ap]
  have h_b_at_b : s_b.regs "b" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [h_b_reg, h_a_other "ap" (by decide), h_oc_other "ap" (by decide), h_ap]
  have h_mem_at_b : s_b.mem = s.mem := by
    rw [h_b_mem_eq, h_a_mem_eq, h_oc_mem]
  -- The 4-limb input at src_addr (= ap_addr) is preserved.
  have h_src_mem_at_b : memNat4 src_addr s_b.mem = some a_val := by
    rw [h_mem_at_b]; exact h_a_mem
  have h_b_mem_for_montmul : memNat4 ap_addr s_b.mem = some a_val := by
    rw [h_src_eq] at h_src_mem_at_b
    exact h_src_mem_at_b
  -- The output range at dst_addr is allocated.
  have h_dst_alloc_at_b : ∀ k : Fin 32,
      ∃ b, s_b.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b := by
    intro k; rw [h_mem_at_b]; exact h_dst_alloc k
  -- Apply MontmulCallFacts.call_correct on s_b.
  let call_instr : InstrR :=
    .Ccall .DoNotInline []
      { name := "bignum_montmul_p25519" }
      [.Pvar { gv := { var := { vname := "oc", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "a", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "b", vtype := .sword .U64 },
                       info := {} }, gs := false }]
  have h_call_shape : ∃ (ii : InlineInfo) (op_v a_v b_v : GVar),
      call_instr = .Ccall ii [] ⟨"bignum_montmul_p25519"⟩
        [.Pvar op_v, .Pvar a_v, .Pvar b_v]
      ∧ op_v.gv.var.vname = "oc"
      ∧ a_v.gv.var.vname = "a"
      ∧ b_v.gv.var.vname = "b" :=
    ⟨.DoNotInline, _, _, _, rfl, rfl, rfl, rfl⟩
  obtain ⟨s_final, h_call_run, h_call_post, h_call_frame, _h_call_alloc⟩ :=
    hAx.call_correct s_b fuel
      "oc" "a" "b" dst_addr ap_addr ap_addr a_val a_val
      h_oc_at_b h_a_at_b h_b_at_b h_b_mem_for_montmul h_b_mem_for_montmul
      h_dst_alloc_at_b call_instr h_call_shape
  -- Frame on the chain step: addrInits don't touch memory, so
  -- `s_b.mem = s.mem` and montmul's frame at `dst_addr` lifts through.
  have h_frame : ∀ addr : UInt64,
      ¬ MemoryModel.range dst_addr 32 addr →
      s_final.mem.loadByte addr = s.mem.loadByte addr := by
    intro addr h_addr
    have h_mont := h_call_frame addr h_addr
    rw [h_mont, h_mem_at_b]
  -- Compose the four runs into a single run on the full sqr_body.
  refine ⟨s_final, ?_, h_call_post, h_frame⟩
  -- Goal: bignumExecFuel registry (fuel + 1) (full_body) s = some s_final.
  -- Strategy: associate-right and apply the cassgn-append lemma three times.
  -- full_body = (oc_init ++ a_init) ++ (b_init ++ [call_instr])
  -- We'll build it step by step.
  show bignumExecFuel registry (fuel + 1)
    (BignumInvP25519.sqr_step idx dstOff (-1)) s = some s_final
  -- Unfold sqr_step.
  show bignumExecFuel registry (fuel + 1)
    (BignumInvP25519.addrInit "oc" dstOff ++
     BignumInvP25519.addrInit "a" (-1) ++
     BignumInvP25519.addrInit "b" (-1) ++
     [.Ccall .DoNotInline []
        { name := "bignum_montmul_p25519" }
        [.Pvar { gv := { var := { vname := "oc", vtype := .sword .U64 },
                         info := {} }, gs := false },
         .Pvar { gv := { var := { vname := "a", vtype := .sword .U64 },
                         info := {} }, gs := false },
         .Pvar { gv := { var := { vname := "b", vtype := .sword .U64 },
                         info := {} }, gs := false }]]) s = some s_final
  -- Each addrInit body is a list of Cassgn-only instructions.
  have h_oc_cassgn : ∀ i ∈ BignumInvP25519.addrInit "oc" dstOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_dstOff_ne_zero,
      if_neg h_dstOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  have h_a_cassgn : ∀ i ∈ BignumInvP25519.addrInit "a" (-1),
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, show ((-1 : Int) = 0) = False from
      by decide,
      if_false, if_true, List.mem_singleton] at hi
    subst hi
    refine ⟨_, _, _, _, rfl⟩
  have h_b_cassgn : ∀ i ∈ BignumInvP25519.addrInit "b" (-1),
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, show ((-1 : Int) = 0) = False from
      by decide,
      if_false, if_true, List.mem_singleton] at hi
    subst hi
    refine ⟨_, _, _, _, rfl⟩
  -- Build the chain.  Compose oc_init ∘ (a_init ∘ (b_init ∘ [call])).
  have step_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "b" (-1) ++ [call_instr]) s_a = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_b_cassgn s_a s_b s_final h_b_run
    exact h_call_run
  have step_a_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "a" (-1) ++
         (BignumInvP25519.addrInit "b" (-1) ++ [call_instr])) s_oc = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_a_cassgn s_oc s_a s_final h_a_run
    exact step_b_call
  have step_full :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" dstOff ++
         (BignumInvP25519.addrInit "a" (-1) ++
          (BignumInvP25519.addrInit "b" (-1) ++ [call_instr]))) s = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_oc_cassgn s s_oc s_final h_oc_run
    exact step_a_b_call
  -- Re-bracket via List.append_assoc to match sqr_step's actual layout.
  have h_assoc : (BignumInvP25519.addrInit "oc" dstOff ++
       BignumInvP25519.addrInit "a" (-1) ++
       BignumInvP25519.addrInit "b" (-1) ++
       [call_instr]) =
      BignumInvP25519.addrInit "oc" dstOff ++
       (BignumInvP25519.addrInit "a" (-1) ++
        (BignumInvP25519.addrInit "b" (-1) ++ [call_instr])) := by
    simp [List.append_assoc]
  show bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" dstOff ++
         BignumInvP25519.addrInit "a" (-1) ++
         BignumInvP25519.addrInit "b" (-1) ++
         [call_instr]) s = some s_final
  rw [h_assoc]
  exact step_full

/-- Block-4-shaped `mul_step` (all three offsets generic, i.e. ≠ {0, −1}):
    running `BignumInvP25519.mul_step idx dstOff aOff bOff` computes
    `dst := a · b mod p_25519`, where `dst_addr.toNat`, `a_addr.toNat`,
    `b_addr.toNat` match the bitvector arithmetic that `addrInit` performs
    (`op + offset`).

    Discharged from:
    * `addrInit_generic_succ` (three times, for `oc`, `a`, `b` with their
      respective generic offsets),
    * `MontmulCallFacts.call_correct` (for the Ccall),
    * straight-line composition via `bignumExecFuel_append_cassgn`. -/
theorem chain_mul_step_correct
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr : UInt64) (ap_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (a_addr b_addr : UInt64)
    (a_val b_val : Nat)
    (h_a_mem : memNat4 a_addr s.mem = some a_val)
    (h_b_mem : memNat4 b_addr s.mem = some b_val)
    (dst_addr : UInt64)
    (h_dst_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b)
    -- Shape: the body is the public `mul_step` constructor's output,
    -- specialised to the all-generic offsets case (the only one used in
    -- `BignumInvP25519.body`).
    (idx : Nat) (dstOff aOff bOff : Int)
    (h_dstOff_ne_zero : dstOff ≠ 0) (h_dstOff_ne_negOne : dstOff ≠ -1)
    (h_aOff_ne_zero : aOff ≠ 0) (h_aOff_ne_negOne : aOff ≠ -1)
    (h_bOff_ne_zero : bOff ≠ 0) (h_bOff_ne_negOne : bOff ≠ -1)
    (h_dst_addr_eq :
      BitVec.ofNat 64 dst_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 dstOff)
    (h_a_addr_eq :
      BitVec.ofNat 64 a_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 aOff)
    (h_b_addr_eq :
      BitVec.ofNat 64 b_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 bOff)
    (mul_body : List InstrR)
    (h_shape : mul_body = BignumInvP25519.mul_step idx dstOff aOff bOff) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) mul_body s = some s' ∧
      memNat4 dst_addr s'.mem = some ((a_val * b_val) % p_25519) ∧
      -- Frame: bytes outside the 32-byte dst window are unchanged.
      (∀ addr : UInt64,
        ¬ MemoryModel.range dst_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) := by
  -- Mirror the proof of `chain_sqr_step_correct`: walk through the three
  -- addrInits (all generic), then apply `MontmulCallFacts.call_correct`, then glue.
  subst h_shape
  -- Get post-state of `addrInit "oc" dstOff` (generic case).
  obtain ⟨s_oc, h_oc_run, h_oc_reg, h_oc_mem, h_oc_other⟩ :=
    addrInit_generic_succ registry fuel s "oc" dstOff
      h_dstOff_ne_zero h_dstOff_ne_negOne
  -- Get post-state of `addrInit "a" aOff` (generic case) from s_oc.
  obtain ⟨s_a, h_a_run, h_a_reg, h_a_mem_eq, h_a_other⟩ :=
    addrInit_generic_succ registry fuel s_oc "a" aOff
      h_aOff_ne_zero h_aOff_ne_negOne
  -- Get post-state of `addrInit "b" bOff` (generic case) from s_a.
  obtain ⟨s_b, h_b_run, h_b_reg, h_b_mem_eq, h_b_other⟩ :=
    addrInit_generic_succ registry fuel s_a "b" bOff
      h_bOff_ne_zero h_bOff_ne_negOne
  -- After three addrInits, registers `oc`, `a`, `b` hold the intended
  -- addresses; memory unchanged.
  have h_oc_at_b : s_b.regs "oc" = BitVec.ofNat 64 dst_addr.toNat := by
    rw [h_b_other "oc" (by decide), h_a_other "oc" (by decide), h_oc_reg, h_op]
    exact h_dst_addr_eq.symm
  have h_a_at_b : s_b.regs "a" = BitVec.ofNat 64 a_addr.toNat := by
    rw [h_b_other "a" (by decide), h_a_reg, h_oc_other "op" (by decide), h_op]
    exact h_a_addr_eq.symm
  have h_b_at_b : s_b.regs "b" = BitVec.ofNat 64 b_addr.toNat := by
    rw [h_b_reg, h_a_other "op" (by decide), h_oc_other "op" (by decide), h_op]
    exact h_b_addr_eq.symm
  have h_mem_at_b : s_b.mem = s.mem := by
    rw [h_b_mem_eq, h_a_mem_eq, h_oc_mem]
  -- The 4-limb inputs at a_addr and b_addr are preserved.
  have h_a_mem_at_b : memNat4 a_addr s_b.mem = some a_val := by
    rw [h_mem_at_b]; exact h_a_mem
  have h_b_mem_at_b : memNat4 b_addr s_b.mem = some b_val := by
    rw [h_mem_at_b]; exact h_b_mem
  -- The output range at dst_addr is allocated.
  have h_dst_alloc_at_b : ∀ k : Fin 32,
      ∃ b, s_b.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b := by
    intro k; rw [h_mem_at_b]; exact h_dst_alloc k
  -- Apply MontmulCallFacts.call_correct on s_b.
  let call_instr : InstrR :=
    .Ccall .DoNotInline []
      { name := "bignum_montmul_p25519" }
      [.Pvar { gv := { var := { vname := "oc", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "a", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "b", vtype := .sword .U64 },
                       info := {} }, gs := false }]
  have h_call_shape : ∃ (ii : InlineInfo) (op_v a_v b_v : GVar),
      call_instr = .Ccall ii [] ⟨"bignum_montmul_p25519"⟩
        [.Pvar op_v, .Pvar a_v, .Pvar b_v]
      ∧ op_v.gv.var.vname = "oc"
      ∧ a_v.gv.var.vname = "a"
      ∧ b_v.gv.var.vname = "b" :=
    ⟨.DoNotInline, _, _, _, rfl, rfl, rfl, rfl⟩
  obtain ⟨s_final, h_call_run, h_call_post, h_call_frame, _h_call_alloc⟩ :=
    hAx.call_correct s_b fuel
      "oc" "a" "b" dst_addr a_addr b_addr a_val b_val
      h_oc_at_b h_a_at_b h_b_at_b h_a_mem_at_b h_b_mem_at_b
      h_dst_alloc_at_b call_instr h_call_shape
  -- Frame on the chain step: addrInits don't touch memory, so
  -- `s_b.mem = s.mem` and montmul's frame at `dst_addr` lifts through.
  have h_frame : ∀ addr : UInt64,
      ¬ MemoryModel.range dst_addr 32 addr →
      s_final.mem.loadByte addr = s.mem.loadByte addr := by
    intro addr h_addr
    have h_mont := h_call_frame addr h_addr
    rw [h_mont, h_mem_at_b]
  -- Compose the four runs into a single run on the full mul_body.
  refine ⟨s_final, ?_, h_call_post, h_frame⟩
  show bignumExecFuel registry (fuel + 1)
    (BignumInvP25519.mul_step idx dstOff aOff bOff) s = some s_final
  show bignumExecFuel registry (fuel + 1)
    (BignumInvP25519.addrInit "oc" dstOff ++
     BignumInvP25519.addrInit "a" aOff ++
     BignumInvP25519.addrInit "b" bOff ++
     [.Ccall .DoNotInline []
        { name := "bignum_montmul_p25519" }
        [.Pvar { gv := { var := { vname := "oc", vtype := .sword .U64 },
                         info := {} }, gs := false },
         .Pvar { gv := { var := { vname := "a", vtype := .sword .U64 },
                         info := {} }, gs := false },
         .Pvar { gv := { var := { vname := "b", vtype := .sword .U64 },
                         info := {} }, gs := false }]]) s = some s_final
  -- Each addrInit body is a list of Cassgn-only instructions.
  have h_oc_cassgn : ∀ i ∈ BignumInvP25519.addrInit "oc" dstOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_dstOff_ne_zero,
      if_neg h_dstOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  have h_a_cassgn : ∀ i ∈ BignumInvP25519.addrInit "a" aOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_aOff_ne_zero,
      if_neg h_aOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  have h_b_cassgn : ∀ i ∈ BignumInvP25519.addrInit "b" bOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_bOff_ne_zero,
      if_neg h_bOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  -- Build the chain.  Compose oc_init ∘ (a_init ∘ (b_init ∘ [call])).
  have step_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "b" bOff ++ [call_instr]) s_a = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_b_cassgn s_a s_b s_final h_b_run
    exact h_call_run
  have step_a_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "a" aOff ++
         (BignumInvP25519.addrInit "b" bOff ++ [call_instr])) s_oc = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_a_cassgn s_oc s_a s_final h_a_run
    exact step_b_call
  have step_full :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" dstOff ++
         (BignumInvP25519.addrInit "a" aOff ++
          (BignumInvP25519.addrInit "b" bOff ++ [call_instr]))) s = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_oc_cassgn s s_oc s_final h_oc_run
    exact step_a_b_call
  -- Re-bracket via List.append_assoc to match mul_step's actual layout.
  have h_assoc : (BignumInvP25519.addrInit "oc" dstOff ++
       BignumInvP25519.addrInit "a" aOff ++
       BignumInvP25519.addrInit "b" bOff ++
       [call_instr]) =
      BignumInvP25519.addrInit "oc" dstOff ++
       (BignumInvP25519.addrInit "a" aOff ++
        (BignumInvP25519.addrInit "b" bOff ++ [call_instr])) := by
    simp [List.append_assoc]
  show bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" dstOff ++
         BignumInvP25519.addrInit "a" aOff ++
         BignumInvP25519.addrInit "b" bOff ++
         [call_instr]) s = some s_final
  rw [h_assoc]
  exact step_full

/-- **Generic-source squaring step.**  When `srcOff ≠ {0, −1}`,
    `BignumInvP25519.sqr_step idx dstOff srcOff` and
    `BignumInvP25519.mul_step idx dstOff srcOff srcOff` produce
    *identical* instruction sequences (both unfold to the same three
    `addrInit`s plus the same Ccall), so this is a 1-line lift of
    `chain_mul_step_correct` with `aOff = bOff = srcOff` and
    `a_addr = b_addr = src_addr`.

    Needed for the inductive `repeated_sqr_then_mul` discharge: the
    loop iterations call `sqr_step idx other cur` where `cur` ranges
    over `{OFF_t, OFF_u}` (both generic), not `OFF_ap = -1`. -/
theorem chain_sqr_step_correct_generic
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr : UInt64) (ap_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (src_addr : UInt64)
    (a_val : Nat)
    (h_a_mem : memNat4 src_addr s.mem = some a_val)
    (dst_addr : UInt64)
    (h_dst_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b)
    (idx : Nat) (dstOff srcOff : Int)
    (h_dstOff_ne_zero : dstOff ≠ 0) (h_dstOff_ne_negOne : dstOff ≠ -1)
    (h_srcOff_ne_zero : srcOff ≠ 0) (h_srcOff_ne_negOne : srcOff ≠ -1)
    (h_dst_addr_eq :
      BitVec.ofNat 64 dst_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 dstOff)
    (h_src_addr_eq :
      BitVec.ofNat 64 src_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 srcOff)
    (sqr_body : List InstrR)
    (h_shape : sqr_body = BignumInvP25519.sqr_step idx dstOff srcOff) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) sqr_body s = some s' ∧
      memNat4 dst_addr s'.mem = some ((a_val * a_val) % p_25519) ∧
      (∀ addr : UInt64,
        ¬ MemoryModel.range dst_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) := by
  -- `sqr_step idx dstOff srcOff = mul_step idx dstOff srcOff srcOff`
  -- by definitional equality (both unfold to the same body).
  have h_eq : BignumInvP25519.sqr_step idx dstOff srcOff =
              BignumInvP25519.mul_step idx dstOff srcOff srcOff := rfl
  rw [h_eq] at h_shape
  exact chain_mul_step_correct registry hAx s fuel
    op_addr ap_addr h_op h_ap
    src_addr src_addr a_val a_val h_a_mem h_a_mem
    dst_addr h_dst_alloc
    idx dstOff srcOff srcOff
    h_dstOff_ne_zero h_dstOff_ne_negOne
    h_srcOff_ne_zero h_srcOff_ne_negOne
    h_srcOff_ne_zero h_srcOff_ne_negOne
    h_dst_addr_eq h_src_addr_eq h_src_addr_eq
    sqr_body h_shape

/-- **`mul_step` with `dstOff = 0`.**  Specialised variant where the
    destination is the `op` register itself (e.g. block 13's terminal
    `op := z2_250_0^32 · z11`).  The `oc` register is initialised via
    `addrInit_zero_succ` (single Cassgn `oc := op`) rather than the
    two-Cassgn generic case.

    `aOff` and `bOff` remain generic.  Result lands at `op_addr`. -/
theorem chain_mul_step_correct_dst_zero
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (a_addr b_addr : UInt64)
    (a_val b_val : Nat)
    (h_a_mem : memNat4 a_addr s.mem = some a_val)
    (h_b_mem : memNat4 b_addr s.mem = some b_val)
    (h_op_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)
    (idx : Nat) (aOff bOff : Int)
    (h_aOff_ne_zero : aOff ≠ 0) (h_aOff_ne_negOne : aOff ≠ -1)
    (h_bOff_ne_zero : bOff ≠ 0) (h_bOff_ne_negOne : bOff ≠ -1)
    (h_a_addr_eq :
      BitVec.ofNat 64 a_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 aOff)
    (h_b_addr_eq :
      BitVec.ofNat 64 b_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 bOff)
    (mul_body : List InstrR)
    (h_shape : mul_body = BignumInvP25519.mul_step idx 0 aOff bOff) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) mul_body s = some s' ∧
      memNat4 op_addr s'.mem = some ((a_val * b_val) % p_25519) ∧
      (∀ addr : UInt64,
        ¬ MemoryModel.range op_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) := by
  subst h_shape
  -- Step 1: addrInit "oc" 0 → s_oc.regs "oc" = s.regs "op" = op_addr.
  obtain ⟨s_oc, h_oc_run, h_oc_reg, h_oc_mem, h_oc_other⟩ :=
    addrInit_zero_succ registry fuel s "oc"
  -- Step 2: addrInit "a" aOff (generic) from s_oc.
  obtain ⟨s_a, h_a_run, h_a_reg, h_a_mem_eq, h_a_other⟩ :=
    addrInit_generic_succ registry fuel s_oc "a" aOff
      h_aOff_ne_zero h_aOff_ne_negOne
  -- Step 3: addrInit "b" bOff (generic) from s_a.
  obtain ⟨s_b, h_b_run, h_b_reg, h_b_mem_eq, h_b_other⟩ :=
    addrInit_generic_succ registry fuel s_a "b" bOff
      h_bOff_ne_zero h_bOff_ne_negOne
  have h_oc_at_b : s_b.regs "oc" = BitVec.ofNat 64 op_addr.toNat := by
    rw [h_b_other "oc" (by decide), h_a_other "oc" (by decide), h_oc_reg, h_op]
  have h_a_at_b : s_b.regs "a" = BitVec.ofNat 64 a_addr.toNat := by
    rw [h_b_other "a" (by decide), h_a_reg, h_oc_other "op" (by decide), h_op]
    exact h_a_addr_eq.symm
  have h_b_at_b : s_b.regs "b" = BitVec.ofNat 64 b_addr.toNat := by
    rw [h_b_reg, h_a_other "op" (by decide), h_oc_other "op" (by decide), h_op]
    exact h_b_addr_eq.symm
  have h_mem_at_b : s_b.mem = s.mem := by
    rw [h_b_mem_eq, h_a_mem_eq, h_oc_mem]
  have h_a_mem_at_b : memNat4 a_addr s_b.mem = some a_val := by
    rw [h_mem_at_b]; exact h_a_mem
  have h_b_mem_at_b : memNat4 b_addr s_b.mem = some b_val := by
    rw [h_mem_at_b]; exact h_b_mem
  have h_op_alloc_at_b : ∀ k : Fin 32,
      ∃ b, s_b.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b := by
    intro k; rw [h_mem_at_b]; exact h_op_alloc k
  let call_instr : InstrR :=
    .Ccall .DoNotInline []
      { name := "bignum_montmul_p25519" }
      [.Pvar { gv := { var := { vname := "oc", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "a", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "b", vtype := .sword .U64 },
                       info := {} }, gs := false }]
  have h_call_shape : ∃ (ii : InlineInfo) (op_v a_v b_v : GVar),
      call_instr = .Ccall ii [] ⟨"bignum_montmul_p25519"⟩
        [.Pvar op_v, .Pvar a_v, .Pvar b_v]
      ∧ op_v.gv.var.vname = "oc"
      ∧ a_v.gv.var.vname = "a"
      ∧ b_v.gv.var.vname = "b" :=
    ⟨.DoNotInline, _, _, _, rfl, rfl, rfl, rfl⟩
  obtain ⟨s_final, h_call_run, h_call_post, h_call_frame, _h_call_alloc⟩ :=
    hAx.call_correct s_b fuel
      "oc" "a" "b" op_addr a_addr b_addr a_val b_val
      h_oc_at_b h_a_at_b h_b_at_b h_a_mem_at_b h_b_mem_at_b
      h_op_alloc_at_b call_instr h_call_shape
  have h_frame : ∀ addr : UInt64,
      ¬ MemoryModel.range op_addr 32 addr →
      s_final.mem.loadByte addr = s.mem.loadByte addr := by
    intro addr h_addr
    have h_mont := h_call_frame addr h_addr
    rw [h_mont, h_mem_at_b]
  refine ⟨s_final, ?_, h_call_post, h_frame⟩
  -- Now compose: addrInit "oc" 0 is a 1-Cassgn body (h_oc_cassgn);
  -- addrInit "a" aOff and addrInit "b" bOff are 2-Cassgn bodies (generic).
  have h_oc_cassgn : ∀ i ∈ BignumInvP25519.addrInit "oc" 0,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_true, List.mem_singleton] at hi
    subst hi
    refine ⟨_, _, _, _, rfl⟩
  have h_a_cassgn : ∀ i ∈ BignumInvP25519.addrInit "a" aOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_aOff_ne_zero,
      if_neg h_aOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  have h_b_cassgn : ∀ i ∈ BignumInvP25519.addrInit "b" bOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_bOff_ne_zero,
      if_neg h_bOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  have step_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "b" bOff ++ [call_instr]) s_a = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_b_cassgn s_a s_b s_final h_b_run
    exact h_call_run
  have step_a_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "a" aOff ++
         (BignumInvP25519.addrInit "b" bOff ++ [call_instr])) s_oc = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_a_cassgn s_oc s_a s_final h_a_run
    exact step_b_call
  have step_full :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" 0 ++
         (BignumInvP25519.addrInit "a" aOff ++
          (BignumInvP25519.addrInit "b" bOff ++ [call_instr]))) s = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_oc_cassgn s s_oc s_final h_oc_run
    exact step_a_b_call
  have h_assoc : (BignumInvP25519.addrInit "oc" 0 ++
       BignumInvP25519.addrInit "a" aOff ++
       BignumInvP25519.addrInit "b" bOff ++
       [call_instr]) =
      BignumInvP25519.addrInit "oc" 0 ++
       (BignumInvP25519.addrInit "a" aOff ++
        (BignumInvP25519.addrInit "b" bOff ++ [call_instr])) := by
    simp [List.append_assoc]
  show bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" 0 ++
         BignumInvP25519.addrInit "a" aOff ++
         BignumInvP25519.addrInit "b" bOff ++
         [call_instr]) s = some s_final
  rw [h_assoc]
  exact step_full

/-- **`mul_step` with `bOff = -1`.**  Specialised variant where the
    `b` argument is the `ap` register itself (e.g. block 3's
    `z9 := z2² · ap`).  The `b` register is initialised via
    `addrInit_negOne_succ` (single Cassgn `b := ap`) rather than the
    two-Cassgn generic case.

    `dstOff` and `aOff` remain generic.  The "b value" is `ap_val`
    (the 4-limb value at `ap_addr`). -/
theorem chain_mul_step_correct_b_negOne
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (a_addr : UInt64)
    (a_val ap_val : Nat)
    (h_a_mem : memNat4 a_addr s.mem = some a_val)
    (h_ap_mem : memNat4 ap_addr s.mem = some ap_val)
    (dst_addr : UInt64)
    (h_dst_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b)
    (idx : Nat) (dstOff aOff : Int)
    (h_dstOff_ne_zero : dstOff ≠ 0) (h_dstOff_ne_negOne : dstOff ≠ -1)
    (h_aOff_ne_zero : aOff ≠ 0) (h_aOff_ne_negOne : aOff ≠ -1)
    (h_dst_addr_eq :
      BitVec.ofNat 64 dst_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 dstOff)
    (h_a_addr_eq :
      BitVec.ofNat 64 a_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 aOff)
    (mul_body : List InstrR)
    (h_shape : mul_body = BignumInvP25519.mul_step idx dstOff aOff (-1)) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) mul_body s = some s' ∧
      memNat4 dst_addr s'.mem = some ((a_val * ap_val) % p_25519) ∧
      (∀ addr : UInt64,
        ¬ MemoryModel.range dst_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) := by
  subst h_shape
  obtain ⟨s_oc, h_oc_run, h_oc_reg, h_oc_mem, h_oc_other⟩ :=
    addrInit_generic_succ registry fuel s "oc" dstOff
      h_dstOff_ne_zero h_dstOff_ne_negOne
  obtain ⟨s_a, h_a_run, h_a_reg, h_a_mem_eq, h_a_other⟩ :=
    addrInit_generic_succ registry fuel s_oc "a" aOff
      h_aOff_ne_zero h_aOff_ne_negOne
  -- Step 3: addrInit "b" (-1) via negOne variant — b := ap.
  obtain ⟨s_b, h_b_run, h_b_reg, h_b_mem_eq, h_b_other⟩ :=
    addrInit_negOne_succ registry fuel s_a "b"
  have h_oc_at_b : s_b.regs "oc" = BitVec.ofNat 64 dst_addr.toNat := by
    rw [h_b_other "oc" (by decide), h_a_other "oc" (by decide), h_oc_reg, h_op]
    exact h_dst_addr_eq.symm
  have h_a_at_b : s_b.regs "a" = BitVec.ofNat 64 a_addr.toNat := by
    rw [h_b_other "a" (by decide), h_a_reg, h_oc_other "op" (by decide), h_op]
    exact h_a_addr_eq.symm
  -- b register now holds s_a.regs "ap" = ... = s.regs "ap" = ap_addr.
  have h_b_at_b : s_b.regs "b" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [h_b_reg, h_a_other "ap" (by decide), h_oc_other "ap" (by decide), h_ap]
  have h_mem_at_b : s_b.mem = s.mem := by
    rw [h_b_mem_eq, h_a_mem_eq, h_oc_mem]
  have h_a_mem_at_b : memNat4 a_addr s_b.mem = some a_val := by
    rw [h_mem_at_b]; exact h_a_mem
  have h_ap_mem_at_b : memNat4 ap_addr s_b.mem = some ap_val := by
    rw [h_mem_at_b]; exact h_ap_mem
  have h_dst_alloc_at_b : ∀ k : Fin 32,
      ∃ b, s_b.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b := by
    intro k; rw [h_mem_at_b]; exact h_dst_alloc k
  let call_instr : InstrR :=
    .Ccall .DoNotInline []
      { name := "bignum_montmul_p25519" }
      [.Pvar { gv := { var := { vname := "oc", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "a", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "b", vtype := .sword .U64 },
                       info := {} }, gs := false }]
  have h_call_shape : ∃ (ii : InlineInfo) (op_v a_v b_v : GVar),
      call_instr = .Ccall ii [] ⟨"bignum_montmul_p25519"⟩
        [.Pvar op_v, .Pvar a_v, .Pvar b_v]
      ∧ op_v.gv.var.vname = "oc"
      ∧ a_v.gv.var.vname = "a"
      ∧ b_v.gv.var.vname = "b" :=
    ⟨.DoNotInline, _, _, _, rfl, rfl, rfl, rfl⟩
  obtain ⟨s_final, h_call_run, h_call_post, h_call_frame, _h_call_alloc⟩ :=
    hAx.call_correct s_b fuel
      "oc" "a" "b" dst_addr a_addr ap_addr a_val ap_val
      h_oc_at_b h_a_at_b h_b_at_b h_a_mem_at_b h_ap_mem_at_b
      h_dst_alloc_at_b call_instr h_call_shape
  have h_frame : ∀ addr : UInt64,
      ¬ MemoryModel.range dst_addr 32 addr →
      s_final.mem.loadByte addr = s.mem.loadByte addr := by
    intro addr h_addr
    have h_mont := h_call_frame addr h_addr
    rw [h_mont, h_mem_at_b]
  refine ⟨s_final, ?_, h_call_post, h_frame⟩
  have h_oc_cassgn : ∀ i ∈ BignumInvP25519.addrInit "oc" dstOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_dstOff_ne_zero,
      if_neg h_dstOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  have h_a_cassgn : ∀ i ∈ BignumInvP25519.addrInit "a" aOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_aOff_ne_zero,
      if_neg h_aOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  have h_b_cassgn : ∀ i ∈ BignumInvP25519.addrInit "b" (-1),
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, show ((-1 : Int) = 0) = False from
      by decide, if_false, if_true, List.mem_singleton] at hi
    subst hi
    refine ⟨_, _, _, _, rfl⟩
  have step_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "b" (-1) ++ [call_instr]) s_a = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_b_cassgn s_a s_b s_final h_b_run
    exact h_call_run
  have step_a_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "a" aOff ++
         (BignumInvP25519.addrInit "b" (-1) ++ [call_instr])) s_oc = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_a_cassgn s_oc s_a s_final h_a_run
    exact step_b_call
  have step_full :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" dstOff ++
         (BignumInvP25519.addrInit "a" aOff ++
          (BignumInvP25519.addrInit "b" (-1) ++ [call_instr]))) s = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_oc_cassgn s s_oc s_final h_oc_run
    exact step_a_b_call
  have h_assoc : (BignumInvP25519.addrInit "oc" dstOff ++
       BignumInvP25519.addrInit "a" aOff ++
       BignumInvP25519.addrInit "b" (-1) ++
       [call_instr]) =
      BignumInvP25519.addrInit "oc" dstOff ++
       (BignumInvP25519.addrInit "a" aOff ++
        (BignumInvP25519.addrInit "b" (-1) ++ [call_instr])) := by
    simp [List.append_assoc]
  show bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" dstOff ++
         BignumInvP25519.addrInit "a" aOff ++
         BignumInvP25519.addrInit "b" (-1) ++
         [call_instr]) s = some s_final
  rw [h_assoc]
  exact step_full

/-- **`mul_step` with `dstOff = 0` AND `bOff = -1`.**  Combined
    specialised variant for the p58 chain's terminal
    `op := z2_250_0^4 · ap` (block 13b of `BignumPowP58P25519.body`).
    Both `oc := op` and `b := ap` use the single-Cassgn addrInit
    variants. -/
theorem chain_mul_step_correct_dst_zero_b_negOne
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (a_addr : UInt64)
    (a_val ap_val : Nat)
    (h_a_mem : memNat4 a_addr s.mem = some a_val)
    (h_ap_mem : memNat4 ap_addr s.mem = some ap_val)
    (h_op_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)
    (idx : Nat) (aOff : Int)
    (h_aOff_ne_zero : aOff ≠ 0) (h_aOff_ne_negOne : aOff ≠ -1)
    (h_a_addr_eq :
      BitVec.ofNat 64 a_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 aOff)
    (mul_body : List InstrR)
    (h_shape : mul_body = BignumInvP25519.mul_step idx 0 aOff (-1)) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) mul_body s = some s' ∧
      memNat4 op_addr s'.mem = some ((a_val * ap_val) % p_25519) ∧
      (∀ addr : UInt64,
        ¬ MemoryModel.range op_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) := by
  subst h_shape
  obtain ⟨s_oc, h_oc_run, h_oc_reg, h_oc_mem, h_oc_other⟩ :=
    addrInit_zero_succ registry fuel s "oc"
  obtain ⟨s_a, h_a_run, h_a_reg, h_a_mem_eq, h_a_other⟩ :=
    addrInit_generic_succ registry fuel s_oc "a" aOff
      h_aOff_ne_zero h_aOff_ne_negOne
  obtain ⟨s_b, h_b_run, h_b_reg, h_b_mem_eq, h_b_other⟩ :=
    addrInit_negOne_succ registry fuel s_a "b"
  have h_oc_at_b : s_b.regs "oc" = BitVec.ofNat 64 op_addr.toNat := by
    rw [h_b_other "oc" (by decide), h_a_other "oc" (by decide), h_oc_reg, h_op]
  have h_a_at_b : s_b.regs "a" = BitVec.ofNat 64 a_addr.toNat := by
    rw [h_b_other "a" (by decide), h_a_reg, h_oc_other "op" (by decide), h_op]
    exact h_a_addr_eq.symm
  have h_b_at_b : s_b.regs "b" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [h_b_reg, h_a_other "ap" (by decide), h_oc_other "ap" (by decide), h_ap]
  have h_mem_at_b : s_b.mem = s.mem := by
    rw [h_b_mem_eq, h_a_mem_eq, h_oc_mem]
  have h_a_mem_at_b : memNat4 a_addr s_b.mem = some a_val := by
    rw [h_mem_at_b]; exact h_a_mem
  have h_ap_mem_at_b : memNat4 ap_addr s_b.mem = some ap_val := by
    rw [h_mem_at_b]; exact h_ap_mem
  have h_op_alloc_at_b : ∀ k : Fin 32,
      ∃ b, s_b.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b := by
    intro k; rw [h_mem_at_b]; exact h_op_alloc k
  let call_instr : InstrR :=
    .Ccall .DoNotInline []
      { name := "bignum_montmul_p25519" }
      [.Pvar { gv := { var := { vname := "oc", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "a", vtype := .sword .U64 },
                       info := {} }, gs := false },
       .Pvar { gv := { var := { vname := "b", vtype := .sword .U64 },
                       info := {} }, gs := false }]
  have h_call_shape : ∃ (ii : InlineInfo) (op_v a_v b_v : GVar),
      call_instr = .Ccall ii [] ⟨"bignum_montmul_p25519"⟩
        [.Pvar op_v, .Pvar a_v, .Pvar b_v]
      ∧ op_v.gv.var.vname = "oc"
      ∧ a_v.gv.var.vname = "a"
      ∧ b_v.gv.var.vname = "b" :=
    ⟨.DoNotInline, _, _, _, rfl, rfl, rfl, rfl⟩
  obtain ⟨s_final, h_call_run, h_call_post, h_call_frame, _h_call_alloc⟩ :=
    hAx.call_correct s_b fuel
      "oc" "a" "b" op_addr a_addr ap_addr a_val ap_val
      h_oc_at_b h_a_at_b h_b_at_b h_a_mem_at_b h_ap_mem_at_b
      h_op_alloc_at_b call_instr h_call_shape
  have h_frame : ∀ addr : UInt64,
      ¬ MemoryModel.range op_addr 32 addr →
      s_final.mem.loadByte addr = s.mem.loadByte addr := by
    intro addr h_addr
    have h_mont := h_call_frame addr h_addr
    rw [h_mont, h_mem_at_b]
  refine ⟨s_final, ?_, h_call_post, h_frame⟩
  have h_oc_cassgn : ∀ i ∈ BignumInvP25519.addrInit "oc" 0,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_true, List.mem_singleton] at hi
    subst hi
    refine ⟨_, _, _, _, rfl⟩
  have h_a_cassgn : ∀ i ∈ BignumInvP25519.addrInit "a" aOff,
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, if_neg h_aOff_ne_zero,
      if_neg h_aOff_ne_negOne, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine ⟨_, _, _, _, rfl⟩
    · refine ⟨_, _, _, _, rfl⟩
  have h_b_cassgn : ∀ i ∈ BignumInvP25519.addrInit "b" (-1),
      ∃ lv tag ty rhs, i = .Cassgn lv tag ty rhs := by
    intro i hi
    simp only [BignumInvP25519.addrInit, show ((-1 : Int) = 0) = False from
      by decide, if_false, if_true, List.mem_singleton] at hi
    subst hi
    refine ⟨_, _, _, _, rfl⟩
  have step_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "b" (-1) ++ [call_instr]) s_a = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_b_cassgn s_a s_b s_final h_b_run
    exact h_call_run
  have step_a_b_call :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "a" aOff ++
         (BignumInvP25519.addrInit "b" (-1) ++ [call_instr])) s_oc = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_a_cassgn s_oc s_a s_final h_a_run
    exact step_b_call
  have step_full :
      bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" 0 ++
         (BignumInvP25519.addrInit "a" aOff ++
          (BignumInvP25519.addrInit "b" (-1) ++ [call_instr]))) s = some s_final := by
    apply bignumExecFuel_append_cassgn registry fuel _ _ h_oc_cassgn s s_oc s_final h_oc_run
    exact step_a_b_call
  have h_assoc : (BignumInvP25519.addrInit "oc" 0 ++
       BignumInvP25519.addrInit "a" aOff ++
       BignumInvP25519.addrInit "b" (-1) ++
       [call_instr]) =
      BignumInvP25519.addrInit "oc" 0 ++
       (BignumInvP25519.addrInit "a" aOff ++
        (BignumInvP25519.addrInit "b" (-1) ++ [call_instr])) := by
    simp [List.append_assoc]
  show bignumExecFuel registry (fuel + 1)
        (BignumInvP25519.addrInit "oc" 0 ++
         BignumInvP25519.addrInit "a" aOff ++
         BignumInvP25519.addrInit "b" (-1) ++
         [call_instr]) s = some s_final
  rw [h_assoc]
  exact step_full

/-! ## §1c  Equation lemmas for `sqr_chain_loop` and `repeated_sqr_then_mul`

The structural-recursive `BignumInvP25519.sqr_chain_loop` (commit
`259e8940`) admits two unfolding equations.  They are both `rfl` —
the value is by structural recursion on the first arg — but stating
them as named lemmas lets downstream proofs use `rw` rather than
`show` for clarity. -/

/-- Empty-loop case: `sqr_chain_loop 0` is the identity on the accumulator. -/
@[simp] theorem sqr_chain_loop_zero
    (curOff otherOff : Int) (idx : Nat) (acc : List InstrR) :
    BignumInvP25519.sqr_chain_loop 0 curOff otherOff idx acc =
      (acc, curOff, idx) := rfl

/-- Successor-loop case: peel one squaring iteration off the front,
    swap cur/other for the ping-pong, and recurse on the smaller `i`.
    The accumulator absorbs one `sqr_step idx otherOff curOff` block. -/
theorem sqr_chain_loop_succ
    (i : Nat) (curOff otherOff : Int) (idx : Nat) (acc : List InstrR) :
    BignumInvP25519.sqr_chain_loop (i + 1) curOff otherOff idx acc =
      BignumInvP25519.sqr_chain_loop i otherOff curOff (idx + 1)
        (acc ++ BignumInvP25519.sqr_step idx otherOff curOff) := rfl

/-- Repeated-squaring chain expanded:
    `repeated_sqr_then_mul startIdx dstOff srcOff otherOff n` =
    `step0 ++ <loop body> ++ mulInstrs` where
    - `step0` is the initial squaring `src → t`,
    - `<loop body>` is the `(n-1)`-fold ping-pong producing `src^(2^n)`
      at `finalOff` ∈ {OFF_t, OFF_u}`,
    - `mulInstrs` is the final multiply `dst := finalBuf · other`. -/
theorem repeated_sqr_then_mul_unfold
    (startIdx : Nat) (dstOff srcOff otherOff : Int) (n : Nat) :
    (BignumInvP25519.repeated_sqr_then_mul startIdx dstOff srcOff otherOff n).fst =
      let step0 := BignumInvP25519.sqr_step startIdx BignumInvP25519.OFF_t srcOff
      let result := BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) step0
      let finalOff := result.2.1
      let idxAfterSqr := result.2.2
      result.1 ++ BignumInvP25519.mul_step idxAfterSqr dstOff finalOff otherOff := rfl

/-! ## §1c.1  Accumulator-invariance lemmas for `sqr_chain_loop`

The loop's instruction-list output, final-offset, and next-idx are all
*compositional* in the accumulator: starting with a non-empty `acc` is
the same as starting with `[]` and prepending `acc` to the result.
This lets us decompose the loop body into a fixed prefix + the
empty-accumulator recursive tail, which is the shape `sqr_chain_loop_effect`'s
inductive step needs to apply chain_sqr_step_correct + IH. -/

theorem sqr_chain_loop_acc_split
    (i : Nat) (curOff otherOff : Int) (idx : Nat) (acc : List InstrR) :
    (BignumInvP25519.sqr_chain_loop i curOff otherOff idx acc).fst =
      acc ++ (BignumInvP25519.sqr_chain_loop i curOff otherOff idx []).fst := by
  induction i generalizing curOff otherOff idx acc with
  | zero => simp [BignumInvP25519.sqr_chain_loop]
  | succ j ih =>
    rw [sqr_chain_loop_succ, sqr_chain_loop_succ]
    rw [ih otherOff curOff (idx + 1)
          (acc ++ BignumInvP25519.sqr_step idx otherOff curOff)]
    rw [ih otherOff curOff (idx + 1)
          ([] ++ BignumInvP25519.sqr_step idx otherOff curOff)]
    simp [List.append_assoc]

theorem sqr_chain_loop_acc_final_off
    (i : Nat) (curOff otherOff : Int) (idx : Nat) (acc : List InstrR) :
    (BignumInvP25519.sqr_chain_loop i curOff otherOff idx acc).snd.fst =
      (BignumInvP25519.sqr_chain_loop i curOff otherOff idx []).snd.fst := by
  induction i generalizing curOff otherOff idx acc with
  | zero => simp [BignumInvP25519.sqr_chain_loop]
  | succ j ih =>
    rw [sqr_chain_loop_succ, sqr_chain_loop_succ]
    rw [ih otherOff curOff (idx + 1) (acc ++ _),
        ih otherOff curOff (idx + 1) ([] ++ _)]

theorem sqr_chain_loop_acc_final_idx
    (i : Nat) (curOff otherOff : Int) (idx : Nat) (acc : List InstrR) :
    (BignumInvP25519.sqr_chain_loop i curOff otherOff idx acc).snd.snd =
      (BignumInvP25519.sqr_chain_loop i curOff otherOff idx []).snd.snd := by
  induction i generalizing curOff otherOff idx acc with
  | zero => simp [BignumInvP25519.sqr_chain_loop]
  | succ j ih =>
    rw [sqr_chain_loop_succ, sqr_chain_loop_succ]
    rw [ih otherOff curOff (idx + 1) (acc ++ _),
        ih otherOff curOff (idx + 1) ([] ++ _)]

/-! ## §1c.2  Register preservation for `addrInit` and `sqr_step`

These lemmas factor out the per-instruction `preservesRegRec` discharge
so it can be reused at every iteration of the
`sqr_chain_loop_effect` induction.  `addrInit lvalName offset`
unfolds via two `if`s, but every branch only writes to `lvalName`. -/

theorem addrInit_preservesRegRec_of_ne
    (lvalName : String) (offset : Int) (r : String) (h : r ≠ lvalName) :
    ∀ i ∈ BignumInvP25519.addrInit lvalName offset, i.preservesRegRec r := by
  intro i hi
  simp only [BignumInvP25519.addrInit] at hi
  by_cases h0 : offset = 0
  · simp [h0, List.mem_singleton] at hi
    subst hi
    simp [InstrR.preservesRegRec, InstrR.regWritesRec,
      BignumInvP25519.lvR, CatCrypt.Crypto.Jasmin.S2NBignumSSA.v]
    exact h
  · simp only [h0, if_false] at hi
    by_cases h1 : offset = -1
    · simp [h1, List.mem_singleton] at hi
      subst hi
      simp [InstrR.preservesRegRec, InstrR.regWritesRec,
        BignumInvP25519.lvR, CatCrypt.Crypto.Jasmin.S2NBignumSSA.v]
      exact h
    · simp only [h1, if_false, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simp [InstrR.preservesRegRec, InstrR.regWritesRec,
          BignumInvP25519.lvR, CatCrypt.Crypto.Jasmin.S2NBignumSSA.v]
        exact h
      · simp [InstrR.preservesRegRec, InstrR.regWritesRec,
          BignumInvP25519.lvR, CatCrypt.Crypto.Jasmin.S2NBignumSSA.v]
        exact h

theorem sqr_step_preservesRegRec_of_ne
    (idx : Nat) (dstOff srcOff : Int) (r : String)
    (h_oc : r ≠ "oc") (h_a : r ≠ "a") (h_b : r ≠ "b") :
    ∀ i ∈ BignumInvP25519.sqr_step idx dstOff srcOff, i.preservesRegRec r := by
  intro i hi
  simp only [BignumInvP25519.sqr_step, List.append_assoc, List.mem_append,
    List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | rfl
  · exact addrInit_preservesRegRec_of_ne "oc" dstOff r h_oc i hi
  · exact addrInit_preservesRegRec_of_ne "a" srcOff r h_a i hi
  · exact addrInit_preservesRegRec_of_ne "b" srcOff r h_b i hi
  · simp [InstrR.preservesRegRec, InstrR.regWritesRec]

theorem addrInit_isNonControl (lvalName : String) (offset : Int) :
    ∀ i ∈ BignumInvP25519.addrInit lvalName offset, i.isNonControl := by
  intro i hi
  simp only [BignumInvP25519.addrInit] at hi
  by_cases h0 : offset = 0
  · simp [h0, List.mem_singleton] at hi
    subst hi; trivial
  · simp only [h0, if_false] at hi
    by_cases h1 : offset = -1
    · simp [h1, List.mem_singleton] at hi
      subst hi; trivial
    · simp only [h1, if_false, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> trivial

theorem sqr_step_isNonControl (idx : Nat) (dstOff srcOff : Int) :
    ∀ i ∈ BignumInvP25519.sqr_step idx dstOff srcOff, i.isNonControl := by
  intro i hi
  simp only [BignumInvP25519.sqr_step, List.append_assoc, List.mem_append,
    List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | rfl
  · exact addrInit_isNonControl "oc" dstOff i hi
  · exact addrInit_isNonControl "a" srcOff i hi
  · exact addrInit_isNonControl "b" srcOff i hi
  · trivial

theorem mul_step_isNonControl (idx : Nat) (dstOff aOff bOff : Int) :
    ∀ i ∈ BignumInvP25519.mul_step idx dstOff aOff bOff, i.isNonControl := by
  intro i hi
  simp only [BignumInvP25519.mul_step, List.append_assoc, List.mem_append,
    List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | rfl
  · exact addrInit_isNonControl "oc" dstOff i hi
  · exact addrInit_isNonControl "a" aOff i hi
  · exact addrInit_isNonControl "b" bOff i hi
  · trivial

theorem mul_step_preservesRegRec_of_ne
    (idx : Nat) (dstOff aOff bOff : Int) (r : String)
    (h_oc : r ≠ "oc") (h_a : r ≠ "a") (h_b : r ≠ "b") :
    ∀ i ∈ BignumInvP25519.mul_step idx dstOff aOff bOff, i.preservesRegRec r := by
  intro i hi
  simp only [BignumInvP25519.mul_step, List.append_assoc, List.mem_append,
    List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | rfl
  · exact addrInit_preservesRegRec_of_ne "oc" dstOff r h_oc i hi
  · exact addrInit_preservesRegRec_of_ne "a" aOff r h_a i hi
  · exact addrInit_preservesRegRec_of_ne "b" bOff r h_b i hi
  · simp [InstrR.preservesRegRec, InstrR.regWritesRec]

/-- Every instruction in `sqr_chain_loop i ...` body satisfies `isNonControl`.
    Proven by induction on `i`, using `sqr_step_isNonControl` at each step. -/
theorem sqr_chain_loop_isNonControl
    (i : Nat) (curOff otherOff : Int) (idx : Nat) :
    ∀ instr ∈ (BignumInvP25519.sqr_chain_loop i curOff otherOff idx []).fst,
      instr.isNonControl := by
  induction i generalizing curOff otherOff idx with
  | zero => simp [BignumInvP25519.sqr_chain_loop]
  | succ j ih =>
    intro instr h_mem
    rw [sqr_chain_loop_succ, sqr_chain_loop_acc_split] at h_mem
    simp only [List.nil_append, List.mem_append] at h_mem
    rcases h_mem with h_pre | h_tail
    · exact sqr_step_isNonControl idx otherOff curOff instr h_pre
    · exact ih otherOff curOff (idx + 1) instr h_tail

/-- Every instruction in `sqr_chain_loop i ...` body preserves any
    register `r ∉ {oc, a, b}`. -/
theorem sqr_chain_loop_preservesRegRec_of_ne
    (i : Nat) (curOff otherOff : Int) (idx : Nat) (r : String)
    (h_oc : r ≠ "oc") (h_a : r ≠ "a") (h_b : r ≠ "b") :
    ∀ instr ∈ (BignumInvP25519.sqr_chain_loop i curOff otherOff idx []).fst,
      instr.preservesRegRec r := by
  induction i generalizing curOff otherOff idx with
  | zero => simp [BignumInvP25519.sqr_chain_loop]
  | succ j ih =>
    intro instr h_mem
    rw [sqr_chain_loop_succ, sqr_chain_loop_acc_split] at h_mem
    simp only [List.nil_append, List.mem_append] at h_mem
    rcases h_mem with h_pre | h_tail
    · exact sqr_step_preservesRegRec_of_ne idx otherOff curOff r h_oc h_a h_b instr h_pre
    · exact ih otherOff curOff (idx + 1) instr h_tail

/-- Parity of `sqr_chain_loop`'s final offset: after `i` iterations
    starting from `(curOff, otherOff)`, the cur ↔ other swap-counter
    determines whether `finalOff = curOff` (even `i`) or `otherOff`
    (odd `i`). -/
theorem sqr_chain_loop_final_off
    (i : Nat) (curOff otherOff : Int) (idx : Nat) :
    (BignumInvP25519.sqr_chain_loop i curOff otherOff idx []).snd.fst =
      (if i % 2 = 0 then curOff else otherOff) := by
  induction i generalizing curOff otherOff idx with
  | zero => simp [BignumInvP25519.sqr_chain_loop]
  | succ j ih =>
    rw [sqr_chain_loop_succ]
    rw [sqr_chain_loop_acc_final_off j otherOff curOff (idx + 1) _]
    rw [ih otherOff curOff (idx + 1)]
    by_cases h : j % 2 = 0
    · simp [h, Nat.succ_mod_two_eq_one_iff.mpr h]
    · have : j % 2 = 1 := Nat.mod_two_ne_zero.mp h
      simp [h, this, Nat.succ_mod_two_eq_zero_iff.mpr this]

/-! ## §1d  Algebraic helper for the loop counter

The `sqr_chain_loop_effect` discharge requires the algebraic identity
`a^(2^(j+1)) = (a^2)^(2^j)`.  This is `pow_mul`, but stating it
specialised for our specific shape avoids a case-split on `Nat.pow`'s
unfolding inside the main proof. -/

theorem pow_two_succ (a : Nat) (j : Nat) :
    a ^ (2 ^ (j + 1)) = (a ^ 2) ^ (2 ^ j) := by
  rw [show (2 : Nat) ^ (j + 1) = 2 * 2 ^ j from by ring, pow_mul]

/-! ## §1e  Side lemma: `sqr_chain_loop_effect`

Running `BignumInvP25519.sqr_chain_loop i curOff otherOff idx []` from
a state where `cur_addr` (corresponding to `curOff`) holds `cur_val`
produces a state where the loop's final-off buffer holds
`cur_val^(2^i) mod p_25519`.

**Status (2026-05-10):** fully proven.  Base case via `pow_one`;
inductive step composes `chain_sqr_step_correct_generic` (one sqr
iteration) with the IH (remaining j iterations) via
`bignumExecFuel_append_join`, with the algebraic bridge from
`(cur_val²%p)^(2^j) % p` to `cur_val^(2^(j+1)) % p` via `pow_two_succ`
+ `Nat.pow_mod`. -/

theorem sqr_chain_loop_effect
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (i : Nat)
    (curOff otherOff : Int)
    (h_curOff_ne_zero : curOff ≠ 0) (h_curOff_ne_negOne : curOff ≠ -1)
    (h_otherOff_ne_zero : otherOff ≠ 0) (h_otherOff_ne_negOne : otherOff ≠ -1)
    (cur_addr other_addr : UInt64)
    (h_cur_addr_eq : BitVec.ofNat 64 cur_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 curOff)
    (h_other_addr_eq : BitVec.ofNat 64 other_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 otherOff)
    (cur_val : Nat) (h_cur_lt : cur_val < p_25519)
    (h_cur_mem : memNat4 cur_addr s.mem = some cur_val)
    (h_cur_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (cur_addr + UInt64.ofNat k.val) = some b)
    (h_other_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (other_addr + UInt64.ofNat k.val) = some b)
    (h_no_alias : ∀ k1 k2 : Fin 32,
       cur_addr + UInt64.ofNat k1.val ≠ other_addr + UInt64.ofNat k2.val)
    (idx : Nat) :
    let R := BignumInvP25519.sqr_chain_loop i curOff otherOff idx []
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) R.fst s = some s' ∧
      ∃ final_addr : UInt64,
        BitVec.ofNat 64 final_addr.toNat =
          BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 R.snd.fst ∧
        memNat4 final_addr s'.mem = some ((cur_val ^ (2 ^ i)) % p_25519) ∧
      -- Frame: bytes outside the two 32-byte scratch windows
      -- (cur_addr, other_addr) are unchanged.
      (∀ addr : UInt64,
         ¬ MemoryModel.range cur_addr 32 addr →
         ¬ MemoryModel.range other_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) := by
  induction i generalizing s curOff otherOff cur_addr other_addr cur_val idx
    h_curOff_ne_zero h_curOff_ne_negOne h_otherOff_ne_zero h_otherOff_ne_negOne
    h_cur_alloc h_other_alloc with
  | zero =>
    -- Base case: sqr_chain_loop 0 curOff otherOff idx [] = ([], curOff, idx).
    -- bignumExecFuel on [] preserves the state; cur_val^(2^0) = cur_val^1 = cur_val,
    -- and `cur_val % p_25519 = cur_val` by h_cur_lt.
    refine ⟨s, ?_, cur_addr, h_cur_addr_eq, ?_, ?_⟩
    · -- bignumExecFuel registry (fuel+1) [] s = some s
      simp [BignumInvP25519.sqr_chain_loop, bignumExecFuel]
    · -- memNat4 cur_addr s.mem = some (cur_val ^ 1 % p_25519)
      simp only [BignumInvP25519.sqr_chain_loop, pow_one, pow_zero]
      rw [h_cur_mem]
      congr 1
      exact (Nat.mod_eq_of_lt h_cur_lt).symm
    · -- Frame: 0 iterations leaves memory untouched.
      intro addr _ _; rfl
  | succ j ih =>
    -- Stage 1: unfold `R = sqr_chain_loop (j+1) curOff otherOff idx []` via
    -- `sqr_chain_loop_succ` + `sqr_chain_loop_acc_split` to expose the
    -- prefix `sqr_step idx otherOff curOff` and the empty-acc tail.
    simp only [sqr_chain_loop_succ, List.nil_append]
    rw [show (BignumInvP25519.sqr_chain_loop j otherOff curOff (idx + 1)
             (BignumInvP25519.sqr_step idx otherOff curOff)).fst =
            BignumInvP25519.sqr_step idx otherOff curOff ++
            (BignumInvP25519.sqr_chain_loop j otherOff curOff (idx + 1) []).fst
            from sqr_chain_loop_acc_split j otherOff curOff (idx + 1) _,
        sqr_chain_loop_acc_final_off j otherOff curOff (idx + 1) _]
    -- Stage 2: apply chain_sqr_step_correct_generic for the prefix
    -- `sqr_step idx otherOff curOff`. dst = other_addr, src = cur_addr.
    obtain ⟨s_mid, h_exec_pre, h_other_mem_post, h_frame_pre⟩ :=
      chain_sqr_step_correct_generic registry hAx s fuel
        op_addr ap_addr h_op h_ap
        cur_addr cur_val h_cur_mem
        other_addr h_other_alloc
        idx otherOff curOff
        h_otherOff_ne_zero h_otherOff_ne_negOne
        h_curOff_ne_zero h_curOff_ne_negOne
        h_other_addr_eq h_cur_addr_eq
        (BignumInvP25519.sqr_step idx otherOff curOff) rfl
    -- Stage 3a: s_mid preserves "op" and "ap" registers (sqr_step writes
    -- only to oc/a/b plus the Ccall, which has empty regWritesRec).
    have h_op_mid : s_mid.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
      rw [← h_op]
      exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
        registry _ _ "op"
        (sqr_step_preservesRegRec_of_ne idx otherOff curOff "op"
          (by decide) (by decide) (by decide))
        s s_mid h_exec_pre
    have h_ap_mid : s_mid.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
      rw [← h_ap]
      exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
        registry _ _ "ap"
        (sqr_step_preservesRegRec_of_ne idx otherOff curOff "ap"
          (by decide) (by decide) (by decide))
        s s_mid h_exec_pre
    -- Stage 3b: each byte at cur_addr in s_mid loads to the same value
    -- as in s.  By h_no_alias, every cur_addr + k (k ∈ Fin 32) is outside
    -- range other_addr 32; the frame condition then preserves loadByte.
    have h_byte_frame : ∀ k : Fin 32,
        s_mid.mem.loadByte (cur_addr + UInt64.ofNat k.val) =
          s.mem.loadByte (cur_addr + UInt64.ofNat k.val) := by
      intro k
      apply h_frame_pre
      rintro ⟨k', hk'_lt, h_eq⟩
      exact h_no_alias k ⟨k', hk'_lt⟩ h_eq
    -- Stage 3c: byte-allocation at cur_addr in s_mid.  Lift h_cur_alloc
    -- (s.mem) to s_mid.mem via h_byte_frame.
    have h_cur_alloc_mid : ∀ k : Fin 32,
        ∃ b, s_mid.mem.loadByte (cur_addr + UInt64.ofNat k.val) = some b := by
      intro k
      rw [h_byte_frame k]
      exact h_cur_alloc k
    -- Stage 3c': byte-allocation at other_addr in s_mid.  Derived from
    -- h_other_mem_post (memNat4 ⇒ all 32 bytes loadable).
    have h_other_alloc_mid : ∀ k : Fin 32,
        ∃ b, s_mid.mem.loadByte (other_addr + UInt64.ofNat k.val) = some b := by
      intro k
      exact memNat4_imp_byte_alloc other_addr s_mid.mem _ h_other_mem_post k.val k.isLt
    -- Stage 3b': memNat4 cur_addr s_mid.mem = some cur_val.  Reduce to
    -- a byte-by-byte equality via `memNat4_eq_of_byte_eq`.
    have h_cur_mem_mid : memNat4 cur_addr s_mid.mem = some cur_val := by
      have h_eq : memNat4 cur_addr s_mid.mem = memNat4 cur_addr s.mem := by
        apply memNat4_eq_of_byte_eq
        intro k hk
        exact h_byte_frame ⟨k, hk⟩
      rw [h_eq]; exact h_cur_mem
    -- Stage 3d: the swapped no-alias.
    have h_no_alias_swap : ∀ k1 k2 : Fin 32,
        other_addr + UInt64.ofNat k1.val ≠ cur_addr + UInt64.ofNat k2.val :=
      fun k1 k2 h => h_no_alias k2 k1 h.symm
    -- Stage 3e: the new cur_val is bounded.
    have h_squared_lt : cur_val * cur_val % p_25519 < p_25519 :=
      Nat.mod_lt _ (by unfold p_25519; decide)
    -- Stage 4a: apply the IH at s_mid with cur ↔ other swapped.
    -- New "h_cur_alloc" = old h_other_alloc_mid (alloc at other_addr in s_mid).
    -- New "h_other_alloc" = old h_cur_alloc_mid (alloc at cur_addr in s_mid).
    obtain ⟨s', h_exec_tail, final_addr, h_final_addr_eq, h_final_mem, h_frame_tail⟩ :=
      ih s_mid h_op_mid h_ap_mid otherOff curOff
        h_otherOff_ne_zero h_otherOff_ne_negOne
        h_curOff_ne_zero h_curOff_ne_negOne
        other_addr cur_addr h_other_addr_eq h_cur_addr_eq
        (cur_val * cur_val % p_25519) h_squared_lt
        h_other_mem_post h_other_alloc_mid h_cur_alloc_mid
        h_no_alias_swap (idx + 1)
    -- Stage 4b: combine the prefix and tail executions.
    refine ⟨s', ?_, final_addr, h_final_addr_eq, ?_, ?_⟩
    · exact CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1)
        (BignumInvP25519.sqr_step idx otherOff curOff)
        ((BignumInvP25519.sqr_chain_loop j otherOff curOff (idx + 1) []).fst)
        (sqr_step_isNonControl idx otherOff curOff)
        s s_mid s' h_exec_pre h_exec_tail
    · -- Bridge: ((cur_val * cur_val) % p_25519)^(2^j) % p_25519
      --       = cur_val^(2^(j+1)) % p_25519
      rw [h_final_mem]
      congr 1
      rw [pow_two_succ, sq, ← Nat.pow_mod]
    · -- Frame: compose h_frame_pre (s → s_mid, outside other_addr 32) with
      -- h_frame_tail (s_mid → s', outside other_addr ∪ cur_addr 32).
      intro addr h_not_cur h_not_other
      rw [h_frame_tail addr h_not_other h_not_cur]
      exact h_frame_pre addr h_not_other

/-! ## §2  Repeated-squaring then multiply — proven theorems

`repeated_sqr_then_mul` is the central step of the 12-block chain
prefix: it computes `dst := src^(2^n) · other`.  Its correctness
contract is discharged via three proven theorems, one per offset
shape encountered in `BignumInvP25519.body`:

* §2.5 `chain_repeated_sqr_then_mul_correct_generic` — the typical
  case where `dstOff`, `srcOff`, `otherOff` are all `≠ {0, -1}`
  (used by blocks 5–12).
* §2.5b `chain_repeated_sqr_then_mul_correct_dst_zero` — used by
  block 13's terminal `op := z2_250_0^32 · z11`, where `dstOff = 0`.
* §2.5c `chain_repeated_sqr_then_mul_correct_other_negOne` — used by
  block 3's `z9 := z2² · ap`, where `otherOff = -1`.

All three share the same proof structure (decompose rsm_body via
`repeated_sqr_then_mul_unfold` + `sqr_chain_loop_acc_split`; apply
`chain_sqr_step_correct_generic` → `sqr_chain_loop_effect` →
`chain_mul_step_correct[_dst_zero/_b_negOne]`; glue via
`bignumExecFuel_append_join`).  They differ only in the
`chain_mul_step_*` variant used for the final multiply phase.
-/

/-! ## §2.5a  Generic-offsets discharge

For the *generic* case (`dstOff`, `srcOff`, `otherOff` all `≠ {0,-1}`),
the rsm is discharged from `chain_sqr_step_correct_generic`
+ `sqr_chain_loop_effect` + `chain_mul_step_correct`, with the
forward-sequencing `bignumExecFuel_append_join` gluing the three
phases.  8 of the 10 in-file rsm callers (blocks 5–12) fit this shape.

The two outliers (block 3 with `otherOff = -1`, block 13 with
`dstOff = 0`) are discharged in §2.5b and §2.5c via specialised
`chain_mul_step` variants. -/

theorem chain_repeated_sqr_then_mul_correct_generic
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (n : Nat) (h_n : n ≥ 1)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (src_addr other_addr dst_addr : UInt64)
    (src_val other_val : Nat)
    (h_src_mem : memNat4 src_addr s.mem = some src_val)
    (h_other_mem : memNat4 other_addr s.mem = some other_val)
    (h_dst_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b)
    -- Offsets + address derivations.
    (startIdx : Nat) (dstOff srcOff otherOff : Int)
    (h_dstOff_ne_zero : dstOff ≠ 0) (h_dstOff_ne_negOne : dstOff ≠ -1)
    (h_srcOff_ne_zero : srcOff ≠ 0) (h_srcOff_ne_negOne : srcOff ≠ -1)
    (h_otherOff_ne_zero : otherOff ≠ 0) (h_otherOff_ne_negOne : otherOff ≠ -1)
    (h_dst_addr_eq : BitVec.ofNat 64 dst_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 dstOff)
    (h_src_addr_eq : BitVec.ofNat 64 src_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 srcOff)
    (h_other_addr_eq : BitVec.ofNat 64 other_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 otherOff)
    -- Scratch buffer addresses + alloc.
    (t_addr u_addr : UInt64)
    (h_t_addr_eq : BitVec.ofNat 64 t_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_t)
    (h_u_addr_eq : BitVec.ofNat 64 u_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_u)
    (h_t_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b)
    (h_u_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b)
    -- Non-aliasing: dst, src, other, t, u all pairwise disjoint
    -- on their 32-byte windows.
    (h_no_alias_dst_t : ∀ k1 k2 : Fin 32,
       dst_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_dst_u : ∀ k1 k2 : Fin 32,
       dst_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_src_t : ∀ k1 k2 : Fin 32,
       src_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_src_u : ∀ k1 k2 : Fin 32,
       src_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_other_t : ∀ k1 k2 : Fin 32,
       other_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_other_u : ∀ k1 k2 : Fin 32,
       other_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_t_u : ∀ k1 k2 : Fin 32,
       t_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    -- Shape: rsm_body is the actual output of repeated_sqr_then_mul.
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx dstOff srcOff otherOff n).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 dst_addr s'.mem =
        some (((src_val ^ (2^n)) * other_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range dst_addr 32 addr →
         ¬ MemoryModel.range t_addr 32 addr →
         ¬ MemoryModel.range u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) := by
  -- Abbreviations.
  set step0 := BignumInvP25519.sqr_step startIdx BignumInvP25519.OFF_t srcOff
  set loop_body :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).fst
  set loop_finalOff :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).snd.fst
  set loop_finalIdx :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).snd.snd
  set mul_body :=
    BignumInvP25519.mul_step loop_finalIdx dstOff loop_finalOff otherOff
  -- rsm_body shape: step0 ++ loop_body ++ mul_body.
  have h_body : (BignumInvP25519.repeated_sqr_then_mul startIdx dstOff srcOff
      otherOff n).fst = step0 ++ loop_body ++ mul_body := by
    rw [repeated_sqr_then_mul_unfold]
    simp only [step0, loop_body, loop_finalOff, loop_finalIdx, mul_body]
    rw [sqr_chain_loop_acc_split (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
    rw [sqr_chain_loop_acc_final_off (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
    rw [sqr_chain_loop_acc_final_idx (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
  rw [h_shape, h_body]
  -- Stage 1: chain_sqr_step_correct_generic on step0.
  obtain ⟨s1, h_run1, h_t_mem1, h_frame1⟩ :=
    chain_sqr_step_correct_generic registry hAx s fuel
      op_addr ap_addr h_op h_ap
      src_addr src_val h_src_mem
      t_addr h_t_alloc
      startIdx BignumInvP25519.OFF_t srcOff
      (by decide) (by decide)
      h_srcOff_ne_zero h_srcOff_ne_negOne
      h_t_addr_eq h_src_addr_eq
      step0 rfl
  -- Stage 1a: register preservation for "op" and "ap" across step0.
  have h_op1 : s1.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
    rw [← h_op]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "op"
      (sqr_step_preservesRegRec_of_ne startIdx BignumInvP25519.OFF_t srcOff "op"
        (by decide) (by decide) (by decide))
      s s1 h_run1
  have h_ap1 : s1.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [← h_ap]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "ap"
      (sqr_step_preservesRegRec_of_ne startIdx BignumInvP25519.OFF_t srcOff "ap"
        (by decide) (by decide) (by decide))
      s s1 h_run1
  -- Stage 1b: alloc at t_addr in s1 (from h_t_mem1).
  have h_t_alloc1 : ∀ k : Fin 32,
      ∃ b, s1.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b := by
    intro k
    exact memNat4_imp_byte_alloc t_addr s1.mem _ h_t_mem1 k.val k.isLt
  -- Stage 1c: alloc at u_addr in s1 (lift via frame; u_addr disjoint from t_addr).
  have h_u_alloc1 : ∀ k : Fin 32,
      ∃ b, s1.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b := by
    intro k
    have h_outside : ¬ MemoryModel.range t_addr 32
        (u_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_t_u ⟨k', hk'⟩ k h_eq.symm
    rw [h_frame1 _ h_outside]
    exact h_u_alloc k
  have h_squared_lt : src_val * src_val % p_25519 < p_25519 :=
    Nat.mod_lt _ (by unfold p_25519; decide)
  -- Stage 2: sqr_chain_loop_effect on the (n-1)-iter loop.
  obtain ⟨s2, h_run2, final_addr, h_final_addr_eq, h_final_mem, h_frame2⟩ :=
    sqr_chain_loop_effect registry hAx s1 fuel
      op_addr ap_addr h_op1 h_ap1 (n - 1)
      BignumInvP25519.OFF_t BignumInvP25519.OFF_u
      (by decide) (by decide) (by decide) (by decide)
      t_addr u_addr h_t_addr_eq h_u_addr_eq
      (src_val * src_val % p_25519) h_squared_lt h_t_mem1
      h_t_alloc1 h_u_alloc1 h_no_alias_t_u (startIdx + 1)
  -- Stage 2a: register preservation across the loop body.
  have h_op2 : s2.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
    rw [← h_op1]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "op"
      (sqr_chain_loop_preservesRegRec_of_ne (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) "op"
        (by decide) (by decide) (by decide))
      s1 s2 h_run2
  have h_ap2 : s2.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [← h_ap1]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "ap"
      (sqr_chain_loop_preservesRegRec_of_ne (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) "ap"
        (by decide) (by decide) (by decide))
      s1 s2 h_run2
  -- Stage 2c: dst alloc preserved through step1 + step2.
  have h_dst_alloc2 : ∀ k : Fin 32,
      ∃ b, s2.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b := by
    intro k
    have h_not_t : ¬ MemoryModel.range t_addr 32 (dst_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_dst_t k ⟨k', hk'⟩ h_eq
    have h_not_u : ¬ MemoryModel.range u_addr 32 (dst_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_dst_u k ⟨k', hk'⟩ h_eq
    rw [h_frame2 _ h_not_t h_not_u, h_frame1 _ h_not_t]
    exact h_dst_alloc k
  -- Stage 2d: other_addr's value preserved through step1 + step2.
  have h_other_mem2 : memNat4 other_addr s2.mem = some other_val := by
    have h_byte_frame_other : ∀ k : Nat, k < 32 →
        s2.mem.loadByte (other_addr + UInt64.ofNat k) =
          s.mem.loadByte (other_addr + UInt64.ofNat k) := by
      intro k hk
      have h_not_t : ¬ MemoryModel.range t_addr 32 (other_addr + UInt64.ofNat k) := by
        rintro ⟨k', hk', h_eq⟩
        exact h_no_alias_other_t ⟨k, hk⟩ ⟨k', hk'⟩ h_eq
      have h_not_u : ¬ MemoryModel.range u_addr 32 (other_addr + UInt64.ofNat k) := by
        rintro ⟨k', hk', h_eq⟩
        exact h_no_alias_other_u ⟨k, hk⟩ ⟨k', hk'⟩ h_eq
      rw [h_frame2 _ h_not_t h_not_u, h_frame1 _ h_not_t]
    have h_eq : memNat4 other_addr s2.mem = memNat4 other_addr s.mem :=
      memNat4_eq_of_byte_eq other_addr s2.mem s.mem h_byte_frame_other
    rw [h_eq]; exact h_other_mem
  -- Stage 3a: finalOff is ≠ {0, -1}.  By sqr_chain_loop_final_off, it's
  -- either OFF_t or OFF_u; both are 384 / 416 ≠ {0, -1}.
  have h_finalOff_value : loop_finalOff =
      (if (n - 1) % 2 = 0 then BignumInvP25519.OFF_t else BignumInvP25519.OFF_u) := by
    simp only [loop_finalOff]
    exact sqr_chain_loop_final_off (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1)
  have h_finalOff_ne_zero : loop_finalOff ≠ 0 := by
    rw [h_finalOff_value]; split <;> decide
  have h_finalOff_ne_negOne : loop_finalOff ≠ -1 := by
    rw [h_finalOff_value]; split <;> decide
  -- Stage 3: chain_mul_step_correct on mul_body.
  obtain ⟨s', h_run3, h_dst_mem3, h_frame3⟩ :=
    chain_mul_step_correct registry hAx s2 fuel
      op_addr ap_addr h_op2 h_ap2
      final_addr other_addr
      ((src_val * src_val % p_25519) ^ (2 ^ (n - 1)) % p_25519) other_val
      h_final_mem h_other_mem2
      dst_addr h_dst_alloc2
      loop_finalIdx dstOff loop_finalOff otherOff
      h_dstOff_ne_zero h_dstOff_ne_negOne
      h_finalOff_ne_zero h_finalOff_ne_negOne
      h_otherOff_ne_zero h_otherOff_ne_negOne
      h_dst_addr_eq h_final_addr_eq h_other_addr_eq
      mul_body rfl
  -- Compose s → s1 → s2 → s' via bignumExecFuel_append_join.
  refine ⟨s', ?_, ?_, ?_⟩
  · -- bignumExecFuel registry (fuel+1) (step0 ++ loop_body ++ mul_body) s = some s'
    have h_step01 := CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1) step0 loop_body
        (sqr_step_isNonControl startIdx BignumInvP25519.OFF_t srcOff)
        s s1 s2 h_run1 h_run2
    exact CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1) (step0 ++ loop_body) mul_body
        (by
          intro i hi
          rcases List.mem_append.mp hi with h | h
          · exact sqr_step_isNonControl startIdx BignumInvP25519.OFF_t srcOff i h
          · exact sqr_chain_loop_isNonControl (n - 1) BignumInvP25519.OFF_t
              BignumInvP25519.OFF_u (startIdx + 1) i h)
        s s2 s' h_step01 h_run3
  · -- Algebraic bridge:
    -- ((src² % p)^(2^(n-1)) % p * other) % p = (src^(2^n) * other) % p.
    rw [h_dst_mem3]
    congr 1
    -- Goal: ((src*src) % p)^(2^(n-1)) % p * other % p = src^(2^n) * other % p
    -- Step A: ((src*src) % p)^(2^(n-1)) % p = (src*src)^(2^(n-1)) % p (Nat.pow_mod ←).
    rw [show (src_val * src_val % p_25519) ^ 2 ^ (n - 1) % p_25519 =
            (src_val * src_val) ^ 2 ^ (n - 1) % p_25519 from
        (Nat.pow_mod (src_val * src_val) (2 ^ (n - 1)) p_25519).symm]
    -- Step B: a % p * b % p = a * b % p via Nat.mul_mod.
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    -- Goal: (src*src)^(2^(n-1)) * other % p = src^(2^n) * other % p
    congr 1
    -- Goal: (src*src)^(2^(n-1)) * other = src^(2^n) * other
    congr 1
    -- Goal: (src*src)^(2^(n-1)) = src^(2^n)
    rw [show src_val * src_val = src_val ^ 2 from (sq src_val).symm, ← pow_mul]
    -- Goal: src^(2 * 2^(n-1)) = src^(2^n)
    congr 1
    -- Goal: 2 * 2^(n-1) = 2^n
    have h_n_eq : n = (n - 1) + 1 := by omega
    conv_rhs => rw [h_n_eq, pow_succ]
    ring
  · -- Frame composition: bytes outside dst/t/u 32-byte windows unchanged
    -- from s to s' via s → s1 (frame outside t) → s2 (frame outside t ∪ u)
    -- → s' (frame outside dst).
    intro addr h_not_dst h_not_t h_not_u
    rw [h_frame3 addr h_not_dst, h_frame2 addr h_not_t h_not_u, h_frame1 addr h_not_t]

/-! ## §2.5b  `dstOff = 0` discharge (block 13) -/

/-- **rsm with `dstOff = 0`.**  Specialised discharge for block 13's
    terminal `op := z2_250_0^32 · z11`: the destination is `op_addr`
    itself.  Uses `chain_mul_step_correct_dst_zero` for the final
    multiply step. -/
theorem chain_repeated_sqr_then_mul_correct_dst_zero
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (n : Nat) (h_n : n ≥ 1)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (src_addr other_addr : UInt64)
    (src_val other_val : Nat)
    (h_src_mem : memNat4 src_addr s.mem = some src_val)
    (h_other_mem : memNat4 other_addr s.mem = some other_val)
    (h_op_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)
    (startIdx : Nat) (srcOff otherOff : Int)
    (h_srcOff_ne_zero : srcOff ≠ 0) (h_srcOff_ne_negOne : srcOff ≠ -1)
    (h_otherOff_ne_zero : otherOff ≠ 0) (h_otherOff_ne_negOne : otherOff ≠ -1)
    (h_src_addr_eq : BitVec.ofNat 64 src_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 srcOff)
    (h_other_addr_eq : BitVec.ofNat 64 other_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 otherOff)
    (t_addr u_addr : UInt64)
    (h_t_addr_eq : BitVec.ofNat 64 t_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_t)
    (h_u_addr_eq : BitVec.ofNat 64 u_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_u)
    (h_t_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b)
    (h_u_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b)
    -- Non-aliasing.
    (h_no_alias_op_t : ∀ k1 k2 : Fin 32,
       op_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_op_u : ∀ k1 k2 : Fin 32,
       op_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_src_t : ∀ k1 k2 : Fin 32,
       src_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_src_u : ∀ k1 k2 : Fin 32,
       src_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_other_t : ∀ k1 k2 : Fin 32,
       other_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_other_u : ∀ k1 k2 : Fin 32,
       other_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_t_u : ∀ k1 k2 : Fin 32,
       t_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx 0 srcOff otherOff n).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 op_addr s'.mem =
        some (((src_val ^ (2^n)) * other_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range op_addr 32 addr →
         ¬ MemoryModel.range t_addr 32 addr →
         ¬ MemoryModel.range u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) := by
  set step0 := BignumInvP25519.sqr_step startIdx BignumInvP25519.OFF_t srcOff
  set loop_body :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).fst
  set loop_finalOff :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).snd.fst
  set loop_finalIdx :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).snd.snd
  set mul_body :=
    BignumInvP25519.mul_step loop_finalIdx 0 loop_finalOff otherOff
  have h_body : (BignumInvP25519.repeated_sqr_then_mul startIdx 0 srcOff
      otherOff n).fst = step0 ++ loop_body ++ mul_body := by
    rw [repeated_sqr_then_mul_unfold]
    simp only [step0, loop_body, loop_finalOff, loop_finalIdx, mul_body]
    rw [sqr_chain_loop_acc_split (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
    rw [sqr_chain_loop_acc_final_off (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
    rw [sqr_chain_loop_acc_final_idx (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
  rw [h_shape, h_body]
  -- Stage 1: step0.
  obtain ⟨s1, h_run1, h_t_mem1, h_frame1⟩ :=
    chain_sqr_step_correct_generic registry hAx s fuel
      op_addr ap_addr h_op h_ap
      src_addr src_val h_src_mem
      t_addr h_t_alloc
      startIdx BignumInvP25519.OFF_t srcOff
      (by decide) (by decide)
      h_srcOff_ne_zero h_srcOff_ne_negOne
      h_t_addr_eq h_src_addr_eq
      step0 rfl
  have h_op1 : s1.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
    rw [← h_op]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "op"
      (sqr_step_preservesRegRec_of_ne startIdx BignumInvP25519.OFF_t srcOff "op"
        (by decide) (by decide) (by decide))
      s s1 h_run1
  have h_ap1 : s1.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [← h_ap]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "ap"
      (sqr_step_preservesRegRec_of_ne startIdx BignumInvP25519.OFF_t srcOff "ap"
        (by decide) (by decide) (by decide))
      s s1 h_run1
  have h_t_alloc1 : ∀ k : Fin 32,
      ∃ b, s1.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b := by
    intro k
    exact memNat4_imp_byte_alloc t_addr s1.mem _ h_t_mem1 k.val k.isLt
  have h_u_alloc1 : ∀ k : Fin 32,
      ∃ b, s1.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b := by
    intro k
    have h_outside : ¬ MemoryModel.range t_addr 32
        (u_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_t_u ⟨k', hk'⟩ k h_eq.symm
    rw [h_frame1 _ h_outside]
    exact h_u_alloc k
  have h_squared_lt : src_val * src_val % p_25519 < p_25519 :=
    Nat.mod_lt _ (by unfold p_25519; decide)
  -- Stage 2: loop.
  obtain ⟨s2, h_run2, final_addr, h_final_addr_eq, h_final_mem, h_frame2⟩ :=
    sqr_chain_loop_effect registry hAx s1 fuel
      op_addr ap_addr h_op1 h_ap1 (n - 1)
      BignumInvP25519.OFF_t BignumInvP25519.OFF_u
      (by decide) (by decide) (by decide) (by decide)
      t_addr u_addr h_t_addr_eq h_u_addr_eq
      (src_val * src_val % p_25519) h_squared_lt h_t_mem1
      h_t_alloc1 h_u_alloc1 h_no_alias_t_u (startIdx + 1)
  have h_op2 : s2.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
    rw [← h_op1]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "op"
      (sqr_chain_loop_preservesRegRec_of_ne (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) "op"
        (by decide) (by decide) (by decide))
      s1 s2 h_run2
  have h_ap2 : s2.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [← h_ap1]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "ap"
      (sqr_chain_loop_preservesRegRec_of_ne (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) "ap"
        (by decide) (by decide) (by decide))
      s1 s2 h_run2
  have h_op_alloc2 : ∀ k : Fin 32,
      ∃ b, s2.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b := by
    intro k
    have h_not_t : ¬ MemoryModel.range t_addr 32 (op_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_op_t k ⟨k', hk'⟩ h_eq
    have h_not_u : ¬ MemoryModel.range u_addr 32 (op_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_op_u k ⟨k', hk'⟩ h_eq
    rw [h_frame2 _ h_not_t h_not_u, h_frame1 _ h_not_t]
    exact h_op_alloc k
  have h_other_mem2 : memNat4 other_addr s2.mem = some other_val := by
    have h_byte_frame_other : ∀ k : Nat, k < 32 →
        s2.mem.loadByte (other_addr + UInt64.ofNat k) =
          s.mem.loadByte (other_addr + UInt64.ofNat k) := by
      intro k hk
      have h_not_t : ¬ MemoryModel.range t_addr 32 (other_addr + UInt64.ofNat k) := by
        rintro ⟨k', hk', h_eq⟩
        exact h_no_alias_other_t ⟨k, hk⟩ ⟨k', hk'⟩ h_eq
      have h_not_u : ¬ MemoryModel.range u_addr 32 (other_addr + UInt64.ofNat k) := by
        rintro ⟨k', hk', h_eq⟩
        exact h_no_alias_other_u ⟨k, hk⟩ ⟨k', hk'⟩ h_eq
      rw [h_frame2 _ h_not_t h_not_u, h_frame1 _ h_not_t]
    have h_eq : memNat4 other_addr s2.mem = memNat4 other_addr s.mem :=
      memNat4_eq_of_byte_eq other_addr s2.mem s.mem h_byte_frame_other
    rw [h_eq]; exact h_other_mem
  have h_finalOff_value : loop_finalOff =
      (if (n - 1) % 2 = 0 then BignumInvP25519.OFF_t else BignumInvP25519.OFF_u) := by
    simp only [loop_finalOff]
    exact sqr_chain_loop_final_off (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1)
  have h_finalOff_ne_zero : loop_finalOff ≠ 0 := by
    rw [h_finalOff_value]; split <;> decide
  have h_finalOff_ne_negOne : loop_finalOff ≠ -1 := by
    rw [h_finalOff_value]; split <;> decide
  -- Stage 3: chain_mul_step_correct_dst_zero on mul_body.
  obtain ⟨s', h_run3, h_dst_mem3, h_frame3⟩ :=
    chain_mul_step_correct_dst_zero registry hAx s2 fuel
      op_addr ap_addr h_op2 h_ap2
      final_addr other_addr
      ((src_val * src_val % p_25519) ^ (2 ^ (n - 1)) % p_25519) other_val
      h_final_mem h_other_mem2 h_op_alloc2
      loop_finalIdx loop_finalOff otherOff
      h_finalOff_ne_zero h_finalOff_ne_negOne
      h_otherOff_ne_zero h_otherOff_ne_negOne
      h_final_addr_eq h_other_addr_eq
      mul_body rfl
  refine ⟨s', ?_, ?_, ?_⟩
  · have h_step01 := CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1) step0 loop_body
        (sqr_step_isNonControl startIdx BignumInvP25519.OFF_t srcOff)
        s s1 s2 h_run1 h_run2
    exact CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1) (step0 ++ loop_body) mul_body
        (by
          intro i hi
          rcases List.mem_append.mp hi with h | h
          · exact sqr_step_isNonControl startIdx BignumInvP25519.OFF_t srcOff i h
          · exact sqr_chain_loop_isNonControl (n - 1) BignumInvP25519.OFF_t
              BignumInvP25519.OFF_u (startIdx + 1) i h)
        s s2 s' h_step01 h_run3
  · -- Algebraic bridge (identical to the generic case).
    rw [h_dst_mem3]
    congr 1
    rw [show (src_val * src_val % p_25519) ^ 2 ^ (n - 1) % p_25519 =
            (src_val * src_val) ^ 2 ^ (n - 1) % p_25519 from
        (Nat.pow_mod (src_val * src_val) (2 ^ (n - 1)) p_25519).symm]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    congr 1
    congr 1
    rw [show src_val * src_val = src_val ^ 2 from (sq src_val).symm, ← pow_mul]
    congr 1
    have h_n_eq : n = (n - 1) + 1 := by omega
    conv_rhs => rw [h_n_eq, pow_succ]
    ring
  · intro addr h_not_op h_not_t h_not_u
    rw [h_frame3 addr h_not_op, h_frame2 addr h_not_t h_not_u, h_frame1 addr h_not_t]

/-! ## §2.5c  `otherOff = -1` discharge (block 3) -/

/-- **rsm with `otherOff = -1`.**  Specialised discharge for block 3's
    `z9 := z2² · ap`: the "other" buffer is `ap_addr` itself.  Uses
    `chain_mul_step_correct_b_negOne` for the final multiply step. -/
theorem chain_repeated_sqr_then_mul_correct_other_negOne
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (n : Nat) (h_n : n ≥ 1)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (src_addr dst_addr : UInt64)
    (src_val ap_val : Nat)
    (h_src_mem : memNat4 src_addr s.mem = some src_val)
    (h_ap_mem : memNat4 ap_addr s.mem = some ap_val)
    (h_dst_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b)
    (startIdx : Nat) (dstOff srcOff : Int)
    (h_dstOff_ne_zero : dstOff ≠ 0) (h_dstOff_ne_negOne : dstOff ≠ -1)
    (h_srcOff_ne_zero : srcOff ≠ 0) (h_srcOff_ne_negOne : srcOff ≠ -1)
    (h_dst_addr_eq : BitVec.ofNat 64 dst_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 dstOff)
    (h_src_addr_eq : BitVec.ofNat 64 src_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 srcOff)
    (t_addr u_addr : UInt64)
    (h_t_addr_eq : BitVec.ofNat 64 t_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_t)
    (h_u_addr_eq : BitVec.ofNat 64 u_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_u)
    (h_t_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b)
    (h_u_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b)
    (h_no_alias_dst_t : ∀ k1 k2 : Fin 32,
       dst_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_dst_u : ∀ k1 k2 : Fin 32,
       dst_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_src_t : ∀ k1 k2 : Fin 32,
       src_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_src_u : ∀ k1 k2 : Fin 32,
       src_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_ap_t : ∀ k1 k2 : Fin 32,
       ap_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_ap_u : ∀ k1 k2 : Fin 32,
       ap_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_t_u : ∀ k1 k2 : Fin 32,
       t_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx dstOff srcOff (-1) n).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 dst_addr s'.mem =
        some (((src_val ^ (2^n)) * ap_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range dst_addr 32 addr →
         ¬ MemoryModel.range t_addr 32 addr →
         ¬ MemoryModel.range u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) := by
  set step0 := BignumInvP25519.sqr_step startIdx BignumInvP25519.OFF_t srcOff
  set loop_body :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).fst
  set loop_finalOff :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).snd.fst
  set loop_finalIdx :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).snd.snd
  set mul_body :=
    BignumInvP25519.mul_step loop_finalIdx dstOff loop_finalOff (-1)
  have h_body : (BignumInvP25519.repeated_sqr_then_mul startIdx dstOff srcOff
      (-1) n).fst = step0 ++ loop_body ++ mul_body := by
    rw [repeated_sqr_then_mul_unfold]
    simp only [step0, loop_body, loop_finalOff, loop_finalIdx, mul_body]
    rw [sqr_chain_loop_acc_split (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
    rw [sqr_chain_loop_acc_final_off (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
    rw [sqr_chain_loop_acc_final_idx (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
  rw [h_shape, h_body]
  -- Stage 1: step0.
  obtain ⟨s1, h_run1, h_t_mem1, h_frame1⟩ :=
    chain_sqr_step_correct_generic registry hAx s fuel
      op_addr ap_addr h_op h_ap
      src_addr src_val h_src_mem
      t_addr h_t_alloc
      startIdx BignumInvP25519.OFF_t srcOff
      (by decide) (by decide)
      h_srcOff_ne_zero h_srcOff_ne_negOne
      h_t_addr_eq h_src_addr_eq
      step0 rfl
  have h_op1 : s1.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
    rw [← h_op]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "op"
      (sqr_step_preservesRegRec_of_ne startIdx BignumInvP25519.OFF_t srcOff "op"
        (by decide) (by decide) (by decide))
      s s1 h_run1
  have h_ap1 : s1.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [← h_ap]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "ap"
      (sqr_step_preservesRegRec_of_ne startIdx BignumInvP25519.OFF_t srcOff "ap"
        (by decide) (by decide) (by decide))
      s s1 h_run1
  have h_t_alloc1 : ∀ k : Fin 32,
      ∃ b, s1.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b := by
    intro k
    exact memNat4_imp_byte_alloc t_addr s1.mem _ h_t_mem1 k.val k.isLt
  have h_u_alloc1 : ∀ k : Fin 32,
      ∃ b, s1.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b := by
    intro k
    have h_outside : ¬ MemoryModel.range t_addr 32
        (u_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_t_u ⟨k', hk'⟩ k h_eq.symm
    rw [h_frame1 _ h_outside]
    exact h_u_alloc k
  have h_squared_lt : src_val * src_val % p_25519 < p_25519 :=
    Nat.mod_lt _ (by unfold p_25519; decide)
  -- Stage 2: loop.
  obtain ⟨s2, h_run2, final_addr, h_final_addr_eq, h_final_mem, h_frame2⟩ :=
    sqr_chain_loop_effect registry hAx s1 fuel
      op_addr ap_addr h_op1 h_ap1 (n - 1)
      BignumInvP25519.OFF_t BignumInvP25519.OFF_u
      (by decide) (by decide) (by decide) (by decide)
      t_addr u_addr h_t_addr_eq h_u_addr_eq
      (src_val * src_val % p_25519) h_squared_lt h_t_mem1
      h_t_alloc1 h_u_alloc1 h_no_alias_t_u (startIdx + 1)
  have h_op2 : s2.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
    rw [← h_op1]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "op"
      (sqr_chain_loop_preservesRegRec_of_ne (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) "op"
        (by decide) (by decide) (by decide))
      s1 s2 h_run2
  have h_ap2 : s2.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [← h_ap1]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "ap"
      (sqr_chain_loop_preservesRegRec_of_ne (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) "ap"
        (by decide) (by decide) (by decide))
      s1 s2 h_run2
  have h_dst_alloc2 : ∀ k : Fin 32,
      ∃ b, s2.mem.loadByte (dst_addr + UInt64.ofNat k.val) = some b := by
    intro k
    have h_not_t : ¬ MemoryModel.range t_addr 32 (dst_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_dst_t k ⟨k', hk'⟩ h_eq
    have h_not_u : ¬ MemoryModel.range u_addr 32 (dst_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_dst_u k ⟨k', hk'⟩ h_eq
    rw [h_frame2 _ h_not_t h_not_u, h_frame1 _ h_not_t]
    exact h_dst_alloc k
  have h_ap_mem2 : memNat4 ap_addr s2.mem = some ap_val := by
    have h_byte_frame_ap : ∀ k : Nat, k < 32 →
        s2.mem.loadByte (ap_addr + UInt64.ofNat k) =
          s.mem.loadByte (ap_addr + UInt64.ofNat k) := by
      intro k hk
      have h_not_t : ¬ MemoryModel.range t_addr 32 (ap_addr + UInt64.ofNat k) := by
        rintro ⟨k', hk', h_eq⟩
        exact h_no_alias_ap_t ⟨k, hk⟩ ⟨k', hk'⟩ h_eq
      have h_not_u : ¬ MemoryModel.range u_addr 32 (ap_addr + UInt64.ofNat k) := by
        rintro ⟨k', hk', h_eq⟩
        exact h_no_alias_ap_u ⟨k, hk⟩ ⟨k', hk'⟩ h_eq
      rw [h_frame2 _ h_not_t h_not_u, h_frame1 _ h_not_t]
    have h_eq : memNat4 ap_addr s2.mem = memNat4 ap_addr s.mem :=
      memNat4_eq_of_byte_eq ap_addr s2.mem s.mem h_byte_frame_ap
    rw [h_eq]; exact h_ap_mem
  have h_finalOff_value : loop_finalOff =
      (if (n - 1) % 2 = 0 then BignumInvP25519.OFF_t else BignumInvP25519.OFF_u) := by
    simp only [loop_finalOff]
    exact sqr_chain_loop_final_off (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1)
  have h_finalOff_ne_zero : loop_finalOff ≠ 0 := by
    rw [h_finalOff_value]; split <;> decide
  have h_finalOff_ne_negOne : loop_finalOff ≠ -1 := by
    rw [h_finalOff_value]; split <;> decide
  -- Stage 3: chain_mul_step_correct_b_negOne.
  obtain ⟨s', h_run3, h_dst_mem3, h_frame3⟩ :=
    chain_mul_step_correct_b_negOne registry hAx s2 fuel
      op_addr ap_addr h_op2 h_ap2
      final_addr
      ((src_val * src_val % p_25519) ^ (2 ^ (n - 1)) % p_25519) ap_val
      h_final_mem h_ap_mem2
      dst_addr h_dst_alloc2
      loop_finalIdx dstOff loop_finalOff
      h_dstOff_ne_zero h_dstOff_ne_negOne
      h_finalOff_ne_zero h_finalOff_ne_negOne
      h_dst_addr_eq h_final_addr_eq
      mul_body rfl
  refine ⟨s', ?_, ?_, ?_⟩
  · have h_step01 := CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1) step0 loop_body
        (sqr_step_isNonControl startIdx BignumInvP25519.OFF_t srcOff)
        s s1 s2 h_run1 h_run2
    exact CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1) (step0 ++ loop_body) mul_body
        (by
          intro i hi
          rcases List.mem_append.mp hi with h | h
          · exact sqr_step_isNonControl startIdx BignumInvP25519.OFF_t srcOff i h
          · exact sqr_chain_loop_isNonControl (n - 1) BignumInvP25519.OFF_t
              BignumInvP25519.OFF_u (startIdx + 1) i h)
        s s2 s' h_step01 h_run3
  · rw [h_dst_mem3]
    congr 1
    rw [show (src_val * src_val % p_25519) ^ 2 ^ (n - 1) % p_25519 =
            (src_val * src_val) ^ 2 ^ (n - 1) % p_25519 from
        (Nat.pow_mod (src_val * src_val) (2 ^ (n - 1)) p_25519).symm]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    congr 1
    congr 1
    rw [show src_val * src_val = src_val ^ 2 from (sq src_val).symm, ← pow_mul]
    congr 1
    have h_n_eq : n = (n - 1) + 1 := by omega
    conv_rhs => rw [h_n_eq, pow_succ]
    ring
  · intro addr h_not_dst h_not_t h_not_u
    rw [h_frame3 addr h_not_dst, h_frame2 addr h_not_t h_not_u, h_frame1 addr h_not_t]

/-! ## §2.5d  `dstOff = 0` AND `otherOff = -1` discharge (p58 block 13b) -/

/-- **rsm with `dstOff = 0` AND `otherOff = -1`.**  Discharge for the
    p58 chain's terminal `op := z2_250_0^4 · ap`. -/
theorem chain_repeated_sqr_then_mul_correct_dst_zero_other_negOne
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (n : Nat) (h_n : n ≥ 1)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (src_addr : UInt64)
    (src_val ap_val : Nat)
    (h_src_mem : memNat4 src_addr s.mem = some src_val)
    (h_ap_mem : memNat4 ap_addr s.mem = some ap_val)
    (h_op_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)
    (startIdx : Nat) (srcOff : Int)
    (h_srcOff_ne_zero : srcOff ≠ 0) (h_srcOff_ne_negOne : srcOff ≠ -1)
    (h_src_addr_eq : BitVec.ofNat 64 src_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 srcOff)
    (t_addr u_addr : UInt64)
    (h_t_addr_eq : BitVec.ofNat 64 t_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_t)
    (h_u_addr_eq : BitVec.ofNat 64 u_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_u)
    (h_t_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b)
    (h_u_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b)
    (h_no_alias_op_t : ∀ k1 k2 : Fin 32,
       op_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_op_u : ∀ k1 k2 : Fin 32,
       op_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_src_t : ∀ k1 k2 : Fin 32,
       src_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_src_u : ∀ k1 k2 : Fin 32,
       src_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_ap_t : ∀ k1 k2 : Fin 32,
       ap_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val)
    (h_no_alias_ap_u : ∀ k1 k2 : Fin 32,
       ap_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (h_no_alias_t_u : ∀ k1 k2 : Fin 32,
       t_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx 0 srcOff (-1) n).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 op_addr s'.mem =
        some (((src_val ^ (2^n)) * ap_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range op_addr 32 addr →
         ¬ MemoryModel.range t_addr 32 addr →
         ¬ MemoryModel.range u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) := by
  set step0 := BignumInvP25519.sqr_step startIdx BignumInvP25519.OFF_t srcOff
  set loop_body :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).fst
  set loop_finalOff :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).snd.fst
  set loop_finalIdx :=
    (BignumInvP25519.sqr_chain_loop (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1) []).snd.snd
  set mul_body :=
    BignumInvP25519.mul_step loop_finalIdx 0 loop_finalOff (-1)
  have h_body : (BignumInvP25519.repeated_sqr_then_mul startIdx 0 srcOff
      (-1) n).fst = step0 ++ loop_body ++ mul_body := by
    rw [repeated_sqr_then_mul_unfold]
    simp only [step0, loop_body, loop_finalOff, loop_finalIdx, mul_body]
    rw [sqr_chain_loop_acc_split (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
    rw [sqr_chain_loop_acc_final_off (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
    rw [sqr_chain_loop_acc_final_idx (n - 1) BignumInvP25519.OFF_t
          BignumInvP25519.OFF_u (startIdx + 1) step0]
  rw [h_shape, h_body]
  obtain ⟨s1, h_run1, h_t_mem1, h_frame1⟩ :=
    chain_sqr_step_correct_generic registry hAx s fuel
      op_addr ap_addr h_op h_ap
      src_addr src_val h_src_mem
      t_addr h_t_alloc
      startIdx BignumInvP25519.OFF_t srcOff
      (by decide) (by decide)
      h_srcOff_ne_zero h_srcOff_ne_negOne
      h_t_addr_eq h_src_addr_eq
      step0 rfl
  have h_op1 : s1.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
    rw [← h_op]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "op"
      (sqr_step_preservesRegRec_of_ne startIdx BignumInvP25519.OFF_t srcOff "op"
        (by decide) (by decide) (by decide))
      s s1 h_run1
  have h_ap1 : s1.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [← h_ap]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "ap"
      (sqr_step_preservesRegRec_of_ne startIdx BignumInvP25519.OFF_t srcOff "ap"
        (by decide) (by decide) (by decide))
      s s1 h_run1
  have h_t_alloc1 : ∀ k : Fin 32,
      ∃ b, s1.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b := by
    intro k
    exact memNat4_imp_byte_alloc t_addr s1.mem _ h_t_mem1 k.val k.isLt
  have h_u_alloc1 : ∀ k : Fin 32,
      ∃ b, s1.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b := by
    intro k
    have h_outside : ¬ MemoryModel.range t_addr 32
        (u_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_t_u ⟨k', hk'⟩ k h_eq.symm
    rw [h_frame1 _ h_outside]
    exact h_u_alloc k
  have h_squared_lt : src_val * src_val % p_25519 < p_25519 :=
    Nat.mod_lt _ (by unfold p_25519; decide)
  obtain ⟨s2, h_run2, final_addr, h_final_addr_eq, h_final_mem, h_frame2⟩ :=
    sqr_chain_loop_effect registry hAx s1 fuel
      op_addr ap_addr h_op1 h_ap1 (n - 1)
      BignumInvP25519.OFF_t BignumInvP25519.OFF_u
      (by decide) (by decide) (by decide) (by decide)
      t_addr u_addr h_t_addr_eq h_u_addr_eq
      (src_val * src_val % p_25519) h_squared_lt h_t_mem1
      h_t_alloc1 h_u_alloc1 h_no_alias_t_u (startIdx + 1)
  have h_op2 : s2.regs "op" = BitVec.ofNat 64 op_addr.toNat := by
    rw [← h_op1]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "op"
      (sqr_chain_loop_preservesRegRec_of_ne (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) "op"
        (by decide) (by decide) (by decide))
      s1 s2 h_run2
  have h_ap2 : s2.regs "ap" = BitVec.ofNat 64 ap_addr.toNat := by
    rw [← h_ap1]
    exact CatCrypt.Tactics.PreservationCombinator.bignumExecFuel_preserves_reg
      registry _ _ "ap"
      (sqr_chain_loop_preservesRegRec_of_ne (n - 1) BignumInvP25519.OFF_t
        BignumInvP25519.OFF_u (startIdx + 1) "ap"
        (by decide) (by decide) (by decide))
      s1 s2 h_run2
  have h_op_alloc2 : ∀ k : Fin 32,
      ∃ b, s2.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b := by
    intro k
    have h_not_t : ¬ MemoryModel.range t_addr 32 (op_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_op_t k ⟨k', hk'⟩ h_eq
    have h_not_u : ¬ MemoryModel.range u_addr 32 (op_addr + UInt64.ofNat k.val) := by
      rintro ⟨k', hk', h_eq⟩
      exact h_no_alias_op_u k ⟨k', hk'⟩ h_eq
    rw [h_frame2 _ h_not_t h_not_u, h_frame1 _ h_not_t]
    exact h_op_alloc k
  have h_ap_mem2 : memNat4 ap_addr s2.mem = some ap_val := by
    have h_byte_frame_ap : ∀ k : Nat, k < 32 →
        s2.mem.loadByte (ap_addr + UInt64.ofNat k) =
          s.mem.loadByte (ap_addr + UInt64.ofNat k) := by
      intro k hk
      have h_not_t : ¬ MemoryModel.range t_addr 32 (ap_addr + UInt64.ofNat k) := by
        rintro ⟨k', hk', h_eq⟩
        exact h_no_alias_ap_t ⟨k, hk⟩ ⟨k', hk'⟩ h_eq
      have h_not_u : ¬ MemoryModel.range u_addr 32 (ap_addr + UInt64.ofNat k) := by
        rintro ⟨k', hk', h_eq⟩
        exact h_no_alias_ap_u ⟨k, hk⟩ ⟨k', hk'⟩ h_eq
      rw [h_frame2 _ h_not_t h_not_u, h_frame1 _ h_not_t]
    have h_eq : memNat4 ap_addr s2.mem = memNat4 ap_addr s.mem :=
      memNat4_eq_of_byte_eq ap_addr s2.mem s.mem h_byte_frame_ap
    rw [h_eq]; exact h_ap_mem
  have h_finalOff_value : loop_finalOff =
      (if (n - 1) % 2 = 0 then BignumInvP25519.OFF_t else BignumInvP25519.OFF_u) := by
    simp only [loop_finalOff]
    exact sqr_chain_loop_final_off (n - 1) BignumInvP25519.OFF_t
      BignumInvP25519.OFF_u (startIdx + 1)
  have h_finalOff_ne_zero : loop_finalOff ≠ 0 := by
    rw [h_finalOff_value]; split <;> decide
  have h_finalOff_ne_negOne : loop_finalOff ≠ -1 := by
    rw [h_finalOff_value]; split <;> decide
  obtain ⟨s', h_run3, h_dst_mem3, h_frame3⟩ :=
    chain_mul_step_correct_dst_zero_b_negOne registry hAx s2 fuel
      op_addr ap_addr h_op2 h_ap2
      final_addr
      ((src_val * src_val % p_25519) ^ (2 ^ (n - 1)) % p_25519) ap_val
      h_final_mem h_ap_mem2 h_op_alloc2
      loop_finalIdx loop_finalOff
      h_finalOff_ne_zero h_finalOff_ne_negOne
      h_final_addr_eq
      mul_body rfl
  refine ⟨s', ?_, ?_, ?_⟩
  · have h_step01 := CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1) step0 loop_body
        (sqr_step_isNonControl startIdx BignumInvP25519.OFF_t srcOff)
        s s1 s2 h_run1 h_run2
    exact CatCrypt.Crypto.Jasmin.BignumExec.bignumExecFuel_append_join
        registry (fuel + 1) (step0 ++ loop_body) mul_body
        (by
          intro i hi
          rcases List.mem_append.mp hi with h | h
          · exact sqr_step_isNonControl startIdx BignumInvP25519.OFF_t srcOff i h
          · exact sqr_chain_loop_isNonControl (n - 1) BignumInvP25519.OFF_t
              BignumInvP25519.OFF_u (startIdx + 1) i h)
        s s2 s' h_step01 h_run3
  · rw [h_dst_mem3]
    congr 1
    rw [show (src_val * src_val % p_25519) ^ 2 ^ (n - 1) % p_25519 =
            (src_val * src_val) ^ 2 ^ (n - 1) % p_25519 from
        (Nat.pow_mod (src_val * src_val) (2 ^ (n - 1)) p_25519).symm]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    congr 1
    congr 1
    rw [show src_val * src_val = src_val ^ 2 from (sq src_val).symm, ← pow_mul]
    congr 1
    have h_n_eq : n = (n - 1) + 1 := by omega
    conv_rhs => rw [h_n_eq, pow_succ]
    ring
  · intro addr h_not_op h_not_t h_not_u
    rw [h_frame3 addr h_not_op, h_frame2 addr h_not_t h_not_u, h_frame1 addr h_not_t]

/-! ## §2.6  Scratch buffer bundle

Each `repeated_sqr_then_mul` block uses two scratch buffers at
`OFF_t` and `OFF_u` (relative to `op_addr`).  Bundling their
addresses + allocation + non-aliasing hypotheses into a single
record keeps the §3 block theorem signatures compact. -/

/-- Scratch-buffer evidence for a `repeated_sqr_then_mul` block at
    state `s` with base register `op_addr`, used together with input
    addresses (`src_addr`, `other_addr`) and an output address
    (`dst_addr`).  Encapsulates:
    * Address derivations: `t/u_addr = op_addr + OFF_{t,u}`.
    * Allocation: 32 bytes readable at `t_addr` and `u_addr`.
    * Non-aliasing: `dst/src/other` 32-byte windows disjoint from
      both scratch windows. -/
structure RsmScratch (s : BignumState) (op_addr dst_addr src_addr other_addr : UInt64) where
  t_addr : UInt64
  u_addr : UInt64
  h_t_addr_eq : BitVec.ofNat 64 t_addr.toNat =
     BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_t
  h_u_addr_eq : BitVec.ofNat 64 u_addr.toNat =
     BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_u
  h_t_alloc : ∀ k : Fin 32,
    ∃ b, s.mem.loadByte (t_addr + UInt64.ofNat k.val) = some b
  h_u_alloc : ∀ k : Fin 32,
    ∃ b, s.mem.loadByte (u_addr + UInt64.ofNat k.val) = some b
  h_no_alias_dst_t : ∀ k1 k2 : Fin 32,
     dst_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val
  h_no_alias_dst_u : ∀ k1 k2 : Fin 32,
     dst_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val
  h_no_alias_src_t : ∀ k1 k2 : Fin 32,
     src_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val
  h_no_alias_src_u : ∀ k1 k2 : Fin 32,
     src_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val
  h_no_alias_other_t : ∀ k1 k2 : Fin 32,
     other_addr + UInt64.ofNat k1.val ≠ t_addr + UInt64.ofNat k2.val
  h_no_alias_other_u : ∀ k1 k2 : Fin 32,
     other_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val
  h_no_alias_t_u : ∀ k1 k2 : Fin 32,
     t_addr + UInt64.ofNat k1.val ≠ u_addr + UInt64.ofNat k2.val

/-! ## §3  Per-block triples for the 12-block prefix

With the chain-step contracts in tree, each block's triple is a
one-liner applying the appropriate chain-step theorem. -/

/-- Block 2 chain-step shape: `z2 := ap² mod p_25519`.

    The body is `BignumInvP25519.sqr_step 0 OFF_z2 OFF_ap`; the
    caller supplies the body equality as `h_shape`. -/
theorem block2_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (a_val : Nat)
    (h_a_mem : memNat4 ap_addr s.mem = some a_val)
    (z2_addr : UInt64)
    (h_z2_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_addr + UInt64.ofNat k.val) = some b)
    (h_z2_addr_eq :
      BitVec.ofNat 64 z2_addr.toNat =
        BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2)
    (sqr_body : List InstrR)
    (h_shape : sqr_body = BignumInvP25519.sqr_step 0
      BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) sqr_body s = some s' ∧
      memNat4 z2_addr s'.mem = some ((a_val * a_val) % p_25519) ∧
      (∀ addr : UInt64,
        ¬ MemoryModel.range z2_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) := by
  -- OFF_ap = -1, OFF_z2 = 32 (≠ 0, ≠ -1), so block2 fits the
  -- generic-dst / negOne-src shape of `chain_sqr_step_correct`.
  apply chain_sqr_step_correct registry hAx s fuel
    op_addr ap_addr h_op h_ap
    ap_addr rfl a_val h_a_mem
    z2_addr h_z2_alloc 0 BignumInvP25519.OFF_z2
    (by simp [BignumInvP25519.OFF_z2])
    (by simp [BignumInvP25519.OFF_z2])
    h_z2_addr_eq sqr_body
  -- The shape hypothesis: rewrite OFF_ap = -1.
  rw [h_shape]
  show BignumInvP25519.sqr_step 0 BignumInvP25519.OFF_z2 BignumInvP25519.OFF_ap =
       BignumInvP25519.sqr_step 0 BignumInvP25519.OFF_z2 (-1)
  rfl

/-- Block 4 chain-step shape: `z11 := z9 · z2 mod p_25519`.

    Specialised to the all-generic-offsets case
    (`OFF_z11 = 96`, `OFF_z9 = 64`, `OFF_z2 = 32`, all ≠ {0, −1})
    that `BignumInvP25519.body` actually emits. -/
theorem block4_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z9_addr z2_addr z11_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z9_val z2_val : Nat)
    (h_z9_mem : memNat4 z9_addr s.mem = some z9_val)
    (h_z2_mem : memNat4 z2_addr s.mem = some z2_val)
    (h_z11_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z11_addr + UInt64.ofNat k.val) = some b)
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
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) mul_body s = some s' ∧
      memNat4 z11_addr s'.mem = some ((z9_val * z2_val) % p_25519) ∧
      (∀ addr : UInt64,
        ¬ MemoryModel.range z11_addr 32 addr →
        s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_mul_step_correct registry hAx s fuel
    op_addr ap_addr h_op h_ap
    z9_addr z2_addr z9_val z2_val h_z9_mem h_z2_mem
    z11_addr h_z11_alloc
    idx BignumInvP25519.OFF_z11 BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2
    (by simp [BignumInvP25519.OFF_z11])
    (by simp [BignumInvP25519.OFF_z11])
    (by simp [BignumInvP25519.OFF_z9])
    (by simp [BignumInvP25519.OFF_z9])
    (by simp [BignumInvP25519.OFF_z2])
    (by simp [BignumInvP25519.OFF_z2])
    h_z11_addr_eq h_z9_addr_eq h_z2_addr_eq mul_body h_shape

/-! ### Repeated-square-then-multiply blocks (3, 5–13)

Each of these 10 blocks is a `repeated_sqr_then_mul (n) src other →
dst` macro from `BignumInvP25519.body` (lines 2503-2539 of
`S2NBignumSSA.lean`). They share the axiom contract: running the
`rsm_body` produces `dst := src^(2^n) · other mod p_25519`. The chain
exponent table:

| Block | n   | Pattern                                                    |
|-------|-----|------------------------------------------------------------|
| 3     | 2   | `z9 := (z2)^(2^2) · ap`                                    |
| 5     | 1   | `z2_5_0 := (z11)^(2^1) · z9`                               |
| 6     | 5   | `z2_10_0 := (z2_5_0)^(2^5) · z2_5_0`                       |
| 7     | 10  | `z2_20_0 := (z2_10_0)^(2^10) · z2_10_0`                    |
| 8     | 20  | `z2_40_0 := (z2_20_0)^(2^20) · z2_20_0`                    |
| 9     | 10  | `z2_50_0 := (z2_40_0)^(2^10) · z2_10_0`                    |
| 10    | 50  | `z2_100_0 := (z2_50_0)^(2^50) · z2_50_0`                   |
| 11    | 100 | `z2_200_0 := (z2_100_0)^(2^100) · z2_100_0`                |
| 12    | 50  | `z2_250_0 := (z2_200_0)^(2^50) · z2_50_0`                  |
| 13    | 5   | `op := (z2_250_0)^(2^5) · z11`                             |

Each theorem is a one-line instantiation of
`chain_repeated_sqr_then_mul_correct` with the specific `n`, source,
other, and destination addresses. Variable naming (`z2_addr`,
`z9_addr`, etc.) tracks the chain's named intermediates. -/

/-- Block 3: `z9 := (z2)^(2^2) · ap mod p_25519` (2 sqr + 1 mul).
    Now discharged via `chain_repeated_sqr_then_mul_correct_other_negOne`
    (the otherOff = -1 specialised variant). -/
theorem block3_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_addr z9_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_val ap_val : Nat)
    (h_z2_mem : memNat4 z2_addr s.mem = some z2_val)
    (h_ap_mem : memNat4 ap_addr s.mem = some ap_val)
    (h_z9_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z9_addr + UInt64.ofNat k.val) = some b)
    (h_z9_addr_eq : BitVec.ofNat 64 z9_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z9)
    (h_z2_addr_eq : BitVec.ofNat 64 z2_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2)
    (scratch : RsmScratch s op_addr z9_addr z2_addr ap_addr)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul 1
        BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2
        BignumInvP25519.OFF_ap 2).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z9_addr s'.mem =
        some (((z2_val ^ (2^2)) * ap_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z9_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_other_negOne registry hAx s fuel
    op_addr ap_addr 2 (by decide) h_op h_ap
    z2_addr z9_addr z2_val ap_val h_z2_mem h_ap_mem
    h_z9_alloc 1 BignumInvP25519.OFF_z9 BignumInvP25519.OFF_z2
    (by decide) (by decide) (by decide) (by decide)
    h_z9_addr_eq h_z2_addr_eq
    scratch.t_addr scratch.u_addr
    scratch.h_t_addr_eq scratch.h_u_addr_eq scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u
    rsm_body h_shape

/-- Block 5: `z2_5_0 := (z11)^(2^1) · z9 mod p_25519` (1 sqr + 1 mul).
    `startIdx` is caller-supplied (depends on idx after blocks 3 + 4).
    Now discharged via `chain_repeated_sqr_then_mul_correct_generic`. -/
theorem block5_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z11_addr z9_addr z2_5_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z11_val z9_val : Nat)
    (h_z11_mem : memNat4 z11_addr s.mem = some z11_val)
    (h_z9_mem : memNat4 z9_addr s.mem = some z9_val)
    (h_z2_5_0_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_5_0_addr + UInt64.ofNat k.val) = some b)
    (h_z2_5_0_addr_eq : BitVec.ofNat 64 z2_5_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_5_0)
    (h_z11_addr_eq : BitVec.ofNat 64 z11_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z11)
    (h_z9_addr_eq : BitVec.ofNat 64 z9_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z9)
    (scratch : RsmScratch s op_addr z2_5_0_addr z11_addr z9_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_5_0 BignumInvP25519.OFF_z11
        BignumInvP25519.OFF_z9 1).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z2_5_0_addr s'.mem =
        some (((z11_val ^ (2^1)) * z9_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z2_5_0_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_generic registry hAx s fuel
    op_addr ap_addr 1 (by decide) h_op h_ap
    z11_addr z9_addr z2_5_0_addr z11_val z9_val h_z11_mem h_z9_mem
    h_z2_5_0_alloc startIdx BignumInvP25519.OFF_z2_5_0
    BignumInvP25519.OFF_z11 BignumInvP25519.OFF_z9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h_z2_5_0_addr_eq h_z11_addr_eq h_z9_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape

/-- Block 6: `z2_10_0 := (z2_5_0)^(2^5) · z2_5_0 mod p_25519` (5 sqr + 1 mul). -/
theorem block6_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_5_0_addr z2_10_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_5_0_val : Nat)
    (h_z2_5_0_mem : memNat4 z2_5_0_addr s.mem = some z2_5_0_val)
    (h_z2_10_0_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_10_0_addr + UInt64.ofNat k.val) = some b)
    (h_z2_10_0_addr_eq : BitVec.ofNat 64 z2_10_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_10_0)
    (h_z2_5_0_addr_eq : BitVec.ofNat 64 z2_5_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_5_0)
    (scratch : RsmScratch s op_addr z2_10_0_addr z2_5_0_addr z2_5_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_10_0 BignumInvP25519.OFF_z2_5_0
        BignumInvP25519.OFF_z2_5_0 5).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z2_10_0_addr s'.mem =
        some (((z2_5_0_val ^ (2^5)) * z2_5_0_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z2_10_0_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_generic registry hAx s fuel
    op_addr ap_addr 5 (by decide) h_op h_ap
    z2_5_0_addr z2_5_0_addr z2_10_0_addr z2_5_0_val z2_5_0_val
    h_z2_5_0_mem h_z2_5_0_mem h_z2_10_0_alloc startIdx
    BignumInvP25519.OFF_z2_10_0 BignumInvP25519.OFF_z2_5_0
    BignumInvP25519.OFF_z2_5_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h_z2_10_0_addr_eq h_z2_5_0_addr_eq h_z2_5_0_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape

/-- Block 7: `z2_20_0 := (z2_10_0)^(2^10) · z2_10_0 mod p_25519` (10 sqr + 1 mul). -/
theorem block7_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_10_0_addr z2_20_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_10_0_val : Nat)
    (h_z2_10_0_mem : memNat4 z2_10_0_addr s.mem = some z2_10_0_val)
    (h_z2_20_0_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_20_0_addr + UInt64.ofNat k.val) = some b)
    (h_z2_20_0_addr_eq : BitVec.ofNat 64 z2_20_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_20_0)
    (h_z2_10_0_addr_eq : BitVec.ofNat 64 z2_10_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_10_0)
    (scratch : RsmScratch s op_addr z2_20_0_addr z2_10_0_addr z2_10_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_20_0 BignumInvP25519.OFF_z2_10_0
        BignumInvP25519.OFF_z2_10_0 10).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z2_20_0_addr s'.mem =
        some (((z2_10_0_val ^ (2^10)) * z2_10_0_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z2_20_0_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_generic registry hAx s fuel
    op_addr ap_addr 10 (by decide) h_op h_ap
    z2_10_0_addr z2_10_0_addr z2_20_0_addr z2_10_0_val z2_10_0_val
    h_z2_10_0_mem h_z2_10_0_mem h_z2_20_0_alloc startIdx
    BignumInvP25519.OFF_z2_20_0 BignumInvP25519.OFF_z2_10_0
    BignumInvP25519.OFF_z2_10_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h_z2_20_0_addr_eq h_z2_10_0_addr_eq h_z2_10_0_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape

/-- Block 8: `z2_40_0 := (z2_20_0)^(2^20) · z2_20_0 mod p_25519` (20 sqr + 1 mul). -/
theorem block8_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_20_0_addr z2_40_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_20_0_val : Nat)
    (h_z2_20_0_mem : memNat4 z2_20_0_addr s.mem = some z2_20_0_val)
    (h_z2_40_0_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_40_0_addr + UInt64.ofNat k.val) = some b)
    (h_z2_40_0_addr_eq : BitVec.ofNat 64 z2_40_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_40_0)
    (h_z2_20_0_addr_eq : BitVec.ofNat 64 z2_20_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_20_0)
    (scratch : RsmScratch s op_addr z2_40_0_addr z2_20_0_addr z2_20_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_40_0 BignumInvP25519.OFF_z2_20_0
        BignumInvP25519.OFF_z2_20_0 20).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z2_40_0_addr s'.mem =
        some (((z2_20_0_val ^ (2^20)) * z2_20_0_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z2_40_0_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_generic registry hAx s fuel
    op_addr ap_addr 20 (by decide) h_op h_ap
    z2_20_0_addr z2_20_0_addr z2_40_0_addr z2_20_0_val z2_20_0_val
    h_z2_20_0_mem h_z2_20_0_mem h_z2_40_0_alloc startIdx
    BignumInvP25519.OFF_z2_40_0 BignumInvP25519.OFF_z2_20_0
    BignumInvP25519.OFF_z2_20_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h_z2_40_0_addr_eq h_z2_20_0_addr_eq h_z2_20_0_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape

/-- Block 9: `z2_50_0 := (z2_40_0)^(2^10) · z2_10_0 mod p_25519` (10 sqr + 1 mul). -/
theorem block9_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_40_0_addr z2_10_0_addr z2_50_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_40_0_val z2_10_0_val : Nat)
    (h_z2_40_0_mem : memNat4 z2_40_0_addr s.mem = some z2_40_0_val)
    (h_z2_10_0_mem : memNat4 z2_10_0_addr s.mem = some z2_10_0_val)
    (h_z2_50_0_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_50_0_addr + UInt64.ofNat k.val) = some b)
    (h_z2_50_0_addr_eq : BitVec.ofNat 64 z2_50_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_50_0)
    (h_z2_40_0_addr_eq : BitVec.ofNat 64 z2_40_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_40_0)
    (h_z2_10_0_addr_eq : BitVec.ofNat 64 z2_10_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_10_0)
    (scratch : RsmScratch s op_addr z2_50_0_addr z2_40_0_addr z2_10_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_50_0 BignumInvP25519.OFF_z2_40_0
        BignumInvP25519.OFF_z2_10_0 10).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z2_50_0_addr s'.mem =
        some (((z2_40_0_val ^ (2^10)) * z2_10_0_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z2_50_0_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_generic registry hAx s fuel
    op_addr ap_addr 10 (by decide) h_op h_ap
    z2_40_0_addr z2_10_0_addr z2_50_0_addr z2_40_0_val z2_10_0_val
    h_z2_40_0_mem h_z2_10_0_mem h_z2_50_0_alloc startIdx
    BignumInvP25519.OFF_z2_50_0 BignumInvP25519.OFF_z2_40_0
    BignumInvP25519.OFF_z2_10_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h_z2_50_0_addr_eq h_z2_40_0_addr_eq h_z2_10_0_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape

/-- Block 10: `z2_100_0 := (z2_50_0)^(2^50) · z2_50_0 mod p_25519` (50 sqr + 1 mul). -/
theorem block10_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_50_0_addr z2_100_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_50_0_val : Nat)
    (h_z2_50_0_mem : memNat4 z2_50_0_addr s.mem = some z2_50_0_val)
    (h_z2_100_0_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_100_0_addr + UInt64.ofNat k.val) = some b)
    (h_z2_100_0_addr_eq : BitVec.ofNat 64 z2_100_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_100_0)
    (h_z2_50_0_addr_eq : BitVec.ofNat 64 z2_50_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_50_0)
    (scratch : RsmScratch s op_addr z2_100_0_addr z2_50_0_addr z2_50_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_100_0 BignumInvP25519.OFF_z2_50_0
        BignumInvP25519.OFF_z2_50_0 50).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z2_100_0_addr s'.mem =
        some (((z2_50_0_val ^ (2^50)) * z2_50_0_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z2_100_0_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_generic registry hAx s fuel
    op_addr ap_addr 50 (by decide) h_op h_ap
    z2_50_0_addr z2_50_0_addr z2_100_0_addr z2_50_0_val z2_50_0_val
    h_z2_50_0_mem h_z2_50_0_mem h_z2_100_0_alloc startIdx
    BignumInvP25519.OFF_z2_100_0 BignumInvP25519.OFF_z2_50_0
    BignumInvP25519.OFF_z2_50_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h_z2_100_0_addr_eq h_z2_50_0_addr_eq h_z2_50_0_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape

/-- Block 11: `z2_200_0 := (z2_100_0)^(2^100) · z2_100_0 mod p_25519` (100 sqr + 1 mul). -/
theorem block11_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_100_0_addr z2_200_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_100_0_val : Nat)
    (h_z2_100_0_mem : memNat4 z2_100_0_addr s.mem = some z2_100_0_val)
    (h_z2_200_0_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_200_0_addr + UInt64.ofNat k.val) = some b)
    (h_z2_200_0_addr_eq : BitVec.ofNat 64 z2_200_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_200_0)
    (h_z2_100_0_addr_eq : BitVec.ofNat 64 z2_100_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_100_0)
    (scratch : RsmScratch s op_addr z2_200_0_addr z2_100_0_addr z2_100_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_200_0 BignumInvP25519.OFF_z2_100_0
        BignumInvP25519.OFF_z2_100_0 100).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z2_200_0_addr s'.mem =
        some (((z2_100_0_val ^ (2^100)) * z2_100_0_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z2_200_0_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_generic registry hAx s fuel
    op_addr ap_addr 100 (by decide) h_op h_ap
    z2_100_0_addr z2_100_0_addr z2_200_0_addr z2_100_0_val z2_100_0_val
    h_z2_100_0_mem h_z2_100_0_mem h_z2_200_0_alloc startIdx
    BignumInvP25519.OFF_z2_200_0 BignumInvP25519.OFF_z2_100_0
    BignumInvP25519.OFF_z2_100_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h_z2_200_0_addr_eq h_z2_100_0_addr_eq h_z2_100_0_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape

/-- Block 12: `z2_250_0 := (z2_200_0)^(2^50) · z2_50_0 mod p_25519` (50 sqr + 1 mul). -/
theorem block12_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_200_0_addr z2_50_0_addr z2_250_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_200_0_val z2_50_0_val : Nat)
    (h_z2_200_0_mem : memNat4 z2_200_0_addr s.mem = some z2_200_0_val)
    (h_z2_50_0_mem : memNat4 z2_50_0_addr s.mem = some z2_50_0_val)
    (h_z2_250_0_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (z2_250_0_addr + UInt64.ofNat k.val) = some b)
    (h_z2_250_0_addr_eq : BitVec.ofNat 64 z2_250_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_250_0)
    (h_z2_200_0_addr_eq : BitVec.ofNat 64 z2_200_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_200_0)
    (h_z2_50_0_addr_eq : BitVec.ofNat 64 z2_50_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_50_0)
    (scratch : RsmScratch s op_addr z2_250_0_addr z2_200_0_addr z2_50_0_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_z2_250_0 BignumInvP25519.OFF_z2_200_0
        BignumInvP25519.OFF_z2_50_0 50).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 z2_250_0_addr s'.mem =
        some (((z2_200_0_val ^ (2^50)) * z2_50_0_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range z2_250_0_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) :=
  chain_repeated_sqr_then_mul_correct_generic registry hAx s fuel
    op_addr ap_addr 50 (by decide) h_op h_ap
    z2_200_0_addr z2_50_0_addr z2_250_0_addr z2_200_0_val z2_50_0_val
    h_z2_200_0_mem h_z2_50_0_mem h_z2_250_0_alloc startIdx
    BignumInvP25519.OFF_z2_250_0 BignumInvP25519.OFF_z2_200_0
    BignumInvP25519.OFF_z2_50_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h_z2_250_0_addr_eq h_z2_200_0_addr_eq h_z2_50_0_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape

/-- Block 13: `op := (z2_250_0)^(2^5) · z11 mod p_25519` (5 sqr + 1 mul, terminal step).
    The destination is `op_addr` itself (`OFF_op = 0`).  Now discharged
    via `chain_repeated_sqr_then_mul_correct_dst_zero`. -/
theorem block13_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_250_0_addr z11_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_250_0_val z11_val : Nat)
    (h_z2_250_0_mem : memNat4 z2_250_0_addr s.mem = some z2_250_0_val)
    (h_z11_mem : memNat4 z11_addr s.mem = some z11_val)
    (h_op_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)
    (h_z2_250_0_addr_eq : BitVec.ofNat 64 z2_250_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_250_0)
    (h_z11_addr_eq : BitVec.ofNat 64 z11_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z11)
    (scratch : RsmScratch s op_addr op_addr z2_250_0_addr z11_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_op BignumInvP25519.OFF_z2_250_0
        BignumInvP25519.OFF_z11 5).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 op_addr s'.mem =
        some (((z2_250_0_val ^ (2^5)) * z11_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range op_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) := by
  -- block 13 has dstOff = OFF_op = 0; use the dst_zero specialised
  -- discharge.  Note: `OFF_op = 0` is a defn equality, so we can
  -- pass the shape with `OFF_op` and let the theorem see `0`.
  have h_shape' : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        0 BignumInvP25519.OFF_z2_250_0 BignumInvP25519.OFF_z11 5).fst := by
    rw [h_shape]
    rfl
  exact chain_repeated_sqr_then_mul_correct_dst_zero registry hAx s fuel
    op_addr ap_addr 5 (by decide) h_op h_ap
    z2_250_0_addr z11_addr z2_250_0_val z11_val
    h_z2_250_0_mem h_z11_mem h_op_alloc startIdx
    BignumInvP25519.OFF_z2_250_0 BignumInvP25519.OFF_z11
    (by decide) (by decide) (by decide) (by decide)
    h_z2_250_0_addr_eq h_z11_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape'

/-- Block 13b (p58 chain): `op := (z2_250_0)^(2^2) · ap mod p_25519`
    (2 sqr + 1 mul, terminal step of `BignumPowP58P25519.body`).
    The destination is `op_addr` (`OFF_op = 0`) AND the "other" is
    `ap_addr` (`OFF_ap = -1`).  Discharged via
    `chain_repeated_sqr_then_mul_correct_dst_zero_other_negOne`. -/
theorem block13b_correctness_via_axiom
    (registry : BignumRegistry)
    (hAx : MontmulCallFacts registry)
    (s : BignumState) (fuel : Nat)
    (op_addr ap_addr z2_250_0_addr : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 op_addr.toNat)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 ap_addr.toNat)
    (z2_250_0_val ap_val : Nat)
    (h_z2_250_0_mem : memNat4 z2_250_0_addr s.mem = some z2_250_0_val)
    (h_ap_mem : memNat4 ap_addr s.mem = some ap_val)
    (h_op_alloc : ∀ k : Fin 32,
      ∃ b, s.mem.loadByte (op_addr + UInt64.ofNat k.val) = some b)
    (h_z2_250_0_addr_eq : BitVec.ofNat 64 z2_250_0_addr.toNat =
       BitVec.ofNat 64 op_addr.toNat + BitVec.ofInt 64 BignumInvP25519.OFF_z2_250_0)
    (scratch : RsmScratch s op_addr op_addr z2_250_0_addr ap_addr)
    (startIdx : Nat)
    (rsm_body : List InstrR)
    (h_shape : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        BignumInvP25519.OFF_op BignumInvP25519.OFF_z2_250_0
        BignumInvP25519.OFF_ap 2).fst) :
    ∃ s' : BignumState,
      bignumExecFuel registry (fuel + 1) rsm_body s = some s' ∧
      memNat4 op_addr s'.mem =
        some (((z2_250_0_val ^ (2^2)) * ap_val) % p_25519) ∧
      (∀ addr : UInt64,
         ¬ MemoryModel.range op_addr 32 addr →
         ¬ MemoryModel.range scratch.t_addr 32 addr →
         ¬ MemoryModel.range scratch.u_addr 32 addr →
         s'.mem.loadByte addr = s.mem.loadByte addr) := by
  -- OFF_op = 0 and OFF_ap = -1, both defn-equalities.
  have h_shape' : rsm_body =
      (BignumInvP25519.repeated_sqr_then_mul startIdx
        0 BignumInvP25519.OFF_z2_250_0 (-1) 2).fst := by
    rw [h_shape]
    rfl
  exact chain_repeated_sqr_then_mul_correct_dst_zero_other_negOne
    registry hAx s fuel
    op_addr ap_addr 2 (by decide) h_op h_ap
    z2_250_0_addr z2_250_0_val ap_val
    h_z2_250_0_mem h_ap_mem h_op_alloc startIdx
    BignumInvP25519.OFF_z2_250_0
    (by decide) (by decide)
    h_z2_250_0_addr_eq
    scratch.t_addr scratch.u_addr scratch.h_t_addr_eq scratch.h_u_addr_eq
    scratch.h_t_alloc scratch.h_u_alloc
    scratch.h_no_alias_dst_t scratch.h_no_alias_dst_u
    scratch.h_no_alias_src_t scratch.h_no_alias_src_u
    scratch.h_no_alias_other_t scratch.h_no_alias_other_u
    scratch.h_no_alias_t_u rsm_body h_shape'

/-! ## §4  Trust set summary

This file holds **0 axioms**.  All chain-step lemmas and the rsm
correctness contract are proven theorems over the `MontmulCallFacts`
hypothesis.

Discharge inventory:
* §1 — `chain_sqr_step_correct`, `chain_mul_step_correct`,
  `chain_sqr_step_correct_generic`, plus the two specialised mul-step
  variants `chain_mul_step_correct_dst_zero` (block 13) and
  `chain_mul_step_correct_b_negOne` (block 3).
* §1e — `sqr_chain_loop_effect` (the ping-pong loop, ~250 LoC).
* §2.5a — `chain_repeated_sqr_then_mul_correct_generic`
  (blocks 5–12, ~150 LoC).
* §2.5b — `chain_repeated_sqr_then_mul_correct_dst_zero` (block 13).
* §2.5c — `chain_repeated_sqr_then_mul_correct_other_negOne` (block 3).

The discharge structure is uniform: each rsm decomposes as
`step0 ++ loop_body ++ mul_body`; chain_sqr_step → sqr_chain_loop_effect
→ chain_mul_step[_*]; forward-sequenced via `bignumExecFuel_append_join`;
algebraically closed by `pow_two_succ` + `Nat.mul_mod` + `Nat.pow_mod`.

Remaining external trust set: the `MontmulCallFacts` hypothesis
structure in `MontmulAxiom.lean` (the s2n-bignum verified primitive,
carried as an explicit per-registry hypothesis), plus the
deterministic semantics of `addrInit` and `bignumExecFuel` (proven
deterministic via §0a/§0b).
-/

end CatCrypt.Crypto.Jasmin.BignumHoare.ChainStepAxioms
