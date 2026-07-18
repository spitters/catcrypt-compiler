/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumHoare
import CatCrypt.Crypto.Jasmin.BignumHoare.ModWrap

set_option autoImplicit false

/-!
# `bignum_mod_p25519_4` — final operational + frame closure

Holds the three closure theorems for `bignum_mod_p25519_4`:

- `bodyComputesAlgoNat` — operational soundness (4-deep `cases` over the
  store chunk).
- `bodyPreservesInput` — frame property over the input region (32-byte
  preservation expansion).
- `bignum_mod_p25519_4_correct_universal` — the `BignumTriple` shape
  combining the two above with `algoNat_eq_specNat`.

## Why a separate module?

These three theorems have very large per-declaration elaboration peaks
(deep nested `cases` on `execInstr` outputs + a 32-element terminal
`simp only`). Co-located in `BignumHoare.lean` they pushed cumulative
elaboration past the 14 GiB host RAM ceiling. Splitting them into a
dependent module lets each elaborate in a fresh process so the term
cache resets between files.

This file extends the same `CatCrypt.Crypto.Jasmin.BignumHoare`
namespace as its parent — declarations are addressable as
`BignumHoare.bodyComputesAlgoNat` etc., the same path they had pre-split.
-/

namespace CatCrypt.Crypto.Jasmin.BignumHoare

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Hoare
open CatCrypt.Crypto.Jasmin.MemoryModel

/-- Operational soundness: under the precondition, executing the body
    computes the `algoNat` transformation on the input limbs into the
    output memory.

    Proof: decompose `body = pre31 ++ stores4` via `bignumExec_append`.
    Chunk 1 (pre31) preserves memory and the `op` register. Chunk 2
    (stores4) writes the four `oi` registers to `base_op + {0,8,16,24}`.
    The byte-memory bridging is fully closed via the helpers
    `load64Mem_store64_self` (matching read/store) and
    `load64Mem_store64_offset_const` (peel a disjoint-offset outer store).
    The algorithmic kernel — that the four `oi` registers hold limbs
    of `algoNat a_val` — is delegated to `pre_oi_values` above.

    Status: structural framing complete; the 4-read chain is fully
    closed (h_L3 via `load64Mem_store64_self`; h_L0, h_L1, h_L2 via
    iterated `load64Mem_store64_offset_const` then `_store64_self`).
    The kernel content has been factored out into `pre_oi_values` (which
    currently contains the only `sorry` in the file — the mvcgen Phase 3
    work item). -/
theorem bodyComputesAlgoNat
    (base_a base_op : UInt64)
    (_h_disj : MemoryModel.Disjoint
                (MemoryModel.range base_a 32)
                (MemoryModel.range base_op 32))
    (s s' : BignumState)
    (h_pre : bignumModPre base_a base_op s)
    (h_step : bignumStep S2NBignumSSA.BignumModP25519_4.body s s') :
    ∃ a_val, memNat4 base_a s.mem = some a_val ∧ a_val < 2 * (2^255 - 19) ∧
    memNat4 base_op s'.mem = some (S2NBignumSSA.BignumModP25519_4.algoNat a_val) := by
  -- The precondition gives us `a_val` and the bound directly.
  obtain ⟨h_ap, h_op, h_zero, a_val, h_load_a, h_a_bound, _h_op_alloc⟩ := h_pre
  refine ⟨a_val, h_load_a, h_a_bound, ?_⟩
  -- Decompose body = pre31 ++ stores4.
  unfold bignumStep at h_step
  let pre : List InstrR := S2NBignumSSA.BignumModP25519_4.body.take 31
  let stores : List InstrR := S2NBignumSSA.BignumModP25519_4.body.drop 31
  have h_split : S2NBignumSSA.BignumModP25519_4.body = pre ++ stores :=
    (List.take_append_drop 31 _).symm
  rw [h_split] at h_step
  obtain ⟨s_mid, h_pre_exec, h_st_exec⟩ :=
    BignumExec.bignumExec_append _ _ _ _ h_step
  -- Step 1: pre has no Lmem stores; mem preserved through pre.
  have h_pre_no_lmem_B :
      ∀ i ∈ pre, instrNotLmemB i = true := by
    show ∀ i ∈ S2NBignumSSA.BignumModP25519_4.body.take 31,
          instrNotLmemB i = true
    decide
  have h_pre_no_lmem :
      ∀ i ∈ pre, ∀ ws base off al sty rhs,
        i ≠ .Cassgn (.Lmem ws base off) al sty rhs :=
    fun i hi => instrNotLmem_of_B i (h_pre_no_lmem_B i hi)
  have h_s_mid_mem : s_mid.mem = s.mem :=
    body_no_lmem_mem_frame _ _ _ h_pre_exec h_pre_no_lmem
  -- Step 2: pre preserves regs "op", "ap", "zero".
  have h_pre_no_op_B : ∀ i ∈ pre, instrNoWriteB "op" i = true := by
    show ∀ i ∈ S2NBignumSSA.BignumModP25519_4.body.take 31,
          instrNoWriteB "op" i = true
    decide
  have h_pre_no_op : ∀ i ∈ pre, instrNoWrite "op" i :=
    fun i hi => instrNoWrite_of_B "op" i (h_pre_no_op_B i hi)
  have h_s_mid_op : s_mid.regs "op" = s.regs "op" :=
    bignumExec_regs_frame "op" _ _ _ h_pre_exec h_pre_no_op
  rw [h_op] at h_s_mid_op
  -- Step 3: identify stores chunk.
  have h_stores_eq : stores =
      [InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 0))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o0" }, gs := false }),
       InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 8))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o1" }, gs := false }),
       InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 16))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o2" }, gs := false }),
       InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 24))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o3" }, gs := false })] := rfl
  rw [h_stores_eq] at h_st_exec
  simp only [BignumExec.bignumExec] at h_st_exec
  -- Trace the 4 stores. Need to track o0..o3 register values plus s_mid.regs "op".
  cases h_step1 :
    BignumExec.execInstr s_mid
      (InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 0))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o0" }, gs := false }))
    with
  | none => rw [h_step1] at h_st_exec; simp at h_st_exec
  | some s2 =>
    rw [h_step1] at h_st_exec
    simp only at h_st_exec
    obtain ⟨h_s2_regs, v1, h_v1_eq, h_s2_mem⟩ :=
      execInstr_storeOp_const s_mid s2 (0 : Int) 0 (by decide) "o0" base_op
        h_s_mid_op h_step1
    cases h_step2 :
      BignumExec.execInstr s2
        (InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 8))
            .AT_none (.sword .U64)
            (.Pvar { gv := { var := S2NBignumSSA.v "o1" }, gs := false }))
      with
    | none => rw [h_step2] at h_st_exec; simp at h_st_exec
    | some s3 =>
      rw [h_step2] at h_st_exec
      simp only at h_st_exec
      have h_s2_op : s2.regs "op" = BitVec.ofNat 64 base_op.toNat := by
        rw [h_s2_regs]; exact h_s_mid_op
      obtain ⟨h_s3_regs, v2, h_v2_eq, h_s3_mem⟩ :=
        execInstr_storeOp_const s2 s3 (8 : Int) 8 (by decide) "o1" base_op
          h_s2_op h_step2
      cases h_step3 :
        BignumExec.execInstr s3
          (InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" }
                            (.Pconst 16))
              .AT_none (.sword .U64)
              (.Pvar { gv := { var := S2NBignumSSA.v "o2" }, gs := false }))
        with
      | none => rw [h_step3] at h_st_exec; simp at h_st_exec
      | some s4 =>
        rw [h_step3] at h_st_exec
        simp only at h_st_exec
        have h_s3_op : s3.regs "op" = BitVec.ofNat 64 base_op.toNat := by
          rw [h_s3_regs]; exact h_s2_op
        obtain ⟨h_s4_regs, v3, h_v3_eq, h_s4_mem⟩ :=
          execInstr_storeOp_const s3 s4 (16 : Int) 16 (by decide) "o2" base_op
            h_s3_op h_step3
        cases h_step4 :
          BignumExec.execInstr s4
            (InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" }
                              (.Pconst 24))
                .AT_none (.sword .U64)
                (.Pvar { gv := { var := S2NBignumSSA.v "o3" }, gs := false }))
          with
        | none => rw [h_step4] at h_st_exec; simp at h_st_exec
        | some s5 =>
          rw [h_step4] at h_st_exec
          simp only at h_st_exec
          have h_s4_op : s4.regs "op" = BitVec.ofNat 64 base_op.toNat := by
            rw [h_s4_regs]; exact h_s3_op
          obtain ⟨_h_s5_regs, v4, h_v4_eq, h_s5_mem⟩ :=
            execInstr_storeOp_const s4 s5 (24 : Int) 24 (by decide) "o3" base_op
              h_s4_op h_step4
          have h_s5_eq : s5 = s' := Option.some.inj h_st_exec
          subst h_s5_eq
          rw [show (base_op + UInt64.ofNat 0 : UInt64) = base_op + 0 from by simp]
              at h_s2_mem
          rw [show (base_op + UInt64.ofNat 8 : UInt64) = base_op + 8 from rfl]
              at h_s3_mem
          rw [show (base_op + UInt64.ofNat 16 : UInt64) = base_op + 16 from rfl]
              at h_s4_mem
          rw [show (base_op + UInt64.ofNat 24 : UInt64) = base_op + 24 from rfl]
              at h_s5_mem
          have h_s5_full : s5.mem =
              ((((s.mem.store64 (base_op + 0) v1).store64 (base_op + 8) v2).store64
                  (base_op + 16) v3).store64 (base_op + 24) v4) := by
            rw [h_s5_mem, h_s4_mem, h_s3_mem, h_s2_mem, h_s_mid_mem]
          have h_v1_o0 :
              v1 = UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o0").vname).toNat :=
            h_v1_eq
          have h_v2_o1 :
              v2 = UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o1").vname).toNat := by
            rw [h_v2_eq, h_s2_regs]
          have h_v3_o2 :
              v3 = UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o2").vname).toNat := by
            rw [h_v3_eq, h_s3_regs, h_s2_regs]
          have h_v4_o3 :
              v4 = UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o3").vname).toNat := by
            rw [h_v4_eq, h_s4_regs, h_s3_regs, h_s2_regs]
          have h_kernel :
              v1.toNat + v2.toNat * 2 ^ 64 + v3.toNat * 2 ^ 128 + v4.toNat * 2 ^ 192 =
                S2NBignumSSA.BignumModP25519_4.algoNat a_val := by
            rw [h_v1_o0, h_v2_o1, h_v3_o2, h_v4_o3]
            exact pre_oi_values base_a base_op s s_mid h_ap h_op h_zero
              a_val h_load_a h_a_bound h_pre_exec
          unfold memNat4
          rw [h_s5_full]
          have h_L3 : BignumExec.load64Mem
              ((((s.mem.store64 (base_op + 0) v1).store64 (base_op + 8) v2).store64
                (base_op + 16) v3).store64 (base_op + 24) v4) (base_op + 24) = some v4 :=
            load64Mem_store64_self _ _ _
          have h_eq_0 : (base_op + 0 : UInt64) = base_op + UInt64.ofNat 0 := rfl
          have h_eq_8 : (base_op + 8 : UInt64) = base_op + UInt64.ofNat 8 := rfl
          have h_eq_16 : (base_op + 16 : UInt64) = base_op + UInt64.ofNat 16 := rfl
          have h_eq_24 : (base_op + 24 : UInt64) = base_op + UInt64.ofNat 24 := rfl
          have h_L0 : BignumExec.load64Mem
              ((((s.mem.store64 (base_op + 0) v1).store64 (base_op + 8) v2).store64
                (base_op + 16) v3).store64 (base_op + 24) v4) (base_op + 0) = some v1 := by
            rw [h_eq_0, h_eq_8, h_eq_16, h_eq_24]
            rw [load64Mem_store64_offset_const _ _ 24 0 _ (Or.inl (by omega)) (by omega)]
            rw [load64Mem_store64_offset_const _ _ 16 0 _ (Or.inl (by omega)) (by omega)]
            rw [load64Mem_store64_offset_const _ _ 8 0 _ (Or.inl (by omega)) (by omega)]
            exact load64Mem_store64_self _ _ _
          have h_L1 : BignumExec.load64Mem
              ((((s.mem.store64 (base_op + 0) v1).store64 (base_op + 8) v2).store64
                (base_op + 16) v3).store64 (base_op + 24) v4) (base_op + 8) = some v2 := by
            rw [h_eq_0, h_eq_8, h_eq_16, h_eq_24]
            rw [load64Mem_store64_offset_const _ _ 24 8 _ (Or.inl (by omega)) (by omega)]
            rw [load64Mem_store64_offset_const _ _ 16 8 _ (Or.inl (by omega)) (by omega)]
            exact load64Mem_store64_self _ _ _
          have h_L2 : BignumExec.load64Mem
              ((((s.mem.store64 (base_op + 0) v1).store64 (base_op + 8) v2).store64
                (base_op + 16) v3).store64 (base_op + 24) v4) (base_op + 16) = some v3 := by
            rw [h_eq_0, h_eq_8, h_eq_16, h_eq_24]
            rw [load64Mem_store64_offset_const _ _ 24 16 _ (Or.inl (by omega)) (by omega)]
            exact load64Mem_store64_self _ _ _
          set MM := ((((s.mem.store64 (base_op + 0) v1).store64 (base_op + 8) v2).store64
                (base_op + 16) v3).store64 (base_op + 24) v4) with hMM
          have h_L0' : BignumExec.load64Mem MM base_op = some v1 := by
            have h_zero_eq : (base_op + 0 : UInt64) = base_op := by simp
            rw [← h_zero_eq]; exact h_L0
          rw [h_L0', h_L1, h_L2, h_L3]
          simp; exact h_kernel

/-- Frame property: the body only writes to the output region, so the
    input region's memory is unchanged. Combined with `h_load_a` from
    the precondition, this gives `memNat4 base_a s'.mem = some a_val`.

    Proof: decompose `body = pre ++ stores`, where `pre` (29 instructions)
    has no `Lmem` writes, so `body_no_lmem_mem_frame` gives mem
    preservation through `pre`. The 4 stores all target `base_op + k`
    for `k ∈ {0, 8, 16, 24}` (since the `op` register is preserved by
    `bignumExec_regs_frame`); each affects only the 8 bytes at that
    offset. Then `range32_disjoint_byte_ne` (via `h_disj`) shows that
    each of the 32 bytes read by `memNat4 base_a` is outside the
    write footprint, so its value is preserved. -/
theorem bodyPreservesInput
    (base_a base_op : UInt64)
    (h_disj : MemoryModel.Disjoint
                (MemoryModel.range base_a 32)
                (MemoryModel.range base_op 32))
    (s s' : BignumState)
    (h_pre : bignumModPre base_a base_op s)
    (h_step : bignumStep S2NBignumSSA.BignumModP25519_4.body s s') :
    memNat4 base_a s'.mem = memNat4 base_a s.mem := by
  obtain ⟨_h_ap, h_op, _h_zero, _, _, _, _⟩ := h_pre
  unfold bignumStep at h_step
  let pre : List InstrR := S2NBignumSSA.BignumModP25519_4.body.take 31
  let stores : List InstrR := S2NBignumSSA.BignumModP25519_4.body.drop 31
  have h_split : S2NBignumSSA.BignumModP25519_4.body = pre ++ stores :=
    (List.take_append_drop 31 _).symm
  rw [h_split] at h_step
  obtain ⟨s1, h_pre_exec, h_st_exec⟩ :=
    BignumExec.bignumExec_append _ _ _ _ h_step
  have h_pre_no_lmem_B :
      ∀ i ∈ pre, instrNotLmemB i = true := by
    show ∀ i ∈ S2NBignumSSA.BignumModP25519_4.body.take 31,
          instrNotLmemB i = true
    decide
  have h_pre_no_lmem :
      ∀ i ∈ pre, ∀ ws base off al sty rhs,
        i ≠ .Cassgn (.Lmem ws base off) al sty rhs :=
    fun i hi => instrNotLmem_of_B i (h_pre_no_lmem_B i hi)
  have h_s1_mem : s1.mem = s.mem :=
    body_no_lmem_mem_frame _ _ _ h_pre_exec h_pre_no_lmem
  have h_pre_no_op_B : ∀ i ∈ pre, instrNoWriteB "op" i = true := by
    show ∀ i ∈ S2NBignumSSA.BignumModP25519_4.body.take 31,
          instrNoWriteB "op" i = true
    decide
  have h_pre_no_op : ∀ i ∈ pre, instrNoWrite "op" i :=
    fun i hi => instrNoWrite_of_B "op" i (h_pre_no_op_B i hi)
  have h_s1_op : s1.regs "op" = s.regs "op" :=
    bignumExec_regs_frame "op" _ _ _ h_pre_exec h_pre_no_op
  rw [h_op] at h_s1_op
  have h_stores_eq : stores =
      [InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 0))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o0" }, gs := false }),
       InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 8))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o1" }, gs := false }),
       InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 16))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o2" }, gs := false }),
       InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 24))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o3" }, gs := false })] := rfl
  rw [h_stores_eq] at h_st_exec
  simp only [BignumExec.bignumExec] at h_st_exec
  cases h_step1 :
    BignumExec.execInstr s1
      (InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 0))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v "o0" }, gs := false }))
      with
  | none => rw [h_step1] at h_st_exec; simp at h_st_exec
  | some s2 =>
    rw [h_step1] at h_st_exec
    simp only at h_st_exec
    obtain ⟨h_s2_regs, v1, _, h_s2_mem⟩ :=
      execInstr_storeOp_const s1 s2 (0 : Int) 0 (by decide) "o0" base_op
        h_s1_op h_step1
    cases h_step2 :
      BignumExec.execInstr s2
        (InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" } (.Pconst 8))
            .AT_none (.sword .U64)
            (.Pvar { gv := { var := S2NBignumSSA.v "o1" }, gs := false }))
        with
    | none => rw [h_step2] at h_st_exec; simp at h_st_exec
    | some s3 =>
      rw [h_step2] at h_st_exec
      simp only at h_st_exec
      have h_s2_op : s2.regs "op" = BitVec.ofNat 64 base_op.toNat := by
        rw [h_s2_regs]; exact h_s1_op
      obtain ⟨h_s3_regs, v2, _, h_s3_mem⟩ :=
        execInstr_storeOp_const s2 s3 (8 : Int) 8 (by decide) "o1" base_op
          h_s2_op h_step2
      cases h_step3 :
        BignumExec.execInstr s3
          (InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" }
                            (.Pconst 16))
              .AT_none (.sword .U64)
              (.Pvar { gv := { var := S2NBignumSSA.v "o2" }, gs := false }))
          with
      | none => rw [h_step3] at h_st_exec; simp at h_st_exec
      | some s4 =>
        rw [h_step3] at h_st_exec
        simp only at h_st_exec
        have h_s3_op : s3.regs "op" = BitVec.ofNat 64 base_op.toNat := by
          rw [h_s3_regs]; exact h_s2_op
        obtain ⟨h_s4_regs, v3, _, h_s4_mem⟩ :=
          execInstr_storeOp_const s3 s4 (16 : Int) 16 (by decide) "o2" base_op
            h_s3_op h_step3
        cases h_step4 :
          BignumExec.execInstr s4
            (InstrR.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" }
                              (.Pconst 24))
                .AT_none (.sword .U64)
                (.Pvar { gv := { var := S2NBignumSSA.v "o3" }, gs := false }))
            with
        | none => rw [h_step4] at h_st_exec; simp at h_st_exec
        | some s5 =>
          rw [h_step4] at h_st_exec
          simp only at h_st_exec
          have h_s4_op : s4.regs "op" = BitVec.ofNat 64 base_op.toNat := by
            rw [h_s4_regs]; exact h_s3_op
          obtain ⟨_h_s5_regs, v4, _, h_s5_mem⟩ :=
            execInstr_storeOp_const s4 s5 (24 : Int) 24 (by decide) "o3" base_op
              h_s4_op h_step4
          have h_s5_eq : s5 = s' := Option.some.inj h_st_exec
          subst h_s5_eq
          have h_byte_pres : ∀ a : UInt64,
              ¬ MemoryModel.range base_op 32 a →
              s5.mem.loadByte a = s.mem.loadByte a := by
            intro a hOut
            rw [h_s5_mem, h_s4_mem, h_s3_mem, h_s2_mem, h_s1_mem]
            rw [store64_loadByte_outside_op _ base_op 24 (by omega) v4 a hOut]
            rw [store64_loadByte_outside_op _ base_op 16 (by omega) v3 a hOut]
            rw [store64_loadByte_outside_op _ base_op 8 (by omega) v2 a hOut]
            rw [store64_loadByte_outside_op _ base_op 0 (by omega) v1 a hOut]
          have h_a_outside : ∀ k : Nat, k < 32 →
              ¬ MemoryModel.range base_op 32 (base_a + UInt64.ofNat k) := by
            intro k hk h_in_op
            obtain ⟨k', hk'_lt, hk'_eq⟩ := h_in_op
            apply MemoryModel.range_disjoint_byte_ne
                    base_a base_op 32 h_disj k k' hk hk'_lt
            exact hk'_eq
          unfold memNat4 BignumExec.load64Mem
          have h_pres_at : ∀ k : Nat, k < 32 →
              s5.mem.loadByte (base_a + UInt64.ofNat k) =
                s.mem.loadByte (base_a + UInt64.ofNat k) :=
            fun k hk => h_byte_pres _ (h_a_outside k hk)
          have e0 : s5.mem.loadByte base_a = s.mem.loadByte base_a := by
            have := h_pres_at 0 (by omega); simpa using this
          have e1 : s5.mem.loadByte (base_a + 1) =
                    s.mem.loadByte (base_a + 1) := h_pres_at 1 (by omega)
          have e2 : s5.mem.loadByte (base_a + 2) =
                    s.mem.loadByte (base_a + 2) := h_pres_at 2 (by omega)
          have e3 : s5.mem.loadByte (base_a + 3) =
                    s.mem.loadByte (base_a + 3) := h_pres_at 3 (by omega)
          have e4 : s5.mem.loadByte (base_a + 4) =
                    s.mem.loadByte (base_a + 4) := h_pres_at 4 (by omega)
          have e5 : s5.mem.loadByte (base_a + 5) =
                    s.mem.loadByte (base_a + 5) := h_pres_at 5 (by omega)
          have e6 : s5.mem.loadByte (base_a + 6) =
                    s.mem.loadByte (base_a + 6) := h_pres_at 6 (by omega)
          have e7 : s5.mem.loadByte (base_a + 7) =
                    s.mem.loadByte (base_a + 7) := h_pres_at 7 (by omega)
          have e8 : s5.mem.loadByte (base_a + 8) =
                    s.mem.loadByte (base_a + 8) := by
            have := h_pres_at 8 (by omega); simpa using this
          have e9 : s5.mem.loadByte (base_a + 8 + 1) =
                    s.mem.loadByte (base_a + 8 + 1) := by
            have := h_pres_at 9 (by omega)
            have h9 : base_a + 8 + 1 = base_a + UInt64.ofNat 9 := by ext; simp [UInt64.toNat_add]
            rw [h9]; exact this
          have e10 : s5.mem.loadByte (base_a + 8 + 2) =
                     s.mem.loadByte (base_a + 8 + 2) := by
            have := h_pres_at 10 (by omega)
            have h10 : base_a + 8 + 2 = base_a + UInt64.ofNat 10 := by ext; simp [UInt64.toNat_add]
            rw [h10]; exact this
          have e11 : s5.mem.loadByte (base_a + 8 + 3) =
                     s.mem.loadByte (base_a + 8 + 3) := by
            have := h_pres_at 11 (by omega)
            have h11 : base_a + 8 + 3 = base_a + UInt64.ofNat 11 := by ext; simp [UInt64.toNat_add]
            rw [h11]; exact this
          have e12 : s5.mem.loadByte (base_a + 8 + 4) =
                     s.mem.loadByte (base_a + 8 + 4) := by
            have := h_pres_at 12 (by omega)
            have h12 : base_a + 8 + 4 = base_a + UInt64.ofNat 12 := by ext; simp [UInt64.toNat_add]
            rw [h12]; exact this
          have e13 : s5.mem.loadByte (base_a + 8 + 5) =
                     s.mem.loadByte (base_a + 8 + 5) := by
            have := h_pres_at 13 (by omega)
            have h13 : base_a + 8 + 5 = base_a + UInt64.ofNat 13 := by ext; simp [UInt64.toNat_add]
            rw [h13]; exact this
          have e14 : s5.mem.loadByte (base_a + 8 + 6) =
                     s.mem.loadByte (base_a + 8 + 6) := by
            have := h_pres_at 14 (by omega)
            have h14 : base_a + 8 + 6 = base_a + UInt64.ofNat 14 := by ext; simp [UInt64.toNat_add]
            rw [h14]; exact this
          have e15 : s5.mem.loadByte (base_a + 8 + 7) =
                     s.mem.loadByte (base_a + 8 + 7) := by
            have := h_pres_at 15 (by omega)
            have h15 : base_a + 8 + 7 = base_a + UInt64.ofNat 15 := by ext; simp [UInt64.toNat_add]
            rw [h15]; exact this
          have e16 : s5.mem.loadByte (base_a + 16) =
                     s.mem.loadByte (base_a + 16) := by
            have := h_pres_at 16 (by omega); simpa using this
          have e17 : s5.mem.loadByte (base_a + 16 + 1) =
                     s.mem.loadByte (base_a + 16 + 1) := by
            have := h_pres_at 17 (by omega)
            have h : base_a + 16 + 1 = base_a + UInt64.ofNat 17 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e18 : s5.mem.loadByte (base_a + 16 + 2) =
                     s.mem.loadByte (base_a + 16 + 2) := by
            have := h_pres_at 18 (by omega)
            have h : base_a + 16 + 2 = base_a + UInt64.ofNat 18 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e19 : s5.mem.loadByte (base_a + 16 + 3) =
                     s.mem.loadByte (base_a + 16 + 3) := by
            have := h_pres_at 19 (by omega)
            have h : base_a + 16 + 3 = base_a + UInt64.ofNat 19 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e20 : s5.mem.loadByte (base_a + 16 + 4) =
                     s.mem.loadByte (base_a + 16 + 4) := by
            have := h_pres_at 20 (by omega)
            have h : base_a + 16 + 4 = base_a + UInt64.ofNat 20 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e21 : s5.mem.loadByte (base_a + 16 + 5) =
                     s.mem.loadByte (base_a + 16 + 5) := by
            have := h_pres_at 21 (by omega)
            have h : base_a + 16 + 5 = base_a + UInt64.ofNat 21 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e22 : s5.mem.loadByte (base_a + 16 + 6) =
                     s.mem.loadByte (base_a + 16 + 6) := by
            have := h_pres_at 22 (by omega)
            have h : base_a + 16 + 6 = base_a + UInt64.ofNat 22 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e23 : s5.mem.loadByte (base_a + 16 + 7) =
                     s.mem.loadByte (base_a + 16 + 7) := by
            have := h_pres_at 23 (by omega)
            have h : base_a + 16 + 7 = base_a + UInt64.ofNat 23 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e24 : s5.mem.loadByte (base_a + 24) =
                     s.mem.loadByte (base_a + 24) := by
            have := h_pres_at 24 (by omega); simpa using this
          have e25 : s5.mem.loadByte (base_a + 24 + 1) =
                     s.mem.loadByte (base_a + 24 + 1) := by
            have := h_pres_at 25 (by omega)
            have h : base_a + 24 + 1 = base_a + UInt64.ofNat 25 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e26 : s5.mem.loadByte (base_a + 24 + 2) =
                     s.mem.loadByte (base_a + 24 + 2) := by
            have := h_pres_at 26 (by omega)
            have h : base_a + 24 + 2 = base_a + UInt64.ofNat 26 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e27 : s5.mem.loadByte (base_a + 24 + 3) =
                     s.mem.loadByte (base_a + 24 + 3) := by
            have := h_pres_at 27 (by omega)
            have h : base_a + 24 + 3 = base_a + UInt64.ofNat 27 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e28 : s5.mem.loadByte (base_a + 24 + 4) =
                     s.mem.loadByte (base_a + 24 + 4) := by
            have := h_pres_at 28 (by omega)
            have h : base_a + 24 + 4 = base_a + UInt64.ofNat 28 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e29 : s5.mem.loadByte (base_a + 24 + 5) =
                     s.mem.loadByte (base_a + 24 + 5) := by
            have := h_pres_at 29 (by omega)
            have h : base_a + 24 + 5 = base_a + UInt64.ofNat 29 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e30 : s5.mem.loadByte (base_a + 24 + 6) =
                     s.mem.loadByte (base_a + 24 + 6) := by
            have := h_pres_at 30 (by omega)
            have h : base_a + 24 + 6 = base_a + UInt64.ofNat 30 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          have e31 : s5.mem.loadByte (base_a + 24 + 7) =
                     s.mem.loadByte (base_a + 24 + 7) := by
            have := h_pres_at 31 (by omega)
            have h : base_a + 24 + 7 = base_a + UInt64.ofNat 31 := by ext; simp [UInt64.toNat_add]
            rw [h]; exact this
          simp only [bind, Option.bind, e0, e1, e2, e3, e4, e5, e6, e7, e8,
                     e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
                     e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31]

/-- Universal correctness for `bignum_mod_p25519_4`.

    Combines the operational lemma (`bodyComputesAlgoNat` — the body
    computes `algoNat (memNat4 base_a s.mem)` into `memNat4 base_op s'.mem`),
    the frame lemma (`bodyPreservesInput` — input region unchanged),
    and the algebraic core (`S2NBignumSSA.BignumModP25519_4.algoNat_eq_specNat`
    — `algoNat = specNat = (· % p)` under `a < 2p`).

    The `BignumTriple` shape: under the precondition (input < 2p,
    output range allocated, input/output ranges disjoint), executing
    the body lands in a state whose output region holds the canonical
    reduction of the input.

    Status: structural skeleton complete; final closure depends on
    `bodyComputesAlgoNat` and `bodyPreservesInput`, which discharge
    to per-instruction VCs (the mvcgen-plugin watch-list item). -/
theorem bignum_mod_p25519_4_correct_universal
    (base_a base_op : UInt64)
    (h_disj : MemoryModel.Disjoint
                (MemoryModel.range base_a 32)
                (MemoryModel.range base_op 32)) :
    BignumTriple
      (bignumModPre base_a base_op)
      S2NBignumSSA.BignumModP25519_4.body
      (bignumModPost base_a base_op) := by
  intro s s' h_pre h_step
  obtain ⟨a_val, h_load_a, h_a_bound, h_load_op⟩ :=
    bodyComputesAlgoNat base_a base_op h_disj s s' h_pre h_step
  have h_input_preserved : memNat4 base_a s'.mem = memNat4 base_a s.mem :=
    bodyPreservesInput base_a base_op h_disj s s' h_pre h_step
  refine ⟨a_val, ?_, S2NBignumSSA.BignumModP25519_4.algoNat a_val, h_load_op, ?_⟩
  · rw [h_input_preserved]; exact h_load_a
  · have := S2NBignumSSA.BignumModP25519_4.algoNat_eq_specNat a_val h_a_bound
    simp [S2NBignumSSA.BignumModP25519_4.specNat] at this
    exact this

end CatCrypt.Crypto.Jasmin.BignumHoare
