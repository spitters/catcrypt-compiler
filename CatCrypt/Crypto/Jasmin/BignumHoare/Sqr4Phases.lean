/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumExec
import CatCrypt.Crypto.Jasmin.BignumStepSpecs
import CatCrypt.Crypto.Jasmin.BignumHoare
import CatCrypt.Crypto.Jasmin.Hoare
import CatCrypt.Crypto.Jasmin.S2NBignumSSA
import CatCrypt.Crypto.Jasmin.BignumHoare.Sqr4Algebra

set_option autoImplicit false

/-!
# `bignum_sqr_4` Phase Triples

The four Hoare triples that decompose the 63-instruction
`BignumSqr4.body` into Init / Phase A / Phase B / Phase C chunks, plus
the functional `sqr_4_memory_filled` glue and the algebraic
`sqr_4_correct_with_chain_witnesses` consumer.

All four phase triples go through the `BignumStepSpecs` `@[spec]`
route: the body slice is unrolled with `bignumExecM_cons`/`_nil`,
`mvcgen` composes the Q-parametric per-instruction-shape specs, and
the single residual VC is closed by the `setReg`/`storeMem` projection
simp set (plus, for Phase C, the `load64Mem`-through-`store64` peels).
This keeps every declaration within default heartbeats — no raw
`stepInstrM`/`execInstr` unfolding inside `mvcgen`.

Body shape is the ADCX/ADOX dual-chain (mirroring s2n-bignum's
`bignum_sqr_4_8.S`), so the slice indices use `take 13 / drop 13 …`
matching the init-with-cf=of=0 phase length.

## Contents

- `sqr4_init_triple`, `sqr4_phaseA_triple`, `sqr4_phaseB_triple`,
  `sqr4_phaseC_triple` — the four phase Hoare triples (`@[spec]`-route,
  Qed).
- `sqr_4_correct_with_chain_witnesses` — algebraic correctness given
  user-supplied chain witnesses (closes via `sqr4_chain_eq_square`).
- `sqr_4_memory_filled` — functional wrapper composing the four phase
  triples through `bignumExec_append` + `triple_apply_run` (Qed).
-/

namespace CatCrypt.Crypto.Jasmin.BignumHoare

open Std.Do
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Hoare

/-! ### `@[spec]`-route VC helpers

Local copies of `BignumStepSpecs.setReg_regs` / `setReg_mem` /
`load_addr_bridge` (same statements; keeping them here lets the
per-load VC simp set live next to its consumer). -/

private theorem sqr_setReg_regs (s : BignumState) (x y : String) (v : BitVec 64) :
    (BignumExec.setReg s x v).regs y = if y = x then v else s.regs y := rfl

private theorem sqr_setReg_mem (s : BignumState) (x : String) (v : BitVec 64) :
    (BignumExec.setReg s x v).mem = s.mem := rfl

private theorem sqr_load_addr_bridge (b : UInt64) (k : BitVec 64) :
    UInt64.ofNat ((BitVec.ofNat 64 b.toNat + k).toNat)
      = b + UInt64.ofNat k.toNat := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, BitVec.toNat_add, Nat.add_mod]

private theorem sqr_ofNat_toNat (a : UInt64) :
    BitVec.ofNat 64 a.toNat = a.toBitVec := by
  rw [show a.toNat = a.toBitVec.toNat from rfl, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]

/-- `storeMem` does not touch the register file. -/
private theorem sqr_storeMem_regs (s : BignumState) (a v : UInt64)
    (y : String) : (BignumExec.storeMem s a v).regs y = s.regs y := rfl

/-- `storeMem` is `Mem.store64` on the memory component. -/
private theorem sqr_storeMem_mem (s : BignumState) (a v : UInt64) :
    (BignumExec.storeMem s a v).mem = s.mem.store64 a v := rfl

/-! ### Phase-C memory peels

The Phase C VC reads 8 words back through the 8-store chain at
`base_op + {0, 8, …, 56}`. `sqr_load64Mem_store64_skip` peels a
disjoint-constant-offset store (wrapping `load64Mem_store64_offset_const`
from `BignumHoare.lean` in the `base + UInt64.ofNat k` normal form the
`@[spec]`-route simp produces); the `_skip0` / `_self0` variants handle
the offset-0 read whose address is the bare `base_op`. -/

private theorem sqr_load64Mem_store64_skip (m : MemoryModel.Mem)
    (base : UInt64) (ks kr : Nat) (v : UInt64)
    (h_disj : kr + 8 ≤ ks ∨ ks + 8 ≤ kr)
    (h_bound : ks + 8 ≤ 256 ∧ kr + 8 ≤ 256) :
    BignumExec.load64Mem (m.store64 (base + UInt64.ofNat ks) v)
        (base + UInt64.ofNat kr)
      = BignumExec.load64Mem m (base + UInt64.ofNat kr) :=
  load64Mem_store64_offset_const m base ks kr v h_disj h_bound

private theorem sqr_load64Mem_store64_skip0 (m : MemoryModel.Mem)
    (base : UInt64) (ks : Nat) (v : UInt64)
    (h_lo : 8 ≤ ks) (h_hi : ks + 8 ≤ 256) :
    BignumExec.load64Mem (m.store64 (base + UInt64.ofNat ks) v) base
      = BignumExec.load64Mem m base := by
  have h := load64Mem_store64_offset_const m base ks 0 v
    (Or.inl (by omega)) ⟨h_hi, by omega⟩
  simpa [show (UInt64.ofNat 0 : UInt64) = 0 from rfl] using h

private theorem sqr_load64Mem_store64_self0 (m : MemoryModel.Mem)
    (base : UInt64) (v : UInt64) :
    BignumExec.load64Mem (m.store64 (base + UInt64.ofNat 0) v) base
      = some v := by
  rw [show base + UInt64.ofNat 0 = base from by
        simp [show (UInt64.ofNat 0 : UInt64) = 0 from rfl]]
  exact load64Mem_store64_self m base v

/-! ### Phase 4 — `bignum_sqr_4` Init phase Triple

First chunk of `bignum_sqr_4`'s chunked Triple proof: the 13-instruction
init phase (zero, 4 loads, 6 d_k = 0, cf/of init). Postcondition pins
regs zero, a0..a3 (loaded values), d_k_0 = 0 for k ∈ 1..6, and
cf = of = 0 (set up for the ADCX/ADOX dual chain in Phase A). -/

private theorem sqr4_init_triple
    (base_a base_op : UInt64) (a0 a1 a2 a3 : UInt64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              (S2NBignumSSA.BignumSqr4.body.take 13))
      (fun s => ⌜s.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
                 s.regs "op" = BitVec.ofNat 64 base_op.toNat ∧
                 BignumExec.load64Mem s.mem base_a = some a0 ∧
                 BignumExec.load64Mem s.mem (base_a + 8) = some a1 ∧
                 BignumExec.load64Mem s.mem (base_a + 16) = some a2 ∧
                 BignumExec.load64Mem s.mem (base_a + 24) = some a3⌝)
      (⇓ _ => fun s_mid =>
        ⌜s_mid.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
         s_mid.regs "op" = BitVec.ofNat 64 base_op.toNat ∧
         s_mid.regs "zero" = 0 ∧
         s_mid.regs "a0" = a0.toBitVec ∧
         s_mid.regs "a1" = a1.toBitVec ∧
         s_mid.regs "a2" = a2.toBitVec ∧
         s_mid.regs "a3" = a3.toBitVec ∧
         s_mid.regs "d1_0" = 0 ∧
         s_mid.regs "d2_0" = 0 ∧
         s_mid.regs "d3_0" = 0 ∧
         s_mid.regs "d4_0" = 0 ∧
         s_mid.regs "d5_0" = 0 ∧
         s_mid.regs "d6_0" = 0 ∧
         s_mid.regs "cf"   = 0 ∧
         s_mid.regs "of"   = 0⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumSqr4.body, List.take,
             BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil]
  mvcgen
  rename_i s h_pre
  obtain ⟨h_ap, h_op, h_a0, h_a1, h_a2, h_a3⟩ := h_pre
  -- One `simp only` round per load64: strip the `setReg` frame off the
  -- address/memory, bridge the BitVec address computation back to
  -- `base_a + k`, and resolve the load via the precondition hypothesis;
  -- then `mspec` symbolically executes up to the next load.
  simp only [sqr_setReg_regs, sqr_setReg_mem,
             String.reduceEq, reduceIte, h_ap, h_a0,
             sqr_load_addr_bridge,
             show UInt64.ofNat (BitVec.ofInt 64 0).toNat = 0 from rfl,
             UInt64.add_zero]
  mspec BignumStepSpecs.load64_spec
  simp only [sqr_setReg_regs, sqr_setReg_mem,
             String.reduceEq, reduceIte, h_ap, h_a1,
             sqr_load_addr_bridge,
             show UInt64.ofNat (BitVec.ofInt 64 8).toNat = 8 from rfl]
  mspec BignumStepSpecs.load64_spec
  simp only [sqr_setReg_regs, sqr_setReg_mem,
             String.reduceEq, reduceIte, h_ap, h_a2,
             sqr_load_addr_bridge,
             show UInt64.ofNat (BitVec.ofInt 64 16).toNat = 16 from rfl]
  mspec BignumStepSpecs.load64_spec
  simp only [sqr_setReg_regs, sqr_setReg_mem,
             String.reduceEq, reduceIte, h_ap, h_a3,
             sqr_load_addr_bridge,
             show UInt64.ofNat (BitVec.ofInt 64 24).toNat = 24 from rfl]
  mspec BignumStepSpecs.assignConst_spec
  mspec BignumStepSpecs.assignConst_spec
  mspec BignumStepSpecs.assignConst_spec
  mspec BignumStepSpecs.assignConst_spec
  mspec BignumStepSpecs.assignConst_spec
  mspec BignumStepSpecs.assignConst_spec
  mspec BignumStepSpecs.assignConst_spec
  mspec BignumStepSpecs.assignConst_spec
  mvcgen
  simp only [sqr_setReg_regs, String.reduceEq, reduceIte, h_ap, h_op,
             sqr_ofNat_toNat, show BitVec.ofInt 64 0 = 0 from rfl,
             and_self]

/-! ### Phase 4 — `bignum_sqr_4` Phase C Triple (diagonals + stores)

Phase C: 23 instructions (4 loadRdx + 4 mulx + 8 store64 + 7 add/adc).
Stores are interleaved with computation so the body slice is the
canonical "compute-and-store" pattern.

Postcondition: 8 memory values at op+0..op+56 exist and were stored
by the chain. The algebraic content (= a²) is added externally via
`sqr4_chain_eq_square` once the mulx hypotheses are in scope. -/

private theorem sqr4_phaseC_triple
    (base_op : UInt64) (a0 a1 a2 a3 e1 e2 e3 e4 e5 e6 : BitVec 64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              ((S2NBignumSSA.BignumSqr4.body.drop 40).take 23))
      (fun s => ⌜s.regs "op" = BitVec.ofNat 64 base_op.toNat ∧
                 s.regs "zero" = 0 ∧
                 s.regs "a0" = a0 ∧ s.regs "a1" = a1 ∧
                 s.regs "a2" = a2 ∧ s.regs "a3" = a3 ∧
                 s.regs "e1" = e1 ∧ s.regs "e2" = e2 ∧ s.regs "e3" = e3 ∧
                 s.regs "e4" = e4 ∧ s.regs "e5" = e5 ∧ s.regs "e6" = e6⌝)
      (⇓ _ => fun s_mid =>
        let s0h := (BignumExec.mulx a0 a0).1
        let s0l := (BignumExec.mulx a0 a0).2
        let s1h := (BignumExec.mulx a1 a1).1
        let s1l := (BignumExec.mulx a1 a1).2
        let s2h := (BignumExec.mulx a2 a2).1
        let s2l := (BignumExec.mulx a2 a2).2
        let s3h := (BignumExec.mulx a3 a3).1
        let s3l := (BignumExec.mulx a3 a3).2
        let cf01 := (BignumExec.addCarry e1 s0h).1
        let o1 := (BignumExec.addCarry e1 s0h).2
        let cf12 := (BignumExec.addCarryIn e2 s1l cf01).1
        let o2 := (BignumExec.addCarryIn e2 s1l cf01).2
        let cf23 := (BignumExec.addCarryIn e3 s1h cf12).1
        let o3 := (BignumExec.addCarryIn e3 s1h cf12).2
        let cf34 := (BignumExec.addCarryIn e4 s2l cf23).1
        let o4 := (BignumExec.addCarryIn e4 s2l cf23).2
        let cf45 := (BignumExec.addCarryIn e5 s2h cf34).1
        let o5 := (BignumExec.addCarryIn e5 s2h cf34).2
        let cf56 := (BignumExec.addCarryIn e6 s3l cf45).1
        let o6 := (BignumExec.addCarryIn e6 s3l cf45).2
        let o7 := (BignumExec.addCarryIn s3h 0 cf56).2
        ⌜BignumExec.load64Mem s_mid.mem base_op = some (UInt64.ofNat s0l.toNat) ∧
         BignumExec.load64Mem s_mid.mem (base_op + 8) = some (UInt64.ofNat o1.toNat) ∧
         BignumExec.load64Mem s_mid.mem (base_op + 16) = some (UInt64.ofNat o2.toNat) ∧
         BignumExec.load64Mem s_mid.mem (base_op + 24) = some (UInt64.ofNat o3.toNat) ∧
         BignumExec.load64Mem s_mid.mem (base_op + 32) = some (UInt64.ofNat o4.toNat) ∧
         BignumExec.load64Mem s_mid.mem (base_op + 40) = some (UInt64.ofNat o5.toNat) ∧
         BignumExec.load64Mem s_mid.mem (base_op + 48) = some (UInt64.ofNat o6.toNat) ∧
         BignumExec.load64Mem s_mid.mem (base_op + 56) = some (UInt64.ofNat o7.toNat)⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumSqr4.body, List.drop, List.take,
             BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil]
  mvcgen
  rename_i s h_pre
  obtain ⟨h_op, h_zero, h_a0, h_a1, h_a2, h_a3,
          h_e1, h_e2, h_e3, h_e4, h_e5, h_e6⟩ := h_pre
  simp only [sqr_setReg_regs, sqr_setReg_mem, sqr_storeMem_regs,
             sqr_storeMem_mem, String.reduceEq, reduceIte,
             h_op, h_zero, h_a0, h_a1, h_a2, h_a3,
             h_e1, h_e2, h_e3, h_e4, h_e5, h_e6,
             sqr_load_addr_bridge,
             show UInt64.ofNat (BitVec.ofInt 64 0).toNat = UInt64.ofNat 0 from rfl,
             show UInt64.ofNat (BitVec.ofInt 64 8).toNat = UInt64.ofNat 8 from rfl,
             show UInt64.ofNat (BitVec.ofInt 64 16).toNat = UInt64.ofNat 16 from rfl,
             show UInt64.ofNat (BitVec.ofInt 64 24).toNat = UInt64.ofNat 24 from rfl,
             show UInt64.ofNat (BitVec.ofInt 64 32).toNat = UInt64.ofNat 32 from rfl,
             show UInt64.ofNat (BitVec.ofInt 64 40).toNat = UInt64.ofNat 40 from rfl,
             show UInt64.ofNat (BitVec.ofInt 64 48).toNat = UInt64.ofNat 48 from rfl,
             show UInt64.ofNat (BitVec.ofInt 64 56).toNat = UInt64.ofNat 56 from rfl,
             show (8 : UInt64) = UInt64.ofNat 8 from rfl,
             show (16 : UInt64) = UInt64.ofNat 16 from rfl,
             show (24 : UInt64) = UInt64.ofNat 24 from rfl,
             show (32 : UInt64) = UInt64.ofNat 32 from rfl,
             show (40 : UInt64) = UInt64.ofNat 40 from rfl,
             show (48 : UInt64) = UInt64.ofNat 48 from rfl,
             show (56 : UInt64) = UInt64.ofNat 56 from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sqr_load64Mem_store64_skip0 _ _ 56 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip0 _ _ 48 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip0 _ _ 40 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip0 _ _ 32 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip0 _ _ 24 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip0 _ _ 16 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip0 _ _ 8 _ (by omega) (by omega),
        sqr_load64Mem_store64_self0]
  · rw [sqr_load64Mem_store64_skip _ _ 56 8 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 48 8 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 40 8 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 32 8 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 24 8 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 16 8 _ (by omega) (by omega),
        load64Mem_store64_self]
  · rw [sqr_load64Mem_store64_skip _ _ 56 16 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 48 16 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 40 16 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 32 16 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 24 16 _ (by omega) (by omega),
        load64Mem_store64_self]
  · rw [sqr_load64Mem_store64_skip _ _ 56 24 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 48 24 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 40 24 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 32 24 _ (by omega) (by omega),
        load64Mem_store64_self]
  · rw [sqr_load64Mem_store64_skip _ _ 56 32 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 48 32 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 40 32 _ (by omega) (by omega),
        load64Mem_store64_self]
  · rw [sqr_load64Mem_store64_skip _ _ 56 40 _ (by omega) (by omega),
        sqr_load64Mem_store64_skip _ _ 48 40 _ (by omega) (by omega),
        load64Mem_store64_self]
  · rw [sqr_load64Mem_store64_skip _ _ 56 48 _ (by omega) (by omega),
        load64Mem_store64_self]
  · rw [load64Mem_store64_self]

/-! ### Phase 4 — `bignum_sqr_4` Phase A Triple (off-diagonal accumulation)

Phase A: 21 instructions (3 loadRdx + 6 mulx + 12 add/adc) computing
the 6 d_k accumulator values from the off-diagonal mulx products.

The proof uses an "abstracted" postcondition: we pin regs "a_i"
unchanged (they're inputs only) and let the d_k values be whatever
mvcgen + simp produces, captured in a single `∃` existential. Phase B
then takes those values as opaque inputs.

This avoids transcribing the full ~80-equation chain trace into the
Triple postcondition; the existential captures everything Phase B
needs. -/

private theorem sqr4_phaseA_triple
    (base_a base_op : UInt64) (a0 a1 a2 a3 : BitVec 64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              ((S2NBignumSSA.BignumSqr4.body.drop 13).take 21))
      (fun s => ⌜s.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
                 s.regs "op" = BitVec.ofNat 64 base_op.toNat ∧
                 s.regs "zero" = 0 ∧
                 s.regs "a0" = a0 ∧ s.regs "a1" = a1 ∧
                 s.regs "a2" = a2 ∧ s.regs "a3" = a3 ∧
                 s.regs "d1_0" = 0 ∧ s.regs "d2_0" = 0 ∧
                 s.regs "d3_0" = 0 ∧ s.regs "d4_0" = 0 ∧
                 s.regs "d5_0" = 0 ∧ s.regs "d6_0" = 0 ∧
                 s.regs "cf" = 0 ∧ s.regs "of" = 0⌝)
      (⇓ _ => fun s_mid =>
        ⌜s_mid.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
         s_mid.regs "op" = BitVec.ofNat 64 base_op.toNat ∧
         s_mid.regs "zero" = 0 ∧
         s_mid.regs "a0" = a0 ∧ s_mid.regs "a1" = a1 ∧
         s_mid.regs "a2" = a2 ∧ s_mid.regs "a3" = a3 ∧
         s_mid.regs "h01" = (BignumExec.mulx a0 a1).1 ∧
         s_mid.regs "l01" = (BignumExec.mulx a0 a1).2 ∧
         s_mid.regs "h02" = (BignumExec.mulx a0 a2).1 ∧
         s_mid.regs "l02" = (BignumExec.mulx a0 a2).2 ∧
         s_mid.regs "h03" = (BignumExec.mulx a0 a3).1 ∧
         s_mid.regs "l03" = (BignumExec.mulx a0 a3).2 ∧
         s_mid.regs "h12" = (BignumExec.mulx a1 a2).1 ∧
         s_mid.regs "l12" = (BignumExec.mulx a1 a2).2 ∧
         s_mid.regs "h13" = (BignumExec.mulx a1 a3).1 ∧
         s_mid.regs "l13" = (BignumExec.mulx a1 a3).2 ∧
         s_mid.regs "h23" = (BignumExec.mulx a2 a3).1 ∧
         s_mid.regs "l23" = (BignumExec.mulx a2 a3).2 ∧
         (∃ d1 d2 d3 d4 d5 d6 : BitVec 64,
            s_mid.regs "d1_1" = d1 ∧ s_mid.regs "d2_2" = d2 ∧
            s_mid.regs "d3_3" = d3 ∧ s_mid.regs "d4_3" = d4 ∧
            s_mid.regs "d5_2" = d5 ∧ s_mid.regs "d6_1" = d6)⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumSqr4.body, List.drop, List.take,
             BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil]
  mvcgen
  rename_i s h_pre
  obtain ⟨h_ap, h_op, h_zero, h_a0, h_a1, h_a2, h_a3,
          h_d1, h_d2, h_d3, h_d4, h_d5, h_d6, h_cf, h_of⟩ := h_pre
  simp only [sqr_setReg_regs, String.reduceEq, reduceIte,
             h_ap, h_op, h_zero, h_a0, h_a1, h_a2, h_a3,
             h_d1, h_d2, h_d3, h_d4, h_d5, h_d6, h_cf, h_of,
             true_and]
  exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Phase 4 — `bignum_sqr_4` Phase B Triple

Phase B: 6-instruction shift-left chain doubling d_1..d_6 → e_1..e_6.
Mirrors `double_p25519_phaseA` (ADC chain) but 6-limb. -/

private theorem sqr4_phaseB_triple
    (base_a base_op : UInt64) (a0 a1 a2 a3 : BitVec 64)
    (d1 d2 d3 d4 d5 d6 : BitVec 64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              ((S2NBignumSSA.BignumSqr4.body.drop 34).take 6))
      (fun s => ⌜s.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
                 s.regs "op" = BitVec.ofNat 64 base_op.toNat ∧
                 s.regs "zero" = 0 ∧
                 s.regs "a0" = a0 ∧ s.regs "a1" = a1 ∧
                 s.regs "a2" = a2 ∧ s.regs "a3" = a3 ∧
                 s.regs "d1_1" = d1 ∧ s.regs "d2_2" = d2 ∧
                 s.regs "d3_3" = d3 ∧ s.regs "d4_3" = d4 ∧
                 s.regs "d5_2" = d5 ∧ s.regs "d6_1" = d6⌝)
      (⇓ _ => fun s_mid =>
        ⌜s_mid.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
         s_mid.regs "op" = BitVec.ofNat 64 base_op.toNat ∧
         s_mid.regs "zero" = 0 ∧
         s_mid.regs "a0" = a0 ∧ s_mid.regs "a1" = a1 ∧
         s_mid.regs "a2" = a2 ∧ s_mid.regs "a3" = a3 ∧
         s_mid.regs "e1" = (BignumExec.addCarry d1 d1).2 ∧
         s_mid.regs "e2" = (BignumExec.addCarryIn d2 d2
                              (BignumExec.addCarry d1 d1).1).2 ∧
         s_mid.regs "e3" = (BignumExec.addCarryIn d3 d3
                              (BignumExec.addCarryIn d2 d2
                                 (BignumExec.addCarry d1 d1).1).1).2 ∧
         s_mid.regs "e4" = (BignumExec.addCarryIn d4 d4
                              (BignumExec.addCarryIn d3 d3
                                 (BignumExec.addCarryIn d2 d2
                                    (BignumExec.addCarry d1 d1).1).1).1).2 ∧
         s_mid.regs "e5" = (BignumExec.addCarryIn d5 d5
                              (BignumExec.addCarryIn d4 d4
                                 (BignumExec.addCarryIn d3 d3
                                    (BignumExec.addCarryIn d2 d2
                                       (BignumExec.addCarry d1 d1).1).1).1).1).2 ∧
         s_mid.regs "e6" = (BignumExec.addCarryIn d6 d6
                              (BignumExec.addCarryIn d5 d5
                                 (BignumExec.addCarryIn d4 d4
                                    (BignumExec.addCarryIn d3 d3
                                       (BignumExec.addCarryIn d2 d2
                                          (BignumExec.addCarry d1 d1).1).1).1).1).1).2⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumSqr4.body, List.drop, List.take,
             BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil]
  mvcgen
  rename_i s h_pre
  obtain ⟨h_ap, h_op, h_zero, h_a0, h_a1, h_a2, h_a3,
          h_d1, h_d2, h_d3, h_d4, h_d5, h_d6⟩ := h_pre
  simp only [sqr_setReg_regs, String.reduceEq, reduceIte,
             h_ap, h_op, h_zero, h_a0, h_a1, h_a2, h_a3,
             h_d1, h_d2, h_d3, h_d4, h_d5, h_d6, and_self]

/-! ### Phase 4 — `bignum_sqr_4` algebraic correctness (`= a²`)

`sqr_4_correct_with_chain_witnesses` closes the algebraic correctness
side: given the chain reaches s_mid AND the user supplies witnesses
that the 8 stored memory values match the computed expressions in
terms of a's mulx outputs + Phase B's doubling identity, the memory
contents decode to `a²` at Nat level.

The witnesses can be derived mechanically by re-tracing the chain
(future work via further phase-Triple postcondition strengthening to
expose mulx outputs); the algebraic content itself is fully closed
here via `sqr4_chain_eq_square`. -/
theorem sqr_4_correct_with_chain_witnesses
    (a0 a1 a2 a3 : UInt64)
    (o0 o1 o2 o3 o4 o5 o6 o7 : UInt64)
    (e1 e2 e3 e4 e5 e6 : BitVec 64)
    (h01 l01 h02 l02 h03 l03 h12 l12 h13 l13 h23 l23 : BitVec 64)
    (m_01 : h01.toNat * 2^64 + l01.toNat = a0.toNat * a1.toNat)
    (m_02 : h02.toNat * 2^64 + l02.toNat = a0.toNat * a2.toNat)
    (m_03 : h03.toNat * 2^64 + l03.toNat = a0.toNat * a3.toNat)
    (m_12 : h12.toNat * 2^64 + l12.toNat = a1.toNat * a2.toNat)
    (m_13 : h13.toNat * 2^64 + l13.toNat = a1.toNat * a3.toNat)
    (m_23 : h23.toNat * 2^64 + l23.toNat = a2.toNat * a3.toNat)
    (s0h s0l s1h s1l s2h s2l s3h s3l : BitVec 64)
    (m_d0 : s0h.toNat * 2^64 + s0l.toNat = a0.toNat * a0.toNat)
    (m_d1 : s1h.toNat * 2^64 + s1l.toNat = a1.toNat * a1.toNat)
    (m_d2 : s2h.toNat * 2^64 + s2l.toNat = a2.toNat * a2.toNat)
    (m_d3 : s3h.toNat * 2^64 + s3l.toNat = a3.toNat * a3.toNat)
    (h_e :
      e1.toNat + e2.toNat * 2^64 + e3.toNat * 2^128 +
      e4.toNat * 2^192 + e5.toNat * 2^256 + e6.toNat * 2^320 =
        2 * (l01.toNat +
             (h01.toNat + l02.toNat) * 2^64 +
             (h02.toNat + l03.toNat + l12.toNat) * 2^128 +
             (h03.toNat + h12.toNat + l13.toNat) * 2^192 +
             (h13.toNat + l23.toNat) * 2^256 +
             h23.toNat * 2^320))
    (o_sum_eq :
      o0.toNat + o1.toNat * 2^64 + o2.toNat * 2^128 + o3.toNat * 2^192 +
      o4.toNat * 2^256 + o5.toNat * 2^320 + o6.toNat * 2^384 + o7.toNat * 2^448 =
      e1.toNat * 2^64 + e2.toNat * 2^128 + e3.toNat * 2^192 +
      e4.toNat * 2^256 + e5.toNat * 2^320 + e6.toNat * 2^384 +
      (s0l.toNat + s0h.toNat * 2^64 +
       s1l.toNat * 2^128 + s1h.toNat * 2^192 +
       s2l.toNat * 2^256 + s2h.toNat * 2^320 +
       s3l.toNat * 2^384 + s3h.toNat * 2^448))
    (h_no_overflow :
      e1.toNat * 2^64 + e2.toNat * 2^128 + e3.toNat * 2^192 +
      e4.toNat * 2^256 + e5.toNat * 2^320 + e6.toNat * 2^384 +
      (s0l.toNat + s0h.toNat * 2^64 +
       s1l.toNat * 2^128 + s1h.toNat * 2^192 +
       s2l.toNat * 2^256 + s2h.toNat * 2^320 +
       s3l.toNat * 2^384 + s3h.toNat * 2^448) < 2^512) :
    o0.toNat + o1.toNat * 2^64 + o2.toNat * 2^128 + o3.toNat * 2^192 +
    o4.toNat * 2^256 + o5.toNat * 2^320 + o6.toNat * 2^384 + o7.toNat * 2^448 =
    (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192) *
    (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192) := by
  rw [o_sum_eq]
  exact sqr4_chain_eq_square
    a0.toBitVec a1.toBitVec a2.toBitVec a3.toBitVec
    h01 l01 h02 l02 h03 l03 h12 l12 h13 l13 h23 l23
    (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; exact m_01)
    (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; exact m_02)
    (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; exact m_03)
    (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; exact m_12)
    (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; exact m_13)
    (by rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]; exact m_23)
    s0h s0l s1h s1l s2h s2l s3h s3l
    (by rw [UInt64.toNat_toBitVec]; exact m_d0)
    (by rw [UInt64.toNat_toBitVec]; exact m_d1)
    (by rw [UInt64.toNat_toBitVec]; exact m_d2)
    (by rw [UInt64.toNat_toBitVec]; exact m_d3)
    e1 e2 e3 e4 e5 e6 h_e h_no_overflow

/-! ### Phase 4 — `bignum_sqr_4` functional wrapper

`sqr_4_memory_filled` — the chained-Triple result lifted to functional
`bignumExec`. Given the chain reaches s_mid, memory at op+8k contains
8 values (no algebraic claim — that requires composition with
`sqr4_chain_eq_square` and the specific mulx hypotheses, deferred).

Proof: split the 63-instruction body into the four phase chunks
(3× `bignumExec_append`), then thread the four phase triples through
`triple_apply_run` (each functional run converted to its monadic form
via `bignumExecM_iff_bignumExec`). The local `irreducible` attribute
on `bignumExecM` keeps unification from whnf-evaluating the chunk
interpreters at the `triple_apply_run` applications. -/
attribute [local irreducible] BignumExec.bignumExecM in
theorem sqr_4_memory_filled
    (base_a base_op : UInt64)
    (s s_mid : BignumState)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 base_a.toNat)
    (h_op : s.regs "op" = BitVec.ofNat 64 base_op.toNat)
    (a0 a1 a2 a3 : UInt64)
    (h_a0 : BignumExec.load64Mem s.mem base_a = some a0)
    (h_a1 : BignumExec.load64Mem s.mem (base_a + 8) = some a1)
    (h_a2 : BignumExec.load64Mem s.mem (base_a + 16) = some a2)
    (h_a3 : BignumExec.load64Mem s.mem (base_a + 24) = some a3)
    (h_pre_exec :
      bignumExec (S2NBignumSSA.BignumSqr4.body.take 63) s = some s_mid) :
    ∃ o0 o1 o2 o3 o4 o5 o6 o7 : UInt64,
      BignumExec.load64Mem s_mid.mem base_op = some o0 ∧
      BignumExec.load64Mem s_mid.mem (base_op + 8) = some o1 ∧
      BignumExec.load64Mem s_mid.mem (base_op + 16) = some o2 ∧
      BignumExec.load64Mem s_mid.mem (base_op + 24) = some o3 ∧
      BignumExec.load64Mem s_mid.mem (base_op + 32) = some o4 ∧
      BignumExec.load64Mem s_mid.mem (base_op + 40) = some o5 ∧
      BignumExec.load64Mem s_mid.mem (base_op + 48) = some o6 ∧
      BignumExec.load64Mem s_mid.mem (base_op + 56) = some o7 := by
  -- Decompose the 63-instruction body into the four phase chunks.
  rw [show S2NBignumSSA.BignumSqr4.body.take 63 =
        S2NBignumSSA.BignumSqr4.body.take 13 ++
        ((S2NBignumSSA.BignumSqr4.body.drop 13).take 21 ++
         ((S2NBignumSSA.BignumSqr4.body.drop 34).take 6 ++
          (S2NBignumSSA.BignumSqr4.body.drop 40).take 23)) from rfl]
    at h_pre_exec
  obtain ⟨s1, h_run1, h_rest1⟩ :=
    BignumExec.bignumExec_append _ _ _ _ h_pre_exec
  obtain ⟨s2, h_run2, h_rest2⟩ :=
    BignumExec.bignumExec_append _ _ _ _ h_rest1
  obtain ⟨s3, h_run3, h_run4⟩ :=
    BignumExec.bignumExec_append _ _ _ _ h_rest2
  -- Init phase: registers ap/op/zero/a0..a3/d*_0/cf/of pinned at s1.
  have h_init := BignumExec.triple_apply_run
    (sqr4_init_triple base_a base_op a0 a1 a2 a3)
    ((BignumExec.bignumExecM_iff_bignumExec _ s s1).mpr h_run1)
    ⟨h_ap, h_op, h_a0, h_a1, h_a2, h_a3⟩
  -- Phase A: off-diagonal accumulation; d1..d6 existentially captured.
  have h_A := BignumExec.triple_apply_run
    (sqr4_phaseA_triple base_a base_op
      a0.toBitVec a1.toBitVec a2.toBitVec a3.toBitVec)
    ((BignumExec.bignumExecM_iff_bignumExec _ s1 s2).mpr h_run2)
    h_init
  obtain ⟨hA_ap, hA_op, hA_zero, hA_a0, hA_a1, hA_a2, hA_a3,
          _, _, _, _, _, _, _, _, _, _, _, _,
          d1, d2, d3, d4, d5, d6, hd1, hd2, hd3, hd4, hd5, hd6⟩ := h_A
  -- Phase B: doubling chain d_k → e_k.
  have h_B := BignumExec.triple_apply_run
    (sqr4_phaseB_triple base_a base_op
      a0.toBitVec a1.toBitVec a2.toBitVec a3.toBitVec d1 d2 d3 d4 d5 d6)
    ((BignumExec.bignumExecM_iff_bignumExec _ s2 s3).mpr h_run3)
    ⟨hA_ap, hA_op, hA_zero, hA_a0, hA_a1, hA_a2, hA_a3,
     hd1, hd2, hd3, hd4, hd5, hd6⟩
  obtain ⟨hB_ap, hB_op, hB_zero, hB_a0, hB_a1, hB_a2, hB_a3,
          hB_e1, hB_e2, hB_e3, hB_e4, hB_e5, hB_e6⟩ := h_B
  -- Phase C: diagonal squares + the 8 output stores.
  have h_C := BignumExec.triple_apply_run
    (sqr4_phaseC_triple base_op
      a0.toBitVec a1.toBitVec a2.toBitVec a3.toBitVec _ _ _ _ _ _)
    ((BignumExec.bignumExecM_iff_bignumExec _ s3 s_mid).mpr h_run4)
    ⟨hB_op, hB_zero, hB_a0, hB_a1, hB_a2, hB_a3,
     hB_e1, hB_e2, hB_e3, hB_e4, hB_e5, hB_e6⟩
  obtain ⟨hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7⟩ := h_C
  exact ⟨_, _, _, _, _, _, _, _, hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7⟩

/-! ### Removed: `sqr_4_correct`

This theorem claimed that `BignumSqr4.body.take 63` computes `a²` at
8-limb output.  Its proof was blocked on
`sqr4_phaseA_chain_eq_invariant_sum_bv384` (in `Sqr4Algebra.lean`),
which is provably false under the current SSA encoding.

**Reroute strategy (2026-05-11):** the inv/p58 chains route through
`bignum_montmul_p25519(out, x, x)` (via
`ChainStepAxioms.chain_sqr_step_correct_generic`), which provides
**modular** squaring `out = x² mod p_25519` directly from
`MontmulAxiom.montmul_call_squaring`.  This bypasses the buggy
`BignumSqr4.body` SSA entirely.

The raw 4×4→8 squaring (without mod) has no in-tree consumer; if
needed it would require either fixing the SSA encoding (extending
with ADCX/ADOX dual-carry-chain support) or trusting an s2n-bignum-
style HOL Light port for `bignum_sqr_4_8`. -/

end CatCrypt.Crypto.Jasmin.BignumHoare
