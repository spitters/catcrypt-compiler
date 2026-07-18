/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumHoare
import CatCrypt.Crypto.Jasmin.BignumHoare.ChainAlgebra

set_option autoImplicit false

attribute [local irreducible] CatCrypt.Crypto.Jasmin.BignumExec.bignumExecM

/-!
# Hoare-triple wrappers for `bignum_sub_p25519`

Per-primitive companion to `BignumHoare.lean` for the
`bignum_sub_p25519` body (chunked, mirrors double):

- `sub_p25519_phaseA_triple` (instructions 1-13: zero, 4 a-loads,
  4 b-loads, SBB chain).
- `sub_p25519_phaseB_triple` (instructions 14-22: mask SBB +
  p constants + masks + ADC chain).
- `sub_p25519_triple` — composes Phase A + B via
  `bignumExecM_append` + `Std.Do.Triple.bind`.
- `sub_p25519_pre_oi_values` — functional wrapper over the
  composed triple.

Split out from a former monolithic `Wrappers.lean`; see
`BignumHoare/ModWrap.lean` for the rationale (14 GiB RAM ceiling).
-/

namespace CatCrypt.Crypto.Jasmin.BignumHoare

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Hoare
open CatCrypt.Crypto.Jasmin.MemoryModel

/-! ### Equation lemmas — `BignumSubP25519`-specific wrappers (re-exposed for mvcgen) -/

private theorem sub_assignConst_eq (s : String) (k : Int) :
    S2NBignumSSA.assignConst s k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v s }) .AT_none (.sword .U64) (.Pconst k) := rfl

private theorem sub_assignBin_eq (s : String) (op : SOp2) (a b : String) :
    S2NBignumSSA.assignBin s op a b =
      .Cassgn (.Lvar { var := S2NBignumSSA.v s }) .AT_none (.sword .U64)
        (.Papp2 op (.Pvar { gv := { var := S2NBignumSSA.v a }, gs := false })
                   (.Pvar { gv := { var := S2NBignumSSA.v b }, gs := false })) := rfl

private theorem sub_subCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumSubP25519.subCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SUB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

private theorem sub_sbbCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumSubP25519.sbbCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SBB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

private theorem sub_addCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumSubP25519.addCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"ADD_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

private theorem sub_adcCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumSubP25519.adcCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"ADC_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

private theorem sub_load64_eq (x base : String) (k : Int) :
    S2NBignumSSA.BignumSubP25519.load64 x base k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64)
        (.Pload .U64 { var := S2NBignumSSA.v base } (.Pconst k)) := rfl

private theorem sub_store64_eq (base : String) (k : Int) (src : String) :
    S2NBignumSSA.BignumSubP25519.store64 base k src =
      .Cassgn (.Lmem .U64 { var := S2NBignumSSA.v base } (.Pconst k))
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

-- Phase A for `bignum_sub_p25519`: instructions 1-13
-- (zero, 4 a-loads, 4 b-loads, SBB chain). Postcondition pins
-- regs r0..r3 = SBB chain output (subBorrow/subBorrowIn `.2`s).
open Std.Do in
private theorem sub_p25519_phaseA_triple
    (base_a base_b : UInt64) (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              (S2NBignumSSA.BignumSubP25519.body.take 13))
      (fun s => ⌜s.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
                 s.regs "bp" = BitVec.ofNat 64 base_b.toNat ∧
                 s.regs "zero" = 0 ∧
                 BignumExec.load64Mem s.mem base_a = some a0 ∧
                 BignumExec.load64Mem s.mem (base_a + 8) = some a1 ∧
                 BignumExec.load64Mem s.mem (base_a + 16) = some a2 ∧
                 BignumExec.load64Mem s.mem (base_a + 24) = some a3 ∧
                 BignumExec.load64Mem s.mem base_b = some b0 ∧
                 BignumExec.load64Mem s.mem (base_b + 8) = some b1 ∧
                 BignumExec.load64Mem s.mem (base_b + 16) = some b2 ∧
                 BignumExec.load64Mem s.mem (base_b + 24) = some b3⌝)
      (⇓ _ => fun s_mid =>
        ⌜s_mid.regs "zero" = 0 ∧
         s_mid.regs "r0" = (BignumExec.subBorrow a0.toBitVec b0.toBitVec).2 ∧
         s_mid.regs "r1" = (BignumExec.subBorrowIn a1.toBitVec b1.toBitVec
                              (BignumExec.subBorrow a0.toBitVec b0.toBitVec).1).2 ∧
         s_mid.regs "r2" = (BignumExec.subBorrowIn a2.toBitVec b2.toBitVec
                              (BignumExec.subBorrowIn a1.toBitVec b1.toBitVec
                                 (BignumExec.subBorrow a0.toBitVec b0.toBitVec).1).1).2 ∧
         s_mid.regs "r3" = (BignumExec.subBorrowIn a3.toBitVec b3.toBitVec
                              (BignumExec.subBorrowIn a2.toBitVec b2.toBitVec
                                 (BignumExec.subBorrowIn a1.toBitVec b1.toBitVec
                                    (BignumExec.subBorrow a0.toBitVec b0.toBitVec).1).1).1).2 ∧
         s_mid.regs "cf" =
           (BignumExec.subBorrowIn a3.toBitVec b3.toBitVec
              (BignumExec.subBorrowIn a2.toBitVec b2.toBitVec
                 (BignumExec.subBorrowIn a1.toBitVec b1.toBitVec
                    (BignumExec.subBorrow a0.toBitVec b0.toBitVec).1).1).1).1⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumSubP25519.body, List.take]
  set_option maxRecDepth 4000 in
  mvcgen [BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil,
          BignumExec.stepInstrM,
          BignumExec.execInstr, BignumExec.evalPExpr,
          BignumExec.resolveAddr, BignumExec.setReg,
          BignumExec.writeSubBundle, BignumExec.subBorrow,
          BignumExec.subBorrowIn,
          sub_subCopn_eq, sub_sbbCopn_eq,
          sub_addCopn_eq, sub_adcCopn_eq,
          sub_load64_eq, sub_store64_eq,
          sub_assignConst_eq, sub_assignBin_eq]
  · rename_i s_pre h_pre
    obtain ⟨h_ap, h_bp, h_zero, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3⟩ := h_pre
    bignum_wp_unfold
    simp only [S2NBignumSSA.v]
    have bridge : ∀ (k : UInt64) (base : UInt64),
        UInt64.ofNat ((base.toNat + k.toNat) % 18446744073709551616) = base + k := by
      intro k base; rw [← UInt64.toNat_add]; exact UInt64.ofNat_toNat
    have h_a8 : UInt64.ofNat ((base_a.toNat + 8) % 18446744073709551616) = base_a + 8 :=
      bridge 8 base_a
    have h_a16 : UInt64.ofNat ((base_a.toNat + 16) % 18446744073709551616) = base_a + 16 :=
      bridge 16 base_a
    have h_a24 : UInt64.ofNat ((base_a.toNat + 24) % 18446744073709551616) = base_a + 24 :=
      bridge 24 base_a
    have h_b8 : UInt64.ofNat ((base_b.toNat + 8) % 18446744073709551616) = base_b + 8 :=
      bridge 8 base_b
    have h_b16 : UInt64.ofNat ((base_b.toNat + 16) % 18446744073709551616) = base_b + 16 :=
      bridge 16 base_b
    have h_b24 : UInt64.ofNat ((base_b.toNat + 24) % 18446744073709551616) = base_b + 24 :=
      bridge 24 base_b
    simp [h_ap, h_bp, h_zero, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3,
          h_a8, h_a16, h_a24, h_b8, h_b16, h_b24, pure, StateT.pure,
          BignumExec.subBorrow, BignumExec.subBorrowIn]

-- Phase B for `bignum_sub_p25519`: instructions 14-22
-- (mask SBB + p constants + masks + ADC chain). Closes algoNat equation.
open Std.Do in
private theorem sub_p25519_phaseB_triple
    (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              ((S2NBignumSSA.BignumSubP25519.body.drop 13).take 9))
      (fun s => ⌜s.regs "zero" = 0 ∧
                 s.regs "r0" = (BignumExec.subBorrow a0.toBitVec b0.toBitVec).2 ∧
                 s.regs "r1" = (BignumExec.subBorrowIn a1.toBitVec b1.toBitVec
                                  (BignumExec.subBorrow a0.toBitVec b0.toBitVec).1).2 ∧
                 s.regs "r2" = (BignumExec.subBorrowIn a2.toBitVec b2.toBitVec
                                  (BignumExec.subBorrowIn a1.toBitVec b1.toBitVec
                                     (BignumExec.subBorrow a0.toBitVec b0.toBitVec).1).1).2 ∧
                 s.regs "r3" = (BignumExec.subBorrowIn a3.toBitVec b3.toBitVec
                                  (BignumExec.subBorrowIn a2.toBitVec b2.toBitVec
                                     (BignumExec.subBorrowIn a1.toBitVec b1.toBitVec
                                        (BignumExec.subBorrow a0.toBitVec b0.toBitVec).1).1).1).2 ∧
                 s.regs "cf" =
                   (BignumExec.subBorrowIn a3.toBitVec b3.toBitVec
                      (BignumExec.subBorrowIn a2.toBitVec b2.toBitVec
                         (BignumExec.subBorrowIn a1.toBitVec b1.toBitVec
                            (BignumExec.subBorrow a0.toBitVec b0.toBitVec).1).1).1).1⌝)
      (⇓ _ => fun s_mid =>
        ⌜(s_mid.regs "s0").toNat
            + (s_mid.regs "s1").toNat * 2 ^ 64
            + (s_mid.regs "s2").toNat * 2 ^ 128
            + (s_mid.regs "s3").toNat * 2 ^ 192
          = S2NBignumSSA.BignumSubP25519.algoNat
              (a0.toNat + a1.toNat * 2 ^ 64
                + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192)
              (b0.toNat + b1.toNat * 2 ^ 64
                + b2.toNat * 2 ^ 128 + b3.toNat * 2 ^ 192)⌝) := by
  -- Recipe mirrors `double_p25519_phaseB_triple` (see DoubleWrap.lean).
  -- Pre-rewrite the SBB-form r0..r3, cf hypotheses into chain form
  -- (using `subBorrow_*_eq*` / `subBorrowIn_*_eq*` from ChainAlgebra)
  -- BEFORE calling simp on the goal — this makes the LHS align with
  -- the chain-form keystone `sub_p25519_chain_algoNat` so the final
  -- `exact key` does not require deep defeq unification.
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumSubP25519.body, List.drop, List.take]
  set_option maxHeartbeats 32000000 in
  set_option maxRecDepth 4000 in
  mvcgen [BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil,
          BignumExec.stepInstrM,
          BignumExec.execInstr, BignumExec.evalPExpr,
          BignumExec.resolveAddr, BignumExec.setReg,
          BignumExec.writeSubBundle, BignumExec.subBorrow,
          BignumExec.subBorrowIn,
          sub_subCopn_eq, sub_sbbCopn_eq,
          sub_addCopn_eq, sub_adcCopn_eq,
          sub_load64_eq, sub_store64_eq,
          sub_assignConst_eq, sub_assignBin_eq]
  · rename_i s_pre h_pre
    obtain ⟨h_zero, h_r0, h_r1, h_r2, h_r3, h_cf⟩ := h_pre
    -- Bridge `addCarryIn` (ADC chain in Phase B body) and `subBorrow*`
    -- (SBB chain inherited from Phase A's postcondition) into the
    -- chain form used by the keystone `sub_p25519_chain_algoNat`. The
    -- `subBorrow_*` rules are `rfl`-bridges in `ChainAlgebra.lean`.
    simp only [addCarryIn_carry_eq_chain, subBorrow_borrow_eq_chain,
               subBorrowIn_borrow_eq_chain, subBorrow_diff_eq,
               subBorrowIn_diff_eq] at *
    bignum_wp_unfold
    simp only [S2NBignumSSA.v]
    -- The `← BitVec.toNat_*` rules block the default simp set's
    -- `BitVec → Nat` rewrites, keeping the goal in BitVec form so it
    -- aligns with the keystone's LHS for `exact key`.
    set_option linter.unusedSimpArgs false in
    simp [h_zero, h_r0, h_r1, h_r2, h_r3, h_cf, pure, StateT.pure,
          BignumExec.addCarry, BignumExec.addCarryIn,
          ← BitVec.toNat_neg, ← BitVec.toNat_and, ← BitVec.toNat_or,
          ← BitVec.toNat_xor, ← BitVec.toNat_sub, ← BitVec.toNat_add]
    have key := sub_p25519_chain_algoNat a0.toBitVec a1.toBitVec a2.toBitVec a3.toBitVec
                                          b0.toBitVec b1.toBitVec b2.toBitVec b3.toBitVec
    simp only [UInt64.toNat_toBitVec] at key
    -- maxRecDepth 4000 is enough once the goal/key shapes are aligned;
    -- without the alignment via the named bridges this would diverge.
    set_option maxRecDepth 4000 in exact key

-- Hoare triple for `bignum_sub_p25519` (full body except final 4 stores).
-- Composes Phase A + Phase B via `List.take_add` + `bignumExecM_append`
-- + `Std.Do.Triple.bind`. The file-scope `attribute [local irreducible]
-- bignumExecM` (line 10) blocks Lean from whnf-unfolding the 22-element
-- body literal during the bind unification.
open Std.Do in
private theorem sub_p25519_triple
    (base_a base_b : UInt64) (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              (S2NBignumSSA.BignumSubP25519.body.take 22))
      (fun s => ⌜s.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
                 s.regs "bp" = BitVec.ofNat 64 base_b.toNat ∧
                 s.regs "zero" = 0 ∧
                 BignumExec.load64Mem s.mem base_a = some a0 ∧
                 BignumExec.load64Mem s.mem (base_a + 8) = some a1 ∧
                 BignumExec.load64Mem s.mem (base_a + 16) = some a2 ∧
                 BignumExec.load64Mem s.mem (base_a + 24) = some a3 ∧
                 BignumExec.load64Mem s.mem base_b = some b0 ∧
                 BignumExec.load64Mem s.mem (base_b + 8) = some b1 ∧
                 BignumExec.load64Mem s.mem (base_b + 16) = some b2 ∧
                 BignumExec.load64Mem s.mem (base_b + 24) = some b3⌝)
      (⇓ _ => fun s_mid =>
        ⌜(s_mid.regs "s0").toNat
            + (s_mid.regs "s1").toNat * 2 ^ 64
            + (s_mid.regs "s2").toNat * 2 ^ 128
            + (s_mid.regs "s3").toNat * 2 ^ 192
          = S2NBignumSSA.BignumSubP25519.algoNat
              (a0.toNat + a1.toNat * 2 ^ 64
                + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192)
              (b0.toNat + b1.toNat * 2 ^ 64
                + b2.toNat * 2 ^ 128 + b3.toNat * 2 ^ 192)⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  rw [show (22 : Nat) = 13 + 9 from rfl, List.take_add]
  rw [BignumExec.bignumExecM_append]
  exact Std.Do.Triple.bind
    (BignumExec.bignumExecM BignumExec.emptyRegistry
      (S2NBignumSSA.BignumSubP25519.body.take 13))
    (fun _ => BignumExec.bignumExecM BignumExec.emptyRegistry
      ((S2NBignumSSA.BignumSubP25519.body.drop 13).take 9))
    (sub_p25519_phaseA_triple base_a base_b a0 a1 a2 a3 b0 b1 b2 b3)
    (fun _ => sub_p25519_phaseB_triple a0 a1 a2 a3 b0 b1 b2 b3)

/-- Functional wrapper for `bignum_sub_p25519`. Mirror of
    `double_p25519_pre_oi_values` but for the sub_p25519 body and
    two-input shape (a, b). -/
theorem sub_p25519_pre_oi_values
    (base_a base_b : UInt64)
    (s s_mid : BignumState)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 base_a.toNat)
    (h_bp : s.regs "bp" = BitVec.ofNat 64 base_b.toNat)
    (h_zero : s.regs "zero" = 0)
    (a_val b_val : Nat)
    (h_load_a : memNat4 base_a s.mem = some a_val)
    (h_load_b : memNat4 base_b s.mem = some b_val)
    (h_pre_exec :
      bignumExec (S2NBignumSSA.BignumSubP25519.body.take 22) s = some s_mid) :
    (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "s0").vname).toNat).toNat
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "s1").vname).toNat).toNat * 2 ^ 64
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "s2").vname).toNat).toNat * 2 ^ 128
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "s3").vname).toNat).toNat * 2 ^ 192
      = S2NBignumSSA.BignumSubP25519.algoNat a_val b_val := by
  obtain ⟨a0, a1, a2, a3, h_a0, h_a1, h_a2, h_a3, h_a_decomp⟩ :=
    (memNat4_eq_some_iff base_a s.mem a_val).mp h_load_a
  obtain ⟨b0, b1, b2, b3, h_b0, h_b1, h_b2, h_b3, h_b_decomp⟩ :=
    (memNat4_eq_some_iff base_b s.mem b_val).mp h_load_b
  rw [← BignumExec.bignumExecM_iff_bignumExec] at h_pre_exec
  have h_post := BignumExec.triple_apply_run
    (sub_p25519_triple base_a base_b a0 a1 a2 a3 b0 b1 b2 b3)
    h_pre_exec
    ⟨h_ap, h_bp, h_zero, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3⟩
  rw [h_a_decomp, h_b_decomp]
  have hs0 := (s_mid.regs (S2NBignumSSA.v "s0").vname).isLt
  have hs1 := (s_mid.regs (S2NBignumSSA.v "s1").vname).isLt
  have hs2 := (s_mid.regs (S2NBignumSSA.v "s2").vname).isLt
  have hs3 := (s_mid.regs (S2NBignumSSA.v "s3").vname).isLt
  rw [UInt64.toNat_ofNat_of_lt' hs0,
      UInt64.toNat_ofNat_of_lt' hs1,
      UInt64.toNat_ofNat_of_lt' hs2,
      UInt64.toNat_ofNat_of_lt' hs3]
  exact h_post

end CatCrypt.Crypto.Jasmin.BignumHoare
