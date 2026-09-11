/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.BignumHoare
public import CatCrypt.Crypto.Jasmin.BignumHoare.ChainAlgebra

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] CatCrypt.Crypto.Jasmin.BignumExec.bignumExecM

/-!
# Hoare-triple wrappers for `bignum_double_p25519`

Per-primitive companion to `BignumHoare.lean` for the
`bignum_double_p25519` body:

- `double_p25519_phaseA_triple` (instructions 1-13: zero, 4 loads, 4
  r←a copies, ADC chain).
- `double_p25519_phaseB_triple` (instructions 14-39: assignConsts +
  r→t copies + SBB chain + mask-cmov).
- `double_p25519_triple` — composes Phase A + B via
  `bignumExecM_append` + `Std.Do.Triple.bind`.
- `double_p25519_pre_oi_values` — functional wrapper over the
  composed triple.

Split out from a former monolithic `Wrappers.lean`; see
`BignumHoare/ModWrap.lean` for the rationale (14 GiB RAM ceiling).
-/

namespace CatCrypt.Crypto.Jasmin.BignumHoare

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Hoare
open CatCrypt.Crypto.Jasmin.MemoryModel

/-! ### Equation lemmas — `BignumDoubleP25519`-specific wrappers (re-exposed for mvcgen) -/

theorem dbl_assignConst_eq (s : String) (k : Int) :
    S2NBignumSSA.assignConst s k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v s }) .AT_none (.sword .U64) (.Pconst k) := rfl

theorem dbl_assignBin_eq (s : String) (op : SOp2) (a b : String) :
    S2NBignumSSA.assignBin s op a b =
      .Cassgn (.Lvar { var := S2NBignumSSA.v s }) .AT_none (.sword .U64)
        (.Papp2 op (.Pvar { gv := { var := S2NBignumSSA.v a }, gs := false })
                   (.Pvar { gv := { var := S2NBignumSSA.v b }, gs := false })) := rfl

theorem dbl_subCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumDoubleP25519.subCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SUB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

theorem dbl_sbbCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumDoubleP25519.sbbCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SBB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

theorem dbl_addCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumDoubleP25519.addCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"ADD_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

theorem dbl_adcCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumDoubleP25519.adcCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"ADC_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

theorem dbl_load64_eq (x base : String) (k : Int) :
    S2NBignumSSA.BignumDoubleP25519.load64 x base k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64)
        (.Pload .U64 { var := S2NBignumSSA.v base } (.Pconst k)) := rfl

theorem dbl_store64_eq (base : String) (k : Int) (src : String) :
    S2NBignumSSA.BignumDoubleP25519.store64 base k src =
      .Cassgn (.Lmem .U64 { var := S2NBignumSSA.v base } (.Pconst k))
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

theorem dbl_copy64'_eq (dst src : String) :
    S2NBignumSSA.BignumDoubleP25519.copy64' dst src =
      .Cassgn (.Lvar { var := S2NBignumSSA.v dst }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

-- Phase A for `bignum_double_p25519`: instructions 1-13
-- (zero, 4 loads, 4 r←a copies, ADC chain). Postcondition pins down
-- the regs r0..r3 reached by the ADC chain in addCarry/addCarryIn
-- semantics, ready for Phase B.
open Std.Do in
theorem double_p25519_phaseA_triple
    (base_a : UInt64) (a0 a1 a2 a3 : UInt64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              (S2NBignumSSA.BignumDoubleP25519.body.take 13))
      (fun s => ⌜s.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
                 s.regs "zero" = 0 ∧
                 BignumExec.load64Mem s.mem base_a = some a0 ∧
                 BignumExec.load64Mem s.mem (base_a + 8) = some a1 ∧
                 BignumExec.load64Mem s.mem (base_a + 16) = some a2 ∧
                 BignumExec.load64Mem s.mem (base_a + 24) = some a3⌝)
      (⇓ _ => fun s_mid =>
        ⌜s_mid.regs "zero" = 0 ∧
         s_mid.regs "r0" = (BignumExec.addCarry a0.toBitVec a0.toBitVec).2 ∧
         s_mid.regs "r1" = (BignumExec.addCarryIn a1.toBitVec a1.toBitVec
                              (BignumExec.addCarry a0.toBitVec a0.toBitVec).1).2 ∧
         s_mid.regs "r2" = (BignumExec.addCarryIn a2.toBitVec a2.toBitVec
                              (BignumExec.addCarryIn a1.toBitVec a1.toBitVec
                                 (BignumExec.addCarry a0.toBitVec a0.toBitVec).1).1).2 ∧
         s_mid.regs "r3" = (BignumExec.addCarryIn a3.toBitVec a3.toBitVec
                              (BignumExec.addCarryIn a2.toBitVec a2.toBitVec
                                 (BignumExec.addCarryIn a1.toBitVec a1.toBitVec
                                    (BignumExec.addCarry a0.toBitVec a0.toBitVec).1).1).1).2⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumDoubleP25519.body, List.take]
  set_option maxRecDepth 4000 in
  mvcgen [BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil,
          BignumExec.stepInstrM,
          BignumExec.execInstr, BignumExec.evalPExpr,
          BignumExec.resolveAddr, BignumExec.setReg,
          BignumExec.writeSubBundle, BignumExec.subBorrow,
          BignumExec.subBorrowIn,
          dbl_subCopn_eq, dbl_sbbCopn_eq,
          dbl_addCopn_eq, dbl_adcCopn_eq,
          dbl_load64_eq, dbl_store64_eq, dbl_copy64'_eq,
          dbl_assignConst_eq, dbl_assignBin_eq]
  · rename_i s_pre h_pre
    obtain ⟨h_ap, h_zero, h_a0, h_a1, h_a2, h_a3⟩ := h_pre
    bignum_wp_unfold
    simp only [S2NBignumSSA.v]
    have bridge : ∀ (k : UInt64),
        UInt64.ofNat ((base_a.toNat + k.toNat) % 18446744073709551616) = base_a + k := by
      intro k; rw [← UInt64.toNat_add]; exact UInt64.ofNat_toNat
    have h_addr_8 : UInt64.ofNat ((base_a.toNat + 8) % 18446744073709551616) = base_a + 8 :=
      bridge 8
    have h_addr_16 : UInt64.ofNat ((base_a.toNat + 16) % 18446744073709551616) = base_a + 16 :=
      bridge 16
    have h_addr_24 : UInt64.ofNat ((base_a.toNat + 24) % 18446744073709551616) = base_a + 24 :=
      bridge 24
    simp [h_ap, h_zero, h_a0, h_a1, h_a2, h_a3,
          h_addr_8, h_addr_16, h_addr_24, pure, StateT.pure,
          BignumExec.addCarry, BignumExec.addCarryIn]

-- Phase B for `bignum_double_p25519`: instructions 14-39
-- (26 instructions: assignConsts + r→t copies + SBB chain + mask-cmov).
-- Precondition: state matches Phase A's postcondition (r0..r3 = ADC
-- chain output, zero = 0). Postcondition: algoNat equation.
open Std.Do in
theorem double_p25519_phaseB_triple
    (a0 a1 a2 a3 : UInt64)
    (h_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 +
                  a3.toNat * 2^192 < 2^255 - 19) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              ((S2NBignumSSA.BignumDoubleP25519.body.drop 13).take 26))
      (fun s => ⌜s.regs "zero" = 0 ∧
                 s.regs "r0" = (BignumExec.addCarry a0.toBitVec a0.toBitVec).2 ∧
                 s.regs "r1" = (BignumExec.addCarryIn a1.toBitVec a1.toBitVec
                                  (BignumExec.addCarry a0.toBitVec a0.toBitVec).1).2 ∧
                 s.regs "r2" = (BignumExec.addCarryIn a2.toBitVec a2.toBitVec
                                  (BignumExec.addCarryIn a1.toBitVec a1.toBitVec
                                     (BignumExec.addCarry a0.toBitVec a0.toBitVec).1).1).2 ∧
                 s.regs "r3" = (BignumExec.addCarryIn a3.toBitVec a3.toBitVec
                                  (BignumExec.addCarryIn a2.toBitVec a2.toBitVec
                                     (BignumExec.addCarryIn a1.toBitVec a1.toBitVec
                                        (BignumExec.addCarry a0.toBitVec a0.toBitVec).1).1).1).2⌝)
      (⇓ _ => fun s_mid =>
        ⌜(s_mid.regs "o0").toNat
            + (s_mid.regs "o1").toNat * 2 ^ 64
            + (s_mid.regs "o2").toNat * 2 ^ 128
            + (s_mid.regs "o3").toNat * 2 ^ 192
          = S2NBignumSSA.BignumDoubleP25519.algoNat
              (a0.toNat + a1.toNat * 2 ^ 64
                + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192)⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumDoubleP25519.body, List.drop, List.take]
  set_option maxRecDepth 4000 in
  mvcgen [BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil,
          BignumExec.stepInstrM,
          BignumExec.execInstr, BignumExec.evalPExpr,
          BignumExec.resolveAddr, BignumExec.setReg,
          BignumExec.writeSubBundle, BignumExec.subBorrow,
          BignumExec.subBorrowIn,
          dbl_subCopn_eq, dbl_sbbCopn_eq,
          dbl_addCopn_eq, dbl_adcCopn_eq,
          dbl_load64_eq, dbl_store64_eq, dbl_copy64'_eq,
          dbl_assignConst_eq, dbl_assignBin_eq]
  · rename_i s_pre h_pre
    obtain ⟨h_zero, h_r0, h_r1, h_r2, h_r3⟩ := h_pre
    bignum_wp_unfold
    simp only [S2NBignumSSA.v]
    simp only [addCarryIn_carry_eq_chain,
               show ∀ a : BitVec 64, (BignumExec.addCarry a a).1 =
                 if (a + a).ult a then (1 : BitVec 64) else 0 from fun _ => rfl,
               show ∀ a : BitVec 64, (BignumExec.addCarry a a).2 = a + a from fun _ => rfl,
               show ∀ a b cin : BitVec 64, (BignumExec.addCarryIn a b cin).2 =
                 a + b + (cin &&& 1) from fun _ _ _ => rfl] at h_r0 h_r1 h_r2 h_r3
    simp [h_zero, h_r0, h_r1, h_r2, h_r3, pure, StateT.pure,
          ← BitVec.toNat_neg, ← BitVec.toNat_and, ← BitVec.toNat_or,
          ← BitVec.toNat_xor]
    have key := double_p25519_chain_algoNat a0.toBitVec a1.toBitVec
                  a2.toBitVec a3.toBitVec h_bound
    simp only [UInt64.toNat_toBitVec] at key
    exact key

/-! ### Phase 4 — `bignum_double_p25519` Hoare-triple wrapper

Mirrors `pre_oi_values_triple` but for the double_p25519 body.
Uses the same recipe: body unfold + mvcgen + bignum_wp_unfold +
bv_normalize + apply algoNat keystone via the chain bridge.

Note: this requires the input bound `a < p` (h_bound) to ensure
2a < B = 2^256, otherwise algoNat's `(2a) % B` doesn't equal `2a`. -/

-- Chunked composition via explicit `Std.Do.Triple.bind` term.
-- Splits `body.take 39 = body.take (13 + 26)` via `List.take_add`
-- (no list-literal materialization), then applies `Triple.bind`
-- as a fully-applied term. The file-scope `attribute [local
-- irreducible] bignumExecM` (line 11) blocks Lean from
-- whnf-unfolding the long body literal during the bind unification.
open Std.Do in
theorem double_p25519_triple
    (base_a : UInt64) (a0 a1 a2 a3 : UInt64)
    (h_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 +
                  a3.toNat * 2^192 < 2^255 - 19) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              (S2NBignumSSA.BignumDoubleP25519.body.take 39))
      (fun s => ⌜s.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
                 s.regs "zero" = 0 ∧
                 BignumExec.load64Mem s.mem base_a = some a0 ∧
                 BignumExec.load64Mem s.mem (base_a + 8) = some a1 ∧
                 BignumExec.load64Mem s.mem (base_a + 16) = some a2 ∧
                 BignumExec.load64Mem s.mem (base_a + 24) = some a3⌝)
      (⇓ _ => fun s_mid =>
        ⌜(s_mid.regs "o0").toNat
            + (s_mid.regs "o1").toNat * 2 ^ 64
            + (s_mid.regs "o2").toNat * 2 ^ 128
            + (s_mid.regs "o3").toNat * 2 ^ 192
          = S2NBignumSSA.BignumDoubleP25519.algoNat
              (a0.toNat + a1.toNat * 2 ^ 64
                + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192)⌝) := by
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  rw [show (39 : Nat) = 13 + 26 from rfl, List.take_add]
  rw [BignumExec.bignumExecM_append]
  exact Std.Do.Triple.bind
    (BignumExec.bignumExecM BignumExec.emptyRegistry
      (S2NBignumSSA.BignumDoubleP25519.body.take 13))
    (fun _ => BignumExec.bignumExecM BignumExec.emptyRegistry
      ((S2NBignumSSA.BignumDoubleP25519.body.drop 13).take 26))
    (double_p25519_phaseA_triple base_a a0 a1 a2 a3)
    (fun _ => double_p25519_phaseB_triple a0 a1 a2 a3 h_bound)

/-- Functional wrapper for `bignum_double_p25519`. After running the
    first 39 instructions of the body (everything except the final 4
    `op[i]:=oi` stores), the four `oi` registers hold the limbs of
    `algoNat a_val`.

    Mirror of `pre_oi_values` but for the double_p25519 body; lifts
    `double_p25519_triple` (the chunked Hoare triple) to the functional
    `bignumExec` interface used by the diff-test gate. -/
theorem double_p25519_pre_oi_values
    (base_a : UInt64)
    (s s_mid : BignumState)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 base_a.toNat)
    (h_zero : s.regs "zero" = 0)
    (a_val : Nat)
    (h_load_a : memNat4 base_a s.mem = some a_val)
    (h_a_bound : a_val < 2 ^ 255 - 19)
    (h_pre_exec :
      bignumExec (S2NBignumSSA.BignumDoubleP25519.body.take 39) s = some s_mid) :
    (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o0").vname).toNat).toNat
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o1").vname).toNat).toNat * 2 ^ 64
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o2").vname).toNat).toNat * 2 ^ 128
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o3").vname).toNat).toNat * 2 ^ 192
      = S2NBignumSSA.BignumDoubleP25519.algoNat a_val := by
  -- Expose per-limb load hypotheses.
  obtain ⟨a0, a1, a2, a3, h_a0, h_a1, h_a2, h_a3, h_a_decomp⟩ :=
    (memNat4_eq_some_iff base_a s.mem a_val).mp h_load_a
  -- Convert functional `bignumExec` to monadic `bignumExecM`,
  -- then apply double_p25519_triple via triple_apply_run.
  rw [← BignumExec.bignumExecM_iff_bignumExec] at h_pre_exec
  have h_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128
                  + a3.toNat * 2^192 < 2^255 - 19 := by
    rw [← h_a_decomp]; exact h_a_bound
  have h_post := BignumExec.triple_apply_run
    (double_p25519_triple base_a a0 a1 a2 a3 h_bound)
    h_pre_exec
    ⟨h_ap, h_zero, h_a0, h_a1, h_a2, h_a3⟩
  -- The triple's post matches our goal modulo:
  -- (1) `(UInt64.ofNat _.toNat).toNat = _.toNat` (truncating roundtrip);
  -- (2) `a_val = a0.toNat + ...` via h_a_decomp.
  rw [h_a_decomp]
  have ho0 := (s_mid.regs (S2NBignumSSA.v "o0").vname).isLt
  have ho1 := (s_mid.regs (S2NBignumSSA.v "o1").vname).isLt
  have ho2 := (s_mid.regs (S2NBignumSSA.v "o2").vname).isLt
  have ho3 := (s_mid.regs (S2NBignumSSA.v "o3").vname).isLt
  rw [UInt64.toNat_ofNat_of_lt' ho0,
      UInt64.toNat_ofNat_of_lt' ho1,
      UInt64.toNat_ofNat_of_lt' ho2,
      UInt64.toNat_ofNat_of_lt' ho3]
  exact h_post

end CatCrypt.Crypto.Jasmin.BignumHoare
