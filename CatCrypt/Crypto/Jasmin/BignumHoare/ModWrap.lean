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
# Hoare-triple wrappers for `bignum_mod_p25519_4`

Holds the heavy `Triple`-typed declarations specific to the
`bignum_mod_p25519_4` primitive:

- `pre_oi_values_triple` — the heavy `mvcgen` Hoare triple over the
  31-instruction kernel.
- `pre_oi_values` — functional wrapper that lifts the triple to the
  `bignumExec` interface used by `bodyComputesAlgoNat` /
  `ModP25519Final.lean`.

## Why a per-primitive module?

The *statements* of these declarations are very large (deep nested
`subBorrowIn` / `addCarryIn` chains over 31-instruction bodies).
Type-checking and caching them alongside the double_p25519 /
sub_p25519 wrappers in a single file pushed cumulative elaboration
past the 14 GiB host RAM ceiling. Splitting per primitive lets each
pair (phase triple + functional wrapper) elaborate in its own Lean
process so the term cache resets between files. The
`attribute [local irreducible] bignumExecM` (line 11) keeps mvcgen's
whnf budget bounded so default heartbeats suffice.

This module extends the `CatCrypt.Crypto.Jasmin.BignumHoare` namespace
— declarations are addressable as `BignumHoare.pre_oi_values` etc.,
the same path they had pre-split.
-/

namespace CatCrypt.Crypto.Jasmin.BignumHoare

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Hoare
open CatCrypt.Crypto.Jasmin.MemoryModel

/-! ### Equation lemmas — `BignumModP25519_4`-specific wrappers (re-exposed for mvcgen) -/

private theorem mod_assignConst_eq (s : String) (k : Int) :
    S2NBignumSSA.assignConst s k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v s }) .AT_none (.sword .U64) (.Pconst k) := rfl

private theorem mod_assignBin_eq (s : String) (op : SOp2) (a b : String) :
    S2NBignumSSA.assignBin s op a b =
      .Cassgn (.Lvar { var := S2NBignumSSA.v s }) .AT_none (.sword .U64)
        (.Papp2 op (.Pvar { gv := { var := S2NBignumSSA.v a }, gs := false })
                   (.Pvar { gv := { var := S2NBignumSSA.v b }, gs := false })) := rfl

private theorem mod_load64_eq (x base : String) (k : Int) :
    S2NBignumSSA.BignumModP25519_4.load64 x base k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64)
        (.Pload .U64 { var := S2NBignumSSA.v base } (.Pconst k)) := rfl

private theorem mod_store64_eq (base : String) (k : Int) (src : String) :
    S2NBignumSSA.BignumModP25519_4.store64 base k src =
      .Cassgn (.Lmem .U64 { var := S2NBignumSSA.v base } (.Pconst k))
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

private theorem mod_copy64_eq (dst src : String) :
    S2NBignumSSA.BignumModP25519_4.copy64 dst src =
      .Cassgn (.Lvar { var := S2NBignumSSA.v dst }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

private theorem mod_subCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumModP25519_4.subCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SUB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

private theorem mod_sbbCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumModP25519_4.sbbCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SBB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

/-! ### Hoare-triple form of the kernel — Phase 3 mvcgen target

Path 1 from the closure analysis: state the kernel as a Hoare triple
over `bignumExecM emptyRegistry pre`. This is the shape mvcgen walks
natively (per `BignumExec.lean §14` smoke tests). -/

open Std.Do in
/-- Hoare-triple form of `pre_oi_values`. Parameterized over the four
    a-limbs (which the surrounding context provides via `memNat4`
    decomposition). Closes via mvcgen + simp + bv_decide. -/
theorem pre_oi_values_triple
    (base_a : UInt64) (a0 a1 a2 a3 : UInt64) :
    Triple (BignumExec.bignumExecM BignumExec.emptyRegistry
              (S2NBignumSSA.BignumModP25519_4.body.take 31))
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
          = S2NBignumSSA.BignumModP25519_4.algoNat
              (a0.toNat + a1.toNat * 2 ^ 64
                + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192)⌝) := by
  -- Reduce body literal + List.take BEFORE mvcgen so the wp goal
  -- starts from a concrete 31-element list. The
  -- `attribute [local irreducible] BignumExec.bignumExecM` declared
  -- at file scope keeps mvcgen's whnf budget bounded — the previous
  -- 16M-heartbeat OOM is no longer needed; default heartbeats suffice.
  show Triple (BignumExec.bignumExecM BignumExec.emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumModP25519_4.body, List.take]
  set_option maxRecDepth 4000 in
  mvcgen [BignumExec.bignumExecM_cons, BignumExec.bignumExecM_nil,
          BignumExec.stepInstrM,
          BignumExec.execInstr, BignumExec.evalPExpr,
          BignumExec.resolveAddr, BignumExec.setReg,
          BignumExec.writeSubBundle, BignumExec.subBorrow,
          BignumExec.subBorrowIn,
          mod_assignConst_eq, mod_assignBin_eq, mod_load64_eq,
          mod_store64_eq, mod_copy64_eq, mod_subCopn_eq, mod_sbbCopn_eq]
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
          ← BitVec.toNat_neg, ← BitVec.toNat_and, ← BitVec.toNat_or,
          ← BitVec.toNat_xor]
    exact sbb_chain_algoNat a0.toBitVec a1.toBitVec a2.toBitVec a3.toBitVec

/-- The algorithmic kernel of `bignum_mod_p25519_4`: after running the
    first 31 instructions of the body (everything except the final 4
    `op[i]:=oi` stores), the four `oi` registers hold the limbs of
    `algoNat a_val`.

    Phase 3 of the mvcgen integration plan
    asks for this lemma to be discharged via `mvcgen + bv_decide`. The
    framing here is the cleanest target for that proof: load values are
    factored out as `a_val := memNat4 base_a s.mem` (already present in
    the surrounding `bodyComputesAlgoNat` context), so the residual VC
    after mvcgen is a pure 256-bit BitVec identity (SUB/SBB chain +
    mask-cmov vs. `algoNat`) that `bv_decide` should handle.

    **Status (2026-04-27):** statement only — the proof is the open
    Phase 3 work item. -/
theorem pre_oi_values
    (base_a base_op : UInt64)
    (s s_mid : BignumState)
    (h_ap : s.regs "ap" = BitVec.ofNat 64 base_a.toNat)
    (h_op : s.regs "op" = BitVec.ofNat 64 base_op.toNat)
    (h_zero : s.regs "zero" = 0)
    (a_val : Nat)
    (h_load_a : memNat4 base_a s.mem = some a_val)
    (h_a_bound : a_val < 2 * (2 ^ 255 - 19))
    (h_pre_exec :
      bignumExec (S2NBignumSSA.BignumModP25519_4.body.take 31) s = some s_mid) :
    (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o0").vname).toNat).toNat
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o1").vname).toNat).toNat * 2 ^ 64
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o2").vname).toNat).toNat * 2 ^ 128
      + (UInt64.ofNat (s_mid.regs (S2NBignumSSA.v "o3").vname).toNat).toNat * 2 ^ 192
      = S2NBignumSSA.BignumModP25519_4.algoNat a_val := by
  -- Sub-task A (✅): expose per-limb load hypotheses.
  obtain ⟨a0, a1, a2, a3, h_a0, h_a1, h_a2, h_a3, h_a_decomp⟩ :=
    (memNat4_eq_some_iff base_a s.mem a_val).mp h_load_a
  -- Convert functional `bignumExec` to monadic `bignumExecM`,
  -- then apply pre_oi_values_triple via triple_apply_run.
  rw [← BignumExec.bignumExecM_iff_bignumExec] at h_pre_exec
  have h_post := BignumExec.triple_apply_run
    (pre_oi_values_triple base_a a0 a1 a2 a3)
    h_pre_exec
    ⟨h_ap, h_zero, h_a0, h_a1, h_a2, h_a3⟩
  -- The triple's post matches our goal modulo:
  -- (1) `(UInt64.ofNat _.toNat).toNat = _.toNat` (truncating roundtrip
  --     since BitVec 64.toNat < 2^64);
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
