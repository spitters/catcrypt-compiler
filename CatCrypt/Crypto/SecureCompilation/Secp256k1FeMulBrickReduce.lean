/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickFrame
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickProduct
public import CatCrypt.Crypto.Optimizer.SolinasFoldChain

/-!
# The Solinas reduction half of the secp256k1 field-multiply brick

`Secp256k1PointOpFront.feMulHalves` runs an `8 × 8` operand-scanning multiply,
**four** `Secp256k1FeMulFront.genFold` Solinas folds, one ripple subtract of `p`
and a branch-free select. This module gives the four folds, the subtract and the
select their value semantics over `TranslateDialectScalar.semScalar`, at the
generator granularity `Secp256k1FeAddSubBrick` established for the add and
subtract bricks: no emitted command list is reduced.

The product half — the value semantics of `genMul` itself — is stated as the
interface `GenMulSpec` and discharged by `genMulSpec_holds` from
`Secp256k1FeMulBrickProduct.genMul_prod`, so the two halves compose without
either duplicating the other.

## The fold's value

One `genFold` on an `n`-limb list splits it at limb 8, multiplies the high part
by the two-limb constant `c = 2 ^ 32 + 977` and adds the low part back. Every
limb is below `2 ^ 32`, so the low 8 limbs carry `V % 2 ^ 256` and the rest carry
`V / 2 ^ 256`, and the emitted block computes
`ModReduceSelect.solinasFold solinasParamsSecp256k1 V`. The magnitude chain for
four folds and the closing select are in `Optimizer.SolinasFoldChain`.

## Main results

* `GenMulSpec`, `genMulSpec_holds` — the value semantics of `genMul` this module
  consumes, and its discharge from the product half.
* `genMul_len`, `genMul_names` — the result name list of `genMul`, from its loop
  mirror: its length, and that each entry is inside the private prefix, the zero
  slot, or the empty default.
* `foldChi`, `foldCmds`, `foldRes`, `foldLen`, `genFold_split` — one fold's two
  blocks, its result names, and their count.
* `genFold_sem` — one fold's value semantics: the result limbs carry
  `solinasFold solinasParamsSecp256k1` of the input limbs' value.
* `feMulHalves_cmds`, `feMulHalves_sem` — the multiply brick's block
  decomposition and its value semantics.
* `brickStep_mul`, `brickStep` — the per-brick obligation of
  `Secp256k1PointOpFrontDenote` on the `mul` arm, and on all three arms.
* `mulBrickValue_of_heads` — the `Secp256k1FeMulBrickFrame.MulEntry`-shaped value
  statement, for operand and output names outside the brick's own namespace.
* `mulBrickValue_holds` — `Secp256k1FeMulBrickFrame.MulBrickValue` itself, the
  head conditions discharged from the schedule-name conditions it carries.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickReduce

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
  (seqAll mask32 sv genMul genAdd genSub genFold pNat pl32 cc0 cc1)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp emitFOp feH feMulHalves plNames fm fa fs)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (feVal schedNameB FOpSchedOkB)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional (stepFOpG envUpd)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk forIn_range_inv arraySet_inv arrayReplicate_inv arrayToList_getBang
   MulI MulO genMulRun genMulOuterStep genMulInnerStep genMul_eq notTmp_empty)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickFrame (MulEntry MulBrickValue)
open CatCrypt.Crypto.Optimizer.ModReduceSelect
open CatCrypt.Crypto.Optimizer.SolinasFoldChain

/-! ## 1. Name algebra for two-character tags -/

/-- `toString` on a `String` is the identity. -/
theorem toStringStr (s : String) : toString s = s := rfl

theorem hd_empty : hd "" = none := rfl

theorem ne_empty_hd {t : String} {c : Char} (ht : hd t = some c) (w : String) :
    ("" : String) ≠ t ++ w := by
  intro he
  have hx : hd (t ++ w) = some c := hdAppend ht
  simp [← he, hd_empty] at hx

/-- The empty default name is outside every namespace with a first character. -/
theorem outOf_empty {t : String} {c : Char} (ht : hd t = some c) : OutOf t "" :=
  ⟨notTmp_empty, ne_empty_hd ht⟩

/-- Two names under a common prefix whose two-character tags differ in their
    second character. -/
theorem tag2Ne {q t u : String} {a b c e : Char}
    (ht : t.toList = [a, b]) (hu : u.toList = [c, e]) (hbe : b ≠ e) (w v : String) :
    q ++ t ++ w ≠ q ++ u ++ v := by
  intro hEq
  rw [String.append_assoc, String.append_assoc] at hEq
  have h2 := congrArg String.toList ((String.append_right_inj q).mp hEq)
  rw [String.toList_append, String.toList_append, ht, hu] at h2
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h2
  exact hbe h2.2.1

/-- A name under one two-character tag is outside a sibling two-character tag's
    namespace. -/
theorem tag2Out {q : String} {cq : Char} (hq : hd q = some cq) (hcq : cq ≠ '_')
    {t u : String} {a b c e : Char}
    (ht : t.toList = [a, b]) (hu : u.toList = [c, e]) (hbe : b ≠ e) (w : String) :
    OutOf (q ++ u) (q ++ t ++ w) :=
  ⟨(headOk_of_hd (hdAppend (hdAppend hq)) hcq).notTmp,
   fun v => tag2Ne ht hu hbe w v⟩

theorem tl_F1 : ("F1" : String).toList = ['F', '1'] := rfl
theorem tl_F2 : ("F2" : String).toList = ['F', '2'] := rfl
theorem tl_F3 : ("F3" : String).toList = ['F', '3'] := rfl
theorem tl_F4 : ("F4" : String).toList = ['F', '4'] := rfl

theorem hd_F1 : hd "F1" = some 'F' := rfl
theorem hd_F4 : hd "F4" = some 'F' := rfl
theorem hd_Mtag : hd "M" = some 'M' := rfl
theorem hd_mtag : hd "m" = some 'm' := rfl
theorem hd_atag : hd "a" = some 'a' := rfl

/-! ## 2. Limb-list arithmetic -/

/-- Splitting an `accN` at an interior index. -/
theorem accN_add (v : Nat → Nat) (m : Nat) :
    ∀ j, accN v (m + j) = accN v m + 2 ^ (32 * m) * accN (fun k => v (m + k)) j := by
  intro j
  induction j with
  | zero => simp [accN]
  | succ j ih =>
      have h1 : accN v (m + (j + 1)) = accN v (m + j) + 2 ^ (32 * (m + j)) * v (m + j) :=
        accN_succ v (m + j)
      have hg : accN (fun k => v (m + k)) (j + 1)
          = accN (fun k => v (m + k)) j + 2 ^ (32 * j) * v (m + j) := rfl
      have hpow : (2 : Nat) ^ (32 * (m + j)) = 2 ^ (32 * m) * 2 ^ (32 * j) := by
        rw [Nat.mul_add, pow_add]
      rw [h1, ih, hg, hpow]
      ring

/-- An `accN` whose tail entries vanish is the `accN` of its head. -/
theorem accN_ext_zero (v : Nat → Nat) (m : Nat) :
    ∀ j, (∀ k, m ≤ k → k < m + j → v k = 0) → accN v (m + j) = accN v m := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      have h1 : accN v (m + (j + 1)) = accN v (m + j) + 2 ^ (32 * (m + j)) * v (m + j) :=
        accN_succ v (m + j)
      rw [h1, h (m + j) (by omega) (by omega), Nat.mul_zero, Nat.add_zero]
      exact ih (fun k hk _ => h k hk (by omega))

/-- Reading a dropped list at an index. -/
theorem drop_getBang (l : List String) (m k : Nat) : (l.drop m)[k]! = l[m + k]! := by
  induction m generalizing l with
  | zero => simp
  | succ m ih =>
      cases l with
      | nil => simp
      | cons a t =>
          rw [List.drop_succ_cons, ih t,
            show m + 1 + k = (m + k) + 1 from by omega,
            List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
          simp

/-- A list index past the end reads the `getD` default. -/
theorem getD_past (l : List String) (k : Nat) (hk : l.length ≤ k) (d : String) :
    l.getD k d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

/-! ## 3. The operand-scanning multiply: structure and value interface -/

/-- A name a builder's accumulator array under `pfx` can hold: inside `pfx`'s
    namespace, the zero slot, or the empty default. -/
def UnderPfx (zero pfx s : String) : Prop := (∃ w, s = pfx ++ w) ∨ s = zero ∨ s = ""

theorem genMulRun_size (zero : String) (aN bN : List String) (pfx : String) :
    (genMulRun zero aN bN pfx).fst.size = aN.length + bN.length := by
  unfold genMulRun
  refine forIn_range_inv (fun r : MulO => r.fst.size = aN.length + bN.length) _ _ _ ?_ ?_ ?_
  · simp
  · intro i s s' hs hy
    simp only [genMulOuterStep] at hy
    injection hy with hy
    subst hy
    simp only [setBang_size]
    refine forIn_range_inv (fun r : MulI => r.fst.size = aN.length + bN.length) _ _ _ hs ?_ ?_
    · intro j t t' ht hyj
      simp only [genMulInnerStep] at hyj
      injection hyj with hyj
      subst hyj
      simpa [setBang_size] using ht
    · intro j t t' _ hyj
      simp only [genMulInnerStep] at hyj
      injection hyj
  · intro i s s' _ hd
    simp only [genMulOuterStep] at hd
    injection hd

/-- **The operand-scanning multiply returns `|a| + |b|` result names.** -/
theorem genMul_len (zero : String) (aN bN : List String) (pfx : String) :
    (genMul zero aN bN pfx).2.length = aN.length + bN.length := by
  rw [genMul_eq]
  simpa using genMulRun_size zero aN bN pfx

/-- **Each result name of the operand-scanning multiply is inside its private
    prefix's namespace**, the zero slot, or the empty default. -/
theorem genMul_names (zero : String) (aN bN : List String) (pfx : String) (k : Nat) :
    UnderPfx zero pfx ((genMul zero aN bN pfx).2[k]!) := by
  have hp : ∀ i j : Nat, UnderPfx zero pfx s!"{pfx}p{i}_{j}" := fun i j =>
    Or.inl ⟨"p" ++ toString i ++ "_" ++ toString j,
      by simp only [toStringStr, String.append_assoc]⟩
  have hk : ∀ i j : Nat, UnderPfx zero pfx s!"{pfx}k{i}_{j}" := fun i j =>
    Or.inl ⟨"k" ++ toString i ++ "_" ++ toString j,
      by simp only [toStringStr, String.append_assoc]⟩
  have key : ∀ k : Nat, UnderPfx zero pfx ((genMulRun zero aN bN pfx).fst[k]!) := by
    unfold genMulRun
    refine forIn_range_inv (fun r : MulO => ∀ k : Nat, UnderPfx zero pfx (r.fst[k]!))
      _ _ _ ?_ ?_ ?_
    · exact arrayReplicate_inv _ _ (UnderPfx zero pfx) (Or.inr (Or.inl rfl))
        (Or.inr (Or.inr rfl))
    · intro i s s' hs hy
      simp only [genMulOuterStep] at hy
      injection hy with hy
      subst hy
      have hinner : (fun r : MulI =>
          (∀ k : Nat, UnderPfx zero pfx (r.fst[k]!)) ∧ UnderPfx zero pfx r.snd.fst)
          ((forIn [:bN.length] (⟨s.fst, zero, s.snd⟩)
            (genMulInnerStep zero aN bN pfx i) : Id _)) := by
        refine forIn_range_inv (fun r : MulI =>
            (∀ k : Nat, UnderPfx zero pfx (r.fst[k]!)) ∧ UnderPfx zero pfx r.snd.fst)
          _ _ _ ⟨hs, Or.inr (Or.inl rfl)⟩ ?_ ?_
        · intro j t t' ht hyj
          simp only [genMulInnerStep] at hyj
          injection hyj with hyj
          subst hyj
          exact ⟨fun k => arraySet_inv t.fst (i + j) k _ (UnderPfx zero pfx) ht.1 (hp i j),
            hk i j⟩
        · intro j t t' _ hyj
          simp only [genMulInnerStep] at hyj
          injection hyj
      exact fun k =>
        arraySet_inv _ (i + bN.length) k _ (UnderPfx zero pfx) hinner.1 hinner.2
    · intro i s s' _ hd
      simp only [genMulOuterStep] at hd
      injection hd
  rw [genMul_eq]
  show UnderPfx zero pfx ((genMulRun zero aN bN pfx).fst.toList[k]!)
  rw [arrayToList_getBang]
  exact key k

/-- **The value semantics of the operand-scanning multiply.** On an entry
    environment whose operand slots hold 32-bit limbs outside the builder's
    private prefix, the emitted block leaves every name outside that prefix alone,
    its result names hold 32-bit limbs, and their little-endian value is the
    product of the operands' values. The two operand lists carry at most ten
    limbs, the range over which a column's decimal name suffix is injective. -/
def GenMulSpec : Prop :=
  ∀ (aN bN : List String) (pfx : String), HeadOk pfx →
    aN.length ≤ 10 → bN.length ≤ 10 →
    (∀ i, i < aN.length → OutOf pfx (aN[i]!)) →
    (∀ i, i < bN.length → OutOf pfx (bN[i]!)) →
    OutOf pfx "ZZ" →
    ∀ (env env' : SEnvScalar),
      (envReader env "ZZ").toNat = 0 →
      (∀ i, i < aN.length → (envReader env (aN[i]!)).toNat < 2 ^ 32) →
      (∀ i, i < bN.length → (envReader env (bN[i]!)).toNat < 2 ^ 32) →
      semList (genMul "ZZ" aN bN pfx).1 env = some env' →
        (∀ s, OutOf pfx s → envReader env' s = envReader env s)
        ∧ (∀ k, k < aN.length + bN.length →
            (envReader env' ((genMul "ZZ" aN bN pfx).2[k]!)).toNat < 2 ^ 32)
        ∧ accN (fun k => (envReader env' ((genMul "ZZ" aN bN pfx).2[k]!)).toNat)
              (aN.length + bN.length)
            = accN (fun k => (envReader env (aN[k]!)).toNat) aN.length
              * accN (fun k => (envReader env (bN[k]!)).toNat) bN.length

/-- **`GenMulSpec` holds**, by the operand-scanning product at zero slot `"ZZ"`. -/
theorem genMulSpec_holds : GenMulSpec :=
  fun aN bN pfx hp hna hnb hao hbo hzo env env' hz hA hB hsem =>
    Secp256k1FeMulBrickProduct.genMul_prod "ZZ" aN bN pfx hp hna hnb hzo hao hbo
      env env' hz hA hB hsem

/-! ## 4. The constant slots a fold reads -/

/-- The constant slots `Secp256k1PointOpFront.constInit` binds, at their values. -/
structure ConstsAt (env : SEnvScalar) : Prop where
  /-- The zero slot holds `0`. -/
  zero : (envReader env "ZZ").toNat = 0
  /-- The low limb of the Solinas constant holds `977`. -/
  lo : (envReader env "CC0").toNat = cc0
  /-- The high limb of the Solinas constant holds `1`. -/
  hi : (envReader env "CC1").toNat = cc1
  /-- The eight modulus slots hold the 32-bit limbs of `p`. -/
  modulus : ∀ i, i < 8 → (envReader env s!"PL{i}").toNat = pl32.getD i 0

/-- The brick scope pins all four constant slots, so it carries `ConstsAt`. -/
theorem constsAt_of_brickScope {env : SEnvScalar} (h : BrickScope env) : ConstsAt env :=
  ⟨h.zero, h.lo, h.hi, h.modulus⟩

theorem ConstsAt.frame {env : SEnvScalar} {q : String} {cq : Char} (h : ConstsAt env)
    (hq : hd q = some cq) (hZ : 'Z' ≠ cq) (hC : 'C' ≠ cq) (hP : 'P' ≠ cq) {env' : SEnvScalar}
    (hfr : ∀ s, OutOf q s → envReader env' s = envReader env s) :
    ConstsAt env' where
  zero := by rw [hfr _ (outOf_of_hd hq hd_ZZ hZ (by decide))]; exact h.zero
  lo := by rw [hfr _ (outOf_of_hd hq hd_CC0 hC (by decide))]; exact h.lo
  hi := by rw [hfr _ (outOf_of_hd hq hd_CC1 hC (by decide))]; exact h.hi
  modulus := by
    intro i hi
    rw [hfr _ (outOf_of_hd hq (hd_PL i) hP (by decide))]
    exact h.modulus i hi

theorem secpModulus : solinasParamsSecp256k1.modulus = pNat := by
  norm_num [SolinasPrime.modulus, solinasParamsSecp256k1,
    CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront.pNat]

/-! ## 5. One Solinas fold -/

theorem genFold_unfold (zero c0N c1N : String) (full : List String) (pfx : String) :
    genFold zero c0N c1N full pfx =
      if (full.drop 8).isEmpty then ([], full)
      else ((genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).1
              ++ (genAdd zero (full.take 8)
                    (genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).2 (pfx ++ "a")).1,
            (genAdd zero (full.take 8)
              (genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).2 (pfx ++ "a")).2) := rfl

/-- The `c · high` product-limb names of one Solinas fold. -/
def foldChi (full : List String) (pfx : String) : List String :=
  (genMul "ZZ" ["CC0", "CC1"] (full.drop 8) (pfx ++ "m")).2

/-- The commands one Solinas fold emits, for a nonempty high half. -/
def foldCmds (full : List String) (pfx : String) : List LowCT :=
  (genMul "ZZ" ["CC0", "CC1"] (full.drop 8) (pfx ++ "m")).1
    ++ (genAdd "ZZ" (full.take 8) (foldChi full pfx) (pfx ++ "a")).1

/-- The result-limb names of one Solinas fold, for a nonempty high half. -/
def foldRes (full : List String) (pfx : String) : List String :=
  (genAdd "ZZ" (full.take 8) (foldChi full pfx) (pfx ++ "a")).2

/-- The number of limbs one Solinas fold returns from an `n`-limb input. -/
def foldLen (n : Nat) : Nat := max 8 (2 + (n - 8)) + 1

theorem foldChi_names (full : List String) (pfx : String) (i : Nat) :
    UnderPfx "ZZ" (pfx ++ "m") ((foldChi full pfx)[i]!) :=
  genMul_names "ZZ" ["CC0", "CC1"] (full.drop 8) (pfx ++ "m") i

theorem foldChi_len (full : List String) (pfx : String) (n : Nat) (hlen : full.length = n) :
    (foldChi full pfx).length = 2 + (n - 8) := by
  show (genMul "ZZ" ["CC0", "CC1"] (full.drop 8) (pfx ++ "m")).2.length = 2 + (n - 8)
  rw [genMul_len, List.length_drop, hlen]
  rfl

theorem take8_len (full : List String) (n : Nat) (hlen : full.length = n) (hn : 8 ≤ n) :
    (full.take 8).length = 8 := by
  rw [List.length_take, hlen]
  omega

theorem foldRes_len (full : List String) (pfx : String) (n : Nat)
    (hlen : full.length = n) (hn : 8 ≤ n) : (foldRes full pfx).length = foldLen n := by
  show (genAdd "ZZ" (full.take 8) (foldChi full pfx) (pfx ++ "a")).2.length = foldLen n
  rw [genAdd_len, take8_len full n hlen hn, foldChi_len full pfx n hlen, foldLen]

theorem genFold_split (full : List String) (pfx : String) (n : Nat)
    (hlen : full.length = n) (hn : 8 < n) :
    genFold "ZZ" "CC0" "CC1" full pfx = (foldCmds full pfx, foldRes full pfx) := by
  have hd8 : (full.drop 8).length = n - 8 := by rw [List.length_drop, hlen]
  have hne : ¬ ((full.drop 8).isEmpty = true) := by
    simp only [List.isEmpty_iff, ← List.length_eq_zero_iff, hd8]
    omega
  rw [genFold_unfold, ite_eq_right hne]
  rfl

/-- **One Solinas fold computes `solinasFold` of its input limbs' value.** The
    input carries at most eighteen limbs, so its high half is within the
    ten-limb range the operand-scanning multiply's column names cover. -/
theorem genFold_sem (hM : GenMulSpec) (pfx : String) (full : List String) (n : Nat)
    (hlen : full.length = n) (hn : 8 < n) (hn18 : n ≤ 18)
    {cp : Char} (hpo : hd pfx = some cp) (hcp : cp ≠ '_') (hZp : 'Z' ≠ cp) (hCp : 'C' ≠ cp)
    (hout : ∀ k, k < n → OutOf pfx (full[k]!))
    (env env' : SEnvScalar) (hcs : ConstsAt env)
    (hlt : ∀ k, k < n → (envReader env (full[k]!)).toNat < 2 ^ 32)
    (hsem : semList (foldCmds full pfx) env = some env') :
    (∀ s, OutOf pfx s → envReader env' s = envReader env s)
    ∧ (∀ k, k < foldLen n → ∃ w, (foldRes full pfx)[k]! = pfx ++ w)
    ∧ (∀ k, k < foldLen n → (envReader env' ((foldRes full pfx)[k]!)).toNat < 2 ^ 32)
    ∧ accN (fun k => (envReader env' ((foldRes full pfx)[k]!)).toNat) (foldLen n)
        = solinasFold solinasParamsSecp256k1
            (accN (fun k => (envReader env (full[k]!)).toNat) n) := by
  have hq : HeadOk pfx := headOk_of_hd hpo hcp
  have hZ : OutOf pfx "ZZ" := outOf_of_hd hpo hd_ZZ hZp (by decide)
  have hC0 : OutOf pfx "CC0" := outOf_of_hd hpo hd_CC0 hCp (by decide)
  have hC1 : OutOf pfx "CC1" := outOf_of_hd hpo hd_CC1 hCp (by decide)
  have hlo : (full.take 8).length = 8 := take8_len full n hlen (by omega)
  have hhi : (full.drop 8).length = n - 8 := by rw [List.length_drop, hlen]
  have hchiL : (foldChi full pfx).length = 2 + (n - 8) := foldChi_len full pfx n hlen
  have hcc0 : (["CC0", "CC1"] : List String)[0]! = "CC0" := rfl
  have hcc1 : (["CC0", "CC1"] : List String)[1]! = "CC1" := rfl
  have hccLen : (["CC0", "CC1"] : List String).length = 2 := rfl
  -- split the fold into its multiply and add blocks
  rw [foldCmds] at hsem
  obtain ⟨E1, hmc, hac⟩ := splitApp hsem
  -- the constant pair and the high half, as `genMul` operands
  have hccOut : ∀ i, i < (["CC0", "CC1"] : List String).length →
      OutOf (pfx ++ "m") ((["CC0", "CC1"] : List String)[i]!) := by
    intro i hi
    rw [hccLen] at hi
    interval_cases i
    · exact hC0.sub "m"
    · exact hC1.sub "m"
  have hhiOut : ∀ i, i < (full.drop 8).length → OutOf (pfx ++ "m") ((full.drop 8)[i]!) := by
    intro i hi
    rw [hhi] at hi
    exact drop_getBang full 8 i ▸ (hout (8 + i) (by omega)).sub "m"
  have hccLt : ∀ i, i < (["CC0", "CC1"] : List String).length →
      (envReader env ((["CC0", "CC1"] : List String)[i]!)).toNat < 2 ^ 32 := by
    intro i hi
    rw [hccLen] at hi
    interval_cases i
    · simp [hcs.lo, cc0]
    · simp [hcs.hi, cc1]
  have hhiLt : ∀ i, i < (full.drop 8).length →
      (envReader env ((full.drop 8)[i]!)).toNat < 2 ^ 32 := by
    intro i hi
    rw [hhi] at hi
    exact drop_getBang full 8 i ▸ hlt (8 + i) (by omega)
  obtain ⟨fr1, chiLt, chiAcc⟩ :=
    hM ["CC0", "CC1"] (full.drop 8) (pfx ++ "m") (hq.append "m")
      (by rw [hccLen]; omega) (by rw [hhi]; omega) hccOut hhiOut (hZ.sub "m")
      env E1 hcs.zero hccLt hhiLt hmc
  -- the constant pair's value is `c`
  have hcVal : accN (fun k => (envReader env ((["CC0", "CC1"] : List String)[k]!)).toNat) 2
      = solinasParamsSecp256k1.c := by
    simp only [accN, hcc0, hcc1, hcs.lo, hcs.hi]
    norm_num [cc0, cc1, solinasParamsSecp256k1]
  -- the add block
  rw [genAdd_cmds, hlo, hchiL] at hac
  have hZ1 : (envReader E1 "ZZ").toNat = 0 := by
    rw [fr1 _ (hZ.sub "m")]; exact hcs.zero
  have hloO : ∀ i, OutOf (pfx ++ "a") ((full.take 8).getD i "ZZ") := by
    intro i
    by_cases h : i < 8
    · rw [getD_getBang _ i (by rw [hlo]; exact h), take_getBang _ 8 i h]
      exact (hout i (by omega)).sub "a"
    · rw [getD_past _ i (by rw [hlo]; omega)]
      exact hZ.sub "a"
  have hchiO : ∀ i, OutOf (pfx ++ "a") ((foldChi full pfx).getD i "ZZ") := by
    intro i
    by_cases h : i < (foldChi full pfx).length
    · rw [getD_getBang _ i h]
      rcases foldChi_names full pfx i with ⟨w, hw⟩ | hzz | hee
      · rw [hw]; exact sibOut hq hd_mtag hd_atag (by decide) w
      · rw [hzz]; exact hZ.sub "a"
      · rw [hee]; exact outOf_empty (hdAppend hpo)
    · rw [getD_past _ i (by omega)]
      exact hZ.sub "a"
  have hloLt : ∀ i, (envReader E1 ((full.take 8).getD i "ZZ")).toNat < 2 ^ 32 := by
    intro i
    by_cases h : i < 8
    · rw [getD_getBang _ i (by rw [hlo]; exact h), take_getBang _ 8 i h,
        fr1 _ ((hout i (by omega)).sub "m")]
      exact hlt i (by omega)
    · rw [getD_past _ i (by rw [hlo]; omega), hZ1]; norm_num
  have hchiLt : ∀ i, (envReader E1 ((foldChi full pfx).getD i "ZZ")).toNat < 2 ^ 32 := by
    intro i
    by_cases h : i < (foldChi full pfx).length
    · rw [getD_getBang _ i h]
      refine chiLt i ?_
      rw [hccLen, hhi]
      rw [hchiL] at h
      omega
    · rw [getD_past _ i (by omega), hZ1]; norm_num
  obtain ⟨fr2, sLt, cLe, accAdd⟩ :=
    aCmds_sem "ZZ" (full.take 8) (foldChi full pfx) (pfx ++ "a") (hq.append "a")
      (fun i => (hloO i).1) (fun i => (hchiO i).1)
      (fun i w => (hloO i).2 w) (fun i w => (hchiO i).2 w)
      E1 hZ1 hloLt hchiLt (max 8 (2 + (n - 8))) env' hac
  -- the result names
  have hmaxEq : max (full.take 8).length (foldChi full pfx).length = max 8 (2 + (n - 8)) := by
    rw [hlo, hchiL]
  have hresK : ∀ k, k < max 8 (2 + (n - 8)) →
      (foldRes full pfx)[k]! = s!"{pfx ++ "a"}s{k}" := fun k hk =>
    genAdd_name "ZZ" (full.take 8) (foldChi full pfx) (pfx ++ "a") k
      (by rw [hmaxEq]; exact hk)
  have hresN : (foldRes full pfx)[max 8 (2 + (n - 8))]!
      = aCar "ZZ" (pfx ++ "a") (max 8 (2 + (n - 8))) :=
    hmaxEq ▸ genAdd_top "ZZ" (full.take 8) (foldChi full pfx) (pfx ++ "a")
  have hfoldLen : foldLen n = max 8 (2 + (n - 8)) + 1 := rfl
  -- the frame
  have hframe : ∀ s, OutOf pfx s → envReader env' s = envReader env s := by
    intro s hs
    rw [fr2 s (hs.sub "a").1 (hs.sub "a").2, fr1 s (hs.sub "m")]
  -- the result names lie in `pfx`'s namespace
  have hnames : ∀ k, k < foldLen n → ∃ w, (foldRes full pfx)[k]! = pfx ++ w := by
    intro k hk
    rw [hfoldLen] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · refine ⟨"a" ++ "s" ++ toString k, ?_⟩
      rw [hresK k h]
      simp only [toStringStr, String.append_assoc]
    · subst h
      obtain ⟨m, hm⟩ : ∃ m, max 8 (2 + (n - 8)) = m + 1 := ⟨max 8 (2 + (n - 8)) - 1, by omega⟩
      refine ⟨"a" ++ "k" ++ toString m, ?_⟩
      rw [hresN, hm]
      simp only [aCar, toStringStr, String.append_assoc]
  -- the result limbs are 32-bit
  have hrlt : ∀ k, k < foldLen n →
      (envReader env' ((foldRes full pfx)[k]!)).toNat < 2 ^ 32 := by
    intro k hk
    rw [hfoldLen] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · rw [hresK k h]; exact sLt k h
    · subst h; rw [hresN]; exact lt_of_le_of_lt cLe (by norm_num)
  refine ⟨hframe, hnames, hrlt, ?_⟩
  -- the value
  have hsum : accN (fun k => (envReader env' ((foldRes full pfx)[k]!)).toNat) (foldLen n)
      = accN (fun k => (envReader env' s!"{pfx ++ "a"}s{k}").toNat) (max 8 (2 + (n - 8)))
        + 2 ^ (32 * max 8 (2 + (n - 8)))
          * (envReader env' (aCar "ZZ" (pfx ++ "a") (max 8 (2 + (n - 8))))).toNat := by
    rw [hfoldLen, accN_succ,
      accN_congr (max 8 (2 + (n - 8))) (fun k hk => by rw [hresK k hk]), hresN]
  have hlopad : accN (fun k => (envReader E1 ((full.take 8).getD k "ZZ")).toNat)
        (max 8 (2 + (n - 8)))
      = accN (fun k => (envReader env (full[k]!)).toNat) 8 := by
    have hz : ∀ k, 8 ≤ k → k < 8 + (max 8 (2 + (n - 8)) - 8) →
        (envReader E1 ((full.take 8).getD k "ZZ")).toNat = 0 := by
      intro k hk _
      rw [getD_past _ k (by rw [hlo]; omega), hZ1]
    have hx := accN_ext_zero (fun k => (envReader E1 ((full.take 8).getD k "ZZ")).toNat) 8
      (max 8 (2 + (n - 8)) - 8) hz
    rw [show 8 + (max 8 (2 + (n - 8)) - 8) = max 8 (2 + (n - 8)) from by omega] at hx
    rw [hx]
    refine accN_congr 8 (fun k hk => ?_)
    rw [getD_getBang _ k (by rw [hlo]; exact hk), take_getBang _ 8 k hk,
      fr1 _ ((hout k (by omega)).sub "m")]
  have hchipad : accN (fun k => (envReader E1 ((foldChi full pfx).getD k "ZZ")).toNat)
        (max 8 (2 + (n - 8)))
      = accN (fun k => (envReader E1 ((foldChi full pfx)[k]!)).toNat) (2 + (n - 8)) := by
    have hz : ∀ k, 2 + (n - 8) ≤ k →
        k < 2 + (n - 8) + (max 8 (2 + (n - 8)) - (2 + (n - 8))) →
        (envReader E1 ((foldChi full pfx).getD k "ZZ")).toNat = 0 := by
      intro k hk _
      rw [getD_past _ k (by rw [hchiL]; omega), hZ1]
    have hx := accN_ext_zero (fun k => (envReader E1 ((foldChi full pfx).getD k "ZZ")).toNat)
      (2 + (n - 8)) (max 8 (2 + (n - 8)) - (2 + (n - 8))) hz
    rw [show 2 + (n - 8) + (max 8 (2 + (n - 8)) - (2 + (n - 8))) = max 8 (2 + (n - 8))
      from by omega] at hx
    rw [hx]
    refine accN_congr (2 + (n - 8)) (fun k hk => ?_)
    rw [getD_getBang _ k (by rw [hchiL]; exact hk)]
  have hchiV : accN (fun k => (envReader E1 ((foldChi full pfx)[k]!)).toNat) (2 + (n - 8))
      = solinasParamsSecp256k1.c
        * accN (fun k => (envReader env ((full.drop 8)[k]!)).toNat) (n - 8) := by
    simpa only [hccLen, hhi, hcVal] using! chiAcc
  -- the input value splits at limb 8
  have hVsplit : accN (fun k => (envReader env (full[k]!)).toNat) n
      = accN (fun k => (envReader env (full[k]!)).toNat) 8
        + 2 ^ (32 * 8) * accN (fun k => (envReader env ((full.drop 8)[k]!)).toNat) (n - 8) := by
    have hx := accN_add (fun k => (envReader env (full[k]!)).toNat) 8 (n - 8)
    rw [show 8 + (n - 8) = n from by omega] at hx
    have hdc : accN (fun k => (envReader env (full[8 + k]!)).toNat) (n - 8)
        = accN (fun k => (envReader env ((full.drop 8)[k]!)).toNat) (n - 8) :=
      accN_congr (n - 8) (fun k _ => by rw [drop_getBang])
    rw [hx, hdc]
  have hlow : accN (fun k => (envReader env (full[k]!)).toNat) 8 < 2 ^ (32 * 8) :=
    accN_lt _ 8 (fun k hk => hlt k (by omega))
  have hpow : (2 : Nat) ^ (32 * 8) = 2 ^ solinasParamsSecp256k1.k := by
    norm_num [solinasParamsSecp256k1]
  have hmodv : accN (fun k => (envReader env (full[k]!)).toNat) n
        % 2 ^ solinasParamsSecp256k1.k
      = accN (fun k => (envReader env (full[k]!)).toNat) 8 := by
    rw [← hpow, hVsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hdivv : accN (fun k => (envReader env (full[k]!)).toNat) n
        / 2 ^ solinasParamsSecp256k1.k
      = accN (fun k => (envReader env ((full.drop 8)[k]!)).toNat) (n - 8) := by
    rw [← hpow, hVsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (32 * 8)),
      Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [hsum, accAdd, hlopad, hchipad, hchiV, solinasFold, hmodv, hdivv]
  ring

/-! ## 6. The multiply brick's blocks -/

/-- The 16 product-limb names of the multiply brick. -/
def mulProd (q : String) (A B : List String) : List String := (genMul "ZZ" A B (q ++ "M")).2

/-- The limb names after the first Solinas fold. -/
def mulR1 (q : String) (A B : List String) : List String :=
  (genFold "ZZ" "CC0" "CC1" (mulProd q A B) (q ++ "F1")).2

/-- The limb names after the second Solinas fold. -/
def mulR2 (q : String) (A B : List String) : List String :=
  (genFold "ZZ" "CC0" "CC1" (mulR1 q A B) (q ++ "F2")).2

/-- The limb names after the third Solinas fold. -/
def mulR3 (q : String) (A B : List String) : List String :=
  (genFold "ZZ" "CC0" "CC1" (mulR2 q A B) (q ++ "F3")).2

/-- The limb names after the fourth Solinas fold. -/
def mulR4 (q : String) (A B : List String) : List String :=
  (genFold "ZZ" "CC0" "CC1" (mulR3 q A B) (q ++ "F4")).2

/-- The eight low limbs the trial subtract reads. -/
def mulLo8 (q : String) (A B : List String) : List String := (mulR4 q A B).take 8

/-- The trial subtract of `p` inside the multiply brick. -/
def mulSub (q : String) (A B : List String) : List LowCT × List String × String :=
  genSub "ZZ" (mulLo8 q A B) plNames (q ++ "S")

/-- The multiply, the four folds and the trial subtract, concatenated. -/
def mulBlocks (q : String) (A B : List String) : List LowCT :=
  (genMul "ZZ" A B (q ++ "M")).1
    ++ (genFold "ZZ" "CC0" "CC1" (mulProd q A B) (q ++ "F1")).1
    ++ (genFold "ZZ" "CC0" "CC1" (mulR1 q A B) (q ++ "F2")).1
    ++ (genFold "ZZ" "CC0" "CC1" (mulR2 q A B) (q ++ "F3")).1
    ++ (genFold "ZZ" "CC0" "CC1" (mulR3 q A B) (q ++ "F4")).1
    ++ (mulSub q A B).1

theorem feMulHalves_cmds (q : String) (A B : List String) :
    (feMulHalves q A B).1
      = selCmds q (rNamesOf q) (mulLo8 q A B) (mulSub q A B).2.1
          (mulBlocks q A B ++ maskCmds q (mulSub q A B).2.2) 8 := by
  rw [show (feMulHalves q A B).1
      = (forIn [:8] (mulBlocks q A B ++ maskCmds q (mulSub q A B).2.2)
          (fun i cmds => ForInStep.yield
            (cmds ++ [selOne q (rNamesOf q) (mulLo8 q A B) (mulSub q A B).2.1 i]))
          : Id (List LowCT)) from rfl]
  exact selCmds_run _ _ _ _ _ _

theorem feMulHalves_names (q : String) (A B : List String) :
    (feMulHalves q A B).2 = rNamesOf q := rfl

/-! ## 7. The multiply brick's value semantics -/

/-- **The multiply brick realizes `fm` on the operands' half-limb readout.** The
    four folds land the product below `2 ^ 256` and the conditional subtract
    canonicalises it; every name outside the brick's private prefix is
    untouched. -/
theorem feMulHalves_sem_gen (hM : GenMulSpec) (q a b : String) {cq : Char}
    (hq : hd q = some cq) (hcq : cq ≠ '_')
    (hZq : 'Z' ≠ cq) (hCq : 'C' ≠ cq) (hPq : 'P' ≠ cq)
    (hZout : OutOf q "ZZ")
    (hPout : ∀ i : Nat, OutOf q s!"PL{i}")
    (hAout : ∀ k, k < (feH a).length → OutOf q ((feH a)[k]!))
    (hBout : ∀ k, k < (feH b).length → OutOf q ((feH b)[k]!))
    (env env' : SEnvScalar) (hcs : ConstsAt env)
    (hAlt : ∀ k, k < 8 → (envReader env (feHN a k)).toNat < 2 ^ 32)
    (hBlt : ∀ k, k < 8 → (envReader env (feHN b k)).toNat < 2 ^ 32)
    (hAc : accN (fun k => (envReader env (feHN a k)).toNat) 8 < pNat)
    (hBc : accN (fun k => (envReader env (feHN b k)).toNat) 8 < pNat)
    (hsem : semList (feMulHalves q (feH a) (feH b)).1 env = some env') :
    (∀ s, OutOf q s → envReader env' s = envReader env s)
    ∧ (∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat < 2 ^ 32)
    ∧ accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8
        = fm (accN (fun k => (envReader env (feHN a k)).toNat) 8)
             (accN (fun k => (envReader env (feHN b k)).toNat) 8) := by
  have hqok : HeadOk q := headOk_of_hd hq hcq
  -- split the brick into its blocks
  rw [feMulHalves_cmds, selCmds_split] at hsem
  obtain ⟨E7, hpre, hsel⟩ := splitApp hsem
  obtain ⟨E6, hblocks, hmask⟩ := splitApp hpre
  rw [mulBlocks] at hblocks
  obtain ⟨E5, hb5, hsub⟩ := splitApp hblocks
  obtain ⟨E4, hb4, hf4⟩ := splitApp hb5
  obtain ⟨E3, hb3, hf3⟩ := splitApp hb4
  obtain ⟨E2, hb2, hf2⟩ := splitApp hb3
  obtain ⟨E1, hmul, hf1⟩ := splitApp hb2
  -- block 1: the 8 x 8 operand-scanning multiply
  obtain ⟨fr1, prodLt, prodAcc⟩ :=
    hM (feH a) (feH b) (q ++ "M") (hqok.append "M")
      (by rw [feH_len a]; omega) (by rw [feH_len b]; omega)
      (fun i hi => (hAout i hi).sub "M") (fun i hi => (hBout i hi).sub "M")
      (hZout.sub "M") env E1 hcs.zero
      (fun i hi => by
        rw [feH_len a] at hi
        rw [feH_getBang a i hi]
        exact hAlt i hi)
      (fun i hi => by
        rw [feH_len b] at hi
        rw [feH_getBang b i hi]
        exact hBlt i hi)
      hmul
  have hprodLen : (mulProd q (feH a) (feH b)).length = 16 := by
    show (genMul "ZZ" (feH a) (feH b) (q ++ "M")).2.length = 16
    rw [genMul_len, feH_len a, feH_len b]
  have hprodLt : ∀ k, k < 16 →
      (envReader E1 ((mulProd q (feH a) (feH b))[k]!)).toNat < 2 ^ 32 := by
    intro k hk
    refine prodLt k ?_
    rw [feH_len a, feH_len b]
    omega
  have hprodAcc : accN (fun k => (envReader E1 ((mulProd q (feH a) (feH b))[k]!)).toNat) 16
      = accN (fun k => (envReader env (feHN a k)).toNat) 8
        * accN (fun k => (envReader env (feHN b k)).toNat) 8 := by
    have hx := prodAcc
    rw [feH_len a, feH_len b, show (8 : Nat) + 8 = 16 from by norm_num,
      show (genMul "ZZ" (feH a) (feH b) (q ++ "M")).2 = mulProd q (feH a) (feH b) from rfl] at hx
    -- Both `accN_congr` arguments are stated in full: left implicit, `rw` picks
    -- the operand-name form on the wrong side of the equation.
    have hA8 : accN (fun k => (envReader env ((feH a)[k]!)).toNat) 8
        = accN (fun k => (envReader env (feHN a k)).toNat) 8 :=
      accN_congr 8 (fun k hk => by rw [feH_getBang a k hk])
    have hB8 : accN (fun k => (envReader env ((feH b)[k]!)).toNat) 8
        = accN (fun k => (envReader env (feHN b k)).toNat) 8 :=
      accN_congr 8 (fun k hk => by rw [feH_getBang b k hk])
    rw [hx, hA8, hB8]
  have hprodOut : ∀ k, k < 16 → OutOf (q ++ "F1") ((mulProd q (feH a) (feH b))[k]!) := by
    intro k _
    show OutOf (q ++ "F1") ((genMul "ZZ" (feH a) (feH b) (q ++ "M")).2[k]!)
    rcases genMul_names "ZZ" (feH a) (feH b) (q ++ "M") k with ⟨w, hw⟩ | hzz | hee
    · rw [hw]; exact sibOut hqok hd_Mtag hd_F1 (by decide) w
    · rw [hzz]; exact hZout.sub "F1"
    · rw [hee]; exact outOf_empty (hdAppend hq)
  have hcs1 : ConstsAt E1 := hcs.frame hq hZq hCq hPq (fun s hs => fr1 s (hs.sub "M"))
  -- fold 1
  have hsp1 := genFold_split (mulProd q (feH a) (feH b)) (q ++ "F1") 16 hprodLen (by omega)
  rw [show (genFold "ZZ" "CC0" "CC1" (mulProd q (feH a) (feH b)) (q ++ "F1")).1
      = foldCmds (mulProd q (feH a) (feH b)) (q ++ "F1") from congrArg Prod.fst hsp1] at hf1
  have hr1eq : mulR1 q (feH a) (feH b) = foldRes (mulProd q (feH a) (feH b)) (q ++ "F1") := by
    show (genFold "ZZ" "CC0" "CC1" (mulProd q (feH a) (feH b)) (q ++ "F1")).2 = _
    rw [hsp1]
  obtain ⟨g1fr, g1nm, g1lt, g1acc⟩ :=
    genFold_sem hM (q ++ "F1") (mulProd q (feH a) (feH b)) 16 hprodLen (by omega) (by omega)
      (hdAppend hq) hcq hZq hCq hprodOut E1 E2 hcs1 hprodLt hf1
  have hr1len : (mulR1 q (feH a) (feH b)).length = 11 := by
    norm_num [hr1eq, foldRes_len _ _ 16 hprodLen (by omega), foldLen]
  have hr1nm : ∀ k, k < 11 → ∃ w, (mulR1 q (feH a) (feH b))[k]! = (q ++ "F1") ++ w :=
    fun k hk => hr1eq ▸ g1nm k (by rw [foldLen]; omega)
  have hr1lt : ∀ k, k < 11 → (envReader E2 ((mulR1 q (feH a) (feH b))[k]!)).toNat < 2 ^ 32 :=
    fun k hk => hr1eq ▸ g1lt k (by rw [foldLen]; omega)
  have hr1acc : accN (fun k => (envReader E2 ((mulR1 q (feH a) (feH b))[k]!)).toNat) 11
      = solinasFold solinasParamsSecp256k1
          (accN (fun k => (envReader E1 ((mulProd q (feH a) (feH b))[k]!)).toNat) 16) := by
    rw [hr1eq]
    simpa only [show foldLen 16 = 11 from by norm_num [foldLen]] using g1acc
  have hr1out : ∀ k, k < 11 → OutOf (q ++ "F2") ((mulR1 q (feH a) (feH b))[k]!) := by
    intro k hk
    obtain ⟨w, hw⟩ := hr1nm k hk
    exact hw ▸ tag2Out hq hcq tl_F1 tl_F2 (by decide) w
  have hcs2 : ConstsAt E2 := hcs1.frame (hdAppend hq) hZq hCq hPq g1fr
  -- fold 2
  have hsp2 := genFold_split (mulR1 q (feH a) (feH b)) (q ++ "F2") 11 hr1len (by omega)
  rw [show (genFold "ZZ" "CC0" "CC1" (mulR1 q (feH a) (feH b)) (q ++ "F2")).1
      = foldCmds (mulR1 q (feH a) (feH b)) (q ++ "F2") from congrArg Prod.fst hsp2] at hf2
  have hr2eq : mulR2 q (feH a) (feH b) = foldRes (mulR1 q (feH a) (feH b)) (q ++ "F2") := by
    show (genFold "ZZ" "CC0" "CC1" (mulR1 q (feH a) (feH b)) (q ++ "F2")).2 = _
    rw [hsp2]
  obtain ⟨g2fr, g2nm, g2lt, g2acc⟩ :=
    genFold_sem hM (q ++ "F2") (mulR1 q (feH a) (feH b)) 11 hr1len (by omega) (by omega)
      (hdAppend hq) hcq hZq hCq hr1out E2 E3 hcs2 hr1lt hf2
  have hr2len : (mulR2 q (feH a) (feH b)).length = 9 := by
    norm_num [hr2eq, foldRes_len _ _ 11 hr1len (by omega), foldLen]
  have hr2nm : ∀ k, k < 9 → ∃ w, (mulR2 q (feH a) (feH b))[k]! = (q ++ "F2") ++ w :=
    fun k hk => hr2eq ▸ g2nm k (by rw [foldLen]; omega)
  have hr2lt : ∀ k, k < 9 → (envReader E3 ((mulR2 q (feH a) (feH b))[k]!)).toNat < 2 ^ 32 :=
    fun k hk => hr2eq ▸ g2lt k (by rw [foldLen]; omega)
  have hr2acc : accN (fun k => (envReader E3 ((mulR2 q (feH a) (feH b))[k]!)).toNat) 9
      = solinasFold solinasParamsSecp256k1
          (accN (fun k => (envReader E2 ((mulR1 q (feH a) (feH b))[k]!)).toNat) 11) := by
    rw [hr2eq]
    simpa only [show foldLen 11 = 9 from by norm_num [foldLen]] using g2acc
  have hr2out : ∀ k, k < 9 → OutOf (q ++ "F3") ((mulR2 q (feH a) (feH b))[k]!) := by
    intro k hk
    obtain ⟨w, hw⟩ := hr2nm k hk
    exact hw ▸ tag2Out hq hcq tl_F2 tl_F3 (by decide) w
  have hcs3 : ConstsAt E3 := hcs2.frame (hdAppend hq) hZq hCq hPq g2fr
  -- fold 3
  have hsp3 := genFold_split (mulR2 q (feH a) (feH b)) (q ++ "F3") 9 hr2len (by omega)
  rw [show (genFold "ZZ" "CC0" "CC1" (mulR2 q (feH a) (feH b)) (q ++ "F3")).1
      = foldCmds (mulR2 q (feH a) (feH b)) (q ++ "F3") from congrArg Prod.fst hsp3] at hf3
  have hr3eq : mulR3 q (feH a) (feH b) = foldRes (mulR2 q (feH a) (feH b)) (q ++ "F3") := by
    show (genFold "ZZ" "CC0" "CC1" (mulR2 q (feH a) (feH b)) (q ++ "F3")).2 = _
    rw [hsp3]
  obtain ⟨g3fr, g3nm, g3lt, g3acc⟩ :=
    genFold_sem hM (q ++ "F3") (mulR2 q (feH a) (feH b)) 9 hr2len (by omega) (by omega)
      (hdAppend hq) hcq hZq hCq hr2out E3 E4 hcs3 hr2lt hf3
  have hr3len : (mulR3 q (feH a) (feH b)).length = 9 := by
    norm_num [hr3eq, foldRes_len _ _ 9 hr2len (by omega), foldLen]
  have hr3nm : ∀ k, k < 9 → ∃ w, (mulR3 q (feH a) (feH b))[k]! = (q ++ "F3") ++ w :=
    fun k hk => hr3eq ▸ g3nm k (by rw [foldLen]; omega)
  have hr3lt : ∀ k, k < 9 → (envReader E4 ((mulR3 q (feH a) (feH b))[k]!)).toNat < 2 ^ 32 :=
    fun k hk => hr3eq ▸ g3lt k (by rw [foldLen]; omega)
  have hr3acc : accN (fun k => (envReader E4 ((mulR3 q (feH a) (feH b))[k]!)).toNat) 9
      = solinasFold solinasParamsSecp256k1
          (accN (fun k => (envReader E3 ((mulR2 q (feH a) (feH b))[k]!)).toNat) 9) := by
    rw [hr3eq]
    simpa only [show foldLen 9 = 9 from by norm_num [foldLen]] using g3acc
  have hr3out : ∀ k, k < 9 → OutOf (q ++ "F4") ((mulR3 q (feH a) (feH b))[k]!) := by
    intro k hk
    obtain ⟨w, hw⟩ := hr3nm k hk
    exact hw ▸ tag2Out hq hcq tl_F3 tl_F4 (by decide) w
  have hcs4 : ConstsAt E4 := hcs3.frame (hdAppend hq) hZq hCq hPq g3fr
  -- fold 4
  have hsp4 := genFold_split (mulR3 q (feH a) (feH b)) (q ++ "F4") 9 hr3len (by omega)
  rw [show (genFold "ZZ" "CC0" "CC1" (mulR3 q (feH a) (feH b)) (q ++ "F4")).1
      = foldCmds (mulR3 q (feH a) (feH b)) (q ++ "F4") from congrArg Prod.fst hsp4] at hf4
  have hr4eq : mulR4 q (feH a) (feH b) = foldRes (mulR3 q (feH a) (feH b)) (q ++ "F4") := by
    show (genFold "ZZ" "CC0" "CC1" (mulR3 q (feH a) (feH b)) (q ++ "F4")).2 = _
    rw [hsp4]
  obtain ⟨g4fr, g4nm, g4lt, g4acc⟩ :=
    genFold_sem hM (q ++ "F4") (mulR3 q (feH a) (feH b)) 9 hr3len (by omega) (by omega)
      (hdAppend hq) hcq hZq hCq hr3out E4 E5 hcs4 hr3lt hf4
  have hr4len : (mulR4 q (feH a) (feH b)).length = 9 := by
    norm_num [hr4eq, foldRes_len _ _ 9 hr3len (by omega), foldLen]
  have hr4nm : ∀ k, k < 9 → ∃ w, (mulR4 q (feH a) (feH b))[k]! = (q ++ "F4") ++ w :=
    fun k hk => hr4eq ▸ g4nm k (by rw [foldLen]; omega)
  have hr4lt : ∀ k, k < 9 → (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat < 2 ^ 32 :=
    fun k hk => hr4eq ▸ g4lt k (by rw [foldLen]; omega)
  have hr4acc : accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9
      = solinasFold solinasParamsSecp256k1
          (accN (fun k => (envReader E4 ((mulR3 q (feH a) (feH b))[k]!)).toNat) 9) := by
    rw [hr4eq]
    simpa only [show foldLen 9 = 9 from by norm_num [foldLen]] using g4acc
  have hcs5 : ConstsAt E5 := hcs4.frame (hdAppend hq) hZq hCq hPq g4fr
  -- the four-fold value and its magnitude
  have hchain : accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9
      = solinasFold solinasParamsSecp256k1 (solinasFold solinasParamsSecp256k1
          (solinasFold solinasParamsSecp256k1 (solinasFold solinasParamsSecp256k1
            (accN (fun k => (envReader env (feHN a k)).toNat) 8
              * accN (fun k => (envReader env (feHN b k)).toNat) 8)))) := by
    rw [hr4acc, hr3acc, hr2acc, hr1acc, hprodAcc]
  have hpsmall : pNat < 2 ^ 256 := by
    norm_num [CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront.pNat]
  have hW4lt : accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9
      < 2 ^ 256 := by
    rw [hchain]
    exact secpFourFold_lt (by omega) (by omega)
  have hr49 : accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9
      = accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 8
        + 2 ^ (32 * 8) * (envReader E5 ((mulR4 q (feH a) (feH b))[8]!)).toNat := accN_succ _ 8
  have hlow8 : accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 8
      < 2 ^ (32 * 8) := accN_lt _ 8 (fun k hk => hr4lt k (by omega))
  have hp256 : (2 : Nat) ^ (32 * 8) = 2 ^ 256 := by norm_num
  have htop : (envReader E5 ((mulR4 q (feH a) (feH b))[8]!)).toNat = 0 := by
    by_contra h
    have h2 : (2 : Nat) ^ (32 * 8)
        ≤ 2 ^ (32 * 8) * (envReader E5 ((mulR4 q (feH a) (feH b))[8]!)).toNat :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)
    omega
  have hlo8val : accN (fun k => (envReader E5 ((mulLo8 q (feH a) (feH b))[k]!)).toNat) 8
      = accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9 := by
    rw [hr49, htop, Nat.mul_zero, Nat.add_zero]
    exact accN_congr 8 (fun k hk => by
      show (envReader E5 ((mulR4 q (feH a) (feH b)).take 8)[k]!).toNat = _
      rw [take_getBang _ 8 k hk])
  -- the trial subtract of `p`
  have hlo8len : (mulLo8 q (feH a) (feH b)).length = 8 := by
    show ((mulR4 q (feH a) (feH b)).take 8).length = 8
    simp [List.length_take, hr4len]
  have hlo8out : ∀ i, i < 8 → OutOf (q ++ "S") ((mulLo8 q (feH a) (feH b))[i]!) := by
    intro i hi
    show OutOf (q ++ "S") (((mulR4 q (feH a) (feH b)).take 8)[i]!)
    rw [take_getBang _ 8 i hi]
    obtain ⟨w, hw⟩ := hr4nm i (by omega)
    exact hw ▸ sibOut hqok hd_F4 hd_S (by decide) w
  have hlo8lt : ∀ i, i < 8 → (envReader E5 ((mulLo8 q (feH a) (feH b))[i]!)).toNat < 2 ^ 32 := by
    intro i hi
    show (envReader E5 (((mulR4 q (feH a) (feH b)).take 8)[i]!)).toNat < 2 ^ 32
    exact take_getBang (mulR4 q (feH a) (feH b)) 8 i hi ▸ hr4lt i (by omega)
  rw [mulSub, genSub_cmds, hlo8len] at hsub
  obtain ⟨fr6, dLt, bLe, accSub⟩ :=
    sCmds_sem "ZZ" (mulLo8 q (feH a) (feH b)) plNames (q ++ "S") 8 (hqok.append "S")
      (fun i hi => (hlo8out i hi).1)
      (fun i hi => by
        rw [getD_getBang _ i (by rw [plNames_len]; exact hi), plNames_getBang i hi]
        exact ((hPout i).sub "S").1)
      (fun i w hi => (hlo8out i hi).2 w)
      (fun i w hi => by
        rw [getD_getBang _ i (by rw [plNames_len]; exact hi), plNames_getBang i hi]
        exact ((hPout i).sub "S").2 w)
      E5 hcs5.zero hlo8lt
      (fun i hi => by
        rw [getD_getBang _ i (by rw [plNames_len]; exact hi), plNames_getBang i hi,
          hcs5.modulus i hi]
        exact pl32_lt i)
      8 (le_refl 8) E6 hsub
  have hplsum : accN (fun k => (envReader E5 (plNames.getD k "ZZ")).toNat) 8 = pNat :=
    (accN_congr 8 (fun k hk => by
      rw [getD_getBang _ k (by rw [plNames_len]; exact hk), plNames_getBang k hk,
        hcs5.modulus k hk])).trans accN_pl32
  have hbwname : (mulSub q (feH a) (feH b)).2.2 = sBor "ZZ" (q ++ "S") 8 := by
    show (genSub "ZZ" (mulLo8 q (feH a) (feH b)) plNames (q ++ "S")).2.2 = sBor "ZZ" (q ++ "S") 8
    rw [genSub_borrow, hlo8len]
  have hdk : ∀ k, k < 8 → (mulSub q (feH a) (feH b)).2.1[k]! = s!"{q ++ "S"}d{k}" := fun k hk =>
    genSub_name "ZZ" (mulLo8 q (feH a) (feH b)) plNames (q ++ "S") k (by rw [hlo8len]; exact hk)
  have hDlt : accN (fun k => (envReader E6 s!"{q ++ "S"}d{k}").toNat) 8 < 2 ^ (32 * 8) :=
    accN_lt _ 8 (fun k hk => dLt k hk)
  have hbal : accN (fun k => (envReader E6 s!"{q ++ "S"}d{k}").toNat) 8
        + solinasParamsSecp256k1.modulus
      = accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9
        + 2 ^ 256 * (envReader E6 (sBor "ZZ" (q ++ "S") 8)).toNat := by
    simpa only [hplsum, hlo8val, ← secpModulus, hp256] using accSub
  -- the branch-free masks
  rw [hbwname] at hmask
  obtain ⟨frM, mask1, mask0⟩ :=
    maskCmds_sem q (sBor "ZZ" (q ++ "S") 8) hqok (KeepMask q)
      (fun s hs => hs.1) (fun s hs => hs.2.1) (fun s hs => hs.2.2.1) (fun s hs => hs.2.2.2)
      E6 E7 hmask
  have hlo8keepM : ∀ k, k < 8 → KeepMask q ((mulLo8 q (feH a) (feH b))[k]!) := by
    intro k hk
    show KeepMask q (((mulR4 q (feH a) (feH b)).take 8)[k]!)
    rw [take_getBang _ 8 k hk]
    obtain ⟨w, hw⟩ := hr4nm k (by omega)
    exact hw ▸ keepMask_sub hqok hd_F4 (by decide) (by decide) w
  have hlo8keepS : ∀ k, k < 8 → KeepSel q ((mulLo8 q (feH a) (feH b))[k]!) := by
    intro k hk
    show KeepSel q (((mulR4 q (feH a) (feH b)).take 8)[k]!)
    rw [take_getBang _ 8 k hk]
    obtain ⟨w, hw⟩ := hr4nm k (by omega)
    exact hw ▸ keepSel_sub hqok hd_F4 (by decide) w
  have hdkeepM : ∀ k, k < 8 → KeepMask q ((mulSub q (feH a) (feH b)).2.1[k]!) := by
    intro k hk
    rw [hdk k hk]
    show KeepMask q (q ++ "S" ++ "d" ++ toString k)
    rw [nameAssoc]
    exact keepMask_sub hqok hd_S (by decide) (by decide) _
  have hdkeepS : ∀ k, k < 8 → KeepSel q ((mulSub q (feH a) (feH b)).2.1[k]!) := by
    intro k hk
    rw [hdk k hk]
    show KeepSel q (q ++ "S" ++ "d" ++ toString k)
    rw [nameAssoc]
    exact keepSel_sub hqok hd_S (by decide) _
  have hlo8E7 : ∀ k, k < 8 → envReader E7 ((mulLo8 q (feH a) (feH b))[k]!)
      = envReader E5 ((mulLo8 q (feH a) (feH b))[k]!) := by
    intro k hk
    rw [frM _ (hlo8keepM k hk), fr6 _ (hlo8out k hk).1 (hlo8out k hk).2]
  have hdE7 : ∀ k, k < 8 → envReader E7 ((mulSub q (feH a) (feH b)).2.1[k]!)
      = envReader E6 ((mulSub q (feH a) (feH b)).2.1[k]!) := fun k hk => frM _ (hdkeepM k hk)
  -- the branch-free select
  obtain ⟨frS, selv⟩ :=
    selBody_sem q (rNamesOf q) (mulLo8 q (feH a) (feH b)) (mulSub q (feH a) (feH b)).2.1 8
      (KeepSel q)
      (fun i hi => by
        rw [rNamesOf_getBang q i hi]
        exact (headOk_of_hd (hdAppend (hdAppend hq)) hcq).notTmp)
      (fun i j hi hj hij => by
        rw [rNamesOf_getBang q i hi, rNamesOf_getBang q j hj]; exact nmNe q (idxNe "R" hij))
      (fun i hi s hs => by rw [rNamesOf_getBang q i hi]; exact hs.2 i hi)
      (fun s hs => hs.1) hlo8keepS hdkeepS (keepSel_mm hqok) (keepSel_nm hqok)
      E7 8 (le_refl 8) env' hsel
  -- the frame
  have hframe : ∀ s, OutOf q s → envReader env' s = envReader env s := by
    intro s hs
    rw [frS s (keepSel_out hs), frM s (keepMask_out hs),
      fr6 s (hs.sub "S").1 (hs.sub "S").2, g4fr s (hs.sub "F4"), g3fr s (hs.sub "F3"),
      g2fr s (hs.sub "F2"), g1fr s (hs.sub "F1"), fr1 s (hs.sub "M")]
  -- the two branches of the select
  have hfm : fm (accN (fun k => (envReader env (feHN a k)).toNat) 8)
      (accN (fun k => (envReader env (feHN b k)).toNat) 8)
      = (accN (fun k => (envReader env (feHN a k)).toNat) 8
          * accN (fun k => (envReader env (feHN b k)).toNat) 8) % pNat := rfl
  have hres : (∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat < 2 ^ 32)
      ∧ accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8
          = (accN (fun k => (envReader env (feHN a k)).toNat) 8
              * accN (fun k => (envReader env (feHN b k)).toNat) 8) % pNat := by
    rcases (by omega : (envReader E6 (sBor "ZZ" (q ++ "S") 8)).toNat = 0
        ∨ (envReader E6 (sBor "ZZ" (q ++ "S") 8)).toNat = 1) with hbv | hbv
    · obtain ⟨hmm, hnm⟩ := mask0 hbv
      have hR : ∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat
          = (envReader E6 s!"{q ++ "S"}d{k}").toNat := by
        intro k hk
        have hs := selv k hk
        rw [rNamesOf_getBang q k hk] at hs
        rw [hs, hmm, hnm, hdE7 k hk, hdk k hk]
        exact selRight (dLt k hk)
      have hacc : accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8
          = accN (fun k => (envReader E6 s!"{q ++ "S"}d{k}").toNat) 8 :=
        accN_congr 8 (fun k hk => hR k hk)
      obtain ⟨hlt', hmod'⟩ :=
        secpSelect (V := accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9)
          (D := accN (fun k => (envReader E6 s!"{q ++ "S"}d{k}").toNat) 8) (b := 0)
          (R := accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8)
          hW4lt (by rw [hp256] at hDlt; exact hDlt) (by omega)
          (by rw [hbv] at hbal; exact hbal) (by intro h; exact absurd h (by decide))
          (fun _ => hacc)
      rw [secpModulus] at hlt' hmod'
      refine ⟨fun k hk => by rw [hR k hk]; exact dLt k hk, ?_⟩
      rw [Nat.mod_eq_of_lt hlt'] at hmod'
      rw [hmod', hchain, ← secpModulus, secpFourFold_mod]
    · obtain ⟨hmm, hnm⟩ := mask1 hbv
      have hR : ∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat
          = (envReader E5 ((mulLo8 q (feH a) (feH b))[k]!)).toNat := by
        intro k hk
        have hs := selv k hk
        rw [rNamesOf_getBang q k hk] at hs
        rw [hs, hmm, hnm, hlo8E7 k hk]
        exact selLeft (hlo8lt k hk)
      have hacc : accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8
          = accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9 :=
        (accN_congr 8 (fun k hk => hR k hk)).trans hlo8val
      obtain ⟨hlt', hmod'⟩ :=
        secpSelect (V := accN (fun k => (envReader E5 ((mulR4 q (feH a) (feH b))[k]!)).toNat) 9)
          (D := accN (fun k => (envReader E6 s!"{q ++ "S"}d{k}").toNat) 8) (b := 1)
          (R := accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8)
          hW4lt (by rw [hp256] at hDlt; exact hDlt) (by omega)
          (by rw [hbv] at hbal; exact hbal) (fun _ => hacc)
          (by intro h; exact absurd h (by decide))
      rw [secpModulus] at hlt' hmod'
      refine ⟨fun k hk => by rw [hR k hk]; exact hlo8lt k hk, ?_⟩
      rw [Nat.mod_eq_of_lt hlt'] at hmod'
      rw [hmod', hchain, ← secpModulus, secpFourFold_mod]
  exact ⟨hframe, hres.1, by rw [hres.2, hfm]⟩

/-- The multiply brick realizes `fm` at the head-`'o'` output/operand separation,
    where the output name has head `'o'` and each operand head differs from `'o'`.
    A specialization of `feMulHalves_sem_gen`. -/
theorem feMulHalves_sem (hM : GenMulSpec) (q a b : String) {ca cb : Char}
    (hq : hd q = some 'o')
    (hda : hd a = some ca) (hca : ca ≠ 'o') (hca' : ca ≠ '_')
    (hdb : hd b = some cb) (hcb : cb ≠ 'o') (hcb' : cb ≠ '_')
    (env env' : SEnvScalar) (hcs : ConstsAt env)
    (hAlt : ∀ k, k < 8 → (envReader env (feHN a k)).toNat < 2 ^ 32)
    (hBlt : ∀ k, k < 8 → (envReader env (feHN b k)).toNat < 2 ^ 32)
    (hAc : accN (fun k => (envReader env (feHN a k)).toNat) 8 < pNat)
    (hBc : accN (fun k => (envReader env (feHN b k)).toNat) 8 < pNat)
    (hsem : semList (feMulHalves q (feH a) (feH b)).1 env = some env') :
    (∀ s, OutOf q s → envReader env' s = envReader env s)
    ∧ (∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat < 2 ^ 32)
    ∧ accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8
        = fm (accN (fun k => (envReader env (feHN a k)).toNat) 8)
             (accN (fun k => (envReader env (feHN b k)).toNat) 8) :=
  feMulHalves_sem_gen hM q a b hq (by decide) (by decide) (by decide) (by decide)
    (outOf_of_hd hq hd_ZZ (by decide) (by decide))
    (fun i => outOf_of_hd hq (hd_PL i) (by decide) (by decide))
    (fun k hk => by
      rw [feH_len a] at hk
      exact feH_getBang a k hk ▸ outOf_of_hd hq (hd_feHN hda k) hca hca')
    (fun k hk => by
      rw [feH_len b] at hk
      exact feH_getBang b k hk ▸ outOf_of_hd hq (hd_feHN hdb k) hcb hcb')
    env env' hcs hAlt hBlt hAc hBc hsem

/-! ## 8. The per-brick obligation on the multiply arm -/

/-- The `mul` arm of `emitFOp`, split at the output copies. -/
theorem emitFOp_mul_split (idx : Nat) (o a b : String) :
    emitFOp idx (FOp.mul o a b)
      = (feMulHalves s!"op{idx}" (feH a) (feH b)).1
        ++ wireBody o (feMulHalves s!"op{idx}" (feH a) (feH b)).2 8 := rfl

/-- **The `mul` brick realizes one `fm` step.** -/
theorem brickStep_mul (hM : GenMulSpec) (idx : Nat) (o a b : String)
    (hop : FOpSchedOkB (FOp.mul o a b) = true)
    (env env' : SEnvScalar) (hsc : BrickScope env) (hcs : ConstsAt env)
    (hsem : semScalar (seqAll (emitFOp idx (FOp.mul o a b))) env = some env') :
    BrickScope env'
      ∧ ∀ fe, schedNameB fe = true →
          feVal env' fe = stepFOpG fm fa fs (feVal env) (FOp.mul o a b) fe := by
  simp only [FOpSchedOkB, Bool.and_eq_true] at hop
  obtain ⟨⟨hoS, haS⟩, hbS⟩ := hop
  obtain ⟨ca, hda, hca, hca'⟩ := hd_of_schedName haS
  obtain ⟨cb, hdb, hcb, hcb'⟩ := hd_of_schedName hbS
  obtain ⟨co, hdo, hco, hco'⟩ := hd_of_schedName hoS
  rw [semScalar_seqAll_eq_semList, emitFOp_mul_split] at hsem
  obtain ⟨Eb, hbrick, hwire⟩ := splitApp hsem
  obtain ⟨hf, hlt, hacc⟩ :=
    feMulHalves_sem hM s!"op{idx}" a b (hd_opPfx idx) hda hca hca' hdb hcb hcb' env Eb hcs
      (hsc.limbs a haS) (hsc.limbs b hbS)
      (by rw [← feVal_eq_accN]; exact hsc.canonical a haS)
      (by rw [← feVal_eq_accN]; exact hsc.canonical b hbS) hbrick
  have hrn : ∀ k, k < 8 →
      (feMulHalves s!"op{idx}" (feH a) (feH b)).2[k]! = s!"{s!"op{idx}"}R{k}" := by
    intro k hk; rw [feMulHalves_names]; exact rNamesOf_getBang _ k hk
  have hcr : accN (fun k =>
        (envReader Eb ((feMulHalves s!"op{idx}" (feH a) (feH b)).2[k]!)).toNat) 8
      = accN (fun k => (envReader Eb s!"{s!"op{idx}"}R{k}").toNat) 8 :=
    accN_congr 8 (fun k hk => by
      show (envReader Eb ((feMulHalves s!"op{idx}" (feH a) (feH b)).2[k]!)).toNat = _
      rw [hrn k hk])
  refine brickWire_step idx o (feMulHalves s!"op{idx}" (feH a) (feH b)).2
      (fm (feVal env a) (feVal env b)) hoS env Eb env' hsc hf
      (fun k hk => by rw [hrn k hk]; exact hlt k hk) ?_ ?_ ?_ hwire
  · rw [hcr, hacc, feVal_eq_accN env a, feVal_eq_accN env b]
  · intro k hk
    rw [hrn k hk]
    exact ⟨(headOk_of_hd (hdAppend (hdAppend (hd_opPfx idx))) (by decide)).notTmp,
      fun j _ => neOfHd (hdAppend (hdAppend (hd_opPfx idx))) (hd_feHN hdo j) (Ne.symm hco)⟩
  · exact Nat.mod_lt _ pNat_pos

/-- **The per-brick field obligation on all three arms**, over `BrickScope`
    together with the reduction constants the multiply brick reads. -/
theorem brickStep (hM : GenMulSpec) (i : Nat) (op : FOp) (hop : FOpSchedOkB op = true)
    (env env' : SEnvScalar) (hsc : BrickScope env) (hcs : ConstsAt env)
    (hsem : semScalar (seqAll (emitFOp i op)) env = some env') :
    BrickScope env'
      ∧ ∀ fe, schedNameB fe = true → feVal env' fe = stepFOpG fm fa fs (feVal env) op fe := by
  cases op with
  | mul o a b => exact brickStep_mul hM i o a b hop env env' hsc hcs hsem
  | add o a b => exact brickStep_add i o a b hop env env' hsc hsem
  | sub o a b => exact brickStep_sub i o a b hop env env' hsc hsem

/-! ## 9. The value obligation in `MulEntry` form -/

/-- **The value half of the `mul` arm over `MulEntry`**, for operand and output
    names outside the brick's own `op{idx}` namespace. -/
theorem mulBrickValue_of_heads (hM : GenMulSpec) (idx : Nat) (o a b : String)
    {co ca cb : Char}
    (hdo : hd o = some co) (hco : co ≠ 'o') (hco' : co ≠ '_')
    (hda : hd a = some ca) (hca : ca ≠ 'o') (hca' : ca ≠ '_')
    (hdb : hd b = some cb) (hcb : cb ≠ 'o') (hcb' : cb ≠ '_')
    (env env' : SEnvScalar) (hE : MulEntry env a b)
    (hsem : semScalar (seqAll (emitFOp idx (FOp.mul o a b))) env = some env') :
    feVal env' o = fm (feVal env a) (feVal env b) := by
  have hcs : ConstsAt env := ⟨hE.zero, hE.constLo, hE.constHi, hE.modulus⟩
  rw [semScalar_seqAll_eq_semList, emitFOp_mul_split] at hsem
  obtain ⟨Eb, hbrick, hwire⟩ := splitApp hsem
  obtain ⟨hf, hlt, hacc⟩ :=
    feMulHalves_sem hM s!"op{idx}" a b (hd_opPfx idx) hda hca hca' hdb hcb hcb' env Eb hcs
      (fun k hk => by rw [← feHN_eq]; exact hE.limbA k hk)
      (fun k hk => by rw [← feHN_eq]; exact hE.limbB k hk)
      (by rw [← feVal_eq_accN]; exact hE.ltA) (by rw [← feVal_eq_accN]; exact hE.ltB) hbrick
  have hrn : ∀ k, k < 8 →
      (feMulHalves s!"op{idx}" (feH a) (feH b)).2[k]! = s!"{s!"op{idx}"}R{k}" := by
    intro k hk; rw [feMulHalves_names]; exact rNamesOf_getBang _ k hk
  obtain ⟨frW, wv⟩ :=
    wireBody_sem o (feMulHalves s!"op{idx}" (feH a) (feH b)).2 8 (KeepWire o)
      (fun k _ => (headOk_of_hd (hd_feHN hdo k) hco').notTmp)
      (fun k j hk hj hkj hne => hkj (feHN_inj hk hj hne).2)
      (fun k hk s hs => hs.2 k hk) (fun s hs => hs.1)
      (fun k hk => by
        rw [hrn k hk]
        exact ⟨(headOk_of_hd (hdAppend (hdAppend (hd_opPfx idx))) (by decide)).notTmp,
          fun j _ => neOfHd (hdAppend (hdAppend (hd_opPfx idx))) (hd_feHN hdo j) (Ne.symm hco)⟩)
      Eb 8 (le_refl 8) env' hwire
  rw [feVal_eq_accN, accN_congr 8 (fun k hk => by rw [wv k hk, hrn k hk])]
  rw [hacc, feVal_eq_accN env a, feVal_eq_accN env b]

/-- **The value half of the `mul` brick, with no residual hypothesis.** The
    head conditions of `mulBrickValue_of_heads` follow from the schedule-name
    conditions by `Secp256k1FeAddSubBrick.hd_of_schedName`, and
    `genMulSpec_holds` discharges the product obligation, so `MulBrickValue`
    holds outright. -/
theorem mulBrickValue_holds : MulBrickValue := by
  intro idx o a b env env' ho ha hb hE hsem
  obtain ⟨co, hdo, hco, hco'⟩ := hd_of_schedName ho
  obtain ⟨ca, hda, hca, hca'⟩ := hd_of_schedName ha
  obtain ⟨cb, hdb, hcb, hcb'⟩ := hd_of_schedName hb
  exact mulBrickValue_of_heads genMulSpec_holds idx o a b hdo hco hco'
    hda hca hca' hdb hcb hcb' env env' hE hsem

#check @mulBrickValue_holds

end CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickReduce
