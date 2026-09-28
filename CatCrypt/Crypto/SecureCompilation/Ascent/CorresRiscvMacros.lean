/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscvSolver
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering64

/-!
# Transport lemmas for the RV64 carry macros

The RV64 kernels are `ROp64` blocks (`RiscvLowering64`); `lowerRBlock64` expands each
op to its `RInst64` instructions, and the carry ops expand to the `sltu` idioms
(`addcc`, `addc`, `subbb`, `subb`) and the mask select (`csub`). This module states,
for each op, what running its expansion does to a machine state described by a
register valuation, in the continuation-passing shape of `S2nMontmulP384Proof.run_mov`:
the valuation after the op is a chain of `upd` writes, and the words the op writes
satisfy an equation over `Nat` (`d + 2^64 · c = a + b + cin` for the add chain,
`d + b + bin = a + 2^64 · borrow` for the subtract chain, a select for `csub`).

The state description is `SRr` itself: `SRr s R` says every register read of `s` is
`R`. Each expansion's register-write fold is obtained by `corres_sym_rv` (the
`*_fold` theorems), so the transport lemma of a macro is its fold read through the
`sltu` carry facts `sltu_add_carry` and `sltu_sub_borrow` of `RiscvModel64`.

A macro reads and writes named registers, so its equation holds only when no operand
is overwritten before its last read and no destination is the zero register. The
`*OK` predicates state those conditions on the names; at the literal names of a kernel
they are closed by `decide`.

## Main definitions

* `upd`, `NZ`, `Reach`: the register valuation update, the non-zero-register
  predicate, and the reachability of a described state.
* `AddccOK`, `AddcOK`, `SubbbOK`, `SubbOK`, `CsubOK`: the name conditions of the macros.

## Main results

* `addcc_fold`, `addc_fold`, `subbb_fold`, `subb_fold`, `csub_fold`: the register-write
  fold of each expansion under `SRr`, by `corres_sym_rv`.
* `run_add`, `run_sub`, `run_and`, `run_or`, `run_xor`, `run_mul`, `run_mulhu`, `run_li`,
  `run_mov`: transport through a single-instruction op.
* `run_addcc`, `run_addc`, `run_subbb`, `run_subb`, `run_csub`: transport through a
  carry macro, with the `Nat` equation of the written words.
* `mul_mulhu_recompose`: `lo + 2^64 · hi = a · b` for the `mul`/`mulhu` pair.
* `lowerRBlock64_cons`, `lowerRBlock64_append`, `run_nil`: the block algebra the
  segment proofs fold over.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## The register valuation -/

/-- The valuation with `d` set to `v`. Unlike `writeR` it has no zero-register guard;
    the transport lemmas use it only at destinations that satisfy `NZ`. -/
def upd (R : AStateR) (d : String) (v : X64R) : AStateR :=
  fun r => if r = d then v else R r

@[simp] theorem upd_same (R : AStateR) (d : String) (v : X64R) : upd R d v d = v := by
  simp [upd]

@[simp] theorem upd_other (R : AStateR) (d r : String) (v : X64R) (h : r ≠ d) :
    upd R d v r = R r := by
  simp [upd, h]

/-- A register name that is not the hard-wired zero register. -/
def NZ (r : String) : Prop := r ≠ "zero" ∧ r ≠ "x0"

instance (r : String) : Decidable (NZ r) := by unfold NZ; infer_instance

theorem writeR_eq_upd {d : String} (h : NZ d) (v : X64R) (st : AStateR) :
    writeR d v st = upd st d v := by
  have h1 : ¬ (d = "zero" ∨ d = "x0") := by
    rintro (h' | h') <;> [exact h.1 h'; exact h.2 h']
  funext r
  simp [writeR, upd, h1]

/-- Every machine state is described by its own read map. -/
theorem SRr_self (s : RState64) : SRr s s.get := fun _ => rfl

/-- Under `SRr`, the zero register reads `0` on the abstract side too. -/
theorem SRr_zero {s : RState64} {R : AStateR} (hs : SRr s R) : R "zero" = 0 := by
  rw [← hs "zero"]; simp [RState64.get]

/-- The states reachable from a described state: some valuation satisfying `P`. -/
def Reach (P : AStateR → Prop) (t : RState64) : Prop := ∃ R, SRr t R ∧ P R

theorem run_nil {P : AStateR → Prop} {R : AStateR} {t : RState64} (hs : SRr t R)
    (hP : P R) : Reach P (runRBlock64 t []) :=
  ⟨R, hs, hP⟩

/-! ## The block algebra -/

theorem lowerRBlock64_cons (op : ROp64) (ops : List ROp64) :
    lowerRBlock64 (op :: ops) = toRInst64 op ++ lowerRBlock64 ops := by
  simp [lowerRBlock64, List.flatMap_cons]

theorem lowerRBlock64_nil : lowerRBlock64 [] = [] := rfl

theorem lowerRBlock64_append (xs ys : List ROp64) :
    lowerRBlock64 (xs ++ ys) = lowerRBlock64 xs ++ lowerRBlock64 ys := by
  simp [lowerRBlock64, List.flatMap_append]

/-! ## The folds of the macro expansions -/

theorem addcc_fold (d cout a b : String) :
    CorresR SRr (fun _ => True)
      (fun st => mvStepR d "sum__" (sltuStepR cout "sum__" a (addStepR "sum__" a b st)))
      (toRInst64 (.addcc d cout a b)) := by
  corres_sym_rv

theorem addc_fold (d cout a b cin t : String) :
    CorresR SRr (fun _ => True)
      (fun st => mvStepR d "sum__" (orStepR cout "c1__" "c2__" (sltuStepR "c2__" "sum__" t
        (addStepR "sum__" t cin (sltuStepR "c1__" t a (addStepR t a b st))))))
      (toRInst64 (.addc d cout a b cin t)) := by
  corres_sym_rv

theorem subbb_fold (d bout a b : String) :
    CorresR SRr (fun _ => True)
      (fun st => subStepR d a b (sltuStepR bout a b st))
      (toRInst64 (.subbb d bout a b)) := by
  corres_sym_rv

theorem subb_fold (d bout a b bin t : String) :
    CorresR SRr (fun _ => True)
      (fun st => mvStepR d "dif__" (orStepR bout "b1__" "b2__" (subStepR "dif__" t bin
        (sltuStepR "b2__" t bin (subStepR t a b (sltuStepR "b1__" a b st))))))
      (toRInst64 (.subb d bout a b bin t)) := by
  corres_sym_rv

theorem csub_fold (d sub orig cond mask t : String) :
    CorresR SRr (fun _ => True)
      (fun st => mvStepR d t (orStepR t t "csm__" (xorStepR "csm__" orig "csm__"
        (andStepR "csm__" orig mask (andStepR t sub mask (subStepR mask "zero" cond st))))))
      (toRInst64 (.csub d sub orig cond mask t)) := by
  corres_sym_rv

/-! ## The arithmetic of the carry idioms -/

/-- The carry word of `x + y` by `sltu`, as a `Nat` equation. -/
theorem carry_word (x y : X64R) :
    (x + y).toNat + 2 ^ 64 * ((if x + y < x then 1 else 0 : X64R)).toNat
        = x.toNat + y.toNat
      ∧ ((if x + y < x then 1 else 0 : X64R)).toNat ≤ 1 := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.lt_def, BitVec.toNat_add]
  split_ifs with h <;> simp <;> omega

/-- The add-with-carry-in idiom: the sum word plus the `or` of the two `sltu` words
    at weight `2^64` is the exact sum, when the carry-in is `0` or `1`. -/
theorem addc_arith (x y c : X64R) (hc : c.toNat ≤ 1) :
    (x + y + c).toNat + 2 ^ 64 * ((if x + y < x then 1 else 0 : X64R)
        ||| (if x + y + c < x + y then 1 else 0)).toNat
        = x.toNat + y.toNat + c.toNat
      ∧ ((if x + y < x then 1 else 0 : X64R)
        ||| (if x + y + c < x + y then 1 else 0)).toNat ≤ 1 := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.lt_def, BitVec.toNat_add]
  split_ifs with h1 h2 h2 <;> simp <;> omega

/-- The borrow word of `x - y` by `sltu`, as a `Nat` equation. -/
theorem borrow_word (x y : X64R) :
    (x - y).toNat + y.toNat = x.toNat + 2 ^ 64 * ((if x < y then 1 else 0 : X64R)).toNat
      ∧ ((if x < y then 1 else 0 : X64R)).toNat ≤ 1 := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.lt_def, BitVec.toNat_sub]
  split_ifs with h <;> simp <;> omega

/-- The subtract-with-borrow-in idiom, when the borrow-in is `0` or `1`. -/
theorem subb_arith (x y c : X64R) (hc : c.toNat ≤ 1) :
    (x - y - c).toNat + y.toNat + c.toNat
        = x.toNat + 2 ^ 64 * ((if x < y then 1 else 0 : X64R)
          ||| (if x - y < c then 1 else 0)).toNat
      ∧ ((if x < y then 1 else 0 : X64R) ||| (if x - y < c then 1 else 0)).toNat ≤ 1 := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.lt_def, BitVec.toNat_sub]
  split_ifs with h1 h2 h2 <;> simp <;> omega

/-- The mask select: with `cond ∈ {0, 1}`, `(sub &&& (0 - cond)) ||| (orig ^^^ (orig &&& (0 - cond)))`
    is `sub` when `cond = 1` and `orig` when `cond = 0`. -/
theorem csub_arith (sub orig cond : X64R) (hc : cond.toNat ≤ 1) :
    (sub &&& (0 - cond)) ||| (orig ^^^ (orig &&& (0 - cond)))
      = if cond.toNat = 1 then sub else orig := by
  have h01 : cond = 0 ∨ cond = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · left; exact BitVec.eq_of_toNat_eq (by simpa using h)
    · right; exact BitVec.eq_of_toNat_eq (by simpa using h)
  rcases h01 with rfl | rfl
  · simp
  · rw [show (0 : X64R) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.and_allOnes, BitVec.xor_self, BitVec.or_zero]
    simp

/-- The `mul`/`mulhu` pair recomposes the 128-bit product. -/
theorem mul_mulhu_recompose (a b : X64R) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)).toNat
      = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  have hlt : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hab
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hlt]
  omega

/-! ## Transport through a single-instruction op -/

section Single

variable {Q : RState64 → Prop} {rest : List RInst64} {R : AStateR} {s : RState64}

/-- The step of an instruction whose semantics is one register write. -/
theorem run_set (i : RInst64) (d : String) (v : X64R) (hd : NZ d) (hs : SRr s R)
    (hi : evalRInst64 s i = s.set d v)
    (h : ∀ s', SRr s' (upd R d v) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (i :: rest)) := by
  rw [runRBlock64_cons, hi]
  refine h _ fun r => ?_
  rw [get_set_eq_writeR, writeR_eq_upd hd, funext hs]

theorem run_add (d a b : String) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (R a + R b)) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.add d a b) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64, opAdd64, hs a, hs b]) h

theorem run_sub (d a b : String) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (R a - R b)) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.sub d a b) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64, opSub64, hs a, hs b]) h

theorem run_and (d a b : String) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (R a &&& R b)) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.and d a b) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64, opAnd64, hs a, hs b]) h

theorem run_or (d a b : String) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (R a ||| R b)) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.or d a b) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64, opOr64, hs a, hs b]) h

theorem run_xor (d a b : String) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (R a ^^^ R b)) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.xor d a b) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64, opXor64, hs a, hs b]) h

theorem run_mul (d a b : String) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (R a * R b)) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.mul d a b) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64, opMul64, hs a, hs b]) h

theorem run_mulhu (d a b : String) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (BitVec.ofNat 64 (((R a).toNat * (R b).toNat) >>> 64))) →
      Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.mulhu d a b) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64, opMulhu, hs a, hs b]) h

theorem run_li (d : String) (imm : Nat) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (BitVec.ofNat 64 imm)) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.li d imm) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64]) h

theorem run_mov (d a : String) (hd : NZ d) (hs : SRr s R)
    (h : ∀ s', SRr s' (upd R d (R a)) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.mov d a) ++ rest)) :=
  run_set _ d _ hd hs (by simp only [evalRInst64, hs a]) h

end Single

/-! ## Transport through a carry macro -/

/-- The name conditions of `addcc d cout a b`: the destinations are not the zero
    register and are distinct, and the second read of `a` is not clobbered. -/
def AddccOK (d cout a _b : String) : Prop :=
  NZ d ∧ NZ cout ∧ d ≠ cout ∧ cout ≠ "sum__" ∧ a ≠ "sum__"

/-- The name conditions of `addc d cout a b cin t`. -/
def AddcOK (d cout a _b cin t : String) : Prop :=
  NZ d ∧ NZ cout ∧ NZ t ∧ d ≠ cout ∧ t ≠ a ∧ t ≠ cin ∧ t ≠ "c1__" ∧ t ≠ "sum__" ∧
    cin ≠ "c1__" ∧ cout ≠ "sum__"

/-- The name conditions of `subbb d bout a b`. -/
def SubbbOK (d bout a b : String) : Prop :=
  NZ d ∧ NZ bout ∧ d ≠ bout ∧ bout ≠ a ∧ bout ≠ b

/-- The name conditions of `subb d bout a b bin t`. -/
def SubbOK (d bout a b bin t : String) : Prop :=
  NZ d ∧ NZ bout ∧ NZ t ∧ d ≠ bout ∧ t ≠ bin ∧ t ≠ "b1__" ∧ t ≠ "b2__" ∧
    a ≠ "b1__" ∧ b ≠ "b1__" ∧ bin ≠ "b1__" ∧ bin ≠ "b2__" ∧ bout ≠ "dif__"

/-- The name conditions of `csub d sub orig cond mask t`. -/
def CsubOK (d sub orig _cond mask t : String) : Prop :=
  NZ d ∧ NZ mask ∧ NZ t ∧ mask ≠ sub ∧ mask ≠ orig ∧ t ≠ orig ∧ t ≠ mask ∧
    orig ≠ "csm__" ∧ t ≠ "csm__"

instance (d cout a b : String) : Decidable (AddccOK d cout a b) := by
  unfold AddccOK; infer_instance
instance (d cout a b cin t : String) : Decidable (AddcOK d cout a b cin t) := by
  unfold AddcOK; infer_instance
instance (d bout a b : String) : Decidable (SubbbOK d bout a b) := by
  unfold SubbbOK; infer_instance
instance (d bout a b bin t : String) : Decidable (SubbOK d bout a b bin t) := by
  unfold SubbOK; infer_instance
instance (d sub orig cond mask t : String) : Decidable (CsubOK d sub orig cond mask t) := by
  unfold CsubOK; infer_instance

section Macros

variable {Q : RState64 → Prop} {rest : List RInst64} {R : AStateR} {s : RState64}

/-- `addcc d cout a b`: `d` receives the wrapped sum, `cout` its carry word. -/
theorem run_addcc (d cout a b : String) (hok : AddccOK d cout a b) (hs : SRr s R)
    (h : ∀ (D C : X64R) (s' : RState64),
      SRr s' (upd (upd (upd R "sum__" D) cout C) d D) →
      D.toNat + 2 ^ 64 * C.toNat = (R a).toNat + (R b).toNat → C.toNat ≤ 1 →
      Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.addcc d cout a b) ++ rest)) := by
  obtain ⟨hd, hcout, hdc, hcs, has⟩ := hok
  rw [RISCVBackend.runRBlock64_append]
  have hf := addcc_fold d cout a b s R hs trivial
  simp only [mvStepR, sltuStepR, addStepR, writeR_eq_upd hd, writeR_eq_upd hcout,
    writeR_eq_upd (show NZ "sum__" by decide), upd_same,
    upd_other _ _ _ _ has, upd_other _ _ _ _ hcs.symm] at hf
  obtain ⟨h1, h2⟩ := carry_word (R a) (R b)
  exact h _ _ _ hf h1 h2

/-- `addc d cout a b cin t`: `d` receives the wrapped `a + b + cin`, `cout` its carry
    word, when `cin` is `0` or `1`. The scratch `t`, `c1__`, `sum__`, `c2__` hold
    intermediate words. -/
theorem run_addc (d cout a b cin t : String) (hok : AddcOK d cout a b cin t) (hs : SRr s R)
    (hcin : (R cin).toNat ≤ 1)
    (h : ∀ (w1 w2 w3 w4 D C : X64R) (s' : RState64),
      SRr s' (upd (upd (upd (upd (upd (upd R t w1) "c1__" w2) "sum__" w3) "c2__" w4)
        cout C) d D) →
      D.toNat + 2 ^ 64 * C.toNat = (R a).toNat + (R b).toNat + (R cin).toNat →
      C.toNat ≤ 1 → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.addc d cout a b cin t) ++ rest)) := by
  obtain ⟨hd, hcout, ht, hdc, hta, htc, htc1, hts, hcc1, hcs⟩ := hok
  rw [RISCVBackend.runRBlock64_append]
  have hf := addc_fold d cout a b cin t s R hs trivial
  simp only [mvStepR, orStepR, sltuStepR, addStepR, writeR_eq_upd hd, writeR_eq_upd hcout,
    writeR_eq_upd ht, writeR_eq_upd (show NZ "sum__" by decide),
    writeR_eq_upd (show NZ "c1__" by decide), writeR_eq_upd (show NZ "c2__" by decide),
    upd_same, upd_other _ _ _ _ hta.symm, upd_other _ _ _ _ htc.symm,
    upd_other _ _ _ _ htc1, upd_other _ _ _ _ hts, upd_other _ _ _ _ hcc1,
    upd_other _ _ _ _ hcs.symm,
    upd_other _ _ _ _ (show ("c1__" : String) ≠ "sum__" by decide),
    upd_other _ _ _ _ (show ("c1__" : String) ≠ "c2__" by decide),
    upd_other _ _ _ _ (show ("sum__" : String) ≠ "c2__" by decide)] at hf
  obtain ⟨h1, h2⟩ := addc_arith (R a) (R b) (R cin) hcin
  exact h _ _ _ _ _ _ _ hf h1 h2

/-- `subbb d bout a b`: `d` receives the wrapped difference, `bout` its borrow word. -/
theorem run_subbb (d bout a b : String) (hok : SubbbOK d bout a b) (hs : SRr s R)
    (h : ∀ (D B : X64R) (s' : RState64),
      SRr s' (upd (upd R bout B) d D) →
      D.toNat + (R b).toNat = (R a).toNat + 2 ^ 64 * B.toNat → B.toNat ≤ 1 →
      Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.subbb d bout a b) ++ rest)) := by
  obtain ⟨hd, hbout, hdb, hba, hbb⟩ := hok
  rw [RISCVBackend.runRBlock64_append]
  have hf := subbb_fold d bout a b s R hs trivial
  simp only [subStepR, sltuStepR, writeR_eq_upd hd, writeR_eq_upd hbout,
    upd_other _ _ _ _ hba.symm, upd_other _ _ _ _ hbb.symm] at hf
  obtain ⟨h1, h2⟩ := borrow_word (R a) (R b)
  exact h _ _ _ hf h1 h2

/-- `subb d bout a b bin t`: `d` receives the wrapped `a - b - bin`, `bout` its borrow
    word, when `bin` is `0` or `1`. -/
theorem run_subb (d bout a b bin t : String) (hok : SubbOK d bout a b bin t) (hs : SRr s R)
    (hbin : (R bin).toNat ≤ 1)
    (h : ∀ (w1 w2 w3 w4 D B : X64R) (s' : RState64),
      SRr s' (upd (upd (upd (upd (upd (upd R "b1__" w1) t w2) "b2__" w3) "dif__" w4)
        bout B) d D) →
      D.toNat + (R b).toNat + (R bin).toNat = (R a).toNat + 2 ^ 64 * B.toNat →
      B.toNat ≤ 1 → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.subb d bout a b bin t) ++ rest)) := by
  obtain ⟨hd, hbout, ht, hdb, htbin, htb1, htb2, hab1, hbb1, hbinb1, hbinb2, hbd⟩ := hok
  rw [RISCVBackend.runRBlock64_append]
  have hf := subb_fold d bout a b bin t s R hs trivial
  simp only [mvStepR, orStepR, subStepR, sltuStepR, writeR_eq_upd hd, writeR_eq_upd hbout,
    writeR_eq_upd ht, writeR_eq_upd (show NZ "b1__" by decide),
    writeR_eq_upd (show NZ "b2__" by decide), writeR_eq_upd (show NZ "dif__" by decide),
    upd_same, upd_other _ _ _ _ htbin.symm, upd_other _ _ _ _ htb1.symm, upd_other _ _ _ _ htb2,
    upd_other _ _ _ _ hab1, upd_other _ _ _ _ hbb1, upd_other _ _ _ _ hbinb1,
    upd_other _ _ _ _ hbinb2, upd_other _ _ _ _ hbd.symm,
    upd_other _ _ _ _ (show ("b1__" : String) ≠ "b2__" by decide),
    upd_other _ _ _ _ (show ("b1__" : String) ≠ "dif__" by decide),
    upd_other _ _ _ _ (show ("b2__" : String) ≠ "dif__" by decide)] at hf
  obtain ⟨h1, h2⟩ := subb_arith (R a) (R b) (R bin) hbin
  exact h _ _ _ _ _ _ _ hf h1 h2

/-- `csub d sub orig cond mask t`: `d` receives `sub` when `cond = 1` and `orig` when
    `cond = 0`. -/
theorem run_csub (d sub orig cond mask t : String) (hok : CsubOK d sub orig cond mask t)
    (hs : SRr s R) (hcond : (R cond).toNat ≤ 1)
    (h : ∀ (w1 w2 w3 w4 D : X64R) (s' : RState64),
      SRr s' (upd (upd (upd (upd (upd (upd R mask w1) t w2) "csm__" w3) "csm__" w4)
        t D) d D) →
      D = (if (R cond).toNat = 1 then R sub else R orig) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (toRInst64 (.csub d sub orig cond mask t) ++ rest)) := by
  obtain ⟨hd, hmask, ht, hms, hmo, hto, htm, hoc, htc⟩ := hok
  rw [RISCVBackend.runRBlock64_append]
  have hf := csub_fold d sub orig cond mask t s R hs trivial
  simp only [mvStepR, orStepR, xorStepR, andStepR, subStepR, writeR_eq_upd hd,
    writeR_eq_upd hmask, writeR_eq_upd ht, writeR_eq_upd (show NZ "csm__" by decide),
    upd_same, upd_other _ _ _ _ hms.symm, upd_other _ _ _ _ hmo.symm,
    upd_other _ _ _ _ hto.symm, upd_other _ _ _ _ htm.symm, upd_other _ _ _ _ hoc,
    upd_other _ _ _ _ htc, SRr_zero hs] at hf
  exact h _ _ _ _ _ _ hf (csub_arith (R sub) (R orig) (R cond) hcond)

end Macros

end CatCrypt.Crypto.SecureCompilation.Ascent
