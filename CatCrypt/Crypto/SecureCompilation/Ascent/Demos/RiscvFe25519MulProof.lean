/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMontMulKernel
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64

/-!
# Correctness of the RV64 schoolbook multiply and the Curve25519 multiply and square

`RiscvMontMulKernel.mul48Block64` is the 4×4 schoolbook multiply of the RV64 backend and
`RiscvX25519FieldKernel.feMulBlock` / `feSqrBlock` are the Curve25519 field multiply and
square built on it; their values are checked there by `native_decide` on worked vectors.
This module proves them for all inputs, over `runRBlock64`.

## Main results

* `mul48_run`: from a zero accumulator, `mul48Block64` leaves the 512-bit product
  `u · v` in `acc0..acc7`, for all `u` in `u0..u3` and `v` in `v0..v3`;
* `feMul_correct`: `feMulBlock` leaves `x · y mod p25519` in `z0..z3`, for every machine
  state, with `x` in `q0..q3` and `y` in `y0..y3`;
* `feSqr_correct`: `feSqrBlock` leaves `x · x mod p25519`;
* `feMul_correct_zmod`, `feSqr_correct_zmod`: the same, canonical and in `ZMod p25519`.

## Structure

* `foldInto_run`: `foldInto k src` adds `src · 2^(64k)` to the accumulator window
  `acc8`, when the sum stays below `2^512` (eight cases, one carry chain each);
* `macAt_run`: one multiply-accumulate step adds `u_i · v_j · 2^(64(i+j))`;
* `macs_run`, `mul48_eq`, `mterms_pairs16`: the sixteen steps sum to `u · v`;
* `reduce_run`: `feMulReduce` forms `lo + 38 · hi`, a five-limb value below `39 · 2^256`,
  and hands it to `RiscvFe25519AddSubProof.fold5_run`;
* `prep_run`, `feMul_run`, `feSqr_run`: the marshalling moves and the composition.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519MulProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMontMulKernel
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros

/-! ## The accumulator window -/

/-- The eight accumulator words `acc0..acc7` as a 512-bit value. -/
def acc8 (R : AStateR) : Nat :=
  (R "acc0").toNat + 2 ^ 64 * (R "acc1").toNat + 2 ^ 128 * (R "acc2").toNat
    + 2 ^ 192 * (R "acc3").toNat + 2 ^ 256 * (R "acc4").toNat + 2 ^ 320 * (R "acc5").toNat
    + 2 ^ 384 * (R "acc6").toNat + 2 ^ 448 * (R "acc7").toNat

/-- The registers one fold writes: the accumulator, the two ripple carries and the macro
    scratch. -/
def foldWrites : List String :=
  ["acc0", "acc1", "acc2", "acc3", "acc4", "acc5", "acc6", "acc7",
    "cra", "crb", "tt__", "sum__", "c1__", "c2__"]

/-! ## One fold -/

section Fold

variable {Q : RState64 → Prop} {rest : List RInst64}

theorem fold_close {X Y c : Nat} (hkey : X + 2 ^ 512 * c = Y) (hb : Y < 2 ^ 512) : X = Y := by
  omega

theorem accAt0 : accAt 0 = "acc0" := by decide
theorem accAt1 : accAt 1 = "acc1" := by decide
theorem accAt2 : accAt 2 = "acc2" := by decide
theorem accAt3 : accAt 3 = "acc3" := by decide
theorem accAt4 : accAt 4 = "acc4" := by decide
theorem accAt5 : accAt 5 = "acc5" := by decide
theorem accAt6 : accAt 6 = "acc6" := by decide
theorem accAt7 : accAt 7 = "acc7" := by decide

theorem foldInto_eq0 (src : String) : foldInto 0 src =
    [.addcc "acc0" "cra" "acc0" src,
      .addc "acc1" "crb" "acc1" "zero" "cra" "tt__",
      .addc "acc2" "cra" "acc2" "zero" "crb" "tt__",
      .addc "acc3" "crb" "acc3" "zero" "cra" "tt__",
      .addc "acc4" "cra" "acc4" "zero" "crb" "tt__",
      .addc "acc5" "crb" "acc5" "zero" "cra" "tt__",
      .addc "acc6" "cra" "acc6" "zero" "crb" "tt__",
      .addc "acc7" "crb" "acc7" "zero" "cra" "tt__"] := by
  simp [foldInto, accAt0, accAt1, accAt2, accAt3, accAt4, accAt5, accAt6, accAt7, List.range_succ]

theorem foldInto_eq1 (src : String) : foldInto 1 src =
    [.addcc "acc1" "cra" "acc1" src,
      .addc "acc2" "crb" "acc2" "zero" "cra" "tt__",
      .addc "acc3" "cra" "acc3" "zero" "crb" "tt__",
      .addc "acc4" "crb" "acc4" "zero" "cra" "tt__",
      .addc "acc5" "cra" "acc5" "zero" "crb" "tt__",
      .addc "acc6" "crb" "acc6" "zero" "cra" "tt__",
      .addc "acc7" "cra" "acc7" "zero" "crb" "tt__"] := by
  simp [foldInto, accAt1, accAt2, accAt3, accAt4, accAt5, accAt6, accAt7, List.range_succ]

theorem foldInto_eq2 (src : String) : foldInto 2 src =
    [.addcc "acc2" "cra" "acc2" src,
      .addc "acc3" "crb" "acc3" "zero" "cra" "tt__",
      .addc "acc4" "cra" "acc4" "zero" "crb" "tt__",
      .addc "acc5" "crb" "acc5" "zero" "cra" "tt__",
      .addc "acc6" "cra" "acc6" "zero" "crb" "tt__",
      .addc "acc7" "crb" "acc7" "zero" "cra" "tt__"] := by
  simp [foldInto, accAt2, accAt3, accAt4, accAt5, accAt6, accAt7, List.range_succ]

theorem foldInto_eq3 (src : String) : foldInto 3 src =
    [.addcc "acc3" "cra" "acc3" src,
      .addc "acc4" "crb" "acc4" "zero" "cra" "tt__",
      .addc "acc5" "cra" "acc5" "zero" "crb" "tt__",
      .addc "acc6" "crb" "acc6" "zero" "cra" "tt__",
      .addc "acc7" "cra" "acc7" "zero" "crb" "tt__"] := by
  simp [foldInto, accAt3, accAt4, accAt5, accAt6, accAt7, List.range_succ]

theorem foldInto_eq4 (src : String) : foldInto 4 src =
    [.addcc "acc4" "cra" "acc4" src,
      .addc "acc5" "crb" "acc5" "zero" "cra" "tt__",
      .addc "acc6" "cra" "acc6" "zero" "crb" "tt__",
      .addc "acc7" "crb" "acc7" "zero" "cra" "tt__"] := by
  simp [foldInto, accAt4, accAt5, accAt6, accAt7, List.range_succ]

theorem foldInto_eq5 (src : String) : foldInto 5 src =
    [.addcc "acc5" "cra" "acc5" src,
      .addc "acc6" "crb" "acc6" "zero" "cra" "tt__",
      .addc "acc7" "cra" "acc7" "zero" "crb" "tt__"] := by
  simp [foldInto, accAt5, accAt6, accAt7, List.range_succ]

theorem foldInto_eq6 (src : String) : foldInto 6 src =
    [.addcc "acc6" "cra" "acc6" src,
      .addc "acc7" "crb" "acc7" "zero" "cra" "tt__"] := by
  simp [foldInto, accAt6, accAt7, List.range_succ]

theorem foldInto_eq7 (src : String) : foldInto 7 src =
    [.addcc "acc7" "cra" "acc7" src] := by
  simp [foldInto, accAt7]

/-- **One fold.** `foldInto k src` adds `src · 2^(64k)` to the accumulator window when
    the sum stays below `2^512`, and writes only `foldWrites`. -/
theorem foldInto_run (k : Nat) (hk : k < 8) (src : String) {R : AStateR} {s : RState64}
    (hs : SRr s R) (hb : acc8 R + (R src).toNat * 2 ^ (64 * k) < 2 ^ 512)
    (h : ∀ (R' : AStateR) (s' : RState64), SRr s' R' →
      acc8 R' = acc8 R + (R src).toNat * 2 ^ (64 * k) →
      (∀ r, r ∉ foldWrites → R' r = R r) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (lowerRBlock64 (foldInto k src) ++ rest)) := by
  have hz : (R "zero").toNat = 0 := by rw [SRr_zero hs]; rfl
  interval_cases k
  · rw [foldInto_eq0]
    simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil, List.append_assoc]
    refine run_addcc _ _ _ _ (by unfold AddccOK; decide) hs ?_; intro D0 C0 s0 hs0 e0 hc0
    refine run_addc _ _ _ _ _ _ (by decide) hs0
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc0) ?_
    intro _ _ _ _ D1 C1 s1 hs1 e1 hc1
    refine run_addc _ _ _ _ _ _ (by decide) hs1
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
    intro _ _ _ _ D2 C2 s2 hs2 e2 hc2
    refine run_addc _ _ _ _ _ _ (by decide) hs2
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
    intro _ _ _ _ D3 C3 s3 hs3 e3 hc3
    refine run_addc _ _ _ _ _ _ (by decide) hs3
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc3) ?_
    intro _ _ _ _ D4 C4 s4 hs4 e4 hc4
    refine run_addc _ _ _ _ _ _ (by decide) hs4
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc4) ?_
    intro _ _ _ _ D5 C5 s5 hs5 e5 hc5
    refine run_addc _ _ _ _ _ _ (by decide) hs5
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc5) ?_
    intro _ _ _ _ D6 C6 s6 hs6 e6 hc6
    refine run_addc _ _ _ _ _ _ (by decide) hs6
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc6) ?_
    intro _ _ _ _ D7 C7 s7 hs7 e7 hc7
    refine h _ _ hs7 (fold_close (c := C7.toNat) ?_ hb) ?_
    · simp only [acc8, upd, ↓reduceIte, String.reduceEq, hz] at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
      omega
    · intro r hr
      simp only [foldWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [upd, hr, ↓reduceIte]
  · rw [foldInto_eq1]
    simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil, List.append_assoc]
    refine run_addcc _ _ _ _ (by unfold AddccOK; decide) hs ?_; intro D0 C0 s0 hs0 e0 hc0
    refine run_addc _ _ _ _ _ _ (by decide) hs0
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc0) ?_
    intro _ _ _ _ D1 C1 s1 hs1 e1 hc1
    refine run_addc _ _ _ _ _ _ (by decide) hs1
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
    intro _ _ _ _ D2 C2 s2 hs2 e2 hc2
    refine run_addc _ _ _ _ _ _ (by decide) hs2
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
    intro _ _ _ _ D3 C3 s3 hs3 e3 hc3
    refine run_addc _ _ _ _ _ _ (by decide) hs3
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc3) ?_
    intro _ _ _ _ D4 C4 s4 hs4 e4 hc4
    refine run_addc _ _ _ _ _ _ (by decide) hs4
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc4) ?_
    intro _ _ _ _ D5 C5 s5 hs5 e5 hc5
    refine run_addc _ _ _ _ _ _ (by decide) hs5
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc5) ?_
    intro _ _ _ _ D6 C6 s6 hs6 e6 hc6
    refine h _ _ hs6 (fold_close (c := C6.toNat) ?_ hb) ?_
    · simp only [acc8, upd, ↓reduceIte, String.reduceEq, hz] at e0 e1 e2 e3 e4 e5 e6 ⊢
      omega
    · intro r hr
      simp only [foldWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [upd, hr, ↓reduceIte]
  · rw [foldInto_eq2]
    simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil, List.append_assoc]
    refine run_addcc _ _ _ _ (by unfold AddccOK; decide) hs ?_; intro D0 C0 s0 hs0 e0 hc0
    refine run_addc _ _ _ _ _ _ (by decide) hs0
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc0) ?_
    intro _ _ _ _ D1 C1 s1 hs1 e1 hc1
    refine run_addc _ _ _ _ _ _ (by decide) hs1
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
    intro _ _ _ _ D2 C2 s2 hs2 e2 hc2
    refine run_addc _ _ _ _ _ _ (by decide) hs2
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
    intro _ _ _ _ D3 C3 s3 hs3 e3 hc3
    refine run_addc _ _ _ _ _ _ (by decide) hs3
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc3) ?_
    intro _ _ _ _ D4 C4 s4 hs4 e4 hc4
    refine run_addc _ _ _ _ _ _ (by decide) hs4
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc4) ?_
    intro _ _ _ _ D5 C5 s5 hs5 e5 hc5
    refine h _ _ hs5 (fold_close (c := C5.toNat) ?_ hb) ?_
    · simp only [acc8, upd, ↓reduceIte, String.reduceEq, hz] at e0 e1 e2 e3 e4 e5 ⊢
      omega
    · intro r hr
      simp only [foldWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [upd, hr, ↓reduceIte]
  · rw [foldInto_eq3]
    simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil, List.append_assoc]
    refine run_addcc _ _ _ _ (by unfold AddccOK; decide) hs ?_; intro D0 C0 s0 hs0 e0 hc0
    refine run_addc _ _ _ _ _ _ (by decide) hs0
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc0) ?_
    intro _ _ _ _ D1 C1 s1 hs1 e1 hc1
    refine run_addc _ _ _ _ _ _ (by decide) hs1
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
    intro _ _ _ _ D2 C2 s2 hs2 e2 hc2
    refine run_addc _ _ _ _ _ _ (by decide) hs2
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
    intro _ _ _ _ D3 C3 s3 hs3 e3 hc3
    refine run_addc _ _ _ _ _ _ (by decide) hs3
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc3) ?_
    intro _ _ _ _ D4 C4 s4 hs4 e4 hc4
    refine h _ _ hs4 (fold_close (c := C4.toNat) ?_ hb) ?_
    · simp only [acc8, upd, ↓reduceIte, String.reduceEq, hz] at e0 e1 e2 e3 e4 ⊢
      omega
    · intro r hr
      simp only [foldWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [upd, hr, ↓reduceIte]
  · rw [foldInto_eq4]
    simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil, List.append_assoc]
    refine run_addcc _ _ _ _ (by unfold AddccOK; decide) hs ?_; intro D0 C0 s0 hs0 e0 hc0
    refine run_addc _ _ _ _ _ _ (by decide) hs0
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc0) ?_
    intro _ _ _ _ D1 C1 s1 hs1 e1 hc1
    refine run_addc _ _ _ _ _ _ (by decide) hs1
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
    intro _ _ _ _ D2 C2 s2 hs2 e2 hc2
    refine run_addc _ _ _ _ _ _ (by decide) hs2
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
    intro _ _ _ _ D3 C3 s3 hs3 e3 hc3
    refine h _ _ hs3 (fold_close (c := C3.toNat) ?_ hb) ?_
    · simp only [acc8, upd, ↓reduceIte, String.reduceEq, hz] at e0 e1 e2 e3 ⊢
      omega
    · intro r hr
      simp only [foldWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [upd, hr, ↓reduceIte]
  · rw [foldInto_eq5]
    simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil, List.append_assoc]
    refine run_addcc _ _ _ _ (by unfold AddccOK; decide) hs ?_; intro D0 C0 s0 hs0 e0 hc0
    refine run_addc _ _ _ _ _ _ (by decide) hs0
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc0) ?_
    intro _ _ _ _ D1 C1 s1 hs1 e1 hc1
    refine run_addc _ _ _ _ _ _ (by decide) hs1
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
    intro _ _ _ _ D2 C2 s2 hs2 e2 hc2
    refine h _ _ hs2 (fold_close (c := C2.toNat) ?_ hb) ?_
    · simp only [acc8, upd, ↓reduceIte, String.reduceEq, hz] at e0 e1 e2 ⊢
      omega
    · intro r hr
      simp only [foldWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [upd, hr, ↓reduceIte]
  · rw [foldInto_eq6]
    simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil, List.append_assoc]
    refine run_addcc _ _ _ _ (by unfold AddccOK; decide) hs ?_; intro D0 C0 s0 hs0 e0 hc0
    refine run_addc _ _ _ _ _ _ (by decide) hs0
      (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc0) ?_
    intro _ _ _ _ D1 C1 s1 hs1 e1 hc1
    refine h _ _ hs1 (fold_close (c := C1.toNat) ?_ hb) ?_
    · simp only [acc8, upd, ↓reduceIte, String.reduceEq, hz] at e0 e1 ⊢
      omega
    · intro r hr
      simp only [foldWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [upd, hr, ↓reduceIte]
  · rw [foldInto_eq7]
    simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil]
    refine run_addcc _ _ _ _ (by unfold AddccOK; decide) hs ?_; intro D0 C0 s0 hs0 e0 hc0
    refine h _ _ hs0 (fold_close (c := C0.toNat) ?_ hb) ?_
    · simp only [acc8, upd, ↓reduceIte, String.reduceEq] at e0 ⊢
      omega
    · intro r hr
      simp only [foldWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [upd, hr, ↓reduceIte]

/-! ## One multiply-accumulate step -/

/-- The registers one step `macAt` writes. -/
def macWrites : List String := foldWrites ++ ["lo__", "hi__"]

theorem mac_bound {A lo hi P M : Nat} (hrec : lo + 2 ^ 64 * hi = P) (hb : A + P * M < 2 ^ 512) :
    A + lo * M < 2 ^ 512 ∧ (A + lo * M) + hi * (M * 2 ^ 64) < 2 ^ 512 ∧
      (A + lo * M) + hi * (M * 2 ^ 64) = A + P * M := by
  have e : lo * M + hi * (M * 2 ^ 64) = P * M := by rw [← hrec]; ring
  have : lo * M ≤ P * M := Nat.mul_le_mul_right _ (by omega)
  refine ⟨by omega, by omega, by omega⟩

/-- **One step.** `macAt i j xi yj` adds `xi · yj · 2^(64(i+j))` to the accumulator
    window when the sum stays below `2^512`, and writes only `macWrites`. -/
theorem macAt_run (i j : Nat) (hij : i + j ≤ 6) (xi yj : String) (hx : xi ∉ macWrites)
    (hy : yj ∉ macWrites) {R : AStateR} {s : RState64} (hs : SRr s R)
    (hb : acc8 R + (R xi).toNat * (R yj).toNat * 2 ^ (64 * (i + j)) < 2 ^ 512)
    (h : ∀ (R' : AStateR) (s' : RState64), SRr s' R' →
      acc8 R' = acc8 R + (R xi).toNat * (R yj).toNat * 2 ^ (64 * (i + j)) →
      (∀ r, r ∉ macWrites → R' r = R r) → Q (runRBlock64 s' rest)) :
    Q (runRBlock64 s (lowerRBlock64 (macAt i j xi yj) ++ rest)) := by
  simp only [macWrites, foldWrites, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hx hy
  unfold macAt
  simp only [lowerRBlock64_append, List.cons_append, List.nil_append, lowerRBlock64_cons,
    List.append_assoc]
  refine run_mul "lo__" xi yj (by decide) hs ?_; intro s1 hs1
  refine run_mulhu "hi__" xi yj (by decide) hs1 ?_; intro s2 hs2
  have hx1 : upd R "lo__" (R xi * R yj) xi = R xi := upd_other _ _ _ _ hx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hy1 : upd R "lo__" (R xi * R yj) yj = R yj := upd_other _ _ _ _ hy.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hx1, hy1] at hs2
  generalize hL : R xi * R yj = L at hs2
  generalize hH : BitVec.ofNat 64 (((R xi).toNat * (R yj).toNat) >>> 64) = H at hs2
  have hrec : L.toNat + 2 ^ 64 * H.toNat = (R xi).toNat * (R yj).toNat := by
    rw [← hL, ← hH]; exact mul_mulhu_recompose _ _
  have hA : acc8 (upd (upd R "lo__" L) "hi__" H) = acc8 R := by
    simp only [acc8, upd, ↓reduceIte, String.reduceEq]
  have hM : 2 ^ (64 * (i + j + 1)) = 2 ^ (64 * (i + j)) * 2 ^ 64 := by
    rw [show 64 * (i + j + 1) = 64 * (i + j) + 64 by ring, pow_add]
  obtain ⟨b1, b2, bsum⟩ := mac_bound (A := acc8 R) (M := 2 ^ (64 * (i + j))) hrec hb
  refine foldInto_run (i + j) (by omega) "lo__" hs2
    (by simp only [hA, upd, ↓reduceIte, String.reduceEq]; exact b1) ?_
  intro R3 s3 hs3 e3 f3
  have hhi : R3 "hi__" = H := by rw [f3 "hi__" (by decide)]; simp [upd]
  refine foldInto_run (i + j + 1) (by omega) "hi__" hs3
    (by rw [e3, hhi, hM, hA]; simpa only [upd, ↓reduceIte, String.reduceEq] using b2) ?_
  intro R4 s4 hs4 e4 f4
  refine h R4 s4 hs4 ?_ ?_
  · rw [e4, e3, hhi, hM, hA]
    simpa only [upd, ↓reduceIte, String.reduceEq] using bsum
  · intro r hr
    simp only [macWrites, foldWrites, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hr
    rw [f4 r (by simp [foldWrites, hr]), f3 r (by simp [foldWrites, hr])]
    simp only [upd, hr, ↓reduceIte]

end Fold

/-! ## The schoolbook -/

/-- The limb names of the schoolbook's inputs. -/
def uN (i : Nat) : String := "u" ++ toString i
def vN (j : Nat) : String := "v" ++ toString j

/-- The steps for a list of limb pairs. -/
def macBlock (ps : List (Nat × Nat)) : List ROp64 :=
  ps.flatMap fun p => macAt p.1 p.2 (uN p.1) (vN p.2)

/-- The weight of limb position `k`. -/
def wt (k : Nat) : Nat := Nat.pow 2 (64 * k)

/-- The partial product of one limb pair, at its weight. -/
def mterm (R : AStateR) (p : Nat × Nat) : Nat :=
  (R (uN p.1)).toNat * (R (vN p.2)).toNat * wt (p.1 + p.2)

/-- The partial products of a list of limb pairs. -/
def mterms (R : AStateR) (ps : List (Nat × Nat)) : Nat := (ps.map (mterm R)).sum

theorem uN_notMem (i : Nat) (hi : i < 4) : uN i ∉ macWrites := by
  interval_cases i <;> decide

theorem vN_notMem (j : Nat) (hj : j < 4) : vN j ∉ macWrites := by
  interval_cases j <;> decide

theorem mterms_congr {R R' : AStateR} (ps : List (Nat × Nat))
    (h : ∀ p ∈ ps, R' (uN p.1) = R (uN p.1) ∧ R' (vN p.2) = R (vN p.2)) :
    mterms R' ps = mterms R ps := by
  unfold mterms
  congr 1
  refine List.map_congr_left fun p hp => ?_
  unfold mterm
  rw [(h p hp).1, (h p hp).2]

/-- **The steps for a list of limb pairs** add their partial products to the window. -/
theorem macs_run (ps : List (Nat × Nat)) (hps : ∀ p ∈ ps, p.1 < 4 ∧ p.2 < 4)
    {R : AStateR} {s : RState64} (hs : SRr s R) (hb : acc8 R + mterms R ps < 2 ^ 512) :
    Reach (fun R' => acc8 R' = acc8 R + mterms R ps ∧ ∀ r, r ∉ macWrites → R' r = R r)
      (runRBlock64 s (lowerRBlock64 (macBlock ps))) := by
  induction ps generalizing R s with
  | nil => exact run_nil hs ⟨by simp [mterms], fun _ _ => rfl⟩
  | cons p ps ih =>
    obtain ⟨hp1, hp2⟩ := hps p (by simp)
    have hps' : ∀ q ∈ ps, q.1 < 4 ∧ q.2 < 4 := fun q hq => hps q (by simp [hq])
    have hsplit : mterms R (p :: ps) = mterm R p + mterms R ps := by simp [mterms]
    rw [hsplit] at hb ⊢
    unfold macBlock
    rw [List.flatMap_cons, lowerRBlock64_append]
    refine macAt_run (Q := Reach fun R' => acc8 R' = acc8 R + (mterm R p + mterms R ps) ∧
        ∀ r, r ∉ macWrites → R' r = R r) (rest := lowerRBlock64 (macBlock ps))
      p.1 p.2 (by omega) (uN p.1) (vN p.2) (uN_notMem _ hp1) (vN_notMem _ hp2) hs
      (show acc8 R + mterm R p < 2 ^ 512 by omega) ?_
    intro R' s' hs' e f
    change acc8 R' = acc8 R + mterm R p at e
    have hc : mterms R' ps = mterms R ps := mterms_congr ps fun q hq =>
      ⟨f _ (uN_notMem _ (hps' q hq).1), f _ (vN_notMem _ (hps' q hq).2)⟩
    refine (ih hps' hs' (by rw [e, hc]; omega)).mono ?_
    rintro R'' ⟨h1, h2⟩
    refine ⟨by rw [h1, e, hc]; omega, fun r hr => by rw [h2 r hr, f r hr]⟩

/-- The sixteen limb pairs of the schoolbook, in its order. -/
def pairs16 : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
    (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

theorem pairs16_eq :
    pairs16 = (List.range 4).flatMap fun i => (List.range 4).map fun j => (i, j) := by
  decide

theorem flatten_flatMap_map {α β γ : Type} (l : List α) (m : List β) (g : α → β → List γ) :
    (l.flatMap fun i => m.map (g i)).flatten
      = (l.flatMap fun i => m.map fun j => (i, j)).flatMap fun p => g p.1 p.2 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatten_append, ih, List.flatMap_cons, List.flatMap_append,
      List.flatMap_map]
    rfl

theorem mul48_eq : mul48Block64 = macBlock pairs16 := by
  rw [pairs16_eq]
  unfold mul48Block64 macBlock
  exact flatten_flatMap_map (List.range 4) (List.range 4) fun i j => macAt i j (uN i) (vN j)

theorem uN_eqs : uN 0 = "u0" ∧ uN 1 = "u1" ∧ uN 2 = "u2" ∧ uN 3 = "u3" :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem vN_eqs : vN 0 = "v0" ∧ vN 1 = "v1" ∧ vN 2 = "v2" ∧ vN 3 = "v3" :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem limbs4_wt (R : AStateR) (a0 a1 a2 a3 : String) :
    limbs4 R a0 a1 a2 a3 = (R a0).toNat + wt 1 * (R a1).toNat + wt 2 * (R a2).toNat
      + wt 3 * (R a3).toNat := rfl

set_option exponentiation.threshold 600 in
theorem wt_facts : wt 0 = 1 ∧ wt 2 = wt 1 * wt 1 ∧ wt 3 = wt 2 * wt 1 ∧ wt 4 = wt 3 * wt 1 ∧
    wt 5 = wt 4 * wt 1 ∧ wt 6 = wt 5 * wt 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The schoolbook identity over the limb values. -/
theorem poly16 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    a0 * b0 * wt 0 + (a0 * b1 * wt 1 + (a0 * b2 * wt 2 + (a0 * b3 * wt 3 + (a1 * b0 * wt 1 + (a1 * b1 * wt 2 + (a1 * b2 * wt 3 + (a1 * b3 * wt 4 + (a2 * b0 * wt 2 + (a2 * b1 * wt 3 + (a2 * b2 * wt 4 + (a2 * b3 * wt 5 + (a3 * b0 * wt 3 + (a3 * b1 * wt 4 + (a3 * b2 * wt 5 + a3 * b3 * wt 6)))))))))))))) =
    (a0 + wt 1 * a1 + wt 2 * a2 + wt 3 * a3) * (b0 + wt 1 * b1 + wt 2 * b2 + wt 3 * b3) := by
  obtain ⟨h0, h2, h3, h4, h5, h6⟩ := wt_facts
  rw [h0, h6, h5, h4, h3, h2]
  generalize wt 1 = B
  ring

theorem mterm_eq (R : AStateR) (i j : Nat) :
    mterm R (i, j) = (R (uN i)).toNat * (R (vN j)).toNat * wt (i + j) := rfl

theorem mterms_cons (R : AStateR) (p : Nat × Nat) (ps : List (Nat × Nat)) :
    mterms R (p :: ps) = mterm R p + mterms R ps := by
  simp [mterms]

theorem mterms_nil (R : AStateR) : mterms R [] = 0 := rfl

theorem poly16' (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    a0 * b0 * wt (0 + 0) + (a0 * b1 * wt (0 + 1) + (a0 * b2 * wt (0 + 2) + (a0 * b3 * wt (0 + 3) + (a1 * b0 * wt (1 + 0) + (a1 * b1 * wt (1 + 1) + (a1 * b2 * wt (1 + 2) + (a1 * b3 * wt (1 + 3) + (a2 * b0 * wt (2 + 0) + (a2 * b1 * wt (2 + 1) + (a2 * b2 * wt (2 + 2) + (a2 * b3 * wt (2 + 3) + (a3 * b0 * wt (3 + 0) + (a3 * b1 * wt (3 + 1) + (a3 * b2 * wt (3 + 2) + (a3 * b3 * wt (3 + 3) + 0))))))))))))))) =
    (a0 + wt 1 * a1 + wt 2 * a2 + wt 3 * a3) * (b0 + wt 1 * b1 + wt 2 * b2 + wt 3 * b3) := by
  rw [Nat.add_zero (a3 * b3 * wt (3 + 3))]
  exact poly16 a0 a1 a2 a3 b0 b1 b2 b3

set_option simprocs false in
theorem mterms_pairs16 (R : AStateR) :
    mterms R pairs16 = limbs4 R "u0" "u1" "u2" "u3" * limbs4 R "v0" "v1" "v2" "v3" := by
  rw [← uN_eqs.1, ← uN_eqs.2.1, ← uN_eqs.2.2.1, ← uN_eqs.2.2.2, ← vN_eqs.1, ← vN_eqs.2.1,
    ← vN_eqs.2.2.1, ← vN_eqs.2.2.2]
  show mterms R [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)] = _
  rw [mterms_cons, mterms_cons, mterms_cons, mterms_cons, mterms_cons, mterms_cons, mterms_cons,
    mterms_cons, mterms_cons, mterms_cons, mterms_cons, mterms_cons, mterms_cons, mterms_cons,
    mterms_cons, mterms_cons, mterms_nil]
  simp only [mterm_eq]
  rw [limbs4_wt, limbs4_wt]
  exact poly16' _ _ _ _ _ _ _ _


set_option exponentiation.threshold 600 in
/-- **The schoolbook.** From a zero accumulator, `mul48Block64` leaves the 512-bit
    product `x · y` in `acc0..acc7`, with `x` in `u0..u3` and `y` in `v0..v3`, and writes
    only `macWrites`. -/
theorem mul48_run {R : AStateR} {s : RState64} (hs : SRr s R) (h0 : acc8 R = 0) :
    Reach (fun R' => acc8 R' = limbs4 R "u0" "u1" "u2" "u3" * limbs4 R "v0" "v1" "v2" "v3"
      ∧ ∀ r, r ∉ macWrites → R' r = R r) (runRBlock64 s (lowerRBlock64 mul48Block64)) := by
  have hlt : limbs4 R "u0" "u1" "u2" "u3" * limbs4 R "v0" "v1" "v2" "v3" < 2 ^ 512 := by
    calc _ < 2 ^ 256 * 2 ^ 256 :=
          Nat.mul_lt_mul'' (limbs4_lt R "u0" "u1" "u2" "u3") (limbs4_lt R "v0" "v1" "v2" "v3")
      _ = 2 ^ 512 := by norm_num
  rw [mul48_eq]
  refine (macs_run pairs16 (by decide) hs (by rw [h0, mterms_pairs16]; omega)).mono ?_
  rintro R' ⟨h1, h2⟩
  exact ⟨by rw [h1, h0, mterms_pairs16]; omega, h2⟩

/-! ## Composition and frames -/

/-- Run a block in two parts: the second part starts from a state described by the
    first part's postcondition. -/
theorem reach_append {P P' : AStateR → Prop} {s : RState64} {A B : List RInst64}
    (h1 : Reach P' (runRBlock64 s A))
    (h2 : ∀ (R' : AStateR) (t : RState64), SRr t R' → P' R' → Reach P (runRBlock64 t B)) :
    Reach P (runRBlock64 s (A ++ B)) := by
  rw [runRBlock64_append]
  obtain ⟨R', hs', hP'⟩ := h1
  exact h2 R' _ hs' hP'

/-- The destinations of a block. -/
def blockWrites (b : List RInst64) : List String := b.map fun i => (rinst64DstSrcs i).1

/-- **A block leaves every register it does not write.** -/
theorem runRBlock64_frame (b : List RInst64) (s : RState64) (r : String)
    (h : r ∉ blockWrites b) : (runRBlock64 s b).get r = s.get r := by
  induction b generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [blockWrites, List.map_cons, List.mem_cons, not_or] at h
    rw [runRBlock64_cons, ih _ h.2]
    rw [RiscvRename64.evalRInst64_eq_set]
    exact RState64.get_set_other _ _ _ _ h.1

/-! ## The reduction `feMulReduce` -/

/-- The partial products of `38 · hi` accumulated by `feMulReduce`, as in
    `mul121666_arith`. -/
theorem mul38_arith (x0 x1 x2 x3 l0 l1 l2 l3 h0 h1 h2 h3 a1 a2 a3 a4 p1 p2 p3 p4 : Nat)
    (hx3 : x3 < 2 ^ 64) (ha4 : a4 < 2 ^ 64)
    (r0 : l0 + 2 ^ 64 * h0 = x0 * 38) (r1 : l1 + 2 ^ 64 * h1 = x1 * 38)
    (r2 : l2 + 2 ^ 64 * h2 = x2 * 38) (r3 : l3 + 2 ^ 64 * h3 = x3 * 38)
    (e1 : a1 + 2 ^ 64 * p1 = h0 + l1) (e2 : a2 + 2 ^ 64 * p2 = h1 + l2 + p1)
    (e3 : a3 + 2 ^ 64 * p3 = h2 + l3 + p2) (e4 : a4 + 2 ^ 64 * p4 = h3 + p3)
    (hp3 : p3 ≤ 1) :
    a4 ≤ 38 ∧ l0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4
      = 38 * (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) := by
  have hh3 : h3 < 38 := by omega
  have hp4 : p4 = 0 := by omega
  subst hp4
  omega

/-- `T = lo + H` as a five-limb value; its top limb stays below `2^20`. -/
theorem addT_arith (a0 a1 a2 a3 j0 j1 j2 j3 j4 t0 t1 t2 t3 t4 c1 c2 c3 c4 c5 : Nat)
    (hj4 : j4 ≤ 38) (ht4 : t4 < 2 ^ 64)
    (e0 : t0 + 2 ^ 64 * c1 = a0 + j0) (e1 : t1 + 2 ^ 64 * c2 = a1 + j1 + c1)
    (e2 : t2 + 2 ^ 64 * c3 = a2 + j2 + c2) (e3 : t3 + 2 ^ 64 * c4 = a3 + j3 + c3)
    (e4 : t4 + 2 ^ 64 * c5 = j4 + c4) (hc4 : c4 ≤ 1) :
    t4 < 2 ^ 20 ∧ t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 + 2 ^ 256 * t4
      = (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3)
        + (j0 + 2 ^ 64 * j1 + 2 ^ 128 * j2 + 2 ^ 192 * j3 + 2 ^ 256 * j4) := by
  have hc5 : c5 = 0 := by omega
  subst hc5
  omega

/-- `2^256 ≡ 38` modulo `p25519`. -/
theorem fold38_mod (lo hi : Nat) : (lo + 38 * hi) % p25519 = (lo + 2 ^ 256 * hi) % p25519 := by
  have : lo + 2 ^ 256 * hi = lo + 38 * hi + p25519 * (2 * hi) := by rw [p25519_eq]; omega
  rw [this, Nat.add_mul_mod_self_left]

/-- **The reduction.** `feMulReduce` leaves the 512-bit accumulator value modulo
    `p25519` in `z0..z3`. -/
theorem reduce_run {R : AStateR} {s : RState64} (hs : SRr s R) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3" = acc8 R % p25519)
      (runRBlock64 s (lowerRBlock64 feMulReduce)) := by
  unfold feMulReduce
  simp only [List.cons_append, List.nil_append, lowerRBlock64_cons]
  refine run_li _ _ (by decide) hs ?_; intro s1 hs1
  refine run_mul _ _ _ (by decide) hs1 ?_; intro s2 hs2
  refine run_mulhu _ _ _ (by decide) hs2 ?_; intro s3 hs3
  refine run_mul _ _ _ (by decide) hs3 ?_; intro s4 hs4
  refine run_mulhu _ _ _ (by decide) hs4 ?_; intro s5 hs5
  refine run_mul _ _ _ (by decide) hs5 ?_; intro s6 hs6
  refine run_mulhu _ _ _ (by decide) hs6 ?_; intro s7 hs7
  refine run_mul _ _ _ (by decide) hs7 ?_; intro s8 hs8
  refine run_mulhu _ _ _ (by decide) hs8 ?_; intro s9 hs9
  refine run_mov _ _ (by decide) hs9 ?_; intro s10 hs10
  refine run_addcc _ _ _ _ (by decide) hs10 ?_; intro J1 Q1 s11 hs11 e1 hq1
  refine run_addc _ _ _ _ _ _ (by decide) hs11
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hq1) ?_
  intro _ _ _ _ J2 Q2 s12 hs12 e2 hq2
  refine run_addc _ _ _ _ _ _ (by decide) hs12
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hq2) ?_
  intro _ _ _ _ J3 Q3 s13 hs13 e3 hq3
  refine run_addcc _ _ _ _ (by decide) hs13 ?_; intro J4 Q4 s14 hs14 e4 _
  refine run_addcc _ _ _ _ (by decide) hs14 ?_; intro T0 C1 s15 hs15 f0 hc1
  refine run_addc _ _ _ _ _ _ (by decide) hs15
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
  intro _ _ _ _ T1 C2 s16 hs16 f1 hc2
  refine run_addc _ _ _ _ _ _ (by decide) hs16
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
  intro _ _ _ _ T2 C3 s17 hs17 f2 hc3
  refine run_addc _ _ _ _ _ _ (by decide) hs17
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc3) ?_
  intro _ _ _ _ T3 C4 s18 hs18 f3 hc4
  refine run_addcc _ _ _ _ (by decide) hs18 ?_; intro T4 C5 s19 hs19 f4 _
  simp only [upd, ↓reduceIte, String.reduceEq] at e1 e2 e3 e4 f0 f1 f2 f3 f4 hc4
  have hk : (BitVec.ofNat 64 38).toNat = 38 := rfl
  have r0 := mul_mulhu_recompose (R "acc4") (BitVec.ofNat 64 38)
  have r1 := mul_mulhu_recompose (R "acc5") (BitVec.ofNat 64 38)
  have r2 := mul_mulhu_recompose (R "acc6") (BitVec.ofNat 64 38)
  have r3 := mul_mulhu_recompose (R "acc7") (BitVec.ofNat 64 38)
  simp only [hk] at r0 r1 r2 r3 e1 e2 e3 e4
  obtain ⟨hj4, hH⟩ := mul38_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (R "acc7").isLt J4.isLt r0 r1 r2 r3 e1 e2 e3 e4 hq3
  obtain ⟨ht4, hT⟩ := addT_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj4 T4.isLt
    f0 f1 f2 f3 f4 hc4
  refine (fold5_run (by decide) hs19 (by simp only [upd, ↓reduceIte]; exact ht4)).mono ?_
  rintro R' ⟨hv, _⟩
  rw [hv]
  simp only [limbs4, upd, ↓reduceIte, String.reduceEq]
  rw [hT, hH, fold38_mod]
  unfold acc8
  congr 1
  omega

/-! ## The field multiply and square -/

theorem zeroAcc_eq : zeroAcc = [.li "acc0" 0, .li "acc1" 0, .li "acc2" 0, .li "acc3" 0,
    .li "acc4" 0, .li "acc5" 0, .li "acc6" 0, .li "acc7" 0] := by
  have e : zeroAcc = (List.range 8).map (fun k => ROp64.li (accAt k) 0) := rfl
  simp [e, List.range_succ, accAt0, accAt1, accAt2, accAt3, accAt4, accAt5, accAt6, accAt7]

/-- The marshalling and zeroing before the schoolbook. -/
def feMulPrep : List ROp64 :=
  [ .mov "u0" "q0", .mov "u1" "q1", .mov "u2" "q2", .mov "u3" "q3"
  , .mov "v0" "y0", .mov "v1" "y1", .mov "v2" "y2", .mov "v3" "y3" ] ++ zeroAcc

theorem feMulBlock_eq : feMulBlock = feMulPrep ++ mul48Block64 ++ feMulReduce := rfl

set_option exponentiation.threshold 600 in
theorem prep_run {R : AStateR} {s : RState64} (hs : SRr s R) :
    Reach (fun R' => limbs4 R' "u0" "u1" "u2" "u3" = limbs4 R "q0" "q1" "q2" "q3" ∧
        limbs4 R' "v0" "v1" "v2" "v3" = limbs4 R "y0" "y1" "y2" "y3" ∧ acc8 R' = 0)
      (runRBlock64 s (lowerRBlock64 feMulPrep)) := by
  unfold feMulPrep
  rw [zeroAcc_eq]
  simp only [List.cons_append, List.nil_append, lowerRBlock64_cons, lowerRBlock64_nil]
  refine run_mov _ _ (by decide) hs ?_; intro s1 hs1
  refine run_mov _ _ (by decide) hs1 ?_; intro s2 hs2
  refine run_mov _ _ (by decide) hs2 ?_; intro s3 hs3
  refine run_mov _ _ (by decide) hs3 ?_; intro s4 hs4
  refine run_mov _ _ (by decide) hs4 ?_; intro s5 hs5
  refine run_mov _ _ (by decide) hs5 ?_; intro s6 hs6
  refine run_mov _ _ (by decide) hs6 ?_; intro s7 hs7
  refine run_mov _ _ (by decide) hs7 ?_; intro s8 hs8
  refine run_li _ _ (by decide) hs8 ?_; intro s9 hs9
  refine run_li _ _ (by decide) hs9 ?_; intro s10 hs10
  refine run_li _ _ (by decide) hs10 ?_; intro s11 hs11
  refine run_li _ _ (by decide) hs11 ?_; intro s12 hs12
  refine run_li _ _ (by decide) hs12 ?_; intro s13 hs13
  refine run_li _ _ (by decide) hs13 ?_; intro s14 hs14
  refine run_li _ _ (by decide) hs14 ?_; intro s15 hs15
  refine run_li _ _ (by decide) hs15 ?_; intro s16 hs16
  refine run_nil hs16 ⟨?_, ?_, ?_⟩
  · simp only [limbs4, upd, ↓reduceIte, String.reduceEq]
  · simp only [limbs4, upd, ↓reduceIte, String.reduceEq]
  · simp only [acc8, upd, ↓reduceIte, String.reduceEq]; rfl

/-- **`feMulBlock` computes the field product** in `z0..z3`, from `x` in `q0..q3` and
    `y` in `y0..y3`. -/
theorem feMul_run {R : AStateR} {s : RState64} (hs : SRr s R) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3"
        = limbs4 R "q0" "q1" "q2" "q3" * limbs4 R "y0" "y1" "y2" "y3" % p25519)
      (runRBlock64 s (lowerRBlock64 feMulBlock)) := by
  rw [feMulBlock_eq, lowerRBlock64_append, lowerRBlock64_append]
  refine reach_append (reach_append (prep_run hs) fun R1 t1 h1 ⟨hu, hv, h0⟩ =>
    (mul48_run h1 h0).mono fun R2 ⟨e2, _⟩ => ?_) fun R2 t2 h2 (e2 : acc8 R2 = _) =>
      (reduce_run h2).mono fun R3 h3 => by rw [h3, e2]
  exact (show acc8 R2 = limbs4 R "q0" "q1" "q2" "q3" * limbs4 R "y0" "y1" "y2" "y3" by
    rw [e2, hu, hv])

theorem feSqrBlock_eq : feSqrBlock =
    [.mov "y0" "q0", .mov "y1" "q1", .mov "y2" "q2", .mov "y3" "q3"] ++ feMulBlock := rfl

/-- **`feSqrBlock` computes the field square** in `z0..z3`, from `x` in `q0..q3`. -/
theorem feSqr_run {R : AStateR} {s : RState64} (hs : SRr s R) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3"
        = limbs4 R "q0" "q1" "q2" "q3" * limbs4 R "q0" "q1" "q2" "q3" % p25519)
      (runRBlock64 s (lowerRBlock64 feSqrBlock)) := by
  rw [feSqrBlock_eq, lowerRBlock64_append]
  simp only [lowerRBlock64_cons, lowerRBlock64_nil, List.append_nil, List.append_assoc]
  refine run_mov _ _ (by decide) hs ?_; intro s1 hs1
  refine run_mov _ _ (by decide) hs1 ?_; intro s2 hs2
  refine run_mov _ _ (by decide) hs2 ?_; intro s3 hs3
  refine run_mov _ _ (by decide) hs3 ?_; intro s4 hs4
  refine (feMul_run hs4).mono fun R' h => ?_
  rw [h]
  simp only [limbs4, upd, ↓reduceIte, String.reduceEq]

/-! ## The closed statements -/

/-- **`feMulBlock` computes the field product.** For every machine state, running the
    lowered block leaves `x · y mod p25519` in `z0..z3`, with `x` the limbs in `q0..q3`
    and `y` those in `y0..y3`. -/
theorem feMul_correct (s : RState64) :
    limbs4 (runRBlock64 s (lowerRBlock64 feMulBlock)).get "z0" "z1" "z2" "z3"
      = limbs4 s.get "q0" "q1" "q2" "q3" * limbs4 s.get "y0" "y1" "y2" "y3" % p25519 :=
  reach_get (feMul_run (SRr_self s))

/-- **`feSqrBlock` computes the field square.** -/
theorem feSqr_correct (s : RState64) :
    limbs4 (runRBlock64 s (lowerRBlock64 feSqrBlock)).get "z0" "z1" "z2" "z3"
      = limbs4 s.get "q0" "q1" "q2" "q3" * limbs4 s.get "q0" "q1" "q2" "q3" % p25519 :=
  reach_get (feSqr_run (SRr_self s))

/-- `feMul_correct`, canonical and in `ZMod p25519`. -/
theorem feMul_correct_zmod (s : RState64) :
    limbs4 (runRBlock64 s (lowerRBlock64 feMulBlock)).get "z0" "z1" "z2" "z3" < p25519 ∧
      ((limbs4 (runRBlock64 s (lowerRBlock64 feMulBlock)).get "z0" "z1" "z2" "z3" : Nat)
          : ZMod p25519)
        = (limbs4 s.get "q0" "q1" "q2" "q3" : ZMod p25519)
          * (limbs4 s.get "y0" "y1" "y2" "y3" : ZMod p25519) := by
  rw [feMul_correct]
  refine ⟨Nat.mod_lt _ p25519_pos, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul]

/-- `feSqr_correct`, canonical and in `ZMod p25519`. -/
theorem feSqr_correct_zmod (s : RState64) :
    limbs4 (runRBlock64 s (lowerRBlock64 feSqrBlock)).get "z0" "z1" "z2" "z3" < p25519 ∧
      ((limbs4 (runRBlock64 s (lowerRBlock64 feSqrBlock)).get "z0" "z1" "z2" "z3" : Nat)
          : ZMod p25519)
        = (limbs4 s.get "q0" "q1" "q2" "q3" : ZMod p25519) ^ 2 := by
  rw [feSqr_correct]
  refine ⟨Nat.mod_lt _ p25519_pos, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul, sq]

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519MulProof.feMul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feMul_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519MulProof
