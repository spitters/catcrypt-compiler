/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy

/-!
# The secp256k1 field add and subtract bricks, on all inputs

`Secp256k1PointOpFront.emitFOp` turns one schedule entry into a flat `List LowCT`
over 32-bit half-limbs held in 64-bit words: the operand-scanning builders
`Secp256k1FeMulFront.genAdd` / `genSub`, a branch-free mask, and eight copies into
the output field element's half-limb slots. This module gives the `add` and `sub`
arms their value semantics under `TranslateDialectScalar.semScalar`, symbolically —
no emitted command list is reduced and no concrete 256-bit value is evaluated.

The proof runs at generator granularity, mirroring the coverage argument of
`Secp256k1PointOpFrontCovered`. Each builder's `Id.run do` loop is identified with
an explicit `Nat`-recursion by a trip-indexed loop invariant (`forInRangeIdx`), and
that recursion is then read back through `semScalar` one trip at a time, carrying
the limb bound, the carry (or borrow) bound and the weighted-sum identity as a
single induction.

## The environment scope

The bricks compute their base-field operation on the environments `BrickScope`
describes: `ZZ` holds `0`, `PL0 .. PL7` hold the 32-bit limbs of `p`, and every
schedule-name field element's eight half-limb slots hold a canonical residue below
`p` in limbs below `2^32`. The scope is needed — the generated carry chain reads
`ZZ` as its incoming carry and `PL0 .. PL7` as the modulus, and the operand-scanning
columns stay inside 64 bits only for 32-bit limbs. `brickStep_addSub` re-establishes
`BrickScope` on the output environment, so the scope threads along a schedule.

## Main results

* `forInRangeIdx` — a trip-indexed invariant for an `Id`-monad `forIn` over `[:n]`.
* `aCmds_sem`, `sCmds_sem` — the operand-scanning add and the ripple subtract:
  the emitted trips leave the weighted limb sum and the carry/borrow bound.
* `feAddHalves_sem`, `feSubHalves_sem` — the two field bricks: the result names
  carry `fa` / `fs` of the operands' half-limb readout, and every name outside the
  brick's private prefix is untouched.
* `brickWire_step` — a brick plus its output copy moves the schedule-name readout
  by one `envUpd`.
* `brickStep_add`, `brickStep_sub`, `brickStep_addSub` — the per-brick obligation of
  `Secp256k1PointOpFrontDenote` on the `add` and `sub` arms, over `BrickScope`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
  (seqAll mask32 sv genAdd genSub pNat pl32 cc0 cc1)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp emitFOp feH feAddHalves feSubHalves plNames fm fa fs)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (feVal schedNameB FOpSchedOkB)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional (stepFOpG envUpd)

/-! ## 1. Name algebra -/

/-- Two names built by appending different suffixes to a common prefix differ. -/
theorem pfxNe {p u v : String} (h : u ≠ v) : p ++ u ≠ p ++ v :=
  fun he => h ((String.append_right_inj p).mp he)

/-- The first character of a name. -/
def hd (s : String) : Option Char := s.toList.head?

theorem hdAppend {u v : String} {c : Char} (h : hd u = some c) : hd (u ++ v) = some c := by
  unfold hd at h ⊢
  rw [String.toList_append]
  cases hu : u.toList with
  | nil => rw [hu] at h; simp at h
  | cons a t => rw [hu] at h; simpa using! h

/-- Names whose first characters differ are different. -/
theorem neOfHd {u v : String} {c d : Char} (hu : hd u = some c) (hv : hd v = some d)
    (h : c ≠ d) : u ≠ v := by
  intro he; rw [he, hv] at hu; exact h (Option.some.inj hu.symm)

/-! ## 2. The waist semantics of a `seqAll` is the command-list semantics -/

theorem semScalar_seqAll_eq_semList : ∀ (l : List LowCT) (env : SEnvScalar),
    semScalar (seqAll l) env = semList l env := by
  intro l
  induction l with
  | nil => intro env; rfl
  | cons c cs ih =>
      intro env
      rw [Secp256k1PointOpFrontDenote.semScalar_seqAll_cons, semList_cons]
      cases semScalar c env with
      | none => rfl
      | some e => simpa using ih e

/-! ## 3. A trip-indexed loop invariant -/

theorem forInRange'Idx {σ : Type} (P : Nat → σ → Prop) (f : Nat → σ → Id (ForInStep σ))
    (hstep : ∀ i s s', P i s → f i s = ForInStep.yield s' → P (i + 1) s')
    (hnd : ∀ (i : Nat) (s s' : σ), f i s ≠ ForInStep.done s') :
    ∀ (len start : Nat) (init : σ), P start init →
      P (start + len) (forIn (List.range' start len 1) init f) := by
  intro len
  induction len with
  | zero => intro start init h; simpa using! h
  | succ len ih =>
      intro start init h
      rw [List.range'_succ, List.forIn_cons]
      show P (start + (len + 1))
        (match f start init with
          | .done b => (pure b : Id σ)
          | .yield b => forIn (List.range' (start + 1) len 1) b f)
      cases hfa : f start init with
      | done b => exact absurd hfa (hnd start init b)
      | yield b =>
          have := ih (start + 1) b (hstep start init b h hfa)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! this

/-- A trip-indexed state predicate carried across an `Id`-monad `forIn` over `[:n]`. -/
theorem forInRangeIdx {σ : Type} (P : Nat → σ → Prop) (n : Nat)
    (f : Nat → σ → Id (ForInStep σ)) (init : σ) (hinit : P 0 init)
    (hstep : ∀ i s s', P i s → f i s = ForInStep.yield s' → P (i + 1) s')
    (hnd : ∀ (i : Nat) (s s' : σ), f i s ≠ ForInStep.done s') :
    P n (forIn [:n] init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have := forInRange'Idx P f hstep hnd n 0 init hinit
  simpa using this

/-! ## 4. Little-endian 32-bit limb values -/

/-- `Σ_{k < n} 2^{32k} · v k`. -/
def accN (v : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => accN v n + 2 ^ (32 * n) * v n

theorem accN_succ (v : Nat → Nat) (n : Nat) :
    accN v (n + 1) = accN v n + 2 ^ (32 * n) * v n := rfl

theorem accN_congr {v w : Nat → Nat} : ∀ n, (∀ k, k < n → v k = w k) → accN v n = accN w n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      rw [accN, accN, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

theorem accN_lt (v : Nat → Nat) : ∀ n, (∀ k, k < n → v k < 2 ^ 32) → accN v n < 2 ^ (32 * n) := by
  intro n
  induction n with
  | zero => intro _; simp [accN]
  | succ n ih =>
      intro h
      have h1 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have h2 := h n (Nat.lt_succ_self n)
      have : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by
        rw [← pow_add]; ring_nf
      rw [accN, this]
      calc accN v n + 2 ^ (32 * n) * v n
          < 2 ^ (32 * n) + 2 ^ (32 * n) * v n := by omega
        _ ≤ 2 ^ (32 * n) * 2 ^ 32 := by nlinarith [Nat.one_le_two_pow (n := 32 * n)]

/-! ## 5. Indexed names -/

theorem tagNe {a b : String} {ca cb : Char} (ha : hd a = some ca) (hb : hd b = some cb)
    (h : ca ≠ cb) (i j : Nat) : a ++ toString i ≠ b ++ toString j :=
  neOfHd (hdAppend ha) (hdAppend hb) h

theorem idxNe (a : String) {i j : Nat} (h : i ≠ j) : a ++ toString i ≠ a ++ toString j := by
  intro he
  exact h (repr_injective (by simpa [toString] using! (String.append_right_inj a).mp he))

/-- Two indexed names under a common prefix differ when their tag-and-index suffixes do. -/
theorem nmNe (p : String) {a b : String} {i j : Nat} (h : a ++ toString i ≠ b ++ toString j) :
    p ++ a ++ toString i ≠ p ++ b ++ toString j := by
  rw [String.append_assoc, String.append_assoc]
  exact pfxNe h

/-! ## 6. `BitVec` readings of the emitted `SExpr` arms -/

theorem bvAdd_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bvSub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le h

theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bvAnd_mask (a : BitVec 64) :
    (a &&& BitVec.ofNat 64 mask32).toNat = a.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and, ofNat_toNat (by norm_num [mask32]),
    show mask32 = 2 ^ 32 - 1 by norm_num [mask32], Nat.and_two_pow_sub_one_eq_mod]

theorem bvAnd_zero (x : BitVec 64) : (x &&& (0 : BitVec 64)).toNat = 0 := by
  rw [BitVec.toNat_and]; simp

theorem bvAnd_mask_lt {y : BitVec 64} (hy : y.toNat < 2 ^ 32) :
    (y &&& BitVec.ofNat 64 mask32).toNat = y.toNat := by
  rw [bvAnd_mask, Nat.mod_eq_of_lt hy]

/-- The select value when the mask selects the second operand. -/
theorem selRight {x y : BitVec 64} (hy : y.toNat < 2 ^ 32) :
    ((x &&& (0 : BitVec 64)) + (y &&& BitVec.ofNat 64 mask32)).toNat = y.toNat := by
  rw [bvAdd_toNat (by rw [bvAnd_zero, bvAnd_mask_lt hy]; omega), bvAnd_zero, bvAnd_mask_lt hy]
  omega

/-- The select value when the mask selects the first operand. -/
theorem selLeft {x y : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    ((x &&& BitVec.ofNat 64 mask32) + (y &&& (0 : BitVec 64))).toNat = x.toNat := by
  rw [bvAdd_toNat (by rw [bvAnd_zero, bvAnd_mask_lt hx]; omega), bvAnd_zero, bvAnd_mask_lt hx]
  omega

/-- A logical right shift by the masked count `32` divides by `2 ^ 32`. -/
theorem bvShr32 (a : BitVec 64) :
    (a >>> VIR.shiftMask 64 (BitVec.ofNat 64 32).toNat).toNat = a.toNat / 2 ^ 32 := by
  rw [ofNat_toNat (by norm_num), VIR.shiftMask_of_lt (by decide), BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

/-! ## 7. Reading back one emitted assignment -/

theorem stepAt {x : String} {e : SExpr} {env env' : SEnvScalar}
    (h : semList [LowCT.RScalarSetExpr x e] env = some env') :
    envReader env' x = SExpr.evalBV (envReader env) e :=
  envReader_setExpr_at (by rwa [semList_single] at h)

theorem stepOff {x : String} {e : SExpr} {env env' : SEnvScalar}
    (h : semList [LowCT.RScalarSetExpr x e] env = some env') (s : String)
    (hs : ¬ isTmpName s) (hne : s ≠ x) : envReader env' s = envReader env s :=
  envReader_setExpr_off (by rwa [semList_single] at h) s hs hne

/-- Peel the first command off a successful run of a nonempty block. -/
theorem peel {c : LowCT} {l : List LowCT} {env env' : SEnvScalar}
    (h : semList (c :: l) env = some env') :
    ∃ e, semList [c] env = some e ∧ semList l e = some env' := by
  obtain ⟨e, h1, h2⟩ := semList_cons_eq h
  exact ⟨e, by rw [semList_single]; exact h1, h2⟩

/-! ## 8. `Array.set!` read-back -/

theorem setBang_size (a : Array String) (p : Nat) (v : String) : (a.set! p v).size = a.size := by
  show (a.setIfInBounds p v).size = a.size
  simp

theorem setBang_get_ne (a : Array String) {p k : Nat} (v : String) (h : k ≠ p) :
    (a.set! p v)[k]! = a[k]! := by
  show (a.setIfInBounds p v)[k]! = a[k]!
  by_cases hk : k < a.size
  · rw [getElem!_pos (a.setIfInBounds p v) k (by simpa using! hk), getElem!_pos a k hk]
    exact Array.getElem_setIfInBounds_ne hk (Ne.symm h)
  · rw [getElem!_neg (a.setIfInBounds p v) k (by simpa using! hk), getElem!_neg a k hk]

theorem setBang_get_eq (a : Array String) {p : Nat} (v : String) (h : p < a.size) :
    (a.set! p v)[p]! = v := by
  show (a.setIfInBounds p v)[p]! = v
  rw [getElem!_pos (a.setIfInBounds p v) p (by simpa using! h)]
  simp

/-! ## 9. The operand-scanning add, unrolled -/

/-- The carry slot entering trip `i` of `genAdd`. -/
def aCar (zero pfx : String) : Nat → String
  | 0 => zero
  | i + 1 => s!"{pfx}k{i}"

/-- The three commands `genAdd` emits at trip `i`. -/
def aTrip (zero : String) (aN bN : List String) (pfx : String) (i : Nat) : List LowCT :=
  [ LowCT.RScalarSetExpr s!"{pfx}t{i}"
      (.SAdd (.SAdd (sv (aN.getD i zero)) (sv (bN.getD i zero))) (sv (aCar zero pfx i)))
  , LowCT.RScalarSetExpr s!"{pfx}s{i}" (.SAnd (sv s!"{pfx}t{i}") (.SLit mask32))
  , LowCT.RScalarSetExpr s!"{pfx}k{i}" (.SShr (sv s!"{pfx}t{i}") (.SLit 32)) ]

/-- The commands `genAdd` has emitted after `i` trips. -/
def aCmds (zero : String) (aN bN : List String) (pfx : String) : Nat → List LowCT
  | 0 => []
  | i + 1 => aCmds zero aN bN pfx i ++ aTrip zero aN bN pfx i

/-- The result-name array after `i` trips of `genAdd` over an `n`-limb operand pair. -/
def aRes (zero pfx : String) (n : Nat) : Nat → Array String
  | 0 => Array.replicate (n + 1) zero
  | i + 1 => (aRes zero pfx n i).set! i s!"{pfx}s{i}"

theorem aRes_size (zero pfx : String) (n : Nat) : ∀ i, (aRes zero pfx n i).size = n + 1 := by
  intro i
  induction i with
  | zero => simp [aRes]
  | succ i ih => rw [aRes, setBang_size, ih]

theorem aRes_get (zero pfx : String) (n : Nat) :
    ∀ (i k : Nat), k < i → i ≤ n + 1 → (aRes zero pfx n i)[k]! = s!"{pfx}s{k}" := by
  intro i
  induction i with
  | zero => intro k hk; omega
  | succ i ih =>
      intro k hk hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · rw [aRes, setBang_get_ne _ _ (by omega)]
        exact ih k h (by omega)
      · subst h
        rw [aRes, setBang_get_eq _ _ (by rw [aRes_size]; omega)]

open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (genAddStep genAddRun genAdd_eq genSubStep genSubRun genSub_eq HeadOk AddS SubS
   arrayToList_getBang)

/-- The `genAdd` loop state after `i` trips. -/
def aState (zero : String) (aN bN : List String) (pfx : String) (i : Nat) : AddS :=
  ⟨aCar zero pfx i, aCmds zero aN bN pfx i, aRes zero pfx (max aN.length bN.length) i⟩

theorem genAddRun_spec (zero : String) (aN bN : List String) (pfx : String) :
    genAddRun zero aN bN pfx = aState zero aN bN pfx (max aN.length bN.length) := by
  unfold genAddRun
  refine forInRangeIdx (fun i s => s = aState zero aN bN pfx i) _ _ _ rfl ?_ ?_
  · intro i s s' hs hy
    subst hs
    simp only [genAddStep, aState] at hy ⊢
    injection hy with hy
    subst hy
    simp only [aCar, aCmds, aTrip, aRes, List.append_assoc, List.cons_append, List.nil_append]
  · intro i s s' h
    simp only [genAddStep] at h
    injection h

theorem genAdd_cmds (zero : String) (aN bN : List String) (pfx : String) :
    (genAdd zero aN bN pfx).1 = aCmds zero aN bN pfx (max aN.length bN.length) := by
  rw [genAdd_eq, genAddRun_spec]
  rfl

theorem genAdd_name (zero : String) (aN bN : List String) (pfx : String) (k : Nat)
    (hk : k < max aN.length bN.length) :
    (genAdd zero aN bN pfx).2[k]! = s!"{pfx}s{k}" := by
  rw [genAdd_eq, genAddRun_spec]
  simp only [aState]
  rw [arrayToList_getBang, setBang_get_ne _ _ (by omega)]
  exact aRes_get zero pfx _ _ k hk (by omega)

theorem genAdd_top (zero : String) (aN bN : List String) (pfx : String) :
    (genAdd zero aN bN pfx).2[max aN.length bN.length]!
      = aCar zero pfx (max aN.length bN.length) := by
  rw [genAdd_eq, genAddRun_spec]
  simp only [aState]
  rw [arrayToList_getBang,
    setBang_get_eq _ _ (by rw [aRes_size]; omega)]

/-! ## 10. Character heads of the emitted tags -/

theorem hd_t : hd "t" = some 't' := rfl
theorem hd_s : hd "s" = some 's' := rfl
theorem hd_k : hd "k" = some 'k' := rfl
theorem hd_d : hd "d" = some 'd' := rfl
theorem hd_h : hd "h" = some 'h' := rfl
theorem hd_b : hd "b" = some 'b' := rfl

/-- Split a successful run at a command-list concatenation. -/
theorem splitApp {l₁ l₂ : List LowCT} {env env' : SEnvScalar}
    (h : semList (l₁ ++ l₂) env = some env') :
    ∃ e, semList l₁ env = some e ∧ semList l₂ e = some env' := by
  rw [semList_append] at h
  cases he : semList l₁ env with
  | none => rw [he] at h; simp at h
  | some e => exact ⟨e, rfl, by rw [he] at h; simpa using! h⟩

/-- A name outside the `pfx` namespace differs from an indexed `pfx` name. -/
theorem outNe {s pfx : String} (hs : ∀ w : String, s ≠ pfx ++ w) (a : String) (i : Nat) :
    s ≠ pfx ++ a ++ toString i := by
  rw [String.append_assoc]; exact hs _

/-! ## 11. The add chain's value semantics -/

theorem aCmds_sem (zero : String) (aN bN : List String) (pfx : String)
    (hp : HeadOk pfx)
    (hAn : ∀ i, ¬ isTmpName (aN.getD i zero)) (hBn : ∀ i, ¬ isTmpName (bN.getD i zero))
    (hAo : ∀ (i : Nat) (w : String), aN.getD i zero ≠ pfx ++ w)
    (hBo : ∀ (i : Nat) (w : String), bN.getD i zero ≠ pfx ++ w)
    (env : SEnvScalar) (hz0 : (envReader env zero).toNat = 0)
    (hA : ∀ i, (envReader env (aN.getD i zero)).toNat < 2 ^ 32)
    (hB : ∀ i, (envReader env (bN.getD i zero)).toNat < 2 ^ 32) :
    ∀ (i : Nat) (envI : SEnvScalar), semList (aCmds zero aN bN pfx i) env = some envI →
      (∀ s, ¬ isTmpName s → (∀ w : String, s ≠ pfx ++ w) → envReader envI s = envReader env s)
      ∧ (∀ k, k < i → (envReader envI s!"{pfx}s{k}").toNat < 2 ^ 32)
      ∧ (envReader envI (aCar zero pfx i)).toNat ≤ 1
      ∧ accN (fun k => (envReader envI s!"{pfx}s{k}").toNat) i
            + 2 ^ (32 * i) * (envReader envI (aCar zero pfx i)).toNat
          = accN (fun k => (envReader env (aN.getD k zero)).toNat) i
            + accN (fun k => (envReader env (bN.getD k zero)).toNat) i := by
  have hnt : ∀ u : String, ¬ isTmpName (pfx ++ u) :=
    fun u => Secp256k1PointOpFrontCovered.HeadOk.notTmp (Secp256k1PointOpFrontCovered.HeadOk.append hp u)
  have hntI : ∀ (u : String) (j : Nat), ¬ isTmpName (pfx ++ u ++ toString j) := by
    intro u j; rw [String.append_assoc]; exact hnt _
  intro i
  induction i with
  | zero =>
      intro envI hsem
      simp only [aCmds, semList] at hsem
      obtain rfl : envI = env := (Option.some.inj hsem).symm
      exact ⟨fun _ _ _ => rfl, fun k hk => absurd hk (by omega), by rw [aCar]; omega, by
        simp [accN, aCar, hz0]⟩
  | succ i ih =>
      intro env' hsem
      rw [aCmds] at hsem
      obtain ⟨envI, hpre, htrip⟩ := splitApp hsem
      obtain ⟨hfr, hslt, hcle, hacc⟩ := ih envI hpre
      simp only [aTrip] at htrip
      obtain ⟨e1, h1, r1⟩ := peel htrip
      obtain ⟨e2, h2, r2⟩ := peel r1
      obtain ⟨e3, h3, r3⟩ := peel r2
      have hE3 : env' = e3 := (Option.some.inj r3).symm
      subst hE3
      -- names
      set tn := s!"{pfx}t{i}" with htn
      set sn := s!"{pfx}s{i}" with hsn
      set kn := s!"{pfx}k{i}" with hkn
      have htn_sn : tn ≠ sn := nmNe pfx (tagNe hd_t hd_s (by decide) i i)
      have hsn_kn : sn ≠ kn := nmNe pfx (tagNe hd_s hd_k (by decide) i i)
      have hsk_tn : ∀ k, s!"{pfx}s{k}" ≠ tn := fun k => nmNe pfx (tagNe hd_s hd_t (by decide) k i)
      have hsk_kn : ∀ k, s!"{pfx}s{k}" ≠ kn := fun k => nmNe pfx (tagNe hd_s hd_k (by decide) k i)
      have hsk_sn : ∀ k, k ≠ i → s!"{pfx}s{k}" ≠ sn := fun k hk => nmNe pfx (idxNe "s" hk)
      -- values entering the trip
      have hAi : envReader envI (aN.getD i zero) = envReader env (aN.getD i zero) :=
        hfr _ (hAn i) (hAo i)
      have hBi : envReader envI (bN.getD i zero) = envReader env (bN.getD i zero) :=
        hfr _ (hBn i) (hBo i)
      set A := (envReader env (aN.getD i zero)).toNat with hAdef
      set B := (envReader env (bN.getD i zero)).toNat with hBdef
      set C := (envReader envI (aCar zero pfx i)).toNat with hCdef
      have hAlt : A < 2 ^ 32 := hA i
      have hBlt : B < 2 ^ 32 := hB i
      -- the trip's first command
      have hv1 : (envReader e1 tn).toNat = A + B + C := by
        rw [stepAt h1]
        simp only [SExpr.evalBV, sv]
        rw [bvAdd_toNat (by rw [bvAdd_toNat (by rw [hAi, hBi]; omega), hAi, hBi]; omega),
          bvAdd_toNat (by rw [hAi, hBi]; omega), hAi, hBi]
      have hsum : A + B + C < 2 ^ 33 := by omega
      -- the trip's second command
      have ht2 : envReader e2 tn = envReader e1 tn := stepOff h2 tn (hntI _ _) htn_sn
      have hv2 : (envReader e2 sn).toNat = (A + B + C) % 2 ^ 32 := by
        rw [stepAt h2]
        simp only [SExpr.evalBV, sv]
        rw [bvAnd_mask, hv1]
      -- the trip's third command
      have hv3 : (envReader env' kn).toNat = (A + B + C) / 2 ^ 32 := by
        rw [stepAt h3]
        simp only [SExpr.evalBV, sv]
        rw [bvShr32, ht2, hv1]
      have hsnFinal : (envReader env' sn).toNat = (A + B + C) % 2 ^ 32 := by
        rw [stepOff h3 sn (hntI _ _) hsn_kn, hv2]
      have hkeep : ∀ k, k ≠ i → envReader env' s!"{pfx}s{k}" = envReader envI s!"{pfx}s{k}" := by
        intro k hk
        rw [stepOff h3 s!"{pfx}s{k}" (hntI "s" k) (hsk_kn k),
          stepOff h2 s!"{pfx}s{k}" (hntI "s" k) (hsk_sn k hk),
          stepOff h1 s!"{pfx}s{k}" (hntI "s" k) (hsk_tn k)]
      have hfr' : ∀ s, ¬ isTmpName s → (∀ w : String, s ≠ pfx ++ w) →
          envReader env' s = envReader env s := by
        intro s hs hso
        rw [stepOff h3 s hs (outNe hso "k" i), stepOff h2 s hs (outNe hso "s" i),
          stepOff h1 s hs (outNe hso "t" i)]
        exact hfr s hs hso
      refine ⟨hfr', ?_, ?_, ?_⟩
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · rw [hkeep k (by omega)]; exact hslt k h
        · subst h; rw [hsnFinal]; exact Nat.mod_lt _ (by norm_num)
      · rw [show aCar zero pfx (i + 1) = kn from rfl, hv3]; omega
      · rw [show aCar zero pfx (i + 1) = kn from rfl, accN, accN, accN,
          accN_congr i (fun k hk => by rw [hkeep k (by omega)]), hsnFinal, hv3]
        have hpow : (2 : Nat) ^ (32 * (i + 1)) = 2 ^ (32 * i) * 2 ^ 32 := by
          rw [← pow_add]; ring_nf
        have hmd : (A + B + C) % 2 ^ 32 + 2 ^ 32 * ((A + B + C) / 2 ^ 32) = A + B + C :=
          Nat.mod_add_div _ _
        rw [hpow]
        set M := (2 : Nat) ^ (32 * i)
        set S := accN (fun k => (envReader envI s!"{pfx}s{k}").toNat) i
        set r := (A + B + C) % 2 ^ 32
        set q := (A + B + C) / 2 ^ 32
        have e1' : S + M * r + M * 2 ^ 32 * q = S + M * (r + 2 ^ 32 * q) := by ring
        rw [e1', hmd]
        have e2' : S + M * (A + B + C) = (S + M * C) + M * A + M * B := by ring
        rw [e2', hacc]
        ring

/-! ## 12. The ripple subtract, unrolled -/

/-- The borrow slot entering trip `i` of `genSub`. -/
def sBor (zero pfx : String) : Nat → String
  | 0 => zero
  | i + 1 => s!"{pfx}b{i}"

/-- The four commands `genSub` emits at trip `i`. -/
def sTrip (zero : String) (aN pN : List String) (pfx : String) (i : Nat) : List LowCT :=
  [ LowCT.RScalarSetExpr s!"{pfx}t{i}"
      (.SSub (.SSub (.SAdd (sv (aN[i]!)) (.SLit 4294967296)) (sv (pN.getD i zero)))
        (sv (sBor zero pfx i)))
  , LowCT.RScalarSetExpr s!"{pfx}d{i}" (.SAnd (sv s!"{pfx}t{i}") (.SLit mask32))
  , LowCT.RScalarSetExpr s!"{pfx}h{i}" (.SShr (sv s!"{pfx}t{i}") (.SLit 32))
  , LowCT.RScalarSetExpr s!"{pfx}b{i}" (.SSub (.SLit 1) (sv s!"{pfx}h{i}")) ]

/-- The commands `genSub` has emitted after `i` trips. -/
def sCmds (zero : String) (aN pN : List String) (pfx : String) : Nat → List LowCT
  | 0 => []
  | i + 1 => sCmds zero aN pN pfx i ++ sTrip zero aN pN pfx i

/-- The difference-name array after `i` trips of `genSub` over an `n`-limb minuend. -/
def sRes (zero pfx : String) (n : Nat) : Nat → Array String
  | 0 => Array.replicate n zero
  | i + 1 => (sRes zero pfx n i).set! i s!"{pfx}d{i}"

theorem sRes_size (zero pfx : String) (n : Nat) : ∀ i, (sRes zero pfx n i).size = n := by
  intro i
  induction i with
  | zero => simp [sRes]
  | succ i ih => rw [sRes, setBang_size, ih]

theorem sRes_get (zero pfx : String) (n : Nat) :
    ∀ (i k : Nat), k < i → i ≤ n → (sRes zero pfx n i)[k]! = s!"{pfx}d{k}" := by
  intro i
  induction i with
  | zero => intro k hk; omega
  | succ i ih =>
      intro k hk hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · rw [sRes, setBang_get_ne _ _ (by omega)]
        exact ih k h (by omega)
      · subst h
        rw [sRes, setBang_get_eq _ _ (by rw [sRes_size]; omega)]

/-- The `genSub` loop state after `i` trips. -/
def sState (zero : String) (aN pN : List String) (pfx : String) (i : Nat) : SubS :=
  ⟨sBor zero pfx i, sCmds zero aN pN pfx i, sRes zero pfx aN.length i⟩

theorem genSubRun_spec (zero : String) (aN pN : List String) (pfx : String) :
    genSubRun zero aN pN pfx = sState zero aN pN pfx aN.length := by
  unfold genSubRun
  refine forInRangeIdx (fun i s => s = sState zero aN pN pfx i) _ _ _ rfl ?_ ?_
  · intro i s s' hs hy
    subst hs
    simp only [genSubStep, sState] at hy ⊢
    injection hy with hy
    subst hy
    simp only [sBor, sCmds, sTrip, sRes, List.append_assoc, List.cons_append, List.nil_append]
  · intro i s s' h
    simp only [genSubStep] at h
    injection h

theorem genSub_cmds (zero : String) (aN pN : List String) (pfx : String) :
    (genSub zero aN pN pfx).1 = sCmds zero aN pN pfx aN.length := by
  rw [genSub_eq, genSubRun_spec]
  rfl

theorem genSub_name (zero : String) (aN pN : List String) (pfx : String) (k : Nat)
    (hk : k < aN.length) : (genSub zero aN pN pfx).2.1[k]! = s!"{pfx}d{k}" := by
  rw [genSub_eq, genSubRun_spec]
  simp only [sState]
  rw [arrayToList_getBang]
  exact sRes_get zero pfx _ _ k hk (by omega)

theorem genSub_borrow (zero : String) (aN pN : List String) (pfx : String) :
    (genSub zero aN pN pfx).2.2 = sBor zero pfx aN.length := by
  rw [genSub_eq, genSubRun_spec]
  rfl

/-! ## 13. The subtract chain's value semantics -/

theorem sCmds_sem (zero : String) (aN pN : List String) (pfx : String) (n : Nat)
    (hp : HeadOk pfx)
    (hAn : ∀ i, i < n → ¬ isTmpName (aN[i]!)) (hPn : ∀ i, i < n → ¬ isTmpName (pN.getD i zero))
    (hAo : ∀ (i : Nat) (w : String), i < n → aN[i]! ≠ pfx ++ w)
    (hPo : ∀ (i : Nat) (w : String), i < n → pN.getD i zero ≠ pfx ++ w)
    (env : SEnvScalar) (hz0 : (envReader env zero).toNat = 0)
    (hA : ∀ i, i < n → (envReader env (aN[i]!)).toNat < 2 ^ 32)
    (hP : ∀ i, i < n → (envReader env (pN.getD i zero)).toNat < 2 ^ 32) :
    ∀ (i : Nat), i ≤ n → ∀ (envI : SEnvScalar),
      semList (sCmds zero aN pN pfx i) env = some envI →
      (∀ s, ¬ isTmpName s → (∀ w : String, s ≠ pfx ++ w) → envReader envI s = envReader env s)
      ∧ (∀ k, k < i → (envReader envI s!"{pfx}d{k}").toNat < 2 ^ 32)
      ∧ (envReader envI (sBor zero pfx i)).toNat ≤ 1
      ∧ accN (fun k => (envReader envI s!"{pfx}d{k}").toNat) i
            + accN (fun k => (envReader env (pN.getD k zero)).toNat) i
          = accN (fun k => (envReader env (aN[k]!)).toNat) i
            + 2 ^ (32 * i) * (envReader envI (sBor zero pfx i)).toNat := by
  have hnt : ∀ u : String, ¬ isTmpName (pfx ++ u) :=
    fun u => Secp256k1PointOpFrontCovered.HeadOk.notTmp
      (Secp256k1PointOpFrontCovered.HeadOk.append hp u)
  have hntI : ∀ (u : String) (j : Nat), ¬ isTmpName (pfx ++ u ++ toString j) := by
    intro u j; rw [String.append_assoc]; exact hnt _
  intro i
  induction i with
  | zero =>
      intro _ envI hsem
      simp only [sCmds, semList] at hsem
      obtain rfl : envI = env := (Option.some.inj hsem).symm
      exact ⟨fun _ _ _ => rfl, fun k hk => absurd hk (by omega), by rw [sBor]; omega, by
        simp [accN, sBor, hz0]⟩
  | succ i ih =>
      intro hin env' hsem
      rw [sCmds] at hsem
      obtain ⟨envI, hpre, htrip⟩ := splitApp hsem
      obtain ⟨hfr, hdlt, hble, hacc⟩ := ih (by omega) envI hpre
      have hi : i < n := by omega
      simp only [sTrip] at htrip
      obtain ⟨e1, h1, r1⟩ := peel htrip
      obtain ⟨e2, h2, r2⟩ := peel r1
      obtain ⟨e3, h3, r3⟩ := peel r2
      obtain ⟨e4, h4, r4⟩ := peel r3
      have hE4 : env' = e4 := (Option.some.inj r4).symm
      subst hE4
      set tn := s!"{pfx}t{i}" with htn
      set dn := s!"{pfx}d{i}" with hdn
      set hn := s!"{pfx}h{i}" with hhn
      set bn := s!"{pfx}b{i}" with hbn
      have htn_dn : tn ≠ dn := nmNe pfx (tagNe hd_t hd_d (by decide) i i)
      have hhn_bn : hn ≠ bn := nmNe pfx (tagNe hd_h hd_b (by decide) i i)
      have hdk_tn : ∀ k, s!"{pfx}d{k}" ≠ tn := fun k => nmNe pfx (tagNe hd_d hd_t (by decide) k i)
      have hdk_hn : ∀ k, s!"{pfx}d{k}" ≠ hn := fun k => nmNe pfx (tagNe hd_d hd_h (by decide) k i)
      have hdk_bn : ∀ k, s!"{pfx}d{k}" ≠ bn := fun k => nmNe pfx (tagNe hd_d hd_b (by decide) k i)
      have hdk_dn : ∀ k, k ≠ i → s!"{pfx}d{k}" ≠ dn := fun k hk => nmNe pfx (idxNe "d" hk)
      have hAi : envReader envI (aN[i]!) = envReader env (aN[i]!) :=
        hfr _ (hAn i hi) (fun w => hAo i w hi)
      have hPi : envReader envI (pN.getD i zero) = envReader env (pN.getD i zero) :=
        hfr _ (hPn i hi) (fun w => hPo i w hi)
      set A := (envReader env (aN[i]!)).toNat with hAdef
      set P := (envReader env (pN.getD i zero)).toNat with hPdef
      set b := (envReader envI (sBor zero pfx i)).toNat with hbdef
      have hAlt : A < 2 ^ 32 := hA i hi
      have hPlt : P < 2 ^ 32 := hP i hi
      -- the trip's first command
      have hv1 : (envReader e1 tn).toNat = A + 2 ^ 32 - P - b := by
        rw [stepAt h1]
        simp only [SExpr.evalBV, sv]
        have hlit : ((BitVec.ofNat 64 4294967296) : BitVec 64).toNat = 2 ^ 32 := by
          rw [ofNat_toNat (by norm_num)]; norm_num
        have hs1 : (envReader envI (aN[i]!) + BitVec.ofNat 64 4294967296).toNat = A + 2 ^ 32 := by
          rw [bvAdd_toNat (by rw [hAi, hlit]; omega), hAi, hlit]
        have hs2 : ((envReader envI (aN[i]!) + BitVec.ofNat 64 4294967296)
            - envReader envI (pN.getD i zero)).toNat = A + 2 ^ 32 - P := by
          rw [bvSub_toNat (by rw [hs1, hPi]; omega), hs1, hPi]
        rw [bvSub_toNat (by rw [hs2]; omega), hs2]
      have hble' : b ≤ 1 := hble
      have hv1lt : (envReader e1 tn).toNat < 2 ^ 33 := by rw [hv1]; omega
      have ht2 : envReader e2 tn = envReader e1 tn := stepOff h2 tn (hntI _ _) htn_dn
      have hv2 : (envReader e2 dn).toNat = (envReader e1 tn).toNat % 2 ^ 32 := by
        rw [stepAt h2]; simp only [SExpr.evalBV, sv]; rw [bvAnd_mask]
      have hv3 : (envReader e3 hn).toNat = (envReader e1 tn).toNat / 2 ^ 32 := by
        rw [stepAt h3]; simp only [SExpr.evalBV, sv]; rw [bvShr32, ht2]
      have hh_le : (envReader e3 hn).toNat ≤ 1 := by rw [hv3]; omega
      have hv4 : (envReader env' bn).toNat = 1 - (envReader e3 hn).toNat := by
        rw [stepAt h4]
        simp only [SExpr.evalBV, sv]
        rw [bvSub_toNat (by rw [ofNat_toNat (by norm_num)]; omega), ofNat_toNat (by norm_num)]
      have hdFinal : (envReader env' dn).toNat = (envReader e1 tn).toNat % 2 ^ 32 := by
        rw [stepOff h4 dn (hntI _ _) (hdk_bn i), stepOff h3 dn (hntI _ _) (hdk_hn i), hv2]
      have hkeep : ∀ k, k ≠ i → envReader env' s!"{pfx}d{k}" = envReader envI s!"{pfx}d{k}" := by
        intro k hk
        rw [stepOff h4 s!"{pfx}d{k}" (hntI "d" k) (hdk_bn k),
          stepOff h3 s!"{pfx}d{k}" (hntI "d" k) (hdk_hn k),
          stepOff h2 s!"{pfx}d{k}" (hntI "d" k) (hdk_dn k hk),
          stepOff h1 s!"{pfx}d{k}" (hntI "d" k) (hdk_tn k)]
      have hfr' : ∀ s, ¬ isTmpName s → (∀ w : String, s ≠ pfx ++ w) →
          envReader env' s = envReader env s := by
        intro s hs hso
        rw [stepOff h4 s hs (outNe hso "b" i), stepOff h3 s hs (outNe hso "h" i),
          stepOff h2 s hs (outNe hso "d" i), stepOff h1 s hs (outNe hso "t" i)]
        exact hfr s hs hso
      refine ⟨hfr', ?_, ?_, ?_⟩
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · rw [hkeep k (by omega)]; exact hdlt k h
        · subst h; rw [hdFinal]; exact Nat.mod_lt _ (by norm_num)
      · rw [show sBor zero pfx (i + 1) = bn from rfl, hv4]; omega
      · rw [show sBor zero pfx (i + 1) = bn from rfl, accN, accN, accN,
          accN_congr i (fun k hk => by rw [hkeep k (by omega)]), hdFinal, hv4]
        have hpow : (2 : Nat) ^ (32 * (i + 1)) = 2 ^ (32 * i) * 2 ^ 32 := by
          rw [← pow_add]; ring_nf
        have hcol : (envReader e1 tn).toNat % 2 ^ 32 + P + b
            = A + 2 ^ 32 * (1 - (envReader e3 hn).toNat) := by
          have hmd : (envReader e1 tn).toNat % 2 ^ 32
              + 2 ^ 32 * ((envReader e1 tn).toNat / 2 ^ 32) = (envReader e1 tn).toNat :=
            Nat.mod_add_div _ _
          rw [hv3]
          omega
        rw [hpow]
        set M := (2 : Nat) ^ (32 * i)
        set D := accN (fun k => (envReader envI s!"{pfx}d{k}").toNat) i
        set PP := accN (fun k => (envReader env (pN.getD k zero)).toNat) i
        set AA := accN (fun k => (envReader env (aN[k]!)).toNat) i
        set r := (envReader e1 tn).toNat % 2 ^ 32
        set q := 1 - (envReader e3 hn).toNat
        have e1' : D + M * r + (PP + M * P) = (D + PP) + M * (r + P) := by ring
        rw [e1', hacc]
        have e2' : AA + M * b + M * (r + P) = AA + M * (r + P + b) := by ring
        rw [e2', hcol]
        ring

/-! ## 14. Half-limb slot names -/

/-- The `k`-th half-limb slot of field element `u`. -/
def feHN (u : String) (k : Nat) : String := u ++ "h" ++ toString k

theorem feHN_eq (u : String) (k : Nat) : s!"{u}h{k}" = feHN u k := rfl

theorem appSuffixInj {u v s t : String} (h : u ++ s = v ++ t) (hl : s.length = t.length) :
    u = v ∧ s = t := by
  have h' : u.toList ++ s.toList = v.toList ++ t.toList := by
    rw [← String.toList_append, ← String.toList_append, h]
  have hl' : s.toList.length = t.toList.length := by
    rw [← String.length_toList, ← String.length_toList] at hl; exact hl
  obtain ⟨h1, h2⟩ := List.append_inj' h' hl'
  exact ⟨String.toList_inj.mp h1, String.toList_inj.mp h2⟩

theorem digitLen {k : Nat} (hk : k < 8) : ("h" ++ toString k).length = 2 := by
  interval_cases k <;> decide

theorem feHN_assoc (u : String) (k : Nat) : feHN u k = u ++ ("h" ++ toString k) := by
  rw [feHN, String.append_assoc]

/-- The half-limb slot names of two field elements collide only at the same element
    and index. -/
theorem feHN_inj {u v : String} {k j : Nat} (hk : k < 8) (hj : j < 8)
    (h : feHN u k = feHN v j) : u = v ∧ k = j := by
  rw [feHN_assoc, feHN_assoc] at h
  obtain ⟨h1, h2⟩ := appSuffixInj h (by rw [digitLen hk, digitLen hj])
  refine ⟨h1, repr_injective (by simpa [toString] using! (String.append_right_inj "h").mp h2)⟩

/-- A two-character name is never a half-limb slot name of a nonempty field element. -/
theorem feHN_ne_short {u v : String} {k : Nat} (hk : k < 8) {c : Char} (hu : hd u = some c)
    (hv : v.length = 2) : feHN u k ≠ v := by
  intro he
  have hlen : u.length + 2 = 2 := by
    rw [← digitLen hk, ← String.length_append, ← feHN_assoc, he, hv]
    rw [digitLen hk]
  have : u.toList = [] := by
    have : u.length = 0 := by omega
    rw [← String.length_toList] at this
    exact List.eq_nil_of_length_eq_zero this
  rw [hd, this] at hu
  simp at hu

/-- A half-limb slot name ends in `h` followed by one digit, so a name whose
    two-character suffix does not start with `h` is not one. -/
theorem feHN_ne_suffix2 {u : String} {k : Nat} (hk : k < 8) {pre suf : String}
    (hs : suf.length = 2) (hsh : hd suf ≠ some 'h') : feHN u k ≠ pre ++ suf := by
  intro he
  rw [feHN_assoc] at he
  obtain ⟨-, h2⟩ := appSuffixInj he (by rw [digitLen hk, hs])
  exact hsh (h2 ▸ hdAppend (u := "h") (v := toString k) rfl)

/-- `CC0` is not a half-limb slot name. -/
theorem feHN_ne_cc0 {u : String} {k : Nat} (hk : k < 8) : feHN u k ≠ "CC0" :=
  feHN_ne_suffix2 (pre := "C") (suf := "C0") hk (by decide) (by decide)

/-- `CC1` is not a half-limb slot name. -/
theorem feHN_ne_cc1 {u : String} {k : Nat} (hk : k < 8) : feHN u k ≠ "CC1" :=
  feHN_ne_suffix2 (pre := "C") (suf := "C1") hk (by decide) (by decide)

/-- `PL{i}` is not a half-limb slot name. -/
theorem feHN_ne_pl {u : String} {k i : Nat} (hk : k < 8) (hi : i < 8) :
    feHN u k ≠ s!"PL{i}" := by
  intro he
  rw [feHN_assoc] at he
  have hpl : (s!"PL{i}" : String) = "P" ++ ("L" ++ toString i) := by
    show "P" ++ "L" ++ toString i = _
    rw [String.append_assoc]
  rw [hpl] at he
  obtain ⟨-, h2⟩ := appSuffixInj he (by rw [digitLen hk]; interval_cases i <;> decide)
  exact absurd (Option.some.inj ((hdAppend (u := "h") (v := toString k) rfl).symm.trans
    (h2 ▸ hdAppend (u := "L") (v := toString i) rfl))) (by decide)

/-! ## 15. The half-limb residue readout as an `accN` -/

theorem feVal_eq_accN (env : SEnvScalar) (fe : String) :
    feVal env fe = accN (fun k => (envReader env (feHN fe k)).toNat) 8 := by
  simp only [feVal, accN, feHN_eq, show (List.range 8) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-! ## 16. The modulus as a limb sum -/

theorem pl32_lt (k : Nat) : pl32.getD k 0 < 2 ^ 32 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : pl32[k]? with
  | none => simp
  | some v =>
      have : v ∈ pl32 := List.mem_of_getElem? h
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp this
      simpa using lt_of_le_of_lt Nat.and_le_right (by norm_num [mask32])

theorem andMask32 (n : Nat) : n &&& mask32 = n % 2 ^ 32 := by
  rw [show mask32 = 2 ^ 32 - 1 by norm_num [mask32], Nat.and_two_pow_sub_one_eq_mod]

theorem accN_pl32 : accN (fun k => pl32.getD k 0) 8 = pNat := by
  simp only [accN, pl32, show (List.range 8) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    andMask32, Nat.shiftRight_eq_div_pow]
  norm_num [pNat]

/-! ## 17. The two bricks' command lists, unrolled -/

/-- The eight result names of the `feAdd` brick. -/
def rNamesOf (pfx : String) : List String := (List.range 8).map (fun i => s!"{pfx}R{i}")

/-- The eight masked-modulus names of the `feSub` brick. -/
def pmNamesOf (pfx : String) : List String := (List.range 8).map (fun i => s!"{pfx}PM{i}")

/-- The nine-limb sum names of the `feAdd` brick. -/
def s9Of (pfx : String) (A B : List String) : List String := (genAdd "ZZ" A B (pfx ++ "A")).2

/-- The trial subtraction of `p` inside the `feAdd` brick. -/
def subA (pfx : String) (A B : List String) : List LowCT × List String × String :=
  genSub "ZZ" (s9Of pfx A B) (plNames ++ ["ZZ"]) (pfx ++ "S")

/-- The three branch-free mask bindings. -/
def maskCmds (pfx bw : String) : List LowCT :=
  [ LowCT.RScalarSetExpr (pfx ++ "MMR") (.SSub (.SLit 0) (sv bw))
  , LowCT.RScalarSetExpr (pfx ++ "MM") (.SAnd (sv (pfx ++ "MMR")) (.SLit mask32))
  , LowCT.RScalarSetExpr (pfx ++ "NM") (.SXor (sv (pfx ++ "MM")) (.SLit mask32)) ]

/-- The two mask bindings of the `feSub` brick. -/
def maskCmds2 (pfx bw : String) : List LowCT :=
  [ LowCT.RScalarSetExpr (pfx ++ "MMR") (.SSub (.SLit 0) (sv bw))
  , LowCT.RScalarSetExpr (pfx ++ "MM") (.SAnd (sv (pfx ++ "MMR")) (.SLit mask32)) ]

/-- One branch-free select assignment. -/
def selOne (pfx : String) (rN s9 d9 : List String) (i : Nat) : LowCT :=
  LowCT.RScalarSetExpr (rN[i]!)
    (.SAdd (.SAnd (sv (s9[i]!)) (sv (pfx ++ "MM"))) (.SAnd (sv (d9[i]!)) (sv (pfx ++ "NM"))))

/-- The select block after `i` trips. -/
def selCmds (pfx : String) (rN s9 d9 : List String) (init : List LowCT) : Nat → List LowCT
  | 0 => init
  | i + 1 => selCmds pfx rN s9 d9 init i ++ [selOne pfx rN s9 d9 i]

theorem selCmds_run (pfx : String) (rN s9 d9 : List String) (init : List LowCT) (n : Nat) :
    (forIn [:n] init (fun i cmds =>
        ForInStep.yield (cmds ++ [selOne pfx rN s9 d9 i])) : Id (List LowCT))
      = selCmds pfx rN s9 d9 init n := by
  refine forInRangeIdx (fun i cmds => cmds = selCmds pfx rN s9 d9 init i) _ _ _ rfl ?_ ?_
  · intro i s s' hs hy
    subst hs
    injection hy with hy
    subst hy
    rfl
  · intro i s s' h
    injection h

/-- One masked-modulus assignment of the `feSub` brick. -/
def pmOne (pfx : String) (pmN : List String) (i : Nat) : LowCT :=
  LowCT.RScalarSetExpr (pmN[i]!) (.SAnd (sv (plNames[i]!)) (sv (pfx ++ "MM")))

/-- The masked-modulus block after `i` trips. -/
def pmCmds (pfx : String) (pmN : List String) (init : List LowCT) : Nat → List LowCT
  | 0 => init
  | i + 1 => pmCmds pfx pmN init i ++ [pmOne pfx pmN i]

theorem pmCmds_run (pfx : String) (pmN : List String) (init : List LowCT) (n : Nat) :
    (forIn [:n] init (fun i cmds => ForInStep.yield (cmds ++ [pmOne pfx pmN i])) : Id (List LowCT))
      = pmCmds pfx pmN init n := by
  refine forInRangeIdx (fun i cmds => cmds = pmCmds pfx pmN init i) _ _ _ rfl ?_ ?_
  · intro i s s' hs hy
    subst hs
    injection hy with hy
    subst hy
    rfl
  · intro i s s' h
    injection h

theorem feAddHalves_cmds (pfx : String) (A B : List String) :
    (feAddHalves pfx A B).1
      = selCmds pfx (rNamesOf pfx) (s9Of pfx A B) (subA pfx A B).2.1
          (((genAdd "ZZ" A B (pfx ++ "A")).1 ++ (subA pfx A B).1)
            ++ maskCmds pfx (subA pfx A B).2.2) 8 := by
  rw [show (feAddHalves pfx A B).1
      = (forIn [:8] (((genAdd "ZZ" A B (pfx ++ "A")).1 ++ (subA pfx A B).1)
            ++ maskCmds pfx (subA pfx A B).2.2)
          (fun i cmds => ForInStep.yield
            (cmds ++ [selOne pfx (rNamesOf pfx) (s9Of pfx A B) (subA pfx A B).2.1 i]))
          : Id (List LowCT)) from rfl]
  exact selCmds_run _ _ _ _ _ _

theorem feAddHalves_names (pfx : String) (A B : List String) :
    (feAddHalves pfx A B).2 = rNamesOf pfx := rfl

theorem feSubHalves_cmds (pfx : String) (A B : List String) :
    (feSubHalves pfx A B).1
      = pmCmds pfx (pmNamesOf pfx)
          ((genSub "ZZ" A B (pfx ++ "S")).1 ++ maskCmds2 pfx (genSub "ZZ" A B (pfx ++ "S")).2.2) 8
        ++ (genAdd "ZZ" (genSub "ZZ" A B (pfx ++ "S")).2.1 (pmNamesOf pfx) (pfx ++ "A")).1 :=
  congrArg
    (fun c => c ++ (genAdd "ZZ" (genSub "ZZ" A B (pfx ++ "S")).2.1 (pmNamesOf pfx) (pfx ++ "A")).1)
    (pmCmds_run pfx (pmNamesOf pfx)
      ((genSub "ZZ" A B (pfx ++ "S")).1 ++ maskCmds2 pfx (genSub "ZZ" A B (pfx ++ "S")).2.2) 8)

theorem feSubHalves_names (pfx : String) (A B : List String) :
    (feSubHalves pfx A B).2
      = (genAdd "ZZ" (genSub "ZZ" A B (pfx ++ "S")).2.1 (pmNamesOf pfx) (pfx ++ "A")).2.take 8 :=
  rfl

/-! ## 18. The two trailing blocks, split off their prefix -/

/-- The select block alone. -/
def selBody (pfx : String) (rN s9 d9 : List String) : Nat → List LowCT
  | 0 => []
  | i + 1 => selBody pfx rN s9 d9 i ++ [selOne pfx rN s9 d9 i]

theorem selCmds_split (pfx : String) (rN s9 d9 : List String) (init : List LowCT) :
    ∀ i, selCmds pfx rN s9 d9 init i = init ++ selBody pfx rN s9 d9 i := by
  intro i
  induction i with
  | zero => simp [selCmds, selBody]
  | succ i ih => rw [selCmds, ih, selBody, List.append_assoc]

/-- The masked-modulus block alone. -/
def pmBody (pfx : String) (pmN : List String) : Nat → List LowCT
  | 0 => []
  | i + 1 => pmBody pfx pmN i ++ [pmOne pfx pmN i]

theorem pmCmds_split (pfx : String) (pmN : List String) (init : List LowCT) :
    ∀ i, pmCmds pfx pmN init i = init ++ pmBody pfx pmN i := by
  intro i
  induction i with
  | zero => simp [pmCmds, pmBody]
  | succ i ih => rw [pmCmds, ih, pmBody, List.append_assoc]

/-! ## 19. The two trailing blocks, read back -/

theorem selBody_sem (pfx : String) (rN s9 d9 : List String) (n : Nat) (Keep : String → Prop)
    (hRnt : ∀ i, i < n → ¬ isTmpName (rN[i]!))
    (hRne : ∀ i j, i < n → j < n → i ≠ j → rN[i]! ≠ rN[j]!)
    (hRK : ∀ i, i < n → ∀ s, Keep s → s ≠ rN[i]!)
    (hK : ∀ s, Keep s → ¬ isTmpName s)
    (hs9K : ∀ i, i < n → Keep (s9[i]!)) (hd9K : ∀ i, i < n → Keep (d9[i]!))
    (hMMK : Keep (pfx ++ "MM")) (hNMK : Keep (pfx ++ "NM")) (E : SEnvScalar) :
    ∀ i, i ≤ n → ∀ E', semList (selBody pfx rN s9 d9 i) E = some E' →
      (∀ s, Keep s → envReader E' s = envReader E s)
      ∧ ∀ k, k < i → (envReader E' (rN[k]!)).toNat
          = ((envReader E (s9[k]!) &&& envReader E (pfx ++ "MM"))
              + (envReader E (d9[k]!) &&& envReader E (pfx ++ "NM"))).toNat := by
  intro i
  induction i with
  | zero =>
      intro _ E' hsem
      simp only [selBody, semList] at hsem
      obtain rfl : E' = E := (Option.some.inj hsem).symm
      exact ⟨fun _ _ => rfl, fun k hk => absurd hk (by omega)⟩
  | succ i ih =>
      intro hin E' hsem
      rw [selBody] at hsem
      obtain ⟨E1, hpre, htail⟩ := splitApp hsem
      obtain ⟨hkeep, hval⟩ := ih (by omega) E1 hpre
      have hi : i < n := by omega
      obtain ⟨E2, h1, r1⟩ := peel htail
      have hE : E' = E2 := (Option.some.inj r1).symm
      subst hE
      have hnew : envReader E' (rN[i]!)
          = SExpr.evalBV (envReader E1)
              ((SExpr.SAnd (sv (s9[i]!)) (sv (pfx ++ "MM"))).SAdd
                (SExpr.SAnd (sv (d9[i]!)) (sv (pfx ++ "NM")))) := stepAt h1
      have hkeep' : ∀ s, Keep s → envReader E' s = envReader E s := by
        intro s hs
        rw [stepOff h1 s (hK s hs) (hRK i hi s hs)]
        exact hkeep s hs
      refine ⟨hkeep', ?_⟩
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · rw [stepOff h1 (rN[k]!) (hRnt k (by omega)) (hRne k i (by omega) hi (by omega))]
        exact hval k h
      · subst h
        rw [hnew]
        simp only [SExpr.evalBV, sv]
        rw [hkeep _ (hs9K k hi), hkeep _ hMMK, hkeep _ (hd9K k hi), hkeep _ hNMK]

theorem pmBody_sem (pfx : String) (pmN : List String) (n : Nat) (Keep : String → Prop)
    (hPnt : ∀ i, i < n → ¬ isTmpName (pmN[i]!))
    (hPne : ∀ i j, i < n → j < n → i ≠ j → pmN[i]! ≠ pmN[j]!)
    (hPK : ∀ i, i < n → ∀ s, Keep s → s ≠ pmN[i]!)
    (hK : ∀ s, Keep s → ¬ isTmpName s)
    (hplK : ∀ i, i < n → Keep (plNames[i]!)) (hMMK : Keep (pfx ++ "MM")) (E : SEnvScalar) :
    ∀ i, i ≤ n → ∀ E', semList (pmBody pfx pmN i) E = some E' →
      (∀ s, Keep s → envReader E' s = envReader E s)
      ∧ ∀ k, k < i → envReader E' (pmN[k]!)
          = envReader E (plNames[k]!) &&& envReader E (pfx ++ "MM") := by
  intro i
  induction i with
  | zero =>
      intro _ E' hsem
      simp only [pmBody, semList] at hsem
      obtain rfl : E' = E := (Option.some.inj hsem).symm
      exact ⟨fun _ _ => rfl, fun k hk => absurd hk (by omega)⟩
  | succ i ih =>
      intro hin E' hsem
      rw [pmBody] at hsem
      obtain ⟨E1, hpre, htail⟩ := splitApp hsem
      obtain ⟨hkeep, hval⟩ := ih (by omega) E1 hpre
      have hi : i < n := by omega
      obtain ⟨E2, h1, r1⟩ := peel htail
      have hE : E' = E2 := (Option.some.inj r1).symm
      subst hE
      have hnew : envReader E' (pmN[i]!)
          = SExpr.evalBV (envReader E1)
              (SExpr.SAnd (sv (plNames[i]!)) (sv (pfx ++ "MM"))) := stepAt h1
      have hkeep' : ∀ s, Keep s → envReader E' s = envReader E s := by
        intro s hs
        rw [stepOff h1 s (hK s hs) (hPK i hi s hs)]
        exact hkeep s hs
      refine ⟨hkeep', ?_⟩
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · rw [stepOff h1 (pmN[k]!) (hPnt k (by omega)) (hPne k i (by omega) hi (by omega))]
        exact hval k h
      · subst h
        rw [hnew]
        simp only [SExpr.evalBV, sv]
        rw [hkeep _ (hplK k hi), hkeep _ hMMK]

/-! ## 20. Indexing the generated name lists -/

theorem mapRange_len {α : Type} (n : Nat) (f : Nat → α) :
    ((List.range n).map f).length = n := by simp

theorem mapRange_getBang {α : Type} [Inhabited α] (n : Nat) (f : Nat → α) (k : Nat) (hk : k < n) :
    ((List.range n).map f)[k]! = f k := by
  rw [getElem!_pos _ k (by rw [mapRange_len]; exact hk)]
  simp

theorem mapRange_getD {α : Type} (n : Nat) (f : Nat → α) (k : Nat) (hk : k < n) (d : α) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [hk]

theorem feH_len (fe : String) : (feH fe).length = 8 := mapRange_len 8 _

theorem feH_getBang (fe : String) (k : Nat) (hk : k < 8) : (feH fe)[k]! = feHN fe k :=
  mapRange_getBang 8 _ k hk

theorem feH_getD (fe z : String) (k : Nat) (hk : k < 8) : (feH fe).getD k z = feHN fe k :=
  mapRange_getD 8 _ k hk z

theorem feH_getD_ge (fe z : String) (k : Nat) (hk : 8 ≤ k) : (feH fe).getD k z = z := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [feH_len]; omega)]
  rfl

theorem plNames_len : plNames.length = 8 := mapRange_len 8 _

theorem plNames_getBang (i : Nat) (hi : i < 8) : plNames[i]! = s!"PL{i}" :=
  mapRange_getBang 8 _ i hi

theorem rNamesOf_getBang (pfx : String) (k : Nat) (hk : k < 8) :
    (rNamesOf pfx)[k]! = s!"{pfx}R{k}" := mapRange_getBang 8 _ k hk

theorem pmNamesOf_getBang (pfx : String) (k : Nat) (hk : k < 8) :
    (pmNamesOf pfx)[k]! = s!"{pfx}PM{k}" := mapRange_getBang 8 _ k hk

theorem pmNamesOf_getD (pfx : String) (k : Nat) (hk : k < 8) (d : String) :
    (pmNamesOf pfx).getD k d = s!"{pfx}PM{k}" := mapRange_getD 8 _ k hk d

theorem pmNamesOf_len (pfx : String) : (pmNamesOf pfx).length = 8 := mapRange_len 8 _

theorem pN9_getD_lt (k : Nat) (hk : k < 8) : (plNames ++ ["ZZ"]).getD k "ZZ" = s!"PL{k}" := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [plNames_len]; exact hk)]
  rw [← List.getD_eq_getElem?_getD]
  exact mapRange_getD 8 _ k hk "ZZ"

theorem pN9_getD_ge (k : Nat) (hk : 8 ≤ k) : (plNames ++ ["ZZ"]).getD k "ZZ" = "ZZ" := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [plNames_len]; exact hk),
    plNames_len]
  rcases Nat.eq_or_lt_of_le hk with h | h
  · simp [← h]
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem genAdd_len (zero : String) (aN bN : List String) (pfx : String) :
    (genAdd zero aN bN pfx).2.length = max aN.length bN.length + 1 := by
  rw [genAdd_eq, genAddRun_spec]
  simp only [aState, Array.length_toList, setBang_size, aRes_size]

theorem genSub_len (zero : String) (aN pN : List String) (pfx : String) :
    (genSub zero aN pN pfx).2.1.length = aN.length := by
  rw [genSub_eq, genSubRun_spec]
  simp only [sState, Array.length_toList, sRes_size]

/-! ## 21. The branch-free mask block -/

theorem bvSubOne_toNat : ((BitVec.ofNat 64 0 - BitVec.ofNat 64 1 : BitVec 64)).toNat = 2 ^ 64 - 1 := by
  decide

theorem maskCmds_sem (pfx bw : String) (hq : HeadOk pfx) (Keep : String → Prop)
    (hK : ∀ s, Keep s → ¬ isTmpName s)
    (hKr : ∀ s, Keep s → s ≠ pfx ++ "MMR")
    (hKm : ∀ s, Keep s → s ≠ pfx ++ "MM")
    (hKn : ∀ s, Keep s → s ≠ pfx ++ "NM")
    (E E' : SEnvScalar) (h : semList (maskCmds pfx bw) E = some E') :
    (∀ s, Keep s → envReader E' s = envReader E s)
    ∧ ((envReader E bw).toNat = 1 →
        envReader E' (pfx ++ "MM") = BitVec.ofNat 64 mask32 ∧ envReader E' (pfx ++ "NM") = 0)
    ∧ ((envReader E bw).toNat = 0 →
        envReader E' (pfx ++ "MM") = 0 ∧ envReader E' (pfx ++ "NM") = BitVec.ofNat 64 mask32) := by
  have hnt : ∀ u : String, ¬ isTmpName (pfx ++ u) :=
    fun u => Secp256k1PointOpFrontCovered.HeadOk.notTmp
      (Secp256k1PointOpFrontCovered.HeadOk.append hq u)
  simp only [maskCmds] at h
  obtain ⟨E1, h1, r1⟩ := peel h
  obtain ⟨E2, h2, r2⟩ := peel r1
  obtain ⟨E3, h3, r3⟩ := peel r2
  have hE : E' = E3 := (Option.some.inj r3).symm
  subst hE
  have v1 : envReader E1 (pfx ++ "MMR") = BitVec.ofNat 64 0 - envReader E bw := by
    rw [stepAt h1]; simp only [SExpr.evalBV, sv]
  have v2 : envReader E2 (pfx ++ "MM")
      = envReader E1 (pfx ++ "MMR") &&& BitVec.ofNat 64 mask32 := by
    rw [stepAt h2]; simp only [SExpr.evalBV, sv]
  have v2' : envReader E' (pfx ++ "MM") = envReader E2 (pfx ++ "MM") :=
    stepOff h3 _ (hnt _) (pfxNe (by decide))
  have v3 : envReader E' (pfx ++ "NM")
      = envReader E2 (pfx ++ "MM") ^^^ BitVec.ofNat 64 mask32 := by
    rw [stepAt h3]; simp only [SExpr.evalBV, sv]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rw [stepOff h3 s (hK s hs) (hKn s hs), stepOff h2 s (hK s hs) (hKm s hs),
      stepOff h1 s (hK s hs) (hKr s hs)]
  · intro hb1
    have hbv : envReader E bw = BitVec.ofNat 64 1 :=
      BitVec.eq_of_toNat_eq (by rw [hb1, ofNat_toNat (by norm_num)])
    have hmm : envReader E2 (pfx ++ "MM") = BitVec.ofNat 64 mask32 := by
      refine BitVec.eq_of_toNat_eq ?_
      rw [v2, v1, hbv, bvAnd_mask, bvSubOne_toNat, ofNat_toNat (by norm_num [mask32])]
      norm_num [mask32]
    exact ⟨by rw [v2', hmm], by rw [v3, hmm]; simp⟩
  · intro hb0
    have hbv : envReader E bw = BitVec.ofNat 64 0 :=
      BitVec.eq_of_toNat_eq (by rw [hb0, ofNat_toNat (by norm_num)])
    have hmm : envReader E2 (pfx ++ "MM") = 0 := by
      refine BitVec.eq_of_toNat_eq ?_
      rw [v2, v1, hbv, bvAnd_mask]
      decide
    exact ⟨by rw [v2', hmm], by rw [v3, hmm]; simp⟩

/-! ## 22. Names outside a brick's private namespace -/

/-- A name the brick never writes: non-temporary and outside its private prefix. -/
def OutOf (pfx s : String) : Prop := ¬ isTmpName s ∧ ∀ w : String, s ≠ pfx ++ w

theorem OutOf.sub {q s : String} (h : OutOf q s) (t : String) : OutOf (q ++ t) s :=
  ⟨h.1, fun w => by rw [String.append_assoc]; exact h.2 _⟩

theorem OutOf.idx {q s : String} (h : OutOf q s) (t : String) (k : Nat) :
    s ≠ q ++ t ++ toString k := outNe h.2 t k

theorem headOk_of_hd {s : String} {c : Char} (h : hd s = some c) (hc : c ≠ '_') : HeadOk s := by
  unfold hd at h
  cases hs : s.toList with
  | nil => rw [hs] at h; simp at h
  | cons x t =>
      rw [hs] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      exact ⟨x, t, hs, by rw [h]; exact hc⟩

theorem outOf_of_hd {q s : String} {cq cs : Char} (hq : hd q = some cq) (hs : hd s = some cs)
    (hne : cs ≠ cq) (hc : cs ≠ '_') : OutOf q s :=
  ⟨(headOk_of_hd hs hc).notTmp, fun _ => neOfHd hs (hdAppend hq) hne⟩

/-- A name under a sibling sub-prefix is outside this sub-prefix's namespace. -/
theorem sibOut {q : String} (hq : HeadOk q) {t u : String} {ct cu : Char}
    (ht : hd t = some ct) (hu : hd u = some cu) (hne : ct ≠ cu) (w : String) :
    OutOf (q ++ u) (q ++ t ++ w) := by
  refine ⟨Secp256k1PointOpFrontCovered.HeadOk.notTmp
    (Secp256k1PointOpFrontCovered.HeadOk.append
      (Secp256k1PointOpFrontCovered.HeadOk.append hq t) w), ?_⟩
  intro v he
  rw [String.append_assoc, String.append_assoc] at he
  exact neOfHd (hdAppend ht) (hdAppend hu) hne ((String.append_right_inj q).mp he)

theorem nameAssoc (p t f : String) (k : Nat) :
    p ++ t ++ f ++ toString k = p ++ t ++ (f ++ toString k) := String.append_assoc

/-- Two names under different sub-prefixes of a common prefix differ. -/
theorem sib2Ne {q t u : String} {ct cu : Char} (ht : hd t = some ct) (hu : hd u = some cu)
    (hne : ct ≠ cu) (w v : String) : q ++ t ++ w ≠ q ++ u ++ v := by
  rw [String.append_assoc, String.append_assoc]
  exact pfxNe (neOfHd (hdAppend ht) (hdAppend hu) hne)

theorem subNe {q t u : String} {ct cu : Char} (ht : hd t = some ct) (hu : hd u = some cu)
    (hne : ct ≠ cu) (w : String) : q ++ t ++ w ≠ q ++ u := by
  rw [String.append_assoc]
  exact pfxNe (neOfHd (hdAppend ht) hu hne)

theorem hd_feHN {u : String} {c : Char} (h : hd u = some c) (k : Nat) : hd (feHN u k) = some c :=
  hdAppend (hdAppend h)

theorem hd_ZZ : hd "ZZ" = some 'Z' := rfl
theorem hd_PL (i : Nat) : hd s!"PL{i}" = some 'P' := hdAppend rfl
theorem hd_CC0 : hd "CC0" = some 'C' := rfl
theorem hd_CC1 : hd "CC1" = some 'C' := rfl
theorem hd_A : hd "A" = some 'A' := rfl
theorem hd_S : hd "S" = some 'S' := rfl
theorem hd_R : hd "R" = some 'R' := rfl
theorem hd_M : hd "MM" = some 'M' := rfl
theorem hd_MR : hd "MMR" = some 'M' := rfl
theorem hd_N : hd "NM" = some 'N' := rfl
theorem hd_PM : hd "PM" = some 'P' := rfl

/-! ### List read-back and the two-binding mask block -/

theorem getD_getBang {α : Type} [Inhabited α] (l : List α) (k : Nat) (hk : k < l.length) (d : α) :
    l.getD k d = l[k]! := by
  rw [List.getD_eq_getElem?_getD, getElem!_pos l k hk, List.getElem?_eq_getElem hk]
  rfl

theorem take_getBang {α : Type} [Inhabited α] (l : List α) (n k : Nat) (hk : k < n) :
    (l.take n)[k]! = l[k]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_take,
    ite_eq_left hk]

theorem maskCmds2_sem (pfx bw : String) (Keep : String → Prop)
    (hK : ∀ s, Keep s → ¬ isTmpName s)
    (hKr : ∀ s, Keep s → s ≠ pfx ++ "MMR")
    (hKm : ∀ s, Keep s → s ≠ pfx ++ "MM")
    (E E' : SEnvScalar) (h : semList (maskCmds2 pfx bw) E = some E') :
    (∀ s, Keep s → envReader E' s = envReader E s)
    ∧ ((envReader E bw).toNat = 1 → envReader E' (pfx ++ "MM") = BitVec.ofNat 64 mask32)
    ∧ ((envReader E bw).toNat = 0 → envReader E' (pfx ++ "MM") = 0) := by
  simp only [maskCmds2] at h
  obtain ⟨E1, h1, r1⟩ := peel h
  obtain ⟨E2, h2, r2⟩ := peel r1
  have hE : E' = E2 := (Option.some.inj r2).symm
  subst hE
  have v1 : envReader E1 (pfx ++ "MMR") = BitVec.ofNat 64 0 - envReader E bw := by
    rw [stepAt h1]; simp only [SExpr.evalBV, sv]
  have v2 : envReader E' (pfx ++ "MM")
      = envReader E1 (pfx ++ "MMR") &&& BitVec.ofNat 64 mask32 := by
    rw [stepAt h2]; simp only [SExpr.evalBV, sv]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rw [stepOff h2 s (hK s hs) (hKm s hs), stepOff h1 s (hK s hs) (hKr s hs)]
  · intro hb1
    have hbv : envReader E bw = BitVec.ofNat 64 1 :=
      BitVec.eq_of_toNat_eq (by rw [hb1, ofNat_toNat (by norm_num)])
    refine BitVec.eq_of_toNat_eq ?_
    rw [v2, v1, hbv, bvAnd_mask, bvSubOne_toNat, ofNat_toNat (by norm_num [mask32])]
    norm_num [mask32]
  · intro hb0
    have hbv : envReader E bw = BitVec.ofNat 64 0 :=
      BitVec.eq_of_toNat_eq (by rw [hb0, ofNat_toNat (by norm_num)])
    refine BitVec.eq_of_toNat_eq ?_
    rw [v2, v1, hbv, bvAnd_mask]
    decide

/-! ## 23. The frames of the mask and select blocks -/

/-- The names the three mask bindings leave alone. -/
def KeepMask (q s : String) : Prop :=
  ¬ isTmpName s ∧ s ≠ q ++ "MMR" ∧ s ≠ q ++ "MM" ∧ s ≠ q ++ "NM"

/-- The names the select block leaves alone. -/
def KeepSel (q s : String) : Prop := ¬ isTmpName s ∧ ∀ j, j < 8 → s ≠ s!"{q}R{j}"

/-- The names the masked-modulus block leaves alone. -/
def KeepPm (q s : String) : Prop := ¬ isTmpName s ∧ ∀ j, j < 8 → s ≠ s!"{q}PM{j}"

theorem keepMask_sub {q t : String} (hq : HeadOk q) {ct : Char} (ht : hd t = some ct)
    (h1 : ct ≠ 'M') (h2 : ct ≠ 'N') (w : String) : KeepMask q (q ++ t ++ w) :=
  ⟨Secp256k1PointOpFrontCovered.HeadOk.notTmp
    (Secp256k1PointOpFrontCovered.HeadOk.append
      (Secp256k1PointOpFrontCovered.HeadOk.append hq t) w),
   subNe ht hd_MR h1 w, subNe ht hd_M h1 w, subNe ht hd_N h2 w⟩

theorem keepMask_out {q s : String} (h : OutOf q s) : KeepMask q s :=
  ⟨h.1, h.2 _, h.2 _, h.2 _⟩

theorem keepSel_sub {q t : String} (hq : HeadOk q) {ct : Char} (ht : hd t = some ct)
    (h : ct ≠ 'R') (w : String) : KeepSel q (q ++ t ++ w) :=
  ⟨Secp256k1PointOpFrontCovered.HeadOk.notTmp
    (Secp256k1PointOpFrontCovered.HeadOk.append
      (Secp256k1PointOpFrontCovered.HeadOk.append hq t) w),
   fun j _ => sib2Ne ht hd_R h w (toString j)⟩

theorem keepSel_out {q s : String} (h : OutOf q s) : KeepSel q s :=
  ⟨h.1, fun j _ => h.idx "R" j⟩

theorem keepPm_sub {q t : String} (hq : HeadOk q) {ct : Char} (ht : hd t = some ct)
    (h : ct ≠ 'P') (w : String) : KeepPm q (q ++ t ++ w) :=
  ⟨Secp256k1PointOpFrontCovered.HeadOk.notTmp
    (Secp256k1PointOpFrontCovered.HeadOk.append
      (Secp256k1PointOpFrontCovered.HeadOk.append hq t) w),
   fun j _ => sib2Ne ht hd_PM h w (toString j)⟩

theorem keepPm_out {q s : String} (h : OutOf q s) : KeepPm q s :=
  ⟨h.1, fun j _ => h.idx "PM" j⟩

theorem keepSel_mm {q : String} (hq : HeadOk q) : KeepSel q (q ++ "MM") :=
  ⟨Secp256k1PointOpFrontCovered.HeadOk.notTmp
    (Secp256k1PointOpFrontCovered.HeadOk.append hq _),
   fun j _ => Ne.symm (subNe hd_R hd_M (by decide) (toString j))⟩

theorem keepSel_nm {q : String} (hq : HeadOk q) : KeepSel q (q ++ "NM") :=
  ⟨Secp256k1PointOpFrontCovered.HeadOk.notTmp
    (Secp256k1PointOpFrontCovered.HeadOk.append hq _),
   fun j _ => Ne.symm (subNe hd_R hd_N (by decide) (toString j))⟩

theorem keepPm_mm {q : String} (hq : HeadOk q) : KeepPm q (q ++ "MM") :=
  ⟨Secp256k1PointOpFrontCovered.HeadOk.notTmp
    (Secp256k1PointOpFrontCovered.HeadOk.append hq _),
   fun j _ => Ne.symm (subNe hd_PM hd_M (by decide) (toString j))⟩

/-! ## 24. The `feAdd` brick -/

theorem feAddHalves_sem_gen (q a b : String) {cq : Char}
    (hq : hd q = some cq) (hcq : cq ≠ '_')
    (hAout : ∀ i : Nat, OutOf q ((feH a).getD i "ZZ"))
    (hBout : ∀ i : Nat, OutOf q ((feH b).getD i "ZZ"))
    (hZout : OutOf q "ZZ")
    (hPout : ∀ i : Nat, OutOf q s!"PL{i}")
    (env env' : SEnvScalar)
    (hz : (envReader env "ZZ").toNat = 0)
    (hpl : ∀ i, i < 8 → (envReader env s!"PL{i}").toNat = pl32.getD i 0)
    (hAlt : ∀ k, k < 8 → (envReader env (feHN a k)).toNat < 2 ^ 32)
    (hBlt : ∀ k, k < 8 → (envReader env (feHN b k)).toNat < 2 ^ 32)
    (hAc : accN (fun k => (envReader env (feHN a k)).toNat) 8 < pNat)
    (hBc : accN (fun k => (envReader env (feHN b k)).toNat) 8 < pNat)
    (hsem : semList (feAddHalves q (feH a) (feH b)).1 env = some env') :
    (∀ s, OutOf q s → envReader env' s = envReader env s)
    ∧ (∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat < 2 ^ 32)
    ∧ accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8
        = fa (accN (fun k => (envReader env (feHN a k)).toNat) 8)
             (accN (fun k => (envReader env (feHN b k)).toNat) 8) := by
  have hqok : HeadOk q := headOk_of_hd hq hcq
  have hqA : HeadOk (q ++ "A") := Secp256k1PointOpFrontCovered.HeadOk.append hqok _
  have hqS : HeadOk (q ++ "S") := Secp256k1PointOpFrontCovered.HeadOk.append hqok _
  have hmax : max (feH a).length (feH b).length = 8 := by simp [feH_len]
  -- split the brick into its four blocks
  rw [feAddHalves_cmds, selCmds_split] at hsem
  obtain ⟨E3, hpre, hsel⟩ := splitApp hsem
  obtain ⟨E2, hpre2, hmask⟩ := splitApp hpre
  obtain ⟨E1, hga, hgs⟩ := splitApp hpre2
  -- block 1: the nine-limb sum
  rw [genAdd_cmds, hmax] at hga
  obtain ⟨fr1, slt1, cle1, acc1⟩ :=
    aCmds_sem "ZZ" (feH a) (feH b) (q ++ "A") hqA
      (fun i => ((hAout i).sub "A").1) (fun i => ((hBout i).sub "A").1)
      (fun i => ((hAout i).sub "A").2) (fun i => ((hBout i).sub "A").2)
      env hz
      (fun i => by
        by_cases h : i < 8
        · rw [feH_getD _ _ i h]; exact hAlt i h
        · rw [feH_getD_ge _ _ i (by omega), hz]; norm_num)
      (fun i => by
        by_cases h : i < 8
        · rw [feH_getD _ _ i h]; exact hBlt i h
        · rw [feH_getD_ge _ _ i (by omega), hz]; norm_num)
      8 E1 hga
  -- the nine sum-limb names
  have hs9len : (s9Of q (feH a) (feH b)).length = 9 := by
    rw [s9Of, genAdd_len, hmax]
  have hs9k : ∀ k, k < 8 → (s9Of q (feH a) (feH b))[k]! = s!"{q ++ "A"}s{k}" := by
    intro k hk; exact genAdd_name _ _ _ _ k (by rw [hmax]; exact hk)
  have hs98 : (s9Of q (feH a) (feH b))[8]! = aCar "ZZ" (q ++ "A") 8 := by
    have := genAdd_top "ZZ" (feH a) (feH b) (q ++ "A")
    rw [hmax] at this; exact this
  have hAsib : ∀ (f : String) (k : Nat), OutOf (q ++ "S") (q ++ "A" ++ f ++ toString k) := by
    intro f k; rw [nameAssoc]; exact sibOut hqok hd_A hd_S (by decide) _
  have hs9out : ∀ k, k < 9 → OutOf (q ++ "S") ((s9Of q (feH a) (feH b))[k]!) := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · rw [hs9k k h]; exact hAsib "s" k
    · subst h; rw [hs98]; exact hAsib "k" 7
  have hS9lt : ∀ k, k < 9 → (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat < 2 ^ 32 := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · rw [hs9k k h]; exact slt1 k h
    · subst h; rw [hs98]; exact lt_of_le_of_lt cle1 (by norm_num)
  have hZ1 : (envReader E1 "ZZ").toNat = 0 := by
    rw [fr1 "ZZ" (hZout.sub "A").1 (hZout.sub "A").2, hz]
  have hP1 : ∀ i, i < 8 → (envReader E1 s!"PL{i}").toNat = pl32.getD i 0 := by
    intro i hi
    rw [fr1 _ ((hPout i).sub "A").1 ((hPout i).sub "A").2]; exact hpl i hi
  have hpNout : ∀ i, i < 9 → OutOf (q ++ "S") ((plNames ++ ["ZZ"]).getD i "ZZ") := by
    intro i hi
    by_cases h : i < 8
    · rw [pN9_getD_lt i h]; exact (hPout i).sub "S"
    · rw [pN9_getD_ge i (by omega)]; exact hZout.sub "S"
  have hpNv : ∀ i, i < 9 → (envReader E1 ((plNames ++ ["ZZ"]).getD i "ZZ")).toNat
      = if i < 8 then pl32.getD i 0 else 0 := by
    intro i hi
    by_cases h : i < 8
    · rw [pN9_getD_lt i h, hP1 i h, ite_eq_left h]
    · rw [pN9_getD_ge i (by omega), hZ1, ite_eq_right h]
  -- block 2: the trial subtraction of `p`
  rw [subA, genSub_cmds, hs9len] at hgs
  obtain ⟨fr2, dlt2, ble2, acc2⟩ :=
    sCmds_sem "ZZ" (s9Of q (feH a) (feH b)) (plNames ++ ["ZZ"]) (q ++ "S") 9 hqS
      (fun i hi => (hs9out i hi).1) (fun i hi => (hpNout i hi).1)
      (fun i w hi => (hs9out i hi).2 w) (fun i w hi => (hpNout i hi).2 w)
      E1 hZ1 hS9lt
      (fun i hi => by rw [hpNv i hi]; split <;> [exact pl32_lt i; norm_num])
      9 (le_refl 9) E2 hgs
  -- block 3: the branch-free masks
  have hbwname : (subA q (feH a) (feH b)).2.2 = sBor "ZZ" (q ++ "S") 9 := by
    rw [subA, genSub_borrow, hs9len]
  rw [hbwname] at hmask
  obtain ⟨frM, mask1, mask0⟩ :=
    maskCmds_sem q (sBor "ZZ" (q ++ "S") 9) hqok (KeepMask q)
      (fun s hs => hs.1) (fun s hs => hs.2.1) (fun s hs => hs.2.2.1) (fun s hs => hs.2.2.2)
      E2 E3 hmask
  have hd9k : ∀ k, k < 9 → (subA q (feH a) (feH b)).2.1[k]! = s!"{q ++ "S"}d{k}" := by
    intro k hk
    rw [subA]
    exact genSub_name "ZZ" (s9Of q (feH a) (feH b)) (plNames ++ ["ZZ"]) (q ++ "S") k
      (by rw [hs9len]; exact hk)
  have hs9keepM : ∀ k, k < 9 → KeepMask q ((s9Of q (feH a) (feH b))[k]!) := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · rw [hs9k k h]
      show KeepMask q (q ++ "A" ++ "s" ++ toString k)
      rw [nameAssoc]; exact keepMask_sub hqok hd_A (by decide) (by decide) _
    · subst h
      rw [hs98]
      show KeepMask q (q ++ "A" ++ "k" ++ toString 7)
      rw [nameAssoc]; exact keepMask_sub hqok hd_A (by decide) (by decide) _
  have hs9keepS : ∀ k, k < 9 → KeepSel q ((s9Of q (feH a) (feH b))[k]!) := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · rw [hs9k k h]
      show KeepSel q (q ++ "A" ++ "s" ++ toString k)
      rw [nameAssoc]; exact keepSel_sub hqok hd_A (by decide) _
    · subst h
      rw [hs98]
      show KeepSel q (q ++ "A" ++ "k" ++ toString 7)
      rw [nameAssoc]; exact keepSel_sub hqok hd_A (by decide) _
  have hd9keepM : ∀ k, k < 9 → KeepMask q ((subA q (feH a) (feH b)).2.1[k]!) := by
    intro k hk
    rw [hd9k k hk]
    show KeepMask q (q ++ "S" ++ "d" ++ toString k)
    rw [nameAssoc]; exact keepMask_sub hqok hd_S (by decide) (by decide) _
  have hd9keepS : ∀ k, k < 9 → KeepSel q ((subA q (feH a) (feH b)).2.1[k]!) := by
    intro k hk
    rw [hd9k k hk]
    show KeepSel q (q ++ "S" ++ "d" ++ toString k)
    rw [nameAssoc]; exact keepSel_sub hqok hd_S (by decide) _
  have hs9E3 : ∀ k, k < 9 → envReader E3 ((s9Of q (feH a) (feH b))[k]!)
      = envReader E1 ((s9Of q (feH a) (feH b))[k]!) := by
    intro k hk
    rw [frM _ (hs9keepM k hk), fr2 _ (hs9out k hk).1 (hs9out k hk).2]
  have hd9E3 : ∀ k, k < 9 → envReader E3 ((subA q (feH a) (feH b)).2.1[k]!)
      = envReader E2 ((subA q (feH a) (feH b)).2.1[k]!) := fun k hk => frM _ (hd9keepM k hk)
  -- block 4: the branch-free select
  obtain ⟨frS, selv⟩ :=
    selBody_sem q (rNamesOf q) (s9Of q (feH a) (feH b)) (subA q (feH a) (feH b)).2.1 8 (KeepSel q)
      (fun i hi => by
        rw [rNamesOf_getBang q i hi]
        exact Secp256k1PointOpFrontCovered.HeadOk.notTmp
          (Secp256k1PointOpFrontCovered.HeadOk.append
            (Secp256k1PointOpFrontCovered.HeadOk.append hqok "R") _))
      (fun i j hi hj hij => by
        rw [rNamesOf_getBang q i hi, rNamesOf_getBang q j hj]; exact nmNe q (idxNe "R" hij))
      (fun i hi s hs => by rw [rNamesOf_getBang q i hi]; exact hs.2 i hi)
      (fun s hs => hs.1)
      (fun i hi => hs9keepS i (by omega)) (fun i hi => hd9keepS i (by omega))
      (keepSel_mm hqok) (keepSel_nm hqok)
      E3 8 (le_refl 8) env' hsel
  -- the two limb families and their sums
  have hS9sum : accN (fun k => (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat) 9
      = accN (fun k => (envReader env (feHN a k)).toNat) 8
        + accN (fun k => (envReader env (feHN b k)).toNat) 8 := by
    have h9 : accN (fun k => (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat) 9
        = accN (fun k => (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat) 8
          + 2 ^ (32 * 8) * (envReader E1 ((s9Of q (feH a) (feH b))[8]!)).toNat := accN_succ _ 8
    have hc : accN (fun k => (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat) 8
        = accN (fun k => (envReader E1 s!"{q ++ "A"}s{k}").toNat) 8 :=
      accN_congr 8 (fun k hk => by rw [hs9k k hk])
    have hcA : accN (fun k => (envReader env ((feH a).getD k "ZZ")).toNat) 8
        = accN (fun k => (envReader env (feHN a k)).toNat) 8 :=
      accN_congr 8 (fun k hk => by rw [feH_getD _ _ k hk])
    have hcB : accN (fun k => (envReader env ((feH b).getD k "ZZ")).toNat) 8
        = accN (fun k => (envReader env (feHN b k)).toNat) 8 :=
      accN_congr 8 (fun k hk => by rw [feH_getD _ _ k hk])
    rw [h9, hc, show (envReader E1 ((s9Of q (feH a) (feH b))[8]!)).toNat
        = (envReader E1 (aCar "ZZ" (q ++ "A") 8)).toNat by rw [hs98], acc1, hcA, hcB]
  have hPsum : accN (fun k => (envReader E1 ((plNames ++ ["ZZ"]).getD k "ZZ")).toNat) 9
      = pNat := by
    have h9 : accN (fun k => (envReader E1 ((plNames ++ ["ZZ"]).getD k "ZZ")).toNat) 9
        = accN (fun k => (envReader E1 ((plNames ++ ["ZZ"]).getD k "ZZ")).toNat) 8
          + 2 ^ (32 * 8) * (envReader E1 ((plNames ++ ["ZZ"]).getD 8 "ZZ")).toNat := accN_succ _ 8
    have hc : accN (fun k => (envReader E1 ((plNames ++ ["ZZ"]).getD k "ZZ")).toNat) 8
        = accN (fun k => pl32.getD k 0) 8 :=
      accN_congr 8 (fun k hk => by rw [hpNv k (by omega), ite_eq_left hk])
    rw [h9, hc, accN_pl32, hpNv 8 (by omega), ite_eq_right (by omega)]
    ring
  have hbal : accN (fun k => (envReader E2 s!"{q ++ "S"}d{k}").toNat) 9 + pNat
      = accN (fun k => (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat) 9
        + 2 ^ (32 * 9) * (envReader E2 (sBor "ZZ" (q ++ "S") 9)).toNat := by
    rw [← hPsum]; exact acc2
  -- the closing arithmetic
  have h9S : accN (fun k => (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat) 9
      = accN (fun k => (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat) 8
        + 2 ^ (32 * 8) * (envReader E1 ((s9Of q (feH a) (feH b))[8]!)).toNat := accN_succ _ 8
  have h9D : accN (fun k => (envReader E2 s!"{q ++ "S"}d{k}").toNat) 9
      = accN (fun k => (envReader E2 s!"{q ++ "S"}d{k}").toNat) 8
        + 2 ^ (32 * 8) * (envReader E2 s!"{q ++ "S"}d{8}").toNat := accN_succ _ 8
  have hSacc8 : accN (fun k => (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat) 8
      < 2 ^ (32 * 8) := accN_lt _ 8 (fun k hk => hS9lt k (by omega))
  have hDacc8 : accN (fun k => (envReader E2 s!"{q ++ "S"}d{k}").toNat) 8 < 2 ^ (32 * 8) :=
    accN_lt _ 8 (fun k hk => dlt2 k (by omega))
  have hD9lt : accN (fun k => (envReader E2 s!"{q ++ "S"}d{k}").toNat) 9 < 2 ^ (32 * 9) :=
    accN_lt _ 9 dlt2
  have hStop1 : (envReader E1 ((s9Of q (feH a) (feH b))[8]!)).toNat ≤ 1 := by
    rw [hs98]; exact cle1
  have hpsmall : pNat < 2 ^ (32 * 8) := by norm_num [pNat]
  have hframe : ∀ s, OutOf q s → envReader env' s = envReader env s := by
    intro s hs
    rw [frS s (keepSel_out hs), frM s (keepMask_out hs),
      fr2 s (hs.sub "S").1 (hs.sub "S").2, fr1 s (hs.sub "A").1 (hs.sub "A").2]
  have hfa : ∀ x y : Nat, fa x y = (x + y) % pNat := fun _ _ => rfl
  rcases (by omega : (envReader E2 (sBor "ZZ" (q ++ "S") 9)).toNat = 0
      ∨ (envReader E2 (sBor "ZZ" (q ++ "S") 9)).toNat = 1) with hbv | hbv
  · -- the sum was at least `p`: the trial difference is kept
    obtain ⟨hmm, hnm⟩ := mask0 hbv
    have hR : ∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat
        = (envReader E2 s!"{q ++ "S"}d{k}").toNat := by
      intro k hk
      have hs := selv k hk
      rw [rNamesOf_getBang q k hk] at hs
      rw [hs, hmm, hnm, hd9E3 k (by omega), hd9k k (by omega)]
      exact selRight (dlt2 k (by omega))
    refine ⟨hframe, fun k hk => by rw [hR k hk]; exact dlt2 k (by omega), ?_⟩
    rw [accN_congr 8 (fun k hk => hR k hk), hfa]
    rw [hbv] at hbal
    have hD8 : (envReader E2 s!"{q ++ "S"}d{8}").toNat = 0 := by omega
    have hge : pNat ≤ accN (fun k => (envReader env (feHN a k)).toNat) 8
        + accN (fun k => (envReader env (feHN b k)).toNat) 8 := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    omega
  · -- the sum was below `p`: the sum itself is kept
    obtain ⟨hmm, hnm⟩ := mask1 hbv
    have hR : ∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat
        = (envReader E1 ((s9Of q (feH a) (feH b))[k]!)).toNat := by
      intro k hk
      have hs := selv k hk
      rw [rNamesOf_getBang q k hk] at hs
      rw [hs, hmm, hnm, hs9E3 k (by omega)]
      exact selLeft (hS9lt k (by omega))
    refine ⟨hframe, fun k hk => by rw [hR k hk]; exact hS9lt k (by omega), ?_⟩
    rw [accN_congr 8 (fun k hk => hR k hk), hfa]
    rw [hbv] at hbal
    have hS8 : (envReader E1 ((s9Of q (feH a) (feH b))[8]!)).toNat = 0 := by omega
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The add brick realizes `fa` at the head-`'o'` output/operand separation, where
    the output name has head `'o'` and each operand head differs from `'o'`.
    A specialization of `feAddHalves_sem_gen`. -/
theorem feAddHalves_sem (q a b : String) {ca cb : Char}
    (hq : hd q = some 'o')
    (hda : hd a = some ca) (hca : ca ≠ 'o') (hca' : ca ≠ '_')
    (hdb : hd b = some cb) (hcb : cb ≠ 'o') (hcb' : cb ≠ '_')
    (env env' : SEnvScalar)
    (hz : (envReader env "ZZ").toNat = 0)
    (hpl : ∀ i, i < 8 → (envReader env s!"PL{i}").toNat = pl32.getD i 0)
    (hAlt : ∀ k, k < 8 → (envReader env (feHN a k)).toNat < 2 ^ 32)
    (hBlt : ∀ k, k < 8 → (envReader env (feHN b k)).toNat < 2 ^ 32)
    (hAc : accN (fun k => (envReader env (feHN a k)).toNat) 8 < pNat)
    (hBc : accN (fun k => (envReader env (feHN b k)).toNat) 8 < pNat)
    (hsem : semList (feAddHalves q (feH a) (feH b)).1 env = some env') :
    (∀ s, OutOf q s → envReader env' s = envReader env s)
    ∧ (∀ k, k < 8 → (envReader env' s!"{q}R{k}").toNat < 2 ^ 32)
    ∧ accN (fun k => (envReader env' s!"{q}R{k}").toNat) 8
        = fa (accN (fun k => (envReader env (feHN a k)).toNat) 8)
             (accN (fun k => (envReader env (feHN b k)).toNat) 8) :=
  feAddHalves_sem_gen q a b hq (by decide)
    (fun i => by
      by_cases h : i < 8
      · rw [feH_getD _ _ i h]; exact outOf_of_hd hq (hd_feHN hda i) hca hca'
      · rw [feH_getD_ge _ _ i (by omega)]; exact outOf_of_hd hq hd_ZZ (by decide) (by decide))
    (fun i => by
      by_cases h : i < 8
      · rw [feH_getD _ _ i h]; exact outOf_of_hd hq (hd_feHN hdb i) hcb hcb'
      · rw [feH_getD_ge _ _ i (by omega)]; exact outOf_of_hd hq hd_ZZ (by decide) (by decide))
    (outOf_of_hd hq hd_ZZ (by decide) (by decide))
    (fun i => outOf_of_hd hq (hd_PL i) (by decide) (by decide))
    env env' hz hpl hAlt hBlt hAc hBc hsem

/-! ## 25. The `feSub` brick -/

theorem feSubHalves_sem_gen (q a b : String) {cq : Char}
    (hq : hd q = some cq) (hcq : cq ≠ '_')
    (hZout : OutOf q "ZZ")
    (hPout : ∀ i : Nat, OutOf q s!"PL{i}")
    (hAout : ∀ k, k < 8 → OutOf q (feHN a k))
    (hBout : ∀ k, k < 8 → OutOf q (feHN b k))
    (env env' : SEnvScalar)
    (hz : (envReader env "ZZ").toNat = 0)
    (hpl : ∀ i, i < 8 → (envReader env s!"PL{i}").toNat = pl32.getD i 0)
    (hAlt : ∀ k, k < 8 → (envReader env (feHN a k)).toNat < 2 ^ 32)
    (hBlt : ∀ k, k < 8 → (envReader env (feHN b k)).toNat < 2 ^ 32)
    (hAc : accN (fun k => (envReader env (feHN a k)).toNat) 8 < pNat)
    (hBc : accN (fun k => (envReader env (feHN b k)).toNat) 8 < pNat)
    (hsem : semList (feSubHalves q (feH a) (feH b)).1 env = some env') :
    (∀ s, OutOf q s → envReader env' s = envReader env s)
    ∧ (∀ k, k < 8 → (envReader env' s!"{q ++ "A"}s{k}").toNat < 2 ^ 32)
    ∧ accN (fun k => (envReader env' s!"{q ++ "A"}s{k}").toNat) 8
        = fs (accN (fun k => (envReader env (feHN a k)).toNat) 8)
             (accN (fun k => (envReader env (feHN b k)).toNat) 8) := by
  have hqok : HeadOk q := headOk_of_hd hq hcq
  have hqA : HeadOk (q ++ "A") := Secp256k1PointOpFrontCovered.HeadOk.append hqok _
  have hqS : HeadOk (q ++ "S") := Secp256k1PointOpFrontCovered.HeadOk.append hqok _
  -- split the brick into its four blocks
  rw [feSubHalves_cmds, pmCmds_split] at hsem
  obtain ⟨E3, hpre, hga⟩ := splitApp hsem
  obtain ⟨E2, hpre2, hpm⟩ := splitApp hpre
  obtain ⟨E1, hgs, hmask⟩ := splitApp hpre2
  -- block 1: the ripple difference
  rw [genSub_cmds, feH_len] at hgs
  obtain ⟨fr1, dlt1, ble1, acc1⟩ :=
    sCmds_sem "ZZ" (feH a) (feH b) (q ++ "S") 8 hqS
      (fun i hi => by rw [feH_getBang a i hi]; exact ((hAout i hi).sub "S").1)
      (fun i hi => by rw [feH_getD b "ZZ" i hi]; exact ((hBout i hi).sub "S").1)
      (fun i w hi => by rw [feH_getBang a i hi]; exact ((hAout i hi).sub "S").2 w)
      (fun i w hi => by rw [feH_getD b "ZZ" i hi]; exact ((hBout i hi).sub "S").2 w)
      env hz
      (fun i hi => by rw [feH_getBang a i hi]; exact hAlt i hi)
      (fun i hi => by rw [feH_getD b "ZZ" i hi]; exact hBlt i hi)
      8 (le_refl 8) E1 hgs
  -- block 2: the branch-free mask
  have hbwname : (genSub "ZZ" (feH a) (feH b) (q ++ "S")).2.2 = sBor "ZZ" (q ++ "S") 8 := by
    rw [genSub_borrow, feH_len]
  rw [hbwname] at hmask
  obtain ⟨frM, mask1, mask0⟩ :=
    maskCmds2_sem q (sBor "ZZ" (q ++ "S") 8) (KeepMask q)
      (fun s hs => hs.1) (fun s hs => hs.2.1) (fun s hs => hs.2.2.1) E1 E2 hmask
  -- block 3: the masked modulus
  obtain ⟨frP, pmv⟩ :=
    pmBody_sem q (pmNamesOf q) 8 (KeepPm q)
      (fun i hi => by
        rw [pmNamesOf_getBang q i hi]
        exact Secp256k1PointOpFrontCovered.HeadOk.notTmp
          (Secp256k1PointOpFrontCovered.HeadOk.append
            (Secp256k1PointOpFrontCovered.HeadOk.append hqok "PM") _))
      (fun i j hi hj hij => by
        rw [pmNamesOf_getBang q i hi, pmNamesOf_getBang q j hj]; exact nmNe q (idxNe "PM" hij))
      (fun i hi s hs => by rw [pmNamesOf_getBang q i hi]; exact hs.2 i hi)
      (fun s hs => hs.1)
      (fun i hi => by rw [plNames_getBang i hi]; exact keepPm_out (hPout i))
      (keepPm_mm hqok) E2 8 (le_refl 8) E3 hpm
  -- block 4: the add-back
  have hd8len : (genSub "ZZ" (feH a) (feH b) (q ++ "S")).2.1.length = 8 := by
    rw [genSub_len, feH_len]
  have hpmlen : (pmNamesOf q).length = 8 := mapRange_len 8 _
  have hmaxDA : max (genSub "ZZ" (feH a) (feH b) (q ++ "S")).2.1.length (pmNamesOf q).length = 8 := by
    rw [hd8len, hpmlen]; simp
  have hd8k : ∀ k, k < 8 → (genSub "ZZ" (feH a) (feH b) (q ++ "S")).2.1[k]! = s!"{q ++ "S"}d{k}" :=
    fun k hk => genSub_name "ZZ" (feH a) (feH b) (q ++ "S") k (by rw [feH_len]; exact hk)
  have hd8gd : ∀ k, (genSub "ZZ" (feH a) (feH b) (q ++ "S")).2.1.getD k "ZZ"
      = if k < 8 then s!"{q ++ "S"}d{k}" else "ZZ" := by
    intro k
    by_cases h : k < 8
    · rw [getD_getBang _ k (by rw [hd8len]; exact h), hd8k k h, ite_eq_left h]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hd8len]; omega), ite_eq_right h]; rfl
  have hpmgd : ∀ k, (pmNamesOf q).getD k "ZZ" = if k < 8 then s!"{q}PM{k}" else "ZZ" := by
    intro k
    by_cases h : k < 8
    · rw [pmNamesOf_getD q k h, ite_eq_left h]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hpmlen]; omega), ite_eq_right h]; rfl
  -- the value the masked modulus carries
  have hdE3 : ∀ k, k < 8 → envReader E3 s!"{q ++ "S"}d{k}" = envReader E1 s!"{q ++ "S"}d{k}" := by
    intro k hk
    have h1 : KeepPm q s!"{q ++ "S"}d{k}" := by
      show KeepPm q (q ++ "S" ++ "d" ++ toString k)
      rw [nameAssoc]; exact keepPm_sub hqok hd_S (by decide) _
    have h2 : KeepMask q s!"{q ++ "S"}d{k}" := by
      show KeepMask q (q ++ "S" ++ "d" ++ toString k)
      rw [nameAssoc]; exact keepMask_sub hqok hd_S (by decide) (by decide) _
    rw [frP _ h1, frM _ h2]
  have hplE2 : ∀ i, i < 8 → (envReader E2 (plNames[i]!)).toNat = pl32.getD i 0 := by
    intro i hi
    rw [plNames_getBang i hi, frM _ (keepMask_out (hPout i)),
      fr1 _ ((hPout i).sub "S").1 ((hPout i).sub "S").2]
    exact hpl i hi
  have hpmv : ∀ i, i < 8 → (envReader E3 ((pmNamesOf q)[i]!)).toNat
      = if (envReader E1 (sBor "ZZ" (q ++ "S") 8)).toNat = 1 then pl32.getD i 0 else 0 := by
    intro i hi
    rw [pmv i hi]
    rcases (by omega : (envReader E1 (sBor "ZZ" (q ++ "S") 8)).toNat = 0
        ∨ (envReader E1 (sBor "ZZ" (q ++ "S") 8)).toNat = 1) with hbv | hbv
    · rw [mask0 hbv, ite_eq_right (by omega), bvAnd_zero]
    · rw [mask1 hbv, ite_eq_left hbv, bvAnd_mask_lt (by rw [hplE2 i hi]; exact pl32_lt i), hplE2 i hi]
  -- block 4: the add-back
  rw [genAdd_cmds, hmaxDA] at hga
  have hdOut : ∀ k, k < 8 → OutOf (q ++ "A") s!"{q ++ "S"}d{k}" := by
    intro k _
    show OutOf (q ++ "A") (q ++ "S" ++ "d" ++ toString k)
    rw [nameAssoc]; exact sibOut hqok hd_S hd_A (by decide) _
  have hpmOut : ∀ k, k < 8 → OutOf (q ++ "A") s!"{q}PM{k}" := by
    intro k _
    show OutOf (q ++ "A") (q ++ "PM" ++ toString k)
    exact sibOut hqok hd_PM hd_A (by decide) _
  obtain ⟨frA, sltA, cleA, accA⟩ :=
    aCmds_sem "ZZ" (genSub "ZZ" (feH a) (feH b) (q ++ "S")).2.1 (pmNamesOf q) (q ++ "A") hqA
      (fun i => by
        rw [hd8gd i]; split
        · exact (hdOut i (by assumption)).1
        · exact (hZout.sub "A").1)
      (fun i => by
        rw [hpmgd i]; split
        · exact (hpmOut i (by assumption)).1
        · exact (hZout.sub "A").1)
      (fun i w => by
        rw [hd8gd i]; split
        · exact (hdOut i (by assumption)).2 w
        · exact (hZout.sub "A").2 w)
      (fun i w => by
        rw [hpmgd i]; split
        · exact (hpmOut i (by assumption)).2 w
        · exact (hZout.sub "A").2 w)
      E3
      (by rw [frP _ (keepPm_out hZout), frM _ (keepMask_out hZout),
        fr1 _ (hZout.sub "S").1 (hZout.sub "S").2]; exact hz)
      (fun i => by
        rw [hd8gd i]; split
        · rename_i h; rw [hdE3 i h]; exact dlt1 i (by omega)
        · rw [frP _ (keepPm_out hZout), frM _ (keepMask_out hZout),
            fr1 _ (hZout.sub "S").1 (hZout.sub "S").2, hz]; norm_num)
      (fun i => by
        rw [hpmgd i]; split
        · rename_i h
          rw [show (s!"{q}PM{i}" : String) = (pmNamesOf q)[i]! from (pmNamesOf_getBang q i h).symm,
            hpmv i h]
          split
          · exact pl32_lt i
          · norm_num
        · rw [frP _ (keepPm_out hZout), frM _ (keepMask_out hZout),
            fr1 _ (hZout.sub "S").1 (hZout.sub "S").2, hz]; norm_num)
      8 env' hga
  -- the closing arithmetic
  have hcD : accN (fun k =>
        (envReader E3 ((genSub "ZZ" (feH a) (feH b) (q ++ "S")).2.1.getD k "ZZ")).toNat) 8
      = accN (fun k => (envReader E1 s!"{q ++ "S"}d{k}").toNat) 8 :=
    accN_congr 8 (fun k hk => by rw [hd8gd k, ite_eq_left hk, hdE3 k hk])
  have hcP : accN (fun k => (envReader E3 ((pmNamesOf q).getD k "ZZ")).toNat) 8
      = if (envReader E1 (sBor "ZZ" (q ++ "S") 8)).toNat = 1 then pNat else 0 := by
    rcases (by omega : (envReader E1 (sBor "ZZ" (q ++ "S") 8)).toNat = 0
        ∨ (envReader E1 (sBor "ZZ" (q ++ "S") 8)).toNat = 1) with hbv | hbv
    · rw [ite_eq_right (by omega),
        accN_congr (v := fun k => (envReader E3 ((pmNamesOf q).getD k "ZZ")).toNat)
          (w := fun _ => 0) 8 (fun k hk => by
            show (envReader E3 ((pmNamesOf q).getD k "ZZ")).toNat = 0
            rw [hpmgd k, ite_eq_left hk,
              show (s!"{q}PM{k}" : String) = (pmNamesOf q)[k]! from (pmNamesOf_getBang q k hk).symm,
              hpmv k hk, ite_eq_right (by omega)])]
      simp [accN]
    · rw [ite_eq_left hbv,
        accN_congr (v := fun k => (envReader E3 ((pmNamesOf q).getD k "ZZ")).toNat)
          (w := fun k => pl32.getD k 0) 8 (fun k hk => by
            show (envReader E3 ((pmNamesOf q).getD k "ZZ")).toNat = pl32.getD k 0
            rw [hpmgd k, ite_eq_left hk,
              show (s!"{q}PM{k}" : String) = (pmNamesOf q)[k]! from (pmNamesOf_getBang q k hk).symm,
              hpmv k hk, ite_eq_left hbv]),
        accN_pl32]
  have hcA : accN (fun k => (envReader env ((feH a)[k]!)).toNat) 8
      = accN (fun k => (envReader env (feHN a k)).toNat) 8 :=
    accN_congr 8 (fun k hk => by rw [feH_getBang a k hk])
  have hcB : accN (fun k => (envReader env ((feH b).getD k "ZZ")).toNat) 8
      = accN (fun k => (envReader env (feHN b k)).toNat) 8 :=
    accN_congr 8 (fun k hk => by rw [feH_getD b "ZZ" k hk])
  rw [hcD, hcP] at accA
  rw [hcA, hcB] at acc1
  have hRlt : accN (fun k => (envReader env' s!"{q ++ "A"}s{k}").toNat) 8 < 2 ^ (32 * 8) :=
    accN_lt _ 8 sltA
  have hDlt : accN (fun k => (envReader E1 s!"{q ++ "S"}d{k}").toNat) 8 < 2 ^ (32 * 8) :=
    accN_lt _ 8 (fun k hk => dlt1 k (by omega))
  have hpsmall : pNat < 2 ^ (32 * 8) := by norm_num [pNat]
  have hfs : ∀ x y : Nat, fs x y = (x + pNat - y) % pNat := fun _ _ => rfl
  have hframe : ∀ s, OutOf q s → envReader env' s = envReader env s := by
    intro s hs
    rw [frA s (hs.sub "A").1 (hs.sub "A").2, frP s (keepPm_out hs), frM s (keepMask_out hs),
      fr1 s (hs.sub "S").1 (hs.sub "S").2]
  refine ⟨hframe, sltA, ?_⟩
  rw [hfs]
  rcases (by omega : (envReader E1 (sBor "ZZ" (q ++ "S") 8)).toNat = 0
      ∨ (envReader E1 (sBor "ZZ" (q ++ "S") 8)).toNat = 1) with hbv | hbv
  · rw [hbv] at acc1 accA
    rw [ite_eq_right (by decide : ¬ ((0 : Nat) = 1))] at accA
    have hge : accN (fun k => (envReader env (feHN b k)).toNat) 8
        ≤ accN (fun k => (envReader env (feHN a k)).toNat) 8 := by omega
    rw [show accN (fun k => (envReader env (feHN a k)).toNat) 8 + pNat
          - accN (fun k => (envReader env (feHN b k)).toNat) 8
        = (accN (fun k => (envReader env (feHN a k)).toNat) 8
            - accN (fun k => (envReader env (feHN b k)).toNat) 8) + pNat from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hbv] at acc1 accA
    rw [ite_eq_left (rfl : (1 : Nat) = 1)] at accA
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The sub brick realizes `fs` at the head-`'o'` output/operand separation, where
    the output name has head `'o'` and each operand head differs from `'o'`.
    A specialization of `feSubHalves_sem_gen`. -/
theorem feSubHalves_sem (q a b : String) {ca cb : Char}
    (hq : hd q = some 'o')
    (hda : hd a = some ca) (hca : ca ≠ 'o') (hca' : ca ≠ '_')
    (hdb : hd b = some cb) (hcb : cb ≠ 'o') (hcb' : cb ≠ '_')
    (env env' : SEnvScalar)
    (hz : (envReader env "ZZ").toNat = 0)
    (hpl : ∀ i, i < 8 → (envReader env s!"PL{i}").toNat = pl32.getD i 0)
    (hAlt : ∀ k, k < 8 → (envReader env (feHN a k)).toNat < 2 ^ 32)
    (hBlt : ∀ k, k < 8 → (envReader env (feHN b k)).toNat < 2 ^ 32)
    (hAc : accN (fun k => (envReader env (feHN a k)).toNat) 8 < pNat)
    (hBc : accN (fun k => (envReader env (feHN b k)).toNat) 8 < pNat)
    (hsem : semList (feSubHalves q (feH a) (feH b)).1 env = some env') :
    (∀ s, OutOf q s → envReader env' s = envReader env s)
    ∧ (∀ k, k < 8 → (envReader env' s!"{q ++ "A"}s{k}").toNat < 2 ^ 32)
    ∧ accN (fun k => (envReader env' s!"{q ++ "A"}s{k}").toNat) 8
        = fs (accN (fun k => (envReader env (feHN a k)).toNat) 8)
             (accN (fun k => (envReader env (feHN b k)).toNat) 8) :=
  feSubHalves_sem_gen q a b hq (by decide)
    (outOf_of_hd hq hd_ZZ (by decide) (by decide))
    (fun i => outOf_of_hd hq (hd_PL i) (by decide) (by decide))
    (fun k _ => outOf_of_hd hq (hd_feHN hda k) hca hca')
    (fun k _ => outOf_of_hd hq (hd_feHN hdb k) hcb hcb')
    env env' hz hpl hAlt hBlt hAc hBc hsem

/-! ## 26. The copy into the output field element's half-limb slots -/

/-- The copies `emitFOp` appends after a brick, after `i` of them. -/
def wireBody (o : String) (rn : List String) : Nat → List LowCT
  | 0 => []
  | i + 1 => wireBody o rn i ++ [LowCT.RScalarSetExpr (feHN o i) (sv (rn[i]!))]

theorem wireBody_eq (o : String) (rn : List String) :
    (List.range 8).map (fun k => (LowCT.RScalarSetExpr s!"{o}h{k}" (sv (rn[k]!)) : LowCT))
      = wireBody o rn 8 := rfl

theorem wireBody_sem (o : String) (rn : List String) (n : Nat) (Keep : String → Prop)
    (hOnt : ∀ k, k < n → ¬ isTmpName (feHN o k))
    (hOne : ∀ k j, k < n → j < n → k ≠ j → feHN o k ≠ feHN o j)
    (hOK : ∀ k, k < n → ∀ s, Keep s → s ≠ feHN o k)
    (hK : ∀ s, Keep s → ¬ isTmpName s)
    (hrK : ∀ k, k < n → Keep (rn[k]!)) (E : SEnvScalar) :
    ∀ i, i ≤ n → ∀ E', semList (wireBody o rn i) E = some E' →
      (∀ s, Keep s → envReader E' s = envReader E s)
      ∧ ∀ k, k < i → envReader E' (feHN o k) = envReader E (rn[k]!) := by
  intro i
  induction i with
  | zero =>
      intro _ E' hsem
      simp only [wireBody, semList] at hsem
      obtain rfl : E' = E := (Option.some.inj hsem).symm
      exact ⟨fun _ _ => rfl, fun k hk => absurd hk (by omega)⟩
  | succ i ih =>
      intro hin E' hsem
      rw [wireBody] at hsem
      obtain ⟨E1, hpre, htail⟩ := splitApp hsem
      obtain ⟨hkeep, hval⟩ := ih (by omega) E1 hpre
      have hi : i < n := by omega
      obtain ⟨E2, h1, r1⟩ := peel htail
      have hE : E' = E2 := (Option.some.inj r1).symm
      subst hE
      have hkeep' : ∀ s, Keep s → envReader E' s = envReader E s := by
        intro s hs
        rw [stepOff h1 s (hK s hs) (hOK i hi s hs)]
        exact hkeep s hs
      refine ⟨hkeep', ?_⟩
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · rw [stepOff h1 (feHN o k) (hOnt k (by omega)) (hOne k i (by omega) hi (by omega))]
        exact hval k h
      · subst h
        rw [stepAt h1]
        simp only [SExpr.evalBV, sv]
        exact hkeep _ (hrK k hi)

/-! ## 27. Schedule names -/

theorem hd_of_schedName {fe : String} (h : schedNameB fe = true) :
    ∃ c, hd fe = some c ∧ c ≠ 'o' ∧ c ≠ '_' := by
  unfold schedNameB at h
  cases hs : fe.toList with
  | nil => rw [hs] at h; exact absurd h (by decide)
  | cons c t =>
      rw [hs] at h
      have hup : c.isUpper = true := h
      refine ⟨c, by rw [hd, hs]; rfl, ?_, ?_⟩
      · intro hc; rw [hc] at hup; exact absurd hup (by decide)
      · intro hc; rw [hc] at hup; exact absurd hup (by decide)

theorem hd_opPfx (i : Nat) : hd s!"op{i}" = some 'o' := hdAppend rfl

/-! ## 28. The scope the bricks are correct on -/

/-- The environment scope on which the emitted field bricks realize their base-field
    operation: the reduction constants carry the values `constInit` binds, and every
    schedule field element's eight half-limb slots hold a canonical residue in
    32-bit limbs. -/
structure BrickScope (env : SEnvScalar) : Prop where
  zero : (envReader env "ZZ").toNat = 0
  lo : (envReader env "CC0").toNat = cc0
  hi : (envReader env "CC1").toNat = cc1
  modulus : ∀ i, i < 8 → (envReader env s!"PL{i}").toNat = pl32.getD i 0
  limbs : ∀ fe, schedNameB fe = true → ∀ k, k < 8 → (envReader env (feHN fe k)).toNat < 2 ^ 32
  canonical : ∀ fe, schedNameB fe = true → feVal env fe < pNat

/-- The names the copy block leaves alone. -/
def KeepWire (o s : String) : Prop := ¬ isTmpName s ∧ ∀ j, j < 8 → s ≠ feHN o j

/-- **A brick plus its output copy realizes one schedule step.** From a brick whose
    result names carry the residue `v` in 32-bit limbs and which leaves everything
    outside its private prefix alone, the eight copies into `o`'s half-limb slots
    move the schedule-name readout by one `envUpd`. -/
theorem brickWire_step (idx : Nat) (o : String) (rn : List String) (v : Nat)
    (ho : schedNameB o = true)
    (env Eb env' : SEnvScalar) (hsc : BrickScope env)
    (hb1 : ∀ s, OutOf s!"op{idx}" s → envReader Eb s = envReader env s)
    (hb2 : ∀ k, k < 8 → (envReader Eb (rn[k]!)).toNat < 2 ^ 32)
    (hb3 : accN (fun k => (envReader Eb (rn[k]!)).toNat) 8 = v)
    (hrK : ∀ k, k < 8 → KeepWire o (rn[k]!))
    (hv : v < pNat)
    (hwire : semList (wireBody o rn 8) Eb = some env') :
    BrickScope env' ∧ ∀ fe, schedNameB fe = true → feVal env' fe = envUpd (feVal env) o v fe := by
  obtain ⟨co, hdo, hco, hco'⟩ := hd_of_schedName ho
  have hOnt : ∀ k, k < 8 → ¬ isTmpName (feHN o k) :=
    fun k _ => (headOk_of_hd (hd_feHN hdo k) hco').notTmp
  obtain ⟨frW, wv⟩ :=
    wireBody_sem o rn 8 (KeepWire o) hOnt
      (fun k j hk hj hkj hne => hkj (feHN_inj hk hj hne).2)
      (fun k hk s hs => hs.2 k hk) (fun s hs => hs.1) hrK Eb 8 (le_refl 8) env' hwire
  -- every schedule slot other than the output's is untouched
  have hother : ∀ fe, schedNameB fe = true → fe ≠ o → ∀ k, k < 8 →
      envReader env' (feHN fe k) = envReader env (feHN fe k) := by
    intro fe hfe hne k _
    obtain ⟨cf, hdf, hcf, hcf'⟩ := hd_of_schedName hfe
    have hkw : KeepWire o (feHN fe k) :=
      ⟨(headOk_of_hd (hd_feHN hdf k) hcf').notTmp,
       fun j hj he => hne (feHN_inj (by omega) hj he).1⟩
    rw [frW _ hkw]
    exact hb1 _ (outOf_of_hd (hd_opPfx idx) (hd_feHN hdf k) hcf hcf')
  have hOut : ∀ k, k < 8 → envReader env' (feHN o k) = envReader Eb (rn[k]!) := wv
  have hvalO : feVal env' o = v := by
    rw [feVal_eq_accN, accN_congr 8 (fun k hk => by rw [hOut k hk]), hb3]
  have hvalOther : ∀ fe, schedNameB fe = true → fe ≠ o → feVal env' fe = feVal env fe := by
    intro fe hfe hne
    rw [feVal_eq_accN, feVal_eq_accN, accN_congr 8 (fun k hk => by rw [hother fe hfe hne k hk])]
  have hZK : KeepWire o "ZZ" :=
    ⟨(headOk_of_hd hd_ZZ (by decide)).notTmp,
     fun j hj => Ne.symm (feHN_ne_short hj hdo (by decide))⟩
  have hPK : ∀ i, i < 8 → KeepWire o s!"PL{i}" :=
    fun i hi => ⟨(headOk_of_hd (hd_PL i) (by decide)).notTmp,
      fun j hj => Ne.symm (feHN_ne_pl hj hi)⟩
  have hC0K : KeepWire o "CC0" :=
    ⟨(headOk_of_hd hd_CC0 (by decide)).notTmp, fun j hj => Ne.symm (feHN_ne_cc0 hj)⟩
  have hC1K : KeepWire o "CC1" :=
    ⟨(headOk_of_hd hd_CC1 (by decide)).notTmp, fun j hj => Ne.symm (feHN_ne_cc1 hj)⟩
  have hZout : OutOf s!"op{idx}" "ZZ" :=
    outOf_of_hd (hd_opPfx idx) hd_ZZ (by decide) (by decide)
  have hPout : ∀ i, OutOf s!"op{idx}" s!"PL{i}" :=
    fun i => outOf_of_hd (hd_opPfx idx) (hd_PL i) (by decide) (by decide)
  have hC0out : OutOf s!"op{idx}" "CC0" :=
    outOf_of_hd (hd_opPfx idx) hd_CC0 (by decide) (by decide)
  have hC1out : OutOf s!"op{idx}" "CC1" :=
    outOf_of_hd (hd_opPfx idx) hd_CC1 (by decide) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [frW _ hZK, hb1 _ hZout]; exact hsc.zero
  · rw [frW _ hC0K, hb1 _ hC0out]; exact hsc.lo
  · rw [frW _ hC1K, hb1 _ hC1out]; exact hsc.hi
  · intro i hi; rw [frW _ (hPK i hi), hb1 _ (hPout i)]; exact hsc.modulus i hi
  · intro fe hfe k hk
    by_cases hne : fe = o
    · subst hne
      rw [hOut k hk]; exact hb2 k hk
    · rw [hother fe hfe hne k hk]; exact hsc.limbs fe hfe k hk
  · intro fe hfe
    by_cases hne : fe = o
    · subst hne; rw [hvalO]; exact hv
    · rw [hvalOther fe hfe hne]; exact hsc.canonical fe hfe
  · intro fe hfe
    by_cases hne : fe = o
    · subst hne; rw [hvalO]; simp [envUpd]
    · rw [hvalOther fe hfe hne]; simp [envUpd, hne]

/-! ## 29. The per-brick obligation on the add and subtract arms -/

theorem pNat_pos : 0 < pNat := by norm_num [pNat]

/-- **The `add` brick realizes one `fa` step.** -/
theorem brickStep_add (idx : Nat) (o a b : String) (hop : FOpSchedOkB (FOp.add o a b) = true)
    (env env' : SEnvScalar) (hsc : BrickScope env)
    (hsem : semScalar (seqAll (emitFOp idx (FOp.add o a b))) env = some env') :
    BrickScope env'
      ∧ ∀ fe, schedNameB fe = true →
          feVal env' fe = stepFOpG fm fa fs (feVal env) (FOp.add o a b) fe := by
  simp only [FOpSchedOkB, Bool.and_eq_true] at hop
  obtain ⟨⟨hoS, haS⟩, hbS⟩ := hop
  obtain ⟨ca, hda, hca, hca'⟩ := hd_of_schedName haS
  obtain ⟨cb, hdb, hcb, hcb'⟩ := hd_of_schedName hbS
  obtain ⟨co, hdo, hco, hco'⟩ := hd_of_schedName hoS
  rw [semScalar_seqAll_eq_semList,
    show emitFOp idx (FOp.add o a b)
      = (feAddHalves s!"op{idx}" (feH a) (feH b)).1
        ++ wireBody o (feAddHalves s!"op{idx}" (feH a) (feH b)).2 8 from rfl] at hsem
  obtain ⟨Eb, hbrick, hwire⟩ := splitApp hsem
  obtain ⟨hf, hlt, hacc⟩ :=
    feAddHalves_sem s!"op{idx}" a b (hd_opPfx idx) hda hca hca' hdb hcb hcb' env Eb
      hsc.zero hsc.modulus (hsc.limbs a haS) (hsc.limbs b hbS)
      (by rw [← feVal_eq_accN]; exact hsc.canonical a haS)
      (by rw [← feVal_eq_accN]; exact hsc.canonical b hbS) hbrick
  have hrn : ∀ k, k < 8 →
      (feAddHalves s!"op{idx}" (feH a) (feH b)).2[k]! = s!"{s!"op{idx}"}R{k}" := by
    intro k hk; rw [feAddHalves_names]; exact rNamesOf_getBang _ k hk
  have hcr : accN (fun k =>
        (envReader Eb ((feAddHalves s!"op{idx}" (feH a) (feH b)).2[k]!)).toNat) 8
      = accN (fun k => (envReader Eb s!"{s!"op{idx}"}R{k}").toNat) 8 :=
    accN_congr 8 (fun k hk => by
      show (envReader Eb ((feAddHalves s!"op{idx}" (feH a) (feH b)).2[k]!)).toNat = _
      rw [hrn k hk])
  refine brickWire_step idx o (feAddHalves s!"op{idx}" (feH a) (feH b)).2
      (fa (feVal env a) (feVal env b)) hoS env Eb env' hsc hf
      (fun k hk => by rw [hrn k hk]; exact hlt k hk) ?_ ?_ ?_ hwire
  · rw [hcr, hacc, feVal_eq_accN env a, feVal_eq_accN env b]
  · intro k hk
    rw [hrn k hk]
    exact ⟨(headOk_of_hd (hdAppend (hdAppend (hd_opPfx idx))) (by decide)).notTmp,
      fun j _ => neOfHd (hdAppend (hdAppend (hd_opPfx idx))) (hd_feHN hdo j) (Ne.symm hco)⟩
  · exact Nat.mod_lt _ pNat_pos

/-- **The `sub` brick realizes one `fs` step.** -/
theorem brickStep_sub (idx : Nat) (o a b : String) (hop : FOpSchedOkB (FOp.sub o a b) = true)
    (env env' : SEnvScalar) (hsc : BrickScope env)
    (hsem : semScalar (seqAll (emitFOp idx (FOp.sub o a b))) env = some env') :
    BrickScope env'
      ∧ ∀ fe, schedNameB fe = true →
          feVal env' fe = stepFOpG fm fa fs (feVal env) (FOp.sub o a b) fe := by
  simp only [FOpSchedOkB, Bool.and_eq_true] at hop
  obtain ⟨⟨hoS, haS⟩, hbS⟩ := hop
  obtain ⟨ca, hda, hca, hca'⟩ := hd_of_schedName haS
  obtain ⟨cb, hdb, hcb, hcb'⟩ := hd_of_schedName hbS
  obtain ⟨co, hdo, hco, hco'⟩ := hd_of_schedName hoS
  rw [semScalar_seqAll_eq_semList,
    show emitFOp idx (FOp.sub o a b)
      = (feSubHalves s!"op{idx}" (feH a) (feH b)).1
        ++ wireBody o (feSubHalves s!"op{idx}" (feH a) (feH b)).2 8 from rfl] at hsem
  obtain ⟨Eb, hbrick, hwire⟩ := splitApp hsem
  obtain ⟨hf, hlt, hacc⟩ :=
    feSubHalves_sem s!"op{idx}" a b (hd_opPfx idx) hda hca hca' hdb hcb hcb' env Eb
      hsc.zero hsc.modulus (hsc.limbs a haS) (hsc.limbs b hbS)
      (by rw [← feVal_eq_accN]; exact hsc.canonical a haS)
      (by rw [← feVal_eq_accN]; exact hsc.canonical b hbS) hbrick
  have hrn : ∀ k, k < 8 →
      (feSubHalves s!"op{idx}" (feH a) (feH b)).2[k]! = s!"{s!"op{idx}" ++ "A"}s{k}" := by
    intro k hk
    rw [feSubHalves_names, take_getBang _ 8 k hk]
    refine genAdd_name "ZZ" (genSub "ZZ" (feH a) (feH b) (s!"op{idx}" ++ "S")).2.1
      (pmNamesOf s!"op{idx}") (s!"op{idx}" ++ "A") k ?_
    rw [genSub_len, feH_len, pmNamesOf_len]
    simpa using! hk
  have hcr : accN (fun k =>
        (envReader Eb ((feSubHalves s!"op{idx}" (feH a) (feH b)).2[k]!)).toNat) 8
      = accN (fun k => (envReader Eb s!"{s!"op{idx}" ++ "A"}s{k}").toNat) 8 :=
    accN_congr 8 (fun k hk => by
      show (envReader Eb ((feSubHalves s!"op{idx}" (feH a) (feH b)).2[k]!)).toNat = _
      rw [hrn k hk])
  refine brickWire_step idx o (feSubHalves s!"op{idx}" (feH a) (feH b)).2
      (fs (feVal env a) (feVal env b)) hoS env Eb env' hsc hf
      (fun k hk => by rw [hrn k hk]; exact hlt k hk) ?_ ?_ ?_ hwire
  · rw [hcr, hacc, feVal_eq_accN env a, feVal_eq_accN env b]
  · intro k hk
    rw [hrn k hk]
    exact ⟨(headOk_of_hd (hdAppend (hdAppend (hdAppend (hd_opPfx idx)))) (by decide)).notTmp,
      fun j _ => neOfHd (hdAppend (hdAppend (hdAppend (hd_opPfx idx)))) (hd_feHN hdo j)
        (Ne.symm hco)⟩
  · exact Nat.mod_lt _ pNat_pos

/-- **The per-brick field obligation on the add and subtract arms.** One emitted
    `add` or `sub` brick's waist semantics moves the half-limb residue readout by
    exactly one `stepFOpG` at `fa`/`fs`, on every schedule-name field element, and
    leaves the environment in the scope the next brick needs. -/
theorem brickStep_addSub (i : Nat) (op : FOp) (hop : FOpSchedOkB op = true)
    (hkind : (∃ o a b, op = FOp.add o a b) ∨ (∃ o a b, op = FOp.sub o a b))
    (env env' : SEnvScalar) (hsc : BrickScope env)
    (hsem : semScalar (seqAll (emitFOp i op)) env = some env') :
    BrickScope env'
      ∧ ∀ fe, schedNameB fe = true → feVal env' fe = stepFOpG fm fa fs (feVal env) op fe := by
  rcases hkind with ⟨o, a, b, rfl⟩ | ⟨o, a, b, rfl⟩
  · exact brickStep_add i o a b hop env env' hsc hsem
  · exact brickStep_sub i o a b hop env env' hsc hsem

end CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
