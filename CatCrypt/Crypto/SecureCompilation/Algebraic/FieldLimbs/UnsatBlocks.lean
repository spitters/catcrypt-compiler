/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatZ
public import CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
public meta import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
public meta import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatZ
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact

/-!
# Unsaturated Solinas carry-multiply blocks as `jasminDialect` programs

The word layer of the unsaturated Solinas template of `UnsatZ`. A limb is a 64-bit word; a
product term `x_i · (y_j · M)` is formed at 128 bits (`castW 64 128`, `regArith .mul 128`),
with `y_j · M` a 64-bit product by the constant `M`; the terms of one limb are summed at
128 bits. A carry out of a 128-bit limb is `castW 128 64 (shrImm 128 b ·)` and its low part
`castW 128 64 (· and (2^b - 1))`; a carry out of a 64-bit limb is `shrImm 64 b` and `and`
at 64 bits. The carry out of the top limb is multiplied by the multipliers of
`wrapTerms` at 64 bits and added to their limbs. This is the shape of fiat-crypto's Rust
output for `curve25519_64` `carry_mul` and `carry_square`.

The blocks are built by the continuation-passing combinators `bindK` and `MC` of
`Curve25519`. Each combinator has a specification over the integer semantics
`MultiReturnCom.denoteZ` of `ComRangeExact`, whose values compose through renamings that
preserve integer values (`PresZ`). The specifications have no bounds: they relate the
integer semantics of a block to the integer layer `UnsatZ` exactly
(`carryProdBlk_denoteZ`). The one bounds-indexed statement, `carryMulBlk_denote`, is the
instance of `denoteMR_eq_denoteZ_of_boundsOk` at a block, with `UnsatZ.carryMulZ_cong`.

Products at `reg 128` print as `u128` in Rust; the owned x86 back end has no scalar
`reg 128` lowering, so these blocks are Rust-printer output only.

## Main definitions

* `LV`: a limb variable, 128-bit or 64-bit.
* `mulCK`, `termK`, `sumK`, `prodK`: a constant multiple, a product term, the sum of the
  terms of one limb, the product limbs.
* `splitK`, `addK`, `wrapK`, `carryK`, `chainK`, `finK`: the carry combinators.
* `carryProdBlk`, `carryMulBlk`, `carrySquareBlk`: the blocks, over the operand variables
  `aVar`, `bVar` (product) and `sVar` (square).
* `WordOk`: the limb width and every multiplier fit 64-bit words.
* `looseIv`, `tightIv`: fiat-crypto's loose and tight limb bounds for Curve25519.

## Main results

* `carryProdBlk_denoteZ`, `carryMulBlk_denoteZ`, `carrySquareBlk_denoteZ`: the integer
  semantics of a block is the carry schedule applied to the product limbs; no bounds.
* `carryMulBlk_denote`, `carrySquareBlk_denote`: when `boundsOkMR` holds and the input
  readings lie in their intervals, the output readings lie in theirs and their value is
  the product of the input values in `ZMod p`.
* `curve25519Unsat_wordOk`, `curve25519Unsat_pZ_nonneg`, and `#kat` checks that
  `boundsOkMR` holds for the Curve25519 blocks from `looseIv` inputs to `tightIv` outputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatBlocks

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (hget JCtxt)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (MC bindK)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatZ

/-- The 64-bit register type. -/
abbrev r64 : JasminTy := .reg 64

/-- The 128-bit register type. -/
abbrev r128 : JasminTy := .reg 128

/-! ## 1. Expressions and their integer semantics -/

section Exprs

variable {Γ : JCtxt}

/-- The expression `regArith op w` on `a`, `b`. -/
def eAr (op : JasminBinOp) (w : ℕ) (a b : Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w) :=
  { op := .regArith op w, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The expression `regConst w n`. -/
def eK (w n : ℕ) : Expr jasminDialect Γ (.reg w) :=
  { op := .regConst w n, retTy_eq := rfl, args := .nil }

/-- The expression `castW w w'` on `a`. -/
def eCast (w w' : ℕ) (a : Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w') :=
  { op := .castW w w', retTy_eq := rfl, args := .cons a .nil }

/-- The expression `shrImm w n` on `a`. -/
def eShr (w n : ℕ) (a : Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w) :=
  { op := .shrImm w n, retTy_eq := rfl, args := .cons a .nil }

variable (Z : ZVec Γ)

theorem eAr_opZ (op : JasminBinOp) (w : ℕ) (a b : Var Γ (.reg w)) :
    opZ (eAr op w a b).op (eAr op w a b).args Z = binZ op (hget Z a) (hget Z b) := rfl

theorem eK_opZ (w n : ℕ) : opZ (eK (Γ := Γ) w n).op (eK w n).args Z = ((n % 2 ^ w : ℕ) : ℤ) :=
  rfl

theorem eCast_opZ (w w' : ℕ) (a : Var Γ (.reg w)) :
    opZ (eCast w w' a).op (eCast w w' a).args Z = hget Z a := rfl

theorem eShr_opZ (w n : ℕ) (a : Var Γ (.reg w)) :
    opZ (eShr w n a).op (eShr w n a).args Z = hget Z a / 2 ^ n := rfl

end Exprs

/-- The `and` with the mask `2^b - 1`, as a `w`-bit constant with `b ≤ w`, is `lowZ b`. -/
theorem andZ_mask_const {b w : ℕ} (hb : b ≤ w) (x : ℤ) :
    andZ x (((2 ^ b - 1) % 2 ^ w : ℕ) : ℤ) = lowZ b x := by
  have h1 : 2 ^ b - 1 < 2 ^ w :=
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos b) one_pos) (Nat.pow_le_pow_right two_pos hb)
  rw [Nat.mod_eq_of_lt h1]
  unfold andZ lowZ
  rw [Int.toNat_natCast, Nat.and_two_pow_sub_one_eq_mod]

/-- A renaming `r` carries the integer values `Z` to `Z'` when every variable keeps its
    value. -/
abbrev PresZ {Γ Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (Z : ZVec Γ) (Z' : ZVec Δ) : Prop :=
  ∀ {t : JasminTy} (v : Var Γ t), hget Z' (r v) = hget Z v

theorem PresZ.comp {Γ₁ Γ₂ Γ₃ : JCtxt} {r₁ : Ctxt.Hom Γ₁ Γ₂} {r₂ : Ctxt.Hom Γ₂ Γ₃}
    {Z₁ : ZVec Γ₁} {Z₂ : ZVec Γ₂} {Z₃ : ZVec Γ₃} (h₁ : PresZ r₁ Z₁ Z₂) (h₂ : PresZ r₂ Z₂ Z₃) :
    PresZ (fun v => r₂ (r₁ v)) Z₁ Z₃ :=
  fun v => (h₂ (r₁ v)).trans (h₁ v)

theorem PresZ.id {Γ : JCtxt} (Z : ZVec Γ) : PresZ (fun v => v) Z Z := fun _ => rfl

/-- The integer semantics of `bindK e k` is that of `k` at the bound variable, whose value
    is `opZ e`. -/
theorem bindK_Q {Γ : JCtxt} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ t → MC Δ ts)
    (Z : ZVec Γ) (Q : ZVec ts → Prop)
    (hk : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (x : Var Δ t) (Z' : ZVec Δ), PresZ r Z Z' →
      hget Z' x = opZ e.op e.args Z → Q ((k r x).denoteZ Z')) :
    Q ((bindK e k).denoteZ Z) :=
  hk _ _ _ (fun _ => rfl) rfl

/-! ## 2. Limb variables -/

/-- A limb variable: a 128-bit or a 64-bit word. -/
inductive LV (Δ : JCtxt) where
  /-- A 128-bit limb. -/
  | wide (v : Var Δ r128)
  /-- A 64-bit limb. -/
  | narrow (v : Var Δ r64)

/-- Rename a limb variable. -/
def LV.map {Δ Δ' : JCtxt} (r : Ctxt.Hom Δ Δ') : LV Δ → LV Δ'
  | .wide v => .wide (r v)
  | .narrow v => .narrow (r v)

/-- The integer value of a limb variable. -/
def LV.z {Δ : JCtxt} (Z : ZVec Δ) : LV Δ → ℤ
  | .wide v => hget Z v
  | .narrow v => hget Z v

theorem LV.z_map {Δ Δ' : JCtxt} {r : Ctxt.Hom Δ Δ'} {Z : ZVec Δ} {Z' : ZVec Δ'}
    (h : PresZ r Z Z') (l : LV Δ) : (l.map r).z Z' = l.z Z := by
  cases l <;> exact h _

/-- Write the values `g L` at the limbs `L` of `Ls`, in order. -/
def updL {n : ℕ} : List (Fin n) → (Fin n → ℤ) → (Fin n → ℤ) → Fin n → ℤ
  | [], f, _ => f
  | L :: Ls, f, g => updL Ls (Function.update f L (g L)) g

theorem updL_apply {n : ℕ} (Ls : List (Fin n)) (f g : Fin n → ℤ) (j : Fin n) :
    updL Ls f g j = if j ∈ Ls then g j else f j := by
  induction Ls generalizing f with
  | nil => simp [updL]
  | cons L Ls ih =>
    simp only [updL, ih, List.mem_cons]
    by_cases h1 : j ∈ Ls
    · simp [h1]
    · by_cases h2 : j = L
      · subst h2; simp
      · simp [h1, h2]

theorem updL_finRange {n : ℕ} (f g : Fin n → ℤ) : updL (List.finRange n) f g = g := by
  funext j; simp [updL_apply]

/-! ## 3. Product limbs -/

/-- The product `v · M` by the 64-bit constant `M`, the variable `v` itself when `M = 1`. -/
def mulCK {Γ : JCtxt} {ts : List JasminTy} (M : ℕ) (v : Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r64 → MC Δ ts) : MC Γ ts :=
  if M = 1 then k (fun u => u) v
  else
    bindK (eK 64 M) fun r c =>
    bindK (eAr .mul 64 (r v) c) fun r' m =>
    k (fun u => r' (r u)) m

theorem mulCK_Q {Γ : JCtxt} {ts : List JasminTy} (M : ℕ) (hM : M < 2 ^ 64) (v : Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r64 → MC Δ ts) (Z : ZVec Γ) (Q : ZVec ts → Prop)
    (hk : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (x : Var Δ r64) (Z' : ZVec Δ), PresZ r Z Z' →
      hget Z' x = mulC M (hget Z v) → Q ((k r x).denoteZ Z')) :
    Q ((mulCK M v k).denoteZ Z) := by
  unfold mulCK
  split_ifs with h
  · exact hk _ _ _ (PresZ.id Z) (by simp [mulC, h])
  · refine bindK_Q _ _ _ _ fun r c Z1 h1 hc => bindK_Q _ _ _ _ fun r' m Z2 h2 hm =>
      hk _ _ _ (PresZ.comp h1 h2) ?_
    rw [hm, eAr_opZ, h1, hc, eK_opZ, Nat.mod_eq_of_lt hM]
    simp [binZ, mulC, h]

/-- The product term `x_i · (y_j · M)` of `t = (i, j, M)` at 128 bits. -/
def termK {n : ℕ} {Γ : JCtxt} {ts : List JasminTy} (xa xb : Fin n → Var Γ r64)
    (t : Fin n × Fin n × ℕ) (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r128 → MC Δ ts) :
    MC Γ ts :=
  mulCK t.2.2 (xb t.2.1) fun r y =>
  bindK (eCast 64 128 (r (xa t.1))) fun r1 a' =>
  bindK (eCast 64 128 (r1 y)) fun r2 y' =>
  bindK (eAr .mul 128 (r2 a') y') fun r3 p =>
  k (fun u => r3 (r2 (r1 (r u)))) p

theorem termK_Q {n : ℕ} {Γ : JCtxt} {ts : List JasminTy} (xa xb : Fin n → Var Γ r64)
    (t : Fin n × Fin n × ℕ) (hM : t.2.2 < 2 ^ 64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r128 → MC Δ ts) (Z : ZVec Γ) (Q : ZVec ts → Prop)
    (hk : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (x : Var Δ r128) (Z' : ZVec Δ), PresZ r Z Z' →
      hget Z' x = termZ (fun i => hget Z (xa i)) (fun i => hget Z (xb i)) t →
        Q ((k r x).denoteZ Z')) :
    Q ((termK xa xb t k).denoteZ Z) := by
  unfold termK
  refine mulCK_Q _ hM _ _ _ _ fun r y Z1 h1 hy => ?_
  refine bindK_Q _ _ _ _ fun r1 a' Z2 h2 ha => ?_
  refine bindK_Q _ _ _ _ fun r2 y' Z3 h3 hy' => ?_
  refine bindK_Q _ _ _ _ fun r3 p Z4 h4 hp => ?_
  refine hk _ _ _ (PresZ.comp (PresZ.comp (PresZ.comp h1 h2) h3) h4) ?_
  simp only [hp, eAr_opZ, h3, hy', eCast_opZ, ha, h2, h1, hy]
  rfl

/-- The sum of the terms `tl` onto the accumulator `acc` at 128 bits, each new term added on
    the left; the constant `0` for no term and no accumulator. -/
def sumK {n : ℕ} {ts : List JasminTy} : {Γ : JCtxt} → (Fin n → Var Γ r64) →
    (Fin n → Var Γ r64) → List (Fin n × Fin n × ℕ) → Option (Var Γ r128) →
    (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r128 → MC Δ ts) → MC Γ ts
  | _, _, _, [], none, k => bindK (eK 128 0) fun r c => k r c
  | _, _, _, [], some a, k => k (fun u => u) a
  | _, xa, xb, t :: tl, none, k =>
    termK xa xb t fun r p =>
    sumK (fun i => r (xa i)) (fun i => r (xb i)) tl (some p) fun r' s => k (fun u => r' (r u)) s
  | _, xa, xb, t :: tl, some a, k =>
    termK xa xb t fun r p =>
    bindK (eAr .add 128 p (r a)) fun r1 s =>
    sumK (fun i => r1 (r (xa i))) (fun i => r1 (r (xb i))) tl (some s) fun r' s' =>
      k (fun u => r' (r1 (r u))) s'

theorem sumK_Q {n : ℕ} {ts : List JasminTy} (tl : List (Fin n × Fin n × ℕ))
    (hM : ∀ t ∈ tl, t.2.2 < 2 ^ 64) : ∀ {Γ : JCtxt} (xa xb : Fin n → Var Γ r64)
    (acc : Option (Var Γ r128)) (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r128 → MC Δ ts)
    (Z : ZVec Γ) (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (x : Var Δ r128) (Z' : ZVec Δ), PresZ r Z Z' →
      hget Z' x = sumZ (fun i => hget Z (xa i)) (fun i => hget Z (xb i)) tl
        (acc.map (hget Z)) → Q ((k r x).denoteZ Z')),
    Q ((sumK xa xb tl acc k).denoteZ Z) := by
  induction tl with
  | nil =>
    intro Γ xa xb acc k Z Q hk
    cases acc with
    | none =>
      refine bindK_Q _ _ _ _ fun r c Z1 h1 hc => hk _ _ _ h1 ?_
      rw [hc, eK_opZ]; simp [sumZ]
    | some a => exact hk _ _ _ (PresZ.id Z) rfl
  | cons t tl ih =>
    intro Γ xa xb acc k Z Q hk
    have hM' : ∀ s ∈ tl, s.2.2 < 2 ^ 64 := fun s hs => hM s (by simp [hs])
    cases acc with
    | none =>
      refine termK_Q _ _ _ (hM t (by simp)) _ _ _ fun r p Z1 h1 hp => ?_
      refine ih hM' _ _ _ _ _ _ fun r' s Z2 h2 hs => hk _ _ _ (PresZ.comp h1 h2) ?_
      simp only [hs, h1, Option.map_some, Option.map_none, hp, sumZ]
    | some a =>
      refine termK_Q _ _ _ (hM t (by simp)) _ _ _ fun r p Z1 h1 hp => ?_
      refine bindK_Q _ _ _ _ fun r1 s Z2 h2 hs => ?_
      refine ih hM' _ _ _ _ _ _ fun r' s' Z3 h3 hs' =>
        hk _ _ _ (PresZ.comp (PresZ.comp h1 h2) h3) ?_
      simp only [hs', h1, h2, Option.map_some, sumZ, hs, eAr_opZ, hp]
      rfl

/-- The product limbs: limb `L` of `Ls` becomes the 128-bit sum of the terms `Tb L`. -/
def prodK {n : ℕ} {ts : List JasminTy} : {Γ : JCtxt} → (Fin n → Var Γ r64) →
    (Fin n → Var Γ r64) → (Fin n → List (Fin n × Fin n × ℕ)) → List (Fin n) →
    (Fin n → LV Γ) → (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin n → LV Δ) → MC Δ ts) → MC Γ ts
  | _, _, _, _, [], st, k => k (fun u => u) st
  | _, xa, xb, Tb, L :: Ls, st, k =>
    sumK xa xb (Tb L) none fun r s =>
    prodK (fun i => r (xa i)) (fun i => r (xb i)) Tb Ls
      (Function.update (fun j => (st j).map r) L (.wide s)) fun r' st' =>
        k (fun u => r' (r u)) st'

theorem prodK_Q {n : ℕ} {ts : List JasminTy} (Tb : Fin n → List (Fin n × Fin n × ℕ))
    (hM : ∀ L, ∀ t ∈ Tb L, t.2.2 < 2 ^ 64) (Ls : List (Fin n)) : ∀ {Γ : JCtxt}
    (xa xb : Fin n → Var Γ r64) (st : Fin n → LV Γ)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin n → LV Δ) → MC Δ ts)
    (Z : ZVec Γ) (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (st' : Fin n → LV Δ) (Z' : ZVec Δ), PresZ r Z Z' →
      (fun j => (st' j).z Z') = updL Ls (fun j => (st j).z Z)
        (fun L => sumZ (fun i => hget Z (xa i)) (fun i => hget Z (xb i)) (Tb L) none) →
        Q ((k r st').denoteZ Z')),
    Q ((prodK xa xb Tb Ls st k).denoteZ Z) := by
  induction Ls with
  | nil => intro Γ xa xb st k Z Q hk; exact hk _ _ _ (PresZ.id Z) rfl
  | cons L Ls ih =>
    intro Γ xa xb st k Z Q hk
    refine sumK_Q _ (hM L) _ _ _ _ _ _ fun r s Z1 h1 hs => ?_
    refine ih _ _ _ _ _ _ fun r' st' Z2 h2 hst => hk _ _ _ (PresZ.comp h1 h2) ?_
    rw [hst]
    simp only [h1, updL]
    congr 1
    funext j
    by_cases hj : j = L
    · subst hj; simp [LV.z, hs]
    · simp [Function.update_of_ne hj, LV.z_map h1]

/-! ## 4. Carries -/

/-- Split a limb into its low `b` bits and the rest shifted down by `b`, both 64-bit:
    `castW 128 64` of `and` with the mask and of `shrImm 128 b` for a 128-bit limb, `and`
    and `shrImm 64 b` for a 64-bit limb. -/
def splitK {Γ : JCtxt} {ts : List JasminTy} (b : ℕ) (l : LV Γ)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r64 → Var Δ r64 → MC Δ ts) : MC Γ ts :=
  match l with
  | .wide v =>
    bindK (eShr 128 b v) fun r1 s =>
    bindK (eCast 128 64 s) fun r2 hi =>
    bindK (eK 128 (2 ^ b - 1)) fun r3 m =>
    bindK (eAr .and 128 (r3 (r2 (r1 v))) m) fun r4 a =>
    bindK (eCast 128 64 a) fun r5 lo =>
    k (fun u => r5 (r4 (r3 (r2 (r1 u))))) lo (r5 (r4 (r3 hi)))
  | .narrow v =>
    bindK (eShr 64 b v) fun r1 hi =>
    bindK (eK 64 (2 ^ b - 1)) fun r2 m =>
    bindK (eAr .and 64 (r2 (r1 v)) m) fun r3 lo =>
    k (fun u => r3 (r2 (r1 u))) lo (r3 (r2 hi))

theorem splitK_Q {Γ : JCtxt} {ts : List JasminTy} (b : ℕ) (hb : b ≤ 64) (l : LV Γ)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r64 → Var Δ r64 → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (hk : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (lo hi : Var Δ r64) (Z' : ZVec Δ), PresZ r Z Z' →
      hget Z' lo = lowZ b (l.z Z) → hget Z' hi = l.z Z / 2 ^ b → Q ((k r lo hi).denoteZ Z')) :
    Q ((splitK b l k).denoteZ Z) := by
  cases l with
  | wide v =>
    simp only [splitK]
    refine bindK_Q _ _ _ _ fun r1 s Z1 h1 hs => ?_
    refine bindK_Q _ _ _ _ fun r2 hi Z2 h2 hhi => ?_
    refine bindK_Q _ _ _ _ fun r3 m Z3 h3 hm => ?_
    refine bindK_Q _ _ _ _ fun r4 a Z4 h4 ha => ?_
    refine bindK_Q _ _ _ _ fun r5 lo Z5 h5 hlo => ?_
    refine hk _ _ _ _ (PresZ.comp (PresZ.comp (PresZ.comp (PresZ.comp h1 h2) h3) h4) h5) ?_ ?_
    · rw [hlo, eCast_opZ, ha, eAr_opZ, hm, eK_opZ, h3, h2, h1]
      exact andZ_mask_const (le_trans hb (by norm_num)) _
    · rw [h5, h4, h3, hhi, eCast_opZ, hs, eShr_opZ]; rfl
  | narrow v =>
    simp only [splitK]
    refine bindK_Q _ _ _ _ fun r1 hi Z1 h1 hhi => ?_
    refine bindK_Q _ _ _ _ fun r2 m Z2 h2 hm => ?_
    refine bindK_Q _ _ _ _ fun r3 lo Z3 h3 hlo => ?_
    refine hk _ _ _ _ (PresZ.comp (PresZ.comp h1 h2) h3) ?_ ?_
    · rw [hlo, eAr_opZ, hm, eK_opZ, h2, h1]
      exact andZ_mask_const hb _
    · rw [h3, h2, hhi, eShr_opZ]; rfl

/-- Add the 64-bit word `d` to a limb, at the width of the limb. -/
def addK {Γ : JCtxt} {ts : List JasminTy} (l : LV Γ) (d : Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → LV Δ → MC Δ ts) : MC Γ ts :=
  match l with
  | .wide v =>
    bindK (eCast 64 128 d) fun r1 d' =>
    bindK (eAr .add 128 (r1 v) d') fun r2 s =>
    k (fun u => r2 (r1 u)) (.wide s)
  | .narrow v => bindK (eAr .add 64 v d) fun r s => k r (.narrow s)

theorem addK_Q {Γ : JCtxt} {ts : List JasminTy} (l : LV Γ) (d : Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → LV Δ → MC Δ ts) (Z : ZVec Γ) (Q : ZVec ts → Prop)
    (hk : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (l' : LV Δ) (Z' : ZVec Δ), PresZ r Z Z' →
      l'.z Z' = l.z Z + hget Z d → Q ((k r l').denoteZ Z')) :
    Q ((addK l d k).denoteZ Z) := by
  cases l with
  | wide v =>
    simp only [addK]
    refine bindK_Q _ _ _ _ fun r1 d' Z1 h1 hd => ?_
    refine bindK_Q _ _ _ _ fun r2 s Z2 h2 hs => hk _ _ _ (PresZ.comp h1 h2) ?_
    simp only [LV.z, hs, eAr_opZ, h1, hd, eCast_opZ]; rfl
  | narrow v =>
    simp only [addK]
    refine bindK_Q _ _ _ _ fun r s Z1 h1 hs => hk _ _ _ h1 ?_
    simp only [LV.z, hs, eAr_opZ]; rfl

theorem update_eq_setAt {n : ℕ} (f : Fin n → ℤ) (i : ℕ) (h : i < n) (v : ℤ) :
    Function.update f ⟨i, h⟩ v = setAt i v f := by
  funext j
  by_cases hj : (j : ℕ) = i
  · have : j = ⟨i, h⟩ := Fin.ext hj
    subst this; simp [setAt]
  · have : j ≠ ⟨i, h⟩ := fun e => hj (by rw [e])
    simp [setAt, hj, Function.update_of_ne this]

theorem update_eq_addAt {n : ℕ} (f : Fin n → ℤ) (i : ℕ) (h : i < n) (d : ℤ) :
    Function.update f ⟨i, h⟩ (f ⟨i, h⟩ + d) = addAt i d f := by
  funext j
  by_cases hj : (j : ℕ) = i
  · have : j = ⟨i, h⟩ := Fin.ext hj
    subst this; simp [addAt]
  · have : j ≠ ⟨i, h⟩ := fun e => hj (by rw [e])
    simp [addAt, hj, Function.update_of_ne this]

theorem addAt_of_ge {n : ℕ} (f : Fin n → ℤ) (i : ℕ) (h : ¬ i < n) (d : ℤ) :
    addAt i d f = f := by
  funext j
  have : (j : ℕ) ≠ i := by have := j.isLt; omega
  simp [addAt, this]

theorem z_update' {n : ℕ} {Δ : JCtxt} (Z : ZVec Δ) (g : Fin n → LV Δ) (L : Fin n) (l : LV Δ) :
    (fun j => (Function.update g L l j).z Z) =
      Function.update (fun j => (g j).z Z) L (l.z Z) := by
  funext j
  by_cases hj : j = L
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem z_map' {n : ℕ} {Δ Δ' : JCtxt} {r : Ctxt.Hom Δ Δ'} {Z : ZVec Δ} {Z' : ZVec Δ'}
    (h : PresZ r Z Z') (st : Fin n → LV Δ) :
    (fun j => ((st j).map r).z Z') = fun j => (st j).z Z := by
  funext j; exact LV.z_map h _

section Carry

variable (P : UnsatParams)

/-- Add the multiples `M · hi` of the top carry `hi` at the limbs of the terms `tl`; a term
    whose limb is not below `n` is skipped. -/
def wrapK {ts : List JasminTy} : {Γ : JCtxt} → Var Γ r64 → List (ℕ × ℕ) →
    (Fin P.n → LV Γ) → (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin P.n → LV Δ) → MC Δ ts) → MC Γ ts
  | _, _, [], st, k => k (fun u => u) st
  | _, hi, t :: tl, st, k =>
    if h : t.1 < P.n then
      mulCK t.2 hi fun r m =>
      addK ((st ⟨t.1, h⟩).map r) m fun r' nl =>
      wrapK (r' (r hi)) tl
        (Function.update (fun j => (st j).map (fun u => r' (r u))) ⟨t.1, h⟩ nl)
        fun r'' st' => k (fun u => r'' (r' (r u))) st'
    else wrapK hi tl st k

theorem wrapK_Q {ts : List JasminTy} (tl : List (ℕ × ℕ)) (hM : ∀ t ∈ tl, t.2 < 2 ^ 64) :
    ∀ {Γ : JCtxt} (hi : Var Γ r64) (st : Fin P.n → LV Γ)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin P.n → LV Δ) → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (st' : Fin P.n → LV Δ) (Z' : ZVec Δ), PresZ r Z Z' →
      (fun j => (st' j).z Z') = P.wrapZ (hget Z hi) tl (fun j => (st j).z Z) →
        Q ((k r st').denoteZ Z')),
    Q ((wrapK P hi tl st k).denoteZ Z) := by
  induction tl with
  | nil => intro Γ hi st k Z Q hk; exact hk _ _ _ (PresZ.id Z) rfl
  | cons t tl ih =>
    intro Γ hi st k Z Q hk
    have hM' : ∀ s ∈ tl, s.2 < 2 ^ 64 := fun s hs => hM s (by simp [hs])
    unfold wrapK
    split_ifs with h
    · refine mulCK_Q _ (hM t (by simp)) _ _ _ _ fun r m Z1 h1 hm => ?_
      refine addK_Q _ _ _ _ _ fun r' nl Z2 h2 hnl => ?_
      refine ih hM' _ _ _ _ _ fun r'' st' Z3 h3 hst =>
        hk _ _ _ (PresZ.comp (PresZ.comp h1 h2) h3) ?_
      rw [hst, z_update', z_map' (PresZ.comp h1 h2), hnl, LV.z_map h1, h2, hm,
        UnsatParams.wrapZ, update_eq_addAt]
      simp only [h1]
    · refine ih hM' _ _ _ _ _ fun r st' Z' h1 hst => hk _ _ _ h1 ?_
      rw [hst, UnsatParams.wrapZ, addAt_of_ge _ _ h]

/-- The carry at limb `i`: `splitK`, then the rest added to limb `i + 1` (`addK`) or, for the
    top limb, placed by `wrapK`; nothing when `i ≥ n`. -/
def carryK {Γ : JCtxt} {ts : List JasminTy} (i : ℕ) (st : Fin P.n → LV Γ)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin P.n → LV Δ) → MC Δ ts) : MC Γ ts :=
  if h : i < P.n then
    if h2 : i + 1 < P.n then
      splitK P.b (st ⟨i, h⟩) fun r lo hi =>
      addK ((st ⟨i + 1, h2⟩).map r) hi fun r' nl =>
      k (fun u => r' (r u))
        (Function.update (Function.update (fun j => (st j).map (fun u => r' (r u))) ⟨i, h⟩
          (.narrow (r' lo))) ⟨i + 1, h2⟩ nl)
    else
      splitK P.b (st ⟨i, h⟩) fun r lo hi =>
      wrapK P hi P.wrapTerms (Function.update (fun j => (st j).map r) ⟨i, h⟩ (.narrow lo))
        fun r' st' => k (fun u => r' (r u)) st'
  else k (fun u => u) st

theorem carryK_Q {Γ : JCtxt} {ts : List JasminTy} (hb : P.b ≤ 64)
    (hW : ∀ t ∈ P.wrapTerms, t.2 < 2 ^ 64) (i : ℕ) (st : Fin P.n → LV Γ)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin P.n → LV Δ) → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (hk : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (st' : Fin P.n → LV Δ) (Z' : ZVec Δ), PresZ r Z Z' →
      (fun j => (st' j).z Z') = P.carryZ i (fun j => (st j).z Z) → Q ((k r st').denoteZ Z')) :
    Q ((carryK P i st k).denoteZ Z) := by
  have hg : ∀ h : i < P.n, getZ (fun j => (st j).z Z) i = (st ⟨i, h⟩).z Z := fun h => by
    simp [getZ, h]
  unfold carryK
  split_ifs with h h2
  · refine splitK_Q _ hb _ _ _ _ fun r lo hi Z1 h1 hlo hhi => ?_
    refine addK_Q _ _ _ _ _ fun r' nl Z2 h2' hnl => hk _ _ _ (PresZ.comp h1 h2') ?_
    rw [z_update', z_update', z_map' (PresZ.comp h1 h2')]
    simp only [UnsatParams.carryZ, h, h2, ite_true, hg h]
    have e : LV.z Z2 nl = setAt i (lowZ P.b ((st ⟨i, h⟩).z Z)) (fun j => (st j).z Z)
        ⟨i + 1, h2⟩ + (st ⟨i, h⟩).z Z / 2 ^ P.b := by
      rw [hnl, LV.z_map h1, hhi]
      simp [setAt]
    rw [e]
    simp only [LV.z, h2', hlo]
    rw [update_eq_setAt _ i h, update_eq_addAt]
  · refine splitK_Q _ hb _ _ _ _ fun r lo hi Z1 h1 hlo hhi => ?_
    refine wrapK_Q P _ hW _ _ _ _ _ fun r' st' Z2 h2' hst => hk _ _ _ (PresZ.comp h1 h2') ?_
    rw [hst, z_update', z_map' h1]
    simp only [UnsatParams.carryZ, h, h2, ite_true, ite_false, hg h, hhi]
    rw [update_eq_setAt]
    simp only [LV.z, hlo]
  · exact hk _ _ _ (PresZ.id Z) (by simp [UnsatParams.carryZ, h])

/-- The carries of the schedule `sched`, in order. -/
def chainK {ts : List JasminTy} : {Γ : JCtxt} → List ℕ → (Fin P.n → LV Γ) →
    (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin P.n → LV Δ) → MC Δ ts) → MC Γ ts
  | _, [], st, k => k (fun u => u) st
  | _, i :: is, st, k =>
    carryK P i st fun r st' => chainK is st' fun r' st'' => k (fun u => r' (r u)) st''

theorem chainK_Q {ts : List JasminTy} (hb : P.b ≤ 64) (hW : ∀ t ∈ P.wrapTerms, t.2 < 2 ^ 64)
    (sched : List ℕ) : ∀ {Γ : JCtxt} (st : Fin P.n → LV Γ)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin P.n → LV Δ) → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (st' : Fin P.n → LV Δ) (Z' : ZVec Δ), PresZ r Z Z' →
      (fun j => (st' j).z Z') = P.carryChain sched (fun j => (st j).z Z) →
        Q ((k r st').denoteZ Z')),
    Q ((chainK P sched st k).denoteZ Z) := by
  induction sched with
  | nil => intro Γ st k Z Q hk; exact hk _ _ _ (PresZ.id Z) rfl
  | cons i is ih =>
    intro Γ st k Z Q hk
    refine carryK_Q P hb hW i _ _ _ _ fun r st' Z1 h1 hst => ?_
    refine ih _ _ _ _ fun r' st'' Z2 h2 hst2 => hk _ _ _ (PresZ.comp h1 h2) ?_
    rw [hst2, hst]
    rfl

end Carry

/-- Narrow the limbs `Ls` into the output words `out`: a 64-bit limb is taken as it is, a
    128-bit limb through `castW 128 64`. -/
def finK {n : ℕ} {ts : List JasminTy} : {Γ : JCtxt} → List (Fin n) → (Fin n → LV Γ) →
    (Fin n → Var Γ r64) → (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin n → Var Δ r64) → MC Δ ts) →
    MC Γ ts
  | _, [], _, out, k => k (fun u => u) out
  | _, L :: Ls, st, out, k =>
    match st L with
    | .narrow v => finK Ls st (Function.update out L v) k
    | .wide v =>
      bindK (eCast 128 64 v) fun r x =>
      finK Ls (fun j => (st j).map r) (Function.update (fun j => r (out j)) L x) fun r' o =>
        k (fun u => r' (r u)) o

theorem finK_Q {n : ℕ} {ts : List JasminTy} (Ls : List (Fin n)) : ∀ {Γ : JCtxt}
    (st : Fin n → LV Γ) (out : Fin n → Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → (Fin n → Var Δ r64) → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (out' : Fin n → Var Δ r64) (Z' : ZVec Δ),
      PresZ r Z Z' →
      (fun j => hget Z' (out' j)) = updL Ls (fun j => hget Z (out j)) (fun j => (st j).z Z) →
        Q ((k r out').denoteZ Z')),
    Q ((finK Ls st out k).denoteZ Z) := by
  induction Ls with
  | nil => intro Γ st out k Z Q hk; exact hk _ _ _ (PresZ.id Z) rfl
  | cons L Ls ih =>
    intro Γ st out k Z Q hk
    simp only [finK]
    split
    · next v hv =>
      refine ih _ _ _ _ _ fun r out' Z' h1 ho => hk _ _ _ h1 ?_
      rw [ho, updL]
      congr 1
      funext j
      by_cases hj : j = L
      · subst hj; simp [hv, LV.z]
      · simp [Function.update_of_ne hj]
    · next v hv =>
      refine bindK_Q _ _ _ _ fun r x Z1 h1 hx => ?_
      refine ih _ _ _ _ _ fun r' out' Z2 h2 ho => hk _ _ _ (PresZ.comp h1 h2) ?_
      rw [ho, updL, z_map' h1]
      congr 1
      funext j
      by_cases hj : j = L
      · subst hj; simp [hv, LV.z, hx, eCast_opZ]
      · simp [Function.update_of_ne hj, h1]

/-- The output variables as a return vector. -/
def hvOfFn {Δ : JCtxt} : (n : ℕ) → (Fin n → Var Δ r64) →
    HVector (fun ty => Var Δ ty) (List.replicate n r64)
  | 0, _ => .nil
  | n + 1, f => .cons (f 0) (hvOfFn n fun i => f i.succ)

theorem hvGetZ_lookupZ {Δ : JCtxt} (Z : ZVec Δ) : ∀ (n : ℕ) (f : Fin n → Var Δ r64)
    (j : Fin n), hvGetZ (lookupZ (hvOfFn n f) Z) j = hget Z (f j)
  | 0, _, j => j.elim0
  | _ + 1, _, ⟨0, _⟩ => rfl
  | n + 1, f, ⟨j + 1, hj⟩ => hvGetZ_lookupZ Z n (fun i => f i.succ) ⟨j, by omega⟩

/-- The context of `m` 64-bit words. -/
abbrev RCtx (m : ℕ) : JCtxt := List.replicate m r64

/-- The input variable at position `i` of a context of `m` 64-bit words. -/
def rv : (m i : ℕ) → i < m → Var (RCtx m) r64
  | _ + 1, 0, _ => .here
  | m + 1, i + 1, h => .there (rv m i (by omega))

/-! ## 5. The blocks -/

/-- The carried product block of the placed terms `T` with the carry schedule `sched`, over
    the operand limbs `xa`, `xb`: the product limbs at 128 bits, the carries, and the limbs
    narrowed to 64 bits. -/
def carryProdBlk (P : UnsatParams) (T : List (Fin P.n × Fin P.n × ℕ × ℕ)) (sched : List ℕ)
    {Γ : JCtxt} (xa xb : Fin P.n → Var Γ r64) : MC Γ (RCtx P.n) :=
  prodK xa xb (tbl T) (List.finRange P.n) (fun j => .narrow (xa j)) fun r st =>
  chainK P sched st fun r' st' =>
  finK (List.finRange P.n) st' (fun j => r' (r (xa j))) fun _ out => .ret (hvOfFn P.n out)

/-- **The integer semantics of a carried product block.** Limb `j` of the integer
    semantics is limb `j` of the carry schedule applied to the product limbs of the operand
    values; no bounds. -/
theorem carryProdBlk_denoteZ (P : UnsatParams) (T : List (Fin P.n × Fin P.n × ℕ × ℕ))
    (sched : List ℕ) {Γ : JCtxt} (xa xb : Fin P.n → Var Γ r64) (hb : P.b ≤ 64)
    (hT : ∀ t ∈ T, t.2.2.2 < 2 ^ 64) (hW : ∀ t ∈ P.wrapTerms, t.2 < 2 ^ 64) (Z : ZVec Γ)
    (j : Fin P.n) :
    hvGetZ ((carryProdBlk P T sched xa xb).denoteZ Z) j =
      P.carryChain sched (prodZ T (fun i => hget Z (xa i)) (fun i => hget Z (xb i))) j := by
  have hM : ∀ L, ∀ t ∈ tbl T L, t.2.2 < 2 ^ 64 := by
    intro L t ht
    unfold tbl at ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    exact hT t0 (List.mem_filter.1 ht0).1
  refine prodK_Q (tbl T) hM _ _ _ _ _ _ (fun z => hvGetZ z j = _) fun r st Z1 h1 hst => ?_
  refine chainK_Q P hb hW _ _ _ _ (fun z => hvGetZ z j = _) fun r' st' Z2 h2 hst2 => ?_
  refine finK_Q _ _ _ _ _ (fun z => hvGetZ z j = _) fun r'' out Z3 h3 ho => ?_
  show hvGetZ (lookupZ (hvOfFn P.n out) Z3) j = _
  rw [hvGetZ_lookupZ, congrFun ho j, updL_apply, ite_eq_left (List.mem_finRange j),
    congrFun hst2 j, hst, updL_finRange]
  rfl

/-- The limb width and every multiplier of the product, square and top-carry terms fit
    64-bit words. -/
def WordOk (P : UnsatParams) : Prop :=
  P.b ≤ 64 ∧ (∀ t ∈ P.mulTerms, t.2.2.2 < 2 ^ 64) ∧ (∀ t ∈ P.sqTerms, t.2.2.2 < 2 ^ 64) ∧
    ∀ t ∈ P.wrapTerms, t.2 < 2 ^ 64

instance (P : UnsatParams) : Decidable (WordOk P) := by unfold WordOk; infer_instance

/-- Operand `a` at positions `0 … n-1` of the context of a product block. -/
def aVar (n : ℕ) (i : Fin n) : Var (RCtx (2 * n)) r64 :=
  rv (2 * n) i (by have := i.isLt; omega)

/-- Operand `b` at positions `n … 2n-1` of the context of a product block. -/
def bVar (n : ℕ) (i : Fin n) : Var (RCtx (2 * n)) r64 :=
  rv (2 * n) (n + i) (by have := i.isLt; omega)

/-- Operand `a` of a square block. -/
def sVar (n : ℕ) (i : Fin n) : Var (RCtx n) r64 := rv n i i.isLt

/-- The carried product block `a · b` with the carry schedule `sched`. -/
def carryMulBlk (P : UnsatParams) (sched : List ℕ) :
    MC (RCtx (2 * P.n)) (RCtx P.n) :=
  carryProdBlk P P.mulTerms sched (aVar P.n) (bVar P.n)

/-- The carried square block `a · a` with the carry schedule `sched`. -/
def carrySquareBlk (P : UnsatParams) (sched : List ℕ) :
    MC (RCtx P.n) (RCtx P.n) :=
  carryProdBlk P P.sqTerms sched (sVar P.n) (sVar P.n)

/-- The integer semantics of the carried product block is the carry schedule applied to the
    product limbs `mulZ`; no bounds. -/
theorem carryMulBlk_denoteZ (P : UnsatParams) (sched : List ℕ) (hw : WordOk P)
    (Z : ZVec (RCtx (2 * P.n))) (j : Fin P.n) :
    hvGetZ ((carryMulBlk P sched).denoteZ Z) j =
      P.carryChain sched (P.mulZ (fun i => hget Z (aVar P.n i)) (fun i => hget Z (bVar P.n i)))
        j :=
  carryProdBlk_denoteZ P _ sched _ _ hw.1 hw.2.1 hw.2.2.2 Z j

/-- The integer semantics of the carried square block is the carry schedule applied to the
    square limbs `squareZ`; no bounds. -/
theorem carrySquareBlk_denoteZ (P : UnsatParams) (sched : List ℕ) (hw : WordOk P)
    (Z : ZVec (RCtx P.n)) (j : Fin P.n) :
    hvGetZ ((carrySquareBlk P sched).denoteZ Z) j =
      P.carryChain sched (P.squareZ (fun i => hget Z (sVar P.n i))) j :=
  carryProdBlk_denoteZ P _ sched _ _ hw.1 hw.2.2.1 hw.2.2.2 Z j

theorem hget_zvals_nonneg {Γ : JCtxt} (V : Valuation Γ) (v : Var Γ r64) :
    0 ≤ hget (zvals false V) v := by
  rw [hget_zvals]
  exact Int.natCast_nonneg _

/-- **The carried product under its bounds check.** When `boundsOkMR` holds and the
    unsigned readings of the inputs lie in `ivs`, the readings of the outputs lie in `outs`
    and their value is the product of the values of the operands in `ZMod p`. -/
theorem carryMulBlk_denote (P : UnsatParams) (sched : List ℕ) (hw : WordOk P)
    (hP : P.Placed) (hp : 0 ≤ P.pZ) (ivs : HVector (fun _ => Iv) (RCtx (2 * P.n)))
    (outs : HVector (fun _ => Iv) (RCtx P.n))
    (h : boundsOkMR false ivs (carryMulBlk P sched) outs = true)
    (V : Valuation (RCtx (2 * P.n))) (hV : ValsIn false ivs V) :
    ((P.evalZ (fun j => hvGetZ (zvals false ((carryMulBlk P sched).denote V)) j) : ℤ) :
        ZMod P.p) =
      (P.evalZ (fun i => hget (zvals false V) (aVar P.n i)) : ZMod P.p) *
        (P.evalZ (fun i => hget (zvals false V) (bVar P.n i)) : ZMod P.p) ∧
      ValsIn false outs ((carryMulBlk P sched).denote V) := by
  obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false ivs _ outs h V hV
  refine ⟨?_, hout⟩
  have hc := P.carryMulZ_cong hP sched (fun i => hget (zvals false V) (aVar P.n i))
    (fun i => hget (zvals false V) (bVar P.n i)) (fun i => hget_zvals_nonneg V _)
    (fun i => hget_zvals_nonneg V _)
  have hpZ : ((P.p : ℕ) : ℤ) = P.pZ := Int.toNat_of_nonneg hp
  rw [← Int.cast_mul, ZMod.intCast_eq_intCast_iff, hpZ, e]
  simpa only [carryMulBlk_denoteZ P sched hw] using hc

/-- **The carried square under its bounds check.** When `boundsOkMR` holds and the
    unsigned readings of the input lie in `ivs`, the readings of the outputs lie in `outs`
    and their value is the square of the value of the operand in `ZMod p`. -/
theorem carrySquareBlk_denote (P : UnsatParams) (sched : List ℕ) (hw : WordOk P)
    (hP : P.Placed) (hp : 0 ≤ P.pZ) (ivs : HVector (fun _ => Iv) (RCtx P.n))
    (outs : HVector (fun _ => Iv) (RCtx P.n))
    (h : boundsOkMR false ivs (carrySquareBlk P sched) outs = true)
    (V : Valuation (RCtx P.n)) (hV : ValsIn false ivs V) :
    ((P.evalZ (fun j => hvGetZ (zvals false ((carrySquareBlk P sched).denote V)) j) : ℤ) :
        ZMod P.p) =
      (P.evalZ (fun i => hget (zvals false V) (sVar P.n i)) : ZMod P.p) *
        (P.evalZ (fun i => hget (zvals false V) (sVar P.n i)) : ZMod P.p) ∧
      ValsIn false outs ((carrySquareBlk P sched).denote V) := by
  obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false ivs _ outs h V hV
  refine ⟨?_, hout⟩
  have hc := P.carrySquareZ_cong hP sched (fun i => hget (zvals false V) (sVar P.n i))
    (fun i => hget_zvals_nonneg V _)
  have hpZ : ((P.p : ℕ) : ℤ) = P.pZ := Int.toNat_of_nonneg hp
  rw [← Int.cast_mul, ZMod.intCast_eq_intCast_iff, hpZ, e]
  simpa only [carrySquareBlk_denoteZ P sched hw] using hc

/-! ## 6. Curve25519 -/

theorem curve25519Unsat_wordOk : WordOk curve25519Unsat := by decide

theorem curve25519Unsat_pZ_nonneg : 0 ≤ curve25519Unsat.pZ := by
  rw [curve25519Unsat_pZ]; norm_num

/-- fiat-crypto's loose bound of a `curve25519_64` limb, `[0, 3·2^51]` (the bounds of
    `fiat_25519_loose_field_element`, the input type of `carry_mul` and `carry_square`). -/
def looseIv : Iv := (0, 0x18000000000000)

/-- fiat-crypto's tight bound of a `curve25519_64` limb, `[0, 2^51]` (the bounds of
    `fiat_25519_tight_field_element`, the output type of `carry_mul` and `carry_square`). -/
def tightIv : Iv := (0, 0x8000000000000)

/- The carried product of Curve25519 with fiat-crypto's carry schedule passes the bounds
   check from loose inputs to tight outputs. -/
#kat boundsOkMR false (hvConst looseIv _) (carryMulBlk curve25519Unsat curve25519Chain)
  (hvConst tightIv _)

/- The carried square of Curve25519 passes the same check. -/
#kat boundsOkMR false (hvConst looseIv _) (carrySquareBlk curve25519Unsat curve25519Chain)
  (hvConst tightIv _)

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatBlocks
