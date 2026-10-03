/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# `fieldDialect → jasminDialect` over `n` 64-bit limbs in Montgomery form

For a modulus record `P : FieldLimbs.Mont.LimbParams n`, the multi-value block lowering
from `fieldDialect` to `jasminDialect` that represents every field type by `n` 64-bit
registers. A value of `fp P.p` is carried by the limbs of its Montgomery form
(`FieldLimbs.Mont.enc`); values of other types are carried by `n` zero limbs. The blocks
are the generic-`n` blocks of `FieldLimbs.Mont`, so the lowering and its denotation
theorem hold for every limb count, among them `n = 4` (P-256) and `n = 6` (P-384).

| source op at `P.p` | target block |
|---|---|
| `fAdd` | `Mont.addBlk xs ys` |
| `fSub` | `Mont.subBlk xs ys` |
| `fNeg` | `Mont.negBlk xs` |
| `fMul` | `Mont.mulBlk xs ys` |
| `fInv` | `Mont.invBlk xs`, the Montgomery power `x^(p-2)` |
| `fieldDouble` | `Mont.addBlk xs xs` |
| `fieldSquare` | `Mont.sqrBlk xs` |
| `fConst c` | `Mont.constBlk n (c · 2^(64n)).val` |
| `fCopy` | `Mont.retN n xs`, the return of the operand limbs |

Every other operation, and every operation at another modulus, lowers to the zero
limbs; the coverage predicate `GoodV` excludes them, and admits `fInv` only at a prime
modulus.

## Main definitions

* `limbVars`, `opX`, `opY`: the limb variables of the first and second operand.
* `mapTysL`, `encL`: the type map and the encoding.
* `lowerOpL`, `loweringL`: the per-operation blocks and the `MultiBlockLoweringData`.
* `GoodV`: addition, subtraction, negation, multiplication, doubling, squaring,
  constants and copies at `P.p`, and inversion at a prime `P.p`.
* `opGoodB`, `GoodVB`: the decision of coverage without inversion.

## Main results

* `nv_opX`, `nv_opY`: the operand limb variables of a flattened valuation carry the
  Montgomery forms.
* `blockSquareV`: the block square of `loweringL` for `GoodV` expressions.
* `GoodVB_sound`: a program accepted by `GoodVB` is `GoodV`-covered.
* `fieldToJasminLimbs_denote`: for every `GoodV`-covered program `c`,
  `(loweringL P).lowerMulti c` maps the flattened encoding of a valuation to the
  encoding of `c.denote V`; `fieldToJasminLimbs_denoteB` is its form under `GoodVB`.

## The program over word arrays

For per-operation blocks `lo : LimbBlocks n`, `fieldComOf lo c` is a straight-line
`jasminDialect` program over a word array of `n` limbs for each source variable followed by
an output array: it loads the limbs of every input array (`loadLimbs`, `loadArgs`:
`regConst` indices and `stackLoad`), runs the lowering `(loweringOf lo).lowerR` on the
loaded limbs, stores the result limbs into the output array (`storeLimbs`: `regConst`
indices and `stackStore`) and returns the last stored array. `fieldCom P c` is
`fieldComOf (lowerOpL P) c`.

* `loadLimbs_denote`, `loadArgs_denote`, `storeLimbs_denote`: the loads read the limbs
  `arrLimbs` of the arrays, and the stores write them (`storeVal`).
* `arrLimbs_storeVal`: the limbs read back from the stored array are the stored limbs.
* `fieldComOf_denote`: for blocks with a block square at an encoding, a covered `c` and
  input arrays whose limbs (`arrFlat`) are the encodings of the values of `V`, the limbs of
  the output array of `fieldComOf lo c` are the encoding of `c.denote V`; `fieldCom_denote`
  is its instance at the Montgomery blocks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 MC nv nv_cons nv_map
  bindK bindK_denote eConst Pres Pres.id Pres.comp)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

/-! ## 1. Operand variables -/

/-- The `k` variables of the context `Rn k`, in order. -/
def limbVars : (k : Nat) → List (Var (d := jasminDialect) (Rn k) w64)
  | 0 => []
  | k + 1 => .here :: (limbVars k).map fun v => .there v

theorem limbVars_length : ∀ k, (limbVars k).length = k
  | 0 => rfl
  | k + 1 => by simp [limbVars, limbVars_length k]

theorem nv_map_there {t : JasminTy} {Δ : Ctxt jasminDialect} (a : ⟦t⟧) (A : Valuation Δ) :
    ∀ xs : List (Var Δ w64),
      nv (Δ := t :: Δ) (.cons a A) (xs.map fun v => .there v) = nv A xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, nv_cons, nv_map_there a A xs]
      rfl

theorem nv_limbVars : ∀ (k v : Nat), nv (limbsN k v) (limbVars k) = v % 2 ^ (64 * k)
  | 0, v => by simp only [limbVars, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl
  | k + 1, v => by
      show (BitVec.ofNat 64 v).toNat
          + 2 ^ 64 * nv (Δ := w64 :: Rn k) (.cons _ (limbsN k (v / 2 ^ 64)))
            ((limbVars k).map fun x => .there x) = _
      rw [nv_map_there, nv_limbVars k, BitVec.toNat_ofNat, two_pow_succ, Nat.mul_comm _ (2 ^ 64),
        Nat.mod_mul]

/-- The limbs of the first operand of a context `Rn n ++ Γ`. -/
def opX (n : Nat) (Γ : Ctxt jasminDialect) : List (Var (d := jasminDialect) (Rn n ++ Γ) w64) :=
  (limbVars n).map fun v => inlHom Γ v

/-- The limbs of the second operand of a context `Rn n ++ (Rn n ++ Γ)`. -/
def opY (n : Nat) (Γ : Ctxt jasminDialect) : List (Var (d := jasminDialect) (Rn n ++ (Rn n ++ Γ)) w64) :=
  (opX n Γ).map fun v => inrHom (Rn n) v

theorem opX_length (n : Nat) (Γ : Ctxt jasminDialect) : (opX n Γ).length = n := by
  simp [opX, limbVars_length]

theorem opY_length (n : Nat) (Γ : Ctxt jasminDialect) : (opY n Γ).length = n := by
  simp [opY, opX_length]

theorem nv_opX {n : Nat} {Γ : Ctxt jasminDialect} (v : Nat) (hv : v < 2 ^ (64 * n))
    (B : Valuation Γ) : nv (hvAppend (limbsN n v) B) (opX n Γ) = v := by
  rw [opX, nv_map (r := fun {_} w => inlHom Γ w) (W := limbsN n v)
    (fun w => lookup_inlHom B w _), nv_limbVars, Nat.mod_eq_of_lt hv]

theorem nv_opY {n : Nat} {Γ : Ctxt jasminDialect} (A : Valuation (Rn n)) (v : Nat)
    (hv : v < 2 ^ (64 * n)) (B : Valuation Γ) :
    nv (hvAppend A (hvAppend (limbsN n v) B)) (opY n Γ) = v := by
  rw [opY, nv_map (r := fun {_} w => inrHom (Rn n) w) (W := hvAppend (limbsN n v) B)
    (fun w => lookup_inrHom _ A w), nv_opX v hv]

variable {n : Nat} (P : LimbParams n)

theorem nv_encX {Γ : Ctxt jasminDialect} (x : ZMod P.p) (B : Valuation Γ) :
    nv (hvAppend (enc P x) B) (opX n Γ) = (x * R P).val :=
  nv_opX _ (val_lt_two_pow P _) B

theorem nv_encY {Γ : Ctxt jasminDialect} (A : Valuation (Rn n)) (y : ZMod P.p)
    (B : Valuation Γ) :
    nv (hvAppend A (hvAppend (enc P y) B)) (opY n Γ) = (y * R P).val :=
  nv_opY A _ (val_lt_two_pow P _) B

/-! ## 2. The lowering -/

/-- Every field type is carried by `n` 64-bit registers. -/
@[reducible] def mapTysL (n : Nat) : fieldDialect.Ty → List jasminDialect.Ty := fun _ => Rn n

/-- The encoding: `enc P` on `fp P.p`, and zero limbs on every other type. -/
def encL : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t)
  | .fp q, x => if h : q = P.p then enc P (cast (congrArg ZMod h) x) else limbsN n 0
  | .fp2 _, _ => limbsN n 0
  | .fp6 _, _ => limbsN n 0
  | .fp12 _, _ => limbsN n 0

theorem encL_fp (x : ZMod P.p) : encL P (t := .fp P.p) x = enc P x := by
  simp only [encL, dite_true]
  rfl

/-- The block of each field operation at `P.p`: addition, subtraction, negation,
    multiplication, inversion, doubling, squaring, constants and copies; the zero limbs
    otherwise. -/
def lowerOpL : (op : fieldDialect.Op) →
    MultiReturnCom jasminDialect (ctxFlat (mapTysL n) (DialectSignature.sig op))
      (mapTysL n (DialectSignature.ret op))
  | .fAdd q => if q = P.p then addBlk P (opX n _) (opY n []) else constBlk n 0
  | .fSub q => if q = P.p then subBlk P (opX n _) (opY n []) else constBlk n 0
  | .fNeg q => if q = P.p then negBlk P (opX n []) else constBlk n 0
  | .fMul q => if q = P.p then mulBlk P (opX n _) (opY n []) else constBlk n 0
  | .fInv q => if q = P.p then invBlk P (opX n []) else constBlk n 0
  | .fConst q c => if h : q = P.p then constBlk n ((cast (congrArg ZMod h) c * R P).val)
    else constBlk n 0
  | .fCopy q => if q = P.p then retN n (opX n []) else constBlk n 0
  | .fieldDouble q => if q = P.p then addBlk P (opX n []) (opX n []) else constBlk n 0
  | .fieldSquare q => if q = P.p then sqrBlk P (opX n []) else constBlk n 0
  | .ext2Mul _ | .ext2Add _ | .ext2Sub _ | .frobenius2 _ | .ext6Mul _ _ | .ext6Add _
  | .ext6Sub _ | .ext12Mul _ _ | .ext12Add _ | .ext12Sub _ => constBlk n 0

/-- The multi-value lowering `fieldDialect → jasminDialect` over `n` limbs in
    Montgomery form. -/
def loweringL : MultiBlockLoweringData fieldDialect jasminDialect where
  mapTys := mapTysL n
  lowerOp := lowerOpL P

/-- The operations covered at `P.p`: addition, subtraction, negation, multiplication,
    doubling, squaring, constants and copies, and inversion when `P.p` is prime. -/
def GoodV {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) : Prop :=
  e.op = .fAdd P.p ∨ e.op = .fMul P.p ∨ (∃ c : ZMod P.p, e.op = .fConst P.p c) ∨
    e.op = .fCopy P.p ∨ e.op = .fSub P.p ∨ e.op = .fNeg P.p ∨ e.op = .fieldDouble P.p ∨
    e.op = .fieldSquare P.p ∨ (P.p.Prime ∧ e.op = .fInv P.p)

/-! ## 3. The block square and the fundamental theorem -/

/-- **The block square of `loweringL` on `GoodV`.** -/
theorem blockSquareV :
    (loweringL P).BlockSquare (fun {t} x => encL P (t := t) x) (GoodV P) := by
  intro Γ t e hg vals
  obtain ⟨op, h, args⟩ := e
  rcases hg with hop | hop | ⟨c, hop⟩ | hop | hop | hop | hop | hop | ⟨hp, hop⟩ <;>
    subst hop
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL P (.fAdd P.p)).denote (hvAppend (encL P a) (hvAppend (encL P b) .nil))
      = encL P (t := .fp P.p) (fAddF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact addBlk_denote P _ _ _ (opX_length _ _) (opY_length _ _) a b (nv_encX P a _)
      (nv_encY P _ b _)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL P (.fMul P.p)).denote (hvAppend (encL P a) (hvAppend (encL P b) .nil))
      = encL P (t := .fp P.p) (fMulF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact mulBlk_denote P _ _ _ (opX_length _ _) (opY_length _ _) a b (nv_encX P a _)
      (nv_encY P _ b _)
  · obtain ⟨⟩ := vals
    show (lowerOpL P (.fConst P.p c)).denote .nil = encL P (t := .fp P.p) (fConstF c)
    rw [encL_fp, lowerOpL, dif_pos rfl]
    exact constBlk_denote _ _ _
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fCopy P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fCopyF a)
    rw [encL_fp, lowerOpL, if_pos rfl, retN_denote _ _ _ (opX_length _ _), nv_encX]
    rfl
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL P (.fSub P.p)).denote (hvAppend (encL P a) (hvAppend (encL P b) .nil))
      = encL P (t := .fp P.p) (fSubF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact subBlk_denote_enc P _ _ _ (opX_length _ _) (opY_length _ _) a b (nv_encX P a _)
      (nv_encY P _ b _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fNeg P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fNegF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact negBlk_denote_enc P _ _ (opX_length _ _) a (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fieldDouble P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fDoubleF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact addBlk_denote P _ _ _ (opX_length _ _) (opX_length _ _) a a (nv_encX P a _)
      (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fieldSquare P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fSquareF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact sqrBlk_denote P _ _ (opX_length _ _) a (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fInv P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fInvF a)
    rw [encL_fp, encL_fp, lowerOpL, if_pos rfl]
    exact invBlk_denote_inv P hp _ _ (opX_length _ _) a (nv_encX P a _)

/-- **Denotation preservation of `fieldDialect → jasminDialect` over `n` limbs in
    Montgomery form.** A `GoodV`-covered field program lowers to a multi-result jasmin
    program that maps the limbs of its inputs to the limbs of its result. -/
theorem fieldToJasminLimbs_denote {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodV P) c) (V : Valuation Γ) :
    ((loweringL P).lowerMulti c).denote (flatVal (fun {t} x => encL P (t := t) x) V)
      = encL P (c.denote V) :=
  (loweringL P).multiFundamental_on (fun {t} x => encL P (t := t) x) (GoodV P)
    (blockSquareV P) c hc V

/-! ## 4. The decision of coverage -/

/-- The operations `GoodVB` accepts: those of `GoodV` at `P.p` except inversion. -/
def opGoodB : fieldDialect.Op → Bool
  | .fAdd q | .fSub q | .fNeg q | .fMul q | .fCopy q | .fieldDouble q | .fieldSquare q =>
      q == P.p
  | .fConst q _ => q == P.p
  | _ => false

/-- The coverage decision: every let-bound operation passes `opGoodB`. -/
def GoodVB : {Γ : Ctxt fieldDialect} → {t : FieldTy} → Com fieldDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opGoodB P e.op && GoodVB body

theorem opGoodB_sound {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t)
    (h : opGoodB P e.op = true) : GoodV P e := by
  obtain ⟨op, _, _⟩ := e
  cases op <;> simp only [opGoodB, beq_iff_eq, Bool.false_eq_true] at h <;> subst h <;>
    simp [GoodV]

/-- A program accepted by `GoodVB` is `GoodV`-covered. -/
theorem GoodVB_sound : {Γ : Ctxt fieldDialect} → {t : FieldTy} →
    (c : Com fieldDialect Γ t) → GoodVB P c = true → CoveredCom (GoodV P) c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, h => by
      simp only [GoodVB, Bool.and_eq_true] at h
      exact ⟨opGoodB_sound P e h.1, GoodVB_sound body h.2⟩

/-- Denotation preservation on a program accepted by `GoodVB`. -/
theorem fieldToJasminLimbs_denoteB {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : GoodVB P c = true) (V : Valuation Γ) :
    ((loweringL P).lowerMulti c).denote (flatVal (fun {t} x => encL P (t := t) x) V)
      = encL P (c.denote V) :=
  fieldToJasminLimbs_denote P c (GoodVB_sound P c hc) V

/-! ## 5. The lowered program over word arrays -/

section Arrays

variable (n)

/-- The type of a word array of `n` limbs. -/
abbrev arrTy : JasminTy := .stackArr 64 n

/-- The context of word arrays, one for each variable of a source context. -/
@[reducible] def arrCtx : Ctxt fieldDialect → Ctxt jasminDialect
  | [] => []
  | _ :: Γ => arrTy n :: arrCtx Γ

variable {n}

/-- The expression `stackLoad 64 n a i`. -/
def eLoad {Γ : Ctxt jasminDialect} (a : Var Γ (arrTy n)) (i : Var Γ w64) :
    Expr jasminDialect Γ w64 :=
  { op := .stackLoad 64 n, retTy_eq := rfl, args := .cons a (.cons i .nil) }

/-- The expression `stackStore 64 n a i x`. -/
def eStore {Γ : Ctxt jasminDialect} (a : Var Γ (arrTy n)) (i x : Var Γ w64) :
    Expr jasminDialect Γ (arrTy n) :=
  { op := .stackStore 64 n, retTy_eq := rfl, args := .cons a (.cons i (.cons x .nil)) }

/-- The renaming of `t :: ts` that sends the head to `v` and the tail through `h`. -/
def consHom {Δ : Ctxt jasminDialect} {t : JasminTy} {ts : Ctxt jasminDialect}
    (v : Var Δ t) (h : Ctxt.Hom ts Δ) : Ctxt.Hom (t :: ts) Δ := fun {_} w =>
  match w with
  | .here => v
  | .there w => h w

/-- The `m` words of the array `a` from index `j`, as limbs. -/
def arrLimbs (a : Fin n → BitVec 64) : (m j : Nat) → ListDenote (Rn m)
  | 0, _ => .nil
  | m + 1, j => .cons (stackGet a j) (arrLimbs a m (j + 1))

/-- The limbs of each array of a valuation of `arrCtx n Γ`, appended. -/
def arrFlat : {Γ : Ctxt fieldDialect} → Valuation (arrCtx n Γ) → Valuation (ctxFlat (mapTysL n) Γ)
  | [], .nil => .nil
  | _ :: _, .cons a A => hvAppend (arrLimbs (n := n) a n 0) (arrFlat A)

/-- The loads of `m` words of the array `a` from index `j`; the continuation receives the
    renaming of the context and the renaming of `Rn m` onto the loaded limbs. -/
def loadLimbs {bs : List JasminTy} : {Δ : Ctxt jasminDialect} → (m j : Nat) →
    Var Δ (arrTy n) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Rn m) Δ' → MC Δ' bs) → MC Δ bs
  | _, 0, _, _, k => k (fun v => v) (fun v => nomatch v)
  | _, m + 1, j, a, k =>
      bindK (eConst j) fun r₁ i =>
      bindK (eLoad (r₁ a) i) fun r₂ x =>
      loadLimbs m (j + 1) (r₂ (r₁ a)) fun r₃ h =>
        k (fun v => r₃ (r₂ (r₁ v))) (consHom (r₃ x) h)

/-- The loads of the `n` limbs of every array of `arrCtx n Γ`, through the renaming `src`;
    the continuation receives the renaming of the context and the renaming of the flattened
    context onto the loaded limbs. -/
def loadArgs {bs : List JasminTy} : (Γ : Ctxt fieldDialect) → {Δ : Ctxt jasminDialect} →
    Ctxt.Hom (arrCtx n Γ) Δ →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (ctxFlat (mapTysL n) Γ) Δ' →
      MC Δ' bs) → MC Δ bs
  | [], _, _, k => k (fun v => v) (fun v => nomatch v)
  | _ :: Γ, _, src, k =>
      loadLimbs n 0 (src .here) fun r₁ hx =>
      loadArgs Γ (fun v => r₁ (src (.there v))) fun r₂ hr =>
        k (fun v => r₂ (r₁ v)) (appendHom (fun w => r₂ (hx w)) hr)

/-- The stores of the limbs `h` into the array `o` from index `j`, returning the last
    array. -/
def storeLimbs : {Δ : Ctxt jasminDialect} → (m j : Nat) → Var Δ (arrTy n) →
    Ctxt.Hom (Rn m) Δ → MC Δ [arrTy n]
  | _, 0, _, o, _ => .ret (.cons o .nil)
  | _, m + 1, j, o, h =>
      bindK (eConst j) fun r₁ i =>
      bindK (eStore (r₁ o) i (r₁ (h .here))) fun r₂ o' =>
      storeLimbs m (j + 1) o' fun w => r₂ (r₁ (h (.there w)))

/-- The array `o` with the limbs `L` written from index `j`. -/
def storeVal (o : Fin n → BitVec 64) (j : Nat) : {m : Nat} → ListDenote (Rn m) →
    Fin n → BitVec 64
  | 0, _ => o
  | _ + 1, .cons x L => storeVal (stackSet o j x) (j + 1) L

theorem loadLimbs_denote {bs : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (a : Var Δ (arrTy n))
      (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Rn m) Δ' → MC Δ' bs)
      (W : Valuation Δ) (G : ListDenote bs), j + m < 2 ^ 64 →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h : Ctxt.Hom (Rn m) Δ')
          (W' : Valuation Δ'), Pres r W W' → pullV h W' = arrLimbs (a.lookup W) m j →
          (k r h).denote W' = G) →
      (loadLimbs m j a k).denote W = G
  | _, 0, _, _, _, W, _, _, hk => hk (fun v => v) _ W (Pres.id W) rfl
  | _, m + 1, j, a, k, W, G, hj, hk => by
      refine bindK_denote _ _ W G fun r₁ i W₁ h₁ hi => ?_
      refine bindK_denote _ _ W₁ G fun r₂ x W₂ h₂ hx => ?_
      refine loadLimbs_denote m (j + 1) _ _ W₂ G (by omega) fun r₃ h W₃ h₃ hh => ?_
      refine hk _ _ W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) ?_
      have ha : (r₂ (r₁ a)).lookup W₂ = a.lookup W := (h₂ _).trans (h₁ a)
      rw [ha] at hh
      show HVector.cons ((r₃ x).lookup W₃) (pullV h W₃) = _
      rw [hh, h₃ x, hx]
      have e : (eLoad (r₁ a) i).denote W₁
          = stackGet ((r₁ a).lookup W₁) (i.lookup W₁).toNat := rfl
      have e₀ : (i.lookup W₁).toNat = j % 2 ^ 64 := by
        rw [hi]
        exact BitVec.toNat_ofNat j 64
      rw [e, h₁ a, e₀, Nat.mod_eq_of_lt (by omega)]
      rfl

theorem pullV_pres {Γ Δ : Ctxt jasminDialect} {r : Ctxt.Hom Γ Δ} {W : Valuation Γ}
    {W' : Valuation Δ} (h : Pres r W W') : pullV r W' = W :=
  valuation_ext _ _ fun v => by rw [lookup_pullV]; exact h v

theorem pullV_comp_pres {Δ Δ' : Ctxt jasminDialect} {ts : Ctxt jasminDialect}
    {r : Ctxt.Hom Δ Δ'} {W : Valuation Δ} {W' : Valuation Δ'} (h : Pres r W W')
    (f : Ctxt.Hom ts Δ) : pullV (fun v => r (f v)) W' = pullV f W := by
  rw [pullV_comp f r, pullV_pres h]

theorem loadArgs_denote {bs : List JasminTy} (hn : n < 2 ^ 64) :
    ∀ (Γ : Ctxt fieldDialect) {Δ : Ctxt jasminDialect} (src : Ctxt.Hom (arrCtx n Γ) Δ)
      (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (ctxFlat (mapTysL n) Γ) Δ' → MC Δ' bs)
      (W : Valuation Δ) (G : ListDenote bs),
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ')
          (h : Ctxt.Hom (ctxFlat (mapTysL n) Γ) Δ') (W' : Valuation Δ'), Pres r W W' →
          pullV h W' = arrFlat (pullV src W) → (k r h).denote W' = G) →
      (loadArgs Γ src k).denote W = G
  | [], _, _, k, W, _, hk => hk (fun v => v) _ W (Pres.id W) rfl
  | _ :: Γ, _, src, k, W, G, hk => by
      refine loadLimbs_denote n 0 _ _ W G (by omega) fun r₁ hx W₁ h₁ hhx => ?_
      refine loadArgs_denote hn Γ _ _ W₁ G fun r₂ hr W₂ h₂ hhr => ?_
      refine hk _ _ W₂ (Pres.comp h₁ h₂) ?_
      rw [pullV_appendHom, hhr, pullV_comp_pres h₂ hx, hhx,
        pullV_comp_pres h₁ (fun v => src (.there v))]
      rfl

theorem storeVal_get_lt (o : Fin n → BitVec 64) (i : Nat) :
    ∀ {m : Nat} (j : Nat) (L : ListDenote (Rn m)), i < j → j + m ≤ n →
      stackGet (storeVal o j L) i = stackGet o i
  | 0, _, _, _, _ => rfl
  | m + 1, j, .cons x L, hij, hjm => by
      show stackGet (storeVal (stackSet o j x) (j + 1) L) i = _
      rw [storeVal_get_lt _ i (j + 1) L (by omega) (by omega)]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [stackGet, stackSet]
      rw [if_neg]
      intro he
      have := congrArg Fin.val he
      simp only [Nat.mod_eq_of_lt (show i < n' + 1 by omega),
        Nat.mod_eq_of_lt (show j < n' + 1 by omega)] at this
      omega

theorem arrLimbs_storeVal :
    ∀ {m : Nat} (o : Fin n → BitVec 64) (j : Nat) (L : ListDenote (Rn m)), j + m ≤ n →
      arrLimbs (storeVal o j L) m j = L
  | 0, _, _, .nil, _ => rfl
  | m + 1, o, j, .cons x L, hjm => by
      show (HVector.cons (stackGet (storeVal (stackSet o j x) (j + 1) L) j)
        (arrLimbs (storeVal (stackSet o j x) (j + 1) L) m (j + 1)) : ListDenote (Rn (m + 1)))
          = _
      rw [arrLimbs_storeVal _ (j + 1) L (by omega),
        storeVal_get_lt _ j (j + 1) L (by omega) (by omega)]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [stackGet, stackSet, if_true]

theorem storeLimbs_denote (hn : n < 2 ^ 64) :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy n)) (h : Ctxt.Hom (Rn m) Δ)
      (W : Valuation Δ), j + m ≤ n →
      (storeLimbs m j o h).denote W = .cons (storeVal (o.lookup W) j (pullV h W)) .nil
  | _, 0, _, _, _, _, _ => rfl
  | _, m + 1, j, o, h, W, hjm => by
      refine bindK_denote _ _ W _ fun r₁ i W₁ h₁ hi => ?_
      refine bindK_denote _ _ W₁ _ fun r₂ o' W₂ h₂ ho => ?_
      rw [storeLimbs_denote hn m (j + 1) o' _ W₂ (by omega)]
      have e : (eStore (r₁ o) i (r₁ (h .here))).denote W₁
          = stackSet ((r₁ o).lookup W₁) (i.lookup W₁).toNat ((r₁ (h .here)).lookup W₁) := rfl
      have e₀ : (i.lookup W₁).toNat = j := by
        rw [hi]
        exact (BitVec.toNat_ofNat j 64).trans (Nat.mod_eq_of_lt (by omega))
      rw [ho, e, e₀, h₁ o, h₁ (h .here),
        pullV_comp_pres h₂ (fun w => r₁ (h (.there w))),
        pullV_comp_pres h₁ (fun w => h (.there w))]
      rfl

end Arrays

/-! ## 6. The field program over word arrays -/

section Generic

/-- The per-operation blocks of a lowering of `fieldDialect` over `n` limbs. -/
abbrev LimbBlocks (n : Nat) : Type :=
  (op : fieldDialect.Op) →
    MultiReturnCom jasminDialect (ctxFlat (mapTysL n) (DialectSignature.sig op))
      (mapTysL n (DialectSignature.ret op))

/-- The lowering of `fieldDialect` over `n` limbs with the blocks `lo`. -/
abbrev loweringOf (lo : LimbBlocks n) : MultiBlockLoweringData fieldDialect jasminDialect where
  mapTys := mapTysL n
  lowerOp := lo

/-- **The lowered field program over word arrays, as a multi-result program**, for the
    blocks `lo`. Over the context `arrCtx n Γ ++ [arrTy n]` (a word array for each source
    variable, then the output array): the loads of the `n` limbs of every input array, the
    lowering `(loweringOf lo).lowerR` of `c` on the loaded limbs, and the stores of the
    result limbs into the output array; the program returns the last stored array. -/
def fieldBodyOf (lo : LimbBlocks n) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : MC (arrCtx n Γ ++ [arrTy n]) [arrTy n] :=
  loadArgs Γ (fun v => inlHom [arrTy n] v) fun r h =>
    (loweringOf lo).lowerR h c fun r₂ vs =>
      storeLimbs n 0 (r₂ (r (inrHom (arrCtx n Γ) .here))) (hvToHom vs)

/-- **The lowered field program over word arrays** for the blocks `lo`. -/
def fieldComOf (lo : LimbBlocks n) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : Com jasminDialect (arrCtx n Γ ++ [arrTy n]) (arrTy n) :=
  (fieldBodyOf lo c).toComHead

theorem fieldBodyOf_denote (lo : LimbBlocks n) (enc : (loweringOf lo).Enc)
    (Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
    (hsq : (loweringOf lo).BlockSquare enc Good) (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (c : Com fieldDialect Γ t) (hc : CoveredCom Good c) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64) (hA : arrFlat A = flatVal enc V) :
    (fieldBodyOf lo c).denote (hvAppend A (.cons o .nil))
      = .cons (storeVal o 0 (enc (c.denote V))) .nil := by
  refine loadArgs_denote hn Γ _ _ _ _ fun r h W' hr hh => ?_
  refine (loweringOf lo).lowerR_denote_on enc Good hsq h c _ W' V _ hc ?_
    fun r₂ vs W'' h₂ hvs => ?_
  · refine hh.trans ?_
    rw [pullV_inlHom]
    exact hA
  · have e₁ : pullV (Γ := Rn n) (fun w => hvToHom vs w) W'' = enc (c.denote V) :=
      (pullV_hvToHom W'' vs).trans hvs
    have e₂ : (r₂ (r (inrHom (arrCtx n Γ) .here))).lookup W'' = o := by
      rw [h₂, hr, lookup_inrHom]
      rfl
    refine (storeLimbs_denote hn n 0 _ (fun w => hvToHom vs w) W'' (by omega)).trans ?_
    rw [e₂, e₁]

/-- **Denotation of the lowered field program over word arrays** for the blocks `lo` with
    the block square `hsq` at the encoding `enc`. For a `Good`-covered field program `c` and
    input arrays whose limbs are the encodings of the values of `V`, the output array of
    `fieldComOf lo c` holds the limbs of the encoding of `c.denote V`, whatever the output
    array held on entry. -/
theorem fieldComOf_denote (lo : LimbBlocks n) (enc : (loweringOf lo).Enc)
    (Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
    (hsq : (loweringOf lo).BlockSquare enc Good) (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (c : Com fieldDialect Γ t) (hc : CoveredCom Good c) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64) (hA : arrFlat A = flatVal enc V) :
    arrLimbs ((fieldComOf lo c).denote (hvAppend A (.cons o .nil))) n 0
      = enc (c.denote V) := by
  rw [fieldComOf, MultiReturnCom.toComHead_denote,
    fieldBodyOf_denote lo enc Good hsq hn c hc V A o hA]
  exact arrLimbs_storeVal o 0 _ (by omega)

end Generic

/-- **The lowered field program over word arrays, as a multi-result program**, for the
    Montgomery blocks `lowerOpL P`. -/
def fieldBody {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    MC (arrCtx n Γ ++ [arrTy n]) [arrTy n] :=
  fieldBodyOf (lowerOpL P) c

/-- **The lowered field program over word arrays** for the Montgomery blocks. -/
def fieldCom {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    Com jasminDialect (arrCtx n Γ ++ [arrTy n]) (arrTy n) :=
  fieldComOf (lowerOpL P) c

theorem fieldBody_denote (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodV P) c) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => encL P (t := t) x) V) :
    (fieldBody P c).denote (hvAppend A (.cons o .nil))
      = .cons (storeVal o 0 (encL P (c.denote V))) .nil :=
  fieldBodyOf_denote (lowerOpL P) (fun {t} x => encL P (t := t) x) (GoodV P) (blockSquareV P)
    hn c hc V A o hA

/-- **Denotation of the lowered field program over word arrays.** For a `GoodV`-covered
    field program `c` and input arrays whose limbs are the encodings of the values of `V`,
    the output array of `fieldCom P c` holds the limbs of the encoding of `c.denote V`,
    whatever the output array held on entry. -/
theorem fieldCom_denote (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodV P) c) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => encL P (t := t) x) V) :
    arrLimbs ((fieldCom P c).denote (hvAppend A (.cons o .nil))) n 0
      = encL P (c.denote V) :=
  fieldComOf_denote (lowerOpL P) (fun {t} x => encL P (t := t) x) (GoodV P) (blockSquareV P)
    hn c hc V A o hA

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
