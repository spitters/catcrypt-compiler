/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontCIOS
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# `fieldDialect → jasminDialect` over `n` 64-bit limbs in Montgomery form

For a modulus record `P : FieldLimbs.Mont.LimbParams n`, the multi-value block lowering
from `fieldDialect` to `jasminDialect` that represents every field type by `n` 64-bit
registers. A value of `fp P.p` is carried by the limbs of its Montgomery form
(`FieldLimbs.Mont.enc`); values of other types are carried by `n` zero limbs. The blocks
are the generic-`n` blocks of `FieldLimbs.Mont`, so the lowering and its denotation
theorem hold for every limb count, among them `n = 4` (P-256) and `n = 6` (P-384).
The product block is `Mont.mulBlkRoute`: the interleaved block `Mont.mulBlkI` at six or
more limbs and `Mont.mulBlk` below; both satisfy the statement of `Mont.mulBlk_denote`.

| source op at `P.p` | target block |
|---|---|
| `fAdd` | `Mont.addBlk xs ys` |
| `fSub` | `Mont.subBlk xs ys` |
| `fNeg` | `Mont.negBlk xs` |
| `fMul` | `Mont.mulBlkRoute xs ys` |
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
`fieldComOf (lowerOpL P) c`, except on a program that is one product at `P.p` below six
limbs (`mulShapeLU?`), where it is `mulLoadBody`: the limbs of the first factor are loaded up
front, and the row word of each row of the schoolbook product (`prodLoadK`, `loadRowsK`)
is loaded from the array of the second factor immediately before its row, so that a row
word occupies a register only during its row.

* `loadLimbs_denote`, `loadArgs_denote`, `storeLimbs_denote`: the loads read the limbs
  `arrLimbs` of the arrays, and the stores write them (`storeVal`).
* `arrLimbs_storeVal`: the limbs read back from the stored array are the stored limbs.
* `fieldComOf_denote`: for blocks with a block square at an encoding, a covered `c` and
  input arrays whose limbs (`arrFlat`) are the encodings of the values of `V`, the limbs of
  the output array of `fieldComOf lo c` are the encoding of `c.denote V`; `fieldCom_denote`
  is its statement for `fieldCom P`.
* `prodLoadK_denote`, `mulLoadBody_denote`: the product with the row words loaded at their
  row has the value of the schoolbook product, and `mulLoadBody` writes the Montgomery
  form of the product of the factors.
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
  bindK bindK_denote eConst Pres Pres.id Pres.comp lk nv_lt mulRowK mulRowK_denote accK)
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
  | .fMul q => if q = P.p then mulBlkRoute P (opX n _) (opY n []) else constBlk n 0
  | .fInv q => if q = P.p then invBlk P (opX n []) else constBlk n 0
  | .fConst q c => if h : q = P.p then constBlk n ((cast (congrArg ZMod h) c * R P).val)
    else constBlk n 0
  | .fCopy q => if q = P.p then retN n (opX n []) else constBlk n 0
  | .fieldDouble q => if q = P.p then addBlk P (opX n []) (opX n []) else constBlk n 0
  | .fieldSquare q => if q = P.p then sqrBlk P (opX n []) else constBlk n 0

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
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact addBlk_denote P _ _ _ (opX_length _ _) (opY_length _ _) a b (nv_encX P a _)
      (nv_encY P _ b _)
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL P (.fMul P.p)).denote (hvAppend (encL P a) (hvAppend (encL P b) .nil))
      = encL P (t := .fp P.p) (fMulF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact mulBlkRoute_denote P _ _ _ (opX_length _ _) (opY_length _ _) a b (nv_encX P a _)
      (nv_encY P _ b _)
  · obtain ⟨⟩ := vals
    show (lowerOpL P (.fConst P.p c)).denote .nil = encL P (t := .fp P.p) (fConstF c)
    rw [encL_fp, lowerOpL, dite_eq_left rfl]
    exact constBlk_denote _ _ _
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fCopy P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fCopyF a)
    rw [encL_fp, lowerOpL, ite_eq_left rfl, retN_denote _ _ _ (opX_length _ _), nv_encX]
    rfl
  · rcases vals with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    show (lowerOpL P (.fSub P.p)).denote (hvAppend (encL P a) (hvAppend (encL P b) .nil))
      = encL P (t := .fp P.p) (fSubF a b)
    rw [encL_fp, encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact subBlk_denote_enc P _ _ _ (opX_length _ _) (opY_length _ _) a b (nv_encX P a _)
      (nv_encY P _ b _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fNeg P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fNegF a)
    rw [encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact negBlk_denote_enc P _ _ (opX_length _ _) a (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fieldDouble P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fDoubleF a)
    rw [encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact addBlk_denote P _ _ _ (opX_length _ _) (opX_length _ _) a a (nv_encX P a _)
      (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fieldSquare P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fSquareF a)
    rw [encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
    exact sqrBlk_denote P _ _ (opX_length _ _) a (nv_encX P a _)
  · rcases vals with _ | ⟨a, _ | _⟩
    show (lowerOpL P (.fInv P.p)).denote (hvAppend (encL P a) .nil)
      = encL P (t := .fp P.p) (fInvF a)
    rw [encL_fp, encL_fp, lowerOpL, ite_eq_left rfl]
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
      rw [ite_eq_right]
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
      simp only [stackGet, stackSet, ite_true]

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

/-! ## 7. The product with the row words loaded at their row -/

section LoadAtUse

/-- The value of the `m` words of the array `A` from index `j`, least significant first. -/
def arrVal (A : Fin n → BitVec 64) : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, j => (stackGet A j).toNat + 2 ^ 64 * arrVal A m (j + 1)

theorem arrVal_eq (A : Fin n → BitVec 64) :
    ∀ m j, arrVal A m j = nv (arrLimbs A m j) (limbVars m)
  | 0, _ => rfl
  | m + 1, j => by
      rw [arrVal, arrVal_eq A m (j + 1)]
      show _ = nv (Δ := w64 :: Rn m) (.cons _ (arrLimbs A m (j + 1)))
        (.here :: (limbVars m).map fun v => .there v)
      rw [nv_cons, nv_map_there]
      rfl

theorem eLoad_denote_of {Γ : Ctxt jasminDialect} (a : Var Γ (arrTy n)) (i : Var Γ w64)
    (W : Valuation Γ) (j : Nat) (hi : i.lookup W = BitVec.ofNat 64 j) (hj : j < 2 ^ 64) :
    (eLoad a i).denote W = stackGet (a.lookup W) j := by
  have e : (eLoad a i).denote W = stackGet (a.lookup W) (i.lookup W).toNat := rfl
  rw [e, hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

/-- The rows `i, …, i + m - 1` of the schoolbook product of the limbs `xs` and the words
    of the array `a`, accumulated into `acc`: the row word of row `j` is loaded from index
    `j` of `a` immediately before the row. -/
def loadRowsK {ts : List JasminTy} : {Δ : Ctxt jasminDialect} → Nat → Nat →
    Var Δ (arrTy n) → List (Var Δ w64) → List (Var Δ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, 0, _, _, acc, k => k (fun v => v) acc
  | _, i, m + 1, a, xs, acc, k =>
      bindK (eConst i) fun r₁ idx =>
      bindK (eLoad (r₁ a) idx) fun r₂ y =>
      accK i (xs.map fun v => r₂ (r₁ v)) y (acc.map fun v => r₂ (r₁ v)) fun r₃ acc' =>
      loadRowsK (i + 1) m (r₃ (r₂ (r₁ a))) (xs.map fun v => r₃ (r₂ (r₁ v))) acc'
        fun r₄ out => k (fun v => r₄ (r₃ (r₂ (r₁ v)))) out

theorem loadRowsK_denote {ts : List JasminTy} (A : Fin n → BitVec 64) : ∀ (m : Nat)
    {Δ : Ctxt jasminDialect} (i : Nat) (a : Var Δ (arrTy n)) (xs acc : List (Var Δ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W₀ : Valuation Δ) (G : ListDenote ts) (Y₀ : Nat),
    a.lookup W₀ = A → xs.length = n → acc.length = i + n → Y₀ < 2 ^ (64 * i) →
    i + m ≤ 2 ^ 64 → nv W₀ acc = nv W₀ xs * Y₀ →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
      (W' : Valuation Δ'), Pres r W₀ W' → out.length = i + m + n →
      nv W' out = nv W₀ xs * (Y₀ + 2 ^ (64 * i) * arrVal A m i) → (k r out).denote W' = G) →
    (loadRowsK i m a xs acc k).denote W₀ = G := by
  intro m
  induction m with
  | zero =>
    intro Δ i a xs acc k W₀ G Y₀ _ _ hacc _ _ hv hk
    rw [loadRowsK]
    exact hk _ acc W₀ (Pres.id W₀) (by simp [hacc]) (by simp [hv, arrVal])
  | succ m ih =>
    intro Δ i a xs acc k W₀ G Y₀ ha hxs hacc hY hm hv hk
    rw [loadRowsK]
    refine bindK_denote _ _ _ _ fun r₁ idx W₁ h₁ hidx => ?_
    refine bindK_denote _ _ _ _ fun r₂ y W₂ h₂ hy => ?_
    have h12 : Pres (fun v => r₂ (r₁ v)) W₀ W₂ := Pres.comp h₁ h₂
    have ey : (lk y W₂).toNat = (stackGet A i).toNat := by
      rw [show lk y W₂ = _ from hy, eLoad_denote_of _ _ _ i hidx (by omega), h₁ a, ha]
    have hX := nv_lt W₀ xs
    rw [hxs] at hX
    have hy' := (stackGet A i).isLt
    have hBi := two_pow_succ i
    have hstep : Y₀ + 2 ^ (64 * i) * (stackGet A i).toNat < 2 ^ (64 * (i + 1)) := by
      have : 2 ^ (64 * i) * (stackGet A i).toNat ≤ 2 ^ (64 * i) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hpow : 2 ^ (64 * n) * 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ (64 * (n + 1)) := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      ring_nf
    refine accK_denote_n (n := n) i _ y _ _ W₂ G (by simp [hxs]) (by simp [hacc]) ?_
      fun r₃ a' W₃ h₃ ha' hav => ?_
    · rw [nv_map h12, nv_map h12, hv, ey, ← hpow]
      calc nv W₀ xs * Y₀ + 2 ^ (64 * i) * (nv W₀ xs * (stackGet A i).toNat)
          = nv W₀ xs * (Y₀ + 2 ^ (64 * i) * (stackGet A i).toNat) := by ring
        _ < 2 ^ (64 * n) * 2 ^ (64 * (i + 1)) := Nat.mul_lt_mul'' hX hstep
    · have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W₀ W₃ := Pres.comp h12 h₃
      refine ih (i + 1) _ _ a' _ W₃ G (Y₀ + 2 ^ (64 * i) * (stackGet A i).toNat)
        (by rw [h123 a, ha]) (by simp [hxs]) (by rw [ha']; ring) hstep (by omega) ?_
        fun r₄ out W₄ h₄ hout hval => ?_
      · rw [hav, nv_map h123, nv_map h12, nv_map h12, hv, ey]
        ring
      · refine hk _ out W₄ (Pres.comp h123 h₄) (by rw [hout]; ring) ?_
        rw [hval, nv_map h123, arrVal, hBi]
        ring

/-- The schoolbook product of the limbs `xs` and the `n` words of the array `a`, as `2n`
    limbs: the row word of each row is loaded from `a` immediately before the row, so a
    row word is live only during its own row. -/
def prodLoadK {ts : List JasminTy} {Δ : Ctxt jasminDialect} (xs : List (Var Δ w64))
    (a : Var Δ (arrTy n))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) :
    MC Δ ts :=
  bindK (eConst 0) fun r₁ idx =>
  bindK (eLoad (r₁ a) idx) fun r₂ y =>
  mulRowK (xs.map fun v => r₂ (r₁ v)) y fun r₃ acc =>
  loadRowsK 1 (n - 1) (r₃ (r₂ (r₁ a))) (xs.map fun v => r₃ (r₂ (r₁ v))) acc fun r₄ out =>
    k (fun v => r₄ (r₃ (r₂ (r₁ v)))) out

theorem prodLoadK_denote {ts : List JasminTy} {Δ : Ctxt jasminDialect}
    (xs : List (Var Δ w64)) (a : Var Δ (arrTy n))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W : Valuation Δ) (G : ListDenote ts) (hn0 : 0 < n) (hn : n ≤ 2 ^ 64)
    (hxs : xs.length = n)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
      (W' : Valuation Δ'), Pres r W W' → out.length = n + n →
      nv W' out = nv W xs * arrVal (a.lookup W) n 0 → (k r out).denote W' = G) :
    (prodLoadK xs a k).denote W = G := by
  refine bindK_denote _ _ _ _ fun r₁ idx W₁ h₁ hidx => ?_
  refine bindK_denote _ _ _ _ fun r₂ y W₂ h₂ hy => ?_
  have h12 : Pres (fun v => r₂ (r₁ v)) W W₂ := Pres.comp h₁ h₂
  have ey : (lk y W₂).toNat = (stackGet (a.lookup W) 0).toNat := by
    rw [show lk y W₂ = _ from hy, eLoad_denote_of _ _ _ 0 hidx (by omega), h₁ a]
  refine mulRowK_denote _ y _ W₂ G fun r₃ acc W₃ h₃ hacc hav => ?_
  have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W W₃ := Pres.comp h12 h₃
  have hy0 := (stackGet (a.lookup W) 0).isLt
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  refine loadRowsK_denote (a.lookup W) n' 1 _ _ acc _ W₃ G (stackGet (a.lookup W) 0).toNat
    (h123 a) (by simp [hxs]) (by simp [hacc, hxs]; omega) (by simpa using hy0) (by omega) ?_
    fun r₄ out W₄ h₄ hout hval => ?_
  · rw [hav, nv_map h123, nv_map h12, ey]
  · refine hk _ out W₄ (Pres.comp h123 h₄) (by rw [hout]; omega) ?_
    rw [hval, nv_map h123, arrVal, Nat.mul_one, Nat.zero_add]

/-- The stores of the limbs `out` into the array `o` from index `0`, returning the last
    array; the array `o` itself when `out` is empty. -/
def storeOut {Δ : Ctxt jasminDialect} (o : Var Δ (arrTy n)) :
    List (Var Δ w64) → MC Δ [arrTy n]
  | [] => .ret (.cons o .nil)
  | a :: as => storeLimbs n 0 o (hvToHom (varsPad a n (a :: as)))

theorem storeOut_denote (hn : n < 2 ^ 64) {Δ : Ctxt jasminDialect} (o : Var Δ (arrTy n))
    (out : List (Var Δ w64)) (W : Valuation Δ) (hout : out.length = n) (hn0 : 0 < n) :
    (storeOut o out).denote W = .cons (storeVal (o.lookup W) 0 (limbsN n (nv W out))) .nil := by
  cases out with
  | nil => simp at hout; omega
  | cons a as =>
    subst hout
    rw [storeOut, storeLimbs_denote hn _ 0 _ _ W (by omega), pullV_hvToHom,
      lookupVars_varsPad]

/-- **The Montgomery product over word arrays with the row words loaded at their row.**
    The loads of the `n` limbs of the array `ia`, the schoolbook product `prodLoadK` with
    the words of the array `ib`, `n` words of Montgomery reduction with one conditional
    subtraction (`redcFinK`), and the stores of the result limbs into the array `o`. -/
def mulLoadBody {Δ : Ctxt jasminDialect} (ia ib o : Var Δ (arrTy n)) : MC Δ [arrTy n] :=
  loadLimbs n 0 ia fun r h =>
  prodLoadK ((limbVars n).map fun v => h v) (r ib) fun r₂ T =>
  redcFinK P T fun r₃ out =>
  storeOut (r₃ (r₂ (r o))) out

/-- On arrays `ia`, `ib` holding the limbs of the Montgomery forms of `x` and `y`,
    `mulLoadBody` writes the limbs of the Montgomery form of `x * y` into `o`. -/
theorem mulLoadBody_denote (hn : n < 2 ^ 64) {Δ : Ctxt jasminDialect}
    (ia ib o : Var Δ (arrTy n)) (W : Valuation Δ) (x y : ZMod P.p)
    (ha : arrLimbs (ia.lookup W) n 0 = enc P x) (hb : arrLimbs (ib.lookup W) n 0 = enc P y) :
    (mulLoadBody P ia ib o).denote W = .cons (storeVal (o.lookup W) 0 (enc P (x * y))) .nil := by
  have hn0 := n_pos P
  refine loadLimbs_denote n 0 ia _ W _ (by omega) fun r h W₁ hr hh => ?_
  have hX : nv W₁ ((limbVars n).map fun v => h v) = (x * R P).val := by
    rw [nv_map (W := pullV h W₁) (fun w => (lookup_pullV h w W₁).symm), hh, ha,
      enc, nv_limbVars, Nat.mod_eq_of_lt (val_lt_two_pow P _)]
  refine prodLoadK_denote _ (r ib) _ W₁ _ hn0 (by omega) (by simp [limbVars_length])
    fun r₂ T W₂ h₂ hT hTv => ?_
  have hY : arrVal ((r ib).lookup W₁) n 0 = (y * R P).val := by
    rw [hr ib, arrVal_eq, hb, enc, nv_limbVars, Nat.mod_eq_of_lt (val_lt_two_pow P _)]
  refine redcFinK_denote P T _ W₂ _ (by rw [hT]; ring)
    (by rw [hTv, hX, hY]; exact Nat.mul_lt_mul'' (val_lt P _) (val_lt P _))
    fun r₃ out W₃ h₃ hout hlt hmod => ?_
  have hv : nv W₃ out = (x * y * R P).val :=
    mont_val_eq P x y _ hlt (by rwa [hTv, hX, hY] at hmod)
  rw [storeOut_denote hn _ out W₃ hout hn0, hv, h₃, h₂, hr]
  rfl

/-- A field program that is one product at `P.p` of two variables of its context, returned
    at once: the two variables, the return type and the denotation. -/
structure MulShape {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) where
  /-- The first factor. -/
  a : Var Γ (.fp P.p)
  /-- The second factor. -/
  b : Var Γ (.fp P.p)
  /-- The return type is `fp P.p`. -/
  ht : t = .fp P.p
  /-- The program denotes the product of the two factors. -/
  hden : ∀ V : Valuation Γ, HEq (c.denote V) (fMulF (a.lookup V) (b.lookup V))

/-- The shape `MulShape` of `c`, when `c` binds one product at `P.p` and returns it. -/
def mulShape? : {Γ : Ctxt fieldDialect} → {t : FieldTy} → (c : Com fieldDialect Γ t) →
    Option (MulShape P c)
  | _, _, .var ⟨.fMul q, hr, .cons a (.cons b .nil)⟩ (.ret .here) =>
      if hq : q = P.p then
        some ⟨hq ▸ a, hq ▸ b, by subst hq hr; rfl, by intro V; subst hq hr; rfl⟩
      else none
  | _, _, _ => none

/-- The word array of a source variable in `arrCtx n Γ`. -/
def arrVar : {Γ : Ctxt fieldDialect} → {t : FieldTy} → Var Γ t → Var (arrCtx n Γ) (arrTy n)
  | _ :: _, _, .here => .here
  | _ :: _, _, .there v => .there (arrVar v)

theorem arrLimbs_arrVar (enc : ∀ {t : FieldTy}, ⟦t⟧ → Valuation (mapTysL n t)) :
    ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} (v : Var Γ t) (A : Valuation (arrCtx n Γ))
      (V : Valuation Γ), arrFlat A = flatVal enc V →
      arrLimbs ((arrVar v).lookup A) n 0 = enc (v.lookup V)
  | _ :: _, _, .here, .cons a A, .cons x V, h => by
      have e := congrArg (pullV (inlHom _)) h
      rw [arrFlat, flatVal, pullV_inlHom, pullV_inlHom] at e
      exact e
  | _ :: _, _, .there v, .cons a A, .cons x V, h => by
      have e := congrArg (pullV (inrHom _)) h
      rw [arrFlat, flatVal, pullV_inrHom, pullV_inrHom] at e
      exact arrLimbs_arrVar enc v A V e

end LoadAtUse

/-- The shape `mulShape?` of `c` when the load-at-use product applies: below six limbs.
    From six limbs the interleaved CIOS block of `fieldBodyOf` measures faster
    (P-384 multiply 1.18 of fiat C through CIOS against 1.37 through `mulLoadBody`,
    `bench/field_bytes`, 2026-10-05). -/
def mulShapeLU? {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    Option (MulShape P c) :=
  if n < 6 then mulShape? P c else none

/-- **The lowered field program over word arrays, as a multi-result program**, for the
    Montgomery blocks: `mulLoadBody` on the arrays of the two factors when `c` is one
    product at `P.p` below six limbs (`mulShapeLU?`), and `fieldBodyOf (lowerOpL P) c`
    otherwise. -/
def fieldBody {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    MC (arrCtx n Γ ++ [arrTy n]) [arrTy n] :=
  match mulShapeLU? P c with
  | some s => mulLoadBody P (inlHom [arrTy n] (arrVar s.a)) (inlHom [arrTy n] (arrVar s.b))
      (inrHom (arrCtx n Γ) .here)
  | none => fieldBodyOf (lowerOpL P) c

/-- **The lowered field program over word arrays** for the Montgomery blocks. -/
def fieldCom {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    Com jasminDialect (arrCtx n Γ ++ [arrTy n]) (arrTy n) :=
  (fieldBody P c).toComHead

theorem fieldBody_denote (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodV P) c) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => encL P (t := t) x) V) :
    (fieldBody P c).denote (hvAppend A (.cons o .nil))
      = .cons (storeVal o 0 (encL P (c.denote V))) .nil := by
  unfold fieldBody
  split
  · rename_i s _
    obtain ⟨a, b, ht, hden⟩ := s
    subst ht
    rw [mulLoadBody_denote P hn _ _ _ _ (a.lookup V) (b.lookup V)
      (by rw [lookup_inlHom, arrLimbs_arrVar (fun {t} x => encL P (t := t) x) a A V hA,
        encL_fp])
      (by rw [lookup_inlHom, arrLimbs_arrVar (fun {t} x => encL P (t := t) x) b A V hA,
        encL_fp]),
      lookup_inrHom, eq_of_heq (hden V), encL_fp]
    rfl
  · exact fieldBodyOf_denote (lowerOpL P) (fun {t} x => encL P (t := t) x) (GoodV P)
      (blockSquareV P) hn c hc V A o hA

/-- **Denotation of the lowered field program over word arrays.** For a `GoodV`-covered
    field program `c` and input arrays whose limbs are the encodings of the values of `V`,
    the output array of `fieldCom P c` holds the limbs of the encoding of `c.denote V`,
    whatever the output array held on entry. -/
theorem fieldCom_denote (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) (hc : CoveredCom (GoodV P) c) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => encL P (t := t) x) V) :
    arrLimbs ((fieldCom P c).denote (hvAppend A (.cons o .nil))) n 0
      = encL P (c.denote V) := by
  rw [fieldCom, MultiReturnCom.toComHead_denote, fieldBody_denote P hn c hc V A o hA]
  exact arrLimbs_storeVal o 0 _ (by omega)

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
