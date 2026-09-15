/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs25519
public import CatCrypt.Crypto.SecureCompilation.VIR.EdPointOnCurve

/-!
# The `a = −1` extended-coordinate point addition as a `fieldDialect` program

`pointAddProg dd i` is a `Com fieldDialect` program over eight field elements
`X₁, Y₁, Z₁, T₁, X₂, Y₂, Z₂, T₂` of `ZMod (2^255 - 19)`, binding the twenty-three
steps of the Hisil–Wong–Carter–Dawson addition at `a = −1` with curve constant
`dd`,

```
A = (Y₁−X₁)(Y₂−X₂);  B = (Y₁+X₁)(Y₂+X₂);  C = T₁·2dd·T₂;  D = 2Z₁·Z₂
E = B−A;  F = D−C;  G = D+C;  H = B+A
X₃ = E·F;  Y₃ = G·H;  Z₃ = F·G;  T₃ = E·H
```

and returning coordinate `i` of the result. The last four bindings are `fCopy`
bindings of `X₃`, `Y₃`, `Z₃`, `T₃` in that order, so the four coordinates are the
last four bindings of the program whichever one is returned.

Every binding is an `fAdd`, `fSub`, `fMul`, `fieldDouble`, `fConst` or `fCopy` at
`2^255 - 19`, which is the coverage predicate `FieldToJasminLimbs25519.GoodL`, so
the program lowers to four 64-bit limbs per coordinate by
`fieldToJasminLimbs_denote`.

## Curve parameters

`ed25519Ext` is the `Jasmin.EdwardsCurve.EdwardsParams` record at `a = −1` and
`d = ed25519D`, built from `EdPointOnCurve.isEdCurve_of_ed25519_constants`. Its
`nonsquare_d` field is the completeness condition, so
`EdwardsPointExt.m1add_ZneZero` applies: at inputs that are extended points — `Z ≠ 0`,
`T·Z = X·Y`, and `(X/Z, Y/Z)` on the curve — the denominator `F·G` of the formula is
nonzero and the formula has no exceptional case. The inputs need satisfy nothing
beyond membership in `EdwardsPointExt ed25519Ext`; in particular the two points may
be equal, opposite, or the identity.

## Main definitions

* `inCtxt`, `inVal`: the eight input field elements and a valuation of them.
* `vAt`: the variable `n` bindings from the top of a context.
* `addSpec`: the four output coordinates as a function of the inputs.
* `pointAddBody`, `pointAddProg`: the twenty-three bindings and the program
  returning coordinate `i`.
* `ed25519Ext`: the Ed25519 curve record.

## Main results

* `pointAddProg_covered`: every binding is `GoodL`.
* `pointAddProg_denote_x3`, `_y3`, `_z3`, `_t3`: the four denotations are the four
  entries of `addSpec`.
* `addSpec_m1add`: `addSpec` at `ed25519D` is the coordinate quadruple of
  `EdwardsPointExt.m1add`.
* `pointAddProg_m1add`: the program's four outputs are the coordinates of
  `m1add P Q`, whose affine projection is `EdwardsPointAff.add P.toAff Q.toAff`.
* `pointAddProg_z3_ne_zero`: the third output is nonzero at extended-point inputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs25519 (F25519 GoodL)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (p25519)
open CatCrypt.Crypto.Jasmin.EdwardsCurve (EdwardsPointAff EdwardsPointExt)
open CatCrypt.Util (P25519 ed25519D)

/-! ## 1. Inputs and variables -/

/-- The input context: `X₁, Y₁, Z₁, T₁, X₂, Y₂, Z₂, T₂`, the first at the head. -/
abbrev inCtxt : Ctxt fieldDialect := List.replicate 8 F25519

/-- The valuation of the eight inputs. -/
def inVal (x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) : Valuation inCtxt :=
  .cons x1 (.cons y1 (.cons z1 (.cons t1 (.cons x2 (.cons y2 (.cons z2 (.cons t2 .nil)))))))

/-- The variable `n` bindings from the top of a context. -/
def vAt : (n : Nat) → {Γ : Ctxt fieldDialect} →
    @Var fieldDialect (List.replicate (n + 1) F25519 ++ Γ) F25519
  | 0, _ => .here
  | n + 1, _ => (vAt n).there

/-! ## 2. The bindings -/

section Exprs

variable {Γ : Ctxt fieldDialect}

/-- The binding `a + b`. -/
def eAdd (a b : Var Γ F25519) : Expr fieldDialect Γ F25519 :=
  ⟨.fAdd p25519, rfl, .cons a (.cons b .nil)⟩

/-- The binding `a − b`. -/
def eSub (a b : Var Γ F25519) : Expr fieldDialect Γ F25519 :=
  ⟨.fSub p25519, rfl, .cons a (.cons b .nil)⟩

/-- The binding `a · b`. -/
def eMul (a b : Var Γ F25519) : Expr fieldDialect Γ F25519 :=
  ⟨.fMul p25519, rfl, .cons a (.cons b .nil)⟩

/-- The binding `a + a`. -/
def eDbl (a : Var Γ F25519) : Expr fieldDialect Γ F25519 :=
  ⟨.fieldDouble p25519, rfl, .cons a .nil⟩

/-- The binding of the constant `c`. -/
def eConst (c : ZMod p25519) : Expr fieldDialect Γ F25519 :=
  ⟨.fConst p25519 c, rfl, .nil⟩

/-- The binding `a`, as its own binding. -/
def eCopy (a : Var Γ F25519) : Expr fieldDialect Γ F25519 :=
  ⟨.fCopy p25519, rfl, .cons a .nil⟩

theorem good_eAdd (a b : Var Γ F25519) : GoodL (eAdd a b) := Or.inl rfl

theorem good_eSub (a b : Var Γ F25519) : GoodL (eSub a b) := Or.inr (Or.inl rfl)

theorem good_eMul (a b : Var Γ F25519) : GoodL (eMul a b) :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem good_eDbl (a : Var Γ F25519) : GoodL (eDbl a) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

theorem good_eConst (c : ZMod p25519) : GoodL (eConst (Γ := Γ) c) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))))

theorem good_eCopy (a : Var Γ F25519) : GoodL (eCopy a) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

end Exprs

/-! ## 3. The program -/

/-- The context of the continuation: the twenty-three bindings over the inputs. -/
abbrev outCtxt : Ctxt fieldDialect := List.replicate 23 F25519 ++ inCtxt

/-- The twenty-three bindings of the addition at curve constant `dd`, followed by
    the continuation `k`. The bindings are `Y₁−X₁`, `Y₂−X₂`, `A`, `Y₁+X₁`, `Y₂+X₂`,
    `B`, `2dd`, `T₁·2dd`, `C`, `2Z₁`, `D`, `E`, `F`, `G`, `H`, `X₃`, `Y₃`, `T₃`,
    `Z₃`, and copies of `X₃`, `Y₃`, `Z₃`, `T₃`. -/
def pointAddBody (dd : ZMod p25519) {s : FieldTy} (k : Com fieldDialect outCtxt s) :
    Com fieldDialect inCtxt s :=
  .var (eSub (vAt 1) (vAt 0)) <|
  .var (eSub (vAt 6) (vAt 5)) <|
  .var (eMul (vAt 1) (vAt 0)) <|
  .var (eAdd (vAt 4) (vAt 3)) <|
  .var (eAdd (vAt 9) (vAt 8)) <|
  .var (eMul (vAt 1) (vAt 0)) <|
  .var (eConst (dd + dd)) <|
  .var (eMul (vAt 10) (vAt 0)) <|
  .var (eMul (vAt 0) (vAt 15)) <|
  .var (eDbl (vAt 11)) <|
  .var (eMul (vAt 0) (vAt 16)) <|
  .var (eSub (vAt 5) (vAt 8)) <|
  .var (eSub (vAt 1) (vAt 3)) <|
  .var (eAdd (vAt 2) (vAt 4)) <|
  .var (eAdd (vAt 8) (vAt 11)) <|
  .var (eMul (vAt 3) (vAt 2)) <|
  .var (eMul (vAt 2) (vAt 1)) <|
  .var (eMul (vAt 5) (vAt 2)) <|
  .var (eMul (vAt 5) (vAt 4)) <|
  .var (eCopy (vAt 3)) <|
  .var (eCopy (vAt 3)) <|
  .var (eCopy (vAt 2)) <|
  .var (eCopy (vAt 4)) <|
  k

/-- The variable of output coordinate `i` among the four trailing copies. -/
def outVar : Fin 4 → Var outCtxt F25519
  | 0 => vAt 3
  | 1 => vAt 2
  | 2 => vAt 1
  | 3 => vAt 0

/-- The extended-coordinate addition at curve constant `dd`, returning coordinate
    `i` of `X₃, Y₃, Z₃, T₃`. -/
def pointAddProg (dd : ZMod p25519) (i : Fin 4) : Com fieldDialect inCtxt F25519 :=
  pointAddBody dd (.ret (outVar i))

theorem pointAddProg_covered (dd : ZMod p25519) (i : Fin 4) :
    CoveredCom GoodL (pointAddProg dd i) :=
  ⟨good_eSub _ _, good_eSub _ _, good_eMul _ _, good_eAdd _ _, good_eAdd _ _,
    good_eMul _ _, good_eConst _, good_eMul _ _, good_eMul _ _, good_eDbl _,
    good_eMul _ _, good_eSub _ _, good_eSub _ _, good_eAdd _ _, good_eAdd _ _,
    good_eMul _ _, good_eMul _ _, good_eMul _ _, good_eMul _ _, good_eCopy _,
    good_eCopy _, good_eCopy _, good_eCopy _, trivial⟩

/-! ## 4. The value of the program -/

/-- The four output coordinates of the addition at curve constant `dd`. -/
def addSpec (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    ZMod p25519 × ZMod p25519 × ZMod p25519 × ZMod p25519 :=
  let a := (y1 - x1) * (y2 - x2)
  let b := (y1 + x1) * (y2 + x2)
  let c := t1 * (dd + dd) * t2
  let dv := (z1 + z1) * z2
  let e := b - a
  let f := dv - c
  let g := dv + c
  let h := b + a
  (e * f, g * h, f * g, e * h)

theorem pointAddProg_denote_x3 (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    (pointAddProg dd 0).denote (inVal x1 y1 z1 t1 x2 y2 z2 t2)
      = (addSpec dd x1 y1 z1 t1 x2 y2 z2 t2).1 := rfl

theorem pointAddProg_denote_y3 (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    (pointAddProg dd 1).denote (inVal x1 y1 z1 t1 x2 y2 z2 t2)
      = (addSpec dd x1 y1 z1 t1 x2 y2 z2 t2).2.1 := rfl

theorem pointAddProg_denote_z3 (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    (pointAddProg dd 2).denote (inVal x1 y1 z1 t1 x2 y2 z2 t2)
      = (addSpec dd x1 y1 z1 t1 x2 y2 z2 t2).2.2.1 := rfl

theorem pointAddProg_denote_t3 (dd x1 y1 z1 t1 x2 y2 z2 t2 : ZMod p25519) :
    (pointAddProg dd 3).denote (inVal x1 y1 z1 t1 x2 y2 z2 t2)
      = (addSpec dd x1 y1 z1 t1 x2 y2 z2 t2).2.2.2 := rfl

/-! ## 5. The group law -/

/-- The Ed25519 curve `−x² + y² = 1 + d·x²·y²` as the record of
    `Jasmin/EdwardsCurve.lean`, with the completeness conditions of
    `EdPointOnCurve.isEdCurve_of_ed25519_constants`. -/
def ed25519Ext : CatCrypt.Crypto.Jasmin.EdwardsCurve.EdwardsParams (ZMod P25519) :=
  (CatCrypt.Crypto.SecureCompilation.VIR.EdPointOnCurve.isEdCurve_of_ed25519_constants
    (C := ⟨-1, ed25519D⟩) rfl rfl).toCurve

theorem ed25519Ext_a : ed25519Ext.a = -1 := rfl

theorem ed25519Ext_d : ed25519Ext.d = ed25519D := rfl

/-- The valuation of the eight coordinates of two extended points. -/
def extVal (P Q : EdwardsPointExt ed25519Ext) : Valuation inCtxt :=
  inVal P.X P.Y P.Z P.T Q.X Q.Y Q.Z Q.T

theorem addSpec_m1add (P Q : EdwardsPointExt ed25519Ext) :
    addSpec ed25519D P.X P.Y P.Z P.T Q.X Q.Y Q.Z Q.T
      = ((EdwardsPointExt.m1add ed25519Ext_a P Q).X,
         (EdwardsPointExt.m1add ed25519Ext_a P Q).Y,
         (EdwardsPointExt.m1add ed25519Ext_a P Q).Z,
         (EdwardsPointExt.m1add ed25519Ext_a P Q).T) := by
  simp only [addSpec, EdwardsPointExt.m1add, ed25519Ext_d, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, trivial⟩

/-- **The program adds the two points.** At inputs that are extended points of the
    Ed25519 curve, the four outputs are the coordinates of `m1add P Q`, and the
    affine projection of that point is the sum of the affine projections of the
    inputs. -/
theorem pointAddProg_m1add (P Q : EdwardsPointExt ed25519Ext) :
    (pointAddProg ed25519D 0).denote (extVal P Q)
        = (EdwardsPointExt.m1add ed25519Ext_a P Q).X ∧
      (pointAddProg ed25519D 1).denote (extVal P Q)
        = (EdwardsPointExt.m1add ed25519Ext_a P Q).Y ∧
      (pointAddProg ed25519D 2).denote (extVal P Q)
        = (EdwardsPointExt.m1add ed25519Ext_a P Q).Z ∧
      (pointAddProg ed25519D 3).denote (extVal P Q)
        = (EdwardsPointExt.m1add ed25519Ext_a P Q).T ∧
      (EdwardsPointExt.m1add ed25519Ext_a P Q).toAff
        = EdwardsPointAff.add P.toAff Q.toAff := by
  have h := addSpec_m1add P Q
  rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff] at h
  exact ⟨(pointAddProg_denote_x3 ..).trans h.1,
    (pointAddProg_denote_y3 ..).trans h.2.1,
    (pointAddProg_denote_z3 ..).trans h.2.2.1,
    (pointAddProg_denote_t3 ..).trans h.2.2.2,
    EdwardsPointExt.to_affine_m1add ed25519Ext_a P Q⟩

/-- **The formula has no exceptional case.** At extended-point inputs the third
    output `Z₃ = F·G` is nonzero, so the quadruple of outputs is again an extended
    point. -/
theorem pointAddProg_z3_ne_zero (P Q : EdwardsPointExt ed25519Ext) :
    (pointAddProg ed25519D 2).denote (extVal P Q) ≠ (0 : ZMod p25519) := by
  rw [(pointAddProg_m1add P Q).2.2.1]
  exact (EdwardsPointExt.m1add ed25519Ext_a P Q).Z_ne_zero

end CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd
