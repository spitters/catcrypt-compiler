/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontInstances

/-!
# Ascent correspondences from relational-front realizations

The relational front (`RelationalFront`) ties an abstract operation
`op : A → A → A` to a word operation `bop : BitVec 64 → BitVec 64 → BitVec 64`
through an `EndoOpRealization op bop`: an injective encoding
`enc : A → BitVec 64` with the commuting square
`enc (op a b) = bop (enc a) (enc b)`. The ascent (`Ascent.Corres`) relates a
`LowCT` command under `semScalar` to an abstract state transformer through a state
relation. This module states the scalar state relation of an encoding and derives,
from a realization, the `Corres` rule of a `LowCT` assignment whose word value is
`bop` of two slots.

The state relation `SRenc enc` reads the encoding in the direction a realization
supplies it, abstract to concrete: every non-temp name holds the word `enc` of its
abstract value. The identity word relation `SRwordBV` is `SRenc id`; the
`ZMod 2^64` relation `SRwordNT` is `SRenc wDec` for the decoder `wDec` inverse to
`wEnc`.

The rule `corres_of_realization` takes the `LowCT` command
`RScalarSetExpr dst e`. A word operation `bop` is in general not one `SExpr` node,
so the rule takes an expression `e` with `srcClean e` and the hypothesis
`∀ β, SExpr.evalBV β e = bop (β x) (β y)`: `e` computes `bop` of the slots `x`
and `y` under every reader. The abstract step sets `dst` to `op (a x) (a y)`; the
proof uses the realization's `commutes` and no injectivity.

## Main results

* `SRenc` — the scalar state relation of an encoding `enc : A → BitVec 64`.
* `srenc_iff_srwordBV`, `srwordBV_iff_srenc`, `srwordNT_iff_srenc`,
  `srenc_wDec_of_srword` — `SRenc` against `SRwordBV`, `SRwordNT` and `SRword`.
* `corres_of_realization` — the `Corres (SRenc R.enc)` rule of an
  `EndoOpRealization`.
* `corres_of_realizedKernel`, `evalBV_eq_realizedKernel_denote` — the rule for a
  `RealizedKernel`, and the agreement of the `LowCT` word value with the kernel's
  emitted `Com` denotation.
* `addMod251Expr`, `corres_addMod251`, `corres_addMod251_abr` — the instance for
  the `ZMod 251` addition kernel `addMod251RealizedKernel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Bridges.ReprTransfer
open CatCrypt.Crypto.SecureCompilation.RelationalFront
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## The state relation of an encoding -/

/-- The scalar state relation of an encoding `enc : A → BitVec 64`: every non-temp
    name holds the `.sword 64` word `enc` of its abstract value. -/
def SRenc {A : Type} (enc : A → BitVec 64) (env : SEnvScalar) (a : String → A) : Prop :=
  ∀ x, ¬ isTmpName x → env x = some ⟨.sword 64, enc (a x)⟩

/-- `SRenc enc` is the identity word relation on the encoded abstract state. -/
theorem srenc_iff_srwordBV {A : Type} (enc : A → BitVec 64) (env : SEnvScalar)
    (a : String → A) : SRenc enc env a ↔ SRwordBV env (fun s => enc (a s)) := Iff.rfl

/-- The identity word relation `SRwordBV` is `SRenc` at the identity encoding. -/
theorem srwordBV_iff_srenc (env : SEnvScalar) (a : String → BitVec 64) :
    SRwordBV env a ↔ SRenc id env a := Iff.rfl

/-- The decoder `ZMod 2^64 → BitVec 64`, the canonical representative of a residue. -/
def wDec (z : ZMod (2 ^ 64)) : BitVec 64 := BitVec.ofNat 64 z.val

/-- `wEnc` is a left inverse of `wDec`. -/
theorem wEnc_wDec (z : ZMod (2 ^ 64)) : wEnc (wDec z) = z := by
  simp only [wEnc, wDec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ZMod.val_lt z),
    ZMod.natCast_val, ZMod.cast_id', id]

/-- `wDec` is a left inverse of `wEnc`. -/
theorem wDec_wEnc (w : BitVec 64) : wDec (wEnc w) = w := by
  apply BitVec.eq_of_toNat_eq
  simp only [wDec, wEnc, BitVec.toNat_ofNat, ZMod.val_natCast, Nat.mod_eq_of_lt w.isLt]

/-- The `ZMod 2^64` word relation `SRwordNT` is `SRenc` at the decoder `wDec`. -/
theorem srwordNT_iff_srenc (env : SEnvScalar) (a : String → ZMod (2 ^ 64)) :
    SRwordNT env a ↔ SRenc wDec env a := by
  constructor
  · intro h x hx
    obtain ⟨w, hw, hwa⟩ := h x hx
    rw [hw, ← hwa, wDec_wEnc]
  · intro h x hx
    exact ⟨wDec (a x), h x hx, wEnc_wDec (a x)⟩

/-- The total word relation `SRword` implies `SRenc` at the decoder `wDec`. -/
theorem srenc_wDec_of_srword {env : SEnvScalar} {a : String → ZMod (2 ^ 64)}
    (h : SRword env a) : SRenc wDec env a :=
  (srwordNT_iff_srenc env a).mp (srword_srwordNT h)

/-! ## The correspondence rule of a realization -/

/-- The `Corres` rule of an `EndoOpRealization op bop`. If `e` is source-clean and
    computes `bop` of the slots `x` and `y` under every reader, then
    `RScalarSetExpr dst e` corresponds, under `SRenc R.enc`, to the abstract step
    setting `dst` to `op (a x) (a y)` and leaving every other name unchanged. -/
theorem corres_of_realization {A : Type} {op : A → A → A}
    {bop : BitVec 64 → BitVec 64 → BitVec 64} (R : EndoOpRealization op bop)
    (dst x y : String) (e : SExpr) (he : srcClean e)
    (hbop : ∀ β : String → BitVec 64, SExpr.evalBV β e = bop (β x) (β y)) :
    Corres (SRenc R.enc) (fun _ => True)
      (fun a s => if s = dst then op (a x) (a y) else a s)
      (.RScalarSetExpr dst e) := by
  intro env a hSR _
  obtain ⟨env', hstep, hSR'⟩ :=
    corres_setExprWord dst e he env (fun s => R.enc (a s)) hSR trivial
  refine ⟨env', hstep, fun s hs => ?_⟩
  have h := hSR' s hs
  by_cases hsd : s = dst
  · simp only [if_pos hsd] at h ⊢
    rw [h, hbop, R.commutes]
  · simp only [if_neg hsd] at h ⊢
    exact h

/-- The `Corres` rule of a `RealizedKernel`: `corres_of_realization` at the kernel's
    realization. -/
theorem corres_of_realizedKernel {A : Type} {op : A → A → A} (K : RealizedKernel op)
    (dst x y : String) (e : SExpr) (he : srcClean e)
    (hbop : ∀ β : String → BitVec 64, SExpr.evalBV β e = K.bop (β x) (β y)) :
    Corres (SRenc K.realization.enc) (fun _ => True)
      (fun a s => if s = dst then op (a x) (a y) else a s)
      (.RScalarSetExpr dst e) :=
  corres_of_realization K.realization dst x y e he hbop

/-- The word value of an expression computing a kernel's `bop` is the denotation of
    the kernel's emitted `Com` on the valuation `(β y, β x)`. -/
theorem evalBV_eq_realizedKernel_denote {A : Type} {op : A → A → A}
    (K : RealizedKernel op) (x y : String) (e : SExpr)
    (hbop : ∀ β : String → BitVec 64, SExpr.evalBV β e = K.bop (β x) (β y))
    (β : String → BitVec 64) :
    SExpr.evalBV β e = Com.denote K.com (.cons (β y) (.cons (β x) .nil)) := by
  rw [hbop, K.com_denotes_bop]

/-! ## The `ZMod 251` addition kernel -/

/-- The `SExpr` computing `csub251 s` from an expression `s`: the branch-free
    conditional subtraction of `251`. -/
def csub251Expr (s : SExpr) : SExpr :=
  .SAdd (.SSub s (.SLit 251))
    (.SAnd (.SSub (.SLit 0) (.SShr (.SSub s (.SLit 251)) (.SLit 63))) (.SLit 251))

/-- The `SExpr` computing `addMod251RealizedKernel.bop` of the slots `x` and `y`. -/
def addMod251Expr (x y : String) : SExpr := csub251Expr (.SAdd (.SVar x) (.SVar y))

/-- `addMod251Expr x y` evaluates to the kernel operator on the slots `x` and `y`. -/
theorem evalBV_addMod251Expr (x y : String) (β : String → BitVec 64) :
    SExpr.evalBV β (addMod251Expr x y) = addMod251RealizedKernel.bop (β x) (β y) := rfl

/-- `addMod251Expr x y` is source-clean when `x` and `y` are not temp names. -/
theorem srcClean_addMod251Expr {x y : String} (hx : ¬ isTmpName x) (hy : ¬ isTmpName y) :
    srcClean (addMod251Expr x y) := by
  have h251 : srcClean (.SLit 251) := show 251 < 2 ^ 64 by norm_num
  have h63 : srcClean (.SLit 63) := show 63 < 2 ^ 64 by norm_num
  have h0 : srcClean (.SLit 0) := show 0 < 2 ^ 64 by norm_num
  exact ⟨⟨⟨hx, hy⟩, h251⟩, ⟨⟨h0, ⟨⟨⟨hx, hy⟩, h251⟩, h63⟩⟩, h251⟩⟩

/-- The `Corres` rule of the `ZMod 251` addition kernel: `RScalarSetExpr dst
    (addMod251Expr x y)` corresponds, under `SRenc encMod251`, to the abstract step
    setting `dst` to `a x + a y` in `ZMod 251`. -/
theorem corres_addMod251 (dst x y : String) (hx : ¬ isTmpName x) (hy : ¬ isTmpName y) :
    Corres (SRenc addMod251RealizedKernel.realization.enc) (fun _ => True)
      (fun a s => if s = dst then a x + a y else a s)
      (.RScalarSetExpr dst (addMod251Expr x y)) :=
  corres_of_realizedKernel addMod251RealizedKernel dst x y _
    (srcClean_addMod251Expr hx hy) (evalBV_addMod251Expr x y)

/-- `corres_addMod251` at the slot names `a`, `b` and destination `r`. -/
theorem corres_addMod251_abr :
    Corres (SRenc encMod251) (fun _ => True)
      (fun φ s => if s = "r" then φ "a" + φ "b" else φ s)
      (.RScalarSetExpr "r" (addMod251Expr "a" "b")) :=
  corres_addMod251 "r" "a" "b" (notTmp_of_short "a" (by decide))
    (notTmp_of_short "b" (by decide))

end CatCrypt.Crypto.SecureCompilation.Ascent
