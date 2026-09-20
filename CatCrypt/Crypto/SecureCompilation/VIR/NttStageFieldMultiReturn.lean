/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PolyToField
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom

/-!
# One radix-2 NTT stage as a multi-return `fieldDialect` program

`VIR/PolyToField.lean` carries one Cooley–Tukey butterfly as two single-return
`Com fieldDialect` schedules, one per output.  A transform stage is `n/2`
butterflies whose two outputs share the twiddle product, and a stage's `n`
outputs are the next stage's `n` inputs, so a stage has no single-return form.

`MultiReturnCom` (`VIR/MultiReturnCom.lean`) is the multi-output `Com`: it keeps
the same A-normal-form binding chain and returns an `HVector` of variables
indexed by a list of dialect types.  A stage is therefore expressible over the
existing `FieldTy` alphabet, with no array type, index type or memory op: the
`n` lanes are `n` separate `fp q` bindings and the stage boundary is the return
list `[fp q, fp q, fp q, fp q]`.

This file carries the smallest stage with a non-trivial twiddle — stage `1` of a
four-point transform, two butterflies with twiddles `1` and `ω` — and ties its
denotation to `CompPoly`'s `butterflyStageSpec` at that stage.

The last four bindings of `stage1Prog` are its four outputs in output order,
which is the convention `JasminLprogExport.Com.toLprogPhysAbi` reads when it
emits one epilogue store per output.

## Main definitions

* `F` — the `fp q` dialect type, abbreviated.
* `b0`, `b1`, `b2`, `b3`, `b4`, `b6`, `b8` — the de Bruijn variables at those
  indices of a context carrying the named dialect type at that position.
* `constE`, `addE`, `subE`, `mulE` — the one-op `fieldDialect` expression
  builders used by the stage.
* `Γstage4`, `stageVal` — the stage input context `[fp q, fp q, fp q, fp q, fp q]`
  carrying `(ζ, x₀, x₁, x₂, x₃)`, and its valuation.
* `Out4` — the stage return list `[fp q, fp q, fp q, fp q]`.
* `toArray4` — a four-entry stage output read as an `Array (ZMod q)`.
* `stage1Prog` — stage `1` of the four-point transform as a
  `MultiReturnCom fieldDialect (Γstage4 q) (Out4 q)`.

## Main results

* `stage1Prog_denote` — the four lanes of the `stage1Prog` denotation.
* `stage1_lanes` — the four lanes of `butterflyStageSpec D 1` on a domain of
  size four.
* `stage1_denote` — on a domain of size four, `butterflyStageSpec D 1` applied to
  `#[x₀, x₁, x₂, x₃]` equals `toArray4` of the denotation of `stage1Prog` at
  twiddle `D.omega`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldMultiReturn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var)
open CompPoly.CPolynomial.NTT (Domain)
open CompPoly.CPolynomial.NTT.Transform (butterflyStageSpec butterflyBlockStep butterflyInnerStep)

variable {q : Nat}

/-! ## 1. Abbreviations

The stage context is homogeneous — every lane and the twiddle are `fp q` — so a
variable is fixed by its de Bruijn index alone.  `b0`–`b8` name the indices the
stage uses; each is well-typed in any context carrying the same dialect type at
that position. -/

/-- The prime-field dialect type at modulus `q`. -/
abbrev F (q : Nat) : FieldTy := FieldTy.fp q

/-- The variable at de Bruijn index `0`. -/
abbrev b0 {Γ : Ctxt fieldDialect} {t : FieldTy} : Var (t :: Γ) t := .here
/-- The variable at de Bruijn index `1`. -/
abbrev b1 {Γ : Ctxt fieldDialect} {t a₀ : FieldTy} : Var (a₀ :: t :: Γ) t := .there .here
/-- The variable at de Bruijn index `2`. -/
abbrev b2 {Γ : Ctxt fieldDialect} {t a₀ a₁ : FieldTy} :
    Var (a₀ :: a₁ :: t :: Γ) t := .there (.there .here)
/-- The variable at de Bruijn index `3`. -/
abbrev b3 {Γ : Ctxt fieldDialect} {t a₀ a₁ a₂ : FieldTy} :
    Var (a₀ :: a₁ :: a₂ :: t :: Γ) t := .there (.there (.there .here))
/-- The variable at de Bruijn index `4`. -/
abbrev b4 {Γ : Ctxt fieldDialect} {t a₀ a₁ a₂ a₃ : FieldTy} :
    Var (a₀ :: a₁ :: a₂ :: a₃ :: t :: Γ) t := .there (.there (.there (.there .here)))
/-- The variable at de Bruijn index `6`. -/
abbrev b6 {Γ : Ctxt fieldDialect} {t a₀ a₁ a₂ a₃ a₄ a₅ : FieldTy} :
    Var (a₀ :: a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: t :: Γ) t :=
  .there (.there (.there (.there (.there (.there .here)))))
/-- The variable at de Bruijn index `8`. -/
abbrev b8 {Γ : Ctxt fieldDialect} {t a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : FieldTy} :
    Var (a₀ :: a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: a₆ :: a₇ :: t :: Γ) t :=
  .there (.there (.there (.there (.there (.there (.there (.there .here)))))))

/-- The nullary `fConst q c` expression. -/
def constE {Γ : Ctxt fieldDialect} (c : ZMod q) : Expr fieldDialect Γ (F q) :=
  ⟨.fConst q c, rfl, .nil⟩

/-- The `fAdd q` expression on two variables. -/
def addE {Γ : Ctxt fieldDialect} (a b : Var Γ (F q)) : Expr fieldDialect Γ (F q) :=
  ⟨.fAdd q, rfl, .cons a (.cons b .nil)⟩

/-- The `fSub q` expression on two variables. -/
def subE {Γ : Ctxt fieldDialect} (a b : Var Γ (F q)) : Expr fieldDialect Γ (F q) :=
  ⟨.fSub q, rfl, .cons a (.cons b .nil)⟩

/-- The `fMul q` expression on two variables. -/
def mulE {Γ : Ctxt fieldDialect} (a b : Var Γ (F q)) : Expr fieldDialect Γ (F q) :=
  ⟨.fMul q, rfl, .cons a (.cons b .nil)⟩

/-! ## 2. The stage interface -/

/-- The stage input context: the twiddle base `ζ` and the four lanes. -/
abbrev Γstage4 (q : Nat) : Ctxt fieldDialect := [F q, F q, F q, F q, F q]

/-- The valuation `⟨ζ, x₀, x₁, x₂, x₃⟩` of `Γstage4`. -/
def stageVal (z x0 x1 x2 x3 : ZMod q) : Ctxt.Valuation (Γstage4 q) :=
  .cons z (.cons x0 (.cons x1 (.cons x2 (.cons x3 .nil))))

/-- The stage return list: four lanes. -/
abbrev Out4 (q : Nat) : List fieldDialect.Ty := [F q, F q, F q, F q]

/-- A four-entry stage output read as an `Array (ZMod q)`, lane `i` at index `i`. -/
def toArray4 : ListDenote (Out4 q) → Array (ZMod q)
  | .cons v0 (.cons v1 (.cons v2 (.cons v3 .nil))) => #[v0, v1, v2, v3]

/-! ## 3. The stage program

Stage `1` of a four-point transform is one block of two butterflies, on the lane
pairs `(0, 2)` and `(1, 3)`, with twiddles `1` and `ζ`.  Each butterfly's two
outputs share its twiddle product: `t₀` is read by `o₀` and `o₂`, `t₁` by `o₁`
and `o₃`.  A per-output schedule would bind each product twice. -/

/-- Stage `1` of the four-point transform: the twiddle constant `1`, the two
    twiddle products, then the four output lanes in order. -/
def stage1Prog : MultiReturnCom fieldDialect (Γstage4 q) (Out4 q) :=
  .var (constE (1 : ZMod q))            -- c₁
    (.var (mulE b0 b4)                  -- t₀ = c₁ · x₂
      (.var (mulE b2 b6)                -- t₁ = ζ · x₃
        (.var (addE b4 b1)              -- o₀ = x₀ + t₀
          (.var (addE b6 b1)            -- o₁ = x₁ + t₁
            (.var (subE b6 b3)          -- o₂ = x₀ − t₀
              (.var (subE b8 b3)        -- o₃ = x₁ − t₁
                (.ret (.cons b3 (.cons b2 (.cons b1 (.cons b0 .nil)))))))))))

/-! ## 4. The stage denotation against `butterflyStageSpec`

`butterflyStageSpec D 1` on a domain of size four has `blockSize = 4`,
`half = 2`, `wm = D.omega ^ (4 / 4)` and one block, so it is two inner steps
with running twiddles `1` and `wm`. -/

/-- The four lanes `stage1Prog` denotes to: the two butterflies on the lane pairs
    `(0, 2)` and `(1, 3)`, at twiddles `1` and `z`. -/
theorem stage1Prog_denote (z x0 x1 x2 x3 : ZMod q) :
    toArray4 ((stage1Prog (q := q)).denote (stageVal z x0 x1 x2 x3))
      = #[x0 + 1 * x2, x1 + z * x3, x0 - 1 * x2, x1 - z * x3] := rfl

variable [Fact (Nat.Prime q)]

/-- The lane-by-lane value of stage `1` of `butterflyStageSpec` on a domain of
    size four. -/
theorem stage1_lanes (D : Domain (ZMod q)) (hlog : D.logN = 2) (x0 x1 x2 x3 : ZMod q) :
    butterflyStageSpec D 1 #[x0, x1, x2, x3]
      = #[x0 + 1 * x2, x1 + 1 * D.omega ^ 1 * x3,
          x0 - 1 * x2, x1 - 1 * D.omega ^ 1 * x3] := by
  obtain ⟨logN, ω, prim⟩ := D
  subst hlog
  have h1 : butterflyStageSpec (R := ZMod q) ⟨2, ω, prim⟩ 1 #[x0, x1, x2, x3]
      = butterflyBlockStep 4 2 (ω ^ 1) 0 #[x0, x1, x2, x3] := by
    simp [butterflyStageSpec]
  have h2 : butterflyBlockStep (R := ZMod q) 4 2 (ω ^ 1) 0 #[x0, x1, x2, x3]
      = (butterflyInnerStep 4 2 (ω ^ 1) 0 1
          (butterflyInnerStep 4 2 (ω ^ 1) 0 0 (#[x0, x1, x2, x3], 1))).1 := rfl
  rw [h1, h2]
  simp [butterflyInnerStep]

/-- Stage `1` of `butterflyStageSpec` on a four-element array equals the four
    lanes of `stage1Prog` run at twiddle `D.omega`. -/
theorem stage1_denote (D : Domain (ZMod q)) (hlog : D.logN = 2) (x0 x1 x2 x3 : ZMod q) :
    butterflyStageSpec D 1 #[x0, x1, x2, x3]
      = toArray4 ((stage1Prog (q := q)).denote (stageVal D.omega x0 x1 x2 x3)) := by
  rw [stage1Prog_denote, stage1_lanes D hlog]
  simp

end CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldMultiReturn
