/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-!
# Equality saturation as the equality test between two dialect programs

Two `Com jasminDialect` programs that the bounded saturation engine sends to the
same term denote the same function. The search that produced the two canonical
forms is untrusted: the certificate is `saturateCom_denote` applied on each side
together with the syntactic equality of the results, so an incomplete or
badly-tuned search costs coverage and never soundness.

## What is proved

* `KEnv.unknown` — the environment that claims no constant, consistent with every
  valuation (`KEnv.unknown_consistent`). It is the starting environment for a
  program whose constants are all introduced by its own `regConst` binders.
* `denote_eq_of_saturateCom_eq` — the certificate: equal saturations give equal
  denotations.
* `denote_eq_of_saturateCom_eq_unknown` — the same with the starting environment
  fixed to `KEnv.unknown`, so the only hypothesis left is the syntactic equality
  of the two canonical forms.
* `addZero_xorZero_denote_eq` — a worked pair. `x + 0` and `x ^^^ 0` are
  different programs with different ops; both saturate to the same term, and
  their denotational equality follows with no `BitVec` reasoning of its own.
* `mulZero_ne_addZero_saturate` — the negative side. `x * 0` saturates to a
  different term than `x + 0`, so the test rejects a pair that is not
  denotationally equal.

## Where this sits

The descent compiles a source program to a `Com jasminDialect`. The ascent, via
`JInstrToArithBlock`, lifts a decoded machine block to a `Com jasminDialect`.
The two are the same type but not the same term: register choice, operand order
and strength-reduced forms differ. Comparing their saturations is what makes the
two ladders meet.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-! ## 1. The environment that claims nothing -/

/-- The known-constant environment claiming no constant for any binding of `Γ`.
    Every program whose constants are introduced by its own `regConst` binders
    can start from it: `extendK` discovers those constants as the engine
    descends. -/
def KEnv.unknown : (Γ : Ctxt jasminDialect) → KEnv Γ
  | [] => .nil
  | _ :: Γ => .cons none (KEnv.unknown Γ)

/-- Looking up any variable in `KEnv.unknown` yields no constant. -/
theorem KEnv.lookup_unknown {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ v : Ctxt.Var Γ t, KEnv.lookup v (KEnv.unknown Γ) = none
  | .here => rfl
  | .there v => by
      simp only [KEnv.unknown, KEnv.lookup]
      exact KEnv.lookup_unknown v

/-- `KEnv.unknown` is consistent with every valuation: it makes no claim that
    could fail. -/
theorem KEnv.unknown_consistent {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) : KEnv.Consistent (KEnv.unknown Γ) V := by
  intro w v n hv
  rw [KEnv.lookup_unknown v] at hv
  exact absurd hv (by simp)

/-! ## 2. The certificate -/

/-- **Equal saturations certify equal denotations.** If the bounded engine sends
    `c₁` and `c₂` to the same term under an environment consistent with `V`, the
    two programs denote the same value on `V`. The proof is the two instances of
    `saturateCom_denote` joined by the syntactic equality; nothing about how the
    canonical form was reached enters it. -/
theorem denote_eq_of_saturateCom_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c₁ c₂ : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V)
    (h : saturateCom fuel c₁ k = saturateCom fuel c₂ k) :
    c₁.denote V = c₂.denote V := by
  rw [← saturateCom_denote fuel c₁ k V hk, h, saturateCom_denote fuel c₂ k V hk]

/-- The certificate with the starting environment fixed to `KEnv.unknown`: the
    only remaining hypothesis is the syntactic equality of the two canonical
    forms, which for a concrete pair is decided by evaluation. -/
theorem denote_eq_of_saturateCom_eq_unknown {Γ : Ctxt jasminDialect}
    {t : JasminTy} (fuel : Nat) (c₁ c₂ : Com jasminDialect Γ t)
    (h : saturateCom fuel c₁ (KEnv.unknown Γ)
          = saturateCom fuel c₂ (KEnv.unknown Γ)) (V : Ctxt.Valuation Γ) :
    c₁.denote V = c₂.denote V :=
  denote_eq_of_saturateCom_eq fuel c₁ c₂ (KEnv.unknown Γ) V
    (KEnv.unknown_consistent V) h

/-! ## 3. A worked pair

`Γ1` holds the single input `x`. Each program first binds the constant `0` with
a `regConst` binder, then combines `x` with it. The engine discovers the
constant through `extendK` and fires the identity collapse on both. -/

/-- The one-input context. -/
abbrev Γ1 : Ctxt jasminDialect := [.reg 64]

/-- The zero-constant expression at width 64, in a context extended by one
    binding. -/
def zeroE : Expr jasminDialect Γ1 (.reg 64) :=
  .mk (.regConst 64 0) rfl .nil

/-- `x ⟨bop⟩ 0`, with the constant bound first so it is the second operand:
    `let z = regConst 64 0 in let s = x ⟨bop⟩ z in ret s`. -/
def withZero (bop : JasminBinOp) : Com jasminDialect Γ1 (.reg 64) :=
  .var zeroE
    (.var (.mk (.regArith bop 64) rfl (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- `x + 0` and `x ^^^ 0` saturate to the same term. Both fire the identity
    collapse, which rewrites to `x ||| x` regardless of the original op. -/
theorem addZero_xorZero_saturate_eq :
    saturateCom 1 (withZero .add) (KEnv.unknown Γ1)
      = saturateCom 1 (withZero .xor) (KEnv.unknown Γ1) := by
  rfl

/-- **The worked pair.** `x + 0` and `x ^^^ 0` denote the same function, by the
    certificate alone: the two programs are syntactically different and carry
    different ops, and no `BitVec` identity is invoked here. -/
theorem addZero_xorZero_denote_eq (V : Ctxt.Valuation Γ1) :
    (withZero .add).denote V = (withZero .xor).denote V :=
  denote_eq_of_saturateCom_eq_unknown 1 (withZero .add) (withZero .xor)
    addZero_xorZero_saturate_eq V

/-! ## 4. The negative side

A test that accepted everything would certify nothing. `x * 0` is not `x + 0`,
and the engine's canonical forms differ: the annihilator rewrites to `z &&& z`
where the collapse rewrites to `x ||| x`. -/

/-- The valuation sending the single input to `1`, which separates `x * 0` from
    `x + 0`. -/
def oneV : Ctxt.Valuation Γ1 := .cons (1 : BitVec 64) .nil

/-- `x * 0` at `x = 1` is `0`. -/
theorem withZero_mul_denote_one : (withZero .mul).denote oneV = (0 : BitVec 64) :=
  rfl

/-- `x + 0` at `x = 1` is `1`. -/
theorem withZero_add_denote_one : (withZero .add).denote oneV = (1 : BitVec 64) :=
  rfl

/-- `x * 0` and `x + 0` do not saturate to the same term. Were they equal, the
    certificate would give equal denotations, and the two differ at `x = 1`. -/
theorem mulZero_ne_addZero_saturate :
    saturateCom 1 (withZero .mul) (KEnv.unknown Γ1)
      ≠ saturateCom 1 (withZero .add) (KEnv.unknown Γ1) := by
  intro h
  have hd := denote_eq_of_saturateCom_eq_unknown 1 (withZero .mul) (withZero .add)
    h oneV
  rw [withZero_mul_denote_one, withZero_add_denote_one] at hd
  have hn : (0 : BitVec 64).toNat = (1 : BitVec 64).toNat := congrArg BitVec.toNat hd
  simp at hn

end CatCrypt.Crypto.SecureCompilation.Ascent
