/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Egraph
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

/-!
# Verified local peephole rewrite pass for `Com`

A structural `Com → Com` peephole pass over the typed VIR
`jasminDialect`, complementary to the bounded equality-saturation engine in
`Egraph.lean`. Where the egraph pass fires *algebraic* rules that depend on a
known-constant operand, the peephole pass fires *purely local, syntactic*
patterns: two-address / addressing-mode-friendly cleanups (cf the linear-jasmin
two-address discipline) and identity collapses that need no constant
analysis — only that two argument variables are syntactically equal.

Like the egraph pass, the rewrite is at the `Expr` level (context- and
return-type-preserving), lifted homomorphically over `Com`. Each pattern carries
a `BitVec`-identity soundness lemma; denotation preservation for the
whole `Com` is an induction (**not** `rfl`).

## The peephole pattern set

Operating on `Expr jasminDialect Γ (.reg w)` whose two `regArith` arguments are
the *same* variable `a` (detected syntactically via `varEq`):

* **self-subtract → zeroing idiom** (`sub a a ↦ xor a a`): the classic x86
  `xor reg, reg` zeroing peephole — `a - a = a ^^^ a = 0`, and `xor reg,reg` is
  the canonical, encoding-friendly zeroing form. Soundness: `sub_self_eq_xor`.
* **idempotent-and → idempotent-or** (`and a a ↦ or a a`): canonicalises the two
  equal idempotent copies to a single form. `a &&& a = a ||| a = a`.
  Soundness: `and_self_eq_or`.

Both are redundant-move / identity cleanups: each takes a binder that is really a
copy or a zero and rewrites it to its canonical encoding-friendly form, without
disturbing De Bruijn indices (the rewrite reuses the same argument variable `a`).

## Preservation theorems

* `peepExpr_denote` : per-Expr denotation equality (real BitVec algebra,
  conditioned on the syntactic equality witnessed by `varEq`).
* `peepCom_denote`  : `(peepCom c).denote V = c.denote V`, by induction over the
  `Com` let-chain. **Not `rfl`.**
* `peepCom_ctSafe`  : CT preservation (dialect is branch-free).
* `peepCom_cost_le` : cost-non-increasing.

All goals closed. Axiom set: `propext`, `Quot.sound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.Peephole

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-! ## 1. Syntactic variable equality

`Ctxt.Var` has no `DecidableEq` instance. The Boolean equality test and its soundness,
by which the peephole patterns detect that both operands are the same variable, are the
dialect-generic `AegraphGeneric.varEq` and `AegraphGeneric.varEq_sound` at
`jasminDialect`. -/

/-- Boolean equality of two De Bruijn variables of the same type: `AegraphGeneric.varEq`
    at `jasminDialect`. -/
def varEq {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Ctxt.Var Γ t → Ctxt.Var Γ t → Bool :=
  AegraphGeneric.varEq

/-- `varEq a b = true` implies `a = b`. -/
theorem varEq_sound {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (a b : Ctxt.Var Γ t), varEq a b = true → a = b :=
  AegraphGeneric.varEq_sound

/-! ## 2. Soundness of the BitVec identities -/

/-- `a - a = a ^^^ a` (both `0`): the zeroing-idiom canonicalisation. -/
theorem sub_self_eq_xor {w : Nat} (x : BitVec w) : x - x = x ^^^ x := by simp

/-- `a &&& a = a ||| a` (both `a`): idempotent-copy canonicalisation. -/
theorem and_self_eq_or {w : Nat} (x : BitVec w) : x &&& x = x ||| x := by simp

/-! ## 3. The `Expr`-level peephole rewrite -/

/-- Rewrite a binary `regArith` whose two operands are the *same* variable.
Returns `none` if no pattern matches. -/
def peepBin {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) :
    Option (Expr jasminDialect Γ (.reg w)) :=
  if varEq a b then
    match bop with
    | .sub => some (binE .xor a b)  -- a - a ↦ a ^^^ a  (zeroing idiom)
    | .and => some (binE .or a b)   -- a &&& a ↦ a ||| a (idempotent copy)
    | _    => none
  else none

/-- **Soundness of `peepBin`.** Any expression `peepBin` produces denotes the
same value as the original `binE bop a b`. A `BitVec`-algebra proof
(using the syntactic `a = b` from `varEq`), **not** `rfl`. -/
theorem peepBin_sound {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) (V : Ctxt.Valuation Γ)
    (e' : Expr jasminDialect Γ (.reg w))
    (he : peepBin bop a b = some e') :
    e'.denote V = (binE bop a b).denote V := by
  unfold peepBin at he
  by_cases hv : varEq a b
  · -- a = b
    have hab : a = b := varEq_sound a b hv
    subst hab
    simp only [hv, if_true] at he
    cases bop <;>
      first
        | (injection he with he; subst he;
           simp only [binE_denote, JasminBinOp.apply]; simp)
        | simp at he
  · simp only [hv, Bool.false_eq_true, if_false] at he
    exact absurd he (by simp)

/-- Apply the peephole at one expression. Identity unless the expression is a
binary `regArith` over `reg w` whose two operands are equal and match a pattern. -/
def peepExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Expr jasminDialect Γ t :=
  match e with
  | ⟨.regArith bop w, hop, args⟩ =>
      let a : Ctxt.Var Γ (.reg w) := args.head
      let b : Ctxt.Var Γ (.reg w) := args.tail.head
      match peepBin bop a b with
      | some e' => hop ▸ e'
      | none    => ⟨.regArith bop w, hop, args⟩
  | e => e

/-- **Denotation preservation for `peepExpr`.** -/
theorem peepExpr_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (peepExpr e).denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [peepExpr, HVector.head, HVector.tail]
        rcases hr : peepBin bop a b with _ | e'
        · simp
        · rw [peepBin_sound bop a b V e' hr]; rfl
  | stackLoad w n => simp [peepExpr]
  | stackStore w n => simp [peepExpr]
  | castW w w' => simp [peepExpr]
  | extCall nm a r => simp [peepExpr]
  | regConst w n => simp [peepExpr]
  | vpackZMM bop => simp [peepExpr]
  | vpackZMMd bop => simp [peepExpr]
  | vprordZMM n => simp [peepExpr]
  | vpslldq n => simp [peepExpr]
  | vpsrldq n => simp [peepExpr]
  | vsimd op => simp [peepExpr]
  | vymm op => simp [peepExpr]
  | mulhi w => simp [peepExpr]
  | addCarryLo w => simp [peepExpr]
  | addCarryHi w => simp [peepExpr]
  | rorImm w n => simp [peepExpr]
  | shrImm w n => simp [peepExpr]
  | sarImm w n => simp [peepExpr]
  | shlImm w n => simp [peepExpr]
  | select w => simp [peepExpr]
  | callN name argTys retTys => simp [peepExpr]
  | cmp c w => simp [peepExpr]
  | cmpImm c w n => simp [peepExpr]

/-! ## 4. Cost non-increase of `peepExpr`

`sub`/`and` (cost 1) are replaced by `xor`/`or` (cost 1), so cost is preserved.
We state the `≤` form for uniformity with the egraph pass. -/

/-- `peepBin` never increases op cost. -/
theorem peepBin_cost_le {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w))
    (e' : Expr jasminDialect Γ (.reg w))
    (he : peepBin bop a b = some e') :
    opCost e'.op ≤ opCost (JasminOp.regArith bop w) := by
  unfold peepBin at he
  by_cases hv : varEq a b
  · simp only [hv, if_true] at he
    cases bop <;>
      first
        | (injection he with he; subst he; simp [opCost, binE])
        | simp at he
  · simp only [hv, Bool.false_eq_true, if_false] at he
    exact absurd he (by simp)

/-- `peepExpr` never increases op cost. -/
theorem peepExpr_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) :
    opCost (peepExpr e).op ≤ opCost e.op := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [peepExpr, HVector.head, HVector.tail]
        rcases hr : peepBin bop a b with _ | e'
        · simp
        · exact peepBin_cost_le bop a b e' hr
  | stackLoad w n => simp [peepExpr]
  | stackStore w n => simp [peepExpr]
  | castW w w' => simp [peepExpr]
  | extCall nm a r => simp [peepExpr]
  | regConst w n => simp [peepExpr]
  | vpackZMM bop => simp [peepExpr]
  | vpackZMMd bop => simp [peepExpr]
  | vprordZMM n => simp [peepExpr]
  | vpslldq n => simp [peepExpr]
  | vpsrldq n => simp [peepExpr]
  | vsimd op => simp [peepExpr]
  | vymm op => simp [peepExpr]
  | mulhi w => simp [peepExpr]
  | addCarryLo w => simp [peepExpr]
  | addCarryHi w => simp [peepExpr]
  | rorImm w n => simp [peepExpr]
  | shrImm w n => simp [peepExpr]
  | sarImm w n => simp [peepExpr]
  | shlImm w n => simp [peepExpr]
  | select w => simp [peepExpr]
  | callN name argTys retTys => simp [peepExpr]
  | cmp c w => simp [peepExpr]
  | cmpImm c w n => simp [peepExpr]

/-! ## 5. The `Com`-level peephole pass

`peepCom` rewrites every let-bound expression with `peepExpr`, descending into
the body. It is purely local — no env threading, since the patterns are
syntactic (no constant lookup). It is therefore a single bounded pass; iterating
it is idempotent for this pattern set. -/

/-- One peephole pass over a `Com`. -/
def peepCom {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | .ret v => .ret v
  | .var e body => .var (peepExpr e) (peepCom body)

/-- **Denotation preservation for the peephole pass.** `peepCom c` denotes the
same function as `c`. By induction over the `Com` let-chain — **not** `rfl`. -/
theorem peepCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      (peepCom c).denote V = c.denote V
  | .ret v, _ => rfl
  | .var e body, V => by
      simp only [peepCom, Com.denote]
      rw [peepExpr_denote e V]
      exact peepCom_denote body (V.extend (e.denote V))

/-! ## 6. CT preservation -/

/-- **CT preservation for the peephole pass.** The dialect is branch-free, so
both the input and the rewritten `Com` are CT-safe. -/
theorem peepCom_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) :
    ctSafeComJ (peepCom c) = ctSafeComJ c := by
  rw [ctSafeComJ_true (peepCom c), ctSafeComJ_true c]

/-! ## 7. Cost non-increase -/

/-- **The peephole pass is cost-non-increasing.** -/
theorem peepCom_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t), comCost (peepCom c) ≤ comCost c
  | .ret _ => Nat.le_refl _
  | .var e body => by
      simp only [peepCom, comCost]
      have h1 : opCost (peepExpr e).op ≤ opCost e.op := peepExpr_cost_le e
      have h2 : comCost (peepCom body) ≤ comCost body := peepCom_cost_le body
      omega

/-! ## 8. Self-contained validation

A small `Com jasminDialect [reg 32] (reg 32)` exercising the peephole:

    let z = x - x      -- a self-subtract (a redundant zeroing)
    ret z

The peephole rewrites `x - x` to the `xor x x` zeroing idiom (a redundant-move /
encoding-friendly cleanup). We check the denotation is preserved (both map any
`x` to `0`) and the rewrite is non-increasing in cost. We also exercise the
idempotent-and canonicalisation `x & x ↦ x | x`. -/

/-- The self-subtract demo: `x ↦ x - x`. -/
def demoSelfSub : Com jasminDialect [.reg 32] (.reg 32) :=
  -- z = x - x.  x is `.here` in context `[reg 32]`.
  .var (binE .sub .here .here)
    (.ret .here)

/-- **The peephole rewrites the `sub` site to a `xor` zeroing idiom.** The
rewritten binder is `xor x x` (the canonical zeroing form). -/
example : peepCom demoSelfSub =
    Com.var (binE .xor (Ctxt.Var.here) (Ctxt.Var.here)) (.ret .here) := by
  rfl

/-- **Denotation preserved.** The rewritten program denotes the same function as
the input — both map `x` to `0`. Via `peepCom_denote`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (peepCom demoSelfSub).denote V = demoSelfSub.denote V :=
  peepCom_denote demoSelfSub V

/-- Concretely, on `x = 42`, both denote `0`. -/
example : demoSelfSub.denote (.cons (42 : BitVec 32) .nil) = (0 : BitVec 32) := rfl

example :
    (peepCom demoSelfSub).denote (.cons (42 : BitVec 32) .nil) = (0 : BitVec 32) :=
  rfl

/-- **Cost non-increasing.** -/
example : comCost (peepCom demoSelfSub) ≤ comCost demoSelfSub :=
  peepCom_cost_le demoSelfSub

/-- **CT preserved on the demo.** -/
example : ctSafeComJ (peepCom demoSelfSub) = ctSafeComJ demoSelfSub :=
  peepCom_ctSafe demoSelfSub

/-- The idempotent-and demo: `x ↦ x & x`. -/
def demoSelfAnd : Com jasminDialect [.reg 32] (.reg 32) :=
  .var (binE .and .here .here) (.ret .here)

/-- The peephole canonicalises `x & x` to `x | x`. -/
example : peepCom demoSelfAnd =
    Com.var (binE .or (Ctxt.Var.here) (Ctxt.Var.here)) (.ret .here) := by
  rfl

/-- Denotation preserved for the idempotent-and demo (both map `x` to `x`). -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (peepCom demoSelfAnd).denote V = demoSelfAnd.denote V :=
  peepCom_denote demoSelfAnd V

example : demoSelfAnd.denote (.cons (42 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

/-! ## 9. Composition with the egraph pass

The two passes compose: run the peephole, then the egraph engine (or vice
versa); denotation and CT-safety are preserved by transitivity of the
individual preservation theorems. -/

/-- **Composed denotation preservation.** Peephole then egraph saturation
preserves denotation, given a consistent known-constant env. -/
theorem peep_then_saturate_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    (saturateCom fuel (peepCom c) k).denote V = c.denote V := by
  rw [saturateCom_denote fuel (peepCom c) k V hk, peepCom_denote c V]

/-- **Composed CT preservation.** -/
theorem peep_then_saturate_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    ctSafeComJ (saturateCom fuel (peepCom c) k) = ctSafeComJ c := by
  rw [saturateCom_ctSafe fuel (peepCom c) k, peepCom_ctSafe c]

end CatCrypt.Crypto.Optimizer.Rewrite.Peephole
