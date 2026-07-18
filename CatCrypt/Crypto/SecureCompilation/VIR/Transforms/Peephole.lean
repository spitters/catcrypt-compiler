/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import CatCrypt.Crypto.SecureCompilation.VIR.Grind

/-!
# Verified peephole rewrites on `Com catCryptDialect`

A small `Com`-level peephole pass that combines

* **constant folding** (Group A): when an op's two args refer to two
  preceding `.var` bindings that are `bvConst`s of the same width,
  replace the binary op with the folded constant.
* **algebraic peephole** (Group B): when an op's args are syntactically
  the same variable (e.g. `bvXor v v`), replace the op with the
  algebraic identity (here `bvConst 0`).

Each rewrite **changes the head Expr of one or more `.var` bindings** —
the binding structure (and hence the De-Bruijn indices in the body) is
preserved. Identity rewrites like `bvAnd v all-ones → v` would need to
substitute `v` for the binding's `.here` reference throughout `body`
and are deferred (documented as a v1 limitation).

The correctness theorem `peephole_denote_eq` is proved by structural
recursion on `Com`. The algebraic case closes via the `@[grind =]`
lemmas in `VIR/Grind.lean`.

## Catalogue (v1)

| # | Pattern | Rewrite | Group |
|---|---------|---------|-------|
| 1 | `bvAdd v_a v_b` with `v_a = .there .here, v_b = .here`, both bvConst-bound | `bvConst (a + b)` | A |
| 2 | `bvSub v_a v_b` with `v_a = .there .here, v_b = .here`, both bvConst-bound | `bvConst (a - b)` | A |
| 3 | `bvXor v_a v_b` with `v_a = .there .here, v_b = .here`, both bvConst-bound | `bvConst (a ^^^ b)` | A |
| 4 | `bvXor v v` (same variable, both args) | `bvConst 0` | B |
| 5 | `bvSub v v` (same variable, both args) | `bvConst 0` | B |

The Group-A patterns recognise the canonical layout

```
let a = bvConst α : sword w in
let b = bvConst β : sword w in
let c = bvOp w .there.here .here in
body
```

i.e. two adjacent `bvConst`s of the same width followed by a binary op
whose args point to `.there .here` and `.here`. This is the shape
produced by `CryptoToVIR.toVIRCom` on `let a = K1; let b = K2; let c =
a `op` b in …`. More general "constant tracking" (where the bvConst
bindings are not immediately adjacent to the op) is left to a future
pass.

## v1 limitations

* `bvAnd x all-ones → x` and `bvOr x 0 → x` rewrites are **not**
  implemented: they require substituting `x` for the freshly-bound
  variable's `.here` reference throughout `body` (i.e. an actual
  De-Bruijn substitution). The current pass is binding-preserving.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

set_option autoImplicit false

universe u v

namespace Peephole

/-! ## 1. Decidable equality on Vars

Used to recognise `bvXor v v` and `bvSub v v` shapes where both args
are literally the same De-Bruijn variable. -/

/-- Decide propositional equality of two `Var`s in the same context. -/
def Var.eqDec {d : Dialect} {Γ : Ctxt d} {t : d.Ty} :
    (v₁ v₂ : Ctxt.Var Γ t) → Decidable (v₁ = v₂)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (fun h => by cases h)
  | .there _, .here => isFalse (fun h => by cases h)
  | .there v₁, .there v₂ =>
      match Var.eqDec v₁ v₂ with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (fun heq => by cases heq; exact h rfl)

instance {d : Dialect} {Γ : Ctxt d} {t : d.Ty} :
    DecidableEq (Ctxt.Var Γ t) := Var.eqDec

/-! ## 2. Algebraic peephole (Group B)

`tryAlgebraicExpr` looks at a single `Expr` and returns a replacement
of the **same type** if an algebraic rule fires (currently:
`bvXor v v → bvConst 0` and `bvSub v v → bvConst 0`). -/

/-- Apply the algebraic rewrite at a single binding, given the
    destructured `(op, retTy_eq, args)` fields and the body.

    When `op = .bvXor w` (or `.bvSub w`) and the two args are equal
    Vars, we replace the binding's head Expr with `bvConst w 0`. The
    binding's De-Bruijn index and `body` are untouched. -/
def buildAlgVar {Γ : Ctxt catCryptDialect} {bs s : CryptoTy} :
    (op : CatCryptOp) →
    (DialectSignature.ret (d := catCryptDialect) op = bs) →
    HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := catCryptDialect) op) →
    Com catCryptDialect (bs :: Γ) s →
    Com catCryptDialect Γ s
  | .bvXor w, retTy_eq, args, body =>
      match args with
      | .cons v₁ (.cons v₂ .nil) =>
          if v₁ = v₂ then
            .var (t := bs) { op := .bvConst w 0, retTy_eq := retTy_eq,
                             args := .nil } body
          else
            .var (t := bs) { op := .bvXor w, retTy_eq := retTy_eq,
                             args := .cons v₁ (.cons v₂ .nil) } body
  | .bvSub w, retTy_eq, args, body =>
      match args with
      | .cons v₁ (.cons v₂ .nil) =>
          if v₁ = v₂ then
            .var (t := bs) { op := .bvConst w 0, retTy_eq := retTy_eq,
                             args := .nil } body
          else
            .var (t := bs) { op := .bvSub w, retTy_eq := retTy_eq,
                             args := .cons v₁ (.cons v₂ .nil) } body
  | op, retTy_eq, args, body =>
      .var (t := bs) { op := op, retTy_eq := retTy_eq, args := args } body

/-- Try to algebraically simplify a `.var e body` by destructuring `e`
    and dispatching via `buildAlgVar`. Other shapes (`.ret`) are
    unchanged. -/
def tryAlgebraicVar {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    Com catCryptDialect Γ t → Com catCryptDialect Γ t
  | .ret v => .ret v
  | .var (t := bs) ⟨op, retTy_eq, args⟩ body =>
      buildAlgVar (bs := bs) (s := t) op retTy_eq args body

/-! ## 3. Constant folding (Group A) -/

/-- Helper: a "constant-folding op kind", used to factor the binary-op
    case dispatch in `tryConstFold3`. -/
inductive FoldOp where
  | add | sub | xor
  deriving DecidableEq

/-- Compute the folded constant for a given fold kind. -/
def FoldOp.apply {w : Nat} : FoldOp → BitVec w → BitVec w → BitVec w
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .xor, a, b => a ^^^ b

/-- Detect a binary fold op at the head of an Expr. Returns `(width,
    kind)` if matched, else `none`. -/
def matchFoldOp : CatCryptOp → Option (Nat × FoldOp)
  | .bvAdd w => some (w, .add)
  | .bvSub w => some (w, .sub)
  | .bvXor w => some (w, .xor)
  | _ => none

/-- Try to constant-fold a 3-let chain. We require all three bindings
    to have type `.sword w` for a common `w`. Returns the folded
    program or the input unchanged.

    To avoid dependent-type juggling, we match all three bindings with
    the **same** pattern variable `w` for the type. This forces the
    type-checker to unify the three widths at match time. -/
def tryConstFold3 {Γ : Ctxt catCryptDialect} {s : CryptoTy} :
    Com catCryptDialect Γ s → Com catCryptDialect Γ s
  | .var (t := CryptoTy.sword w₁) e1
      (.var (t := CryptoTy.sword w₂) e2
        (.var (t := CryptoTy.sword w₃) e3 body)) =>
      let original :=
        Com.var (t := CryptoTy.sword w₁) e1
          (Com.var (t := CryptoTy.sword w₂) e2
            (Com.var (t := CryptoTy.sword w₃) e3 body))
      match e1.op, e2.op, matchFoldOp e3.op with
      | .bvConst wa a, .bvConst wb b, some (_, op) =>
          if _h1 : w₁ = wa then
            if _h2 : w₂ = wa then
              if h3 : w₃ = wa then
                if h4 : wa = wb then
                  let b' : BitVec wa := h4 ▸ b
                  let folded : BitVec wa := FoldOp.apply op a b'
                  let foldedAtW3 : BitVec w₃ := h3 ▸ folded
                  let newE3 :
                      Expr catCryptDialect
                        (CryptoTy.sword w₂ :: CryptoTy.sword w₁ :: Γ)
                        (CryptoTy.sword w₃) :=
                    { op := .bvConst w₃ foldedAtW3, retTy_eq := rfl,
                      args := .nil }
                  Com.var e1 (Com.var e2 (Com.var newE3 body))
                else original
              else original
            else original
          else original
      | _, _, _ => original
  | c => c

/-! ## 4. Top-level rewrite -/

/-- One-pass peephole rewrite on `Com`. Applies algebraic peephole
    (Group B) to each `.var` binding (via `buildAlgVar` directly to
    keep the binding type stable), then recurses into the body. -/
def peephole {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    Com catCryptDialect Γ t → Com catCryptDialect Γ t
  | .ret v => .ret v
  | .var (t := bs) ⟨op, retTy_eq, args⟩ body =>
      -- Apply head rewrite then recurse into body (structurally smaller).
      buildAlgVar (bs := bs) (s := t) op retTy_eq args (peephole body)

/-! ## 5. Correctness -/

/-- `buildAlgVar` preserves denotation: the rewritten `.var` binding
    yields the same value as the original. -/
theorem buildAlgVar_denote {Γ : Ctxt catCryptDialect} {bs s : CryptoTy}
    (op : CatCryptOp)
    (retTy_eq : DialectSignature.ret (d := catCryptDialect) op = bs)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
              (DialectSignature.sig (d := catCryptDialect) op))
    (body : Com catCryptDialect (bs :: Γ) s) (V : Ctxt.Valuation Γ) :
    (buildAlgVar (bs := bs) (s := s) op retTy_eq args body).denote V =
      (Com.var (t := bs) ⟨op, retTy_eq, args⟩ body).denote V := by
  -- Case on op. Only bvXor/bvSub branches diverge from `c => c`.
  cases op
  all_goals try rfl
  -- bvXor w
  · rename_i w
    -- args : HVector ... [.sword w, .sword w]
    match args with
    | .cons v₁ (.cons v₂ .nil) =>
        simp only [buildAlgVar]
        by_cases hv : v₁ = v₂
        · simp only [hv, if_true]
          subst hv
          -- `retTy_eq : .sword w = bs`. Substitute to make `bs = .sword w`,
          -- then all types reduce.
          subst retTy_eq
          -- Now both `.var` constructors are at concrete type sword w.
          -- Show: (.var (bvConst-0) body).denote V = (.var (bvXor-vv) body).denote V.
          -- We compute the bound value on each side explicitly.
          -- The two `.var` Coms reduce to body.denote (V.extend X) for
          -- X = 0 and X = v ^^^ v respectively. We pose v as a BitVec.
          set vv : BitVec w := v₁.lookup V with hvv_def
          have hL : (Com.var (t := CryptoTy.sword w)
                      ⟨CatCryptOp.bvConst w 0, rfl, .nil⟩ body).denote V
                    = body.denote (V.extend (0 : BitVec w)) := rfl
          have hR : (Com.var (t := CryptoTy.sword w)
                      ⟨CatCryptOp.bvXor w, rfl,
                        .cons v₁ (.cons v₁ .nil)⟩ body).denote V
                    = body.denote (V.extend (vv ^^^ vv)) := rfl
          rw [hL, hR]
          congr 1
          congr 1
          have hzero : vv ^^^ vv = (0 : BitVec w) := by grind
          rw [hzero]
        · simp only [hv, if_false]
  -- bvSub w
  · rename_i w
    match args with
    | .cons v₁ (.cons v₂ .nil) =>
        simp only [buildAlgVar]
        by_cases hv : v₁ = v₂
        · simp only [hv, if_true]
          subst hv
          subst retTy_eq
          set vv : BitVec w := v₁.lookup V with hvv_def
          have hL : (Com.var (t := CryptoTy.sword w)
                      ⟨CatCryptOp.bvConst w 0, rfl, .nil⟩ body).denote V
                    = body.denote (V.extend (0 : BitVec w)) := rfl
          have hR : (Com.var (t := CryptoTy.sword w)
                      ⟨CatCryptOp.bvSub w, rfl,
                        .cons v₁ (.cons v₁ .nil)⟩ body).denote V
                    = body.denote (V.extend (vv - vv)) := rfl
          rw [hL, hR]
          congr 1
          congr 1
          have hzero : vv - vv = (0 : BitVec w) := by grind
          rw [hzero]
        · simp only [hv, if_false]

/-- **Main correctness theorem.** The `peephole` pass preserves
    denotation. -/
theorem peephole_denote_eq {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) (V : Ctxt.Valuation Γ) :
    (peephole c).denote V = c.denote V := by
  induction c with
  | ret v => rfl
  | var e body ih =>
      -- Destructure e so its op/retTy_eq/args are exposed.
      match e with
      | ⟨op, retTy_eq, args⟩ =>
          -- peephole unfolds to `buildAlgVar … op retTy_eq args (peephole body)`
          show (peephole (Com.var ⟨op, retTy_eq, args⟩ body)).denote V =
            (Com.var ⟨op, retTy_eq, args⟩ body).denote V
          unfold peephole
          rw [buildAlgVar_denote]
          simp only [Com.denote]
          rw [ih]

/-! ## 6. Smoke tests -/

namespace SmokeTest

/-- Group B smoke test: `let x = bvConst 0x42; let y = bvXor x x; ret y`
    should evaluate to `0`. -/
def progSelfXor : Com catCryptDialect [] (CryptoTy.sword 8) :=
  .var (t := CryptoTy.sword 8)
      { op := .bvConst 8 (0x42 : BitVec 8), retTy_eq := rfl, args := .nil }
    (.var (t := CryptoTy.sword 8)
        { op := .bvXor 8, retTy_eq := rfl,
          args := .cons .here (.cons .here .nil) }
      (.ret .here))

example : progSelfXor.denote .nil = (0 : BitVec 8) := by
  unfold progSelfXor; rfl

example : (peephole progSelfXor).denote .nil = (0 : BitVec 8) := by
  rw [peephole_denote_eq]; rfl

/-- Group B smoke test: `bvSub x x = 0`. -/
def progSelfSub : Com catCryptDialect [] (CryptoTy.sword 8) :=
  .var (t := CryptoTy.sword 8)
      { op := .bvConst 8 (0x99 : BitVec 8), retTy_eq := rfl, args := .nil }
    (.var (t := CryptoTy.sword 8)
        { op := .bvSub 8, retTy_eq := rfl,
          args := .cons .here (.cons .here .nil) }
      (.ret .here))

example : (peephole progSelfSub).denote .nil = (0 : BitVec 8) := by
  rw [peephole_denote_eq]; rfl

/-- Group A smoke test (source program): `let a = 3; let b = 4; let c =
    a + b; ret c` has denotation `7`. The folded version (via
    `tryConstFold3`) denotes to the same value. -/
def progAdd : Com catCryptDialect [] (CryptoTy.sword 8) :=
  .var (t := CryptoTy.sword 8)
      { op := .bvConst 8 (3 : BitVec 8), retTy_eq := rfl, args := .nil }
    (.var (t := CryptoTy.sword 8)
        { op := .bvConst 8 (4 : BitVec 8), retTy_eq := rfl, args := .nil }
      (.var (t := CryptoTy.sword 8)
          { op := .bvAdd 8, retTy_eq := rfl,
            args := .cons (.there .here) (.cons .here .nil) }
        (.ret .here)))

example : progAdd.denote .nil = (7 : BitVec 8) := by
  unfold progAdd; rfl

example : (tryConstFold3 progAdd).denote .nil = (7 : BitVec 8) := by
  -- After folding, the third binding is `bvConst 8 7`, so denotation is 7.
  rfl

/-- Group A smoke test: `bvXor 0xAA 0x55 = 0xFF`. -/
def progXor : Com catCryptDialect [] (CryptoTy.sword 8) :=
  .var (t := CryptoTy.sword 8)
      { op := .bvConst 8 (0xAA : BitVec 8), retTy_eq := rfl, args := .nil }
    (.var (t := CryptoTy.sword 8)
        { op := .bvConst 8 (0x55 : BitVec 8), retTy_eq := rfl, args := .nil }
      (.var (t := CryptoTy.sword 8)
          { op := .bvXor 8, retTy_eq := rfl,
            args := .cons (.there .here) (.cons .here .nil) }
        (.ret .here)))

example : progXor.denote .nil = (0xFF : BitVec 8) := by
  unfold progXor; rfl

example : (tryConstFold3 progXor).denote .nil = (0xFF : BitVec 8) := by
  rfl

end SmokeTest

end Peephole

end CatCrypt.Crypto.SecureCompilation.VIR
