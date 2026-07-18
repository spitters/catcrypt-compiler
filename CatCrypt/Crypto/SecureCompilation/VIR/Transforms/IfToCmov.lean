/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CTPredicate
import CatCrypt.Crypto.SecureCompilation.VIR.Grind
import CatCrypt.Crypto.SecureCompilation.VIR.Regions

/-!
# `if`-to-`cmov` rewriter on `ComR catCryptDialect`

This file implements the load-bearing constant-time mitigation for VIR:
a verified rewrite that turns a `Secret`-tagged `ifBit` conditional
(which `ctSafeComR` rejects) into a branch-free arithmetic chain
(which `ctSafeComR` accepts).

## Scope (v2)

We handle **two** value-shaped rewrites; both arms of the `ifBit` must
be `.ret` of a variable.

For `t = .bit`, we emit the standard branch-free bit `cmov`:

```
ifBit c .Secret (.ret a) (.ret b)   -- a, b : Var Γ .bit
  ↦   let nc  = not c
      let ca  = and c a
      let ncb = and nc b
      let r   = or ca ncb
      ret r
```

For `t = .sword n`, we emit the standard mask-based cmov, using the
`bitToSword n` op (added in `CatCryptDialect.lean`) as the mask source.
`bitToSword n c` denotes `if c then allOnes n else 0`, so

```
ifBit c .Secret (.ret a) (.ret b)   -- a, b : Var Γ (.sword n)
  ↦   let ec  = bitToSword n c
      let nec = bvNot n ec
      let lhs = bvAnd n ec a
      let rhs = bvAnd n nec b
      let r   = bvOr n lhs rhs
      ret r
```

This is the common case in real CT crypto code: constant-time selects
on 64-bit limbs, scalar reduction, point conditional swap, etc.

All other shapes (nested `ComR` arms, sum/pair/memref returns) are
returned unchanged. Lifting full sub-programs into a single context
is follow-up work.

## What this file provides

1. `cmovBit` — the four-op branch-free `ComR` chain.
2. `ifToCmov` — the (total) rewrite, returning the input for any shape
   we don't handle.
3. `ifToCmov_denote_eq` — denotation is preserved.
4. `ifToCmov_makes_bit_secret_ifBits_ctSafe` — for the value-shaped
   bit case, the rewrite produces a CT-safe program.
5. `ifToCmov_ctSafe_or_unchanged` — global non-decrease of CT-safety.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR
namespace Transforms

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
  (CatCryptOp catCryptDialect catCryptDenote)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. The branch-free `cmov` chain for `.bit`

We construct `ComR catCryptDialect Γ .bit` representing
`(c ∧ a) ∨ (¬c ∧ b)` as a 4-let chain. Variables are encoded via De
Bruijn indices: each `var` push shifts old names by one `.there`. -/

/-- Branch-free cmov on a single bit: `(c ∧ a) ∨ (¬c ∧ b)`.

    Encoded as a 4-step let-chain inside `ComR`. The result is
    region-free (no `ifBit` nodes), so `ctSafeComR` accepts it. -/
def cmovBit {Γ : Ctxt catCryptDialect}
    (c a b : Ctxt.Var Γ .bit) : ComR catCryptDialect Γ .bit :=
  -- Step 1: nc = not c        (binding at .here in (.bit :: Γ))
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.not, retTy_eq := rfl,
      args := .cons c .nil } <|
  -- Step 2: ca = and c a      (binding at .here in (.bit :: .bit :: Γ))
  -- After step 1, original Γ-vars need one .there shift.
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.and, retTy_eq := rfl,
      args := .cons (.there c) (.cons (.there a) .nil) } <|
  -- Step 3: ncb = and nc b    (binding at .here in (.bit :: .bit :: .bit :: Γ))
  -- nc was .here in step 1's body; in step 3's expression context
  -- (.bit :: .bit :: Γ) it is .there .here. b needs two .there shifts.
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.and, retTy_eq := rfl,
      args := .cons (.there .here)
                    (.cons (.there (.there b)) .nil) } <|
  -- Step 4: r = or ca ncb     (binding at .here in (.bit ::… :: Γ))
  -- ca is .there .here; ncb is .here.
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.or, retTy_eq := rfl,
      args := .cons (.there .here) (.cons .here .nil) } <|
  -- Return the freshly-bound `r`.
  ComR.ret .here

/-! ## 2. Denotation of `cmovBit`

Every step of `cmovBit`'s chain is a single op (`not`/`and`/`or`) on
variables with `retTy_eq := rfl`. Both `ComR.denote` and `Expr.denote`
reduce definitionally on these shapes, so the whole chain computes to
`(c && a) || (!c && b)` by `rfl`. Case-splitting on the three bits
gives `if c then a else b`. -/

/-- Compute `cmovBit c a b`'s denotation directly to the branch-free
    Boolean expression. Everything reduces by `rfl`. -/
private theorem cmovBit_denote_compute {Γ : Ctxt catCryptDialect}
    (c a b : Ctxt.Var Γ .bit) (V : Ctxt.Valuation Γ) :
    (cmovBit c a b).denote V =
      ((c.lookup V && a.lookup V) || (!(c.lookup V) && b.lookup V)) := by
  rfl

/-- `cmovBit` computes the standard branch-free conditional move on bits:
    `if c then a else b`. -/
@[simp] theorem cmovBit_denote {Γ : Ctxt catCryptDialect}
    (c a b : Ctxt.Var Γ .bit) (V : Ctxt.Valuation Γ) :
    (cmovBit c a b).denote V =
      (if c.lookup V then a.lookup V else b.lookup V) := by
  rw [cmovBit_denote_compute]
  cases c.lookup V <;> cases a.lookup V <;> cases b.lookup V <;> rfl

/-! ## 2b. The branch-free `cmov` chain for `.sword n`

The `.sword n` cmov uses the standard mask pattern:
`(extend c &&& a) ||| (~~~ extend c &&& b)`. Encoded as a 5-let chain.

Variable shifts under the chain (Γ at depth 0):
- Step 1 binds `ec` at depth 1 (.here in (.sword n :: Γ)).
- Step 2 binds `nec`: `ec` is at `.there .here` in step 2's expression
  context (which is .sword n :: Γ), but wait — step 2 lives in
  (.sword n :: Γ) since we've added one binding. `ec` is `.here`. The
  result of step 2 binds in (.sword n :: .sword n :: Γ).
- Step 3 binds `lhs = ec &&& a`: `ec` is `.there .here` (under step-2's
  push), `a` is shifted by 2 (`.there (.there a)`).
- Step 4 binds `rhs = nec &&& b`: `nec` is `.there .here` (under
  step-3's push), `b` is shifted by 3 (`.there³ b`).
- Step 5 binds `r = lhs ||| rhs`: `lhs` is `.there .here`, `rhs` is
  `.here`.
- Return `.here` (the freshly-bound `r`). -/

/-- Branch-free cmov on `.sword n`: `(extend c &&& a) ||| (~~~ extend c &&& b)`.

    Encoded as a 5-step let-chain inside `ComR`. The result is region-
    free (no `ifBit` nodes), so `ctSafeComR` accepts it. -/
def cmovSword {Γ : Ctxt catCryptDialect} {n : Nat}
    (c : Ctxt.Var Γ .bit) (a b : Ctxt.Var Γ (.sword n)) :
    ComR catCryptDialect Γ (.sword n) :=
  -- Step 1: ec = bitToSword n c
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.bitToSword n, retTy_eq := rfl,
      args := .cons c .nil } <|
  -- Step 2: nec = bvNot n ec       (ec at .here)
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.bvNot n, retTy_eq := rfl,
      args := .cons .here .nil } <|
  -- Step 3: lhs = bvAnd n ec a     (ec at .there .here; a shifted by 2)
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.bvAnd n, retTy_eq := rfl,
      args := .cons (.there .here)
                    (.cons (.there (.there a)) .nil) } <|
  -- Step 4: rhs = bvAnd n nec b    (nec at .there .here; b shifted by 3)
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.bvAnd n, retTy_eq := rfl,
      args := .cons (.there .here)
                    (.cons (.there (.there (.there b))) .nil) } <|
  -- Step 5: r = bvOr n lhs rhs     (lhs at .there .here; rhs at .here)
  ComR.var (d := catCryptDialect)
    { op := CatCryptOp.bvOr n, retTy_eq := rfl,
      args := .cons (.there .here) (.cons .here .nil) } <|
  ComR.ret .here

/-- Compute `cmovSword c a b`'s denotation directly to the branch-free
    BitVec expression. Everything reduces by `rfl`. -/
private theorem cmovSword_denote_compute {Γ : Ctxt catCryptDialect} {n : Nat}
    (c : Ctxt.Var Γ .bit) (a b : Ctxt.Var Γ (.sword n))
    (V : Ctxt.Valuation Γ) :
    (cmovSword c a b).denote V =
      (((if c.lookup V then BitVec.allOnes n else 0) &&& a.lookup V)
        ||| ((~~~ (if c.lookup V then BitVec.allOnes n else 0)) &&& b.lookup V)) := by
  rfl

/-- `cmovSword` computes the standard branch-free conditional move on
    `.sword n`: `if c then a else b`. -/
@[simp] theorem cmovSword_denote {Γ : Ctxt catCryptDialect} {n : Nat}
    (c : Ctxt.Var Γ .bit) (a b : Ctxt.Var Γ (.sword n))
    (V : Ctxt.Valuation Γ) :
    (cmovSword c a b).denote V =
      (if c.lookup V then a.lookup V else b.lookup V) := by
  rw [cmovSword_denote_compute]
  -- Case-split on the Boolean and let BitVec arithmetic close each side.
  -- The `Bool`-valued `if` reduces on the constructors.
  rcases c.lookup V with _ | _
  · -- c = false: 0 &&& a ||| ~~~0 &&& b = b
    show (0#n &&& a.lookup V) ||| ((~~~ (0#n : BitVec n)) &&& b.lookup V)
          = b.lookup V
    rw [BitVec.not_zero, BitVec.zero_and, BitVec.allOnes_and, BitVec.zero_or]
  · -- c = true: allOnes &&& a ||| ~~~allOnes &&& b = a
    show ((BitVec.allOnes n) &&& a.lookup V)
          ||| ((~~~ (BitVec.allOnes n)) &&& b.lookup V) = a.lookup V
    rw [BitVec.not_allOnes, BitVec.allOnes_and, BitVec.zero_and, BitVec.or_zero]

/-! ## 3. The rewriter

`ifToCmov` matches the *exact* value-shaped Secret-tagged `ifBit` pattern
on both `.bit` and `.sword n` returns and rewrites it; otherwise it
returns the input.

Implementation: we go via per-type auxiliaries. The top-level wrapper
dispatches on `t` and on the input's constructor shape, falling through
to the identity in every case we don't recognise. -/

/-- Inner helper: rewrite a bit-typed `ComR` *if* it is the exact
    value-shaped `Secret`-tagged `ifBit`. Otherwise return the input. -/
def ifToCmovBit {Γ : Ctxt catCryptDialect} :
    ComR catCryptDialect Γ .bit → ComR catCryptDialect Γ .bit
  | ComR.ifBit cond .Secret (ComR.ret a) (ComR.ret b) =>
      cmovBit cond a b
  | c => c

/-- Inner helper: rewrite a `.sword n`-typed `ComR` *if* it is the exact
    value-shaped `Secret`-tagged `ifBit`. Otherwise return the input. -/
def ifToCmovSword {Γ : Ctxt catCryptDialect} {n : Nat} :
    ComR catCryptDialect Γ (.sword n) → ComR catCryptDialect Γ (.sword n)
  | ComR.ifBit cond .Secret (ComR.ret a) (ComR.ret b) =>
      cmovSword cond a b
  | c => c

/-- Top-level rewrite. Dispatches on the return type: `.bit` and
    `.sword n` are handled; all other types are identity. -/
def ifToCmov {Γ : Ctxt catCryptDialect} : {t : CryptoTy} →
    ComR catCryptDialect Γ t → ComR catCryptDialect Γ t
  | .bit, c => ifToCmovBit c
  | .unit, c => c
  | .pair _ _, c => c
  | .sum _ _, c => c
  | .sword _, c => ifToCmovSword c
  | .memref _, c => c

/-! ## 4. Denotational correctness -/

/-- `ifToCmovBit` preserves the pure denotation. -/
theorem ifToCmovBit_denote_eq {Γ : Ctxt catCryptDialect}
    (c : ComR catCryptDialect Γ .bit) (V : Ctxt.Valuation Γ) :
    (ifToCmovBit c).denote V = c.denote V := by
  -- The only non-trivial case is the value-shaped `Secret`-tagged `ifBit`.
  match c with
  | ComR.ret _ => rfl
  | ComR.var _ _ => rfl
  | ComR.ifBit _ .Public _ _ => rfl
  | ComR.ifBit _ .Secret (ComR.var _ _) _ => rfl
  | ComR.ifBit _ .Secret (ComR.ifBit ..) _ => rfl
  | ComR.ifBit _ .Secret (ComR.ret _) (ComR.var _ _) => rfl
  | ComR.ifBit _ .Secret (ComR.ret _) (ComR.ifBit ..) => rfl
  | ComR.ifBit cond .Secret (ComR.ret a) (ComR.ret b) =>
      -- `ifToCmovBit` rewrote this to `cmovBit cond a b`.
      show (cmovBit cond a b).denote V = _
      rw [cmovBit_denote]
      -- The RHS is `(ifBit cond _ (ret a) (ret b)).denote V`, which
      -- unfolds to `if HasBoolBit.toBool (cond.lookup V) then a.lookup V
      -- else b.lookup V`. For `catCryptDialect`, `HasBoolBit.toBool = id`.
      rfl

/-- `ifToCmovSword` preserves the pure denotation. -/
theorem ifToCmovSword_denote_eq {Γ : Ctxt catCryptDialect} {n : Nat}
    (c : ComR catCryptDialect Γ (.sword n)) (V : Ctxt.Valuation Γ) :
    (ifToCmovSword c).denote V = c.denote V := by
  -- The only non-trivial case is the value-shaped `Secret`-tagged `ifBit`.
  match c with
  | ComR.ret _ => rfl
  | ComR.var _ _ => rfl
  | ComR.ifBit _ .Public _ _ => rfl
  | ComR.ifBit _ .Secret (ComR.var _ _) _ => rfl
  | ComR.ifBit _ .Secret (ComR.ifBit ..) _ => rfl
  | ComR.ifBit _ .Secret (ComR.ret _) (ComR.var _ _) => rfl
  | ComR.ifBit _ .Secret (ComR.ret _) (ComR.ifBit ..) => rfl
  | ComR.ifBit cond .Secret (ComR.ret a) (ComR.ret b) =>
      show (cmovSword cond a b).denote V = _
      rw [cmovSword_denote]
      rfl

/-- `ifToCmov` preserves the pure denotation of any `ComR`. -/
theorem ifToCmov_denote_eq {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : ComR catCryptDialect Γ t) (V : Ctxt.Valuation Γ) :
    (ifToCmov c).denote V = c.denote V := by
  cases t with
  | bit => exact ifToCmovBit_denote_eq c V
  | unit => rfl
  | pair _ _ => rfl
  | sum _ _ => rfl
  | sword _ => exact ifToCmovSword_denote_eq c V
  | memref _ => rfl

/-! ## 5. CT-safety of the rewritten form -/

/-- `cmovBit` is region-free, hence CT-safe by structure. -/
@[simp] theorem ctSafeComR_cmovBit {Γ : Ctxt catCryptDialect}
    (c a b : Ctxt.Var Γ .bit) :
    ctSafeComR (cmovBit c a b) = true := by
  -- Each let-bound expression is `not`/`and`/`or`, all CT-safe ops.
  rfl

/-- **Main CT escalation theorem** (specific to the rewritten shape):
    on the *exact* value-shaped, bit-typed, `Secret`-tagged `ifBit`,
    `ifToCmov` produces a CT-safe program. -/
theorem ifToCmov_makes_bit_secret_ifBits_ctSafe
    {Γ : Ctxt catCryptDialect} (cond a b : Ctxt.Var Γ .bit) :
    ctSafeComR
        (ifToCmov (ComR.ifBit (d := catCryptDialect) (t := .bit)
            cond .Secret (.ret a) (.ret b))) = true := by
  -- Unfolds: `ifToCmov` on `.bit` calls `ifToCmovBit`, which on the
  -- value-shaped pattern returns `cmovBit cond a b`.
  show ctSafeComR (cmovBit cond a b) = true
  exact ctSafeComR_cmovBit cond a b

/-- `cmovSword` is region-free, hence CT-safe by structure. -/
@[simp] theorem ctSafeComR_cmovSword {Γ : Ctxt catCryptDialect} {n : Nat}
    (c : Ctxt.Var Γ .bit) (a b : Ctxt.Var Γ (.sword n)) :
    ctSafeComR (cmovSword c a b) = true := by
  -- Each let-bound expression is `bitToSword`/`bvNot`/`bvAnd`/`bvOr`,
  -- all CT-safe ops (none is `ite`).
  rfl

/-- **CT escalation theorem for `.sword n`:** on the value-shaped,
    `.sword n`-typed, `Secret`-tagged `ifBit`, `ifToCmov` produces a
    CT-safe program. -/
theorem ifToCmov_makes_sword_secret_ifBits_ctSafe
    {Γ : Ctxt catCryptDialect} {n : Nat}
    (cond : Ctxt.Var Γ .bit) (a b : Ctxt.Var Γ (.sword n)) :
    ctSafeComR
        (ifToCmov (ComR.ifBit (d := catCryptDialect) (t := .sword n)
            cond .Secret (.ret a) (.ret b))) = true := by
  show ctSafeComR (cmovSword cond a b) = true
  exact ctSafeComR_cmovSword cond a b

/-- **Non-decrease of CT-safety.** For any input, the rewriter's output
    is either CT-safe outright (we discharged an `ifBit`) or has the
    same CT-safety as the input (we left the program alone). -/
theorem ifToCmov_ctSafe_or_unchanged
    {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : ComR catCryptDialect Γ t) :
    ctSafeComR (ifToCmov c) = true
      ∨ ctSafeComR (ifToCmov c) = ctSafeComR c := by
  cases t with
  | bit =>
      -- Case split on the bit-typed program's shape.
      match c with
      | ComR.ret _ => right; rfl
      | ComR.var _ _ => right; rfl
      | ComR.ifBit _ .Public _ _ => right; rfl
      | ComR.ifBit _ .Secret (ComR.var _ _) _ => right; rfl
      | ComR.ifBit _ .Secret (ComR.ifBit ..) _ => right; rfl
      | ComR.ifBit _ .Secret (ComR.ret _) (ComR.var _ _) => right; rfl
      | ComR.ifBit _ .Secret (ComR.ret _) (ComR.ifBit ..) => right; rfl
      | ComR.ifBit cond .Secret (ComR.ret a) (ComR.ret b) =>
          left
          exact ifToCmov_makes_bit_secret_ifBits_ctSafe cond a b
  | unit => right; rfl
  | pair _ _ => right; rfl
  | sum _ _ => right; rfl
  | sword n =>
      -- Mirror the `.bit` case for `.sword n`.
      match c with
      | ComR.ret _ => right; rfl
      | ComR.var _ _ => right; rfl
      | ComR.ifBit _ .Public _ _ => right; rfl
      | ComR.ifBit _ .Secret (ComR.var _ _) _ => right; rfl
      | ComR.ifBit _ .Secret (ComR.ifBit ..) _ => right; rfl
      | ComR.ifBit _ .Secret (ComR.ret _) (ComR.var _ _) => right; rfl
      | ComR.ifBit _ .Secret (ComR.ret _) (ComR.ifBit ..) => right; rfl
      | ComR.ifBit cond .Secret (ComR.ret a) (ComR.ret b) =>
          left
          exact ifToCmov_makes_sword_secret_ifBits_ctSafe cond a b
  | memref _ => right; rfl

/-! ## 6. Smoke test -/

/-- Smoke test: the rewriter turns a `Secret`-tagged bit `ifBit` into
    a CT-safe program. -/
example {Γ : Ctxt catCryptDialect} (c a b : Ctxt.Var Γ .bit) :
    ctSafeComR (ifToCmov (ComR.ifBit (d := catCryptDialect) (t := .bit)
        c .Secret (.ret a) (.ret b))) = true := by
  exact ifToCmov_makes_bit_secret_ifBits_ctSafe c a b

/-- Smoke test: denotation is preserved on the rewritten shape. -/
example {Γ : Ctxt catCryptDialect}
    (c a b : Ctxt.Var Γ .bit) (V : Ctxt.Valuation Γ) :
    (ifToCmov (ComR.ifBit (d := catCryptDialect) (t := .bit)
        c .Secret (.ret a) (.ret b))).denote V =
      (ComR.ifBit (d := catCryptDialect) (t := .bit)
        c .Secret (.ret a) (.ret b)).denote V :=
  ifToCmov_denote_eq _ V

/-- Smoke test (sword): the rewriter turns a `Secret`-tagged
    `.sword n` `ifBit` into a CT-safe program. This is the
    load-bearing case for real crypto code (constant-time selects on
    64-bit limbs, scalar reduction, point swap, etc.). -/
example {Γ : Ctxt catCryptDialect} {n : Nat}
    (c : Ctxt.Var Γ .bit) (a b : Ctxt.Var Γ (.sword n)) :
    ctSafeComR (ifToCmov (ComR.ifBit (d := catCryptDialect) (t := .sword n)
        c .Secret (.ret a) (.ret b))) = true := by
  exact ifToCmov_makes_sword_secret_ifBits_ctSafe c a b

/-- Smoke test (sword): denotation is preserved on the rewritten shape. -/
example {Γ : Ctxt catCryptDialect} {n : Nat}
    (c : Ctxt.Var Γ .bit) (a b : Ctxt.Var Γ (.sword n))
    (V : Ctxt.Valuation Γ) :
    (ifToCmov (ComR.ifBit (d := catCryptDialect) (t := .sword n)
        c .Secret (.ret a) (.ret b))).denote V =
      (ComR.ifBit (d := catCryptDialect) (t := .sword n)
        c .Secret (.ret a) (.ret b)).denote V :=
  ifToCmov_denote_eq _ V

end Transforms
end CatCrypt.Crypto.SecureCompilation.VIR
