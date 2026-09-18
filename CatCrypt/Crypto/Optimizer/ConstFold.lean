/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-!
# Verified constant-folding / partial-evaluation for `Com` (jasminDialect)

A structural `Com → Com` constant-folding pass over the typed VIR
`jasminDialect`, in the same vein as `Optimizer/Rewrite/Egraph.lean` (which it
imports for its known-constant-environment infrastructure) and
`Optimizer/ComDCE.lean`. Where `Egraph.lean` fires algebraic rules when the
**second** operand of a `regArith` is a known constant, this pass closes the
two complementary gaps that complete partial evaluation:

1. **Full fold (both operands constant).** When *both* operands of a binary
   `regArith` are known constants (`regConst`), the whole op is evaluated at
   compile time and replaced by a single nullary `regConst w n` materialising
   the result `(bop.apply (ofNat w ca) (ofNat w cb))`. This is
   `regConst a + regConst b ↦ regConst (a + b)` and its cousins for every
   `JasminBinOp`. The replacement is a nullary op of the *same* return type
   `reg w` in the *same* context, so no De Bruijn renumbering is needed.

2. **One-operand identities / annihilators (either side).** `x + 0 ↦ x`,
   `x * 1 ↦ x`, `x * 0 ↦ 0`, `x & 0 ↦ 0`, … fired whether the constant is the
   first or the second operand (`Egraph.rewriteBin` only inspects the second).
   These collapse the algebraic no-ops a classical-offset partial evaluation
   leaves behind: folding a classical operand into an operation collapses the
   gate to a wire (identity) or a constant (annihilator).

This is the IR realisation of the *classical-offset partial evaluation*
optimisation: a known classical operand of a gate is folded in, collapsing the
gate. Here the "gate" is a `regArith` op and the "classical operand" is a
`regConst` binder.

## Preservation theorem

* `foldBin_sound` : per-fold `BitVec`-algebra denotation equality (real, not
  `rfl`): the full-fold arm relies on `BitVec.ofNat_toNat` to undo the
  `toNat` round-trip in the materialised constant.
* `foldExpr_denote` : one-expression denotation preservation under a consistent
  known-constant env.
* `foldCom_denote` : `(foldCom c k).denote V = c.denote V`, by induction over
  the `Com` let-chain (reusing `Egraph.extendK` / `extendK_consistent`).
  **Not `rfl`.**
* `foldCom_ctSafe` : CT preservation — every fold produces only straight-line
  ops (`regConst` / `regArith .or` / `regArith .and`), so the branch-free
  invariant is maintained.

All goals closed. No `sorry`. Axiom set inherited via `Egraph`
(`propext`, `Quot.sound`, `Classical.choice`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ConstFold

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open Ctxt (Var)

/-! ## 1. The fold at the `Expr` level

`foldBin` rewrites a binary `regArith bop a b` given the optional known
constants `ca` (for `a`) and `cb` (for `b`). It returns `none` if no fold
fires. The arms:

* **full fold** (both constant): emit `regConst w n` with
  `n = (bop.apply (ofNat w ca) (ofNat w cb)).toNat`.
* **identity** (one side a neutral constant): emit `binE .or a a` (denotes the
  live operand) — reusing the Egraph idiom that keeps the rewrite inside the
  existing context with no fresh binder.
* **annihilator** (one side absorbing): emit `binE .and z z` where `z` is the
  operand that *holds* the constant `0` (so it really denotes `0`).

All RHS shapes are within the existing context `Γ`, of return type `reg w`. -/

/-- Build a nullary `regConst w n` expression (denotes `BitVec.ofNat w n`). -/
def constE {Γ : Ctxt jasminDialect} (w n : Nat) :
    Expr jasminDialect Γ (.reg w) :=
  { op := .regConst w n, retTy_eq := rfl, args := .nil }

/-- Denotation of a `constE`: the materialised constant. Closes by `rfl`. -/
theorem constE_denote {Γ : Ctxt jasminDialect} (w n : Nat)
    (V : Ctxt.Valuation Γ) :
    (constE (Γ := Γ) w n).denote V = BitVec.ofNat w n := rfl

/-- Constant-fold a binary `regArith` given the known constants of *both*
operands. `none` if no rule fires.

* `some ca, some cb` ⇒ full fold to `regConst w (bop.apply …).toNat`.
* one-operand identity / annihilator arms fire from either side. -/
def foldBin {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Var Γ (.reg w))
    (ca cb : Option Nat) : Option (Expr jasminDialect Γ (.reg w)) :=
  match ca, cb with
  -- full fold: both operands are compile-time constants
  | some na, some nb =>
      some (constE w ((bop.apply (BitVec.ofNat w na) (BitVec.ofNat w nb)).toNat))
  -- second-operand identities / annihilators (mirror Egraph.rewriteBin)
  | _, some 0 =>
      match bop with
      | .add => some (binE .or a a)    -- x + 0 = x
      | .xor => some (binE .or a a)    -- x ^^^ 0 = x
      | .or  => some (binE .or a a)    -- x ||| 0 = x
      | .mul => some (binE .and b b)   -- x * 0 = 0 (b holds 0)
      | .and => some (binE .and b b)   -- x &&& 0 = 0 (b holds 0)
      | _    => none
  | _, some 1 =>
      match bop with
      | .mul => some (binE .or a a)    -- x * 1 = x
      | _    => none
  -- first-operand identities / annihilators (a holds the constant)
  | some 0, _ =>
      match bop with
      | .add => some (binE .or b b)    -- 0 + x = x
      | .xor => some (binE .or b b)    -- 0 ^^^ x = x
      | .or  => some (binE .or b b)    -- 0 ||| x = x
      | .mul => some (binE .and a a)   -- 0 * x = 0 (a holds 0)
      | .and => some (binE .and a a)   -- 0 &&& x = 0 (a holds 0)
      | _    => none
  | some 1, _ =>
      match bop with
      | .mul => some (binE .or b b)    -- 1 * x = x
      | _    => none
  | _, _ => none

/-! ## 2. Soundness of `foldBin` -/

/-- **Soundness of `foldBin`.** Under a known-constant env consistent with `V`,
any expression `foldBin` produces denotes the same value as the original
`binE bop a b`. The full-fold arm is a `BitVec`-algebra fact (undoing
the `toNat` round-trip of the materialised constant via `BitVec.ofNat_toNat`),
not `rfl`. -/
theorem foldBin_sound {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Var Γ (.reg w))
    (k : KEnv Γ) (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V)
    (ca cb : Option Nat)
    (hca : ca = KEnv.lookup a k) (hcb : cb = KEnv.lookup b k)
    (e' : Expr jasminDialect Γ (.reg w))
    (he : foldBin bop a b ca cb = some e') :
    e'.denote V = (binE bop a b).denote V := by
  -- Resolve the value of `a` and `b` whenever a constant is claimed.
  have hav : ∀ na, ca = some na → a.lookup V = BitVec.ofNat w na := by
    intro na h; exact hk a na (by rw [← hca]; exact h)
  have hbv : ∀ nb, cb = some nb → b.lookup V = BitVec.ofNat w nb := by
    intro nb h; exact hk b nb (by rw [← hcb]; exact h)
  rw [binE_denote]
  -- Case on the two optional constants exactly as `foldBin` does.
  match hca' : ca, hcb' : cb with
  | some na, some nb =>
      -- full fold
      subst hca'; subst hcb'
      simp only [foldBin] at he
      injection he with he; subst he
      rw [constE_denote]
      rw [hav na rfl, hbv nb rfl]
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | none, some nb =>
      subst hca'; subst hcb'
      have hb0 := hbv nb rfl
      -- only nb ∈ {0,1} fire; otherwise no rule
      match nb, hb0 with
      | 0, hb0 =>
          cases bop <;>
            first
              | (simp only [foldBin] at he; injection he with he; subst he;
                 simp only [binE_denote, JasminBinOp.apply, hb0]; simp)
              | simp [foldBin] at he
      | 1, hb0 =>
          cases bop <;>
            first
              | (simp only [foldBin] at he; injection he with he; subst he;
                 simp only [binE_denote, JasminBinOp.apply, hb0]; simp)
              | simp [foldBin] at he
      | (n + 2), _ =>
          cases bop <;> simp [foldBin] at he
  | some na, none =>
      subst hca'; subst hcb'
      have ha0 := hav na rfl
      match na, ha0 with
      | 0, ha0 =>
          cases bop <;>
            first
              | (simp only [foldBin] at he; injection he with he; subst he;
                 simp only [binE_denote, JasminBinOp.apply, ha0]; simp)
              | simp [foldBin] at he
      | 1, ha0 =>
          cases bop <;>
            first
              | (simp only [foldBin] at he; injection he with he; subst he;
                 simp only [binE_denote, JasminBinOp.apply, ha0]; simp)
              | simp [foldBin] at he
      | (n + 2), _ =>
          cases bop <;> simp [foldBin] at he
  | none, none =>
      subst hca'; subst hcb'
      cases bop <;> simp [foldBin] at he

/-! ## 3. The `Expr`-level fold (any expression)

`foldExpr e k` folds a single expression: if `e` is a binary `regArith` over
`reg w` for which `foldBin` fires (consulting the known constants of *both*
operands), it returns the folded expression; otherwise it returns `e`
unchanged. Type- and context-preserving by construction. -/

/-- Fold one expression with the known-constant env. Identity unless the
expression is a binary `regArith` over `reg w` whose operand constants fire a
fold. -/
def foldExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) : Expr jasminDialect Γ t :=
  match e with
  | ⟨.regArith bop w, hop, args⟩ =>
      let a : Var Γ (.reg w) := args.head
      let b : Var Γ (.reg w) := args.tail.head
      match foldBin bop a b (KEnv.lookup a k) (KEnv.lookup b k) with
      | some e' => hop ▸ e'
      | none    => ⟨.regArith bop w, hop, args⟩
  | e => e

/-- **Denotation preservation for `foldExpr`.** Under a consistent env, folding
one expression preserves its denotation. -/
theorem foldExpr_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ)
    (hk : KEnv.Consistent k V) :
    (foldExpr e k).denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [foldExpr, HVector.head, HVector.tail]
        rcases hr : foldBin bop a b (KEnv.lookup a k) (KEnv.lookup b k) with _ | e'
        · simp
        · rw [foldBin_sound bop a b k V hk _ _ rfl rfl e' hr]
          rfl
  | stackLoad w n => simp [foldExpr]
  | stackStore w n => simp [foldExpr]
  | castW w w' => simp [foldExpr]
  | extCall nm a r => simp [foldExpr]
  | regConst w n => simp [foldExpr]
  | vpackZMM bop => simp [foldExpr]
  | vpackZMMd bop => simp [foldExpr]
  | vprordZMM n => simp [foldExpr]
  | vpslldq n => simp [foldExpr]
  | vpsrldq n => simp [foldExpr]
  | vsimd op => simp [foldExpr]
  | vymm op => simp [foldExpr]
  | mulhi w => simp [foldExpr]
  | addCarryLo w => simp [foldExpr]
  | addCarryHi w => simp [foldExpr]
  | rorImm w n => simp [foldExpr]
  | shrImm w n => simp [foldExpr]
  | sarImm w n => simp [foldExpr]
  | shlImm w n => simp [foldExpr]
  | select w => simp [foldExpr]
  | callN name argTys retTys => simp [foldExpr]
  | cmp c w => simp [foldExpr]
  | cmpImm c w n => simp [foldExpr]

/-! ## 4. The constant-folding pass over `Com`

`foldCom` does one structural pass: it folds every let-bound expression with
`foldExpr`, threading the known-constant env (a `regConst _ n` binder pushes
`some n`, via `Egraph.extendK`), and descends into the body. -/

/-- One structural constant-folding pass over a `Com`, threading the
known-constant env. -/
def foldCom {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → KEnv Γ → Com jasminDialect Γ t
  | .ret v, _ => .ret v
  | .var e body, k => .var (foldExpr e k) (foldCom body (extendK e k))

/-- **Denotation preservation for `foldCom`.** `foldCom c k` denotes the same
function as `c`, for any env `k` consistent with the valuation. Proved by
induction over the `Com` let-chain — **not** `rfl`: each binder's expression is
folded via the denotation-preserving `foldExpr`, and the env is
threaded consistently using `Egraph.extendK_consistent` (folding `e` does not
change its denotation, so the constant the binder claims is unchanged). -/
theorem foldCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ),
      KEnv.Consistent k V → (foldCom c k).denote V = c.denote V
  | .ret v, _, _, _ => rfl
  | .var e body, k, V, hk => by
      simp only [foldCom, Com.denote]
      rw [foldExpr_denote e k V hk]
      exact foldCom_denote body (extendK e k) (V.extend (e.denote V))
        (extendK_consistent e k V hk)

/-! ## 5. CT preservation

`jasminDialect` is branch-free, so every `Com` — input or output — is CT-safe
under the structural `Egraph.ctSafeComJ` predicate. The fold produces only
straight-line ops, so the invariant is maintained. -/

/-- **CT preservation for the fold pass.** `foldCom c k` is CT-safe iff `c` is
(both are, since the dialect has no conditional op). -/
theorem foldCom_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    ctSafeComJ (foldCom c k) = ctSafeComJ c := by
  rw [ctSafeComJ_true (foldCom c k), ctSafeComJ_true c]

/-! ## 6. Self-contained validation

A `Com jasminDialect [] (reg 32)` exercising the full fold end-to-end:

    let c2 = regConst 32 2     -- constant 2
    let c3 = regConst 32 3     -- constant 3
    let r  = c2 + c3           -- both operands constant ⇒ fold to regConst 5
    ret r

The pass folds the `add` site (both operands known constants) to the single
nullary `regConst 32 5`. We check the rewritten `Com` denotes `5`, equal to
the input. -/

/-- The input program: `(regConst 2) + (regConst 3)`, both operands constant. -/
def demoFold : Com jasminDialect [] (.reg 32) :=
  -- position 0: c2 = 2.  Context becomes [reg32 (=c2)].
  .var (constE 32 2)
    -- position 1: c3 = 3.  Context becomes [reg32 (=c3), reg32 (=c2)].
    (.var (constE 32 3)
      -- position 2: r = c2 + c3.  c3 = .here, c2 = .there .here.
      (.var (binE .add (.there .here) .here)
        (.ret .here)))

/-- The empty known-constant env for the empty top-level context. -/
def demoK : KEnv ([] : Ctxt jasminDialect) := KEnv.nil

/-- The empty env is consistent with the (unique) empty valuation. -/
theorem demoK_consistent (V : Ctxt.Valuation (d := jasminDialect) []) :
    KEnv.Consistent demoK V := by
  intro w v n hv
  cases v

/-- **The fold collapses the `add` to a single `regConst 32 5`.** A concrete
`rfl`-checkable witness: after the pass the third binder is the materialised
constant `5`. -/
example :
    foldCom demoFold demoK =
      Com.var (constE 32 2)
        (.var (constE 32 3)
          (.var (constE 32 5) (.ret .here))) := rfl

/-- **Denotation preserved**, via the general theorem. -/
example (V : Ctxt.Valuation (d := jasminDialect) []) :
    (foldCom demoFold demoK).denote V = demoFold.denote V :=
  foldCom_denote demoFold demoK V (demoK_consistent V)

/-- **Both denote the constant `5`.** Concretely on the empty valuation. -/
example : demoFold.denote .nil = (5 : BitVec 32) := rfl

example : (foldCom demoFold demoK).denote .nil = (5 : BitVec 32) := rfl

/-- **CT preserved** on the demo. -/
example : ctSafeComJ (foldCom demoFold demoK) = ctSafeComJ demoFold :=
  foldCom_ctSafe demoFold demoK

/-! ## 7. One-operand identity folds exercised

A program with `x + 0` where the `0` is the *first* operand (which
`Egraph.rewriteBin` would miss, but `foldBin` folds from either side):

    let c0 = regConst 32 0     -- constant 0
    let r  = c0 + x            -- 0 + x = x   (first-operand identity)
    ret r
-/

/-- `0 + x` with the constant `0` as the *first* operand. -/
def demoFirstId : Com jasminDialect [.reg 32] (.reg 32) :=
  -- c0 = 0.  Context [c0, x]; x = .there .here, c0 = .here.
  .var (constE 32 0)
    -- r = c0 + x.  c0 = .here, x = .there .here.
    (.var (binE .add .here (.there .here))
      (.ret .here))

/-- The top-level env: `x` is a free input (no known constant). -/
def demoFirstK : KEnv ([.reg 32] : Ctxt jasminDialect) := KEnv.cons none KEnv.nil

theorem demoFirstK_consistent (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    KEnv.Consistent demoFirstK V := by
  intro w v n hv
  cases v with
  | here => simp [demoFirstK, KEnv.lookup] at hv
  | there v' => cases v' <;> simp [demoFirstK, KEnv.lookup] at hv

/-- **First-operand identity folded**: `0 + x` becomes `x ||| x` (`binE .or x x`,
which denotes `x`), reusing the existing variable. -/
example :
    foldCom demoFirstId demoFirstK =
      Com.var (constE 32 0)
        (.var (binE .or (.there .here) (.there .here)) (.ret .here)) := rfl

/-- **Denotation preserved** (both map `x ↦ x`). -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (foldCom demoFirstId demoFirstK).denote V = demoFirstId.denote V :=
  foldCom_denote demoFirstId demoFirstK V (demoFirstK_consistent V)

/-- Concretely, on `x = 42`, both denote `42`. -/
example : demoFirstId.denote (.cons (42 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

example :
    (foldCom demoFirstId demoFirstK).denote (.cons (42 : BitVec 32) .nil)
      = (42 : BitVec 32) := rfl

end CatCrypt.Crypto.Optimizer.ConstFold
