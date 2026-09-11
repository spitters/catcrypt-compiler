/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all CatCrypt.Crypto.SecureCompilation.ImpExprToThir
import all CatCrypt.Crypto.SecureCompilation.ThirToComFront
import all CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public meta import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
public import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction

/-!
# A `desugarSelect` pre-pass: compiling a public `ifThenElse` branchlessly

The core `impExprToThir` translator rejects `ImpExpr.ifThenElse` outright (it is in
the `=> none` set), so the front cannot ingest a conditional. This pre-pass closes
that gap **without touching the core**, the same way `desugarNot` closed the `Not`
gap: it structurally rewrites every `ifThenElse c a b` into the constant-time
branchless-select idiom

```text
  if c then a else b   ↦   b ⊕ ((0 − c) & (a ⊕ b))
```

with `c ∈ {0,1}` (a public boolean). For `c = 1` the mask `0 − c` is all-ones, so
the expression is `b ⊕ (a ⊕ b) = a`; for `c = 0` the mask is `0`, so it is
`b ⊕ 0 = b`. The result uses only `Sub` / `BitAnd` / `BitXor` — heads the §3
translator already accepts — and contains **no** branch: it compiles through the
*unchanged* `compileFromHax` and is constant-time by construction
(`JasminCTByConstruction`: the emitted `Com` is in the index-free fragment, no
`stackLoad`/`stackStore`, no data-dependent control surface).

This is the *public*-conditional case. A *secret*-conditioned branch is exactly
what the source CT gate (`ImpCTGate.impCTSafe`) rejects; here the condition is a
public input, and the desugaring makes the lowering branchless regardless — the
"restrict the language" route turning a conditional into a cmov-shaped dataflow op.

The Emit form (`desugarSelectEmit`) materializes the `0` literal into a fresh local
`__selZero` (the §3 lowering takes a binary-op operand from a register, not a bare
literal — the same register-materialization `desugarNotEmit` does for its all-ones
constant).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSelect

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminBinOp)

/-! ## §1  The branchless-select bit identity -/

/-- **The branchless constant-time select identity.** For a boolean `cv ∈ {0,1}`,
    the masked form `bv ⊕ ((0 − cv) & (av ⊕ bv))` equals `if cv = 1 then av else bv`.
    The correctness core of `desugarSelect`. -/
theorem select_mask_eq (cv av bv : BitVec 32) (hc : cv = 0 ∨ cv = 1) :
    bv ^^^ ((0 - cv) &&& (av ^^^ bv)) = if cv = 1 then av else bv := by
  rcases hc with h | h <;> subst h <;> bv_decide

/-! ## §2  The `desugarSelect` pre-pass (Emit form) -/

mutual
/-- Single-expression select-rewriter referencing a pre-materialized zero local
    `z`: `ifThenElse c a b ↦ BitXor[b, BitAnd[Sub[z, c], BitXor[a, b]]]`, recursing
    into every subterm. Fuel-bounded like `desugarNot`/`anfLift`. -/
def desugarSelectRefE (z : String) : Nat → ImpExpr → ImpExpr
  | 0, e => e
  | _ + 1, .lit l => .lit l
  | _ + 1, .var x => .var x
  | fuel + 1, .letBind x v b =>
      .letBind x (desugarSelectRefE z fuel v) (desugarSelectRefE z fuel b)
  | fuel + 1, .ifThenElse c a b =>
      let c' := desugarSelectRefE z fuel c
      let a' := desugarSelectRefE z fuel a
      let b' := desugarSelectRefE z fuel b
      .app "BitXor"
        [ b',
          .app "BitAnd"
            [ .app "Sub" [.var z, c'], .app "BitXor" [a', b'] ] ]
  | fuel + 1, .app f args => .app f (desugarSelectRefL z fuel args)
  | _ + 1, e => e
/-- Argument-list walker for `desugarSelectRefE`. -/
def desugarSelectRefL (z : String) : Nat → List ImpExpr → List ImpExpr
  | _, [] => []
  | fuel, a :: rest => desugarSelectRefE z fuel a :: desugarSelectRefL z fuel rest
end

/-- The select pre-pass: bind `0` to a fresh top-level local `__selZero`, then
    rewrite every `ifThenElse` to the branchless masked form referencing it. -/
def desugarSelectEmit (e : ImpExpr) : ImpExpr :=
  .letBind "__selZero" (.lit (.int 0)) (desugarSelectRefE "__selZero" 1000 e)

/-! ## §3  A public conditional select, compiled end to end

`cselSrc` is the canonical conditional `if c then a else b` over three scalar
inputs, in the param-self-binding shape extraction emits. -/

/-- The source conditional: `if c then a else b`, params `["c","a","b"]`. -/
def cselSrc : ImpExpr :=
  .letBind "c" (.var "c")
   (.letBind "a" (.var "a")
    (.letBind "b" (.var "b")
     (.ifThenElse (.var "c") (.var "a") (.var "b"))))

/-- The explicit emit-desugared form of `cselSrc`. -/
def cselDesugaredEmit : ImpExpr :=
  .letBind "__selZero" (.lit (.int 0))
   (.letBind "c" (.var "c")
    (.letBind "a" (.var "a")
     (.letBind "b" (.var "b")
      (.app "BitXor"
        [ .var "b",
          .app "BitAnd"
            [ .app "Sub" [.var "__selZero", .var "c"],
              .app "BitXor" [.var "a", .var "b"] ] ]))))

/-- `desugarSelectEmit` of `cselSrc` is the explicit `cselDesugaredEmit`. -/
theorem desugarSelectEmit_csel_eq : desugarSelectEmit cselSrc = cselDesugaredEmit := by
  simp [desugarSelectEmit, desugarSelectRefE, cselDesugaredEmit, cselSrc]

/-- **`desugarSelect` makes the conditional denote, branchlessly.** The ANF-lifted
    emit-desugared `cselSrc` (params `["c","a","b"]`, `c = inpGet 0` a boolean)
    denotes to `if c = 1 then a else b` — via the masked-select identity
    `select_mask_eq`. -/
theorem csel_denoteScalar (cv av bv : BitVec 32) (hc : cv = 0 ∨ cv = 1) :
    ImpExpr.denoteScalar (w := 32) (nIn := 3) ["c", "a", "b"] ![cv, av, bv]
        (anfLift (desugarSelectEmit cselSrc)) (fun _ => none)
      = some (if cv = 1 then av else bv) := by
  rw [desugarSelectEmit_csel_eq]
  have e : ImpExpr.denoteScalar (w := 32) (nIn := 3) ["c", "a", "b"] ![cv, av, bv]
        (anfLift cselDesugaredEmit) (fun _ => none)
      = some (bv ^^^ ((0 - cv) &&& (av ^^^ bv))) := by
    simp only [cselDesugaredEmit, anfLift, anfVal, stripWidthSuffix,
      ImpExpr.denoteScalar, denoteAtomExpr,
      List.idxOf?, List.findIdx?, reduceIte, String.reduceEq]
    rfl
  rw [e]; exact congrArg some (select_mask_eq cv av bv hc)

/-! ## §4  The compile-from-hax deliverable -/

/-- The compile-from-hax pipeline succeeds on the emit-desugared conditional. -/
theorem csel_isSome :
    (compileFromHax (w := 32) (nIn := 3) ["c", "a", "b"]
      (anfLift (desugarSelectEmit cselSrc))).isSome := by
  rw [desugarSelectEmit_csel_eq]; native_decide

/-- **A public conditional compiles correctly, branchlessly.** There is a compiled
    `Com jasminDialect` `c_` with `compileFromHax ["c","a","b"] (anfLift (desugarSelect
    cselSrc)) = some c_`, and for every boolean `cv ∈ {0,1}` and `av, bv`, `c_`'s
    denotation is exactly `if cv = 1 then av else bv`. The front now ingests a
    public `ifThenElse` — lowered to a branch-free cmov-shaped dataflow body — via
    the verified `desugarSelect` pre-pass and the unchanged `compileFromHax`. -/
theorem csel_select_compiles :
    ∃ c_ : Com jasminDialect (frontCtxt 32 3 []) (rW 32),
      compileFromHax (w := 32) (nIn := 3) ["c", "a", "b"]
          (anfLift (desugarSelectEmit cselSrc)) = some c_ ∧
      ∀ (cv av bv : BitVec 32), cv = 0 ∨ cv = 1 →
        c_.denote (inputValuation 32 3 ![cv, av, bv]) = if cv = 1 then av else bv := by
  set c_ := (compileFromHax (w := 32) (nIn := 3) ["c", "a", "b"]
    (anfLift (desugarSelectEmit cselSrc))).get csel_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 3) ["c", "a", "b"]
      (anfLift (desugarSelectEmit cselSrc)) = some c_ := (Option.some_get _).symm
  refine ⟨c_, hc, ?_⟩
  intro cv av bv hcv
  exact compileFromHax_meets_spec (w := 32) (nIn := 3) ["c", "a", "b"] ![cv, av, bv]
    (anfLift (desugarSelectEmit cselSrc)) _ hc (csel_denoteScalar cv av bv hcv)

/-- **The compiled conditional is constant-time by construction.** The emitted
    `Com jasminDialect` is in the index-free fragment — no `stackLoad`/`stackStore`,
    no data-dependent control surface — so `ComJasminCTByConstruction` holds: the
    public `ifThenElse` became a branch-free, channel-free body. -/
theorem csel_compiled_is_CT :
    ComJasminCTByConstruction
      ((compileFromHax (w := 32) (nIn := 3) ["c", "a", "b"]
        (anfLift (desugarSelectEmit cselSrc))).get csel_isSome) :=
  (comJasminCT?_eq_true_iff _).mp (by native_decide)

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSelect
