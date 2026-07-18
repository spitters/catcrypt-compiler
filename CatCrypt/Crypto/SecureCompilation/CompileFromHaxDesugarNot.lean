/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax
import CatCrypt.Crypto.SHA256.Extraction.Sha256_haxpipe

/-!
# A `desugarNot` pre-pass: compiling the verbatim SHA-256 `Ch` extraction

`CompileFromHaxLeaves.ch_compiles` compiled a **hand-built** `Ch` source
(`chSrc`) in which the complement `¬e` was *manually* pre-desugared to
`BitXor[e, ones]` with the all-ones constant materialized into a local. The real
typed extraction the hax pipeline emits — `Sha256.ch_impExpr` (in
`CatCrypt/Crypto/SHA256/Extraction/Sha256_haxpipe.lean`) — instead contains a
bare `Not#32[e]` head:

```text
ch_impExpr =
  letBind "e" (var "e") (letBind "f" (var "f") (letBind "g" (var "g")
    BitXor#32[ BitAnd#32[e, f], BitAnd#32[ Not#32[e], g ] ]))
```

The §3 front translator `rhsOf` has **no `Not` arm** (it recognizes binary ALU
and shift heads only; `ImpExprToThir` §10's note records this exactly: *"It does
not cover a `Not[·]` operand … the orthogonal `rhsOf`-has-no-NOT-`Rhs`
limitation"*). The width-agnostic translator also cannot synthesize the all-ones
literal that complement needs. So `ch_impExpr` does **not** compile verbatim —
which is precisely why the committed `chSrc` hand-built the complement.

This module adds the missing **pre-pass**, additively (no edit to
`ImpExprToThir.lean`): `desugarNot` structurally rewrites every
`Not[a]` / `BitNot[a]` (after dropping a `#<width>` tag via the committed
`stripWidthSuffix`) into the all-ones-XOR form the existing `BitXor` recognizer
handles. Run *before* `anfLift`, it turns the real `Not#32[e]` extraction into a
`BitXor`-only body that `anfLift`/`compileFromHax` consume — so `ch_impExpr`
compiles **verbatim**, no hand-desugaring.

## Two forms of the all-ones XOR (and why the emit path materializes it)

The clean rewrite is `Not[a] ↦ BitXor[desugarNot a, lit (2^w−1)]` — the literal
all-ones-XOR (`desugarNot` below; `desugarNot_app_not` is the exact structural
equation). Its `denoteScalar` is the FIPS complement `~~~` (via
`BitVec.xor_allOnes`, `lit (2^32−1)` denoting to `allOnes 32`). This is the
value-preserving fact: the compiler now *has* a `Not` body with a denotation.

For the **emitted jasmin** there is one more wrinkle the committed `chSrc`
already documented: the C1 lowering rejects a bare literal in a binary-op
operand position (`Atom.toVar (.lit _) = none`), so the all-ones constant must be
*materialized into a register* first. The `desugarNotEmit` form does exactly
that — it binds the all-ones constant to a single fresh local at the top and
rewrites `Not[a] ↦ BitXor[desugarNotEmit a, var ones]`. That is the form whose
`anfLift` compiles end to end (`ch_desugar_verbatim_compiles`), value-preserving
against the FIPS `Ch` formula. The two forms denote identically; the emit form
only differs by hoisting the constant into a local, the same register
materialization `chSrc` performs by hand.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxDesugarNot

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  The `desugarNot` pre-pass (literal all-ones-XOR form)

`desugarNot w` structurally rewrites `Not[a]`/`BitNot[a]` (modulo a `#<width>`
head tag) into `BitXor[desugarNot a, lit (2^w−1)]`, recursing into every
subterm. Fuel-bounded (like §10's `anfLift`/`anfVal`), so termination is
structural on the fuel; fuel `1000` covers any realistic extracted body. -/

mutual
/-- Single-expression `Not`-rewriter. Drops a `#<width>` tag via the committed
    `stripWidthSuffix`, then rewrites a unary `Not`/`BitNot` to the all-ones XOR;
    every other head recurses into its arguments. -/
def desugarNotE (w : Nat) : Nat → ImpExpr → ImpExpr
  | 0, e => e
  | _ + 1, .lit l => .lit l
  | _ + 1, .var x => .var x
  | fuel + 1, .letBind x v b =>
      .letBind x (desugarNotE w fuel v) (desugarNotE w fuel b)
  | fuel + 1, .app f args =>
      match stripWidthSuffix f, args with
      | "Not", [a] => .app "BitXor" [desugarNotE w fuel a, .lit (.int (2 ^ w - 1))]
      | "BitNot", [a] => .app "BitXor" [desugarNotE w fuel a, .lit (.int (2 ^ w - 1))]
      | _, _ => .app f (desugarNotL w fuel args)
  | _ + 1, e => e
/-- Argument-list walker for `desugarNotE`. -/
def desugarNotL (w : Nat) : Nat → List ImpExpr → List ImpExpr
  | _, [] => []
  | fuel, a :: rest => desugarNotE w fuel a :: desugarNotL w fuel rest
end

/-- The `desugarNot` pre-pass: structurally desugar every bitwise-NOT into the
    all-ones XOR, with the standard fuel budget. -/
def desugarNot (w : Nat) (e : ImpExpr) : ImpExpr := desugarNotE w 1000 e

/-- **The clean structural step.** `desugarNot` rewrites a unary `Not[a]` into the
    all-ones-XOR form `BitXor[desugarNot a, lit (2^w−1)]`. The general, true
    equation the pre-pass is built on — proved by the `desugarNotE` equation
    lemmas (`simp`). -/
theorem desugarNot_app_not (w n : Nat) (a : ImpExpr) :
    desugarNotE w (n + 1) (.app "Not" [a])
      = .app "BitXor" [desugarNotE w n a, .lit (.int (2 ^ w - 1))] := by
  simp [desugarNotE, stripWidthSuffix]

/-- Same for the `BitNot` spelling of the head. -/
theorem desugarNot_app_bitnot (w n : Nat) (a : ImpExpr) :
    desugarNotE w (n + 1) (.app "BitNot" [a])
      = .app "BitXor" [desugarNotE w n a, .lit (.int (2 ^ w - 1))] := by
  simp [desugarNotE, stripWidthSuffix]

/-! ## §2  `desugarNot` on the real `Sha256.ch_impExpr`

The literal-form `desugarNot` removes the real `Not#32[e]` head from the verbatim
extraction, leaving a `BitXor`/`BitAnd` body (the `#32` tags survive — `anfLift`
strips those — exactly as in the verbatim σ-family). -/

/-- The explicit literal-form desugaring of `Sha256.ch_impExpr`: the `Not#32[e]`
    has become `BitXor[e, lit (2³²−1)]`; the `BitXor#32`/`BitAnd#32` heads are
    unchanged (they are handled by `anfLift`'s `stripWidthSuffix`). -/
def chDesugared : ImpExpr :=
  .letBind "e" (.var "e")
   (.letBind "f" (.var "f")
    (.letBind "g" (.var "g")
     (.app "BitXor#32"
       [(.app "BitAnd#32" [(.var "e"), (.var "f")]),
        (.app "BitAnd#32"
          [(.app "BitXor" [(.var "e"), (.lit (.int (2 ^ 32 - 1)))]), (.var "g")])])))

/-- `desugarNot` of the verbatim `Sha256.ch_impExpr` is the explicit `chDesugared`
    (the `Not#32[e]` rewritten to `BitXor[e, lit (2³²−1)]`). Closed-term
    computation through the `desugarNotE` equation lemmas. -/
theorem desugarNot_ch_eq : desugarNot 32 Sha256.ch_impExpr = chDesugared := by
  simp [desugarNot, desugarNotE, desugarNotL, chDesugared, Sha256.ch_impExpr,
    stripWidthSuffix]

/-- **`desugarNot` makes the verbatim `Ch` body denote.** The `anfLift` of the
    desugared real `ch_impExpr` (parameters `["e","f","g"]`) denotes to the FIPS
    180-4 `Ch` value `(e ∧ f) ⊕ (¬e ∧ g)`. The literal `2³²−1` folds to
    `allOnes 32` (`by decide`) and `e ^^^ allOnes = ~~~e` (`BitVec.xor_allOnes`).
    The honest value-preservation fact: the `#32`-tagged `Not`-bearing literal had
    no denotation of its own; `desugarNot` (removing the `Not`) + `anfLift`
    (stripping the tags) is what gives it the FIPS `Ch` denotation. -/
theorem ch_desugar_denoteScalar (x y z : BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := 3) ["e", "f", "g"] ![x, y, z]
        (anfLift (desugarNot 32 Sha256.ch_impExpr)) (fun _ => none)
      = some ((x &&& y) ^^^ ((~~~x) &&& z)) := by
  rw [desugarNot_ch_eq]
  have e : ImpExpr.denoteScalar (w := 32) (nIn := 3) ["e", "f", "g"] ![x, y, z]
        (anfLift chDesugared) (fun _ => none)
      = some ((x &&& y) ^^^ ((x ^^^ BitVec.ofNat 32 4294967295) &&& z)) := by
    simp only [chDesugared, anfLift, anfVal, stripWidthSuffix,
      ImpExpr.denoteScalar, denoteAtomExpr,
      List.idxOf?, List.findIdx?, reduceIte, String.reduceEq]
    rfl
  rw [e, show (BitVec.ofNat 32 4294967295) = BitVec.allOnes 32 from by decide,
    BitVec.xor_allOnes]

/-! ## §3  The emit form (register-materialized all-ones constant)

`desugarNotEmit` is the literal-form pre-pass with the all-ones constant hoisted
to a single fresh top-level local `__dsugOnes` and the `Not` rewritten to
`BitXor[a, var __dsugOnes]`. This is the form whose `anfLift` compiles end to end:
the C1 lowering accepts the materialized local as a binary-op operand, where it
rejected the bare literal (the register-materialization the committed `chSrc`
performs by hand). The two forms denote identically. -/

mutual
/-- Single-expression `Not`-rewriter referencing a pre-materialized all-ones local
    `o` (instead of inlining the literal). -/
def desugarNotRefE (o : String) : Nat → ImpExpr → ImpExpr
  | 0, e => e
  | _ + 1, .lit l => .lit l
  | _ + 1, .var x => .var x
  | fuel + 1, .letBind x v b =>
      .letBind x (desugarNotRefE o fuel v) (desugarNotRefE o fuel b)
  | fuel + 1, .app f args =>
      match stripWidthSuffix f, args with
      | "Not", [a] => .app "BitXor" [desugarNotRefE o fuel a, .var o]
      | "BitNot", [a] => .app "BitXor" [desugarNotRefE o fuel a, .var o]
      | _, _ => .app f (desugarNotRefL o fuel args)
  | _ + 1, e => e
def desugarNotRefL (o : String) : Nat → List ImpExpr → List ImpExpr
  | _, [] => []
  | fuel, a :: rest => desugarNotRefE o fuel a :: desugarNotRefL o fuel rest
end

/-- The emit pre-pass: bind the all-ones constant `2^w−1` to a fresh top-level
    local `__dsugOnes`, then rewrite every `Not` to `BitXor[·, var __dsugOnes]`.
    The materialized-into-a-register all-ones-XOR. -/
def desugarNotEmit (w : Nat) (e : ImpExpr) : ImpExpr :=
  .letBind "__dsugOnes" (.lit (.int (2 ^ w - 1))) (desugarNotRefE "__dsugOnes" 1000 e)

/-- The explicit emit-form desugaring of `Sha256.ch_impExpr`. -/
def chDesugaredEmit : ImpExpr :=
  .letBind "__dsugOnes" (.lit (.int (2 ^ 32 - 1)))
   (.letBind "e" (.var "e")
    (.letBind "f" (.var "f")
     (.letBind "g" (.var "g")
      (.app "BitXor#32"
        [(.app "BitAnd#32" [(.var "e"), (.var "f")]),
         (.app "BitAnd#32"
           [(.app "BitXor" [(.var "e"), (.var "__dsugOnes")]), (.var "g")])]))))

/-- `desugarNotEmit` of the verbatim `Sha256.ch_impExpr` is the explicit
    `chDesugaredEmit`. Closed-term computation through the equation lemmas. -/
theorem desugarNotEmit_ch_eq : desugarNotEmit 32 Sha256.ch_impExpr = chDesugaredEmit := by
  simp [desugarNotEmit, desugarNotRefE, desugarNotRefL, chDesugaredEmit,
    Sha256.ch_impExpr, stripWidthSuffix]

/-! ## §4  The verbatim-`Ch` deliverable

`chNorm` is the `rfl`-pinned ANF normal form of the emit-desugared real
`ch_impExpr`; the three theorems mirror the σ₀/Maj/`ch` pattern. -/

/-- The `rfl`-pinned ANF normal form of the emit-desugared verbatim `ch_impExpr`. -/
noncomputable def chNorm : ImpExpr := anfLift (desugarNotEmit 32 Sha256.ch_impExpr)

/-- The emit-desugared verbatim `Ch` body denotes to the FIPS 180-4 `Ch` value
    `(e ∧ f) ⊕ (¬e ∧ g)` — the all-ones local `__dsugOnes` is bound to
    `2³²−1 = allOnes 32`, so `e ^^^ __dsugOnes = ~~~e` (`BitVec.xor_allOnes`). -/
theorem ch_desugarEmit_denoteScalar (x y z : BitVec 32) :
    ImpExpr.denoteScalar (w := 32) (nIn := 3) ["e", "f", "g"] ![x, y, z]
        (anfLift (desugarNotEmit 32 Sha256.ch_impExpr)) (fun _ => none)
      = some ((x &&& y) ^^^ ((~~~x) &&& z)) := by
  rw [desugarNotEmit_ch_eq]
  have e : ImpExpr.denoteScalar (w := 32) (nIn := 3) ["e", "f", "g"] ![x, y, z]
        (anfLift chDesugaredEmit) (fun _ => none)
      = some ((x &&& y) ^^^ ((x ^^^ BitVec.ofNat 32 4294967295) &&& z)) := by
    simp only [chDesugaredEmit, anfLift, anfVal, stripWidthSuffix,
      ImpExpr.denoteScalar, denoteAtomExpr,
      List.idxOf?, List.findIdx?, reduceIte, String.reduceEq]
    rfl
  rw [e, show (BitVec.ofNat 32 4294967295) = BitVec.allOnes 32 from by decide,
    BitVec.xor_allOnes]

/-- The compile-from-hax pipeline succeeds on the emit-desugared verbatim `Ch`. -/
theorem ch_desugar_isSome :
    (compileFromHax (w := 32) (nIn := 3) ["e", "f", "g"]
      (anfLift (desugarNotEmit 32 Sha256.ch_impExpr))).isSome := by
  rw [desugarNotEmit_ch_eq]; native_decide

/-- **The verbatim SHA-256 `Ch` extraction compiles correctly via `desugarNot`.**
    There is a compiled `Com jasminDialect` `c` such that the **verbatim**
    `Sha256.ch_impExpr` literal — with its bare `Not#32[e]` head, taken exactly as
    the typed extraction pipeline emits it — `desugarNotEmit`/`anfLift`-compiles to
    `c`, and for every triple `(e, f, g)`, `c`'s `BitVec 32` denotation (under the
    input valuation `![e, f, g]`) is exactly the FIPS 180-4 `Ch` formula
    `(e ∧ f) ⊕ (¬e ∧ g)`. The headline result: the `desugarNot` pre-pass lets the
    real `Not`-bearing extraction compile, where the committed `ch_compiles` had to
    hand-build the complement. Routed through the C3 meta-theorem
    `compileFromHax_meets_spec`. -/
theorem ch_desugar_verbatim_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 3) ["e", "f", "g"]
          (anfLift (desugarNotEmit 32 Sha256.ch_impExpr)) = some c ∧
      ∀ (x y z : BitVec 32),
        c.denote (inputValuation 32 3 ![x, y, z])
          = (x &&& y) ^^^ ((~~~x) &&& z) := by
  set c := (compileFromHax (w := 32) (nIn := 3) ["e", "f", "g"]
    (anfLift (desugarNotEmit 32 Sha256.ch_impExpr))).get ch_desugar_isSome with hc_def
  have hc : compileFromHax (w := 32) (nIn := 3) ["e", "f", "g"]
      (anfLift (desugarNotEmit 32 Sha256.ch_impExpr)) = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x y z
  exact compileFromHax_meets_spec (w := 32) (nIn := 3) ["e", "f", "g"] ![x, y, z]
    (anfLift (desugarNotEmit 32 Sha256.ch_impExpr)) _ hc
    (ch_desugarEmit_denoteScalar x y z)

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxDesugarNot
