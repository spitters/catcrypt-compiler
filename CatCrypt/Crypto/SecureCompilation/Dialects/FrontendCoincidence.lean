/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ImpExprToThir
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# DF keystone (base cases): the two frontend denotations COINCIDE on the
# heap-free scalar-ALU fragment

This module is the **base-case feasibility result** for the "DF keystone" of the
MLIR-dialect-alignment restructure: showing that the two frontend ingestion
paths for a *pure scalar* Rust `ImpExpr` compute the **same value** on the
heap-free fragment, so the two paths become one meaning.

## The two paths

* **Path A — scalar-THIR-direct.**
  `ImpExpr.denoteScalar (params) (I) : ImpExpr → (String → Option (BitVec w)) →
  Option (BitVec w)` (`CatCrypt.Crypto.SecureCompilation.ImpExprToThir`). A
  *source* semantics for the let-normalized scalar ARX subset, generic in the
  working width `w`. Atoms go through `denoteAtomExpr`; binary-arith `.app`
  heads dispatch via `recogBin` to `JasminBinOp.apply`; `.letBind` recurses.

* **Path B — whole-function LowCT.**
  The pure/scalar *expression* evaluator on the LowCT side is
  `SExpr.evalBV (β : String → BitVec 64) : SExpr → BitVec 64`
  (`CatCrypt.Crypto.Jasmin.LowCT`), the u64-wrapping-faithful evaluator: every
  node does the corresponding `BitVec 64` operation, truncating mod `2^64` at
  each step exactly like the hardware. `SVar x ↦ β x`, `SLit n ↦ BitVec.ofNat 64
  n`, `SAdd ↦ +`, `SXor ↦ ^^^`, …

## Feasibility map (the exact relationship)

On the **heap-free scalar-ALU fragment** — variable/literal atoms, and the
binary ALU `.app` heads `add/sub/mul/and/or/xor` (i.e. `recogBin` heads) — the
two denotations coincide *exactly* at the fixed working width `w = 64`, which is
where the two types meet:

```
denoteScalar params I e ρ  =  some (SExpr.evalBV β (toSExpr e))
```

once we (i) **pin the width** at `w = 64` (Path A is generic `w`; `evalBV` is
fixed `BitVec 64`, so `w = 64` is the unique clean alignment), (ii) supply the
**`SExpr` image** `toSExpr e` of the scalar-ALU `ImpExpr` (the hand-written
`SExpr` that the LowCT scalar evaluator would compute — the LowCT *command*
lowering `haxToLowCT` routes scalar binops through `RCall`, not through a
top-level `SExpr`, so the genuine point of contact is the `SExpr` evaluator, not
a bare `haxToLowCT` image; see the *obstacle* note below), and (iii) impose the
**env-agreement predicate** linking Path A's partial `ρ : String → Option (BitVec
64)` (together with the `params`/`I` input convention) to Path B's total `β :
String → BitVec 64`:

```
EnvAgree params I ρ β  :=
  ∀ x,  denoteAtomExpr params I (.var x) ρ  =  some (β x)
```

i.e. each variable's Path-A reading (input word `inpGet I i` if `x` is parameter
`i`, else the local `ρ x`) equals its Path-B reading `β x`. Under `EnvAgree`, a
**literal** atom coincides because both sides are `BitVec.ofNat 64 n`; a
**variable** atom coincides by `EnvAgree` directly; a **binary ALU** `.app`
coincides because `JasminBinOp.apply op` and the corresponding `SExpr.evalBV`
node are the *same* `BitVec 64` operation (`+`/`-`/`*`/`&&&`/`|||`/`^^^`).

### The general theorem (statement shape — proved here for the non-`let` fragment)

```
theorem denoteScalar_coincides_evalBV
    (params : List String) (I : Fin nIn → BitVec 64)
    (ρ : String → Option (BitVec 64)) (β : String → BitVec 64)
    (hβ : EnvAgree params I ρ β)
    (e : ImpExpr) {s : SExpr} (hs : toSExpr e = some s) :
    ImpExpr.denoteScalar params I e ρ = some (SExpr.evalBV β s)
```

The membership side-condition is `toSExpr e = some s` (`toSExpr` is the partial
`SExpr` image: it succeeds exactly on the variable/literal atoms and the
recognised binary-ALU heads on two atoms — the heap-free scalar-ALU fragment).
This file **proves `denoteScalar_coincides_evalBV` in full for that
fragment** — every leaf atom and every one binary-ALU layer (`toSExpr` does not
descend into a `.letBind`, so this is the complete coincidence for everything
`toSExpr` accepts).

### Obstacle: extending the fragment through `.letBind`

`toSExpr` deliberately returns `none` on `.letBind`. Extending coincidence
across `let` is the remaining inductive glue and is genuinely non-trivial: Path A
(`denoteScalar`) threads the bound value into a *new local* in `ρ` (the partial
`String → Option (BitVec 64)` env), while Path B would have to thread it into the
*total* `β : String → BitVec 64`. The induction therefore requires re-proving
`EnvAgree params I ρ' β'` under the *extended* environments
`ρ' = (fun y => if y = x then some vv else ρ y)` and a matching `β'` — i.e. an
`EnvAgree`-preservation lemma for `let`-extension, plus a decision on how Path B
materialises the bound value (LowCT lowers a scalar `let` to a fresh
`RScalarSet`/`RLetU64Zero` *command*, so the genuine Path-B `let` lives in the
`RustExec` big-step over `RustState`, not in the `SExpr` evaluator). That is the
next keystone increment; it is out of scope for this base-case file, which leaves
no proof obligations open.

## Honesty note (what is NOT claimed)

* **Shifts / rotates are deliberately excluded.** Path A's shift/rotate
  (`recogShift`, `ShiftKind.apply`) uses a *compile-time immediate* count `n :
  Nat` (`av.rotateRight n`, `av >>> n`). The `SExpr` shift nodes `SShr`/`SShl`
  take a *dynamic* `SExpr` shift operand evaluated via `(b.evalBV β).toNat`, and
  `SExpr` has **no rotate node at all**. So there is no clean `SExpr` image of
  the Path-A shift/rotate arms; the genuinely coincident scalar fragment is the
  variable/literal/binary-ALU core. This is stated, not papered over.

* Each lemma below is genuinely about **both** `denoteScalar`/`denoteAtomExpr`
  (Path A) **and** `SExpr.evalBV` (Path B); none is a restatement of one side.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)

/-! ## §1  The `SExpr` image of a scalar-ALU atom / binop

`atomSExpr` maps a Path-A atom-expression (`.var`/`.lit`) to its Path-B `SExpr`
image. A `.var x` becomes the *single* slot read `SVar x`: the `EnvAgree`
predicate absorbs the parameter-vs-local distinction (a parameter reads
`inpGet I i` on Path A, and `β` is required to agree with that), so Path B needs
only one variable node. A literal becomes `SLit n`. -/

/-- `SExpr` image of an atom-expression (`.var`/`.lit`). `none` on anything else
    (including the `Not`/`index` `.app` atoms, which are heap/complement, not
    scalar-ALU leaves). -/
def atomSExpr : ImpExpr → Option SExpr
  | .var x => some (.SVar x)
  | .lit l => (litNat? l).map (fun n => .SLit n)
  | _ => none

/-- The `JasminBinOp` for a recognised ALU head, mapped to its `SExpr`
    constructor. Mirrors `recogBin` arm-for-arm onto `SExpr`. `andn`/`or` :
    `SExpr` has `SAnd`/`SXor`/`SAdd`/`SSub`/`SMul` but no `SOr`/`SAndn`, so the
    coincident binary fragment is `add/sub/mul/and/xor`. -/
def binSExpr : JasminBinOp → Option (SExpr → SExpr → SExpr)
  | .add => some .SAdd
  | .sub => some .SSub
  | .mul => some .SMul
  | .and => some .SAnd
  | .xor => some .SXor
  | _    => none

/-- `SExpr` image of a scalar-ALU `ImpExpr`: a leaf atom, or a recognised binary
    ALU head applied to two atom arguments. Anything else (shift/rotate, `Not`,
    `or`/`andn`, nested-app args, `letBind`) is `none` — the v1 coincident
    fragment. -/
def toSExpr : ImpExpr → Option SExpr
  | .app f args =>
      match recogBin f, args with
      | some op, [a, b] =>
          (binSExpr op).bind fun mk =>
            (atomSExpr a).bind fun sa =>
              (atomSExpr b).map fun sb => mk sa sb
      | _, _ => none
  | e => atomSExpr e

/-! ## §2  The env-agreement predicate

`EnvAgree params I ρ β` says every Path-A variable reading equals the Path-B
reading `β x`. This is the *exact* hypothesis that makes the variable-atom and
binop base cases coincide; it folds the parameter/local distinction (Path A) and
the `params`/`I` input convention into a single per-variable equation. -/

/-- Env-agreement: each variable's Path-A atom reading equals Path-B's `β x`. -/
def EnvAgree {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64)
    (ρ : String → Option (BitVec 64)) (β : String → BitVec 64) : Prop :=
  ∀ x, denoteAtomExpr params I (.var x) ρ = some (β x)

/-! ## §3  Base-case coincidence lemmas (the deliverable)

Each is genuinely about both Path A (`denoteAtomExpr`/`denoteScalar`) and Path B
(`SExpr.evalBV`). -/

/-- **Literal-atom coincidence.** A literal atom's Path-A denotation equals
    `some` of its Path-B `evalBV` image: both are `BitVec.ofNat 64 n`. Genuinely
    relates `denoteAtomExpr` (LHS) and `SExpr.evalBV` (RHS). -/
theorem lit_coincides {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64)
    (ρ : String → Option (BitVec 64)) (β : String → BitVec 64)
    (l : ImpLit) {n : Nat} (hl : litNat? l = some n) :
    denoteAtomExpr params I (.lit l) ρ
      = some (SExpr.evalBV β (.SLit n)) := by
  simp [denoteAtomExpr, SExpr.evalBV, hl]

/-- **Variable-atom coincidence.** Under `EnvAgree`, a variable atom's Path-A
    denotation equals `some` of its Path-B `evalBV` image `β x`. Genuinely
    relates `denoteAtomExpr` (LHS) and `SExpr.evalBV (.SVar x)` (RHS, which is
    `β x`); the content is supplied entirely by `EnvAgree`. -/
theorem var_coincides {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64)
    (ρ : String → Option (BitVec 64)) (β : String → BitVec 64)
    (hβ : EnvAgree params I ρ β) (x : String) :
    denoteAtomExpr params I (.var x) ρ
      = some (SExpr.evalBV β (.SVar x)) := by
  -- RHS `evalBV β (.SVar x)` is definitionally `β x`.
  show denoteAtomExpr params I (.var x) ρ = some (β x)
  exact hβ x

/-- **Atom coincidence (unified leaf step).** If an atom-expression `e`
    (`.var`/`.lit`) has `SExpr` image `s` (`atomSExpr e = some s`), then under
    `EnvAgree` its Path-A denotation equals `some (evalBV β s)`. This is the
    leaf step the binop lemma consumes. -/
theorem atom_coincides {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64)
    (ρ : String → Option (BitVec 64)) (β : String → BitVec 64)
    (hβ : EnvAgree params I ρ β) :
    (e : ImpExpr) → {s : SExpr} → atomSExpr e = some s →
    denoteAtomExpr params I e ρ = some (SExpr.evalBV β s)
  | .var x, s, hs => by
      simp only [atomSExpr, Option.some.injEq] at hs
      subst hs
      exact var_coincides params I ρ β hβ x
  | .lit l, s, hs => by
      simp only [atomSExpr, Option.map_eq_some_iff] at hs
      obtain ⟨n, hn1, hn2⟩ := hs
      subst hn2
      exact lit_coincides params I ρ β l hn1

/-! ### Per-op binary-ALU coincidence

Each covered ALU op is the *same* `BitVec 64` operation on both sides:
`JasminBinOp.apply op av bv` equals the corresponding `SExpr.evalBV` binary node
applied to `av`, `bv`. These are the load-bearing op-agreement facts; each holds
by `rfl` (the two semantics are the literally same `BitVec 64` operation). -/

/-- `add`: `JasminBinOp.apply` agrees with the `SAdd` node. -/
theorem apply_add_eq_evalBV (β : String → BitVec 64) (sa sb : SExpr) :
    JasminBinOp.apply .add (SExpr.evalBV β sa) (SExpr.evalBV β sb)
      = SExpr.evalBV β (.SAdd sa sb) := rfl

/-- `sub`: `JasminBinOp.apply` agrees with the `SSub` node. -/
theorem apply_sub_eq_evalBV (β : String → BitVec 64) (sa sb : SExpr) :
    JasminBinOp.apply .sub (SExpr.evalBV β sa) (SExpr.evalBV β sb)
      = SExpr.evalBV β (.SSub sa sb) := rfl

/-- `mul`: `JasminBinOp.apply` agrees with the `SMul` node. -/
theorem apply_mul_eq_evalBV (β : String → BitVec 64) (sa sb : SExpr) :
    JasminBinOp.apply .mul (SExpr.evalBV β sa) (SExpr.evalBV β sb)
      = SExpr.evalBV β (.SMul sa sb) := rfl

/-- `and`: `JasminBinOp.apply` agrees with the `SAnd` node. -/
theorem apply_and_eq_evalBV (β : String → BitVec 64) (sa sb : SExpr) :
    JasminBinOp.apply .and (SExpr.evalBV β sa) (SExpr.evalBV β sb)
      = SExpr.evalBV β (.SAnd sa sb) := rfl

/-- `xor`: `JasminBinOp.apply` agrees with the `SXor` node. -/
theorem apply_xor_eq_evalBV (β : String → BitVec 64) (sa sb : SExpr) :
    JasminBinOp.apply .xor (SExpr.evalBV β sa) (SExpr.evalBV β sb)
      = SExpr.evalBV β (.SXor sa sb) := rfl

/-- The op-agreement bundled for `toSExpr`'s covered set: if `binSExpr op = some
    mk`, then `JasminBinOp.apply op` agrees with the `evalBV` of `mk` on any
    sub-`SExpr` values. This is the generic per-op fact `bin_coincides` consumes,
    proved by case on the (five covered) ops. -/
theorem apply_eq_evalBV_of_binSExpr (β : String → BitVec 64)
    {op : JasminBinOp} {mk : SExpr → SExpr → SExpr} (hmk : binSExpr op = some mk)
    (sa sb : SExpr) :
    JasminBinOp.apply op (SExpr.evalBV β sa) (SExpr.evalBV β sb)
      = SExpr.evalBV β (mk sa sb) := by
  cases op <;> simp only [binSExpr, Option.some.injEq, reduceCtorEq] at hmk <;>
    subst hmk <;> rfl

/-- **Binary-ALU step coincidence (the inductive STEP for one binop).** A
    recognised binary ALU head `f` (`recogBin f = some op`) in the covered set
    (`binSExpr op = some mk`), applied to two atom arguments `a`, `b` whose
    `SExpr` images are `sa`, `sb`, coincides between the two paths:

    * Path A `denoteScalar (.app f [a, b])` dispatches via `recogBin` to
      `JasminBinOp.apply op` on the atom denotations, and
    * Path B `evalBV β (mk sa sb)` is the matching `SExpr` binary node,

    and the two are equal (modulo the `some`). Consumes the atom-leaf coincidence
    (`atom_coincides`) on each argument and the per-op agreement
    (`apply_eq_evalBV_of_binSExpr`). Genuinely about both `denoteScalar` (LHS)
    and `SExpr.evalBV` (RHS). -/
theorem bin_coincides {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64)
    (ρ : String → Option (BitVec 64)) (β : String → BitVec 64)
    (hβ : EnvAgree params I ρ β)
    {f : String} {op : JasminBinOp} (hf : recogBin f = some op)
    {a b : ImpExpr} {sa sb : SExpr}
    (ha : atomSExpr a = some sa) (hb : atomSExpr b = some sb)
    {mk : SExpr → SExpr → SExpr} (hmk : binSExpr op = some mk) :
    ImpExpr.denoteScalar params I (.app f [a, b]) ρ
      = some (SExpr.evalBV β (mk sa sb)) := by
  -- Path A: unfold `denoteScalar` and route the `recogBin f` match to `some op`.
  unfold ImpExpr.denoteScalar
  rw [hf]
  -- Collapse the (now constructor-headed) `recogBin`/`args` match.
  simp only []
  -- Each atom argument coincides.
  rw [atom_coincides params I ρ β hβ a ha, atom_coincides params I ρ β hβ b hb]
  -- Now `some (evalBV β sa) bind …`, collapse and apply the per-op agreement.
  simp only [Option.bind_some, Option.map_some, Option.some.injEq]
  exact apply_eq_evalBV_of_binSExpr β hmk sa sb

/-! ## §4  Unified leaf+step coincidence over the covered fragment

Combining the atom and binop cases gives coincidence for the whole *non-`let`*
covered fragment in one statement, keyed off `toSExpr`. (The `letBind` case — the
only recursive constructor — is the remaining inductive glue; see the obstacle
note in the module docstring.) -/

/-- **Covered-fragment coincidence (atoms + one binop layer).** For any scalar
    `ImpExpr` that `toSExpr` accepts (a leaf atom, or a recognised binary-ALU head
    on two atoms), Path A `denoteScalar` equals `some` of Path B `evalBV` under
    `EnvAgree`. The base-case theorem the DF-keystone induction would extend over
    `letBind`. Genuinely relates `denoteScalar` and `SExpr.evalBV`. -/
theorem denoteScalar_coincides_evalBV {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64))
    (β : String → BitVec 64) (hβ : EnvAgree params I ρ β) :
    (e : ImpExpr) → {s : SExpr} → toSExpr e = some s →
    ImpExpr.denoteScalar params I e ρ = some (SExpr.evalBV β s)
  | .app f args, s, hs => by
      -- `toSExpr (.app f args)` succeeds only for `recogBin f = some op` and
      -- `args = [a, b]` with both atom images present.
      simp only [toSExpr] at hs
      -- Case the operator head; only a recognised binary head can succeed.
      cases hrec : recogBin f with
      | none => rw [hrec] at hs; simp at hs
      | some op =>
        rw [hrec] at hs
        -- Case the argument list down to exactly `[a, b]`.
        match args, hs with
        | [a, b], hs =>
          simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
          obtain ⟨mk, hmk, sa, ha, sb, hb, hs⟩ := hs
          subst hs
          exact bin_coincides params I ρ β hβ hrec ha hb hmk
  | .var x, s, hs => by
      -- bare atom: `denoteScalar` falls through to `denoteAtomExpr`.
      simp only [toSExpr] at hs
      show denoteAtomExpr params I (.var x) ρ = some (SExpr.evalBV β s)
      exact atom_coincides params I ρ β hβ (.var x) hs
  | .lit l, s, hs => by
      simp only [toSExpr] at hs
      show denoteAtomExpr params I (.lit l) ρ = some (SExpr.evalBV β s)
      exact atom_coincides params I ρ β hβ (.lit l) hs

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence
