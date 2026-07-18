/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Fe25519MulLeafGoldenPath
import CatCrypt.Crypto.SecureCompilation.Fe25519AddLeafGoldenPath

/-!
# A typed symbol-table elaborator: named-variable Jasmin-like leaf syntax over `Com`

`Fe25519OrchestrationSyntax.lean`'s `jexpr%` hides the `Expr`-record boilerplate
(`retTy_eq := rfl`, the `HVector` `.cons`/`.nil` spine) but leaves the genuinely
hard part exposed: the **typed de-Bruijn resolution**. A `Com` leaf still reads
its inputs as `.there (.there .here)` — a raw index that carries the proof its
slot has the right `JasminTy`. Writing those indices by hand is what makes a
`Com jasminDialect` leaf unreadable, and getting one wrong is a silent
mis-wiring the type-checker only catches if the two slots happen to differ in
type.

This file closes that gap with a **`kernel%` elaborator**: you name the formals
and every let-binding, and the elaborator resolves each named use to its typed
`Ctxt.Var` index. So the fe25519 multiply-accumulate column low word reads

```text
  kernel% (acc_lo : .reg 64) (acc_hi : .reg 64) (a : .reg 64) (b : .reg 64) {
    p_lo := (JasminOp.regArith .mul 64) [a, b];
    s    := (JasminOp.regArith .add 64) [acc_lo, p_lo];
    ret s
  }
```

and elaborates to **exactly** the hand-written de-Bruijn `Com`
`Fe25519MulLeaf.fe25519MacColLoCom` — witnessed by `macColKernel_eq_leaf : … = … := rfl`.

## How the resolution works (the typed symbol table)

The `Com` framework binds each `.var` result at the **front** of the context:
`Com.var (e : Expr d Γ t) (body : Com d (t :: Γ) s)`. So de-Bruijn index `0`
(`Ctxt.Var.here`) is always the most-recently-bound name, and every prior name
shifts one step deeper (`Ctxt.Var.there`). The elaborator mirrors this with a
compile-time **scope** — an `Array Name` whose position `i` is exactly the
de-Bruijn index of that name:

* the formals seed the scope in declaration order (`formals[0]` is index `0`);
* each `name := op [args…]` binding **prepends** `name` (it becomes the new
  index `0`, every existing name shifts up by one — recorded by re-indexing the
  array, `#[name] ++ scope`);
* a named use resolves to `Ctxt.Var.there^i Ctxt.Var.here` where `i` is the
  name's position in the current scope.

The **type proof rides for free on intrinsic typing.** `Ctxt.Var.here` has type
`Var (t :: Γ) t` by its constructor, so once the elaborator emits the right
*index*, Lean's checker verifies the slot type is what the op's signature
demands — a wrong index that lands on a wrong-typed slot is a type error, not a
silent bug. The elaborator therefore never manufactures a proof term; it only
computes indices, and the kernel discharges the `JasminTy` obligation.

`kernel%` is an `elab` (not a `macro`): the scope is genuine monadic state
threaded through the statement list, which a `macro`'s independent per-statement
`$[…]` expansion cannot express (each statement would expand without knowing the
accumulated scope). See §"Dialect-genericity" at the foot of the file.

## What is proved (0 sorries, no new axioms)

* `macColKernel_eq_leaf` — the named multiply-accumulate column low word
  elaborates to **exactly** `Fe25519MulLeaf.fe25519MacColLoCom`, by `rfl`.
* `addLimbKernel_eq_leaf` — the named per-limb field add elaborates to **exactly**
  `Fe25519AddLeaf.fe25519Add51LimbCom`, by `rfl`. This one exercises a second op
  (`stackLoad`) and a mixed context (`stackArr` + `reg`), so the resolution is
  shown faithful across ops and types, not just for one shape.

Both are `rfl` against the deployed golden-path leaves — the named notation adds
readability and index-safety with **no new trust**: the elaborated term is
definitionally the hand-authored one.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519KernelSyntax

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open Lean Lean.Elab Lean.Elab.Term

/-! ## 1. The surface grammar

A `kernel%` program is a sequence of typed formals, then a `{ … }` body of
`;`-separated statements. Each non-final statement is a let-binding
`name := op [arg, …]`; the final statement is `ret name`. The op is a full
term (parenthesised so `term:max` reads it as one atom); the args are the
names of formals or earlier bindings. Both are **dialect-agnostic**: the
elaborator never inspects the op or the types, only the names. -/

/-- A typed formal parameter `(name : ty)`. `ty` is any term of the dialect's
    `Ty` (e.g. `.reg 64`, `.stackArr 64 5` for `jasminDialect`). -/
declare_syntax_cat kformal
syntax "(" ident " : " term ")" : kformal

/-- A kernel statement: either a let-binding `name := op [args…]` or the final
    `ret name`. -/
declare_syntax_cat kstmt
/-- Let-binding: bind `name` to `op` applied to the named `args`. -/
syntax (name := kbind) ident " := " term:max "[" ident,* "]" : kstmt
/-- Terminal return of a named value. -/
syntax (name := kret) "ret " ident : kstmt

/-! ## 2. The elaborator (the typed symbol table)

The four helpers below are dialect-agnostic — they only compute de-Bruijn
indices from names and emit the dialect-parametric `Ctxt.Var` / `HVector` /
`Expr.mk` / `Com` constructors. -/

/-- Resolve a named use to its typed de-Bruijn `Ctxt.Var`. The name's position
    `i` in `scope` is its de-Bruijn index, so this emits
    `Ctxt.Var.there^i Ctxt.Var.here`. The `JasminTy` proof is discharged by
    intrinsic typing when the emitted index is checked against the context. -/
private def resolveVar (scope : Array Name) (nm : Name) : TermElabM (TSyntax `term) := do
  match scope.findIdx? (· == nm) with
  | none => throwError "kernel%: unbound variable `{nm}`"
  | some i => do
    let mut v ← `(Ctxt.Var.here)
    for _ in [0:i] do
      v ← `(Ctxt.Var.there $v)
    return v

/-- Build the `HVector` argument spine `.cons a₀ (.cons a₁ … .nil)`. -/
private def mkHVector (vs : List (TSyntax `term)) : TermElabM (TSyntax `term) := do
  let mut acc ← `(HVector.nil)
  for v in vs.reverse do
    acc ← `(HVector.cons $v $acc)
  return acc

/-- Fold the statement list into a `Com`, threading the compile-time scope.
    A binding prepends its name to the scope (new index `0`); `ret` emits the
    return of the resolved var. -/
private partial def buildCom (scope : Array Name) : List Syntax → TermElabM (TSyntax `term)
  | [] => throwError "kernel%: empty body"
  | [s] =>
    if s.isOfKind ``kret then do
      let nm := s.getArgs[1]!.getId
      let v ← resolveVar scope nm
      `(Com.ret $v)
    else
      throwError "kernel%: body must end with `ret name`"
  | s :: rest =>
    if s.isOfKind ``kbind then do
      let nm := s.getArgs[0]!.getId
      let opStx : TSyntax `term := ⟨s.getArgs[2]!⟩
      -- args are `ident,*` at position 4; `.getSepArgs` drops the `,` separators
      let argIdents := s.getArgs[4]!.getArgs.filter (·.getKind == identKind)
      let argVars ← argIdents.toList.mapM (fun x => resolveVar scope x.getId)
      let hv ← mkHVector argVars
      -- new binding is index 0; existing names shift one deeper
      let body ← buildCom (#[nm] ++ scope) rest
      `(Com.var (Expr.mk $opStx rfl $hv) $body)
    else
      throwError "kernel%: only the last statement may be `ret name`"

/-- `kernel% (n₁ : ty₁) … { s₁; …; ret r }` — a named-variable straight-line
    `Com` leaf. Parses the typed formals into the initial scope (declaration
    order = de-Bruijn order), builds the `Com` with `buildCom`, ascribes the
    explicit formal context (so the de-Bruijn indices type-check
    deterministically), and elaborates. Every named use resolves to its typed
    de-Bruijn `Ctxt.Var`. -/
elab (name := kernelStx) "kernel% " fs:kformal+ "{" ss:sepBy1(kstmt, ";") "}" : term
    <= expectedType => do
  -- The formal *names* seed the scope in declaration order (= de-Bruijn order).
  -- The formal *types* are surface documentation; the authoritative context `Γ`
  -- (and the dialect) is read from the expected `Com d Γ t` type below.
  let formalNames : Array Name := fs.map (fun f => f.raw.getArgs[1]!.getId)
  let stmts := ss.getElems.toList.map (·.raw)
  let comTerm ← buildCom formalNames stmts
  -- Elaborate the `Com` term against the expected `Com d Γ t`: `Γ` pins every
  -- resolved `.here`/`.there` index to its slot type (the typed de-Bruijn proof),
  -- and `d` is fixed by the expected type — no dialect-specific reasoning here.
  elabTerm comTerm (some expectedType)

/-! ## 3. The payoff — named notation elaborates to the hand-written leaves, by `rfl` -/

/-- The fe25519 multiply-accumulate column low word, in named form. Compare
    `Fe25519MulLeaf.fe25519MacColLoCom`, whose body spells the same wiring as
    `.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)`. -/
def macColKernel : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  kernel% (acc_lo : .reg 64) (acc_hi : .reg 64) (a : .reg 64) (b : .reg 64) {
    p_lo := (JasminOp.regArith .mul 64) [a, b];
    s    := (JasminOp.regArith .add 64) [acc_lo, p_lo];
    ret s
  }

/-- **The elaborator is faithful — `rfl`.** The named multiply-accumulate column
    low word elaborates to **exactly** the hand-authored golden-path leaf; the
    symbol table resolved `a`, `b`, `acc_lo`, `p_lo`, `s` to precisely the
    de-Bruijn indices the hand-written `Com` spells out. -/
theorem macColKernel_eq_leaf :
    macColKernel = Fe25519MulLeaf.fe25519MacColLoCom := rfl

/-- The fe25519 per-limb field add, in named form. Two `stackLoad`s over a mixed
    `stackArr`/`reg` context plus a `regArith .add` — exercises the resolution
    across a second op and heterogeneous slot types. Compare
    `Fe25519AddLeaf.fe25519Add51LimbCom`. -/
def addLimbKernel : Com jasminDialect [.stackArr 64 5, .stackArr 64 5, .reg 64] (.reg 64) :=
  kernel% (A : .stackArr 64 5) (B : .stackArr 64 5) (i : .reg 64) {
    ai := (JasminOp.stackLoad 64 5) [A, i];
    bi := (JasminOp.stackLoad 64 5) [B, i];
    s  := (JasminOp.regArith .add 64) [ai, bi];
    ret s
  }

/-- **The elaborator is faithful across ops and mixed types — `rfl`.** The named
    per-limb field add elaborates to **exactly** `fe25519Add51LimbCom`. `A`, `B`,
    `i` resolve to their `stackArr`/`reg` slots and `ai`, `bi`, `s` to their
    binding indices, matching the hand-written de-Bruijn leaf. -/
theorem addLimbKernel_eq_leaf :
    addLimbKernel = Fe25519AddLeaf.fe25519Add51LimbCom := rfl

/-! ## 4. Dialect-genericity

The elaborator is **already dialect-generic**: `resolveVar`, `mkHVector`,
`buildCom`, and `elabKernel` never mention `jasminDialect`, `JasminTy`, or
`JasminOp`. They compute de-Bruijn indices from names, emit `Ctxt.Var` /
`HVector` / `Expr.mk` / `Com.var` / `Com.ret` (all dialect-parametric), and
ascribe `Com _ [tys…] _` with the dialect `d` left to inference. The op terms
and formal types are opaque payloads copied verbatim into the output.

To reuse `kernel%` for another `Com` dialect, nothing in this file changes: the
caller writes the other dialect's op terms and `Ty` values in the same surface
positions (e.g. `(x : .someTy)` and `(SomeOp.foo …) [args]`), and the ascription
`Com _ [tys…] _` picks up that dialect from the expected type or the ops. The
only jasmin-specific content here is §3's *examples* (the two witnesses against
the jasmin leaves), not the elaborator. A future refactor could lift the four
private helpers into a shared `VIR/KernelSyntax.lean`; they are written so that
move is a copy, not a rewrite. -/

end CatCrypt.Crypto.SecureCompilation.Fe25519KernelSyntax
