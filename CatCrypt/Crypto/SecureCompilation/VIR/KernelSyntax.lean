/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# `kernel%` — a dialect-generic typed symbol-table elaborator for `Com` leaves

This module is the **reusable** home of the `kernel%` surface: a named-variable
concrete syntax that elaborates to an intrinsically-typed `Com` leaf for **any**
`Com` dialect. It is the shared, end-state form of the elaborator prototyped in
`Fe25519KernelSyntax.lean` (which stays as a transition artifact).

A `Com` leaf reads its inputs as typed de-Bruijn `Ctxt.Var`s — `.there (.there
.here)` — a raw index that also carries the proof its slot has the right dialect
`Ty`. Writing those indices by hand is what makes a `Com` leaf unreadable, and a
wrong index is a silent mis-wiring the type-checker catches only when the two
slots differ in type. `kernel%` closes that gap: you name the formals and every
let-binding, and the elaborator resolves each named use to its typed `Ctxt.Var`.
So a multiply-accumulate column low word reads

```text
  kernel% (acc_lo : .reg 64) (acc_hi : .reg 64) (a : .reg 64) (b : .reg 64) {
    p_lo := (JasminOp.regArith .mul 64) [a, b];
    s    := (JasminOp.regArith .add 64) [acc_lo, p_lo];
    ret s
  }
```

## Dialect-genericity (why this module is reusable)

`resolveVar`, `mkHVector`, `buildCom`, and the `kernel%` elaborator **never**
mention `jasminDialect`, `JasminTy`, or `JasminOp`. They compute de-Bruijn
indices from names and emit only the dialect-parametric constructors
`Ctxt.Var.here` / `.there`, `HVector.cons` / `.nil`, `Expr.mk`, `Com.var`,
`Com.ret`. The op terms and formal `Ty` values are opaque payloads copied
verbatim into the output; the dialect `d` and context `Γ` are read from the
expected `Com d Γ t` type at the elaboration site.

**To reuse `kernel%` for another dialect, nothing in this file changes.** The
caller writes that dialect's op terms and `Ty` values in the same surface
positions (`(x : .someTy)` and `(SomeOp.foo …) [args]`) and ascribes the result
`Com _ [tys…] _`; the ascription pins the dialect. §2 keeps a **jasmin
instantiation demo** — the only dialect-specific content in the file.

## How the resolution works (the typed symbol table)

`Com` binds each `.var` result at the **front** of the context: `Com.var (e :
Expr d Γ t) (body : Com d (t :: Γ) s)`. So de-Bruijn index `0` (`Ctxt.Var.here`)
is always the most-recently-bound name, and every prior name shifts one step
deeper (`Ctxt.Var.there`). The elaborator mirrors this with a compile-time
**scope** — an `Array Name` whose position `i` is the de-Bruijn index of that
name:

* the formals seed the scope in declaration order (`formals[0]` is index `0`);
* each `name := op [args…]` binding **prepends** `name` (it becomes the new
  index `0`, every existing name shifts up by one — `#[name] ++ scope`);
* a named use resolves to `Ctxt.Var.there^i Ctxt.Var.here`.

The **type proof rides for free on intrinsic typing.** `Ctxt.Var.here` has type
`Var (t :: Γ) t` by its constructor, so once the elaborator emits the right
*index*, Lean's checker verifies the slot type is what the op's signature
demands. The elaborator therefore never manufactures a proof term; it computes
indices only, and intrinsic typing discharges the `Ty` obligation.

`kernel%` is an `elab` (not a `macro`): the scope is genuine monadic state
threaded through the statement list, which a `macro`'s independent per-statement
`$[…]` expansion cannot express.

## Establishing trust ONCE, not per-program

The `kernel%` surface is a **transparent AST builder**. Its correctness is
established by the **fixed elaborator-regression suite** in §2 — a small set of
`kernel% X = <hand-written Com> := rfl` witnesses on distinct op/type shapes.
Those `rfl`s test *the elaborator*, once. They are **not** meant to be repeated
per authored program: once the elaborator is trusted, a leaf is written
`def foo := kernel% (…){ … }` directly and needs no `= raw-AST` twin (the surface
IS the definition). See `Fe25519TwoLanguageProgram.lean` for that end state.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax

open CatCrypt.Crypto.SecureCompilation.VIR
open Lean Lean.Elab Lean.Elab.Term

/-! ## 1. The surface grammar + the dialect-generic elaborator

A `kernel%` program is a sequence of typed formals, then a `{ … }` body of
`;`-separated statements. Each non-final statement is a let-binding
`name := op [arg, …]`; the final statement is `ret name`. The op is a full term
(parenthesised so `term:max` reads it as one atom); the args are names of
formals or earlier bindings. Everything below is dialect-agnostic — the
elaborator inspects only names, never ops or types. -/

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

/-- Resolve a named use to its typed de-Bruijn `Ctxt.Var`. The name's position
    `i` in `scope` is its de-Bruijn index, so this emits
    `Ctxt.Var.there^i Ctxt.Var.here`. The typing proof is discharged by
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
    `Com` leaf, for **any** `Com` dialect. Parses the typed formals into the
    initial scope (declaration order = de-Bruijn order), builds the `Com` with
    `buildCom`, and elaborates against the expected `Com d Γ t`: `Γ` pins every
    resolved `.here`/`.there` index to its slot type (the typed de-Bruijn proof)
    and `d` is fixed by the expected type — no dialect-specific reasoning. -/
elab (name := kernelStx) "kernel% " fs:kformal+ "{" ss:sepBy1(kstmt, ";") "}" : term
    <= expectedType => do
  let formalNames : Array Name := fs.map (fun f => f.raw.getArgs[1]!.getId)
  let stmts := ss.getElems.toList.map (·.raw)
  let comTerm ← buildCom formalNames stmts
  elabTerm comTerm (some expectedType)

/-! ## 2. Jasmin instantiation demo + the fixed elaborator-regression suite

The only dialect-specific content in this file. The two witnesses below pin
`kernel%` at `jasminDialect` against hand-written `Com` leaves on **distinct**
op/type shapes (a `mul`+`add` register kernel; a `stackLoad`×2 + `add` kernel
over a mixed `stackArr`/`reg` context). These are the elaborator's test suite —
they establish, ONCE, that the symbol table resolves names to the exact typed
de-Bruijn indices a hand-written leaf spells out. Authored programs do not
repeat this. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- Hand-written target: the multiply-accumulate column low word
    `p_lo := a * b ; s := acc_lo + p_lo ; ret s` over `[acc_lo, acc_hi, a, b]`. -/
def macColHand : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  .var { op := .regArith .mul 64, retTy_eq := rfl,
         args := .cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil) }
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here))

/-- The same kernel authored through `kernel%`. -/
def macColKernel : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  kernel% (acc_lo : .reg 64) (acc_hi : .reg 64) (a : .reg 64) (b : .reg 64) {
    p_lo := (JasminOp.regArith .mul 64) [a, b];
    s    := (JasminOp.regArith .add 64) [acc_lo, p_lo];
    ret s
  }

/-- **Elaborator regression (shape 1) — `rfl`.** `kernel%` resolves `a`, `b`,
    `acc_lo`, `p_lo`, `s` to exactly the de-Bruijn indices the hand-written leaf
    spells out. -/
theorem macColKernel_eq_hand : macColKernel = macColHand := rfl

/-- Hand-written target: the per-limb field add `ai := A[i] ; bi := B[i] ;
    s := ai + bi ; ret s` over `[A : stackArr 64 5, B : stackArr 64 5, i : reg 64]`. -/
def addLimbHand : Com jasminDialect [.stackArr 64 5, .stackArr 64 5, .reg 64] (.reg 64) :=
  .var { op := .stackLoad 64 5, retTy_eq := rfl,
         args := .cons .here (.cons (.there (.there .here)) .nil) }
  (.var { op := .stackLoad 64 5, retTy_eq := rfl,
          args := .cons (.there (.there .here))
                    (.cons (.there (.there (.there .here))) .nil) }
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))

/-- The same kernel authored through `kernel%`. -/
def addLimbKernel : Com jasminDialect [.stackArr 64 5, .stackArr 64 5, .reg 64] (.reg 64) :=
  kernel% (A : .stackArr 64 5) (B : .stackArr 64 5) (i : .reg 64) {
    ai := (JasminOp.stackLoad 64 5) [A, i];
    bi := (JasminOp.stackLoad 64 5) [B, i];
    s  := (JasminOp.regArith .add 64) [ai, bi];
    ret s
  }

/-- **Elaborator regression (shape 2) — `rfl`.** A second op (`stackLoad`) over a
    mixed `stackArr`/`reg` context: the resolution is faithful across ops and
    heterogeneous slot types, not just for one shape. -/
theorem addLimbKernel_eq_hand : addLimbKernel = addLimbHand := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax
