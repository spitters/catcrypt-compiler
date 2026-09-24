/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness

/-!
# A denotation-preserving instruction-selection rewrite over `Com jasminDialect`

`ArithIselSoundness.lean` proves, at the *value* (`BitVec`) level, that each native
x86 op equals its neutral-arith idiom (`andn_eq_andnot`,
`mulhi_eq_mulHiW`, `rorImm_eq_shiftOr`, `select_eq_maskSelect`). Those equivalences
license instruction selection: the legalizer may emit the faster native op in place
of the always-valid emulation **without changing the denotation**. This file lifts
that licence to an actual program transform — a `Com jasminDialect → Com jasminDialect`
rewrite — and proves the transform is denotation-preserving (`iselCom_denote`).

## What this pass selects (the clean, same-shape case)

The pass walks a `Com jasminDialect` and applies a **same-shape** `Expr`-level
rewrite at each binding: it canonicalizes the operand order of a **commutative**
register binop (`add`/`mul`/`and`/`or`/`xor`) — `regArith op ⟨a, b⟩ ↦ regArith op ⟨b, a⟩`.
This is a legitimate ISel canonicalization (it normalizes towards a target's
preferred operand order, e.g. to expose a two-address `dst = dst OP src` form), it
is a single-`Expr`-to-single-`Expr` swap (no node-count change), and its
denotation-preservation is exactly the `BitVec` commutativity of the op — the same
kind of value-level identity the `ArithIselSoundness` lemmas package. We lift it to
`Expr.denote` (`iselExpr_denote`) and to `Com.denote` (`iselCom_denote`) by `Com`
induction.

The headline theorem is `iselCom_denote : (iselCom c).denote V = c.denote V`: the
ISel pass never affects the value a program computes. Correctness is therefore
*independent* of the pass — the reading where native-op / canonical-form
selection is a perf-only choice below the `llvm` waist.

## What needs a multi-op rewrite (documented, out of this simple pass's scope)

The headline native-op selections from `ArithIselSoundness` are **not** single-`Expr`
swaps in `Com jasminDialect`; each rewrites an emulation *subtree* of several ops to
one native op (a node-count-changing transform that must thread fresh de-Bruijn
bindings), which a single-`Expr` map cannot express:

* **ANDN** (`andn_eq_andnot`): the and-not emulation is `xori; andi` (two bindings)
  collapsing to one `regArith .andn` — and the native op *transposes* the operands
  (`(~~~a) &&& b` vs the emulation's `a &&& ~~~b`), so the swap also reorders args.
* **CMOV / SELECT** (`select_eq_maskSelect`): the masked-select emulation
  `(x &&& c) ||| (y &&& ~~~c)` is a four-op subtree, and the native `select` op
  *materialises* a 1-bit condition from the full mask `c` (a representation change,
  not a re-spelling) — so the rewrite both collapses nodes and changes the operand
  representation.
* **ROR** (`rorImm_eq_shiftOr`): the rotate emulation `(a >>> n) ||| (a <<< (w-n))`
  is a three-op `shr; shl; or` subtree collapsing to one `rorImm` — node-count change.
* **MULX-hi** (`mulhi_eq_mulHiW`): `mulhi` *is* the neutral widening-hi value
  definitionally, but it has no neutral single-op image in `jasminDialect` to swap
  *from* — its emulation lives in the `arith` dialect.

These multi-op (subtree-collapsing / operand-materialising) selections are outside
this pass; the value-level soundness for each is discharged in
`ArithIselSoundness`. This pass establishes the denotation-preserving rewrite
*framework* (the structural `Com` recursion + the `Expr.denote` lift) on the cleanest
same-shape case, so the multi-op extensions reuse the same preservation skeleton.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselPass

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Commutative register binops

The pass canonicalizes operand order only for the binops whose `apply` is
commutative; for every other op it is the identity. -/

/-- The register binops with a commutative `apply` (`a OP b = b OP a` at every
    width). Operand-order canonicalization is denotation-preserving exactly for
    these. -/
def binOpIsComm : JasminBinOp → Bool
  | .add => true
  | .mul => true
  | .and => true
  | .or  => true
  | .xor => true
  | _ => false

/-- **Commutativity of a flagged binop.** For every op `binOpIsComm op` accepts,
    `op.apply a b = op.apply b a` at every width — the value-level fact that makes
    operand-order canonicalization denotation-preserving. -/
theorem binOp_apply_comm {w : Nat} (op : JasminBinOp)
    (h : binOpIsComm op = true) (a b : BitVec w) :
    op.apply a b = op.apply b a := by
  cases op <;> simp_all [binOpIsComm, JasminBinOp.apply,
    BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm,
    BitVec.xor_comm]

/-! ## 2. Argument-order swap for a binary `Expr`

For a `regArith op w` expression whose op is commutative, swap its two operand
variables; otherwise return the expression unchanged. The swap is same-shape (the
op and its `[reg w, reg w]` signature are unchanged — only the two `Var`s in the
arg `HVector` are transposed), so no de-Bruijn re-threading is needed.

We isolate the operand transpose as `swapArgs` over the binary signature
`[reg w, reg w]` (a clean structural `HVector` swap), and have `iselExpr` dispatch
only on `e.op` — keeping its `match` free of the dependent-`HVector` pattern that
defeats equation-lemma generation. -/

/-- Transpose the two operand variables of a binary `[reg w, reg w]` argument
    vector. -/
def swapArgs {Γ : Ctxt jasminDialect} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var Γ ty) [JasminTy.reg w, JasminTy.reg w]) :
    HVector (fun ty => Ctxt.Var Γ ty) [JasminTy.reg w, JasminTy.reg w] :=
  .cons args.tail.head (.cons args.head .nil)

/-- The operand-order ISel rewrite on a single jasmin expression. On a commutative
    `regArith` op it transposes the two argument variables (`swapArgs`); on every
    other op it is the identity. The `match` is on `e.op` only, so the
    arg-`HVector` is handled through `swapArgs`/the structure update rather than a
    dependent pattern. -/
def iselExpr {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Expr jasminDialect Γ t :=
  match e.op, e.retTy_eq, e.args with
  | .regArith op w, h, args =>
      if binOpIsComm op = true then
        { op := .regArith op w, retTy_eq := h, args := swapArgs args }
      else
        { op := .regArith op w, retTy_eq := h, args := args }
  | _, _, _ => e

/-! ## 3. Denotation preservation for `iselExpr` -/

/-- **`iselExpr` is denotation-preserving.** The operand-order canonicalization
    computes the same value on every valuation: the commutative case is closed by
    `binOp_apply_comm`, every other case is syntactically the identity. -/
theorem iselExpr_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (iselExpr e).denote V = e.denote V := by
  rcases e with ⟨op, h, args⟩
  cases op with
  | regArith bop w =>
      match args with
      | .cons a (.cons b .nil) =>
          subst h
          simp only [iselExpr]
          by_cases hc : binOpIsComm bop = true
          · rw [if_pos hc]
            simp only [Expr.denote, swapArgs, HVector.head, HVector.tail]
            show jasminDenote.denote (.regArith bop w) _
              = jasminDenote.denote (.regArith bop w) _
            exact binOp_apply_comm bop hc _ _
          · rw [if_neg hc]
  | _ => rfl

/-! ## 4. Lift the rewrite structurally to `Com` -/

/-- The ISel pass on a whole program: apply `iselExpr` at every let-binding,
    leaving the control structure unchanged. -/
def iselCom {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | .ret v => .ret v
  | .var e body => .var (iselExpr e) (iselCom body)

/-- **Headline: the ISel pass is denotation-preserving.** `iselCom` never changes
    the value a program computes — at each binding the rewritten expression denotes
    equally (`iselExpr_denote`), so the bound valuation is unchanged and the `Com`
    recursion carries the equality through. Hence native-op / canonical-form
    instruction selection is a perf-only transform, never correctness-critical. -/
theorem iselCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (iselCom c).denote V = c.denote V := by
  induction c with
  | ret v => rfl
  | var e body ih =>
      simp only [iselCom, Com.denote]
      rw [iselExpr_denote e V]
      exact ih _

/-! ## 5. Worked example

A two-op program `s = a + b; t = a + s; ret t` over `[reg 32, reg 32]`. The pass
canonicalizes both commutative `add`s to swapped operand order; the headline
theorem guarantees the rewritten program denotes identically. -/

/-- Worked source program: `let s = a + b; let t = a + s; ret t`. -/
def exampleProg : Com jasminDialect [.reg 32, .reg 32] (.reg 32) :=
  .var (.mk (.regArith .add 32) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.var (.mk (.regArith .add 32) rfl
            (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- The ISel pass preserves the worked example's denotation on every input. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32, .reg 32]) :
    (iselCom exampleProg).denote V = exampleProg.denote V :=
  iselCom_denote exampleProg V

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselPass
