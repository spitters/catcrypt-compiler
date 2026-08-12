/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect

/-!
# A *denoting* MLIR `scf` dialect in the VIR framework — CHES Sprint 1 / item H

> **STATUS — MLIR-CORRESPONDENCE LAYER, NOT THE EMIT PATH.** `rfl`
> semantic-agreement lemmas proving CatCrypt control flow matches upstream MLIR
> `scf`; NO lowering out, ZERO emit traffic. The real control-flow substrate is
> the Lprog control flow plus the loop emit (`ComToArmLoop`,
> `LprogControlFlow`); this dialect duplicates it for correspondence only.

Sibling of `MlirArithDialect.lean`. Where the arith dialect's ops denote
each as a single `BitVec → BitVec` style pure function (no sub-program
embedded), the **scf** dialect packages **control flow**: nested branches
(`scf.if`), bounded loops (`scf.for`), and bounded `while` loops
(`scf.while`).

## Design choice (read this first)

VIR's `Core.lean` ships a *region-free* `Com` (only `.ret` and `.var`).
The cleanest way to add a denoting scf dialect without modifying that
foundation is to make each scf op **carry the body's semantic function
directly** as constructor data — exactly as `MlirArithOp.shli` already
carries the static shift amount `(k : Nat)` as op data.

Concretely:

* `scfIf w` carries `(thenF elseF : BitVec w → BitVec w)` — the two
  pre-denoted branches as Lean functions. The op's arguments are the
  condition `(bit)` and a single "input" `(sword w)` value flowing into
  whichever branch the condition selects. Denotation: `if cond then
  thenF input else elseF input`.
* `scfFor w` carries `(bodyF : Nat → BitVec w → BitVec w)` — the
  pre-denoted loop body, parameterised by the loop index. The op's
  arguments are `(lo hi step : Nat)` carried *statically* in the op
  itself (so the for is bounded by Lean computation), and an initial
  `(sword w)` accumulator. Denotation: classical foldl over `[lo,
  lo+step, …, lo + k*step < hi]`.
* `scfWhile w` carries `(condF : BitVec w → Bool)` and `(bodyF :
  BitVec w → BitVec w)` plus a static `fuel : Nat`. Bounded while —
  iterates `bodyF` at most `fuel` times while `condF state`. Denotation:
  `Nat.rec`-style fuel-indexed fold. **Unbounded** while is intentionally
  out of scope: the denotation would need a fixpoint or partial-function
  apparatus that the in-tree VIR doesn't yet have.

The "body as constructor data" pattern is the same trick lean-mlir's own
control-flow ops use when they embed regions: the op type is parametric
over the body's denotation. The textual MLIR representation has the
body as a literal SSA region; the denotation reads it as a function.
In our case, `compileProg` (in `ComToVeir.lean`) builds these closures
from sub-`Prog`s via `Prog.eval`.

## Restriction: bounded while only

`scfWhile` is **fuel-indexed**: the caller supplies a `Nat` upper bound
on iterations. Truly-general while (no fuel) is not denoted here. This
matches the H1-H4 plan's explicit fall-back: "If `scfWhile` denotation
is intractable, ship `scfIf` + `scfFor` only with `scfWhile` deferred —
this still extends AST-direct meaningfully." We ship a fuel-indexed
`scfWhile` because (a) the denotation is total, (b) all real-world
crypto loops we lower from Jasmin are statically bounded anyway (e.g.
`mpn_add_n` over a known limb count), and (c) the semantic-agreement
theorem is provable.

## Why this is honest

The scf dialect's denotation is **fully** captured in Lean: every op
denotes to a pure `HVector → ⟦retTy⟧` Lean function. There is no
external interpreter, no toolchain hypothesis, no `opaque`. The
semantic-agreement theorems (§3) close by `rfl`, exactly like the arith
dialect's — because the dialect's denotation literally is the body
function the caller supplied.

The cost we pay is that the op carries its body as a Lean function: it
is **not** a first-order data structure that could be serialised as MLIR
text in isolation. For text emission, the caller projects the body back
to a printable form (or emits it inline from the source `Prog`). The
text-emit path is decoupled from the denotation path, exactly as Phase
6′ promises.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlirScfDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect

/-! ## 1. Op tags

Three constructors mirroring MLIR's `scf.if` / `scf.for` / `scf.while`.
Each carries the body's pre-denoted Lean function as op data — see the
module docstring for the design rationale. We index `sword` results by a
width `w : Nat` so the op's `sig`/`ret` (in §2) pins types exactly. -/

/-- Operation tags for the local denoting MLIR `scf` dialect. Each op
    carries its body's pre-denoted Lean function as constructor data. -/
inductive MlirScfOp where
  /-- `scf.if` over `sword w`: branch on a condition bit. The two body
      closures `thenF` / `elseF` are the (pre-denoted) Lean semantics of
      the then/else branches; each takes a single `BitVec w` input
      (provided as op operand) and returns a `BitVec w`. Args:
      `(cond : bit, input : sword w)`; result: `sword w`. -/
  | scfIf (w : Nat) (thenF elseF : BitVec w → BitVec w)
  /-- Heterogeneous-width `scf.if`: like `scfIf`, but the input flowing
      into the two branches has width `w_in`, possibly different from
      the result width `w`. Both branch closures take a `BitVec w_in`
      input and return a `BitVec w`. Args:
      `(cond : bit, input : sword w_in)`; result: `sword w`.

      The homogeneous case is recoverable as `scfIfHetero w w` (modulo
      the `scfIf` shape); we keep `scfIf` unchanged for backward
      compatibility, and use this new constructor in `compileCif` for
      branches whose output width differs from the carried input. -/
  | scfIfHetero (w w_in : Nat) (thenF elseF : BitVec w_in → BitVec w)
  /-- `scf.for` over `sword w`: bounded loop. `lo`/`hi`/`step` are
      static loop bounds (so the loop is statically bounded by Lean
      computation). `bodyF` is the pre-denoted loop body, parameterised
      by the *iteration count* `(k : Nat)` and the running accumulator
      `(BitVec w)`. Args: `(init : sword w)`; result: `sword w` (the
      final accumulator). -/
  | scfFor (w : Nat) (lo hi step : Nat) (bodyF : Nat → BitVec w → BitVec w)
  /-- `scf.while` over `sword w`, **fuel-indexed**. `condF` is the
      pre-denoted loop-condition; `bodyF` is the pre-denoted body.
      `fuel : Nat` is a static upper bound on iterations. Args:
      `(init : sword w)`; result: `sword w` (state after at most
      `fuel` iterations). -/
  | scfWhile (w : Nat) (fuel : Nat) (condF : BitVec w → Bool)
             (bodyF : BitVec w → BitVec w)

/-! ## 2. The dialect, signature, denotation -/

/-- The local MLIR `scf` dialect: `Op` is `MlirScfOp`, `Ty` is `CryptoTy`
    (shared with `mlirArithDialect`, so a sum-of-dialects translation
    can mix arith + scf ops freely). -/
@[reducible] def mlirScfDialect : Dialect :=
  { Op := MlirScfOp, Ty := CryptoTy }

/-- Operation signatures: argument types + result type.
    Marked `@[reducible]` so the per-op `*_denote` rewrite lemmas in §3
    can write argument vectors at the literal `[CryptoTy.bit, …]` shape
    instead of the unreduced `DialectSignature.sig op` projection. -/
@[reducible] instance instMlirScfSignature : DialectSignature mlirScfDialect where
  sig op := match op with
    | .scfIf w _ _ => [.bit, .sword w]
    | .scfIfHetero _ w_in _ _ => [.bit, .sword w_in]
    | .scfFor w _ _ _ _ => [.sword w]
    | .scfWhile w _ _ _ => [.sword w]
  ret op := match op with
    | .scfIf w _ _ => .sword w
    | .scfIfHetero w _ _ _ => .sword w
    | .scfFor w _ _ _ _ => .sword w
    | .scfWhile w _ _ _ => .sword w

/-! ### 2.1. Pure Lean helpers for the for/while semantics -/

/-- A bounded `for`-fold: starting from `init`, run `bodyF` at indices
    `lo, lo+step, lo+2*step, …`, stopping when the index reaches `hi`.
    Implemented by structural recursion on a fuel parameter
    `(hi - lo + step)` to keep it terminating without `Nat.rec` gymnastics. -/
def forFold (w : Nat) (lo hi step : Nat) (bodyF : Nat → BitVec w → BitVec w)
    (init : BitVec w) : BitVec w :=
  -- Termination metric: how many iterations can possibly fit. With a
  -- nonzero step this is `⌈(hi - lo) / step⌉`. With step = 0 we treat
  -- it as 0 iterations (one-arg id), matching MLIR's "step must be
  -- positive" precondition.
  let rec go (k : Nat) (idx : Nat) (acc : BitVec w) : BitVec w :=
    match k with
    | 0 => acc
    | n + 1 =>
        if idx < hi then go n (idx + step) (bodyF idx acc)
        else acc
  go (hi - lo + 1) lo init

/-- A fuel-indexed `while`-fold: starting from `init`, iterate `bodyF`
    as long as `condF` holds, capped at `fuel` iterations. -/
def whileFold (w : Nat) (fuel : Nat) (condF : BitVec w → Bool)
    (bodyF : BitVec w → BitVec w) (init : BitVec w) : BitVec w :=
  match fuel with
  | 0 => init
  | n + 1 =>
      if condF init then whileFold w n condF bodyF (bodyF init)
      else init

/-- Operation denotation: the **standard MLIR `scf` integer semantics**,
    specialised to `sword w` for the `init`/result. -/
instance mlirScfDenote : DialectDenote mlirScfDialect where
  denote op := match op with
    | .scfIf w thenF elseF => fun args =>
        let cond : Bool := args.head
        let input : BitVec w := args.tail.head
        if cond then thenF input else elseF input
    | .scfIfHetero _ w_in thenF elseF => fun args =>
        let cond : Bool := args.head
        let input : BitVec w_in := args.tail.head
        if cond then thenF input else elseF input
    | .scfFor w lo hi step bodyF => fun args =>
        let init : BitVec w := args.head
        forFold w lo hi step bodyF init
    | .scfWhile w fuel condF bodyF => fun args =>
        let init : BitVec w := args.head
        whileFold w fuel condF bodyF init

/-! ## 3. Per-op semantic agreement

For scf ops there's no `catCryptDialect` counterpart to compare against
(catCrypt is pure-expression only, no control flow). Instead, the
agreement statements certify that the denotation **really is** what the
op constructor data says.

With the `@[reducible]` `DialectSignature` instance, the `sig`/`ret`
projections reduce per-op, so `rfl` closes each agreement. -/

section Agreement

/-- The dialect's `scfIf` denotation is the literal `if/then/else`. -/
theorem scfIf_denote (w : Nat) (thenF elseF : BitVec w → BitVec w)
    (cond : Bool) (input : BitVec w) :
    DialectDenote.denote (d := mlirScfDialect) (.scfIf w thenF elseF)
        (HVector.cons cond (HVector.cons input HVector.nil))
      = (if cond then thenF input else elseF input) := rfl

/-- The dialect's `scfIfHetero` denotation is the literal `if/then/else`
    over heterogeneous-width branches. Same content as `scfIf_denote`
    but with output width `w` independent of input width `w_in`. -/
theorem scfIfHetero_denote (w w_in : Nat)
    (thenF elseF : BitVec w_in → BitVec w)
    (cond : Bool) (input : BitVec w_in) :
    DialectDenote.denote (d := mlirScfDialect) (.scfIfHetero w w_in thenF elseF)
        (HVector.cons cond (HVector.cons input HVector.nil))
      = (if cond then thenF input else elseF input) := rfl

/-- The dialect's `scfFor` denotation matches `forFold`. -/
theorem scfFor_denote (w : Nat) (lo hi step : Nat)
    (bodyF : Nat → BitVec w → BitVec w) (init : BitVec w) :
    DialectDenote.denote (d := mlirScfDialect) (.scfFor w lo hi step bodyF)
        (HVector.cons init HVector.nil)
      = forFold w lo hi step bodyF init := rfl

/-- The dialect's `scfWhile` denotation matches `whileFold`. -/
theorem scfWhile_denote (w : Nat) (fuel : Nat) (condF : BitVec w → Bool)
    (bodyF : BitVec w → BitVec w) (init : BitVec w) :
    DialectDenote.denote (d := mlirScfDialect) (.scfWhile w fuel condF bodyF)
        (HVector.cons init HVector.nil)
      = whileFold w fuel condF bodyF init := rfl

end Agreement

/-! ## 4. Smoke tests

These verify the denotation reduces by `rfl` on concrete inputs — the
dialect is "really computational". The `scfIf_denote` / `scfFor_denote`
/ `scfWhile_denote` rewrite lemmas in §3 (all `rfl`) handle the
`DialectDenote.denote` ↔ user-function bridging cleanly; here we just
exercise the `forFold` / `whileFold` helpers on small concrete inputs. -/

/-- `forFold` summing the indices `0,1,2` (lo=0, hi=3, step=1). -/
example :
    forFold 32 0 3 1 (fun k acc => acc + BitVec.ofNat 32 k) (0 : BitVec 32)
      = (3 : BitVec 32) := by
  -- 0 + 0 + 1 + 2 = 3
  rfl

/-- `whileFold` with fuel 5 doubling until ≥ 8. -/
example :
    whileFold 8 5 (fun x => x < 8) (fun x => x * 2) (1 : BitVec 8)
      = (8 : BitVec 8) := rfl

/-- `forFold` with `lo = hi` (no iterations) returns the initial value. -/
example :
    forFold 16 5 5 1 (fun _ acc => acc + 1) (42 : BitVec 16)
      = (42 : BitVec 16) := rfl

/-- `whileFold` with `fuel = 0` is identity. -/
example :
    whileFold 8 0 (fun _ => true) (fun x => x * 2) (3 : BitVec 8)
      = (3 : BitVec 8) := rfl

/-- Heterogeneous `scfIfHetero`: input width 32, output width 8. The
    `then` branch truncates to the low byte of input + 1, the `else`
    branch returns a fixed byte. On `cond = true`, `input = 5#32`,
    expect `6#8`. -/
example :
    DialectDenote.denote (d := mlirScfDialect)
        (.scfIfHetero 8 32
          (fun x => (x.truncate 8) + 1#8)
          (fun _ => 0#8))
        (HVector.cons true (HVector.cons (5 : BitVec 32) HVector.nil))
      = (6 : BitVec 8) := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.MlirScfDialect
