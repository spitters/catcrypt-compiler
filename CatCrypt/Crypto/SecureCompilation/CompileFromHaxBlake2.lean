/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits a BLAKE2s G step from extracted source

This module extends the **C4** step of the verified-compiler plan to a **third
primitive family**: BLAKE2 (an ARX design — Add / Rotate / Xor). The C4 SHA-256
leaves (`CompileFromHaxLeaves`) and the Keccak χ lane (`CompileFromHaxKeccak`)
showed `compileFromHax` *emitting* a crypto leaf from hax-extracted source for
the bitwise (`¬`/`∧`/`⊕`) and rotate families. Here we do the same for the
**BLAKE2s G mixing function** (RFC 7693), whose body uses *only* modular
wrapping-add, bitwise xor, and right-rotate — all already recognised by the
verified front. **No change to the verified front is required**; this is a clean
fan-out data point to a new (ARX) primitive family.

## BLAKE2s G (RFC 7693), w = 32

The G mixing function takes four state words `(a, b, c, d)` and two message
words `(x, y)` and computes (all arithmetic mod 2³², `>>>` is right-rotate):

```
a = a + b + x;   d = (d ^ a) >>> 16;
c = c + d;       b = (b ^ c) >>> 12;
a = a + b + y;   d = (d ^ a) >>>  8;
c = c + d;       b = (b ^ c) >>>  7;
```

This file emits the **final `a` word** (the front returns a single register),
with the six inputs `(a, b, c, d, x, y)` as the parameters (`nIn = 6`). The
returned value is `a₂ = (a + b + x) + b'` where `b' = ((b ^ ((c + (d ^ ((a+b)+x))>>>16)))>>>12)` and the
second add folds in `y` — i.e. the standard G output word. The remaining two
state words are mixed by the same `+`/`^`/`>>>` shapes, so the single-word
mechanism scales by replication to the full G function and the BLAKE2s round.

## Method (mirrors `CompileFromHaxLeaves.maj_compiles` / `CompileFromHaxKeccak.chiLane_compiles`)

`a + b + x` is two wrapping adds, each `^` an `BitXor`, each `>>> n` a
`rotate_right` with a literal count — exactly the `recogBin`/`recogShift`
recognizers exercised by the SHA-256 big-sigma and majority leaves. As in
`maj_compiles`, the source is fully let-normalized (one operator per `letBind`,
all arguments atoms or earlier locals) and the six-input valuation `![a,b,c,d,x,y]`
reduces componentwise.

The leaf follows the C3 obligation pattern exactly:

1. `blake2GSrc` — a let-normalized `ImpExpr` source.
2. `blake2GSpec` — the explicit closed-form final `a` word, computed step by step.
3. `blake2GSrc_denoteScalar` — the source `denoteScalar` computes `blake2GSpec`.
4. `blake2G_compileFromHax_isSome` — the compile succeeds (`native_decide`).
5. `blake2G_compiles` — the emitted jasmin `Com` denotes to `blake2GSpec`,
   routed through the C3 per-primitive obligation `compileFromHax_meets_spec`.

The emitted jasmin `Com` is *computed by the verified compiler from the extracted
source*, proven equal to the RFC 7693 G output word — the compiler authored the
leaf, with no front change beyond the SHA-256/Keccak leaves. This is the first
ARX (Add/Rotate/Xor) family fan-out.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The BLAKE2s G mixing function — output word

Parameters `["a","b","c","d","x","y"]` (`nIn = 6`; `I 0 = a`, …, `I 5 = y`),
at `w = 32`. The six-input vector is `![a,b,c,d,x,y]`, so
`inpGet ![a,b,c,d,x,y] 0 = a`, etc. Each `wrapping_add`/`BitXor`/`rotate_right`
is its own `letBind` over atom arguments; the rotate count is a literal `.int n`. -/

/-- The BLAKE2s G source as a hax `ImpExpr`, fully let-normalized, parameters
    `["a","b","c","d","x","y"]`. The two-summand updates `a = a+b+x` and
    `a = a+b+y` are each a pair of `wrapping_add`s; each `d = (d^a) >>> n` and
    `b = (b^c) >>> n` is a `BitXor` followed by a `rotate_right` with literal
    count `n`. Returns the final `a` register (`a2`). -/
def blake2GSrc : ImpExpr :=
  -- a = a + b + x
  .letBind "a1a" (.app "wrapping_add" [.var "a", .var "b"])
   (.letBind "a1" (.app "wrapping_add" [.var "a1a", .var "x"])
    -- d = (d ^ a) >>> 16
    (.letBind "dx1" (.app "BitXor" [.var "d", .var "a1"])
     (.letBind "d1" (.app "rotate_right" [.var "dx1", .lit (.int 16)])
      -- c = c + d
      (.letBind "c1" (.app "wrapping_add" [.var "c", .var "d1"])
       -- b = (b ^ c) >>> 12
       (.letBind "bx1" (.app "BitXor" [.var "b", .var "c1"])
        (.letBind "b1" (.app "rotate_right" [.var "bx1", .lit (.int 12)])
         -- a = a + b + y
         (.letBind "a2a" (.app "wrapping_add" [.var "a1", .var "b1"])
          (.letBind "a2" (.app "wrapping_add" [.var "a2a", .var "y"])
           (.var "a2")))))))))

/-- The explicit closed-form RFC 7693 BLAKE2s G **output word** (the final `a`),
    computed step by step at `w = 32`. Stated as a plain `def` so the spec is
    explicit and auditable. -/
def blake2GSpec (a b c d x y : BitVec 32) : BitVec 32 :=
  let a1 := a + b + x
  let d1 := (d ^^^ a1).rotateRight 16
  let c1 := c + d1
  let b1 := (b ^^^ c1).rotateRight 12
  let a2 := a1 + b1 + y
  a2

/-- The G source denotes (under `denoteScalar`, parameters
    `["a","b","c","d","x","y"]`) to the RFC 7693 output word `blake2GSpec`,
    reading `a = inpGet I 0`, …, `y = inpGet I 5`. The closed let-normalized body
    reduces; `wrapping_add` is `+`, `BitXor` is `^^^`, `rotate_right n` is
    `.rotateRight n`. -/
theorem blake2GSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] I blake2GSrc (fun _ => none)
      = some (blake2GSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)) := by
  -- The closed let-normalized `denoteScalar` chain and `blake2GSpec` both reduce
  -- definitionally (string lookups and the `recogBin`/`recogShift` recognizers
  -- compute on the closed source), so the source-spec is a `rfl`.
  rfl

/-- The compile-from-hax pipeline succeeds on the BLAKE2s G word (`w = 32`, six
    parameters). -/
theorem blake2G_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2GSrc).isSome := by
  native_decide

/-- **BLAKE2s G output word emitted by the verified compiler.** There is a
    compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b","c","d","x","y"] blake2GSrc = some c`, and for every
    `(a, b, c, d, x, y)`, `c`'s `BitVec 32` denotation (under the input valuation
    `![a, b, c, d, x, y]`) is exactly the RFC 7693 G output word `blake2GSpec`.
    Routed through the C3 per-primitive obligation `compileFromHax_meets_spec`.
    This is a C4 fan-out to a *third* primitive family (BLAKE2 / ARX), reusing the
    SHA-256/Keccak `wrapping_add`/`BitXor`/`rotate_right` recognizers with no front
    change. The full G function is two more `+`/`^`/`>>>` mixes of the same shape;
    a BLAKE2s round is eight G applications. -/
theorem blake2G_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2GSrc = some prog ∧
      ∀ (a b c d x y : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, x, y])
          = blake2GSpec a b c d x y := by
  set prog := (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2GSrc).get
    blake2G_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2GSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d x y
  -- The RFC G source-spec at `![a,b,c,d,x,y]`: `inpGet ![a,b,c,d,x,y] i` reduces
  -- to the i-th component, so the spec is the plain `blake2GSpec a b c d x y`.
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] ![a, b, c, d, x, y]
      blake2GSrc (fun _ => none) = some (blake2GSpec a b c d x y) := by
    have h := blake2GSrc_denoteScalar (nIn := 6) ![a, b, c, d, x, y]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 32) (nIn := 6) ["a", "b", "c", "d", "x", "y"]
    ![a, b, c, d, x, y] blake2GSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2
