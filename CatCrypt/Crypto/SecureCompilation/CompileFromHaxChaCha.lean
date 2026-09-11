/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the ChaCha20 quarter-round from extracted source

This module is another **C4** fan-out of the verified-compiler plan, alongside
the SHA-256 leaves (`CompileFromHaxLeaves`), the Keccak χ lane
(`CompileFromHaxKeccak`), and the BLAKE2s G step (`CompileFromHaxBlake2`): the
**ChaCha20 quarter-round** (RFC 8439 §2.1), another ARX (Add / Rotate / Xor)
design. As with BLAKE2s, the body uses *only* modular wrapping-add, bitwise xor,
and rotate — all already recognised by the verified front. **No change to the
verified front is required.**

## The RFC 8439 §2.1 quarter-round

`QUARTERROUND(a, b, c, d)` updates the four words in place (all arithmetic mod
2³², `<<<` is left-rotate):

```
a += b;  d ^= a;  d = d <<< 16;
c += d;  b ^= c;  b = b <<< 12;
a += b;  d ^= a;  d = d <<<  8;
c += d;  b ^= c;  b = b <<<  7;
```

The front recognises only `rotate_right` (not `rotate_left`), so — exactly as in
`CompileFromHaxBlake2` — each left-rotate `x <<< n` is modelled as the equal
`rotate_right(x, 32 - n)`. This matches `ThirToComFront.chachaQRSpec`, whose
reference uses `x.rotateRight (32 - n)`, so we reuse that closed-form spec.

## Method (mirrors `CompileFromHaxBlake2.blake2G_compiles`)

The quarter-round produces four output words, so — as in
`ThirToComFront.{qrAThir, qrBThir, qrCThir, qrDThir}` (the SHA-256 `a'`/`e'`
split idiom) — it is emitted as **four single-output leaves**, each computing
the shared 12-step ARX body and returning one of `(a', b', c', d')`. Each leaf:

1. a let-normalized `ImpExpr` source (one operator per `letBind`, atoms or
   earlier locals as args; `wrapping_add`→`add`, `BitXor`→`xor`,
   `rotate_right`→`ror` with literal count);
2. a `*_src_denoteScalar` proof that the source `denoteScalar` computes the
   corresponding `chachaQRSpec` component (by `rfl`);
3. a `*_isSome` (`native_decide`);
4. a `*_compiles` routing the source-spec through the C3 per-primitive obligation
   `compileFromHax_meets_spec`.

Inputs `(a, b, c, d)` are parameters `["a","b","c","d"]` (`nIn = 4`), at `w = 32`.

All four components are derived (`qrA_compiles` … `qrD_compiles`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxChaCha

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## The shared quarter-round ARX body (let-normalized)

The 12 compute bindings of the RFC 8439 quarter-round, head-last in the
let-chain, parameters `["a","b","c","d"]`. The trailing `cont` selects which
output word the leaf returns; the four leaves differ only in this final `.var`.
Left-rotate `x <<< n` is `rotate_right(x, 32 - n)`. -/

/-- The shared ChaCha20 quarter-round body as a chain of `ImpExpr` `letBind`s over
    the parameters `["a","b","c","d"]`, terminated by `cont` (the output-word
    selector). The bound names track `chachaQRSpec`'s SSA: `a1 = a+b`,
    `d1 = (d^a1) <<< 16`, `c1 = c+d1`, `b1 = (b^c1) <<< 12`, `a2 = a1+b1`,
    `d2 = (d1^a2) <<< 8`, `c2 = c1+d2`, `b2 = (b1^c2) <<< 7`. -/
def qrBodySrc (cont : ImpExpr) : ImpExpr :=
  -- a1 = a + b
  .letBind "a1" (.app "wrapping_add" [.var "a", .var "b"])
   -- d1 = (d ^ a1) <<< 16  ==  rotate_right(d^a1, 16)
   (.letBind "dx1" (.app "BitXor" [.var "d", .var "a1"])
    (.letBind "d1" (.app "rotate_right" [.var "dx1", .lit (.int 16)])
     -- c1 = c + d1
     (.letBind "c1" (.app "wrapping_add" [.var "c", .var "d1"])
      -- b1 = (b ^ c1) <<< 12  ==  rotate_right(b^c1, 20)
      (.letBind "bx1" (.app "BitXor" [.var "b", .var "c1"])
       (.letBind "b1" (.app "rotate_right" [.var "bx1", .lit (.int 20)])
        -- a2 = a1 + b1
        (.letBind "a2" (.app "wrapping_add" [.var "a1", .var "b1"])
         -- d2 = (d1 ^ a2) <<< 8  ==  rotate_right(d1^a2, 24)
         (.letBind "dx2" (.app "BitXor" [.var "d1", .var "a2"])
          (.letBind "d2" (.app "rotate_right" [.var "dx2", .lit (.int 24)])
           -- c2 = c1 + d2
           (.letBind "c2" (.app "wrapping_add" [.var "c1", .var "d2"])
            -- b2 = (b1 ^ c2) <<< 7  ==  rotate_right(b1^c2, 25)
            (.letBind "bx2" (.app "BitXor" [.var "b1", .var "c2"])
             (.letBind "b2" (.app "rotate_right" [.var "bx2", .lit (.int 25)])
              cont)))))))))))

/-- The `a'` leaf returns the final `a` word (`a2`). -/
def qrASrc : ImpExpr := qrBodySrc (.var "a2")
/-- The `b'` leaf returns the final `b` word (`b2`). -/
def qrBSrc : ImpExpr := qrBodySrc (.var "b2")
/-- The `c'` leaf returns the final `c` word (`c2`). -/
def qrCSrc : ImpExpr := qrBodySrc (.var "c2")
/-- The `d'` leaf returns the final `d` word (`d2`). -/
def qrDSrc : ImpExpr := qrBodySrc (.var "d2")

/-! ## Source-spec agreement (each leaf's source denotes to its `chachaQRSpec` component) -/

/-- The `a'` source denotes to `(chachaQRSpec a b c d).1` (`= a'`). The closed
    let-normalized body reduces; `wrapping_add` is `+`, `BitXor` is `^^^`,
    `rotate_right n` is `.rotateRight n`, and `chachaQRSpec`'s `rotateRight (32-n)`
    matches the source's literal counts (`16, 20, 24, 25`). -/
theorem qrASrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d"] I qrASrc (fun _ => none)
      = some (chachaQRSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)).1 := by
  rfl

/-- The `b'` source denotes to `(chachaQRSpec a b c d).2.1` (`= b'`). -/
theorem qrBSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d"] I qrBSrc (fun _ => none)
      = some (chachaQRSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)).2.1 := by
  rfl

/-- The `c'` source denotes to `(chachaQRSpec a b c d).2.2.1` (`= c'`). -/
theorem qrCSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d"] I qrCSrc (fun _ => none)
      = some (chachaQRSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)).2.2.1 := by
  rfl

/-- The `d'` source denotes to `(chachaQRSpec a b c d).2.2.2` (`= d'`). -/
theorem qrDSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d"] I qrDSrc (fun _ => none)
      = some (chachaQRSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)).2.2.2 := by
  rfl

/-! ## Compile success (`native_decide`) -/

theorem qrA_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrASrc).isSome := by
  native_decide

theorem qrB_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrBSrc).isSome := by
  native_decide

theorem qrC_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrCSrc).isSome := by
  native_decide

theorem qrD_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrDSrc).isSome := by
  native_decide

/-! ## The four emitted leaves -/

/-- **ChaCha20 quarter-round `a'` word emitted by the verified compiler.** There
    is a compiled `Com jasminDialect` `prog` with
    `compileFromHax ["a","b","c","d"] qrASrc = some prog`, and for every
    `(a, b, c, d)`, `prog`'s `BitVec 32` denotation (under the input valuation
    `![a, b, c, d]`) is exactly the RFC 8439 §2.1 quarter-round `a'`
    (`(chachaQRSpec a b c d).1`). Routed through `compileFromHax_meets_spec`. -/
theorem qrA_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrASrc = some prog ∧
      ∀ (a b c d : BitVec 32),
        prog.denote (inputValuation 32 4 ![a, b, c, d])
          = (chachaQRSpec a b c d).1 := by
  set prog := (compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrASrc).get
    qrA_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrASrc = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d"] ![a, b, c, d]
      qrASrc (fun _ => none) = some (chachaQRSpec a b c d).1 := by
    exact qrASrc_denoteScalar (nIn := 4) ![a, b, c, d]
  exact compileFromHax_meets_spec (w := 32) (nIn := 4) ["a", "b", "c", "d"]
    ![a, b, c, d] qrASrc _ hc hspec

/-- **ChaCha20 quarter-round `b'` word emitted by the verified compiler.**
    `prog`'s denotation is `(chachaQRSpec a b c d).2.1`. -/
theorem qrB_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrBSrc = some prog ∧
      ∀ (a b c d : BitVec 32),
        prog.denote (inputValuation 32 4 ![a, b, c, d])
          = (chachaQRSpec a b c d).2.1 := by
  set prog := (compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrBSrc).get
    qrB_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrBSrc = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d"] ![a, b, c, d]
      qrBSrc (fun _ => none) = some (chachaQRSpec a b c d).2.1 := by
    exact qrBSrc_denoteScalar (nIn := 4) ![a, b, c, d]
  exact compileFromHax_meets_spec (w := 32) (nIn := 4) ["a", "b", "c", "d"]
    ![a, b, c, d] qrBSrc _ hc hspec

/-- **ChaCha20 quarter-round `c'` word emitted by the verified compiler.**
    `prog`'s denotation is `(chachaQRSpec a b c d).2.2.1`. -/
theorem qrC_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrCSrc = some prog ∧
      ∀ (a b c d : BitVec 32),
        prog.denote (inputValuation 32 4 ![a, b, c, d])
          = (chachaQRSpec a b c d).2.2.1 := by
  set prog := (compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrCSrc).get
    qrC_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrCSrc = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d"] ![a, b, c, d]
      qrCSrc (fun _ => none) = some (chachaQRSpec a b c d).2.2.1 := by
    exact qrCSrc_denoteScalar (nIn := 4) ![a, b, c, d]
  exact compileFromHax_meets_spec (w := 32) (nIn := 4) ["a", "b", "c", "d"]
    ![a, b, c, d] qrCSrc _ hc hspec

/-- **ChaCha20 quarter-round `d'` word emitted by the verified compiler.**
    `prog`'s denotation is `(chachaQRSpec a b c d).2.2.2`. -/
theorem qrD_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrDSrc = some prog ∧
      ∀ (a b c d : BitVec 32),
        prog.denote (inputValuation 32 4 ![a, b, c, d])
          = (chachaQRSpec a b c d).2.2.2 := by
  set prog := (compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrDSrc).get
    qrD_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 4) ["a", "b", "c", "d"] qrDSrc = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d"] ![a, b, c, d]
      qrDSrc (fun _ => none) = some (chachaQRSpec a b c d).2.2.2 := by
    exact qrDSrc_denoteScalar (nIn := 4) ![a, b, c, d]
  exact compileFromHax_meets_spec (w := 32) (nIn := 4) ["a", "b", "c", "d"]
    ![a, b, c, d] qrDSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxChaCha
