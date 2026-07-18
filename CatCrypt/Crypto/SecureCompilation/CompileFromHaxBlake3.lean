/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the BLAKE3 compress `G` from extracted source

This module is a **C4** fan-out of the verified-compiler plan, alongside the
SHA-256 leaves (`CompileFromHaxLeaves`), the Keccak χ lane
(`CompileFromHaxKeccak`), the BLAKE2s `G` step (`CompileFromHaxBlake2`), and the
ChaCha20 quarter-round (`CompileFromHaxChaCha`): the **BLAKE3 compression `G`
mixing function** (BLAKE3 reference `g`). Like BLAKE2s/ChaCha, the body uses
*only* modular wrapping-add, bitwise xor, and right-rotate — all already
recognised by the verified front. **No change to the verified front is
required.**

## The BLAKE3 reference `g` (w = 32)

The `G` mixing function takes four state words `(a, b, c, d)` and two message
words `(m0, m1)` and computes (all arithmetic mod 2³², `>>>` is right-rotate):

```
a = a + b + m0;   d = (d ^ a) >>> 16;
c = c + d;        b = (b ^ c) >>> 12;
a = a + b + m1;   d = (d ^ a) >>>  8;
c = c + d;        b = (b ^ c) >>>  7;
```

This is the ChaCha quarter-round skeleton with the two message-word injections
`m0`,`m1`, identical in shape to BLAKE2s `G`. The right-rotate counts are exactly
the literals `16, 12, 8, 7`, so — unlike ChaCha, whose *left*-rotates the front
models as `rotate_right(x, 32-n)` — the BLAKE3 source's `rotate_right` counts are
the rotate counts verbatim. The matching closed-form spec is `blake3GSpec` here
(the BLAKE3-reference `g`, matching `BLAKE3.CompressOwnedEmit.gSpec`).

## Method (mirrors `CompileFromHaxChaCha.qr{A,B,C,D}_compiles`)

The `G` mixing produces four output words, so — as in `qr{A,B,C,D}Src` — it is
emitted as **four single-output leaves**, each computing the shared ARX body and
returning one of `(a', b', c', d')`. Single-output leaves dodge the O(n²)
many-output `rfl` wall. Each leaf:

1. a let-normalized `ImpExpr` source (one operator per `letBind`, atoms or earlier
   locals as args; `wrapping_add`→`add`, `BitXor`→`xor`, `rotate_right`→`ror`
   with literal count);
2. a `*_src_denoteScalar` proof that the source `denoteScalar` computes the
   corresponding `blake3GSpec` component (by `rfl`);
3. a `*_isSome` (`native_decide`);
4. a `*_compiles` routing the source-spec through the C3 per-primitive obligation
   `compileFromHax_meets_spec`.

Inputs `(a, b, c, d, m0, m1)` are parameters `["a","b","c","d","m0","m1"]`
(`nIn = 6`), at `w = 32`.

All four components are derived (`blake3GA_compiles` … `blake3GD_compiles`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake3

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## The BLAKE3 `G` closed-form spec (on `BitVec 32`)

A direct transcription of the BLAKE3 reference `g`, matching
`BLAKE3.CompressOwnedEmit.gSpec` (restated here as a tuple of the four output
words, to keep this leaf module self-contained). -/

/-- The BLAKE3 reference `g` output words `(a', b', c', d')` on state words
    `(a, b, c, d)` and message words `(m0, m1)`, all at `w = 32`. -/
def blake3GSpec (a b c d m0 m1 : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a1 := a + b + m0
  let d1 := (d ^^^ a1).rotateRight 16
  let c1 := c + d1
  let b1 := (b ^^^ c1).rotateRight 12
  let a2 := a1 + b1 + m1
  let d2 := (d1 ^^^ a2).rotateRight 8
  let c2 := c1 + d2
  let b2 := (b1 ^^^ c2).rotateRight 7
  (a2, b2, c2, d2)

/-! ## The shared `G` ARX body (let-normalized)

The 14 compute bindings of the BLAKE3 reference `g`, head-last in the let-chain,
parameters `["a","b","c","d","m0","m1"]`. The trailing `cont` selects which output
word the leaf returns; the four leaves differ only in this final `.var`. Each
`a = a + b + m` is a pair of `wrapping_add`s; each `>>> n` is a `rotate_right`
with the verbatim literal count `16, 12, 8, 7`. -/

/-- The shared BLAKE3 `G` body as a chain of `ImpExpr` `letBind`s over the
    parameters `["a","b","c","d","m0","m1"]`, terminated by `cont` (the output-word
    selector). The bound names track `blake3GSpec`'s SSA: `a1 = a+b+m0`,
    `d1 = (d^a1) >>> 16`, `c1 = c+d1`, `b1 = (b^c1) >>> 12`, `a2 = a1+b1+m1`,
    `d2 = (d1^a2) >>> 8`, `c2 = c1+d2`, `b2 = (b1^c2) >>> 7`. -/
def gBodySrc (cont : ImpExpr) : ImpExpr :=
  -- a1 = a + b + m0
  .letBind "a1a" (.app "wrapping_add" [.var "a", .var "b"])
   (.letBind "a1" (.app "wrapping_add" [.var "a1a", .var "m0"])
    -- d1 = (d ^ a1) >>> 16
    (.letBind "dx1" (.app "BitXor" [.var "d", .var "a1"])
     (.letBind "d1" (.app "rotate_right" [.var "dx1", .lit (.int 16)])
      -- c1 = c + d1
      (.letBind "c1" (.app "wrapping_add" [.var "c", .var "d1"])
       -- b1 = (b ^ c1) >>> 12
       (.letBind "bx1" (.app "BitXor" [.var "b", .var "c1"])
        (.letBind "b1" (.app "rotate_right" [.var "bx1", .lit (.int 12)])
         -- a2 = a1 + b1 + m1
         (.letBind "a2a" (.app "wrapping_add" [.var "a1", .var "b1"])
          (.letBind "a2" (.app "wrapping_add" [.var "a2a", .var "m1"])
           -- d2 = (d1 ^ a2) >>> 8
           (.letBind "dx2" (.app "BitXor" [.var "d1", .var "a2"])
            (.letBind "d2" (.app "rotate_right" [.var "dx2", .lit (.int 8)])
             -- c2 = c1 + d2
             (.letBind "c2" (.app "wrapping_add" [.var "c1", .var "d2"])
              -- b2 = (b1 ^ c2) >>> 7
              (.letBind "bx2" (.app "BitXor" [.var "b1", .var "c2"])
               (.letBind "b2" (.app "rotate_right" [.var "bx2", .lit (.int 7)])
                cont)))))))))))))

/-- The `a'` leaf returns the final `a` word (`a2`). -/
def gASrc : ImpExpr := gBodySrc (.var "a2")
/-- The `b'` leaf returns the final `b` word (`b2`). -/
def gBSrc : ImpExpr := gBodySrc (.var "b2")
/-- The `c'` leaf returns the final `c` word (`c2`). -/
def gCSrc : ImpExpr := gBodySrc (.var "c2")
/-- The `d'` leaf returns the final `d` word (`d2`). -/
def gDSrc : ImpExpr := gBodySrc (.var "d2")

/-! ## Source-spec agreement (each leaf's source denotes to its `blake3GSpec` component) -/

/-- The `a'` source denotes to `(blake3GSpec a b c d m0 m1).1` (`= a'`). The closed
    let-normalized body reduces; `wrapping_add` is `+`, `BitXor` is `^^^`,
    `rotate_right n` is `.rotateRight n`. -/
theorem gASrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "m0", "m1"] I gASrc (fun _ => none)
      = some (blake3GSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)).1 := by
  rfl

/-- The `b'` source denotes to `(blake3GSpec a b c d m0 m1).2.1` (`= b'`). -/
theorem gBSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "m0", "m1"] I gBSrc (fun _ => none)
      = some (blake3GSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)).2.1 := by
  rfl

/-- The `c'` source denotes to `(blake3GSpec a b c d m0 m1).2.2.1` (`= c'`). -/
theorem gCSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "m0", "m1"] I gCSrc (fun _ => none)
      = some (blake3GSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)).2.2.1 := by
  rfl

/-- The `d'` source denotes to `(blake3GSpec a b c d m0 m1).2.2.2` (`= d'`). -/
theorem gDSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "m0", "m1"] I gDSrc (fun _ => none)
      = some (blake3GSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)).2.2.2 := by
  rfl

/-! ## Compile success (`native_decide`) -/

theorem gA_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gASrc).isSome := by
  native_decide

theorem gB_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gBSrc).isSome := by
  native_decide

theorem gC_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gCSrc).isSome := by
  native_decide

theorem gD_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gDSrc).isSome := by
  native_decide

/-! ## The four emitted leaves -/

/-- **BLAKE3 `G` `a'` word emitted by the verified compiler.** There is a compiled
    `Com jasminDialect` `prog` with
    `compileFromHax ["a","b","c","d","m0","m1"] gASrc = some prog`, and for every
    `(a, b, c, d, m0, m1)`, `prog`'s `BitVec 32` denotation (under the input
    valuation `![a, b, c, d, m0, m1]`) is exactly the BLAKE3 reference `g` `a'`
    word (`(blake3GSpec a b c d m0 m1).1`). Routed through
    `compileFromHax_meets_spec`. This is a C4 fan-out reusing the
    `wrapping_add`/`BitXor`/`rotate_right` recognizers with no front change. -/
theorem blake3GA_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gASrc = some prog ∧
      ∀ (a b c d m0 m1 : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, m0, m1])
          = (blake3GSpec a b c d m0 m1).1 := by
  set prog := (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gASrc).get
    gA_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gASrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d m0 m1
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "m0", "m1"] ![a, b, c, d, m0, m1]
      gASrc (fun _ => none) = some (blake3GSpec a b c d m0 m1).1 := by
    have h := gASrc_denoteScalar (nIn := 6) ![a, b, c, d, m0, m1]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"]
    ![a, b, c, d, m0, m1] gASrc _ hc hspec

/-- **BLAKE3 `G` `b'` word emitted by the verified compiler.**
    `prog`'s denotation is `(blake3GSpec a b c d m0 m1).2.1`. -/
theorem blake3GB_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gBSrc = some prog ∧
      ∀ (a b c d m0 m1 : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, m0, m1])
          = (blake3GSpec a b c d m0 m1).2.1 := by
  set prog := (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gBSrc).get
    gB_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gBSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d m0 m1
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "m0", "m1"] ![a, b, c, d, m0, m1]
      gBSrc (fun _ => none) = some (blake3GSpec a b c d m0 m1).2.1 := by
    have h := gBSrc_denoteScalar (nIn := 6) ![a, b, c, d, m0, m1]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"]
    ![a, b, c, d, m0, m1] gBSrc _ hc hspec

/-- **BLAKE3 `G` `c'` word emitted by the verified compiler.**
    `prog`'s denotation is `(blake3GSpec a b c d m0 m1).2.2.1`. -/
theorem blake3GC_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gCSrc = some prog ∧
      ∀ (a b c d m0 m1 : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, m0, m1])
          = (blake3GSpec a b c d m0 m1).2.2.1 := by
  set prog := (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gCSrc).get
    gC_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gCSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d m0 m1
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "m0", "m1"] ![a, b, c, d, m0, m1]
      gCSrc (fun _ => none) = some (blake3GSpec a b c d m0 m1).2.2.1 := by
    have h := gCSrc_denoteScalar (nIn := 6) ![a, b, c, d, m0, m1]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"]
    ![a, b, c, d, m0, m1] gCSrc _ hc hspec

/-- **BLAKE3 `G` `d'` word emitted by the verified compiler.**
    `prog`'s denotation is `(blake3GSpec a b c d m0 m1).2.2.2`. -/
theorem blake3GD_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 6 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gDSrc = some prog ∧
      ∀ (a b c d m0 m1 : BitVec 32),
        prog.denote (inputValuation 32 6 ![a, b, c, d, m0, m1])
          = (blake3GSpec a b c d m0 m1).2.2.2 := by
  set prog := (compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gDSrc).get
    gD_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"] gDSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d m0 m1
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "m0", "m1"] ![a, b, c, d, m0, m1]
      gDSrc (fun _ => none) = some (blake3GSpec a b c d m0 m1).2.2.2 := by
    have h := gDSrc_denoteScalar (nIn := 6) ![a, b, c, d, m0, m1]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 32) (nIn := 6) ["a", "b", "c", "d", "m0", "m1"]
    ![a, b, c, d, m0, m1] gDSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake3
