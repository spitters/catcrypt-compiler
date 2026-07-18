/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the BLAKE2b G step from extracted source

This module extends the **C4** compile-from-hax fan-out to **BLAKE2b**, the
width-64 sibling of the BLAKE2s G leaf in `CompileFromHaxBlake2`. BLAKE2s G is an
ARX design at `w = 32`; BLAKE2b G is the *same* ARX shape at `w = 64`, with the
rotate amounts `{32, 24, 16, 63}` and the same two message-word adds `x, y`
(RFC 7693 §3.1). No change to the verified front is required: `wrapping_add`,
`BitXor`, and `rotate_right` (with any literal count `< w`) are exactly the
`recogBin`/`recogShift` recognizers exercised by the SHA-256 / Keccak / BLAKE2s
leaves, and they fire identically at `w = 64`.

## BLAKE2b G (RFC 7693 §3.1), w = 64

The G mixing function takes four state words `(a, b, c, d)` and two message words
`(x, y)` and computes (all arithmetic mod 2⁶⁴, `>>>` is right-rotate):

```
a = a + b + x;   d = (d ^ a) >>> 32;
c = c + d;       b = (b ^ c) >>> 24;
a = a + b + y;   d = (d ^ a) >>> 16;
c = c + d;       b = (b ^ c) >>> 63;
```

producing the four updated words `(a', b', c', d')`. This file derives each of
the four as a **single-output leaf**: the source `blake2bGSrc` is the full
let-normalized G body (one operator per `letBind`, all arguments atoms or earlier
locals), and four leaf sources `blake2bG{A,B,C,D}Src` re-use that body but return
the chosen final word (`a'`, `b'`, `c'`, `d'` respectively). Each leaf is the
analogue of `CompileFromHaxBlake2.blake2G_compiles` at `w = 64`.

The closed-form spec mirrors `ThirToComFront.blake2bGSpec` componentwise.

## Method (mirrors `CompileFromHaxBlake2.blake2G_compiles`)

For each output component:

1. `blake2bG{A,B,C,D}Src` — a let-normalized `ImpExpr` source (full G body, then
   return the chosen word).
2. `blake2bG{a,b,c,d}Spec` — the explicit closed-form RFC 7693 component.
3. `blake2bG{A,B,C,D}Src_denoteScalar` — the source `denoteScalar` computes the
   component spec (`rfl`).
4. `blake2bG{A,B,C,D}_compileFromHax_isSome` — the compile succeeds
   (`native_decide`).
5. `blake2bG{A,B,C,D}_compiles` — the emitted jasmin `Com` denotes to the
   component spec, routed through the C3 obligation `compileFromHax_meets_spec`.

The emitted jasmin `Com` is *computed by the verified compiler from the extracted
source*, proven equal to the RFC 7693 G component — the compiler authored the
leaf, with no front change beyond the SHA-256 / Keccak / BLAKE2s leaves. This is
the width-64 ARX fan-out data point.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2b

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The BLAKE2b G mixing function — let-normalized full body

Parameters `["a","b","c","d","x","y"]` (`nIn = 6`; `I 0 = a`, …, `I 5 = y`),
at `w = 64`. The six-input vector is `![a,b,c,d,x,y]`, so
`inpGet ![a,b,c,d,x,y] 0 = a`, etc. Each `wrapping_add`/`BitXor`/`rotate_right`
is its own `letBind` over atom arguments; the rotate count is a literal `.int n`
with `n ∈ {32, 24, 16, 63}`. -/

/-- The full BLAKE2b G body as a chain of `letBind`s, parameterized over the final
    `ImpExpr` returned (so each single-output leaf shares the same compute chain
    and only differs in its tail). Bindings (head-first):
    `a1a, a1 (= a'pre), d1x, d1, c1, b1x, b1, a2a, a2 (= a'), d2x, d2 (= d'),
    c2 (= c'), b2x, b2 (= b')`. -/
def gBodyWith (ret : ImpExpr) : ImpExpr :=
  -- a = a + b + x
  .letBind "a1a" (.app "wrapping_add" [.var "a", .var "b"])
   (.letBind "a1" (.app "wrapping_add" [.var "a1a", .var "x"])
    -- d = (d ^ a) >>> 32
    (.letBind "d1x" (.app "BitXor" [.var "d", .var "a1"])
     (.letBind "d1" (.app "rotate_right" [.var "d1x", .lit (.int 32)])
      -- c = c + d
      (.letBind "c1" (.app "wrapping_add" [.var "c", .var "d1"])
       -- b = (b ^ c) >>> 24
       (.letBind "b1x" (.app "BitXor" [.var "b", .var "c1"])
        (.letBind "b1" (.app "rotate_right" [.var "b1x", .lit (.int 24)])
         -- a = a + b + y
         (.letBind "a2a" (.app "wrapping_add" [.var "a1", .var "b1"])
          (.letBind "a2" (.app "wrapping_add" [.var "a2a", .var "y"])
           -- d = (d ^ a) >>> 16
           (.letBind "d2x" (.app "BitXor" [.var "d1", .var "a2"])
            (.letBind "d2" (.app "rotate_right" [.var "d2x", .lit (.int 16)])
             -- c = c + d
             (.letBind "c2" (.app "wrapping_add" [.var "c1", .var "d2"])
              -- b = (b ^ c) >>> 63
              (.letBind "b2x" (.app "BitXor" [.var "b1", .var "c2"])
               (.letBind "b2" (.app "rotate_right" [.var "b2x", .lit (.int 63)])
                ret)))))))))))))

/-- BLAKE2b G leaf returning the updated `a` word (`a'`). -/
def blake2bGASrc : ImpExpr := gBodyWith (.var "a2")
/-- BLAKE2b G leaf returning the updated `b` word (`b'`). -/
def blake2bGBSrc : ImpExpr := gBodyWith (.var "b2")
/-- BLAKE2b G leaf returning the updated `c` word (`c'`). -/
def blake2bGCSrc : ImpExpr := gBodyWith (.var "c2")
/-- BLAKE2b G leaf returning the updated `d` word (`d'`). -/
def blake2bGDSrc : ImpExpr := gBodyWith (.var "d2")

/-! ## Closed-form RFC 7693 BLAKE2b G output words (`w = 64`)

These mirror `ThirToComFront.blake2bGSpec` componentwise; each is stated as a
plain `def` so the spec is explicit and auditable. -/

/-- The updated `a` word `a'` of RFC 7693 BLAKE2b G. -/
def blake2bGaSpec (a b c d x y : BitVec 64) : BitVec 64 :=
  let a1 := a + b + x
  let d1 := (d ^^^ a1).rotateRight 32
  let c1 := c + d1
  let b1 := (b ^^^ c1).rotateRight 24
  let a2 := a1 + b1 + y
  a2

/-- The updated `d` word `d'` of RFC 7693 BLAKE2b G. -/
def blake2bGdSpec (a b c d x y : BitVec 64) : BitVec 64 :=
  let a1 := a + b + x
  let d1 := (d ^^^ a1).rotateRight 32
  let c1 := c + d1
  let b1 := (b ^^^ c1).rotateRight 24
  let a2 := a1 + b1 + y
  let d2 := (d1 ^^^ a2).rotateRight 16
  d2

/-- The updated `c` word `c'` of RFC 7693 BLAKE2b G. -/
def blake2bGcSpec (a b c d x y : BitVec 64) : BitVec 64 :=
  let a1 := a + b + x
  let d1 := (d ^^^ a1).rotateRight 32
  let c1 := c + d1
  let b1 := (b ^^^ c1).rotateRight 24
  let a2 := a1 + b1 + y
  let d2 := (d1 ^^^ a2).rotateRight 16
  let c2 := c1 + d2
  c2

/-- The updated `b` word `b'` of RFC 7693 BLAKE2b G. -/
def blake2bGbSpec (a b c d x y : BitVec 64) : BitVec 64 :=
  let a1 := a + b + x
  let d1 := (d ^^^ a1).rotateRight 32
  let c1 := c + d1
  let b1 := (b ^^^ c1).rotateRight 24
  let a2 := a1 + b1 + y
  let d2 := (d1 ^^^ a2).rotateRight 16
  let c2 := c1 + d2
  let b2 := (b1 ^^^ c2).rotateRight 63
  b2

/-! ## Source-spec lemmas (each `denoteScalar` computes its component, by `rfl`) -/

/-- The `a'` leaf source denotes (under `denoteScalar`) to `blake2bGaSpec`. -/
theorem blake2bGASrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] I blake2bGASrc (fun _ => none)
      = some (blake2bGaSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)) := by
  rfl

/-- The `b'` leaf source denotes (under `denoteScalar`) to `blake2bGbSpec`. -/
theorem blake2bGBSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] I blake2bGBSrc (fun _ => none)
      = some (blake2bGbSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)) := by
  rfl

/-- The `c'` leaf source denotes (under `denoteScalar`) to `blake2bGcSpec`. -/
theorem blake2bGCSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] I blake2bGCSrc (fun _ => none)
      = some (blake2bGcSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)) := by
  rfl

/-- The `d'` leaf source denotes (under `denoteScalar`) to `blake2bGdSpec`. -/
theorem blake2bGDSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] I blake2bGDSrc (fun _ => none)
      = some (blake2bGdSpec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3)
                (inpGet I 4) (inpGet I 5)) := by
  rfl

/-! ## Compile-success obligations (`native_decide`) -/

theorem blake2bGA_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGASrc).isSome := by
  native_decide

theorem blake2bGB_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGBSrc).isSome := by
  native_decide

theorem blake2bGC_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGCSrc).isSome := by
  native_decide

theorem blake2bGD_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGDSrc).isSome := by
  native_decide

/-! ## Emitted-`Com`-meets-spec theorems (routed through `compileFromHax_meets_spec`) -/

/-- **BLAKE2b G updated `a` word emitted by the verified compiler.** There is a
    compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b","c","d","x","y"] blake2bGASrc = some c`, and for every
    `(a,b,c,d,x,y)`, `c`'s `BitVec 64` denotation (under `![a,b,c,d,x,y]`) is the
    RFC 7693 G output word `a' = blake2bGaSpec`. Width-64 ARX fan-out, reusing the
    `wrapping_add`/`BitXor`/`rotate_right` recognizers with no front change. -/
theorem blake2bGA_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 6 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGASrc = some prog ∧
      ∀ (a b c d x y : BitVec 64),
        prog.denote (inputValuation 64 6 ![a, b, c, d, x, y])
          = blake2bGaSpec a b c d x y := by
  set prog := (compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGASrc).get
    blake2bGA_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGASrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d x y
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] ![a, b, c, d, x, y]
      blake2bGASrc (fun _ => none) = some (blake2bGaSpec a b c d x y) := by
    have h := blake2bGASrc_denoteScalar (nIn := 6) ![a, b, c, d, x, y]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"]
    ![a, b, c, d, x, y] blake2bGASrc _ hc hspec

/-- **BLAKE2b G updated `b` word emitted by the verified compiler** (`b' = blake2bGbSpec`). -/
theorem blake2bGB_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 6 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGBSrc = some prog ∧
      ∀ (a b c d x y : BitVec 64),
        prog.denote (inputValuation 64 6 ![a, b, c, d, x, y])
          = blake2bGbSpec a b c d x y := by
  set prog := (compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGBSrc).get
    blake2bGB_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGBSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d x y
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] ![a, b, c, d, x, y]
      blake2bGBSrc (fun _ => none) = some (blake2bGbSpec a b c d x y) := by
    have h := blake2bGBSrc_denoteScalar (nIn := 6) ![a, b, c, d, x, y]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"]
    ![a, b, c, d, x, y] blake2bGBSrc _ hc hspec

/-- **BLAKE2b G updated `c` word emitted by the verified compiler** (`c' = blake2bGcSpec`). -/
theorem blake2bGC_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 6 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGCSrc = some prog ∧
      ∀ (a b c d x y : BitVec 64),
        prog.denote (inputValuation 64 6 ![a, b, c, d, x, y])
          = blake2bGcSpec a b c d x y := by
  set prog := (compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGCSrc).get
    blake2bGC_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGCSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d x y
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] ![a, b, c, d, x, y]
      blake2bGCSrc (fun _ => none) = some (blake2bGcSpec a b c d x y) := by
    have h := blake2bGCSrc_denoteScalar (nIn := 6) ![a, b, c, d, x, y]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"]
    ![a, b, c, d, x, y] blake2bGCSrc _ hc hspec

/-- **BLAKE2b G updated `d` word emitted by the verified compiler** (`d' = blake2bGdSpec`). -/
theorem blake2bGD_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 6 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGDSrc = some prog ∧
      ∀ (a b c d x y : BitVec 64),
        prog.denote (inputValuation 64 6 ![a, b, c, d, x, y])
          = blake2bGdSpec a b c d x y := by
  set prog := (compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGDSrc).get
    blake2bGD_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"] blake2bGDSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b c d x y
  have hspec : ImpExpr.denoteScalar ["a", "b", "c", "d", "x", "y"] ![a, b, c, d, x, y]
      blake2bGDSrc (fun _ => none) = some (blake2bGdSpec a b c d x y) := by
    have h := blake2bGDSrc_denoteScalar (nIn := 6) ![a, b, c, d, x, y]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 6) ["a", "b", "c", "d", "x", "y"]
    ![a, b, c, d, x, y] blake2bGDSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxBlake2b
