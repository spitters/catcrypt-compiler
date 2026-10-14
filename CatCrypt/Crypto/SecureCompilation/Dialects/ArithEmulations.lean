/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Dialects.Arith

/-!
# D1 — neutral-arith emulation library (the legalization baseline / conformance suite)

The MLIR dialect-alignment plan's D1 step requires that the branchless idioms a
target ISA exposes as single instructions — *and-not*, *select-by-mask*,
*rotate-by-immediate* — are each **expressible** in the neutral `arith` op set,
with a machine-checked correctness proof. Native selections (`andn`, `vpternlog`
masks, `ror`) are perf-only ISel *below* the `llvm` waist; the always-valid form a
legalizer can fall back to is the derived `Com arithDialect` program built here.

This file is that conformance suite: for each idiom we

1. build a derived `Com arithDialect Γ (.int w)` program over the neutral op set
   (`andi`/`ori`/`xori`/`constant`/`shrui_imm`/`shli_imm` only — no native op), and
2. prove its `Com.denote` equals the intended `BitVec` operation.

## Idioms

* **and-not** `a &&& (~~~ b)` — via `xori` against an all-ones constant then `andi`.
* **select-by-mask** `(x &&& c) ||| (y &&& (~~~ c))` — the branchless conditional;
  we prove the *masked-form* equality (the conformance content), not the
  `c ∈ {0, allOnes} ⇒ branch` corollary.
* **rotate-right-by-immediate** `(a >>> n) ||| (a <<< (w - n))` — the shift-or
  form. At the conformance width `w = 64` with a fixed amount we also state the
  `BitVec.rotateRight` corollary.

All three correctness proofs hold at fully symbolic width `w`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith
open Ctxt (Var)

/-! ## 0a. Denotation-reduction lemmas and the `arith_denote` driver

`Com.denote` of a concrete `Com arithDialect` reduces to its underlying `BitVec`
expression through `Com.denote`/`Expr.denote`, the op semantics (`arithDenote`), the
`HVector` projections, the `Expr.lookupArgs` argument resolver, and `Ctxt.Var.lookup`.
These last three are structural-recursive `def`s whose unfolding equations a bare
`rfl` will not iota-reduce inside a deep de-Bruijn term, so we expose each as a
definitional rewrite atom and drive the reduction with `rw`/`simp only`. The
`arith_denote` macro packages the recipe (cf. `VIR/MulDenoteErgonomics.lean`'s
`com_denote`). -/

/-- `lookupArgs` peels one argument: a definitional rewrite atom. -/
theorem lookupArgs_cons {Γ : Ctxt arithDialect} {t : ArithTy} {ts : List ArithTy}
    (x : Var Γ t) (rest : HVector (fun ty => Var Γ ty) ts) (V : Ctxt.Valuation Γ) :
    Expr.lookupArgs (.cons x rest) V = .cons (x.lookup V) (Expr.lookupArgs rest V) := rfl

/-- `HVector.head` of a `cons`. -/
theorem head_cons {α : Type} {f : α → Type} {t : α} {ts : List α}
    (x : f t) (xs : HVector f ts) : (HVector.cons x xs).head = x := rfl

/-- `HVector.tail` of a `cons`. -/
theorem tail_cons {α : Type} {f : α → Type} {t : α} {ts : List α}
    (x : f t) (xs : HVector f ts) : (HVector.cons x xs).tail = xs := rfl

/-- `Ctxt.Var.lookup` of the de-Bruijn-0 variable. -/
theorem lookup_here {Γ : Ctxt arithDialect} {t : ArithTy}
    (v : ⟦t⟧) (V : Ctxt.Valuation Γ) :
    (Var.here : Var (t :: Γ) t).lookup (.cons v V) = v := rfl

/-- `Ctxt.Var.lookup` shifting past one binder. -/
theorem lookup_there {Γ : Ctxt arithDialect} {t s : ArithTy}
    (x : Var Γ t) (v : ⟦s⟧) (V : Ctxt.Valuation Γ) :
    (x.there : Var (s :: Γ) t).lookup (.cons v V) = x.lookup V := rfl

/-- Reduce a concrete `Com arithDialect` denotation to its `BitVec` expression.
    Phase 1 opens the binder/op skeleton; `repeat rw [lookupArgs_cons]` peels the
    per-op argument vectors to `cons` form; `simp only [head_cons, tail_cons]`
    settles the `arithDenote` projections; the trailing `rw [lookup_there/here]`
    chains resolve each de-Bruijn variable to its bound value. -/
macro "arith_denote" : tactic =>
  `(tactic|
    (simp only [Com.denote, Expr.denote, Ctxt.Valuation.extend, DialectDenote.denote,
      arithDenote]
     repeat rw [lookupArgs_cons]
     (try simp only [head_cons, tail_cons])
     (repeat rw [lookup_there])
     (repeat rw [lookup_here])))

/-! ## 0. The all-ones constant materialised by `arith.constant` -/

/-- `arith.constant w (2^w - 1)` materialises the all-ones bitvector. This is the
    standard NOT-via-XOR mask: `b ^^^ allOnes = ~~~ b` (`BitVec.xor_allOnes`). -/
theorem ofNat_allOnes (w : Nat) :
    BitVec.ofNat w (2 ^ w - 1) = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.allOnes, BitVec.toNat_ofNat]

/-! ## 1. and-not  `andnot a b = a &&& (~~~ b)` -/

/-- Derived neutral-arith program for `a &&& (~~~ b)` over inputs `[a, b]`.

    Bindings (newest at head): `allOnes := constant`, `notB := b ^^^ allOnes`,
    `out := a &&& notB`. Under the binders, in context `[notB, allOnes, a, b]`,
    `a = .there.there.here`, `notB = .here`. -/
def andnotProg (w : Nat) : Com arithDialect [.int w, .int w] (.int w) :=
  -- allOnes := constant w (2^w-1)   ctx [a, b] → [allOnes, a, b]
  .var (.mk (.constant w (2 ^ w - 1)) rfl .nil)
    -- notB := b ^^^ allOnes;  b = .there.there.here, allOnes = .here
    (.var (.mk (.xori w) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
      -- out := a &&& notB;  a = .there.there.here, notB = .here
      (.var (.mk (.andi w) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
        (.ret .here)))

/-- Correctness of the and-not emulation, at fully symbolic width `w`. -/
theorem andnotProg_denote (w : Nat) (a b : BitVec w) :
    (andnotProg w).denote (.cons a (.cons b .nil)) = a &&& (~~~ b) := by
  have h : (andnotProg w).denote (.cons a (.cons b .nil))
      = a &&& (b ^^^ BitVec.ofNat w (2 ^ w - 1)) := by
    simp only [andnotProg]; arith_denote
  rw [h, ofNat_allOnes, BitVec.xor_allOnes]

/-! ## 2. select-by-mask  `select c x y = (x &&& c) ||| (y &&& (~~~ c))` -/

/-- Derived neutral-arith program for the branchless masked select
    `(x &&& c) ||| (y &&& (~~~ c))` over inputs `[c, x, y]`.

    Bindings (newest at head): `allOnes := constant`, `notC := c ^^^ allOnes`,
    `xc := x &&& c`, `ync := y &&& notC`, `out := xc ||| ync`. -/
def selectProg (w : Nat) : Com arithDialect [.int w, .int w, .int w] (.int w) :=
  -- ctx [c, x, y] → [allOnes, c, x, y]
  .var (.mk (.constant w (2 ^ w - 1)) rfl .nil)
    -- notC := c ^^^ allOnes;  c = .there.here, allOnes = .here   → [notC, allOnes, c, x, y]
    (.var (.mk (.xori w) rfl (.cons (.there .here) (.cons .here .nil)))
      -- xc := x &&& c;  x = .there.there.there.here, c = .there.there.here  → [xc, notC, allOnes, c, x, y]
      (.var (.mk (.andi w) rfl
          (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
        -- ync := y &&& notC;  y = .there.there.there.there.there.here, notC = .there.here
        -- → [ync, xc, notC, allOnes, c, x, y]
        (.var (.mk (.andi w) rfl
            (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there .here) .nil)))
          -- out := xc ||| ync;  xc = .there.here, ync = .here
          (.var (.mk (.ori w) rfl (.cons (.there .here) (.cons .here .nil)))
            (.ret .here)))))

/-- Correctness of the masked-select emulation (the conformance content: equality
    to the masked form, not the `c ∈ {0, allOnes}` branch corollary), at fully
    symbolic width `w`. -/
theorem selectProg_denote (w : Nat) (c x y : BitVec w) :
    (selectProg w).denote (.cons c (.cons x (.cons y .nil)))
      = (x &&& c) ||| (y &&& (~~~ c)) := by
  have h : (selectProg w).denote (.cons c (.cons x (.cons y .nil)))
      = (x &&& c) ||| (y &&& (c ^^^ BitVec.ofNat w (2 ^ w - 1))) := by
    simp only [selectProg]; arith_denote
  rw [h, ofNat_allOnes, BitVec.xor_allOnes]

/-! ## 3. rotate-right-by-immediate  `rotr a n = (a >>> n) ||| (a <<< (w - n))` -/

/-- Derived neutral-arith program for the shift-or rotate-right form
    `(a >>> n) ||| (a <<< (w - n))` over input `[a]`.

    Bindings (newest at head): `hi := a >>> n`, `lo := a <<< (w - n)`,
    `out := hi ||| lo`. -/
def rotrProg (w n : Nat) : Com arithDialect [.int w] (.int w) :=
  -- ctx [a] → [hi, a]
  .var (.mk (.shrui_imm w n) rfl (.cons .here .nil))
    -- lo := a <<< (w-n);  a = .there.here  → [lo, hi, a]
    (.var (.mk (.shli_imm w (w - n)) rfl (.cons (.there .here) .nil))
      -- out := hi ||| lo;  hi = .there.here, lo = .here
      (.var (.mk (.ori w) rfl (.cons (.there .here) (.cons .here .nil)))
        (.ret .here)))

/-- Correctness of the rotate-right shift-or emulation (the shift-or form) for a
    rotation amount `n < w`, at fully symbolic width `w`. -/
theorem rotrProg_denote (w n : Nat) (hn : n < w) (a : BitVec w) :
    (rotrProg w n).denote (.cons a .nil) = (a >>> n) ||| (a <<< (w - n)) := by
  simp only [rotrProg]; arith_denote
  rw [shiftMask_of_lt hn]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hw : shiftMask w w = 0 ∨ shiftMask w w = w := by
      unfold shiftMask
      split <;> (try split) <;> (try split) <;> (try split) <;> omega
    rcases hw with h | h <;> simp [h]
  · rw [shiftMask_of_lt (by omega : w - n < w)]

/-- Conformance-width corollary: at `w = 64` with a fixed shift amount, the
    shift-or form computed by `rotrProg` agrees with `BitVec.rotateRight`. Stated
    for the representative amount `n = 8`. `BitVec.rotateRight_def` characterises
    `rotateRight r` as `(· >>> (r % w)) ||| (· <<< (w - r % w))`; at the fixed
    `w = 64`, `r = 8` the `8 % 64 = 8`, `64 - 8 = 56` arithmetic settles
    definitionally against `rotrProg`'s shift-or form. -/
theorem rotrProg_denote_rotateRight_64 (a : BitVec 64) :
    (rotrProg 64 8).denote (.cons a .nil) = BitVec.rotateRight a 8 := by
  rw [rotrProg_denote 64 8 (by decide), BitVec.rotateRight_def]

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations
