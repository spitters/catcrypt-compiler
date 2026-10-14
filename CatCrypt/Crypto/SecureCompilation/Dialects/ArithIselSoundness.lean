/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# D1/D3 — native instruction-selection soundness

This file closes the instruction-selection (ISel) leg of the D1 conformance
story. `ArithEmulations.lean` builds, for each branchless idiom a target ISA
exposes as a single native instruction, the **always-valid** neutral-arith
fallback program (`Com arithDialect`) and proves the `BitVec` value it computes.
`JasminDialect.lean` exposes the corresponding **native** ops (CMOV/`select`,
ANDN/`andn`, ROR/`rorImm`, MULX/`mulhi`, ADX/`addCarry{Lo,Hi}`) with their own
`jasminDenote` semantics.

ISel is the legalizer choice between the two: emit the neutral emulation, or the
faster native op. For that swap to be **perf-only** (never correctness-critical),
the native op must compute *exactly* the same `BitVec` value as its emulation.
This module proves that equivalence for each idiom, at fully symbolic
width `w`:

| native op (jasmin) | emulation (`arith`)        | equivalence lemma            |
|--------------------|----------------------------|------------------------------|
| `andn`  (ANDN)     | `andnotProg` value         | `andn_eq_andnot`             |
| `select` (CMOV)    | `selectProg` value (masked)| `select_eq_maskSelect`       |
| `rorImm` (ROR)     | `rotrProg` value (shift-or)| `rorImm_eq_rotrProg`         |
| `mulhi` (MULX hi)  | `mulHiW` (widening hi)     | `mulhi_eq_mulHiW`            |

**The headline.** Each lemma says the native op and the emulation agree on every
input. Hence native-op ISel — CMOV, ANDN, ROR, MULX — is a *proven-equivalent*
perf-only swap: the neutral-arith emulation is the always-valid fallback, the
native op is the proven-equal faster form, and the legalizer may pick either
without affecting the denotation (correctness). The native op is never
correctness-critical: it is *defined* to equal the emulation.

**ADX (`addCarryLo`/`addCarryHi`)** is discussed in §5: the carry-chain add is a
two-output instruction (data word + carry-out bit). The data word `a + b + cin`
*is* expressible in the neutral add-with-carry-in form, but the **carry-out bit**
`carryOutBit` reads the unbounded `a.toNat + b.toNat + cin.toNat ≥ 2 ^ w` overflow
that the carry-free `arith` add (`a + b`, width-truncating) deliberately discards.
So ADX is *not* a pure-perf swap against the neutral op set — the
carry-out is extra information, not a re-spelling. We state the data-word
identity (`addCarryLo_eq_addCarryWord`) and note the carry-out gap rather than
fabricate a neutral emulation for it.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations

/-! ## 1. ANDN (BMI1) — `andn` ≡ the and-not emulation

`andnotProg_denote` proves the neutral emulation computes `a &&& ~~~ b`. The
native `JasminBinOp.andn` denotes (via `JasminBinOp.apply`) to `(~~~ a) &&& b` —
it complements its *first* source (the x86 `ANDN dst, a, b ⇒ (~a) & b`). The two
are the same `&&&`-of-a-complement up to which operand is complemented, so the
native op equals the emulation's value with the operands transposed. -/

/-- The native `andn` op computes `(~~~ a) &&& b` — its raw `jasminDenote`. -/
theorem andn_apply (w : Nat) (a b : BitVec w) :
    JasminBinOp.andn.apply a b = (~~~ a) &&& b := rfl

/-- **ANDN ISel soundness.** The native `andn` op, applied to `b, a`, computes the
    exact value the and-not emulation `andnotProg` produces on `a, b`
    (`andnotProg_denote`'s RHS `a &&& ~~~ b`). So emitting `andn b a` in place of
    the `xori; andi` emulation is a denotation-preserving, perf-only swap. -/
theorem andn_eq_andnot (w : Nat) (a b : BitVec w) :
    JasminBinOp.andn.apply b a = a &&& (~~~ b) := by
  simp [JasminBinOp.apply, BitVec.and_comm]

/-- Spelled against the emulation theorem directly: `andn b a` equals
    `(andnotProg w).denote ⟨a, b⟩`. -/
theorem andn_eq_andnotProg_denote (w : Nat) (a b : BitVec w) :
    JasminBinOp.andn.apply b a
      = (andnotProg w).denote (.cons a (.cons b .nil)) := by
  rw [andnotProg_denote, andn_eq_andnot]

/-! ## 2. CMOV (`select`) — `selectW` ≡ the masked-select emulation

`selectProg_denote` proves the neutral emulation computes the masked form
`(x &&& c) ||| (y &&& ~~~ c)` for a full-width mask `c`. The native `select` op
takes a **1-bit** condition `cond : reg 1` and denotes (`selectW`) to the branch
`if cond = 1 then x else y`. These are the same *iff* the masked form's mask is
the full mask `if cond = 1 then allOnes else 0` materialised from the 1-bit
condition: with that mask, `c ∈ {allOnes, 0}`, and the two `&&&`-`|||` terms
collapse to the taken branch. -/

/-- The native `select` op computes the branch `if cond = 1#1 then a else b` —
    its raw `jasminDenote` (`selectW`). -/
theorem select_apply (w : Nat) (cond : BitVec 1) (a b : BitVec w) :
    selectW cond a b = if cond = 1#1 then a else b := rfl

/-- The full mask the 1-bit `select` condition stands for: `allOnes` when the
    condition is set, `0` otherwise. This is the `mask = 0 - cond` the branchless
    CMOV idiom materialises. -/
def condMask (w : Nat) (cond : BitVec 1) : BitVec w :=
  if cond = 1#1 then BitVec.allOnes w else 0

/-- **CMOV ISel soundness.** With the full mask `condMask` the 1-bit condition
    materialises, the masked-select emulation value `(x &&& c) ||| (y &&& ~~~ c)`
    (`selectProg_denote`'s RHS) equals the native `select` op's branch
    `selectW cond x y`. So emitting a `CMOV`/native `select` in place of the
    `xori; andi; andi; ori` mask emulation is a denotation-preserving, perf-only
    swap. -/
theorem select_eq_maskSelect (w : Nat) (cond : BitVec 1) (x y : BitVec w) :
    (x &&& condMask w cond) ||| (y &&& (~~~ condMask w cond))
      = selectW cond x y := by
  unfold selectW condMask
  by_cases h : cond = 1#1 <;> simp [h, BitVec.and_allOnes]

/-- Spelled against the emulation theorem directly: the native `select` value
    equals `(selectProg w).denote ⟨condMask w cond, x, y⟩` — the emulation run on
    the materialised full mask. -/
theorem select_eq_selectProg_denote (w : Nat) (cond : BitVec 1) (x y : BitVec w) :
    selectW cond x y
      = (selectProg w).denote (.cons (condMask w cond) (.cons x (.cons y .nil))) := by
  rw [selectProg_denote, select_eq_maskSelect]

/-! ## 3. ROR (`rorImm`) — `rotateRight` ≡ the shift-or emulation

`rotrProg_denote` proves the neutral emulation computes the shift-or form
`(a >>> n) ||| (a <<< (w - n))`. The native `rorImm w n` op denotes to
`a.rotateRight n`. For an **in-range** immediate `0 < n < w` (every SHA-512
Σ/σ and Keccak ρ rotate), `BitVec.rotateRight_def` (with `n % w = n`) makes the
two bit-for-bit equal. The JasminDialect lemma `rorImm_denote_eq_shiftOr`
provides exactly that `BitVec`-algebra step. -/

/-- The native `rorImm` op computes `a.rotateRight n` — its raw `jasminDenote`. -/
theorem rorImm_apply (w n : Nat) (a : BitVec w) :
    (jasminDenote.denote (.rorImm w n) (.cons a .nil)) = a.rotateRight n := rfl

/-- **ROR ISel soundness.** For an in-range immediate `n < w`, the native
    `rorImm` op value `a.rotateRight n` equals the shift-or emulation value
    `(a >>> n) ||| (a <<< (w - n))` (`rotrProg_denote`'s RHS). So collapsing the
    `shr; shl; or` rotate triple to a single `rorImm` is a denotation-preserving,
    perf-only swap. -/
theorem rorImm_eq_shiftOr (w n : Nat) (hn : n < w) (a : BitVec w) :
    a.rotateRight n = (a >>> n) ||| (a <<< (w - n)) :=
  rorImm_denote_eq_shiftOr n hn a

/-- Spelled against the emulation theorem directly: for in-range `n`, the native
    `rorImm` value equals `(rotrProg w n).denote ⟨a⟩`. -/
theorem rorImm_eq_rotrProg_denote (w n : Nat) (hn : n < w) (a : BitVec w) :
    a.rotateRight n = (rotrProg w n).denote (.cons a .nil) := by
  rw [rotrProg_denote w n hn, rorImm_eq_shiftOr w n hn a]

/-- Conformance-width corollary at `w = 64`, `n = 8` (cf.
    `rotrProg_denote_rotateRight_64`): the native `rorImm 64 8` value equals the
    `rotrProg 64 8` emulation, with no side condition (`8 < 64` discharged). -/
theorem rorImm_eq_rotrProg_denote_64 (a : BitVec 64) :
    a.rotateRight 8 = (rotrProg 64 8).denote (.cons a .nil) := by
  rw [rotrProg_denote_rotateRight_64]

/-! ## 4. MULX hi (`mulhi`) — the native op IS the neutral widening-hi value

The high word of the widening multiply is the neutral `arith.mului_extended_hi`
image: `mulHiW a b = ofNat w (a.toNat * b.toNat / 2 ^ w)`. The native `mulhi`
op's `jasminDenote` is literally `mulHiW`, so the equivalence is definitional —
the native MULX-hi op selection is sound by `rfl`. -/

/-- The native `mulhi` op computes `mulHiW a b` — its raw `jasminDenote`. -/
theorem mulhi_apply (w : Nat) (a b : BitVec w) :
    (jasminDenote.denote (.mulhi w) (.cons a (.cons b .nil))) = mulHiW a b := rfl

/-- **MULX-hi ISel soundness.** The native `mulhi` op computes exactly the
    neutral widening-multiply high word `ofNat w (a.toNat * b.toNat / 2 ^ w)`. The
    native op *is* the neutral value (definitional `rfl`), so selecting MULX's
    high output for the widening-hi idiom is correctness-trivially sound. -/
theorem mulhi_eq_mulHiW (w : Nat) (a b : BitVec w) :
    (jasminDenote.denote (.mulhi w) (.cons a (.cons b .nil)))
      = BitVec.ofNat w (a.toNat * b.toNat / 2 ^ w) := rfl

/-! ## 5. ADX (`addCarryLo` / `addCarryHi`) — data word ≡ neutral add-with-carry,
    carry-out is extra information

The carry-chain add `ADCX/ADOX dst := dst + src + cin` is a **two-output**
instruction modelled by two single-output ops:

* `addCarryLo` — the data word `addCarryWord a b cin = a + b + ofNat w cin.toNat`;
* `addCarryHi` — the carry-out bit `carryOutBit a b cin`
  (`= 1 iff a.toNat + b.toNat + cin.toNat ≥ 2 ^ w`).

The **data word** is expressible in the neutral op set: it is two
width-truncating `arith` adds (`(a + b) + ext cin`). We state that identity below.

The **carry-out bit**, however, reads the *unbounded* sum's overflow past
`2 ^ w` — information the carry-free neutral `arith` add (`a + b`, which truncates
mod `2 ^ w`) deliberately discards. There is no carry-free `arith` op whose value
recovers it; the ADX trio earns its keep precisely by exposing that bit. So ADX is
**not** a pure-perf swap against the neutral op set — unlike ANDN/CMOV/ROR/MULX,
the native carry-out is extra semantics, not a re-spelling. We record the
data-word equivalence and leave the carry-out as a deliberately-unmatched native
capability (no fabricated neutral emulation). -/

/-- The native `addCarryLo` op computes `addCarryWord a b cin` — its raw
    `jasminDenote`. -/
theorem addCarryLo_apply (w : Nat) (a b : BitVec w) (cin : BitVec 1) :
    (jasminDenote.denote (.addCarryLo w) (.cons a (.cons b (.cons cin .nil))))
      = addCarryWord a b cin := rfl

/-- **ADX data-word identity (the expressible part).** The native `addCarryLo`
    data result is the neutral add-with-carry-in form `a + b + ext(cin)` — two
    width-truncating adds, expressible without any native op. (The carry-OUT bit
    `addCarryHi`/`carryOutBit` is the extra information the neutral op
    set cannot recover; see the section docstring.) -/
theorem addCarryLo_eq_addWithCarryIn (w : Nat) (a b : BitVec w) (cin : BitVec 1) :
    (jasminDenote.denote (.addCarryLo w) (.cons a (.cons b (.cons cin .nil))))
      = a + b + BitVec.ofNat w cin.toNat := rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness
