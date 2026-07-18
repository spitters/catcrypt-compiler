/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminMonoSem

/-!
# `CProg`-free reference data for the s2n-bignum SSA ports

This module holds the **`CProg`-free** per-kernel reference data — the
SSA `body` (a `List InstrR`), the pure reference semantics `refSem`
(via `pureEvalMonoCmd`), and the bit-vector correctness specs — for the
s2n-bignum SSA ports whose `catCryptDialect` twins live in
`SecureCompilation/Jasmin/S2NBignumSSADialect.lean`.

It is extracted out of `S2NBignumSSA.lean` so that the dialect layer can
depend on these references **without** dragging in `S2NBignumSSA`'s
`CProg`-stated material (`prog : Option (CProg …)` and the
`cryptoSSA_denote` corollaries, both of which mention the `CProg`
inductive / `CProg.denote`). That `CProg`-stated material stays in
`S2NBignumSSA.lean`, which now imports **this** module for the shared
`body`/`refSem`/`spec` definitions.

Everything here is stated over `Var`, `InstrR`, `BitVec`, and the
proved-translator's pure evaluator `pureEvalMonoCmd` — none of it
mentions `CProg`, `CExpr`, `CProg.denote`, or `cryptoSSA_denote`.

## Kernels covered

* `Simple`      — the Atlas `simple.s` port (`r = a`);
* `WordAvg`     — overflow-safe unsigned average `(a&b) + ((a^b)>>1)`;
* `ByteReverse` — 64-bit byte reversal;
* `NegModInv`   — Newton negated modular inverse, with the full
                  `word_negmodinv_correct` proof chain.

The SSA builder helpers (`v`, `assignConst`, `assignBin`, `assignShL`,
`assignShR`) also live here; they are `CProg`-free and shared by every
port in `S2NBignumSSA.lean`.
-/

namespace CatCrypt.Crypto.Jasmin.S2NBignumSSA

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.ToSSA

set_option autoImplicit false

/-! ## SSA builder helpers (`CProg`-free) -/

/-- A u64 variable with the given name. -/
def v (s : String) : Var := { vname := s, vtype := .sword .U64 }

private def pvar (s : String) : PExpr := .Pvar { gv := { var := v s }, gs := false }
private def plval (s : String) : LVal := .Lvar { var := v s }
private def cassgn (s : String) (e : PExpr) : InstrR :=
  .Cassgn (plval s) .AT_none (.sword .U64) e

/-- `s := k` (constant). -/
def assignConst (s : String) (k : Int) : InstrR := cassgn s (.Pconst k)
/-- `s := op a b` (both operands SSA variables). -/
def assignBin (s : String) (op : SOp2) (a b : String) : InstrR :=
  cassgn s (.Papp2 op (pvar a) (pvar b))
/-- `s := a <<< k` (constant shift). -/
def assignShL (s : String) (a : String) (k : Nat) : InstrR :=
  cassgn s (.Papp2 (.Olsl .U64) (pvar a) (.Pconst (k : Int)))
/-- `s := a >>> k` (constant shift). -/
def assignShR (s : String) (a : String) (k : Nat) : InstrR :=
  cassgn s (.Papp2 (.Olsr .U64) (pvar a) (.Pconst (k : Int)))

/-! ## Port 1: `simple.s` — body + reference semantics + spec

ARM:
```
add x2, x1, x0     // x2 := x1 + x0
sub x2, x2, x1     // x2 := x2 - x1
```
SSA:
```
t := x1 + x0
r := t  - x1
```
Result: `r = a` where `x0 = a, x1 = b`. -/

namespace Simple

def body : List InstrR :=
  [ assignBin "t" (.Oadd .U64) "x1" "x0"
  , assignBin "r" (.Osub .U64) "t"  "x1" ]

/-- Reference semantics: run `body` against `pureEvalMonoCmd`. -/
def refSem (a b : BitVec 64) : BitVec 64 :=
  pureEvalMonoCmd 64
    (fun w => if w = v "x0" then a else if w = v "x1" then b else 0)
    (v "r") body

/-- Spec: the ARM `SIMPLE_SPEC` post-condition — `r = a`. -/
theorem spec (a b : BitVec 64) : refSem a b = a := by
  show (b + a) - b = a
  bv_decide

end Simple

/-! ## Port 2: `word_negmodinv.S` — body + Newton correctness chain

The ARM source (s2n-bignum `arm/generic/word_negmodinv.S`) uses register
aliasing heavily. After SSA renaming, the body becomes 18 assignments:
18 strict `let`-bindings, one per ARM primitive operation (each `madd`
is split into mul + add). -/

namespace NegModInv

def body : List InstrR :=
  -- Initial 5-bit approximation: x = (a - (a<<2)) XOR 2
  [ assignShL  "t0"  "a"  2                       -- lsl x, a, #2
  , assignBin  "t1"  (.Osub .U64)  "a"   "t0"     -- sub x, a, x
  , assignConst "c2"  2                           -- (materialize #2 for xor)
  , assignBin  "x0_" (.Olxor .U64) "t1"  "c2"     -- eor x, x, #2

  -- one = 1
  , assignConst "one" 1                           -- mov one, #1

  -- First Newton step (5→10 bits)
  , assignBin  "t2"  (.Omul .U64) "a"    "x0_"    -- (a * x)
  , assignBin  "e1"  (.Oadd .U64) "t2"   "one"    -- madd e1, a, x, one
  , assignBin  "e2"  (.Omul .U64) "e1"   "e1"     -- mul e2, e1, e1
  , assignBin  "t4"  (.Omul .U64) "e1"   "x0_"    -- (e1 * x)
  , assignBin  "x1_" (.Oadd .U64) "t4"   "x0_"    -- madd x, e1, x, x

  -- Second Newton step (10→20 bits)
  , assignBin  "e4"  (.Omul .U64) "e2"   "e2"     -- mul e4, e2, e2
  , assignBin  "t6"  (.Omul .U64) "e2"   "x1_"    -- (e2 * x)
  , assignBin  "x2_" (.Oadd .U64) "t6"   "x1_"    -- madd x, e2, x, x

  -- Third Newton step (20→40 bits)
  , assignBin  "e8"  (.Omul .U64) "e4"   "e4"     -- mul e8, e4, e4
  , assignBin  "t8"  (.Omul .U64) "e4"   "x2_"    -- (e4 * x)
  , assignBin  "x3_" (.Oadd .U64) "t8"   "x2_"    -- madd x, e4, x, x

  -- Final Newton step (40→64 bits)
  , assignBin  "t9"  (.Omul .U64) "e8"   "x3_"    -- (e8 * x)
  , assignBin  "ret" (.Oadd .U64) "t9"   "x3_" ]  -- madd x0, e8, x, x

/-- Reference semantics via `pureEvalMonoCmd`. -/
def refSem (a : BitVec 64) : BitVec 64 :=
  pureEvalMonoCmd 64 (fun w => if w = v "a" then a else 0) (v "ret") body

/-! ### Closed-form Newton chain

Unfolding `pureEvalMonoCmd` over `body` instruction-by-instruction yields a
closed-form expression in `a`. We expose this once as `refSemClosed`,
prove `refSem = refSemClosed` by computation (every match arm of
`pureEvalMonoCmd` reduces, since all the SSA names are distinct strings),
and then state Newton correctness as a single `BitVec 64` equation. -/

/-- Closed-form Newton iteration: 5-bit seed plus four doubling steps,
    written directly as `BitVec 64` arithmetic. Each `x_{i+1}` line
    instantiates Newton's update `x · (2 + a·x)` (the variant that
    converges to the inverse of `-a`, hence the `+1` in the final spec). -/
def refSemClosed (a : BitVec 64) : BitVec 64 :=
  -- 5-bit seed: x0 = (a - (a<<<2)) XOR 2 = (-3·a) XOR 2
  let x0 := (a - (a <<< 2)) ^^^ 2
  -- Newton step 1 (5→10 bits): x1 = x0 · (2 + a·x0) written via the
  -- ARM source's actual instruction sequence (e1 := a·x0+1; x1 := e1·x0+x0).
  let e1 := a * x0 + 1
  let x1 := e1 * x0 + x0
  -- e2 = e1² is reused as the next "error" multiplier.
  let e2 := e1 * e1
  -- Newton step 2 (10→20 bits): x2 := e2·x1 + x1
  let x2 := e2 * x1 + x1
  let e4 := e2 * e2
  -- Newton step 3 (20→40 bits)
  let x3 := e4 * x2 + x2
  let e8 := e4 * e4
  -- Newton step 4 (40→64 bits) — final
  e8 * x3 + x3

/-- The proved-translator reference semantics agrees with the closed-form
    chain. Pure unfolding: `pureEvalMonoCmd` walks 18 `Cassgn` instructions,
    each of which reduces because variable names are distinct strings. -/
theorem refSem_eq_closed (a : BitVec 64) : refSem a = refSemClosed a := by
  rfl

/-- The 5-bit Newton seed `x0 = (a − 4·a) XOR 2`, paired with an odd `a`,
    produces an error `a*x0 + 1` whose low 5 bits are zero — equivalently,
    `(a*x0 + 1) &&& 0x1F = 0`. Single SAT goal in `a`, ~few seconds. -/
theorem seed_low5_zero (a : BitVec 64) (h_odd : a &&& 1 = 1) :
    let x0 := (a - (a <<< 2)) ^^^ 2
    (a * x0 + 1) &&& 0x1F = 0 := by
  bv_decide (config := { acNf := true })

/-- Squaring a `BitVec 64` whose low `k` bits are zero gives a value
    whose low `min(2k, 64)` bits are zero. We only need the four
    instantiations `k = 5, 10, 20, 40`. -/
private theorem sq_low5_to_low10 (e : BitVec 64) (h : e &&& 0x1F = 0) :
    (e * e) &&& 0x3FF = 0 := by
  bv_decide (config := { acNf := true })

private theorem sq_low10_to_low20 (e : BitVec 64) (h : e &&& 0x3FF = 0) :
    (e * e) &&& 0xFFFFF = 0 := by
  bv_decide (config := { acNf := true })

private theorem sq_low20_to_low40 (e : BitVec 64) (h : e &&& 0xFFFFF = 0) :
    (e * e) &&& 0xFFFFFFFFFF = 0 := by
  bv_decide (config := { acNf := true })

/-- Once 40 low bits are zero, one more squaring gives a value with all
    64 bits zero — i.e. plain equality with `0`. Final piece. -/
private theorem sq_low40_to_zero (e : BitVec 64) (h : e &&& 0xFFFFFFFFFF = 0) :
    e * e = 0 := by
  bv_decide (config := { acNf := true })

/-- The single Newton-step identity, `with a single squaring of error`.
    Given any `x` and any `e` satisfying the symbolic equation
    `e = a*x + 1`, the next iterate `x' = e*x + x` has error `a*x' + 1`
    equal to `e²`. This is a 3-variable bit-vector identity (`a, x, e`
    bound by the rewrite) — proved by `bv_decide` after substituting
    `e := a*x + 1`. -/
theorem newton_step_error (a x : BitVec 64) :
    a * ((a * x + 1) * x + x) + 1 = (a * x + 1) * (a * x + 1) := by
  -- Reduce to a `Nat` modular identity, then close via `ring_nf` since the
  -- map `BitVec 64 → ZMod (2^64) ≃ Nat (mod 2^64)` is a ring hom.
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul]
  ring_nf

/-- **Headline lemma.** Newton iteration over the 5→10→20→40→64 bit-width
    schedule produces a 64-bit integer `refSem a` such that
    `a · refSem a + 1 ≡ 0 (mod 2^64)` for **every odd** `a : BitVec 64`.

    This is the universal correctness statement that the concrete
    `native_decide` examples above only witness pointwise.

    **Proof.** Each Newton step squares the error `e_i := a · x_i + 1`
    (lemma `newton_step_error`). Starting with `a` odd, the seed `x0`
    gives `e_0` with low-5 bits zero (`seed_low5_zero`); four squarings
    push the zero-bit prefix to 10, 20, 40, 64. The last step concludes
    `e_3² = 0` in `BitVec 64`, which is exactly `a · x_4 + 1 = 0`. -/
theorem word_negmodinv_correct (a : BitVec 64)
    (h_odd : a &&& 1 = 1) :
    a * refSem a + 1 = 0 := by
  rw [refSem_eq_closed]
  -- Strategy: chain the `newton_step_error` rewrites bottom-up to
  -- eliminate the intermediate `e_i` in favour of `a*x_i + 1`. Then
  -- the squaring chain `low5 → low10 → low20 → low40 → 0` closes it.
  -- `simp only [refSemClosed]` does β/ζ/δ reduction so `set` can
  -- match the inlined patterns. Plain `unfold` leaves nested `have`s
  -- that `rw` cannot reach into.
  simp only [refSemClosed]
  set x0 : BitVec 64 := (a - (a <<< 2)) ^^^ 2
  -- Define the Newton iterates in line with `refSemClosed`.
  set x1 : BitVec 64 := (a * x0 + 1) * x0 + x0 with hx1_def
  -- After `set`, occurrences of `(a*x0+1)*x0 + x0` in the goal fold to `x1`.
  -- The remaining goal has `e2 = (a*x0+1) * (a*x0+1)` and `e2 * x1 + x1`.
  -- Replace `e2 = (a*x0+1)²` by `a*x1 + 1` using `newton_step_error`.
  have h_x1 : a * x1 + 1 = (a * x0 + 1) * (a * x0 + 1) := newton_step_error a x0
  -- Rewrite *inside* the goal: replace `(a*x0+1)*(a*x0+1)` by `a*x1 + 1`.
  rw [show (a * x0 + 1) * (a * x0 + 1) = a * x1 + 1 from h_x1.symm]
  -- Now `x2 := (a*x1+1) * x1 + x1`.
  set x2 : BitVec 64 := (a * x1 + 1) * x1 + x1 with hx2_def
  have h_x2 : a * x2 + 1 = (a * x1 + 1) * (a * x1 + 1) := newton_step_error a x1
  rw [show (a * x1 + 1) * (a * x1 + 1) = a * x2 + 1 from h_x2.symm]
  set x3 : BitVec 64 := (a * x2 + 1) * x2 + x2 with hx3_def
  have h_x3 : a * x3 + 1 = (a * x2 + 1) * (a * x2 + 1) := newton_step_error a x2
  rw [show (a * x2 + 1) * (a * x2 + 1) = a * x3 + 1 from h_x3.symm]
  -- Goal is now `a * ((a*x3 + 1) * x3 + x3) + 1 = 0`.
  -- One more application of `newton_step_error a x3` closes it.
  rw [newton_step_error a x3]
  -- Goal: `(a * x3 + 1) * (a * x3 + 1) = 0`.
  -- Establish the bit-prefix invariant for `e3 := a*x3 + 1` by chaining
  -- `seed_low5_zero` through three squarings. Each `rw` of `h_x?`
  -- replaces `a*x_? + 1` by the corresponding `e_{?-1}²`.
  have h_e0 : (a * x0 + 1) &&& 0x1F = 0 := seed_low5_zero a h_odd
  have h_e1 : (a * x1 + 1) &&& 0x3FF = 0 := by
    rw [h_x1]; exact sq_low5_to_low10 _ h_e0
  have h_e2 : (a * x2 + 1) &&& 0xFFFFF = 0 := by
    rw [h_x2]; exact sq_low10_to_low20 _ h_e1
  have h_e3 : (a * x3 + 1) &&& 0xFFFFFFFFFF = 0 := by
    rw [h_x3]; exact sq_low20_to_low40 _ h_e2
  exact sq_low40_to_zero _ h_e3

/-- Convenient `ZMod (2^64)` rephrasing. Often the consumer wants this
    statement in `ZMod` form (e.g. when chaining with field-extension
    proofs over base `ZMod p` for non-pow2 `p`). -/
theorem word_negmodinv_correct_nat (a : BitVec 64)
    (h_odd : a &&& 1 = 1) :
    (a.toNat * (refSem a).toNat + 1) % 2^64 = 0 := by
  have h := word_negmodinv_correct a h_odd
  -- Translate the `BitVec` equation to a `Nat` modular equation.
  have h2 : (a * refSem a + 1).toNat = (0 : BitVec 64).toNat := by rw [h]
  simpa [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] using h2

end NegModInv

/-! ## Port 3: `word_bytereverse.S` — body + reference semantics

ARM source (`arm/generic/word_bytereverse.S`):
```asm
        mov     x1, #0xFFFF0000FFFF0000
        mov     x2, #0x0000FFFF0000FFFF
        and     x1, x1, x0
        and     x2, x2, x0
        ror     x1, x1, #32
        orr     x0, x1, x2

        mov     x1, #0xFF00FF00FF00FF00
        mov     x2, #0x00FF00FF00FF00FF
        and     x1, x1, x0
        and     x2, x2, x0
        ror     x1, x1, #24
        ror     x2, x2, #8
        orr     x0, x1, x2
```
`ROR y, #n` is synthesised as `(y >>> n) | (y <<< (64-n))`. -/

namespace ByteReverse

def body : List InstrR :=
  -- Pass 1: swap 16-bit halves within each 32-bit lane
  [ assignConst "m1a"  (0xFFFF0000FFFF0000 : Int)
  , assignConst "m1b"  (0x0000FFFF0000FFFF : Int)
  , assignBin   "h1"   (.Oland .U64) "m1a" "a"
  , assignBin   "l1"   (.Oland .U64) "m1b" "a"
  , assignShR   "h1s"  "h1" 32
  , assignShL   "h1l"  "h1" 32
  , assignBin   "h1r"  (.Olor .U64) "h1s" "h1l"    -- ror(h1, 32)
  , assignBin   "r1"   (.Olor .U64) "h1r" "l1"

  -- Pass 2: swap bytes within each 16-bit half
  , assignConst "m2a"  (0xFF00FF00FF00FF00 : Int)
  , assignConst "m2b"  (0x00FF00FF00FF00FF : Int)
  , assignBin   "h2"   (.Oland .U64) "m2a" "r1"
  , assignBin   "l2"   (.Oland .U64) "m2b" "r1"
  , assignShR   "h2s"  "h2" 24
  , assignShL   "h2l"  "h2" 40                      -- 64 - 24
  , assignBin   "h2r"  (.Olor .U64) "h2s" "h2l"    -- ror(h2, 24)
  , assignShR   "l2s"  "l2" 8
  , assignShL   "l2l"  "l2" 56                      -- 64 - 8
  , assignBin   "l2r"  (.Olor .U64) "l2s" "l2l"    -- ror(l2, 8)
  , assignBin   "ret"  (.Olor .U64) "h2r" "l2r" ]

def refSem (a : BitVec 64) : BitVec 64 :=
  pureEvalMonoCmd 64 (fun w => if w = v "a" then a else 0) (v "ret") body

end ByteReverse

/-! ## Port 11: `word_avg` — body + reference semantics

`(a + b) / 2 = (a & b) + ((a ^ b) >> 1)`. Computes the average of two u64s
without the intermediate overflow. -/

namespace WordAvg

def body : List InstrR :=
  [ assignBin "an" (.Oland .U64) "a" "b"    -- a & b
  , assignBin "ax" (.Olxor .U64) "a" "b"    -- a ^ b
  , assignShR "ah" "ax" 1                    -- (a ^ b) >> 1
  , assignBin "ret" (.Oadd .U64) "an" "ah" ]

def refSem (a b : BitVec 64) : BitVec 64 :=
  (a &&& b) + ((a ^^^ b) >>> 1)

end WordAvg

end CatCrypt.Crypto.Jasmin.S2NBignumSSA
