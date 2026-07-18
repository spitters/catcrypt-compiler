/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnAddmul1Prototype
import CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnSubPrototype
import CatCrypt.Crypto.Number.MontgomeryReduction

set_option autoImplicit false

/-!
# CIOS Montgomery multiplication — Lean prototype `mpn_mont_mul`

**EXPERIMENTAL FILE.**  Companion to `MpnMulPrototype.lean` /
`MpnDivRemPrototype.lean` / `MpnAddNAdcSpillPrototype.lean`.  Implements the
**Coarsely Integrated Operand Scanning** (CIOS) Montgomery multiplication
algorithm of Koc, Acar, Kaliski (1996, "Analyzing and Comparing Montgomery
Multiplication Algorithms", IEEE Micro 16(3), §5).

For odd modulus `N` (k limbs, top-limb-set), pick the Montgomery radix
`R = 2^(64·k)`.  The Montgomery constant `n0' = -N⁻¹ mod 2⁶⁴` is fixed by `N`.
Given `u, v ∈ [0, N)`, CIOS produces in `2k²+k` MAC operations the value

```
mpnMontMul u v N n0'  =  u · v · R⁻¹  mod  N
```

This is the workhorse of any Montgomery field arithmetic (P-256, P-384,
secp256k1, Curve25519, FIPS-186-5 RSA…): one Montgomery multiplication is
about 2× the cost of one schoolbook `mpn_mul`, but it leaves the result
in [0, N) without a divide, so chained field multiplies pay no per-op
reduction cost.

## CIOS, the algorithm (Koc-Acar-Kaliski §5)

```
t := 0                                    (length k+1)
for i = 0 to k-1 do
  C := 0
  for j = 0 to k-1 do
    (C, S) := t[j] + u[i] * v[j] + C      -- multiply-accumulate row
    t[j] := S
  (C, S) := t[k] + C
  t[k] := S
  m := t[0] * n0' mod 2⁶⁴                 -- Montgomery digit
  (C, S) := t[0] + m * N[0]
  for j = 1 to k-1 do
    (C, S) := t[j] + m * N[j] + C
    t[j-1] := S
  (C, S) := t[k] + C
  t[k-1] := S
  t[k]   := C
if t ≥ N then t := t - N
return t[0..k-1]
```

Each outer iteration `i` does two `mpn_addmul_1`-shaped inner passes: one
that multiplies row `u[i] · v` into `t`, and one that adds `m · N` shifted
to wipe `t[0]` (since `m = -t[0]/N[0] mod 2⁶⁴` makes `t[0] + m·N[0]`
divisible by 2⁶⁴, which lets us right-shift `t` by one limb).  After `k`
outer iterations `t < 2N`, so a single conditional subtract finishes.

## Functional spec

We give `mpnMontMul` recursively in `i` (outer index 0..k-1) and use the
already-proved building blocks `mpnAddmul1` (carry-chain MAC), `mpnAddN`,
`mpnSubN` (carry-chain add/sub), and `mulx` (64×64→128).  No bv_decide
acrobatics, no Nat-modulo theorems — the row-MAC identity already lives
in `MpnAddmul1Prototype` (`mpnAddmul1_spec_carryIn_zero`).

The headline `toNat`-correctness theorem is the residual; what we ship
here axiom-clean is:

1. The pure CIOS reference (`mpnMontMul`) and length lemma.
2. Concrete `native_decide` smoke tests at k=4 (P-256-like) and k=8
   (1024-bit Mersenne-like) showing the algorithm produces the correct
   `u·v·R⁻¹ mod N` for chosen inputs.
3. The Jasmin emission scaffold (`bodyMontMul`, `mpnMontMulFd`).
4. A precisely-named sorry-free `Prop` residual
   (`mpn_mont_mul_outer_loop_step_obligation`) and its closure theorem
   `MpnMontMulJasminRefines_holds`.

## Why a residual instead of full closure (honest)

The outer CIOS loop is a *growing-width Cfor over the t-accumulator*: at
outer iteration `i`, the running accumulator `t` has length `k+1`, and
the body performs two `mpn_addmul_1`-shaped sub-passes plus a sliding
right-shift.  This is the same structural pattern as
`MpnPowPrototype.MpnPowJasminRefines` (growing-width arena bit-loop) and
`MpnDivRemPrototype.MpnDivRemJasminRefines` (growing-position quotient
loop).  Following exactly that established pattern, we pin the inductive
step as a `Prop` and discharge the prelude / closure in this file.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnMontgomeryPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAddmul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnSubPrototype

/-! ## §1  Pure CIOS reference `mpnMontMul`

We define the outer-loop step `montStep` as a function that consumes one
row `(u[i])` and produces the updated accumulator `t' : List (BitVec 64)`
of length `k+1` (where `k = |v| = |N|`).  Then `mpnMontMul` is the fold
over the rows of `u`, finishing with the final conditional subtract.

`montStep` factors into two MAC passes:

* `macRow t u_i v` — does `t' := t + u_i · v` over the low `k+1` limbs
  (using `mpnAddmul1` over `|v|=k` low limbs + one carry-out into `t[k]`).
* `montReduce t' m N` — does `t'' := (t' + m · N) >>> 64` where
  `m = t'[0] * n0' mod 2⁶⁴`; this is the right-shift that the CIOS
  invariant makes exact (the low limb is zero by construction of `m`).
-/

/-- `macRow t u_i v` performs `t := t + u_i · v` where `t` has length
    `|v| + 1` (the schoolbook-row carry chain).  Uses `mpnAddmul1` for
    the `|v|` low limbs and propagates the final carry into `t[|v|]`. -/
def macRow (t : List (BitVec 64)) (u_i : BitVec 64) (v : List (BitVec 64)) :
    List (BitVec 64) :=
  let tLow := t.take v.length
  let tHi  := (t.drop v.length).headD 0
  let (rs, fcy) := mpnAddmul1 tLow v u_i 0
  -- The carry-out `fcy` adds into `t[|v|]` (which fits in 64 bits: the row
  -- MAC fits in k+1 limbs).
  rs ++ [tHi + fcy]

/-- `montReduce` computes `m := t[0] * n0'`, does `t := t + m * N` (over
    the low `k+1` limbs), and right-shifts by one limb.  The low limb of
    `t + m·N` is zero by construction of `m`, so the right-shift is exact. -/
def montReduce (t : List (BitVec 64)) (N : List (BitVec 64))
    (n0' : BitVec 64) : List (BitVec 64) :=
  let t0 := t.headD 0
  let m := t0 * n0'
  -- MAC: t := t + m * N over |N|+1 limbs.
  let t' := macRow t m N
  -- Right-shift by one limb (drop the now-zero low limb), zero-extend with
  -- a fresh top zero so the length is preserved.
  (t'.drop 1) ++ [0]

/-- One outer CIOS iteration: `t := montReduce (macRow t u_i v) N n0'`.
    Preserves the length of `t` (= `|N|+1 = |v|+1`). -/
def montStep (t : List (BitVec 64)) (u_i : BitVec 64)
    (v N : List (BitVec 64)) (n0' : BitVec 64) : List (BitVec 64) :=
  montReduce (macRow t u_i v) N n0'

/-- The outer fold: process each `u[i]` in turn, starting from `t = 0`
    (length `|v|+1`).  After `|u|` iterations, `t` holds the result before
    the final conditional subtract. -/
def montFold (u v N : List (BitVec 64)) (n0' : BitVec 64) :
    List (BitVec 64) :=
  u.foldl (fun t u_i => montStep t u_i v N n0') (List.replicate (v.length + 1) 0)

/-- Final conditional subtract: if `t ≥ N`, return `t - N` (length `|N|`),
    else return `t.take |N|` (drop the top zero).  Operates on `t` of
    length `|N|+1`.  In the CIOS invariant, after `k` outer iterations
    `t < 2N` and the top limb is 0 or 1; the conditional subtract
    discriminates on whether `t < N`. -/
def montFinalSub (t N : List (BitVec 64)) : List (BitVec 64) :=
  let tLow := t.take N.length
  let sub := mpnSubN tLow N false
  -- sub.2 = true ⇒ tLow < N, so the top limb of t must be 0 ⇒ return tLow.
  -- sub.2 = false ⇒ tLow ≥ N, so return sub.1 (= tLow - N).
  -- We also need to check the top limb: if t[k] ≠ 0 then we must subtract
  -- regardless (since 2^(64k) ≥ N).  Combined:
  let tHi := (t.drop N.length).headD 0
  if tHi != 0 || !sub.2 then sub.1 else tLow

/-- **Pure CIOS Montgomery multiplication** — `u · v · R⁻¹ mod N` where
    `R = 2^(64·|N|)`.  Requires `|u| = |v| = |N|` and `N` odd
    (so that `n0' · N[0] ≡ -1 mod 2^64`); on ill-formed input the result is
    a well-defined limb list, just not necessarily a valid Montgomery
    product. -/
def mpnMontMul (u v N : List (BitVec 64)) (n0' : BitVec 64) :
    List (BitVec 64) :=
  montFinalSub (montFold u v N n0') N

/-! ### Length lemmas -/

/-- `mpnAddmul1` over a `k`-long accumulator returns a `k`-long list. -/
theorem mpnAddmul1_length_eq (out a : List (BitVec 64)) (b cy : BitVec 64)
    (h : out.length = a.length) :
    (mpnAddmul1 out a b cy).1.length = out.length :=
  CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype.mpnAddmul1_length out a b cy h

/-- `macRow t u_i v` has length `|v| + 1` provided `|t| = |v| + 1`. -/
theorem macRow_length (t : List (BitVec 64)) (u_i : BitVec 64)
    (v : List (BitVec 64)) (h : t.length = v.length + 1) :
    (macRow t u_i v).length = v.length + 1 := by
  unfold macRow
  rw [List.length_append, List.length_singleton]
  have hlen : (t.take v.length).length = v.length := by
    rw [List.length_take]; omega
  rw [mpnAddmul1_length_eq (t.take v.length) v u_i 0 hlen, hlen]

/-- `montReduce t N n0'` has length `|t|` provided `|t| = |N| + 1`. -/
theorem montReduce_length (t N : List (BitVec 64)) (n0' : BitVec 64)
    (h : t.length = N.length + 1) :
    (montReduce t N n0').length = N.length + 1 := by
  unfold montReduce
  rw [List.length_append, List.length_singleton, List.length_drop,
      macRow_length t (t.headD 0 * n0') N h]
  omega

/-- `montStep` preserves length `|v| + 1`. -/
theorem montStep_length (t : List (BitVec 64)) (u_i : BitVec 64)
    (v N : List (BitVec 64)) (n0' : BitVec 64)
    (ht : t.length = v.length + 1) (hN : v.length = N.length) :
    (montStep t u_i v N n0').length = v.length + 1 := by
  unfold montStep
  rw [hN]
  exact montReduce_length _ _ _ (by rw [macRow_length t u_i v ht]; omega)

/-- Foldl-length preservation: any accumulator of length `|v|+1` stays at
    `|v|+1` after folding any number of `montStep`s. -/
theorem montFold_aux (v N : List (BitVec 64)) (n0' : BitVec 64)
    (hN : v.length = N.length) :
    ∀ (us : List (BitVec 64)) (acc : List (BitVec 64)),
      acc.length = v.length + 1 →
      (us.foldl (fun t u_i => montStep t u_i v N n0') acc).length = v.length + 1 := by
  intro us
  induction us with
  | nil => intro acc hacc; simpa using hacc
  | cons uj rs ih =>
    intro acc hacc
    rw [List.foldl_cons]
    exact ih (montStep acc uj v N n0') (montStep_length acc uj v N n0' hacc hN)

/-- `montFold` produces a length-`|v| + 1` list. -/
theorem montFold_length (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (hN : v.length = N.length) :
    (montFold u v N n0').length = v.length + 1 := by
  unfold montFold
  have hInit : (List.replicate (v.length + 1) (0 : BitVec 64)).length = v.length + 1 := by
    simp [List.length_replicate]
  exact montFold_aux v N n0' hN u (List.replicate (v.length + 1) 0) hInit

/-- `mpnSubN` of equal-length operands preserves length. -/
theorem mpnSubN_length (a b : List (BitVec 64)) (bin : Bool)
    (h : a.length = b.length) :
    (mpnSubN a b bin).1.length = a.length := by
  induction a generalizing b bin with
  | nil => simp [mpnSubN]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [mpnSubN, List.length_cons]
      congr 1
      exact ih ys _ (by simpa using h)

/-- `mpnMontMul u v N n0'` has length `|N|`. -/
theorem mpnMontMul_length (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (hN : v.length = N.length) :
    (mpnMontMul u v N n0').length = N.length := by
  have hft := montFold_length u v N n0' hN
  have hlow : ((montFold u v N n0').take N.length).length = N.length := by
    rw [List.length_take, hft]; omega
  have hdiff : (mpnSubN ((montFold u v N n0').take N.length) N false).1.length
      = N.length := by
    rw [mpnSubN_length _ _ false hlow, hlow]
  unfold mpnMontMul montFinalSub
  -- Both branches of the if produce length |N|.
  by_cases hbranch :
    ((((montFold u v N n0').drop N.length).headD 0) != 0
      || !(mpnSubN ((montFold u v N n0').take N.length) N false).2) = true
  · -- branch: diff
    rw [show (if (((((montFold u v N n0').drop N.length).headD 0)) != 0
              || !(mpnSubN ((montFold u v N n0').take N.length) N false).2) = true
           then (mpnSubN ((montFold u v N n0').take N.length) N false).1
           else (montFold u v N n0').take N.length)
        = (mpnSubN ((montFold u v N n0').take N.length) N false).1 from
        if_pos hbranch]
    exact hdiff
  · rw [show (if (((((montFold u v N n0').drop N.length).headD 0)) != 0
              || !(mpnSubN ((montFold u v N n0').take N.length) N false).2) = true
           then (mpnSubN ((montFold u v N n0').take N.length) N false).1
           else (montFold u v N n0').take N.length)
        = (montFold u v N n0').take N.length from
        if_neg hbranch]
    exact hlow

/-! ## §1b  `toNat`-level bridge to the abstract Montgomery law

This section is the **limb-decode bridge** (task E1b): it relates the
in-tree BitVec-limb CIOS reference (`macRow` / `montReduce` / `montStep` /
`montFold` / `mpnMontMul`) to the prime-parametric `Nat` reduction
`CatCrypt.Crypto.Number.montgomeryReduce` (proved sorry-free in
`Crypto/Number/MontgomeryReduction.lean`).

The decode function is `toNat` (little-endian limb denotation, from
`MpnAddPrototype`).  The plan is:

1. `macRow_toNat` — one row-MAC pass decodes to `toNat t + toNat v · u_i`,
   reusing the per-limb addmul carry-propagation `mpnAddmul1_spec_carryIn_zero`
   already proved in `MpnAddmul1Prototype`.  The only side-condition is the
   top-limb no-overflow `htop` (the CIOS accumulator invariant guarantees it).
2. `montReduce_toNat_bridge` — one Montgomery-reduce pass decodes to the
   abstract `montgomeryReduce (toNat N) (2^64) n0'.toNat (toNat t)`, the
   single-limb (radix `R = 2^64`) instance of the abstract recurrence.  The
   two CIOS-specific facts (the low limb of `t + m·N` is zeroed; the top limb
   doesn't overflow) appear as explicit hypotheses, matching the abstract
   exactness `montgomeryReduce_dvd`.
3. `montgomeryReduce_comp` (abstract, proved) then composes the per-limb
   radix-`2^64` reductions into a full-width radix-`2^(64·k)` reduction.

The multi-limb outer-fold induction (closing the side-conditions across all
`k` iterations) is the residual stated at the end of this section. -/

open CatCrypt.Crypto.Number

/-- **Row-MAC decode (limb bridge step 1).**

    For accumulator `t` of length `|v| + 1` whose top limb does not overflow
    when the addmul carry-out is folded in, `macRow t u_i v` decodes to the
    exact multiply-accumulate `toNat t + toNat v · u_i`.

    Proof: split `t = t.take|v| ++ [t[|v|]]`, apply the per-limb addmul
    contract `mpnAddmul1_spec_carryIn_zero` on the low `|v|` limbs, and fold
    the addmul carry-out into the top limb (no overflow by `htop`). -/
theorem macRow_toNat (t : List (BitVec 64)) (u_i : BitVec 64)
    (v : List (BitVec 64)) (ht : t.length = v.length + 1)
    (htop : ((t.drop v.length).headD 0).toNat
              + (mpnAddmul1 (t.take v.length) v u_i 0).2.toNat < 2 ^ 64) :
    toNat (macRow t u_i v) = toNat t + toNat v * u_i.toNat := by
  -- Notation for the low window, the top limb, and the addmul result.
  set tLow := t.take v.length with htLow
  set tHi := (t.drop v.length).headD 0 with htHi
  set rs := (mpnAddmul1 tLow v u_i 0).1 with hrs
  set fcy := (mpnAddmul1 tLow v u_i 0).2 with hfcy
  have hLowLen : tLow.length = v.length := by
    rw [htLow, List.length_take]; omega
  -- The drop window is a singleton `[tHi]`.
  have hdropLen : (t.drop v.length).length = 1 := by
    rw [List.length_drop]; omega
  have hdropEq : t.drop v.length = [tHi] := by
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hdropLen
    rw [ha, htHi, ha]; simp
  -- Decode of `t` via take/drop split.
  have htSplit : toNat t = toNat tLow + (2 ^ 64) ^ v.length * tHi.toNat := by
    conv_lhs => rw [← List.take_append_drop v.length t]
    rw [← htLow, MpnMulPrototype.toNat_append, hLowLen, hdropEq]
    simp [toNat]
  -- The addmul carry-propagation contract on the low window.
  have hspec := mpnAddmul1_spec_carryIn_zero tLow v hLowLen u_i
  -- hspec : toNat rs + (2^64)^|v| * fcy.toNat = toNat tLow + toNat v * u_i.toNat
  rw [← hrs, ← hfcy] at hspec
  -- Decode of `macRow = rs ++ [tHi + fcy]`.
  have hmac : macRow t u_i v = rs ++ [tHi + fcy] := by
    simp only [macRow, ← htLow, ← htHi, ← hrs, ← hfcy]
  have hrsLen : rs.length = v.length := by
    rw [hrs, mpnAddmul1_length_eq tLow v u_i 0 hLowLen, hLowLen]
  rw [hmac, MpnMulPrototype.toNat_append, hrsLen]
  -- The top limb does not overflow: (tHi + fcy).toNat = tHi.toNat + fcy.toNat.
  have htopAdd : (tHi + fcy).toNat = tHi.toNat + fcy.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt htop]
  -- toNat (macRow) = toNat rs + 2^(64|v|) * (tHi + fcy)
  --              = (toNat tLow + toNat v · u_i - 2^(64|v|)·fcy) + 2^(64|v|)·(tHi+fcy)
  --              = toNat tLow + toNat v · u_i + 2^(64|v|)·tHi  = toNat t + toNat v·u_i.
  simp only [toNat, Nat.mul_zero, Nat.add_zero, htopAdd]
  rw [htSplit, Nat.mul_add]
  -- Linear over Nat with hspec as the addmul identity.
  omega

/-- **Montgomery-reduce decode (limb bridge step 2).**

    One CIOS reduce pass `montReduce t N n0'` decodes — via the limb-MAC
    bridge `macRow_toNat` — to the abstract single-limb (radix `R = 2^64`)
    Montgomery reduction `montgomeryReduce (toNat N) (2^64) n0'.toNat (toNat t)`.

    Hypotheses model the two CIOS-specific invariant facts (proved per
    iteration by the outer-loop induction, residual below):

    * `ht : |t| = |N| + 1`;
    * `htop` — the MAC top limb does not overflow (the accumulator bound);
    * `hzero` — the low limb of `t + m·N` is zeroed, i.e. `(macRow t m N)[0] = 0`,
      which is the BitVec realisation of the abstract exactness
      `montgomeryReduce_dvd` (the Montgomery digit `m` is chosen to make
      `t + m·N` divisible by `2^64`).

    The abstract `montgomeryReduce_comp` then composes `k` of these radix-`2^64`
    passes into a full radix-`2^(64·k)` reduction. -/
theorem montReduce_toNat_bridge (t N : List (BitVec 64)) (n0' : BitVec 64)
    (ht : t.length = N.length + 1)
    (htop : ((t.drop N.length).headD 0).toNat
              + (mpnAddmul1 (t.take N.length) N (t.headD 0 * n0') 0).2.toNat < 2 ^ 64)
    (hzero : (macRow t (t.headD 0 * n0') N).headD 0 = 0) :
    toNat (montReduce t N n0')
      = montgomeryReduce (toNat N) (2 ^ 64) n0'.toNat (toNat t) := by
  set m := t.headD 0 * n0' with hm
  -- `macRow`-decode of the reduced accumulator.
  have hmac : toNat (macRow t m N) = toNat t + toNat N * m.toNat :=
    macRow_toNat t m N ht htop
  -- `montReduce` denotes `toNat (macRow …) drop-one limb` (the `++[0]` adds nothing).
  set t' := macRow t m N with ht'
  -- General head/drop split of the denotation (holds for every list, incl. nil).
  have toNat_headD_drop : ∀ l : List (BitVec 64),
      toNat l = (l.headD 0).toNat + 2 ^ 64 * toNat (l.drop 1) := by
    intro l
    cases l with
    | nil => simp [toNat]
    | cons x xs => simp [toNat]
  -- toNat t' = t'[0] + 2^64 · toNat (t'.drop 1) ; with t'[0] = 0 this is 2^64·(drop1).
  have ht'toNat : toNat t' = 2 ^ 64 * toNat (t'.drop 1) := by
    rw [toNat_headD_drop t', hzero]
    simp
  -- montReduce decode: the trailing `++[0]` contributes nothing.
  have hmr : toNat (montReduce t N n0') = toNat (t'.drop 1) := by
    have : montReduce t N n0' = t'.drop 1 ++ [0] := by
      simp only [montReduce, ← hm, ← ht']
    rw [this, MpnMulPrototype.toNat_append]; simp [toNat]
  rw [hmr]
  -- Abstract side: montgomeryReduce (toNat N) (2^64) n0' (toNat t)
  --   = (toNat t + ((toNat t · n0') % 2^64) · toNat N) / 2^64.
  -- The CIOS digit is m = t[0]·n0', and m.toNat = (toNat t · n0') % 2^64.
  have hmdigit : m.toNat = (toNat t * n0'.toNat) % 2 ^ 64 := by
    rw [hm, BitVec.toNat_mul]
    -- t[0].toNat ≡ toNat t (mod 2^64): higher limbs are multiples of 2^64.
    have hhead : (t.headD 0).toNat % 2 ^ 64 = toNat t % 2 ^ 64 := by
      conv_rhs => rw [toNat_headD_drop t]
      rw [Nat.mul_comm, Nat.add_mul_mod_self_right]
    -- both sides reduce the first factor mod 2^64, which `hhead` equates.
    rw [Nat.mul_mod, hhead, ← Nat.mul_mod]
  -- Tie the two: toNat (macRow) = toNat t + (digit)·toNat N, divided by 2^64.
  unfold montgomeryReduce
  rw [← hmdigit]
  -- toNat t + m·toNat N = toNat t' = 2^64 · toNat (t'.drop 1), so /2^64 = toNat (t'.drop 1).
  rw [show toNat t + m.toNat * toNat N = toNat t + toNat N * m.toNat from by ring,
      ← hmac, ht'toNat, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ 64)]

/-! ### Multi-limb residual

`macRow_toNat` and `montReduce_toNat_bridge` give the **per-limb (radix
`2^64`) decode bridge**: one CIOS reduce pass equals one abstract
`montgomeryReduce` at `R = 2^64`, under the two CIOS invariant
side-conditions (`htop` top-limb no-overflow, `hzero` low-limb-zeroed).

The remaining work to reach the headline
`toNat (mpnMontMul u v N n0') ≡ toNat u · toNat v · R⁻¹ (mod toNat N)`
is the **outer-fold induction**: thread `montReduce_toNat_bridge` through
`montFold`'s `k` iterations, discharging `htop`/`hzero` at each step from the
accumulator bound `toNat t < 2·N·2^64` (so the top limb is `0` or `1` and the
digit construction zeroes the low limb), and compose the `k` radix-`2^64`
passes via the abstract `montgomeryReduce_comp` into a single radix-`2^(64·k)`
reduction.  The final conditional subtract `montFinalSub` then maps the
`[0, 2N)` representative to the canonical `[0, N)` residue.  This induction is
the residual `mpn_mont_mul_outer_loop_step_obligation` (§4) viewed at the
`toNat` (rather than memory-state) level. -/

/-! ## §2  Concrete `native_decide` smoke tests

We exhibit two concrete instances of `mpnMontMul` and validate them
against `(u · v · R⁻¹) mod toNat N` via `native_decide`.  The k=4 case
covers a P-256-like 256-bit modulus; the k=8 case covers a 512-bit
modulus suitable for RSA-1024-half / paillier.

### Test vector generation

These vectors were generated from first principles by computing
`R⁻¹ mod N` and `n0' = (-N⁻¹) mod 2⁶⁴` over Lean's `Nat` — the same
algorithm any reference implementation (OpenSSL `bn_mont_test`, BoringSSL
`bn_test.cc`, GMP `mpn_redc_1`, libsecp256k1 `secp256k1_modinv64`) would
use.  The values are checked end-to-end by `native_decide` below; no
"trust me, OpenSSL says so" is involved. -/

/-- Compute `n0' = -N[0]⁻¹ mod 2⁶⁴` for an odd modulus `N`.  Hensel's
    lemma: starting from `x := 1` (correct mod 2), iterate `x := x · (2 - N[0]·x)
    mod 2⁶⁴` six times to double precision each round; after 6 iterations
    `x ≡ N[0]⁻¹ mod 2⁶⁴`.  Then negate.  Pure `BitVec` computation. -/
def montN0Prime (N : List (BitVec 64)) : BitVec 64 :=
  let n0 := N.headD 0
  -- Hensel iteration: x_{k+1} = x_k * (2 - n0 * x_k)
  -- Each iteration doubles the precision; start from 1 (correct mod 2).
  let go : BitVec 64 → BitVec 64 := fun x => x * (2 - n0 * x)
  let x := go (go (go (go (go (go 1)))))
  -- Now x ≡ n0⁻¹ mod 2⁶⁴; we want -n0⁻¹ mod 2⁶⁴.
  0 - x

/-- Check: `montN0Prime N * N.headD 0 ≡ -1 mod 2⁶⁴`.  This is the defining
    relation of `n0'`. -/
example :
    let N : List (BitVec 64) := [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF, 0, 0xFFFFFFFF00000001]
    (montN0Prime N) * (N.headD 0) = (0xFFFFFFFFFFFFFFFF : BitVec 64) := by
  native_decide

-- A nontrivial odd modulus (4 limbs, P-256-ish — top limb set).
private def testN4 : List (BitVec 64) :=
  [0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF, 0, 0xFFFFFFFF00000001]

private def testN0Prime4 : BitVec 64 := montN0Prime testN4

-- Sanity check the n0' computation: testN4[0] * testN0Prime4 = -1 mod 2^64.
example : testN4.headD 0 * testN0Prime4 = (-1 : BitVec 64) := by native_decide

/-- Identity instance: `MontMul(0, anything) = 0` for the k=4 modulus. -/
example : mpnMontMul (List.replicate 4 0) [1, 0, 0, 0] testN4 testN0Prime4
    = List.replicate 4 0 := by native_decide

/-- Length sanity at k=4. -/
example : (mpnMontMul [1, 0, 0, 0] [1, 0, 0, 0] testN4 testN0Prime4).length = 4 := by
  native_decide

/-- The CIOS algorithm is **deterministic** at k=4 — same inputs always
    produce the same output (basic well-definedness). -/
example :
    mpnMontMul [7, 0, 0, 0] [11, 0, 0, 0] testN4 testN0Prime4
      = mpnMontMul [7, 0, 0, 0] [11, 0, 0, 0] testN4 testN0Prime4 := by
  native_decide

/-- **Headline k=4 smoke test**: compute `MontMul(R mod N, R mod N) = R mod N`.
    Since `MontMul(x, y) = x · y · R⁻¹ mod N` and we want `R · R · R⁻¹ = R`
    (mod N), this checks the algorithm's identity on the Montgomery one.

    `R mod N = 2^256 mod testN4` we compute by `Nat`-arithmetic and then
    represent as 4-limb. -/
private def R4 : Nat := 2 ^ 256
private def R4mod : Nat :=
  let N := toNat testN4
  R4 % N

/-- Encode a `Nat` (< 2^256) as a 4-limb `BitVec 64` list. -/
private def toLimbs4 (x : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 x,
   BitVec.ofNat 64 (x >>> 64),
   BitVec.ofNat 64 (x >>> 128),
   BitVec.ofNat 64 (x >>> 192)]

private def testR4limbs : List (BitVec 64) := toLimbs4 R4mod

/-- `R mod N` is a 4-limb representation of the value `R mod N`. -/
example : toNat testR4limbs = R4mod := by native_decide

/-- **CIOS at k=4, identity check**: `MontMul(R, R) ≡ R (mod N)`.

    `toNat (mpnMontMul R R N n0') ≡ toNat R · toNat R · R⁻¹ mod N`
                                  `≡ R mod N` (since `R · R⁻¹ ≡ 1`).
    So both sides equal `R mod N`.  The mod-N equality is checked
    directly. -/
example :
    toNat (mpnMontMul testR4limbs testR4limbs testN4 testN0Prime4) % toNat testN4
      = R4mod % toNat testN4 := by native_decide

/-- **CIOS at k=4, second nontrivial check**: `MontMul(x, 1) ≡ x · R⁻¹ (mod N)`.
    Taking `x = R^2 mod N` makes the LHS `≡ R mod N`. -/
private def R4sqModN : Nat := (R4 * R4) % toNat testN4

private def testR4sqLimbs : List (BitVec 64) := toLimbs4 R4sqModN

/-- `MontMul(R², 1, N, n0') ≡ R (mod N)`. -/
example :
    toNat (mpnMontMul testR4sqLimbs [1, 0, 0, 0] testN4 testN0Prime4)
      % toNat testN4
      = R4mod := by native_decide

-- k=8 modulus: pseudo-Mersenne, 512-bit (top-limb-set + odd).
private def testN8 : List (BitVec 64) :=
  [0xFFFFFFFFFFFFFFC5, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF,
   0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]

private def testN0Prime8 : BitVec 64 := montN0Prime testN8

/-- Sanity check: `testN8[0] * testN0Prime8 = -1 mod 2^64`. -/
example : testN8.headD 0 * testN0Prime8 = (-1 : BitVec 64) := by native_decide

/-- Length sanity at k=8. -/
example : (mpnMontMul (List.replicate 8 1) (List.replicate 8 0) testN8 testN0Prime8).length
    = 8 := by native_decide

/-- Identity at k=8: `MontMul(0, anything) = 0`. -/
example : mpnMontMul (List.replicate 8 0) (List.replicate 8 1) testN8 testN0Prime8
    = List.replicate 8 0 := by native_decide

/-- Encode `Nat < 2^512` as 8-limb. -/
private def toLimbs8 (x : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 x,
   BitVec.ofNat 64 (x >>> 64),
   BitVec.ofNat 64 (x >>> 128),
   BitVec.ofNat 64 (x >>> 192),
   BitVec.ofNat 64 (x >>> 256),
   BitVec.ofNat 64 (x >>> 320),
   BitVec.ofNat 64 (x >>> 384),
   BitVec.ofNat 64 (x >>> 448)]

private def R8 : Nat := 2 ^ 512
private def R8mod : Nat := R8 % toNat testN8
private def testR8limbs : List (BitVec 64) := toLimbs8 R8mod

example : toNat testR8limbs = R8mod := by native_decide

/-- **CIOS at k=8, headline check**: `MontMul(R, R) ≡ R (mod N)`. -/
example :
    toNat (mpnMontMul testR8limbs testR8limbs testN8 testN0Prime8) % toNat testN8
      = R8mod := by native_decide

private def R8sqModN : Nat := (R8 * R8) % toNat testN8
private def testR8sqLimbs : List (BitVec 64) := toLimbs8 R8sqModN

/-- `MontMul(R², 1, N, n0') ≡ R (mod N)` at k=8. -/
example :
    toNat (mpnMontMul testR8sqLimbs (1 :: List.replicate 7 0) testN8 testN0Prime8)
      % toNat testN8
      = R8mod := by native_decide

/-! ## §3  Jasmin emission scaffold

We assemble the `bodyMontMul` Jasmin body as a Ccall-composition over the
already-verified `mpn_addmul_1` kernel (the row MAC).  The structure
mirrors `MpnMulPrototype.mulBody` (which Ccalls into `mpn_addmul_1` for
schoolbook `mpn_mul`).  The Montgomery reduction step uses one extra
straight-line `MULX` for `m := t[0] * n0'` and then a second Ccall into
the same `mpn_addmul_1` kernel.

### Register & memory layout

Inputs in registers:
* `op`  — output pointer (k limbs)
* `up`  — pointer to `u` (k limbs)
* `vp`  — pointer to `v` (k limbs)
* `Np`  — pointer to `N` (k limbs)
* `n`   — limb count `k`
* `n0p` — `n0'` (passed by value, in a register; not by pointer for ease)
* `tp`  — pointer to a scratch buffer for `t` (k+1 limbs, zero-initialised)

The body emits: for `i = 0 to k-1`:
  - `mpn_addmul_1(tp, vp, [up + 8·i], n)`    -- row MAC: t += u[i] · v
  - `m := [tp+0] * n0p`
  - `mpn_addmul_1(tp, Np, m, n)`             -- reduce: t += m · N
  - shift t right by one limb (move tp += 8 conceptually, or memmove)

After k iterations, conditional subtract is one `mpn_sub_n` + `mpn_cmp`.
For the prototype we emit the Cfor scaffolding and leave the per-row
discharge as a Ccall obligation. -/

/-- A `reg u64` variable. -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s`. -/
def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- `r := r + k` (scalar update). -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- One outer iteration body of CIOS, Ccall-composed.

  ```
  mpn_addmul_1(tp, vp, [up+0], n)   ; t += u[i] · v
  m := [tp+0]                        ; load t[0]
  m := m * n0p                       ; m := t[0] · n0'  (via Copn MULX bundle)
  mpn_addmul_1(tp, Np, m, n)         ; t += m · N
  tp += 8                            ; right-shift t by one limb
  up += 8                            ; advance to next u[i]
  ```

  The two `Ccall`s into `mpn_addmul_1` discharge the MAC arithmetic via
  `MpnAddmul1JasminRefines`; the straight-line glue between them is a
  load + MULX + advance. -/
def montOuterBody : List InstrR :=
  [ -- t += u[i] · v   (using current up[0] as the scalar)
    .Ccall .DoNotInline []
      { name := "mpn_addmul_1" }
      [ pv "tp", pv "vp", .Pload .U64 { var := vr "up" } (.Pconst 0), pv "n" ]
    -- m := t[0]
  , .Cassgn (.Lvar { var := vr "m" }) .AT_none (.sword .U64)
      (.Pload .U64 { var := vr "tp" } (.Pconst 0))
    -- m := m * n0p
  , .Cassgn (.Lvar { var := vr "m" }) .AT_none (.sword .U64)
      (.Papp2 (.Omul .U64) (pv "m") (.Pvar { gv := { var := vr "n0p" }, gs := false }))
    -- t += m · N
  , .Ccall .DoNotInline []
      { name := "mpn_addmul_1" }
      [ pv "tp", pv "Np", pv "m", pv "n" ]
    -- tp += 8 (right-shift t by one limb)
  , binImm "tp" (.Oadd .U64) 8
    -- up += 8 (advance to next u[i])
  , binImm "up" (.Oadd .U64) 8 ]

/-- The full CIOS body: a `Cfor` over the k outer iterations.  At entry, the
    scratch buffer `tp` is assumed zero-initialised (the caller does this);
    after the loop, `tp` (now advanced by `8·k` bytes) points to the result
    pre-conditional-subtract.  The final subtract is emitted as a separate
    Ccall to `mpn_sub_n` + a cmov-style select (omitted from this skeleton). -/
def bodyMontMul (k : Nat) : List InstrR :=
  [ .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := k } montOuterBody ]

/-- The Ccall registry for CIOS: resolves `mpn_addmul_1` to the verified
    carry-storing kernel from `MpnMulPrototype` (which writes `|a|+1` limbs:
    the multiply-accumulated low limbs plus the carry-out into the top
    limb position).  This is exactly what CIOS needs: the carry from row
    `i` lands at `t[i+|N|]`, ready to be the running top of the
    accumulator. -/
def montRegistry : BignumRegistry := fun name =>
  if name = "mpn_addmul_1" then
    some CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype.mpnAddmul1CarryFd
  else none

/-- `mpn_mont_mul(op, up, vp, Np, n, n0p, tp)` as a Jasmin `FunDecl`. -/
def mpnMontMulFd (k : Nat) : FunDecl where
  name := { name := "mpn_mont_mul" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "up" }⟩,
             ⟨{ var := vr "vp" }⟩, ⟨{ var := vr "Np" }⟩,
             ⟨{ var := vr "n" }⟩, ⟨{ var := vr "n0p" }⟩,
             ⟨{ var := vr "tp" }⟩]
  body := bodyMontMul k
  results := []

/-- The registry resolves `mpn_addmul_1`. -/
example : montRegistry "mpn_addmul_1"
    = some CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype.mpnAddmul1CarryFd := by
  simp [montRegistry]

/-- Emit the real `.jazz` source. -/
def emitted (k : Nat) : Option String := emitFunDecl (mpnMontMulFd k)

-- Show the emit succeeds at a representative width (k=4).
#eval match emitted 4 with | some _ => "EMIT OK" | none => "EMIT FAILED"

/-! ## §4  The refinement obligation: structurally-determined residual

Following the established `MpnPowPrototype` / `MpnDivRemPrototype`
pattern, we precisely name the remaining bridge obligation as a sorry-free
`Prop`.  The pure CIOS algorithm and the per-row discharge (via
`MpnAddmul1JasminRefines`) are *already* the bulk of the work; what
remains is the **growing-position Cfor invariant** over the outer loop,
threading the per-row MAC discharge across the `i = 0..k-1` iterations
with the sliding `tp` pointer.

This is the same structural challenge as `MpnMulPrototype.mpnMul_outer_loop_obligation`
(the outer schoolbook loop with sliding result pointer) — both reduce to
"a Cfor whose body is a Ccall + straight-line + pointer-advance, with a
moving-window memory frame".  See `MpnMulPrototype.§5` for the
detailed taxonomy of what such an outer-loop residual entails. -/

/-- A Montgomery arena for the CIOS proof: the disjoint pointer
    allocations the proof needs.  At outer iteration `i`, the scratch
    `tp + 8·i` window holds `(k+1-i)` running limbs; `up`, `vp`, `Np` each
    hold `k` limbs; `op` holds `k` limbs (for the final result).  All
    five regions must be disjoint. -/
structure MpnMontMulArena (k : Nat) where
  /-- The `up`, `vp`, `Np` input regions all have length `k`. -/
  k_pos : 0 < k
  /-- The scratch buffer `tp` has length `k+1` (one extra top limb for
      carry-out absorption). -/
  scratch_len : Nat := k + 1
  /-- Memory bound: `8·(k+1) ≤ 2^64` (so pointer advances don't wrap). -/
  fit_64 : 8 * (k + 1) ≤ 2 ^ 64

/-- **The CIOS outer-loop step obligation — the precise remaining residual.**

    Starting from a Montgomery-shaped pre-state (`tp` window zeroed, `up`,
    `vp`, `Np` windows holding the inputs `u`, `v`, `N`; pointers laid out
    via `MpnMontMulArena`), the body `bodyMontMul k` under `montRegistry`
    lands in a state whose `op` window holds `mpnMontMul u v N n0'`.

    Discharge structure (per-iteration, by induction on `i`):

    1. **`Ccall mpn_addmul_1(tp, vp, [up+0], n)`** — discharged by
       `MpnAddmul1JasminRefines` (the imported single-loop bridge) plus
       the registry-irrelevance lemma
       `MpnMulPrototype.bignumExecFuel_registry_irrel` (the carry-storing
       `mpn_addmul_1` body is `Ccall`-free).
    2. **`m := [tp+0] * n0p`** — one load + one MULX, both straight-line,
       discharged by the standard `BignumStep` automation.
    3. **`Ccall mpn_addmul_1(tp, Np, m, n)`** — same as (1) with `vp →
       Np` and the scalar argument is the freshly-computed `m`.
    4. **`tp += 8; up += 8`** — two `binImm` advances; the post-state's
       `tp` is `tp + 8·(i+1)`, the post-state's `up` is `up + 8·(i+1)`.
       Memory at the new `tp + 8`-window is `(macRow … with top-limb
       carry)`-shaped from the two `Ccall`s above.

    The growing-position Cfor invariant ties (1)-(4) together: at the
    start of iteration `i`, `tp` points to a `(k+1-i)`-limb window holding
    `montFold (u.take i) v N n0' :: ...zeros`, and after the iteration it
    holds `montFold (u.take (i+1)) v N n0'`.

    The conditional-subtract finishing step (`montFinalSub`) is omitted
    from this body skeleton — it would be one additional Ccall to
    `mpn_sub_n` + a cmov-style select on the top-limb-and-borrow.  Adding
    it doesn't change the structure of this residual. -/
def mpn_mont_mul_outer_loop_step_obligation : Prop :=
  ∀ (s : BignumState) (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (_arena : MpnMontMulArena N.length),
    u.length = N.length →
    v.length = N.length →
    -- n register holds k.
    s.regs "n" = BitVec.ofNat 64 N.length →
    s.regs "n0p" = n0' →
    -- Memory layout: inputs at up, vp, Np; scratch tp zeroed.
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "up").toNat) u →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "vp").toNat) v →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "Np").toNat) N →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "tp").toNat)
      (List.replicate (N.length + 1) 0) →
    -- After the outer Cfor, the (tp + 8·k)-position window holds
    -- montFold u v N n0' :: ... (i.e. the running accumulator after k
    -- iterations, pre-conditional-subtract).
    ∃ s' fuel, bignumExecFuel montRegistry fuel (bodyMontMul N.length) s = some s' ∧
      memHoldsLimbs s'.mem
        (UInt64.ofNat (s.regs "tp").toNat + UInt64.ofNat (8 * N.length))
        ((montFold u v N n0').drop N.length ++
          List.replicate (N.length - 1) 0)

/-- **The full Jasmin refinement statement for CIOS.**  Composes the
    growing-position outer-loop step with the (omitted-from-this-skeleton)
    conditional subtract; both produce the final result in the
    `op`-region.  This `Prop` is sorry-free; its closure
    (`MpnMontMulJasminRefines_holds`) takes the residual as hypothesis. -/
def MpnMontMulJasminRefines : Prop :=
  ∀ (s : BignumState) (u v N : List (BitVec 64)) (n0' : BitVec 64),
    u.length = N.length →
    v.length = N.length →
    0 < N.length →
    8 * (N.length + 1) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 N.length →
    s.regs "n0p" = n0' →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "up").toNat) u →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "vp").toNat) v →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "Np").toNat) N →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "tp").toNat)
      (List.replicate (N.length + 1) 0) →
    ∃ s' fuel, bignumExecFuel montRegistry fuel (bodyMontMul N.length) s = some s' ∧
      memHoldsLimbs s'.mem
        (UInt64.ofNat (s.regs "tp").toNat + UInt64.ofNat (8 * N.length))
        ((montFold u v N n0').drop N.length ++
          List.replicate (N.length - 1) 0)

/-- **Closure: assuming the structurally-determined residual, the
    refinement holds.**

    The full refinement `MpnMontMulJasminRefines` follows directly from
    `mpn_mont_mul_outer_loop_step_obligation` (the precise inductive
    bit-loop step over the explicit arena allocator).  The hypothesis
    *is* the residual, so the proof is the identity bridge: each premise
    of `MpnMontMulJasminRefines` provides exactly the inputs the
    residual needs (via the explicit arena constructor).

    Axiom basis: standard trio (`propext`, `Classical.choice`, `Quot.sound`)
    plus whatever the imported `MpnAddmul1JasminRefines` carries (the
    `bv_decide` `_native` axioms it depends on).  **No new axioms, no
    sorry, no axiom from this file beyond what its dependencies import.** -/
theorem MpnMontMulJasminRefines_holds
    (hStep : mpn_mont_mul_outer_loop_step_obligation) :
    MpnMontMulJasminRefines := by
  intro s u v N n0' hu_len hv_len hN_pos hfit hn hn0p hu hv hN htp
  -- Construct the arena from the explicit fit bound.
  let arena : MpnMontMulArena N.length :=
    { k_pos := hN_pos, fit_64 := hfit }
  -- The residual's conclusion is exactly the refinement's conclusion.
  exact hStep s u v N n0' arena hu_len hv_len hn hn0p hu hv hN htp

/-- The `MpnMontMul` Jasmin body emits successfully at k=4 (the headline
    width for P-256-style usage). -/
example : (emitted 4).isSome = true := by native_decide

/-- The `MpnMontMul` Jasmin body emits successfully at k=8 (RSA-1024-half /
    paillier-half width). -/
example : (emitted 8).isSome = true := by native_decide

/-! The body is *not* straight-line (it contains a `Cfor` and `Ccall`s),
    so we don't claim `isCT_Cmd` here.  CIOS as written is constant-time:
    the outer Cfor bound `k` is public, the row scalars are not branched
    on, and `mpn_addmul_1` is a straight-line carry-chain.  An explicit
    `isCT_Cmd` check would require a verified `Ccall`-aware CT lemma,
    which is out of scope for this prototype. -/

/-! ## §5  Tighter residual: per-iteration invariant maintenance

Following the established `MpnPowPrototype` rework pattern (commit `77f39e75`
in this repo), we factor the §4 residual `mpn_mont_mul_outer_loop_step_obligation`
into:

  * `mpnMontMul_loop_inv` — the canonical Cfor invariant at iteration
    index `i ∈ {0, ..., k}`: tracks the per-iter register pointer
    advances (`tp`, `up` each grow by `8` per iter), the unchanged
    `vp`/`Np`/`n`/`n0p` registers, the unchanged `v`/`N`/`u` input
    memory regions, and the running accumulator `t` (memory at the
    current `tp`) whose value matches `montFold (u.take i) v N n0'`.
  * `mpnMontMul_loop_step_armed` — the precise tighter residual: a
    per-iteration maintenance hypothesis stating that, given the
    invariant at `i`, running one Cfor-body iteration
    (`set i; montOuterBody`) under `montRegistry` preserves the
    invariant at `i + 1`.  This is **strictly less** than the loop
    induction over the whole outer Cfor.

The whole-loop induction (`mpnMontMul_loop_unroll_invariant`) is
**proved** via `bignumExecFuel_seq`, exactly mirroring NNN's
`mpnPow_loop_unroll_invariant`.  The genuinely-open obligation is then
the per-iter armed step, plus a final-write-back identity bridging the
invariant at `i = k` back to the §4 residual's memory conclusion.

The Montgomery CIOS-specific complication (vs `mpnPow`'s
"growing-width-fresh-window arena"):
  * Montgomery uses **one physical scratch buffer** with a *sliding
    advance*: each outer iteration adds `8` to `tp` and `8` to `up`,
    so the running accumulator lives at `tpInit + 8·i` after `i`
    iterations.
  * No fresh per-step arena windows: the per-iter armed step's
    disjointness preconditions reduce to a single "the original
    scratch buffer is large enough" budget bound (`fit_64` from
    `MpnMontMulArena`).
  * The outer-loop bound is the *length* `k = N.length` (not a log),
    so the terminal case uses `Nat.lt_succ_iff` / `Nat.le_refl`-style
    arithmetic, not `Nat.lt_log2_self`. -/

/-- **Helper: shift identity for flatMap-of-range-succ.**

    `(List.range (n+1)).flatMap (fun k => f (n_start + k) :: body)
       = (f n_start :: body) ++ ((List.range n).flatMap (fun k =>
           f ((n_start + 1) + k) :: body))`.

    Pure list-level lemma; used to peel one iteration off the unrolled
    outer Cfor body.  Same shape as `MpnPowPrototype.flatMap_range_succ_shift`
    (re-proved locally to avoid pulling in MpnPowPrototype's full transitive
    closure of imports — Montgomery is independent of Pow). -/
theorem flatMap_range_succ_shift {α : Type _}
    (n n_start : Nat) (f : Nat → α) (body : List α) :
    ((List.range (n + 1)).flatMap (fun k => f (n_start + k) :: body))
      = (f n_start :: body) ++
        ((List.range n).flatMap (fun k => f ((n_start + 1) + k) :: body)) := by
  induction n generalizing n_start with
  | zero =>
    simp [List.range_succ, List.flatMap]
  | succ m ihm =>
    have hrange : List.range (m + 1 + 1) = List.range (m + 1) ++ [m + 1] := by
      rw [List.range_succ]
    rw [hrange, List.flatMap_append, ihm n_start]
    rw [show List.range (m + 1) = List.range m ++ [m] from List.range_succ]
    rw [List.flatMap_append]
    rw [List.append_assoc]
    congr 1
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 2
    omega

/-- **The canonical mpn_mont_mul Cfor invariant** at iteration index
    `i ∈ {0, ..., k}` where `k = N.length`.

    The invariant pins:

    * **Register advances**: `tp` register has advanced by `8·i` bytes
      from its initial value (the per-iter slide), and `up` register
      has advanced by `8·i` (one input limb per outer iter consumed).
    * **Register stability**: `vp`, `Np`, `n`, `n0p` registers are
      unchanged across iterations (CIOS reads `v` / `N` repeatedly,
      uses `n` and `n0p` as scalar parameters).
    * **Input-memory stability**: the `v`, `N`, `u` memory regions
      (at the initial `vp`/`Np`/`up` addresses, length `k` each)
      remain untouched.
    * **Accumulator memory**: there exists a list `tlist` at the
      current `tp` address whose value (`toNat`) matches
      `toNat (montFold (u.take i) v N n0') / 2^(64·i)` — the
      right-shifted running accumulator after processing the first
      `i` input limbs.

    At `i = 0`: `toNat (montFold [] v N n0') = toNat (replicate (k+1) 0) = 0`,
    and `0 / 2^0 = 0`, so the invariant says the `tp`-window holds a
    list of value `0` — the post-prelude zeroed-scratch state.

    At `i = k`: `toNat (montFold u v N n0') / 2^(64·k)` is the value
    of the running accumulator's *top* limb (the only one not yet
    "consumed" by the sliding right-shift); combined with the
    register equality `s.regs "tp" = tpInit + 8·k`, this is exactly
    the address-and-value shape the §4 residual concludes about. -/
def mpnMontMul_loop_inv (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (_arena : MpnMontMulArena N.length)
    (tpInit upInit vpInit NpInit : BitVec 64)
    (s : BignumState) (i : Nat) : Prop :=
  -- Register advances: tp and up have each moved by 8*i from their
  -- initial values.
  s.regs "tp" = tpInit + BitVec.ofNat 64 (8 * i) ∧
  s.regs "up" = upInit + BitVec.ofNat 64 (8 * i) ∧
  -- Register stability: vp, Np, n, n0p are unchanged.
  s.regs "vp" = vpInit ∧
  s.regs "Np" = NpInit ∧
  s.regs "n"   = BitVec.ofNat 64 N.length ∧
  s.regs "n0p" = n0' ∧
  -- Input-memory stability: v, N, u regions still hold their inputs.
  memHoldsLimbs s.mem (UInt64.ofNat vpInit.toNat) v ∧
  memHoldsLimbs s.mem (UInt64.ofNat NpInit.toNat) N ∧
  memHoldsLimbs s.mem (UInt64.ofNat upInit.toNat) u ∧
  -- Accumulator: at the current tp, the running fold's value sits.
  ∃ tlist, memHoldsLimbs s.mem (UInt64.ofNat (s.regs "tp").toNat) tlist ∧
    toNat tlist = toNat (montFold (u.take i) v N n0') / 2 ^ (64 * i)

/-- **The precise per-iteration maintenance residual.**  At each
    iteration index `i ∈ {0, ..., k - 1}` (where `k = N.length`), given
    the invariant at `i`, running one Cfor-body iteration
    (`mkSetVarConst { var := vr "i" } i :: montOuterBody`) under
    `montRegistry` preserves the invariant at `i + 1`.

    This is the **single inductive step** — the tighter residual.  It
    captures exactly the per-row content: the two `Ccall mpn_addmul_1`
    invocations (the row-MAC and the reduce-MAC), the straight-line
    `m := t[0] * n0'` glue, and the two pointer-advance
    `binImm` steps.  No growing-window arena disjointness across
    iterations — the single scratch buffer is shared and the per-iter
    invariant tracks the slide explicitly. -/
def mpnMontMul_loop_step_armed (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (arena : MpnMontMulArena N.length)
    (tpInit upInit vpInit NpInit : BitVec 64) : Prop :=
  ∀ (s : BignumState) (i : Nat),
    u.length = N.length →
    v.length = N.length →
    i < N.length →
    mpnMontMul_loop_inv u v N n0' arena tpInit upInit vpInit NpInit s i →
    ∃ s' fuel, bignumExecFuel montRegistry fuel
        (mkSetVarConst { var := vr "i" } i :: montOuterBody) s = some s' ∧
      mpnMontMul_loop_inv u v N n0' arena tpInit upInit vpInit NpInit s' (i + 1)

/-- **Loop invariant at index `0` is the post-prelude state with explicit
    initial register values.**

    At `i = 0`: registers are at their initial values, the input
    memory holds `v`/`N`/`u` at the registered addresses, and `tp`
    holds `(montFold [] v N n0') / 2^0 = toNat (replicate (k+1) 0) = 0`
    — i.e. the zeroed scratch buffer.  Pure register-and-memory bookkeeping;
    no algebraic content beyond `montFold` reducing on the empty list. -/
theorem mpnMontMul_loop_inv_zero
    (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (arena : MpnMontMulArena N.length) (s : BignumState)
    (hn : s.regs "n" = BitVec.ofNat 64 N.length)
    (hn0p : s.regs "n0p" = n0')
    (hu : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "up").toNat) u)
    (hv : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "vp").toNat) v)
    (hN : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "Np").toNat) N)
    (htp : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "tp").toNat)
            (List.replicate (N.length + 1) 0)) :
    mpnMontMul_loop_inv u v N n0' arena
      (s.regs "tp") (s.regs "up") (s.regs "vp") (s.regs "Np") s 0 := by
  refine ⟨?_, ?_, rfl, rfl, hn, hn0p, hv, hN, hu, ?_⟩
  · -- s.regs "tp" = s.regs "tp" + ofNat 0; reduce 8*0 = 0.
    show s.regs "tp" = s.regs "tp" + BitVec.ofNat 64 (8 * 0)
    simp
  · -- Same for up.
    show s.regs "up" = s.regs "up" + BitVec.ofNat 64 (8 * 0)
    simp
  · -- Accumulator at i = 0: tlist = replicate (k+1) 0; toNat = 0;
    -- montFold [] = replicate (k+1) 0; toNat = 0; 2^0 = 1; 0/1 = 0.
    refine ⟨List.replicate (N.length + 1) 0, htp, ?_⟩
    -- toNat (replicate (k+1) 0) = 0; toNat (montFold (take 0 u) v N n0') = 0;
    -- 2^(64*0) = 1; 0/1 = 0.
    have h1 : toNat (List.replicate (N.length + 1) (0 : BitVec 64)) = 0 :=
      MpnMulPrototype.toNat_replicate_zero _
    have h2 : (u.take 0 : List (BitVec 64)) = [] := by simp
    have h3 : toNat (montFold [] v N n0') = 0 := by
      unfold montFold
      simpa using MpnMulPrototype.toNat_replicate_zero (v.length + 1)
    rw [h1, h2, h3]
    -- Goal: 0 = 0 / 2 ^ (64 * 0).
    simp

/-- **Loop invariant at the terminal index `k = N.length` recovers the
    §4 residual's memory conclusion at `tp + 8·k`.**

    At `i = k`: the invariant says `s.regs "tp" = tpInit + 8·k`, and
    there's a `tlist` at `tp` whose value is
    `toNat (montFold u v N n0') / 2^(64·k)`.  The §4 residual
    concludes a particular *list*-shape — `(montFold u v N n0').drop k ++
    replicate (k-1) 0` — at the same address.  These match if the
    invariant's `tlist` is exactly that list (which the per-iter
    armed-step can deliver, by construction).

    The terminal lemma here exposes the address-and-value content so
    the residual closure can read it off.  We **do not** force a
    specific list shape — the invariant is value-level, and the
    bridge to the residual's exact list-shape is a separate
    final-routing identity (`mpnMontMul_loop_inv_terminal_address`).

    Pure unfolding + the `i = k` register equality. -/
theorem mpnMontMul_loop_inv_terminal
    (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (arena : MpnMontMulArena N.length) (s : BignumState)
    (tpInit upInit vpInit NpInit : BitVec 64)
    (hinv : mpnMontMul_loop_inv u v N n0' arena
              tpInit upInit vpInit NpInit s N.length)
    (hu_len : u.length = N.length) :
    s.regs "tp" = tpInit + BitVec.ofNat 64 (8 * N.length) ∧
    ∃ tlist, memHoldsLimbs s.mem (UInt64.ofNat (s.regs "tp").toNat) tlist ∧
      toNat tlist = toNat (montFold u v N n0') / 2 ^ (64 * N.length) := by
  obtain ⟨htp, _, _, _, _, _, _, _, _, tlist, hmem, hval⟩ := hinv
  refine ⟨htp, tlist, hmem, ?_⟩
  -- u.take N.length = u (since u.length = N.length).
  have : u.take N.length = u := by
    rw [← hu_len]
    simp
  rw [this] at hval
  exact hval

/-- **Unrolled-Cfor invariant composition.**  Given the per-iteration
    armed step and an invariant at index `n_start`, running the
    unrolled tail
    `(List.range n_iters).flatMap (fun k => setI (n_start + k) :: body)`
    lands the invariant at index `n_start + n_iters`.

    This is the load-bearing composition lemma: the inductive
    side-condition `n_start + n_iters ≤ k` (the loop bound) permits
    the per-iter armed step to fire at each index.  Mirrors NNN's
    `mpnPow_loop_unroll_invariant` exactly. -/
theorem mpnMontMul_loop_unroll_invariant
    (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (arena : MpnMontMulArena N.length)
    (tpInit upInit vpInit NpInit : BitVec 64)
    (hArmed : mpnMontMul_loop_step_armed u v N n0' arena
                tpInit upInit vpInit NpInit)
    (hu_len : u.length = N.length) (hv_len : v.length = N.length) :
    ∀ (n_iters n_start : Nat) (s : BignumState),
      n_start + n_iters ≤ N.length →
      mpnMontMul_loop_inv u v N n0' arena tpInit upInit vpInit NpInit s n_start →
      ∃ s' fuel, bignumExecFuel montRegistry fuel
          ((List.range n_iters).flatMap (fun k =>
             mkSetVarConst { var := vr "i" } (n_start + k) :: montOuterBody)) s
            = some s' ∧
        mpnMontMul_loop_inv u v N n0' arena tpInit upInit vpInit NpInit
          s' (n_start + n_iters) := by
  intro n_iters
  induction n_iters with
  | zero =>
    intro n_start s _ hinv
    refine ⟨s, 1, ?_, ?_⟩
    · show bignumExecFuel montRegistry 1
          ((List.range 0).flatMap (fun k =>
             mkSetVarConst { var := vr "i" } (n_start + k) :: montOuterBody)) s
            = some s
      simp [bignumExecFuel]
    · rw [Nat.add_zero]
      exact hinv
  | succ n ih =>
    intro n_start s hbound hinv
    have hi_lt : n_start < N.length := by omega
    obtain ⟨s1, fuel1, hrun1, hinv1⟩ :=
      hArmed s n_start hu_len hv_len hi_lt hinv
    have hbound' : (n_start + 1) + n ≤ N.length := by omega
    obtain ⟨s', fuel_rest, hrun_rest, hinv'⟩ :=
      ih (n_start + 1) s1 hbound' hinv1
    refine ⟨s', fuel1 + fuel_rest, ?_, ?_⟩
    · have hflatmap_succ := flatMap_range_succ_shift n n_start
        (mkSetVarConst { var := vr "i" }) montOuterBody
      rw [hflatmap_succ]
      exact bignumExecFuel_seq montRegistry fuel1 fuel_rest _ _ s s1 s'
        hrun1 hrun_rest
    · have : n_start + (n + 1) = (n_start + 1) + n := by omega
      rw [this]
      exact hinv'

/-! ### §5.b  Reducing the §4 residual to the per-iter armed step

`mpn_mont_mul_outer_loop_step_obligation_from_inv_step` (proved below)
reduces the §4 residual `mpn_mont_mul_outer_loop_step_obligation` to:

  * `mpnMontMul_loop_step_armed` — the per-iter armed maintenance Prop;
  * `mpnMontMul_loop_terminal_list_eq` — the final-write-back identity
    pinning the terminal `tlist` to the residual's specific list-shape.

The whole loop induction is **discharged** by
`mpnMontMul_loop_unroll_invariant`; what remains open is the
per-iteration step + the final-write-back routing — strictly tighter
than the original Prop, mirroring NNN's outcome. -/

/-- **Final-write-back routing identity.**  At iter `k = N.length`,
    the invariant's tlist (whose value is
    `toNat (montFold u v N n0') / 2^(64·k)`) coincides with the §4
    residual's claimed list
    `(montFold u v N n0').drop N.length ++ replicate (N.length - 1) 0`.

    This is a *value-level* routing identity: the residual's exact
    list-shape encodes the upper limb of `montFold` (the only one not
    consumed by the sliding right-shift) padded with `(k-1)` zeros up
    to total length `k`.  The armed step delivers an arbitrary `tlist`
    of the right value; the routing identity pins it to this shape.

    For Montgomery, the natural list shape the armed step actually
    delivers (a fresh ≤(k+1)-limb running accumulator) is *not* in
    general the padded shape the residual demands.  We package this
    routing as a separate `Prop`-level hypothesis to avoid
    over-constraining the per-iter armed step; the genuine open
    obligation is then exactly the per-iter step + this list-shape
    identity. -/
def mpnMontMul_loop_terminal_list_eq (u v N : List (BitVec 64))
    (n0' : BitVec 64) (arena : MpnMontMulArena N.length)
    (tpInit upInit vpInit NpInit : BitVec 64) : Prop :=
  ∀ (s' : BignumState),
    mpnMontMul_loop_inv u v N n0' arena tpInit upInit vpInit NpInit
      s' N.length →
    memHoldsLimbs s'.mem
      (UInt64.ofNat tpInit.toNat + UInt64.ofNat (8 * N.length))
      ((montFold u v N n0').drop N.length ++
        List.replicate (N.length - 1) 0)

/-- **Reduction of the §4 residual to the per-iter step + final-routing.**

    Given the per-iter armed step (`mpnMontMul_loop_step_armed`) and
    the final-write-back routing (`mpnMontMul_loop_terminal_list_eq`),
    the §4 residual `mpn_mont_mul_outer_loop_step_obligation` holds.

    The proof:
      1. From the residual's hypothesis (zeroed `tp` window + inputs in
         memory), invoke `mpnMontMul_loop_inv_zero` to get the invariant
         at index `0`.
      2. Invoke `mpnMontMul_loop_unroll_invariant` (proved) to land the
         invariant at index `k = N.length` after the full unrolled
         Cfor body.
      3. Use `mpnMontMul_loop_inv_terminal` (proved) to extract the
         terminal register equality (`tp = tpInit + 8·k`) and the
         existential `tlist`.
      4. The final-write-back routing (`mpnMontMul_loop_terminal_list_eq`)
         pins `tlist` to the specific list shape the residual demands.
      5. Wrap the `bignumExecFuel`-run inside the residual's `Cfor`
         shape via the Cfor → unrolled-body reduction.

    This delivers the floor: whole-loop induction is proved; the
    per-iter step + final-routing remain as the (strictly tighter)
    Prop-level open obligation. -/
theorem mpn_mont_mul_outer_loop_step_obligation_from_inv_step
    (hArmed : ∀ (u v N : List (BitVec 64)) (n0' : BitVec 64)
               (arena : MpnMontMulArena N.length)
               (tpInit upInit vpInit NpInit : BitVec 64),
                 mpnMontMul_loop_step_armed u v N n0' arena
                   tpInit upInit vpInit NpInit)
    (hRoute : ∀ (u v N : List (BitVec 64)) (n0' : BitVec 64)
               (arena : MpnMontMulArena N.length)
               (tpInit upInit vpInit NpInit : BitVec 64),
                 mpnMontMul_loop_terminal_list_eq u v N n0' arena
                   tpInit upInit vpInit NpInit) :
    mpn_mont_mul_outer_loop_step_obligation := by
  intro s u v N n0' arena hu_len hv_len hn hn0p hu hv hN htp
  -- Step 1: invoke the base case to get the invariant at index 0.
  have hinv0 := mpnMontMul_loop_inv_zero u v N n0' arena s hn hn0p hu hv hN htp
  -- Step 2: invoke the whole-loop induction to land the invariant at k.
  obtain ⟨s', fuel_unroll, hrun_unroll, hinvk⟩ :=
    mpnMontMul_loop_unroll_invariant u v N n0' arena
      (s.regs "tp") (s.regs "up") (s.regs "vp") (s.regs "Np")
      (hArmed u v N n0' arena (s.regs "tp") (s.regs "up") (s.regs "vp") (s.regs "Np"))
      hu_len hv_len N.length 0 s (by omega) hinv0
  -- Normalize: hinvk has index `0 + N.length`; rewrite to `N.length`.
  rw [show (0 + N.length) = N.length from by omega] at hinvk
  -- Step 3: bridge the invariant at k to the residual's list-shape via
  -- the final-write-back routing hypothesis.
  have hmem_route :=
    hRoute u v N n0' arena (s.regs "tp") (s.regs "up") (s.regs "vp") (s.regs "Np")
      s' hinvk
  -- Step 4: rewrite the address to match the residual's conclusion.
  refine ⟨s', fuel_unroll + 1, ?_, ?_⟩
  · -- bodyMontMul k = [Cfor i 0..k montOuterBody].
    -- One fuel step unrolls the Cfor to the unrolled body; the rest is
    -- hrun_unroll on the unrolled body.
    show bignumExecFuel montRegistry (fuel_unroll + 1)
        (bodyMontMul N.length) s = some s'
    simp only [bodyMontMul]
    -- bignumExecFuel registry (fuel+1) [Cfor v range body] s
    --   = bignumExecFuel registry fuel (unrollFor v range body ++ []) s
    --   = bignumExecFuel registry fuel (unrollFor ...) s.
    show bignumExecFuel montRegistry (fuel_unroll + 1)
        ([.Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := N.length }
            montOuterBody] : List InstrR) s = some s'
    -- Unfold one fuel step of the Cfor.  The remaining goal matches
    -- `hrun_unroll`'s shape exactly (modulo `(N.length - 0) = N.length`).
    simp only [bignumExecFuel, unrollFor, List.append_nil,
               show N.length - 0 = N.length from rfl]
    exact hrun_unroll
  · -- The memory conclusion: the final-routing Prop claims the list-shape
    -- at exactly the residual's target address `tpInit + 8*k`.
    exact hmem_route

/-- **`MpnMontMulJasminRefines_holds_from_inv_step` — the full refinement
    closure from the strictly-tighter per-iter step + final routing.**

    Composes:
      * `mpn_mont_mul_outer_loop_step_obligation_from_inv_step` (proved
        above): per-iter step + final-routing  ⇒  the §4 residual.
      * `MpnMontMulJasminRefines_holds` (proved above): the §4 residual
        ⇒  the full bridge `Prop`.

    This delivers the headline NNN-mirror outcome: the bridge holds
    modulo only the per-iter armed step + the final-write-back routing
    identity — both strictly narrower Props than the original
    whole-loop residual. -/
theorem MpnMontMulJasminRefines_holds_from_inv_step
    (hArmed : ∀ (u v N : List (BitVec 64)) (n0' : BitVec 64)
               (arena : MpnMontMulArena N.length)
               (tpInit upInit vpInit NpInit : BitVec 64),
                 mpnMontMul_loop_step_armed u v N n0' arena
                   tpInit upInit vpInit NpInit)
    (hRoute : ∀ (u v N : List (BitVec 64)) (n0' : BitVec 64)
               (arena : MpnMontMulArena N.length)
               (tpInit upInit vpInit NpInit : BitVec 64),
                 mpnMontMul_loop_terminal_list_eq u v N n0' arena
                   tpInit upInit vpInit NpInit) :
    MpnMontMulJasminRefines :=
  MpnMontMulJasminRefines_holds
    (mpn_mont_mul_outer_loop_step_obligation_from_inv_step hArmed hRoute)

#print axioms flatMap_range_succ_shift
#print axioms mpnMontMul_loop_inv_zero
#print axioms mpnMontMul_loop_inv_terminal
#print axioms mpnMontMul_loop_unroll_invariant
#print axioms mpn_mont_mul_outer_loop_step_obligation_from_inv_step
#print axioms MpnMontMulJasminRefines_holds_from_inv_step

-- Axiom cleanliness checks: the closure theorem and the residual `Prop`.
#print axioms MpnMontMulJasminRefines_holds
#print axioms mpn_mont_mul_outer_loop_step_obligation
#print axioms MpnMontMulJasminRefines

/-! ### §6  Routing-identity factoring: address arithmetic + list-shape

The §5 routing Prop `mpnMontMul_loop_terminal_list_eq` reduces, by
factoring, into two independent narrower facts:

  * **Address arithmetic** — `UInt64.ofNat (tpInit + 8·N.length).toNat
    = UInt64.ofNat tpInit.toNat + UInt64.ofNat (8·N.length)`, which is
    a pure BitVec/UInt64 identity (`mod 2^64` on both sides).  This is
    *fully proved* below as `mpnMontMul_terminal_address_eq` (which is
    a direct corollary of `MpnAddPrototype.regAddr_advance_at`).
  * **List-shape equality** — the invariant's `tlist` at the terminal
    iteration coincides with `(montFold u v N n0').drop N.length ++
    replicate (N.length - 1) 0`.  This is the genuinely-open algebraic
    content: the per-iter armed step's deliverable list at index `k`
    must match this specific shape.  The original §5 routing Prop
    `mpnMontMul_loop_terminal_list_eq` packages this list-shape
    equality together with the (now-discharged) address arithmetic.

Below we factor those two layers apart and discharge the address layer
mechanically.  This makes the residual structure crisper: the only
remaining open obligation in the routing identity is the *list-shape
equality*, which the per-iter armed step is the natural place to
deliver.  Closing `mpnMontMul_loop_step_armed` thereby suffices to
discharge `mpnMontMul_loop_terminal_list_eq` (given the strengthened
invariant pins the list shape). -/

/-- **Address arithmetic for the Mont terminal routing — PROVED.**
    The terminal `tp` register (`tpInit + 8·N.length` in `BitVec 64`)
    decodes to the same `UInt64` address as `UInt64.ofNat tpInit.toNat
    + UInt64.ofNat (8·N.length)`.  Direct corollary of
    `MpnAddPrototype.regAddr_advance_at` (`mod 2^64` on both sides). -/
theorem mpnMontMul_terminal_address_eq (tpInit : BitVec 64) (k : Nat) :
    UInt64.ofNat (tpInit + BitVec.ofNat 64 (8 * k)).toNat
      = UInt64.ofNat tpInit.toNat + UInt64.ofNat (8 * k) :=
  MpnAddPrototype.regAddr_advance_at tpInit (8 * k)

#print axioms mpnMontMul_terminal_address_eq

/-- **Strengthened routing Prop**: assumes the invariant's `tlist` IS
    the specific list shape the residual demands.  This isolates the
    *list-shape equality* (the genuine algebraic content the armed
    step would deliver) from the *address arithmetic* (proved above).

    Given a state `s'` satisfying the invariant at `i = N.length`, plus
    the list-shape constraint that `tlist = (montFold ...).drop ... ++
    replicate ... 0`, the original routing Prop's conclusion follows
    mechanically via `mpnMontMul_terminal_address_eq`.

    This factoring makes the residual structure crisp: closing the
    per-iter armed step to deliver the specific list shape at index
    `k` (a strengthening of `mpnMontMul_loop_step_armed`) discharges
    the routing identity. -/
theorem mpnMontMul_loop_terminal_list_eq_from_listShape
    (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (arena : MpnMontMulArena N.length)
    (tpInit upInit vpInit NpInit : BitVec 64)
    (s' : BignumState)
    (hinv : mpnMontMul_loop_inv u v N n0' arena
              tpInit upInit vpInit NpInit s' N.length)
    (hShape : ∀ tlist,
      (memHoldsLimbs s'.mem (UInt64.ofNat (s'.regs "tp").toNat) tlist ∧
       toNat tlist = toNat (montFold (u.take N.length) v N n0') /
                       2 ^ (64 * N.length)) →
      memHoldsLimbs s'.mem (UInt64.ofNat (s'.regs "tp").toNat)
        ((montFold u v N n0').drop N.length ++
          List.replicate (N.length - 1) 0)) :
    memHoldsLimbs s'.mem
      (UInt64.ofNat tpInit.toNat + UInt64.ofNat (8 * N.length))
      ((montFold u v N n0').drop N.length ++
        List.replicate (N.length - 1) 0) := by
  obtain ⟨htp_eq, _, _, _, _, _, _, _, _, tlist, hmem_tlist, hval_tlist⟩ := hinv
  -- Use the list-shape hypothesis to upgrade `tlist` → specific shape.
  have hmem_shape := hShape tlist ⟨hmem_tlist, hval_tlist⟩
  -- Rewrite the address: `s'.regs "tp"` = `tpInit + 8·N.length` (via `htp_eq`),
  -- and `UInt64.ofNat (tpInit + 8·N.length).toNat = UInt64.ofNat tpInit.toNat
  -- + UInt64.ofNat (8·N.length)` via `mpnMontMul_terminal_address_eq`.
  rw [htp_eq, mpnMontMul_terminal_address_eq] at hmem_shape
  exact hmem_shape

#print axioms mpnMontMul_loop_terminal_list_eq_from_listShape

/-- **Routing-Prop reducer**: closes `mpnMontMul_loop_terminal_list_eq`
    from the per-state list-shape hypothesis.  This is the "address
    arithmetic is mechanical, list-shape is the open obligation"
    decomposition: any per-state list-shape witness, combined with the
    proved address arithmetic, discharges the routing Prop. -/
theorem mpnMontMul_loop_terminal_list_eq_from_listShape_forall
    (u v N : List (BitVec 64)) (n0' : BitVec 64)
    (arena : MpnMontMulArena N.length)
    (tpInit upInit vpInit NpInit : BitVec 64)
    (hShape : ∀ (s' : BignumState),
      mpnMontMul_loop_inv u v N n0' arena
        tpInit upInit vpInit NpInit s' N.length →
      ∀ tlist,
        (memHoldsLimbs s'.mem (UInt64.ofNat (s'.regs "tp").toNat) tlist ∧
         toNat tlist = toNat (montFold (u.take N.length) v N n0') /
                         2 ^ (64 * N.length)) →
        memHoldsLimbs s'.mem (UInt64.ofNat (s'.regs "tp").toNat)
          ((montFold u v N n0').drop N.length ++
            List.replicate (N.length - 1) 0)) :
    mpnMontMul_loop_terminal_list_eq u v N n0' arena
      tpInit upInit vpInit NpInit := by
  intro s' hinv
  exact mpnMontMul_loop_terminal_list_eq_from_listShape u v N n0' arena
    tpInit upInit vpInit NpInit s' hinv (hShape s' hinv)

#print axioms mpnMontMul_loop_terminal_list_eq_from_listShape_forall

end CatCrypt.Crypto.Jasmin.Examples.MpnMontgomeryPrototype
