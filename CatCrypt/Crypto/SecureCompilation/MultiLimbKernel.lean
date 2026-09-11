/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutral
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-!
# Multi-limb bignum: 128-bit addition with a verified carry chain

The scale-up from single-limb field ops to multi-limb bignums. A two-limb
(128-bit) addition: add the low limbs, derive the branchless carry-out
(`addCarry_toNat`), and feed it into the high-limb add. The carry is the
limb-to-limb propagation every wider bignum add chains; this is the 2-limb base
case, compiled to both backends.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-- 128-bit addition `(ahi:alo) + (bhi:blo)`: low add, branchless carry, high add. -/
def add2Prog : RegProg :=
  [ .add "slo" "alo" "blo",
    .loadImm "ones" 0xFFFFFFFFFFFFFFFF,
    .eor "sxa" "slo" "alo",
    .eor "nsxa" "sxa" "ones",
    .sub "smla" "slo" "alo",
    .and "t1" "nsxa" "smla",
    .eor "nslo" "slo" "ones",
    .and "t2" "nslo" "alo",
    .orr "bor0" "t2" "t1",
    .shrI "cy" "bor0" 63,
    .add "thi" "ahi" "bhi",
    .add "shi" "thi" "cy" ]

theorem add2Prog_slo (env : Env) :
    (RegProg.denotePure add2Prog env) "slo" = env "alo" + env "blo" := by
  simp only [add2Prog, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure,
    Env.set, Env.get, String.reduceEq, reduceIte]

theorem add2Prog_shi (env : Env) :
    (RegProg.denotePure add2Prog env) "shi"
      = (env "ahi" + env "bhi") + bSltu (env "alo" + env "blo") (env "alo") := by
  simp only [add2Prog, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure,
    Env.set, Env.get, bSltu, String.reduceEq, reduceIte]
  bv_decide

/-- **Value-correctness.** The `(shi:slo)` output is the 128-bit truncated sum of
    the inputs `(ahi:alo)` and `(bhi:blo)`. -/
theorem add2Prog_value (env : Env) :
    ((RegProg.denotePure add2Prog env) "shi").toNat * 2 ^ 64
        + ((RegProg.denotePure add2Prog env) "slo").toNat
      = (((env "ahi").toNat * 2 ^ 64 + (env "alo").toNat)
          + ((env "bhi").toNat * 2 ^ 64 + (env "blo").toNat)) % 2 ^ 128 := by
  rw [add2Prog_shi, add2Prog_slo]
  have hc := addCarry_toNat (env "alo") (env "blo")
  have hslo : (env "alo" + env "blo").toNat = ((env "alo").toNat + (env "blo").toNat) % 2 ^ 64 :=
    BitVec.toNat_add _ _
  have hshi : ((env "ahi" + env "bhi") + bSltu (env "alo" + env "blo") (env "alo")).toNat
      = (((env "ahi").toNat + (env "bhi").toNat) % 2 ^ 64
          + (bSltu (env "alo" + env "blo") (env "alo")).toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]
  have hcy : (bSltu (env "alo" + env "blo") (env "alo")).toNat ≤ 1 := by
    rw [bSltu_eq]; split <;> simp
  have h1 := (env "ahi").isLt; have h2 := (env "alo").isLt
  have h3 := (env "bhi").isLt; have h4 := (env "blo").isLt
  have h5 := (env "alo" + env "blo").isLt
  rw [hshi]; omega

/-- The 128-bit add compiles to AArch64 (generic keystone). -/
theorem add2Prog_arm (s : BState) :
    runBBlock s (lowerBBlock (regToBOp add2Prog)) = armTarget.denote add2Prog s :=
  regToBOp_denote add2Prog s

/-- …and to RISC-V. -/
theorem add2Prog_riscv (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp add2Prog)) = rvTarget.denote add2Prog s :=
  regToROp_denote add2Prog s

/-! ## N-limb generalization: the carry chain by induction -/

/-- Per-limb add-with-carry: `s = a + b + cin` plus the two-stage carry-out recovers
    the full sum. (`linarith` keeps `2^64` a coefficient where `omega` would loop.) -/
theorem adc_toNat (a b cin : BitVec 64) :
    (a + b + cin).toNat
        + (bSltu (a + b) a + bSltu (a + b + cin) (a + b)).toNat * 2 ^ 64
      = a.toNat + b.toNat + cin.toNat := by
  have e1 := addCarry_toNat a b
  have e2 := addCarry_toNat (a + b) cin
  have hc1 : (bSltu (a + b) a).toNat ≤ 1 := by rw [bSltu_eq]; split <;> simp
  have hc2 : (bSltu (a + b + cin) (a + b)).toNat ≤ 1 := by rw [bSltu_eq]; split <;> simp
  generalize bSltu (a + b) a = C1 at e1 hc1 ⊢
  generalize bSltu (a + b + cin) (a + b) = C2 at e2 hc2 ⊢
  have hsum2 : C1.toNat + C2.toNat < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.add_le_add hc1 hc2) (by norm_num)
  have hcsum : (C1 + C2).toNat = C1.toNat + C2.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum2]
  rw [hcsum]
  linarith [e1, e2]

/-- The carry-out is `0` or `1` when the incoming carry is. -/
theorem adc_carry_le (a b cin : BitVec 64) (hc : cin.toNat ≤ 1) :
    (bSltu (a + b) a + bSltu (a + b + cin) (a + b)).toNat ≤ 1 := by
  have h := adc_toNat a b cin
  have ha := a.isLt; have hb := b.isLt
  have hs := (a + b + cin).isLt
  nlinarith [h, ha, hb, hs, hc, Nat.zero_le (a + b + cin).toNat]

/-- Little-endian limb-list value. -/
def bignumVal : List (BitVec 64) → Nat
  | [] => 0
  | l :: ls => l.toNat + 2 ^ 64 * bignumVal ls

/-- Schoolbook limb-wise add with carry (full sum: the final carry becomes the top limb). -/
def addLimbs : List (BitVec 64) → List (BitVec 64) → BitVec 64 → List (BitVec 64)
  | a :: as, b :: bs, c =>
      (a + b + c) :: addLimbs as bs (bSltu (a + b) a + bSltu (a + b + c) (a + b))
  | _, _, c => [c]

/-- **N-limb add value-correctness.** For equal-length limb lists, the carry chain
    computes the exact integer sum (low limb to high, final carry on top). -/
theorem addLimbs_val : ∀ (as bs : List (BitVec 64)) (c : BitVec 64), c.toNat ≤ 1 →
    as.length = bs.length →
    bignumVal (addLimbs as bs c) = bignumVal as + bignumVal bs + c.toNat
  | [], [], c, _, _ => by simp [addLimbs, bignumVal]
  | a :: as, b :: bs, c, hc, hlen => by
      have hc' : (bSltu (a + b) a + bSltu (a + b + c) (a + b)).toNat ≤ 1 := adc_carry_le a b c hc
      have ih := addLimbs_val as bs _ hc' (by simpa using hlen)
      have hadc := adc_toNat a b c
      simp only [addLimbs, bignumVal]
      rw [ih]
      nlinarith [hadc]
  | [], _ :: _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, hlen => by simp at hlen

/-- **The wide product** — the multi-limb multiply primitive. A single-limb `mul`
    (`a*b mod 2^64`) and `mulhi` (`a*b / 2^64`) together are the exact 128-bit product
    `a·b`, as a 2-limb bignum. This is the per-cell product schoolbook multiplication
    accumulates. -/
theorem mulWide_val (a b : BitVec 64) :
    bignumVal [a * b, BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)] = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_lt_mul_of_lt_of_le ha (le_of_lt hb) (by positivity)
  have hhi : (a.toNat * b.toNat) / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hab
  simp only [bignumVal, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hhi, mul_zero, add_zero]
  exact Nat.mod_add_div _ _

/-- The high limb of the wide product. -/
def mulhi (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)

theorem mulWide_lo_hi (a b : BitVec 64) :
    (a * b).toNat + (mulhi a b).toNat * 2 ^ 64 = a.toNat * b.toNat := by
  have h := mulWide_val a b
  simp only [bignumVal, mulhi] at h ⊢
  linarith [h]

/-- **Schoolbook inner loop** — scalar × bignum with a running carry: multiply each
    limb of `bs` by the scalar `a`, accumulating the high half into the next limb's
    carry. This is the core loop schoolbook (and Karatsuba) multiplication is built
    from. -/
def mulScalar (a : BitVec 64) : List (BitVec 64) → BitVec 64 → List (BitVec 64)
  | [], c => [c]
  | b :: bs, c => (a * b + c) :: mulScalar a bs (mulhi a b + bSltu (a * b + c) (a * b))

/-- **Inner-loop value-correctness.** `mulScalar a bs c` represents `a · bignumVal bs + c`. -/
theorem mulScalar_val (a : BitVec 64) : ∀ (bs : List (BitVec 64)) (c : BitVec 64),
    bignumVal (mulScalar a bs c) = a.toNat * bignumVal bs + c.toNat
  | [], c => by simp [mulScalar, bignumVal]
  | b :: bs, c => by
      have ih := mulScalar_val a bs (mulhi a b + bSltu (a * b + c) (a * b))
      have hac := addCarry_toNat (a * b) c
      have hlohi := mulWide_lo_hi a b
      have ha := a.isLt; have hb := b.isLt
      have hablt : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hbs : (bSltu (a * b + c) (a * b)).toNat ≤ 1 := by rw [bSltu_eq]; split <;> simp
      have hcout : (mulhi a b + bSltu (a * b + c) (a * b)).toNat
          = (mulhi a b).toNat + (bSltu (a * b + c) (a * b)).toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt
          (by nlinarith [hlohi, hablt, hbs, (a * b).isLt, Nat.zero_le (a * b).toNat])]
      simp only [mulScalar, bignumVal] at ih ⊢
      rw [ih, hcout]
      nlinarith [hac, hlohi]

/-! ## Full schoolbook multiplication: the outer loop -/

/-- Uneven-length bignum add with carry (the shift-and-add the outer loop needs). -/
def bnAdd : List (BitVec 64) → List (BitVec 64) → BitVec 64 → List (BitVec 64)
  | [], [], c => [c]
  | [], y :: ys, c => (y + c) :: bnAdd [] ys (bSltu (y + c) y)
  | x :: xs, [], c => (x + c) :: bnAdd xs [] (bSltu (x + c) x)
  | x :: xs, y :: ys, c =>
      (x + y + c) :: bnAdd xs ys (bSltu (x + y) x + bSltu (x + y + c) (x + y))

theorem bnAdd_val : ∀ (xs ys : List (BitVec 64)) (c : BitVec 64),
    bignumVal (bnAdd xs ys c) = bignumVal xs + bignumVal ys + c.toNat
  | [], [], c => by simp [bnAdd, bignumVal]
  | [], y :: ys, c => by
      have ih := bnAdd_val [] ys (bSltu (y + c) y)
      have hac := addCarry_toNat y c
      simp only [bnAdd, bignumVal] at ih ⊢; rw [ih]; nlinarith [hac]
  | x :: xs, [], c => by
      have ih := bnAdd_val xs [] (bSltu (x + c) x)
      have hac := addCarry_toNat x c
      simp only [bnAdd, bignumVal] at ih ⊢; rw [ih]; nlinarith [hac]
  | x :: xs, y :: ys, c => by
      have ih := bnAdd_val xs ys (bSltu (x + y) x + bSltu (x + y + c) (x + y))
      have hadc := adc_toNat x y c
      simp only [bnAdd, bignumVal] at ih ⊢; rw [ih]; nlinarith [hadc]

/-- **Full schoolbook N-limb multiplication**: accumulate the shifted scalar products. -/
def mulBignum : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], _ => []
  | a :: as, bs => bnAdd (mulScalar a bs 0) (0 :: mulBignum as bs) 0

/-- **The kernel computes the exact integer product** of the two bignums. -/
theorem mulBignum_val : ∀ (as bs : List (BitVec 64)),
    bignumVal (mulBignum as bs) = bignumVal as * bignumVal bs
  | [], bs => by simp [mulBignum, bignumVal]
  | a :: as, bs => by
      have ih := mulBignum_val as bs
      have hsc := mulScalar_val a bs 0
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      simp only [mulBignum, bnAdd_val, bignumVal, hsc, ih, h0]
      ring

/-! ## Multi-limb subtraction (two's complement reuse of the add carry chain)

`x − y` over limbs is `x + (~y) + 1`: complement each limb of `y`, then run the
verified `addLimbs` carry chain with an incoming carry of `1`. The result carries an
extra top limb that is `1` exactly when `x ≥ y` (no borrow) and `0` on borrow — the
flag a modular reduction selects on. Built entirely from `addLimbs` and bitwise-not,
both of which the compiler's branchless alphabet already lowers. -/

/-- Bitwise-complement every limb (the `~y` of two's-complement subtract). -/
def notLimbs (ys : List (BitVec 64)) : List (BitVec 64) := ys.map (~~~·)

/-- `Σ ~yᵢ·2⁶⁴ⁱ + Σ yᵢ·2⁶⁴ⁱ + 1 = 2^(64·n)`: the complemented limbs are the
    ones'-complement of the value. -/
theorem notLimbs_val : ∀ ys : List (BitVec 64),
    bignumVal (notLimbs ys) + bignumVal ys + 1 = (2 ^ 64) ^ ys.length
  | [] => by simp [notLimbs, bignumVal]
  | y :: ys => by
      have ih := notLimbs_val ys
      have hy : (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := BitVec.toNat_not
      have hyb := y.isLt
      simp only [notLimbs, List.map_cons, bignumVal, List.length_cons] at ih ⊢
      have hps : ((2 : ℕ) ^ 64) ^ (ys.length + 1) = (2 ^ 64) ^ ys.length * 2 ^ 64 :=
        pow_succ _ _
      rw [hy]
      omega

/-- Multi-limb subtract `x − y` as two's complement: complement `y`, add with carry
    `1`. Produces `x.length + 1` limbs; the top limb is the not-borrow flag. -/
def subLimbs (xs ys : List (BitVec 64)) : List (BitVec 64) :=
  addLimbs xs (notLimbs ys) 1

/-- **Multi-limb subtraction value-correctness.** For equal-length operands,
    `bignumVal (subLimbs xs ys) + bignumVal ys = bignumVal xs + 2^(64·n)`. When
    `bignumVal xs ≥ bignumVal ys` the low `n` limbs hold `xs − ys` and the top limb
    is `1`; on borrow the top limb is `0` — the conditional-subtract reduction flag. -/
theorem subLimbs_val (xs ys : List (BitVec 64)) (hlen : xs.length = ys.length) :
    bignumVal (subLimbs xs ys) + bignumVal ys = bignumVal xs + (2 ^ 64) ^ xs.length := by
  have hnlen : xs.length = (notLimbs ys).length := by simp [notLimbs, hlen]
  have hav := addLimbs_val xs (notLimbs ys) 1 (by decide) hnlen
  have hnv := notLimbs_val ys
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [subLimbs]
  rw [hav, h1, hlen]
  omega

/-! ## Multi-limb modular reduction: the conditional subtract `V mod p` for `V < 2p`

The single-limb reduction `bCondSub` (`FieldReduceIdioms`) handles `x < 2p`; its
multi-limb analog reduces an `n`-limb value `V ∈ [0, 2p)` to its residue. Compute
`d = subLimbs V p` (whose top limb is the not-borrow flag, `1` iff `V ≥ p`), then
branchless-select the low `n` limbs of `d` (`= V − p`) when `V ≥ p`, else `V`. This
is `V mod p`, and every step is a verified multi-limb add/sub plus a per-limb
mask-select the backends already lower. -/

/-- An `n`-limb value is below `2^(64n)`. -/
theorem bignumVal_lt : ∀ l : List (BitVec 64), bignumVal l < (2 ^ 64) ^ l.length
  | [] => by simp [bignumVal]
  | a :: as => by
      have ih := bignumVal_lt as
      have ha := a.isLt
      have hps : ((2 : ℕ) ^ 64) ^ (as.length + 1) = (2 ^ 64) ^ as.length * 2 ^ 64 :=
        pow_succ _ _
      simp only [bignumVal, List.length_cons]
      omega

/-- `bignumVal` of an appended top limb: the limb scales by `2^(64·len)`. -/
theorem bignumVal_snoc : ∀ (xs : List (BitVec 64)) (t : BitVec 64),
    bignumVal (xs ++ [t]) = bignumVal xs + t.toNat * (2 ^ 64) ^ xs.length
  | [], t => by simp [bignumVal]
  | x :: xs, t => by
      have ih := bignumVal_snoc xs t
      have hps : ((2 : ℕ) ^ 64) ^ (xs.length + 1) = (2 ^ 64) ^ xs.length * 2 ^ 64 :=
        pow_succ _ _
      simp only [List.cons_append, bignumVal, List.length_cons]
      rw [ih, hps]; ring

/-- The carry chain (and so `subLimbs`) of equal-length operands has length `n + 1`. -/
theorem addLimbs_length : ∀ (xs ys : List (BitVec 64)) (c : BitVec 64),
    xs.length = ys.length → (addLimbs xs ys c).length = xs.length + 1
  | [], [], _, _ => by simp [addLimbs]
  | x :: xs, y :: ys, c, hlen => by
      have ih := addLimbs_length xs ys (bSltu (x + y) x + bSltu (x + y + c) (x + y))
        (by simpa using hlen)
      simp only [addLimbs, List.length_cons]; rw [ih]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- Branchless per-limb select: mask all-ones picks `a`, mask zero picks `b`. -/
def selLimbs (m : BitVec 64) : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | a :: as, b :: bs => ((a &&& m) ||| (b &&& ~~~m)) :: selLimbs m as bs
  | _, _ => []

/-- All-ones mask selects the first operand. -/
theorem selLimbs_ones : ∀ (a b : List (BitVec 64)), a.length = b.length →
    bignumVal (selLimbs (-1) a b) = bignumVal a
  | [], [], _ => by simp [selLimbs, bignumVal]
  | x :: xs, y :: ys, hlen => by
      have ih := selLimbs_ones xs ys (by simpa using hlen)
      have hpix : (x &&& (-1) ||| y &&& ~~~(-1 : BitVec 64)) = x := by bv_decide
      simp only [selLimbs, bignumVal]; rw [hpix, ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- Zero mask selects the second operand. -/
theorem selLimbs_zero : ∀ (a b : List (BitVec 64)), a.length = b.length →
    bignumVal (selLimbs 0 a b) = bignumVal b
  | [], [], _ => by simp [selLimbs, bignumVal]
  | x :: xs, y :: ys, hlen => by
      have ih := selLimbs_zero xs ys (by simpa using hlen)
      have hpix : (x &&& 0 ||| y &&& ~~~(0 : BitVec 64)) = y := by bv_decide
      simp only [selLimbs, bignumVal]; rw [hpix, ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **Multi-limb conditional subtract** — the modular reduction for `V < 2p`. -/
def condSubLimbs (x p : List (BitVec 64)) : List (BitVec 64) :=
  let d := subLimbs x p
  selLimbs (0 - d.getLastD 0) d.dropLast x

/-- **Multi-limb modular reduction value-correctness.** For an `n`-limb value
    `V = bignumVal x` with `V < 2·bignumVal p`, the conditional subtract is exactly
    the residue `V mod p`. The over-limbs analog of `bCondSub_toNat`. -/
theorem condSubLimbs_val (x p : List (BitVec 64)) (hlen : x.length = p.length)
    (hx : bignumVal x < 2 * bignumVal p) :
    bignumVal (condSubLimbs x p) = bignumVal x % bignumVal p := by
  set n := x.length with hn
  set V := bignumVal x with hV
  set P := bignumVal p with hP
  set Q := (2 ^ 64) ^ n with hQ
  -- the difference d and its decomposition into low limbs `dl` and top flag
  have hnl : x.length = (notLimbs p).length := by
    simp only [notLimbs, List.length_map]; exact hlen
  have hdlen : (subLimbs x p).length = n + 1 := by
    simpa [subLimbs, hn] using addLimbs_length x (notLimbs p) 1 hnl
  have hne : subLimbs x p ≠ [] := by
    intro h; rw [h] at hdlen; simp at hdlen
  set d := subLimbs x p with hd
  set flag := d.getLastD 0 with hflag
  set dl := d.dropLast with hdl
  have hgl : d.getLastD 0 = d.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
  have hsplit : dl ++ [flag] = d := by
    rw [hdl, hflag, hgl]; exact List.dropLast_concat_getLast hne
  have hdllen : dl.length = n := by
    have hc := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil, hdlen] at hc
    omega
  -- value relations
  have hsnoc : bignumVal d = bignumVal dl + flag.toNat * Q := by
    have hbs := bignumVal_snoc dl flag
    rw [hsplit, hdllen] at hbs; exact hbs
  have hsv : bignumVal d + P = V + Q := by
    have hsubv := subLimbs_val x p hlen; rw [← hd] at hsubv; exact hsubv
  have hdllt : bignumVal dl < Q := by have := bignumVal_lt dl; rwa [hdllen] at this
  have hplt : P < Q := by have := bignumVal_lt p; rwa [← hlen] at this
  have hQpos : 0 < Q := by rw [hQ]; positivity
  -- E : bignumVal dl + flag.toNat * Q + P = V + Q
  have hE : bignumVal dl + flag.toNat * Q + P = V + Q := by rw [← hsnoc]; exact hsv
  -- the top limb is the not-borrow bit, 0 or 1
  have hm1 : flag.toNat ≤ 1 := by
    nlinarith [hE, hdllt, hx, hplt, hQpos, Nat.zero_le (bignumVal dl)]
  have hcases : flag.toNat = 0 ∨ flag.toNat = 1 := by omega
  rcases hcases with hf0 | hf1
  · -- flag = 0 ⇒ V < p ⇒ select x unchanged
    rw [hf0] at hE
    have hVlt : V < P := by omega
    have hfeq : flag = 0 := by rw [← BitVec.toNat_inj]; simpa using hf0
    have hmask : (0 : BitVec 64) - flag = 0 := by rw [hfeq]; decide
    simp only [condSubLimbs, ← hd]
    rw [← hflag, ← hdl, hmask, selLimbs_zero dl x (by rw [hdllen, hn]),
        Nat.mod_eq_of_lt hVlt]
  · -- flag = 1 ⇒ p ≤ V ⇒ select the difference dl = V - p
    rw [hf1] at hE
    have hVge : P ≤ V := by omega
    have hdlv : bignumVal dl = V - P := by omega
    have hfeq : flag = 1 := by rw [← BitVec.toNat_inj]; simpa using hf1
    have hmask : (0 : BitVec 64) - flag = -1 := by rw [hfeq]; decide
    simp only [condSubLimbs, ← hd]
    rw [← hflag, ← hdl, hmask, selLimbs_ones dl x (by rw [hdllen, hn]), hdlv,
        Nat.mod_eq_sub_mod hVge, Nat.mod_eq_of_lt (by omega)]

/-! ## Barrett reduction: the quotient-error bound

The mathematical heart of reducing a wide value `x < 2^m` modulo `p`: with the
precomputed reciprocal `μ = ⌊2^m / p⌋`, the estimate `q = ⌊x·μ / 2^m⌋` satisfies
`q·p ≤ x < (q+2)·p`. So `x − q·p ∈ [0, 2p)`, which the conditional subtract
(`condSubLimbs`) finishes. This is a pure-`Nat` fact about floors — the limb-level
Barrett kernel computes `μ` (a constant), `x·μ` and `q·p` (`mulBignum`), the shift
(limb drop) and `x − q·p` (`subLimbs`), each already value-correct. -/

/-- **Barrett quotient-error bound.** For `x < 2^m` and `μ = ⌊2^m/p⌋`, the estimate
    `q = ⌊x·μ/2^m⌋` brackets the true quotient: `q·p ≤ x < (q+2)·p`. -/
theorem barrett_bound (x p m : Nat) (hp : 0 < p) (hx : x < 2 ^ m) :
    (x * (2 ^ m / p) / 2 ^ m) * p ≤ x ∧
    x < (x * (2 ^ m / p) / 2 ^ m + 2) * p := by
  have h2m : 0 < 2 ^ m := by positivity
  set μ := 2 ^ m / p with hμ
  set q := x * μ / 2 ^ m with hq
  have hμp : μ * p ≤ 2 ^ m := Nat.div_mul_le_self (2 ^ m) p
  have hq1 : q * 2 ^ m ≤ x * μ := Nat.div_mul_le_self (x * μ) (2 ^ m)
  have hμp2 : 2 ^ m < μ * p + p := Nat.lt_div_mul_add hp
  have hq2 : x * μ < q * 2 ^ m + 2 ^ m := Nat.lt_div_mul_add h2m
  refine ⟨?_, ?_⟩
  · -- upper: q·p ≤ x
    apply Nat.le_of_mul_le_mul_right _ h2m
    calc q * p * 2 ^ m = q * 2 ^ m * p := by ring
      _ ≤ x * μ * p := by gcongr
      _ = x * (μ * p) := by ring
      _ ≤ x * 2 ^ m := by gcongr
  · -- lower: x < (q+2)·p
    by_cases hμ0 : μ = 0
    · have hlt : 2 ^ m < p := by rw [hμ0] at hμp2; omega
      have hq0 : q = 0 := by rw [hq, hμ0, Nat.mul_zero, Nat.zero_div]
      rw [hq0]; omega
    · have hμpos : 0 < μ := Nat.pos_of_ne_zero hμ0
      have hxμ : x * μ < 2 ^ m * μ := by
        have := (Nat.mul_lt_mul_right hμpos).mpr hx; simpa [Nat.mul_comm] using this
      have hqμ : q < μ := by
        have hlt : q * 2 ^ m < μ * 2 ^ m := by
          calc q * 2 ^ m ≤ x * μ := hq1
            _ < 2 ^ m * μ := hxμ
            _ = μ * 2 ^ m := by ring
        exact (Nat.mul_lt_mul_right h2m).mp hlt
      have hq1pos : 0 < q + 1 := Nat.succ_pos q
      have hfinal : x * μ < (q + 2) * p * μ :=
        calc x * μ < q * 2 ^ m + 2 ^ m := hq2
          _ = (q + 1) * 2 ^ m := by ring
          _ < (q + 1) * (μ * p + p) := (Nat.mul_lt_mul_left hq1pos).mpr hμp2
          _ ≤ (q + 2) * p * μ := by nlinarith [hqμ, hp, hμpos]
      exact Nat.lt_of_mul_lt_mul_right hfinal

/-- **Limb shift.** Dropping the low `k` limbs is division by `2^(64k)` — the right
    shift the Barrett quotient `⌊x·μ / 2^m⌋` needs (`m = 64k`). -/
theorem bignumVal_drop : ∀ (k : Nat) (l : List (BitVec 64)),
    bignumVal (l.drop k) = bignumVal l / (2 ^ 64) ^ k
  | 0, l => by simp
  | _ + 1, [] => by simp [bignumVal]
  | k + 1, a :: as => by
      have ih := bignumVal_drop k as
      have ha := a.isLt
      have hpow : ((2 : ℕ) ^ 64) ^ (k + 1) = 2 ^ 64 * (2 ^ 64) ^ k := by
        rw [pow_succ, Nat.mul_comm]
      have hdiv : (a.toNat + 2 ^ 64 * bignumVal as) / 2 ^ 64 = bignumVal as := by
        rw [Nat.mul_comm, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt ha,
          Nat.zero_add]
      simp only [List.drop_succ_cons, bignumVal]
      rw [ih, hpow, ← Nat.div_div_eq_div_mul, hdiv]

/-- **Take/drop value split.** Splitting a limb list at `k` splits its value into the
    low `k` limbs plus the high limbs scaled by `2^(64k)`. -/
theorem bignumVal_take_drop : ∀ (k : Nat) (l : List (BitVec 64)),
    bignumVal l = bignumVal (l.take k) + (2 ^ 64) ^ k * bignumVal (l.drop k)
  | 0, l => by simp [bignumVal]
  | _ + 1, [] => by simp [bignumVal]
  | k + 1, a :: as => by
      have ih := bignumVal_take_drop k as
      have hpow : ((2 : ℕ) ^ 64) ^ (k + 1) = 2 ^ 64 * (2 ^ 64) ^ k := by
        rw [pow_succ, Nat.mul_comm]
      simp only [List.take_succ_cons, List.drop_succ_cons, bignumVal]
      rw [ih, hpow]; ring

/-- A value below `2^(64k)` is unchanged by truncating to its low `k` limbs. -/
theorem bignumVal_take_of_lt (k : Nat) (l : List (BitVec 64))
    (h : bignumVal l < (2 ^ 64) ^ k) : bignumVal (l.take k) = bignumVal l := by
  have hd : bignumVal (l.drop k) = 0 := by rw [bignumVal_drop]; exact Nat.div_eq_of_lt h
  have hsplit := bignumVal_take_drop k l
  rw [hd, Nat.mul_zero, Nat.add_zero] at hsplit
  exact hsplit.symm

/-! ## Length bounds and the full Barrett field reduction -/

/-- The scalar inner loop produces one limb per input plus the final carry. -/
theorem mulScalar_length (a : BitVec 64) : ∀ (bs : List (BitVec 64)) (c : BitVec 64),
    (mulScalar a bs c).length = bs.length + 1
  | [], _ => by simp [mulScalar]
  | b :: bs, c => by
      have ih := mulScalar_length a bs (mulhi a b + bSltu (a * b + c) (a * b))
      simp only [mulScalar, List.length_cons]; omega

/-- The uneven add produces `max` of the input lengths plus one. -/
theorem bnAdd_length : ∀ (xs ys : List (BitVec 64)) (c : BitVec 64),
    (bnAdd xs ys c).length = max xs.length ys.length + 1
  | [], [], _ => by simp [bnAdd]
  | [], y :: ys, c => by
      have ih := bnAdd_length [] ys (bSltu (y + c) y)
      simp only [bnAdd, List.length_cons, List.length_nil] at *; omega
  | x :: xs, [], c => by
      have ih := bnAdd_length xs [] (bSltu (x + c) x)
      simp only [bnAdd, List.length_cons, List.length_nil] at *; omega
  | x :: xs, y :: ys, c => by
      have ih := bnAdd_length xs ys (bSltu (x + y) x + bSltu (x + y + c) (x + y))
      simp only [bnAdd, List.length_cons] at *; omega

/-- A nonempty schoolbook multiply has at least `bs.length + 1` limbs. -/
theorem mulBignum_length_ge (a : BitVec 64) (as bs : List (BitVec 64)) :
    bs.length + 1 ≤ (mulBignum (a :: as) bs).length := by
  simp only [mulBignum, bnAdd_length, mulScalar_length, List.length_cons]; omega

/-- The low `W` limbs of a `(W+1)`-limb value are its residue mod `2^(64W)`. -/
theorem bignumVal_dropLast (W : Nat) (l : List (BitVec 64)) (hl : l.length = W + 1) :
    bignumVal l.dropLast = bignumVal l % (2 ^ 64) ^ W := by
  have hne : l ≠ [] := by intro h; rw [h] at hl; simp at hl
  have hsplit : l.dropLast ++ [l.getLast hne] = l := List.dropLast_concat_getLast hne
  have hdl : l.dropLast.length = W := by
    have hc := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil, hl] at hc; omega
  have hbs := bignumVal_snoc l.dropLast (l.getLast hne)
  rw [hsplit, hdl] at hbs
  rw [hbs, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by have := bignumVal_lt l.dropLast; rwa [hdl] at this)]

/-- **Full multi-limb Barrett field reduction.** Reduce the `W`-limb value `x`
    modulo the `W`-limb prime `p`, given the precomputed reciprocal `mu = ⌊2^(64W)/p⌋`.
    Quotient estimate `q = ⌊x·mu / 2^(64W)⌋` (multiply + limb drop), difference
    `x − q·p` (truncated multiply + subtract), then one conditional subtract. -/
def barrettReduce (x p mu : List (BitVec 64)) (W : Nat) : List (BitVec 64) :=
  let q := (mulBignum x mu).drop W
  let qp := (mulBignum q p).take W
  condSubLimbs (subLimbs x qp).dropLast p

/-- **Barrett reduction value-correctness.** The full reduction computes `x mod p`
    for any `W`-limb prime `p`, composing the verified multiply, drop, subtract and
    conditional-subtract kernels under the Barrett quotient-error bound. -/
theorem barrettReduce_val (x p mu : List (BitVec 64)) (W : Nat) (hW : 0 < W)
    (hxl : x.length = W) (hpl : p.length = W) (hmul : mu.length = W)
    (hppos : 0 < bignumVal p)
    (hmuval : bignumVal mu = (2 ^ 64) ^ W / bignumVal p) :
    bignumVal (barrettReduce x p mu W) = bignumVal x % bignumVal p := by
  have hVB : bignumVal x < (2 ^ 64) ^ W := by have := bignumVal_lt x; rwa [hxl] at this
  have hBe : (2 : ℕ) ^ (64 * W) = (2 ^ 64) ^ W := by rw [pow_mul]
  -- x nonempty ⇒ mulBignum x mu has ≥ W+1 limbs ⇒ q nonempty
  have hxne : x ≠ [] := by intro h; rw [h] at hxl; simp at hxl; omega
  obtain ⟨xh, xt, hxeq⟩ := List.exists_cons_of_ne_nil hxne
  have hxmu_len : W + 1 ≤ (mulBignum x mu).length := by
    rw [hxeq]; have h := mulBignum_length_ge xh xt mu; rwa [hmul] at h
  have hqne : (mulBignum x mu).drop W ≠ [] := by
    intro h; have hc := congrArg List.length h; rw [List.length_drop] at hc; simp at hc; omega
  obtain ⟨qh, qt, hqeq⟩ := List.exists_cons_of_ne_nil hqne
  -- quotient value and Barrett bracket
  have hqval : bignumVal ((mulBignum x mu).drop W)
      = bignumVal x * ((2 ^ 64) ^ W / bignumVal p) / (2 ^ 64) ^ W := by
    rw [bignumVal_drop, mulBignum_val, hmuval]
  obtain ⟨hub, hlb⟩ :=
    barrett_bound (bignumVal x) (bignumVal p) (64 * W) hppos (by rw [hBe]; exact hVB)
  rw [hBe] at hub hlb
  rw [← hqval] at hub hlb
  set qv := bignumVal ((mulBignum x mu).drop W) with hqvd
  have hlb' : bignumVal x < qv * bignumVal p + 2 * bignumVal p := by
    rw [show qv * bignumVal p + 2 * bignumVal p = (qv + 2) * bignumVal p from by ring]; exact hlb
  -- qp = (mulBignum q p).take W : value qv·P, length W
  have hqpsrc : W ≤ (mulBignum ((mulBignum x mu).drop W) p).length := by
    rw [hqeq]; have h := mulBignum_length_ge qh qt p; rw [hpl] at h; omega
  have hqpval : bignumVal ((mulBignum ((mulBignum x mu).drop W) p).take W) = qv * bignumVal p := by
    rw [bignumVal_take_of_lt, mulBignum_val]
    rw [mulBignum_val]; exact lt_of_le_of_lt hub hVB
  have hqplen : ((mulBignum ((mulBignum x mu).drop W) p).take W).length = W := by
    rw [List.length_take]; omega
  -- difference r = subLimbs x qp : value V + B − qv·P, length W+1
  set qp := (mulBignum ((mulBignum x mu).drop W) p).take W with hqpd
  have hxqp : x.length = qp.length := by rw [hxl, hqplen]
  have hrlen : (subLimbs x qp).length = W + 1 := by
    rw [subLimbs, addLimbs_length x (notLimbs qp) 1 (by simp [notLimbs, hxqp]), hxl]
  have hrval : bignumVal (subLimbs x qp) = bignumVal x + (2 ^ 64) ^ W - qv * bignumVal p := by
    have hs := subLimbs_val x qp hxqp
    rw [hqpval, hxl] at hs; omega
  -- low W limbs of r hold V − qv·P
  have hdrop : bignumVal (subLimbs x qp).dropLast = bignumVal x - qv * bignumVal p := by
    rw [bignumVal_dropLast W _ hrlen, hrval]
    have hsub : bignumVal x + (2 ^ 64) ^ W - qv * bignumVal p
        = (bignumVal x - qv * bignumVal p) + (2 ^ 64) ^ W := by omega
    rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- final conditional subtract
  have hdroplen : (subLimbs x qp).dropLast.length = W := by
    rw [List.length_dropLast, hrlen]; omega
  simp only [barrettReduce, ← hqpd]
  rw [condSubLimbs_val _ p (by rw [hdroplen, hpl]) (by rw [hdrop]; omega), hdrop]
  -- (V − qv·P) mod P = V mod P
  conv_rhs => rw [show bignumVal x = (bignumVal x - qv * bignumVal p) + qv * bignumVal p from by omega]
  rw [Nat.add_mul_mod_self_right]

end CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
