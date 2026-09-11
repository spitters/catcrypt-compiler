/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie

/-!
# #606 fan-out: the verified compiler emits the Mersenne-31 field ADD and REDUCE

This module completes the Mersenne-31 (`p = 2³¹ − 1 = 2147483647`, the
CircleSTARK / Plonky3-M31 base field) compile-from-hax leaf family: the
**multiply** is `CompileFromHaxMersenne31.m31Mul_compiles`; here we add the
**field add** and the standalone **Mersenne reduce** (the `2³¹ ≡ 1` double-fold
plus branch-free conditional subtract that is the M31 analogue of the Baby Bear
`barrettReduceMU`).

## Mersenne-31 add, `w = 64`

With `a, b ∈ [0, p)` the sum `a + b ≤ 2p − 2 < 2³²` fits without wrap, and a
single branch-free conditional subtract of `p` lands the canonical residue:

```
   s := a + b                                     -- s < 2³²
   t := s - p ; m := t >> 63 ; r := ((0 - m) & p) + t
```

## Mersenne-31 reduce, `w = 64`

For any `x < 2⁶²` (the product domain: `(2³¹−2)² < 2⁶²`), `2³¹ ≡ 1 (mod p)`
folds the high bits; two folds plus one conditional subtract land `x mod p`:

```
   x := (x & M) + (x >> 31)                       -- 1st fold: x < 2³²  (M = p)
   x := (x & M) + (x >> 31)                       -- 2nd fold: x ≤ 2³¹
   t := x - p ; m := t >> 63 ; r := ((0 - m) & p) + t
```

`m31MulFold = m31ReduceFold ∘ (·*·)` definitionally (`m31ReduceFold_mulFold`).

All steps are `&`/`>>`/`+`/`-` over GPRs — the existing recognizers
(`wrapping_add`/`wrapping_sub`/`shift_right`/`BitAnd` with literal counts)
accept them, so **no change to the verified front is required**.

## Method (mirrors `CompileFromHaxMersenne31.m31Mul_compiles`)

`m31AddSrc`/`m31ReduceSrc` are the let-normalized `ImpExpr`s; `m31AddFold`/
`m31ReduceFold` the explicit closed emit forms they denote to; the `_compiles`
theorems route the source-spec `rfl`s through the C3 per-primitive obligation
`compileFromHax_meets_spec`. The abstract `% p` ties (`m31AddFold_eq_mod`,
`m31ReduceFold_eq_mod`) are closed by `Nat` arithmetic on `toNat` (no
`bv_decide` bitblast — the #117 Barrett seam SAT-times-out at `2³¹`), and the
`Zm31 = ZMod 2147483647` field ties (`m31AddFold_eq_field`,
`m31ReduceFold_eq_field`) lift them to the Mathlib field, the add/reduce
analogues of `CompileFromHaxMersenne31Tie.m31MulFold_eq_field`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Add

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Tie
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## The Mersenne-31 add source — `w = 64`, parameters `["a","b"]` -/

/-- The Mersenne-31 field-add source as a hax `ImpExpr`, fully let-normalized,
    parameters `["a","b"]`. Integer add (no wrap on the residue domain), then a
    branch-free conditional subtract of `p = 2³¹−1` using the `0 − (t >> 63)`
    mask. Returns the residue register `r`. -/
def m31AddSrc : ImpExpr :=
  .letBind "cP" (.lit (.int 2147483647))
   (.letBind "c0" (.lit (.int 0))
    (.letBind "s" (.app "wrapping_add" [.var "a", .var "b"])
     (.letBind "t" (.app "wrapping_sub" [.var "s", .var "cP"])
      (.letBind "m" (.app "shift_right" [.var "t", .lit (.int 63)])
       (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
        (.letBind "mm" (.app "BitAnd" [.var "nm", .var "cP"])
         (.letBind "r" (.app "wrapping_add" [.var "mm", .var "t"])
          (.var "r"))))))))

/-- The explicit closed **emit form** the add source denotes to, at `w = 64`:
    integer add plus the branch-free conditional subtract of `p`.
    `m31AddFold_eq_mod` ties it to abstract `(a+b) % p` on `a, b < p`. -/
def m31AddFold (a b : BitVec 64) : BitVec 64 :=
  let s := a + b
  let t := s - 2147483647
  let m := t >>> (63 : Nat)
  ((0 - m) &&& 2147483647) + t

/-- The Mersenne-31 add source denotes (under `denoteScalar`, parameters
    `["a","b"]`) to the emit form `m31AddFold`. -/
theorem m31AddSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["a", "b"] I m31AddSrc (fun _ => none)
      = some (m31AddFold (inpGet I 0) (inpGet I 1)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the Mersenne-31 add. -/
theorem m31Add_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 2) ["a", "b"] m31AddSrc).isSome := by
  native_decide

/-- **Mersenne-31 add emitted by the verified compiler (fold form).**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["a","b"] m31AddSrc = some c`, and for every `(a, b)`,
    `c`'s `BitVec 64` denotation (under `![a, b]`) is the closed emit form
    `m31AddFold`. Routed through `compileFromHax_meets_spec`. The abstract
    `(a+b) % p` tie is `m31AddFold_eq_mod`. -/
theorem m31Add_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 2 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 2) ["a", "b"] m31AddSrc = some prog ∧
      ∀ (a b : BitVec 64),
        prog.denote (inputValuation 64 2 ![a, b])
          = m31AddFold a b := by
  set prog := (compileFromHax (w := 64) (nIn := 2) ["a", "b"] m31AddSrc).get
    m31Add_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 2) ["a", "b"] m31AddSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar ["a", "b"] ![a, b]
      m31AddSrc (fun _ => none) = some (m31AddFold a b) := by
    have h := m31AddSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 2) ["a", "b"]
    ![a, b] m31AddSrc _ hc hspec

/-! ## The Mersenne-31 reduce source — `w = 64`, parameter `["x"]` -/

/-- The standalone Mersenne-31 reduce source as a hax `ImpExpr`, parameter
    `["x"]`: the `2³¹ ≡ 1` double-fold plus the branch-free conditional subtract
    (the tail of `m31MulSrc`, exposed as its own leaf — the M31 analogue of the
    Baby Bear `barrettReduceMU`). Valid on `x < 2⁶²` (the product domain). -/
def m31ReduceSrc : ImpExpr :=
  .letBind "cP" (.lit (.int 2147483647))
   (.letBind "c0" (.lit (.int 0))
    (.letBind "lo0" (.app "BitAnd" [.var "x", .var "cP"])
     (.letBind "hi0" (.app "shift_right" [.var "x", .lit (.int 31)])
      (.letBind "p1" (.app "wrapping_add" [.var "lo0", .var "hi0"])
       (.letBind "lo1" (.app "BitAnd" [.var "p1", .var "cP"])
        (.letBind "hi1" (.app "shift_right" [.var "p1", .lit (.int 31)])
         (.letBind "p2" (.app "wrapping_add" [.var "lo1", .var "hi1"])
          (.letBind "t" (.app "wrapping_sub" [.var "p2", .var "cP"])
           (.letBind "m" (.app "shift_right" [.var "t", .lit (.int 63)])
            (.letBind "nm" (.app "wrapping_sub" [.var "c0", .var "m"])
             (.letBind "mm" (.app "BitAnd" [.var "nm", .var "cP"])
              (.letBind "r" (.app "wrapping_add" [.var "mm", .var "t"])
               (.var "r")))))))))))))

/-- The explicit closed **emit form** the reduce source denotes to, at `w = 64`:
    the Mersenne `2³¹ ≡ 1` double-fold plus the branch-free conditional
    subtract. `m31ReduceFold_eq_mod` ties it to `x % p` on `x < 2⁶²`. -/
def m31ReduceFold (x : BitVec 64) : BitVec 64 :=
  let p1 := (x &&& 2147483647) + (x >>> (31 : Nat))
  let p2 := (p1 &&& 2147483647) + (p1 >>> (31 : Nat))
  let t  := p2 - 2147483647
  let m  := t >>> (63 : Nat)
  let mm := (0 - m) &&& 2147483647
  mm + t

/-- The emitted multiply IS multiply-then-reduce: `m31MulFold a b`
    (`CompileFromHaxMersenne31`) is definitionally `m31ReduceFold (a * b)`. -/
theorem m31ReduceFold_mulFold (a b : BitVec 64) :
    CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31.m31MulFold a b
      = m31ReduceFold (a * b) := rfl

/-- The Mersenne-31 reduce source denotes (under `denoteScalar`, parameter
    `["x"]`) to the emit form `m31ReduceFold`. -/
theorem m31ReduceSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar ["x"] I m31ReduceSrc (fun _ => none)
      = some (m31ReduceFold (inpGet I 0)) := by
  rfl

/-- The compile-from-hax pipeline succeeds on the Mersenne-31 reduce. -/
theorem m31Reduce_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["x"] m31ReduceSrc).isSome := by
  native_decide

/-- **Mersenne-31 reduce emitted by the verified compiler (fold form).**
    There is a compiled `Com jasminDialect` `c` with
    `compileFromHax ["x"] m31ReduceSrc = some c`, and for every `x`, `c`'s
    `BitVec 64` denotation is the closed emit form `m31ReduceFold`. Routed
    through `compileFromHax_meets_spec`. The abstract `x % p` tie (on the
    `x < 2⁶²` domain) is `m31ReduceFold_eq_mod`. -/
theorem m31Reduce_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] m31ReduceSrc = some prog ∧
      ∀ (x : BitVec 64),
        prog.denote (inputValuation 64 1 (fun _ => x))
          = m31ReduceFold x := by
  set prog := (compileFromHax (w := 64) (nIn := 1) ["x"] m31ReduceSrc).get
    m31Reduce_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["x"] m31ReduceSrc
      = some prog := (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro x
  have hspec : ImpExpr.denoteScalar ["x"] (fun _ : Fin 1 => x)
      m31ReduceSrc (fun _ => none) = some (m31ReduceFold x) := by
    have h := m31ReduceSrc_denoteScalar (nIn := 1) (fun _ => x)
    simpa only [inpGet] using! h
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["x"]
    (fun _ => x) m31ReduceSrc _ hc hspec

/-! ## The abstract `% p` ties (`Nat` arithmetic on `toNat`, no bitblast) -/

/-- On the residue domain `a, b < p = 2³¹−1`, the `BitVec 64` sum is the integer
    sum: it never wraps `2⁶⁴` (`a + b < 2³²`). -/
theorem m31_toNat_add (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    (a + b).toNat = a.toNat + b.toNat := by
  have h1 : a.toNat < 2147483647 := by bv_omega
  have h2 : b.toNat < 2147483647 := by bv_omega
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Mersenne-31 add fold = `(a+b) mod p`** on the residue domain `a, b < p`
    (`p = 2147483647 = 2³¹ − 1`). Ties the emitted closed fold form `m31AddFold`
    (the `_compiles` deliverable) to abstract modular add. Proved via `Nat`
    arithmetic on `toNat`: the sum `< 2³²` never wraps, and the single
    branch-free csub of `p` lands the result in `[0, p)`. -/
theorem m31AddFold_eq_mod (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    m31AddFold a b = (a + b) % 2147483647#64 := by
  have ham : a.toNat < 2147483647 := by bv_omega
  have hbm : b.toNat < 2147483647 := by bv_omega
  have hmask : ∀ n : Nat, n &&& 2147483647 = n % 2147483648 := by
    intro n; rw [show (2147483647 : Nat) = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hlit : BitVec.toNat (2147483647 : BitVec 64) = 2147483647 := rfl
  have hlit0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
  apply BitVec.eq_of_toNat_eq
  unfold m31AddFold
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_sub, BitVec.toNat_umod, Nat.shiftRight_eq_div_pow,
    hlit, hlit0, hmask]
  rw [show (2147483647#64 : BitVec 64).toNat = 2147483647 from rfl]
  -- The sum never wraps 2⁶⁴; name it and reason on `Nat`.
  have hs : (a.toNat + b.toNat) % 2 ^ 64 = a.toNat + b.toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [hs]
  set s := a.toNat + b.toNat with hsdef
  have hslt : s < 4294967294 := by omega
  clear_value s
  clear hsdef ham hbm ha hb hmask hlit hlit0 hs
  -- The branch-free csub of `p = 2147483647`, two cases on `s < p`:
  rcases Nat.lt_or_ge s 2147483647 with hlt | hge
  · -- s < p: `t = 2⁶⁴ − p + s ∈ [2⁶³, 2⁶⁴)`, sign bit `m = 1`, mask `= p`,
    -- result `(p + (2⁶⁴ − p + s)) % 2⁶⁴ = s = s % p`.
    have ht : (2 ^ 64 - 2147483647 + s) % 2 ^ 64 = 2 ^ 64 - 2147483647 + s := by
      apply Nat.mod_eq_of_lt; omega
    rw [ht]
    have hm : (2 ^ 64 - 2147483647 + s) / 2 ^ 63 = 1 := by
      rw [Nat.div_eq_of_lt_le] <;> omega
    rw [hm]
    omega
  · -- s ≥ p: `2⁶⁴ − p + s ≥ 2⁶⁴`, so `t = s − p < p`, `m = 0`, mask `0`,
    -- result `s − p = s % p`.
    have ht : (2 ^ 64 - 2147483647 + s) % 2 ^ 64 = s - 2147483647 := by
      have : 2 ^ 64 - 2147483647 + s = 2 ^ 64 + (s - 2147483647) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [ht]
    have hm : (s - 2147483647) / 2 ^ 63 = 0 := by
      apply Nat.div_eq_of_lt; omega
    rw [hm]
    omega

/-- **Mersenne-31 reduce fold = `x mod p`** on the product domain `x < 2⁶²`
    (`p = 2147483647 = 2³¹ − 1`). Ties the emitted closed fold form
    `m31ReduceFold` (the `_compiles` deliverable) to the abstract modular
    reduce. Proved via `Nat` arithmetic on `toNat` (the same structured route as
    `CompileFromHaxMersenne31.m31MulFold_eq_mod`, of which this is the tail):
    `2³¹ ≡ 1`, so the first fold preserves the residue with value `< 2³²`, the
    second drops it to `≤ 2³¹`, and the branch-free csub lands `[0, p)`. -/
theorem m31ReduceFold_eq_mod (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    m31ReduceFold x = x % 2147483647#64 := by
  have hmask : ∀ n : Nat, n &&& 2147483647 = n % 2147483648 := by
    intro n; rw [show (2147483647 : Nat) = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hlit : BitVec.toNat (2147483647 : BitVec 64) = 2147483647 := rfl
  have hlit0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
  apply BitVec.eq_of_toNat_eq
  unfold m31ReduceFold
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_sub, BitVec.toNat_umod, Nat.shiftRight_eq_div_pow,
    hlit, hlit0, hmask]
  rw [show (2147483647#64 : BitVec 64).toNat = 2147483647 from rfl]
  set P := x.toNat with hP
  clear_value P
  clear hP hmask hlit hlit0
  -- Euclidean split `P = q·2³¹ + r`, `q, r < 2³¹` (`P < 2⁶²`).
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2147483648 ∧ P = q * 2147483648 + r :=
    ⟨P / 2147483648, P % 2147483648, Nat.mod_lt _ (by norm_num), by omega⟩
  have hq : q < 2147483648 := by omega
  -- First fold value f1 = r + q, < 2³².
  have hf1 : (q * 2147483648 + r) % 2147483648 + (q * 2147483648 + r) / 2 ^ 31 = r + q := by
    rw [show (2 ^ 31 : Nat) = 2147483648 from rfl]
    omega
  rw [hf1]
  have hf1lt : r + q < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hf1lt]
  -- Second fold value f2 = (r+q) % 2³¹ + (r+q) / 2³¹, ≤ 2³¹.
  set f2 := (r + q) % 2147483648 + (r + q) / 2 ^ 31 with hf2
  have hf2lt : f2 < 2 ^ 64 := by
    rw [hf2, show (2 ^ 31 : Nat) = 2147483648 from rfl]; omega
  rw [Nat.mod_eq_of_lt hf2lt]
  have hf2le : f2 ≤ 2147483648 := by
    rw [hf2, show (2 ^ 31 : Nat) = 2147483648 from rfl]; omega
  -- f2 ≡ P (mod p): the two folds preserve the residue mod p = 2³¹−1.
  have hcong : f2 % 2147483647 = (q * 2147483648 + r) % 2147483647 := by
    rw [hf2, show (2 ^ 31 : Nat) = 2147483648 from rfl]
    omega
  clear_value f2
  rw [← hcong]
  -- The branch-free csub of `p`; `f2 ≤ 2³¹ = p + 1`.
  rcases Nat.lt_or_ge f2 2147483647 with hlt | hge
  · have ht : (2 ^ 64 - 2147483647 + f2) % 2 ^ 64 = 2 ^ 64 - 2147483647 + f2 := by
      apply Nat.mod_eq_of_lt; omega
    rw [ht]
    have hm : (2 ^ 64 - 2147483647 + f2) / 2 ^ 63 = 1 := by
      rw [Nat.div_eq_of_lt_le] <;> omega
    rw [hm]
    omega
  · have ht : (2 ^ 64 - 2147483647 + f2) % 2 ^ 64 = f2 - 2147483647 := by
      have : 2 ^ 64 - 2147483647 + f2 = 2 ^ 64 + (f2 - 2147483647) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [ht]
    have hm : (f2 - 2147483647) / 2 ^ 63 = 0 := by
      apply Nat.div_eq_of_lt; omega
    rw [hm]
    omega

/-! ## The `Zm31 = ZMod 2147483647` field ties (the add/reduce analogues of
`CompileFromHaxMersenne31Tie.m31MulFold_eq_field`) -/

/-- **Mersenne-31 add emit-form ↔ abstract `Zm31` field tie.** On the residue
    domain `a, b < p`, the emitted add fold — read back as a
    `Zm31 = ZMod 2147483647` field element via `fromNat ∘ toNat` — equals the
    `Zm31` field sum of the elements the inputs encode. Composed with
    `m31Add_compiles`, the verified compiler's emitted jasmin `Com` computes the
    Mersenne `GF(2³¹−1)` base-field add. -/
theorem m31AddFold_eq_field (a b : BitVec 64)
    (ha : a < 2147483647#64) (hb : b < 2147483647#64) :
    fromNat (m31AddFold a b).toNat
      = fromNat a.toNat + fromNat b.toNat := by
  rw [m31AddFold_eq_mod a b ha hb]
  unfold fromNat
  have hp : (2147483647#64 : BitVec 64).toNat = 2147483647 := by decide
  rw [BitVec.toNat_umod, hp, m31_toNat_add a b ha hb]
  rw [ZMod.natCast_mod, Nat.cast_add]

/-- **Mersenne-31 reduce emit-form ↔ abstract `Zm31` field tie.** On the product
    domain `x < 2⁶²`, the emitted reduce fold — read back as a `Zm31` field
    element — equals the field element `x` encodes: the reduce is the identity
    on residues classes. Composed with `m31Reduce_compiles`, the emitted jasmin
    `Com` computes the canonical-residue projection of `GF(2³¹−1)`. -/
theorem m31ReduceFold_eq_field (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    fromNat (m31ReduceFold x).toNat = fromNat x.toNat := by
  rw [m31ReduceFold_eq_mod x hx]
  unfold fromNat
  have hp : (2147483647#64 : BitVec 64).toNat = 2147483647 := by decide
  rw [BitVec.toNat_umod, hp, ZMod.natCast_mod]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMersenne31Add
