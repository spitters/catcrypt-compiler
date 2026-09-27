/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.JasminTypes
public import Mathlib.Data.List.Basic

/-!
# `LowCT` scalar expressions

The scalar expression language `SExpr` of `LowCT`
(`CatCrypt.Crypto.Jasmin.LowCT` re-exports it) with its scalar-environment
semantics: `SExpr.eval` over unbounded naturals, `SExpr.evalBV` over 64-bit
words, the side condition `SExpr.inRange` under which the two agree, and the
Rust and Jasmin printers `SExpr.ppRust` and `SExpr.ppJazz`. The tower-aware
evaluators `SExpr.evalState` and `SExpr.evalStateBV` read a `RustState` and
are in `CatCrypt.Crypto.Jasmin.LowCTExec`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

/-! ## §2b  Scalar expressions

`SExpr` is a small expression language over Nat-valued scalar slots
(those bound by `RLetU64Zero` and `RScalarSet`).  Used by
`RScalarSetExpr` to assign a runtime computed
value to a scalar slot, e.g. `k := i * 16 + d` for runtime `i`/`d`.

Mirrors Rocq's `sexpr_ed` (`SafeRustEd25519Sim.v`).  The 8 constructors
cover the index-arithmetic + bit-twiddle patterns the byte-level Rocq
side uses; the Lean side currently only needs `SVar`, `SLit`, `SAdd`,
`SMul`, but parity with Rocq keeps the cross-formalism mapping clean. -/
inductive SExpr where
  | SVar : String → SExpr           -- read a u64-typed scalar slot
  | SLit : Nat → SExpr              -- Nat literal
  | SAdd : SExpr → SExpr → SExpr
  | SSub : SExpr → SExpr → SExpr    -- saturating: max 0
  | SMul : SExpr → SExpr → SExpr
  | SShr : SExpr → SExpr → SExpr    -- right shift (truncating, LOGICAL)
  | SShl : SExpr → SExpr → SExpr    -- left shift
  | SAnd : SExpr → SExpr → SExpr    -- bitwise and
  | SXor : SExpr → SExpr → SExpr    -- bitwise xor (GF(16) add)
  | SLt  : SExpr → SExpr → SExpr    -- x < y → 0 / 1 (UNSIGNED)
  /-- **Signed-arith extension —arithmetic shift right.**
      `SAsr a b` shifts `a` right by `b`, interpreting `a` as a 64-bit
      **two's-complement** signed value: the sign bit (bit 63) is replicated
      into the vacated high bits.  This is the FIPS-204 `montgomery_reduce`
      `r >> 32` step (C99 6.5.7(5) sign-preserving shift on a negative `int64`).
      Lowers to Jasmin `Oasr U64` (`>>s`).  Distinct from `SShr` (logical
      `>>`, vacated bits zero) — the two coincide only when `a`'s sign bit is 0. -/
  | SAsr : SExpr → SExpr → SExpr    -- arithmetic (sign-preserving) shift right
  /-- **Signed-arith extension —signed multiply.**
      `SMulS a b` is the 64-bit low-word product, with both operands
      interpreted as two's-complement.  At the low-64-bit word level a signed
      product and an unsigned product carry the *same* bit pattern (multiply
      is sign-agnostic mod 2^64), so `SMulS` and `SMul` produce identical
      stored words; `SMulS` records the *signed intent* so a following `SAsr`
      reads a sign-correct value (`montgomery_reduce`'s `(int64_t)t * Q`).
      Lowers to Jasmin `Omul U64`. -/
  | SMulS : SExpr → SExpr → SExpr   -- signed (two's-complement) multiply
  /-- **Widening-multiply extension —unsigned high word.**
      `SMulHiU a b` is the *high* 64 bits of the full `64×64 → 128` **unsigned**
      product of `a` and `b` (each read as a `u64` word).  Paired with the
      existing low-word `SMul`, the pair `(SMulHiU a b, SMul a b)` reconstructs
      the full 128-bit unsigned product as a (hi, lo) limb pair — the building
      block for a 128-bit accumulator.  Lowers to the Jasmin `#MULX` intrinsic
      (BMI2 unsigned `hi:lo = a*b`), with the low output discarded (`_`).
      Distinct from `SMul` (which keeps the low word). -/
  | SMulHiU : SExpr → SExpr → SExpr -- high 64 bits of unsigned 64×64→128 product
  /-- **Widening-multiply extension —signed high word.**
      `SMulHiS a b` is the *high* 64 bits of the full `64×64 → 128` **signed**
      (two's-complement) product of `a` and `b`.  Paired with the low-word
      `SMulS`, the pair `(SMulHiS a b, SMulS a b)` reconstructs the full signed
      128-bit product as a (hi, lo) limb pair — the 62-bit-radix safegcd
      `update_de_62` / `update_fg_62` accumulator step (`t.u as i128 * d.v[0] as
      i128`, products up to ~2^124).  Lowers to the Jasmin `#IMUL` intrinsic
      (signed wide multiply, 7 outputs `OF,SF,_,ZF,_,hi,lo`), keeping only the
      `hi` output.  Unlike `SMul`/`SMulS` the *low* word agrees between signed
      and unsigned, but the *high* word does NOT — `SMulHiS` ≠ `SMulHiU`
      whenever exactly one operand's sign bit is set. -/
  | SMulHiS : SExpr → SExpr → SExpr -- high 64 bits of signed 64×64→128 product
  /-- **Tower-limb read extension —read limb `i` of a
      tower slot.**  `SLimb v i` is the value of limb `i` (a little-endian
      `u64` word) of the limb-bearing tower slot named `v`.  Mirrors
      AUCurves' `sexpr_ed` constructor `SLimb : var → nat → sexpr_ed`
      (`SafeRustEd25519Sim.v`), whose `eval_sexpr_ed` reads limb `i` from
      `rs_get_tower_ed rs v` (radix-2^51 / saturated representations,
      masked through `mask64`).  This is the value used by the real inline
      field-op bodies, e.g. `fe25519_add_body`'s
      `REdLimbStore dest i (SAdd (SLimb a i) (SLimb b i))`.

      Because `SLimb` reads the **tower heap**, not the scalar heap, the
      scalar-only `SExpr.eval : (String → Nat) → SExpr → Nat` cannot see its
      value: that evaluator gives `SLimb` a safe default of `0` (a tower-free
      environment carries no limbs).  The faithful image is the
      tower-aware `SExpr.evalState : RustState → SExpr → Nat` (`LowCTExec`), which
      reads the limb from `rs.rsTower`.  Keeping the scalar `eval` signature
      intact is deliberate (other in-flight emit modules depend on it). -/
  | SLimb : String → Nat → SExpr
  deriving Repr, Inhabited

/-- Wrap a `Nat` into its 64-bit two's-complement signed `Int` value:
    bits `[0,63]` of `n` interpreted as a signed 64-bit machine integer.
    Used by the signed `SExpr.eval` arms (`SAsr`, `SMulS`) so the Lean-side
    semantics matches Jasmin's `>>s` / signed-`*` on a `reg u64`. -/
def sexprToSignedInt64 (n : Nat) : Int := (BitVec.ofNat 64 n).toInt

/-- Wrap an `Int` back into its 64-bit two's-complement `Nat` representative
    (bits `[0,63]`), the storage form `rsScalar` holds. -/
def sexprOfSignedInt64 (z : Int) : Nat := (BitVec.ofInt 64 z).toNat

/-- **Widening-multiply extension.** High 64 bits of the full
    `64×64 → 128` **unsigned** product of the two stored words `a`, `b`.
    Each operand is first reduced mod `2^64` (the `u64` storage form), the
    full Nat product is taken, and its bits `[64,127]` are returned.  Matches
    the Jasmin `#MULX` intrinsic's `hi` output. -/
def sexprMulHiU (a b : Nat) : Nat :=
  ((a % (2 ^ 64)) * (b % (2 ^ 64))) >>> 64

/-- **Widening-multiply extension.** High 64 bits of the full
    `64×64 → 128` **signed** (two's-complement) product.  The operands are
    interpreted as signed int64 (`sexprToSignedInt64`), the exact `Int`
    product is taken, arithmetically shifted right by 64 (`Int` shift = floor
    division by `2^64`, i.e. sign-preserving), and the resulting `Int` high
    word is wrapped back to its 64-bit stored pattern.  Matches the Jasmin
    `#IMUL` intrinsic's `hi` output (the `RDX` half of the signed `imul`). -/
def sexprMulHiS (a b : Nat) : Nat :=
  sexprOfSignedInt64 ((sexprToSignedInt64 a * sexprToSignedInt64 b) >>> 64)

/-- Evaluate an `SExpr` against the scalar environment.  Returns a Nat
    (no error path — undefined vars read as 0 via `rsScalar` default,
    SSub saturates at 0 rather than going negative).  Matches the
    `rsScalar : String → Nat` default-0 behaviour in `RustState`.

    Intended use. This is the scalar semantics of `RustExec`: arithmetic over
    unbounded naturals with saturating subtraction. It is the referent for Rust
    `saturating_sub` (the hax front lowers `scalar#Sub` and `min` to `SSub`), for
    loop counters and array indices, and for values that stay below `2^64`. It is
    not the referent for a wrapping kernel: `SAdd`, `SMul` and `SShl` do not wrap,
    and on overflowing inputs the value differs from both the hardware (mod 2^64)
    and Rust `u64` (wrap or panic). The wrapping referent is `SExpr.evalBV`, used
    by `semScalar`.

    Bridges to `SExpr.evalBV`, each with its in-range hypothesis:
    `SExpr.evalBV_eq_ofNat_eval` and `SExpr.toNat_evalBV_of_inRange` (under
    `SExpr.inRange σ e`); `SExpr.evalStateBV_eq_ofNat_evalState` (under
    `SExpr.inRangeState`). -/
def SExpr.eval (σ : String → Nat) : SExpr → Nat
  | .SVar x   => σ x
  | .SLit n   => n
  | .SAdd a b => a.eval σ + b.eval σ
  | .SSub a b => a.eval σ - b.eval σ
  | .SMul a b => a.eval σ * b.eval σ
  | .SShr a b => a.eval σ >>> b.eval σ
  | .SShl a b => a.eval σ <<< b.eval σ
  | .SAnd a b => a.eval σ &&& b.eval σ
  | .SXor a b => a.eval σ ^^^ b.eval σ
  | .SLt  a b => if a.eval σ < b.eval σ then 1 else 0
  -- Signed-arith extension: two's-complement-faithful semantics via
  -- `BitVec 64`.  `SAsr` interprets its operand as a signed int64 and
  -- shifts right with sign replication (matches Jasmin `>>s`); `SMulS`
  -- multiplies as signed int64 and re-wraps mod 2^64.
  | .SAsr a b =>
      sexprOfSignedInt64 (sexprToSignedInt64 (a.eval σ) >>> (b.eval σ : Nat))
  | .SMulS a b =>
      sexprOfSignedInt64 (sexprToSignedInt64 (a.eval σ) * sexprToSignedInt64 (b.eval σ))
  -- Widening-multiply extension: the high word of the 128-bit product.
  | .SMulHiU a b => sexprMulHiU (a.eval σ) (b.eval σ)
  | .SMulHiS a b => sexprMulHiS (a.eval σ) (b.eval σ)
  -- Tower-limb read extension: `SLimb` reads the tower heap, which the
  -- scalar environment `σ : String → Nat` does not carry.  The scalar `eval`
  -- therefore returns a SAFE DEFAULT of `0` — the faithful value lives in
  -- `SExpr.evalState` (`LowCTExec`).  This arm keeps `eval` total and exhaustive
  -- WITHOUT changing its signature (other emit modules depend on it).
  | .SLimb _ _ => 0

/-! ### Wrapping-`u64` reconciliation

`SExpr.eval` (above) evaluates over **unbounded `Nat`**.  The jasmin / x86
target, by contrast, stores every scalar as a `u64` and wraps every
intermediate arithmetic operation **mod 2^64** (two's-complement).  On
overflowing inputs the two can disagree — e.g. `SAdd (SLit (2^63)) (SLit (2^63))`
is `2^64` in the Nat model but `0` on the hardware.  Leaving this implicit
would silently assume `Nat = u64`, a soundness gap in the emit-correctness
chain.

`SExpr.evalBV` is the **wrapping-`u64`-faithful** evaluator: every node does the
corresponding `Nat` operation and immediately truncates to a `BitVec 64` (i.e.
reduces mod `2^64`), exactly mirroring the hardware.  It is the
storage-truncation image of `eval` made *intermediate-faithful*.  Note the
signed / widening arms (`SAsr`, `SMulS`, `SMulHi{U,S}`) already produce an
in-`u64`-range value in `eval` (via `sexprOfSignedInt64` / `% 2^64`), so their
`evalBV` arm is the literal truncation of that same value — they are
wrapping-faithful; only the plain `Nat`-arithmetic arms (`SAdd`,
`SSub`, `SMul`, `SShl`, `SShr`, `SLt`, `SAnd`, `SXor`) need reconciling.

The bridge to the Nat model is `SExpr.evalBV_eq_ofNat_eval` below: under the
explicit in-range side-condition `SExpr.inRange` the wrapping evaluator equals
`BitVec.ofNat 64 (eval …)`, i.e. *no wrap actually occurs* and the Nat model is
sound for the hardware on those inputs. -/

/-- Evaluate an `SExpr` over 64-bit words, wrapping at the width at every node.

    Intended use. This is the scalar semantics of `semScalar` and the referent for
    wrapping kernels (modular additions, rotations, `wrapping_*` operations): its
    value on every input is the value the emitted code computes. `SExpr.eval`, the
    `RustExec` semantics, agrees with it on in-range inputs only; the bridges are
    `SExpr.evalBV_eq_ofNat_eval` (under `SExpr.inRange`) and
    `SExpr.evalStateBV_eq_ofNat_evalState` (under `SExpr.inRangeState`). `SSub`
    wraps here and saturates in `SExpr.eval`; the two agree on `SSub a b` only when
    `b ≤ a`. -/
def SExpr.evalBV (β : String → BitVec 64) : SExpr → BitVec 64
  | .SVar x   => β x
  | .SLit n   => BitVec.ofNat 64 n
  | .SAdd a b => a.evalBV β + b.evalBV β
  | .SSub a b => a.evalBV β - b.evalBV β
  | .SMul a b => a.evalBV β * b.evalBV β
  | .SShr a b => (a.evalBV β) >>> (b.evalBV β).toNat
  | .SShl a b => (a.evalBV β) <<< (b.evalBV β).toNat
  | .SAnd a b => a.evalBV β &&& b.evalBV β
  | .SXor a b => a.evalBV β ^^^ b.evalBV β
  | .SLt  a b => if (a.evalBV β).toNat < (b.evalBV β).toNat then 1 else 0
  | .SAsr a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64 (sexprToSignedInt64 (a.evalBV β).toNat >>> ((b.evalBV β).toNat : Nat)))
  | .SMulS a b =>
      BitVec.ofNat 64
        (sexprOfSignedInt64 (sexprToSignedInt64 (a.evalBV β).toNat * sexprToSignedInt64 (b.evalBV β).toNat))
  | .SMulHiU a b => BitVec.ofNat 64 (sexprMulHiU (a.evalBV β).toNat (b.evalBV β).toNat)
  | .SMulHiS a b => BitVec.ofNat 64 (sexprMulHiS (a.evalBV β).toNat (b.evalBV β).toNat)
  | .SLimb _ _ => 0

/-- In-range side-condition for the Nat-model `eval` to agree with the
    wrapping-`u64` hardware `evalBV` on a given scalar environment `σ`.

    The bitwise arms (`SAnd`, `SXor`) and the signed/widening arms wrap
    homomorphically and need **no** condition; the conditions that actually
    matter are:

    * `SSub a b` — the Nat model **saturates** at `0` while hardware **wraps**;
      they agree exactly when there is no underflow (`b ≤ a`).
    * `SShr` / `SShl` / `SLt` — the operand(s) must be representable in `u64`
      (`< 2^64`) and the shift amount `< 64`, so that the `Nat` shift/compare
      coincides with the 64-bit one.
    * Every additive / multiplicative node must itself land back in `u64`
      range so that the *outer* truncation is the identity at the Nat level —
      this is what "no wrap occurs" means.

    When `inRange σ e` holds, `eval σ e < 2^64` and the Nat model is sound for
    the hardware (`evalBV_eq_ofNat_eval` + `eval_lt_of_inRange`). -/
def SExpr.inRange (σ : String → Nat) : SExpr → Prop
  | .SVar x   => σ x < 2 ^ 64
  | .SLit n   => n < 2 ^ 64
  | .SAdd a b => a.inRange σ ∧ b.inRange σ ∧ a.eval σ + b.eval σ < 2 ^ 64
  | .SSub a b => a.inRange σ ∧ b.inRange σ ∧ b.eval σ ≤ a.eval σ
  | .SMul a b => a.inRange σ ∧ b.inRange σ ∧ a.eval σ * b.eval σ < 2 ^ 64
  | .SShr a b => a.inRange σ ∧ b.inRange σ ∧ b.eval σ < 64
  | .SShl a b => a.inRange σ ∧ b.inRange σ ∧ b.eval σ < 64 ∧ a.eval σ <<< b.eval σ < 2 ^ 64
  | .SAnd a b => a.inRange σ ∧ b.inRange σ
  | .SXor a b => a.inRange σ ∧ b.inRange σ
  | .SLt  a b => a.inRange σ ∧ b.inRange σ
  | .SAsr a b => a.inRange σ ∧ b.inRange σ
  | .SMulS a b => a.inRange σ ∧ b.inRange σ
  | .SMulHiU a b => a.inRange σ ∧ b.inRange σ
  | .SMulHiS a b => a.inRange σ ∧ b.inRange σ
  | .SLimb _ _ => True

/-- `sexprOfSignedInt64` always lands in `u64` range: it is the `toNat` of a
    `BitVec 64`. -/
theorem sexprOfSignedInt64_lt (z : Int) : sexprOfSignedInt64 z < 2 ^ 64 := by
  unfold sexprOfSignedInt64
  exact (BitVec.ofInt 64 z).isLt

/-- `sexprMulHiU` always lands in `u64` range. -/
theorem sexprMulHiU_lt (a b : Nat) : sexprMulHiU a b < 2 ^ 64 := by
  unfold sexprMulHiU
  have ha : a % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  have hb : b % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  calc (a % 2 ^ 64 * (b % 2 ^ 64)) >>> 64
      = (a % 2 ^ 64 * (b % 2 ^ 64)) / 2 ^ 64 := by
        simp [Nat.shiftRight_eq_div_pow]
    _ < 2 ^ 64 := by
        apply Nat.div_lt_of_lt_mul
        calc a % 2 ^ 64 * (b % 2 ^ 64) < 2 ^ 64 * 2 ^ 64 :=
              Nat.mul_lt_mul'' ha hb
          _ = 2 ^ 64 * 2 ^ 64 := rfl

/-- `sexprMulHiS` always lands in `u64` range (it is a `sexprOfSignedInt64`). -/
theorem sexprMulHiS_lt (a b : Nat) : sexprMulHiS a b < 2 ^ 64 := by
  unfold sexprMulHiS
  exact sexprOfSignedInt64_lt _

/-- Under `inRange`, the Nat-model value is representable in `u64`: no overflow
    happens, so the model agrees with the truncated/wrapped storage form. -/
theorem SExpr.eval_lt_of_inRange (σ : String → Nat) :
    ∀ e : SExpr, e.inRange σ → e.eval σ < 2 ^ 64 := by
  intro e
  induction e with
  | SVar x => intro h; exact h
  | SLit n => intro h; exact h
  | SAdd a b _ _ => intro h; exact h.2.2
  | SSub a b iha _ => intro h; exact lt_of_le_of_lt (Nat.sub_le _ _) (iha h.1)
  | SMul a b _ _ => intro h; exact h.2.2
  | SShr a b iha _ =>
      intro h
      exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (iha h.1)
  | SShl a b _ _ => intro h; exact h.2.2.2
  | SAnd a b iha ihb =>
      intro h
      exact lt_of_le_of_lt (Nat.and_le_left) (iha h.1)
  | SXor a b iha ihb =>
      intro h
      have := Nat.xor_lt_two_pow (n := 64) (lt_of_lt_of_le (iha h.1) (le_refl _))
        (lt_of_lt_of_le (ihb h.2) (le_refl _))
      exact this
  | SLt a b _ _ =>
      intro _; simp only [SExpr.eval]; split <;> norm_num
  | SAsr a b _ _ => intro _; exact sexprOfSignedInt64_lt _
  | SMulS a b _ _ => intro _; exact sexprOfSignedInt64_lt _
  | SMulHiU a b _ _ => intro _; exact sexprMulHiU_lt _ _
  | SMulHiS a b _ _ => intro _; exact sexprMulHiS_lt _ _
  | SLimb v i => intro _; positivity

/-- Lift a scalar environment `σ : String → Nat` to the wrapping-`u64`
    environment `String → BitVec 64` that the hardware sees. -/
def SExpr.liftEnv (σ : String → Nat) : String → BitVec 64 :=
  fun x => BitVec.ofNat 64 (σ x)

/-- **Wrapping-`u64` ⇔ Nat-model bridge (`.toNat` form).**
    Under the in-range side-condition `inRange σ e`, the `Nat` read back out of
    the wrapping-`u64` evaluator equals the Nat-model value: i.e. **no wrap
    occurs**, so `SExpr.eval` faithfully predicts the hardware result.  This is
    the formal statement that the Nat model is sound w.r.t. overflow precisely
    on the inputs the side-condition allows. -/
theorem SExpr.toNat_evalBV_of_inRange (σ : String → Nat) :
    ∀ e : SExpr, e.inRange σ →
      (e.evalBV (SExpr.liftEnv σ)).toNat = e.eval σ := by
  intro e
  induction e with
  | SVar x =>
      intro h
      simp only [SExpr.evalBV, SExpr.liftEnv, SExpr.eval, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h
  | SLit n =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h
  | SAdd a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_add, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2
  | SSub a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_sub, iha h.1, ihb h.2.1]
      have hba : eval σ b ≤ eval σ a := h.2.2
      have hlt : eval σ a < 2 ^ 64 := SExpr.eval_lt_of_inRange σ a h.1
      have heq : 2 ^ 64 - eval σ b + eval σ a = 2 ^ 64 + (eval σ a - eval σ b) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  | SMul a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_mul, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2
  | SShr a b iha ihb =>
      intro h
      rw [SExpr.evalBV, SExpr.eval, BitVec.toNat_ushiftRight, iha h.1, ihb h.2.1]
  | SShl a b iha ihb =>
      intro h
      rw [SExpr.evalBV, SExpr.eval, BitVec.toNat_shiftLeft, iha h.1, ihb h.2.1]
      exact Nat.mod_eq_of_lt h.2.2.2
  | SAnd a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_and, iha h.1, ihb h.2]
  | SXor a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_xor, iha h.1, ihb h.2]
  | SLt a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, iha h.1, ihb h.2]
      split <;> simp
  | SAsr a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprOfSignedInt64_lt _)
  | SMulS a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprOfSignedInt64_lt _)
  | SMulHiU a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprMulHiU_lt _ _)
  | SMulHiS a b iha ihb =>
      intro h
      simp only [SExpr.evalBV, SExpr.eval, BitVec.toNat_ofNat, iha h.1, ihb h.2]
      exact Nat.mod_eq_of_lt (sexprMulHiS_lt _ _)
  | SLimb v i =>
      intro _
      simp [SExpr.evalBV, SExpr.eval]

/-- **Wrapping-`u64` ⇔ Nat-model bridge (`BitVec` form).**  The direct
    corollary: on in-range inputs the wrapping evaluator *is* the truncation of
    the Nat model.  Combined with `eval_lt_of_inRange` this says the
    emit-correctness chain — which stores `BitVec.ofNat 64 (eval …)` — agrees
    with the hardware that wraps at every step.  No silent `Nat = u64`
    assumption remains. -/
theorem SExpr.evalBV_eq_ofNat_eval (σ : String → Nat) (e : SExpr)
    (h : e.inRange σ) :
    e.evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 (e.eval σ) := by
  apply BitVec.eq_of_toNat_eq
  rw [SExpr.toNat_evalBV_of_inRange σ e h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (SExpr.eval_lt_of_inRange σ e h)]

/-- Render an `SExpr` as Rust source.  Parenthesises every binary
    operation conservatively. -/
def SExpr.ppRust : SExpr → String
  | .SVar x   => x
  | .SLit n   => toString n ++ "u64"
  | .SAdd a b => "(" ++ a.ppRust ++ " + " ++ b.ppRust ++ ")"
  | .SSub a b => "(" ++ a.ppRust ++ ".saturating_sub(" ++ b.ppRust ++ "))"
  | .SMul a b => "(" ++ a.ppRust ++ " * " ++ b.ppRust ++ ")"
  | .SShr a b => "(" ++ a.ppRust ++ " >> " ++ b.ppRust ++ ")"
  | .SShl a b => "(" ++ a.ppRust ++ " << " ++ b.ppRust ++ ")"
  | .SAnd a b => "(" ++ a.ppRust ++ " & " ++ b.ppRust ++ ")"
  | .SXor a b => "(" ++ a.ppRust ++ " ^ " ++ b.ppRust ++ ")"
  | .SLt  a b => "(if " ++ a.ppRust ++ " < " ++ b.ppRust ++ " { 1u64 } else { 0u64 })"
  -- Signed-arith extension: cast through i64 for the signed operation,
  -- then back to u64 (the storage form), matching `SExpr.eval`'s BitVec model.
  | .SAsr a b =>
      "(((" ++ a.ppRust ++ " as i64) >> " ++ b.ppRust ++ ") as u64)"
  | .SMulS a b =>
      "(((" ++ a.ppRust ++ " as i64).wrapping_mul(" ++ b.ppRust ++ " as i64)) as u64)"
  -- Widening-multiply extension: widen to (u/i)128, multiply, take the
  -- high 64 bits via `>> 64`, narrow back to u64 — matches `SExpr.eval`'s
  -- `sexprMulHi{U,S}` model.
  | .SMulHiU a b =>
      "(((((" ++ a.ppRust ++ " as u128) * (" ++ b.ppRust ++ " as u128)) >> 64) as u64))"
  | .SMulHiS a b =>
      "(((((" ++ a.ppRust ++ " as i64 as i128) * (" ++ b.ppRust ++
        " as i64 as i128)) >> 64) as u64))"
  -- Tower-limb read extension: limb `i` of the tower slot `v` is the
  -- `v.limbs[i]` field access in Rust surface source.
  | .SLimb v i => v ++ ".limbs[" ++ toString i ++ "]"

/-- Render an `SExpr` as **Jasmin surface source**.  Sibling of `ppRust`,
    used by the `.jazz` direct emit path (`RustEmitJazz.lean`).

    Jasmin's surface syntax differs from Rust's on a few points:

    * Integer literals are unsuffixed (`0`, `1`, `255`) — Jasmin has no
      `u64` / `u32` literal suffix in expression position.
    * Subtraction is the plain `-` operator with wrap-around semantics
      on `u64`/`u32` — there is no `.saturating_sub(...)` method.  For
      callers of `RScalarSetExpr` whose precondition guarantees the
      subtraction does not underflow (e.g. `ctr > 0` before `ctr - 1`),
      wrap-around `-` coincides with saturating subtraction; otherwise
      a runtime guard is the caller's responsibility.
    * The binops `+ - * >> & ^ |` are syntactically the same in both
      surfaces.
    * Variable names are passed through unchanged.
    * `SLt` lowers to a conditional `if … else …` block — Jasmin uses
      the same `if (cond) { a } else { b }` form in expression position
      via the surface preprocessor, so we keep the Rust-style braces. -/
def SExpr.ppJazz : SExpr → String
  | .SVar x   => x
  | .SLit n   => toString n
  | .SAdd a b => "(" ++ a.ppJazz ++ " + " ++ b.ppJazz ++ ")"
  | .SSub a b => "(" ++ a.ppJazz ++ " - " ++ b.ppJazz ++ ")"
  | .SMul a b => "(" ++ a.ppJazz ++ " * " ++ b.ppJazz ++ ")"
  | .SShr a b => "(" ++ a.ppJazz ++ " >> " ++ b.ppJazz ++ ")"
  | .SShl a b => "(" ++ a.ppJazz ++ " << " ++ b.ppJazz ++ ")"
  | .SAnd a b => "(" ++ a.ppJazz ++ " & " ++ b.ppJazz ++ ")"
  | .SXor a b => "(" ++ a.ppJazz ++ " ^ " ++ b.ppJazz ++ ")"
  | .SLt  a b => "(if (" ++ a.ppJazz ++ " < " ++ b.ppJazz ++ ") { 1 } else { 0 })"
  -- Signed-arith extension: Jasmin's `>>s` is the arithmetic
  -- (sign-preserving) shift right; signed `*` shares the `*` token (the low
  -- word is sign-agnostic).  Jasmin infers signedness from the `>>s` operator
  -- and from declared reg types, so no explicit cast token is needed here.
  | .SAsr a b => "(" ++ a.ppJazz ++ " >>s " ++ b.ppJazz ++ ")"
  | .SMulS a b => "(" ++ a.ppJazz ++ " * " ++ b.ppJazz ++ ")"
  -- Widening-multiply extension: the high word of a 64×64→128 product
  -- is NOT a Jasmin infix expression — it is the multi-output intrinsic
  -- `#MULX` / `#IMUL` (lowered as a `Copn` by `LowCTToJasmin`'s dedicated
  -- `RScalarSetExpr` arm).  This surface-string path is the text emitter,
  -- which never receives a top-level high-mul; the two arms below print
  -- parenthesised intrinsic calls so that `ppJazz` is total.
  | .SMulHiU a b => "#MULX_hi(" ++ a.ppJazz ++ ", " ++ b.ppJazz ++ ")"
  | .SMulHiS a b => "#IMUL_hi(" ++ a.ppJazz ++ ", " ++ b.ppJazz ++ ")"
  -- Tower-limb read extension: limb `i` of the tower slot `v` is the
  -- array access `v[i]` in Jasmin surface source (the slot is a `reg u64[N]`).
  | .SLimb v i => v ++ "[" ++ toString i ++ "]"

/-- Convenience: build the `SExpr` expression `<var> - 1`.  Used by the
    parameterless `RWhileNz` countdown idiom — the loop counter is
    decremented at the end of each iteration via
    `RScalarSetExpr "ctr" (SExpr.subOne "ctr")`. -/
def SExpr.subOne (x : String) : SExpr :=
  .SSub (.SVar x) (.SLit 1)

end CatCrypt.Crypto.Jasmin.LowCT
