/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.SExprSigned
public import CatCrypt.Crypto.Jasmin.LowCTSyntax

/-!
# Signed word operations of the hax front computed in the scalar heap

A value of Rust `i32` or `i64` is held in a `u64` slot as its 64-bit two's complement
`BitVec.ofInt 64 z`, and an `i32` value sign-extended.  The width-tagged signed calls of
hax (`wrapping_add#i32`, `Shr#i64`, `cast#i32`, …) have scalar expressions over the
operations `lowerSExpr` lowers (`SExprSigned`), read in the wrapping semantics
`SExpr.evalBV`:

* the wrapping addition, subtraction and multiplication and the left shift of `i<w>` as
  the `u64` operation followed by sign extension from `w` bits (`sextSExpr`); the
  arithmetic right shift as `asrSExpr`, which keeps a sign-extended value sign-extended;
  the checked addition, subtraction and multiplication `Add#i<w>`, `Sub#i<w>`, `Mul#i<w>`
  as the wrapping ones, whose value is the checked one where Rust does not panic
  (`SignedOp.sexpr`);
* the conversions `cast#i<w>` as sign extension from `w` bits, and the conversions
  `cast#u32`, `cast#u64`, `cast#usize` of a signed value as its low bits
  (`signedUnSExpr`);
* the comparisons `Lt`, `Gt`, `Le`, `Ge` of two signed values through `sltSExpr`
  (`SignedCmp.sexpr`).

`scalarizeSignedIn W I` lowers the bindings of these calls to scalar assignments,
tracking the names `W` known to hold a value in a `u64` slot and the names `I` known to
hold a signed value.  A conversion is lowered only on a name of `W` (its source type is
not in its name, and a `u128` or `i128` value is not held in a `u64` slot), and a
comparison only on two names of `I` (on unsigned words the signed comparison differs).
The pass runs after `scalarizeNarrowOps` and `scalarizeWordOps`, whose lowered bindings
are `RLetU64Zero` bindings.

## Main definitions

* `SignedOp`, `SignedOp.int`, `signedOpOf`, `SignedOp.sexpr` — the signed two-operand
  operations, their integer meaning, their call names and their scalar expressions.
* `signedCastOf`, `residueCastOf`, `signedUnSExpr` — the conversions.
* `SignedCmp`, `signedCmpOf`, `SignedCmp.bool`, `SignedCmp.sexpr` — the comparisons.
* `signedLetIn`, `bindsInt`, `bindsSigned`, `scalarizeSignedIn`, `scalarizeSignedOps` —
  the lowering pass.

## Main results

* `SignedOp.int_range` — the value of a signed operation lies in `[-2^63, 2^63)`.
* `bmod_self_of_range` — a value of `i32` or `i64` is its own residue.
* `SignedOp.sexpr_evalBV` — the scalar expression of a signed operation on the two's
  complements of two integers evaluates to the two's complement of the operation's value.
* `evalBV_signedCast`, `toNat_residueCast` — the same for the conversions.
* `SignedCmp.sexpr_evalBV` — a comparison evaluates to `1` or `0` as the integer
  comparison.
* `signedLetIn_op`, `signedLetIn_cast`, `signedLetIn_residue`, `signedLetIn_cmp` — the
  lowering of a binding is the scalar assignment the step lemmas of
  `HaxToLowCTSignedOpsSim` are stated on.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.Ascent (sextSExpr asrSExpr sltSExpr
  evalBV_sextSExpr_ofInt evalBV_asrSExpr sshiftRight_ofInt evalBV_sltSExpr slt_ofInt
  ofInt_sub ofInt_shiftLeft toNat_ofInt_and_mask)

/-! ### Signed operations -/

/-- The two-operand operations of `i32` and `i64` code: the wrapping operations, the
    shifts, and the checked operations `addC`, `subC`, `mulC` of the Rust operators
    `+`, `-`, `*`. -/
inductive SignedOp where
  | add | sub | mul | shl | shr | addC | subC | mulC
  deriving DecidableEq, Repr

/-- The integer value of a signed operation at width `w`: the wrapping sum, difference
    and product in `[-2^(w-1), 2^(w-1))` (`Int.bmod`); the left shift and the arithmetic
    right shift of an operand of `i<w>` by an amount in `[0, w)`; the checked sum,
    difference and product of two operands of `i<w>` when it lies in `i<w>`; `none`
    otherwise (the arms of `Hax.hax64Builtins`, where Rust panics). -/
def SignedOp.int (w : Nat) : SignedOp → Int → Int → Option Int
  | .add, a, b => some ((a + b).bmod (2 ^ w))
  | .sub, a, b => some ((a - b).bmod (2 ^ w))
  | .mul, a, b => some ((a * b).bmod (2 ^ w))
  | .shl, a, b =>
      if -2 ^ (w - 1) ≤ a ∧ a < 2 ^ (w - 1) ∧ 0 ≤ b ∧ b < w then
        some ((a * 2 ^ b.toNat).bmod (2 ^ w))
      else none
  | .shr, a, b =>
      if -2 ^ (w - 1) ≤ a ∧ a < 2 ^ (w - 1) ∧ 0 ≤ b ∧ b < w then some (a >>> b.toNat)
      else none
  | .addC, a, b =>
      if -2 ^ (w - 1) ≤ a ∧ a < 2 ^ (w - 1) ∧ -2 ^ (w - 1) ≤ b ∧ b < 2 ^ (w - 1) ∧
          -2 ^ (w - 1) ≤ a + b ∧ a + b < 2 ^ (w - 1) then some (a + b)
      else none
  | .subC, a, b =>
      if -2 ^ (w - 1) ≤ a ∧ a < 2 ^ (w - 1) ∧ -2 ^ (w - 1) ≤ b ∧ b < 2 ^ (w - 1) ∧
          -2 ^ (w - 1) ≤ a - b ∧ a - b < 2 ^ (w - 1) then some (a - b)
      else none
  | .mulC, a, b =>
      if -2 ^ (w - 1) ≤ a ∧ a < 2 ^ (w - 1) ∧ -2 ^ (w - 1) ≤ b ∧ b < 2 ^ (w - 1) ∧
          -2 ^ (w - 1) ≤ a * b ∧ a * b < 2 ^ (w - 1) then some (a * b)
      else none

/-- The width and operation of a width-tagged signed call of `i32` or `i64` (`isize`
    `64` bits wide). -/
def signedOpOf : String → Option (Nat × SignedOp)
  | "wrapping_add#i32" => some (32, .add)
  | "wrapping_add#i64" => some (64, .add)
  | "wrapping_sub#i32" => some (32, .sub)
  | "wrapping_sub#i64" => some (64, .sub)
  | "wrapping_mul#i32" => some (32, .mul)
  | "wrapping_mul#i64" => some (64, .mul)
  | "Shl#i32" => some (32, .shl)
  | "Shl#i64" => some (64, .shl)
  | "Shr#i32" => some (32, .shr)
  | "Shr#i64" => some (64, .shr)
  | "Add#i32" => some (32, .addC)
  | "Add#i64" => some (64, .addC)
  | "Add#isize" => some (64, .addC)
  | "Sub#i32" => some (32, .subC)
  | "Sub#i64" => some (64, .subC)
  | "Sub#isize" => some (64, .subC)
  | "Mul#i32" => some (32, .mulC)
  | "Mul#i64" => some (64, .mulC)
  | "Mul#isize" => some (64, .mulC)
  | _ => none

/-- The widths of the signed calls are `32` and `64`. -/
theorem signedOpOf_width {f : String} {w : Nat} {op : SignedOp}
    (h : signedOpOf f = some (w, op)) : w = 32 ∨ w = 64 := by
  unfold signedOpOf at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;> omega

/-- The scalar expression of a signed operation at width `w` on the operands `a` and
    `b`. -/
def SignedOp.sexpr (w : Nat) : SignedOp → SExpr → SExpr → SExpr
  | .add, a, b => sextSExpr w (.SAdd a b)
  | .sub, a, b => sextSExpr w (.SSub a b)
  | .mul, a, b => sextSExpr w (.SMul a b)
  | .shl, a, b => sextSExpr w (.SShl a b)
  | .shr, a, b => asrSExpr a b
  | .addC, a, b => sextSExpr w (.SAdd a b)
  | .subC, a, b => sextSExpr w (.SSub a b)
  | .mulC, a, b => sextSExpr w (.SMul a b)

/-- The residue of an integer modulo `2^w` in `[-2^(w-1), 2^(w-1))` lies in
    `[-2^63, 2^63)` for `w ≤ 64`. -/
theorem bmod_range (z : Int) {w : Nat} (hw0 : 0 < w) (hw : w ≤ 64) :
    -2 ^ 63 ≤ z.bmod (2 ^ w) ∧ z.bmod (2 ^ w) < 2 ^ 63 := by
  have h1 := @Int.le_bmod z (2 ^ w) (by positivity)
  have h2 := @Int.bmod_lt z (2 ^ w) (by positivity)
  have hp : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have hq : ((2 ^ w : Nat) : Int) / 2 ≤ 2 ^ 63 := by
    have : ((2 ^ w : Nat) : Int) ≤ 2 ^ 64 := by exact_mod_cast hp
    omega
  have hq' : (((2 ^ w : Nat) : Int) + 1) / 2 ≤ 2 ^ 63 := by
    have : ((2 ^ w : Nat) : Int) ≤ 2 ^ 64 := by exact_mod_cast hp
    have : (2 : Int) ∣ ((2 ^ w : Nat) : Int) := by
      obtain ⟨k, hk⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
      subst hk
      exact ⟨((2 ^ k : Nat) : Int), by push_cast; ring⟩
    omega
  push_cast at h1 h2 hq hq'
  omega

/-- The value of a signed operation at width `32` or `64` lies in `[-2^63, 2^63)`. -/
theorem SignedOp.int_range {w : Nat} (hw : w = 32 ∨ w = 64) (op : SignedOp) {a b r : Int}
    (hr : op.int w a b = some r) : -2 ^ 63 ≤ r ∧ r < 2 ^ 63 := by
  have hw0 : 0 < w := by omega
  have hw64 : w ≤ 64 := by omega
  cases op <;> simp only [SignedOp.int] at hr
  case add | sub | mul => cases hr; exact bmod_range _ hw0 hw64
  case shl =>
    split at hr
    · cases hr; exact bmod_range _ hw0 hw64
    · cases hr
  case shr =>
    split at hr
    · rename_i hc
      cases hr
      have hp : (0 : Int) < 2 ^ b.toNat := by positivity
      have hs : a >>> b.toNat = a / 2 ^ b.toNat := Int.shiftRight_eq_div_pow a b.toNat
      have hwp : (2 : Int) ^ (w - 1) ≤ 2 ^ 63 := pow_le_pow_right₀ (by decide) (by omega)
      rw [hs]
      constructor
      · rw [Int.le_ediv_iff_mul_le hp]
        have : (1 : Int) ≤ 2 ^ b.toNat := by omega
        nlinarith [hc.1]
      · by_cases ha0 : a < 0
        · have : a / 2 ^ b.toNat ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg (by omega) hp
          omega
        · have := Int.ediv_le_self (2 ^ b.toNat) (by omega : 0 ≤ a)
          omega
    · cases hr
  case addC | subC | mulC =>
    split at hr
    · rename_i hc
      cases hr
      have hwp : (2 : Int) ^ (w - 1) ≤ 2 ^ 63 := pow_le_pow_right₀ (by decide) (by omega)
      obtain ⟨-, -, -, -, h1, h2⟩ := hc
      exact ⟨by linarith, by linarith⟩
    · cases hr

/-- A value of `i<w>`, `w` of `32` or `64`, is its own residue modulo `2^w` in
    `[-2^(w-1), 2^(w-1))`. -/
theorem bmod_self_of_range {w : Nat} (hw : w = 32 ∨ w = 64) {z : Int} (h1 : -2 ^ (w - 1) ≤ z)
    (h2 : z < 2 ^ (w - 1)) : z.bmod (2 ^ w) = z := by
  rcases hw with rfl | rfl <;>
    exact Int.bmod_eq_of_le (by push_cast; norm_num at h1 ⊢; omega)
      (by push_cast; norm_num at h2 ⊢; omega)

/-- The two's complement of a non-negative amount below `64` reads back as the
    amount. -/
theorem toNat_ofInt_amount {b : Int} (h0 : 0 ≤ b) (h : b < 64) :
    (BitVec.ofInt 64 b).toNat = b.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by push_cast; omega)]

/-- **The scalar expression of a signed operation.** On operands evaluating to the two's
    complements of `za` and `zb`, the scalar expression of a signed operation at width
    `32` or `64` evaluates to the two's complement of the operation's value. -/
theorem SignedOp.sexpr_evalBV {w : Nat} (hw : w = 32 ∨ w = 64) (op : SignedOp)
    (β : String → BitVec 64) {ea eb : SExpr} {za zb r : Int}
    (ha : ea.evalBV β = BitVec.ofInt 64 za) (hb : eb.evalBV β = BitVec.ofInt 64 zb)
    (hr : op.int w za zb = some r) :
    (op.sexpr w ea eb).evalBV β = BitVec.ofInt 64 r := by
  have hw' : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by omega
  cases op <;> simp only [SignedOp.int] at hr
  case add =>
    cases hr
    exact evalBV_sextSExpr_ofInt hw' β (by simp only [SExpr.evalBV, ha, hb, BitVec.ofInt_add])
  case sub =>
    cases hr
    exact evalBV_sextSExpr_ofInt hw' β (by simp only [SExpr.evalBV, ha, hb, ofInt_sub])
  case mul =>
    cases hr
    exact evalBV_sextSExpr_ofInt hw' β (by simp only [SExpr.evalBV, ha, hb, BitVec.ofInt_mul])
  case shl =>
    split at hr
    · rename_i hc
      cases hr
      refine evalBV_sextSExpr_ofInt hw' β ?_
      have hs : SecureCompilation.VIR.shiftMask 64 zb.toNat = zb.toNat :=
        SecureCompilation.VIR.shiftMask_of_lt (by omega)
      simp only [SExpr.evalBV, ha, hb, toNat_ofInt_amount hc.2.2.1 (by omega), hs,
        ofInt_shiftLeft]
    · cases hr
  case shr =>
    split at hr
    · rename_i hc
      cases hr
      have hwp : (2 : Int) ^ (w - 1) ≤ 2 ^ 63 := pow_le_pow_right₀ (by decide) (by omega)
      have hs : SecureCompilation.VIR.shiftMask 64 zb.toNat = zb.toNat :=
        SecureCompilation.VIR.shiftMask_of_lt (by omega)
      simp only [SignedOp.sexpr, evalBV_asrSExpr, ha, hb,
        toNat_ofInt_amount hc.2.2.1 (by omega), hs]
      exact sshiftRight_ofInt (by omega) (by omega) _
    · cases hr
  case addC =>
    split at hr
    · rename_i hc
      cases hr
      rw [← bmod_self_of_range hw hc.2.2.2.2.1 hc.2.2.2.2.2]
      exact evalBV_sextSExpr_ofInt hw' β (by simp only [SExpr.evalBV, ha, hb, BitVec.ofInt_add])
    · cases hr
  case subC =>
    split at hr
    · rename_i hc
      cases hr
      rw [← bmod_self_of_range hw hc.2.2.2.2.1 hc.2.2.2.2.2]
      exact evalBV_sextSExpr_ofInt hw' β (by simp only [SExpr.evalBV, ha, hb, ofInt_sub])
    · cases hr
  case mulC =>
    split at hr
    · rename_i hc
      cases hr
      rw [← bmod_self_of_range hw hc.2.2.2.2.1 hc.2.2.2.2.2]
      exact evalBV_sextSExpr_ofInt hw' β (by simp only [SExpr.evalBV, ha, hb, BitVec.ofInt_mul])
    · cases hr

/-! ### Conversions -/

/-- The width of a conversion to a signed type `i<w>`, `isize` `64` bits wide. -/
def signedCastOf : String → Option Nat
  | "cast#i8" => some 8
  | "cast#i16" => some 16
  | "cast#i32" => some 32
  | "cast#i64" => some 64
  | "cast#isize" => some 64
  | _ => none

/-- The widths of the signed conversions are `8`, `16`, `32` and `64`. -/
theorem signedCastOf_width {f : String} {w : Nat} (h : signedCastOf f = some w) :
    w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
  unfold signedCastOf at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

/-- The width of a conversion to an unsigned type by the residue modulo `2^w`, defined on
    every integer: `cast#u32`, `cast#u64` and `cast#usize`. -/
def residueCastOf : String → Option Nat
  | "cast#u32" => some 32
  | "cast#u64" => some 64
  | "cast#usize" => some 64
  | _ => none

/-- The widths of the residue conversions are `32` and `64`. -/
theorem residueCastOf_width {f : String} {w : Nat} (h : residueCastOf f = some w) :
    w = 32 ∨ w = 64 := by
  unfold residueCastOf at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

/-- The scalar expression of the conversion `f` of the variable `a`, with `W` the names
    known to hold a value in a `u64` slot: a signed conversion to `w` bits is the sign
    extension from `w` bits, a residue conversion the low `w` bits; a name outside `W`
    has none. -/
def signedUnSExpr (W : List String) (f a : String) : Option SExpr :=
  if a ∈ W then
    match signedCastOf f with
    | some w => some (sextSExpr w (.SVar a))
    | none => (residueCastOf f).map fun w => .SAnd (.SVar a) (.SLit (2 ^ w - 1))
  else none

/-- A signed conversion of the two's complement of `z` evaluates to the two's complement
    of `z.bmod (2^w)`. -/
theorem evalBV_signedCast {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) {a : String} {z : Int} (ha : β a = BitVec.ofInt 64 z) :
    (sextSExpr w (.SVar a)).evalBV β = BitVec.ofInt 64 (z.bmod (2 ^ w)) :=
  evalBV_sextSExpr_ofInt hw β (by simp only [SExpr.evalBV, ha])

/-- A residue conversion of the two's complement of `z` evaluates to the residue of `z`
    modulo `2^w`. -/
theorem toNat_residueCast {w : Nat} (hw : w ≤ 64) (β : String → BitVec 64) {a : String}
    {z : Int} (ha : β a = BitVec.ofInt 64 z) :
    ((SExpr.SAnd (.SVar a) (.SLit (2 ^ w - 1))).evalBV β).toNat = (z % 2 ^ w).toNat := by
  simp only [SExpr.evalBV, ha]
  exact toNat_ofInt_and_mask z hw

/-! ### Comparisons -/

/-- The integer comparisons. -/
inductive SignedCmp where
  | lt | gt | le | ge
  deriving DecidableEq, Repr

/-- The comparison of a comparison call. -/
def signedCmpOf : String → Option SignedCmp
  | "Lt" => some .lt
  | "Gt" => some .gt
  | "Le" => some .le
  | "Ge" => some .ge
  | _ => none

/-- The Boolean value of a comparison of two integers. -/
def SignedCmp.bool : SignedCmp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .gt, a, b => decide (b < a)
  | .le, a, b => decide (a ≤ b)
  | .ge, a, b => decide (b ≤ a)

/-- The scalar expression of a signed comparison: `sltSExpr` of the operands in order or
    swapped, complemented in its low bit for `Le` and `Ge`. -/
def SignedCmp.sexpr : SignedCmp → SExpr → SExpr → SExpr
  | .lt, a, b => sltSExpr a b
  | .gt, a, b => sltSExpr b a
  | .le, a, b => .SXor (sltSExpr b a) (.SLit 1)
  | .ge, a, b => .SXor (sltSExpr a b) (.SLit 1)

/-- **The scalar expression of a signed comparison.** On operands evaluating to the two's
    complements of two `i64` values, a comparison evaluates to `1` when the integer
    comparison holds and to `0` otherwise. -/
theorem SignedCmp.sexpr_evalBV (c : SignedCmp) (β : String → BitVec 64) {ea eb : SExpr}
    {za zb : Int} (ha1 : -2 ^ 63 ≤ za) (ha2 : za < 2 ^ 63) (hb1 : -2 ^ 63 ≤ zb)
    (hb2 : zb < 2 ^ 63) (ha : ea.evalBV β = BitVec.ofInt 64 za)
    (hb : eb.evalBV β = BitVec.ofInt 64 zb) :
    (c.sexpr ea eb).evalBV β = if c.bool za zb then 1 else 0 := by
  have hab := slt_ofInt ha1 ha2 hb1 hb2
  have hba := slt_ofInt hb1 hb2 ha1 ha2
  cases c <;> simp only [SignedCmp.sexpr, SignedCmp.bool, SExpr.evalBV, evalBV_sltSExpr, ha, hb,
    hab, hba]
  · rfl
  · rfl
  · by_cases h : zb < za
    · simp [h, show ¬ za ≤ zb by omega]
    · simp [h, show za ≤ zb by omega]
  · by_cases h : za < zb
    · simp [h, show ¬ zb ≤ za by omega]
    · simp [h, show zb ≤ za by omega]

/-! ### The lowering pass -/

/-- The binding `RLetZero x t b` with a first call into `x` lowered to a scalar
    assignment inside `RLetU64Zero x`: a signed operation `f(a, b)` to
    `SignedOp.sexpr`, a comparison `f(a, b)` of two names of `I` to `SignedCmp.sexpr`,
    and a conversion `f(a)` with a scalar expression `signedUnSExpr W f a` to it. -/
def signedLetIn (W I : List String) (x : String) (t : TowerType) : LowCT → LowCT
  | .RSeq (.RCall f dest [a, b]) body =>
      if dest.locVar = x then
        match signedOpOf f with
        | some (w, op) =>
            .RLetU64Zero x
              (.RSeq (.RScalarSetExpr x (op.sexpr w (.SVar a.locVar) (.SVar b.locVar))) body)
        | none =>
          match signedCmpOf f with
          | some c =>
              if a.locVar ∈ I ∧ b.locVar ∈ I then
                .RLetU64Zero x
                  (.RSeq (.RScalarSetExpr x (c.sexpr (.SVar a.locVar) (.SVar b.locVar))) body)
              else .RLetZero x t (.RSeq (.RCall f dest [a, b]) body)
          | none => .RLetZero x t (.RSeq (.RCall f dest [a, b]) body)
      else .RLetZero x t (.RSeq (.RCall f dest [a, b]) body)
  | .RSeq (.RCall f dest [a]) body =>
      match signedUnSExpr W f a.locVar with
      | some se =>
          if dest.locVar = x then .RLetU64Zero x (.RSeq (.RScalarSetExpr x se) body)
          else .RLetZero x t (.RSeq (.RCall f dest [a]) body)
      | none => .RLetZero x t (.RSeq (.RCall f dest [a]) body)
  | b => .RLetZero x t b

/-- Whether the body `b` of a binding of `x` binds `x` to a signed value: its first
    command is a signed operation or a signed conversion into `x`. -/
def bindsSigned (x : String) : LowCT → Bool
  | .RSeq (.RCall f dest _) _ =>
      dest.locVar == x && ((signedOpOf f).isSome || (signedCastOf f).isSome)
  | _ => false

/-- Whether the body `b` of a binding of `x` binds `x` to a value held in a `u64` slot: a
    signed value, a residue conversion, a comparison or an array load into `x`. -/
def bindsInt (x : String) : LowCT → Bool
  | .RSeq (.RCall f dest _) b =>
      bindsSigned x (.RSeq (.RCall f dest []) b) ||
        (dest.locVar == x && ((residueCastOf f).isSome || (signedCmpOf f).isSome))
  | .RSeq (.RArrLoad dest _ _) _ => dest.locVar == x
  | _ => false

/-- The names `N` with `x` added when `c` holds, and removed otherwise. -/
def bindName (N : List String) (x : String) (c : Bool) : List String :=
  if c then x :: N else N.filter (· != x)

/-- The pass lowering every binding of a signed operation, comparison or conversion
    (`signedLetIn`), tracking the names `W` in scope known to hold a value in a `u64`
    slot (bound by `RLetU64Zero`, by a binding of `bindsInt`, and the loop indices) and
    the names `I` known to hold a signed value (bound by a binding of `bindsSigned`).  A
    binding of any other value removes its name from both. -/
def scalarizeSignedIn (W I : List String) : LowCT → LowCT
  | .RLetZero x t b =>
      signedLetIn W I x t
        (scalarizeSignedIn (bindName W x (bindsInt x b)) (bindName I x (bindsSigned x b)) b)
  | .RSeq a b => .RSeq (scalarizeSignedIn W I a) (scalarizeSignedIn W I b)
  | .RLetU64Zero x b => .RLetU64Zero x (scalarizeSignedIn (x :: W) (I.filter (· != x)) b)
  | .RIfNz v t e => .RIfNz v (scalarizeSignedIn W I t) (scalarizeSignedIn W I e)
  | .RWhileNz v b => .RWhileNz v (scalarizeSignedIn W I b)
  | .RFor x n b => .RFor x n (scalarizeSignedIn (x :: W) (I.filter (· != x)) b)
  | .RForRuntime x bound b =>
      .RForRuntime x bound (scalarizeSignedIn (x :: W) (I.filter (· != x)) b)
  | .RBlock b => .RBlock (scalarizeSignedIn W I b)
  | c => c

/-- `scalarizeSignedIn` from the names `S` known to hold signed values in `u64` slots,
    such as the parameters of a signed type. -/
def scalarizeSignedOps (S : List String) : LowCT → LowCT := scalarizeSignedIn S S

/-- A binding of a signed operation into `x` is lowered to the scalar assignment of
    `SignedOp.sexpr`, the shape of `step_signed`. -/
theorem signedLetIn_op {W I : List String} {x f : String} {t : TowerType}
    {dest a b : Located} {body : LowCT} {w : Nat} {op : SignedOp}
    (hf : signedOpOf f = some (w, op)) (hd : dest.locVar = x) :
    signedLetIn W I x t (.RSeq (.RCall f dest [a, b]) body) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (op.sexpr w (.SVar a.locVar) (.SVar b.locVar)))
        body) := by
  simp [signedLetIn, hf, hd]

/-- A binding of a comparison of two names of `I` into `x` is lowered to the scalar
    assignment of `SignedCmp.sexpr`, the shape of `step_signedCmp`. -/
theorem signedLetIn_cmp {W I : List String} {x f : String} {t : TowerType}
    {dest a b : Located} {body : LowCT} {c : SignedCmp} (hf : signedCmpOf f = some c)
    (hd : dest.locVar = x) (ha : a.locVar ∈ I) (hb : b.locVar ∈ I) :
    signedLetIn W I x t (.RSeq (.RCall f dest [a, b]) body) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (c.sexpr (.SVar a.locVar) (.SVar b.locVar)))
        body) := by
  have hn : signedOpOf f = none := by
    unfold signedCmpOf at hf
    split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf <;> rfl
  simp [signedLetIn, hf, hd, hn, ha, hb]

/-- A binding of a signed conversion into `x` of a name of `W` is lowered to the scalar
    assignment of the sign extension, the shape of `step_signedCast`. -/
theorem signedLetIn_cast {W I : List String} {x f : String} {t : TowerType}
    {dest a : Located} {body : LowCT} {w : Nat} (hf : signedCastOf f = some w)
    (ha : a.locVar ∈ W) (hd : dest.locVar = x) :
    signedLetIn W I x t (.RSeq (.RCall f dest [a]) body) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (sextSExpr w (.SVar a.locVar))) body) := by
  simp [signedLetIn, signedUnSExpr, hf, ha, hd]

/-- A binding of a residue conversion into `x` of a name of `W` is lowered to the scalar
    assignment of its low bits, the shape of `step_residueCast`. -/
theorem signedLetIn_residue {W I : List String} {x f : String} {t : TowerType}
    {dest a : Located} {body : LowCT} {w : Nat} (hf : residueCastOf f = some w)
    (ha : a.locVar ∈ W) (hd : dest.locVar = x) :
    signedLetIn W I x t (.RSeq (.RCall f dest [a]) body) =
      .RLetU64Zero x
        (.RSeq (.RScalarSetExpr x (.SAnd (.SVar a.locVar) (.SLit (2 ^ w - 1)))) body) := by
  have hn : signedCastOf f = none := by
    unfold residueCastOf at hf
    split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf <;> rfl
  simp [signedLetIn, signedUnSExpr, hf, hn, ha, hd]

end CatCrypt.Crypto.Hax
