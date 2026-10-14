/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeirSemantics
import all Veir.Interpreter.Basic
import all Veir.Data.LLVM.Int.Basic
import all Veir.IR.Attribute

/-!
# The scalar fragment of `jasminDialect` in VeIR, with bare shifts under `ComShiftSafe`

`ComToVeirSemantics` interprets the lowering of the `arith` fragment (`JasminOp.InArith`)
with VeIR's `Veir.interpretOp'`. The table of expansions
`JasminOp.bridgeExpansion? bare`, defined in `ComToVeir_JasminDialect`, covers the
scalar fragment `JasminOp.InBridge`, with the same semantic theorems. At `bare = false`
it is the table of the `ToVeirOp jasminDialect` instance.

## The table

| `JasminOp` | operations | value on LLVM integers |
|---|---|---|
| `regArith shl w`, `regArith shr w` | `bare = false`: `shiftSelectExpansion`; `bare = true`: one `arith.shli` or `arith.shrui` | `veirShiftSel`; `veirBinInt` |
| `regArith andn w` | constant all ones, `arith.xori`, `arith.andi` | `veirAndn` |
| `shlImm w n`, `shrImm w n` | constant `shiftMask w n` and the shift when it is below `w`; constant `0` otherwise | `veirShlImm`, `veirShrImm` |
| `sarImm w n` | constant `min n (w - 1)` and `arith.shrsi` | `veirSarImm` |
| `rorImm w n` | `arith.shrui` by `n % w`, `arith.shli` by `w - n % w`, `arith.ori`; no operation for `n % w = 0` | `veirRorImm` |
| `castW w w'` | `arith.extui`, `arith.trunci`, or no operation at equal widths | `veirCastW` |
| `mulhi w` | `arith.mului_extended`, second result | `LLVM.Int.umulHigh` |
| `cmp c w`, `cmpImm c w n` | `arith.cmpi`, against the constant `n` for `cmpImm` | `LLVM.Int.icmp` |
| `select w` | `arith.select` | `LLVM.Int.select` |
| `addCarryLo w` | `arith.extui` of the carry, two `arith.addi` | `veirAddCarryLo` |
| `addCarryHi w` | `arith.extui` of the carry, two `arith.addui_extended`, `arith.ori` of the flags | `veirAddCarryHi` |

Every constant shift amount the table emits is below the width, so no immediate shift
or rotate is poison. `andn` complements its first operand, as `JasminBinOp.apply .andn`
does. Memory ops, calls, vector ops and the stack array types stay outside the fragment.

## Main results

* `veirRunComBare_eq`: with `bare = true`, on the scalar fragment and under
  `ComShiftSafe`, the op-by-op VeIR interpretation from the encoded valuation returns
  the encoded denotation.
* `veirRunComBridge_eq_denote`: with `bare = false` the same holds for every shift
  amount.
* `veirRunComWith_bridge_refines`: for both values of `bare` and every shift amount,
  from an environment refined by the encoded valuation the VeIR result is refined by
  the encoded denotation; the total value refines VeIR's value, which may be poison.
* `veirRunBindingWith_bridge_square`: the square of one binding, from which the three
  program theorems follow by induction on the program.
* `veirRunComWith_bridgeExpansion?_false`: the table with `bare = false` is the
  lowering of the `ToVeirOp jasminDialect` instance, so the interpretation under it is
  `veirRunCom`.
* `veirRunCom_bridge_refines`, `veirRunCom_bridge_eq_denote`: the refinement and the
  equation for `veirRunCom`, the interpretation of what the instance emits, on the
  scalar fragment and for every shift amount.
* `veirAndn_val`, `veirShlImm_val`, `veirShrImm_val`, `veirSarImm_val`, `veirRorImm_val`,
  `veirCastW_val`, `umulHigh_val`, `icmp_val`, `select_val`, `veirAddCarryLo_val`,
  `veirAddCarryHi_val`: on defined operands the value of each lowering is the
  denotation of the op; each has a `_refines` form for operands that may be poison.

`bridgeExpansionOf bare` is the expansion argument of the builders `lowerComWfWith`,
`lowerComToFuncAtWf` and `lowerComToModuleWf`; `lowerComBridgeWf` is the first of them
at `jasminDialect`. The theorems here are about the operations of the table run in
order by `Veir.interpretOp'`; they do not read the pointer graph the builder produces.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

open Veir Veir.Data
open CatCrypt.Crypto.SecureCompilation.VIR (Com Expr Ctxt TyDenote DialectSignature)
open Ctxt (Var Valuation)

/-! ## Refinement of LLVM integers by defined values -/

/-- A unary function on LLVM integers that maps `a` to `c`, and poison to a value
refined by `c`, maps every integer refined by `a` to one refined by `c`. -/
theorem llvmInt_refines₁ {w w' : Nat} (f : LLVM.Int w → LLVM.Int w') {a : BitVec w}
    {c : BitVec w'} (hv : f (.val a) = .val c) (hp : f .poison ⊒ .val c) {x : LLVM.Int w}
    (hx : x ⊒ .val a) : f x ⊒ .val c := by
  rcases (llvmInt_isRefinedBy_val_iff x a).1 hx with rfl | rfl
  · exact hp
  · rw [hv]; exact isRefinedBy_refl _

/-- A binary function on LLVM integers that is poison on a poison operand and maps
`a`, `b` to `c` maps integers refined by `a`, `b` to one refined by `c`. -/
theorem llvmInt_refines₂ {w₁ w₂ w' : Nat} (f : LLVM.Int w₁ → LLVM.Int w₂ → LLVM.Int w')
    {a : BitVec w₁} {b : BitVec w₂} {c : BitVec w'} (hv : f (.val a) (.val b) = .val c)
    (hl : ∀ y, f .poison y = .poison) (hr : ∀ x, f x .poison = .poison)
    {x : LLVM.Int w₁} {y : LLVM.Int w₂} (hx : x ⊒ .val a) (hy : y ⊒ .val b) :
    f x y ⊒ .val c := by
  rcases (llvmInt_isRefinedBy_val_iff x a).1 hx with rfl | rfl
  · rw [hl]; exact llvmInt_poison_isRefinedBy _
  rcases (llvmInt_isRefinedBy_val_iff y b).1 hy with rfl | rfl
  · rw [hr]; exact llvmInt_poison_isRefinedBy _
  · rw [hv]; exact isRefinedBy_refl _

/-- A ternary function on LLVM integers that is poison on a poison operand and maps
`a`, `b`, `c` to `d` maps integers refined by `a`, `b`, `c` to one refined by `d`. -/
theorem llvmInt_refines₃ {w₁ w₂ w₃ w' : Nat}
    (f : LLVM.Int w₁ → LLVM.Int w₂ → LLVM.Int w₃ → LLVM.Int w')
    {a : BitVec w₁} {b : BitVec w₂} {c : BitVec w₃} {d : BitVec w'}
    (hv : f (.val a) (.val b) (.val c) = .val d)
    (h₁ : ∀ y z, f .poison y z = .poison) (h₂ : ∀ x z, f x .poison z = .poison)
    (h₃ : ∀ x y, f x y .poison = .poison)
    {x : LLVM.Int w₁} {y : LLVM.Int w₂} {z : LLVM.Int w₃} (hx : x ⊒ .val a) (hy : y ⊒ .val b)
    (hz : z ⊒ .val c) : f x y z ⊒ .val d := by
  rcases (llvmInt_isRefinedBy_val_iff x a).1 hx with rfl | rfl
  · rw [h₁]; exact llvmInt_poison_isRefinedBy _
  rcases (llvmInt_isRefinedBy_val_iff y b).1 hy with rfl | rfl
  · rw [h₂]; exact llvmInt_poison_isRefinedBy _
  rcases (llvmInt_isRefinedBy_val_iff z c).1 hz with rfl | rfl
  · rw [h₃]; exact llvmInt_poison_isRefinedBy _
  · rw [hv]; exact isRefinedBy_refl _

/-! ## Values of the lowered operations on LLVM integers -/

/-- The value of the `andn` expansion: `arith.xori` of the first operand with the
all-ones constant, then `arith.andi` with the second operand. The first operand is
the complemented one, as in `JasminBinOp.apply .andn`. -/
def veirAndn {w : Nat} (x y : LLVM.Int w) : LLVM.Int w :=
  LLVM.Int.and (LLVM.Int.xor x (.val (BitVec.allOnes w))) y

/-- On defined operands the `andn` expansion is `JasminBinOp.apply .andn`. -/
theorem veirAndn_val {w : Nat} (a b : BitVec w) :
    veirAndn (.val a) (.val b) = .val (JasminBinOp.apply .andn a b) := by
  simp [veirAndn, LLVM.Int.and, LLVM.Int.xor, Id.run, JasminBinOp.apply, BitVec.xor_allOnes]

/-- The `andn` expansion is monotone for VeIR's refinement. -/
theorem veirAndn_refines {w : Nat} {x y : LLVM.Int w} {a b : BitVec w} (hx : x ⊒ .val a)
    (hy : y ⊒ .val b) : veirAndn x y ⊒ .val (JasminBinOp.apply .andn a b) :=
  llvmInt_refines₂ veirAndn (veirAndn_val a b) (fun _ => rfl) (fun x => by cases x <;> rfl)
    hx hy

/-- The value of the lowering of `shlImm w n`: `arith.shli` by the constant
`shiftMask w n` when it is below `w`, and the constant `0` otherwise. -/
def veirShlImm (w n : Nat) (x : LLVM.Int w) : LLVM.Int w :=
  if shiftMask w n < w then veirBinInt .shl x (.val (BitVec.ofNat w (shiftMask w n)))
  else .val 0

/-- The value of the lowering of `shrImm w n`: `arith.shrui` by the constant
`shiftMask w n` when it is below `w`, and the constant `0` otherwise. -/
def veirShrImm (w n : Nat) (x : LLVM.Int w) : LLVM.Int w :=
  if shiftMask w n < w then veirBinInt .shr x (.val (BitVec.ofNat w (shiftMask w n)))
  else .val 0

/-- A constant below the width is its own value at that width. -/
theorem toNat_ofNat_of_lt_width {w n : Nat} (h : n < w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h Nat.lt_two_pow_self)

/-- On a defined operand the lowering of `shlImm w n` is `a <<< shiftMask w n`. -/
theorem veirShlImm_val (w n : Nat) (a : BitVec w) :
    veirShlImm w n (.val a) = .val (a <<< shiftMask w n) := by
  unfold veirShlImm
  split
  · rename_i h
    rw [veirBinInt_val .shl (by decide) a _ (fun _ => by rw [toNat_ofNat_of_lt_width h]; exact h)]
    simp only [JasminBinOp.apply, toNat_ofNat_of_lt_width h, shiftMask_shiftMask]
  · rename_i h
    rw [BitVec.shiftLeft_eq_zero (Nat.le_of_not_lt h)]
    rfl

/-- On a defined operand the lowering of `shrImm w n` is `a >>> shiftMask w n`. -/
theorem veirShrImm_val (w n : Nat) (a : BitVec w) :
    veirShrImm w n (.val a) = .val (a >>> shiftMask w n) := by
  unfold veirShrImm
  split
  · rename_i h
    rw [veirBinInt_val .shr (by decide) a _ (fun _ => by rw [toNat_ofNat_of_lt_width h]; exact h)]
    simp only [JasminBinOp.apply, toNat_ofNat_of_lt_width h, shiftMask_shiftMask]
  · rename_i h
    rw [BitVec.ushiftRight_eq_zero (Nat.le_of_not_lt h)]
    rfl

/-- The lowering of `shlImm w n` is monotone for VeIR's refinement. -/
theorem veirShlImm_refines (w n : Nat) {x : LLVM.Int w} {a : BitVec w} (hx : x ⊒ .val a) :
    veirShlImm w n x ⊒ .val (a <<< shiftMask w n) :=
  llvmInt_refines₁ (veirShlImm w n) (veirShlImm_val w n a)
    (by rw [← veirShlImm_val w n a]; unfold veirShlImm; split
        · exact llvmInt_poison_isRefinedBy _
        · exact isRefinedBy_refl _) hx

/-- The lowering of `shrImm w n` is monotone for VeIR's refinement. -/
theorem veirShrImm_refines (w n : Nat) {x : LLVM.Int w} {a : BitVec w} (hx : x ⊒ .val a) :
    veirShrImm w n x ⊒ .val (a >>> shiftMask w n) :=
  llvmInt_refines₁ (veirShrImm w n) (veirShrImm_val w n a)
    (by rw [← veirShrImm_val w n a]; unfold veirShrImm; split
        · exact llvmInt_poison_isRefinedBy _
        · exact isRefinedBy_refl _) hx

/-- The value of the lowering of `sarImm w n`: the operand at width `0`, and
`arith.shrsi` by the constant `min n (w - 1)` otherwise. -/
def veirSarImm (w n : Nat) (x : LLVM.Int w) : LLVM.Int w :=
  if w = 0 then x else LLVM.Int.ashr x (.val (BitVec.ofNat w (min n (w - 1))))

/-- An arithmetic right shift by `n` is the shift by `min n (w - 1)`: every amount
from `w - 1` on fills the word with the sign bit. -/
theorem sshiftRight_min {w : Nat} (a : BitVec w) (n : Nat) :
    a.sshiftRight (min n (w - 1)) = a.sshiftRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight]
  by_cases hn : n ≤ w - 1
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (Nat.le_of_not_le hn)]
    have h1 : ¬ w ≤ i := Nat.not_le.2 hi
    simp only [h1, decide_false, Bool.not_false, Bool.true_and]
    have h2 : ¬ n + i < w := by omega
    simp only [h2, ↓reduceIte]
    by_cases h3 : w - 1 + i < w
    · have : w - 1 + i = w - 1 := by omega
      simp only [this, BitVec.msb_eq_getLsbD_last, ite_self]
    · simp only [h3, ↓reduceIte]

/-- On a defined operand the lowering of `sarImm w n` is `a.sshiftRight n`. -/
theorem veirSarImm_val (w n : Nat) (a : BitVec w) :
    veirSarImm w n (.val a) = .val (a.sshiftRight n) := by
  unfold veirSarImm
  split
  · rename_i h
    subst h
    exact congrArg _ (Subsingleton.elim _ _)
  · rename_i h
    have hm : min n (w - 1) < w := by omega
    have hlt : ¬ w ≤ (BitVec.ofNat w (min n (w - 1))).toNat := by
      rw [toNat_ofNat_of_lt_width hm]; omega
    simp only [LLVM.Int.ashr, Id.run, bitVec_ge_natCast_self_iff, BitVec.sshiftRight_eq',
      toNat_ofNat_of_lt_width hm]
    simp [sshiftRight_min a n]
    omega

/-- The lowering of `sarImm w n` is monotone for VeIR's refinement. -/
theorem veirSarImm_refines (w n : Nat) {x : LLVM.Int w} {a : BitVec w} (hx : x ⊒ .val a) :
    veirSarImm w n x ⊒ .val (a.sshiftRight n) :=
  llvmInt_refines₁ (veirSarImm w n) (veirSarImm_val w n a)
    (by unfold veirSarImm; split <;> exact llvmInt_poison_isRefinedBy _) hx

/-- The value of the lowering of `rorImm w n`: the operand when `w = 0` or
`n % w = 0`, and otherwise `arith.ori` of `arith.shrui` by `n % w` and `arith.shli` by
`w - n % w`, two amounts below the width. -/
def veirRorImm (w n : Nat) (x : LLVM.Int w) : LLVM.Int w :=
  if w = 0 ∨ n % w = 0 then x
  else LLVM.Int.or (veirBinInt .shr x (.val (BitVec.ofNat w (n % w))))
    (veirBinInt .shl x (.val (BitVec.ofNat w (w - n % w))))

/-- On a defined operand the lowering of `rorImm w n` is `a.rotateRight n`. -/
theorem veirRorImm_val (w n : Nat) (a : BitVec w) :
    veirRorImm w n (.val a) = .val (a.rotateRight n) := by
  unfold veirRorImm
  split
  · rename_i h
    rcases h with h | h
    · subst h
      exact congrArg _ (Subsingleton.elim _ _)
    · rw [BitVec.rotateRight_def, h]
      simp
  · rename_i h
    have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => h (Or.inl h0)
    have hr : n % w < w := Nat.mod_lt _ hw
    have hr0 : n % w ≠ 0 := fun h0 => h (Or.inr h0)
    have hl : w - n % w < w := by omega
    rw [veirBinInt_val .shr (by decide) a _ (fun _ => by rw [toNat_ofNat_of_lt_width hr]; exact hr),
      veirBinInt_val .shl (by decide) a _ (fun _ => by rw [toNat_ofNat_of_lt_width hl]; exact hl)]
    simp only [JasminBinOp.apply, toNat_ofNat_of_lt_width hr, toNat_ofNat_of_lt_width hl,
      shiftMask_of_lt hr, shiftMask_of_lt hl, BitVec.rotateRight_def]
    simp [LLVM.Int.or, Id.run]

/-- The lowering of `rorImm w n` is monotone for VeIR's refinement. -/
theorem veirRorImm_refines (w n : Nat) {x : LLVM.Int w} {a : BitVec w} (hx : x ⊒ .val a) :
    veirRorImm w n x ⊒ .val (a.rotateRight n) :=
  llvmInt_refines₁ (veirRorImm w n) (veirRorImm_val w n a)
    (by unfold veirRorImm; split <;> exact llvmInt_poison_isRefinedBy _) hx

/-- On defined operands the high result of `arith.mului_extended` is `mulHiW`. -/
theorem umulHigh_val {w : Nat} (a b : BitVec w) :
    LLVM.Int.umulHigh (.val a) (.val b) = .val (mulHiW a b) := by
  simp only [LLVM.Int.umulHigh, Id.run, mulHiW]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  have hle : 2 ^ w ≤ 2 ^ (w + w) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right w w)
  have hab : a.toNat * b.toNat < 2 ^ (w + w) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul'' ha hb
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hle),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb hle), Nat.mod_eq_of_lt hab, Nat.shiftRight_eq_div_pow]

/-- The high result of `arith.mului_extended` is monotone for VeIR's refinement. -/
theorem umulHigh_refines {w : Nat} {x y : LLVM.Int w} {a b : BitVec w} (hx : x ⊒ .val a)
    (hy : y ⊒ .val b) : LLVM.Int.umulHigh x y ⊒ .val (mulHiW a b) :=
  llvmInt_refines₂ LLVM.Int.umulHigh (umulHigh_val a b) (fun _ => rfl)
    (fun x => by cases x <;> rfl) hx hy

/-- On defined operands `arith.cmpi` with the predicate of `c` is `cmpBit c`. -/
theorem icmp_val {w : Nat} (c : JasminCmp) (a b : BitVec w) :
    LLVM.Int.icmp (.val a) (.val b) c.toIntPred = .val (cmpBit c a b) := by
  have h : ∀ p : Bool, BitVec.ofBool p = if p = true then 1#1 else 0#1 := by decide
  cases c <;> exact congrArg LLVM.Int.val (h _)

/-- `arith.cmpi` is monotone for VeIR's refinement. -/
theorem icmp_refines {w : Nat} (c : JasminCmp) {x y : LLVM.Int w} {a b : BitVec w}
    (hx : x ⊒ .val a) (hy : y ⊒ .val b) :
    LLVM.Int.icmp x y c.toIntPred ⊒ .val (cmpBit c a b) :=
  llvmInt_refines₂ (fun x y => LLVM.Int.icmp x y c.toIntPred) (icmp_val c a b) (fun _ => rfl)
    (fun x => by cases x <;> rfl) hx hy

/-- On defined operands `arith.select` is `selectW`. -/
theorem select_val {w : Nat} (c : BitVec 1) (a b : BitVec w) :
    LLVM.Int.select (.val c) (.val a) (.val b) = .val (selectW c a b) := by
  simp only [LLVM.Int.select, Id.run, selectW, beq_iff_eq]
  split <;> rfl

/-- `arith.select` is monotone for VeIR's refinement: poison in the arm the
condition does not pick does not reach the result. -/
theorem select_refines {w : Nat} {s : LLVM.Int 1} {x y : LLVM.Int w} {c : BitVec 1}
    {a b : BitVec w} (hs : s ⊒ .val c) (hx : x ⊒ .val a) (hy : y ⊒ .val b) :
    LLVM.Int.select s x y ⊒ .val (selectW c a b) := by
  rcases (llvmInt_isRefinedBy_val_iff s c).1 hs with rfl | rfl
  · exact llvmInt_poison_isRefinedBy _
  simp only [LLVM.Int.select, Id.run, selectW, beq_iff_eq]
  split
  · exact hx
  · exact hy

/-- The value of the lowering of `castW w w'`: `arith.extui` when `w < w'`,
`arith.trunci` when `w' < w`, and the operand at equal widths. -/
def veirCastW (w w' : Nat) (x : LLVM.Int w) : LLVM.Int w' :=
  if h : w < w' then LLVM.Int.zext x w' false h
  else if h' : w' < w then LLVM.Int.trunc x w' false false h'
  else x.cast (Nat.le_antisymm (Nat.le_of_not_lt h') (Nat.le_of_not_lt h))

/-- On a defined operand the lowering of `castW w w'` is `a.zeroExtend w'`. -/
theorem veirCastW_val (w w' : Nat) (a : BitVec w) :
    veirCastW w w' (.val a) = .val (a.zeroExtend w') := by
  unfold veirCastW
  split
  · simp [LLVM.Int.zext, Id.run]
  · split
    · simp [LLVM.Int.trunc, Id.run]
    · rename_i h h'
      have hw : w = w' := Nat.le_antisymm (Nat.le_of_not_lt h') (Nat.le_of_not_lt h)
      subst hw
      simp [LLVM.Int.cast]

/-- The lowering of `castW w w'` is monotone for VeIR's refinement. -/
theorem veirCastW_refines (w w' : Nat) {x : LLVM.Int w} {a : BitVec w} (hx : x ⊒ .val a) :
    veirCastW w w' x ⊒ .val (a.zeroExtend w') :=
  llvmInt_refines₁ (veirCastW w w') (veirCastW_val w w' a)
    (by unfold veirCastW; split
        · exact llvmInt_poison_isRefinedBy _
        · split <;> exact llvmInt_poison_isRefinedBy _) hx

/-- The carry-in of a carry-chain add at width `w`, as a `w`-bit LLVM integer:
`arith.extui` for `1 < w`, the operand itself at `w = 1`. Width `0` has no carry
word; the value there is `0`. -/
def veirCarryIn (w : Nat) (c : LLVM.Int 1) : LLVM.Int w :=
  if h : 1 < w then LLVM.Int.zext c w false h
  else if h' : w = 1 then c.cast h'.symm
  else .val 0

/-- The value of the lowering of `addCarryLo w`: `arith.addi` of the two words and
then of the carry-in; at width `0` the one `arith.addi`. -/
def veirAddCarryLo (w : Nat) (x y : LLVM.Int w) (c : LLVM.Int 1) : LLVM.Int w :=
  if w = 0 then LLVM.Int.add x y else LLVM.Int.add (LLVM.Int.add x y) (veirCarryIn w c)

/-- The value of the lowering of `addCarryHi w`: `arith.ori` of the overflow flags
of the two `arith.addui_extended`, the first of the two words and the second of
their sum and the carry-in; at width `0` the carry-in. -/
def veirAddCarryHi (w : Nat) (x y : LLVM.Int w) (c : LLVM.Int 1) : LLVM.Int 1 :=
  if w = 0 then c
  else LLVM.Int.or (LLVM.Int.uaddOverflowFlag x y)
    (LLVM.Int.uaddOverflowFlag (LLVM.Int.add x y) (veirCarryIn w c))

/-- On a defined carry and a width at least one, the carry-in word is the zero
extension of the carry. -/
theorem veirCarryIn_val {w : Nat} (hw : w ≠ 0) (c : BitVec 1) :
    veirCarryIn w (.val c) = .val (BitVec.ofNat w c.toNat) := by
  unfold veirCarryIn
  split
  · simp [LLVM.Int.zext, Id.run, BitVec.ofNat_toNat]
  · split
    · rename_i h
      subst h
      simp [LLVM.Int.cast]
    · omega

/-- At a width of at least one, the carry-in word of a poison carry is poison. -/
theorem veirCarryIn_poison {w : Nat} (hw : w ≠ 0) : veirCarryIn w .poison = .poison := by
  unfold veirCarryIn
  split
  · rfl
  · split
    · rfl
    · omega

/-- On defined operands the lowering of `addCarryLo w` is `addCarryWord`. -/
theorem veirAddCarryLo_val (w : Nat) (a b : BitVec w) (c : BitVec 1) :
    veirAddCarryLo w (.val a) (.val b) (.val c) = .val (addCarryWord a b c) := by
  unfold veirAddCarryLo
  split
  · rename_i h
    subst h
    exact congrArg LLVM.Int.val (Subsingleton.elim (a + b) _)
  · rename_i h
    rw [veirCarryIn_val h]
    simp [LLVM.Int.add, Id.run, addCarryWord]

/-- The lowering of `addCarryLo w` is monotone for VeIR's refinement. -/
theorem veirAddCarryLo_refines (w : Nat) {x y : LLVM.Int w} {s : LLVM.Int 1}
    {a b : BitVec w} {c : BitVec 1} (hx : x ⊒ .val a) (hy : y ⊒ .val b) (hs : s ⊒ .val c) :
    veirAddCarryLo w x y s ⊒ .val (addCarryWord a b c) := by
  by_cases hw : w = 0
  · subst hw
    rw [Subsingleton.elim (addCarryWord a b c) (a + b)]
    have h : ∀ z, veirAddCarryLo 0 x y z = LLVM.Int.add x y := fun _ => rfl
    rw [h]
    exact llvmInt_refines₂ (fun x y => LLVM.Int.add x y) (by simp [LLVM.Int.add, Id.run])
      (fun _ => rfl) (fun x => by cases x <;> rfl) hx hy
  · refine llvmInt_refines₃ (veirAddCarryLo w) (veirAddCarryLo_val w a b c) ?_ ?_ ?_ hx hy hs
    · intro y z; simp only [veirAddCarryLo, hw, ↓reduceIte]; rfl
    · intro x z; simp only [veirAddCarryLo, hw, ↓reduceIte]; cases x <;> rfl
    · intro x y; simp only [veirAddCarryLo, hw, ↓reduceIte, veirCarryIn_poison hw]
      cases LLVM.Int.add x y <;> rfl

/-- The carry-out of `a + b + cin` is the disjunction of the unsigned overflow of
`a + b` and of the unsigned overflow of adding the carry-in to that sum. -/
theorem carryOutBit_eq_or {w : Nat} (hw : w ≠ 0) (a b : BitVec w) (c : BitVec 1) :
    carryOutBit a b c = BitVec.ofBool (BitVec.uaddOverflow a b) |||
      BitVec.ofBool (BitVec.uaddOverflow (a + b) (BitVec.ofNat w c.toNat)) := by
  have hc : c.toNat < 2 := c.isLt
  have h2 : 2 ≤ 2 ^ w :=
    Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (Nat.pos_of_ne_zero hw))
  have hC : (BitVec.ofNat w c.toNat).toNat = c.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ha := a.isLt
  have hb := b.isLt
  simp only [carryOutBit, BitVec.uaddOverflow, hC, BitVec.toNat_add]
  by_cases h1 : a.toNat + b.toNat ≥ 2 ^ w
  · have h3 : a.toNat + b.toNat + c.toNat ≥ 2 ^ w := by omega
    have h : ∀ p : Bool, 1#1 = 1#1 ||| BitVec.ofBool p := by decide
    simp only [h1, h3, ↓reduceIte, decide_true, BitVec.ofBool_true]
    exact h _
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_not_le h1)]
    by_cases h3 : a.toNat + b.toNat + c.toNat ≥ 2 ^ w <;> simp [h1, h3]

/-- On defined operands the lowering of `addCarryHi w` is `carryOutBit`. -/
theorem veirAddCarryHi_val (w : Nat) (a b : BitVec w) (c : BitVec 1) :
    veirAddCarryHi w (.val a) (.val b) (.val c) = .val (carryOutBit a b c) := by
  unfold veirAddCarryHi
  split
  · rename_i h
    subst h
    have ha : a = 0#0 := Subsingleton.elim _ _
    have hb : b = 0#0 := Subsingleton.elim _ _
    subst ha hb
    rcases bitVec1_eq c with rfl | rfl <;> rfl
  · rename_i h
    rw [veirCarryIn_val h, carryOutBit_eq_or h]
    simp [LLVM.Int.add, LLVM.Int.or, LLVM.Int.uaddOverflowFlag, Id.run]

/-- The lowering of `addCarryHi w` is monotone for VeIR's refinement. -/
theorem veirAddCarryHi_refines (w : Nat) {x y : LLVM.Int w} {s : LLVM.Int 1}
    {a b : BitVec w} {c : BitVec 1} (hx : x ⊒ .val a) (hy : y ⊒ .val b) (hs : s ⊒ .val c) :
    veirAddCarryHi w x y s ⊒ .val (carryOutBit a b c) := by
  by_cases hw : w = 0
  · subst hw
    have h : ∀ x y z, veirAddCarryHi 0 x y z = z := fun _ _ _ => rfl
    have hv := veirAddCarryHi_val 0 a b c
    rw [h] at hv ⊢
    rw [← LLVM.Int.val.inj hv]
    exact hs
  · refine llvmInt_refines₃ (veirAddCarryHi w) (veirAddCarryHi_val w a b c) ?_ ?_ ?_ hx hy hs
    · intro y z; simp only [veirAddCarryHi, hw, ↓reduceIte]; rfl
    · intro x z; simp only [veirAddCarryHi, hw, ↓reduceIte]; cases x <;> rfl
    · intro x y; simp only [veirAddCarryHi, hw, ↓reduceIte, veirCarryIn_poison hw]
      cases x <;> cases y <;> rfl

/-! ## The expansions

The table `JasminOp.bridgeExpansion?`, its expansions and `bridgeExpansionOf` are
defined in `ComToVeir_JasminDialect`, where `bridgeExpansion? false` is the `expand?`
of the `ToVeirOp jasminDialect` instance. -/

/-- The lowering of `jasminDialect` with the expansions `bridgeExpansionOf bare`, at
the end of the block `blk`. -/
abbrev lowerComBridgeWf (bare : Bool) (blk : BlockPtr) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (vm : VarMap Γ) (c : Com jasminDialect Γ t) (ctx : WfIRContext OpCode) :
    Option (WfIRContext OpCode × List OperationPtr × ValuePtr) :=
  lowerComWfWith (bridgeExpansionOf bare) JasminTy.toVeirTy blk vm c ctx

/-- `bridgeExpansionOf false` is the expansion the `ToVeirOp jasminDialect` instance
gives; `veirExpansionOf_eq_bridgeExpansionOf` states it without the fragment
hypothesis. -/
theorem bridgeExpansionOf_false_of_inArith (o : JasminOp) (_h : JasminOp.InArith o)
    (nargs : Nat) : bridgeExpansionOf false o nargs = veirExpansionOf (d := jasminDialect) o nargs :=
  (veirExpansionOf_eq_bridgeExpansionOf o nargs).symm

/-! ## Running the expansions -/

/-- The run of an expansion on operand values: its steps by `veirRunSteps`, then its
value. -/
def veirRunExpansion (x : VeirExpansion OpCode) (resTy : TypeAttr) (args : List RuntimeValue)
    (mem : MemoryState) : Interp (RuntimeValue × MemoryState) := do
  let (done, mem') ← veirRunSteps args resTy x.steps [] mem
  let some r := VeirSrc.resolveVal args done x.value | .fail
  pure (r, mem')

/-- The operations the lowering emits under the expansions `ex` for a binding of
type `t` with op `o`, run on the operand values `args`: the expansion `ex o`, or the
one operation `veirRunOp` and the result in the slot `resultSlotOfOp o` names. -/
def veirRunBindingWith (ex : JasminOp → Option (VeirExpansion OpCode)) (o : JasminOp)
    (t : JasminTy) (args : List RuntimeValue) (mem : MemoryState) :
    Interp (RuntimeValue × MemoryState) :=
  match ex o with
  | some x => veirRunExpansion x (JasminTy.toVeirTy t) args mem
  | none => do
      let (vals, mem', _) ← veirRunOp o t args mem
      let some r := vals[(JasminOp.resultSlotOfOp o).2]? | .fail
      pure (r, mem')

/-- The op-by-op VeIR interpretation of a `Com` under the expansions `ex`: each
binding runs `veirRunBindingWith ex` on the values of its arguments and binds the
value of the binding; `ret v` returns the value of `v`. -/
def veirRunComWith (ex : JasminOp → Option (VeirExpansion OpCode)) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t →
    VEnv Γ → MemoryState → Interp RuntimeValue
  | _, _, .ret v, ρ, _ => .ok (ρ _ v)
  | _, _, .var (t := tEx) e body, ρ, mem => do
      let (r, mem') ← veirRunBindingWith ex e.op tEx (argVals ρ e.args) mem
      veirRunComWith ex body (ρ.extend r) mem'

/-- Where `ex` agrees with the expansions of the `ToVeirOp jasminDialect` instance,
`veirRunBindingWith ex` is `veirRunBinding`. -/
theorem veirRunBindingWith_eq_veirRunBinding
    {ex : JasminOp → Option (VeirExpansion OpCode)} {o : JasminOp}
    (h : ex o = JasminOp.bridgeExpansion? false o) (t : JasminTy) (args : List RuntimeValue)
    (mem : MemoryState) : veirRunBindingWith ex o t args mem = veirRunBinding o t args mem := by
  unfold veirRunBindingWith veirRunBinding
  rw [h]
  cases JasminOp.bridgeExpansion? false o <;> rfl

/-- `veirRunCom` is `veirRunComWith` at the expansions of the `ToVeirOp jasminDialect`
instance, `JasminOp.bridgeExpansion? false`. -/
theorem veirRunComWith_bridgeExpansion?_false : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (ρ : VEnv Γ) (mem : MemoryState),
    veirRunComWith (JasminOp.bridgeExpansion? false) c ρ mem = veirRunCom c ρ mem
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, ρ, mem => by
    simp only [veirRunComWith, veirRunCom, veirRunBindingWith_eq_veirRunBinding rfl]
    cases veirRunBinding e.op _ (argVals ρ e.args) mem with
    | ok p => exact veirRunComWith_bridgeExpansion?_false body _ _
    | _ => rfl

/-- On the `arith` fragment `veirRunCom` is `veirRunComWith` at the expansions
`JasminOp.expandVeir?` of that fragment. -/
theorem veirRunComWith_expandVeir? : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (ρ : VEnv Γ) (mem : MemoryState), ComInArith c →
    veirRunComWith JasminOp.expandVeir? c ρ mem = veirRunCom c ρ mem
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .var e body, ρ, mem, hc => by
    simp only [veirRunComWith, veirRunCom, veirRunBindingWith_eq_veirRunBinding
      (JasminOp.bridgeExpansion?_false_of_inArith e.op hc.1).symm]
    cases veirRunBinding e.op _ (argVals ρ e.args) mem with
    | ok p => exact veirRunComWith_expandVeir? body _ _ hc.2
    | _ => rfl

/-- Evaluation of `veirRunExpansion` on a closed list of steps: unfolds the step
runner, the operand resolution and the `arith` arms of `Veir.interpretOp'`. -/
macro "veir_run_simp" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [veirRunExpansion, aliasExpansion, stConst, stOp, stAddExt, iTy, veirRunSteps,
    List.mapM_nil, Option.pure_def, interpretOp', Arith.interpretOp', List.map_cons,
    Option.getD_some, Option.getD_none, List.map_nil, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, zero_lt_one, getElem?_pos, List.getElem_toArray,
    List.getElem_cons_zero, Attribute.asType_val, BitVec.ofInt_natCast, Interp.pure_eq,
    Interp.bind_ok, List.nil_append, List.mapM_cons, VeirSrc.resolveVal, Nat.reduceAdd,
    Nat.lt_add_one, List.getElem_cons_succ, Option.bind_some, Option.bind_eq_bind, ne_eq,
    Interp.liftOption_none, dite_not, List.cons_append, Nat.zero_lt_succ, not_true_eq_false,
    ↓reduceDIte, LLVM.Int.cast_self, Nat.reduceLT, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    $ls,*])

/-- The expansion of `regArith andn w` runs to `veirAndn`, with memory unchanged. -/
theorem veirRunExpansion_andn (w : Nat) (x y : LLVM.Int w) (resTy : TypeAttr)
    (mem : MemoryState) :
    veirRunExpansion (JasminOp.andnExpansion w) resTy [.int w x, .int w y] mem =
      .ok (.int w (veirAndn x y), mem) := by
  veir_run_simp [JasminOp.andnExpansion, veirAndn]

/-- The expansion of `shlImm w n` runs to `veirShlImm`, with memory unchanged. -/
theorem veirRunExpansion_shlImm (w n : Nat) (x : LLVM.Int w) (resTy : TypeAttr)
    (mem : MemoryState) :
    veirRunExpansion (JasminOp.shlImmExpansion w n) resTy [.int w x] mem =
      .ok (.int w (veirShlImm w n x), mem) := by
  by_cases h : shiftMask w n < w
  · simp only [JasminOp.shlImmExpansion, veirShlImm, h, ↓reduceIte]
    veir_run_simp [veirBinInt]
    rfl
  · simp only [JasminOp.shlImmExpansion, veirShlImm, h, ↓reduceIte]
    veir_run_simp []
    rfl

/-- The expansion of `shrImm w n` runs to `veirShrImm`, with memory unchanged. -/
theorem veirRunExpansion_shrImm (w n : Nat) (x : LLVM.Int w) (resTy : TypeAttr)
    (mem : MemoryState) :
    veirRunExpansion (JasminOp.shrImmExpansion w n) resTy [.int w x] mem =
      .ok (.int w (veirShrImm w n x), mem) := by
  by_cases h : shiftMask w n < w
  · simp only [JasminOp.shrImmExpansion, veirShrImm, h, ↓reduceIte]
    veir_run_simp [veirBinInt]
    rfl
  · simp only [JasminOp.shrImmExpansion, veirShrImm, h, ↓reduceIte]
    veir_run_simp []
    rfl

/-- The expansion of `sarImm w n` runs to `veirSarImm`, with memory unchanged. -/
theorem veirRunExpansion_sarImm (w n : Nat) (x : LLVM.Int w) (resTy : TypeAttr)
    (mem : MemoryState) :
    veirRunExpansion (JasminOp.sarImmExpansion w n) resTy [.int w x] mem =
      .ok (.int w (veirSarImm w n x), mem) := by
  by_cases h : w = 0
  · simp only [JasminOp.sarImmExpansion, veirSarImm, h, ↓reduceIte]
    rfl
  · simp only [JasminOp.sarImmExpansion, veirSarImm, h, ↓reduceIte]
    veir_run_simp []
    rfl

/-- The expansion of `rorImm w n` runs to `veirRorImm`, with memory unchanged. -/
theorem veirRunExpansion_rorImm (w n : Nat) (x : LLVM.Int w) (resTy : TypeAttr)
    (mem : MemoryState) :
    veirRunExpansion (JasminOp.rorImmExpansion w n) resTy [.int w x] mem =
      .ok (.int w (veirRorImm w n x), mem) := by
  by_cases h : w = 0 ∨ n % w = 0
  · simp only [JasminOp.rorImmExpansion, veirRorImm, h, ↓reduceIte]
    rfl
  · simp only [JasminOp.rorImmExpansion, veirRorImm, h, ↓reduceIte]
    veir_run_simp [veirBinInt]
    rfl

/-- The expansion of `castW w w'` runs to `veirCastW`, with memory unchanged. -/
theorem veirRunExpansion_castW (w w' : Nat) (x : LLVM.Int w) (resTy : TypeAttr)
    (mem : MemoryState) :
    veirRunExpansion (JasminOp.castWExpansion w w') resTy [.int w x] mem =
      .ok (.int w' (veirCastW w w' x), mem) := by
  by_cases h : w < w'
  · have h' : ¬ w' ≤ w := Nat.not_le.2 h
    simp only [JasminOp.castWExpansion, veirCastW, h, ↓reduceIte, ↓reduceDIte]
    veir_run_simp [h']
    rfl
  · by_cases h2 : w' < w
    · have h' : ¬ w' ≥ w := Nat.not_le.2 h2
      simp only [JasminOp.castWExpansion, veirCastW, h, h2, ↓reduceIte, ↓reduceDIte]
      veir_run_simp [h']
      rfl
    · have hw : w = w' := Nat.le_antisymm (Nat.le_of_not_lt h2) (Nat.le_of_not_lt h)
      subst hw
      simp only [JasminOp.castWExpansion, veirCastW, h, ↓reduceIte, ↓reduceDIte,
        LLVM.Int.cast_self]
      rfl

/-- The expansion of `cmpImm c w n` runs to `arith.cmpi` against the constant `n`,
with memory unchanged. -/
theorem veirRunExpansion_cmpImm (c : JasminCmp) (w n : Nat) (x : LLVM.Int w)
    (resTy : TypeAttr) (mem : MemoryState) :
    veirRunExpansion (JasminOp.cmpImmExpansion c w n) resTy [.int w x] mem =
      .ok (.int 1 (LLVM.Int.icmp x (.val (BitVec.ofNat w n)) c.toIntPred), mem) := by
  veir_run_simp [JasminOp.cmpImmExpansion]

/-- The expansion of `addCarryLo w` runs to `veirAddCarryLo`, with memory unchanged. -/
theorem veirRunExpansion_addCarryLo (w : Nat) (x y : LLVM.Int w) (c : LLVM.Int 1)
    (resTy : TypeAttr) (mem : MemoryState) :
    veirRunExpansion (JasminOp.addCarryLoExpansion w) resTy [.int w x, .int w y, .int 1 c]
      mem = .ok (.int w (veirAddCarryLo w x y c), mem) := by
  by_cases h0 : w = 0
  · simp only [JasminOp.addCarryLoExpansion, veirAddCarryLo, h0, ↓reduceIte]
    veir_run_simp []
    rfl
  · by_cases h1 : 1 < w
    · have h' : ¬ w ≤ 1 := Nat.not_le.2 h1
      simp only [JasminOp.addCarryLoExpansion, veirAddCarryLo, veirCarryIn, h0, h1, ↓reduceIte,
        ↓reduceDIte]
      veir_run_simp [h']
      rfl
    · have hw : w = 1 := by omega
      subst hw
      simp only [JasminOp.addCarryLoExpansion, veirAddCarryLo, veirCarryIn, h0, h1, ↓reduceIte,
        ↓reduceDIte, LLVM.Int.cast_self]
      veir_run_simp []
      rfl

/-- The expansion of `addCarryHi w` runs to `veirAddCarryHi`, with memory unchanged. -/
theorem veirRunExpansion_addCarryHi (w : Nat) (x y : LLVM.Int w) (c : LLVM.Int 1)
    (resTy : TypeAttr) (mem : MemoryState) :
    veirRunExpansion (JasminOp.addCarryHiExpansion w) resTy [.int w x, .int w y, .int 1 c]
      mem = .ok (.int 1 (veirAddCarryHi w x y c), mem) := by
  by_cases h0 : w = 0
  · simp only [JasminOp.addCarryHiExpansion, veirAddCarryHi, h0, ↓reduceIte]
    rfl
  · by_cases h1 : 1 < w
    · have h' : ¬ w ≤ 1 := Nat.not_le.2 h1
      simp only [JasminOp.addCarryHiExpansion, veirAddCarryHi, veirCarryIn, h0, h1, ↓reduceIte,
        ↓reduceDIte]
      veir_run_simp [h']
      rfl
    · have hw : w = 1 := by omega
      subst hw
      simp only [JasminOp.addCarryHiExpansion, veirAddCarryHi, veirCarryIn, h0, h1, ↓reduceIte,
        ↓reduceDIte, LLVM.Int.cast_self]
      veir_run_simp []
      rfl

/-! ## The bindings that are one operation -/

/-- The binding `mulhi w` runs to the second result of `arith.mului_extended`,
`LLVM.Int.umulHigh`, with memory unchanged. -/
theorem veirRunBindingWith_mulhi (bare : Bool) (w : Nat) (x y : LLVM.Int w)
    (mem : MemoryState) :
    veirRunBindingWith (JasminOp.bridgeExpansion? bare) (.mulhi w) (.reg w)
      [.int w x, .int w y] mem = .ok (.int w (LLVM.Int.umulHigh x y), mem) := by
  simp only [veirRunBindingWith, JasminOp.bridgeExpansion?, veirRunOp, JasminOp.toMlirOpCode,
    JasminOp.resultSlotOfOp, interpretOp', Arith.interpretOp', ne_eq, not_true_eq_false,
    dite_false, LLVM.Int.cast_self, Interp.pure_eq, Interp.bind_ok]
  rfl

/-- The binding `cmp c w` runs to `arith.cmpi` with the predicate of `c`, with memory
unchanged. -/
theorem veirRunBindingWith_cmp (bare : Bool) (c : JasminCmp) (w : Nat) (x y : LLVM.Int w)
    (mem : MemoryState) :
    veirRunBindingWith (JasminOp.bridgeExpansion? bare) (.cmp c w) (.reg 1)
      [.int w x, .int w y] mem = .ok (.int 1 (LLVM.Int.icmp x y c.toIntPred), mem) := by
  simp only [veirRunBindingWith, JasminOp.bridgeExpansion?, veirRunOp, JasminOp.toMlirOpCode,
    JasminOp.resultSlotOfOp, interpretOp', Arith.interpretOp', ne_eq, not_true_eq_false,
    dite_false, LLVM.Int.cast_self, Interp.pure_eq, Interp.bind_ok]
  rfl

/-- The binding `select w` runs to `arith.select`, with memory unchanged. -/
theorem veirRunBindingWith_select (bare : Bool) (w : Nat) (s : LLVM.Int 1) (x y : LLVM.Int w)
    (mem : MemoryState) :
    veirRunBindingWith (JasminOp.bridgeExpansion? bare) (.select w) (.reg w)
      [.int 1 s, .int w x, .int w y] mem = .ok (.int w (LLVM.Int.select s x y), mem) := by
  simp only [veirRunBindingWith, JasminOp.bridgeExpansion?, veirRunOp, JasminOp.toMlirOpCode,
    JasminOp.resultSlotOfOp, interpretOp', Arith.interpretOp', ne_eq, not_true_eq_false,
    dite_false, LLVM.Int.cast_self, Interp.pure_eq, Interp.bind_ok]
  rfl

/-! ## The value relation and the square of each operation

The value relation between a `jasminDialect` value `a` of type `t` and a VeIR runtime
value `r` is `r ⊒ encodeVal t a`: the runtime value is refined by the encoding of the
total value. On integers it holds when `r` is poison or the defined integer
(`llvmInt_isRefinedBy_val_iff`). A square for an operation states that VeIR's
interpretation of its lowering maps related operands to a related result, and
encoded operands to the encoded result. -/

/-- The encoding of a value is refined by itself. -/
theorem encodeVal_isRefinedBy_self (t : JasminTy) (a : TyDenote.denote t) :
    encodeVal t a ⊒ encodeVal t a := by
  cases t <;> exact (int_isRefinedBy_int_iff _ _).2 (isRefinedBy_refl _)

/-- The square of a unary integer operation: from a runtime operand refined by `a`,
the operand is an integer `s`, the result `f s` is refined by `den a`, and is
`den a` when the operand is `a`. -/
theorem int_square₁ {w w' : Nat} (f : LLVM.Int w → LLVM.Int w') (den : BitVec w → BitVec w')
    (hv : ∀ a, f (.val a) = .val (den a))
    (hm : ∀ (a : BitVec w) (x : LLVM.Int w), x ⊒ .val a → f x ⊒ .val (den a))
    {rx : RuntimeValue} {a : BitVec w} (hx : rx ⊒ RuntimeValue.int w (.val a)) :
    ∃ s, rx = .int w s ∧
      (RuntimeValue.int w' (f s) ⊒ RuntimeValue.int w' (.val (den a))) ∧
      (rx = .int w (.val a) → RuntimeValue.int w' (f s) = .int w' (.val (den a))) := by
  obtain ⟨s, rfl, hs⟩ := eq_int_of_isRefinedBy_int hx
  refine ⟨s, rfl, (int_isRefinedBy_int_iff _ _).2 (hm a s hs), fun h => ?_⟩
  cases h
  rw [hv]

/-- The square of a binary integer operation. -/
theorem int_square₂ {w₁ w₂ w' : Nat} (f : LLVM.Int w₁ → LLVM.Int w₂ → LLVM.Int w')
    (den : BitVec w₁ → BitVec w₂ → BitVec w')
    (hv : ∀ a b, f (.val a) (.val b) = .val (den a b))
    (hm : ∀ (a : BitVec w₁) (b : BitVec w₂) (x : LLVM.Int w₁) (y : LLVM.Int w₂),
      x ⊒ .val a → y ⊒ .val b → f x y ⊒ .val (den a b))
    {rx ry : RuntimeValue} {a : BitVec w₁} {b : BitVec w₂}
    (hx : rx ⊒ RuntimeValue.int w₁ (.val a)) (hy : ry ⊒ RuntimeValue.int w₂ (.val b)) :
    ∃ s₁ s₂, rx = .int w₁ s₁ ∧ ry = .int w₂ s₂ ∧
      (RuntimeValue.int w' (f s₁ s₂) ⊒ RuntimeValue.int w' (.val (den a b))) ∧
      (rx = .int w₁ (.val a) → ry = .int w₂ (.val b) →
        RuntimeValue.int w' (f s₁ s₂) = .int w' (.val (den a b))) := by
  obtain ⟨s₁, rfl, hs₁⟩ := eq_int_of_isRefinedBy_int hx
  obtain ⟨s₂, rfl, hs₂⟩ := eq_int_of_isRefinedBy_int hy
  refine ⟨s₁, s₂, rfl, rfl, (int_isRefinedBy_int_iff _ _).2 (hm a b s₁ s₂ hs₁ hs₂),
    fun h₁ h₂ => ?_⟩
  cases h₁
  cases h₂
  rw [hv]

/-- The square of a ternary integer operation. -/
theorem int_square₃ {w₁ w₂ w₃ w' : Nat}
    (f : LLVM.Int w₁ → LLVM.Int w₂ → LLVM.Int w₃ → LLVM.Int w')
    (den : BitVec w₁ → BitVec w₂ → BitVec w₃ → BitVec w')
    (hv : ∀ a b c, f (.val a) (.val b) (.val c) = .val (den a b c))
    (hm : ∀ (a : BitVec w₁) (b : BitVec w₂) (c : BitVec w₃) (x : LLVM.Int w₁) (y : LLVM.Int w₂)
      (z : LLVM.Int w₃), x ⊒ .val a → y ⊒ .val b → z ⊒ .val c → f x y z ⊒ .val (den a b c))
    {rx ry rz : RuntimeValue} {a : BitVec w₁} {b : BitVec w₂} {c : BitVec w₃}
    (hx : rx ⊒ RuntimeValue.int w₁ (.val a)) (hy : ry ⊒ RuntimeValue.int w₂ (.val b))
    (hz : rz ⊒ RuntimeValue.int w₃ (.val c)) :
    ∃ s₁ s₂ s₃, rx = .int w₁ s₁ ∧ ry = .int w₂ s₂ ∧ rz = .int w₃ s₃ ∧
      (RuntimeValue.int w' (f s₁ s₂ s₃) ⊒ RuntimeValue.int w' (.val (den a b c))) ∧
      (rx = .int w₁ (.val a) → ry = .int w₂ (.val b) → rz = .int w₃ (.val c) →
        RuntimeValue.int w' (f s₁ s₂ s₃) = .int w' (.val (den a b c))) := by
  obtain ⟨s₁, rfl, hs₁⟩ := eq_int_of_isRefinedBy_int hx
  obtain ⟨s₂, rfl, hs₂⟩ := eq_int_of_isRefinedBy_int hy
  obtain ⟨s₃, rfl, hs₃⟩ := eq_int_of_isRefinedBy_int hz
  refine ⟨s₁, s₂, s₃, rfl, rfl, rfl,
    (int_isRefinedBy_int_iff _ _).2 (hm a b c s₁ s₂ s₃ hs₁ hs₂ hs₃), fun h₁ h₂ h₃ => ?_⟩
  cases h₁
  cases h₂
  cases h₃
  rw [hv]

/-! ## The fragment and its bindings -/

/-- The scalar fragment: the binary ops `regArith bop w` for every `bop`, the
constant, the high multiply, the comparisons, the select, the width cast, the
rotate, the immediate shifts and the two carry-chain words. Memory ops, calls and
vector ops are outside it. -/
def JasminOp.InBridge : JasminOp → Prop
  | .regArith _ _ => True
  | .regConst _ _ => True
  | .mulhi _ => True
  | .cmp _ _ => True
  | .cmpImm _ _ _ => True
  | .select _ => True
  | .castW _ _ => True
  | .rorImm _ _ => True
  | .shlImm _ _ => True
  | .shrImm _ _ => True
  | .sarImm _ _ => True
  | .addCarryLo _ => True
  | .addCarryHi _ => True
  | _ => False

/-- Every op bound in the program is in the scalar fragment. -/
def ComInBridge : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => JasminOp.InBridge e.op ∧ ComInBridge body

/-- The `arith` fragment is part of the scalar fragment. -/
theorem JasminOp.InArith.inBridge {o : JasminOp} (h : JasminOp.InArith o) :
    JasminOp.InBridge o := by
  cases o <;> trivial

/-- A program of the `arith` fragment is in the scalar fragment. -/
theorem ComInArith.inBridge : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t}, ComInArith c → ComInBridge c
  | _, _, .ret _, _ => trivial
  | _, _, .var _ _, h => ⟨h.1.inBridge, ComInArith.inBridge h.2⟩

/-- The square of one binding of the scalar fragment, for both values of `bare`.
With operands refined by the encoded valuation, the operations of the binding run to
a value `r` with memory unchanged; `r` is refined by the encoded denotation of the
binding; and `r` is the encoded denotation when the operands are the encoded
valuation and, for `bare = true`, the shift amount is below the width. -/
theorem veirRunBindingWith_bridge_square {Γ : Ctxt jasminDialect} {t : JasminTy} (bare : Bool)
    (e : Expr jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : JasminOp.InBridge e.op)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v ⊒ encodeVal s (v.lookup V)) :
    ∃ r, veirRunBindingWith (JasminOp.bridgeExpansion? bare) e.op t (argVals ρ e.args) mem =
        .ok (r, mem) ∧
      r ⊒ encodeVal t (e.denote V) ∧
      ((∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) →
        (bare = true → JasminOp.ShiftSafe e.op (Expr.lookupArgs e.args V)) →
        r = encodeVal t (e.denote V)) := by
  by_cases ha : JasminOp.InArith e.op
  · cases bare
    · obtain ⟨r, hop, hr⟩ := veirRunBinding_expr_refines e V ρ mem ha hρ
      have hrun := veirRunBindingWith_eq_veirRunBinding
        (ex := JasminOp.bridgeExpansion? false) (o := e.op) rfl t (argVals ρ e.args) mem
      refine ⟨r, hrun.trans hop, hr, fun he _ => ?_⟩
      have h2 := veirRunBinding_expr_eq e V ρ mem ha he
      rw [hop] at h2
      simpa using h2
    · obtain ⟨⟨r, hop, hr⟩, hslot⟩ := veirRunOp_expr_refines e V ρ mem ha hρ
      have hx := JasminOp.bridgeExpansion?_true_of_inArith e.op ha
      refine ⟨r, ?_, hr, fun he hs => ?_⟩
      · simp only [veirRunBindingWith, hx, hop, hslot, Interp.bind_ok]
        rfl
      · obtain ⟨h2, _⟩ := veirRunOp_expr_eq e V ρ mem ha (hs rfl) he
        rw [hop] at h2
        simpa using h2
  · obtain ⟨op, hret, args⟩ := e
    cases op <;>
      simp only [JasminOp.InBridge, JasminOp.InArith, ne_eq, not_not, not_true_eq_false,
        not_false_eq_true] at hc ha
    case regArith bop w =>
      subst ha
      subst hret
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest' =>
          cases rest'
          obtain ⟨s₁, s₂, h₁, h₂, hr, he⟩ := int_square₂ (veirAndn (w := w))
            (JasminBinOp.apply .andn) veirAndn_val (fun _ _ _ _ => veirAndn_refines)
            (hρ _ x) (hρ _ y)
          refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x) (hρe _ y)⟩
          show veirRunExpansion (JasminOp.andnExpansion w) _ [ρ _ x, ρ _ y] mem = _
          rw [h₁, h₂]
          exact veirRunExpansion_andn w s₁ s₂ _ mem
    case mulhi w =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest' =>
          cases rest'
          obtain ⟨s₁, s₂, h₁, h₂, hr, he⟩ := int_square₂ (LLVM.Int.umulHigh (w := w))
            mulHiW umulHigh_val (fun _ _ _ _ => umulHigh_refines) (hρ _ x) (hρ _ y)
          refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x) (hρe _ y)⟩
          show veirRunBindingWith _ (.mulhi w) (.reg w) [ρ _ x, ρ _ y] mem = _
          rw [h₁, h₂]
          exact veirRunBindingWith_mulhi bare w s₁ s₂ mem
    case cmp c w =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest' =>
          cases rest'
          obtain ⟨s₁, s₂, h₁, h₂, hr, he⟩ := int_square₂
            (fun x y : LLVM.Int w => LLVM.Int.icmp x y c.toIntPred) (cmpBit c) (icmp_val c)
            (fun _ _ _ _ => icmp_refines c) (hρ _ x) (hρ _ y)
          refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x) (hρe _ y)⟩
          show veirRunBindingWith _ (.cmp c w) (.reg 1) [ρ _ x, ρ _ y] mem = _
          rw [h₁, h₂]
          exact veirRunBindingWith_cmp bare c w s₁ s₂ mem
    case cmpImm c w n =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest
        obtain ⟨s, h₁, hr, he⟩ := int_square₁
          (fun x : LLVM.Int w => LLVM.Int.icmp x (.val (BitVec.ofNat w n)) c.toIntPred)
          (fun a => cmpBit c a (BitVec.ofNat w n)) (fun a => icmp_val c a _)
          (fun _ _ h => icmp_refines c h (isRefinedBy_refl _)) (hρ _ x)
        refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x)⟩
        show veirRunExpansion (JasminOp.cmpImmExpansion c w n) _ [ρ _ x] mem = _
        rw [h₁]
        exact veirRunExpansion_cmpImm c w n s _ mem
    case select w =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest' =>
          cases rest' with
          | cons z rest'' =>
            cases rest''
            obtain ⟨s₁, s₂, s₃, h₁, h₂, h₃, hr, he⟩ := int_square₃
              (LLVM.Int.select (w := w)) selectW select_val
              (fun _ _ _ _ _ _ => select_refines) (hρ _ x) (hρ _ y) (hρ _ z)
            refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x) (hρe _ y) (hρe _ z)⟩
            show veirRunBindingWith _ (.select w) (.reg w) [ρ _ x, ρ _ y, ρ _ z] mem = _
            rw [h₁, h₂, h₃]
            exact veirRunBindingWith_select bare w s₁ s₂ s₃ mem
    case castW w w' =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest
        obtain ⟨s, h₁, hr, he⟩ := int_square₁ (veirCastW w w') (fun a => a.zeroExtend w')
          (veirCastW_val w w') (fun _ _ => veirCastW_refines w w') (hρ _ x)
        refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x)⟩
        show veirRunExpansion (JasminOp.castWExpansion w w') _ [ρ _ x] mem = _
        rw [h₁]
        exact veirRunExpansion_castW w w' s _ mem
    case rorImm w n =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest
        obtain ⟨s, h₁, hr, he⟩ := int_square₁ (veirRorImm w n) (fun a => a.rotateRight n)
          (veirRorImm_val w n) (fun _ _ => veirRorImm_refines w n) (hρ _ x)
        refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x)⟩
        show veirRunExpansion (JasminOp.rorImmExpansion w n) _ [ρ _ x] mem = _
        rw [h₁]
        exact veirRunExpansion_rorImm w n s _ mem
    case shlImm w n =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest
        obtain ⟨s, h₁, hr, he⟩ := int_square₁ (veirShlImm w n) (fun a => a <<< shiftMask w n)
          (veirShlImm_val w n) (fun _ _ => veirShlImm_refines w n) (hρ _ x)
        refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x)⟩
        show veirRunExpansion (JasminOp.shlImmExpansion w n) _ [ρ _ x] mem = _
        rw [h₁]
        exact veirRunExpansion_shlImm w n s _ mem
    case shrImm w n =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest
        obtain ⟨s, h₁, hr, he⟩ := int_square₁ (veirShrImm w n) (fun a => a >>> shiftMask w n)
          (veirShrImm_val w n) (fun _ _ => veirShrImm_refines w n) (hρ _ x)
        refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x)⟩
        show veirRunExpansion (JasminOp.shrImmExpansion w n) _ [ρ _ x] mem = _
        rw [h₁]
        exact veirRunExpansion_shrImm w n s _ mem
    case sarImm w n =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest
        obtain ⟨s, h₁, hr, he⟩ := int_square₁ (veirSarImm w n) (fun a => a.sshiftRight n)
          (veirSarImm_val w n) (fun _ _ => veirSarImm_refines w n) (hρ _ x)
        refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x)⟩
        show veirRunExpansion (JasminOp.sarImmExpansion w n) _ [ρ _ x] mem = _
        rw [h₁]
        exact veirRunExpansion_sarImm w n s _ mem
    case addCarryLo w =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest' =>
          cases rest' with
          | cons z rest'' =>
            cases rest''
            obtain ⟨s₁, s₂, s₃, h₁, h₂, h₃, hr, he⟩ := int_square₃ (veirAddCarryLo w)
              addCarryWord (veirAddCarryLo_val w)
              (fun _ _ _ _ _ _ => veirAddCarryLo_refines w) (hρ _ x) (hρ _ y) (hρ _ z)
            refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x) (hρe _ y) (hρe _ z)⟩
            show veirRunExpansion (JasminOp.addCarryLoExpansion w) _ [ρ _ x, ρ _ y, ρ _ z] mem
              = _
            rw [h₁, h₂, h₃]
            exact veirRunExpansion_addCarryLo w s₁ s₂ s₃ _ mem
    case addCarryHi w =>
      subst hret
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest' =>
          cases rest' with
          | cons z rest'' =>
            cases rest''
            obtain ⟨s₁, s₂, s₃, h₁, h₂, h₃, hr, he⟩ := int_square₃ (veirAddCarryHi w)
              carryOutBit (veirAddCarryHi_val w)
              (fun _ _ _ _ _ _ => veirAddCarryHi_refines w) (hρ _ x) (hρ _ y) (hρ _ z)
            refine ⟨_, ?_, hr, fun hρe _ => he (hρe _ x) (hρe _ y) (hρe _ z)⟩
            show veirRunExpansion (JasminOp.addCarryHiExpansion w) _ [ρ _ x, ρ _ y, ρ _ z] mem
              = _
            rw [h₁, h₂, h₃]
            exact veirRunExpansion_addCarryHi w s₁ s₂ s₃ _ mem

/-! ## Programs -/

/-- On the scalar fragment, for both values of `bare` and every shift amount, the
op-by-op VeIR interpretation from an environment refined by the encoded valuation
`V` returns a value refined by the encoded denotation of the program: the total value
refines VeIR's value, which may be poison. -/
theorem veirRunComWith_bridge_refines (bare : Bool) : ∀ {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ)
    (mem : MemoryState), ComInBridge c →
    (∀ (s : JasminTy) (v : Var Γ s), ρ s v ⊒ encodeVal s (v.lookup V)) →
    ∃ r, veirRunComWith (JasminOp.bridgeExpansion? bare) c ρ mem = .ok r ∧
      r ⊒ encodeVal t (c.denote V)
  | _, _, .ret v, V, ρ, _, _, hρ => ⟨ρ _ v, rfl, hρ _ v⟩
  | _, _, .var e body, V, ρ, mem, hc, hρ => by
    obtain ⟨r, hop, hr, _⟩ := veirRunBindingWith_bridge_square bare e V ρ mem hc.1 hρ
    simp only [veirRunComWith, hop, Interp.bind_ok]
    exact veirRunComWith_bridge_refines bare body _ _ mem hc.2
      (VEnv.extend_rel (· ⊒ ·) ρ V r (e.denote V) hρ hr)

/-- On the scalar fragment the op-by-op VeIR interpretation from the encoded
valuation `V` returns the encoded denotation of the program: for every shift amount
with `bare = false`, and under `ComShiftSafe` with `bare = true`. -/
theorem veirRunComWith_bridge_eq (bare : Bool) : ∀ {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ)
    (mem : MemoryState), ComInBridge c → (bare = true → ComShiftSafe c V) →
    (∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) →
    veirRunComWith (JasminOp.bridgeExpansion? bare) c ρ mem = .ok (encodeVal t (c.denote V))
  | _, _, .ret v, V, ρ, _, _, _, hρ => by
    rw [veirRunComWith, hρ]
    rfl
  | _, _, .var e body, V, ρ, mem, hc, hs, hρ => by
    obtain ⟨r, hop, _, he⟩ := veirRunBindingWith_bridge_square bare e V ρ mem hc.1
      (fun s v => by rw [hρ]; exact encodeVal_isRefinedBy_self _ _)
    have hr := he hρ (fun hb => (hs hb).1)
    subst hr
    simp only [veirRunComWith, hop, Interp.bind_ok]
    exact veirRunComWith_bridge_eq bare body _ _ mem hc.2 (fun hb => (hs hb).2)
      (VEnv.extend_rel (· = ·) ρ V _ (e.denote V) hρ rfl)

/-- The bare-shift lowering under `ComShiftSafe`: on the scalar fragment, with every
shift amount below its width, the VeIR interpretation of the lowering that emits each
shift as one `arith.shli` or `arith.shrui` returns the encoded denotation. -/
theorem veirRunComBare_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : ComInBridge c) (hs : ComShiftSafe c V)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) :
    veirRunComWith (JasminOp.bridgeExpansion? true) c ρ mem =
      .ok (encodeVal t (c.denote V)) :=
  veirRunComWith_bridge_eq true c V ρ mem hc (fun _ => hs) hρ

/-- The lowering with the shift expansion: on the scalar fragment, for every shift
amount, the VeIR interpretation returns the encoded denotation. -/
theorem veirRunComBridge_eq_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : ComInBridge c)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) :
    veirRunComWith (JasminOp.bridgeExpansion? false) c ρ mem =
      .ok (encodeVal t (c.denote V)) :=
  veirRunComWith_bridge_eq false c V ρ mem hc (fun h => absurd h (by decide)) hρ

/-- The interpretation under `bridgeExpansion? false` is `veirRunCom`;
`veirRunComWith_bridgeExpansion?_false` states it without the fragment hypothesis. -/
theorem veirRunComWith_bridge_eq_veirRunCom {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (ρ : VEnv Γ) (mem : MemoryState) (_hc : ComInArith c) :
    veirRunComWith (JasminOp.bridgeExpansion? false) c ρ mem = veirRunCom c ρ mem :=
  veirRunComWith_bridgeExpansion?_false c ρ mem

/-! ## The `ToVeirOp jasminDialect` instance on the scalar fragment

`veirRunCom` runs the operations the `ToVeirOp jasminDialect` instance emits, whose
expansions are `JasminOp.bridgeExpansion? false`. The two theorems below are
`veirRunComWith_bridge_refines` and `veirRunComBridge_eq_denote` at that instance. -/

/-- On the scalar fragment, for every shift amount, the op-by-op VeIR interpretation
of the operations the `ToVeirOp jasminDialect` instance emits, from an environment
refined by the encoded valuation `V`, returns a value refined by the encoded
denotation of the program. -/
theorem veirRunCom_bridge_refines {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : ComInBridge c)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v ⊒ encodeVal s (v.lookup V)) :
    ∃ r, veirRunCom c ρ mem = .ok r ∧ r ⊒ encodeVal t (c.denote V) := by
  rw [← veirRunComWith_bridgeExpansion?_false]
  exact veirRunComWith_bridge_refines false c V ρ mem hc hρ

/-- On the scalar fragment, for every shift amount, the op-by-op VeIR interpretation
of the operations the `ToVeirOp jasminDialect` instance emits, from the encoded
valuation `V`, returns the encoded denotation of the program. -/
theorem veirRunCom_bridge_eq_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : ComInBridge c)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) :
    veirRunCom c ρ mem = .ok (encodeVal t (c.denote V)) := by
  rw [← veirRunComWith_bridgeExpansion?_false]
  exact veirRunComBridge_eq_denote c V ρ mem hc hρ

end CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
