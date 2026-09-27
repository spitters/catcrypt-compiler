/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir_JasminDialect
public import Veir.Interpreter.Basic
public import Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Basic
import all Veir.Data.LLVM.Int.Basic
import all Veir.IR.Attribute

/-!
# Semantics of the `Com → Veir` lowering on the `arith` fragment of `jasminDialect`

The `arith` fragment of `jasminDialect` is the set of ops `regArith bop w` with
`bop ∈ {add, sub, mul, and, or, xor, shl, shr}` and `regConst w n`. The instance
`ToVeirOp jasminDialect` sends them to `arith.addi`, `arith.subi`, `arith.muli`,
`arith.andi`, `arith.ori`, `arith.xori`, `arith.shli`, `arith.shrui` and
`arith.constant`, each with its default properties (no `nsw`, `nuw`, `exact` or
`disjoint` flag) and one result.

* `interpretOp'_regArith`, `interpretOp'_regConst`: VeIR's operation interpreter
  `Veir.interpretOp'`, run on the op-code and properties the lowering emits and on
  operands encoded as `RuntimeValue.int`, returns the encoded LLVM value
  `veirBinInt bop x y`, leaves memory unchanged and takes no control-flow action.
* `veirBinInt_val`: on defined operands `veirBinInt` is the denotation
  `JasminBinOp.apply`, except that `arith.shli`/`arith.shrui` return poison when the
  shift amount is at least the width (`veirBinInt_shl_poison`,
  `veirBinInt_shr_poison`), where `JasminBinOp.apply` returns the logical shift
  (zero).
* `veirRunCom` interprets a `Com` op by op with `Veir.interpretOp'`, reading
  operands from an environment of runtime values and binding the result slot the
  lowering (`lowerExprSingle`) binds. `veirRunCom_eq` states that on the fragment,
  from the encoded valuation, it returns the encoded denotation whenever every
  shift amount is below its width (`Com.ShiftSafe`); `veirRunCom_refines` states
  that without that condition the VeIR result is refined, in VeIR's sense, by the
  encoded denotation.

`veirRunCom` reads the op list of `lowerCom` with the same op-codes, properties,
result types, operand order and result slot; it does not read the pointer graph
that `lowerComToBlockRegion` builds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

open Veir Veir.Data
open CatCrypt.Crypto.SecureCompilation.VIR (Com Expr Ctxt TyDenote DialectSignature)
open Ctxt (Var Valuation)

/-! ## Op level -/

/-- The value VeIR's `arith` interpreter computes for the op-code of
`regArith bop w` with default properties, on LLVM integers. `andn` has no
`arith` op-code and is sent to poison. -/
def veirBinInt : JasminBinOp → {w : Nat} → LLVM.Int w → LLVM.Int w → LLVM.Int w
  | .add, _, x, y => LLVM.Int.add x y
  | .sub, _, x, y => LLVM.Int.sub x y
  | .mul, _, x, y => LLVM.Int.mul x y
  | .and, _, x, y => LLVM.Int.and x y
  | .or, _, x, y => LLVM.Int.or x y
  | .xor, _, x, y => LLVM.Int.xor x y
  | .shl, _, x, y => LLVM.Int.shl x y
  | .shr, _, x, y => LLVM.Int.lshr x y
  | .andn, _, _, _ => .poison

/-- The shift ops of `JasminBinOp`. -/
def JasminBinOp.IsShift : JasminBinOp → Prop
  | .shl => True
  | .shr => True
  | _ => False

/-- `Veir.interpretOp'` on the op-code and properties of `regArith bop w`, for
`bop ≠ andn`, with two `w`-bit integer operands, returns `veirBinInt bop x y`. -/
theorem interpretOp'_regArith (bop : JasminBinOp) (hb : bop ≠ .andn) (w : Nat)
    (x y : LLVM.Int w) (rts : Array TypeAttr) (bo : Array BlockPtr) (mem : MemoryState)
    (layout : DataLayout) :
    Veir.interpretOp' (JasminOp.toMlirOpCode (.regArith bop w))
      (JasminOp.propsOfOp (.regArith bop w)) rts #[.int w x, .int w y] bo mem layout =
      .ok (#[.int w (veirBinInt bop x y)], mem, none) := by
  cases bop <;> first
    | exact absurd rfl hb
    | (simp only [Veir.interpretOp', JasminOp.toMlirOpCode, JasminBinOp.toArithOpCode,
        Arith.interpretOp', ne_eq, not_true_eq_false, dite_false, LLVM.Int.cast_self,
        Interp.pure_eq, Interp.bind_ok, veirBinInt] <;> rfl)

/-- `Veir.interpretOp'` on the op-code and properties of `regConst w n`, with the
result type the lowering emits, returns the `w`-bit constant `BitVec.ofNat w n`. -/
theorem interpretOp'_regConst (w n : Nat) (bo : Array BlockPtr) (mem : MemoryState)
    (layout : DataLayout) :
    Veir.interpretOp' (JasminOp.toMlirOpCode (.regConst w n))
      (JasminOp.propsOfOp (.regConst w n)) #[JasminTy.toVeirTy (.reg w)] #[] bo mem layout =
      .ok (#[.int w (.val (BitVec.ofNat w n))], mem, none) := by
  simp only [Veir.interpretOp', JasminOp.toMlirOpCode, Arith.interpretOp', Interp.pure_eq]
  have h : BitVec.ofInt w ((BitVec.ofNat w n).toNat : Int) = BitVec.ofNat w n := by
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← h]
  rfl

/-- The shift-amount test of `LLVM.Int.shl` and `LLVM.Int.lshr`, `b ≥ w` in
`BitVec w`, is `w ≤ b.toNat`. -/
theorem bitVec_ge_natCast_self_iff {w : Nat} (b : BitVec w) :
    b ≥ (w : BitVec w) ↔ w ≤ b.toNat := by
  simp [BitVec.le_def, Nat.mod_eq_of_lt Nat.lt_two_pow_self]

/-- A shift amount at least the width: `arith.shli` is poison. -/
theorem veirBinInt_shl_poison {w : Nat} (a b : BitVec w) (h : w ≤ b.toNat) :
    veirBinInt .shl (.val a) (.val b) = .poison := by
  simp only [veirBinInt, LLVM.Int.shl, Id.run, (bitVec_ge_natCast_self_iff b).2 h, if_true]
  rfl

/-- A shift amount at least the width: `arith.shrui` is poison. -/
theorem veirBinInt_shr_poison {w : Nat} (a b : BitVec w) (h : w ≤ b.toNat) :
    veirBinInt .shr (.val a) (.val b) = .poison := by
  simp only [veirBinInt, LLVM.Int.lshr, Id.run, (bitVec_ge_natCast_self_iff b).2 h, if_true]
  rfl

/-- On defined operands, and a shift amount below the width for the shifts,
`veirBinInt` is the value of `JasminBinOp.apply`. -/
theorem veirBinInt_val (bop : JasminBinOp) (hb : bop ≠ .andn) {w : Nat} (a b : BitVec w)
    (hs : bop.IsShift → b.toNat < w) :
    veirBinInt bop (.val a) (.val b) = .val (bop.apply a b) := by
  cases bop
  all_goals first
    | exact absurd rfl hb
    | rfl
    | (have hlt := hs trivial
       simp only [veirBinInt, LLVM.Int.shl, LLVM.Int.lshr, Id.run, bitVec_ge_natCast_self_iff,
         JasminBinOp.apply, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
       simp [Nat.not_le.2 hlt])

/-- Every op of `veirBinInt` returns poison on a poison operand. -/
theorem veirBinInt_poison_left (bop : JasminBinOp) {w : Nat} (y : LLVM.Int w) :
    veirBinInt bop .poison y = .poison := by
  cases bop <;> rfl

/-- Every op of `veirBinInt` returns poison on a poison operand. -/
theorem veirBinInt_poison_right (bop : JasminBinOp) {w : Nat} (x : LLVM.Int w) :
    veirBinInt bop x .poison = .poison := by
  cases bop <;> cases x <;> rfl

/-- An LLVM integer refines to a defined value exactly when it is that value or
poison. -/
theorem llvmInt_isRefinedBy_val_iff {w : Nat} (x : LLVM.Int w) (a : BitVec w) :
    (x ⊒ LLVM.Int.val a) ↔ x = .poison ∨ x = .val a := by
  cases x <;> simp [isRefinedBy_eq, eq_comm]

/-- Poison is refined by every LLVM integer. -/
theorem llvmInt_poison_isRefinedBy {w : Nat} (y : LLVM.Int w) : LLVM.Int.poison ⊒ y :=
  (isRefinedBy_eq _ _).2 trivial

/-- `veirBinInt` is monotone for VeIR's refinement: operands refined by `a` and
`b` give a result refined by `JasminBinOp.apply bop a b`, for every shift amount. -/
theorem veirBinInt_refines (bop : JasminBinOp) (hb : bop ≠ .andn) {w : Nat}
    {x y : LLVM.Int w} {a b : BitVec w} (hx : x ⊒ .val a) (hy : y ⊒ .val b) :
    veirBinInt bop x y ⊒ .val (bop.apply a b) := by
  rcases (llvmInt_isRefinedBy_val_iff x a).1 hx with rfl | rfl
  · rw [veirBinInt_poison_left]; exact llvmInt_poison_isRefinedBy _
  rcases (llvmInt_isRefinedBy_val_iff y b).1 hy with rfl | rfl
  · rw [veirBinInt_poison_right]; exact llvmInt_poison_isRefinedBy _
  by_cases hs : bop.IsShift → b.toNat < w
  · rw [veirBinInt_val bop hb a b hs]
    exact isRefinedBy_refl _
  · have hsh : bop.IsShift := Classical.byContradiction fun h => hs (fun h' => absurd h' h)
    have hge : w ≤ b.toNat := Nat.le_of_not_lt fun h => hs (fun _ => h)
    cases bop <;> simp only [JasminBinOp.IsShift] at hsh
    · rw [veirBinInt_shl_poison a b hge]; exact llvmInt_poison_isRefinedBy _
    · rw [veirBinInt_shr_poison a b hge]; exact llvmInt_poison_isRefinedBy _

/-! ## Runtime values -/

/-- The runtime value of a `jasminDialect` value: a `w`-bit register is the
defined `w`-bit integer, a flag is the defined `i1`. Stack arrays and inline
integers have no counterpart in the `arith` fragment and are sent to the
poison `i0`. -/
def encodeVal : (t : JasminTy) → TyDenote.denote t → RuntimeValue
  | .reg w, x => .int w (.val x)
  | .bool, b => .int 1 (.val (BitVec.ofBool b))
  | .stackArr _ _, _ => .int 0 .poison
  | .inlineInt, _ => .int 0 .poison

/-- Runtime refinement of two integers of one width is refinement of the LLVM
integers. -/
theorem int_isRefinedBy_int_iff {w : Nat} (s t : LLVM.Int w) :
    (RuntimeValue.int w s ⊒ RuntimeValue.int w t) ↔ (s ⊒ t) := by
  simp [RuntimeValue.isRefinedBy]

/-- A runtime value refined by a defined `w`-bit integer is a `w`-bit integer
refined by it. -/
theorem eq_int_of_isRefinedBy_int {w : Nat} {r : RuntimeValue} {a : BitVec w}
    (h : r ⊒ RuntimeValue.int w (.val a)) :
    ∃ s : LLVM.Int w, r = .int w s ∧ (s ⊒ LLVM.Int.val a) := by
  cases r <;> simp only [RuntimeValue.isRefinedBy] at h
  rename_i w' s
  obtain ⟨rfl, h⟩ := h
  exact ⟨s, rfl, by simpa using h⟩

/-! ## Op-by-op interpretation of a `Com` -/

/-- The ops of the `arith` fragment: `regArith bop w` for `bop ≠ andn`, and
`regConst w n`. -/
def JasminOp.InArith : JasminOp → Prop
  | .regArith bop _ => bop ≠ .andn
  | .regConst _ _ => True
  | _ => False

/-- Every op bound in the program is in the `arith` fragment. -/
def ComInArith : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => JasminOp.InArith e.op ∧ ComInArith body

/-- The shift amount of a shift op is below the width, on the given arguments. -/
def JasminOp.ShiftSafe : (o : JasminOp) →
    HVector (fun t => TyDenote.denote t) (DialectSignature.sig (d := jasminDialect) o) → Prop
  | .regArith bop w, args => bop.IsShift → (args.tail.head : BitVec w).toNat < w
  | _, _ => True

/-- Every shift bound in the program, run from `V`, has its amount below the
width. -/
def ComShiftSafe : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t →
    Valuation Γ → Prop
  | _, _, .ret _, _ => True
  | _, _, .var e body, V =>
      JasminOp.ShiftSafe e.op (Expr.lookupArgs e.args V) ∧
        ComShiftSafe body (Ctxt.Valuation.extend V (e.denote V))

/-- An environment of runtime values, one per variable. -/
abbrev VEnv (Γ : Ctxt jasminDialect) : Type := ∀ t : JasminTy, Var Γ t → RuntimeValue

/-- Extend an environment with the value of a new binding. -/
def VEnv.extend {Γ : Ctxt jasminDialect} {t : JasminTy} (ρ : VEnv Γ) (r : RuntimeValue) :
    VEnv (t :: Γ) :=
  fun s v => by
    cases v with
    | here => exact r
    | there v' => exact ρ s v'

/-- The runtime values of the arguments of a binding, in order. -/
def argVals {Γ : Ctxt jasminDialect} (ρ : VEnv Γ) :
    {tys : List JasminTy} → HVector (fun ty => Var Γ ty) tys → List RuntimeValue
  | [], .nil => []
  | _ :: _, .cons v rest => ρ _ v :: argVals ρ rest

/-- The operation `lowerExprSingle` emits for a binding of type `t` with op `o`,
run by `Veir.interpretOp'` on the operand values `args`: the op-code
`toMlirOpCode o`, the properties `propsOfOp o`, `max n 1` results of type
`toVeirTy t` where `n` is the result count of `resultSlotOfOp o`. -/
def veirRunOp (o : JasminOp) (t : JasminTy) (args : List RuntimeValue) (mem : MemoryState) :
    Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  Veir.interpretOp' (JasminOp.toMlirOpCode o) (JasminOp.propsOfOp o)
    (Array.replicate (max (JasminOp.resultSlotOfOp o).1 1) (JasminTy.toVeirTy t))
    args.toArray #[] mem

/-- The op-by-op VeIR interpretation of a `Com`: each binding runs the operation
`lowerExprSingle` emits for it (`veirRunOp`) on the values of its arguments and
binds the result in the slot `resultSlotOfOp` names; `ret v` returns the value of
`v`. -/
def veirRunCom : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t →
    VEnv Γ → MemoryState → Interp RuntimeValue
  | _, _, .ret v, ρ, _ => .ok (ρ _ v)
  | _, _, .var (t := tEx) e body, ρ, mem => do
      let (vals, mem', _) ← veirRunOp e.op tEx (argVals ρ e.args) mem
      let some r := vals[(JasminOp.resultSlotOfOp e.op).2]? | .fail
      veirRunCom body (ρ.extend r) mem'

/-- `veirRunOp` uses the op-code, properties, result slot and result type of the
`ToVeirOp jasminDialect` and `ToVeirTy jasminDialect` instances. -/
theorem veirRunOp_uses_instances :
    (ToVeirOp.toOp (d := jasminDialect) = JasminOp.toMlirOpCode) ∧
      (ToVeirOp.resultSlot (d := jasminDialect) = JasminOp.resultSlotOfOp) ∧
      (ToVeirTy.toTy (d := jasminDialect) = JasminTy.toVeirTy) ∧
      (ToVeirOp.expand? (d := jasminDialect) = fun _ => none) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- One binding of the `arith` fragment, with its shift amount below the width and
operands read from the encoded valuation, runs to the encoded denotation of the
binding, with memory unchanged. -/
theorem veirRunOp_expr_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : JasminOp.InArith e.op) (hs : JasminOp.ShiftSafe e.op (Expr.lookupArgs e.args V))
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) :
    veirRunOp e.op t (argVals ρ e.args) mem = .ok (#[encodeVal t (e.denote V)], mem, none) ∧
      (JasminOp.resultSlotOfOp e.op).2 = 0 := by
  obtain ⟨op, hret, args⟩ := e
  cases op <;> simp only [JasminOp.InArith] at hc
  case regArith bop w =>
    subst hret
    cases args with
    | cons x rest =>
      cases rest with
      | cons y rest' =>
        cases rest'
        refine ⟨?_, rfl⟩
        have hargs : (argVals ρ (HVector.cons x (HVector.cons y HVector.nil))).toArray =
            #[.int w (.val (x.lookup V)), .int w (.val (y.lookup V))] := by
          show #[ρ _ x, ρ _ y] = _
          rw [hρ, hρ]
          rfl
        simp only [veirRunOp]
        rw [hargs, interpretOp'_regArith bop hc,
          veirBinInt_val bop hc (x.lookup V) (y.lookup V) hs]
        rfl
  case regConst w n =>
    subst hret
    cases args
    refine ⟨?_, rfl⟩
    exact interpretOp'_regConst w n #[] mem .riscv64

/-- One binding of the `arith` fragment, with operands refined by the encoded
valuation, runs to a single result refined by the encoded denotation of the
binding, with memory unchanged, for every shift amount. -/
theorem veirRunOp_expr_refines {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : JasminOp.InArith e.op)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v ⊒ encodeVal s (v.lookup V)) :
    (∃ r, veirRunOp e.op t (argVals ρ e.args) mem = .ok (#[r], mem, none) ∧
        r ⊒ encodeVal t (e.denote V)) ∧
      (JasminOp.resultSlotOfOp e.op).2 = 0 := by
  obtain ⟨op, hret, args⟩ := e
  cases op <;> simp only [JasminOp.InArith] at hc
  case regArith bop w =>
    subst hret
    cases args with
    | cons x rest =>
      cases rest with
      | cons y rest' =>
        cases rest'
        refine ⟨?_, rfl⟩
        obtain ⟨sx, hsx, hrx⟩ := eq_int_of_isRefinedBy_int (hρ _ x)
        obtain ⟨sy, hsy, hry⟩ := eq_int_of_isRefinedBy_int (hρ _ y)
        have hargs : (argVals ρ (HVector.cons x (HVector.cons y HVector.nil))).toArray =
            #[.int w sx, .int w sy] := by
          show #[ρ _ x, ρ _ y] = _
          rw [hsx, hsy]
        refine ⟨.int w (veirBinInt bop sx sy), ?_, ?_⟩
        · simp only [veirRunOp]
          rw [hargs, interpretOp'_regArith bop hc]
        · exact (int_isRefinedBy_int_iff _ _).2 (veirBinInt_refines bop hc hrx hry)
  case regConst w n =>
    subst hret
    cases args
    refine ⟨⟨.int w (.val (BitVec.ofNat w n)), interpretOp'_regConst w n #[] mem .riscv64, ?_⟩,
      rfl⟩
    exact (int_isRefinedBy_int_iff _ _).2 (isRefinedBy_refl _)

/-- The environment `ρ.extend r` agrees with the valuation `V.extend a` when `ρ`
agrees with `V` and `r` with `a`, for a relation `R` between runtime values. -/
theorem VEnv.extend_rel {Γ : Ctxt jasminDialect} {t : JasminTy} (R : RuntimeValue → RuntimeValue → Prop)
    (ρ : VEnv Γ) (V : Valuation Γ) (r : RuntimeValue) (a : TyDenote.denote t)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), R (ρ s v) (encodeVal s (v.lookup V)))
    (hr : R r (encodeVal t a)) :
    ∀ (s : JasminTy) (v : Var (t :: Γ) s),
      R (ρ.extend r s v) (encodeVal s (v.lookup (Ctxt.Valuation.extend V a))) := by
  intro s v
  cases v with
  | here => exact hr
  | there v' => exact hρ _ v'

/-- On the `arith` fragment, with every shift amount below its width, the op-by-op
VeIR interpretation from the encoded valuation `V` returns the encoded
denotation of the program. -/
theorem veirRunCom_eq : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState),
    ComInArith c → ComShiftSafe c V →
    (∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) →
    veirRunCom c ρ mem = .ok (encodeVal t (c.denote V))
  | _, _, .ret v, V, ρ, _, _, _, hρ => by
    rw [veirRunCom, hρ]
    rfl
  | _, _, .var e body, V, ρ, mem, hc, hs, hρ => by
    obtain ⟨hop, hslot⟩ := veirRunOp_expr_eq e V ρ mem hc.1 hs.1 hρ
    simp only [veirRunCom, hop, hslot, Interp.bind_ok]
    exact veirRunCom_eq body _ _ mem hc.2 hs.2
      (VEnv.extend_rel (· = ·) ρ V _ (e.denote V) hρ rfl)

/-- On the `arith` fragment, for every shift amount, the op-by-op VeIR
interpretation from an environment refined by the encoded valuation `V` returns a
value refined by the encoded denotation of the program. -/
theorem veirRunCom_refines : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState),
    ComInArith c →
    (∀ (s : JasminTy) (v : Var Γ s), ρ s v ⊒ encodeVal s (v.lookup V)) →
    ∃ r, veirRunCom c ρ mem = .ok r ∧ r ⊒ encodeVal t (c.denote V)
  | _, _, .ret v, V, ρ, _, _, hρ => ⟨ρ _ v, rfl, hρ _ v⟩
  | _, _, .var e body, V, ρ, mem, hc, hρ => by
    obtain ⟨⟨r, hop, hr⟩, hslot⟩ := veirRunOp_expr_refines e V ρ mem hc.1 hρ
    simp only [veirRunCom, hop, hslot, Interp.bind_ok]
    exact veirRunCom_refines body _ _ mem hc.2
      (VEnv.extend_rel (· ⊒ ·) ρ V r (e.denote V) hρ hr)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
