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
`arith.andi`, `arith.ori`, `arith.xori` and `arith.constant`, each with its default
properties (no `nsw`, `nuw`, `exact` or `disjoint` flag) and one result; it sends
the shifts to the expansion `shiftSelectExpansion`, an `arith.shli` or
`arith.shrui` under an `arith.select` of `0` when the amount is at least the width.

* `interpretOp'_regArith`, `interpretOp'_regConst`: VeIR's operation interpreter
  `Veir.interpretOp'`, run on the op-code and properties the lowering emits and on
  operands encoded as `RuntimeValue.int`, returns the encoded LLVM value
  `veirBinInt bop x y`, leaves memory unchanged and takes no control-flow action.
* `veirBinInt_val`: on defined operands `veirBinInt` is the denotation
  `JasminBinOp.apply`, except that `arith.shli`/`arith.shrui` return poison when the
  shift amount is at least the width (`veirBinInt_shl_poison`,
  `veirBinInt_shr_poison`), where `JasminBinOp.apply` returns the logical shift
  (zero).
* `veirShiftSel_val`: the shift expansion (`veirShiftSel`) on defined operands is
  `JasminBinOp.apply` for every amount, since `arith.select` returns the arm its
  condition picks and poison in the other arm does not reach the result.
* `veirRunCom` interprets a `Com` binding by binding with `Veir.interpretOp'`,
  reading operands from an environment of runtime values and running the
  operations `lowerExpr` emits (`veirRunBinding`). `veirRunCom_eq_denote` states
  that on the fragment, from the encoded valuation, it returns the encoded
  denotation for every shift amount; `veirRunCom_refines` states that from an
  environment refined by the encoded valuation the VeIR result is refined, in
  VeIR's sense, by the encoded denotation.

`veirRunCom` reads the op list of `lowerCom` with the same op-codes, properties,
result types, operand order and bound value; it does not read the pointer graph
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

/-! ## The shift expansion -/

/-- The value of `shiftSelectExpansion bop w` on LLVM integers: `arith.select` of
the constant `0` when `arith.cmpi uge` finds the amount `y` at least `w`, and of
`veirBinInt bop x y` otherwise. -/
def veirShiftSel (bop : JasminBinOp) {w : Nat} (x y : LLVM.Int w) : LLVM.Int w :=
  LLVM.Int.select (LLVM.Int.icmp y (.val (BitVec.ofNat w w)) .uge) (.val 0)
    (veirBinInt bop x y)

/-- The `arith.cmpi uge` of a defined amount `b` against the width constant. -/
theorem icmp_uge_width {w : Nat} (b : BitVec w) :
    LLVM.Int.icmp (.val b) (.val (BitVec.ofNat w w)) .uge =
      .val (BitVec.ofBool (decide (w ≤ b.toNat))) := by
  simp [LLVM.Int.icmp, Id.run, LLVM.IntPred.eval, BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt Nat.lt_two_pow_self]

/-- On defined operands, the shift expansion is the value of `JasminBinOp.apply`
for every shift amount: `0` when the amount is at least the width, where the
shift alone is poison. -/
theorem veirShiftSel_val (bop : JasminBinOp) (hb : bop.IsShift) {w : Nat} (a b : BitVec w) :
    veirShiftSel bop (.val a) (.val b) = .val (bop.apply a b) := by
  simp only [veirShiftSel, icmp_uge_width]
  by_cases h : w ≤ b.toNat
  · cases bop <;> simp only [JasminBinOp.IsShift] at hb
    · simp [LLVM.Int.select, Id.run, h, JasminBinOp.apply, BitVec.shiftLeft_eq_zero h]
    · simp [LLVM.Int.select, Id.run, h, JasminBinOp.apply, BitVec.ushiftRight_eq_zero h]
  · have hlt : b.toNat < w := Nat.lt_of_not_le h
    have hne : bop ≠ .andn := by rintro rfl; exact hb
    simp only [LLVM.Int.select, Id.run, h, decide_false, BitVec.ofBool_false]
    exact veirBinInt_val bop hne a b (fun _ => hlt)

/-- The shift expansion is monotone for VeIR's refinement: operands refined by `a`
and `b` give a result refined by `JasminBinOp.apply bop a b`, for every shift
amount. -/
theorem veirShiftSel_refines (bop : JasminBinOp) (hb : bop.IsShift) {w : Nat}
    {x y : LLVM.Int w} {a b : BitVec w} (hx : x ⊒ .val a) (hy : y ⊒ .val b) :
    veirShiftSel bop x y ⊒ .val (bop.apply a b) := by
  have hne : bop ≠ .andn := by rintro rfl; exact hb
  rcases (llvmInt_isRefinedBy_val_iff y b).1 hy with rfl | rfl
  · exact llvmInt_poison_isRefinedBy _
  by_cases h : w ≤ b.toNat
  · have hv : ∀ z : LLVM.Int w, veirShiftSel bop z (.val b) = .val 0 := by
      intro z
      simp [veirShiftSel, icmp_uge_width, LLVM.Int.select, Id.run, h]
    rw [hv, ← hv (.val a), veirShiftSel_val bop hb a b]
    exact isRefinedBy_refl _
  · have hv : veirShiftSel bop x (.val b) = veirBinInt bop x (.val b) := by
      simp [veirShiftSel, icmp_uge_width, LLVM.Int.select, Id.run, h]
    rw [hv]
    exact veirBinInt_refines bop hne hx hy

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

/-- The runtime value an operand of an expansion denotes: argument `i` of `args`,
or result `slot` of the earlier operation `j`, whose results are `done[j]`. -/
def VeirSrc.resolveVal (args : List RuntimeValue) (done : List (Array RuntimeValue)) :
    VeirSrc → Option RuntimeValue
  | .arg i => args[i]?
  | .res j slot => done[j]?.bind (·[slot]?)

/-- The operations of an expansion (`emitStep`), run in order by `Veir.interpretOp'`:
each reads its operands through `VeirSrc.resolveVal`, has the result types of the
step with `none` read as `resTy`, and appends its results to `done`. -/
def veirRunSteps (args : List RuntimeValue) (resTy : TypeAttr) :
    List (VeirExpandStep OpCode) → List (Array RuntimeValue) → MemoryState →
    Interp (List (Array RuntimeValue) × MemoryState)
  | [], done, mem => .ok (done, mem)
  | s :: rest, done, mem => do
      let some ops := s.operands.mapM (VeirSrc.resolveVal args done) | .fail
      let (vals, mem', _) ← Veir.interpretOp' s.op s.props
        (s.results.map (·.getD resTy)).toArray ops.toArray #[] mem
      veirRunSteps args resTy rest (done ++ [vals]) mem'

/-- The operations `lowerExpr` emits for a binding of type `t` with op `o`, run on
the operand values `args`: the steps of `JasminOp.expandVeir? o` followed by the
value of the expansion, or the one operation `veirRunOp` and the result in the slot
`resultSlotOfOp o` names. -/
def veirRunBinding (o : JasminOp) (t : JasminTy) (args : List RuntimeValue)
    (mem : MemoryState) : Interp (RuntimeValue × MemoryState) :=
  match JasminOp.expandVeir? o with
  | some x => do
      let (done, mem') ← veirRunSteps args (JasminTy.toVeirTy t) x.steps [] mem
      let some r := VeirSrc.resolveVal args done x.value | .fail
      pure (r, mem')
  | none => do
      let (vals, mem', _) ← veirRunOp o t args mem
      let some r := vals[(JasminOp.resultSlotOfOp o).2]? | .fail
      pure (r, mem')

/-- The op-by-op VeIR interpretation of a `Com`: each binding runs the operations
`lowerExpr` emits for it (`veirRunBinding`) on the values of its arguments and
binds the value of the binding; `ret v` returns the value of `v`. -/
def veirRunCom : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t →
    VEnv Γ → MemoryState → Interp RuntimeValue
  | _, _, .ret v, ρ, _ => .ok (ρ _ v)
  | _, _, .var (t := tEx) e body, ρ, mem => do
      let (r, mem') ← veirRunBinding e.op tEx (argVals ρ e.args) mem
      veirRunCom body (ρ.extend r) mem'

/-- `veirRunBinding` uses the op-code, properties, result slot, result type and
expansion of the `ToVeirOp jasminDialect` and `ToVeirTy jasminDialect` instances. -/
theorem veirRunOp_uses_instances :
    (ToVeirOp.toOp (d := jasminDialect) = JasminOp.toMlirOpCode) ∧
      (ToVeirOp.resultSlot (d := jasminDialect) = JasminOp.resultSlotOfOp) ∧
      (ToVeirTy.toTy (d := jasminDialect) = JasminTy.toVeirTy) ∧
      (ToVeirOp.expand? (d := jasminDialect) = JasminOp.expandVeir?) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The expansion of a shift `regArith bop w`, run on two `w`-bit operands, returns
`veirShiftSel bop x y` with memory unchanged. -/
theorem veirRunBinding_shift (bop : JasminBinOp) (hb : bop.IsShift) (w : Nat)
    (x y : LLVM.Int w) (mem : MemoryState) :
    veirRunBinding (.regArith bop w) (.reg w) [.int w x, .int w y] mem =
      .ok (.int w (veirShiftSel bop x y), mem) := by
  cases bop <;> simp only [JasminBinOp.IsShift] at hb
  all_goals
    simp only [veirRunBinding, JasminOp.expandVeir?, JasminOp.shiftSelectExpansion,
      BitVec.toNat_ofNat, Nat.mod_two_pow_self, JasminOp.toMlirOpCode,
      JasminBinOp.toArithOpCode, veirRunSteps, List.mapM_nil, Option.pure_def, interpretOp',
      Arith.interpretOp', JasminTy.toVeirTy, List.map_cons, Option.getD_none, List.map_nil,
      List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, zero_lt_one,
      getElem?_pos, List.getElem_toArray, List.getElem_cons_zero, Attribute.asType_val,
      BitVec.ofInt_natCast, Interp.pure_eq, Interp.bind_ok, List.nil_append, List.mapM_cons,
      VeirSrc.resolveVal, Nat.reduceAdd, Nat.lt_add_one, List.getElem_cons_succ,
      Option.bind_some, Option.bind_eq_bind, ne_eq, Interp.liftOption_none, dite_not,
      List.cons_append, Nat.zero_lt_succ, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
      BitVec.ofInt_ofNat, Nat.reduceLT, veirShiftSel, BitVec.ofNat_eq_ofNat, veirBinInt]
    rfl

/-- An op that is not a shift has no expansion. -/
theorem JasminOp.expandVeir?_eq_none (o : JasminOp)
    (h : ¬ ∃ bop w, o = .regArith bop w ∧ bop.IsShift) : JasminOp.expandVeir? o = none := by
  cases o <;> try rfl
  rename_i bop w
  cases bop <;> first | rfl | exact absurd ⟨_, _, rfl, trivial⟩ h

/-- An op that is not a shift is `ShiftSafe` on every argument. -/
theorem JasminOp.shiftSafe_of_not_shift (o : JasminOp)
    (args : HVector (fun t => TyDenote.denote t) (DialectSignature.sig (d := jasminDialect) o))
    (h : ¬ ∃ bop w, o = .regArith bop w ∧ bop.IsShift) : JasminOp.ShiftSafe o args := by
  cases o <;> first | trivial | exact fun hb => absurd ⟨_, _, rfl, hb⟩ h

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

/-- The operand values of a two-argument binding, read from an environment. -/
theorem argVals_two {Γ : Ctxt jasminDialect} (ρ : VEnv Γ) {s₁ s₂ : JasminTy} (x : Var Γ s₁)
    (y : Var Γ s₂) : argVals ρ (HVector.cons x (HVector.cons y HVector.nil)) = [ρ _ x, ρ _ y] :=
  rfl

/-- One binding of the `arith` fragment, with operands read from the encoded
valuation, runs to the encoded denotation of the binding, with memory unchanged,
for every shift amount. -/
theorem veirRunBinding_expr_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : JasminOp.InArith e.op)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) :
    veirRunBinding e.op t (argVals ρ e.args) mem = .ok (encodeVal t (e.denote V), mem) := by
  by_cases hsh : ∃ bop w, e.op = .regArith bop w ∧ bop.IsShift
  · obtain ⟨bop, w, hop, hbs⟩ := hsh
    obtain ⟨op, hret, args⟩ := e
    simp only at hop
    subst hop
    subst hret
    cases args with
    | cons x rest =>
      cases rest with
      | cons y rest' =>
        cases rest'
        simp only
        rw [argVals_two, hρ, hρ]
        exact (veirRunBinding_shift bop hbs w _ _ mem).trans
          (by rw [veirShiftSel_val bop hbs]; rfl)
  · have hx := JasminOp.expandVeir?_eq_none e.op hsh
    obtain ⟨hop, hslot⟩ := veirRunOp_expr_eq e V ρ mem hc
      (JasminOp.shiftSafe_of_not_shift e.op _ hsh) hρ
    simp only [veirRunBinding, hx, hop, hslot, Interp.bind_ok]
    rfl

/-- One binding of the `arith` fragment, with operands refined by the encoded
valuation, runs to a value refined by the encoded denotation of the binding, with
memory unchanged, for every shift amount. -/
theorem veirRunBinding_expr_refines {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : JasminOp.InArith e.op)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v ⊒ encodeVal s (v.lookup V)) :
    ∃ r, veirRunBinding e.op t (argVals ρ e.args) mem = .ok (r, mem) ∧
      r ⊒ encodeVal t (e.denote V) := by
  by_cases hsh : ∃ bop w, e.op = .regArith bop w ∧ bop.IsShift
  · obtain ⟨bop, w, hop, hbs⟩ := hsh
    obtain ⟨op, hret, args⟩ := e
    simp only at hop
    subst hop
    subst hret
    cases args with
    | cons x rest =>
      cases rest with
      | cons y rest' =>
        cases rest'
        obtain ⟨sx, hsx, hrx⟩ := eq_int_of_isRefinedBy_int (hρ _ x)
        obtain ⟨sy, hsy, hry⟩ := eq_int_of_isRefinedBy_int (hρ _ y)
        refine ⟨.int w (veirShiftSel bop sx sy), ?_, ?_⟩
        · simp only
          rw [argVals_two, hsx, hsy]
          exact veirRunBinding_shift bop hbs w _ _ mem
        · exact (int_isRefinedBy_int_iff _ _).2 (veirShiftSel_refines bop hbs hrx hry)
  · have hx := JasminOp.expandVeir?_eq_none e.op hsh
    obtain ⟨⟨r, hop, hr⟩, hslot⟩ := veirRunOp_expr_refines e V ρ mem hc hρ
    refine ⟨r, ?_, hr⟩
    simp only [veirRunBinding, hx, hop, hslot, Interp.bind_ok]
    rfl

/-- On the `arith` fragment, for every shift amount, the op-by-op VeIR
interpretation from the encoded valuation `V` returns the encoded denotation of the
program. -/
theorem veirRunCom_eq_denote : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState),
    ComInArith c →
    (∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) →
    veirRunCom c ρ mem = .ok (encodeVal t (c.denote V))
  | _, _, .ret v, V, ρ, _, _, hρ => by
    rw [veirRunCom, hρ]
    rfl
  | _, _, .var e body, V, ρ, mem, hc, hρ => by
    have hop := veirRunBinding_expr_eq e V ρ mem hc.1 hρ
    simp only [veirRunCom, hop, Interp.bind_ok]
    exact veirRunCom_eq_denote body _ _ mem hc.2
      (VEnv.extend_rel (· = ·) ρ V _ (e.denote V) hρ rfl)

/-- On the `arith` fragment, with every shift amount below its width, the op-by-op
VeIR interpretation from the encoded valuation `V` returns the encoded denotation
of the program. `veirRunCom_eq_denote` states it for every shift amount. -/
theorem veirRunCom_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ) (ρ : VEnv Γ) (mem : MemoryState)
    (hc : ComInArith c) (_hs : ComShiftSafe c V)
    (hρ : ∀ (s : JasminTy) (v : Var Γ s), ρ s v = encodeVal s (v.lookup V)) :
    veirRunCom c ρ mem = .ok (encodeVal t (c.denote V)) :=
  veirRunCom_eq_denote c V ρ mem hc hρ

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
    obtain ⟨r, hop, hr⟩ := veirRunBinding_expr_refines e V ρ mem hc.1 hρ
    simp only [veirRunCom, hop, Interp.bind_ok]
    exact veirRunCom_refines body _ _ mem hc.2
      (VEnv.extend_rel (· ⊒ ·) ρ V r (e.denote V) hρ hr)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
