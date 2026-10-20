/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrWord

/-!
# Simulation of the straight-line Jasmin lowering in the `psem.v` mirror

The code `nfToJasminBody` emits for a binding of an operation, translated by
`translateCmdExt` and typed by `typeC` as `translateFn` does, runs in the mirror's `Sem`
from a state that agrees with the valuation of the program to a state that agrees with the
valuation extended by the denotation of the operation (`emitOp_sem`). A straight-line region
(let-bindings, then `ret`) runs to a state whose returned variables hold the denotation of
the region (`nfToJasminBody_sem`).

## Agreement

A dialect value of type `reg w` is held as the mirror word of the mirror word size `mws w`
with the same unsigned value: a `reg 1` value is a `0`/`1` word of type `u64`. A stack array
`stackArr w n` is held as a byte array of `n * (mws w).bytes` bytes whose little-endian word
at the byte offset `j * (mws w).bytes` is element `j`. A Jasmin variable `x` is held at the
mirror variable `mvar x` of the same name and translated type (`JazzVarAgrees`).

`JazzStoreAgrees env d L V s` relates the environment `env` of the lowering, the depth `d`
of the next binding, a set `L` of de Bruijn indices (the variables read by the rest of the
program, `usesIdx`), the valuation `V` and the mirror state `s`: every index of `L` names
an argument or a binding below `d` (`EnvBelow`), distinct indices of `L` name distinct
variables, its variable holds its value, and every array variable of the mirror state holds
an array of its declared size (`VmArrTyped`). An in-place store overwrites the variable of
its array operand; `linGo` guarantees that index is not read afterwards.

## Operator semantics and indices

The mirror's operator semantics is a parameter `opS : OpSem`. `JazzOpAgrees opS` states the
word equations of the operators the lowering emits at the word sizes of the x86
general-purpose registers, each as `sem_op_typed.v` gives it (a shift count is converted
to `u8` and masked by `x86_shift_mask`); `jazzOpSem` is an operator semantics that
satisfies them (`jazzOpSem_agrees`). The dialect reads and writes a stack array at the
index modulo its length, while the mirror's `getWord`/`setWord` fail out of range;
`IdxInBounds` states, along the denotation of a program, that every array access of the run
is in range.

## Main results

* `JazzVarAgrees`, `JazzStoreAgrees`, `JazzResAgrees`: the agreement relations.
* `JazzOpAgrees`, `jazzOpSem`, `jazzOpSem_agrees`: the operator equations and an instance.
* `IdxInBounds`: the index precondition.
* `emitOp_sem`: the code of one binding simulates the operation.
* `nfToJasminBody_sem`: a straight-line region simulates its denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (varIndex)
open CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem (gprB bmiB jazzOps jazzAsmSem
  JazzAsmAgrees opName)
open CatCrypt.Crypto.Jasmin.CoqSemMirror (Value Vm Estate OpSem AsmSem GlobDecls Prog Sem
  SemIr SemI SemFor JResult truncateVal evalAtype JArrayMirror MemModel semPexpr writeLval
  writeLvals setVar getVar mkLvar)

/-! ## 1. Mirror word sizes and variables -/

/-- The mirror word size of a dialect width: `U8`, `U16`, `U32`, `U128`, `U256` at those
widths and `U64` at every other width, a `reg 1` value being a `u64` word. -/
def mws (w : Nat) : MWSize :=
  if w = 8 then .U8 else if w = 16 then .U16 else if w = 32 then .U32
  else if w = 128 then .U128 else if w = 256 then .U256 else .U64

/-- Every width other than `512` has the word size `mws w` in the mirror. -/
theorem translateWSize_wsOf {w : Nat} (h : w ≠ 512) : translateWSize (wsOf w) = some (mws w) := by
  unfold wsOf mws
  split_ifs <;> rfl

/-- The byte width of `wsOf w` is that of `mws w` for every width other than `512`. -/
theorem bytes_wsOf {w : Nat} (h : w ≠ 512) : (wsOf w).bytes = (mws w).bytes := by
  unfold wsOf mws
  split_ifs <;> rfl

/-- A width of `widthOkB` is the bit width of a word size of `gprB`. -/
theorem exists_gpr {w : Nat} (h : widthOkB w = true) :
    ∃ ws : MWSize, gprB ws = true ∧ ws.bits = w ∧ mws w = ws ∧
      translateWSize (wsOf w) = some ws := by
  simp only [widthOkB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl
  · exact ⟨.U8, rfl, rfl, rfl, rfl⟩
  · exact ⟨.U16, rfl, rfl, rfl, rfl⟩
  · exact ⟨.U32, rfl, rfl, rfl, rfl⟩
  · exact ⟨.U64, rfl, rfl, rfl, rfl⟩

/-- The mirror variable of a Jasmin variable: its name at its translated type. -/
def mvar (x : JVar) : MVar := { vtype := (translateSTypeExt x.vtype).getD .aint, vname := x.vname }

/-- The mirror variable with information of a Jasmin variable. -/
def mvi (x : JVar) : MVarI := { v_var := mvar x }

/-- A Jasmin variable without a 512-bit type translates to `mvi`. -/
theorem translateVarIExt_mvi {x : JVar} (h : OkV x) : translateVarIExt ⟨x, vi0⟩ = some (mvi x) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (translateSTypeExt_isSome h)
  simp [translateVarIExt, translateVarExt, ht, mvi, mvar]

/-- The mirror type of a register variable. -/
theorem mvar_vtype_reg {x : JVar} {w : Nat} (hx : x.vtype = styOf (.reg w)) (h : w ≠ 512) :
    (mvar x).vtype = .aword (mws w) := by
  simp [mvar, hx, styOf, ptyOf, CatCrypt.Crypto.Jasmin.Jazz.PType.toSType, translateSTypeExt,
    translateSType, translateWSize_wsOf h]

/-- The mirror type of an array variable. -/
theorem mvar_vtype_arr {x : JVar} {w n : Nat} (hx : x.vtype = styOf (.stackArr w n))
    (h : w ≠ 512) : (mvar x).vtype = .aarr .U8 (n * (mws w).bytes) := by
  simp [mvar, hx, styOf, ptyOf, CatCrypt.Crypto.Jasmin.Jazz.PType.toSType, translateSTypeExt,
    bytes_wsOf h]

/-! ## 2. Agreement -/

/-- The mirror value `v` holds the dialect value `a` of type `t`: a register as the word of
size `mws w` with the same unsigned value, a stack array as the byte array whose
little-endian words are its elements, an integer and a Boolean as themselves. -/
def JazzValAgrees : (t : JasminTy) → ⟦t⟧ → Value → Prop
  | .reg w, a, v => v = .Vword (mws w) (BitVec.ofNat _ (BitVec.toNat (w := w) a))
  | .stackArr w n, a, v => ∃ arr : JArrayMirror (n * (mws w).bytes),
      v = .Varr _ arr ∧ ∀ j : Fin n,
        arr.readLE (j.val * (mws w).bytes) (mws w).bytes = (BitVec.toNat (w := w) (a j))
  | .inlineInt, a, v => v = .Vint (a : Nat)
  | .bool, a, v => v = .Vbool a

/-- The Jasmin variable `x` has the type of `t` and its mirror variable holds `a`. -/
def JazzVarAgrees (x : JVar) (t : JasminTy) (a : ⟦t⟧) (vm : Vm) : Prop :=
  x.vtype = styOf t ∧ JazzValAgrees t a (vm (mvar x))

/-- Every mirror variable of an array type holds an array of its declared size. -/
def VmArrTyped (vm : Vm) : Prop :=
  ∀ (y : MVar) (ws : MWSize) (n : Nat), y.vtype = .aarr ws n → ∃ a, vm y = .Varr n a

/-- The variable `v` is an argument `mkV 'a' k s` or a binding `mkV 'r' k s` at a depth
`k < d`. -/
def EnvBelow (d : Nat) (v : JVar) : Prop :=
  (∃ k s, v = mkV 'a' k s) ∨ ∃ k s, k < d ∧ v = mkV 'r' k s

/-- The names of the scratch variables of the code of one binding: the carry flag, the
scratch registers `mkV 't' k s` and the indices `mkV 'i' k s` of zeroing loops. -/
def Scratch (nm : String) : Prop :=
  nm = "cf" ∨ ∃ k s, nm = nameOf 't' k s ∨ nm = nameOf 'i' k s

variable {SyscallState Mem : Type} [MemModel Mem]

/-- **Store agreement.** The environment `env` at the depth `d` and the mirror state `s`
agree with the valuation `V` on the indices of `L`: each names an argument or a binding
below `d`, distinct indices name distinct variables, each variable holds its value, and
every array variable holds an array of its declared size. -/
structure JazzStoreAgrees (env : List JVar) (d : Nat) (L : Nat → Prop) {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) (s : Estate SyscallState Mem) : Prop where
  /-- Every live variable holds its value. -/
  agree : ∀ {t : JasminTy} (v : Ctxt.Var Γ t), L (varIndex v) →
    JazzVarAgrees (env.getD (varIndex v) dfltV) t (v.lookup V) s.evm
  /-- Every live index names an argument or a binding below `d`. -/
  below : ∀ i, L i → EnvBelow d (env.getD i dfltV)
  /-- Distinct live indices name distinct variables. -/
  inj : ∀ i j, L i → L j → (env.getD i dfltV).vname = (env.getD j dfltV).vname → i = j
  /-- Every array variable holds an array of its declared size. -/
  arrTyped : VmArrTyped s.evm

/-- The variables `res` hold the values `r` in the state `s`. -/
def JazzResAgrees : {ts : List JasminTy} → List JVar → HVector (fun t => ⟦t⟧) ts →
    Estate SyscallState Mem → Prop
  | [], [], .nil, _ => True
  | t :: _, x :: xs, .cons a r, s => JazzVarAgrees x t a s.evm ∧ JazzResAgrees xs r s
  | _, _, _, _ => False

/-! ## 3. The operator semantics -/

/-- **Operator equations.** The unary and binary operators the lowering emits, at the word
sizes of `gprB`, as `sem_op_typed.v` gives them: the word of an integer and the unsigned
integer of a `u64` word, zero extension, negation, the ring and bitwise operations, the
shifts (the count converted to `u8` and masked by `x86_shift_mask`, `shiftMask`), and
disequality. -/
structure JazzOpAgrees (opS : OpSem) : Prop where
  /-- `Oword_of_int ws`. -/
  wordOfInt : ∀ ws : MWSize, gprB ws = true → ∀ z : Int,
    opS.sem_sop1 (.Oword_of_int ws) (.Vint z) = .ok (.Vword ws (BitVec.ofInt ws.bits z))
  /-- `Oint_of_word Unsigned U64`. -/
  intOfWord : ∀ a : BitVec 64,
    opS.sem_sop1 (.Oint_of_word .Unsigned .U64) (.Vword .U64 a) = .ok (.Vint (a.toNat : Int))
  /-- `Ozeroext wso wsi`. -/
  zeroext : ∀ wso wsi : MWSize, gprB wso = true → gprB wsi = true → ∀ a : BitVec wsi.bits,
    opS.sem_sop1 (.Ozeroext wso wsi) (.Vword wsi a) = .ok (.Vword wso (a.setWidth wso.bits))
  /-- `Oneg (Op_w ws)`. -/
  neg : ∀ ws : MWSize, gprB ws = true → ∀ a : BitVec ws.bits,
    opS.sem_sop1 (.Oneg (.Op_w ws)) (.Vword ws a) = .ok (.Vword ws (-a))
  /-- `Oadd (Op_w ws)`. -/
  add : ∀ ws : MWSize, gprB ws = true → ∀ a b : BitVec ws.bits,
    opS.sem_sop2 (.Oadd (.Op_w ws)) (.Vword ws a) (.Vword ws b) = .ok (.Vword ws (a + b))
  /-- `Osub (Op_w ws)`. -/
  sub : ∀ ws : MWSize, gprB ws = true → ∀ a b : BitVec ws.bits,
    opS.sem_sop2 (.Osub (.Op_w ws)) (.Vword ws a) (.Vword ws b) = .ok (.Vword ws (a - b))
  /-- `Omul (Op_w ws)`. -/
  mul : ∀ ws : MWSize, gprB ws = true → ∀ a b : BitVec ws.bits,
    opS.sem_sop2 (.Omul (.Op_w ws)) (.Vword ws a) (.Vword ws b) = .ok (.Vword ws (a * b))
  /-- `Oland ws`. -/
  land : ∀ ws : MWSize, gprB ws = true → ∀ a b : BitVec ws.bits,
    opS.sem_sop2 (.Oland ws) (.Vword ws a) (.Vword ws b) = .ok (.Vword ws (a &&& b))
  /-- `Olor ws`. -/
  lor : ∀ ws : MWSize, gprB ws = true → ∀ a b : BitVec ws.bits,
    opS.sem_sop2 (.Olor ws) (.Vword ws a) (.Vword ws b) = .ok (.Vword ws (a ||| b))
  /-- `Olxor ws`. -/
  lxor : ∀ ws : MWSize, gprB ws = true → ∀ a b : BitVec ws.bits,
    opS.sem_sop2 (.Olxor ws) (.Vword ws a) (.Vword ws b) = .ok (.Vword ws (a ^^^ b))
  /-- `Olsl (Op_w ws)`, the count a word of any size of `gprB`. -/
  lsl : ∀ ws ws' : MWSize, gprB ws = true → gprB ws' = true → ∀ (a : BitVec ws.bits)
    (c : BitVec ws'.bits), opS.sem_sop2 (.Olsl (.Op_w ws)) (.Vword ws a) (.Vword ws' c) =
      .ok (.Vword ws (a <<< shiftMask ws.bits (c.toNat % 256)))
  /-- `Olsr ws`, the count a word of any size of `gprB`. -/
  lsr : ∀ ws ws' : MWSize, gprB ws = true → gprB ws' = true → ∀ (a : BitVec ws.bits)
    (c : BitVec ws'.bits), opS.sem_sop2 (.Olsr ws) (.Vword ws a) (.Vword ws' c) =
      .ok (.Vword ws (a >>> shiftMask ws.bits (c.toNat % 256)))
  /-- `Oasr (Op_w ws)`, the count a word of any size of `gprB`. -/
  asr : ∀ ws ws' : MWSize, gprB ws = true → gprB ws' = true → ∀ (a : BitVec ws.bits)
    (c : BitVec ws'.bits), opS.sem_sop2 (.Oasr (.Op_w ws)) (.Vword ws a) (.Vword ws' c) =
      .ok (.Vword ws (a.sshiftRight (shiftMask ws.bits (c.toNat % 256))))
  /-- `Oneq (Op_w ws)`. -/
  neq : ∀ ws : MWSize, gprB ws = true → ∀ a b : BitVec ws.bits,
    opS.sem_sop2 (.Oneq (.Op_w ws)) (.Vword ws a) (.Vword ws b) = .ok (.Vbool (a != b))

/-- The unary operators of `jazzOpSem`: each operand converted by `to_int` or `to_word` as
`sem_op_typed.v` does. -/
def jazzSop1 : MSOp1 → Value → JResult Value
  | .Oword_of_int ws, v => do let z ← v.toInt; .ok (.Vword ws (BitVec.ofInt ws.bits z))
  | .Oint_of_word .Unsigned ws, v => do let a ← v.toWord ws; .ok (.Vint (a.toNat : Int))
  | .Ozeroext wso wsi, v => do let a ← v.toWord wsi; .ok (.Vword wso (a.setWidth wso.bits))
  | .Oneg (.Op_w ws), v => do let a ← v.toWord ws; .ok (.Vword ws (-a))
  | _, _ => .typeError

/-- A binary word operation of `jazzOpSem`: both operands converted to words of size `ws`. -/
def wordOp2 (ws : MWSize) (f : BitVec ws.bits → BitVec ws.bits → Value) (v1 v2 : Value) :
    JResult Value := do
  let a ← v1.toWord ws
  let b ← v2.toWord ws
  .ok (f a b)

/-- A shift of `jazzOpSem`: the count converted to a `u8` word. -/
def wordShiftSem (ws : MWSize) (f : BitVec ws.bits → Nat → BitVec ws.bits) (v1 v2 : Value) :
    JResult Value := do
  let a ← v1.toWord ws
  let c ← v2.toWord .U8
  .ok (.Vword ws (f a (shiftMask ws.bits c.toNat)))

/-- The binary operators of `jazzOpSem`. -/
def jazzSop2 : MSOp2 → Value → Value → JResult Value
  | .Oadd (.Op_w ws) => wordOp2 ws fun a b => .Vword ws (a + b)
  | .Osub (.Op_w ws) => wordOp2 ws fun a b => .Vword ws (a - b)
  | .Omul (.Op_w ws) => wordOp2 ws fun a b => .Vword ws (a * b)
  | .Oland ws => wordOp2 ws fun a b => .Vword ws (a &&& b)
  | .Olor ws => wordOp2 ws fun a b => .Vword ws (a ||| b)
  | .Olxor ws => wordOp2 ws fun a b => .Vword ws (a ^^^ b)
  | .Oneq (.Op_w ws) => wordOp2 ws fun a b => .Vbool (a != b)
  | .Olsl (.Op_w ws) => wordShiftSem ws fun a k => a <<< k
  | .Olsr ws => wordShiftSem ws fun a k => a >>> k
  | .Oasr (.Op_w ws) => wordShiftSem ws fun a k => a.sshiftRight k
  | _ => fun _ _ => .typeError

/-- An operator semantics with the equations of `JazzOpAgrees`. -/
def jazzOpSem : OpSem where
  sem_sop1 := jazzSop1
  sem_sop2 := jazzSop2
  sem_opN := fun _ _ => .typeError

/-- A word converted to its own size is itself. -/
theorem toWord_self (ws : MWSize) (a : BitVec ws.bits) : (Value.Vword ws a).toWord ws = .ok a := by
  simp [Value.toWord, CatCrypt.Crypto.Jasmin.CoqSemMirror.truncateWord]

/-- A word of a size of `gprB` converted to `u8` is its value modulo `256`. -/
theorem toWord_U8 {ws : MWSize} (h : gprB ws = true) (c : BitVec ws.bits) :
    (Value.Vword ws c).toWord .U8 = .ok (BitVec.ofNat _ c.toNat) := by
  have h8 : CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits ≤ ws.bits := by
    cases ws <;> simp_all [gprB] <;> decide
  simp only [Value.toWord, CatCrypt.Crypto.Jasmin.CoqSemMirror.truncateWord, h8, if_true]

/-- A shift of `jazzOpSem` with a count word of a size of `gprB`. -/
theorem wordShiftSem_eq {ws ws' : MWSize} (h : gprB ws' = true)
    (f : BitVec ws.bits → Nat → BitVec ws.bits) (a : BitVec ws.bits) (c : BitVec ws'.bits) :
    wordShiftSem ws f (.Vword ws a) (.Vword ws' c) =
      .ok (.Vword ws (f a (shiftMask ws.bits (c.toNat % 256)))) := by
  simp only [wordShiftSem, toWord_self, toWord_U8 h c, JResult.monad_bind_eq, JResult.bind_ok,
    BitVec.toNat_ofNat]
  rfl

/-- `jazzOpSem` satisfies the operator equations. -/
theorem jazzOpSem_agrees : JazzOpAgrees jazzOpSem where
  wordOfInt _ _ _ := rfl
  intOfWord a := by
    simp only [jazzOpSem, jazzSop1, JResult.monad_bind_eq, Value.toWord,
      CatCrypt.Crypto.Jasmin.CoqSemMirror.truncateWord, le_refl, if_true, JResult.bind_ok,
      BitVec.toNat_ofNat]
    exact congrArg (fun k : Nat => JResult.ok (Value.Vint (k : Int))) (Nat.mod_eq_of_lt a.isLt)
  zeroext _ _ _ _ a := by
    simp only [jazzOpSem, jazzSop1, toWord_self, JResult.monad_bind_eq, JResult.bind_ok]
  neg _ _ a := by
    simp only [jazzOpSem, jazzSop1, toWord_self, JResult.monad_bind_eq, JResult.bind_ok]
  add _ _ a b := by simp only [jazzOpSem, jazzSop2, wordOp2, toWord_self,
    JResult.monad_bind_eq, JResult.bind_ok]
  sub _ _ a b := by simp only [jazzOpSem, jazzSop2, wordOp2, toWord_self,
    JResult.monad_bind_eq, JResult.bind_ok]
  mul _ _ a b := by simp only [jazzOpSem, jazzSop2, wordOp2, toWord_self,
    JResult.monad_bind_eq, JResult.bind_ok]
  land _ _ a b := by simp only [jazzOpSem, jazzSop2, wordOp2, toWord_self,
    JResult.monad_bind_eq, JResult.bind_ok]
  lor _ _ a b := by simp only [jazzOpSem, jazzSop2, wordOp2, toWord_self,
    JResult.monad_bind_eq, JResult.bind_ok]
  lxor _ _ a b := by simp only [jazzOpSem, jazzSop2, wordOp2, toWord_self,
    JResult.monad_bind_eq, JResult.bind_ok]
  neq _ _ a b := by simp only [jazzOpSem, jazzSop2, wordOp2, toWord_self,
    JResult.monad_bind_eq, JResult.bind_ok]
  lsl _ _ _ h a c := wordShiftSem_eq h _ a c
  lsr _ _ _ h a c := wordShiftSem_eq h _ a c
  asr _ _ _ h a c := wordShiftSem_eq h _ a c

/-! ## 4. Mirror steps -/

section Steps
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- A defined value is its own truncation at its type. -/
theorem truncateVal_typeOf {v : Value} (hv : v.isDefined = true) :
    truncateVal v.typeOf v = .ok v := by
  cases v with
  | Vbool b => rfl
  | Vint z => rfl
  | Varr n a => simp [truncateVal, Value.typeOf, JArrayMirror.cast]
  | Vword sz w => exact ComJasminBridgeFull.truncateVal_aword_self sz w
  | Vundef t => simp [Value.isDefined] at hv

/-- A read of a local variable holding a defined value. -/
theorem semPexpr_mpv {s : Estate SyscallState Mem} {x : MVarI} {v : Value}
    (h : s.evm x.v_var = v) (hv : v.isDefined = true) :
    semPexpr (Mem := Mem) true gd opS s (mpv x) = .ok v := by
  show CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar true gd s.evm (mkLvar x) = _
  unfold CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar
  rw [show (mkLvar x).isLvar = true from rfl, if_pos rfl]
  show getVar true s.evm x.v_var = _
  unfold getVar
  simp [Vm.get, h, hv]

/-- A write of a defined value of the declared type to a local variable. -/
theorem writeLval_lvar {s : Estate SyscallState Mem} {x : MVarI} {v : Value}
    (hv : v.isDefined = true) (hty : v.typeOf = evalAtype x.v_var.vtype) :
    writeLval (Mem := Mem) true gd opS (.Lvar x) v s =
      .ok (s.withVm (s.evm.set x.v_var v)) := by
  show (do let vm ← setVar true s.evm x.v_var v; .ok (s.withVm vm)) = _
  have hDB : CatCrypt.Crypto.Jasmin.CoqSemMirror.DB v = true := by
    simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.DB, hv]
  have htr : ∀ t, v.typeOf = t → CatCrypt.Crypto.Jasmin.CoqSemMirror.truncatable t v = true :=
    fun t h => by simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.truncatable, h]
  unfold setVar
  cases hvt : x.v_var.vtype <;> simp only [hvt, evalAtype] at hty <;>
    simp [hDB, htr _ hty]

/-- A discarded output of a value its type truncates. -/
theorem writeLval_lnone {s : Estate SyscallState Mem} {ty : MAtype} {v : Value}
    (ht : CatCrypt.Crypto.Jasmin.CoqSemMirror.truncatable (evalAtype ty) v = true)
    (hdb : CatCrypt.Crypto.Jasmin.CoqSemMirror.DB v = true) :
    writeLval (Mem := Mem) true gd opS (.Lnone () ty) v s = .ok s := by
  show CatCrypt.Crypto.Jasmin.CoqSemMirror.writeNone s (evalAtype ty) v = _
  simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.writeNone, ht, hdb]

/-- **Assignment step.** An assignment whose right-hand side evaluates to a defined value
of the type of its target writes that value. -/
theorem semIr_masgn {s : Estate SyscallState Mem} {x : MVarI} {e : MPexpr} {v : Value}
    (he : semPexpr (Mem := Mem) true gd opS s e = .ok v) (hv : v.isDefined = true)
    (hty : v.typeOf = evalAtype x.v_var.vtype) :
    SemIr aS opS gd prog s (masgn x e) (s.withVm (s.evm.set x.v_var v)) :=
  .Eassgn _ _ _ _ _ _ v v he (by rw [← hty]; exact truncateVal_typeOf hv)
    (writeLval_lvar opS gd hv hty)

/-- **Asm step.** An asm operation whose operands evaluate to `vs`, whose semantics returns
`rs`, and whose outputs take `rs`. -/
theorem semIr_mcopn {s s' : Estate SyscallState Mem} {o : String} {lvs : List MLval}
    {es : List MPexpr} {vs rs : List Value}
    (hes : CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprs (Mem := Mem) true gd opS s es = .ok vs)
    (ho : aS.sopn_sem (.Oasm o) vs = .ok rs)
    (hw : writeLvals (Mem := Mem) true gd opS s lvs rs = .ok s') :
    SemIr aS opS gd prog s (mcopn o lvs es) s' := by
  refine .Eopn _ _ _ _ _ _ ?_
  simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.semSopn, hes,
    CatCrypt.Crypto.Jasmin.CoqSemMirror.execSopn, ho, hw]

/-- A step followed by a run. -/
theorem sem_cons {s s1 s2 : Estate SyscallState Mem} {i : MInstrR} {c : List MInstr}
    (h1 : SemIr aS opS gd prog s i s1) (h2 : Sem aS opS gd prog s1 c s2) :
    Sem aS opS gd prog s (.MkI () i :: c) s2 :=
  .Eseq _ _ _ _ _ (.EmkI _ _ _ _ h1) h2

/-- A unary operation over an evaluated operand. -/
theorem semPexpr_papp1 {s : Estate SyscallState Mem} {o : MSOp1} {e : MPexpr} {v : Value}
    (h : semPexpr (Mem := Mem) true gd opS s e = .ok v) :
    semPexpr (Mem := Mem) true gd opS s (.Papp1 o e) = opS.sem_sop1 o v := by
  show (do let v1 ← semPexpr (Mem := Mem) true gd opS s e; opS.sem_sop1 o v1) = _
  rw [h]; rfl

/-- A binary operation over evaluated operands. -/
theorem semPexpr_papp2 {s : Estate SyscallState Mem} {o : MSOp2} {e1 e2 : MPexpr}
    {v1 v2 : Value} (h1 : semPexpr (Mem := Mem) true gd opS s e1 = .ok v1)
    (h2 : semPexpr (Mem := Mem) true gd opS s e2 = .ok v2) :
    semPexpr (Mem := Mem) true gd opS s (.Papp2 o e1 e2) = opS.sem_sop2 o v1 v2 := by
  show (do let v1 ← semPexpr (Mem := Mem) true gd opS s e1
           let v2 ← semPexpr (Mem := Mem) true gd opS s e2
           opS.sem_sop2 o v1 v2) = _
  rw [h1, h2]; rfl

/-- The typed word constant `(ws) z`. -/
theorem semPexpr_wconst (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true)
    (s : Estate SyscallState Mem) (z : Int) :
    semPexpr (Mem := Mem) true gd opS s (typeConst (.aword ws) z) =
      .ok (.Vword ws (BitVec.ofInt ws.bits z)) := by
  rw [show typeConst (.aword ws) z = .Papp1 (.Oword_of_int ws) (.Pconst z) from rfl,
    semPexpr_papp1 opS gd (v := .Vint z) rfl, hop.wordOfInt ws hg]

/-- The operands of a list of reads. -/
theorem semPexprs_cons {s : Estate SyscallState Mem} {e : MPexpr} {es : List MPexpr}
    {v : Value} {vs : List Value} (h : semPexpr (Mem := Mem) true gd opS s e = .ok v)
    (hs : CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprs (Mem := Mem) true gd opS s es = .ok vs) :
    CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprs (Mem := Mem) true gd opS s (e :: es) =
      .ok (v :: vs) := by
  show (do let v ← semPexpr (Mem := Mem) true gd opS s e
           let vs ← CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprList (Mem := Mem) true gd opS s es
           .ok (v :: vs)) = _
  rw [h, show CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprList (Mem := Mem) true gd opS s es
    = .ok vs from hs]; rfl

/-- The empty list of operands. -/
theorem semPexprs_nil (s : Estate SyscallState Mem) :
    CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprs (Mem := Mem) true gd opS s [] = .ok [] := rfl

end Steps

/-! ## 5. Steps over the Jasmin code -/

/-- The translation of a command with a head instruction. -/
theorem translateCmdExt_cons_inv {i : AInstrR} {c : List AInstrR} {c' : List MInstr}
    (h : translateCmdExt (i :: c) = some c') :
    ∃ i' c'', translateInstrRExt i = some i' ∧ translateCmdExt c = some c'' ∧
      c' = .MkI () i' :: c'' := by
  simp only [translateCmdExt] at h
  cases hi : translateInstrRExt i with
  | none => simp [hi] at h
  | some i' =>
      cases hc : translateCmdExt c with
      | none => simp [hi, hc] at h
      | some c'' =>
          simp only [hi, hc, Option.some.injEq] at h
          exact ⟨i', c'', rfl, rfl, h.symm⟩

/-- The translation of a concatenation splits. -/
theorem translateCmdExt_append_inv : ∀ {a b : List AInstrR} {c' : List MInstr},
    translateCmdExt (a ++ b) = some c' →
      ∃ a' b', translateCmdExt a = some a' ∧ translateCmdExt b = some b' ∧ c' = a' ++ b'
  | [], _, _, h => ⟨[], _, rfl, h, rfl⟩
  | i :: a, b, c', h => by
      obtain ⟨i', c'', hi, hc, rfl⟩ := translateCmdExt_cons_inv (c := a ++ b) h
      obtain ⟨a', b', ha, hb, rfl⟩ := translateCmdExt_append_inv hc
      exact ⟨.MkI () i' :: a', b', by simp [translateCmdExt, hi, ha], hb, rfl⟩

/-- The typing of a concatenation. -/
theorem typeC_append : ∀ a b : List MInstr, typeC (a ++ b) = typeC a ++ typeC b
  | [], _ => rfl
  | .MkI ii i :: a, b => by
      rw [List.cons_append, typeC, typeC, typeC_append a b, List.cons_append]

section Run
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- The end of a command. -/
theorem sem_nil_step {c' : List MInstr} (hc : translateCmdExt [] = some c')
    (s : Estate SyscallState Mem) : Sem aS opS gd prog s (typeC c') s := by
  simp only [translateCmdExt, Option.some.injEq] at hc
  subst hc
  exact .Eskip _

/-- **Assignment over the Jasmin code.** The translated and typed assignment `x = e` runs
when its typed right-hand side evaluates to a defined value of the type of `x`. -/
theorem sem_asgn_step {x : JVar} (hx : OkV x) {e : APExpr} {e' : MPexpr}
    (he : translatePExprExt e = some e') {c : List AInstrR} {c' : List MInstr}
    (hc : translateCmdExt (asgn x e :: c) = some c') {s s2 : Estate SyscallState Mem}
    {v : Value}
    (hv : semPexpr (Mem := Mem) true gd opS s (typeE (mvar x).vtype e') = .ok v)
    (hdef : v.isDefined = true) (hty : v.typeOf = evalAtype (mvar x).vtype)
    (hrest : ∀ c'', translateCmdExt c = some c'' →
      Sem aS opS gd prog (s.withVm (s.evm.set (mvar x) v)) (typeC c'') s2) :
    Sem aS opS gd prog s (typeC c') s2 := by
  obtain ⟨i', c'', hi, hc', rfl⟩ := translateCmdExt_cons_inv hc
  rw [translateInstrRExt_asgn (translateVarIExt_mvi hx) he, Option.some.injEq] at hi
  subst hi
  exact sem_cons aS opS gd prog (semIr_masgn aS opS gd prog (x := mvi x) hv hdef hty)
    (hrest c'' hc')

/-- **Asm operation over the Jasmin code.** The translated and typed `copn o outs es` runs
when its typed operands evaluate, the asm semantics returns, and the outputs take the
results. -/
theorem sem_copn_step {o : String} {outs : List (Option JVar)} {es : List APExpr}
    {c : List AInstrR} {c' : List MInstr} (hc : translateCmdExt (copn o outs es :: c) = some c')
    {lvs' : List MLval}
    (hl : (outLvs (CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o outs.length) 0 outs).mapM
      translateLValExt = some lvs')
    {es' : List MPexpr} (he : es.mapM translatePExprExt = some es')
    {s s1 s2 : Estate SyscallState Mem} {vs rs : List Value}
    (hes : CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprs (Mem := Mem) true gd opS s
      (typeArgs (sopnTys (.Oasm o)) es') = .ok vs)
    (ho : aS.sopn_sem (.Oasm o) vs = .ok rs)
    (hw : writeLvals (Mem := Mem) true gd opS s (lvs'.map typeLv) rs = .ok s1)
    (hrest : ∀ c'', translateCmdExt c = some c'' → Sem aS opS gd prog s1 (typeC c'') s2) :
    Sem aS opS gd prog s (typeC c') s2 := by
  obtain ⟨i', c'', hi, hc', rfl⟩ := translateCmdExt_cons_inv hc
  have hi' : translateInstrRExt (copn o outs es) = some (.Copn lvs' .AT_none (.Oasm o) es') := by
    simp [copn, translateInstrRExt, hl, he, translateAssgnTag]
  rw [hi', Option.some.injEq] at hi
  subst hi
  exact sem_cons aS opS gd prog (semIr_mcopn aS opS gd prog hes ho hw) (hrest c'' hc')

/-- **Concatenation over the Jasmin code.** -/
theorem sem_append_step {a b : List AInstrR} {c' : List MInstr}
    (hc : translateCmdExt (a ++ b) = some c') {s s2 : Estate SyscallState Mem}
    (ha : ∀ a', translateCmdExt a = some a' → ∃ s1, Sem aS opS gd prog s (typeC a') s1 ∧
      ∀ b', translateCmdExt b = some b' → Sem aS opS gd prog s1 (typeC b') s2) :
    Sem aS opS gd prog s (typeC c') s2 := by
  obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv hc
  obtain ⟨s1, h1, h2⟩ := ha a' ha'
  rw [typeC_append]
  exact ComJasminBridgeProgram.sem_append aS opS gd prog h1 (h2 b' hb')

end Run

/-! ## 6. States after a binding -/

/-- The mirror state `s'` is `s` with the variable `y` holding a value of `R`, every other
variable outside the scratch variables unchanged, and the memory and syscall state
unchanged. -/
structure Post (s s' : Estate SyscallState Mem) (y : MVar) (R : Value → Prop) : Prop where
  /-- The syscall state is unchanged. -/
  scs : s'.escs = s.escs
  /-- The memory is unchanged. -/
  mem : s'.emem = s.emem
  /-- The variable `y` holds a value of `R`. -/
  res : R (s'.evm y)
  /-- Every other variable outside the scratch variables is unchanged. -/
  frame : ∀ z : MVar, z.vname ≠ y.vname → ¬ Scratch z.vname → s'.evm z = s.evm z
  /-- Array variables keep holding arrays of their sizes. -/
  arr : VmArrTyped s.evm → VmArrTyped s'.evm

/-- A write reads back. -/
@[simp] theorem set_same (vm : Vm) (x : MVar) (v : Value) : vm.set x v x = v := by
  simp [Vm.set]

/-- A write leaves a variable of another name unchanged. -/
theorem set_ne {vm : Vm} {x z : MVar} (v : Value) (h : z.vname ≠ x.vname) :
    vm.set x v z = vm z := by
  simp only [Vm.set]
  rw [if_neg (by intro h'; exact h (by simp only [decide_eq_true_eq] at h'; rw [h']))]

/-- A write of a defined value of the declared type keeps arrays at their sizes. -/
theorem arrTyped_set {vm : Vm} (h : VmArrTyped vm) {x : MVar} {v : Value}
    (hv : v.isDefined = true) (hty : v.typeOf = evalAtype x.vtype) :
    VmArrTyped (vm.set x v) := by
  intro y ws n hy
  by_cases hyx : y = x
  · subst hyx
    rw [hy] at hty
    simp only [set_same]
    cases v with
    | Varr m a =>
        simp only [Value.typeOf, evalAtype, CatCrypt.Crypto.Jasmin.CoqSemMirror.Ctype.carr.injEq]
          at hty
        subst hty
        exact ⟨a, rfl⟩
    | _ => simp_all [Value.typeOf, evalAtype, Value.isDefined]
  · simp only [Vm.set, decide_eq_true_eq, hyx, if_false]
    exact h y ws n hy

/-- A name of a scratch variable is not a name outside the scratch variables. -/
theorem ne_of_not_scratch {a b : String} (ha : ¬ Scratch a) (hb : Scratch b) : a ≠ b :=
  fun h => ha (h ▸ hb)

/-- The scratch registers are scratch variables. -/
theorem scratch_tmp (k : Nat) (ws : AWSize) : Scratch (mvar (tmp k ws)).vname :=
  Or.inr ⟨k, _, Or.inl rfl⟩

/-- The carry flag is a scratch variable. -/
theorem scratch_cf : Scratch mcf.v_var.vname := Or.inl rfl

/-- The loop indices of zeroing loops are scratch variables. -/
theorem scratch_idx (k : Nat) (s : ASType) : Scratch (mvar (mkV 'i' k s)).vname :=
  Or.inr ⟨k, s, Or.inr rfl⟩

omit [MemModel Mem] in
/-- The state `s` with the variables of `vm` is a `Post` state when `vm` satisfies its
three conditions. -/
theorem post_of {s : Estate SyscallState Mem} {vm : Vm} {y : MVar} {R : Value → Prop}
    (hres : R (vm y))
    (hframe : ∀ z : MVar, z.vname ≠ y.vname → ¬ Scratch z.vname → vm z = s.evm z)
    (harr : VmArrTyped s.evm → VmArrTyped vm) : Post s (s.withVm vm) y R :=
  ⟨rfl, rfl, hres, hframe, harr⟩

/-! ## 7. Word sizes, names and tables of the asm operations -/

/-- At a word size of `gprB`, `asmName base` is `opName base`. -/
theorem asmName_wsOf {ws : MWSize} (hg : gprB ws = true) (base : String) :
    asmName base (wsOf ws.bits) = opName base ws := by
  have h := asmName_eq_opName base
  cases ws
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2
  · simp [gprB] at hg
  · simp [gprB] at hg

/-- At a word size of `gprB`, `wsOf ws.bits` translates to `ws`. -/
theorem translateWSize_gpr {ws : MWSize} (_hg : gprB ws = true) :
    translateWSize (wsOf ws.bits) = some ws := by
  cases ws <;> rfl

/-- At a word size of `gprB`, `mws ws.bits` is `ws`. -/
theorem mws_gpr {ws : MWSize} (_hg : gprB ws = true) : mws ws.bits = ws := by
  cases ws <;> rfl

/-- The word sizes of `gprB` are those of the x86 general-purpose registers. -/
theorem wsOf_gpr_mem {ws : MWSize} (hg : gprB ws = true) :
    wsOf ws.bits ∈ [CatCrypt.Crypto.Jasmin.WSize.U8, .U16, .U32, .U64] := by
  cases ws <;> simp_all [gprB] <;> decide

/-- The types of the `_` outputs of the asm operations of the lowering at the word sizes of
the x86 general-purpose registers: five flags and a word for `ADD`, `ADC`, `NEG`, `ANDN`,
five flags for `CMP`, and two words for `MULX_lo_hi`. -/
theorem opnNoneTys_gpr : ∀ ws ∈ [CatCrypt.Crypto.Jasmin.WSize.U8, .U16, .U32, .U64],
    CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys (asmName "ADD" ws) 6 =
        List.replicate 5 .sbool ++ [.sword ws] ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys (asmName "ADC" ws) 6 =
        List.replicate 5 .sbool ++ [.sword ws] ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys (asmName "NEG" ws) 6 =
        List.replicate 5 .sbool ++ [.sword ws] ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys (asmName "ANDN" ws) 6 =
        List.replicate 5 .sbool ++ [.sword ws] ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys (asmName "CMP" ws) 5 =
        List.replicate 5 .sbool ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys (asmName "MULX_lo_hi" ws) 2 =
        [.sword ws, .sword ws] :=
  CatCrypt.Crypto.Jasmin.JazzToInstrR.gprAsm_opnNoneTys

/-- The `b5w_ty` outputs with the carry flag and the word `x` translate to `mCWOuts`. -/
theorem mapM_outsCW {o : String} {ws : AWSize}
    (ho : CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o 6 =
      List.replicate 5 .sbool ++ [.sword ws]) {x : JVar} (hx : OkV x) :
    (outLvs (CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o (outsCW x).length) 0
      (outsCW x)).mapM translateLValExt = some (mCWOuts (mvi x)) := by
  have hl : (outsCW x).length = 6 := rfl
  rw [hl, ho]
  simp only [outsCW, outLvs, List.replicate, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
    translateLValExt_lvv (translateVarIExt_mvi hx), translateLValExt_lvv translateVarIExt_cf]
  rfl

/-- The `b5w_ty` outputs with the word `x` only translate to `mWOuts`. -/
theorem mapM_outsW {o : String} {ws : AWSize}
    (ho : CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o 6 =
      List.replicate 5 .sbool ++ [.sword ws]) {x : JVar} (hx : OkV x) :
    (outLvs (CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o (outsW x).length) 0
      (outsW x)).mapM translateLValExt = some (mWOuts (mvi x)) := by
  have hl : (outsW x).length = 6 := rfl
  rw [hl, ho]
  simp only [outsW, outLvs, List.replicate, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
    translateLValExt_lvv (translateVarIExt_mvi hx)]
  rfl

/-- The `b5_ty` outputs with the carry flag translate to the flag outputs of `CMP`. -/
theorem mapM_outsCmp {o : String}
    (ho : CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o 5 = List.replicate 5 .sbool) :
    (outLvs (CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o
      ([none, some cfVar, none, none, none] : List (Option JVar)).length) 0
      [none, some cfVar, none, none, none]).mapM translateLValExt =
      some [mnb, .Lvar mcf, mnb, mnb, mnb] := by
  have hl : ([none, some cfVar, none, none, none] : List (Option JVar)).length = 5 := rfl
  rw [hl, ho]
  simp only [outLvs, List.replicate, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some]
  simp only [List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
    translateLValExt_lvv translateVarIExt_cf]
  rfl

/-- The outputs of `MULX_lo_hi` at a word size `ws` with the high word `x` translate to a
discarded word of that size and `x`. -/
theorem mapM_outsMulx {o : String} {ws : MWSize}
    (ho : CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o 2 =
      [.sword (wsOf ws.bits), .sword (wsOf ws.bits)]) {x : JVar} (hx : OkV x) :
    (outLvs (CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys o
      ([none, some x] : List (Option JVar)).length) 0 [none, some x]).mapM translateLValExt =
      some [.Lnone () (.aword ws), .Lvar (mvi x)] := by
  have hl : ([none, some x] : List (Option JVar)).length = 2 := rfl
  have hn : translateLValExt (.Lnone vi0 (.sword (wsOf ws.bits))) =
      some (.Lnone () (.aword ws)) := by
    cases ws <;> rfl
  rw [hl, ho]
  simp only [outLvs, List.getElem?_cons_zero, Option.getD_some]
  simp only [List.mapM_cons, List.mapM_nil, hn, translateLValExt_lvv (translateVarIExt_mvi hx)]
  rfl

/-- The `_` outputs of `ROR` at a word size of `gprB`: the flags `of cf` and a word. -/
theorem opnNoneTys_ror {ws : MWSize} (hg : gprB ws = true) :
    CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys (asmName "ROR" (wsOf ws.bits)) 3 =
      [.sbool, .sbool, .sword (wsOf ws.bits)] :=
  CatCrypt.Crypto.Jasmin.JazzToInstrR.rorAsm_opnNoneTys _ (by
    have h := wsOf_gpr_mem hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h <;> simp [h])

/-- The `b2w_ty` outputs of `ROR` with the word `x` translate to two discarded flags and
`x`. -/
theorem mapM_outsRor {ws : MWSize} (hg : gprB ws = true) {x : JVar} (hx : OkV x) :
    (outLvs (CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys (asmName "ROR" (wsOf ws.bits))
      ([none, none, some x] : List (Option JVar)).length) 0 [none, none, some x]).mapM
      translateLValExt = some [mnb, mnb, .Lvar (mvi x)] := by
  have hl : ([none, none, some x] : List (Option JVar)).length = 3 := rfl
  rw [hl, opnNoneTys_ror hg]
  simp only [outLvs, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
    translateLValExt_lvv (translateVarIExt_mvi hx)]
  rfl

/-- The operand types of `ROR` at a word size of `gprB`: a word and a `u8` count. -/
theorem jazzArgTys_ror {ws : MWSize} (hg : gprB ws = true) :
    JazzAsmSem.jazzArgTys (opName "ROR" ws) = some [.aword ws, .aword .U8] := by
  cases ws <;> simp_all [gprB, JazzAsmSem.jazzArgTys, JazzAsmSem.jazzRows, opName,
    JazzAsmSem.wsName, JazzAsmSem.rowArgTys]

/-- The reads of translated locals. -/
theorem mapM_pv_mvi : ∀ {xs : List JVar}, (∀ v ∈ xs, OkV v) →
    (xs.map pv).mapM translatePExprExt = some (xs.map fun v => mpv (mvi v))
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.map_cons, List.mapM_cons,
        translatePExprExt_pv (translateVarIExt_mvi (h x List.mem_cons_self)),
        mapM_pv_mvi (fun v hv => h v (List.mem_cons_of_mem _ hv))]
      rfl

/-- The typing leaves reads unchanged. -/
theorem typeArgs_mpv : ∀ (tys : List MAtype) (xs : List MVarI),
    typeArgs tys (xs.map mpv) = xs.map mpv
  | [], _ => by simp [typeArgs]
  | _ :: _, [] => rfl
  | _ :: tys, _ :: xs => by
      simp only [List.map_cons, typeArgs]
      exact congrArg _ (typeArgs_mpv tys xs)

/-! ## 8. Writes of the outputs of the asm operations -/

section Outs
variable (gd : GlobDecls) (opS : OpSem)

/-- A flag value of a discarded Boolean output is accepted. -/
theorem writeLval_flag (s : Estate SyscallState Mem) (f : CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.JFlag) :
    writeLval (Mem := Mem) true gd opS mnb (JazzAsmSem.flagVal f) s = .ok s := by
  apply writeLval_lnone
  · cases f <;> rfl
  · cases f <;> rfl

/-- The outputs `mCWOuts x` of a `b5w_ty` result whose carry flag is `cb`. -/
theorem writeLvals_CW (s : Estate SyscallState Mem) {ws : MWSize}
    (r : CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.B5W ws.bits) {cb : Bool}
    (hcf : r.cf = some cb) {x : MVarI} (hx : x.v_var.vtype = .aword ws) :
    writeLvals (Mem := Mem) true gd opS s ((mCWOuts x).map typeLv) (JazzAsmSem.b5wVals ws r) =
      .ok (s.withVm ((s.evm.set mcf.v_var (.Vbool cb)).set x.v_var (.Vword ws r.word))) := by
  rw [show (mCWOuts x).map typeLv = mCWOuts x from rfl]
  simp only [mCWOuts, JazzAsmSem.b5wVals, JazzAsmSem.b5Vals, List.cons_append, List.nil_append,
    writeLvals, JResult.fold2, JResult.monad_bind_eq, writeLval_flag, JResult.bind_ok, hcf]
  rw [show JazzAsmSem.flagVal (some cb) = .Vbool cb from rfl, writeLval_lvar opS gd rfl rfl]
  simp only [JResult.bind_ok]
  rw [writeLval_lvar opS gd rfl (by rw [hx]; rfl)]
  rfl

/-- The outputs `mWOuts x` of a `b5w_ty` result. -/
theorem writeLvals_W (s : Estate SyscallState Mem) {ws : MWSize}
    (r : CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.B5W ws.bits) {x : MVarI}
    (hx : x.v_var.vtype = .aword ws) :
    writeLvals (Mem := Mem) true gd opS s ((mWOuts x).map typeLv) (JazzAsmSem.b5wVals ws r) =
      .ok (s.withVm (s.evm.set x.v_var (.Vword ws r.word))) := by
  rw [show (mWOuts x).map typeLv = mWOuts x from rfl]
  simp only [mWOuts, JazzAsmSem.b5wVals, JazzAsmSem.b5Vals, List.cons_append, List.nil_append,
    writeLvals, JResult.fold2, JResult.monad_bind_eq, writeLval_flag, JResult.bind_ok]
  rw [writeLval_lvar opS gd rfl (by rw [hx]; rfl)]
  rfl

/-- The flag outputs of `CMP` whose carry flag is `cb`. -/
theorem writeLvals_cmp (s : Estate SyscallState Mem) {w : Nat}
    (r : CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.B5W w) {cb : Bool}
    (hcf : r.cf = some cb) :
    writeLvals (Mem := Mem) true gd opS s
      (([mnb, .Lvar mcf, mnb, mnb, mnb] : List MLval).map typeLv) (JazzAsmSem.b5Vals r) =
      .ok (s.withVm (s.evm.set mcf.v_var (.Vbool cb))) := by
  rw [show ([mnb, .Lvar mcf, mnb, mnb, mnb] : List MLval).map typeLv =
    [mnb, .Lvar mcf, mnb, mnb, mnb] from rfl]
  simp only [JazzAsmSem.b5Vals, writeLvals, JResult.fold2, JResult.monad_bind_eq, writeLval_flag,
    JResult.bind_ok, hcf]
  rw [show JazzAsmSem.flagVal (some cb) = .Vbool cb from rfl, writeLval_lvar opS gd rfl rfl]
  simp only [JResult.bind_ok]

/-- The outputs of `MULX_lo_hi` at a word size `ws`: the low word discarded, the high word
to `x`. -/
theorem writeLvals_mulx (s : Estate SyscallState Mem) {ws : MWSize} (lo hi : BitVec ws.bits)
    {x : MVarI} (hx : x.v_var.vtype = .aword ws) :
    writeLvals (Mem := Mem) true gd opS s
      (([.Lnone () (.aword ws), .Lvar x] : List MLval).map typeLv)
      [.Vword ws lo, .Vword ws hi] =
      .ok (s.withVm (s.evm.set x.v_var (.Vword ws hi))) := by
  rw [show (([.Lnone () (.aword ws), .Lvar x] : List MLval).map typeLv) =
    [.Lnone () (.aword ws), .Lvar x] from rfl]
  simp only [writeLvals, JResult.fold2, JResult.monad_bind_eq]
  rw [writeLval_lnone opS gd (by cases ws <;> rfl) rfl, JResult.bind_ok, writeLval_lvar opS gd
    rfl (by rw [hx]; rfl)]
  rfl

/-- The outputs of `ROR`: the two flags discarded, the word to `x`. -/
theorem writeLvals_ror (s : Estate SyscallState Mem) {ws : MWSize}
    (r : CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.B2W ws.bits) {x : MVarI}
    (hx : x.v_var.vtype = .aword ws) :
    writeLvals (Mem := Mem) true gd opS s (([mnb, mnb, .Lvar x] : List MLval).map typeLv)
      (JazzAsmSem.b2wVals ws r) = .ok (s.withVm (s.evm.set x.v_var (.Vword ws r.word))) := by
  rw [show ([mnb, mnb, .Lvar x] : List MLval).map typeLv = [mnb, mnb, .Lvar x] from rfl]
  simp only [JazzAsmSem.b2wVals, writeLvals, JResult.fold2, JResult.monad_bind_eq,
    writeLval_flag, JResult.bind_ok]
  rw [writeLval_lvar opS gd rfl (by rw [hx]; rfl)]
  rfl

end Outs

/-! ## 9. Word facts -/

/-- A word size of `gprB` has a width of `widthOkB`. -/
theorem widthOkB_bits {ws : MWSize} (hg : gprB ws = true) : widthOkB ws.bits = true := by
  cases ws <;> first | rfl | simp [gprB] at hg

/-- The mirror word size of a width of `bitOkB` is a word size of `gprB`. -/
theorem gprB_mws {w : Nat} (h : bitOkB w = true) : gprB (mws w) = true := by
  simp only [bitOkB, widthOkB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | ((h | h) | h) | h <;> subst h <;> rfl

/-- The shift masks of the word sizes of `gprB` ignore the bits of the count above `u8`. -/
theorem shiftMask_mod256 {ws : MWSize} (hg : gprB ws = true) (k : Nat) :
    shiftMask ws.bits (k % 256) = shiftMask ws.bits k := by
  cases ws <;> simp [gprB, shiftMask, CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.bits] at hg ⊢

/-- The shift masks of the word sizes of `gprB` are idempotent. -/
theorem shiftMask_idem {ws : MWSize} (hg : gprB ws = true) (k : Nat) :
    shiftMask ws.bits (shiftMask ws.bits k) = shiftMask ws.bits k := by
  cases ws <;> simp [gprB, shiftMask, CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.bits] at hg ⊢

/-- The shift masks of the word sizes of `gprB` are below `64`. -/
theorem shiftMask_lt {ws : MWSize} (hg : gprB ws = true) (k : Nat) :
    shiftMask ws.bits k < 64 := by
  cases ws <;> simp [gprB, shiftMask, CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.bits] at hg ⊢ <;>
    omega

/-- The `u8` word of a count below `256`. -/
theorem toNat_ofInt_u8 {m : Nat} (hm : m < 256) :
    (BitVec.ofInt (CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits) (m : Int)).toNat % 256 = m := by
  show (BitVec.ofInt 8 (m : Int)).toNat % 256 = m
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

/-- The binary operations of `regArith` other than `andn` translate to mirror operators
whose equations are `JasminBinOp.apply`. -/
theorem binSop_sem {opS : OpSem} (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true)
    {bop : JasminBinOp} (hb : bop ≠ .andn) :
    ∃ mop, translateSOp2Ext (binSop (wsOf ws.bits) bop) = some mop ∧
      ∀ a b : BitVec ws.bits,
        opS.sem_sop2 mop (.Vword ws a) (.Vword ws b) = .ok (.Vword ws (bop.apply a b)) := by
  have hws := translateWSize_gpr hg
  cases bop
  · exact ⟨.Oadd (.Op_w ws), by simp [binSop, translateSOp2Ext, translateSOp2, hws],
      hop.add ws hg⟩
  · exact ⟨.Osub (.Op_w ws), by simp [binSop, translateSOp2Ext, translateSOp2, hws],
      hop.sub ws hg⟩
  · exact ⟨.Omul (.Op_w ws), by simp [binSop, translateSOp2Ext, translateSOp2, hws],
      hop.mul ws hg⟩
  · exact ⟨.Oland ws, by simp [binSop, translateSOp2Ext, translateSOp2, hws], hop.land ws hg⟩
  · exact ⟨.Olor ws, by simp [binSop, translateSOp2Ext, translateSOp2, hws], hop.lor ws hg⟩
  · exact ⟨.Olxor ws, by simp [binSop, translateSOp2Ext, translateSOp2, hws], hop.lxor ws hg⟩
  · refine ⟨.Olsl (.Op_w ws), by simp [binSop, translateSOp2Ext, translateSOp2, hws],
      fun a b => ?_⟩
    rw [hop.lsl ws ws hg hg a b, shiftMask_mod256 hg]; rfl
  · refine ⟨.Olsr ws, by simp [binSop, translateSOp2Ext, translateSOp2, hws], fun a b => ?_⟩
    rw [hop.lsr ws ws hg hg a b, shiftMask_mod256 hg]; rfl
  · exact absurd rfl hb

/-! ## 10. The code of each operation -/

section Ops
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- **Register arithmetic.** `x = a; x = x OP b` writes `bop.apply a b` to `x`. -/
theorem sem_regArith (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true)
    {bop : JasminBinOp} (hb : bop ≠ .andn) {x a b : JVar} (hx : OkV x) (ha : OkV a)
    (hb' : OkV b) (hxt : (mvar x).vtype = .aword ws) (hbx : b.vname ≠ x.vname)
    {s : Estate SyscallState Mem} {va vb : BitVec ws.bits}
    (hva : s.evm (mvar a) = .Vword ws va) (hvb : s.evm (mvar b) = .Vword ws vb)
    {c' : List MInstr}
    (hc : translateCmdExt [asgn x (pv a),
      asgn x (.Papp2 (binSop (wsOf ws.bits) bop) (pv x) (pv b))] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws (bop.apply va vb)) := by
  obtain ⟨mop, hmop, hsem⟩ := binSop_sem hop hg hb
  have hty : ∀ u : BitVec ws.bits, (Value.Vword ws u).typeOf = evalAtype (mvar x).vtype :=
    fun _ => by rw [hxt]; rfl
  refine ⟨s.withVm ((s.evm.set (mvar x) (.Vword ws va)).set (mvar x)
    (.Vword ws (bop.apply va vb))), ?_, post_of (by simp) ?_ ?_⟩
  · refine sem_asgn_step aS opS gd prog hx (translatePExprExt_pv (translateVarIExt_mvi ha)) hc
      (semPexpr_mpv opS gd hva rfl) rfl (hty va) (fun c1 hc1 => ?_)
    refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp2 hmop
      (translatePExprExt_pv (translateVarIExt_mvi hx))
      (translatePExprExt_pv (translateVarIExt_mvi hb'))) hc1 ?_ rfl (hty _)
      (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    show semPexpr (Mem := Mem) true gd opS _ (.Papp2 mop (mpv (mvi x)) (mpv (mvi b))) = _
    rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
      (semPexpr_mpv opS gd ((set_ne _ hbx).trans hvb) rfl), hsem]
  · intro z hz _
    rw [set_ne _ hz, set_ne _ hz]
  · exact fun h => arrTyped_set (arrTyped_set h rfl (hty _)) rfl (hty _)

/-- **And-not.** `_, _, _, _, _, x = #ANDN(a, b)` writes `~~~a &&& b` to `x`. -/
theorem sem_andn (haS : JazzAsmAgrees aS) {ws : MWSize} (hg : gprB ws = true)
    (hbm : bmiB ws = true) {x a b : JVar} (hx : OkV x) (ha : OkV a) (hb : OkV b)
    (hxt : (mvar x).vtype = .aword ws) {s : Estate SyscallState Mem} {va vb : BitVec ws.bits}
    (hva : s.evm (mvar a) = .Vword ws va) (hvb : s.evm (mvar b) = .Vword ws vb)
    {c' : List MInstr}
    (hc : translateCmdExt [copn (asmName "ANDN" (wsOf ws.bits)) (outsW x) [pv a, pv b]] =
      some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws ((~~~va) &&& vb)) := by
  have ho := (opnNoneTys_gpr _ (wsOf_gpr_mem hg)).2.2.2.1
  have hbm' : bmiOkB ws.bits = true := by cases ws <;> simp_all [bmiB] <;> rfl
  have hmem : asmName "ANDN" (wsOf ws.bits) ∈ jazzOps :=
    ((asmName_mem_jazzOps (widthOkB_bits hg)).2.2.2.2 hbm').1
  refine ⟨s.withVm (s.evm.set (mvar x) (.Vword ws ((~~~va) &&& vb))), ?_,
    post_of (by simp) ?_ ?_⟩
  · refine sem_copn_step aS opS gd prog (vs := [.Vword ws va, .Vword ws vb]) hc
      (mapM_outsW ho hx) (mapM_pv_mvi (xs := [a, b]) (by simp [ha, hb])) ?_ ?_
      (writeLvals_W gd opS s (CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.x86_ANDN va vb)
        (x := mvi x) hxt) (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    · rw [show [a, b].map (fun v => mpv (mvi v)) = [mvi a, mvi b].map mpv from rfl, typeArgs_mpv]
      exact semPexprs_cons opS gd (semPexpr_mpv opS gd hva rfl)
        (semPexprs_cons opS gd (semPexpr_mpv opS gd hvb rfl) (semPexprs_nil opS gd s))
    · rw [haS _ hmem, asmName_wsOf hg]
      exact JazzAsmSem.jazzAsmSem_andn ws hbm va vb
  · intro z hz _
    rw [set_ne _ hz]
  · exact fun h => arrTyped_set h rfl (by rw [hxt]; rfl)

/-- **Constant.** `x = (ws) z` writes the word of `z` to `x`. -/
theorem sem_regConst (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true) {x : JVar}
    (hx : OkV x) (hxt : (mvar x).vtype = .aword ws) {s : Estate SyscallState Mem} {z : Int}
    {c' : List MInstr} (hc : translateCmdExt [asgn x (cnst z)] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws (BitVec.ofInt ws.bits z)) := by
  refine ⟨s.withVm (s.evm.set (mvar x) (.Vword ws (BitVec.ofInt ws.bits z))), ?_,
    post_of (by simp) ?_ ?_⟩
  · refine sem_asgn_step aS opS gd prog hx (translatePExprExt_cnst z) hc ?_ rfl
      (by rw [hxt]; rfl) (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    rw [hxt]
    exact semPexpr_wconst opS gd hop hg _ z
  · intro z hz _
    rw [set_ne _ hz]
  · exact fun h => arrTyped_set h rfl (by rw [hxt]; rfl)

/-- **Immediate shift.** `x = a; x = x OP m` with the count `m` typed `u8`. -/
theorem sem_shiftImm (hop : JazzOpAgrees opS) {ws : MWSize} (_hg : gprB ws = true)
    {sop : ASOp2} {mop : MSOp2} (hsop : translateSOp2Ext sop = some mop)
    (hty2 : (op2Tys mop).2 = .aword .U8) {m : Nat} {f : BitVec ws.bits → BitVec ws.bits}
    (hsem : ∀ a, opS.sem_sop2 mop (.Vword ws a) (.Vword .U8
      (BitVec.ofInt CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits (m : Int))) =
      .ok (.Vword ws (f a)))
    {x a : JVar} (hx : OkV x) (ha : OkV a) (hxt : (mvar x).vtype = .aword ws)
    {s : Estate SyscallState Mem} {va : BitVec ws.bits} (hva : s.evm (mvar a) = .Vword ws va)
    {c' : List MInstr}
    (hc : translateCmdExt [asgn x (pv a), asgn x (.Papp2 sop (pv x) (cnst (m : Int)))] =
      some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ Post s s' (mvar x) (· = .Vword ws (f va)) := by
  have hty : ∀ u : BitVec ws.bits, (Value.Vword ws u).typeOf = evalAtype (mvar x).vtype :=
    fun _ => by rw [hxt]; rfl
  refine ⟨s.withVm ((s.evm.set (mvar x) (.Vword ws va)).set (mvar x) (.Vword ws (f va))), ?_,
    post_of (by simp) ?_ ?_⟩
  · refine sem_asgn_step aS opS gd prog hx (translatePExprExt_pv (translateVarIExt_mvi ha)) hc
      (semPexpr_mpv opS gd hva rfl) rfl (hty va) (fun c1 hc1 => ?_)
    refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp2 hsop
      (translatePExprExt_pv (translateVarIExt_mvi hx)) (translatePExprExt_cnst _)) hc1 ?_ rfl
      (hty _) (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    rw [show typeE (mvar x).vtype (.Papp2 mop (mpv (mvi x)) (.Pconst (m : Int))) =
      .Papp2 mop (mpv (mvi x)) (typeConst (op2Tys mop).2 (m : Int)) from rfl, hty2,
      semPexpr_papp2 opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (semPexpr_wconst opS gd hop rfl _ _), hsem]
  · intro z hz _
    rw [set_ne _ hz, set_ne _ hz]
  · exact fun h => arrTyped_set (arrTyped_set h rfl (hty _)) rfl (hty _)

/-- **High multiply.** At a word size of `bmiB`, `_, x = #MULX_lo_hi_NN(a, b)` writes the
high word. -/
theorem sem_mulhi (haS : JazzAsmAgrees aS) {ws : MWSize} (hg : gprB ws = true)
    (hbm : bmiB ws = true) {x a b : JVar} (hx : OkV x) (ha : OkV a)
    (hb : OkV b) (hxt : (mvar x).vtype = .aword ws) {s : Estate SyscallState Mem}
    {va vb : BitVec ws.bits} (hva : s.evm (mvar a) = .Vword ws va)
    (hvb : s.evm (mvar b) = .Vword ws vb) {c' : List MInstr}
    (hc : translateCmdExt
      [copn (asmName "MULX_lo_hi" (wsOf ws.bits)) [none, some x] [pv a, pv b]] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws (mulHiW va vb)) := by
  have ho := (opnNoneTys_gpr _ (wsOf_gpr_mem hg)).2.2.2.2.2
  have hbm' : bmiOkB ws.bits = true := by cases ws <;> simp_all [bmiB] <;> rfl
  have hmem : asmName "MULX_lo_hi" (wsOf ws.bits) ∈ jazzOps :=
    ((asmName_mem_jazzOps (widthOkB_bits hg)).2.2.2.2 hbm').2
  refine ⟨s.withVm (s.evm.set (mvar x) (.Vword ws (mulHiW va vb))), ?_,
    post_of (by simp) ?_ ?_⟩
  · refine sem_copn_step aS opS gd prog (vs := [.Vword ws va, .Vword ws vb]) hc
      (mapM_outsMulx ho hx)
      (mapM_pv_mvi (xs := [a, b]) (by simp [ha, hb])) ?_ ?_
      (writeLvals_mulx gd opS s
        (CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.x86_MULX_lo_hi va vb).1
        (mulHiW va vb) (x := mvi x) hxt) (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    · rw [show [a, b].map (fun v => mpv (mvi v)) = [mvi a, mvi b].map mpv from rfl, typeArgs_mpv]
      exact semPexprs_cons opS gd (semPexpr_mpv opS gd hva rfl)
        (semPexprs_cons opS gd (semPexpr_mpv opS gd hvb rfl) (semPexprs_nil opS gd s))
    · rw [haS _ hmem, asmName_wsOf hg]
      exact JazzAsmSem.jazzAsmSem_mulx_lo_hi ws hbm va vb
  · intro z hz _
    rw [set_ne _ hz]
  · exact fun h => arrTyped_set h rfl (by rw [hxt]; rfl)

/-- At a word size of `gprB` and a count `m` below its width, the word of `x86_ROR` at the
`u8` count `m` is `rotateRight m`. -/
theorem x86_ROR_word {ws : MWSize} (hg : gprB ws = true) (a : BitVec ws.bits) {m : Nat}
    (hm : m < ws.bits) :
    (CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.x86_ROR a
      ((BitVec.ofInt CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits (m : Int)).setWidth
        ws.bits)).word = a.rotateRight m := by
  have h64 : ws.bits ≤ 64 := by cases ws <;> simp_all [gprB] <;> decide
  have hp : ws.bits < 2 ^ ws.bits := by cases ws <;> simp_all [gprB] <;> decide
  have h8 : (BitVec.ofInt CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits (m : Int)).toNat =
      m := by
    have h1 := toNat_ofInt_u8 (m := m) (by omega)
    have h2 := (BitVec.ofInt CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits (m : Int)).isLt
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_eq h2 (by rfl))] at h1
    exact h1
  have hc : CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.shiftCount
      ((BitVec.ofInt CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits (m : Int)).setWidth
        ws.bits) = m := by
    unfold CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.shiftCount
    rw [BitVec.toNat_setWidth, h8, Nat.mod_eq_of_lt (by omega)]
    exact shiftMask_of_lt hm
  simp only [CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.x86_ROR, hc]
  split_ifs with h0
  · subst h0
    simp [BitVec.rotateRight_def]
  all_goals exact (rorImm_denote_eq_shiftOr m hm a).symm

/-- **Immediate rotate.** `x = a; _, _, x = #ROR(x, m)` with the count `m` below the width
typed `u8` writes `rotateRight m` of `a` to `x`. -/
theorem sem_ror (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {ws : MWSize}
    (hg : gprB ws = true) {m : Nat} (hm : m < ws.bits) {x a : JVar} (hx : OkV x) (ha : OkV a)
    (hxt : (mvar x).vtype = .aword ws) {s : Estate SyscallState Mem} {va : BitVec ws.bits}
    (hva : s.evm (mvar a) = .Vword ws va) {c' : List MInstr}
    (hc : translateCmdExt [asgn x (pv a), copn (asmName "ROR" (wsOf ws.bits))
      [none, none, some x] [pv x, cnst (m : Int)]] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws (va.rotateRight m)) := by
  have hty : ∀ u : BitVec ws.bits, (Value.Vword ws u).typeOf = evalAtype (mvar x).vtype :=
    fun _ => by rw [hxt]; rfl
  have hmem : asmName "ROR" (wsOf ws.bits) ∈ jazzOps :=
    asmName_ror_mem_jazzOps (widthOkB_bits hg)
  refine ⟨s.withVm ((s.evm.set (mvar x) (.Vword ws va)).set (mvar x)
    (.Vword ws (va.rotateRight m))), ?_, post_of (by simp) ?_ ?_⟩
  · refine sem_asgn_step aS opS gd prog hx (translatePExprExt_pv (translateVarIExt_mvi ha)) hc
      (semPexpr_mpv opS gd hva rfl) rfl (hty va) (fun c1 hc1 => ?_)
    have hw := writeLvals_ror gd opS (s.withVm (s.evm.set (mvar x) (.Vword ws va)))
      (CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.x86_ROR va
        ((BitVec.ofInt CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits (m : Int)).setWidth
          ws.bits)) (x := mvi x) hxt
    rw [x86_ROR_word hg va hm] at hw
    refine sem_copn_step aS opS gd prog
      (vs := [.Vword ws va, .Vword .U8 (BitVec.ofInt _ (m : Int))]) hc1
      (mapM_outsRor hg hx) (es' := [mpv (mvi x), .Pconst (m : Int)]) ?_ ?_ ?_ hw
      (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    · simp only [List.mapM_cons, List.mapM_nil, translatePExprExt_pv (translateVarIExt_mvi hx),
        translatePExprExt_cnst]
      rfl
    · rw [show sopnTys (.Oasm (asmName "ROR" (wsOf ws.bits))) = [.aword ws, .aword .U8] by
        simp only [sopnTys, asmName_wsOf hg, jazzArgTys_ror hg, Option.getD_some]]
      exact semPexprs_cons opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (semPexprs_cons opS gd (semPexpr_wconst opS gd hop rfl _ _) (semPexprs_nil opS gd _))
    · rw [haS _ hmem, asmName_wsOf hg]
      exact JazzAsmSem.jazzAsmSem_ror ws hg va _
  · intro z hz _
    rw [set_ne _ hz, set_ne _ hz]
  · exact fun h => arrTyped_set (arrTyped_set h rfl (hty _)) rfl (hty _)

end Ops

/-! ## 11. Stack arrays -/

/-- A word size of `gprB` has eight bits per byte. -/
theorem bits_eq_bytes {ws : MWSize} (_hg : gprB ws = true) : ws.bits = 8 * ws.bytes := by
  cases ws <;> rfl

/-- A word of a size of `gprB` has fewer values than its bytes. -/
theorem toNat_lt_bytes {ws : MWSize} (hg : gprB ws = true) (v : BitVec ws.bits) :
    v.toNat < 256 ^ ws.bytes := by
  have h : v.toNat < 2 ^ ws.bits := v.isLt
  have he : (2 : Nat) ^ ws.bits = 256 ^ ws.bytes := by
    rw [bits_eq_bytes hg, Nat.pow_mul]
  omega

/-- An element `i < n` of an array of `n` words of `ws.bytes` bytes is an access in range. -/
theorem accessOk_scaled {n : Nat} (ws : MWSize) {i : Nat} (hi : i < n) :
    JArrayMirror.AccessOk (n * ws.bytes) .Unaligned ws
      ((i : Int) * JArrayMirror.scale .AAscale ws) := by
  have h : (i + 1) * ws.bytes ≤ n * ws.bytes := Nat.mul_le_mul_right _ hi
  refine ⟨Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _), ?_,
    fun h => by cases h⟩
  simp only [JArrayMirror.scale]
  rw [show ((i : Int) * (ws.bytes : Int)).toNat = i * ws.bytes by omega]
  rw [Nat.succ_mul] at h
  exact h

/-- The scaled read of the element `i < n`. -/
theorem getWord_scaled {n : Nat} (ws : MWSize) (arr : JArrayMirror (n * ws.bytes)) {i : Nat}
    (hi : i < n) :
    JArrayMirror.getWord arr .Unaligned .AAscale ws (i : Int) =
      .ok (BitVec.ofNat ws.bits (arr.readLE (i * ws.bytes) ws.bytes)) := by
  unfold JArrayMirror.getWord
  rw [if_pos (accessOk_scaled ws hi)]
  simp only [JArrayMirror.scale]
  rw [show ((i : Int) * (ws.bytes : Int)).toNat = i * ws.bytes by omega]

/-- The scaled write of the element `i < n`. -/
theorem setWord_scaled {n : Nat} (ws : MWSize) (arr : JArrayMirror (n * ws.bytes)) {i : Nat}
    (hi : i < n) (v : BitVec ws.bits) :
    JArrayMirror.setWord arr .Unaligned .AAscale ws (i : Int) v =
      .ok (arr.writeLE (i * ws.bytes) ws.bytes v.toNat) := by
  unfold JArrayMirror.setWord
  rw [if_pos (accessOk_scaled ws hi)]
  simp only [JArrayMirror.scale]
  rw [show ((i : Int) * (ws.bytes : Int)).toNat = i * ws.bytes by omega]

/-- **Array agreement after a store.** The bytes of an array holding `A` after the write of
`v` at the element `i` hold `stackSet A i v`. -/
theorem readLE_store {ws : MWSize} (hg : gprB ws = true) {n : Nat} {A : Fin n → BitVec ws.bits}
    {arr : JArrayMirror (n * ws.bytes)}
    (h : ∀ j : Fin n, arr.readLE (j.val * ws.bytes) ws.bytes = (A j).toNat) {i : Nat}
    (hi : i < n) (v : BitVec ws.bits) (j : Fin n) :
    (arr.writeLE (i * ws.bytes) ws.bytes v.toNat).readLE (j.val * ws.bytes) ws.bytes =
      (stackSet A i v j).toNat := by
  have hs := stackSet_fin A ⟨i, hi⟩ v
  simp only at hs
  rw [hs]
  dsimp only
  by_cases hj : j = ⟨i, hi⟩
  · subst hj
    rw [if_pos rfl, ComJasminBridgeArrWord.readLE_writeLE_same arr _ _ _
      (by have := Nat.mul_le_mul_right ws.bytes hi; rw [Nat.succ_mul] at this; exact this),
      Nat.mod_eq_of_lt (toNat_lt_bytes hg v)]
  · rw [if_neg hj, ComJasminBridgeArrWord.readLE_writeLE_disjoint, h j]
    have hne : j.val ≠ i := fun e => hj (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · left
      have := Nat.mul_le_mul_right ws.bytes hlt
      rw [Nat.succ_mul] at this
      exact this
    · right
      have := Nat.mul_le_mul_right ws.bytes hlt
      rw [Nat.succ_mul] at this
      exact this

section Arr
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

omit [MemModel Mem] in
/-- A local variable holding a defined value reads as a `getGvar`. -/
theorem getGvar_mkLvar {s : Estate SyscallState Mem} {x : MVarI} {v : Value}
    (h : s.evm x.v_var = v) (hv : v.isDefined = true) :
    CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar true gd s.evm (mkLvar x) = .ok v := by
  unfold CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar
  rw [show (mkLvar x).isLvar = true from rfl, if_pos rfl]
  show getVar true s.evm x.v_var = _
  unfold getVar
  simp [Vm.get, h, hv]

/-- **Array read.** A scaled read of the array variable `x` at an evaluated index. -/
theorem semPexpr_pget {s : Estate SyscallState Mem} {x : MVarI} {N : Nat}
    {arr : JArrayMirror N} (hx : s.evm x.v_var = .Varr N arr) {e : MPexpr} {i : Int}
    (he : semPexpr (Mem := Mem) true gd opS s e = .ok (.Vint i)) (ws : MWSize) :
    semPexpr (Mem := Mem) true gd opS s (.Pget .Unaligned .AAscale ws (mkLvar x) e) =
      JResult.bind (JArrayMirror.getWord arr .Unaligned .AAscale ws i)
        (fun w => .ok (.Vword ws w)) := by
  have hg := getGvar_mkLvar gd hx rfl
  cases ws
  · rw [JArrayMirror.getWord_U8]
    simp only [semPexpr, hg, he, JResult.monad_bind_eq, JResult.bind_ok, Value.toInt]
    split <;> rfl
  all_goals simp only [semPexpr, hg, he, JResult.monad_bind_eq, JResult.bind_ok, Value.toInt]

/-- **Array write.** A scaled write of a word to the array variable `x` at an evaluated
index. -/
theorem writeLval_of_setWord {s : Estate SyscallState Mem} {x : MVarI} {N : Nat}
    {arr : JArrayMirror N} (hx : s.evm x.v_var = .Varr N arr)
    (hxt : x.v_var.vtype = .aarr .U8 N) {e : MPexpr} {i : Int}
    (he : semPexpr (Mem := Mem) true gd opS s e = .ok (.Vint i)) {ws : MWSize}
    {v : BitVec ws.bits} {arr' : JArrayMirror N}
    (hset : JArrayMirror.setWord arr .Unaligned .AAscale ws i v = .ok arr') :
    writeLval (Mem := Mem) true gd opS (.Laset .Unaligned .AAscale ws x e) (.Vword ws v) s =
      .ok (s.withVm (s.evm.set x.v_var (.Varr N arr'))) := by
  have hget : getVar true s.evm x.v_var = .ok (.Varr N arr) := by
    unfold getVar; simp [Vm.get, hx, Value.isDefined]
  have hw : CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar (Mem := Mem) true x (.Varr N arr') s =
      .ok (s.withVm (s.evm.set x.v_var (.Varr N arr'))) :=
    writeLval_lvar opS gd rfl (by rw [hxt]; rfl)
  cases ws
  · have hU8 := JArrayMirror.setWord_U8 arr .Unaligned .AAscale i v
    rw [hU8] at hset
    split at hset
    · cases hset
      simp only [writeLval, hget, he, JResult.monad_bind_eq, JResult.bind_ok, Value.toInt,
        toWord_self]
      rw [dif_pos ‹_›]
      exact hw
    · cases hset
  all_goals simp only [writeLval, hget, he, JResult.monad_bind_eq, JResult.bind_ok,
    Value.toInt, toWord_self, hset]
  all_goals exact hw

/-- **Store step.** The assignment of a word to the element `i < n` of an array variable
holding `n` words of size `ws`. -/
theorem semIr_store {s : Estate SyscallState Mem} {ws : MWSize} {a : MVarI} {n : Nat}
    {arr : JArrayMirror (n * ws.bytes)} (hva : s.evm a.v_var = .Varr _ arr)
    (hat : a.v_var.vtype = .aarr .U8 (n * ws.bytes)) {idx : MPexpr} {i : Nat} (hi : i < n)
    (hidx : semPexpr (Mem := Mem) true gd opS s idx = .ok (.Vint (i : Int))) {e : MPexpr}
    {vv : BitVec ws.bits} (he : semPexpr (Mem := Mem) true gd opS s e = .ok (.Vword ws vv)) :
    SemIr aS opS gd prog s (.Cassgn (.Laset .Unaligned .AAscale ws a idx) .AT_none (.aword ws) e)
      (s.withVm (s.evm.set a.v_var
        (.Varr _ (arr.writeLE (i * ws.bytes) ws.bytes vv.toNat)))) :=
  .Eassgn _ _ _ _ _ _ _ _ he (ComJasminBridgeFull.truncateVal_aword_self ws vv)
    (writeLval_of_setWord opS gd hva hat hidx (setWord_scaled ws arr hi vv))

/-- A write leaves every other variable unchanged. -/
theorem set_ne_var {vm : Vm} {x z : MVar} (v : Value) (h : z ≠ x) : vm.set x v z = vm z := by
  simp [Vm.set, h]

/-- The typed body of a zeroing loop over the array `x` with the index `j`. -/
def zeroArrayBody (ws : MWSize) (x j : MVarI) : List MInstr :=
  [.MkI () (.Cassgn (.Laset .Unaligned .AAscale ws x (mpv j)) .AT_none (.aword ws)
    (typeConst (.aword ws) 0))]

/-- **Zeroing iterations.** The iterations of a zeroing loop over the indices `l`, all
elements of the array, write zero at each element of `l` and leave the others. -/
theorem semFor_zero (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true) {n : Nat}
    {x j : MVarI} (hxj : x.v_var ≠ j.v_var) (hjt : j.v_var.vtype = .aint)
    (hxt : x.v_var.vtype = .aarr .U8 (n * ws.bytes)) :
    ∀ (l : List Int) (s : Estate SyscallState Mem) (arr : JArrayMirror (n * ws.bytes)),
      s.evm x.v_var = .Varr _ arr → (∀ i ∈ l, 0 ≤ i ∧ i.toNat < n) →
      ∃ (s' : Estate SyscallState Mem) (arr' : JArrayMirror (n * ws.bytes)),
        SemFor aS opS gd prog j l s (zeroArrayBody ws x j) s' ∧ s'.escs = s.escs ∧
        s'.emem = s.emem ∧ s'.evm x.v_var = .Varr _ arr' ∧
        (∀ q : Fin n, arr'.readLE (q.val * ws.bytes) ws.bytes =
          if ((q.val : Nat) : Int) ∈ l then 0 else arr.readLE (q.val * ws.bytes) ws.bytes) ∧
        (∀ z, z ≠ x.v_var → z ≠ j.v_var → s'.evm z = s.evm z) ∧
        (VmArrTyped s.evm → VmArrTyped s'.evm) := by
  intro l
  induction l with
  | nil =>
      intro s arr hx _
      exact ⟨s, arr, .EForDone _ _ _, rfl, rfl, hx, fun q => by simp, fun _ _ _ => rfl, id⟩
  | cons i l ih =>
      intro s arr hx hl
      obtain ⟨hi0, hin⟩ := hl i List.mem_cons_self
      have hw1 : CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar (Mem := Mem) true j (.Vint i) s =
          .ok (s.withVm (s.evm.set j.v_var (.Vint i))) :=
        writeLval_lvar opS gd rfl (by rw [hjt]; rfl)
      have hx1 : (s.withVm (s.evm.set j.v_var (.Vint i))).evm x.v_var = .Varr _ arr :=
        (set_ne_var _ hxj).trans hx
      have hidx : semPexpr (Mem := Mem) true gd opS (s.withVm (s.evm.set j.v_var (.Vint i)))
          (mpv j) = .ok (.Vint ((i.toNat : Nat) : Int)) :=
        semPexpr_mpv opS gd (by rw [Int.toNat_of_nonneg hi0]; exact set_same _ _ _) rfl
      have hst := semIr_store aS opS gd prog hx1 hxt hin hidx
        (semPexpr_wconst opS gd hop hg _ 0)
      obtain ⟨s', arr', hfor, hscs, hmem, hx', hrd, hfr, harr⟩ :=
        ih ((s.withVm (s.evm.set j.v_var (.Vint i))).withVm
            ((s.evm.set j.v_var (.Vint i)).set x.v_var
              (.Varr _ (arr.writeLE (i.toNat * ws.bytes) ws.bytes
                (BitVec.ofInt ws.bits 0).toNat))))
          (arr.writeLE (i.toNat * ws.bytes) ws.bytes (BitVec.ofInt ws.bits 0).toNat)
          (set_same _ _ _) (fun i' h => hl i' (List.mem_cons_of_mem _ h))
      refine ⟨s', arr', .EForOne _ _ _ _ _ _ _ _ hw1
        (sem_cons aS opS gd prog hst (.Eskip _)) hfor, hscs, hmem, hx', ?_, ?_, ?_⟩
      · intro q
        rw [hrd q]
        by_cases hq : ((q.val : Nat) : Int) ∈ l
        · rw [if_pos hq, if_pos (List.mem_cons_of_mem _ hq)]
        · rw [if_neg hq]
          by_cases hqe : q.val = i.toNat
          · rw [if_pos (List.mem_cons.mpr (Or.inl (by omega))), hqe,
              ComJasminBridgeArrWord.readLE_writeLE_same arr _ _ _
                (by have := Nat.mul_le_mul_right ws.bytes hin; rw [Nat.succ_mul] at this
                    exact this)]
            simp
          · rw [if_neg (by simp only [List.mem_cons, not_or]; exact ⟨by omega, hq⟩),
              ComJasminBridgeArrWord.readLE_writeLE_disjoint]
            rcases Nat.lt_or_gt_of_ne hqe with hlt | hlt
            · left
              have := Nat.mul_le_mul_right ws.bytes hlt
              rw [Nat.succ_mul] at this
              exact this
            · right
              have := Nat.mul_le_mul_right ws.bytes hlt
              rw [Nat.succ_mul] at this
              exact this
      · intro z hzx hzj
        rw [hfr z hzx hzj]
        exact (set_ne_var _ hzx).trans (set_ne_var _ hzj)
      · exact fun h => harr (arrTyped_set (arrTyped_set h rfl (by rw [hjt]; rfl)) rfl
          (by rw [hxt]; rfl))

/-- **Zeroing loop.** `for j = 0 to n { x[j] = 0 }` over an array variable of `n` words
writes zero at every element. -/
theorem semIr_zero (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true) {n : Nat}
    {x j : MVarI} (hxj : x.v_var ≠ j.v_var) (hjt : j.v_var.vtype = .aint)
    (hxt : x.v_var.vtype = .aarr .U8 (n * ws.bytes)) {s : Estate SyscallState Mem}
    {arr : JArrayMirror (n * ws.bytes)} (hx : s.evm x.v_var = .Varr _ arr) :
    ∃ (s' : Estate SyscallState Mem) (arr' : JArrayMirror (n * ws.bytes)),
      SemIr aS opS gd prog s (.Cfor j ⟨.UpTo, .Pconst 0, .Pconst (n : Int)⟩ (zeroArrayBody ws x j))
        s' ∧ s'.escs = s.escs ∧ s'.emem = s.emem ∧ s'.evm x.v_var = .Varr _ arr' ∧
      (∀ q : Fin n, arr'.readLE (q.val * ws.bytes) ws.bytes = 0) ∧
      (∀ z, z ≠ x.v_var → z ≠ j.v_var → s'.evm z = s.evm z) ∧
      (VmArrTyped s.evm → VmArrTyped s'.evm) := by
  have hmem : ∀ q : Nat, ((q : Int) ∈ CatCrypt.Crypto.Jasmin.CoqSemMirror.wrange .UpTo 0 (n : Int)
      ↔ q < n) := by
    intro q
    simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.wrange, List.mem_map, List.mem_range,
      Int.ofNat_eq_natCast]
    constructor
    · rintro ⟨k, hk, he⟩; omega
    · intro h; exact ⟨q, by omega, by omega⟩
  obtain ⟨s', arr', hfor, hscs, hm, hx', hrd, hfr, harr⟩ :=
    semFor_zero aS opS gd prog hop hg hxj hjt hxt
      (CatCrypt.Crypto.Jasmin.CoqSemMirror.wrange .UpTo 0 (n : Int)) s arr hx (by
      intro i hi
      simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.wrange, List.mem_map, List.mem_range,
        Int.ofNat_eq_natCast] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      omega)
  refine ⟨s', arr', .Efor _ _ _ _ _ _ _ 0 n rfl rfl hfor, hscs, hm, hx', fun q => ?_, hfr, harr⟩
  rw [hrd q, if_pos ((hmem q.val).mpr q.isLt)]

end Arr

/-! ## 12. Flags -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (x86_ADD x86_ADC x86_NEG x86_CMP x86_SUB
  add_carry rflags_of_aluop)

/-- The carry flag of `ADC`: the sum reaches `2 ^ w`. -/
theorem x86_ADC_cf {w : Nat} (a b : BitVec w) (c : Bool) :
    (x86_ADC a b c).cf = some (decide (2 ^ w ≤ a.toNat + b.toNat + (if c then 1 else 0))) := by
  simp only [x86_ADC, rflags_of_aluop, add_carry,
    CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.wunsigned, BitVec.toNat_ofNat]
  congr 1
  have hP : 0 < 2 ^ w := Nat.two_pow_pos w
  have ha := a.isLt
  have hb := b.isLt
  have hc : (if c then 1 else 0) ≤ 1 := by split <;> omega
  generalize (if c then 1 else 0) = k at *
  generalize 2 ^ w = P at *
  apply decide_eq_decide.mpr
  constructor
  · intro h
    by_contra h'
    exact h (Nat.mod_eq_of_lt (by omega))
  · intro h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The borrow of a difference modulo `P` is the unsigned order. -/
theorem sub_cf_aux {P a b : Nat} (ha : a < P) (hb : b < P) :
    decide ((((P - b + a) % P : Nat) : Int) ≠ (a : Int) - (b : Int)) = decide (a < b) := by
  apply decide_eq_decide.mpr
  by_cases h : a < b
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [h, iff_true]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [h, iff_false, not_not]
    omega

/-- The carry flag of `CMP`: the unsigned order. -/
theorem x86_CMP_cf {w : Nat} (a b : BitVec w) :
    (x86_CMP a b).cf = some (decide (a.toNat < b.toNat)) := by
  simp only [x86_CMP, x86_SUB, CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.wunsigned,
    BitVec.toNat_sub]
  congr 1
  exact sub_cf_aux a.isLt b.isLt

/-- The carry flag of `ADD_64(c, -1)` on a `0`/`1` word is that bit. -/
theorem x86_ADD_cf_cin (cin : BitVec 1) :
    (x86_ADD (BitVec.ofNat 64 cin.toNat) (BitVec.ofInt 64 (-1))).cf =
      some (decide (cin.toNat = 1)) := by
  rcases bitVec1_eq cin with rfl | rfl <;> decide

/-- `x ^ 1` of a `0`/`1` word is the complement bit. -/
theorem flip_bit (P : Bool) :
    BitVec.ofNat 64 (if P then 1 else 0) ^^^ BitVec.ofInt 64 1 =
      BitVec.ofNat 64 (if !P then 1 else 0) := by
  cases P <;> decide

/-! ## 13. Blocks of the carry and comparison idioms -/

/-- A typed operand that evaluates to the word `b` in every state that agrees with `s` outside
the scratch variables. -/
def Stable (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem) (ws : MWSize)
    (e : MPexpr) (b : BitVec ws.bits) : Prop :=
  ∀ s' : Estate SyscallState Mem, (∀ z : MVar, ¬ Scratch z.vname → s'.evm z = s.evm z) →
    semPexpr (Mem := Mem) true gd opS s' (typeE (.aword ws) e) = .ok (.Vword ws b)

/-- A read of a variable outside the scratch variables is a stable operand. -/
theorem stable_mpv {gd : GlobDecls} {opS : OpSem} {s : Estate SyscallState Mem} {ws : MWSize}
    {a : JVar} (ha : ¬ Scratch a.vname) {b : BitVec ws.bits}
    (hv : s.evm (mvar a) = .Vword ws b) : Stable gd opS s ws (mpv (mvi a)) b :=
  fun _ hf => semPexpr_mpv opS gd ((hf (mvar a) ha).trans hv) rfl

/-- A constant is a stable operand. -/
theorem stable_const {gd : GlobDecls} {opS : OpSem} (hop : JazzOpAgrees opS)
    {s : Estate SyscallState Mem} {ws : MWSize} (hg : gprB ws = true) (z : Int) :
    Stable gd opS s ws (.Pconst z) (BitVec.ofInt ws.bits z) :=
  fun s' _ => semPexpr_wconst opS gd hop hg s' z

/-- A stable operand stays stable over writes of scratch variables. -/
theorem Stable.mono {gd : GlobDecls} {opS : OpSem} {s s1 : Estate SyscallState Mem}
    {ws : MWSize} {e : MPexpr} {b : BitVec ws.bits} (h : Stable gd opS s ws e b)
    (hf : ∀ z : MVar, ¬ Scratch z.vname → s1.evm z = s.evm z) : Stable gd opS s1 ws e b :=
  fun s' hf' => h s' fun z hz => (hf' z hz).trans (hf z hz)

omit [MemModel Mem] in
/-- Two `Post` steps compose when the variable of the first is outside the frame of the
second. -/
theorem Post.trans {s s1 s2 : Estate SyscallState Mem} {y1 y2 : MVar}
    {R1 R2 : Value → Prop} (h1 : Post s s1 y1 R1) (h2 : Post s1 s2 y2 R2)
    (hy : ∀ z : MVar, z.vname ≠ y2.vname → ¬ Scratch z.vname → z.vname ≠ y1.vname) :
    Post s s2 y2 R2 :=
  ⟨h2.scs.trans h1.scs, h2.mem.trans h1.mem, h2.res,
    fun z hz hs => (h2.frame z hz hs).trans (h1.frame z (hy z hz hs) hs),
    fun h => h2.arr (h1.arr h)⟩

/-- The mirror type of a scratch register at a word size of `gprB`. -/
theorem mvar_tmp {ws : MWSize} (hg : gprB ws = true) (k : Nat) :
    (mvar (tmp k (wsOf ws.bits))).vtype = .aword ws := by
  simp [mvar, tmp, mkV, translateSTypeExt, translateSType, translateWSize_gpr hg]

/-- A scratch register at a word size of `gprB` translates. -/
theorem okV_tmp_gpr {ws : MWSize} (hg : gprB ws = true) (k : Nat) :
    OkV (tmp k (wsOf ws.bits)) := by
  apply okV_tmp
  cases ws <;> simp [gprB, wsOf, CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.bits] at hg ⊢

/-- The carry flag is the mirror variable `mcf`. -/
theorem mvar_cf : mvar cfVar = mcf.v_var := rfl

/-- The name of a scratch register is not the name of the carry flag. -/
theorem tmp_ne_cf (k : Nat) (ws : AWSize) : (mvar (tmp k ws)).vname ≠ mcf.v_var.vname :=
  (cf_ne_nameOf 't' k _).symm

section Blocks
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- **Disequality flag.** `t = a; t = t ^ b; _, cf, _, _, _, t = #NEG(t)` sets the carry flag
to `a ≠ b`. -/
theorem blk_neq (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {ws : MWSize}
    (hg : gprB ws = true) {ea eb : APExpr} {ea' eb' : MPexpr}
    (hea : translatePExprExt ea = some ea') (heb : translatePExprExt eb = some eb')
    {s : Estate SyscallState Mem} {a b : BitVec ws.bits} (hsa : Stable gd opS s ws ea' a)
    (hsb : Stable gd opS s ws eb' b) {c' : List MInstr}
    (hc : translateCmdExt [asgn (tmp 0 (wsOf ws.bits)) ea,
      asgn (tmp 0 (wsOf ws.bits)) (.Papp2 (.Olxor (wsOf ws.bits)) (pv (tmp 0 (wsOf ws.bits))) eb),
      copn (asmName "NEG" (wsOf ws.bits)) (outsCW (tmp 0 (wsOf ws.bits)))
        [pv (tmp 0 (wsOf ws.bits))]] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' mcf.v_var (· = .Vbool (decide (a ≠ b))) := by
  have ht := okV_tmp_gpr hg 0
  have htt := mvar_tmp hg 0
  have hsc := scratch_tmp 0 (wsOf ws.bits)
  have ho := (opnNoneTys_gpr _ (wsOf_gpr_mem hg)).2.2.1
  have hmem : asmName "NEG" (wsOf ws.bits) ∈ jazzOps :=
    (asmName_mem_jazzOps (widthOkB_bits hg)).2.2.1
  have hty : ∀ u : BitVec ws.bits,
      (Value.Vword ws u).typeOf = evalAtype (mvar (tmp 0 (wsOf ws.bits))).vtype :=
    fun _ => by rw [htt]; rfl
  set t := mvar (tmp 0 (wsOf ws.bits)) with ht_def
  have hf1 : ∀ (vm : Vm) (v : Value) (z : MVar), ¬ Scratch z.vname → vm.set t v z = vm z :=
    fun _ _ z hz => set_ne _ (ne_of_not_scratch hz hsc)
  have hf2 : ∀ (vm : Vm) (v : Value) (z : MVar), ¬ Scratch z.vname → vm.set mcf.v_var v z = vm z :=
    fun _ _ z hz => set_ne _ (ne_of_not_scratch hz scratch_cf)
  refine ⟨s.withVm ((((s.evm.set t (.Vword ws a)).set t (.Vword ws (a ^^^ b))).set mcf.v_var
      (.Vbool (decide (a ^^^ b ≠ 0)))).set t (.Vword ws (0 - (a ^^^ b)))), ?_,
    post_of ?_ ?_ ?_⟩
  · refine sem_asgn_step aS opS gd prog ht hea hc (v := .Vword ws a) ?_ rfl (hty a)
      (fun c1 hc1 => ?_)
    · rw [htt]; exact hsa s fun _ _ => rfl
    refine sem_asgn_step aS opS gd prog ht (translatePExprExt_papp2
      (op' := .Olxor ws) (by simp [translateSOp2Ext, translateSOp2, translateWSize_gpr hg])
      (translatePExprExt_pv (translateVarIExt_mvi ht)) heb) hc1 (v := .Vword ws (a ^^^ b))
      ?_ rfl (hty _) (fun c2 hc2 => ?_)
    · rw [htt]
      show semPexpr (Mem := Mem) true gd opS _
        (.Papp2 (.Olxor ws) (mpv (mvi (tmp 0 (wsOf ws.bits)))) (typeE (.aword ws) eb')) = _
      rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (hsb _ fun z hz => hf1 _ _ z hz), hop.lxor ws hg]
    refine sem_copn_step aS opS gd prog (vs := [.Vword ws (a ^^^ b)]) hc2 (mapM_outsCW ho ht)
      (mapM_pv_mvi (xs := [tmp 0 (wsOf ws.bits)]) (by simp [ht])) ?_ ?_
      (writeLvals_CW gd opS _ (x86_NEG (a ^^^ b)) (cb := decide (a ^^^ b ≠ 0)) rfl
        (x := mvi (tmp 0 (wsOf ws.bits))) htt) (fun c3 hc3 => sem_nil_step aS opS gd prog hc3 _)
    · rw [show [tmp 0 (wsOf ws.bits)].map (fun v => mpv (mvi v)) =
        [mvi (tmp 0 (wsOf ws.bits))].map mpv from rfl, typeArgs_mpv]
      exact semPexprs_cons opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (semPexprs_nil opS gd _)
    · rw [haS _ hmem, asmName_wsOf hg]
      exact JazzAsmSem.jazzAsmSem_neg ws hg _
  · show (_ : Vm) mcf.v_var = _
    rw [set_ne _ (tmp_ne_cf 0 _).symm, set_same]
    congr 2
    exact propext (not_congr BitVec.xor_eq_zero_iff)
  · intro z _ hz
    rw [hf1 _ _ z hz, hf2 _ _ z hz, hf1 _ _ z hz, hf1 _ _ z hz]
  · exact fun h => arrTyped_set (arrTyped_set (arrTyped_set (arrTyped_set h rfl (hty _)) rfl
      (hty _)) rfl rfl) rfl (hty _)

/-- **Order flag.** `t = e1; t' = e2; _, cf, _, _, _ = #CMP(t, t')` sets the carry flag to
`e1 < e2`. -/
theorem blk_below (haS : JazzAsmAgrees aS) {ws : MWSize} (hg : gprB ws = true)
    {e1 e2 : APExpr} {e1' e2' : MPexpr}
    (he1 : translatePExprExt e1 = some e1') (he2 : translatePExprExt e2 = some e2')
    {s : Estate SyscallState Mem} {a b : BitVec ws.bits} (hsa : Stable gd opS s ws e1' a)
    (hsb : Stable gd opS s ws e2' b) {c' : List MInstr}
    (hc : translateCmdExt [asgn (tmp 0 (wsOf ws.bits)) e1, asgn (tmp 1 (wsOf ws.bits)) e2,
      copn (asmName "CMP" (wsOf ws.bits)) [none, some cfVar, none, none, none]
        [pv (tmp 0 (wsOf ws.bits)), pv (tmp 1 (wsOf ws.bits))]] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' mcf.v_var (· = .Vbool (decide (a.toNat < b.toNat))) := by
  have ht := okV_tmp_gpr hg 0
  have ht' := okV_tmp_gpr hg 1
  have htt := mvar_tmp hg 0
  have htt' := mvar_tmp hg 1
  have hsc := scratch_tmp 0 (wsOf ws.bits)
  have hsc' := scratch_tmp 1 (wsOf ws.bits)
  have ho := (opnNoneTys_gpr _ (wsOf_gpr_mem hg)).2.2.2.2.1
  have hmem : asmName "CMP" (wsOf ws.bits) ∈ jazzOps :=
    (asmName_mem_jazzOps (widthOkB_bits hg)).2.2.2.1
  set t := mvar (tmp 0 (wsOf ws.bits))
  set t' := mvar (tmp 1 (wsOf ws.bits))
  have hf : ∀ (vm : Vm) (y : MVar) (v : Value) (z : MVar), Scratch y.vname →
      ¬ Scratch z.vname → vm.set y v z = vm z :=
    fun _ _ _ z hy hz => set_ne _ (ne_of_not_scratch hz hy)
  have htn : t'.vname ≠ t.vname := by
    simp only [t, t', mvar, tmp, mkV]
    intro h
    exact absurd (nameOf_inj h).2.1 (by decide)
  refine ⟨s.withVm (((s.evm.set t (.Vword ws a)).set t' (.Vword ws b)).set mcf.v_var
      (.Vbool (decide (a.toNat < b.toNat)))), ?_, post_of (by simp) ?_ ?_⟩
  · refine sem_asgn_step aS opS gd prog ht he1 hc (v := .Vword ws a) ?_ rfl
      (by rw [htt]; rfl) (fun c1 hc1 => ?_)
    · rw [htt]; exact hsa s fun _ _ => rfl
    refine sem_asgn_step aS opS gd prog ht' he2 hc1 (v := .Vword ws b) ?_ rfl
      (by rw [htt']; rfl) (fun c2 hc2 => ?_)
    · rw [htt']; exact hsb _ fun z hz => hf _ _ _ z hsc hz
    refine sem_copn_step aS opS gd prog (vs := [.Vword ws a, .Vword ws b]) hc2 (mapM_outsCmp ho)
      (mapM_pv_mvi (xs := [tmp 0 (wsOf ws.bits), tmp 1 (wsOf ws.bits)]) (by simp [ht, ht']))
      ?_ ?_ (writeLvals_cmp gd opS _ (x86_CMP a b) (x86_CMP_cf a b))
      (fun c3 hc3 => sem_nil_step aS opS gd prog hc3 _)
    · rw [show [tmp 0 (wsOf ws.bits), tmp 1 (wsOf ws.bits)].map (fun v => mpv (mvi v)) =
        [mvi (tmp 0 (wsOf ws.bits)), mvi (tmp 1 (wsOf ws.bits))].map mpv from rfl,
        typeArgs_mpv]
      exact semPexprs_cons opS gd (semPexpr_mpv opS gd ((set_ne _ htn.symm).trans
          (set_same _ _ _)) rfl)
        (semPexprs_cons opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
          (semPexprs_nil opS gd _))
    · rw [haS _ hmem, asmName_wsOf hg]
      exact JazzAsmSem.jazzAsmSem_cmp ws hg a b
  · intro z _ hz
    rw [hf _ _ _ z scratch_cf hz, hf _ _ _ z hsc' hz, hf _ _ _ z hsc hz]
  · exact fun h => arrTyped_set (arrTyped_set (arrTyped_set h rfl (by rw [htt]; rfl)) rfl
      (by rw [htt']; rfl)) rfl rfl

/-- **Carry materialisation.** `x = 0; _, _, _, _, _, x = #ADC_64(x, x, cf)` writes the carry
flag `P` to `x` as a `0`/`1` word. -/
theorem blk_matCF (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {x : JVar} (hx : OkV x)
    (hxt : (mvar x).vtype = .aword .U64) (hxc : ¬ Scratch x.vname)
    {s : Estate SyscallState Mem} {P : Bool} (hcf : s.evm mcf.v_var = .Vbool P)
    {c' : List MInstr} (hc : translateCmdExt (matCF x) = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword .U64 (BitVec.ofNat 64 (if P then 1 else 0))) := by
  have hmem : "ADC_64" ∈ jazzOps := by
    simp [jazzOps, JazzAsmSem.jazzRows, JazzAsmSem.opName, JazzAsmSem.wsName]
  have hxcf : mcf.v_var.vname ≠ x.vname := fun h => hxc (h ▸ scratch_cf)
  refine ⟨s.withVm ((s.evm.set (mvar x) (.Vword .U64 (BitVec.ofInt 64 0))).set (mvar x)
      (.Vword .U64 (x86_ADC (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) P).word)), ?_,
    post_of ?_ ?_ ?_⟩
  · refine sem_asgn_step aS opS gd prog hx (translatePExprExt_cnst 0) hc
      (v := .Vword .U64 (BitVec.ofInt 64 0)) ?_ rfl
      (by rw [hxt]; rfl) (fun c1 hc1 => ?_)
    · rw [hxt]; exact semPexpr_wconst opS gd hop rfl _ 0
    refine sem_copn_step aS opS gd prog (vs := [.Vword .U64 (BitVec.ofInt 64 0),
        .Vword .U64 (BitVec.ofInt 64 0), .Vbool P]) hc1 (mapM_outsW
        CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys_ADC_64 hx)
      (mapM_pv_mvi (xs := [x, x, cfVar]) (by simp [hx, okV_cf])) ?_ ?_
      (writeLvals_W gd opS _ (x86_ADC (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) P)
        (ws := .U64) (x := mvi x) hxt) (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    · rw [show [x, x, cfVar].map (fun v => mpv (mvi v)) = [mvi x, mvi x, mvi cfVar].map mpv
        from rfl, typeArgs_mpv]
      exact semPexprs_cons opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (semPexprs_cons opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
          (semPexprs_cons opS gd (semPexpr_mpv opS gd ((set_ne _ hxcf).trans hcf) rfl)
            (semPexprs_nil opS gd _)))
    · rw [haS _ hmem]
      exact JazzAsmSem.jazzAsmSem_adc .U64 rfl _ _ P
  · show (_ : Vm) (mvar x) = _
    rw [set_same]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [x86_ADC, rflags_of_aluop, add_carry, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    cases P <;> simp
  · intro z hz _
    rw [set_ne _ hz, set_ne _ hz]
  · exact fun h => arrTyped_set (arrTyped_set h rfl (by rw [hxt]; rfl)) rfl (by rw [hxt]; rfl)

/-- **Complement.** `x = x ^ 1`. -/
theorem blk_flip (hop : JazzOpAgrees opS) {x : JVar} (hx : OkV x)
    (hxt : (mvar x).vtype = .aword .U64) {s : Estate SyscallState Mem} {u : BitVec 64}
    (hv : s.evm (mvar x) = .Vword .U64 u) {c' : List MInstr}
    (hc : translateCmdExt [asgn x (.Papp2 (.Olxor .U64) (pv x) (cnst 1))] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword .U64 (u ^^^ BitVec.ofInt 64 1)) := by
  refine ⟨s.withVm (s.evm.set (mvar x) (.Vword .U64 (u ^^^ BitVec.ofInt 64 1))), ?_,
    post_of (by simp) (fun z hz _ => set_ne _ hz)
      (fun h => arrTyped_set h rfl (by rw [hxt]; rfl))⟩
  refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp2 (op' := .Olxor .U64) rfl
    (translatePExprExt_pv (translateVarIExt_mvi hx)) (translatePExprExt_cnst 1)) hc ?_ rfl
    (by rw [hxt]; rfl) (fun c1 hc1 => sem_nil_step aS opS gd prog hc1 _)
  show semPexpr (Mem := Mem) true gd opS s
    (.Papp2 (.Olxor .U64) (mpv (mvi x)) (typeConst (.aword .U64) 1)) = _
  rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd hv rfl) (semPexpr_wconst opS gd hop rfl s 1)]
  exact hop.lxor .U64 rfl _ _

/-- **Carry-in.** `_, cf, _, _, _, t = #ADD_64(cin, -1)` sets the carry flag to the bit
`cin`. -/
theorem blk_cin (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {cv : JVar} (hcv : OkV cv)
    (_hcs : ¬ Scratch cv.vname) {s : Estate SyscallState Mem} {cin : BitVec 1}
    (hv : s.evm (mvar cv) = .Vword .U64 (BitVec.ofNat 64 cin.toNat)) {c' : List MInstr}
    (hc : translateCmdExt [cinCode cv] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' mcf.v_var (· = .Vbool (decide (cin.toNat = 1))) := by
  have hmem : "ADD_64" ∈ jazzOps := by
    simp [jazzOps, JazzAsmSem.jazzRows, JazzAsmSem.opName, JazzAsmSem.wsName]
  have ht := okV_tmp_gpr (ws := .U64) rfl 0
  have htt : (mvar (tmp 0 (wsOf 64))).vtype = .aword .U64 := mvar_tmp (ws := .U64) rfl 0
  have hsc := scratch_tmp 0 (wsOf 64)
  have hes : [pv cv, cnst (-1)].mapM translatePExprExt = some [mpv (mvi cv), .Pconst (-1)] := by
    rw [List.mapM_cons, translatePExprExt_pv (translateVarIExt_mvi hcv), List.mapM_cons,
      translatePExprExt_cnst]
    rfl
  refine ⟨s.withVm ((s.evm.set mcf.v_var (.Vbool (decide (cin.toNat = 1)))).set
      (mvar (tmp 0 (wsOf 64)))
      (.Vword .U64 (x86_ADD (BitVec.ofNat 64 cin.toNat) (BitVec.ofInt 64 (-1))).word)), ?_,
      post_of ?_ ?_ ?_⟩
  · refine sem_copn_step aS opS gd prog
      (vs := [.Vword .U64 (BitVec.ofNat 64 cin.toNat), .Vword .U64 (BitVec.ofInt 64 (-1))]) hc
      (mapM_outsCW CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys_ADD_64 ht) hes ?_ ?_
      (writeLvals_CW gd opS _ (ws := .U64)
        (x86_ADD (BitVec.ofNat 64 cin.toNat) (BitVec.ofInt 64 (-1))) (x86_ADD_cf_cin cin)
        (x := mvi (tmp 0 (wsOf 64))) htt)
      (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    · show CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprs (Mem := Mem) true gd opS s
        [mpv (mvi cv), typeConst (.aword .U64) (-1)] = _
      exact semPexprs_cons opS gd (semPexpr_mpv opS gd hv rfl)
        (semPexprs_cons opS gd (semPexpr_wconst opS gd hop rfl s (-1))
          (semPexprs_nil opS gd _))
    · rw [haS _ hmem]
      exact JazzAsmSem.jazzAsmSem_add .U64 rfl _ _
  · show (_ : Vm) mcf.v_var = _
    rw [set_ne _ (tmp_ne_cf 0 _).symm, set_same]
  · intro z _ hz
    rw [set_ne _ (ne_of_not_scratch hz hsc), set_ne _ (ne_of_not_scratch hz scratch_cf)]
  · exact fun h => arrTyped_set (arrTyped_set h rfl rfl) rfl (by rw [htt]; rfl)

/-- **Carry addition.** `x = a; _, cf, _, _, _, x = #ADC(x, b, cf)` with the carry flag `cb`
writes the word of `ADC` to `x` and its carry to the flag. -/
theorem blk_adc (haS : JazzAsmAgrees aS) {ws : MWSize} (hg : gprB ws = true) {x a b : JVar}
    (hx : OkV x) (ha : OkV a) (hb : OkV b) (hxt : (mvar x).vtype = .aword ws)
    (hxcf : x.vname ≠ "cf") (hbx : b.vname ≠ x.vname) {s : Estate SyscallState Mem}
    {va vb : BitVec ws.bits} {cb : Bool} (hva : s.evm (mvar a) = .Vword ws va)
    (hvb : s.evm (mvar b) = .Vword ws vb) (hcf : s.evm mcf.v_var = .Vbool cb)
    {c' : List MInstr}
    (hc : translateCmdExt [asgn x (pv a),
      copn (asmName "ADC" (wsOf ws.bits)) (outsCW x) [pv x, pv b, pv cfVar]] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws (x86_ADC va vb cb).word) ∧
      s'.evm mcf.v_var = .Vbool (decide (2 ^ ws.bits ≤ va.toNat + vb.toNat +
        (if cb then 1 else 0))) := by
  have ho := (opnNoneTys_gpr _ (wsOf_gpr_mem hg)).2.1
  have hmem : asmName "ADC" (wsOf ws.bits) ∈ jazzOps :=
    (asmName_mem_jazzOps (widthOkB_bits hg)).2.1
  have hcfx : mcf.v_var.vname ≠ x.vname := fun h => hxcf h.symm
  have hty : ∀ u : BitVec ws.bits, (Value.Vword ws u).typeOf = evalAtype (mvar x).vtype :=
    fun _ => by rw [hxt]; rfl
  refine ⟨s.withVm (((s.evm.set (mvar x) (.Vword ws va)).set mcf.v_var
      (.Vbool (decide (2 ^ ws.bits ≤ va.toNat + vb.toNat + (if cb then 1 else 0))))).set
      (mvar x) (.Vword ws (x86_ADC va vb cb).word)), ?_, post_of (by simp) ?_ ?_, ?_⟩
  · refine sem_asgn_step aS opS gd prog hx (translatePExprExt_pv (translateVarIExt_mvi ha)) hc
      (semPexpr_mpv opS gd hva rfl) rfl (hty va) (fun c1 hc1 => ?_)
    refine sem_copn_step aS opS gd prog (vs := [.Vword ws va, .Vword ws vb, .Vbool cb]) hc1
      (mapM_outsCW ho hx) (mapM_pv_mvi (xs := [x, b, cfVar]) (by simp [hx, hb, okV_cf])) ?_ ?_
      (writeLvals_CW gd opS _ (x86_ADC va vb cb) (x86_ADC_cf va vb cb) (x := mvi x) hxt)
      (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
    · rw [show [x, b, cfVar].map (fun v => mpv (mvi v)) = [mvi x, mvi b, mvi cfVar].map mpv
        from rfl, typeArgs_mpv]
      exact semPexprs_cons opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (semPexprs_cons opS gd (semPexpr_mpv opS gd ((set_ne _ hbx).trans hvb) rfl)
          (semPexprs_cons opS gd (semPexpr_mpv opS gd ((set_ne _ hcfx).trans hcf) rfl)
            (semPexprs_nil opS gd _)))
    · rw [haS _ hmem, asmName_wsOf hg]
      exact JazzAsmSem.jazzAsmSem_adc ws hg va vb cb
  · intro z hz hs
    rw [set_ne _ hz, set_ne _ (ne_of_not_scratch hs scratch_cf), set_ne _ hz]
  · exact fun h => arrTyped_set (arrTyped_set (arrTyped_set h rfl (hty _)) rfl rfl) rfl (hty _)
  · exact (set_ne (z := mcf.v_var) (x := mvar x) _ hcfx).trans (set_same _ _ _)

end Blocks

omit [MemModel Mem] in
/-- A `Post` state over the scratch variable `y` is a `Post` state over every variable whose
new value is in `R'`. -/
theorem Post.change_target {s s' : Estate SyscallState Mem} {y y' : MVar} {R R' : Value → Prop}
    (h : Post s s' y R) (hy : Scratch y.vname) (hR : R' (s'.evm y')) : Post s s' y' R' :=
  ⟨h.scs, h.mem, hR, fun z _ hz => h.frame z (ne_of_not_scratch hz hy) hz, h.arr⟩

section Seq
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- **Sequencing of blocks.** -/
theorem seq_post {a b : List AInstrR} {c' : List MInstr}
    (hc : translateCmdExt (a ++ b) = some c') {s : Estate SyscallState Mem} {y1 y2 : MVar}
    {R1 R2 : Value → Prop}
    (ha : ∀ a', translateCmdExt a = some a' →
      ∃ s1, Sem aS opS gd prog s (typeC a') s1 ∧ Post s s1 y1 R1)
    (hb : ∀ s1, Post s s1 y1 R1 → ∀ b', translateCmdExt b = some b' →
      ∃ s2, Sem aS opS gd prog s1 (typeC b') s2 ∧ Post s1 s2 y2 R2)
    (hy : ∀ z : MVar, z.vname ≠ y2.vname → ¬ Scratch z.vname → z.vname ≠ y1.vname) :
    ∃ s2, Sem aS opS gd prog s (typeC c') s2 ∧ Post s s2 y2 R2 := by
  obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv hc
  obtain ⟨s1, h1, hp1⟩ := ha a' ha'
  obtain ⟨s2, h2, hp2⟩ := hb s1 hp1 b' hb'
  refine ⟨s2, ?_, hp1.trans hp2 hy⟩
  rw [typeC_append]
  exact ComJasminBridgeProgram.sem_append aS opS gd prog h1 h2

omit [MemModel Mem] in
/-- A variable outside the scratch variables keeps its value over a `Post` step of a scratch
variable. -/
theorem Post.read {s s' : Estate SyscallState Mem} {y : MVar} {R : Value → Prop}
    (h : Post s s' y R) (hy : Scratch y.vname) {z : MVar} (hz : ¬ Scratch z.vname) :
    s'.evm z = s.evm z :=
  h.frame z (ne_of_not_scratch hz hy) hz

/-- **Low carry word.** The code of `addCarryLo`. -/
theorem sem_addCarryLo (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {ws : MWSize}
    (hg : gprB ws = true) {x a b cv : JVar} (hx : OkV x) (ha : OkV a) (hb : OkV b)
    (hcv : OkV cv) (hxt : (mvar x).vtype = .aword ws) (hxs : ¬ Scratch x.vname)
    (has : ¬ Scratch a.vname) (hbs : ¬ Scratch b.vname) (hcs : ¬ Scratch cv.vname)
    (hbx : b.vname ≠ x.vname) {s : Estate SyscallState Mem} {va vb : BitVec ws.bits}
    {cin : BitVec 1} (hva : s.evm (mvar a) = .Vword ws va) (hvb : s.evm (mvar b) = .Vword ws vb)
    (hvc : s.evm (mvar cv) = .Vword .U64 (BitVec.ofNat 64 cin.toNat)) {c' : List MInstr}
    (hc : translateCmdExt ([cinCode cv] ++ [asgn x (pv a),
      copn (asmName "ADC" (wsOf ws.bits)) (outsCW x) [pv x, pv b, pv cfVar]]) = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws (x86_ADC va vb (decide (cin.toNat = 1))).word) := by
  refine seq_post aS opS gd prog hc
    (fun a' ha' => blk_cin aS opS gd prog haS hop hcv hcs hvc ha') (fun s1 hp1 b' hb' => ?_)
    (fun z _ hz => ne_of_not_scratch hz scratch_cf)
  obtain ⟨s2, h2, hp2, _⟩ := blk_adc aS opS gd prog haS hg hx ha hb hxt
    (fun h => hxs (h ▸ scratch_cf)) hbx ((hp1.read scratch_cf has).trans hva)
    ((hp1.read scratch_cf hbs).trans hvb) hp1.res hb'
  exact ⟨s2, h2, hp2⟩

/-- **Carry-out bit.** The code of `addCarryHi`. -/
theorem sem_addCarryHi (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {ws : MWSize}
    (hg : gprB ws = true) {x a b cv : JVar} (hx : OkV x) (ha : OkV a) (hb : OkV b)
    (hcv : OkV cv) (hxt : (mvar x).vtype = .aword .U64) (hxs : ¬ Scratch x.vname)
    (has : ¬ Scratch a.vname) (hbs : ¬ Scratch b.vname) (hcs : ¬ Scratch cv.vname)
    {s : Estate SyscallState Mem} {va vb : BitVec ws.bits}
    {cin : BitVec 1} (hva : s.evm (mvar a) = .Vword ws va) (hvb : s.evm (mvar b) = .Vword ws vb)
    (hvc : s.evm (mvar cv) = .Vword .U64 (BitVec.ofNat 64 cin.toNat)) {c' : List MInstr}
    (hc : translateCmdExt (([cinCode cv] ++ [asgn (tmp 1 (wsOf ws.bits)) (pv a),
      copn (asmName "ADC" (wsOf ws.bits)) (outsCW (tmp 1 (wsOf ws.bits)))
        [pv (tmp 1 (wsOf ws.bits)), pv b, pv cfVar]]) ++ matCF x) = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword .U64 (BitVec.ofNat 64
        (if decide (2 ^ ws.bits ≤ va.toNat + vb.toNat + (if cin.toNat = 1 then 1 else 0))
          then 1 else 0))) := by
  have ht := okV_tmp_gpr hg 1
  have hsc := scratch_tmp 1 (wsOf ws.bits)
  have hbt : b.vname ≠ (tmp 1 (wsOf ws.bits)).vname := ne_of_not_scratch hbs hsc
  refine seq_post aS opS gd prog hc (y1 := mcf.v_var)
    (R1 := (· = .Vbool (decide (2 ^ ws.bits ≤ va.toNat + vb.toNat +
      (if cin.toNat = 1 then 1 else 0))))) (fun a' ha' => ?_) (fun s2 hp2 b' hb' => ?_)
    (fun z _ hz => ne_of_not_scratch hz scratch_cf)
  · refine seq_post aS opS gd prog ha'
      (fun a'' ha'' => blk_cin aS opS gd prog haS hop hcv hcs hvc ha'')
      (fun s1 hp1 b'' hb'' => ?_) (fun z _ hz => ne_of_not_scratch hz scratch_cf)
    obtain ⟨s2, h2, hp2, hcf2⟩ := blk_adc aS opS gd prog haS hg ht ha hb (mvar_tmp hg 1)
      (tmp_ne_cf 1 _) hbt ((hp1.read scratch_cf has).trans hva)
      ((hp1.read scratch_cf hbs).trans hvb) hp1.res hb''
    refine ⟨s2, h2, hp2.change_target hsc ?_⟩
    rw [hcf2]
    simp
  · exact blk_matCF aS opS gd prog haS hop hx hxt hxs hp2.res hb'

omit [MemModel Mem] in
/-- A `Post` state for a weaker condition on the new value. -/
theorem Post.mono {s s' : Estate SyscallState Mem} {y : MVar} {R R' : Value → Prop}
    (h : Post s s' y R) (hR : ∀ v, R v → R' v) : Post s s' y R' :=
  ⟨h.scs, h.mem, hR _ h.res, h.frame, h.arr⟩

/-- The value of a comparison bit. -/
theorem cmpBit_toNat {w : Nat} (c : JasminCmp) (a b : BitVec w) :
    (cmpBit c a b).toNat = if c.holds a b then 1 else 0 := by
  unfold cmpBit
  split <;> rfl

/-- **Comparison.** The code `cmpCode c` writes the comparison bit of its operands to `x`. -/
theorem sem_cmpCode (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {ws : MWSize}
    (hg : gprB ws = true) (c : JasminCmp) {x : JVar} (hx : OkV x)
    (hxt : (mvar x).vtype = .aword .U64) (hxs : ¬ Scratch x.vname) {ea eb : APExpr}
    {ea' eb' : MPexpr} (hea : translatePExprExt ea = some ea')
    (heb : translatePExprExt eb = some eb') {s : Estate SyscallState Mem}
    {a b : BitVec ws.bits} (hsa : Stable gd opS s ws ea' a) (hsb : Stable gd opS s ws eb' b)
    {c' : List MInstr} (hc : translateCmdExt (cmpCode c (wsOf ws.bits) x ea eb) = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword .U64 (BitVec.ofNat 64 (cmpBit c a b).toNat)) := by
  have hyx : ∀ z : MVar, z.vname ≠ (mvar x).vname → ¬ Scratch z.vname →
      z.vname ≠ (mvar x).vname := fun _ h _ => h
  have hycf : ∀ z : MVar, z.vname ≠ (mvar x).vname → ¬ Scratch z.vname →
      z.vname ≠ mcf.v_var.vname := fun _ _ hz => ne_of_not_scratch hz scratch_cf
  have hmat : ∀ (s1 : Estate SyscallState Mem) (P : Bool), s1.evm mcf.v_var = .Vbool P →
      ∀ b', translateCmdExt (matCF x) = some b' → ∃ s2, Sem aS opS gd prog s1 (typeC b') s2 ∧
        Post s1 s2 (mvar x) (· = .Vword .U64 (BitVec.ofNat 64 (if P then 1 else 0))) :=
    fun _ _ hcf _ hb' => blk_matCF aS opS gd prog haS hop hx hxt hxs hcf hb'
  have hflip : ∀ (s2 : Estate SyscallState Mem) (P : Bool),
      Post s s2 (mvar x) (· = .Vword .U64 (BitVec.ofNat 64 (if P then 1 else 0))) →
      ∀ b', translateCmdExt [asgn x (.Papp2 (.Olxor .U64) (pv x) (cnst 1))] = some b' →
        ∃ s3, Sem aS opS gd prog s2 (typeC b') s3 ∧
          Post s2 s3 (mvar x) (· = .Vword .U64 (BitVec.ofNat 64 (if !P then 1 else 0))) :=
    fun _ P hp _ hb' => by
      obtain ⟨s3, h3, hp3⟩ := blk_flip aS opS gd prog hop hx hxt hp.res hb'
      exact ⟨s3, h3, hp3.mono fun v hv => by rw [hv, flip_bit]⟩
  cases c <;> simp only [cmpCode] at hc
  · -- eq
    obtain ⟨s', h', hp'⟩ := seq_post aS opS gd prog hc (fun a' ha' => seq_post aS opS gd prog ha'
      (fun a'' ha'' => blk_neq aS opS gd prog haS hop hg hea heb hsa hsb ha'')
      (fun s1 hp1 b' hb' => hmat s1 _ hp1.res b' hb') hycf)
      (fun s2 hp2 b' hb' => hflip s2 _ hp2 b' hb') hyx
    refine ⟨s', h', hp'.mono fun v hv => ?_⟩
    rw [hv, cmpBit_toNat]
    by_cases h : a = b <;> simp [h, JasminCmp.holds]
  · -- ne
    obtain ⟨s', h', hp'⟩ := seq_post aS opS gd prog hc
      (fun a'' ha'' => blk_neq aS opS gd prog haS hop hg hea heb hsa hsb ha'')
      (fun s1 hp1 b' hb' => hmat s1 _ hp1.res b' hb') hycf
    refine ⟨s', h', hp'.mono fun v hv => ?_⟩
    rw [hv, cmpBit_toNat]
    by_cases h : a = b <;> simp [h, JasminCmp.holds]
  · -- ult
    obtain ⟨s', h', hp'⟩ := seq_post aS opS gd prog hc
      (fun a'' ha'' => blk_below aS opS gd prog haS hg hea heb hsa hsb ha'')
      (fun s1 hp1 b' hb' => hmat s1 _ hp1.res b' hb') hycf
    refine ⟨s', h', hp'.mono fun v hv => ?_⟩
    rw [hv, cmpBit_toNat]
    simp [JasminCmp.holds, BitVec.ult]
  · -- ule
    obtain ⟨s', h', hp'⟩ := seq_post aS opS gd prog hc (fun a' ha' => seq_post aS opS gd prog ha'
      (fun a'' ha'' => blk_below aS opS gd prog haS hg heb hea hsb hsa ha'')
      (fun s1 hp1 b' hb' => hmat s1 _ hp1.res b' hb') hycf)
      (fun s2 hp2 b' hb' => hflip s2 _ hp2 b' hb') hyx
    refine ⟨s', h', hp'.mono fun v hv => ?_⟩
    have key : JasminCmp.ule.holds a b = !decide (b.toNat < a.toNat) := by
      simp only [JasminCmp.holds, BitVec.ule]
      by_cases h : b.toNat < a.toNat <;> simp [h]; omega
    rw [hv, cmpBit_toNat, key]
  · -- ugt
    obtain ⟨s', h', hp'⟩ := seq_post aS opS gd prog hc
      (fun a'' ha'' => blk_below aS opS gd prog haS hg heb hea hsb hsa ha'')
      (fun s1 hp1 b' hb' => hmat s1 _ hp1.res b' hb') hycf
    refine ⟨s', h', hp'.mono fun v hv => ?_⟩
    rw [hv, cmpBit_toNat]
    simp [JasminCmp.holds, BitVec.ult]
  · -- uge
    obtain ⟨s', h', hp'⟩ := seq_post aS opS gd prog hc (fun a' ha' => seq_post aS opS gd prog ha'
      (fun a'' ha'' => blk_below aS opS gd prog haS hg hea heb hsa hsb ha'')
      (fun s1 hp1 b' hb' => hmat s1 _ hp1.res b' hb') hycf)
      (fun s2 hp2 b' hb' => hflip s2 _ hp2 b' hb') hyx
    refine ⟨s', h', hp'.mono fun v hv => ?_⟩
    have key : JasminCmp.uge.holds a b = !decide (a.toNat < b.toNat) := by
      simp only [JasminCmp.holds, BitVec.ule]
      by_cases h : a.toNat < b.toNat <;> simp [h]; omega
    rw [hv, cmpBit_toNat, key]

end Seq

/-! ## 14. Assignments with truncation, select and casts -/

/-- A word truncated to a size no larger. -/
theorem truncateVal_word_le {ws ws' : MWSize} (h : ws.bits ≤ ws'.bits) (u : BitVec ws'.bits) :
    truncateVal (.cword ws) (.Vword ws' u) = .ok (.Vword ws (BitVec.ofNat ws.bits u.toNat)) := by
  simp [truncateVal, CatCrypt.Crypto.Jasmin.CoqSemMirror.truncateWord, h]

section Trunc
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- **Assignment with truncation over the Jasmin code.** -/
theorem sem_asgn_step_tr {x : JVar} (hx : OkV x) {e : APExpr} {e' : MPexpr}
    (he : translatePExprExt e = some e') {c : List AInstrR} {c' : List MInstr}
    (hc : translateCmdExt (asgn x e :: c) = some c') {s s2 : Estate SyscallState Mem}
    {v v' : Value}
    (hv : semPexpr (Mem := Mem) true gd opS s (typeE (mvar x).vtype e') = .ok v)
    (htr : truncateVal (evalAtype (mvar x).vtype) v = .ok v')
    (hdef : v'.isDefined = true) (hty : v'.typeOf = evalAtype (mvar x).vtype)
    (hrest : ∀ c'', translateCmdExt c = some c'' →
      Sem aS opS gd prog (s.withVm (s.evm.set (mvar x) v')) (typeC c'') s2) :
    Sem aS opS gd prog s (typeC c') s2 := by
  obtain ⟨i', c'', hi, hc', rfl⟩ := translateCmdExt_cons_inv hc
  rw [translateInstrRExt_asgn (translateVarIExt_mvi hx) he, Option.some.injEq] at hi
  subst hi
  exact sem_cons aS opS gd prog (.Eassgn _ _ _ _ _ _ v v' hv htr
    (writeLval_lvar opS gd (x := mvi x) hdef hty)) (hrest c'' hc')

/-- **Select.** `m = c; m = -m; x = a; x = x ^ b; x = x & m; x = x ^ b` writes
`selectW c a b` to `x`. -/
theorem sem_select (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true)
    {x cv a b : JVar} (hx : OkV x) (hcv : OkV cv) (ha : OkV a) (hb : OkV b)
    (hxt : (mvar x).vtype = .aword ws) (hxs : ¬ Scratch x.vname) (has : ¬ Scratch a.vname)
    (hbs : ¬ Scratch b.vname)
    (hbx : b.vname ≠ x.vname) {s : Estate SyscallState Mem} {cnd : BitVec 1}
    {va vb : BitVec ws.bits}
    (hvc : s.evm (mvar cv) = .Vword .U64 (BitVec.ofNat 64 cnd.toNat))
    (hva : s.evm (mvar a) = .Vword ws va) (hvb : s.evm (mvar b) = .Vword ws vb)
    {c' : List MInstr}
    (hc : translateCmdExt [asgn (tmp 0 (wsOf ws.bits)) (pv cv),
      asgn (tmp 0 (wsOf ws.bits)) (.Papp1 (.Oneg (wsOf ws.bits)) (pv (tmp 0 (wsOf ws.bits)))),
      asgn x (pv a), asgn x (.Papp2 (.Olxor (wsOf ws.bits)) (pv x) (pv b)),
      asgn x (.Papp2 (.Oland (wsOf ws.bits)) (pv x) (pv (tmp 0 (wsOf ws.bits)))),
      asgn x (.Papp2 (.Olxor (wsOf ws.bits)) (pv x) (pv b))] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws (selectW cnd va vb)) := by
  have hm := okV_tmp_gpr hg 0
  have hmt := mvar_tmp hg 0
  have hsc := scratch_tmp 0 (wsOf ws.bits)
  have hws := translateWSize_gpr hg
  have hle : ws.bits ≤ CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U64.bits := by
    cases ws <;> simp_all [gprB] <;> decide
  set m := mvar (tmp 0 (wsOf ws.bits))
  set mc : BitVec ws.bits := BitVec.ofNat ws.bits (BitVec.ofNat 64 cnd.toNat).toNat
  have hmx : m.vname ≠ x.vname := fun h => hxs (h ▸ hsc)
  have hbm : b.vname ≠ m.vname := ne_of_not_scratch hbs hsc
  have htx : ∀ u : BitVec ws.bits, (Value.Vword ws u).typeOf = evalAtype (mvar x).vtype :=
    fun _ => by rw [hxt]; rfl
  have htm : ∀ u : BitVec ws.bits, (Value.Vword ws u).typeOf = evalAtype m.vtype :=
    fun _ => by rw [hmt]; rfl
  refine ⟨s.withVm ((((((s.evm.set m (.Vword ws mc)).set m (.Vword ws (-mc))).set (mvar x)
      (.Vword ws va)).set (mvar x) (.Vword ws (va ^^^ vb))).set (mvar x)
      (.Vword ws ((va ^^^ vb) &&& -mc))).set (mvar x)
      (.Vword ws (((va ^^^ vb) &&& -mc) ^^^ vb))), ?_, post_of ?_ ?_ ?_⟩
  · refine sem_asgn_step_tr aS opS gd prog hm (translatePExprExt_pv (translateVarIExt_mvi hcv))
      hc (semPexpr_mpv opS gd hvc rfl) (by rw [hmt]; exact truncateVal_word_le hle _) rfl
      (htm _) (fun c1 hc1 => ?_)
    refine sem_asgn_step aS opS gd prog hm (translatePExprExt_papp1
      (op' := .Oneg (.Op_w ws)) (by simp [translateSOp1, hws])
      (translatePExprExt_pv (translateVarIExt_mvi hm))) hc1 (v := .Vword ws (-mc)) ?_ rfl
      (htm _) (fun c2 hc2 => ?_)
    · show semPexpr (Mem := Mem) true gd opS _ (.Papp1 (.Oneg (.Op_w ws)) (mpv (mvi _))) = _
      rw [semPexpr_papp1 opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)]
      exact hop.neg ws hg _
    refine sem_asgn_step aS opS gd prog hx (translatePExprExt_pv (translateVarIExt_mvi ha))
      hc2 (v := .Vword ws va) (semPexpr_mpv opS gd ?_ rfl) rfl (htx _) (fun c3 hc3 => ?_)
    · have ham : a.vname ≠ m.vname := ne_of_not_scratch has hsc
      simp only [Estate.withVm, mvi,
        set_ne (z := mvar a) (x := mvar (tmp 0 (wsOf ws.bits))) _ ham, hva]
    refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp2 (op' := .Olxor ws)
      (by simp [translateSOp2Ext, translateSOp2, hws])
      (translatePExprExt_pv (translateVarIExt_mvi hx))
      (translatePExprExt_pv (translateVarIExt_mvi hb))) hc3 (v := .Vword ws (va ^^^ vb)) ?_ rfl
      (htx _) (fun c4 hc4 => ?_)
    · show semPexpr (Mem := Mem) true gd opS _ (.Papp2 (.Olxor ws) (mpv (mvi x)) (mpv (mvi b))) = _
      rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (semPexpr_mpv opS gd (v := .Vword ws vb) (by
          simp only [Estate.withVm, mvi, set_ne (z := mvar b) (x := mvar x) _ hbx,
            set_ne (z := mvar b) (x := mvar (tmp 0 (wsOf ws.bits))) _ hbm, hvb]) rfl)]
      exact hop.lxor ws hg _ _
    refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp2 (op' := .Oland ws)
      (by simp [translateSOp2Ext, translateSOp2, hws])
      (translatePExprExt_pv (translateVarIExt_mvi hx))
      (translatePExprExt_pv (translateVarIExt_mvi hm))) hc4
      (v := .Vword ws ((va ^^^ vb) &&& -mc)) ?_ rfl (htx _) (fun c5 hc5 => ?_)
    · show semPexpr (Mem := Mem) true gd opS _ (.Papp2 (.Oland ws) (mpv (mvi x)) (mpv (mvi _))) = _
      rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (semPexpr_mpv opS gd (v := .Vword ws (-mc)) (by
          simp only [Estate.withVm, mvi,
            set_ne (z := mvar (tmp 0 (wsOf ws.bits))) (x := mvar x) _ hmx, set_same]) rfl)]
      exact hop.land ws hg _ _
    refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp2 (op' := .Olxor ws)
      (by simp [translateSOp2Ext, translateSOp2, hws])
      (translatePExprExt_pv (translateVarIExt_mvi hx))
      (translatePExprExt_pv (translateVarIExt_mvi hb))) hc5
      (v := .Vword ws (((va ^^^ vb) &&& -mc) ^^^ vb)) ?_ rfl (htx _)
      (fun c6 hc6 => sem_nil_step aS opS gd prog hc6 _)
    show semPexpr (Mem := Mem) true gd opS _ (.Papp2 (.Olxor ws) (mpv (mvi x)) (mpv (mvi b))) = _
    rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
      (semPexpr_mpv opS gd (v := .Vword ws vb) (by
        simp only [Estate.withVm, mvi, set_ne (z := mvar b) (x := mvar x) _ hbx,
          set_ne (z := mvar b) (x := mvar (tmp 0 (wsOf ws.bits))) _ hbm, hvb]) rfl)]
    exact hop.lxor ws hg _ _
  · simp only [set_same]
    congr 1
    rcases bitVec1_eq cnd with rfl | rfl
    · simp [mc, selectW]
    · have h1 : mc = 1 := by
        apply BitVec.eq_of_toNat_eq
        simp only [mc, BitVec.toNat_ofNat]
        cases ws <;> simp_all [gprB]
      rw [h1]
      simp [selectW, BitVec.neg_one_eq_allOnes, BitVec.xor_assoc]
  · intro z hz hzs
    have hzm : z.vname ≠ m.vname := ne_of_not_scratch hzs hsc
    rw [set_ne _ hz, set_ne _ hz, set_ne _ hz, set_ne _ hz, set_ne _ hzm, set_ne _ hzm]
  · exact fun h => arrTyped_set (arrTyped_set (arrTyped_set (arrTyped_set (arrTyped_set
      (arrTyped_set h rfl (htm _)) rfl (htm _)) rfl (htx _)) rfl (htx _)) rfl (htx _)) rfl (htx _)

/-- The bit width of `wsOf w` is that of `mws w` for every width other than `512`. -/
theorem bits_wsOf {w : Nat} (h : w ≠ 512) : (wsOf w).bits = (mws w).bits := by
  unfold wsOf mws
  split_ifs <;> rfl

/-- A width of `bitOkB` is at most the bit width of its mirror word size. -/
theorem le_mws_bits {w : Nat} (h : bitOkB w = true) : w ≤ (mws w).bits := by
  simp only [bitOkB, widthOkB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | ((h | h) | h) | h <;> subst h <;> decide

/-- A width of `bitOkB` other than `1` is the bit width of its mirror word size. -/
theorem mws_bits {w : Nat} (h : bitOkB w = true) (h1 : w ≠ 1) : (mws w).bits = w := by
  simp only [bitOkB, widthOkB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | ((h | h) | h) | h <;> subst h <;> first | rfl | exact absurd rfl h1

/-- A width of `bitOkB` is not `512`. -/
theorem ne_512_of_bitOk {w : Nat} (h : bitOkB w = true) : w ≠ 512 := by
  simp only [bitOkB, widthOkB, Bool.or_eq_true, beq_iff_eq] at h
  omega

/-- The value of a word read at a larger mirror word size. -/
theorem toNat_mws {w B : Nat} (va : BitVec w) (hB : w ≤ B) (B' : Nat) :
    (va.toNat % 2 ^ B) % 2 ^ B' = va.toNat % 2 ^ B' := by
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le va.isLt (Nat.pow_le_pow_right (by omega) hB))]

/-- **Cast.** The code `castCode x a w w'` writes the zero extension or truncation of `a` to
the width `w'` to `x`. -/
theorem sem_castW (hop : JazzOpAgrees opS) {w w' : Nat} (hw : bitOkB w = true)
    (hw' : bitOkB w' = true) {x a : JVar} (hx : OkV x) (ha : OkV a)
    (hxt : (mvar x).vtype = .aword (mws w')) {s : Estate SyscallState Mem} {va : BitVec w}
    (hva : s.evm (mvar a) = .Vword (mws w) (BitVec.ofNat _ va.toNat)) {c' : List MInstr}
    (hc : translateCmdExt (castCode x a w w') = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword (mws w') (BitVec.ofNat _ (va.setWidth w').toNat)) := by
  have gw := gprB_mws hw
  have gw' := gprB_mws hw'
  have hB := le_mws_bits hw
  have hty : ∀ u : BitVec (mws w').bits, (Value.Vword (mws w') u).typeOf =
      evalAtype (mvar x).vtype := fun _ => by rw [hxt]; rfl
  have hbw := bits_wsOf (ne_512_of_bitOk hw)
  have hbw' := bits_wsOf (ne_512_of_bitOk hw')
  have hz : translateSOp1 (.Ozeroext (wsOf w') (wsOf w)) = some (.Ozeroext (mws w') (mws w)) := by
    simp [translateSOp1, translateWSize_wsOf (ne_512_of_bitOk hw),
      translateWSize_wsOf (ne_512_of_bitOk hw')]
  -- the first instruction and its value
  obtain ⟨u, hfirst, hu⟩ : ∃ u : BitVec (mws w').bits, (∀ (c : List AInstrR) (c' : List MInstr),
      translateCmdExt ((if (wsOf w).bits < (wsOf w').bits then
        [asgn x (.Papp1 (.Ozeroext (wsOf w') (wsOf w)) (pv a))] else [asgn x (pv a)]) ++ c) =
        some c' → ∀ s2, (∀ c'', translateCmdExt c = some c'' →
          Sem aS opS gd prog (s.withVm (s.evm.set (mvar x) (.Vword (mws w') u))) (typeC c'') s2) →
        Sem aS opS gd prog s (typeC c') s2)
      ∧ u.toNat = va.toNat % 2 ^ (mws w').bits := by
    by_cases hlt : (wsOf w).bits < (wsOf w').bits
    · refine ⟨(BitVec.ofNat (mws w).bits va.toNat).setWidth (mws w').bits, fun c c' hc s2 hr => ?_,
        ?_⟩
      · rw [if_pos hlt] at hc
        refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp1 hz
          (translatePExprExt_pv (translateVarIExt_mvi ha))) hc ?_ rfl (hty _) hr
        show semPexpr (Mem := Mem) true gd opS s (.Papp1 (.Ozeroext (mws w') (mws w)) (mpv (mvi a)))
          = _
        rw [semPexpr_papp1 opS gd (semPexpr_mpv opS gd hva rfl), hop.zeroext _ _ gw' gw]
      · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        exact toNat_mws va hB _
    · have hle : (mws w').bits ≤ (mws w).bits := by omega
      refine ⟨BitVec.ofNat (mws w').bits (BitVec.ofNat (mws w).bits va.toNat).toNat,
        fun c c' hc s2 hr => ?_, ?_⟩
      · rw [if_neg hlt] at hc
        exact sem_asgn_step_tr aS opS gd prog hx (translatePExprExt_pv (translateVarIExt_mvi ha))
          hc (semPexpr_mpv opS gd hva rfl) (by rw [hxt]; exact truncateVal_word_le hle _) rfl
          (hty _) hr
      · simp only [BitVec.toNat_ofNat]
        exact toNat_mws va hB _
  unfold castCode at hc
  by_cases h1 : w' = 1
  · subst h1
    rw [if_pos rfl] at hc
    have hxt' : (mvar x).vtype = .aword .U64 := hxt
    have hty1 : ∀ u : BitVec 64, (Value.Vword .U64 u).typeOf = evalAtype (mvar x).vtype :=
      fun _ => by rw [hxt']; rfl
    refine ⟨s.withVm ((s.evm.set (mvar x) (.Vword (mws 1) u)).set (mvar x)
      (.Vword .U64 ((show BitVec 64 from u) &&& BitVec.ofInt 64 1))), hfirst _ c' hc _
        (fun c1 hc1 => ?_),
      post_of ?_ (fun z hz _ => by rw [set_ne _ hz, set_ne _ hz])
        (fun h => arrTyped_set (arrTyped_set h rfl (hty _)) rfl (hty1 _))⟩
    · refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp2 (op' := .Oland .U64) rfl
        (translatePExprExt_pv (translateVarIExt_mvi hx)) (translatePExprExt_cnst 1)) hc1 ?_ rfl
        (hty1 _) (fun c2 hc2 => sem_nil_step aS opS gd prog hc2 _)
      rw [hxt']
      show semPexpr (Mem := Mem) true gd opS _
        (.Papp2 (.Oland .U64) (mpv (mvi x)) (typeConst (.aword .U64) 1)) = _
      rw [semPexpr_papp2 opS gd (semPexpr_mpv opS gd (set_same _ _ _) rfl)
        (semPexpr_wconst opS gd hop rfl _ 1)]
      exact hop.land .U64 rfl _ _
    · rw [set_same]
      congr 1
      apply BitVec.eq_of_toNat_eq
      have hu' : u.toNat = va.toNat % 2 ^ 64 := hu
      change (u.toNat &&& (BitVec.ofInt 64 1).toNat) =
        (va.setWidth 1).toNat % 2 ^ 64
      rw [show (BitVec.ofInt 64 1).toNat = 1 from rfl, Nat.and_one_is_mod, hu',
        BitVec.toNat_setWidth]
      omega
  · rw [if_neg h1, List.append_nil] at hc
    refine ⟨s.withVm (s.evm.set (mvar x) (.Vword (mws w') u)), hfirst [] c'
      (by rw [List.append_nil]; exact hc) _ (fun c'' hc'' => sem_nil_step aS opS gd prog hc'' _),
      post_of ?_ (fun z hz _ => set_ne _ hz) (fun h => arrTyped_set h rfl (hty _))⟩
    rw [set_same]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [hu, BitVec.toNat_ofNat, BitVec.toNat_setWidth, mws_bits hw' h1, Nat.mod_mod]

/-- The shifts `shl` and `shr` translate to mirror operators that, on a count truncated to
`u8`, compute `JasminBinOp.apply`. -/
theorem shiftSop_sem {opS : OpSem} (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true)
    {bop : JasminBinOp} (hsh : bop = .shl ∨ bop = .shr) :
    ∃ mop, translateSOp2Ext (binSop (wsOf ws.bits) bop) = some mop ∧
      ∀ a b : BitVec ws.bits, opS.sem_sop2 mop (.Vword ws a)
        (.Vword .U8 (BitVec.ofNat _ b.toNat)) = .ok (.Vword ws (bop.apply a b)) := by
  have hws := translateWSize_gpr hg
  rcases hsh with rfl | rfl
  · refine ⟨.Olsl (.Op_w ws), by simp [binSop, translateSOp2Ext, translateSOp2, hws],
      fun a b => ?_⟩
    rw [hop.lsl ws .U8 hg rfl a _, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide),
      shiftMask_mod256 hg]
    rfl
  · refine ⟨.Olsr ws, by simp [binSop, translateSOp2Ext, translateSOp2, hws], fun a b => ?_⟩
    rw [hop.lsr ws .U8 hg rfl a _, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide),
      shiftMask_mod256 hg]
    rfl

/-- **Register shift.** `x = a; t = b; x = x OP t`, with the count truncated to the `u8`
scratch register `t` (`cntV`), writes `bop.apply a b` to `x` for the shifts `shl` and
`shr`. -/
theorem sem_shiftReg (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true)
    {bop : JasminBinOp} (hsh : bop = .shl ∨ bop = .shr) {x a b : JVar} (hx : OkV x)
    (ha : OkV a) (hb : OkV b) (hxt : (mvar x).vtype = .aword ws) (hxs : ¬ Scratch x.vname)
    (hbx : b.vname ≠ x.vname) {s : Estate SyscallState Mem} {va vb : BitVec ws.bits}
    (hva : s.evm (mvar a) = .Vword ws va) (hvb : s.evm (mvar b) = .Vword ws vb)
    {c' : List MInstr}
    (hc : translateCmdExt [asgn x (pv a), asgn cntV (pv b),
      asgn x (.Papp2 (binSop (wsOf ws.bits) bop) (pv x) (pv cntV))] = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar x) (· = .Vword ws (bop.apply va vb)) := by
  have hg8 : gprB .U8 = true := rfl
  have hm : OkV cntV := okV_tmp_gpr hg8 0
  have hmt : (mvar cntV).vtype = .aword .U8 := mvar_tmp hg8 0
  have hsc : Scratch (mvar cntV).vname := scratch_tmp 0 .U8
  have hle : CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits ≤ ws.bits := by
    cases ws <;> simp_all [gprB] <;> decide
  obtain ⟨mop, hmop, hsem⟩ := shiftSop_sem hop hg hsh
  have hmx : (mvar cntV).vname ≠ x.vname := fun h => hxs (h ▸ hsc)
  have htx : ∀ u : BitVec ws.bits, (Value.Vword ws u).typeOf = evalAtype (mvar x).vtype :=
    fun _ => by rw [hxt]; rfl
  have htm : ∀ u : BitVec CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.U8.bits,
      (Value.Vword .U8 u).typeOf = evalAtype (mvar cntV).vtype :=
    fun _ => by rw [hmt]; rfl
  refine ⟨s.withVm (((s.evm.set (mvar x) (.Vword ws va)).set (mvar cntV)
      (.Vword .U8 (BitVec.ofNat _ vb.toNat))).set (mvar x) (.Vword ws (bop.apply va vb))), ?_,
    post_of (by simp) ?_ ?_⟩
  · refine sem_asgn_step aS opS gd prog hx (translatePExprExt_pv (translateVarIExt_mvi ha))
      hc (semPexpr_mpv opS gd hva rfl) rfl (htx va) (fun c1 hc1 => ?_)
    refine sem_asgn_step_tr aS opS gd prog hm (translatePExprExt_pv (translateVarIExt_mvi hb))
      hc1 (v := .Vword ws vb) (semPexpr_mpv opS gd ?_ rfl)
      (by rw [hmt]; exact truncateVal_word_le hle vb) rfl
      (htm _) (fun c2 hc2 => ?_)
    · exact (set_ne _ hbx).trans hvb
    refine sem_asgn_step aS opS gd prog hx (translatePExprExt_papp2 hmop
      (translatePExprExt_pv (translateVarIExt_mvi hx))
      (translatePExprExt_pv (translateVarIExt_mvi hm))) hc2 ?_ rfl (htx _)
      (fun c3 hc3 => sem_nil_step aS opS gd prog hc3 _)
    show semPexpr (Mem := Mem) true gd opS _ (.Papp2 mop (mpv (mvi x)) (mpv (mvi cntV))) = _
    rw [semPexpr_papp2 opS gd
      (semPexpr_mpv opS gd ((set_ne _ (Ne.symm hmx)).trans (set_same _ _ _)) rfl)
      (semPexpr_mpv opS gd (set_same _ _ _) rfl), hsem]
  · intro z hz hzs
    rw [set_ne _ hz, set_ne _ (ne_of_not_scratch hzs hsc), set_ne _ hz]
  · exact fun h => arrTyped_set (arrTyped_set (arrTyped_set h rfl (htx _)) rfl (htm _)) rfl
      (htx _)

end Trunc

/-! ## 15. The array operations -/

/-- **Store-immediate image.** `A[k] = v` translates to the mirror write at the constant
index. -/
theorem translateCmdExt_stackStoreImm {w n k d : Nat} {x a v : JVar} {a' v' : MVarI}
    {ws' : MWSize} (hws : translateWSize (wsOf w) = some ws')
    (ha : translateVarIExt ⟨a, vi0⟩ = some a') (hv : translateVarIExt ⟨v, vi0⟩ = some v') :
    (emitOp (.stackStoreImm w n k) d x [a, v]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [.Cassgn (.Laset .Unaligned .AAscale ws' a' (.Pconst (k : Int))) .AT_none
        (.aword ws') (mpv v')]) := by
  have he : emitOp (.stackStoreImm w n k) d x [a, v] =
      some ([.Cassgn (.Laset .AAscale (wsOf w) ⟨a, vi0⟩ (cnst k)) .AT_none (.sword (wsOf w))
        (pv v)], a) := rfl
  rw [he, Option.bind_some]
  refine translateCmdExt_mkCmd (.cons ?_ .nil)
  simp [translateInstrRExt, translateLValExt, hws, ha, translateIdx, intOfWordIdx,
    translateArrAccess, translateSTypeExt, translateSType, translatePExprExt_pv hv,
    translateAssgnTag, cnst, translatePExprExt, translatePExpr]

/-- **Zeroing image.** `for i = 0 to n { x[i] = 0 }` translates to the mirror loop. -/
theorem translateCmdExt_stackZero {w n d : Nat} {x : JVar} {as : List JVar} {ws' : MWSize}
    (hws : translateWSize (wsOf w) = some ws') (hx : OkV x) :
    (emitOp (.stackZero w n) d x as).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [.Cfor (mvi (mkV 'i' d .sint))
        ⟨.UpTo, .Pconst 0, .Pconst (n : Int)⟩
        [.MkI () (.Cassgn (.Laset .Unaligned .AAscale ws' (mvi x) (mpv (mvi (mkV 'i' d .sint))))
          .AT_none (.aword ws') (.Pconst 0))]]) := by
  have hj : OkV (mkV 'i' d .sint) := okV_mkV sint_ne_U512
  have he : emitOp (.stackZero w n) d x as =
      some ([.Cfor ⟨mkV 'i' d .sint, vi0⟩ ⟨.UpTo, 0, n⟩
        [.Cassgn (.Laset .AAscale (wsOf w) ⟨x, vi0⟩ (pv (mkV 'i' d .sint))) .AT_none
          (.sword (wsOf w)) (cnst 0)]], x) := rfl
  rw [he, Option.bind_some]
  refine translateCmdExt_mkCmd (.cons ?_ .nil)
  have hidx : translateIdx (pv (mkV 'i' d .sint)) = some (mpv (mvi (mkV 'i' d .sint))) := by
    unfold translateIdx intOfWordIdx
    simp only [pv]
    rw [if_neg (by simp [mkV])]
    exact translatePExprExt_pv (translateVarIExt_mvi hj)
  have hbody : translateCmdExt [.Cassgn (.Laset .AAscale (wsOf w) ⟨x, vi0⟩ (pv (mkV 'i' d .sint)))
      .AT_none (.sword (wsOf w)) (cnst 0)] =
      some [.MkI () (.Cassgn (.Laset .Unaligned .AAscale ws' (mvi x) (mpv (mvi (mkV 'i' d .sint))))
        .AT_none (.aword ws') (.Pconst 0))] := by
    simp [translateCmdExt, translateInstrRExt, translateLValExt, hws, translateVarIExt_mvi hx,
      hidx, translateArrAccess, translateSTypeExt, translateSType, translateAssgnTag, cnst,
      translatePExprExt, translatePExpr]
  simp [translateInstrRExt, translateVarIExt_mvi hj, hbody, translateDir]

section ArrOps
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- **Load.** `x = A[(uint) i]` writes the element `i` of the array. -/
theorem sem_stackLoad (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true)
    {x a i : JVar} (hx : OkV x) (ha : OkV a) (hi : OkV i) (hxt : (mvar x).vtype = .aword ws)
    {s : Estate SyscallState Mem} {n : Nat} {arr : JArrayMirror (n * ws.bytes)}
    (hva : s.evm (mvar a) = .Varr _ arr) {vi : BitVec 64}
    (hvi : s.evm (mvar i) = .Vword .U64 vi) (hin : vi.toNat < n) {k d : Nat}
    {c' : List MInstr}
    (hc : (emitOp (.stackLoad ws.bits k) d x [a, i]).bind (fun r => translateCmdExt r.1) =
      some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ Post s s' (mvar x)
      (· = .Vword ws (BitVec.ofNat ws.bits (arr.readLE (vi.toNat * ws.bytes) ws.bytes))) := by
  rw [translateCmdExt_stackLoad (translateWSize_gpr hg) (translateVarIExt_mvi hx)
    (translateVarIExt_mvi ha) (translateVarIExt_mvi hi), Option.some.injEq] at hc
  subst hc
  have hty : ∀ u : BitVec ws.bits, (Value.Vword ws u).typeOf = evalAtype (mvar x).vtype :=
    fun _ => by rw [hxt]; rfl
  refine ⟨s.withVm (s.evm.set (mvar x)
      (.Vword ws (BitVec.ofNat ws.bits (arr.readLE (vi.toNat * ws.bytes) ws.bytes)))),
    ?_, post_of (by simp) (fun z hz _ => set_ne _ hz) (fun h => arrTyped_set h rfl (hty _))⟩
  rw [typeC_mkCmd]
  refine sem_cons aS opS gd prog (semIr_masgn aS opS gd prog (x := mvi x) ?_ rfl (hty _))
    (.Eskip _)
  show semPexpr (Mem := Mem) true gd opS s (.Pget .Unaligned .AAscale ws (mkLvar (mvi a))
    (.Papp1 (.Oint_of_word .Unsigned .U64) (mpv (mvi i)))) = _
  rw [semPexpr_pget opS gd hva ((semPexpr_papp1 opS gd (semPexpr_mpv opS gd hvi rfl)).trans
    (hop.intOfWord vi)) ws, getWord_scaled ws arr hin]
  rfl

/-- **Store.** `A[(uint) i] = v` writes the word `v` at the element `i` of the array, in
place. -/
theorem sem_stackStore {ws : MWSize} (hg : gprB ws = true) (hop : JazzOpAgrees opS)
    {x a i v : JVar} (ha : OkV a) (hi : OkV i) (hv : OkV v)
    {n : Nat} (hat : (mvar a).vtype = .aarr .U8 (n * ws.bytes))
    {s : Estate SyscallState Mem} {arr : JArrayMirror (n * ws.bytes)}
    (hva : s.evm (mvar a) = .Varr _ arr) {vi : BitVec 64}
    (hvi : s.evm (mvar i) = .Vword .U64 vi) (hin : vi.toNat < n) {vv : BitVec ws.bits}
    (hvv : s.evm (mvar v) = .Vword ws vv) {k d : Nat} {c' : List MInstr}
    (hc : (emitOp (.stackStore ws.bits k) d x [a, i, v]).bind (fun r => translateCmdExt r.1) =
      some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ Post s s' (mvar a)
      (· = .Varr _ (arr.writeLE (vi.toNat * ws.bytes) ws.bytes vv.toNat)) := by
  rw [translateCmdExt_stackStore (translateWSize_gpr hg) (translateVarIExt_mvi ha)
    (translateVarIExt_mvi hi) (translateVarIExt_mvi hv), Option.some.injEq] at hc
  subst hc
  refine ⟨s.withVm (s.evm.set (mvar a)
      (.Varr _ (arr.writeLE (vi.toNat * ws.bytes) ws.bytes vv.toNat))),
    ?_, post_of (by simp) (fun z hz _ => set_ne _ hz)
      (fun h => arrTyped_set h rfl (by rw [hat]; rfl))⟩
  rw [typeC_mkCmd]
  exact sem_cons aS opS gd prog (semIr_store aS opS gd prog (a := mvi a) hva hat hin
    ((semPexpr_papp1 opS gd (semPexpr_mpv opS gd hvi rfl)).trans (hop.intOfWord vi))
    (semPexpr_mpv opS gd hvv rfl)) (.Eskip _)

/-- **Store at a constant index.** `A[k] = v` writes the word `v` at the element `k`. -/
theorem sem_stackStoreImm {ws : MWSize} (hg : gprB ws = true) {x a v : JVar} (ha : OkV a)
    (hv : OkV v) {n : Nat} (hat : (mvar a).vtype = .aarr .U8 (n * ws.bytes))
    {s : Estate SyscallState Mem} {arr : JArrayMirror (n * ws.bytes)}
    (hva : s.evm (mvar a) = .Varr _ arr) {k : Nat} (hk : k < n) {vv : BitVec ws.bits}
    (hvv : s.evm (mvar v) = .Vword ws vv) {d : Nat} {c' : List MInstr}
    (hc : (emitOp (.stackStoreImm ws.bits n k) d x [a, v]).bind (fun r => translateCmdExt r.1) =
      some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ Post s s' (mvar a)
      (· = .Varr _ (arr.writeLE (k * ws.bytes) ws.bytes vv.toNat)) := by
  rw [translateCmdExt_stackStoreImm (translateWSize_gpr hg) (translateVarIExt_mvi ha)
    (translateVarIExt_mvi hv), Option.some.injEq] at hc
  subst hc
  refine ⟨s.withVm (s.evm.set (mvar a) (.Varr _ (arr.writeLE (k * ws.bytes) ws.bytes vv.toNat))),
    ?_, post_of (by simp) (fun z hz _ => set_ne _ hz)
      (fun h => arrTyped_set h rfl (by rw [hat]; rfl))⟩
  rw [typeC_mkCmd]
  exact sem_cons aS opS gd prog (semIr_store aS opS gd prog (a := mvi a) hva hat hk rfl
    (semPexpr_mpv opS gd hvv rfl)) (.Eskip _)

/-- **Zeroing.** `for i = 0 to n { x[i] = 0 }` over the fresh array variable `x` writes an
array of zero words. -/
theorem sem_stackZero (hop : JazzOpAgrees opS) {ws : MWSize} (hg : gprB ws = true) {n d : Nat}
    {x : JVar} {as : List JVar} (hx : OkV x) (hxt : (mvar x).vtype = .aarr .U8 (n * ws.bytes))
    (hxs : ¬ Scratch x.vname) {s : Estate SyscallState Mem} (harr : VmArrTyped s.evm)
    {c' : List MInstr}
    (hc : (emitOp (.stackZero ws.bits n) d x as).bind (fun r => translateCmdExt r.1) = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ Post s s' (mvar x)
      (fun v => ∃ arr : JArrayMirror (n * ws.bytes), v = .Varr _ arr ∧
        ∀ q : Fin n, arr.readLE (q.val * ws.bytes) ws.bytes = 0) := by
  rw [translateCmdExt_stackZero (translateWSize_gpr hg) hx, Option.some.injEq] at hc
  subst hc
  have hsc := scratch_idx d .sint
  have hxj : (mvi x).v_var ≠ (mvi (mkV 'i' d .sint)).v_var := fun h => hxs (by
    have h' : x.vname = (mvar (mkV 'i' d .sint)).vname :=
      congrArg CatCrypt.Crypto.Jasmin.CoqSemMirror.Var.vname h
    rw [h']
    exact hsc)
  obtain ⟨arr, harr0⟩ := harr (mvar x) _ _ hxt
  obtain ⟨s', arr', hfor, hscs, hm, hx', hrd, hfr, harr'⟩ :=
    semIr_zero aS opS gd prog hop hg hxj rfl hxt harr0
  refine ⟨s', ?_, ⟨hscs, hm, ⟨arr', hx', hrd⟩, fun z hz hzs => hfr z
    (fun h => hz (h ▸ rfl)) (fun h => hzs (h ▸ hsc)), harr'⟩⟩
  rw [typeC_mkCmd]
  exact sem_cons aS opS gd prog hfor (.Eskip _)

end ArrOps

/-! ## 16. The index precondition -/

/-- The array accesses of one operation on the arguments `args` are in range: the index of
a load or store is below the length of the array. -/
def opIdxOk (op : JasminOp) :
    HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op) → Prop :=
  match op with
  | .stackLoad _ n => fun args => (args.tail.head : BitVec 64).toNat < n
  | .stackStore _ n => fun args => (args.tail.head : BitVec 64).toNat < n
  | .stackStoreImm _ n k => fun _ => k < n
  | _ => fun _ => True

/-- The tuples of an exit-flag loop after `n` runs of its body that returned the bit `1`. -/
def whileStates {cs : List JasminTy}
    (step : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs))) :
    Nat → Ctxt.Valuation (d := jasminDialect) cs → Option (Ctxt.Valuation (d := jasminDialect) cs)
  | 0, acc => some acc
  | n + 1, acc => step acc >>= fun r =>
      if HasBoolBit.toBool (d := jasminDialect) r.head then whileStates step n r.tail else none

/-- **Index precondition.** Along the denotation of `p` in the call environment `E` at the
fuel `fuel`, every load and store reads or writes an element in range: at each binding the
indices of `opIdxOk`, in each run of a loop body from each tuple the run reaches, in the
branch taken, and in the continuation of each construct from each value it denotes. -/
def IdxInBounds (E : CallEnv jasminDialect) (fuel : Nat) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
      Ctxt.Valuation Γ → Prop
  | _, _, .ret _, _ => True
  | _, _, .var e k, V =>
      opIdxOk e.op (Expr.lookupArgs e.args V) ∧ IdxInBounds E fuel k (V.extend (e.denote V))
  | _, _, .forLoop count inits body k, V =>
      (∀ (i : Nat) acc, i < HasWord64.toNat (d := jasminDialect) (count.lookup V) →
        (List.range i).foldlM (fun acc j => body.denoteAt E fuel
          (MultiBlockLowering.hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) j) V)))
          (Expr.lookupArgs inits V) = some acc →
        IdxInBounds E fuel body
          (MultiBlockLowering.hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V))) ∧
      ∀ acc, (List.range (HasWord64.toNat (d := jasminDialect) (count.lookup V))).foldlM
          (fun acc j => body.denoteAt E fuel
            (MultiBlockLowering.hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) j) V)))
          (Expr.lookupArgs inits V) = some acc →
        IdxInBounds E fuel k (MultiBlockLowering.hvAppend acc V)
  | _, _, .ifThenElse cond thn els k, V =>
      (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then IdxInBounds E fuel thn V
        else IdxInBounds E fuel els V) ∧
      ∀ r, (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then
          thn.denoteAt E fuel V else els.denoteAt E fuel V) = some r →
        IdxInBounds E fuel k (MultiBlockLowering.hvAppend r V)
  | _, _, .whileLoop inits body k, V =>
      (∀ (n : Nat) acc, whileStates (fun acc => body.denoteAt E fuel
          (MultiBlockLowering.hvAppend acc V)) n (Expr.lookupArgs inits V) = some acc →
        IdxInBounds E fuel body (MultiBlockLowering.hvAppend acc V)) ∧
      ∀ acc, NFProg.whileIter (fun acc => body.denoteAt E fuel
          (MultiBlockLowering.hvAppend acc V)) fuel (Expr.lookupArgs inits V) = some acc →
        IdxInBounds E fuel k (MultiBlockLowering.hvAppend acc V)
  | _, _, .call (as := as) (rs := rs) f args k, V =>
      ∀ r, E.call f as rs (Expr.lookupArgs args V) = some r →
        IdxInBounds E fuel k (MultiBlockLowering.hvAppend r V)

/-! ## 17. Names and arguments -/

/-- Names with different leading characters differ. -/
theorem nameOf_ne {c c' : Char} (h : c ≠ c') (k k' : Nat) (s s' : ASType) :
    nameOf c k s ≠ nameOf c' k' s' :=
  fun e => h (nameOf_inj e).1

/-- A variable whose leading character is neither `t` nor `i` is not a scratch variable. -/
theorem not_scratch_mkV {c : Char} (ht : c ≠ 't') (hi : c ≠ 'i') (k : Nat) (s : ASType) :
    ¬ Scratch (mkV c k s).vname := by
  rintro (h | ⟨k', s', h | h⟩)
  · exact cf_ne_nameOf c k s h.symm
  · exact ht (nameOf_inj h).1
  · exact hi (nameOf_inj h).1

/-- An argument or a binding is not a scratch variable. -/
theorem EnvBelow.not_scratch {d : Nat} {v : JVar} (h : EnvBelow d v) : ¬ Scratch v.vname := by
  rcases h with ⟨k, s, rfl⟩ | ⟨k, s, _, rfl⟩ <;> exact not_scratch_mkV (by decide) (by decide) _ _

/-- An argument or a binding below `d` is not the binding at `d`. -/
theorem EnvBelow.ne_new {d : Nat} {v : JVar} (h : EnvBelow d v) (s0 : ASType) :
    v.vname ≠ (mkV 'r' d s0).vname := by
  rcases h with ⟨k, s, rfl⟩ | ⟨k, s, hk, rfl⟩
  · exact nameOf_ne (by decide) _ _ _ _
  · intro e
    have := (nameOf_inj e).2.1
    omega

/-- `EnvBelow` is monotone in the depth. -/
theorem EnvBelow.mono {d d' : Nat} {v : JVar} (h : EnvBelow d v) (hd : d ≤ d') :
    EnvBelow d' v := by
  rcases h with h | ⟨k, s, hk, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, s, by omega, rfl⟩

/-- The facts the code of a binding needs of an operand variable. -/
structure ArgOk (d : Nat) (t : JasminTy) (val : ⟦t⟧) (vm : Vm) (x : JVar) : Prop where
  /-- It translates. -/
  ok : OkV x
  /-- It is not a scratch variable. -/
  scr : ¬ Scratch x.vname
  /-- It is not the binding at `d`. -/
  fresh : ∀ s0, x.vname ≠ (mkV 'r' d s0).vname
  /-- It holds its value. -/
  agr : JazzVarAgrees x t val vm

omit [MemModel Mem] in
/-- A live operand variable satisfies `ArgOk`. -/
theorem argOk {env : List JVar} {d : Nat} {L : Nat → Prop} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {s : Estate SyscallState Mem} (hs : JazzStoreAgrees env d L V s)
    {t : JasminTy} (v : Ctxt.Var Γ t) (hl : L (varIndex v)) (ht : tyOkB t = true) :
    ArgOk d t (v.lookup V) s.evm (env.getD (varIndex v) dfltV) := by
  have ha := hs.agree v hl
  have hb := hs.below _ hl
  exact ⟨by rw [OkV, ha.1]; exact styOf_ne_U512 ht, hb.not_scratch, hb.ne_new, ha⟩

/-- A word read back at its own size. -/
theorem vword_ofNat (ws : MWSize) (u : BitVec ws.bits) :
    Value.Vword ws (BitVec.ofNat ws.bits u.toNat) = Value.Vword ws u := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The value of a register of a width of `gprB`. -/
theorem reg_val {ws : MWSize} (_hg : gprB ws = true) {u : BitVec ws.bits} {v : Value}
    (h : JazzValAgrees (.reg ws.bits) u v) : v = .Vword ws u := by
  rw [show v = _ from h]
  cases ws <;> exact vword_ofNat _ u

/-- A word of a width of `gprB` holds its register value. -/
theorem reg_val_mk {ws : MWSize} (_hg : gprB ws = true) (u : BitVec ws.bits) :
    JazzValAgrees (.reg ws.bits) u (.Vword ws u) := by
  show Value.Vword ws u = _
  cases ws <;> exact (vword_ofNat _ u).symm

/-- The bytes of an array of a width of `gprB`. -/
theorem arr_val {ws : MWSize} (hg : gprB ws = true) {n : Nat} {A : Fin n → BitVec ws.bits}
    {v : Value} (h : JazzValAgrees (.stackArr ws.bits n) A v) :
    ∃ arr : JArrayMirror (n * ws.bytes), v = .Varr _ arr ∧
      ∀ j : Fin n, arr.readLE (j.val * ws.bytes) ws.bytes = (A j).toNat := by
  cases ws <;> simp only [gprB] at hg <;> exact h

/-- An array of bytes holding the words `A`. -/
theorem arr_val_mk {ws : MWSize} (hg : gprB ws = true) {n : Nat} {A : Fin n → BitVec ws.bits}
    {arr : JArrayMirror (n * ws.bytes)}
    (h : ∀ j : Fin n, arr.readLE (j.val * ws.bytes) ws.bytes = (A j).toNat) :
    JazzValAgrees (.stackArr ws.bits n) A (.Varr _ arr) := by
  cases ws <;> simp only [gprB] at hg <;> exact ⟨arr, rfl, h⟩

/-- The mirror type of the binding of a register of a width of `gprB`. -/
theorem mvar_new_reg {ws : MWSize} (hg : gprB ws = true) (d : Nat) :
    (mvar (mkV 'r' d (styOf (.reg ws.bits)))).vtype = .aword ws := by
  rw [mvar_vtype_reg rfl (ne_512_of_bitOk (by simp [bitOkB, widthOkB_bits hg])), mws_gpr hg]

/-- The mirror type of an array variable of a width of `gprB`. -/
theorem mvar_arr {ws : MWSize} (hg : gprB ws = true) {x : JVar} {n : Nat}
    (hx : x.vtype = styOf (.stackArr ws.bits n)) : (mvar x).vtype = .aarr .U8 (n * ws.bytes) := by
  rw [mvar_vtype_arr hx (ne_512_of_bitOk (by simp [bitOkB, widthOkB_bits hg])), mws_gpr hg]

/-- The binding at `d` is not a scratch variable. -/
theorem not_scratch_new (d : Nat) (s : ASType) : ¬ Scratch (mkV 'r' d s).vname :=
  not_scratch_mkV (by decide) (by decide) d s

/-! ## 18. Codes and values of the operations -/

/-- The operations of `regArith` other than `andn` pass `opOkB` at a width of `widthOkB`. -/
theorem opOkB_regArith {bop : JasminBinOp} (hb : bop ≠ .andn) (w : Nat) :
    opOkB (.regArith bop w) = widthOkB w := by
  cases bop <;> first | rfl | exact absurd rfl hb

/-- The code of `regArith` other than `andn` and the shifts `shl` and `shr`. -/
theorem emitOp_regArith {bop : JasminBinOp} (hb : bop ≠ .andn)
    (hsh : ¬ (bop = .shl ∨ bop = .shr)) (w d : Nat) (x : JVar) (as : List JVar) :
    emitOp (.regArith bop w) d x as = some ([asgn x (pv (as.getD 0 dfltV)),
      asgn x (.Papp2 (binSop (wsOf w) bop) (pv x) (pv (as.getD 1 dfltV)))], x) := by
  cases bop <;> first | rfl | exact absurd rfl hb | exact absurd (by simp) hsh

/-- The code of the shifts `shl` and `shr` of `regArith`: the count moved to the `u8`
register `cntV`. -/
theorem emitOp_shiftReg {bop : JasminBinOp} (hsh : bop = .shl ∨ bop = .shr) (w d : Nat)
    (x : JVar) (as : List JVar) :
    emitOp (.regArith bop w) d x as = some ([asgn x (pv (as.getD 0 dfltV)),
      asgn cntV (pv (as.getD 1 dfltV)),
      asgn x (.Papp2 (binSop (wsOf w) bop) (pv x) (pv cntV))], x) := by
  rcases hsh with rfl | rfl <;> rfl

/-- The select code moves the condition word with a plain assignment at the widths of
`gprB`. -/
theorem castCode_sel {ws : MWSize} (hg : gprB ws = true) (m c : JVar) :
    castCode m c 64 ws.bits = [asgn m (pv c)] := by
  cases ws <;> first | rfl | simp [gprB] at hg

/-- The word of `ADC` on a carry bit is `addCarryWord`. -/
theorem adc_word {w : Nat} (a b : BitVec w) (cin : BitVec 1) :
    (x86_ADC a b (decide (cin.toNat = 1))).word = addCarryWord a b cin := by
  apply BitVec.eq_of_toNat_eq
  rcases bitVec1_eq cin with rfl | rfl <;>
    simp [x86_ADC, rflags_of_aluop, add_carry, addCarryWord, BitVec.toNat_add, Nat.add_mod]

/-- The carry-out of `ADC` on a carry bit is `carryOutBit`. -/
theorem adc_carry {w : Nat} (a b : BitVec w) (cin : BitVec 1) :
    BitVec.ofNat 64 (if decide (2 ^ w ≤ a.toNat + b.toNat + (if cin.toNat = 1 then 1 else 0))
      then 1 else 0) = BitVec.ofNat 64 (carryOutBit a b cin).toNat := by
  rcases bitVec1_eq cin with rfl | rfl <;> simp only [carryOutBit] <;> split_ifs <;>
    first | rfl | (simp_all; omega) | simp_all

/-- The constant of `cmpImm` is the word `BitVec.ofNat w n`. -/
theorem ofInt_mod (w n : Nat) : BitVec.ofInt w ((n % 2 ^ w : Nat) : Int) = BitVec.ofNat w n := by
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp

/-- Two-operand argument vectors. -/
theorem hv2 {Γ : Ctxt jasminDialect} {t1 t2 : JasminTy}
    (args : HVector (fun t => Ctxt.Var Γ t) [t1, t2]) :
    ∃ a b, args = .cons a (.cons b .nil) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  exact ⟨a, b, rfl⟩

/-- Three-operand argument vectors. -/
theorem hv3 {Γ : Ctxt jasminDialect} {t1 t2 t3 : JasminTy}
    (args : HVector (fun t => Ctxt.Var Γ t) [t1, t2, t3]) :
    ∃ a b c, args = .cons a (.cons b (.cons c .nil)) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
  exact ⟨a, b, c, rfl⟩

/-- One-operand argument vectors. -/
theorem hv1 {Γ : Ctxt jasminDialect} {t1 : JasminTy}
    (args : HVector (fun t => Ctxt.Var Γ t) [t1]) : ∃ a, args = .cons a .nil := by
  rcases args with _ | ⟨a, _ | _⟩
  exact ⟨a, rfl⟩

/-- Closes the membership of an operand index in the indices of its argument vector. -/
local macro "hv_mem" : tactic => `(tactic| first
  | exact List.mem_cons_self
  | exact List.mem_cons_of_mem _ List.mem_cons_self
  | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-! ## 19. The code of one binding -/

section Emit
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- **The code of one binding.** For an operation that passes `opOkB`
bound at a type of `tyOkB`, from a state that agrees with `V` on the operands,
with its array indices in range, the translated and typed code `emitOp` emits runs to a
state in which the variable `y` it returns holds the denotation of the operation and every
other variable outside the scratch variables is unchanged. `y` is the fresh binding at `d`,
or the array operand of an in-place store. -/
theorem emitOp_sem (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t) (hok : opOkB e.op = true)
    (ht : tyOkB t = true) {env : List JVar} {d : Nat}
    {L : Nat → Prop} {V : Ctxt.Valuation Γ} {s : Estate SyscallState Mem}
    (hs : JazzStoreAgrees env d L V s) (hL : ∀ i ∈ hvIdxs e.args, L i)
    (hidx : opIdxOk e.op (Expr.lookupArgs e.args V)) {c : List AInstrR} {y : JVar}
    (he : emitOp e.op d (mkV 'r' d (styOf t)) (resolveHV env e.args) = some (c, y))
    {c' : List MInstr} (hc : translateCmdExt c = some c') :
    ∃ s', Sem aS opS gd prog s (typeC c') s' ∧
      Post s s' (mvar y) (JazzValAgrees t (e.denote V)) ∧ y.vtype = styOf t ∧
      ((storeSrc? e.op (hvIdxs e.args) = none ∧ y = mkV 'r' d (styOf t)) ∨
        ∃ a, storeSrc? e.op (hvIdxs e.args) = some a ∧ y = env.getD a dfltV) := by
  have hb : (emitOp e.op d (mkV 'r' d (styOf t)) (resolveHV env e.args)).bind
      (fun r => translateCmdExt r.1) = some c' := by rw [he]; exact hc
  obtain ⟨op, hret, args⟩ := e
  cases hret
  have hxok : OkV (mkV 'r' d (styOf (DialectSignature.ret (d := jasminDialect) op))) :=
    okV_mkV (styOf_ne_U512 ht)
  have hxs := not_scratch_new d (styOf (DialectSignature.ret (d := jasminDialect) op))
  have hmem : ∀ v ∈ hvIdxs args, L v := hL
  cases op with
  | regArith bop w =>
      obtain ⟨a, b, rfl⟩ := hv2 (t1 := .reg w) (t2 := .reg w) args
      by_cases hbop : bop = .andn
      · subst hbop
        have hw : bmiOkB w = true := hok
        obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (widthOkB_of_bmi hw)
        have hbm : bmiB ws = true := by
          cases ws <;> simp_all [bmiOkB, gprB, bmiB, CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.bits]
        have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
        have A := argOk hs a (hmem _ (by hv_mem)) htw
        have B := argOk hs b (hmem _ (by hv_mem)) htw
        have he' : some ([copn (asmName "ANDN" (wsOf ws.bits))
            (outsW (mkV 'r' d (styOf (.reg ws.bits))))
            [pv (env.getD (varIndex a) dfltV), pv (env.getD (varIndex b) dfltV)]],
            mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
        obtain ⟨s', hsem, hp⟩ := sem_andn aS opS gd prog haS hg hbm hxok A.ok B.ok
          (mvar_new_reg hg d) (reg_val hg A.agr.2) (reg_val hg B.agr.2) hc
        exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; exact reg_val_mk hg _, rfl,
          Or.inl ⟨rfl, rfl⟩⟩
      · have hw : widthOkB w = true := (opOkB_regArith hbop w).symm.trans hok
        obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr hw
        have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
        have A := argOk hs a (hmem _ (by hv_mem)) htw
        have B := argOk hs b (hmem _ (by hv_mem)) htw
        by_cases hsh : bop = .shl ∨ bop = .shr
        · have he' := (emitOp_shiftReg hsh ws.bits d (mkV 'r' d (styOf (.reg ws.bits)))
            [env.getD (varIndex a) dfltV, env.getD (varIndex b) dfltV]).symm.trans he
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
          obtain ⟨s', hsem, hp⟩ := sem_shiftReg aS opS gd prog hop hg hsh hxok A.ok B.ok
            (mvar_new_reg hg d) hxs (B.fresh _) (reg_val hg A.agr.2) (reg_val hg B.agr.2) hc
          exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; exact reg_val_mk hg _, rfl,
            Or.inl ⟨rfl, rfl⟩⟩
        have he' := (emitOp_regArith hbop hsh ws.bits d (mkV 'r' d (styOf (.reg ws.bits)))
          [env.getD (varIndex a) dfltV, env.getD (varIndex b) dfltV]).symm.trans he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
        obtain ⟨s', hsem, hp⟩ := sem_regArith aS opS gd prog hop hg hbop hxok A.ok B.ok
          (mvar_new_reg hg d) (B.fresh _) (reg_val hg A.agr.2) (reg_val hg B.agr.2) hc
        exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; exact reg_val_mk hg _, rfl,
          Or.inl ⟨rfl, rfl⟩⟩
  | regConst w n =>
      have hw : bitOkB w = true := ht
      have he' : some ([asgn (mkV 'r' d (styOf (.reg w))) (cnst ((n % 2 ^ w : Nat) : Int))],
          mkV 'r' d (styOf (.reg w))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_regConst aS opS gd prog hop (gprB_mws hw) hxok
        (mvar_vtype_reg rfl (ne_512_of_bitOk hw)) (s := s) hc
      refine ⟨s', hsem, hp.mono fun v hv => ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      rw [hv]
      show _ = Value.Vword (mws w) (BitVec.ofNat _ (BitVec.ofNat w n).toNat)
      rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  | shrImm w n =>
      obtain ⟨a, rfl⟩ := hv1 (t1 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have he' : some ([asgn (mkV 'r' d (styOf (.reg ws.bits))) (pv (env.getD (varIndex a) dfltV)),
          asgn (mkV 'r' d (styOf (.reg ws.bits))) (.Papp2 (.Olsr (wsOf ws.bits))
            (pv (mkV 'r' d (styOf (.reg ws.bits)))) (cnst (shiftMask ws.bits n)))],
          mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_shiftImm aS opS gd prog hop hg (mop := .Olsr ws)
        (by simp [translateSOp2Ext, translateSOp2, translateWSize_gpr hg]) rfl
        (f := fun u => u >>> shiftMask ws.bits n)
        (fun u => by
          rw [hop.lsr ws .U8 hg rfl u _, toNat_ofInt_u8 (by have := shiftMask_lt hg n; omega),
            shiftMask_idem hg])
        hxok A.ok (mvar_new_reg hg d) (reg_val hg A.agr.2) hc
      exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; exact reg_val_mk hg _, rfl,
        Or.inl ⟨rfl, rfl⟩⟩
  | shlImm w n =>
      obtain ⟨a, rfl⟩ := hv1 (t1 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have he' : some ([asgn (mkV 'r' d (styOf (.reg ws.bits))) (pv (env.getD (varIndex a) dfltV)),
          asgn (mkV 'r' d (styOf (.reg ws.bits))) (.Papp2 (.Olsl (wsOf ws.bits))
            (pv (mkV 'r' d (styOf (.reg ws.bits)))) (cnst (shiftMask ws.bits n)))],
          mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_shiftImm aS opS gd prog hop hg (mop := .Olsl (.Op_w ws))
        (by simp [translateSOp2Ext, translateSOp2, translateWSize_gpr hg]) rfl
        (f := fun u => u <<< shiftMask ws.bits n)
        (fun u => by
          rw [hop.lsl ws .U8 hg rfl u _, toNat_ofInt_u8 (by have := shiftMask_lt hg n; omega),
            shiftMask_idem hg])
        hxok A.ok (mvar_new_reg hg d) (reg_val hg A.agr.2) hc
      exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; exact reg_val_mk hg _, rfl,
        Or.inl ⟨rfl, rfl⟩⟩
  | sarImm w n =>
      obtain ⟨a, rfl⟩ := hv1 (t1 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have hpos : 0 < ws.bits := by cases ws <;> simp_all [gprB] <;> decide
      have hsc := sarCount_lt hpos n
      have he' : some ([asgn (mkV 'r' d (styOf (.reg ws.bits))) (pv (env.getD (varIndex a) dfltV)),
          asgn (mkV 'r' d (styOf (.reg ws.bits))) (.Papp2 (.Oasr (wsOf ws.bits))
            (pv (mkV 'r' d (styOf (.reg ws.bits)))) (cnst (sarCount ws.bits n)))],
          mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_shiftImm aS opS gd prog hop hg (mop := .Oasr (.Op_w ws))
        (by simp [translateSOp2Ext, translateSOp2, translateWSize_gpr hg]) rfl
        (f := fun u => u.sshiftRight (sarCount ws.bits n))
        (fun u => by
          rw [hop.asr ws .U8 hg rfl u _, toNat_ofInt_u8 (by
            have : ws.bits ≤ 64 := by cases ws <;> simp_all [gprB] <;> decide
            omega), shiftMask_of_lt hsc])
        hxok A.ok (mvar_new_reg hg d) (reg_val hg A.agr.2) hc
      refine ⟨s', hsem, hp.mono fun v hv => ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      rw [hv, sshiftRight_sarCount]
      exact reg_val_mk hg _
  | rorImm w n =>
      obtain ⟨a, rfl⟩ := hv1 (t1 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have hpos : 0 < ws.bits := by cases ws <;> simp_all [gprB] <;> decide
      have he' : some ([asgn (mkV 'r' d (styOf (.reg ws.bits))) (pv (env.getD (varIndex a) dfltV)),
          copn (asmName "ROR" (wsOf ws.bits)) [none, none, some (mkV 'r' d (styOf (.reg ws.bits)))]
            [pv (mkV 'r' d (styOf (.reg ws.bits))), cnst ((n % ws.bits : Nat) : Int)]],
          mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_ror aS opS gd prog haS hop hg (m := n % ws.bits)
        (Nat.mod_lt _ hpos) hxok A.ok (mvar_new_reg hg d) (reg_val hg A.agr.2) hc
      refine ⟨s', hsem, hp.mono fun v hv => ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      rw [hv, BitVec.rotateRight_mod_eq_rotateRight]
      exact reg_val_mk hg _
  | castW w w' =>
      obtain ⟨a, rfl⟩ := hv1 (t1 := .reg w) args
      have hww : bitOkB w = true ∧ bitOkB w' = true := by
        simpa [opOkB, Bool.and_eq_true] using hok
      have A := argOk hs a (hmem _ (by hv_mem)) (show tyOkB (.reg w) = true from hww.1)
      have he' : some (castCode (mkV 'r' d (styOf (.reg w'))) (env.getD (varIndex a) dfltV) w w',
          mkV 'r' d (styOf (.reg w'))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_castW aS opS gd prog hop hww.1 hww.2 hxok A.ok
        (mvar_vtype_reg rfl (ne_512_of_bitOk hww.2)) A.agr.2 hc
      exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | stackLoad w n =>
      obtain ⟨a, i, rfl⟩ := hv2 (t1 := .stackArr w n) (t2 := .reg 64) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have A := argOk hs a (hmem _ (by hv_mem))
        (show tyOkB (.stackArr ws.bits n) = true from widthOkB_bits hg)
      have I := argOk hs i (hmem _ (by hv_mem)) (show tyOkB (.reg 64) = true from rfl)
      obtain ⟨arr, hva, hrd⟩ := arr_val hg A.agr.2
      have hvi := reg_val (ws := .U64) rfl I.agr.2
      have hin : (i.lookup V).toNat < n := hidx
      have he' : some ([asgn (mkV 'r' d (styOf (.reg ws.bits))) (.Pget .AAscale (wsOf ws.bits)
          ⟨⟨env.getD (varIndex a) dfltV, vi0⟩, false⟩
          (.Papp1 (.Oint_of_word .U64) (pv (env.getD (varIndex i) dfltV))))],
          mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_stackLoad aS opS gd prog hop hg hxok A.ok I.ok
        (mvar_new_reg hg d) hva hvi hin hb
      refine ⟨s', hsem, hp.mono fun v hv => ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      have hget := stackGet_id (a.lookup V) ⟨_, hin⟩
      show JazzValAgrees (.reg ws.bits) (stackGet (a.lookup V) (i.lookup V).toNat) v
      rw [hget, hv, hrd ⟨_, hin⟩, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact reg_val_mk hg _
  | stackStore w n =>
      obtain ⟨a, i, u, rfl⟩ := hv3 (t1 := .stackArr w n) (t2 := .reg 64) (t3 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have A := argOk hs a (hmem _ (by hv_mem))
        (show tyOkB (.stackArr ws.bits n) = true from widthOkB_bits hg)
      have I := argOk hs i (hmem _ (by hv_mem)) (show tyOkB (.reg 64) = true from rfl)
      have U := argOk hs u (hmem _ (by hv_mem))
        (show tyOkB (.reg ws.bits) = true by simp [tyOkB, bitOkB, widthOkB_bits hg])
      obtain ⟨arr, hva, hrd⟩ := arr_val hg A.agr.2
      have hvi := reg_val (ws := .U64) rfl I.agr.2
      have hin : (i.lookup V).toNat < n := hidx
      have he' : some ([.Cassgn (.Laset .AAscale (wsOf ws.bits) ⟨env.getD (varIndex a) dfltV, vi0⟩
          (.Papp1 (.Oint_of_word .U64) (pv (env.getD (varIndex i) dfltV)))) .AT_none
          (.sword (wsOf ws.bits)) (pv (env.getD (varIndex u) dfltV))],
          env.getD (varIndex a) dfltV) = some (c, y) := he
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_stackStore aS opS gd prog hg hop A.ok I.ok U.ok
        (mvar_arr hg A.agr.1) hva hvi hin (reg_val hg U.agr.2) hb
      refine ⟨s', hsem, hp.mono fun v hv => ?_, A.agr.1, Or.inr ⟨varIndex a, rfl, rfl⟩⟩
      rw [hv]
      exact arr_val_mk hg (readLE_store hg hrd hin _)
  | stackStoreImm w n k =>
      obtain ⟨a, u, rfl⟩ := hv2 (t1 := .stackArr w n) (t2 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have A := argOk hs a (hmem _ (by hv_mem))
        (show tyOkB (.stackArr ws.bits n) = true from widthOkB_bits hg)
      have U := argOk hs u (hmem _ (by hv_mem))
        (show tyOkB (.reg ws.bits) = true by simp [tyOkB, bitOkB, widthOkB_bits hg])
      obtain ⟨arr, hva, hrd⟩ := arr_val hg A.agr.2
      have hin : k < n := hidx
      have he' : some ([.Cassgn (.Laset .AAscale (wsOf ws.bits) ⟨env.getD (varIndex a) dfltV, vi0⟩
          (cnst k)) .AT_none (.sword (wsOf ws.bits)) (pv (env.getD (varIndex u) dfltV))],
          env.getD (varIndex a) dfltV) = some (c, y) := he
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_stackStoreImm aS opS gd prog hg A.ok U.ok
        (mvar_arr hg A.agr.1) hva hin (reg_val hg U.agr.2) hb
      refine ⟨s', hsem, hp.mono fun v hv => ?_, A.agr.1, Or.inr ⟨varIndex a, rfl, rfl⟩⟩
      rw [hv]
      exact arr_val_mk hg (readLE_store hg hrd hin _)
  | stackZero w n =>
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have he' : some ([.Cfor ⟨mkV 'i' d .sint, vi0⟩ ⟨.UpTo, 0, n⟩
          [.Cassgn (.Laset .AAscale (wsOf ws.bits) ⟨mkV 'r' d (styOf (.stackArr ws.bits n)), vi0⟩
            (pv (mkV 'i' d .sint))) .AT_none (.sword (wsOf ws.bits)) (cnst 0)]],
          mkV 'r' d (styOf (.stackArr ws.bits n))) = some (c, y) := he
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_stackZero aS opS gd prog hop hg hxok (mvar_arr hg rfl) hxs
        hs.arrTyped hb
      refine ⟨s', hsem, hp.mono fun v hv => ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      obtain ⟨arr, rfl, h0⟩ := hv
      exact arr_val_mk hg fun j => (h0 j).trans rfl
  | mulhi w =>
      obtain ⟨a, b, rfl⟩ := hv2 (t1 := .reg w) (t2 := .reg w) args
      have hw : bmiOkB w = true := hok
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (widthOkB_of_bmi hw)
      have hbm : bmiB ws = true := by
        cases ws <;> simp_all [bmiOkB, gprB, bmiB, CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize.bits]
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have B := argOk hs b (hmem _ (by hv_mem)) htw
      have he' : some ([copn (asmName "MULX_lo_hi" (wsOf ws.bits))
          [none, some (mkV 'r' d (styOf (.reg ws.bits)))]
          [pv (env.getD (varIndex a) dfltV), pv (env.getD (varIndex b) dfltV)]],
          mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_mulhi aS opS gd prog haS hg hbm hxok A.ok B.ok
        (mvar_new_reg hg d) (reg_val hg A.agr.2) (reg_val hg B.agr.2) hc
      exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; exact reg_val_mk hg _, rfl,
        Or.inl ⟨rfl, rfl⟩⟩
  | addCarryLo w =>
      obtain ⟨a, b, cv, rfl⟩ := hv3 (t1 := .reg w) (t2 := .reg w) (t3 := .reg 1) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have B := argOk hs b (hmem _ (by hv_mem)) htw
      have C := argOk hs cv (hmem _ (by hv_mem)) (show tyOkB (.reg 1) = true from rfl)
      have he' : some ([cinCode (env.getD (varIndex cv) dfltV),
          asgn (mkV 'r' d (styOf (.reg ws.bits))) (pv (env.getD (varIndex a) dfltV)),
          copn (asmName "ADC" (wsOf ws.bits)) (outsCW (mkV 'r' d (styOf (.reg ws.bits))))
            [pv (mkV 'r' d (styOf (.reg ws.bits))), pv (env.getD (varIndex b) dfltV), pv cfVar]],
          mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_addCarryLo aS opS gd prog haS hop hg hxok A.ok B.ok C.ok
        (mvar_new_reg hg d) hxs A.scr B.scr C.scr (B.fresh _) (reg_val hg A.agr.2)
        (reg_val hg B.agr.2) C.agr.2 hc
      refine ⟨s', hsem, hp.mono fun v hv => ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      rw [hv, adc_word]
      exact reg_val_mk hg _
  | addCarryHi w =>
      obtain ⟨a, b, cv, rfl⟩ := hv3 (t1 := .reg w) (t2 := .reg w) (t3 := .reg 1) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have B := argOk hs b (hmem _ (by hv_mem)) htw
      have C := argOk hs cv (hmem _ (by hv_mem)) (show tyOkB (.reg 1) = true from rfl)
      have he' : some ([cinCode (env.getD (varIndex cv) dfltV),
          asgn (tmp 1 (wsOf ws.bits)) (pv (env.getD (varIndex a) dfltV)),
          copn (asmName "ADC" (wsOf ws.bits)) (outsCW (tmp 1 (wsOf ws.bits)))
            [pv (tmp 1 (wsOf ws.bits)), pv (env.getD (varIndex b) dfltV), pv cfVar]] ++
            matCF (mkV 'r' d (styOf (.reg 1))),
          mkV 'r' d (styOf (.reg 1))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_addCarryHi aS opS gd prog haS hop hg hxok A.ok B.ok C.ok
        (mvar_vtype_reg (w := 1) rfl (by decide)) hxs A.scr B.scr C.scr (reg_val hg A.agr.2)
        (reg_val hg B.agr.2) C.agr.2 hc
      refine ⟨s', hsem, hp.mono fun v hv => ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      rw [hv, adc_carry]
      rfl
  | cmp cc w =>
      obtain ⟨a, b, rfl⟩ := hv2 (t1 := .reg w) (t2 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have B := argOk hs b (hmem _ (by hv_mem)) htw
      have he' : some (cmpCode cc (wsOf ws.bits) (mkV 'r' d (styOf (.reg 1)))
          (pv (env.getD (varIndex a) dfltV)) (pv (env.getD (varIndex b) dfltV)),
          mkV 'r' d (styOf (.reg 1))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_cmpCode aS opS gd prog haS hop hg cc hxok
        (mvar_vtype_reg (w := 1) rfl (by decide)) hxs (translatePExprExt_pv (translateVarIExt_mvi A.ok))
        (translatePExprExt_pv (translateVarIExt_mvi B.ok)) (stable_mpv A.scr (reg_val hg A.agr.2))
        (stable_mpv B.scr (reg_val hg B.agr.2)) hc
      exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | cmpImm cc w n =>
      obtain ⟨a, rfl⟩ := hv1 (t1 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have he' : some (cmpCode cc (wsOf ws.bits) (mkV 'r' d (styOf (.reg 1)))
          (pv (env.getD (varIndex a) dfltV)) (cnst ((n % 2 ^ ws.bits : Nat) : Int)),
          mkV 'r' d (styOf (.reg 1))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      obtain ⟨s', hsem, hp⟩ := sem_cmpCode aS opS gd prog haS hop hg cc hxok
        (mvar_vtype_reg (w := 1) rfl (by decide)) hxs (translatePExprExt_pv (translateVarIExt_mvi A.ok))
        (translatePExprExt_cnst _) (stable_mpv A.scr (reg_val hg A.agr.2))
        (stable_const hop hg _) hc
      refine ⟨s', hsem, hp.mono fun v hv => ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      rw [hv, ofInt_mod]
      rfl
  | select w =>
      obtain ⟨cv, a, b, rfl⟩ := hv3 (t1 := .reg 1) (t2 := .reg w) (t3 := .reg w) args
      obtain ⟨ws, hg, rfl, -, -⟩ := exists_gpr (show widthOkB w = true from hok)
      have htw : tyOkB (.reg ws.bits) = true := by simp [tyOkB, bitOkB, widthOkB_bits hg]
      have C := argOk hs cv (hmem _ (by hv_mem)) (show tyOkB (.reg 1) = true from rfl)
      have A := argOk hs a (hmem _ (by hv_mem)) htw
      have B := argOk hs b (hmem _ (by hv_mem)) htw
      have he' : some (castCode (tmp 0 (wsOf ws.bits)) (env.getD (varIndex cv) dfltV) 64 ws.bits ++
          [asgn (tmp 0 (wsOf ws.bits)) (.Papp1 (.Oneg (wsOf ws.bits)) (pv (tmp 0 (wsOf ws.bits)))),
            asgn (mkV 'r' d (styOf (.reg ws.bits))) (pv (env.getD (varIndex a) dfltV)),
            asgn (mkV 'r' d (styOf (.reg ws.bits))) (.Papp2 (.Olxor (wsOf ws.bits))
              (pv (mkV 'r' d (styOf (.reg ws.bits)))) (pv (env.getD (varIndex b) dfltV))),
            asgn (mkV 'r' d (styOf (.reg ws.bits))) (.Papp2 (.Oland (wsOf ws.bits))
              (pv (mkV 'r' d (styOf (.reg ws.bits)))) (pv (tmp 0 (wsOf ws.bits)))),
            asgn (mkV 'r' d (styOf (.reg ws.bits))) (.Papp2 (.Olxor (wsOf ws.bits))
              (pv (mkV 'r' d (styOf (.reg ws.bits)))) (pv (env.getD (varIndex b) dfltV)))],
          mkV 'r' d (styOf (.reg ws.bits))) = some (c, y) := he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
      rw [castCode_sel hg] at hc
      obtain ⟨s', hsem, hp⟩ := sem_select aS opS gd prog hop hg hxok C.ok A.ok B.ok
        (mvar_new_reg hg d) hxs A.scr B.scr (B.fresh _) C.agr.2 (reg_val hg A.agr.2)
        (reg_val hg B.agr.2) hc
      exact ⟨s', hsem, hp.mono fun v hv => by rw [hv]; exact reg_val_mk hg _, rfl,
        Or.inl ⟨rfl, rfl⟩⟩
  | _ => simp [emitOp] at he

end Emit

/-! ## 20. Straight-line regions -/

/-- The straight-line programs: let-bindings, then `ret`. -/
def LetsThenRet : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Prop
  | _, _, .ret _ => True
  | _, _, .var _ k => LetsThenRet k
  | _, _, _ => False

omit [MemModel Mem] in
/-- The returned variables of a store that agrees on their indices hold their values. -/
theorem resAgrees_ret {env : List JVar} {d : Nat} {L : Nat → Prop} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {s : Estate SyscallState Mem} (hs : JazzStoreAgrees env d L V s) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts),
      (∀ i ∈ hvIdxs vs, L i) → JazzResAgrees (resolveHV env vs) (Expr.lookupArgs vs V) s
  | [], .nil, _ => trivial
  | _ :: _, .cons v vs, h =>
      ⟨hs.agree v (h _ List.mem_cons_self),
        resAgrees_ret hs vs fun i hi => h i (List.mem_cons_of_mem _ hi)⟩

section Body
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- **Straight-line regions.** A straight-line region that `widthsGo` and the
in-place store check `linGo` accept, lowered by `nfToJasminBody` and translated and typed,
runs from a state that agrees with `V` on the variables the region reads, with its array
indices in range, to a state in which the returned variables hold the values the region
denotes. -/
theorem nfToJasminBody_sem (haS : JazzAsmAgrees aS) (hop : JazzOpAgrees opS)
    (E : CallEnv jasminDialect) (fuel : Nat) :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts),
      LetsThenRet p → widthsGo p = true →
      ∀ {loc : Nat} {env : List JVar} {d n : Nat} {out : JOut}, linGo p loc = true →
      nfToJasminBody env p d n = some out →
      ∀ {c' : List MInstr}, translateCmdExt out.code = some c' →
      ∀ {V : Ctxt.Valuation Γ} {r : HVector (fun t => ⟦t⟧) ts}, p.denoteAt E fuel V = some r →
      IdxInBounds E fuel p V →
      ∀ {s : Estate SyscallState Mem}, JazzStoreAgrees env d (fun i => usesIdx p i = true) V s →
      ∃ s', Sem aS opS gd prog s (typeC c') s' ∧ JazzResAgrees out.res r s' := by
  intro Γ ts p
  induction p with
  | ret vs =>
      intro _ _ loc env d n out _ hout c' hc V r hden _ s hs
      simp only [nfToJasminBody, Option.some.injEq] at hout
      subst hout
      have hr : r = Expr.lookupArgs vs V := by
        simpa [NFProg.denoteAt, NFProg.denote] using hden.symm
      subst hr
      refine ⟨s, sem_nil_step aS opS gd prog hc s, resAgrees_ret hs vs fun i hi => ?_⟩
      simp [usesIdx, hi]
  | @var Γ t ts e k ih =>
      intro hsl hw loc env d n out hlin hout c' hc V r hden hidx s hs
      simp only [widthsGo, Bool.and_eq_true] at hw
      obtain ⟨⟨ht, hok⟩, hwk⟩ := hw
      simp only [linGo, Bool.and_eq_true] at hlin
      obtain ⟨hlin1, hlink⟩ := hlin
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hout
      obtain ⟨⟨cx, y⟩, hcx, rk, hrk, rfl⟩ := hout
      obtain ⟨a', b', ha', hb', rfl⟩ := translateCmdExt_append_inv hc
      obtain ⟨s1, hsem1, hp, hyt, hsrc⟩ := emitOp_sem aS opS gd prog haS hop e hok ht
        hs (fun i hi => by simp [usesIdx, hi]) hidx.1 hcx ha'
      have hden' : k.denoteAt E fuel (V.extend (e.denote V)) = some r := by
        simpa [NFProg.denoteAt, NFProg.denote] using hden
      -- the fresh or in-place variable is distinct from the other live variables
      have hne : ∀ i, usesIdx k (i + 1) = true →
          (env.getD i dfltV).vname ≠ y.vname := by
        intro i hi
        rcases hsrc with ⟨_, rfl⟩ | ⟨a, ha, rfl⟩
        · exact (hs.below i (by simp [usesIdx, hi])).ne_new _
        · rw [ha] at hlin1
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hlin1
          intro heq
          have hai : a ∈ hvIdxs e.args := by
            revert ha
            unfold storeSrc?
            split <;> simp_all
          have := hs.inj i a (by simp [usesIdx, hi]) (by simp [usesIdx, hai]) heq
          subst this
          rw [hlin1.2] at hi
          exact Bool.false_ne_true hi
      have hyb : EnvBelow (d + 1) y := by
        rcases hsrc with ⟨_, rfl⟩ | ⟨a, ha, rfl⟩
        · exact Or.inr ⟨d, _, by omega, rfl⟩
        · have hai : a ∈ hvIdxs e.args := by
            revert ha
            unfold storeSrc?
            split <;> simp_all
          exact (hs.below a (by simp [usesIdx, hai])).mono (by omega)
      have hs1 : JazzStoreAgrees (y :: env) (d + 1) (fun i => usesIdx k i = true)
          (V.extend (e.denote V)) s1 := by
        refine ⟨fun {t'} v hl => ?_, fun i hl => ?_, fun i j hi hj heq => ?_, hp.arr hs.arrTyped⟩
        · cases v with
          | here => exact ⟨hyt, hp.res⟩
          | there v =>
              have hl' : usesIdx (NFProg.var e k) (varIndex v) = true := by
                simp [usesIdx, show usesIdx k (varIndex v + 1) = true from hl]
              have ho := hs.agree v hl'
              refine ⟨ho.1, ?_⟩
              show JazzValAgrees t' (v.lookup V) (s1.evm (mvar (env.getD (varIndex v) dfltV)))
              rw [hp.frame _ (hne _ hl) (hs.below _ hl').not_scratch]
              exact ho.2
        · cases i with
          | zero => exact hyb
          | succ i =>
              exact (hs.below i (by simp [usesIdx, show usesIdx k (i + 1) = true from hl])).mono
                (by omega)
        · cases i with
          | zero =>
              cases j with
              | zero => rfl
              | succ j => exact absurd heq.symm (hne j hj)
          | succ i =>
              cases j with
              | zero => exact absurd heq (hne i hi)
              | succ j =>
                  exact congrArg (· + 1) (hs.inj i j (by simp [usesIdx, show usesIdx k (i + 1) = true from hi])
                    (by simp [usesIdx, show usesIdx k (j + 1) = true from hj]) heq)
      obtain ⟨s2, hsem2, hres⟩ := ih hsl hwk hlink hrk hb' hden' hidx.2 hs1
      refine ⟨s2, ?_, hres⟩
      rw [typeC_append]
      exact ComJasminBridgeProgram.sem_append aS opS gd prog hsem1 hsem2
  | forLoop => intro hsl; exact absurd hsl id
  | ifThenElse => intro hsl; exact absurd hsl id
  | whileLoop => intro hsl; exact absurd hsl id
  | call => intro hsl; exact absurd hsl id

end Body

end CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSem
