/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

@[expose] public section

set_option autoImplicit false

/-!
# Array-returning straight-line simulation (the array analogue of `comToLprog_lsemMem`)

`comToLprog_lsemMem` (`JasminLsemMem`) is the straight-line linearizer simulation
for a **register-returning** `ScalarMemN` update: it decodes the result at a
register via `decodeM`. An array-accumulator loop body (`mpn_mul_1`'s limb body)
returns a `.stackArr w n`, so the scalar brick is out of scope.

This module supplies the array-return analogue.

## Main results

* `ArrMemN` — the array-returning memref straight-line fragment: the same
  `.var` binding arms as `ScalarMemN` (register arithmetic / const / select /
  shifts / mulhi / carry lo-hi / cast / stack load / stack store), but the
  terminal `.ret` returns a `.stackArr w n` variable.
* `lsemStraightMemArr_straightOps_store` — the strengthened straight-line
  simulation for an `ArrMemN` chain: run + final store agreement with the
  binding-extended valuation + write frame. The `.var` induction is the
  `lsemStraightMem_straightOps_store` skeleton; the array terminal contributes
  only the trivial base case.
* `denoteLets_getArr_comRetReg` — read the returned array off the final
  agreement: at the return slot `comRetReg`, `getArr`/`decodeArrM` returns the
  chain's denotation. A structural `Com` induction, terminal-type-agnostic in
  the `.var` case.
* `comToLprog_lsemMemArr` — the composed array-return simulation: running
  `straightOpsMem` of an `ArrMemN` update from the encoded valuation leaves the
  result array at `comRetReg`, `decodeArrM`-readable, equal to `Com.denote`.

The returned array lands at the SSA return slot `comRetReg` (a fresh
`regName`-block slot for a chain whose final binding is a store), not at the
accumulator argument slot; wiring this as the per-trip `hsim` of
`loopMemArr_export_faithful_denote` requires the store to target the accumulator
slot in place (as `fillBodyM` does), which `straightOpsMem` does not emit.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrReturn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)

/-! ## 1. The array-returning memref straight-line fragment -/

/-- The array-returning stack-memory straight-line fragment: the same binding
    arms as `ScalarMemN`, with the terminal returning a `.stackArr w n`. -/
inductive ArrMemN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | retArr {Γ : Ctxt jasminDialect} {w n : Nat} (v : Ctxt.Var Γ (.stackArr w n)) :
      ArrMemN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | const {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (n : Nat)
      (hwn : w = 64 ∨ w = 32)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.regConst w n, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.select w, heq, args⟩ body)
  | shr {Γ : Ctxt jasminDialect} {s : JasminTy} {w m : Nat} (hm : m < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w m) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w m)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.shrImm w m, heq, args⟩ body)
  | shl {Γ : Ctxt jasminDialect} {s : JasminTy} {w m : Nat} (hm : m < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w m) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w m)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.shlImm w m, heq, args⟩ body)
  | sar {Γ : Ctxt jasminDialect} {s : JasminTy} {w m : Nat} (hm : m < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w m) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w m)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.sarImm w m, heq, args⟩ body)
  | mulhi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.mulhi w, heq, args⟩ body)
  | addLo {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body)
  | addHi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
      {body : Com jasminDialect (.reg 1 :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body)
  | cast {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.castW w w', heq, args⟩ body)
  | load {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackLoad w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.stackLoad w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.stackLoad w n, heq, args⟩ body)
  | store {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackStore w n)
        = .stackArr w n)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.stackStore w n)))
      {body : Com jasminDialect (.stackArr w n :: Γ) s}
      (hbody : ArrMemN body) :
      ArrMemN (.var ⟨JasminOp.stackStore w n, heq, args⟩ body)

/-- An `ArrMemN` program returns a stack array. -/
theorem ArrMemN.ret_arr {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ArrMemN com) : ∃ w n, t = .stackArr w n := by
  induction hcom with
  | retArr v => exact ⟨_, _, rfl⟩
  | var _ _ _ _ ih => exact ih
  | const _ _ _ _ _ ih => exact ih
  | sel _ _ _ ih => exact ih
  | shr _ _ _ _ ih => exact ih
  | shl _ _ _ _ ih => exact ih
  | sar _ _ _ _ ih => exact ih
  | mulhi _ _ _ ih => exact ih
  | addLo _ _ _ ih => exact ih
  | addHi _ _ _ ih => exact ih
  | cast _ _ _ ih => exact ih
  | load _ _ _ ih => exact ih
  | store _ _ _ ih => exact ih

/-- Depth bookkeeping for the strengthened induction: one binding shifts the
    final depth by one. -/
theorem arr_shift_depth {nArgs a b : Nat} {Γ' : Ctxt jasminDialect}
    {st : LstateM} {V : Ctxt.Valuation Γ'}
    (h : StoreAgreesM nArgs ((a + 1) + b) st V) :
    StoreAgreesM nArgs (a + (b + 1)) st V := by
  rw [show a + (b + 1) = (a + 1) + b from by omega]
  exact h

/-! ## 2. The strengthened straight-line simulation for an array-returning chain -/

/-- **Core simulation, strengthened conclusion, array-returning chain.** As
    `lsemStraightMem_straightOps_store`, for an `ArrMemN` chain: the landing state
    agrees with the binding-extended valuation `comDenoteLets com V` at the final
    depth, and the write frame confines the touched slots to the fresh
    `regName`-block. The `.var` arms are the `lsemStraightMem_straightOps_store`
    induction verbatim; the array terminal is the trivial base case. -/
theorem lsemStraightMemArr_straightOps_store {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ArrMemN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateM} {V : Ctxt.Valuation Γ},
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesM nArgs curDepth st V →
      ∃ st', lsemStraightMem (straightOpsMem nArgs com curDepth) st = some st' ∧
        StoreAgreesM nArgs (curDepth + comLen com) st' (comDenoteLets com V) ∧
        WriteFrame curDepth st st' := by
  induction hcom with
  | retArr v =>
      intro nArgs curDepth st V _ _ hagree
      exact ⟨st, rfl, hagree, WriteFrame.refl curDepth st⟩
  | var bop heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_var (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) bop heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_var, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_const (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) n (by rcases hwn with h | h <;> omega) heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_const, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | sel heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_sel (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_sel, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | shr hm heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_shr (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_shr, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | shl hm heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_shl (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_shl, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | sar hm heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_sar (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_sar, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | mulhi heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_mulhi (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.mulhi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_mulhi, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | addLo heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_addLo (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.addCarryLo _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_addLo, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | addHi heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_addHi (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.addCarryHi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_addHi, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | cast heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_cast (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.castW _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_cast, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | load heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_load (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.stackLoad _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_load, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg
  | store heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_store (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) heq args hagree
      have hagree' := StoreAgreesM.stepArr
        ((⟨JasminOp.stackStore _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepArr _ hFr⟩
      · rw [straightOpsMem_store, lsemStraightMem_cons, hstep]; exact hrun
      · exact arr_shift_depth hAg

/-! ## 3. Reading the returned array off the final agreement -/

/-- The array return slot of a `.ret v` at an array variable is the resolved
    variable name. -/
theorem comRetReg_ret_arr {Γ : Ctxt jasminDialect} {w n : Nat}
    (v : Ctxt.Var Γ (.stackArr w n)) (nArgs curDepth : Nat) :
    comRetReg nArgs argName (Com.ret v) curDepth
      = operandName (resolveVar curDepth nArgs argName (fun _ => none) v) := by
  rw [show comRetReg nArgs argName (Com.ret v) curDepth
      = (match resolveVar curDepth nArgs argName (fun _ => none) v with
        | .reg r => r
        | .arr b i => b ++ "[" ++ toString i ++ "]"
        | .imm k => toString k
        | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]") from rfl]
  rw [resolveVar_isReg v]
  rfl

/-- **Read the returned array off the final agreement (return-type-general).**
    From an agreement with the binding-extended valuation `comDenoteLets com V`
    at the final depth, the return slot `comRetReg` reads (via
    `decodeArrM`/`getArr` at shape `(w, n)`) the chain's denotation. The `.var`
    case is uniform in the binding op (it advances one depth and rebinds the
    valuation); the return type is carried as an equation `ht` so the induction
    ranges over a variable index. -/
theorem denoteLets_getArr_comRetReg_gen {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) :
    ∀ {w n : Nat} (ht : t = .stackArr w n) {nArgs curDepth : Nat} {st : LstateM}
      (V : Ctxt.Valuation Γ),
      StoreAgreesM nArgs (curDepth + comLen com) st (comDenoteLets com V) →
      decodeArrM st (comRetReg nArgs argName com curDepth) w n
        = some (ht ▸ com.denote V : ⟦(JasminTy.stackArr w n)⟧) := by
  induction com with
  | ret v =>
      intro w n ht nArgs curDepth st V h
      subst ht
      show st.getArr (comRetReg nArgs argName (Com.ret v) curDepth) w n = some (v.lookup V)
      rw [comRetReg_ret_arr v nArgs curDepth]
      exact h.arr v
  | var e body ih =>
      intro w n ht nArgs curDepth st V h
      subst ht
      have h' : StoreAgreesM nArgs ((curDepth + 1) + comLen body) st
          (comDenoteLets body (V.extend (e.denote V))) := by
        rw [show (curDepth + 1) + comLen body = curDepth + comLen (Com.var e body) from by
          simp only [comLen]; omega]
        exact h
      exact ih (w := w) (n := n) rfl (V.extend (e.denote V)) h'

/-- **Read the returned array off the final agreement.** The array-terminal
    instance of `denoteLets_getArr_comRetReg_gen`. -/
theorem denoteLets_getArr_comRetReg {Γ : Ctxt jasminDialect} {w n : Nat}
    (com : Com jasminDialect Γ (.stackArr w n))
    {nArgs curDepth : Nat} {st : LstateM} (V : Ctxt.Valuation Γ)
    (h : StoreAgreesM nArgs (curDepth + comLen com) st (comDenoteLets com V)) :
    decodeArrM st (comRetReg nArgs argName com curDepth) w n = some (com.denote V) :=
  denoteLets_getArr_comRetReg_gen com rfl V h

/-! ## 4. The composed array-return simulation -/

/-- **Array-return straight-line simulation (array-terminal form of
    `comToLprog_lsemMem`).** Running the stack-memory-fragment `.var`-chain
    `straightOpsMem` of an array-returning `ArrMemN` update from the encoded
    argument valuation, the result array lands at the return slot `comRetReg`,
    `decodeArrM`-readable at shape `(w, n)`, equal to the source program's
    `Com.denote`. -/
theorem comToLprog_lsemMemArr {Γ : Ctxt jasminDialect} {w n : Nat}
    {com : Com jasminDialect Γ (.stackArr w n)} (hcom : ArrMemN com)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightMem (straightOpsMem Γ.length com Γ.length) (encodeM V) = some st' ∧
      decodeArrM st' (comRetReg Γ.length argName com Γ.length) w n = some (com.denote V) := by
  obtain ⟨st', hrun, hAg, _hFr⟩ :=
    lsemStraightMemArr_straightOps_store hcom (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeM V) (V := V) rfl le_rfl (encodeM_StoreAgreesM V)
  exact ⟨st', hrun, denoteLets_getArr_comRetReg com V hAg⟩

/-- **Faithfulness (packaged), array-returning chain.** -/
theorem comToLprog_faithful_memArr {Γ : Ctxt jasminDialect} {w n : Nat}
    {com : Com jasminDialect Γ (.stackArr w n)} (hcom : ArrMemN com)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightMem (straightOpsMem Γ.length com Γ.length) (encodeM V)).bind
        (fun st' => decodeArrM st' (comRetReg Γ.length argName com Γ.length) w n) =
      some (com.denote V) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemMemArr hcom V
  rw [hrun, Option.bind_some, hdec]

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrReturn
