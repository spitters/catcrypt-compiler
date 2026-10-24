/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArr

/-!
# `Com ↔ Jasmin` bridge extension: the register-index `Pget` read

`JasminPrint.lowerExpr` lowers `stackLoad w n` to
`Cassgn (Lvar dst) _ (sword w) (Pget AAscale w arr (Pvar idx))` with a `reg 64`
index register `idx`; the JasminPrint evaluator reads the cell
`stackGet arr (idx.toNat)`. The `psem.v` mirror reads an array index through
`Value.toInt`, which accepts only an `int`; Jasmin's type checker makes the
word-to-int conversion explicit as `Oint_of_word`. The mirror form of the
emitted read is therefore

```
Pget al aa U8 arr (Papp1 (Oint_of_word Unsigned U64) (Pvar idx))
```

## The index correspondence

`IntOfWordAgrees opS` states that `opS` converts a `u64` word to the
non-negative integer of its unsigned value. `withIntOfWord opS` is `opS` with
that one unary operator set accordingly, and `withIntOfWord_agrees` proves the
predicate for it. Under this predicate, a register index holding `Vword U64 i`
evaluates to `Vint i.toNat` (`semPexpr_idxExpr`), and under `StateCorrReg` the
JasminPrint store holds the same `i` at `idx`.

## Contents

* `idxExpr`, `IntOfWordAgrees`, `withIntOfWord`, `withIntOfWord_agrees`.
* `semPexpr_idxExpr` — the mirror index evaluation.
* `semPexpr_pget_reg` / `pget_reg_read_corr` — the mirror cell read at an
  in-range register index, and the agreeing JasminPrint `stackGet` read.
* `cassgn_pget_reg_selfContained` / `cassgn_pget_reg_endToEnd` — the per-step
  bridge for `dst := arr[idx]` with the RHS derived, and its `SemIr` step.
* `stackSet_eq_setByte`, `mirror_laset_post` — the `stackStore` write
  `Laset al aa U8 arr (idxExpr idx) := src`: at an in-range index the JasminPrint
  `stackSet` is the mirror `setByte`, and the mirror run writes the updated array.
* `stateCorrArr_write` / `stateCorrReg_write_arr` — the paired array write extends
  `StateCorrArr` by `arr` and preserves a register frame distinct from `arr`.
* `store_stackSet_corr` — the `stackStore` value computed from the store is the
  mirror's updated array.
* `cassgn_laset_simulates` / `cassgn_laset_endToEnd` — the per-step `Laset` bridge
  and its `SemIr` step.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrIdx

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArr

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The index conversion -/

/-- The mirror index expression for a `u64` index register: `int_of_word` of the
    register read. -/
def idxExpr (idx : VarI) : Pexpr := .Papp1 (.Oint_of_word .Unsigned .U64) (.Pvar (mkLvar idx))

/-- `opS` converts a `u64` word to the integer of its unsigned value. -/
def IntOfWordAgrees (opS : OpSem) : Prop :=
  ∀ w : BitVec WSize.U64.bits,
    opS.sem_sop1 (.Oint_of_word .Unsigned .U64) (.Vword .U64 w) = .ok (.Vint (w.toNat : Int))

/-- `opS` with the unsigned `u64` `int_of_word` conversion set to the unsigned
    value; every other operator is unchanged. -/
def withIntOfWord (opS : OpSem) : OpSem where
  sem_sop1 := fun o v =>
    match o, v with
    | .Oint_of_word .Unsigned .U64, .Vword .U64 w => .ok (.Vint (w.toNat : Int))
    | o, v => opS.sem_sop1 o v
  sem_sop2 := opS.sem_sop2
  sem_opN := opS.sem_opN

/-- `withIntOfWord opS` satisfies `IntOfWordAgrees`. -/
theorem withIntOfWord_agrees (opS : OpSem) : IntOfWordAgrees (withIntOfWord opS) :=
  fun _ => rfl

/-- The mirror evaluates the index expression of a register holding `Vword U64 i`
    to `Vint i.toNat`. -/
theorem semPexpr_idxExpr
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem)
    (idx : VarI) (i : BitVec WSize.U64.bits)
    (hagree : IntOfWordAgrees opS)
    (hread : (s.evm).get idx.v_var = .Vword .U64 i) :
    semPexpr (Mem := Mem) true gd opS s (idxExpr idx) = .ok (.Vint (i.toNat : Int)) := by
  show (do
      let v1 ← semPexpr (Mem := Mem) true gd opS s (.Pvar (mkLvar idx))
      opS.sem_sop1 (.Oint_of_word .Unsigned .U64) v1) = _
  rw [semPexpr_pvar_vword gd opS s idx .U64 i hread]
  exact hagree i

/-! ## §2. The register-index cell read -/

/-- The mirror `semPexpr` of `Pget al aa U8 x (idxExpr idx)`, when `x` reads
    `Varr n a` and `idx` reads `Vword U64 i` with `i.toNat < n`, is the cell byte
    `Vword U8 (a ⟨i.toNat, hin⟩)`. -/
theorem semPexpr_pget_reg
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem)
    (x idx : VarI) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (i : BitVec WSize.U64.bits)
    (hagree : IntOfWordAgrees opS)
    (hread : (s.evm).get x.v_var = .Varr n a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hin : i.toNat < n) :
    semPexpr (Mem := Mem) true gd opS s (.Pget al aa .U8 (mkLvar x) (idxExpr idx))
      = .ok (.Vword .U8 (a ⟨i.toNat, hin⟩)) := by
  have hgv : getGvar true gd s.evm (mkLvar x) = .ok (.Varr n a) := by
    unfold getGvar
    rw [show (mkLvar x).isLvar = true from rfl]
    simp only [ite_true]
    show getVar true s.evm (mkLvar x).gv.v_var = _
    unfold getVar
    rw [show (mkLvar x).gv.v_var = x.v_var from rfl, hread]
    rfl
  show (do
      let vr ← getGvar true gd s.evm (mkLvar x)
      match vr with
      | .Varr n a =>
          let vi ← semPexpr (Mem := Mem) true gd opS s (idxExpr idx)
          let i ← vi.toInt
          if h : 0 ≤ i ∧ i.toNat < n then
            .ok (Value.Vword .U8 (a ⟨i.toNat, h.2⟩))
          else .typeError
      | _ => .typeError) = _
  rw [hgv]
  show (do
      let vi ← semPexpr (Mem := Mem) true gd opS s (idxExpr idx)
      let i ← vi.toInt
      if h : 0 ≤ i ∧ i.toNat < n then
        .ok (Value.Vword .U8 (a ⟨i.toNat, h.2⟩))
      else .typeError) = _
  rw [semPexpr_idxExpr gd opS s idx i hagree hidx]
  show (if h : 0 ≤ (i.toNat : Int) ∧ (i.toNat : Int).toNat < n then
        (.ok (Value.Vword .U8 (a ⟨(i.toNat : Int).toNat, h.2⟩)) : JResult Value)
      else .typeError) = _
  rw [dite_eq_left ⟨Int.natCast_nonneg _, by simpa using hin⟩]
  simp

/-- **Register-index `Pget`-read correspondence.** Under `StateCorrArr` for the
    array `x` and `StateCorrReg` for the index register `idx`, with `x` reading
    `Varr n a` and `idx` reading `Vword U64 i` in range:

    * the mirror `Pget` evaluates to the cell byte `a ⟨i.toNat, hin⟩`; and
    * the JasminPrint read `stackGet (Store.get st x.vname (stackArr 8 n))
      (Store.get st idx.vname (reg 64)).toNat` — the `stackLoad` arm of
      `JasminPrintSemCorrect.execExpr` — is the same byte. -/
theorem pget_reg_read_corr
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem) (st : Store)
    (arrNames regNames : List Var) (x idx : VarI) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (i : BitVec WSize.U64.bits)
    (hagree : IntOfWordAgrees opS)
    (harr : StateCorrArr arrNames st (s.evm)) (hxm : x.v_var ∈ arrNames)
    (hreg : StateCorrReg regNames st (s.evm)) (him : idx.v_var ∈ regNames)
    (hread : (s.evm).get x.v_var = .Varr n a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hin : i.toNat < n) :
    semPexpr (Mem := Mem) true gd opS s (.Pget al aa .U8 (mkLvar x) (idxExpr idx))
      = .ok (.Vword .U8 (a ⟨i.toNat, hin⟩))
    ∧ stackGet (Store.get st x.v_var.vname (.stackArr 8 n))
        (BitVec.toNat (Store.get st idx.v_var.vname (.reg 64)))
        = a ⟨i.toNat, hin⟩ := by
  refine ⟨semPexpr_pget_reg gd opS s x idx n a al aa i hagree hread hidx hin, ?_⟩
  obtain ⟨_, hst⟩ :=
    arr_read_corr (SyscallState := SyscallState) gd s st arrNames x n a harr hxm hread
  have hi : Store.get st idx.v_var.vname (.reg WSize.U64.bits) = i :=
    (pvar_read_corr (Mem := Mem) gd opS s st regNames idx .U64 i hreg him hidx).2
  have hi' : Store.get st idx.v_var.vname (.reg 64) = i := hi
  rw [hst, hi']
  exact stackGet_id a ⟨i.toNat, hin⟩

/-! ## §3. The per-step bridge -/

/-- **Self-contained per-step register-index `Pget` bridge.** For
    `dst := arr[idx]` (byte destination register, `arr` holding `Varr n a`, `idx`
    a `u64` register holding an in-range index), the mirror `Cassgn` run lands
    `s.withVm (s.evm.set dst (Vword U8 (a ⟨i.toNat, hin⟩)))`, and the post-state
    corresponds (`StateCorrReg (dst :: names)`) to
    `Store.set st dst.vname (a ⟨i.toNat, hin⟩)`. The RHS byte is derived from the
    mirror reads; `cassgn_pget_reg_endToEnd` adds the agreeing store read. -/
theorem cassgn_pget_reg_selfContained
    (gd : GlobDecls) (opS : OpSem) (tag : AssgnTag)
    (dst arr idx : VarI) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (i : BitVec WSize.U64.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hagree : IntOfWordAgrees opS)
    (hdst : dst.v_var.vtype = .aword .U8)
    (hread : (s.evm).get arr.v_var = .Varr n a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hin : i.toNat < n)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Lvar dst) (.aword .U8)
        (.Pget al aa .U8 (mkLvar arr) (idxExpr idx)) s
      = .ok (s.withVm ((s.evm).set dst.v_var (.Vword .U8 (a ⟨i.toNat, hin⟩))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg 8) (a ⟨i.toNat, hin⟩))
        ((s.evm).set dst.v_var (.Vword .U8 (a ⟨i.toNat, hin⟩))) := by
  have hrhs := semPexpr_pget_reg gd opS s arr idx n a al aa i hagree hread hidx hin
  exact cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
    gd opS dst .U8 tag (.Pget al aa .U8 (mkLvar arr) (idxExpr idx))
    (a ⟨i.toNat, hin⟩) s st names hdst hrhs hdistinct hcorr

/-- **End-to-end per-step register-index `Pget` bridge.** Under the hypotheses of
    `cassgn_pget_reg_selfContained`, the `Cassgn` witnesses the relational step
    `SemIr` to `s.withVm (s.evm.set dst (Vword U8 (a ⟨i.toNat, hin⟩)))`, the
    post-state corresponds to `Store.set st dst.vname (a ⟨i.toNat, hin⟩)`, and the
    JasminPrint `stackLoad` read of `arr` at the store's `idx` is that byte. -/
theorem cassgn_pget_reg_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat)
    (dst arr idx : VarI) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (i : BitVec WSize.U64.bits) (tag : AssgnTag)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hagree : IntOfWordAgrees opS)
    (hdst : dst.v_var.vtype = .aword .U8)
    (hread : (s.evm).get arr.v_var = .Varr n a)
    (harr : StateCorrArr [arr.v_var] st (s.evm))
    (him : idx.v_var ∈ names)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hin : i.toNat < n)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    SemIr (Mem := Mem) aS opS gd prog s
        (.Cassgn (.Lvar dst) tag (.aword .U8) (.Pget al aa .U8 (mkLvar arr) (idxExpr idx)))
        (s.withVm ((s.evm).set dst.v_var (.Vword .U8 (a ⟨i.toNat, hin⟩))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg 8) (a ⟨i.toNat, hin⟩))
        ((s.evm).set dst.v_var (.Vword .U8 (a ⟨i.toNat, hin⟩)))
    ∧ stackGet (Store.get st arr.v_var.vname (.stackArr 8 n))
        (BitVec.toNat (Store.get st idx.v_var.vname (.reg 64))) = a ⟨i.toNat, hin⟩ := by
  have hrhs := semPexpr_pget_reg gd opS s arr idx n a al aa i hagree hread hidx hin
  obtain ⟨hsem, hcorr'⟩ := cassgn_regArith_endToEnd (SyscallState := SyscallState) (Mem := Mem)
    aS opS gd prog dst .U8 tag (.Pget al aa .U8 (mkLvar arr) (idxExpr idx))
    (a ⟨i.toNat, hin⟩) s st names fuel hdst hrhs hdistinct hcorr
  exact ⟨hsem, hcorr',
    (pget_reg_read_corr gd opS s st [arr.v_var] names arr idx n a al aa i hagree
      harr (by simp) hcorr him hread hidx hin).2⟩

/-! ## §4. The `Laset` array-cell write

`JasminPrint.lowerExpr` lowers `stackStore w n` to the in-place update
`Cassgn (Laset AAscale w arr (Pvar idx)) AT_none (sword w) (Pvar src)`: the result
array keeps the source array's name, and the JasminPrint evaluator stores
`stackSet arr idx.toNat src` there. The mirror form over byte arrays is
`Cassgn (Laset al aa U8 arr (idxExpr idx)) tag (aword U8) (Pvar src)`. -/

/-- At an in-range index, the JasminPrint `stackSet` is the mirror `setByte`. -/
theorem stackSet_eq_setByte {n : Nat} (a : JArrayMirror n) (k : Nat) (hk : k < n)
    (v : BitVec 8) :
    (stackSet (w := 8) a k v : JArrayMirror n) = JArrayMirror.setByte a ⟨k, hk⟩ v := by
  cases n with
  | zero => omega
  | succ m =>
    funext j
    simp [stackSet, JArrayMirror.setByte, Nat.mod_eq_of_lt hk]

/-- **Mirror `Laset` post-state.** For `arr[idx] := src` with `arr : aarr ws n`
    reading `Varr n a`, `idx` a `u64` register holding `i` with `i.toNat < n`, and
    `src` holding `Vword U8 v`, the mirror assignment writes
    `Varr n (setByte a ⟨i.toNat, hin⟩ v)` into `arr`. -/
theorem mirror_laset_post
    (gd : GlobDecls) (opS : OpSem)
    (arr idx src : VarI) (ws : WSize) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (i : BitVec WSize.U64.bits) (v : BitVec WSize.U8.bits)
    (s : Estate SyscallState Mem)
    (hagree : IntOfWordAgrees opS)
    (harrTy : arr.v_var.vtype = .aarr ws n)
    (hread : (s.evm).get arr.v_var = .Varr n a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hsrc : (s.evm).get src.v_var = .Vword .U8 v)
    (hin : i.toNat < n) :
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Laset al aa .U8 arr (idxExpr idx))
        (.aword .U8) (.Pvar (mkLvar src)) s
      = .ok (s.withVm ((s.evm).set arr.v_var
          (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v)))) := by
  unfold OpSemCoverage.assignExec
  rw [semPexpr_pvar_vword gd opS s src .U8 v hsrc]
  show (do
      let v' ← truncateVal (.cword .U8) (.Vword .U8 v)
      writeLval (Mem := Mem) true gd opS (.Laset al aa .U8 arr (idxExpr idx)) v' s) = _
  rw [truncateVal_aword_self]
  show writeLval (Mem := Mem) true gd opS (.Laset al aa .U8 arr (idxExpr idx)) (.Vword .U8 v) s = _
  have hgv : getVar true s.evm arr.v_var = .ok (.Varr n a) := by
    unfold getVar; rw [hread]; rfl
  have hw : Value.toWord .U8 (.Vword .U8 v) = .ok v := by
    show truncateWord .U8 (sz' := .U8) v = _
    unfold truncateWord
    simp only [le_refl, ite_true]
    congr 1
    apply BitVec.eq_of_toNat_eq; simp
  show (do
      let valR ← getVar true s.evm arr.v_var
      match valR with
      | .Varr n a =>
          let iV ← semPexpr (Mem := Mem) true gd opS s (idxExpr idx)
          let i ← iV.toInt
          let wv ← Value.toWord .U8 (.Vword .U8 v)
          if h : 0 ≤ i ∧ i.toNat < n then
            let a' := JArrayMirror.setByte a ⟨i.toNat, h.2⟩ wv
            writeVar (Mem := Mem) true arr (.Varr n a') s
          else .typeError
      | _ => .typeError) = _
  rw [hgv]
  show (do
      let iV ← semPexpr (Mem := Mem) true gd opS s (idxExpr idx)
      let i ← iV.toInt
      let wv ← Value.toWord .U8 (.Vword .U8 v)
      if h : 0 ≤ i ∧ i.toNat < n then
        writeVar (Mem := Mem) true arr (.Varr n (JArrayMirror.setByte a ⟨i.toNat, h.2⟩ wv)) s
      else .typeError) = _
  rw [semPexpr_idxExpr gd opS s idx i hagree hidx]
  show (do
      let wv ← Value.toWord .U8 (.Vword .U8 v)
      if h : 0 ≤ (i.toNat : Int) ∧ (i.toNat : Int).toNat < n then
        writeVar (Mem := Mem) true arr
          (.Varr n (JArrayMirror.setByte a ⟨(i.toNat : Int).toNat, h.2⟩ wv)) s
      else .typeError) = _
  rw [hw]
  show (if h : 0 ≤ (i.toNat : Int) ∧ (i.toNat : Int).toNat < n then
        writeVar (Mem := Mem) true arr
          (.Varr n (JArrayMirror.setByte a ⟨(i.toNat : Int).toNat, h.2⟩ v)) s
      else .typeError) = _
  rw [dite_eq_left ⟨Int.natCast_nonneg _, by simpa using hin⟩]
  unfold writeVar setVar
  rw [harrTy]
  simp [DB, Value.isDefined, truncatable, Value.typeOf]

/-- **Array-write preservation.** Writing `arr := Varr n a'` on the mirror and
    the byte function `a'` at `arr.vname` in the store extends `StateCorrArr` to
    `arr :: names`, for a frame of variables distinct from `arr` with names
    distinct from `arr.vname`. -/
theorem stateCorrArr_write (arr : Var) (n : Nat) (a' : JArrayMirror n)
    (st : Store) (vm : Vm) (names : List Var)
    (hdistinct : ∀ r ∈ names, r ≠ arr ∧ r.vname ≠ arr.vname)
    (hcorr : StateCorrArr names st vm) :
    StateCorrArr (arr :: names)
      (Store.set st arr.vname (t := .stackArr 8 n) a')
      (vm.set arr (.Varr n a')) := by
  intro r hr
  rcases List.mem_cons.mp hr with h | h
  · subst h
    show Store.set st r.vname (t := .stackArr 8 n) a' r.vname = encodeArrVal ((vm.set r (.Varr n a')).get r)
    simp [Store.set, encodeArrVal, Vm.get, Vm.set]
  · obtain ⟨hne, hname⟩ := hdistinct r h
    show Store.set st arr.vname (t := .stackArr 8 n) a' r.vname
      = encodeArrVal ((vm.set arr (.Varr n a')).get r)
    have hm : (vm.set arr (.Varr n a')).get r = vm.get r := by simp [Vm.get, Vm.set, hne]
    have hs : Store.set st arr.vname (t := .stackArr 8 n) a' r.vname = st r.vname := by
      simp [Store.set, hname]
    rw [hm, hs]
    exact hcorr r h

/-- **Register frame across an array write.** The paired array write at `arr`
    leaves `StateCorrReg` on a register frame distinct from `arr` unchanged. -/
theorem stateCorrReg_write_arr (arr : Var) (n : Nat) (a' : JArrayMirror n)
    (st : Store) (vm : Vm) (names : List Var)
    (hdistinct : ∀ r ∈ names, r ≠ arr ∧ r.vname ≠ arr.vname)
    (hcorr : StateCorrReg names st vm) :
    StateCorrReg names
      (Store.set st arr.vname (t := .stackArr 8 n) a')
      (vm.set arr (.Varr n a')) := by
  intro r h
  obtain ⟨hne, hname⟩ := hdistinct r h
  show Store.set st arr.vname (t := .stackArr 8 n) a' r.vname
    = encodeRegVal ((vm.set arr (.Varr n a')).get r)
  have hm : (vm.set arr (.Varr n a')).get r = vm.get r := by simp [Vm.get, Vm.set, hne]
  have hs : Store.set st arr.vname (t := .stackArr 8 n) a' r.vname = st r.vname := by
    simp [Store.set, hname]
  rw [hm, hs]
  exact hcorr r h

/-- **The JasminPrint `stackStore` value.** Under `StateCorrArr` for `arr` and
    `StateCorrReg` for the index and source registers, the value the `stackStore`
    arm of `JasminPrintSemCorrect.execExpr` computes from the store,
    `stackSet arr (idx.toNat) src`, is the mirror's updated array
    `setByte a ⟨i.toNat, hin⟩ v`. -/
theorem store_stackSet_corr
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem) (st : Store)
    (arrNames regNames : List Var) (arr idx src : VarI) (n : Nat) (a : JArrayMirror n)
    (i : BitVec WSize.U64.bits) (v : BitVec WSize.U8.bits)
    (harr : StateCorrArr arrNames st (s.evm)) (ham : arr.v_var ∈ arrNames)
    (hreg : StateCorrReg regNames st (s.evm))
    (him : idx.v_var ∈ regNames) (hsm : src.v_var ∈ regNames)
    (hread : (s.evm).get arr.v_var = .Varr n a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hsrc : (s.evm).get src.v_var = .Vword .U8 v)
    (hin : i.toNat < n) :
    stackSet (Store.get st arr.v_var.vname (.stackArr 8 n))
        (BitVec.toNat (Store.get st idx.v_var.vname (.reg 64)))
        (Store.get st src.v_var.vname (.reg 8))
      = JArrayMirror.setByte a ⟨i.toNat, hin⟩ v := by
  obtain ⟨_, hst⟩ :=
    arr_read_corr (SyscallState := SyscallState) gd s st arrNames arr n a harr ham hread
  have hi : Store.get st idx.v_var.vname (.reg 64) = i :=
    (pvar_read_corr (Mem := Mem) gd opS s st regNames idx .U64 i hreg him hidx).2
  have hv : Store.get st src.v_var.vname (.reg 8) = v :=
    (pvar_read_corr (Mem := Mem) gd opS s st regNames src .U8 v hreg hsm hsrc).2
  rw [hst, hi, hv]
  exact stackSet_eq_setByte a i.toNat hin v

/-- **Simulation (paired step) for the `Laset` write.** For
    `arr[idx] := src` with the hypotheses of `mirror_laset_post`, `arr`
    corresponding on `StateCorrArr arrNames`, `idx`, `src` in the register frame
    `regNames`, and both frames distinct from `arr` (the array frame except for
    `arr` itself):

    * the mirror run writes `Varr n a'` with `a' = setByte a ⟨i.toNat, hin⟩ v`;
    * the JasminPrint `stackStore` value computed from the store is `a'`;
    * the post-states satisfy `StateCorrArr (arr :: arrNames)` and
      `StateCorrReg regNames` for `Store.set st arr.vname a'`. -/
theorem cassgn_laset_simulates
    (gd : GlobDecls) (opS : OpSem)
    (arr idx src : VarI) (ws : WSize) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (i : BitVec WSize.U64.bits) (v : BitVec WSize.U8.bits)
    (s : Estate SyscallState Mem) (st : Store) (arrNames regNames : List Var)
    (hagree : IntOfWordAgrees opS)
    (harrTy : arr.v_var.vtype = .aarr ws n)
    (hread : (s.evm).get arr.v_var = .Varr n a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hsrc : (s.evm).get src.v_var = .Vword .U8 v)
    (hin : i.toNat < n)
    (harr : StateCorrArr (arr.v_var :: arrNames) st (s.evm))
    (hreg : StateCorrReg regNames st (s.evm))
    (him : idx.v_var ∈ regNames) (hsm : src.v_var ∈ regNames)
    (hdA : ∀ r ∈ arrNames, r ≠ arr.v_var ∧ r.vname ≠ arr.v_var.vname)
    (hdR : ∀ r ∈ regNames, r ≠ arr.v_var ∧ r.vname ≠ arr.v_var.vname) :
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Laset al aa .U8 arr (idxExpr idx))
        (.aword .U8) (.Pvar (mkLvar src)) s
      = .ok (s.withVm ((s.evm).set arr.v_var
          (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))))
    ∧ stackSet (Store.get st arr.v_var.vname (.stackArr 8 n))
        (BitVec.toNat (Store.get st idx.v_var.vname (.reg 64)))
        (Store.get st src.v_var.vname (.reg 8))
      = JArrayMirror.setByte a ⟨i.toNat, hin⟩ v
    ∧ StateCorrArr (arr.v_var :: arrNames)
        (Store.set st arr.v_var.vname (t := .stackArr 8 n) (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))
        ((s.evm).set arr.v_var (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v)))
    ∧ StateCorrReg regNames
        (Store.set st arr.v_var.vname (t := .stackArr 8 n) (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))
        ((s.evm).set arr.v_var (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))) := by
  have hframe : StateCorrArr arrNames st (s.evm) := fun r hr => harr r (List.mem_cons_of_mem _ hr)
  exact ⟨mirror_laset_post gd opS arr idx src ws n a al aa i v s hagree harrTy hread hidx hsrc hin,
    store_stackSet_corr gd opS s st (arr.v_var :: arrNames) regNames arr idx src n a i v
      harr List.mem_cons_self hreg him hsm hread hidx hsrc hin,
    stateCorrArr_write arr.v_var n _ st s.evm arrNames hdA hframe,
    stateCorrReg_write_arr arr.v_var n _ st s.evm regNames hdR hreg⟩

/-- **End-to-end bridge for the `Laset` write.** Under the hypotheses of
    `cassgn_laset_simulates`, the emitted `Cassgn` witnesses the relational step
    `SemIr` to the written state, and both correspondences hold after the paired
    write. -/
theorem cassgn_laset_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat) (tag : AssgnTag)
    (arr idx src : VarI) (ws : WSize) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (i : BitVec WSize.U64.bits) (v : BitVec WSize.U8.bits)
    (s : Estate SyscallState Mem) (st : Store) (arrNames regNames : List Var)
    (hagree : IntOfWordAgrees opS)
    (harrTy : arr.v_var.vtype = .aarr ws n)
    (hread : (s.evm).get arr.v_var = .Varr n a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hsrc : (s.evm).get src.v_var = .Vword .U8 v)
    (hin : i.toNat < n)
    (harr : StateCorrArr (arr.v_var :: arrNames) st (s.evm))
    (hreg : StateCorrReg regNames st (s.evm))
    (him : idx.v_var ∈ regNames) (hsm : src.v_var ∈ regNames)
    (hdA : ∀ r ∈ arrNames, r ≠ arr.v_var ∧ r.vname ≠ arr.v_var.vname)
    (hdR : ∀ r ∈ regNames, r ≠ arr.v_var ∧ r.vname ≠ arr.v_var.vname) :
    SemIr (Mem := Mem) aS opS gd prog s
        (.Cassgn (.Laset al aa .U8 arr (idxExpr idx)) tag (.aword .U8) (.Pvar (mkLvar src)))
        (s.withVm ((s.evm).set arr.v_var (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))))
    ∧ StateCorrArr (arr.v_var :: arrNames)
        (Store.set st arr.v_var.vname (t := .stackArr 8 n) (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))
        ((s.evm).set arr.v_var (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v)))
    ∧ StateCorrReg regNames
        (Store.set st arr.v_var.vname (t := .stackArr 8 n) (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))
        ((s.evm).set arr.v_var (.Varr n (JArrayMirror.setByte a ⟨i.toNat, hin⟩ v))) := by
  obtain ⟨hrun, _, hA, hR⟩ :=
    cassgn_laset_simulates gd opS arr idx src ws n a al aa i v s st arrNames regNames
      hagree harrTy hread hidx hsrc hin harr hreg him hsm hdA hdR
  refine ⟨?_, hA, hR⟩
  apply ExecAdequacy.execInstrR_sound (n := fuel + 1) aS opS gd prog
  rw [OpSemCoverage.execInstrR_Cassgn_eq]
  exact hrun

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrIdx
