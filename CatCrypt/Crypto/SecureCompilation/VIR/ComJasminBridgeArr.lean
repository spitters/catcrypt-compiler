/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeExt2

/-!
# `Com ↔ Jasmin` bridge extension: the `Pget` array-cell read shape

`ComJasminBridgeExt` / `ComJasminBridgeExt2` close the register-word RHS shapes
(`castW`, `signext`, truncation). The remaining emit shape catalogued as a
residual is `Pget` — the `stackLoad` array read: `Pget aa ws x idx` reads a
`.Varr n a` from the source slot and returns the byte `a ⟨i, …⟩` at a constant
index.

`StateBijection.encodeRegVal` maps every non-`Vword` value — including an array
`.Varr n a` — to `DynVal.default (.reg 0)`, discarding the byte function. So
`StateCorrReg`/`RegCorr` carries no array-cell correspondence and a `Pget` read
is unrecoverable under it. This file adds, **without editing `StateBijection`**,
a parallel array-slot correspondence and closes the constant-index `Pget`.

## The array-slot correspondence

A mirror array value is `.Varr n a` with `a : JArrayMirror n = Fin n → BitVec 8`
(byte function). The JasminPrint side stores an array at
`⟦.stackArr 8 n⟧ = Fin n → BitVec 8` — the *same* byte function. So the array
encoding is the identity on the byte function once the length tag matches, just
as `RegCorr` is near-identity on the reg word. `encodeArrVal` maps
`.Varr n a ↦ ⟨.stackArr 8 n, a⟩`, and `ArrCorr d v := d = encodeArrVal v` is the
value-level array correspondence; `StateCorrArr` lifts it to a frame.

## What is proved (all sorry-free)

* `encodeArrVal` / `ArrCorr` / `StateCorrArr` — the additive array-slot
  correspondence (parallel to `RegCorr`/`StateCorrReg`, no edit to
  `StateBijection`).
* `store_get_stackArr` — the JasminPrint `Store.get` at a `stackArr` name returns
  the stored byte function.
* `arr_read_corr` — the array-slot read correspondence: under `StateCorrArr`, the
  mirror `getGvar` of a corresponding array variable is `.ok (.Varr n a)` and the
  JasminPrint `Store.get st x.vname (.stackArr 8 n)` is the *same* `a`.
* `semPexpr_pget_const` — the mirror `semPexpr` of `Pget aa ws x (Pconst k)` at a
  constant in-range index: `.ok (.Vword .U8 (a ⟨k.toNat, hkn⟩))`.
* `pget_read_corr` — the **`Pget`-read correspondence** (const index, the array
  analogue of `OperandReadCorr.papp2_read_corr` / `papp1_zeroext_read_corr`):
  under `StateCorrArr`, the mirror `Pget` evaluates to the cell byte
  `a ⟨k.toNat, hkn⟩`, and the JasminPrint `stackGet (Store.get …) k.toNat` is the
  *same* byte.
* `cassgn_pget_selfContained` — the self-contained per-step `Pget` bridge:
  `dst := arr[k]` (byte destination), the RHS cell byte *derived* from the array
  slot, threaded through `ComJasminBridgeFull.cassgn_regArith_simulates`.
* `cassgn_pget_endToEnd` — adds `SemIr` adequacy via
  `ComJasminBridgeFull.cassgn_regArith_endToEnd`.
* `ArrExample.selfContained_getExample` — the worked `x := arr[2]` example, RHS
  byte derived from the `Store` array slot.

## Scope

This closes the **constant-index** `Pget aa ws x (Pconst k)`. The mirror `Pget`
returns a byte (`.Vword .U8`), so the destination is a byte register and the
correspondence is byte-granular, matching the mirror's array model. The
**variable-index** shape `Pget aa ws x (Pvar idx)` — the `stackLoad` emit's
register index — is a separate residual: the mirror reads the index via
`Value.toInt`, which succeeds only on a `.Vint` (an `int`-typed index), so a
register (`.Vword`) index needs an index-value correspondence
(`.Vword ↦ .Vint`) not present here.

0 sorries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArr

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The array-slot correspondence

A mirror array `.Varr n a` (`a : JArrayMirror n = Fin n → BitVec 8`) encodes to
the JasminPrint `DynVal ⟨.stackArr 8 n, a⟩` (`⟦.stackArr 8 n⟧ = Fin n → BitVec 8`
carries the *same* byte function). This is the array analogue of
`StateBijection.encodeRegVal`. -/

/-- Encode a mirror array `Value` to a JasminPrint `DynVal`. A `Varr n a` becomes
    the stack-array `DynVal` `⟨.stackArr 8 n, a⟩` carrying the same byte function.
    Non-array values are out-of-(array-)fragment, mapped to the default. -/
def encodeArrVal : Value → DynVal
  | .Varr n a => ⟨.stackArr 8 n, a⟩
  | _         => DynVal.default (.reg 0)

/-- The array-fragment value correspondence: a JasminPrint `DynVal` `d` and a
    mirror `Value` `v` correspond iff `d` is exactly the array encoding of `v`. -/
def ArrCorr (d : DynVal) (v : Value) : Prop := d = encodeArrVal v

/-- The encoding of a mirror array corresponds to it. -/
theorem arrCorr_encode (v : Value) : ArrCorr (encodeArrVal v) v := rfl

/-- On a mirror `Varr`, the correspondence determines the `DynVal` exactly. -/
theorem arrCorr_varr (n : Nat) (a : JArrayMirror n) :
    ArrCorr (⟨.stackArr 8 n, a⟩ : DynVal) (.Varr n a) := rfl

/-- `StateCorrArr names s vm`: for every array variable `r` in `names`, the
    `Store` value at `r.vname` corresponds to the mirror `Vm` value at `r`. The
    array-slot analogue of `StateBijection.StateCorrReg`. -/
def StateCorrArr (names : List Var) (s : Store) (vm : Vm) : Prop :=
  ∀ r ∈ names, ArrCorr (s r.vname) (vm.get r)

/-! ## §2. The array-slot read correspondence

The JasminPrint `Store.get st name (.stackArr 8 n)` on a slot holding
`⟨.stackArr 8 n, a⟩` returns the byte function `a`. Under `StateCorrArr`, a mirror
array variable reading `.Varr n a` therefore has its `Store` slot holding exactly
`a`, so the two array reads agree. -/

/-- The JasminPrint `Store` reads the byte function it holds at a `stackArr`-typed
    name. `Store.get` at the *declared* array type returns the stored value. -/
theorem store_get_stackArr (st : Store) (name : String) (n : Nat)
    (a : JArrayMirror n)
    (hst : st name = (⟨.stackArr 8 n, a⟩ : DynVal)) :
    Store.get st name (.stackArr 8 n) = a := by
  unfold Store.get
  rw [hst]
  simp
  rfl

omit [MemModel Mem] in
/-- **Array-slot read correspondence.** Under `StateCorrArr names st vm`, an array
    variable `x ∈ names` whose mirror slot holds `Varr n a`:

    * the mirror `getGvar` of the local `x` is `.ok (.Varr n a)`; and
    * the JasminPrint `Store.get st x.vname (.stackArr 8 n)` is the *same* `a`. -/
theorem arr_read_corr
    (gd : GlobDecls) (s : Estate SyscallState Mem) (st : Store)
    (names : List Var) (x : VarI) (n : Nat) (a : JArrayMirror n)
    (hcorr : StateCorrArr names st (s.evm))
    (hmem : x.v_var ∈ names)
    (hread : (s.evm).get x.v_var = .Varr n a) :
    getGvar true gd s.evm (mkLvar x) = .ok (.Varr n a)
    ∧ Store.get st x.v_var.vname (.stackArr 8 n) = a := by
  refine ⟨?_, ?_⟩
  · unfold getGvar
    rw [show (mkLvar x).isLvar = true from rfl]
    simp only [if_true]
    show getVar true s.evm (mkLvar x).gv.v_var = _
    unfold getVar
    rw [show (mkLvar x).gv.v_var = x.v_var from rfl, hread]
    rfl
  · have hac : ArrCorr (st x.v_var.vname) ((s.evm).get x.v_var) := hcorr x.v_var hmem
    unfold ArrCorr at hac
    rw [hread] at hac
    exact store_get_stackArr st x.v_var.vname n a hac

/-! ## §3. The mirror `Pget` at a constant index

`semPexpr` of `Pget aa ws x (Pconst k)` reads the array via `getGvar`, evaluates
the index `Pconst k` to `.Vint k`, converts to `k` (`Value.toInt`), and — when
`0 ≤ k` and `k.toNat < n` — returns the cell byte `.Vword .U8 (a ⟨k.toNat, …⟩)`. -/

/-- The mirror `semPexpr` of `Pget al aa U8 x (Pconst k)`, when `x` reads
    `Varr n a` and `k` is an in-range constant index, is
    `.ok (.Vword .U8 (a ⟨k.toNat, hkn⟩))` — the array cell byte. -/
theorem semPexpr_pget_const
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem)
    (x : VarI) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (k : Int)
    (hread : (s.evm).get x.v_var = .Varr n a)
    (hk0 : 0 ≤ k) (hkn : k.toNat < n) :
    semPexpr (Mem := Mem) true gd opS s (.Pget al aa .U8 (mkLvar x) (.Pconst k))
      = .ok (.Vword .U8 (a ⟨k.toNat, hkn⟩)) := by
  show (do
      let vr ← getGvar true gd s.evm (mkLvar x)
      match vr with
      | .Varr n a =>
          let vi ← semPexpr (Mem := Mem) true gd opS s (.Pconst k)
          let i ← vi.toInt
          if h : 0 ≤ i ∧ i.toNat < n then
            .ok (Value.Vword .U8 (a ⟨i.toNat, h.2⟩))
          else .typeError
      | _ => .typeError) = _
  rw [show getGvar true gd s.evm (mkLvar x)
        = .ok (.Varr n a) from by
    unfold getGvar
    rw [show (mkLvar x).isLvar = true from rfl]
    simp only [if_true]
    show getVar true s.evm (mkLvar x).gv.v_var = _
    unfold getVar
    rw [show (mkLvar x).gv.v_var = x.v_var from rfl, hread]
    rfl]
  show (do
      let vi ← semPexpr (Mem := Mem) true gd opS s (.Pconst k)
      let i ← vi.toInt
      if h : 0 ≤ i ∧ i.toNat < n then
        .ok (Value.Vword .U8 (a ⟨i.toNat, h.2⟩))
      else .typeError) = _
  show (do
      let i ← Value.toInt (.Vint k)
      if h : 0 ≤ i ∧ i.toNat < n then
        .ok (Value.Vword .U8 (a ⟨i.toNat, h.2⟩))
      else .typeError) = _
  show (if h : 0 ≤ k ∧ k.toNat < n then
        (.ok (Value.Vword .U8 (a ⟨k.toNat, h.2⟩)) : JResult Value)
      else .typeError) = _
  rw [dif_pos ⟨hk0, hkn⟩]

/-- **`Pget`-read correspondence (const index).** Under `StateCorrArr names st vm`,
    for an array variable `x ∈ names` reading `Varr n a` and an in-range constant
    index `k`:

    * the mirror `semPexpr` of `Pget al aa U8 x (Pconst k)` is
      `.ok (.Vword .U8 (a ⟨k.toNat, hkn⟩))` — the cell byte; and
    * the JasminPrint `stackGet (Store.get st x.vname (.stackArr 8 n)) k.toNat` is
      the *same* byte `a ⟨k.toNat, hkn⟩`.

    The cell byte is *computed from the corresponding array slot*, not supplied.
    The array analogue of `OperandReadCorr.papp2_read_corr`. -/
theorem pget_read_corr
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem) (st : Store)
    (names : List Var) (x : VarI) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (k : Int)
    (hcorr : StateCorrArr names st (s.evm))
    (hmem : x.v_var ∈ names)
    (hread : (s.evm).get x.v_var = .Varr n a)
    (hk0 : 0 ≤ k) (hkn : k.toNat < n) :
    semPexpr (Mem := Mem) true gd opS s (.Pget al aa .U8 (mkLvar x) (.Pconst k))
      = .ok (.Vword .U8 (a ⟨k.toNat, hkn⟩))
    ∧ stackGet (Store.get st x.v_var.vname (.stackArr 8 n)) k.toNat
        = a ⟨k.toNat, hkn⟩ := by
  refine ⟨semPexpr_pget_const gd opS s x n a al aa k hread hk0 hkn, ?_⟩
  obtain ⟨_, hst⟩ := arr_read_corr (SyscallState := SyscallState) gd s st names x n a hcorr hmem hread
  rw [hst]
  exact stackGet_id a ⟨k.toNat, hkn⟩

/-! ## §4. The self-contained per-step `Pget` bridge

`ComJasminBridgeFull.cassgn_regArith_simulates` is generic in the RHS expression
`e` and its value `w`. We *derive* `hrhs` for the `Pget` shape (the cell byte)
from `pget_read_corr` and feed it through: the destination is a byte register
(`aword .U8`) and the produced value is the array cell byte. -/

/-- **Self-contained per-step `Pget` bridge (RHS derived).** For `dst := arr[k]`
    (byte destination register, `arr` an array variable, `k` an in-range constant
    index), given:

    * `dst` is a register of width `.U8`, frame-distinct from `names`;
    * the array slot `arr` holds `Varr n a` and corresponds
      (`StateCorrArr [arr.v_var]`);
    * the register frame corresponds (`StateCorrReg names`),

    the mirror `Cassgn` run lands `s.withVm (s.evm.set dst (.Vword .U8 (a ⟨k, …⟩)))`,
    and the post-state corresponds (`StateCorrReg (dst :: names)`) to the
    JasminPrint `Store.set st dst (a ⟨k, …⟩)` — the same cell byte the
    `stackLoad` read produces. The RHS value is derived, not assumed. -/
theorem cassgn_pget_selfContained
    (gd : GlobDecls) (opS : OpSem) (tag : AssgnTag)
    (dst arr : VarI) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (k : Int)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hdst : dst.v_var.vtype = .aword .U8)
    (hread : (s.evm).get arr.v_var = .Varr n a)
    (harr : StateCorrArr [arr.v_var] st (s.evm))
    (hk0 : 0 ≤ k) (hkn : k.toNat < n)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Lvar dst) (.aword .U8)
        (.Pget al aa .U8 (mkLvar arr) (.Pconst k)) s
      = .ok (s.withVm ((s.evm).set dst.v_var (.Vword .U8 (a ⟨k.toNat, hkn⟩))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg 8) (a ⟨k.toNat, hkn⟩))
        ((s.evm).set dst.v_var (.Vword .U8 (a ⟨k.toNat, hkn⟩))) := by
  obtain ⟨hrhs, _⟩ :=
    pget_read_corr (SyscallState := SyscallState) gd opS s st [arr.v_var] arr n a
      al aa k harr (by simp) hread hk0 hkn
  exact cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
    gd opS dst .U8 tag (.Pget al aa .U8 (mkLvar arr) (.Pconst k))
    (a ⟨k.toNat, hkn⟩) s st names hdst hrhs hdistinct hcorr

/-! ## §5. The end-to-end `Pget` bridge (adequacy)

Chaining `ComJasminBridgeFull.cassgn_regArith_endToEnd`: the mirror run of the
`Pget` `Cassgn` *witnesses* the reference `psem.v` relational step `SemIr`, and
the post-state corresponds. -/

/-- **End-to-end per-step `Pget` bridge.** For the `Pget` `Cassgn`
    `dst := arr[k]` (const index), at fuel `fuel+1`, the mirror run witnesses the
    reference relational step `SemIr` landing
    `s.withVm (s.evm.set dst (.Vword .U8 (a ⟨k, …⟩)))`, and the post-state
    corresponds (`StateCorrReg`) to the JasminPrint `Store.set st dst (a ⟨k, …⟩)`.
    The RHS cell byte is derived via `pget_read_corr`. -/
theorem cassgn_pget_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (dst arr : VarI) (n : Nat) (a : JArrayMirror n)
    (al : Aligned) (aa : ArrAccess) (k : Int) (tag : AssgnTag)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var) (fuel : Nat)
    (hdst : dst.v_var.vtype = .aword .U8)
    (hread : (s.evm).get arr.v_var = .Varr n a)
    (harr : StateCorrArr [arr.v_var] st (s.evm))
    (hk0 : 0 ≤ k) (hkn : k.toNat < n)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    SemIr (Mem := Mem) aS opS gd prog s
        (.Cassgn (.Lvar dst) tag (.aword .U8)
          (.Pget al aa .U8 (mkLvar arr) (.Pconst k)))
        (s.withVm ((s.evm).set dst.v_var (.Vword .U8 (a ⟨k.toNat, hkn⟩))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg 8) (a ⟨k.toNat, hkn⟩))
        ((s.evm).set dst.v_var (.Vword .U8 (a ⟨k.toNat, hkn⟩))) := by
  obtain ⟨hrhs, _⟩ :=
    pget_read_corr (SyscallState := SyscallState) gd opS s st [arr.v_var] arr n a
      al aa k harr (by simp) hread hk0 hkn
  exact cassgn_regArith_endToEnd (SyscallState := SyscallState) (Mem := Mem)
    aS opS gd prog dst .U8 tag (.Pget al aa .U8 (mkLvar arr) (.Pconst k))
    (a ⟨k.toNat, hkn⟩) s st names fuel hdst hrhs hdistinct hcorr

/-! ## §6. Worked example: `x := arr[2]` (byte read at a constant index)

The array read `x := arr[2]` (`arr : stackArr 8 4` holding bytes `[10,11,12,13]`,
`x : reg u8`), with the RHS cell byte *computed from the `Store` array slot*
(`arr` read from a corresponding array variable). From `arr[2] = 12` the loaded
byte is `12 : BitVec 8`. -/

namespace ArrExample

/-- A 4-byte array `[10, 11, 12, 13]`. -/
def arrData : JArrayMirror 4 := fun i =>
  match i with
  | ⟨0, _⟩ => (10 : BitVec 8)
  | ⟨1, _⟩ => (11 : BitVec 8)
  | ⟨2, _⟩ => (12 : BitVec 8)
  | ⟨3, _⟩ => (13 : BitVec 8)

/-- `x : reg u8` (the loaded-byte destination). -/
def xVar : VarI := { v_var := { vname := "x", vtype := .aword .U8 } }
/-- `arr : the array source, an `aarr` variable of 4 bytes. -/
def arrVar : VarI := { v_var := { vname := "arr", vtype := .aarr .U8 4 } }

/-- A start `Estate` holding `arr = Varr 4 arrData`. -/
def startState : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  { escs := (), emem := (),
    evm := Vm.set Vm.init arrVar.v_var (.Varr 4 arrData) }

theorem startState_arr :
    (startState.evm).get arrVar.v_var = .Varr 4 arrData := by
  show (Vm.set Vm.init arrVar.v_var (.Varr 4 arrData)).get arrVar.v_var = _
  simp [Vm.get, Vm.set]

/-- The `Store` slot holding `arr = ⟨.stackArr 8 4, arrData⟩`. -/
def startStore : Store :=
  Store.set (fun _ => DynVal.default (.reg 0)) arrVar.v_var.vname
    (t := .stackArr 8 4) arrData

theorem startStore_corr : StateCorrArr [arrVar.v_var] startStore (startState.evm) := by
  intro r hr
  rcases List.mem_singleton.mp hr with h
  subst h
  show ArrCorr (startStore arrVar.v_var.vname) ((startState.evm).get arrVar.v_var)
  rw [startState_arr]
  show startStore arrVar.v_var.vname = (⟨.stackArr 8 4, arrData⟩ : DynVal)
  unfold startStore Store.set
  simp

/-- **The loaded byte `arr[2]` is DERIVED (not supplied).** Given the initial
    `StateCorrArr [arr]`, the `Pget` RHS `Pget AAscale U8 arr (Pconst 2)`
    *evaluates to* `.ok (.Vword U8 12)` — `arr`'s cell 2 read from the `Store`
    array slot. -/
theorem rhs_derived :
    semPexpr (Mem := OpSemCoverage.AssignExample.TrivialMem) true []
        (addOpSemReg .U8) startState
        (.Pget .IsAligned .AAscale .U8 (mkLvar arrVar) (.Pconst 2))
      = .ok (.Vword .U8 (12 : BitVec 8))
    ∧ stackGet (Store.get startStore arrVar.v_var.vname (.stackArr 8 4)) 2
        = (12 : BitVec 8) := by
  obtain ⟨heval, hget⟩ :=
    pget_read_corr (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] (addOpSemReg .U8) startState startStore [arrVar.v_var] arrVar 4
      arrData .IsAligned .AAscale 2 startStore_corr (by simp) startState_arr
      (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · rw [heval]; rfl
  · show stackGet (Store.get startStore arrVar.v_var.vname (.stackArr 8 4))
        ((2 : Int).toNat) = _
    rw [hget]; rfl

/-- **Worked self-contained `x := arr[2]` step.** From `StateCorrArr [arr]` with
    `arr[2] = 12`, the `Pget` `Cassgn` `x := arr[2]` mirror-runs to
    `x = Vword U8 12` — the cell byte **derived** from the `Store` array slot
    (`pget_read_corr`), not supplied; and the post-state corresponds
    (`StateCorrReg [x]`) to the JasminPrint `Store.set st "x" (12 : BitVec 8)`. -/
theorem selfContained_getExample :
    OpSemCoverage.assignExec
        (Mem := OpSemCoverage.AssignExample.TrivialMem)
        (addOpSemReg .U8) []
        (.Lvar xVar) (.aword .U8)
        (.Pget .IsAligned .AAscale .U8 (mkLvar arrVar) (.Pconst 2)) startState
      = .ok (startState.withVm ((startState.evm).set xVar.v_var
          (.Vword .U8 (12 : BitVec 8))))
    ∧ StateCorrReg [xVar.v_var]
        (Store.set startStore xVar.v_var.vname (t := .reg 8) (12 : BitVec 8))
        ((startState.evm).set xVar.v_var (.Vword .U8 (12 : BitVec 8))) := by
  have hcell : arrData ⟨(2 : Int).toNat, by decide⟩ = (12 : BitVec 8) := by decide
  rw [← hcell]
  exact
    cassgn_pget_selfContained (SyscallState := Unit)
      (Mem := OpSemCoverage.AssignExample.TrivialMem)
      [] (addOpSemReg .U8) .AT_none xVar arrVar 4 arrData
      .IsAligned .AAscale 2 startState startStore []
      (by rfl) startState_arr startStore_corr (by decide) (by decide)
      (by intro r' hr'; exact absurd hr' (List.not_mem_nil))
      (stateCorrReg_nil startStore (startState.evm))

end ArrExample

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArr
