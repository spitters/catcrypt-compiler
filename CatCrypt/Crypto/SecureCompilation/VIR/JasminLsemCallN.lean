/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.String.Defs
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf

/-!
# Faithful `lsem` for the multi-result external-call `callN`
# — increment 10 of porting jasmin's `lsem`

Increment 9 (`JasminLsemLeaf.lean`) brought the **single-result** opaque external
leaf `extCall name [.reg w] (.reg w')` into the unconditional functional ∧
constant-time `lsem` simulation, carrying the leaf-agreement hypothesis
`LeafAgreesN`. It deferred the **multi-result external call** `callN` as "needs
multiple destination registers".

This module **adds the `callN` arm**. The decisive structural finding — established
by reading the dialect (`JasminDialect.lean`) and the emit path
(`JasminLprogExport.lean`) — is:

> **Inside the `Com`/`Expr` framework that the whole `lsem` simulation lives over,
> `callN` is a SINGLE-result op, NOT multi-slot.**

Concretely:

* `DialectSignature.ret (callN name argTys retTys) = callNRet retTys =
  retTys.headD (.reg 0)` — a SINGLE `JasminTy`, the *head* result slot. An `Expr`
  in this framework has exactly one return type, so the multi-result tuple has
  nowhere to land at the `Com`/`opToLinstrR`/`straightOps*` layer.
* `jasminDenote.denote (callN _ _ retTys) = fun _ => JasminTy.default
  (callNRet retTys)` — a SINGLE value (the opaque default of the head result
  type), independent of the arguments.
* `opToLinstrR (callN name _ _) dst srcs = .Lopn [.reg dst] ("CALLN:" ++ name)
  srcs` — emits exactly **one** destination slot `[.reg dst]`, the same wire shape
  as `extCall`'s `"CALL:"` modulo the disjoint `"CALLN:"` prefix.

The `k`-output tuple (`callNDefaults`) is consumed **only** by the
`func.call` lowering, a *different* lowering path than
`opToLinstrR`/`comToBody`. The straight-line linearizer
(`straightOpsMC`/`straightOps*`) and `comToBody` only ever emit the single head
slot for `callN`. So the simulation never sees a multi-destination `callN`: at
the layer it models, `callN` is precisely an `extCall`-shaped opaque leaf on its
head register result. (This is the documented "single-head projection it exposes is
an `extCall`-shaped opaque leaf" remark from increment 9, now discharged as a
first-class arm rather than left in spirit.)

## The multi-result store-agreement question, answered

The task asked: does a faithful `callN` step need a multi-slot store-agreement?
**No — not at this layer.** A multi-slot store-agreement would be needed for the
`func.call` lowering (the path that writes `k` destinations). But `comToBody` /
the linearizer never invoke that path: an `Expr`'s single `ret` forces the head
projection, and `opToLinstrR` emits one `.reg dst`. The single fresh
`regName curDepth` per binding that `StoreAgreesN` models is therefore *exactly*
the right shape for the `callN` head — no widening of `StoreAgreesN` is needed,
and inventing a multi-slot one here would be modelling a wire the linearizer does
not emit. (Should the `func.call` lowering ever be brought under an `lsem`
simulation, that is where a multi-destination store-agreement belongs; it is a
separate lowering, out of scope of the straight-line linearizer this proves.)

## What the op emits, and the fidelity route

We scope the `callN` arm to the **single register argument, register head-result**
shape `callN name [.reg w] retTys` with `callNRet retTys = .reg w'` — the form a
scalar straight-line kernel emits. As in increment 9 we thread typed instructions
`LinstrRT = LinstrR × Option Nat`: the `LinstrR` component is *exactly*
`straightOpsLeaf`'s emitted instruction — its `.fst`-projection equals
`straightOpsMC` (the wire/byte tie `straightOpsCallN_wire`) — and the descriptor
slot carries `some w'` on a `callN` binding (the head result width `w'`, read from
the binding's typing; never a wire annotation, so the bytes are unchanged). The
emitted mnemonic is the **real** bare `"CALLN:" ++ name` from `opToLinstrR`; we
invent no mnemonic and do not touch the emit path.

## The carried agreement (documented, external)

The lsem step writes a **leaf function** `leaf name w w'`, drawn from a carried
leaf environment. The simulation carries

    LeafAgreesCN leaf  :  ∀ name w w' retTys (va : BitVec w),
        callNRet retTys = .reg w' →
        (leaf name w w' va : BitVec w') =
          (jasminDenote.denote (callN name [.reg w] retTys) ⟨va⟩ : ⟦callNRet retTys⟧)
            (cast to .reg w')

i.e. the lsem step's leaf = the `Com` `callN`'s *head* denotation. The dialect
models that head as the opaque default, so for a generic `callN` this RHS is
`(0 : BitVec w')`; a real multi-result intrinsic supplies its own `leaf` and
discharges `LeafAgreesCN` from its KAT, exactly as `LeafAgreesN` /
`latticeLeafAgrees`. Nothing here *proves* the external call correct — its
correctness is its own KAT, stated as `LeafAgreesCN`.

## Leakage (constant-time): the ABI, never values

The leak of `Lopn [.reg dst] ("CALLN:" ++ name) [.reg a]` is, by `linstrLeak`,
the single event over the opcode (`"CALLN:" ++ name` = the call name) plus the
destination/argument register **names** (the ABI structure), and **no register
value**. Identical CT behaviour to the `extCall` leaf — automatic, since the
wire is an `Lopn` and `lsemLeakLeaf` leaks `linstrLeak i.fst`.

**All goals closed, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`, no emit-path edit.** The `lsem→bytes` encoder and Sail
tables remain the declared trusted base, as for every verified compiler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCallN

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf

/-! ## 1. The opaque multi-result-call leaf environment and the carried agreement -/

/-- An **opaque multi-result-call leaf environment**: for a leaf `name` and the
    single-register-arg / register-head-result shape `[.reg w] → .reg w'`, the
    leaf is a function `BitVec w → BitVec w'`. Same shape as increment 9's
    `LeafEnvN`; the value supplied is the call's *head* result. -/
abbrev LeafEnvCN : Type := (name : String) → (w w' : Nat) → BitVec w → BitVec w'

/-- **The carried multi-result-call agreement (documented, external).** The lsem
    step's leaf `leaf name w w'` equals the `Com` `callN`'s **head** denotation —
    the opaque default of the head result type — on every single-register
    argument, for any `retTys` whose head is `.reg w'`. This is the multi-result
    analogue of `LeafAgreesN`: its truth is the leaf's own KAT. (For a generic
    `callN` the dialect head denotation is `JasminTy.default (.reg w') =
    (0 : BitVec w')`; a real intrinsic supplies a `leaf` and discharges this from
    its KAT.) -/
def LeafAgreesCN (leaf : LeafEnvCN) : Prop :=
  ∀ (name : String) (w w' : Nat) (va : BitVec w),
    (leaf name w w' va : BitVec w') = (0 : BitVec w')

/-! ## 2. Recognising the `CALLN:` wire and the typed step -/

/-- Recognise a structured multi-result-call (`callN`) head instruction and return
    `(dst, name, a)`; `none` otherwise. `opToLinstrR` lowers a register-head `callN`
    to one of two width-dependent head shadow mnemonics:

    * an **all-GP** call (`callHasWide false`) keeps the plain `"CALLN:" ++ name`
      shadow — strip the `"CALLN:"` prefix to recover `name`;
    * a call with an **SSE-class** (`> 64`) head result or argument emits the
      widened `"CALLNW:" ++ <retW> ++ ";" ++ <argWs> ++ ";" ++ name` shadow
      (`encodeCallW`) — strip the `"CALLNW:"` prefix and the two `;`-free numeric
      header fields (`dropSemiField` twice) to recover `name`.

    The head prefixes `"CALLN:"`/`"CALLNW:"` are disjoint from increment 9's
    single-result `"CALL:"`/`"CALLW:"` (index 4 is `'N'` vs `':'`/`'W'`), so a
    `callN` head is never mistaken for an `extCall` wire and vice versa. -/
def callNStruct? : LinstrR → Option (String × String × String)
  | .Lopn [.reg dst] opn [.reg a] =>
      let ns := opn.toList
      if "CALLNW:".toList.isPrefixOf ns then
        some (dst,
          String.ofList (JasminLsemLeaf.dropSemiField
            (JasminLsemLeaf.dropSemiField (ns.drop "CALLNW:".toList.length))), a)
      else if "CALLN:".toList.isPrefixOf ns then
        some (dst, String.ofList (ns.drop "CALLN:".toList.length), a)
      else none
  | _ => none

/-- The typed single-step semantics for the multi-result-call fragment,
    parametrised by a leaf environment `leaf`. On a `callN`-tagged instruction
    (`callNStruct?` recognises the `"CALLN:name"` wire form *and* the descriptor
    `some w'` is present) it reads the source `a` at its store width `w`, and
    writes the leaf result `leaf name w w' (va)` (with `w'` the head-result width,
    carried in the typed `.snd` descriptor) to `dst` — faithful to `eval_instr`'s
    external `Oasm` `Lopn`, the leaf the external multi-result call's head. On
    every other typed instruction it delegates to increment 9's `lsemStepLeaf`. -/
def lsemStepCallN (leaf : LeafEnvCN) (i : LinstrRT) (s : LstateN) :
    Option LstateN :=
  match callNStruct? i.fst, i.snd with
  | some (dst, name, a), some w' =>
      match readReg s (.reg a) with
      | some ⟨w, va⟩ => some ((s.setReg dst (leaf name w w' va)).nextPc)
      | none => none
  | _, _ => lsemStepLeaf leaf i s

/-- `opToLinstrR` on a register-head `callN` produces the bare `"CALLN:name"`
    wire, which `callNStruct?` recognises with the source register recovered. -/
theorem callNStruct?_callN {w : Nat} {retTys : List JasminTy} (name dst a : String) :
    callNStruct? (opToLinstrR (JasminOp.callN name [.reg w] retTys) dst [.reg a])
      = some (dst, name, a) := by
  simp only [opToLinstrR]
  split
  · -- SSE-class widths: the widened `CALLNW:<retW>;<argWs>;name` head shadow.
    have hm : encodeCallW "CALLNW:" name (callMarshalWidth (retTys.headD (.reg 0)))
        (List.map callMarshalWidth [.reg w])
        = "CALLNW:" ++ toString (callMarshalWidth (retTys.headD (.reg 0))) ++ ";"
            ++ toString w ++ ";" ++ name := rfl
    rw [hm]
    have hpfx : "CALLNW:".toList.isPrefixOf
        ("CALLNW:" ++ toString (callMarshalWidth (retTys.headD (.reg 0))) ++ ";"
          ++ toString w ++ ";" ++ name).toList = true := by
      simp [List.isPrefixOf, String.toList_append]
    simp only [callNStruct?, hpfx, if_true,
      JasminLsemLeaf.callw_extract _ _ _ _
        (JasminLsemLeaf.semi_notMem_toString _) (JasminLsemLeaf.semi_notMem_toString w),
      String.ofList_toList]
  · -- all-GP widths: the plain `CALLN:name` head shadow.
    simp only [callNStruct?]
    rw [String.toList_append]
    simp [List.isPrefixOf, String.ofList_toList]

/-- A `"CALLN:"` wire is NOT a `"CALL:"` wire: the increment-9 single-result
    recogniser `callStruct?` returns `none` on the `callN` head. (Index 4 is
    `'N'` in `"CALLN:"` but `':'` in `"CALL:"`.) -/
theorem callStruct?_callN {w : Nat} {retTys : List JasminTy} (name dst a : String) :
    JasminLsemLeaf.callStruct? (opToLinstrR (JasminOp.callN name [.reg w] retTys) dst [.reg a])
      = none := by
  simp only [opToLinstrR]
  split <;> simp [JasminLsemLeaf.callStruct?, List.isPrefixOf, String.toList_append, encodeCallW]

/-- On any instruction that is not a `CALLN:` wire (or has no descriptor),
    `lsemStepCallN` delegates to increment 9's `lsemStepLeaf`. -/
theorem lsemStepCallN_of_delegate (leaf : LeafEnvCN) (i : LinstrRT) (s : LstateN)
    (h : callNStruct? i.fst = none ∨ i.snd = none) :
    lsemStepCallN leaf i s = lsemStepLeaf leaf i s := by
  rcases h with h | h
  · simp only [lsemStepCallN, h]
  · simp only [lsemStepCallN, h]; cases callNStruct? i.fst <;> rfl

/-! ### `lsemStraightCallN` / leakage over the typed step -/

/-- Typed straight-line execution: the sequential fold of `lsemStepCallN`. -/
def lsemStraightCallN (leaf : LeafEnvCN) : List LinstrRT → LstateN → Option LstateN
  | [], s => some s
  | i :: is, s =>
      match lsemStepCallN leaf i s with
      | some s' => lsemStraightCallN leaf is s'
      | none => none

@[simp] theorem lsemStraightCallN_nil (leaf : LeafEnvCN) (s : LstateN) :
    lsemStraightCallN leaf [] s = some s := rfl

@[simp] theorem lsemStraightCallN_cons (leaf : LeafEnvCN) (i : LinstrRT)
    (is : List LinstrRT) (s : LstateN) :
    lsemStraightCallN leaf (i :: is) s =
      (match lsemStepCallN leaf i s with
        | some s' => lsemStraightCallN leaf is s'
        | none => none) := rfl

/-- Typed leakage trace: the leak of each typed instruction is the leak of its
    **wire** (`linstrLeak i.fst`), so neither the descriptor `w'` nor any leaf
    value enters the attacker's view. For a `callN` wire `Lopn [.reg dst]
    ("CALLN:" ++ name) [.reg a]`, `linstrLeak` yields the call name plus the
    destination/argument register **names** (the ABI), never a value. -/
def lsemLeakCallN (leaf : LeafEnvCN) : List LinstrRT → LstateN → List JasminLsemRobust.LLeak
  | [], _ => []
  | i :: is, s =>
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepCallN leaf i s with
          | some s' => lsemLeakCallN leaf is s'
          | none => [])

@[simp] theorem lsemLeakCallN_nil (leaf : LeafEnvCN) (s : LstateN) :
    lsemLeakCallN leaf [] s = [] := rfl

@[simp] theorem lsemLeakCallN_cons (leaf : LeafEnvCN) (i : LinstrRT)
    (is : List LinstrRT) (s : LstateN) :
    lsemLeakCallN leaf (i :: is) s =
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepCallN leaf i s with
          | some s' => lsemLeakCallN leaf is s'
          | none => []) := rfl

/-! ## 3. The typed emission `straightOpsCallN` and the wire/byte tie -/

/-- The typed straight-line `LinstrRT` chain a `Com` emits in the multi-result-call
    fragment. A register-head `callN name [.reg w] retTys` binding (with
    `callNRet retTys = .reg w'`) emits its **real**
    `opToLinstrR (callN name [.reg w] retTys)` instruction (bare `"CALLN:name"`)
    paired with the descriptor `some w'`; every other binding reuses increment 9's
    `straightOpsLeaf` emission verbatim. -/
def straightOpsCallN (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrRT
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let elem : LinstrRT :=
        match e.op with
        | .callN _ _ retTys => (opToLinstrR e.op (regName curDepth) src, some (tyWidth (callNRet retTys)))
        | .extCall _ _ (.reg w') => (opToLinstrR e.op (regName curDepth) src, some w')
        | .castW _ w' => (opToLinstrR e.op (regName curDepth) src, some w')
        | _ =>
          let wire : LinstrR :=
            match e.op, src with
            | .shrImm w n, [s] => shiftLinstr "SHR" w (regName curDepth) s n
            | .shlImm w n, [s] => shiftLinstr "SHL" w (regName curDepth) s n
            | .sarImm w n, [s] => shiftLinstr "SAR" w (regName curDepth) s n
            | _, _ => opToLinstrR e.op (regName curDepth) src
          (wire, none)
      elem :: straightOpsCallN nArgs body (curDepth + 1)

/-- **The wire/byte tie.** The `.fst`-projection (the emitted bytes) of the typed
    chain `straightOpsCallN` is *exactly* `straightOpsMC` — the descriptors `w'`
    (callN / cast / leaf) live only in the `.snd` component. So `straightOpsCallN`
    emits the same bytes as `straightOpsMC`, which is `comToBody`'s body; the
    `callN`'s wire is the REAL bare `"CALLN:name"` `opToLinstrR` output. -/
theorem straightOpsCallN_wire (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsCallN nArgs com curDepth).map Prod.fst =
      straightOpsMC nArgs com curDepth := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      simp only [straightOpsCallN, straightOpsMC, List.map_cons, ih]
      congr 1
      cases hop : e.op <;> (try rfl)
      · rename_i name argTys retTy
        cases retTy <;> rfl

/-- The `.fst`-projection of `straightOpsCallN` also equals `straightOpsLeaf`'s
    (both project to `straightOpsMC`) — so the multi-result-call chain emits the
    same bytes as the increment-9 leaf chain. -/
theorem straightOpsCallN_wire_leaf (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsCallN nArgs com curDepth).map Prod.fst =
      (straightOpsLeaf nArgs com curDepth).map Prod.fst := by
  rw [straightOpsCallN_wire, straightOpsLeaf_wire]

/-! ### `straightOpsCallN` unfolding on the `callN` and delegated heads -/

theorem straightOpsCallN_callN {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat} {retTys : List JasminTy} (name : String)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.callN name [.reg w] retTys) = callNRet retTys)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.callN name [.reg w] retTys)))
    (body : Com jasminDialect (callNRet retTys :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.callN name [.reg w] retTys, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.callN name [.reg w] retTys) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.callN name [.reg w] retTys, heq, args⟩ :
            Expr jasminDialect Γ (callNRet retTys))), some (tyWidth (callNRet retTys)))
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCallN_ext {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w w' : Nat} (name : String)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
    (body : Com jasminDialect (.reg w' :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.extCall name [.reg w] (.reg w')) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
            Expr jasminDialect Γ (.reg w'))), some w')
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCallN_cast {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (body : Com jasminDialect (.reg w' :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.castW w w', heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.castW w w') (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))), some w')
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCallN_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.shrImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SHR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCallN_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.shlImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SHL" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCallN_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.sarImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SAR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCallN_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.regArith bop w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsCallN_const {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.regConst w n, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .nil => rfl

theorem straightOpsCallN_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.select w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.select w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsCallN_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.mulhi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsCallN_addLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsCallN_addHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (body : Com jasminDialect (.reg 1 :: Γ) s) :
    straightOpsCallN nArgs (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), none)
      :: straightOpsCallN nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-! ## 4. Per-binding agreement for `callN` and the delegated heads -/

/-- Transporting the opaque default of a type `t` along `t = .reg w'` yields the
    zero word `(0 : BitVec w')`. (The dialect models `callN`'s head as the opaque
    default; this lemma reads off that the transported head default is `0`.) -/
theorem default_cast_reg {t : JasminTy} {w' : Nat} (h : t = .reg w') :
    (h ▸ JasminTy.default t : ⟦(JasminTy.reg w')⟧) = (0 : BitVec w') := by
  cases h; rfl

/-- The `exprArgs` of a `callN` binding (single register argument) is its single
    resolved source. -/
theorem exprArgs_callN {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect} {w : Nat}
    {retTys : List JasminTy} (name : String)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.callN name [.reg w] retTys) = callNRet retTys)
    (a : Ctxt.Var Γ (.reg w)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.callN name [.reg w] retTys, heq, .cons a .nil⟩ :
        Expr jasminDialect Γ (callNRet retTys))
      = [resolveVar curDepth nArgs argName (fun _ => none) a] := rfl

/-- **`callN` per-binding step (opaque multi-result-call head), under the carried
    agreement.** From a store agreeing with `V`, the typed `callN` instruction
    `(opToLinstrR (callN name [.reg w] retTys) …, some w')` (with the head result
    `callNRet retTys = .reg w'`) `lsemStepCallN`s to the state writing the
    binding's denotation `(callN …).denote V` to `regName curDepth`, reading the
    source `a` at the recovered input width `w` and writing the leaf result at the
    head-result width `w'`. The denotation equality holds because the dialect
    head denotation of `callN` is the opaque default `(0 : BitVec w')`, which the
    carried `LeafAgreesCN` matches. Faithful to `eval_instr`'s external `Lopn`. -/
theorem lsemStepCallN_callN {leaf : LeafEnvCN} (hleaf : LeafAgreesCN leaf)
    {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w w' : Nat} {retTys : List JasminTy}
    (name : String) (hr : callNRet retTys = .reg w')
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.callN name [.reg w] retTys) = callNRet retTys)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.callN name [.reg w] retTys)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.callN name [.reg w] retTys) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.callN name [.reg w] retTys, heq, args⟩ :
              Expr jasminDialect Γ (callNRet retTys))), some w')
        st =
      some ((st.setReg (regName curDepth)
        (hr ▸ (⟨JasminOp.callN name [.reg w] retTys, heq, args⟩ :
          Expr jasminDialect Γ (callNRet retTys)).denote V : ⟦(JasminTy.reg w')⟧)).nextPc) := by
  match args with
  | .cons a .nil =>
    have ha : readReg st (.reg (operandName (resolveVar curDepth nArgs argName (fun _ => none) a)))
        = some ⟨w, a.lookup V⟩ := by
      have := readReg_resolveVar a hagree; rwa [resolveVar_isReg a] at this
    rw [exprArgs_callN name heq a, resolveVar_isReg a]
    simp only [lsemStepCallN, callNStruct?_callN name _ _, ha]
    congr 2
    -- the leaf value equals the `callN` head denotation (opaque default 0), by
    -- the carried agreement; the `callN` head denotation, transported to `.reg w'`,
    -- is also 0
    rw [hleaf name w w' (a.lookup V)]
    congr 1
    exact (default_cast_reg hr).symm

/-- The increment-9 `extCall` head delegates: its `"CALL:"` wire is not a
    `"CALLN:"` wire, so `lsemStepCallN` falls through to `lsemStepLeaf`, closed by
    increment 9's `lsemStepLeaf_ext` under the carried `LeafAgreesN`. -/
theorem lsemStepCallN_ext {leaf : LeafEnvCN}
    (hleafN : JasminLsemLeaf.LeafAgreesN leaf)
    {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w w' : Nat} (name : String)
    (hname : loadSymTarget? name = none)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.extCall name [.reg w] (.reg w')) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
              Expr jasminDialect Γ (.reg w'))), some w')
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
          Expr jasminDialect Γ (.reg w')).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inl ?_)]
  · exact JasminLsemLeaf.lsemStepLeaf_ext hleafN name hname heq args hagree
  · -- the extCall wire is a `"CALL:"` head, never a `"CALLN:"` head
    match args with
    | .cons a .nil =>
      rw [JasminLsemLeaf.exprArgs_extCall name heq a, resolveVar_isReg a]
      simp only [opToLinstrR, hname]
      split <;> simp [callNStruct?, List.isPrefixOf, String.toList_append, encodeCallW]

theorem lsemStepCallN_cast {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.castW w w') (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))), some w')
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w')).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inl ?_)]
  · exact lsemStepLeaf_cast heq args hagree
  · -- the cast wire is a `CASTW_*`, `ZEROEXT` or `TRUNC`, never a `CALLN:` head
    simp only [opToLinstrR]
    split
    all_goals
      simp only [callNStruct?, castWMnem]
      split <;> rename_i h <;> first | rfl |
        (injection h with _ ho _; subst ho; repeat' (first | rfl | split))

theorem lsemStepCallN_var {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_var bop heq args hagree

theorem lsemStepCallN_const {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (n : Nat) (hwn : w = 64 ∨ w = 32)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_const (V := V) n hwn heq args hagree

theorem lsemStepCallN_sel {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.select w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_sel heq args hagree

theorem lsemStepCallN_shr {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (shiftLinstr "SHR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_shr hn heq args hagree

theorem lsemStepCallN_shl {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (shiftLinstr "SHL" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_shl hn heq args hagree

theorem lsemStepCallN_sar {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (shiftLinstr "SAR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_sar hn heq args hagree

theorem lsemStepCallN_mulhi {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_mulhi heq args hagree

theorem lsemStepCallN_addLo {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_addLo heq args hagree

theorem lsemStepCallN_addHi {leaf : LeafEnvCN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCallN leaf
        (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1)).denote V)).nextPc) := by
  rw [lsemStepCallN_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepLeaf_addHi heq args hagree

/-! ## 5. The multi-result-call source fragment `ScalarCallN` -/

/-- The straight-line **multi-result-call-fragment** scalar source: every binding
    is one of increment 9's `ScalarLeafN` heads (`regArith`, `select`, an
    immediate shift, the widening-multiply / carry-chain trio, a `castW`, or a
    single-result `extCall`), **or** a register-head multi-result external call
    `callN name [.reg w] retTys` (single register argument, head result
    `callNRet retTys = .reg w'`). This subsumes increment 9's `ScalarLeafN`. -/
inductive ScalarCallN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
      ScalarCallN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | const {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (n : Nat)
      (hwn : w = 64 ∨ w = 32)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.regConst w n, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.select w, heq, args⟩ body)
  | shr {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.shrImm w n, heq, args⟩ body)
  | shl {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.shlImm w n, heq, args⟩ body)
  | sar {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.sarImm w n, heq, args⟩ body)
  | mulhi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.mulhi w, heq, args⟩ body)
  | addLo {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body)
  | addHi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
      {body : Com jasminDialect (.reg 1 :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body)
  | cast {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.castW w w', heq, args⟩ body)
  | ext {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat} (name : String)
      (hname : loadSymTarget? name = none)
      (heq : DialectSignature.ret (d := jasminDialect)
        (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ body)
  | callN {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat} {retTys : List JasminTy}
      (name : String) (hr : callNRet retTys = .reg w')
      (heq : DialectSignature.ret (d := jasminDialect)
        (JasminOp.callN name [.reg w] retTys) = callNRet retTys)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.callN name [.reg w] retTys)))
      {body : Com jasminDialect (callNRet retTys :: Γ) s}
      (hbody : ScalarCallN body) :
      ScalarCallN (.var ⟨JasminOp.callN name [.reg w] retTys, heq, args⟩ body)

/-- `ScalarCallN` subsumes `ScalarLeafN`: every increment-9 opaque-leaf-fragment
    program is in the multi-result-call fragment. So the increment-9 results are
    special cases. -/
theorem ScalarCallN.of_scalarLeafN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : ScalarLeafN com) : ScalarCallN com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq args _ ih => exact .var bop heq args ih
  | const n hwn heq args _ ih => exact .const n hwn heq args ih
  | sel heq args _ ih => exact .sel heq args ih
  | shr hn heq args _ ih => exact .shr hn heq args ih
  | shl hn heq args _ ih => exact .shl hn heq args ih
  | sar hn heq args _ ih => exact .sar hn heq args ih
  | mulhi heq args _ ih => exact .mulhi heq args ih
  | addLo heq args _ ih => exact .addLo heq args ih
  | addHi heq args _ ih => exact .addHi heq args ih
  | cast heq args _ ih => exact .cast heq args ih
  | ext name hname heq args _ ih => exact .ext name hname heq args ih

/-- A `ScalarCallN` program returns a register. -/
theorem ScalarCallN.ret_reg {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCallN com) : ∃ w, t = .reg w := by
  induction hcom with
  | ret v => exact ⟨_, rfl⟩
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
  | ext _ _ _ _ _ ih => exact ih
  | callN _ _ _ _ _ ih => exact ih

/-- A register-result variant of `StoreAgreesN.step`: when the binding type `t`
    is `.reg w'` (via `h`), writing the transported value `h ▸ val` to
    `regName curDepth` extends the agreement to the binding-extended valuation
    `V.extend (t := t) val`. This is exactly `StoreAgreesN.step` after substituting
    `t = .reg w'`; it lets the `callN` arm extend its `callNRet retTys`-typed
    binding (which is `.reg w'`) without an ill-typed `▸` over `⟦·⟧`. -/
theorem StoreAgreesN.stepReg {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {st : LstateN} {V : Ctxt.Valuation Γ} {t : JasminTy} {w' : Nat}
    (h : t = .reg w') (val : ⟦t⟧)
    (hlen : Γ.length = curDepth) (harg : nArgs ≤ curDepth)
    (hagree : StoreAgreesN nArgs curDepth st V) :
    StoreAgreesN nArgs (curDepth + 1)
      ((st.setReg (regName curDepth) (h ▸ val : ⟦(JasminTy.reg w')⟧)).nextPc)
      (V.extend (Γ := Γ) (t := t) val) := by
  subst h
  exact StoreAgreesN.step val hlen harg hagree

/-! ## 6. The core multi-result-call straight-line simulation

Same induction skeleton as increment 9's `lsemStraightLeaf_straightOps`, with the
new `callN` arm closed by `lsemStepCallN_callN` (under the carried `LeafAgreesCN`)
+ `StoreAgreesN.step`, the `ext` arm by `lsemStepCallN_ext` (under the carried
`LeafAgreesN`), and the nine other delegated arms by the `lsemStepCallN_*`. The
`callN` arm steps a `callNRet retTys = .reg w'` binding; `hr` converts the
binding-extended valuation over `callNRet retTys :: Γ` to the `.reg w'` shape
`StoreAgreesN.step` expects. -/

/-- **Core simulation (parametrized by an agreeing start state), multi-result-call
    fragment, under both carried leaf agreements `LeafAgreesCN leaf` (for the
    `callN` head) and `LeafAgreesN leaf` (for the single-result `extCall`).** From
    any width-tagged store `st` agreeing with `V` at depth `curDepth`, running the
    multi-result-call-fragment `.var`-chain `straightOpsCallN` succeeds, lands in a
    store agreeing with the binding-extended valuation, and reads `Com.denote com V`
    (transported to its return width) at the return register. -/
theorem lsemStraightCallN_straightOps {leaf : LeafEnvCN}
    (hleafN : JasminLsemLeaf.LeafAgreesN leaf) (hleafCN : LeafAgreesCN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCallN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateN} {V : Ctxt.Valuation Γ}
      {w : Nat} (hw : t = .reg w),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth st V →
      ∃ st', lsemStraightCallN leaf (straightOpsCallN nArgs com curDepth) st = some st' ∧
        evalOperandN st' w (.reg (comRetReg nArgs argName com curDepth)) =
          some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth st V w hw hlen harg hagree
      cases hw
      refine ⟨st, rfl, ?_⟩
      have key : resolveVar curDepth nArgs argName (fun _ => none) v
          = LOperand.reg (comRetReg nArgs argName (Com.ret v) curDepth) := by
        simp only [comRetReg, resolveVar]
        split <;> rfl
      rw [← key]
      exact hagree v
  | var bop heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_var (leaf := leaf) (V := V) (st := st) bop heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_var, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_const (leaf := leaf) (V := V) (st := st) n hwn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_const, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sel heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_sel (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_sel, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shr hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_shr (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_shr, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shl hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_shl (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_shl, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sar hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_sar (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_sar, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | mulhi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_mulhi (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.mulhi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_mulhi, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addLo heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_addLo (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryLo _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_addLo, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addHi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_addHi (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryHi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_addHi, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | cast heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_cast (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.castW _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_cast, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | ext name hname heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCallN_ext hleafN (V := V) (st := st) name hname heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.extCall name _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_ext, lsemStraightCallN_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | @callN Γ s w w' retTys name hr heq args body hbody ih =>
      intro nArgs curDepth st V w₀ hw hlen harg hagree
      have hstep := lsemStepCallN_callN hleafCN (V := V) (st := st) name hr heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ :=
        StoreAgreesN.stepReg (t := callNRet retTys) (w' := w') hr
          ((⟨JasminOp.callN name [.reg w] retTys, heq, args⟩ :
            Expr jasminDialect Γ (callNRet retTys)).denote V)
          hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCallN_callN, lsemStraightCallN_cons]
        rw [show some (tyWidth (callNRet retTys)) = (some w' : Option Nat) from by
          rw [hr]; rfl] at *
        rw [hstep]; exact hrun
      · simp only [comRetReg]; exact hret

/-! ## 7. Faithfulness, leak state-independence, and the capstone -/

/-- **Straight-line linearizer simulation, multi-result-call fragment.** Running
    the multi-result-call-fragment `.var`-chain `straightOpsCallN` (under both
    carried agreements) from the encoded argument valuation and decoding the
    result register at width `w` equals the source program's `Com.denote`. -/
theorem comToLprog_lsemCallN {leaf : LeafEnvCN}
    (hleafN : JasminLsemLeaf.LeafAgreesN leaf) (hleafCN : LeafAgreesCN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCallN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V) = some st' ∧
      decodeN st' (comRetReg Γ.length argName com Γ.length) w =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraightCallN_straightOps hleafN hleafCN hcom hw (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeN V) (V := V) rfl le_rfl (encodeN_StoreAgreesN V)
  exact ⟨st', hrun, by simpa only [decodeN, evalOperandN] using hret⟩

/-- **Faithfulness (packaged), multi-result-call fragment.** -/
theorem comToLprog_faithful_callN {leaf : LeafEnvCN}
    (hleafN : JasminLsemLeaf.LeafAgreesN leaf) (hleafCN : LeafAgreesCN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCallN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemCallN hleafN hleafCN hcom hw V
  rw [hrun, Option.bind_some, hdec]

/-- **Leak state-independence, multi-result-call fragment (unconditional in the
    input valuations).** The leakage trace of the multi-result-call-fragment
    `.var`-chain is the **same from any two initial states agreeing with the same
    valuation**: every head has a `linstrLeak` reading only the wire syntax — for
    `callN`, the call *name* and the source/destination register *names* (the
    ABI), never a register value, the descriptor width, nor the leaf result — and
    `lsemStepCallN`s successfully, so both states take the `some` branch and the
    tails close by the IH. -/
theorem lsemLeakCallN_straightOps_state_independent {leaf : LeafEnvCN}
    (hleafN : JasminLsemLeaf.LeafAgreesN leaf) (hleafCN : LeafAgreesCN leaf)
    {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarCallN com) :
    ∀ {nArgs curDepth : Nat} {V₁ V₂ : Ctxt.Valuation Γ} (s₁ s₂ : LstateN),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth s₁ V₁ → StoreAgreesN nArgs curDepth s₂ V₂ →
      lsemLeakCallN leaf (straightOpsCallN nArgs com curDepth) s₁ =
        lsemLeakCallN leaf (straightOpsCallN nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v => intro nArgs curDepth V₁ V₂ s₁ s₂ _ _ _ _; rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_var (leaf := leaf) (V := V₁) bop heq args hag1
      have hstep2 := lsemStepCallN_var (leaf := leaf) (V := V₂) bop heq args hag2
      rw [straightOpsCallN_var]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_const (leaf := leaf) (V := V₁) n hwn heq args hag1
      have hstep2 := lsemStepCallN_const (leaf := leaf) (V := V₂) n hwn heq args hag2
      rw [straightOpsCallN_const]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sel heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_sel (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepCallN_sel (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsCallN_sel]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shr hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_shr (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepCallN_shr (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsCallN_shr]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shl hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_shl (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepCallN_shl (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsCallN_shl]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sar hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_sar (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepCallN_sar (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsCallN_sar]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | mulhi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_mulhi (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepCallN_mulhi (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsCallN_mulhi]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addLo heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_addLo (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepCallN_addLo (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsCallN_addLo]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addHi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_addHi (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepCallN_addHi (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsCallN_addHi]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | cast heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_cast (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepCallN_cast (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsCallN_cast]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | ext name hname heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_ext hleafN (V := V₁) name hname heq args hag1
      have hstep2 := lsemStepCallN_ext hleafN (V := V₂) name hname heq args hag2
      rw [straightOpsCallN_ext]
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | @callN Γ s w w' retTys name hr heq args body hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCallN_callN hleafCN (V := V₁) name hr heq args hag1
      have hstep2 := lsemStepCallN_callN hleafCN (V := V₂) name hr heq args hag2
      rw [straightOpsCallN_callN]
      rw [show some (tyWidth (callNRet retTys)) = (some w' : Option Nat) from by
        rw [hr]; rfl] at *
      simp only [lsemLeakCallN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.stepReg (t := callNRet retTys) (w' := w') hr _ hlen harg hag1)
        (StoreAgreesN.stepReg (t := callNRet retTys) (w' := w') hr _ hlen harg hag2)

/-! ## 8. The unconditional multi-result-call capstone: `correct ∧ robust` -/

/-- **`correct ∧ robust` for the multi-result-call fragment
    (`ScalarLeafN ∪ callN`), under the carried leaf agreements.** For a
    multi-result-call-fragment scalar straight-line `Com` with return type `.reg w`
    and a leaf environment `leaf` whose external primitives agree with the dialect
    (`LeafAgreesN leaf` for `extCall`, `LeafAgreesCN leaf` for the `callN` head):

    1. *(correct, §7)* running the linearizer-emitted `.var`-chain
       `straightOpsCallN` on the encoded argument valuation and decoding the result
       register at width `w` yields exactly `com.denote V`; and
    2. *(robust / constant-time, §7)* the leakage trace `lsemLeakCallN
       (straightOpsCallN …)` is the **same from the encodings of any two input
       valuations** — the attacker's view is a function of the emitted instruction
       list alone, never of a register value, the descriptor width, or the leaf
       result. For a `callN` it leaks the call **name** + argument-register
       **structure** (the ABI), never argument values.

    This is **unconditional in the runtime inputs**: no IR→x86 faithfulness
    hypothesis, no `jasminc_preserves_ct`. The **only** carried hypotheses are the
    leaf agreements — the external primitives' own KATs, *documented* (a `callN` is a
    external multi-result leaf, exactly like `JasminLeafAgrees`). Both
    conjuncts concern one and the same object — the linearizer-emitted straight-line
    body run by `lsemStraightCallN` (functional) and observed by `lsemLeakCallN`
    (CT). The call is read over the REAL bare `"CALLN:name"` `opToLinstrR` already
    emits (`straightOpsCallN_wire`: the `.fst`-projection is exactly `straightOpsMC`),
    so the emitted **bytes are unchanged**; the head-result width `w'` is the
    typed-step descriptor, never a wire annotation. The `lsem→bytes` encoder and
    Sail tables remain the declared trusted base. -/
theorem owned_lsem_correct_and_robust_callN {leaf : LeafEnvCN}
    (hleafN : JasminLsemLeaf.LeafAgreesN leaf) (hleafCN : LeafAgreesCN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCallN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (§7), under the carried leaf agreements
    ((lsemStraightCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§7)
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V₂)) := by
  refine ⟨comToLprog_faithful_callN hleafN hleafCN hcom hw V, ?_⟩
  intro V₁ V₂
  exact lsemLeakCallN_straightOps_state_independent hleafN hleafCN hcom (encodeN V₁) (encodeN V₂)
    rfl le_rfl (encodeN_StoreAgreesN V₁) (encodeN_StoreAgreesN V₂)

/-! ## 9. Tie-back: the increment-9 opaque-leaf fragment is subsumed -/

/-- Every increment-9 opaque-leaf-fragment program satisfies the multi-result-call
    capstone (for any agreeing leaf): the increment-9 results are special cases of
    the increment-10 ones. -/
theorem owned_lsem_correct_and_robust_callN_of_scalarLeafN {leaf : LeafEnvCN}
    (hleafN : JasminLsemLeaf.LeafAgreesN leaf) (hleafCN : LeafAgreesCN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t}
    (hcom : ScalarLeafN com) {w : Nat} (hw : t = .reg w) (V : Ctxt.Valuation Γ) :
    ((lsemStraightCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakCallN leaf (straightOpsCallN Γ.length com Γ.length) (encodeN V₂)) :=
  owned_lsem_correct_and_robust_callN hleafN hleafCN (ScalarCallN.of_scalarLeafN hcom) hw V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCallN
