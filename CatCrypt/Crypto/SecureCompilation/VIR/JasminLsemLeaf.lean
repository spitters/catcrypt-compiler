/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.String.Defs
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast

/-!
# Faithful `lsem` for the opaque external-leaf fragment
# — increment 9 of porting jasmin's `lsem`

Increments 1–8 brought `regArith`, `regConst`, the width-mixing `select`, the
immediate shifts, the widening-multiply / carry-chain trio and the width cast
`castW` into the unconditional functional ∧ constant-time `lsem` simulation.
Each named `extCall`, `vpackZMM` and `callN` on its deferral list as the
remaining "SIMD / opaque-leaf axes".

This module **adds the `extCall` arm** — the *opaque external-leaf* op — to the
simulation. `extCall` is an external primitive: its meaning is a
**carried leaf** (an external function keyed by `name`), exactly like the
existing opaque-leaf edge `JasminPrintSemCorrect.LeafAgrees` /
`CryptoToJasminComCorrect.JasminLeafAgrees`. Its correctness is the leaf's own
KAT, carried as a hypothesis — this is the honest, achievable target.

## What the op emits, and the fidelity route

`opToLinstrR` (`JasminLprogExport.lean`) lowers a NON-reserved `extCall name`
to one of two width-dependent shadow mnemonics over the resolved sources:

    extCall name argTys retTy  ↦
      Lopn [.reg dst] ("CALL:" ++ name) srcs                    -- all-GP widths
      Lopn [.reg dst] (encodeCallW "CALLW:" name retW argWs) srcs  -- SSE-class (> 64)

An **all-GP** call (`callHasWide false`) keeps the bare `"CALL:" ++ name`; a call
with an SSE-class (`> 64`, e.g. `reg 128`) argument or result emits the widened
`"CALLW:" ++ <retW> ++ ";" ++ <argWs> ++ ";" ++ name` header (the widths reach
`expandCallShadows`, which routes each to its SysV register class). `callStruct?`
recognises both and recovers `name` (stripping the numeric header for `CALLW:`).
(The reserved `loadSymPrefix` names are the orthogonal `.rodata` symbol-load seam
and are out of scope here.) The emitted bytes are exactly this — we do **not**
invent a mnemonic, add an operand, or touch the emit path. As in
increment 8 the simulation threads a list of **typed instructions**
`LinstrRT := LinstrR × Option Nat` (reusing increment 8's pairing): the
`LinstrR` component is *exactly* `straightOpsMC`'s emitted instruction (its
`.fst`-projection equals `straightOpsMC` / `straightOpsLeaf`, the **wire/byte
tie** `straightOpsLeaf_wire`), and the descriptor slot is `none` on every
extCall binding (the leaf needs no width descriptor: its result width is the
op's `retTy`, read from the binding's typing).

## The opaque leaf and the carried agreement (honest, external)

We scope the `extCall` arm to the **single register argument, register result**
shape `extCall name [.reg w] (.reg w')` — the call form a scalar straight-line
kernel emits (one source register, one destination register). The lsem step
reads the source register `a` (at the recovered input width `w`) and writes the
result of a **leaf function** `leaf name`, drawn from a carried leaf environment
`LeafEnvN`. The simulation then CARRIES the leaf-agreement hypothesis

    LeafAgreesN leaf  :  ∀ name w w' (va : BitVec w),
        (leaf name w w' va : BitVec w') = jasminExtSem name [.reg w] (.reg w') ⟨va⟩

i.e. the lsem step's leaf = the `Com` `extCall`'s denotation leaf. This is the
honest external-primitive edge (the analogue of `JasminLeafAgrees`): nothing in
this module *proves* the external primitive correct — its correctness is its own
KAT, stated here as `LeafAgreesN`. (For a generic register `extCall`,
`jasminExtSem` falls to the opaque default `0`; a real intrinsic supplies its
own `leaf`, and `LeafAgreesN` is then the obligation discharged by the
intrinsic's KAT, exactly as `latticeLeafAgrees` discharges the lattice NTT
leaves.)

## Leakage (constant-time): the ABI, never values

The leak of the extCall wire `Lopn [.reg dst] mnem [.reg a]` (with `mnem` the
`"CALL:name"` or `"CALLW:<retW>;<argWs>;name"` shadow) is, by `linstrLeak`, the
single event `LLeak.opn mnem [regShape dst] [regShape a]` — the opcode (= the
**call name**, plus the marshal **widths** in the `CALLW:` case) plus the
destination/argument register **names** (the ABI structure), and **no register
value**. So an opaque
CT leaf leaks via its own ABI exactly as required: name + argument-register
structure, never argument values. This is automatic — `lsemLeakCast` already
leaks `linstrLeak i.fst`, and the extCall wire is an `Lopn`.

## Op set now covered

`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
addCarryHi ∪ castW ∪ extCall` — the `ScalarLeafN` predicate, which subsumes
increment 8's `ScalarCastN` (`ScalarLeafN.of_scalarCastN`). The `extCall` arm
is the first **opaque** binding: its value is not computed from the dialect
denotation but supplied by the carried leaf and tied back by `LeafAgreesN`.

### `vpackZMM` / `callN`: assessed, deferred

* **`vpackZMM`** (`bop : JasminBinOp`, `[.reg 512, .reg 512] → .reg 512`) — needs
  the **SIMD lane model**: its denotation `zmmPackQ bop a b` is the per-64-bit-
  lane `bop` over eight lanes of a 512-bit register, and a faithful step must
  read/write `BitVec 512` register tags and run the 8-lane pack. The width-tagged
  store `LstateN` *can* hold a `BitVec 512` tag, but no `lsemStep*` arm models the
  lane decomposition / `zmmPackQ` data effect, and `evalOperandN`/`applyOpnN` are
  scalar (one homogeneous width, the binop list). Adding it cleanly requires a
  lane-structured step (`zmmPackQ` as an `applyOpn`-level primitive) — a separate
  SIMD increment. **Deferred** (not faked).

* **`callN`** (`name`, `argTys`, `retTys` — multi-result) — needs **multiple
  destination registers**. At the single-output `LinstrR` layer `opToLinstrR`
  emits only the head slot (`"CALLN:" ++ name`, one `.reg dst`), and the dialect
  `Expr` denotation is the opaque default of the *head* result type
  (`JasminTy.default (callNRet retTys)`); the `k`-output tuple
  (`callNDefaults`) is consumed only by the `func.call` lowering, which writes
  `k` destinations. A faithful lsem step would have to write all `k` result
  registers and a multi-slot store-agreement, which `straightOps*`/`StoreAgreesN`
  (single fresh `regName curDepth` per binding) do not model. **Deferred** (not
  faked); the single-head projection it exposes is already an `extCall`-shaped
  opaque leaf, so the *head slot* is covered in spirit by this increment.

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`.** The `lsem→bytes` encoder and Sail tables remain the
declared trusted base, as for every verified compiler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf

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

/-! ## 1. The opaque leaf environment and the carried agreement -/

/-- An **opaque external-leaf environment**: for a leaf `name` and the
    single-register-arg / register-result shape `[.reg w] → .reg w'`, the leaf
    is a function `BitVec w → BitVec w'`. This is the lsem model's analogue of
    `JasminPrintSemCorrect.LeafSem`, specialised to the scalar call shape a
    straight-line kernel emits. -/
abbrev LeafEnvN : Type := (name : String) → (w w' : Nat) → BitVec w → BitVec w'

/-- **The carried leaf-agreement hypothesis (honest, external).** The lsem
    step's leaf `leaf name w w'` equals the `Com` `extCall`'s denotation leaf
    `jasminExtSem name [.reg w] (.reg w')` on every single-register argument.
    This is the opaque external-primitive edge: its truth is the leaf's own KAT,
    exactly as `JasminLeafAgrees` / `latticeLeafAgrees`. (For a generic register
    `extCall`, the RHS is the opaque default `0`; a real intrinsic supplies a
    `leaf` and discharges this from its KAT.) -/
def LeafAgreesN (leaf : LeafEnvN) : Prop :=
  ∀ (name : String) (w w' : Nat) (va : BitVec w),
    (leaf name w w' va : BitVec w') =
      jasminExtSem name [.reg w] (.reg w') (.cons va .nil)

/-! ## 2. Recognising the `extCall` wire and the typed step -/

/-- Drop the first `;`-delimited field of a char list: everything up to and
    including the next `;`. Two applications strip the `<retW>;<argWs>;` numeric
    header of a widened `CALLW:` mnemonic, leaving the leaf `name` verbatim (which
    may itself contain `;`, since no further splitting happens). -/
def dropSemiField (cs : List Char) : List Char := (cs.dropWhile (· ≠ ';')).drop 1

/-- The decimal string of a `Nat` contains no `;` — its characters are all
    digits. Used to show the two numeric header fields (`<retW>`, `<argWs>`) of a
    `CALLW:` mnemonic are `;`-free, so `dropSemiField` splits exactly at the two
    header delimiters and recovers the leaf `name`. -/
theorem semi_notMem_toString (n : Nat) : ∀ c ∈ (toString n).toList, c ≠ ';' := by
  intro c hc
  have hd : (toString n).toList = Nat.toDigits 10 n := by simp [toString, Nat.repr]
  rw [hd] at hc
  have hdig : c.isDigit = true :=
    Nat.isDigit_of_mem_toDigits (by norm_num) (by norm_num) hc
  intro hcs; rw [hcs] at hdig; exact absurd hdig (by decide)

/-- `dropSemiField` of a `;`-free prefix followed by `';' :: t` is exactly `t`:
    the `dropWhile` consumes the whole `;`-free `pre`, stops at the delimiter, and
    the `drop 1` discards it. -/
theorem dropSemiField_prefix (pre t : List Char) (h : ∀ c ∈ pre, c ≠ ';') :
    dropSemiField (pre ++ ';' :: t) = t := by
  unfold dropSemiField
  rw [List.dropWhile_append_of_pos (by intro c hc; simpa using h c hc)]
  simp [List.dropWhile]

/-- Stripping a `<pfx><retS>;<argS>;<name>` mnemonic's `pfx` and its two numeric
    header fields (both `;`-free) with `dropSemiField` twice recovers `name`
    verbatim. Prefix-generic so both the single-result `"CALLW:"` and the
    multi-result `"CALLNW:"` widened shadows reuse it. -/
theorem callw_extract (pfx retS argS name : String)
    (hr : ∀ c ∈ retS.toList, c ≠ ';') (ha : ∀ c ∈ argS.toList, c ≠ ';') :
    dropSemiField (dropSemiField
      ((pfx ++ retS ++ ";" ++ argS ++ ";" ++ name).toList.drop pfx.toList.length))
      = name.toList := by
  have e : (pfx ++ retS ++ ";" ++ argS ++ ";" ++ name).toList
      = pfx.toList ++ (retS.toList ++ ';' :: (argS.toList ++ ';' :: name.toList)) := by
    simp [String.toList_append, List.append_assoc]
  rw [e, List.drop_left, dropSemiField_prefix _ _ hr, dropSemiField_prefix _ _ ha]

/-- Recognise a structured external-call instruction and return `(dst, name, a)`;
    `none` otherwise. `opToLinstrR` lowers a NON-reserved single-arg `extCall name`
    to one of two width-dependent shadow mnemonics over the resolved source:

    * an **all-GP** call (`callHasWide false`, both widths `≤ 64`) keeps the plain
      `"CALL:" ++ name` shadow — we strip the `"CALL:"` prefix to recover `name`;
    * a call with an **SSE-class** (`> 64`, e.g. `reg 128`) argument or result
      emits the widened `"CALLW:" ++ <retW> ++ ";" ++ <argWs> ++ ";" ++ name`
      shadow (`encodeCallW`) — we strip the `"CALLW:"` prefix and the two numeric
      header fields (`dropSemiField` twice) to recover `name`.

    The two prefixes are mutually exclusive (`"CALL:"[4] = ':'` vs
    `"CALLW:"[4] = 'W'`), and neither is a prefix of the `callN` head shadows
    `"CALLN:"`/`"CALLNW:"` (index `4` is `'N'`), so this single-result recogniser
    returns `none` on the multi-result `callN` wire. Matching on the character
    lists (not `String.startsWith`/`drop`) keeps the recogniser kernel-reducing on
    string literals. -/
def callStruct? : LinstrR → Option (String × String × String)
  | .Lopn [.reg dst] opn [.reg a] =>
      let ns := opn.toList
      if "CALLW:".toList.isPrefixOf ns then
        some (dst,
          String.ofList (dropSemiField (dropSemiField (ns.drop "CALLW:".toList.length))), a)
      else if "CALL:".toList.isPrefixOf ns then
        some (dst, String.ofList (ns.drop "CALL:".toList.length), a)
      else none
  | _ => none

/-- The typed single-step semantics for the opaque-leaf fragment, parametrised by
    a leaf environment `leaf`. On an extCall-tagged instruction (`callStruct?`
    recognises the `"CALL:name"` wire form *and* the descriptor `some w'` is
    present) it reads the source `a` at its store width `w` (recovered from `a`'s
    tag), and writes the leaf result `leaf name w w' (va)` (with `w'` the
    binding's result width, carried in the typed `.snd` descriptor exactly as
    increment 8 carries the cast width) to `dst` — faithful to `eval_instr`'s
    external-`Oasm` `Lopn`, with the leaf the external primitive. On every other
    typed instruction it delegates the wire to increment 8's `lsemStepCast`.

    The result width `w'` of the leaf is not on the wire; it lives only in the
    typed `.snd` descriptor (the model's typed environment, the `extCall`'s
    `retTy` width recovered from the binding's typing) — never a wire annotation,
    so the bytes are unchanged (`straightOpsLeaf_wire`). -/
def lsemStepLeaf (leaf : LeafEnvN) (i : LinstrRT) (s : LstateN) :
    Option LstateN :=
  match callStruct? i.fst, i.snd with
  | some (dst, name, a), some w' =>
      match readReg s (.reg a) with
      | some ⟨w, va⟩ => some ((s.setReg dst (leaf name w w' va)).nextPc)
      | none => none
  | _, _ => lsemStepCast i s

theorem callStruct?_extCall {w w' : Nat} (name dst a : String)
    (hname : loadSymTarget? name = none) :
    callStruct? (opToLinstrR (JasminOp.extCall name [.reg w] (.reg w')) dst [.reg a])
      = some (dst, name, a) := by
  simp only [opToLinstrR, hname]
  split
  · -- SSE-class (`> 64`) widths: `opToLinstrR` emits the widened
    -- `CALLW:<retW>;<argWs>;name` shadow (`encodeCallW`).
    have hm : encodeCallW "CALLW:" name (callMarshalWidth (.reg w'))
        (List.map callMarshalWidth [.reg w])
        = "CALLW:" ++ toString w' ++ ";" ++ toString w ++ ";" ++ name := rfl
    rw [hm]
    have hpfx : "CALLW:".toList.isPrefixOf
        ("CALLW:" ++ toString w' ++ ";" ++ toString w ++ ";" ++ name).toList = true := by
      simp [List.isPrefixOf, String.toList_append]
    simp only [callStruct?, hpfx, if_true,
      callw_extract _ _ _ _ (semi_notMem_toString w') (semi_notMem_toString w),
      String.ofList_toList]
  · -- all-GP (`≤ 64`) widths: `opToLinstrR` keeps the plain `CALL:name` shadow.
    simp only [callStruct?]
    rw [String.toList_append]
    simp [List.isPrefixOf, String.ofList_toList]

theorem lsemStepLeaf_of_delegate (leaf : LeafEnvN) (i : LinstrRT) (s : LstateN)
    (h : callStruct? i.fst = none ∨ i.snd = none) :
    lsemStepLeaf leaf i s = lsemStepCast i s := by
  rcases h with h | h
  · simp only [lsemStepLeaf, h]
  · simp only [lsemStepLeaf, h]; cases callStruct? i.fst <;> rfl

/-! ### `lsemStraightLeaf` / leakage over the typed step -/

/-- Typed straight-line execution: the sequential fold of `lsemStepLeaf`. -/
def lsemStraightLeaf (leaf : LeafEnvN) : List LinstrRT → LstateN → Option LstateN
  | [], s => some s
  | i :: is, s =>
      match lsemStepLeaf leaf i s with
      | some s' => lsemStraightLeaf leaf is s'
      | none => none

@[simp] theorem lsemStraightLeaf_nil (leaf : LeafEnvN) (s : LstateN) :
    lsemStraightLeaf leaf [] s = some s := rfl

@[simp] theorem lsemStraightLeaf_cons (leaf : LeafEnvN) (i : LinstrRT)
    (is : List LinstrRT) (s : LstateN) :
    lsemStraightLeaf leaf (i :: is) s =
      (match lsemStepLeaf leaf i s with
        | some s' => lsemStraightLeaf leaf is s'
        | none => none) := rfl

/-- Typed leakage trace: the leak of each typed instruction is the leak of its
    **wire** (`linstrLeak i.fst`), so neither the descriptor `w'` nor any leaf
    value enters the attacker's view. For an extCall wire `Lopn [.reg dst]
    ("CALL:" ++ name) [.reg a]`, `linstrLeak` yields the call name plus the
    destination/argument register **names** (the ABI), never a value. -/
def lsemLeakLeaf (leaf : LeafEnvN) : List LinstrRT → LstateN → List JasminLsemRobust.LLeak
  | [], _ => []
  | i :: is, s =>
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepLeaf leaf i s with
          | some s' => lsemLeakLeaf leaf is s'
          | none => [])

@[simp] theorem lsemLeakLeaf_nil (leaf : LeafEnvN) (s : LstateN) :
    lsemLeakLeaf leaf [] s = [] := rfl

@[simp] theorem lsemLeakLeaf_cons (leaf : LeafEnvN) (i : LinstrRT)
    (is : List LinstrRT) (s : LstateN) :
    lsemLeakLeaf leaf (i :: is) s =
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepLeaf leaf i s with
          | some s' => lsemLeakLeaf leaf is s'
          | none => []) := rfl

/-! ## 3. The typed emission `straightOpsLeaf` and the wire/byte tie

`straightOpsLeaf` mirrors increment 8's `straightOpsCast`, but emits the typed
`LinstrRT` for an extCall binding as its real `opToLinstrR` instruction
(`"CALL:name"`) paired with the descriptor `some w'` (the `retTy` width). Every
other binding reuses `straightOpsCast`'s emission. The `.fst`-projection of the
typed list is *exactly* `straightOpsMC` — the wire/byte tie. -/

/-- The typed straight-line `LinstrRT` chain a `Com` emits in the opaque-leaf
    fragment. The single-reg-arg / reg-result extCall binding emits its **real**
    `opToLinstrR (extCall name [.reg w] (.reg w'))` instruction (bare
    `"CALL:name"`) paired with the descriptor `some w'`; every other binding
    reuses `straightOpsCast`'s emission (so cast bindings keep their `some w'`
    descriptor, the rest `none`). -/
def straightOpsLeaf (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrRT
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let elem : LinstrRT :=
        match e.op with
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
      elem :: straightOpsLeaf nArgs body (curDepth + 1)

/-- **The wire/byte tie.** The `.fst`-projection (the emitted bytes) of the typed
    chain `straightOpsLeaf` is *exactly* increment 7's `straightOpsMC` — the
    descriptors `w'` (cast / leaf) live only in the `.snd` component. So
    `straightOpsLeaf` emits the same bytes as `straightOpsMC`, which is
    `comToBody`'s body; the extCall's wire is the REAL `"CALL:name"` /
    `"CALLW:…;name"` `opToLinstrR` output. -/
theorem straightOpsLeaf_wire (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsLeaf nArgs com curDepth).map Prod.fst =
      straightOpsMC nArgs com curDepth := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      simp only [straightOpsLeaf, straightOpsMC, List.map_cons, ih]
      congr 1
      cases hop : e.op <;> (try rfl)
      · rename_i name argTys retTy
        cases retTy <;> rfl

/-- The `.fst`-projection of `straightOpsLeaf` also equals `straightOpsCast`'s
    (both project to `straightOpsMC`) — so the leaf chain emits the same bytes as
    the increment-8 chain. -/
theorem straightOpsLeaf_wire_cast (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsLeaf nArgs com curDepth).map Prod.fst =
      (straightOpsCast nArgs com curDepth).map Prod.fst := by
  rw [straightOpsLeaf_wire, straightOpsCast_wire]

/-! ### `straightOpsLeaf` unfolding on the extCall and delegated heads -/

theorem straightOpsLeaf_ext {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w w' : Nat} (name : String)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
    (body : Com jasminDialect (.reg w' :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.extCall name [.reg w] (.reg w')) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
            Expr jasminDialect Γ (.reg w'))), some w')
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsLeaf_cast {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (body : Com jasminDialect (.reg w' :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.castW w w', heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.castW w w') (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))), some w')
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsLeaf_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.shrImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SHR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsLeaf_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.shlImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SHL" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsLeaf_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.sarImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SAR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsLeaf_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.regArith bop w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsLeaf_const {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.regConst w n, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .nil => rfl

theorem straightOpsLeaf_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.select w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.select w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsLeaf_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.mulhi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsLeaf_addLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsLeaf_addHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (body : Com jasminDialect (.reg 1 :: Γ) s) :
    straightOpsLeaf nArgs (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), none)
      :: straightOpsLeaf nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-! ## 4. Per-binding agreement for `extCall` and the delegated heads -/

/-- The `exprArgs` of an extCall binding is its single resolved source. -/
theorem exprArgs_extCall {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect} {w w' : Nat}
    (name : String)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
    (a : Ctxt.Var Γ (.reg w)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.extCall name [.reg w] (.reg w'), heq, .cons a .nil⟩ :
        Expr jasminDialect Γ (.reg w'))
      = [resolveVar curDepth nArgs argName (fun _ => none) a] := rfl

/-- **extCall per-binding step (opaque leaf), under the carried agreement.** From
    a store agreeing with `V`, the typed extCall instruction `(opToLinstrR
    (extCall name [.reg w] (.reg w')) …, some w')` `lsemStepLeaf`s to the state
    writing the binding's denotation `(extCall …).denote V` to `regName curDepth`,
    reading the source `a` at the recovered input width `w` and writing the leaf
    result at the descriptor width `w'`. The denotation equality is the carried
    `LeafAgreesN` hypothesis: the lsem step's leaf = the dialect `extCall` leaf
    (`jasminExtSem`). Faithful to `eval_instr`'s external `Lopn`; honest opaque
    external primitive. -/
theorem lsemStepLeaf_ext {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w w' : Nat} (name : String)
    (hname : loadSymTarget? name = none)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (opToLinstrR (JasminOp.extCall name [.reg w] (.reg w')) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
              Expr jasminDialect Γ (.reg w'))), some w')
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
          Expr jasminDialect Γ (.reg w')).denote V)).nextPc) := by
  match args with
  | .cons a .nil =>
    have ha : readReg st (.reg (operandName (resolveVar curDepth nArgs argName (fun _ => none) a)))
        = some ⟨w, a.lookup V⟩ := by
      have := readReg_resolveVar a hagree; rwa [resolveVar_isReg a] at this
    rw [exprArgs_extCall name heq a, resolveVar_isReg a]
    simp only [lsemStepLeaf, callStruct?_extCall name _ _ hname, ha]
    congr 2
    -- the leaf value equals the `extCall` denotation, by the carried agreement
    rw [hleaf name w w' (a.lookup V)]
    rfl

/-- The delegated (non-extCall) bindings step via `lsemStepLeaf` to their
    denotations: each packages through `lsemStepLeaf_of_delegate` then the
    increment-8 `lsemStepCast_*`. The extCall head is excluded (its descriptor is
    `some w'` and `callStruct?` recognises it), so the delegate condition uses
    the cast/non-leaf heads' descriptor / wire shape. -/
theorem lsemStepLeaf_var {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_var bop heq args hagree

theorem lsemStepLeaf_const {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (n : Nat) (hwn : w = 64 ∨ w = 32)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_const (V := V) n hwn heq args hagree

theorem lsemStepLeaf_sel {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (opToLinstrR (JasminOp.select w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_sel heq args hagree

theorem lsemStepLeaf_shr {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (shiftLinstr "SHR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_shr hn heq args hagree

theorem lsemStepLeaf_shl {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (shiftLinstr "SHL" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_shl hn heq args hagree

theorem lsemStepLeaf_sar {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (shiftLinstr "SAR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_sar hn heq args hagree

theorem lsemStepLeaf_mulhi {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_mulhi heq args hagree

theorem lsemStepLeaf_addLo {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_addLo heq args hagree

theorem lsemStepLeaf_addHi {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1)).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inr rfl)]
  exact lsemStepCast_addHi heq args hagree

theorem lsemStepLeaf_cast {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf leaf
        (opToLinstrR (JasminOp.castW w w') (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))), some w')
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w')).denote V)).nextPc) := by
  rw [lsemStepLeaf_of_delegate _ _ _ (Or.inl ?_)]
  · exact lsemStepCast_cast heq args hagree
  · -- the cast wire is a `ZEROEXT`/`TRUNC`, never a `CALL:` head, so `callStruct? = none`
    simp only [opToLinstrR, callStruct?]
    split <;> rename_i h <;> first | rfl | (injection h with _ ho _; subst ho; split <;> rfl)

/-! ## 5. The opaque-leaf source fragment `ScalarLeafN` -/

/-- The straight-line **opaque-leaf-fragment** scalar source: every binding is a
    `regArith`, a width-mixing `select`, an in-range immediate shift, one of the
    widening-multiply / carry-chain trio, a width cast `castW w w'`, or an opaque
    external leaf `extCall name [.reg w] (.reg w')` (single register argument,
    register result, non-reserved name). This subsumes increment 8's
    `ScalarCastN`. The `ext` arm carries `loadSymTarget? name = none` so the
    binding emits the `"CALL:name"` wire (not the orthogonal symbol-load). -/
inductive ScalarLeafN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
      ScalarLeafN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | const {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (n : Nat)
      (hwn : w = 64 ∨ w = 32)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.regConst w n, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.select w, heq, args⟩ body)
  | shr {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.shrImm w n, heq, args⟩ body)
  | shl {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.shlImm w n, heq, args⟩ body)
  | sar {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.sarImm w n, heq, args⟩ body)
  | mulhi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.mulhi w, heq, args⟩ body)
  | addLo {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body)
  | addHi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
      {body : Com jasminDialect (.reg 1 :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body)
  | cast {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.castW w w', heq, args⟩ body)
  | ext {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat} (name : String)
      (hname : loadSymTarget? name = none)
      (heq : DialectSignature.ret (d := jasminDialect)
        (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ScalarLeafN body) :
      ScalarLeafN (.var ⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ body)

/-- `ScalarLeafN` subsumes `ScalarCastN`: every increment-8 width-cast-fragment
    program is in the opaque-leaf fragment. So the increment-8 results are special
    cases. -/
theorem ScalarLeafN.of_scalarCastN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : ScalarCastN com) : ScalarLeafN com := by
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

/-- A `ScalarLeafN` program returns a register. -/
theorem ScalarLeafN.ret_reg {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com) : ∃ w, t = .reg w := by
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

/-! ## 6. The core opaque-leaf straight-line simulation

Same induction skeleton as increment 8's `lsemStraightCast_straightOps`, with the
new `ext` arm closed by `lsemStepLeaf_ext` (under the carried `LeafAgreesN`) +
`StoreAgreesN.step`, and the nine delegated arms by the `lsemStepLeaf_*` (each
reducing through `lsemStepLeaf_of_delegate` to the increment-8 `lsemStepCast_*`).
The `ext` arm steps a `.reg w'` binding, so the binding-extended valuation is over
`.reg w' :: Γ` — `StoreAgreesN.step` absorbs the width-changing leaf result. -/

/-- **Core simulation (parametrized by an agreeing start state), opaque-leaf
    fragment, under the carried leaf agreement `LeafAgreesN leaf`.** From any
    width-tagged store `st` agreeing with `V` at depth `curDepth`, running the
    opaque-leaf-fragment `.var`-chain `straightOpsLeaf` succeeds, lands in a store
    agreeing with the binding-extended valuation, and reads `Com.denote com V`
    (transported to its return width) at the return register. The external leaf's
    value is supplied by `leaf` and tied to the dialect denotation by
    `LeafAgreesN`. -/
theorem lsemStraightLeaf_straightOps {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateN} {V : Ctxt.Valuation Γ}
      {w : Nat} (hw : t = .reg w),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth st V →
      ∃ st', lsemStraightLeaf leaf (straightOpsLeaf nArgs com curDepth) st = some st' ∧
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
      have hstep := lsemStepLeaf_var (leaf := leaf) (V := V) (st := st) bop heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_var, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_const (leaf := leaf) (V := V) (st := st) n hwn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_const, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sel heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_sel (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_sel, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shr hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_shr (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_shr, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shl hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_shl (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_shl, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sar hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_sar (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_sar, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | mulhi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_mulhi (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.mulhi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_mulhi, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addLo heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_addLo (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryLo _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_addLo, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addHi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_addHi (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryHi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_addHi, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | cast heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_cast (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.castW _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_cast, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | ext name hname heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepLeaf_ext hleaf (V := V) (st := st) name hname heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.extCall name _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsLeaf_ext, lsemStraightLeaf_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret

/-! ## 7. Faithfulness, leak state-independence, and the capstone -/

/-- **Straight-line linearizer simulation, opaque-leaf fragment.** Running the
    opaque-leaf-fragment `.var`-chain `straightOpsLeaf` (under `LeafAgreesN`) from
    the encoded argument valuation and decoding the result register at width `w`
    equals the source program's `Com.denote`. -/
theorem comToLprog_lsemLeaf {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V) = some st' ∧
      decodeN st' (comRetReg Γ.length argName com Γ.length) w =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraightLeaf_straightOps hleaf hcom hw (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeN V) (V := V) rfl le_rfl (encodeN_StoreAgreesN V)
  exact ⟨st', hrun, by simpa only [decodeN, evalOperandN] using hret⟩

/-- **Faithfulness (packaged), opaque-leaf fragment.** -/
theorem comToLprog_faithful_leaf {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemLeaf hleaf hcom hw V
  rw [hrun, Option.bind_some, hdec]

/-- **Leak state-independence, opaque-leaf fragment (unconditional in the input
    valuations).** The leakage trace of the opaque-leaf-fragment `.var`-chain is
    the **same from any two initial states agreeing with the same valuation**:
    every head (`regArith`, `select`, a shift, one of the trio, a `castW`, or an
    `extCall`) has a `linstrLeak` reading only the wire syntax — for `extCall`,
    the call *name* and the source/destination register *names* (the ABI), never
    a register value, the descriptor width, nor the leaf result — and
    `lsemStepLeaf`s successfully, so both states take the `some` branch and the
    tails (still agreeing with the extended valuation) close by the IH. -/
theorem lsemLeakLeaf_straightOps_state_independent {leaf : LeafEnvN}
    (hleaf : LeafAgreesN leaf) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com) :
    ∀ {nArgs curDepth : Nat} {V₁ V₂ : Ctxt.Valuation Γ} (s₁ s₂ : LstateN),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth s₁ V₁ → StoreAgreesN nArgs curDepth s₂ V₂ →
      lsemLeakLeaf leaf (straightOpsLeaf nArgs com curDepth) s₁ =
        lsemLeakLeaf leaf (straightOpsLeaf nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v => intro nArgs curDepth V₁ V₂ s₁ s₂ _ _ _ _; rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_var (leaf := leaf) (V := V₁) bop heq args hag1
      have hstep2 := lsemStepLeaf_var (leaf := leaf) (V := V₂) bop heq args hag2
      rw [straightOpsLeaf_var]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_const (leaf := leaf) (V := V₁) n hwn heq args hag1
      have hstep2 := lsemStepLeaf_const (leaf := leaf) (V := V₂) n hwn heq args hag2
      rw [straightOpsLeaf_const]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sel heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_sel (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepLeaf_sel (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsLeaf_sel]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shr hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_shr (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepLeaf_shr (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsLeaf_shr]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shl hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_shl (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepLeaf_shl (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsLeaf_shl]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sar hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_sar (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepLeaf_sar (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsLeaf_sar]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | mulhi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_mulhi (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepLeaf_mulhi (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsLeaf_mulhi]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addLo heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_addLo (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepLeaf_addLo (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsLeaf_addLo]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addHi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_addHi (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepLeaf_addHi (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsLeaf_addHi]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | cast heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_cast (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepLeaf_cast (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsLeaf_cast]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | ext name hname heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepLeaf_ext hleaf (V := V₁) name hname heq args hag1
      have hstep2 := lsemStepLeaf_ext hleaf (V := V₂) name hname heq args hag2
      rw [straightOpsLeaf_ext]
      simp only [lsemLeakLeaf_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)

/-! ## 8. The unconditional opaque-leaf capstone: `correct ∧ robust` -/

/-- **`correct ∧ robust` for the opaque-leaf fragment
    (`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
    addCarryHi ∪ castW ∪ extCall`), under the carried leaf agreement.** For an
    opaque-leaf-fragment scalar straight-line `Com` with return type `.reg w` and
    a leaf environment `leaf` whose external primitives agree with the dialect
    (`LeafAgreesN leaf`):

    1. *(correct, §7)* running the linearizer-emitted `.var`-chain
       `straightOpsLeaf` on the encoded argument valuation and decoding the result
       register at width `w` yields exactly `com.denote V`; and
    2. *(robust / constant-time, §7)* the leakage trace `lsemLeakLeaf
       (straightOpsLeaf …)` is the **same from the encodings of any two input
       valuations** — the attacker's view is a function of the emitted instruction
       list alone, never of a register value, the descriptor width, or the leaf
       result. For an `extCall` it leaks the call **name** + argument-register
       **structure** (the ABI), never argument values.

    This is **unconditional in the runtime inputs**: no IR→x86 faithfulness
    hypothesis, no `jasminc_preserves_ct`. The **only** carried hypothesis is
    `LeafAgreesN leaf` — the external primitive's own KAT, which is *honest*: an
    `extCall` is an external leaf, exactly like `JasminLeafAgrees`. Both
    conjuncts concern one and the same object — the opaque-leaf linearizer-emitted
    straight-line body run by `lsemStraightLeaf` (functional) and observed by
    `lsemLeakLeaf` (CT). The external call is read over the REAL `"CALL:name"` /
    `"CALLW:…;name"` wire `opToLinstrR` already emits (`straightOpsLeaf_wire`: the
    `.fst`-projection is exactly `straightOpsMC`), so the emitted **bytes are
    unchanged**; the result
    width `w'` is the typed-step descriptor, never a wire annotation. The
    `lsem→bytes` encoder and Sail tables remain the declared trusted base. -/
theorem owned_lsem_correct_and_robust_leaf {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (§7), under the carried leaf agreement
    ((lsemStraightLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§7)
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V₂)) := by
  refine ⟨comToLprog_faithful_leaf hleaf hcom hw V, ?_⟩
  intro V₁ V₂
  exact lsemLeakLeaf_straightOps_state_independent hleaf hcom (encodeN V₁) (encodeN V₂)
    rfl le_rfl (encodeN_StoreAgreesN V₁) (encodeN_StoreAgreesN V₂)

/-! ## 9. Tie-back: the increment-8 width-cast fragment is subsumed -/

/-- Every increment-8 width-cast-fragment program satisfies the opaque-leaf
    capstone (for any agreeing leaf): the increment-8 results are special cases of
    the increment-9 ones. -/
theorem owned_lsem_correct_and_robust_leaf_of_scalarCastN {leaf : LeafEnvN}
    (hleaf : LeafAgreesN leaf) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarCastN com)
    {w : Nat} (hw : t = .reg w) (V : Ctxt.Valuation Γ) :
    ((lsemStraightLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakLeaf leaf (straightOpsLeaf Γ.length com Γ.length) (encodeN V₂)) :=
  owned_lsem_correct_and_robust_leaf hleaf (ScalarLeafN.of_scalarCastN hcom) hw V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
