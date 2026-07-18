/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast

/-!
# Faithful `lsem` for the stack-memory fragment
# — increment 9 of porting jasmin's `lsem`

Increments 1–8 (`JasminLsemCast.lean` and predecessors) brought the whole
register fragment — `regArith`, the width-mixing `select`, the immediate shifts,
the widening-multiply / carry-chain trio and the width cast `castW` — into the
unconditional functional ∧ constant-time `lsem` simulation, all over the
register-only state `LstateN`. Each of those increments named
`stackLoad`/`stackStore` on its deferral list, with the same concrete
obstruction:

> **`stackLoad`/`stackStore`** — the memory/array carrier, an orthogonal state
> axis. `LstateN` is a pure register file (`lvm : String → Σ w, BitVec w`); it
> has no place to hold a `stackArr w n` value (a `Fin n → BitVec w`).

This module **adds the `stackLoad`/`stackStore` arms** — faithfully, *without* a
wire change.

## The model: a register state + an array carrier

`LstateM` bundles the increment-8 register state `LstateN` (`reg`) with an
**array carrier** `larr : String → Σ (w n : Nat), Fin n → BitVec w`: each SSA
name that holds a `stackArr w n` value maps to that array together with its
shape. The register half is reused verbatim — every increment-1–8 step runs over
`s.reg` unchanged — so this module is purely *additive* on the orthogonal memory
axis.

## The fidelity route: a typed step over the REAL `"LOADIDX"/"STOREIDX"` wire

`opToLinstrR` lowers a runtime-indexed `stackLoad w n` to
`Lopn [.reg dst] "LOADIDX" [.arrIdx base idx (w/8)]` and a runtime-indexed
`stackStore w n` to `Lopn [.reg dst] "STOREIDX" [.arrIdx base idx (w/8), val]`
(`JasminLprogExport.lean:304–317`). The emitted **bytes are exactly this**. We do
**not** invent a mnemonic, nor add operands, nor touch the emit path. The SIB
operand `.arrIdx base idx scale` carries the address *structure* (the array base
name, the index-register name, the byte stride `w/8`) — never the array length
`n`, never the loaded/stored value.

The array length `n` is genuinely absent from that wire (`.arrIdx` carries only
`scale = w/8`). Jasmin's own `eval_instr` reads the slot count from the *array
descriptor* — the typed `Lvar`/`Laset` whose `sarr len` the linear program
retains — **not** from the operand syntax. We mirror that exactly: the
load/store step is **indexed by the array shape `(w, n)`**, recovered from the
`Com` binding's typing (`Expr.op = .stackLoad w n` / `.stackStore w n`, whose
`DialectSignature` retains both `w` and `n`), while it runs over the REAL emitted
`"LOADIDX"/"STOREIDX"` instruction. The shape descriptor is the lsem model's
typed environment — the same `sarr len` jasmin's `read_linear` reconstructs from
the typed program — never a change to the surface syntax the bytes print from.

Concretely, the simulation threads a list of **typed instructions**
`LinstrRM := LinstrR × MemTag`: the `LinstrR` component is *exactly* the
increment-8 `straightOpsCast` wire (its `.fst`-projection equals
`(straightOpsCast …).map Prod.fst`, proved below — the **wire/byte tie**), and
the `MemTag` carries, for a memory binding, the array shape `(w, n)` and whether
it is a load or a store (delegating the cast descriptor `Option Nat` for every
register binding). The step `lsemStepMem` runs the `LOADIDX`/`STOREIDX` arm over
the array carrier, and delegates every other typed instruction to increment 8's
`lsemStepCast` over the register half.

## Constant-time: addresses leak, values don't; the index is public

The leak of each typed instruction is the leak of its **wire** (`linstrLeak
i.fst`). For a `LOADIDX`/`STOREIDX` the wire's `.arrIdx base idx scale` leaks the
**address structure** (base name, index-register *name*, stride) via
`OperandShape.idxShape`, exactly the crypto constant-time model — *addresses
leak, values don't*. The loaded/stored **value never enters the leak**, and the
array length `n` (the typed `.snd` descriptor) never enters the wire.

This makes the leak trace state-independent **unconditionally** (the per-
instruction leak is syntactic), as for `castW`. The genuine constant-time
*discipline* the model encodes is the **public-index** requirement: the index
register names a `BitVec 64` whose value is data-independent and in range
(`idx.toNat < n`). A **secret-dependent** index would make the leaked address
`(base, idx, scale)` depend on a secret through `idx`'s *runtime value* — but
note the leak here is over the index *register name* (syntactic), not its value,
so the wire-level state-independence holds regardless; the public-index
hypothesis is stated honestly on the functional side (it is what makes the cell
addressed by `stackGet`/`stackSet` the intended one). Secret-indexed loads are
genuinely *not* constant-time on real silicon (cache/timing) — that residual is
out of scope of this syntactic leak model and is flagged, not hidden.

## Op set now covered

`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
addCarryHi ∪ castW ∪ stackLoad ∪ stackStore` — the `ScalarMemN` predicate, which
subsumes increment 8's `ScalarCastN` (`ScalarMemN.of_scalarCastN`).
`stackLoad`/`stackStore` are the **first memory ops**: they read/write the array
carrier, the orthogonal state axis. Still deferred, with the same honest reasons:
`regConst` (string-baked width on the wire), `vpackZMM`/`extCall`/`callN` (SIMD /
opaque-leaf axes), the secret-index address-leak residual (above).

## Compile-time-offset word memory (`loadC` / `storeC`)

Alongside the runtime-indexed `stackLoad`/`stackStore` (which address a
name-keyed whole array by a runtime index register), `LstateM` carries a **third**
axis: the compile-time-offset word memory `lmem : String → Int → BitVec 64`, the
restored increment-1 `Lstate.lmem` carrier. It is **type-identical** to
`X86Backend.Jasmin.JMem 64` (and `JState.mem`), which lets a compile-time-
displacement word load/store (`Lopn`'s `.arr base off` operand) be mirrored
faithfully by the `.loadC` / `.storeC` `MemTag` arms — the exact `JState.loadMem`
/ `JState.storeMem` word semantics (`lsemStepMem_loadC` / `lsemStepMem_storeC`).
This is what closes the memory axis of the `runBlock`↔`lsem` machine-model bridge
(`RunBlockLsemAgree`) for the point-op frame prologue/epilogue (`loadSlot4` /
`storeSlot4`), whose accesses are all compile-time offsets. The `lmem` field is
**additive** (defaulted), so the whole increment-1–9 register/array chain — none
of which touch `lmem` — is unchanged.

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`.** The `lsem→bytes` encoder and Sail tables remain the
declared trusted base, as for every verified compiler.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

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

/-! ## 1. `LstateM`: the register state + an array carrier

`LstateM` adds the orthogonal memory axis: alongside the increment-8 register
state `reg : LstateN`, an array carrier `larr` keyed by SSA name. Each name that
holds a `stackArr w n` value maps to that array together with its shape `(w, n)`;
untouched names default to the empty `stackArr 0 0`. -/

/-- A typed stack-array cell: a `stackArr w n` value together with its shape. -/
abbrev ArrCell : Type := Σ (w n : Nat), Fin n → BitVec w

/-- The default (empty) array cell `stackArr 0 0`. -/
def ArrCell.default : ArrCell := ⟨0, 0, Fin.elim0⟩

/-- The stack-memory linear state: the increment-8 register file `reg : LstateN`
    plus an **array carrier** `larr` mapping each SSA name to a (shape-tagged)
    stack array. The register half is reused verbatim; `larr` is the new,
    orthogonal memory axis. -/
structure LstateM where
  /-- The register half: increment-8's width-tagged register file. -/
  reg : LstateN := {}
  /-- The array carrier: each name maps to a shape-tagged stack array. Untouched
      names default to the empty `stackArr 0 0` cell. -/
  larr : String → ArrCell := fun _ => ArrCell.default
  /-- The **compile-time-offset word memory** (increment-1's orphaned `Lstate.lmem`
      carrier, restored here): a word-addressed map `(base, byte-offset) ↦ word`,
      **type-identical** to `X86Backend.Jasmin.JMem 64 = String → Int → BitVec 64`
      (and to `X86Backend.Jasmin.JState.mem`). This is the axis that lets a
      compile-time-displacement `loadMem`/`storeMem` (`Lopn`'s `.arr base off`
      operand, evaluated at the compile-time offset exactly as increment-1's
      `evalOperand`) be mirrored faithfully. Untouched cells read `0`. The field is
      **additive** (a default is supplied), so every existing `LstateM` value and
      every increment-1–9 step lemma — none of which touch `lmem` — is unchanged. -/
  lmem : String → Int → BitVec 64 := fun _ _ => 0

/-- Read an array **at an expected shape** `(w, n)`: `some arr` iff the stored
    cell's shape is `(w, n)`, `none` on a shape mismatch. The array analogue of
    `LstateN.getW`. -/
def LstateM.getArr (s : LstateM) (r : String) (w n : Nat) :
    Option (Fin n → BitVec w) :=
  if hw : (s.larr r).fst = w then
    if hn : (s.larr r).snd.fst = n then
      some (hn ▸ hw ▸ (s.larr r).snd.snd)
    else none
  else none

/-- Write a width-`w` length-`n` array `arr` to the carrier slot `r`, leaving the
    register half and the pc unchanged. The array analogue of `LstateN.setReg`. -/
def LstateM.setArr (s : LstateM) (r : String) {w n : Nat} (arr : Fin n → BitVec w) :
    LstateM :=
  { s with larr := fun r' => if r' = r then ⟨w, n, arr⟩ else s.larr r' }

/-- Write a width-`w` register `r := v` (delegated to the register half).
    `regName`/`argName` register names never collide with array names that hold a
    `stackArr`, but the carriers are separate anyway. -/
def LstateM.setReg (s : LstateM) (r : String) {w : Nat} (v : BitVec w) : LstateM :=
  { s with reg := s.reg.setReg r v }

/-- Advance the pc (on the register half). -/
def LstateM.nextPc (s : LstateM) : LstateM := { s with reg := s.reg.nextPc }

@[simp] theorem LstateM.reg_setArr (s : LstateM) (r : String) {w n : Nat}
    (arr : Fin n → BitVec w) : (s.setArr r arr).reg = s.reg := rfl

@[simp] theorem LstateM.larr_setReg (s : LstateM) (r : String) {w : Nat}
    (v : BitVec w) : (s.setReg r v).larr = s.larr := rfl

@[simp] theorem LstateM.reg_setReg (s : LstateM) (r : String) {w : Nat}
    (v : BitVec w) : (s.setReg r v).reg = s.reg.setReg r v := rfl

@[simp] theorem LstateM.reg_nextPc (s : LstateM) : s.nextPc.reg = s.reg.nextPc := rfl

@[simp] theorem LstateM.larr_nextPc (s : LstateM) : s.nextPc.larr = s.larr := rfl

@[simp] theorem LstateM.larr_setArr (s : LstateM) (r : String) {w n : Nat}
    (arr : Fin n → BitVec w) :
    (s.setArr r arr).larr = (fun r' => if r' = r then ⟨w, n, arr⟩ else s.larr r') := rfl

@[simp] theorem LstateM.getArr_setArr_same (s : LstateM) (r : String) {w n : Nat}
    (arr : Fin n → BitVec w) : (s.setArr r arr).getArr r w n = some arr := by
  have h : (s.setArr r arr).larr r = ⟨w, n, arr⟩ := by simp [LstateM.setArr]
  unfold LstateM.getArr
  rw [h]
  simp

@[simp] theorem LstateM.getArr_setArr_other (s : LstateM) (r r' : String) {w n : Nat}
    (arr : Fin n → BitVec w) (w' n' : Nat) (h : r' ≠ r) :
    (s.setArr r arr).getArr r' w' n' = s.getArr r' w' n' := by
  have hlarr : (s.setArr r arr).larr r' = s.larr r' := by simp [LstateM.setArr, if_neg h]
  unfold LstateM.getArr
  rw [hlarr]

@[simp] theorem LstateM.getArr_setReg (s : LstateM) (r r' : String) {w : Nat}
    (v : BitVec w) (w' n' : Nat) : (s.setReg r v).getArr r' w' n' = s.getArr r' w' n' := by
  unfold LstateM.getArr; rw [LstateM.larr_setReg]

@[simp] theorem LstateM.getArr_nextPc (s : LstateM) (r : String) (w n : Nat) :
    s.nextPc.getArr r w n = s.getArr r w n := by
  unfold LstateM.getArr; rw [LstateM.larr_nextPc]

/-! ### 1a. The compile-time-offset word memory op (`JState.storeMem` twin)

`storeMemC` writes a 64-bit word to the compile-time-offset memory carrier
`lmem`, the exact mirror of `X86Backend.Jasmin.JState.store` (same shape, same
finite-map update). Reads are the bare `s.lmem base off`, matching
`X86Backend.Jasmin.JState.load` / increment-1's `evalOperand` on the `.arr`
operand. The register half and array carrier are left untouched — this is a
third, orthogonal axis. -/

/-- Write a width-64 word `v` at the compile-time offset `[base + off]` in the word
    memory carrier, leaving the register half, the array carrier and the pc
    unchanged. The `LstateM` twin of `X86Backend.Jasmin.JState.store` (identical
    finite-map update over the type-identical carrier). -/
def LstateM.storeMemC (s : LstateM) (base : String) (off : Int) (v : BitVec 64) :
    LstateM :=
  { s with lmem := fun b o => if b = base ∧ o = off then v else s.lmem b o }

@[simp] theorem LstateM.lmem_setReg (s : LstateM) (r : String) {w : Nat}
    (v : BitVec w) : (s.setReg r v).lmem = s.lmem := rfl

@[simp] theorem LstateM.lmem_setArr (s : LstateM) (r : String) {w n : Nat}
    (arr : Fin n → BitVec w) : (s.setArr r arr).lmem = s.lmem := rfl

@[simp] theorem LstateM.lmem_nextPc (s : LstateM) : s.nextPc.lmem = s.lmem := rfl

@[simp] theorem LstateM.reg_storeMemC (s : LstateM) (base : String) (off : Int)
    (v : BitVec 64) : (s.storeMemC base off v).reg = s.reg := rfl

@[simp] theorem LstateM.larr_storeMemC (s : LstateM) (base : String) (off : Int)
    (v : BitVec 64) : (s.storeMemC base off v).larr = s.larr := rfl

@[simp] theorem LstateM.lmem_storeMemC (s : LstateM) (base : String) (off : Int)
    (v : BitVec 64) :
    (s.storeMemC base off v).lmem
      = fun b o => if b = base ∧ o = off then v else s.lmem b o := rfl

/-- Reading back the just-written cell of a `storeMemC` returns `v` — the memory
    analogue of `JState.load_store_same`. -/
@[simp] theorem LstateM.lmem_storeMemC_same (s : LstateM) (base : String) (off : Int)
    (v : BitVec 64) : (s.storeMemC base off v).lmem base off = v := by
  simp [LstateM.storeMemC]

/-- Reading a different cell of a `storeMemC` falls through — the memory analogue
    of `JState.load_store_other`. -/
@[simp] theorem LstateM.lmem_storeMemC_other (s : LstateM) (base : String) (off : Int)
    (v : BitVec 64) (b' : String) (o' : Int) (h : ¬ (b' = base ∧ o' = off)) :
    (s.storeMemC base off v).lmem b' o' = s.lmem b' o' := by
  simp only [LstateM.storeMemC]; rw [if_neg h]

/-! ## 2. The typed instruction list and its wire projection

The simulation threads `LinstrRM := LinstrR × MemTag`: the `LinstrR` is the
emitted instruction (the increment-8 `straightOpsCast` wire, byte-for-byte), and
the `MemTag` carries the typed-environment descriptor — the cast width for a
register binding (delegated to `lsemStepCast`), or the array shape `(w, n)` plus
the load/store role for a memory binding. The `.fst`-projection of the typed list
is *exactly* `(straightOpsCast …).map Prod.fst` (the wire/byte tie,
`straightOpsMem_wire` below). -/

/-- The typed-environment descriptor for one binding: a register binding carries
    increment-8's cast descriptor `Option Nat` (`reg`); a memory binding carries
    the array shape `(w, n)` and the load/store role. The descriptor is the
    lsem model's typed environment — jasmin's `sarr len` / `Ozeroext ws'` — and
    **never enters the emitted bytes** (`straightOpsMem_wire`). -/
inductive MemTag where
  /-- A register binding, delegated to `lsemStepCast` with this cast descriptor. -/
  | reg (castDescr : Option Nat)
  /-- A `stackLoad w n` binding (read cell → register). -/
  | load (w n : Nat)
  /-- A `stackStore w n` binding (write cell → new array). -/
  | store (w n : Nat)
  /-- A **compile-time-offset word load** (`JState.loadMem` twin): read the word
      memory carrier `lmem` at the compile-time offset carried by the wire's
      `.arr base off` operand → register. The `MEMORY`-axis analogue of the runtime
      `.load`; addresses a fixed displacement, never a runtime index register. -/
  | loadC
  /-- A **compile-time-offset word store** (`JState.storeMem` twin): write a
      register value into `lmem` at the compile-time offset carried by the wire's
      `.arr base off` destination operand. -/
  | storeC
  deriving DecidableEq

/-- A typed linear instruction: the emitted `LinstrR` paired with a `MemTag`. -/
abbrev LinstrRM : Type := LinstrR × MemTag

/-- Recognise the runtime-indexed `LOADIDX` wire form
    `Lopn [.reg dst] "LOADIDX" [.arrIdx base idx _]` (the real `stackLoad` image)
    and return `(dst, base, idx)`; `none` otherwise. The mnemonic is the BARE
    `"LOADIDX"` (`opToLinstrR` applies no `withWidthTag`), matched directly. -/
def loadStruct? : LinstrR → Option (String × String × String)
  | .Lopn [.reg dst] opn [.arrIdx base idx _] =>
      if opn = "LOADIDX" then some (dst, base, idx) else none
  | _ => none

/-- Recognise the runtime-indexed `STOREIDX` wire form
    `Lopn [.reg dst] "STOREIDX" [.arrIdx base idx _, .reg val]` (the real
    `stackStore` image) and return `(dst, base, idx, val)`; `none` otherwise. -/
def storeStruct? : LinstrR → Option (String × String × String × String)
  | .Lopn [.reg dst] opn [.arrIdx base idx _, .reg val] =>
      if opn = "STOREIDX" then some (dst, base, idx, val) else none
  | _ => none

/-- Recognise the **compile-time-offset load** wire form
    `Lopn [.reg dst] "MOVQ" [.arr base off]` (the `JState.loadMem` image, an
    aligned whole-word `mov dst, [base + off]` through a register base) and return
    `(dst, base, off)`; `none` otherwise. The offset `off` is the compile-time
    displacement (`Nat`, evaluated at `Int.ofNat off` exactly as increment-1's
    `evalOperand` on the `.arr` operand), never a runtime index register. -/
def loadCStruct? : LinstrR → Option (String × String × Nat)
  | .Lopn [.reg dst] opn [.arr base off] =>
      if opn = "MOVQ" then some (dst, base, off) else none
  | _ => none

/-- Recognise the **compile-time-offset store** wire form
    `Lopn [.arr base off] "MOVQ" [.reg src]` (the `JState.storeMem` image, an
    aligned whole-word `mov [base + off], src`) and return `(base, off, src)`;
    `none` otherwise. The destination is the memory cell `.arr base off` (compile-
    time displacement), the source a register. -/
def storeCStruct? : LinstrR → Option (String × Nat × String)
  | .Lopn [.arr base off] opn [.reg src] =>
      if opn = "MOVQ" then some (base, off, src) else none
  | _ => none

/-- The typed single-step semantics for the stack-memory fragment. On a
    load-tagged instruction (`loadStruct?` recognises `"LOADIDX"` *and* the tag is
    `.load w n`) it reads the source array `base` at shape `(w, n)`, the index
    register `idx` at width 64, and writes `stackGet arr idx.toNat = (stackLoad w
    n).denote …` to the destination register `dst`. On a store-tagged instruction
    (`storeStruct?` + `.store w n`) it reads `base` at `(w, n)`, `idx` at 64, the
    value `val` at width `w`, and writes the **new array** `stackSet arr idx.toNat
    v = (stackStore w n).denote …` to the destination array slot `dst`. On every
    register binding (`.reg castDescr`) it delegates the wire to increment 8's
    `lsemStepCast` over the register half, leaving the array carrier unchanged.

    Faithful to `eval_instr`'s `Laset`/`Lvar` load/store arms: read the array
    descriptor's shape from the typed environment (the `MemTag`), evaluate the
    SIB address from the wire, run the data effect, write the destination, advance
    the pc. The array shape `(w, n)` is the typed-step parameter (jasmin reads it
    from the `sarr len` descriptor, not the operand syntax); the wire `i.fst` is
    the REAL emitted `"LOADIDX"/"STOREIDX"` instruction. -/
def lsemStepMem (i : LinstrRM) (s : LstateM) : Option LstateM :=
  match i.snd with
  | .load w n =>
      match loadStruct? i.fst with
      | some (dst, base, idx) =>
          match s.getArr base w n, s.reg.getW idx 64 with
          | some arr, some vi => some ((s.setReg dst (stackGet arr vi.toNat)).nextPc)
          | _, _ => none
      | none => lsemStepCast (i.fst, none) s.reg |>.map (fun r => { s with reg := r })
  | .store w n =>
      match storeStruct? i.fst with
      | some (dst, base, idx, val) =>
          match s.getArr base w n, s.reg.getW idx 64, s.reg.getW val w with
          | some arr, some vi, some vv =>
              some ((s.setArr dst (stackSet arr vi.toNat vv)).nextPc)
          | _, _, _ => none
      | none => lsemStepCast (i.fst, none) s.reg |>.map (fun r => { s with reg := r })
  | .loadC =>
      match loadCStruct? i.fst with
      | some (dst, base, off) =>
          some ((s.setReg dst (s.lmem base (Int.ofNat off))).nextPc)
      | none => none
  | .storeC =>
      match storeCStruct? i.fst with
      | some (base, off, src) =>
          match s.reg.getW src 64 with
          | some v => some ((s.storeMemC base (Int.ofNat off) v).nextPc)
          | none => none
      | none => none
  | .reg castDescr =>
      (lsemStepCast (i.fst, castDescr) s.reg).map (fun r => { s with reg := r })

/-- The register-binding delegation collapses to a `lsemStepCast` over the
    register half, lifted across the array carrier. -/
theorem lsemStepMem_reg (wire : LinstrR) (castDescr : Option Nat) (s : LstateM) :
    lsemStepMem (wire, .reg castDescr) s =
      (lsemStepCast (wire, castDescr) s.reg).map (fun r => { s with reg := r }) := rfl

/-! ## 3. Recognizer facts: the load/store heads on the real wire forms

`loadStruct?`/`storeStruct?` recognise the real runtime-indexed `stackLoad`/
`stackStore` wire forms `opToLinstrR` emits. -/

/-- `loadStruct?` recognises the real `stackLoad` wire form
    `Lopn [.reg dst] "LOADIDX" [.arrIdx base idx (w/8)]`. -/
theorem loadStruct?_stackLoad {w n : Nat} (dst base idx : String) :
    loadStruct? (opToLinstrR (JasminOp.stackLoad w n) dst [.reg base, .reg idx])
      = some (dst, base, idx) := by
  simp only [opToLinstrR, loadStruct?, if_true]

/-- `storeStruct?` recognises the real `stackStore` wire form
    `Lopn [.reg dst] "STOREIDX" [.arrIdx base idx (w/8), .reg val]`. -/
theorem storeStruct?_stackStore {w n : Nat} (dst base idx val : String) :
    storeStruct? (opToLinstrR (JasminOp.stackStore w n) dst [.reg base, .reg idx, .reg val])
      = some (dst, base, idx, val) := by
  simp only [opToLinstrR, storeStruct?, if_true]

/-! ### 3a. The compile-time-offset load/store step reductions

The two step lemmas the `runBlock`↔`lsem` memory bridge (`RunBlockLsemAgree`)
runs against: a `.loadC`-tagged `MOVQ` reads `lmem` at the compile-time offset
into a register; a `.storeC`-tagged `MOVQ` writes a register value into `lmem` at
the compile-time offset. Both are the exact `JState.loadMem`/`JState.storeMem`
word semantics over the type-identical carrier. -/

/-- **Compile-time load step.** `lsemStepMem` of a `.loadC`-tagged
    `Lopn [.reg dst] "MOVQ" [.arr base off]` writes `s.lmem base (Int.ofNat off)`
    to `dst` and advances the pc — the `JState.loadMem` word read over the
    type-identical carrier. Never fails. -/
theorem lsemStepMem_loadC (dst base : String) (off : Nat) (s : LstateM) :
    lsemStepMem (.Lopn [.reg dst] "MOVQ" [.arr base off], .loadC) s
      = some ((s.setReg dst (s.lmem base (Int.ofNat off))).nextPc) := by
  simp only [lsemStepMem, loadCStruct?, if_true]

/-- **Compile-time store step.** Given the source register `src` reads `v` at
    width 64, `lsemStepMem` of a `.storeC`-tagged `Lopn [.arr base off] "MOVQ"
    [.reg src]` writes `v` into `lmem` at `[base + off]` and advances the pc — the
    `JState.storeMem` word write over the type-identical carrier. Never fails. -/
theorem lsemStepMem_storeC (base : String) (off : Nat) (src : String) (s : LstateM)
    (v : BitVec 64) (hv : s.reg.getW src 64 = some v) :
    lsemStepMem (.Lopn [.arr base off] "MOVQ" [.reg src], .storeC) s
      = some ((s.storeMemC base (Int.ofNat off) v).nextPc) := by
  simp only [lsemStepMem, storeCStruct?, if_true, hv]

/-! ## 4. The typed emission `straightOpsMem` and the wire/byte tie

`straightOpsMem` mirrors increment 8's `straightOpsCast`, but emits the typed
`LinstrRM` for each binding: a memory binding emits its real `opToLinstrR`
instruction paired with the array-shape descriptor `.load w n` / `.store w n`;
every other binding reuses `straightOpsCast`'s emission paired with `.reg`
carrying the (delegated) cast descriptor. The `.fst`-projection of the typed list
is *exactly* `(straightOpsCast …).map Prod.fst` — the wire/byte tie. -/

/-- Translate increment 8's typed-cast descriptor `Option Nat` into the
    register-binding `MemTag`. -/
def MemTag.ofCast : Option Nat → MemTag := MemTag.reg

/-- The typed straight-line `LinstrRM` chain a `Com` emits in the stack-memory
    fragment. A `stackLoad w n` / `stackStore w n` binding emits its **real**
    `opToLinstrR` instruction (bare `"LOADIDX"`/`"STOREIDX"`) paired with the
    array-shape descriptor; every other binding reuses `straightOpsCast`'s
    emission (its wire and cast descriptor), retagged as a `.reg` binding. -/
def straightOpsMem (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrRM
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let elem : LinstrRM :=
        match e.op with
        | .stackLoad w n => (opToLinstrR e.op (regName curDepth) src, .load w n)
        | .stackStore w n => (opToLinstrR e.op (regName curDepth) src, .store w n)
        | .castW _ w' => (opToLinstrR e.op (regName curDepth) src, .reg (some w'))
        | _ =>
          -- mirror `straightOpsCast`'s register wire (shifts get the immediate
          -- form), tagged `.reg none` (the register binding has no cast descr).
          let wire : LinstrR :=
            match e.op, src with
            | .shrImm w n, [s] => shiftLinstr "SHR" w (regName curDepth) s n
            | .shlImm w n, [s] => shiftLinstr "SHL" w (regName curDepth) s n
            | .sarImm w n, [s] => shiftLinstr "SAR" w (regName curDepth) s n
            | _, _ => opToLinstrR e.op (regName curDepth) src
          (wire, .reg none)
      elem :: straightOpsMem nArgs body (curDepth + 1)

/-- **The wire/byte tie.** The `.fst`-projection (the emitted bytes) of the typed
    stack-memory chain `straightOpsMem` is *exactly* increment 8's
    `(straightOpsCast …).map Prod.fst`. So `straightOpsMem` emits the same bytes
    as `straightOpsCast` (= `straightOpsMC` = `comToBody`'s body, by
    `straightOpsCast_wire` / `straightOps_eq_body`) — the load/store wires are the
    REAL bare `"LOADIDX"/"STOREIDX"` `opToLinstrR` output, and the array shape
    `(w, n)` lives only in the `.snd` `MemTag` component, never on the wire. -/
theorem straightOpsMem_wire (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsMem nArgs com curDepth).map Prod.fst =
      (straightOpsCast nArgs com curDepth).map Prod.fst := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      simp only [straightOpsMem, straightOpsCast, List.map_cons, ih]
      congr 1
      cases e.op <;> rfl

/-- Composed with increment 8's `straightOpsCast_wire`, the bytes equal
    `straightOpsMC` directly. -/
theorem straightOpsMem_wire_MC (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsMem nArgs com curDepth).map Prod.fst =
      straightOpsMC nArgs com curDepth := by
  rw [straightOpsMem_wire, straightOpsCast_wire]

/-! ### `straightOpsMem` unfolding on each binding head -/

theorem straightOpsMem_load {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackLoad w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackLoad w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.stackLoad w n, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.stackLoad w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.stackLoad w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .load w n)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsMem_store {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackStore w n)
      = .stackArr w n)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackStore w n)))
    (body : Com jasminDialect (.stackArr w n :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.stackStore w n, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.stackStore w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.stackStore w n, heq, args⟩ :
            Expr jasminDialect Γ (.stackArr w n))), .store w n)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-- A `castW` binding emits its real `opToLinstrR` wire tagged `.reg (some w')`. -/
theorem straightOpsMem_cast {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (body : Com jasminDialect (.reg w' :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.castW w w', heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.castW w w') (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))),
        .reg (some w'))
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsMem_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.regArith bop w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsMem_const {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.regConst w n, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .nil => rfl

theorem straightOpsMem_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.select w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.select w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsMem_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w m : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w m) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w m)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.shrImm w m, heq, args⟩ body) curDepth =
      (shiftLinstr "SHR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shrImm w m, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) m,
        .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsMem_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w m : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w m) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w m)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.shlImm w m, heq, args⟩ body) curDepth =
      (shiftLinstr "SHL" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shlImm w m, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) m,
        .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsMem_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w m : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w m) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w m)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.sarImm w m, heq, args⟩ body) curDepth =
      (shiftLinstr "SAR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.sarImm w m, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) m,
        .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsMem_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.mulhi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsMem_addLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsMem_addHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (body : Com jasminDialect (.reg 1 :: Γ) s) :
    straightOpsMem nArgs (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), .reg none)
      :: straightOpsMem nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-! ## 5. The stack-memory store-agreement invariant

`StoreAgreesM nArgs curDepth s V` says the bundled state `s` reproduces the
valuation `V` on **both** axes through the linearizer's `resolveVar` naming: the
register half `s.reg` agrees on every `.reg w'` variable (increment 8's
`StoreAgreesN`), and the array carrier `s.larr` agrees on every `.stackArr w n`
variable (reads, at shape `(w, n)`, the value `V` assigns it). -/

/-- The bundled state `s` agrees with valuation `V` at SSA depth `curDepth`: the
    register half satisfies increment 8's `StoreAgreesN`, and every in-scope array
    variable `v : Var Γ (.stackArr w n)`, resolved through `resolveVar`, reads its
    `V`-value out of the array carrier **at shape `(w, n)`** (`getArr` succeeds and
    returns it). -/
def StoreAgreesM (nArgs curDepth : Nat) {Γ : Ctxt jasminDialect}
    (s : LstateM) (V : Ctxt.Valuation Γ) : Prop :=
  StoreAgreesN nArgs curDepth s.reg V ∧
  ∀ {w n : Nat} (v : Ctxt.Var Γ (.stackArr w n)),
    s.getArr (operandName (resolveVar curDepth nArgs argName (fun _ => none) v)) w n =
      some (v.lookup V)

/-- The register half of a `StoreAgreesM`. -/
theorem StoreAgreesM.reg {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} (h : StoreAgreesM nArgs curDepth s V) :
    StoreAgreesN nArgs curDepth s.reg V := h.1

/-- The array half of a `StoreAgreesM`. -/
theorem StoreAgreesM.arr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} (h : StoreAgreesM nArgs curDepth s V)
    {w n : Nat} (v : Ctxt.Var Γ (.stackArr w n)) :
    s.getArr (operandName (resolveVar curDepth nArgs argName (fun _ => none) v)) w n =
      some (v.lookup V) := h.2 v

/-- Read an array data source `v : Var Γ (.stackArr w n)` out of the carrier from
    a `StoreAgreesM` agreement: `getArr` at the resolved name and shape `(w, n)`
    returns `v.lookup V`. The bridge that lets the load/store step read the
    operand array. -/
theorem getArr_resolveVar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} {w n : Nat} (v : Ctxt.Var Γ (.stackArr w n))
    (hagree : StoreAgreesM nArgs curDepth s V) :
    s.getArr (operandName (resolveVar curDepth nArgs argName (fun _ => none) v)) w n
      = some (v.lookup V) := hagree.arr v

/-- The `exprArgs` of a `stackLoad` binding is `[arrName, idxName]`. -/
theorem exprArgs_load {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackLoad w n) = .reg w)
    (arr : Ctxt.Var Γ (.stackArr w n)) (idx : Ctxt.Var Γ (.reg 64)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.stackLoad w n, heq, .cons arr (.cons idx .nil)⟩ :
        Expr jasminDialect Γ (.reg w))
      = [resolveVar curDepth nArgs argName (fun _ => none) arr,
         resolveVar curDepth nArgs argName (fun _ => none) idx] := rfl

/-- The `exprArgs` of a `stackStore` binding is `[arrName, idxName, valName]`. -/
theorem exprArgs_store {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackStore w n)
      = .stackArr w n)
    (arr : Ctxt.Var Γ (.stackArr w n)) (idx : Ctxt.Var Γ (.reg 64))
    (val : Ctxt.Var Γ (.reg w)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.stackStore w n, heq, .cons arr (.cons idx (.cons val .nil))⟩ :
        Expr jasminDialect Γ (.stackArr w n))
      = [resolveVar curDepth nArgs argName (fun _ => none) arr,
         resolveVar curDepth nArgs argName (fun _ => none) idx,
         resolveVar curDepth nArgs argName (fun _ => none) val] := rfl

/-! ## 6. Per-binding agreement for `stackLoad` / `stackStore` -/

/-- **`stackLoad` per-binding step.** From a bundled store agreeing with `V`, the
    typed load instruction `(opToLinstrR (stackLoad w n) …, .load w n)`
    `lsemStepMem`s to the state writing the binding's denotation
    `(stackLoad w n).denote V = stackGet (arr.lookup V) (idx.lookup V).toNat` to
    `regName curDepth`. The source array `arr` is read from the array carrier at
    shape `(w, n)` (recovered from the typed `.load` descriptor); the index `idx`
    from the register half at width 64. Faithful to `eval_instr`'s `Laset` load. -/
theorem lsemStepMem_load {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackLoad w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackLoad w n)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.stackLoad w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.stackLoad w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))),
          .load w n)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.stackLoad w n, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  match args with
  | .cons arr (.cons idx .nil) =>
    have harr : st.getArr
        (operandName (resolveVar curDepth nArgs argName (fun _ => none) arr)) w n
        = some (arr.lookup V) := getArr_resolveVar arr hagree
    have hidx : st.reg.getW
        (operandName (resolveVar curDepth nArgs argName (fun _ => none) idx)) 64
        = some (idx.lookup V) := by
      have := hagree.reg idx
      rwa [evalOperandN_resolveVar] at this
    rw [exprArgs_load heq arr idx, resolveVar_isReg arr, resolveVar_isReg idx]
    simp only [lsemStepMem, opToLinstrR, loadStruct?, if_true, harr, hidx]
    rfl

/-- **`stackStore` per-binding step.** From a bundled store agreeing with `V`, the
    typed store instruction `(opToLinstrR (stackStore w n) …, .store w n)`
    `lsemStepMem`s to the state writing the binding's denotation
    `(stackStore w n).denote V = stackSet (arr.lookup V) (idx.lookup V).toNat
    (val.lookup V)` (the **new array**) to the destination **array** slot
    `regName curDepth`. The source array is read at shape `(w, n)`, the index at
    width 64, the value at width `w`. Faithful to `eval_instr`'s `Laset` store. -/
theorem lsemStepMem_store {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackStore w n)
      = .stackArr w n)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackStore w n)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.stackStore w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.stackStore w n, heq, args⟩ :
              Expr jasminDialect Γ (.stackArr w n))),
          .store w n)
        st =
      some ((st.setArr (regName curDepth)
        ((⟨JasminOp.stackStore w n, heq, args⟩ :
          Expr jasminDialect Γ (.stackArr w n)).denote V)).nextPc) := by
  match args with
  | .cons arr (.cons idx (.cons val .nil)) =>
    have harr : st.getArr
        (operandName (resolveVar curDepth nArgs argName (fun _ => none) arr)) w n
        = some (arr.lookup V) := getArr_resolveVar arr hagree
    have hidx : st.reg.getW
        (operandName (resolveVar curDepth nArgs argName (fun _ => none) idx)) 64
        = some (idx.lookup V) := by
      have := hagree.reg idx
      rwa [evalOperandN_resolveVar] at this
    have hval : st.reg.getW
        (operandName (resolveVar curDepth nArgs argName (fun _ => none) val)) w
        = some (val.lookup V) := by
      have := hagree.reg val
      rwa [evalOperandN_resolveVar] at this
    rw [exprArgs_store heq arr idx val, resolveVar_isReg arr, resolveVar_isReg idx,
      resolveVar_isReg val]
    simp only [lsemStepMem, opToLinstrR, storeStruct?, if_true, harr, hidx, hval]
    rfl

/-! ### The register-delegated bindings over `LstateM`

Each increment-8 register binding `lsemStepMem`s through `lsemStepMem_reg` to the
register-half `lsemStepCast` step, lifted across the (unchanged) array carrier.
The increment-8 `lsemStepCast_*` lemmas supply the register-half value. -/

/-- Lift an increment-8 register step to `LstateM`: if `lsemStepCast (wire, descr)
    st.reg` writes `regName curDepth := value` (and bumps pc), then
    `lsemStepMem (wire, .reg descr) st` writes `regName curDepth := value` on the
    `LstateM` register half (array carrier untouched). -/
theorem lsemStepMem_of_reg {curDepth : Nat} {st : LstateM} {wire : LinstrR}
    {descr : Option Nat} {w : Nat} (value : BitVec w)
    (h : lsemStepCast (wire, descr) st.reg
      = some ((st.reg.setReg (regName curDepth) value).nextPc)) :
    lsemStepMem (wire, .reg descr) st
      = some ((st.setReg (regName curDepth) value).nextPc) := by
  rw [lsemStepMem_reg, h, Option.map_some]
  rfl

theorem lsemStepMem_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_var bop heq args hagree.reg)

theorem lsemStepMem_const {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w : Nat} (n : Nat) (hwn : w = 64 ∨ w = 32)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_const (V := V) n hwn heq args hagree.reg)

theorem lsemStepMem_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.select w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.select w, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_sel heq args hagree.reg)

theorem lsemStepMem_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w m : Nat} (hm : m < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w m) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w m)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (shiftLinstr "SHR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shrImm w m, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) m, .reg none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shrImm w m, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_shr hm heq args hagree.reg)

theorem lsemStepMem_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w m : Nat} (hm : m < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w m) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w m)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (shiftLinstr "SHL" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shlImm w m, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) m, .reg none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shlImm w m, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_shl hm heq args hagree.reg)

theorem lsemStepMem_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w m : Nat} (hm : m < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w m) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w m)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (shiftLinstr "SAR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.sarImm w m, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) m, .reg none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.sarImm w m, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_sar hm heq args hagree.reg)

theorem lsemStepMem_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.mulhi w, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_mulhi heq args hagree.reg)

theorem lsemStepMem_addLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .reg none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryLo w, heq, args⟩ :
          Expr jasminDialect Γ (.reg w)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_addLo heq args hagree.reg)

theorem lsemStepMem_addHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), .reg none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryHi w, heq, args⟩ :
          Expr jasminDialect Γ (.reg 1)).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_addHi heq args hagree.reg)

theorem lsemStepMem_cast {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateM} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (hagree : StoreAgreesM nArgs curDepth st V) :
    lsemStepMem
        (opToLinstrR (JasminOp.castW w w') (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))),
          .reg (some w'))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.castW w w', heq, args⟩ :
          Expr jasminDialect Γ (.reg w')).denote V)).nextPc) :=
  lsemStepMem_of_reg _ (lsemStepCast_cast heq args hagree.reg)

/-! ## 7. Invariant preservation on both write kinds

A register-writing binding (every delegated head, and `stackLoad`) preserves
`StoreAgreesM` by the increment-8 `StoreAgreesN.step` on the register half, with
the array half untouched (the array carrier is unchanged, and the freshly bound
`.here` has a register type). A store binding (`stackStore`) writes the new array
to the array carrier and preserves agreement symmetrically. -/

/-- The resolved name of an earlier array variable `v'` (resolved slot
    `< curDepth`) differs from `regName curDepth`, so writing the fresh array slot
    leaves its `getArr` unchanged. Array analogue of
    `evalOperandN_setReg_resolveVar`. -/
theorem getArr_setArr_resolveVar {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect}
    {w' n' : Nat} (v : Ctxt.Var Γ (.stackArr w' n')) (s : LstateM) {w n : Nat}
    (arr : Fin n → BitVec w) (hlt : varIndex v < curDepth) :
    (s.setArr (regName curDepth) arr).getArr
        (operandName (resolveVar curDepth nArgs argName (fun _ => none) v)) w' n' =
      s.getArr (operandName (resolveVar curDepth nArgs argName (fun _ => none) v)) w' n' := by
  simp only [resolveVar, operandName]
  set slot := curDepth - 1 - varIndex v with hslot
  have hslt : slot < curDepth := by omega
  by_cases hsa : slot < nArgs
  · simp only [hsa, if_true]
    rw [LstateM.getArr_setArr_other]
    exact fun he => (JasminLsemSimulation.regName_ne_argName curDepth slot) he.symm
  · simp only [hsa, if_false]
    rw [LstateM.getArr_setArr_other]
    exact fun he => (JasminLsemSimulation.regName_ne (by omega)) he.symm

/-- **Invariant preservation — register write.** Writing a `.reg w` value to
    `regName curDepth` (every delegated head and `stackLoad`) and advancing the pc
    preserves `StoreAgreesM`, extending the valuation with the register value. The
    register half is increment 8's `StoreAgreesN.step`; the array half is
    unchanged (carrier untouched; the new `.here` is a register binder). -/
theorem StoreAgreesM.stepReg {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} {w : Nat} (val : BitVec w)
    (hlen : Γ.length = curDepth) (harg : nArgs ≤ curDepth)
    (hagree : StoreAgreesM nArgs curDepth s V) :
    StoreAgreesM nArgs (curDepth + 1)
      ((s.setReg (regName curDepth) val).nextPc)
      (V.extend (Γ := Γ) (t := .reg w) val) := by
  refine ⟨?_, ?_⟩
  · -- register half: the increment-8 step
    show StoreAgreesN nArgs (curDepth + 1) ((s.reg.setReg (regName curDepth) val).nextPc)
      (V.extend (Γ := Γ) (t := .reg w) val)
    exact StoreAgreesN.step (s := s.reg) (V := V) val hlen harg hagree.reg
  · -- array half: a `.reg w :: Γ` array var is `.there v'`; carrier untouched
    intro w' n' v
    cases v with
    | there v' =>
        rw [JasminLsemSimulation.resolveVar_there]
        simp only [LstateM.getArr_nextPc, LstateM.getArr_setReg]
        exact hagree.arr v'

/-- **Invariant preservation — array write.** Writing a `.stackArr w n` value (a
    `stackStore` result) to `regName curDepth` and advancing the pc preserves
    `StoreAgreesM`. The register half is unchanged (carrier untouched; the new
    `.here` is an array binder, not a register), the array half extends. -/
theorem StoreAgreesM.stepArr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} {w n : Nat} (arr : Fin n → BitVec w)
    (hlen : Γ.length = curDepth) (harg : nArgs ≤ curDepth)
    (hagree : StoreAgreesM nArgs curDepth s V) :
    StoreAgreesM nArgs (curDepth + 1)
      ((s.setArr (regName curDepth) arr).nextPc)
      (V.extend (Γ := Γ) (t := .stackArr w n) arr) := by
  refine ⟨?_, ?_⟩
  · -- register half: a `.stackArr w n :: Γ` register var is `.there v'`; carrier untouched
    intro w' v
    cases v with
    | there v' =>
        rw [JasminLsemSimulation.resolveVar_there]
        show evalOperandN (((s.setArr (regName curDepth) arr).nextPc).reg) w'
            (resolveVar curDepth nArgs argName (fun _ => none) v') = _
        simp only [LstateM.reg_nextPc, LstateM.reg_setArr, evalOperandN_nextPc]
        exact hagree.reg v'
  · intro w' n' v
    cases v with
    | here =>
        simp only [resolveVar, varIndex]
        have hslot : curDepth + 1 - 1 - 0 = curDepth := by omega
        rw [hslot]
        have hsa : ¬ curDepth < nArgs := by omega
        simp only [hsa, if_false, operandName, LstateM.getArr_nextPc]
        -- `.here : Var (.stackArr w n :: Γ) (.stackArr w' n')` forces `(w', n') = (w, n)`
        rw [LstateM.getArr_setArr_same]
        rfl
    | there v' =>
        rw [JasminLsemSimulation.resolveVar_there]
        have hlt : varIndex v' < curDepth := by
          have := JasminLsemSimulation.varIndex_lt v'; omega
        simp only [LstateM.getArr_nextPc]
        rw [getArr_setArr_resolveVar v' s arr hlt]
        exact hagree.arr v'

/-! ## 8. `lsemStraightMem` / leakage over the typed step -/

/-- Typed straight-line execution: the sequential fold of `lsemStepMem`. -/
def lsemStraightMem : List LinstrRM → LstateM → Option LstateM
  | [], s => some s
  | i :: is, s =>
      match lsemStepMem i s with
      | some s' => lsemStraightMem is s'
      | none => none

@[simp] theorem lsemStraightMem_nil (s : LstateM) : lsemStraightMem [] s = some s := rfl

@[simp] theorem lsemStraightMem_cons (i : LinstrRM) (is : List LinstrRM) (s : LstateM) :
    lsemStraightMem (i :: is) s =
      (match lsemStepMem i s with
        | some s' => lsemStraightMem is s'
        | none => none) := rfl

/-- Typed leakage trace: the leak of each typed instruction is the leak of its
    **wire** (`linstrLeak i.fst`), so the array shape `(w, n)` never enters the
    attacker's view (it is the model's typed environment). For a `LOADIDX`/
    `STOREIDX` the wire leaks the address structure (`base`, `idx`-register name,
    stride) via `idxShape`, never the loaded/stored value — the crypto CT model.
    Faithful to the emit path: the bytes are `i.fst`, so the leak is of `i.fst`. -/
def lsemLeakMem : List LinstrRM → LstateM → List JasminLsemRobust.LLeak
  | [], _ => []
  | i :: is, s =>
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepMem i s with
          | some s' => lsemLeakMem is s'
          | none => [])

@[simp] theorem lsemLeakMem_nil (s : LstateM) : lsemLeakMem [] s = [] := rfl

@[simp] theorem lsemLeakMem_cons (i : LinstrRM) (is : List LinstrRM) (s : LstateM) :
    lsemLeakMem (i :: is) s =
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepMem i s with
          | some s' => lsemLeakMem is s'
          | none => []) := rfl

/-! ## 9. The stack-memory source fragment `ScalarMemN` -/

/-- The straight-line **stack-memory-fragment** scalar source: every binding is an
    increment-8 register head (`regArith`/`select`/shifts/the trio/`castW`) or a
    memory op (`stackLoad`/`stackStore`). This subsumes increment 8's
    `ScalarCastN`. The `load` arm binds a `.reg w`; the `store` arm binds a
    `.stackArr w n` — the first array-valued binder. The whole program still
    returns a register `.reg t`. -/
inductive ScalarMemN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
      ScalarMemN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | const {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (n : Nat)
      (hwn : w = 64 ∨ w = 32)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.regConst w n, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.select w, heq, args⟩ body)
  | shr {Γ : Ctxt jasminDialect} {s : JasminTy} {w m : Nat} (hm : m < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w m) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w m)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.shrImm w m, heq, args⟩ body)
  | shl {Γ : Ctxt jasminDialect} {s : JasminTy} {w m : Nat} (hm : m < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w m) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w m)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.shlImm w m, heq, args⟩ body)
  | sar {Γ : Ctxt jasminDialect} {s : JasminTy} {w m : Nat} (hm : m < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w m) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w m)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.sarImm w m, heq, args⟩ body)
  | mulhi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.mulhi w, heq, args⟩ body)
  | addLo {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body)
  | addHi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
      {body : Com jasminDialect (.reg 1 :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body)
  | cast {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.castW w w', heq, args⟩ body)
  | load {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackLoad w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.stackLoad w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.stackLoad w n, heq, args⟩ body)
  | store {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackStore w n)
        = .stackArr w n)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.stackStore w n)))
      {body : Com jasminDialect (.stackArr w n :: Γ) s}
      (hbody : ScalarMemN body) :
      ScalarMemN (.var ⟨JasminOp.stackStore w n, heq, args⟩ body)

/-- `ScalarMemN` subsumes `ScalarCastN`: every increment-8 width-cast-fragment
    program is in the stack-memory fragment. So the increment-8 results are
    special cases. -/
theorem ScalarMemN.of_scalarCastN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : ScalarCastN com) : ScalarMemN com := by
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

/-- A `ScalarMemN` program returns a register. -/
theorem ScalarMemN.ret_reg {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) : ∃ w, t = .reg w := by
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
  | load _ _ _ ih => exact ih
  | store _ _ _ ih => exact ih

/-! ## 10. The core stack-memory straight-line simulation

Same induction skeleton as increment 8's `lsemStraightCast_straightOps`, with the
new `load`/`store` arms closed by `lsemStepMem_load`/`lsemStepMem_store` +
`StoreAgreesM.stepReg`/`StoreAgreesM.stepArr`, and the ten delegated arms by the
`lsemStepMem_*` (each lifting `lsemStepCast_*` over the register half through
`lsemStepMem_of_reg`). The `store` arm steps a `.stackArr w n` binding, so the
binding-extended valuation is over `.stackArr w n :: Γ` — `StoreAgreesM.stepArr`
absorbs the array-valued binding; the body still returns a register. -/

/-- **Core simulation (parametrized by an agreeing start state), stack-memory
    fragment.** From any bundled store `st` agreeing with `V` at depth
    `curDepth`, running the stack-memory-fragment `.var`-chain `straightOpsMem`
    succeeds, lands in a store agreeing with the binding-extended valuation, and
    reads `Com.denote com V` (transported to its return width) at the return
    register (on the register half). -/
theorem lsemStraightMem_straightOps {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateM} {V : Ctxt.Valuation Γ}
      {w : Nat} (hw : t = .reg w),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesM nArgs curDepth st V →
      ∃ st', lsemStraightMem (straightOpsMem nArgs com curDepth) st = some st' ∧
        evalOperandN st'.reg w (.reg (comRetReg nArgs argName com curDepth)) =
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
      exact hagree.reg v
  | var bop heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_var (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        bop heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_var, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_const (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        n hwn heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_const, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sel heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_sel (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_sel, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shr hm heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_shr (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_shr, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shl hm heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_shl (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_shl, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sar hm heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_sar (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_sar, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | mulhi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_mulhi (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.mulhi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_mulhi, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addLo heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_addLo (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.addCarryLo _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_addLo, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addHi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_addHi (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.addCarryHi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_addHi, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | cast heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_cast (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.castW _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_cast, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | load heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_load (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.stackLoad _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_load, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | store heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMem_store (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' := StoreAgreesM.stepArr
        ((⟨JasminOp.stackStore _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMem_store, lsemStraightMem_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret

/-! ## 11. `encodeM`/`decodeM` and the top-level faithfulness statement

`encodeM` places the argument valuation into the bundled state: register args go
into the register half (via increment 2's `encodeAuxN`), array args into the
array carrier, each at its own shape. -/

/-- Encode the array-typed arguments of a valuation into the array carrier,
    placing the value at de Bruijn index `i` at `argName (Γ.length - 1 - i)`,
    tagged with its own shape. Register heads are skipped here (they go into the
    register half). -/
def encodeArrAuxM : {Γ : Ctxt jasminDialect} → Ctxt.Valuation Γ → LstateM → LstateM
  | [], _, st => st
  | (.stackArr w' n') :: rest, .cons hd tl, st =>
      (encodeArrAuxM tl st).setArr (argName rest.length)
        (hd : Fin n' → BitVec w')
  | _ :: _, .cons _ tl, st => encodeArrAuxM tl st

/-- The canonical encoding of an argument valuation into a fresh bundled state:
    register args in the register half (`encodeN`), array args in the array
    carrier (`encodeArrAuxM`). -/
def encodeM {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) : LstateM :=
  encodeArrAuxM V { reg := encodeN V }

/-- Decode a register from the bundled state at width `w`: read it back via the
    register half's `getW`. Paired with `comRetReg`, this reads the result the
    body computed. -/
def decodeM (st : LstateM) (obsName : String) (w : Nat) : Option (BitVec w) :=
  st.reg.getW obsName w

/-- The array encoder leaves the register half untouched. -/
theorem encodeArrAuxM_reg {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ)
    (st : LstateM) : (encodeArrAuxM V st).reg = st.reg := by
  induction V with
  | nil => rfl
  | cons hd tl ih =>
      rename_i τ rest
      cases τ with
      | reg w' => simpa [encodeArrAuxM] using ih
      | stackArr w' n' => simpa [encodeArrAuxM, LstateM.setArr] using ih
      | inlineInt => simpa [encodeArrAuxM] using ih
      | bool => simpa [encodeArrAuxM] using ih

/-- The array encoder reads back each array variable at its `argName` slot, at its
    own shape: the value at de Bruijn index `varIndex v` (type `.stackArr w' n'`)
    is stored at `argName (Γ.length - 1 - varIndex v)` with shape `(w', n')`. -/
theorem encodeArrAuxM_lookup {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ)
    (st : LstateM) {τ : JasminTy} (v : Ctxt.Var Γ τ) {w' n' : Nat}
    (h : τ = .stackArr w' n') :
    (encodeArrAuxM V st).getArr (argName (Γ.length - 1 - varIndex v)) w' n' =
      some (h ▸ v.lookup V : ⟦(JasminTy.stackArr w' n')⟧) := by
  induction v with
  | here =>
      rename_i Γ' σ
      subst h
      cases V with
      | cons hd tl =>
        show ((encodeArrAuxM tl st).setArr (argName (List.length Γ')) (hd : Fin n' → BitVec w')).getArr
              (argName (List.length Γ' + 1 - 1 - 0)) w' n' = some hd
        have hslot : List.length Γ' + 1 - 1 - 0 = List.length Γ' := by omega
        rw [hslot, LstateM.getArr_setArr_same]
  | there v' ih =>
      rename_i Γ' tt σ
      subst h
      have heq2 : List.length Γ' + 1 - 1 - (varIndex v' + 1)
          = List.length Γ' - 1 - varIndex v' := by omega
      cases V with
      | cons hd tl =>
        have hlt : varIndex v' < List.length Γ' := JasminLsemSimulation.varIndex_lt v'
        cases σ with
        | stackArr wσ nσ =>
            show ((encodeArrAuxM tl st).setArr (argName (List.length Γ')) (hd : Fin nσ → BitVec wσ)).getArr
                  (argName (List.length Γ' + 1 - 1 - (varIndex v' + 1))) w' n' = some (v'.lookup tl)
            rw [LstateM.getArr_setArr_other _ _ _ _ _ _
              (JasminLsemSimulation.argName_ne (by omega)), heq2]
            exact ih tl rfl
        | reg wσ =>
            show (encodeArrAuxM tl st).getArr
                  (argName (List.length Γ' + 1 - 1 - (varIndex v' + 1))) w' n' = some (v'.lookup tl)
            rw [heq2]; exact ih tl rfl
        | inlineInt =>
            show (encodeArrAuxM tl st).getArr
                  (argName (List.length Γ' + 1 - 1 - (varIndex v' + 1))) w' n' = some (v'.lookup tl)
            rw [heq2]; exact ih tl rfl
        | bool =>
            show (encodeArrAuxM tl st).getArr
                  (argName (List.length Γ' + 1 - 1 - (varIndex v' + 1))) w' n' = some (v'.lookup tl)
            rw [heq2]; exact ih tl rfl

/-- **`encodeM` establishes the start-state agreement.** The encoded bundled
    store agrees with the valuation at the start depth `curDepth = nArgs =
    Γ.length`, on both axes. The base case of the simulation induction. -/
theorem encodeM_StoreAgreesM {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    StoreAgreesM Γ.length Γ.length (encodeM V) V := by
  refine ⟨?_, ?_⟩
  · -- register half: `encodeM`'s register half is `encodeN V`
    have hreg : (encodeM V).reg = encodeN V := encodeArrAuxM_reg V _
    rw [show StoreAgreesN Γ.length Γ.length (encodeM V).reg V
        = StoreAgreesN Γ.length Γ.length (encodeN V) V from by rw [hreg]]
    exact encodeN_StoreAgreesN V
  · -- array half
    intro w' n' v
    have hslot : Γ.length - 1 - varIndex v < Γ.length := by
      have := JasminLsemSimulation.varIndex_lt v; omega
    simp only [resolveVar, hslot, if_true, operandName, encodeM]
    exact encodeArrAuxM_lookup V _ v rfl

/-! ## 12. Faithfulness, leak state-independence, and the capstone -/

/-- **Straight-line linearizer simulation, stack-memory fragment.** Running the
    stack-memory-fragment `.var`-chain `straightOpsMem` from the encoded argument
    valuation and decoding the result register at width `w` equals the source
    program's `Com.denote`. -/
theorem comToLprog_lsemMem {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightMem (straightOpsMem Γ.length com Γ.length) (encodeM V) = some st' ∧
      decodeM st' (comRetReg Γ.length argName com Γ.length) w =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraightMem_straightOps hcom hw (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeM V) (V := V) rfl le_rfl (encodeM_StoreAgreesM V)
  exact ⟨st', hrun, by simpa only [decodeM, evalOperandN] using hret⟩

/-- **Faithfulness (packaged), stack-memory fragment.** -/
theorem comToLprog_faithful_mem {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightMem (straightOpsMem Γ.length com Γ.length) (encodeM V)).bind
        (fun st' => decodeM st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemMem hcom hw V
  rw [hrun, Option.bind_some, hdec]

/-- **Leak state-independence, stack-memory fragment (unconditional).** The
    leakage trace of the stack-memory-fragment `.var`-chain is the **same from any
    two initial states agreeing with the same valuation**: every head — register
    (`regArith`/`select`/shifts/the trio/`castW`) or memory
    (`stackLoad`/`stackStore`) — has a `linstrLeak` reading only the wire syntax.
    For a memory op that is the address structure `.arrIdx base idx scale` (base
    name + index-register *name* + stride), never a register value nor the array
    length `n`; the loaded/stored value never appears. Both states take the
    `some` branch (the step succeeds from any agreeing store) and the tails (still
    agreeing with the extended valuation) close by the IH. -/
theorem lsemLeakMem_straightOps_state_independent {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) :
    ∀ {nArgs curDepth : Nat} {V₁ V₂ : Ctxt.Valuation Γ} (s₁ s₂ : LstateM),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesM nArgs curDepth s₁ V₁ → StoreAgreesM nArgs curDepth s₂ V₂ →
      lsemLeakMem (straightOpsMem nArgs com curDepth) s₁ =
        lsemLeakMem (straightOpsMem nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v => intro nArgs curDepth V₁ V₂ s₁ s₂ _ _ _ _; rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_var (V := V₁) bop heq args hag1
      have hstep2 := lsemStepMem_var (V := V₂) bop heq args hag2
      rw [straightOpsMem_var]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_const (V := V₁) n hwn heq args hag1
      have hstep2 := lsemStepMem_const (V := V₂) n hwn heq args hag2
      rw [straightOpsMem_const]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | sel heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_sel (V := V₁) heq args hag1
      have hstep2 := lsemStepMem_sel (V := V₂) heq args hag2
      rw [straightOpsMem_sel]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | shr hm heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_shr (V := V₁) hm heq args hag1
      have hstep2 := lsemStepMem_shr (V := V₂) hm heq args hag2
      rw [straightOpsMem_shr]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | shl hm heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_shl (V := V₁) hm heq args hag1
      have hstep2 := lsemStepMem_shl (V := V₂) hm heq args hag2
      rw [straightOpsMem_shl]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | sar hm heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_sar (V := V₁) hm heq args hag1
      have hstep2 := lsemStepMem_sar (V := V₂) hm heq args hag2
      rw [straightOpsMem_sar]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | mulhi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_mulhi (V := V₁) heq args hag1
      have hstep2 := lsemStepMem_mulhi (V := V₂) heq args hag2
      rw [straightOpsMem_mulhi]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | addLo heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_addLo (V := V₁) heq args hag1
      have hstep2 := lsemStepMem_addLo (V := V₂) heq args hag2
      rw [straightOpsMem_addLo]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | addHi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_addHi (V := V₁) heq args hag1
      have hstep2 := lsemStepMem_addHi (V := V₂) heq args hag2
      rw [straightOpsMem_addHi]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | cast heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_cast (V := V₁) heq args hag1
      have hstep2 := lsemStepMem_cast (V := V₂) heq args hag2
      rw [straightOpsMem_cast]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | load heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_load (V := V₁) heq args hag1
      have hstep2 := lsemStepMem_load (V := V₂) heq args hag2
      rw [straightOpsMem_load]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepReg _ hlen harg hag1) (StoreAgreesM.stepReg _ hlen harg hag2)
  | store heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMem_store (V := V₁) heq args hag1
      have hstep2 := lsemStepMem_store (V := V₂) heq args hag2
      rw [straightOpsMem_store]
      simp only [lsemLeakMem_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesM.stepArr _ hlen harg hag1) (StoreAgreesM.stepArr _ hlen harg hag2)

/-! ## 13. The unconditional stack-memory capstone: `correct ∧ robust` -/

/-- **Unconditional `correct ∧ robust` for the stack-memory fragment
    (`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
    addCarryHi ∪ castW ∪ stackLoad ∪ stackStore`).** For a stack-memory-fragment
    scalar straight-line `Com` with return type `.reg w`:

    1. *(correct, §12)* running the linearizer-emitted `.var`-chain
       `straightOpsMem` on the encoded argument valuation and decoding the result
       register at width `w` yields exactly `com.denote V`; and
    2. *(robust / constant-time, §12)* the leakage trace `lsemLeakMem
       (straightOpsMem …)` is the **same from the encodings of any two input
       valuations** — the attacker's view is a function of the emitted instruction
       list alone, never of a register value, never of a loaded/stored memory
       value, and never of the array length `n` (which lives only in the typed
       `MemTag` `.snd` component).

    This is **unconditional**: no IR→x86 faithfulness hypothesis, no
    `jasminc_preserves_ct`. Both conjuncts concern one and the same object — the
    stack-memory linearizer-emitted straight-line body run by `lsemStraightMem`
    (functional) and observed by `lsemLeakMem` (CT). The memory ops are read over
    the REAL bare role mnemonics `"LOADIDX"/"STOREIDX"` `opToLinstrR` already
    emits (`straightOpsMem_wire`: the `.fst`-projection is exactly
    `(straightOpsCast …).map Prod.fst = straightOpsMC`), so the emitted **bytes are
    unchanged**; the array shape `(w, n)` is the typed-step descriptor (the
    `sarr len` jasmin's `read_linear` reconstructs), never a wire annotation. The
    first capstone covering `stackLoad`/`stackStore` — the **first memory ops**:
    they read/write the array carrier, an orthogonal state axis.

    **Constant-time discipline (the public-index requirement).** This is the
    *syntactic* CT model: the wire's `.arrIdx base idx scale` leaks the **address
    structure** (base name, index-register *name*, stride) via `idxShape`, never
    the value — *addresses leak, values don't*. So the leak trace is
    state-independent unconditionally. The genuine CT discipline the model encodes
    is that the index register's *value* be **public** (data-independent, in
    range): a SECRET-dependent index would, on real silicon, leak the addressed
    cell through cache/timing — secret-indexed loads are genuinely **not**
    constant-time. That residual is outside this syntactic leak model and is
    flagged here, not hidden; the in-range/total addressing (`stackGet`/`stackSet`
    reduce `% n`) makes the functional placement sound for any index. The
    `lsem→bytes` encoder and Sail tables remain the declared trusted base. -/
theorem owned_lsem_correct_and_robust_mem {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (§12)
    ((lsemStraightMem (straightOpsMem Γ.length com Γ.length) (encodeM V)).bind
        (fun st' => decodeM st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§12)
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakMem (straightOpsMem Γ.length com Γ.length) (encodeM V₁) =
        lsemLeakMem (straightOpsMem Γ.length com Γ.length) (encodeM V₂)) := by
  refine ⟨comToLprog_faithful_mem hcom hw V, ?_⟩
  intro V₁ V₂
  exact lsemLeakMem_straightOps_state_independent hcom (encodeM V₁) (encodeM V₂)
    rfl le_rfl (encodeM_StoreAgreesM V₁) (encodeM_StoreAgreesM V₂)

/-! ## 14. Tie-back: the increment-8 width-cast fragment is subsumed

`ScalarMemN.of_scalarCastN` shows every `ScalarCastN` program is a `ScalarMemN`
program. The stack-memory capstone therefore specialises to the width-cast
fragment (and, transitively, to the mul/carry / shift / width-mixed / `regArith`
fragments of increments 2–8). -/

/-- Every increment-8 width-cast-fragment program satisfies the stack-memory
    capstone: the increment-8 results are special cases of the increment-9 ones.
    (Bridged through `LstateM`'s register half; the array carrier is inert for a
    register-only program.) -/
theorem owned_lsem_correct_and_robust_mem_of_scalarCastN {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarCastN com)
    {w : Nat} (hw : t = .reg w) (V : Ctxt.Valuation Γ) :
    ((lsemStraightMem (straightOpsMem Γ.length com Γ.length) (encodeM V)).bind
        (fun st' => decodeM st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakMem (straightOpsMem Γ.length com Γ.length) (encodeM V₁) =
        lsemLeakMem (straightOpsMem Γ.length com Γ.length) (encodeM V₂)) :=
  owned_lsem_correct_and_robust_mem (ScalarMemN.of_scalarCastN hcom) hw V

/-! ## 15. Strengthened simulation: the final store agreement + the write frame

`lsemStraightMem_straightOps` (§10) reads only the RETURN register off the final
store. The loop lowering (a `chain ++ writeback` body threaded across back-edge
trips) additionally needs (a) the **final store agreement** — after the chain,
every in-scope register/array slot still reads the (binding-extended) valuation,
so the writeback can re-establish the next trip's encoded state — and (b) a
**write frame** — the chain writes only the fresh `regName`-slots at depth
`≥ curDepth`, so the loop counter and every argument slot survive it. This
section ADDS a variant exposing both; the §10 statement is byte-for-byte
unchanged (its importers are untouched). -/

/-- Number of `.var` bindings of a `Com` (= the emitted chain length). -/
def comLen : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => comLen body + 1

/-- The binding-extended context a `Com` bottoms out in (its `.ret`'s context). -/
def comOutCtx : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t →
    Ctxt jasminDialect
  | Γ, _, .ret _ => Γ
  | _, _, .var _ body => comOutCtx body

/-- The binding-extended valuation at the `.ret`: fold every binding's
    denotation onto the argument valuation (the `denoteLets` of the mainline
    `Com` API, local to this backend). -/
def comDenoteLets : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (com : Com jasminDialect Γ t) → Ctxt.Valuation Γ → Ctxt.Valuation (comOutCtx com)
  | _, _, .ret _, V => V
  | _, _, .var e body, V => comDenoteLets body (V.extend (e.denote V))

/-- **The write frame**: `s'` reads identically to `s` at every register and
    every array slot whose name avoids the fresh `regName`-block at depth `≥ d`.
    What an emitted chain rooted at depth `d` is allowed to touch. -/
def WriteFrame (d : Nat) (s s' : LstateM) : Prop :=
  (∀ (r : String) (w : Nat), (∀ k, d ≤ k → r ≠ regName k) →
      s'.reg.getW r w = s.reg.getW r w)
  ∧ (∀ (r : String) (w n : Nat), (∀ k, d ≤ k → r ≠ regName k) →
      s'.getArr r w n = s.getArr r w n)

/-- The reflexive frame. -/
theorem WriteFrame.refl (d : Nat) (s : LstateM) : WriteFrame d s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- Absorb one register write at the block root `regName d` into the frame:
    a `WriteFrame (d+1)` from the written state is a `WriteFrame d` from the
    unwritten one. -/
theorem WriteFrame.stepReg {d : Nat} {st st' : LstateM} {w : Nat} (val : BitVec w)
    (h : WriteFrame (d + 1) ((st.setReg (regName d) val).nextPc) st') :
    WriteFrame d st st' := by
  refine ⟨?_, ?_⟩
  · intro r w'' hr
    rw [h.1 r w'' (fun k hk => hr k (by omega))]
    show ((st.reg.setReg (regName d) val).nextPc).getW r w'' = st.reg.getW r w''
    rw [LstateN.getW_nextPc]
    exact LstateN.getW_setReg_other _ _ _ _ _ (hr d le_rfl)
  · intro r w'' n'' hr
    rw [h.2 r w'' n'' (fun k hk => hr k (by omega))]
    rw [LstateM.getArr_nextPc, LstateM.getArr_setReg]

/-- Absorb one array write at the block root `regName d` into the frame. -/
theorem WriteFrame.stepArr {d : Nat} {st st' : LstateM} {w n : Nat}
    (arr : Fin n → BitVec w)
    (h : WriteFrame (d + 1) ((st.setArr (regName d) arr).nextPc) st') :
    WriteFrame d st st' := by
  refine ⟨?_, ?_⟩
  · intro r w'' hr
    rw [h.1 r w'' (fun k hk => hr k (by omega))]
    show (((st.setArr (regName d) arr).nextPc).reg).getW r w'' = st.reg.getW r w''
    rw [LstateM.reg_nextPc, LstateM.reg_setArr, LstateN.getW_nextPc]
  · intro r w'' n'' hr
    rw [h.2 r w'' n'' (fun k hk => hr k (by omega))]
    rw [LstateM.getArr_nextPc]
    exact LstateM.getArr_setArr_other _ _ _ _ _ _ (hr d le_rfl)

/-- The name an in-scope variable resolves to (an `argName` or an earlier
    `regName` slot) is never a fresh-block name `regName k`, `k ≥ curDepth`. -/
theorem resolveVar_operandName_ne_regName {curDepth nArgs : Nat}
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ)
    (hv : varIndex v < curDepth) (k : Nat) (hk : curDepth ≤ k) :
    operandName (resolveVar curDepth nArgs argName (fun _ => none) v) ≠ regName k := by
  simp only [resolveVar, operandName]
  by_cases hsa : curDepth - 1 - varIndex v < nArgs
  · simp only [hsa, if_true]
    exact fun h => JasminLsemSimulation.regName_ne_argName k _ h.symm
  · simp only [hsa, if_false]
    exact JasminLsemSimulation.regName_ne (by omega)

/-- **Frame transport of the agreement.** A state carrying a `WriteFrame
    curDepth` from an agreeing state still agrees: every in-scope variable
    resolves outside the fresh block, so its register/array read is unchanged. -/
theorem StoreAgreesM.of_frame {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s s' : LstateM} {V : Ctxt.Valuation Γ} (hlen : Γ.length = curDepth)
    (hagree : StoreAgreesM nArgs curDepth s V) (hframe : WriteFrame curDepth s s') :
    StoreAgreesM nArgs curDepth s' V := by
  refine ⟨?_, ?_⟩
  · intro w' v
    have hv : varIndex v < curDepth := hlen ▸ JasminLsemSimulation.varIndex_lt v
    rw [evalOperandN_resolveVar, hframe.1 _ _
      (fun k hk => resolveVar_operandName_ne_regName v hv k hk),
      ← evalOperandN_resolveVar]
    exact hagree.reg v
  · intro w' n' v
    have hv : varIndex v < curDepth := hlen ▸ JasminLsemSimulation.varIndex_lt v
    rw [hframe.2 _ _ _ (fun k hk => resolveVar_operandName_ne_regName v hv k hk)]
    exact hagree.arr v

/-- Depth bookkeeping for the strengthened induction: one binding shifts the
    final depth by one, `(a + 1) + b = a + (b + 1)`. -/
private theorem storeAgrees_shift_depth {nArgs a b : Nat} {Γ' : Ctxt jasminDialect}
    {st : LstateM} {V : Ctxt.Valuation Γ'}
    (h : StoreAgreesM nArgs ((a + 1) + b) st V) :
    StoreAgreesM nArgs (a + (b + 1)) st V := by
  rw [show a + (b + 1) = (a + 1) + b from by omega]
  exact h

/-- **Core simulation, strengthened conclusion (§10's induction re-run).** As
    `lsemStraightMem_straightOps`, but the conclusion exposes the **final store
    agreement** — the landing state agrees with the binding-extended valuation
    `comDenoteLets com V` at the final depth — and the **write frame** — only
    the fresh `regName`-block at depth `≥ curDepth` was touched. The §10
    statement is unchanged; this is the additive variant the loop writeback
    (`JasminLsemMemSourceTieUncond`) discharges its per-trip simulation with. -/
theorem lsemStraightMem_straightOps_store {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateM} {V : Ctxt.Valuation Γ},
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesM nArgs curDepth st V →
      ∃ st', lsemStraightMem (straightOpsMem nArgs com curDepth) st = some st' ∧
        StoreAgreesM nArgs (curDepth + comLen com) st' (comDenoteLets com V) ∧
        WriteFrame curDepth st st' := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth st V hlen harg hagree
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
      · exact storeAgrees_shift_depth hAg
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_const (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) n hwn heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hAg, hFr⟩ := ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_, WriteFrame.stepReg _ hFr⟩
      · rw [straightOpsMem_const, lsemStraightMem_cons, hstep]; exact hrun
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg
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
      · exact storeAgrees_shift_depth hAg

/-- **The full strengthened package (register return).** Run + the return-value
    read (§10, never re-proved — merged by determinism of the fold) + the final
    store's agreement with the **original** valuation (frame transport) + the
    write frame. What the per-trip writeback discharge consumes. -/
theorem lsemStraightMem_straightOps_full {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) {w : Nat} (hw : t = .reg w)
    {nArgs curDepth : Nat} {st : LstateM} {V : Ctxt.Valuation Γ}
    (hlen : Γ.length = curDepth) (harg : nArgs ≤ curDepth)
    (hagree : StoreAgreesM nArgs curDepth st V) :
    ∃ st', lsemStraightMem (straightOpsMem nArgs com curDepth) st = some st' ∧
      StoreAgreesM nArgs curDepth st' V ∧
      WriteFrame curDepth st st' ∧
      evalOperandN st'.reg w (.reg (comRetReg nArgs argName com curDepth)) =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st1, hrun1, hret⟩ := lsemStraightMem_straightOps hcom hw hlen harg hagree
  obtain ⟨st2, hrun2, _hAg, hFr⟩ :=
    lsemStraightMem_straightOps_store hcom hlen harg hagree
  rw [hrun1] at hrun2
  obtain rfl := Option.some.inj hrun2
  exact ⟨st1, hrun1, StoreAgreesM.of_frame hlen hagree hFr, hFr, hret⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
