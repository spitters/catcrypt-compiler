/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Std.Data.HashMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaData
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaData

/-!
# Physical-register allocation for the linear export

The x86-64 register classes, the per-slot event trace of a linear body, the
linear-scan allocation over general-purpose and vector registers with spilling,
the two-address lowering of one binop, and the caller-save barriers around
`Lcall`.

## Main definitions

* `X86Backend.LprogAsmPrinter.x86Abi` (defined in `VIR.X86IsaData`): the x86 register file
  and calling convention, the default `IsaAbi` of every allocator and renaming definition
  below, each of which reads its allocation pool from the record it is given.
* `PhysEvent`, `bodyPhysTable`: the slot trace and its allocation table.
* `physTable`, `physTableClassed`: one-class and two-class linear scan.
* `lowerTwoAddr`: two-address lowering of a resolved binop.
* `straightCallPhys`: the straight-line multi-call barrier.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 7. Physical-register export (link 3/7: `assemble_prog`)

The `Com.toLprog` above emits a **pre-register-allocation SSA** lprog: every
binding's destination is a fresh virtual register (`r39 … r1654`), operands are
the argument names (`a0 … a38`), and each binop is 3-address (`dst ≠ src0`).
jasmin's `assemble_prog` (`asm_gen.ml :: xreg_of_var`) rejects this: it requires
every operand to be a **physical x86 (x)register** in **destructive two-address**
form (the explicit `id_out` shares asm-arg position 0 with `id_in[0]`, so the
destination must equal the first source).

This section adds a second export, `Com.toLprogPhysText`, that:

1. derives a **logical-slot read/write trace** from the body (the dst and src
   operands of each `Lopn`), one `PhysEvent` per binding;
2. runs a **linear-scan register allocation** over the **13 allocatable x86-64
   GP registers** (`RAX RBX RCX RDX RSI RDI RBP R8 … R13`; `RSP` is the stack
   pointer, `R14`/`R15` are reserved reload scratches), with **stack-slot
   spill** for any slot whose linear-scan physical index lands ≥ 13;
3. lowers each binop `dst = op src0 src1` to **two-address** form — `mov dst,
   src0` then `op dst, src1`, collapsed to the single `op dst, src1` when the RA
   already placed `dst` on `src0`'s physical location.

The virtual `Com.toLprog` is kept verbatim (it is the object of the
`LprogExportFaithful` hypothesis); the physical export is a *separate* lowering
on top of the same body walk, so both share `comToBody`. -/

/-! ### 7a. The 13 allocatable x86-64 GP registers + 2 reserved reload scratches

The allocatable registers `gpRegNames`, the reload scratches `reloadScratch` (`R15`) and
`reloadScratch2` (`R14`), the save slots `LprogAsmPrinter.qsaveSlot`, the callee-saved
registers `LprogAsmPrinter.calleeSavedRegs` and the record `LprogAsmPrinter.x86Abi` are
defined in `VIR.X86IsaData`. The physical index `0 … 12` names an allocatable register;
`13 …` spills to the stack array `k`. -/

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

/-! ### 7a′. The vector register class

The GP allocator above (`gpRegNames`) is scalar-only: it names physical slot
`0 … 12` as a GP register and `13 …` as a stack spill `k.N`. A `Com` that mixes
scalar GP ops with **vector** ops (`SimdOp`/`vpackZMM`, whose `Lopn` mnemonic
starts with `V` — `VPADDQ`, `VPXOR`, `VPACK8u64:…`, `VPROR D:…`, …) needs a
*disjoint* physical pool: a vector value must land in `%xmm/%ymm/%zmm`, never in
a GP register, and a scalar value never in a vector register.

The vector physical indices are carried in the SAME `Nat`-valued slot map as the
GP indices, offset by `vectorBase`. `physRegName` reads the class from the index
(`phys ≥ vectorBase` ⇒ vector). A GP spill index reaches `vectorBase` at
`vectorBase - numGPRegs` spill cells, so the index alone does not determine the
class; `physRegNameC` takes the class as an argument (the slot's class,
`slotIsVec`) and renders a GP-class index as a GP register or `k.N` and a
vector-class index as a vector register or `kv.N` at every index
(`physRegNameC_false_resolved`, `physRegNameC_true_resolved`). Where the slot's
class is the class the threshold reads, the two renderings agree
(`physRegNameC_decide`). -/

/-- The 16 allocatable x86 vector register names (`%xmm0 … %xmm15`), indexed by
    the per-class physical slot `0 … 15`. The textual name is width-agnostic
    (`XMM<i>`); the renderer widens it to `%ymm`/`%zmm` from the op's mnemonic if
    needed (VEX/EVEX encode the width on the instruction, not the register name).
    Disjoint from `gpRegNames`, so a vector value never collides with a GP one. -/
def vectorRegNames : List String :=
  ["XMM0", "XMM1", "XMM2", "XMM3", "XMM4", "XMM5", "XMM6", "XMM7",
   "XMM8", "XMM9", "XMM10", "XMM11", "XMM12", "XMM13", "XMM14", "XMM15"]

/-- Number of allocatable physical vector registers. -/
def numVecRegs : Nat := vectorRegNames.length

/-- The offset by which a vector physical slot index is shifted in the shared
    `Nat` slot map, so the class is recoverable from the index alone: a physical
    index `< vectorBase` is GP (allocatable register or `k.N` GP spill); an index
    `≥ vectorBase` is vector (`vectorRegNames[phys - vectorBase]`, or a `kv.N`
    vector spill on overflow). A GP spill index `numGPRegs + cell` reaches it at
    `cell ≥ vectorBase - numGPRegs`; `physRegNameC` renders such an index by the
    class of its slot. -/
def vectorBase : Nat := 4294967296

/-- Render a physical slot index as an operand name over the allocation pool
    `abi.allocPool` (at `x86Abi`, `gpRegNames`, `numGPRegs = 13`).

    * `phys < numGPRegs` (`< 13`): an allocatable GP register (`RAX … R13`).
    * `numGPRegs ≤ phys < vectorBase`: a GP stack spill slot `k.{phys-13}` (a
      real `RSP`-relative stack reference). The `.` separator (not `[]`) carries
      no brackets — the textual `Lopn` grammar reserves `[ ]` for the operand
      lists. The reserved scratch `R15` (`reloadScratch`) is never produced here.
    * `phys ≥ vectorBase`: a **vector** physical slot. `phys - vectorBase` indexes
      `vectorRegNames` (`XMM0 … XMM15`); on overflow it is a vector stack spill
      `kv.{idx-numVecRegs}`.

    A pure-scalar body never produces `phys ≥ vectorBase`, so its rendering is
    byte-identical to the GP-only original. -/
def physRegName (phys : Nat) (abi : IsaAbi := x86Abi) : String :=
  if phys ≥ vectorBase then
    let vidx := phys - vectorBase
    match vectorRegNames[vidx]? with
    | some r => r
    | none => "kv." ++ toString (vidx - numVecRegs)
  else
    match abi.allocPool[phys]? with
    | some r => r
    | none => "k." ++ toString (phys - abi.allocPool.length)

/-- Render physical index `phys` of register class `vec` (`true`: vector,
    `false`: GP) as an operand name over `abi.allocPool`.

    * vector class: the vector rendering of `physRegName` at
      `max phys vectorBase` (`vectorRegNames[phys - vectorBase]`, else
      `kv.{phys - vectorBase - numVecRegs}`);
    * GP class below `vectorBase`: `physRegName phys` (an `allocPool` register,
      else `k.{phys - |allocPool|}`);
    * GP class at or above `vectorBase`: the GP spill `k.{phys - |allocPool|}`.

    A GP-class index never renders as a vector name and a vector-class index
    never as a GP name, whatever its value. -/
def physRegNameC (vec : Bool) (phys : Nat) (abi : IsaAbi := x86Abi) : String :=
  if vec then physRegName (max phys vectorBase) abi
  else if phys < vectorBase then physRegName phys abi
  else "k." ++ toString (phys - abi.allocPool.length)

/-- At the class the index threshold reads, `physRegNameC` is `physRegName`. -/
theorem physRegNameC_decide (p : Nat) (abi : IsaAbi) :
    physRegNameC (decide (vectorBase ≤ p)) p abi = physRegName p abi := by
  unfold physRegNameC
  by_cases h : vectorBase ≤ p
  · simp [h]
  · simp [h, Nat.lt_of_not_le h]

/-- A GP-class index below `vectorBase` renders as `physRegName` does. -/
theorem physRegNameC_false_of_lt {p : Nat} (abi : IsaAbi) (hv : p < vectorBase) :
    physRegNameC false p abi = physRegName p abi := by
  simp [physRegNameC, hv]

/-- A vector-class index at or above `vectorBase` renders as `physRegName` does. -/
theorem physRegNameC_true_of_le {p : Nat} (abi : IsaAbi) (hv : vectorBase ≤ p) :
    physRegNameC true p abi = physRegName p abi := by
  simp [physRegNameC, Nat.max_eq_left hv]

/-- A GP-class index renders as a register of `abi.allocPool` or a GP spill
    slot `k.N`, at every index. -/
theorem physRegNameC_false_resolved (p : Nat) (abi : IsaAbi) :
    physRegNameC false p abi ∈ abi.allocPool ∨
      ∃ n : Nat, physRegNameC false p abi = "k." ++ toString n := by
  unfold physRegNameC
  simp only [Bool.false_eq_true, ite_false]
  split
  · unfold physRegName
    rw [ite_eq_right (by omega)]
    split
    · next r hr => exact Or.inl (List.mem_of_getElem? hr)
    · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

/-- A vector-class index renders as a register of `vectorRegNames` or a vector
    spill slot `kv.N`, at every index. -/
theorem physRegNameC_true_resolved (p : Nat) (abi : IsaAbi) :
    physRegNameC true p abi ∈ vectorRegNames ∨
      ∃ n : Nat, physRegNameC true p abi = "kv." ++ toString n := by
  unfold physRegNameC physRegName
  simp only [ite_true]
  rw [ite_eq_left (Nat.le_max_right _ _)]
  split
  · next r hr => exact Or.inl (List.mem_of_getElem? hr)
  · exact Or.inr ⟨_, rfl⟩

/-- The first character of a `k.N` spill name. -/
theorem kSpill_head (n : Nat) : ("k." ++ toString n).toList.head? = some 'k' := by
  simp [String.toList_append, show "k.".toList = ['k', '.'] from rfl]

/-- A GP spill name `k.N` is never a vector spill name `kv.M`. -/
theorem kSpill_ne_kvSpill (n m : Nat) : "k." ++ toString n ≠ "kv." ++ toString m := by
  intro h
  have hd := congrArg String.toList h
  simp [String.toList_append, show "k.".toList = ['k', '.'] from rfl,
    show "kv.".toList = ['k', 'v', '.'] from rfl] at hd

/-- Every vector register name starts with `X`. -/
theorem vectorRegNames_head : ∀ r ∈ vectorRegNames, r.toList.head? = some 'X' := by
  decide

/-- A GP spill name `k.N` is not a vector register name. -/
theorem kSpill_not_mem_vectorRegNames (n : Nat) : "k." ++ toString n ∉ vectorRegNames := by
  intro h
  have := vectorRegNames_head _ h
  rw [kSpill_head] at this
  exact absurd (Option.some.inj this) (by decide)

/-- The allocation pool of `abi` is disjoint from the vector names: no pool
    register is a vector register or a vector spill name `kv.N`. -/
def PoolVecFree (abi : IsaAbi) : Prop :=
  ∀ r ∈ abi.allocPool, r ∉ vectorRegNames ∧ ∀ n : Nat, r ≠ "kv." ++ toString n

/-- **GP class names no vector name.** Over a pool disjoint from the vector
    names, a GP-class index never renders as a vector register or a `kv.N`
    vector spill slot. -/
theorem physRegNameC_false_not_vec {abi : IsaAbi} (hpool : PoolVecFree abi) (p : Nat) :
    physRegNameC false p abi ∉ vectorRegNames ∧
      ∀ n : Nat, physRegNameC false p abi ≠ "kv." ++ toString n := by
  rcases physRegNameC_false_resolved p abi with h | ⟨m, h⟩
  · exact hpool _ h
  · rw [h]
    exact ⟨kSpill_not_mem_vectorRegNames m, kSpill_ne_kvSpill m⟩

/-- **Vector class names no GP name.** Over a pool disjoint from the vector
    names, a vector-class index never renders as a register of the pool or a
    `k.N` GP spill slot. -/
theorem physRegNameC_true_not_gp {abi : IsaAbi} (hpool : PoolVecFree abi) (p : Nat) :
    physRegNameC true p abi ∉ abi.allocPool ∧
      ∀ n : Nat, physRegNameC true p abi ≠ "k." ++ toString n := by
  rcases physRegNameC_true_resolved p abi with h | ⟨m, h⟩
  · refine ⟨fun hm => (hpool _ hm).1 h, fun n hn => ?_⟩
    rw [hn] at h
    exact kSpill_not_mem_vectorRegNames n h
  · rw [h]
    exact ⟨fun hm => (hpool _ hm).2 m rfl, fun n hn => kSpill_ne_kvSpill n m hn.symm⟩

/-- The x86 allocation pool is disjoint from the vector names. -/
theorem x86Abi_poolVecFree : PoolVecFree x86Abi := by
  have hR : ∀ r ∈ x86Abi.allocPool, r.toList.head? = some 'R' := by decide
  intro r hr
  refine ⟨fun hv => ?_, fun n hn => ?_⟩
  · have h1 := hR r hr
    rw [vectorRegNames_head r hv] at h1
    exact absurd (Option.some.inj h1) (by decide)
  · have h1 := hR r hr
    rw [hn] at h1
    simp [String.toList_append, show "kv.".toList = ['k', 'v', '.'] from rfl] at h1

/-! ### 7b. Per-binding slot events

A `PhysEvent` records, for one emitted `Lopn`, the destination operand and the
source operands, *as logical slot indices*. We index the body's operand names
(`a{j}` / `r{d}`) by first-appearance order, so the slot universe is exactly the
set of distinct registers the body touches — faithful to `comToBody`. -/

/-- One binding's operand footprint over logical-slot indices: the slot written
    and the slots read. Mirrors `UnrolledComRA.SlotEvent` (kept local so this
    export does not pull in the SHA-2 / Keccak trace machinery). -/
structure PhysEvent where
  /-- The logical slot written. -/
  wr : Nat
  /-- The logical slots read. -/
  rds : List Nat
  deriving Repr, DecidableEq

/-- The operand name of an `LOperand` for slot-indexing purposes (immediates and
    array elements are not register-file slots). -/
def LOperand.regName? : LOperand → Option String
  | .reg n => some n
  | .arr _ _ => none
  | .imm _ => none
  -- A register-indexed (SIB) operand `base[idx*scale]` reads the runtime index
  -- register `idx` from the register file; `base` is the (memory-resident)
  -- stack array. For the single-name `regName?` view (used by the *destination*
  -- side, where a SIB never appears) we surface the index register `idx`; the
  -- *source* side uses `LOperand.srcRegNames` below, which contributes BOTH the
  -- base pointer and the index so each is register-allocated and physical-mapped.
  | .arrIdx _ idx _ => some idx

/-- The register-file slot names an `LOperand` contributes **as a source**. This
    differs from `regName?` only on the SIB form `arrIdx base idx scale`, where
    the *base pointer* `base` is a GP source register (the runtime array
    base, supplied as a SysV pointer arg) alongside the index `idx`. Tracking the
    base here is what lets the linear scan allocate it and `remapOperand` rewrite
    the SIB's base/index to physical registers (so the printer renders
    `(%ptr,%idx,scale)` rather than `%<UNKNOWN:aN>`). For every non-SIB operand
    it agrees with `regName?.toList`, so existing kernels' traces are unchanged. -/
def LOperand.srcRegNames : LOperand → List String
  | .reg n => [n]
  | .arr _ _ => []
  | .imm _ => []
  | .arrIdx base idx _ => [base, idx]

/-- The destination + source register names of one `Lopn` (other `linstr_r`
    constructors carry no register-file slot footprint). The source side uses
    `srcRegNames` so a SIB source contributes both its base and index registers. -/
def linstrRegNames : LinstrR → Option (Option String × List String)
  | .Lopn dsts _ srcs =>
      some (dsts.head?.bind LOperand.regName?, srcs.flatMap LOperand.srcRegNames)
  | _ => none

/-- The ordered list of `(dstName?, srcNames)` of a body's `Lopn`s. -/
def bodyOpNames (body : Lcmd) : List (Option String × List String) :=
  body.filterMap (fun i => linstrRegNames i.li_i)

/-- Does the body contain a `MULXHI` binding? The post-RA `fuseMulHiLprog` pass
    overwrites `%rdx` at every such site (`MOV %rdx, s1` to pin the `mulx`
    multiplicand), so when this holds the allocator must withhold `%rdx` (physical
    index 3) from the pool — otherwise a value the scan parks there is clobbered.
    `false` leaves the pool at the full 13 registers, so a body with no mul-hi
    allocates exactly as before. -/
def bodyHasMulHi (body : Lcmd) : Bool :=
  body.any (fun i => match i.li_i with
    | .Lopn _ opn _ => opn.startsWith "MULXHI"
    | _ => false)

/-- The physical slots the allocator withholds for a body: `[3]` (`%rdx`) when the
    body has a `MULXHI` binding (see `bodyHasMulHi`), else none. -/
def bodyReservedGP (body : Lcmd) : List Nat :=
  if bodyHasMulHi body then [3] else []

/-! ### Compiled name-slot cache (performance)

The reference definitions `bodyNames` / `nameSlot` / `bodyTrace` are the spec.
Naively interpreted they are super-quadratic on a large body: `nameSlot`
recomputes `bodyNames` (itself `O(n²)` via `List.eraseDups`) and then runs an
`O(n)` `idxOf`, and it is called once per operand from `bodyTrace`,
`remapOperand`, and the ABI epilogue — `O(n³)` for SHA-256's ~4000-binding
body, which is why the `lean --run` interpreter never finished.

The compiled implementations below build, in a single `O(n)` pass over the
body, the first-appearance name list together with a `Std.HashMap String Nat`
giving each name's slot, and key that build on the body's runtime pointer so
repeated calls over the same body reuse it. `@[implemented_by]` swaps these in
for native execution; the pure spec is unchanged (the cache is an
implementation detail behind a `@[implemented_by]` boundary — no new axiom and
no admitted proof enters the spec side). -/

/-- The first-appearance distinct register-name list of a body, paired with the
    name→slot `HashMap`. Built in one `O(n)` pass. -/
@[inline] def bodyNameInfoImpl (body : Lcmd) : Array String × Std.HashMap String Nat :=
  Id.run do
    let mut names : Array String := #[]
    let mut m : Std.HashMap String Nat := {}
    for i in body do
      match i.li_i with
      | .Lopn dsts _ srcs =>
          let consider : List String :=
            (dsts.head?.bind LOperand.regName?).toList
              ++ srcs.flatMap LOperand.srcRegNames
          for nm in consider do
            if !m.contains nm then
              m := m.insert nm names.size
              names := names.push nm
      | _ => pure ()
    return (names, m)

/-- Pointer-keyed cache of `bodyNameInfoImpl`. The entry **retains the cached
    body** (a strong reference), so the cached object stays alive for the
    lifetime of the entry and its address cannot be reused by a different
    list; `ptrEq` against the live cached object therefore implies object
    identity (hence value equality), making a hit sound.

    Retention is required: a bare-address key over a non-retained body is
    unsound — once an exporter's virtual body is freed, the next export's body
    head cell can be allocated at the same address (same-size cons cells), and
    a false hit register-allocates the new body under the stale name→slot
    table. Every name absent from the stale table collapses onto the single
    out-of-universe sentinel slot `names.size`, so all such operands share ONE
    physical register and their use-site reloads clobber each other (e.g. a
    binop over two ABI inputs degenerating to `x ^ x`; the regression shape
    theorem is `LeaRoundThirEmit.leaX1_reloads_distinct`).

    Correctness does not depend on the cache hitting (a miss just rebuilds),
    only on a hit returning THIS body's table — which retention guarantees. -/
unsafe def bodyNameInfoCacheRef :
    IO.Ref (Option (Lcmd × Array String × Std.HashMap String Nat)) :=
  unsafeBaseIO (IO.mkRef none)

@[inline] unsafe def bodyNameInfoCached (body : Lcmd) :
    Array String × Std.HashMap String Nat :=
  unsafeBaseIO do
    match ← bodyNameInfoCacheRef.get with
    | some (cachedBody, names, m) =>
        if ptrEq body cachedBody then return (names, m)
        else
          let r := bodyNameInfoImpl body
          bodyNameInfoCacheRef.set (some (body, r.1, r.2))
          return r
    | none =>
        let r := bodyNameInfoImpl body
        bodyNameInfoCacheRef.set (some (body, r.1, r.2))
        return r

@[inline] unsafe def bodyNamesImpl (body : Lcmd) : List String :=
  (bodyNameInfoCached body).1.toList

/-- The distinct register names of a body in first-appearance order (the slot
    universe). -/
@[implemented_by bodyNamesImpl]
def bodyNames (body : Lcmd) : List String :=
  (bodyOpNames body).flatMap (fun (d, s) => d.toList ++ s) |>.eraseDups

@[inline] unsafe def nameSlotImpl (body : Lcmd) (n : String) : Nat :=
  let (names, m) := bodyNameInfoCached body
  m.getD n names.size

/-- The logical-slot index of a register name in a body (its first-appearance
    rank); `bodyNames.length` (out of universe) if absent. -/
@[implemented_by nameSlotImpl]
def nameSlot (body : Lcmd) (n : String) : Nat :=
  (bodyNames body).idxOf n

/-- The per-binding `PhysEvent` trace of a body: each `Lopn` becomes one event
    over the slot indices of its operands. A binding with no register
    destination (none of the producer's binops) contributes a liveness-only
    event reusing slot `0`. -/
@[inline] unsafe def bodyTraceImpl (body : Lcmd) : List PhysEvent :=
  let (names, m) := bodyNameInfoCached body
  let slot (nm : String) : Nat := m.getD nm names.size
  body.filterMap (fun i =>
    match i.li_i with
    | .Lopn dsts _ srcs =>
        let d := dsts.head?.bind LOperand.regName?
        let s := srcs.flatMap LOperand.srcRegNames
        some { wr := (d.map slot).getD 0, rds := s.map slot }
    | _ => none)

@[implemented_by bodyTraceImpl]
def bodyTrace (body : Lcmd) : List PhysEvent :=
  (bodyOpNames body).map (fun (d, s) =>
    { wr := (d.map (nameSlot body)).getD 0
      rds := s.map (nameSlot body) })

/-! ### 7b′. Register-class classification (GP vs vector)

A logical slot belongs to the **vector** register class iff a vector `Lopn`
touches it. A vector `Lopn` is one whose (width-stripped) mnemonic starts with
`V`: every `SimdOp.mnemonic` (`VPADDQ`, `VPXOR`, `VGF2P8MULB`, `VAESENC`, …) and
every `vpackZMM`/`vprordZMM`/`vps*` export arm (`VPACK8u64:…`, `VPACKD:…`,
`VPRORD:…`, `VPSLLDQ:…`, `VPSRLDQ:…`) begins with `V`, while **no** GP mnemonic
does (`ADD`, `SUB`, `MUL`, `MOV`, `CMOV`, `LOAD*`, `STORE*`, `ZEROEXT`, `TRUNC`,
`CALL:`, `MULXHI`, `ADCX`, `ROR:`, `SHR:`, `SHL:`, `SAR:`, `LOADSYM`). So the
`V`-prefix is a sound, additive class oracle: a body with no vector op classifies
every slot GP and the allocator is byte-identical to the original. In a body
with a vector op, the 256-bit value of a register-indexed access with element
stride `32` (`wideIdxVecNames`) is also vector. -/

/-- Is `opn` a **vector** `Lopn` mnemonic? True iff its width-stripped form starts
    with `"V"` — the common prefix of every `SimdOp.mnemonic` and every
    `vpack*`/`vpror*`/`vpsl*`/`vpsr*` export arm, and of no GP mnemonic. -/
def isVectorMnem (opn : String) : Bool := (stripWidthTag opn).startsWith "V"

/-- The register names of a 256-bit register-indexed access (`scale = 32`) that
    hold a 256-bit value: the destination of a `LOADIDX` and the stored value of a
    `STOREIDX`. The access has no vector mnemonic. -/
def wideIdxVecNames : LinstrR → List String
  | .Lopn [.reg d] "LOADIDX" [.arrIdx _ _ 32] => [d]
  | .Lopn _ "STOREIDX" [.arrIdx _ _ 32, .reg v] => [v]
  | _ => []

/-- Whether some `Lopn` of the body has a vector mnemonic (`isVectorMnem`). -/
def bodyHasVecOp (body : Lcmd) : Bool :=
  body.any fun i => match i.li_i with
    | .Lopn _ opn _ => isVectorMnem opn
    | _ => false

/-- A vector-class array marking which logical slots are in the **vector**
    register class: slot `s` is vector iff some vector `Lopn` (`isVectorMnem`)
    writes or reads it, or, in a body with a vector op, it is a 256-bit value of
    a register-indexed access (`wideIdxVecNames`). Built in one `O(n)` pass over
    the body, keyed by the same `nameSlot` indexing `bodyTrace` uses, so the class
    array aligns with the trace's slot universe. A body with no vector op yields
    the all-`false` array (every slot GP), so the GP-only allocation is
    unchanged. -/
@[inline] unsafe def bodyVecSlotsImpl (body : Lcmd) : Array Bool :=
  let (names, m) := bodyNameInfoCached body
  let slot (nm : String) : Nat := m.getD nm names.size
  let hasVec := bodyHasVecOp body
  Id.run do
    let mut a : Array Bool := Array.replicate (names.size + 1) false
    for i in body do
      match i.li_i with
      | .Lopn dsts opn srcs =>
          if isVectorMnem opn then
            let touched : List String :=
              (dsts.head?.bind LOperand.regName?).toList
                ++ srcs.flatMap LOperand.srcRegNames
            for nm in touched do
              let s := slot nm
              if s < a.size then a := a.set! s true
          else if hasVec then
            for nm in wideIdxVecNames (.Lopn dsts opn srcs) do
              let s := slot nm
              if s < a.size then a := a.set! s true
      | _ => pure ()
    return a

/-- Spec form of `bodyVecSlots` (the `@[implemented_by]` target is the cached
    one). Slot `s` is vector iff some `Lopn` with a vector mnemonic touches the
    register name whose `nameSlot` is `s`, or, in a body with a vector op, that
    name is a 256-bit value of a register-indexed access (`wideIdxVecNames`).
    Sized by `bodyNames body |>.length` (the distinct-name universe), the same
    upper bound `nameSlot` ranks against. -/
@[implemented_by bodyVecSlotsImpl]
def bodyVecSlots (body : Lcmd) : Array Bool :=
  Id.run do
    let mut a : Array Bool := Array.replicate ((bodyNames body).length + 1) false
    for i in body do
      match i.li_i with
      | .Lopn dsts opn srcs =>
          if isVectorMnem opn then
            let names : List String :=
              (dsts.head?.bind LOperand.regName?).toList
                ++ srcs.flatMap LOperand.srcRegNames
            for nm in names do
              let s := nameSlot body nm
              if s < a.size then a := a.set! s true
          else if bodyHasVecOp body then
            for nm in wideIdxVecNames (.Lopn dsts opn srcs) do
              let s := nameSlot body nm
              if s < a.size then a := a.set! s true
      | _ => pure ()
    return a

/-- The vector-class predicate over slots: `true` iff slot `s` is vector. Out of
    range (`s ≥ vecArr.size`) defaults to GP (`false`). -/
def slotIsVec (vecArr : Array Bool) (s : Nat) : Bool := vecArr[s]?.getD false

/-! ### 7c. Linear-scan physical allocation (13 GP regs + spill)

A Poletto–Sarkar linear scan over a **bounded** physical pool, derived locally
over `PhysEvent`: process slots in live-range-start order, reclaim registers
whose owner's range ended, take the lowest free register in `[0, numGPRegs)`.

When the pool is full, the *spill-at-interval* rule picks the value that goes to
the stack by **spill cost**: the register-resident value with the largest live
range *per use*, `(rangeEnd - position) / useCount`. A value that is touched on
every step therefore outranks an equally long-lived value that is touched twice.
The incoming interval competes under the same measure and is spilled itself when
it is the cheaper one.

Stack cells form a pool separate from the registers. Each cell carries the hull
`(minStart, maxEnd)` of the ranges placed in it, and a range enters a cell only
when it is disjoint from that hull. A spilled value occupies its cell over its
**whole** range — including the prefix it already spent in a register — so cell
reuse is decided against the hull rather than against the set of values live at
the spill point. -/

/-- All slots touched by an event. -/
def PhysEvent.touched (ev : PhysEvent) : List Nat := ev.wr :: ev.rds

/-- Slot-universe size (max touched slot + 1). -/
def physUniverse (tr : List PhysEvent) : Nat :=
  (tr.flatMap PhysEvent.touched).foldl Nat.max 0 + 1

/-- First trace position touching slot `s` (`tr.length` if never). -/
def physFirstTouch (tr : List PhysEvent) (s : Nat) : Nat :=
  match tr.zipIdx.find? (fun p => p.1.touched.contains s) with
  | some (_, i) => i
  | none => tr.length

/-- Last trace position touching slot `s` (`0` if never). -/
def physLastTouch (tr : List PhysEvent) (s : Nat) : Nat :=
  (tr.zipIdx.filterMap (fun p => if p.1.touched.contains s then some p.2 else none)).foldl
    Nat.max 0

/-- Conservative live range `[firstTouch, lastTouch]` of slot `s`. -/
def physLiveRange (tr : List PhysEvent) (s : Nat) : Nat × Nat :=
  (physFirstTouch tr s, physLastTouch tr s)

/-- Two ranges overlap iff each starts no later than the other ends. -/
def physRangesOverlap (r1 r2 : Nat × Nat) : Bool :=
  r1.1 ≤ r2.2 && r2.1 ≤ r1.2

/-- An in-flight *register* allocation during the scan. -/
structure PhysActive where
  /-- First trace position of the allocated slot's live range. -/
  st : Nat
  /-- Last trace position of the allocated slot's live range. -/
  en : Nat
  /-- The allocated physical register index (`< numRegs`). -/
  phys : Nat
  /-- The logical slot holding the register. -/
  slot : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The lowest physical index in `[0, numRegs)` held by no active allocation and
    not in `reserved`. `reserved` names physical slots withheld from allocation for
    the whole body — used to keep `%rdx` (index 3) free when the body has a mul-hi
    binding, which the post-RA `fuseMulHiLprog` pass overwrites at every fused
    `mulx` site (mirrors the JInstr route's resident-pool `%rdx` reservation). The
    `[]` case is definitionally the un-reserved scan, so every 2-argument caller
    and its proofs are unchanged. -/
def freeRegIn (numRegs : Nat) (used : List Nat) (reserved : List Nat := []) :
    Option Nat :=
  match reserved with
  | [] => (List.range numRegs).find? (fun ph => !used.contains ph)
  | r  => (List.range numRegs).find? (fun ph => !used.contains ph && !r.contains ph)

/-- Per-cell occupancy hulls: entry `i` is the `(minStart, maxEnd)` hull of the
    ranges placed in stack cell `i`, whose physical index is `numRegs + i`. -/
abbrev CellHulls := Array (Nat × Nat)

/-- The first cell index `≥ i` whose hull is disjoint from `[st, en]`, or
    `hulls.size` when every existing cell overlaps. -/
def firstFittingCell (hulls : CellHulls) (st en : Nat) : Nat → Nat
  | i =>
    if h : i < hulls.size then
      if physRangesOverlap hulls[i] (st, en) then firstFittingCell hulls st en (i + 1)
      else i
    else i
termination_by i => hulls.size - i
decreasing_by omega

/-- Place `[st, en]` in the lowest cell whose hull is disjoint from it, widening
    that cell's hull to cover the range; append a fresh cell when none fits. -/
def allocCell (hulls : CellHulls) (st en : Nat) : Nat × CellHulls :=
  let i := firstFittingCell hulls st en 0
  match hulls[i]? with
  | some c => (i, hulls.set! i (Nat.min c.1 st, Nat.max c.2 en))
  | none => (i, hulls.push (st, en))

/-- Spill-cost order on allocations at trace position `st`: `a` outranks `b` when
    its remaining range per use is larger, `(a.en - st) / uses[a.slot]` against
    `(b.en - st) / uses[b.slot]`, compared by cross-multiplication. Ties break on
    the later range end, then on the larger slot index. -/
def spillPrefer (st : Nat) (uses : Array Nat) (a b : PhysActive) : Bool :=
  let ka := (a.en - st) * Nat.max 1 (uses[b.slot]?.getD 1)
  let kb := (b.en - st) * Nat.max 1 (uses[a.slot]?.getD 1)
  if ka == kb then
    if a.en == b.en then a.slot > b.slot else a.en > b.en
  else ka > kb

/-- The register-resident allocation that `spillPrefer` ranks highest. -/
def spillVictim (st : Nat) (uses : Array Nat) (act : List PhysActive) :
    Option PhysActive :=
  act.foldl (fun best a =>
      match best with
      | some b => if spillPrefer st uses a b then some a else best
      | none => some a)
    none

/-- One scan step over the interval `[st, en]` of slot `s`.

    Register allocations whose range ended before `st` are reclaimed. If a
    register in `[0, numRegs)` is then free, `s` takes the lowest one. Otherwise
    `spillVictim` ranks the register-resident values, the winner is compared
    against the incoming interval under the same `spillPrefer` order, and the
    higher-ranked of the two moves to a stack cell for its whole range
    (`allocCell`). When the victim is a resident value, `s` takes the register it
    vacates.

    Assignments are accumulated most-recent-first, so `find?` on the result reads
    the final location of a slot that a later step moved to a cell. -/
def physScanSpillStep (numRegs : Nat) (uses : Array Nat)
    (act : List PhysActive) (hulls : CellHulls) (acc : List (Nat × Nat))
    (s st en : Nat) (reserved : List Nat := []) :
    List PhysActive × CellHulls × List (Nat × Nat) :=
  let act' := act.filter (fun a => a.en ≥ st)
  let used := act'.map PhysActive.phys
  match freeRegIn numRegs used reserved with
  | some ph => (⟨st, en, ph, s⟩ :: act', hulls, (s, ph) :: acc)
  | none =>
      let inc : PhysActive := ⟨st, en, numRegs, s⟩
      match spillVictim st uses act' with
      | some far =>
          if spillPrefer st uses far inc then
            let r := allocCell hulls far.st far.en
            (⟨st, en, far.phys, s⟩ :: act'.filter (fun a => a.phys != far.phys),
             r.2, (far.slot, numRegs + r.1) :: (s, far.phys) :: acc)
          else
            let r := allocCell hulls st en
            (act', r.2, (s, numRegs + r.1) :: acc)
      | none =>
          let r := allocCell hulls st en
          (act', r.2, (s, numRegs + r.1) :: acc)

/-- Run the bounded scan over `(slot, start, end)` triples sorted by start. -/
def physScanSpill (numRegs : Nat) (uses : Array Nat)
    (items : List (Nat × Nat × Nat)) (act : List PhysActive) (hulls : CellHulls)
    (acc : List (Nat × Nat)) (reserved : List Nat := []) : List (Nat × Nat) :=
  match items with
  | [] => acc
  | (s, st, en) :: rest =>
      let (act', hulls', acc') :=
        physScanSpillStep numRegs uses act hulls acc s st en reserved
      physScanSpill numRegs uses rest act' hulls' acc' reserved

/-! #### The scan's register-distinctness invariant

The register half of the allocation is safe because the physical indices held by
the in-flight allocations stay pairwise distinct: `freeRegIn` only ever hands out
an index no active allocation holds, and the one step that hands out an index
already in use (`spillVictim` moving a resident value to a stack cell) drops that
value's allocation in the same step. Two slots whose ranges overlap are therefore
never given the same register. -/

/-- Occurrences of slot `s` among the slots the trace touches. -/
def physSlotUses (tr : List PhysEvent) (s : Nat) : Nat :=
  (tr.flatMap PhysEvent.touched).count s

/-- `List.merge` with an explicit fuel argument, recursive on the fuel. Fuel `0`
    returns the first list. -/
def mergeFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, _ => xs
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | f + 1, x :: xs, y :: ys =>
      if le x y then x :: mergeFuel le f xs (y :: ys)
      else y :: mergeFuel le f (x :: xs) ys

open List.MergeSort.Internal in
/-- `List.mergeSort` with an explicit fuel argument, recursive on the fuel: the
    same contiguous split and the same merge, so the sort is stable. Fuel `0`
    returns the list. -/
def mergeSortFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | f + 1, a :: b :: l =>
      let lr := splitInTwo ⟨a :: b :: l, rfl⟩
      mergeFuel le (l.length + 2) (mergeSortFuel le f lr.1.1) (mergeSortFuel le f lr.2.1)

/-- `List.mergeSort` at the fuel its own argument supplies. `List.merge` and
    `List.mergeSort` are sealed to the kernel, so a closed application of either
    has no normal form, and `mergeSortFuel` recurses on a `Nat` instead.

    Recursion on a `Nat` is necessary and not sufficient. The recursion calls
    `List.MergeSort.Internal.splitInTwo`, which the module system seals as well,
    so inside a `module` a closed `kernelMergeSort` application still has no
    normal form. A module stating an equation about one unseals it with
    `import all Init.Data.List.Sort.Basic` and `import all Init.Data.List.Sort.Impl`.
    `import all` exposes only the named module's own implementation section and
    is not transitive, so each such module carries its own copy of both lines.
    Measured on Lean 4.33.1. `physLiveData` sorts live intervals with this. -/
def kernelMergeSort {α : Type} (le : α → α → Bool) (l : List α) : List α :=
  mergeSortFuel le l.length l

/-- Compiled `physLiveData`: one `O(n)` pass over the trace records the first
    touch, the last touch and the touch count of every slot into arrays (rather
    than re-scanning the trace per slot in
    `physFirstTouch`/`physLastTouch`/`physSlotUses`). -/
@[inline] def physLiveDataImpl (tr : List PhysEvent) :
    List (Nat × Nat × Nat) × Array Nat :=
  let univ := physUniverse tr
  let len := tr.length
  let (firstA, lastA, useA) : Array Nat × Array Nat × Array Nat := Id.run do
    let mut fst : Array Nat := Array.replicate univ len   -- sentinel = len (never)
    let mut lst : Array Nat := Array.replicate univ 0
    let mut cnt : Array Nat := Array.replicate univ 0
    let mut pos := 0
    for ev in tr do
      for s in ev.touched do
        if s < univ then
          if fst[s]! == len then fst := fst.set! s pos
          lst := lst.set! s pos
          cnt := cnt.set! s (cnt[s]! + 1)
      pos := pos + 1
    return (fst, lst, cnt)
  let raw := (List.range univ).filterMap (fun s =>
    let st := firstA[s]!
    if st < len then some (s, st, lastA[s]!) else none)
  (raw.mergeSort (fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 ≤ b.1)), useA)

/-- The live slots paired with ranges (sorted by start then slot), together with
    the per-slot touch counts over `[0, physUniverse)`. -/
@[implemented_by physLiveDataImpl]
def physLiveData (tr : List PhysEvent) : List (Nat × Nat × Nat) × Array Nat :=
  let univ := physUniverse tr
  let raw := (List.range univ).filterMap (fun s =>
    let (st, en) := physLiveRange tr s
    if st < tr.length then some (s, st, en) else none)
  (kernelMergeSort (fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 ≤ b.1)) raw,
   ((List.range univ).map (physSlotUses tr)).toArray)

/-- The live slots paired with ranges, sorted by start then slot. -/
def physLiveItems (tr : List PhysEvent) : List (Nat × Nat × Nat) :=
  (physLiveData tr).1

/-- The logical→physical slot assignment: the linear scan over the allocation pool
    `abi.allocPool`. -/
def physAssign (tr : List PhysEvent) (abi : IsaAbi := x86Abi) : List (Nat × Nat) :=
  let d := physLiveData tr
  physScanSpill abi.allocPool.length d.2 d.1 [] #[] []

/-- The logical→physical slot map (identity outside the live set). -/
def physMap (tr : List PhysEvent) (s : Nat) (abi : IsaAbi := x86Abi) : Nat :=
  match (physAssign tr abi).find? (fun p => p.1 == s) with
  | some (_, ph) => ph
  | none => s

/-- Compiled `physTable`: scatter the assignment into an identity-seeded array
    in one pass (rather than `assign.find?` per slot). -/
@[inline] def physTableImpl (tr : List PhysEvent) (abi : IsaAbi := x86Abi) : Array Nat :=
  let univ := physUniverse tr
  Id.run do
    let mut t : Array Nat := (Array.range univ)
    -- `physAssign` is most-recent-first (a slot the scan later moved to a stack
    -- cell appears twice, newest first), and `physTable`'s `find?` reads the
    -- head; scattering in reverse gives the same last-write-wins result.
    for (s, ph) in (physAssign tr abi).reverse do
      if s < univ then t := t.set! s ph
    return t

/-- Precomputed logical→physical lookup table over `[0, physUniverse)`. -/
@[implemented_by physTableImpl]
def physTable (tr : List PhysEvent) (abi : IsaAbi := x86Abi) : Array Nat :=
  let assign := physAssign tr abi
  let univ := physUniverse tr
  (Array.range univ).map (fun s =>
    match assign.find? (fun p => p.1 == s) with
    | some (_, ph) => ph
    | none => s)

/-- Memoised `physMap` via an `O(1)` table lookup. -/
def physMapTabled (tbl : Array Nat) (s : Nat) : Nat := tbl[s]?.getD s

/-! ### 7c′. Two-class linear scan (GP + vector in one pass)

`physAssign` runs a single linear scan over *all* live slots into the GP pool.
For a mixed scalar+vector `Com`, the slots split into two classes (`bodyVecSlots`)
that must allocate from **disjoint** physical pools. `physAssignClassed` keeps the
exact Poletto–Sarkar scan but partitions the live items by class *before*
scanning: GP slots run one scan into pool `0,1,…` (rendered as `RAX,RBX,…`/`k.N`
GP spills), vector slots run an **independent** scan into pool `0,1,…` that is
then offset by `vectorBase` (rendered as `XMM0,XMM1,…`/`kv.N` vector spills). A
vector value never takes a GP physical index and a scalar value never takes a
vector one.

When `vecArr` marks no slot vector (every pure-scalar kernel), the vector item
list is empty, the GP item list is exactly `physLiveItems tr`, and the GP scan is
the same call `physScanSpill numGPRegs uses items [] #[] []` as `physAssign` — so
the result is byte-identical to the GP-only allocator. -/

/-- Class-aware logical→physical assignment. Partition the live items by class
    (`vecArr`), run two independent linear scans, and offset the vector class's
    physical indices by `vectorBase`. Reduces to `physAssign tr` when no slot is
    vector. -/
def physAssignClassed (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved : List Nat := []) (reservedVec : List Nat := []) (abi : IsaAbi := x86Abi) :
    List (Nat × Nat) :=
  let d := physLiveData tr
  let gpItems := d.1.filter (fun it => !slotIsVec vecArr it.1)
  let vecItems := d.1.filter (fun it => slotIsVec vecArr it.1)
  let gpAssign := physScanSpill abi.allocPool.length d.2 gpItems [] #[] [] reserved
  -- `reservedVec` (default `[]`) lists vector-pool indices the scan must avoid.
  -- The batch8 path passes `[numVecRegs - 1]` (= `[15]`) to reserve `%ymm15` as
  -- the printer's spill-legalization scratch: the excluded index is never handed
  -- out, and the first spill takes index `numVecRegs` (→ `kv.0`), so the register
  -- boundary in `physRegName` (and its faithfulness lemmas) is unchanged.
  let vecAssign := physScanSpill numVecRegs d.2 vecItems [] #[] [] reservedVec
  gpAssign ++ vecAssign.map (fun p => (p.1, p.2 + vectorBase))

/-- Compiled class-aware `physTable`: scatter the class-aware assignment into an
    identity-seeded array in one pass. -/
@[inline] def physTableClassedImpl (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved : List Nat := []) (reservedVec : List Nat := []) (abi : IsaAbi := x86Abi) :
    Array Nat :=
  let univ := physUniverse tr
  Id.run do
    let mut t : Array Nat := (Array.range univ)
    -- Reverse for the same last-write-wins reason as `physTableImpl`.
    for (s, ph) in (physAssignClassed tr vecArr reserved reservedVec abi).reverse do
      if s < univ then t := t.set! s ph
    return t

/-- Class-aware logical→physical lookup table: like `physTable`, but GP and
    vector slots are allocated from disjoint pools (`physAssignClassed`). For a
    body with no vector slot this is `physTable tr` exactly. -/
@[implemented_by physTableClassedImpl]
def physTableClassed (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved : List Nat := []) (reservedVec : List Nat := []) (abi : IsaAbi := x86Abi) :
    Array Nat :=
  let assign := physAssignClassed tr vecArr reserved reservedVec abi
  let univ := physUniverse tr
  (Array.range univ).map (fun s =>
    match assign.find? (fun p => p.1 == s) with
    | some (_, ph) => ph
    | none => s)

/-- The class-aware physical table for a body: `physTableClassed` over `bodyTrace`
    with the body's own `bodyVecSlots` classification. This is the single-pass
    mixed scalar+vector register allocator — GP bindings to GP regs, vector
    bindings to `XMM`. For a pure-scalar body (`bodyVecSlots` all-`false`) it is
    `physTable (bodyTrace body)`, so existing kernels are byte-identical. -/
def bodyPhysTable (body : Lcmd) (abi : IsaAbi := x86Abi) : Array Nat :=
  physTableClassed (bodyTrace body) (bodyVecSlots body) (bodyReservedGP body) [] abi

/-! ### 7d. Two-address lowering of one binop

Each producer binop `dst = op src0 src1` becomes the destructive pair
`mov dst, src0; op dst, src1`, collapsed to `op dst, src1` when `dst = src0`
already (the RA may place them on the same physical register). The `mov` is the
x86 register move; the reader maps `MOV` accordingly. -/

/-- Is an operand a red-zone spill slot (`k.N`, rendered by `physRegName` for an
    allocation index `≥ numGPRegs`)? Such operands the reader materialises as
    `RSP`-relative memory references, so a two-operand x86 instruction may carry
    at most one of them. -/
def LOperand.isSpill : LOperand → Bool
  | .reg n => "k.".isPrefixOf n
  | _ => false

/-- Is a SIB element name a spill slot? A SIB base/index is a bare register
    *name* (`arrIdx`'s `base`/`idx` are `String`s, always full-64-bit registers
    in x86 SIB addressing). The spilling allocator may place either on the stack,
    giving a `k.N` name — which is **not** a register and which the owned printer
    renders as the `%<UNKNOWN:k.N>` sentinel `as` rejects (an x86 SIB base/index
    must be a register). -/
def sibNameSpill (n : String) : Bool := "k.".isPrefixOf n

/-- Legalize a register-indexed (SIB) memory element `arrIdx base idx scale` so
    that **both** its base and index are real registers, as x86 SIB addressing
    requires. The spilling allocator may place the base pointer and/or the index
    on the stack (a `k.N` spill name); the owned printer renders such a SIB
    base/index as the `%<UNKNOWN:k.N>` sentinel — bug class 3 on the **address**
    (the third remaining ChaCha codegen error,
    `movq %r15, (%<UNKNOWN:k.5>, %rax, 8)`). When the base is a spill it is
    reloaded into the secondary scratch `R14` (`reloadScratch2`); when the index
    is a spill it is reloaded into the primary scratch `R15` (`reloadScratch`).
    Returns `(prelude, fixedElem)` where `fixedElem`'s base/index are always
    registers, and `prelude` are the reload `mov`s (each a legal `mov reg, mem`).

    The two scratches are disjoint from each other and from the load/store value
    routing convention: the LOAD/STORE legalizers route a spilled *value* through
    `R15`, but a `LOADIDX`/`STOREIDX` whose SIB index is itself a spill is the
    rare case the address-reload below targets — and the caller composes the two
    so the address reload runs *first*, before any value routing reuses `R15`.
    For the common base-only spill (the observed ChaCha bug) only `R14` is used,
    leaving `R15` free for the value. Non-SIB operands pass through unchanged. -/
def legalizeSibElem (o : LOperand) : List LinstrR × LOperand :=
  match o with
  | .arrIdx base idx scale =>
      let basePre : List LinstrR :=
        if sibNameSpill base then [.Lopn [.reg reloadScratch2] "MOV:64" [.reg base]]
        else []
      let base' : String := if sibNameSpill base then reloadScratch2 else base
      let idxPre : List LinstrR :=
        if sibNameSpill idx then [.Lopn [.reg reloadScratch] "MOV:64" [.reg idx]]
        else []
      let idx' : String := if sibNameSpill idx then reloadScratch else idx
      (basePre ++ idxPre, .arrIdx base' idx' scale)
  | _ => ([], o)

/-! ### Frame-array names

A frame array of `n` words at byte offset `o` from the post-`leaq` `%rsp` is named
`fa.<o>.<n>`. The name denotes the address of the array's cell 0; the only instruction that
mentions it is the address load `LEA:64 d, fa.<o>.<n>` (`ptrLoad`). The frame-array region
occupies `[0, faBytes body)` at the bottom of the frame, below every other frame cell. -/

/-- The name `fa.<o>.<n>` of a frame array of `n` words at byte offset `o` from the
    post-`leaq` `%rsp`. -/
def faName (o n : Nat) : String := "fa." ++ toString o ++ "." ++ toString n

/-- The offset and the word count of a frame-array name `fa.<o>.<n>`, read over the character
    list; `none` for every other name. -/
def faParts? (q : String) : Option (Nat × Nat) :=
  if hasPrefix q "fa." then
    match (q.toList.drop 3).span (· != '.') with
    | (os, '.' :: ns) =>
        match natOfDigits? os, natOfDigits? ns with
        | some o, some n => some (o, n)
        | _, _ => none
    | _ => none
  else none

/-- Whether a name is a frame-array name `fa.<o>.<n>`. -/
def faB (q : String) : Bool := (faParts? q).isSome

/-- The end `o + 8 n` of the frame array an operand names, and `0` for an operand that names
    no frame array. -/
def faOpBytes : LOperand → Nat
  | .reg q =>
      match faParts? q with
      | some (o, n) => o + 8 * n
      | none => 0
  | _ => 0

/-- The bytes of the frame-array region of a body: the largest end `o + 8 n` over the
    frame-array names `fa.<o>.<n>` of its instructions, and `0` for a body without them. -/
def faBytes (body : Lcmd) : Nat :=
  body.foldl (fun acc i =>
    match i.li_i with
    | .Lopn dsts _ srcs => (dsts ++ srcs).foldl (fun a o => max a (faOpBytes o)) acc
    | _ => acc) 0

/-- Whether an operand names no frame array. -/
def faFreeOp : LOperand → Bool
  | .reg q => !faB q
  | _ => true

/-- Whether no instruction of a body names a frame array. -/
def faFree (body : Lcmd) : Bool :=
  body.all fun i =>
    match i.li_i with
    | .Lopn dsts _ srcs => (dsts ++ srcs).all faFreeOp
    | _ => true

/-- An operand that names no frame array ends no frame array. -/
theorem faOpBytes_of_faFreeOp {o : LOperand} (h : faFreeOp o = true) : faOpBytes o = 0 := by
  cases o with
  | reg q => grind [faFreeOp, faB, faOpBytes]
  | _ => rfl

/-- The fold of `faOpBytes` over operands that name no frame array returns its start. -/
theorem foldl_faOpBytes_of_faFreeOp (l : List LOperand) (a : Nat)
    (h : l.all faFreeOp = true) :
    l.foldl (fun a o => max a (faOpBytes o)) a = a := by
  induction l generalizing a with
  | nil => rfl
  | cons o l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.foldl_cons, faOpBytes_of_faFreeOp h.1, Nat.max_zero, ih _ h.2]

/-- **A body without frame-array names has an empty frame-array region.** -/
theorem faBytes_eq_zero_of_faFree {body : Lcmd}
    (h : faFree body = true) : faBytes body = 0 := by
  unfold faBytes
  generalize 0 = a
  induction body generalizing a with
  | nil => rfl
  | cons i body ih =>
    simp only [faFree, List.all_cons, Bool.and_eq_true] at h
    simp only [List.foldl_cons]
    split
    · rename_i heq
      simp only [heq] at h
      rw [foldl_faOpBytes_of_faFreeOp _ _ h.1]
      exact ih h.2 a
    · exact ih h.2 a

/-- **The pointer load** of a reload slot `q` into `R14` (`reloadScratch2`): the address load
    `LEA:64 R14, q` of a frame-array name, and the move `MOVQ R14, q` of a save slot
    otherwise. -/
def ptrLoad (q : String) : LinstrR :=
  if faB q then .Lopn [.reg reloadScratch2] "LEA:64" [.reg q]
  else .Lopn [.reg reloadScratch2] "MOVQ" [.reg q]

/-- The pointer load of a save slot is the move `MOVQ R14, q`. -/
theorem ptrLoad_qsave {q : String} (h : faB q = false) :
    ptrLoad q = .Lopn [.reg reloadScratch2] "MOVQ" [.reg q] := by
  simp [ptrLoad, h]

/-- The pointer load of a frame-array name is the address load `LEA:64 R14, q`. -/
theorem ptrLoad_fa {q : String} (h : faB q = true) :
    ptrLoad q = .Lopn [.reg reloadScratch2] "LEA:64" [.reg q] := by
  simp [ptrLoad, h]

/-- The two forms of a pointer load. -/
theorem ptrLoad_cases (q : String) :
    ptrLoad q = .Lopn [.reg reloadScratch2] "MOVQ" [.reg q] ∨
      ptrLoad q = .Lopn [.reg reloadScratch2] "LEA:64" [.reg q] := by
  cases h : faB q
  · exact .inl (ptrLoad_qsave h)
  · exact .inr (ptrLoad_fa h)

/-- **Reload a clobbered memref base pointer from its red-zone save slot.**

    In the 2-pointer memref ABI (`inLoadMap = none`, `outStoreMap = []` —
    ChaCha/SHA/Keccak whole-state kernels), each `LOADIDX`/`STOREIDX`
    self-addresses through a pointer argument `aj` used as the SIB base. After
    `remapOperand`, that base is the *physical* register the linear-scan RA gave
    `aj` (e.g. `RDI`/`RCX`), into which `buildArgPtrMaterialize` copied the
    SysV-argument pointer **once** at function entry. But that physical register
    is in the allocatable set, so the 20-round body REUSES it as a scratch — by
    the time a later `memrefSetDyn`/`memrefGetDyn` resolves its SIB base, the
    register holds a ChaCha *word*, not the pointer, and the store/load writes
    through garbage (the gdb-confirmed segfault: `%rdi` = `0x6b3ca454`, a word).

    The pointer is, however, live in MEMORY the whole function: the prologue
    saved it to the red zone (`qsave.RDI`/`qsave.RSI`). So we mirror
    `legalizeSibElem`'s reload-base pattern, but keyed on the ABI-arg's qsave
    slot rather than on a spill name: immediately before the access, emit
    `mov R14, [qsave.<abiArg>]` and rewrite the SIB base to `R14`
    (`reloadScratch2`). The reload is unconditional per access (one extra `movq`),
    which keeps the reasoning local and never trusts the body-clobberable
    register.

    `memrefBaseReload : String → Option String` maps a physical base register
    name (`phys(aj)`) to the qsave slot holding its pointer; it is built by the
    ABI export from `abiArgs`/the RA table (see `comToLfundefPhysAbi`). Off the
    memref ABI path it is `fun _ => none`, so this is the identity `([], o)` and
    every existing kernel's bytes are unchanged.

    `R14` is disjoint from the value/index routing in `legalizeMemLoad`/
    `legalizeMemStore`: those route a spilled VALUE or a spilled INDEX through
    `R15`, and `legalizeSibElem`'s spill-base reload (also `R14`) is **not**
    triggered here — the base we hand back is the register `R14`, not a `k.N`
    spill — so the pointer in `R14` survives untouched through the access. -/
def reloadMemrefBase (memrefBaseReload : String → Option String) (o : LOperand) :
    List LinstrR × LOperand :=
  match o with
  | .arrIdx base idx scale =>
      match memrefBaseReload base with
      | some qsave => ([ptrLoad qsave], .arrIdx reloadScratch2 idx scale)
      | none => ([], o)
  | _ => ([], o)

/-- **The reload of a register base** `b`: when `memrefBaseReload` maps `b` to a reload slot
    `q`, the pointer load `ptrLoad q` into `R14` and the base `R14` (`reloadScratch2`); no
    instruction and the base `b` otherwise. It is the base reload of `reloadMemrefBase` for a
    base that is a register operand rather than the base of an indexed operand
    (`reloadMemrefBase_arrIdx`). -/
def reloadRegBase (memrefBaseReload : String → Option String) (b : String) :
    List LinstrR × String :=
  match memrefBaseReload b with
  | some qsave => ([ptrLoad qsave], reloadScratch2)
  | none => ([], b)

/-- The reload of a register base with a reload slot `q` is the pointer load of `q`. -/
theorem reloadRegBase_some_ptrLoad {mbr : String → Option String} {b q : String}
    (h : mbr b = some q) : reloadRegBase mbr b = ([ptrLoad q], reloadScratch2) := by
  simp [reloadRegBase, h]

/-- The reload of a register base with a save slot `q` is the move `MOVQ R14, q`. -/
theorem reloadRegBase_some {mbr : String → Option String} {b q : String}
    (h : mbr b = some q) (hq : faB q = false) :
    reloadRegBase mbr b = ([.Lopn [.reg reloadScratch2] "MOVQ" [.reg q]], reloadScratch2) := by
  simp [reloadRegBase, h, ptrLoad_qsave hq]

theorem reloadRegBase_none {mbr : String → Option String} {b : String} (h : mbr b = none) :
    reloadRegBase mbr b = ([], b) := by
  simp [reloadRegBase, h]

/-- The base reload of an indexed operand is the reload of its base register. -/
theorem reloadMemrefBase_arrIdx (mbr : String → Option String) (b y : String) (s : Nat) :
    reloadMemrefBase mbr (.arrIdx b y s) =
      ((reloadRegBase mbr b).1, .arrIdx (reloadRegBase mbr b).2 y s) := by
  cases h : mbr b <;> simp [reloadMemrefBase, reloadRegBase, h]

/-- Every instruction of a register-base reload is the pointer load of the reload slot of the
    base. -/
theorem reloadRegBase_mem {mbr : String → Option String} {b : String} {r : LinstrR}
    (hr : r ∈ (reloadRegBase mbr b).1) :
    ∃ q, mbr b = some q ∧ r = ptrLoad q := by
  cases h : mbr b with
  | none => simp [reloadRegBase, h] at hr
  | some q => exact ⟨q, rfl, by simpa [reloadRegBase, h] using hr⟩

/-- **The base reload of a constant-shape array instruction**, the register-base form of
    `reloadMemrefBase`. A zeroing `ZEROARR [B] [#n, #w]`, whose base is its destination `B`,
    becomes the pointer load `ptrLoad q` of the reload slot `q` of `B` followed by the physical
    form `ZEROARR [] [R14, #n, #w]`, which reads its base as a source; a constant-index store
    `STOREIMM [D] [B, V, #k]` becomes `ptrLoad q` for the reload slot `q` of `B` followed by
    `STOREIMM [R14] [R14, V, #k]`. The result is `none` for every other instruction and when
    the base has no reload slot. -/
def reloadArrImm (memrefBaseReload : String → Option String) : LinstrR → Option (List LinstrR)
  | .Lopn [.reg b] opn [.imm n, .imm w] =>
      if opn = "ZEROARR" then
        (memrefBaseReload b).map fun q =>
          [ptrLoad q, .Lopn [] "ZEROARR" [.reg reloadScratch2, .imm n, .imm w]]
      else none
  | .Lopn [.reg _] opn [.reg b, .reg v, .imm k] =>
      if opn = "STOREIMM" then
        (memrefBaseReload b).map fun q =>
          [ptrLoad q,
           .Lopn [.reg reloadScratch2] "STOREIMM" [.reg reloadScratch2, .reg v, .imm k]]
      else none
  | _ => none

/-- The reload of a zeroing whose base has the reload slot `q`. -/
theorem reloadArrImm_zeroArr_ptrLoad {mbr : String → Option String} {b q : String}
    (n w : Nat) (h : mbr b = some q) :
    reloadArrImm mbr (.Lopn [.reg b] "ZEROARR" [.imm n, .imm w]) =
      some [ptrLoad q, .Lopn [] "ZEROARR" [.reg reloadScratch2, .imm n, .imm w]] := by
  simp [reloadArrImm, h]

/-- The reload of a constant-index store whose base has the reload slot `q`. -/
theorem reloadArrImm_storeImm_ptrLoad {mbr : String → Option String} {b q : String}
    (d v : String) (k : Nat) (h : mbr b = some q) :
    reloadArrImm mbr (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k]) =
      some [ptrLoad q,
        .Lopn [.reg reloadScratch2] "STOREIMM" [.reg reloadScratch2, .reg v, .imm k]] := by
  simp [reloadArrImm, h]

/-- The reload of a zeroing whose base has the save slot `q`. -/
theorem reloadArrImm_zeroArr {mbr : String → Option String} {b q : String} (n w : Nat)
    (h : mbr b = some q) (hq : faB q = false) :
    reloadArrImm mbr (.Lopn [.reg b] "ZEROARR" [.imm n, .imm w]) =
      some [.Lopn [.reg reloadScratch2] "MOVQ" [.reg q],
        .Lopn [] "ZEROARR" [.reg reloadScratch2, .imm n, .imm w]] := by
  simp [reloadArrImm, h, ptrLoad_qsave hq]

/-- The reload of a constant-index store whose base has the save slot `q`. -/
theorem reloadArrImm_storeImm {mbr : String → Option String} {b q : String} (d v : String)
    (k : Nat) (h : mbr b = some q) (hq : faB q = false) :
    reloadArrImm mbr (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k]) =
      some [.Lopn [.reg reloadScratch2] "MOVQ" [.reg q],
        .Lopn [.reg reloadScratch2] "STOREIMM" [.reg reloadScratch2, .reg v, .imm k]] := by
  simp [reloadArrImm, h, ptrLoad_qsave hq]

/-- An instruction other than `ZEROARR` and `STOREIMM` has no constant-shape base reload. -/
theorem reloadArrImm_of_ne (mbr : String → Option String) {ds ss : List LOperand} {opn : String}
    (h1 : opn ≠ "ZEROARR") (h2 : opn ≠ "STOREIMM") :
    reloadArrImm mbr (.Lopn ds opn ss) = none := by
  unfold reloadArrImm
  split <;> simp_all

/-- Off the memref path (no base has a save slot) there is no constant-shape base reload. -/
theorem reloadArrImm_of_noSlot {mbr : String → Option String} (h : ∀ b, mbr b = none)
    (i : LinstrR) : reloadArrImm mbr i = none := by
  unfold reloadArrImm
  split <;> simp_all

/-- **The forms of a constant-shape base reload.** A reload `l` of `reloadArrImm` is the
    pointer load of the reload slot `q` of the base `b` into `R14` followed by the physical form
    of a zeroing of `b` or of a constant-index store into `b`, both addressed through `R14`. -/
theorem reloadArrImm_eq_some {mbr : String → Option String} {i : LinstrR} {l : List LinstrR}
    (h : reloadArrImm mbr i = some l) :
    ∃ b q, mbr b = some q ∧
      ((∃ n w, i = .Lopn [.reg b] "ZEROARR" [.imm n, .imm w] ∧
          l = [ptrLoad q, .Lopn [] "ZEROARR" [.reg reloadScratch2, .imm n, .imm w]]) ∨
        (∃ d v k, i = .Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k] ∧
          l = [ptrLoad q,
            .Lopn [.reg reloadScratch2] "STOREIMM" [.reg reloadScratch2, .reg v, .imm k]])) := by
  unfold reloadArrImm at h
  split at h
  · grind only [Option.map_eq_some_iff]
  · grind only [Option.map_eq_some_iff]
  · cases h

/-- Legalize a two-address binop `op dst, src` (sources `[dst, src]`) so it
    carries **no** memory (spill) operand inside the binop itself — every `k.N`
    name appears only in a MOV source or destination. jasmin's `asmgen` refuses
    to map a memory `lexpr` to a register operand of a non-MOV `Lopn`, so any
    spill must be reloaded through one of the two reserved scratches.

    Four cases by `(dst.isSpill, src.isSpill)`:

    * `(false, false)` — both registers: emit the direct
      `op dst, src` (1 `Lopn`).
    * `(false, true)` — register destination, spill source: route `src` through
      `R15`, `mov R15, src; op dst, R15` (2 `Lopn`s).
    * `(true, false)` — spill destination, register source: route `dst` through
      `R15`, `mov R15, dst; op R15, src; mov dst, R15` (3 `Lopn`s).
    * `(true, true)` — both spills: route `dst` through `R15` and `src` through
      `R14`, `mov R15, dst; mov R14, src; op R15, R14; mov dst, R15`
      (4 `Lopn`s).

    Every emitted `Lopn` is either a MOV (which permits a memory lexpr/rexpr)
    or has all of its non-MOV register operands in `R15`/`R14`. -/
def legalizeBinop (dst src : LOperand) (opn : String) (mov : String := "MOV") :
    List LinstrR :=
  match dst.isSpill, src.isSpill with
  | false, false =>
      [.Lopn [dst] opn [dst, src]]
  | false, true =>
      [.Lopn [.reg reloadScratch] mov [src],
       .Lopn [dst] opn [dst, .reg reloadScratch]]
  | true, false =>
      [.Lopn [.reg reloadScratch] mov [dst],
       .Lopn [.reg reloadScratch] opn [.reg reloadScratch, src],
       .Lopn [dst] mov [.reg reloadScratch]]
  | true, true =>
      [.Lopn [.reg reloadScratch] mov [dst],
       .Lopn [.reg reloadScratch2] mov [src],
       .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .reg reloadScratch2],
       .Lopn [dst] mov [.reg reloadScratch]]

/-- The two-address binop alphabet of the physical lowering: the mnemonics, after
    their width tag is stripped, that `physBodyRmap` and its ABI variants lower
    through `lowerTwoAddr` (and so through `legalizeBinop`). -/
def isTwoAddrBinop (opn : String) : Bool :=
  ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR"].contains
    (stripWidthTag opn)

/-- Legalize a register copy `mov dst, src` (sources `[src]`) so it carries at
    most one memory (spill) operand. When BOTH `dst` and `src` are spill slots,
    `mov [mem], [mem]` is illegal; route through the reserved reload scratch:
    `mov R15, src; mov dst, R15`. Otherwise emit the single copy unchanged. -/
def legalizeMov (dst src : LOperand) (mov : String := "MOV") : List LinstrR :=
  if dst.isSpill && src.isSpill then
    [.Lopn [.reg reloadScratch] mov [src],
     .Lopn [dst] mov [.reg reloadScratch]]
  else
    [.Lopn [dst] mov [src]]

/-- Legalize a **single-source memory LOAD** op `Lopn [dst] opn [src]` (a `LOAD`
    or register-indexed `LOADIDX`, whose source is always a memory operand — a
    spill slot or a `(%base,%idx,scale)` SIB element) so the emitted x86 carries
    at most one memory operand.

    The owned printer renders such a load as `mov<sz> src, dst`. When the
    destination `dst` is itself a spill slot (a memory operand), that single line
    is an illegal `mov mem, mem` (the whole-state ChaCha/SHA/Keccak/NTT kernels
    hit this when the loaded word's SSA result lands in a stack slot). Route the
    load through the reserved primary scratch `R15`:
    `op R15, src; mov dst, R15` — the load writes the register `R15` (one memory
    operand: the source), then a plain `mov` stores `R15` to the stack slot (one
    memory operand: the destination). Both moves are legal.

    The SIB base/index of a `LOADIDX` are allocatable GP registers (never `R15`,
    which is reserved and never an allocation target — `physRegName`), so the
    routing scratch never collides with the address registers. When `dst` is a
    register, the direct one-line load is already legal and is emitted unchanged.

    The split is denotation-preserving: `dst ← src` equals `R15 ← src; dst ← R15`
    on the abstract machine (`R15` is dead at this point — it is only ever the
    legalization scratch). The trailing reload `mov` inherits the load's width
    via `mov` so the full loaded value survives into the slot. -/
def legalizeMemLoad (dst src : LOperand) (opn : String) (mov : String := "MOV") :
    List LinstrR :=
  -- The trailing `mov dst, R15` must store the **load width** so a 64-bit value
  -- the `LOADIDX` parked in R15 is not truncated by a 32-bit `movl` into the
  -- slot. The owned printer sizes a `LOADIDX` by its SIB scale (`scale·8` bits),
  -- so when `src` is a SIB element with an 8-byte stride the spill-store is
  -- `MOV:64`; otherwise it inherits the op's `mov` width.
  let storeMov : String :=
    match src with
    | .arrIdx _ _ scale => if scale ≥ 8 then "MOV:64" else mov
    | _ => mov
  -- First make the SIB source's base/index registers (the address-reload prelude
  -- runs before any value routing reuses `R15`): a spilled SIB base/index would
  -- otherwise render as the `%<UNKNOWN:k.N>` sentinel `as` rejects.
  let (addrPre, src') := legalizeSibElem src
  addrPre ++
  (if dst.isSpill then
    [.Lopn [.reg reloadScratch] opn [src'],
     .Lopn [dst] storeMov [.reg reloadScratch]]
  else
    [.Lopn [dst] opn [src']])

/-- True iff `opn` is a memory-LOAD mnemonic whose source operand is always a
    memory reference (`LOAD` / `LOADIDX`, optionally `:64`-tagged). These are the
    single-source ops that `legalizeMemLoad` must route through `R15` when their
    destination is a spill slot, to avoid an illegal `mov mem, mem`. -/
def isMemLoad (opn : String) : Bool :=
  let base := stripWidthTag opn
  base == "LOAD" || base == "LOADIDX"

/-- Legalize a **memory STORE** op so the emitted x86 carries at most one memory
    operand. The mirror of `legalizeMemLoad`.

    A register-indexed store `Lopn [d] STOREIDX [arrIdx, val]` writes the value
    `val` into the SIB memory destination `(%base,%idx,scale)` (the `Lopn`
    destination `d` names the functionally-updated array — the dialect's
    `stackStore` returns the new array — so it is NOT an x86 operand). The owned
    printer renders it as `mov<sz> val, (%base,%idx,scale)`. When the value source
    `val` is itself a spill slot (a memory operand), that single line is an
    illegal `mov mem, mem` (the whole-state ChaCha/SHA/Keccak/NTT kernels hit this
    when the word being stored lives in a stack slot). Route the value through the
    reserved primary scratch `R15`: `mov R15, val; STOREIDX [arrIdx, R15]` — the
    leading `mov` loads the spill word into the register `R15` (one memory
    operand: the source), then the store writes `R15` to the SIB destination (one
    memory operand: the destination). Both moves are legal.

    `dArr` is the (non-operand) array-result destination, `addr` the SIB / memory
    destination operand, `val` the stored value, `opn` the store mnemonic. The SIB
    base/index of a `STOREIDX` are allocatable GP registers (never `R15`, which is
    reserved and never an allocation target — `physRegName`), so the routing
    scratch never collides with the address registers. When `val` is a register,
    the direct one-line store is already legal and is emitted unchanged.

    The split is denotation-preserving: `[addr] ← val` equals
    `R15 ← val; [addr] ← R15` on the abstract machine (`R15` is dead at this point
    — it is only ever the legalization scratch). The leading reload `mov` inherits
    the store width via `mov` so the full value survives into the scratch. -/
def legalizeMemStore (dArr addr val : LOperand) (opn : String)
    (mov : String := "MOV") : List LinstrR :=
  -- The reload `mov R15, val` must move the **store width** so a 64-bit value
  -- is not truncated by a 32-bit `movl`. The owned printer sizes a `STOREIDX`
  -- by its SIB scale (`scale·8` bits), so when `addr` is a SIB element with an
  -- 8-byte stride the reload is `MOV:64`; otherwise it inherits the op's `mov`
  -- width (the spill-routing reloads elsewhere already key off the `:64` tag).
  let reloadMov : String :=
    match addr with
    | .arrIdx _ _ scale => if scale ≥ 8 then "MOV:64" else mov
    | _ => mov
  -- First make the SIB destination's base/index registers (the base reloads into
  -- the secondary scratch `R14`, disjoint from the value's `R15` routing below),
  -- so a spilled SIB base/index never renders as the `%<UNKNOWN:k.N>` sentinel
  -- `as` rejects (the observed `movq %r15, (%<UNKNOWN:k.5>, %rax, 8)`).
  let (addrPre, addr') := legalizeSibElem addr
  -- BOTH-SPILLED collision arm: when `legalizeSibElem` reloaded a spilled SIB
  -- INDEX into `R15` AND the value is a spill, the value routing below would
  -- reuse `R15` and clobber the index before the store reads it (the observed
  -- `mov 0x28(%rsp),%r15; mov 0x20(%rsp),%r15; mov %r15,(%r14,%r15,8)` — the
  -- query-walk segfault). Fold the SIB address into `R14` with a `LEA:64`
  -- while the index is still live in `R15`; `R15` is then free for the value,
  -- and the store goes through the flat `mem.R14.0` operand (the base in
  -- `R14` is consumed by the `LEA`, so overwriting it is safe).
  match addr', val.isSpill with
  | .arrIdx b i scale, true =>
      if i == reloadScratch then
        addrPre ++
        [.Lopn [.reg reloadScratch2] "LEA:64" [.arrIdx b i scale],
         .Lopn [.reg reloadScratch] reloadMov [val],
         .Lopn [.reg ("mem." ++ reloadScratch2 ++ ".0")] reloadMov
           [.reg reloadScratch]]
      else
        addrPre ++
        [.Lopn [.reg reloadScratch] reloadMov [val],
         .Lopn [dArr] opn [addr', .reg reloadScratch]]
  | _, true =>
      addrPre ++
      [.Lopn [.reg reloadScratch] reloadMov [val],
       .Lopn [dArr] opn [addr', .reg reloadScratch]]
  | _, false =>
      addrPre ++ [.Lopn [dArr] opn [addr', val]]

/-- True iff `opn` is a memory-STORE mnemonic whose value source may be a memory
    (spill) operand (`STORE` / `STOREIDX`, optionally `:64`-tagged). These are the
    two-source ops `legalizeMemStore` must route through `R15` when their value
    source is a spill slot, to avoid an illegal `mov mem, mem`. -/
def isMemStore (opn : String) : Bool :=
  let base := stripWidthTag opn
  base == "STORE" || base == "STOREIDX"

/-- A binop immediate source that does not fit a sign-extended `imm32` must be
    materialised into a register first: x86 has no `op r64, imm64` encoding
    (only `imm32`, sign-extended). Keccak's ι step XORs a full 64-bit round
    constant `RC[round]`, so the U64 path routes any `s1 = #v` with `v ≥ 2^31`
    through `reloadScratch2` (R14) via a `MOV:64 R14, #v` (an x86 `movabs`),
    then uses `R14` as the binop's register source. Returns `(prelude, s1')`.
    For the 32-bit path (`mov ≠ "MOV:64"`) this is the identity `([], s1)`, so
    the existing ChaCha/SHA shapes are unchanged. -/
def materializeWideImm (s1 : LOperand) (mov : String) : List LinstrR × LOperand :=
  match s1, mov with
  | .imm v, "MOV:64" =>
      if 2 ^ 31 ≤ v then
        ([.Lopn [.reg reloadScratch2] "MOV:64" [.imm v]], .reg reloadScratch2)
      else ([], s1)
  | _, _ => ([], s1)

/-- Lower a single resolved binop into its two-address `LinstrR` sequence over
    physical operand names, legalizing any two-memory-operand instruction by
    routing one source through the reserved reload scratch.
    `dst`, `s0`, `s1` are physical operand names; `opn` the producer mnemonic.
    When `dst = s0` the RA already placed `dst` on `s0`'s register, so the leading
    `mov` collapses; otherwise a `mov dst, s0` (itself legalized) precedes the
    op (itself legalized). A wide U64 immediate `s1` is materialised into a
    register first (`materializeWideImm`). -/
def lowerTwoAddr (dst s0 s1 : LOperand) (opn : String) (mov : String := "MOV") :
    List LinstrR :=
  let (immPre, s1') := materializeWideImm s1 mov
  if dst = s0 then
    immPre ++ legalizeBinop dst s1' opn mov
  else
    legalizeMov dst s0 mov ++ immPre ++ legalizeBinop dst s1' opn mov

/-- Lower a constant-shift binop (`SHL`/`SHR` with a compile-time shift count)
    into two-address form with the count as an **immediate** operand (`#v`). x86
    forces a register shift count into `CL`; an immediate `imm8` count needs no
    forced register, so emitting the (compile-time-constant) ChaCha rotate amounts
    as immediates removes the `(compile_arg) bad forced register` constraint.

    `dst`, `s0` are physical operand names; `v` the immediate shift amount.

    Even though the immediate source carries no memory operand, jasmin's `asmgen`
    still refuses a spill `lexpr` as the destination of a non-MOV `Lopn` — so a
    `SHL` whose destination is a spill (`k.N`) must be reloaded through the
    primary scratch `R15`:

    * `dst = s0`, `dst` register: single `op dst, #v`.
    * `dst = s0`, `dst` spill: `mov R15, dst; op R15, #v; mov dst, R15`.
    * `dst ≠ s0`, `dst` register: `mov dst, s0; op dst, #v` (the leading mov is
      legalized — `s0` may itself be a spill, which is a legal MOV source).
    * `dst ≠ s0`, `dst` spill: `mov R15, s0; op R15, #v; mov dst, R15` (the
      leading mov pulls `s0` directly into the scratch, avoiding a redundant
      reload of `dst`'s stale value). -/
def lowerTwoAddrShiftImm (dst s0 : LOperand) (v : Nat) (opn : String)
    (mov : String := "MOV") : List LinstrR :=
  if dst.isSpill then
    -- Reload-pass: thread the shift through `R15`. Source the scratch from `s0`
    -- (the value being operated on); when `dst = s0` they coincide and this is
    -- the canonical `mov R15, dst; op R15, #v; mov dst, R15` shape.
    [.Lopn [.reg reloadScratch] mov [s0],
     .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .imm v],
     .Lopn [dst] mov [.reg reloadScratch]]
  else if dst = s0 then
    [.Lopn [dst] opn [dst, .imm v]]
  else
    legalizeMov dst s0 mov ++ [.Lopn [dst] opn [dst, .imm v]]

/-- True iff `opn` is a **native immediate shift / rotate** mnemonic
    (`ROR:n` / `ROL:n` / `SHL:n` / `SHR:n` / `SAR:n`, optionally `:64`-tagged),
    the single-source form `opToLinstrR` emits for `.rorImm` / `.shlImm` /
    `.shrImm`. The count is carried IN the mnemonic, so these are a
    one-source unary op (`Lopn [d] "ROR:n" [s]`), distinct from the two-source
    register `SHL`/`SHR` the `isBinop` arm re-lowers. -/
def isNativeShiftRotate (opn : String) : Bool :=
  let base := stripWidthTag opn
  ["ROR:", "ROL:", "SHL:", "SHR:", "SAR:"].any (fun p => p.isPrefixOf base)

/-- Lower a native immediate shift / rotate (`ROR:n` / `SHL:n` / …, the unary
    `opToLinstrR`-emitted form of `.rorImm` / `.shlImm` / `.shrImm`) into a form
    whose operand is never a memory (spill) slot. x86 accepts a memory operand on
    `ror $n, mem`, but the **owned printer** (`LprogAsmPrinter`) renders the
    two-address `dst ≠ src` case as `mov src, dst; ror $n, dst`; when both `dst`
    and `src` are spills, that leading `mov` is an illegal `mov mem, mem`. The
    `.rorImm`/`.shlImm`/`.shrImm` op binds a fresh SSA result from its one value
    operand, so after RA `dst` and `src` are independent slots, either of which
    the spilling allocator may place in memory. When either is a spill, thread
    the value through the primary reload scratch `R15`:
    `mov R15, src; ror $n R15; mov dst, R15` (mirrors `lowerTwoAddrShiftImm`).

    `dst`, `s` are physical operand names (post-RA), `opn` the native mnemonic.
    * neither a spill: single `op dst` after the printer's own `mov src,dst`
      collapse (or it renders `mov src,dst; ror $n,dst`, both legal reg forms).
    * either a spill: `mov R15, s; op R15; mov dst, R15` — all three legal. -/
def lowerNativeShiftRotate (dst s : LOperand) (opn : String) (mov : String) :
    List LinstrR :=
  if dst.isSpill || s.isSpill then
    [.Lopn [.reg reloadScratch] mov [s],
     .Lopn [.reg reloadScratch] opn [.reg reloadScratch],
     .Lopn [dst] mov [.reg reloadScratch]]
  else
    [.Lopn [dst] opn [s]]

/-! ### 7e. The physical body and export

We re-walk `comToBody` (the same SSA body), remap every operand name through the
linear-scan physical map, and re-lower each binary `Lopn` to two-address form.
Non-binop `Lopn`s (LOAD/STORE/casts/calls) and the `Lret` pass through with
operands remapped. -/

/-! ### 7c′. Caller-save barrier for an in-loop `Lcall`

A real `call` (the `loopBodyCallLcmd` SysV sequence, used by MSM's Straus inner
loop and the GGM real AES-PRG node) clobbers all SysV *caller-saved* registers
(`RAX RCX RDX RSI RDI R8 R9 R10 R11`). Any value live across the call — the
accumulator, the loop index `Lidx<d>`, the trip counter `Lctr<d>`, every pinned
invariant base — must therefore sit in a *callee-saved* register
(`RBX RBP R12 R13`) so the callee preserves it. The linear scan (`physScan`) is
oblivious to `Lcall` (`bodyTrace` records only `Lopn` footprints), and its
default pool order `gpRegNames = [RAX, RBX, RCX, …]` assigns the longest-lived
slots — exactly the loop-carried ones — the lowest physical indices, i.e. the
*caller-saved* `RAX`/`RCX`/… So a call-containing body needs two corrections at
operand-remap time:

* **callee-saved-first placement** — permute the allocated GP physical index
  through `calleeSavedFirstOrder` so the earliest-allocated (loop-carried) slots
  land in the callee-saved block first; and
* **literal-ABI pinning** — the marshalling `MOV RDI, …` / `MOV …, RAX` name
  hardware registers literally (the SysV arg/return regs); those names must
  survive the RA verbatim (an `Lcall`'s ABI contract), never be reassigned.

These corrections are provided by `physNameForBody` (used by the aux
name-resolution passes `buildArgMaterializePhys` / `buildArgPtrMaterialize` /
`buildEpilogue`) and `remapOperandCalleeSave`: `calleeFirstPhys` performs the
callee-saved-first placement and `isHwRegName` the literal pinning, both gated on
`bodyHasCall`. The body emit `physBody` / `physBodyWithStores` uses the call-free
`remapOperand` (so the faithfulness-chain parametric proofs see the plain
physical lookup). The callee-saved registers a loop-carried value lands in are
already saved/restored by `buildPrologue` / `calleeSaveRestoreEpilogue`. -/

/-- True iff the body issues a real `LinstrR.Lcall` (the caller-save barrier
    engages for such bodies; a call-free body is unaffected). -/
def bodyHasCall (body : Lcmd) : Bool :=
  body.any (fun i => match i.li_i with | .Lcall _ _ => true | _ => false)

/-- The literal hardware register names — the full physical GP file (`RSP`
    included: it is the stack pointer and must never be reassigned either) plus
    the SysV SSE arg registers (`XMM0…XMM7`). A name in this set is a *literal*
    hardware register (the SysV arg/return registers the marshalling names — GP
    `RDI`/`RSI`/`RAX` from `loopBodyCallLcmd`, xmm `XMM0…XMM7` from
    `loopBodyCallLcmdClassed`), pinned to itself by the call barrier rather than
    routed through the RA. An SSA value is never named `XMM<i>` literally (a
    vector value is a fresh SSA name resolved to an xmm *by* the RA), so pinning
    the SSE arg names is additive: a call-free / GP-only body is unaffected. -/
def hwRegNames : List String :=
  gpRegNames ++ [reloadScratch2, reloadScratch, "RSP"] ++ sysvSseArgRegs

/-- Is `n` a literal hardware GP register name (`hwRegNames`)? -/
def isHwRegName (n : String) : Bool := hwRegNames.contains n

/-- Is `n` a **frame-slot** operand name rather than a register-file name: a GP
    spill `k.N`, a vector spill `kv.N`, an ABI save `qsave.X`, or a
    base-relative memory reference `mem.<base>.<off>`?

    These four prefixes are the operand classes `LprogAsmPrinter.resolveName`
    resolves to a memory address; each denotes a location in the frame, not a
    slot in the register file, so the register allocator's name→physical lookup
    does not apply to it. The SSA names a body carries (`r<d>`, `a<j>`,
    `L<d>_r<k>`, `Lctr<d>`, `Lidx<d>`) begin with none of these prefixes, so no
    allocated name is classified here. -/
def isFrameSlotName (n : String) : Bool :=
  hasPrefix n "k." || hasPrefix n "kv." || hasPrefix n "qsave." || hasPrefix n "mem."

/-- The callee-saved-first permutation of the 13 allocatable GP physical indices
    (`gpRegNames` order). The callee-saved registers come first —
    `RBX(1) RBP(6) R12(11) R13(12)` — then the caller-saved
    `RAX(0) RCX(2) RDX(3) RSI(4) RDI(5) R8(7) R9(8) R10(9) R11(10)`. Applied to a
    call-containing body's allocated GP indices so the longest-lived (loop-carried)
    slots, which the linear scan assigns the lowest indices, land in the
    callee-saved block first (and thus survive a `call`). -/
def calleeSavedFirstOrder : List Nat := [1, 6, 11, 12, 0, 2, 3, 4, 5, 7, 8, 9, 10]

/-- Permute an allocated GP physical index through `calleeSavedFirstOrder`
    (callee-saved registers first). Spill indices (`≥ numGPRegs`) and vector
    indices (`≥ vectorBase`) pass through unchanged. -/
def calleeFirstPhys (p : Nat) : Nat :=
  if p < numGPRegs then calleeSavedFirstOrder.getD p p else p

/-- The allocatable *caller-saved* GP register names — every `gpRegNames` entry
    a SysV leaf `call` may clobber (`RBX RBP R12 R13` are the callee-saved four;
    the reserved scratch `R14`/`R15` are callee-saved and never allocated). A
    loop-invariant pointer base that the looped-call barrier's static
    `calleeFirstPhys` placement overflowed into one of these (a 5th+ loop-carried
    slot, past the four callee-saved registers) is destroyed by an in-loop
    `Lcall` unless it is reloaded from its red-zone qsave slot after the call
    (`ComL.toLfundefPhysAbi`'s `callArgBaseReload`). -/
def callerSavedAllocGPRs : List String :=
  ["RAX", "RCX", "RDX", "RSI", "RDI", "R8", "R9", "R10", "R11"]

/-- Is `n` an allocatable caller-saved GP register name (`callerSavedAllocGPRs`)? -/
def isCallerSavedAllocGPR (n : String) : Bool := callerSavedAllocGPRs.contains n

/-! ### 7c″. Straight-line multi-call barrier (liveness-computed)

`calleeFirstPhys` is a *static* index permutation: the earliest-allocated
(longest-lived) GP slots land in the 4 callee-saved registers, the rest fall
back into the caller-saved block. That is sound for the looped call path (the
loop-carried set is small and earliest-allocated) but NOT for a straight-line
multi-leaf-call orchestration (the ML-DSA keygen caller): with more than 4 raw
GP indices in flight the 5th+ land in `RAX`/`RCX`/… and are destroyed by the
next `call`'s return, and an index permuted into a SysV argument register
(`RDX`/`RSI`/`RDI`/…) is overwritten by a later call site's own marshalling
`MOV`s before its last read (the ≥3-arg `bytes_concat_6` marshal defect).

For a body that is straight-line (no label / branch) AND issues real `Lcall`s
(`bodyStraightCall`), the barrier is therefore *liveness-computed*
(`straightCallRelocTable`) instead of static:

* a raw GP index hosting a slot whose live range crosses a `call` — or a
  write-only slot (an output read only after the body, e.g. by an inline out
  store / the return; conservatively treated as live to the end) — is homed
  **callee-saved** (`RBX RBP R12 R13`), then **stack-spilled** (`k.N`, inside
  the printer-allocated frame, which survives calls) once those run out;
* every other raw GP index is homed in `R10`/`R11` — the only caller-saved
  registers no SysV marshal (`RDI…R9`) or return-capture (`RAX`) `MOV` ever
  writes — then spilled likewise.

So NO allocated value ever resolves to `RAX`/`RDI`/`RSI`/`RDX`/`RCX`/`R8`/`R9`:
every call-marshal source reads from a callee-saved / `R10` / `R11` / frame-spill
home, which no earlier marshal `MOV` of the same call site can have overwritten —
the marshal read-after-overwrite hazard is structurally impossible. Literal SysV
hardware names stay pinned (`isHwRegName`), exactly as in the looped barrier.
A vector (`XMM`) value live across a call remains unsupported (SysV has no
callee-saved xmm; documented at `loopBodyCallLcmdClassed`).

The looped call path (`Llabel`/`Lcond` back-edges — MSM / GGM) keeps the static
`calleeFirstPhys` placement byte-identically, and a call-free body is
untouched. -/

/-- True iff the body is a **straight-line call body**: it issues a real
    `Lcall` and carries no intra-body control flow (no label / branch / goto).
    Gates the liveness-computed straight-line call barrier
    (`straightCallRelocTable`); the looped call path (`Llabel`/`Lcond` present)
    keeps the static `calleeFirstPhys` placement, and a call-free body is
    unaffected. -/
def bodyStraightCall (body : Lcmd) : Bool :=
  bodyHasCall body && !body.any (fun i =>
    match i.li_i with
    | .Llabel _ _ => true
    | .Lcond _ _ => true
    | .Lgoto _ => true
    | .Ligoto _ => true
    | .LstoreLabel _ _ => true
    | _ => false)

/-- The body's `Lcall` positions in `bodyTrace` coordinates: for each call, the
    number of `Lopn` events preceding it (`bodyTrace` indexes `Lopn`s only, so a
    call sits between event `p-1` and event `p`). A slot with live range
    `[st, en]` is live across that call iff `st < p ∧ p ≤ en`. -/
def bodyCallTracePositions (body : Lcmd) : List Nat :=
  (body.foldl (fun (acc : List Nat × Nat) i =>
      match i.li_i with
      | .Lopn _ _ _ => (acc.1, acc.2 + 1)
      | .Lcall _ _ => (acc.2 :: acc.1, acc.2)
      | _ => acc) ([], 0)).1.reverse

/-- The callee-saved pool of the straight-line call barrier, as `gpRegNames`
    indices: `RBX(1) RBP(6) R12(11) R13(12)` — preserved by any SysV callee
    (and saved/restored by `buildPrologue` / `calleeSaveRestoreEpilogue`). -/
def straightCallCalleeSavedPool : List Nat := [1, 6, 11, 12]

/-- The non-cross scratch pool of the straight-line call barrier, as
    `gpRegNames` indices: `R10(9) R11(10)` — the only allocatable caller-saved
    registers that no SysV call-marshal (`RDI RSI RDX RCX R8 R9`) or
    return-capture (`RAX`) `MOV` writes, so a value that dies before the next
    `call` is safe there. -/
def straightCallScratchPool : List Nat := [9, 10]

/-- The first fresh GP frame-spill index of an allocation table `tbl`: one more
    than the largest entry `v ≥ numGPRegs` whose slot `s` is of GP class
    (`slotIsVec vecArr s = false`), and `numGPRegs` when there is none. The class
    of an entry is the class of its slot, so a GP spill index at or above
    `vectorBase` counts and a vector-class index does not. -/
def gpSpillBase (vecArr : Array Bool) (tbl : Array Nat) : Nat :=
  tbl.toList.zipIdx.foldl
    (fun b e => if !slotIsVec vecArr e.2 && numGPRegs ≤ e.1 then Nat.max b (e.1 + 1) else b)
    numGPRegs

/-- The list form of `gpSpillBase_eq_of_fit`, from slot `k` on. -/
theorem gpSpillBase_foldl_eq_of_fit (vecArr : Array Bool) :
    ∀ (l : List Nat) (k b : Nat),
      (∀ (i : Nat) (h : i < l.length), slotIsVec vecArr (k + i) = decide (vectorBase ≤ l[i])) →
      (l.zipIdx k).foldl
          (fun b e => if !slotIsVec vecArr e.2 && numGPRegs ≤ e.1 then Nat.max b (e.1 + 1)
            else b) b =
        l.foldl (fun b v => if numGPRegs ≤ v && v < vectorBase then Nat.max b (v + 1) else b) b
  | [], _, _, _ => rfl
  | v :: vs, k, b, hfit => by
    have h0 : slotIsVec vecArr k = decide (vectorBase ≤ v) := by
      exact hfit 0 (by simp)
    simp only [List.zipIdx_cons, List.foldl_cons]
    rw [h0]
    have hstep : (if (!decide (vectorBase ≤ v) && decide (numGPRegs ≤ v)) = true then
          Nat.max b (v + 1) else b) =
        (if (decide (numGPRegs ≤ v) && decide (v < vectorBase)) = true then
          Nat.max b (v + 1) else b) := by
      by_cases h1 : vectorBase ≤ v <;> by_cases h2 : numGPRegs ≤ v <;> simp [h1, h2]
    rw [hstep]
    exact gpSpillBase_foldl_eq_of_fit vecArr vs (k + 1) _ fun i hi => by
      have := hfit (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- **Fresh spill base under the fit.** When the class of every slot is the
    class the index threshold reads (every GP-class entry is `< vectorBase`,
    every vector-class entry `≥ vectorBase`), `gpSpillBase` is the threshold
    scan over the entries `numGPRegs ≤ v < vectorBase`. -/
theorem gpSpillBase_eq_of_fit (vecArr : Array Bool) (tbl : Array Nat)
    (hfit : ∀ (s : Nat) (h : s < tbl.size), slotIsVec vecArr s = decide (vectorBase ≤ tbl[s])) :
    gpSpillBase vecArr tbl =
      tbl.foldl (fun b v => if numGPRegs ≤ v && v < vectorBase then Nat.max b (v + 1) else b)
        numGPRegs := by
  unfold gpSpillBase
  rw [← Array.foldl_toList]
  exact gpSpillBase_foldl_eq_of_fit vecArr tbl.toList 0 numGPRegs fun i hi => by
    simpa using hfit i (by simpa using hi)

/-- The straight-line call barrier's relocation of **raw** allocated GP indices
    (the `physScan` output, `< numGPRegs`) onto call-safe homes. For each raw
    index actually used by a non-hardware-named slot:

    * **crossing** (some hosted slot is live across an `Lcall`, or is
      write-only — an output read only after the body, treated as live to the
      end): the next free index from `straightCallCalleeSavedPool`, else a
      fresh frame-spill index (above every spill the scan already assigned);
    * **non-crossing**: the next free index from `straightCallScratchPool`,
      else a fresh frame-spill index.

    Unused raw indices keep their identity image (nothing resolves through
    them: literal hardware names are pinned by `isHwRegName` before the table
    is consulted). The synthetic `%livepin` liveness pin is ignored. Raw spill
    (`≥ numGPRegs`) and vector (`≥ vectorBase`) indices pass through unchanged
    (`straightCallPhys`). -/
def straightCallRelocTableCore (body : Lcmd) (tbl : Array Nat) : Array Nat :=
  Id.run do
    let tr := bodyTrace body
    let calls := bodyCallTracePositions body
    let names : Array String := (bodyNames body).toArray
    let univ := physUniverse tr
    -- Slots read by at least one event (a write-only slot is presumed an
    -- output — read only after the body — and treated as call-crossing).
    let mut isRead : Array Bool := Array.replicate univ false
    for ev in tr do
      for s in ev.rds do
        if s < isRead.size then isRead := isRead.set! s true
    -- Per raw GP index: used by a non-hw slot / hosts a crossing non-hw slot.
    let mut usedRaw : Array Bool := Array.replicate numGPRegs false
    let mut crossRaw : Array Bool := Array.replicate numGPRegs false
    for it in physLiveItems tr do
      let s := it.1
      let en := it.2.2
      let nm := names[s]?.getD ""
      -- An argument slot (`a<j>`) is materialized at ENTRY by
      -- `buildArgPtrMaterialize` (before the first trace event), so its
      -- effective live range starts at 0: an argument first read after a
      -- call must count as call-crossing (its home is written before the
      -- call runs).
      let st := if nm.startsWith "a" && (strDropToNat? nm 1).isSome
                then 0 else it.2.1
      if nm != "%livepin" && !isHwRegName nm then
        let raw := physMapTabled tbl s
        if raw < numGPRegs then
          usedRaw := usedRaw.set! raw true
          let crossing := calls.any (fun p => st < p && p ≤ en)
                            || !(isRead[s]?.getD true)
          if crossing then crossRaw := crossRaw.set! raw true
    -- Fresh spill indices start above every spill the scan already assigned.
    let spillBase := gpSpillBase (bodyVecSlots body) tbl
    let mut reloc : Array Nat := Array.range numGPRegs
    let mut crossPool := straightCallCalleeSavedPool
    let mut nonCrossPool := straightCallScratchPool
    let mut nextSpill := spillBase
    for raw in [0:numGPRegs] do
      if usedRaw[raw]?.getD false then
        if crossRaw[raw]?.getD false then
          match crossPool with
          | r :: rest => reloc := reloc.set! raw r; crossPool := rest
          | [] => reloc := reloc.set! raw nextSpill; nextSpill := nextSpill + 1
        else
          match nonCrossPool with
          | r :: rest => reloc := reloc.set! raw r; nonCrossPool := rest
          | [] => reloc := reloc.set! raw nextSpill; nextSpill := nextSpill + 1
    return reloc

/-- `straightCallRelocTableCore`, recomputed per call. The barrier resolver
    `physNameForBody` consults this once per operand, so the table is
    recomputed O(operands) times per export — acceptable at the straight-line
    call bodies' sizes (≤ a few hundred instructions). A pointer-keyed
    global-ref cache here (the `bodyNameInfoCacheRef` pattern, two-key
    variant) corrupted the mimalloc heap under `lake build`'s async
    elaboration tasks (mi_malloc SIGSEGV in a later compile step), so the
    compiled form stays the pure recomputation. -/
def straightCallRelocTable (body : Lcmd) (tbl : Array Nat) : Array Nat :=
  straightCallRelocTableCore body tbl

/-- Resolve logical slot `s` to its physical index under the straight-line call
    barrier: the raw scan index relocated through `straightCallRelocTable` when
    it is an allocatable GP register; spill (`≥ numGPRegs`) and vector
    (`≥ vectorBase`) indices pass through unchanged. -/
def straightCallPhys (body : Lcmd) (tbl : Array Nat) (s : Nat) : Nat :=
  let raw := physMapTabled tbl s
  if raw < numGPRegs then (straightCallRelocTable body tbl)[raw]?.getD raw
  else raw

/-- Resolve an SSA register name `n` to its physical register name for `body` —
    the single source of truth shared by `remapOperand` and every auxiliary
    name-resolution pass (`buildArgMaterializePhys`, `buildArgPtrMaterialize`,
    `buildEpilogue`, and the looped export's `memrefBaseReload`).

    A **frame-slot** name (`isFrameSlotName`: `k.`/`kv.`/`qsave.`/`mem.`) names a
    location in the frame, which the printer resolves itself, and passes through
    unchanged on every path.

    For a call-free body this is the post-RA lookup
    `physRegName (physMapTabled tbl (nameSlot body n))`. For a body that issues a
    real `Lcall` (`bodyHasCall`), the caller-save barrier engages: a literal
    hardware register (`isHwRegName`, the SysV arg/return marshalling names) is
    pinned to itself, and every other allocated GP slot is routed

    * through the **liveness-computed** straight-line relocation when the body
      is a straight-line call body (`bodyStraightCall`): the relocation is
      COMPOSED INTO `tbl` once at the export site
      (`straightCallComposeTable` in `comToLfundefPhysAbi` — call-crossing
      slots callee-saved-then-spilled, the rest to the marshal-untouched
      `R10`/`R11`-then-spill pool), so the lookup here is the plain post-RA
      one and the frame sizing sees the relocation's fresh spill indices; or
    * through the static callee-saved-first permutation (`calleeFirstPhys`)
      on the looped call path (`Llabel`/`Lcond` back-edges present).

    The prologue / arg materialize / epilogue agree with the barrier-relocated
    body (all resolve through THIS function, over the SAME composed table). -/
def physNameForBody (body : Lcmd) (tbl : Array Nat) (n : String) (abi : IsaAbi := x86Abi) :
    String :=
  if isFrameSlotName n then n
  else if bodyHasCall body then
    if isHwRegName n then n
    else if bodyStraightCall body then
      physRegName (physMapTabled tbl (nameSlot body n)) abi
    else physRegName (calleeFirstPhys (physMapTabled tbl (nameSlot body n))) abi
  else
    physRegName (physMapTabled tbl (nameSlot body n)) abi

-- Static checks pinning the frame-slot passthrough: a GP spill, a vector spill,
-- an ABI save and a base-relative memory reference each resolve to themselves,
-- under a call-free body and under a body that issues a call, while an SSA name
-- still resolves through the allocation table.
#guard physNameForBody [] #[] "mem.RSP.0" = "mem.RSP.0"
#guard physNameForBody [] #[] "k.3" = "k.3"
#guard physNameForBody [] #[] "kv.1" = "kv.1"
#guard physNameForBody [] #[] "qsave.RDX" = "qsave.RDX"
#guard physNameForBody [⟨0, .Lcall none ("f", 0)⟩] #[] "mem.RSP.96" = "mem.RSP.96"
#guard physNameForBody [⟨0, .Lcall none ("f", 0)⟩] #[] "qsave.RDX" = "qsave.RDX"
#guard physNameForBody [] #[] "r0" = "RAX"

/-- Compose the straight-line call relocation into an allocation table: every
    GP entry is routed through `straightCallRelocTable` (computed ONCE — the
    per-name `straightCallPhys` consultation recomputed the liveness scan per
    operand), spill/vector entries pass through. Applied at the export site so
    every seam (prologue, arg materialize, body remap, epilogue, frame sizing)
    reads one coherent table — in particular the relocation's FRESH spill
    indices participate in the frame-size maximum. -/
def straightCallComposeTable (body : Lcmd) (tbl : Array Nat) : Array Nat :=
  if bodyStraightCall body then
    let reloc := straightCallRelocTable body tbl
    tbl.map (fun v => if v < numGPRegs then reloc[v]?.getD v else v)
  else tbl

/-- Remap a single `LOperand`'s register name through the physical map of `tr`,
    given the body it came from (for slot indexing). Immediates / compile-time
    array elements pass through. A register-indexed (SIB) operand
    `arrIdx base idx scale` has **both** its base pointer and index remapped to
    physical registers (both are tracked register-file sources via
    `LOperand.srcRegNames`); without this the SIB's `base`/`idx` would keep their
    raw SSA arg names (`a0`/`a1`/…) and the printer would render
    `%<UNKNOWN:aN>`.

    Each register name is the post-RA physical lookup
    `physRegName (physMapTabled tbl (nameSlot body n))`. This is the call-free
    renaming; the `Lcall` caller-save variant is `remapOperandCalleeSave`. -/
def remapOperand (body : Lcmd) (tbl : Array Nat) (o : LOperand) (abi : IsaAbi := x86Abi) :
    LOperand :=
  match o with
  | .reg n => .reg (physRegName (physMapTabled tbl (nameSlot body n)) abi)
  | .arrIdx base idx scale =>
      .arrIdx (physRegName (physMapTabled tbl (nameSlot body base)) abi)
              (physRegName (physMapTabled tbl (nameSlot body idx)) abi)
              scale
  | o => o

/-- `remapOperand` with the `Lcall` caller-save barrier: each register name is
    resolved by `physNameForBody`, so for a body that issues a real call the
    loop-carried slots are routed to callee-saved registers (`calleeFirstPhys`)
    and the SysV hardware names are pinned to themselves. `physBody` selects this
    for `bodyHasCall` bodies; a call-free body uses `remapOperand`. -/
def remapOperandCalleeSave (body : Lcmd) (tbl : Array Nat) (o : LOperand)
    (abi : IsaAbi := x86Abi) : LOperand :=
  match o with
  | .reg n => .reg (physNameForBody body tbl n abi)
  | .arrIdx base idx scale =>
      .arrIdx (physNameForBody body tbl base abi) (physNameForBody body tbl idx abi) scale
  | o => o

/-- A shift-count immediate oracle: maps the SSA source register name of a
    `SHL`/`SHR` shift-count operand to its compile-time constant value, when that
    source is a constant input (so the producer can render the count as an `#imm`
    rather than a forced-`CL` register). The default oracle `fun _ => none` keeps
    every count as a register (the original behaviour); a producer that knows its
    shift constants supplies the concrete map (e.g. ChaCha's `a32 … a38 ↦
    16,12,8,7,20,24,25`). -/
abbrev ShiftImmOracle := String → Option Nat

/-- Build a shift-count oracle that resolves a count register by **dataflow**:
    a body `MOV[:w] r, #v` binding (the rendering of a nullary `regConst v`,
    `opToLinstrR`) defines `r := v`, so any `SHL`/`SHR` whose count source is
    that `r` can take the count as an `#imm` operand. This lets a producer whose
    shift counts are materialised by `regConst` bindings (rather than constant
    *inputs*, as ChaCha/SHA/Keccak use) still avoid the x86 forced-`CL`
    constraint, with no per-binding oracle to hand-write.

    `regName` is De-Bruijn-unique (`"r" ++ toString depth`), but a body need not be
    in SSA form: the loop frames of the region export seed a trip index with
    `MOV r,#0`, advance it with `ADD` and reset it after the exit label. A name
    therefore resolves only when the body writes it exactly once, by that `MOV`; a
    name written by another `Lopn` or more than once resolves to none. Only
    single-source immediate MOVs contribute (the `regConst` shape); two-address
    legalization MOVs (`MOV dst, src0`) carry a register source and are ignored. -/
def movImmTable (body : Lcmd) : Array (Option Nat) := Id.run do
  -- Index the resolved counts by the De-Bruijn depth `k` encoded in the body
  -- name `regName k = "r" ++ toString k`, in a single `Array (Option Nat)` pass.
  -- This avoids String-keyed hashing over a ~364k-instruction body: build is
  -- O(n), lookup is O(1) on the parsed index. Names that aren't `r<k>` (e.g.
  -- `a<j>` args) never name a `regConst`, so they're absent and resolve to none.
  -- `w` counts the writes of each name by an `Lopn`.
  let mut a : Array (Option Nat) := Array.replicate body.length none
  let mut w : Array Nat := Array.replicate body.length 0
  for i in body do
    match i.li_i with
    | .Lopn outs opn ins =>
        for o in outs do
          match o with
          | .reg d =>
              if d.startsWith "r" then
                match strDropToNat? d 1 with
                | some k => if k < w.size then w := w.set! k (w[k]! + 1)
                | none => pure ()
          | _ => pure ()
        match outs, ins with
        | [.reg d], [.imm v] =>
            if (stripWidthTag opn) == "MOV" then
              if d.startsWith "r" then
                match strDropToNat? d 1 with
                | some k => if k < a.size then a := a.set! k (some v)
                | none => pure ()
        | _, _ => pure ()
    | _ => pure ()
  return (a.zip w).map fun (v, n) => if n == 1 then v else none

/-- Resolve a body register name `r<k>` against a prebuilt `movImmTable`. -/
def movImmLookup (tbl : Array (Option Nat)) (n : String) : Option Nat :=
  if n.startsWith "r" then
    match strDropToNat? n 1 with
    | some k => if k < tbl.size then tbl[k]! else none
    | none => none
  else none

/-- A `ShiftImmOracle` resolving `regConst`-defined shift counts by dataflow
    (see `movImmTable`). The table is built once; the returned closure captures
    it. (Provided for callers that want a standalone oracle; the ABI export
    builds the table inline so single-evaluation is guaranteed.) -/
def movImmOracle (body : Lcmd) : ShiftImmOracle :=
  let tbl := movImmTable body
  fun n => movImmLookup tbl n

/-- The two-address physical body lowering, parametric in the operand renamer
    `rmap`. `physBody` instantiates it with the call-free `remapOperand`;
    `physBodyCalleeSave` with the `Lcall` caller-save `remapOperandCalleeSave`. -/
def physBodyRmap (rmap : LOperand → LOperand) (shiftImm : ShiftImmOracle)
    (body : Lcmd) : Lcmd :=
  -- two-address mnemonics that take exactly two register sources (the optional
  -- `:64` width tag is stripped before the membership test).
  let isBinop (opn : String) : Bool := isTwoAddrBinop opn
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  -- The injected legalization moves inherit the op's width: a `:64` op routes
  -- its reload moves through `MOV:64` so the full 64-bit value survives.
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  -- Detect a constant shift count: either `s1` is already an `.imm` (producer-
  -- level `ImmSlotMap` substitution) or its SSA register name is covered by the
  -- legacy `ShiftImmOracle`. Both routes funnel into `lowerTwoAddrShiftImm`.
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  body.flatMap (fun i =>
    match i.li_i with
    -- Only the two-source binop alphabet is re-lowered to destructive
    -- two-address form. Three-source ops (the carry-chain `ADCX`/`ADOX`
    -- + carry-out, which carry an extra `reg 1` carry-in) and every other
    -- `Lopn` (MULXHI, LOAD/STORE, casts, MOV) fall through to the general
    -- arm with **all** operands remapped — never truncated to two sources.
    | .Lopn (d :: _) opn ((s0 :: s1 :: _) : List LOperand) =>
        if isBinop opn then
          -- a constant-count shift: emit the count as an immediate
          match (if isShift opn then shiftImmVal s1 else none) with
          | some v =>
              (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
                (fun r => ⟨i.li_ii, r⟩)
          | none =>
              (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
                (fun r => ⟨i.li_ii, r⟩)
        else
          match i.li_i with
          -- A `STOREIDX` (register-indexed store: srcs are exactly
          -- `[arrIdx, val]`) whose remapped value source is a spill slot would
          -- render as an illegal `mov mem, mem` (the symmetric mirror of the
          -- LOAD case). Route the value through `R15` (store fix).
          | .Lopn [d'] opn' [addr, val] =>
              if isMemStore opn' then
                (legalizeMemStore (rmap d') (rmap addr) (rmap val) opn' (movFor opn')).map
                  (fun r => ⟨i.li_ii, r⟩)
              else
                [⟨i.li_ii, .Lopn [rmap d'] opn' [rmap addr, rmap val]⟩]
          | .Lopn dsts opn srcs =>
              [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
          | other => [⟨i.li_ii, other⟩]
    -- Native immediate shift / rotate (`ROR:n` / `SHL:n` / …): a one-source
    -- in-place op. Route a spilled operand through R15 so the owned printer
    -- never emits `mov mem, mem` (native-rotate spill legalization).
    | .Lopn [d] opn [s] =>
        if isNativeShiftRotate opn then
          (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
            (fun r => ⟨i.li_ii, r⟩)
        else if isMemLoad opn then
          -- A `LOAD`/`LOADIDX` whose remapped destination is a spill slot would
          -- render as an illegal `mov mem, mem`; route through `R15`.
          (legalizeMemLoad (rmap d) (rmap s) opn (movFor opn)).map
            (fun r => ⟨i.li_ii, r⟩)
        else if stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ" then
          -- A plain register-copy `MOV`/`MOVQ` whose BOTH remapped operands are
          -- spill slots renders as an illegal `mov mem, mem`. This is the 3-deep
          -- block-loop failure mode: at that nesting the loop-carried scalars
          -- (accumulator / index / counter) all spill, so the loop-init and
          -- accumulator-feedback `MOV`s (`whileLcmdNz`, `blockLoopFrame`) get
          -- both operands in the frame. `legalizeMov` routes one side through the
          -- reserved reload scratch `R15` (`mov R15, src; mov dst, R15`), exactly
          -- as the two-address binop's leading-`mov` legalizer does. It is the
          -- identity when at most one operand is a spill, so every existing
          -- kernel's body (no surviving two-spill standalone `MOV`) is
          -- byte-identical. Passing `opn` keeps the move's width tag.
          (legalizeMov (rmap d) (rmap s) opn).map (fun r => ⟨i.li_ii, r⟩)
        else
          [⟨i.li_ii, .Lopn [rmap d] opn [rmap s]⟩]
    | .Lopn dsts opn srcs =>
        [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
    | other => [⟨i.li_ii, other⟩])

/-- The physical two-address body over the call-free `remapOperand` (the renamer
    the parametric faithfulness chain reasons about). Class-aware allocation
    (`bodyPhysTable`): GP bindings → GP regs, vector bindings → XMM. -/
def physBody (shiftImm : ShiftImmOracle) (body : Lcmd) (abi : IsaAbi := x86Abi) : Lcmd :=
  physBodyRmap (fun o => remapOperand body (bodyPhysTable body abi) o abi) shiftImm body

/-- The physical two-address body with the `Lcall` caller-save barrier: the
    operand renamer is `remapOperandCalleeSave`, so a body that issues a real
    `Lcall` pins the SysV hardware names and routes loop-carried slots to
    callee-saved registers. `toLfundefPhys` selects this for `bodyHasCall` bodies. -/
def physBodyCalleeSave (shiftImm : ShiftImmOracle) (body : Lcmd) (abi : IsaAbi := x86Abi) :
    Lcmd :=
  physBodyRmap
    (fun o => remapOperandCalleeSave body
      (straightCallComposeTable body (bodyPhysTable body abi)) o abi)
    shiftImm body

/-- **Materialize the SysV argument registers into the body's register file**
    for the *value-return* export (`comToLfundefPhys`).

    The body reads argument `j` under the name `argName j`, which the linear-scan
    RA has assigned to some physical register `phys(aj)` that is **not** in
    general the SysV call-arg register `callRegArgs[j]` (`[RDI, RSI, …]`).
    `comToLfundefPhys` declares `lfd_arg := callRegArgs.take n` but — unlike the
    pointer-out `comToLfundefPhysAbi`, which calls `buildArgPtrMaterialize` —
    emits **no** copy from `callRegArgs[j]` into `phys(aj)` by itself. Without one
    the body reads whatever was in `phys(aj)` at entry (a callee-saved register it
    just saved, hence a constant value independent of the argument). This emits, for
    each in-range argument `j` whose name `aj` the body actually references, the
    entry copy `phys(aj) ← callRegArgs[j]`, sourcing the *live* SysV register
    directly (there is no red-zone save on this path):

    * `phys(aj) == callRegArgs[j]`: skipped (value already in place);
    * `phys(aj)` a register `R`: `mov R, callRegArgs[j]`;
    * `phys(aj)` a spill `k.N`: `mov R15, callRegArgs[j]; mov [k.N], R15`.

    Copies are emitted in argument order. (For the simple value-return kernels
    that use this path — single-word doubling / reductions — there is no
    cross-argument aliasing where one argument's destination register is another,
    later, argument's live source.) -/
def buildArgMaterializePhys (virt : Lfundef) (tbl : Array Nat)
    (callRegArgs : List String) (abi : IsaAbi := x86Abi) : Lcmd :=
  let body := virt.lfd_body
  let nArgs := min virt.lfd_arg.length callRegArgs.length
  ((callRegArgs.take nArgs).zipIdx).flatMap (fun ⟨abiReg, j⟩ =>
    let nm := argName j
    let used := body.any (fun i =>
      match i.li_i with
      | .Lopn _ _ srcs => srcs.any (fun s =>
          match s with
          | .reg n => n == nm
          | .arrIdx b idx _ => b == nm || idx == nm
          | _ => false)
      | _ => false)
    if !used then []
    else
      -- Resolve through the SAME barrier the body used (`physNameForBody`): a
      -- call-containing body relocated this slot via `calleeFirstPhys`, so the
      -- entry copy must target the relocated register, not the raw one.
      let phys := physNameForBody body tbl nm abi
      let dst : LOperand := .reg phys
      if phys == abiReg then []
      else if dst.isSpill then
        [⟨0, .Lopn [.reg reloadScratch] "MOVQ" [.reg abiReg]⟩,
         ⟨0, .Lopn [dst] "MOVQ" [.reg reloadScratch]⟩]
      else
        [⟨0, .Lopn [dst] "MOVQ" [.reg abiReg]⟩])

/-- The physical `lfundef` for a `Com`: same args/types/result as the virtual
    `comToLfundef`, but a physical, two-address body and result register. The
    result register name is the physical location of the virtual result.
    `shiftImm` (default: none) supplies the constant shift-count → immediate map
    for `SHL`/`SHR` counts. The allocation pool and the argument registers are those
    of `abi`. -/
def comToLfundefPhys {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) (abi : IsaAbi := x86Abi) :
    Lfundef :=
  let virt := comToLfundef com immSlotMap
  -- Class-aware table (matches `physBody`'s `bodyPhysTable`): GP→GP, vector→XMM.
  -- For a pure-scalar body this is `physTable (bodyTrace …)`, so unchanged.
  -- Straight-line call bodies get the liveness relocation composed in once
  -- (`straightCallComposeTable`, identity otherwise) — the SAME table
  -- `physBodyCalleeSave` remaps with, so the seams agree.
  let tbl := straightCallComposeTable virt.lfd_body (bodyPhysTable virt.lfd_body abi)
  -- Resolve through the body's barrier so the `RAX` return epilogue reads the
  -- register a call-containing body left the result in (`physNameForBody`).
  let resPhys := virt.lfd_res.map (fun n => physNameForBody virt.lfd_body tbl n abi)
  -- `assemble_fd` (jasmin `proofs/arch/asm_gen.v`, line 602) requires every
  -- `lfd_arg` entry to be mappable to a typed register via
  -- `asm_typed_reg_of_var`. The virtual `comToLfundef.lfd_arg` carries `aN`
  -- names which are not architecture registers (they would fail
  -- `to_reg`/`to_regx`/`to_xreg`/`to_rflag` and trigger
  -- `asmgen: can not map variable to a register`).
  --
  -- The physical body has already rewritten every `aN` source operand to
  -- its post-RA physical register via the linear-scan map (`physBody` +
  -- `remapOperand`), so the args are not referenced by name in the body.
  -- We therefore project `lfd_arg` to the argument registers `abi.argRegs`
  -- (at `x86Abi` the six SysV registers `[RDI, RSI, RDX, RCX, R8, R9]`, the
  -- `call_reg_args` list `check_call_conv` checks against). The producer
  -- emits up to six arguments; remaining inputs are expected by the body
  -- as register reads (the caller materialises them per the body's RA
  -- choice, which is the trust boundary documented in the bench README).
  let callRegArgs : List String := abi.argRegs
  let nArgsExported : Nat := min virt.lfd_arg.length callRegArgs.length
  let argSig := callRegArgs.take nArgsExported
  let tyinSig := virt.lfd_tyin.take nArgsExported
  -- Copy each SysV argument register `callRegArgs[j]` into the physical register
  -- the RA assigned to the body's `argName j` (skipping copies already in place).
  -- Without this, the body read uninitialised registers as its inputs and the
  -- result was constant in the arguments.
  let argMat := buildArgMaterializePhys virt tbl callRegArgs abi
  let pbody := if bodyHasCall virt.lfd_body
               then physBodyCalleeSave shiftImm virt.lfd_body abi
               else physBody shiftImm virt.lfd_body abi
  -- Move the result into the SysV return register `RAX` before the trailing
  -- `Lret`. The renderer (`renderLfundef`) emits a bare `ret` and the SysV
  -- callee returns its `uint64_t`/`uint32_t` result in `RAX` (`EAX`), but the
  -- linear-scan RA assigns the `Com`'s `.ret` value to an arbitrary physical
  -- register (`resPhys`, e.g. `RBX` for the doubling kernel). Without this copy
  -- the function returns whatever happens to be in `RAX` (a stale intermediate),
  -- not the computed result. Inserted before the final `Lret` (mirroring
  -- `insertEpilogue`), and skipped when the result already lands in `RAX`.
  let retEpi : Lcmd :=
    match resPhys with
    | [r] => if r == "RAX" then [] else [⟨0, .Lopn [.reg "RAX"] "MOVQ" [.reg r]⟩]
    | _ => []
  let bodyWithRet : Lcmd :=
    if retEpi.isEmpty then pbody else pbody.dropLast ++ retEpi ++ [⟨0, .Lret⟩]
  { virt with
    lfd_body := argMat ++ bodyWithRet
    lfd_arg := argSig
    lfd_tyin := tyinSig
    lfd_res := resPhys }

/-- Export a `Com` to a physical-register, two-address `Lprog`.
    * `shiftImm` (default: none) — legacy SSA-name-keyed shift-count oracle.
    * `immSlotMap` (default: none) — producer-level slot → constant map; the
      preferred path since it works regardless of how SSA names get rewritten
      by alpha-renaming/`physBody` rmap. -/
def Com.toLprogPhys {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) (abi : IsaAbi := x86Abi) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs := [(fname, comToLfundefPhys com shiftImm immSlotMap abi)] }

/-- Serialize the physical export to the textual lprog blob (magic + text). -/
def Com.toLprogPhysText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) (abi : IsaAbi := x86Abi) : String :=
  magic ++ (Com.toLprogPhys com fname shiftImm immSlotMap abi).toText ++ "\n"

/-- The physical export's bytes. -/
def Com.toLprogPhysBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) (abi : IsaAbi := x86Abi) : ByteArray :=
  (Com.toLprogPhysText com fname shiftImm immSlotMap abi).toUTF8

/-- Write the physical-register lprog blob for a `Com` to a file. -/
def Com.writeLprogPhysFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (path : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    IO Unit :=
  IO.FS.writeBinFile path (Com.toLprogPhysBytes com fname shiftImm immSlotMap)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
