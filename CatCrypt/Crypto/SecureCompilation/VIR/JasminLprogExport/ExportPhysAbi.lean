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
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhys
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhys

/-!
# Physical-register export with the SysV ABI

The ABI prologue and epilogue, register-residence coalescing, memref-pointer
thread canonicalization, and the physical-register exports of straight-line
`Com` and looped `ComL` programs, including the frame-owning and the
frame-plus-caller-pointer variants.

## Main definitions

* `comToLfundefPhysAbi`, `Com.toLprogPhysAbi`: the ABI-wrapped export of `Com`.
* `ComL.toLfundefPhys`, `ComL.toLprogPhys`: the physical export of `ComL`.
* `ComL.toLfundefPhysFramed`: the frame-owning export.
* `ComL.toLfundefPhysAbi`, `ComL.toLfundefPhysFramedAbi`: the ABI exports of
  looped kernels.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

/-! ### 7f. ABI prologue/epilogue (2-pointer SysV calling convention)

`comToLfundefPhys` exports `lfd_arg` as the first six SysV call-arg registers
`[RDI, RSI, …]`, which satisfies `assemble_fd`'s `check_call_conv` but leaves
the caller to materialise the remaining input slots (every input beyond the
first six is read by the body but never bound to a call-arg register).

For a real C-side ABI like `chacha20_block(uint32_t *out, const uint32_t *inp)`
the caller passes **two pointers** (`RDI = out`, `RSI = inp`) and the body
loads its scalar inputs from `[RSI + 4*k]` and stores its scalar outputs to
`[RDI + 4*k]`. The producer wraps the verified physical body with an ABI
prologue (loads) and epilogue (stores), keeping the body unchanged:

```
prologue (loads):
  mov  R_phys_of_argslot,  [RSI + 4*k]      -- one per active argument slot
                                            -- (slots covered by an immSlotMap
                                            -- entry are skipped — already #imm)
body:
  <unchanged physBody>                       -- the verified two-address body
epilogue (stores), before Lret:
  mov  [RDI + 4*j], R_phys_of_output_j      -- one per output word
```

The memory operand for `[base + off]` is rendered as the register-name string
`"mem.<base>.<off>"` — the `LOperand.reg` constructor is reused (so existing
`LOperand`-keyed proofs are unchanged); `read_linear.ml` recognises the
`"mem."` prefix and materialises the operand as `Fexpr.Load`/`Fexpr.Store` at
`[<base> + <off>]`, exactly mirroring how the `"k."` spill prefix is handled.
-/

/-- An input-load map: argument slot index → `(base-pointer register, byte
    offset)`. The prologue emits a `mov R_phys_of_argslot, [base + off]` for each
    slot the map covers, where `R_phys_of_argslot` is the post-RA physical
    register the body reads at that argument slot. Slots not in the map are
    skipped (e.g. constant-input slots covered by an `immSlotMap`). -/
abbrev InLoadMap := Nat → Option (String × Nat)

/-- An output-store target: the i-th entry is the `(base-pointer register, byte
    offset)` to store the i-th of the last `storeTargets.length` bindings'
    results into. The epilogue emits a `mov [base + off], R_phys_of_output_i`
    for each target, before the body's `Lret`. -/
abbrev OutStoreMap := List (String × Nat)

/-- Render a `[base + off]` memory reference as a register-name string, using
    the convention `read_linear.ml` parses (mirrors the `k.<N>` spill prefix).
    Used inside `LOperand.reg` so no new `LOperand` constructor is needed and
    existing `LOperand`-keyed proofs continue to apply. -/
def memName (base : String) (off : Nat) : String :=
  "mem." ++ base ++ "." ++ toString off

-- The loop-body buffer name agrees with the general frame-memory name. The walk
-- that lays those buffers sits above this definition and carries its own copy of
-- the spelling; these checks hold the two together.
#guard frameBufName 0 = memName "RSP" 0
#guard frameBufName 32 = memName "RSP" 32

/-- The destination operand name of the `bidx`-th binding of a virtual body
    `body` (counting only `Lopn`s; `Lret` is skipped). The binding's destination
    is the first lexpr of its `Lopn`. Returns `none` if `bidx` is out of range
    or the binding has no register destination. -/
def bindingDstOp (body : Lcmd) (bidx : Nat) : Option LOperand :=
  match (body.filterMap (fun i =>
    match i.li_i with
    | .Lopn (d :: _) _ _ => some d
    | _ => none))[bidx]? with
  | some d => some d
  | none => none

/-- The total number of `Lopn` bindings in a virtual body (excludes `Lret`). -/
def numBindings (body : Lcmd) : Nat :=
  body.foldl (fun n i =>
    match i.li_i with
    | .Lopn _ _ _ => n + 1
    | _ => n) 0

/-- The logical slots holding the `n = outStoreMap.length` designated outputs of
    `body`, in output order. The `j`-th output is the destination register of the
    `(firstOutIdx + j)`-th `Lopn` binding (`firstOutIdx = numBindings - n`) — the
    SAME binding the epilogue stores into `out[j]`. A binding with no register
    destination (or out of range) contributes no slot. -/
def outStoreSlots (body : Lcmd) (outStoreMap : OutStoreMap) : List Nat :=
  let n := outStoreMap.length
  let total := numBindings body
  let firstOutIdx := total - n
  (List.range n).filterMap (fun j =>
    match bindingDstOp body (firstOutIdx + j) with
    | some (.reg name) => some (nameSlot body name)
    | _ => none)

/-- **Multi-output liveness fix.** The body's register allocator (`physTable ∘
    bodyTrace`) computes each slot's live range as `[firstTouch, lastTouch]` over
    the body trace ALONE — it does not see the ABI epilogue's inline output stores
    (those are inserted AFTER allocation, by `physBodyWithStores`). So a
    designated-output slot's range ends at the binding that defines it: it is
    never read again inside the body, and the linear scan freely reclaims its
    physical register for a later binding.

    When the last `n` bindings are short, non-overlapping live ranges (the worst
    case: trailing identity copies `out[k] := out[k] | out[k]` emitted by a
    multi-output producer), the scan assigns ALL of them the lowest free physical
    register — so every output slot coalesces onto ONE register and the epilogue
    stores the same value into every `out[j]`.

    This appends one synthetic liveness event to the trace that READS every output
    slot simultaneously at the final position. That extends each output slot's
    `lastTouch` to the trace end and makes the `n` output slots mutually live, so
    the linear scan is forced to keep each in its OWN physical register (none can
    be reclaimed or coalesced before the stores run). The event writes no fresh
    slot (`wr` reuses the first output slot, already touched), so it does not grow
    the slot universe. When `outStoreMap = []` (every register-ABI / single-store
    kernel) the appended event list is empty and the trace is byte-identical, so
    those exports are unchanged. -/
def bodyTraceOut (body : Lcmd) (outStoreMap : OutStoreMap) : List PhysEvent :=
  let base := bodyTrace body
  match outStoreSlots body outStoreMap with
  | [] => base
  | slots@(s0 :: _) => base ++ [{ wr := s0, rds := slots }]

/-- The output-liveness-extended physical-allocation table: `physTable` over the
    trace augmented by `bodyTraceOut`. Used wherever the ABI export resolves a
    body name to its post-RA physical register so that the `n` distinct outputs
    occupy `n` distinct physical registers across the epilogue stores. Reduces to
    `physTable (bodyTrace body)` when `outStoreMap = []`. -/
def physTableOut (body : Lcmd) (outStoreMap : OutStoreMap)
    (reservedVec : List Nat := []) (abi : IsaAbi := x86Abi) : Array Nat :=
  -- Class-aware (`bodyVecSlots`): GP outputs → GP regs, vector outputs → XMM, in
  -- one scan. For a body with no vector op this is `physTable (bodyTraceOut …)`,
  -- so the GP-only multi-output allocation is byte-identical. `reservedVec`
  -- (default `[]`) excludes vector indices; the batch8 path passes `[numVecRegs-1]`.
  physTableClassed (bodyTraceOut body outStoreMap) (bodyVecSlots body)
    (bodyReservedGP body) reservedVec abi

/-- Conservative upper bound on the argument-slot count referenced by a virtual
    body: the maximum `s` such that `argName s` appears anywhere in the body,
    plus one (saturating at zero when no arg name is referenced). Used by
    `physBodyWithStores` to size the first-use tracking array. -/
def virtBodyNumArgs (body : Lcmd) : Nat :=
  body.foldl (fun n i =>
    match i.li_i with
    | .Lopn _ _ srcs =>
        srcs.foldl (fun n' s =>
          match s with
          | .reg name =>
              if name.startsWith "a" then
                match strDropToNat? name 1 with
                | some k => Nat.max n' (k + 1)
                | none => n'
              else n'
          | _ => n') n
    | _ => n) 0

/-- The textual operand name of the 64-bit `RDI` save slot in the red zone.
    The convention `qsave.<reg>` is recognised by `read_linear.ml` as a
    `Load/Store U64` at a fixed red-zone offset (`RSP - 128` for `qsave.RDI`,
    `RSP - 120` for `qsave.RSI`). The high 16 bytes of the 128-byte red zone
    hold the two saved SysV-argument pointers; `k.N` U32 spill slots used by
    the body's register allocator occupy the remaining 112 bytes (≤28 spills
    fit, well above ChaCha's ~5). -/
def abiSaveRdiName : String := "qsave.RDI"

/-- The textual operand name of the 64-bit `RSI` save slot in the red zone.
    See `abiSaveRdiName` for the layout convention. -/
def abiSaveRsiName : String := "qsave.RSI"

/-- Build the ABI prologue. The prologue is now just the **pointer save/copy**
    prelude; the per-slot input loads are inlined into the body by
    `physBodyWithStores` (at each argument slot's first-use position) so the
    body's existing linear-scan RA correctly accounts for their lifetime.

    Two complications drive the shape:

    * `RSI`/`RDI` are in the linear scan's allocatable register set, so the
      body's RA may assign an SSA slot to physical `RSI` / `RDI`. The very
      act of writing physical `RSI` clobbers the input pointer.
    * We can't extend `lfd_arg` beyond the 2-pointer SysV signature
      (`check_call_conv` constrains this).

    Solution: at the very start of the prologue, **save** `RDI` to a red-zone
    save slot (so the epilogue can recover it after the body has clobbered
    `RDI`), and **copy** `RSI` into the reserved secondary scratch `R14` (so
    the inline per-slot loads can use `[R14 + off]` as their base, immune to
    clobbers of `RSI`):

    ```
    movq  [qsave.RDI], RDI       -- save out-pointer to red zone
    movq  R14,         RSI       -- park inp-pointer in R14 (reserved scratch)
    ```

    SysV x86-64 ABI callee-saved GP set is `{RBX, RBP, R12, R13, R14, R15}`.
    Although `R14` and `R15` are *also* used as our reserved reload scratches
    (so the body transiently writes them), we must restore the caller's
    values before `Lret`. Hence we save **all six** SysV callee-saved
    registers into the red zone here; the epilogue
    (`calleeSaveRestoreEpilogue`) restores them. The pre-2026-05-27 prologue
    saved only `RBX/RBP/R12/R13` and treated `R14/R15` as caller-saved
    scratches — this was a correctness bug surfaced when a caller compiled
    at `-O2 -march=native` hoisted a loop-invariant into `R14`/`R15` across
    our call site (every prior bench passed by luck because the harnesses
    never loaded state into those registers).

    `inLoadMap` is taken as a parameter only for the legality lemmas (so
    `buildPrologue_all_MOV_or_MOVQ` doesn't change shape); the actual
    per-slot loads are emitted inside `physBodyWithStores`. -/
def buildPrologue (_virt : Lfundef) (_tbl : Array Nat)
    (_inLoadMap : InLoadMap) : Lcmd :=
  -- The body's linear-scan RA may allocate any of the SysV callee-saved GP
  -- registers (RBX, RBP, R12, R13) — all four are in `gpRegNames`. The
  -- body's reload pass additionally writes R14 / R15 as reserved scratches.
  -- SysV x86-64 ABI callee-saved = {RBX, RBP, R12, R13, R14, R15}; all six
  -- must be saved and restored.
  --
  -- Red-zone layout (high to low, starting at RSP-128):
  --   [-128..-121]  qsave.RDI
  --   [-120..-113]  qsave.RSI
  --   [-112..-105]  callee-saved RBX
  --   [-104..-97]   callee-saved RBP
  --   [-96..-89]    callee-saved R12
  --   [-88..-81]    callee-saved R13
  --   [-80..-73]    callee-saved R14   (added 2026-05-27 for ABI correctness)
  --   [-72..-65]    callee-saved R15   (added 2026-05-27 for ABI correctness)
  --   k.0 = -4, k.1 = -8, ..., k.N at -4-4N (body's u32 spills)
  --
  -- Then save BOTH pointers and park RSI into R14 for the first inline load.
  -- The R14/R15 saves happen BEFORE the RSI-park into R14 (the park clobbers
  -- the original R14 value).
  [⟨0, .Lopn [.reg abiSaveRdiName] "MOVQ" [.reg "RDI"]⟩,
   ⟨0, .Lopn [.reg abiSaveRsiName] "MOVQ" [.reg "RSI"]⟩,
   ⟨0, .Lopn [.reg "qsave.RBX"] "MOVQ" [.reg "RBX"]⟩,
   ⟨0, .Lopn [.reg "qsave.RBP"] "MOVQ" [.reg "RBP"]⟩,
   ⟨0, .Lopn [.reg "qsave.R12"] "MOVQ" [.reg "R12"]⟩,
   ⟨0, .Lopn [.reg "qsave.R13"] "MOVQ" [.reg "R13"]⟩,
   ⟨0, .Lopn [.reg "qsave.R14"] "MOVQ" [.reg "R14"]⟩,
   ⟨0, .Lopn [.reg "qsave.R15"] "MOVQ" [.reg "R15"]⟩,
   ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg "RSI"]⟩]

/-- The red-zone save-slot name a SysV pointer-argument register is parked into
    by `buildPrologue`. The canonical 2-pointer ABI saves `RDI`/`RSI`; any other
    ABI register sources straight from itself (it is still live at entry). -/
def abiSaveOf (reg : String) : Option String :=
  if reg == "RDI" then some abiSaveRdiName
  else if reg == "RSI" then some abiSaveRsiName
  else none

/-- The save slot an input load recovers its base pointer from: the slot of the
    base register the `InLoadMap` entry names, and `qsave.RSI` for a base with no
    save slot. A map that names only `RSI` gets `qsave.RSI`, so its loads are
    unchanged; a map that also names `RDI` reads those inputs through the saved
    `RDI`. -/
def abiLoadSave (base : String) : String := (abiSaveOf base).getD abiSaveRsiName

/-- The red-zone save-slot name for the 3rd+ SysV pointer-argument registers
    (`RDX`, `RCX`, `R8`, `R9`) used by the **multi-input looped** 2-pointer-ABI
    export (`ComL.toLfundefPhysAbi`). The straight-line export never sees these
    (its callers all use the 2-pointer `[RDI, RSI]` signature), so this is kept
    separate from `abiSaveOf` to leave the straight-line / single-input bytes
    untouched.

    A multi-input GF-dot kernel (`out[i] := f(a[i], b[i])`, the `qruov`/`sdith`
    shape) takes `inArgs = [a, b]` with `abiArgs = [RDI, RSI, RDX]`. Each input
    array base must reload from ITS OWN red-zone qsave slot before every
    `LOADIDX`; without a slot for the 2nd input it would (mis-)reload from the
    out slot (`qsave.RDI`), reading `out[]` as `b[]` — garbage. So every ABI
    register in the signature gets a slot.

    Offsets continue the `buildPrologue` red-zone layout below `qsave.R15`
    (`RSP-72`): `qsave.RDX = RSP-64`, `qsave.RCX = RSP-56`, `qsave.R8 = RSP-48`,
    `qsave.R9 = RSP-40`. `read_linear.ml`'s `qsave_addr_of_name` must map these
    to the matching offsets. -/
def abiSaveOfExt (reg : String) : Option String :=
  match abiSaveOf reg with
  | some s => some s
  | none =>
      if reg == "RDX" then some "qsave.RDX"
      else if reg == "RCX" then some "qsave.RCX"
      else if reg == "R8"  then some "qsave.R8"
      else if reg == "R9"  then some "qsave.R9"
      else none

/-- **The argument registers the looped prologue saves after its fixed part**: the
    arguments of `abiArgs` after the first two, without `RDI` and `RSI`, which
    `buildPrologue` saves in every prologue, so the prologue of `lfundefPhysAbiOfVirtCert`
    saves neither of them a second time. On a System V layout, whose argument registers are a
    prefix of `RDI, RSI, RDX, RCX, R8, R9`, this list is `abiArgs.drop 2`. -/
def extraSaveRegs (abiArgs : List String) : List String :=
  (abiArgs.drop 2).filter fun r => !(r == "RDI" || r == "RSI")

/-- `extraSaveRegs` contains neither `RDI` nor `RSI`. -/
theorem not_mem_extraSaveRegs {abiArgs : List String} {r : String}
    (h : r ∈ extraSaveRegs abiArgs) : r ≠ "RDI" ∧ r ≠ "RSI" := by
  simp only [extraSaveRegs, List.mem_filter, Bool.not_eq_true', Bool.or_eq_false_iff,
    beq_eq_false_iff_ne] at h
  exact h.2

/-- **`extraSaveRegs` skips nothing on a layout without `RDI` and `RSI` after the first two
    arguments**, among them every prefix of the System V argument registers. -/
theorem extraSaveRegs_eq_drop {abiArgs : List String}
    (h : ∀ r ∈ abiArgs.drop 2, r ≠ "RDI" ∧ r ≠ "RSI") :
    extraSaveRegs abiArgs = abiArgs.drop 2 := by
  refine List.filter_eq_self.mpr fun r hr => ?_
  obtain ⟨h1, h2⟩ := h r hr
  simp [h1, h2]

/-- **The stack offset of an argument name**: `off` for the export name `RSP+off` of a
    parameter that the caller passes in the stack word `[RSP + off]` (the seventh and later
    System V integer arguments), and `none` for every other name, among them every
    argument register. -/
def abiStackOff? (reg : String) : Option Nat :=
  match reg.toList with
  | 'R' :: 'S' :: 'P' :: '+' :: ds =>
      if !ds.isEmpty && ds.all Char.isDigit then some (Nat.ofDigitChars 10 ds 0) else none
  | _ => none

/-- The export name `RSP+off` has the stack offset `off`. -/
theorem abiStackOff?_rsp (off : Nat) : abiStackOff? ("RSP+" ++ toString off) = some off := by
  have hne := Nat.toDigits_ne_nil (b := 10) (n := off)
  have hd : (Nat.toDigits 10 off).all Char.isDigit = true :=
    List.all_eq_true.mpr fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [abiStackOff?, String.toList_append, Nat.toString_eq_ofList_toDigits,
    String.toList_ofList]
  simp [hd, hne, Nat.ofDigitChars_ten_toDigits]

/-- An argument register has no stack offset. -/
theorem abiStackOff?_of_ne {reg : String} (h : reg.toList.take 4 ≠ ['R', 'S', 'P', '+']) :
    abiStackOff? reg = none := by
  unfold abiStackOff?
  split
  · rename_i ds hds
    rw [hds] at h
    exact absurd rfl h
  · rfl

/-- **The frame slot an argument is read from**: the save slot `abiSaveOfExt` of an
    argument register, and for a stack argument `RSP+off` the caller's stack word, named
    `qsave.RSP+off`, which the printer places `off` bytes above the frame. A stack word is
    written by the caller only, so it has no save in the prologue (`extraInputSaves` reads
    `abiSaveOfExt`). -/
def abiSlotOfExt (reg : String) : Option String :=
  match abiSaveOfExt reg with
  | some s => some s
  | none => (abiStackOff? reg).map fun _ => "qsave." ++ reg

/-- A stack argument `RSP+off` is read from the frame slot `qsave.RSP+off`. -/
theorem abiSlotOfExt_rsp (off : Nat) :
    abiSlotOfExt ("RSP+" ++ toString off) = some ("qsave." ++ ("RSP+" ++ toString off)) := by
  have hs : abiSaveOfExt ("RSP+" ++ toString off) = none := by
    have h4 : ∀ r : String, r.toList.take 4 = ['R', 'S', 'P', '+'] →
        r ≠ "RDI" ∧ r ≠ "RSI" ∧ r ≠ "RDX" ∧ r ≠ "RCX" ∧ r ≠ "R8" ∧ r ≠ "R9" := by
      intro r hr
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; simp at hr)
    obtain ⟨h1, h2, h3, h5, h6, h7⟩ := h4 ("RSP+" ++ toString off) (by simp)
    simp only [abiSaveOfExt, abiSaveOf, beq_iff_eq, h1, h2, h3, h5, h6, h7, ite_false]
  simp only [abiSlotOfExt, hs, abiStackOff?_rsp, Option.map_some]

/-- **Materialize the pointer arguments into the body's register file.**

    The 2-pointer memref ABI (`inLoadMap = none`, `outStoreMap = []`: the body
    self-addresses through pointer arguments used as `LOADIDX`/`STOREIDX` SIB
    bases — ChaCha/SHA/Keccak whole-state kernels) needs each argument name
    `aj` to actually hold the value of the j-th SysV argument register at entry.
    The linear-scan RA assigns `aj` to some physical register or spill slot
    (`physMapTabled tbl (nameSlot virt aj)`) that is **not** in general the ABI
    register `abiArgs[j]` (observed: ChaCha's out-pointer `a0 ↦ RCX`, in-pointer
    `a1 ↦ k.5`), and the prologue only *saves* `RDI`/`RSI` — nothing copies them
    into `aj`'s slot. The body then reads a garbage register / uninitialized
    spill as its SIB base, so every input load and output store hits a wrong
    address (the observed segfault / stack corruption).

    This emits, for each in-range ABI argument `j` whose body name `aj` is
    *actually used*, the copy `aj ← abiArgs[j]` sourced from the argument's
    red-zone save slot (`qsave.RDI`/`qsave.RSI`, written first by
    `buildPrologue`) so no source register is clobbered by an earlier copy:

    * `aj`'s slot is a register `R`: `mov R, [qsave.<abiArg>]` (legal mem→reg);
      skipped entirely when `R == abiArgs[j]` (the value is already in place).
    * `aj`'s slot is a spill `k.N`: `mov R15, [qsave.<abiArg>]; mov [k.N], R15`
      (a direct `mov [k.N], [qsave]` would be an illegal mem→mem).

    For an ABI register with no red-zone save (any beyond the canonical `RDI`/
    `RSI`), the copy sources the live ABI register directly (`mov R, ABIreg`);
    these run after the qsave-sourced copies and the live register is untouched
    by them. A stack argument, named `RSP+off` (`abiStackOff?`), is loaded from the
    caller's stack word `qsave.RSP+off` (`abiSlotOfExt`), which the printer places `off`
    bytes above the frame. The per-word scalar ABI (`inLoadMap` non-empty) sets `aj` via
    the inline first-use loads instead, so for those callers this prelude is empty
    (their `aj` names are not used as bare registers / SIB bases). -/
def buildArgPtrMaterialize (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (inLoadMap : InLoadMap) (abi : IsaAbi := x86Abi) : Lcmd :=
  let body := virt.lfd_body
  (abiArgs.zipIdx).flatMap (fun ⟨abiReg, j⟩ =>
    -- A slot covered by `inLoadMap` is materialized by the inline first-use
    -- load, not here (scalar-word ABI) — skip it.
    match inLoadMap j with
    | some _ => []
    | none =>
        let nm := argName j
        -- Only materialize argument names the body actually references.
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
          -- Resolve through the body's barrier (`physNameForBody`) so the
          -- pointer load targets the same register a call-containing body reads.
          let phys := physNameForBody body tbl nm abi
          let dst : LOperand := .reg phys
          -- `abiSlotOfExt`: the 3rd+ SysV argument registers (`RDX`/`RCX`/…) source
          -- from their own qsave slots (saved by the `extraInputSaves` prologue
          -- tail), and a stack argument from the caller's stack word. It is
          -- `abiSaveOf` on `{RDI, RSI}`, so ≤2-arg kernels are byte-identical.
          match abiSlotOfExt abiReg with
          | some saveName =>
              let memSrc : LOperand := .reg saveName
              if dst.isSpill then
                [⟨0, .Lopn [.reg reloadScratch] "MOVQ" [memSrc]⟩,
                 ⟨0, .Lopn [dst] "MOVQ" [.reg reloadScratch]⟩]
              else if phys == abiReg then
                -- Value already in the right register; nothing to do.
                []
              else
                [⟨0, .Lopn [dst] "MOVQ" [memSrc]⟩]
          | none =>
              -- No red-zone save: source the live ABI register directly.
              if phys == abiReg then []
              else if dst.isSpill then
                [⟨0, .Lopn [.reg reloadScratch] "MOVQ" [.reg abiReg]⟩,
                 ⟨0, .Lopn [dst] "MOVQ" [.reg reloadScratch]⟩]
              else
                [⟨0, .Lopn [dst] "MOVQ" [.reg abiReg]⟩])

/-- Build the ABI epilogue. The epilogue runs after the verified two-address
    body, and is responsible for getting the body's last-`n` SSA results out
    to the C-side `out` buffer.

    Since the body may have used physical `RDI` as a normal allocation target
    (RDI is in `gpRegNames`), the original C-ABI value of `RDI` (the output
    pointer) has been clobbered by the time the epilogue runs. The prologue
    saved it to the red zone (`k.31`); the epilogue restores it into the
    reserved secondary scratch `R14` (so subsequent stores can use
    `[R14 + off]` as their base):

    ```
    mov  R14, [k.31]         -- recover out-pointer from red zone
    <per-output stores via [R14 + off]>
    ```

    Then for each output target, emit a `mov [R14 + off], R_phys` (register
    source) or a two-step `mov R15, [k.N]; mov [R14 + off], R15` (spill source
    — single-memory legality forbids `mov [mem], [spill]` directly). The
    source's physical name comes from the post-RA lookup of the i-th `Lopn`
    binding's destination in the virtual body (the i-th of the last `n`,
    where `n = outStoreMap.length`). Stores are emitted in output order
    (target 0 first). The base register inside `memName` is always `R14`,
    regardless of what the caller-side `outStoreMap` says. -/
def buildEpilogue (virt : Lfundef) (tbl : Array Nat)
    (outStoreMap : OutStoreMap) (abi : IsaAbi := x86Abi) : Lcmd :=
  let restore : Lcmd :=
    [⟨0, .Lopn [.reg reloadScratch2] "MOV" [.reg abiSaveRdiName]⟩]
  let n := outStoreMap.length
  let total := numBindings virt.lfd_body
  let firstOutIdx := total - n
  let stores : Lcmd := (List.range n).flatMap (fun j =>
    match outStoreMap[j]? with
    | none => []
    | some (_base, off) =>
        match bindingDstOp virt.lfd_body (firstOutIdx + j) with
        | none => []
        | some (.reg srcName) =>
            -- Resolve through the body's barrier (`physNameForBody`) so the
            -- store reads from the register a call-containing body wrote.
            let phys := physNameForBody virt.lfd_body tbl srcName abi
            let src : LOperand := .reg phys
            -- Always store via R14 (the restored out-pointer).
            let memDst : LOperand := .reg (memName reloadScratch2 off)
            if src.isSpill then
              -- spill source: route through the reserved reload scratch
              [⟨0, .Lopn [.reg reloadScratch] "MOV" [src]⟩,
               ⟨0, .Lopn [memDst] "MOV" [.reg reloadScratch]⟩]
            else
              [⟨0, .Lopn [memDst] "MOV" [src]⟩]
        | some _ => [])
  restore ++ stores

/-- Insert the epilogue stores just before the final `Lret` of a body. The
    body's last instruction is always `Lret` (proved by `comToBody_ends_Lret`);
    we drop it, append the epilogue, then re-append the `Lret`. -/
def insertEpilogue (body : Lcmd) (epi : Lcmd) : Lcmd :=
  body.dropLast ++ epi ++ [⟨0, .Lret⟩]

/-- The mnemonic of a register-allocated one-source instruction `d := opn s`: the
    64-bit move `MOV:64` when `opn` is the untagged `MOV`, the destination `d` is a
    spill slot, the source `s` is an immediate below `2^31` and the body's spill
    slots are 8 bytes wide (`u64`); `opn` otherwise. The 64-bit store writes the
    whole slot, and a `movq` of an immediate below `2^31` sign-extends it to the
    same value. -/
def spillImmMovMnem (u64 : Bool) (opn : String) (d s : LOperand) : String :=
  match s with
  | .imm v =>
      if u64 && opn == "MOV" && d.isSpill && decide (v < 2 ^ 31) then withWidthTag 64 "MOV"
      else opn
  | _ => opn

/-- `spillImmMovMnem` leaves every mnemonic other than `MOV` unchanged. -/
theorem spillImmMovMnem_of_ne {u64 : Bool} {opn : String} (d s : LOperand)
    (h : opn ≠ "MOV") : spillImmMovMnem u64 opn d s = opn := by
  unfold spillImmMovMnem
  split
  · simp [h]
  · rfl

/-- The instructions of a register-allocated one-source instruction `d := opn s`
    under the move selection `spillImmMovMnem u64`: for a register copy (`MOV` or
    `MOVQ` after the width tag is stripped) the copy legalized by `legalizeMov`, which
    routes a copy between two spill slots through `R15`; the single instruction
    otherwise. -/
def legalizeOneSrc (u64 : Bool) (opn : String) (d s : LOperand) : List LinstrR :=
  if stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ" then
    legalizeMov d s (spillImmMovMnem u64 opn d s)
  else [.Lopn [d] (spillImmMovMnem u64 opn d s) [s]]

/-- On a mnemonic that is not a register copy, `legalizeOneSrc` is the single
    instruction under the mnemonic `opn`. -/
theorem legalizeOneSrc_of_ne {u64 : Bool} {opn : String} (d s : LOperand)
    (h : stripWidthTag opn ≠ "MOV") (h' : stripWidthTag opn ≠ "MOVQ") :
    legalizeOneSrc u64 opn d s = [.Lopn [d] opn [s]] := by
  have hm : opn ≠ "MOV" := fun e => h (by rw [e]; decide)
  simp [legalizeOneSrc, h, h', spillImmMovMnem_of_ne d s hm]

/-- On operands of which at most one is a spill slot, `legalizeOneSrc` is the single
    instruction under the move selection. -/
theorem legalizeOneSrc_of_not_spill {u64 : Bool} {opn : String} {d s : LOperand}
    (h : (d.isSpill && s.isSpill) = false) :
    legalizeOneSrc u64 opn d s = [.Lopn [d] (spillImmMovMnem u64 opn d s) [s]] := by
  unfold legalizeOneSrc legalizeMov
  simp [h]

/-- **The legalized copy between spill slots.** A register copy whose operands are both
    spill slots is `MOV R15, s; MOV d, R15` under the mnemonic `opn`. -/
theorem legalizeOneSrc_spill {u64 : Bool} {opn : String} {d s : LOperand}
    (ho : (stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ") = true)
    (hd : d.isSpill = true) (hs : s.isSpill = true) :
    legalizeOneSrc u64 opn d s
      = [.Lopn [.reg reloadScratch] opn [s], .Lopn [d] opn [.reg reloadScratch]] := by
  have hm : spillImmMovMnem u64 opn d s = opn := by
    unfold spillImmMovMnem
    split
    · simp [LOperand.isSpill] at hs
    · rfl
  simp only [legalizeOneSrc, ho, ite_true, hm, legalizeMov, hd, hs, Bool.and_self]

/-- The constant the oracle `shiftImm` gives for the index name of a
    register-indexed address of the virtual body; `none` on every other operand. -/
def idxConst (shiftImm : ShiftImmOracle) : LOperand → Option Nat
  | .arrIdx _ idx _ => shiftImm idx
  | _ => none

/-- The displacement store of a spilled value at a spilled index of known value.

    For a register-allocated address `arrIdx b i 8` whose index `i` is a spill
    slot, a spilled value `val` and an index constant `c < 2^28`, the store is
    `MOV:64 R15, val; STORE:64 mem.<b'>.<8c>, R15`, where `b'` is `b`, or `R14`
    after the reload `MOV:64 R14, b` when `b` is a spill slot. `none` in every
    other case. The index is not loaded and the base register is not written
    after its reload. -/
def constIdxStore? (k : Option Nat) (addr val : LOperand) : Option (List LinstrR) :=
  match addr with
  | .arrIdx b i scale =>
      -- The spill tests come before the constant, so a store that fails them
      -- reduces without evaluating the oracle.
      if sibNameSpill i && val.isSpill && scale == 8 then
        match k with
        | some c =>
            if c < 2 ^ 28 then
              let basePre : List LinstrR :=
                if sibNameSpill b then [.Lopn [.reg reloadScratch2] "MOV:64" [.reg b]] else []
              let b' : String := if sibNameSpill b then reloadScratch2 else b
              some (basePre ++
                [.Lopn [.reg reloadScratch] "MOV:64" [val],
                 .Lopn [.reg (memName b' (8 * c))] "STORE:64" [.reg reloadScratch]])
            else none
        | none => none
      else none
  | _ => none

/-- `legalizeMemStore` with an optional index constant `k`: the displacement
    store `constIdxStore? k addr val` when it is defined, and
    `legalizeMemStore dArr addr val opn mov` otherwise. -/
def legalizeMemStoreK (k : Option Nat) (dArr addr val : LOperand) (opn : String)
    (mov : String := "MOV") : List LinstrR :=
  match constIdxStore? k addr val with
  | some l => l
  | none => legalizeMemStore dArr addr val opn mov

/-- Without an index constant there is no displacement store. -/
@[simp] theorem constIdxStore?_none (addr val : LOperand) :
    constIdxStore? none addr val = none := by
  unfold constIdxStore?
  split
  · split <;> rfl
  · rfl

/-- A register value has no displacement store. -/
theorem constIdxStore?_of_not_spill (k : Option Nat) (addr : LOperand) {val : LOperand}
    (h : val.isSpill = false) : constIdxStore? k addr val = none := by
  unfold constIdxStore?
  split
  · simp [h]
  · rfl

/-- An address whose index is not a spill slot has no displacement store. -/
theorem constIdxStore?_of_idx (k : Option Nat) (b i : String) (scale : Nat) (val : LOperand)
    (h : sibNameSpill i = false) : constIdxStore? k (.arrIdx b i scale) val = none := by
  simp [constIdxStore?, h]

/-- An address that is not register-indexed has no displacement store. -/
theorem constIdxStore?_of_not_arrIdx (k : Option Nat) {addr : LOperand} (val : LOperand)
    (h : ∀ b i scale, addr ≠ .arrIdx b i scale) : constIdxStore? k addr val = none := by
  unfold constIdxStore?
  split
  · exact absurd rfl (h _ _ _)
  · rfl

/-- Where there is no displacement store, `legalizeMemStoreK` is `legalizeMemStore`. -/
theorem legalizeMemStoreK_of_none {k : Option Nat} {addr val : LOperand} (dArr : LOperand)
    (opn mov : String) (h : constIdxStore? k addr val = none) :
    legalizeMemStoreK k dArr addr val opn mov = legalizeMemStore dArr addr val opn mov := by
  simp [legalizeMemStoreK, h]

/-- Without an index constant, `legalizeMemStoreK` is `legalizeMemStore`. -/
@[simp] theorem legalizeMemStoreK_none (dArr addr val : LOperand) (opn mov : String) :
    legalizeMemStoreK none dArr addr val opn mov = legalizeMemStore dArr addr val opn mov :=
  legalizeMemStoreK_of_none dArr opn mov (constIdxStore?_none addr val)

/-- **The displacement store.** A spilled value stored at a spilled index of
    constant `c < 2^28` under an 8-byte stride through a register base `b` is
    `MOV:64 R15, val; STORE:64 mem.<b>.<8c>, R15`. -/
theorem legalizeMemStoreK_const {c : Nat} {b i : String} {val : LOperand} (dArr : LOperand)
    (opn mov : String) (hb : sibNameSpill b = false) (hi : sibNameSpill i = true)
    (hv : val.isSpill = true) (hc : c < 2 ^ 28) :
    legalizeMemStoreK (some c) dArr (.arrIdx b i 8) val opn mov
      = [.Lopn [.reg reloadScratch] "MOV:64" [val],
         .Lopn [.reg (memName b (8 * c))] "STORE:64" [.reg reloadScratch]] := by
  simp [legalizeMemStoreK, constIdxStore?, hb, hi, hv, hc]

/-- The select `opn d, [c, t, f]` with its spill slots routed through the scratch
    registers: a condition `c` in a spill slot is first loaded by `MOV:64 R14, c` and
    the select reads `R14`; a destination `d` in a spill slot is replaced by `R15`,
    followed by the store `MOV:64 d, R15`. The select does not read its destination,
    so the slot is not loaded. -/
def cmovSpillSeq (opn : String) (d c t f : LOperand) : List LinstrR :=
  (if c.isSpill then [.Lopn [.reg reloadScratch2] "MOV:64" [c]] else [])
    ++ (if d.isSpill then
          [.Lopn [.reg reloadScratch] opn
              [if c.isSpill then .reg reloadScratch2 else c, t, f],
           .Lopn [d] "MOV:64" [.reg reloadScratch]]
        else [.Lopn [d] opn [if c.isSpill then .reg reloadScratch2 else c, t, f]])

/-- The select with spilled operands through the scratch registers.

    For a single destination `d`, the mnemonic `CMOV:64` and three sources `c`, `t`,
    `f`, where the destination or the condition is a spill slot, the select is
    `cmovSpillSeq opn d c t f`. `none` in every other case. -/
def cmovSpillDst? (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    Option (List LinstrR) :=
  match dsts, srcs with
  | [d], [c, t, f] =>
      -- The spill tests come before the mnemonic, so register operands reduce
      -- without comparing strings.
      if (d.isSpill || c.isSpill) && opn == "CMOV:64" then
        some (cmovSpillSeq opn d c t f)
      else none
  | _, _ => none

/-- The mnemonics of the materialised comparison `SET<cc>`, after the width tag is
    stripped. -/
def isSetccMnem (opn : String) : Bool :=
  ["SETE", "SETNE", "SETB", "SETBE", "SETA", "SETAE"].contains (stripWidthTag opn)

/-- The move of the materialised comparison `opn`: `MOV:64` for a `:64`-tagged
    mnemonic, `MOV` otherwise. -/
def setccMov (opn : String) : String := if hasSuffix opn ":64" then "MOV:64" else "MOV"

/-- The materialised comparison with spilled operands through the scratch registers.

    For a single destination `d`, a comparison mnemonic `opn` (`isSetccMnem`) and two
    register-named sources `a`, `b`, one of the three a spill slot, the comparison is
    `MOV R15, a; MOV R14, b; opn R15, [R15, R14]; MOV d, R15`, the moves at the width
    of the comparison (`setccMov`). `none` in every other case. -/
def setccSpill? (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    Option (List LinstrR) :=
  match dsts, srcs with
  | [d], [.reg a, .reg b] =>
      if (d.isSpill || (LOperand.reg a).isSpill || (LOperand.reg b).isSpill)
          && isSetccMnem opn then
        some [.Lopn [.reg reloadScratch] (setccMov opn) [.reg a],
              .Lopn [.reg reloadScratch2] (setccMov opn) [.reg b],
              .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .reg reloadScratch2],
              .Lopn [d] (setccMov opn) [.reg reloadScratch]]
      else none
  | _, _ => none

/-- The instructions of a register-allocated `Lopn` with destinations `dsts`,
    mnemonic `opn` and sources `srcs`: the scratch select `cmovSpillDst?` or the
    scratch comparison `setccSpill?` when one is defined, and the single instruction
    `Lopn dsts opn srcs` otherwise. -/
def legalizeSpillDst (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    List LinstrR :=
  match cmovSpillDst? dsts opn srcs with
  | some l => l
  | none =>
      match setccSpill? dsts opn srcs with
      | some l => l
      | none => [.Lopn dsts opn srcs]

/-- A mnemonic other than `CMOV:64` has no scratch select. -/
theorem cmovSpillDst?_of_ne (dsts : List LOperand) {opn : String} (srcs : List LOperand)
    (h : opn ≠ "CMOV:64") : cmovSpillDst? dsts opn srcs = none := by
  unfold cmovSpillDst?
  split
  · simp [h]
  · rfl

/-- A mnemonic other than a comparison mnemonic has no scratch comparison. -/
theorem setccSpill?_of_ne (dsts : List LOperand) {opn : String} (srcs : List LOperand)
    (h : isSetccMnem opn = false) : setccSpill? dsts opn srcs = none := by
  unfold setccSpill?
  split
  · simp [h]
  · rfl

/-- Operands none of which is a spill slot have no scratch select. -/
theorem cmovSpillDst?_of_not_spill {dsts : List LOperand} (opn : String)
    {srcs : List LOperand} (h : ∀ d ∈ dsts, d.isSpill = false)
    (hs : ∀ s ∈ srcs, s.isSpill = false) : cmovSpillDst? dsts opn srcs = none := by
  unfold cmovSpillDst?
  split
  · simp [h _ (List.mem_singleton_self _), hs _ (List.mem_cons_self ..)]
  · rfl

/-- Operands none of which is a spill slot have no scratch comparison. -/
theorem setccSpill?_of_not_spill {dsts : List LOperand} (opn : String)
    {srcs : List LOperand} (h : ∀ d ∈ dsts, d.isSpill = false)
    (hs : ∀ s ∈ srcs, s.isSpill = false) : setccSpill? dsts opn srcs = none := by
  unfold setccSpill?
  split
  · rename_i a b
    have ha := hs (.reg a) (by simp)
    have hb := hs (.reg b) (by simp)
    simp [h _ (List.mem_singleton_self _), ha, hb]
  · rfl

/-- Where there is neither a scratch select nor a scratch comparison,
    `legalizeSpillDst` is the single instruction. -/
theorem legalizeSpillDst_of_none {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (h : cmovSpillDst? dsts opn srcs = none) (h' : setccSpill? dsts opn srcs = none) :
    legalizeSpillDst dsts opn srcs = [.Lopn dsts opn srcs] := by
  simp [legalizeSpillDst, h, h']

/-- On a mnemonic other than `CMOV:64` and the comparison mnemonics,
    `legalizeSpillDst` is the single instruction. -/
theorem legalizeSpillDst_of_ne (dsts : List LOperand) {opn : String} (srcs : List LOperand)
    (h : opn ≠ "CMOV:64") (h' : isSetccMnem opn = false) :
    legalizeSpillDst dsts opn srcs = [.Lopn dsts opn srcs] :=
  legalizeSpillDst_of_none (cmovSpillDst?_of_ne dsts srcs h) (setccSpill?_of_ne dsts srcs h')

/-- On operands none of which is a spill slot, `legalizeSpillDst` is the single
    instruction. -/
theorem legalizeSpillDst_of_not_spill {dsts : List LOperand} (opn : String)
    {srcs : List LOperand} (h : ∀ d ∈ dsts, d.isSpill = false)
    (hs : ∀ s ∈ srcs, s.isSpill = false) :
    legalizeSpillDst dsts opn srcs = [.Lopn dsts opn srcs] :=
  legalizeSpillDst_of_none (cmovSpillDst?_of_not_spill opn h hs)
    (setccSpill?_of_not_spill opn h hs)

/-- **The scratch select.** A `CMOV:64` whose destination or condition is a spill slot
    is `cmovSpillSeq "CMOV:64" d c t f`. -/
theorem legalizeSpillDst_cmov {d c : LOperand} (t f : LOperand)
    (h : (d.isSpill || c.isSpill) = true) :
    legalizeSpillDst [d] "CMOV:64" [c, t, f] = cmovSpillSeq "CMOV:64" d c t f := by
  simp [legalizeSpillDst, cmovSpillDst?, h]

/-- The select on a spilled condition into a register destination reloads the condition
    into `R14`. -/
theorem cmovSpillSeq_cond {d c : LOperand} (opn : String) (t f : LOperand)
    (hd : d.isSpill = false) (hc : c.isSpill = true) :
    cmovSpillSeq opn d c t f
      = [.Lopn [.reg reloadScratch2] "MOV:64" [c],
         .Lopn [d] opn [.reg reloadScratch2, t, f]] := by
  simp [cmovSpillSeq, hd, hc]

/-- The select on a spilled condition into a spilled destination reloads the condition
    into `R14`, selects into `R15` and stores `R15` to the destination. -/
theorem cmovSpillSeq_cond_dst {d c : LOperand} (opn : String) (t f : LOperand)
    (hd : d.isSpill = true) (hc : c.isSpill = true) :
    cmovSpillSeq opn d c t f
      = [.Lopn [.reg reloadScratch2] "MOV:64" [c],
         .Lopn [.reg reloadScratch] opn [.reg reloadScratch2, t, f],
         .Lopn [d] "MOV:64" [.reg reloadScratch]] := by
  simp [cmovSpillSeq, hd, hc]

/-- The select on a register condition into a spilled destination selects into `R15` and
    stores `R15` to the destination. -/
theorem cmovSpillSeq_dst {d c : LOperand} (opn : String) (t f : LOperand)
    (hd : d.isSpill = true) (hc : c.isSpill = false) :
    cmovSpillSeq opn d c t f
      = [.Lopn [.reg reloadScratch] opn [c, t, f],
         .Lopn [d] "MOV:64" [.reg reloadScratch]] := by
  simp [cmovSpillSeq, hd, hc]

/-- The move of a materialised comparison is a `MOV` after its width tag is stripped. -/
theorem stripWidthTag_setccMov (opn : String) : stripWidthTag (setccMov opn) = "MOV" := by
  unfold setccMov
  split <;> decide +kernel

/-- **The scratch comparison.** A comparison `opn d, [a, b]` over register names, one
    of the three a spill slot, is `MOV R15, a; MOV R14, b; opn R15, [R15, R14];
    MOV d, R15`. -/
theorem legalizeSpillDst_setcc {d : LOperand} {opn a b : String}
    (h : (d.isSpill || (LOperand.reg a).isSpill || (LOperand.reg b).isSpill) = true)
    (ho : isSetccMnem opn = true) :
    legalizeSpillDst [d] opn [.reg a, .reg b]
      = [.Lopn [.reg reloadScratch] (setccMov opn) [.reg a],
         .Lopn [.reg reloadScratch2] (setccMov opn) [.reg b],
         .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .reg reloadScratch2],
         .Lopn [d] (setccMov opn) [.reg reloadScratch]] := by
  have hc : cmovSpillDst? [d] opn [.reg a, .reg b] = none := rfl
  simp only [legalizeSpillDst, hc, setccSpill?, h, ho, Bool.and_self, ite_true]

/-- Every instruction of `legalizeSpillDst dsts opn srcs` is an `Lopn` each of whose
    operands is a destination in `dsts`, a source in `srcs`, or one of the scratch
    registers `R15` (`reloadScratch`) and `R14` (`reloadScratch2`). -/
theorem legalizeSpillDst_mem {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    {r : LinstrR} (h : r ∈ legalizeSpillDst dsts opn srcs) :
    ∃ ds o ss, r = .Lopn ds o ss ∧ ∀ x ∈ ds ++ ss,
      x ∈ dsts ∨ x ∈ srcs ∨ x = .reg reloadScratch ∨ x = .reg reloadScratch2 := by
  unfold legalizeSpillDst at h
  split at h
  · rename_i l hl
    unfold cmovSpillDst? at hl
    split at hl
    · split at hl
      · cases hl
        unfold cmovSpillSeq at h
        rename_i d c t f _
        cases hc : c.isSpill <;> cases hd : d.isSpill <;>
          simp only [hc, hd, Bool.false_eq_true, ite_false, ite_true, List.nil_append,
            List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at h <;>
          rcases h with rfl | rfl | rfl <;>
          exact ⟨_, _, _, rfl, by intro x hx; simp at hx ⊢; aesop⟩
      · cases hl
    · cases hl
  · split at h
    · rename_i l _ hl
      unfold setccSpill? at hl
      split at hl
      · split at hl
        · cases hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl | rfl <;>
            exact ⟨_, _, _, rfl, by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp⟩
        · cases hl
      · cases hl
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨_, _, _, rfl, fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)⟩

/-! ### The allocator's decision -/

/-- **The allocation table of `physBodyWithStores`**: the linear scan `physTableOut` of
    `body` at the output stores `outStoreMap` and the reserved vector indices
    `reservedVec`, with the straight-line call relocation composed in
    (`straightCallComposeTable`). -/
def physAllocTbl (body : Lcmd) (outStoreMap : OutStoreMap) (reservedVec : List Nat := [])
    (abi : IsaAbi := x86Abi) : Array Nat :=
  straightCallComposeTable body (physTableOut body outStoreMap reservedVec abi)

/-- **The allocator's renaming** of a register name `n` of `body` over the table `tbl`:
    the name of the register operand `physBodyWithStores` writes for `.reg n`, that is
    the `.reg` arm of `remapOperandCalleeSave` (`physNameForBody`) on a body with an
    `Lcall` and of `remapOperand` otherwise. It is one location per name over the whole
    body and is not injective: names with disjoint live ranges share a register or a
    frame cell. -/
def allocName (body : Lcmd) (tbl : Array Nat) (n : String) (abi : IsaAbi := x86Abi) :
    String :=
  if bodyHasCall body then physNameForBody body tbl n abi
  else physRegName (physMapTabled tbl (nameSlot body n)) abi

/-- The names of `body` that the allocation certificate covers: every name of
    `bodyNames body` other than the liveness pseudo-name `%livepin`, a hardware register
    name and a frame-slot name. -/
def allocCertNames (body : Lcmd) : List String :=
  (bodyNames body).filter fun n => n != "%livepin" && !isHwRegName n && !isFrameSlotName n

/-- **The allocation certificate over a table**: each name of `allocCertNames body`
    paired with its image `allocName body tbl n`. -/
def allocCertOf (body : Lcmd) (tbl : Array Nat) (abi : IsaAbi := x86Abi) :
    List (String × String) :=
  (allocCertNames body).map fun n => (n, allocName body tbl n abi)

/-- **The allocation certificate of `physBodyWithStores`**: `allocCertOf` over the table
    `physAllocTbl`, the pairs `(n, allocName body tbl n)` of the names the allocator
    renames. -/
def allocCert (body : Lcmd) (outStoreMap : OutStoreMap) (reservedVec : List Nat := [])
    (abi : IsaAbi := x86Abi) : List (String × String) :=
  allocCertOf body (physAllocTbl body outStoreMap reservedVec abi) abi

/-- A pair of the certificate over `tbl` is a covered name and its image under
    `allocName`. -/
theorem mem_allocCertOf {body : Lcmd} {tbl : Array Nat} {abi : IsaAbi} {n m : String} :
    (n, m) ∈ allocCertOf body tbl abi
      ↔ n ∈ allocCertNames body ∧ allocName body tbl n abi = m := by
  unfold allocCertOf
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, rfl, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨n, hx, rfl, rfl⟩


/-- A `physBody` variant that:

    1. Inserts ABI-prologue loads INLINE — for each argument slot covered by
       `inLoadMap`, the load is emitted just before the FIRST virtual body
       instruction that reads it. This solves the lifetime problem on the
       INPUT side: the existing linear-scan RA assumes each arg slot's
       physical register is "live from first use to last use"; loading all
       args upfront would force them to be simultaneously live at position 0,
       and any two slots sharing a physical register (because their body
       liveness doesn't overlap) would clobber each other. Loading at
       first-use exactly matches the RA's lifetime model.

    2. Inserts ABI-epilogue stores INLINE — for each of the last `n` `Lopn`
       bindings (where `n = outStoreMap.length`), a store of the binding's
       destination physical register to `[storeBase + offset]` is emitted
       just after the binding's physBody expansion. This solves the lifetime
       problem on the OUTPUT side: under SSA only the LAST `Com.ret` value
       is live at function exit; the other 15 outputs' physical registers
       have been reclaimed for later computations. Storing each output
       inline preserves the value before any subsequent overwrite.

    Each store is preceded by a `mov reloadScratch2, [qsave.RDI]` to recover
    the out-pointer (since `reloadScratch2 = R14` may have been transiently
    used as a body scratch).

    Both load- and store- bases default to `reloadScratch2` (= `R14`). The
    prologue (built by `buildPrologue`) parks `RSI` into `R14` for the load
    side; the per-store reload puts `RDI` (recovered from `qsave.RDI`) into
    `R14` for the store side. -/
/- Compiled twin of `physBodyWithStores`. Semantically identical to the spec
    below, but it removes the spec's quadratic recomputations for a ~4000-binding
    body:

    * `bidx` (binding index at each position) is carried in a running counter
      instead of `(body.take virtIdx).filter …).length` per position (`O(n²)`);
    * the argument-slot first-use map is built by parsing the `aN` slot index
      directly from each source name (`O(n)`), instead of scanning
      `List.range nArgs` per source (`O(n·nArgs)`);
    * loads-at-position is an array indexed by position (`O(1)` lookup).

    The remapping (`rmap`), two-address lowering, and emitted-instruction shapes
    are byte-for-byte the spec's. -/
@[inline] unsafe def physBodyWithStoresImpl (shiftImm : ShiftImmOracle)
    (body : Lcmd) (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat := 0)
    (memrefBaseReload : String → Option String := fun _ => none)
    (callArgBaseReload : List (String × String) := [])
    (reservedVec : List Nat := []) (abi : IsaAbi := x86Abi) : Lcmd :=
  -- Output-liveness-extended allocation: the `n` designated output slots are kept
  -- in `n` distinct physical registers across the epilogue stores (see
  -- `bodyTraceOut`). Reduces to `physTable (bodyTrace body)` for `outStoreMap=[]`.
  let tbl := physAllocTbl body outStoreMap reservedVec abi
  -- Caller-save clobber barrier (matches the spec `physBodyWithStores`): a body
  -- carrying a real `Lcall` renames through `remapOperandCalleeSave`; a call-free
  -- body keeps `remapOperand` (byte-identical).
  let rmap := if bodyHasCall body then remapOperandCalleeSave body tbl (abi := abi)
              else remapOperand body tbl (abi := abi)
  let isBinop (opn : String) : Bool := isTwoAddrBinop opn
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  -- The ABI prologue/epilogue moves the U64 state lanes whenever the body is a
  -- U64 kernel (Keccak): a body op carrying `:64` ⇒ the inline load/store moves
  -- must be `MOV:64` so the full 64-bit memory value survives.
  let bodyIsU64 : Bool := body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => hasSuffix opn ":64"
    | _ => false)
  -- The ABI MOV widths (narrow-buffer seam). Two distinct legs:
  --   * `abiMovBuf` — the mov that **touches the C buffer** (`mem.RSI`/`mem.RDI`).
  --     When the caller passes a narrow `abiW` (16 / 8 — the buffer's *element*
  --     width, e.g. Frodo's `uint16_t`), this leg is tagged `MOV:16`/`MOV:8`, so
  --     the owned printer renders a zero-extending `movz{w,b}l` load (a memory
  --     source → 32-bit working register) and a width-exact `mov{w,b}` store (a
  --     memory dest → narrow write, no overrun of the neighbouring element).
  --   * `abiMovReg` — the mov on the **scratch ↔ spill** routing leg (register to
  --     register / register to spill). This must stay full-width (`MOV:64`/`MOV`):
  --     the spill holds the body's working value, so narrowing it would truncate.
  -- `abiW = 0` (every existing caller) makes both legs the 64-bit
  -- `MOV:64`/`MOV`, so the emitted body is byte-identical. `abiW = 256` (the
  -- batch8 packed SoA ABI) makes both legs `VMOVDQU`, so the printer renders the
  -- `mem ↔ %ymm` loads/stores as `vmovdqu`.
  let abiMovReg : String :=
    if abiW == 256 then "VMOVDQU" else if bodyIsU64 then "MOV:64" else "MOV"
  let abiMovBuf : String :=
    if abiW == 16 then "MOV:16"
    else if abiW == 8 then "MOV:8"
    else abiMovReg
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  let n := outStoreMap.length
  let total := numBindings body
  let firstOutIdx := total - n
  let nArgs := virtBodyNumArgs body
  -- Parse `argName s = "a" ++ toString s` back to its index `s` (none if the
  -- name is not an arg name in range).
  let argIdx? (nm : String) : Option Nat :=
    if nm.startsWith "a" then
      match strDropToNat? nm 1 with
      | some s => if s < nArgs then some s else none
      | none => none
    else none
  -- argSlot s -> first virt position that reads it, and the inverse:
  -- position -> list of (argSlot, base, off) loads to emit before it.
  let firstUseMap : Array (Option Nat) := Id.run do
    let mut arr : Array (Option Nat) := Array.replicate nArgs none
    let mut pos := 0
    for i in body do
      match i.li_i with
      | .Lopn _ _ srcs =>
          for src in srcs do
            match src with
            | .reg nm =>
                match argIdx? nm with
                | some s => if (arr[s]!).isNone then arr := arr.set! s (some pos)
                | none => pure ()
            | _ => pure ()
      | _ => pure ()
      pos := pos + 1
    return arr
  let loadsByPos : Array (List (Nat × String × Nat)) := Id.run do
    let mut arr : Array (List (Nat × String × Nat)) := Array.replicate body.length []
    for s in List.range nArgs do
      match firstUseMap[s]! with
      | some fpos =>
          if fpos < arr.size then
            match inLoadMap s with
            | some (base, off) => arr := arr.set! fpos (arr[fpos]! ++ [(s, base, off)])
            | none => pure ()
      | none => pure ()
    return arr
  -- Emit, carrying the running binding index (`bidx` of each position).
  Id.run do
    let mut out : Array Linstr := #[]
    let mut bidx := 0
    let mut virtIdx := 0
    for i in body do
      let loads : Lcmd := (loadsByPos[virtIdx]!).flatMap (fun ⟨_s, base, off⟩ =>
        let phys := physNameForBody body tbl (argName _s) abi
        let dst : LOperand := .reg phys
        let memSrc : LOperand := .reg (memName loadBase off)
        let reloadIn : Linstr :=
          ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg (abiLoadSave base)]⟩
        if dst.isSpill then
          [reloadIn,
           ⟨0, .Lopn [.reg reloadScratch] abiMovBuf [memSrc]⟩,
           ⟨0, .Lopn [dst] abiMovReg [.reg reloadScratch]⟩]
        else
          [reloadIn,
           ⟨0, .Lopn [dst] abiMovBuf [memSrc]⟩])
      let thisBidx := bidx
      let expanded : Lcmd :=
        match i.li_i with
        | .Lopn (d :: _) opn (s0 :: s1 :: _) =>
            if isBinop opn then
              match (if isShift opn then shiftImmVal s1 else none) with
              | some v =>
                  (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
                    (fun r => ⟨i.li_ii, r⟩)
              | none =>
                  (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
                    (fun r => ⟨i.li_ii, r⟩)
            else
              -- three-source carry ops keep all sources (no truncation).
              match i.li_i with
              -- A `STOREIDX` (srcs `[arrIdx, val]`) whose remapped value source
              -- is a spill slot would render as an illegal `mov mem, mem` (the
              -- mirror of the LOAD case). Route the value through `R15`.
              | .Lopn [d'] opn' [addr, val] =>
                  if isMemStore opn' then
                    -- Reload the memref base pointer from its red-zone qsave slot
                    -- into R14 immediately before the store: the RA-assigned
                    -- ABI register holding it has been clobbered by the body.
                    let (baseReload, addr') := reloadMemrefBase memrefBaseReload (rmap addr)
                    (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
                    (legalizeMemStoreK (idxConst shiftImm addr) (rmap d') addr' (rmap val) opn'
                       (movFor opn')).map (fun r => ⟨i.li_ii, r⟩)
                  else
                    -- A comparison with a spilled operand runs on the scratch
                    -- registers (`legalizeSpillDst`).
                    (legalizeSpillDst [rmap d'] opn' [rmap addr, rmap val]).map
                      (fun r => ⟨i.li_ii, r⟩)
              -- A `CMOV:64` with a spilled destination or condition runs on the
              -- scratch registers (`legalizeSpillDst`).
              | .Lopn dsts opn srcs =>
                  (legalizeSpillDst (dsts.map rmap) opn (srcs.map rmap)).map
                    (fun r => ⟨i.li_ii, r⟩)
              | other => [⟨i.li_ii, other⟩]
        -- Native immediate shift / rotate (`ROR:n` / `SHL:n` / …): one-source
        -- in-place op. Route a spilled operand through R15 (spill legalize).
        | .Lopn [d] opn [s] =>
            if isNativeShiftRotate opn then
              (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
                (fun r => ⟨i.li_ii, r⟩)
            else if isMemLoad opn then
              -- A `LOAD`/`LOADIDX` into a spill slot would render as an illegal
              -- `mov mem, mem`; route through `R15` (whole-state load fix).
              -- First reload the memref base pointer from its qsave slot into R14.
              let (baseReload, s') := reloadMemrefBase memrefBaseReload (rmap s)
              (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
              (legalizeMemLoad (rmap d) s' opn (movFor opn)).map
                (fun r => ⟨i.li_ii, r⟩)
            else
              -- A copy between two spill slots goes through `R15` (`legalizeOneSrc`).
              (legalizeOneSrc bodyIsU64 opn (rmap d) (rmap s)).map (fun r => ⟨i.li_ii, r⟩)
        | .Lopn dsts opn srcs =>
            [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
        | other => [⟨i.li_ii, other⟩]
      let store : Lcmd :=
        match i.li_i with
        | .Lopn (d :: _) _ _ =>
            if thisBidx ≥ firstOutIdx ∧ thisBidx < total then
              let outIdx := thisBidx - firstOutIdx
              match outStoreMap[outIdx]? with
              | some (_base, off) =>
                  let src := rmap d
                  let memDst : LOperand := .reg (memName storeBase off)
                  let reloadOut : Linstr :=
                    ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg abiSaveRdiName]⟩
                  if src.isSpill then
                    [⟨0, .Lopn [.reg reloadScratch] abiMovReg [src]⟩,
                     reloadOut,
                     ⟨0, .Lopn [memDst] abiMovBuf [.reg reloadScratch]⟩]
                  else
                    [reloadOut,
                     ⟨0, .Lopn [memDst] abiMovBuf [src]⟩]
              | none => []
            else []
        | _ => []
      -- After a real in-loop `Lcall`, restore each loop-invariant pointer base
      -- that the looped-call barrier overflowed into a *caller-saved* register
      -- (`callArgBaseReload`, keyed physReg ↦ qsave slot) from its red-zone save
      -- slot: the SysV leaf clobbers caller-saved GPRs, so an invariant base that
      -- did not fit the four callee-saved registers is otherwise destroyed. A
      -- base already in a callee-saved register is not in the list, so a body
      -- whose loop-carried set fits (≤4) emits nothing here (byte-identical).
      let callReload : Lcmd :=
        match i.li_i with
        | .Lcall _ _ =>
            callArgBaseReload.map (fun (physReg, qsave) =>
              (⟨0, .Lopn [.reg physReg] "MOVQ" [.reg qsave]⟩ : Linstr))
        | _ => []
      -- advance the binding counter (only `Lopn`s count, matching the spec)
      match i.li_i with
      | .Lopn _ _ _ => bidx := bidx + 1
      | _ => pure ()
      virtIdx := virtIdx + 1
      out := (((out ++ loads.toArray) ++ expanded.toArray)
                ++ callReload.toArray) ++ store.toArray
    return out.toList

@[implemented_by physBodyWithStoresImpl]
def physBodyWithStores (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat := 0)
    (memrefBaseReload : String → Option String := fun _ => none)
    (callArgBaseReload : List (String × String) := [])
    (reservedVec : List Nat := []) (abi : IsaAbi := x86Abi) : Lcmd :=
  -- Output-liveness-extended allocation (multi-output store fix): see
  -- `bodyTraceOut`. `physTableOut body []` = `physTable (bodyTrace body)`.
  let tbl := physAllocTbl body outStoreMap reservedVec abi
  -- Caller-save clobber barrier: a body carrying a real `Lcall` (an expanded
  -- `CALL:`/`CALLN:` leaf-call shadow, `expandCallShadows`) renames through
  -- `remapOperandCalleeSave` — the SysV hardware marshalling names (`RDI…`,`RAX`)
  -- are pinned to themselves and every other GP slot is routed callee-saved-first
  -- (`calleeFirstPhys`) so a value live across the call survives it. A call-free
  -- body keeps the plain `remapOperand`, so its bytes are byte-identical.
  let rmap := if bodyHasCall body then remapOperandCalleeSave body tbl (abi := abi)
              else remapOperand body tbl (abi := abi)
  let isBinop (opn : String) : Bool := isTwoAddrBinop opn
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  let bodyIsU64 : Bool := body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => hasSuffix opn ":64"
    | _ => false)
  -- ABI MOV widths. See `physBodyWithStoresImpl` for the buffer-leg
  -- (`abiMovBuf`, narrow `MOV:16`/`MOV:8`) vs spill-routing-leg (`abiMovReg`,
  -- full-width) split; `abiW = 0` makes both `MOV:64`/`MOV` (byte-identical).
  -- `abiW = 256` (batch8 packed SoA) makes both `VMOVDQU`.
  let abiMovReg : String :=
    if abiW == 256 then "VMOVDQU" else if bodyIsU64 then "MOV:64" else "MOV"
  let abiMovBuf : String :=
    if abiW == 16 then "MOV:16"
    else if abiW == 8 then "MOV:8"
    else abiMovReg
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  let n := outStoreMap.length
  let total := numBindings body
  let firstOutIdx := total - n
  let nArgs := virtBodyNumArgs body
  -- Build a list of (virtPosition, argSlot) pairs: the first-use position of
  -- each argument slot. We use this to insert the load just before the
  -- corresponding instruction.
  let firstUseMap : Array (Option Nat) := -- argSlot s -> first virt pos
    Id.run do
      let mut arr : Array (Option Nat) := Array.replicate nArgs none
      for (i, virtIdx) in body.zipIdx do
        match i.li_i with
        | .Lopn _ _ srcs =>
            for src in srcs do
              match src with
              | .reg n =>
                  for s in (List.range nArgs) do
                    if n == argName s && (arr[s]?.getD none).isNone then
                      arr := arr.set! s (some virtIdx)
              | _ => pure ()
        | _ => pure ()
      return arr
  -- For each virtual position, list of (argSlot, base, off) loads to emit
  -- BEFORE that position.
  let loadsAtPos : Nat → List (Nat × String × Nat) := fun pos =>
    (List.range nArgs).filterMap (fun s =>
      match firstUseMap[s]?.getD none with
      | some fpos =>
          if fpos == pos then
            match inLoadMap s with
            | some (base, off) => some (s, base, off)
            | none => none
          else none
      | none => none)
  ((body.zipIdx).flatMap (fun ⟨i, virtIdx⟩ =>
    -- Inline ABI-prologue loads to emit BEFORE this instruction's expansion.
    -- Each load is preceded by `mov R14, [qsave.RSI]` to recover the input
    -- pointer (since R14 may have been overwritten with RDI by a prior
    -- inline output store). The recovery is unconditional rather than
    -- tracking state since the cost (one extra MOVQ per load) is negligible
    -- and the simpler code makes the reasoning local.
    let loads : Lcmd := (loadsAtPos virtIdx).flatMap (fun ⟨s, base, off⟩ =>
      let phys := physNameForBody body tbl (argName s) abi
      let dst : LOperand := .reg phys
      let memSrc : LOperand := .reg (memName loadBase off)
      let reloadIn : Linstr :=
        ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg (abiLoadSave base)]⟩
      if dst.isSpill then
        [reloadIn,
         ⟨0, .Lopn [.reg reloadScratch] abiMovBuf [memSrc]⟩,
         ⟨0, .Lopn [dst] abiMovReg [.reg reloadScratch]⟩]
      else
        [reloadIn,
         ⟨0, .Lopn [dst] abiMovBuf [memSrc]⟩])
    -- The binding index of this position: count of Lopns strictly before it
    -- in the body. (The body's last instruction is `Lret`, not an Lopn, so
    -- non-Lopn positions get `bidx = total` which is past the last-n range.)
    let bidx := ((body.take virtIdx).filter (fun li =>
      match li.li_i with | .Lopn _ _ _ => true | _ => false)).length
    let expanded : Lcmd :=
      match i.li_i with
      | .Lopn (d :: _) opn (s0 :: s1 :: _) =>
          if isBinop opn then
            match (if isShift opn then shiftImmVal s1 else none) with
            | some v =>
                (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
                  (fun r => ⟨i.li_ii, r⟩)
            | none =>
                (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
                  (fun r => ⟨i.li_ii, r⟩)
          else
            -- three-source carry ops keep all sources (no truncation).
            match i.li_i with
            -- A `STOREIDX` (srcs `[arrIdx, val]`) whose remapped value source is
            -- a spill slot would render as an illegal `mov mem, mem` (the mirror
            -- of the LOAD case). Route the value through `R15` (store fix).
            | .Lopn [d'] opn' [addr, val] =>
                if isMemStore opn' then
                  -- Reload the memref base pointer from its red-zone qsave slot
                  -- into R14 immediately before the store: the RA-assigned ABI
                  -- register holding it has been clobbered by the body.
                  let (baseReload, addr') := reloadMemrefBase memrefBaseReload (rmap addr)
                  (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
                  (legalizeMemStoreK (idxConst shiftImm addr) (rmap d') addr' (rmap val) opn'
                     (movFor opn')).map (fun r => ⟨i.li_ii, r⟩)
                else
                  (legalizeSpillDst [rmap d'] opn' [rmap addr, rmap val]).map
                    (fun r => ⟨i.li_ii, r⟩)
            | .Lopn dsts opn srcs =>
                (legalizeSpillDst (dsts.map rmap) opn (srcs.map rmap)).map
                  (fun r => ⟨i.li_ii, r⟩)
            | other => [⟨i.li_ii, other⟩]
      -- Native immediate shift / rotate (`ROR:n` / `SHL:n` / …): one-source
      -- in-place op. Route a spilled operand through R15 (spill legalize).
      | .Lopn [d] opn [s] =>
          if isNativeShiftRotate opn then
            (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
          else if isMemLoad opn then
            -- A `LOAD`/`LOADIDX` into a spill slot would render as an illegal
            -- `mov mem, mem`; route through `R15` (whole-state load fix).
            -- First reload the memref base pointer from its qsave slot into R14.
            let (baseReload, s') := reloadMemrefBase memrefBaseReload (rmap s)
            (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
            (legalizeMemLoad (rmap d) s' opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
          else
            (legalizeOneSrc bodyIsU64 opn (rmap d) (rmap s)).map (fun r => ⟨i.li_ii, r⟩)
      | .Lopn dsts opn srcs =>
          [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
      | other => [⟨i.li_ii, other⟩]
    -- If this binding is one of the last n, append a store of its dst. The
    -- store is preceded by a reload of the out-pointer into R14 (the body
    -- may have clobbered R14 since it's the secondary scratch). When the src
    -- is itself a spill slot, route it through R15 first.
    let store : Lcmd :=
      match i.li_i with
      | .Lopn (d :: _) _ _ =>
          if bidx ≥ firstOutIdx ∧ bidx < total then
            let outIdx := bidx - firstOutIdx
            match outStoreMap[outIdx]? with
            | some (_base, off) =>
                let src := rmap d
                let memDst : LOperand := .reg (memName storeBase off)
                let reloadOut : Linstr :=
                  ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg abiSaveRdiName]⟩
                if src.isSpill then
                  [⟨0, .Lopn [.reg reloadScratch] abiMovReg [src]⟩,
                   reloadOut,
                   ⟨0, .Lopn [memDst] abiMovBuf [.reg reloadScratch]⟩]
                else
                  [reloadOut,
                   ⟨0, .Lopn [memDst] abiMovBuf [src]⟩]
            | none => []
          else []
      | _ => []
    -- After a real in-loop `Lcall`, reload each loop-invariant pointer base the
    -- looped-call barrier overflowed into a caller-saved register from its qsave
    -- slot (see `physBodyWithStoresImpl`). Empty (byte-identical) when the
    -- loop-carried set fits the four callee-saved registers.
    let callReload : Lcmd :=
      match i.li_i with
      | .Lcall _ _ =>
          callArgBaseReload.map (fun (physReg, qsave) =>
            (⟨0, .Lopn [.reg physReg] "MOVQ" [.reg qsave]⟩ : Linstr))
      | _ => []
    loads ++ expanded ++ callReload ++ store))

/-- **The register arm of the renaming of `physBodyWithStores` is `allocName`**: the
    operand renaming `rmap` of `physBodyWithStores` over a table `tbl` sends the register
    operand `.reg n` to `.reg (allocName body tbl n)`. -/
theorem physBodyWithStores_allocName (body : Lcmd) (tbl : Array Nat) (n : String)
    (abi : IsaAbi) :
    (if bodyHasCall body then remapOperandCalleeSave body tbl (.reg n) (abi := abi)
      else remapOperand body tbl (.reg n) (abi := abi))
      = .reg (allocName body tbl n abi) := by
  unfold allocName
  split <;> rfl

/-- **The constant-shape base reload of a physical body**: every instruction that
    `reloadArrImm` rewrites (a `ZEROARR` or `STOREIMM` whose register base has a save slot) is
    replaced by its reload, each instruction of the reload carrying the instruction index of
    the original; every other instruction is kept. -/
def reloadArrImmBody (memrefBaseReload : String → Option String) (l : Lcmd) : Lcmd :=
  l.flatMap fun r =>
    match reloadArrImm memrefBaseReload r.li_i with
    | some l' => l'.map fun x => (⟨r.li_ii, x⟩ : Linstr)
    | none => [r]

theorem reloadArrImmBody_append (mbr : String → Option String) (a b : Lcmd) :
    reloadArrImmBody mbr (a ++ b) = reloadArrImmBody mbr a ++ reloadArrImmBody mbr b :=
  List.flatMap_append ..

theorem reloadArrImmBody_flatMap {α : Type} (mbr : String → Option String) (f : α → Lcmd)
    (l : List α) :
    reloadArrImmBody mbr (l.flatMap f) = l.flatMap fun a => reloadArrImmBody mbr (f a) :=
  List.flatMap_assoc

/-- A body none of whose instructions has a constant-shape base reload is its own reload. -/
theorem reloadArrImmBody_eq_self {mbr : String → Option String} {l : Lcmd}
    (h : ∀ r ∈ l, reloadArrImm mbr r.li_i = none) : reloadArrImmBody mbr l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp_all [reloadArrImmBody]

/-- **A body without `ZEROARR` and `STOREIMM` keeps its bytes** under the constant-shape base
    reload. -/
theorem reloadArrImmBody_eq_of_noArrImm (mbr : String → Option String) {l : Lcmd}
    (h : ∀ r ∈ l, ∀ ds o ss, r.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    reloadArrImmBody mbr l = l := by
  refine reloadArrImmBody_eq_self fun r hr => ?_
  obtain ⟨ii, w⟩ := r
  cases w with
  | Lopn ds o ss =>
    obtain ⟨h1, h2⟩ := h _ hr ds o ss rfl
    exact reloadArrImm_of_ne mbr h1 h2
  | _ => simp [reloadArrImm]

/-- An instruction of the reloaded body is an instruction of the body, or an instruction of
    the reload of an instruction `i` of the body, at the index of `i`. -/
theorem mem_reloadArrImmBody {mbr : String → Option String} {l : Lcmd} {r : Linstr}
    (hr : r ∈ reloadArrImmBody mbr l) :
    r ∈ l ∨ ∃ i ∈ l, ∃ l', reloadArrImm mbr i.li_i = some l' ∧ r.li_ii = i.li_ii ∧
      r.li_i ∈ l' := by
  obtain ⟨i, hi, hri⟩ := List.mem_flatMap.mp hr
  revert hri
  cases hre : reloadArrImm mbr i.li_i with
  | none => exact fun hri => .inl (by simp_all)
  | some l' =>
    intro hri
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hri
    exact .inr ⟨i, hi, l', hre, rfl, hx⟩

/-- **The reload commutes with a filter** `p` that takes, on each instruction of a reload,
    the value it takes on the reloaded instruction. -/
theorem reloadArrImmBody_filter {mbr : String → Option String} (p : Linstr → Bool) (l : Lcmd)
    (hp : ∀ i l', reloadArrImm mbr i.li_i = some l' → ∀ x ∈ l', p ⟨i.li_ii, x⟩ = p i) :
    (reloadArrImmBody mbr l).filter p = reloadArrImmBody mbr (l.filter p) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons]
    simp only [reloadArrImmBody, List.flatMap_cons, List.filter_append] at ih ⊢
    rw [ih]
    cases hre : reloadArrImm mbr a.li_i with
    | none => cases hpa : p a <;> simp [hpa, hre]
    | some l' =>
      have hl := hp a l' hre
      cases hpa : p a
      · simp only [Bool.false_eq_true, ite_false]
        rw [List.filter_eq_nil_iff.mpr]
        · rfl
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          simp [hl y hy, hpa]
      · simp only [ite_true, List.flatMap_cons, hre, List.append_left_inj]
        rw [List.filter_eq_self.mpr]
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simp [hl y hy, hpa]

/-- The per-position emitter of `physBodyWithStores`: the instructions that one
    virtual position `(i, virtIdx)` of `body` contributes, as the concatenation
    of its inline ABI-prologue loads, its register-allocated expansion, its
    post-call pointer reloads and its inline output store.

    `physBodyWithStores_eq_flatMap` states the agreement with the emitter:
    `physBodyWithStores` is the `flatMap` of this function over `body.zipIdx`,
    and that equality holds by `rfl`. Every argument is an argument of
    `physBodyWithStores`, and the allocation table, the operand remap, the ABI
    move mnemonics and the argument-load schedule are derived here exactly as
    they are there, so an edit to one side that the other does not receive fails
    the equality. -/
def physPositionEmit (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat := 0)
    (memrefBaseReload : String → Option String := fun _ => none)
    (callArgBaseReload : List (String × String) := [])
    (reservedVec : List Nat := []) : Linstr × Nat → Lcmd :=
  let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
  let rmap := if bodyHasCall body then remapOperandCalleeSave body tbl
              else remapOperand body tbl
  let isBinop (opn : String) : Bool := isTwoAddrBinop opn
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  let bodyIsU64 : Bool := body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => hasSuffix opn ":64"
    | _ => false)
  let abiMovReg : String :=
    if abiW == 256 then "VMOVDQU" else if bodyIsU64 then "MOV:64" else "MOV"
  let abiMovBuf : String :=
    if abiW == 16 then "MOV:16"
    else if abiW == 8 then "MOV:8"
    else abiMovReg
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  let n := outStoreMap.length
  let total := numBindings body
  let firstOutIdx := total - n
  let nArgs := virtBodyNumArgs body
  let firstUseMap : Array (Option Nat) :=
    Id.run do
      let mut arr : Array (Option Nat) := Array.replicate nArgs none
      for (i, virtIdx) in body.zipIdx do
        match i.li_i with
        | .Lopn _ _ srcs =>
            for src in srcs do
              match src with
              | .reg n =>
                  for s in (List.range nArgs) do
                    if n == argName s && (arr[s]?.getD none).isNone then
                      arr := arr.set! s (some virtIdx)
              | _ => pure ()
        | _ => pure ()
      return arr
  let loadsAtPos : Nat → List (Nat × String × Nat) := fun pos =>
    (List.range nArgs).filterMap (fun s =>
      match firstUseMap[s]?.getD none with
      | some fpos =>
          if fpos == pos then
            match inLoadMap s with
            | some (base, off) => some (s, base, off)
            | none => none
          else none
      | none => none)
  fun ⟨i, virtIdx⟩ =>
    let loads : Lcmd := (loadsAtPos virtIdx).flatMap (fun ⟨s, base, off⟩ =>
      let phys := physNameForBody body tbl (argName s)
      let dst : LOperand := .reg phys
      let memSrc : LOperand := .reg (memName loadBase off)
      let reloadIn : Linstr :=
        ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg (abiLoadSave base)]⟩
      if dst.isSpill then
        [reloadIn,
         ⟨0, .Lopn [.reg reloadScratch] abiMovBuf [memSrc]⟩,
         ⟨0, .Lopn [dst] abiMovReg [.reg reloadScratch]⟩]
      else
        [reloadIn,
         ⟨0, .Lopn [dst] abiMovBuf [memSrc]⟩])
    let bidx := ((body.take virtIdx).filter (fun li =>
      match li.li_i with | .Lopn _ _ _ => true | _ => false)).length
    let expanded : Lcmd :=
      match i.li_i with
      | .Lopn (d :: _) opn (s0 :: s1 :: _) =>
          if isBinop opn then
            match (if isShift opn then shiftImmVal s1 else none) with
            | some v =>
                (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
                  (fun r => ⟨i.li_ii, r⟩)
            | none =>
                (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
                  (fun r => ⟨i.li_ii, r⟩)
          else
            match i.li_i with
            | .Lopn [d'] opn' [addr, val] =>
                if isMemStore opn' then
                  let (baseReload, addr') := reloadMemrefBase memrefBaseReload (rmap addr)
                  (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
                  (legalizeMemStoreK (idxConst shiftImm addr) (rmap d') addr' (rmap val) opn'
                     (movFor opn')).map (fun r => ⟨i.li_ii, r⟩)
                else
                  (legalizeSpillDst [rmap d'] opn' [rmap addr, rmap val]).map
                    (fun r => ⟨i.li_ii, r⟩)
            | .Lopn dsts opn srcs =>
                (legalizeSpillDst (dsts.map rmap) opn (srcs.map rmap)).map
                  (fun r => ⟨i.li_ii, r⟩)
            | other => [⟨i.li_ii, other⟩]
      | .Lopn [d] opn [s] =>
          if isNativeShiftRotate opn then
            (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
          else if isMemLoad opn then
            let (baseReload, s') := reloadMemrefBase memrefBaseReload (rmap s)
            (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
            (legalizeMemLoad (rmap d) s' opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
          else
            (legalizeOneSrc bodyIsU64 opn (rmap d) (rmap s)).map (fun r => ⟨i.li_ii, r⟩)
      | .Lopn dsts opn srcs =>
          [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
      | other => [⟨i.li_ii, other⟩]
    let store : Lcmd :=
      match i.li_i with
      | .Lopn (d :: _) _ _ =>
          if bidx ≥ firstOutIdx ∧ bidx < total then
            let outIdx := bidx - firstOutIdx
            match outStoreMap[outIdx]? with
            | some (_base, off) =>
                let src := rmap d
                let memDst : LOperand := .reg (memName storeBase off)
                let reloadOut : Linstr :=
                  ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg abiSaveRdiName]⟩
                if src.isSpill then
                  [⟨0, .Lopn [.reg reloadScratch] abiMovReg [src]⟩,
                   reloadOut,
                   ⟨0, .Lopn [memDst] abiMovBuf [.reg reloadScratch]⟩]
                else
                  [reloadOut,
                   ⟨0, .Lopn [memDst] abiMovBuf [src]⟩]
            | none => []
          else []
      | _ => []
    let callReload : Lcmd :=
      match i.li_i with
      | .Lcall _ _ =>
          callArgBaseReload.map (fun (physReg, qsave) =>
            (⟨0, .Lopn [.reg physReg] "MOVQ" [.reg qsave]⟩ : Linstr))
      | _ => []
    loads ++ expanded ++ callReload ++ store

/-- The callee-saved-register restore epilogue: pops the 6 SysV callee-saved
    GP registers `(RBX, RBP, R12, R13, R14, R15)` from their red-zone save
    slots, restoring the caller's values before the function returns. Emitted
    just before the body's final `Lret`.

    R14/R15 are added (2026-05-27) for SysV ABI correctness: although the
    body's reload pass uses them as scratches, they are callee-saved per the
    SysV x86-64 ABI and must be restored. -/
def calleeSaveRestoreEpilogue : Lcmd :=
  [⟨0, .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"]⟩,
   ⟨0, .Lopn [.reg "RBP"] "MOVQ" [.reg "qsave.RBP"]⟩,
   ⟨0, .Lopn [.reg "R12"] "MOVQ" [.reg "qsave.R12"]⟩,
   ⟨0, .Lopn [.reg "R13"] "MOVQ" [.reg "qsave.R13"]⟩,
   ⟨0, .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.R14"]⟩,
   ⟨0, .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.R15"]⟩]

/-! ### 7f′. Register-residence coalescing (X25519 monolithic RA recovery)

The default export names each `Com` binding with a **fresh** SSA register
`r{depth}` (`comToBody`/`regName`), so the linear-scan allocator (`physTable`)
sees one live range per binding. For a deep straight-line body that only ever
touches a small fixed set of **logical** working slots — like the Poseidon2
permutation (16 lanes + 9 scratch = 25 slots, reused across 21 rounds) — this
is catastrophic: thousands of ranges exhaust the 15 GP registers and nearly
every value spills to the stack and is reloaded per use.

A **residence remap** collapses every body SSA name onto its logical working
slot, so the allocator scans the small slot universe instead. When the producer
supplies a `slotOfBinding : Nat → Nat` map (binding ordinal → logical slot), the
`n`-th body binding's def name `r{nArgs+n}` is rewritten to a residence-class
name `res{slotOfBinding n}`. Because the producer maintains the residence
invariant (a logical slot is overwritten only after its previous value is dead —
the X25519 monolithic register-residence discipline), this rewrite is
a pure α-relabeling: at every program point a read of `r{m}` and the read of the
residence class it collapses to resolve to the same most-recent definition, so
the body's denotation is unchanged.

The remap touches only the body's `r{…}` SSA names; argument names `a{j}` are
left intact (the ABI prologue's `inLoadMap`/`firstUse` logic keys on them), and
the `outStoreMap`/`inLoadMap` are slot-keyed, so they are unaffected. -/

/-- Rewrite one body register name under a residence remap. Body SSA names
    `r{k}` with `k ≥ nArgs` (i.e. body bindings, not arguments) are rewritten to
    `res{slotOfBinding (k - nArgs)}`; argument names `a{j}` and any other name
    pass through unchanged. -/
def residenceRenameName (nArgs : Nat) (slotOfBinding : Nat → Nat) (n : String) :
    String :=
  if n.startsWith "r" then
    match strDropToNat? n 1 with
    | some k => if k ≥ nArgs then "res" ++ toString (slotOfBinding (k - nArgs)) else n
    | none => n
  else n

/-- Rewrite one `LOperand` under the residence remap (register names only;
    immediates / array elements pass through). -/
def residenceRenameOperand (nArgs : Nat) (slotOfBinding : Nat → Nat) :
    LOperand → LOperand
  | .reg n => .reg (residenceRenameName nArgs slotOfBinding n)
  | o => o

/-- Apply the residence remap to a whole virtual body. Every `Lopn`'s
    destination and source register names are rewritten; non-`Lopn`
    instructions pass through. The op mnemonics, widths, immediates, memory
    references, and instruction order are all preserved, so the body still
    denotes the same value sequence — only the virtual-register *labels* change,
    collapsing the SSA universe onto the logical residence slots. -/
def residenceRenameBody (nArgs : Nat) (slotOfBinding : Nat → Nat) (body : Lcmd) :
    Lcmd :=
  body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        ⟨i.li_ii, .Lopn (dsts.map (residenceRenameOperand nArgs slotOfBinding)) opn
          (srcs.map (residenceRenameOperand nArgs slotOfBinding))⟩
    | _ => i)

/-- The residence-coalesced body uses at most `nArgs + |range slotOfBinding|`
    distinct register names — the small logical universe, not one per binding.
    Compiled `slotOfBinding` is provided as an `Array` lookup so the rewrite is
    a single `O(n)` pass with `O(1)` per-binding lookups. -/
def residenceArraySlotOf (slots : Array Nat) (n : Nat) : Nat :=
  slots[n]?.getD 0

/-- Materialize `regConst`-defined shift counts as `.imm` operands **before** the
    residence rename. The default shift-count → immediate resolution
    (`movImmTable`) keys on the unique `r{k}` SSA name of the `MOV r,#v`
    (`regConst`) that defines the count; but the residence rename collapses many
    such defs onto the same reused residence register (e.g. all the `sc0`
    constants land on one `res16`), so a name-keyed last-write-wins table would
    be ambiguous after renaming. We therefore resolve the count on the **unique
    pre-rename names**: any `SHL`/`SHR` whose count source `r{k}` is resolved to
    a constant `v` by `movImmTable body` has that source replaced by `.imm v`
    in place. The rename then leaves the immediate untouched, and the rest of the
    pipeline (`physBodyWithStores`, `lowerTwoAddrShiftImm`) emits the count as an
    `imm8`, avoiding the x86 forced-`CL` constraint — exactly as the non-resident
    path's dataflow oracle does, but resolved before the SSA universe collapses. -/
def materializeShiftCountImms (body : Lcmd) : Lcmd :=
  let movTbl := movImmTable body
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn (s0 :: s1 :: rest) =>
        if isShift opn then
          match s1 with
          | .reg nm =>
              match movImmLookup movTbl nm with
              | some v => ⟨i.li_ii, .Lopn dsts opn (s0 :: .imm v :: rest)⟩
              | none => i
          | _ => i
        else i
    | _ => i)

/-! ### 7f″. Memref-pointer thread canonicalization (in-place store aliasing)

A `memrefSetDyn wrk i v` lowers (`opToLinstrR` `.stackStore`) to
`STOREIDX r{depth}, (base,idx,scale), val`, whose **destination** `r{depth}`
names the dialect's "new array" result — but `memrefSetDyn` is an *in-place*
store: the result memref is the SAME pointer as its input `base`. The store
does NOT move the pointer. The default SSA export, however, gives the result a
**fresh** name, so each `memrefSetDyn` in a forward-threaded resident kernel
(ChaCha's `wrk_v0 → wrk_v1 → …`) becomes a distinct live range. The linear-scan
RA then allocates each threaded name to a *separate* GP register, and the
straight-line body reuses those registers as scratch between two accesses —
clobbering the pointer. A later `STOREIDX`/`LOADIDX` whose SIB base resolves to
such a clobbered register then self-addresses through a DATA word, not the
pointer ⇒ SIGSEGV.

The fix models the dialect's semantics directly: rewrite every `STOREIDX`
destination name to its SIB **base** name (its canonical root), and rewrite all
downstream references through the same alias. The whole `wrk_v0 → wrk_v1 → …`
chain collapses onto a single name (the original array argument `aj`), so:

* the RA sees ONE long-lived array-pointer slot, kept live across the body
  (it is read by every memref access), never reused as scratch; and
* every `LOADIDX`/`STOREIDX` SIB base is now the argument name `aj`, so the ABI
  export's `memrefBaseReload` (keyed on `phys(aj)`) reloads the pointer from its
  red-zone qsave slot before *every* access — not just the first.

The rewrite is a pure α-relabeling (`memrefSetDyn`'s result and its input
pointer denote the same memref), so the body's value sequence is unchanged.

It touches ONLY bodies that contain a `STOREIDX` (the memref / 2-pointer ABI
path). Scalar-word kernels (MayoUov/MontRedc, routed through
`inLoadMap`/`outStoreMap`) emit no `STOREIDX` — `arrChainAlias` is empty for
them, and `canonicalizeMemrefThread` is the identity, so their bytes are
unchanged. -/

/-- Build the in-place-store alias map for a body: `dst ↦ canonical(base)` for
    every `STOREIDX dst, (base,idx,scale), val`. Processed in program order with
    each `base` already resolved through earlier aliases, so the map sends every
    threaded array name straight to its chain root (the array argument). Names
    that never name a memref-store result are absent (resolve to themselves). -/
def arrChainAlias (body : Lcmd) : Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String String := {}
  let resolve (m : Std.HashMap String String) (n : String) : String :=
    m.getD n n
  for i in body do
    match i.li_i with
    | .Lopn [.reg dst] opn (.arrIdx base _ _ :: _) =>
        if isMemStore opn then
          m := m.insert dst (resolve m base)
    | _ => pure ()
  return m

/-- Resolve a register name through the memref-thread alias map (identity off
    the map). The map is pre-flattened to chain roots, so one lookup suffices. -/
def canonMemrefName (m : Std.HashMap String String) (n : String) : String :=
  m.getD n n

/-- Rewrite one `LOperand`'s register names through the memref-thread alias map
    (both plain `reg` names and a SIB `arrIdx` base/index). Immediates and
    compile-time array elements pass through. -/
def canonMemrefOperand (m : Std.HashMap String String) : LOperand → LOperand
  | .reg n => .reg (canonMemrefName m n)
  | .arrIdx base idx scale => .arrIdx (canonMemrefName m base) (canonMemrefName m idx) scale
  | o => o

/-- Collapse a body's forward-threaded memref-pointer chain onto its root name
    (the array argument), so the in-place `memrefSetDyn` result aliases its input
    pointer. See `arrChainAlias` for the rationale. The op mnemonics, widths,
    immediates, and instruction order are preserved — only the threaded array
    *labels* change — so the body still denotes the same value sequence. When the
    body has no `STOREIDX` (every scalar kernel), the alias map is empty and this
    is the identity (existing bytes unchanged). -/
def canonicalizeMemrefThread (body : Lcmd) : Lcmd :=
  let m := arrChainAlias body
  if m.isEmpty then body
  else body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        ⟨i.li_ii, .Lopn (dsts.map (canonMemrefOperand m)) opn
          (srcs.map (canonMemrefOperand m))⟩
    | _ => i)

/-- Whether an `extCall` argument vector forwards the enclosing function's
    parameters unchanged: entry `j` is the parameter at root position `j`, i.e.
    De Bruijn index `nArgs - 1 - j` in the newest-first context. `expected`
    counts down from `nArgs - 1`; the vector must be non-empty and its last
    entry the oldest parameter (index `0`). -/
def argsForwardParams {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → Nat → Bool
  | [], .nil, _ => false
  | _ :: _, .cons v rest, expected =>
      varIndex v == expected &&
        (match rest with
         | .nil => expected == 0
         | .cons _ _ => expected != 0 && argsForwardParams rest (expected - 1))

/-- Recognise a degenerate zero-marshalling forwarder `Com`: a single
    `extCall sym` binding whose arguments forward the enclosing parameters
    unchanged (`argsForwardParams`) and which is returned directly (`.ret .here`).
    Returns the callee symbol only when the inbound ABI `abiArgs` already equals
    the callee's SysV argument registers in order (`RDI, RSI, RDX, …`) and every
    parameter is forwarded — so `call sym; ret` needs no argument moves or result
    staging. Every other `Com` (and any argument permutation, partial forward, or
    non-`.here` return) yields `none` and falls through to the marshalling
    export unchanged. -/
def degenerateForwarderSym? {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (abiArgs : List String) : Option String :=
  match com with
  | .var e body =>
      match e, body with
      | ⟨.extCall sym argTys _, _, args⟩, .ret v =>
          if varIndex v == 0
             && Γ.length ≥ 1
             && argTys.length == Γ.length
             && abiArgs == (List.range Γ.length).map (fun j => sysvArgRegs.getD j "")
             && argsForwardParams args (Γ.length - 1)
          then some sym else none
      | _, _ => none
  | _ => none

/-- **The result-liveness pin** of a register result returned in `RAX`: when `retToRax` is
    set and there are no output stores, the liveness instruction reading the first result
    name of `res`, placed after the body in the input of the allocation. The return move
    reads the register of that name after the body, so the trace of the allocation reads it
    at its last position and its live range extends to the end of the body. The allocated
    body drops the instruction with the argument-liveness pin. Empty otherwise. -/
def resLivePin (retToRax : Bool) (outStoreMap : OutStoreMap) (res : List String) : Lcmd :=
  if retToRax && outStoreMap.isEmpty then
    match res.head? with
    | some rn => [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" [.reg rn]⟩]
    | none => []
  else []

/-- **The ABI-wrapping tail of `comToLfundefPhysAbi` with its allocation certificate**:
    the physical `lfundef` of an already-built virtual `Lfundef` and the certificate
    `allocCertOf` of the allocator input body over the table that `physBodyWithStores`
    reads (`physAllocTbl` at the output stores and the reserved vector indices),
    computed with that table. `comToLfundefPhysAbiFromVirt` is its first component. -/
def comToLfundefPhysAbiFromVirtCert (virt0 : Lfundef)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false)
    (forwarderBody? : Option Lcmd := none)
    (reserveVecScratch : Bool := false)
    (retToRax : Bool := false) (abi : IsaAbi := x86Abi) :
    Lfundef × List (String × String) :=
  -- `reserveVecScratch` (batch8 SoA path): cap the vector RA pool at
  -- `numVecRegs - 1`, reserving `%ymm15` as the printer's spill-legalization
  -- scratch so its bounce needs no per-op save/restore. `false` (every existing
  -- caller) uses the full pool, so the emitted bytes are unchanged.
  let reservedVec : List Nat := if reserveVecScratch then [numVecRegs - 1] else []
  -- Expand any straight-line `CALL:`/`CALLN:` leaf-call shadow into a real
  -- `Lcall` + SysV marshalling (`expandCallShadows`) before the RA runs, so the
  -- linear scan sees the call as a caller-save clobber barrier (the marshalled
  -- `MOV RDI,…`/`MOV dst,RAX` land beside the real `Lcall`). Identity on a
  -- call-free body, so every existing kernel is byte-identical.
  let virt0 := { virt0 with lfd_body := expandCallShadows virt0.lfd_body }
  -- Optional register-residence coalescing: collapse every body SSA name
  -- onto its logical working slot before the linear-scan allocation, so the RA
  -- keeps the small fixed working set register-resident instead of one live
  -- range per binding. `none` (every existing caller) leaves the body
  -- byte-identical to the per-binding-SSA export.
  let virtR :=
    match residence with
    | none => virt0
    | some slots =>
        let nArgs := virt0.lfd_arg.length
        -- Resolve `regConst`-defined shift counts to immediates on the unique
        -- pre-rename names, THEN collapse the SSA universe onto residence slots.
        let bodyImm := materializeShiftCountImms virt0.lfd_body
        { virt0 with
          lfd_body := residenceRenameBody nArgs (residenceArraySlotOf slots)
                        bodyImm }
  -- Memref-pointer thread canonicalization (in-place store aliasing): collapse
  -- every forward-threaded `memrefSetDyn` result name onto its input array
  -- pointer (its SIB base), so the array pointer is ONE long-lived RA slot kept
  -- live across the body and every `LOADIDX`/`STOREIDX` SIB base is the array
  -- argument `aj` (so `memrefBaseReload` reloads it before every access — the
  -- segfault fix). The identity on scalar kernels (no `STOREIDX`), so their
  -- bytes are unchanged. Runs after the residence rename so the alias map sees
  -- the post-rename array names.
  -- Argument-liveness pin (3+-argument signatures). The linear-scan RA sees an
  -- argument used only as a late `LOADIDX`/`STOREIDX` SIB base as "born late", so
  -- a scalar argument that dies early can be allocated the SAME physical register
  -- — which makes `memrefBaseReload` (keyed on the physical register) reload the
  -- array base from the wrong argument's qsave slot. A synthetic `LIVEPIN` that
  -- reads every argument at entry forces all arguments live from entry, so each
  -- gets a distinct register; it is filtered out after `physBodyWithStores`.
  -- ≤2-argument signatures inject nothing, so their bytes are unchanged —
  -- UNLESS the caller opts in with `forceLivePin` (a 2-pointer kernel whose
  -- OUT arg is born late can coalesce onto the IN arg's register, making the
  -- register-keyed `memrefBaseReload` map ambiguous: the m31 reduce loaded its
  -- input through the OUT pointer's qsave slot).
  let nArgs := virtR.lfd_arg.length
  let livePin : Lcmd :=
    if nArgs ≥ 3 || forceLivePin then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range nArgs).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []
  let virt := { virtR with
    lfd_body := livePin ++ canonicalizeMemrefThread virtR.lfd_body
      ++ resLivePin retToRax outStoreMap virtR.lfd_res }
  -- Output-liveness-extended allocation table (multi-output store fix): the `n`
  -- designated outputs occupy `n` DISTINCT physical registers across the epilogue
  -- stores (see `bodyTraceOut`). EVERY consumer of `tbl` here (prologue,
  -- `buildArgPtrMaterialize`, `memrefBaseReload`, and the inline stores in
  -- `physBodyWithStores` below) must use the SAME table so the body's physical
  -- register names agree. `physTableOut … []` = `physTable (bodyTrace …)`, so the
  -- register-ABI / single-store kernels are byte-identical.
  -- For a STRAIGHT-LINE CALL body, the liveness-computed call-barrier
  -- relocation is composed into the table HERE, once — every seam below
  -- (including the frame sizing, which must see the relocation's fresh spill
  -- indices) then reads one coherent table via `physNameForBody`'s plain
  -- lookup. Identity on call-free and looped bodies.
  let tbl := straightCallComposeTable virt.lfd_body
    (physTableOut virt.lfd_body outStoreMap reservedVec abi)
  -- Each EXTRA SysV argument register beyond `RDI`/`RSI` (`RDX`/`RCX`/`R8`/`R9`,
  -- a 3+-argument signature) gets its own red-zone qsave slot, appended after the
  -- fixed prologue, so the argument materialize / SIB-base reloads can source it
  -- from a stable slot. For ≤2-argument signatures `abiArgs.drop 2 = []`, so the
  -- prologue bytes are unchanged.
  let extraInputSaves : Lcmd :=
    (abiArgs.drop 2).filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none)
  let prologue := buildPrologue virt tbl inLoadMap ++ extraInputSaves
  -- Materialize the pointer arguments into the body's RA-assigned register/slot
  -- (the 2-pointer memref ABI: the body uses `aj` directly as a LOADIDX/STOREIDX
  -- SIB base, but the RA placed `aj` in a register/spill that the prologue never
  -- copied the SysV argument register into — see `buildArgPtrMaterialize`). For
  -- the scalar-word ABI (`inLoadMap` non-empty) this is empty.
  let argMat := buildArgPtrMaterialize virt tbl abiArgs inLoadMap abi
  -- Use physBodyWithStores to insert inline stores after each output binding.
  -- This solves the SSA liveness problem: the source `Com` `.ret`s a single
  -- value, so under register allocation only the LAST output register is alive
  -- at function exit; the other 15 have been reclaimed for later writes.
  -- Storing each output immediately after its binding preserves the value
  -- before any subsequent overwrite.
  -- Compose the caller's shift oracle with the dataflow `regConst`→imm resolver
  -- (`movImmOracle`): the caller's map wins; otherwise a count register defined
  -- by a body `MOV r,#v` (a `regConst v`) is resolved to `#v`. This lets a
  -- `regConst`-based producer (Poseidon2: shift counts 31/63 materialised by
  -- `regConst`) avoid the x86 forced-`CL` shift-count constraint. For
  -- ChaCha/SHA/Keccak (counts via `immSlotMap` → `.imm`, or via the caller
  -- oracle) `movImmOracle` returns none for the relevant names, so behaviour is
  -- unchanged. `dataflow` is bound here so its `Array` is built exactly once
  -- (not per shift-count lookup).
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  -- Build the memref-base reload map (2-pointer memref ABI): each pointer arg
  -- `aj` (one NOT covered by `inLoadMap`, with a red-zone qsave slot) is
  -- RA-assigned to a physical register that the body reuses as a scratch — so
  -- every `LOADIDX`/`STOREIDX` SIB base must be reloaded from `qsave.<abiReg>`
  -- into R14 immediately before the access (`reloadMemrefBase`). The map keys on
  -- the physical base register name `phys(aj)` and yields the qsave slot. For the
  -- scalar-word ABI (`inLoadMap` non-empty) it is empty, so the existing scalar
  -- kernels (MayoUov/MontRedc, which route through `inLoadMap`/`outStoreMap`) are
  -- unaffected.
  let memrefBaseReload : String → Option String :=
    let pairs : List (String × String) :=
      (abiArgs.zipIdx).filterMap (fun ⟨abiReg, j⟩ =>
        match inLoadMap j with
        | some _ => none
        | none =>
            -- `abiSlotOfExt`: a 3rd+ array argument (`RDX`/…) reloads its SIB base
            -- from its own qsave slot instead of the `RSI` input slot, and a stack
            -- argument from the caller's stack word.
            match abiSlotOfExt abiReg with
            | some saveName =>
                let phys := physNameForBody virt.lfd_body tbl (argName j) abi
                some (phys, saveName)
            | none => none)
    fun base => (pairs.find? (fun p => p.1 == base)).map Prod.snd
  -- Drop the synthetic argument-liveness pin (it carried no value, only liveness).
  let bodyWithInlineStores := (physBodyWithStores shiftImm' virt.lfd_body
    inLoadMap reloadScratch2 outStoreMap reloadScratch2 abiW memrefBaseReload
    (reservedVec := reservedVec) (abi := abi)).filter
    (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
  -- Straight-line-call return materialization: the liveness-computed barrier
  -- homes the final capture (`MOV dst, RAX`) in a callee-saved register or a
  -- frame spill, so `RAX` holding the `Com`'s return value at `Lret` is not
  -- guaranteed by the last call's return alone (the caller-side functional-leaf
  -- ABI reads the result from `RAX`). Move the barrier-resolved return name
  -- back into `RAX` before the callee-saved restore. Emitted only for
  -- `bodyStraightCall` bodies, and for every body when `retToRax` is set (a
  -- register result returned in `RAX`), whose return name is a body slot and
  -- does not already resolve to `RAX`; with `retToRax` unset every call-free /
  -- looped kernel is byte-identical.
  let retMat : Lcmd :=
    if bodyStraightCall virt.lfd_body || retToRax then
      match virt.lfd_res.head? with
      | some rn =>
          if nameSlot virt.lfd_body rn < (bodyNames virt.lfd_body).length then
            let phys := physNameForBody virt.lfd_body tbl rn abi
            if phys == sysvRetReg then []
            -- MOVQ (64-bit): the returned value is a full word/pointer — an
            -- untagged MOV renders `movl` and TRUNCATES a returned pointer
            -- to 32 bits (harness segfault on dereference).
            else [⟨0, .Lopn [.reg sysvRetReg] "MOVQ" [.reg phys]⟩]
          else []
      | none => []
    else []
  -- Insert the callee-saved-register restore just before the final `Lret`.
  let bodyWithRestore :=
    insertEpilogue bodyWithInlineStores (retMat ++ calleeSaveRestoreEpilogue)
  -- Degenerate zero-marshalling forwarder (`forwarderBody?`, supplied by the
  -- caller): a `Com` that is a single `extCall sym` binding forwarding the
  -- enclosing parameters unchanged and returned directly, whose inbound ABI
  -- already equals the callee's SysV argument registers. Its body is
  -- `call sym; ret` with no argument moves or result staging — bypassing the
  -- `prologue`/`argMat`/marshalling above. Only the `lfd_body` field is
  -- affected; every other field is the same structure literal as the general
  -- path. `none` yields `prologue ++ argMat ++ bodyWithRestore` byte-for-byte.
  ({ virt with
    lfd_body := forwarderBody?.getD (prologue ++ argMat ++ bodyWithRestore)
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := [] }, allocCertOf virt.lfd_body tbl abi)

/-- The ABI-wrapping tail of `comToLfundefPhysAbi`, over an already-built virtual
    `Lfundef` (`comToLfundef`'s output): the function of
    `comToLfundefPhysAbiFromVirtCert`. Everything here operates on the flat,
    string-named body, so an emit path that produces the virtual body by other
    means — a fused lowering that avoids a quadratic intermediate `Com` — calls
    this directly. `forwarderBody?` supplies the degenerate zero-marshalling
    forwarder body when applicable (`none` on the general path).

    * `shiftImm` — legacy SSA-name-keyed shift-count oracle.
    * `inLoadMap` — argument slot → `(base, off)` memory load (default: none —
      which reproduces `comToLfundefPhys`'s register-only behaviour).
    * `outStoreMap` — list of output store targets (default: empty — no stores).
    * `abiArgs` — the `lfd_arg` list (default: `["RDI", "RSI"]` for `out, inp`).
    * `abiTyin` — the `lfd_tyin` list (default: two 64-bit pointer widths).
-/
def comToLfundefPhysAbiFromVirt (virt0 : Lfundef)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false)
    (forwarderBody? : Option Lcmd := none)
    (reserveVecScratch : Bool := false)
    (retToRax : Bool := false) (abi : IsaAbi := x86Abi) :
    Lfundef :=
  (comToLfundefPhysAbiFromVirtCert virt0 shiftImm inLoadMap outStoreMap abiArgs abiTyin
    residence abiW forceLivePin forwarderBody? reserveVecScratch retToRax abi).1

/-- The function of `comToLfundefPhysAbiFromVirtCert` is `comToLfundefPhysAbiFromVirt`. -/
theorem comToLfundefPhysAbiFromVirtCert_fst (virt0 : Lfundef) (shiftImm : ShiftImmOracle)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap) (abiArgs : List String)
    (abiTyin : List Nat) (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool)
    (forwarderBody? : Option Lcmd) (reserveVecScratch retToRax : Bool) (abi : IsaAbi) :
    (comToLfundefPhysAbiFromVirtCert virt0 shiftImm inLoadMap outStoreMap abiArgs abiTyin
        residence abiW forceLivePin forwarderBody? reserveVecScratch retToRax abi).1
      = comToLfundefPhysAbiFromVirt virt0 shiftImm inLoadMap outStoreMap abiArgs abiTyin
        residence abiW forceLivePin forwarderBody? reserveVecScratch retToRax abi := rfl

/-- The ABI-wrapped physical `lfundef` for a `Com`: same args/types as the
    underlying physical export, but `lfd_arg` is reset to a fixed 2-pointer
    SysV signature (`[RDI, RSI]` for the canonical `out, inp` C ABI), the body
    is prefixed with the prologue (loads inputs from `[RSI + ...]`) and
    suffixed with the epilogue (stores outputs to `[RDI + ...]`), and `lfd_res`
    is empty (the body returns its result via memory at `*out`). Builds the
    virtual `Lfundef` with `comToLfundef` and wraps it with
    `comToLfundefPhysAbiFromVirt`.

    * `shiftImm` — legacy SSA-name-keyed shift-count oracle.
    * `immSlotMap` — producer-level slot → constant map (default: none).
    * `inLoadMap` — argument slot → `(base, off)` memory load (default: none —
      which reproduces `comToLfundefPhys`'s register-only behaviour).
    * `outStoreMap` — list of output store targets (default: empty — no stores).
    * `abiArgs` — the `lfd_arg` list (default: `["RDI", "RSI"]` for `out, inp`).
    * `abiTyin` — the `lfd_tyin` list (default: two 64-bit pointer widths).
-/
def comToLfundefPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false)
    (retToRax : Bool := false) (abi : IsaAbi := x86Abi) :
    Lfundef :=
  comToLfundefPhysAbiFromVirt (comToLfundef com immSlotMap)
    (shiftImm := shiftImm) (inLoadMap := inLoadMap) (outStoreMap := outStoreMap)
    (abiArgs := abiArgs) (abiTyin := abiTyin) (residence := residence)
    (abiW := abiW) (forceLivePin := forceLivePin) (retToRax := retToRax) (abi := abi)
    (forwarderBody? := (degenerateForwarderSym? com abiArgs).map
      (fun sym => [⟨0, .Lcall none (sym, 0)⟩, ⟨0, .Lret⟩]))

/-- Export a `Com` to a 2-pointer-ABI physical-register, two-address `Lprog`.
    See `comToLfundefPhysAbi` for the ABI wrapping (prologue loads + epilogue
    stores around the verified two-address body). -/
def Com.toLprogPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false)
    (retToRax : Bool := false) (abi : IsaAbi := x86Abi) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, comToLfundefPhysAbi com shiftImm immSlotMap inLoadMap
                 outStoreMap abiArgs abiTyin residence abiW forceLivePin retToRax abi)] }

/-- Serialize the ABI-wrapped physical export to the textual lprog blob. -/
def Com.toLprogPhysAbiText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none) : String :=
  magic ++ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
              outStoreMap abiArgs abiTyin residence).toText ++ "\n"

/-- The ABI-wrapped physical export's bytes. -/
def Com.toLprogPhysAbiBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none) : ByteArray :=
  (Com.toLprogPhysAbiText com fname shiftImm immSlotMap inLoadMap
    outStoreMap abiArgs abiTyin residence).toUTF8

/-- Write the ABI-wrapped physical-register lprog blob to a file. -/
def Com.writeLprogPhysAbiFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (path : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none) :
    IO Unit :=
  IO.FS.writeBinFile path
    (Com.toLprogPhysAbiBytes com fname shiftImm immSlotMap inLoadMap
       outStoreMap abiArgs abiTyin residence)

/-! ### 7g. Physical-register export of a looped `ComL`

`comLToBody` (§3b) lowers a fixed-trip `ComL` to a **rolled** control-flow body
(one `Llabel`/`Lcond` back-edge, **one** body copy), but it emits pre-RA SSA: the
accumulator is `regName curDepth`, the trip counter `loopCtr d` (`Lctr<d>`), and
the loop body's temporaries the disjoint `loopReg d k` namespace (`L<d>_r<k>`).
Those names render as `%<UNKNOWN:rN>` placeholders — `as` cannot assemble them.

This section gives the looped `ComL` the **same physical register allocation**
the straight-line `Com` gets (§7e). The key observation is that the physical-RA
pass (`bodyTrace`/`physTable`/`physBody`/`remapOperand`) walks an *`Lcmd`* by
first-appearance of operand names — it is **agnostic to how those names were
produced**. Feeding it `comLToBody`'s output therefore allocates the loop body's
bindings exactly like any straight-line binding:

* the accumulator name is touched at the seed `MOV`, every trip's feedback, and
  is read every trip — so its live range spans the whole loop and the linear
  scan keeps it in **one fixed physical register** (loop-carried);
* the trip counter is touched at its `MOV`-init and every `SUB`/`CMP` — so it too
  stays in one fixed register across all trips;
* the body temporaries (`L<d>_r<k>`) are written-before-read each trip, so a
  single physical register, reused across trips, is the correct rolled semantics.

The back-edge instructions (`Llabel`, `Lcond`) carry no register-file slot
(`linstrRegNames` returns `none`), so they pass through `physBody` untouched —
the rolled shape (one body, real `jne .L<d>`) is preserved while every GP operand
becomes a real x86 register. The result is an **assemblable, byte-KAT'able**
looped `.s`, with no `%<UNKNOWN>`.

`ComL.toLfundefPhys` is the loop-aware mirror of `comToLfundefPhys` (§7e): it
runs the same arg-materialize prelude (`buildArgMaterializePhys`) and the same
`RAX` return epilogue, so a loop-free `ComL` produces a byte-identical `lfundef`
to `comToLfundefPhys` on its `Com` image (the straight-line path is unchanged —
this is purely additive). -/

/-- The physical, two-address `lfundef` for a **looped** `ComL` — the loop-aware
    mirror of `comToLfundefPhys`. The body is `comLToBody` (a rolled back-edge,
    one body copy) run through the SAME physical RA (`physBody`) as a straight-line
    `Com`: the accumulator and trip counter become loop-carried physical
    registers, the body temporaries reused physical registers across trips, and
    the back-edge (`Llabel`/`Lcond`) passes through untouched. No operand is left
    as an `%<UNKNOWN>` SSA name. SysV arguments are materialized into the body's
    RA-assigned registers at entry, and the result is moved into `RAX` before the
    final `Lret`. On a loop-free `ComL` this is byte-identical to
    `comToLfundefPhys` on its `Com` image (additive). -/
def ComL.toLfundefPhys {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) (abi : IsaAbi := x86Abi) :
    Lfundef :=
  let virt := ComL.toLfundef c immSlotMap
  -- Class-aware table (matches `physBody`'s `bodyPhysTable`): GP→GP, vector→XMM.
  -- For a pure-scalar body this is `physTable (bodyTrace …)`, so unchanged.
  let tbl := straightCallComposeTable virt.lfd_body (bodyPhysTable virt.lfd_body abi)
  let resPhys := virt.lfd_res.map (fun n => physNameForBody virt.lfd_body tbl n abi)
  -- Project `lfd_arg` to the argument registers `abi.argRegs` (as
  -- `comToLfundefPhys`); the body reads its arguments by their RA-assigned
  -- physical register after `physBody` rewrites every `aN` operand.
  let callRegArgs : List String := abi.argRegs
  let nArgsExported : Nat := min virt.lfd_arg.length callRegArgs.length
  let argSig := callRegArgs.take nArgsExported
  let tyinSig := virt.lfd_tyin.take nArgsExported
  -- Copy each SysV argument register into the physical register the RA assigned
  -- to the body's `argName j` (skipping copies already in place).
  let argMat := buildArgMaterializePhys virt tbl callRegArgs abi
  -- The rolled, physically-allocated loop body. `physBody` allocates the loop
  -- body's bindings (accumulator / counter / temps) exactly like a straight-line
  -- body; the `Llabel`/`Lcond` back-edge passes through untouched.
  let pbody := if bodyHasCall virt.lfd_body
               then physBodyCalleeSave shiftImm virt.lfd_body abi
               else physBody shiftImm virt.lfd_body abi
  -- Move the result into the SysV return register `RAX` before the trailing
  -- `Lret` (skipped when the result already lands in `RAX`).
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

/-! ### 7g″. Frame-allocating (self-owning) physical export (`ComL.toLfundefPhysFramed`)

`ComL.toLfundefPhys` (§7g) is **register-ABI-only**: every `stackArr`-typed array
argument is a *caller-passed SysV pointer*, materialised from `RDI/RSI/…` into its
RA-assigned register (`buildArgMaterializePhys`). A self-allocating kernel — one
that owns its array buffers in its **own** stack frame rather than receiving them
as pointer arguments (MAYO's parameterless `mayo_solve_gf16` self-test owns 53 KB
of local `A/y/r/x/P/P2` buffers) — cannot be expressed that way: there is no SysV
pointer for a local buffer, and the register-ABI export hard-sets `lfd_stk_max :=
0`, so `renderLfundef` opens no frame.

This section adds the **frame-allocating** export, purely additively (a new
function; §7g's register-ABI export is untouched). Instead of binding each array
base to a SysV argument register, it:

1. emits a `FRAME` directive (`Lopn [] "FRAME" [.imm frameBytes]`) as the body's
   first instruction — the array-ABI marker `frameSize` reads to open a real
   `leaq -F(%rsp), %rsp` frame (and `renderLinstrR` drops, issuing no x86 line);
2. sets `lfd_stk_max := frameBytes` on the exported `Lfundef`;
3. binds each local array base with `leaq off(%rsp), %reg` (`buildFrameBaseMaterialize`)
   — the array's frame region base loaded into the RA register the body uses as
   the `stackLoad`/`stackStore` SIB base. Unlike the register-ABI `argMat`, each
   `LEA` is self-contained (it reads only `%rsp`), so it is free of the
   §7g′ SysV-argument clobber chain — the k-th array role follows the k-th
   `localBases` entry, not the RA assignment.

The body's `stackLoad`/`stackStore` then address `off(%rsp,%idx,scale)` — a cell
of the self-owned frame region — with no caller pointer anywhere. There are no
incoming SysV pointer arguments, so `lfd_arg`/`lfd_tyin` are empty. -/

/-- Materialise each self-owned array base as `leaq off(%rsp), %reg` — the
    frame-allocating analogue of `buildArgMaterializePhys`. For the `j`-th entry
    `(name, off)` of `localBases`, `argName j` is the array parameter that the body
    threads as a `stackLoad`/`stackStore` SIB base; its RA-assigned physical
    register (`physNameForBody`) is loaded with the effective address `%rsp + off`
    (its region base in the self-allocated frame). Bases the body never references
    are skipped (as `buildArgMaterializePhys` skips unused args). A spilled base is
    routed through `reloadScratch` (`LEA R15, off(%rsp); MOVQ slot, R15`). Each
    `LEA` reads only `%rsp`, so — unlike the SysV-argument copy chain — no base
    clobbers another. -/
def buildFrameBaseMaterialize (virt : Lfundef) (tbl : Array Nat)
    (localBases : List (String × Nat)) (abi : IsaAbi := x86Abi) : Lcmd :=
  let body := virt.lfd_body
  (localBases.zipIdx).flatMap (fun ⟨(_name, off), j⟩ =>
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
      let phys := physNameForBody body tbl nm abi
      let dst : LOperand := .reg phys
      if dst.isSpill then
        [⟨0, .Lopn [.reg reloadScratch] "LEA:64" [.reg (memName "RSP" off)]⟩,
         ⟨0, .Lopn [dst] "MOVQ" [.reg reloadScratch]⟩]
      else
        [⟨0, .Lopn [dst] "LEA:64" [.reg (memName "RSP" off)]⟩])

/-! ### Packed-frame SIB base = `%rsp` directly (framed self-owning path only)

The register-allocated SIB base of a `stackLoad`/`stackStore` (`remapOperand`
resolves the array-base SSA name to a physical register) is unstable when the
packed frame region is threaded as the loop **product accumulator** through a
deep (3-nested) solve: the linear scan sees the array base as a loop-carried
value with fragmented live ranges and REUSES its physical register between
loops, so at whole-solve scale the SIB base collides with a loop counter
(gdb: `movq %val, (%rcx, %rax, 8)` with `%rcx` = a counter, not the frame
pointer, as the SIB base). A single-loop kernel (`coreDotPacked`) keeps the
base stable and works; the 3-deep whole solve does not.

The fix uses **`%rsp` itself** as the SIB base for a self-owning
(`toLfundefPhysFramed`) function that owns a **single** array region at frame
offset `0` and issues no call. After the prologue `leaq -F(%rsp), %rsp` the
frame base IS `%rsp`, and — because the function is call-free with no mid-body
push/pop (the callee-saved brackets sit OUTSIDE the frame alloc) — `%rsp` is
stable across the whole body, so `(%rsp, %idx, 8)` addresses frame cell `idx`
correctly throughout. `%rsp` is a legal SIB base.

* NO dedicated base register is reserved and NO register is evicted from the
  allocatable pool — this is what avoids the register-pressure spillover that a
  pinned-register eviction caused (the innermost index then collided at 3-deep
  nesting);
* every `STOREIDX`/`LOADIDX` SIB base is rewritten to `%rsp` (the computed index
  register and scale are unchanged), so every cell access is `(%rsp, %idx, 8)`;
* no base LEA in the prologue — the frame alloc `leaq -F(%rsp), %rsp` already
  establishes `%rsp` as the base — and no callee-saved push/pop is added on
  account of the base.

This is scoped to the single-region (offset-0), call-free framed path; a
multi-region, offset-shifted, or call-issuing framed function keeps the
register-allocated base (unchanged), and the register-ABI exports
(`toLfundefPhys`/`toLfundefPhysAbi`) are untouched. -/

/-- The register used as the packed frame SIB base on the single-region,
    call-free framed path: `%rsp` itself (the frame base after `leaq -F(%rsp)`). -/
def frameBaseSibReg : String := "RSP"

/-- Rewrite a SIB (`arrIdx`) operand's base to `r`, keeping the index register
    and scale. Non-SIB operands pass through. -/
def pinSibOperand (r : String) : LOperand → LOperand
  | .arrIdx _ idx scale => .arrIdx r idx scale
  | o => o

/-- Rewrite every SIB base in one lowered instruction to `r` (applied to both
    destinations and sources; only the packed `STOREIDX`/`LOADIDX` carry a SIB
    operand). -/
def pinInstrSib (r : String) : LinstrR → LinstrR
  | .Lopn dsts opn srcs => .Lopn (dsts.map (pinSibOperand r)) opn (srcs.map (pinSibOperand r))
  | other => other

/-- The **frame-allocating** physical `lfundef` for a looped `ComL` — the
    self-owning analogue of `ComL.toLfundefPhys`. The array bases in `localBases`
    are laid in a `frameBytes`-byte frame the function allocates itself
    (`leaq -frameBytes(%rsp)` prologue, driven by the injected `FRAME` directive
    and recorded in `lfd_stk_max`); each is bound with `leaq off(%rsp), %reg` into
    the register the body threads as its `stackLoad`/`stackStore` SIB base, so
    every array access is a cell of the self-owned frame. There are no incoming
    SysV pointer arguments (`lfd_arg`/`lfd_tyin` empty). On a `ComL` that touches
    no array (empty `localBases`, `frameBytes = 0`) this is byte-identical to
    `ComL.toLfundefPhys` apart from the (dropped) `FRAME` directive and the
    `lfd_stk_max`/`lfd_arg` fields — purely additive.

    For a **single**-region (offset-0), **call-free** framed function the packed
    frame SIB base is `%rsp` directly (`frameBaseSibReg`): no base LEA, no
    reserved register, no eviction — after `leaq -F(%rsp), %rsp` the frame base
    is `%rsp` and every `STOREIDX`/`LOADIDX` SIB base is rewritten to `%rsp`
    (`(%rsp, %idx, 8)`). This is the fix for the deep-solve base/index collision
    (see the note above); a multi-region, offset-shifted, or call-issuing framed
    body keeps the register-allocated base (byte-identical to before). -/
def ComL.toLfundefPhysFramed {Γ : Ctxt jasminDialect} {t : JasminTy}
    (frameBytes : Nat) (localBases : List (String × Nat))
    (c : ComL Γ t) (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) (abi : IsaAbi := x86Abi) :
    Lfundef :=
  let virt := ComL.toLfundef c immSlotMap
  let hasCall := bodyHasCall virt.lfd_body
  -- Use `%rsp` directly as the SIB base on the single-region (offset-0),
  -- call-free path (no reserved register, no eviction).
  let pin := (match localBases with | [(_, 0)] => true | _ => false) && !hasCall
  let tbl := straightCallComposeTable virt.lfd_body (bodyPhysTable virt.lfd_body abi)
  let resPhys := virt.lfd_res.map (fun n => physNameForBody virt.lfd_body tbl n abi)
  -- The self-owned array bases. When pinning to `%rsp`, no base LEA is needed
  -- (the frame alloc already establishes `%rsp` as the base); otherwise each
  -- base goes to its RA-assigned register.
  let frameMat : Lcmd :=
    if pin then [] else buildFrameBaseMaterialize virt tbl localBases abi
  let pbody0 := if hasCall then physBodyCalleeSave shiftImm virt.lfd_body abi
                else physBody shiftImm virt.lfd_body abi
  -- Rewrite every packed SIB base to `%rsp`.
  let pbody : Lcmd :=
    if pin then pbody0.map (fun i => ⟨i.li_ii, pinInstrSib frameBaseSibReg i.li_i⟩) else pbody0
  let retEpi : Lcmd :=
    match resPhys with
    | [r] => if r == "RAX" then [] else [⟨0, .Lopn [.reg "RAX"] "MOVQ" [.reg r]⟩]
    | _ => []
  let bodyWithRet : Lcmd :=
    if retEpi.isEmpty then pbody else pbody.dropLast ++ retEpi ++ [⟨0, .Lret⟩]
  -- The `FRAME` marker: `frameSize` reads it to open a real `leaq -F(%rsp)` frame.
  let frameDir : Linstr := ⟨0, .Lopn [] "FRAME" [.imm frameBytes]⟩
  { virt with
    lfd_body := frameDir :: (frameMat ++ bodyWithRet)
    lfd_arg := []
    lfd_tyin := []
    lfd_res := resPhys
    lfd_stk_max := frameBytes }

/-- Export a looped `ComL` to a physical-register, two-address `Lprog` — the
    loop-aware mirror of `Com.toLprogPhys`. The single exported function has a
    rolled, physically-allocated body (real x86 registers, real `jne .L<d>`
    back-edge, one body copy). -/
def ComL.toLprogPhys {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) (abi : IsaAbi := x86Abi) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs := [(fname, ComL.toLfundefPhys c shiftImm immSlotMap abi)] }

/-- Serialize the looped physical export to the textual lprog blob (magic + text). -/
def ComL.toLprogPhysText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : String :=
  magic ++ (ComL.toLprogPhys c fname shiftImm immSlotMap).toText ++ "\n"

/-- The looped physical export's bytes. -/
def ComL.toLprogPhysBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : ByteArray :=
  (ComL.toLprogPhysText c fname shiftImm immSlotMap).toUTF8

/-- Write the looped physical-register lprog blob for a `ComL` to a file. -/
def ComL.writeLprogPhysFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String) (path : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    IO Unit :=
  IO.FS.writeBinFile path (ComL.toLprogPhysBytes c fname shiftImm immSlotMap)

/-! ### 7g′. 2-pointer-ABI physical export of a looped `ComL` (array-map kernels)

`ComL.toLfundefPhys` (§7g) gives the looped body the same SSA→physical RA as a
straight-line `Com`, but it is **register-ABI-only**: it treats the
`stackArr`-typed array arguments as if they were scalar register values, copies
each into its RA-assigned register once at entry (`buildArgMaterializePhys`), and
the loop body uses the accumulator register / the invariant-base registers
directly as `STOREIDX`/`LOADIDX` SIB bases.

For a 2-pointer array-map kernel — `mayo_encode(out, in)`,
`out[i] := f(in[i])` — that is **wrong in two ways** (gdb/objdump-confirmed):

1. **IN/OUT role binding by RA, not ABI.** The accumulator (output base) and the
   invariant (input base) are bound to whatever physical registers the linear
   scan happens to assign; nothing pins the i-th array role to the i-th SysV
   pointer register, so the rendered loads/stores can address the wrong array.

2. **Invariant-base clobber → SIGSEGV.** The array-base registers are in the
   allocatable pool, so the loop body reuses them as scratch mid-iteration
   (`movzbl …, %rsi` overwriting the in-pointer in `%rsi`). A later
   `LOADIDX`/`STOREIDX` whose SIB base resolves to such a clobbered register
   self-addresses through a *data word* — a wild store.

The straight-line memref kernels (ChaCha/SHA/Keccak) already have the robust
fix: `comToLfundefPhysAbi` saves each pointer argument to a red-zone qsave slot
in the prologue and, via `reloadMemrefBase`, **reloads the SIB base from its
qsave slot into `R14` immediately before every access** — so the base is never a
body-clobberable register and the IN/OUT roles follow the *ABI argument →
qsave-slot* mapping, not the RA. This section lifts that exact machinery onto the
looped `ComL` path.

The one looped-specific step: in an array-map loop the store base is the
**accumulator** register (`regName nArgs`, seeded `MOV acc, a_out`), not the out
argument directly. Because the dialect's `stackStore` is an *in-place* update —
the result memref is the same pointer as its input — the accumulator IS the out
pointer, so aliasing the accumulator name onto the out-argument name `a_out`
across the whole loop body is a pure α-relabeling of the pointer-base role. After
that alias (and the standard `canonicalizeMemrefThread` collapsing the
`STOREIDX`-result thread), every `STOREIDX` base is `a_out` and every `LOADIDX`
base is the corresponding `a_in`, so the shared `memrefBaseReload` reloads each
from its qsave slot before each access — identical to the proven straight-line
ChaCha path. The accumulator feedback (`MOV acc, ret`) collapses to the harmless
no-op `MOV a_out, a_out`, and the `CMP Lctr, invBase` liveness touch is now
redundant (the base lives in memory) but harmless. -/

/-- Rename a register name `from_ ↦ to_` (identity elsewhere): the primitive of
    the accumulator→out-argument alias used by the looped 2-pointer-ABI export. -/
def aliasRegName (from_ to_ : String) (n : String) : String :=
  if n == from_ then to_ else n

/-- Apply `aliasRegName from_ to_` to one `LOperand` — both a plain `reg` name and
    a SIB `arrIdx` base/index. Immediates and compile-time array elements pass
    through. -/
def aliasRegOperand (from_ to_ : String) : LOperand → LOperand
  | .reg n => .reg (aliasRegName from_ to_ n)
  | .arrIdx base idx scale =>
      .arrIdx (aliasRegName from_ to_ base) (aliasRegName from_ to_ idx) scale
  | o => o

/-- Alias the accumulator register name onto the out-argument name across a whole
    looped body: every `Lopn` destination/source `reg` and every SIB base/index
    equal to `from_` becomes `to_`. The op mnemonics, widths, immediates, and
    instruction order are preserved (only the pointer-base *label* changes), so
    the body still denotes the same value sequence — `stackStore` returns its
    input pointer, so the accumulator and the out argument are the same memref. -/
def aliasRegBody (from_ to_ : String) (body : Lcmd) : Lcmd :=
  body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        ⟨i.li_ii, .Lopn (dsts.map (aliasRegOperand from_ to_)) opn
          (srcs.map (aliasRegOperand from_ to_))⟩
    | _ => i)

/-- The base names of the **array-typed** (`.stackArr`) entries of a variable
    vector, in vector order, under the `resolveVar` convention. The array-typed
    restriction of `exprArgsHV`.

    A scalar invariant (`.reg`, `.inlineInt`, `.bool`) is never a
    `LOADIDX`/`STOREIDX` SIB base, so it takes no red-zone reload slot; dropping
    it here keeps the array bases at the positions the memref ABI assigns them.
    Entries that resolve to an immediate are dropped, as in `exprArgsHV`'s
    `.reg`-filtered use. -/
def arrArgNamesHV (curDepth nArgs : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} :
    {tys : Ctxt jasminDialect} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    List String
  | [], _ => []
  | ty :: _, .cons v rest =>
      let rest' := arrArgNamesHV curDepth nArgs immSlotMap rest
      match ty, resolveVar curDepth nArgs argName immSlotMap v with
      | .stackArr _ _, LOperand.reg n => n :: rest'
      | _, _ => rest'

/-- The out-base name and the array-typed invariant base names of one loop node's
    `init` / `invs`. The arm every array-carrying `ComL` loop constructor
    shares. -/
def loopArgBasesOf (curDepth nArgs : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} {tys : Ctxt jasminDialect}
    (init : Ctxt.Var Γ τ) (invs : HVector (fun ty => Ctxt.Var Γ ty) tys) :
    Option (String × List String) :=
  match resolveVar curDepth nArgs argName immSlotMap init with
  | LOperand.reg outNm =>
      some (outNm, arrArgNamesHV curDepth nArgs immSlotMap invs)
  | _ => none

/-- Resolve a looped `ComL`'s **canonical loop-argument base names** from the
    `forLoopN` (or `forLoop`) node's `init` and `invs`, using the *same*
    `resolveVar` convention the body lowering (`comLToBody`) uses.
    Returns `(outBase, inBases)` where `outBase` is the name the body's
    accumulator / out-array base resolves to (`resolveVar init`) and `inBases`
    are the base names of the **array-typed** invariants, in `invs` order
    (`arrArgNamesHV invs`).

    `ComL.toLfundefPhysAbi` zips `inBases` against `abiArgs.drop 1`, so a base's
    ABI register is fixed by its position among the array invariants. A scalar
    invariant holds no array base and is dropped, keeping that position count
    independent of where a kernel lists its scalars: with scalars in the list,
    every array base to their right would be paired with an ABI register one
    place too far, reloading the array through a scalar's red-zone slot.

    `resolveVar` maps a `Var` to `argName (curDepth - 1 - deBruijn)` — the slot
    counted from the program root, i.e. the **reverse** of the newest-first `Γ`.
    For a top-level `ComL` whose `Γ` is the argument list, the loop's `init` (the
    newest binder `.here`, the out/accumulator) resolves to the **highest** arg
    slot and the last `invs` entry resolves to `a0`. Deriving the names here
    makes the role→name mapping match the body regardless of how a caller ordered
    its `outArg`/`inArgs` hints.

    Returns `none` for a loop-free `ComL` (no `forLoop`/`forLoopN` node). -/
def ComL.loopArgBaseNames (nArgs : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (curDepth : Nat) : Option (String × List String) :=
  match c with
  | ComL.ret _ => none
  | ComL.var _ body => ComL.loopArgBaseNames nArgs immSlotMap body (curDepth + 1)
  | ComL.forLoop _ init _ =>
      match resolveVar curDepth nArgs argName immSlotMap init with
      | LOperand.reg n => some (n, [])
      | _ => none
  | ComL.forLoopN _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs
  | ComL.forLoopNRt _ _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs
  | ComL.forLoopNRtNested _ _ _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs
  | ComL.whileNz _ _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs
  | ComL.forLoopBlock _ _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs

/-- The virtual-register index of each loop node's accumulator, in spine order.

    A loop binds its final accumulator into scope for its continuation, and a
    `var` binds its expression, so the register index of a node's accumulator is
    the context depth at that node. Called with `depth := nArgs`, the head of the
    result is `nArgs` — the name `ComL.toLfundefPhysAbi` has always aliased — and
    the tail is the accumulators of the later loops of a continuation chain,
    which carry the same array. A single-loop program yields a one-element list,
    so nothing about its export changes. -/
def ComL.loopAccRegs {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (depth : Nat) : List Nat :=
  match c with
  | ComL.ret _ => []
  | ComL.var _ body => ComL.loopAccRegs body (depth + 1)
  | ComL.forLoop _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.forLoopN _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.forLoopNRt _ _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.forLoopNRtNested _ _ _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.whileNz _ _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.forLoopBlock _ _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)

/-- The pairs of array names with the argument register of their own slot: a name
    `argName j` with `j < abiArgs.length` is paired with `abiArgs[j]`, and a name that
    is no argument name below `abiArgs.length` has no pair. -/
def argBasePairsPos (names abiArgs : List String) : List (String × String) :=
  names.filterMap fun nm =>
    (abiArgs.zipIdx.find? fun q => argName q.2 == nm).map fun q => (nm, q.1)

/-- **The pairs of array base names with argument registers** of the looped
    physical-ABI export.

    At `posBind = false` the pairing is by role: the out base `outArg'` with the first
    register of `abiArgs` and the `i`-th in base with the register `i + 1`, whatever
    argument slots the names denote. A kernel whose C signature lists the output
    pointer first and whose context lists it elsewhere uses this pairing.

    At `posBind = true` the pairing is by slot (`argBasePairsPos`): each base
    `argName j` with the register `abiArgs[j]`, the register
    `buildArgPtrMaterialize` reads the same name from. A program whose arguments
    follow `abiArgs` slot by slot uses this pairing; under it a scalar argument and
    an array base never share a register. -/
def argBasePairs : Bool → String → List String → List String → List (String × String)
  | false, outArg', inArgs', abiArgs =>
      (outArg', abiArgs.headD "RDI") :: (inArgs'.zip (abiArgs.drop 1))
  | true, outArg', inArgs', abiArgs => argBasePairsPos (outArg' :: inArgs') abiArgs

/-- The pairing by role is `argBasePairs` at `posBind = false`. -/
theorem argBasePairs_false (outArg' : String) (inArgs' abiArgs : List String) :
    argBasePairs false outArg' inArgs' abiArgs
      = (outArg', abiArgs.headD "RDI") :: (inArgs'.zip (abiArgs.drop 1)) := rfl

/-- **The 2-pointer-ABI physical `lfundef` of a virtual looped `lfundef` with its
    allocation certificate**: the physical `lfundef` of `lfundefPhysAbiOfVirt` and the
    certificate `allocCertOf` of the allocator input body over the table that
    `physBodyWithStores` reads (`physAllocTbl` with no output store), computed from the
    scan table of the function. `lfundefPhysAbiOfVirt` is its first component. -/
def lfundefPhysAbiOfVirtCert (virt0 : Lfundef) (outArg' : String) (inArgs' : List String)
    (accRegs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (abi : IsaAbi := x86Abi)
    (posBind : Bool := false) :
    Lfundef × List (String × String) :=
  -- Argument-liveness pin (4+-argument looped signatures — the chained-phase
  -- kernels whose per-phase runtime bounds are read LATE, at each phase's loop
  -- head). Without the pin the linear-scan RA sees each scalar bound as "born
  -- late" and coalesces SEVERAL bound names onto ONE physical register, so
  -- `buildArgPtrMaterialize`'s entry copies overwrite each other and every
  -- phase but the last reads the wrong trip count (the fri_proof fold-chain
  -- segfault). The synthetic `LIVEPIN` reads every argument at entry, forcing
  -- distinct allocations live to their last (phase-head) use; it is filtered
  -- out after `physBodyWithStores`. ≤3-argument signatures (single bound, read
  -- at body start — the QRUOV/HAWK/FAEST GF-dot shape) inject nothing, so
  -- every existing kernel's bytes are unchanged.
  let livePin : Lcmd :=
    if abiArgs.length ≥ 4 then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []
  let body1 := livePin
    ++ canonicalizeMemrefThread
         (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body)
  let virt := { virt0 with lfd_body := body1 }
  -- Output-liveness allocation table (`outStoreMap = []` ⇒ `physTable (bodyTrace …)`).
  let tbl := physTableOut virt.lfd_body [] (abi := abi)
  -- Prologue: save both SysV pointer args (and the six callee-saved GP regs) to
  -- the red zone; the per-access reload sources the array bases from there.
  -- For a MULTI-INPUT signature (`[RDI, RSI, RDX, …]` — the GF-dot kernels),
  -- the canonical `buildPrologue` only saves `RDI`/`RSI`. Each EXTRA input
  -- pointer register (`RDX`, `RCX`, `R8`, `R9`) needs its OWN red-zone qsave
  -- slot so the loop body can reload that input's array base from its own slot
  -- (not the out slot). The saves are appended AFTER the fixed prologue (and
  -- after the `RSI→R14` park), so the single-input / 2-pointer prologue bytes
  -- are unchanged. The save sources the live ABI register directly (it is still
  -- live at entry; `buildArgPtrMaterialize` only clobbers it afterwards).
  -- `RDI` and `RSI`, which the fixed prologue saves, are skipped (`extraSaveRegs`).
  let extraInputSaves : Lcmd :=
    (extraSaveRegs abiArgs).filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none)
  let prologue := buildPrologue virt tbl (fun _ => none) ++ extraInputSaves
  -- Materialize each SysV pointer arg into the RA-assigned register the body uses
  -- for its argument name (the 2-pointer memref ABI; `inLoadMap = none`).
  let argMat := buildArgPtrMaterialize virt tbl abiArgs (fun _ => none) abi
  -- Compose the caller's shift oracle with the dataflow `regConst`→imm resolver.
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  -- The memref-base reload map: each array argument `aj` (out + ins) maps its
  -- RA-assigned physical register to its red-zone qsave slot, so every SIB base
  -- is reloaded from memory into `R14` immediately before the access — never a
  -- body-clobberable register.
  -- By role (`posBind = false`) the out base takes `abiArgs[0]` and the i-th ARRAY
  -- invariant `abiArgs[i+1]`: the memref ABI places the output pointer first and
  -- the input pointers next, ahead of any scalar argument. `inArgs'` holds only the
  -- array invariants (`arrArgNamesHV`), so a scalar listed among the invariants does
  -- not shift the array bases to the right of it onto the following ABI register.
  -- By slot (`posBind = true`) each base `argName j` takes `abiArgs[j]`.
  let argAbi : List (String × String) := argBasePairs posBind outArg' inArgs' abiArgs
  -- `abiSaveOfExt` (not `abiSaveOf`): each input base — including the 3rd+ ABI
  -- register (`RDX`/`RCX`/…) — maps to its OWN qsave slot. With plain `abiSaveOf`
  -- the 2nd input (`RDX`) returned `none`, dropping its pair, so its `LOADIDX`
  -- base was never reloaded and (after `buildArgPtrMaterialize`) read from the
  -- out pointer's register — the byte-KAT-confirmed garbage (qruov/sdith). Each
  -- `(argNm, abiReg)` pair keys on the per-input phys base and yields the input's
  -- distinct slot, so the i-th input reloads from the i-th input's slot.
  let reloadPairs : List (String × String) :=
    argAbi.filterMap (fun (argNm, abiReg) =>
      match abiSaveOfExt abiReg with
      | some saveName =>
          -- Key on the barrier-resolved phys base (`physNameForBody`): a
          -- call-containing body relocated the array-base register, so the
          -- reload map must match the register the body's SIB actually reads.
          some (physNameForBody virt.lfd_body tbl argNm abi, saveName)
      | none => none)
  let memrefBaseReload : String → Option String :=
    fun base => (reloadPairs.find? (fun p => p.1 == base)).map Prod.snd
  -- In-loop-`call` invariant-base restore list. The looped-call barrier's static
  -- `calleeFirstPhys` protects only the first four loop-carried slots (the four
  -- callee-saved registers); a 5th+ loop-carried invariant pointer base (a
  -- multi-pointer rolled fold with an in-loop `call` — the SHAKE256 sponge absorb
  -- input / squeeze output ptr) overflows into a caller-saved register and is
  -- clobbered by the leaf `call`. Reloading it from its qsave slot after each
  -- in-loop `Lcall` (`physBodyWithStores`'s `callArgBaseReload`) restores it.
  --
  -- Keyed *positionally* — `physNameForBody (argName j) ↦ qsave[abiArgs[j]]` —
  -- to mirror `buildArgPtrMaterialize` exactly: at entry the register holding
  -- `argName j` is loaded from `qsave[abiArgs[j]]`, so the post-call reload must
  -- restore that same slot. (The `reloadPairs`/`memrefBaseReload` SIB map keys on
  -- the loop's `init`/`invs` de-Bruijn order via `loopArgBaseNames`, which for a
  -- fold whose accumulator is not the 0-th root arg is *swapped* against the
  -- positional order — correct for a SIB base reloaded into R14, wrong as an
  -- in-register restore.) Bases in a callee-saved register are excluded, so a
  -- body whose loop-carried set fits stays byte-identical (X25519
  -- single-accumulator whole-fold, every ≤4-base kernel).
  let callArgBaseReload : List (String × String) :=
    (abiArgs.zipIdx).filterMap (fun (abiReg, j) =>
      match abiSaveOfExt abiReg with
      | some saveName =>
          let phys := physNameForBody virt.lfd_body tbl (argName j) abi
          if isCallerSavedAllocGPR phys then some (phys, saveName) else none
      | none => none)
  -- The rolled loop body with per-access SIB-base reloads. `outStoreMap = []`
  -- (the loop already carries its own inline `STOREIDX`), `inLoadMap = none`
  -- (the body self-addresses through the array pointers, not per-word loads).
  -- A `ZEROARR`/`STOREIMM` whose register base has a save slot addresses its base
  -- through `R14`, reloaded from that slot (`reloadArrImmBody`).
  let bodyWithReload := reloadArrImmBody memrefBaseReload
    ((physBodyWithStores shiftImm' virt.lfd_body
      (fun _ => none) reloadScratch2 [] reloadScratch2 0 memrefBaseReload
      callArgBaseReload (abi := abi)).filter
      (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true))
  -- Restore the callee-saved registers before the final `Lret`.
  let bodyWithRestore := insertEpilogue bodyWithReload calleeSaveRestoreEpilogue
  ({ virt with
    lfd_body := prologue ++ argMat ++ bodyWithRestore
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := [] }, allocCertOf virt.lfd_body (straightCallComposeTable virt.lfd_body tbl) abi)

/-- The 2-pointer-ABI physical `lfundef` of a virtual looped `lfundef` `virt0`: the
    part of `ComL.toLfundefPhysAbi` after the virtual export, the function of
    `lfundefPhysAbiOfVirtCert`.

    `outArg'` is the canonical out-array base name, `inArgs'` the array-typed input
    base names in ABI order, and `accRegs` the register names of the loop
    accumulators that carry the output array. Each accumulator is aliased onto
    `outArg'` and the in-place `STOREIDX`-result thread is collapsed onto its SIB
    base, so every `STOREIDX` base is `outArg'` and every `LOADIDX` base is an
    `inArgs'` name, all covered by the qsave-reload map. Every loop on the
    continuation spine carries the same output array, so every accumulator is
    aliased: a later loop of a chain left unaliased would hold the root-counted seed
    `resolveVar` gives it (the invariant pointer), and an 8-layer NTT rendered that
    way stores into its read-only zeta table.

    `ComL.toLfundefPhysAbi_eq_ofVirt` states that `ComL.toLfundefPhysAbi` is this
    function at `ComL.toLfundef`; the carried-register loop language `ComLJ` uses it
    at its own virtual export. `posBind` selects the pairing of array bases with
    argument registers (`argBasePairs`): by role at `false`, by slot at `true`. -/
def lfundefPhysAbiOfVirt (virt0 : Lfundef) (outArg' : String) (inArgs' : List String)
    (accRegs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (abi : IsaAbi := x86Abi)
    (posBind : Bool := false) :
    Lfundef :=
  (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin abi
    posBind).1

/-- The function of `lfundefPhysAbiOfVirtCert` is `lfundefPhysAbiOfVirt`. -/
theorem lfundefPhysAbiOfVirtCert_fst (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs : List String) (shiftImm : ShiftImmOracle) (abiArgs : List String)
    (abiTyin : List Nat) (abi : IsaAbi) (posBind : Bool) :
    (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin abi
        posBind).1
      = lfundefPhysAbiOfVirt virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin abi
        posBind := rfl

/-- `lfundefPhysAbiOfVirt` depends on `posBind` only through the pairs
    `argBasePairs` of its base names: two settings with the same pairs give the same
    function. -/
theorem lfundefPhysAbiOfVirt_congr_pairs (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs : List String) (shiftImm : ShiftImmOracle) (abiArgs : List String)
    (abiTyin : List Nat) (abi : IsaAbi) (b₁ b₂ : Bool)
    (h : argBasePairs b₁ outArg' inArgs' abiArgs = argBasePairs b₂ outArg' inArgs' abiArgs) :
    lfundefPhysAbiOfVirt virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin abi b₁
      = lfundefPhysAbiOfVirt virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin abi b₂ := by
  unfold lfundefPhysAbiOfVirt lfundefPhysAbiOfVirtCert
  rw [h]

/-- The 2-pointer-ABI physical `lfundef` for a **looped** `ComL` array-map kernel
    (`out[i] := f(in[i])`, the `mayo_encode` / `*_sign_rwhile` shape) — the
    loop-aware mirror of `comToLfundefPhysAbi` (§7f).

    `nArgs` is `Γ.length` (the accumulator name is `regName nArgs`). The output
    and input array base names are derived from the `ComL`'s own loop `init`/`invs`
    via `ComL.loopArgBaseNames` (the canonical `resolveVar`-convention names the
    body uses), so the role→name mapping is always correct regardless of the
    `Γ`-vs-root ordering of the caller's `outArg`/`inArgs` hints (the qruov/sdith
    2nd-input base-mis-resolution fix). The caller's `outArg`/`inArgs` are used
    only as a fallback when the program has no loop node. `abiArgs` is the SysV
    pointer-register signature (default `[RDI, RSI]` = `out, inp`).

    The fix vs `ComL.toLfundefPhys`: the accumulator is aliased onto `outArg`, the
    `STOREIDX`-result thread is canonicalized, the pointer arguments are saved to
    red-zone qsave slots in the prologue, and `physBodyWithStores` reloads each
    `LOADIDX`/`STOREIDX` SIB base from its qsave slot into `R14` immediately
    before every access (`memrefBaseReload`). So the IN/OUT array roles follow the
    *argument → qsave-slot* mapping (no swap), and neither base is ever a
    body-clobberable register (no clobber → no segfault). One body copy, real
    `jne .L<d>` back-edge, real x86 registers throughout. The part after the virtual
    export is `lfundefPhysAbiOfVirt`.

    `posBind` selects the pairing of array bases with argument registers
    (`argBasePairs`). At `false` the out base reloads from the slot of `abiArgs[0]`
    whatever argument slot it denotes; a program whose arguments follow `abiArgs`
    slot by slot, with the output array at a slot other than `0`, takes `true`. -/
def ComL.toLfundefPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (abi : IsaAbi := x86Abi)
    (posBind : Bool := false) :
    Lfundef :=
  let nArgs := Γ.length
  let virt0 := ComL.toLfundef c immSlotMap
  -- Derive the canonical out-/in-array base names from the program's own loop
  -- node (`init`/`invs`) under the body's `resolveVar` convention. This is the
  -- name each role's `LOADIDX`/`STOREIDX` SIB base ACTUALLY uses in `virt0`, so
  -- the alias and the qsave-reload map key on the right names regardless of
  -- how the caller ordered `outArg`/`inArgs` (the qruov/sdith fix — see
  -- `ComL.loopArgBaseNames`). Only the ARRAY-typed invariants appear in `inArgs'`,
  -- so the positional pairing with `abiArgs.drop 1` counts array bases and
  -- is unaffected by where the kernel lists its scalar invariants. Falls back to
  -- the caller's hints for a loop-free `ComL` (no loop node).
  let derived : String × List String :=
    match ComL.loopArgBaseNames nArgs immSlotMap c nArgs with
    | some (o, ins) => (o, ins)
    | none => (outArg, inArgs)
  -- The accumulator of every loop on the continuation spine; a single-loop program
  -- has a one-element `loopAccRegs`.
  let accRegs := (ComL.loopAccRegs c nArgs).map regName
  lfundefPhysAbiOfVirt virt0 derived.1 derived.2 accRegs shiftImm abiArgs abiTyin abi posBind

/-- `ComL.toLfundefPhysAbi` is `lfundefPhysAbiOfVirt` at the virtual export
    `ComL.toLfundef`, the derived base names and the loop accumulators. -/
theorem ComL.toLfundefPhysAbi_eq_ofVirt {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (outArg : String) (inArgs : List String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (abiArgs : List String) (abiTyin : List Nat) :
    ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs abiTyin =
      lfundefPhysAbiOfVirt (ComL.toLfundef c immSlotMap)
        (match ComL.loopArgBaseNames Γ.length immSlotMap c Γ.length with
          | some (o, ins) => (o, ins)
          | none => (outArg, inArgs)).1
        (match ComL.loopArgBaseNames Γ.length immSlotMap c Γ.length with
          | some (o, ins) => (o, ins)
          | none => (outArg, inArgs)).2
        ((ComL.loopAccRegs c Γ.length).map regName) shiftImm abiArgs abiTyin :=
  rfl

/-- **The export by slot is the export by role when the two pairings agree.** For a
    program whose loop node has the base names `(o, ins)`, with the same pairs
    `argBasePairs` at both settings, `ComL.toLfundefPhysAbi` at `posBind = true` is
    `ComL.toLfundefPhysAbi` at `posBind = false`. -/
theorem ComL.toLfundefPhysAbi_posBind_congr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (outArg : String) (inArgs : List String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (abiArgs : List String) (abiTyin : List Nat) (abi : IsaAbi)
    (o : String) (ins : List String)
    (hd : ComL.loopArgBaseNames Γ.length immSlotMap c Γ.length = some (o, ins))
    (h : argBasePairs true o ins abiArgs = argBasePairs false o ins abiArgs) :
    ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs abiTyin abi true
      = ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs abiTyin abi false := by
  unfold ComL.toLfundefPhysAbi
  simp only [hd]
  exact lfundefPhysAbiOfVirt_congr_pairs _ _ _ _ _ _ _ _ _ _ h

/-- Export a looped array-map `ComL` to a 2-pointer-ABI physical `Lprog` (the
    `mayo_encode` shape). See `ComL.toLfundefPhysAbi` for the IN/OUT-base reload
    fix (no swap, no clobber). -/
def ComL.toLprogPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (abi : IsaAbi := x86Abi)
    (posBind : Bool := false) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap
                 abiArgs abiTyin abi posBind)] }

/-- Serialize the looped 2-pointer-ABI physical export to the textual lprog blob. -/
def ComL.toLprogPhysAbiText {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : String :=
  magic ++
    (ComL.toLprogPhysAbi c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin).toText
    ++ "\n"

/-- The looped 2-pointer-ABI physical export's bytes. -/
def ComL.toLprogPhysAbiBytes {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : ByteArray :=
  (ComL.toLprogPhysAbiText c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin).toUTF8

/-- Write the looped 2-pointer-ABI physical lprog blob for a `ComL` to a file. -/
def ComL.writeLprogPhysAbiFile {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String) (path : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    IO Unit :=
  IO.FS.writeBinFile path
    (ComL.toLprogPhysAbiBytes c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin)

/-! ### 7g‴. Frame + caller-pointer ABI export with in-place array-call
(`ComL.toLfundefPhysFramedAbi`)

`ComL.toLfundefPhysFramed` (§7g″) owns ALL its arrays in a self-allocated frame
(no SysV pointer arguments), and `ComL.toLfundefPhysAbi` (§7g′) treats ALL its
arrays as caller SysV pointers reloaded from **red-zone** qsave slots. A sponge
kernel is **mixed**: its working state buffer is a self-owned frame array, while
its input/digest are caller SysV pointers — AND it calls an emitted permute leaf
in place between the absorb blocks. The red-zone qsave reload of §7g′ is unsafe
here (a `call` clobbers the red zone below `%rsp`), so the caller pointers must be
parked in **call-surviving** locations: a callee-saved register (the input, read
across both permute calls) or a frame slot (the digest, reloaded once at the
squeeze) — exactly the `p2_hash_kat_link.jazz::p2_sponge16` discipline.

This section adds the mixed export, purely additively. It lowers the (unrolled)
`ComL` to its SIB virtual body (`ComL.toLfundef`), then performs a **direct
offset-folding lowering** for the memref word-move + in-place-call fragment:

* a `regConst` index binding (`MOV r,#k`) is **deferred** — folded into the
  `scale*k` byte offset of the `LOADIDX`/`STOREIDX` that reads it (the `arrIdx`
  carries the `scale`), so no index register is materialised;
* a `LOADIDX base[idx*scale]` becomes `movq (scale*k)(<basephys>), %rax`, and a
  `STOREIDX base[idx*scale],val` becomes `movq %rax, (scale*k)(<basephys>)`, with
  the stored value threaded through `%rax` (a `regConst` value is materialised
  `movq $v,%rax`; a loaded word is already resident);
* a `CALL:<sym>` shadow whose array argument is the state buffer becomes the
  in-place SysV pointer call `leaq <state>,%rdi; leaq <state>,%rsi; call <sym>`
  (out == in — the emitted permute reads all inputs before writing any output,
  so aliasing is safe), with **no** `%rax` capture (the leaf writes through the
  out pointer).

`<basephys>` is dispatched per base: a frame-local array is `off(%rsp)`; a
register-parked caller pointer uses its holding register; a frame-slot-parked
caller pointer reloads its parked pointer into `R11` first. -/

/-- Resolve a memref base name to `(reloadPrelude, baseReg, extraByteOff)`:
    a frame-local array lives at `off(%rsp)`; a register-parked caller pointer
    uses its holding register directly; a frame-slot-parked caller pointer
    reloads the parked pointer into `R11`. -/
def framedAbiResolveBase (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (base : String) : Lcmd × String × Nat :=
  match frameOff base with
  | some fo => ([], "RSP", fo)
  | none =>
    match regOf base with
    | some r => ([], r, 0)
    | none =>
      match slotOff base with
      | some so => ([⟨0, .Lopn [.reg "R11"] "LOAD:64" [.reg (memName "RSP" so)]⟩], "R11", 0)
      | none => ([], base, 0)

/-- The in-place SysV pointer marshalling for a permute leaf call `state' =
    sym(state)`: pass the state buffer's address in BOTH `RDI` (out) and `RSI`
    (in), then `call sym`. No `RAX` capture (void return: the leaf writes through
    the out pointer). A frame-local base is `leaq off(%rsp),%reg`; a register-held
    pointer is `mov %reg,%hold`; a frame-slot pointer reloads into `%reg`. -/
def framedAbiCallMarshal (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (sym base : String) : Lcmd :=
  let mkArg (dstReg : String) : Lcmd :=
    match frameOff base with
    | some fo => [⟨0, .Lopn [.reg dstReg] "LEA:64" [.reg (memName "RSP" fo)]⟩]
    | none =>
      match regOf base with
      | some r => if r == dstReg then [] else [⟨0, .Lopn [.reg dstReg] "MOV:64" [.reg r]⟩]
      | none =>
        match slotOff base with
        | some so => [⟨0, .Lopn [.reg dstReg] "LOAD:64" [.reg (memName "RSP" so)]⟩]
        | none => []
  mkArg "RDI" ++ mkArg "RSI" ++ [⟨0, .Lcall none (sym, 0)⟩]

/-- Marshal one array base into a SysV argument register `dstReg`: a frame-local
    array is `leaq off(%rsp),%dstReg`; a register-parked caller pointer is
    `mov %hold,%dstReg`; a frame-slot-parked caller pointer reloads into
    `%dstReg`. The single-base helper for the distinct-buffer marshal below;
    identical in shape to `framedAbiCallMarshal`'s inner `mkArg`. -/
def framedAbiMarshalArg (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (base dstReg : String) : Lcmd :=
  match frameOff base with
  | some fo => [⟨0, .Lopn [.reg dstReg] "LEA:64" [.reg (memName "RSP" fo)]⟩]
  | none =>
    match regOf base with
    | some r => if r == dstReg then [] else [⟨0, .Lopn [.reg dstReg] "MOV:64" [.reg r]⟩]
    | none =>
      match slotOff base with
      | some so => [⟨0, .Lopn [.reg dstReg] "LOAD:64" [.reg (memName "RSP" so)]⟩]
      | none => []

/-- The System V AMD64 integer-argument registers, in call order. -/
def framedAbiArgRegs : List String := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]

/-- The **distinct-buffer** SysV pointer marshalling for a leaf call
    `sym(base₀, base₁, …)`: each array base is passed in its own SysV argument
    register (`base₀ → RDI`, `base₁ → RSI`, `base₂ → RDX`, …), then `call sym`. No
    `RAX` capture (void return: the leaf writes through its out pointer). This is
    the generalization of the in-place `framedAbiCallMarshal` (which passes ONE
    base to both RDI and RSI) to a leaf whose destination and source buffers are
    distinct — e.g. `sdith_shake128_into(out_state, in_msg)`. -/
def framedAbiCallMarshalN (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (sym : String) (bases : List String) : Lcmd :=
  ((bases.zip framedAbiArgRegs).flatMap (fun ⟨b, r⟩ =>
      framedAbiMarshalArg frameOff regOf slotOff b r))
    ++ [⟨0, .Lcall none (sym, 0)⟩]

/-- The in-place-thread alias map for a framed body: `dst ↦ canonical(base)` for
    every `STOREIDX dst, (base,…), val` (the memref store result aliases its input
    array) AND every `CALL:/CALLN: dst, (base₀, …)` (the leaf-call result aliases
    its destination buffer, argument `0`). Processed in program order with each
    base already resolved through earlier aliases, so a functionally-threaded
    frame array — a `ComL` that rebinds its self-owned buffer through each store
    and leaf call — resolves every threaded name straight back to its frame base.
    Extends `arrChainAlias` with the leaf-call arm; on a body that threads only
    original bases (every current framed caller) it maps unreferenced result
    labels and the rewrite is a no-op on emitted operands. -/
def framedAbiArrChainAlias (body : Lcmd) : Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String String := {}
  let resolve (m : Std.HashMap String String) (n : String) : String := m.getD n n
  for i in body do
    match i.li_i with
    | .Lopn [.reg dst] opn (.arrIdx base _ _ :: _) =>
        if isMemStore opn then m := m.insert dst (resolve m base)
    | .Lopn [.reg dst] opn (.reg base0 :: _) =>
        if opn.startsWith "CALL:" || opn.startsWith "CALLN:" then
          m := m.insert dst (resolve m base0)
    | _ => pure ()
  return m

/-- Collapse a framed body's forward-threaded frame-array chain (STOREIDX and
    leaf-call results) onto its root base name, so a `ComL` that threads its
    self-owned buffer through stores and distinct-buffer leaf calls resolves every
    reference back to its frame slot. The op mnemonics, widths, immediates, and
    order are preserved — only the threaded array labels change. When the body
    threads only original bases (`framedAbiArrChainAlias` maps no referenced
    operand), this is the identity on emitted operands. -/
def framedAbiCanonThread (body : Lcmd) : Lcmd :=
  let m := framedAbiArrChainAlias body
  if m.isEmpty then body
  else body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        ⟨i.li_ii, .Lopn (dsts.map (canonMemrefOperand m)) opn
          (srcs.map (canonMemrefOperand m))⟩
    | _ => i)

/-- The direct offset-folding physical lowering of a straight-line memref
    word-move + in-place-call virtual body (see §7g‴). `regConst` index bindings
    are deferred and folded into `scale*k` offsets; `LOADIDX`/`STOREIDX` become
    `%rax`-threaded `movq`s at `off(%base)`; `CALL:` shadows become in-place SysV
    pointer calls. Straight-line only (the sponge fragment carries no loop
    back-edge). -/
def framedAbiLowerBody (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (body : Lcmd) : Lcmd :=
  (body.foldl (fun (st : Std.HashMap String Nat × Lcmd) i =>
    let imm := st.1
    let out := st.2
    match i.li_i with
    | .Lopn [.reg d] opn [.imm k] =>
        if stripWidthTag opn == "MOV" then (imm.insert d k, out)
        else (imm, out ++ [i])
    | .Lopn [.reg _d] opn [.arrIdx base idxName scale] =>
        if stripWidthTag opn == "LOADIDX" then
          let k := imm.getD idxName 0
          let (prelude, breg, boff) := framedAbiResolveBase frameOff regOf slotOff base
          (imm, out ++ prelude ++
            [⟨0, .Lopn [.reg "RAX"] "LOAD:64" [.reg (memName breg (boff + scale * k))]⟩])
        else (imm, out ++ [i])
    | .Lopn [.reg _d] opn [.arrIdx base idxName scale, val] =>
        if stripWidthTag opn == "STOREIDX" then
          let k := imm.getD idxName 0
          let (prelude, breg, boff) := framedAbiResolveBase frameOff regOf slotOff base
          let valMat : Lcmd :=
            match val with
            | .reg vn =>
                if imm.contains vn then [⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm (imm.getD vn 0)]⟩]
                else []
            | .imm kk => [⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm kk]⟩]
            | _ => []
          (imm, out ++ valMat ++ prelude ++
            [⟨0, .Lopn [.reg (memName breg (boff + scale * k))] "STORE:64" [.reg "RAX"]⟩])
        else (imm, out ++ [i])
    | .Lopn [.reg _d] opn (.reg base :: rest) =>
        if opn.startsWith "CALL:" || opn.startsWith "CALLN:" then
          let sym := if opn.startsWith "CALLN:" then (opn.drop 6).toString
                     else (opn.drop 5).toString
          -- The array bases the leaf call passes, in argument order. A single
          -- base keeps the in-place `framedAbiCallMarshal` (RDI = RSI = base),
          -- byte-identical for every current single-arg in-place caller; two or
          -- more DISTINCT bases route to `framedAbiCallMarshalN` (base₀ → RDI,
          -- base₁ → RSI, …), the distinct-buffer generalization.
          let regBases : List String := (LOperand.reg base :: rest).filterMap (fun o =>
            match o with | .reg b => some b | _ => none)
          match regBases with
          | [_] => (imm, out ++ framedAbiCallMarshal frameOff regOf slotOff sym base)
          | _ => (imm, out ++ framedAbiCallMarshalN frameOff regOf slotOff sym regBases)
        else (imm, out ++ [i])
    | _ => (imm, out ++ [i]))
    ({}, [])).2

/-- The **mixed frame + caller-pointer ABI** physical `lfundef` for an unrolled
    memref `ComL` that calls an in-place permute leaf (the `PaddingFreeSponge`
    shape). Frame-local arrays (`frameArrs`, name → byte offset) live in a
    `frameBytes`-byte self-owned frame; register-parked caller pointers
    (`regParks`, base → (hold reg, SysV arg reg)) survive the permute calls in a
    callee-saved register; frame-slot-parked caller pointers (`slotParks`, base →
    (frame slot, SysV arg reg)) are reloaded before use. The body is
    `ComL.toLfundef`'d and lowered by `framedAbiLowerBody`; the `FRAME` directive
    + `lfd_stk_max` open the frame. No incoming value is returned (`lfd_res = []`);
    the result reaches the caller through the digest pointer.

    Union of the three existing pieces (§7g″ `FRAME`/`lfd_stk_max`, the memref
    thread + the SysV pointer ABI of §7g′) plus the in-place array-call
    marshalling `framedAbiCallMarshal`. The existing exports are untouched. -/
def ComL.toLfundefPhysFramedAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (frameBytes : Nat)
    (frameArrs : List (String × Nat))
    (regParks : List (String × String × String))
    (slotParks : List (String × Nat × String))
    (c : ComL Γ t)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (immSlotMap : ImmSlotMap := fun _ => none) :
    Lfundef :=
  let virt := ComL.toLfundef c immSlotMap
  let frameOff : String → Option Nat := fun b => (frameArrs.find? (·.1 == b)).map (·.2)
  let regOf : String → Option String := fun b => (regParks.find? (·.1 == b)).map (·.2.1)
  let slotOff : String → Option Nat := fun b => (slotParks.find? (·.1 == b)).map (·.2.1)
  -- Park caller pointers in call-surviving locations: register parks into a
  -- callee-saved hold register (`MOV hold, abiReg` — the renderer brackets the
  -- written callee-saved reg with `push`/`pop`); slot parks into a frame slot.
  let parkReg : Lcmd :=
    regParks.map (fun ⟨_, hold, abiReg⟩ => ⟨0, .Lopn [.reg hold] "MOV:64" [.reg abiReg]⟩)
  let parkSlot : Lcmd :=
    slotParks.map (fun ⟨_, slot, abiReg⟩ =>
      ⟨0, .Lopn [.reg (memName "RSP" slot)] "STORE:64" [.reg abiReg]⟩)
  let frameDir : Linstr := ⟨0, .Lopn [] "FRAME" [.imm frameBytes]⟩
  -- Collapse any forward-threaded frame-array chain (STOREIDX / leaf-call
  -- results) back onto its base name, so a `ComL` that functionally rebinds its
  -- self-owned buffer through each store and distinct-buffer leaf call resolves
  -- every base to its frame slot. Identity on emitted operands for a body that
  -- threads only original bases (every current single-buffer in-place caller).
  let lowered := framedAbiLowerBody frameOff regOf slotOff
    (framedAbiCanonThread virt.lfd_body)
  { virt with
    lfd_body := frameDir :: (parkReg ++ parkSlot ++ lowered)
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := []
    lfd_stk_max := frameBytes }

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
