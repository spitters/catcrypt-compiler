/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll

/-!
# Memory (`memref`) dialect over the owned x86 machine (#566)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

The memory tier of the Com/VIR substrate, companion to the `scf` dialect
(`ScfDialect.lean`): first-class `memref.load` / `memref.store` ops over the
owned x86 machine state's word-addressed memory `JState.mem`. Together,
`scf` (structured control) + `memref` (memory) round out the MLIR-style
structured substrate over the same machine state `JState w`.

## Region-free, machine-state encoding

Like `scf`, these ops are single-output, region-free dialect ops over the
machine-state type `mach w` (`⟦·⟧ = JState w`). The address `(base register,
byte offset)` is a compile-time op parameter — exactly the reg-ptr ABI the owned
kernels use (`JInstr.loadMem` / `storeMem`, the word-granular `mem_read`/
`mem_write` of `arch_sem.v`). No new memory semantics are introduced; the ops'
denotations are the existing `JState.load` / `JState.store` effects, and the
`memref → cf` lowering emits the matching single `JInstr` whose `runBlock`
denotation coincides.

## Ops (`MemrefOp`)

* `mLoad dst base off w`   — `dst := mem[base + off]`. Denotation
                             `s.setReg dst (x86_MOV (s.load base off))`.
* `mStore base off src w`  — `mem[base + off] := src`. Denotation
                             `s.store base off (x86_MOV (src.eval s))`.

## What is proved

* `mLoad_denote` / `mStore_denote` — the op denotations are exactly the
  machine-memory effects above (definitional).
* `mLoad_lowering_denote` / `mStore_lowering_denote` — **the `memref → cf`
  denotation-preservation**: each memref op denotes the same machine-state
  transformer as its lowered single-`JInstr` `cf` image (`lowerBlock` of the
  matching `loadMem` / `storeMem`), via `lowerBlock_denote`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MemrefDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-! ## 1. Types -/

/-- The `memref` dialect's value-type alphabet: the owned x86 machine state. -/
inductive MemrefTy where
  /-- The owned x86 machine state, `⟦·⟧ = JState w`. -/
  | mach (w : Nat)
  deriving DecidableEq

/-- Total denotation of `MemrefTy`. -/
@[reducible] instance : TyDenote MemrefTy where
  denote
    | .mach w => JState w

/-! ## 2. Op tags -/

/-- Memory operations over the machine state. Addresses are compile-time op
    parameters (reg-ptr ABI). -/
inductive MemrefOp where
  /-- Load `mem[base + off]` into register `dst`. -/
  | mLoad (dst base : String) (off : Int) (w : Nat)
  /-- Store `src` into `mem[base + off]`. -/
  | mStore (base : String) (off : Int) (src : JOperand) (w : Nat)

/-- The `memref` dialect. -/
@[reducible] def memrefDialect : Dialect :=
  { Op := MemrefOp, Ty := MemrefTy }

/-! ## 3. Op signatures -/

instance : DialectSignature memrefDialect where
  sig op := match op with
    | .mLoad _ _ _ w => [.mach w]
    | .mStore _ _ _ w => [.mach w]
  ret op := match op with
    | .mLoad _ _ _ w => .mach w
    | .mStore _ _ _ w => .mach w

/-! ## 4. Op denotation -/

instance memrefDenote : DialectDenote memrefDialect where
  denote op := match op with
    | .mLoad dst base off _ => fun args =>
        let s : JState _ := args.head
        s.setReg dst (x86_MOV (s.load base off))
    | .mStore base off src _ => fun args =>
        let s : JState _ := args.head
        s.store base off (x86_MOV (src.eval s))

/-! ## 5. Single-op `Com` programs and their denotations -/

/-- The one-op `memref.load` program over `[mach w]`. -/
def mLoadProg (dst base : String) (off : Int) (w : Nat) :
    Com memrefDialect [.mach w] (.mach w) :=
  .var (.mk (.mLoad dst base off w) rfl (.cons .here .nil)) (.ret .here)

/-- The one-op `memref.store` program over `[mach w]`. -/
def mStoreProg (base : String) (off : Int) (src : JOperand) (w : Nat) :
    Com memrefDialect [.mach w] (.mach w) :=
  .var (.mk (.mStore base off src w) rfl (.cons .here .nil)) (.ret .here)

/-- **`memref.load` denotation.** -/
@[simp] theorem mLoad_denote (dst base : String) (off : Int) (w : Nat) (s : JState w) :
    (mLoadProg dst base off w).denote (.cons s .nil)
      = s.setReg dst (x86_MOV (s.load base off)) := rfl

/-- **`memref.store` denotation.** -/
@[simp] theorem mStore_denote (base : String) (off : Int) (src : JOperand)
    (w : Nat) (s : JState w) :
    (mStoreProg base off src w).denote (.cons s .nil)
      = s.store base off (x86_MOV (src.eval s)) := rfl

/-! ## 6. The `memref → cf` lowering and its denotation-preservation -/

/-- Lower a `memref.load` to its `cf`-level image: the single straight-line
    `JInstr.loadMem`, lowered to `Com (x86Dialect w)`. -/
def lowerMLoad (dst base : String) (off : Int) (w : Nat) :
    Com (x86Dialect w) [X86Ty.machine w] (X86Ty.machine w) :=
  lowerBlock (Γ := []) [JInstr.loadMem dst base off]

/-- Lower a `memref.store` to its `cf`-level image: the single straight-line
    `JInstr.storeMem`, lowered to `Com (x86Dialect w)`. -/
def lowerMStore (base : String) (off : Int) (src : JOperand) (w : Nat) :
    Com (x86Dialect w) [X86Ty.machine w] (X86Ty.machine w) :=
  lowerBlock (Γ := []) [JInstr.storeMem base off src]

/-- **`memref.load → cf` denotation-preservation.** The `memref.load` op denotes
    the same machine-state transformer as its lowered single-`JInstr` `cf` image. -/
theorem mLoad_lowering_denote (dst base : String) (off : Int) (w : Nat) (s : JState w) :
    (mLoadProg dst base off w).denote (.cons s .nil)
      = (lowerMLoad dst base off w).denote (.cons s .nil) := by
  rw [mLoad_denote, lowerMLoad, lowerBlock_denote]
  simp [runBlock_cons, runBlock_nil, evalInstr]

/-- **`memref.store → cf` denotation-preservation.** The `memref.store` op denotes
    the same machine-state transformer as its lowered single-`JInstr` `cf` image. -/
theorem mStore_lowering_denote (base : String) (off : Int) (src : JOperand)
    (w : Nat) (s : JState w) :
    (mStoreProg base off src w).denote (.cons s .nil)
      = (lowerMStore base off src w).denote (.cons s .nil) := by
  rw [mStore_denote, lowerMStore, lowerBlock_denote]
  simp [runBlock_cons, runBlock_nil, evalInstr]

end CatCrypt.Crypto.SecureCompilation.X86Backend.MemrefDialect
