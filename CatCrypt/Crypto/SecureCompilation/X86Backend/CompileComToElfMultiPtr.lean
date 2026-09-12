/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull
public meta import CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit
public import CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit

/-!
# The N-pointer `Com → ELF` owned-emit entry

`CompileComToElfJInstrFull.physBodyOf` calls `Com.toLprogPhysAbi com fname` at its
defaults, so the physical body it extracts is always the 2-pointer one
(`abiArgs = ["RDI", "RSI"]`, `abiTyin = [64, 64]`, `residence = none`, `abiW = 0`,
`forceLivePin = false`). Every ELF entry built over it —
`CompileComToElfJInstrFull.compileComToElfJInstrFull`,
`CompileComToElfJInstrFull6.compileComToElfJInstrFull6`,
`OptimizedComToElfFull.optimizedCompileComToElf` — inherits that ABI and exposes no
parameter for another one, and `OptimizedComToElfFull.optimizedCompileComToElf`'s
reference fallback `CompileComToElf.compileComToElf com fname` is likewise taken at
the 2-pointer defaults.

`abiArgs` is what `comToLfundefPhysAbi` reads to build the extra-argument red-zone
qsave stores (`abiArgs.drop 2`), the pointer materialize `buildArgPtrMaterialize`,
the SIB-base reload map `memrefBaseReload` (`abiArgs.zipIdx`), the entry liveness
pin (`nArgs ≥ 3`), and `lfd_arg`/`lfd_tyin`. A three-pointer kernel — the m31
binary field ops, MAYO `mayo_quadform_n8_rc`, the secp256k1 point ops — therefore
loses its third pointer entirely when routed through those entries: no qsave slot,
no materialize, no reload entry.

`gatherJBlock6` is not what blocks the N-pointer body. It returns `some` on the
three-pointer m31 bodies (§4), so the fast path of
`OptimizedComToElfFull.optimizedCompileComToElf` fires on a body compiled at the
wrong ABI and the entry returns bytes with no diagnostic. The gap is the missing
ABI parameter, not the gather fragment.

## Main results

* `physBodyOfAbi` — the physical body at a caller-chosen pointer ABI; the
  N-pointer analogue of `CompileComToElfJInstrFull.physBodyOf`, which it
  reproduces definitionally at the 2-pointer defaults (`physBodyOfAbi_two`).
* `gathersAbi` — whether the N-pointer body is inside the `gatherJBlock6`
  fragment.
* `optElfAbi?` — the optimized N-pointer ELF entry, `Option`-valued: `none`
  outside the gather fragment rather than a fallback. Its `.isSome` is
  `gathersAbi` (`optElfAbi?_isSome`).
* `optElfAbi` — the total N-pointer entry, whose fallback passes the caller's
  `abiArgs`/`abiTyin`/`residence`/`abiW` on to `CompileComToElf.compileComToElf`.
* `gatheredAbi` — the `JInstr` block the N-pointer body gathers to.
* `optElfAbi_sound` / `optElfAbi_sound_fp` / `optElfAbi_allDirect` — the
  `runBlock` soundness of the optimization step on the N-pointer body, its
  footprint-relative form, and constant-time preservation. Instances of
  `X86OptPipelineComposed.composeValidated_sound` / `_sound_fp` /
  `_allDirect`, in the shape of
  `OptimizedComToElfFull.optimizedCompileComToElf_sound`.
* §4 — `#guard`s pinning `gathersAbi` for the three-pointer (`out`, `a`, `b` →
  RDI/RSI/RDX) and two-pointer (`out`, `x` → RDI/RSI) Mersenne-31 kernels.

`CompileComToElf.compileComToElf` carries no `forceLivePin` parameter, so
`optElfAbi`'s fallback emits the un-pinned body for a kernel that asked for the
pin. `optElfAbi?` has no fallback and is unaffected.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfMultiPtr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JState runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
  (composeValidated composeValidated_sound composeValidated_allDirect composeValidated_sound_fp
    composedDead agreeExcept)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf (optPipeline)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull (optJElf6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull (physBodyOf)

/-! ## 1. The physical body at a caller-chosen pointer ABI -/

/-- The single exported function's physical-ABI body of a `Com`, at the pointer
    ABI the caller names: `abiArgs` are the SysV argument registers bound to the
    `Com`'s context slots (slot `j` from `abiArgs[j]`), `abiTyin` their widths,
    and `residence` / `abiW` / `forceLivePin` the remaining
    `Com.toLprogPhysAbi` knobs. -/
def physBodyOfAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat) := none) (abiW : Nat := 0)
    (forceLivePin : Bool := false) : List Linstr :=
  ((Com.toLprogPhysAbi com fname (fun _ => none) (fun _ => none) (fun _ => none) []
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs.head?.map
    (fun p => p.2.lfd_body)).getD []

/-- At the 2-pointer defaults `physBodyOfAbi` is
    `CompileComToElfJInstrFull.physBodyOf`. Definitional. -/
theorem physBodyOfAbi_two {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    physBodyOfAbi com fname ["RDI", "RSI"] [64, 64] none 0 false = physBodyOf com fname := rfl

/-- Whether the N-pointer physical body is inside the `gatherJBlock6` fragment,
    i.e. whether the optimized byte path covers this kernel at this ABI. -/
def gathersAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat) := none) (abiW : Nat := 0)
    (forceLivePin : Bool := false) : Bool :=
  (gatherJBlock6 (physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin)).isSome

/-! ## 2. The N-pointer ELF entries -/

/-- **The optimized N-pointer `Com → ELF` entry.** Lower the `Com` at the caller's
    pointer ABI, gather with `gatherJBlock6`, run the validated optimization
    pipeline, encode and frame through `OptimizedComToElfFull.optJElf6`. `none`
    when the body is outside the gather fragment, so an uncovered kernel is a
    visible `none` rather than bytes from another path. -/
def optElfAbi? {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat) := none) (abiW : Nat := 0)
    (forceLivePin : Bool := false) : Option ByteArray :=
  let body := physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin
  (gatherJBlock6 body).map (fun _ => optJElf6 body fname)

/-- **The total N-pointer `Com → ELF` entry.** `optElfAbi?` where that is `some`;
    otherwise the reference `CompileComToElf.compileComToElf` with the caller's
    `abiArgs` / `abiTyin` / `residence` / `abiW` passed on, so the pointer ABI
    survives the fallback. `compileComToElf` takes no `forceLivePin`, so a pinned
    kernel outside the gather fragment falls back to the un-pinned body. -/
def optElfAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat) := none) (abiW : Nat := 0)
    (forceLivePin : Bool := false) : ByteArray :=
  let body := physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin
  if (gatherJBlock6 body).isSome then optJElf6 body fname
  else CompileComToElf.compileComToElf com fname (fun _ => none) (fun _ => none)
    (fun _ => none) [] abiArgs abiTyin residence abiW

/-- `optElfAbi?` is `some` exactly on the bodies `gathersAbi` accepts. -/
theorem optElfAbi?_isSome {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool) :
    (optElfAbi? com fname abiArgs abiTyin residence abiW forceLivePin).isSome
      = gathersAbi com fname abiArgs abiTyin residence abiW forceLivePin := by
  cases h : gatherJBlock6 (physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin) <;>
    simp [optElfAbi?, gathersAbi, h]

/-- On a covered kernel the total entry returns the optimized bytes of the
    N-pointer body — the fallback is not taken. -/
theorem optElfAbi_eq_of_gathers {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool)
    (h : gathersAbi com fname abiArgs abiTyin residence abiW forceLivePin = true) :
    optElfAbi com fname abiArgs abiTyin residence abiW forceLivePin
      = optJElf6 (physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin) fname := by
  unfold optElfAbi
  simp only [gathersAbi] at h
  simp [h]

/-- On a covered kernel the two entries agree. -/
theorem optElfAbi?_eq_some_of_gathers {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool)
    (h : gathersAbi com fname abiArgs abiTyin residence abiW forceLivePin = true) :
    optElfAbi? com fname abiArgs abiTyin residence abiW forceLivePin
      = some (optElfAbi com fname abiArgs abiTyin residence abiW forceLivePin) := by
  rw [optElfAbi_eq_of_gathers com fname abiArgs abiTyin residence abiW forceLivePin h]
  cases hg : gatherJBlock6 (physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin)
  · simp [gathersAbi, hg] at h
  · simp [optElfAbi?, hg]

/-! ## 3. Soundness of the optimization step on the N-pointer body

The gather, the framing wrap and the ELF stitch are shared with the 2-pointer
entries; the only step that can move the bytes is `composeValidated optPipeline`.
Its `runBlock` effect is nil on every block and every state, so it is nil on the
block an N-pointer body gathers to. -/

/-- The block an N-pointer physical body gathers to, `[]` outside the fragment.
    The block `optElfAbi`'s body slot optimizes and encodes. -/
def gatheredAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat) := none) (abiW : Nat := 0)
    (forceLivePin : Bool := false) : List (JInstr 64) :=
  (gatherJBlock6 (physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin)).getD []

/-- **Soundness.** When the N-pointer physical body gathers to `g`, the body-slot
    bytes `optElfAbi` emits are the encoding of `composeValidated optPipeline g`,
    and that optimized block is `runBlock`-equal to the unoptimized gathered block
    `g` on every machine state. The second conjunct is an instance of
    `composeValidated_sound`, in the shape of
    `OptimizedComToElfFull.optimizedCompileComToElf_sound`. -/
theorem optElfAbi_sound {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool)
    (g : List (JInstr 64))
    (hg : gatherJBlock6 (physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin)
            = some g) :
    OptimizedComToElfFull.optJBodyBytes6
        (physBodyOfAbi com fname abiArgs abiTyin residence abiW forceLivePin)
        = GatherImmForms.encodeJBlock6 PhysBodyGather.physAlloc (composeValidated optPipeline g)
      ∧ ∀ s : JState 64, runBlock s (composeValidated optPipeline g) = runBlock s g :=
  ⟨by simp [OptimizedComToElfFull.optJBodyBytes6, hg],
   fun s => composeValidated_sound optPipeline g rfl s⟩

/-- **Footprint-relative soundness.** The optimized block of an N-pointer body
    agrees with the gathered block modulo the pipeline's accumulated dead set
    `composedDead optPipeline` on every state. For this pipeline that dead set is
    `[]`, so this specializes to `optElfAbi_sound`. An instance of
    `composeValidated_sound_fp`. -/
theorem optElfAbi_sound_fp {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool) :
    ∀ s : JState 64,
      agreeExcept
        (composedDead optPipeline (gatheredAbi com fname abiArgs abiTyin residence abiW
          forceLivePin))
        (runBlock s (composeValidated optPipeline
          (gatheredAbi com fname abiArgs abiTyin residence abiW forceLivePin)))
        (runBlock s (gatheredAbi com fname abiArgs abiTyin residence abiW forceLivePin)) :=
  fun s => composeValidated_sound_fp optPipeline _ s

/-- **Constant-time preservation.** When the block an N-pointer body gathers to is
    in the direct-addressing constant-time class, the optimized block is too. An
    instance of `composeValidated_allDirect`. -/
theorem optElfAbi_allDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool)
    (hd : allDirect (gatheredAbi com fname abiArgs abiTyin residence abiW forceLivePin) = true) :
    allDirect (composeValidated optPipeline
        (gatheredAbi com fname abiArgs abiTyin residence abiW forceLivePin)) = true :=
  composeValidated_allDirect optPipeline _ hd

/-! ## 4. Multi-pointer coverage on the Mersenne-31 kernels

`m31_mul_owned` and `m31_add_owned` take three pointers (`out` → RDI, `a` → RSI,
`b` → RDX) and `m31_reduce_owned` two (`out` → RDI, `x` → RSI), at the same
`forceLivePin := true` the kernels' `.s` export uses. The `#guard`s pin
`gathersAbi` for each, so a lowering change that pushes one of these bodies out of
the `gatherJBlock6` fragment — where the optimized entry would silently stop
firing — breaks the build. -/

open CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit (toJasmin mulFrontCom addFrontCom
  reduceFrontCom)

/-- `gathersAbi` at the pointer ABI `abiArgs` for a lowered front kernel, `false`
    if the front or the jasmin lowering declined. -/
def kernelGathers (abiArgs : List String) (fname : String)
    (j : Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t)) : Bool :=
  (j.map (fun s =>
    gathersAbi s.2.2 fname abiArgs (abiArgs.map (fun _ => 64)) none 0 true)).getD false

#guard kernelGathers ["RDI", "RSI", "RDX"] "m31_mul_owned" (toJasmin mulFrontCom)
#guard kernelGathers ["RDI", "RSI", "RDX"] "m31_add_owned" (toJasmin addFrontCom)
#guard kernelGathers ["RDI", "RSI"] "m31_reduce_owned" (toJasmin reduceFrontCom)

end CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfMultiPtr
