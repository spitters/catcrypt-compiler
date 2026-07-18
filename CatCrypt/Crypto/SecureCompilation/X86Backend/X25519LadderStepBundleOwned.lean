/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven

/-!
# Owned X25519 Montgomery-ladder step at the `(out, acc)` bundle ABI

The whitelisted artifact `bench/x25519_compare/x25519_ladder_step_rustcmd_link.s`
exports

    x25519_ladder_step_rustcmd(uint64_t *out, const uint64_t *acc)

over the 24-word ladder bundle `[x2 | z2 | x3 | z3 | scalar | base]` (each field
element four little-endian `u64` limbs, radix-`2^64`). In that artifact the
actual field arithmetic is delegated to an `inline fn x25519_ladder_iter`
*pass-through shim* (`include/x25519_leaves.jinc`) that copies the bundle through
unchanged; the genuine Montgomery step is supplied at link time by the
formosa-25519 `ref4` `.o`. So the whitelisted `.s` does **no** crypto — it is a
`movq`-only copy-in / copy-out spine around a rust-linked leaf.

This module emits an **owned** (no jasminc, no rust leaf) function with the
**same symbol and ABI** whose body is the genuine RFC 7748 §5 differential
double-and-add field step, computed entirely in-Lean over the proven Curve25519
field leaves (`Fe25519{Ops,LazyOps,Mul}Kernel`). It reuses the already-proven
fused monolithic step `X25519MonoLadderKernel.monoLadderStepBlock` (denotation =
`runBlock`, no `sorry`) operating on a single stack frame `fp`, wrapped with:

* **copy-in** — read the four working coordinates `x2,z2,x3,z3` from `acc` and
  the differential base `x1` from the bundle's `base` slot (`acc + 160`) into the
  `fp` frame slots the fused body addresses;
* the **fused field step** (`monoLadderStepBlock`): `A=x2+z2`, `AA=A²`,
  `B=x2−z2`, `BB=B²`, `E=AA−BB`, `C=x3+z3`, `D=x3−z3`, `DA=D·A`, `CB=C·B`,
  `x3=(DA+CB)²`, `z3=x1·(DA−CB)²`, `x2=AA·BB`, `z2=E·(121666·E+BB)` — every op
  one of the proven field leaves, op-to-op through the frame, zero inter-op calls;
* **copy-out** — write the new `x2,z2,x3,z3` from the frame to `out`, and pass
  the `scalar` / `base` slots through `acc → out` unchanged (so the 24-word
  bundle shape is preserved for the next ladder step).

The `cswap` of `(x2,x3),(z2,z3)` by the current scalar bit is the constant-time
word swap the caller performs on the bundle between steps (exactly as the
per-leaf / mono ladders in `bench/x25519_ladder_compare/`); it touches only
bundle memory, so it composes with this body unchanged.

## What is proved / checked here

* `bundleStepBlock_lowering_correct` — the whole copy-in ++ fused-step ++
  copy-out body lowers denotation-preservingly through the owned x86 backend
  (`lowerBlock_denote_closed`): on any incoming state the lowered
  `Com (x86Dialect 64)` denotes exactly `runBlock`. No `sorry`.
* The emitted `.s` is one function `x25519_ladder_step_rustcmd`, MULX-bearing,
  carrying the `$121666` `a24` immediate, with `out`/`acc` pinned to the
  System-V argument registers `%rdi`/`%rsi` and the frame pointer in a
  callee-saved register.
* An **independent** `GF(2^255−19)` reference (`ladderRef`, plain `Nat`-mod-`p`
  differential add-and-double) is provided in §6 for the runtime KAT to compare
  against; `feOf` reads a 4-limb output back as a `Nat`.

## Honest scope — value identity is C/GMP-KAT-gated (REV-12), not in-Lean

The full field-arithmetic *value* identity (the `runBlock` of the 1058-`JInstr`
field step = `ladderRef` mod `p`) is **not** discharged in Lean: it is the
256×256→512 bignum identity that `Fe25519{Mul,Ops}Kernel` / `BignumMontMulKernel`
already establish is `#eval`/`native_decide`-infeasible (interpreter-deep
string-keyed memory + SAT-scale carry chains — the documented REV-12 boundary;
`Fe25519MulKernel`/`BignumMontMulKernel` gate the same identity at runtime, NOT
in-Lean). What is owned and proven **in Lean** here is the **composition + ABI
shape**: the copy-in/step/copy-out body is genuine emitted `JInstr`, lowers
denotation-preservingly through the verified backend (`*_lowering_correct`),
allocates without GP overflow, and renders to one `(out, acc)`-ABI function.

The value identity is gated by the **runtime C/GMP KAT** — exactly the gate the
existing `monoLadderStepBlock` field arithmetic already passes against RFC 7748
§5.2 + s2n (`bench/x25519_ladder_compare/x25519_ladder_mono.c`). Since this body
reuses `monoLadderStepBlock` verbatim, the new C harness
`bench/x25519_compare/x25519_ladder_step_owned_kat.c` exercises the `(out, acc)`
wrapper: it (a) cross-checks one bundle step against the independent `ladderRef`,
and (b) drives the full 255-step ladder through `x25519_ladder_step_rustcmd`
and validates byte-for-byte against RFC 7748 §5.2 and s2n `curve25519_x25519`.
The whitelisted artifact's spine, by contrast, computes nothing (shim leaf).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X25519LadderStepBundleOwned

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven (valLimbs)

/-! ## 1. Bundle byte-offsets in `acc` / `out`

The 24-word bundle is `[x2 | z2 | x3 | z3 | scalar | base]`, each element four
`u64` limbs (32 bytes). The frame slots `slotX2..slotX1` (from
`X25519MonoLadderKernel`) are `0,32,64,96,128`; the differential base `x1` lives
at the **bundle** `base` slot, byte 160. -/

def accX2 : Int := 0
def accZ2 : Int := 32
def accX3 : Int := 64
def accZ3 : Int := 96
def accScalar : Int := 128
def accBase : Int := 160

/-- Copy a 4-limb (32-byte) field element from base `src`@`srcOff` to base
    `dst`@`dstOff`, through register `r`. -/
def copyFe (src : String) (srcOff : Int) (dst : String) (dstOff : Int)
    (r : String) : List (JInstr 64) :=
  [ .loadMem r src srcOff,        .storeMem dst dstOff (.reg r)
  , .loadMem r src (srcOff + 8),  .storeMem dst (dstOff + 8) (.reg r)
  , .loadMem r src (srcOff + 16), .storeMem dst (dstOff + 16) (.reg r)
  , .loadMem r src (srcOff + 24), .storeMem dst (dstOff + 24) (.reg r) ]

/-! ## 2. Copy-in: bundle `acc` → frame `fp`

Read the four working coordinates and the differential base into the frame slots
the fused body (`monoLadderStepBlock`) reads (`slotX2,slotZ2,slotX3,slotZ3` and
`slotX1` for `x1`). -/

def copyInBlock : List (JInstr 64) :=
  copyFe "acc" accX2   "fp" slotX2 "cpr"
  ++ copyFe "acc" accZ2   "fp" slotZ2 "cpr"
  ++ copyFe "acc" accX3   "fp" slotX3 "cpr"
  ++ copyFe "acc" accZ3   "fp" slotZ3 "cpr"
  ++ copyFe "acc" accBase "fp" slotX1 "cpr"   -- x1 (differential) ← bundle base

/-! ## 3. Copy-out: frame `fp` → bundle `out`, plus scalar/base pass-through

Write the new coordinates and carry the `scalar`/`base` slots forward unchanged
so the 24-word bundle stays well-formed for the next step. -/

def copyOutBlock : List (JInstr 64) :=
  copyFe "fp" slotX2 "out" accX2 "cpr"
  ++ copyFe "fp" slotZ2 "out" accZ2 "cpr"
  ++ copyFe "fp" slotX3 "out" accX3 "cpr"
  ++ copyFe "fp" slotZ3 "out" accZ3 "cpr"
  ++ copyFe "acc" accScalar "out" accScalar "cpr"   -- scalar pass-through
  ++ copyFe "acc" accBase   "out" accBase   "cpr"   -- base pass-through

/-! ## 4. The whole owned bundle-step body -/

/-- The full owned ladder-step body at the `(out, acc)` bundle ABI: copy-in ++
    fused field step ++ copy-out. Genuine emitted `JInstr`; zero rust-linked
    leaves. -/
def bundleStepBlock : List (JInstr 64) :=
  copyInBlock ++ monoLadderStepBlock ++ copyOutBlock

/-- Copy-in is 5 field-element copies (5×8 = 40 `JInstr`); copy-out is 6 (x2,z2,
    x3,z3 + scalar/base pass-through, 6×8 = 48); the fused field step is 1058.
    Total 1146. -/
theorem bundleStepBlock_length : bundleStepBlock.length = 1146 := by
  native_decide

/-! ## 5. Lowering correctness over the whole body

`lowerBlock_denote_closed` is parametric in the block, so it applies to the full
copy-in/step/copy-out composition directly. -/

/-- **Lowering correctness on the owned bundle-step body.** The whole body lowers
    denotation-preservingly through the owned x86 backend, on any incoming state.
    No `sorry`. -/
theorem bundleStepBlock_lowering_correct (s : JState 64) :
    (lowerBlock (Γ := []) bundleStepBlock).denote (.cons s .nil)
      = runBlock s bundleStepBlock :=
  lowerBlock_denote_closed bundleStepBlock s

/-! ## 6. Independent `GF(2^255−19)` reference (plain `Nat` mod p)

A from-scratch differential add-and-double over `Nat` — no machine model, no
field leaves, just `Nat` arithmetic mod `p`. This is the **independent
reference** the runtime C/GMP KAT (`x25519_ladder_step_owned_kat.c`'s `ref_step`)
mirrors limb-for-limb; the KAT compares it against the owned `.s` output (the
REV-12-mandated runtime gate, since the in-Lean `runBlock` value identity is
infeasible to discharge). Kept here so the Lean source and the C oracle share one
written spec. -/

/-- `p = 2^255 − 19`. -/
def p25519 : Nat := 2 ^ 255 - 19

/-- One RFC 7748 §5 differential double-and-add step on `(x2,z2,x3,z3)` with
    differential base `x1`. Returns the new `(x2,z2,x3,z3)`. -/
def ladderRef (x1 x2 z2 x3 z3 : Nat) : Nat × Nat × Nat × Nat :=
  let a  := (x2 + z2) % p25519
  let aa := (a * a) % p25519
  let b  := (x2 + p25519 - z2 % p25519) % p25519
  let bb := (b * b) % p25519
  let e  := (aa + p25519 - bb % p25519) % p25519
  let c  := (x3 + z3) % p25519
  let d  := (x3 + p25519 - z3 % p25519) % p25519
  let da := (d * a) % p25519
  let cb := (c * b) % p25519
  let x3' := (((da + cb) % p25519) ^ 2) % p25519
  let t   := (da + p25519 - cb % p25519) % p25519
  let z3' := (x1 * ((t * t) % p25519)) % p25519
  let x2' := (aa * bb) % p25519
  let z2' := (e * (((121666 * e) % p25519 + bb) % p25519)) % p25519
  (x2', z2', x3', z3')

/-- Read four little-endian `u64` limbs from base `b`@byte `off` of state `s` as
    a `Nat`. -/
def feOf (s : JState 64) (b : String) (off : Int) : Nat :=
  valLimbs [s.load b off, s.load b (off + 8), s.load b (off + 16), s.load b (off + 24)]

/-! ## 7. Emission — one assembly function `x25519_ladder_step_rustcmd`

The `out`/`acc` System-V pointer arguments must survive the whole field step (the
copy-out at the end reads `acc`'s scalar/base slots and writes through `out`), but
the field multiply/square already needs **13** scratch names against the 14-slot
GP pool with only the frame base `fp` pinned (the mono kernel's exact budget).
There is therefore no room to *also* hold `out`/`acc` in pinned pool registers
across the field step. So we **spill the two pointers to the frame** in the
prologue and reload them just before copy-out: this keeps the field step's pool
identical to the mono kernel's (only `fp` pinned ⇒ 13 free), so the mono kernel's
verified no-overflow per-op allocation carries over unchanged.

Frame layout (`%rbx` base): bytes `0..479` the 15 field slots (`X25519Mono`'s
`frameBytes`), bytes `480`/`488` the spilled `acc`/`out` pointers. -/

/-- Spill-slot byte offsets for the two ABI pointers, just past the field slots. -/
def accSpill : Int := 480
def outSpill : Int := 488

/-- Frame + ABI pins for the copy spines: `out`→`%rdi`, `acc`→`%rsi`, `fp`→`%rbx`.
    The copy-in spine runs before any field op clobbers `%rdi`/`%rsi`, and the
    copy-out spine runs after the pointers are reloaded into them. -/
def spinePins : GpAlloc := [("out", "%rdi"), ("acc", "%rsi"), ("fp", "%rbx")]

/-- The field-step per-op pins: only `fp`→`%rbx` (plus the op's MULX pins). This
    is the mono kernel's budget, so `X25519MonoLadderKernel`'s verified
    no-overflow allocation applies; `%rdi`/`%rsi` are free scratch here because
    the `out`/`acc` pointers are spilled in the frame and reloaded for copy-out. -/
def stepFramePins : GpAlloc := [("fp", "%rbx")]

/-- Render the copy-in spine: `out`/`acc`/`fp` pinned. -/
def copyInLines : List String :=
  renderBlockBody (allocGp spinePins copyInBlock) copyInBlock

/-- Render the copy-out spine: `out`/`acc`/`fp` pinned. -/
def copyOutLines : List String :=
  renderBlockBody (allocGp spinePins copyOutBlock) copyOutBlock

/-- Render one field-step op block with `fp` pinned (to `%rbx`) and the op's MULX
    pin set — exactly `X25519MonoLadderKernel.renderOpBlock`'s budget, only with
    the frame base in `%rbx` instead of `%rdi`. -/
def renderStepOp (mulxPins : GpAlloc) (block : List (JInstr 64)) : List String :=
  let pins := stepFramePins ++ mulxPins
  renderBlockBody (allocGp pins block) block

/-- The field-step ops in order (reuse the mono kernel's rebased `opInline*` /
    slot layout); rendered with `fp`→`%rbx` via `renderStepOp`. -/
def stepOpsBundle : List (GpAlloc × List (JInstr 64)) := stepOps

/-- The concatenated field-step body lines. -/
def stepBodyLines : List String :=
  stepOpsBundle.flatMap (fun e => renderStepOp e.1 e.2)

/-- Reload the spilled `out`/`acc` pointers into `%rdi`/`%rsi` before copy-out. -/
def reloadPtrLines : List String :=
  [ "\tmovq " ++ toString accSpill ++ "(%rbx), %rsi"
  , "\tmovq " ++ toString outSpill ++ "(%rbx), %rdi" ]

/-- The whole owned step body lines: copy-in ++ field step ++ reload ++ copy-out. -/
def bundleBodyLines : List String :=
  copyInLines ++ stepBodyLines ++ reloadPtrLines ++ copyOutLines

/-- The whole step as one assembly function `x25519_ladder_step_rustcmd(out, acc)`.
    Prologue: save callee-saved GPs, reserve a 512-byte frame in `%rbx`, and spill
    the `acc`/`out` pointers to the frame (slots `480`/`488`) so the field step can
    use `%rdi`/`%rsi` as scratch. Epilogue restores and returns. -/
def bundleStepAsm : String :=
  renderLeafFn "x25519_ladder_step_rustcmd"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15", "\tpushq %rbp"
    , "\tsubq $512, %rsp", "\tmovq %rsp, %rbx"
    , "\tmovq %rsi, " ++ toString accSpill ++ "(%rbx)"   -- spill acc ptr
    , "\tmovq %rdi, " ++ toString outSpill ++ "(%rbx)" ] -- spill out ptr
    bundleBodyLines
    [ "\tmovq %rdi, %rax"                                 -- reg-ptr return: out
    , "\taddq $512, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-! ## 8. No register-allocation overflow on any emitted block -/

/-- The copy spines and every field-step op block fit the GP budget once the ABI
    pointers and frame base are pinned. -/
theorem bundle_alloc_no_overflow :
    allocOverflow spinePins copyInBlock = none
      ∧ allocOverflow spinePins copyOutBlock = none
      ∧ stepOpsBundle.all (fun e => allocOverflow (stepFramePins ++ e.1) e.2 == none) = true := by
  native_decide

/-- Shape: the emitted body is one function with the exact ABI symbol, contains
    MULX (field multiplies/squares) and the `$121666` `a24` immediate. -/
theorem bundleStepAsm_shape :
    BignumMontMulKernel.hasSub bundleStepAsm "x25519_ladder_step_rustcmd"
      ∧ BignumMontMulKernel.hasSub bundleStepAsm "mulxq"
      ∧ BignumMontMulKernel.hasSub bundleStepAsm "$121666" := by
  native_decide

/-! ## 9. Emit driver -/

def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/x25519_compare/gen_com"
  IO.FS.writeFile
    "bench/x25519_compare/gen_com/x25519_ladder_step_rustcmd_owned.s" bundleStepAsm
  IO.println "wrote gen_com/x25519_ladder_step_rustcmd_owned.s (owned, no rust leaf)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.X25519LadderStepBundleOwned
