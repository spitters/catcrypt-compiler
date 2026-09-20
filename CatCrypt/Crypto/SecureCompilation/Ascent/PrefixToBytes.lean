/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ComScalarPrefix
public import CatCrypt.Crypto.SecureCompilation.Ascent.BlockTieFinalState
public import CatCrypt.Crypto.SecureCompilation.Ascent.FrontToBytes

/-!
# The scalar prefix of a dialect program, its bytes, and its slots

A `Com jasminDialect` whose leading operations are scalar reaches machine bytes
through its prefix, and every slot the prefix binds is readable from its
register. The program's return type is unconstrained, so this covers the shape
the `LowCT` front emits: scalar operations followed by a unit binder and a unit
return.

## What is proved

* `finalCtx_eq_finalCtxB` — the two final-context recursions agree, so a prefix
  recognised by `comScalarPrefix` is the same block the state correspondence is
  indexed by.
* `prefix_bytes_state` — for a recognised prefix: the encoding of the lowered
  block decodes to that block renamed through the allocation, and the state
  correspondence holds at the prefix's final context.
* `unitProg_prefix_bytes` — the instance, on a program of the front's shape.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

/-! ## 1. The two final-context recursions agree -/

/-- `ArithBlock.finalCtx`, which types the tail `comScalarPrefix` returns, and
    `finalCtxB`, which indexes the state correspondence, are the same function. -/
theorem finalCtx_eq_finalCtxB : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) →
    ab.finalCtx = finalCtxB ab
  | _, .ret _ => rfl
  | _, .op _ _ _ _ rest => finalCtx_eq_finalCtxB rest
  | _, .un _ _ _ rest => finalCtx_eq_finalCtxB rest
  | _, .cnst _ rest => finalCtx_eq_finalCtxB rest

/-! ## 2. The composition -/

/-- **A recognised scalar prefix reaches bytes, and every slot it binds is
    readable.** The block whose bytes these are is `c`'s prefix, since `c` is
    that prefix followed by the tail; the encoding decodes to the block renamed
    through the allocation; and after `runBlock` the state correspondence holds
    at the prefix's final context, so each slot sits in its own register. -/
theorem prefix_bytes_state {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (ab : ArithBlock Γ)
    (tail : Com jasminDialect ab.finalCtx t)
    (h : comScalarPrefix c = some ⟨ab, tail⟩)
    (nm : RegMapG Γ) (g : Nat → String) (alloc : GpAlloc)
    (hc : ∀ i ∈ lowerBlock ab nm g, blockCovered i = true)
    (hr : ∀ i ∈ lowerBlock ab nm g, mulxRdxOk alloc i = true)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG nm V s) (hfresh : FreshFor nm g) :
    ab.toComWith tail = c
      ∧ decodeJStream (lowerBlock ab nm g).length
          (encodeJBlock alloc (lowerBlock ab nm g))
          = some ((lowerBlock ab nm g).map (renameJ alloc))
      ∧ JStateInterpG (finalNm ab nm g) (finalVal ab V)
          (runBlock s (lowerBlock ab nm g)) :=
  ⟨comScalarPrefix_toComWith c ab tail h,
   roundtrip_block alloc (lowerBlock ab nm g) hc hr,
   lowerBlock_tie_state ab nm g s V hinterp hfresh⟩

/-! ## 3. The instance

`comBlock2Unit` has the shape the `LowCT` front emits: two scalar operations, a
unit binder and a unit return. Its prefix is `block2`, lowered over the register
map and stream of `DialectToBytes`. -/

/-- The prefix of the front-shaped program lowers to the same instructions as
    `block2`. -/
theorem unitProg_prefix_block :
    comScalarPrefix comBlock2Unit = some ⟨block2, comBlock2UnitTail⟩ :=
  comBlock2Unit_prefix

/-- **The instance.** The prefix lowers to the front-routed block, whose bytes
    decode back to it, and both slots the prefix binds are readable from their
    registers. -/
theorem unitProg_prefix_bytes (s : JState 64) (V : Ctxt.Valuation Δ2)
    (hinterp : JStateInterpG nm2 V s) :
    decodeJStream frontBlock.length frontBytes = some frontBlock ∧
      JStateInterpG (finalNm block2 nm2 g2) (finalVal block2 V)
        (runBlock s frontBlock) :=
  ⟨frontBytes_decode, frontBlock_final_state s V hinterp⟩

/-- On the sample state the prefix leaves `x + y = 42` in `%rcx` and
    `(x + y) * x = 294` in `%rdx`. -/
theorem sample_prefix_slots :
    (runBlock sampleS2 frontBlock).get "%rcx" = (42 : BitVec 64) ∧
      (runBlock sampleS2 frontBlock).get "%rdx" = (294 : BitVec 64) :=
  ⟨(unitProg_prefix_bytes sampleS2 sampleV2 sampleS2_interp).2 (.there .here),
   (unitProg_prefix_bytes sampleS2 sampleV2 sampleS2_interp).2 .here⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
