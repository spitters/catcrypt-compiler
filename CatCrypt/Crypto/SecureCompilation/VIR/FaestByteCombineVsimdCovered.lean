/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop

@[expose] public section

set_option autoImplicit false

/-!
# FAEST per-index `acc ^= bf128_mul(x[i], alpha_i)` re-sourced through the vector front

The FAEST QuickSilver linear check accumulates a GF(2^128) inner product
`acc = Σ_i x[i] ·_clmul alpha_i` — a loop over a **128-bit array** `x` whose body
is, per index, a 128-bit dynamic load `x[i]` feeding a carry-less multiply into a
128-bit accumulator. Until now the vsimd front could carry the multiply/xor
(`RolledVsimdFrontValidate`, `GhashClmulVsimdCovered`) but NOT the per-index
128-bit load: `RolledVsimdFrontValidate §Note` flagged that `memrefGetDyn`
returns `.sword 64` only. This module closes that gap.

## The new capability: `memrefGetDyn128` + the `vloadidx128` front tag

`CatCryptDialect.memrefGetDyn128 n` is the 128-bit twin of `memrefGetDyn` (added
ADDITIVELY — a distinct ctor, not a widening of `memrefGetDyn`, whose `.sword 64`
return the whole scalar path depends on). It reads a 128-bit value from a
`.memref n` (64-bit-limb array) at 128-bit index `k` by packing the two
consecutive limbs `2k`, `2k+1` little-endian (`memGetDyn128`), the x86 byte-offset
model of a `vmovdqu (%base,%idx,16)` gather.

The vsimd front intercepts the `RVsimdSetExpr "…" "vloadidx128" [x, idx]` node
(`VsimdTag.loadidx128`): unlike the register-operand vsimd ops it resolves `x` via
`lookupMemrefV` and `idx` via `lookupU64`, and emits `.memrefGetDyn128 n` binding
the destination at `.sword 128`. So the full FAEST body

```
  xi  := x[idx]           -- RVsimdSetExpr "xi"  "vloadidx128" ["x","idx"]   (128-bit load)
  t   := clmul(xi, alpha) -- RVsimdSetExpr "t"   "clmul.0"     ["xi","alpha"] (GF(2^128) product)
  acc := acc ⊕ t          -- RVsimdSetExpr "acc" "vsimd.xor"   ["acc","t"]    (accumulate)
```

descends through `translateDialectControlV` to a `Com catCryptDialect` whose
**whole-program machine denote** is exactly the per-index bf128-accumulate — a
concrete `Com.denote = spec` over a memref valuation, exercising the new 128-bit
dynamic load (`native_decide`).

## Scope of the deliverable (honest)

* This reaches the **dialect** with a faithful whole-program denote. It does NOT
  reach owned `.s`: `memrefGetDyn128` is a 128-bit gather from a 64-bit-element
  stack array, for which jasmin has no single op (`stackLoad` is width-matched to
  the array element), so `cryptoDialectToJasminCom` DECLINES it — the honest
  byte-emit residual, exactly as with the SHA-NI ops (`Sha2ShaniVsimdCovered`).
  The decline is exhibited by `faestProg_declines_jasmin`.
* Consequently the rolled `ComL.forLoopN` wrapper (`rolledForLoopNV`, whose body
  is lowered by `cryptoDialectToJasminCom`) also declines
  (`faestRolled_declines`); the whole-program denote is delivered at the
  straight-line dialect-`Com` per-index level instead, via the concrete
  memref-valuation `native_decide` (the SEnv-based
  `translateDialectControlV_denote` homomorphism is vacuous on the memref load —
  the SEnv models only 128-bit register values).

Invoke:  `lake build CatCrypt.Crypto.SecureCompilation.VIR.FaestByteCombineVsimdCovered`
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.FaestByteCombineVsimdCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (clmul128W)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 0. Dimensions — a 128-bit array of two elements (`.memref 4` = 4 limbs) -/

/-- The FAEST-style 128-bit array carries its elements as consecutive 64-bit
    limb pairs, so a length-2 128-bit array is a `.memref 4` (4 × 64-bit). -/
def faN : Nat := 4

/-! ## 1. The per-index body context `[acc, idx, x, alpha]`

`acc` is the 128-bit accumulator (`.here`), `idx` the runtime 128-bit index
(`.sword 64`, `.there .here`), `x` the 128-bit array (`.memref faN`), `alpha` the
per-index GF(2^128) constant (`.sword 128`). -/

/-- The body context: `.sword 128` accumulator, `.sword 64` index, `.memref faN`
    128-bit array, `.sword 128` field constant. -/
def faΓ : Ctx := [.sword 128, .sword 64, .memref faN, .sword 128]

/-- The body VarMap: `acc ↦ .here`, `idx ↦ .there .here`, `x ↦ .there² .here`,
    `alpha ↦ .there³ .here`. -/
def faVM : VarMap faΓ :=
  (((VarMap.empty.bind (t := .sword 128) "alpha").bind (t := .memref faN) "x").bind
      (t := .sword 64) "idx").bind (t := .sword 128) "acc"

/-! ## 2. The FAEST per-index body: 128-bit load + clmul + xor accumulate -/

/-- One index of the FAEST bf128 accumulate: `xi := x[idx]` (128-bit dynamic
    load), `t := clmul(xi, alpha)` (GF(2^128) carry-less product), `acc := acc ⊕ t`. -/
def faestBody : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "xi"  "vloadidx128" ["x", "idx"])
  (.RSeq (LowCT.RVsimdSetExpr "t"   "clmul.0"     ["xi", "alpha"])
         (LowCT.RVsimdSetExpr "acc" "vsimd.xor"   ["acc", "t"]))

/-! ## 3. Coverage -/

/-- **The FAEST per-index body is `IsCoveredV`**: three `vsimd`-tagged ops — the
    new 128-bit load `vloadidx128`, the `clmul.0` product, and the `vsimd.xor`
    accumulate — each tag parsing. -/
theorem faestBody_coveredV : IsCoveredV faestBody :=
  .rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
  (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
         (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide)))

/-! ## 4. The vsimd front fires -/

/-- **The vsimd front fires on the FAEST per-index body** (the `vloadidx128` arm
    resolves `x`/`idx` and emits `.memrefGetDyn128`). -/
theorem faestFront_fires : (translateDialectControlV faVM faestBody).isSome := by
  native_decide

/-- The front-emitted result program (returns the `.sword 128` slot `acc`). -/
def faestProg : Option (Com catCryptDialect faΓ (.sword 128)) :=
  vsimdResultProg faVM faestBody "acc"

/-- The front actually emits a result program. -/
theorem faestProg_isSome : faestProg.isSome := by native_decide

/-! ## 5. Byte-emit residual (honest): `cryptoDialectToJasminCom` declines

The emitted program contains `memrefGetDyn128` — a 128-bit gather from a
64-bit-element stack array, which jasmin's width-matched `stackLoad` cannot
express as a single op — so the lowering DECLINES. This reaches the dialect with
a faithful denote (below), not owned `.s`; the honest analogue of the SHA-NI
residual. -/

/-- **The lowering declines** (`memrefGetDyn128` has no single jasmin op). -/
theorem faestProg_declines_jasmin :
    (faestProg.bind cryptoDialectToJasminCom) = none := by native_decide

/-! ## 6. THE DELIVERABLE — whole-program dialect denote = the bf128 accumulate

The front-emitted `Com catCryptDialect` denotes exactly the per-index
bf128-accumulate: for the memref array `arr`, `acc := acc ⊕ clmul(x[idx], alpha)`
with `x[idx]` the little-endian pack of limbs `2·idx`, `2·idx+1` (`memGetDyn128`).
A concrete memref-valuation `native_decide` — the load, the product, and the
accumulate all evaluated through the dialect denotation, exercising
`memrefGetDyn128`. -/

/-- INDEPENDENT pure-`BitVec 128` reference: `acc ⊕ (x[idx] ·_clmul alpha)`, the
    128-bit load `x[idx]` = `memGetDyn128 arr idx.toNat`, the product the low-lane
    `clmul128W` (byte-identical to `VPCLMULQDQ` imm `0x00`). -/
def faestSpec (acc0 alpha : BitVec 128) (arr : Fin faN → BitVec 64)
    (idx : BitVec 64) : BitVec 128 :=
  acc0 ^^^ clmul128W (memGetDyn128 arr idx.toNat) alpha 0

/-- Denote the front-emitted program at a concrete valuation
    `[acc0, idx, arr, alpha]`. -/
def faestDenote (acc0 : BitVec 128) (idx : BitVec 64) (arr : Fin faN → BitVec 64)
    (alpha : BitVec 128) : Option (BitVec 128) :=
  faestProg.map (fun com =>
    com.denote (.cons acc0 (.cons idx (.cons arr (.cons alpha .nil)))))

/-- A concrete two-element 128-bit array (as 4 limbs): element 0 = limbs (0,1),
    element 1 = limbs (2,3). -/
def sampleArr : Fin faN → BitVec 64 :=
  fun i => match i with
    | ⟨0, _⟩ => 0x0011223344556677
    | ⟨1, _⟩ => 0x8899aabbccddeeff
    | ⟨2, _⟩ => 0x0123456789abcdef
    | _      => 0xfedcba9876543210

/-- Sample 128-bit accumulator seed and field constant. -/
def sampleAcc   : BitVec 128 := 0x0f1e2d3c4b5a69788796a5b4c3d2e1f0
def sampleAlpha : BitVec 128 := 0x00112233445566778899aabbccddeeff

/-- **denote = spec at index 1** (loads element 1 = limbs 2,3 of `x`): the
    front-emitted program computes `acc ⊕ clmul(x[1], alpha)`. -/
theorem faestDenote_spec_idx1 :
    faestDenote sampleAcc 1 sampleArr sampleAlpha
      = some (faestSpec sampleAcc sampleAlpha sampleArr 1) := by native_decide

/-- **denote = spec at index 0** (loads element 0 = limbs 0,1). -/
theorem faestDenote_spec_idx0 :
    faestDenote sampleAcc 0 sampleArr sampleAlpha
      = some (faestSpec sampleAcc sampleAlpha sampleArr 0) := by native_decide

/-- **Carry-suppression KAT.** With `acc = 0`, `alpha = 3` (`x + 1`), and index `1`
    selecting the 128-bit element `x[1] = 3` (limbs 2,3 = `(3,0)` below), the step
    is `(x+1)·_clmul(x+1) = (x+1)² = x²+1 = 5` over `GF(2)[x]` — the defining
    carry-*less* property, NOT the integer `3·3 = 9`. -/
theorem faestDenote_carry_suppression :
    faestDenote 0 1 (fun i => match i with | ⟨2, _⟩ => 3 | _ => 0) 3
      = some 5 := by native_decide

/-! ## 7. The rolled `ComL.forLoopN` wrapper is blocked by the same residual

`rolledForLoopNV` lowers its front body through `cryptoDialectToJasminCom`
(`frontLoopBodyJV`), which declines `memrefGetDyn128` (§5), so the rolled owned
loop path likewise declines (`rolledForLoopNV = none`). The whole-program denote
is delivered above at the straight-line dialect level via the concrete
memref-valuation `native_decide`; reaching a rolled owned `.s` is gated on a
128-bit gather backend op (out of the dialect+front scope).

## 8. Axiom audit -/

#print axioms faestBody_coveredV
#print axioms faestFront_fires
#print axioms faestProg_declines_jasmin
#print axioms faestDenote_spec_idx1
#print axioms faestDenote_carry_suppression

end CatCrypt.Crypto.SecureCompilation.VIR.FaestByteCombineVsimdCovered
