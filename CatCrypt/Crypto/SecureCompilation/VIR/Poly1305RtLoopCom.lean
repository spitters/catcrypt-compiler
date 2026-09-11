/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Poly1305Com
public import CatCrypt.Crypto.SecureCompilation.VIR.Poly1305Com
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Poly1305 MAC — FRONT-COMPILED owned runtime-block-loop x86-64 emit

The Poly1305 130-bit field MAC over `𝔽_{2¹³⁰−5}` as a **runtime-trip counted
loop** `ComL.forLoopNRt`, sourced through the verified `CProg`-free runtime-loop
front — NO hand-built `Com` in the emit path. The per-block `5×26`-limb HACL
Horner field step is authored as a covered `LowCT` loop body
(`RArrLoad`/`RScalarSetExpr`/`RArrStore` over the runtime loop index `idx`) and
front-compiled by `rolledForLoopNRt`:

```
  blockBodyLowCT (RArrLoad acc/inp/block-limbs at idx + RScalarSetExpr HACL
                  field step + RArrStore acc)
    --(rolledForLoopNRt: translateDialectControl + cryptoDialectToJasminCom)-->
        JLoopBodyN.update : Com jasminDialect [A5, reg 64, AM] A5
    --(ComL.forLoopNRt update nblk out [inp] (ret out))--> ComL  (ONE body copy + jne back-edge)
    --(ComL.toLprogPhysAbi / renderLprogAtt)--------------> AT&T .s (NO jasminc)
```

The accumulator (the `out` array) is threaded through the back-edge, the
message-block input array `inp` is the loop invariant, and the trip count is the
**runtime** `nblk` argument (read from `RDX`). The per-block field schedule is
identical to `Poly1305Com` (the fixed-`NBlk` straight-line counterpart) — the
HACL `r5i = 5·rᵢ` precompute, the five register diagonals, the carry chain with
the `2¹³⁰ ≡ 5` top-limb fold; here it is written once and folded `nblk` times.

## ABI (matches the C KAT harness `poly1305_mac_hacl(out, inp, nblk)`)

  `extern uint64_t *poly1305_mac_hacl(uint64_t *out, const uint64_t *inp, uint64_t nblk);`

* `out`  (RDI) — 5 × u64 MAC accumulator limbs, live in this buffer across loop
  iterations. **The caller must zero `out` before the call** (it seeds the Horner
  fold at 0); the harnesses pass `uint64_t acc[5] = {0}`.
* `inp`  (RSI) — `r[0..4]` (5 u64 clamped key limbs) then `nblk` pre-packed 5-limb
  message blocks (`inp[5 + 5·i + k]`).
* `nblk` (RDX) — the runtime block count: the loop folds exactly `nblk` blocks.

The body, at trip `idx`, loads `acc[0..4]` from `out`, `r[0..4]` from `inp[0..4]`,
the block limbs `inp[5 + 5·idx + k]` (a computed-index load), runs the Horner step
`a := (a + blockᵢ)·r mod p` (add block, recompute `r5`, five diagonals, carry),
and stores the limbs back to `out`. The final mod-`2¹³⁰−5` freeze, `+ s`, and
serialization are done in C.

## What is verified in-model

`ComL.denote macRtProg` over a concrete input `Valuation` is the kernel's
word-level semantics: the runtime fold of the per-block field step. The front
succeeds (`macRtProg_isSome`) and the emit renders. The driver
`bench/chachapoly_compare/poly1305_rtloop_refcheck.lean` `#eval`-checks the
denotation against an INDEPENDENT plain-`Nat` Poly1305 reference (Horner over `ℤ`
reduced mod `2¹³⁰−5`) on the RFC 8439 §2.5.2 vector and pseudo-random cases. The
external `bench/chachapoly_compare` `aead-vs` KAT byte-checks the owned `.s`
against HACL* under the `poly1305_mac_hacl` symbol.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poly1305RtLoopCom

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.VIR.Poly1305Com
  (rN aN r5N dN diagExpr carryStmts seqAll)

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- Max words of the message-block input array `inp` in the DENOTE model. The
    rendered SIB loads use byte offsets, so the assembly is size-agnostic; this
    only bounds the in-Lean `#eval` check. `5 + 5·1100 = 5505` covers the AEAD
    `NBlkAeadMax = 1100` 16 KiB row. -/
abbrev M : Nat := 5505

/-- The 5-limb accumulator array type (`out`). -/
abbrev A5 : JasminTy := .stackArr 64 5
/-- The message-block input array type (`inp`). -/
abbrev AM : JasminTy := .stackArr 64 M

/-! ## 1. The per-block HACL field step, authored as covered LowCT

The loop body runs over the catCryptDialect context
`Γbody = [acc:.memref 5, idx:.sword 64, inp:.memref M]` (accumulator first, the
runtime loop index next, the message-block array as the invariant). `idx` is the
loop binder; the block-limb loads compute their index from it. The scalar field
arithmetic (`r5`, five diagonals, carry chain) is REUSED verbatim from the
fixed-trip `Poly1305Com` (`diagExpr` / `carryStmts`), so the two kernels
share one field schedule. -/

/-- Loaded-block-limb slot name `b{k}`. -/
def bN (k : Nat) : String := "b" ++ toString k

/-- The accumulator array slot `acc` (5 × u64). -/
def accLoc : Located := ⟨"acc", .TBytes 40⟩

/-- The message-block input array slot `inp` (`M` × u64). -/
def inpLoc : Located := ⟨"inp", .TBytes (8 * M)⟩

/-- Load the accumulator limbs `a0..a4` from `acc[0..4]` (constant indices). -/
def loadAccStmts : List LowCT :=
  (List.range 5).flatMap (fun k =>
    [ .RScalarSetExpr "ix" (.SLit k), .RArrLoad ⟨aN k, .TU64⟩ accLoc "ix" ])

/-- Load the clamped key limbs `r0..r4` from `inp[0..4]` (constant indices). -/
def loadKeyStmts : List LowCT :=
  (List.range 5).flatMap (fun k =>
    [ .RScalarSetExpr "ix" (.SLit k), .RArrLoad ⟨rN k, .TU64⟩ inpLoc "ix" ])

/-- Set the block base `5·idx + 5` and load the block limbs `b0..b4` from
    `inp[base + k]` (computed indices off the runtime loop index). -/
def loadBlockStmts : List LowCT :=
  .RScalarSetExpr "base" (.SAdd (.SMul (.SLit 5) (.SVar "idx")) (.SLit 5))
  :: (List.range 5).flatMap (fun k =>
       [ .RScalarSetExpr "ix" (.SAdd (.SVar "base") (.SLit k)),
         .RArrLoad ⟨bN k, .TU64⟩ inpLoc "ix" ])

/-- Add the block limbs into the accumulator, `a_k += b_k`. -/
def addBlockStmts : List LowCT :=
  (List.range 5).map (fun k =>
    .RScalarSetExpr (aN k) (.SAdd (.SVar (aN k)) (.SVar (bN k))))

/-- The HACL wraps `r5_j = 5·r_j` for `j = 1..4`. -/
def wrapStmts : List LowCT :=
  (List.range 4).map (fun j =>
    .RScalarSetExpr (r5N (j+1)) (.SMul (.SVar (rN (j+1))) (.SLit 5)))

/-- The five register diagonals `d0..d4`. -/
def diagStmts : List LowCT :=
  (List.range 5).map (fun o => .RScalarSetExpr (dN o) (diagExpr o))

/-- Store the reduced limbs `a0..a4` back to `acc[0..4]`. -/
def storeAccStmts : List LowCT :=
  (List.range 5).flatMap (fun k =>
    [ .RScalarSetExpr "ix" (.SLit k), .RArrStore accLoc "ix" ⟨aN k, .TU64⟩ ])

/-- One Horner block over the runtime loop index `idx`: load the accumulator
    `a0..a4` from `acc[0..4]`, the key `r0..r4` from `inp[0..4]`, the block limbs
    `b0..b4` from `inp[5 + 5·idx + k]`; add the block (`a_k += b_k`), recompute the
    wraps `r5_j = 5·r_j`, the five diagonals `d0..d4`, the carry chain; store the
    reduced limbs `a0..a4` back to `acc[0..4]`. Leaves `acc` rebound at
    `.memref 5` (the accName the front's epilogue returns). -/
def blockBodyLowCT : LowCT := seqAll (
  loadAccStmts ++ loadKeyStmts ++ loadBlockStmts ++ addBlockStmts
    ++ wrapStmts ++ diagStmts ++ carryStmts ++ storeAccStmts)

/-! ## 2. The body context + VarMap

`Γbody = [acc, idx, inp]` (head-first): `acc` the accumulator (`.here`), `idx` the
runtime loop index (`.there .here`), `inp` the invariant (`.there² .here`). -/

/-- The loop-body context: accumulator `acc` (5 limbs), loop index, invariant
    input array `inp` (`M` words). -/
def Γbody : Ctx := [.memref 5, .sword 64, .memref M]

/-- The body VarMap: `inp` bound deepest, then `idx`, then `acc` at `.here`. -/
def vmBody : VarMap Γbody :=
  (((VarMap.empty.bind (t := .memref M) "inp").bind
      (t := .sword 64) "idx").bind (t := .memref 5) "acc")

/-! ## 3. The whole MAC `ComL` (the runtime-trip loop)

Outer argument context `Γ = [nblk:reg 64, inp:AM, out:A5]` (newest-first). Under
the export's program-root `resolveVar` convention this routes `out → a0 → RDI`,
`inp → a1 → RSI`, `nblk → a2 → RDX` — the `poly1305_mac_hacl(out, inp, nblk)`
ABI. `count = .here` (nblk), `init = .there² .here` (out seed), the invariant
`inp = .there .here`. -/

/-- The front-compiled runtime-trip Poly1305 MAC (one body copy + `jne` back-edge,
    counter seeded from the runtime `nblk` register), or `none` if the front
    declines. -/
def macRtProgOpt : Option (ComL [r64, AM, A5] A5) :=
  rolledForLoopNRt (Γouter := [r64, AM, A5]) (accCTy := .memref 5)
    (invCTys := [.memref M])
    vmBody "acc" blockBodyLowCT
    (count := .here)
    (init := .there (.there .here))
    (invs := .cons (.there .here) .nil)

/-- The runtime-loop body front-compiles and wraps to a
    `ComL.forLoopNRt`. -/
theorem macRtProg_isSome : macRtProgOpt.isSome := by native_decide

/-- **The whole Poly1305 MAC as a runtime-trip `ComL.forLoopNRt`** — FRONT-GENERATED
    (`rolledForLoopNRt` = `translateDialectControl` + `cryptoDialectToJasminCom`
    on the covered `LowCT` body, wrapped in `ComL.forLoopNRt`), not hand-built.
    Seeds the accumulator from `out`, folds `blockBodyLowCT` exactly `nblk` times
    over the `inp` invariant, returns the final accumulator array. -/
def macRtProg : ComL [r64, AM, A5] A5 := macRtProgOpt.get macRtProg_isSome

/-! ## 4. The owned `Lprog` and the rendered `.s` -/

/-- The runtime-loop Poly1305 MAC as a rolled, owned-RA 3-pointer-ABI `Lprog`
    under the C symbol `fname` (`RDI = out`, `RSI = inp`, `RDX = nblk`). -/
def macRtLprog (fname : String) : Lprog :=
  ComL.toLprogPhysAbi macRtProg fname (argName 0) [argName 1]
    (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]

/-- The owned AT&T `.s` text for the runtime-loop Poly1305 MAC (NO jasminc). -/
def macRtAsm (fname : String) : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (macRtLprog fname)

/-! ## 5. Structural gates on the rolled physical body -/

/-- The 3-arg-ABI physical body of the front-compiled runtime-count loop. -/
def macRtPhysBody : Lcmd :=
  (ComL.toLfundefPhysAbi macRtProg (argName 0) [argName 1]
    (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]).lfd_body

/-- **Real back-edge preserved through RA:** the physical body has both an
    internal `Llabel` and a `Lcond` (`jne .L<d>`) — a counted loop, NOT an
    unrolled `nblk`-copy chain. -/
theorem macRtPhysBody_has_backedge :
    (macRtPhysBody.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
      && (macRtPhysBody.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))
      = true := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Poly1305RtLoopCom
