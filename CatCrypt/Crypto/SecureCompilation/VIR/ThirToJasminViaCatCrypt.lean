/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ThirToCatCryptDialect
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

/-!
# The composed `thir → catCrypt → jasmin` spine (the convergence route, LIVE)

`ThirToCatCryptDialect.lean` lifts a THIR-front body **up** into the high
algebraic crypto-SSA surface `catCryptDialect`
(`lowerThirToCatCrypt : Com thirDialect → Option (Com catCryptDialect)`, sound
by `lowerThirToCatCrypt_denote`). `DialectToJasminCom.lean` then lowers that
high surface back **down** to the flat register/two-address
`jasminDialect`
(`cryptoDialectToJasminCom`, sound by
`DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`).

This file **composes** the two edges into a single end-to-end route

```
Com thirDialect ──lowerThirToCatCrypt──▶ Com catCryptDialect
                ──cryptoDialectToJasminCom──▶ Com jasminDialect
```

and proves one denote-preservation theorem for the whole spine by threading the
two committed soundness lemmas. This demonstrates the **convergence**: a
hax/THIR-front body can reach `jasminDialect` *via the high `catCryptDialect`*
(where the algebraic optimizer, the relational-compile passes, and the
field/limb rewrites live) — not only by the flat `thir → jasmin` path of
`ThirDialect.lean`. The route is *live*, not vacuous: the smoke demonstrator
routes a scalar `a + b` THIR kernel all the way to a jasmin `regArith add`,
denoting identically.

## The carrier/valuation transport composition

The intermediate `catCryptDialect` program lives at context `tcCtx Γ` and type
`tcTy t` (the `JasminTy → CryptoTy` type map of `ThirToCatCryptDialect`). Lowering
it lands `Com jasminDialect (mapCtx (tcCtx Γ)) (mapTy (tcTy t))` (the
`CryptoTy → JasminTy` map of `CryptoToJasminCom`). The composed valuation
transport is `ctMapValD ∘ vTcVal` and the composed value transport is
`ctTransTy ∘ tcEntry t`; the two soundness lemmas chain exactly:

    j.denote (ctMapValD (vTcVal V))
      = ctTransTy (c'.denote (vTcVal V))          -- cryptoDialectToJasminCom_denote_eq'
      = ctTransTy (tcEntry t (c.denote V))         -- lowerThirToCatCrypt_denote

On the covered `reg w` fragment both `tcEntry (.reg w)` and `ctTransTy (.sword w)`
are the identity (`⟦.reg w⟧ = ⟦.sword w⟧ = BitVec w` defeq), so the composite is
exact denotation preservation.

## Covered fragment

The composed route covers exactly the **intersection** of the two edges'
fragments. `lowerThirToCatCrypt` covers `thBin add/sub/mul/and/or/xor`,
`thShlImm`/`thShrImm`, `thConst`, and `let`/`var`/`ret`;
`cryptoDialectToJasminCom` covers `bvAdd/Sub/Mul/And/Or/Xor`, `bvConst`,
`extCall`, the dynamic memref ops, and the word-native crypto ops. The seam
declines `bvShiftL`/`bvShiftR` (the immediate logical shifts `thShlImm`/`thShrImm`
lower into), so the composed route covers the **arith + const core**
(`add/sub/mul/and/or/xor` + `thConst`) end-to-end. Extending the route to the
immediate shifts requires the parallel `catCryptDialect`-ops work that teaches
`cryptoDialectToJasminCom` to lower `bvShiftL`/`bvShiftR` (it already lowers the
*variable* shifts `bvShiftLV`/`bvShiftRV` and the rotates `bvRor`/`bvShiftRA`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ThirToJasminViaCatCrypt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.ThirToCatCrypt
  (tcTy tcCtx tcEntry vTcVal lowerThirToCatCrypt lowerThirToCatCrypt_denote
   smokeAddThir)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
  (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
  (ctMapValD cryptoDialectToJasminCom_denote_eq')
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect
  (ctTransTy ctTransTy_sword)
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (thirDialect thirDenote)

/-! ## 1. The composed route -/

/-- The composed `thir → catCrypt → jasmin` route: lift the THIR body up to
    `catCryptDialect` (`lowerThirToCatCrypt`), then lower it back down to
    `jasminDialect` (`cryptoDialectToJasminCom`). `none` exactly when either edge
    declines (the composed fragment is the intersection of the two edges'). -/
def thirToJasminViaCatCrypt {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) :
    Option (Com jasminDialect (mapCtx (tcCtx Γ)) (mapTy (tcTy t))) :=
  (lowerThirToCatCrypt c).bind cryptoDialectToJasminCom

/-! ## 2. End-to-end denotation preservation (the headline)

Compose the two committed soundness lemmas. The `Option.bind` succeeds only when
both edges do, exposing the intermediate `catCryptDialect` program `c'` with
`lowerThirToCatCrypt c = some c'` and `cryptoDialectToJasminCom c' = some j`. The
first edge's soundness rewrites the jasmin denotation through `c'`; the second
rewrites `c'` through the THIR source. -/

/-- **The end-to-end spine soundness theorem.** When the composed route succeeds
    (`thirToJasminViaCatCrypt c = some j`), the resulting `jasminDialect` program
    `j` denotes, on the composed-transport valuation `ctMapValD (vTcVal V)`, to the
    composed transport `ctTransTy (tcEntry t (c.denote V))` of the source THIR
    denotation. Proved by *composing* `cryptoDialectToJasminCom_denote_eq'` (the
    catCrypt → jasmin edge) with `lowerThirToCatCrypt_denote` (the thir → catCrypt
    edge). On the `reg w` fragment both transports are the identity, so this is
    exact denotation preservation along the high `catCryptDialect` route. -/
theorem thirToJasminViaCatCrypt_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) (V : Ctxt.Valuation Γ)
    (j : Com jasminDialect (mapCtx (tcCtx Γ)) (mapTy (tcTy t)))
    (hj : thirToJasminViaCatCrypt c = some j) :
    j.denote (ctMapValD (vTcVal V))
      = ctTransTy (tcEntry t (c.denote V)) := by
  -- Peel the `Option.bind`: expose the intermediate catCrypt program `c'`.
  unfold thirToJasminViaCatCrypt at hj
  rw [Option.bind_eq_some_iff] at hj
  obtain ⟨c', hc', hjc⟩ := hj
  -- catCrypt → jasmin edge.
  rw [cryptoDialectToJasminCom_denote_eq' c' (vTcVal V) j hjc]
  -- thir → catCrypt edge.
  rw [lowerThirToCatCrypt_denote c V c' hc']

/-! ## 3. Live demonstrator: a scalar `a + b` routes the full spine

The `smokeAddThir` kernel (`let s = a + b; ret s` over `[reg 64, reg 64]`), the
THIR-front image of a hax scalar body, routes the **whole** spine: up to a
`catCryptDialect` `bvAdd 64`, then down to a `jasminDialect` `regArith add 64`.
We confirm the route *succeeds* and is denotation-preserving — proving the
convergence route is live, not vacuous. -/

/-- The composed route succeeds on the scalar `add` kernel: it climbs to
    `catCryptDialect` (`bvAdd 64`) and descends to `jasminDialect`
    (`regArith add 64`). -/
theorem smokeAddViaCatCrypt_isSome :
    (thirToJasminViaCatCrypt smokeAddThir).isSome := by
  native_decide

/-- The fully-routed `jasminDialect` program: the `add` kernel after the whole
    `thir → catCrypt → jasmin` spine, at `[reg 64, reg 64] ⊢ reg 64`. -/
def smokeAddJasminViaCatCrypt :
    Com jasminDialect (mapCtx (tcCtx [.reg 64, .reg 64])) (mapTy (tcTy (.reg 64))) :=
  (thirToJasminViaCatCrypt smokeAddThir).get smokeAddViaCatCrypt_isSome

/-- **The route is live and denotation-preserving end-to-end.** The fully-routed
    jasmin program denotes exactly the source THIR `add` kernel (`reg` fragment,
    so both transports are the identity), on every input — by
    `thirToJasminViaCatCrypt_denote`. -/
theorem smokeAddViaCatCrypt_denote
    (V : Ctxt.Valuation (d := jasminDialect) [.reg 64, .reg 64]) :
    smokeAddJasminViaCatCrypt.denote (ctMapValD (vTcVal V))
      = ctTransTy (tcEntry (.reg 64) (smokeAddThir.denote V)) :=
  thirToJasminViaCatCrypt_denote smokeAddThir V smokeAddJasminViaCatCrypt
    (Option.eq_some_of_isSome smokeAddViaCatCrypt_isSome)

end CatCrypt.Crypto.SecureCompilation.VIR.ThirToJasminViaCatCrypt
