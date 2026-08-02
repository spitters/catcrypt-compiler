/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RustStateSubstrate
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintCorrect
import CatCrypt.Crypto.SecureCompilation.BorrowSafety

/-!
# Extraction-rooted compiler correctness on the `CProg`-free dialect front

`CompilerCorrectness.lean` builds the *optimizer + backend* half of the
end-to-end story for the lattice NTT-multiplication route
(`latticeNttMul_compile_correct`). This file builds the **front-rooted**
analogue: it starts from *extracted* `LowCT` and chains the verified front
stages into one statement, so the correctness story can begin at the
extraction boundary. It is stated over the dialect-native front:

```
LowCT c   ──TranslateDialectDirectControl.translateDialectControl──▶   Com[catCryptDialect]
            ──DialectToJasminCom.cryptoDialectToJasminCom (A1)──▶      Com[jasmin]
            ──JasminPrint.lowerComToProg (A4)──▶                       JasminProg
```

## The two front theorems we chain

* **front (LowCT → catCryptDialect)** — `CryptoDialectRustSim.rustExecSimulatesDialect`.
  This is a **simulation/refinement** result, *not* a denotational equality:
  on the control-covered fragment `IsCoveredCtl`, given a successful dialect
  translation `translateDialectControl vm c = some o` and a concrete execution
  `RustExec N leafSpec c rs rs'` from a state related to the entry valuation
  (`RustStateInterp vm rs V`), it produces an **existential** post-state
  valuation `V' : HVec o.Γ'` with `RustStateInterp o.vm rs' V'` (a byte-layout
  invariant per VarMap binding). Its *statement* names only the `CProg`-free
  front; no `CProg`/`translate` appears.

* **A1 (catCryptDialect → Com[jasmin])** —
  `DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`. This is a
  **denotational equality**: if the front succeeds
  (`cryptoDialectToJasminCom com = some jcom`), then the lowered jasmin program
  denotes to the value transport `jcom.denote (ctMapValD W) = ctTransTy (com.denote W)`.
  Unlike the old `CProg` route, leaf agreement is **discharged internally**
  (`dialectJasminLeafAgrees_holds`), so no `JasminLeafAgrees` hypothesis is
  carried; and both sides are plain values, with no `SPComp` purity read-off.

## The shape mismatch (the adapter)

The two front theorems fuse with a single honest adapter: the front simulation
relates the *state* (`RustStateInterp`, over `HVec o.Γ'`), while A1 relates the
*denotation* (over a `Ctxt.Valuation`). The bridge between them is the
**operational↔denotational adequacy** of the dialect front — that the dialect
program's denotational value `com.denote W` equals the value the source `LowCT`
leaves in the tracked variable `w`. §2b carries it as the explicit hypothesis
`hAdequacy`; §2c **discharges** it from the scalar front-preservation
homomorphism (`TranslateDialectScalar.translateDialectControl_denote_ctl`),
with the value leg stated over the source waist semantics `semScalar` (see
§2c's header for why `semScalar`, not a `leafSpec`-oracle `RustExec` value, is
the provable — and honest — form).

## Trust base (the parametric edges)

Mirrors `CompilerCorrectness.lean`'s trust base. The extraction-rooted story
bottoms out at explicit edges, handled separately rather than hand-waved:

1. **extraction → LowCT** — `haxToLowCT_simulates_full`, discharged
   per-protocol by the bridge `Hyp_*` obligations. An upstream edge; not here.
2. **LowCT → catCryptDialect** — `rustExecSimulatesDialect` (a *simulation*;
   the state invariant `RustStateInterp` is the byte-layout relation preserved).
3. **catCryptDialect→jasmin adequacy** — DISCHARGED (§2c): the dialect
   program's denotation equals the machine-word source-semantics value
   (`semScalar`), proved by the scalar front-preservation homomorphism over
   the `IsCoveredSCtl` sublanguage. The residual, explicitly-named edges are
   the per-kernel `SExpr.inRange` reconciliation to the `Nat`-model
   `RustExec` and the opaque-leaf `leafSpec` convention (§2c header). §2b's
   `hAdequacy`-parametric forms remain for callers outside that sublanguage.
4. **semantic printer faithfulness** — only *structural* faithfulness is proved
   (A4, `JasminPrintCorrect`, instruction counts); the `JasminProg → .jazz`
   text/parse is a later tier.
5. **`.jazz → x86`** — `jasminc`, the deliberate trusted base.

The cross-side leaf agreement that the old `CProg` route carried as
`JasminLeafAgrees` is, on the dialect front, discharged unconditionally by
`DialectToJasminComCorrect.dialectJasminLeafAgrees_holds` rather than a
parametric edge of the front lowering.

All goals closed (no `sorry`); the gaps are carried as the explicit
hypotheses listed above.
-/

set_option autoImplicit true -- SSA IR front: many context/type variables

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
-- `ctTransTy` (and its identity/default lemmas) live in `JasminValTransport.lean`
-- under the `CryptoToJasminComCorrect` namespace — not in `CryptoToJasminComCorrect.lean`
-- itself — so this open does not depend on the `CProg`-lowering correctness module.
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Core

/-! ## 1. The dialect front program

`translateDialectControl` yields a *prefix* `o.cont : ComCont Γ o.Γ'`. The
complete dialect program A1 consumes is the close-off `o.cont (Com.ret w)`
(`Option`-valued, since `ComCont` may decline a node). We carry that complete
dialect program `com : Com catCryptDialect Γ t` directly, with its lowering
success `hCom`; the link of `com` to the front output is the operational↔
denotational adequacy bridge `hAdequacy` of the fused theorem below. -/

/-! ## 2. The composed front meta-theorem

We chain the `CProg`-free front simulation
(`CryptoDialectRustSim.rustExecSimulatesDialect`, for the state witness `V'`)
with A1 (`cryptoDialectToJasminCom_denote_eq'`, for the denotation). Leaf
agreement is discharged internally by A1, so no `JasminLeafAgrees` hypothesis is
carried. -/

/-- **Extraction-rooted front correctness (LowCT → Com[catCryptDialect] →
    Com[jasmin]), loose form.**

    Composes the two `CProg`-free front stages into a conjunction. Given:

    * `hCov : IsCoveredCtl c` — the source is in the control-covered fragment;
    * `hTrans : translateDialectControl vm c = some o` — the dialect front
      succeeds;
    * `hExec : RustExec N leafSpec c rs rs'` — a concrete execution trace;
    * `hInv : RustStateInterp vm rs V` — the entry state is byte-layout-related
      to the entry valuation `V`;
    * `hCom : cryptoDialectToJasminCom com = some jcom` — A1's dialect→jasmin
      lowering succeeds,

    the conclusion chains both stages:

    * the front simulation yields an existential post-state valuation `V'` with
      `RustStateInterp o.vm rs' V'` (LowCT → catCryptDialect), and
    * the lowered jasmin program denotes to the value transport of the dialect
      program's denotation (`jcom.denote (ctMapValD W) = ctTransTy (com.denote W)`,
      catCryptDialect → Com[jasmin] via A1).

    The two halves use independent entry valuations (`V : HVec Γ` for the
    simulation, `W : Ctxt.Valuation Γ` for the dialect denotation); the fused
    form below ties them. Leaf agreement is discharged internally by
    `dialectJasminLeafAgrees_holds`. -/
theorem rustToJasminCom_denote_eq
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (V : HVec Γ) (W : Ctxt.Valuation (d := catCryptDialect) Γ)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hCov : IsCoveredCtl c)
    (hTrans : translateDialectControl vm c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hInv : RustStateInterp vm rs V)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    (∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V')
      ∧ jcom.denote (ctMapValD W) = ctTransTy (com.denote W) :=
  ⟨rustExecSimulatesDialect vm c o N leafSpec rs rs' hCov hTrans hExec V hInv,
   cryptoDialectToJasminCom_denote_eq' com W jcom hCom⟩

/-! ## 2b. Tightened fused chain

`rustToJasminCom_denote_eq` above is a loose *conjunction*: its two halves use
independent entry valuations (`V` vs `W`) and `com.denote W` is unrelated to the
front's post-state. The theorem below tightens it:

* the **front simulation is discharged**, not assumed —
  `rustExecSimulatesDialect` supplies the post-state `V'`;
* the conclusion **fuses** the two stages: the jasmin program's denotation equals
  the `ctTransTy`-transport of the LowCT post-state's value for `w`
  (`w.lookup V'`), so it reads "the compiled jasmin code computes the
  value the LowCT source leaves in `w`".

The *only* remaining hypothesis is `hAdequacy`: the dialect program's denotation
`com.denote W` equals `w.lookup V'` for the simulation's post-state `V'`. This is
precisely the **operational↔denotational adequacy** of the dialect front — that
`Com.denote` (the value semantics A1 uses) agrees with the source semantics on
the value left in `w`. That adequacy theorem now exists —
`TranslateDialectScalar.translateDialectControl_denote_ctl`, over the source
waist semantics `semScalar` — and §2c uses it to state the chain with no
adequacy hypothesis at all. The `hAdequacy`-parametric forms in this section
remain for callers outside the `IsCoveredSCtl` sublanguage (or whose value
claim is pinned to a specific `leafSpec` oracle, which the discharged form
deliberately does not cover — see §2c). -/

/-- **End-to-end (dialect front route), fused.** With the front simulation
    discharged and the operational↔denotational adequacy bridge `hAdequacy` as
    the sole explicit hypothesis: there is a post-state valuation `V'`
    byte-related to the LowCT output `rs'`, and the emitted jasmin program's
    denotation is the `ctTransTy`-transport of that post-state's value for `w`.

    ## Honest guarantee (the precise spec — read this before relying on the name)

    *Assuming the dialect program's denotational value equals the operationally-
    produced value (`hAdequacy`), then for a single tracked output variable `w`
    the emitted jasmin program's denotation equals the value the source `LowCT`
    leaves in `w` — output-value agreement under a byte-layout invariant, not
    full functional/memory equivalence, with the hard adequacy edge
    supplied as a hypothesis rather than proved.*

    ### GUARANTEED (proved internally)
    * **Single-output value agreement on the tracked variable `w`.** The
      conclusion equates `jcom.denote (ctMapValD W)` with `ctTransTy (w.lookup V')`
      — the value of the *one* chosen output variable `w` in the related
      post-state `V'`. The front simulation (`rustExecSimulatesDialect`) chains
      with the A1 lowering (`cryptoDialectToJasminCom_denote_eq'`, proved by
      program induction).
    * Existence of a post-state valuation `V'` byte-related to `rs'` (this is
      what the front simulation delivers — *existence*, not value).
    * **Leaf agreement is discharged**, not assumed: A1 closes it via
      `dialectJasminLeafAgrees_holds` (arith/const leaves agree by computation,
      `extCall` leaves on the opaque canonical default). The old `CProg` route's
      `JasminLeafAgrees` hypothesis is gone.

    ### ASSUMED (not proved here — supplied by the caller)
    * `hAdequacy` — operational↔denotational value agreement: that the
      existentially-chosen post-state `V'` carries the value the dialect program
      `com` denotes to. The front simulation gives a related `V'` but **not**
      that the denotation matches; that is exactly what `hAdequacy` asserts. On
      the `IsCoveredSCtl` sublanguage prefer the §2c forms
      (`rustToJasminCom_endToEnd_unconditional`), where this edge is proved
      from `translateDialectControl_denote_ctl` rather than assumed.
    * `hCov`, `hTrans`, `hExec`, `hInv`, `hCom` — caller-supplied premises (the
      source is control-covered, the front ran, a concrete trace, entry states
      related, the lowering ran).

    ### NoAliasVM restriction (silently carried by `hInv`)
    `hInv : RustStateInterp vm rs V` is a byte-layout invariant whose `noAlias`
    **field** is `NoAliasVM vm`. It requires `vm.lookup` to be injective on
    names. The simulation conclusion is *false* for an aliasing seed `vm`. This
    restriction is **not visible in the signature** — it lives inside the
    `RustStateInterp` structure.

    ### NOT claimed
    * No full functional / memory-image / state-transformer equivalence.
    * No multi-output equivalence (only the single tracked `w`).
    * No behavior on aliasing seeds (`NoAliasVM` excludes them — see above). -/
theorem rustToJasminCom_endToEnd
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (V : HVec Γ) (W : Ctxt.Valuation (d := catCryptDialect) Γ)
    (w : CVar o.Γ' t)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hCov : IsCoveredCtl c)
    (hTrans : translateDialectControl vm c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hInv : RustStateInterp vm rs V)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hAdequacy : ∀ V' : HVec o.Γ', RustStateInterp o.vm rs' V' →
        com.denote W = w.lookup V') :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V'
      ∧ jcom.denote (ctMapValD W) = ctTransTy (w.lookup V') := by
  obtain ⟨V', hV'⟩ :=
    rustExecSimulatesDialect vm c o N leafSpec rs rs' hCov hTrans hExec V hInv
  refine ⟨V', hV', ?_⟩
  rw [← hAdequacy V' hV']
  exact cryptoDialectToJasminCom_denote_eq' com W jcom hCom

/-- **Top-level end-to-end (dialect front route), entry interpretation
    discharged.** The top-level specialisation of `rustToJasminCom_endToEnd`: the
    entry varmap is `VarMap.empty` and the front-entry valuation is `HVec.nil`,
    so the entry `RustStateInterp` hypothesis — which silently carried
    `NoAliasVM` in its `noAlias` field — is built **internally** via
    `BorrowSafety.entry_interp` (whose `noAlias` field is `noAlias_empty`). The
    caller therefore supplies no `hInv` and no aliasing hypothesis: the
    `NoAliasVM` side condition is discharged here for every translator-rooted
    program, since every translation pipeline starts from `VarMap.empty`.

    The non-top-level `rustToJasminCom_endToEnd` keeps `hInv` because it is
    parametric over an arbitrary entry varmap `vm`, where `hInv`
    carries the full byte-layout invariant ((rather than only `NoAliasVM`)) and is a real
    precondition. -/
theorem rustToJasminCom_endToEnd_topLevel
    {t : CryptoTy}
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (W : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx))
    (w : CVar o.Γ' t)
    (com : Com catCryptDialect ([] : Ctx) t)
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy t))
    (hCov : IsCoveredCtl c)
    (hTrans : translateDialectControl VarMap.empty c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hAdequacy : ∀ V' : HVec o.Γ', RustStateInterp o.vm rs' V' →
        com.denote W = w.lookup V') :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V'
      ∧ jcom.denote (ctMapValD W) = ctTransTy (w.lookup V') :=
  rustToJasminCom_endToEnd VarMap.empty c o N leafSpec rs rs' HVec.nil W w com jcom
    hCov hTrans hExec
    (CatCrypt.Crypto.SecureCompilation.BorrowSafety.entry_interp rs) hCom hAdequacy

/-! ## 2c. The adequacy edge discharged — end-to-end without `hAdequacy`

`rustToJasminCom_endToEnd` above isolates the operational↔denotational adequacy
of the dialect front as its sole `hAdequacy` hypothesis. The scalar
front-preservation homomorphism
(`TranslateDialectScalar.translateDialectControl_denote_ctl`) is that adequacy
theorem: for any `IsCoveredSCtl`-covered body, front success + source-semantics
success give a post-valuation `V'` consistent with the source post-environment
and per-tail denotation agreement — exactly the coercion the fused chain needs.
The theorems below chain it with A1, producing end-to-end statements whose only
premises are compilation/run successes, entry consistency, and output tracking.
No adequacy hypothesis remains.

**Which source semantics the value claim is stated over.** The homomorphism
runs over `semScalar`, the pure env-level **machine-word-faithful** semantics
of the covered `LowCT` arms, whose per-op waist is exactly what the emitted
dialect op denotes by (opaque leaves ↦ `CryptoTy.default`, dynamic array ops
↦ `memGetDyn`/`memSetDyn`, `SExpr` assignments ↦ the wrapping-u64
`SExpr.evalBV`, `RFor` ↦ the per-trip fold, `RIfNz` ↦ the φ-merge select).
It is NOT `RustExec`, which diverges at exactly two documented points:

1. **opaque leaf calls** — `RustExec` resolves each `RCall` through the
   `leafSpec` **oracle** (`leafSpec.call …`), while the dialect — and hence
   the compiled jasmin program — denotes an opaque leaf to
   `CryptoTy.default`;
2. **`SExpr` arithmetic (the #250 boundary)** — `RustExec`'s
   `scalarSetExpr` arm evaluates with the saturating-`Nat` `SExpr.eval`
   (e.g. `SSub (SLit 0) (SLit 1)` gives `0`), while `semScalar` uses the
   wrapping `SExpr.evalBV` (gives `2^64 − 1`) — the hardware's behavior.
   The two coincide exactly under the `SExpr.inRange` side condition
   (`SExpr.evalBV_eq_ofNat_eval`, `LowCT.lean`), the per-kernel no-overflow
   discipline the field kernels already carry.

A value equation quantified over arbitrary-`leafSpec` `RustExec` post-states
(the literal `hAdequacy` shape) is therefore FALSE in general, and the
theorems above are usable only by callers who can discharge `hAdequacy` for
their specific program/`leafSpec`/input range. The discharged form below
states the value leg over `semScalar` — the semantics the compiled code
actually has (the hardware wraps), and hence the strongest value claim a
front-general theorem can make. Tying that claim back to the `Nat`-model
`RustExec` value on a given kernel is the separate per-kernel `inRange`
reconciliation (point 2 above, plus a leaf-free body or a matching
`leafSpec` for point 1) — deliberately NOT smuggled into this statement.
The byte-level `RustExec` simulation survives unchanged as the existence
conjunct (`rustExecSimulatesDialect`), fed from the SAME coverage hypothesis
via `IsCoveredSCtl.toIsCoveredCtl`. -/

/-- **Front value-preservation, adequacy discharged (LowCT source semantics →
    Com[jasmin] denotation).** If the dialect front and the A1 lowering both
    succeed, the entry valuation is consistent with the entry environment, and
    the source semantics `semScalar` runs `c` to `env'` leaving `val` in the
    tracked output `name` (which the front's post-varmap resolves to the slot
    `w`), then the emitted jasmin program computes `val`:
    `jcom.denote (ctMapValD V) = ctTransTy val`.

    This is `rustToJasminCom_endToEnd`'s value leg with the adequacy edge
    **proved**, not assumed — stated over the `semScalar` waist (the literal
    `hAdequacy` shape over `RustExec` post-states is false in general; see
    the §2c header). `translateDialectControl_denote_ctl` supplies the
    post-valuation `V'` consistent with `env'` and the denotation agreement
    `com.denote V = (Com.ret (toVIRVar w)).denote V'`; `ConsistentS.lookup_eq`
    reads `val` out of the return slot; A1 transports along the jasmin
    lowering. Sublanguage: `IsCoveredSCtl` (the 19 straight-line arms with
    `srcClean` on `RScalarSetExpr`, plus `RFor` and `RIfNz`). -/
theorem semScalarToJasminCom_denote_eq
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (name : String) (w : CVar o.Γ' t) (val : ⟦t⟧)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl vm c = some o)
    (hCons : ConsistentS vm V env)
    (hSem : semScalar c env = some env')
    (hName : o.vm.lookup name = some ⟨t, w⟩)
    (hVal : env' name = some ⟨t, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = ctTransTy val := by
  obtain ⟨V', hc', hcont⟩ :=
    translateDialectControl_denote_ctl hCov vm V env env' o hCons hTrans hSem
  obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar w))
  rw [hRet] at hcom'
  obtain rfl := Option.some.inj hcom'
  rw [cryptoDialectToJasminCom_denote_eq' com V jcom hCom, hden]
  exact congrArg ctTransTy (hc'.lookup_eq hName hVal)

/-- **End-to-end (dialect front route), adequacy discharged.** The successor of
    `rustToJasminCom_endToEnd` with the `hAdequacy` hypothesis **gone**: the
    scalar front-preservation homomorphism proves the operational↔denotational
    coercion, so every remaining premise is a compilation/run success, an entry
    consistency, or an output-tracking fact.

    ## Honest guarantee (the precise spec)

    *For a single tracked output variable `name`/`w`, the emitted jasmin
    program's denotation equals the value the source `LowCT` semantics
    (`semScalar`) leaves in `name`, and a post-state valuation byte-related to
    the operational (`RustExec`) output exists — over the `IsCoveredSCtl`
    sublanguage, with no adequacy hypothesis.*

    ### GUARANTEED (proved internally)
    * **Source-value agreement on the tracked output**:
      `jcom.denote (ctMapValD V) = ctTransTy val` where `val` is what
      `semScalar` leaves in `name` (via `semScalarToJasminCom_denote_eq`,
      i.e. `translateDialectControl_denote_ctl` + A1; leaf agreement
      discharged by `dialectJasminLeafAgrees_holds`).
    * **Byte-level post-state existence**: `∃ Vb', RustStateInterp o.vm rs' Vb'`
      (the front simulation `rustExecSimulatesDialect`, fed from the same
      coverage via `IsCoveredSCtl.toIsCoveredCtl`).

    ### Scope / NOT claimed
    * The value semantics is `semScalar` (the machine-word-faithful dialect
      waist), NOT the `RustExec` `Nat` over-model — see §2c's header for the
      two divergence points (opaque leaf calls: oracle vs `CryptoTy.default`;
      `SExpr` arithmetic: saturating `SExpr.eval` vs wrapping `SExpr.evalBV`,
      the #250 boundary, reconciled per kernel under `SExpr.inRange` via
      `SExpr.evalBV_eq_ofNat_eval`). No claim is made about the `RustExec`
      value of the tracked output.
    * Single tracked output; no full memory-image equivalence.
    * `NoAliasVM` is carried inside `hInv` exactly as in
      `rustToJasminCom_endToEnd` (discharged at top level below). -/
theorem rustToJasminCom_endToEnd_unconditional
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (Vb : HVec Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (name : String) (w : CVar o.Γ' t) (val : ⟦t⟧)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl vm c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hInv : RustStateInterp vm rs Vb)
    (hCons : ConsistentS vm V env)
    (hSem : semScalar c env = some env')
    (hName : o.vm.lookup name = some ⟨t, w⟩)
    (hVal : env' name = some ⟨t, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    (∃ Vb' : HVec o.Γ', RustStateInterp o.vm rs' Vb')
      ∧ jcom.denote (ctMapValD V) = ctTransTy val :=
  ⟨rustExecSimulatesDialect vm c o N leafSpec rs rs' hCov.toIsCoveredCtl
      hTrans hExec Vb hInv,
   semScalarToJasminCom_denote_eq vm c o V env env' name w val com jcom
      hCov hTrans hCons hSem hName hVal hRet hCom⟩

/-- **Top-level end-to-end, adequacy discharged, entry hypotheses gone.** The
    top-level specialisation of `rustToJasminCom_endToEnd_unconditional`: the
    entry varmap is `VarMap.empty`, so BOTH entry invariants are built
    internally — the byte-layout `RustStateInterp` via
    `BorrowSafety.entry_interp` (discharging the `NoAliasVM` side condition)
    and the valuation consistency via `consistentS_empty`. The caller supplies
    only: the coverage, the three compilation/run successes (`hTrans`,
    `hExec`, `hSem`), the output tracking (`hName`, `hVal`), and the two
    lowering successes (`hRet`, `hCom`). -/
theorem rustToJasminCom_endToEnd_topLevel_unconditional
    {t : CryptoTy}
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (env' : SEnvScalar) (name : String) (w : CVar o.Γ' t) (val : ⟦t⟧)
    (com : Com catCryptDialect ([] : Ctx) t)
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy t))
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl VarMap.empty c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hSem : semScalar c (fun _ => none) = some env')
    (hName : o.vm.lookup name = some ⟨t, w⟩)
    (hVal : env' name = some ⟨t, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    (∃ Vb' : HVec o.Γ', RustStateInterp o.vm rs' Vb')
      ∧ jcom.denote
          (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy val :=
  rustToJasminCom_endToEnd_unconditional VarMap.empty c o N leafSpec rs rs'
    HVec.nil (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx))
    (fun _ => none) env' name w val com jcom hCov hTrans hExec
    (CatCrypt.Crypto.SecureCompilation.BorrowSafety.entry_interp rs)
    consistentS_empty hSem hName hVal hRet hCom

/-! ## 3. Structural emission corollary (A4)

Ties the printer-faithfulness (A4, `lowerComToProg_body_length`) to the front:
the emitted `JasminProg` has exactly one instruction per binding of the lowered
front CProg `jcom`. This is the front-rooted analogue of
`CompilerCorrectness.latticeNttMul_emit_wellformed`. -/

/-- **Emission well-formedness (front route, A4).** The `JasminProg` emitted
    from the lowered front program `jcom` has exactly one body instruction per
    `Com.var` binding (`Com.jOpCount jcom`). Direct instance of
    `JasminPrintCorrect.lowerComToProg_body_length`. Combined with
    `rustToJasminCom_denote_eq`'s `hCom`, this counts one instruction per
    binding the LowCT→CryptoSSA→jasmin front produced. -/
theorem rustToJasmin_emit_wellformed
    {Γ : Ctx} {t : CryptoTy}
    (name : String)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t)) :
    ((lowerComToProg name jcom).funcs.head?.map (fun fd => fd.body.length))
      = some (Com.jOpCount jcom) :=
  lowerComToProg_body_length name jcom

/-- A single function is emitted from the front program (A4). -/
theorem rustToJasmin_emit_one_func
    {Γ : Ctx} {t : CryptoTy}
    (name : String)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t)) :
    (lowerComToProg name jcom).funcs.length = 1 :=
  lowerComToProg_one_func name jcom

/-! ## 4. Smoke: the dialect front route on the `fp_add` arith kernel

The `addComCD` arith kernel of `DialectToJasminCom.SmokeTest` is a closed
`Com catCryptDialect` in A1's lowered fragment. It instantiates the A1-and-A4
tail of the dialect front composition concretely: A1 lowers it (leaf agreement
discharged internally), and A4 counts its instructions. -/

namespace Smoke

open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom.SmokeTest

/-- A1 tail on the kernel: the lowered jasmin program denotes to
    `ctTransTy (addComCD.denote W)`. Direct instance of
    `cryptoDialectToJasminCom_denote_eq'` (leaf agreement discharged). -/
theorem kernel_a1
    (W : Ctxt.Valuation (d := catCryptDialect) [.sword 64, .sword 64]) :
    SmokeTest.addComJ.denote (ctMapValD W) = ctTransTy (SmokeTest.addComCD.denote W) :=
  cryptoDialectToJasminCom_denote_eq' SmokeTest.addComCD W SmokeTest.addComJ
    (Option.some_get SmokeTest.addComCD_isSome)

/-- A4 tail on the kernel: the emitted `JasminProg` has one body instruction per
    `Com.var` binding. -/
theorem kernel_a4 :
    ((lowerComToProg "fp_add_arith_d" SmokeTest.addComJ).funcs.head?.map
      (fun fd => fd.body.length)) = some (Com.jOpCount SmokeTest.addComJ) :=
  lowerComToProg_body_length "fp_add_arith_d" SmokeTest.addComJ

end Smoke

end CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
