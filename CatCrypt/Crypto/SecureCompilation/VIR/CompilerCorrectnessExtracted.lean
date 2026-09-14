/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RustStateSubstrate
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintCorrect
public import CatCrypt.Crypto.SecureCompilation.BorrowSafety

/-!
# Extraction-rooted compiler correctness on the dialect front

`CompilerCorrectness.lean` states the optimizer and backend half of the
correctness chain for the lattice NTT-multiplication route
(`latticeNttMul_compile_correct`). This file states the front-rooted
analogue: it starts from `LowCT` (the output of extraction) and chains the
front stages into one statement. The front is:

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
  invariant per VarMap binding).

* **A1 (catCryptDialect → Com[jasmin])** —
  `DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`. This is a
  **denotational equality**: if the front succeeds
  (`cryptoDialectToJasminCom com = some jcom`), then the lowered jasmin program
  denotes to the value transport `jcom.denote (ctMapValD W) = ctTransTy (com.denote W)`.
  Leaf agreement is proved inside the theorem
  (`dialectJasminLeafAgrees_holds`), so no leaf-agreement hypothesis is
  carried; both sides are plain values, with no `SPComp` purity read-off.

## The adapter between the two theorems

The front simulation relates the *state* (`RustStateInterp`, over
`HVec o.Γ'`), while A1 relates the *denotation* (over a `Ctxt.Valuation`). The
two are joined by the **operational↔denotational adequacy** of the dialect
front: the dialect program's denotational value `com.denote W` equals the value
the source `LowCT` leaves in the tracked variable `w`. §2b carries it as the
explicit hypothesis `hAdequacy`; §2c states the value leg over the source
waist semantics `semScalar` instead and derives the needed agreement from the
scalar front-preservation homomorphism
(`TranslateDialectScalar.translateDialectControl_denote_ctl`). §2c's header
explains why the value leg is stated over `semScalar` and not over a
`leafSpec`-oracle `RustExec` value.

## Trust base (the parametric edges)

As in `CompilerCorrectness.lean`, the chain ends at explicit edges:

1. **extraction → LowCT** — `haxToLowCT_simulates_full`, whose hypotheses are
   per-protocol obligations. This edge is not used in this file.
2. **LowCT → catCryptDialect** — `rustExecSimulatesDialect` (a *simulation*;
   the state invariant `RustStateInterp` is the byte-layout relation preserved).
3. **catCryptDialect→jasmin adequacy** — proved in §2c over the
   `IsCoveredSCtl` sublanguage: the dialect program's denotation equals the
   machine-word source-semantics value (`semScalar`), by the scalar
   front-preservation homomorphism. Two edges remain outside the statement:
   the per-kernel `SExpr.inRange` reconciliation with the `Nat`-model
   `RustExec`, and the opaque-leaf `leafSpec` convention (§2c header). §2b's
   `hAdequacy`-parametric forms serve callers outside that sublanguage.
4. **semantic printer faithfulness** — only *structural* faithfulness is proved
   here (A4, `JasminPrintCorrect`, instruction counts); the
   `JasminProg → .jazz` text and parse step is not covered.
5. **`.jazz → x86`** — not covered by the theorems in this file.

Leaf agreement between the dialect and the jasmin lowering is proved
unconditionally by `DialectToJasminComCorrect.dialectJasminLeafAgrees_holds`
and is not a parametric edge of the front lowering.

The file contains no `sorry`; the remaining gaps are the explicit hypotheses
listed above.
-/

@[expose] public section

set_option autoImplicit true -- SSA IR front: many context/type variables

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
-- `ctTransTy` (and its identity/default lemmas) are declared in `JasminValTransport.lean`
-- under the `CryptoToJasminComCorrect` namespace.
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

The front simulation
(`CryptoDialectRustSim.rustExecSimulatesDialect`, for the state witness `V'`)
is chained with A1 (`cryptoDialectToJasminCom_denote_eq'`, for the
denotation). Leaf agreement is proved inside A1, so no leaf-agreement
hypothesis is carried. -/

/-- **Extraction-rooted front correctness (LowCT → Com[catCryptDialect] →
    Com[jasmin]), loose form.**

    Composes the two front stages into a conjunction. Given:

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
    form below ties them. Leaf agreement is proved inside A1 by
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
front's post-state. The theorem below ties the two halves together:

* the front simulation is applied inside the proof —
  `rustExecSimulatesDialect` supplies the post-state `V'`;
* the conclusion equates the jasmin program's denotation with the
  `ctTransTy`-transport of the LowCT post-state's value for `w`
  (`w.lookup V'`).

The additional hypothesis is `hAdequacy`: for every post-state `V'` related to
`rs'`, the dialect program's denotation `com.denote W` equals `w.lookup V'`.
This is the **operational↔denotational adequacy** of the dialect front, that
`Com.denote` (the value semantics A1 uses) agrees with the source semantics on
the value left in `w`. §2c derives the corresponding statement from
`TranslateDialectScalar.translateDialectControl_denote_ctl`, over the source
waist semantics `semScalar`, and states the chain without an adequacy
hypothesis. The `hAdequacy`-parametric forms in this section serve callers
outside the `IsCoveredSCtl` sublanguage, and callers whose value claim is
stated for a specific `leafSpec` oracle, which §2c does not cover. -/

/-- **End-to-end (dialect front route), fused.** Under `hCov`, `hTrans`,
    `hExec`, `hInv`, `hCom` and the operational↔denotational adequacy
    hypothesis `hAdequacy`: there is a post-state valuation `V'` byte-related
    to the LowCT output `rs'`, and the emitted jasmin program's denotation is
    the `ctTransTy`-transport of that post-state's value for `w`.

    ## Guarantee

    *Assuming the dialect program's denotational value equals the value in
    every post-state related to `rs'` (`hAdequacy`), then for a single tracked
    output variable `w` the emitted jasmin program's denotation equals the
    value the source `LowCT` leaves in `w`. This is output-value agreement
    under a byte-layout invariant, not full functional or memory equivalence,
    and the adequacy edge is a hypothesis.*

    ### Proved in the theorem
    * **Single-output value agreement on the tracked variable `w`.** The
      conclusion equates `jcom.denote (ctMapValD W)` with `ctTransTy (w.lookup V')`
      — the value of the *one* chosen output variable `w` in the related
      post-state `V'`. The front simulation (`rustExecSimulatesDialect`) chains
      with the A1 lowering (`cryptoDialectToJasminCom_denote_eq'`, proved by
      program induction).
    * Existence of a post-state valuation `V'` byte-related to `rs'` (this is
      what the front simulation delivers — *existence*, not value).
    * **Leaf agreement** is proved inside A1 via
      `dialectJasminLeafAgrees_holds` (arith/const leaves agree by computation,
      `extCall` leaves on the opaque canonical default).

    ### Hypotheses supplied by the caller
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

    ### NoAliasVM restriction (carried inside `hInv`)
    `hInv : RustStateInterp vm rs V` is a byte-layout invariant whose `noAlias`
    **field** is `NoAliasVM vm`. It requires `vm.lookup` to be injective on
    names, so `hInv` cannot hold for an aliasing seed `vm`. The restriction
    does not appear in the signature; it is a field of the `RustStateInterp`
    structure.

    ### Not claimed
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
    so the entry `RustStateInterp` hypothesis, which carries `NoAliasVM` in its
    `noAlias` field, is built inside the proof via
    `BorrowSafety.entry_interp` (whose `noAlias` field is `noAlias_empty`). The
    caller supplies no `hInv` and no aliasing hypothesis; the `NoAliasVM` side
    condition is discharged for translations that start from `VarMap.empty`.
    `hAdequacy` remains a hypothesis.

    The non-top-level `rustToJasminCom_endToEnd` keeps `hInv` because it is
    parametric over an arbitrary entry varmap `vm`, where `hInv` carries the
    full byte-layout invariant (not only `NoAliasVM`) and is a precondition. -/
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

/-! ## 2c. End-to-end without `hAdequacy`

`rustToJasminCom_endToEnd` above carries the operational↔denotational adequacy
of the dialect front as the hypothesis `hAdequacy`. The scalar
front-preservation homomorphism
(`TranslateDialectScalar.translateDialectControl_denote_ctl`) supplies an
adequacy statement over `semScalar`: for any `IsCoveredSCtl`-covered body,
front success and source-semantics success give a post-valuation `V'`
consistent with the source post-environment, together with per-tail
denotation agreement. The theorems below chain it with A1. Their premises are
coverage, compilation and run successes, entry consistency, and output
tracking; they carry no adequacy hypothesis.

**Which source semantics the value claim is stated over.** The homomorphism
runs over `semScalar`, the pure env-level **machine-word-faithful** semantics
of the covered `LowCT` arms, whose per-op waist is exactly what the emitted
dialect op denotes by (opaque leaves ↦ `CryptoTy.default`, dynamic array ops
↦ `memGetDyn`/`memSetDyn`, `SExpr` assignments ↦ the wrapping-u64
`SExpr.evalBV`, `RFor` ↦ the per-trip fold, `RIfNz` ↦ the φ-merge select).
It differs from `RustExec` at the following two points:

1. **opaque leaf calls** — `RustExec` resolves each `RCall` through the
   `leafSpec` **oracle** (`leafSpec.call …`), while the dialect — and hence
   the compiled jasmin program — denotes an opaque leaf to
   `CryptoTy.default`;
2. **`SExpr` arithmetic** — `RustExec`'s
   `scalarSetExpr` arm evaluates with the saturating-`Nat` `SExpr.eval`
   (e.g. `SSub (SLit 0) (SLit 1)` gives `0`), while `semScalar` uses the
   wrapping `SExpr.evalBV` (gives `2^64 − 1`) — the hardware's behavior.
   Under the `SExpr.inRange` side condition, `SExpr.evalBV` equals the
   64-bit truncation of `SExpr.eval` (`SExpr.evalBV_eq_ofNat_eval`,
   `LowCT.lean`); `inRange` is a per-kernel no-overflow condition.

A value equation quantified over arbitrary-`leafSpec` `RustExec` post-states
(the shape of `hAdequacy`) therefore does not hold in general, and the
theorems above apply only where the caller can discharge `hAdequacy` for a
specific program, `leafSpec` and input range. The form below states the value
leg over `semScalar`, whose `SExpr` arithmetic wraps as the hardware does.
Relating that value to the `Nat`-model `RustExec` value on a given kernel is a
separate per-kernel obligation (the `inRange` condition of point 2, and a
leaf-free body or a matching `leafSpec` for point 1) and is not part of these
statements. The byte-level `RustExec` simulation appears as the existence
conjunct (`rustExecSimulatesDialect`), obtained from the same coverage
hypothesis via `IsCoveredSCtl.toIsCoveredCtl`. -/

/-- **Front value-preservation without an adequacy hypothesis (LowCT source semantics →
    Com[jasmin] denotation).** If the dialect front and the A1 lowering both
    succeed, the entry valuation is consistent with the entry environment, and
    the source semantics `semScalar` runs `c` to `env'` leaving `val` in the
    tracked output `name` (which the front's post-varmap resolves to the slot
    `w`), then the emitted jasmin program computes `val`:
    `jcom.denote (ctMapValD V) = ctTransTy val`.

    This is the value leg of `rustToJasminCom_endToEnd` without an adequacy
    hypothesis, stated over the `semScalar` waist rather than over `RustExec`
    post-states (see the §2c header). `translateDialectControl_denote_ctl`
    supplies the post-valuation `V'` consistent with `env'` and the denotation
    agreement `com.denote V = (Com.ret (toVIRVar w)).denote V'`;
    `ConsistentS.lookup_eq` reads `val` out of the return slot; A1 transports
    along the jasmin lowering. Sublanguage: `IsCoveredSCtl` (the straight-line
    arms of `IsCoveredS`, plus `RFor` and `RIfNz`). -/
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

/-- **End-to-end (dialect front route), without an adequacy hypothesis.** The
    counterpart of `rustToJasminCom_endToEnd` without `hAdequacy`: the scalar
    front-preservation homomorphism relates the dialect denotation to
    `semScalar`, so the premises are coverage (`hCov : IsCoveredSCtl c`),
    compilation and run successes, entry invariants (`hInv`, `hCons`), and
    output tracking.

    ## Guarantee

    *For a single tracked output variable `name`/`w`, the emitted jasmin
    program's denotation equals the value the source `LowCT` semantics
    (`semScalar`) leaves in `name`, and a post-state valuation byte-related to
    the operational (`RustExec`) output exists, over the `IsCoveredSCtl`
    sublanguage.*

    ### Proved in the theorem
    * **Source-value agreement on the tracked output**:
      `jcom.denote (ctMapValD V) = ctTransTy val` where `val` is what
      `semScalar` leaves in `name` (via `semScalarToJasminCom_denote_eq`,
      i.e. `translateDialectControl_denote_ctl` + A1; leaf agreement
      discharged by `dialectJasminLeafAgrees_holds`).
    * **Byte-level post-state existence**: `∃ Vb', RustStateInterp o.vm rs' Vb'`
      (the front simulation `rustExecSimulatesDialect`, fed from the same
      coverage via `IsCoveredSCtl.toIsCoveredCtl`).

    ### Scope and claims not made
    * The value semantics is `semScalar` (the machine-word-faithful dialect
      waist), not the `RustExec` `Nat` model; see §2c's header for the
      two divergence points (opaque leaf calls: oracle vs `CryptoTy.default`;
      `SExpr` arithmetic: saturating `SExpr.eval` vs wrapping `SExpr.evalBV`,
      which agree under `SExpr.inRange` by `SExpr.evalBV_eq_ofNat_eval`). No
      claim is made about the `RustExec` value of the tracked output.
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

/-- **Top-level end-to-end, without adequacy or entry hypotheses.** The
    top-level specialisation of `rustToJasminCom_endToEnd_unconditional`: the
    entry varmap is `VarMap.empty` and the source entry environment is empty,
    so both entry invariants are built inside the proof: the byte-layout
    `RustStateInterp` via
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
front program `jcom`. This is the front-rooted analogue of
`CompilerCorrectness.latticeNttMul_emit_wellformed`. -/

/-- **Emission well-formedness (front route, A4).** The `JasminProg` emitted
    from the lowered front program `jcom` has exactly one body instruction per
    `Com.var` binding (`Com.jOpCount jcom`). Direct instance of
    `JasminPrintCorrect.lowerComToProg_body_length`. Combined with
    `rustToJasminCom_denote_eq`'s `hCom`, this counts one instruction per
    binding the LowCT → catCryptDialect → jasmin front produced. -/
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
proved inside A1), and A4 counts its instructions. -/

namespace Smoke

open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom.SmokeTest

/-- A1 tail on the kernel: the lowered jasmin program denotes to
    `ctTransTy (addComCD.denote W)`. Direct instance of
    `cryptoDialectToJasminCom_denote_eq'` (leaf agreement proved inside A1). -/
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
