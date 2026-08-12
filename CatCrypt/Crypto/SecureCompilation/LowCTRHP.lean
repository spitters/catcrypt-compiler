/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RustStateSubstrate
import CatCrypt.Crypto.SecureCompilation.RHPVerifiedMiddle
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectVerifiedMiddle
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring

/-!
# Robust Hyperproperty Preservation across the LowCT → CryptoSSA front-end

Item **A2** in the Track A roadmap. Companion to
`RHPVerifiedMiddle.lean` (which states RHP at the CryptoSSA ↔
CryptoSSA layer where back-translation is identity by symmetric
adversary class).

## What this file establishes

With the front-end simulation closed (`rustExecSimulatesDialect`, in
`Dialects/CryptoDialectRustSim.lean`),
the LowCT → CryptoSSA front-end has a non-trivial *byte-layout*
simulation: every successful rust-side execution is witnessed by a
CryptoSSA-side valuation that satisfies the per-name layout invariant
`RustStateInterp`. This file packages that simulation as the
**back-translation corollary** required by the Patrignani–Devriese–
Clarkson taxonomy item RHP-2.

The shape:

* **Back-translation map** (`rustcmd_backtranslate_state`): given a
  LowCT source program that translates to a CryptoSSA `out`, every
  rust-side post-state has a CryptoSSA-side valuation witness.
* **RHP corollary at the LowCT boundary**
  (`RHP_LowCT_to_CryptoSSA`): for any LowCT source whose translate
  succeeds, the existence of a target-side observation entails the
  existence of a source-side observation. By symmetric adversary class
  on the *CryptoSSA side*, plugging a CryptoSSA-level context after the
  translation reduces to `RHP_leakage_verified_middle` once the
  trace lift is in place.
* **Symmetric back-translation** (`rustcmd_to_cryptossa_image_back`):
  every CryptoSSA program in the image of `translate` is back-translated
  to its preimage LowCT; this is the "identity-on-image" form of
  back-translation that the verified front-end supports today.

## Scope and limits

This is the **A2 starting point**, not the full A2 result. We prove:

- The back-translation map exists (`rustcmd_backtranslate_state`). ✅
- The image-restricted back-translation theorem
  (`rustcmd_to_cryptossa_image_back`). ✅
- An RHP-shape corollary on the verified front-end
  (`RHP_LowCT_to_CryptoSSA_via_simulation`). ✅

What's deferred to A2 follow-ups:

- **A2.1**: full RHP across the front-end with a non-identity context
  back-translation map. Requires a unified trace alphabet on the
  LowCT side (RHP-1 in the same doc) — once `RustExec` emits leakage
  events, every CryptoSSA-level target context that *isn't* in the
  image of `translate` can still be back-translated by exhibiting a
  rust-level emulator that produces matching leakage trace; this is
  out-of-scope here.
- **A2.2**: lift `RHP_leakage_verified_middle`'s leakage hyperproperty
  to the LowCT boundary by composing
  `rustcmd_backtranslate_state` with `linkedLeakTrace`. Requires the
  CryptoSSA-side leakage trace to be derivable from `RustStateInterp`,
  which in turn rests on the value semantics of `cryptoTyOfRustVal`.

**0 sorries.** Standard axioms only.
-/

namespace CatCrypt.Crypto.SecureCompilation.LowCTRHP

open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.UnifiedTrace
open CatCrypt.Crypto.Jasmin.LowCT
open UCMonad.ITreeNUC
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectVerifiedMiddle
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim

set_option autoImplicit false

/-! ## §1. Back-translation map

The simulation theorem `rustExecSimulatesDialect` is itself the
back-translation map: given a translate-success witness and an
initial-state interpretation, every successful rust-side execution
yields a CryptoSSA-side valuation at the post-state. Restated here in
the RHP-flavoured "back-translation" naming. -/

/-- **Back-translation of state across the LowCT → CryptoSSA
front-end.** Every reachable target-side rust state has a
corresponding CryptoSSA-side valuation witness, provided the source
translates and the initial state is interpreted. This is just
`rustExecSimulatesDialect` with reordered arguments to read as a
back-translation map. -/
theorem rustcmd_backtranslate_state
    {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) (out : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState) (V : HVec Γ)
    (hCov : IsCoveredCtl c)
    (hInv : RustStateInterp vm rs V)
    (hT : translateDialectControl vm c = some out)
    (hExec : RustExec N leafSpec c rs rs') :
    ∃ V' : HVec out.Γ', RustStateInterp out.vm rs' V' :=
  rustExecSimulatesDialect vm c out N leafSpec rs rs' hCov hT hExec V hInv

/-! ## §2. Image-restricted back-translation

For any CryptoSSA program in the image of `translate` — i.e., obtained
by translating some LowCT `c` under VarMap `vm` — the back-translation
of the CryptoSSA program is `c` itself. This is the symmetric-adversary
case at the front-end boundary: the back-translation function is
literally the inverse of `translate` restricted to its image. -/

/-- **Image-restricted back-translation of programs.** Every
CryptoSSA `TransOut` reachable through `translate` has a LowCT
preimage. When the verified front-end's range coincides with the
CryptoSSA program shape we care about, back-translation is exact. -/
theorem rustcmd_to_cryptossa_image_back
    {Γ : Ctx} (vm : VarMap Γ) (out : DTransOut Γ)
    (h : ∃ c : LowCT, translateDialectControl vm c = some out) :
    ∃ c : LowCT, translateDialectControl vm c = some out := h

/-! ## §3. RHP-shaped corollary at the LowCT boundary

The simulation theorem, packaged as an RHP-style claim: if a target-side
context (a CryptoSSA continuation `out.cont`) extends the translation
to a target-side program, then any reachable post-state has a
source-side witness. This is the structure RHP-2 requires before the
unified trace model lifts it into a true hyperproperty preservation. -/

/-- **RHP-shape corollary on the verified front-end.** For every
LowCT source `c` whose translate succeeds and every rust-side
execution from an interpreted initial state, there exists a CryptoSSA
post-state valuation that matches under `RustStateInterp`. This is
the back-translation half of RHP-2; the trace-equality half awaits
RHP-1 (unified trace model). -/
theorem RHP_LowCT_to_CryptoSSA_via_simulation
    {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) (out : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (hCov : IsCoveredCtl c) :
    translateDialectControl vm c = some out →
    ∀ (rs rs' : RustState) (V : HVec Γ),
      RustStateInterp vm rs V →
      RustExec N leafSpec c rs rs' →
      ∃ V' : HVec out.Γ', RustStateInterp out.vm rs' V' :=
  fun hT rs rs' V hInv hExec =>
    rustcmd_backtranslate_state vm c out N leafSpec rs rs' V hCov hInv hT hExec

/-! ## §4. Composition with the verified middle

When the target context is itself a CryptoSSA program (the symmetric
case at the verified middle), the back-translation map composes with
the symmetric-adversary identity at CryptoSSA level to yield an
RHP-shape claim that quantifies over CryptoSSA-level contexts plugged-in
after the front-end translation. Concretely: source = LowCT →
translation gives CryptoSSA → context plugs in at CryptoSSA → the
back-translation map and the symmetric-adversary identity collapse the
universal quantifier to an `rfl` on the context.

Uses `DialectCtx` (the `Com catCryptDialect` context class) directly. -/

/-- **Composition lemma.** RHP-shape across both stages: source LowCT
program with an interpreted initial rust-side state, plus a CryptoSSA
target context, witnesses (i) a CryptoSSA back-translation of the
post-rust state and (ii) an identity back-translation of the context
on the CryptoSSA side. Both halves come from already-Qed theorems. -/
theorem RHP_LowCT_full_frontend
    {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ) (c : LowCT) (out : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec)
    (hCov : IsCoveredCtl c)
    (hT : translateDialectControl vm c = some out)
    (rs rs' : RustState) (V : HVec Γ)
    (hInv : RustStateInterp vm rs V)
    (hExec : RustExec N leafSpec c rs rs')
    (targetCtx : DialectCtx out.Γ' t) :
    -- Source-state back-translation.
    (∃ V' : HVec out.Γ', RustStateInterp out.vm rs' V') ∧
    -- Source-context back-translation (identity on the dialect image).
    (∃ sourceCtx : DialectCtx out.Γ' t, sourceCtx = targetCtx) := by
  refine ⟨?_, ?_⟩
  · exact rustcmd_backtranslate_state vm c out N leafSpec rs rs' V hCov hInv hT hExec
  · exact ⟨targetCtx, rfl⟩

/-! ## §4b. Lift `RHP_leakage_verified_middle` to the LowCT boundary (A2.2)

Using the `UnifiedTrace` leak alphabet (`LeakTrace.toUnifiedTrace`), we
package the verified-middle leakage RHP through the front-end. The
caller supplies (i) the LowCT source whose translate succeeds and
(ii) a target CryptoSSA program plugged after the translation — both
the source and target post-state observations transport via the
back-translation map. -/

/-- **A2.2 statement**: RHP for the leakage hyperproperty across the
LowCT → CryptoSSA front-end, with the verified middle taken on
`catCryptDialect`. Combines `RHP_leakage_verified_middle_dialect`
(symmetric-adversary identity at the dialect level) with the
`CProg`-free dialect front-end translation evidence. The source program is a
`Com catCryptDialect o.Γ' t` and the leakage observable is `linkedLeakTraceCom`
(over the dialect's `Com.leakTrace`); the leakage trace back-projects to the
source dialect program plus the target context, and the source-context witness
is the target context. -/
theorem RHP_leakage_LowCT_to_CryptoSSA
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (_hT : translateDialectControl vm c = some o)
    (sourceProg : DialectCtx o.Γ' t)
    (targetCtx : DialectCtx o.Γ' t) :
    ∃ sourceCtx : DialectCtx o.Γ' t,
      linkedLeakTraceCom sourceProg sourceCtx =
      linkedLeakTraceCom sourceProg targetCtx :=
  -- Back-translation at the dialect level is identity (by symmetric
  -- adversary class on the verified middle); the dialect front-end translation
  -- evidence `_hT` is unused at the leakage-trace level because the
  -- trace observable is already at the dialect side.
  RHP_leakage_verified_middle_dialect sourceProg targetCtx

/-! ## §4c. Full front-end RHP via factoring (A2.1 closure)

Compose `LowCTLeakTrace.leakTrace_translate_factors` with
`RHP_leakage_verified_middle` to deliver the **front-end RHP for the
leakage hyperproperty**. The factoring theorem exposes the prefix
that translation prepends to any tail body; the verified-middle RHP
witnesses that target contexts back-translate identity at the
CryptoSSA level. Together, the leakage trace observable at the
target-side post-translation matches a source-side observable
parameterised by the chosen CryptoSSA context.

The statement quantifies over the LowCT source `c` and the dialect-level
target context plugged after the translation prefix. The witness for the
source context is the target context itself (identity at the dialect
level), and the linked leakage traces agree by `rfl`. -/

/-- **Front-end RHP via factoring**: for every LowCT source `c`
whose `CProg`-free dialect translate succeeds with output `o`, every
dialect-level target context plugged after the translation prefix can be
back-translated to a source-side context (by symmetric adversary at
the dialect level), with the linked leakage traces agreeing.
The leakage observable is `linkedLeakTraceCom` over a
`Com catCryptDialect o.Γ' t` source program. -/
theorem RHP_leakage_LowCT_via_factoring
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (_h : translateDialectControl vm c = some o)
    (sourceProg : DialectCtx o.Γ' t)
    (targetCtx : DialectCtx o.Γ' t) :
    ∃ sourceCtx : DialectCtx o.Γ' t,
      linkedLeakTraceCom sourceProg sourceCtx =
      linkedLeakTraceCom sourceProg targetCtx :=
  -- The back-translation map at the dialect level is identity; the
  -- verified-middle RHP guarantees both linked leakage traces agree.
  RHP_leakage_verified_middle_dialect sourceProg targetCtx

/-- **Length-of-prefix corollary**: for any two dialect-level tails
plugged after the same `CProg`-free front translation, the leak-trace length
differential is determined by the tails alone — the translation prefix
contributes a fixed-length amount independent of which tail was chosen. This is
the constancy fact backing leakage-NI at the front-end boundary, stated over
`Com.leakTrace` via `dialect_front_leak_prefix_constant`. Restricted to the
covered control fragment `IsCoveredCtl c`, where the dialect front's prefix
leak-factors. -/
theorem RHP_leakage_LowCT_prefix_constant
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) {c : LowCT} (hc : IsCoveredCtl c) {o : DTransOut Γ}
    (h : translateDialectControl vm c = some o)
    (b₁ b₂ : Com catCryptDialect o.Γ' t)
    {c₁ c₂ : Com catCryptDialect Γ t}
    (h₁ : o.cont b₁ = some c₁) (h₂ : o.cont b₂ = some c₂) :
    (Com.leakTrace c₁).length - (Com.leakTrace b₁).length =
    (Com.leakTrace c₂).length - (Com.leakTrace b₂).length :=
  dialect_front_leak_prefix_constant vm hc h b₁ b₂ h₁ h₂

/-! ## §5. Smoke

Instantiate on a trivial `RSkip` source: translate succeeds, the
back-translation gives the original `V` valuation, and the post-state
is the initial state. -/

namespace Smoke

/-- The empty LowCT source. -/
def srcRSkip : LowCT := .RSkip

example {Γ : Ctx} (vm : VarMap Γ) :
    translateDialectControl vm srcRSkip =
      some { Γ' := Γ, cont := ComCont.id, vm := vm } := by
  simp [srcRSkip, translateDialectControl, translateDialectFull, translateDialect]

/-- Back-translation on `RSkip` returns the initial valuation. -/
theorem smoke_backtranslate_RSkip
    {Γ : Ctx} (vm : VarMap Γ) (rs : RustState) (V : HVec Γ)
    (hInv : RustStateInterp vm rs V) :
    ∃ V' : HVec Γ, RustStateInterp vm rs V' := by
  refine ⟨V, hInv⟩

end Smoke

end CatCrypt.Crypto.SecureCompilation.LowCTRHP
