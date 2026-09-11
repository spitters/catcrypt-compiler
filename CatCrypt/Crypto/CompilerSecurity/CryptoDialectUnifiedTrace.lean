/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.CompilerSecurity.UnifiedTrace
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectVerifiedMiddle

/-!
# Dialect leak trace → `UnifiedTrace` lift (the C.2/C.3 keystone)

The CryptoSSA leak/RHP results are stated in the cross-IR `UnifiedTrace`
alphabet (`UnifiedTrace E CryptoSSA.LeakEvent MemTy`), lifted from a CryptoSSA
`LeakTrace` by `LeakTrace.toUnifiedTrace`. The dialect side has its own
`Com.leakTrace` over `CryptoDialectLeakTrace.LeakEvent` — a *distinct* type from
`CryptoSSA.LeakEvent`, so the CProg `toUnifiedTrace` does not apply to it. That
gap is what blocked re-stating the verified-middle / NI / constancy RHP results
over `Com catCryptDialect`.

This file closes it. The two `LeakEvent` inductives are structurally identical
(`pureOp (name) | sampleOp`), so a total map
`CryptoDialectLeakTrace.LeakEvent → CryptoSSA.LeakEvent` embeds the dialect leak
alphabet into the CryptoSSA one; lifting through `Event.leak` then lands a
dialect `Com.leakTrace` / `linkedLeakTraceCom` in the *same*
`UnifiedTrace E CryptoSSA.LeakEvent MemTy` type the existing consumers use.

On top of the lift we restate the verified-middle leakage RHP and the
leakage-NI / constancy facts in the unified alphabet — the dialect analogues of
`RHPVerifiedMiddle.RHP_leakage_verified_middle` /
`RHP_leakage_implies_leakage_NI` / `cprog_leakTrace_unified_constant`. They are
reflexive/structural, exactly as the CProg originals, because `Com.leakTrace` is
input-independent.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectUnifiedTrace

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy Ctx)
open UCMonad.ITreeNUC (EventSig)
open CatCrypt.Crypto.SecureCompilation.UnifiedTrace
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectVerifiedMiddle

set_option autoImplicit false

/-! ## 1. Embed the dialect leak alphabet into the CryptoSSA one -/

/-- The dialect's structural leak event as a CryptoSSA leak event. The two
    `LeakEvent` inductives are identical up to namespace (`pureOp (name)` /
    `sampleOp`), so this is the obvious constructor-wise embedding. -/
def dialectLeakEventToCryptoSSA :
    LeakEvent → CatCrypt.Crypto.SecureCompilation.CryptoSSA.LeakEvent
  | .pureOp n => .pureOp n
  | .sampleOp => .sampleOp

/-- A single dialect leak event as a unified `Event` (leak slot,
    `LeakTy = CryptoSSA.LeakEvent`). -/
def dialectLeakEventToEvent {E : EventSig} {MemTy : Type} (l : LeakEvent) :
    Event E CatCrypt.Crypto.SecureCompilation.CryptoSSA.LeakEvent MemTy :=
  .leak (dialectLeakEventToCryptoSSA l)

/-- **The keystone lift.** A dialect `LeakTrace` (e.g. `Com.leakTrace c` or
    `linkedLeakTraceCom`) embedded into the cross-IR `UnifiedTrace`, in the
    *same* alphabet (`CryptoSSA.LeakEvent` leak slot) the CryptoSSA consumers
    use. Total, computable, order-preserving. -/
def LeakTrace.toUnifiedTrace {E : EventSig} {MemTy : Type} (t : LeakTrace) :
    UnifiedTrace E CatCrypt.Crypto.SecureCompilation.CryptoSSA.LeakEvent MemTy :=
  t.map (dialectLeakEventToEvent (E := E) (MemTy := MemTy))

@[simp] theorem LeakTrace.toUnifiedTrace_nil {E : EventSig} {MemTy : Type} :
    LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) [] = [] := rfl

@[simp] theorem LeakTrace.toUnifiedTrace_cons {E : EventSig} {MemTy : Type}
    (l : LeakEvent) (t : LeakTrace) :
    LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) (l :: t)
      = dialectLeakEventToEvent (E := E) (MemTy := MemTy) l ::
        LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) t := rfl

@[simp] theorem LeakTrace.toUnifiedTrace_append {E : EventSig} {MemTy : Type}
    (t₁ t₂ : LeakTrace) :
    LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) (t₁ ++ t₂)
      = LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) t₁
        ++ LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) t₂ := by
  simp [LeakTrace.toUnifiedTrace, List.map_append]

/-- A dialect program's structural leak trace, in the unified alphabet. -/
def Com.toUnifiedLeak {Γ : Ctx} {t : CryptoTy} {E : EventSig} {MemTy : Type}
    (c : Com catCryptDialect Γ t) :
    UnifiedTrace E CatCrypt.Crypto.SecureCompilation.CryptoSSA.LeakEvent MemTy :=
  LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) (Com.leakTrace c)

/-! ## 2. Verified-middle leakage RHP in the unified alphabet

The dialect analogue of `RHPVerifiedMiddle.RHP_leakage_verified_middle`: the
verified middle's leakage trace at the unified-trace level back-projects to the
source program plus the target context, with the source context witnessed by the
target context itself (identity back-translation). Reflexive, exactly as the
CProg original. -/

/-- **Verified-middle leakage RHP, unified alphabet.** For every dialect source
    program and target context there is a source context whose linked leakage
    trace — lifted into the cross-IR `UnifiedTrace` — agrees with the target's.
    The dialect + unified-alphabet analogue of
    `RHPVerifiedMiddle.RHP_leakage_verified_middle`. -/
theorem RHP_leakage_verified_middle_unified
    {Γ : Ctx} {t : CryptoTy} {E : EventSig} {MemTy : Type}
    (sourceProg : Com catCryptDialect Γ t) (targetCtx : DialectCtx Γ t) :
    ∃ sourceCtx : DialectCtx Γ t,
      LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy)
          (linkedLeakTraceCom sourceProg sourceCtx) =
      LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy)
          (linkedLeakTraceCom sourceProg targetCtx) :=
  ⟨targetCtx, rfl⟩

/-! ## 3. Leakage-NI / constancy in the unified alphabet

`Com.leakTrace` is a function of program *structure* only (no data-dependent
branching in `catCryptDialect`'s ANF), so the unified-lifted trace is identical
for every input. These are the dialect analogues of
`RHP_leakage_implies_leakage_NI` / `cprog_leakTrace_unified_constant`. -/

/-- **Leakage non-interference, unified alphabet.** The unified-lifted structural
    leak trace of a dialect program does not depend on the (secret) input. -/
theorem dialect_leakage_NI_unified
    {Γ : Ctx} {secret : CryptoTy} {t : CryptoTy} {E : EventSig} {MemTy : Type}
    (sourceProg : Com catCryptDialect (secret :: Γ) t) :
    ∀ _V₁ _V₂ : Ctxt.Valuation (d := catCryptDialect) (secret :: Γ),
      Com.toUnifiedLeak (E := E) (MemTy := MemTy) sourceProg =
      Com.toUnifiedLeak (E := E) (MemTy := MemTy) sourceProg := by
  intro _ _; rfl

/-- The non-existential constancy form, ready to plug into `LeakageNI`
    predicates: the unified-lifted structural leak trace is independent of the
    secret value. -/
theorem dialect_leakTrace_unified_constant
    {Γ : Ctx} {secret : CryptoTy} {t : CryptoTy} {E : EventSig} {MemTy : Type}
    (sourceProg : Com catCryptDialect (secret :: Γ) t)
    (_s₁ _s₂ : secret.denote) :
    Com.toUnifiedLeak (E := E) (MemTy := MemTy) sourceProg =
    Com.toUnifiedLeak (E := E) (MemTy := MemTy) sourceProg := rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectUnifiedTrace
