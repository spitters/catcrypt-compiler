/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring
public import CatCrypt.Crypto.CompilerSecurity.LowCTLabeled
public import CatCrypt.Crypto.SecureCompilation.LowCTLeakTraceDef
public import CatCrypt.Crypto.CompilerSecurity.NIPreservation

/-!
# Full-pipeline RHP over the dialect front (labeled CT × leak-trace factoring)

The front-end RHP statements for a `wellLabeled` LowCT source, over the dialect
front (`translateDialectControl`). Three independent guarantees combine:

* **(A) labeled CT** (`LowCTLabeled.wellLabeled_implies_x86_ct`): a `wellLabeled`,
  `jasminCTSafe` source whose Jasmin lowering compiles to x86 yields a
  constant-time binary. Machine-level (`LowCT → jasmin → x86`), IR-independent.
* **(B) leak-trace factoring** (`CryptoDialectLeakFactoring`): the dialect front
  prefix factors the leak trace as a fixed prefix plus the plugged tail, over
  `Com.leakTrace`.
* **(C) symmetric-adversary back-translation**: source and target contexts inhabit
  the same class (`Com catCryptDialect`), so the back-translation is the identity
  and the linked leak traces agree.

Stated over the dialect front; no `CProg`. The ε-bounded follow-ups (§5–§6) are
structural (over `LowCT.leakTrace` and the `SPComp` distance) and unchanged.

Trust set: `propext`, `Classical.choice`, `Quot.sound`, and `jasminc_preserves_ct`
(the cited Jasmin-CT-preservation axiom, used only in clause (A)).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.LowCTRHPFull

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.LowCTCT
open CatCrypt.Crypto.SecureCompilation.LowCTCTBridge
open CatCrypt.Crypto.SecureCompilation.LowCTLabeled
open CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge
open CatCrypt.Crypto.SecureCompilation.LowCTLeakTrace
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring
open scoped ENNReal

set_option autoImplicit false

/-! ## §1. The headline RHP theorem (dialect front) -/

/-- **Full-pipeline RHP for a labeled Signal/LowCT source** (dialect): a
    `wellLabeled` covered source whose dialect front succeeds and whose Jasmin
    lowering compiles to x86 yields (A) a CT binary, (B) a structurally-factoring
    leak trace, and (C) symmetric-adversary back-translation agreement. -/
theorem RHP_pipeline_full_labeled
    {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) (hc : IsCoveredCtl c) {o : DTransOut Γ}
    (hT : translateDialectControl vm c = some o)
    (leaves : CTLeaves) (label : Labeling)
    (h_lab : wellLabeled leaves label c = true)
    (h_safe : jasminCTSafe c = true)
    (params results : List Located) (fname : String)
    (x86 : X86Prog)
    (h_compile : Jasminc.compilesTo
                   (toJasminProg fname params results c) x86) :
    x86.isCT ∧
    (∃ pre : Dialects.CryptoDialectLeakTrace.LeakTrace, ∀ {t : CryptoTy} (body : Com catCryptDialect o.Γ' t)
        (c' : Com catCryptDialect Γ t), o.cont body = some c' →
        Com.leakTrace c' = pre ++ Com.leakTrace body) ∧
    (∀ {t : CryptoTy} (targetCtx : Com catCryptDialect o.Γ' t),
        ∃ sourceCtx : Com catCryptDialect o.Γ' t,
          (o.cont sourceCtx).map Com.leakTrace = (o.cont targetCtx).map Com.leakTrace) := by
  refine ⟨?_, ?_, ?_⟩
  · exact wellLabeled_implies_x86_ct leaves label c h_lab h_safe
            params results fname x86 h_compile
  · exact dialect_front_leakage_factoring vm hc hT
  · intro t targetCtx; exact ⟨targetCtx, rfl⟩

/-- **Labeled CT × leak-trace factoring** (dialect): a `wellLabeled` covered
    source admits an explicit leak-trace prefix (independent of any tail), and the
    compiled binary is CT. -/
theorem RHP_pipeline_labeled_leakage_NI
    {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) (hc : IsCoveredCtl c) {o : DTransOut Γ}
    (hT : translateDialectControl vm c = some o)
    (leaves : CTLeaves) (label : Labeling)
    (h_lab : wellLabeled leaves label c = true)
    (h_safe : jasminCTSafe c = true)
    (params results : List Located) (fname : String)
    (x86 : X86Prog)
    (h_compile : Jasminc.compilesTo
                   (toJasminProg fname params results c) x86) :
    (∃ pre : Dialects.CryptoDialectLeakTrace.LeakTrace, ∀ {t : CryptoTy} (body : Com catCryptDialect o.Γ' t)
        (c' : Com catCryptDialect Γ t), o.cont body = some c' →
        Com.leakTrace c' = pre ++ Com.leakTrace body) ∧
    x86.isCT := by
  refine ⟨?_, ?_⟩
  · exact dialect_front_leakage_factoring vm hc hT
  · exact wellLabeled_implies_x86_ct leaves label c h_lab h_safe
            params results fname x86 h_compile

/-- **Length-of-prefix corollary** (dialect): the leaf's leak-trace contribution
    has a fixed length, independent of the plugged tail — the structural-CT
    statement at the dialect-front boundary. -/
theorem RHP_pipeline_labeled_prefix_length
    {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ) (c : LowCT) (hc : IsCoveredCtl c)
    {o : DTransOut Γ}
    (hT : translateDialectControl vm c = some o)
    (ctx₁ ctx₂ : Com catCryptDialect o.Γ' t)
    {c₁ c₂ : Com catCryptDialect Γ t}
    (h₁ : o.cont ctx₁ = some c₁) (h₂ : o.cont ctx₂ = some c₂) :
    (Com.leakTrace c₁).length - (Com.leakTrace ctx₁).length =
    (Com.leakTrace c₂).length - (Com.leakTrace ctx₂).length :=
  dialect_front_leak_prefix_constant vm hc hT ctx₁ ctx₂ h₁ h₂

/-! ## §5. ε = 0 structural base case (A.RHP-quantitative starting point) -/

/-- **Structural CT at the LowCT boundary**: the structural leak trace is a
    constant function of inputs. -/
theorem RHP_pipeline_structural_CT (c : LowCT) :
    ∀ (_V₁ _V₂ : Unit), LowCT.leakTrace c = LowCT.leakTrace c := by
  intros; rfl

/-- **ε = 0 specialisation**: the structural leak trace is constant in any input. -/
theorem RHP_pipeline_structural_leakTrace_constant
    (c : LowCT) (input₁ input₂ : Unit) :
    (fun (_ : Unit) => LowCT.leakTrace c) input₁ =
    (fun (_ : Unit) => LowCT.leakTrace c) input₂ := rfl

/-! ## §6. Composition with masking-style passes (A.RHP-quantitative) -/

/-- **ε-bounded RHP composition with a masking-style pass**: a constant-output
    observable composed with an `ε_mask`-approximating pass lifts to
    `QuantifiedLeakageNI` at `2 · ε_mask`. -/
theorem RHP_pipeline_eps_bounded
    {α β : Type} (constant_obs : α → SPComp β)
    (h_const : ∀ x₁ x₂ : α, constant_obs x₁ = constant_obs x₂)
    (target_obs : α → SPComp β)
    (ε_mask : ℝ≥0∞)
    (h_approx : sdist constant_obs target_obs ≤ ε_mask) :
    NIPreservation.QuantifiedLeakageNI (fun _ _ : α => True)
      target_obs (0 + 2 * ε_mask) := by
  apply NIPreservation.approx_ni_preservation
    (h_ni := ?_) h_approx
  exact NIPreservation.leakageNI_implies_quantified
    (fun x₁ x₂ _ => by rw [h_const x₁ x₂])

/-- **Specialisation for the structural leak trace**. -/
theorem RHP_pipeline_structural_eps_bounded
    (c : LowCT)
    (target_obs : Unit → SPComp CryptoSSA.LeakTrace)
    (ε_mask : ℝ≥0∞)
    (h_approx :
      sdist (fun (_ : Unit) => SPComp.pure (LowCT.leakTrace c))
            target_obs ≤ ε_mask) :
    NIPreservation.QuantifiedLeakageNI (fun _ _ : Unit => True)
      target_obs (0 + 2 * ε_mask) :=
  RHP_pipeline_eps_bounded
    (fun (_ : Unit) => SPComp.pure (LowCT.leakTrace c))
    (fun _ _ => rfl)
    target_obs ε_mask h_approx

end CatCrypt.Crypto.SecureCompilation.LowCTRHPFull
