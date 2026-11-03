/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.NFToRustM
import all Init.Internal.Order.Basic

/-!
# Exit-flag loops: the Aeneas `loop` against the fuel-bounded iteration

The reading `nfToRustM` runs an exit-flag loop `whileLoop` as the Aeneas combinator `loop`
over its body (`flagStep`). This module proves that a value of that run is the value of the
fuel-bounded iteration `NFProg.whileIter` of the denotation, from some fuel on, and
assembles the simulation of `AeneasFront/NFToRustM.lean` for every NF program.

The proof is fixpoint induction on `loop` (`Lean.Order.fix_induct`) with a motive that holds
at divergence, so it is admissible in the flat order of `RustM`
(`Lean.Order.admissible_flatOrder`): the argument of `loop_spec` in the vendored model. No
termination measure is used.

## Main results

* `loop_whileIter`: a value of `loop` over a step that agrees with a fuel-indexed body is a
  value of `whileIter` at every fuel and every bound from some point on
* `sim_whileLoop`: the simulation step at `whileLoop`
* `nfToRustM_sim`: the simulation for every NF program
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.ImpToNF (PDenP tableOf)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

-- The fixpoint induction on `loop` names the monotonicity proof of its `partial_fixpoint`
-- definition, as `Aeneas.Std.loop_spec` does; the generated `loop.fixpoint_induct` states
-- its bottom through `FlatOrder.mk`, which the module system does not expose.
set_option linter.auxLemma false in
/-- **The Aeneas `loop` against `whileIter`.** If every value of the Aeneas step `F` at a tuple
    is `flagStep r` for a value `r` of the fuel-indexed body `step` from some fuel on, then a
    value of `loop F` is the value of `whileIter (step f) n` for all `f` and `n` from some
    bound on. -/
theorem loop_whileIter {cs : List NfTy}
    (F : Valuation (d := nfDialect) cs →
      RustM (Aeneas.Std.ControlFlow (Valuation (d := nfDialect) cs) (Valuation (d := nfDialect) cs)))
    (step : Nat → Valuation (d := nfDialect) cs →
      Option (Valuation (d := nfDialect) (HasBitType.bit (d := nfDialect) :: cs)))
    (hF : ∀ acc c, F acc = .ok c →
      ∃ r N, (∀ f, N ≤ f → step f acc = some r) ∧ c = flagStep r) :
    ∀ init res, loop F init = .ok res →
      ∃ N, ∀ f n, N ≤ f → N ≤ n → NFProg.whileIter (step f) n init = some res := by
  intro init
  delta loop
  refine Lean.Order.fix_induct (loop._proof_1 F)
    (motive := fun g => ∀ x res, g x = .ok res →
      ∃ N, ∀ f n, N ≤ f → N ≤ n → NFProg.whileIter (step f) n x = some res) ?_ ?_ init
  · apply Lean.Order.admissible_pi
    intro x
    apply Lean.Order.admissible_apply (β := fun _ => RustM (Valuation (d := nfDialect) cs))
      (P := fun _ r => ∀ res, r = .ok res →
        ∃ N, ∀ f n, N ≤ f → N ≤ n → NFProg.whileIter (step f) n x = some res) x
    exact Lean.Order.admissible_flatOrder _ (fun _ h => by cases h)
  · intro g IH x res hg
    simp only [] at hg
    rcases hb : F x with c | e | _
    · rw [hb] at hg
      obtain ⟨r, N₁, hN₁, rfl⟩ := hF x c hb
      have hstep : ∀ f, N₁ ≤ f → ∀ n', NFProg.whileIter (step f) (n' + 1) x =
          if r.head then NFProg.whileIter (step f) n' r.tail else some r.tail := by
        intro f hf n'
        rw [NFProg.whileIter, hN₁ f hf, Option.bind_eq_bind, Option.bind_some]
        rfl
      cases hh : r.head with
      | true =>
        have hg' : g r.tail = .ok res := by simpa [flagStep, hh] using hg
        obtain ⟨N₂, hN₂⟩ := IH r.tail res hg'
        refine ⟨max N₁ (N₂ + 1), fun f n hf hn => ?_⟩
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rw [hstep f (le_of_max_le_left hf) n', hh]
        simp only [ite_true]
        exact hN₂ f n' (by omega) (by omega)
      | false =>
        have hg' : r.tail = res := by simpa [flagStep, hh] using hg
        refine ⟨max N₁ 1, fun f n hf hn => ?_⟩
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rw [hstep f (le_of_max_le_left hf) n', hh, hg']
        rfl
    · rw [hb] at hg
      cases hg
    · rw [hb] at hg
      cases hg

/-- **The simulation step at an exit-flag loop.** -/
theorem sim_whileLoop {Γ : Ctxt nfDialect} {cs ts : List NfTy}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg nfDialect (cs ++ Γ) (HasBitType.bit (d := nfDialect) :: cs))
    (k : NFProg nfDialect (cs ++ Γ) ts) (V : Valuation Γ)
    (hb : ∀ V', Sim body V') (hk : ∀ acc, Sim k (hvAppend acc V)) :
    Sim (.whileLoop inits body k) V := by
  intro W h
  rw [nfToRustM] at h
  obtain ⟨acc, hacc, h⟩ := rustM_bind_ok h
  obtain ⟨N₂, hN₂⟩ := hk acc W h
  obtain ⟨N₁, hN₁⟩ := loop_whileIter _
    (fun f acc => PDenP hax64WExit f body (hvAppend acc V))
    (fun acc c hc => by
      obtain ⟨r, hr, hc⟩ := rustM_bind_ok hc
      cases hc
      obtain ⟨N, hN⟩ := hb _ r hr
      exact ⟨r, N, hN, rfl⟩) _ _ hacc
  refine ⟨max N₁ N₂, fun fuel hf => ?_⟩
  change NFProg.whileIter (fun acc => PDenP hax64WExit fuel body (hvAppend acc V)) fuel
      (Expr.lookupArgs inits V) >>= (fun acc => PDenP hax64WExit fuel k (hvAppend acc V)) =
    some W
  rw [hN₁ fuel fuel (le_of_max_le_left hf) (le_of_max_le_left hf), Option.bind_eq_bind,
    Option.bind_some]
  exact hN₂ fuel (le_of_max_le_right hf)

/-- **The simulation.** For every NF program, a value of the Aeneas reading `nfToRustM` is
    the denotation `PDenP hax64WExit` of the compiler at every fuel from some fuel on. -/
theorem nfToRustM_sim : ∀ {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (V : Valuation Γ), Sim p V
  | _, _, .ret vs, V => sim_ret vs V
  | _, _, .var e k, V => sim_var e k V fun _ => nfToRustM_sim k _
  | _, _, .forLoop count inits body k, V =>
    sim_forLoop count inits body k V (fun V' => nfToRustM_sim body V')
      (fun _ => nfToRustM_sim k _)
  | _, _, .ifThenElse cond thn els k, V =>
    sim_ifThenElse cond thn els k V (nfToRustM_sim thn V) (nfToRustM_sim els V)
      (fun _ => nfToRustM_sim k _)
  | _, _, .whileLoop inits body k, V =>
    sim_whileLoop inits body k V (fun V' => nfToRustM_sim body V')
      (fun _ => nfToRustM_sim k _)
  | _, _, .call _ _ _, _ => fun _ h => by rw [nfToRustM] at h; cases h

/-- **The simulation at some fuel.** -/
theorem nfToRustM_sim_exists {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (V : Valuation Γ) (W : Valuation (d := nfDialect) ts) (h : nfToRustM p V = .ok W) :
    ∃ fuel, PDenP hax64WExit fuel p V = some W := by
  obtain ⟨N, hN⟩ := nfToRustM_sim p V W h
  exact ⟨N, hN N le_rfl⟩

/-! ## Monotonicity of the denotation in the fuel

These lemmas are about `NFProg.denote` of `VIR/NFProg.lean`; they are stated here, beside
their first use, because editing `NFProg.lean` rebuilds the whole compiler. -/

section Mono

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]

omit [DialectSignature d] [HasWord64 d] in
/-- The iteration of an exit-flag loop is monotone in the step and in the fuel. -/
theorem whileIter_mono {cs : List d.Ty}
    {step step' : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs))}
    (hs : ∀ a r, step a = some r → step' a = some r) :
    ∀ (n : Nat) (acc r : Valuation cs), NFProg.whileIter step n acc = some r →
      NFProg.whileIter step' (n + 1) acc = some r
  | 0, _, _, h => by cases h
  | n + 1, acc, r, h => by
    rw [NFProg.whileIter] at h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    rw [NFProg.whileIter, hs acc x hx, Option.bind_eq_bind, Option.bind_some]
    split at h
    · rename_i hb
      rw [ite_eq_left hb]
      exact whileIter_mono hs n _ r h
    · rename_i hb
      rw [ite_eq_right hb]
      exact h

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] in
/-- A fold in `Option` is monotone in its step. -/
theorem foldlM_mono {β : Type} {f g : β → Nat → Option β}
    (hfg : ∀ a i r, f a i = some r → g a i = some r) :
    ∀ (l : List Nat) (acc r : β), l.foldlM f acc = some r → l.foldlM g acc = some r
  | [], _, _, h => h
  | i :: l, acc, r, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hfg acc i x hx, Option.bind_eq_bind, Option.bind_some]
    exact foldlM_mono hfg l x r h

variable [DialectDenoteM d Option] [CallDenote d]

/-- **Monotonicity of the denotation in the fuel.** A value of a program at the fuel `n` is
    its value at the fuel `n + 1`. -/
theorem NFProg.denote_mono : ∀ {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (n : Nat)
    (V : Valuation Γ) (r : Valuation ts), p.denote n V = some r → p.denote (n + 1) V = some r
  | _, _, .ret _, _, _, _, h => h
  | _, _, .var e k, n, V, r, h => by
    rw [NFProg.denote] at h ⊢
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hx, Option.bind_eq_bind, Option.bind_some]
    exact NFProg.denote_mono k n _ r h
  | _, _, .forLoop count inits body k, n, V, r, h => by
    rw [NFProg.denote] at h ⊢
    obtain ⟨acc, hacc, h⟩ := Option.bind_eq_some_iff.mp h
    rw [foldlM_mono (fun a i r' hr' => NFProg.denote_mono body n _ r' hr') _ _ _ hacc,
      Option.bind_eq_bind, Option.bind_some]
    exact NFProg.denote_mono k n _ r h
  | _, _, .ifThenElse cond thn els k, n, V, r, h => by
    rw [NFProg.denote] at h ⊢
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    have hx' : (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote (n + 1) V
        else els.denote (n + 1) V) = some x := by
      split
      · rename_i hc
        rw [ite_eq_left hc] at hx
        exact NFProg.denote_mono thn n V x hx
      · rename_i hc
        rw [ite_eq_right hc] at hx
        exact NFProg.denote_mono els n V x hx
    rw [hx', Option.bind_eq_bind, Option.bind_some]
    exact NFProg.denote_mono k n _ r h
  | _, _, .whileLoop inits body k, n, V, r, h => by
    rw [NFProg.denote] at h ⊢
    obtain ⟨acc, hacc, h⟩ := Option.bind_eq_some_iff.mp h
    rw [whileIter_mono (fun a r' hr' => NFProg.denote_mono body n _ r' hr') n _ _ hacc,
      Option.bind_eq_bind, Option.bind_some]
    exact NFProg.denote_mono k n _ r h
  | _, _, .call f args k, n, V, r, h => by
    rw [NFProg.denote] at h ⊢
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hx, Option.bind_eq_bind, Option.bind_some]
    exact NFProg.denote_mono k n _ r h

end Mono

end CatCrypt.Crypto.SecureCompilation.AeneasFront
