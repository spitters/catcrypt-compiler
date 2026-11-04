/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses

/-!
# Elimination of aborting branches

A front that reads a panicking guard `if c then fail else ()` of its source emits the branch
`ifThenElse c thn (ret []) k` whose arm `thn` starts with an aborting operation, an operation
that denotes no value. The pass `NFProg.abortElim ab` replaces such a branch by its
continuation `k`, for the aborting operations that the test `ab` marks. It keeps every run
of its input that succeeds: a run that succeeds through the branch takes the empty arm, so
it reads `k` at the valuation of the branch. Programs in which `ab` marks no operation are
left unchanged.

The pass is stated for every dialect and every test `ab`; the certificate takes the
hypothesis that every operation `ab` marks denotes no value.

## Main definitions

* `NFProg.abortsFirst`, `NFProg.isRetNil`, `NFProg.abortFree` — the tests of the pass.
* `NFProg.iteElim`, `NFProg.abortElim` — the pass.
* `NFProgPasses.abortElimStep` — the pass as a chain step.

## Main results

* `NFProg.denote_abortElim` — a value of a program is a value of its elimination.
* `NFProg.abortElim_of_abortFree` — the pass is the identity on programs in which `ab` marks
  no operation.
* `NFProgPasses.abortElimCert` — the certificate of the step at equal inputs and outputs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] (ab : d.Op → Bool)

/-- A program whose first statement binds an operation that `ab` marks. -/
def abortsFirst {Γ : Ctxt d} {ts : List d.Ty} : NFProg d Γ ts → Bool
  | .var e _ => ab e.op
  | _ => false

/-- A program that returns at once. -/
def isRetNil {Γ : Ctxt d} {ts : List d.Ty} : NFProg d Γ ts → Bool
  | .ret _ => true
  | _ => false

/-- A program none of whose bound operations `ab` marks. -/
def abortFree : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => !ab e.op && abortFree k
  | _, _, .forLoop _ _ body k => abortFree body && abortFree k
  | _, _, .ifThenElse _ thn els k => abortFree thn && abortFree els && abortFree k
  | _, _, .whileLoop _ body k => abortFree body && abortFree k
  | _, _, .call _ _ k => abortFree k

/-- The branch `ifThenElse c thn els k`, or its continuation `k` when it has no result, its
    first arm aborts first and its second arm returns at once. -/
def iteElim {Γ : Ctxt d} {ts : List d.Ty} : {rs : List d.Ty} →
    Var Γ (HasBitType.bit (d := d)) → NFProg d Γ rs → NFProg d Γ rs →
    NFProg d (rs ++ Γ) ts → NFProg d Γ ts
  | [], c, thn, els, k =>
      if abortsFirst ab thn && isRetNil els then k else .ifThenElse c thn els k
  | _ :: _, c, thn, els, k => .ifThenElse c thn els k

/-- **The elimination of aborting branches**: every branch without result whose first arm
    aborts first and whose second arm returns at once is replaced by its continuation. -/
def abortElim : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → NFProg d Γ ts
  | _, _, .ret vs => .ret vs
  | _, _, .var e k => .var e (abortElim k)
  | _, _, .forLoop count inits body k => .forLoop count inits (abortElim body) (abortElim k)
  | _, _, .ifThenElse c thn els k => iteElim ab c (abortElim thn) (abortElim els) (abortElim k)
  | _, _, .whileLoop inits body k => .whileLoop inits (abortElim body) (abortElim k)
  | _, _, .call f args k => .call f args (abortElim k)

/-- A program that aborts first is not free of marked operations. -/
theorem abortsFirst_of_abortFree {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (h : abortFree ab p = true) : abortsFirst ab p = false := by
  cases p with
  | var e k =>
      simp only [abortFree, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact h.1
  | _ => rfl

/-- **The pass is the identity on programs free of marked operations.** -/
theorem abortElim_of_abortFree : ∀ {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts),
    abortFree ab p = true → abortElim ab p = p
  | _, _, .ret _, _ => rfl
  | _, _, .var e k, h => by
      simp only [abortFree, Bool.and_eq_true] at h
      rw [abortElim, abortElim_of_abortFree k h.2]
  | _, _, .forLoop _ _ body k, h => by
      simp only [abortFree, Bool.and_eq_true] at h
      rw [abortElim, abortElim_of_abortFree body h.1, abortElim_of_abortFree k h.2]
  | _, _, .ifThenElse (rs := rs) c thn els k, h => by
      simp only [abortFree, Bool.and_eq_true] at h
      rw [abortElim, abortElim_of_abortFree thn h.1.1, abortElim_of_abortFree els h.1.2,
        abortElim_of_abortFree k h.2]
      cases rs with
      | nil =>
          rw [iteElim, abortsFirst_of_abortFree ab thn h.1.1, Bool.false_and]
          exact ite_eq_right Bool.false_ne_true
      | cons _ _ => rfl
  | _, _, .whileLoop _ body k, h => by
      simp only [abortFree, Bool.and_eq_true] at h
      rw [abortElim, abortElim_of_abortFree body h.1, abortElim_of_abortFree k h.2]
  | _, _, .call _ _ k, h => by
      rw [abortElim, abortElim_of_abortFree k h]

variable [DialectDenoteM d Option] [CallDenote d]

/-- **The branch step of the pass keeps successful runs.** If every operation `ab` marks
    denotes no value, a value of a branch is a value of `iteElim` of it: through a branch
    replaced by its continuation, the run took the second arm, which returns the empty
    tuple. -/
theorem denote_iteElim
    (hab : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      ab e.op = true → e.denoteM V = none)
    {Γ : Ctxt d} {ts rs : List d.Ty} (fuel : Nat) (c : Var Γ (HasBitType.bit (d := d)))
    (thn els : NFProg d Γ rs) (k : NFProg d (rs ++ Γ) ts) (V : Valuation Γ)
    (W : Valuation ts) (h : (NFProg.ifThenElse c thn els k).denote fuel V = some W) :
    (iteElim ab c thn els k).denote fuel V = some W := by
  cases rs with
  | cons _ _ => exact h
  | nil =>
      rw [iteElim]
      split
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        rw [NFProg.denote] at h
        obtain ⟨r, hr, hk⟩ := Option.bind_eq_some_iff.mp h
        split at hr
        · cases thn with
          | var e k' =>
              rw [NFProg.denote, hab e V hc.1] at hr
              cases hr
          | _ => simp [abortsFirst] at hc
        · cases els with
          | ret vs =>
              rw [NFProg.denote] at hr
              cases hr
              cases vs
              exact hk
          | _ => simp [isRetNil] at hc
      · exact h

/-- **A value of a program is a value of its elimination**, when every operation `ab` marks
    denotes no value. -/
theorem denote_abortElim
    (hab : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      ab e.op = true → e.denoteM V = none) :
    ∀ {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (fuel : Nat) (V : Valuation Γ)
      (W : Valuation ts), p.denote fuel V = some W → (abortElim ab p).denote fuel V = some W
  | _, _, .ret _, _, _, _, h => h
  | _, _, .var e k, fuel, V, W, h => by
    rw [NFProg.denote] at h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    rw [abortElim, NFProg.denote, hx, Option.bind_eq_bind, Option.bind_some]
    exact denote_abortElim hab k fuel _ W h
  | _, _, .forLoop count inits body k, fuel, V, W, h => by
    rw [NFProg.denote] at h
    obtain ⟨acc, hacc, h⟩ := Option.bind_eq_some_iff.mp h
    have hf : ∀ (l : List Nat) (a r : Valuation _),
        l.foldlM (fun acc i => body.denote fuel
          (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V))) a = some r →
        l.foldlM (fun acc i => (abortElim ab body).denote fuel
          (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V))) a = some r := by
      intro l
      induction l with
      | nil => exact fun _ _ h => h
      | cons i l ih =>
          intro a r hl
          rw [List.foldlM_cons] at hl ⊢
          obtain ⟨y, hy, hl⟩ := Option.bind_eq_some_iff.mp hl
          rw [denote_abortElim hab body fuel _ y hy, Option.bind_eq_bind, Option.bind_some]
          exact ih y r hl
    rw [abortElim, NFProg.denote, hf _ _ _ hacc, Option.bind_eq_bind, Option.bind_some]
    exact denote_abortElim hab k fuel _ W h
  | _, _, .ifThenElse c thn els k, fuel, V, W, h => by
    rw [abortElim]
    apply denote_iteElim ab hab
    rw [NFProg.denote] at h ⊢
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    have hr' : (if HasBoolBit.toBool (d := d) (c.lookup V) then
        (abortElim ab thn).denote fuel V else (abortElim ab els).denote fuel V) = some r := by
      split
      · rename_i hc
        rw [ite_eq_left hc] at hr
        exact denote_abortElim hab thn fuel V r hr
      · rename_i hc
        rw [ite_eq_right hc] at hr
        exact denote_abortElim hab els fuel V r hr
    rw [hr', Option.bind_eq_bind, Option.bind_some]
    exact denote_abortElim hab k fuel _ W h
  | _, _, .whileLoop inits body k, fuel, V, W, h => by
    rw [NFProg.denote] at h
    obtain ⟨acc, hacc, h⟩ := Option.bind_eq_some_iff.mp h
    have hw : ∀ (n : Nat) (a r : Valuation _),
        whileIter (fun acc => body.denote fuel (hvAppend acc V)) n a = some r →
        whileIter (fun acc => (abortElim ab body).denote fuel (hvAppend acc V)) n a =
          some r := by
      intro n
      induction n with
      | zero => exact fun _ _ h => h
      | succ n ih =>
          intro a r hl
          rw [whileIter] at hl ⊢
          obtain ⟨y, hy, hl⟩ := Option.bind_eq_some_iff.mp hl
          rw [denote_abortElim hab body fuel _ y hy, Option.bind_eq_bind, Option.bind_some]
          split at hl
          · rename_i hb
            rw [ite_eq_left hb]
            exact ih _ r hl
          · rename_i hb
            rw [ite_eq_right hb]
            exact hl
    rw [abortElim, NFProg.denote, hw _ _ _ hacc, Option.bind_eq_bind, Option.bind_some]
    exact denote_abortElim hab k fuel _ W h
  | _, _, .call f args k, fuel, V, W, h => by
    rw [NFProg.denote] at h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    rw [abortElim, NFProg.denote, hx, Option.bind_eq_bind, Option.bind_some]
    exact denote_abortElim hab k fuel _ W h

end NFProg

namespace NFProgPasses

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] (ab : d.Op → Bool)

/-- The elimination of aborting branches as a chain step; it never refuses. -/
def abortElimStep (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.Step (NFProg d Γ ts) (NFProg d Γ ts) :=
  ⟨"abortElim", fun p => some (NFProg.abortElim ab p)⟩

/-- **The certificate of the elimination of aborting branches**, at equal inputs and
    outputs, when every operation `ab` marks denotes no value (`NFProg.denote_abortElim`). -/
def abortElimCert [DialectDenoteM d Option] [CallDenote d]
    (hab : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Valuation Γ),
      ab e.op = true → e.denoteM V = none)
    (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.StepCert (abortElimStep ab Γ ts).run (nfSem fuel d Γ ts) (nfSem fuel d Γ ts) :=
  PassChain.StepCert.ofRefines _ fun p q V o hf hd => by
    cases hf
    exact NFProg.denote_abortElim ab hab p fuel V o hd

end NFProgPasses

end CatCrypt.Crypto.SecureCompilation.VIR
