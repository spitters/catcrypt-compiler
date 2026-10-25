/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFDceLeak

/-!
# Forwarding of loads from one-word stack arrays

`fwdLoad1 p` replaces each load `stackLoad 64 1 s c` of `p` from an array `s` that `p` binds,
in the same region, by a constant-index store `stackStoreImm 64 1 i z a`, by the stored value
`a`: the binding of the load is removed and its uses read `a`. An array of one word holds the
single word last stored, so the load reads `a` at every index. The facts `StoreFacts Γ`
record, for each one-word array of the context, the stored word when the array is bound by
such a store; a region body starts with the facts of the enclosing context.

The store, the zero array it updates and the index of the load stay bound; when nothing else
reads them, dead-binding elimination `NFProg.dce` removes them.

The pass is a function on `NFProg jasminDialect Γ ts`. It preserves the denotation at every
call environment and fuel (`denoteAt_fwdLoad1`). Its leakage run emits the events of the
source run less the events of the forwarded loads, read off the trace along the structure of
the source by `fwdLoad1Erase` (`leakRunMC_fwdLoad1`); under `jLeakModel` a load emits one
`addr` event at its index and a store none. Two source runs with equal events give two runs
of `fwdLoad1 p` with equal events (`fwdLoad1_ctRelC`).

## Main definitions

* `storeVal1?`, `loadArr1?` — the stored word of a store into a one-word array, and the array
  of a load from one.
* `StoreFacts`, `StoreFacts.pushStore`, `StoreFacts.appNone` — the stored words known in a
  context.
* `fwdLoad1Go`, `fwdLoad1` — the pass along a renaming, and at the identity.
* `fwdLoad1Erase` — the reading of a source trace that drops the events of forwarded loads.

## Main results

* `denoteAt_fwdLoad1` — the pass preserves the denotation.
* `leakRunMC_fwdLoad1` — the leakage transformer of the pass.
* `fwdLoad1_ctRelC` — equal source events give equal events after the pass.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFFwdLoad1

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy JasminOp jasminDialect
  stackGet stackSet)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProg (Agrees agrees_id agrees_lift appLift
  agrees_appLift bindHom agrees_bindHom lookupArgs_renameVars denoteM_rename varTyCast
  lookup_varTyCast)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (evCount iterErase whileErase
  forIterLeak_erase whileIterLeak_erase Expr.ctLeak_length)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak.NFProg (leakRunMC)

/-! ## 1. Stores into and loads from one-word arrays -/

/-- The stored word of a constant-index store into an array of one 64-bit word. -/
def storeVal1? {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Expr jasminDialect Γ t → Option (Var Γ (.reg 64))
  | ⟨op, _, args⟩ =>
      match op, args with
      | .stackStoreImm 64 1 _, args => some args.tail.head
      | _, _ => none

/-- The array of a load from an array of one 64-bit word, with the result type `reg 64`. -/
def loadArr1? {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Expr jasminDialect Γ t → Option {_s : Var Γ (.stackArr 64 1) // t = .reg 64}
  | ⟨op, h, args⟩ =>
      match op, h, args with
      | .stackLoad 64 1, h, args => some ⟨args.head, h.symm⟩
      | _, _, _ => none

/-- A store into an array of one word holds the stored word. -/
theorem storeVal1?_denote {Γ : Ctxt jasminDialect} (e : Expr jasminDialect Γ (.stackArr 64 1))
    {a : Var Γ (.reg 64)} (h : storeVal1? e = some a) (V : Valuation Γ) :
    e.denote V 0 = a.lookup V := by
  obtain ⟨op, hty, args⟩ := e
  cases op
  case stackStoreImm w n i =>
    cases hty
    rcases args with _ | ⟨z, _ | ⟨a', _ | _⟩⟩
    simp only [storeVal1?, Option.some.injEq] at h
    subst h
    show stackSet (z.lookup V) i (a'.lookup V) 0 = _
    simp only [stackSet]
    rw [ite_eq_left (Fin.ext (by simp [Nat.mod_one]))]
    rfl
  all_goals simp [storeVal1?] at h

/-- A load from an array of one word reads the word the array holds. -/
theorem loadArr1?_denote {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    {s : Var Γ (.stackArr 64 1)} {h : t = .reg 64} (he : loadArr1? e = some ⟨s, h⟩)
    {Δ : Ctxt jasminDialect} (b : Var Δ (.reg 64)) (V : Valuation Γ) (W : Valuation Δ)
    (hb : b.lookup W = s.lookup V 0) :
    (varTyCast h.symm b).lookup W = e.denote V := by
  obtain ⟨op, hty, args⟩ := e
  cases op
  case stackLoad w n =>
    rcases args with _ | ⟨s', _ | ⟨c, _ | _⟩⟩
    subst hty
    simp only [loadArr1?] at he
    rcases eq_or_ne w 64 with rfl | hw
    swap
    · split at he <;> simp_all
    rcases eq_or_ne n 1 with rfl | hn
    swap
    · split at he <;> simp_all
    simp only [Option.some.injEq, Subtype.mk.injEq] at he
    change s' = s at he
    subst he
    rw [lookup_varTyCast]
    show b.lookup W = stackGet (s'.lookup V) (c.lookup V).toNat
    rw [hb]
    exact congrArg (s'.lookup V) (Subsingleton.elim _ _)
  all_goals simp [loadArr1?] at he

/-! ## 2. The stored words known in a context -/

/-- The stored words known in the context `Γ`: for a one-word array, the variable of the word
    a store into it stored, when it is bound by such a store. -/
abbrev StoreFacts (Γ : Ctxt jasminDialect) : Type :=
  Var Γ (.stackArr 64 1) → Option (Var Γ (.reg 64))

/-- The facts of the context extended by one binding whose own fact is `new`. -/
def StoreFacts.consFact {Γ : Ctxt jasminDialect} {t : JasminTy}
    (new : Option (Var (t :: Γ) (.reg 64))) (K : StoreFacts Γ) : StoreFacts (t :: Γ) :=
  fun v => match t, v, new with
    | _, .here, new => new
    | _, .there v, _ => (K v).map .there

/-- The facts of the context extended by the binding of `e`: a store into a one-word array
    records its stored word. -/
def StoreFacts.pushStore {Γ : Ctxt jasminDialect} {t : JasminTy} (K : StoreFacts Γ)
    (e : Expr jasminDialect Γ t) : StoreFacts (t :: Γ) :=
  StoreFacts.consFact ((storeVal1? e).map .there) K

/-- The facts of the context extended by the prefix `cs`, with no fact on the prefix. -/
def StoreFacts.appNone {Γ : Ctxt jasminDialect} : (cs : List JasminTy) → StoreFacts Γ →
    StoreFacts (cs ++ Γ)
  | [], K => K
  | _ :: cs, K => StoreFacts.consFact none (StoreFacts.appNone cs K)

/-- The facts hold at a valuation: each array with a fact holds the recorded word. -/
def StoreFacts.HoldsAt {Γ : Ctxt jasminDialect} (K : StoreFacts Γ) (V : Valuation Γ) : Prop :=
  ∀ (s : Var Γ (.stackArr 64 1)) (a : Var Γ (.reg 64)), K s = some a →
    s.lookup V 0 = a.lookup V

theorem storeFacts_holds_none {Γ : Ctxt jasminDialect} (V : Valuation Γ) :
    StoreFacts.HoldsAt (fun _ => none) V :=
  fun _ _ h => by cases h

theorem StoreFacts.HoldsAt.consFact_none {Γ : Ctxt jasminDialect} {t : JasminTy}
    {K : StoreFacts Γ}
    {V : Valuation Γ} (hK : K.HoldsAt V) (x : ⟦t⟧) :
    (StoreFacts.consFact none K).HoldsAt (V.extend x) := by
  intro s a h
  cases s with
  | here => simp [StoreFacts.consFact] at h
  | there s =>
      simp only [StoreFacts.consFact, Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      exact hK s a' ha

theorem StoreFacts.HoldsAt.pushStore {Γ : Ctxt jasminDialect} {t : JasminTy} {K : StoreFacts Γ}
    {V : Valuation Γ} (hK : K.HoldsAt V) (e : Expr jasminDialect Γ t) :
    (K.pushStore e).HoldsAt (V.extend (e.denote V)) := by
  intro s a h
  cases s with
  | here =>
      simp only [StoreFacts.pushStore, StoreFacts.consFact, Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      exact storeVal1?_denote e ha V
  | there s =>
      simp only [StoreFacts.pushStore, StoreFacts.consFact, Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      exact hK s a' ha

theorem StoreFacts.HoldsAt.appNone {Γ : Ctxt jasminDialect} {K : StoreFacts Γ} {V : Valuation Γ}
    (hK : K.HoldsAt V) : (cs : List JasminTy) → (A : Valuation (d := jasminDialect) cs) →
    (StoreFacts.appNone cs K).HoldsAt (hvAppend A V)
  | [], .nil => hK
  | _ :: cs, .cons a A => (hK.appNone cs A).consFact_none a

/-! ## 3. The pass -/

/-- **Forwarding of loads from one-word arrays along a renaming.** A binding of a load from a
    one-word array `s` with a fact `a` is removed, and its uses read the image of `a`
    under the renaming; every other binding is kept and records its fact; the regions are
    entered with the facts of the enclosing context. -/
def fwdLoad1Go : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → StoreFacts Γ → Ctxt.Hom Γ Δ → NFProg jasminDialect Δ ts
  | _, _, _, .ret vs, _, ren => .ret (HVector.renameVars ren vs)
  | _, _, _, .var e k, K, ren =>
      match loadArr1? e with
      | some ⟨s, h⟩ =>
          match K s with
          | some a =>
              fwdLoad1Go k (K.pushStore e) (bindHom (.cons (varTyCast h.symm (ren a)) .nil) ren)
          | none => .var (e.rename ren) (fwdLoad1Go k (K.pushStore e) (Ctxt.Hom.lift ren))
      | none => .var (e.rename ren) (fwdLoad1Go k (K.pushStore e) (Ctxt.Hom.lift ren))
  | _, _, _, .forLoop (cs := cs) count inits body k, K, ren =>
      .forLoop (ren count) (HVector.renameVars ren inits)
        (fwdLoad1Go body (StoreFacts.appNone cs (StoreFacts.consFact none K))
          (appLift cs (Ctxt.Hom.lift ren)))
        (fwdLoad1Go k (StoreFacts.appNone cs K) (appLift cs ren))
  | _, _, _, .ifThenElse (rs := rs) cond thn els k, K, ren =>
      .ifThenElse (ren cond) (fwdLoad1Go thn K ren) (fwdLoad1Go els K ren)
        (fwdLoad1Go k (StoreFacts.appNone rs K) (appLift rs ren))
  | _, _, _, .whileLoop (cs := cs) inits body k, K, ren =>
      .whileLoop (HVector.renameVars ren inits) (fwdLoad1Go body (StoreFacts.appNone cs K)
        (appLift cs ren)) (fwdLoad1Go k (StoreFacts.appNone cs K) (appLift cs ren))
  | _, _, _, .call (rs := rs) f args k, K, ren =>
      .call f (HVector.renameVars ren args)
        (fwdLoad1Go k (StoreFacts.appNone rs K) (appLift rs ren))

/-- **Forwarding of loads from one-word arrays**: `fwdLoad1Go` from no facts at the identity
    renaming. -/
def fwdLoad1 {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    NFProg jasminDialect Γ ts :=
  fwdLoad1Go p (fun _ => none) (fun v => v)

/-! ## 4. Preservation of the denotation -/

/-- **Preservation along a renaming.** When `ren` relates `V` to `W` and the facts hold at
    `V`, the pass denotes at `W`, at every call environment and fuel, what the source denotes
    at `V`. -/
theorem denoteAt_fwdLoad1Go (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (K : StoreFacts Γ) (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ)
      (W : Valuation Δ), Agrees ren V W → K.HoldsAt V →
      (fwdLoad1Go p K ren).denoteAt E fuel W = p.denoteAt E fuel V := by
  induction p with
  | ret vs =>
      intro Δ K ren V W h hK
      simp only [fwdLoad1Go, NFProg.denoteAt, NFProg.denote, lookupArgs_renameVars h]
  | var e k ih =>
      intro Δ K ren V W h hK
      have hkeep : (NFProg.var (e.rename ren)
          (fwdLoad1Go k (K.pushStore e) (Ctxt.Hom.lift ren))).denoteAt E fuel W =
          (NFProg.var e k).denoteAt E fuel V := by
        simp only [NFProg.denoteAt, NFProg.denote, denoteM_rename h,
          Expr.denoteM_option_eq_some, Option.bind_eq_bind, Option.bind_some]
        exact ih _ _ _ _ (agrees_lift h _) (hK.pushStore e)
      simp only [fwdLoad1Go]
      split
      · rename_i s hty hl
        split
        · rename_i a ha
          have hx : (varTyCast hty.symm (ren a)).lookup W = e.denote V :=
            loadArr1?_denote e hl (ren a) V W ((h a).trans (hK s a ha).symm)
          have hag : Agrees (bindHom (.cons (varTyCast hty.symm (ren a)) .nil) ren)
              (V.extend (e.denote V)) W := by
            rw [← hx]
            exact agrees_bindHom h (HVector.cons (varTyCast hty.symm (ren a)) .nil)
          rw [ih _ _ _ _ hag (hK.pushStore e)]
          simp only [NFProg.denoteAt, NFProg.denote, Expr.denoteM_option_eq_some,
            Option.bind_eq_bind, Option.bind_some]
        · exact hkeep
      · exact hkeep
  | forLoop count inits body k ihb ihk =>
      intro Δ K ren V W h hK
      have hb : ∀ acc i, (fwdLoad1Go body (StoreFacts.appNone _ (StoreFacts.consFact none K))
            (appLift _ (Ctxt.Hom.lift ren))).denoteAt E fuel
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W)) =
          body.denoteAt E fuel (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun acc i => ihb _ _ _ _ (agrees_appLift (agrees_lift h _) _ acc)
          ((hK.consFact_none _).appNone _ acc)
      have hk : ∀ acc, (fwdLoad1Go k (StoreFacts.appNone _ K) (appLift _ ren)).denoteAt E fuel
            (hvAppend acc W) = k.denoteAt E fuel (hvAppend acc V) :=
        fun acc => ihk _ _ _ _ (agrees_appLift h _ acc) (hK.appNone _ acc)
      simp only [NFProg.denoteAt] at hb hk
      simp only [fwdLoad1Go, NFProg.denoteAt, NFProg.denote, lookupArgs_renameVars h, h count,
        hb, hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ K ren V W h hK
      have hk : ∀ r, (fwdLoad1Go k (StoreFacts.appNone _ K) (appLift _ ren)).denoteAt E fuel
            (hvAppend r W) = k.denoteAt E fuel (hvAppend r V) :=
        fun r => ihk _ _ _ _ (agrees_appLift h _ r) (hK.appNone _ r)
      have ht := iht K ren V W h hK
      have he := ihe K ren V W h hK
      simp only [NFProg.denoteAt] at hk ht he
      simp only [fwdLoad1Go, NFProg.denoteAt, NFProg.denote, h cond, ht, he, hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ K ren V W h hK
      have hb : ∀ acc, (fwdLoad1Go body (StoreFacts.appNone _ K) (appLift _ ren)).denoteAt E fuel
            (hvAppend acc W) = body.denoteAt E fuel (hvAppend acc V) :=
        fun acc => ihb _ _ _ _ (agrees_appLift h _ acc) (hK.appNone _ acc)
      have hk : ∀ acc, (fwdLoad1Go k (StoreFacts.appNone _ K) (appLift _ ren)).denoteAt E fuel
            (hvAppend acc W) = k.denoteAt E fuel (hvAppend acc V) :=
        fun acc => ihk _ _ _ _ (agrees_appLift h _ acc) (hK.appNone _ acc)
      simp only [NFProg.denoteAt] at hb hk
      simp only [fwdLoad1Go, NFProg.denoteAt, NFProg.denote, lookupArgs_renameVars h, hb, hk]
  | call f args k ih =>
      intro Δ K ren V W h hK
      have hk : ∀ r, (fwdLoad1Go k (StoreFacts.appNone _ K) (appLift _ ren)).denoteAt E fuel
            (hvAppend r W) = k.denoteAt E fuel (hvAppend r V) :=
        fun r => ih _ _ _ _ (agrees_appLift h _ r) (hK.appNone _ r)
      simp only [NFProg.denoteAt] at hk
      simp only [fwdLoad1Go, NFProg.denoteAt, NFProg.denote, lookupArgs_renameVars h, hk]

/-- **Preservation.** `fwdLoad1 p` denotes what `p` denotes, at every call environment, fuel
    and valuation. -/
theorem denoteAt_fwdLoad1 (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    (fwdLoad1 p).denoteAt E fuel V = p.denoteAt E fuel V :=
  denoteAt_fwdLoad1Go E fuel p _ _ V V (agrees_id V) (storeFacts_holds_none V)

/-! ## 5. Leakage -/

/-- **The erasure of the pass on traces**: the reading of a trace along the structure of `p`
    from the facts `K`, dropping the events of each forwarded load and keeping every other
    event; a `call` node emits no event. It returns the kept events and the rest of the
    trace. -/
def fwdLoad1Erase (M : LeakModel jasminDialect) (fuel : Nat) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
    StoreFacts Γ → List CTLeak → List CTLeak × List CTLeak
  | _, _, .ret _, _, tr => ([], tr)
  | _, _, .var e k, K, tr =>
      if ((loadArr1? e).bind fun s => K s.1).isSome then
        fwdLoad1Erase M fuel k (K.pushStore e) (tr.drop (evCount (M.kind e.op)))
      else
        (tr.take (evCount (M.kind e.op)) ++
            (fwdLoad1Erase M fuel k (K.pushStore e) (tr.drop (evCount (M.kind e.op)))).1,
          (fwdLoad1Erase M fuel k (K.pushStore e) (tr.drop (evCount (M.kind e.op)))).2)
  | _, _, .forLoop (cs := cs) _ _ body k, K, tr =>
      match tr with
      | .trip n :: tr' =>
          (.trip n :: ((iterErase (fwdLoad1Erase M fuel body
                (StoreFacts.appNone cs (StoreFacts.consFact none K))) n tr').1 ++
              (fwdLoad1Erase M fuel k (StoreFacts.appNone cs K)
                (iterErase (fwdLoad1Erase M fuel body
                  (StoreFacts.appNone cs (StoreFacts.consFact none K))) n tr').2).1),
            (fwdLoad1Erase M fuel k (StoreFacts.appNone cs K)
              (iterErase (fwdLoad1Erase M fuel body
                (StoreFacts.appNone cs (StoreFacts.consFact none K))) n tr').2).2)
      | _ => ([], tr)
  | _, _, .ifThenElse (rs := rs) _ thn els k, K, tr =>
      match tr with
      | .branch b :: tr' =>
          (.branch b :: ((if b then fwdLoad1Erase M fuel thn K tr'
              else fwdLoad1Erase M fuel els K tr').1 ++
              (fwdLoad1Erase M fuel k (StoreFacts.appNone rs K)
                (if b then fwdLoad1Erase M fuel thn K tr'
                  else fwdLoad1Erase M fuel els K tr').2).1),
            (fwdLoad1Erase M fuel k (StoreFacts.appNone rs K)
              (if b then fwdLoad1Erase M fuel thn K tr'
                else fwdLoad1Erase M fuel els K tr').2).2)
      | _ => ([], tr)
  | _, _, .whileLoop (cs := cs) _ body k, K, tr =>
      ((whileErase (fwdLoad1Erase M fuel body (StoreFacts.appNone cs K)) fuel tr).1 ++
          (fwdLoad1Erase M fuel k (StoreFacts.appNone cs K)
            (whileErase (fwdLoad1Erase M fuel body (StoreFacts.appNone cs K)) fuel tr).2).1,
        (fwdLoad1Erase M fuel k (StoreFacts.appNone cs K)
          (whileErase (fwdLoad1Erase M fuel body (StoreFacts.appNone cs K)) fuel tr).2).2)
  | _, _, .call (rs := rs) _ _ k, K, tr => fwdLoad1Erase M fuel k (StoreFacts.appNone rs K) tr

/-- A renamed expression emits at `W` the events of the source at `V`. -/
theorem ctLeak_exprRename (M : LeakModel jasminDialect) {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : Agrees ren V W)
    (e : Expr jasminDialect Γ t) :
    ComLevelCheck.Expr.ctLeak M (e.rename ren) W = ComLevelCheck.Expr.ctLeak M e V := by
  obtain ⟨op, rfl, args⟩ := e
  show ComLevelCheck.opLeak M op (Expr.lookupArgs (HVector.renameVars ren args) W) =
    ComLevelCheck.opLeak M op (Expr.lookupArgs args V)
  rw [lookupArgs_renameVars h args]

/-- **The leakage transformer of the pass along a renaming.** When `ren` relates `V` to `W`
    and the facts hold at `V`, a successful leakage run of `p` at `V` is matched by a leakage
    run of the pass at `W` to the same results, whose events are the events `fwdLoad1Erase`
    keeps from the trace of `p`. -/
theorem leakRunMC_fwdLoad1Go (M : LeakModel jasminDialect) (E : CallEnv jasminDialect)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (K : StoreFacts Γ) (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ)
      (W : Valuation Δ), Agrees ren V W → K.HoldsAt V →
      ∀ r : Valuation (d := jasminDialect) ts × List CTLeak, leakRunMC M E fuel p V = some r →
      ∃ l, leakRunMC M E fuel (fwdLoad1Go p K ren) W = some (r.1, l) ∧
        ∀ rest, fwdLoad1Erase M fuel p K (r.2 ++ rest) = (l, rest) := by
  induction p with
  | ret vs =>
      intro Δ K ren V W h hK r hr
      simp only [leakRunMC, Option.some.injEq] at hr
      subst hr
      refine ⟨[], ?_, fun rest => rfl⟩
      simp only [fwdLoad1Go, leakRunMC, lookupArgs_renameVars h]
  | var e k ih =>
      intro Δ K ren V W h hK r hr
      simp only [leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some,
        Option.map_eq_some_iff] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      have hlen := Expr.ctLeak_length M e V
      have htake : ∀ rest, (ComLevelCheck.Expr.ctLeak M e V ++ (q.2 ++ rest)).take
          (evCount (M.kind e.op)) = ComLevelCheck.Expr.ctLeak M e V := by
        intro rest; rw [← hlen, List.take_left]
      have hdrop : ∀ rest, (ComLevelCheck.Expr.ctLeak M e V ++ (q.2 ++ rest)).drop
          (evCount (M.kind e.op)) = q.2 ++ rest := by
        intro rest; rw [← hlen, List.drop_left]
      cases hc : (loadArr1? e).bind (fun s => K s.1) with
      | some a =>
          obtain ⟨⟨s, hty⟩, hl, ha⟩ := Option.bind_eq_some_iff.mp hc
          have hx : (varTyCast hty.symm (ren a)).lookup W = e.denote V :=
            loadArr1?_denote e hl (ren a) V W ((h a).trans (hK s a ha).symm)
          have hag : Agrees (bindHom (.cons (varTyCast hty.symm (ren a)) .nil) ren)
              (V.extend (e.denote V)) W := by
            rw [← hx]
            exact agrees_bindHom h (HVector.cons (varTyCast hty.symm (ren a)) .nil)
          obtain ⟨l, hl', el⟩ := ih _ _ _ _ hag (hK.pushStore e) q hq
          refine ⟨l, ?_, fun rest => ?_⟩
          · simp only [fwdLoad1Go, hl, ha]
            exact hl'
          · simp only [fwdLoad1Erase, hc, Option.isSome_some, ite_true, List.append_assoc]
            rw [hdrop]
            exact el rest
      | none =>
          have hpass : fwdLoad1Go (NFProg.var e k) K ren =
              .var (e.rename ren) (fwdLoad1Go k (K.pushStore e) (Ctxt.Hom.lift ren)) := by
            simp only [fwdLoad1Go]
            split
            · rename_i s hty hl
              split
              · rename_i a ha
                simp [hl, ha] at hc
              · rfl
            · rfl
          obtain ⟨l, hl', el⟩ := ih _ _ _ _ (agrees_lift h (e.denote V)) (hK.pushStore e) q hq
          refine ⟨ComLevelCheck.Expr.ctLeak M e V ++ l, ?_, fun rest => ?_⟩
          · rw [hpass]
            have hd : (e.rename ren).denote W = e.denote V := by
              simpa using denoteM_rename h e
            simp only [leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some, hd, hl',
              ctLeak_exprRename M h e, Option.map_some]
          · simp only [fwdLoad1Erase, hc, Option.isSome_none, Bool.false_eq_true, ite_false,
              List.append_assoc, htake, hdrop, el]
  | forLoop count inits body k ihb ihk =>
      intro Δ K ren V W h hK r hr
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, q, hq, rfl⟩ := hr
      obtain ⟨l₁, h₁, e₁⟩ := forIterLeak_erase _ _
        (fwdLoad1Erase M fuel body (StoreFacts.appNone _ (StoreFacts.consFact none K)))
        (fun i X r hr => ihb _ _ _ _ (agrees_appLift (agrees_lift h _) _ X)
          ((hK.consFact_none _).appNone _ X) r hr) _ _ a ha
      obtain ⟨l₂, h₂, e₂⟩ := ihk _ _ _ _ (agrees_appLift h _ _) (hK.appNone _ _) q hq
      refine ⟨.trip (HasWord64.toNat (d := jasminDialect) (count.lookup V)) :: (l₁ ++ l₂), ?_,
        fun rest => ?_⟩
      · simp only [Ctxt.Valuation.extend] at h₁
        simp only [fwdLoad1Go, leakRunMC, lookupArgs_renameVars h, h count, h₁,
          Option.bind_some, h₂, Option.map_some]
      · simp only [List.length_range] at e₁
        simp only [fwdLoad1Erase, List.cons_append, List.append_assoc, e₁, e₂]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ K ren V W h hK r hr
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, q, hq, rfl⟩ := hr
      obtain ⟨l₂, h₂, e₂⟩ := ihk _ _ _ _ (agrees_appLift h _ _) (hK.appNone _ _) q hq
      have harm : ∃ l₁, (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then
            leakRunMC M E fuel (fwdLoad1Go thn K ren) W
          else leakRunMC M E fuel (fwdLoad1Go els K ren) W) = some (a.1, l₁) ∧
          ∀ rest, (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then
            fwdLoad1Erase M fuel thn K (a.2 ++ rest)
          else fwdLoad1Erase M fuel els K (a.2 ++ rest)) = (l₁, rest) := by
        split at ha
        · rename_i hb
          obtain ⟨l₁, h₁, e₁⟩ := iht K ren V W h hK a ha
          exact ⟨l₁, by rw [ite_eq_left hb]; exact h₁,
            fun rest => by rw [ite_eq_left hb]; exact e₁ rest⟩
        · rename_i hb
          obtain ⟨l₁, h₁, e₁⟩ := ihe K ren V W h hK a ha
          exact ⟨l₁, by rw [ite_eq_right hb]; exact h₁,
            fun rest => by rw [ite_eq_right hb]; exact e₁ rest⟩
      obtain ⟨l₁, h₁, e₁⟩ := harm
      refine ⟨.branch (HasBoolBit.toBool (d := jasminDialect) (cond.lookup V)) :: (l₁ ++ l₂),
        ?_, fun rest => ?_⟩
      · simp only [fwdLoad1Go, leakRunMC, h cond, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [fwdLoad1Erase, List.cons_append, List.append_assoc, e₁, e₂]
  | whileLoop inits body k ihb ihk =>
      intro Δ K ren V W h hK r hr
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, q, hq, rfl⟩ := hr
      obtain ⟨l₁, h₁, e₁⟩ := whileIterLeak_erase _ _
        (fwdLoad1Erase M fuel body (StoreFacts.appNone _ K))
        (fun X r hr => ihb _ _ _ _ (agrees_appLift h _ X) (hK.appNone _ X) r hr) _ _ a ha
      obtain ⟨l₂, h₂, e₂⟩ := ihk _ _ _ _ (agrees_appLift h _ _) (hK.appNone _ _) q hq
      refine ⟨l₁ ++ l₂, ?_, fun rest => ?_⟩
      · simp only [fwdLoad1Go, leakRunMC, lookupArgs_renameVars h, h₁, Option.bind_some, h₂,
          Option.map_some]
      · simp only [fwdLoad1Erase, List.append_assoc, e₁, e₂]
  | call f args k ih =>
      intro Δ K ren V W h hK r hr
      simp only [leakRunMC, Option.bind_eq_some_iff] at hr
      obtain ⟨y, hy, hu⟩ := hr
      obtain ⟨l, hl, el⟩ := ih _ _ _ _ (agrees_appLift h _ y) (hK.appNone _ y) r hu
      refine ⟨l, ?_, fun rest => el rest⟩
      simp only [fwdLoad1Go, leakRunMC, lookupArgs_renameVars h, hy, Option.bind_some, hl]

/-- **The leakage transformer of the pass.** A successful leakage run of `p` is matched by a
    leakage run of `fwdLoad1 p` to the same results, whose events are the events
    `fwdLoad1Erase` keeps from the trace of `p`. -/
theorem leakRunMC_fwdLoad1 (M : LeakModel jasminDialect) (E : CallEnv jasminDialect)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (V : Valuation Γ) (r : Valuation (d := jasminDialect) ts × List CTLeak)
    (h : leakRunMC M E fuel p V = some r) :
    ∃ l, leakRunMC M E fuel (fwdLoad1 p) V = some (r.1, l) ∧
      ∀ rest, fwdLoad1Erase M fuel p (fun _ => none) (r.2 ++ rest) = (l, rest) :=
  leakRunMC_fwdLoad1Go M E fuel p _ _ V V (agrees_id V) (storeFacts_holds_none V) r h

/-- **Constant time through the pass, relative to source runs.** Two successful runs of `p`
    with equal events give two successful runs of `fwdLoad1 p` to the same results with equal
    events. -/
theorem fwdLoad1_ctRelC (M : LeakModel jasminDialect) (E : CallEnv jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation (d := jasminDialect) ts × List CTLeak)
    (h₁ : leakRunMC M E fuel p V₁ = some r₁) (h₂ : leakRunMC M E fuel p V₂ = some r₂)
    (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, leakRunMC M E fuel (fwdLoad1 p) V₁ = some s₁ ∧
      leakRunMC M E fuel (fwdLoad1 p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧
      s₁.2 = s₂.2 := by
  obtain ⟨l₁, k₁, e₁⟩ := leakRunMC_fwdLoad1 M E fuel p V₁ r₁ h₁
  obtain ⟨l₂, k₂, e₂⟩ := leakRunMC_fwdLoad1 M E fuel p V₂ r₂ h₂
  refine ⟨_, _, k₁, k₂, rfl, rfl, ?_⟩
  have h1 := e₁ []
  have h2 := e₂ []
  rw [he] at h1
  rw [h1] at h2
  exact (Prod.mk.inj h2).1

end CatCrypt.Crypto.SecureCompilation.VIR.NFFwdLoad1
