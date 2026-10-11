/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxSourceLeak
public import CatCrypt.Crypto.Hax.NFToCatLeak
public import CatCrypt.Crypto.Hax.NFToCatCall
public import CatCrypt.Crypto.SecureCompilation.CT.HaxLevels

/-!
# The leakage transformer of `impToNF`

The front `ImpToNF.impToNF` as a pass of the structured-leakage pattern: the leakage of the
`NFProg` it emits is a function of the source leakage alone.

## The source leakage

`srcLeakCl bi cl e fuel env` is the leakage of the run of `denote' bi fuel e` from `env`, a
tree of the events `SrcEv` of `srcLeak` with the shape of the evaluation. It differs from
`srcLeak` on the constructs that `srcLeak` leaves opaque: a call `app f args` leaves the
leakages of its arguments, left to right, and then the call leakage `cl f vals` of the call on
the argument values `vals`; an assignment leaves the leakage of its right-hand side; a tuple
the leakages of its components. The source leakage of the front `srcLeakNF` has the call
leakage `nfCallLeak`, the event `op (callLeak f vals)`; `callLeak f vals` is the event list of
the leakage model `nfLeakModel` for a call of `f`, read on the source values (`valNatOf`).

## Call leakages

A call leakage `C : CallLeak` pairs a source call leakage `C.cl` with the events `C.ce` of a
binding of a call in the emitted program; `C.opEv` gives every other operation its events of
`nfLeakModel`. It agrees with the builtins `bi` (`CallLeak.Agrees`) when the events of a call
that succeeds are the events `nfTrace` of its source call leakage. The call leakage of the
front, `CallLeak.nf`, agrees with every builtins, and its runs are the runs `nfLeakRun` of
`nfLeakModel` (`nfLeakRunE_nf`). A call leakage that expands the calls of a crate gives a call
the leakage of the body of the callee.

## The transformer

`nfTrace l` maps a source leakage tree to the events of `nfLeakModel`: a branch to `branch`,
the bounds `lo, hi` of a counted loop to the trip count `trip ((hi - lo).toNat % 2 ^ 64)`, an
operation event to its events, and every other event to none.

## The leakage run with an event function

`NFProg.leakRunE ev` is the leakage run of an `NFProg` in which a binding of an operation `op`
on the values `x` emits the events `ev op x`; at `ev = opLeak M` it is the run
`NFProg.leakRunM M` (`NFProg.leakRunE_opLeak`). `NFPre.leakRunE ev` is the leakage run of a
prefix; a filled prefix runs the prefix and then its continuation (`NFPre.leakRunE_plug`).

## Constant time

Source constant time `SourceCTNF` for a level table `lt` compares the events `nfTrace` of two
runs without the leaf calls of tagged field heads (`stripField`): a tagged field call is
compiled to a field body whose constant time is proved separately. The leakage model
`nfLeakModelQ` makes those calls quiet, and its runs are the stripped runs of `nfLeakModel`
(`nfLeakRunQ_eq`, from the change of model `NFProg.leakRunM_filter`). From `SourceCTNF`, two
leakage runs in `nfLeakModelQ` of the emitted program from valuations related to environments
agreeing on the public variables emit equal events (`impToNF_ct_runs`). For a function body
with the parameters `ps`, whose source run ends in a value from every valuation of the parameters, this is `NFCTRel` for the
labels `entryLabels lt ps` (`impToNF_nfCTRel`). At `lt = levelsOf s`, with every parameter
listed in the secrecy record `s`, it holds for the parameter levels `paramLevelOf s`, the
levels of the labels `nfLabels s` of the direct front (`impToNF_nfCTRel_params`).

## Main definitions

* `OpEvents`, `NFProg.leakRunE`, `NFPre.leakRunE`, `PLeak`, `nfLeakRunE`, `QuietPre`
* `CallLeak`, `CallLeak.opEv`, `CallLeak.Quiet`, `CallLeak.Agrees`, `CallLeak.nf`
* `valNatOf`, `callLeak`, `srcLeakCl`, `srcArgsLeakCl`, `nfCallLeak`, `srcLeakNF`,
  `srcArgsLeakNF`, `nfEv`, `nfTrace`
* `LSound` — the simulation statement of `ImpToNF.Sound` with the leakage of the prefix
* `nfLeakModelQ`, `nfLeakRunQ` — the leakage model with quiet field calls and its runs
* `SourceCTNF` — constant time at the source for `srcLeakNF`, modulo the field calls
* `entryLabels`, `entryEnvOf`, `paramLevelOf`

## Main results

* `NFProg.leakRunE_opLeak`, `NFProg.leakRunE_congr`, `NFProg.leakRunE_fst`
* `NFPre.leakRunE_plug`, `NFPre.leakRunE_append`, `NFPre.leakRunE_fst`
* `CallLeak.nf_agrees`, `CallLeak.nf_opEv`, `nfLeakRunE_nf` — the call leakage of the front
* the case lemmas `lsound_lit`, `lsound_atom`, `lsound_seq`, `lsound_letBind`,
  `lsound_assign`, `lsound_args`, `lsound_app`, `lsound_tuple`, `lsound_cond`,
  `loop_leak`, `forRevLeak_ge`, `loopRev_leak`, `quietPre_ctrOut`, `loopOut_leak`,
  `lsound_forFold`, `lsound_forFoldRev`
* `forIterLeak_filter`, `whileIterLeak_filter`, `NFProg.leakRunM_filter`,
  `opLeak_nfLeakModelQ`, `nfLeakRunQ_eq` — the change of leakage model
* `impToNF_lsound`, `impToNF_leakE`, `impToNF_leak` — the leakage transformer of the front
* `impToNF_ct_runs`, `impToNF_nfCTRel`, `pubEqV_entryLabels_levelsOf`,
  `impToNF_nfCTRel_params`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option]

/-- The events of each operation of `d` on its argument values. `opLeak M` is the event
    function of a leakage model `M`. -/
abbrev OpEvents (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] : Type :=
  (op : d.Op) → HVector (fun t => ⟦t⟧) (DialectSignature.sig op) → List CTLeak

/-- The run of a program from a valuation with the list of its events, in which a binding of
    an operation `op` on the argument values `x` emits the events `ev op x`: the run
    `NFProg.leakRunM M` with the event function `ev` in place of `opLeak M`
    (`NFProg.leakRunE_opLeak`). -/
def NFProg.leakRunE (ev : OpEvents d) (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Valuation Γ →
    Option (Valuation ts × List CTLeak)
  | _, _, .ret vs, V => some (Expr.lookupArgs vs V, [])
  | _, _, .var e k, V =>
      (e.denoteM (M := Option) V).bind fun x =>
        (NFProg.leakRunE ev fuel k (V.extend x)).map fun r =>
          (r.1, ev e.op (Expr.lookupArgs e.args V) ++ r.2)
  | _, _, .forLoop count inits body k, V =>
      (forIterLeak
          (fun i acc => NFProg.leakRunE ev fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V)))
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFProg.leakRunE ev fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .trip (HasWord64.toNat (d := d) (count.lookup V)) :: (r.2 ++ q.2))
  | _, _, .ifThenElse cond thn els k, V =>
      (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunE ev fuel thn V
        else NFProg.leakRunE ev fuel els V).bind fun r =>
        (NFProg.leakRunE ev fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, .branch (HasBoolBit.toBool (d := d) (cond.lookup V)) :: (r.2 ++ q.2))
  | _, _, .whileLoop inits body k, V =>
      (whileIterLeak (fun acc => NFProg.leakRunE ev fuel body (hvAppend acc V)) fuel
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFProg.leakRunE ev fuel k (hvAppend r.1 V)).map fun q => (q.1, r.2 ++ q.2)
  | _, _, .call .., _ => none

/-- **The run with the events of a leakage model** is the leakage run `NFProg.leakRunM`. -/
theorem NFProg.leakRunE_opLeak (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V : Valuation Γ) :
    NFProg.leakRunE (opLeak M) fuel p V = NFProg.leakRunM M fuel p V := by
  induction p with
  | ret vs => rfl
  | var e k ih => simp only [NFProg.leakRunE, NFProg.leakRunM, ih]; rfl
  | forLoop count inits body k ihb ihk => simp only [NFProg.leakRunE, NFProg.leakRunM, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.leakRunE, NFProg.leakRunM, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk => simp only [NFProg.leakRunE, NFProg.leakRunM, ihb, ihk]
  | call => rfl

/-- Two event functions that agree give the same run. -/
theorem NFProg.leakRunE_congr {ev ev' : OpEvents d} (h : ∀ op x, ev op x = ev' op x)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) :
    NFProg.leakRunE ev fuel p V = NFProg.leakRunE ev' fuel p V := by
  have : ev = ev' := funext fun op => funext fun x => h op x
  subst this
  rfl

/-- **The results of the run** are the denotation of the program in the empty call
    environment. -/
theorem NFProg.leakRunE_fst (ev : OpEvents d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (V : Valuation Γ) :
    (NFProg.leakRunE ev fuel p V).map Prod.fst = p.denoteAt CallEnv.empty fuel V := by
  let _ : CallDenote d := ⟨CallEnv.empty⟩
  show (NFProg.leakRunE ev fuel p V).map Prod.fst = p.denote fuel V
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.leakRunE, NFProg.denote, Option.bind_eq_bind]
      rcases e.denoteM (M := Option) V with _ | x
      · rfl
      · simp only [Option.bind_some, Option.map_map]
        exact ih _
  | forLoop count inits body k ihb ihk =>
      rw [NFProg.denote_forLoop, ← forIterLeak_fst _ _ (fun i acc => ihb _)]
      simp only [NFProg.leakRunE, Option.bind_eq_bind]
      rcases forIterLeak _ _ _ with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | ifThenElse cond thn els k iht ihe ihk =>
      rw [NFProg.denote_ifThenElse]
      have hc : (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
          else els.denote fuel V) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunE ev fuel thn V
            else NFProg.leakRunE ev fuel els V).map Prod.fst := by
        split <;> simp only [iht, ihe]
      rw [hc]
      simp only [NFProg.leakRunE, Option.bind_eq_bind]
      rcases (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunE ev fuel thn V
        else NFProg.leakRunE ev fuel els V) with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | whileLoop inits body k ihb ihk =>
      rw [NFProg.denote_whileLoop, ← whileIterLeak_fst _ _ (fun acc => ihb _)]
      simp only [NFProg.leakRunE, Option.bind_eq_bind]
      rcases whileIterLeak _ _ _ with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ihk _
  | call => rfl

/-- The run of a prefix from a valuation with the list of its events: the valuation of the
    hole and the events of `NFProg.leakRunE ev` of the bindings, loops and branches of the
    prefix. -/
def NFPre.leakRunE (ev : OpEvents d) (fuel : Nat) :
    {Γ Δ : Ctxt d} → NFPre d Γ Δ → Valuation Γ → Option (Valuation Δ × List CTLeak)
  | _, _, .nil, V => some (V, [])
  | _, _, .var e p, V =>
      (e.denoteM (M := Option) V).bind fun x =>
        (NFPre.leakRunE ev fuel p (V.extend x)).map fun r =>
          (r.1, ev e.op (Expr.lookupArgs e.args V) ++ r.2)
  | _, _, .forLoop count inits body p, V =>
      (forIterLeak
          (fun i acc => NFProg.leakRunE ev fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V)))
          (Expr.lookupArgs inits V)).bind fun r =>
        (NFPre.leakRunE ev fuel p (hvAppend r.1 V)).map fun q =>
          (q.1, .trip (HasWord64.toNat (d := d) (count.lookup V)) :: (r.2 ++ q.2))
  | _, _, .ifThenElse cond thn els p, V =>
      (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunE ev fuel thn V
        else NFProg.leakRunE ev fuel els V).bind fun r =>
        (NFPre.leakRunE ev fuel p (hvAppend r.1 V)).map fun q =>
          (q.1, .branch (HasBoolBit.toBool (d := d) (cond.lookup V)) :: (r.2 ++ q.2))

/-- **A filled prefix** runs the prefix and then its continuation from the valuation of the
    hole, with the events of the two in order. -/
theorem NFPre.leakRunE_plug (ev : OpEvents d) (fuel : Nat) {Γ Δ : Ctxt d} {ts : List d.Ty}
    (p : NFPre d Γ Δ) (k : NFProg d Δ ts) (V : Valuation Γ) :
    NFProg.leakRunE ev fuel (p.plug k) V =
      (NFPre.leakRunE ev fuel p V).bind fun r =>
        (NFProg.leakRunE ev fuel k r.1).map fun q => (q.1, r.2 ++ q.2) := by
  induction p with
  | nil =>
      simp only [NFPre.plug, NFPre.leakRunE, Option.bind_some, List.nil_append]
      cases NFProg.leakRunE ev fuel k V <;> rfl
  | var e p ih =>
      simp only [NFPre.plug, NFProg.leakRunE, NFPre.leakRunE, ih]
      cases e.denoteM (M := Option) V with
      | none => rfl
      | some x =>
          simp only [Option.bind_some]
          cases NFPre.leakRunE ev fuel p (V.extend x) with
          | none => rfl
          | some r =>
              simp only [Option.bind_some, Option.map_some, Option.map_map]
              cases NFProg.leakRunE ev fuel k r.1 <;> simp [List.append_assoc]
  | forLoop count inits body p ih =>
      simp only [NFPre.plug, NFProg.leakRunE, NFPre.leakRunE, ih]
      cases forIterLeak (fun i acc => NFProg.leakRunE ev fuel body
          (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V)))
          (Expr.lookupArgs inits V) with
      | none => rfl
      | some a =>
          simp only [Option.bind_some]
          cases NFPre.leakRunE ev fuel p (hvAppend a.1 V) with
          | none => rfl
          | some r =>
              simp only [Option.bind_some, Option.map_some]
              cases NFProg.leakRunE ev fuel k r.1 <;> simp [List.append_assoc]
  | ifThenElse cond thn els p ih =>
      simp only [NFPre.plug, NFProg.leakRunE, NFPre.leakRunE, ih]
      cases (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunE ev fuel thn V
        else NFProg.leakRunE ev fuel els V) with
      | none => rfl
      | some a =>
          simp only [Option.bind_some]
          cases NFPre.leakRunE ev fuel p (hvAppend a.1 V) with
          | none => rfl
          | some r =>
              simp only [Option.bind_some, Option.map_some]
              cases NFProg.leakRunE ev fuel k r.1 <;> simp [List.append_assoc]

/-- **A composed prefix** runs the first prefix and then the second from the valuation of the
    hole of the first, with the events of the two in order. -/
theorem NFPre.leakRunE_append (ev : OpEvents d) (fuel : Nat) {Γ Δ Θ : Ctxt d}
    (p : NFPre d Γ Δ) (q : NFPre d Δ Θ) (V : Valuation Γ) :
    NFPre.leakRunE ev fuel (p.append q) V =
      (NFPre.leakRunE ev fuel p V).bind fun r =>
        (NFPre.leakRunE ev fuel q r.1).map fun s => (s.1, r.2 ++ s.2) := by
  induction p with
  | nil =>
      simp only [NFPre.append, NFPre.leakRunE, Option.bind_some, List.nil_append]
      cases NFPre.leakRunE ev fuel q V <;> rfl
  | var e p ih =>
      simp only [NFPre.append, NFPre.leakRunE, ih]
      cases e.denoteM (M := Option) V with
      | none => rfl
      | some x =>
          simp only [Option.bind_some]
          cases NFPre.leakRunE ev fuel p (V.extend x) with
          | none => rfl
          | some r =>
              simp only [Option.bind_some, Option.map_some]
              cases NFPre.leakRunE ev fuel q r.1 <;> simp [List.append_assoc]
  | forLoop count inits body p ih =>
      simp only [NFPre.append, NFPre.leakRunE, ih]
      cases forIterLeak (fun i acc => NFProg.leakRunE ev fuel body
          (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V)))
          (Expr.lookupArgs inits V) with
      | none => rfl
      | some a =>
          simp only [Option.bind_some]
          cases NFPre.leakRunE ev fuel p (hvAppend a.1 V) with
          | none => rfl
          | some r =>
              simp only [Option.bind_some, Option.map_some]
              cases NFPre.leakRunE ev fuel q r.1 <;> simp [List.append_assoc]
  | ifThenElse cond thn els p ih =>
      simp only [NFPre.append, NFPre.leakRunE, ih]
      cases (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunE ev fuel thn V
        else NFProg.leakRunE ev fuel els V) with
      | none => rfl
      | some a =>
          simp only [Option.bind_some]
          cases NFPre.leakRunE ev fuel p (hvAppend a.1 V) with
          | none => rfl
          | some r =>
              simp only [Option.bind_some, Option.map_some]
              cases NFPre.leakRunE ev fuel q r.1 <;> simp [List.append_assoc]

/-- **The valuation of the leakage run of a prefix** is its denotation in the empty call
    environment. -/
theorem NFPre.leakRunE_fst (ev : OpEvents d) (fuel : Nat) {Γ Δ : Ctxt d}
    (p : NFPre d Γ Δ) (V : Valuation Γ) :
    (NFPre.leakRunE ev fuel p V).map Prod.fst =
      @NFPre.denote d _ _ _ _ _ ⟨CallEnv.empty⟩ fuel Γ Δ p V := by
  let _ : CallDenote d := ⟨CallEnv.empty⟩
  induction p with
  | nil => rfl
  | var e p ih =>
      simp only [NFPre.leakRunE, NFPre.denote, Option.bind_eq_bind]
      rcases e.denoteM (M := Option) V with _ | x
      · rfl
      · simp only [Option.bind_some, Option.map_map]
        exact ih _
  | @forLoop Γ' Δ' cs_1 count inits body p ih =>
      have hb : ∀ (i : Nat) (acc : Valuation cs_1),
          (NFProg.leakRunE ev fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V))).map Prod.fst =
          body.denote fuel (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) :=
        fun i acc => NFProg.leakRunE_fst ev fuel body
          (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V))
      rw [NFPre.denote, ← forIterLeak_fst _ _ hb]
      simp only [NFPre.leakRunE, Option.bind_eq_bind]
      rcases forIterLeak (fun i acc => NFProg.leakRunE ev fuel body
          (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V)))
          (Expr.lookupArgs inits V) with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ih _
  | ifThenElse cond thn els p ih =>
      have hc : (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
          else els.denote fuel V) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunE ev fuel thn V
            else NFProg.leakRunE ev fuel els V).map Prod.fst := by
        split
        · exact (NFProg.leakRunE_fst ev fuel thn V).symm
        · exact (NFProg.leakRunE_fst ev fuel els V).symm
      simp only [NFPre.denote, hc]
      simp only [NFPre.leakRunE, Option.bind_eq_bind]
      rcases (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunE ev fuel thn V
        else NFProg.leakRunE ev fuel els V) with _ | ⟨a, t⟩
      · rfl
      · simp only [Option.bind_some, Option.map_some, Option.map_map]
        exact ih _

/-! ## A change of leakage model that filters the events -/

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] in
/-- The iterations of a counted loop under a step whose events are the events of `step`
    filtered by `q` have the events of the iterations under `step` filtered by `q`. -/
theorem forIterLeak_filter (q : CTLeak → Bool) {cs : List d.Ty}
    (step step' : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (h : ∀ i acc, step' i acc = (step i acc).map fun r => (r.1, r.2.filter q)) :
    ∀ (is : List Nat) (acc : Valuation cs), forIterLeak step' is acc =
      (forIterLeak step is acc).map fun r => (r.1, r.2.filter q)
  | [], _ => rfl
  | i :: is, acc => by
      simp only [forIterLeak, h]
      rcases step i acc with _ | ⟨a, l⟩
      · rfl
      · simp only [Option.map_some, Option.bind_some, forIterLeak_filter q step step' h is a]
        rcases forIterLeak step is a with _ | ⟨b, m⟩
        · rfl
        · simp [List.filter_append]

omit [DialectSignature d] [HasWord64 d] [DialectDenoteM d Option] in
/-- The runs of a loop in exit-flag form under a body whose events are the events of `step`
    filtered by `q`, for a `q` that keeps every branch event, have the events of the runs
    under `step` filtered by `q`. -/
theorem whileIterLeak_filter (q : CTLeak → Bool) (hb : ∀ b, q (.branch b) = true)
    {cs : List d.Ty}
    (step step' : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (h : ∀ acc, step' acc = (step acc).map fun r => (r.1, r.2.filter q)) :
    ∀ (n : Nat) (acc : Valuation cs), whileIterLeak step' n acc =
      (whileIterLeak step n acc).map fun r => (r.1, r.2.filter q)
  | 0, _ => rfl
  | n + 1, acc => by
      simp only [whileIterLeak, h]
      rcases step acc with _ | ⟨a, l⟩
      · rfl
      · simp only [Option.map_some, Option.bind_some]
        split
        · rw [whileIterLeak_filter q hb step step' h n]
          rcases whileIterLeak step n a.tail with _ | ⟨b, m⟩
          · rfl
          · simp [List.filter_append, hb]
        · simp [List.filter_append, hb]

/-- **A change of leakage model that filters the events.** When every operation emits under
    `M'` the events it emits under `M` filtered by `q`, and `q` keeps every branch and trip
    event, the leakage run of a program under `M'` is its run under `M` with the events
    filtered by `q`. -/
theorem NFProg.leakRunM_filter (M M' : LeakModel d) (q : CTLeak → Bool)
    (hb : ∀ b, q (.branch b) = true) (ht : ∀ n, q (.trip n) = true)
    (hop : ∀ op vals, opLeak M' op vals = (opLeak M op vals).filter q) (fuel : Nat)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) :
    NFProg.leakRunM M' fuel p V =
      (NFProg.leakRunM M fuel p V).map fun r => (r.1, r.2.filter q) := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.leakRunM]
      rcases e.denoteM (M := Option) V with _ | x
      · rfl
      · simp only [Option.bind_some, ih, Option.map_map]
        congr 1
        funext r
        simp [Expr.ctLeak, hop, List.filter_append]
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.leakRunM]
      rw [forIterLeak_filter q _ _ (fun i acc => ihb _)]
      rcases forIterLeak _ _ _ with _ | ⟨a, l⟩
      · rfl
      · simp only [Option.map_some, Option.bind_some, ihk, Option.map_map]
        congr 1
        funext r
        simp [List.filter_append, ht]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.leakRunM]
      have hc : (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunM M' fuel thn V
          else NFProg.leakRunM M' fuel els V) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunM M fuel thn V
            else NFProg.leakRunM M fuel els V).map fun r => (r.1, r.2.filter q) := by
        split
        · exact iht V
        · exact ihe V
      rw [hc]
      rcases (if HasBoolBit.toBool (d := d) (cond.lookup V) then NFProg.leakRunM M fuel thn V
        else NFProg.leakRunM M fuel els V) with _ | ⟨a, l⟩
      · rfl
      · simp only [Option.map_some, Option.bind_some, ihk, Option.map_map]
        congr 1
        funext r
        simp [List.filter_append, hb]
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.leakRunM]
      rw [whileIterLeak_filter q hb _ _ (fun acc => ihb _)]
      rcases whileIterLeak _ _ _ with _ | ⟨a, l⟩
      · rfl
      · simp only [Option.map_some, Option.bind_some, ihk, Option.map_map]
        congr 1
        funext r
        simp [List.filter_append]
  | call => rfl

end CatCrypt.Crypto.SecureCompilation.VIR

namespace CatCrypt.Crypto.Hax.ImpToNF

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote' denoteArgs')
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax.NFToCat (nfLeakModel nfKind nfValNat nfLeakRun stripField
  isFieldEvent)
open CatCrypt.Crypto.Jasmin.LowCT (LevelTable SecretLevel)
open MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## Call leakages -/

/-- **A call leakage**: the source leakage `cl f vals` of a call of `f` on the source values
    `vals`, and the events `ce f as r x` of a binding of the call `NfOp.call f as r` on the
    values `x`. The call leakage of the front is `CallLeak.nf`; a call leakage that expands
    the calls of a crate gives a call the leakage of the body of the callee. -/
structure CallLeak where
  /-- The source leakage of a call. -/
  cl : String → List Value → SrcLeak
  /-- The events of a binding of a call. -/
  ce : (f : String) → (as : List NfTy) → NfTy → HVector (fun t : NfTy => ⟦t⟧) as →
    List CTLeak

/-- The events of an operation under the call leakage `C`: the events `C.ce` at a call, also
    under a source name, and the events of `nfLeakModel` at every other operation. -/
def CallLeak.opEv (C : CallLeak) : OpEvents nfDialect
  | .named _ op, x => C.opEv op x
  | .call f as r, x => C.ce f as r x
  | op, x => ComLevelCheck.opLeak nfLeakModel op x

/-- An operation with no event under the call leakage `C`. -/
def CallLeak.Quiet (C : CallLeak) (op : NfOp) : Prop :=
  ∀ x, C.opEv op x = []

variable {C : CallLeak}

/-! ## The prefix leakage over `nfDialect` -/

/-- The leakage run of a prefix over `nfDialect` with the leaves of `tableOf bi`, with the
    events of the call leakage `C`. -/
abbrev PLeak (bi : Builtins) (C : CallLeak) (fuel : Nat) {Γ Δ : Ctxt nfDialect}
    (p : NFPre nfDialect Γ Δ) (V : Valuation Γ) : Option (Valuation Δ × List CTLeak) :=
  @NFPre.leakRunE nfDialect _ _ _ _ (nfDenote (tableOf bi)) C.opEv fuel Γ Δ p V

/-- The leakage run of a program over `nfDialect` with the leaves of `tableOf bi`, with the
    events of the call leakage `C`. At `CallLeak.nf` it is `nfLeakRun` (`nfLeakRunE_nf`). -/
abbrev nfLeakRunE (bi : Builtins) (C : CallLeak) (fuel : Nat) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    Option (Valuation (d := nfDialect) ts × List CTLeak) :=
  @NFProg.leakRunE nfDialect _ _ _ _ (nfDenote (tableOf bi)) C.opEv fuel _ _ p V

/-- The valuation of the prefix leakage run is the denotation of the prefix. -/
theorem PLeak_fst (bi : Builtins) (C : CallLeak) (fuel : Nat) {Γ Δ : Ctxt nfDialect}
    (p : NFPre nfDialect Γ Δ) (V : Valuation Γ) :
    (PLeak bi C fuel p V).map Prod.fst = PDen bi fuel p V :=
  @NFPre.leakRunE_fst nfDialect _ _ _ _ (nfDenote (tableOf bi)) C.opEv fuel _ _ p V

/-- A prefix leakage run that succeeds ends at the denotation of the prefix. -/
theorem PLeak_den {bi : Builtins} {fuel : Nat} {Γ Δ : Ctxt nfDialect}
    {p : NFPre nfDialect Γ Δ} {V : Valuation Γ} {W : Valuation Δ} {t : List CTLeak}
    (h : PLeak bi C fuel p V = some (W, t)) : PDen bi fuel p V = some W := by
  rw [← PLeak_fst bi C, h]; rfl

/-- The prefix leakage run of a composed prefix. -/
theorem PLeak_append (bi : Builtins) (C : CallLeak) (fuel : Nat) {Γ Δ Θ : Ctxt nfDialect}
    (p : NFPre nfDialect Γ Δ) (q : NFPre nfDialect Δ Θ) (V : Valuation Γ) :
    PLeak bi C fuel (p.append q) V =
      (PLeak bi C fuel p V).bind fun r =>
        (PLeak bi C fuel q r.1).map fun s => (s.1, r.2 ++ s.2) :=
  @NFPre.leakRunE_append nfDialect _ _ _ _ (nfDenote (tableOf bi)) C.opEv fuel _ _ _ p q V

/-- Two prefix leakage runs that succeed compose. -/
theorem PLeak_append_some {bi : Builtins} {fuel : Nat} {Γ Δ Θ : Ctxt nfDialect}
    {p : NFPre nfDialect Γ Δ} {q : NFPre nfDialect Δ Θ} {V : Valuation Γ} {W₁ : Valuation Δ}
    {W₂ : Valuation Θ} {t₁ t₂ : List CTLeak} (h₁ : PLeak bi C fuel p V = some (W₁, t₁))
    (h₂ : PLeak bi C fuel q W₁ = some (W₂, t₂)) :
    PLeak bi C fuel (p.append q) V = some (W₂, t₁ ++ t₂) := by
  rw [PLeak_append, h₁, Option.bind_some, h₂]; rfl

/-- The leakage run of a filled prefix over `nfDialect`. -/
theorem nfLeakRunE_plug (bi : Builtins) (C : CallLeak) (fuel : Nat) {Γ Δ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFPre nfDialect Γ Δ) (k : NFProg nfDialect Δ ts) (V : Valuation Γ) :
    nfLeakRunE bi C fuel (p.plug k) V =
      (PLeak bi C fuel p V).bind fun r =>
        (nfLeakRunE bi C fuel k r.1).map fun q => (q.1, r.2 ++ q.2) :=
  @NFPre.leakRunE_plug nfDialect _ _ _ _ (nfDenote (tableOf bi)) C.opEv fuel _ _ _ p k V

/-! ## The events of an operation of the front -/

/-- The natural-number reading of a source value: an integer by its natural number, a
    boolean by its bit, every other value as `0`. -/
def valNatOf : Value → Nat
  | .int n => n.toNat
  | .bool b => b.toNat
  | _ => 0

/-- The reading of the encoding of a value is the reading `nfValNat` of the value. -/
theorem valNatOf_enc : (t : NfTy) → (x : t.denote) → valNatOf (enc t x) = nfValNat t x
  | .word _, x => by simp [enc, valNatOf, nfValNat]
  | .int, _ => rfl
  | .bit, _ => rfl
  | .unit, _ => rfl
  | .arr _ _, _ => rfl
  | .pair _ _, _ => rfl
  | .uint _, _ => rfl
  | .sint _, _ => rfl
  | .tnil, _ => rfl
  | .tcons _ _, _ => rfl
  | .slice _, _ => rfl

/-- The readings of a vector of values are the readings of their encodings. -/
theorem valsNat_encAll : (as : List NfTy) → (xs : HVector NfTy.denote as) →
    valsNat nfLeakModel xs = (encAll as xs).map valNatOf
  | [], .nil => rfl
  | a :: as, .cons x xs => by
      change nfValNat a x :: valsNat nfLeakModel xs = valNatOf (enc a x) :: _
      rw [valNatOf_enc, valsNat_encAll as xs]

/-- The events of a call of `f` on the source values `vals` in the leakage model
    `nfLeakModel`: the class `nfKind` of a call of `f`, read on the values by `valNatOf`. -/
def callLeak (f : String) (vals : List Value) : List CTLeak :=
  match nfKind (.call f [] .unit) with
  | .quiet => []
  | .addrAt k => [.addr "" (((vals.map valNatOf).getD k 0 : Nat) : Int)]
  | .vt m => [.vt m (vals.map valNatOf)]
  | .vtCall g => [.vtCall g ((vals.map valNatOf).map fun x => [x])]

/-- The events under `C` of a binding of the front are the events of its operation: the
    source name `mkEN` gives the binding does not change them. -/
theorem opEv_mkEN (C : CallLeak) (tgt : Option String) {Γ : Ctxt nfDialect} (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) (V : Valuation Γ) :
    C.opEv (mkEN tgt op args).op (Expr.lookupArgs (mkEN tgt op args).args V) =
      C.opEv op (Expr.lookupArgs args V) := by
  cases tgt <;> rfl

/-! ## The source leakage -/

mutual
/-- **The source leakage of the fragment of `impToNF`** with the leakage `cl f vals` of a
    call of `f` on the argument values `vals` (see the module docstring). -/
def srcLeakCl (bi : Builtins) (cl : String → List Value → SrcLeak) :
    ImpExpr → Nat → Env → SrcLeak
  | .lit _, _, _ => .nil
  | .var _, _, _ => .nil
  | .unitVal, _, _ => .nil
  | .typeAscription e _, fuel, env => srcLeakCl bi cl e fuel env
  | .letBind n v body, fuel, env =>
    .cat (srcLeakCl bi cl v fuel env)
      (contLeak ((denote' bi fuel v).run env) fun w e1 =>
        srcLeakCl bi cl body fuel (e1.extend n w))
  | .seq a b, fuel, env =>
    .cat (srcLeakCl bi cl a fuel env)
      (contLeak ((denote' bi fuel a).run env) fun _ e1 => srcLeakCl bi cl b fuel e1)
  | .assign _ r, fuel, env => srcLeakCl bi cl r fuel env
  | .app f args, fuel, env =>
    .cat (srcArgsLeakCl bi cl args fuel env)
      (match (denoteArgs' bi fuel args).run env with
       | (some vals, _) => cl f vals
       | _ => .nil)
  | .tuple es, fuel, env => srcArgsLeakCl bi cl es fuel env
  | .ifThenElse c t e, fuel, env =>
    .cat (srcLeakCl bi cl c fuel env)
      (match (denote' bi fuel c).run env with
       | (.val (.bool true), e1) => .cat (.ev (.branch true)) (srcLeakCl bi cl t fuel e1)
       | (.val (.bool false), e1) => .cat (.ev (.branch false)) (srcLeakCl bi cl e fuel e1)
       | _ => .nil)
  | .forFold i lo hi body, fuel, env =>
    boundsLeak bi lo hi (srcLeakCl bi cl lo fuel) (srcLeakCl bi cl hi fuel) fuel
      (fun l h => forLeak bi i body (srcLeakCl bi cl body) fuel l h) env
  | .forFoldRev i lo hi body, fuel, env =>
    boundsLeak bi lo hi (srcLeakCl bi cl lo fuel) (srcLeakCl bi cl hi fuel) fuel
      (fun l h => forRevLeak bi i body (srcLeakCl bi cl body) fuel l h) env
  | e, _, env => .ev (.opaque env e)

/-- `srcLeakCl` of a list of expressions run left to right, as `denoteArgs'` runs them. -/
def srcArgsLeakCl (bi : Builtins) (cl : String → List Value → SrcLeak) :
    List ImpExpr → Nat → Env → SrcLeak
  | [], _, _ => .nil
  | e :: es, fuel, env =>
    .cat (srcLeakCl bi cl e fuel env)
      (contLeak ((denote' bi fuel e).run env) fun _ e1 => srcArgsLeakCl bi cl es fuel e1)
end

/-- The call leakage of the front: the event `op (callLeak f vals)` of a call of `f` on the
    values `vals`. -/
def nfCallLeak (f : String) (vals : List Value) : SrcLeak :=
  .ev (.op (callLeak f vals))

/-- **The source leakage of the front**: `srcLeakCl` with the call leakage `nfCallLeak`. -/
abbrev srcLeakNF (bi : Builtins) : ImpExpr → Nat → Env → SrcLeak :=
  srcLeakCl bi nfCallLeak

/-- `srcLeakNF` of a list of expressions run left to right. -/
abbrev srcArgsLeakNF (bi : Builtins) : List ImpExpr → Nat → Env → SrcLeak :=
  srcArgsLeakCl bi nfCallLeak

/-- The events of `nfLeakModel` of a source event. -/
def nfEv : SrcEv → List CTLeak
  | .branch b => [.branch b]
  | .exit => []
  | .bound lo hi => [.trip ((hi - lo).toNat % 2 ^ 64)]
  | .op l => l
  | .opaque _ _ => []

/-- **The leakage transformer of `impToNF`**: the events of `nfLeakModel` of a source
    leakage tree, in evaluation order. -/
def nfTrace : SrcLeak → List CTLeak
  | .nil => []
  | .ev x => nfEv x
  | .cat a b => nfTrace a ++ nfTrace b

/-- **A call leakage agrees with the builtins `bi`**: the events of a binding of a call that
    succeeds at `tableOf bi` are the events `nfTrace` of its source leakage on the encoded
    arguments. -/
def CallLeak.Agrees (C : CallLeak) (bi : Builtins) : Prop :=
  ∀ f as r (x : HVector (fun t : NfTy => ⟦t⟧) as) y, (tableOf bi).call f as r x = some y →
    C.ce f as r x = nfTrace (C.cl f (encAll as x))

/-- **The call leakage of the front**: the source leakage `nfCallLeak` and the events of
    `nfLeakModel` at a call. -/
def CallLeak.nf : CallLeak where
  cl := nfCallLeak
  ce f as _ x := callLeak f (encAll as x)

/-- The call leakage of the front agrees with every builtins. -/
theorem CallLeak.nf_agrees (bi : Builtins) : CallLeak.nf.Agrees bi :=
  fun _ _ _ _ _ _ => rfl

/-- The events of an operation under the call leakage of the front are its events under
    `nfLeakModel`. -/
theorem CallLeak.nf_opEv : ∀ (op : NfOp) (x : HVector (fun t : NfTy => ⟦t⟧) op.sig),
    CallLeak.nf.opEv op x = ComLevelCheck.opLeak nfLeakModel op x
  | .named _ op, x => CallLeak.nf_opEv op x
  | .call f as r, x => by
      change callLeak f (encAll as x) = ComLevelCheck.opLeak nfLeakModel (.call f as r) x
      unfold ComLevelCheck.opLeak callLeak
      rw [show nfLeakModel.kind (.call f as r) = nfKind (.call f [] .unit) from rfl,
        valsNat_encAll]
      rfl
  | .const _ _, _ | .constBit _, _ | .constUnit, _ | .bin _ _, _ | .un _ _, _ | .cast _ _, _
  | .scast _ _, _ | .cmp _ _, _ | .andB, _ | .orB, _ | .xorB, _ | .eqB, _ | .notB, _
  | .index _ _, _ | .update _ _, _ | .arrLit _ _, _ | .arrRepeat _ _, _ | .mkPair _ _, _
  | .fst _ _, _ | .snd _ _, _ | .ilit _ _, _ | .ctr, _ | .trip _, _ | .tnilV, _
  | .tconsV _ _, _ | .thead _ _, _ | .ttail _ _, _ => rfl

/-- **The run with the call leakage of the front** is the leakage run `nfLeakRun`. -/
theorem nfLeakRunE_nf (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    nfLeakRunE bi CallLeak.nf fuel p V = nfLeakRun bi fuel p V :=
  (@NFProg.leakRunE_congr nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ _ CallLeak.nf_opEv
    fuel _ _ p V).trans
    (@NFProg.leakRunE_opLeak nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModel fuel _ _ p V)

/-- The leakage after a value that is the encoding of a value of the front. -/
theorem contLeak_enc (t : NfTy) (x : t.denote) (e1 : Env) (k : Value → Env → SrcLeak) :
    contLeak (.val (enc t x), e1) k = k (enc t x) e1 := by
  have h := enc_ne_controlFlow t x
  generalize enc t x = w at h ⊢
  cases w <;> first | rfl | exact absurd rfl (h _ _)

/-! ## The simulation with leakage -/

/-- **The simulation statement with leakage** for the expression `e` and the output `o` of
    the front from `σ` under the call leakage `C`: `ImpToNF.Sound`, with the prefix run by
    its leakage run with the events of `C`, whose events are the transformed source leakage
    `nfTrace (srcLeakCl bi C.cl e fuel env)`. -/
def LSound (bi : Builtins) (C : CallLeak) (fuel : Nat) (e : ImpExpr) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (o : Out Γ) : Prop :=
  ∀ (env : Env) (V : Valuation Γ) (v : Value) (env' : Env), EnvRel σ env V →
    (denote' bi fuel e).run env = (.val v, env') →
    ∀ tf, ∃ W, PLeak bi C tf o.pre V = some (W, nfTrace (srcLeakCl bi C.cl e fuel env)) ∧
      EnvRel o.σ env' W ∧ v = enc o.t (o.res.lookup W)

/-- The simulation with leakage implies the simulation. -/
theorem LSound.sound {bi : Builtins} {fuel : Nat} {e : ImpExpr} {Γ : Ctxt nfDialect}
    {σ : NfEnv Γ} {o : Out Γ} (h : LSound bi C fuel e σ o) : Sound bi fuel e σ o := by
  intro env V v env' hrel hrun tf
  obtain ⟨W, hW, hr, hv⟩ := h env V v env' hrel hrun tf
  exact ⟨W, PLeak_den hW, hr, hv⟩

/-- The prefix leakage run of one binding of a quiet operation. -/
theorem PLeak_bind1N_quiet (bi : Builtins) (fuel : Nat) (tgt : Option String)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (op : NfOp) (hq : C.Quiet op)
    (args : HVector (fun t => Var Γ t) op.sig) (V : Valuation Γ) :
    PLeak bi C fuel (bind1N tgt σ op args).pre V =
      (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V)).map fun x => (V.extend x, []) := by
  simp only [PLeak, bind1N, NFPre.leakRunE]
  rw [opEv_mkEN C tgt op args V, hq]
  cases tgt <;>
  · simp only [mkEN, Expr.denoteM, nfDenote_denoteM]
    change (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V)).bind
      (fun x => Option.map (fun r => (r.1, [] ++ r.2)) (some (V.extend x, []))) = _
    cases nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) <;> rfl

/-- `ImpToNF.sound_bind1N` with leakage, for a quiet operation and an expression with no
    source event. -/
theorem lsound_bind1N (bi : Builtins) (fuel : Nat) (e : ImpExpr) (tgt : Option String)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (op : NfOp) (hq : C.Quiet op)
    (args : HVector (fun t => Var Γ t) op.sig)
    (hl : ∀ env, nfTrace (srcLeakCl bi C.cl e fuel env) = [])
    (h : ∀ env V v env', EnvRel σ env V → (denote' bi fuel e).run env = (.val v, env') →
      env' = env ∧ ∃ x, nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some x ∧
        v = enc op.ret x) :
    LSound bi C fuel e σ (bind1N tgt σ op args) := by
  intro env V v env' hrel hrun tf
  obtain ⟨rfl, x, hx, rfl⟩ := h env V v env' hrel hrun
  refine ⟨V.extend x, ?_, hrel.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩
  rw [hl, PLeak_bind1N_quiet bi tf tgt σ op hq args V, hx]
  rfl

/-! ## Prefixes with no event -/

/-- A prefix with no event: its leakage run is its denotation with the empty list. -/
def QuietPre (bi : Builtins) (C : CallLeak) (tf : Nat) {Γ Δ : Ctxt nfDialect}
    (p : NFPre nfDialect Γ Δ) : Prop :=
  ∀ V, PLeak bi C tf p V = (PDen bi tf p V).map fun W => (W, [])

theorem QuietPre.nil (bi : Builtins) (tf : Nat) {Γ : Ctxt nfDialect} :
    QuietPre bi C tf (NFPre.nil : NFPre nfDialect Γ Γ) := fun _ => rfl

theorem QuietPre.append {bi : Builtins} {tf : Nat} {Γ Δ Θ : Ctxt nfDialect}
    {p : NFPre nfDialect Γ Δ} {q : NFPre nfDialect Δ Θ} (hp : QuietPre bi C tf p)
    (hq : QuietPre bi C tf q) : QuietPre bi C tf (p.append q) := by
  intro V
  rw [PLeak_append, PDen_append, hp]
  cases PDen bi tf p V with
  | none => rfl
  | some W =>
      simp only [Option.map_some, Option.bind_some]
      rw [hq W]
      cases PDen bi tf q W <;> rfl

/-- One binding of a quiet operation has no event. -/
theorem QuietPre.var (bi : Builtins) (tf : Nat) (tgt : Option String) {Γ : Ctxt nfDialect}
    (op : NfOp) (hq : C.Quiet op) (args : HVector (fun t => Var Γ t) op.sig) :
    QuietPre bi C tf (.var (mkEN tgt op args) .nil : NFPre nfDialect Γ (op.ret :: Γ)) := by
  intro V
  have h1 := PLeak_bind1N_quiet bi tf tgt [] op hq args V
  have h2 := PDen_bind1N bi tf tgt [] op args V
  simp only [bind1N] at h1 h2
  rw [h1, h2]
  cases nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) <;> rfl

/-- The bindings of `tupleOut` have no event. -/
theorem quietPre_tupleOut (bi : Builtins) (tf : Nat) :
    ∀ {Γ : Ctxt nfDialect} (tgt : Option String) (as : List NfTy)
      (vs : HVector (fun t => Var Γ t) as), QuietPre bi C tf (tupleOut tgt as vs).2.1
  | _, tgt, [], .nil => QuietPre.var bi tf tgt .tnilV (fun _ => rfl) .nil
  | _, tgt, _ :: as, .cons _ vs =>
      QuietPre.append (quietPre_tupleOut bi tf none as vs)
        (QuietPre.var bi tf tgt _ (fun _ => rfl) _)

/-- The prefix of an atom has no event. -/
theorem quietPre_atomOut (bi : Builtins) (tf : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ)
    (a : ImpExpr) {o : Out Γ} (h : atomOut σ a = some o) : QuietPre bi C tf o.pre := by
  cases a with
  | var x =>
      simp only [atomOut, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      exact QuietPre.nil bi tf
  | lit l =>
      cases l with
      | bool b =>
          simp only [atomOut, litOut, Option.some.injEq] at h
          subst h
          exact QuietPre.var bi tf none _ (fun _ => rfl) _
      | unit =>
          simp only [atomOut, litOut, Option.some.injEq] at h
          subst h
          exact QuietPre.var bi tf none _ (fun _ => rfl) _
      | int n | uintLit W n | sintLit W n =>
          simp only [atomOut, litOut, Option.bind_eq_some_iff] at h
          obtain ⟨⟨t, v⟩, -, hs⟩ := h
          split at hs
          · simp only [Option.some.injEq] at hs
            subst hs
            exact QuietPre.var bi tf none _ (fun _ => rfl) _
          · cases hs
  | _ => simp [atomOut] at h

/-- The prefix of a list of atoms has no event. -/
theorem quietPre_argsOut (bi : Builtins) (tf : Nat) (es : List ImpExpr) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {oa : ArgsOut Γ}, argsOut σ es = some oa →
      QuietPre bi C tf oa.pre := by
  induction es with
  | nil =>
      intro Γ σ oa h
      simp only [argsOut, Option.some.injEq] at h
      subst h
      exact QuietPre.nil bi tf
  | cons e es ih =>
      intro Γ σ oa h
      simp only [argsOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, os, hos, rfl⟩ := h
      exact QuietPre.append (quietPre_atomOut bi tf σ e ho) (ih o.σ hos)

/-- The leakage after a part has no event when no continuation has one. -/
theorem nfTrace_contLeak_nil (o : Outcome × Env) (k : Value → Env → SrcLeak)
    (hk : ∀ w e, nfTrace (k w e) = []) : nfTrace (contLeak o k) = [] := by
  unfold contLeak
  split <;> first | rfl | exact hk _ _

/-- A list of atoms has no source event. -/
theorem nfTrace_srcArgsLeakNF_atoms (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} :
    ∀ (es : List ImpExpr) (σ : NfEnv Γ) {oa : ArgsOut Γ}, argsOut σ es = some oa →
      ∀ env, nfTrace (srcArgsLeakCl bi C.cl es fuel env) = [] := by
  intro es
  induction es generalizing Γ with
  | nil => intro σ oa _ env; simp only [srcArgsLeakCl, nfTrace]
  | cons e es ih =>
      intro σ oa h env
      simp only [argsOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, os, hos, rfl⟩ := h
      have he : nfTrace (srcLeakCl bi C.cl e fuel env) = [] := by
        cases e with
        | var x => rfl
        | lit l => rfl
        | _ => simp [atomOut] at ho
      simp only [srcArgsLeakCl, nfTrace, he, List.nil_append]
      exact nfTrace_contLeak_nil _ _ fun _ e1 => ih o.σ hos e1

/-! ## The constructs other than the loop and the conditional -/

open _root_.Hax.ContinueFlag (var_run lit_run unitVal_run letBind_run seq_run app_run
  args_nil_run args_cons_run)

/-- A literal is sound with leakage. -/
theorem lsound_lit (bi : Builtins) (fuel : Nat) (tgt : Option String) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (l : ImpLit) {o : Out Γ} (h : litOut tgt σ l = some o) :
    LSound bi C fuel (.lit l) σ o := by
  have hsrc : ∀ (env : Env) (v : Value) (env' : Env),
      (denote' bi fuel (.lit l)).run env = (.val v, env') → env' = env ∧ v = Value.ofLit l := by
    intro env v env' hr
    rw [lit_run] at hr
    cases hr
    exact ⟨rfl, rfl⟩
  have hl : ∀ env, nfTrace (srcLeakCl bi C.cl (.lit l) fuel env) = [] := fun _ => rfl
  cases l with
  | bool b =>
      simp only [litOut, Option.some.injEq] at h
      subst h
      exact lsound_bind1N bi fuel _ tgt σ _ (fun _ => rfl) _ hl fun env V v env' _ hr => by
        obtain ⟨rfl, rfl⟩ := hsrc env v env' hr
        exact ⟨rfl, b, rfl, rfl⟩
  | unit =>
      simp only [litOut, Option.some.injEq] at h
      subst h
      exact lsound_bind1N bi fuel _ tgt σ _ (fun _ => rfl) _ hl fun env V v env' _ hr => by
        obtain ⟨rfl, rfl⟩ := hsrc env v env' hr
        exact ⟨rfl, (), rfl, rfl⟩
  | int n | uintLit W n | sintLit W n =>
      simp only [litOut, Option.bind_eq_some_iff] at h
      obtain ⟨⟨t, v⟩, hlit, hs⟩ := h
      split at hs
      · rename_i hsome
        simp only [Option.some.injEq] at hs
        subst hs
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
        exact lsound_bind1N bi fuel _ tgt σ _ (fun _ => rfl) _ hl fun env V v' env' _ hr => by
          obtain ⟨rfl, rfl⟩ := hsrc env v' env' hr
          exact ⟨rfl, x, hx, ofLit_enc hlit hx⟩
      · cases hs

/-- An atom is sound with leakage. -/
theorem lsound_atom (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ)
    (a : ImpExpr) {o : Out Γ} (h : atomOut σ a = some o) : LSound bi C fuel a σ o := by
  cases a with
  | var x =>
      simp only [atomOut, Option.map_eq_some_iff] at h
      obtain ⟨⟨t, r⟩, hx, rfl⟩ := h
      intro env V v env' hrel hrun tf
      rw [var_run] at hrun
      rw [hrel x t r hx] at hrun
      cases hrun
      exact ⟨V, rfl, hrel, rfl⟩
  | lit l => exact lsound_lit bi fuel none σ l h
  | _ => simp [atomOut] at h

/-- A sequence of two outputs sound with leakage is sound with leakage. -/
theorem lsound_seq (bi : Builtins) (fuel : Nat) {a b : ImpExpr} {Γ : Ctxt nfDialect}
    {σ : NfEnv Γ} {oa : Out Γ} (ha : LSound bi C fuel a σ oa) {ob : Out oa.Δ}
    (hb : LSound bi C fuel b oa.σ ob) : LSound bi C fuel (.seq a b) σ (oa.comp ob) := by
  intro env V v env' hrel hrun tf
  obtain ⟨ra, e1, h1⟩ := run_val_split (denote' bi fuel a) env
  cases ra with
  | val va =>
      obtain ⟨W1, hW1, hrel1, rfl⟩ := ha env V va e1 hrel h1 tf
      rw [seq_run_val bi fuel b h1 (enc_ne_controlFlow _ _)] at hrun
      obtain ⟨W2, hW2, hrel2, rfl⟩ := hb e1 W1 v env' hrel1 hrun tf
      refine ⟨W2, ?_, hrel2, rfl⟩
      show PLeak bi C tf (oa.pre.append ob.pre) V = _
      rw [PLeak_append_some hW1 hW2]
      simp only [srcLeakCl, h1, contLeak_enc, nfTrace]
      rfl
  | _ => rw [seq_run, h1] at hrun; cases hrun

/-- A binding of an output sound with leakage, followed by an output sound with leakage from
    the environment of names with the bound name, is sound with leakage. -/
theorem lsound_letBind (bi : Builtins) (fuel : Nat) (x : String) {v b : ImpExpr}
    {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {ov : Out Γ} (hv : LSound bi C fuel v σ ov)
    {ob : Out ov.Δ} (hb : LSound bi C fuel b ((x, ⟨ov.t, ov.res⟩) :: ov.σ) ob) :
    LSound bi C fuel (.letBind x v b) σ (ov.comp ob) := by
  intro env V w env' hrel hrun tf
  obtain ⟨rv, e1, h1⟩ := run_val_split (denote' bi fuel v) env
  cases rv with
  | val wv =>
      obtain ⟨W1, hW1, hrel1, rfl⟩ := hv env V wv e1 hrel h1 tf
      rw [letBind_run_val bi fuel x b h1 (enc_ne_controlFlow _ _)] at hrun
      obtain ⟨W2, hW2, hrel2, rfl⟩ := hb _ W1 w env' (hrel1.cons x ov.t ov.res) hrun tf
      refine ⟨W2, ?_, hrel2, rfl⟩
      show PLeak bi C tf (ov.pre.append ob.pre) V = _
      rw [PLeak_append_some hW1 hW2]
      simp only [srcLeakCl, h1, contLeak_enc, nfTrace]
      rfl
  | _ => rw [letBind_run, h1] at hrun; cases hrun

/-- An assignment of an output sound with leakage is sound with leakage. -/
theorem lsound_assign (bi : Builtins) (fuel : Nat) (x : String) (tgt : Option String)
    {r : ImpExpr} {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {o : Out Γ} (hr : LSound bi C fuel r σ o) :
    LSound bi C fuel (.assign x r) σ
      (o.comp (bind1N tgt ((x, ⟨o.t, o.res⟩) :: o.σ) .constUnit .nil)) := by
  intro env V w env' hrel hrun tf
  obtain ⟨rv, e1, h1⟩ := run_val_split (denote' bi fuel r) env
  cases rv with
  | val wv =>
      obtain ⟨W1, hW1, hrel1, rfl⟩ := hr env V wv e1 hrel h1 tf
      rw [assign_run_val bi fuel x h1 (enc_ne_controlFlow _ _)] at hrun
      cases hrun
      refine ⟨W1.extend (), ?_, (hrel1.cons x o.t o.res).mapV (fun v => Var.there v)
        fun _ _ => rfl, rfl⟩
      have h2 := PLeak_bind1N_quiet (C := C) bi tf tgt ((x, ⟨o.t, o.res⟩) :: o.σ) .constUnit
        (fun _ => rfl) .nil W1
      have hs : srcLeakCl bi C.cl (.assign x r) fuel env = srcLeakCl bi C.cl r fuel env := by
        simp only [srcLeakCl]
      have h2' : PLeak bi C tf (bind1N tgt ((x, ⟨o.t, o.res⟩) :: o.σ) .constUnit .nil).pre W1 =
          some (W1.extend (show NfTy.unit.denote from ()), []) := h2.trans rfl
      have h3 := PLeak_append_some hW1 h2'
      rw [List.append_nil] at h3
      rw [hs]
      exact h3
  | _ =>
      simp only [denote', StateT.run, bind, StateT.bind, pure, modify, modifyGet,
        MonadStateOf.modifyGet] at h1 hrun
      rw [h1] at hrun
      cases hrun

/-- **The arguments of a call are sound with leakage** when the front is sound with leakage
    for each argument. -/
theorem lsound_args (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (fuel : Nat) (es : List ImpExpr)
    (H : ∀ e ∈ es, ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ},
      impToNF sigOf none σ e = some o → LSound bi C fuel e σ o) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {oa : ArgsOut Γ}, impArgsNF sigOf σ es = some oa →
    ∀ (env : Env) (V : Valuation Γ) (vals : List Value) (env' : Env), EnvRel σ env V →
    (denoteArgs' bi fuel es).run env = (some vals, env') →
    ∀ tf, ∃ W, PLeak bi C tf oa.pre V = some (W, nfTrace (srcArgsLeakCl bi C.cl es fuel env)) ∧
      EnvRel oa.σ env' W ∧ vals = encAll oa.as (Expr.lookupArgs oa.vs W) := by
  induction es with
  | nil =>
      intro Γ σ oa h env V vals env' hrel hr tf
      simp only [impArgsNF, Option.some.injEq] at h
      subst h
      rw [args_nil_run] at hr
      cases hr
      exact ⟨V, rfl, hrel, rfl⟩
  | cons e es ih =>
      intro Γ σ oa h env V vals env' hrel hr tf
      simp only [impArgsNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, os, hos, rfl⟩ := h
      obtain ⟨a, e1, h1⟩ := run_val_split (denote' bi fuel e) env
      cases a with
      | val v =>
          obtain ⟨W1, hW1, hrel1, rfl⟩ :=
            H e List.mem_cons_self σ ho env V v e1 hrel h1 tf
          rw [args_cons_run_val bi fuel es h1 (enc_ne_controlFlow _ _)] at hr
          obtain ⟨m, e2, h2⟩ := run_val_split (denoteArgs' bi fuel es) e1
          rw [h2] at hr
          cases m with
          | none => cases hr
          | some vals' =>
              cases hr
              obtain ⟨W2, hW2, hrel2, rfl⟩ :=
                ih (fun e' he' => H e' (List.mem_cons_of_mem _ he')) o.σ hos e1 W1 vals' e2
                  hrel1 h2 tf
              refine ⟨W2, ?_, hrel2, ?_⟩
              · show PLeak bi C tf (o.pre.append os.pre) V = _
                rw [PLeak_append_some hW1 hW2]
                simp only [srcArgsLeakCl, h1, contLeak_enc, nfTrace]
              · show _ :: _ = enc o.t ((os.pre.wk o.res).lookup W2) :: _
                rw [@NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ tf _ _ _ os.pre
                  o.res _ _ (PLeak_den hW2)]
      | _ =>
          rw [args_cons_run, h1] at hr
          cases hr

/-- A call of a builtin is sound with leakage under `TypedCalls`, for a call leakage that
    agrees with the builtins, when the front is sound with leakage for each argument: its
    events are those of the arguments followed by the events of the call leakage of the call
    on the argument values. -/
theorem lsound_app (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (hC : C.Agrees bi) (fuel : Nat) (tgt : Option String) (f : String)
    (args : List ImpExpr) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (HA : ∀ e ∈ args, ∀ {Γ' : Ctxt nfDialect} (σ' : NfEnv Γ') {o' : Out Γ'},
      impToNF sigOf none σ' e = some o' → LSound bi C fuel e σ' o')
    (h : impToNF sigOf tgt σ (.app f args) = some o) : LSound bi C fuel (.app f args) σ o := by
  simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨oa, hoa, r, hr, rfl⟩ := h
  intro env V v env' hrel hrun tf
  obtain ⟨m, e1, h1⟩ := run_val_split (denoteArgs' bi fuel args) env
  rw [app_run, h1] at hrun
  cases m with
  | none => cases hrun
  | some vals =>
      obtain ⟨W, hW, hrel1, rfl⟩ :=
        lsound_args bi sigOf fuel args HA σ hoa env V vals e1 hrel h1 tf
      dsimp only at hrun
      cases hb : bi f (encAll oa.as (Expr.lookupArgs oa.vs W)) with
      | none => rw [hb] at hrun; cases hrun
      | some w =>
          rw [hb] at hrun
          cases hrun
          obtain ⟨y, hy, rfl⟩ := hT f oa.as r hr _ _ hb
          refine ⟨W.extend y, ?_, hrel1.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩
          have hcall : (tableOf bi).call f oa.as r (Expr.lookupArgs oa.vs W) = some y := by
            simp only [tableOf, hb, Option.bind_some, hy]
          have hstep : PLeak bi C tf (.var (mkEN tgt (.call f oa.as r) oa.vs) .nil) W =
              some (W.extend y, C.ce f oa.as r (Expr.lookupArgs oa.vs W)) := by
            simp only [PLeak, NFPre.leakRunE]
            rw [opEv_mkEN C tgt (.call f oa.as r) oa.vs W]
            cases tgt <;>
            · simp only [mkEN, Expr.denoteM, nfDenote_denoteM]
              change ((tableOf bi).call f oa.as r (Expr.lookupArgs oa.vs W)).bind
                (fun x => Option.map (fun q => (q.1,
                  C.ce f oa.as r (Expr.lookupArgs oa.vs W) ++ q.2))
                  (some (W.extend x, []))) = _
              simp only [hcall, Option.bind_some, Option.map_some, List.append_nil]
          show PLeak bi C tf (oa.pre.append _) V = _
          rw [PLeak_append_some hW hstep, hC f oa.as r _ y hcall]
          simp only [srcLeakCl, h1, nfTrace]

/-- A tuple of atoms is sound with leakage, with no event. -/
theorem lsound_tuple (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (fuel : Nat) (tgt : Option String) (es : List ImpExpr) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.tuple es) = some o) : LSound bi C fuel (.tuple es) σ o := by
  have hs := tuple_sound bi sigOf fuel tgt es σ h
  simp only [impToNF, Option.map_eq_some_iff] at h
  obtain ⟨oa, hoa, rfl⟩ := h
  intro env V v env' hrel hrun tf
  obtain ⟨W, hW, hr, hv⟩ := hs env V v env' hrel hrun tf
  refine ⟨W, ?_, hr, hv⟩
  have hq : QuietPre bi C tf (oa.pre.append (tupleOut tgt oa.as oa.vs).2.1) :=
    QuietPre.append (quietPre_argsOut bi tf es σ hoa) (quietPre_tupleOut bi tf tgt oa.as oa.vs)
  have ht : nfTrace (srcLeakCl bi C.cl (.tuple es) fuel env) = [] := by
    simp only [srcLeakCl]
    exact nfTrace_srcArgsLeakNF_atoms bi fuel es σ hoa env
  rw [ht]
  show PLeak bi C tf (oa.pre.append (tupleOut tgt oa.as oa.vs).2.1) V = _
  rw [hq]
  rw [show PDen bi tf (oa.pre.append (tupleOut tgt oa.as oa.vs).2.1) V = some W from hW]
  rfl

/-- The simulation with leakage from the simulation and the events of the prefix: a prefix
    leakage run that succeeds ends at the valuation of the simulation. -/
theorem lsound_of_sound {bi : Builtins} {fuel : Nat} {e : ImpExpr} {Γ : Ctxt nfDialect}
    {σ : NfEnv Γ} {o : Out Γ} (hs : Sound bi fuel e σ o)
    (ht : ∀ (env : Env) (V : Valuation Γ) (v : Value) (env' : Env), EnvRel σ env V →
      (denote' bi fuel e).run env = (.val v, env') →
      ∀ tf, ∃ W, PLeak bi C tf o.pre V = some (W, nfTrace (srcLeakCl bi C.cl e fuel env))) :
    LSound bi C fuel e σ o := by
  intro env V v env' hrel hrun tf
  obtain ⟨W, hW, hr, hv⟩ := hs env V v env' hrel hrun tf
  obtain ⟨W', hW'⟩ := ht env V v env' hrel hrun tf
  have hd := PLeak_den hW'
  rw [hW, Option.some.injEq] at hd
  subst hd
  exact ⟨W, hW', hr, hv⟩

/-! ## The conditional -/

/-- The prefix leakage run of the branch of `condOut` whose taken arm runs to the results `r`
    with the events `t`: the event `branch` of the condition, then `t`. -/
theorem PLeak_ifThenElse_some (bi : Builtins) (tf : Nat) {Γ : Ctxt nfDialect}
    {rs : List NfTy} (cond : Var Γ NfTy.bit) (thn els : NFProg nfDialect Γ rs)
    (V : Valuation Γ) {r : Valuation (d := nfDialect) rs} {t : List CTLeak}
    (hr : nfLeakRunE bi C tf (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) = true then thn
      else els) V = some (r, t)) :
    PLeak bi C tf (.ifThenElse cond thn els .nil : NFPre nfDialect Γ (rs ++ Γ)) V =
      some (hvAppend r V, .branch (HasBoolBit.toBool (d := nfDialect) (cond.lookup V)) ::
        (t ++ [])) := by
  have hr' : (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) = true then
      nfLeakRunE bi C tf thn V else nfLeakRunE bi C tf els V) = some (r, t) := by
    split
    · rename_i hc; rw [if_pos hc] at hr; exact hr
    · rename_i hc; rw [if_neg hc] at hr; exact hr
  simp only [PLeak, NFPre.leakRunE]
  rw [hr']
  rfl

/-- **A conditional is sound with leakage**, when the front is sound with leakage for its
    condition and its arms: its events are those of the condition, the event `branch` of the
    condition, and the events of the arm taken. -/
theorem lsound_cond (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (fuel : Nat) (tgt : Option String) (c a b : ImpExpr) {Γ : Ctxt nfDialect} (σ : NfEnv Γ)
    {o : Out Γ} (h : impToNF sigOf tgt σ (.ifThenElse c a b) = some o)
    (HC : ∀ {o' : Out Γ}, impToNF sigOf none σ c = some o' → LSound bi C fuel c σ o')
    (HA : ∀ {Γ' : Ctxt nfDialect} (σ' : NfEnv Γ') {o' : Out Γ'},
      impToNF sigOf none σ' a = some o' → LSound bi C fuel a σ' o')
    (HB : ∀ {Γ' : Ctxt nfDialect} (σ' : NfEnv Γ') {o' : Out Γ'},
      impToNF sigOf none σ' b = some o' → LSound bi C fuel b σ' o') :
    LSound bi C fuel (.ifThenElse c a b) σ o := by
  have hS := cond_sound bi sigOf fuel tgt c a b σ h (fun h' => (HC h').sound)
    (fun σ' _ h' => (HA σ' h').sound) (fun σ' _ h' => (HB σ' h').sound)
  refine lsound_of_sound hS ?_
  simp only [impToNF, Option.bind_eq_some_iff] at h
  obtain ⟨oc, hoc, h⟩ := h
  have hC := HC hoc
  obtain ⟨Δc, tc, prec, σc, resc⟩ := oc
  by_cases htc : tc = NfTy.bit
  · subst htc
    rw [dif_pos rfl] at h
    intro env V r env' hrel hrun tf
    obtain ⟨rc, e1, h1⟩ := run_val_split (denote' bi fuel c) env
    cases rc with
    | val vc =>
        obtain ⟨W1, hW1, hrel1, rfl⟩ := hC env V vc e1 hrel h1 tf
        rw [ifThenElse_run_bool bi fuel a b h1] at hrun
        unfold condOut at h
        obtain ⟨oa, hoa, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨ob, hob, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨Δb, tb, preb, σb, resb⟩ := ob
        by_cases ht : tb = oa.t
        · subst ht
          rw [dif_pos rfl] at h
          obtain ⟨ra, hra, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨rb, hrb, rfl⟩ := Option.map_eq_some_iff.mp h
          cases hk : resc.lookup W1 with
          | true =>
              have hrun' : (denote' bi fuel a).run e1 = (.val r, env') := by
                simpa [hk] using hrun
              obtain ⟨W2, hW2, -, -⟩ := HA σc hoa e1 W1 r env' hrel1 hrun' tf
              have harm : nfLeakRunE bi C tf (oa.pre.plug (.ret (.cons oa.res ra))) W1 =
                  some (Expr.lookupArgs (.cons oa.res ra) W2,
                    nfTrace (srcLeakCl bi C.cl a fuel e1) ++ []) := by
                rw [nfLeakRunE_plug, hW2]; rfl
              have hstep := PLeak_ifThenElse_some bi tf resc (oa.pre.plug (.ret (.cons oa.res ra)))
                ((Out.mk Δb oa.t preb σb resb).pre.plug (.ret (.cons resb rb))) W1
                (r := Expr.lookupArgs (.cons oa.res ra) W2)
                (by
                  have : HasBoolBit.toBool (d := nfDialect) (resc.lookup W1) = true := hk
                  rw [if_pos this]; exact harm)
              refine ⟨hvAppend (Expr.lookupArgs (.cons oa.res ra) W2) W1,
                (PLeak_append_some hW1 hstep).trans ?_⟩
              simp only [srcLeakCl, h1, hk, enc, nfTrace, nfEv, List.append_nil]
              rfl
          | false =>
              have hrun' : (denote' bi fuel b).run e1 = (.val r, env') := by
                simpa [hk] using hrun
              obtain ⟨W2, hW2, -, -⟩ := HB σc hob e1 W1 r env' hrel1 hrun' tf
              have harm : nfLeakRunE bi C tf
                  ((Out.mk Δb oa.t preb σb resb).pre.plug (.ret (.cons resb rb))) W1 =
                  some (Expr.lookupArgs (.cons resb rb) W2,
                    nfTrace (srcLeakCl bi C.cl b fuel e1) ++ []) := by
                rw [nfLeakRunE_plug]
                rw [show PLeak bi C tf preb W1 = _ from hW2]
                rfl
              have hstep := PLeak_ifThenElse_some bi tf resc (oa.pre.plug (.ret (.cons oa.res ra)))
                ((Out.mk Δb oa.t preb σb resb).pre.plug (.ret (.cons resb rb))) W1
                (r := Expr.lookupArgs (.cons resb rb) W2)
                (by
                  have : HasBoolBit.toBool (d := nfDialect) (resc.lookup W1) = false := hk
                  rw [if_neg (by rw [this]; exact Bool.false_ne_true)]; exact harm)
              refine ⟨hvAppend (Expr.lookupArgs (.cons resb rb) W2) W1,
                (PLeak_append_some hW1 hstep).trans ?_⟩
              simp only [srcLeakCl, h1, hk, enc, nfTrace, nfEv, List.append_nil]
              rfl
        · rw [dif_neg ht] at h
          cases h
    | _ =>
        rw [_root_.Hax.ContinueFlag.ifThenElse_run, h1] at hrun
        cases hrun
  · rw [dif_neg htc] at h
    cases h

/-! ## The counted loop -/

open _root_.Hax.ContinueFlag (forLoop_ge_run forLoop_zero_run forLoop_succ_run)
open _root_.Hax.InlineLocalClosures (frameOk)

/-- A value that is not a control-flow value. -/
theorem isControlFlow_false {w : Value} (h : ∀ b u, w ≠ .controlFlow b u) :
    w.isControlFlow = false := by
  cases w <;> first | rfl | exact absurd rfl (h _ _)

/-- The trips of a counted loop from a counter at or above the upper bound leave no event. -/
theorem forLeak_ge (bi : Builtins) (i : String) (body : ImpExpr) (lb : Nat → Env → SrcLeak)
    (fuel : Nat) {lo hi : Int} (h : hi ≤ lo) (env : Env) :
    forLeak bi i body lb fuel lo hi env = .nil := by
  cases fuel with
  | zero => rfl
  | succ n => simp only [forLeak, if_pos (show lo ≥ hi from h)]

/-- **The loop with leakage.** `ImpToNF.loop_sound` for a step with events: let every run of
    the body from an environment satisfying `Inv`, extended with the counter `lo + k`, to a
    value be matched by the step at `k` with the events of the transformed source leakage of
    the body. Then a run of `denoteForLoop'` from the counter `lo + k` to a value, with `m`
    trips left, is matched by the iteration of the step over `k, …, k + m - 1`, with the events
    of the transformed leakage `forLeak` of the trips. -/
theorem loop_leak (bi : Builtins) (i : String) (body : ImpExpr) (lo h : Int) {cs : List NfTy}
    (step : Nat → Valuation (d := nfDialect) cs →
      Option (Valuation (d := nfDialect) cs × List CTLeak))
    (Inv : Env → Valuation (d := nfDialect) cs → Prop)
    (HS : ∀ (k fuel : Nat) (env : Env) (acc : Valuation (d := nfDialect) cs) (rb : Outcome)
      (e₂ : Env), k < 2 ^ 64 → lo + (k : Int) < h → Inv env acc →
      (denote' bi fuel body).run (env.extend i (.int (lo + k))) = (rb, e₂) →
      (∃ w, rb = .val w) → ∃ w acc', rb = .val w ∧ (∀ b u, w ≠ .controlFlow b u) ∧
        step k acc =
          some (acc', nfTrace (srcLeakCl bi C.cl body fuel (env.extend i (.int (lo + k))))) ∧
        Inv e₂ acc') :
    ∀ (m k fuel : Nat) (env : Env) (acc : Valuation (d := nfDialect) cs) (r : Value) (e : Env),
      (h - (lo + k)).toNat = m → k + m < 2 ^ 64 → Inv env acc →
      (_root_.Hax.denoteForLoop' bi fuel i (lo + k) h body).run env = (.val r, e) →
      ∃ acc', forIterLeak step (List.range' k m) acc =
          some (acc', nfTrace (forLeak bi i body (srcLeakCl bi C.cl body) fuel (lo + k) h env)) ∧
        Inv e acc' := by
  intro m
  induction m with
  | zero =>
      intro k fuel env acc r e hm _ hinv hrun
      rw [forLoop_ge_run bi fuel i _ h body env (by omega)] at hrun
      cases hrun
      refine ⟨acc, ?_, hinv⟩
      rw [forLeak_ge bi i body _ fuel (by omega) env]
      rfl
  | succ m ih =>
      intro k fuel env acc r e hm hk hinv hrun
      have hlt : lo + k < h := by omega
      cases fuel with
      | zero =>
          rw [forLoop_zero_run bi i _ h body env hlt] at hrun
          cases hrun
      | succ f =>
          obtain ⟨rb, e₂, hb⟩ := run_val_split (denote' bi (f + 1) body)
            (env.extend i (.int (lo + k)))
          cases rb with
          | val w =>
              obtain ⟨w, acc', hw, hcf, hacc', hinv'⟩ := HS k (f + 1) env acc _ e₂
                (by omega) hlt hinv hb ⟨w, rfl⟩
              cases hw
              rw [forLoop_succ_run_val bi f i body hlt hb hcf] at hrun
              have hk1 : lo + k + 1 = lo + ((k + 1 : Nat) : Int) := by push_cast; ring
              rw [hk1] at hrun
              obtain ⟨acc'', hfold, hinv''⟩ :=
                ih (k + 1) f e₂ acc' r e (by omega) (by omega) hinv' hrun
              refine ⟨acc'', ?_, hinv''⟩
              rw [List.range'_succ]
              simp only [forIterLeak, hacc', Option.bind_some, hfold, Option.map_some]
              simp only [forLeak, if_neg (show ¬ (lo + (k : Int) ≥ h) by omega), hb,
                tripCont_val (isControlFlow_false hcf), hk1, nfTrace]
          | _ =>
              rw [forLoop_succ_run bi f i _ h body env hlt, hb] at hrun
              cases hrun

/-- The trips of a reverse counted loop on an empty range leave no event. -/
theorem forRevLeak_ge (bi : Builtins) (i : String) (body : ImpExpr)
    (lb : Nat → Env → SrcLeak) (fuel : Nat) {lo hi : Int} (h : hi ≤ lo) (env : Env) :
    forRevLeak bi i body lb fuel lo hi env = .nil := by
  cases fuel with
  | zero => rfl
  | succ n => simp only [forRevLeak, if_pos (show lo ≥ hi from h)]

/-- **The reverse loop with leakage.** `loop_leak` for `denoteForLoopRev'`: with the step at
    `k` matching the runs of the body from the counter `h - 1 - k`, a run of
    `denoteForLoopRev'` on the range from `lo` to `h - k`, with `m` trips left, is matched by
    the iteration of the step over `k, …, k + m - 1`, with the events of the transformed
    leakage `forRevLeak` of the trips. -/
theorem loopRev_leak (bi : Builtins) (i : String) (body : ImpExpr) (lo h : Int)
    {cs : List NfTy}
    (step : Nat → Valuation (d := nfDialect) cs →
      Option (Valuation (d := nfDialect) cs × List CTLeak))
    (Inv : Env → Valuation (d := nfDialect) cs → Prop)
    (HS : ∀ (k fuel : Nat) (env : Env) (acc : Valuation (d := nfDialect) cs) (rb : Outcome)
      (e₂ : Env), k < 2 ^ 64 → lo + (k : Int) < h → Inv env acc →
      (denote' bi fuel body).run (env.extend i (.int (h - 1 - k))) = (rb, e₂) →
      (∃ w, rb = .val w) → ∃ w acc', rb = .val w ∧ (∀ b u, w ≠ .controlFlow b u) ∧
        step k acc =
          some (acc', nfTrace (srcLeakCl bi C.cl body fuel (env.extend i (.int (h - 1 - k))))) ∧
        Inv e₂ acc') :
    ∀ (m k fuel : Nat) (env : Env) (acc : Valuation (d := nfDialect) cs) (r : Value) (e : Env),
      (h - k - lo).toNat = m → k + m < 2 ^ 64 → Inv env acc →
      (_root_.Hax.denoteForLoopRev' bi fuel i lo (h - k) body).run env = (.val r, e) →
      ∃ acc', forIterLeak step (List.range' k m) acc =
          some (acc', nfTrace (forRevLeak bi i body (srcLeakCl bi C.cl body) fuel lo (h - k) env)) ∧
        Inv e acc' := by
  intro m
  induction m with
  | zero =>
      intro k fuel env acc r e hm _ hinv hrun
      rw [forLoopRev_ge_run bi fuel i lo _ body env (by omega)] at hrun
      cases hrun
      refine ⟨acc, ?_, hinv⟩
      rw [forRevLeak_ge bi i body _ fuel (by omega) env]
      rfl
  | succ m ih =>
      intro k fuel env acc r e hm hk hinv hrun
      have hlt : lo < h - k := by omega
      cases fuel with
      | zero =>
          rw [forLoopRev_zero_run bi i lo _ body env hlt] at hrun
          cases hrun
      | succ f =>
          have hc : h - (k : Int) - 1 = h - 1 - k := by ring
          obtain ⟨rb, e₂, hb⟩ := run_val_split (denote' bi (f + 1) body)
            (env.extend i (.int (h - 1 - k)))
          cases rb with
          | val w =>
              obtain ⟨w, acc', hw, hcf, hacc', hinv'⟩ := HS k (f + 1) env acc _ e₂
                (by omega) (by omega) hinv hb ⟨w, rfl⟩
              cases hw
              rw [← hc] at hb hacc'
              rw [forLoopRev_succ_run_val bi f i body hlt hb hcf] at hrun
              have hk1 : h - (k : Int) - 1 = h - ((k + 1 : Nat) : Int) := by push_cast; ring
              rw [hk1] at hrun
              obtain ⟨acc'', hfold, hinv''⟩ :=
                ih (k + 1) f e₂ acc' r e (by omega) (by omega) hinv' hrun
              refine ⟨acc'', ?_, hinv''⟩
              rw [← hk1] at hfold
              rw [List.range'_succ]
              simp only [forIterLeak, hacc', Option.bind_some, hfold, Option.map_some]
              simp only [forRevLeak, if_neg (show ¬ (lo ≥ h - (k : Int)) by omega), hb,
                tripCont_val (isControlFlow_false hcf), nfTrace]
          | _ =>
              rw [← hc] at hb
              rw [forLoopRev_succ_run bi f i lo _ body env hlt, hb] at hrun
              cases hrun

/-- The counter binding `ctrOut` has no event. -/
theorem quietPre_ctrOut (bi : Builtins) (tf : Nat) {Γ₃ : Ctxt nfDialect} (cs : List NfTy)
    (i : String) (σB : NfEnv (cs ++ NfTy.word 64 :: Γ₃)) (loV : Var Γ₃ NfTy.int)
    (rev : Option (Var Γ₃ (NfTy.word 64))) : QuietPre bi C tf (ctrOut cs i σB loV rev).pre := by
  cases rev with
  | none => exact QuietPre.var bi tf (some i) .ctr (fun _ => rfl) _
  | some m =>
      exact QuietPre.append (QuietPre.var bi tf none (.bin .sub 64) (fun _ => rfl) _)
        (QuietPre.var bi tf (some i) .ctr (fun _ => rfl) _)

/-- The prefix leakage run of a counted loop whose iteration over the trips `0, …, n - 1`
    succeeds with the events `t`, followed by a prefix with no event: the event `trip n`, then
    `t`. -/
theorem PLeak_forLoop_some (bi : Builtins) (tf : Nat) {Γ Δ : Ctxt nfDialect}
    {cs : List NfTy} {count : Var Γ (NfTy.word 64)} {inits : HVector (fun t => Var Γ t) cs}
    {body : NFProg nfDialect (cs ++ NfTy.word 64 :: Γ) cs} {p : NFPre nfDialect (cs ++ Γ) Δ}
    {V : Valuation Γ} {acc : Valuation (d := nfDialect) cs} {W : Valuation Δ} {t : List CTLeak}
    (n : Nat) (hn : (count.lookup V).toNat = n)
    (hfold : forIterLeak (fun j a => nfLeakRunE bi C tf body
      (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
      (List.range' 0 n) (Expr.lookupArgs inits V) = some (acc, t))
    (hp : PLeak bi C tf p (hvAppend acc V) = some (W, [])) :
    PLeak bi C tf (.forLoop count inits body p) V = some (W, .trip n :: (t ++ [])) := by
  show (forIterLeak (fun j a => nfLeakRunE bi C tf body
      (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
      (List.range (count.lookup V).toNat) (Expr.lookupArgs inits V)).bind (fun r =>
        (PLeak bi C tf p (hvAppend r.1 V)).map fun q =>
          (q.1, CTLeak.trip (count.lookup V).toNat :: (r.2 ++ q.2))) = _
  rw [hn, List.range_eq_range', hfold, Option.bind_some, hp]
  rfl

/-- **The counted loop of the front with leakage.** Under the hypotheses of
    `ImpToNF.loopOut_sound`, with the prefix `pre₀` run by its leakage run to `V₃` with the
    events `tpre` and the body sound with leakage, the output of `loopOut` emits `tpre`, the
    trip count, and the transformed leakage `forLeak` of the trips of the source loop. -/
theorem loopOut_leak (bi : Builtins) (fuel : Nat) (body : ImpExpr) (tgt : Option String)
    {Γ Γ₃ : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γ₃) (σ₃ : NfEnv Γ₃)
    (loV : Var Γ₃ NfTy.int) (tripV : Var Γ₃ (NfTy.word 64))
    (rev : Option (Var Γ₃ (NfTy.word 64))) (i : String) (xs : List String)
    (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ)) {o : Out Γ}
    (h₀ : loopOut tgt pre₀ σ₃ loV tripV rev i xs cs inits rec = some o)
    (HB : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) {o' : Out Δ}, rec σ' = some o' →
      ∀ fuel', LSound bi C fuel' body σ' o')
    (hlen : xs.length = cs.length)
    (hfr : ∀ x, x ∉ xs → x ≠ i → ∀ q, σ₃.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) body = true)
    (env : Env) (V : Valuation Γ) (V₃ : Valuation Γ₃) (tf : Nat) (tpre : List CTLeak)
    (hpre : PLeak bi C tf pre₀ V = some (V₃, tpre)) (hrel : EnvRel σ₃ env V₃)
    (hcar : CarriedRel env xs cs (Expr.lookupArgs inits V₃)) (lo h : Int)
    (hlo : loV.lookup V₃ = lo) (htrip : tripV.lookup V₃ = BitVec.ofNat 64 (h - lo).toNat)
    (hM : (h - lo).toNat < 2 ^ 64) (hlo0 : 0 ≤ lo) (hh64 : h ≤ 2 ^ 64)
    (hrev : ∀ m, rev = some m →
      (m.lookup V₃ : BitVec 64) = BitVec.ofNat 64 (h - lo).toNat - 1) (r : Value)
    (env' : Env)
    (hrun : (match rev with
      | none => _root_.Hax.denoteForLoop' bi fuel i lo h body
      | some _ => _root_.Hax.denoteForLoopRev' bi fuel i lo h body).run env = (.val r, env')) :
    ∃ W, PLeak bi C tf o.pre V = some (W, tpre ++ (.trip (h - lo).toNat ::
      (nfTrace (match rev with
        | none => forLeak bi i body (srcLeakCl bi C.cl body) fuel lo h env
        | some _ => forRevLeak bi i body (srcLeakCl bi C.cl body) fuel lo h env) ++ []))) := by
  simp only [loopOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₀
  obtain ⟨ob, hob, rets, hrets, rfl⟩ := h₀
  let Inv : Env → Valuation (d := nfDialect) cs → Prop := fun e acc =>
    CarriedRel e xs cs acc ∧ FrameRel σ₃ i xs e V₃
  let oC := ctrOut cs i (loopEnv σ₃ i xs cs (headVars cs)
    fun v => Var.shiftApp (d := nfDialect) cs v.there) loV rev
  have hcv : ∀ k : Nat, lo + (k : Int) < h →
      ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64)) =
        (rev.map fun m => (m.lookup V₃ : BitVec 64)).elim (lo + k) fun _ => h - 1 - k :=
    fun k hk => ctrVal_trip lo h k hM hk (rev.map fun m => (m.lookup V₃ : BitVec 64))
      fun m hm => by
        obtain ⟨m', hm', hmm⟩ := Option.map_eq_some_iff.mp hm
        rw [← hmm]
        exact hrev m' hm'
  have HS : ∀ (k f : Nat) (e : Env) (acc : Valuation (d := nfDialect) cs) (rb : Outcome)
      (e₂ : Env), k < 2 ^ 64 → lo + (k : Int) < h → Inv e acc →
      (denote' bi f body).run
        (e.extend i (.int (ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64))))) =
        (rb, e₂) →
      (∃ w, rb = .val w) → ∃ w acc', rb = .val w ∧ (∀ b u, w ≠ .controlFlow b u) ∧
        nfLeakRunE bi C tf ((NFPre.append oC.pre ob.pre).plug (.ret rets))
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) =
          some (acc', nfTrace (srcLeakCl bi C.cl body f (e.extend i
            (.int (ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64))))))) ∧
        Inv e₂ acc' := by
    intro k f e acc rb e₂ hk hkh hinv hb hval
    obtain ⟨w, rfl⟩ := hval
    have hB : EnvRel (loopEnv σ₃ i xs cs (headVars cs)
        fun v => Var.shiftApp (d := nfDialect) cs v.there) e
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) :=
      EnvRel.loopEnv σ₃ i xs cs hlen (headVars cs) _
        (W := hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
        (by rw [lookupArgs_headVars]; exact hinv.1) hinv.2
        (by intro t v; rw [Var.lookup_shiftApp]; rfl)
    have hc : ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64)) < 2 ^ 64 := by
      rw [hcv k hkh]
      generalize (rev.map fun m => (m.lookup V₃ : BitVec 64)) = q
      cases q <;> simp only [Option.elim] <;> omega
    obtain ⟨Wc, hWc, hrelC, hencC⟩ := ctrOut_sound bi cs i _ loV rev acc V₃ k e hB hk lo hlo
      hlo0 hc
    have hpC : PLeak bi C tf oC.pre
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) =
        some (Wc, []) := by
      rw [quietPre_ctrOut bi tf cs i _ loV rev, hWc tf]
      rfl
    rw [← hencC] at hb
    obtain ⟨W', hW', hrel', rfl⟩ := HB _ hob f _ _ w e₂ (hrelC.cons i _ _) hb tf
    refine ⟨_, Expr.lookupArgs rets W', rfl, enc_ne_controlFlow _ _, ?_, ?_, ?_⟩
    · rw [nfLeakRunE_plug, PLeak_append_some hpC hW', hencC]
      simp only [Option.bind_some, List.nil_append]
      show Option.map _ (some (Expr.lookupArgs rets W', ([] : List CTLeak))) = _
      simp only [Option.map_some, List.append_nil]
    · exact CarriedRel.of_varsAt hrel' xs cs hrets
    · intro x hx hxi t v hl
      rw [denote'_keeps bi body (hfr x hx hxi _ hl) f _ hb (by rintro ⟨_, h⟩; cases h),
        Env.extend_other _ _ _ _ hxi]
      exact hinv.2 x hx hxi t v hl
  obtain ⟨accF, hfold⟩ : ∃ accF, forIterLeak (fun j a => nfLeakRunE bi C tf
      ((NFPre.append oC.pre ob.pre).plug (.ret rets))
      (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V₃)))
      (List.range' 0 (h - lo).toNat) (Expr.lookupArgs inits V₃) =
      some (accF, nfTrace (match rev with
        | none => forLeak bi i body (srcLeakCl bi C.cl body) fuel lo h env
        | some _ => forRevLeak bi i body (srcLeakCl bi C.cl body) fuel lo h env)) := by
    cases rev with
    | none =>
        have hrun0 : (_root_.Hax.denoteForLoop' bi fuel i (lo + ((0 : Nat) : Int)) h
            body).run env = (.val r, env') := by simpa using hrun
        obtain ⟨accF, hfold, -⟩ := loop_leak bi i body lo h _ Inv
          (fun k f e acc rb e₂ hk hkh hinv hb hval => HS k f e acc rb e₂ hk hkh hinv hb hval)
          ((h - lo).toNat) 0 fuel env (Expr.lookupArgs inits V₃) r env' (by simp)
          (by simpa using hM) ⟨hcar, fun x _ _ t v hl => hrel x t v hl⟩ hrun0
        have hl0 : lo + ((0 : Nat) : Int) = lo := by simp
        rw [hl0] at hfold
        exact ⟨accF, hfold⟩
    | some m =>
        have hrun0 : (_root_.Hax.denoteForLoopRev' bi fuel i lo (h - ((0 : Nat) : Int))
            body).run env = (.val r, env') := by simpa using hrun
        obtain ⟨accF, hfold, -⟩ := loopRev_leak bi i body lo h _ Inv
          (fun k f e acc rb e₂ hk hkh hinv hb hval => by
            have h1 := hcv k hkh
            simp only [Option.map_some, Option.elim] at h1
            rw [← h1] at hb ⊢
            exact HS k f e acc rb e₂ hk hkh hinv hb hval)
          ((h - lo).toNat) 0 fuel env (Expr.lookupArgs inits V₃) r env' (by simp)
          (by simpa using hM) ⟨hcar, fun x _ _ t v hl => hrel x t v hl⟩ hrun0
        have hl0 : h - ((0 : Nat) : Int) = h := by simp
        rw [hl0] at hfold
        exact ⟨accF, hfold⟩
  refine ⟨HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.unit) () (hvAppend accF V₃), ?_⟩
  refine PLeak_append_some hpre (PLeak_forLoop_some bi tf ((h - lo).toNat) ?_ hfold ?_)
  · rw [htrip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM]
  · exact (PLeak_bind1N_quiet bi tf tgt _ .constUnit (fun _ => rfl) .nil _).trans rfl

/-- The integer a counted-loop bound denotes, read off an encoded value, is the integer
    `NfTy.toInt?` reads. -/
theorem boundInt_enc {t : NfTy} {x : t.denote} {h : Int} (hx : NfTy.toInt? t x = some h) :
    boundInt (enc t x) = some h := by
  cases t <;> simp only [NfTy.toInt?, reduceCtorEq] at hx <;> cases hx <;> rfl

/-- **A counted loop is sound with leakage**, when the front is sound with leakage for its
    body: its events are the trip count and the events of the trips. -/
theorem lsound_forFold (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (fuel : Nat) (tgt : Option String) (i : String) (lo : Int) (hi body : ImpExpr)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.forFold i (.lit (.int lo)) hi body) = some o)
    (HB : ∀ {Γ' : Ctxt nfDialect} (σ' : NfEnv Γ') {o' : Out Γ'},
      impToNF sigOf none σ' body = some o' → ∀ fuel', LSound bi C fuel' body σ' o') :
    LSound bi C fuel (.forFold i (.lit (.int lo)) hi body) σ o := by
  have hS := forFold_sound bi sigOf fuel tgt i lo hi body σ h
    (fun σ' _ h' fuel' => (HB σ' h' fuel').sound)
  refine lsound_of_sound hS ?_
  simp only [impToNF, Option.bind_eq_some_iff] at h
  obtain ⟨oHi, hHi, hL⟩ := h
  split at hL
  case isFalse => cases hL
  rename_i hbd
  intro env V r env' hrel hrun tf
  obtain ⟨hv, e1, hh⟩ := forFold_hi_val bi fuel i lo hi body hrun
  have he1 : e1 = env := by
    have := atomOut_env bi fuel _ hi hHi env
    rw [hh] at this; exact this
  subst he1
  have hrelLo : EnvRel (bind1 σ (.ilit .int lo) .nil).σ e1
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo V) :=
    hrel.mapV (fun v => Var.there v) fun _ _ => rfl
  have hLo : PDen bi tf (bind1 σ (.ilit .int lo) .nil).pre V =
      some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo V) :=
    (PDen_bind1 bi tf σ (.ilit .int lo) .nil V).trans rfl
  obtain ⟨W2, hW2, hrel2, rfl⟩ := atomOut_sound bi fuel _ hi hHi e1 _ hv e1 hrelLo hh tf
  obtain ⟨hInt, htoInt, hloop⟩ := forFold_enc_run bi fuel i lo hi body hh hrun
  have hloW : (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res).lookup W2 = lo :=
    (@NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ tf _ _ _ oHi.pre _ _ _ hW2).trans
      rfl
  have hargsT : Expr.lookupArgs (HVector.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res)
      (HVector.cons oHi.res .nil)) W2 =
      HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo
        (HVector.cons (t := oHi.t) (oHi.res.lookup W2) .nil) := by
    show HVector.cons ((oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res).lookup W2)
      (HVector.cons (oHi.res.lookup W2) .nil) = _
    rw [hloW]
    rfl
  have hTrip : PDen bi tf (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).pre W2 =
      some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat) W2) := by
    refine (PDen_bind1 bi tf _ (.trip oHi.t) _ W2).trans ?_
    refine (congrArg (fun a => Option.map _ (nfDenoteOp (tableOf bi) (.trip oHi.t) a))
      hargsT).trans ?_
    show Option.map _ ((NfTy.toInt? oHi.t (oHi.res.lookup W2)).map
      fun hi => BitVec.ofNat 64 (hi - lo).toNat) = _
    rw [htoInt]
    rfl
  have hrelT : EnvRel (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).σ e1
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat) W2) :=
    hrel2.mapV (fun v => Var.there v) fun _ _ => rfl
  have hlitE : ∀ n, hi = .lit (.int n) → enc oHi.t (oHi.res.lookup W2) = .int n :=
    fun n hn => by
      subst hn
      rw [lit_run] at hh
      have h1 := (Prod.mk.inj hh).1
      injection h1 with h2
      exact h2.symm
  have hrange := bound_range hbd htoInt hlitE
  have hM := trip_lt_of_bound hbd htoInt hlitE
  -- the prefix before the loop has no event
  have hq : QuietPre bi C tf (((bind1 σ (.ilit .int lo) .nil).pre.append oHi.pre).append
      (bind1 oHi.σ (.trip oHi.t)
        (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).pre) :=
    QuietPre.append (QuietPre.append (QuietPre.var bi tf none _ (fun _ => rfl) _)
      (quietPre_atomOut bi tf _ hi hHi)) (QuietPre.var bi tf none _ (fun _ => rfl) _)
  have hpre := hq V
  rw [PDen_append_some bi tf (PDen_append_some bi tf hLo hW2) hTrip] at hpre
  obtain ⟨W, hW⟩ := loopOut_leak bi fuel body tgt _ _ _ _ _ i _ _ _ _ hL
    (fun σ' _ h' fuel' => HB σ' h' fuel')
    (by rw [List.length_map, entriesVars_length])
    (fun x hx hxi _ hl => frameOk_of_not_carried _ i body hl hxi hx)
    e1 V _ tf [] hpre hrelT
    (CarriedRel.of_entries hrelT _ (carried_lookup _ i body)) lo hInt hloW rfl
    hM hrange.1 (le_of_lt hrange.2) (fun _ h => by cases h) r env' hloop
  refine ⟨W, hW.trans ?_⟩
  -- the source trace
  have hhi : nfTrace (srcLeakCl bi C.cl hi fuel e1) = [] := by
    cases hi with
    | var x => rfl
    | lit l => rfl
    | _ => simp [atomOut] at hHi
  have hlo' : (denote' bi fuel (.lit (.int lo))).run e1 = (.val (.int lo), e1) :=
    lit_run bi fuel _ _
  simp only [srcLeakCl, boundsLeak, hlo', hh]
  rw [boundInt_enc htoInt]
  simp only [boundInt, nfTrace, nfEv, hhi, Nat.mod_eq_of_lt hM, List.nil_append,
    List.append_nil, List.cons_append]

/-- **A reverse counted loop is sound with leakage**, when the front is sound with leakage
    for its body: its events are the trip count and the events of the trips, from `hi - 1`
    down to `lo`. -/
theorem lsound_forFoldRev (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (fuel : Nat) (tgt : Option String) (i : String) (lo : Int) (hi body : ImpExpr)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.forFoldRev i (.lit (.int lo)) hi body) = some o)
    (HB : ∀ {Γ' : Ctxt nfDialect} (σ' : NfEnv Γ') {o' : Out Γ'},
      impToNF sigOf none σ' body = some o' → ∀ fuel', LSound bi C fuel' body σ' o') :
    LSound bi C fuel (.forFoldRev i (.lit (.int lo)) hi body) σ o := by
  have hS := forFoldRev_sound bi sigOf fuel tgt i lo hi body σ h
    (fun σ' _ h' fuel' => (HB σ' h' fuel').sound)
  refine lsound_of_sound hS ?_
  simp only [impToNF, Option.bind_eq_some_iff] at h
  obtain ⟨oHi, hHi, hL⟩ := h
  split at hL
  case isFalse => cases hL
  rename_i hbd
  intro env V r env' hrel hrun tf
  obtain ⟨hv, e1, hh⟩ := forFoldRev_hi_val bi fuel i lo hi body hrun
  have he1 : e1 = env := by
    have := atomOut_env bi fuel _ hi hHi env
    rw [hh] at this; exact this
  subst he1
  have hrelLo : EnvRel (bind1 σ (.ilit .int lo) .nil).σ e1
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo V) :=
    hrel.mapV (fun v => Var.there v) fun _ _ => rfl
  have hLo : PDen bi tf (bind1 σ (.ilit .int lo) .nil).pre V =
      some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo V) :=
    (PDen_bind1 bi tf σ (.ilit .int lo) .nil V).trans rfl
  obtain ⟨W2, hW2, hrel2, rfl⟩ := atomOut_sound bi fuel _ hi hHi e1 _ hv e1 hrelLo hh tf
  obtain ⟨hInt, htoInt, hloop⟩ := forFoldRev_enc_run bi fuel i lo hi body hh hrun
  have hloW : (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res).lookup W2 = lo :=
    (@NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ tf _ _ _ oHi.pre _ _ _
      hW2).trans rfl
  have hargsT : Expr.lookupArgs (HVector.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res)
      (HVector.cons oHi.res .nil)) W2 =
      HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo
        (HVector.cons (t := oHi.t) (oHi.res.lookup W2) .nil) := by
    show HVector.cons ((oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res).lookup W2)
      (HVector.cons (oHi.res.lookup W2) .nil) = _
    rw [hloW]
    rfl
  have hTrip : PDen bi tf (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).pre W2 =
      some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat) W2) := by
    refine (PDen_bind1 bi tf _ (.trip oHi.t) _ W2).trans ?_
    refine (congrArg (fun a => Option.map _ (nfDenoteOp (tableOf bi) (.trip oHi.t) a))
      hargsT).trans ?_
    show Option.map _ ((NfTy.toInt? oHi.t (oHi.res.lookup W2)).map
      fun hi => BitVec.ofNat 64 (hi - lo).toNat) = _
    rw [htoInt]
    rfl
  have hrelT : EnvRel (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).σ e1
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat) W2) :=
    hrel2.mapV (fun v => Var.there v) fun _ _ => rfl
  have hOne : PDen bi tf (bind1 (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).σ
      (.ilit (.word 64) 1) .nil).pre
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat) W2) =
      some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (BitVec.ofNat 64 1)
        (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
          (BitVec.ofNat 64 (hInt - lo).toNat) W2)) :=
    (PDen_bind1 bi tf _ (.ilit (.word 64) 1) .nil _).trans rfl
  have hSub : PDen bi tf (bind1 (bind1 (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).σ
      (.ilit (.word 64) 1) .nil).σ (.bin .sub 64)
      (.cons (Var.there Var.here) (.cons Var.here .nil))).pre
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (BitVec.ofNat 64 1)
        (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
          (BitVec.ofNat 64 (hInt - lo).toNat) W2)) =
      some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat - 1)
        (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (BitVec.ofNat 64 1)
          (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
            (BitVec.ofNat 64 (hInt - lo).toNat) W2))) :=
    (PDen_bind1 bi tf _ (.bin .sub 64) _ _).trans rfl
  have hrelM := (hrelT.mapV (fun v => Var.there (s := NfTy.word 64) v) fun _ _ => rfl).mapV
    (fun v => Var.there (s := NfTy.word 64) v)
    (W := HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat - 1)
        (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (BitVec.ofNat 64 1)
          (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
            (BitVec.ofNat 64 (hInt - lo).toNat) W2))) fun _ _ => rfl
  have hlitE : ∀ n, hi = .lit (.int n) → enc oHi.t (oHi.res.lookup W2) = .int n :=
    fun n hn => by
      subst hn
      rw [lit_run] at hh
      have h1 := (Prod.mk.inj hh).1
      injection h1 with h2
      exact h2.symm
  have hrange := bound_range hbd htoInt hlitE
  have hM := trip_lt_of_bound hbd htoInt hlitE
  -- the prefix before the loop has no event
  have hq : QuietPre bi C tf (((((bind1 σ (.ilit .int lo) .nil).pre.append oHi.pre).append
      (bind1 oHi.σ (.trip oHi.t)
        (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).pre).append
      (bind1 (bind1 oHi.σ (.trip oHi.t)
        (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).σ
        (.ilit (.word 64) 1) .nil).pre).append
      (bind1 (bind1 (bind1 oHi.σ (.trip oHi.t)
        (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).σ
        (.ilit (.word 64) 1) .nil).σ (.bin .sub 64)
        (.cons (Var.there Var.here) (.cons Var.here .nil))).pre) :=
    QuietPre.append (QuietPre.append (QuietPre.append (QuietPre.append
      (QuietPre.var bi tf none _ (fun _ => rfl) _) (quietPre_atomOut bi tf _ hi hHi))
      (QuietPre.var bi tf none _ (fun _ => rfl) _)) (QuietPre.var bi tf none _ (fun _ => rfl) _))
      (QuietPre.var bi tf none (.bin .sub 64) (fun _ => rfl) _)
  have hpre := hq V
  rw [PDen_append_some bi tf (PDen_append_some bi tf (PDen_append_some bi tf
    (PDen_append_some bi tf hLo hW2) hTrip) hOne) hSub] at hpre
  obtain ⟨W, hW⟩ := loopOut_leak bi fuel body tgt _ _ _ _ _ i _ _ _ _ hL
    (fun σ' _ h' fuel' => HB σ' h' fuel')
    (by rw [List.length_map, entriesVars_length])
    (fun x hx hxi _ hl => frameOk_of_not_carried _ i body hl hxi hx)
    e1 V _ tf [] hpre hrelM
    (CarriedRel.of_entries hrelM _ (carried_lookup _ i body)) lo hInt hloW rfl
    hM hrange.1 (le_of_lt hrange.2) (fun _ hm => by cases hm; rfl) r env' hloop
  refine ⟨W, hW.trans ?_⟩
  -- the source trace
  have hhi : nfTrace (srcLeakCl bi C.cl hi fuel e1) = [] := by
    cases hi with
    | var x => rfl
    | lit l => rfl
    | _ => simp [atomOut] at hHi
  have hlo' : (denote' bi fuel (.lit (.int lo))).run e1 = (.val (.int lo), e1) :=
    lit_run bi fuel _ _
  simp only [srcLeakCl, boundsLeak, hlo', hh]
  rw [boundInt_enc htoInt]
  simp only [boundInt, nfTrace, nfEv, hhi, Nat.mod_eq_of_lt hM, List.nil_append,
    List.append_nil, List.cons_append]

/-! ## The leakage transformer of the front -/

/-- **The front simulates `denote'` with leakage.** Under `TypedCalls bi sigOf` and a call
    leakage `C` that agrees with `bi`, for every expression `e` the front translates from
    `σ`, a run of `denote' bi fuel e` from an environment related to `V` to a value is
    matched, at every target fuel, by the leakage run of the prefix with the events of `C`,
    whose events are the transformed source leakage `nfTrace (srcLeakCl bi C.cl e fuel env)`.
    At `C = CallLeak.nf` the events are those of `nfLeakModel` and the source leakage is
    `srcLeakNF`. -/
theorem impToNF_lsound (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (hC : C.Agrees bi) (e : ImpExpr) :
    ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ},
      impToNF sigOf tgt σ e = some o → ∀ fuel, LSound bi C fuel e σ o := by
  induction e using ImpExpr.ind
  case lit l => intro tgt Γ σ o h fuel; exact lsound_lit bi fuel tgt σ l h
  case var x => intro tgt Γ σ o h fuel; exact lsound_atom bi fuel σ _ h
  case letBind x v b ihv ihb =>
    intro tgt Γ σ o h fuel
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ov, hov, ob, hob, rfl⟩ := h
    exact lsound_letBind bi fuel x (ihv _ σ hov fuel) (ihb _ _ hob fuel)
  case seq a b iha ihb =>
    intro tgt Γ σ o h fuel
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨oa, hoa, ob, hob, rfl⟩ := h
    exact lsound_seq bi fuel (iha _ σ hoa fuel) (ihb _ _ hob fuel)
  case assign x r ih =>
    intro tgt Γ σ o h fuel
    simp only [impToNF, Option.map_eq_some_iff] at h
    obtain ⟨o', ho', rfl⟩ := h
    exact lsound_assign bi fuel x tgt (ih _ σ ho' fuel)
  case app f args iha =>
    intro tgt Γ σ o h fuel
    exact lsound_app bi sigOf hT hC fuel tgt f args σ
      (fun e he _ σ' _ h' => iha e he none σ' h' fuel) h
  case tuple es _ => intro tgt Γ σ o h fuel; exact lsound_tuple bi sigOf fuel tgt es σ h
  case unitVal =>
    intro tgt Γ σ o h fuel
    simp only [impToNF, Option.some.injEq] at h
    subst h
    exact lsound_bind1N bi fuel _ tgt σ _ (fun _ => rfl) _ (fun _ => rfl)
      fun env V v env' _ hr => by
        rw [unitVal_run] at hr
        cases hr
        exact ⟨rfl, (), rfl, rfl⟩
  case typeAscription e s ih =>
    intro tgt Γ σ o h fuel env V v env' hrel hrun tf
    have hr : (denote' bi fuel (.typeAscription e s)).run env = (denote' bi fuel e).run env := by
      simp only [denote']
    have hs : srcLeakCl bi C.cl (.typeAscription e s) fuel env = srcLeakCl bi C.cl e fuel env := by
      simp only [srcLeakCl]
    rw [hr] at hrun
    rw [hs]
    exact ih _ σ h fuel env V v env' hrel hrun tf
  case forFold i lo hi body _ _ ihb =>
    intro tgt Γ σ o h fuel
    cases lo with
    | lit l =>
        cases l with
        | int n =>
            exact lsound_forFold bi sigOf fuel tgt i n hi body σ h
              fun σ' _ h' fuel' => ihb none σ' h' fuel'
        | _ => simp [impToNF] at h
    | _ => simp [impToNF] at h
  case forFoldRev i lo hi body _ _ ihb =>
    intro tgt Γ σ o h fuel
    cases lo with
    | lit l =>
        cases l with
        | int n =>
            exact lsound_forFoldRev bi sigOf fuel tgt i n hi body σ h
              fun σ' _ h' fuel' => ihb none σ' h' fuel'
        | _ => simp [impToNF] at h
    | _ => simp [impToNF] at h
  case ifThenElse c a b ihc iha ihb =>
    intro tgt Γ σ o h fuel
    exact lsound_cond bi sigOf fuel tgt c a b σ h (fun h' => ihc none σ h' fuel)
      (fun σ' _ h' => iha none σ' h' fuel) (fun σ' _ h' => ihb none σ' h' fuel)
  all_goals intro tgt Γ σ o h; simp [impToNF] at h

/-- **The leakage transformer of `impToNF` under a call leakage.** Under
    `TypedCalls bi sigOf` and a call leakage `C` that agrees with `bi`, a run of
    `denote' bi fuel e` from an environment related to `V` by `σ` to a value is matched, at
    every target fuel, by the leakage run `nfLeakRunE bi C` of the program `impToNF` emits,
    which returns the encoding of the value and the events
    `nfTrace (srcLeakCl bi C.cl e fuel env)`. -/
theorem impToNF_leakE (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (hC : C.Agrees bi) {e : ImpExpr} {tgt : Option String}
    {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {o : Out Γ} (h : impToNF sigOf tgt σ e = some o)
    {fuel : Nat} {env : Env} {V : Valuation Γ} {v : Value} {env' : Env}
    (hrel : EnvRel σ env V) (hrun : (denote' bi fuel e).run env = (.val v, env')) (tf : Nat) :
    ∃ x : o.t.denote, nfLeakRunE bi C tf o.prog V =
        some (HVector.cons (f := fun t => ⟦t⟧) x .nil, nfTrace (srcLeakCl bi C.cl e fuel env)) ∧
      v = enc o.t x := by
  obtain ⟨W, hW, -, rfl⟩ :=
    impToNF_lsound bi sigOf hT hC e tgt σ h fuel env V v env' hrel hrun tf
  refine ⟨o.res.lookup W, ?_, rfl⟩
  rw [Out.prog, nfLeakRunE_plug, hW, Option.bind_some]
  show Option.map _ (some (Expr.lookupArgs (HVector.cons o.res .nil) W, ([] : List CTLeak))) = _
  simp only [Option.map_some, List.append_nil]
  rfl

/-- **The leakage transformer of `impToNF`.** Under `TypedCalls bi sigOf`, a run of
    `denote' bi fuel e` from an environment related to `V` by `σ` to a value is matched, at
    every target fuel, by the leakage run `nfLeakRun` of the program `impToNF` emits, which
    returns the encoding of the value and the events `nfTrace (srcLeakNF bi e fuel env)`, a
    function of the source leakage alone: `impToNF_leakE` at the call leakage `CallLeak.nf`
    of the front. -/
theorem impToNF_leak (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) {e : ImpExpr} {tgt : Option String} {Γ : Ctxt nfDialect}
    {σ : NfEnv Γ} {o : Out Γ} (h : impToNF sigOf tgt σ e = some o) {fuel : Nat} {env : Env}
    {V : Valuation Γ} {v : Value} {env' : Env} (hrel : EnvRel σ env V)
    (hrun : (denote' bi fuel e).run env = (.val v, env')) (tf : Nat) :
    ∃ x : o.t.denote, nfLeakRun bi tf o.prog V =
        some (HVector.cons (f := fun t => ⟦t⟧) x .nil, nfTrace (srcLeakNF bi e fuel env)) ∧
      v = enc o.t x := by
  rw [← nfLeakRunE_nf]
  exact impToNF_leakE bi sigOf hT (CallLeak.nf_agrees bi) h hrel hrun tf

/-! ## The leakage model with quiet field calls -/

/-- **The leakage model of `nfDialect` with quiet field calls**: the class `nfKind` of an
    operation, except that a call of a tagged field head (`Hax.FieldTag.fieldTag?`) is
    quiet. -/
def nfLeakModelQ : LeakModel nfDialect where
  kind op := match nfKind op with
    | .vtCall f => if (_root_.Hax.FieldTag.fieldTag? f).isSome then .quiet else .vtCall f
    | k => k
  valNat := nfValNat

/-- The events of an operation under `nfLeakModelQ` are its events under `nfLeakModel`
    without the leaf calls of tagged field heads. -/
theorem opLeak_nfLeakModelQ (op : NfOp)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := nfDialect) op)) :
    ComLevelCheck.opLeak nfLeakModelQ op vals =
      stripField (ComLevelCheck.opLeak nfLeakModel op vals) := by
  have hv : ∀ {tys : List NfTy} (xs : HVector (fun t => ⟦t⟧) tys),
      valsNat nfLeakModelQ xs = valsNat nfLeakModel xs := by
    intro tys xs
    induction xs with
    | nil => rfl
    | cons x xs ih => exact congrArg (List.cons _) ih
  unfold ComLevelCheck.opLeak
  rw [hv]
  simp only [nfLeakModelQ, nfLeakModel]
  cases nfKind op with
  | vtCall f =>
      cases h : (_root_.Hax.FieldTag.fieldTag? f).isSome <;>
        simp [stripField, isFieldEvent, h]
  | _ => simp [stripField, isFieldEvent]

/-- The leakage run of a program of `nfDialect` over the leaf table of the builtin table `bi`
    in the leakage model `nfLeakModelQ`. -/
abbrev nfLeakRunQ (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    Option (Valuation (d := nfDialect) ts × List CTLeak) :=
  @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModelQ fuel _ _ p V

/-- **The run with quiet field calls is the stripped run**: the leakage run of a program in
    `nfLeakModelQ` is its run in `nfLeakModel` with the leaf calls of tagged field heads
    removed from the events (`stripField`). -/
theorem nfLeakRunQ_eq (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    nfLeakRunQ bi fuel p V = (nfLeakRun bi fuel p V).map fun r => (r.1, stripField r.2) :=
  @NFProg.leakRunM_filter nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModel nfLeakModelQ
    (fun e => !isFieldEvent e) (fun _ => rfl) (fun _ => rfl) opLeak_nfLeakModelQ fuel _ _ p V

/-! ## Constant time through the front -/

/-- **Source constant time for `srcLeakNF`, modulo the field calls,** of `e` for the split
    `lt`: two runs at the same fuel from environments agreeing on the public variables, both
    ending in a value, have equal events `nfTrace` of their leakage once the leaf calls of
    tagged field heads are removed (`stripField`). A tagged field call is compiled to a
    fiat-template body whose constant time is a property of that body
    (`FieldLevel.fieldBody_nfCTRel`); its arguments are the only events removed. -/
def SourceCTNF (bi : Builtins) (lt : LevelTable) (e : ImpExpr) : Prop :=
  ∀ (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (v₁ v₂ : Value),
    PubEqEnv lt env₁ env₂ →
    (denote' bi fuel e).run env₁ = (.val v₁, env₁') →
    (denote' bi fuel e).run env₂ = (.val v₂, env₂') →
    stripField (nfTrace (srcLeakNF bi e fuel env₁)) =
      stripField (nfTrace (srcLeakNF bi e fuel env₂))

/-- **Two runs through the front.** Under `TypedCalls bi sigOf` and source constant time
    modulo the field calls, the leakage runs of the program `impToNF` emits from two
    valuations related by `σ` to environments agreeing on the public variables, from which the
    source runs to values, emit equal events once the leaf calls of tagged field heads are
    removed. -/
theorem impToNF_ct_runs (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) {lt : LevelTable} {e : ImpExpr} (hct : SourceCTNF bi lt e)
    {tgt : Option String} {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {o : Out Γ}
    (h : impToNF sigOf tgt σ e = some o) {fuel : Nat} {env₁ env₂ env₁' env₂' : Env}
    {V₁ V₂ : Valuation Γ} {v₁ v₂ : Value} (hr₁ : EnvRel σ env₁ V₁) (hr₂ : EnvRel σ env₂ V₂)
    (hpub : PubEqEnv lt env₁ env₂)
    (hrun₁ : (denote' bi fuel e).run env₁ = (.val v₁, env₁'))
    (hrun₂ : (denote' bi fuel e).run env₂ = (.val v₂, env₂')) (tf : Nat)
    {q₁ q₂ : Valuation (d := nfDialect) [o.t] × List CTLeak}
    (hq₁ : nfLeakRunQ bi tf o.prog V₁ = some q₁) (hq₂ : nfLeakRunQ bi tf o.prog V₂ = some q₂) :
    q₁.2 = q₂.2 := by
  obtain ⟨_, h₁, -⟩ := impToNF_leak bi sigOf hT h hr₁ hrun₁ tf
  obtain ⟨_, h₂, -⟩ := impToNF_leak bi sigOf hT h hr₂ hrun₂ tf
  rw [nfLeakRunQ_eq, h₁, Option.map_some, Option.some.injEq] at hq₁
  rw [nfLeakRunQ_eq, h₂, Option.map_some, Option.some.injEq] at hq₂
  rw [← hq₁, ← hq₂]
  exact hct fuel env₁ env₂ env₁' env₂' v₁ v₂ hpub hrun₁ hrun₂

/-- The labels of the parameters `ps` read from the level table `lt`. -/
def entryLabels (lt : LevelTable) : (ps : List (String × NfTy)) →
    Labels (d := nfDialect) (entryCtx ps)
  | [] => .nil
  | (x, _) :: ps => .cons (lt x) (entryLabels lt ps)

/-- The source environment of a valuation of the parameters `ps`: each name bound to the
    encoding of the value of its first occurrence, every other name unbound. -/
def entryEnvOf : (ps : List (String × NfTy)) → Valuation (entryCtx ps) → Env
  | [], _ => fun _ => none
  | (x, t) :: ps, .cons y V => (entryEnvOf ps V).extend x (enc t y)

/-- The environment of names of the parameters is related to the source environment of a
    valuation. -/
theorem entryEnvOf_rel : ∀ (ps : List (String × NfTy)) (V : Valuation (entryCtx ps)),
    EnvRel (entryEnv ps) (entryEnvOf ps V) V
  | [], .nil => by
      intro x t v hx
      simp [entryEnv, NfEnv.lookup] at hx
  | (x, t) :: ps, .cons y V => by
      intro x' t' v hx'
      change NfEnv.lookup ((x, ⟨t, Var.here⟩) ::
        NfEnv.mapV (fun v => Var.there v) (entryEnv ps)) x' = _ at hx'
      rw [NfEnv.lookup_cons] at hx'
      split at hx'
      · rename_i hxx
        subst hxx
        cases hx'
        exact Env.extend_same _ _ _
      · rename_i hxx
        have := EnvRel.mapV (entryEnvOf_rel ps V) (fun v => Var.there v) (W := .cons y V)
          (fun _ _ => rfl) x' t' v hx'
        change ((entryEnvOf ps V).extend x (enc t y)) x' = _
        rw [Env.extend_other _ _ _ _ (Ne.symm (by simpa using hxx))]
        exact this

/-- Valuations agreeing on the positions `entryLabels lt ps` marks public have source
    environments agreeing on the variables `lt` marks public. -/
theorem pubEqEnv_entryEnvOf (lt : LevelTable) : ∀ (ps : List (String × NfTy))
    (V₁ V₂ : Valuation (entryCtx ps)), PubEqV (entryLabels lt ps) V₁ V₂ →
    PubEqEnv lt (entryEnvOf ps V₁) (entryEnvOf ps V₂)
  | [], .nil, .nil, _ => fun _ _ => rfl
  | (x, t) :: ps, .cons y₁ V₁, .cons y₂ V₂, h => by
      intro z hz
      change ((entryEnvOf ps V₁).extend x (enc t y₁)) z =
        ((entryEnvOf ps V₂).extend x (enc t y₂)) z
      by_cases hxz : x = z
      · subst hxz
        rw [Env.extend_same, Env.extend_same]
        have := h t (Var.here) hz
        exact congrArg (fun w => some (enc t w)) this
      · rw [Env.extend_other _ _ _ _ (Ne.symm hxz), Env.extend_other _ _ _ _ (Ne.symm hxz)]
        exact pubEqEnv_entryEnvOf lt ps V₁ V₂
          (fun t' v hv => h t' (Var.there v) hv) z hz

/-- **Constant time through the front.** Under `TypedCalls bi sigOf`, let `e` be constant
    time at the source modulo the field calls for the level table `lt` (`SourceCTNF`), and
    let the source run of `e` at the fuel `fuel` end in a value from the source environment of
    every valuation of the parameters `ps`. Then the program `impToNF` emits from the
    parameters is constant time in the leakage model `nfLeakModelQ` with quiet field calls,
    relative to the runs that succeed, for the labels `entryLabels lt ps` of the parameters,
    at every target fuel. -/
theorem impToNF_nfCTRel (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (lt : LevelTable) (ps : List (String × NfTy)) {e : ImpExpr}
    (hct : SourceCTNF bi lt e) {tgt : Option String} {o : Out (entryCtx ps)}
    (h : impToNF sigOf tgt (entryEnv ps) e = some o) (fuel : Nat)
    (hterm : ∀ V : Valuation (entryCtx ps), ∃ v env',
      (denote' bi fuel e).run (entryEnvOf ps V) = (.val v, env')) (tf : Nat) :
    @NFCTRel nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModelQ _ _
      (entryLabels lt ps) tf o.prog := by
  intro V₁ V₂ q₁ q₂ hpub hq₁ hq₂
  obtain ⟨v₁, env₁', hrun₁⟩ := hterm V₁
  obtain ⟨v₂, env₂', hrun₂⟩ := hterm V₂
  exact impToNF_ct_runs bi sigOf hT hct h (entryEnvOf_rel ps V₁) (entryEnvOf_rel ps V₂)
    (pubEqEnv_entryEnvOf lt ps V₁ V₂ hpub) hrun₁ hrun₂ tf hq₁ hq₂

/-! ## The labels of a secrecy record -/

open _root_.Hax (FnSecrecy BindingSecrecy)
open CatCrypt.Crypto.SecureCompilation.CT (levelsOf levelsOf_eq_public_iff secretSlots
  bindingSlots)

/-- The level of a parameter named `x` in the secrecy record `s`: public when the record lists
    it as public, secret otherwise (the level of the parameter labels `nfLabels` of the direct
    front). -/
def paramLevelOf (s : FnSecrecy) (x : String) : SecretLevel :=
  if s.params.lookup x = some .pub then .Public else .Secret

/-- A listed parameter that `levelsOf s` marks public is listed as public. -/
theorem paramLevelOf_of_levelsOf {s : FnSecrecy} {x : String}
    (hx : ∃ b, (x, b) ∈ s.params) (h : levelsOf s x = .Public) :
    paramLevelOf s x = .Public := by
  rw [levelsOf_eq_public_iff] at h
  have key : ∀ (l : List (String × BindingSecrecy)) (b : BindingSecrecy), (x, b) ∈ l →
      ∃ b', l.lookup x = some b' ∧ (x, b') ∈ l := by
    intro l b hb
    induction l with
    | nil => cases hb
    | cons p ps ih =>
        obtain ⟨y, c⟩ := p
        by_cases hxy : x = y
        · subst hxy
          exact ⟨c, by simp [List.lookup], List.mem_cons_self⟩
        · rcases List.mem_cons.mp hb with hb | hb
          · cases hb; exact absurd rfl hxy
          · obtain ⟨b', h1, h2⟩ := ih hb
            refine ⟨b', ?_, List.mem_cons_of_mem _ h2⟩
            have : (x == y) = false := by simpa using hxy
            simp [List.lookup, this, h1]
  obtain ⟨b, hl, hm⟩ := key s.params hx.choose hx.choose_spec
  unfold paramLevelOf
  rw [hl]
  cases b with
  | pub => rfl
  | secret =>
      exact absurd (List.mem_flatMap.mpr ⟨(x, .secret), hm, by simp [bindingSlots]⟩) h
  | fields fs =>
      exact absurd (List.mem_flatMap.mpr ⟨(x, .fields fs), hm, by simp [bindingSlots]⟩) h

/-- **The label correspondence.** When every parameter of `ps` is listed in the secrecy
    record `s`, valuations agreeing on the positions the parameter levels `paramLevelOf s`
    mark public agree on the positions `entryLabels (levelsOf s) ps` marks public. -/
theorem pubEqV_entryLabels_levelsOf (s : FnSecrecy) :
    ∀ (ps : List (String × NfTy)), (∀ p ∈ ps, ∃ b, (p.1, b) ∈ s.params) →
    ∀ (V₁ V₂ : Valuation (entryCtx ps)), PubEqV (entryLabels (paramLevelOf s) ps) V₁ V₂ →
      PubEqV (entryLabels (levelsOf s) ps) V₁ V₂
  | [], _, _, _, _ => fun _ v => nomatch v
  | (x, t) :: ps, hps, .cons y₁ V₁, .cons y₂ V₂, h => by
      intro t' v hv
      cases v with
      | here =>
          exact h _ .here (paramLevelOf_of_levelsOf (hps (x, t) List.mem_cons_self) hv)
      | there v =>
          exact pubEqV_entryLabels_levelsOf s ps
            (fun p hp => hps p (List.mem_cons_of_mem _ hp)) V₁ V₂
            (fun t'' w hw => h t'' (.there w) hw) t' v hv

/-- **Constant time through the front, for the parameter labels of a secrecy record.**
    `impToNF_nfCTRel` at the level table `levelsOf s`, stated for the labels `paramLevelOf s`
    of the parameters, each of which `s` lists. -/
theorem impToNF_nfCTRel_params (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (s : FnSecrecy) (ps : List (String × NfTy))
    (hps : ∀ p ∈ ps, ∃ b, (p.1, b) ∈ s.params) {e : ImpExpr}
    (hct : SourceCTNF bi (levelsOf s) e) {tgt : Option String} {o : Out (entryCtx ps)}
    (h : impToNF sigOf tgt (entryEnv ps) e = some o) (fuel : Nat)
    (hterm : ∀ V : Valuation (entryCtx ps), ∃ v env',
      (denote' bi fuel e).run (entryEnvOf ps V) = (.val v, env')) (tf : Nat) :
    @NFCTRel nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModelQ _ _
      (entryLabels (paramLevelOf s) ps) tf o.prog := by
  intro V₁ V₂ q₁ q₂ hpub hq₁ hq₂
  exact impToNF_nfCTRel bi sigOf hT (levelsOf s) ps hct h fuel hterm tf V₁ V₂ q₁ q₂
    (pubEqV_entryLabels_levelsOf s ps hps V₁ V₂ hpub) hq₁ hq₂

end CatCrypt.Crypto.Hax.ImpToNF
