/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF

/-!
# The front `impToNF` at the level of call trees: the conditional and the `while` loop

The relation `RelT` of `NFCallTreeImpToNF` for a conditional `ifThenElse` and for a loop
`whileFold` on a flag. An arm of a conditional is related to the arm of the region
`NFPre.ifThenElse` closed by the return of its value and of the carried names (`ArmRel`); the
trips of the `while` loop at the source fuel `n` are related to the exit-flag iteration at
every count `m ≥ n`, each target body at the target fuel `tf ≥ m` (`whileTrips_relT`).

## Main definitions

* `ArmRel`: the leaf relation of an arm of a conditional.
* `whileBodyK`: the continuation of a trip of `denoteWhileT` after the body.

## Main results

* `condArm_relT`, `cond_relT`: the arms of a conditional and the conditional.
* `whileTrips_relT`, `whileFold_relT`: the trips of a `while` loop and the loop.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF

open _root_.Hax (ImpExpr ImpLit Value Env Outcome)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (LeafCall leafSig linkReader
  opTree)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm (LeafP)
open _root_.Hax.InlineLocalClosures (frameOk)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc bind_ret)
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## The arms of a conditional -/

section Cond

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- The leaves of a tree satisfy a family of properties when they satisfy each. -/
theorem leafP_all {E : EventSig} {R ι : Type} {P : ι → R → Prop} (t : CallTree E R)
    (h : ∀ i, LeafP (P i) t) : LeafP (fun r => ∀ i, P i r) t := by
  induction t with
  | ret r => exact .ret fun i => by cases h i with | ret hi => exact hi
  | vis e c ih => exact .vis fun a => ih a fun i => by cases h i with | vis hi => exact hi a

/-- A relation of trees carries a property of the leaves of the source tree. -/
theorem ruttS_srcLeaf {E₁ E₂ : EventSig} {g₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {R₁ R₂ : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {P : R₁ → Prop}
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttS g₁ RE RA RR Fail t₁ t₂)
    (hP : LeafP P t₁) : RuttS g₁ RE RA (fun a b => RR a b ∧ P a) Fail t₁ t₂ := by
  induction h with
  | ret h => cases hP with | ret hp => exact .ret ⟨h, hp⟩
  | fail h => exact .fail h
  | vis he _ ih => cases hP with | vis hP => exact .vis he fun a₁ a₂ ha => ih a₁ a₂ ha (hP a₁)
  | skip _ ih => cases hP with | vis hP => exact .skip (ih (hP _))

/-- The leaves of the reading of an expression that binds no name of `σc` outside `xs`, whose
    outcome is not an error, keep those names. -/
theorem keeps_leafP (e : ImpExpr) {Γc : Ctxt nfDialect} (σc : NfEnv Γc) (xs : List String)
    (hfr : ∀ x, x ∉ xs → ∀ q, σc.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) e = true)
    (fuel : Nat) (env : Env) :
    LeafP (fun r : Outcome × Env => ∀ y, _root_.Hax.InlineLocalClosures.IsErr r.1 ∨ y ∈ xs ∨
      σc.lookup y = none ∨ r.2 y = env y) (denoteT evTable fuel e env) := by
  refine leafP_all _ fun y => ?_
  by_cases hy : y ∉ xs ∧ ∃ q, σc.lookup y = some q
  · obtain ⟨hx, q, hq⟩ := hy
    exact (NFCallTreeANorm.denoteT_keeps evTable e (hfr y hx q hq) fuel env).mono
      fun r hr => by
        by_cases he : _root_.Hax.InlineLocalClosures.IsErr r.1
        · exact .inl he
        · exact .inr (.inr (.inr (hr he)))
  · refine NFCallTreeANorm.leafP_of_forall (fun r => ?_) _
    by_cases hx : y ∈ xs
    · exact .inr (.inl hx)
    · refine .inr (.inr (.inl ?_))
      cases hq : σc.lookup y with
      | none => rfl
      | some q => exact absurd ⟨hx, q, hq⟩ hy

/-- The leaf relation of an arm of a conditional closed by the return of the variables `X`:
    a source value encoding the value of the arm, the returned values at the hole, the carried
    names reading the values of `rets` there, and the other names of `σc` unchanged. -/
def ArmRel {Γc : Ctxt nfDialect} (σc : NfEnv Γc) (Vc : Valuation Γc) (xs : List String)
    (cs : List NfTy) (o : Out Γc) (rets : HVector (fun t => Var o.Δ t) cs) {rs : List NfTy}
    (X : HVector (fun t => Var o.Δ t) rs) (r : Outcome × Env)
    (w : Option (Valuation (d := nfDialect) rs)) : Prop :=
  ∃ v W, r.1 = .val v ∧ w = some (Expr.lookupArgs X W) ∧ v = enc o.t (o.res.lookup W) ∧
    CarriedRel r.2 xs cs (Expr.lookupArgs rets W) ∧
    ∀ y, y ∉ xs → ∀ t (u : Var Γc t), σc.lookup y = some ⟨t, u⟩ →
      r.2 y = some (enc t (u.lookup Vc))

/-- **One arm of a conditional.** An output related to the arm `e` from `σc`, closed by the
    return of the variables `X`, relates the trees at `ArmRel`, when `e` binds no name of `σc`
    outside `xs`. -/
theorem condArm_relT (fuel tf : Nat) (e : ImpExpr) {Γc : Ctxt nfDialect} (σc : NfEnv Γc)
    (xs : List String) (cs : List NfTy) {o : Out Γc} (rets : HVector (fun t => Var o.Δ t) cs)
    (hrets : varsAt o.σ xs cs = some rets) (hS : RelT h₁ tE fuel tf e σc o)
    (hfr : ∀ x, x ∉ xs → ∀ q, σc.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) e = true)
    (env : Env) (Vc : Valuation Γc) (hrel : EnvRel σc env Vc) {rs : List NfTy}
    (X : HVector (fun t => Var o.Δ t) rs) :
    RuttS h₁ ImpRE ImpRA (ArmRel σc Vc xs cs o rets X) SrcFail (denoteT evTable fuel e env)
      (treeAt linkReader tE tf (o.pre.plug (.ret X)) Vc) := by
  rw [treeAt_plug, ← bind_ret (denoteT evTable fuel e env)]
  unfold obind
  refine RuttS.bind (ruttS_srcLeaf (hS env Vc hrel) (keeps_leafP e σc xs hfr fuel env)) ?_ ?_
  · rintro ⟨o1, e1⟩ s₂ ⟨⟨v, W, h1, rfl, hrelW, hv⟩, hkeep⟩
    dsimp only at h1 hrelW hkeep ⊢
    refine .ret ⟨v, W, h1, rfl, hv, CarriedRel.of_varsAt hrelW xs cs hrets, fun y hy t u hl => ?_⟩
    rcases hkeep y with he | hm | hn | hk
    · rw [h1] at he
      obtain ⟨_, he⟩ := he
      cases he
    · exact absurd hm hy
    · rw [hl] at hn
      cases hn
    · change e1 y = _
      rw [hk, hrel y t u hl]
  · intro s₁ hf t
    exact .fail hf

/-- The environment of names after a conditional is related to the final environment of an
    arm whose carried names read `acc` and whose other names are unchanged. -/
theorem condEnv_rel {Γc : Ctxt nfDialect} (σc : NfEnv Γc) (Vc : Valuation Γc)
    (xs : List String) (cs : List NfTy) (hlen : xs.length = cs.length) (t : NfTy) (x : t.denote)
    (acc : Valuation (d := nfDialect) cs) (env' : Env) (hcar : CarriedRel env' xs cs acc)
    (hkeep : ∀ y, y ∉ xs → ∀ t (u : Var Γc t), σc.lookup y = some ⟨t, u⟩ →
      env' y = some (enc t (u.lookup Vc))) :
    EnvRel (condEnv σc xs t cs) env' (HVector.cons (f := fun t => ⟦t⟧) x (hvAppend acc Vc)) := by
  intro y t' v hl
  refine EnvRel.bindAll xs cs _ _ hlen ?_ y ?_ t' v hl
  · show CarriedRel env' xs cs (Expr.lookupArgs (HVector.renameVars (fun v => Var.there v)
      (headVars cs)) (HVector.cons (f := fun t => ⟦t⟧) x (hvAppend acc Vc)))
    rw [lookupArgs_headVars_there]
    exact hcar
  · intro hy t'' v' hl'
    rw [NfEnv.lookup_mapV, Option.map_eq_some_iff] at hl'
    obtain ⟨⟨t0, v0⟩, h0, heq⟩ := hl'
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨rfl, hv'⟩ := heq
    rw [hkeep y hy t0 v0 h0, ← eq_of_heq hv']
    exact congrArg (fun z => some (enc t0 z))
      (Var.lookup_shiftApp (t :: cs) (HVector.cons (f := fun t => ⟦t⟧) x acc) v0 Vc).symm

/-- The environment of names after a conditional of the unit type is related to the final
    environment of an arm whose carried names read `acc` and whose other names are
    unchanged. -/
theorem condEnvU_rel {Γc : Ctxt nfDialect} (σc : NfEnv Γc) (Vc : Valuation Γc)
    (xs : List String) (cs : List NfTy) (hlen : xs.length = cs.length)
    (acc : Valuation (d := nfDialect) cs) (env' : Env) (hcar : CarriedRel env' xs cs acc)
    (hkeep : ∀ y, y ∉ xs → ∀ t (u : Var Γc t), σc.lookup y = some ⟨t, u⟩ →
      env' y = some (enc t (u.lookup Vc))) :
    EnvRel (NfEnv.bindAll xs cs (headVars cs)
      (NfEnv.mapV (fun v => Var.shiftApp (d := nfDialect) cs v) σc)) env' (hvAppend acc Vc) := by
  intro y t v hl
  refine EnvRel.bindAll xs cs _ _ hlen ?_ y ?_ t v hl
  · rw [lookupArgs_headVars]
    exact hcar
  · intro hy t' v' hl'
    rw [NfEnv.lookup_mapV, Option.map_eq_some_iff] at hl'
    obtain ⟨⟨t0, v0⟩, h0, heq⟩ := hl'
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨rfl, hv'⟩ := heq
    rw [hkeep y hy t0 v0 h0, ← eq_of_heq hv']
    exact congrArg (fun z => some (enc t0 z)) (Var.lookup_shiftApp cs acc v0 Vc).symm

/-- `obind` at a leaf with a value is the continuation at the value. -/
theorem obind_ret_some {E : EventSig} {α β : Type} (a : α) (k : α → CallTree E (Option β)) :
    obind (.ret (some a)) k = k a := rfl

/-- A source tree related to a target tree whose related leaves are values, followed by
    continuations related at those values, and whose failed leaves continue to failed trees. -/
theorem ruttS_obindK {S α R₁ β : Type} {RR' : S → Option α → Prop} {Fail' : S → Prop}
    {RR : R₁ → Option β → Prop} {Fail : R₁ → Prop}
    {t₁ : CallTree linkSig S} {t₂ : CallTree leafSig (Option α)}
    {K₁ : S → CallTree linkSig R₁} {K₂ : α → CallTree leafSig (Option β)}
    (h : RuttS h₁ ImpRE ImpRA RR' Fail' t₁ t₂)
    (hk : ∀ r x, RR' r (some x) → RuttS h₁ ImpRE ImpRA RR Fail (K₁ r) (K₂ x))
    (hR : ∀ r w, RR' r w → ∃ x, w = some x)
    (hf : ∀ r, Fail' r → ∀ t, RuttS h₁ ImpRE ImpRA RR Fail (K₁ r) t) :
    RuttS h₁ ImpRE ImpRA RR Fail (t₁.bind K₁) (obind t₂ K₂) := by
  unfold obind
  refine RuttS.bind h (fun r w hr => ?_) hf
  obtain ⟨x, rfl⟩ := hR r w hr
  exact hk r x hr

/-- The tree of a branch region followed by the empty prefix. -/
theorem preTreeAt_ifThenElse_nil {Γ : Ctxt nfDialect} {rs : List NfTy}
    (tf : Nat) (cond : Var Γ NfTy.bit) (thn els : NFProg nfDialect Γ rs) (V : Valuation Γ) :
    preTreeAt linkReader tE tf (.ifThenElse cond thn els .nil) V =
      obind (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) then
          treeAt linkReader tE tf thn V else treeAt linkReader tE tf els V)
        fun r => .ret (some (hvAppend r V)) := rfl

end Cond


/-! ## The conditional -/

section CondRelT

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- **A conditional relates the trees**, when the front relates the trees of its condition and
    of its arms. -/
theorem cond_relT (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat)
    (tgt : Option String) (c a b : ImpExpr) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.ifThenElse c a b) = some o)
    (hc : ∀ {oc : Out Γ}, impToNF sigOf none σ c = some oc → RelT h₁ tE fuel tf c σ oc)
    (ha : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) {o' : Out Δ},
      impToNF sigOf none σ' a = some o' → RelT h₁ tE fuel tf a σ' o')
    (hb : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) {o' : Out Δ},
      impToNF sigOf none σ' b = some o' → RelT h₁ tE fuel tf b σ' o') :
    RelT h₁ tE fuel tf (.ifThenElse c a b) σ o := by
  simp only [impToNF, Option.bind_eq_some_iff] at h
  obtain ⟨oc, hoc, h⟩ := h
  have hC := hc hoc
  obtain ⟨Δc, tc, prec, σc, resc⟩ := oc
  by_cases htc : tc = NfTy.bit
  swap
  · rw [dite_eq_right htc] at h
    cases h
  subst htc
  rw [dite_eq_left rfl] at h
  have hlen : ((condCarried σc a b).map (·.1)).length =
      (entriesVars (condCarried σc a b)).1.length := by
    rw [List.length_map, entriesVars_length]
  have hfr : ∀ x, x ∉ (condCarried σc a b).map (·.1) → ∀ q, σc.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) a = true ∧
        frameOk (fun _ => true) (fun n => n != x) (fun _ => true) b = true :=
    fun x hx _ hq => frameOk_of_not_condCarried σc a b hq hx
  generalize (condCarried σc a b).map (·.1) = xs at h hlen hfr
  generalize (entriesVars (condCarried σc a b)).1 = cs at h hlen
  unfold condOut at h
  obtain ⟨oa, hoa, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ob, hob, h⟩ := Option.bind_eq_some_iff.mp h
  have hA := ha σc hoa
  have hB := hb σc hob
  obtain ⟨Δb, tb, preb, σb, resb⟩ := ob
  by_cases ht : tb = oa.t
  swap
  · rw [dite_eq_right ht] at h
    cases h
  subst ht
  rw [dite_eq_left rfl] at h
  obtain ⟨ra, hra, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rb, hrb, h⟩ := Option.map_eq_some_iff.mp h
  have hlen' : (xs ++ (condFresh σc oa.σ σb).map (·.1)).length =
      (cs ++ (condFresh σc oa.σ σb).map (·.2)).length := by
    simp only [List.length_append, List.length_map, hlen]
  have hfr' : ∀ x, x ∉ xs ++ (condFresh σc oa.σ σb).map (·.1) → ∀ q, σc.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) a = true ∧
        frameOk (fun _ => true) (fun n => n != x) (fun _ => true) b = true :=
    fun x hx q hq => hfr x (fun h => hx (List.mem_append_left _ h)) q hq
  intro env V hrel
  rw [NFCallTreeAnfPick.denoteT_ifThenElse_run]
  by_cases hu : oa.t = NfTy.unit
  · rw [ite_eq_left hu] at h
    subst h
    dsimp only
    rw [preTreeAt_append, preTreeAt_append, obind_assoc]
    refine ruttS_valK (o := ⟨Δc, .bit, prec, σc, resc⟩) (hC env V hrel) (fun e1 W1 hrel1 => ?_)
      (ruttS_keep _ ?_)
    · rw [preTreeAt_ifThenElse_nil, obind_assoc]
      simp only [obind_ret_some]
      have hbit : enc NfTy.bit (resc.lookup W1) =
          .bool (HasBoolBit.toBool (d := nfDialect) (resc.lookup W1)) := rfl
      rw [hbit]
      cases hcb : HasBoolBit.toBool (d := nfDialect) (resc.lookup W1) with
      | true =>
        simp only [ite_true]
        rw [← bind_ret (denoteT evTable fuel a e1)]
        refine ruttS_obindK (condArm_relT fuel tf a σc _ _ ra hra hA
          (fun x hx q hq => (hfr' x hx q hq).1) e1 W1 hrel1 ra) (fun r x hx => ?_)
          (fun r w ⟨_, _, _, hw, _⟩ => ⟨_, hw⟩) (fun r hf t => .fail hf)
        obtain ⟨v, W2, h1, hx, hv, hcar, hkeep⟩ := hx
        cases hx
        rw [preTreeAt_bind1N tE tf none _ .constUnit .nil _ fun _ => rfl]
        exact .ret ⟨v, _, h1, rfl, (condEnvU_rel σc W1 _ _ hlen' _ r.2 hcar hkeep).mapV
          (fun v => Var.there v) fun _ _ => rfl, hv.trans (enc_unit_eq hu _)⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [← bind_ret (denoteT evTable fuel b e1)]
        refine ruttS_obindK (condArm_relT fuel tf b σc _ _ rb hrb hB
          (fun x hx q hq => (hfr' x hx q hq).2) e1 W1 hrel1 rb) (fun r x hx => ?_)
          (fun r w ⟨_, _, _, hw, _⟩ => ⟨_, hw⟩) (fun r hf t => .fail hf)
        obtain ⟨v, W2, h1, hx, hv, hcar, hkeep⟩ := hx
        cases hx
        rw [preTreeAt_bind1N tE tf none _ .constUnit .nil _ fun _ => rfl]
        exact .ret ⟨v, _, h1, rfl, (condEnvU_rel σc W1 _ _ hlen' _ r.2 hcar hkeep).mapV
          (fun v => Var.there v) fun _ _ => rfl, hv.trans (enc_unit_eq hu _)⟩
    · intro o e1 ho
      cases o with
      | val v => exact absurd rfl (ho v)
      | _ => rfl
  · rw [ite_eq_right hu] at h
    subst h
    dsimp only
    rw [preTreeAt_append]
    refine ruttS_valK (o := ⟨Δc, .bit, prec, σc, resc⟩) (hC env V hrel) (fun e1 W1 hrel1 => ?_)
      (ruttS_keep _ ?_)
    · rw [preTreeAt_ifThenElse_nil]
      dsimp only
      have hbit : enc NfTy.bit (resc.lookup W1) =
          .bool (HasBoolBit.toBool (d := nfDialect) (resc.lookup W1)) := rfl
      rw [hbit]
      cases hcb : HasBoolBit.toBool (d := nfDialect) (resc.lookup W1) with
      | true =>
        simp only [ite_true]
        rw [← bind_ret (denoteT evTable fuel a e1)]
        refine ruttS_obindK (condArm_relT fuel tf a σc _ _ ra hra hA
          (fun x hx q hq => (hfr' x hx q hq).1) e1 W1 hrel1 (.cons oa.res ra)) (fun r x hx => ?_)
          (fun r w ⟨_, _, _, hw, _⟩ => ⟨_, hw⟩) (fun r hf t => .fail hf)
        obtain ⟨v, W2, h1, hx, hv, hcar, hkeep⟩ := hx
        cases hx
        exact .ret ⟨v, _, h1, rfl,
          condEnv_rel σc W1 _ _ hlen' oa.t (oa.res.lookup W2) _ r.2 hcar hkeep, hv⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [← bind_ret (denoteT evTable fuel b e1)]
        refine ruttS_obindK (condArm_relT fuel tf b σc _ _ rb hrb hB
          (fun x hx q hq => (hfr' x hx q hq).2) e1 W1 hrel1 (.cons resb rb)) (fun r x hx => ?_)
          (fun r w ⟨_, _, _, hw, _⟩ => ⟨_, hw⟩) (fun r hf t => .fail hf)
        obtain ⟨v, W2, h1, hx, hv, hcar, hkeep⟩ := hx
        cases hx
        exact .ret ⟨v, _, h1, rfl,
          condEnv_rel σc W1 _ _ hlen' oa.t (resb.lookup W2) _ r.2 hcar hkeep, hv⟩
    · intro o e1 ho
      cases o with
      | val v => exact absurd rfl (ho v)
      | _ => rfl



end CondRelT

/-! ## The `while` loop -/

section While

variable {E : EventSig} (bt : TreeTable E)

/-- The continuation of a trip of `denoteWhileT` after the body. -/
def whileBodyK (n : Nat) (c body : ImpExpr) : Outcome × Env → CallTree E (Outcome × Env)
  | (.val (.controlFlow true v), e2) => .ret (.val v, e2)
  | (.val (.controlFlow false _), e2) => denoteWhileT bt n c body e2
  | (.val _, e2) => denoteWhileT bt n c body e2
  | (o, e2) => .ret (o, e2)

/-- One trip of a `whileFold` loop on a flag that reads the Boolean `b`. -/
theorem whileT_var_succ (n : Nat) (g : String) (body : ImpExpr) (env : Env) (b : Bool)
    (hg : env g = some (.bool b)) :
    denoteWhileT bt (n + 1) (.var g) body env =
      if b then (denoteT bt (n + 1) body env).bind (whileBodyK bt n (.var g) body)
      else .ret (.val .unit, env) := by
  rw [NFCallTreeWhileTrue.whileT_succ_run,
    NFCallTreeRepeatCount.denoteT_var_run bt (n + 1) g env _ hg]
  cases b <;> rfl

/-- The continuation of a trip at a value that is not a control-flow value is the next trip. -/
theorem whileBodyK_val (n : Nat) (c body : ImpExpr) {w : Value} (hw : w.isControlFlow = false)
    (e2 : Env) : whileBodyK bt n c body (.val w, e2) = denoteWhileT bt n c body e2 := by
  cases w with
  | controlFlow k u => cases hw
  | _ => rfl

end While

section WhileRel

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- The step of the `while` loop of the front at an unset flag returns the flag and the
    carried tuple. -/
theorem treeAt_whileOutStep_false (tf : Nat) {Γ : Ctxt nfDialect} (cs : List NfTy)
    (gV : Var (d := nfDialect) (cs ++ Γ) NfTy.bit) (ob : Out (cs ++ Γ))
    (rets : HVector (fun t => Var ob.Δ t) cs) (acc : Valuation (d := nfDialect) cs)
    (V : Valuation Γ) (h : gV.lookup (hvAppend acc V) = false) :
    treeAt linkReader tE tf (whileOutStep cs gV ob rets) (hvAppend acc V) =
      .ret (some (HVector.cons (t := NfTy.bit) false acc)) := by
  show obind (if HasBoolBit.toBool (d := nfDialect) (gV.lookup (hvAppend acc V)) then
      treeAt linkReader tE tf (ob.pre.plug (.ret (.cons (ob.pre.wk gV) rets))) (hvAppend acc V)
    else treeAt linkReader tE tf (.ret (.cons gV (headVars cs))) (hvAppend acc V)) (fun r =>
      treeAt linkReader tE tf (.ret (headVars (NfTy.bit :: cs))) (hvAppend r (hvAppend acc V)))
    = _
  simp only [show HasBoolBit.toBool (d := nfDialect) (gV.lookup (hvAppend acc V)) = false from h,
    Bool.false_eq_true, ite_false]
  show CallTree.ret (some (Expr.lookupArgs (headVars (NfTy.bit :: cs))
    (hvAppend (Expr.lookupArgs (HVector.cons gV (headVars cs)) (hvAppend acc V))
      (hvAppend acc V)))) = _
  rw [lookupArgs_headVars]
  show CallTree.ret (some (HVector.cons (gV.lookup (hvAppend acc V))
    (Expr.lookupArgs (headVars cs) (hvAppend acc V)))) = _
  rw [lookupArgs_headVars, h]

/-- The step of the `while` loop of the front at a set flag runs the body and returns the flag
    and the carried variables at its hole. -/
theorem treeAt_whileOutStep_true (tf : Nat) {Γ : Ctxt nfDialect} (cs : List NfTy)
    (gV : Var (d := nfDialect) (cs ++ Γ) NfTy.bit) (ob : Out (cs ++ Γ))
    (rets : HVector (fun t => Var ob.Δ t) cs) (X : Valuation (d := nfDialect) (cs ++ Γ))
    (h : gV.lookup X = true) :
    treeAt linkReader tE tf (whileOutStep cs gV ob rets) X =
      obind (preTreeAt linkReader tE tf ob.pre X) fun W =>
        .ret (some (HVector.cons (t := NfTy.bit) ((ob.pre.wk gV).lookup W)
          (Expr.lookupArgs rets W))) := by
  show obind (if HasBoolBit.toBool (d := nfDialect) (gV.lookup X) then
      treeAt linkReader tE tf (ob.pre.plug (.ret (.cons (ob.pre.wk gV) rets))) X
    else treeAt linkReader tE tf (.ret (.cons gV (headVars cs))) X) (fun r =>
      treeAt linkReader tE tf (.ret (headVars (NfTy.bit :: cs))) (hvAppend r X)) = _
  rw [show HasBoolBit.toBool (d := nfDialect) (gV.lookup X) = true from h, ite_eq_left rfl,
    treeAt_plug, obind_assoc]
  congr 1
  funext W
  show CallTree.ret (some (Expr.lookupArgs (headVars (NfTy.bit :: cs))
    (hvAppend (Expr.lookupArgs (HVector.cons (ob.pre.wk gV) rets) W) X))) = _
  rw [lookupArgs_headVars]
  rfl

/-- **The trips of the `while` loop of the front.** From an environment and a carried tuple
    satisfying `Inv`, the source loop at the fuel `n` and the iteration of the step at a count
    `m ≥ n`, each body at the target fuel `tf ≥ m`, are related: a source value is the unit
    value, matched by a final carried tuple satisfying `Inv` with the final environment. -/
theorem whileTrips_relT (g : String) (body : ImpExpr) {Γ : Ctxt nfDialect} (V : Valuation Γ)
    {cs : List NfTy} (tf : Nat) (gV : Var (d := nfDialect) (cs ++ Γ) NfTy.bit)
    (ob : Out (cs ++ Γ)) (rets : HVector (fun t => Var ob.Δ t) cs) (σB : NfEnv (cs ++ Γ))
    (Inv : Env → Valuation (d := nfDialect) cs → Prop)
    (HG : ∀ e acc, Inv e acc → e g = some (.bool (gV.lookup (hvAppend acc V))))
    (HB : ∀ fuel', fuel' ≤ tf → RelT h₁ tE fuel' tf body σB ob)
    (HE : ∀ e acc, Inv e acc → EnvRel σB e (hvAppend acc V))
    (KP : Env → Outcome × Env → Prop)
    (HK : ∀ fuel' e, LeafP (KP e) (denoteT evTable fuel' body e))
    (HI : ∀ e acc e2 W v, Inv e acc → KP e (.val v, e2) → EnvRel ob.σ e2 W →
      Inv e2 (Expr.lookupArgs rets W)) :
    ∀ (n m : Nat), n ≤ m → m ≤ tf → ∀ e acc, Inv e acc →
      RuttS h₁ ImpRE ImpRA (fun r w => ∃ accF, r.1 = .val .unit ∧ w = some accF ∧ Inv r.2 accF)
        SrcFail (denoteWhileT evTable n (.var g) body e)
        (owhileIter (fun acc => treeAt linkReader tE tf (whileOutStep cs gV ob rets)
          (hvAppend acc V)) m acc) := by
  intro n
  induction n with
  | zero =>
    intro m _ _ e acc _
    rw [NFCallTreeWhileTrue.whileT_zero_run]
    exact .fail fun v h => by cases h
  | succ n ih =>
    intro m hm hmt e acc hinv
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [whileT_var_succ evTable n g body e _ (HG e acc hinv)]
    cases hb : gV.lookup (hvAppend acc V) with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      show RuttS _ _ _ _ _ _ (obind (treeAt linkReader tE tf (whileOutStep cs gV ob rets)
        (hvAppend acc V)) _)
      rw [treeAt_whileOutStep_false tf cs gV ob rets acc V hb]
      exact .ret ⟨acc, rfl, rfl, hinv⟩
    | true =>
      simp only [ite_true]
      show RuttS _ _ _ _ _ _ (obind (treeAt linkReader tE tf (whileOutStep cs gV ob rets)
        (hvAppend acc V)) _)
      rw [treeAt_whileOutStep_true tf cs gV ob rets _ hb, obind_assoc]
      simp only [obind_ret_some]
      refine ruttS_obindK (ruttS_tgtLeaf (ruttS_srcLeaf (HB (n + 1) (by omega) e _ (HE e acc hinv))
        (HK (n + 1) e)) (preTreeAt_wk linkReader tE tf ob.pre (hvAppend acc V)))
        (fun r W hr => ?_) (fun r w ⟨⟨⟨_, _, _, hw, _⟩, _⟩, _⟩ => ⟨_, hw⟩)
        (fun r hf t => ?_)
      · obtain ⟨⟨⟨v, W', h1, hW, hrelW, hv⟩, hkp⟩, hwk⟩ := hr
        cases hW
        rcases r with ⟨o1, e2⟩
        dsimp only at h1 hrelW hkp hv
        subst h1
        rw [hv] at hkp ⊢
        rw [whileBodyK_val evTable n _ body (enc_isControlFlow _ _), hwk W rfl, hb]
        exact ih m (by omega) (by omega) e2 _ (HI e acc e2 W _ hinv hkp hrelW)
      · rcases r with ⟨o1, e2⟩
        cases o1 with
        | val v => exact absurd rfl (hf v)
        | _ => exact .fail hf

/-- **A `while` loop on a flag relates the trees**, at every target fuel at least the source
    fuel, when the front relates the trees of its body at every such pair of fuels. -/
theorem whileFold_relT (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat)
    (hle : fuel ≤ tf) (tgt : Option String) (g : String) (body : ImpExpr)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.whileFold (.var g) body) = some o)
    (HB : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) {o' : Out Δ},
      impToNF sigOf none σ' body = some o' → ∀ fuel' tf', fuel' ≤ tf' →
        RelT h₁ tE fuel' tf' body σ' o') :
    RelT h₁ tE fuel tf (.whileFold (.var g) body) σ o := by
  simp only [impToNF] at h
  have hlen : ((condCarried σ body body).map (·.1)).length =
      (entriesVars (condCarried σ body body)).1.length := by
    rw [List.length_map, entriesVars_length]
  have hfr : ∀ x, x ∉ (condCarried σ body body).map (·.1) → ∀ q, σ.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) body = true :=
    fun x hx _ hl => (frameOk_of_not_condCarried σ body body hl hx).1
  have hcar : ∀ env V, EnvRel σ env V → CarriedRel env ((condCarried σ body body).map (·.1))
      (entriesVars (condCarried σ body body)).1
      (Expr.lookupArgs (entriesVars (condCarried σ body body)).2 V) :=
    fun env V hrel => CarriedRel.of_entries hrel _ (condCarried_lookup σ body body)
  generalize (condCarried σ body body).map (·.1) = xs at h hlen hfr hcar
  generalize entriesVars (condCarried σ body body) = EV at h hlen hcar
  obtain ⟨cs, inits⟩ := EV
  dsimp only at h hlen hcar
  have hc := whileOut_whileCarry tgt σ g xs cs inits _ h
  simp only [whileOut, hc, ite_true, Option.bind_eq_some_iff] at h
  obtain ⟨⟨pt, pv⟩, hg, h⟩ := h
  split at h
  case isFalse => cases h
  rename_i hpt
  dsimp only at hpt
  subst hpt
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ob, hob, rets, hrets, rfl⟩ := h
  intro env V hrel
  let Inv : Env → Valuation (d := nfDialect) cs → Prop := fun e acc =>
    CarriedRel e xs cs acc ∧ ∀ x, x ∉ xs → ∀ t (v : Var Γ t), σ.lookup x = some ⟨t, v⟩ →
      e x = some (enc t (v.lookup V))
  have hB : ∀ e acc, Inv e acc → EnvRel (whileEnv σ xs cs (headVars cs)
      fun v => Var.shiftApp (d := nfDialect) cs v) e (hvAppend acc V) := fun e acc hinv =>
    EnvRel.whileEnv σ xs cs hlen (headVars cs) _ (by rw [lookupArgs_headVars]; exact hinv.1)
      hinv.2 (fun t v => Var.lookup_shiftApp cs acc v V)
  have hT := whileTrips_relT (h₁ := h₁) (tE := tE) g body V tf pv ob rets _ Inv
    (fun e acc hinv => hB e acc hinv g _ pv hg) (fun fuel' hf => HB _ hob fuel' tf hf) hB
    (fun e r => ∀ y, _root_.Hax.InlineLocalClosures.IsErr r.1 ∨ y ∈ xs ∨ σ.lookup y = none ∨
      r.2 y = e y)
    (fun fuel' e => keeps_leafP body σ xs hfr fuel' e)
    (fun e acc e2 W v hinv hkp hrelW => ⟨CarriedRel.of_varsAt hrelW xs cs hrets,
      fun y hy t u hl => by
        rcases hkp y with he | hm | hn | hk
        · obtain ⟨_, he⟩ := he
          cases he
        · exact absurd hm hy
        · rw [hl] at hn
          cases hn
        · exact hk.trans (hinv.2 y hy t u hl)⟩)
    fuel tf hle le_rfl env _ ⟨hcar env V hrel, fun x _ t v hl => hrel x t v hl⟩
  rw [NFCallTreeWhileTrue.denoteT_whileFold, ← bind_ret (denoteWhileT evTable fuel _ body env)]
  show RuttS _ _ _ _ _ _ (obind (owhileIter _ tf _) _)
  refine ruttS_obindK hT (fun r accF hr => ?_) (fun r w ⟨_, _, hw, _⟩ => ⟨_, hw⟩)
    (fun r hf t => .fail hf)
  obtain ⟨accF', h1, hacc, hinvF⟩ := hr
  cases hacc
  rw [preTreeAt_bind1N tE tf tgt _ .constUnit .nil _ fun _ => rfl]
  rcases r with ⟨o1, e'⟩
  dsimp only at h1 hinvF
  subst h1
  exact .ret ⟨_, _, rfl, rfl, (hB e' _ hinvF).mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩

end WhileRel


end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF
