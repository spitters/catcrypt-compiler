/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont

/-!
# The select lowering at the level of call trees

The select lowering `NFProg.lowerSelects` replaces a branch whose arms are straight-line
programs of speculatable operations by the bindings of both arms and one select per result.
The arms have no `call`, so at the pure reader each arm is a leaf of `some` value
(`treeAt_straightSpec`), and running both arms adds no event. The lowered program has the
call tree of its input, at every reader-free tree call environment and fuel
(`treeAt_lowerSelects`); the proof follows `NFProg.denote_lowerSel` clause by clause, with
trees in place of denotations.

## Main results

* `treeAt_straightSpec`: a straight-line program of speculatable operations has the tree of
  a leaf of `some` value.
* `emitArm?_treeAt`, `emitSels_treeAt`, `lowerIte?_treeAt`: the trees of the parts of a
  lowered branch.
* `treeAt_lowerSel`, `treeAt_lowerSelects`: the lowering keeps the call tree.
* `refinesT_lowerSelectsStep`: the stage lemma of `lowerSelectsStep` at `mfEnv`.
* `LeafOK`, `leafOK_obind`, `leafOK_ofoldl`, `leafOK_owhileIter`, `obind_congr_inv`,
  `ofoldl_congr_inv`, `owhileIter_congr_inv`: invariants of the leaves of a tree under every
  answer, and the congruences of the tree combinators under an invariant.
* `retsWithin_leafOK`, `carriedGo_treeAt`, `treeAt_loopRange`, `refinesT_synRangeStep`: the
  checker of the range stage at the tree level, and the stage lemma of `synRangeStep`.
* `treeAt_nfGo_env`, `treeAt_aegraphOptNF_env`: the e-graph pass keeps the tree at every tree
  call environment.
* `refinesT_jasminTail`, `ruttS_jasminTail`: the steps of `extChainCore` in `jasminDialect`,
  from the tree `nfProgTree` of their input to the tree `mfTree` of their output, and their
  composition after a relation `RuttS`.

The range stage drops masks on the strength of intervals of the variables a loop carries. The
interval of a result of a call is the full lane range, so the invariant of the checker holds of
every leaf of the tree under every answer to every event (`retsWithin_leafOK`), and the stage
keeps the tree.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont
open CatCrypt.Crypto.SecureCompilation.VIR.NFProg (Agrees agrees_id agrees_lift agrees_comp
  appLift agrees_appLift bindHom agrees_bindHom lookupArgs_renameVars denoteM_rename lowerSel
  lowerSelects lowerIte? emitArm? emitSels straightSpec Lowerable)
open Ctxt (Var Valuation)

section Generic

variable {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
  [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] [HasSelect d]
  (tE : TreeCallEnv E d) (fuel : Nat)

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option]
  [HasSelect d] in
/-- Unfolding lemma of `obind` at a leaf of `some` value: the continuation at the value. -/
theorem obind_ret_some {α β : Type} (a : α) (k : α → CallTree E (Option β)) :
    obind (.ret (some a)) k = k a :=
  rfl

/-- **A straight-line program of speculatable operations is a leaf** of `some` value at the
    pure reader. -/
theorem treeAt_straightSpec {Γ : Ctxt d} {rs : List d.Ty} (p : NFProg d Γ rs)
    (hp : straightSpec p = true) :
    ∀ V : Valuation Γ, ∃ A, treeAt pureReader tE fuel p V = .ret (some A) := by
  induction p with
  | ret vs => exact fun _ => ⟨_, rfl⟩
  | var e k ih =>
    intro V
    simp only [straightSpec, Bool.and_eq_true] at hp
    obtain ⟨op, rfl, args⟩ := e
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
      (HasSelect.isSome_denoteM op hp.1.1 (Expr.lookupArgs args V))
    simp only [treeAt, pureReader]
    rw [show Expr.denoteM (M := Option) ⟨op, rfl, args⟩ V = some x from hx]
    exact ih hp.2 _
  | forLoop => simp [straightSpec] at hp
  | ifThenElse => simp [straightSpec] at hp
  | whileLoop => simp [straightSpec] at hp
  | call => simp [straightSpec] at hp

omit [HasSelect d] in
/-- **The tree of `emitArm?`.** If every program the continuation returns at a renaming
    relating `W` to `W'` has at `W'` the tree `G` of the values of its variables, a program
    `emitArm? p ren kont` returns has the tree of `p` followed by `G`. -/
theorem emitArm?_treeAt {ts : List d.Ty} {Γ : Ctxt d} {rs : List d.Ty} (p : NFProg d Γ rs) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ)
      (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
        Option (NFProg d Δ' ts))
      (V : Valuation Γ) (W : Valuation Δ)
      (G : Valuation rs → CallTree E (Option (Valuation ts))),
      Agrees ren V W →
      (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs)
        (W' : Valuation Δ'), Agrees r W W' → ∀ q, kont r res = some q →
          treeAt pureReader tE fuel q W' = G (Expr.lookupArgs res W')) →
      ∀ q, emitArm? p ren kont = some q →
        treeAt pureReader tE fuel q W = obind (treeAt pureReader tE fuel p V) G := by
  induction p with
  | ret vs =>
    intro Δ ren kont V W G hren hk q hq
    rw [hk (fun v => v) _ W (agrees_id W) q hq, lookupArgs_renameVars hren]
    rfl
  | var e k ih =>
    intro Δ ren kont V W G hren hk q hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [treeAt, pureReader, denoteM_rename hren, obind_assoc]
    congr 1
    funext x
    exact ih _ _ _ _ G (agrees_lift hren x)
      (fun r res W' hr q hq => hk _ res W' (fun v => hr (.there v)) q hq) q' hq'
  | forLoop => intro _ _ _ _ _ _ _ _ q hq; simp [emitArm?] at hq
  | ifThenElse => intro _ _ _ _ _ _ _ _ q hq; simp [emitArm?] at hq
  | whileLoop => intro _ _ _ _ _ _ _ _ q hq; simp [emitArm?] at hq
  | call => intro _ _ _ _ _ _ _ _ q hq; simp [emitArm?] at hq

/-- **The tree of `emitSels`.** If every program the continuation returns at a renaming
    relating `W` to `W'` has the tree `G` of the values of its variables, the selects have
    the tree `G` at the values of `va` when `c` reads as `true` and at those of `vb`
    otherwise. -/
theorem emitSels_treeAt {ts : List d.Ty} : ∀ {Δ : Ctxt d} {rs : List d.Ty}
    (h : rs.all HasSelect.selects = true) (c : Var Δ (HasBitType.bit (d := d)))
    (va vb : HVector (fun t => Var Δ t) rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts)
    (W : Valuation Δ) (G : Valuation rs → CallTree E (Option (Valuation ts))),
    (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs)
      (W' : Valuation Δ'), Agrees r W W' →
        treeAt pureReader tE fuel (kont r res) W' = G (Expr.lookupArgs res W')) →
    treeAt pureReader tE fuel (emitSels h c va vb kont) W =
      G (if HasBoolBit.toBool (d := d) (c.lookup W) then Expr.lookupArgs va W
        else Expr.lookupArgs vb W)
  | _, [], _, _, .nil, .nil, kont, W, G, hk => by
      rw [emitSels, hk _ _ W (agrees_id W)]
      split <;> rfl
  | _, _ :: _, h, c, .cons a va, .cons b vb, kont, W, G, hk => by
      rw [emitSels]
      simp only [treeAt, pureReader, HasSelect.denoteM_sel]
      rw [obind_ret_some, emitSels_treeAt _ _ _ _ _ _
        (fun R => G (.cons (if HasBoolBit.toBool (d := d) (c.lookup W) then a.lookup W
          else b.lookup W) R)) (fun r res W' hr => ?_)]
      · rw [lookupArgs_shiftVars, lookupArgs_shiftVars]
        change G (HVector.cons _ (if HasBoolBit.toBool (d := d) (c.lookup W) then _ else _)) = _
        cases HasBoolBit.toBool (d := d) (c.lookup W) <;> rfl
      · rw [hk _ _ W' (fun v => hr (.there v))]
        change G (HVector.cons ((r .here).lookup W') _) = _
        rw [hr .here]
        rfl

/-- **The tree of `lowerIte?`.** If every program the continuation returns at a renaming
    relating `W` to `W'` has the tree `G` of the values of its variables, a program
    `lowerIte? c thn els kont` returns has the tree of the branch on `c` followed by `G`. -/
theorem lowerIte?_treeAt {ts : List d.Ty} {Δ : Ctxt d} {rs : List d.Ty}
    (c : Var Δ (HasBitType.bit (d := d))) (thn els : NFProg d Δ rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts)
    (W : Valuation Δ) (G : Valuation rs → CallTree E (Option (Valuation ts)))
    (hk : ∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs)
      (W' : Valuation Δ'), Agrees r W W' →
        treeAt pureReader tE fuel (kont r res) W' = G (Expr.lookupArgs res W'))
    (q : NFProg d Δ ts) (hq : lowerIte? c thn els kont = some q) :
    treeAt pureReader tE fuel q W =
      obind (if HasBoolBit.toBool (d := d) (c.lookup W) then treeAt pureReader tE fuel thn W
        else treeAt pureReader tE fuel els W) G := by
  unfold lowerIte? at hq
  split at hq
  next h =>
    simp only [Lowerable, Bool.and_eq_true] at h
    obtain ⟨A, hA⟩ := treeAt_straightSpec tE fuel thn h.1.2 W
    obtain ⟨B, hB⟩ := treeAt_straightSpec tE fuel els h.2 W
    rw [emitArm?_treeAt tE fuel thn _ _ W W
      (fun A => obind (treeAt pureReader tE fuel els W) fun B =>
        G (if HasBoolBit.toBool (d := d) (c.lookup W) then A else B)) (agrees_id W) ?_ q hq]
    · rw [hA, hB]
      cases HasBoolBit.toBool (d := d) (c.lookup W) <;> rfl
    · intro Δ1 r1 va W1 hr1 q1 hq1
      rw [emitArm?_treeAt tE fuel els r1 _ W W1
        (fun B => G (if HasBoolBit.toBool (d := d) (c.lookup W)
          then Expr.lookupArgs va W1 else B)) hr1 ?_ q1 hq1]
      intro Δ2 r2 vb W2 hr2 q2 hq2
      obtain rfl := Option.some.inj hq2
      rw [emitSels_treeAt tE fuel _ _ _ _ _ W2 G
        (fun r3 res W3 hr3 => hk _ res W3 (agrees_comp (agrees_comp hr1 hr2) hr3)),
        hr2 (r1 c), hr1 c, lookupArgs_renameVars hr2]
  next => cases hq

/-- **The lowering keeps the tree.** A program lowered along a renaming relating `V` to `W`
    has at `W` the tree of the source at `V`. -/
theorem treeAt_lowerSel {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ) (W : Valuation Δ),
      Agrees ren V W →
        treeAt pureReader tE fuel (lowerSel p ren) W = treeAt pureReader tE fuel p V := by
  induction p with
  | ret vs =>
    intro Δ ren V W h
    simp only [lowerSel, treeAt, lookupArgs_renameVars h]
  | var e k ih =>
    intro Δ ren V W h
    simp only [lowerSel, treeAt, pureReader, denoteM_rename h]
    congr 1
    funext x
    exact ih _ _ _ (agrees_lift h x)
  | forLoop count inits body k ihb ihk =>
    intro Δ ren V W h
    have hb : ∀ acc i, treeAt pureReader tE fuel (lowerSel body (appLift _ (Ctxt.Hom.lift ren)))
        (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W)) =
        treeAt pureReader tE fuel body (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) :=
      fun acc i => ihb _ _ _ (agrees_appLift (agrees_lift h _) _ acc)
    have hk : ∀ acc, treeAt pureReader tE fuel (lowerSel k (appLift _ ren)) (hvAppend acc W) =
        treeAt pureReader tE fuel k (hvAppend acc V) :=
      fun acc => ihk _ _ _ (agrees_appLift h _ acc)
    simp only [lowerSel, treeAt, lookupArgs_renameVars h, h count, hb, hk]
  | ifThenElse cond thn els k iht ihe ihk =>
    intro Δ ren V W h
    have hk : ∀ r, treeAt pureReader tE fuel (lowerSel k (appLift _ ren)) (hvAppend r W) =
        treeAt pureReader tE fuel k (hvAppend r V) :=
      fun r => ihk _ _ _ (agrees_appLift h _ r)
    have harms : (if HasBoolBit.toBool (d := d) ((ren cond).lookup W)
          then treeAt pureReader tE fuel (lowerSel thn ren) W
          else treeAt pureReader tE fuel (lowerSel els ren) W) =
        (if HasBoolBit.toBool (d := d) (cond.lookup V) then treeAt pureReader tE fuel thn V
          else treeAt pureReader tE fuel els V) := by
      rw [h cond, iht _ _ _ h, ihe _ _ _ h]
    rw [lowerSel]
    split
    next q hq =>
      rw [lowerIte?_treeAt tE fuel _ _ _ _ W
        (fun r => treeAt pureReader tE fuel k (hvAppend r V))
        (fun r res W' hr => ihk _ _ _ (agrees_bindHom (agrees_comp h hr) res)) q hq, harms]
      rfl
    next =>
      rw [treeAt, harms]
      simp only [hk]
      rfl
  | whileLoop inits body k ihb ihk =>
    intro Δ ren V W h
    have hb : ∀ acc, treeAt pureReader tE fuel (lowerSel body (appLift _ ren)) (hvAppend acc W) =
        treeAt pureReader tE fuel body (hvAppend acc V) :=
      fun acc => ihb _ _ _ (agrees_appLift h _ acc)
    have hk : ∀ acc, treeAt pureReader tE fuel (lowerSel k (appLift _ ren)) (hvAppend acc W) =
        treeAt pureReader tE fuel k (hvAppend acc V) :=
      fun acc => ihk _ _ _ (agrees_appLift h _ acc)
    simp only [lowerSel, treeAt, lookupArgs_renameVars h, hb, hk]
  | call f args k ih =>
    intro Δ ren V W h
    have hk : ∀ r, treeAt pureReader tE fuel (lowerSel k (appLift _ ren)) (hvAppend r W) =
        treeAt pureReader tE fuel k (hvAppend r V) :=
      fun r => ih _ _ _ (agrees_appLift h _ r)
    simp only [lowerSel, treeAt, lookupArgs_renameVars h, hk]

/-- **`lowerSelects p` has the tree of `p`**, at every tree call environment, fuel and
    valuation. -/
theorem treeAt_lowerSelects {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (V : Valuation Γ) :
    treeAt pureReader tE fuel (lowerSelects p) V = treeAt pureReader tE fuel p V :=
  treeAt_lowerSel tE fuel p _ V V (agrees_id V)

end Generic

/-- **The stage lemma of `lowerSelectsStep` at the tree level**: the output has the tree of
    its input at `mfEnv`, so it refines it at every source handler. -/
theorem refinesT_lowerSelectsStep
    (h₁ : ∀ e : (nfCallSig JasminDialect.jasminDialect).Event,
      (nfCallSig JasminDialect.jasminDialect).Resp e) (fuel : Nat)
    {Γ : Ctxt JasminDialect.jasminDialect} {ts : List JasminDialect.JasminTy}
    {p q : NFProg JasminDialect.jasminDialect Γ ts}
    (hf : (NFProgPasses.lowerSelectsStep Γ ts).run p = some q) (X : Valuation Γ) :
    RefinesT h₁ (mfTree fuel p X) (mfTree fuel q X) := by
  obtain rfl : lowerSelects p = q := Option.some.inj hf
  rw [mfTree, mfTree, treeAt_lowerSelects]
  exact RefinesT.refl _

/-! ## Invariants of the leaves of a tree -/

section Leaves

variable {E : EventSig}

/-- **Every leaf of `some` value satisfies `Q`**, under every answer to every event. -/
def LeafOK {α : Type} (Q : α → Prop) : CallTree E (Option α) → Prop
  | .ret o => ∀ a, o = some a → Q a
  | .vis _ k => ∀ r, LeafOK Q (k r)

/-- A property that holds of every value holds of every leaf. -/
theorem leafOK_of {α : Type} {Q : α → Prop} (h : ∀ a, Q a) :
    ∀ t : CallTree E (Option α), LeafOK Q t
  | .ret _ => fun a _ => h a
  | .vis _ k => fun r => leafOK_of h (k r)

/-- `LeafOK` is monotone in the property. -/
theorem LeafOK.mono {α : Type} {Q Q' : α → Prop} (h : ∀ a, Q a → Q' a) :
    ∀ {t : CallTree E (Option α)}, LeafOK Q t → LeafOK Q' t
  | .ret _, ht => fun a ha => h a (ht a ha)
  | .vis _ _, ht => fun r => LeafOK.mono h (ht r)

/-- Sequencing keeps `LeafOK`: leaves of the prefix satisfy `Q`, and the continuation at a
    value satisfying `Q` has leaves satisfying `R`. -/
theorem leafOK_obind {α β : Type} {Q : α → Prop} {R : β → Prop}
    {k : α → CallTree E (Option β)} (hk : ∀ a, Q a → LeafOK R (k a)) :
    ∀ {t : CallTree E (Option α)}, LeafOK Q t → LeafOK R (obind t k)
  | .ret none, _ => fun _ h => by cases h
  | .ret (some a), ht => hk a (ht a rfl)
  | .vis _ _, ht => fun r => leafOK_obind hk (ht r)

/-- Two continuations that agree on the values satisfying `Q` give the same sequencing after
    a prefix whose leaves satisfy `Q`. -/
theorem obind_congr_inv {α β : Type} {Q : α → Prop} {k₁ k₂ : α → CallTree E (Option β)}
    (hk : ∀ a, Q a → k₁ a = k₂ a) :
    ∀ {t : CallTree E (Option α)}, LeafOK Q t → obind t k₁ = obind t k₂
  | .ret none, _ => rfl
  | .ret (some a), ht => hk a (ht a rfl)
  | .vis e _, ht => congrArg (CallTree.vis e) (funext fun r => obind_congr_inv hk (ht r))

/-- A fold whose step keeps `P` keeps `P` at its leaves. -/
theorem leafOK_ofoldl {α β : Type} {P : β → Prop} {f : β → α → CallTree E (Option β)}
    (hf : ∀ b a, P b → LeafOK P (f b a)) :
    ∀ (l : List α) (b : β), P b → LeafOK P (ofoldl f l b)
  | [], _, hb => fun _ h => by cases h; exact hb
  | a :: l, b, hb => leafOK_obind (fun b' hb' => leafOK_ofoldl hf l b' hb') (hf b a hb)

/-- Two folds whose steps agree on the states satisfying `P`, from a state satisfying `P`,
    are equal when the step keeps `P`. -/
theorem ofoldl_congr_inv {α β : Type} (P : β → Prop)
    (f g : β → α → CallTree E (Option β))
    (hg : ∀ b a, P b → g b a = f b a) (hf : ∀ b a, P b → LeafOK P (f b a)) :
    ∀ (l : List α) (b : β), P b → ofoldl g l b = ofoldl f l b
  | [], _, _ => rfl
  | a :: l, b, hb => by
    change obind (g b a) _ = obind (f b a) _
    rw [hg b a hb]
    exact obind_congr_inv (fun b' hb' => ofoldl_congr_inv P f g hg hf l b' hb') (hf b a hb)

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [HasBoolBit d]

/-- An exit-flag iteration whose body keeps `P` at the tail keeps `P` at its leaves. -/
theorem leafOK_owhileIter {cs : List d.Ty} {P : Valuation cs → Prop}
    {s : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs)))}
    (hs : ∀ a, P a → LeafOK (fun r => P r.tail) (s a)) :
    ∀ (n : Nat) (a : Valuation cs), P a → LeafOK P (NFProgCallTree.owhileIter s n a)
  | 0, _, _ => fun _ h => by cases h
  | n + 1, a, ha => leafOK_obind (fun r hr => by
      split
      · exact leafOK_owhileIter hs n _ hr
      · exact fun _ h => by cases h; exact hr) (hs a ha)

/-- Two exit-flag iterations whose bodies agree on the states satisfying `P`, from a state
    satisfying `P`, are equal when the body keeps `P` at the tail. -/
theorem owhileIter_congr_inv {cs : List d.Ty} (P : Valuation cs → Prop)
    (f g : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs))))
    (hg : ∀ a, P a → g a = f a) (hf : ∀ a, P a → LeafOK (fun r => P r.tail) (f a)) :
    ∀ (n : Nat) (a : Valuation cs), P a →
      NFProgCallTree.owhileIter g n a = NFProgCallTree.owhileIter f n a
  | 0, _, _ => rfl
  | n + 1, a, ha => by
    change obind (g a) _ = obind (f a) _
    rw [hg a ha]
    refine obind_congr_inv (fun r hr => ?_) (hf a ha)
    split
    · exact owhileIter_congr_inv P f g hg hf n _ hr
    · rfl

end Leaves

/-! ## The range stage -/

section Range

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy jasminDialect)
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep synAnn)

variable {E : EventSig} (tE : TreeCallEnv E jasminDialect) (fuel : Nat)

/-- **Soundness of the checker at the tree level.** Under an environment that holds of `V`,
    every leaf of `some` value of the tree of a program whose returns `retsWithin` accepts
    for `ivs` lies within `ivs`, under every answer to every event. -/
theorem retsWithin_leafOK : ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat)
    (a : CarriedAnn) (p : NFProg jasminDialect Γ ts) (ivs : List Iv) (V : Ctxt.Valuation Γ),
    len = Γ.length → EnvOK A V → retsWithin A len a p ivs = true →
    LeafOK (InvOK ts ivs) (treeAt pureReader tE fuel p V)
  | _, _, _, _, _, .ret vs, ivs, V, _, hA, hc => fun _ h => by
      cases h
      exact argsWithin_sound hA vs ivs hc
  | _, _, A, len, a, .var e k, ivs, V, hlen, hA, hc => by
      simp only [retsWithin] at hc
      simp only [treeAt, pureReader, Expr.denoteM_option_eq_some, obind_ret_some]
      exact retsWithin_leafOK _ (len + 1) a k ivs _ (by simp [hlen])
        (hA.cons (stageAbs_sound hA hlen e)) hc
  | _, _, A, len, a, .forLoop (cs := cs) count inits body k, ivs, V, hlen, hA, hc => by
      simp only [retsWithin] at hc
      simp only [treeAt]
      refine leafOK_obind (Q := CarriedOK (forInductive A len a inits body) cs a.ivs)
        (fun acc hacc => retsWithin_leafOK _ _ a.rest k ivs _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hacc hA) hc)
        (leafOK_ofoldl (fun acc i hP => ?_) _ _ (forInductive_init hA))
      cases hok : forInductive A len a inits body
      · exact leafOK_of (fun _ h => by cases h) _
      · have hok' := hok
        simp only [forInductive, Bool.and_eq_true] at hok'
        exact LeafOK.mono (fun _ hr _ => hr) (retsWithin_leafOK _ _ a.inner body a.ivs _
          (length_body cs _ hlen) (envOK_invApp cs a.ivs acc (hP hok) (envOK_topCons hA _))
          hok'.2)
  | _, _, A, len, a, .ifThenElse (rs := rs) cond thn els k, ivs, V, hlen, hA, hc => by
      simp only [retsWithin] at hc
      simp only [treeAt]
      exact leafOK_obind (Q := fun _ => True) (fun r _ => retsWithin_leafOK _ _ a.rest k ivs _
        (length_app rs hlen) (envOK_topApp rs r hA) hc) (leafOK_of (fun _ => trivial) _)
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k, ivs, V, hlen, hA, hc => by
      simp only [retsWithin] at hc
      simp only [treeAt]
      refine leafOK_obind (Q := CarriedOK (whileInductive A len a inits body) cs a.ivs)
        (fun acc hacc => retsWithin_leafOK _ _ a.rest k ivs _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hacc hA) hc)
        (leafOK_owhileIter (fun acc hP => ?_) _ _ (whileInductive_init hA))
      cases hok : whileInductive A len a inits body
      · exact leafOK_of (fun _ h => by cases h) _
      · have hok' := hok
        simp only [whileInductive, Bool.and_eq_true] at hok'
        exact LeafOK.mono (fun r hr _ => invOK_tail r hr) (retsWithin_leafOK _ _ a.inner body _ _
          (length_app cs hlen) (envOK_invApp cs a.ivs acc (hP hok) hA) hok'.2)
  | _, _, A, len, a, .call (rs := rs) f args k, ivs, V, hlen, hA, hc => by
      simp only [retsWithin] at hc
      simp only [treeAt]
      exact leafOK_obind (Q := fun _ => True) (fun r _ => retsWithin_leafOK _ _ a k ivs _
        (length_app rs hlen) (envOK_topApp rs r hA) hc) (leafOK_of (fun _ => trivial) _)

/-- The tree of the body of a counted loop keeps `CarriedOK` at the result of the checker. -/
theorem forInductive_leafOK {Γ : JCtxt} {cs : List JasminTy} {A : AEnv Γ} {len : Nat}
    {a : CarriedAnn} {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V)
    (acc : Ctxt.Valuation (d := jasminDialect) cs) (i : Nat)
    (hP : CarriedOK (forInductive A len a inits body) cs a.ivs acc) :
    LeafOK (CarriedOK (forInductive A len a inits body) cs a.ivs)
      (treeAt pureReader tE fuel body
        (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V))) := by
  cases hok : forInductive A len a inits body
  · exact leafOK_of (fun _ h => by cases h) _
  · have hok' := hok
    simp only [forInductive, Bool.and_eq_true] at hok'
    exact LeafOK.mono (fun _ hr _ => hr) (retsWithin_leafOK tE fuel _ _ a.inner body a.ivs _
      (length_body cs _ hlen) (envOK_invApp cs a.ivs acc (hP hok) (envOK_topCons hA _)) hok'.2)

/-- The tree of the body of an exit-flag loop keeps `CarriedOK` at the tail of its leaves. -/
theorem whileInductive_leafOK {Γ : JCtxt} {cs : List JasminTy} {A : AEnv Γ} {len : Nat}
    {a : CarriedAnn} {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs)}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V)
    (acc : Ctxt.Valuation (d := jasminDialect) cs)
    (hP : CarriedOK (whileInductive A len a inits body) cs a.ivs acc) :
    LeafOK (fun r : Ctxt.Valuation (d := jasminDialect)
        (HasBitType.bit (d := jasminDialect) :: cs) =>
        CarriedOK (whileInductive A len a inits body) cs a.ivs r.tail)
      (treeAt pureReader tE fuel body (hvAppend acc V)) := by
  cases hok : whileInductive A len a inits body
  · exact leafOK_of (fun _ h => by cases h) _
  · have hok' := hok
    simp only [whileInductive, Bool.and_eq_true] at hok'
    exact LeafOK.mono (fun r hr _ => invOK_tail r hr) (retsWithin_leafOK tE fuel _ _ a.inner
      body _ _ (length_app cs hlen) (envOK_invApp cs a.ivs acc (hP hok) hA) hok'.2)

/-- **The range traversal keeps the tree.** Under an environment that holds of `V`, the
    output of `carriedGo` has at `V` the tree of its input, for every annotation. -/
theorem carriedGo_treeAt : ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat)
    (a : CarriedAnn) (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ),
    len = Γ.length → EnvOK A V →
      treeAt pureReader tE fuel (carriedGo A len a p) V = treeAt pureReader tE fuel p V
  | _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, A, len, a, .var e k, V, hlen, hA => by
      simp only [carriedGo, treeAt, pureReader, Expr.denoteM_option_eq_some,
        rangeExpr_denote hA hlen e, obind_ret_some]
      exact carriedGo_treeAt _ (len + 1) a k _ (by simp [hlen])
        (hA.cons (stageAbs_sound hA hlen e))
  | _, _, A, len, a, .forLoop (cs := cs) count inits body k, V, hlen, hA => by
      have hb : ∀ (acc : Ctxt.Valuation (d := jasminDialect) cs) (i : Nat),
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          treeAt pureReader tE fuel (carriedGo
              (carriedEnv (forInductive A len a inits body) cs a.ivs
                (topCons (HasWord64.word (d := jasminDialect)) A))
              (cs.length + (len + 1)) a.inner body)
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) =
            treeAt pureReader tE fuel body
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun acc i hP => carriedGo_treeAt _ _ a.inner body _ (length_body cs _ hlen)
          (envOK_carriedEnv cs a.ivs acc hP (envOK_topCons hA _))
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          treeAt pureReader tE fuel (carriedGo (carriedEnv (forInductive A len a inits body) cs
              a.ivs A) (cs.length + len) a.rest k) (hvAppend acc V) =
            treeAt pureReader tE fuel k (hvAppend acc V) :=
        fun acc hP => carriedGo_treeAt _ _ a.rest k _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA)
      have hs := forInductive_leafOK tE fuel (a := a) (inits := inits) (body := body) hlen hA
      have hi := forInductive_init (len := len) (a := a) (inits := inits) (body := body) hA
      simp only [carriedGo, treeAt]
      rw [ofoldl_congr_inv _ _ _ (fun acc i hP => hb acc i hP) (fun acc i hP => hs acc i hP)
        _ _ hi]
      exact obind_congr_inv hk (leafOK_ofoldl (fun acc i hP => hs acc i hP) _ _ hi)
  | _, _, A, len, a, .ifThenElse (rs := rs) cond thn els k, V, hlen, hA => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          treeAt pureReader tE fuel (carriedGo (topApp rs A) (rs.length + len) a.rest k)
              (hvAppend r V) = treeAt pureReader tE fuel k (hvAppend r V) :=
        fun r => carriedGo_treeAt _ _ a.rest k _ (length_app rs hlen) (envOK_topApp rs r hA)
      simp only [carriedGo, treeAt, hk, carriedGo_treeAt A len a.inner thn V hlen hA,
        carriedGo_treeAt A len a.other els V hlen hA]
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k, V, hlen, hA => by
      have hb : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          treeAt pureReader tE fuel (carriedGo (carriedEnv (whileInductive A len a inits body)
              cs a.ivs A) (cs.length + len) a.inner body) (hvAppend acc V) =
            treeAt pureReader tE fuel body (hvAppend acc V) :=
        fun acc hP => carriedGo_treeAt _ _ a.inner body _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA)
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          treeAt pureReader tE fuel (carriedGo (carriedEnv (whileInductive A len a inits body)
              cs a.ivs A) (cs.length + len) a.rest k) (hvAppend acc V) =
            treeAt pureReader tE fuel k (hvAppend acc V) :=
        fun acc hP => carriedGo_treeAt _ _ a.rest k _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA)
      have hs := whileInductive_leafOK tE fuel (a := a) (inits := inits) (body := body) hlen hA
      have hi := whileInductive_init (len := len) (a := a) (inits := inits) (body := body) hA
      simp only [carriedGo, treeAt]
      rw [owhileIter_congr_inv _ _ _ hb hs _ _ hi]
      exact obind_congr_inv hk (leafOK_owhileIter hs _ _ hi)
  | _, _, A, len, a, .call (rs := rs) f args k, V, hlen, hA => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          treeAt pureReader tE fuel (carriedGo (topApp rs A) (rs.length + len) a k)
              (hvAppend r V) = treeAt pureReader tE fuel k (hvAppend r V) :=
        fun r => carriedGo_treeAt _ _ a k _ (length_app rs hlen) (envOK_topApp rs r hA)
      simp only [carriedGo, treeAt, hk]

/-- **`loopRange a p` has the tree of `p`**, at every annotation, fuel and valuation. -/
theorem treeAt_loopRange {Γ : JCtxt} {ts : List JasminTy} (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ) :
    treeAt pureReader tE fuel (loopRange a p) V = treeAt pureReader tE fuel p V :=
  carriedGo_treeAt tE fuel _ _ a p V rfl (envOK_topEnv V)

end Range

/-! ## The e-graph pass at every tree call environment -/

section Aegraph

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF

variable {E : EventSig} {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty]
  [DialectSignature d] [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]
  (tE : TreeCallEnv E d)

omit [DecidableEq d.Ty] [DecidableEq d.Op] in
/-- A let-binding of a dialect with a pure denotation has the call tree of its continuation
    at the extended valuation, at every tree call environment. -/
theorem treeAt_var_pure_env (fuel : Nat) {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty}
    (e : Expr d Γ t) (k : NFProg d (t :: Γ) ts) (V : Valuation Γ) :
    treeAt pureReader tE fuel (.var e k) V =
      treeAt pureReader tE fuel k (V.extend (e.denote V)) := by
  simp only [treeAt, pureReader, Expr.denoteM_option_eq_some]
  rfl

/-- **The call tree of the traversal of the e-graph pass at every tree call environment**:
    under a state sound for `V`, the output of `nfGo R ρ S` has at `V` the tree of its input at
    the valuation pulled back along `ρ`. -/
theorem treeAt_nfGo_env (R : RuleSet d) (fuel : Nat) :
    ∀ {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d)
      (p : NFProg d Γ ts) (V : Valuation Δ), StSound V S →
      treeAt pureReader tE fuel (nfGo R ρ S p) V = treeAt pureReader tE fuel p (V.comap ρ)
  | _, _, _, ρ, _, .ret vs, V, _ => by
      simp only [nfGo, treeAt, Expr.lookupArgs_renameVars]
  | _, Δ, _, ρ, S, .var (t := s) e k, V, hS => by
      simp only [nfGo]
      split
      · rename_i w hc
        obtain ⟨hS', hw⟩ := stVar_sound R hS _ hc
        rw [treeAt_nfGo_env R fuel _ _ k V hS', comap_consHom, hw, Expr.denote_rename,
          treeAt_var_pure_env]
      · rename_i e2 hc
        obtain ⟨hS', hw⟩ := stOne_sound R hS _ hc
        rw [treeAt_var_pure_env, treeAt_nfGo_env R fuel _ _ k _ hS',
          Ctxt.Valuation.extend_comap_lift, hw, Expr.denote_rename, treeAt_var_pure_env]
      · rename_i s1 e1 e2 hc
        obtain ⟨hS', hw⟩ := stTwo_sound R hS _ hc
        rw [treeAt_var_pure_env, treeAt_var_pure_env, treeAt_nfGo_env R fuel _ _ k _ hS',
          comap_consHom, comap_wk2, treeAt_var_pure_env]
        rw [Expr.denote_rename] at hw
        rw [← hw]
        rfl
  | _, _, _, ρ, S, .forLoop (cs := cs) count inits body k, V, hS => by
      have hb : ∀ (acc : Valuation cs) (i : Nat),
          treeAt pureReader tE fuel (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body)
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) =
            treeAt pureReader tE fuel body
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) (V.comap ρ))) := by
        intro acc i
        refine (treeAt_nfGo_env R fuel _ S body _
            (stSound_append acc (stSound_extend (HasWord64.ofNat (d := d) i) hS))).trans ?_
        rw [comap_homLiftApp]
        exact congrArg (fun W => treeAt pureReader tE fuel body (hvAppend acc W))
          (Ctxt.Valuation.extend_comap_lift ρ V _)
      have hk : ∀ acc : Valuation cs,
          treeAt pureReader tE fuel (nfGo R (homLiftApp cs ρ) S k) (hvAppend acc V) =
            treeAt pureReader tE fuel k (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [treeAt_nfGo_env R fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, treeAt, hb, hk, Ctxt.Valuation.lookup_comap,
        Expr.lookupArgs_renameVars]
  | _, _, _, ρ, S, .ifThenElse (rs := rs) cond thn els k, V, hS => by
      have hk : ∀ r : Valuation rs,
          treeAt pureReader tE fuel (nfGo R (homLiftApp rs ρ) S k) (hvAppend r V) =
            treeAt pureReader tE fuel k (hvAppend r (V.comap ρ)) := by
        intro r
        rw [treeAt_nfGo_env R fuel _ S k _ (stSound_append r hS), comap_homLiftApp]
      simp only [nfGo, treeAt, hk, Ctxt.Valuation.lookup_comap,
        treeAt_nfGo_env R fuel ρ S thn V hS, treeAt_nfGo_env R fuel ρ S els V hS]
  | _, _, _, ρ, S, .whileLoop (cs := cs) inits body k, V, hS => by
      have hb : ∀ acc : Valuation cs,
          treeAt pureReader tE fuel (nfGo R (homLiftApp cs ρ) S body) (hvAppend acc V) =
            treeAt pureReader tE fuel body (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [treeAt_nfGo_env R fuel _ S body _ (stSound_append acc hS), comap_homLiftApp]
      have hk : ∀ acc : Valuation cs,
          treeAt pureReader tE fuel (nfGo R (homLiftApp cs ρ) S k) (hvAppend acc V) =
            treeAt pureReader tE fuel k (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [treeAt_nfGo_env R fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, treeAt, hb, hk, Expr.lookupArgs_renameVars]
  | _, _, _, ρ, S, .call (rs := rs) f args k, V, hS => by
      have hk : ∀ r : Valuation rs,
          treeAt pureReader tE fuel (nfGo R (homLiftApp rs ρ) S k) (hvAppend r V) =
            treeAt pureReader tE fuel k (hvAppend r (V.comap ρ)) := by
        intro r
        rw [treeAt_nfGo_env R fuel _ S k _ (stSound_append r hS), comap_homLiftApp]
      simp only [nfGo, treeAt, hk, Expr.lookupArgs_renameVars]

/-- **The e-graph pass keeps the call tree at every tree call environment.** -/
theorem treeAt_aegraphOptNF_env (R : RuleSet d) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (fuel : Nat) (V : Valuation Γ) :
    treeAt pureReader tE fuel (aegraphOptNF R p) V = treeAt pureReader tE fuel p V := by
  rw [aegraphOptNF, treeAt_nfGo_env tE R fuel _ _ p V (stSound_empty V),
    Ctxt.Valuation.comap_id]

end Aegraph

/-- **The stage lemma of `synRangeStep` at the tree level**: the output has the tree of its
    input at `mfEnv`, so it refines it at every source handler. -/
theorem refinesT_synRangeStep
    (h₁ : ∀ e : (nfCallSig JasminDialect.jasminDialect).Event,
      (nfCallSig JasminDialect.jasminDialect).Resp e) (fuel : Nat)
    {Γ : Ctxt JasminDialect.jasminDialect} {ts : List JasminDialect.JasminTy}
    {p q : NFProg JasminDialect.jasminDialect Γ ts}
    (hf : (Optimizer.Rewrite.RangeAnnSyn.synRangeStep Γ ts).run p = some q)
    (X : Valuation Γ) :
    RefinesT h₁ (mfTree fuel p X) (mfTree fuel q X) := by
  obtain rfl : Optimizer.Rewrite.RangeNFLoop.loopRange
      (Optimizer.Rewrite.RangeAnnSyn.synAnn p) p = q := Option.some.inj hf
  rw [mfTree, mfTree, treeAt_loopRange]
  exact RefinesT.refl _

/-! ## The steps of `extChainCore` in `jasminDialect` -/

section Tail

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy jasminDialect)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montifyStep montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldDialectStep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)

/-- **The steps of `extChainCore` in `jasminDialect` at the tree level.** The montify step,
    the field dialect step, the select lowering, the range stage and the e-graph pass at a rule
    set `R`, run in order from `p` to `q₅`: the tree `mfTree` of `q₅` refines the tree
    `nfProgTree` of `p`, at a source handler that answers each inner head by its value. -/
theorem refinesT_jasminTail
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh : ∀ (f : String) (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₁ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (fuel : Nat) (R : Optimizer.Rewrite.AegraphGeneric.RuleSet jasminDialect)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q₁ q₂ q₃ q₄ q₅ : NFProg jasminDialect Γ ts}
    (h1 : (montifyStep Γ ts).run p = some q₁)
    (h2 : (fieldDialectStep Γ ts).run q₁ = some q₂)
    (h3 : (NFProgPasses.lowerSelectsStep Γ ts).run q₂ = some q₃)
    (h4 : (synRangeStep Γ ts).run q₃ = some q₄)
    (h5 : (NFProgPasses.aegraphStep R Γ ts).run q₄ = some q₅) (X : Valuation Γ) :
    RefinesT h₁ (nfProgTree fuel p X) (mfTree fuel q₅ X) := by
  refine RefinesT.trans (refinesT_nfProgTree_montifyStep h₁ fuel hh h1 X) ?_
  refine RefinesT.trans (refinesT_fieldDialectStep h₁ fuel h2 X) ?_
  refine RefinesT.trans (refinesT_lowerSelectsStep h₁ fuel h3 X) ?_
  refine RefinesT.trans (refinesT_synRangeStep h₁ fuel h4 X) ?_
  obtain rfl : Optimizer.Rewrite.AegraphNF.aegraphOptNF R q₄ = q₅ := Option.some.inj h5
  rw [mfTree, mfTree, treeAt_aegraphOptNF_env mfEnv R q₄ fuel X]
  exact RefinesT.refl _

/-- **A relation to the tree of the input of the steps in `jasminDialect` is a relation to the
    tree of their output.** From `RuttS` at the source handler `h₀` to `nfProgTree` of `p`, at
    an intermediate handler `h₁` that answers related events with related answers and each
    inner head by its value, `RuttS` holds to `mfTree` of `q₅`. -/
theorem ruttS_jasminTail {E₀ : EventSig} {R₀ : Type} {h₀ : ∀ e : E₀.Event, E₀.Resp e}
    {RE : E₀.Event → (nfCallSig jasminDialect).Event → Prop}
    {RA : (e₀ : E₀.Event) → (e : (nfCallSig jasminDialect).Event) → E₀.Resp e₀ →
      (nfCallSig jasminDialect).Resp e → Prop}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {RR : R₀ → Option (Valuation (d := jasminDialect) ts) → Prop} {Fail : R₀ → Prop}
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hRA : ∀ e₀ e, RE e₀ e → RA e₀ e (h₀ e₀) (h₁ e))
    (hRR : ∀ r, RR r none → Fail r)
    (hh : ∀ (f : String) (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₁ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (fuel : Nat) (R : Optimizer.Rewrite.AegraphGeneric.RuleSet jasminDialect)
    {p q₁ q₂ q₃ q₄ q₅ : NFProg jasminDialect Γ ts}
    (h1 : (montifyStep Γ ts).run p = some q₁)
    (h2 : (fieldDialectStep Γ ts).run q₁ = some q₂)
    (h3 : (NFProgPasses.lowerSelectsStep Γ ts).run q₂ = some q₃)
    (h4 : (synRangeStep Γ ts).run q₃ = some q₄)
    (h5 : (NFProgPasses.aegraphStep R Γ ts).run q₄ = some q₅) (X : Valuation Γ)
    {t : CallTree E₀ R₀} (ht : RuttS h₀ RE RA RR Fail t (nfProgTree fuel p X)) :
    RuttS h₀ RE RA RR Fail t (mfTree fuel q₅ X) :=
  NFProgCallTreeOpt.RuttS.trans_refinesT hRA hRR ht
    (refinesT_jasminTail h₁ hh fuel R h1 h2 h3 h4 h5 X)

end Tail

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSel
