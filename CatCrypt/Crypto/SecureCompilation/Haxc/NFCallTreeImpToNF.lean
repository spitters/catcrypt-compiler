/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm3
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeWhileTrue

/-!
# The front `impToNF` at the level of call trees

The front `impToNF` translates an expression of the normal form of `HaxLean` to an `NFProg`
program over `nfDialect`; `ImpToNF.impToNF_sound` relates one run of the source to one run of
the target. This module relates the call trees: the source is the reading `denoteT` at the tree
table `evTable`, in which every call is an event of `linkSig`, and the target is the call tree
`treeAt linkReader` of the program, in which every leaf call is an event of `leafSig`.

A prefix of the target has the tree `preTreeAt`, and the tree of a filled prefix is the tree of
the prefix followed by the tree of the filling (`treeAt_plug`). Events are related by `ImpRE`
(the same name, the source arguments the encodings of the typed target arguments), answers by
`ImpRA` (the source answer the encoding of the target answer at the result type), a source
leaf that is a value by `LeafRel` (a target valuation related to the final environment whose
result variable encodes the value), and every other source leaf is failed (`SrcFail`). The
source event of a call `repeat` has no target event: its answer, at the source handler, is the
array the target builds (`RepeatCalls`), and the relation skips it (`RuttS`).

## Main definitions

* `evTable`: the tree table in which every call is one event.
* `preTreeAt`: the call tree of a prefix.
* `ImpRE`, `ImpRA`, `LeafRel`, `SrcFail`: the relations of events, answers and leaves.
* `RelT`: the relation of the source tree of an expression and the tree of its output.

## Main results

* `treeAt_plug`, `preTreeAt_append`: the trees of filled and composed prefixes.
* `litOut_relT`, `atomOut_relT`, `seq_relT`, `letBind_relT`, `assign_relT`, `impArgsNF_relT`,
  `app_relT`, `tuple_relT`, `proj_relT`: the constructs other than the conditional and the
  loops.

The conditional and the `while` loop are in `NFCallTreeImpToNFCond`, the counted loops and the
theorem `impToNF_relT` for every expression in `NFCallTreeImpToNFLoops`.
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

/-! ## The source table and the tree of a prefix -/

/-- The tree table in which every call is one event of `linkSig`, answered by the response. -/
def evTable : TreeTable linkSig := fun g vals =>
  .vis (⟨g, vals⟩ : LinkCall) fun r => CallTree.ret r

section Pre

variable {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- `obind` is associative. -/
theorem obind_assoc {α β γ : Type} (t : CallTree E (Option α))
    (f : α → CallTree E (Option β)) (g : β → CallTree E (Option γ)) :
    obind (obind t f) g = obind t (fun a => obind (f a) g) := by
  unfold obind
  rw [bind_assoc]
  congr 1
  funext o
  cases o <;> rfl

/-- **The call tree of a prefix**: clause by clause `treeAt`, ending at the hole with the
    valuation of the hole. -/
def preTreeAt (ex : ExprReader E d) (tE : TreeCallEnv E d) (fuel : Nat) :
    {Γ Δ : Ctxt d} → NFPre d Γ Δ → Valuation Γ → CallTree E (Option (Valuation Δ))
  | _, _, .nil, V => .ret (some V)
  | _, _, .var e p, V => obind (ex e V) fun x => preTreeAt ex tE fuel p (V.extend x)
  | _, _, .forLoop count inits body p, V =>
      obind (ofoldl (fun acc i => treeAt ex tE fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (List.range (HasWord64.toNat (d := d) (count.lookup V))) (Expr.lookupArgs inits V))
        fun acc => preTreeAt ex tE fuel p (hvAppend acc V)
  | _, _, .ifThenElse cond thn els p, V =>
      obind (if HasBoolBit.toBool (d := d) (cond.lookup V) then treeAt ex tE fuel thn V
          else treeAt ex tE fuel els V)
        fun r => preTreeAt ex tE fuel p (hvAppend r V)
  | _, _, .whileLoop inits body p, V =>
      obind (owhileIter (fun acc => treeAt ex tE fuel body (hvAppend acc V)) fuel
          (Expr.lookupArgs inits V))
        fun acc => preTreeAt ex tE fuel p (hvAppend acc V)

/-- **The tree of a filled prefix** is the tree of the prefix followed by the tree of the
    filling at the valuation of the hole. -/
theorem treeAt_plug (ex : ExprReader E d) (tE : TreeCallEnv E d) (fuel : Nat) {Γ Δ : Ctxt d}
    {ts : List d.Ty} (p : NFPre d Γ Δ) (k : NFProg d Δ ts) (V : Valuation Γ) :
    treeAt ex tE fuel (p.plug k) V =
      obind (preTreeAt ex tE fuel p V) fun W => treeAt ex tE fuel k W := by
  induction p with
  | nil => rfl
  | var e p ih => simp only [NFPre.plug, treeAt, preTreeAt, obind_assoc, ih]
  | forLoop count inits body p ih => simp only [NFPre.plug, treeAt, preTreeAt, obind_assoc, ih]
  | ifThenElse cond thn els p ih => simp only [NFPre.plug, treeAt, preTreeAt, obind_assoc, ih]
  | whileLoop inits body p ih => simp only [NFPre.plug, treeAt, preTreeAt, obind_assoc, ih]

/-- The tree of a composed prefix is the tree of the first followed by the tree of the
    second. -/
theorem preTreeAt_append (ex : ExprReader E d) (tE : TreeCallEnv E d) (fuel : Nat)
    {Γ Δ Θ : Ctxt d} (p : NFPre d Γ Δ) (q : NFPre d Δ Θ) (V : Valuation Γ) :
    preTreeAt ex tE fuel (p.append q) V =
      obind (preTreeAt ex tE fuel p V) fun W => preTreeAt ex tE fuel q W := by
  induction p with
  | nil => rfl
  | var e p ih => simp only [NFPre.append, preTreeAt, obind_assoc, ih]
  | forLoop count inits body p ih => simp only [NFPre.append, preTreeAt, obind_assoc, ih]
  | ifThenElse cond thn els p ih => simp only [NFPre.append, preTreeAt, obind_assoc, ih]
  | whileLoop inits body p ih => simp only [NFPre.append, preTreeAt, obind_assoc, ih]

end Pre

/-! ## The relations of the front -/

/-- **The event relation of the front**: a source call and a leaf call of the same name, whose
    source arguments are the encodings of the typed arguments of the leaf call. -/
def ImpRE (e₀ : linkSig.Event) (e₁ : leafSig.Event) : Prop :=
  e₁.name = LinkCall.name e₀ ∧ LinkCall.args e₀ = encAll e₁.argTys e₁.args

/-- **The answer relation of the front**: the source answer is the encoding of the answer of
    the leaf call at its result type. -/
def ImpRA (e₀ : linkSig.Event) (e₁ : leafSig.Event) (a₀ : linkSig.Resp e₀)
    (a₁ : leafSig.Resp e₁) : Prop :=
  (a₀ : Option Value) = a₁.map (enc e₁.ret)

/-- **The leaf relation of an output**: the source leaf is a value, and the target leaf a
    valuation of the hole related to the final environment whose result variable encodes the
    value. -/
def LeafRel {Γ : Ctxt nfDialect} (o : Out Γ) (r : Outcome × Env) (w : Option (Valuation o.Δ)) :
    Prop :=
  ∃ v W, r.1 = .val v ∧ w = some W ∧ EnvRel o.σ r.2 W ∧ v = enc o.t (o.res.lookup W)

/-- A failed source leaf: its outcome is not a value. -/
def SrcFail (r : Outcome × Env) : Prop := ∀ v, r.1 ≠ .val v

/-- **The relation of the trees of an expression and of an output**: from every environment
    related to a valuation by `EnvRel σ`, the source tree of `e` at the fuel `fuel` and the tree
    of the prefix of `o` at the target fuel `tf` are related by `RuttS` at the source handler
    `h₁`, the events related by `ImpRE`, the answers by `ImpRA`, the leaves by `LeafRel o`, a
    source leaf that is not a value failed. -/
def RelT (h₁ : ∀ e : linkSig.Event, linkSig.Resp e) (tE : TreeCallEnv leafSig nfDialect)
    (fuel tf : Nat) (e : ImpExpr) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (o : Out Γ) : Prop :=
  ∀ (env : Env) (V : Valuation Γ), EnvRel σ env V →
    RuttS h₁ ImpRE ImpRA (LeafRel o) SrcFail (denoteT evTable fuel e env)
      (preTreeAt linkReader tE tf o.pre V)

section Lemmas

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- **A value continuation**: a source tree related to the tree of the prefix of `o`, followed by
    a continuation related at every value leaf to the target continuation, and whose failed
    leaves are failed. -/
theorem ruttS_valK {Γ : Ctxt nfDialect} {o : Out Γ} {R₁ β : Type}
    {RR : R₁ → Option β → Prop} {Fail : R₁ → Prop}
    {t₁ : CallTree linkSig (Outcome × Env)} {t₂ : CallTree leafSig (Option (Valuation o.Δ))}
    {K₁ : Outcome × Env → CallTree linkSig R₁} {K₂ : Valuation o.Δ → CallTree leafSig (Option β)}
    (h : RuttS h₁ ImpRE ImpRA (LeafRel o) SrcFail t₁ t₂)
    (hk : ∀ e1 W, EnvRel o.σ e1 W →
      RuttS h₁ ImpRE ImpRA RR Fail (K₁ (.val (enc o.t (o.res.lookup W)), e1)) (K₂ W))
    (hf : ∀ r, SrcFail r → ∀ t, RuttS h₁ ImpRE ImpRA RR Fail (K₁ r) t) :
    RuttS h₁ ImpRE ImpRA RR Fail (t₁.bind K₁) (obind t₂ K₂) := by
  unfold obind
  refine RuttS.bind h ?_ hf
  rintro ⟨o1, e1⟩ s₂ ⟨v, W, h1, rfl, hrel, rfl⟩
  dsimp only at h1
  subst h1
  exact hk e1 W hrel

/-- A relation of trees carries a property of the leaves of the target tree. -/
theorem ruttS_tgtLeaf {E₁ E₂ : EventSig} {g₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {R₁ R₂ : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {Q : R₂ → Prop}
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : RuttS g₁ RE RA RR Fail t₁ t₂)
    (hQ : LeafP Q t₂) : RuttS g₁ RE RA (fun a b => RR a b ∧ Q b) Fail t₁ t₂ := by
  induction h with
  | ret h => cases hQ with | ret hq => exact .ret ⟨h, hq⟩
  | fail h => exact .fail h
  | vis he _ ih => cases hQ with | vis hQ => exact .vis he fun a₁ a₂ ha => ih a₁ a₂ ha (hQ a₂)
  | skip _ ih => exact .skip (ih hQ)

/-- The leaves of `obind` satisfy a property that holds of `none` and of the leaves of the
    continuation. -/
theorem LeafP.obind {E : EventSig} {α β : Type} {P : Option β → Prop}
    (t : CallTree E (Option α)) {k : α → CallTree E (Option β)} (hn : P none)
    (hk : ∀ a, LeafP P (k a)) : LeafP P (NFProgCallTree.obind t k) := by
  induction t with
  | ret o =>
    cases o with
    | none => exact .ret hn
    | some a => exact hk a
  | vis e c ih => exact .vis fun a => ih a

end Lemmas

/-- A weakened variable reads at every leaf of the tree of a prefix what it reads at the
    start. -/
theorem preTreeAt_wk {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] (ex : ExprReader E d) (tE : TreeCallEnv E d) (fuel : Nat)
    {Γ Δ : Ctxt d} (p : NFPre d Γ Δ) (V : Valuation Γ) :
    LeafP (fun w => ∀ W, w = some W → ∀ t (v : Var Γ t), (p.wk v).lookup W = v.lookup V)
      (preTreeAt ex tE fuel p V) := by
  induction p with
  | nil => exact .ret fun W hW t v => by cases hW; rfl
  | var e p ih =>
    exact LeafP.obind _ (fun W hW => by cases hW) fun x =>
      (ih (V.extend x)).mono fun w hw W hW t v => (hw W hW t (Var.there v)).trans rfl
  | forLoop count inits body p ih =>
    exact LeafP.obind _ (fun W hW => by cases hW) fun acc =>
      (ih (hvAppend acc V)).mono fun w hw W hW t v =>
        (hw W hW t _).trans (Var.lookup_shiftApp _ acc v _)
  | ifThenElse cond thn els p ih =>
    exact LeafP.obind _ (fun W hW => by cases hW) fun r =>
      (ih (hvAppend r V)).mono fun w hw W hW t v =>
        (hw W hW t _).trans (Var.lookup_shiftApp _ r v _)
  | whileLoop inits body p ih =>
    exact LeafP.obind _ (fun W hW => by cases hW) fun acc =>
      (ih (hvAppend acc V)).mono fun w hw W hW t v =>
        (hw W hW t _).trans (Var.lookup_shiftApp _ acc v _)

/-- The tree of one binding of an operation without event is the leaf of its value. -/
theorem preTreeAt_bind1N (tE : TreeCallEnv leafSig nfDialect) (tf : Nat) (tgt : Option String)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
    (V : Valuation Γ) (hop : ∀ a, opTree op a = .ret (nfDenoteOp NfLeafTable.empty op a)) :
    preTreeAt linkReader tE tf (bind1N tgt σ op args).pre V =
      .ret ((nfDenoteOp NfLeafTable.empty op (Expr.lookupArgs args V)).map V.extend) := by
  cases tgt <;>
  · show obind (opTree op (Expr.lookupArgs args V)) (fun x => CallTree.ret (some (V.extend x)))
      = _
    rw [hop]
    cases nfDenoteOp NfLeafTable.empty op (Expr.lookupArgs args V) <;> rfl


/-! ## Readings of the source in sequenced form -/

section Forms

variable {E : EventSig} (bt : TreeTable E) (fuel : Nat)

/-- The reading of a sequence, with the control-flow test of the first value. -/
theorem denoteT_seq_runIf (a b : ImpExpr) (env : Env) :
    denoteT bt fuel (.seq a b) env = (denoteT bt fuel a env).bind fun p =>
      match p with
      | (.val w, e1) => if w.isControlFlow then .ret (.val w, e1) else denoteT bt fuel b e1
      | (o, e1) => .ret (o, e1) := by
  rw [NFCallTreeAnfPick.denoteT_seq_run]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

/-- The reading of an assignment, with the control-flow test of the assigned value. -/
theorem denoteT_assign_runIf (x : String) (r : ImpExpr) (env : Env) :
    denoteT bt fuel (.assign x r) env = (denoteT bt fuel r env).bind fun p =>
      match p with
      | (.val w, e1) => if w.isControlFlow then .ret (.val w, e1)
          else .ret (.val .unit, e1.extend x w)
      | (o, e1) => .ret (o, e1) := by
  rw [denoteT, NFCallTreeRepeatCount.tm_bind_run]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

end Forms

/-! ## The straight-line constructs -/

section Straight

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- One binding of an operation without event, whose value encodes the source value of a
    source leaf at the same environment, relates the trees. -/
theorem relT_bind1N (fuel tf : Nat) (e : ImpExpr) (tgt : Option String) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
    (hop : ∀ a, opTree op a = .ret (nfDenoteOp NfLeafTable.empty op a))
    (h : ∀ env V, EnvRel σ env V → ∃ x,
      nfDenoteOp NfLeafTable.empty op (Expr.lookupArgs args V) = some x ∧
      denoteT evTable fuel e env = .ret (.val (enc op.ret x), env)) :
    RelT h₁ tE fuel tf e σ (bind1N tgt σ op args) := by
  intro env V hrel
  obtain ⟨x, hx, he⟩ := h env V hrel
  rw [he, preTreeAt_bind1N tE tf tgt σ op args V hop, hx]
  exact .ret ⟨_, V.extend x, rfl, rfl, hrel.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩

/-- A literal relates the trees. -/
theorem litOut_relT (fuel tf : Nat) (tgt : Option String) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (l : ImpLit) {o : Out Γ} (h : litOut tgt σ l = some o) :
    RelT h₁ tE fuel tf (.lit l) σ o := by
  have hs : ∀ env, denoteT evTable fuel (.lit l) env = .ret (.val (Value.ofLit l), env) :=
    fun env => NFCallTreeRepeatCount.denoteT_lit_run evTable fuel l env
  cases l with
  | bool b =>
    simp only [litOut, Option.some.injEq] at h
    subst h
    exact relT_bind1N fuel tf _ tgt σ _ _ (fun _ => rfl) fun env V _ => ⟨b, rfl, hs env⟩
  | unit =>
    simp only [litOut, Option.some.injEq] at h
    subst h
    exact relT_bind1N fuel tf _ tgt σ _ _ (fun _ => rfl) fun env V _ => ⟨(), rfl, hs env⟩
  | int n | uintLit W n | sintLit W n =>
    simp only [litOut, Option.bind_eq_some_iff] at h
    obtain ⟨⟨t, v⟩, hl, hs'⟩ := h
    split at hs'
    · rename_i hsome
      simp only [Option.some.injEq] at hs'
      subst hs'
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
      exact relT_bind1N fuel tf _ tgt σ _ _ (fun _ => rfl) fun env V _ =>
        ⟨x, hx, (hs env).trans (by rw [ofLit_enc hl hx])⟩
    · cases hs'

/-- An atom relates the trees. -/
theorem atomOut_relT (fuel tf : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (a : ImpExpr)
    {o : Out Γ} (h : atomOut σ a = some o) : RelT h₁ tE fuel tf a σ o := by
  cases a with
  | var x =>
    simp only [atomOut, Option.map_eq_some_iff] at h
    obtain ⟨⟨t, r⟩, hx, rfl⟩ := h
    intro env V hrel
    rw [NFCallTreeRepeatCount.denoteT_var_run evTable fuel x env _ (hrel x t r hx)]
    exact .ret ⟨_, V, rfl, rfl, hrel, rfl⟩
  | lit l => exact litOut_relT fuel tf none σ l h
  | _ => simp [atomOut] at h

/-- The unit value relates the trees. -/
theorem unitVal_relT (fuel tf : Nat) (tgt : Option String) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) : RelT h₁ tE fuel tf .unitVal σ (bind1N tgt σ .constUnit .nil) :=
  relT_bind1N fuel tf _ tgt σ _ _ (fun _ => rfl) fun env V _ =>
    ⟨(), rfl, by rw [denoteT]; rfl⟩

/-- A failed source leaf followed by a continuation that keeps it is related to every
    tree. -/
theorem ruttS_keep {R₂ : Type} {RR : Outcome × Env → R₂ → Prop}
    (K : Outcome × Env → CallTree linkSig (Outcome × Env))
    (hK : ∀ o e1, (∀ v, o ≠ .val v) → K (o, e1) = .ret (o, e1)) :
    ∀ r, SrcFail r → ∀ t, RuttS h₁ ImpRE ImpRA RR SrcFail (K r) t := by
  rintro ⟨o, e1⟩ hf t
  rw [hK o e1 hf]
  exact .fail hf

/-- A sequence of related outputs relates the trees. -/
theorem seq_relT (fuel tf : Nat) {a b : ImpExpr} {Γ : Ctxt nfDialect} {σ : NfEnv Γ}
    {oa : Out Γ} (ha : RelT h₁ tE fuel tf a σ oa) {ob : Out oa.Δ}
    (hb : RelT h₁ tE fuel tf b oa.σ ob) : RelT h₁ tE fuel tf (.seq a b) σ (oa.comp ob) := by
  intro env V hrel
  rw [denoteT_seq_runIf]
  show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf (oa.pre.append ob.pre) V)
  rw [preTreeAt_append]
  refine ruttS_valK (ha env V hrel) (fun e1 W hrel1 => ?_) (ruttS_keep _ ?_)
  · simp only [enc_isControlFlow, Bool.false_eq_true, ite_false]
    exact hb e1 W hrel1
  · intro o e1 ho
    cases o with
    | val v => exact absurd rfl (ho v)
    | _ => rfl

/-- A binding of a related output, followed by an output related from the environment of
    names with the bound name, relates the trees. -/
theorem letBind_relT (fuel tf : Nat) (x : String) {v b : ImpExpr} {Γ : Ctxt nfDialect}
    {σ : NfEnv Γ} {ov : Out Γ} (hv : RelT h₁ tE fuel tf v σ ov) {ob : Out ov.Δ}
    (hb : RelT h₁ tE fuel tf b ((x, ⟨ov.t, ov.res⟩) :: ov.σ) ob) :
    RelT h₁ tE fuel tf (.letBind x v b) σ (ov.comp ob) := by
  intro env V hrel
  rw [NFCallTreeANorm.denoteT_letBind_runIf]
  show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf (ov.pre.append ob.pre) V)
  rw [preTreeAt_append]
  refine ruttS_valK (hv env V hrel) (fun e1 W hrel1 => ?_) (ruttS_keep _ ?_)
  · simp only [enc_isControlFlow, Bool.false_eq_true, ite_false]
    exact hb _ W (hrel1.cons x ov.t ov.res)
  · intro o e1 ho
    cases o with
    | val v => exact absurd rfl (ho v)
    | _ => rfl

/-- An assignment of a related output relates the trees. -/
theorem assign_relT (fuel tf : Nat) (x : String) (tgt : Option String) {r : ImpExpr}
    {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {o : Out Γ} (hr : RelT h₁ tE fuel tf r σ o) :
    RelT h₁ tE fuel tf (.assign x r) σ
      (o.comp (bind1N tgt ((x, ⟨o.t, o.res⟩) :: o.σ) .constUnit .nil)) := by
  intro env V hrel
  rw [denoteT_assign_runIf]
  show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf
    (o.pre.append (bind1N tgt ((x, ⟨o.t, o.res⟩) :: o.σ) .constUnit .nil).pre) V)
  rw [preTreeAt_append]
  refine ruttS_valK (hr env V hrel) (fun e1 W hrel1 => ?_) (ruttS_keep _ ?_)
  · simp only [enc_isControlFlow, Bool.false_eq_true, ite_false]
    rw [preTreeAt_bind1N tE tf tgt _ .constUnit .nil W fun _ => rfl]
    exact .ret ⟨_, W.extend (), rfl, rfl,
      (hrel1.cons x o.t o.res).mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩
  · intro o e1 ho
    cases o with
    | val v => exact absurd rfl (ho v)
    | _ => rfl

end Straight

/-! ## Lists of arguments, calls, tuples and projections -/

/-- A weakened variable reads at the valuation of a prefix whose tree is one leaf what it reads
    at the start. -/
theorem preTreeAt_wk_of_ret {E : EventSig} {d : Dialect.{0, 0}} [DialectSignature d]
    [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] {ex : ExprReader E d} {tE : TreeCallEnv E d}
    {fuel : Nat} {Γ Δ : Ctxt d} {p : NFPre d Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (h : preTreeAt ex tE fuel p V = .ret (some W)) :
    ∀ t (v : Var Γ t), (p.wk v).lookup W = v.lookup V := by
  have hl := preTreeAt_wk ex tE fuel p V
  rw [h] at hl
  cases hl with
  | ret hq => exact hq W rfl

/-- The leaf relation of a list of arguments: a list of values encoding the variables of the
    output, at a valuation of the hole related to the final environment. -/
def ArgsRel {Γ : Ctxt nfDialect} (oa : ArgsOut Γ) (r : Option (List Value) × Env)
    (w : Option (Valuation oa.Δ)) : Prop :=
  ∃ W, w = some W ∧ r.1 = some (encAll oa.as (Expr.lookupArgs oa.vs W)) ∧ EnvRel oa.σ r.2 W

section Args

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- **A list of arguments relates the trees**, for a translation `A` of lists built from a
    translation `F` of its elements as `impArgsNF` and `argsOut` are, when `F` relates the trees
    of each element. -/
theorem args_relT (fuel tf : Nat)
    (F : ∀ {Γ : Ctxt nfDialect}, NfEnv Γ → ImpExpr → Option (Out Γ))
    (A : ∀ {Γ : Ctxt nfDialect}, NfEnv Γ → List ImpExpr → Option (ArgsOut Γ))
    (hnil : ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ), A σ [] = some ⟨Γ, [], .nil, σ, .nil⟩)
    (hcons : ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (e : ImpExpr) (es : List ImpExpr),
      A σ (e :: es) = (F σ e).bind fun o => (A o.σ es).map fun os =>
        ⟨os.Δ, o.t :: os.as, o.pre.append os.pre, os.σ, .cons (os.pre.wk o.res) os.vs⟩)
    (es : List ImpExpr)
    (H : ∀ e ∈ es, ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}, F σ e = some o →
      RelT h₁ tE fuel tf e σ o) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {oa : ArgsOut Γ}, A σ es = some oa →
    ∀ (env : Env) (V : Valuation Γ), EnvRel σ env V →
      RuttS h₁ ImpRE ImpRA (ArgsRel oa) (fun r => r.1 = none)
        (denoteArgsT evTable fuel es env) (preTreeAt linkReader tE tf oa.pre V) := by
  induction es with
  | nil =>
    intro Γ σ oa h env V hrel
    rw [hnil, Option.some.injEq] at h
    subst h
    rw [NFCallTreeANorm.denoteArgsT_nil_run]
    exact .ret ⟨V, rfl, rfl, hrel⟩
  | cons e es ih =>
    intro Γ σ oa h env V hrel
    rw [hcons] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨o, ho, os, hos, rfl⟩ := h
    rw [NFCallTreeANorm.denoteArgsT_cons_run]
    show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf (o.pre.append os.pre) V)
    rw [preTreeAt_append]
    refine ruttS_valK (H e List.mem_cons_self σ ho env V hrel) (fun e1 W1 hrel1 => ?_) ?_
    · simp only [enc_isControlFlow, Bool.false_eq_true, ite_false]
      rw [← bind_ret (preTreeAt linkReader tE tf os.pre W1)]
      refine RuttS.bind (ruttS_tgtLeaf (ih (fun e' he' => H e' (List.mem_cons_of_mem _ he')) o.σ
        hos e1 W1 hrel1) (preTreeAt_wk linkReader tE tf os.pre W1)) ?_ ?_
      · rintro ⟨m, e2⟩ s₂ ⟨⟨W2, rfl, hm, hrel2⟩, hwk⟩
        dsimp only at hm hrel2
        subst hm
        refine .ret ⟨W2, rfl, ?_, hrel2⟩
        show some (enc o.t (o.res.lookup W1) :: _) = some (enc o.t ((os.pre.wk o.res).lookup W2)
          :: _)
        rw [hwk W2 rfl]
      · rintro ⟨m, e2⟩ hm t
        dsimp only at hm
        subst hm
        exact .fail rfl
    · rintro ⟨o', e1⟩ hf t
      cases o' with
      | val v => exact absurd rfl (hf v)
      | _ => exact .fail rfl

/-- `impArgsNF` relates the trees of its arguments when the front relates the tree of each. -/
theorem impArgsNF_relT (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat)
    (es : List ImpExpr)
    (H : ∀ e ∈ es, ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ},
      impToNF sigOf none σ e = some o → RelT h₁ tE fuel tf e σ o) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {oa : ArgsOut Γ}, impArgsNF sigOf σ es = some oa →
    ∀ (env : Env) (V : Valuation Γ), EnvRel σ env V →
      RuttS h₁ ImpRE ImpRA (ArgsRel oa) (fun r => r.1 = none)
        (denoteArgsT evTable fuel es env) (preTreeAt linkReader tE tf oa.pre V) :=
  args_relT fuel tf (impToNF sigOf none) (impArgsNF sigOf) (fun σ => by rw [impArgsNF])
    (fun σ e es => by rw [impArgsNF]) es H

/-- `argsOut` relates the trees of its atoms. -/
theorem argsOut_relT (fuel tf : Nat) (es : List ImpExpr) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {oa : ArgsOut Γ}, argsOut σ es = some oa →
    ∀ (env : Env) (V : Valuation Γ), EnvRel σ env V →
      RuttS h₁ ImpRE ImpRA (ArgsRel oa) (fun r => r.1 = none)
        (denoteArgsT evTable fuel es env) (preTreeAt linkReader tE tf oa.pre V) :=
  args_relT fuel tf atomOut argsOut (fun σ => by rw [argsOut]) (fun σ e es => by rw [argsOut]) es
    fun e _ _ σ _ h => atomOut_relT fuel tf σ e h

/-- The source reading of a call at `evTable`, after its arguments: one event, answered by the
    value of the call. -/
theorem appKT_evTable (f : String) (vals : List Value) (e1 : Env) :
    NFCallTreeANorm.appKT evTable f (some vals) e1 =
      .vis (⟨f, vals⟩ : LinkCall) fun a => .ret ((match a with
        | some v => .val v
        | none => .err s!"unknown function or bad args: {f}"), e1) := by
  simp only [NFCallTreeANorm.appKT]
  rw [NFCallTreeWhileTrue.lift_bind_run]
  simp only [evTable, CallTree.bind]
  congr 1
  funext a
  cases a <;> rfl

/-- **A call of a leaf relates the trees**: the source event of the call is related to the leaf
    call of the target, when the front relates the trees of the arguments. -/
theorem appCall_relT (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat)
    (tgt : Option String) (f : String) (args : List ImpExpr) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ)
    (HA : ∀ e ∈ args, ∀ {Γ' : Ctxt nfDialect} (σ' : NfEnv Γ') {o' : Out Γ'},
      impToNF sigOf none σ' e = some o' → RelT h₁ tE fuel tf e σ' o')
    {oa : ArgsOut Γ} (hoa : impArgsNF sigOf σ args = some oa) (r : NfTy) :
    RelT h₁ tE fuel tf (.app f args) σ
      ⟨r :: oa.Δ, r, oa.pre.append (.var (mkEN tgt (.call f oa.as r) oa.vs) .nil),
        oa.σ.mapV .there, .here⟩ := by
  intro env V hrel
  rw [NFCallTreeANorm.denoteT_app_run]
  show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf
    (oa.pre.append (.var (mkEN tgt (.call f oa.as r) oa.vs) .nil)) V)
  rw [preTreeAt_append]
  unfold obind
  refine RuttS.bind (impArgsNF_relT sigOf fuel tf args HA σ hoa env V hrel) ?_ ?_
  · rintro ⟨m, e1⟩ s₂ ⟨W, rfl, hm, hrel1⟩
    dsimp only at hm hrel1
    subst hm
    dsimp only
    rw [appKT_evTable]
    have ht : preTreeAt linkReader tE tf
        (.var (mkEN tgt (.call f oa.as r) oa.vs) .nil) W =
        .vis (⟨f, oa.as, r, Expr.lookupArgs oa.vs W⟩ : LeafCall)
          fun y => obind (.ret y) fun x => .ret (some (W.extend x)) := by
      cases tgt <;> rfl
    rw [ht]
    refine .vis ⟨rfl, rfl⟩ fun a₀ a₁ ha => ?_
    change (a₀ : Option Value) = a₁.map (enc r) at ha
    subst ha
    cases a₁ with
    | none => exact .fail fun v h => by cases h
    | some y =>
      exact .ret ⟨_, W.extend y, rfl, rfl,
        hrel1.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩
  · rintro ⟨m, e1⟩ hm t
    dsimp only at hm
    subst hm
    exact .fail fun v h => by cases h

/-- The reading of a tuple at `evTable`, after its elements. -/
theorem tupleKT_some (vals : List Value) (e1 : Env) :
    NFCallTreeANorm.tupleKT (E := linkSig) (some vals) e1 = .ret (.val (.tuple vals), e1) := rfl

/-- The bindings of `tupleOut` have a tree with one leaf, at a valuation in which the tuple
    variable encodes the tuple of the encodings of the components. -/
theorem tupleOut_tree (tf : Nat) :
    ∀ {Γ : Ctxt nfDialect} (tgt : Option String) (as : List NfTy)
      (vs : HVector (fun t => Var Γ t) as) (V : Valuation Γ),
      ∃ W, preTreeAt linkReader tE tf (tupleOut tgt as vs).2.1 V = .ret (some W) ∧
        enc (tupTy as) ((tupleOut tgt as vs).2.2.lookup W) =
          .tuple (encAll as (Expr.lookupArgs vs V))
  | _, tgt, [], .nil, V => by cases tgt <;> exact ⟨V.extend (), rfl, rfl⟩
  | _, tgt, a :: as, .cons v vs, V => by
      have ih := tupleOut_tree tf none as vs V
      show ∃ W, preTreeAt linkReader tE tf ((tupleOut none as vs).2.1.append
          (.var (mkEN tgt (.tconsV a (tupTy as))
            (.cons ((tupleOut none as vs).2.1.wk v) (.cons (tupleOut none as vs).2.2 .nil)))
              .nil)) V = .ret (some W) ∧
          enc (NfTy.tcons a (tupTy as))
            ((Var.here : Var (NfTy.tcons a (tupTy as) :: (tupleOut none as vs).1) _).lookup W) =
          .tuple (encAll (a :: as) (Expr.lookupArgs (.cons v vs) V))
      generalize tupleOut none as vs = T at ih ⊢
      obtain ⟨Δ, p, rv⟩ := T
      obtain ⟨W1, hW1, henc⟩ := ih
      refine ⟨W1.extend (t := NfTy.tcons a (tupTy as)) (v.lookup V, rv.lookup W1), ?_, ?_⟩
      · rw [preTreeAt_append, hW1]
        have hwk := preTreeAt_wk_of_ret hW1 _ v
        cases tgt <;>
        · show CallTree.ret (some (W1.extend (t := NfTy.tcons a (tupTy as))
            ((p.wk v).lookup W1, rv.lookup W1))) = _
          rw [hwk]
      · show Value.tuple (enc a (v.lookup V) :: tailVals (enc (tupTy as) (rv.lookup W1))) = _
        rw [henc]
        rfl

/-- A tuple of atoms relates the trees. -/
theorem tuple_relT (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat)
    (tgt : Option String) (es : List ImpExpr) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.tuple es) = some o) : RelT h₁ tE fuel tf (.tuple es) σ o := by
  simp only [impToNF, Option.map_eq_some_iff] at h
  obtain ⟨oa, hoa, rfl⟩ := h
  intro env V hrel
  rw [NFCallTreeANorm.denoteT_tuple_run]
  show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf
    (oa.pre.append (tupleOut tgt oa.as oa.vs).2.1) V)
  rw [preTreeAt_append]
  unfold obind
  refine RuttS.bind (argsOut_relT fuel tf es σ hoa env V hrel) ?_ ?_
  · rintro ⟨m, e1⟩ s₂ ⟨W, rfl, hm, hrel1⟩
    dsimp only at hm hrel1
    subst hm
    rw [tupleKT_some]
    obtain ⟨W2, hW2, henc⟩ := tupleOut_tree (tE := tE) tf tgt oa.as oa.vs W
    show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf (tupleOut tgt oa.as oa.vs).2.1 W)
    rw [hW2]
    exact .ret ⟨_, W2, rfl, rfl, hrel1.mapV _ (preTreeAt_wk_of_ret hW2), henc.symm⟩
  · rintro ⟨m, e1⟩ hm t
    dsimp only at hm
    subst hm
    exact .fail fun v h => by cases h

end Args

/-! ## Projections -/

/-- The reading of a projection, with the control-flow test of the value. -/
theorem denoteT_proj_runIf {E : EventSig} (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) (i : Nat)
    (env : Env) :
    denoteT bt fuel (.proj e i) env = (denoteT bt fuel e env).bind fun p =>
      match p with
      | (.val w, e1) => if w.isControlFlow then .ret (.val w, e1) else
          match w.projIdx i with
          | some vi => .ret (.val vi, e1)
          | none => .ret (.err s!"projection index {i} out of range", e1)
      | (o, e1) => .ret (o, e1) := by
  rw [denoteT, NFCallTreeRepeatCount.tm_bind_run]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> first | rfl |
      (simp only [Value.isControlFlow, Bool.false_eq_true, ite_false]
       cases Value.projIdx _ i <;> rfl)
  all_goals rfl

/-- The tree of one binding of `bind1` is the tree of `bind1N` without a source name. -/
theorem preTreeAt_bind1 (tE : TreeCallEnv leafSig nfDialect) (tf : Nat) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (V : Valuation Γ)
    (hop : ∀ a, opTree op a = .ret (nfDenoteOp NfLeafTable.empty op a)) :
    preTreeAt linkReader tE tf (bind1 σ op args).pre V =
      .ret ((nfDenoteOp NfLeafTable.empty op (Expr.lookupArgs args V)).map V.extend) :=
  preTreeAt_bind1N tE tf none σ op args V hop

/-- The bindings of `projOut` have a tree with one leaf, at a valuation related to the same
    environment whose result variable encodes the component `i` of the value of `x`. -/
theorem projOut_tree (tE : TreeCallEnv leafSig nfDialect) (tf : Nat) (tgt : Option String)
    (i : Nat) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (t : NfTy) (x : Var Γ t) {o : Out Γ},
      projOut tgt σ t x i = some o → ∀ (env : Env) (V : Valuation Γ), EnvRel σ env V →
      ∃ W, preTreeAt linkReader tE tf o.pre V = .ret (some W) ∧ EnvRel o.σ env W ∧
        (enc t (x.lookup V)).projIdx i = some (enc o.t (o.res.lookup W)) := by
  induction i with
  | zero =>
    intro Γ σ t x o h env V hrel
    cases t with
    | tcons h₀ t =>
      simp only [projOut, Option.some.injEq] at h
      subst h
      refine ⟨V.extend (x.lookup V).1, ?_,
        hrel.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩
      rw [preTreeAt_bind1N tE tf tgt σ _ _ V fun _ => rfl]
      rfl
    | _ => simp [projOut] at h
  | succ i ih =>
    intro Γ σ t x o h env V hrel
    cases t with
    | tcons h₀ t =>
      simp only [projOut, Option.map_eq_some_iff] at h
      obtain ⟨o₂, ho₂, rfl⟩ := h
      obtain ⟨h₁, t₁, rfl⟩ := projOut_tcons ho₂
      have hrel1 : EnvRel (bind1 σ (.ttail h₀ (.tcons h₁ t₁)) (.cons x .nil)).σ env
          (V.extend (x.lookup V).2) :=
        hrel.mapV (fun v => Var.there v) fun _ _ => rfl
      obtain ⟨W, hW, hrel2, hp⟩ := ih _ (.tcons h₁ t₁) _ ho₂ env _ hrel1
      refine ⟨W, ?_, hrel2, hp⟩
      show preTreeAt linkReader tE tf
        ((bind1 σ (.ttail h₀ (.tcons h₁ t₁)) (.cons x .nil)).pre.append o₂.pre) V = _
      rw [preTreeAt_append, preTreeAt_bind1 tE tf σ _ _ V fun _ => rfl]
      exact hW
    | _ => simp [projOut] at h

/-- A projection of a related output relates the trees. -/
theorem proj_relT {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}
    (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat) (tgt : Option String)
    (e : ImpExpr) (i : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.proj e i) = some o)
    (he : ∀ {oe : Out Γ}, impToNF sigOf none σ e = some oe → RelT h₁ tE fuel tf e σ oe) :
    RelT h₁ tE fuel tf (.proj e i) σ o := by
  simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨oe, hoe, op, hop, rfl⟩ := h
  intro env V hrel
  rw [denoteT_proj_runIf]
  show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf (oe.pre.append op.pre) V)
  rw [preTreeAt_append]
  refine ruttS_valK (he hoe env V hrel) (fun e1 W1 hrel1 => ?_) (ruttS_keep _ ?_)
  · simp only [enc_isControlFlow, Bool.false_eq_true, ite_false]
    obtain ⟨W2, hW2, hrel2, hp⟩ := projOut_tree tE tf tgt i oe.σ oe.t oe.res hop e1 W1 hrel1
    rw [hW2, hp]
    exact .ret ⟨_, W2, rfl, rfl, hrel2, rfl⟩
  · intro o e1 ho
    cases o with
    | val v => exact absurd rfl (ho v)
    | _ => rfl

/-! ## The call `repeat` and the calls -/

section Calls

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- **A call `repeat [x, N]` with a literal count `N ≥ 0` relates the trees**, when the source
    handler answers `repeat` as `RepeatCalls` states: the source event is skipped at the answer
    of the source handler, and the target builds the array without event. -/
theorem repeat_relT (hR : RepeatCalls fun f vals => h₁ ⟨f, vals⟩) (fuel tf : Nat)
    (tgt : Option String) (x : ImpExpr) {N : Int} (hN : 0 ≤ N) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) {o : Out Γ} (h : repeatOut tgt σ x N = some o) :
    RelT h₁ tE fuel tf (.app "repeat" [x, .lit (.int N)]) σ o := by
  simp only [repeatOut, Option.bind_eq_some_iff] at h
  obtain ⟨⟨Δ, t, pre, σ₁, res⟩, hox, h⟩ := h
  split at h
  · rename_i ht
    dsimp only at ht
    subst ht
    cases h
    intro env V hrel
    rw [NFCallTreeANorm.denoteT_app_run, NFCallTreeANorm.denoteArgsT_cons_run, bind_assoc]
    show RuttS _ _ _ _ _ _ (preTreeAt linkReader tE tf
      (pre.append (bind1N tgt σ₁ (.arrRepeat N.toNat (.word 64)) (.cons res .nil)).pre) V)
    rw [preTreeAt_append]
    refine ruttS_valK (o := ⟨Δ, .word 64, pre, σ₁, res⟩) (atomOut_relT fuel tf σ x hox env V hrel)
      (fun e1 W1 hrel1 => ?_) ?_
    · simp only [enc_isControlFlow, Bool.false_eq_true, ite_false]
      rw [NFCallTreeANorm.denoteArgsT_cons_run, NFCallTreeRepeatCount.denoteT_lit_run]
      simp only [CallTree.bind, Value.ofLit, Value.isControlFlow, Bool.false_eq_true, ite_false,
        NFCallTreeANorm.denoteArgsT_nil_run, Option.map_some]
      rw [appKT_evTable, preTreeAt_bind1N tE tf tgt σ₁ _ _ W1 fun _ => rfl]
      refine .skip ?_
      cases hb : h₁ ⟨"repeat", [enc (.word 64) (res.lookup W1), .int N]⟩ with
      | none => exact .fail fun v h => by cases h
      | some w =>
        have hw := hR _ N w hN hb
        subst hw
        refine .ret ⟨_, _, rfl, rfl, hrel1.mapV (fun v => Var.there v) fun _ _ => rfl, ?_⟩
        exact (enc_arr_const N.toNat (res.lookup W1)).symm
    · rintro ⟨o', e1⟩ hf t
      cases o' with
      | val v => exact absurd rfl (hf v)
      | _ => exact .fail fun v h => by cases h
  · cases h

/-- **A call relates the trees**, when the front relates the trees of its arguments and the
    source handler answers `repeat` as `RepeatCalls` states. -/
theorem app_relT (hR : RepeatCalls fun f vals => h₁ ⟨f, vals⟩)
    (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat) (tgt : Option String)
    (f : String) (args : List ImpExpr) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (HA : ∀ e ∈ args, ∀ {Γ' : Ctxt nfDialect} (σ' : NfEnv Γ') {o' : Out Γ'},
      impToNF sigOf none σ' e = some o' → RelT h₁ tE fuel tf e σ' o')
    (h : impToNF sigOf tgt σ (.app f args) = some o) : RelT h₁ tE fuel tf (.app f args) σ o := by
  rcases impToNF_app_cases sigOf tgt σ h with ⟨x, N, hr, hro⟩ | ⟨-, oa, hoa, r, -, rfl⟩
  · obtain ⟨rfl, rfl, hN, -⟩ := repeatArgs?_eq_some hr
    exact repeat_relT hR fuel tf tgt x hN σ hro
  · exact appCall_relT sigOf fuel tf tgt f args σ HA hoa r

end Calls

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF
