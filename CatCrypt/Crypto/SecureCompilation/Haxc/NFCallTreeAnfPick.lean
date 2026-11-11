/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeFlat
public import CatCrypt.Crypto.Hax.HaxFrontPrep

/-!
# The choice among the normal form and its rewritings at the level of call trees

The front chooses the body among the normal form `a`, its rewriting `ere a` with the
function-level returns moved into branches, and `tailSome (ere a)` (`anfEPick`). At the level of
call trees the reading `denoteT` of each candidate is related to the reading of `a` from the same
environment by `RuttS` at equal events and answers: a leaf of `a` that is not a value is a failed
leaf, and a value leaf is matched by a leaf with the same outcome or, where `a` returned
`controlFlow true v` at function level, the value `v` (`RetRel`). `ere` keeps the final
environment as well (`ERelT`); `tailSome` keeps the outcome and drops the bindings of the returned
names.

## Main results

* `ere_relT`: the call trees of a body and of its rewriting `ere` are related by `ERelT`.
* `tailSome_relT`: the call trees of `tailSome e` and `e` have equal events and outcomes.
* `anfEPick_relT`: the call tree of the chosen body is related to that of `a` at `RetRel` of the
  outcomes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick

open _root_.Hax
open _root_.Hax.EarlyReturnElim (RetRel hasRet ereSeq ere)
open CatCrypt.Crypto.Hax (tailSome isSomeRet isSomeRet_eq anfEPick)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run tm_pure_run
  denoteT_letBind_run)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)

variable {E : EventSig}

/-! ## Sequencing of trees -/

/-- Sequencing of trees is associative. -/
theorem bind_assoc {α β γ : Type} (t : CallTree E α) (f : α → CallTree E β)
    (g : β → CallTree E γ) : (t.bind f).bind g = t.bind (fun a => (f a).bind g) := by
  induction t with
  | ret a => rfl
  | vis e c ih =>
    show CallTree.vis e _ = CallTree.vis e _
    exact congrArg _ (funext ih)

/-- Sequencing with the leaf is the identity. -/
theorem bind_ret {α : Type} (t : CallTree E α) : t.bind CallTree.ret = t := by
  induction t with
  | ret a => rfl
  | vis e c ih =>
    show CallTree.vis e _ = CallTree.vis e _
    exact congrArg _ (funext ih)

/-! ## The readings of the statements as sequences -/

/-- The reading of a sequence. -/
theorem denoteT_seq_run (bt : TreeTable E) (fuel : Nat) (a b : ImpExpr) (env : Env) :
    denoteT bt fuel (.seq a b) env = (denoteT bt fuel a env).bind fun p =>
      match p with
      | (.val (.controlFlow k v), e1) => .ret (.val (.controlFlow k v), e1)
      | (.val _, e1) => denoteT bt fuel b e1
      | (o, e1) => .ret (o, e1) := by
  rw [denoteT, tm_bind_run]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

/-- The reading of a conditional. -/
theorem denoteT_ifThenElse_run (bt : TreeTable E) (fuel : Nat) (c t e : ImpExpr) (env : Env) :
    denoteT bt fuel (.ifThenElse c t e) env = (denoteT bt fuel c env).bind fun p =>
      match p with
      | (.val (.controlFlow k v), e1) => .ret (.val (.controlFlow k v), e1)
      | (.val (.bool true), e1) => denoteT bt fuel t e1
      | (.val (.bool false), e1) => denoteT bt fuel e e1
      | (.val _, e1) => .ret (.err "if condition not a bool", e1)
      | (o, e1) => .ret (o, e1) := by
  rw [denoteT, tm_bind_run]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v with
    | bool bb => cases bb <;> rfl
    | _ => rfl
  all_goals rfl

/-- The reading of a binding. -/
theorem denoteT_letBind_run' (bt : TreeTable E) (fuel : Nat) (n : String) (v b : ImpExpr)
    (env : Env) :
    denoteT bt fuel (.letBind n v b) env = (denoteT bt fuel v env).bind fun p =>
      match p with
      | (.val (.controlFlow k w), e1) => .ret (.val (.controlFlow k w), e1)
      | (.val w, e1) => denoteT bt fuel b (e1.extend n w)
      | (o, e1) => .ret (o, e1) := by
  rw [denoteT_letBind_run]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

/-- The reading of a function-level return. -/
theorem denoteT_cfBreak_run (bt : TreeTable E) (fuel : Nat) (p : ImpExpr) (env : Env) :
    denoteT bt fuel (.cfBreak p) env = (denoteT bt fuel p env).bind fun q =>
      match q with
      | (.val (.controlFlow k v), e1) => .ret (.val (.controlFlow k v), e1)
      | (.val v, e1) => .ret (.val (.controlFlow true v), e1)
      | (o, e1) => .ret (o, e1) := by
  rw [denoteT, tm_bind_run]
  congr 1
  funext q
  rcases q with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

/-! ## The relation of the call trees of a body and its rewriting -/

variable (h₁ : ∀ e : E.Event, E.Resp e)

/-- **The relation of the call trees of two bodies**: from every environment, the readings are
    related by `RuttS` at equal events and answers; a leaf of the first that is not a value is a
    failed leaf, and a leaf of the first is matched by a leaf with the same environment and an
    outcome related by `RetRel`. -/
def ERelT (bt : TreeTable E) (fuel : Nat) (x y : ImpExpr) : Prop :=
  ∀ env, RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
    (fun r₁ r₂ => r₂.2 = r₁.2 ∧ RetRel r₁.1 r₂.1) (fun r => ¬ ∃ v, r.1 = .val v)
    (denoteT bt fuel x env) (denoteT bt fuel y env)

variable {h₁}

/-- Equal prefixes followed by related continuations are related. -/
theorem ruttS_bind_same {S R₁ R₂ : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (t : CallTree E S) {k₁ : S → CallTree E R₁} {k₂ : S → CallTree E R₂}
    (hk : ∀ s, RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail (k₁ s) (k₂ s)) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail (t.bind k₁) (t.bind k₂) :=
  NFProgCallTree.RuttS.bind (RR' := fun s₁ s₂ => s₁ = s₂) (Fail' := fun _ => False)
    (NFProgCallTree.RuttS.refl (fun _ => rfl) t) (fun s₁ _ hs => hs ▸ hk s₁)
    (fun _ hf => hf.elim)

/-- A leaf related to itself. -/
theorem ruttS_ret_self (r : Outcome × Env) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.2 = r₁.2 ∧ RetRel r₁.1 r₂.1) (fun r => ¬ ∃ v, r.1 = .val v)
      (.ret r) (.ret r) :=
  .ret ⟨rfl, Or.inl rfl⟩

/-- A body is related to itself. -/
theorem ERelT.refl (bt : TreeTable E) (fuel : Nat) (x : ImpExpr) : ERelT h₁ bt fuel x x :=
  fun _ => NFProgCallTree.RuttS.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _

/-- A body with the readings of `x` is related to `z` when `y` is. -/
theorem ERelT.trans_eq {bt : TreeTable E} {fuel : Nat} {x y z : ImpExpr}
    (h : ∀ env, denoteT bt fuel x env = denoteT bt fuel y env) (hyz : ERelT h₁ bt fuel y z) :
    ERelT h₁ bt fuel x z :=
  fun env => (h env) ▸ hyz env

/-- A failed leaf: an outcome that is not a value. -/
theorem ruttS_fail_ret {t₂ : CallTree E (Outcome × Env)} (o : Outcome) (e1 : Env)
    (ho : ∀ v, o ≠ .val v) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.2 = r₁.2 ∧ RetRel r₁.1 r₂.1) (fun r => ¬ ∃ v, r.1 = .val v)
      (.ret (o, e1)) t₂ :=
  .fail fun ⟨v, hv⟩ => ho v hv

/-- `seq (seq a₁ a₂) b` and `seq a₁ (seq a₂ b)` have the same call tree. -/
theorem denoteT_seq_assoc (bt : TreeTable E) (fuel : Nat) (a₁ a₂ b : ImpExpr) (env : Env) :
    denoteT bt fuel (.seq (.seq a₁ a₂) b) env = denoteT bt fuel (.seq a₁ (.seq a₂ b)) env := by
  rw [denoteT_seq_run, denoteT_seq_run, denoteT_seq_run, bind_assoc]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v <;> first | rfl | exact (denoteT_seq_run bt fuel a₂ b e1).symm
  all_goals rfl

/-- `seq a b` and `seq a k` are related when `b` and `k` are. -/
theorem ERelT.seq_congr {bt : TreeTable E} {fuel : Nat} {a b k : ImpExpr}
    (h : ERelT h₁ bt fuel b k) : ERelT h₁ bt fuel (.seq a b) (.seq a k) := by
  intro env
  rw [denoteT_seq_run, denoteT_seq_run]
  refine ruttS_bind_same _ fun p => ?_
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v <;> first | exact ruttS_ret_self _ | exact h e1
  all_goals exact ruttS_ret_self _

/-- `seq a b` and `ereSeq a k` are related when `b` and `k` are. -/
theorem ereSeq_relT {bt : TreeTable E} {fuel : Nat} (a : ImpExpr) :
    ∀ (b k : ImpExpr), ERelT h₁ bt fuel b k → ERelT h₁ bt fuel (.seq a b) (ereSeq a k) := by
  induction a using ImpExpr.ind with
  | cfBreak p _ =>
    intro b k _ env
    simp only [ereSeq]
    rw [denoteT_seq_run, denoteT_cfBreak_run, bind_assoc]
    conv => rhs; rw [← bind_ret (denoteT bt fuel p env)]
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with v | _ | _ | _ | _
    · cases v with
      | controlFlow kk w => exact ruttS_ret_self _
      | _ => exact .ret ⟨rfl, Or.inr ⟨_, rfl, rfl, rfl⟩⟩
    all_goals exact ruttS_fail_ret _ _ (fun _ h => by cases h)
  | ifThenElse c t e _ iht ihe =>
    intro b k hbk
    simp only [ereSeq]
    split
    · intro env
      rw [denoteT_seq_run, denoteT_ifThenElse_run, denoteT_ifThenElse_run, bind_assoc]
      refine ruttS_bind_same _ fun q => ?_
      rcases q with ⟨o, e1⟩
      rcases o with v | _ | _ | _ | _
      · cases v with
        | controlFlow kk w => exact ruttS_ret_self _
        | bool bb =>
          cases bb
          · exact (denoteT_seq_run bt fuel e b e1) ▸ ihe b k hbk e1
          · exact (denoteT_seq_run bt fuel t b e1) ▸ iht b k hbk e1
        | _ => exact ruttS_ret_self _
      all_goals exact ruttS_ret_self _
    · exact ERelT.seq_congr hbk
  | letBind n v body _ ihb =>
    intro b k hbk
    simp only [ereSeq]
    split
    · intro env
      rw [denoteT_seq_run, denoteT_letBind_run', denoteT_letBind_run', bind_assoc]
      refine ruttS_bind_same _ fun q => ?_
      rcases q with ⟨o, e1⟩
      rcases o with w | _ | _ | _ | _
      · cases w with
        | controlFlow kk w => exact ruttS_ret_self _
        | _ => exact (denoteT_seq_run bt fuel body b _) ▸ ihb b k hbk _
      all_goals exact ruttS_ret_self _
    · exact ERelT.seq_congr hbk
  | seq a₁ a₂ ih₁ ih₂ =>
    intro b k hbk
    simp only [ereSeq]
    split
    · exact ERelT.trans_eq (denoteT_seq_assoc bt fuel a₁ a₂ b) (ih₁ _ _ (ih₂ b k hbk))
    · exact ERelT.seq_congr hbk
  | _ => intro b k hbk; exact ERelT.seq_congr hbk

/-- **The call trees of a function body and of its rewriting `ere` are related.** -/
theorem ere_relT (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) : ERelT h₁ bt fuel e (ere e) := by
  induction e using ImpExpr.ind with
  | cfBreak p _ =>
    intro env
    simp only [ere]
    rw [denoteT_cfBreak_run]
    conv => rhs; rw [← bind_ret (denoteT bt fuel p env)]
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with v | _ | _ | _ | _
    · cases v with
      | controlFlow kk w => exact ruttS_ret_self _
      | _ => exact .ret ⟨rfl, Or.inr ⟨_, rfl, rfl, rfl⟩⟩
    all_goals exact ruttS_fail_ret _ _ (fun _ h => by cases h)
  | letBind n v body _ ihb =>
    intro env
    simp only [ere]
    rw [denoteT_letBind_run', denoteT_letBind_run']
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact ruttS_ret_self _
      | _ => exact ihb _
    all_goals exact ruttS_ret_self _
  | seq a b _ ihb =>
    simp only [ere]
    exact ereSeq_relT a b (ere b) ihb
  | ifThenElse c t e _ iht ihe =>
    intro env
    simp only [ere]
    rw [denoteT_ifThenElse_run, denoteT_ifThenElse_run]
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with v | _ | _ | _ | _
    · cases v with
      | controlFlow kk w => exact ruttS_ret_self _
      | bool bb =>
        cases bb
        · exact ihe e1
        · exact iht e1
      | _ => exact ruttS_ret_self _
    all_goals exact ruttS_ret_self _
  | _ => exact ERelT.refl bt fuel _

/-! ## The tail `Some` -/

/-- The reading of a variable just bound is a leaf with its value. -/
theorem denoteT_var_extend (bt : TreeTable E) (fuel : Nat) (n : String) (env : Env) (w : Value) :
    denoteT bt fuel (.var n) (env.extend n w) = .ret (.val w, env.extend n w) :=
  CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount.denoteT_var_run bt fuel n _ w
    (by simp [Env.extend])

/-- **The call trees of `e` and `tailSome e` have equal events and outcomes**, from every
    environment; the final environment of `tailSome e` lacks the bindings of the returned
    names. -/
theorem tailSome_relT (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) (env : Env) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) (fun r₁ r₂ => r₂.1 = r₁.1)
      (fun _ => False) (denoteT bt fuel e env) (denoteT bt fuel (tailSome e) env) := by
  fun_induction tailSome e generalizing env with
  | case1 n v b h =>
    rw [isSomeRet_eq h, denoteT_letBind_run']
    conv => rhs; rw [← bind_ret (denoteT bt fuel v env)]
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact .ret rfl
      | _ => dsimp only; rw [denoteT_var_extend]; exact .ret rfl
    all_goals exact .ret rfl
  | case2 n v b h ih =>
    rw [denoteT_letBind_run', denoteT_letBind_run']
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact .ret rfl
      | _ => exact ih _
    all_goals exact .ret rfl
  | case3 a b ih =>
    rw [denoteT_seq_run, denoteT_seq_run]
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact .ret rfl
      | _ => exact ih _
    all_goals exact .ret rfl
  | case4 c t e iht ihe =>
    rw [denoteT_ifThenElse_run, denoteT_ifThenElse_run]
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact .ret rfl
      | bool bb =>
        cases bb
        · exact ihe _
        · exact iht _
      | _ => exact .ret rfl
    all_goals exact .ret rfl
  | case5 e t ih =>
    rw [denoteT, denoteT]
    exact ih env
  | case6 =>
    exact NFProgCallTree.RuttS.refl (RR := fun r₁ r₂ : Outcome × Env => r₂.1 = r₁.1)
      (fun _ => rfl) _

/-! ## The choice -/

/-- **The call tree of the chosen body is related to that of the normal form.** From every
    environment, the reading of `anfEPick ok a` is related to the reading of `a` at equal events
    and answers: a leaf of `a` that is not a value is a failed leaf, and a value leaf is matched
    by a leaf whose outcome is related by `RetRel`. -/
theorem anfEPick_relT (bt : TreeTable E) (fuel : Nat) (ok : ImpExpr → Bool) (a : ImpExpr)
    (env : Env) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => RetRel r₁.1 r₂.1) (fun r => ¬ ∃ v, r.1 = .val v)
      (denoteT bt fuel a env) (denoteT bt fuel (anfEPick ok a) env) := by
  unfold anfEPick
  split
  · exact NFProgCallTree.RuttS.refl (RR := fun r₁ r₂ : Outcome × Env => RetRel r₁.1 r₂.1)
      (fun _ => Or.inl rfl) _
  · split
    · exact NFProgCallTreeExt.RuttS.mono (fun _ _ h => h.2) (ere_relT bt fuel a env)
    · refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans
        (fun _ _ _ hf => hf.elim) (ere_relT bt fuel a env) (tailSome_relT bt fuel (ere a) env))
      rintro r₀ r₂ ⟨r₁, ⟨-, h01⟩, h12⟩
      rw [h12]
      exact h01

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick
