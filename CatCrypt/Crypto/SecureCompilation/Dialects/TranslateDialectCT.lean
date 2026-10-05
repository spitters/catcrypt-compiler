/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-!
# Constant time through the `LowCT → catCryptDialect` front

`levelCheckF P c` is a level check of a `LowCT` command over one public-name
predicate `P` (the front binds every name, scalar or tower, in one `VarMap`): a
write makes its destination public exactly when every name it reads is public,
and an array access requires a public index. It follows the code the front emits:
`RFor` is checked once per unrolled trip, and `RIfNz` only in the φ-merge shape
the front compiles.

`levelCheckF_front`: when `levelCheckF` accepts `c` and the front
`translateDialectControl` translates it, the emitted program is accepted by the
`Com` level checker (`CryptoDialectCTLeak.catLevelCheck` at the owned parameters)
under entry labels that agree with `P` on the `VarMap`, and hence is constant
time (`levelCheckF_ct`).

## Main definitions

* `LblLe`, `ContChk`, `LabAgree`
* `levelCheckF`

## Main results

* `levelCheck_mono`: the `Com` checker accepts under more public labels
* `lowerSExpr_chk`: the scalar-expression chain
* `levelCheckF_full`, `levelCheckF_front`, `levelCheckF_ct`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectCT

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType SecretLevel)

/-! ## Monotonicity of the `Com` checker -/

section Mono

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-- `L₁` is at least as public as `L₂`. -/
def LblLe {Γ : Ctxt d} (L₁ L₂ : Labels Γ) : Prop :=
  ∀ (t : d.Ty) (v : Ctxt.Var Γ t), lvlOf v L₂ = .Public → lvlOf v L₁ = .Public

omit [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] in
theorem joinAll_mono {Γ : Ctxt d} {L₁ L₂ : Labels Γ} (h : LblLe L₁ L₂) :
    ∀ {tys : List d.Ty} (args : HVector (fun ty => Ctxt.Var Γ ty) tys),
      joinAll (argLvls L₂ args) = .Public → joinAll (argLvls L₁ args) = .Public := by
  intro tys args
  induction args with
  | nil => intro _; rfl
  | cons v rest ih =>
      intro hj
      obtain ⟨hv, hr⟩ := join_eq_public hj
      simp only [argLvls, joinAll, h _ v hv, ih hr]
      rfl

omit [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] in
theorem getD_mono {Γ : Ctxt d} {L₁ L₂ : Labels Γ} (h : LblLe L₁ L₂) :
    ∀ {tys : List d.Ty} (args : HVector (fun ty => Ctxt.Var Γ ty) tys) (k : Nat),
      (argLvls L₂ args).getD k .Secret = .Public →
      (argLvls L₁ args).getD k .Secret = .Public := by
  intro tys args
  induction args with
  | nil => intro k hk; simp [argLvls] at hk
  | cons v rest ih =>
      intro k hk
      cases k with
      | zero =>
          simp only [argLvls, List.getD_cons_zero] at hk ⊢
          exact h _ v hk
      | succ k =>
          simp only [argLvls, List.getD_cons_succ] at hk ⊢
          exact ih k hk

omit [DialectDenote d] in
theorem opAccepts_mono (M : LeakModel d) {Γ : Ctxt d} {L₁ L₂ : Labels Γ} (h : LblLe L₁ L₂)
    (op : d.Op) (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig op))
    (hacc : opAccepts M op (argLvls L₂ args) = true) :
    opAccepts M op (argLvls L₁ args) = true := by
  unfold opAccepts at hacc ⊢
  split
  · rfl
  · next k hk =>
      rw [hk] at hacc
      simp only [decide_eq_true_eq] at hacc ⊢
      exact getD_mono h args k hacc
  · next m hk =>
      rw [hk] at hacc
      simp only [decide_eq_true_eq] at hacc ⊢
      exact joinAll_mono h args hacc
  · next f hk =>
      rw [hk] at hacc
      simp only [decide_eq_true_eq] at hacc ⊢
      exact joinAll_mono h args hacc

omit [DialectDenote d] in
/-- The `Com` checker accepts under labels at least as public. -/
theorem levelCheck_mono (M : LeakModel d) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (L₁ L₂ : Labels Γ), LblLe L₁ L₂ →
      Com.levelCheck M c L₂ = true → Com.levelCheck M c L₁ = true := by
  intro Γ t c
  induction c with
  | ret v => intro _ _ _ _; rfl
  | @var Γ t s e body ih =>
      intro L₁ L₂ hle hc
      simp only [Com.levelCheck, Bool.and_eq_true] at hc ⊢
      refine ⟨opAccepts_mono M hle e.op e.args hc.1, ih _ _ ?_ hc.2⟩
      intro t' v hv
      cases v with
      | here => exact joinAll_mono hle e.args hv
      | there v => exact hle _ v hv

omit [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] in
theorem joinAll_one {Γ : Ctxt d} {L : Labels Γ} {t₁ : d.Ty} {v₁ : Ctxt.Var Γ t₁}
    (h₁ : lvlOf v₁ L = .Public) :
    joinAll (argLvls L (.cons v₁ .nil : HVector (fun ty => Ctxt.Var Γ ty) [t₁])) = .Public := by
  simp only [argLvls, joinAll, h₁]; rfl

omit [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] in
theorem joinAll_two {Γ : Ctxt d} {L : Labels Γ} {t₁ t₂ : d.Ty} {v₁ : Ctxt.Var Γ t₁}
    {v₂ : Ctxt.Var Γ t₂} (h₁ : lvlOf v₁ L = .Public) (h₂ : lvlOf v₂ L = .Public) :
    joinAll (argLvls L (.cons v₁ (.cons v₂ .nil) :
      HVector (fun ty => Ctxt.Var Γ ty) [t₁, t₂])) = .Public := by
  simp only [argLvls, joinAll, h₁, h₂]; rfl

omit [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] in
theorem joinAll_three {Γ : Ctxt d} {L : Labels Γ} {t₁ t₂ t₃ : d.Ty} {v₁ : Ctxt.Var Γ t₁}
    {v₂ : Ctxt.Var Γ t₂} {v₃ : Ctxt.Var Γ t₃} (h₁ : lvlOf v₁ L = .Public)
    (h₂ : lvlOf v₂ L = .Public) (h₃ : lvlOf v₃ L = .Public) :
    joinAll (argLvls L (.cons v₁ (.cons v₂ (.cons v₃ .nil)) :
      HVector (fun ty => Ctxt.Var Γ ty) [t₁, t₂, t₃])) = .Public := by
  simp only [argLvls, joinAll, h₁, h₂, h₃]; rfl

omit [DialectDenote d] in
/-- A binding is accepted when its operation is and the tail is accepted with a
    recorded level at most as public as the join of the argument levels. -/
theorem levelCheck_var_intro (M : LeakModel d) {Γ : Ctxt d} {s t : d.Ty}
    (e : Expr d Γ s) (tail : Com d (s :: Γ) t) (L : Labels Γ) (l : SecretLevel)
    (hacc : opAccepts M e.op (argLvls L e.args) = true)
    (hl : l = .Public → joinAll (argLvls L e.args) = .Public)
    (ht : Com.levelCheck M tail (.cons l L) = true) :
    Com.levelCheck M (.var e tail) L = true := by
  simp only [Com.levelCheck, Bool.and_eq_true]
  refine ⟨hacc, levelCheck_mono M tail _ _ ?_ ht⟩
  intro t' v hv
  cases v with
  | here => exact hl hv
  | there v => exact hv

end Mono

/-! ## Prefix checks -/

/-- The owned leakage model of the dialect. -/
abbrev Mo : LeakModel catCryptDialect := catLeakModel .owned

/-- Labels over a dialect context. -/
abbrev Lb (Γ : Ctx) : Type := Labels (d := catCryptDialect) Γ

/-- The prefix `f` is accepted from labels `L` whenever the tail is accepted from
    labels `L'`. -/
def ContChk {Γ Γ' : Ctx} (f : ComCont Γ Γ') (L : Lb Γ) (L' : Lb Γ') : Prop :=
  ∀ {t : CryptoTy} (tail : Com catCryptDialect Γ' t) (c : Com catCryptDialect Γ t),
    f tail = some c → Com.levelCheck Mo tail L' = true → Com.levelCheck Mo c L = true

theorem contChk_id {Γ : Ctx} (L : Lb Γ) : ContChk ComCont.id L L := by
  intro t tail c h ht
  simp only [ComCont.id, Option.some.injEq] at h
  subst h; exact ht

/-- A binding whose operation the checker accepts, with a recorded level at most
    as public as the join of its argument levels. -/
theorem contChk_varBind {Γ : Ctx} {s : CryptoTy} (e : Expr catCryptDialect Γ s)
    (L : Lb Γ) (l : SecretLevel)
    (hacc : opAccepts Mo e.op (argLvls L e.args) = true)
    (hl : l = .Public → joinAll (argLvls L e.args) = .Public) :
    ContChk (ComCont.varBind e) L (.cons l L) := by
  intro t tail c h ht
  simp only [ComCont.varBind, Option.some.injEq] at h
  subst h
  exact levelCheck_var_intro Mo e tail L l hacc hl ht

theorem contChk_comp {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    {L : Lb Γ} {L' : Lb Γ'} {L'' : Lb Γ''}
    (hf : ContChk f L L') (hg : ContChk g L' L'') : ContChk (ComCont.comp f g) L L'' := by
  intro t tail c h ht
  simp only [ComCont.comp] at h
  split at h
  · next b' hb => exact hf b' c h (hg tail b' hb ht)
  · exact absurd h (by simp)

/-- An operation the owned model classes quiet is accepted under every labels. -/
theorem accepts_quiet {Γ : Ctx} (op : CatCryptOp)
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) (DialectSignature.sig op))
    (L : Lb Γ) (h : catKind .owned op = .quiet) :
    opAccepts Mo op (argLvls L args) = true := by
  simp only [opAccepts, Mo, catLeakModel, h]

/-! ## Agreement of labels with a public-name predicate -/

/-- Every name `Q` marks public is bound, if at all, to a public position. -/
def LabAgree {Γ : Ctx} (Q : String → Bool) (vm : VarMap Γ) (L : Lb Γ) : Prop :=
  ∀ x, Q x = true → ∀ (t : CryptoTy) (v : CVar Γ t), vm.lookup x = some ⟨t, v⟩ →
    lvlOf (toVIRVar v) L = .Public

theorem labAgree_weaken {Γ : Ctx} {s : CryptoTy} {Q : String → Bool} {vm : VarMap Γ}
    {L : Lb Γ} (h : LabAgree Q vm L) (l : SecretLevel) :
    LabAgree Q (vm.weaken (t := s)) (.cons l L) := by
  intro x hx t v hv
  simp only [VarMap.weaken] at hv
  split at hv
  · next t' v' hl =>
      simp only [Option.some.injEq, Sigma.mk.injEq] at hv
      obtain ⟨rfl, hveq⟩ := hv
      cases hveq
      exact h x hx _ v' hl
  · exact absurd hv (by simp)

/-- Binding `x` at a new top position with level `l`: the names `Q'` marks public
    other than `x` are public under `Q`, and `x` is public only if `l` is. -/
theorem labAgree_bind {Γ : Ctx} {s : CryptoTy} {Q Q' : String → Bool} {vm : VarMap Γ}
    {L : Lb Γ} (h : LabAgree Q vm L) (x : String) (l : SecretLevel)
    (hl : Q' x = true → l = .Public) (hQ : ∀ y, y ≠ x → Q' y = true → Q y = true) :
    LabAgree Q' (vm.bind (t := s) x) (.cons l L) := by
  intro y hy t v hv
  simp only [VarMap.bind] at hv
  split at hv
  · next hyx =>
      simp only [Option.some.injEq, Sigma.mk.injEq] at hv
      obtain ⟨rfl, hveq⟩ := hv
      cases hveq
      exact hl (hyx ▸ hy)
  · next hyx =>
    split at hv
    · next t' v' hlk =>
        simp only [Option.some.injEq, Sigma.mk.injEq] at hv
        obtain ⟨rfl, hveq⟩ := hv
        cases hveq
        exact h y (hQ y hyx hy) _ v' hlk
    · exact absurd hv (by simp)

theorem lookupU64_spec {Γ : Ctx} {vm : VarMap Γ} {x : String} {v : CVar Γ (.sword 64)}
    (h : lookupU64 vm x = some v) : vm.lookup x = some ⟨.sword 64, v⟩ := by
  unfold lookupU64 at h
  split at h
  · next v' hl => cases h; exact hl
  · exact absurd h (by simp)

/-- Every variable of the expression is public under `Q`. -/
def AllPub (Q : String → Bool) : SExpr → Prop
  | .SVar x => Q x = true
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => AllPub Q a ∧ AllPub Q b
  | _ => True

theorem allPub_mono {Q Q' : String → Bool} (hQ : ∀ x, Q x = true → Q' x = true) :
    ∀ e : SExpr, AllPub Q e → AllPub Q' e := by
  intro e
  induction e with
  | SVar x => exact hQ x
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      exact fun h => ⟨iha h.1, ihb h.2⟩
  | _ => exact fun _ => trivial

/-- A name predicate that marks no lowering temporary public. -/
def NoTmp (Q : String → Bool) : Prop := ∀ k, Q (tmpName k) = false

/-! ## The source check -/

/-- The name is not spelled like a lowering temporary (`__sx…`). -/
def notTmpB (x : String) : Bool := x.toList.take 4 != "__sx".toList

theorem notTmpB_tmpName (k : Nat) : notTmpB (tmpName k) = false := by
  simp [notTmpB, tmpName]

/-- Set the public flag of `x`; a name spelled like a lowering temporary stays
    secret. -/
def setP (P : String → Bool) (x : String) (b : Bool) : String → Bool :=
  fun y => if y = x then (b && notTmpB x) else P y

theorem noTmp_setP {P : String → Bool} (h : NoTmp P) (x : String) (b : Bool) :
    NoTmp (setP P x b) := by
  intro k
  simp only [setP]
  split
  · next hx => subst hx; simp [notTmpB_tmpName]
  · exact h k

theorem setP_ne {P : String → Bool} {x y : String} {b : Bool} (h : y ≠ x) :
    setP P x b y = P y := by
  simp [setP, h]

theorem setP_self_imp {P : String → Bool} {x : String} {b : Bool} (h : setP P x b x = true) :
    b = true := by
  simp only [setP, if_true, Bool.and_eq_true] at h
  exact h.1

/-- The Boolean form of `AllPub`. -/
def allPubB (Q : String → Bool) : SExpr → Bool
  | .SVar x => Q x
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => allPubB Q a && allPubB Q b
  | _ => true

theorem allPub_of_allPubB (Q : String → Bool) : ∀ e : SExpr, allPubB Q e = true → AllPub Q e := by
  intro e
  induction e with
  | SVar x => exact id
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro h
      simp only [allPubB, Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | _ => exact fun _ => trivial

/-- The leaf names the dialect leakage reads as array accesses. -/
def arrLeafName (f : String) : Bool := f == "arrLoadDyn" || f == "arrStoreDyn"

/-- A leaf call `f(args)` has no secret-dependent event in the owned dialect leakage: `f` is
    a quiet leaf of the owned route, or every argument is public. -/
def leafCallOk (P : String → Bool) (f : String) (args : List Located) : Bool :=
  ownedQuietLeaf f || args.all fun a => P a.locVar

/-- A call `leafCallOk` does not refuse is a quiet leaf of the owned route or has public
    arguments. -/
theorem leafCallOk_of_ne_false{P : String → Bool} {f : String} {args : List Located}
    (h : ¬ leafCallOk P f args = false) :
    ownedQuietLeaf f = true ∨ (args.all fun a => P a.locVar) = true := by
  unfold leafCallOk at h
  cases hq : ownedQuietLeaf f with
  | true => exact Or.inl rfl
  | false => exact Or.inr (by simpa [hq] using h)

/-- **The front-faithful level check.** Over one public-name predicate `P`, the
    predicate after `c`, or `none`. A write makes its destination public exactly
    when every name it reads is public; an array access requires a public index;
    a leaf call requires `leafCallOk`: a quiet leaf of the owned route, or public
    arguments;
    `RFor` is checked once per unrolled trip; `RIfNz` is accepted only in the φ-merge
    shape, whose result is public exactly when the guard is. Leaf calls named like the
    dialect's array leaves, calls into a `TFp` slot, and every arm the check does not
    list are refused. -/
def levelCheckF (P : String → Bool) : LowCT → Option (String → Bool)
  | .RSkip => some P
  | .RAssert _ => some P
  | .RBlock b => levelCheckF P b
  | .RSeq a b => (levelCheckF P a).bind fun P' => levelCheckF P' b
  | .RScalarSet x _ => some (setP P x true)
  | .RLetU64Zero x b => levelCheckF (setP P x true) b
  | .RLetZero _ _ b => levelCheckF P b
  | .RScalarSetExpr x e => some (setP P x (allPubB P e))
  | .RCall f dest args =>
      if dest.locDst = .TFp ∨ arrLeafName f = true ∨ leafCallOk P f args = false then none
      else some (setP P dest.locVar (args.all fun a => P a.locVar))
  | .RCallDstThreaded f dst args =>
      if arrLeafName f = true ∨ leafCallOk P f (dst :: args) = false then none
      else some (setP P dst.locVar ((dst :: args).all fun a => P a.locVar))
  | .RSelect dst sel s0 s1 =>
      some (setP P dst.locVar (P sel && P s0.locVar && P s1.locVar))
  | .RTupleLoad dst src _ => some (setP P dst.locVar (P src.locVar))
  | .RArrLoadLit dst src _ => some (setP P dst.locVar (P src.locVar))
  | .RArrStoreLit arr _ src => some (setP P arr.locVar (P arr.locVar && P src.locVar))
  | .RArrLoad dst src i =>
      if P i then some (setP P dst.locVar (P src.locVar)) else none
  | .RArrStore arr i src =>
      if P i then some (setP P arr.locVar (P arr.locVar && P src.locVar)) else none
  | .RFor x N body =>
      Nat.rec (some P) (fun _ acc => acc.bind fun P' => levelCheckF (setP P' x true) body) N
  | .RIfNz g t e =>
      match asSingleScalarSet t, asSingleScalarSet e with
      | some ts, some es => if ts.name = es.name then some (setP P ts.name (P g)) else none
      | _, _ => none
  | _ => none

/-- The check keeps a temporary-free public predicate temporary-free. -/
theorem levelCheckF_noTmp : ∀ (c : LowCT) (P P' : String → Bool),
    levelCheckF P c = some P' → NoTmp P → NoTmp P' := by
  intro c
  induction c with
  | RSkip => intro P P' h hn; simp [levelCheckF] at h; exact h ▸ hn
  | RAssert _ => intro P P' h hn; simp [levelCheckF] at h; exact h ▸ hn
  | RBlock b ih => intro P P' h hn; exact ih P P' h hn
  | RLetZero _ _ b ih => intro P P' h hn; exact ih P P' h hn
  | RSeq a b iha ihb =>
      intro P P' h hn
      simp only [levelCheckF] at h
      cases ha : levelCheckF P a with
      | none => simp [ha] at h
      | some P₁ => simp only [ha, Option.bind_some] at h; exact ihb P₁ P' h (iha P P₁ ha hn)
  | RLetU64Zero x b ih => intro P P' h hn; exact ih _ P' h (noTmp_setP hn x true)
  | RFor x N body ih =>
      intro P P' h hn
      simp only [levelCheckF] at h
      induction N generalizing P' with
      | zero => simp at h; exact h ▸ hn
      | succ n ihn =>
          simp only at h
          cases hr : (Nat.rec (some P) (fun _ acc => acc.bind fun P' =>
              levelCheckF (setP P' x true) body) n : Option (String → Bool)) with
          | none => rw [hr] at h; simp at h
          | some P₁ =>
              rw [hr] at h
              simp only [Option.bind_some] at h
              exact ih _ P' h (noTmp_setP (ihn P₁ hr) x true)
  | RIfNz g t e _ _ =>
      intro P P' h hn
      simp only [levelCheckF] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact noTmp_setP hn _ _
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | RArrLoad _ _ _ | RArrStore _ _ _ =>
      intro P P' h hn
      simp only [levelCheckF] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact noTmp_setP hn _ _
      · exact absurd h (by simp)
  | RCall _ _ _ | RCallDstThreaded _ _ _ =>
      intro P P' h hn
      simp only [levelCheckF] at h
      split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h; subst h; exact noTmp_setP hn _ _
  | RScalarSet _ _ | RScalarSetExpr _ _ | RSelect _ _ _ _ | RTupleLoad _ _ _
  | RArrLoadLit _ _ _ | RArrStoreLit _ _ _ =>
      intro P P' h hn
      simp only [levelCheckF, Option.some.injEq] at h
      subst h; exact noTmp_setP hn _ _
  | _ => intro P P' h _; simp [levelCheckF] at h

/-! ## Resolved argument lists -/

theorem listSigma_fst {Γ : Ctx} :
    ∀ (xs : List ((t : CryptoTy) × CVar Γ t)), (listSigmaToCHVector xs).1 = xs.map (·.1)
  | [] => rfl
  | ⟨t, v⟩ :: rest => by
      have ih := listSigma_fst rest
      simp only [listSigmaToCHVector, List.map_cons]
      rw [ih]

theorem argLvls_listSigma {Γ : Ctx} (L : Lb Γ) :
    ∀ (xs : List ((t : CryptoTy) × CVar Γ t)),
      argLvls L (toVIRArgs (listSigmaToCHVector xs).2) = xs.map (fun p => lvlOf (toVIRVar p.2) L)
  | [] => rfl
  | ⟨t, v⟩ :: rest => by
      have ih := argLvls_listSigma L rest
      simp only [listSigmaToCHVector, List.map_cons]
      exact congrArg (lvlOf (toVIRVar v) L :: ·) ih

theorem joinAll_eq_public_of {ls : List SecretLevel} (h : ∀ l ∈ ls, l = .Public) :
    joinAll ls = .Public := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      rw [joinAll, h l (List.mem_cons_self), ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]
      rfl

/-- Resolved arguments of public names are at public positions. -/
theorem resolve_pub {Γ : Ctx} {vm : VarMap Γ} {L : Lb Γ} {Q : String → Bool}
    (hA : LabAgree Q vm L) :
    ∀ (args : List Located) (ra : List ((t : CryptoTy) × CVar Γ t)),
      resolveLocatedArgs vm args = some ra → (args.all fun a => Q a.locVar) = true →
      ∀ p ∈ ra, lvlOf (toVIRVar p.2) L = .Public
  | [], ra, h, _ => by simp [resolveLocatedArgs] at h; subst h; simp
  | a :: rest, ra, h, hq => by
      simp only [resolveLocatedArgs] at h
      cases hr : vm.lookup a.locVar with
      | none => simp [hr] at h
      | some r =>
        cases hrs : resolveLocatedArgs vm rest with
        | none => simp [hr, hrs] at h
        | some rs =>
          simp only [hr, hrs, Option.some.injEq] at h
          subst h
          simp only [List.all_cons, Bool.and_eq_true] at hq
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · obtain ⟨t, v⟩ := p
            exact hA _ hq.1 t v hr
          · exact resolve_pub hA rest rs hrs hq.2 p hp

/-! ## The scalar-expression chain -/

/-- **The scalar-expression chain.** The prefix `lowerSExpr` emits is accepted
    (every operation it emits is quiet); it keeps every name of a
    temporary-free public predicate public; and when every variable of the
    expression is public, its result name is public too. -/
theorem lowerSExpr_chk : ∀ (e : SExpr) {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) (L : Lb Γ)
    {o : DTransOut Γ} {nm : String} {cnt' : Nat},
    lowerSExpr vm cnt e = some (o, nm, cnt') →
    ∃ L' : Lb o.Γ', ContChk o.cont L L' ∧
      (∀ Q, NoTmp Q → LabAgree Q vm L → LabAgree Q o.vm L') ∧
      (∀ Q, AllPub Q e → LabAgree Q vm L →
        LabAgree (fun y => Q y || decide (y = nm)) o.vm L') := by
  intro e
  induction e with
  | SVar x =>
      intro Γ vm cnt L o nm cnt' h
      simp only [lowerSExpr] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨L, contChk_id L, fun Q _ hQ => hQ, fun Q hx hQ => ?_⟩
        intro y hy t v hv
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hy
        rcases hy with hy | rfl
        · exact hQ y hy t v hv
        · exact hQ _ hx t v hv
      · exact absurd h (by simp)
  | SLit n =>
      intro Γ vm cnt L o nm cnt' h
      simp only [lowerSExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨.cons .Public L, contChk_comp (contChk_id L)
        (contChk_varBind _ L .Public (accepts_quiet _ _ L rfl) (fun _ => rfl)),
        fun Q hnt hQ => ?_, fun Q _ hQ => ?_⟩
      · exact labAgree_bind hQ _ _ (fun h => absurd h (by rw [hnt _]; decide)) (fun y _ hy => hy)
      · exact labAgree_bind hQ _ _ (fun _ => rfl) (fun y hne hy => by simpa [hne] using hy)
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SMulHiU a b iha ihb =>
      intro Γ vm cnt L o nm cnt' h
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
        obtain ⟨oa, na, c1⟩ := r
        split at h
        · exact absurd h (by simp)
        · next s heqB =>
          obtain ⟨ob, nb, c2⟩ := s
          split at h
          · next va vb hva hvb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨La, hca, hAa, hBa⟩ := iha vm cnt L heqA
            obtain ⟨Lb', hcb, hAb, hBb⟩ := ihb oa.vm c1 La heqB
            refine ⟨.cons _ Lb', contChk_comp (contChk_comp hca hcb)
              (contChk_varBind _ Lb' _ (accepts_quiet _ _ Lb' rfl) id),
              fun Q hnt hQ => ?_, fun Q hall hQ => ?_⟩
            · exact labAgree_bind (hAb Q hnt (hAa Q hnt hQ)) _ _
                (fun h => absurd h (by rw [hnt _]; decide)) (fun y _ hy => hy)
            · have h1 := hBa Q hall.1 hQ
              have h2 := hBb (fun y => Q y || decide (y = na))
                (allPub_mono (fun x hx => by simp [hx]) b hall.2) h1
              have hpa := h2 na (by simp) _ va (lookupU64_spec hva)
              have hpb := h2 nb (by simp) _ vb (lookupU64_spec hvb)
              refine labAgree_bind h2 _ _ ?_ (fun y hne hy => ?_)
              · intro _
                exact joinAll_two hpa hpb
              · simp only [Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
                rcases hy with hy | hy
                · exact Or.inl (Or.inl hy)
                · exact absurd hy hne
          · exact absurd h (by simp)
  | SShl a b iha ihb | SShr a b iha ihb =>
      intro Γ vm cnt L o nm cnt' h
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
        obtain ⟨oa, na, c1⟩ := r
        split at h
        · exact absurd h (by simp)
        · next s heqB =>
          obtain ⟨ob, nb, c2⟩ := s
          split at h
          · next va vb hva hvb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨La, hca, hAa, hBa⟩ := iha vm cnt L heqA
            obtain ⟨Lb', hcb, hAb, hBb⟩ := ihb oa.vm c1 La heqB
            refine ⟨.cons _ Lb', contChk_comp (contChk_comp hca hcb)
              (contChk_varBind _ Lb' _ ?_ id), fun Q hnt hQ => ?_, fun Q hall hQ => ?_⟩
            · cases b <;> exact accepts_quiet _ _ Lb' rfl
            · exact labAgree_bind (hAb Q hnt (hAa Q hnt hQ)) _ _
                (fun h => absurd h (by rw [hnt _]; decide)) (fun y _ hy => hy)
            · have h1 := hBa Q hall.1 hQ
              have h2 := hBb (fun y => Q y || decide (y = na))
                (allPub_mono (fun x hx => by simp [hx]) b hall.2) h1
              have hpa := h2 na (by simp) _ va (lookupU64_spec hva)
              have hpb := h2 nb (by simp) _ vb (lookupU64_spec hvb)
              refine labAgree_bind h2 _ _ ?_ (fun y hne hy => ?_)
              · intro _
                cases b <;> first | exact joinAll_one hpa | exact joinAll_two hpa hpb
              · simp only [Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
                rcases hy with hy | hy
                · exact Or.inl (Or.inl hy)
                · exact absurd hy hne
          · exact absurd h (by simp)
  | _ =>
      intro Γ vm cnt L o nm cnt' h
      simp [lowerSExpr] at h

theorem labAgree_mono {Γ : Ctx} {Q Q' : String → Bool} {vm : VarMap Γ} {L : Lb Γ}
    (h : LabAgree Q vm L) (hQ : ∀ x, Q' x = true → Q x = true) : LabAgree Q' vm L :=
  fun x hx => h x (hQ x hx)

/-! ## The straight-line arms -/

/-- A quiet leaf of the owned route, other than the two array leaves, is quiet in the owned
    dialect leakage. -/
theorem catKind_owned_extCall_quiet {name : String} (hn : arrLeafName name = false)
    (hq : ownedQuietLeaf name = true) (argTys : List CryptoTy) (r : CryptoTy) :
    catKind .owned (.extCall name argTys r) = .quiet := by
  simp only [arrLeafName, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hn
  exact CryptoDialectCTLeak.catKind_extCall_quiet hn.1 hn.2 hq argTys r

/-- A leaf that is neither an array leaf nor a quiet leaf of the owned route is a
    variable-time leaf call in the owned dialect leakage. -/
theorem catKind_owned_extCall_vt {name : String} (hn : arrLeafName name = false)
    (hq : ownedQuietLeaf name = false) (argTys : List CryptoTy) (r : CryptoTy) :
    catKind .owned (.extCall name argTys r) = .vtCall name := by
  simp only [arrLeafName, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hn
  exact CryptoDialectCTLeak.catKind_extCall_vt hn.1 hn.2 hq argTys r

/-- One opaque leaf binding over resolved arguments: a quiet leaf of the owned route, or a
    leaf on public arguments. -/
theorem extCall_step {Γ : Ctx} {vm : VarMap Γ} {L : Lb Γ} {P : String → Bool}
    (hA : LabAgree P vm L) {name : String} (hn : arrLeafName name = false)
    {args : List Located}
    (hq : ownedQuietLeaf name = true ∨ (args.all fun a => P a.locVar) = true)
    {ra : List ((t : CryptoTy) × CVar Γ t)}
    (hra : resolveLocatedArgs vm args = some ra) {argTys : List CryptoTy}
    {hv : CHVector (fun t => CVar Γ t) argTys}
    (hls : listSigmaToCHVector ra = ⟨argTys, hv⟩) (retTy : CryptoTy) (dst : String) (b : Bool)
    (hb : b = true → (args.all fun a => P a.locVar) = true) :
    ∃ l : SecretLevel,
      ContChk (ComCont.varBind (extCallExpr name retTy hv)) L (.cons l L) ∧
      LabAgree (setP P dst b) (vm.bind (t := retTy) dst) (.cons l L) := by
  have hlv : argLvls L (toVIRArgs hv) = ra.map (fun p => lvlOf (toVIRVar p.2) L) := by
    have := argLvls_listSigma L ra
    rw [hls] at this
    exact this
  have hpub : (args.all fun a => P a.locVar) = true →
      joinAll (argLvls L (toVIRArgs hv)) = .Public := by
    intro hall
    rw [hlv]
    apply joinAll_eq_public_of
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    exact resolve_pub hA args ra hra hall p hp
  have hacc : opAccepts Mo (.extCall name argTys retTy) (argLvls L (toVIRArgs hv)) = true := by
    cases hqn : ownedQuietLeaf name with
    | true => exact accepts_quiet _ _ L (catKind_owned_extCall_quiet hn hqn _ _)
    | false =>
        have hall := hq.resolve_left (by simp [hqn])
        simp only [opAccepts, Mo, catLeakModel, catKind_owned_extCall_vt hn hqn]
        exact decide_eq_true (hpub hall)
  exact ⟨_, contChk_varBind _ L _ hacc id,
    labAgree_bind hA dst _ (fun h => hpub (hb (setP_self_imp h)))
      (fun y hne hy => by rwa [setP_ne hne] at hy)⟩

theorem mem_of_joinAll_public : ∀ {ls : List SecretLevel}, joinAll ls = .Public →
    ∀ l ∈ ls, l = .Public
  | [], _ => by simp
  | l :: ls, h => by
      obtain ⟨h1, h2⟩ := join_eq_public h
      intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact h1
      · exact mem_of_joinAll_public h2 l' hl'

theorem contChk_castCtx {Γ : Ctx} {a b : CryptoTy} (h : (a :: Γ) = (b :: Γ))
    {f : ComCont Γ (a :: Γ)} {L : Lb Γ} {l : SecretLevel}
    (hf : ContChk f L (.cons l L)) :
    ContChk (ComCont.castCtx h f) L (.cons l L) := by
  obtain rfl : a = b := (List.cons.inj h).1
  exact hf

/-- A list of levels whose members are all public at an appended index. -/
theorem getD_append_last {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD xs.length d = x := by
  simp

theorem lvls_resolved {Γ : Ctx} (L : Lb Γ) (ra : List ((t : CryptoTy) × CVar Γ t))
    (idx : (t : CryptoTy) × CVar Γ t) {argTys : List CryptoTy}
    {hv : CHVector (fun t => CVar Γ t) argTys}
    (hls : listSigmaToCHVector (ra ++ [idx]) = ⟨argTys, hv⟩) :
    argLvls L (toVIRArgs hv) = (ra ++ [idx]).map (fun p => lvlOf (toVIRVar p.2) L) ∧
      argTys.length - 1 = ra.length := by
  have h1 := argLvls_listSigma L (ra ++ [idx])
  have h2 := listSigma_fst (ra ++ [idx])
  rw [hls] at h1 h2
  refine ⟨h1, ?_⟩
  simp only at h2
  rw [h2]; simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The array-load prefix: its index argument is the index slot, and the loaded
    word is public when the array and the index are. -/
theorem arrLoadCont_chk {Γ : Ctx} (L : Lb Γ) (dty : TowerType)
    (ra : List ((t : CryptoTy) × CVar Γ t)) (idx : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} {hv : CHVector (fun t => CVar Γ t) argTys}
    (hls : listSigmaToCHVector (ra ++ [idx]) = ⟨argTys, hv⟩)
    (hidx : lvlOf (toVIRVar idx.2) L = .Public) :
    ∃ l : SecretLevel, ContChk (arrLoadCont dty ra idx hv) L (.cons l L) ∧
      ((∀ p ∈ ra, lvlOf (toVIRVar p.2) L = .Public) → l = .Public) := by
  obtain ⟨hlv, hlen⟩ := lvls_resolved L ra idx hls
  refine ⟨joinAll ((ra ++ [idx]).map fun p => lvlOf (toVIRVar p.2) L), ?_, fun hall => ?_⟩
  · unfold arrLoadCont
    split
    · next n arrV idxV =>
        refine contChk_varBind _ L _ ?_ (fun hl => ?_)
        · exact decide_eq_true hidx
        · have hm := mem_of_joinAll_public hl
          exact joinAll_two (hm _ (by simp)) hidx
    · refine contChk_varBind _ L _ ?_ (fun hl => ?_)
      · show opAccepts Mo (.extCall "arrLoadDyn" argTys _) (argLvls L (toVIRArgs hv)) = true
        simp only [opAccepts, Mo, catLeakModel, catKind_extCall_arrLoadDyn, decide_eq_true_eq]
        rw [hlv, hlen, List.map_append, List.map_cons, List.map_nil]
        rw [show ra.length = (ra.map fun p => lvlOf (toVIRVar p.2) L).length by simp,
          getD_append_last]
        exact hidx
      · show joinAll (argLvls L (toVIRArgs hv)) = .Public
        rw [hlv]; exact hl
  · apply joinAll_eq_public_of
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_append.mp hp with hp | hp
    · exact hall p hp
    · rw [List.mem_singleton.mp hp]; exact hidx

/-- The array-store prefix: its index argument is the index slot, and the stored
    array is public when the array, the value and the index are. -/
theorem arrStoreCont_chk {Γ : Ctx} (L : Lb Γ) (dty : TowerType)
    (ra : List ((t : CryptoTy) × CVar Γ t)) (idx : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} {hv : CHVector (fun t => CVar Γ t) argTys}
    (hls : listSigmaToCHVector (ra ++ [idx]) = ⟨argTys, hv⟩)
    (hidx : lvlOf (toVIRVar idx.2) L = .Public) :
    ∃ l : SecretLevel, ContChk (arrStoreCont dty ra idx hv) L (.cons l L) ∧
      ((∀ p ∈ ra, lvlOf (toVIRVar p.2) L = .Public) → l = .Public) := by
  obtain ⟨hlv, hlen⟩ := lvls_resolved L ra idx hls
  have hfb : ∃ l : SecretLevel,
      ContChk (ComCont.varBind (extCallExpr "arrStoreDyn" (encodeTy dty) hv)) L (.cons l L) ∧
      ((∀ p ∈ ra, lvlOf (toVIRVar p.2) L = .Public) → l = .Public) := by
    refine ⟨_, contChk_varBind _ L _ ?_ id, fun hall => ?_⟩
    · show opAccepts Mo (.extCall "arrStoreDyn" argTys _) (argLvls L (toVIRArgs hv)) = true
      simp only [opAccepts, Mo, catLeakModel, catKind_extCall_arrStoreDyn, decide_eq_true_eq]
      rw [hlv, hlen, List.map_append, List.map_cons, List.map_nil]
      rw [show ra.length = (ra.map fun p => lvlOf (toVIRVar p.2) L).length by simp,
        getD_append_last]
      exact hidx
    · show joinAll (argLvls L (toVIRArgs hv)) = .Public
      rw [hlv]
      apply joinAll_eq_public_of
      intro l hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      rcases List.mem_append.mp hp with hp | hp
      · exact hall p hp
      · rw [List.mem_singleton.mp hp]; exact hidx
  unfold arrStoreCont
  split
  · next n arrV srcV idxV =>
      split
      · next h =>
          refine ⟨_, contChk_castCtx _ (contChk_varBind _ L _ ?_ id), fun hall => joinAll_three
            (hall _ (List.mem_cons_self ..)) hidx
            (hall _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩
          exact decide_eq_true hidx
      · exact hfb
  · exact hfb

theorem arrLeafName_append {p : String} (s : String)
    (h1 : ¬ p.toList <+: "arrLoadDyn".toList) (h2 : ¬ p.toList <+: "arrStoreDyn".toList) :
    arrLeafName (p ++ s) = false := by
  simp only [arrLeafName, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  refine ⟨fun e => h1 ?_, fun e => h2 ?_⟩
  · rw [← e, String.toList_append]; exact List.prefix_append _ _
  · rw [← e, String.toList_append]; exact List.prefix_append _ _

/-- **The straight-line front.** When `levelCheckF` accepts `c` from `P` and
    `translateDialectFull` translates it, the emitted prefix is accepted from any
    labels agreeing with `P`, into labels agreeing with the predicate after `c`. -/
theorem levelCheckF_full : ∀ (c : LowCT) {Γ : Ctx} (vm : VarMap Γ) (L : Lb Γ)
    (P P' : String → Bool) (o : DTransOut Γ),
    levelCheckF P c = some P' → translateDialectFull vm c = some o → NoTmp P →
    LabAgree P vm L → ∃ L' : Lb o.Γ', ContChk o.cont L L' ∧ LabAgree P' o.vm L' := by
  intro c
  induction c with
  | RSkip =>
      intro Γ vm L P P' o hc ht _ hA
      simp only [levelCheckF, Option.some.injEq] at hc; subst hc
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at ht; subst ht
      exact ⟨L, contChk_id L, hA⟩
  | RAssert _ =>
      intro Γ vm L P P' o hc ht _ hA
      simp only [levelCheckF, Option.some.injEq] at hc; subst hc
      simp only [translateDialectFull, Option.some.injEq] at ht; subst ht
      exact ⟨L, contChk_id L, hA⟩
  | RBlock b ih =>
      intro Γ vm L P P' o hc ht hn hA
      exact ih vm L P P' o hc ht hn hA
  | RLetZero _ _ b ih =>
      intro Γ vm L P P' o hc ht hn hA
      exact ih vm L P P' o hc ht hn hA
  | RScalarSet x n =>
      intro Γ vm L P P' o hc ht _ hA
      simp only [levelCheckF, Option.some.injEq] at hc; subst hc
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at ht; subst ht
      exact ⟨.cons .Public L, contChk_varBind _ L _ (accepts_quiet _ _ L rfl) (fun _ => rfl),
        labAgree_bind hA x _ (fun _ => rfl) (fun y hne hy => by rwa [setP_ne hne] at hy)⟩
  | RSeq a b iha ihb =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      cases ha : levelCheckF P a with
      | none => simp [ha] at hc
      | some P₁ =>
        simp only [ha, Option.bind_some] at hc
        simp only [translateDialectFull] at ht
        cases hta : translateDialectFull vm a with
        | none => simp [hta] at ht
        | some o₁ =>
          simp only [hta] at ht
          cases htb : translateDialectFull o₁.vm b with
          | none => simp [htb] at ht
          | some o₂ =>
            simp only [htb, Option.some.injEq] at ht; subst ht
            obtain ⟨L₁, hc₁, hA₁⟩ := iha vm L P P₁ o₁ ha hta hn hA
            obtain ⟨L₂, hc₂, hA₂⟩ := ihb o₁.vm L₁ P₁ P' o₂ hc htb
              (levelCheckF_noTmp a P P₁ ha hn) hA₁
            exact ⟨L₂, contChk_comp hc₁ hc₂, hA₂⟩
  | RLetU64Zero x b ih =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      simp only [translateDialectFull] at ht
      cases htb : translateDialectFull (vm.bind (t := .sword 64) x) b with
      | none => simp [htb] at ht
      | some ob =>
        simp only [htb, Option.some.injEq] at ht; subst ht
        obtain ⟨L₁, hc₁, hA₁⟩ := ih (vm.bind x) (.cons .Public L) _ P' ob hc htb
          (noTmp_setP hn x true)
          (labAgree_bind hA x _ (fun _ => rfl) (fun y hne hy => by rwa [setP_ne hne] at hy))
        exact ⟨L₁, contChk_comp (contChk_varBind _ L _ (accepts_quiet _ _ L rfl)
          (fun _ => rfl)) hc₁, hA₁⟩
  | RScalarSetExpr x e =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF, Option.some.injEq] at hc; subst hc
      simp only [translateDialectFull] at ht
      cases hl : lowerSExpr vm 0 e with
      | none => simp [hl] at ht
      | some r =>
        obtain ⟨or, nm, cnt'⟩ := r
        simp only [hl] at ht
        cases hv : lookupU64 or.vm nm with
        | none => simp [hv] at ht
        | some v =>
          simp only [hv, Option.some.injEq] at ht; subst ht
          obtain ⟨Lr, hcr, hAr, hBr⟩ := lowerSExpr_chk e vm 0 L hl
          refine ⟨.cons _ Lr, contChk_comp hcr
            (contChk_varBind _ Lr _ (accepts_quiet _ _ Lr rfl) id),
            labAgree_bind (hAr P hn hA) x _ (fun h => ?_)
              (fun y hne hy => by rwa [setP_ne hne] at hy)⟩
          have hall := allPub_of_allPubB P e (setP_self_imp h)
          have hpv := hBr P hall hA nm (by simp) _ v (lookupU64_spec hv)
          exact joinAll_one hpv
  | RFor _ _ _ _ | RIfNz _ _ _ _ _ =>
      intro Γ vm L P P' o _ ht
      simp [translateDialectFull] at ht
  | RCall f dest args =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      split at hc
      · exact absurd hc (by simp)
      · next hnc =>
        simp only [Option.some.injEq] at hc; subst hc
        simp only [not_or, Bool.not_eq_true] at hnc
        simp only [translateDialectFull] at ht
        cases hra : resolveLocatedArgs vm args with
        | none => simp [hra] at ht
        | some ra =>
          simp only [hra] at ht
          split at ht
          · exfalso; simp_all
          · simp only [Option.some.injEq] at ht; subst ht
            obtain ⟨l, hcc, hAA⟩ := extCall_step hA hnc.2.1
              (leafCallOk_of_ne_false hnc.2.2) hra rfl _ dest.locVar _ id
            exact ⟨_, hcc, hAA⟩
  | RCallDstThreaded f dst args =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      split at hc
      · exact absurd hc (by simp)
      · next hnc =>
        simp only [Option.some.injEq] at hc; subst hc
        simp only [not_or, Bool.not_eq_true] at hnc
        simp only [translateDialectFull] at ht
        cases hra : resolveLocatedArgs vm (dst :: args) with
        | none => simp [hra] at ht
        | some ra =>
          simp only [hra, Option.some.injEq] at ht; subst ht
          obtain ⟨l, hcc, hAA⟩ := extCall_step hA hnc.1
            (leafCallOk_of_ne_false hnc.2) hra rfl _ dst.locVar _ id
          exact ⟨_, hcc, hAA⟩
  | RTupleLoad dst src idx =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF, Option.some.injEq] at hc; subst hc
      simp only [translateDialectFull] at ht
      cases hra : resolveLocatedArgs vm [src] with
      | none => simp [hra] at ht
      | some ra =>
        simp only [hra, Option.some.injEq] at ht; subst ht
        obtain ⟨l, hcc, hAA⟩ := extCall_step hA
          (arrLeafName_append (p := "tupleLoad:") _ (by decide) (by decide))
          (Or.inl (ownedQuietLeaf_tupleLoad _)) hra rfl _
          dst.locVar (P src.locVar) (fun h => by simp [h])
        exact ⟨_, hcc, hAA⟩
  | RArrLoad dst src i =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      split at hc
      · next hi =>
        simp only [Option.some.injEq] at hc; subst hc
        simp only [translateDialectFull] at ht
        cases hra : resolveLocatedArgs vm [src] with
        | none => simp [hra] at ht
        | some ra =>
          cases hix : vm.lookup i with
          | none => simp [hra, hix] at ht
          | some idx =>
            simp only [hra, hix, Option.some.injEq] at ht; subst ht
            obtain ⟨ti, iv⟩ := idx
            obtain ⟨l, hcc, hl⟩ := arrLoadCont_chk L dst.locDst ra ⟨ti, iv⟩ rfl
              (hA i hi ti iv hix)
            exact ⟨_, hcc, labAgree_bind hA dst.locVar l
              (fun h => hl (resolve_pub hA [src] ra hra (by simpa using setP_self_imp h)))
              (fun y hne hy => by rwa [setP_ne hne] at hy)⟩
      · exact absurd hc (by simp)
  | RArrStore arr i src =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      split at hc
      · next hi =>
        simp only [Option.some.injEq] at hc; subst hc
        simp only [translateDialectFull] at ht
        cases hra : resolveLocatedArgs vm [arr, src] with
        | none => simp [hra] at ht
        | some ra =>
          cases hix : vm.lookup i with
          | none => simp [hra, hix] at ht
          | some idx =>
            simp only [hra, hix, Option.some.injEq] at ht; subst ht
            obtain ⟨ti, iv⟩ := idx
            obtain ⟨l, hcc, hl⟩ := arrStoreCont_chk L arr.locDst ra ⟨ti, iv⟩ rfl
              (hA i hi ti iv hix)
            exact ⟨_, hcc, labAgree_bind hA arr.locVar l
              (fun h => hl (resolve_pub hA [arr, src] ra hra (by simpa using setP_self_imp h)))
              (fun y hne hy => by rwa [setP_ne hne] at hy)⟩
      · exact absurd hc (by simp)
  | RArrLoadLit dst src idx =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF, Option.some.injEq] at hc; subst hc
      simp only [translateDialectFull] at ht
      split at ht
      · rename_i hlk
        simp only [Option.some.injEq] at ht; subst ht
        refine ⟨_, contChk_comp (contChk_varBind _ L .Public (accepts_quiet _ _ L rfl)
          (fun _ => rfl)) (contChk_varBind _ _ _ (by rfl) id),
          labAgree_bind (labAgree_weaken hA .Public) dst.locVar _ (fun h => ?_)
            (fun y hne hy => by rwa [setP_ne hne] at hy)⟩
        have hsrc := hA _ (by simpa using setP_self_imp h) _ _ hlk
        exact joinAll_two hsrc rfl
      · cases hra : resolveLocatedArgs vm [src] with
        | none => simp [hra] at ht
        | some ra =>
          simp only [hra, Option.some.injEq] at ht; subst ht
          obtain ⟨l, hcc, hAA⟩ := extCall_step hA
            (arrLeafName_append (p := "arrLoad:") _ (by decide) (by decide))
            (Or.inl (ownedQuietLeaf_arrLoad _)) hra rfl _
            dst.locVar (P src.locVar) (fun h => by simp [h])
          exact ⟨_, hcc, hAA⟩
  | RArrStoreLit arr idx src =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF, Option.some.injEq] at hc; subst hc
      simp only [translateDialectFull] at ht
      split at ht
      · rename_i hla hls
        simp only [Option.some.injEq] at ht; subst ht
        refine ⟨_, contChk_comp (contChk_varBind _ L .Public (accepts_quiet _ _ L rfl)
          (fun _ => rfl)) (contChk_varBind _ _ _ (by rfl) id),
          labAgree_bind (labAgree_weaken hA .Public) arr.locVar _ (fun h => ?_)
            (fun y hne hy => by rwa [setP_ne hne] at hy)⟩
        have hb := setP_self_imp h
        simp only [Bool.and_eq_true] at hb
        exact joinAll_three (hA _ hb.1 _ _ hla) rfl (hA _ hb.2 _ _ hls)
      · cases hra : resolveLocatedArgs vm [arr, src] with
        | none => simp [hra] at ht
        | some ra =>
          simp only [hra, Option.some.injEq] at ht; subst ht
          obtain ⟨l, hcc, hAA⟩ := extCall_step hA
            (arrLeafName_append (p := "arrStore:") _ (by decide) (by decide))
            (Or.inl (ownedQuietLeaf_arrStore _)) hra rfl _
            arr.locVar (P arr.locVar && P src.locVar) (fun h => by simpa using h)
          exact ⟨_, hcc, hAA⟩
  | RSelect dst sel s0 s1 =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF, Option.some.injEq] at hc; subst hc
      simp only [translateDialectFull] at ht
      split at ht
      · rename_i sV aV cV _ hsel ha hc'
        simp only [Option.some.injEq] at ht; subst ht
        refine ⟨.cons (joinAll [lvlOf (toVIRVar sV) L, lvlOf (toVIRVar aV) L,
            lvlOf (toVIRVar cV) L]) (.cons (lvlOf (toVIRVar sV) L) (.cons .Public L)), ?_,
          labAgree_bind (labAgree_weaken (labAgree_weaken hA _) _) dst.locVar _
            (fun h => ?_) (fun y hne hy => by rwa [setP_ne hne] at hy)⟩
        · show ContChk (selectCmpCont sV aV cV) _ _
          unfold selectCmpCont
          refine contChk_comp (contChk_varBind _ L .Public (accepts_quiet _ _ L rfl)
            (fun _ => rfl)) (contChk_comp (contChk_varBind _ _ _ (accepts_quiet _ _ _ rfl)
              (fun h => by exact joinAll_two h rfl))
              (contChk_varBind _ _ _ (accepts_quiet _ _ _ rfl) (fun h => ?_)))
          have hm := mem_of_joinAll_public h
          exact joinAll_three (hm (lvlOf (toVIRVar sV) L) (by simp))
            (hm (lvlOf (toVIRVar aV) L) (by simp)) (hm (lvlOf (toVIRVar cV) L) (by simp))
        · have hb := setP_self_imp h
          simp only [Bool.and_eq_true] at hb
          apply joinAll_eq_public_of
          intro l hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl | rfl
          · exact hA _ hb.1.1 _ _ hsel
          · exact hA _ hb.1.2 _ _ ha
          · exact hA _ hb.2 _ _ hc'
      · cases hra : resolveLocatedArgs vm [{ locVar := sel, locSrc := .TU64 }, s0, s1] with
        | none => simp [hra] at ht
        | some ra =>
          simp only [hra, Option.some.injEq] at ht; subst ht
          obtain ⟨l, hcc, hAA⟩ := extCall_step hA (name := "select") rfl
            (Or.inl ownedQuietLeaf_select) hra rfl _
            dst.locVar (P sel && P s0.locVar && P s1.locVar)
            (fun h => by simpa [Bool.and_assoc] using h)
          exact ⟨_, hcc, hAA⟩
  | _ =>
      intro Γ vm L P P' o hc
      simp [levelCheckF] at hc

/-! ## The control arms -/

theorem asSSS_eq {c : LowCT} {s : SingleScalarSet} (h : asSingleScalarSet c = some s) :
    c = .RScalarSet s.name s.val := by
  cases c <;> simp [asSingleScalarSet] at h
  subst h; rfl

/-- **The front.** When `levelCheckF` accepts `c` from `P` and
    `translateDialectControl` translates it, the emitted prefix is accepted from any
    labels agreeing with `P`, into labels agreeing with the predicate after `c`. -/
theorem levelCheckF_front : ∀ (c : LowCT) {Γ : Ctx} (vm : VarMap Γ) (L : Lb Γ)
    (P P' : String → Bool) (o : DTransOut Γ),
    levelCheckF P c = some P' → translateDialectControl vm c = some o → NoTmp P →
    LabAgree P vm L → ∃ L' : Lb o.Γ', ContChk o.cont L L' ∧ LabAgree P' o.vm L' := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      cases ha : levelCheckF P a with
      | none => simp [ha] at hc
      | some P₁ =>
        simp only [ha, Option.bind_some] at hc
        rw [translateDialectControl_rSeq] at ht
        cases hta : translateDialectControl vm a with
        | none => simp [hta] at ht
        | some o₁ =>
          simp only [hta] at ht
          cases htb : translateDialectControl o₁.vm b with
          | none => simp [htb] at ht
          | some o₂ =>
            simp only [htb, Option.some.injEq] at ht; subst ht
            obtain ⟨L₁, hc₁, hA₁⟩ := iha vm L P P₁ o₁ ha hta hn hA
            obtain ⟨L₂, hc₂, hA₂⟩ := ihb o₁.vm L₁ P₁ P' o₂ hc htb
              (levelCheckF_noTmp a P P₁ ha hn) hA₁
            exact ⟨L₂, contChk_comp hc₁ hc₂, hA₂⟩
  | RLetU64Zero x b ih =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      rw [translateDialectControl_rLetU64Zero] at ht
      cases htb : translateDialectControl (vm.bind (t := .sword 64) x) b with
      | none => simp [htb] at ht
      | some ob =>
        simp only [htb, Option.some.injEq] at ht; subst ht
        obtain ⟨L₁, hc₁, hA₁⟩ := ih (vm.bind x) (.cons .Public L) _ P' ob hc htb
          (noTmp_setP hn x true)
          (labAgree_bind hA x _ (fun _ => rfl) (fun y hne hy => by rwa [setP_ne hne] at hy))
        exact ⟨L₁, contChk_comp (contChk_varBind _ L _ (accepts_quiet _ _ L rfl)
          (fun _ => rfl)) hc₁, hA₁⟩
  | RLetZero _ _ b ih =>
      intro Γ vm L P P' o hc ht hn hA
      rw [translateDialectControl_rLetZero] at ht
      exact ih vm L P P' o hc ht hn hA
  | RFor x N body ih =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      simp only [translateDialectControl] at ht
      induction N generalizing P' o with
      | zero =>
          obtain rfl : P = P' := Option.some.inj hc
          simp only [loopRForD, Option.some.injEq] at ht; subst ht
          exact ⟨L, contChk_id L, hA⟩
      | succ n ihn =>
          simp only at hc
          cases hr : (Nat.rec (some P) (fun _ acc => acc.bind fun P' =>
              levelCheckF (setP P' x true) body) n : Option (String → Bool)) with
          | none => rw [hr] at hc; simp at hc
          | some P₁ =>
            rw [hr] at hc
            simp only [Option.bind_some] at hc
            simp only [loopRForD] at ht
            cases hpre : loopRForD (translateBody := fun vm' => translateDialectControl vm' body)
                vm x n with
            | none => rw [hpre] at ht; simp at ht
            | some oPre =>
              rw [hpre] at ht
              simp only at ht
              cases hb : translateDialectControl (oPre.vm.bind (t := .sword 64) x) body with
              | none => rw [hb] at ht; simp at ht
              | some oBody =>
                rw [hb] at ht
                simp only [Option.some.injEq] at ht; subst ht
                obtain ⟨Lpre, hcpre, hApre⟩ := ihn P₁ oPre hr hpre
                have hn₁ : NoTmp P₁ := levelCheckF_noTmp (.RFor x n body) P P₁ hr hn
                obtain ⟨Lb', hcb, hAb⟩ := ih (oPre.vm.bind x) (.cons .Public Lpre) _ P' oBody hc
                  hb (noTmp_setP hn₁ x true)
                  (labAgree_bind hApre x _ (fun _ => rfl)
                    (fun y hne hy => by rwa [setP_ne hne] at hy))
                exact ⟨Lb', contChk_comp hcpre (contChk_comp (contChk_varBind _ Lpre _
                  (accepts_quiet _ _ Lpre rfl) (fun _ => rfl)) hcb), hAb⟩
  | RIfNz g t e _ _ =>
      intro Γ vm L P P' o hc ht hn hA
      simp only [levelCheckF] at hc
      cases hts : asSingleScalarSet t with
      | none => simp [hts] at hc
      | some ts =>
        cases hes : asSingleScalarSet e with
        | none => simp [hts, hes] at hc
        | some es =>
          simp only [hts, hes] at hc
          split at hc
          · next hname =>
            simp only [Option.some.injEq] at hc; subst hc
            obtain rfl := asSSS_eq hts
            obtain rfl := asSSS_eq hes
            obtain ⟨tn, tv⟩ := ts
            obtain ⟨en, ev⟩ := es
            simp only at hname
            subst hname
            simp only [translateDialectControl] at ht
            split at ht
            · next w condVar hlk =>
              simp only [translateDialectFull, translateDialect,
                asSingleScalarSet, List.cons_ne_self, dite_false, if_true,
                Option.some.injEq] at ht
              subst ht
              refine ⟨.cons (lvlOf (toVIRVar condVar) L) (.cons (lvlOf (toVIRVar condVar) L)
                (.cons (lvlOf (toVIRVar condVar) L) (.cons .Public (.cons .Public
                  (.cons .Public L))))), ?_, ?_⟩
              · refine contChk_comp (contChk_varBind _ L .Public (accepts_quiet _ _ L rfl)
                  (fun _ => rfl)) (contChk_comp (contChk_varBind _ _ .Public
                  (accepts_quiet _ _ _ rfl) (fun _ => rfl)) (contChk_comp (contChk_varBind _ _
                  .Public (accepts_quiet _ _ _ rfl) (fun _ => rfl)) (contChk_comp
                  (contChk_varBind _ _ _ (accepts_quiet _ _ _ rfl)
                    (fun h => by exact joinAll_two h rfl))
                  (contChk_comp (contChk_varBind _ _ _ (accepts_quiet _ _ _ rfl)
                    (fun h => by exact joinAll_one h))
                    (contChk_varBind _ _ _ (accepts_quiet _ _ _ rfl)
                      (fun h => by exact joinAll_three h rfl rfl))))))
              · refine labAgree_bind (labAgree_weaken (labAgree_weaken (labAgree_weaken
                  (labAgree_weaken (labAgree_weaken hA _) _) _) _) _) _ _ (fun h => ?_)
                  (fun y hne hy => by rwa [setP_ne hne] at hy)
                exact hA g (setP_self_imp h) _ condVar hlk
            · exact absurd ht (by simp)
          · exact absurd hc (by simp)
  | RWhileNz _ _ _ | RForRuntime _ _ _ _ =>
      intro Γ vm L P P' o hc
      simp [levelCheckF] at hc
  | _ =>
      intro Γ vm L P P' o hc ht hn hA
      exact levelCheckF_full _ vm L P P' o hc ht hn hA

/-- **Constant time through the front.** When `levelCheckF` accepts `c` from `P`,
    `translateDialectControl` translates it, and the entry labels `L` agree with
    `P` on the `VarMap`, the program the prefix builds around a return is
    constant time for `L` in the owned dialect leakage. -/
theorem levelCheckF_ct {c : LowCT} {Γ : Ctx} {vm : VarMap Γ} {L : Lb Γ}
    {P P' : String → Bool} {o : DTransOut Γ}
    (hc : levelCheckF P c = some P') (ht : translateDialectControl vm c = some o)
    (hn : NoTmp P) (hA : LabAgree P vm L) {t : CryptoTy}
    (w : Ctxt.Var (d := catCryptDialect) o.Γ' t)
    (com : Com catCryptDialect Γ t) (hcom : o.cont (Com.ret w) = some com) :
    catCT .owned L com := by
  obtain ⟨L', hcc, _⟩ := levelCheckF_front c vm L P P' o hc ht hn hA
  exact catLevelCheck_sound .owned com L (hcc (Com.ret w) com hcom rfl)

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectCT
