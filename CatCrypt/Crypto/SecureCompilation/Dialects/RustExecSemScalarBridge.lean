/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
public import ReprTransfer

/-!
# The `RustExec` ↔ `semScalar` value-adequacy bridge (reading B)

The word-level end-to-end theorem
`CompilerCorrectnessExtracted.rustToJasminCom_endToEnd_unconditional` takes the
operational premise `hExec : RustExec N leafSpec c rs rs'` (the saturating-`Nat`
`RustState` model) and the denotational premise
`hSem : semScalar c env = some env'` (the wrapping-`BitVec` `SEnvScalar` model)
as **independent** hypotheses, and reads the output value out of `semScalar`'s
`env'`. Tying that value back to the `RustExec` `Nat` model is a per-fragment
`inRange` reconciliation, outside that theorem. This module supplies
that reconciliation on a restricted fragment.

## The crux fact

The refinement `R n w := (w = BitVec.ofNat 64 n)` is a homomorphism for
`+ × << >> & ^` (`BitVec.ofNat` is a ring hom, `Nat` is initial) but *not* for
`-`: `Nat` monus saturates while `BitVec` wraps, so `ofNat (a −ℕ b)` and
`ofNat a −_BV ofNat b` disagree exactly on underflow. The transfer is therefore
free on the clean arms and carries an `inRange` side condition only on
subtraction (and the no-overflow bounds). The already-proven leaf
`SExpr.evalBV_eq_ofNat_eval` localizes that condition; ParamTransfer's
`ReprTransfer` layer packages the refinement (§ "the ParamTransfer registration").

## The entry seam (reads-follow-writes)

The value relation is the **soundness** form `EnvRel` — *wherever* the source
env binds a non-temp name at `.sword 64`, its word is the `ofNat` image of the
`RustState` scalar. This is compatible with `ConsistentS` (the translation
consistency): both hold for the empty entry env (`fun _ => none`) at the empty
varmap, so the two entry hypotheses are jointly satisfiable. What `EnvRel` alone does
NOT give is that a *read* name is bound; that is the reads-follow-writes
condition, carried by the domain invariant `EnvBoundOn rs env B` (`env` correct
on the names in `B`) threaded against the structural scoping `afterB`/`readsOK`:
a covered command's free reads sit in its entry-bound set `B`, and its writes
extend the bound set to `afterB B c`. At the top level the entry-bound set is
empty, so `readsOK` degenerates to "every read follows a prior write" and the
tracked output must be one of the command's writes (`afterB ∅ c name`).

## The restricted fragment (`IsCoveredAdeq`)

`IsCoveredAdeq ⊆ IsCoveredSCtl` is the closed **word** fragment — scalar sets,
`srcClean` scalar-`SExpr` assignments, counted `RFor` loops, and φ-merge-only
`RIfNz` conditionals — carrying the per-arm side conditions under which the
`Nat` and `BitVec` models coincide (the literal / no-overflow / counter bounds).
The opaque-leaf arms (`RCall` / `RArrLoad` / …) are excluded: `semScalar` sends
every opaque leaf to a fixed `CryptoTy.default`, so tying such a slot back to the
`RustExec` `Nat` model is vacuous, and the tower-heap agreement it would need is
`RustStateInterp`'s (byte-leg) job, discharged by
`rustExecSimulatesDialect` in the e2e's existence conjunct.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-! ## The word-level state relations

Two reflections relate a `RustState`'s saturating-`Nat` scalar heap to a
`semScalar` `SEnvScalar`. `EnvRel` is the **strong/total** form — every non-temp
name bound at `.sword 64` to its `ofNat` image; it binds *infinitely* many
names, so it and `ConsistentS` (which pins the env's support to a finite
`VarMap`) are jointly unsatisfiable at any finite entry (`RustExecKernelAdeq`'s
`entry_trio_unsat_empty` records that clash). `EnvBoundOn rs env B` is the
**domain-restricted** form — correct only on the finite set `B`; it *is*
`ConsistentS`-compatible (`EnvBoundOn rs env (fun _ => False)` is vacuous, so the
empty entry env satisfies both), and it is what the seam-closing corollary
threads, at the price of the reads-follow-writes scoping (`readsOK`/`afterB`)
that says a read name lands in `B`. -/

/-- The **strong/total refinement**: every non-temp name is bound at `.sword 64`
    to the `BitVec.ofNat 64` image of its `Nat` value. The reserved `__sx`
    fresh-temp namespace is exempt. -/
def EnvRel (rs : RustState) (env : SEnvScalar) : Prop :=
  ∀ x : String, ¬ isTmpName x →
    env x = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar x)⟩

/-- The **domain-restricted refinement**: the env binds every non-temp name in
    `B` at `.sword 64` to its `ofNat` image. This is the simulation
    invariant — reads consume a `B`-membership to know the read name is bound,
    and writes extend `B`. `EnvBoundOn rs env (fun _ => False)` is trivially true,
    which discharges the entry at the empty varmap, and `EnvBoundOn rs env
    (fun _ => True)` is exactly `EnvRel rs env`. -/
def EnvBoundOn (rs : RustState) (env : SEnvScalar) (B : String → Prop) : Prop :=
  ∀ x : String, B x → ¬ isTmpName x →
    env x = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar x)⟩

/-- The `u64`-range invariant carried alongside the relations: every scalar slot
    is a `u64` (`< 2^64`), the invariant under which `Nat`-monus and
    `BitVec`-wrap coincide. -/
def ScalarInRange (rs : RustState) : Prop := ∀ x : String, rs.rsScalar x < 2 ^ 64

open Classical in
/-- The canonical fully-populated env of a `RustState`: every non-temp name bound
    at `.sword 64` to its `ofNat` image, temps unbound. It satisfies `EnvRel` by
    construction — the reusable strong-form entry env for any state. -/
noncomputable def derivedEnv (rs : RustState) : SEnvScalar :=
  fun s => if isTmpName s then none else some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar s)⟩

theorem envRel_derivedEnv (rs : RustState) : EnvRel rs (derivedEnv rs) := by
  intro x hx
  simp only [derivedEnv, if_neg hx]

/-- The strong reflection is the total-domain restricted reflection. -/
theorem envBoundOn_true_of_envRel {rs : RustState} {env : SEnvScalar} (h : EnvRel rs env) :
    EnvBoundOn rs env (fun _ => True) :=
  fun x _ hx => h x hx

/-- `EnvBoundOn` is monotone in the (dually-ordered) domain: shrinking the set of
    guaranteed-bound names weakens the guarantee. -/
theorem envBoundOn_mono {rs : RustState} {env : SEnvScalar} {B B' : String → Prop}
    (h : EnvBoundOn rs env B) (hsub : ∀ y, B' y → B y) : EnvBoundOn rs env B' :=
  fun y hy hnt => h y (hsub y hy) hnt

/-- `EnvBoundOn` transfers along `OnlyTmpBelow`: a companion env differing only on
    the fresh-temp region agrees on every (non-temp) `B`-name, so it too is bound. -/
theorem envBoundOn_onlyTmp {rs : RustState} {env env2 : SEnvScalar} {B : String → Prop}
    {cnt : Nat} (h : EnvBoundOn rs env B) (hotb : OnlyTmpBelow env env2 cnt) :
    EnvBoundOn rs env2 B := by
  intro y hy hnt
  rw [hotb y (Or.inl hnt)]; exact h y hy hnt

/-- `ScalarInRange` is preserved by a scalar update to an in-range value. -/
theorem scalarInRange_upd {rs : RustState} (h : ScalarInRange rs) (x : String) {v : Nat}
    (hv : v < 2 ^ 64) : ScalarInRange (rsSetScalar rs x v) := by
  intro y
  by_cases hyx : y = x
  · subst hyx; simpa only [rsSetScalar, beq_self_eq_true, if_pos] using hv
  · have hne : ¬ (y == x) = true := by simp [hyx]
    simp only [rsSetScalar, hne, if_false, Bool.false_eq_true]
    exact h y

/-- A scalar write over an `OnlyTmpBelow` companion env extends `EnvBoundOn` by the
    written name: the new binding agrees by construction, and every prior non-temp
    `B`-name is preserved (`rsSetScalar` / `env.upd` touch only the written name,
    and the companion agrees with the tracked env off the fresh-temp region). -/
theorem envBoundOn_updExpr {rs : RustState} {env env2 : SEnvScalar} {B : String → Prop}
    {cnt : Nat} (henv : EnvBoundOn rs env B) (hotb : OnlyTmpBelow env env2 cnt)
    (x : String) (v : Nat) :
    EnvBoundOn (rsSetScalar rs x v) (env2.upd x (t := .sword 64) (BitVec.ofNat 64 v))
      (fun y => B y ∨ y = x) := by
  intro y hy hnt
  by_cases hyx : y = x
  · subst hyx
    simp [SEnvScalar.upd, rsSetScalar]
  · have hb : B y := by
      rcases hy with h | h
      · exact h
      · exact absurd h hyx
    have hne : ¬ (y == x) = true := by simp [hyx]
    simp only [SEnvScalar.upd, if_neg hyx, rsSetScalar, hne, if_false, Bool.false_eq_true]
    rw [hotb y (Or.inl hnt)]; exact henv y hb hnt

/-- The `env2 = env` special case: a plain scalar write extends `EnvBoundOn`. -/
theorem envBoundOn_upd {rs : RustState} {env : SEnvScalar} {B : String → Prop}
    (henv : EnvBoundOn rs env B) (x : String) (v : Nat) :
    EnvBoundOn (rsSetScalar rs x v) (env.upd x (t := .sword 64) (BitVec.ofNat 64 v))
      (fun y => B y ∨ y = x) :=
  envBoundOn_updExpr henv (onlyTmpBelow_refl env 0) x v

/-- `EnvBoundOn` gives the reader value on a bound non-temp name — the `ofNat`
    refinement in `envReader` form, what `SExpr.evalBV`'s `SVar` leaves consume. -/
theorem envReader_of_envBoundOn {rs : RustState} {env : SEnvScalar} {B : String → Prop}
    (h : EnvBoundOn rs env B) (s : String) (hs : B s) (hns : ¬ isTmpName s) :
    envReader env s = BitVec.ofNat 64 (rs.rsScalar s) := by
  simp only [envReader, h s hs hns]

/-! ## The structural scoping (reads-follow-writes)

`afterB B c` is the bound-name set *after* running `c` from entry-bound set `B`
(writes extend it); `readsOK B c` says every free read of `c` sits in the set
bound when the read happens. `varsBoundIn B e` is the leaf condition (`e`'s
`SVar`s are in `B`). Together they are the reads-follow-writes side
condition the weakening of `EnvRel` introduces. -/

/-- `e`'s `SVar` leaves are all in `B`. -/
def varsBoundIn (B : String → Prop) : SExpr → Prop
  | .SVar x => B x
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => varsBoundIn B a ∧ varsBoundIn B b
  | _ => True

/-- The bound-name set after running `c` from entry-bound set `B`. Straight-line
    writes add their destination; `RFor` / `RIfNz` are conservative (they promise
    nothing new — a loop / conditional output must be pre-initialised into `B`),
    which keeps `afterB` count-independent and correct at the zero-trip case. -/
def afterB (B : String → Prop) : LowCT → (String → Prop)
  | .RBlock b => afterB B b
  | .RSeq c₁ c₂ => afterB (afterB B c₁) c₂
  | .RLetU64Zero n b => afterB (fun y => B y ∨ y = n) b
  | .RScalarSet n _ => fun y => B y ∨ y = n
  | .RScalarSetExpr x _ => fun y => B y ∨ y = x
  | _ => B

/-- Every entry-bound name stays bound: `afterB` only grows the bound set. -/
theorem le_afterB : ∀ (c : LowCT) (D : String → Prop) (y : String), D y → afterB D c y := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => exact fun D y hy => ih₂ _ y (ih₁ D y hy)
  | RBlock b ih => exact fun D y hy => ih D y hy
  | RLetU64Zero n b ih => exact fun D y hy => ih _ y (Or.inl hy)
  | RScalarSet _ _ => exact fun _ _ hy => Or.inl hy
  | RScalarSetExpr _ _ => exact fun _ _ hy => Or.inl hy
  | _ => exact fun D y hy => hy

/-- Every free read of `c` is bound when it happens, given entry-bound set `B`. -/
def readsOK (B : String → Prop) : LowCT → Prop
  | .RBlock b => readsOK B b
  | .RSeq c₁ c₂ => readsOK B c₁ ∧ readsOK (afterB B c₁) c₂
  | .RLetU64Zero n b => readsOK (fun y => B y ∨ y = n) b
  | .RScalarSetExpr _ e => varsBoundIn B e
  | .RFor x _ b => readsOK (fun y => B y ∨ y = x) b
  | .RIfNz name _ _ => B name
  | _ => True

/-! ## The canonical leaf oracle

On `IsCoveredAdeq` no opaque-leaf arm fires, so the `RustExec` leaf oracle is
never consulted; `canonicalLeafSpec` is the identity/default `LeafSpec` recorded
for the end-to-end composition interface (§ "compose into the end-to-end
discharge"). -/

/-- The canonical (default) leaf specification. Its call oracle returns the old
    destination value; the store/load oracles are identity — matching the
    information-free `CryptoTy.default` waist `semScalar` assigns opaque leaves.
    On `IsCoveredAdeq` it is never invoked. -/
def canonicalLeafSpec : LeafSpec where
  call := fun _ _ _ oldV _ => oldV
  limbStore := fun _ oldV _ _ => oldV

/-! ## The ParamTransfer registration of the `ofNat` refinement

The refinement `R n w := (w = BitVec.ofNat 64 n)` registers through
`ReprTransfer` at the **homomorphism (map) level** `BinOpHomOn` — *not* the
codomain-embedding (`ReprEmbedding`) or graded-retraction level (`ofNat 64` is
not injective, and `toNat ∘ ofNat 64 ≠ id` off-range). So it registers as
domain-restricted `BinOpHomOn`s: free on the ring / bitwise / shift arms, and the
one arm that needs a side condition — subtraction — is *not* a
`BinOpHomOn` at all (its no-underflow condition is relational, `b ≤ a`); its
whole-expression side-conditioned transfer is `SExpr.evalBV_eq_ofNat_eval`,
re-exported below as `sexprTransfer`. -/

open ReprTransfer

/-- Addition transfers freely: `BitVec.ofNat 64` is an additive homomorphism
    (`dom = fun _ => True`), the map-level `BinOpHomOn` for `+`. -/
def ofNatAddHom : BinOpHomOn (fun n : Nat => BitVec.ofNat 64 n) (fun _ => True)
    (· + ·) (· + ·) where
  app_eq a b _ _ := by rw [BitVec.ofNat_add]

/-- Multiplication transfers freely: the map-level `BinOpHomOn` for `×`. -/
def ofNatMulHom : BinOpHomOn (fun n : Nat => BitVec.ofNat 64 n) (fun _ => True)
    (· * ·) (· * ·) where
  app_eq a b _ _ := by rw [BitVec.ofNat_mul]

/-- **The side-conditioned `SExpr` transfer witness.** On the `inRange`
    sub-domain the wrapping `BitVec` evaluator agrees with the `ofNat` image of
    the saturating-`Nat` evaluator. Wraps the already-proven leaf
    `SExpr.evalBV_eq_ofNat_eval`. -/
theorem sexprTransfer (σ : String → Nat) (e : SExpr) (h : e.inRange σ) :
    e.evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 (e.eval σ) :=
  SExpr.evalBV_eq_ofNat_eval σ e h

/-! ## The command-level simulation -/

/-! ### The restricted fragment -/

/-- The straight-line word-adequacy fragment: the `IsCoveredS` word arms, with
    the per-arm `Nat`↔`BitVec` reconciliation side conditions. The opaque-leaf
    arms are excluded (see the module header). -/
inductive IsCoveredAdeqS : LowCT → Prop
  | rSkip : IsCoveredAdeqS .RSkip
  | rBlock {body : LowCT} : IsCoveredAdeqS body → IsCoveredAdeqS (.RBlock body)
  | rSeq {c₁ c₂ : LowCT} : IsCoveredAdeqS c₁ → IsCoveredAdeqS c₂ →
      IsCoveredAdeqS (.RSeq c₁ c₂)
  | rLetU64Zero {name : String} {body : LowCT} : IsCoveredAdeqS body →
      IsCoveredAdeqS (.RLetU64Zero name body)
  | rScalarSet (name : String) {n : Nat} (hn : n < 2 ^ 64) :
      IsCoveredAdeqS (.RScalarSet name n)
  | rScalarSetExpr (x : String) (e : SExpr) (hclean : srcClean e)
      (hir : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → e.inRange σ) :
      IsCoveredAdeqS (.RScalarSetExpr x e)

/-- The control-extended word-adequacy fragment. Mirrors `IsCoveredSCtl`: a
    single counted `RFor` or φ-merge `RIfNz` over straight-line word code. -/
inductive IsCoveredAdeq : LowCT → Prop
  | ofStraight {c : LowCT} : IsCoveredAdeqS c → IsCoveredAdeq c
  | rFor {x : String} {N : Nat} {body : LowCT} (hN : N ≤ 2 ^ 64) :
      IsCoveredAdeq body → IsCoveredAdeq (.RFor x N body)
  | rIfNz (name mergeName : String) (tv ev : Nat) (hname : ¬ isTmpName name)
      (htv : tv < 2 ^ 64) (hev : ev < 2 ^ 64) :
      IsCoveredAdeq (.RIfNz name (.RScalarSet mergeName tv) (.RScalarSet mergeName ev))

/-! ### The embedding `IsCoveredAdeq ⊆ IsCoveredSCtl` -/

theorem IsCoveredAdeqS.toIsCoveredS {c : LowCT} (h : IsCoveredAdeqS c) : IsCoveredS c := by
  induction h with
  | rSkip => exact .rSkip
  | rBlock _ ih => exact .rBlock ih
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rLetU64Zero _ ih => exact .rLetU64Zero ih
  | rScalarSet name hn => exact .rScalarSet name _
  | rScalarSetExpr x e hclean _ => exact .rScalarSetExpr x e hclean

theorem IsCoveredAdeq.toIsCoveredSCtl {c : LowCT} (h : IsCoveredAdeq c) : IsCoveredSCtl c := by
  induction h with
  | ofStraight hs => exact .ofStraight hs.toIsCoveredS
  | rFor _ _ ih => exact .rFor ih
  | rIfNz name mergeName tv ev _ _ _ =>
      exact .rIfNz (.ofStraight (.rScalarSet _ _)) (.ofStraight (.rScalarSet _ _))

/-! ### `semLowerSExpr` succeeds on a `varsBoundIn` env

The standalone success + non-temp-stability lemma for `semLowerSExpr`: under a
`FreshFrom` scratch region and `EnvBoundOn`-readability of `e`'s (`varsBoundIn`)
leaves, the env-mirror fold succeeds, touches only the fresh-temp region
(`OnlyTmpBelow`), and leaves its result slot readable. -/

/-- One binary `semLowerSExpr` node: `binNode` succeeds when both operand slots
    are readable, extends `OnlyTmpBelow` / `FreshFrom` by one fresh temp, and
    leaves its result temp readable. -/
theorem binNode_ok (env env2 : SEnvScalar) (na nb : String) (cnt c2 : Nat)
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hle : cnt ≤ c2) (hotb : OnlyTmpBelow env env2 cnt)
    (hna : (envReadU64 env2 na).isSome) (hnb : (envReadU64 env2 nb).isSome) :
    ∃ (env3 : SEnvScalar) (nm : String) (cnt' : Nat),
      binNode env2 na nb c2 f = some (env3, nm, cnt') ∧ cnt ≤ cnt' ∧
      OnlyTmpBelow env env3 cnt ∧ ResultOK nm cnt' ∧ (envReadU64 env3 nm).isSome := by
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp hna
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp hnb
  refine ⟨env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (f va vb),
    TranslateDialectDirectArms.tmpName c2, c2 + 1, ?_, by omega,
    onlyTmpBelow_upd hotb hle, Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩,
    by rw [envReadU64_upd_self]; rfl⟩
  simp only [binNode, hva, hvb]

theorem semLowerSExpr_ok' (rs : RustState) (B : String → Prop) :
    ∀ (e : SExpr) (env : SEnvScalar) (cnt : Nat),
      EnvBoundOn rs env B → varsBoundIn B e → srcClean e →
      ∃ (env2 : SEnvScalar) (nm : String) (cnt' : Nat),
        semLowerSExpr env cnt e = some (env2, nm, cnt') ∧ cnt ≤ cnt' ∧
        OnlyTmpBelow env env2 cnt ∧ ResultOK nm cnt' ∧ (envReadU64 env2 nm).isSome := by
  intro e
  induction e with
  | SVar x =>
      intro env cnt henv hvb hcl
      have hx : ¬ isTmpName x := hcl
      have hbx : B x := hvb
      have hbind : env x = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar x)⟩ := henv x hbx hx
      have hread : envReadU64 env x = some (BitVec.ofNat 64 (rs.rsScalar x)) := by
        simp only [envReadU64, hbind]
      refine ⟨env, x, cnt, ?_, le_refl _, onlyTmpBelow_refl env cnt, Or.inl hx, ?_⟩
      · simp only [semLowerSExpr, hread]
      · rw [hread]; rfl
  | SLit n =>
      intro env cnt _ _ _
      refine ⟨env.upd (TranslateDialectDirectArms.tmpName cnt) (t := .sword 64) (BitVec.ofNat 64 n),
        TranslateDialectDirectArms.tmpName cnt, cnt + 1, rfl, Nat.le_succ _,
        onlyTmpBelow_upd (onlyTmpBelow_refl env cnt) (le_refl _),
        Or.inr ⟨cnt, Nat.lt_succ_self _, rfl⟩, ?_⟩
      rw [envReadU64_upd_self]; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro env cnt henv hvb hcl
      obtain ⟨sa, sb⟩ := hcl
      obtain ⟨va, vb⟩ := hvb
      obtain ⟨env1, na, c1, hsemA, hleA, hotbA, hrokA, hreadA⟩ := iha env cnt henv va sa
      have henv1 : EnvBoundOn rs env1 B := envBoundOn_onlyTmp henv hotbA
      obtain ⟨env2, nb, c2, hsemB, hleB, hotbB, hrokB, hreadB⟩ := ihb env1 c1 henv1 vb sb
      have hna2 : (envReadU64 env2 na).isSome := by
        rw [readU64_stable hotbB hrokA]; exact hreadA
      simp only [semLowerSExpr, hsemA, hsemB]
      exact binNode_ok env env2 na nb cnt c2 _ (le_trans hleA hleB)
        (onlyTmpBelow_trans hotbA hotbB hleA) hna2 hreadB
  | SLt a b iha ihb => intro _ _ _ _ hcl; exact hcl.elim
  | SAsr a b iha ihb => intro _ _ _ _ hcl; exact hcl.elim
  | SMulS a b iha ihb => intro _ _ _ _ hcl; exact hcl.elim
  | SMulHiS a b iha ihb => intro _ _ _ _ hcl; exact hcl.elim
  | SLimb v i => intro _ _ _ _ hcl; exact hcl.elim

/-- `SExpr.evalBV` congruence restricted to `varsBoundIn`: readers agreeing on a
    `srcClean` expression's (`varsBoundIn`) leaves agree on the expression. The
    `varsBoundIn`-restricted twin of `evalBV_congr`, so a partial (`ConsistentS`)
    env can drive the `RScalarSetExpr` value proof. -/
theorem evalBV_congr_on (B : String → Prop) (β1 β2 : String → BitVec 64) :
    ∀ (e : SExpr), (∀ s, B s → ¬ isTmpName s → β1 s = β2 s) → varsBoundIn B e → srcClean e →
      SExpr.evalBV β1 e = SExpr.evalBV β2 e := by
  intro e
  induction e with
  | SVar x => intro hβ hvb hcl; simp only [SExpr.evalBV]; exact hβ x hvb hcl
  | SLit n => intro _ _ _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro hβ hvb hcl
      simp only [SExpr.evalBV, iha hβ hvb.1 hcl.1, ihb hβ hvb.2 hcl.2]
  | SLt a b iha ihb => intro _ _ hcl; exact hcl.elim
  | SAsr a b iha ihb => intro _ _ hcl; exact hcl.elim
  | SMulS a b iha ihb => intro _ _ hcl; exact hcl.elim
  | SMulHiS a b iha ihb => intro _ _ hcl; exact hcl.elim
  | SLimb v i => intro _ _ hcl; exact hcl.elim

/-- A `srcClean` expression has no `SLimb` node. -/
theorem limbFree_of_srcClean : ∀ e : SExpr, srcClean e → e.limbFree := by
  intro e
  induction e with
  | SVar x => intro _; trivial
  | SLit n => intro _; trivial
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro hcl; exact ⟨iha hcl.1, ihb hcl.2⟩
  | SLt a b iha ihb => intro hcl; exact hcl.elim
  | SAsr a b iha ihb => intro hcl; exact hcl.elim
  | SMulS a b iha ihb => intro hcl; exact hcl.elim
  | SMulHiS a b iha ihb => intro hcl; exact hcl.elim
  | SLimb v i => intro hcl; exact hcl.elim

/-! ### Straight-line agreement -/

/-- The straight-line half of the simulation: on `IsCoveredAdeqS`, a `RustExec`
    `Nat`-model run is tracked by a defined `semScalar` `BitVec`-model run whose
    output env is `EnvBoundOn` the write set `afterB B c`, given the entry
    `EnvBoundOn rs env B` and the scoping `readsOK B c`. -/
theorem agreeS {N : Nat} {leafSpec : LeafSpec} {c : LowCT} (h : IsCoveredAdeqS c) :
    ∀ {rs rs' : RustState} {env : SEnvScalar} {B : String → Prop},
      RustExec N leafSpec c rs rs' → EnvBoundOn rs env B → ScalarInRange rs → readsOK B c →
      ∃ env', semScalar c env = some env' ∧ EnvBoundOn rs' env' (afterB B c) ∧ ScalarInRange rs' := by
  induction h with
  | rSkip =>
      intro rs rs' env B hexec henv hir _
      cases hexec; exact ⟨env, rfl, henv, hir⟩
  | rBlock _ ih =>
      intro rs rs' env B hexec henv hir hreads
      cases hexec with | block _ _ _ hb =>
        simp only [semScalar]; exact ih hb henv hir hreads
  | rSeq _ _ ih₁ ih₂ =>
      intro rs rs' env B hexec henv hir hreads
      obtain ⟨hr1, hr2⟩ := hreads
      cases hexec with | seq _ _ _ _ _ h1 h2 =>
        obtain ⟨e1, hs1, he1, hi1⟩ := ih₁ h1 henv hir hr1
        obtain ⟨e2, hs2, he2, hi2⟩ := ih₂ h2 he1 hi1 hr2
        exact ⟨e2, by simp only [semScalar, hs1]; exact hs2, he2, hi2⟩
  | rLetU64Zero _ ih =>
      intro rs rs' env B hexec henv hir hreads
      cases hexec with | letU64Zero _ _ _ _ hbody =>
        simp only [semScalar]
        exact ih hbody (by simpa using envBoundOn_upd henv _ 0)
          (scalarInRange_upd hir _ (by positivity)) hreads
  | rScalarSet name hn =>
      intro rs rs' env B hexec henv hir _
      cases hexec
      exact ⟨_, rfl, envBoundOn_upd henv name _, scalarInRange_upd hir name hn⟩
  | rScalarSetExpr x e hclean hir_e =>
      intro rs rs' env B hexec henv hir hreads
      cases hexec
      rw [SExpr.evalState_eq_eval rs e (limbFree_of_srcClean e hclean)]
      have hvb : varsBoundIn B e := hreads
      obtain ⟨env2, nm, cnt', hsem2, _, hotb2, _, _⟩ :=
        semLowerSExpr_ok' rs B e env 0 henv hvb hclean
      have hval : SExpr.evalBV (envReader env) e = BitVec.ofNat 64 (SExpr.eval rs.rsScalar e) := by
        rw [evalBV_congr_on B (envReader env) (SExpr.liftEnv rs.rsScalar) e
              (fun s hs hns => by rw [envReader_of_envBoundOn henv s hs hns]; rfl) hvb hclean]
        exact sexprTransfer rs.rsScalar e (hir_e rs.rsScalar hir)
      refine ⟨env2.upd x (t := .sword 64) (BitVec.ofNat 64 (SExpr.eval rs.rsScalar e)),
        by simp only [semScalar, hsem2]; rw [hval], ?_, ?_⟩
      · exact envBoundOn_updExpr henv hotb2 x _
      · exact scalarInRange_upd hir x (SExpr.eval_lt_of_inRange _ _ (hir_e rs.rsScalar hir))

/-! ### Counted-loop agreement (Nat-induction) -/

/-- `BitVec.ofNat` is injective at `0` on the `u64` sub-domain — the φ-merge guard
    fact (`condv = 0#64 ↔ rsScalar name = 0` when the scalar is a `u64`). -/
theorem ofNat_eq_zero_iff {a : Nat} (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a = 0) ↔ a = 0 := by
  constructor
  · intro h
    have h2 : (BitVec.ofNat 64 a).toNat = 0 := by rw [h]; rfl
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at h2
  · rintro rfl; rfl

/-- The counted `RFor` loop, by `Nat`-induction on the trip count, reusing the
    body agreement `ihBody`. The loop invariant is `EnvBoundOn rs env B` on the
    fixed entry-bound set `B` (`afterB B (RFor …) = B`, conservative): each
    iteration re-binds the counter into `B ∪ {x}`, runs the body (which reads
    within that set and whose writes are folded back to `B` via `le_afterB`), and
    restores `EnvBoundOn` on `B`. -/
theorem agreeFor {N : Nat} {leafSpec : LeafSpec} {x : String} {body : LowCT}
    (ihBody : ∀ {rs rs' : RustState} {env : SEnvScalar} {B : String → Prop},
      RustExec N leafSpec body rs rs' → EnvBoundOn rs env B → ScalarInRange rs → readsOK B body →
      ∃ env', semScalar body env = some env' ∧ EnvBoundOn rs' env' (afterB B body) ∧ ScalarInRange rs') :
    ∀ (M : Nat), M ≤ 2 ^ 64 → ∀ {rs rs' : RustState} {env : SEnvScalar} {B : String → Prop},
      RustExec N leafSpec (.RFor x M body) rs rs' → EnvBoundOn rs env B → ScalarInRange rs →
      readsOK B (.RFor x M body) →
      ∃ env', semScalar (.RFor x M body) env = some env' ∧ EnvBoundOn rs' env' B ∧ ScalarInRange rs' := by
  intro M
  induction M with
  | zero =>
      intro _ rs rs' env B hexec henv hir _
      cases hexec
      exact ⟨env, rfl, henv, hir⟩
  | succ n ihN =>
      intro hN rs rs' env B hexec henv hir hreads
      cases hexec with | forSucc _ _ _ _ _ _ hFor hBody =>
        obtain ⟨envPre, hsPre, hePre, hiPre⟩ := ihN (by omega) hFor henv hir hreads
        have hbodyReads : readsOK (fun y => B y ∨ y = x) body := hreads
        obtain ⟨env', hs', he', hi'⟩ :=
          ihBody hBody (envBoundOn_upd hePre x n) (scalarInRange_upd hiPre x (by omega)) hbodyReads
        have hsPre' : semRForD (fun e => semScalar body e) x n env = some envPre := hsPre
        refine ⟨env', by simp only [semScalar, semRForD, hsPre']; exact hs', ?_, hi'⟩
        exact envBoundOn_mono he' (fun y hy => le_afterB body _ y (Or.inl hy))

/-! ### The command-level simulation -/

/-- **`rustExec_semScalar_agree_scoped` (reading-B value adequacy, scoped form).**
    A `RustExec` `Nat`-model run over the covered word fragment is tracked by a
    defined `semScalar` `BitVec`-model run whose output env is `EnvBoundOn` the
    write set `afterB B c`, given entry `EnvBoundOn rs env B`, `ScalarInRange`,
    and the reads-follow-writes scoping `readsOK B c`. -/
theorem rustExec_semScalar_agree_scoped {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (h : IsCoveredAdeq c) :
    ∀ {rs rs' : RustState} {env : SEnvScalar} {B : String → Prop},
      RustExec N leafSpec c rs rs' → EnvBoundOn rs env B → ScalarInRange rs → readsOK B c →
      ∃ env', semScalar c env = some env' ∧ EnvBoundOn rs' env' (afterB B c) ∧ ScalarInRange rs' := by
  induction h with
  | ofStraight hs => exact agreeS hs
  | rFor hN _ ih => exact agreeFor ih _ hN
  | rIfNz name mergeName tv ev hname htv hev =>
      intro rs rs' env B hexec henv hir hreads
      have hbname : B name := hreads
      have hcond : env name = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar name)⟩ :=
        henv name hbname hname
      cases hexec with
      | ifTrue _ _ _ _ _ v hveq hvne hct =>
          cases hct
          have hne0 : ¬ (BitVec.ofNat 64 (rs.rsScalar name) = 0#64) := fun hc =>
            hvne (hveq ▸ (ofNat_eq_zero_iff (hir name)).mp hc)
          refine ⟨env.upd mergeName (t := .sword 64) (BitVec.ofNat 64 tv), ?_,
            envBoundOn_mono (envBoundOn_upd henv mergeName tv) (fun y hy => Or.inl hy),
            scalarInRange_upd hir mergeName htv⟩
          simp only [semScalar, hcond, asSingleScalarSet, phiSelect, if_true, if_neg hne0]
      | ifFalse _ _ _ _ _ hveq hcf =>
          have heq0 : BitVec.ofNat 64 (rs.rsScalar name) = 0#64 :=
            (ofNat_eq_zero_iff (hir name)).mpr hveq
          clear hveq
          cases hcf
          refine ⟨env.upd mergeName (t := .sword 64) (BitVec.ofNat 64 ev), ?_,
            envBoundOn_mono (envBoundOn_upd henv mergeName ev) (fun y hy => Or.inl hy),
            scalarInRange_upd hir mergeName hev⟩
          simp only [semScalar, hcond, asSingleScalarSet, phiSelect, if_true, if_pos heq0]

/-- A `varsBoundIn` over a pointwise-true bound set is vacuous. -/
theorem varsBoundIn_of_all : ∀ (e : SExpr) (B : String → Prop), (∀ y, B y) → varsBoundIn B e := by
  intro e
  induction e with
  | SVar x => intro B hB; exact hB x
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro B hB; exact ⟨iha B hB, ihb B hB⟩
  | _ => intro B hB; trivial

/-- Over a pointwise-true entry-bound set every read is in scope. -/
theorem readsOK_of_all : ∀ (c : LowCT) (B : String → Prop), (∀ y, B y) → readsOK B c := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ =>
      intro B hB; exact ⟨ih₁ B hB, ih₂ _ (fun y => le_afterB c₁ B y (hB y))⟩
  | RBlock b ih => intro B hB; exact ih B hB
  | RLetU64Zero n b ih => intro B hB; exact ih _ (fun y => Or.inl (hB y))
  | RScalarSetExpr x e => intro B hB; exact varsBoundIn_of_all e B hB
  | RFor x N b ih => intro B hB; exact ih _ (fun y => Or.inl (hB y))
  | RIfNz name t e ihT ihE => intro B hB; exact hB name
  | _ => intro B hB; trivial

/-- On the total entry-bound set every read is trivially in scope. -/
theorem readsOK_true (c : LowCT) : readsOK (fun _ => True) c :=
  readsOK_of_all c _ (fun _ => trivial)

/-- **`rustExec_semScalar_agree` (strong-form value adequacy).** The total-domain
    specialisation of `rustExec_semScalar_agree_scoped`: from the strong reflection
    `EnvRel rs env` (which is `EnvBoundOn` on the total set, so every read is in
    scope, `readsOK_true`) the `semScalar` run is tracked and its output env again
    satisfies the strong `EnvRel`. This is the entry point the per-kernel
    `derivedEnv` route uses. -/
theorem rustExec_semScalar_agree {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (h : IsCoveredAdeq c) {rs rs' : RustState} {env : SEnvScalar}
    (hexec : RustExec N leafSpec c rs rs') (hRel : EnvRel rs env) (hir : ScalarInRange rs) :
    ∃ env', semScalar c env = some env' ∧ EnvRel rs' env' ∧ ScalarInRange rs' := by
  obtain ⟨env', hs, hb', hi'⟩ :=
    rustExec_semScalar_agree_scoped h hexec (envBoundOn_true_of_envRel hRel) hir (readsOK_true c)
  exact ⟨env', hs, fun x hx => hb' x (le_afterB c _ x trivial) hx, hi'⟩

/-! ## Compose into the end-to-end discharge

Feed `rustExec_semScalar_agree_scoped` into `rustToJasminCom_endToEnd_unconditional`:
the denotational premises `hSem` (`semScalar` defined) and `hVal` (the tracked
output value) come *from* `RustExec` + `EnvBoundOn` + the scoping, so the
emitted jasmin program's value leg is tied to the `RustExec` `Nat`-model output
`BitVec.ofNat 64 (rs'.rsScalar name)`. The entry `EnvBoundOn`/`readsOK` pair is
compatible with `ConsistentS` (both hold of the empty entry env), so there is no
free-standing `EnvRel` premise to satisfy alongside `ConsistentS`; the
top-level corollary discharges both entries internally. -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-- **`rustToJasminCom_endToEnd_rustexec_adeq` (reading-B value adequacy, composed).**
    On `IsCoveredAdeq`, from a `RustExec` `Nat`-model run and an entry env that
    reflects the tracked inputs (`EnvBoundOn rs env B`) together with the
    reads-follow-writes scoping (`readsOK B c`, and the tracked output written
    `afterB B c name`), the emitted jasmin program denotes to the `ctTransTy`
    image of the `RustExec` `Nat`-model output word `BitVec.ofNat 64
    (rs'.rsScalar name)`. `EnvBoundOn` is compatible with the translation
    consistency `ConsistentS` (they hold jointly of the entry env), unlike the
    `EnvRel`/`ConsistentS` pair. The `semScalar`
    premises of `rustToJasminCom_endToEnd_unconditional` are discharged from the
    `RustExec` run via `rustExec_semScalar_agree_scoped`; no additional axioms. -/
theorem rustToJasminCom_endToEnd_rustexec_adeq
    {Γ : Ctx}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (Vb : HVec Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env : SEnvScalar) (name : String) (w : CVar o.Γ' (.sword 64))
    (com : Com catCryptDialect Γ (.sword 64))
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy (.sword 64)))
    (B : String → Prop)
    (hAdeq : IsCoveredAdeq c)
    (hTrans : translateDialectControl vm c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hInv : RustStateInterp vm rs Vb)
    (hCons : ConsistentS vm V env)
    (hBound : EnvBoundOn rs env B) (hIR : ScalarInRange rs) (hReads : readsOK B c)
    (hOut : afterB B c name)
    (hName : o.vm.lookup name = some ⟨.sword 64, w⟩)
    (hNameNT : ¬ isTmpName name)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    (∃ Vb' : HVec o.Γ', RustStateInterp o.vm rs' Vb')
      ∧ jcom.denote (ctMapValD V) = ctTransTy (BitVec.ofNat 64 (rs'.rsScalar name)) := by
  obtain ⟨env', hSem, hBound', _⟩ := rustExec_semScalar_agree_scoped hAdeq hExec hBound hIR hReads
  have hVal : env' name = some ⟨(.sword 64 : CryptoTy), BitVec.ofNat 64 (rs'.rsScalar name)⟩ :=
    hBound' name hOut hNameNT
  exact rustToJasminCom_endToEnd_unconditional vm c o N leafSpec rs rs' Vb V env env'
    name w (BitVec.ofNat 64 (rs'.rsScalar name)) com jcom hAdeq.toIsCoveredSCtl hTrans hExec
    hInv hCons hSem hName hVal hRet hCom

/-- **`rustToJasminCom_endToEnd_rustexec_adeq_topLevel` (entry hypotheses gone).**
    The top-level specialisation at `VarMap.empty`: BOTH entry invariants are
    discharged internally — the byte-layout `RustStateInterp` via
    `BorrowSafety.entry_interp`, the valuation consistency via `consistentS_empty`,
    and the value-reflection `EnvBoundOn` **vacuously** (the empty entry env binds
    nothing, so the entry-bound set is empty); no free-standing `EnvRel` premise
    appears. The remaining hypotheses are the per-kernel data: the
    coverage, the compilation/run successes, the `u64`-range `hIR`, and the
    reads-follow-writes scoping `hReads`/`hOut` (over the empty entry-bound set:
    every read follows a prior write, and the tracked output is one of the
    command's writes). -/
theorem rustToJasminCom_endToEnd_rustexec_adeq_topLevel
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (name : String) (w : CVar o.Γ' (.sword 64))
    (com : Com catCryptDialect ([] : Ctx) (.sword 64))
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)))
    (hAdeq : IsCoveredAdeq c)
    (hTrans : translateDialectControl VarMap.empty c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hIR : ScalarInRange rs)
    (hReads : readsOK (fun _ => False) c)
    (hOut : afterB (fun _ => False) c name)
    (hNameNT : ¬ isTmpName name)
    (hName : o.vm.lookup name = some ⟨.sword 64, w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    (∃ Vb' : HVec o.Γ', RustStateInterp o.vm rs' Vb')
      ∧ jcom.denote
          (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (rs'.rsScalar name)) :=
  rustToJasminCom_endToEnd_rustexec_adeq VarMap.empty c o N leafSpec rs rs'
    HVec.nil (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx))
    (fun _ => none) name w com jcom (fun _ => False) hAdeq hTrans hExec
    (CatCrypt.Crypto.SecureCompilation.BorrowSafety.entry_interp rs)
    consistentS_empty (fun _ hx _ => hx.elim) hIR hReads hOut hName hNameNT hRet hCom

/-! ## The word-array extension

`IsCoveredAdeqArr` extends `IsCoveredAdeq` by the dynamic-index word-array arms
`RArrLoad ⟨d, TU64⟩ ⟨s, TArr k TU64⟩ i` and `RArrStore ⟨a, TArr k TU64⟩ i ⟨s, TU64⟩`,
and their twins over `TBytes (8 * m)` arrays.
On the `RustExec` side an array is a byte array in the tower heap `rsTower`, read
and written through the `arrLoad` / `arrStore` oracles of the `LeafSpec`, and the
loaded word lands in a `TU64` tower slot, not in `rsScalar`. On the `semScalar`
side the array is a `.memref` of 64-bit words read by `memGetDyn` and written by
`memSetDyn`, and the loaded word is a `.sword 64` binding. `arrWords` is the
little-endian word view of a `TArr k TU64` byte array and `bytesWords` that of a
`TBytes n` byte array; `TowerWordsOn rs env T`
binds every name in `T` to the word view of its tower slot; `ArrLoadWord` /
`ArrStoreWord` say the oracles read and write one word of that view. The tower
names `T` and the scalar names `B` are disjoint: `towerOK T c` is the name-kind
discipline (scalar writes outside `T`, array operands inside `T`) and `idxOK B c`
binds the index variables in the scalar set, threaded like `readsOK`. -/

/-- The word view of a `TArr k TU64` byte array: word `i` is the little-endian
    64-bit word at bytes `8 i .. 8 i + 7`, at the type `encodeTy (TArr k TU64)`. -/
noncomputable def arrWords (k : Nat) (v : RustVal (.TArr k .TU64)) :
    ⟦encodeTy (.TArr k .TU64)⟧ :=
  fun i => wordOfBytes8 (fun j => v ⟨8 * i.val + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    simp only [TowerType.storageBytes] at hi ⊢
    omega⟩)

/-- The word view of a `TBytes n` byte array: word `i` is the little-endian 64-bit
    word at bytes `8 i .. 8 i + 7`, a byte past `n` reading as `0`, at the type
    `encodeTy (TBytes n)`. -/
noncomputable def bytesWords (n : Nat) (v : RustVal (.TBytes n)) : ⟦encodeTy (.TBytes n)⟧ :=
  fun i => wordOfBytes8 (fun j => rustValByte v (8 * i.val + j.val))

/-- The word-view encoding of a tower value: a `TArr k TU64` array by `arrWords`, a
    `TBytes n` array by `bytesWords`, every other tower value by
    `cryptoTyOfRustVal`. -/
noncomputable def encodeTowerWords : (Σ t : TowerType, RustVal t) → (Σ t : CryptoTy, ⟦t⟧)
  | ⟨.TArr k .TU64, v⟩ => ⟨encodeTy (.TArr k .TU64), arrWords k v⟩
  | ⟨.TBytes n, v⟩ => ⟨encodeTy (.TBytes n), bytesWords n v⟩
  | ⟨t, v⟩ => ⟨encodeTy t, cryptoTyOfRustVal t v⟩

theorem encodeTowerWords_TU64 (v : RustVal .TU64) :
    encodeTowerWords ⟨.TU64, v⟩ = ⟨.sword 64, cryptoTyOfRustVal .TU64 v⟩ := rfl

theorem encodeTowerWords_TArr (k : Nat) (v : RustVal (.TArr k .TU64)) :
    encodeTowerWords ⟨.TArr k .TU64, v⟩ = ⟨encodeTy (.TArr k .TU64), arrWords k v⟩ := rfl

theorem encodeTowerWords_TBytes (n : Nat) (v : RustVal (.TBytes n)) :
    encodeTowerWords ⟨.TBytes n, v⟩ = ⟨encodeTy (.TBytes n), bytesWords n v⟩ := rfl

/-- The tower-heap reflection on `T`: the env binds every non-temp name in `T` to
    the word-view encoding of its tower slot, and is unbound where the tower heap
    is. The tower twin of `EnvBoundOn`. -/
def TowerWordsOn (rs : RustState) (env : SEnvScalar) (T : String → Prop) : Prop :=
  ∀ x : String, T x → ¬ isTmpName x → env x = (rs.rsTower x).map encodeTowerWords

/-- The `arrLoad` oracle reads one word: loading index `idx` of a `TArr k TU64`
    array into a `TU64` slot yields the word `memGetDyn (arrWords k a) idx`, and of
    a `TBytes (8 * m)` array the word `memGetDyn (bytesWords (8 * m) a) idx`. -/
def ArrLoadWord (leafSpec : LeafSpec) : Prop :=
  (∀ (d : String) (oldV : RustVal .TU64) (k : Nat) (a : RustVal (.TArr k .TU64)) (idx : Nat),
    cryptoTyOfRustVal .TU64 (leafSpec.arrLoad ⟨d, .TU64⟩ oldV ⟨.TArr k .TU64, a⟩ idx)
      = memGetDyn (arrWords k a) idx) ∧
  (∀ (d : String) (oldV : RustVal .TU64) (m : Nat) (a : RustVal (.TBytes (8 * m))) (idx : Nat),
    cryptoTyOfRustVal .TU64 (leafSpec.arrLoad ⟨d, .TU64⟩ oldV ⟨.TBytes (8 * m), a⟩ idx)
      = memGetDyn (bytesWords (8 * m) a) idx)

/-- The `arrStore` oracle writes one word: storing a `TU64` value at index `idx` of
    a `TArr k TU64` array yields the word view `memSetDyn (arrWords k a) idx v`, and
    of a `TBytes (8 * m)` array the word view `memSetDyn (bytesWords (8 * m) a) idx v`. -/
def ArrStoreWord (leafSpec : LeafSpec) : Prop :=
  (∀ (a : String) (k : Nat) (oldV : RustVal (.TArr k .TU64)) (idx : Nat) (sv : RustVal .TU64),
    arrWords k (leafSpec.arrStore ⟨a, .TArr k .TU64⟩ oldV idx ⟨.TU64, sv⟩)
      = memSetDyn (arrWords k oldV) idx (cryptoTyOfRustVal .TU64 sv)) ∧
  (∀ (a : String) (m : Nat) (oldV : RustVal (.TBytes (8 * m))) (idx : Nat) (sv : RustVal .TU64),
    bytesWords (8 * m) (leafSpec.arrStore ⟨a, .TBytes (8 * m)⟩ oldV idx ⟨.TU64, sv⟩)
      = memSetDyn (bytesWords (8 * m) oldV) idx (cryptoTyOfRustVal .TU64 sv))

/-- The name-kind discipline of `c` against the tower-name set `T`: every scalar
    write (the loop counter and the φ-merge name included) lands outside `T`, and
    every array operand and word slot of an array access lies in `T`. -/
def towerOK (T : String → Prop) : LowCT → Prop
  | .RBlock b => towerOK T b
  | .RSeq c₁ c₂ => towerOK T c₁ ∧ towerOK T c₂
  | .RLetU64Zero n b => ¬ T n ∧ towerOK T b
  | .RScalarSet n _ => ¬ T n
  | .RScalarSetExpr x _ => ¬ T x
  | .RFor x _ b => ¬ T x ∧ towerOK T b
  | .RIfNz _ t e => towerOK T t ∧ towerOK T e
  | .RArrLoad dst src _ => T dst.locVar ∧ T src.locVar
  | .RArrStore arr _ src => T arr.locVar ∧ T src.locVar
  | _ => True

/-- Every index variable of an array access is bound when the access happens,
    given entry-bound set `B`; threaded like `readsOK`. -/
def idxOK (B : String → Prop) : LowCT → Prop
  | .RBlock b => idxOK B b
  | .RSeq c₁ c₂ => idxOK B c₁ ∧ idxOK (afterB B c₁) c₂
  | .RLetU64Zero n b => idxOK (fun y => B y ∨ y = n) b
  | .RFor x _ b => idxOK (fun y => B y ∨ y = x) b
  | .RArrLoad _ _ idxVar => B idxVar
  | .RArrStore _ idxVar _ => B idxVar
  | _ => True

/-- Under `towerOK`, the bound set stays outside `T` along `afterB`. -/
theorem afterB_disj : ∀ (c : LowCT) (B T : String → Prop), towerOK T c →
    (∀ y, B y → ¬ T y) → ∀ y, afterB B c y → ¬ T y := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => intro B T h hd; exact ih₂ _ T h.2 (ih₁ B T h.1 hd)
  | RBlock b ih => intro B T h hd; exact ih B T h hd
  | RLetU64Zero n b ih =>
      intro B T h hd
      exact ih _ T h.2 (fun y hy => by
        rcases hy with hy | rfl
        · exact hd y hy
        · exact h.1)
  | RScalarSet n _ =>
      intro B T hn hd y hy
      rcases hy with hy | rfl
      · exact hd y hy
      · exact hn
  | RScalarSetExpr x _ =>
      intro B T hx hd y hy
      rcases hy with hy | rfl
      · exact hd y hy
      · exact hx
  | _ => intro B T _ hd y hy; exact hd y hy

/-- The straight-line word-array fragment: the `IsCoveredAdeqS` arms and the
    dynamic-index word-array load and store on non-temp names, the `TU64` word slot
    and the `TArr k TU64` or `TBytes (8 * m)` array given by their tower types. -/
inductive IsCoveredAdeqArrS : LowCT → Prop
  | rSkip : IsCoveredAdeqArrS .RSkip
  | rBlock {body : LowCT} : IsCoveredAdeqArrS body → IsCoveredAdeqArrS (.RBlock body)
  | rSeq {c₁ c₂ : LowCT} : IsCoveredAdeqArrS c₁ → IsCoveredAdeqArrS c₂ →
      IsCoveredAdeqArrS (.RSeq c₁ c₂)
  | rLetU64Zero {name : String} {body : LowCT} : IsCoveredAdeqArrS body →
      IsCoveredAdeqArrS (.RLetU64Zero name body)
  | rScalarSet (name : String) {n : Nat} (hn : n < 2 ^ 64) :
      IsCoveredAdeqArrS (.RScalarSet name n)
  | rScalarSetExpr (x : String) (e : SExpr) (hclean : srcClean e)
      (hir : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → e.inRange σ) :
      IsCoveredAdeqArrS (.RScalarSetExpr x e)
  | rArrLoad (d s idxVar : String) (k : Nat) (hd : ¬ isTmpName d) (hs : ¬ isTmpName s)
      (hi : ¬ isTmpName idxVar) :
      IsCoveredAdeqArrS (.RArrLoad ⟨d, .TU64⟩ ⟨s, .TArr k .TU64⟩ idxVar)
  | rArrStore (a idxVar s : String) (k : Nat) (ha : ¬ isTmpName a) (hs : ¬ isTmpName s)
      (hi : ¬ isTmpName idxVar) :
      IsCoveredAdeqArrS (.RArrStore ⟨a, .TArr k .TU64⟩ idxVar ⟨s, .TU64⟩)
  | rArrLoadBytes (d s idxVar : String) (m : Nat) (hd : ¬ isTmpName d) (hs : ¬ isTmpName s)
      (hi : ¬ isTmpName idxVar) :
      IsCoveredAdeqArrS (.RArrLoad ⟨d, .TU64⟩ ⟨s, .TBytes (8 * m)⟩ idxVar)
  | rArrStoreBytes (a idxVar s : String) (m : Nat) (ha : ¬ isTmpName a) (hs : ¬ isTmpName s)
      (hi : ¬ isTmpName idxVar) :
      IsCoveredAdeqArrS (.RArrStore ⟨a, .TBytes (8 * m)⟩ idxVar ⟨s, .TU64⟩)

/-- The control-extended word-array fragment: `IsCoveredAdeq` over
    `IsCoveredAdeqArrS`. -/
inductive IsCoveredAdeqArr : LowCT → Prop
  | ofStraight {c : LowCT} : IsCoveredAdeqArrS c → IsCoveredAdeqArr c
  | rFor {x : String} {N : Nat} {body : LowCT} (hN : N ≤ 2 ^ 64) :
      IsCoveredAdeqArr body → IsCoveredAdeqArr (.RFor x N body)
  | rIfNz (name mergeName : String) (tv ev : Nat) (hname : ¬ isTmpName name)
      (htv : tv < 2 ^ 64) (hev : ev < 2 ^ 64) :
      IsCoveredAdeqArr (.RIfNz name (.RScalarSet mergeName tv) (.RScalarSet mergeName ev))

theorem IsCoveredAdeqS.toArrS {c : LowCT} (h : IsCoveredAdeqS c) : IsCoveredAdeqArrS c := by
  induction h with
  | rSkip => exact .rSkip
  | rBlock _ ih => exact .rBlock ih
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rLetU64Zero _ ih => exact .rLetU64Zero ih
  | rScalarSet name hn => exact .rScalarSet name hn
  | rScalarSetExpr x e hclean hir => exact .rScalarSetExpr x e hclean hir

theorem IsCoveredAdeq.toArr {c : LowCT} (h : IsCoveredAdeq c) : IsCoveredAdeqArr c := by
  induction h with
  | ofStraight hs => exact .ofStraight hs.toArrS
  | rFor hN _ ih => exact .rFor hN ih
  | rIfNz name mergeName tv ev hname htv hev => exact .rIfNz name mergeName tv ev hname htv hev

theorem IsCoveredAdeqArrS.toIsCoveredS {c : LowCT} (h : IsCoveredAdeqArrS c) : IsCoveredS c := by
  induction h with
  | rSkip => exact .rSkip
  | rBlock _ ih => exact .rBlock ih
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rLetU64Zero _ ih => exact .rLetU64Zero ih
  | rScalarSet name hn => exact .rScalarSet name _
  | rScalarSetExpr x e hclean _ => exact .rScalarSetExpr x e hclean
  | rArrLoad d s idxVar k _ _ _ => exact .rArrLoad _ _ _
  | rArrStore a idxVar s k _ _ _ => exact .rArrStore _ _ _
  | rArrLoadBytes d s idxVar m _ _ _ => exact .rArrLoad _ _ _
  | rArrStoreBytes a idxVar s m _ _ _ => exact .rArrStore _ _ _

theorem IsCoveredAdeqArr.toIsCoveredSCtl {c : LowCT} (h : IsCoveredAdeqArr c) :
    IsCoveredSCtl c := by
  induction h with
  | ofStraight hs => exact .ofStraight hs.toIsCoveredS
  | rFor _ _ ih => exact .rFor ih
  | rIfNz name mergeName tv ev _ _ _ =>
      exact .rIfNz (.ofStraight (.rScalarSet _ _)) (.ofStraight (.rScalarSet _ _))

/-! ### The tower-heap frame lemmas -/

/-- A scalar write outside `T`, over an `OnlyTmpBelow` companion env, preserves
    `TowerWordsOn`: the tower heap is unchanged and no `T`-name is written. -/
theorem towerWordsOn_updScalar {rs : RustState} {env env2 : SEnvScalar} {T : String → Prop}
    {cnt : Nat} (h : TowerWordsOn rs env T) (hotb : OnlyTmpBelow env env2 cnt)
    (x : String) (hx : ¬ T x) (w : BitVec 64) (v : Nat) :
    TowerWordsOn (rsSetScalar rs x v) (env2.upd x (t := .sword 64) w) T := by
  intro y hy hnt
  have hyx : y ≠ x := fun hyx => hx (hyx ▸ hy)
  simp only [SEnvScalar.upd, if_neg hyx, rsSetScalar]
  rw [hotb y (Or.inl hnt)]; exact h y hy hnt

/-- A located lookup is the tower binding at the located type. -/
theorem rsTower_eq_of_locatedLookup {rs : RustState} {loc : Located} {v : RustVal loc.locDst}
    (h : locatedLookup rs loc = some v) : rs.rsTower loc.locVar = some ⟨loc.locDst, v⟩ := by
  simp only [locatedLookup] at h
  split at h
  · rename_i t v' hrt
    split at h
    · rename_i ht
      subst ht
      cases h
      exact hrt
    · cases h
  · cases h

/-- `TowerWordsOn` gives the env binding of a `T`-name whose tower slot is known. -/
theorem towerWordsOn_bind {rs : RustState} {env : SEnvScalar} {T : String → Prop}
    (h : TowerWordsOn rs env T) {x : String} (hx : T x) (hnt : ¬ isTmpName x)
    {p : (t : TowerType) × RustVal t} (hp : rs.rsTower x = some p) :
    env x = some (encodeTowerWords p) := by
  rw [h x hx hnt, hp]; rfl

/-! ### Straight-line agreement with arrays -/

/-- The straight-line half of the word-array simulation: on `IsCoveredAdeqArrS`, a
    `RustExec` run whose `arrLoad` / `arrStore` oracles read and write one word is
    tracked by a defined `semScalar` run whose output env is `EnvBoundOn` the write
    set `afterB B c` and `TowerWordsOn` the tower names `T`, given the entry
    reflections, the disjointness of `B` and `T`, and the scopings `readsOK`,
    `idxOK` and `towerOK`. -/
theorem agreeArrS {N : Nat} {leafSpec : LeafSpec} (hload : ArrLoadWord leafSpec)
    (hstore : ArrStoreWord leafSpec) {c : LowCT} (h : IsCoveredAdeqArrS c) :
    ∀ {rs rs' : RustState} {env : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec c rs rs' → EnvBoundOn rs env B → TowerWordsOn rs env T →
      (∀ y, B y → ¬ T y) → ScalarInRange rs → readsOK B c → idxOK B c → towerOK T c →
      ∃ env', semScalar c env = some env' ∧ EnvBoundOn rs' env' (afterB B c) ∧
        TowerWordsOn rs' env' T ∧ ScalarInRange rs' := by
  induction h with
  | rSkip =>
      intro rs rs' env B T hexec henv htw _ hir _ _ _
      cases hexec; exact ⟨env, rfl, henv, htw, hir⟩
  | rBlock _ ih =>
      intro rs rs' env B T hexec henv htw hdisj hir hreads hidx htok
      cases hexec with | block _ _ _ hb =>
        simp only [semScalar]; exact ih hb henv htw hdisj hir hreads hidx htok
  | rSeq _ _ ih₁ ih₂ =>
      intro rs rs' env B T hexec henv htw hdisj hir hreads hidx htok
      obtain ⟨hr1, hr2⟩ := hreads
      obtain ⟨hi1, hi2⟩ := hidx
      obtain ⟨ht1, ht2⟩ := htok
      cases hexec with | seq _ _ _ _ _ h1 h2 =>
        obtain ⟨e1, hs1, he1, hw1, hi1'⟩ := ih₁ h1 henv htw hdisj hir hr1 hi1 ht1
        obtain ⟨e2, hs2, he2, hw2, hi2'⟩ :=
          ih₂ h2 he1 hw1 (afterB_disj _ B T ht1 hdisj) hi1' hr2 hi2 ht2
        exact ⟨e2, by simp only [semScalar, hs1]; exact hs2, he2, hw2, hi2'⟩
  | rLetU64Zero _ ih =>
      intro rs rs' env B T hexec henv htw hdisj hir hreads hidx htok
      cases hexec with | letU64Zero _ _ _ _ hbody =>
        simp only [semScalar]
        refine ih hbody (by simpa using envBoundOn_upd henv _ 0)
          (towerWordsOn_updScalar htw (onlyTmpBelow_refl env 0) _ htok.1 _ 0) ?_
          (scalarInRange_upd hir _ (by positivity)) hreads hidx htok.2
        intro y hy
        rcases hy with hy | rfl
        · exact hdisj y hy
        · exact htok.1
  | rScalarSet name hn =>
      intro rs rs' env B T hexec henv htw _ hir _ _ htok
      cases hexec
      exact ⟨_, rfl, envBoundOn_upd henv name _,
        towerWordsOn_updScalar htw (onlyTmpBelow_refl env 0) name htok _ _,
        scalarInRange_upd hir name hn⟩
  | rScalarSetExpr x e hclean hir_e =>
      intro rs rs' env B T hexec henv htw _ hir hreads _ htok
      cases hexec
      rw [SExpr.evalState_eq_eval rs e (limbFree_of_srcClean e hclean)]
      have hvb : varsBoundIn B e := hreads
      obtain ⟨env2, nm, cnt', hsem2, _, hotb2, _, _⟩ :=
        semLowerSExpr_ok' rs B e env 0 henv hvb hclean
      have hval : SExpr.evalBV (envReader env) e = BitVec.ofNat 64 (SExpr.eval rs.rsScalar e) := by
        rw [evalBV_congr_on B (envReader env) (SExpr.liftEnv rs.rsScalar) e
              (fun s hs hns => by rw [envReader_of_envBoundOn henv s hs hns]; rfl) hvb hclean]
        exact sexprTransfer rs.rsScalar e (hir_e rs.rsScalar hir)
      refine ⟨env2.upd x (t := .sword 64) (BitVec.ofNat 64 (SExpr.eval rs.rsScalar e)),
        by simp only [semScalar, hsem2]; rw [hval], ?_, ?_, ?_⟩
      · exact envBoundOn_updExpr henv hotb2 x _
      · exact towerWordsOn_updScalar htw hotb2 x htok _ _
      · exact scalarInRange_upd hir x (SExpr.eval_lt_of_inRange _ _ (hir_e rs.rsScalar hir))
  | rArrLoad d s idxVar k hd hs hi =>
      intro rs rs' env B T hexec henv htw hdisj hir _ hidx htok
      have hTd : T d := htok.1
      have hTs : T s := htok.2
      have hBi : B idxVar := hidx
      cases hexec with
      | arrLoad _ _ _ _ idx oldV srcV hidxv hold hsrc =>
        have hsrcT : rs.rsTower s = some ⟨.TArr k .TU64, srcV⟩ := rsTower_eq_of_locatedLookup hsrc
        have henvs : env s = some ⟨encodeTy (.TArr k .TU64), arrWords k srcV⟩ :=
          towerWordsOn_bind htw hTs hs hsrcT
        have henvi : env idxVar = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar idxVar)⟩ :=
          henv idxVar hBi hi
        have hidxn : (BitVec.ofNat 64 (rs.rsScalar idxVar)).toNat = idx := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir idxVar), hidxv]
        refine ⟨env.upd d (t := .sword 64) (memGetDyn (arrWords k srcV) idx), ?_, ?_, ?_, hir⟩
        · rw [← hidxn]; simp only [semScalar, Located.locDst, henvs, henvi]; rfl
        · intro y hy hnt
          have hyd : y ≠ d := fun hyd => hdisj y hy (hyd ▸ hTd)
          simp only [SEnvScalar.upd, if_neg hyd, locatedUpdate, rsSetTower]
          exact henv y hy hnt
        · intro y hy hnt
          by_cases hyd : y = d
          · subst hyd
            simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
              Located.locDst, encodeTowerWords_TU64]
            rw [hload.1]
          · simp only [SEnvScalar.upd, if_neg hyd, locatedUpdate]
            rw [rsSetTower_other rs _ y _ (Ne.symm hyd)]
            exact htw y hy hnt
  | rArrStore a idxVar s k ha hs hi =>
      intro rs rs' env B T hexec henv htw hdisj hir _ hidx htok
      have hTa : T a := htok.1
      have hTs : T s := htok.2
      have hBi : B idxVar := hidx
      cases hexec with
      | arrStore _ _ _ _ idx oldV srcV hidxv hold hsrc =>
        have holdT : rs.rsTower a = some ⟨.TArr k .TU64, oldV⟩ := rsTower_eq_of_locatedLookup hold
        have hsrcT : rs.rsTower s = some ⟨.TU64, srcV⟩ := rsTower_eq_of_locatedLookup hsrc
        have henva : env a = some ⟨encodeTy (.TArr k .TU64), arrWords k oldV⟩ :=
          towerWordsOn_bind htw hTa ha holdT
        have henvs : env s = some ⟨.sword 64, cryptoTyOfRustVal .TU64 srcV⟩ :=
          towerWordsOn_bind htw hTs hs hsrcT
        have henvi : env idxVar = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar idxVar)⟩ :=
          henv idxVar hBi hi
        have hidxn : (BitVec.ofNat 64 (rs.rsScalar idxVar)).toNat = idx := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir idxVar), hidxv]
        refine ⟨env.upd a (t := encodeTy (.TArr k .TU64))
          (memSetDyn (arrWords k oldV) idx (cryptoTyOfRustVal .TU64 srcV)), ?_, ?_, ?_, hir⟩
        · rw [← hidxn]; simp only [semScalar, Located.locDst, henva, henvs, henvi]
          exact dif_pos rfl
        · intro y hy hnt
          have hya : y ≠ a := fun hya => hdisj y hy (hya ▸ hTa)
          simp only [SEnvScalar.upd, if_neg hya, locatedUpdate, rsSetTower]
          exact henv y hy hnt
        · intro y hy hnt
          by_cases hya : y = a
          · subst hya
            simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
              Located.locDst, encodeTowerWords_TArr]
            rw [hstore.1]
          · simp only [SEnvScalar.upd, if_neg hya, locatedUpdate]
            rw [rsSetTower_other rs _ y _ (Ne.symm hya)]
            exact htw y hy hnt
  | rArrLoadBytes d s idxVar m hd hs hi =>
      intro rs rs' env B T hexec henv htw hdisj hir _ hidx htok
      have hTd : T d := htok.1
      have hTs : T s := htok.2
      have hBi : B idxVar := hidx
      cases hexec with
      | arrLoad _ _ _ _ idx oldV srcV hidxv hold hsrc =>
        have hsrcT : rs.rsTower s = some ⟨.TBytes (8 * m), srcV⟩ :=
          rsTower_eq_of_locatedLookup hsrc
        have henvs : env s = some ⟨encodeTy (.TBytes (8 * m)), bytesWords (8 * m) srcV⟩ :=
          towerWordsOn_bind htw hTs hs hsrcT
        have henvi : env idxVar = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar idxVar)⟩ :=
          henv idxVar hBi hi
        have hidxn : (BitVec.ofNat 64 (rs.rsScalar idxVar)).toNat = idx := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir idxVar), hidxv]
        refine ⟨env.upd d (t := .sword 64) (memGetDyn (bytesWords (8 * m) srcV) idx), ?_, ?_, ?_,
          hir⟩
        · rw [← hidxn]; simp only [semScalar, Located.locDst, henvs, henvi]; rfl
        · intro y hy hnt
          have hyd : y ≠ d := fun hyd => hdisj y hy (hyd ▸ hTd)
          simp only [SEnvScalar.upd, if_neg hyd, locatedUpdate, rsSetTower]
          exact henv y hy hnt
        · intro y hy hnt
          by_cases hyd : y = d
          · subst hyd
            simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
              Located.locDst, encodeTowerWords_TU64]
            rw [hload.2]
          · simp only [SEnvScalar.upd, if_neg hyd, locatedUpdate]
            rw [rsSetTower_other rs _ y _ (Ne.symm hyd)]
            exact htw y hy hnt
  | rArrStoreBytes a idxVar s m ha hs hi =>
      intro rs rs' env B T hexec henv htw hdisj hir _ hidx htok
      have hTa : T a := htok.1
      have hTs : T s := htok.2
      have hBi : B idxVar := hidx
      cases hexec with
      | arrStore _ _ _ _ idx oldV srcV hidxv hold hsrc =>
        have holdT : rs.rsTower a = some ⟨.TBytes (8 * m), oldV⟩ :=
          rsTower_eq_of_locatedLookup hold
        have hsrcT : rs.rsTower s = some ⟨.TU64, srcV⟩ := rsTower_eq_of_locatedLookup hsrc
        have henva : env a = some ⟨encodeTy (.TBytes (8 * m)), bytesWords (8 * m) oldV⟩ :=
          towerWordsOn_bind htw hTa ha holdT
        have henvs : env s = some ⟨.sword 64, cryptoTyOfRustVal .TU64 srcV⟩ :=
          towerWordsOn_bind htw hTs hs hsrcT
        have henvi : env idxVar = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar idxVar)⟩ :=
          henv idxVar hBi hi
        have hidxn : (BitVec.ofNat 64 (rs.rsScalar idxVar)).toNat = idx := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir idxVar), hidxv]
        refine ⟨env.upd a (t := encodeTy (.TBytes (8 * m)))
          (memSetDyn (bytesWords (8 * m) oldV) idx (cryptoTyOfRustVal .TU64 srcV)), ?_, ?_, ?_,
          hir⟩
        · rw [← hidxn]; simp only [semScalar, Located.locDst, henva, henvs, henvi]
          exact dif_pos rfl
        · intro y hy hnt
          have hya : y ≠ a := fun hya => hdisj y hy (hya ▸ hTa)
          simp only [SEnvScalar.upd, if_neg hya, locatedUpdate, rsSetTower]
          exact henv y hy hnt
        · intro y hy hnt
          by_cases hya : y = a
          · subst hya
            simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
              Located.locDst, encodeTowerWords_TBytes]
            rw [hstore.2]
          · simp only [SEnvScalar.upd, if_neg hya, locatedUpdate]
            rw [rsSetTower_other rs _ y _ (Ne.symm hya)]
            exact htw y hy hnt

/-! ### Counted-loop agreement with arrays -/

/-- The counted `RFor` loop over a word-array body, by `Nat`-induction on the trip
    count: `agreeFor` with the tower reflection `TowerWordsOn rs env T` carried as
    a second loop invariant (the counter is outside `T`). -/
theorem agreeArrFor {N : Nat} {leafSpec : LeafSpec} {x : String} {body : LowCT}
    (ihBody : ∀ {rs rs' : RustState} {env : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec body rs rs' → EnvBoundOn rs env B → TowerWordsOn rs env T →
      (∀ y, B y → ¬ T y) → ScalarInRange rs → readsOK B body → idxOK B body → towerOK T body →
      ∃ env', semScalar body env = some env' ∧ EnvBoundOn rs' env' (afterB B body) ∧
        TowerWordsOn rs' env' T ∧ ScalarInRange rs') :
    ∀ (M : Nat), M ≤ 2 ^ 64 → ∀ {rs rs' : RustState} {env : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec (.RFor x M body) rs rs' → EnvBoundOn rs env B → TowerWordsOn rs env T →
      (∀ y, B y → ¬ T y) → ScalarInRange rs → readsOK B (.RFor x M body) →
      idxOK B (.RFor x M body) → towerOK T (.RFor x M body) →
      ∃ env', semScalar (.RFor x M body) env = some env' ∧ EnvBoundOn rs' env' B ∧
        TowerWordsOn rs' env' T ∧ ScalarInRange rs' := by
  intro M
  induction M with
  | zero =>
      intro _ rs rs' env B T hexec henv htw _ hir _ _ _
      cases hexec
      exact ⟨env, rfl, henv, htw, hir⟩
  | succ n ihN =>
      intro hN rs rs' env B T hexec henv htw hdisj hir hreads hidx htok
      cases hexec with | forSucc _ _ _ _ _ _ hFor hBody =>
        obtain ⟨envPre, hsPre, hePre, hwPre, hiPre⟩ :=
          ihN (by omega) hFor henv htw hdisj hir hreads hidx htok
        have hbodyReads : readsOK (fun y => B y ∨ y = x) body := hreads
        have hbodyIdx : idxOK (fun y => B y ∨ y = x) body := hidx
        have hdisj' : ∀ y, (B y ∨ y = x) → ¬ T y := by
          intro y hy
          rcases hy with hy | rfl
          · exact hdisj y hy
          · exact htok.1
        obtain ⟨env', hs', he', hw', hi'⟩ :=
          ihBody hBody (envBoundOn_upd hePre x n)
            (towerWordsOn_updScalar hwPre (onlyTmpBelow_refl envPre 0) x htok.1 _ n) hdisj'
            (scalarInRange_upd hiPre x (by omega)) hbodyReads hbodyIdx htok.2
        have hsPre' : semRForD (fun e => semScalar body e) x n env = some envPre := hsPre
        refine ⟨env', by simp only [semScalar, semRForD, hsPre']; exact hs', ?_, hw', hi'⟩
        exact envBoundOn_mono he' (fun y hy => le_afterB body _ y (Or.inl hy))

/-! ### The command-level simulation with arrays -/

/-- **`rustExec_semScalar_agree_arr` (reading-B value adequacy with word arrays).**
    `rustExec_semScalar_agree_scoped` on `IsCoveredAdeqArr`: a `RustExec` run whose
    `arrLoad` / `arrStore` oracles read and write one word (`ArrLoadWord`,
    `ArrStoreWord`) is tracked by a defined `semScalar` run whose output env is
    `EnvBoundOn` the write set `afterB B c` and `TowerWordsOn` the tower names `T`,
    given entry `EnvBoundOn rs env B`, `TowerWordsOn rs env T`, the disjointness of
    `B` and `T`, `ScalarInRange`, and the scopings `readsOK B c`, `idxOK B c` and
    `towerOK T c`. -/
theorem rustExec_semScalar_agree_arr {N : Nat} {leafSpec : LeafSpec}
    (hload : ArrLoadWord leafSpec) (hstore : ArrStoreWord leafSpec) {c : LowCT}
    (h : IsCoveredAdeqArr c) :
    ∀ {rs rs' : RustState} {env : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec c rs rs' → EnvBoundOn rs env B → TowerWordsOn rs env T →
      (∀ y, B y → ¬ T y) → ScalarInRange rs → readsOK B c → idxOK B c → towerOK T c →
      ∃ env', semScalar c env = some env' ∧ EnvBoundOn rs' env' (afterB B c) ∧
        TowerWordsOn rs' env' T ∧ ScalarInRange rs' := by
  induction h with
  | ofStraight hs => exact agreeArrS hload hstore hs
  | rFor hN _ ih => exact agreeArrFor ih _ hN
  | rIfNz name mergeName tv ev hname htv hev =>
      intro rs rs' env B T hexec henv htw _ hir hreads _ htok
      have hbname : B name := hreads
      have hTm : ¬ T mergeName := htok.1
      have hcond : env name = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar name)⟩ :=
        henv name hbname hname
      cases hexec with
      | ifTrue _ _ _ _ _ v hveq hvne hct =>
          cases hct
          have hne0 : ¬ (BitVec.ofNat 64 (rs.rsScalar name) = 0#64) := fun hc =>
            hvne (hveq ▸ (ofNat_eq_zero_iff (hir name)).mp hc)
          refine ⟨env.upd mergeName (t := .sword 64) (BitVec.ofNat 64 tv), ?_,
            envBoundOn_mono (envBoundOn_upd henv mergeName tv) (fun y hy => Or.inl hy),
            towerWordsOn_updScalar htw (onlyTmpBelow_refl env 0) mergeName hTm _ _,
            scalarInRange_upd hir mergeName htv⟩
          simp only [semScalar, hcond, asSingleScalarSet, phiSelect, if_true, if_neg hne0]
      | ifFalse _ _ _ _ _ hveq hcf =>
          have heq0 : BitVec.ofNat 64 (rs.rsScalar name) = 0#64 :=
            (ofNat_eq_zero_iff (hir name)).mpr hveq
          clear hveq
          cases hcf
          refine ⟨env.upd mergeName (t := .sword 64) (BitVec.ofNat 64 ev), ?_,
            envBoundOn_mono (envBoundOn_upd henv mergeName ev) (fun y hy => Or.inl hy),
            towerWordsOn_updScalar htw (onlyTmpBelow_refl env 0) mergeName hTm _ _,
            scalarInRange_upd hir mergeName hev⟩
          simp only [semScalar, hcond, asSingleScalarSet, phiSelect, if_true, if_pos heq0]

/-! ## The word-slot agreement

`rustExec_semScalar_agree_arrW` is `rustExec_semScalar_agree_arr` with a loaded word
allowed to feed an `RScalarSetExpr` whose value is stored back. The two models name
a `TU64` word differently. `semScalar` and the front keep one namespace: the word a
load binds is a `.sword 64` env slot, and an `SVar` reads it. `RustExec` keeps two:
a load writes the tower slot `rsTower`, `SVar` reads the scalar slot `rsScalar`, and
the tower word is read by `SLimb x 0` and written by `RLimbStoreExpr ⟨x, TU64⟩ 0 e`.
`towerSpellC TW c` is the `RustExec` spelling of the front program `c` at the
word-name set `TW`: it rewrites every `SVar x` with `x ∈ TW` to `SLimb x 0` and
every `RScalarSetExpr x e` with `x ∈ TW` to `RLimbStoreExpr ⟨x, TU64⟩ 0 e`; it is
the identity on a program with no word-name reads or writes. The agreement theorem
relates a `RustExec` run of `towerSpellC TW c` to the `semScalar` run of `c`.

`TowerU64On rs TW` says each word name is tower-bound at `TU64`, and `LimbStoreWord`
says the `limbStore` oracle writes the word it is given at limb `0` of a `TU64`
slot. The scopings are `afterBW` (the scalar bound set, word-slot writes excluded),
`readsOKW` (reads, index reads included, resolved in the scalar set or in `TW`) and
`towerOKW` (the name-kind discipline against `T` and its word subset `TW`). -/

/-- The value of `wordOfBytes8 b` as the `ofNat` image of the little-endian number
    of its eight bytes. -/
theorem ofNat_bytes_eq_wordOfBytes8 (b : Fin 8 → BitVec 8) :
    BitVec.ofNat 64 ((b 0).toNat + (b 1).toNat * 2 ^ 8 + (b 2).toNat * 2 ^ 16 +
      (b 3).toNat * 2 ^ 24 + (b 4).toNat * 2 ^ 32 + (b 5).toNat * 2 ^ 40 +
      (b 6).toNat * 2 ^ 48 + (b 7).toNat * 2 ^ 56) = wordOfBytes8 b := by
  simp only [wordOfBytes8]
  rw [show ∀ x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8,
      x0.zeroExtend 64 ||| x1.zeroExtend 64 <<< 8 ||| x2.zeroExtend 64 <<< 16 |||
        x3.zeroExtend 64 <<< 24 ||| x4.zeroExtend 64 <<< 32 ||| x5.zeroExtend 64 <<< 40 |||
        x6.zeroExtend 64 <<< 48 ||| x7.zeroExtend 64 <<< 56
      = x0.zeroExtend 64 + x1.zeroExtend 64 <<< 8 + x2.zeroExtend 64 <<< 16 +
        x3.zeroExtend 64 <<< 24 + x4.zeroExtend 64 <<< 32 + x5.zeroExtend 64 <<< 40 +
        x6.zeroExtend 64 <<< 48 + x7.zeroExtend 64 <<< 56
      from fun _ _ _ _ _ _ _ _ => by bv_decide]
  bv_omega

/-- Limb `0` of a `TU64` tower value is its word: the `ofNat` image of
    `towerLimb v 0` is `cryptoTyOfRustVal .TU64 v`. -/
theorem towerLimb_zero_TU64 (v : RustVal .TU64) :
    BitVec.ofNat 64 (towerLimb v 0) = cryptoTyOfRustVal .TU64 v := by
  simp only [towerLimb, rustValByte, cryptoTyOfRustVal, TowerType.storageBytes]
  simp only [Nat.zero_mul, Nat.zero_add]
  simp (config := {decide := true}) only [dif_pos]
  exact ofNat_bytes_eq_wordOfBytes8 _

/-- The word-typedness of the word names `TW`: each is bound in the tower heap at
    `TU64`. -/
def TowerU64On (rs : RustState) (TW : String → Prop) : Prop :=
  ∀ x : String, TW x → ∃ v : RustVal .TU64, rs.rsTower x = some ⟨.TU64, v⟩

theorem towerU64On_setScalar {rs : RustState} {TW : String → Prop} (h : TowerU64On rs TW)
    (x : String) (v : Nat) : TowerU64On (rsSetScalar rs x v) TW := h

theorem towerU64On_setTower_TU64 {rs : RustState} {TW : String → Prop} (h : TowerU64On rs TW)
    (x : String) (v : RustVal .TU64) : TowerU64On (rsSetTower rs x ⟨.TU64, v⟩) TW := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; exact ⟨v, rsSetTower_same _ _ _⟩
  · rw [rsSetTower_other _ _ _ _ (Ne.symm hyx)]; exact h y hy

theorem towerU64On_setTower_other {rs : RustState} {TW : String → Prop} (h : TowerU64On rs TW)
    {x : String} (hx : ¬ TW x) (p : Σ t : TowerType, RustVal t) :
    TowerU64On (rsSetTower rs x p) TW := by
  intro y hy
  have hyx : y ≠ x := fun hyx => hx (hyx ▸ hy)
  rw [rsSetTower_other _ _ _ _ (Ne.symm hyx)]; exact h y hy

/-- The `limbStore` oracle writes the word: storing `w` at limb `0` of a `TU64` slot
    yields the value whose word is `w`. -/
def LimbStoreWord (leafSpec : LeafSpec) : Prop :=
  ∀ (x : String) (oldV : RustVal .TU64) (w : BitVec 64),
    cryptoTyOfRustVal .TU64 (leafSpec.limbStore ⟨x, .TU64⟩ oldV 0 w) = w

/-! ### The `RustExec` spelling of a front program -/

/-- The `RustExec` spelling of a scalar expression at the word-name set `TW`: a read
    `SVar x` with `x ∈ TW` is the tower-word read `SLimb x 0`; the clean binary arms
    are mapped structurally; every other node is unchanged. -/
def towerSpell (TW : String → Prop) [DecidablePred TW] : SExpr → SExpr
  | .SVar x => if TW x then .SLimb x 0 else .SVar x
  | .SAdd a b => .SAdd (towerSpell TW a) (towerSpell TW b)
  | .SSub a b => .SSub (towerSpell TW a) (towerSpell TW b)
  | .SMul a b => .SMul (towerSpell TW a) (towerSpell TW b)
  | .SAnd a b => .SAnd (towerSpell TW a) (towerSpell TW b)
  | .SXor a b => .SXor (towerSpell TW a) (towerSpell TW b)
  | .SShl a b => .SShl (towerSpell TW a) (towerSpell TW b)
  | .SShr a b => .SShr (towerSpell TW a) (towerSpell TW b)
  | .SMulHiU a b => .SMulHiU (towerSpell TW a) (towerSpell TW b)
  | e => e

/-- The `RustExec` spelling of a front program at the word-name set `TW`: an
    `RScalarSetExpr x e` with `x ∈ TW` is the tower-word write
    `RLimbStoreExpr ⟨x, TU64⟩ 0 (towerSpell TW e)`, with `x ∉ TW` it is
    `RScalarSetExpr x (towerSpell TW e)`; the control arms are mapped structurally;
    every other command is unchanged. -/
def towerSpellC (TW : String → Prop) [DecidablePred TW] : LowCT → LowCT
  | .RBlock b => .RBlock (towerSpellC TW b)
  | .RSeq c₁ c₂ => .RSeq (towerSpellC TW c₁) (towerSpellC TW c₂)
  | .RLetU64Zero n b => .RLetU64Zero n (towerSpellC TW b)
  | .RFor x n b => .RFor x n (towerSpellC TW b)
  | .RIfNz n t e => .RIfNz n (towerSpellC TW t) (towerSpellC TW e)
  | .RScalarSetExpr x e =>
      if TW x then .RLimbStoreExpr ⟨x, .TU64⟩ 0 (towerSpell TW e)
      else .RScalarSetExpr x (towerSpell TW e)
  | c => c

/-- The scalar reader of a spelled expression: a word name reads limb `0` of its
    tower slot, every other name its scalar slot. -/
def spellReader (TW : String → Prop) [DecidablePred TW] (rs : RustState) : String → Nat :=
  fun y => if TW y then rsTowerLimb rs y 0 else rs.rsScalar y

theorem spellReader_lt {TW : String → Prop} [DecidablePred TW] {rs : RustState}
    (hir : ScalarInRange rs) (y : String) : spellReader TW rs y < 2 ^ 64 := by
  unfold spellReader
  split
  · exact rsTowerLimb_lt rs y 0
  · exact hir y

/-- The tower-aware value of the spelled expression is the scalar value of the front
    expression under `spellReader`. -/
theorem evalState_towerSpell (TW : String → Prop) [DecidablePred TW] (rs : RustState) :
    ∀ e : SExpr, srcClean e →
      (towerSpell TW e).evalState rs = e.eval (spellReader TW rs) := by
  intro e
  induction e with
  | SVar x =>
      intro _
      by_cases hx : TW x
      · simp only [towerSpell, if_pos hx, SExpr.evalState, SExpr.eval, spellReader]
      · simp only [towerSpell, if_neg hx, SExpr.evalState, SExpr.eval, spellReader]
  | SLit n => intro _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro hcl
      simp only [towerSpell, SExpr.evalState, SExpr.eval, iha hcl.1, ihb hcl.2]
  | SLt a b _ _ => intro hcl; exact hcl.elim
  | SAsr a b _ _ => intro hcl; exact hcl.elim
  | SMulS a b _ _ => intro hcl; exact hcl.elim
  | SMulHiS a b _ _ => intro hcl; exact hcl.elim
  | SLimb v i => intro hcl; exact hcl.elim

/-! ### The scopings with word slots -/

/-- The scalar bound set after `c` from entry set `B`: `afterB` with the word-slot
    writes (an `RScalarSetExpr` into `TW`) excluded. -/
def afterBW (TW B : String → Prop) : LowCT → (String → Prop)
  | .RBlock b => afterBW TW B b
  | .RSeq c₁ c₂ => afterBW TW (afterBW TW B c₁) c₂
  | .RLetU64Zero n b => afterBW TW (fun y => B y ∨ y = n) b
  | .RScalarSet n _ => fun y => B y ∨ y = n
  | .RScalarSetExpr x _ => fun y => B y ∨ (y = x ∧ ¬ TW x)
  | _ => B

/-- Every free read of `c` is resolved when it happens, given the entry scalar set
    `B` and the word names `TW`: an expression read in `B ∪ TW`, an index read in
    `B`, threaded along `afterBW`. -/
def readsOKW (TW B : String → Prop) : LowCT → Prop
  | .RBlock b => readsOKW TW B b
  | .RSeq c₁ c₂ => readsOKW TW B c₁ ∧ readsOKW TW (afterBW TW B c₁) c₂
  | .RLetU64Zero n b => readsOKW TW (fun y => B y ∨ y = n) b
  | .RScalarSetExpr _ e => varsBoundIn (fun y => B y ∨ TW y) e
  | .RFor x _ b => readsOKW TW (fun y => B y ∨ y = x) b
  | .RIfNz name _ _ => B name
  | .RArrLoad _ _ idxVar => B idxVar
  | .RArrStore _ idxVar _ => B idxVar
  | _ => True

/-- The name-kind discipline of `c` against the tower set `T` and its word subset
    `TW`: the loop counter, the φ-merge name, an `RLetU64Zero` and an `RScalarSet`
    write outside `T`; an `RScalarSetExpr` writes outside `T` or a word name; a load
    lands in a word name and reads an array in `T`; a store writes an array in `T`
    that is not a word name and reads a word slot in `T`. -/
def towerOKW (T TW : String → Prop) : LowCT → Prop
  | .RBlock b => towerOKW T TW b
  | .RSeq c₁ c₂ => towerOKW T TW c₁ ∧ towerOKW T TW c₂
  | .RLetU64Zero n b => ¬ T n ∧ towerOKW T TW b
  | .RScalarSet n _ => ¬ T n
  | .RScalarSetExpr x _ => ¬ T x ∨ TW x
  | .RFor x _ b => ¬ T x ∧ towerOKW T TW b
  | .RIfNz _ t e => towerOKW T TW t ∧ towerOKW T TW e
  | .RArrLoad dst src _ => TW dst.locVar ∧ T src.locVar
  | .RArrStore arr _ src => T arr.locVar ∧ ¬ TW arr.locVar ∧ T src.locVar
  | _ => True

/-- Every entry-bound name stays bound along `afterBW`. -/
theorem le_afterBW (TW : String → Prop) : ∀ (c : LowCT) (D : String → Prop) (y : String),
    D y → afterBW TW D c y := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => exact fun D y hy => ih₂ _ y (ih₁ D y hy)
  | RBlock b ih => exact fun D y hy => ih D y hy
  | RLetU64Zero n b ih => exact fun D y hy => ih _ y (Or.inl hy)
  | RScalarSet _ _ => exact fun _ _ hy => Or.inl hy
  | RScalarSetExpr _ _ => exact fun _ _ hy => Or.inl hy
  | _ => exact fun D y hy => hy

/-- Under `towerOKW`, the scalar bound set stays outside `T` along `afterBW`. -/
theorem afterBW_disj : ∀ (c : LowCT) (B T TW : String → Prop), towerOKW T TW c →
    (∀ y, B y → ¬ T y) → ∀ y, afterBW TW B c y → ¬ T y := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => intro B T TW h hd; exact ih₂ _ T TW h.2 (ih₁ B T TW h.1 hd)
  | RBlock b ih => intro B T TW h hd; exact ih B T TW h hd
  | RLetU64Zero n b ih =>
      intro B T TW h hd
      exact ih _ T TW h.2 (fun y hy => by
        rcases hy with hy | rfl
        · exact hd y hy
        · exact h.1)
  | RScalarSet n _ =>
      intro B T TW hn hd y hy
      rcases hy with hy | rfl
      · exact hd y hy
      · exact hn
  | RScalarSetExpr x _ =>
      intro B T TW hx hd y hy
      rcases hy with hy | ⟨rfl, hnw⟩
      · exact hd y hy
      · exact hx.resolve_right hnw
  | _ => intro B T TW _ hd y hy; exact hd y hy

/-! ### The expression lowering on a readable set -/

/-- Every non-temp name in `R` is bound at `.sword 64` in `env`. -/
def ReadableOn (env : SEnvScalar) (R : String → Prop) : Prop :=
  ∀ x : String, R x → ¬ isTmpName x → (envReadU64 env x).isSome

theorem readableOn_onlyTmp {env env2 : SEnvScalar} {R : String → Prop} {cnt : Nat}
    (h : ReadableOn env R) (hotb : OnlyTmpBelow env env2 cnt) : ReadableOn env2 R := by
  intro y hy hnt
  rw [readU64_stable hotb (Or.inl hnt)]; exact h y hy hnt

/-- `semLowerSExpr_ok'` with the leaf condition `ReadableOn env R` in place of
    `EnvBoundOn rs env B`: the fold succeeds on any `srcClean` expression whose
    leaves are readable. -/
theorem semLowerSExpr_ok_readable (R : String → Prop) :
    ∀ (e : SExpr) (env : SEnvScalar) (cnt : Nat),
      ReadableOn env R → varsBoundIn R e → srcClean e →
      ∃ (env2 : SEnvScalar) (nm : String) (cnt' : Nat),
        semLowerSExpr env cnt e = some (env2, nm, cnt') ∧ cnt ≤ cnt' ∧
        OnlyTmpBelow env env2 cnt ∧ ResultOK nm cnt' ∧ (envReadU64 env2 nm).isSome := by
  intro e
  induction e with
  | SVar x =>
      intro env cnt hR hvb hcl
      have hx : ¬ isTmpName x := hcl
      have hbx : R x := hvb
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hR x hbx hx)
      refine ⟨env, x, cnt, ?_, le_refl _, onlyTmpBelow_refl env cnt, Or.inl hx, ?_⟩
      · simp only [semLowerSExpr, hw]
      · rw [hw]; rfl
  | SLit n =>
      intro env cnt _ _ _
      refine ⟨env.upd (TranslateDialectDirectArms.tmpName cnt) (t := .sword 64) (BitVec.ofNat 64 n),
        TranslateDialectDirectArms.tmpName cnt, cnt + 1, rfl, Nat.le_succ _,
        onlyTmpBelow_upd (onlyTmpBelow_refl env cnt) (le_refl _),
        Or.inr ⟨cnt, Nat.lt_succ_self _, rfl⟩, ?_⟩
      rw [envReadU64_upd_self]; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro env cnt hR hvb hcl
      obtain ⟨sa, sb⟩ := hcl
      obtain ⟨va, vb⟩ := hvb
      obtain ⟨env1, na, c1, hsemA, hleA, hotbA, hrokA, hreadA⟩ := iha env cnt hR va sa
      have hR1 : ReadableOn env1 R := readableOn_onlyTmp hR hotbA
      obtain ⟨env2, nb, c2, hsemB, hleB, hotbB, hrokB, hreadB⟩ := ihb env1 c1 hR1 vb sb
      have hna2 : (envReadU64 env2 na).isSome := by
        rw [readU64_stable hotbB hrokA]; exact hreadA
      simp only [semLowerSExpr, hsemA, hsemB]
      exact binNode_ok env env2 na nb cnt c2 _ (le_trans hleA hleB)
        (onlyTmpBelow_trans hotbA hotbB hleA) hna2 hreadB
  | SLt a b _ _ => intro _ _ _ _ hcl; exact hcl.elim
  | SAsr a b _ _ => intro _ _ _ _ hcl; exact hcl.elim
  | SMulS a b _ _ => intro _ _ _ _ hcl; exact hcl.elim
  | SMulHiS a b _ _ => intro _ _ _ _ hcl; exact hcl.elim
  | SLimb v i => intro _ _ _ _ hcl; exact hcl.elim

/-- The word binding of a word name: under `TowerWordsOn` and
    `TowerU64On`, a non-temp word name is bound at `.sword 64` to the word of its
    `TU64` tower value. -/
theorem wordBind_of_towerU64 {rs : RustState} {env : SEnvScalar} {T TW : String → Prop}
    (htw : TowerWordsOn rs env T) (hu : TowerU64On rs TW)
    (hTW : ∀ y, TW y → T y) {x : String} (hx : TW x) (hnt : ¬ isTmpName x) :
    ∃ v : RustVal .TU64, rs.rsTower x = some ⟨.TU64, v⟩ ∧
      env x = some ⟨.sword 64, cryptoTyOfRustVal .TU64 v⟩ := by
  obtain ⟨v, hv⟩ := hu x hx
  exact ⟨v, hv, towerWordsOn_bind htw (hTW x hx) hnt hv⟩

/-- The scalar set and the word names are jointly readable under the two
    reflections. -/
theorem readableOn_of_reflections {rs : RustState} {env : SEnvScalar} {B T TW : String → Prop}
    (henv : EnvBoundOn rs env B) (htw : TowerWordsOn rs env T)
    (hu : TowerU64On rs TW) (hTW : ∀ y, TW y → T y) :
    ReadableOn env (fun y => B y ∨ TW y) := by
  intro y hy hnt
  rcases hy with hy | hy
  · rw [Option.isSome_iff_exists]
    exact ⟨BitVec.ofNat 64 (rs.rsScalar y), by simp only [envReadU64, henv y hy hnt]⟩
  · obtain ⟨v, _, hb⟩ := wordBind_of_towerU64 htw hu hTW hy hnt
    rw [Option.isSome_iff_exists]
    exact ⟨cryptoTyOfRustVal .TU64 v, by simp only [envReadU64, hb]; rfl⟩

/-- The env reader agrees with the lifted `spellReader` on the scalar set and the
    word names. -/
theorem envReader_eq_spellReader {rs : RustState} {env : SEnvScalar} {B T TW : String → Prop}
    [DecidablePred TW] (henv : EnvBoundOn rs env B) (htw : TowerWordsOn rs env T)
    (hu : TowerU64On rs TW) (hdisj : ∀ y, B y → ¬ T y) (hTW : ∀ y, TW y → T y) :
    ∀ s, (B s ∨ TW s) → ¬ isTmpName s →
      envReader env s = SExpr.liftEnv (spellReader TW rs) s := by
  intro s hs hns
  rcases hs with hs | hs
  · have hnw : ¬ TW s := fun hw => hdisj s hs (hTW s hw)
    rw [envReader_of_envBoundOn henv s hs hns]
    simp only [SExpr.liftEnv, spellReader, if_neg hnw]
  · obtain ⟨v, hv, hb⟩ := wordBind_of_towerU64 htw hu hTW hs hns
    simp only [envReader, hb, SExpr.liftEnv, spellReader, if_pos hs, rsTowerLimb, hv]
    exact (towerLimb_zero_TU64 v).symm

/-! ### Straight-line agreement with word slots -/

/-- The straight-line half of the word-slot simulation: on `IsCoveredAdeqArrS`, a
    `RustExec` run of the spelling `towerSpellC TW c` under one-word array oracles
    and a word-writing `limbStore` oracle is tracked by a defined `semScalar` run of
    `c` whose output env is `EnvBoundOn` the scalar set `afterBW TW B c` and
    `TowerWordsOn` the tower names `T`, with the word names `TW`
    still `TU64`-typed, given the entry reflections, `TW ⊆ T`, the disjointness of
    `B` and `T`, and the scopings `readsOKW` and `towerOKW`. -/
theorem agreeArrWS {N : Nat} {leafSpec : LeafSpec} (hload : ArrLoadWord leafSpec)
    (hstore : ArrStoreWord leafSpec) (hlimb : LimbStoreWord leafSpec)
    (TW : String → Prop) [DecidablePred TW] {c : LowCT} (h : IsCoveredAdeqArrS c) :
    ∀ {rs rs' : RustState} {env : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec (towerSpellC TW c) rs rs' → EnvBoundOn rs env B →
      TowerWordsOn rs env T → TowerU64On rs TW →
      (∀ y, TW y → T y) → (∀ y, B y → ¬ T y) → ScalarInRange rs →
      readsOKW TW B c → towerOKW T TW c →
      ∃ env', semScalar c env = some env' ∧ EnvBoundOn rs' env' (afterBW TW B c) ∧
        TowerWordsOn rs' env' T ∧ TowerU64On rs' TW ∧ ScalarInRange rs' := by
  induction h with
  | rSkip =>
      intro rs rs' env B T hexec henv htw hu _ _ hir _ _
      cases hexec; exact ⟨env, rfl, henv, htw, hu, hir⟩
  | rBlock _ ih =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      simp only [towerSpellC] at hexec
      cases hexec with | block _ _ _ hb =>
        simp only [semScalar]; exact ih hb henv htw hu hTW hdisj hir hreads htok
  | rSeq _ _ ih₁ ih₂ =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      obtain ⟨hr1, hr2⟩ := hreads
      obtain ⟨ht1, ht2⟩ := htok
      simp only [towerSpellC] at hexec
      cases hexec with | seq _ _ _ _ _ h1 h2 =>
        obtain ⟨e1, hs1, he1, hw1, hu1, hi1⟩ := ih₁ h1 henv htw hu hTW hdisj hir hr1 ht1
        obtain ⟨e2, hs2, he2, hw2, hu2, hi2⟩ :=
          ih₂ h2 he1 hw1 hu1 hTW (afterBW_disj _ B T TW ht1 hdisj) hi1 hr2 ht2
        exact ⟨e2, by simp only [semScalar, hs1]; exact hs2, he2, hw2, hu2, hi2⟩
  | rLetU64Zero _ ih =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      simp only [towerSpellC] at hexec
      cases hexec with | letU64Zero _ _ _ _ hbody =>
        simp only [semScalar]
        refine ih hbody (by simpa using envBoundOn_upd henv _ 0)
          (towerWordsOn_updScalar htw (onlyTmpBelow_refl env 0) _ htok.1 _ 0)
          (towerU64On_setScalar hu _ _) hTW ?_
          (scalarInRange_upd hir _ (by positivity)) hreads htok.2
        intro y hy
        rcases hy with hy | rfl
        · exact hdisj y hy
        · exact htok.1
  | rScalarSet name hn =>
      intro rs rs' env B T hexec henv htw hu _ _ hir _ htok
      simp only [towerSpellC] at hexec
      cases hexec
      exact ⟨_, rfl, envBoundOn_upd henv name _,
        towerWordsOn_updScalar htw (onlyTmpBelow_refl env 0) name htok _ _,
        towerU64On_setScalar hu _ _, scalarInRange_upd hir name hn⟩
  | rScalarSetExpr x e hclean hir_e =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      have hvb : varsBoundIn (fun y => B y ∨ TW y) e := hreads
      obtain ⟨env2, nm, cnt', hsem2, _, hotb2, _, _⟩ :=
        semLowerSExpr_ok_readable _ e env 0 (readableOn_of_reflections henv htw hu hTW) hvb hclean
      have hirS : e.inRange (spellReader TW rs) := hir_e _ (spellReader_lt hir)
      have hval : SExpr.evalBV (envReader env) e
          = BitVec.ofNat 64 ((towerSpell TW e).evalState rs) := by
        rw [evalBV_congr_on (fun y => B y ∨ TW y) (envReader env)
              (SExpr.liftEnv (spellReader TW rs)) e
              (envReader_eq_spellReader henv htw hu hdisj hTW) hvb hclean,
          evalState_towerSpell TW rs e hclean]
        exact sexprTransfer _ e hirS
      have hlt : (towerSpell TW e).evalState rs < 2 ^ 64 := by
        rw [evalState_towerSpell TW rs e hclean]
        exact SExpr.eval_lt_of_inRange _ _ hirS
      by_cases hx : TW x
      · simp only [towerSpellC, if_pos hx] at hexec
        cases hexec with | limbStoreExpr _ _ _ _ oldV hold =>
          refine ⟨env2.upd x (t := .sword 64) (BitVec.ofNat 64 ((towerSpell TW e).evalState rs)),
            by simp only [semScalar, hsem2]; rw [hval], ?_, ?_, ?_, hir⟩
          · intro y hy hnt
            have hyx : y ≠ x := by
              rintro rfl
              rcases hy with hy | ⟨_, hnw⟩
              · exact hdisj y hy (hTW y hx)
              · exact hnw hx
            have hby : B y := by
              rcases hy with hy | ⟨_, hnw⟩
              · exact hy
              · exact absurd hx hnw
            simp only [SEnvScalar.upd, if_neg hyx, locatedUpdate, rsSetTower]
            rw [hotb2 y (Or.inl hnt)]; exact henv y hby hnt
          · intro y hy hnt
            by_cases hyx : y = x
            · subst hyx
              simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
                Located.locDst, encodeTowerWords_TU64]
              rw [hlimb]
            · simp only [SEnvScalar.upd, if_neg hyx, locatedUpdate]
              rw [rsSetTower_other rs _ y _ (Ne.symm hyx), hotb2 y (Or.inl hnt)]
              exact htw y hy hnt
          · exact towerU64On_setTower_TU64 hu x _
      · simp only [towerSpellC, if_neg hx] at hexec
        cases hexec
        have hTx : ¬ T x := htok.resolve_right hx
        refine ⟨env2.upd x (t := .sword 64) (BitVec.ofNat 64 ((towerSpell TW e).evalState rs)),
          by simp only [semScalar, hsem2]; rw [hval], ?_, ?_, ?_, ?_⟩
        · exact envBoundOn_mono (envBoundOn_updExpr henv hotb2 x _)
            (fun y hy => by
              rcases hy with hy | ⟨rfl, _⟩
              · exact Or.inl hy
              · exact Or.inr rfl)
        · exact towerWordsOn_updScalar htw hotb2 x hTx _ _
        · exact towerU64On_setScalar hu _ _
        · exact scalarInRange_upd hir x hlt
  | rArrLoad d s idxVar k hd hs hi =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      have hTd : T d := hTW d htok.1
      have hTs : T s := htok.2
      have hBi : B idxVar := hreads
      simp only [towerSpellC] at hexec
      cases hexec with
      | arrLoad _ _ _ _ idx oldV srcV hidxv hold hsrc =>
        have hsrcT : rs.rsTower s = some ⟨.TArr k .TU64, srcV⟩ := rsTower_eq_of_locatedLookup hsrc
        have henvs : env s = some ⟨encodeTy (.TArr k .TU64), arrWords k srcV⟩ :=
          towerWordsOn_bind htw hTs hs hsrcT
        have henvi : env idxVar = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar idxVar)⟩ :=
          henv idxVar hBi hi
        have hidxn : (BitVec.ofNat 64 (rs.rsScalar idxVar)).toNat = idx := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir idxVar), hidxv]
        refine ⟨env.upd d (t := .sword 64) (memGetDyn (arrWords k srcV) idx), ?_, ?_, ?_,
          towerU64On_setTower_TU64 hu d _, hir⟩
        · rw [← hidxn]; simp only [semScalar, Located.locDst, henvs, henvi]; rfl
        · intro y hy hnt
          have hyd : y ≠ d := fun hyd => hdisj y hy (hyd ▸ hTd)
          simp only [SEnvScalar.upd, if_neg hyd, locatedUpdate, rsSetTower]
          exact henv y hy hnt
        · intro y hy hnt
          by_cases hyd : y = d
          · subst hyd
            simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
              Located.locDst, encodeTowerWords_TU64]
            rw [hload.1]
          · simp only [SEnvScalar.upd, if_neg hyd, locatedUpdate]
            rw [rsSetTower_other rs _ y _ (Ne.symm hyd)]
            exact htw y hy hnt
  | rArrStore a idxVar s k ha hs hi =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      have hTa : T a := htok.1
      have hTs : T s := htok.2.2
      have hBi : B idxVar := hreads
      simp only [towerSpellC] at hexec
      cases hexec with
      | arrStore _ _ _ _ idx oldV srcV hidxv hold hsrc =>
        have holdT : rs.rsTower a = some ⟨.TArr k .TU64, oldV⟩ := rsTower_eq_of_locatedLookup hold
        have hsrcT : rs.rsTower s = some ⟨.TU64, srcV⟩ := rsTower_eq_of_locatedLookup hsrc
        have henva : env a = some ⟨encodeTy (.TArr k .TU64), arrWords k oldV⟩ :=
          towerWordsOn_bind htw hTa ha holdT
        have henvs : env s = some ⟨.sword 64, cryptoTyOfRustVal .TU64 srcV⟩ :=
          towerWordsOn_bind htw hTs hs hsrcT
        have henvi : env idxVar = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar idxVar)⟩ :=
          henv idxVar hBi hi
        have hidxn : (BitVec.ofNat 64 (rs.rsScalar idxVar)).toNat = idx := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir idxVar), hidxv]
        refine ⟨env.upd a (t := encodeTy (.TArr k .TU64))
          (memSetDyn (arrWords k oldV) idx (cryptoTyOfRustVal .TU64 srcV)), ?_, ?_, ?_,
          towerU64On_setTower_other hu htok.2.1 _, hir⟩
        · rw [← hidxn]; simp only [semScalar, Located.locDst, henva, henvs, henvi]
          exact dif_pos rfl
        · intro y hy hnt
          have hya : y ≠ a := fun hya => hdisj y hy (hya ▸ hTa)
          simp only [SEnvScalar.upd, if_neg hya, locatedUpdate, rsSetTower]
          exact henv y hy hnt
        · intro y hy hnt
          by_cases hya : y = a
          · subst hya
            simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
              Located.locDst, encodeTowerWords_TArr]
            rw [hstore.1]
          · simp only [SEnvScalar.upd, if_neg hya, locatedUpdate]
            rw [rsSetTower_other rs _ y _ (Ne.symm hya)]
            exact htw y hy hnt
  | rArrLoadBytes d s idxVar m hd hs hi =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      have hTd : T d := hTW d htok.1
      have hTs : T s := htok.2
      have hBi : B idxVar := hreads
      simp only [towerSpellC] at hexec
      cases hexec with
      | arrLoad _ _ _ _ idx oldV srcV hidxv hold hsrc =>
        have hsrcT : rs.rsTower s = some ⟨.TBytes (8 * m), srcV⟩ :=
          rsTower_eq_of_locatedLookup hsrc
        have henvs : env s = some ⟨encodeTy (.TBytes (8 * m)), bytesWords (8 * m) srcV⟩ :=
          towerWordsOn_bind htw hTs hs hsrcT
        have henvi : env idxVar = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar idxVar)⟩ :=
          henv idxVar hBi hi
        have hidxn : (BitVec.ofNat 64 (rs.rsScalar idxVar)).toNat = idx := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir idxVar), hidxv]
        refine ⟨env.upd d (t := .sword 64) (memGetDyn (bytesWords (8 * m) srcV) idx), ?_, ?_, ?_,
          towerU64On_setTower_TU64 hu d _, hir⟩
        · rw [← hidxn]; simp only [semScalar, Located.locDst, henvs, henvi]; rfl
        · intro y hy hnt
          have hyd : y ≠ d := fun hyd => hdisj y hy (hyd ▸ hTd)
          simp only [SEnvScalar.upd, if_neg hyd, locatedUpdate, rsSetTower]
          exact henv y hy hnt
        · intro y hy hnt
          by_cases hyd : y = d
          · subst hyd
            simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
              Located.locDst, encodeTowerWords_TU64]
            rw [hload.2]
          · simp only [SEnvScalar.upd, if_neg hyd, locatedUpdate]
            rw [rsSetTower_other rs _ y _ (Ne.symm hyd)]
            exact htw y hy hnt
  | rArrStoreBytes a idxVar s m ha hs hi =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      have hTa : T a := htok.1
      have hTs : T s := htok.2.2
      have hBi : B idxVar := hreads
      simp only [towerSpellC] at hexec
      cases hexec with
      | arrStore _ _ _ _ idx oldV srcV hidxv hold hsrc =>
        have holdT : rs.rsTower a = some ⟨.TBytes (8 * m), oldV⟩ :=
          rsTower_eq_of_locatedLookup hold
        have hsrcT : rs.rsTower s = some ⟨.TU64, srcV⟩ := rsTower_eq_of_locatedLookup hsrc
        have henva : env a = some ⟨encodeTy (.TBytes (8 * m)), bytesWords (8 * m) oldV⟩ :=
          towerWordsOn_bind htw hTa ha holdT
        have henvs : env s = some ⟨.sword 64, cryptoTyOfRustVal .TU64 srcV⟩ :=
          towerWordsOn_bind htw hTs hs hsrcT
        have henvi : env idxVar = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar idxVar)⟩ :=
          henv idxVar hBi hi
        have hidxn : (BitVec.ofNat 64 (rs.rsScalar idxVar)).toNat = idx := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir idxVar), hidxv]
        refine ⟨env.upd a (t := encodeTy (.TBytes (8 * m)))
          (memSetDyn (bytesWords (8 * m) oldV) idx (cryptoTyOfRustVal .TU64 srcV)), ?_, ?_, ?_,
          towerU64On_setTower_other hu htok.2.1 _, hir⟩
        · rw [← hidxn]; simp only [semScalar, Located.locDst, henva, henvs, henvi]
          exact dif_pos rfl
        · intro y hy hnt
          have hya : y ≠ a := fun hya => hdisj y hy (hya ▸ hTa)
          simp only [SEnvScalar.upd, if_neg hya, locatedUpdate, rsSetTower]
          exact henv y hy hnt
        · intro y hy hnt
          by_cases hya : y = a
          · subst hya
            simp only [SEnvScalar.upd, if_true, locatedUpdate, rsSetTower_same, Option.map_some,
              Located.locDst, encodeTowerWords_TBytes]
            rw [hstore.2]
          · simp only [SEnvScalar.upd, if_neg hya, locatedUpdate]
            rw [rsSetTower_other rs _ y _ (Ne.symm hya)]
            exact htw y hy hnt

/-! ### Counted-loop agreement with word slots -/

/-- The counted `RFor` loop over a word-slot body, by `Nat`-induction on the trip
    count: `agreeArrFor` with `TowerU64On` carried as a third loop invariant. -/
theorem agreeArrWFor {N : Nat} {leafSpec : LeafSpec} (TW : String → Prop) [DecidablePred TW]
    {x : String} {body : LowCT}
    (ihBody : ∀ {rs rs' : RustState} {env : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec (towerSpellC TW body) rs rs' → EnvBoundOn rs env B →
      TowerWordsOn rs env T → TowerU64On rs TW →
      (∀ y, TW y → T y) → (∀ y, B y → ¬ T y) → ScalarInRange rs →
      readsOKW TW B body → towerOKW T TW body →
      ∃ env', semScalar body env = some env' ∧ EnvBoundOn rs' env' (afterBW TW B body) ∧
        TowerWordsOn rs' env' T ∧ TowerU64On rs' TW ∧ ScalarInRange rs') :
    ∀ (M : Nat), M ≤ 2 ^ 64 → ∀ {rs rs' : RustState} {env : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec (.RFor x M (towerSpellC TW body)) rs rs' → EnvBoundOn rs env B →
      TowerWordsOn rs env T → TowerU64On rs TW →
      (∀ y, TW y → T y) → (∀ y, B y → ¬ T y) → ScalarInRange rs →
      readsOKW TW B (.RFor x M body) → towerOKW T TW (.RFor x M body) →
      ∃ env', semScalar (.RFor x M body) env = some env' ∧ EnvBoundOn rs' env' B ∧
        TowerWordsOn rs' env' T ∧ TowerU64On rs' TW ∧ ScalarInRange rs' := by
  intro M
  induction M with
  | zero =>
      intro _ rs rs' env B T hexec henv htw hu _ _ hir _ _
      cases hexec
      exact ⟨env, rfl, henv, htw, hu, hir⟩
  | succ n ihN =>
      intro hN rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      cases hexec with | forSucc _ _ _ _ _ _ hFor hBody =>
        obtain ⟨envPre, hsPre, hePre, hwPre, huPre, hiPre⟩ :=
          ihN (by omega) hFor henv htw hu hTW hdisj hir hreads htok
        have hbodyReads : readsOKW TW (fun y => B y ∨ y = x) body := hreads
        have hdisj' : ∀ y, (B y ∨ y = x) → ¬ T y := by
          intro y hy
          rcases hy with hy | rfl
          · exact hdisj y hy
          · exact htok.1
        obtain ⟨env', hs', he', hw', hu', hi'⟩ :=
          ihBody hBody (envBoundOn_upd hePre x n)
            (towerWordsOn_updScalar hwPre (onlyTmpBelow_refl envPre 0) x htok.1 _ n)
            (towerU64On_setScalar huPre _ _) hTW hdisj'
            (scalarInRange_upd hiPre x (by omega)) hbodyReads htok.2
        have hsPre' : semRForD (fun e => semScalar body e) x n env = some envPre := hsPre
        refine ⟨env', by simp only [semScalar, semRForD, hsPre']; exact hs', ?_, hw', hu', hi'⟩
        exact envBoundOn_mono he' (fun y hy => le_afterBW TW body _ y (Or.inl hy))

/-! ### The command-level simulation with word slots -/

/-- **`rustExec_semScalar_agree_arrW` (reading-B value adequacy with word slots).**
    `rustExec_semScalar_agree_arr` with the `RustExec` run taken over the spelling
    `towerSpellC TW c`: a run under one-word array oracles (`ArrLoadWord`,
    `ArrStoreWord`) and a word-writing `limbStore` oracle (`LimbStoreWord`) is
    tracked by a defined
    `semScalar` run of `c` whose output env is `EnvBoundOn` the scalar set
    `afterBW TW B c` and `TowerWordsOn` the tower names `T`, with
    the word names `TW` still `TU64`-typed, given entry `EnvBoundOn rs env B`,
    `TowerWordsOn rs env T`, `TowerU64On rs TW`, `TW ⊆ T`, the
    disjointness of `B` and `T`, `ScalarInRange`, and the scopings `readsOKW TW B c`
    and `towerOKW T TW c`. -/
theorem rustExec_semScalar_agree_arrW {N : Nat} {leafSpec : LeafSpec}
    (hload : ArrLoadWord leafSpec) (hstore : ArrStoreWord leafSpec)
    (hlimb : LimbStoreWord leafSpec) (TW : String → Prop) [DecidablePred TW] {c : LowCT}
    (h : IsCoveredAdeqArr c) :
    ∀ {rs rs' : RustState} {env : SEnvScalar} {B T : String → Prop},
      RustExec N leafSpec (towerSpellC TW c) rs rs' → EnvBoundOn rs env B →
      TowerWordsOn rs env T → TowerU64On rs TW →
      (∀ y, TW y → T y) → (∀ y, B y → ¬ T y) → ScalarInRange rs →
      readsOKW TW B c → towerOKW T TW c →
      ∃ env', semScalar c env = some env' ∧ EnvBoundOn rs' env' (afterBW TW B c) ∧
        TowerWordsOn rs' env' T ∧ TowerU64On rs' TW ∧ ScalarInRange rs' := by
  induction h with
  | ofStraight hs => exact agreeArrWS hload hstore hlimb TW hs
  | rFor hN _ ih =>
      intro rs rs' env B T hexec henv htw hu hTW hdisj hir hreads htok
      simp only [towerSpellC] at hexec
      exact agreeArrWFor TW ih _ hN hexec henv htw hu hTW hdisj hir hreads htok
  | rIfNz name mergeName tv ev hname htv hev =>
      intro rs rs' env B T hexec henv htw hu _ _ hir hreads htok
      have hbname : B name := hreads
      have hTm : ¬ T mergeName := htok.1
      have hcond : env name = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar name)⟩ :=
        henv name hbname hname
      simp only [towerSpellC] at hexec
      cases hexec with
      | ifTrue _ _ _ _ _ v hveq hvne hct =>
          cases hct
          have hne0 : ¬ (BitVec.ofNat 64 (rs.rsScalar name) = 0#64) := fun hc =>
            hvne (hveq ▸ (ofNat_eq_zero_iff (hir name)).mp hc)
          refine ⟨env.upd mergeName (t := .sword 64) (BitVec.ofNat 64 tv), ?_,
            envBoundOn_mono (envBoundOn_upd henv mergeName tv) (fun y hy => Or.inl hy),
            towerWordsOn_updScalar htw (onlyTmpBelow_refl env 0) mergeName hTm _ _,
            towerU64On_setScalar hu _ _, scalarInRange_upd hir mergeName htv⟩
          simp only [semScalar, hcond, asSingleScalarSet, phiSelect, if_true, if_neg hne0]
      | ifFalse _ _ _ _ _ hveq hcf =>
          have heq0 : BitVec.ofNat 64 (rs.rsScalar name) = 0#64 :=
            (ofNat_eq_zero_iff (hir name)).mpr hveq
          clear hveq
          cases hcf
          refine ⟨env.upd mergeName (t := .sword 64) (BitVec.ofNat 64 ev), ?_,
            envBoundOn_mono (envBoundOn_upd henv mergeName ev) (fun y hy => Or.inl hy),
            towerWordsOn_updScalar htw (onlyTmpBelow_refl env 0) mergeName hTm _ _,
            towerU64On_setScalar hu _ _, scalarInRange_upd hir mergeName hev⟩
          simp only [semScalar, hcond, asSingleScalarSet, phiSelect, if_true, if_pos heq0]

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
