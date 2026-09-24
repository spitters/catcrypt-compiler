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

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
