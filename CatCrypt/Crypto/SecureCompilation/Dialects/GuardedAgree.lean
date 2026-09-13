/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedUnroll
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted

/-!
# `RustExec` agrees with the guarded scalar semantics, and the emit leg

On the guarded fragment `IsCoveredSCtlGuarded`, a `RustExec` run (the `Nat`
model) is tracked by `semScalarGuarded` (the `BitVec` model of the guarded
conversion), under two side conditions:

* `readsG`: every read of the command is in the set of names written before it,
  where a conditional adds no name to that set;
* `InRangeG`: every expression the run evaluates is in `u64` range at the state
  it is evaluated in (no overflow, no saturating subtraction, shift amounts
  below 64).

The proof runs the conversion of a conditional in two modes. Under a flag slot
holding `1` (`ifConvert_taken`) the converted command tracks the `RustExec` run
of the branch; under a flag slot holding `0` (`ifConvert_skipped`) it leaves
every name of the bound list and every lower flag slot unchanged. A conditional
runs its taken branch in the first mode and the other branch in the second.

Composed with the totality judgment `TransTotal` of the front, the denotation
theorem of `translateDialectControl` and `semScalarToJasminCom_denote_eq`, this
gives `translateDialectGuardedIn_jasmin`: from an entry `VarMap`, valuation and
environment that bind a list `S` of input names consistently with the entry
state, the translation with bound list `S` and the jasmin lowering succeed, and
the jasmin program returning a slot in `S` or written outside every conditional
denotes the word of that slot's value at the end of the `RustExec` run.
`translateDialectGuarded_jasmin` is its instance at `S = []`, the empty `VarMap`
and the empty valuation: it covers only commands that read no input, and the
jasmin program it speaks about is a closed constant.

The Boolean tests `readsB`, `afterL` and `inRangeRunBL` are sound checks of the
scoping and in-range conditions on a concrete command and store: `true` implies
the condition, and `false` proves nothing.

## Main definitions

* `afterG`, `readsG`: the names written before a point, and the reads condition
* `InRangeG`: the in-range condition of a run
* `translateDialectGuardedIn`: the guarded translator from a bound input list
* `readsB`, `afterL`, `inRangeRunBL`: sound Boolean checks of the side conditions

## Main results

* `ifConvert_skipped`, `ifConvert_taken`: the two modes of the conversion
* `rustExec_semScalarGuarded_agree`: `RustExec` agrees with `semScalarGuarded`
* `ifConvert_transTotal`: the conversion is in the front's totality judgment
* `translateDialectGuardedIn_jasmin`: the compiled jasmin program, with inputs,
  denotes the value of the `RustExec` run
* `translateDialectGuarded_jasmin`: the same for a command reading no input,
  where the jasmin program is closed
* `readsB_sound`, `afterL_sound`, `inRangeRunB_sound`, `inRangeRunB_storeState`:
  soundness of the Boolean tests
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
  (EnvBoundOn ScalarInRange envReader_of_envBoundOn envBoundOn_updExpr scalarInRange_upd
    envBoundOn_mono)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded

/-! ## Scoping and the in-range condition -/

/-- The names bound after `c`, from the entry set `B`: scalar writes and
    `RLetU64Zero` add their slot; a conditional adds nothing. -/
def afterG (B : String → Prop) : LowCT → (String → Prop)
  | .RSeq a b => afterG (afterG B a) b
  | .RLetU64Zero x b => afterG (fun y => B y ∨ y = x) b
  | .RScalarSet x _ => fun y => B y ∨ y = x
  | .RScalarSetExpr x _ => fun y => B y ∨ y = x
  | _ => B

/-- Every read of `c` is in the bound set at the point of the read. -/
def readsG (B : String → Prop) : LowCT → Prop
  | .RSeq a b => readsG B a ∧ readsG (afterG B a) b
  | .RLetU64Zero x b => readsG (fun y => B y ∨ y = x) b
  | .RScalarSetExpr _ e => varsIn B e
  | .RIfNz g t e => B g ∧ readsG B t ∧ readsG B e
  | _ => True

/-- The in-range condition of a run: every expression the run of `c` from `rs`
    evaluates is in `u64` range at the state it is evaluated in. -/
def InRangeG (N : Nat) (leafSpec : LeafSpec) : LowCT → RustState → Prop
  | .RSeq a b, rs => InRangeG N leafSpec a rs ∧
      ∀ r1, RustExec N leafSpec a rs r1 → InRangeG N leafSpec b r1
  | .RLetU64Zero x b, rs => InRangeG N leafSpec b (rsSetScalar rs x 0)
  | .RScalarSetExpr _ e, rs => e.inRange rs.rsScalar
  | .RIfNz g t e, rs => (rs.rsScalar g ≠ 0 → InRangeG N leafSpec t rs) ∧
      (rs.rsScalar g = 0 → InRangeG N leafSpec e rs)
  | _, _ => True

theorem le_afterG : ∀ (c : LowCT) (B : String → Prop) (y : String), B y → afterG B c y := by
  intro c
  induction c with
  | RSeq a b iha ihb => exact fun B y hy => ihb _ y (iha B y hy)
  | RLetU64Zero x b ih => exact fun B y hy => ih _ y (Or.inl hy)
  | RScalarSet _ _ => exact fun _ _ hy => Or.inl hy
  | RScalarSetExpr _ _ => exact fun _ _ hy => Or.inl hy
  | _ => exact fun _ _ hy => hy

/-! ## Environment helpers -/

/-- The names of `S` are bound words in `env`. -/
def Bound (env : SEnvScalar) (S : List String) : Prop :=
  ∀ y ∈ S, (envReadU64 env y).isSome

/-- The names of `S` are source names. -/
def SrcList (S : List String) : Prop := ∀ y ∈ S, srcName y

/-- A word read of a non-temporary name. -/
def BndP (env : SEnvScalar) (s : String) : Prop := ¬ isTmpName s → (envReadU64 env s).isSome

theorem env_of_readU64 {env : SEnvScalar} {x : String} {w : BitVec 64}
    (h : envReadU64 env x = some w) : env x = some ⟨.sword 64, w⟩ := by
  unfold envReadU64 at h
  split at h
  · rename_i w' heq; cases h; exact heq
  · cases h

theorem readU64_of_env {env : SEnvScalar} {x : String} {w : BitVec 64}
    (h : env x = some ⟨.sword 64, w⟩) : envReadU64 env x = some w := by
  simp only [envReadU64, h]

theorem upd_ne {env : SEnvScalar} {x y : String} {w : BitVec 64} (h : y ≠ x) :
    (env.upd x (t := .sword 64) w) y = env y := by
  simp [SEnvScalar.upd, h]

theorem upd_self {env : SEnvScalar} {x : String} {w : BitVec 64} :
    (env.upd x (t := .sword 64) w) x = some ⟨.sword 64, w⟩ := by
  simp [SEnvScalar.upd]

theorem reader_eq_of_env {env env' : SEnvScalar} {y : String} (h : env' y = env y) :
    envReader env' y = envReader env y := by
  simp only [envReader, h]

theorem readU64_eq_of_env {env env' : SEnvScalar} {y : String} (h : env' y = env y) :
    envReadU64 env' y = envReadU64 env y := by
  simp only [envReadU64, h]

theorem varsIn_elimLt {P : String → Prop} :
    ∀ e : SExpr, varsIn P e → varsIn P (elimLt e) := by
  intro e
  induction e with
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro h; exact ⟨iha h.1, ihb h.2⟩
  | SLt a b iha ihb =>
      intro h
      have ha := iha h.1
      have hb := ihb h.2
      exact ⟨⟨⟨⟨hb, trivial⟩, ⟨⟨trivial, ha⟩, trivial⟩⟩,
        ⟨⟨hb, trivial⟩, ⟨⟨trivial, ha⟩, trivial⟩⟩⟩, trivial⟩
  | _ => intro h; exact h

/-- `semLowerSExpr` succeeds when every variable of a `srcClean` expression is a
    bound word, and it changes only lowering temporaries. -/
theorem semLowerSExpr_bound :
    ∀ (e : SExpr) (env : SEnvScalar) (cnt : Nat), srcClean e → varsIn (BndP env) e →
      ∃ (env2 : SEnvScalar) (nm : String) (cnt' : Nat),
        semLowerSExpr env cnt e = some (env2, nm, cnt') ∧ cnt ≤ cnt' ∧
        OnlyTmpBelow env env2 cnt ∧ ResultOK nm cnt' ∧ (envReadU64 env2 nm).isSome := by
  intro e
  induction e with
  | SVar x =>
      intro env cnt hcl hv
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hv hcl)
      refine ⟨env, x, cnt, ?_, le_refl _, onlyTmpBelow_refl env cnt, Or.inl hcl, ?_⟩
      · simp only [semLowerSExpr, hw]
      · rw [hw]; rfl
  | SLit n =>
      intro env cnt _ _
      refine ⟨env.upd (TranslateDialectDirectArms.tmpName cnt) (t := .sword 64)
          (BitVec.ofNat 64 n),
        TranslateDialectDirectArms.tmpName cnt, cnt + 1, rfl, Nat.le_succ _,
        onlyTmpBelow_upd (onlyTmpBelow_refl env cnt) (le_refl _),
        Or.inr ⟨cnt, Nat.lt_succ_self _, rfl⟩, ?_⟩
      rw [envReadU64_upd_self]; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro env cnt hcl hv
      obtain ⟨env1, na, c1, hsemA, hleA, hotbA, hrokA, hreadA⟩ := iha env cnt hcl.1 hv.1
      have hv1 : varsIn (BndP env1) b := varsIn_mono (fun s hs hnt => by
        rw [readU64_stable hotbA (Or.inl hnt)]; exact hs hnt) b hv.2
      obtain ⟨env2, nb, c2, hsemB, hleB, hotbB, hrokB, hreadB⟩ := ihb env1 c1 hcl.2 hv1
      have hna2 : (envReadU64 env2 na).isSome := by
        rw [readU64_stable hotbB hrokA]; exact hreadA
      simp only [semLowerSExpr, hsemA, hsemB]
      exact RustExecSemScalarBridge.binNode_ok env env2 na nb cnt c2 _ (le_trans hleA hleB)
        (onlyTmpBelow_trans hotbA hotbB hleA) hna2 hreadB
  | SLt a b _ _ => intro _ _ hcl; exact hcl.elim
  | SAsr a b _ _ => intro _ _ hcl; exact hcl.elim
  | SMulS a b _ _ => intro _ _ hcl; exact hcl.elim
  | SMulHiS a b _ _ => intro _ _ hcl; exact hcl.elim
  | SLimb v i => intro _ _ hcl; exact hcl.elim

theorem semScalar_setExpr {x : String} {e : SExpr} {env : SEnvScalar} (hcl : srcClean e)
    (hv : varsIn (BndP env) e) :
    ∃ env2 : SEnvScalar,
      semScalar (.RScalarSetExpr x e) env
        = some (env2.upd x (t := .sword 64) (e.evalBV (envReader env))) ∧
      OnlyTmpBelow env env2 0 := by
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ := semLowerSExpr_bound e env 0 hcl hv
  exact ⟨env2, by simp only [semScalar, hsem], hotb⟩

/-- The value flag `flag` holds: `1` without a flag. -/
def flagVal (flag : Option String) (env : SEnvScalar) : BitVec 64 :=
  match flag with
  | none => 1
  | some f => envReader env f

/-- The value `gWrite flag S x v` stores. -/
def gVal (flag : Option String) (S : List String) (x : String) (v : SExpr)
    (env : SEnvScalar) : BitVec 64 :=
  match flag with
  | none => v.evalBV (envReader env)
  | some f =>
      if x ∈ S then
        envReader env x + envReader env f * (v.evalBV (envReader env) - envReader env x)
      else envReader env f * v.evalBV (envReader env)

theorem semScalar_gWrite {flag : Option String} {S : List String} {x : String} {v : SExpr}
    {env : SEnvScalar} (hcl : srcClean v) (hv : varsIn (BndP env) v) (hx : ¬ isTmpName x)
    (hf : ∀ f, flag = some f → ¬ isTmpName f ∧ (envReadU64 env f).isSome)
    (hxS : x ∈ S → (envReadU64 env x).isSome) :
    ∃ env2 : SEnvScalar,
      semScalar (gWrite flag S x v) env
        = some (env2.upd x (t := .sword 64) (gVal flag S x v env)) ∧
      OnlyTmpBelow env env2 0 := by
  cases flag with
  | none => exact semScalar_setExpr hcl hv
  | some f =>
      obtain ⟨hft, hfb⟩ := hf f rfl
      by_cases hmem : x ∈ S
      · have h := semScalar_setExpr (x := x) (env := env)
          (e := .SAdd (.SVar x) (.SMul (.SVar f) (.SSub v (.SVar x))))
          ⟨hx, hft, hcl, hx⟩ ⟨fun _ => hxS hmem, fun _ => hfb, hv, fun _ => hxS hmem⟩
        simpa only [gWrite, gVal, if_pos hmem, SExpr.evalBV] using h
      · have h := semScalar_setExpr (x := x) (env := env)
          (e := .SMul (.SVar f) v) ⟨hft, hcl⟩ ⟨fun _ => hfb, hv⟩
        simpa only [gWrite, gVal, if_neg hmem, SExpr.evalBV] using h

theorem gVal_one {flag : Option String} {S : List String} {x : String} {v : SExpr}
    {env : SEnvScalar} (h1 : flagVal flag env = 1) :
    gVal flag S x v env = v.evalBV (envReader env) := by
  cases flag with
  | none => rfl
  | some f =>
      have ho1 : ∀ a : BitVec 64, (1 : BitVec 64) * a = a := fun a => by simp
      simp only [flagVal] at h1
      simp only [gVal, h1]
      split_ifs
      · rw [ho1, BitVec.add_comm, BitVec.sub_add_cancel]
      · rw [ho1]

theorem gVal_zero_mem {f : String} {S : List String} {x : String} {v : SExpr}
    {env : SEnvScalar} (h0 : envReader env f = 0) (hmem : x ∈ S) :
    gVal (some f) S x v env = envReader env x := by
  simp [gVal, h0, hmem]

/-! ## Static properties of the conversion -/

/-- The output list of the conversion consists of source names, contains the input
    list and the names written, and the flag index does not decrease. -/
theorem ifConvert_static {c : LowCT} (hc : IsCoveredSCtlGuarded c) :
    ∀ (flag : Option String) (S : List String) (k : Nat) (B : String → Prop),
      SrcList S → (∀ y, B y → y ∈ S) →
      SrcList (ifConvert flag S k c).2.1 ∧ (∀ y ∈ S, y ∈ (ifConvert flag S k c).2.1) ∧
      (∀ y, afterG B c y → y ∈ (ifConvert flag S k c).2.1) ∧
      k ≤ (ifConvert flag S k c).2.2 := by
  induction hc with
  | rSkip => intro _ S k B hS hB; exact ⟨hS, fun _ h => h, hB, le_refl _⟩
  | rSeq _ _ iha ihb =>
      intro flag S k B hS hB
      obtain ⟨hSa, hsubA, hBa, hka⟩ := iha flag S k B hS hB
      obtain ⟨hSb, hsubB, hBb, hkb⟩ := ihb flag _ _ (afterG B _) hSa hBa
      exact ⟨hSb, fun y hy => hsubB y (hsubA y hy), hBb, le_trans hka hkb⟩
  | @rLetU64Zero x _ hx _ ihb =>
      intro flag S k B hS hB
      have hS' : SrcList (x :: S) := by
        intro y hy; rcases List.mem_cons.mp hy with rfl | h; exact hx; exact hS y h
      obtain ⟨hSb, hsubB, hBb, hkb⟩ := ihb flag _ k (fun y => B y ∨ y = x) hS'
        (fun y hy => by rcases hy with h | rfl; exact List.mem_cons_of_mem _ (hB y h);
                                                 exact List.mem_cons_self)
      exact ⟨hSb, fun y hy => hsubB y (List.mem_cons_of_mem _ hy), hBb, hkb⟩
  | rScalarSet hx _ | rScalarSetExpr hx _ _ =>
      intro flag S k B hS hB
      refine ⟨?_, fun y hy => List.mem_cons_of_mem _ hy, ?_, le_refl _⟩
      · intro y hy; rcases List.mem_cons.mp hy with rfl | h; exact hx; exact hS y h
      · intro y hy; rcases hy with h | rfl; exact List.mem_cons_of_mem _ (hB y h)
        exact List.mem_cons_self
  | rIfNz hg _ _ iht ihe =>
      intro flag S k B hS hB
      obtain ⟨hSt, hsubT, _, hkt⟩ := iht (some (guardName k)) S (k + 2) B hS hB
      obtain ⟨hSe, hsubE, _, hke⟩ := ihe (some (guardName (k + 1))) _ _ B hSt
        (fun y hy => hsubT y (hB y hy))
      exact ⟨hSe, fun y hy => hsubE y (hsubT y hy), fun y hy => hsubE y (hsubT y (hB y hy)),
        by simp only [ifConvert]; omega⟩

/-! ## The flag computation of a conditional -/

theorem semScalar_seq (a b : LowCT) (env : SEnvScalar) :
    semScalar (.RSeq a b) env = (semScalar a env).bind (fun e => semScalar b e) := by
  simp only [semScalar]

theorem evalBV_andFlag (flag : Option String) (e : SExpr) (env : SEnvScalar) :
    (andFlag flag e).evalBV (envReader env) = flagVal flag env * e.evalBV (envReader env) := by
  cases flag with
  | none => simp [andFlag, flagVal]
  | some f => rfl

/-- The two flag writes of a converted conditional store `flag * (0 < g)` and
    `flag * (1 - (0 < g))` into `guardName k` and `guardName (k + 1)` and leave
    every other non-temporary name unchanged. -/
theorem semScalar_flags {flag : Option String} {g : String} {k : Nat} {env : SEnvScalar}
    (rest : LowCT) (hg : srcName g) (hgb : (envReadU64 env g).isSome)
    (hf : ∀ f, flag = some f → srcName f ∨ ∃ j, f = guardName j ∧ j < k)
    (hfb : ∀ f, flag = some f → (envReadU64 env f).isSome) :
    ∃ env3 : SEnvScalar,
      semScalar (.RSeq (.RScalarSetExpr (guardName k) (andFlag flag (nzExpr g)))
        (.RSeq (.RScalarSetExpr (guardName (k + 1))
          (andFlag flag (.SSub (.SLit 1) (nzExpr g)))) rest)) env = semScalar rest env3 ∧
      envReadU64 env3 (guardName k)
        = some (flagVal flag env * ltWord 0#64 (envReader env g)) ∧
      envReadU64 env3 (guardName (k + 1))
        = some (flagVal flag env * (1 - ltWord 0#64 (envReader env g))) ∧
      (∀ y, ¬ isTmpName y → y ≠ guardName k → y ≠ guardName (k + 1) → env3 y = env y) := by
  have hne : ∀ f, flag = some f → f ≠ guardName k ∧ f ≠ guardName (k + 1) ∧ ¬ isTmpName f := by
    intro f hfe
    rcases hf f hfe with hs | ⟨j, rfl, hj⟩
    · exact ⟨srcName_ne_guardName hs k, srcName_ne_guardName hs (k + 1), hs.1⟩
    · exact ⟨fun h => by have := guardName_injective h; omega,
        fun h => by have := guardName_injective h; omega, not_isTmpName_guardName j⟩
  have hk1 : guardName k ≠ guardName (k + 1) := fun h => by
    have := guardName_injective h; omega
  have hclF : srcClean (andFlag flag (nzExpr g)) :=
    srcClean_andFlag (fun f hfe => (hne f hfe).2.2) (srcClean_nzExpr hg.1)
  have hvF : ∀ e', varsIn (BndP e') (andFlag flag (nzExpr g)) ↔
      ((∀ f, flag = some f → BndP e' f) ∧ BndP e' g) := by
    intro e'
    cases flag with
    | none => simp [andFlag, nzExpr, ltExpr, carryExpr, varsIn]
    | some f => simp [andFlag, nzExpr, ltExpr, carryExpr, varsIn]
  obtain ⟨env2, hs1, hotb1⟩ := semScalar_setExpr (x := guardName k) hclF
    ((hvF env).mpr ⟨fun f hfe _ => hfb f hfe, fun _ => hgb⟩)
  set env1 := env2.upd (guardName k) (t := .sword 64)
    ((andFlag flag (nzExpr g)).evalBV (envReader env)) with henv1
  have hfr1 : ∀ y, ¬ isTmpName y → y ≠ guardName k → env1 y = env y := by
    intro y hy hyk
    rw [henv1, upd_ne hyk]; exact hotb1 y (Or.inl hy)
  have hg1 : env1 g = env g := hfr1 g hg.1 (srcName_ne_guardName hg k)
  have hclE : srcClean (andFlag flag (.SSub (.SLit 1) (nzExpr g))) :=
    srcClean_andFlag (fun f hfe => (hne f hfe).2.2)
      ⟨show (1 : Nat) < 2 ^ 64 by decide, srcClean_nzExpr hg.1⟩
  have hvE : varsIn (BndP env1) (andFlag flag (.SSub (.SLit 1) (nzExpr g))) := by
    have hgb1 : BndP env1 g := fun _ => by rw [readU64_eq_of_env hg1]; exact hgb
    have hfb1 : ∀ f, flag = some f → BndP env1 f := by
      intro f hfe _
      rw [readU64_eq_of_env (hfr1 f (hne f hfe).2.2 (hne f hfe).1)]; exact hfb f hfe
    cases flag with
    | none => simp [andFlag, nzExpr, ltExpr, carryExpr, varsIn, hgb1]
    | some f => simp [andFlag, nzExpr, ltExpr, carryExpr, varsIn, hgb1, hfb1 f rfl]
  obtain ⟨env4, hs2, hotb2⟩ := semScalar_setExpr (x := guardName (k + 1)) hclE hvE
  have hreadF : ∀ f, flag = some f → envReader env1 f = envReader env f := by
    intro f hfe
    exact reader_eq_of_env (hfr1 f (hne f hfe).2.2 (hne f hfe).1)
  have hflag1 : flagVal flag env1 = flagVal flag env := by
    cases flag with
    | none => rfl
    | some f => exact hreadF f rfl
  refine ⟨env4.upd (guardName (k + 1)) (t := .sword 64)
      ((andFlag flag (.SSub (.SLit 1) (nzExpr g))).evalBV (envReader env1)), ?_, ?_, ?_, ?_⟩
  · rw [semScalar_seq, hs1, Option.bind_some, semScalar_seq, hs2, Option.bind_some]
  · rw [readU64_eq_of_env (upd_ne hk1), readU64_eq_of_env (hotb2 _ (Or.inl
      (not_isTmpName_guardName k))), henv1, envReadU64_upd_self, evalBV_andFlag, nzExpr,
      evalBV_ltExpr]
    rfl
  · rw [envReadU64_upd_self, evalBV_andFlag, hflag1]
    simp only [SExpr.evalBV, nzExpr, evalBV_ltExpr, reader_eq_of_env hg1]
    rfl
  · intro y hy hyk hyk1
    rw [upd_ne hyk1, hotb2 y (Or.inl hy)]
    exact hfr1 y hy hyk

/-! ## The skipped branch -/

theorem gWrite_skipped {j : Nat} {S : List String} {x : String} {v : SExpr} {env : SEnvScalar}
    (hj : envReadU64 env (guardName j) = some 0) (hx : srcName x) (hcl : srcClean v)
    (hv : varsIn (BndP env) v) (hS : SrcList S) (hb : Bound env S) :
    ∃ env' : SEnvScalar, semScalar (gWrite (some (guardName j)) S x v) env = some env' ∧
      (∀ y ∈ S, env' y = env y) ∧ Bound env' (x :: S) ∧
      (∀ i, env' (guardName i) = env (guardName i)) := by
  obtain ⟨env2, hs, hotb⟩ := semScalar_gWrite (flag := some (guardName j)) (S := S) hcl hv hx.1
    (fun f hf => by cases hf; exact ⟨not_isTmpName_guardName j, by rw [hj]; rfl⟩)
    (fun hm => hb x hm)
  have h0 : envReader env (guardName j) = 0 := envReadU64_reader hj
  refine ⟨_, hs, ?_, ?_, ?_⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hb y hy)
      rw [upd_self, gVal_zero_mem h0 hy, envReadU64_reader hw, env_of_readU64 hw]
    · rw [upd_ne hyx]; exact hotb y (Or.inl (hS y hy).1)
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; rw [readU64_of_env upd_self]; rfl
    · rw [readU64_eq_of_env (upd_ne hyx), readU64_eq_of_env (hotb y (Or.inl (hS y
        (List.mem_of_ne_of_mem hyx hy)).1))]
      exact hb y (List.mem_of_ne_of_mem hyx hy)
  · intro i
    rw [upd_ne (fun h => srcName_ne_guardName hx i h.symm)]
    exact hotb _ (Or.inl (not_isTmpName_guardName i))

theorem srcList_cons {x : String} {S : List String} (hx : srcName x) (hS : SrcList S) :
    SrcList (x :: S) := by
  intro y hy; rcases List.mem_cons.mp hy with rfl | h; exact hx; exact hS y h

theorem sub_cons {B : String → Prop} {S : List String} (x : String) (hB : ∀ y, B y → y ∈ S) :
    ∀ y, (B y ∨ y = x) → y ∈ x :: S := by
  intro y hy
  rcases hy with h | rfl
  · exact List.mem_cons_of_mem _ (hB y h)
  · exact List.mem_cons_self

theorem bndP_of_sub {B : String → Prop} {S : List String} {env : SEnvScalar}
    (hB : ∀ y, B y → y ∈ S) (hb : Bound env S) : ∀ s, B s → BndP env s :=
  fun s hs _ => hb s (hB s hs)

/-- Under a flag slot holding `0`, the conversion leaves every name of `S` and every
    guard flag below `k` unchanged, and binds every name of the output list. -/
theorem ifConvert_skipped {c : LowCT} (hc : IsCoveredSCtlGuarded c) :
    ∀ (j : Nat) (S : List String) (k : Nat) (B : String → Prop) (env : SEnvScalar),
      j < k → envReadU64 env (guardName j) = some 0 →
      SrcList S → Bound env S → (∀ y, B y → y ∈ S) → readsG B c →
      ∃ env', semScalar (ifConvert (some (guardName j)) S k c).1 env = some env' ∧
        (∀ y ∈ S, env' y = env y) ∧ Bound env' (ifConvert (some (guardName j)) S k c).2.1 ∧
        (∀ i, i < k → env' (guardName i) = env (guardName i)) := by
  induction hc with
  | rSkip =>
      intro j S k B env _ _ _ hb _ _
      exact ⟨env, rfl, fun _ _ => rfl, hb, fun _ _ => rfl⟩
  | @rSeq a b ha _ iha ihb =>
      intro j S k B env hj hjv hS hb hB hr
      simp only [ifConvert]
      obtain ⟨env1, hs1, hpres1, hb1, hg1⟩ := iha j S k B env hj hjv hS hb hB hr.1
      obtain ⟨hSa, hsubA, hBa, hka⟩ := ifConvert_static ha (some (guardName j)) S k B hS hB
      obtain ⟨env2, hs2, hpres2, hb2, hg2⟩ := ihb j (ifConvert (some (guardName j)) S k a).2.1
        (ifConvert (some (guardName j)) S k a).2.2 (afterG B a) env1 (by omega)
        (by rw [readU64_eq_of_env (hg1 j hj)]; exact hjv) hSa hb1 hBa hr.2
      refine ⟨env2, by rw [semScalar_seq, hs1, Option.bind_some]; exact hs2,
        fun y hy => (hpres2 y (hsubA y hy)).trans (hpres1 y hy), hb2,
        fun i hi => (hg2 i (by omega)).trans (hg1 i hi)⟩
  | @rLetU64Zero x b hx _ ihb =>
      intro j S k B env hj hjv hS hb hB hr
      simp only [ifConvert]
      obtain ⟨env1, hs1, hpres1, hb1, hg1⟩ := gWrite_skipped (v := .SLit 0) hjv hx
        (show (0 : Nat) < 2 ^ 64 by decide) trivial hS hb
      obtain ⟨env2, hs2, hpres2, hb2, hg2⟩ := ihb j (x :: S) k (fun y => B y ∨ y = x) env1 hj
        (by rw [readU64_eq_of_env (hg1 j)]; exact hjv) (srcList_cons hx hS) hb1
        (sub_cons x hB) hr
      refine ⟨env2, by rw [semScalar_seq, hs1, Option.bind_some]; exact hs2,
        fun y hy => (hpres2 y (List.mem_cons_of_mem _ hy)).trans (hpres1 y hy), hb2,
        fun i hi => (hg2 i hi).trans (hg1 i)⟩
  | @rScalarSet x n hx hn =>
      intro j S k B env hj hjv hS hb hB hr
      obtain ⟨env1, hs1, hpres1, hb1, hg1⟩ :=
        gWrite_skipped (v := .SLit n) hjv hx hn trivial hS hb
      exact ⟨env1, hs1, hpres1, hb1, fun i _ => hg1 i⟩
  | @rScalarSetExpr x e hx he _ =>
      intro j S k B env hj hjv hS hb hB hr
      obtain ⟨env1, hs1, hpres1, hb1, hg1⟩ := gWrite_skipped (v := elimLt e) hjv hx
        (srcClean_elimLt e he) (varsIn_elimLt e (varsIn_mono (bndP_of_sub hB hb) e hr)) hS hb
      exact ⟨env1, hs1, hpres1, hb1, fun i _ => hg1 i⟩
  | @rIfNz g t e hg ht he iht ihe =>
      intro j S k B env hj hjv hS hb hB hr
      obtain ⟨hg', ht', he'⟩ := hr
      have hgS := hB g hg'
      simp only [ifConvert]
      obtain ⟨env3, hs3, hft, hfe, hfr3⟩ := semScalar_flags (flag := some (guardName j)) (k := k)
        (.RSeq (ifConvert (some (guardName k)) S (k + 2) t).1
          (ifConvert (some (guardName (k + 1))) (ifConvert (some (guardName k)) S (k + 2) t).2.1
            (ifConvert (some (guardName k)) S (k + 2) t).2.2 e).1)
        hg (hb g hgS) (fun f hf => by cases hf; exact Or.inr ⟨j, rfl, hj⟩)
        (fun f hf => by cases hf; rw [hjv]; rfl)
      have h0 : flagVal (some (guardName j)) env = 0 := envReadU64_reader hjv
      have hz : ∀ a : BitVec 64, (0 : BitVec 64) * a = 0 := fun a => by simp
      rw [h0, hz] at hft hfe
      have hpres3 : ∀ y ∈ S, env3 y = env y := fun y hy =>
        hfr3 y (hS y hy).1 (srcName_ne_guardName (hS y hy) k)
          (srcName_ne_guardName (hS y hy) (k + 1))
      have hb3 : Bound env3 S := fun y hy => by
        rw [readU64_eq_of_env (hpres3 y hy)]; exact hb y hy
      obtain ⟨hSt, hsubT, _, hkt⟩ := ifConvert_static ht (some (guardName k)) S (k + 2) B hS hB
      obtain ⟨envT, hsT, hpresT, hbT, hgT⟩ := iht k S (k + 2) B env3 (by omega) hft hS hb3 hB ht'
      have hfeT : envReadU64 envT (guardName (k + 1)) = some 0 := by
        rw [readU64_eq_of_env (hgT (k + 1) (by omega))]; exact hfe
      obtain ⟨envE, hsE, hpresE, hbE, hgE⟩ := ihe (k + 1)
        (ifConvert (some (guardName k)) S (k + 2) t).2.1
        (ifConvert (some (guardName k)) S (k + 2) t).2.2 B envT (by omega) hfeT hSt hbT
        (fun y hy => hsubT y (hB y hy)) he'
      refine ⟨envE, ?_, ?_, hbE, ?_⟩
      · rw [hs3, semScalar_seq, hsT, Option.bind_some]; exact hsE
      · intro y hy; rw [hpresE y (hsubT y hy), hpresT y hy, hpres3 y hy]
      · intro i hi
        rw [hgE i (by omega), hgT i (by omega)]
        exact hfr3 _ (not_isTmpName_guardName i)
          (fun h => by have := guardName_injective h; omega)
          (fun h => by have := guardName_injective h; omega)

/-! ## The taken branch -/

/-- The flag is absent, or it is a guard flag below `k` holding `1`. -/
def FlagOn (flag : Option String) (k : Nat) (env : SEnvScalar) : Prop :=
  ∀ f, flag = some f → ∃ j, f = guardName j ∧ j < k ∧ envReadU64 env f = some 1

theorem flagVal_of_flagOn {flag : Option String} {k : Nat} {env : SEnvScalar}
    (h : FlagOn flag k env) : flagVal flag env = 1 := by
  cases flag with
  | none => rfl
  | some f =>
      obtain ⟨j, rfl, _, h1⟩ := h f rfl
      exact envReadU64_reader h1

theorem flagOn_mono {flag : Option String} {k k' : Nat} {env env' : SEnvScalar}
    (h : FlagOn flag k env) (hk : k ≤ k')
    (hg : ∀ i, i < k → env' (guardName i) = env (guardName i)) : FlagOn flag k' env' := by
  intro f hfe
  obtain ⟨j, rfl, hj, h1⟩ := h f hfe
  exact ⟨j, rfl, by omega, by rw [readU64_eq_of_env (hg j hj)]; exact h1⟩

theorem write_facts {env env2 : SEnvScalar} {x : String} {S : List String} {w : BitVec 64}
    (hotb : OnlyTmpBelow env env2 0) (hx : srcName x) (hS : SrcList S) (hb : Bound env S) :
    Bound (env2.upd x (t := .sword 64) w) (x :: S) ∧
      (∀ i, (env2.upd x (t := .sword 64) w) (guardName i) = env (guardName i)) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; rw [readU64_of_env upd_self]; rfl
    · have hyS := List.mem_of_ne_of_mem hyx hy
      rw [readU64_eq_of_env (upd_ne hyx), readU64_eq_of_env (hotb y (Or.inl (hS y hyS).1))]
      exact hb y hyS
  · intro i
    rw [upd_ne (fun h => srcName_ne_guardName hx i h.symm)]
    exact hotb _ (Or.inl (not_isTmpName_guardName i))

theorem gWrite_taken {flag : Option String} {k : Nat} {S : List String} {x : String}
    {v : SExpr} {env : SEnvScalar} (hf : FlagOn flag k env) (hx : srcName x) (hcl : srcClean v)
    (hv : varsIn (BndP env) v) (hb : Bound env S) :
    ∃ env2 : SEnvScalar,
      semScalar (gWrite flag S x v) env
        = some (env2.upd x (t := .sword 64) (v.evalBV (envReader env))) ∧
      OnlyTmpBelow env env2 0 := by
  obtain ⟨env2, hs, hotb⟩ := semScalar_gWrite (flag := flag) (S := S) hcl hv hx.1
    (fun f hfe => by
      obtain ⟨j, rfl, _, h1⟩ := hf f hfe
      exact ⟨not_isTmpName_guardName j, by rw [h1]; rfl⟩)
    (fun hm => hb x hm)
  exact ⟨env2, by rw [hs, gVal_one (flagVal_of_flagOn hf)], hotb⟩

/-- Under the absent flag or a flag slot holding `1`, the conversion tracks a
    `RustExec` run: the output environment agrees with the output state on the
    names bound after the command. -/
theorem ifConvert_taken {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hc : IsCoveredSCtlGuarded c) :
    ∀ (flag : Option String) (S : List String) (k : Nat) (B : String → Prop)
      (rs rs' : RustState) (env : SEnvScalar),
      RustExec N leafSpec c rs rs' → InRangeG N leafSpec c rs → readsG B c →
      FlagOn flag k env → SrcList S → Bound env S → (∀ y, B y → y ∈ S) →
      EnvBoundOn rs env B → ScalarInRange rs →
      ∃ env', semScalar (ifConvert flag S k c).1 env = some env' ∧
        EnvBoundOn rs' env' (afterG B c) ∧ ScalarInRange rs' ∧
        Bound env' (ifConvert flag S k c).2.1 ∧
        (∀ i, i < k → env' (guardName i) = env (guardName i)) := by
  induction hc with
  | rSkip =>
      intro flag S k B rs rs' env hexec _ _ _ _ hb _ henv hir
      cases hexec
      exact ⟨env, rfl, henv, hir, hb, fun _ _ => rfl⟩
  | @rSeq a b ha _ iha ihb =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      cases hexec with
      | seq _ _ _ r1 _ h1 h2 =>
          simp only [ifConvert]
          obtain ⟨env1, hs1, henv1, hir1, hb1, hg1⟩ :=
            iha flag S k B rs r1 env h1 hIR.1 hr.1 hf hS hb hB henv hir
          obtain ⟨hSa, _, hBa, hka⟩ := ifConvert_static ha flag S k B hS hB
          obtain ⟨env2, hs2, henv2, hir2, hb2, hg2⟩ :=
            ihb flag (ifConvert flag S k a).2.1 (ifConvert flag S k a).2.2 (afterG B a) r1 rs'
              env1 h2 (hIR.2 r1 h1) hr.2 (flagOn_mono hf hka hg1) hSa hb1 hBa henv1 hir1
          exact ⟨env2, by rw [semScalar_seq, hs1, Option.bind_some]; exact hs2, henv2, hir2,
            hb2, fun i hi => (hg2 i (by omega)).trans (hg1 i hi)⟩
  | @rLetU64Zero x b hx _ ihb =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      cases hexec with
      | letU64Zero _ _ _ _ hbody =>
          simp only [ifConvert]
          obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit 0) (S := S) hf hx
            (show (0 : Nat) < 2 ^ 64 by decide) trivial hb
          obtain ⟨hb1, hg1⟩ :=
            write_facts (w := (SExpr.SLit 0).evalBV (envReader env)) hotb hx hS hb
          have henv1 := envBoundOn_updExpr henv hotb x 0
          obtain ⟨env3, hs3, henv3, hir3, hb3, hg3⟩ :=
            ihb flag (x :: S) k (fun y => B y ∨ y = x) _ rs' _ hbody hIR hr
              (flagOn_mono hf (le_refl k) (fun i _ => hg1 i)) (srcList_cons hx hS) hb1
              (sub_cons x hB) henv1 (scalarInRange_upd hir x (by norm_num))
          exact ⟨env3, by rw [semScalar_seq, hs2, Option.bind_some]; exact hs3, henv3, hir3,
            hb3, fun i hi => (hg3 i hi).trans (hg1 i)⟩
  | @rScalarSet x n hx hn =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      cases hexec
      obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit n) (S := S) hf hx hn trivial hb
      obtain ⟨hb1, hg1⟩ :=
        write_facts (w := (SExpr.SLit n).evalBV (envReader env)) hotb hx hS hb
      exact ⟨_, hs2, envBoundOn_updExpr henv hotb x n, scalarInRange_upd hir x hn, hb1,
        fun i _ => hg1 i⟩
  | @rScalarSetExpr x e hx he _ =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      cases hexec
      obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := elimLt e) (S := S) hf hx
        (srcClean_elimLt e he) (varsIn_elimLt e (varsIn_mono (bndP_of_sub hB hb) e hr)) hb
      have hval : (elimLt e).evalBV (envReader env) = BitVec.ofNat 64 (e.eval rs.rsScalar) := by
        rw [evalBV_elimLt, evalBV_congr_varsIn B (envReader env) (SExpr.liftEnv rs.rsScalar)
          (fun s hs => envReader_of_envBoundOn henv s hs (hS s (hB s hs)).1) e he hr]
        exact SExpr.evalBV_eq_ofNat_eval rs.rsScalar e hIR
      rw [hval] at hs2
      obtain ⟨hb1, hg1⟩ :=
        write_facts (w := BitVec.ofNat 64 (e.eval rs.rsScalar)) hotb hx hS hb
      exact ⟨_, hs2, envBoundOn_updExpr henv hotb x _,
        scalarInRange_upd hir x (SExpr.eval_lt_of_inRange _ _ hIR), hb1, fun i _ => hg1 i⟩
  | @rIfNz g t e hg ht he iht ihe =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      obtain ⟨hg', ht', he'⟩ := hr
      have hgS := hB g hg'
      simp only [ifConvert]
      obtain ⟨env3, hs3, hft, hfe, hfr3⟩ := semScalar_flags (flag := flag) (k := k)
        (.RSeq (ifConvert (some (guardName k)) S (k + 2) t).1
          (ifConvert (some (guardName (k + 1))) (ifConvert (some (guardName k)) S (k + 2) t).2.1
            (ifConvert (some (guardName k)) S (k + 2) t).2.2 e).1)
        hg (hb g hgS)
        (fun f hfe => by obtain ⟨j, rfl, hj, _⟩ := hf f hfe; exact Or.inr ⟨j, rfl, hj⟩)
        (fun f hfe => by obtain ⟨j, rfl, _, h1⟩ := hf f hfe; rw [h1]; rfl)
      have hgv : envReader env g = BitVec.ofNat 64 (rs.rsScalar g) :=
        envReader_of_envBoundOn henv g hg' hg.1
      have hnz : ltWord 0#64 (envReader env g)
          = BitVec.ofNat 64 (if 0 < rs.rsScalar g then 1 else 0) := by
        rw [hgv]; exact ltWord_ofNat (by norm_num) (hir g)
      have ho : ∀ a : BitVec 64, (1 : BitVec 64) * a = a := fun a => by simp
      rw [flagVal_of_flagOn hf, ho, hnz] at hft
      rw [flagVal_of_flagOn hf, ho, hnz] at hfe
      have hpres3 : ∀ y ∈ S, env3 y = env y := fun y hy =>
        hfr3 y (hS y hy).1 (srcName_ne_guardName (hS y hy) k)
          (srcName_ne_guardName (hS y hy) (k + 1))
      have hb3 : Bound env3 S := fun y hy => by
        rw [readU64_eq_of_env (hpres3 y hy)]; exact hb y hy
      have henv3 : EnvBoundOn rs env3 B := fun y hy hnt => by
        rw [hpres3 y (hB y hy)]; exact henv y hy hnt
      have hg3 : ∀ i, i < k → env3 (guardName i) = env (guardName i) := fun i hi =>
        hfr3 _ (not_isTmpName_guardName i)
          (fun h => by have := guardName_injective h; omega)
          (fun h => by have := guardName_injective h; omega)
      obtain ⟨hSt, hsubT, _, hkt⟩ := ifConvert_static ht (some (guardName k)) S (k + 2) B hS hB
      cases hexec with
      | ifTrue _ _ _ _ _ v hv hv0 hct =>
          have hpos : 0 < rs.rsScalar g := by subst hv; omega
          rw [if_pos hpos] at hft hfe
          obtain ⟨envT, hsT, henvT, hirT, hbT, hgT⟩ :=
            iht (some (guardName k)) S (k + 2) B rs rs' env3 hct (hIR.1 (by omega)) ht'
              (fun f hfe' => by cases hfe'; exact ⟨k, rfl, by omega, by rw [hft]; rfl⟩)
              hS hb3 hB henv3 hir
          have hfeT : envReadU64 envT (guardName (k + 1)) = some 0 := by
            rw [readU64_eq_of_env (hgT (k + 1) (by omega)), hfe]; rfl
          obtain ⟨envE, hsE, hpresE, hbE, hgE⟩ := ifConvert_skipped he (k + 1)
            (ifConvert (some (guardName k)) S (k + 2) t).2.1
            (ifConvert (some (guardName k)) S (k + 2) t).2.2 B envT (by omega) hfeT hSt hbT
            (fun y hy => hsubT y (hB y hy)) he'
          refine ⟨envE, ?_, ?_, hirT, hbE, ?_⟩
          · rw [hs3, semScalar_seq, hsT, Option.bind_some]; exact hsE
          · intro y hy hnt
            rw [hpresE y (hsubT y (hB y hy))]
            exact henvT y (le_afterG t B y hy) hnt
          · intro i hi
            rw [hgE i (by omega), hgT i (by omega)]; exact hg3 i hi
      | ifFalse _ _ _ _ _ hz hce =>
          have hnpos : ¬ 0 < rs.rsScalar g := by omega
          rw [if_neg hnpos] at hft hfe
          obtain ⟨envT, hsT, hpresT, hbT, hgT⟩ := ifConvert_skipped ht k S (k + 2) B env3
            (by omega) (by rw [hft]; rfl) hS hb3 hB ht'
          have henvT : EnvBoundOn rs envT B := fun y hy hnt => by
            rw [hpresT y (hB y hy)]; exact henv3 y hy hnt
          obtain ⟨envE, hsE, henvE, hirE, hbE, hgE⟩ :=
            ihe (some (guardName (k + 1))) (ifConvert (some (guardName k)) S (k + 2) t).2.1
              (ifConvert (some (guardName k)) S (k + 2) t).2.2 B rs rs' envT hce (hIR.2 hz) he'
              (fun f hfe' => by
                cases hfe'
                exact ⟨k + 1, rfl, by omega, by
                  rw [readU64_eq_of_env (hgT (k + 1) (by omega)), hfe]; rfl⟩)
              hSt hbT (fun y hy => hsubT y (hB y hy)) henvT hir
          refine ⟨envE, ?_, envBoundOn_mono henvE (fun y hy => le_afterG e B y hy), hirE, hbE,
            ?_⟩
          · rw [hs3, semScalar_seq, hsT, Option.bind_some]; exact hsE
          · intro i hi
            rw [hgE i (by omega), hgT i (by omega)]; exact hg3 i hi

/-- Agreement of `RustExec` with `semScalarGuarded`. On the guarded fragment,
    a `RustExec` run from an in-range state whose expressions stay in range, with
    every read following a write outside every conditional, is tracked by the
    `semScalarGuarded` run from the empty environment: the output environment
    binds every name written outside every conditional to the word of its output
    value. A name written only inside a conditional is not in
    `afterG (fun _ => False) c`, so the conclusion says nothing about it. -/
theorem rustExec_semScalarGuarded_agree {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hc : IsCoveredSCtlGuarded c) {rs rs' : RustState}
    (hexec : RustExec N leafSpec c rs rs') (hir : ScalarInRange rs)
    (hreads : readsG (fun _ => False) c) (hIR : InRangeG N leafSpec c rs) :
    ∃ env', semScalarGuarded c (fun _ => none) = some env' ∧
      EnvBoundOn rs' env' (afterG (fun _ => False) c) ∧ ScalarInRange rs' := by
  obtain ⟨env', hs, henv, hir', _, _⟩ := ifConvert_taken hc none [] 0 (fun _ => False) rs rs'
    (fun _ => none) hexec hIR hreads (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ h => by cases h) (fun _ h => h.elim) (fun _ h => h.elim) hir
  exact ⟨env', hs, henv, hir'⟩

/-! ## Success of the translator and the emit leg -/

open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)

theorem sexprVars_of_varsIn {P : String → Prop} :
    ∀ e : SExpr, srcClean e → varsIn P e → ∀ y ∈ sexprVars e, P y := by
  intro e
  induction e with
  | SVar x =>
      intro _ hv y hy
      simp only [sexprVars, List.mem_singleton] at hy
      subst hy; exact hv
  | SLit n => intro _ _ y hy; simp [sexprVars] at hy
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro hc hv y hy
      simp only [sexprVars, List.mem_append] at hy
      rcases hy with h | h
      · exact iha hc.1 hv.1 y h
      · exact ihb hc.2 hv.2 y h
  | _ => intro hc; exact hc.elim

/-- A name-to-type map claims `y` as a word. -/
def Claims (σ : NameTys) (y : String) : Prop := σ y = some (.sword 64)

theorem claims_upd {σ : NameTys} {x y : String} (h : Claims σ y) :
    Claims (σ.upd x (.sword 64)) y := by
  unfold Claims NameTys.upd at *
  split_ifs <;> simp_all

theorem claims_upd_self {σ : NameTys} {x : String} : Claims (σ.upd x (.sword 64)) x := by
  simp [Claims, NameTys.upd]

theorem gWrite_transTotal {flag : Option String} {S : List String} {x : String} {v : SExpr}
    {σ : NameTys} (hx : ¬ isTmpName x) (hcl : srcClean v) (hv : varsIn (Claims σ) v)
    (hf : ∀ f, flag = some f → Claims σ f ∧ ¬ isTmpName f) (hS : ∀ y ∈ S, Claims σ y) :
    TransTotal σ (gWrite flag S x v) (σ.upd x (.sword 64)) := by
  cases flag with
  | none => exact .rScalarSetExpr x v hx hcl (sexprVars_of_varsIn v hcl hv)
  | some f =>
      obtain ⟨hfc, hft⟩ := hf f rfl
      simp only [gWrite]
      split_ifs with hm
      · exact .rScalarSetExpr x _ hx ⟨hx, hft, hcl, hx⟩
          (sexprVars_of_varsIn _ ⟨hx, hft, hcl, hx⟩ ⟨hS x hm, hfc, hv, hS x hm⟩)
      · exact .rScalarSetExpr x _ hx ⟨hft, hcl⟩ (sexprVars_of_varsIn _ ⟨hft, hcl⟩ ⟨hfc, hv⟩)

/-- The conversion of a guarded-fragment command is in the reads-bound judgment
    `TransTotal` from every name-to-type map claiming the bound list and the flag. -/
theorem ifConvert_transTotal {c : LowCT} (hc : IsCoveredSCtlGuarded c) :
    ∀ (flag : Option String) (S : List String) (k : Nat) (B : String → Prop) (σ : NameTys),
      SrcList S → (∀ y, B y → y ∈ S) → readsG B c → (∀ y ∈ S, Claims σ y) →
      (∀ f, flag = some f → Claims σ f ∧ ¬ isTmpName f) →
      ∃ σ', TransTotal σ (ifConvert flag S k c).1 σ' ∧
        (∀ y ∈ (ifConvert flag S k c).2.1, Claims σ' y) ∧
        (∀ y, Claims σ y → Claims σ' y) := by
  induction hc with
  | rSkip => intro _ S k B σ _ _ _ hS _; exact ⟨σ, .rSkip, hS, fun _ h => h⟩
  | @rSeq a b ha _ iha ihb =>
      intro flag S k B σ hSrc hB hr hS hf
      simp only [ifConvert]
      obtain ⟨σ1, h1, hS1, hm1⟩ := iha flag S k B σ hSrc hB hr.1 hS hf
      obtain ⟨hSa, _, hBa, _⟩ := ifConvert_static ha flag S k B hSrc hB
      obtain ⟨σ2, h2, hS2, hm2⟩ := ihb flag _ _ (afterG B a) σ1 hSa hBa hr.2 hS1
        (fun f hfe => ⟨hm1 f (hf f hfe).1, (hf f hfe).2⟩)
      exact ⟨σ2, .rSeq h1 h2, hS2, fun y h => hm2 y (hm1 y h)⟩
  | @rLetU64Zero x b hx _ ihb =>
      intro flag S k B σ hSrc hB hr hS hf
      simp only [ifConvert]
      have hw := gWrite_transTotal (flag := flag) (S := S) (v := .SLit 0) hx.1
        (show (0 : Nat) < 2 ^ 64 by decide) trivial hf hS
      obtain ⟨σ2, h2, hS2, hm2⟩ := ihb flag (x :: S) k (fun y => B y ∨ y = x) _
        (srcList_cons hx hSrc) (sub_cons x hB) hr
        (fun y hy => by
          rcases List.mem_cons.mp hy with rfl | h
          · exact claims_upd_self
          · exact claims_upd (hS y h))
        (fun f hfe => ⟨claims_upd (hf f hfe).1, (hf f hfe).2⟩)
      exact ⟨σ2, .rSeq hw h2, hS2, fun y h => hm2 y (claims_upd h)⟩
  | @rScalarSet x n hx hn =>
      intro flag S k B σ hSrc hB hr hS hf
      refine ⟨_, gWrite_transTotal (v := .SLit n) hx.1 hn trivial hf hS, ?_,
        fun y h => claims_upd h⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | h
      · exact claims_upd_self
      · exact claims_upd (hS y h)
  | @rScalarSetExpr x e hx he _ =>
      intro flag S k B σ hSrc hB hr hS hf
      refine ⟨_, gWrite_transTotal (v := elimLt e) hx.1 (srcClean_elimLt e he)
        (varsIn_elimLt e (varsIn_mono (fun s hs => hS s (hB s hs)) e hr)) hf hS, ?_,
        fun y h => claims_upd h⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | h
      · exact claims_upd_self
      · exact claims_upd (hS y h)
  | @rIfNz g t e hg ht he iht ihe =>
      intro flag S k B σ hSrc hB hr hS hf
      obtain ⟨hg', ht', he'⟩ := hr
      simp only [ifConvert]
      have hgc : Claims σ g := hS g (hB g hg')
      have hclF : srcClean (andFlag flag (nzExpr g)) :=
        srcClean_andFlag (fun f hfe => (hf f hfe).2) (srcClean_nzExpr hg.1)
      have hvF : ∀ τ : NameTys, Claims τ g → (∀ f, flag = some f → Claims τ f) →
          varsIn (Claims τ) (andFlag flag (nzExpr g)) := by
        intro τ hτg hτf
        cases flag with
        | none => simp [andFlag, nzExpr, ltExpr, carryExpr, varsIn, hτg]
        | some f => simp [andFlag, nzExpr, ltExpr, carryExpr, varsIn, hτg, hτf f rfl]
      have hvE : ∀ τ : NameTys, Claims τ g → (∀ f, flag = some f → Claims τ f) →
          varsIn (Claims τ) (andFlag flag (.SSub (.SLit 1) (nzExpr g))) := by
        intro τ hτg hτf
        cases flag with
        | none => simp [andFlag, nzExpr, ltExpr, carryExpr, varsIn, hτg]
        | some f => simp [andFlag, nzExpr, ltExpr, carryExpr, varsIn, hτg, hτf f rfl]
      have hclE : srcClean (andFlag flag (.SSub (.SLit 1) (nzExpr g))) :=
        srcClean_andFlag (fun f hfe => (hf f hfe).2)
          ⟨show (1 : Nat) < 2 ^ 64 by decide, srcClean_nzExpr hg.1⟩
      have h1 : TransTotal σ (.RScalarSetExpr (guardName k) (andFlag flag (nzExpr g)))
          (σ.upd (guardName k) (.sword 64)) :=
        .rScalarSetExpr _ _ (not_isTmpName_guardName k) hclF
          (sexprVars_of_varsIn _ hclF (hvF σ hgc (fun f hfe => (hf f hfe).1)))
      set σ1 := σ.upd (guardName k) (.sword 64)
      have h2 : TransTotal σ1 (.RScalarSetExpr (guardName (k + 1))
          (andFlag flag (.SSub (.SLit 1) (nzExpr g))))
          (σ1.upd (guardName (k + 1)) (.sword 64)) :=
        .rScalarSetExpr _ _ (not_isTmpName_guardName (k + 1)) hclE
          (sexprVars_of_varsIn _ hclE (hvE σ1 (claims_upd hgc)
            (fun f hfe => claims_upd (hf f hfe).1)))
      set σ2 := σ1.upd (guardName (k + 1)) (.sword 64)
      have hm12 : ∀ y, Claims σ y → Claims σ2 y := fun y h => claims_upd (claims_upd h)
      obtain ⟨hSt, hsubT, _, _⟩ := ifConvert_static ht (some (guardName k)) S (k + 2) B hSrc hB
      obtain ⟨σT, hT, hST, hmT⟩ := iht (some (guardName k)) S (k + 2) B σ2 hSrc hB ht'
        (fun y hy => hm12 y (hS y hy))
        (fun f hfe => by
          cases hfe; exact ⟨claims_upd claims_upd_self, not_isTmpName_guardName k⟩)
      obtain ⟨σE, hE, hSE, hmE⟩ := ihe (some (guardName (k + 1)))
        (ifConvert (some (guardName k)) S (k + 2) t).2.1
        (ifConvert (some (guardName k)) S (k + 2) t).2.2 B σT hSt
        (fun y hy => hsubT y (hB y hy)) he' hST
        (fun f hfe => by
          cases hfe; exact ⟨hmT _ claims_upd_self, not_isTmpName_guardName (k + 1)⟩)
      exact ⟨σE, .rSeq h1 (.rSeq h2 (.rSeq hT hE)), hSE, fun y h => hmE y (hmT y (hm12 y h))⟩

theorem afterG_srcName {c : LowCT} (hc : IsCoveredSCtlGuarded c) :
    ∀ (B : String → Prop), (∀ y, B y → srcName y) → ∀ y, afterG B c y → srcName y := by
  induction hc with
  | rSkip => exact fun B hB => hB
  | rSeq _ _ iha ihb => exact fun B hB => ihb _ (iha B hB)
  | @rLetU64Zero x _ hx _ ihb =>
      exact fun B hB => ihb _ (fun y hy => by rcases hy with h | rfl; exact hB y h; exact hx)
  | @rScalarSet x _ hx _ | @rScalarSetExpr x _ hx _ _ =>
      exact fun B hB y hy => by rcases hy with h | rfl; exact hB y h; exact hx
  | rIfNz _ _ _ _ _ => exact fun B hB => hB

/-- The guarded translator from an entry `VarMap` whose bound names are the list
    `S`: `translateDialectControl` on the guarded conversion with bound list `S`.
    At `S = []` it is `translateDialectGuarded`. -/
def translateDialectGuardedIn {Γ : Ctx} (vm : VarMap Γ) (S : List String) (c : LowCT) :
    Option (DTransOut Γ) :=
  translateDialectControl vm (ifConvert none S 0 c).1

/-- The name-to-type map claiming exactly the names of `S` as words. -/
def listTys (S : List String) : NameTys := fun y => if y ∈ S then some (.sword 64) else none

/-- A word slot of a consistent environment is bound in the `VarMap` at the same
    slot value. -/
theorem lookup_of_consistentS {Γ : Ctx} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar} {y : String}
    {w : BitVec 64} (hcons : ConsistentS vm V env) (hy : env y = some ⟨.sword 64, w⟩) :
    ∃ v : CVar Γ (.sword 64), vm.lookup y = some ⟨.sword 64, v⟩ := by
  have hlk := hcons y
  rw [hy] at hlk
  obtain ⟨⟨t, v⟩, hv⟩ : ∃ p, vm.lookup y = some p := by
    cases h : vm.lookup y with
    | none => rw [h] at hlk; cases hlk
    | some p => exact ⟨p, rfl⟩
  rw [hv] at hlk
  simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq] at hlk
  obtain ⟨rfl, _⟩ := hlk
  exact ⟨v, hv⟩

/-- The compiled program computes the value of the source run, from an entry
    state with inputs. Let `S` list source names, `B` the same set as a predicate,
    and let the entry `VarMap` `vm`, valuation `V` and environment `env` be
    consistent, with `env` binding every name of `S` to the word of its value in
    the entry state `rs`. For a guarded-fragment command with a `RustExec` run
    from `rs` in range whose reads are in `S` or follow a write outside every
    conditional, the guarded translator with bound list `S` and the jasmin
    lowering succeed, and the emitted jasmin program returning the slot of a name
    `name` that is in `S` or written outside every conditional denotes, at the
    valuation `ctMapValD V`, the word of that name's value in the output state. -/
theorem translateDialectGuardedIn_jasmin {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hc : IsCoveredSCtlGuarded c) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (S : List String) (B : String → Prop) (hS : SrcList S)
    (hBS : ∀ y, B y → y ∈ S) (hSB : ∀ y ∈ S, B y)
    (hcons : ConsistentS vm V env) {rs rs' : RustState}
    (henv : EnvBoundOn rs env B)
    (hexec : RustExec N leafSpec c rs rs') (hir : ScalarInRange rs)
    (hreads : readsG B c) (hIR : InRangeG N leafSpec c rs)
    (name : String) (hname : afterG B c name) :
    ∃ (o : DTransOut Γ) (w : CVar o.Γ' (.sword 64))
      (com : Com catCryptDialect Γ (.sword 64))
      (jcom : Com jasminDialect (mapCtx Γ) (mapTy (.sword 64))),
      translateDialectGuardedIn vm S c = some o ∧
      o.vm.lookup name = some ⟨.sword 64, w⟩ ∧
      o.cont (Com.ret (toVIRVar w)) = some com ∧
      cryptoDialectToJasminCom com = some jcom ∧
      jcom.denote (ctMapValD V) = ctTransTy (BitVec.ofNat 64 (rs'.rsScalar name)) := by
  have hwS : ∀ y ∈ S, env y = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar y)⟩ :=
    fun y hy => henv y (hSB y hy) (hS y hy).1
  have hbS : Bound env S := fun y hy => by rw [readU64_of_env (hwS y hy)]; rfl
  obtain ⟨env', hsem, henv', _, _, _⟩ := ifConvert_taken hc none S 0 B rs rs' env hexec hIR
    hreads (fun _ h => by cases h) hS hbS hBS henv hir
  have hsrc : srcName name :=
    afterG_srcName hc B (fun y hy => hS y (hBS y hy)) name hname
  have hval : env' name = some ⟨.sword 64, BitVec.ofNat 64 (rs'.rsScalar name)⟩ :=
    henv' name hname hsrc.1
  have hclaims : ∀ y ∈ S, Claims (listTys S) y := fun y hy => by
    simp [Claims, listTys, hy]
  obtain ⟨σ', htot, _, _⟩ := ifConvert_transTotal hc none S 0 B (listTys S) hS hBS hreads
    hclaims (fun _ h => by cases h)
  have hsrcT : SrcTys (listTys S) := fun x hx => by
    by_cases hm : x ∈ S
    · exact (hS x hm).1
    · simp [listTys, hm] at hx
  have happrox : VmApprox (listTys S) vm := fun x t hx => by
    by_cases hm : x ∈ S
    · simp only [listTys, if_pos hm, Option.some.injEq] at hx
      subst hx
      exact lookup_of_consistentS hcons (hwS x hm)
    · simp [listTys, hm] at hx
  obtain ⟨o, htr, _, hcont⟩ := translateDialectControl_total htot vm hsrcT happrox
  have hcov : IsCoveredSCtl (ifConvert none S 0 c).1 :=
    .ofStraight (ifConvert_covered hc none S 0 (fun _ h => by cases h))
  obtain ⟨V', hcons', _⟩ := translateDialectControl_denote_ctl hcov vm V env env' o hcons htr hsem
  obtain ⟨w, hw⟩ := lookup_of_consistentS hcons' hval
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar w)) (by rfl)
  obtain ⟨jcom, hjcom⟩ := Option.isSome_iff_exists.mp hlow
  exact ⟨o, w, com, jcom, htr, hw, hcom, hjcom,
    CompilerCorrectnessExtracted.semScalarToJasminCom_denote_eq vm (ifConvert none S 0 c).1 o
      V env env' name w _ com jcom hcov htr hcons hsem hw hval hcom hjcom⟩

/-- The compiled program computes the value of the source run, for a command
    that reads no input. The translation starts from the empty `VarMap`, the
    empty valuation and the empty environment, so the emitted jasmin program has
    no parameters and denotes a constant. For a guarded-fragment command with a
    `RustExec` run in range whose every read follows a write outside every
    conditional, the guarded translator and the jasmin lowering succeed, and the
    emitted jasmin program returning the slot of a name `name` written outside
    every conditional denotes the word of that name's value in the output state
    of the run. `translateDialectGuardedIn_jasmin` is the form with inputs. -/
theorem translateDialectGuarded_jasmin {N : Nat} {leafSpec : LeafSpec} {c : LowCT}
    (hc : IsCoveredSCtlGuarded c) {rs rs' : RustState}
    (hexec : RustExec N leafSpec c rs rs') (hir : ScalarInRange rs)
    (hreads : readsG (fun _ => False) c) (hIR : InRangeG N leafSpec c rs)
    (name : String) (hname : afterG (fun _ => False) c name) :
    ∃ (o : DTransOut ([] : Ctx)) (w : CVar o.Γ' (.sword 64))
      (com : Com catCryptDialect ([] : Ctx) (.sword 64))
      (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64))),
      translateDialectGuarded VarMap.empty c = some o ∧
      o.vm.lookup name = some ⟨.sword 64, w⟩ ∧
      o.cont (Com.ret (toVIRVar w)) = some com ∧
      cryptoDialectToJasminCom com = some jcom ∧
      jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (rs'.rsScalar name)) :=
  translateDialectGuardedIn_jasmin hc VarMap.empty .nil (fun _ => none) [] (fun _ => False)
    (fun _ h => by cases h) (fun _ h => h.elim) (fun _ h => by cases h) consistentS_empty
    (fun _ h => h.elim) hexec hir hreads hIR name hname

/-! ## Boolean tests for the scoping and the in-range condition -/

open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedUnroll

/-- The list form of `afterG`. -/
def afterL (L : List String) : LowCT → List String
  | .RSeq a b => afterL (afterL L a) b
  | .RLetU64Zero x b => afterL (x :: L) b
  | .RScalarSet x _ => x :: L
  | .RScalarSetExpr x _ => x :: L
  | _ => L

/-- The list form of `varsIn`. -/
def varsInL (L : List String) : SExpr → Bool
  | .SVar x => decide (x ∈ L)
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b | .SLt a b => varsInL L a && varsInL L b
  | _ => true

/-- The list form of `readsG`. -/
def readsB (L : List String) : LowCT → Bool
  | .RSeq a b => readsB L a && readsB (afterL L a) b
  | .RLetU64Zero x b => readsB (x :: L) b
  | .RScalarSetExpr _ e => varsInL L e
  | .RIfNz g t e => decide (g ∈ L) && readsB L t && readsB L e
  | _ => true

theorem varsInL_sound {L : List String} {B : String → Prop} (hL : ∀ y ∈ L, B y) :
    ∀ e : SExpr, varsInL L e = true → varsIn B e := by
  intro e
  induction e with
  | SVar x => intro h; exact hL x (by simpa [varsInL] using h)
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb
  | SLt a b iha ihb =>
      intro h; simp only [varsInL, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | _ => intro _; trivial

theorem afterL_sound : ∀ (c : LowCT) (L : List String) (B : String → Prop),
    (∀ y ∈ L, B y) → ∀ y ∈ afterL L c, afterG B c y := by
  intro c
  induction c with
  | RSeq a b iha ihb => exact fun L B hL => ihb _ _ (iha L B hL)
  | RLetU64Zero x b ih =>
      intro L B hL
      exact ih _ _ (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | h; exact Or.inr rfl; exact Or.inl (hL y h))
  | RScalarSet x _ | RScalarSetExpr x _ =>
      intro L B hL y hy
      rcases List.mem_cons.mp hy with rfl | h; exact Or.inr rfl; exact Or.inl (hL y h)
  | _ => exact fun L B hL => hL

theorem readsB_sound : ∀ (c : LowCT) (L : List String) (B : String → Prop),
    (∀ y ∈ L, B y) → readsB L c = true → readsG B c := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro L B hL h
      simp only [readsB, Bool.and_eq_true] at h
      exact ⟨iha L B hL h.1, ihb _ _ (afterL_sound a L B hL) h.2⟩
  | RLetU64Zero x b ih =>
      intro L B hL h
      exact ih _ _ (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | h; exact Or.inr rfl; exact Or.inl (hL y h)) h
  | RScalarSetExpr x e => intro L B hL h; exact varsInL_sound hL e h
  | RIfNz g t e iht ihe =>
      intro L B hL h
      simp only [readsB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨hL g h.1.1, iht L B hL h.1.2, ihe L B hL h.2⟩
  | _ => intro _ _ _ _; trivial

/-- The Boolean test for `SExpr.inRange`. -/
def inRangeB (σ : String → Nat) : SExpr → Bool
  | .SVar x => decide (σ x < 2 ^ 64)
  | .SLit n => decide (n < 2 ^ 64)
  | .SAdd a b => inRangeB σ a && inRangeB σ b && decide (a.eval σ + b.eval σ < 2 ^ 64)
  | .SSub a b => inRangeB σ a && inRangeB σ b && decide (b.eval σ ≤ a.eval σ)
  | .SMul a b => inRangeB σ a && inRangeB σ b && decide (a.eval σ * b.eval σ < 2 ^ 64)
  | .SShr a b => inRangeB σ a && inRangeB σ b && decide (b.eval σ < 64)
  | .SShl a b => inRangeB σ a && inRangeB σ b && decide (b.eval σ < 64) &&
      decide (a.eval σ <<< b.eval σ < 2 ^ 64)
  | .SAnd a b | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b
  | .SMulHiS a b => inRangeB σ a && inRangeB σ b
  | .SLimb _ _ => true

theorem inRangeB_sound (σ : String → Nat) :
    ∀ e : SExpr, inRangeB σ e = true → e.inRange σ := by
  intro e
  induction e with
  | SVar x => intro h; exact (by simpa [inRangeB] using h : σ x < 2 ^ 64)
  | SLit n => intro h; exact (by simpa [inRangeB] using h : n < 2 ^ 64)
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SShr a b iha ihb =>
      intro h
      simp only [inRangeB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨iha h.1.1, ihb h.1.2, h.2⟩
  | SShl a b iha ihb =>
      intro h
      simp only [inRangeB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨iha h.1.1.1, ihb h.1.1.2, h.1.2, h.2⟩
  | SAnd a b iha ihb | SXor a b iha ihb | SLt a b iha ihb | SAsr a b iha ihb
  | SMulS a b iha ihb | SMulHiU a b iha ihb | SMulHiS a b iha ihb =>
      intro h
      simp only [inRangeB, Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | SLimb v i => intro _; trivial

/-- The Boolean test for `InRangeG`, computed along the `runK k` run. -/
def inRangeRunB (k : Nat) : LowCT → RustState → Bool
  | .RSeq a b, rs => inRangeRunB k a rs &&
      match runK k a rs with
      | some r1 => inRangeRunB k b r1
      | none => false
  | .RLetU64Zero x b, rs => inRangeRunB k b (rsSetScalar rs x 0)
  | .RScalarSetExpr _ e, rs => inRangeB rs.rsScalar e
  | .RIfNz g t e, rs => if rs.rsScalar g = 0 then inRangeRunB k e rs else inRangeRunB k t rs
  | _, _ => true

theorem inRangeRunB_sound {N : Nat} {leafSpec : LeafSpec} (k : Nat) :
    ∀ (c : LowCT) (rs : RustState), IsScalarCmd c → inRangeRunB k c rs = true →
      InRangeG N leafSpec c rs := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro rs hc h
      cases hc with
      | rSeq hca hcb =>
          simp only [inRangeRunB, Bool.and_eq_true] at h
          refine ⟨iha rs hca h.1, fun r1 hr1 => ?_⟩
          have h2 := h.2
          cases hrun : runK k a rs with
          | none => rw [hrun] at h2; cases h2
          | some r1' =>
              rw [hrun] at h2
              obtain rfl := rustExec_deterministic (runK_rustExec (N := N) (leafSpec := leafSpec)
                k a rs r1' hrun) hca hr1
              exact ihb r1' hcb h2
  | RLetU64Zero x b ih =>
      intro rs hc h
      cases hc with
      | rLetU64Zero _ hcb => exact ih _ hcb h
  | RScalarSetExpr x e => intro rs _ h; exact inRangeB_sound _ e h
  | RIfNz g t e iht ihe =>
      intro rs hc h
      cases hc with
      | rIfNz _ hct hce =>
          simp only [inRangeRunB] at h
          refine ⟨fun hne => ?_, fun hz => ?_⟩
          · rw [if_neg hne] at h; exact iht rs hct h
          · rw [if_pos hz] at h; exact ihe rs hce h
  | _ => intro _ _ _; trivial

/-- `inRangeRunB` over an association-list store. -/
def inRangeRunBL (k : Nat) : LowCT → List (String × Nat) → Bool
  | .RSeq a b, l => inRangeRunBL k a l &&
      match runKL k a l with
      | some l1 => inRangeRunBL k b l1
      | none => false
  | .RLetU64Zero x b, l => inRangeRunBL k b (insertL l x 0)
  | .RScalarSetExpr _ e, l => inRangeB (lookupD l) e
  | .RIfNz g t e, l => if lookupD l g = 0 then inRangeRunBL k e l else inRangeRunBL k t l
  | _, _ => true

theorem inRangeRunB_storeState (k : Nat) (tw : String → Option (Σ t : TowerType, RustVal t)) :
    ∀ (c : LowCT) (l : List (String × Nat)),
      inRangeRunB k c (storeState tw l) = inRangeRunBL k c l := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro l
      simp only [inRangeRunB, inRangeRunBL, iha, runK_storeState]
      cases runKL k a l with
      | none => rfl
      | some l1 => simp only [Option.map_some, ihb]
  | RLetU64Zero x b ih =>
      intro l; simp only [inRangeRunB, inRangeRunBL, rsSetScalar_storeState, ih]
  | RScalarSetExpr x e => intro l; rfl
  | RIfNz g t e iht ihe =>
      intro l
      have hs : (storeState tw l).rsScalar g = lookupD l g := rfl
      simp only [inRangeRunB, inRangeRunBL, hs, iht, ihe]
  | _ => intro l; rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree
