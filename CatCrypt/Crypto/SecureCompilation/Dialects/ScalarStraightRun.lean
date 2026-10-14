/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree
public import CatCrypt.Crypto.SecureCompilation.Dialects.CoveredSCtlDecide

/-!
# An indexed evaluator for straight-line `semScalar` programs

`semScalar` lowers the expression of an `RScalarSetExpr` through `semLowerSExpr`,
which binds a chain of fresh temporaries `tmpName k`. The environment after a run
is therefore determined only up to those temporaries. This module gives an
evaluator that skips them: `intern` replaces the names of a straight-line
program by their indices in a name table, and `runIdx` runs the indexed program
on a list of typed values. The values may contain free variables; a run lemma for
a concrete body is one kernel evaluation of `runProg` (`kernel_rfl`), with the
kernel keeping shared subterms shared.

## Main definitions

* `SrcAgree env G` — `env` and `G` agree on every non-temporary name.
* `IE` / `IL` / `intern` — the indexed program and the interning of names.
* `VEnv` / `runIdx` / `runProg` — the value environment and the evaluator.
* `toS tbl σ base` — the `SEnvScalar` an indexed environment denotes: table names
  read their slot, every other name reads `base`.

## Main results

* `runIdx_sound` — when `p` interns to `ip` and `ip` runs from `σ` to `σ'`,
  `semScalar p` runs from every environment agreeing with `toS tbl σ base` off the
  temporaries to one agreeing with `toS tbl σ' base`.
* `runProg_sound` — the same, started from the base environment itself.
* `toS_not_mem` — a name outside the table reads the base environment.
* `SEnvScalar.upd_same` / `SEnvScalar.upd_ne` — lookups through
  `SEnvScalar.upd`, for `simp [SEnvScalar.upd_same, SEnvScalar.upd_ne]`; a
  string-literal disequality side condition closes by `decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-- An updated name reads back the value it was bound to. -/
theorem SEnvScalar.upd_same (env : SEnvScalar) (x : String) {t : CryptoTy}
    (v : ⟦t⟧) : env.upd x v x = some ⟨t, v⟩ := by
  simp [SEnvScalar.upd]

/-- A name other than the updated one reads through the update. -/
theorem SEnvScalar.upd_ne (env : SEnvScalar) {x y : String} {t : CryptoTy}
    (v : ⟦t⟧) (h : y ≠ x) : env.upd x v y = env y := by
  simp [SEnvScalar.upd, h]

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ScalarStraightRun

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree (BndP)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt (varsIn)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.Ascent (notTmpB srcCleanB notTmpB_sound srcCleanB_sound)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located sexprMulHiU)

theorem notTmp {s : String} (h : notTmpB s = true) : ¬ isTmpName s := notTmpB_sound s h

/-- `env` and `G` agree on every name outside the temporary namespace. -/
def SrcAgree (env G : SEnvScalar) : Prop := ∀ s, ¬ isTmpName s → env s = G s

theorem SrcAgree.refl (G : SEnvScalar) : SrcAgree G G := fun _ _ => rfl

theorem SrcAgree.upd {env G : SEnvScalar} (h : SrcAgree env G) (x : String) {t : CryptoTy}
    (v : ⟦t⟧) : SrcAgree (env.upd x v) (G.upd x v) := by
  intro s hs
  simp only [SEnvScalar.upd]
  split
  · rfl
  · exact h s hs

/-- A clean expression reads the same word from agreeing environments. -/
theorem SrcAgree.evalBV {env G : SEnvScalar} (h : SrcAgree env G) :
    ∀ e : SExpr, srcClean e → e.evalBV (envReader env) = e.evalBV (envReader G) := by
  intro e
  induction e with
  | SVar x => intro hc; simp only [SExpr.evalBV, envReader, h x hc]
  | SLit n => intro _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro hc; simp only [SExpr.evalBV, iha hc.1, ihb hc.2]
  | _ => intro hc; exact hc.elim

/-- Every variable an expression reads is bound to a 64-bit word. -/
def wordsBoundB (G : SEnvScalar) (e : SExpr) : Bool :=
  (sexprVars e).all (fun s => (envReadU64 G s).isSome)

theorem varsIn_of_wordsBoundB {G env : SEnvScalar} (hag : SrcAgree env G) :
    ∀ e : SExpr, srcClean e → wordsBoundB G e = true → varsIn (BndP env) e := by
  intro e
  induction e with
  | SVar x =>
      intro hc hb _
      simp only [wordsBoundB, sexprVars, List.all_cons, List.all_nil, Bool.and_true] at hb
      simpa only [envReadU64, hag x hc] using hb
  | SLit n => intro _ _; trivial
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro hc hb
      simp only [wordsBoundB, sexprVars, List.all_append, Bool.and_eq_true] at hb
      exact ⟨iha hc.1 hb.1, ihb hc.2 hb.2⟩
  | _ => intro hc; exact hc.elim

/-! ## The name table and the indexed value environment -/

/-- A typed scalar value: a `CryptoTy` together with an inhabitant. -/
abbrev SVal := (t : CryptoTy) × ⟦t⟧

/-- A value environment keyed by name-table index; `none` reads through to the
    base environment. -/
abbrev VEnv := List (Option SVal)

/-- The slot at index `i`, `none` beyond the end. -/
def getAt : VEnv → Nat → Option SVal
  | [], _ => none
  | v :: _, 0 => v
  | _ :: vs, n + 1 => getAt vs n

/-- Bind slot `i` to `v`, padding with `none` beyond the end. -/
def setAt : VEnv → Nat → SVal → VEnv
  | [], 0, v => [some v]
  | [], n + 1, v => none :: setAt [] n v
  | _ :: vs, 0, v => some v :: vs
  | w :: vs, n + 1, v => w :: setAt vs n v

theorem getAt_setAt : ∀ (σ : VEnv) (i : Nat) (v : SVal) (j : Nat),
    getAt (setAt σ i v) j = if j = i then some v else getAt σ j
  | [], 0, _, 0 => rfl
  | [], 0, _, _ + 1 => by simp [setAt, getAt]
  | [], _ + 1, _, 0 => by simp [setAt, getAt]
  | [], n + 1, v, j + 1 => by
      simp only [setAt, getAt, getAt_setAt [] n v j, Nat.add_right_cancel_iff]
  | _ :: _, 0, _, 0 => rfl
  | _ :: _, 0, _, _ + 1 => by simp [setAt, getAt]
  | _ :: _, _ + 1, _, 0 => by simp [setAt, getAt]
  | _ :: vs, n + 1, v, j + 1 => by
      simp only [setAt, getAt, getAt_setAt vs n v j, Nat.add_right_cancel_iff]

/-- The index of the first occurrence of a name in the table. -/
def idxIn : List String → String → Option Nat
  | [], _ => none
  | n :: ns, s => if s = n then some 0 else (idxIn ns s).map (· + 1)

theorem idxIn_getElem? : ∀ (tbl : List String) (s : String) (i : Nat),
    idxIn tbl s = some i → tbl[i]? = some s
  | [], _, _, h => by simp [idxIn] at h
  | n :: ns, s, i, h => by
      simp only [idxIn] at h
      split at h
      · cases h; simp_all
      · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simpa using idxIn_getElem? ns s k hk

theorem idxIn_inj {tbl : List String} {s x : String} {i : Nat}
    (hs : idxIn tbl s = some i) (hx : idxIn tbl x = some i) : s = x := by
  have h1 := idxIn_getElem? tbl s i hs
  have h2 := idxIn_getElem? tbl x i hx
  rw [h1] at h2
  exact Option.some.inj h2

theorem idxIn_map : ∀ (tbl : List String) (f : String → Option SVal) (s : String) (i : Nat),
    idxIn tbl s = some i → getAt (tbl.map f) i = f s
  | [], _, _, _, h => by simp [idxIn] at h
  | n :: ns, f, s, i, h => by
      simp only [idxIn] at h
      split at h
      · cases h; subst_vars; rfl
      · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
        exact idxIn_map ns f s k hk

/-- The `SEnvScalar` an indexed environment denotes over a base environment: a
    table name reads its slot when the slot is bound, every other read goes to
    `base`. -/
def toS (tbl : List String) (σ : VEnv) (base : SEnvScalar) : SEnvScalar :=
  fun s => match idxIn tbl s with
    | some i => match getAt σ i with
      | some v => some v
      | none => base s
    | none => base s

theorem toS_at {tbl : List String} {σ : VEnv} {base : SEnvScalar} {x : String} {i : Nat}
    {v : SVal} (hx : idxIn tbl x = some i) (hv : getAt σ i = some v) :
    toS tbl σ base x = some v := by
  simp only [toS, hx, hv]

theorem toS_setAt {tbl : List String} {σ : VEnv} {base : SEnvScalar} {x : String} {i : Nat}
    (hx : idxIn tbl x = some i) (v : SVal) :
    toS tbl (setAt σ i v) base = (toS tbl σ base).upd x (t := v.1) v.2 := by
  funext s
  simp only [SEnvScalar.upd]
  split
  · subst_vars; simp only [toS, hx, getAt_setAt, if_true]
  · rename_i hne
    simp only [toS]
    split
    · rename_i j hj
      have hji : j ≠ i := fun h => hne (idxIn_inj hj (h ▸ hx))
      simp only [getAt_setAt, if_neg hji]
    · rfl

/-- Reading the table names out of a base environment gives an indexed
    environment that denotes the base environment. -/
theorem toS_map (tbl : List String) (base : SEnvScalar) :
    toS tbl (tbl.map base) base = base := by
  funext s
  simp only [toS]
  split
  · rename_i i hi
    rw [idxIn_map tbl base s i hi]
    split <;> simp_all
  · rfl

/-- A name outside the table reads through to the base environment. -/
theorem toS_not_mem {tbl : List String} {σ : VEnv} {base : SEnvScalar} {s : String}
    (hs : s ∉ tbl) : toS tbl σ base s = base s := by
  have : idxIn tbl s = none := by
    cases h : idxIn tbl s with
    | none => rfl
    | some i => exact absurd (List.mem_of_getElem? (idxIn_getElem? tbl s i h)) hs
  simp only [toS, this]

/-! ## The indexed program and its evaluator -/

/-- An `SExpr` over name-table indices. -/
inductive IE where
  | var (i : Nat)
  | lit (n : Nat)
  | add (a b : IE)
  | sub (a b : IE)
  | mul (a b : IE)
  | and (a b : IE)
  | xor (a b : IE)
  | shl (a b : IE)
  | shr (a b : IE)
  | mulHiU (a b : IE)

/-- A straight-line `LowCT` command over name-table indices. -/
inductive IL where
  | skip
  | seq (a b : IL)
  | setLit (x n : Nat)
  | setE (x : Nat) (e : IE)
  | load (d a i : Nat)
  | store (a i s : Nat) (ty : CryptoTy)

/-- Intern the names of an expression. -/
def internE (tbl : List String) : SExpr → Option IE
  | .SVar x => (idxIn tbl x).map .var
  | .SLit n => some (.lit n)
  | .SAdd a b => (internE tbl a).bind fun ia => (internE tbl b).map (.add ia)
  | .SSub a b => (internE tbl a).bind fun ia => (internE tbl b).map (.sub ia)
  | .SMul a b => (internE tbl a).bind fun ia => (internE tbl b).map (.mul ia)
  | .SAnd a b => (internE tbl a).bind fun ia => (internE tbl b).map (.and ia)
  | .SXor a b => (internE tbl a).bind fun ia => (internE tbl b).map (.xor ia)
  | .SShl a b => (internE tbl a).bind fun ia => (internE tbl b).map (.shl ia)
  | .SShr a b => (internE tbl a).bind fun ia => (internE tbl b).map (.shr ia)
  | .SMulHiU a b => (internE tbl a).bind fun ia => (internE tbl b).map (.mulHiU ia)
  | _ => none

/-- Intern the names of a straight-line program. Every name must be in the table
    and outside the temporary namespace, and every expression clean; `none`
    otherwise, and on every arm outside the straight-line fragment. -/
def intern (tbl : List String) : LowCT → Option IL
  | .RSkip => some .skip
  | .RAssert _ => some .skip
  | .RSeq a b => (intern tbl a).bind fun ia => (intern tbl b).map (.seq ia)
  | .RBlock b => intern tbl b
  | .RScalarSet x n => if notTmpB x then (idxIn tbl x).map (.setLit · n) else none
  | .RScalarSetExpr x e =>
      if notTmpB x && srcCleanB e then
        (idxIn tbl x).bind fun ix => (internE tbl e).map (.setE ix)
      else none
  | .RArrLoad ⟨d, .TU64⟩ src i =>
      if notTmpB d && notTmpB src.locVar && notTmpB i then
        (idxIn tbl d).bind fun id => (idxIn tbl src.locVar).bind fun ia =>
          (idxIn tbl i).map (.load id ia)
      else none
  | .RArrStore arr i src =>
      if notTmpB arr.locVar && notTmpB i && notTmpB src.locVar then
        (idxIn tbl arr.locVar).bind fun ia => (idxIn tbl i).bind fun ii =>
          (idxIn tbl src.locVar).map fun is => .store ia ii is (encodeTy arr.locDst)
      else none
  | _ => none

/-- The 64-bit word at slot `i`. -/
def rdW (σ : VEnv) (i : Nat) : Option (BitVec 64) :=
  match getAt σ i with
  | some ⟨.sword 64, w⟩ => some w
  | _ => none

/-- Evaluate an indexed expression; the operations are those of `SExpr.evalBV`. -/
def evalIE (σ : VEnv) : IE → Option (BitVec 64)
  | .var i => rdW σ i
  | .lit n => some (BitVec.ofNat 64 n)
  | .add a b => (evalIE σ a).bind fun x => (evalIE σ b).map fun y => x + y
  | .sub a b => (evalIE σ a).bind fun x => (evalIE σ b).map fun y => x - y
  | .mul a b => (evalIE σ a).bind fun x => (evalIE σ b).map fun y => x * y
  | .and a b => (evalIE σ a).bind fun x => (evalIE σ b).map fun y => x &&& y
  | .xor a b => (evalIE σ a).bind fun x => (evalIE σ b).map fun y => x ^^^ y
  | .shl a b => (evalIE σ a).bind fun x => (evalIE σ b).map fun y =>
      x <<< VIR.shiftMask 64 y.toNat
  | .shr a b => (evalIE σ a).bind fun x => (evalIE σ b).map fun y =>
      x >>> VIR.shiftMask 64 y.toNat
  | .mulHiU a b => (evalIE σ a).bind fun x => (evalIE σ b).map fun y =>
      BitVec.ofNat 64 (sexprMulHiU x.toNat y.toNat)

/-- Run an indexed straight-line program on a value environment. An expression
    assignment binds its destination to the word value and nothing else; loads
    and stores act on bound `memref` slots at bound word indices. -/
def runIdx : IL → VEnv → Option VEnv
  | .skip, σ => some σ
  | .seq a b, σ => (runIdx a σ).bind (runIdx b)
  | .setLit x n, σ => some (setAt σ x ⟨.sword 64, BitVec.ofNat 64 n⟩)
  | .setE x e, σ => (evalIE σ e).map fun v => setAt σ x ⟨.sword 64, v⟩
  | .load d a i, σ =>
      match getAt σ a, rdW σ i with
      | some ⟨.memref _, arr⟩, some iv => some (setAt σ d ⟨.sword 64, memGetDyn arr iv.toNat⟩)
      | _, _ => none
  | .store a i s ty, σ =>
      match getAt σ a, rdW σ i, rdW σ s with
      | some ⟨.memref n, arr⟩, some iv, some v =>
          if ty = .memref n then some (setAt σ a ⟨.memref n, memSetDyn arr iv.toNat v⟩)
          else none
      | _, _, _ => none

/-- Intern and run a program on an indexed environment. -/
def runProg (tbl : List String) (p : LowCT) (σ : VEnv) : Option VEnv :=
  (intern tbl p).bind fun ip => runIdx ip σ

/-! ## Soundness -/

theorem rdW_some {σ : VEnv} {i : Nat} {w : BitVec 64} (h : rdW σ i = some w) :
    getAt σ i = some ⟨.sword 64, w⟩ := by
  unfold rdW at h
  split at h
  · rename_i w' heq; cases h; exact heq
  · cases h

theorem envReader_of_eq {E : SEnvScalar} {x : String} {w : BitVec 64}
    (h : E x = some ⟨.sword 64, w⟩) : envReader E x = w := by
  simp only [envReader, h]

theorem envReadU64_of_eq {E : SEnvScalar} {x : String} {w : BitVec 64}
    (h : E x = some ⟨.sword 64, w⟩) : (envReadU64 E x).isSome = true := by
  simp only [envReadU64, h, Option.isSome_some]

/-- An interned expression evaluates to the `SExpr.evalBV` value over the
    denoted environment, and every variable it reads is a bound word there. -/
theorem evalIE_sound {tbl : List String} {σ : VEnv} {base : SEnvScalar} :
    ∀ (e : SExpr) (ie : IE) (v : BitVec 64), internE tbl e = some ie → evalIE σ ie = some v →
      v = e.evalBV (envReader (toS tbl σ base)) ∧ wordsBoundB (toS tbl σ base) e = true := by
  intro e
  induction e with
  | SVar x =>
      intro ie v hi hv
      obtain ⟨i, hx, rfl⟩ := Option.map_eq_some_iff.mp hi
      have hs := toS_at (base := base) hx (rdW_some hv)
      refine ⟨(envReader_of_eq hs).symm, ?_⟩
      simp only [wordsBoundB, sexprVars, List.all_cons, List.all_nil, Bool.and_true,
        envReadU64_of_eq hs]
  | SLit n =>
      intro ie v hi hv
      simp only [internE, Option.some.injEq] at hi
      subst hi
      simp only [evalIE, Option.some.injEq] at hv
      exact ⟨hv.symm, rfl⟩
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro ie v hi hv
      obtain ⟨ia, ha, hi⟩ := Option.bind_eq_some_iff.mp hi
      obtain ⟨ib, hb, rfl⟩ := Option.map_eq_some_iff.mp hi
      obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hv
      obtain ⟨rfl, hba⟩ := iha ia x ha hx
      obtain ⟨rfl, hbb⟩ := ihb ib y hb hy
      simp only [wordsBoundB, sexprVars, List.all_append] at hba hbb ⊢
      exact ⟨rfl, by simp [hba, hbb]⟩
  | _ => intro ie v hi; simp [internE] at hi

theorem sigma_cast {a b : CryptoTy} (h : a = b) (w : ⟦b⟧) :
    (⟨a, h.symm ▸ w⟩ : SVal) = ⟨b, w⟩ := by
  subst h; rfl

/-- **Soundness of the indexed evaluator.** When `p` interns to `ip` and `ip` runs
    from `σ` to `σ'`, `semScalar p` runs from every environment agreeing with
    `toS tbl σ base` off the temporaries to one agreeing with `toS tbl σ' base`. -/
theorem runIdx_sound {tbl : List String} {base : SEnvScalar} :
    ∀ (p : LowCT) (ip : IL) {σ σ' : VEnv} {env : SEnvScalar}, intern tbl p = some ip →
      runIdx ip σ = some σ' → SrcAgree env (toS tbl σ base) →
      ∃ env', semScalar p env = some env' ∧ SrcAgree env' (toS tbl σ' base)
  | .RSkip, ip, σ, σ', env, hi, hr, hag => by
      simp only [intern, Option.some.injEq] at hi; subst hi
      simp only [runIdx, Option.some.injEq] at hr; subst hr
      exact ⟨env, rfl, hag⟩
  | .RAssert _, ip, σ, σ', env, hi, hr, hag => by
      simp only [intern, Option.some.injEq] at hi; subst hi
      simp only [runIdx, Option.some.injEq] at hr; subst hr
      exact ⟨env, rfl, hag⟩
  | .RSeq a b, ip, σ, σ', env, hi, hr, hag => by
      obtain ⟨ia, ha, hi⟩ := Option.bind_eq_some_iff.mp hi
      obtain ⟨ib, hb, rfl⟩ := Option.map_eq_some_iff.mp hi
      obtain ⟨σ1, h1, h2⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨e1, hr1, ha1⟩ := runIdx_sound a ia ha h1 hag
      obtain ⟨e2, hr2, ha2⟩ := runIdx_sound b ib hb h2 ha1
      exact ⟨e2, by simp only [semScalar, hr1, Option.bind_some, hr2], ha2⟩
  | .RBlock b, ip, σ, σ', env, hi, hr, hag => by
      simpa only [semScalar] using runIdx_sound b ip hi hr hag
  | .RScalarSet x n, ip, σ, σ', env, hi, hr, hag => by
      simp only [intern] at hi
      split at hi
      · obtain ⟨ix, hx, rfl⟩ := Option.map_eq_some_iff.mp hi
        simp only [runIdx, Option.some.injEq] at hr; subst hr
        refine ⟨_, rfl, ?_⟩
        rw [toS_setAt hx]
        exact hag.upd x _
      · cases hi
  | .RScalarSetExpr x e, ip, σ, σ', env, hi, hr, hag => by
      simp only [intern] at hi
      split at hi
      · rename_i hck
        simp only [Bool.and_eq_true] at hck
        have hcl := srcCleanB_sound e hck.2
        obtain ⟨ix, hx, hi⟩ := Option.bind_eq_some_iff.mp hi
        obtain ⟨ie, he, rfl⟩ := Option.map_eq_some_iff.mp hi
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨rfl, hb⟩ := evalIE_sound (base := base) e ie v he hv
        obtain ⟨env2, hrun, hotb⟩ :=
          GuardedAgree.semScalar_setExpr (x := x) hcl (varsIn_of_wordsBoundB hag e hcl hb)
        refine ⟨_, hrun, ?_⟩
        rw [toS_setAt hx, ← hag.evalBV e hcl]
        intro s hs
        simp only [SEnvScalar.upd]
        split
        · rfl
        · exact (hotb s (Or.inl hs)).trans (hag s hs)
      · cases hi
  | .RArrLoad ⟨d, dt⟩ src i, ip, σ, σ', env, hi, hr, hag => by
      cases dt <;> simp only [intern] at hi <;> try cases hi
      split at hi
      · rename_i hck
        simp only [Bool.and_eq_true] at hck
        obtain ⟨⟨_, hs⟩, hii⟩ := hck
        obtain ⟨id, hid, hi⟩ := Option.bind_eq_some_iff.mp hi
        obtain ⟨ia, hia, hi⟩ := Option.bind_eq_some_iff.mp hi
        obtain ⟨ii, hii', rfl⟩ := Option.map_eq_some_iff.mp hi
        simp only [runIdx] at hr
        split at hr
        · rename_i n arr iv hA hI
          simp only [Option.some.injEq] at hr; subst hr
          have hA' : env src.locVar = some ⟨.memref n, arr⟩ :=
            (hag _ (notTmp hs)).trans (toS_at hia hA)
          have hI' : env i = some ⟨.sword 64, iv⟩ :=
            (hag _ (notTmp hii)).trans (toS_at hii' (rdW_some hI))
          refine ⟨_, by simp only [semScalar, hA', hI']; rfl, ?_⟩
          rw [toS_setAt hid]
          exact hag.upd d _
        · cases hr
      · cases hi
  | .RArrStore arr i src, ip, σ, σ', env, hi, hr, hag => by
      simp only [intern] at hi
      split at hi
      · rename_i hck
        simp only [Bool.and_eq_true] at hck
        obtain ⟨⟨ha, hii⟩, hs⟩ := hck
        obtain ⟨ia, hia, hi⟩ := Option.bind_eq_some_iff.mp hi
        obtain ⟨ii, hii', hi⟩ := Option.bind_eq_some_iff.mp hi
        obtain ⟨is, his, rfl⟩ := Option.map_eq_some_iff.mp hi
        simp only [runIdx] at hr
        split at hr
        · rename_i n a iv v hA hI hS
          split at hr
          · rename_i hty
            simp only [Option.some.injEq] at hr; subst hr
            have hA' : env arr.locVar = some ⟨.memref n, a⟩ :=
              (hag _ (notTmp ha)).trans (toS_at hia hA)
            have hI' : env i = some ⟨.sword 64, iv⟩ :=
              (hag _ (notTmp hii)).trans (toS_at hii' (rdW_some hI))
            have hS' : env src.locVar = some ⟨.sword 64, v⟩ :=
              (hag _ (notTmp hs)).trans (toS_at his (rdW_some hS))
            refine ⟨_, by simp only [semScalar, hA', hI', hS', dif_pos hty]; rfl, ?_⟩
            rw [toS_setAt hia]
            intro s hsn
            simp only [SEnvScalar.upd]
            split
            · exact congrArg some (sigma_cast hty _)
            · exact hag s hsn
          · cases hr
        · cases hr
      · cases hi
  | .RLetZero _ _ _, _, _, _, _, hi, _, _
  | .RLetU64Zero _ _, _, _, _, _, hi, _, _
  | .RCall _ _ _, _, _, _, _, hi, _, _
  | .RCallSwap _ _ _ _, _, _, _, _, hi, _, _
  | .RCloneCall _ _ _ _ _ _, _, _, _, _, hi, _, _
  | .RIfNz _ _ _, _, _, _, _, hi, _, _
  | .RWhileNz _ _, _, _, _, _, hi, _, _
  | .RFor _ _ _, _, _, _, _, hi, _, _
  | .RLimbStore _ _ _, _, _, _, _, hi, _, _
  | .RLimbStoreExpr _ _ _, _, _, _, _, hi, _, _
  | .RCallN _ _ _, _, _, _, _, hi, _, _
  | .RSelect _ _ _ _, _, _, _, _, hi, _, _
  | .RFnDef _ _ _ _ _, _, _, _, _, hi, _, _
  | .RFnCall _ _ _, _, _, _, _, hi, _, _
  | .RTupleLoad _ _ _, _, _, _, _, hi, _, _
  | .RArrStoreLit _ _ _, _, _, _, _, hi, _, _
  | .RArrLoadLit _ _ _, _, _, _, _, hi, _, _
  | .RCallDstThreaded _ _ _, _, _, _, _, hi, _, _
  | .RForRuntime _ _ _, _, _, _, _, hi, _, _
  | .RCopy _ _, _, _, _, _, hi, _, _ => by simp [intern] at hi

/-- **The evaluator from a base environment.** When `runProg tbl p` succeeds on the
    table names read out of `base`, `semScalar p base` runs, and off the
    temporaries its result is the evaluator's environment over `base`. -/
theorem runProg_sound {tbl : List String} {p : LowCT} {base : SEnvScalar}
    (h : (runProg tbl p (tbl.map base)).isSome = true) :
    ∃ env', semScalar p base = some env' ∧
      SrcAgree env' (toS tbl ((runProg tbl p (tbl.map base)).get h) base) := by
  obtain ⟨ip, hi, hr⟩ := Option.bind_eq_some_iff.mp (Option.some_get h).symm
  refine runIdx_sound (base := base) p ip hi hr ?_
  rw [toS_map]
  exact SrcAgree.refl base

end CatCrypt.Crypto.SecureCompilation.Dialects.ScalarStraightRun
