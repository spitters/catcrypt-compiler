/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTWordOps
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

/-!
# Straight-line simulation of the word-operation front in `semScalar`

The per-binding simulation between the hax semantics `denote` of an
A-normalised straight-line body and the value semantics `semScalar` of its
lowering by `haxToLowCT` and `scalarizeWordOps`.  Words are related as a hax
`.int n` with `n < 2^64` against the `.sword 64` slot `BitVec.ofNat 64 n`, and
arrays as a hax `.array` of `.int` words against a `.memref n` slot, cell by cell
through `memGetDyn`.

The array arms of `semScalar` read and write only when the load destination is
typed `.TU64` and the stored array's type encodes as the `.memref` of its slot.
The front types the destination of an `index` load `.TFp` and the array of an
`array_update` store `.TBytes 0`; on those types `semScalar` binds the opaque
default (`semScalar_load_TFp`).  `typeWordArrays` retypes the array accesses of a
program on a table of array lengths, and the step lemmas are stated on the
retyped shapes.

## Main definitions

* `WordAt`, `ArrAt`, `EnvRelW` — the environment relation.
* `WordBuiltins` — the facts the builtin table evaluates the word calls,
  `index` and `array_update` by.
* `WordBuiltins'` — the same facts with the word calls restricted to results
  below `2^64`, the bound every binding carries in `WBind.Ok`; the simulation
  theorems assume it.
* `WBind`, `bindsHax`, `bindsLow`, `bindsNext`, `bindsScope`, `BindsOk` — the
  straight-line bindings, their hax and `LowCT` forms, the hax environment after
  them, the related names after them and their side conditions.
* `typeWordArrays` — the retyping of the array accesses.

## Main results

* `WordBuiltins.toBounded` — `WordBuiltins` implies `WordBuiltins'`.
* `step_word`, `step_lit`, `step_load`, `step_store` — one binding preserves
  `EnvRelW`, with the hax run and the `semScalar` run each reduced to the run of
  the continuation.
* `denote_letBind_mulHiChain` — the unfused multiply-high binding runs as the
  fused `mulhi#64` binding.
* `binds_sim`, `segment_sim` — a sequence of bindings preserves `EnvRelW`.
* `semScalar_load_TFp` — on the front's load type the destination is the
  opaque default, which is no `u64` slot.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.WordOpsSim

open _root_.Hax (ImpExpr ImpLit Value Env Builtins denote denoteArgs)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar semScalar envReader envReadU64 semLowerSExpr binNode isTmpName isTmpName_tmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar (semScalar_rLetZero)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)

/-! ### The environment relation -/

/-- The natural number held by a hax name bound to `.int`, else `0`. -/
def natOf (env : Env) (x : String) : Nat :=
  match env x with
  | some (.int n) => n.toNat
  | _ => 0

/-- The list held by a hax name bound to `.array`, else `[]`. -/
def arrOf (env : Env) (x : String) : List Value :=
  match env x with
  | some (.array vs) => vs
  | _ => []

/-- `x` holds a word below `2^64`: `.int n` in hax and `BitVec.ofNat 64 n` at
    `.sword 64` in the scalar environment. -/
def WordAt (env : Env) (σ : SEnvScalar) (x : String) : Prop :=
  ∃ n : Nat, n < 2 ^ 64 ∧ env x = some (.int n) ∧
    σ x = some ⟨.sword 64, (BitVec.ofNat 64 n : BitVec 64)⟩

/-- `x` holds an array of `len` words: a hax `.array` of length `len` whose cell
    `j` is `.int` of cell `j` of the `.memref len` slot. -/
def ArrAt (env : Env) (σ : SEnvScalar) (x : String) (len : Nat) : Prop :=
  ∃ (vs : List Value) (a : Fin len → BitVec 64), env x = some (.array vs) ∧
    σ x = some ⟨.memref len, a⟩ ∧ vs.length = len ∧
    ∀ j, j < len → vs[j]? = some (.int (memGetDyn a j).toNat)

/-- The hax environment `env` and the scalar environment `σ` agree on the words
    `S` and on the arrays `A` (name and length), none of which is a temporary
    of the scalar-expression lowering. -/
structure EnvRelW (env : Env) (σ : SEnvScalar) (S : List String)
    (A : List (String × Nat)) : Prop where
  word : ∀ x ∈ S, WordAt env σ x
  arr : ∀ p ∈ A, ArrAt env σ p.1 p.2
  wordClean : ∀ x ∈ S, ¬ isTmpName x
  arrClean : ∀ p ∈ A, ¬ isTmpName p.1

theorem WordAt.natOf_eq {env : Env} {σ : SEnvScalar} {x : String} (h : WordAt env σ x) :
    natOf env x < 2 ^ 64 ∧ env x = some (.int (natOf env x)) ∧
      envReadU64 σ x = some (BitVec.ofNat 64 (natOf env x)) := by
  obtain ⟨n, hn, he, hs⟩ := h
  simp only [natOf, envReadU64, he, hs, Int.toNat_natCast]
  exact ⟨hn, trivial, trivial⟩

theorem ArrAt.len_eq {env : Env} {σ : SEnvScalar} {x : String} {n m : Nat}
    (h₁ : ArrAt env σ x n) (h₂ : ArrAt env σ x m) : n = m := by
  obtain ⟨_, a, _, ha, _⟩ := h₁
  obtain ⟨_, b, _, hb, _⟩ := h₂
  rw [ha] at hb
  have := (Sigma.mk.inj_iff.mp (Option.some.inj hb)).1
  exact CryptoTy.memref.inj this

theorem WordAt.ne_of_arrAt {env : Env} {σ : SEnvScalar} {x y : String} {n : Nat}
    (hx : WordAt env σ x) (hy : ArrAt env σ y n) : x ≠ y := by
  rintro rfl
  obtain ⟨_, _, he, _⟩ := hx
  obtain ⟨_, _, he', _⟩ := hy
  rw [he] at he'
  cases he'

/-- Writing the word slot `x` preserves the relation on the other names and
    adds `x`. -/
theorem EnvRelW.update {env env' : Env} {σ σ' : SEnvScalar} {S : List String}
    {A : List (String × Nat)} (h : EnvRelW env σ S A) (x : String) (hxT : ¬ isTmpName x)
    (hxA : ∀ p ∈ A, p.1 ≠ x) (henv : ∀ y, y ≠ x → env' y = env y)
    (hσ : ∀ y, y ≠ x → ¬ isTmpName y → σ' y = σ y) (hnew : WordAt env' σ' x) :
    EnvRelW env' σ' (x :: S) A where
  word y hy := by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hnew
    · by_cases hyx : y = x
      · subst hyx; exact hnew
      · obtain ⟨n, hn, he, hs⟩ := h.word y hy
        exact ⟨n, hn, by rw [henv y hyx, he], by rw [hσ y hyx (h.wordClean y hy), hs]⟩
  arr p hp := by
    obtain ⟨vs, a, he, hs, hl, hc⟩ := h.arr p hp
    exact ⟨vs, a, by rw [henv _ (hxA p hp), he], by rw [hσ _ (hxA p hp) (h.arrClean p hp), hs],
      hl, hc⟩
  wordClean y hy := by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxT
    · exact h.wordClean y hy
  arrClean := h.arrClean

/-- Writing the array slot `arr` of length `n` preserves the relation on the
    other names. -/
theorem EnvRelW.update_arr {env env' : Env} {σ σ' : SEnvScalar} {S : List String}
    {A : List (String × Nat)} (h : EnvRelW env σ S A) (arr : String) (n : Nat)
    (hmem : (arr, n) ∈ A) (henv : ∀ y, y ≠ arr → env' y = env y)
    (hσ : ∀ y, y ≠ arr → σ' y = σ y) (hnew : ArrAt env' σ' arr n) :
    EnvRelW env' σ' S A where
  word y hy := by
    have hne : y ≠ arr := (h.word y hy).ne_of_arrAt (h.arr _ hmem)
    obtain ⟨m, hm, he, hs⟩ := h.word y hy
    exact ⟨m, hm, by rw [henv y hne, he], by rw [hσ y hne, hs]⟩
  arr p hp := by
    by_cases hpa : p.1 = arr
    · have hlen : p.2 = n := by
        have h1 := h.arr p hp
        rw [hpa] at h1
        exact h1.len_eq (h.arr _ hmem)
      rw [hpa, hlen]; exact hnew
    · obtain ⟨vs, a, he, hs, hl, hc⟩ := h.arr p hp
      exact ⟨vs, a, by rw [henv _ hpa, he], by rw [hσ _ hpa, hs], hl, hc⟩
  wordClean := h.wordClean
  arrClean := h.arrClean

/-! ### The builtin table -/

/-- The facts the builtin table evaluates the straight-line bindings by: every
    word call of `wordOpNames` on two words below `2^64` as `wordOpNat`, an
    `index` read of an `.int` cell, and an in-range `array_update`. -/
structure WordBuiltins (bi : Builtins) : Prop where
  word : ∀ f ∈ wordOpNames, ∀ n m : Nat, n < 2 ^ 64 → m < 2 ^ 64 →
    bi f [.int n, .int m] = (wordOpNat f n m).map (fun r : Nat => Value.int r)
  index : ∀ (vs : List Value) (i w : Nat), vs[i]? = some (.int w) →
    bi "index" [.array vs, .int i] = some (.int w)
  update : ∀ (vs : List Value) (i : Nat) (v : Value), i < vs.length →
    bi "array_update" [.array vs, .int i, v] = some (.array (vs.set i v))

/-- The facts a builtin table evaluates the straight-line bindings by: every word
    call of `wordOpNames` on two words below `2^64` whose `wordOpNat` result is
    below `2^64` returns that result, an `index` read of an `.int` cell, and an
    in-range `array_update`. -/
structure WordBuiltins' (bi : Builtins) : Prop where
  word : ∀ f ∈ wordOpNames, ∀ n m r : Nat, n < 2 ^ 64 → m < 2 ^ 64 →
    wordOpNat f n m = some r → r < 2 ^ 64 → bi f [.int n, .int m] = some (.int r)
  index : ∀ (vs : List Value) (i w : Nat), vs[i]? = some (.int w) →
    bi "index" [.array vs, .int i] = some (.int w)
  update : ∀ (vs : List Value) (i : Nat) (v : Value), i < vs.length →
    bi "array_update" [.array vs, .int i, v] = some (.array (vs.set i v))

/-- `WordBuiltins` implies `WordBuiltins'`. -/
theorem WordBuiltins.toBounded {bi : Builtins} (h : WordBuiltins bi) : WordBuiltins' bi where
  word f hf n m r hn hm hr _ := by rw [h.word f hf n m hn hm, hr]; rfl
  index := h.index
  update := h.update

/-! ### Cells of a memref -/

theorem memGetDyn_memSetDyn {n : Nat} (a : Fin n → BitVec 64) {i j : Nat} (hi : i < n)
    (hj : j < n) (v : BitVec 64) :
    memGetDyn (memSetDyn a i v) j = if j = i then v else memGetDyn a j := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [memGetDyn, memSetDyn, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj, Fin.mk.injEq]

/-! ### Scalar-expression lowering of a word call -/

/-- The scalar expression of a word call on two `u64` slots lowers to one fresh
    temporary. -/
theorem semLowerSExpr_wordOp {f a b : String} {se : SExpr}
    (hse : wordOpSExpr f (.SVar a) (.SVar b) = some se) {τ : SEnvScalar} {va vb : BitVec 64}
    (ha : envReadU64 τ a = some va) (hb : envReadU64 τ b = some vb) :
    ∃ w : BitVec 64, semLowerSExpr τ 0 se =
      some (τ.upd (tmpName 0) (t := .sword 64) w, tmpName 0, 1) := by
  unfold wordOpSExpr at hse
  split at hse <;> cases hse <;> simp [semLowerSExpr, binNode, ha, hb]

theorem envReader_of_envReadU64 {σ : SEnvScalar} {x : String} {w : BitVec 64}
    (h : envReadU64 σ x = some w) : envReader σ x = w := by
  unfold envReadU64 at h
  unfold envReader
  split at h <;> simp_all

theorem envReadU64_upd_ne {σ : SEnvScalar} {x y : String} {t : CryptoTy} (v : t.denote)
    (h : y ≠ x) : envReadU64 (σ.upd x v) y = envReadU64 σ y := by
  simp [envReadU64, SEnvScalar.upd, h]

theorem upd_ne {σ : SEnvScalar} {x y : String} {t : CryptoTy} (v : t.denote) (h : y ≠ x) :
    σ.upd x v y = σ y := by
  simp [SEnvScalar.upd, h]

theorem upd_self {σ : SEnvScalar} {x : String} {t : CryptoTy} (v : t.denote) :
    σ.upd x v x = some ⟨t, v⟩ := by
  simp [SEnvScalar.upd]

theorem ne_tmpName_of_not_isTmpName {y : String} (h : ¬ isTmpName y) (k : Nat) :
    y ≠ tmpName k := fun e => h (e ▸ isTmpName_tmpName k)

theorem extend_ne {env : Env} {x y : String} (v : Value) (h : y ≠ x) :
    env.extend x v y = env y := by
  simp [Env.extend, h]

theorem extend_self {env : Env} {x : String} (v : Value) : env.extend x v x = some v := by
  simp [Env.extend]

/-! ### The array arms of `semScalar` -/

theorem semScalar_rSeq (c₁ c₂ : LowCT) (σ : SEnvScalar) :
    semScalar (.RSeq c₁ c₂) σ = (semScalar c₁ σ).bind (semScalar c₂) := rfl

/-- A load into a `.TU64` destination reads cell `i` of the array slot. -/
theorem semScalar_arrLoad {σ : SEnvScalar} {x arr i : String} {ta : TowerType} {n : Nat}
    {a : Fin n → BitVec 64} {iv : BitVec 64} (ha : σ arr = some ⟨.memref n, a⟩)
    (hi : σ i = some ⟨.sword 64, iv⟩) :
    semScalar (.RArrLoad ⟨x, .TU64⟩ ⟨arr, ta⟩ i) σ =
      some (σ.upd x (t := .sword 64) (memGetDyn a iv.toNat)) := by
  simp [semScalar, Located.locDst, ha, hi]

/-- A store into an array whose type encodes as the `.memref` of its slot writes
    cell `i`. -/
theorem semScalar_arrStore {σ : SEnvScalar} {arr i v : String} {ta tv : TowerType} {n : Nat}
    {a : Fin n → BitVec 64} {iv vv : BitVec 64} (hty : encodeTy ta = .memref n)
    (ha : σ arr = some ⟨.memref n, a⟩) (hi : σ i = some ⟨.sword 64, iv⟩)
    (hv : σ v = some ⟨.sword 64, vv⟩) :
    ∃ σ', semScalar (.RArrStore ⟨arr, ta⟩ i ⟨v, tv⟩) σ = some σ' ∧
      σ' arr = some ⟨.memref n, memSetDyn a iv.toNat vv⟩ ∧ ∀ y, y ≠ arr → σ' y = σ y := by
  simp only [semScalar, Located.locDst, ha, hi, hv, hty, dite_true]
  refine ⟨_, rfl, ?_, fun y hy => upd_ne _ hy⟩
  rw [upd_self]
  congr 1
  exact Sigma.ext hty (by simp)

/-- On the front's load type `.TFp` the destination is bound to the opaque
    default of `encodeTy .TFp`. -/
theorem semScalar_load_TFp (σ : SEnvScalar) (x arr i : String) (t ta : TowerType)
    (body : LowCT) :
    semScalar (.RLetZero x t (.RSeq (.RArrLoad ⟨x, .TFp⟩ ⟨arr, ta⟩ i) body)) σ =
      semScalar body (σ.upd x (t := encodeTy .TFp) (CryptoTy.default (encodeTy .TFp))) := by
  simp [semScalar, Located.locDst]

/-- The opaque default of the front's load type is no `u64` slot. -/
theorem envReadU64_load_TFp (σ : SEnvScalar) (x : String) :
    envReadU64 (σ.upd x (t := encodeTy .TFp) (CryptoTy.default (encodeTy .TFp))) x = none := by
  simp [envReadU64, SEnvScalar.upd, encodeTy]

/-! ### The hax run of a call on variables -/

theorem denoteArgs_vars_run (bi : Builtins) (fuel : Nat) (env : Env) :
    ∀ (args : List String) (vals : List Value), args.map env = vals.map some →
      (denoteArgs bi fuel (args.map ImpExpr.var)).run env = (some vals, env)
  | [], [], _ => by unfold denoteArgs; rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, v :: vs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [List.map_cons, denoteArgs_cons_run_eq, denote_var_run_eq, h.1]
    simp only [denoteArgs_vars_run bi fuel env as vs h.2, Option.map_some]

/-- A binding of a call on variables bound to `vals` runs its body in the
    environment extended by the builtin's value. -/
theorem denote_letBind_app_run (bi : Builtins) (fuel : Nat) (x f : String)
    (args : List String) (vals : List Value) (v : Value) (body : ImpExpr) (env : Env)
    (hargs : args.map env = vals.map some) (hbi : bi f vals = some v) :
    (denote bi fuel (.letBind x (.app f (args.map ImpExpr.var)) body)).run env =
      (denote bi fuel body).run (env.extend x v) := by
  rw [denote_letBind_run_eq, denote_app_run_eq, denoteArgs_vars_run bi fuel env args vals hargs]
  simp only [hbi]

/-! ### The step lemmas -/

/-- **Word-call binding.** `let x = f(a, b)` on two related words runs in hax
    to the binding of `x` to the call's value `r`, and its lowering
    `RLetU64Zero x (RSeq (RScalarSetExpr x se) _)` runs in `semScalar` to a
    scalar environment related to it with `x` added. -/
theorem step_word {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S : List String} {A : List (String × Nat)} (h : EnvRelW env σ S A)
    {x f a b : String} {se : SExpr} (hf : f ∈ wordOpNames)
    (hse : wordOpSExpr f (.SVar a) (.SVar b) = some se) (ha : a ∈ S) (hb : b ∈ S)
    (hax : a ≠ x) (hbx : b ≠ x) (hxT : ¬ isTmpName x) (hxA : ∀ p ∈ A, p.1 ≠ x)
    {r : Nat} (hr : wordOpNat f (natOf env a) (natOf env b) = some r) (hlt : r < 2 ^ 64)
    (body : ImpExpr) (bodyC : LowCT) :
    (denote bi fuel (.letBind x (.app f [.var a, .var b]) body)).run env =
        (denote bi fuel body).run (env.extend x (.int r)) ∧
      ∃ σ', semScalar (.RLetU64Zero x (.RSeq (.RScalarSetExpr x se) bodyC)) σ =
          semScalar bodyC σ' ∧ EnvRelW (env.extend x (.int r)) σ' (x :: S) A := by
  obtain ⟨haL, haE, haR⟩ := (h.word a ha).natOf_eq
  obtain ⟨hbL, hbE, hbR⟩ := (h.word b hb).natOf_eq
  refine ⟨?_, ?_⟩
  · exact denote_letBind_app_run bi fuel x f [a, b] [.int (natOf env a), .int (natOf env b)]
      _ body env (by simp [haE, hbE]) (hbi.word f hf _ _ _ haL hbL hr hlt)
  · have hτa : envReadU64 (σ.upd x (t := .sword 64) (0 : BitVec 64)) a =
        some (BitVec.ofNat 64 (natOf env a)) := by rw [envReadU64_upd_ne _ hax, haR]
    have hτb : envReadU64 (σ.upd x (t := .sword 64) (0 : BitVec 64)) b =
        some (BitVec.ofNat 64 (natOf env b)) := by rw [envReadU64_upd_ne _ hbx, hbR]
    obtain ⟨w, hlow⟩ := semLowerSExpr_wordOp hse hτa hτb
    have hval : SExpr.evalBV (envReader (σ.upd x (t := .sword 64) (0 : BitVec 64))) se =
        BitVec.ofNat 64 r := by
      apply BitVec.eq_of_toNat_eq
      rw [wordOpSExpr_evalBV _ hse ?_ hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      simp only [SExpr.evalBV, envReader_of_envReadU64 hτa, envReader_of_envReadU64 hτb,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt haL, Nat.mod_eq_of_lt hbL]
      exact hr
    refine ⟨((σ.upd x (t := .sword 64) (0 : BitVec 64)).upd (tmpName 0) (t := .sword 64) w).upd
      x (t := .sword 64) (BitVec.ofNat 64 r), ?_, ?_⟩
    · simp only [semScalar, hlow, hval, Option.bind_some]
    · refine h.update x hxT hxA (fun y hy => extend_ne _ hy) (fun y hy hyT => ?_)
        ⟨r, hlt, extend_self _, upd_self _⟩
      rw [upd_ne _ hy, upd_ne _ (ne_tmpName_of_not_isTmpName hyT 0), upd_ne _ hy]

/-- **Literal binding.** `let x = k` for `k < 2^64` runs in hax to the binding of
    `x` to `.int k`, and its lowering `RLetU64Zero x (RSeq (RScalarSet x k) _)` to
    a related scalar environment with `x` added. -/
theorem step_lit (bi : Builtins) (fuel : Nat) {env : Env} {σ : SEnvScalar} {S : List String}
    {A : List (String × Nat)} (h : EnvRelW env σ S A) {x : String} {k : Nat}
    (hk : k < 2 ^ 64) (hxT : ¬ isTmpName x) (hxA : ∀ p ∈ A, p.1 ≠ x)
    (body : ImpExpr) (bodyC : LowCT) :
    (denote bi fuel (.letBind x (.lit (.int k)) body)).run env =
        (denote bi fuel body).run (env.extend x (.int k)) ∧
      ∃ σ', semScalar (.RLetU64Zero x (.RSeq (.RScalarSet x k) bodyC)) σ =
          semScalar bodyC σ' ∧ EnvRelW (env.extend x (.int k)) σ' (x :: S) A := by
  refine ⟨?_, ?_⟩
  · rw [denote_letBind_run_eq, denote_lit_eq]
    rfl
  · refine ⟨(σ.upd x (t := .sword 64) (0 : BitVec 64)).upd x (t := .sword 64) (BitVec.ofNat 64 k),
      by simp only [semScalar, Option.bind_some], ?_⟩
    refine h.update x hxT hxA (fun y hy => extend_ne _ hy) (fun y hy _ => ?_)
      ⟨k, hk, extend_self _, upd_self _⟩
    rw [upd_ne _ hy, upd_ne _ hy]

/-- **Load binding.** `let x = index(arr, i)` with `i` below the length `n` of the
    related array `arr` runs in hax to the binding of `x` to cell `i`, and its
    lowering with a `.TU64` destination to a related scalar environment with `x`
    added. -/
theorem step_load {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S : List String} {A : List (String × Nat)} (h : EnvRelW env σ S A)
    {x arr i : String} {n : Nat} (t ta : TowerType) (hA : (arr, n) ∈ A) (hi : i ∈ S)
    (hxT : ¬ isTmpName x) (hxA : ∀ p ∈ A, p.1 ≠ x) (hin : natOf env i < n)
    (body : ImpExpr) (bodyC : LowCT) :
    ∃ w : Nat, w < 2 ^ 64 ∧ (arrOf env arr)[natOf env i]? = some (.int w) ∧
      (denote bi fuel (.letBind x (.app "index" [.var arr, .var i]) body)).run env =
        (denote bi fuel body).run (env.extend x (.int w)) ∧
      ∃ σ', semScalar (.RLetZero x t (.RSeq (.RArrLoad ⟨x, .TU64⟩ ⟨arr, ta⟩ i) bodyC)) σ =
          semScalar bodyC σ' ∧ EnvRelW (env.extend x (.int w)) σ' (x :: S) A := by
  obtain ⟨vs, a, he, hs, _, hc⟩ := h.arr _ hA
  obtain ⟨hiL, hiE, hiR⟩ := (h.word i hi).natOf_eq
  have hσi : σ i = some ⟨.sword 64, BitVec.ofNat 64 (natOf env i)⟩ := by
    obtain ⟨m, _, he', hs'⟩ := h.word i hi
    rw [hs']
    rw [hiE] at he'
    simp only [Option.some.injEq, Value.int.injEq, Nat.cast_inj] at he'
    rw [he']
  have hcell := hc _ hin
  have harr : arrOf env arr = vs := by simp [arrOf, he]
  refine ⟨(memGetDyn a (natOf env i)).toNat, (memGetDyn a _).isLt, by rw [harr]; exact hcell,
    ?_, ?_⟩
  · exact denote_letBind_app_run bi fuel x "index" [arr, i] [.array vs, .int (natOf env i)]
      _ body env (by simp [he, hiE]) (hbi.index vs _ _ hcell)
  · refine ⟨σ.upd x (t := .sword 64) (memGetDyn a (natOf env i)), ?_, ?_⟩
    · rw [semScalar_rLetZero, semScalar_rSeq, semScalar_arrLoad hs hσi, Option.bind_some,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hiL]
    · refine h.update x hxT hxA (fun y hy => extend_ne _ hy) (fun y hy _ => upd_ne _ hy)
        ⟨_, (memGetDyn a _).isLt, extend_self _, ?_⟩
      rw [upd_self, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **Store binding.** `let arr = array_update(arr, i, v)` with `i` below the length
    `n` of the related array `arr` runs in hax to the binding of `arr` to the
    updated list, and its lowering `RSeq (RArrStore _ i _) _`, on an array type
    encoding as `.memref n`, to a related scalar environment. -/
theorem step_store {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S : List String} {A : List (String × Nat)} (h : EnvRelW env σ S A)
    {arr i v : String} {n : Nat} (ta tv : TowerType) (hA : (arr, n) ∈ A)
    (hty : encodeTy ta = .memref n) (hi : i ∈ S) (hv : v ∈ S) (hin : natOf env i < n)
    (body : ImpExpr) (bodyC : LowCT) :
    (denote bi fuel (.letBind arr (.app "array_update" [.var arr, .var i, .var v]) body)).run
        env = (denote bi fuel body).run (env.extend arr
          (.array ((arrOf env arr).set (natOf env i) (.int (natOf env v))))) ∧
      ∃ σ', semScalar (.RSeq (.RArrStore ⟨arr, ta⟩ i ⟨v, tv⟩) bodyC) σ = semScalar bodyC σ' ∧
        EnvRelW (env.extend arr
          (.array ((arrOf env arr).set (natOf env i) (.int (natOf env v))))) σ' S A := by
  obtain ⟨vs, a, he, hs, hl, hc⟩ := h.arr _ hA
  obtain ⟨hiL, hiE, hiR⟩ := (h.word i hi).natOf_eq
  obtain ⟨hvL, hvE, hvR⟩ := (h.word v hv).natOf_eq
  have hσ : ∀ y, y ∈ S → σ y = some ⟨.sword 64, BitVec.ofNat 64 (natOf env y)⟩ := by
    intro y hy
    obtain ⟨m, _, he', hs'⟩ := h.word y hy
    rw [hs']
    rw [(h.word y hy).natOf_eq.2.1] at he'
    simp only [Option.some.injEq, Value.int.injEq, Nat.cast_inj] at he'
    rw [he']
  have harr : arrOf env arr = vs := by simp [arrOf, he]
  obtain ⟨σ', hrun, hσa, hσo⟩ := semScalar_arrStore (tv := tv) hty hs (hσ i hi) (hσ v hv)
  refine ⟨?_, σ', ?_, ?_⟩
  · rw [harr]
    exact denote_letBind_app_run bi fuel arr "array_update" [arr, i, v]
      [.array vs, .int (natOf env i), .int (natOf env v)] _ body env (by simp [he, hiE, hvE])
      (hbi.update vs _ _ (by omega))
  · rw [semScalar_rSeq, hrun, Option.bind_some]
  · refine h.update_arr arr n hA (fun y hy => extend_ne _ hy) hσo ?_
    rw [harr]
    refine ⟨_, _, extend_self _, hσa, by simp [hl], fun j hj => ?_⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hiL,
      memGetDyn_memSetDyn a (by omega) hj, List.getElem?_set]
    by_cases hji : j = natOf env i
    · subst hji
      simp [hl, hin, BitVec.toNat_ofNat]
      omega
    · simp [Ne.symm hji, hji, hc j hj]

/-- The binding of the unfused multiply-high idiom on two words runs as the
    binding of the call `mulhi#64`. -/
theorem denote_letBind_mulHiChain {bi : Builtins} (hbi : MulHiBuiltins bi) (fuel : Nat)
    (env : Env) (x a b : String) (n m : Nat) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (ha : env a = some (.int n)) (hb : env b = some (.int m)) (body : ImpExpr) :
    (denote bi fuel (.letBind x (mulHiChain (.var a) (.var b)) body)).run env =
      (denote bi fuel (.letBind x (.app mulHiCallName [.var a, .var b]) body)).run env := by
  rw [denote_letBind_run_eq, denote_letBind_run_eq,
    denote_mulHiChain hbi fuel env a b n m hn hm ha hb]

/-! ### Straight-line sequences -/

/-- A straight-line binding: a word call, a literal, an array load and an array
    store, with the tower types the lowering carries. -/
inductive WBind where
  | word (x f a b : String)
  | lit (x : String) (k : Nat)
  | load (x arr i : String) (t ta : TowerType)
  | store (arr i v : String) (ta tv : TowerType)

namespace WBind

/-- The hax binding with continuation `k`. -/
def hax : WBind → ImpExpr → ImpExpr
  | .word x f a b, k => .letBind x (.app f [.var a, .var b]) k
  | .lit x n, k => .letBind x (.lit (.int n)) k
  | .load x arr i _ _, k => .letBind x (.app "index" [.var arr, .var i]) k
  | .store arr i v _ _, k => .letBind arr (.app "array_update" [.var arr, .var i, .var v]) k

/-- The lowered binding with continuation `k`. -/
def low : WBind → LowCT → LowCT
  | .word x f a b, k =>
      .RLetU64Zero x
        (.RSeq (.RScalarSetExpr x ((wordOpSExpr f (.SVar a) (.SVar b)).getD (.SLit 0))) k)
  | .lit x n, k => .RLetU64Zero x (.RSeq (.RScalarSet x n) k)
  | .load x arr i t ta, k => .RLetZero x t (.RSeq (.RArrLoad ⟨x, .TU64⟩ ⟨arr, ta⟩ i) k)
  | .store arr i v ta tv, k => .RSeq (.RArrStore ⟨arr, ta⟩ i ⟨v, tv⟩) k

/-- The hax environment after the binding. -/
def next : WBind → Env → Env
  | .word x f a b, env =>
      env.extend x (.int ((wordOpNat f (natOf env a) (natOf env b)).getD 0))
  | .lit x n, env => env.extend x (.int n)
  | .load x arr i _ _, env => env.extend x ((arrOf env arr)[natOf env i]?.getD (.int 0))
  | .store arr i v _ _, env =>
      env.extend arr (.array ((arrOf env arr).set (natOf env i) (.int (natOf env v))))

/-- The word names the binding writes. -/
def written : WBind → List String
  | .word x _ _ _ => [x]
  | .lit x _ => [x]
  | .load x _ _ _ _ => [x]
  | .store _ _ _ _ _ => []

/-- The side conditions of the binding on the related words `S`, the related
    arrays `A` and the hax environment `env`. -/
def Ok (S : List String) (A : List (String × Nat)) (env : Env) : WBind → Prop
  | .word x f a b => f ∈ wordOpNames ∧ a ∈ S ∧ b ∈ S ∧ a ≠ x ∧ b ≠ x ∧ ¬ isTmpName x ∧
      (∀ p ∈ A, p.1 ≠ x) ∧ ∃ r, wordOpNat f (natOf env a) (natOf env b) = some r ∧ r < 2 ^ 64
  | .lit x n => n < 2 ^ 64 ∧ ¬ isTmpName x ∧ ∀ p ∈ A, p.1 ≠ x
  | .load x arr i _ _ => i ∈ S ∧ ¬ isTmpName x ∧ (∀ p ∈ A, p.1 ≠ x) ∧
      ∃ n, (arr, n) ∈ A ∧ natOf env i < n
  | .store arr i v ta _ => i ∈ S ∧ v ∈ S ∧
      ∃ n, (arr, n) ∈ A ∧ encodeTy ta = .memref n ∧ natOf env i < n

/-- One binding preserves `EnvRelW`, adding its written names. -/
theorem sim {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S : List String} {A : List (String × Nat)} (h : EnvRelW env σ S A)
    (b : WBind) (hok : b.Ok S A env) (k : ImpExpr) (kC : LowCT) :
    (denote bi fuel (b.hax k)).run env = (denote bi fuel k).run (b.next env) ∧
      ∃ σ', semScalar (b.low kC) σ = semScalar kC σ' ∧
        EnvRelW (b.next env) σ' (b.written ++ S) A := by
  cases b with
  | word x f a b =>
    obtain ⟨hf, ha, hb, hax, hbx, hxT, hxA, r, hr, hlt⟩ := hok
    obtain ⟨se, hse⟩ := Option.isSome_iff_exists.mp
      (by rw [wordOpSExpr_isSome]; exact List.elem_iff.mpr hf :
        (wordOpSExpr f (.SVar a) (.SVar b)).isSome)
    simp only [WBind.hax, WBind.low, WBind.next, WBind.written, hr, hse, Option.getD_some,
      List.singleton_append]
    exact step_word hbi fuel h hf hse ha hb hax hbx hxT hxA hr hlt k kC
  | lit x n =>
    obtain ⟨hn, hxT, hxA⟩ := hok
    exact step_lit bi fuel h hn hxT hxA k kC
  | load x arr i t ta =>
    obtain ⟨hi, hxT, hxA, n, hA, hin⟩ := hok
    obtain ⟨w, _, hw, h1, h2⟩ := step_load hbi fuel h t ta hA hi hxT hxA hin k kC
    simp only [WBind.hax, WBind.low, WBind.next, WBind.written, hw, Option.getD_some,
      List.singleton_append]
    exact ⟨h1, h2⟩
  | store arr i v ta tv =>
    obtain ⟨hi, hv, n, hA, hty, hin⟩ := hok
    exact step_store hbi fuel h ta tv hA hty hi hv hin k kC

end WBind

/-- A sequence of bindings in hax, with continuation `k`. -/
def bindsHax : List WBind → ImpExpr → ImpExpr
  | [], k => k
  | b :: bs, k => b.hax (bindsHax bs k)

/-- A sequence of bindings lowered, with continuation `k`. -/
def bindsLow : List WBind → LowCT → LowCT
  | [], k => k
  | b :: bs, k => b.low (bindsLow bs k)

/-- The hax environment after a sequence of bindings. -/
def bindsNext : List WBind → Env → Env
  | [], env => env
  | b :: bs, env => bindsNext bs (b.next env)

/-- The related word names after a sequence of bindings. -/
def bindsScope : List WBind → List String → List String
  | [], S => S
  | b :: bs, S => bindsScope bs (b.written ++ S)

/-- The side conditions of a sequence of bindings, each at the hax environment
    it runs in. -/
def BindsOk (A : List (String × Nat)) : List WBind → List String → Env → Prop
  | [], _, _ => True
  | b :: bs, S, env => b.Ok S A env ∧ BindsOk A bs (b.written ++ S) (b.next env)

/-- **Straight-line composition.** A sequence of bindings whose side conditions
    hold runs in hax to its continuation in `bindsNext bs env`, and its lowering
    runs in `semScalar` to its continuation in a scalar environment related to
    `bindsNext bs env` on `bindsScope bs S` and `A`. -/
theorem binds_sim {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat)
    (A : List (String × Nat)) :
    ∀ (bs : List WBind) (S : List String) (env : Env) (σ : SEnvScalar),
      EnvRelW env σ S A → BindsOk A bs S env → ∀ (k : ImpExpr) (kC : LowCT),
      (denote bi fuel (bindsHax bs k)).run env = (denote bi fuel k).run (bindsNext bs env) ∧
        ∃ σ', semScalar (bindsLow bs kC) σ = semScalar kC σ' ∧
          EnvRelW (bindsNext bs env) σ' (bindsScope bs S) A
  | [], _, _, σ, h, _, _, _ => ⟨rfl, σ, rfl, h⟩
  | b :: bs, S, env, σ, h, hok, k, kC => by
    obtain ⟨h1, σ₁, h2, h3⟩ := b.sim hbi fuel h hok.1 (bindsHax bs k) (bindsLow bs kC)
    obtain ⟨i1, σ₂, i2, i3⟩ := binds_sim hbi fuel A bs _ _ σ₁ h3 hok.2 k kC
    exact ⟨h1.trans i1, σ₂, h2.trans i2, i3⟩

/-- **Segment.** A sequence of bindings ending in a variable bound after it,
    followed by `()`, as the front emits an `array_update` statement: the hax run
    and the `semScalar` run of `RSeq (RSeq _ RSkip) _` each reach their
    continuation in related environments. -/
theorem segment_sim {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat)
    {A : List (String × Nat)} {bs : List WBind} {S : List String} {env : Env}
    {σ : SEnvScalar} (h : EnvRelW env σ S A) (hok : BindsOk A bs S env) (y : String)
    (hy : ∃ v, bindsNext bs env y = some v) (k : ImpExpr) (kC : LowCT) :
    (denote bi fuel (.seq (.seq (bindsHax bs (.var y)) .unitVal) k)).run env =
        (denote bi fuel k).run (bindsNext bs env) ∧
      ∃ σ', semScalar (.RSeq (.RSeq (bindsLow bs .RSkip) .RSkip) kC) σ = semScalar kC σ' ∧
        EnvRelW (bindsNext bs env) σ' (bindsScope bs S) A := by
  obtain ⟨v, hv⟩ := hy
  obtain ⟨h1, σ', h2, h3⟩ := binds_sim hbi fuel A bs S env σ h hok (.var y) .RSkip
  refine ⟨?_, σ', ?_, h3⟩
  · rw [denote_seq_run_eq, denote_seq_run_eq, h1, denote_var_run_eq, hv]
    simp only [denote_unitVal_eq]
  · rw [semScalar_rSeq, semScalar_rSeq, h2]
    rfl

/-! ### Retyping the array accesses -/

/-- The array accesses of a program retyped on a table `len` of array lengths:
    a load from an array in `len` gets a `.TU64` destination, and a store into
    an array of length `n` in `len` gets the array type `.TBytes (8 * n)`. -/
def typeWordArrays (len : String → Option Nat) : LowCT → LowCT
  | .RArrLoad dst src i =>
      if (len src.locVar).isSome then .RArrLoad ⟨dst.locVar, .TU64⟩ src i
      else .RArrLoad dst src i
  | .RArrStore arr i src =>
      match len arr.locVar with
      | some n => .RArrStore ⟨arr.locVar, .TBytes (8 * n)⟩ i src
      | none => .RArrStore arr i src
  | .RSeq a b => .RSeq (typeWordArrays len a) (typeWordArrays len b)
  | .RLetZero x t b => .RLetZero x t (typeWordArrays len b)
  | .RLetU64Zero x b => .RLetU64Zero x (typeWordArrays len b)
  | .RIfNz v t e => .RIfNz v (typeWordArrays len t) (typeWordArrays len e)
  | .RWhileNz v b => .RWhileNz v (typeWordArrays len b)
  | .RFor x n b => .RFor x n (typeWordArrays len b)
  | .RForRuntime x bound b => .RForRuntime x bound (typeWordArrays len b)
  | .RBlock b => .RBlock (typeWordArrays len b)
  | c => c

/-- The store type `typeWordArrays` gives an array of `n` words encodes as
    `.memref n`. -/
theorem encodeTy_TBytes_eight_mul (n : Nat) : encodeTy (.TBytes (8 * n)) = .memref n := by
  simp only [encodeTy, CryptoTy.memref.injEq]
  omega

end CatCrypt.Crypto.Hax.WordOpsSim
