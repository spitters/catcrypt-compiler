/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxSpine
public import CatCrypt.Crypto.Hax.Hax64Table
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

@[expose] public section

set_option autoImplicit false

/-!
# A tuple result of an array and one of its words

A function body whose statement spine ends in the tail `let y = a[k]; (a, y)` returns the
array `a` together with its word at the index `k`. `stripArrTailE` replaces that tail by `a`:
the body then returns the array alone, the result the word-array route compiles. A run of the
body reading to a value is matched by a run of the stripped body reading to the array `x`, and
the value is the pair of `x` and the word the table `bi` reads at the value of `k` in the
entry environment, when the spine keeps `k` (`keepsWordB`): no binder of the spine other than
`let k = k` names `k`, and no statement of the spine binds `k` (`frameOk`).

On the layout side, a layout whose result is `.tuple [.words r n, .wordAt r i]` reads back
that pair: the words at the entry value of `r`, and the word at the entry value of `r` plus
`8` times the entry value of `i`. `σ.arrPart` is the layout with the result `.words r n`;
the result read-back of the pair follows from that of the array (`resultOf_arrWordTail`).

## Main results

* `arrTailE`, `stripArrTailE`, `spineArrTail`, `keepsWordB` — the tail, the stripped body,
  the tail's names on the spine, and the check that the spine keeps the index.
* `stripArrTailT`, `erase_stripArrTailT` — the stripped typed body, which erases to the
  stripped body.
* `spine_letBind_run`, `spine_seq_run` and their `_val`, `_cf`, `_nval` forms, `arrTail_run` —
  the runs of the spine steps and of the tail.
* `denoteSpine_stripArrTail` — a run of the body reading to a value is matched by a run of
  the stripped body, the value being the pair of the array and its word at the index.
* `AbiLayout.arrPart`, `arrPart_regions`, `arrPart_envOf`, `resultOf_arrWordTail` — the array
  part of a layout with a pair result, which has the entry conditions of the layout, and the
  read-back of the pair.
* `arrWordTailOf`, `arrWordTailOf_spec`, `envOf_scalarArg`, `index_int_words` — the data of a
  pair result, and the facts its composition reads.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open _root_.Hax (ImpExpr TExpr TExprKind ImpType Value Env Builtins Outcome denote'
  denoteArgs')
open _root_.Hax.InlineLocalClosures (denoteSpine frameOk IsErr tuple_run)
open _root_.Hax.ContinueFlag (var_run app_run args_cons_run args_nil_run)
open CatCrypt.Crypto.Hax (isLamE denoteSpine_letBind denoteSpine_seq spineLetStep spineSeqStep
  denote'_keeps)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)

/-! ## 1. The tail and the stripped body -/

/-- The tail `let y = a[k]; (a, y)` with `y ≠ a`: the names `a` and `k`. -/
def arrTailE : ImpExpr → Option (String × String)
  | .letBind y (.app "index" [.var a, .var k]) (.tuple [.var a', .var y']) =>
      if a' = a ∧ y' = y ∧ y ≠ a then some (a, k) else none
  | _ => none

/-- The body with the tail `let y = a[k]; (a, y)` at the end of its spine replaced by `a`. -/
def stripArrTailE : ImpExpr → ImpExpr
  | .letBind y v c =>
      match arrTailE (.letBind y v c) with
      | some (a, _) => .var a
      | none => .letBind y v (stripArrTailE c)
  | .seq a b => .seq a (stripArrTailE b)
  | e => e

/-- The names `a` and `k` of the tail `let y = a[k]; (a, y)` at the end of the spine. -/
def spineArrTail : ImpExpr → Option (String × String)
  | .letBind y v c =>
      match arrTailE (.letBind y v c) with
      | some p => some p
      | none => spineArrTail c
  | .seq _ b => spineArrTail b
  | _ => none

/-- The binding `let k = k`. -/
def isSelfBind (k y : String) : ImpExpr → Bool
  | .var x => x == k && y == k
  | _ => false

/-- **The spine keeps the word `k`**: no binder of the spine before the tail names `k` unless
    it is `let k = k`, no bound expression or statement of the spine binds `k` (`frameOk`), and
    no bound expression is a closure. -/
def keepsWordB (k : String) : ImpExpr → Bool
  | .letBind y v c =>
      match arrTailE (.letBind y v c) with
      | some _ => true
      | none => (y != k || isSelfBind k y v) && !isLamE v &&
          frameOk (fun _ => true) (· != k) (fun _ => true) v && keepsWordB k c
  | .seq a b => frameOk (fun _ => true) (· != k) (fun _ => true) a && keepsWordB k b
  | _ => true

/-- The type of the first component of a tuple, and otherwise the node type. -/
def tupleHeadTy : TExpr → ImpType
  | .mk (.tuple (.mk _ ta :: _)) _ => ta
  | .mk _ t => t

/-- **The stripped typed body**: the tail `let y = a[k]; (a, y)` at the end of the spine
    replaced by `a`, at the type of the tuple's first component. -/
def stripArrTailT : TExpr → TExpr
  | .mk (.letBind y v c) t =>
      match arrTailE (.letBind y v.erase c.erase) with
      | some (a, _) => .mk (.var a) (tupleHeadTy c)
      | none => .mk (.letBind y v (stripArrTailT c)) t
  | .mk (.seq a b) t => .mk (.seq a (stripArrTailT b)) t
  | .mk (.ann e) t => .mk (.ann (stripArrTailT e)) t
  | e => e

theorem stripArrTailE_of_not_spine {e : ImpExpr} (h1 : ∀ y v c, e ≠ .letBind y v c)
    (h2 : ∀ a b, e ≠ .seq a b) : stripArrTailE e = e := by
  unfold stripArrTailE
  split
  · exact absurd rfl (h1 _ _ _)
  · exact absurd rfl (h2 _ _)
  · rfl

/-- The stripped typed body erases to the stripped body. -/
theorem erase_stripArrTailT : ∀ te : TExpr, (stripArrTailT te).erase = stripArrTailE te.erase := by
  intro te
  fun_induction stripArrTailT te with
  | case1 y v c t a k h =>
      simp only [TExpr.erase, stripArrTailE, h]
  | case2 y v c t h ih =>
      simp only [TExpr.erase, stripArrTailE, h, ih]
  | case3 a b t ih =>
      simp only [TExpr.erase, stripArrTailE, ih]
  | case4 e t ih =>
      simp only [TExpr.erase, ih]
  | case5 e h1 h2 h3 =>
      obtain ⟨k, t⟩ := e
      refine (stripArrTailE_of_not_spine (fun y v c he => ?_) (fun a b he => ?_)).symm
      · cases k with
        | letBind => exact h1 _ _ _ _ rfl
        | ann => exact h3 _ _ rfl
        | break_ o => cases o <;> simp [TExpr.erase] at he
        | _ => simp [TExpr.erase] at he
      · cases k with
        | seq => exact h2 _ _ _ rfl
        | ann => exact h3 _ _ rfl
        | break_ o => cases o <;> simp [TExpr.erase] at he
        | _ => simp [TExpr.erase] at he

/-! ## 2. The runs -/

theorem args_cons_val {bi : Builtins} {fuel : Nat} {e : ImpExpr} {es : List ImpExpr}
    {env e1 : Env} {x : Value} (h : (denote' bi fuel e).run env = (.val x, e1))
    (hx : x.isControlFlow = false) :
    (denoteArgs' bi fuel (e :: es)).run env =
      (((denoteArgs' bi fuel es).run e1).1.map (x :: ·), ((denoteArgs' bi fuel es).run e1).2) := by
  rw [args_cons_run, h]
  cases x <;> simp_all [Value.isControlFlow]

theorem args_cons_cf {bi : Builtins} {fuel : Nat} {e : ImpExpr} {es : List ImpExpr}
    {env e1 : Env} {x : Value} (h : (denote' bi fuel e).run env = (.val x, e1))
    (hx : x.isControlFlow = true) : (denoteArgs' bi fuel (e :: es)).run env = (none, e1) := by
  rw [args_cons_run, h]
  cases x <;> simp_all [Value.isControlFlow]

theorem spine_letBind_run (bi : Builtins) (fuel : Nat) (x : String) {v : ImpExpr} (c : ImpExpr)
    (hv : isLamE v = false) (env : Env) :
    (denoteSpine bi fuel (.letBind x v c)).run env =
      match (denote' bi fuel v).run env with
      | (.val (.controlFlow b w), e1) => (.val (.controlFlow b w), e1)
      | (.val w, e1) => (denoteSpine bi fuel c).run (e1.extend x w)
      | (o, e1) => (o, e1) := by
  rw [denoteSpine_letBind _ _ _ _ _ hv]
  simp only [spineLetStep, StateT.run, bind, StateT.bind, pure, modify, modifyGet,
    MonadStateOf.modifyGet]
  rcases (denote' bi fuel v) env with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _ <;> try rfl
  cases w <;> rfl

theorem spine_seq_run (bi : Builtins) (fuel : Nat) (a b : ImpExpr) (env : Env) :
    (denoteSpine bi fuel (.seq a b)).run env =
      match (denote' bi fuel a).run env with
      | (.val (.controlFlow k w), e1) => (.val (.controlFlow k w), e1)
      | (.val _, e1) => (denoteSpine bi fuel b).run e1
      | (o, e1) => (o, e1) := by
  rw [denoteSpine_seq]
  simp only [spineSeqStep, StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel a) env with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _ <;> try rfl
  cases w <;> rfl

theorem spine_letBind_val (bi : Builtins) (fuel : Nat) (x : String) {v : ImpExpr} (c : ImpExpr)
    (hv : isLamE v = false) {env e1 : Env} {w : Value}
    (h : (denote' bi fuel v).run env = (.val w, e1)) (hw : w.isControlFlow = false) :
    (denoteSpine bi fuel (.letBind x v c)).run env = (denoteSpine bi fuel c).run (e1.extend x w) := by
  rw [spine_letBind_run _ _ _ _ hv, h]
  cases w <;> simp_all [Value.isControlFlow]

theorem spine_letBind_cf (bi : Builtins) (fuel : Nat) (x : String) {v : ImpExpr} (c : ImpExpr)
    (hv : isLamE v = false) {env e1 : Env} {w : Value}
    (h : (denote' bi fuel v).run env = (.val w, e1)) (hw : w.isControlFlow = true) :
    (denoteSpine bi fuel (.letBind x v c)).run env = (.val w, e1) := by
  rw [spine_letBind_run _ _ _ _ hv, h]
  cases w <;> simp_all [Value.isControlFlow]

theorem spine_letBind_nval (bi : Builtins) (fuel : Nat) (x : String) {v : ImpExpr} (c : ImpExpr)
    (hv : isLamE v = false) {env e1 : Env} {o : Outcome}
    (h : (denote' bi fuel v).run env = (o, e1)) (ho : ∀ w, o ≠ .val w) :
    (denoteSpine bi fuel (.letBind x v c)).run env = (o, e1) := by
  rw [spine_letBind_run _ _ _ _ hv, h]
  cases o with
  | val w => exact absurd rfl (ho w)
  | _ => rfl

theorem spine_seq_val (bi : Builtins) (fuel : Nat) (a b : ImpExpr) {env e1 : Env} {w : Value}
    (h : (denote' bi fuel a).run env = (.val w, e1)) (hw : w.isControlFlow = false) :
    (denoteSpine bi fuel (.seq a b)).run env = (denoteSpine bi fuel b).run e1 := by
  rw [spine_seq_run, h]
  cases w <;> simp_all [Value.isControlFlow]

theorem spine_seq_cf (bi : Builtins) (fuel : Nat) (a b : ImpExpr) {env e1 : Env} {w : Value}
    (h : (denote' bi fuel a).run env = (.val w, e1)) (hw : w.isControlFlow = true) :
    (denoteSpine bi fuel (.seq a b)).run env = (.val w, e1) := by
  rw [spine_seq_run, h]
  cases w <;> simp_all [Value.isControlFlow]

theorem spine_seq_nval (bi : Builtins) (fuel : Nat) (a b : ImpExpr) {env e1 : Env} {o : Outcome}
    (h : (denote' bi fuel a).run env = (o, e1)) (ho : ∀ w, o ≠ .val w) :
    (denoteSpine bi fuel (.seq a b)).run env = (o, e1) := by
  rw [spine_seq_run, h]
  cases o with
  | val w => exact absurd rfl (ho w)
  | _ => rfl

theorem spineLetStep_val {x : String} {w : Value} {k : StateM Env Outcome}
    (hw : w.isControlFlow = false) :
    spineLetStep x (.val w) k = (do modify (Env.extend · x w); k) := by
  cases w <;> simp_all [spineLetStep, Value.isControlFlow]

theorem spineLetStep_cf {x : String} {w : Value} {k : StateM Env Outcome}
    (hw : w.isControlFlow = true) : spineLetStep x (.val w) k = pure (.val w) := by
  cases w <;> simp_all [spineLetStep, Value.isControlFlow]

/-- **The run of the tail.** At an environment binding `a` to `x` and `k` to `kv`, a run of the
    tail reading to a value `v` reads `x` and `kv` with `bi` at `"index"` to a word `w`, and `v`
    is `w` when `w` is a control-flow value, and the pair `(x, w)` otherwise; `x` is no
    control-flow value. -/
theorem arrTail_run (bi : Builtins) (fuel : Nat) {y a k : String} (hya : y ≠ a) {env env' : Env}
    {x kv v : Value} (hx : env a = some x) (hk : env k = some kv)
    (hr : (denoteSpine bi fuel (.letBind y (.app "index" [.var a, .var k])
      (.tuple [.var a, .var y]))).run env = (.val v, env')) :
    x.isControlFlow = false ∧ ∃ w, bi "index" [x, kv] = some w ∧
      ((w.isControlFlow = true ∧ v = w) ∨ v = .tuple [x, w]) := by
  have hxa : (denote' bi fuel (.var a)).run env = (.val x, env) := by rw [var_run, hx]
  have hka : (denote' bi fuel (.var k)).run env = (.val kv, env) := by rw [var_run, hk]
  have herr : ∀ m, (denote' bi fuel (.app "index" [.var a, .var k])).run env = (.err m, env) →
      False := fun m he => by
    rw [spine_letBind_nval _ _ _ _ rfl he (fun _ h => by cases h)] at hr
    cases hr
  cases hxc : x.isControlFlow with
  | true =>
      exact (herr _ (by rw [app_run, args_cons_cf hxa hxc])).elim
  | false =>
      refine ⟨rfl, ?_⟩
      cases hkc : kv.isControlFlow with
      | true =>
          exact (herr _ (by rw [app_run, args_cons_val hxa hxc, args_cons_cf hka hkc]; rfl)).elim
      | false =>
          have hargs : (denoteArgs' bi fuel [.var a, .var k]).run env = (some [x, kv], env) := by
            rw [args_cons_val hxa hxc, args_cons_val hka hkc, args_nil_run]; rfl
          cases hb : bi "index" [x, kv] with
          | none => exact (herr _ (by rw [app_run, hargs]; simp only [hb]; rfl)).elim
          | some w =>
              refine ⟨w, rfl, ?_⟩
              have happ : (denote' bi fuel (.app "index" [.var a, .var k])).run env =
                  (.val w, env) := by rw [app_run, hargs]; simp only [hb]
              cases hwc : w.isControlFlow with
              | true =>
                  rw [spine_letBind_cf _ _ _ _ rfl happ hwc] at hr
                  cases hr
                  exact Or.inl ⟨rfl, rfl⟩
              | false =>
                  right
                  rw [spine_letBind_val _ _ _ _ rfl happ hwc] at hr
                  have hT : denoteSpine bi fuel (.tuple [.var a, .var y]) =
                      denote' bi fuel (.tuple [.var a, .var y]) := rfl
                  rw [hT, tuple_run] at hr
                  have hxa' : (denote' bi fuel (.var a)).run (env.extend y w) =
                      (.val x, env.extend y w) := by
                    rw [var_run, Env.extend_other _ _ _ _ (Ne.symm hya), hx]
                  have hya' : (denote' bi fuel (.var y)).run (env.extend y w) =
                      (.val w, env.extend y w) := by
                    rw [var_run, Env.extend_same]
                  rw [args_cons_val hxa' hxc, args_cons_val hya' hwc, args_nil_run] at hr
                  cases hr
                  rfl

theorem arrTailE_some {e : ImpExpr} {a k : String} (h : arrTailE e = some (a, k)) :
    ∃ y, e = .letBind y (.app "index" [.var a, .var k]) (.tuple [.var a, .var y]) ∧ y ≠ a := by
  unfold arrTailE at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, hy⟩ := hc
      cases h
      exact ⟨_, rfl, hy⟩
    · cases h
  · cases h

/-- **The stripped body.** Let the spine of `e` end in the tail `let y = a[k]; (a, y)` and keep
    `k` (`keepsWordB`), and let `env` bind `k` to `kv`. Every run of `e` from `env` reading to
    a value `v` is matched by a run of the stripped body reading to a value `x`: either `x` is a
    control-flow value and `v = x`, or `bi` reads `x` and `kv` at `"index"` to a word `w`, and
    `v` is `w` when `w` is a control-flow value and the pair `(x, w)` otherwise. -/
theorem denoteSpine_stripArrTail (bi : Builtins) (fuel : Nat) :
    ∀ (e : ImpExpr) {a k : String} {kv : Value}, spineArrTail e = some (a, k) →
      keepsWordB k e = true → ∀ {env env' : Env} {v : Value}, env k = some kv →
      (denoteSpine bi fuel e).run env = (.val v, env') →
      ∃ x env'', (denoteSpine bi fuel (stripArrTailE e)).run env = (.val x, env'') ∧
        ((x.isControlFlow = true ∧ v = x) ∨ (x.isControlFlow = false ∧ ∃ w,
          bi "index" [x, kv] = some w ∧ ((w.isControlFlow = true ∧ v = w) ∨ v = .tuple [x, w]))) := by
  intro e
  fun_induction spineArrTail e with
  | case1 y v c p hp =>
      intro a k kv hs _ env env' w hk hr
      cases hs
      obtain ⟨y', he, hya⟩ := arrTailE_some hp
      cases he
      have hstrip : stripArrTailE (.letBind y (.app "index" [.var a, .var k])
          (.tuple [.var a, .var y])) = .var a := by
        simp only [stripArrTailE, hp]
      rw [hstrip]
      cases hxa : env a with
      | none =>
          exfalso
          have he : (denote' bi fuel (.app "index" [.var a, .var k])).run env =
              (.err "non-value in function arguments", env) := by
            rw [app_run, args_cons_run, var_run, hxa]
          rw [spine_letBind_nval _ _ _ _ rfl he (fun _ h => by cases h)] at hr
          cases hr
      | some x =>
          obtain ⟨hxc, w', hw, hv⟩ := arrTail_run bi fuel hya hxa hk hr
          refine ⟨x, env, ?_, Or.inr ⟨hxc, w', hw, hv⟩⟩
          show (denote' bi fuel (.var a)).run env = _
          rw [var_run, hxa]
  | case2 y v c hp ih =>
      intro a k kv hs hkeep env env' w hk hr
      simp only [keepsWordB, hp, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
        Bool.not_eq_true'] at hkeep
      obtain ⟨⟨⟨hyk, hlam⟩, hfr⟩, hc⟩ := hkeep
      have hstrip : stripArrTailE (.letBind y v c) = .letBind y v (stripArrTailE c) := by
        simp only [stripArrTailE, hp]
      rw [hstrip]
      rcases hrv : (denote' bi fuel v).run env with ⟨o, e1⟩
      cases o with
      | val u =>
          cases huc : u.isControlFlow with
          | true =>
              rw [spine_letBind_cf _ _ _ _ hlam hrv huc] at hr
              cases hr
              exact ⟨_, _, spine_letBind_cf _ _ _ _ hlam hrv huc, Or.inl ⟨huc, rfl⟩⟩
          | false =>
              rw [spine_letBind_val _ _ _ _ hlam hrv huc] at hr
              have hk2 : (e1.extend y u) k = some kv := by
                by_cases hy : y = k
                · subst hy
                  have hself : isSelfBind y y v = true := by
                    rcases hyk with h | h
                    · exact absurd rfl h
                    · exact h
                  cases v with
                  | var z =>
                      simp only [isSelfBind, Bool.and_eq_true, beq_iff_eq] at hself
                      obtain ⟨rfl, -⟩ := hself
                      rw [var_run, hk] at hrv
                      cases hrv
                      exact Env.extend_same _ _ _
                  | _ => simp [isSelfBind] at hself
                · rw [Env.extend_other _ _ _ _ (Ne.symm hy),
                    denote'_keeps bi v hfr fuel env hrv (fun ⟨_, h⟩ => by cases h), hk]
              obtain ⟨x, env'', hrs, hres⟩ := ih hs hc hk2 hr
              exact ⟨x, env'', by rw [spine_letBind_val _ _ _ _ hlam hrv huc]; exact hrs, hres⟩
      | _ =>
          rw [spine_letBind_nval _ _ _ _ hlam hrv (fun _ h => by cases h)] at hr
          cases hr
  | case3 s b ih =>
      intro a k kv hs hkeep env env' w hk hr
      simp only [keepsWordB, Bool.and_eq_true] at hkeep
      obtain ⟨hfr, hb⟩ := hkeep
      show ∃ x env'', (denoteSpine bi fuel (.seq s (stripArrTailE b))).run env = (.val x, env'') ∧ _
      rcases hrv : (denote' bi fuel s).run env with ⟨o, e1⟩
      cases o with
      | val u =>
          cases huc : u.isControlFlow with
          | true =>
              rw [spine_seq_cf _ _ _ _ hrv huc] at hr
              cases hr
              exact ⟨_, _, spine_seq_cf _ _ _ _ hrv huc, Or.inl ⟨huc, rfl⟩⟩
          | false =>
              rw [spine_seq_val _ _ _ _ hrv huc] at hr
              have hk2 : e1 k = some kv := by
                rw [denote'_keeps bi s hfr fuel env hrv (fun ⟨_, h⟩ => by cases h), hk]
              obtain ⟨x, env'', hrs, hres⟩ := ih hs hb hk2 hr
              exact ⟨x, env'', by rw [spine_seq_val _ _ _ _ hrv huc]; exact hrs, hres⟩
      | _ =>
          rw [spine_seq_nval _ _ _ _ hrv (fun _ h => by cases h)] at hr
          cases hr
  | case4 => intro a k kv hs; cases hs

/-! ## 3. The layout of a pair result -/

/-- The array part of a layout whose result is the pair `.tuple [.words r n, .wordAt r i]`: the
    layout with the result `.words r n`; any other layout unchanged. -/
def AbiLayout.arrPart (σ : AbiLayout) : AbiLayout :=
  match σ.result with
  | .tuple [.words r n, .wordAt _ _] => { σ with result := .words r n }
  | _ => σ

theorem arrPart_regions (σ : AbiLayout) (sa : AState) : σ.arrPart.Regions sa ↔ σ.Regions sa := by
  unfold AbiLayout.arrPart
  split <;> exact Iff.rfl

theorem arrPart_envOf (σ : AbiLayout) (sa : AState) (env : Env) :
    σ.arrPart.EnvOf sa env ↔ σ.EnvOf sa env := by
  unfold AbiLayout.arrPart
  split <;> exact Iff.rfl

theorem arrPart_consts (σ : AbiLayout) : σ.arrPart.consts = σ.consts := by
  unfold AbiLayout.arrPart
  split <;> rfl

theorem arrPart_args (σ : AbiLayout) : σ.arrPart.args = σ.args := by
  unfold AbiLayout.arrPart
  split <;> rfl

/-- **The read-back of a pair result.** For a layout with the result
    `.tuple [.words r n, .wordAt r i]`, if the array part reads back `x` and the table reads `x`
    at the entry value of `i` to `w`, the layout reads back the pair `(x, w)`. -/
theorem resultOf_arrWordTail {σ : AbiLayout} {r i : String} {n : Nat}
    (hres : σ.result = .tuple [.words r n, .wordAt r i]) {sa sa' : AState} {x w : Value}
    (hx : σ.arrPart.ResultOf sa sa' x)
    (hw : CatCrypt.Crypto.Hax.hax64WExit "index" [x, .int ((sa.regs i).toNat : Int)] = some w) :
    σ.ResultOf sa sa' (.tuple [x, w]) := by
  have hx' : x = .array (wordsAt sa'.mem (sa.regs r) n) := by
    simp only [AbiLayout.arrPart, hres, AbiLayout.ResultOf, ResultKind.read] at hx
    exact hx
  subst hx'
  obtain ⟨hlt, rfl⟩ := CatCrypt.Crypto.Hax.hax64Builtins_index_int (by omega)
    (CatCrypt.Crypto.Hax.hax64WExit_sub hw)
  simp only [AbiLayout.ResultOf, hres, ResultKind.read, ResultKind.readList]
  simp [wordsAt]

/-! ## 4. The data of a pair result -/

/-- **The data of a pair result**: for a layout whose result is
    `.tuple [.words r n, .wordAt r i]` and a body whose spine ends in `let y = a[k]; (a, y)`,
    with `k` the scalar parameter in the register `i` and a spine that keeps `k`, the register
    `i` and the name `k`. -/
def arrWordTailOf (σ : AbiLayout) (e : ImpExpr) : Option (String × String) :=
  match σ.result, spineArrTail e with
  | .tuple [.words r _, .wordAt r' i], some (_, k) =>
      if r' = r ∧ (⟨k, i, .scalar⟩ : AbiArg) ∈ σ.args ∧ keepsWordB k e = true then some (i, k)
      else none
  | _, _ => none

theorem arrWordTailOf_spec {σ : AbiLayout} {e : ImpExpr} {i k : String}
    (h : arrWordTailOf σ e = some (i, k)) :
    ∃ r n a, σ.result = .tuple [.words r n, .wordAt r i] ∧ spineArrTail e = some (a, k) ∧
      (⟨k, i, .scalar⟩ : AbiArg) ∈ σ.args ∧ keepsWordB k e = true := by
  unfold arrWordTailOf at h
  split at h
  · rename_i r n r' i' a k' hσ ht
    split at h
    · rename_i hc
      obtain ⟨rfl, hk, hkeep⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨r', n, a, hσ, ht, hk, hkeep⟩
    · cases h
  · cases h

/-- An environment the layout reads off an entry state binds a scalar parameter to the integer
    of its register. -/
theorem envOf_scalarArg {σ : AbiLayout} {sa : AState} {env : Env} {k i : String}
    (hk : (⟨k, i, .scalar⟩ : AbiArg) ∈ σ.args) (henv : σ.EnvOf sa env) :
    env k = some (.int ((sa.regs i).toNat : Int)) :=
  henv.1 _ hk

/-- The table reads an array of integers at an index to an integer. -/
theorem index_int_words {zs : List Int} {kv w : Value}
    (hw : CatCrypt.Crypto.Hax.hax64WExit "index" [.array (zs.map .int), kv] = some w)
    {m : Nat} (hkv : kv = .int (m : Int)) : ∃ z : Int, w = .int z := by
  subst hkv
  obtain ⟨hlt, rfl⟩ := CatCrypt.Crypto.Hax.hax64Builtins_index_int (by omega)
    (CatCrypt.Crypto.Hax.hax64WExit_sub hw)
  simp

end CatCrypt.Crypto.SecureCompilation.Haxc
