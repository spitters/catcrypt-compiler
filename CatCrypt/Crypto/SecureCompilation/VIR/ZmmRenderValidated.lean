/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate
public import CatCrypt.Crypto.SecureCompilation.VIR.ComVarDepth
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapZmmD
public import Std.Data.String.ToNat

/-!
# The validated lane-map render and its soundness

`VpackZmmLinearRender.renderLaneMapZmmFunction` (64-bit lanes, `%zmm` or `%ymm`) and
`renderLaneMapZmmDFunction` (32-bit lanes) print the lane-wise widening of a scalar
straight-line program `c` through an unverified renderer. `renderValidated` and
`renderValidatedD` print the same text and return it only when
`ZmmTextValidate.validate` accepts it against the binding list the renderer read off
`c`, with the range facts the renderer took from `ComRange.rangeAnalysis`.

`renderValidated_sound` and `renderValidatedD_sound` compose `validate_sound` with two
links from the scalar program:

* the bindings (`collectWith_sat`): the valuation `traceEnv`, which gives each name the
  word it holds at the end of the scalar run on one lane, satisfies every binding the
  collector produces (`SatB`), for the covered fragment (`exprZBindScalar`,
  `exprZBindScalar32`);
* the range facts (`rfOf_mem`): when every input word of lane `k` is at most `B`, every
  interval of `rangeInfoOf` holds of the lane-`k` value of its name, by the soundness
  of the analysis (`ComRange.exprAbs_sound`) lane by lane.

The conclusion: running the parsed text on an input region whose lane `k` at the offset
of parameter `s` holds input `s` of lane `k` stores, at output slot `j` and lane `k`,
the value of binding `nBinds c - nOut + j` of the scalar run on lane `k`.

## Main definitions

* `envOf`, `traceEnv`, `bindWords`, `nBinds`: the scalar run by names.
* `rfOf`: the renderer's range facts as the validator's.
* `laneMapValidated`, `renderValidated`, `renderValidatedD`: the validated renders.

## Main results

* `traceEnv_lookup`, `traceEnv_bindWords`: the names hold the scalar values.
* `collectWith_sat`: link 1.
* `rfOf_mem`: link 2.
* `collectWith_scalar32_noOther`: the 32-bit binding map leaves no binding of a program
  covered by `LaneMapZmmD` outside the fragment.
* `laneMapValidated_sound`, `renderValidated_sound`, `renderValidatedD_sound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ZmmRenderValidated

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (VarMap argName paramsAndMap
  paramsAndMapFrom)
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender (ZBind LaneW collectWith
  exprZBindScalar exprZBindScalar32 renderZmmLinearBinds rangeInfoOf ivsConst bcast512d)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode MState run lane)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (SatB validate validate_sound
  lastOuts parse)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (JCtxt regAs regAs_reg AEnv EnvOK
  exprAbs exprAbs_sound analyze hget)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (Iv)

/-! ## 1. Names -/

theorem bindName_inj {i j : Nat} (h : "v" ++ toString i = "v" ++ toString j) : i = j :=
  Nat.repr_injective ((String.append_right_inj "v").mp h)

theorem paramName_inj {i j : Nat} (h : "p" ++ toString i = "p" ++ toString j) : i = j :=
  Nat.repr_injective ((String.append_right_inj "p").mp h)

theorem paramName_ne_bindName (i j : Nat) : "p" ++ toString i ≠ "v" ++ toString j := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp at this

/-- Distinct variables have distinct names. -/
def NamesInj {Γ : JCtxt} (vm : VarMap Γ) : Prop :=
  ∀ (t₁ t₂ : JasminTy) (v₁ : Ctxt.Var Γ t₁) (v₂ : Ctxt.Var Γ t₂),
    vm t₁ v₁ = vm t₂ v₂ → varDepth v₁ = varDepth v₂

/-- No variable is named `v{j}` for `j ≥ next`. -/
def NamesFresh {Γ : JCtxt} (vm : VarMap Γ) (next : Nat) : Prop :=
  ∀ (t : JasminTy) (v : Ctxt.Var Γ t) (j : Nat), next ≤ j → vm t v ≠ "v" ++ toString j

theorem NamesInj.extend {Γ : JCtxt} {u : JasminTy} {vm : VarMap Γ} {next : Nat}
    (hi : NamesInj vm) (hf : NamesFresh vm next) :
    NamesInj (vm.extend (t := u) ("v" ++ toString next)) := by
  intro t₁ t₂ v₁ v₂ h
  cases v₁ with
  | here =>
    cases v₂ with
    | here => rfl
    | there v₂ => exact absurd h.symm (hf _ v₂ next le_rfl)
  | there v₁ =>
    cases v₂ with
    | here => exact absurd h (hf _ v₁ next le_rfl)
    | there v₂ => exact congrArg (· + 1) (hi _ _ v₁ v₂ h)

theorem NamesFresh.extend {Γ : JCtxt} {u : JasminTy} {vm : VarMap Γ} {next : Nat}
    (hf : NamesFresh vm next) :
    NamesFresh (vm.extend (t := u) ("v" ++ toString next)) (next + 1) := by
  intro t v j hj
  cases v with
  | here => intro h; have := bindName_inj h; omega
  | there v => exact hf _ v j (by omega)

/-- Parameter `varDepth v` of the resolver `paramsAndMapFrom base` is named
    `p{base + varDepth v}`. -/
theorem paramsAndMapFrom_snd : ∀ (base : Nat) {Γ : JCtxt} {u : JasminTy} (v : Ctxt.Var Γ u),
    (paramsAndMapFrom base Γ).2 u v = "p" ++ toString (base + varDepth v)
  | _, _ :: _, _, .here => rfl
  | base, _ :: rest, _, .there v => by
    have ih := paramsAndMapFrom_snd (base + 1) (Γ := rest) v
    show (paramsAndMapFrom (base + 1) rest).2 _ v = _
    rw [ih, varDepth, Nat.add_assoc, Nat.add_comm 1]

/-- The parameter names of `paramsAndMapFrom base Γ`. -/
theorem paramsAndMapFrom_names : ∀ (base : Nat) (Γ : JCtxt),
    (paramsAndMapFrom base Γ).1.map (fun p => p.var.var.vname) =
      (List.range' base Γ.length).map (fun s => "p" ++ toString s)
  | _, [] => rfl
  | base, _ :: rest => by
    have ih := paramsAndMapFrom_names (base + 1) rest
    show _ :: (paramsAndMapFrom (base + 1) rest).1.map (fun p => p.var.var.vname) = _
    rw [ih, List.length_cons, List.range'_succ, List.map_cons]
    rfl

theorem paramsAndMap_inj (Γ : JCtxt) : NamesInj (paramsAndMap Γ).2 := by
  intro t₁ t₂ v₁ v₂ h
  simp only [paramsAndMap, paramsAndMapFrom_snd] at h
  simpa using paramName_inj h

theorem paramsAndMap_fresh (Γ : JCtxt) : NamesFresh (paramsAndMap Γ).2 0 := by
  intro t v j _ h
  simp only [paramsAndMap, paramsAndMapFrom_snd] at h
  exact paramName_ne_bindName _ _ h

/-! ## 2. The scalar run by names -/

/-- The `W`-bit word each name holds under the resolver `vm` and the valuation `V`: the
    value of the newest variable of that name when its type is `reg W`, else `0`. -/
def envOf (W : Nat) : {Γ : JCtxt} → VarMap Γ → Ctxt.Valuation Γ → String → BitVec W
  | [], _, _ => fun _ => 0
  | t :: _, vm, .cons x V => fun n =>
    if n = vm t .here then (regAs t W x).getD 0 else envOf W (fun s v => vm s v.there) V n

/-- The word each name holds at the end of the run of `c` from `V`, binding `i` of `c`
    named `v{next + i}` (the names of `VpackZmmLinearRender.collectWith`). -/
def traceEnv (W : Nat) : {Γ : JCtxt} → {t : JasminTy} → VarMap Γ → Nat →
    Ctxt.Valuation Γ → Com jasminDialect Γ t → String → BitVec W
  | _, _, vm, _, V, .ret _ => envOf W vm V
  | _, _, vm, next, V, .var (t := u) e body =>
    traceEnv W (vm.extend (t := u) ("v" ++ toString next)) (next + 1) (V.extend (e.denote V))
      body

/-- The values of the bindings of `c` run from `V`, in order, as `W`-bit words (`none`
    for a binding of another type). -/
def bindWords (W : Nat) : {Γ : JCtxt} → {t : JasminTy} → Ctxt.Valuation Γ →
    Com jasminDialect Γ t → List (Option (BitVec W))
  | _, _, _, .ret _ => []
  | _, _, V, .var (t := u) e body => regAs u W (e.denote V) :: bindWords W (V.extend (e.denote V)) body

/-- The number of bindings of `c`. -/
def nBinds : {Γ : JCtxt} → {t : JasminTy} → Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => nBinds body + 1

theorem envOf_lookup {W : Nat} : ∀ {Γ : JCtxt} (vm : VarMap Γ) (V : Ctxt.Valuation Γ),
    NamesInj vm → ∀ {u : JasminTy} (v : Ctxt.Var Γ u) (x : BitVec W),
    regAs u W (v.lookup V) = some x → envOf W vm V (vm u v) = x
  | t :: _, vm, .cons y V, _, _, .here, x, hx => by
    show (if vm t .here = vm t .here then (regAs t W y).getD 0 else _) = x
    rw [if_pos rfl]
    exact congrArg (·.getD 0) hx |>.trans rfl
  | t :: _, vm, .cons y V, hi, u, .there v, x, hx => by
    have hne : vm u (.there v) ≠ vm t .here := fun h => by
      have := hi _ _ _ _ h
      simp [varDepth] at this
    show (if vm u (.there v) = vm t .here then _ else
      envOf W (fun s v => vm s v.there) V (vm u (.there v))) = x
    rw [if_neg hne]
    exact envOf_lookup (fun s v => vm s v.there) V
      (fun _ _ v₁ v₂ h => by simpa [varDepth] using hi _ _ _ _ h) v x hx

/-- The name of a variable holds its value at the end of the run. -/
theorem traceEnv_lookup {W : Nat} : ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t)
    (vm : VarMap Γ) (next : Nat) (V : Ctxt.Valuation Γ), NamesInj vm → NamesFresh vm next →
    ∀ {u : JasminTy} (v : Ctxt.Var Γ u) (x : BitVec W),
      regAs u W (v.lookup V) = some x → traceEnv W vm next V c (vm u v) = x
  | _, _, .ret _, vm, _, V, hi, _, _, v, x, hx => envOf_lookup vm V hi v x hx
  | _, _, .var (t := s) e body, vm, next, V, hi, hf, _, v, x, hx =>
    traceEnv_lookup body (vm.extend (t := s) ("v" ++ toString next)) (next + 1)
      (V.extend (e.denote V)) (hi.extend hf) hf.extend (.there v) x hx

/-- Binding `j` holds its value at the end of the run, under the name `v{next + j}`. -/
theorem traceEnv_bindWords {W : Nat} : ∀ {Γ : JCtxt} {t : JasminTy}
    (c : Com jasminDialect Γ t) (vm : VarMap Γ) (next : Nat) (V : Ctxt.Valuation Γ),
    NamesInj vm → NamesFresh vm next → ∀ (j : Nat) (x : BitVec W),
      (bindWords W V c)[j]? = some (some x) →
      traceEnv W vm next V c ("v" ++ toString (next + j)) = x
  | _, _, .ret _, _, _, _, _, _, _, _, h => by simp [bindWords] at h
  | _, _, .var (t := s) e body, vm, next, V, hi, hf, 0, x, h => by
    simp only [bindWords, List.getElem?_cons_zero, Option.some.injEq] at h
    exact traceEnv_lookup body (vm.extend (t := s) ("v" ++ toString next)) (next + 1)
      (V.extend (e.denote V)) (hi.extend hf) hf.extend .here x h
  | _, _, .var (t := s) e body, vm, next, V, hi, hf, j + 1, x, h => by
    simp only [bindWords, List.getElem?_cons_succ] at h
    have := traceEnv_bindWords body (vm.extend (t := s) ("v" ++ toString next)) (next + 1)
      (V.extend (e.denote V)) (hi.extend hf) hf.extend j x h
    rw [show next + 1 + j = next + (j + 1) by omega] at this
    exact this

theorem bindWords_length {W : Nat} : ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ), (bindWords W V c).length = nBinds c
  | _, _, .ret _, _ => rfl
  | _, _, .var _ body, _ => by simp [bindWords, nBinds, bindWords_length body]

/-! ## 3. The collector -/

/-- The type of the binding maps of `collectWith`. -/
abbrev BindMap := ∀ {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}, VarMap Γ →
  Expr jasminDialect Γ t → String → ZBind

/-- The binding `F vm e dst` holds on lane `k` of `E` whenever `E k` gives the
    arguments' names their values and `dst` the value of `e`, for `k` below the lane
    count of a 512-bit register. -/
def BindSound (w : LaneW) (F : BindMap) : Prop :=
  ∀ {Γ : JCtxt} {t : JasminTy} (vm : VarMap Γ) (e : Expr jasminDialect Γ t) (dst : String)
    (V : Ctxt.Valuation Γ) (E : Nat → String → BitVec w.bits) (k : Nat), k < 512 / w.bits →
    (∀ (u : JasminTy) (v : Ctxt.Var Γ u) (x : BitVec w.bits),
      regAs u w.bits (v.lookup V) = some x → E k (vm u v) = x) →
    (∀ x, regAs t w.bits (e.denote V) = some x → E k dst = x) →
    SatB w E k (F vm e dst)

/-- A binding in the fragment defines `dst` and has the lane type. -/
def BindShape (w : LaneW) (F : BindMap) : Prop :=
  ∀ {Γ : JCtxt} {t : JasminTy} (vm : VarMap Γ) (e : Expr jasminDialect Γ t) (dst : String),
    (F vm e dst).dst = dst ∧ ((F vm e dst).isOther = false → t = .reg w.bits)

theorem collectWith_acc (F : BindMap) : ∀ {Γ : JCtxt} {t : JasminTy}
    (c : Com jasminDialect Γ t) (vm : VarMap Γ) (next : Nat) (acc : Array ZBind),
    ∀ b ∈ acc.toList, b ∈ (collectWith F vm next acc c).1.toList
  | _, _, .ret _, _, _, _, _, hb => hb
  | _, _, .var (t := s) e body, vm, next, acc, b, hb =>
    collectWith_acc F body (vm.extend (t := s) ("v" ++ toString next)) (next + 1)
      (acc.push (F vm e ("v" ++ toString next))) b (by simp [hb])

/-- The bindings the collector appends are named `v{next}`, `v{next+1}`, …, one per
    binding of `c`. -/
theorem collectWith_toList {F : BindMap} {w : LaneW} (hS : BindShape w F) :
    ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) (vm : VarMap Γ) (next : Nat)
      (acc : Array ZBind), ∃ L : List ZBind,
      (collectWith F vm next acc c).1.toList = acc.toList ++ L ∧
      L.map ZBind.dst = (List.range' next (nBinds c)).map (fun i => "v" ++ toString i)
  | _, _, .ret _, _, _, _ => ⟨[], by simp [collectWith], by simp [nBinds]⟩
  | _, _, .var (t := s) e body, vm, next, acc => by
    obtain ⟨L, h1, h2⟩ := collectWith_toList hS body (vm.extend (t := s) ("v" ++ toString next))
      (next + 1) (acc.push (F vm e ("v" ++ toString next)))
    refine ⟨F vm e ("v" ++ toString next) :: L, ?_, ?_⟩
    · show (collectWith F _ _ _ body).1.toList = _
      rw [h1]; simp
    · rw [List.map_cons, h2, (hS vm e _).1, nBinds, List.range'_succ, List.map_cons]

/-- **Link 1.** The end-of-run valuation of lane `k` satisfies every binding the
    collector produces. -/
theorem collectWith_sat {F : BindMap} {w : LaneW} (hF : BindSound w F) {k : Nat}
    (hk : k < 512 / w.bits) :
    ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) (vm : VarMap Γ) (next : Nat)
      (acc : Array ZBind) (V : Ctxt.Valuation Γ) (E : Nat → String → BitVec w.bits),
      NamesInj vm → NamesFresh vm next → traceEnv w.bits vm next V c = E k →
      (∀ b ∈ acc.toList, SatB w E k b) →
      ∀ b ∈ (collectWith F vm next acc c).1.toList, SatB w E k b
  | _, _, .ret _, _, _, _, _, _, _, _, _, hacc => hacc
  | _, _, .var (t := s) e body, vm, next, acc, V, E, hi, hf, hE, hacc => by
    have hb : SatB w E k (F vm e ("v" ++ toString next)) := by
      refine hF vm e _ V E k hk (fun u v x hx => ?_) (fun x hx => ?_)
      · rw [← hE]
        exact traceEnv_lookup (.var e body) vm next V hi hf v x hx
      · rw [← hE]
        exact traceEnv_lookup body (vm.extend (t := s) ("v" ++ toString next)) (next + 1)
          (V.extend (e.denote V)) (hi.extend hf) hf.extend .here x hx
    refine collectWith_sat hF hk body (vm.extend (t := s) ("v" ++ toString next)) (next + 1)
      (acc.push (F vm e ("v" ++ toString next))) (V.extend (e.denote V)) E (hi.extend hf) hf.extend
      hE ?_
    intro b hb'
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb'
    rcases hb' with hb' | rfl
    · exact hacc b hb'
    · exact hb

/-- Every binding of `c` has the lane type when the collector produces no binding
    outside the fragment. -/
theorem bindWords_some {F : BindMap} {w : LaneW} (hS : BindShape w F) :
    ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) (vm : VarMap Γ) (next : Nat)
      (acc : Array ZBind) (V : Ctxt.Valuation Γ),
      (∀ b ∈ (collectWith F vm next acc c).1.toList, b.isOther = false) →
      ∀ j < nBinds c, ∃ x, (bindWords w.bits V c)[j]? = some (some x)
  | _, _, .ret _, _, _, _, _, _, j, hj => by simp [nBinds] at hj
  | _, _, .var (t := s) e body, vm, next, acc, V, hO, j, hj => by
    cases j with
    | zero =>
      have hmem := collectWith_acc F body (vm.extend (t := s) ("v" ++ toString next)) (next + 1)
        (acc.push (F vm e ("v" ++ toString next))) (F vm e ("v" ++ toString next)) (by simp)
      have hs := (hS vm e _).2 (hO _ hmem)
      subst hs
      exact ⟨e.denote V, by simp [bindWords, regAs_reg]⟩
    | succ j =>
      simp only [bindWords, List.getElem?_cons_succ]
      exact bindWords_some hS body _ (next + 1) _ (V.extend (e.denote V)) hO j
        (by simp [nBinds] at hj; omega)

/-! ## 4. The range facts -/

/-- The validator's range facts from the renderer's range input: `rangeInfoOf`'s
    intervals, parameter names in `[0, B]` and binding `i` (named `v{i}`) in `arr[i]`. -/
def rfOf (names : List String) : Option (Nat × Array Iv) → Std.HashMap String Iv
  | none => {}
  | some (B, arr) => (rangeInfoOf {} names B arr #[]).iv

theorem foldl_insert_mem {α : Type} (key : α → String) (val : α → Iv) :
    ∀ (l : List α) (m0 : Std.HashMap String Iv) (n : String) (i : Iv),
      (l.foldl (fun m a => m.insert (key a) (val a)) m0)[n]? = some i →
      m0[n]? = some i ∨ ∃ a ∈ l, key a = n ∧ val a = i
  | [], _, _, _, h => Or.inl h
  | a :: l, m0, n, i, h => by
    rcases foldl_insert_mem key val l _ n i h with h' | ⟨b, hb, h1, h2⟩
    · rw [Std.HashMap.getElem?_insert] at h'
      split at h'
      · rename_i hk
        cases h'
        exact Or.inr ⟨a, List.mem_cons_self, by simpa using hk, rfl⟩
      · exact Or.inl h'
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩

/-- A range fact of `rfOf` is a parameter's `[0, B]` or a binding's analysis interval. -/
theorem rfOf_cases {names : List String} {B : Nat} {arr : Array Iv} {n : String} {i : Iv}
    (h : (rfOf names (some (B, arr)))[n]? = some i) :
    (n ∈ names ∧ i = (0, Int.ofNat B)) ∨ ∃ j : Nat, arr[j]? = some i ∧ n = "v" ++ toString j := by
  simp only [rfOf, rangeInfoOf] at h
  rw [← Array.foldl_toList] at h
  rcases foldl_insert_mem (fun x : Iv × Nat => "v" ++ toString x.2) (fun x => x.1) _ _ n i h
    with h0 | ⟨⟨x, j⟩, hmem, h1, h2⟩
  · rcases foldl_insert_mem (fun p => p) (fun _ => (0, Int.ofNat B)) names {} n i h0
      with h00 | ⟨p, hp, h1, h2⟩
    · simp at h00
    · exact Or.inl ⟨h1 ▸ hp, h2.symm⟩
  · refine Or.inr ⟨j, ?_, h1.symm⟩
    rw [Array.toList_zipIdx, List.mk_mem_zipIdx_iff_getElem?] at hmem
    simp only at h2
    rw [← h2, ← Array.getElem?_toList]
    exact hmem

/-- The interval `(0, B)` holds of a word at most `B`. -/
theorem mem_zero_B {W B : Nat} {x : BitVec W} (h : x.toNat ≤ B) :
    Iv.Mem W (0, Int.ofNat B) x :=
  ⟨x.toNat, by simp, by simpa using h, by
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast x.isLt)]⟩

/-- The analysis intervals of the bindings hold of the end-of-run valuation, for a
    collector whose bindings all have the lane type. -/
theorem analyze_mem {F : BindMap} {w : LaneW} (hS : BindShape w F) :
    ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) (vm : VarMap Γ) (next : Nat)
      (acc : Array ZBind) (V : Ctxt.Valuation Γ) (A : AEnv Γ),
      NamesInj vm → NamesFresh vm next → EnvOK A V →
      (∀ b ∈ (collectWith F vm next acc c).1.toList, b.isOther = false) →
      ∀ (j : Nat) (i : Iv), (analyze A c)[j]? = some i →
        i.Mem w.bits (traceEnv w.bits vm next V c ("v" ++ toString (next + j)))
  | _, _, .ret _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [analyze] at h
  | _, _, .var (t := s) e body, vm, next, acc, V, A, hi, hf, hA, hO, j, i, h => by
    have hmem := collectWith_acc F body (vm.extend (t := s) ("v" ++ toString next)) (next + 1)
      (acc.push (F vm e ("v" ++ toString next))) (F vm e ("v" ++ toString next)) (by simp)
    have hs := (hS vm e _).2 (hO _ hmem)
    subst hs
    have he := exprAbs_sound hA e
    cases j with
    | zero =>
      simp only [analyze, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      have hv : traceEnv w.bits (vm.extend (t := .reg w.bits) ("v" ++ toString next))
          (next + 1) (V.extend (e.denote V)) body ("v" ++ toString next) = e.denote V :=
        traceEnv_lookup body (vm.extend (t := .reg w.bits) ("v" ++ toString next))
        (next + 1) (V.extend (e.denote V)) (hi.extend hf) hf.extend .here (e.denote V) (regAs_reg _ _)
      show Iv.Mem w.bits _ (traceEnv w.bits _ _ _ body ("v" ++ toString next))
      rw [hv]
      exact he.1
    | succ j =>
      simp only [analyze, List.getElem?_cons_succ] at h
      have := analyze_mem hS body _ (next + 1) _ (V.extend (e.denote V)) _ (hi.extend hf) hf.extend
        (hA.cons he) hO j i h
      rw [show next + 1 + j = next + (j + 1) by omega] at this
      exact this

theorem hget_ivsConst (iv : Iv) : ∀ {Γ : JCtxt} {t : JasminTy} (v : Ctxt.Var Γ t),
    hget (ivsConst iv Γ) v = iv
  | _ :: _, _, .here => rfl
  | _ :: _, _, .there v => hget_ivsConst iv v

theorem var_mem : ∀ {Γ : JCtxt} {t : JasminTy}, Ctxt.Var Γ t → t ∈ Γ
  | _, _, .here => List.mem_cons_self
  | _, _, .there v => List.mem_cons_of_mem _ (var_mem v)

theorem exists_var_of_idx {W : Nat} : ∀ {Γ : JCtxt}, (∀ t ∈ Γ, t = .reg W) →
    ∀ s < Γ.length, ∃ v : Ctxt.Var Γ (.reg W), varDepth v = s
  | [], _, _, hs => by simp at hs
  | t :: Γ, hΓ, 0, _ => by
    obtain rfl := hΓ t List.mem_cons_self
    exact ⟨.here, rfl⟩
  | _ :: Γ, hΓ, s + 1, hs => by
    obtain ⟨v, hv⟩ := exists_var_of_idx (Γ := Γ) (fun t ht => hΓ t (List.mem_cons_of_mem _ ht))
      s (by simpa using hs)
    exact ⟨.there v, by simp [varDepth, hv]⟩

/-- **Link 2.** When every input word is at most `B`, every range fact of the renderer
    holds of the end-of-run valuation. -/
theorem rfOf_mem {F : BindMap} {w : LaneW} (hS : BindShape w F) {Γ : JCtxt} {t : JasminTy}
    (c : Com jasminDialect Γ t) (hΓ : ∀ u ∈ Γ, u = .reg w.bits) (B : Nat)
    (V : Ctxt.Valuation Γ)
    (hB : ∀ v : Ctxt.Var Γ (.reg w.bits), (v.lookup V).toNat ≤ B)
    (hO : ∀ b ∈ (collectWith F (paramsAndMap Γ).2 0 #[] c).1.toList, b.isOther = false) :
    ∀ (n : String) (i : Iv),
      (rfOf ((paramsAndMap Γ).1.map (fun p => p.var.var.vname))
        (some (B, ComRange.rangeAnalysisArray (ivsConst (0, Int.ofNat B) Γ) c)))[n]? = some i →
      i.Mem w.bits (traceEnv w.bits (paramsAndMap Γ).2 0 V c n) := by
  intro n i h
  rcases rfOf_cases h with ⟨hn, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [paramsAndMap, paramsAndMapFrom_names, List.mem_map] at hn
    obtain ⟨s, hs, rfl⟩ := hn
    obtain ⟨v, hv⟩ := exists_var_of_idx hΓ s (by simp at hs; omega)
    have hname : (paramsAndMap Γ).2 _ v = "p" ++ toString s := by
      rw [paramsAndMap, paramsAndMapFrom_snd, hv, Nat.zero_add]
    rw [← hname, traceEnv_lookup c _ 0 V (paramsAndMap_inj Γ) (paramsAndMap_fresh Γ) v _
      (regAs_reg _ _)]
    exact mem_zero_B (hB v)
  · have hA : EnvOK (ComRange.AEnv.ofIvs (ivsConst (0, Int.ofNat B) Γ)) V := by
      intro u v
      rw [ComRange.hget_ofIvs, hget_ivsConst]
      obtain rfl := hΓ u (var_mem v)
      exact ⟨mem_zero_B (hB v), ComRange.SymOK.none _ _ _⟩
    have hj' : (analyze (ComRange.AEnv.ofIvs (ivsConst (0, Int.ofNat B) Γ)) c)[j]? = some i := by
      simpa [ComRange.rangeAnalysisArray, ComRange.rangeAnalysis] using hj
    have := analyze_mem hS c _ 0 #[] V _ (paramsAndMap_inj Γ) (paramsAndMap_fresh Γ) hA hO j i hj'
    rwa [Nat.zero_add] at this

/-! ## 5. The fragments of the two lane maps -/

/-- The sum `Σ_{j<N} x·2^(L·j)` of `N` copies of an `L`-bit word `x` lies below
    `2^(L·N)`, and its `k`-th `L`-bit digit is `x`. -/
theorem bcast_digits (L x : Nat) (hx : x < 2 ^ L) : ∀ N : Nat,
    (List.range N).foldl (fun acc j => acc + x * 2 ^ (L * j)) 0 < 2 ^ (L * N) ∧
    ∀ k < N, (List.range N).foldl (fun acc j => acc + x * 2 ^ (L * j)) 0 / 2 ^ (L * k) % 2 ^ L = x
  | 0 => by simp
  | N + 1 => by
    obtain ⟨h1, h2⟩ := bcast_digits L x hx N
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range N).foldl (fun acc j => acc + x * 2 ^ (L * j)) 0 = S at h1 h2
    have hp : 2 ^ (L * (N + 1)) = 2 ^ L * 2 ^ (L * N) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [hp]
      calc S + x * 2 ^ (L * N) < 2 ^ (L * N) + x * 2 ^ (L * N) := by omega
        _ = (x + 1) * 2 ^ (L * N) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        _ ≤ 2 ^ L * 2 ^ (L * N) := Nat.mul_le_mul_right _ hx
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · have hN : L * N = L * (N - k - 1) + L + L * k := by
          have e : N = (N - k - 1) + 1 + k := by omega
          calc L * N = L * ((N - k - 1) + 1 + k) := by rw [← e]
            _ = _ := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
        have e : x * 2 ^ (L * N) = x * 2 ^ (L * (N - k - 1)) * 2 ^ L * 2 ^ (L * k) := by
          rw [hN, Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
        rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]
        exact h2 k hk
      · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h1, Nat.zero_add,
          Nat.mod_eq_of_lt hx]

/-- Lane `k` of width `L` of a value below `2^512` is its `k`-th `L`-bit digit. -/
theorem lane_ofNat_digit {L k x : Nat} (S : Nat) (hS : S < 2 ^ 512)
    (hd : S / 2 ^ (L * k) % 2 ^ L = x % 2 ^ L) :
    lane L (BitVec.ofNat 512 S) k = BitVec.ofNat L x := by
  apply BitVec.eq_of_toNat_eq
  simp only [lane, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS,
    Nat.shiftRight_eq_div_pow]
  exact hd

/-- Lane `k` of the sixteen-fold broadcast of `n` is `n` as a 32-bit word. -/
theorem lane_bcast512d (n k : Nat) (hk : k < 16) :
    lane 32 (BitVec.ofNat 512 (bcast512d n)) k = BitVec.ofNat 32 n := by
  obtain ⟨h1, h2⟩ := bcast_digits 32 (n % 2 ^ 32) (Nat.mod_lt _ (by norm_num)) 16
  exact lane_ofNat_digit (bcast512d n) (h1.trans_eq (by norm_num)) (h2 k hk)

/-- Lane `k` of the eight-fold broadcast `constZmm n` is `n` as a 64-bit word. -/
theorem lane_constZmm (n k : Nat) (hk : k < 8) :
    lane 64 (BitVec.ofNat 512 (KeccakThetaPiAbstractCom.constZmm n).toNat) k =
      BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact KeccakThetaPiAbstractCom.zmmOfLanes_zmmLane' (fun _ => BitVec.ofNat 64 n) ⟨k, hk⟩

theorem exprZBindScalar_shape : BindShape .q exprZBindScalar := by
  intro Γ t vm e dst
  rcases e with ⟨op, rfl, args⟩
  cases op <;> simp [exprZBindScalar, ZBind.dst, ZBind.isOther] <;> split_ifs <;>
    simp_all <;> rfl

theorem exprZBindScalar32_shape : BindShape .d exprZBindScalar32 := by
  intro Γ t vm e dst
  rcases e with ⟨op, rfl, args⟩
  cases op <;> simp [exprZBindScalar32, ZBind.dst, ZBind.isOther] <;> split_ifs <;>
    simp_all <;> rfl

theorem exprZBindScalar_sound : BindSound .q exprZBindScalar := by
  intro Γ t vm e dst V E k hk ha hd
  rcases e with ⟨op, rfl, args⟩
  cases op with
  | regArith bop w' =>
    by_cases hw : w' = 64
    · subst hw
      match args with
      | .cons a (.cons b .nil) =>
        show _ = _ → _
        intro _
        rw [hd _ (regAs_reg 64 _)]
        show _ = bop.apply (E k (vm _ a)) (E k (vm _ b))
        rw [ha _ a _ (regAs_reg 64 _), ha _ b _ (regAs_reg 64 _)]
        rfl
    · simp [exprZBindScalar, hw, SatB]
  | regConst w' n =>
    by_cases hw : w' = 64
    · subst hw
      show E k dst = _
      rw [hd _ (regAs_reg 64 _)]
      exact (lane_constZmm n k (by simpa [LaneW.bits] using hk)).symm
    · simp [exprZBindScalar, hw, SatB]
  | shlImm w' n =>
    by_cases hw : w' = 64 ∧ n < 64
    · obtain ⟨rfl, hn⟩ := hw
      match args with
      | .cons a .nil =>
        simp only [exprZBindScalar, hn, and_self, if_true, SatB, if_true]
        intro _
        rw [hd _ (regAs_reg 64 _)]
        change _ = E k (vm (JasminTy.reg 64) a) <<< n
        rw [ha _ a _ (regAs_reg 64 _)]
        exact congrArg (fun m : Nat => (show BitVec 64 from a.lookup V) <<< m)
          (shiftMask_of_lt (w := 64) hn)
    · simp [exprZBindScalar, hw, SatB]
  | shrImm w' n =>
    by_cases hw : w' = 64 ∧ n < 64
    · obtain ⟨rfl, hn⟩ := hw
      match args with
      | .cons a .nil =>
        simp only [exprZBindScalar, hn, and_self, if_true, SatB, if_false]
        intro _
        rw [hd _ (regAs_reg 64 _)]
        change _ = E k (vm (JasminTy.reg 64) a) >>> n
        rw [ha _ a _ (regAs_reg 64 _)]
        exact congrArg (fun m : Nat => (show BitVec 64 from a.lookup V) >>> m)
          (shiftMask_of_lt (w := 64) hn)
    · simp [exprZBindScalar, hw, SatB]
  | _ => exact True.intro

/-- The bindings of the 32-bit binding map `exprZBindScalar32` hold of the run of the scalar
    program, lane by lane. `SatB` places no condition on a rotate binding `.rol`, so the
    `rorImm` arm holds without content; the text validator has no recogniser for `vprold`
    and refuses a text that contains a rotate binding. -/
theorem exprZBindScalar32_sound : BindSound .d exprZBindScalar32 := by
  intro Γ t vm e dst V E k hk ha hd
  rcases e with ⟨op, rfl, args⟩
  cases op with
  | regArith bop w' =>
    by_cases hw : w' = 32
    · subst hw
      match args with
      | .cons a (.cons b .nil) =>
        show _ = _ → _
        intro _
        rw [hd _ (regAs_reg 32 _)]
        show _ = bop.apply (E k (vm _ a)) (E k (vm _ b))
        rw [ha _ a _ (regAs_reg 32 _), ha _ b _ (regAs_reg 32 _)]
        rfl
    · simp [exprZBindScalar32, hw, SatB]
  | mulhi w' =>
    by_cases hw : w' = 32
    · subst hw
      match args with
      | .cons a (.cons b .nil) =>
        show E k dst = mulHiW (E k (vm _ a)) (E k (vm _ b))
        rw [hd _ (regAs_reg 32 _), ha _ a _ (regAs_reg 32 _), ha _ b _ (regAs_reg 32 _)]
        rfl
    · simp [exprZBindScalar32, hw, SatB]
  | regConst w' n =>
    by_cases hw : w' = 32
    · subst hw
      show E k dst = _
      rw [hd _ (regAs_reg 32 _)]
      exact (lane_bcast512d n k (by simpa [LaneW.bits] using hk)).symm
    · simp [exprZBindScalar32, hw, SatB]
  | shlImm w' n =>
    by_cases hw : w' = 32 ∧ n < 32
    · obtain ⟨rfl, hn⟩ := hw
      match args with
      | .cons a .nil =>
        simp only [exprZBindScalar32, hn, and_self, if_true, SatB, if_true]
        intro _
        rw [hd _ (regAs_reg 32 _)]
        change _ = E k (vm (JasminTy.reg 32) a) <<< n
        rw [ha _ a _ (regAs_reg 32 _)]
        exact congrArg (fun m : Nat => (show BitVec 32 from a.lookup V) <<< m)
          (shiftMask_of_lt (w := 32) hn)
    · simp [exprZBindScalar32, hw, SatB]
  | shrImm w' n =>
    by_cases hw : w' = 32 ∧ n < 32
    · obtain ⟨rfl, hn⟩ := hw
      match args with
      | .cons a .nil =>
        simp only [exprZBindScalar32, hn, and_self, if_true, SatB, if_false]
        intro _
        rw [hd _ (regAs_reg 32 _)]
        change _ = E k (vm (JasminTy.reg 32) a) >>> n
        rw [ha _ a _ (regAs_reg 32 _)]
        exact congrArg (fun m : Nat => (show BitVec 32 from a.lookup V) >>> m)
          (shiftMask_of_lt (w := 32) hn)
    · simp [exprZBindScalar32, hw, SatB]
  | rorImm w' n =>
    by_cases hw : w' = 32 ∧ 0 < n ∧ n < 32
    · simp [exprZBindScalar32, hw, SatB]
    · simp [exprZBindScalar32, hw, SatB]
  | _ => exact True.intro

/-- An expression in the fragment `LaneMapZmmD` covers has a binding inside the
    fragment of `exprZBindScalar32`. -/
theorem exprZBindScalar32_isOther_covered {Γ : JCtxt} {t : JasminTy} (vm : VarMap Γ)
    (e : Expr jasminDialect Γ t) (dst : String) (he : LaneMapZmmD.CoveredExpr e) :
    (exprZBindScalar32 vm e dst).isOther = false := by
  rcases e with ⟨op, rfl, args⟩
  cases op <;> simp_all [LaneMapZmmD.CoveredExpr, LaneMapVec.LaneShape.CoveredExpr,
    LaneMapVec.dwordZmm, LaneMapVec.zmmDImmBlock, LaneMapVec.zmmDImmCovers,
    exprZBindScalar32, ZBind.isOther]

/-- The add-rotate-xor ops of `LaneMapZmmD.coveredExpr_arx` (`regArith add 32`,
    `regArith xor 32`, `shlImm 32 n` and `shrImm 32 n` with `n < 32`, `rorImm 32 n` with
    `0 < n < 32`) have bindings inside the fragment of `exprZBindScalar32`. -/
theorem exprZBindScalar32_isOther_arx {Γ : JCtxt} {t : JasminTy} (vm : VarMap Γ)
    (e : Expr jasminDialect Γ t) (dst : String)
    (h : e.op = .regArith .add 32 ∨ e.op = .regArith .xor 32 ∨
      (∃ n, n < 32 ∧ (e.op = .shlImm 32 n ∨ e.op = .shrImm 32 n)) ∨
      ∃ n, 0 < n ∧ n < 32 ∧ e.op = .rorImm 32 n) :
    (exprZBindScalar32 vm e dst).isOther = false :=
  exprZBindScalar32_isOther_covered vm e dst (LaneMapZmmD.coveredExpr_arx e h)

/-- For a straight-line program covered by `LaneMapZmmD`, every binding the 32-bit
    collector appends lies inside the fragment: the binding list has no `.other`
    when the accumulator has none. -/
theorem collectWith_scalar32_noOther : ∀ {Γ : JCtxt} {t : JasminTy}
    (c : Com jasminDialect Γ t) (vm : VarMap Γ) (next : Nat) (acc : Array ZBind),
    (∀ b ∈ acc.toList, b.isOther = false) → LaneMapZmmD.LaneMapZmmDCovered c →
    ∀ b ∈ (collectWith exprZBindScalar32 vm next acc c).1.toList, b.isOther = false
  | _, _, .ret _, _, _, _, hacc, _ => hacc
  | _, _, .var (t := s) e body, vm, next, acc, hacc, hc => by
    have hc' : LaneMapZmmD.CoveredExpr e ∧ LaneMapZmmD.LaneMapZmmDCovered body := hc
    exact collectWith_scalar32_noOther body (vm.extend (t := s) ("v" ++ toString next))
      (next + 1) (acc.push (exprZBindScalar32 vm e ("v" ++ toString next))) (by
        intro b hb
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact hacc b hb
        · exact exprZBindScalar32_isOther_covered vm e _ hc'.1) hc'.2

/-! ## 6. The validated render -/

/-- The rendered text `r` when the binding list `bs` has no binding outside the
    fragment and at least `nOut` bindings and `validate` accepts the text; an error
    otherwise. -/
def checkText (m : Mode) (w : LaneW) (names : List String) (offs : List Nat)
    (bs : Array ZBind) (nOut : Nat) (rf : Std.HashMap String Iv) :
    Except String String → Except String String
  | .error e => .error e
  | .ok text =>
    if !(decide (nOut ≤ bs.size) && bs.all (fun b => !b.isOther)) then
      .error "vpackZMM validated render: a binding outside the fragment, or fewer bindings \
        than outputs"
    else if validate m w names offs bs (lastOuts bs nOut) rf text then .ok text
    else .error ("vpackZMM validated render: translation validation rejected the text: "
      ++ ZmmTextValidate.validateDiag m w names offs bs (lastOuts bs nOut) rf text)

theorem checkText_ok {m : Mode} {w : LaneW} {names : List String} {offs : List Nat}
    {bs : Array ZBind} {nOut : Nat} {rf : Std.HashMap String Iv}
    {r : Except String String} {text : String}
    (h : checkText m w names offs bs nOut rf r = .ok text) :
    r = .ok text ∧ nOut ≤ bs.size ∧ (∀ b ∈ bs.toList, b.isOther = false) ∧
      validate m w names offs bs (lastOuts bs nOut) rf text = true := by
  unfold checkText at h
  split at h
  · cases h
  · rename_i t
    split at h
    · cases h
    · rename_i hc
      split at h
      · rename_i hv
        cases h
        have hc' : (decide (nOut ≤ bs.size) && bs.all (fun b => !b.isOther)) = true := by
          simpa using hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem] at hc'
        exact ⟨rfl, hc'.1, fun b hb => by simpa using hc'.2 b (by simpa using hb), hv⟩
      · cases h

/-- The render of the lane map of `c` at lane width `w` (binding map `F`, register mode
    `m`) returned only when it validates: the text `renderZmmLinearBinds` prints from
    the bindings `collectWith F` reads off `c` and, with `inBound = some B`, the
    intervals of `ComRange.rangeAnalysis` of `c` from inputs in `[0, B]`, checked by
    `checkText` against the same bindings and intervals. Every parameter of `c` must be
    a lane word. -/
def laneMapValidated (w : LaneW) (F : BindMap) (m : Mode) {Γ : JCtxt} {t : JasminTy}
    (sym : String) (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t)
    (inBound : Option Nat) : Except String String :=
  let names := (paramsAndMap Γ).1.map (fun p => p.var.var.vname)
  let bs := (collectWith F (paramsAndMap Γ).2 0 #[] c).1
  let ranges := inBound.map
    (fun B => (B, ComRange.rangeAnalysisArray (ivsConst (0, Int.ofNat B) Γ) c))
  if Γ.all (fun u => decide (u = .reg w.bits)) then
    checkText m w names ((List.range names.length).map inOffset) bs nOut (rfOf names ranges)
      (renderZmmLinearBinds sym inOffset nOut names bs ranges (m == .ymm))
  else .error "vpackZMM validated render: a parameter is not a lane word"

/-- `renderLaneMapZmmFunction` (eight 64-bit lanes, or four with `ymm`) returned only
    when its text validates. -/
def renderValidated {Γ : JCtxt} {t : JasminTy} (sym : String) (inOffset : Nat → Nat)
    (nOut : Nat) (c : Com jasminDialect Γ t) (inBound : Option Nat := none)
    (ymm : Bool := false) : Except String String :=
  laneMapValidated .q exprZBindScalar (if ymm then .ymm else .zmm) sym inOffset nOut c inBound

/-- `renderLaneMapZmmDFunction` (sixteen 32-bit lanes) returned only when its text
    validates. -/
def renderValidatedD {Γ : JCtxt} {t : JasminTy} (sym : String) (inOffset : Nat → Nat)
    (nOut : Nat) (c : Com jasminDialect Γ t) (inBound : Option Nat := none) :
    Except String String :=
  laneMapValidated .d exprZBindScalar32 .zmm sym inOffset nOut c inBound

/-- The validated render prints the text of the unvalidated one. -/
theorem renderValidated_text {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {ymm : Bool} {text : String} (h : renderValidated sym inOffset nOut c inBound ymm = .ok text) :
    VpackZmmLinearRender.renderLaneMapZmmFunction sym inOffset nOut c inBound ymm = .ok text := by
  unfold renderValidated laneMapValidated at h
  split at h
  · have hm : ((if ymm then Mode.ymm else Mode.zmm) == Mode.ymm) = ymm := by cases ymm <;> rfl
    rw [hm] at h
    exact (checkText_ok h).1
  · cases h

theorem renderValidatedD_text {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : renderValidatedD sym inOffset nOut c inBound = .ok text) :
    VpackZmmLinearRender.renderLaneMapZmmDFunction sym inOffset nOut c inBound = .ok text := by
  unfold renderValidatedD laneMapValidated at h
  split at h
  · exact (checkText_ok h).1
  · cases h

/-- The output names of the collected bindings: output `j` is binding
    `nBinds c - nOut + j`. -/
theorem lastOuts_getElem? {F : BindMap} {w : LaneW} (hS : BindShape w F) {Γ : JCtxt}
    {t : JasminTy} (c : Com jasminDialect Γ t) (vm : VarMap Γ) (nOut : Nat)
    (hn : nOut ≤ nBinds c) :
    (lastOuts (collectWith F vm 0 #[] c).1 nOut).length = nOut ∧
    ∀ j < nOut, (lastOuts (collectWith F vm 0 #[] c).1 nOut)[j]? =
      some ("v" ++ toString (nBinds c - nOut + j)) := by
  obtain ⟨L, h1, h2⟩ := collectWith_toList hS c vm 0 #[]
  simp only [List.nil_append] at h1
  have hsz : (collectWith F vm 0 #[] c).1.size = nBinds c := by
    rw [← Array.length_toList, h1, ← List.length_map (f := ZBind.dst), h2]; simp
  unfold lastOuts
  rw [hsz, h1, List.map_drop, h2]
  refine ⟨by simp; omega, fun j hj => ?_⟩
  rw [List.getElem?_drop, List.getElem?_map, List.getElem?_range' (by omega)]
  simp

/-- **Soundness of the validated render.** When `laneMapValidated` returns `text`, the
    text parses to a program `prog` with data table `ro`, and for all lane valuations
    `Vs` of the parameters of `c` (lane `k` of the register is the scalar run from
    `Vs k`), each input word at most `B` when `inBound = some B`, and every input region
    whose lane `k` at the offset `inOffset s` of parameter `s` holds that parameter's
    value in `Vs k`, running `prog` from a state with no stores succeeds, and for each
    output `j < nOut` the value stored at `stride·j` has as lane `k` the value of binding
    `nBinds c - nOut + j` of the scalar run from `Vs k`. -/
theorem laneMapValidated_sound {w : LaneW} {F : BindMap} (hF : BindSound w F)
    (hS : BindShape w F) {m : Mode} {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : laneMapValidated w F m sym inOffset nOut c inBound = .ok text) :
    ∃ prog ro, parse m text = .ok (prog, ro) ∧
      ∀ (Vs : Nat → Ctxt.Valuation Γ) (inp : Nat → BitVec 512),
        (∀ B, inBound = some B → ∀ k < m.act / w.bits,
          ∀ v : Ctxt.Var Γ (.reg w.bits), (v.lookup (Vs k)).toNat ≤ B) →
        (∀ k < m.act / w.bits, ∀ v : Ctxt.Var Γ (.reg w.bits),
          lane w.bits (inp (inOffset (varDepth v))) k = v.lookup (Vs k)) →
        ∀ σ : MState, σ.log = [] →
        ∃ σ', run m inp ro σ prog = some σ' ∧
          ∀ j < nOut, ∃ y, σ'.outAt (m.stride * j) = some y ∧
            ∀ k < m.act / w.bits, ∃ x,
              (bindWords w.bits (Vs k) c)[nBinds c - nOut + j]? = some (some x) ∧
              lane w.bits y k = x := by
  unfold laneMapValidated at h
  split at h
  · rename_i hΓ'
    have hΓ : ∀ u ∈ Γ, u = .reg w.bits := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hΓ'
    obtain ⟨-, hn, hO, hv⟩ := checkText_ok h
    obtain ⟨prog, ro, hp, hsound⟩ := validate_sound hv
    refine ⟨prog, ro, hp, ?_⟩
    intro Vs inp hB hinp σ hσ
    have hi := paramsAndMap_inj Γ
    have hf := paramsAndMap_fresh Γ
    have hact : ∀ k, k < m.act / w.bits → k < 512 / w.bits := fun k hk =>
      Nat.lt_of_lt_of_le hk (Nat.div_le_div_right (by cases m <;> simp [Mode.act]))
    have hbs : (collectWith F (paramsAndMap Γ).2 0 #[] c).1.size = nBinds c := by
      obtain ⟨L, h1, h2⟩ := collectWith_toList hS c (paramsAndMap Γ).2 0 #[]
      simp only [List.nil_append] at h1
      rw [← Array.length_toList, h1, ← List.length_map (f := ZBind.dst), h2]; simp
    obtain ⟨σ', hrun, hout⟩ := hsound (fun k => traceEnv w.bits (paramsAndMap Γ).2 0 (Vs k) c)
      (fun b hb k hk => collectWith_sat hF (hact k hk) c _ 0 #[] (Vs k) _ hi hf rfl
        (by simp) b hb)
      (fun n i hni k hk => by
        cases inBound with
        | none => simp [rfOf] at hni
        | some B => exact rfOf_mem hS c hΓ B (Vs k) (hB B rfl k hk) hO n i hni)
      inp
      (fun p off hpo k hk => by
        rw [paramsAndMap, paramsAndMapFrom_names, ← List.range_eq_range', List.length_map,
          List.length_range, List.zip_map', List.mem_map] at hpo
        obtain ⟨s, hs, hps⟩ := hpo
        simp only [Prod.mk.injEq] at hps
        obtain ⟨rfl, rfl⟩ := hps
        obtain ⟨v, rfl⟩ := exists_var_of_idx hΓ s (List.mem_range.mp hs)
        have hname : (paramsAndMap Γ).2 _ v = "p" ++ toString (varDepth v) := by
          rw [paramsAndMap, paramsAndMapFrom_snd, Nat.zero_add]
        rw [hinp k hk v, ← hname,
          traceEnv_lookup c _ 0 (Vs k) hi hf v _ (regAs_reg _ _)])
      σ hσ
    refine ⟨σ', hrun, fun j hj => ?_⟩
    have hn' : nOut ≤ nBinds c := hbs ▸ hn
    obtain ⟨hlen, hget⟩ := lastOuts_getElem? hS c (paramsAndMap Γ).2 nOut hn'
    obtain ⟨y, hy, hlane⟩ := hout j (by rw [hlen]; exact hj)
    refine ⟨y, hy, fun k hk => ?_⟩
    obtain ⟨x, hx⟩ := bindWords_some hS c _ 0 #[] (Vs k) hO (nBinds c - nOut + j) (by omega)
    refine ⟨x, hx, ?_⟩
    obtain ⟨_, heq⟩ := List.getElem?_eq_some_iff.mp (hget j hj)
    rw [hlane k hk, heq]
    have := traceEnv_bindWords c _ 0 (Vs k) hi hf _ x hx
    rwa [Nat.zero_add] at this
  · cases h

/-- **Soundness of `renderValidated`** (eight 64-bit lanes, four with `ymm`): the
    instance of `laneMapValidated_sound` for `LaneMapZmm`'s binding map. -/
theorem renderValidated_sound {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {ymm : Bool} {text : String} (h : renderValidated sym inOffset nOut c inBound ymm = .ok text) :
    let m : Mode := if ymm then .ymm else .zmm
    ∃ prog ro, parse m text = .ok (prog, ro) ∧
      ∀ (Vs : Nat → Ctxt.Valuation Γ) (inp : Nat → BitVec 512),
        (∀ B, inBound = some B → ∀ k < m.act / 64,
          ∀ v : Ctxt.Var Γ (.reg 64), (v.lookup (Vs k)).toNat ≤ B) →
        (∀ k < m.act / 64, ∀ v : Ctxt.Var Γ (.reg 64),
          lane 64 (inp (inOffset (varDepth v))) k = v.lookup (Vs k)) →
        ∀ σ : MState, σ.log = [] →
        ∃ σ', run m inp ro σ prog = some σ' ∧
          ∀ j < nOut, ∃ y, σ'.outAt (m.stride * j) = some y ∧
            ∀ k < m.act / 64, ∃ x,
              (bindWords 64 (Vs k) c)[nBinds c - nOut + j]? = some (some x) ∧
              lane 64 y k = x :=
  laneMapValidated_sound exprZBindScalar_sound exprZBindScalar_shape h

/-- **Soundness of `renderValidatedD`** (sixteen 32-bit lanes): the instance of
    `laneMapValidated_sound` for `LaneMapZmmD`'s binding map. -/
theorem renderValidatedD_sound {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : renderValidatedD sym inOffset nOut c inBound = .ok text) :
    ∃ prog ro, parse .zmm text = .ok (prog, ro) ∧
      ∀ (Vs : Nat → Ctxt.Valuation Γ) (inp : Nat → BitVec 512),
        (∀ B, inBound = some B → ∀ k < 16,
          ∀ v : Ctxt.Var Γ (.reg 32), (v.lookup (Vs k)).toNat ≤ B) →
        (∀ k < 16, ∀ v : Ctxt.Var Γ (.reg 32),
          lane 32 (inp (inOffset (varDepth v))) k = v.lookup (Vs k)) →
        ∀ σ : MState, σ.log = [] →
        ∃ σ', run .zmm inp ro σ prog = some σ' ∧
          ∀ j < nOut, ∃ y, σ'.outAt (64 * j) = some y ∧
            ∀ k < 16, ∃ x,
              (bindWords 32 (Vs k) c)[nBinds c - nOut + j]? = some (some x) ∧
              lane 32 y k = x :=
  laneMapValidated_sound exprZBindScalar32_sound exprZBindScalar32_shape h

end CatCrypt.Crypto.SecureCompilation.VIR.ZmmRenderValidated
