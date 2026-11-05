/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMaskElim
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgDCELive

/-!
# Mask elimination deciding each mask on the uses of its value

At a mask of width `m`, `maskElimGo` decides `okP k (A.push (.relaxed m))` on the whole
continuation `k`. Along the recursion of `maskElim` the analysis holds at the facts of the
source (`okP k (A.push i) = true` for the information `i` of the mask), and the two fact maps
differ only at the mask and at the bindings whose value is computed from it. `okPT` checks the
continuation along a set of *tainted* indices, the variables whose facts may differ: a binding
that reads no tainted variable has the information it has at the source facts, and once no
tainted variable is read by the rest of the program (`fvTree`, the free variables of every
subprogram, computed once) the rest passes. `maskElimFast` is `maskElimGo` with `okPT` in place
of `okP` and the tree of free variables carried along; `maskElim_eq_maskElimFast` is registered
with `@[csimp]`, so compiled code that calls `maskElim` runs `maskElimFast`.

## Main definitions

* `FTree`, `fvTree` — the free variables of a program and of each of its subprograms.
* `FactsAgreeOff` — two fact maps agree on the variables of a set outside a set of tainted indices.
* `okPT` — the analysis along a set of tainted indices.
* `maskElimGoF`, `maskElimFast` — the pass deciding each mask with `okPT`.

## Main results

* `okP_congr` — the analysis reads the facts of the free variables only.
* `okPT_eq` — at fact maps that agree outside the tainted set, where the analysis holds at the
  second, `okPT` is the analysis at the first.
* `maskElimGoF_eq` — `maskElimGoF` is `maskElimGo` wherever the analysis holds.
* `maskElim_eq_maskElimFast` — `maskElim` is `maskElimFast` (`@[csimp]`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

open Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProg (appLift bindHom varTyCast)

/-! ## 1. The free variables of every subprogram -/

/-- A program's shape with the set of free variables of each subprogram. -/
inductive FTree where
  | leaf (s : LiveSet)
  | one (s : LiveSet) (k : FTree)
  | two (s : LiveSet) (a b : FTree)
  | three (s : LiveSet) (a b c : FTree)

/-- The set of free variables at the root of the tree. -/
def FTree.set : FTree → LiveSet
  | .leaf s => s
  | .one s _ => s
  | .two s _ _ => s
  | .three s _ _ _ => s

theorem FTree.set_leaf (s : LiveSet) : (FTree.leaf s).set = s := rfl
theorem FTree.set_one (s : LiveSet) (k : FTree) : (FTree.one s k).set = s := rfl
theorem FTree.set_two (s : LiveSet) (a b : FTree) : (FTree.two s a b).set = s := rfl
theorem FTree.set_three (s : LiveSet) (a b c : FTree) : (FTree.three s a b c).set = s := rfl

/-- **The free variables** of a program and of each subprogram, by de Bruijn index. -/
def fvTree : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → FTree
  | _, _, .ret vs => .leaf (varsSet vs)
  | _, _, .var e k =>
      let t := fvTree k
      .one (LiveSet.union (varsSet e.args) (LiveSet.shift 1 t.set)) t
  | _, _, .forLoop (cs := cs) count inits body k =>
      let tb := fvTree body
      let tk := fvTree k
      .two (LiveSet.union [count.idx] (LiveSet.union (varsSet inits)
        (LiveSet.union (LiveSet.shift (cs.length + 1) tb.set) (LiveSet.shift cs.length tk.set))))
        tb tk
  | _, _, .ifThenElse (rs := rs) cond thn els k =>
      let tt := fvTree thn
      let te := fvTree els
      let tk := fvTree k
      .three (LiveSet.union [cond.idx]
        (LiveSet.union tt.set (LiveSet.union te.set (LiveSet.shift rs.length tk.set)))) tt te tk
  | _, _, .whileLoop (cs := cs) inits body k =>
      let tb := fvTree body
      let tk := fvTree k
      .two (LiveSet.union (varsSet inits)
        (LiveSet.union (LiveSet.shift cs.length tb.set) (LiveSet.shift cs.length tk.set))) tb tk
  | _, _, .call (rs := rs) _ args k =>
      let tk := fvTree k
      .one (LiveSet.union (varsSet args) (LiveSet.shift rs.length tk.set)) tk

/-! ## 2. Agreement of fact maps -/

/-- `A` and `B` agree at every variable whose index is in `S` and not in `R`. -/
def FactsAgreeOff {Γ : Ctxt jasminDialect} (A B : Facts Γ) (R S : LiveSet) : Prop :=
  ∀ {s : JasminTy} (v : Var Γ s), v.idx ∈ S → v.idx ∉ R → A v = B v

theorem mem_varsSet_cons {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (v : Var Γ t) (vs : HVector (fun t => Var Γ t) ts) (i : Nat) :
    i ∈ varsSet (.cons v vs) ↔ i = v.idx ∨ i ∈ varsSet vs := by
  change i ∈ LiveSet.union [v.idx] (varsSet vs) ↔ _
  simp [LiveSet.mem_union]

theorem allExactB_congr {Γ : Ctxt jasminDialect} {A B : Facts Γ} :
    {ts : List JasminTy} → (vs : HVector (fun t => Var Γ t) ts) →
      FactsAgreeOff A B [] (varsSet vs) → allExactB A vs = allExactB B vs
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, h => by
      change ((A v).relW.isNone && allExactB A vs) = ((B v).relW.isNone && allExactB B vs)
      have e1 : A v = B v := h v ((mem_varsSet_cons v vs _).mpr (.inl rfl)) List.not_mem_nil
      have e2 := allExactB_congr vs fun w hw hr => h w ((mem_varsSet_cons v vs _).mpr (.inr hw)) hr
      rw [e1, e2]

theorem agreeOff_head {Γ : Ctxt jasminDialect} {A B : Facts Γ} {t : JasminTy}
    {ts : List JasminTy} (args : HVector (fun t => Var Γ t) (t :: ts))
    (h : FactsAgreeOff A B [] (varsSet args)) : A args.head = B args.head := by
  cases args with
  | cons v vs => exact h v ((mem_varsSet_cons v vs _).mpr (.inl rfl)) List.not_mem_nil

theorem agreeOff_tail {Γ : Ctxt jasminDialect} {A B : Facts Γ} {t : JasminTy}
    {ts : List JasminTy} (args : HVector (fun t => Var Γ t) (t :: ts))
    (h : FactsAgreeOff A B [] (varsSet args)) : FactsAgreeOff A B [] (varsSet args.tail) := by
  cases args with
  | cons v vs => exact fun w hw hr => h w ((mem_varsSet_cons v vs _).mpr (.inr hw)) hr

/-- The analysis of an expression reads the facts of its arguments only. -/
theorem okE_congr {Γ : Ctxt jasminDialect} {t : JasminTy} {A B : Facts Γ}
    (e : Expr jasminDialect Γ t) (h : FactsAgreeOff A B [] (varsSet e.args)) :
    okE A e = okE B e := by
  obtain ⟨op, _, args⟩ := e
  have hall := allExactB_congr args h
  simp only [okE]
  cases op <;> simp only [okOp, exactOp, hall]
  · rename_i bop w _
    have h1 : A args.head = B args.head := agreeOff_head (ts := [.reg w]) args h
    have h2 : A args.tail.head = B args.tail.head :=
      agreeOff_head (ts := []) args.tail (agreeOff_tail (ts := [.reg w]) args h)
    rw [h2]
    cases bop <;> simp only [h1, hall] <;> split <;> (try simp only [h2])
    generalize maskWidth? (B args.tail.head) = mw
    cases mw <;> simp only [h1, h2, hall]
  · have h1 : A args.head = B args.head := agreeOff_head (ts := []) args h
    rw [h1]

/-- The indices of a set raised by `k`: the set seen from under `k` more bindings. -/
def shiftUp (k : Nat) (R : LiveSet) : LiveSet := R.map (· + k)

theorem mem_shiftUp {k n : Nat} {R : LiveSet} : n ∈ shiftUp k R ↔ k ≤ n ∧ n - k ∈ R := by
  simp only [shiftUp, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Nat.le_add_left _ _, by simpa using ha⟩
  · rintro ⟨hk, hn⟩
    exact ⟨n - k, hn, Nat.sub_add_cancel hk⟩

theorem agreeOff_congrS {Γ : Ctxt jasminDialect} {A B : Facts Γ} {R S S' : LiveSet}
    (hS : ∀ i, i ∈ S' → i ∈ S) (h : FactsAgreeOff A B R S) : FactsAgreeOff A B R S' :=
  fun v hv hr => h v (hS _ hv) hr

theorem agreeOff_mono {Γ : Ctxt jasminDialect} {A B : Facts Γ} {R R' S : LiveSet}
    (hR : ∀ i, i ∈ S → i ∉ R' → i ∉ R) (h : FactsAgreeOff A B R S) : FactsAgreeOff A B R' S :=
  fun v hv hr => h v hv (hR _ hv hr)

theorem agreeOff_push {Γ : Ctxt jasminDialect} {t : JasminTy} {A B : Facts Γ} {R R' S : LiveSet}
    {i j : Info} (h : FactsAgreeOff A B R (LiveSet.shift 1 S)) (h0 : 0 ∈ S → 0 ∉ R' → i = j)
    (hR : ∀ n, n + 1 ∉ R' → n ∉ R) :
    FactsAgreeOff (Facts.push (t := t) i A) (Facts.push j B) R' S := by
  intro s v hv hr
  cases v with
  | here => exact h0 hv hr
  | there v => exact h v (LiveSet.mem_shift.mpr hv) (hR _ hr)

theorem agreeOff_appExact {Γ : Ctxt jasminDialect} {A B : Facts Γ} {R : LiveSet} :
    ∀ (cs : List JasminTy) {S : LiveSet}, FactsAgreeOff A B R (LiveSet.shift cs.length S) →
      FactsAgreeOff (Facts.appExact cs A) (Facts.appExact cs B) (shiftUp cs.length R) S
  | [], S, h => by
      refine agreeOff_mono (R := R) (fun i _ hi => ?_) (agreeOff_congrS (S := LiveSet.shift 0 S)
        (fun i hi => by simpa [LiveSet.mem_shift] using hi) h)
      simpa [mem_shiftUp] using hi
  | c :: cs, S, h => by
      refine agreeOff_push (agreeOff_appExact cs (agreeOff_congrS (fun i hi => ?_) h))
        (fun _ _ => rfl) (fun n hn hR => hn ?_)
      · simp only [LiveSet.mem_shift, List.length_cons] at hi ⊢
        rwa [Nat.add_assoc] at hi
      · simp only [mem_shiftUp, List.length_cons] at hR ⊢
        obtain ⟨h1, h2⟩ := hR
        refine ⟨by omega, ?_⟩
        rwa [show n + 1 - (cs.length + 1) = n - cs.length by omega]

theorem agreeOff_appExact0 {Γ : Ctxt jasminDialect} {A B : Facts Γ} (cs : List JasminTy)
    {S : LiveSet} (h : FactsAgreeOff A B [] (LiveSet.shift cs.length S)) :
    FactsAgreeOff (Facts.appExact cs A) (Facts.appExact cs B) [] S :=
  fun v hv _ => agreeOff_appExact cs h v hv (by simp [shiftUp])

/-- **The analysis reads the facts of the free variables only.** -/
theorem okP_congr {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {A B : Facts Γ}, FactsAgreeOff A B [] (fvTree p).set → okP p A = okP p B := by
  induction p with
  | ret vs => intro A B h; exact allExactB_congr vs h
  | var e k ih =>
      intro A B h
      have he : okE A e = okE B e := okE_congr e (agreeOff_congrS
        (fun i hi => LiveSet.mem_union.mpr (.inl hi)) h)
      simp only [okP, he]
      split
      · exact ih (agreeOff_push (agreeOff_congrS (fun i hi => LiveSet.mem_union.mpr (.inr hi)) h)
          (fun _ _ => rfl) (fun _ _ => List.not_mem_nil))
      · rfl
  | forLoop count inits body k ihb ihk =>
      intro A B h
      simp only [fvTree, FTree.set_two] at h
      have hc : A count = B count := h count (by simp [LiveSet.mem_union]) List.not_mem_nil
      have hi := allExactB_congr inits (agreeOff_congrS
        (fun i hi => by simp [LiveSet.mem_union, hi]) h)
      have hb := ihb (agreeOff_appExact0 _ (agreeOff_push (i := .exact) (j := .exact)
        (agreeOff_congrS (fun i hi => by
          simp only [LiveSet.mem_shift] at hi
          simp only [LiveSet.mem_union, LiveSet.mem_shift]
          right; right; left; rwa [Nat.add_comm _ 1, ← Nat.add_assoc]) h)
        (fun _ _ => rfl) (fun _ _ => List.not_mem_nil)))
      have hk := ihk (agreeOff_appExact0 _ (agreeOff_congrS (fun i hi => by
          simp only [LiveSet.mem_union, LiveSet.mem_shift] at hi ⊢
          right; right; right; exact hi) h))
      simp only [okP, hc, hi, hb, hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro A B h
      simp only [fvTree, FTree.set_three] at h
      have hc : A cond = B cond := h cond (by simp [LiveSet.mem_union]) List.not_mem_nil
      have ht := iht (agreeOff_congrS (fun i hi => by simp [LiveSet.mem_union, hi]) h)
      have he := ihe (agreeOff_congrS (fun i hi => by simp [LiveSet.mem_union, hi]) h)
      have hk := ihk (agreeOff_appExact0 _ (agreeOff_congrS (fun i hi => by
          simp only [LiveSet.mem_union, LiveSet.mem_shift] at hi ⊢
          right; right; right; exact hi) h))
      simp only [okP, hc, ht, he, hk]
  | whileLoop inits body k ihb ihk =>
      intro A B h
      simp only [fvTree, FTree.set_two] at h
      have hi := allExactB_congr inits (agreeOff_congrS
        (fun i hi => by simp [LiveSet.mem_union, hi]) h)
      have hb := ihb (agreeOff_appExact0 _ (agreeOff_congrS (fun i hi => by
          simp only [LiveSet.mem_union, LiveSet.mem_shift] at hi ⊢
          right; left; exact hi) h))
      have hk := ihk (agreeOff_appExact0 _ (agreeOff_congrS (fun i hi => by
          simp only [LiveSet.mem_union, LiveSet.mem_shift] at hi ⊢
          right; right; exact hi) h))
      simp only [okP, hi, hb, hk]
  | call fn args k ih =>
      intro A B h
      simp only [fvTree, FTree.set_one] at h
      have ha := allExactB_congr args (agreeOff_congrS
        (fun i hi => by simp [LiveSet.mem_union, hi]) h)
      have hk := ih (agreeOff_appExact0 _ (agreeOff_congrS (fun i hi => by
          simp only [LiveSet.mem_union, LiveSet.mem_shift] at hi ⊢
          right; exact hi) h))
      simp only [okP, ha, hk]

/-! ## 3. The analysis along a set of tainted indices -/

/-- **The analysis along the tainted indices `R`**, at the tree `t` of the free variables of
    `p`: the tainted indices `p` does not read are dropped; with none left the program passes;
    otherwise each binding is analysed as by `okP`, its variable tainted when it reads a
    tainted variable. At a tree of another shape it is `okP`. -/
def okPT : FTree → {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Facts Γ → LiveSet → Bool
  | t, _, _, p, A, R =>
    let R := R.filter fun r => t.set.contains r
    if R.isEmpty then true else
    match t, p with
    | .leaf _, .ret vs => allExactB A vs
    | .one _ tk, .var e k =>
        match okE A e with
        | some i => okPT tk k (A.push i)
            (if (varsSet e.args).any (R.contains ·) then 0 :: shiftUp 1 R else shiftUp 1 R)
        | none => false
    | .two _ tb tk, .forLoop (cs := cs) count inits body k =>
        (A count).relW.isNone && allExactB A inits &&
          okPT tb body (Facts.appExact cs (A.push .exact)) (shiftUp (cs.length + 1) R) &&
          okPT tk k (Facts.appExact cs A) (shiftUp cs.length R)
    | .three _ tt te tk, .ifThenElse (rs := rs) cond thn els k =>
        (A cond).relW.isNone && okPT tt thn A R && okPT te els A R &&
          okPT tk k (Facts.appExact rs A) (shiftUp rs.length R)
    | .two _ tb tk, .whileLoop (cs := cs) inits body k =>
        allExactB A inits && okPT tb body (Facts.appExact cs A) (shiftUp cs.length R) &&
          okPT tk k (Facts.appExact cs A) (shiftUp cs.length R)
    | .one _ tk, .call (rs := rs) _ args k =>
        allExactB A args && okPT tk k (Facts.appExact rs A) (shiftUp rs.length R)
    | _, p => okP p A

theorem agreeOff_appExact_push {Γ : Ctxt jasminDialect} {A B : Facts Γ} {R : LiveSet}
    (cs : List JasminTy) {t : JasminTy} {S : LiveSet}
    (h : FactsAgreeOff A B R (LiveSet.shift (cs.length + 1) S)) :
    FactsAgreeOff (Facts.appExact cs (Facts.push (t := t) .exact A))
      (Facts.appExact cs (Facts.push .exact B)) (shiftUp (cs.length + 1) R) S := by
  refine agreeOff_mono (fun i _ hi hR => hi ?_) (agreeOff_appExact cs (agreeOff_push
    (R' := shiftUp 1 R) (agreeOff_congrS (fun i hi => ?_) h) (fun _ _ => rfl) (fun n hn hr => ?_)))
  · simp only [mem_shiftUp] at hR ⊢
    obtain ⟨h1, h2, h3⟩ := hR
    exact ⟨by omega, by rwa [Nat.sub_sub] at h3⟩
  · simp only [LiveSet.mem_shift] at hi ⊢
    rwa [Nat.add_assoc, Nat.add_comm 1] at hi
  · exact hn (mem_shiftUp.mpr ⟨by omega, by simpa using hr⟩)

/-- The tainted indices of `R` in `S`. -/
abbrev liveIn (S R : LiveSet) : LiveSet := R.filter fun r => S.contains r

theorem okPT_ret {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (vs : HVector (fun t => Var Γ t) ts) (s : LiveSet) (A : Facts Γ) (R : LiveSet) :
    okPT (.leaf s) (.ret vs) A R = if (liveIn s R).isEmpty then true else allExactB A vs := by
  rw [okPT]; rfl

theorem okPT_var {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts) (s : LiveSet) (tk : FTree)
    (A : Facts Γ) (R : LiveSet) :
    okPT (.one s tk) (.var e k) A R = if (liveIn s R).isEmpty then true else
      match okE A e with
      | some i => okPT tk k (A.push i) (if (varsSet e.args).any ((liveIn s R).contains ·) then
          0 :: shiftUp 1 (liveIn s R) else shiftUp 1 (liveIn s R))
      | none => false := by
  rw [okPT]; rfl

theorem okPT_forLoop {Γ : Ctxt jasminDialect} {cs ts : List JasminTy}
    (count : Var Γ (HasWord64.word (d := jasminDialect))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts) (s : LiveSet) (tb tk : FTree) (A : Facts Γ)
    (R : LiveSet) :
    okPT (.two s tb tk) (.forLoop count inits body k) A R = if (liveIn s R).isEmpty then true else
      ((A count).relW.isNone && allExactB A inits &&
        okPT tb body (Facts.appExact cs (A.push .exact)) (shiftUp (cs.length + 1) (liveIn s R)) &&
        okPT tk k (Facts.appExact cs A) (shiftUp cs.length (liveIn s R))) := by
  rw [okPT]; rfl

theorem okPT_ifThenElse {Γ : Ctxt jasminDialect} {rs ts : List JasminTy}
    (cond : Var Γ (HasBitType.bit (d := jasminDialect))) (thn els : NFProg jasminDialect Γ rs)
    (k : NFProg jasminDialect (rs ++ Γ) ts) (s : LiveSet) (tt te tk : FTree) (A : Facts Γ)
    (R : LiveSet) :
    okPT (.three s tt te tk) (.ifThenElse cond thn els k) A R =
      if (liveIn s R).isEmpty then true else
      ((A cond).relW.isNone && okPT tt thn A (liveIn s R) && okPT te els A (liveIn s R) &&
        okPT tk k (Facts.appExact rs A) (shiftUp rs.length (liveIn s R))) := by
  rw [okPT]; rfl

theorem okPT_whileLoop {Γ : Ctxt jasminDialect} {cs ts : List JasminTy}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs))
    (k : NFProg jasminDialect (cs ++ Γ) ts) (s : LiveSet) (tb tk : FTree) (A : Facts Γ)
    (R : LiveSet) :
    okPT (.two s tb tk) (.whileLoop inits body k) A R = if (liveIn s R).isEmpty then true else
      (allExactB A inits &&
        okPT tb body (Facts.appExact cs A) (shiftUp cs.length (liveIn s R)) &&
        okPT tk k (Facts.appExact cs A) (shiftUp cs.length (liveIn s R))) := by
  rw [okPT]; rfl

theorem okPT_call {Γ : Ctxt jasminDialect} {as rs ts : List JasminTy} (fn : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg jasminDialect (rs ++ Γ) ts) (s : LiveSet)
    (tk : FTree) (A : Facts Γ) (R : LiveSet) :
    okPT (.one s tk) (.call fn args k) A R = if (liveIn s R).isEmpty then true else
      (allExactB A args && okPT tk k (Facts.appExact rs A) (shiftUp rs.length (liveIn s R))) := by
  rw [okPT]; rfl

theorem mem_filter_set {S R : LiveSet} {i : Nat} (hi : i ∈ S) :
    i ∈ R.filter (fun r => S.contains r) ↔ i ∈ R := by
  simp [List.mem_filter, hi]

/-- The tainted indices a program reads keep the agreement of the full set. -/
theorem agreeOff_filter {Γ : Ctxt jasminDialect} {A B : Facts Γ} {R S : LiveSet}
    (h : FactsAgreeOff A B R S) : FactsAgreeOff A B (R.filter fun r => S.contains r) S :=
  agreeOff_mono (fun _ hi hr hR => hr ((mem_filter_set hi).mpr hR)) h

theorem agreeOff_nil_of_isEmpty {Γ : Ctxt jasminDialect} {A B : Facts Γ} {R S : LiveSet}
    (h : FactsAgreeOff A B R S) (he : R.isEmpty = true) : FactsAgreeOff A B [] S := by
  rw [List.isEmpty_iff] at he
  subst he
  exact h

/-- **At fact maps that agree outside the tainted indices, where the analysis holds at the
    second, `okPT` is the analysis at the first.** -/
theorem okPT_eq {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {A B : Facts Γ} {R : LiveSet}, FactsAgreeOff A B R (fvTree p).set → okP p B = true →
      okPT (fvTree p) p A R = okP p A := by
  induction p with
  | ret vs =>
      intro A B R h hB
      change okPT (.leaf _) _ A R = _
      rw [okPT_ret]
      split
      · rename_i he
        exact ((okP_congr _ (agreeOff_nil_of_isEmpty (agreeOff_filter h) he)).trans hB).symm
      · rfl
  | var e k ih =>
      intro A B R h hB
      change okPT (.one _ (fvTree k)) _ A R = _
      rw [okPT_var]
      split
      · rename_i he
        exact ((okP_congr _ (agreeOff_nil_of_isEmpty (agreeOff_filter h) he)).trans hB).symm
      · have hf : FactsAgreeOff A B (liveIn (fvTree (.var e k)).set R) (fvTree (.var e k)).set :=
          agreeOff_filter h
        simp only [fvTree, FTree.set_one] at hf
        have hB' := hB
        simp only [okP] at hB'
        cases hj : okE B e with
        | none => simp [hj] at hB'
        | some j =>
          simp only [hj] at hB'
          simp only [okP]
          cases hi : okE A e with
          | none => rfl
          | some i =>
            refine ih (agreeOff_push (agreeOff_congrS
              (fun x hx => LiveSet.mem_union.mpr (.inr hx)) hf) (fun _ hn => ?_) (fun n hn => ?_)) hB'
            · split at hn
              · simp at hn
              · rename_i hany
                have he : okE A e = okE B e := okE_congr e fun v hv _ =>
                  hf v (LiveSet.mem_union.mpr (.inl hv)) fun hr =>
                    hany (List.any_eq_true.mpr ⟨v.idx, hv, List.elem_eq_true_of_mem hr⟩)
                rw [hi, hj] at he
                exact Option.some.inj he
            · intro hr
              apply hn
              split
              · exact List.mem_cons_of_mem _ (mem_shiftUp.mpr ⟨by omega, by simpa using hr⟩)
              · exact mem_shiftUp.mpr ⟨by omega, by simpa using hr⟩
  | forLoop count inits body k ihb ihk =>
      intro A B R h hB
      change okPT (.two _ (fvTree body) (fvTree k)) _ A R = _
      rw [okPT_forLoop]
      split
      · rename_i he
        exact ((okP_congr _ (agreeOff_nil_of_isEmpty (agreeOff_filter h) he)).trans hB).symm
      · have hf : FactsAgreeOff A B (liveIn (fvTree (.forLoop count inits body k)).set R)
            (fvTree (.forLoop count inits body k)).set := agreeOff_filter h
        simp only [fvTree, FTree.set_two] at hf
        simp only [okP, Bool.and_eq_true] at hB
        obtain ⟨⟨-, hb⟩, hk⟩ := hB
        rw [ihb (agreeOff_appExact_push _ (agreeOff_congrS (fun i hi => by
            simp only [LiveSet.mem_union] at hi ⊢; tauto) hf)) hb,
          ihk (agreeOff_appExact _ (agreeOff_congrS (fun i hi => by
            simp only [LiveSet.mem_union] at hi ⊢; tauto) hf)) hk]
        rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      intro A B R h hB
      change okPT (.three _ (fvTree thn) (fvTree els) (fvTree k)) _ A R = _
      rw [okPT_ifThenElse]
      split
      · rename_i he
        exact ((okP_congr _ (agreeOff_nil_of_isEmpty (agreeOff_filter h) he)).trans hB).symm
      · have hf : FactsAgreeOff A B (liveIn (fvTree (.ifThenElse cond thn els k)).set R)
            (fvTree (.ifThenElse cond thn els k)).set := agreeOff_filter h
        simp only [fvTree, FTree.set_three] at hf
        simp only [okP, Bool.and_eq_true] at hB
        obtain ⟨⟨⟨-, ht⟩, he⟩, hk⟩ := hB
        rw [iht (agreeOff_congrS (fun i hi => by
            simp only [LiveSet.mem_union] at hi ⊢; tauto) hf) ht,
          ihe (agreeOff_congrS (fun i hi => by
            simp only [LiveSet.mem_union] at hi ⊢; tauto) hf) he,
          ihk (agreeOff_appExact _ (agreeOff_congrS (fun i hi => by
            simp only [LiveSet.mem_union] at hi ⊢; tauto) hf)) hk]
        rfl
  | whileLoop inits body k ihb ihk =>
      intro A B R h hB
      change okPT (.two _ (fvTree body) (fvTree k)) _ A R = _
      rw [okPT_whileLoop]
      split
      · rename_i he
        exact ((okP_congr _ (agreeOff_nil_of_isEmpty (agreeOff_filter h) he)).trans hB).symm
      · have hf : FactsAgreeOff A B (liveIn (fvTree (.whileLoop inits body k)).set R)
            (fvTree (.whileLoop inits body k)).set := agreeOff_filter h
        simp only [fvTree, FTree.set_two] at hf
        simp only [okP, Bool.and_eq_true] at hB
        obtain ⟨⟨-, hb⟩, hk⟩ := hB
        rw [ihb (agreeOff_appExact _ (agreeOff_congrS (fun i hi => by
            simp only [LiveSet.mem_union] at hi ⊢; tauto) hf)) hb,
          ihk (agreeOff_appExact _ (agreeOff_congrS (fun i hi => by
            simp only [LiveSet.mem_union] at hi ⊢; tauto) hf)) hk]
        rfl
  | call fn args k ih =>
      intro A B R h hB
      change okPT (.one _ (fvTree k)) _ A R = _
      rw [okPT_call]
      split
      · rename_i he
        exact ((okP_congr _ (agreeOff_nil_of_isEmpty (agreeOff_filter h) he)).trans hB).symm
      · have hf : FactsAgreeOff A B (liveIn (fvTree (.call fn args k)).set R)
            (fvTree (.call fn args k)).set := agreeOff_filter h
        simp only [fvTree, FTree.set_one] at hf
        simp only [okP, Bool.and_eq_true] at hB
        obtain ⟨-, hk⟩ := hB
        rw [ih (agreeOff_appExact _ (agreeOff_congrS (fun i hi => by
            simp only [LiveSet.mem_union] at hi ⊢; tauto) hf)) hk]
        rfl

/-! ## 4. The pass -/

/-- **Mask elimination deciding each mask with `okPT`** at the tree of the free variables of the
    continuation and the mask's own index tainted; at a tree of another shape, `maskElimGo`. -/
def maskElimGoF : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → FTree → Facts Γ → Ctxt.Hom Γ Δ → NFProg jasminDialect Δ ts
  | _, _, _, .ret vs, _, _, ren => .ret (HVector.renameVars ren vs)
  | _, _, _, .var e k, .one _ tk, A, ren =>
      match maskOf? A e with
      | some ⟨(x, m), h⟩ =>
          if okPT tk k (A.push (.relaxed m)) [0] then
            maskElimGoF k tk (A.push (.relaxed m))
              (bindHom (.cons (varTyCast h.symm (ren x)) .nil) ren)
          else .var (e.rename ren) (maskElimGoF k tk (A.push ((okE A e).getD .exact))
            (Ctxt.Hom.lift ren))
      | none => .var (e.rename ren) (maskElimGoF k tk (A.push ((okE A e).getD .exact))
          (Ctxt.Hom.lift ren))
  | _, _, _, .forLoop (cs := cs) count inits body k, .two _ tb tk, A, ren =>
      .forLoop (ren count) (HVector.renameVars ren inits)
        (maskElimGoF body tb (Facts.appExact cs (A.push .exact))
          (appLift cs (Ctxt.Hom.lift ren)))
        (maskElimGoF k tk (Facts.appExact cs A) (appLift cs ren))
  | _, _, _, .ifThenElse (rs := rs) cond thn els k, .three _ tt te tk, A, ren =>
      .ifThenElse (ren cond) (maskElimGoF thn tt A ren) (maskElimGoF els te A ren)
        (maskElimGoF k tk (Facts.appExact rs A) (appLift rs ren))
  | _, _, _, .whileLoop (cs := cs) inits body k, .two _ tb tk, A, ren =>
      .whileLoop (HVector.renameVars ren inits) (maskElimGoF body tb (Facts.appExact cs A)
        (appLift cs ren)) (maskElimGoF k tk (Facts.appExact cs A) (appLift cs ren))
  | _, _, _, .call (rs := rs) f args k, .one _ tk, A, ren =>
      .call f (HVector.renameVars ren args)
        (maskElimGoF k tk (Facts.appExact rs A) (appLift rs ren))
  | _, _, _, p, _, A, ren => maskElimGo p A ren

/-- **Mask elimination by the uses of each mask**: `maskElimGoF` at the tree of the free
    variables, with exact information everywhere and the identity renaming. -/
def maskElimFast {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    NFProg jasminDialect Γ ts :=
  maskElimGoF p (fvTree p) (fun _ => .exact) (fun v => v)

/-- The fact maps `A.push i` and `A.push j` agree off the index `0`. -/
theorem agreeOff_push_zero {Γ : Ctxt jasminDialect} {t : JasminTy} (A : Facts Γ) (i j : Info)
    (S : LiveSet) : FactsAgreeOff (Facts.push (t := t) i A) (Facts.push j A) [0] S := by
  intro s v _ hr
  cases v with
  | here => exact absurd (List.mem_singleton_self _) hr
  | there v => rfl

/-- **`maskElimGoF` is `maskElimGo` wherever the analysis holds.** -/
theorem maskElimGoF_eq {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ), okP p A = true →
      maskElimGoF p (fvTree p) A ren = maskElimGo p A ren := by
  induction p with
  | ret vs => intro Δ A ren _; rfl
  | var e k ih =>
      intro Δ A ren hok
      simp only [okP] at hok
      split at hok
      · rename_i i hi
        change maskElimGoF _ (.one _ (fvTree k)) A ren = _
        simp only [maskElimGoF]
        split
        · rename_i x m h he
          have hT : okPT (fvTree k) k (A.push (.relaxed m)) [0] = okP k (A.push (.relaxed m)) :=
            okPT_eq k (agreeOff_push_zero A (.relaxed m) i _) hok
          rw [hT]
          split
          · rename_i hk
            rw [maskElimGo_var_mask e k A ren x m h he hk]
            exact ih _ _ hk
          · rename_i hk
            rw [maskElimGo_var_keep e k A ren (fun x' m' h' he' => by
              rw [he] at he'
              simp only [Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq] at he'
              obtain ⟨-, rfl⟩ := he'
              simpa using hk), hi, Option.getD_some, ih _ _ hok]
        · rename_i hn
          rw [maskElimGo_var_keep e k A ren (fun x' m' h' he' => by
            rw [hn] at he'
            cases he'), hi, Option.getD_some, ih _ _ hok]
      · cases hok
  | forLoop count inits body k ihb ihk =>
      intro Δ A ren hok
      simp only [okP, Bool.and_eq_true] at hok
      obtain ⟨⟨-, hb⟩, hk⟩ := hok
      change maskElimGoF _ (.two _ (fvTree body) (fvTree k)) A ren = _
      simp only [maskElimGoF, maskElimGo, ihb _ _ hb, ihk _ _ hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ A ren hok
      simp only [okP, Bool.and_eq_true] at hok
      obtain ⟨⟨⟨-, ht⟩, he⟩, hk⟩ := hok
      change maskElimGoF _ (.three _ (fvTree thn) (fvTree els) (fvTree k)) A ren = _
      simp only [maskElimGoF, maskElimGo, iht _ _ ht, ihe _ _ he, ihk _ _ hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ A ren hok
      simp only [okP, Bool.and_eq_true] at hok
      obtain ⟨⟨-, hb⟩, hk⟩ := hok
      change maskElimGoF _ (.two _ (fvTree body) (fvTree k)) A ren = _
      simp only [maskElimGoF, maskElimGo, ihb _ _ hb, ihk _ _ hk]
  | call fn args k ih =>
      intro Δ A ren hok
      simp only [okP, Bool.and_eq_true] at hok
      change maskElimGoF _ (.one _ (fvTree k)) A ren = _
      simp only [maskElimGoF, maskElimGo, ih _ _ hok.2]

/-- **`maskElim` is `maskElimFast`**: the compiled code of `maskElim` decides each mask on the
    uses of its value. -/
@[csimp] theorem maskElim_eq_maskElimFast : @maskElim = @maskElimFast := by
  funext Γ ts p
  exact (maskElimGoF_eq p _ _ (okP_of_noRelax p _ fun _ => rfl)).symm

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords
