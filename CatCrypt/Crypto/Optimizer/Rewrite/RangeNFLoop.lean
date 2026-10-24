/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
public import CatCryptCore.Tactics.KatGuard

/-!
# The range stage with checked intervals for loop-carried variables

The range stage `RangeNF.rangeNF` enters every variable a loop carries at the full lane range
of its type. The stage `loopRange` takes an annotation: for each loop of a structured program
`NFProg jasminDialect`, one proposed interval per carried variable. The annotation is not
trusted. A Boolean checker decides whether the proposed intervals are inductive for a loop,
and the traversal uses them for the body and the continuation of that loop only when the
checker accepts; otherwise the carried variables of that loop enter at the full lane range,
as in `rangeNF`.

## The checker

For a loop with carried tuple `cs`, start variables `inits`, proposed intervals `ivs` and
abstract environment `A` at the loop, `forInductive` is the conjunction of

* `argsWithin A inits ivs`: the interval of each start variable under `A` lies within its
  proposed interval;
* `retsWithin (invApp cs ivs (topCons word A)) body ivs`: the analysis of the body from the
  proposed intervals of the carried tuple and the full lane range of the trip index gives,
  at the return of the body, variables whose intervals lie within the proposed intervals.

`whileInductive` is the same condition for a loop in exit-flag form, with the full lane
range for the flag the body returns. An interval `a` lies within `i` (`tyWithin`) when
`i.1 ≤ a.1` and `a.2 ≤ i.2`, for `a` or for its lane interval `ivLane w a`. A proposed list
shorter than the carried tuple is read with the full lane range at the missing positions.

`retsWithin` runs the analysis of `rangeGo` and decides nested loops with the same checker,
so the environment in which it reads a return is the environment the traversal uses.

## Main definitions

* `CarriedAnn`: the annotation, a tree of proposed intervals that follows the loops and
  branches of a program.
* `argsWithin`, `retsWithin`, `forInductive`, `whileInductive`: the checker.
* `invApp`, `carriedEnv`: an abstract environment extended by carried variables at proposed
  intervals, and its choice by the result of the checker.
* `carriedGo`: the traversal of a structured program under an annotation.
* `loopRange`: the stage, the traversal from the full lane range of every input.
* `carriedStep`, `carriedCert`: the chain step of the stage for an annotation computed from
  the program, with the certificate that the output has the denotation of the input.
* `lazyAddLoop`, `lazyAddAnn`: a counted loop that adds a constant to a carried word and
  subtracts the BabyBear prime conditionally, with the interval `[0, p - 1]` proposed for the
  carried word.

## Main results

* `retsWithin_sound`: a result of a program whose returns the checker accepts lies within
  the proposed intervals.
* `carriedGo_denote`, `loopRange_denote`: the stage preserves the `NFProg` denotation at
  every fuel, for every annotation.
* `carriedGo_ctRel`, `loopRange_ctRel`: under a leakage model whose `regArith` operations are
  quiet, two runs of the input with equal events give two runs of the output with equal
  events.
* `loopRange_nfCT`: under such a model the stage keeps `NFCT`.
* `ifFree_loopRange`: the stage keeps a program branch-free.
* `carriedGo_empty`, `loopRange_empty`: at the empty annotation the stage is `rangeNF`.
* On `lazyAddLoop`, `rangeNF` keeps the three `and` operations of the program and
  `loopRange lazyAddAnn` keeps one (`#kat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF

/-! ## 1. Inclusion of intervals -/

/-- The interval `a` lies within the interval `i`. -/
def ivWithin (a i : Iv) : Bool := decide (i.1 ≤ a.1) && decide (a.2 ≤ i.2)

/-- A member of an interval is a member of every interval it lies within. -/
theorem mem_of_ivWithin {w : Nat} {a i : Iv} {x : BitVec w} (h : ivWithin a i = true)
    (hx : a.Mem w x) : i.Mem w x := by
  simp only [ivWithin, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨v, h1, h2, h3⟩ := hx
  exact ⟨v, le_trans h.1 h1, le_trans h2 h.2, h3⟩

/-- The interval `a` of a value of type `t` lies within `i`: for a register type, `a` or
    its lane interval lies within `i`; at every other type the condition is empty. -/
def tyWithin : JasminTy → Iv → Iv → Bool
  | .reg w, a, i => ivWithin a i || ivWithin (ivLane w a) i
  | _, _, _ => true

/-- A value in an interval is in every interval that `tyWithin` accepts for it. -/
theorem valMem_of_tyWithin : ∀ {t : JasminTy} {a i : Iv} {x : ⟦t⟧},
    tyWithin t a i = true → valMem t a x → valMem t i x
  | .reg w, a, i, x, h, hx => by
      simp only [tyWithin, Bool.or_eq_true] at h
      rcases h with h | h
      · exact mem_of_ivWithin h hx
      · exact mem_of_ivWithin h (Iv.Mem.lane hx)
  | .stackArr _ _, _, _, _, _, _ => trivial
  | .inlineInt, _, _, _, _, _ => trivial
  | .bool, _, _, _, _, _ => trivial

/-- Every value of a type is in the full lane range of the type. -/
theorem valMem_top : ∀ (t : JasminTy) (x : ⟦t⟧), valMem t (tyTop t) x
  | .reg _, x => Iv.mem_top x
  | .stackArr _ _, _ => trivial
  | .inlineInt, _ => trivial
  | .bool, _ => trivial

/-- A value in the interval `i` satisfies the abstract value `i` with no fact. -/
theorem valOK_of_valMem {Γ : JCtxt} (V : Ctxt.Valuation Γ) : ∀ {t : JasminTy} {i : Iv}
    {x : ⟦t⟧}, valMem t i x → ValOK V t (i, .none) x
  | .reg w, _, x, h => ⟨h, SymOK.none V w x⟩
  | .stackArr _ _, _, _, _ => trivial
  | .inlineInt, _, _, _ => trivial
  | .bool, _, _, _ => trivial

/-! ## 2. Abstract environments under carried variables at proposed intervals -/

/-- The abstract environment `A` extended by the prefix `cs` of variables, the `j`-th at
    the `j`-th interval of `ivs` with no fact, and at the full lane range of its type when
    `ivs` has no `j`-th entry. -/
def invApp : (cs : List JasminTy) → List Iv → {Γ : JCtxt} → AEnv Γ → AEnv (cs ++ Γ)
  | [], _, _, A => A
  | t :: cs, ivs, _, A =>
      HVector.cons (f := fun _ => AVal) (ivs.headD (tyTop t), .none) (invApp cs ivs.tail A)

/-- The tuple `X` of types `cs` lies within the intervals `ivs`, read as in `invApp`. -/
def InvOK : (cs : List JasminTy) → List Iv → Ctxt.Valuation (d := jasminDialect) cs → Prop
  | [], _, _ => True
  | t :: cs, ivs, .cons x X => valMem t (ivs.headD (tyTop t)) x ∧ InvOK cs ivs.tail X

/-- The tail of a tuple within a list of intervals lies within the tail of the list. -/
theorem invOK_tail {t : JasminTy} {cs : List JasminTy} {i : Iv} {ivs : List Iv} :
    ∀ (r : Ctxt.Valuation (d := jasminDialect) (t :: cs)), InvOK (t :: cs) (i :: ivs) r →
      InvOK cs ivs r.tail
  | .cons _ _, h => h.2

/-- An environment that holds of `V` holds, extended by `invApp`, of every extension of `V`
    by a prefix within the intervals. -/
theorem envOK_invApp : ∀ (cs : List JasminTy) (ivs : List Iv) {Γ : JCtxt} {A : AEnv Γ}
    (X : Ctxt.Valuation (d := jasminDialect) cs) {V : Ctxt.Valuation Γ}, InvOK cs ivs X →
    EnvOK A V →
    EnvOK (invApp cs ivs A) (hvAppend X V : Ctxt.Valuation (d := jasminDialect) (cs ++ Γ))
  | [], _, _, _, .nil, _, _, h => h
  | _ :: cs, ivs, _, _, .cons _ X, _, hX, h =>
      EnvOK.cons (Γ := cs ++ _) (envOK_invApp cs ivs.tail X hX.2 h) (valOK_of_valMem _ hX.1)

/-- At the empty list of intervals `invApp` is `topApp`. -/
theorem invApp_nil : ∀ (cs : List JasminTy) {Γ : JCtxt} (A : AEnv Γ),
    invApp cs [] A = topApp cs A
  | [], _, _ => rfl
  | t :: cs, _, A => by
      show HVector.cons (f := fun _ => AVal) (tyTop t, Sym.none) (invApp cs [] A) =
        topCons t (topApp cs A)
      rw [invApp_nil cs A]
      rfl

/-- The abstract environment of the variables a loop carries: `invApp` at the proposed
    intervals when the checker accepts them (`ok = true`), else `topApp`. -/
def carriedEnv (ok : Bool) (cs : List JasminTy) (ivs : List Iv) {Γ : JCtxt} (A : AEnv Γ) :
    AEnv (cs ++ Γ) :=
  match ok with
  | true => invApp cs ivs A
  | false => topApp cs A

/-- The carried tuple `X` lies within the intervals `ivs` when the checker accepted them. -/
def CarriedOK (ok : Bool) (cs : List JasminTy) (ivs : List Iv)
    (X : Ctxt.Valuation (d := jasminDialect) cs) : Prop :=
  ok = true → InvOK cs ivs X

/-- An environment that holds of `V` holds, extended by `carriedEnv`, of every extension of
    `V` by a carried tuple that satisfies `CarriedOK`. -/
theorem envOK_carriedEnv {ok : Bool} (cs : List JasminTy) (ivs : List Iv) {Γ : JCtxt}
    {A : AEnv Γ} (X : Ctxt.Valuation (d := jasminDialect) cs) {V : Ctxt.Valuation Γ}
    (hX : CarriedOK ok cs ivs X) (h : EnvOK A V) :
    EnvOK (carriedEnv ok cs ivs A)
      (hvAppend X V : Ctxt.Valuation (d := jasminDialect) (cs ++ Γ)) := by
  cases ok
  · exact envOK_topApp cs X h
  · exact envOK_invApp cs ivs X (hX rfl) h

/-- At the empty list of intervals `carriedEnv` is `topApp`, for both values of `ok`. -/
theorem carriedEnv_nil (ok : Bool) (cs : List JasminTy) {Γ : JCtxt} (A : AEnv Γ) :
    carriedEnv ok cs [] A = topApp cs A := by
  cases ok
  · rfl
  · exact invApp_nil cs A

/-! ## 3. The annotation -/

/-- An annotation of a structured program with proposed intervals for the variables its
    loops carry. An annotation addresses the first loop or branch of a program: let-bindings
    and calls are passed over.

    * `empty`: no proposal for the program.
    * `loop ivs body rest`: the intervals `ivs` for the carried tuple of a loop, with the
      annotations of its body and of its continuation.
    * `branch thn els rest`: the annotations of the arms of a branch and of its
      continuation. -/
inductive CarriedAnn where
  | empty
  | loop (ivs : List Iv) (body rest : CarriedAnn)
  | branch (thn els rest : CarriedAnn)

namespace CarriedAnn

/-- The intervals an annotation proposes for the carried tuple of a loop. -/
def ivs : CarriedAnn → List Iv
  | .loop i _ _ => i
  | _ => []

/-- The annotation of a loop body, or of the first arm of a branch. -/
def inner : CarriedAnn → CarriedAnn
  | .loop _ b _ => b
  | .branch t _ _ => t
  | .empty => .empty

/-- The annotation of the second arm of a branch. -/
def other : CarriedAnn → CarriedAnn
  | .branch _ e _ => e
  | _ => .empty

/-- The annotation of the continuation of a loop or a branch. -/
def rest : CarriedAnn → CarriedAnn
  | .loop _ _ r => r
  | .branch _ _ r => r
  | .empty => .empty

end CarriedAnn

/-! ## 4. The checker -/

/-- The interval of each variable of `vs` under `A` lies within its interval of `ivs`. -/
def argsWithin {Γ : JCtxt} (A : AEnv Γ) : {ts : List JasminTy} →
    HVector (fun t => Ctxt.Var Γ t) ts → List Iv → Bool
  | [], .nil, _ => true
  | t :: _, .cons v vs, ivs =>
      tyWithin t (hget A v).1 (ivs.headD (tyTop t)) && argsWithin A vs ivs.tail

/-- Variables that `argsWithin` accepts hold values within the intervals. -/
theorem argsWithin_sound {Γ : JCtxt} {A : AEnv Γ} {V : Ctxt.Valuation Γ} (hA : EnvOK A V) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts) (ivs : List Iv),
      argsWithin A vs ivs = true → InvOK ts ivs (Expr.lookupArgs vs V)
  | [], .nil, _, _ => trivial
  | t :: _, .cons v vs, ivs, h => by
      have h : (tyWithin t (hget A v).1 (ivs.headD (tyTop t)) &&
          argsWithin A vs ivs.tail) = true := h
      simp only [Bool.and_eq_true] at h
      exact ⟨valMem_of_tyWithin h.1 (hA t v).valMem, argsWithin_sound hA vs ivs.tail h.2⟩

/-- The analysis of `rangeGo` on `p` from `A` under the annotation `a` gives, at the return
    of `p`, variables whose intervals lie within `ivs`. The carried variables of a loop of
    `p` enter at the proposed intervals of `a` when those are inductive for the loop, and
    at the full lane range otherwise. -/
def retsWithin : {Γ : JCtxt} → {ts : List JasminTy} → AEnv Γ → Nat → CarriedAnn →
    NFProg jasminDialect Γ ts → List Iv → Bool
  | _, _, A, _, _, .ret vs, ivs => argsWithin A vs ivs
  | _, _, A, len, a, .var e k, ivs =>
      retsWithin (HVector.cons (f := fun _ => AVal) (stageAbs A e len) A) (len + 1) a k ivs
  | _, _, A, len, a, .forLoop (cs := cs) _ inits body k, ivs =>
      retsWithin
        (carriedEnv (argsWithin A inits a.ivs &&
            retsWithin (invApp cs a.ivs (topCons (HasWord64.word (d := jasminDialect)) A))
              (cs.length + (len + 1)) a.inner body a.ivs) cs a.ivs A)
        (cs.length + len) a.rest k ivs
  | _, _, A, len, a, .ifThenElse (rs := rs) _ _ _ k, ivs =>
      retsWithin (topApp rs A) (rs.length + len) a.rest k ivs
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k, ivs =>
      retsWithin
        (carriedEnv (argsWithin A inits a.ivs &&
            retsWithin (invApp cs a.ivs A) (cs.length + len) a.inner body
              (tyTop (HasBitType.bit (d := jasminDialect)) :: a.ivs)) cs a.ivs A)
        (cs.length + len) a.rest k ivs
  | _, _, A, len, a, .call (rs := rs) _ _ k, ivs =>
      retsWithin (topApp rs A) (rs.length + len) a k ivs

/-- The intervals `a.ivs` are inductive for a counted loop with start variables `inits` and
    body `body` under `A`: the start variables lie within them, and the analysis of the body
    from them returns variables within them. -/
def forInductive {Γ : JCtxt} {cs : List JasminTy} (A : AEnv Γ) (len : Nat) (a : CarriedAnn)
    (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs) :
    Bool :=
  argsWithin A inits a.ivs &&
    retsWithin (invApp cs a.ivs (topCons (HasWord64.word (d := jasminDialect)) A))
      (cs.length + (len + 1)) a.inner body a.ivs

/-- The intervals `a.ivs` are inductive for a loop in exit-flag form with start variables
    `inits` and body `body` under `A`. -/
def whileInductive {Γ : JCtxt} {cs : List JasminTy} (A : AEnv Γ) (len : Nat)
    (a : CarriedAnn) (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs)) :
    Bool :=
  argsWithin A inits a.ivs &&
    retsWithin (invApp cs a.ivs A) (cs.length + len) a.inner body
      (tyTop (HasBitType.bit (d := jasminDialect)) :: a.ivs)

/-- The start values of a counted loop satisfy `CarriedOK` at the result of the checker. -/
theorem forInductive_init {Γ : JCtxt} {cs : List JasminTy} {A : AEnv Γ} {len : Nat}
    {a : CarriedAnn} {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs}
    {V : Ctxt.Valuation Γ} (hA : EnvOK A V) :
    CarriedOK (forInductive A len a inits body) cs a.ivs (Expr.lookupArgs inits V) :=
  fun hok => by
    simp only [forInductive, Bool.and_eq_true] at hok
    exact argsWithin_sound hA inits a.ivs hok.1

/-- The start values of an exit-flag loop satisfy `CarriedOK` at the result of the
    checker. -/
theorem whileInductive_init {Γ : JCtxt} {cs : List JasminTy} {A : AEnv Γ} {len : Nat}
    {a : CarriedAnn} {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs)}
    {V : Ctxt.Valuation Γ} (hA : EnvOK A V) :
    CarriedOK (whileInductive A len a inits body) cs a.ivs (Expr.lookupArgs inits V) :=
  fun hok => by
    simp only [whileInductive, Bool.and_eq_true] at hok
    exact argsWithin_sound hA inits a.ivs hok.1

/-! ## 5. Iterations under an invariant -/

/-- A monadic fold whose step keeps `P` ends in a state that satisfies `P`. -/
theorem foldlM_inv {α : Type} (P : α → Prop) (f : α → Nat → Option α)
    (hf : ∀ acc i r, P acc → f acc i = some r → P r) :
    ∀ (l : List Nat) (acc r : α), P acc → l.foldlM f acc = some r → P r
  | [], acc, r, h, e => by
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at e
      exact e ▸ h
  | i :: l, acc, r, h, e => by
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at e
      obtain ⟨u, hu, e⟩ := e
      exact foldlM_inv P f hf l u r (hf acc i u h hu) e

/-- Two monadic folds whose steps agree on the states that satisfy `P`, from a state that
    satisfies `P`, are equal when the step keeps `P`. -/
theorem foldlM_congr_inv {α : Type} (P : α → Prop) (f g : α → Nat → Option α)
    (hg : ∀ acc i, P acc → g acc i = f acc i)
    (hf : ∀ acc i r, P acc → f acc i = some r → P r) :
    ∀ (l : List Nat) (acc : α), P acc → l.foldlM g acc = l.foldlM f acc
  | [], _, _ => rfl
  | i :: l, acc, h => by
      rw [List.foldlM_cons, List.foldlM_cons, hg acc i h]
      rcases hu : f acc i with _ | u
      · rfl
      · exact foldlM_congr_inv P f g hg hf l u (hf acc i u h hu)

/-- An exit-flag iteration whose step keeps `P` ends in a state that satisfies `P`. -/
theorem whileIter_inv {cs : List JasminTy}
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (f : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs)))
    (hf : ∀ acc r, P acc → f acc = some r → P r.tail) :
    ∀ (n : Nat) (acc r : Ctxt.Valuation (d := jasminDialect) cs), P acc →
      NFProg.whileIter f n acc = some r → P r
  | 0, _, _, _, e => by simp [NFProg.whileIter] at e
  | n + 1, acc, r, h, e => by
      simp only [NFProg.whileIter, Option.bind_eq_bind, Option.bind_eq_some_iff] at e
      obtain ⟨u, hu, e⟩ := e
      split at e
      · exact whileIter_inv P f hf n _ r (hf acc u h hu) e
      · cases e
        exact hf acc u h hu

/-- Two exit-flag iterations whose steps agree on the states that satisfy `P`, from a state
    that satisfies `P`, are equal when the step keeps `P`. -/
theorem whileIter_congr_inv {cs : List JasminTy}
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (f g : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs)))
    (hg : ∀ acc, P acc → g acc = f acc)
    (hf : ∀ acc r, P acc → f acc = some r → P r.tail) :
    ∀ (n : Nat) (acc : Ctxt.Valuation (d := jasminDialect) cs), P acc →
      NFProg.whileIter g n acc = NFProg.whileIter f n acc
  | 0, _, _ => rfl
  | n + 1, acc, h => by
      simp only [NFProg.whileIter, hg acc h]
      rcases hu : f acc with _ | u
      · rfl
      · simp only [Option.bind_eq_bind, Option.bind_some]
        split
        · exact whileIter_congr_inv P f g hg hf n _ (hf acc u h hu)
        · rfl

/-- Two binds are equal when their first computations are equal and their continuations
    agree on the result of the first. -/
theorem bind_congr_inv {α β : Type} {o o' : Option α} {K K' : α → Option β} (e : o' = o)
    (hK : ∀ x, o = some x → K' x = K x) : (o' >>= K') = (o >>= K) := by
  subst e
  rcases o' with _ | x
  · rfl
  · exact hK x rfl

/-! ## 6. Soundness of the checker -/

section Denote

variable [CallDenote jasminDialect]

/-- **Soundness of the checker.** Under an environment that holds of `V`, a result of a
    program whose returns `retsWithin` accepts for `ivs` lies within `ivs`. -/
theorem retsWithin_sound (fuel : Nat) : ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ)
    (len : Nat) (a : CarriedAnn) (p : NFProg jasminDialect Γ ts) (ivs : List Iv)
    (V : Ctxt.Valuation Γ), len = Γ.length → EnvOK A V → retsWithin A len a p ivs = true →
    ∀ R, p.denote fuel V = some R → InvOK ts ivs R
  | _, _, _, _, _, .ret vs, ivs, V, _, hA, hc, R, hR => by
      simp only [NFProg.denote, Option.some.injEq] at hR
      subst hR
      exact argsWithin_sound hA vs ivs hc
  | _, _, A, len, a, .var e k, ivs, V, hlen, hA, hc, R, hR => by
      simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some] at hR
      simp only [retsWithin] at hc
      exact retsWithin_sound fuel _ (len + 1) a k ivs _ (by simp [hlen])
        (hA.cons (stageAbs_sound hA hlen e)) hc R hR
  | _, _, A, len, a, .forLoop (cs := cs) count inits body k, ivs, V, hlen, hA, hc, R, hR => by
      simp only [NFProg.denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
      obtain ⟨acc, hacc, hR⟩ := hR
      simp only [retsWithin] at hc
      have hstep : ∀ (acc : Ctxt.Valuation (d := jasminDialect) cs) (i : Nat)
          (r : Ctxt.Valuation (d := jasminDialect) cs),
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          body.denote fuel
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) = some r →
          CarriedOK (forInductive A len a inits body) cs a.ivs r :=
        fun acc i r hP hr hok => by
          have hok' := hok
          simp only [forInductive, Bool.and_eq_true] at hok'
          exact retsWithin_sound fuel _ _ a.inner body a.ivs _ (length_body cs _ hlen)
            (envOK_invApp cs a.ivs acc (hP hok) (envOK_topCons hA _)) hok'.2 r hr
      have hfin := foldlM_inv _ _ hstep _ _ _ (forInductive_init hA) hacc
      exact retsWithin_sound fuel _ _ a.rest k ivs _ (length_app cs hlen)
        (envOK_carriedEnv cs a.ivs acc hfin hA) hc R hR
  | _, _, A, len, a, .ifThenElse (rs := rs) cond thn els k, ivs, V, hlen, hA, hc, R, hR => by
      simp only [NFProg.denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
      obtain ⟨r, _, hR⟩ := hR
      simp only [retsWithin] at hc
      exact retsWithin_sound fuel _ _ a.rest k ivs _ (length_app rs hlen)
        (envOK_topApp rs r hA) hc R hR
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k, ivs, V, hlen, hA, hc, R, hR => by
      simp only [NFProg.denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
      obtain ⟨acc, hacc, hR⟩ := hR
      simp only [retsWithin] at hc
      have hstep : ∀ (acc : Ctxt.Valuation (d := jasminDialect) cs)
          (r : Ctxt.Valuation (d := jasminDialect)
            (HasBitType.bit (d := jasminDialect) :: cs)),
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          body.denote fuel (hvAppend acc V) = some r →
          CarriedOK (whileInductive A len a inits body) cs a.ivs r.tail :=
        fun acc r hP hr hok => by
          have hok' := hok
          simp only [whileInductive, Bool.and_eq_true] at hok'
          exact invOK_tail r (retsWithin_sound fuel _ _ a.inner body _ _ (length_app cs hlen)
            (envOK_invApp cs a.ivs acc (hP hok) hA) hok'.2 r hr)
      have hfin := whileIter_inv _ _ hstep _ _ _ (whileInductive_init hA) hacc
      exact retsWithin_sound fuel _ _ a.rest k ivs _ (length_app cs hlen)
        (envOK_carriedEnv cs a.ivs acc hfin hA) hc R hR
  | _, _, A, len, a, .call (rs := rs) f args k, ivs, V, hlen, hA, hc, R, hR => by
      simp only [NFProg.denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
      obtain ⟨r, _, hR⟩ := hR
      simp only [retsWithin] at hc
      exact retsWithin_sound fuel _ _ a k ivs _ (length_app rs hlen)
        (envOK_topApp rs r hA) hc R hR

/-- The body of a counted loop keeps `CarriedOK` at the result of the checker. -/
theorem forInductive_step (fuel : Nat) {Γ : JCtxt} {cs : List JasminTy} {A : AEnv Γ}
    {len : Nat} {a : CarriedAnn} {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V)
    (acc : Ctxt.Valuation (d := jasminDialect) cs) (i : Nat)
    (r : Ctxt.Valuation (d := jasminDialect) cs)
    (hP : CarriedOK (forInductive A len a inits body) cs a.ivs acc)
    (hr : body.denote fuel
      (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) = some r) :
    CarriedOK (forInductive A len a inits body) cs a.ivs r := fun hok => by
  have hok' := hok
  simp only [forInductive, Bool.and_eq_true] at hok'
  exact retsWithin_sound fuel _ _ a.inner body a.ivs _ (length_body cs _ hlen)
    (envOK_invApp cs a.ivs acc (hP hok) (envOK_topCons hA _)) hok'.2 r hr

/-- The body of an exit-flag loop keeps `CarriedOK` at the result of the checker. -/
theorem whileInductive_step (fuel : Nat) {Γ : JCtxt} {cs : List JasminTy} {A : AEnv Γ}
    {len : Nat} {a : CarriedAnn} {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs)}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V)
    (acc : Ctxt.Valuation (d := jasminDialect) cs)
    (r : Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs))
    (hP : CarriedOK (whileInductive A len a inits body) cs a.ivs acc)
    (hr : body.denote fuel (hvAppend acc V) = some r) :
    CarriedOK (whileInductive A len a inits body) cs a.ivs r.tail := fun hok => by
  have hok' := hok
  simp only [whileInductive, Bool.and_eq_true] at hok'
  exact invOK_tail r (retsWithin_sound fuel _ _ a.inner body _ _ (length_app cs hlen)
    (envOK_invApp cs a.ivs acc (hP hok) hA) hok'.2 r hr)

end Denote

/-! ## 7. The traversal -/

/-- The range traversal of a structured program from the abstract environment `A` of a
    context of length `len` under the annotation `a`: `rangeGo`, with the carried variables
    of a loop at the proposed intervals of `a` in the body and in the continuation when the
    intervals are inductive for the loop, and at the full lane range otherwise. -/
def carriedGo : {Γ : JCtxt} → {ts : List JasminTy} → AEnv Γ → Nat → CarriedAnn →
    NFProg jasminDialect Γ ts → NFProg jasminDialect Γ ts
  | _, _, _, _, _, .ret vs => .ret vs
  | _, _, A, len, a, .var e k =>
      .var (rangeExpr A len e)
        (carriedGo (HVector.cons (f := fun _ => AVal) (stageAbs A e len) A) (len + 1) a k)
  | _, _, A, len, a, .forLoop (cs := cs) count inits body k =>
      .forLoop count inits
        (carriedGo
          (carriedEnv (forInductive A len a inits body) cs a.ivs
            (topCons (HasWord64.word (d := jasminDialect)) A))
          (cs.length + (len + 1)) a.inner body)
        (carriedGo (carriedEnv (forInductive A len a inits body) cs a.ivs A)
          (cs.length + len) a.rest k)
  | _, _, A, len, a, .ifThenElse (rs := rs) cond thn els k =>
      .ifThenElse cond (carriedGo A len a.inner thn) (carriedGo A len a.other els)
        (carriedGo (topApp rs A) (rs.length + len) a.rest k)
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k =>
      .whileLoop inits
        (carriedGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
          (cs.length + len) a.inner body)
        (carriedGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
          (cs.length + len) a.rest k)
  | _, _, A, len, a, .call (rs := rs) f args k =>
      .call f args (carriedGo (topApp rs A) (rs.length + len) a k)

/-- At the empty annotation the traversal is `rangeGo`. -/
theorem carriedGo_empty : ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat)
    (p : NFProg jasminDialect Γ ts), carriedGo A len .empty p = rangeGo A len p
  | _, _, _, _, .ret _ => rfl
  | _, _, A, len, .var e k => by
      simp only [carriedGo, rangeGo, carriedGo_empty]
  | _, _, A, len, .forLoop _ _ body k => by
      simp only [carriedGo, rangeGo, CarriedAnn.ivs, CarriedAnn.inner, CarriedAnn.rest,
        carriedEnv_nil, carriedGo_empty]
  | _, _, A, len, .ifThenElse _ thn els k => by
      simp only [carriedGo, rangeGo, CarriedAnn.inner, CarriedAnn.other, CarriedAnn.rest,
        carriedGo_empty]
  | _, _, A, len, .whileLoop _ body k => by
      simp only [carriedGo, rangeGo, CarriedAnn.ivs, CarriedAnn.inner, CarriedAnn.rest,
        carriedEnv_nil, carriedGo_empty]
  | _, _, A, len, .call _ _ k => by
      simp only [carriedGo, rangeGo, carriedGo_empty]

section Denote

variable [CallDenote jasminDialect]

/-- **Denotation of the traversal.** Under an environment that holds of `V`, the output
    denotes the input at `V`, at every fuel and for every annotation. -/
theorem carriedGo_denote (fuel : Nat) : ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ)
    (len : Nat) (a : CarriedAnn) (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ),
    len = Γ.length → EnvOK A V → (carriedGo A len a p).denote fuel V = p.denote fuel V
  | _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, A, len, a, .var e k, V, hlen, hA => by
      simp only [carriedGo, NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      rw [rangeExpr_denote hA hlen e]
      exact carriedGo_denote fuel _ (len + 1) a k _ (by simp [hlen])
        (hA.cons (stageAbs_sound hA hlen e))
  | _, _, A, len, a, .forLoop (cs := cs) count inits body k, V, hlen, hA => by
      have hb : ∀ (acc : Ctxt.Valuation (d := jasminDialect) cs) (i : Nat),
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          (carriedGo
              (carriedEnv (forInductive A len a inits body) cs a.ivs
                (topCons (HasWord64.word (d := jasminDialect)) A))
              (cs.length + (len + 1)) a.inner body).denote fuel
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) =
            body.denote fuel
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun acc i hP => carriedGo_denote fuel _ _ a.inner body _ (length_body cs _ hlen)
          (envOK_carriedEnv cs a.ivs acc hP (envOK_topCons hA _))
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          (carriedGo (carriedEnv (forInductive A len a inits body) cs a.ivs A)
              (cs.length + len) a.rest k).denote fuel (hvAppend acc V) =
            k.denote fuel (hvAppend acc V) :=
        fun acc hP => carriedGo_denote fuel _ _ a.rest k _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA)
      have hs := forInductive_step fuel (a := a) (inits := inits) (body := body) hlen hA
      have hi := forInductive_init (len := len) (a := a) (inits := inits) (body := body) hA
      simp only [carriedGo, NFProg.denote]
      exact bind_congr_inv (foldlM_congr_inv _ _ _ hb hs _ _ hi)
        (fun acc hacc => hk acc (foldlM_inv _ _ hs _ _ _ hi hacc))
  | _, _, A, len, a, .ifThenElse (rs := rs) cond thn els k, V, hlen, hA => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          (carriedGo (topApp rs A) (rs.length + len) a.rest k).denote fuel (hvAppend r V) =
            k.denote fuel (hvAppend r V) :=
        fun r => carriedGo_denote fuel _ _ a.rest k _ (length_app rs hlen)
          (envOK_topApp rs r hA)
      simp only [carriedGo, NFProg.denote, hk, carriedGo_denote fuel A len a.inner thn V hlen hA,
        carriedGo_denote fuel A len a.other els V hlen hA]
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k, V, hlen, hA => by
      have hb : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          (carriedGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
              (cs.length + len) a.inner body).denote fuel (hvAppend acc V) =
            body.denote fuel (hvAppend acc V) :=
        fun acc hP => carriedGo_denote fuel _ _ a.inner body _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA)
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          (carriedGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
              (cs.length + len) a.rest k).denote fuel (hvAppend acc V) =
            k.denote fuel (hvAppend acc V) :=
        fun acc hP => carriedGo_denote fuel _ _ a.rest k _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA)
      have hs := whileInductive_step fuel (a := a) (inits := inits) (body := body) hlen hA
      have hi := whileInductive_init (len := len) (a := a) (inits := inits) (body := body) hA
      simp only [carriedGo, NFProg.denote]
      exact bind_congr_inv (whileIter_congr_inv _ _ _ hb hs _ _ hi)
        (fun acc hacc => hk acc (whileIter_inv _ _ hs _ _ _ hi hacc))
  | _, _, A, len, a, .call (rs := rs) f args k, V, hlen, hA => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          (carriedGo (topApp rs A) (rs.length + len) a k).denote fuel (hvAppend r V) =
            k.denote fuel (hvAppend r V) :=
        fun r => carriedGo_denote fuel _ _ a k _ (length_app rs hlen) (envOK_topApp rs r hA)
      simp only [carriedGo, NFProg.denote, hk]

end Denote

/-- **The range stage with checked carried intervals**: the traversal under the annotation
    `a` from the full lane range of every input. -/
def loopRange {Γ : JCtxt} {ts : List JasminTy} (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) : NFProg jasminDialect Γ ts :=
  carriedGo (topEnv Γ) Γ.length a p

/-- **Denotation of the stage.** `loopRange a p` denotes the same function as `p` at every
    fuel, for every annotation `a`. -/
theorem loopRange_denote [CallDenote jasminDialect] {Γ : JCtxt} {ts : List JasminTy}
    (a : CarriedAnn) (p : NFProg jasminDialect Γ ts) (fuel : Nat) :
    (loopRange a p).denote fuel = p.denote fuel :=
  funext fun V => carriedGo_denote fuel _ _ a p V rfl (envOK_topEnv V)

/-- **At the empty annotation the stage is `rangeNF`.** -/
theorem loopRange_empty {Γ : JCtxt} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    loopRange .empty p = rangeNF p :=
  carriedGo_empty _ _ p

/-! ## 8. Leakage -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel LeakKind Expr.ctLeak Labels)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.Optimizer.Rewrite.ComGVN (opLeak_length)

/-- **Counted loops related two-run under an invariant.** The statement of
    `AegraphNF.forIterLeak_ctRel` with its hypotheses on the steps required only at the
    states that satisfy `P`, for steps `a₁`, `a₂` that keep `P`, from states that satisfy
    `P`; the final states of `a₁`, `a₂` satisfy `P`. -/
theorem forIterLeak_carried {cs : List JasminTy}
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (a₁ a₂ b₁ b₂ : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak))
    (hP₁ : ∀ i X r, P X → a₁ i X = some r → P r.1)
    (hP₂ : ∀ i X r, P X → a₂ i X = some r → P r.1)
    (hf₁ : ∀ i X, P X → (b₁ i X).map Prod.fst = (a₁ i X).map Prod.fst)
    (hf₂ : ∀ i X, P X → (b₂ i X).map Prod.fst = (a₂ i X).map Prod.fst)
    (hpf : ∀ i X Y (r r' : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)
      (x y : List CTLeak), P X → P Y →
      a₁ i X = some r → a₂ i Y = some r' → r.2 ++ x = r'.2 ++ y → r.2 = r'.2)
    (hrel : ∀ i X Y (r r' s s' : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak),
      P X → P Y → a₁ i X = some r → a₂ i Y = some r' → b₁ i X = some s → b₂ i Y = some s' →
      r.2 = r'.2 → s.2 = s'.2) :
    ∀ (l : List Nat) (X Y : Ctxt.Valuation (d := jasminDialect) cs)
      (r r' s s' : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)
      (x y : List CTLeak), P X → P Y →
      forIterLeak a₁ l X = some r → forIterLeak a₂ l Y = some r' →
      forIterLeak b₁ l X = some s → forIterLeak b₂ l Y = some s' →
      r.2 ++ x = r'.2 ++ y →
      r.2 = r'.2 ∧ s.2 = s'.2 ∧ s.1 = r.1 ∧ s'.1 = r'.1 ∧ P r.1 ∧ P r'.1
  | [], X, Y, r, r', s, s', x, y, hX, hY, h₁, h₂, h₃, h₄, _ => by
      simp only [forIterLeak, Option.some.injEq] at h₁ h₂ h₃ h₄
      subst h₁ h₂ h₃ h₄
      exact ⟨rfl, rfl, rfl, rfl, hX, hY⟩
  | i :: l, X, Y, r, r', s, s', x, y, hX, hY, h₁, h₂, h₃, h₄, he => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂ h₃ h₄
      obtain ⟨u₁, hu₁, q₁, hq₁, rfl⟩ := h₁
      obtain ⟨u₂, hu₂, q₂, hq₂, rfl⟩ := h₂
      obtain ⟨v₁, hv₁, w₁, hw₁, rfl⟩ := h₃
      obtain ⟨v₂, hv₂, w₂, hw₂, rfl⟩ := h₄
      have e₁ : v₁.1 = u₁.1 := by
        have := hf₁ i X hX
        rw [hv₁, hu₁] at this
        exact Option.some.inj this
      have e₂ : v₂.1 = u₂.1 := by
        have := hf₂ i Y hY
        rw [hv₂, hu₂] at this
        exact Option.some.inj this
      rw [e₁] at hw₁
      rw [e₂] at hw₂
      simp only [List.append_assoc] at he
      have hu := hpf i X Y u₁ u₂ _ _ hX hY hu₁ hu₂ he
      rw [hu] at he
      obtain ⟨hq, hw, hs₁, hs₂, hp₁, hp₂⟩ := forIterLeak_carried P a₁ a₂ b₁ b₂ hP₁ hP₂ hf₁
        hf₂ hpf hrel l _ _ q₁ q₂ w₁ w₂ x y (hP₁ i X u₁ hX hu₁) (hP₂ i Y u₂ hY hu₂) hq₁ hq₂
        hw₁ hw₂ (List.append_cancel_left he)
      refine ⟨?_, ?_, hs₁, hs₂, hp₁, hp₂⟩
      · show u₁.2 ++ q₁.2 = u₂.2 ++ q₂.2
        rw [hu, hq]
      · show v₁.2 ++ w₁.2 = v₂.2 ++ w₂.2
        rw [hrel i X Y u₁ u₂ v₁ v₂ hX hY hu₁ hu₂ hv₁ hv₂ hu, hw]

/-- **Exit-flag loops related two-run under an invariant.** The counterpart of
    `forIterLeak_carried` for the iterations `whileIterLeak` of an exit-flag loop. -/
theorem whileIterLeak_carried {cs : List JasminTy}
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (a₁ a₂ b₁ b₂ : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect)
        (HasBitType.bit (d := jasminDialect) :: cs) × List CTLeak))
    (hP₁ : ∀ X r, P X → a₁ X = some r → P r.1.tail)
    (hP₂ : ∀ X r, P X → a₂ X = some r → P r.1.tail)
    (hf₁ : ∀ X, P X → (b₁ X).map Prod.fst = (a₁ X).map Prod.fst)
    (hf₂ : ∀ X, P X → (b₂ X).map Prod.fst = (a₂ X).map Prod.fst)
    (hpf : ∀ X Y (r r' : Ctxt.Valuation (d := jasminDialect)
        (HasBitType.bit (d := jasminDialect) :: cs) × List CTLeak)
      (x y : List CTLeak), P X → P Y → a₁ X = some r → a₂ Y = some r' →
      r.2 ++ x = r'.2 ++ y → r.2 = r'.2)
    (hrel : ∀ X Y (r r' s s' : Ctxt.Valuation (d := jasminDialect)
        (HasBitType.bit (d := jasminDialect) :: cs) × List CTLeak),
      P X → P Y → a₁ X = some r → a₂ Y = some r' → b₁ X = some s → b₂ Y = some s' →
      r.2 = r'.2 → s.2 = s'.2) :
    ∀ (n : Nat) (X Y : Ctxt.Valuation (d := jasminDialect) cs)
      (r r' s s' : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)
      (x y : List CTLeak), P X → P Y →
      whileIterLeak a₁ n X = some r → whileIterLeak a₂ n Y = some r' →
      whileIterLeak b₁ n X = some s → whileIterLeak b₂ n Y = some s' →
      r.2 ++ x = r'.2 ++ y →
      r.2 = r'.2 ∧ s.2 = s'.2 ∧ s.1 = r.1 ∧ s'.1 = r'.1 ∧ P r.1 ∧ P r'.1
  | 0, _, _, _, _, _, _, _, _, _, _, h₁, _, _, _, _ => by simp [whileIterLeak] at h₁
  | n + 1, X, Y, r, r', s, s', x, y, hX, hY, h₁, h₂, h₃, h₄, he => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h₁ h₂ h₃ h₄
      obtain ⟨u₁, hu₁, h₁⟩ := h₁
      obtain ⟨u₂, hu₂, h₂⟩ := h₂
      obtain ⟨v₁, hv₁, h₃⟩ := h₃
      obtain ⟨v₂, hv₂, h₄⟩ := h₄
      have e₁ : v₁.1 = u₁.1 := by
        have := hf₁ X hX
        rw [hv₁, hu₁] at this
        exact Option.some.inj this
      have e₂ : v₂.1 = u₂.1 := by
        have := hf₂ Y hY
        rw [hv₂, hu₂] at this
        exact Option.some.inj this
      rw [e₁] at h₃
      rw [e₂] at h₄
      have hrv := hrel X Y u₁ u₂ v₁ v₂ hX hY hu₁ hu₂ hv₁ hv₂
      have hp₁ := hP₁ X u₁ hX hu₁
      have hp₂ := hP₂ Y u₂ hY hu₂
      by_cases c₁ : HasBoolBit.toBool (d := jasminDialect) u₁.1.head = true <;>
        by_cases c₂ : HasBoolBit.toBool (d := jasminDialect) u₂.1.head = true <;>
        simp only [c₁, c₂, ite_true, ite_false, Bool.false_eq_true, Option.map_eq_some_iff,
          Option.some.injEq] at h₁ h₂ h₃ h₄
      · obtain ⟨q₁, hq₁, rfl⟩ := h₁
        obtain ⟨q₂, hq₂, rfl⟩ := h₂
        obtain ⟨w₁, hw₁, rfl⟩ := h₃
        obtain ⟨w₂, hw₂, rfl⟩ := h₄
        simp only [List.append_assoc, List.cons_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hX hY hu₁ hu₂ he
        rw [hu] at he
        have he' := (List.cons.inj (List.append_cancel_left he)).2
        obtain ⟨hq, hw, hs₁, hs₂, hr₁, hr₂⟩ := whileIterLeak_carried P a₁ a₂ b₁ b₂ hP₁ hP₂
          hf₁ hf₂ hpf hrel n _ _ q₁ q₂ w₁ w₂ x y hp₁ hp₂ hq₁ hq₂ hw₁ hw₂ he'
        refine ⟨?_, ?_, hs₁, hs₂, hr₁, hr₂⟩
        · show u₁.2 ++ .branch true :: q₁.2 = u₂.2 ++ .branch true :: q₂.2
          rw [hu, hq]
        · show v₁.2 ++ .branch true :: w₁.2 = v₂.2 ++ .branch true :: w₂.2
          rw [hrv hu, hw]
      · obtain ⟨q₁, hq₁, rfl⟩ := h₁
        subst h₂
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hX hY hu₁ hu₂ he
        rw [hu] at he
        simp at he
      · obtain ⟨q₂, hq₂, rfl⟩ := h₂
        subst h₁
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hX hY hu₁ hu₂ he
        rw [hu] at he
        simp at he
      · subst h₁ h₂ h₃ h₄
        simp only [List.append_assoc, List.cons_append, List.nil_append] at he
        have hu := hpf X Y u₁ u₂ _ _ hX hY hu₁ hu₂ he
        refine ⟨?_, ?_, ?_, ?_, hp₁, hp₂⟩
        · show u₁.2 ++ [.branch false] = u₂.2 ++ [.branch false]
          rw [hu]
        · show v₁.2 ++ [.branch false] = v₂.2 ++ [.branch false]
          rw [hrv hu]
        · rfl
        · rfl

/-- The leakage run of the body of a counted loop keeps `CarriedOK` at the result of the
    checker. -/
theorem forInductive_leakStep (M : LeakModel jasminDialect) (fuel : Nat) {Γ : JCtxt}
    {cs : List JasminTy} {A : AEnv Γ} {len : Nat} {a : CarriedAnn}
    {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V) (i : Nat)
    (X : Ctxt.Valuation (d := jasminDialect) cs)
    (r : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak)
    (hP : CarriedOK (forInductive A len a inits body) cs a.ivs X)
    (hr : NFProg.leakRun M fuel body
      (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) = some r) :
    CarriedOK (forInductive A len a inits body) cs a.ivs r.1 := by
  have h := NFProg.leakRun_fst M fuel body
    (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V))
  rw [hr, Option.map_some] at h
  let _ : CallDenote jasminDialect := ⟨CallEnv.empty⟩
  exact forInductive_step fuel hlen hA X i r.1 hP h.symm

/-- The leakage run of the body of an exit-flag loop keeps `CarriedOK` at the result of
    the checker. -/
theorem whileInductive_leakStep (M : LeakModel jasminDialect) (fuel : Nat) {Γ : JCtxt}
    {cs : List JasminTy} {A : AEnv Γ} {len : Nat} {a : CarriedAnn}
    {inits : HVector (fun t => Ctxt.Var Γ t) cs}
    {body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs)}
    {V : Ctxt.Valuation Γ} (hlen : len = Γ.length) (hA : EnvOK A V)
    (X : Ctxt.Valuation (d := jasminDialect) cs)
    (r : Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs) ×
      List CTLeak)
    (hP : CarriedOK (whileInductive A len a inits body) cs a.ivs X)
    (hr : NFProg.leakRun M fuel body (hvAppend X V) = some r) :
    CarriedOK (whileInductive A len a inits body) cs a.ivs r.1.tail := by
  have h := NFProg.leakRun_fst M fuel body (hvAppend X V)
  rw [hr, Option.map_some] at h
  let _ : CallDenote jasminDialect := ⟨CallEnv.empty⟩
  exact whileInductive_step fuel hlen hA X r.1 hP h.symm

/-- The results of the leakage run of the traversal are those of the source. -/
theorem carriedGo_leakRun_fst (M : LeakModel jasminDialect) (fuel : Nat) {Γ : JCtxt}
    {ts : List JasminTy} (A : AEnv Γ) (len : Nat) (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ) (hlen : len = Γ.length)
    (hA : EnvOK A V) :
    (NFProg.leakRun M fuel (carriedGo A len a p) V).map Prod.fst =
      (NFProg.leakRun M fuel p V).map Prod.fst := by
  rw [NFProg.leakRun_fst, NFProg.leakRun_fst]
  let _ : CallDenote jasminDialect := ⟨CallEnv.empty⟩
  exact carriedGo_denote fuel A len a p V hlen hA

/-- A run of the traversal and a run of the source have the same results. -/
theorem carriedGo_fst_eq (M : LeakModel jasminDialect) (fuel : Nat) {Γ : JCtxt}
    {ts : List JasminTy} {A : AEnv Γ} {len : Nat} {a : CarriedAnn}
    {p : NFProg jasminDialect Γ ts} {V : Ctxt.Valuation Γ} (hlen : len = Γ.length)
    (hA : EnvOK A V) {r s : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak}
    (h : NFProg.leakRun M fuel p V = some r)
    (h' : NFProg.leakRun M fuel (carriedGo A len a p) V = some s) : s.1 = r.1 := by
  have := carriedGo_leakRun_fst M fuel A len a p V hlen hA
  rw [h, h'] at this
  exact Option.some.inj this

variable {L : LeakModel jasminDialect}

/-- **Leakage of the traversal, two-run.** Under an environment that holds of `V₁` and of
    `V₂` and a leakage model whose `regArith` operations are quiet, two runs of the source
    with equal events give, for any two runs of the output, equal events. -/
theorem carriedGo_ctRel (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat) :
    ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat) (a : CarriedAnn)
      (p : NFProg jasminDialect Γ ts) (V₁ V₂ : Ctxt.Valuation Γ), len = Γ.length →
      EnvOK A V₁ → EnvOK A V₂ →
      ∀ (r₁ r₂ s₁ s₂ : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak),
      NFProg.leakRun L fuel p V₁ = some r₁ → NFProg.leakRun L fuel p V₂ = some r₂ →
      NFProg.leakRun L fuel (carriedGo A len a p) V₁ = some s₁ →
      NFProg.leakRun L fuel (carriedGo A len a p) V₂ = some s₂ → r₁.2 = r₂.2 → s₁.2 = s₂.2
  | _, _, _, _, _, .ret vs, V₁, V₂, _, _, _, r₁, r₂, s₁, s₂, _, _, h₃, h₄, _ => by
      simp only [carriedGo, NFProg.leakRun, Option.some.injEq] at h₃ h₄
      subst h₃ h₄
      rfl
  | _, _, A, len, a, .var e k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂, s₁, s₂, h₁, h₂, h₃, h₄,
      he => by
      simp only [NFProg.leakRun] at h₁ h₂
      obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨hE, hB⟩ := List.append_inj he (opLeak_length L e.op _ _)
      simp only [carriedGo, NFProg.leakRun] at h₃ h₄
      rw [rangeExpr_denote hA₁ hlen e] at h₃
      rw [rangeExpr_denote hA₂ hlen e] at h₄
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      have hE2 : Expr.ctLeak L (rangeExpr A len e) V₁ =
          Expr.ctLeak L (rangeExpr A len e) V₂ := by
        rcases rangeExpr_leak hq A len e with h' | h'
        · rw [h']
          exact hE
        · exact h' _ _
      show Expr.ctLeak L (rangeExpr A len e) V₁ ++ t₁.2 =
        Expr.ctLeak L (rangeExpr A len e) V₂ ++ t₂.2
      rw [hE2]
      congr 1
      exact carriedGo_ctRel hq fuel _ (len + 1) a k _ _ (by simp [hlen])
        (hA₁.cons (stageAbs_sound hA₁ hlen e)) (hA₂.cons (stageAbs_sound hA₂ hlen e))
        u₁ u₂ t₁ t₂ hu₁ hu₂ ht₁ ht₂ hB
  | Γ, _, A, len, a, .forLoop (cs := cs) count inits body k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [carriedGo, NFProg.leakRun] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hn, he'⟩ := List.cons.inj he
      injection hn with hn
      rw [← hn] at hi₂ hj₂
      have hb : ∀ (V : Ctxt.Valuation Γ) (X : Ctxt.Valuation (d := jasminDialect) cs)
          (i : Nat), EnvOK A V → CarriedOK (forInductive A len a inits body) cs a.ivs X →
          EnvOK
            (carriedEnv (forInductive A len a inits body) cs a.ivs
              (topCons (HasWord64.word (d := jasminDialect)) A))
            (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun V X i h hX => envOK_carriedEnv cs a.ivs X hX (envOK_topCons h _)
      have hlb := length_body cs (HasWord64.word (d := jasminDialect)) hlen
      obtain ⟨hi, hj, hji₁, hji₂, hp₁, hp₂⟩ := forIterLeak_carried
        (CarriedOK (forInductive A len a inits body) cs a.ivs)
        (fun i X => NFProg.leakRun L fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₁)))
        (fun i X => NFProg.leakRun L fuel body
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₂)))
        (fun i X => NFProg.leakRun L fuel
          (carriedGo
            (carriedEnv (forInductive A len a inits body) cs a.ivs
              (topCons (HasWord64.word (d := jasminDialect)) A))
            (cs.length + (len + 1)) a.inner body)
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₁)))
        (fun i X => NFProg.leakRun L fuel
          (carriedGo
            (carriedEnv (forInductive A len a inits body) cs a.ivs
              (topCons (HasWord64.word (d := jasminDialect)) A))
            (cs.length + (len + 1)) a.inner body)
          (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V₂)))
        (fun i X r hX hr => forInductive_leakStep L fuel hlen hA₁ i X r hX hr)
        (fun i X r hX hr => forInductive_leakStep L fuel hlen hA₂ i X r hX hr)
        (fun i X hX => carriedGo_leakRun_fst L fuel _ _ _ body _ hlb (hb V₁ X i hA₁ hX))
        (fun i X hX => carriedGo_leakRun_fst L fuel _ _ _ body _ hlb (hb V₂ X i hA₂ hX))
        (fun i X Y r r' x y _ _ h h' hxy =>
          NFProg.leakRun_prefix L fuel body _ _ r r' x y h h' hxy)
        (fun i X Y r r' s s' hX hY h h' g g' hr =>
          carriedGo_ctRel hq fuel _ _ a.inner body _ _ hlb (hb V₁ X i hA₁ hX)
            (hb V₂ Y i hA₂ hY) r r' s s' h h' g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 (forInductive_init hA₁) (forInductive_init hA₂)
        hi₁ hi₂ hj₁ hj₂ he'
      rw [hi] at he'
      have hqq := List.append_cancel_left he'
      have hk := carriedGo_ctRel hq fuel _ _ a.rest k _ _ (length_app cs hlen)
        (envOK_carriedEnv cs a.ivs j₁.1 (by rw [hji₁]; exact hp₁) hA₁)
        (envOK_carriedEnv cs a.ivs j₂.1 (by rw [hji₂]; exact hp₂) hA₂) q₁ q₂ t₁ t₂
        (by rw [hji₁]; exact hq₁) (by rw [hji₂]; exact hq₂) ht₁ ht₂ hqq
      show _ :: (j₁.2 ++ t₁.2) = _ :: (j₂.2 ++ t₂.2)
      rw [hj, hk, hn]
  | _, _, A, len, a, .ifThenElse (rs := rs) cond thn els k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [carriedGo, NFProg.leakRun] at h₃ h₄
      obtain ⟨a₁, ha₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨a₂, ha₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨b₁, hb₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨b₂, hb₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      obtain ⟨hc, he'⟩ := List.cons.inj he
      injection hc with hc
      rw [← hc] at ha₂ hb₂
      have harm : a₁.2 = a₂.2 ∧ b₁.2 = b₂.2 ∧ b₁.1 = a₁.1 ∧ b₂.1 = a₂.1 := by
        cases hcb : HasBoolBit.toBool (d := jasminDialect) (cond.lookup V₁) <;>
          simp only [hcb, ite_true, ite_false, Bool.false_eq_true] at ha₁ ha₂ hb₁ hb₂
        · have ha := NFProg.leakRun_prefix L fuel els _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, carriedGo_ctRel hq fuel A len a.other els V₁ V₂ hlen hA₁ hA₂ a₁ a₂ b₁
            b₂ ha₁ ha₂ hb₁ hb₂ ha, carriedGo_fst_eq L fuel hlen hA₁ ha₁ hb₁,
            carriedGo_fst_eq L fuel hlen hA₂ ha₂ hb₂⟩
        · have ha := NFProg.leakRun_prefix L fuel thn _ _ a₁ a₂ q₁.2 q₂.2 ha₁ ha₂ he'
          exact ⟨ha, carriedGo_ctRel hq fuel A len a.inner thn V₁ V₂ hlen hA₁ hA₂ a₁ a₂ b₁
            b₂ ha₁ ha₂ hb₁ hb₂ ha, carriedGo_fst_eq L fuel hlen hA₁ ha₁ hb₁,
            carriedGo_fst_eq L fuel hlen hA₂ ha₂ hb₂⟩
      obtain ⟨ha, hb, hba₁, hba₂⟩ := harm
      rw [ha] at he'
      have hqq := List.append_cancel_left he'
      have hk := carriedGo_ctRel hq fuel _ _ a.rest k _ _ (length_app rs hlen)
        (envOK_topApp rs b₁.1 hA₁) (envOK_topApp rs b₂.1 hA₂) q₁ q₂ t₁ t₂
        (by rw [hba₁]; exact hq₁) (by rw [hba₂]; exact hq₂) ht₁ ht₂ hqq
      show _ :: (b₁.2 ++ t₁.2) = _ :: (b₂.2 ++ t₂.2)
      rw [hb, hk, hc]
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k, V₁, V₂, hlen, hA₁, hA₂, r₁, r₂,
      s₁, s₂, h₁, h₂, h₃, h₄, he => by
      simp only [NFProg.leakRun] at h₁ h₂
      simp only [carriedGo, NFProg.leakRun] at h₃ h₄
      obtain ⟨i₁, hi₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨i₂, hi₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨j₁, hj₁, h₃⟩ := Option.bind_eq_some_iff.mp h₃
      obtain ⟨t₁, ht₁, rfl⟩ := Option.map_eq_some_iff.mp h₃
      obtain ⟨j₂, hj₂, h₄⟩ := Option.bind_eq_some_iff.mp h₄
      obtain ⟨t₂, ht₂, rfl⟩ := Option.map_eq_some_iff.mp h₄
      have hla := length_app cs hlen
      obtain ⟨hi, hj, hji₁, hji₂, hp₁, hp₂⟩ := whileIterLeak_carried
        (CarriedOK (whileInductive A len a inits body) cs a.ivs)
        (fun X => NFProg.leakRun L fuel body (hvAppend X V₁))
        (fun X => NFProg.leakRun L fuel body (hvAppend X V₂))
        (fun X => NFProg.leakRun L fuel
          (carriedGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
            (cs.length + len) a.inner body) (hvAppend X V₁))
        (fun X => NFProg.leakRun L fuel
          (carriedGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
            (cs.length + len) a.inner body) (hvAppend X V₂))
        (fun X r hX hr => whileInductive_leakStep L fuel hlen hA₁ X r hX hr)
        (fun X r hX hr => whileInductive_leakStep L fuel hlen hA₂ X r hX hr)
        (fun X hX => carriedGo_leakRun_fst L fuel _ _ _ body _ hla
          (envOK_carriedEnv cs a.ivs X hX hA₁))
        (fun X hX => carriedGo_leakRun_fst L fuel _ _ _ body _ hla
          (envOK_carriedEnv cs a.ivs X hX hA₂))
        (fun X Y r r' x y _ _ h h' hxy =>
          NFProg.leakRun_prefix L fuel body _ _ r r' x y h h' hxy)
        (fun X Y r r' s s' hX hY h h' g g' hr =>
          carriedGo_ctRel hq fuel _ _ a.inner body _ _ hla
            (envOK_carriedEnv cs a.ivs X hX hA₁) (envOK_carriedEnv cs a.ivs Y hY hA₂)
            r r' s s' h h' g g' hr)
        _ _ _ i₁ i₂ j₁ j₂ q₁.2 q₂.2 (whileInductive_init hA₁) (whileInductive_init hA₂)
        hi₁ hi₂ hj₁ hj₂ he
      rw [hi] at he
      have hqq := List.append_cancel_left he
      have hk := carriedGo_ctRel hq fuel _ _ a.rest k _ _ hla
        (envOK_carriedEnv cs a.ivs j₁.1 (by rw [hji₁]; exact hp₁) hA₁)
        (envOK_carriedEnv cs a.ivs j₂.1 (by rw [hji₂]; exact hp₂) hA₂) q₁ q₂ t₁ t₂
        (by rw [hji₁]; exact hq₁) (by rw [hji₂]; exact hq₂) ht₁ ht₂ hqq
      show j₁.2 ++ t₁.2 = j₂.2 ++ t₂.2
      rw [hj, hk]
  | _, _, _, _, _, .call .., _, _, _, _, _, _, _, _, _, h₁, _, _, _, _ => by
      simp [NFProg.leakRun] at h₁

/-- **Leakage of the stage, two-run.** Under a leakage model whose `regArith` operations are
    quiet, two runs of `p` that succeed with equal events give two runs of `loopRange a p`
    that succeed, with the same results and equal events. -/
theorem loopRange_ctRel (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : JCtxt} {ts : List JasminTy} (a : CarriedAnn) (p : NFProg jasminDialect Γ ts)
    (V₁ V₂ : Ctxt.Valuation Γ) (r₁ r₂ : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak)
    (h₁ : NFProg.leakRun L fuel p V₁ = some r₁) (h₂ : NFProg.leakRun L fuel p V₂ = some r₂)
    (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRun L fuel (loopRange a p) V₁ = some s₁ ∧
      NFProg.leakRun L fuel (loopRange a p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧ s₂.1 = r₂.1 ∧
      s₁.2 = s₂.2 := by
  have f₁ := carriedGo_leakRun_fst L fuel (topEnv Γ) Γ.length a p V₁ rfl (envOK_topEnv V₁)
  have f₂ := carriedGo_leakRun_fst L fuel (topEnv Γ) Γ.length a p V₂ rfl (envOK_topEnv V₂)
  rw [h₁, Option.map_some] at f₁
  rw [h₂, Option.map_some] at f₂
  obtain ⟨s₁, hs₁, e₁⟩ := Option.map_eq_some_iff.mp f₁
  obtain ⟨s₂, hs₂, e₂⟩ := Option.map_eq_some_iff.mp f₂
  exact ⟨s₁, s₂, hs₁, hs₂, e₁, e₂,
    carriedGo_ctRel hq fuel _ _ a p V₁ V₂ rfl (envOK_topEnv V₁) (envOK_topEnv V₂) r₁ r₂ s₁ s₂
      h₁ h₂ hs₁ hs₂ he⟩

/-- **Constant time of the stage.** Under a leakage model whose `regArith` operations are
    quiet, if `p` is constant time for the labels `Lb`, so is `loopRange a p`. -/
theorem loopRange_nfCT (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : JCtxt} {ts : List JasminTy} (Lb : Labels Γ) (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) (hct : NFCT L Lb fuel p) :
    NFCT L Lb fuel (loopRange a p) := by
  intro V₁ V₂ hV
  have f₁ := carriedGo_leakRun_fst L fuel (topEnv Γ) Γ.length a p V₁ rfl (envOK_topEnv V₁)
  have f₂ := carriedGo_leakRun_fst L fuel (topEnv Γ) Γ.length a p V₂ rfl (envOK_topEnv V₂)
  have hp := hct V₁ V₂ hV
  change (NFProg.leakRun L fuel (carriedGo _ _ a p) V₁).map Prod.snd =
    (NFProg.leakRun L fuel (carriedGo _ _ a p) V₂).map Prod.snd
  rcases hr₁ : NFProg.leakRun L fuel p V₁ with _ | r₁ <;>
    rcases hr₂ : NFProg.leakRun L fuel p V₂ with _ | r₂ <;>
    rw [hr₁] at f₁ hp <;> rw [hr₂] at f₂ hp
  · rw [Option.map_eq_none_iff.mp f₁, Option.map_eq_none_iff.mp f₂]
  · cases hp
  · cases hp
  · obtain ⟨s₁, hs₁, _⟩ := Option.map_eq_some_iff.mp f₁
    obtain ⟨s₂, hs₂, _⟩ := Option.map_eq_some_iff.mp f₂
    rw [hs₁, hs₂, Option.map_some, Option.map_some,
      carriedGo_ctRel hq fuel _ _ a p V₁ V₂ rfl (envOK_topEnv V₁) (envOK_topEnv V₂) r₁ r₂ s₁
        s₂ hr₁ hr₂ hs₁ hs₂ (Option.some.inj hp)]

end Leak

/-! ## 9. The stage keeps a program branch-free -/

/-- **The traversal keeps a program branch-free.** -/
theorem ifFree_carriedGo : ∀ {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (len : Nat)
    (a : CarriedAnn) (p : NFProg jasminDialect Γ ts),
    NFProg.ifFree p = true → NFProg.ifFree (carriedGo A len a p) = true
  | _, _, _, _, _, .ret _, _ => rfl
  | _, _, A, len, a, .var e k, hp => by
      have hk : NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using hp
      simpa only [carriedGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk,
        Bool.true_and] using ifFree_carriedGo _ _ a k hk
  | _, _, A, len, a, .forLoop _ _ body k, hp => by
      have hbk : NFProg.ifFree body = true ∧ NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true] using hp
      simp only [carriedGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true]
      exact ⟨ifFree_carriedGo _ _ _ body hbk.1, ifFree_carriedGo _ _ _ k hbk.2⟩
  | _, _, _, _, _, .ifThenElse .., hp => by
      simp [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] at hp
  | _, _, A, len, a, .whileLoop _ body k, hp => by
      have hbk : NFProg.ifFree body = true ∧ NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true] using hp
      simp only [carriedGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true]
      exact ⟨ifFree_carriedGo _ _ _ body hbk.1, ifFree_carriedGo _ _ _ k hbk.2⟩
  | _, _, A, len, a, .call _ _ k, hp => by
      have hk : NFProg.ifFree k = true := by
        simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] using hp
      simpa only [carriedGo, NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk] using
        ifFree_carriedGo _ _ a k hk

/-- **The stage keeps a program branch-free.** -/
theorem ifFree_loopRange {Γ : JCtxt} {ts : List JasminTy} (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) (hp : NFProg.ifFree p = true) :
    NFProg.ifFree (loopRange a p) = true :=
  ifFree_carriedGo _ _ a p hp

/-! ## 10. The chain step of the stage -/

open NFProgPasses (nfSem)

/-- The stage `loopRange` as a chain step, at the annotation `syn p` computed from the
    input `p`. The function `syn` is not trusted: the stage checks each proposal. -/
def carriedStep (Γ : JCtxt) (ts : List JasminTy)
    (syn : NFProg jasminDialect Γ ts → CarriedAnn) :
    PassChain.Step (NFProg jasminDialect Γ ts) (NFProg jasminDialect Γ ts) :=
  ⟨"range-carried", fun p => some (loopRange (syn p) p)⟩

/-- The certificate of the stage: the rewritten program has the denotation of its input,
    from `loopRange_denote`, for every `syn`. -/
def carriedCert [CallDenote jasminDialect] (fuel : Nat) (Γ : JCtxt) (ts : List JasminTy)
    (syn : NFProg jasminDialect Γ ts → CarriedAnn) :
    PassChain.StepCert (carriedStep Γ ts syn).run (nfSem fuel jasminDialect Γ ts)
      (nfSem fuel jasminDialect Γ ts) :=
  PassChain.StepCert.ofDenoteEq _ fun p q hf => by
    cases hf
    exact loopRange_denote (syn p) p fuel

/-! ## 11. A counted loop with a bounded carried word

`lazyAddLoop` carries one 64-bit word `x` from `0` through `n` trips. Each trip masks `x`
to 31 bits, adds the constant `5`, and subtracts the BabyBear prime `p = 2013265921`
conditionally in mask form: `d = t - p`, the sign word of `d`, its negation, the mask with
`p`, and the conditional add. The continuation masks the final word to 31 bits. The program
has three `and` operations: the two 31-bit masks and the mask with `p`.

With `x` at the full lane range neither 31-bit mask is an identity, and `rangeNF` keeps the
three operations. The interval `[0, p - 1]` is inductive for the loop: the start value `0`
lies in it, and from `x` in it the analysis gives `t` in `[5, p + 4]`, `d` in `[5 - p, 4]`
and the conditional add in `[0, p - 1]`. Under it both 31-bit masks are identities and
become copies; the mask with `p` stays. -/

/-- The number of `and` bindings of a structured program. -/
def andCount : {Γ : JCtxt} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Nat
  | _, _, .ret _ => 0
  | _, _, .var e k =>
      (match (e.op : JasminOp) with
        | .regArith .and _ => 1
        | _ => 0) + andCount k
  | _, _, .forLoop _ _ body k => andCount body + andCount k
  | _, _, .ifThenElse _ thn els k => andCount thn + andCount els + andCount k
  | _, _, .whileLoop _ body k => andCount body + andCount k
  | _, _, .call _ _ k => andCount k

/-- The counted loop of this section over the trip count `n`. -/
def lazyAddLoop : NFProg jasminDialect [JasminTy.reg 64] [JasminTy.reg 64] :=
  let body : NFProg jasminDialect
      [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64]
      [JasminTy.reg 64] :=
    .var ⟨JasminOp.regConst 64 2147483647, rfl, .nil⟩
    (.var ⟨JasminOp.regArith .and 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
    (.var ⟨JasminOp.regConst 64 5, rfl, .nil⟩
    (.var ⟨JasminOp.regArith .add 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
    (.var ⟨JasminOp.regConst 64 2013265921, rfl, .nil⟩
    (.var ⟨JasminOp.regConst 64 63, rfl, .nil⟩
    (.var ⟨JasminOp.regConst 64 0, rfl, .nil⟩
    (.var ⟨JasminOp.regArith .sub 64, rfl,
      .cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)⟩
    (.var ⟨JasminOp.regArith .shr 64, rfl,
      .cons .here (.cons (.there (.there .here)) .nil)⟩
    (.var ⟨JasminOp.regArith .sub 64, rfl,
      .cons (.there (.there .here)) (.cons .here .nil)⟩
    (.var ⟨JasminOp.regArith .and 64, rfl,
      .cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)⟩
    (.var ⟨JasminOp.regArith .add 64, rfl,
      .cons (.there (.there (.there .here))) (.cons .here .nil)⟩
    (.ret (.cons .here .nil)))))))))))))
  let k : NFProg jasminDialect [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64]
      [JasminTy.reg 64] :=
    .var ⟨JasminOp.regConst 64 2147483647, rfl, .nil⟩
    (.var ⟨JasminOp.regArith .and 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
    (.ret (.cons .here .nil)))
  .var ⟨JasminOp.regConst 64 0, rfl, .nil⟩
    (NFProg.forLoop (d := jasminDialect) (cs := [JasminTy.reg 64])
      (Γ := [JasminTy.reg 64, JasminTy.reg 64])
      (.there .here) (.cons .here .nil) body k)

/-- The annotation of `lazyAddLoop`: the interval `[0, p - 1]` for the carried word. -/
def lazyAddAnn : CarriedAnn := .loop [(0, 2013265920)] .empty .empty

/- Under `lazyAddAnn` the stage keeps one `and` operation, the mask with `p`. The budget
   covers the start of the evaluator at the first check of the file. -/
set_option kat.ms 3000 in
#kat andCount (loopRange lazyAddAnn lazyAddLoop) == 1

/- `rangeNF` keeps the three `and` operations of `lazyAddLoop`. -/
#kat andCount (rangeNF lazyAddLoop) == 3

end CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop
