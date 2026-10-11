/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import HaxLean.Phase.InlineLocalClosures

/-!
# Inlining of the functions of a crate in `ImpExpr`

`inlineCrate fs n e` replaces each call of a function of the crate `fs` in `e` by the body
of the function, to the call depth `n`: in the body at the remaining depth `k` each variable `x`
is replaced by the level name `lvlName k x`, and the calls in it are inlined at the
depth `k`. A call `g args` of the function `c` at the depth `k + 1` becomes the call block
`callBlock k`: the arguments are evaluated into a tuple bound to the name `tmpName k`, the
level names of the parameters of `c` are bound to the components of the tuple, and the
inlined body follows. The level names and the tuple names start with the character `'\x00'`,
which no name of the source starts with (`okName`), so the variables of a body inlined at
the level `k` are distinct from the variables of the source and of every other level.

The check `inlOk fs n e` accepts a term of the fragment of the front (literals, variables,
`unitVal`, bindings, assignments, calls, tuples, conditionals, sequences, ascriptions and the
counted loops `forFold`, `forFoldRev`) whose names are names of the source, each call of a
function of `fs` at a positive depth with as many arguments as the function has parameters
and a body accepted at the depth below, and no call of a function of `fs` at the depth `0`.

## Main definitions

* `lvlName`, `tmpName`, `okName`, `IsLow` — the level names, the tuple names, the names of
  the source and the names of the levels below a depth.
* `xf` — the renaming of the variables of a term by `ρ` with the calls replaced by a site
  function.
* `bindParams`, `callBlock`, `inl`, `inlineCrate` — the call block and the inliner.
* `okX`, `inlOk` — the fragment check and the check of the inliner.
* `InlRel` — the relations between the environment of the inlined term and the environment
  of the source term that the refinement keeps.

## Main results

* `inl_ref` — under `InlRel`, the inlined term at the builtins `bi` and the fuel `F + D`
  refines the source term at the builtins with the crate `crateBi fs bi fuelC n` and the
  fuel `F`, for `D ≥ n * fuelC`.
* `inlineCrate_denote'` — every run of the source term at `crateBi fs bi fuelC n` that does
  not end in an error is a run of `inlineCrate fs n e` at `bi`, with the same outcome and a
  final environment that holds every binding of a name of the source.
* `inlRel_srcAgree` — agreement on the bindings of the names of the source is a relation
  `InlRel n id`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpInline

open _root_.Hax (ImpExpr ImpLit Value Env Builtins Outcome denote' denoteArgs' denoteApp'
  denoteForLoop' denoteForLoopRev')
open _root_.Hax.InlineLocalClosures (RefR RefE IsErr run_bind)
open scoped _root_.Hax.InlineLocalClosures
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateBi paramsEnv crateBi_of_find_none)

/-! ## Names -/

/-- The name of the variable `x` of a body inlined at the level `k`. -/
def lvlName (k : Nat) (x : String) : String :=
  String.ofList ('\x00' :: (List.replicate k '\x01' ++ '\x02' :: x.toList))

/-- The name of the tuple of the arguments of a call inlined at the level `k`. -/
def tmpName (k : Nat) : String :=
  String.ofList ('\x00' :: (List.replicate k '\x01' ++ ['\x03']))

/-- A name of the source: a name whose first character is not `'\x00'`. -/
def okName (x : String) : Bool := x.toList.head? != some '\x00'

/-- The names of the levels below `n`: the level names and the tuple names at a level
    `k < n`. -/
def IsLow (n : Nat) (y : String) : Prop :=
  ∃ k, k < n ∧ ((∃ x, y = lvlName k x) ∨ y = tmpName k)

theorem replicate_append_cons_inj {c d d' : Char} (hd : d ≠ c) (hd' : d' ≠ c) :
    ∀ (k j : Nat) (xs ys : List Char),
      List.replicate k c ++ d :: xs = List.replicate j c ++ d' :: ys →
        k = j ∧ d = d' ∧ xs = ys
  | 0, 0, xs, ys, h => by simpa using h
  | 0, j + 1, xs, ys, h => by simp [List.replicate_succ] at h; exact absurd h.1 hd
  | k + 1, 0, xs, ys, h => by simp [List.replicate_succ] at h; exact absurd h.1.symm hd'
  | k + 1, j + 1, xs, ys, h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2, h3⟩ := replicate_append_cons_inj hd hd' k j xs ys h
      exact ⟨by rw [h1], h2, h3⟩

theorem lvlName_inj {k j : Nat} {x z : String} (h : lvlName k x = lvlName j z) :
    k = j ∧ x = z := by
  have h' := congrArg String.toList h
  simp only [lvlName, String.toList_ofList, List.cons.injEq, true_and] at h'
  obtain ⟨h1, -, h3⟩ := replicate_append_cons_inj (by decide) (by decide) k j _ _ h'
  exact ⟨h1, String.toList_inj.mp h3⟩

theorem lvlName_ne_tmpName (k j : Nat) (x : String) : lvlName k x ≠ tmpName j := by
  intro h
  have h' := congrArg String.toList h
  simp only [lvlName, tmpName, String.toList_ofList, List.cons.injEq, true_and] at h'
  obtain ⟨-, h2, -⟩ := replicate_append_cons_inj (by decide) (by decide) k j _ _ h'
  exact absurd h2 (by decide)

theorem tmpName_inj {k j : Nat} (h : tmpName k = tmpName j) : k = j := by
  have h' := congrArg String.toList h
  simp only [tmpName, String.toList_ofList, List.cons.injEq, true_and] at h'
  exact (replicate_append_cons_inj (by decide) (by decide) k j _ _ h').1

theorem okName_ne_lvlName {x : String} (hx : okName x = true) (k : Nat) (z : String) :
    x ≠ lvlName k z := by
  rintro rfl
  simp [okName, lvlName] at hx

theorem okName_ne_tmpName {x : String} (hx : okName x = true) (k : Nat) : x ≠ tmpName k := by
  rintro rfl
  simp [okName, tmpName] at hx

theorem not_isLow_of_okName {x : String} (hx : okName x = true) (n : Nat) : ¬ IsLow n x := by
  rintro ⟨k, -, ⟨z, hz⟩ | hz⟩
  · exact okName_ne_lvlName hx k z hz
  · exact okName_ne_tmpName hx k hz

theorem not_isLow_lvlName (n : Nat) (x : String) : ¬ IsLow n (lvlName n x) := by
  rintro ⟨k, hk, ⟨z, hz⟩ | hz⟩
  · exact absurd (lvlName_inj hz).1 (by omega)
  · exact lvlName_ne_tmpName n k x hz

theorem isLow_lvlName {n k : Nat} (h : k < n) (x : String) : IsLow n (lvlName k x) :=
  ⟨k, h, Or.inl ⟨x, rfl⟩⟩

theorem isLow_tmpName {n k : Nat} (h : k < n) : IsLow n (tmpName k) :=
  ⟨k, h, Or.inr rfl⟩

theorem IsLow.mono {n m : Nat} (h : n ≤ m) {y : String} (hy : IsLow n y) : IsLow m y := by
  obtain ⟨k, hk, hy⟩ := hy
  exact ⟨k, by omega, hy⟩

/-! ## The inliner -/

/-- The term `e` with every variable and binder `x` replaced by `ρ x`, and every call `g args`
    replaced by `site g args'` (`args'` the transformed arguments) when it is defined. The
    constructors outside the fragment of the front are kept. -/
def xf (ρ : String → String) (site : String → List ImpExpr → Option ImpExpr) :
    ImpExpr → ImpExpr
  | .var x => .var (ρ x)
  | .letBind x v b => .letBind (ρ x) (xf ρ site v) (xf ρ site b)
  | .assign x r => .assign (ρ x) (xf ρ site r)
  | .app g args => (site g (xfList ρ site args)).getD (.app g (xfList ρ site args))
  | .tuple es => .tuple (xfList ρ site es)
  | .ifThenElse c t e => .ifThenElse (xf ρ site c) (xf ρ site t) (xf ρ site e)
  | .seq a b => .seq (xf ρ site a) (xf ρ site b)
  | .typeAscription e s => .typeAscription (xf ρ site e) s
  | .forFold i lo hi b => .forFold (ρ i) (xf ρ site lo) (xf ρ site hi) (xf ρ site b)
  | .forFoldRev i lo hi b => .forFoldRev (ρ i) (xf ρ site lo) (xf ρ site hi) (xf ρ site b)
  | e => e
where
  /-- `xf` on every expression of a list. -/
  xfList (ρ : String → String) (site : String → List ImpExpr → Option ImpExpr) :
      List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => xf ρ site e :: xfList ρ site es

@[simp] theorem xf.xfList_eq (ρ : String → String)
    (site : String → List ImpExpr → Option ImpExpr) (es : List ImpExpr) :
    xf.xfList ρ site es = es.map (xf ρ site) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [xf.xfList, ih]

/-- The bindings of the parameters `ps` of a body inlined at the level `n`, from the
    position `i` of the tuple `tmpName n`, followed by `b`. The first parameter is bound
    last, so that among parameters of one name the first one is read. -/
def bindParams (n : Nat) : Nat → List String → ImpExpr → ImpExpr
  | _, [], b => b
  | i, p :: ps, b => bindParams n (i + 1) ps (.letBind (lvlName n p) (.proj (.var (tmpName n)) i) b)

/-- **The call block** of a call inlined at the level `n`: the arguments `args` evaluated
    into a tuple bound to `tmpName n`, the level names of the parameters `ps` bound to its
    components, followed by the body. -/
def callBlock (n : Nat) (ps : List String) (args : List ImpExpr) (body : ImpExpr) : ImpExpr :=
  .letBind (tmpName n) (.tuple args) (bindParams n 0 ps body)

/-- **The inliner** at the depth `n` with the renaming `ρ`: at the depth `n + 1` a call of a
    function `c` of `fs` is the call block at the level `n` of the body of `c`, its variables
    mapped by `lvlName n` and its calls inlined at the depth `n`; at the depth `0` no call is inlined. -/
def inl (fs : List CrateFn) : Nat → (String → String) → ImpExpr → ImpExpr
  | 0, ρ => xf ρ (fun _ _ => none)
  | n + 1, ρ => xf ρ (fun g args => (fs.find? (·.name == g)).map fun c =>
      callBlock n (c.params.map (·.1)) args (inl fs n (lvlName n) c.body))

/-- **The inlining of the functions `fs` of a crate in `e` to the depth `n`.** -/
def inlineCrate (fs : List CrateFn) (n : Nat) (e : ImpExpr) : ImpExpr := inl fs n id e

/-! ## The check -/

/-- The fragment check with the check `call` at every call: the constructors of the
    fragment of the front, every name a name of the source. -/
def okX (call : String → List ImpExpr → Bool) : ImpExpr → Bool
  | .lit _ => true
  | .unitVal => true
  | .var x => okName x
  | .letBind x v b => okName x && okX call v && okX call b
  | .assign x r => okName x && okX call r
  | .app g args => okXList call args && call g args
  | .tuple es => okXList call es
  | .ifThenElse c t e => okX call c && okX call t && okX call e
  | .seq a b => okX call a && okX call b
  | .typeAscription e _ => okX call e
  | .forFold i lo hi b => okName i && okX call lo && okX call hi && okX call b
  | .forFoldRev i lo hi b => okName i && okX call lo && okX call hi && okX call b
  | _ => false
where
  /-- `okX` on every expression of a list. -/
  okXList (call : String → List ImpExpr → Bool) : List ImpExpr → Bool
    | [] => true
    | e :: es => okX call e && okXList call es

theorem okX.okXList_eq (call : String → List ImpExpr → Bool) (es : List ImpExpr) :
    okX.okXList call es = es.all (okX call) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [okX.okXList, ih]

/-- **The check of the inliner** at the depth `n`: the fragment check, with every call of a
    function of `fs` at a positive depth, with as many arguments as parameters and a body
    accepted at the depth below, and no call of a function of `fs` at the depth `0`. -/
def inlOk (fs : List CrateFn) : Nat → ImpExpr → Bool
  | 0 => okX fun g _ => (fs.find? (·.name == g)).isNone
  | n + 1 => okX fun g args =>
      match fs.find? (·.name == g) with
      | none => true
      | some c => args.length == c.params.length && inlOk fs n c.body

/-! ## Relational steps -/

section Steps

variable {R : Env → Env → Prop} {bi₁ bi₂ : Builtins}

theorem refR_modify2 {α : Type} {P Q : Env → Env → Prop} {bad : α → Prop} {n₁ n₂ : String}
    {w : Value} (hn : ∀ e₁ e₂, P e₁ e₂ → Q (e₁.extend n₁ w) (e₂.extend n₂ w))
    {S : Env → Env → Prop} {k₁ k₂ : PUnit → StateM Env α} (h : ∀ u, RefR Q S bad (k₁ u) (k₂ u)) :
    RefR P S bad (_root_.modify (fun x => x.extend n₁ w) >>= k₁)
      (_root_.modify (fun x => x.extend n₂ w) >>= k₂) := by
  intro e₁ e₂ hP o s hr hb
  exact h _ _ _ (hn e₁ e₂ hP) o s hr hb

theorem args_off (g : ImpExpr → ImpExpr) (args : List ImpExpr) (F₁ F₂ : Nat)
    (ih : ∀ a, a ∈ args → RefE R (denote' bi₁ F₁ (g a)) (denote' bi₂ F₂ a)) :
    RefR R R (fun o => o = none) (denoteArgs' bi₁ F₁ (args.map g))
      (denoteArgs' bi₂ F₂ args) := by
  induction args with
  | nil => simp only [List.map_nil, denoteArgs']; exact RefR.pure _
  | cons a as iha =>
    simp only [List.map_cons, denoteArgs']
    refine RefR.bind (badα := IsErr) (ih a List.mem_cons_self) (fun o ho => ?_)
      (fun o ho s => by obtain ⟨m, hm⟩ := ho; subst hm; rfl)
    split
    · exact RefR.pure _
    · exact RefR.bind (badα := fun o => o = none)
        (iha fun b hb => ih b (List.mem_cons_of_mem a hb))
        (fun _ _ => RefR.pure _) (fun r hr s => by subst hr; rfl)
    · exact RefR.pure _

theorem forLoop_off {v₁ v₂ : String} {b₁ b₂ : ImpExpr} {D : Nat}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v₁ w) (e₂.extend v₂ w))
    (h : ∀ F, RefE R (denote' bi₁ (F + D) b₁) (denote' bi₂ F b₂)) :
    ∀ F lo hi, RefE R (denoteForLoop' bi₁ (F + D) v₁ lo hi b₁)
      (denoteForLoop' bi₂ F v₂ lo hi b₂) := by
  intro F
  induction F with
  | zero =>
    intro lo hi
    unfold denoteForLoop'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact RefR.pure _
    · simp only [hl, if_false, if_true]
      apply RefR.of_bad; intro _; exact ⟨_, rfl⟩
  | succ n ih =>
    intro lo hi
    unfold denoteForLoop'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact RefR.pure _
    · have h1 : n + 1 + D ≠ 0 := by omega
      have h2 : n + 1 + D - 1 = n + D := by omega
      simp only [hl, if_false, h1, Nat.add_one_ne_zero, Nat.add_sub_cancel, h2]
      refine refR_modify2 (fun e₁ e₂ h => hv e₁ e₂ _ h) (fun _ => ?_)
      refine RefR.bind (badα := IsErr) (h (n + 1)) (fun o ho => ?_) (fun a ha s => by
        obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
      split <;> first | exact RefR.pure _ | exact ih _ _

theorem forLoopRev_off {v₁ v₂ : String} {b₁ b₂ : ImpExpr} {D : Nat}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v₁ w) (e₂.extend v₂ w))
    (h : ∀ F, RefE R (denote' bi₁ (F + D) b₁) (denote' bi₂ F b₂)) :
    ∀ F lo hi, RefE R (denoteForLoopRev' bi₁ (F + D) v₁ lo hi b₁)
      (denoteForLoopRev' bi₂ F v₂ lo hi b₂) := by
  intro F
  induction F with
  | zero =>
    intro lo hi
    unfold denoteForLoopRev'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact RefR.pure _
    · simp only [hl, if_false, if_true]
      apply RefR.of_bad; intro _; exact ⟨_, rfl⟩
  | succ n ih =>
    intro lo hi
    unfold denoteForLoopRev'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact RefR.pure _
    · have h1 : n + 1 + D ≠ 0 := by omega
      have h2 : n + 1 + D - 1 = n + D := by omega
      simp only [hl, if_false, h1, Nat.add_one_ne_zero, Nat.add_sub_cancel, h2]
      refine refR_modify2 (fun e₁ e₂ h => hv e₁ e₂ _ h) (fun _ => ?_)
      refine RefR.bind (badα := IsErr) (h (n + 1)) (fun o ho => ?_) (fun a ha s => by
        obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
      split <;> first | exact RefR.pure _ | exact ih _ _

/-- A call of a name the two builtins answer alike, on related arguments. -/
theorem app_ref {g : String} (hg : ∀ vals, bi₁ g vals = bi₂ g vals) {F₁ F₂ : Nat}
    {args₁ args₂ : List ImpExpr}
    (hargs : RefR R R (fun o => o = none) (denoteArgs' bi₁ F₁ args₁) (denoteArgs' bi₂ F₂ args₂)) :
    RefE R (denote' bi₁ F₁ (.app g args₁)) (denote' bi₂ F₂ (.app g args₂)) := by
  simp only [denote']
  unfold denoteApp'
  refine RefR.bind (badα := fun o => o = none) hargs (fun r hr => ?_)
    (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
  split
  · rw [hg]
    split <;> exact RefR.pure _
  · exact absurd rfl hr

end Steps

/-! ## The arguments and the parameters of a call block -/

/-- The values of a successful run of the arguments are as many as the arguments, and none
    is a control-flow value. -/
theorem denoteArgs'_some (bi : Builtins) (F : Nat) :
    ∀ (args : List ImpExpr) (e e' : Env) (vals : List Value),
      (denoteArgs' bi F args).run e = (some vals, e') →
        vals.length = args.length ∧ ∀ v ∈ vals, ∀ b w, v ≠ .controlFlow b w
  | [], e, e', vals, h => by
      simp only [denoteArgs'] at h
      cases h
      simp
  | a :: as, e, e', vals, h => by
      rw [denoteArgs', run_bind] at h
      generalize (denote' bi F a).run e = r at h
      obtain ⟨o, e1⟩ := r
      simp only at h
      split at h
      · cases h
      · rename_i v hv
        rw [run_bind] at h
        generalize hr : (denoteArgs' bi F as).run e1 = r at h
        obtain ⟨ro, e2⟩ := r
        cases ro with
        | none => cases h
        | some vs =>
          cases h
          obtain ⟨hl, hc⟩ := denoteArgs'_some bi F as e1 e2 vs hr
          refine ⟨by simp [hl], ?_⟩
          intro w hw b w'
          rcases List.mem_cons.mp hw with rfl | hw
          · exact fun h => hv b w' h
          · exact hc w hw b w'
      · cases h

/-- The run of the bindings of the parameters `ps` from the position `i` of the tuple bound
    to `tmpName n`: the run of `b` from an environment that reads the level name of each
    parameter as `paramsEnv` reads the parameter, and agrees with the environment before at
    every name that is not a level name of the level `n`. -/
theorem bindParams_run (bi : Builtins) (F n : Nat) (vals : List Value)
    (hcf : ∀ v ∈ vals, ∀ b w, v ≠ .controlFlow b w) :
    ∀ (ps : List String) (i : Nat) (b : ImpExpr) (e : Env),
      e (tmpName n) = some (.tuple vals) → i + ps.length ≤ vals.length →
      ∃ e', (denote' bi F (bindParams n i ps b)).run e = (denote' bi F b).run e' ∧
        (∀ x v, paramsEnv ps (vals.drop i) x = some v → e' (lvlName n x) = some v) ∧
        (∀ y, (∀ x, y ≠ lvlName n x) → e' y = e y)
  | [], i, b, e, _, _ => ⟨e, rfl, fun x v h => by simp [paramsEnv] at h, fun _ _ => rfl⟩
  | p :: ps, i, b, e, ht, hl => by
      simp only [List.length_cons] at hl
      obtain ⟨e'', hrun, hpar, hfr⟩ := bindParams_run bi F n vals hcf ps (i + 1)
        (.letBind (lvlName n p) (.proj (.var (tmpName n)) i) b) e ht (by omega)
      have hi : i < vals.length := by omega
      have ht' : e'' (tmpName n) = some (.tuple vals) := by
        rw [hfr _ (fun x h => lvlName_ne_tmpName n n x h.symm)]; exact ht
      refine ⟨e''.extend (lvlName n p) vals[i], ?_, ?_, ?_⟩
      · rw [bindParams, hrun, Hax.ContinueFlag.letBind_run]
        have hproj : (denote' bi F (.proj (.var (tmpName n)) i)).run e'' =
            (.val vals[i], e'') := by
          simp only [denote', StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
            StateT.get, pure, StateT.pure, ht', Value.projIdx, List.getElem?_eq_getElem hi]
        rw [hproj]
        have hv := hcf vals[i] (List.getElem_mem hi)
        generalize vals[i] = v at hv ⊢
        cases v <;> first | rfl | exact absurd rfl (hv _ _)
      · intro x v hx
        rw [List.drop_eq_getElem_cons hi] at hx
        simp only [paramsEnv] at hx
        by_cases hxp : x = p
        · subst hxp
          simp only [if_true] at hx
          cases hx
          exact Env.extend_same _ _ _
        · rw [if_neg hxp] at hx
          rw [Env.extend_other _ _ _ _ (fun h => hxp (lvlName_inj h).2)]
          exact hpar x v hx
      · intro y hy
        rw [Env.extend_other _ _ _ _ (hy p), hfr y hy]

/-! ## The relations the refinement keeps -/

/-- **The relations between the environment `e₁` of the inlined term and the environment
    `e₂` of the source term, at the depth `n` and the renaming `ρ`**: a name `x` of the
    source bound in `e₂` is bound to the same value at `ρ x` in `e₁`; binding `ρ x` and `x`
    to one value keeps the relation; and the relation does not read `e₁` at the names of the
    levels below `n`. -/
structure InlRel (n : Nat) (ρ : String → String) (R : Env → Env → Prop) : Prop where
  /-- A bound name of the source is read alike. -/
  read : ∀ e₁ e₂ x v, R e₁ e₂ → okName x = true → e₂ x = some v → e₁ (ρ x) = some v
  /-- Binding a name of the source keeps the relation. -/
  ext : ∀ e₁ e₂ x w, R e₁ e₂ → okName x = true → R (e₁.extend (ρ x) w) (e₂.extend x w)
  /-- The relation does not read the names of the levels below `n`. -/
  low : ∀ e₁ e₁' e₂, R e₁ e₂ → (∀ y, ¬ IsLow n y → e₁' y = e₁ y) → R e₁' e₂

/-! ## The refinement -/

/-- **The transformation refines the source term** under `InlRel`, at the fuel offset `D`,
    when the site function refines each call the check `call` accepts, on related
    arguments. -/
theorem xf_ref {bi B : Builtins} {n : Nat} {ρ : String → String} {R : Env → Env → Prop}
    (hR : InlRel n ρ R) {D : Nat} {site : String → List ImpExpr → Option ImpExpr}
    {call : String → List ImpExpr → Bool}
    (hsite : ∀ g args args' F, call g args = true →
      RefR R R (fun o => o = none) (denoteArgs' bi (F + D) args') (denoteArgs' B F args) →
      RefE R (denote' bi (F + D) ((site g args').getD (.app g args'))) (denote' B F (.app g args))) :
    ∀ e, okX call e = true → ∀ F, RefE R (denote' bi (F + D) (xf ρ site e)) (denote' B F e) := by
  intro e
  induction e using ImpExpr.ind with
  | lit l =>
    intro _ F
    simp only [xf, denote']
    exact RefR.pure _
  | unitVal =>
    intro _ F
    simp only [xf, denote']
    exact RefR.pure _
  | var x =>
    intro hK F e₁ e₂ hP o s₂ hr hnb
    simp only [okX] at hK
    simp only [xf]
    rw [Hax.ContinueFlag.var_run] at hr ⊢
    cases h : e₂ x with
    | none =>
      simp only [h] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      exact absurd ⟨_, rfl⟩ hnb
    | some v =>
      simp only [h] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      rw [hR.read e₁ e₂ x v hP hK h]
      exact ⟨e₁, rfl, hP⟩
  | letBind x v b ihv ihb =>
    intro hK F
    simp only [okX, Bool.and_eq_true] at hK
    simp only [xf, denote']
    refine RefR.bind (badα := IsErr) (ihv hK.1.2 F) (fun o ho => ?_) (fun a ha s => by
      obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    split
    · exact RefR.pure _
    · exact refR_modify2 (fun e₁ e₂ h => hR.ext e₁ e₂ x _ h hK.1.1) (fun _ => ihb hK.2 F)
    · exact RefR.pure _
  | assign x r ih =>
    intro hK F
    simp only [okX, Bool.and_eq_true] at hK
    simp only [xf, denote']
    refine RefR.bind (badα := IsErr) (ih hK.2 F) (fun o ho => ?_) (fun a ha s => by
      obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    split
    · exact RefR.pure _
    · exact refR_modify2 (fun e₁ e₂ h => hR.ext e₁ e₂ x _ h hK.1) (fun _ => RefR.pure _)
    · exact RefR.pure _
  | app g args ih =>
    intro hK F
    simp only [okX, okX.okXList_eq, List.all_eq_true, Bool.and_eq_true] at hK
    simp only [xf, xf.xfList_eq]
    exact hsite g args _ F hK.2 (args_off _ args _ _ fun a ha => ih a ha (hK.1 a ha) F)
  | tuple es ih =>
    intro hK F
    simp only [okX, okX.okXList_eq, List.all_eq_true] at hK
    simp only [xf, xf.xfList_eq, denote']
    refine RefR.bind (badα := fun o => o = none)
      (args_off _ es _ _ fun a ha => ih a ha (hK a ha) F)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
    split <;> exact RefR.pure _
  | ifThenElse c t e ihc iht ihe =>
    intro hK F
    simp only [okX, Bool.and_eq_true] at hK
    have h1 := ihc hK.1.1 F
    have h2 := iht hK.1.2
    have h3 := ihe hK.2
    simp only [xf, denote']
    rel_step
  | seq a b iha ihb =>
    intro hK F
    simp only [okX, Bool.and_eq_true] at hK
    have h1 := iha hK.1 F
    have h2 := ihb hK.2
    simp only [xf, denote']
    rel_step
  | typeAscription e s ih =>
    intro hK F
    simp only [okX] at hK
    simp only [xf, denote']
    exact ih hK F
  | forFold i lo hi b ihl ihh ihb =>
    intro hK F
    simp only [okX, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2 F
    have hh := ihh hK.1.2
    have := forLoop_off (fun e₁ e₂ w h => hR.ext e₁ e₂ i w h hK.1.1.1) (ihb hK.2)
    simp only [xf, denote']
    rel_step
  | forFoldRev i lo hi b ihl ihh ihb =>
    intro hK F
    simp only [okX, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2 F
    have hh := ihh hK.1.2
    have := forLoopRev_off (fun e₁ e₂ w h => hR.ext e₁ e₂ i w h hK.1.1.1) (ihb hK.2)
    simp only [xf, denote']
    rel_step
  | _ =>
    intro hK
    simp [okX] at hK

/-- **The call block refines the call** of a function `c` of `fs` at the depth `n + 1`, on
    related arguments, when the inlined body refines the body at the depth `n` under every
    relation of the level `n`, for a fuel offset `D ≥ (n + 1) * fuelC`. -/
theorem callBlock_ref {fs : List CrateFn} {bi : Builtins} {fuelC n : Nat} {c : CrateFn}
    {g : String} (hc : fs.find? (·.name == g) = some c) {ρ : String → String}
    {R : Env → Env → Prop} (hR : InlRel (n + 1) ρ R) {args args' : List ImpExpr}
    (hlen : args.length = c.params.length) {D F : Nat} (hD : (n + 1) * fuelC ≤ D)
    (hargs : RefR R R (fun o => o = none) (denoteArgs' bi (F + D) args')
      (denoteArgs' (crateBi fs bi fuelC (n + 1)) F args))
    (hbody : ∀ R', InlRel n (lvlName n) R' → ∀ D', n * fuelC ≤ D' → ∀ F₀,
      RefE R' (denote' bi (F₀ + D') (inl fs n (lvlName n) c.body))
        (denote' (crateBi fs bi fuelC n) F₀ c.body)) :
    RefE R (denote' bi (F + D) (callBlock n (c.params.map (·.1)) args'
        (inl fs n (lvlName n) c.body)))
      (denote' (crateBi fs bi fuelC (n + 1)) F (.app g args)) := by
  intro e₁ e₂ hP o s₂ hr hnb
  -- the run of the source call
  simp only [denote'] at hr
  unfold denoteApp' at hr
  rw [run_bind] at hr
  generalize hA : (denoteArgs' (crateBi fs bi fuelC (n + 1)) F args).run e₂ = A at hr
  obtain ⟨mv, e₂'⟩ := A
  cases mv with
  | none => exact absurd ⟨_, (Prod.mk.inj hr).1.symm⟩ hnb
  | some vals =>
  simp only [crateBi, hc] at hr
  generalize hB : (denote' (crateBi fs bi fuelC n) fuelC c.body).run
    (paramsEnv (c.params.map (·.1)) vals) = Bd at hr
  obtain ⟨ob, sb⟩ := Bd
  have hob : ∃ v, ob = .val v ∧ o = .val v ∧ s₂ = e₂' := by
    simp only at hr
    split at hr
    · rename_i v hv
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      split at hv
      · split at hv
        · cases hv
          exact ⟨_, rfl, rfl, rfl⟩
        · cases hv
      · cases hv
    · exact absurd ⟨_, (Prod.mk.inj hr).1.symm⟩ hnb
  obtain ⟨v, rfl, rfl, hs⟩ := hob
  -- the arguments of the block
  obtain ⟨e₁', hA₁, hR'⟩ := hargs e₁ e₂ hP (some vals) e₂' hA (by simp)
  obtain ⟨hvl, hcf⟩ := denoteArgs'_some _ _ args e₂ e₂' vals hA
  have hT : (denote' bi (F + D) (.tuple args')).run e₁ = (.val (.tuple vals), e₁') := by
    simp only [denote']
    rw [run_bind, hA₁]
    rfl
  set eT := e₁'.extend (tmpName n) (.tuple vals) with heT
  obtain ⟨eB, hrunB, hpar, hfr⟩ := bindParams_run bi (F + D) n vals hcf
    (c.params.map (·.1)) 0 (inl fs n (lvlName n) c.body) eT (Env.extend_same _ _ _)
    (by simp [hvl, hlen])
  -- the body under the relation of the level `n`
  let R' : Env → Env → Prop := fun a b =>
    (∀ x w, okName x = true → b x = some w → a (lvlName n x) = some w) ∧
      ∀ y, ¬ IsLow (n + 1) y → a y = eB y
  have hR'rel : InlRel n (lvlName n) R' := by
    refine ⟨fun a b x w h hx hb => h.1 x w hx hb, fun a b x w h hx => ⟨?_, ?_⟩,
      fun a a' b h hlo => ⟨?_, ?_⟩⟩
    · intro z u hz hb
      by_cases hzx : z = x
      · subst hzx
        rw [Env.extend_same] at hb ⊢
        exact hb
      · rw [Env.extend_other _ _ _ _ hzx] at hb
        rw [Env.extend_other _ _ _ _ (fun h' => hzx (lvlName_inj h').2)]
        exact h.1 z u hz hb
    · intro y hy
      rw [Env.extend_other _ _ _ _ (fun h' => hy (by rw [h']; exact isLow_lvlName (by omega) x))]
      exact h.2 y hy
    · intro z u hz hb
      rw [hlo _ (not_isLow_lvlName n z)]
      exact h.1 z u hz hb
    · intro y hy
      rw [hlo _ (fun h' => hy (h'.mono (by omega)))]
      exact h.2 y hy
  have hstart : R' eB (paramsEnv (c.params.map (·.1)) vals) :=
    ⟨fun x w _ hb => hpar x w (by simpa using hb), fun _ _ => rfl⟩
  have hDle : n * fuelC ≤ F + D - fuelC := by
    have : (n + 1) * fuelC = n * fuelC + fuelC := Nat.succ_mul n fuelC
    omega
  have hfe : fuelC + (F + D - fuelC) = F + D := by
    have : (n + 1) * fuelC = n * fuelC + fuelC := Nat.succ_mul n fuelC
    omega
  obtain ⟨s₁, hs₁, hRs⟩ := hbody R' hR'rel (F + D - fuelC) hDle fuelC eB
    (paramsEnv (c.params.map (·.1)) vals) hstart (.val v) sb hB (by simp [IsErr])
  rw [hfe] at hs₁
  refine ⟨s₁, ?_, ?_⟩
  · rw [callBlock, Hax.ContinueFlag.letBind_run, hT]
    simp only
    rw [hrunB, hs₁]
  · rw [hs]
    refine hR.low e₁' s₁ e₂' hR' (fun y hy => ?_)
    rw [hRs.2 y hy, hfr y (fun x h' => hy (by rw [h']; exact isLow_lvlName (by omega) x)), heT,
      Env.extend_other _ _ _ _ (fun h' => hy (by rw [h']; exact isLow_tmpName (by omega)))]

/-- **The inliner refines the source term.** Under a relation `InlRel n ρ R`, a term `e`
    accepted by `inlOk fs n` inlined at the depth `n` and run at the builtins `bi` and the
    fuel `F + D` refines `e` run at the builtins with the crate `crateBi fs bi fuelC n` and
    the fuel `F`, for every fuel offset `D ≥ n * fuelC`: every run of `e` that does not end in
    an error is a run of the inlined term with the same outcome, the final environments
    related by `R`. -/
theorem inl_ref (fs : List CrateFn) (bi : Builtins) (fuelC : Nat) :
    ∀ (n : Nat) (ρ : String → String) (R : Env → Env → Prop), InlRel n ρ R →
      ∀ e, inlOk fs n e = true → ∀ D, n * fuelC ≤ D → ∀ F,
        RefE R (denote' bi (F + D) (inl fs n ρ e)) (denote' (crateBi fs bi fuelC n) F e)
  | 0, ρ, R, hR, e, he, D, _, F => by
      rw [inl]
      refine xf_ref hR (call := fun g _ => (fs.find? (·.name == g)).isNone) ?_ e
        (by simpa only [inlOk] using he) F
      intro g args args' F' hg hargs
      simp only [Option.getD_none]
      exact app_ref (fun vals => (crateBi_of_find_none fs bi fuelC 0
        (Option.isNone_iff_eq_none.mp hg) vals).symm) hargs
  | n + 1, ρ, R, hR, e, he, D, hD, F => by
      rw [inl]
      refine xf_ref hR (call := fun g args =>
        match fs.find? (·.name == g) with
        | none => true
        | some c => args.length == c.params.length && inlOk fs n c.body) ?_ e
        (by simpa only [inlOk] using he) F
      intro g args args' F' hg hargs
      cases hf : fs.find? (·.name == g) with
      | none =>
        simp only [Option.map_none, Option.getD_none]
        exact app_ref (fun vals => (crateBi_of_find_none fs bi fuelC (n + 1) hf vals).symm)
          hargs
      | some c =>
        simp only [hf, Bool.and_eq_true, beq_iff_eq] at hg
        simp only [Option.map_some, Option.getD_some]
        exact callBlock_ref hf hR hg.1 hD hargs
          (fun R' hR' D' hD' F₀ => inl_ref fs bi fuelC n (lvlName n) R' hR' c.body hg.2 D' hD' F₀)

/-- The relation of `inlineCrate_denote'`: every binding of a name of the source of the
    right environment is a binding of the left one. It is a relation `InlRel n id` at every
    depth. -/
theorem inlRel_srcAgree (n : Nat) :
    InlRel n id fun a b => ∀ x v, okName x = true → b x = some v → a x = some v := by
  refine ⟨fun a b x v h hx hb => h x v hx hb, fun a b x w h hx => ?_,
    fun a a' b h hlo => ?_⟩
  · intro z u hz hb
    by_cases hzx : z = x
    · subst hzx
      rw [Env.extend_same] at hb
      simpa using hb
    · rw [Env.extend_other _ _ _ _ hzx] at hb
      simp only [id]
      rw [Env.extend_other _ _ _ _ hzx]
      exact h z u hz hb
  · intro z u hz hb
    rw [hlo z (not_isLow_of_okName hz n)]
    exact h z u hz hb

/-- **Inlining keeps every run that does not end in an error.** For a term `e` accepted by
    `inlOk fs n`, a run of `e` at the builtins with the crate `crateBi fs bi fuelC n` and the
    fuel `F` from `env` that does not end in an error is a run of `inlineCrate fs n e` at the
    builtins `bi` and the fuel `F + D`, for every `D ≥ n * fuelC`, from `env`, with the same
    outcome; the final environment holds every binding of a name of the source of the final
    environment of the source run. -/
theorem inlineCrate_denote' (fs : List CrateFn) (bi : Builtins) (fuelC n : Nat) {e : ImpExpr}
    (he : inlOk fs n e = true) {F D : Nat} (hD : n * fuelC ≤ D) {env s : Env} {o : Outcome}
    (hrun : (denote' (crateBi fs bi fuelC n) F e).run env = (o, s)) (ho : ¬ IsErr o) :
    ∃ s', (denote' bi (F + D) (inlineCrate fs n e)).run env = (o, s') ∧
      ∀ x v, okName x = true → s x = some v → s' x = some v :=
  inl_ref fs bi fuelC n id _ (inlRel_srcAgree n) e he D hD F env env (fun _ _ _ h => h) o s
    hrun ho

end CatCrypt.Crypto.Hax.ImpInline
