/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes
public import CatCrypt.Crypto.SecureCompilation.Haxc.Consts

/-!
# Closed constants of a crate bound in the source

The constants of a crate are given by their typed bodies. The pre-pass `bindClosed` binds at
the head of an extraction the bodies of the constants that the extraction reads free, directly
or through other such constants, and whose bodies are closed up to them. A constant follows
the constants its body reads, a name bound by a parameter is no constant, and a constant on a
cycle has no binding. A literal body is bound as `bindConsts` binds its value
(`bindClosed_literal`).

The evaluator `denote'` does not restore the environment at the end of a `letBind`, so a
binding inside the body of a constant remains in the environment of the extraction. The pass
binds such a body only when neither the extraction nor a constant bound after it reads a name
the body binds (`scopeOk`), and the frame of the statement spine (`denoteSpine_frame`) then
gives the values of the source. A body with a `match_` has no binding, and a body that binds a
name is bound only in front of an extraction without `match_`, since the frame `denote'_frame`
is stated for expressions without `match_`.

The source with its constants evaluates each bound body in the environment of the constants
before it (`constsEnv`) and reads the entry and each function of a module from its parameters
over that environment (`haxRunsC`). It is the source semantics `haxRuns` of the module with
bound bodies (`haxRuns_bindModule`), so `haxc_correct_auto_access` applies.

## Main results

* `bindClosed`, `bindModule`: the pre-pass on an extraction and on a module.
* `bindClosed_of_not_read`: the pass is the identity on an extraction that reads no constant.
* `closedB_closedConsts`, `mem_closedConsts`: the order of the bindings and the constants bound.
* `run_bindClosed_of_holds`, `run_bindClosed_eq`, `run_bindClosed`: the source theorem.
* `bindClosed_literal`, `closedFnsE_literal`: `bindConsts` and `modFnsE` are the literal case.
* `haxc_correct_closed`: the compiler theorem on a module with the constants of its crate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ClosedConsts

open _root_.Hax (ImpExpr ImpLit TExpr Value Env Builtins Outcome denote' freeVars)
open _root_.Hax.InlineLocalClosures (denoteSpine frameOk bindVars bindAll closureTable IsErr RefE
  RefR denote'_frame renameReads_id frameOk_mono denote'_letBind_lam_err)
open CatCrypt.Crypto.Hax (TyFact tyAgree factNameTys texprFacts isLamE denoteSpine_letBind
  denoteSpine_seq spineLetStep spineSeqStep HaxModule ModFn refBi hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (paramsEnv dec)
open CatCrypt.Crypto.Hax.FrontDomain (ModuleRefusal)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## The bindings -/

/-- The literal bound for a constant with a scalar literal body: an integer or a Boolean. -/
def bodyLit : ImpExpr → Option ImpLit
  | .lit (.int n) => some (.int n)
  | .lit (.uintLit _ n) => some (.int (n : Int))
  | .lit (.sintLit _ n) => some (.int n)
  | .lit (.bool b) => some (.bool b)
  | _ => none

/-- The body a constant denotes by: its literal `bodyLit`, or the erasure of its body. -/
def constBody (c : TExpr) : ImpExpr :=
  match bodyLit c.erase with
  | some l => .lit l
  | none => c.erase

/-- The typed body bound for the constant `k`: its body, or its literal typed as the facts `F`
    type the occurrences of `k`. -/
def constExpr (F : List TyFact) (k : String) (c : TExpr) : TExpr :=
  match bodyLit c.erase with
  | some l => .mk (.lit l) (tyAgree (factNameTys F k))
  | none => c

/-- The typed body bound for a constant erases to the body it denotes by. -/
theorem erase_constExpr (F : List TyFact) (k : String) (c : TExpr) :
    (constExpr F k c).erase = constBody c := by
  unfold constExpr constBody
  split <;> simp [TExpr.erase, *]

/-- The typing facts of an extraction and of the bodies of `cs` that are no literals. -/
def constFacts (cs : List (String × TExpr)) (te : TExpr) : List TyFact :=
  texprFacts te ++ cs.flatMap fun c =>
    if (bodyLit c.2.erase).isSome then [] else texprFacts c.2

/-- The constants `cs` bound in their order at the head of `te`, at the typing facts `F`. -/
def bindBodiesAt (F : List TyFact) : List (String × TExpr) → TExpr → TExpr
  | [], te => te
  | (k, c) :: cs, te =>
    let te' := bindBodiesAt F cs te
    .mk (.letBind k (constExpr F k c) te') te'.ty

/-- The constants `cs` bound in their order at the head of `te`. -/
def bindBodies (cs : List (String × TExpr)) (te : TExpr) : TExpr :=
  bindBodiesAt (constFacts cs te) cs te

/-- The erasure of `bindBodies`: the bodies bound at the head of an erased extraction. -/
def bindE : List (String × TExpr) → ImpExpr → ImpExpr
  | [], e => e
  | c :: cs, e => .letBind c.1 (constBody c.2) (bindE cs e)

/-- The erasure of the bound extraction does not depend on the types of the literals. -/
theorem erase_bindBodiesAt (F : List TyFact) (te : TExpr) :
    ∀ cs, (bindBodiesAt F cs te).erase = bindE cs te.erase
  | [] => by simp [bindBodiesAt, bindE]
  | (k, c) :: cs => by
    simp [bindBodiesAt, bindE, TExpr.erase, erase_constExpr, erase_bindBodiesAt F te cs]

/-- The erasure of `bindBodies`. -/
theorem erase_bindBodies (cs : List (String × TExpr)) (te : TExpr) :
    (bindBodies cs te).erase = bindE cs te.erase :=
  erase_bindBodiesAt _ te cs

/-! ## The constants bound -/

/-- The body of a constant is no closure and binds no name. -/
def bindFree (c : String × TExpr) : Bool :=
  !isLamE (constBody c.2) && (bindVars (constBody c.2)).isEmpty &&
    frameOk (fun _ => true) (bindVars (constBody c.2)).contains (fun _ => true) (constBody c.2)

/-- The body of `c` is closed up to the names `dn`: it reads only these and the names it
    binds. -/
def ready (dn : List String) (c : String × TExpr) : Bool :=
  frameOk (fun x => dn.contains x || (bindVars (constBody c.2)).contains x)
    (bindVars (constBody c.2)).contains (fun _ => true) (constBody c.2)

/-- The body of `c` reads the name `k`. -/
def readsName (k : String) (c : String × TExpr) : Bool :=
  !frameOk (fun x => x != k) (fun _ => true) (fun _ => true) (constBody c.2)

/-- Each constant of a list is closed up to `dn` and the constants before it. -/
def closedB : List String → List (String × TExpr) → Bool
  | _, [] => true
  | dn, c :: cs => ready dn c && closedB (c.1 :: dn) cs

/-- The first constant of each name. -/
def firstOfName : List (String × TExpr) → List (String × TExpr)
  | [] => []
  | c :: cs => c :: (firstOfName cs).filter (·.1 != c.1)

/-- The candidates of an extraction with the bound names `excl`: the first constant of each
    name that is not among `excl`. -/
def constCands (excl : List String) (consts : List (String × TExpr)) : List (String × TExpr) :=
  (firstOfName consts).filter fun c => !excl.contains c.1

/-- The constants of `cs` closed up to `dn` and to each other, dependencies first, in at most
    `n` rounds. A constant on a cycle is in no round. -/
def closedOrder : Nat → List String → List (String × TExpr) → List (String × TExpr)
  | 0, _, _ => []
  | n + 1, dn, cs =>
    let now := cs.filter (ready dn)
    if now.isEmpty then []
    else now ++ closedOrder n (now.map (·.1) ++ dn) (cs.filter fun c => !ready dn c)

/-- The constants of an ordered list that the names `free` read, directly or through a
    constant after them. -/
def readTrim (free : List String) : List (String × TExpr) → List (String × TExpr)
  | [] => []
  | c :: cs =>
    let r := readTrim free cs
    if free.contains c.1 || r.any (readsName c.1) then c :: r else r

/-- **The scope of the body of a constant** `c` bound in front of the constants `cs` and the
    expression `e`, with the names `excl` bound by the parameters: the body is no closure and
    reads no parameter and neither its own name nor one of `cs`; `c` has none of these names;
    and neither `e` nor a body of `cs` reads a name the body binds. -/
def scopeOk (excl : List String) (cs : List (String × TExpr)) (e : ImpExpr)
    (c : String × TExpr) : Bool :=
  let b := constBody c.2
  let W := bindVars b
  !isLamE b && !excl.contains c.1 && !cs.any (·.1 == c.1) &&
    frameOk (fun x => !excl.contains x && x != c.1 && !cs.any (·.1 == x)) W.contains
      (fun _ => true) b &&
    (W.isEmpty || frameOk (fun x => !W.contains x) (fun _ => true) (fun _ => true) e &&
      cs.all fun d => frameOk (fun x => !W.contains x) (fun _ => true) (fun _ => true)
        (constBody d.2))

/-- Each constant of a list is in scope in front of the constants after it. -/
def scopedB (excl : List String) (e : ImpExpr) : List (String × TExpr) → Bool
  | [] => true
  | c :: cs => scopeOk excl cs e c && scopedB excl e cs

/-- The constants of a list that are in scope in front of the kept constants after them. -/
def scopeSel (excl : List String) (e : ImpExpr) : List (String × TExpr) → List (String × TExpr)
  | [] => []
  | c :: cs =>
    let r := scopeSel excl e cs
    if scopeOk excl r e c then c :: r else r

/-- The constants of a list that are closed up to `dn` and the kept constants before them. -/
def closedUp : List String → List (String × TExpr) → List (String × TExpr)
  | _, [] => []
  | dn, c :: cs => if ready dn c then c :: closedUp (c.1 :: dn) cs else closedUp dn cs

/-- **The constants bound at the head of `te`**, whose parameters bind the names `excl`: of
    the candidates closed up to each other, in dependency order, those that `te` reads free,
    directly or through another of them, and whose bindings stay in scope. -/
def closedConsts (excl : List String) (consts : List (String × TExpr)) (te : TExpr) :
    List (String × TExpr) :=
  let free := freeVars te.erase
  let cands := constCands excl consts
  readTrim free
    (closedUp [] (scopeSel excl te.erase (readTrim free (closedOrder cands.length [] cands))))

/-- **The pre-pass**: the typed bodies of `closedConsts` bound at the head of the extraction. -/
def bindClosed (excl : List String) (consts : List (String × TExpr)) (te : TExpr) : TExpr :=
  bindBodies (closedConsts excl consts te) te

/-! ## The properties of the choice -/

/-- `readTrim` keeps a sublist. -/
theorem readTrim_sublist (free : List String) : ∀ cs, (readTrim free cs).Sublist cs
  | [] => by simp [readTrim]
  | c :: cs => by
    have ih := readTrim_sublist free cs
    simp only [readTrim]
    split
    · exact ih.cons_cons c
    · exact ih.cons c

/-- `scopeSel` keeps a sublist. -/
theorem scopeSel_sublist (excl : List String) (e : ImpExpr) :
    ∀ cs, (scopeSel excl e cs).Sublist cs
  | [] => by simp [scopeSel]
  | c :: cs => by
    have ih := scopeSel_sublist excl e cs
    simp only [scopeSel]
    split
    · exact ih.cons_cons c
    · exact ih.cons c

/-- `closedUp` keeps a sublist. -/
theorem closedUp_sublist :∀ dn cs, (closedUp dn cs).Sublist cs
  | _, [] => by simp [closedUp]
  | dn, c :: cs => by
    simp only [closedUp]
    split
    · exact (closedUp_sublist _ cs).cons_cons c
    · exact (closedUp_sublist _ cs).cons c

/-- The order has each constant at most as often as the list it orders. -/
theorem closedOrder_subperm :∀ n dn cs, (closedOrder n dn cs).Subperm cs
  | 0, _, _ => by simp [closedOrder]
  | n + 1, dn, cs => by
    simp only [closedOrder]
    split
    · simp
    · exact ((List.subperm_append_left _).2 (closedOrder_subperm n _ _)).trans
        (List.filter_append_perm (ready dn) cs).subperm

/-- `readTrim` keeps no constant when none is read free. -/
theorem readTrim_eq_nil (free : List String) :
    ∀ cs, (∀ c ∈ cs, c.1 ∉ free) → readTrim free cs = []
  | [], _ => by simp [readTrim]
  | c :: cs, h => by
    have ih := readTrim_eq_nil free cs fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc := h c List.mem_cons_self
    simp [readTrim, ih, hc]

/-- `readTrim` is idempotent. -/
theorem readTrim_idem (free : List String) :
    ∀ cs, readTrim free (readTrim free cs) = readTrim free cs
  | [] => by simp [readTrim]
  | c :: cs => by
    have ih := readTrim_idem free cs
    grind [readTrim]

/-- `readTrim` keeps the constants read free. -/
theorem mem_readTrim_of_mem_free {free : List String} {c : String × TExpr} :
    ∀ {cs}, c ∈ cs → c.1 ∈ free → c ∈ readTrim free cs
  | d :: cs, h, hf => by
    have ih := fun h' => mem_readTrim_of_mem_free (cs := cs) h' hf
    grind [readTrim]

/-- The first constant of a name is a constant of the list. -/
theorem mem_of_mem_firstOfName {c : String × TExpr} :
    ∀ {cs}, c ∈ firstOfName cs → c ∈ cs
  | d :: cs, h => by
    have ih := fun h' => mem_of_mem_firstOfName (c := c) (cs := cs) h'
    grind [firstOfName]
  | [], h => by simp [firstOfName] at h

/-- The first constants of each name have distinct names. -/
theorem nodup_firstOfName :∀ cs, ((firstOfName cs).map (·.1)).Nodup
  | [] => by simp [firstOfName]
  | c :: cs => by
    simp only [firstOfName, List.map_cons, List.nodup_cons]
    exact ⟨by simp, (nodup_firstOfName cs).sublist (List.filter_sublist.map _)⟩

/-- A list with distinct names is the list of its first constants. -/
theorem firstOfName_of_nodup :∀ {cs : List (String × TExpr)},
    (cs.map (·.1)).Nodup → firstOfName cs = cs
  | [], _ => by simp [firstOfName]
  | c :: cs, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [firstOfName, firstOfName_of_nodup h.2, List.cons.injEq, true_and,
      List.filter_eq_self]
    grind

/-- An ordered candidate is a constant of the crate whose name no parameter binds. -/
theorem mem_closedOrder_constCands {excl : List String} {consts : List (String × TExpr)}
    {n : Nat} {c : String × TExpr} (h : c ∈ closedOrder n [] (constCands excl consts)) :
    c ∈ consts ∧ c.1 ∉ excl := by
  have := (closedOrder_subperm _ _ _).subset h
  simp only [constCands, List.mem_filter] at this
  exact ⟨mem_of_mem_firstOfName this.1, by simpa using this.2⟩

/-- A bound constant is a constant of the crate whose name no parameter binds. -/
theorem mem_of_mem_closedConsts {excl : List String} {consts : List (String × TExpr)}
    {te : TExpr} {c : String × TExpr} (h : c ∈ closedConsts excl consts te) :
    c ∈ consts ∧ c.1 ∉ excl :=
  mem_closedOrder_constCands <| (readTrim_sublist _ _).subset <| (scopeSel_sublist _ _ _).subset
    <| (closedUp_sublist _ _).subset <| (readTrim_sublist _ _).subset h

/-- **The pre-pass is the identity on an extraction that reads no constant**: when every
    constant the extraction reads free has the name of a parameter. -/
theorem bindClosed_of_not_read (excl : List String) (consts : List (String × TExpr))
    (te : TExpr) (h : ∀ c ∈ consts, c.1 ∈ freeVars te.erase → c.1 ∈ excl) :
    bindClosed excl consts te = te := by
  have hc : closedConsts excl consts te = [] := by
    refine readTrim_eq_nil _ _ fun c hc hf => ?_
    have := mem_closedOrder_constCands <| (readTrim_sublist _ _).subset <|
      (scopeSel_sublist _ _ _).subset <| (closedUp_sublist _ _).subset hc
    exact this.2 (h c this.1 hf)
  simp [bindClosed, bindBodies, hc, bindBodiesAt]

/-- An expression in two frames is in the frame of the names read in both. -/
theorem frameOk_and {rd rd' rd'' bd bd' ok : String → Bool}
    (h : ∀ x, rd x = true → rd' x = true → rd'' x = true) (e : ImpExpr) :
    frameOk rd bd ok e = true → frameOk rd' bd' ok e = true → frameOk rd'' bd ok e = true := by
  induction e using ImpExpr.ind with
  | app g args ih =>
    simp only [frameOk, _root_.Hax.InlineLocalClosures.frameOk.okList_eq, List.all_eq_true,
      Bool.and_eq_true]
    exact fun h₁ h₂ => ⟨h₁.1, fun a ha => ih a ha (h₁.2 a ha) (h₂.2 a ha)⟩
  | tuple es ih =>
    simp only [frameOk, _root_.Hax.InlineLocalClosures.frameOk.okList_eq, List.all_eq_true]
    exact fun h₁ h₂ a ha => ih a ha (h₁ a ha) (h₂ a ha)
  | match_ => simp [frameOk]
  | _ => simp_all [frameOk]

/-- A body closed up to some names is closed up to more names. -/
theorem ready_mono {dn dn' : List String} {c : String × TExpr}
    (h : ∀ x ∈ dn, x ∈ dn') (hc : ready dn c = true) : ready dn' c = true := by
  refine frameOk_mono (fun x hx => ?_) (fun _ hx => hx) (fun _ hx => hx) _ hc
  grind

/-- A list closed up to some names is closed up to more names. -/
theorem closedB_mono :∀ {cs} {dn dn' : List String},
    (∀ x ∈ dn, x ∈ dn') → closedB dn cs = true → closedB dn' cs = true
  | [], _, _, _, _ => by simp [closedB]
  | c :: cs, dn, dn', h, hc => by
    simp only [closedB, Bool.and_eq_true] at hc ⊢
    exact ⟨ready_mono h hc.1, closedB_mono (by grind) hc.2⟩

/-- A list closed up to a name that none of its bodies reads is closed without it. -/
theorem closedB_drop {k : String} : ∀ {cs} {dn dn' : List String},
    (∀ x ∈ dn, x = k ∨ x ∈ dn') → cs.any (readsName k) = false → closedB dn cs = true →
      closedB dn' cs = true
  | [], _, _, _, _, _ => by simp [closedB]
  | c :: cs, dn, dn', h, hr, hc => by
    simp only [closedB, Bool.and_eq_true, List.any_cons, Bool.or_eq_false_iff] at hc hr ⊢
    refine ⟨frameOk_and (fun x hx hx' => ?_) _ hc.1 (by simpa [readsName] using hr.1),
      closedB_drop (by grind) hr.2 hc.2⟩
    grind

/-- The result of `closedUp` is closed. -/
theorem closedB_closedUp :∀ dn cs, closedB dn (closedUp dn cs) = true
  | _, [] => by simp [closedUp, closedB]
  | dn, c :: cs => by
    simp only [closedUp]
    split
    · simp [closedB, closedB_closedUp, *]
    · exact closedB_closedUp dn cs

/-- `readTrim` keeps a closed list closed. -/
theorem closedB_readTrim (free : List String) :
    ∀ {cs dn}, closedB dn cs = true → closedB dn (readTrim free cs) = true
  | [], _, _ => by simp [readTrim, closedB]
  | c :: cs, dn, h => by
    simp only [closedB, Bool.and_eq_true] at h
    have ih := closedB_readTrim free h.2
    simp only [readTrim]
    split
    · simp [closedB, h.1, ih]
    · exact closedB_drop (k := c.1) (by grind) (by grind) ih

/-- **The bindings have their dependencies first**: each bound body reads, besides the names
    it binds, only constants bound before it. A cycle of constants is thus unbound. -/
theorem closedB_closedConsts (excl : List String) (consts : List (String × TExpr))
    (te : TExpr) : closedB [] (closedConsts excl consts te) = true :=
  closedB_readTrim _ (closedB_closedUp _ _)

/-- A round followed by a list closed up to its names is closed. -/
theorem closedB_append :∀ {as bs dn}, (∀ a ∈ as, ready dn a = true) →
    closedB (as.map (·.1) ++ dn) bs = true → closedB dn (as ++ bs) = true
  | [], _, _, _, h => by simpa using h
  | a :: as, bs, dn, ha, h => by
    simp only [List.cons_append, closedB, Bool.and_eq_true]
    refine ⟨ha a List.mem_cons_self, closedB_append (fun d hd => ?_) ?_⟩
    · exact ready_mono (by grind) (ha d (List.mem_cons_of_mem _ hd))
    · exact closedB_mono (by grind) h

/-- The order is closed. -/
theorem closedB_closedOrder :∀ n dn cs, closedB dn (closedOrder n dn cs) = true
  | 0, _, _ => by simp [closedOrder, closedB]
  | n + 1, dn, cs => by
    simp only [closedOrder]
    split
    · simp [closedB]
    · exact closedB_append (fun a ha => (List.mem_filter.1 ha).2) (closedB_closedOrder n _ _)

/-- The order is saturated: a constant closed up to it is in it. -/
theorem mem_closedOrder : ∀ n dn cs, cs.length ≤ n → ∀ c ∈ cs,
    ready ((closedOrder n dn cs).map (·.1) ++ dn) c = true → c ∈ closedOrder n dn cs
  | 0, _, cs, hn, c, hc, _ => by grind
  | n + 1, dn, cs, hn, c, hc, hr => by
    simp only [closedOrder] at hr ⊢
    split at hr
    · rename_i he
      simp only [List.isEmpty_iff, List.filter_eq_nil_iff] at he
      exact absurd (by simpa using hr) (he c hc)
    · rename_i he
      simp only [he, Bool.false_eq_true, ite_false, List.mem_append]
      by_cases hd : ready dn c = true
      · exact .inl (List.mem_filter.2 ⟨hc, hd⟩)
      · refine .inr (mem_closedOrder n _ _ ?_ c (by simp [hc, hd]) (ready_mono (by grind) hr))
        have hp := (List.filter_append_perm (ready dn) cs).length_eq
        have : 0 < (cs.filter (ready dn)).length :=
          List.length_pos_iff.2 fun h => he (List.isEmpty_iff.2 h)
        simp only [List.length_append] at hp
        omega

/-- The constants `scopeSel` keeps are in scope. -/
theorem scopedB_scopeSel (excl : List String) (e : ImpExpr) :
    ∀ cs, scopedB excl e (scopeSel excl e cs) = true
  | [] => by simp [scopeSel, scopedB]
  | c :: cs => by
    simp only [scopeSel]
    split
    · simp [scopedB, scopedB_scopeSel excl e cs, *]
    · exact scopedB_scopeSel excl e cs

/-- A body in scope in front of a list is in scope in front of a sublist. -/
theorem scopeOk_sublist {excl : List String} {e : ImpExpr} {cs cs' : List (String × TExpr)}
    (h : cs'.Sublist cs) {c : String × TExpr} (hc : scopeOk excl cs e c = true) :
    scopeOk excl cs' e c = true := by
  have hs := h.subset
  simp only [scopeOk, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hc ⊢
  obtain ⟨⟨⟨⟨hl, he⟩, hk⟩, hb⟩, hW⟩ := hc
  refine ⟨⟨⟨⟨hl, he⟩, by grind⟩, frameOk_mono (fun x hx => ?_) (fun _ hx => hx) (fun _ hx => hx)
    _ hb⟩, hW.imp id fun hW => ⟨hW.1, fun d hd => hW.2 d (hs hd)⟩⟩
  grind

/-- A sublist of a list in scope is in scope. -/
theorem scopedB_sublist {excl : List String} {e : ImpExpr} {cs cs' : List (String × TExpr)}
    (h : cs'.Sublist cs) : scopedB excl e cs = true → scopedB excl e cs' = true := by
  induction h with
  | slnil => simp
  | cons c _ ih => grind [scopedB]
  | cons_cons c h ih => grind [scopedB, scopeOk_sublist]

/-- **The bindings are in scope.** -/
theorem scopedB_closedConsts (excl : List String) (consts : List (String × TExpr))
    (te : TExpr) : scopedB excl te.erase (closedConsts excl consts te) = true :=
  scopedB_sublist ((readTrim_sublist _ _).trans (closedUp_sublist _ _)) (scopedB_scopeSel _ _ _)

/-- `closedUp` keeps a closed list. -/
theorem closedUp_eq_self :∀ {cs dn}, closedB dn cs = true → closedUp dn cs = cs
  | [], _, _ => by simp [closedUp]
  | c :: cs, dn, h => by
    simp only [closedB, Bool.and_eq_true] at h
    simp [closedUp, h.1, closedUp_eq_self h.2]

/-- `scopeSel` keeps a closed list of bodies that bind no name. -/
theorem scopeSel_eq_self (excl : List String) (e : ImpExpr) : ∀ {cs} {dn : List String},
    closedB dn cs = true → (∀ c ∈ cs, bindFree c = true) → (cs.map (·.1)).Nodup →
    (∀ c ∈ cs, c.1 ∉ excl ∧ c.1 ∉ dn) → (∀ x ∈ dn, x ∉ excl) → scopeSel excl e cs = cs
  | [], _, _, _, _, _, _ => by simp [scopeSel]
  | c :: cs, dn, hc, hb, hn, hk, hd => by
    simp only [closedB, Bool.and_eq_true] at hc
    simp only [List.map_cons, List.nodup_cons] at hn
    have ih := scopeSel_eq_self excl e hc.2 (fun d hd' => hb d (List.mem_cons_of_mem _ hd')) hn.2
      (by grind) (by grind)
    have hb' := hb c List.mem_cons_self
    simp only [bindFree, Bool.and_eq_true, List.isEmpty_iff] at hb'
    have hf : frameOk (fun x => !excl.contains x && x != c.1 && !cs.any (·.1 == x))
        (bindVars (constBody c.2)).contains (fun _ => true) (constBody c.2) = true := by
      refine frameOk_mono (fun x hx => ?_) (fun _ hx => hx) (fun _ hx => hx) _ hc.1
      grind
    have hok : scopeOk excl cs e c = true := by
      simp only [scopeOk, hb'.1.2, List.isEmpty_nil, Bool.true_or, Bool.and_true]
      grind
    simp [scopeSel, ih, hok]

/-- When no body of a closed constant that the extraction reads binds a name, all these
    constants are bound. -/
theorem closedConsts_of_bindFree (excl : List String) (consts : List (String × TExpr))
    (te : TExpr)
    (hb : ∀ c ∈ readTrim (freeVars te.erase) (closedOrder (constCands excl consts).length []
      (constCands excl consts)), bindFree c = true) :
    closedConsts excl consts te = readTrim (freeVars te.erase)
      (closedOrder (constCands excl consts).length [] (constCands excl consts)) := by
  have hc := closedB_readTrim (freeVars te.erase)
    (closedB_closedOrder (constCands excl consts).length [] (constCands excl consts))
  have hn : ((closedOrder (constCands excl consts).length []
      (constCands excl consts)).map (·.1)).Nodup := by
    obtain ⟨l, hp, hs⟩ := closedOrder_subperm (constCands excl consts).length []
      (constCands excl consts)
    exact (hp.map (·.1)).nodup_iff.1
      (((nodup_firstOfName consts).sublist (List.filter_sublist.map _)).sublist (hs.map _))
  have hs := scopeSel_eq_self excl te.erase hc hb (hn.sublist ((readTrim_sublist _ _).map _))
    (fun c h => ⟨(mem_closedOrder_constCands ((readTrim_sublist _ _).subset h)).2, by simp⟩)
    (by simp)
  simp only [closedConsts, hs, closedUp_eq_self hc, readTrim_idem]

/-- **Every closed constant the extraction reads free is bound.** Let no body of a closed
    constant that the extraction reads bind a name, and let `L` be candidates each closed up
    to those before it, so that `L` witnesses that their bodies are closed. A constant of `L`
    that the extraction reads free is bound. -/
theorem mem_closedConsts {excl : List String} {consts : List (String × TExpr)} {te : TExpr}
    (hb : ∀ c ∈ readTrim (freeVars te.erase) (closedOrder (constCands excl consts).length []
      (constCands excl consts)), bindFree c = true)
    {L : List (String × TExpr)} (hL : closedB [] L = true)
    (hsub : ∀ c ∈ L, c ∈ constCands excl consts) {c : String × TExpr} (hc : c ∈ L)
    (hread : c.1 ∈ freeVars te.erase) : c ∈ closedConsts excl consts te := by
  rw [closedConsts_of_bindFree excl consts te hb]
  refine mem_readTrim_of_mem_free ?_ hread
  generalize hO : closedOrder (constCands excl consts).length [] (constCands excl consts) = O
  suffices ∀ (L : List (String × TExpr)) (dn : List String), closedB dn L = true →
      (∀ d ∈ L, d ∈ constCands excl consts) → (∀ x ∈ dn, x ∈ O.map (·.1)) → ∀ d ∈ L, d ∈ O from
    this L [] hL hsub (by simp) c hc
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
    intro dn hL hsub hd
    simp only [closedB, Bool.and_eq_true] at hL
    have ha : a ∈ O := by
      rw [← hO]
      refine mem_closedOrder _ _ _ le_rfl a (hsub a List.mem_cons_self) ?_
      exact ready_mono (by grind) hL.1
    grind

/-! ## The frame of the statement spine -/

/-- Two environments agree at the names `rd`. -/
def AgreeOn (rd : String → Bool) (a b : Env) : Prop := ∀ x, rd x = true → a x = b x

/-- Agreement is symmetric. -/
theorem AgreeOn.symm {rd : String → Bool} {a b : Env} (h : AgreeOn rd a b) : AgreeOn rd b a :=
  fun x hx => (h x hx).symm

/-- Agreement is kept by a binding of one value. -/
theorem AgreeOn.extend {rd : String → Bool} {a b : Env} (h : AgreeOn rd a b) (n : String)
    (w : Value) : AgreeOn rd (a.extend n w) (b.extend n w) := by
  intro x hx
  simp only [Env.extend, h x hx]

/-- Agreement is kept by the bindings of the arguments of a closure. -/
theorem AgreeOn.bindAll {rd : String → Bool} {a b : Env} (h : AgreeOn rd a b) :
    ∀ ps vals, AgreeOn rd (bindAll a ps vals) (bindAll b ps vals)
  | [], _ => by simpa [_root_.Hax.InlineLocalClosures.bindAll] using h
  | _ :: _, [] => by simpa [_root_.Hax.InlineLocalClosures.bindAll] using h
  | p :: ps, v :: vs => (AgreeOn.bindAll h ps vs).extend p v

/-- `denote'_frame` at the identity renaming and one table. -/
theorem denote'_frame_self (bi : Builtins) {rd bd : String → Bool} {R : Env → Env → Prop}
    (hrd : ∀ a b x, R a b → rd x = true → a x = b x)
    (hbd : ∀ a b n w, R a b → bd n = true → R (a.extend n w) (b.extend n w)) {e : ImpExpr}
    (h : frameOk rd bd (fun _ => true) e = true) (fuel : Nat) :
    RefE R (denote' bi fuel e) (denote' bi fuel e) := by
  have := denote'_frame (R := R) (bi₁ := bi) (bi₂ := bi) id rd bd (fun _ => true) hrd hbd
    (fun _ _ => rfl) e h fuel
  rwa [renameReads_id e (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) e h)]
    at this

/-- An expression refines itself between environments that agree at the names it reads. -/
theorem denote'_agree (bi : Builtins) {rd bd : String → Bool} {e : ImpExpr}
    (h : frameOk rd bd (fun _ => true) e = true) (fuel : Nat) :
    RefE (AgreeOn rd) (denote' bi fuel e) (denote' bi fuel e) :=
  denote'_frame_self bi (fun _ _ x hR hx => hR x hx) (fun _ _ n w hR _ => hR.extend n w) h fuel

/-- An expression changes only the names it binds. -/
theorem denote'_writes (bi : Builtins) (fuel : Nat) {rd : String → Bool} {W : List String}
    {e : ImpExpr} (h : frameOk rd W.contains (fun _ => true) e = true) {env s : Env}
    {o : Outcome} (hr : (denote' bi fuel e).run env = (o, s)) (ho : ¬ IsErr o) :
    ∀ x, W.contains x = false → s x = env x := by
  have hf := denote'_frame_self bi
    (R := fun a b => a = b ∧ ∀ x, W.contains x = false → b x = env x)
    (fun _ _ x hR _ => by rw [hR.1])
    (fun a b n w hR hn => ⟨by rw [hR.1], fun x hx => by
      have : x ≠ n := by grind
      rw [Env.extend_other _ _ _ _ this]
      exact hR.2 x hx⟩) h fuel
  obtain ⟨_, -, -, h₂⟩ := hf env env ⟨rfl, fun _ _ => rfl⟩ o s hr ho
  exact h₂

/-- A run that refines itself under agreement has, up to errors, one outcome. -/
theorem outcome_eq_of_ref {rd : String → Bool} {m : StateM Env Outcome}
    (h : RefE (AgreeOn rd) m m) {a b : Env} (hR : AgreeOn rd a b) :
    (IsErr (m.run a).1 ∧ IsErr (m.run b).1) ∨ (m.run a).1 = (m.run b).1 := by
  by_cases h₂ : IsErr (m.run b).1
  · by_cases h₁ : IsErr (m.run a).1
    · exact .inl ⟨h₁, h₂⟩
    · obtain ⟨s, hs, -⟩ := h b a hR.symm _ _ rfl h₁
      exact .inr (congrArg Prod.fst hs).symm
  · obtain ⟨s, hs, -⟩ := h a b hR _ _ rfl h₂
    exact .inr (congrArg Prod.fst hs :)

/-- The table of a closure depends only on the names its body reads. -/
theorem closureTable_congr (bi : Builtins) (fuel : Nat) (f : String) (ps : List String)
    {rd bd : String → Bool} {body : ImpExpr}
    (h : frameOk rd bd (fun _ => true) body = true) {a b : Env} (hR : AgreeOn rd a b) :
    closureTable bi fuel f ps body a = closureTable bi fuel f ps body b := by
  funext g vals
  simp only [closureTable]
  split
  · split
    · rcases outcome_eq_of_ref (denote'_agree bi h fuel) (hR.bindAll ps vals) with
        ⟨⟨_, h₁⟩, _, h₂⟩ | h' <;> simp [*]
    · rfl
  · rfl

/-- **The frame of the statement spine**: from environments that agree at the names an
    extraction reads, the runs of its source reading that end in no error have the same
    outcome and end in environments that agree at these names. -/
theorem denoteSpine_frame {rd bd : String → Bool} (e : ImpExpr) :
    ∀ (bi : Builtins) (fuel : Nat), frameOk rd bd (fun _ => true) e = true →
      RefE (AgreeOn rd) (denoteSpine bi fuel e) (denoteSpine bi fuel e) := by
  induction e using ImpExpr.ind with
  | letBind x v cont ihv ihc =>
    intro bi fuel h
    clear ihv
    simp only [frameOk, Bool.and_eq_true] at h
    cases v
    case lam ps body =>
      simp only [denoteSpine]
      split
      · intro a b hR o s hr ho
        have hb : frameOk rd bd (fun _ => true) body = true := by simpa [frameOk] using h.1.2
        obtain ⟨s', hs, hR'⟩ := ihc (closureTable bi fuel x ps body b) fuel h.2 a b hR o s hr ho
        refine ⟨s', ?_, hR'⟩
        rw [← closureTable_congr bi fuel x ps hb hR] at hs
        exact hs
      · exact RefR.of_bad (denote'_letBind_lam_err bi fuel x ps body cont)
    all_goals
      rw [denoteSpine_letBind bi fuel x _ cont rfl]
      refine RefR.bind (badα := IsErr) (denote'_agree bi h.1.2 fuel) (fun o ho => ?_)
        (fun o ho s => by obtain ⟨m, rfl⟩ := ho; exact ⟨m, rfl⟩)
      unfold spineLetStep
      split
      · exact RefR.pure _
      · exact RefR.modify_ext (fun _ _ w hR => hR.extend _ w) fun _ => ihc bi fuel h.2
      · exact RefR.pure _
  | seq a b iha ihb =>
    intro bi fuel h
    simp only [frameOk, Bool.and_eq_true] at h
    rw [denoteSpine_seq]
    refine RefR.bind (badα := IsErr) (denote'_agree bi h.1 fuel) (fun o ho => ?_)
      (fun o ho s => by obtain ⟨m, rfl⟩ := ho; exact ⟨m, rfl⟩)
    unfold spineSeqStep
    split
    · exact RefR.pure _
    · exact ihb bi fuel h.2
    · exact RefR.pure _
  | _ =>
    intro bi fuel h
    simp only [denoteSpine]
    exact denote'_agree bi h fuel

/-! ## The values of the constants -/

/-- The value of an outcome that is a value and no control-flow value. -/
def outVal : Outcome → Option Value
  | .val (.controlFlow _ _) => none
  | .val v => some v
  | _ => none

/-- An outcome has the value `v` exactly when it is `v` and `v` is no control-flow value. -/
theorem outVal_eq_some {o : Outcome} {v : Value} :
    outVal o = some v ↔ o = .val v ∧ v.isControlFlow = false := by
  rcases o with w | _ | _ | _ | _
  · cases w <;> grind [outVal, Value.isControlFlow]
  all_goals simp [outVal]

/-- A run that refines itself under agreement has one value. -/
theorem outVal_congr {rd : String → Bool} {m : StateM Env Outcome}
    (h : RefE (AgreeOn rd) m m) {a b : Env} (hR : AgreeOn rd a b) :
    outVal (m.run a).1 = outVal (m.run b).1 := by
  rcases outcome_eq_of_ref h hR with ⟨⟨_, h₁⟩, _, h₂⟩ | h' <;> simp [*, outVal]

/-- **The values of the constants `cs`**, each the value of its body in the environment of the
    constants before it, added to `env`. The environment in which a body ends is discarded,
    so its bindings are local to it. The result is `none` when a body denotes no value. -/
def constsEnv (bi : Builtins) (fuel : Nat) : List (String × TExpr) → Env → Option Env
  | [], env => some env
  | c :: cs, env =>
    (outVal ((denote' bi fuel (constBody c.2)).run env).1).bind fun v =>
      constsEnv bi fuel cs (env.extend c.1 v)

/-- The environment `env` holds at each constant of `cs` the value its body denotes. -/
def ConstsHold (bi : Builtins) (fuel : Nat) (cs : List (String × TExpr)) (env : Env) : Prop :=
  ∀ c ∈ cs, ∃ v, env c.1 = some v ∧
    outVal ((denote' bi fuel (constBody c.2)).run env).1 = some v

/-- An environment that holds the constants is the environment of their values. -/
theorem constsEnv_of_holds (bi : Builtins) (fuel : Nat) : ∀ {cs} {env : Env},
    ConstsHold bi fuel cs env → constsEnv bi fuel cs env = some env
  | [], _, _ => by simp [constsEnv]
  | c :: cs, env, h => by
    obtain ⟨v, hk, hv⟩ := h c List.mem_cons_self
    simp only [constsEnv, hv, Option.bind_some, extend_of_eq hk]
    exact constsEnv_of_holds bi fuel fun d hd => h d (List.mem_cons_of_mem _ hd)

/-- **The environment of the values holds each constant at the value its body denotes.** -/
theorem constsEnv_holds (bi : Builtins) (fuel : Nat) {excl : List String} {e : ImpExpr} :
    ∀ {cs} {env ρ : Env}, scopedB excl e cs = true → constsEnv bi fuel cs env = some ρ →
      ConstsHold bi fuel cs ρ ∧ ∀ x, cs.any (·.1 == x) = false → ρ x = env x
  | [], env, ρ, _, h => by
    simp only [constsEnv, Option.some.injEq] at h
    subst h
    simp [ConstsHold]
  | c :: cs, env, ρ, hs, h => by
    simp only [scopedB, scopeOk, Bool.and_eq_true] at hs
    simp only [constsEnv, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨hH, hoff⟩ := constsEnv_holds bi fuel hs.2 h
    obtain ⟨⟨⟨⟨⟨-, -⟩, hk⟩, hb⟩, -⟩, -⟩ := hs
    refine ⟨fun d hd => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      · refine ⟨v, by rw [hoff _ (by simpa using hk), Env.extend_same], ?_⟩
        rw [outVal_congr (denote'_agree bi hb fuel) (b := env) fun x hx => ?_]
        · exact hv
        · simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hx
          rw [hoff x hx.2, Env.extend_other _ _ _ _ hx.1.2]
      · exact hH d hd
    · simp only [List.any_cons, Bool.or_eq_false_iff] at hx
      rw [hoff x hx.2, Env.extend_other _ _ _ _ (by grind)]

/-- The environment `env` over the environment `ρ`: the binding of `env`, else that of `ρ`. -/
def overlay (env ρ : Env) : Env := fun x => (env x).or (ρ x)

/-- An environment over the empty environment is itself. -/
theorem overlay_empty (env : Env) : overlay env Env.empty = env := by
  funext x
  simp [overlay, Env.empty]

/-- A binding at a name free in the upper environment is a binding in the lower one. -/
theorem overlay_extend {env : Env} (ρ : Env) {k : String} (v : Value) (h : env k = none) :
    (overlay env ρ).extend k v = overlay env (ρ.extend k v) := by
  funext x
  by_cases hx : x = k <;> simp [overlay, Env.extend, hx, h]

/-- The values of constants in scope do not depend on the parameters. -/
theorem constsEnv_overlay (bi : Builtins) (fuel : Nat) {excl : List String} {e : ImpExpr}
    {env : Env} (henv : ∀ x, x ∉ excl → env x = none) : ∀ {cs} (ρ : Env),
    scopedB excl e cs = true →
      constsEnv bi fuel cs (overlay env ρ) = (constsEnv bi fuel cs ρ).map (overlay env)
  | [], ρ, _ => by simp [constsEnv]
  | c :: cs, ρ, hs => by
    simp only [scopedB, scopeOk, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨-, hk⟩, -⟩, hb⟩, -⟩, hs⟩ := hs
    simp only [constsEnv]
    rw [outVal_congr (denote'_agree bi hb fuel) (b := ρ) fun x hx => ?_]
    · cases outVal ((denote' bi fuel (constBody c.2)).run ρ).1 with
      | none => simp
      | some v =>
        simp only [Option.bind_some, overlay_extend ρ v (henv c.1 (by simpa using hk))]
        exact constsEnv_overlay bi fuel henv _ hs
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
      simp [overlay, henv x (by simpa using hx.1.1)]

/-! ## The source theorem -/

/-- The run of a binding on the statement spine. -/
theorem run_spineLet (bi : Builtins) (fuel : Nat) (k : String) (b r : ImpExpr)
    (hl : isLamE b = false) (env : Env) :
    (denoteSpine bi fuel (.letBind k b r)).run env =
      (spineLetStep k ((denote' bi fuel b).run env).1 (denoteSpine bi fuel r)).run
        ((denote' bi fuel b).run env).2 := by
  rw [denoteSpine_letBind bi fuel k b r hl]
  rfl

/-- The step of a binding after a value. -/
theorem spineLetStep_some {o : Outcome} {v : Value} (h : outVal o = some v) (k : String)
    (m : StateM Env Outcome) (s : Env) :
    (spineLetStep k o m).run s = m.run (s.extend k v) := by
  obtain ⟨rfl, hv⟩ := outVal_eq_some.1 h
  cases v <;> first | rfl | simp at hv

/-- The step of a binding after an outcome without a value has no value. -/
theorem spineLetStep_none {o : Outcome} (h : outVal o = none) (k : String)
    (m : StateM Env Outcome) (s : Env) : outVal ((spineLetStep k o m).run s).1 = none := by
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> first | rfl | simp [outVal] at h

/-- The frame of bound bodies is that of the bodies and of the expression. -/
theorem frameOk_bindE {rd : String → Bool} {e : ImpExpr}
    (he : frameOk rd (fun _ => true) (fun _ => true) e = true) : ∀ {cs : List (String × TExpr)},
    (∀ d ∈ cs, frameOk rd (fun _ => true) (fun _ => true) (constBody d.2) = true) →
      frameOk rd (fun _ => true) (fun _ => true) (bindE cs e) = true
  | [], _ => by simpa [bindE] using he
  | d :: cs, h => by
    simp [bindE, frameOk, h d List.mem_cons_self,
      frameOk_bindE he fun d' hd => h d' (List.mem_cons_of_mem _ hd)]

/-- **The bound bodies read as the constants in scope**: from every environment, the value of
    the bound expression is the value of the expression from the environment of the values of
    the constants, and there is none when a body denotes none. -/
theorem run_bindE (bi : Builtins) (fuel : Nat) {excl : List String} {e : ImpExpr} :
    ∀ {cs}, scopedB excl e cs = true → ∀ env : Env,
      outVal ((denoteSpine bi fuel (bindE cs e)).run env).1 =
        (constsEnv bi fuel cs env).bind fun ρ => outVal ((denoteSpine bi fuel e).run ρ).1
  | [], _, env => by simp [bindE, constsEnv]
  | c :: cs, hs, env => by
    simp only [scopedB, scopeOk, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at hs
    obtain ⟨⟨⟨⟨⟨hl, -⟩, -⟩, hb⟩, hW⟩, hs⟩ := hs
    simp only [bindE, constsEnv, run_spineLet bi fuel _ _ _ hl]
    generalize hr : (denote' bi fuel (constBody c.2)).run env = r
    cases hv : outVal r.1 with
    | none => simp [spineLetStep_none hv]
    | some v =>
      rw [spineLetStep_some hv, Option.bind_some, ← run_bindE bi fuel hs (env.extend c.1 v)]
      have hw := denote'_writes bi fuel hb (o := r.1) (s := r.2) hr
        (by obtain ⟨h, -⟩ := outVal_eq_some.1 hv; simp [IsErr, h])
      rcases hW with hW | ⟨he, hds⟩
      · have : r.2 = env := funext fun x => hw x (by simp [List.isEmpty_iff.1 hW])
        rw [this]
      · exact outVal_congr (denoteSpine_frame _ bi fuel (frameOk_bindE he hds))
          (AgreeOn.extend (fun x hx => hw x (by simpa using hx)) _ _)

/-- **The bound extraction reads as the extraction, exactly**, when no bound body binds a
    name: from an environment that holds each constant at the value its body denotes, the
    outcome and the final environment are those of the extraction. -/
theorem run_bindBodies (bi : Builtins) (fuel : Nat) (te : TExpr) :
    ∀ (cs : List (String × TExpr)) (env : Env), (∀ c ∈ cs, bindFree c = true) →
      ConstsHold bi fuel cs env →
      (denoteSpine bi fuel (bindBodies cs te).erase).run env =
        (denoteSpine bi fuel te.erase).run env := by
  intro cs env hb h
  rw [erase_bindBodies]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hb' := hb c List.mem_cons_self
    simp only [bindFree, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at hb'
    obtain ⟨v, hk, hv⟩ := h c List.mem_cons_self
    have hs : ((denote' bi fuel (constBody c.2)).run env).2 = env := funext fun x =>
      denote'_writes bi fuel hb'.2 (Prod.mk.eta).symm
        (by obtain ⟨h', -⟩ := outVal_eq_some.1 hv; simp [IsErr, h']) x (by simp [hb'.1.2])
    simp only [bindE, run_spineLet bi fuel _ _ _ hb'.1.1, spineLetStep_some hv, hs,
      extend_of_eq hk]
    exact ih (fun d hd => hb d (List.mem_cons_of_mem _ hd)) fun d hd =>
      h d (List.mem_cons_of_mem _ hd)

/-- **The pre-pass reads as the extraction, exactly**, when no bound body binds a name. -/
theorem run_bindClosed_eq (bi : Builtins) (fuel : Nat) (excl : List String)
    (consts : List (String × TExpr)) (te : TExpr) (env : Env)
    (hb : ∀ c ∈ closedConsts excl consts te, bindFree c = true)
    (h : ConstsHold bi fuel (closedConsts excl consts te) env) :
    (denoteSpine bi fuel (bindClosed excl consts te).erase).run env =
      (denoteSpine bi fuel te.erase).run env :=
  run_bindBodies bi fuel te _ env hb h

/-- **The source theorem of the pre-pass.** From an environment that holds each bound
    constant at the value its body denotes, the source reading of the bound extraction has
    the value of the source reading of the extraction, also when bodies bind names. -/
theorem run_bindClosed_of_holds (bi : Builtins) (fuel : Nat) (excl : List String)
    (consts : List (String × TExpr)) (te : TExpr) (env : Env)
    (h : ConstsHold bi fuel (closedConsts excl consts te) env) :
    outVal ((denoteSpine bi fuel (bindClosed excl consts te).erase).run env).1 =
      outVal ((denoteSpine bi fuel te.erase).run env).1 := by
  rw [bindClosed, erase_bindBodies, run_bindE bi fuel (scopedB_closedConsts excl consts te),
    constsEnv_of_holds bi fuel h, Option.bind_some]

/-- **The source theorem from the parameters alone**: from an environment that binds only
    names of `excl`, the bound extraction has the value of the extraction from that
    environment over the values of the constants. -/
theorem run_bindClosed (bi : Builtins) (fuel : Nat) (excl : List String)
    (consts : List (String × TExpr)) (te : TExpr) (env : Env)
    (henv : ∀ x, x ∉ excl → env x = none) :
    outVal ((denoteSpine bi fuel (bindClosed excl consts te).erase).run env).1 =
      (constsEnv bi fuel (closedConsts excl consts te) Env.empty).bind fun ρ =>
        outVal ((denoteSpine bi fuel te.erase).run (overlay env ρ)).1 := by
  have hs := scopedB_closedConsts excl consts te
  have he := constsEnv_overlay bi fuel henv Env.empty hs
  rw [overlay_empty] at he
  rw [bindClosed, erase_bindBodies, run_bindE bi fuel hs, he]
  cases constsEnv bi fuel (closedConsts excl consts te) Env.empty <;> rfl

/-! ## The literal case -/

/-- The values of the constants with literal bodies. -/
def litVals (consts : List (String × TExpr)) : List (String × Value) :=
  consts.filterMap fun c => (bodyLit c.2.erase).map fun l => (c.1, Value.ofLit l)

/-- The literal of the value of a literal body is that literal. -/
theorem constLit_bodyLit {b : ImpExpr} {l : ImpLit} (h : bodyLit b = some l) :
    constLit (Value.ofLit l) = some l := by
  unfold bodyLit at h
  split at h <;> cases h <;> rfl

/-- A literal body denotes by a literal. -/
theorem constBody_of_lit {c : TExpr} (h : (bodyLit c.erase).isSome = true) :
    ∃ l, constBody c = .lit l := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h
  exact ⟨l, by simp [constBody, hl]⟩

/-- Literal bodies are bound as `bindConsts` binds their values. -/
theorem bindBodiesAt_literal (te : TExpr) : ∀ cs : List (String × TExpr),
    (∀ c ∈ cs, (bodyLit c.2.erase).isSome = true) →
      bindBodiesAt (texprFacts te) cs te = bindConsts (litVals cs) te
  | [], _ => by simp [bindBodiesAt, litVals, bindConsts]
  | (k, c) :: cs, h => by
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (h (k, c) List.mem_cons_self)
    have ih := bindBodiesAt_literal te cs fun d hd => h d (List.mem_cons_of_mem _ hd)
    simp only [litVals] at ih ⊢
    simp [bindBodiesAt, bindConsts, constExpr, hl, constLit_bodyLit hl, ih]

/-- Closed bodies are ordered in one round. -/
theorem closedOrder_of_ready {n : Nat} {cs : List (String × TExpr)} (hn : cs.length ≤ n)
    (h : ∀ c ∈ cs, ready [] c = true) : closedOrder n [] cs = cs := by
  rcases n with _ | n
  · simp [closedOrder, List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)]
  · have h₁ : cs.filter (ready []) = cs := List.filter_eq_self.2 h
    have h₂ : cs.filter (fun c => !ready [] c) = [] := by simpa using h
    have h₃ : ∀ n dn, closedOrder n dn [] = [] := fun n dn => by cases n <;> simp [closedOrder]
    simp only [closedOrder, h₁, h₂, h₃, List.append_nil]
    grind

/-- Of constants whose bodies read no name, `readTrim` keeps those read free. -/
theorem readTrim_of_lit (free : List String) : ∀ cs : List (String × TExpr),
    (∀ c ∈ cs, ∀ k, readsName k c = false) →
      readTrim free cs = cs.filter fun c => free.contains c.1
  | [], _ => by simp [readTrim]
  | c :: cs, h => by
    have ih := readTrim_of_lit free cs fun d hd => h d (List.mem_cons_of_mem _ hd)
    grind [readTrim]

/-- **`bindConsts` is the literal case of the pre-pass**: on constants with distinct names and
    literal bodies, the bound extraction is that of `bindConsts` on their values, at the
    names read free that no parameter binds, types included. -/
theorem bindClosed_literal (excl : List String) (consts : List (String × TExpr)) (te : TExpr)
    (hn : (consts.map (·.1)).Nodup) (hl : ∀ c ∈ consts, (bodyLit c.2.erase).isSome = true) :
    bindClosed excl consts te = bindConsts ((litVals consts).filter fun c =>
      (freeVars te.erase).contains c.1 && !excl.contains c.1) te := by
  have hlit : ∀ c ∈ consts, bindFree c = true ∧ ready [] c = true ∧
      ∀ k, readsName k c = false := fun c hc => by
    obtain ⟨l, hl⟩ := constBody_of_lit (hl c hc)
    simp [bindFree, ready, readsName, hl, isLamE, bindVars, frameOk]
  have hcand : constCands excl consts = consts.filter fun c => !excl.contains c.1 := by
    rw [constCands, firstOfName_of_nodup hn]
  have hord := closedOrder_of_ready (le_refl (constCands excl consts).length)
    (fun c hc => (hlit c (by rw [hcand] at hc; exact (List.mem_filter.1 hc).1)).2.1)
  have hsel : closedConsts excl consts te = consts.filter fun c =>
      (freeVars te.erase).contains c.1 && !excl.contains c.1 := by
    rw [closedConsts_of_bindFree, hord, hcand, readTrim_of_lit, List.filter_filter]
    · exact fun c hc => (hlit c (List.mem_filter.1 hc).1).2.2
    · rw [hord]
      intro c hc
      have := (readTrim_sublist _ _).subset hc
      rw [hcand] at this
      exact (hlit c (List.mem_filter.1 this).1).1
  have hF : constFacts (closedConsts excl consts te) te = texprFacts te := by
    rw [constFacts, List.flatMap_eq_nil_iff.2 fun c hc => by
      simp [hl c (mem_of_mem_closedConsts hc).1], List.append_nil]
  rw [bindClosed, bindBodies, hF, bindBodiesAt_literal te _ fun c hc =>
    hl c (mem_of_mem_closedConsts hc).1, hsel]
  congr 1
  simp only [litVals, List.filterMap_filter, List.filter_filterMap]
  refine List.filterMap_congr fun c _ => ?_
  cases bodyLit c.2.erase <;> grind

/-! ## The module with its constants -/

/-- A function of a module with the closed constants it reads bound at its head. -/
def bindFn (consts : List (String × TExpr)) (f : ModFn) : ModFn :=
  { f with texpr := bindClosed (f.params.map (·.1)) consts f.texpr }

/-- **The module with bound bodies**: the entry with the constants bound that no name of the
    layout binds, and each function with those that no parameter of it binds. -/
def bindModule (consts : List (String × TExpr)) (σ : AbiLayout) (m : HaxModule) : HaxModule :=
  { m with
    entry := bindClosed σ.envNames consts m.entry
    fns := m.fns.map (bindFn consts) }

/-- **The reference table of functions with constants**: as `refBi`, where the body of a
    function runs from its parameters over the values of the constants it reads, each the
    value of its body at the same table. -/
def refBiC (consts : List (String × TExpr)) (fs : List ModFn) (bi : Builtins) (fuel : Nat) :
    Nat → Builtins
  | 0, g, vals =>
      match fs.find? (·.name == g) with
      | some _ => none
      | none => bi g vals
  | n + 1, g, vals =>
      match fs.find? (·.name == g) with
      | some f =>
          ((constsEnv (refBiC consts fs bi fuel n) fuel
              (closedConsts (f.params.map (·.1)) consts f.texpr) Env.empty).bind fun ρ =>
            outVal ((denoteSpine (refBiC consts fs bi fuel n) fuel f.texpr.erase).run
              (overlay (paramsEnv (f.params.map (·.1)) vals) ρ)).1).bind fun v =>
                if (dec f.res v).isSome then some v else none
      | none => bi g vals

/-- The table of a module with constants, over its linked functions. -/
def tableC (consts : List (String × TExpr)) (m : HaxModule) (bi : Builtins) (fuelC : Nat) :
    Builtins :=
  refBiC consts m.fns (m.linkTable bi) fuelC m.depth

/-- The environment of the parameters binds no other name. -/
theorem paramsEnv_eq_none :∀ {ps : List String} (vals : List Value) {x : String},
    x ∉ ps → paramsEnv ps vals x = none
  | [], _, _, _ => by simp [paramsEnv]
  | _ :: _, [], _, _ => by simp [paramsEnv]
  | p :: ps, v :: vs, x, h => by
    simp only [List.mem_cons, not_or] at h
    simp [paramsEnv, h.1, paramsEnv_eq_none vs h.2]

/-- The answer of a reference table depends only on the value of the outcome. -/
theorem decode_outVal (o : Outcome) (t : CatCrypt.Crypto.SecureCompilation.VIR.NFDialect.NfTy) :
    (match o with
      | .val v => if (dec t v).isSome then some v else none
      | _ => none) = (outVal o).bind fun v => if (dec t v).isSome then some v else none := by
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> try rfl
  simp [outVal, CatCrypt.Crypto.Hax.dec_controlFlow]

/-- **The table of the functions with bound bodies is the table of the functions with
    constants**, at every depth. -/
theorem refBi_bindFn (consts : List (String × TExpr)) (fs : List ModFn) (bi : Builtins)
    (fuel : Nat) : ∀ n, refBi (fs.map (bindFn consts)) bi fuel n = refBiC consts fs bi fuel n := by
  have hf : ∀ g, (fs.map (bindFn consts)).find? (·.name == g) =
      (fs.find? (·.name == g)).map (bindFn consts) := fun g => by
    rw [List.find?_map]
    rfl
  intro n
  induction n with
  | zero =>
    funext g vals
    simp only [refBi, refBiC, hf]
    cases fs.find? (·.name == g) <;> rfl
  | succ n ih =>
    funext g vals
    simp only [refBi, refBiC, hf, ih]
    cases fs.find? (·.name == g) with
    | none => rfl
    | some f =>
      simp only [Option.map_some, bindFn]
      refine (decode_outVal _ f.res).trans ?_
      rw [run_bindClosed _ _ _ _ _ _ fun x hx => paramsEnv_eq_none vals hx]

/-- The table of the module with bound bodies is the table of the module with constants. -/
theorem table_bindModule (consts : List (String × TExpr)) (σ : AbiLayout) (m : HaxModule)
    (bi : Builtins) (fuelC : Nat) :
    (bindModule consts σ m).table bi fuelC = tableC consts m bi fuelC :=
  refBi_bindFn consts m.fns (m.linkTable bi) fuelC m.depth

/-- The pre-pass keeps the entry state the source reads. -/
theorem narrowEntry_bindModule (consts : List (String × TExpr)) (σ : AbiLayout) (m : HaxModule)
    (sa : AState) : narrowEntry (bindModule consts σ m) σ sa = narrowEntry m σ sa := by
  simp only [narrowEntry, narrowOk, bindModule, List.all_map]
  rfl

/-- **The source semantics of a module with the constants of its crate**: `haxRuns`, where
    the bound constants hold the values of their bodies (`constsEnv`), in the entry and in
    each function the entry calls (`tableC`). -/
def haxRunsC (consts : List (String × TExpr)) (σ : AbiLayout) (m : HaxModule) (sa : AState)
    (v : Value) : Prop :=
  ∃ env fuel fuelC ρ env', σ.EnvOf (narrowEntry m σ sa) env ∧
    constsEnv (tableC consts m hax64WExit fuelC) fuel (closedConsts σ.envNames consts m.entry)
      Env.empty = some ρ ∧
    (denoteSpine (tableC consts m hax64WExit fuelC) fuel m.entry.erase).run (overlay env ρ) =
      (.val v, env') ∧ v.isControlFlow = false

/-- **The source of a module with its constants is the source of the module with bound
    bodies**, at every module, layout and constant list. -/
theorem haxRuns_bindModule (consts : List (String × TExpr)) (σ : AbiLayout) (m : HaxModule)
    (sa : AState) (v : Value) :
    haxRuns σ (bindModule consts σ m) sa v ↔ haxRunsC consts σ m sa v := by
  simp only [haxRuns, haxRunsW, HaxModule.Runs, narrowEntry_bindModule, table_bindModule,
    haxRunsC]
  have key : ∀ env fuel fuelC, σ.EnvOf (narrowEntry m σ sa) env →
      outVal ((denoteSpine (tableC consts m hax64WExit fuelC) fuel
        (bindClosed σ.envNames consts m.entry).erase).run env).1 =
      (constsEnv (tableC consts m hax64WExit fuelC) fuel
        (closedConsts σ.envNames consts m.entry) Env.empty).bind fun ρ =>
        outVal ((denoteSpine (tableC consts m hax64WExit fuelC) fuel m.entry.erase).run
          (overlay env ρ)).1 := fun env fuel fuelC henv =>
    run_bindClosed _ _ _ _ _ _ fun x hx => by
      cases he : env x with
      | none => rfl
      | some w => exact absurd (henv.2.2 x (by simp [he])) hx
  constructor
  · rintro ⟨env, fuel, fuelC, env', henv, hr, hv⟩
    have hk := key env fuel fuelC henv
    simp only [bindModule] at hr
    rw [hr, outVal_eq_some.2 ⟨rfl, hv⟩, eq_comm, Option.bind_eq_some_iff] at hk
    obtain ⟨ρ, hρ, ho⟩ := hk
    exact ⟨env, fuel, fuelC, ρ, _, henv, hρ, Prod.ext (outVal_eq_some.1 ho).1 rfl, hv⟩
  · rintro ⟨env, fuel, fuelC, ρ, env', henv, hρ, hr, hv⟩
    have hk := key env fuel fuelC henv
    rw [hρ, Option.bind_some, hr, outVal_eq_some.2 ⟨rfl, hv⟩] at hk
    exact ⟨env, fuel, fuelC, _, henv, Prod.ext (outVal_eq_some.1 hk).1 rfl, hv⟩

section Correct

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.Hax (LinkedFn)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (tabOracle LinkedKernel)
open CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes (HaltsIn)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-- **The compiler theorem on a module with the constants of its crate.** When `compileA`
    returns bytes on the module with bound bodies, every run of the source with its constants
    (`haxRunsC`), constants read by callees included, is read back with the conclusion of
    `haxc_correct_auto_access`. -/
theorem haxc_correct_closed (consts : List (String × TExpr)) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA (bindModule consts σ m) σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : haxRunsC consts σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) :=
  haxc_correct_auto_access (bindModule consts σ m) σ fname P bytes hc sa hsep v
    ((haxRuns_bindModule consts σ m sa v).2 hrun) hnd hk

end Correct

/-! ## The functions of a module from their extractions -/

/-- **The function of a module named `name` with the extraction `te`, in a crate with the
    constants `consts`**: `te` with the parameters and the result type `ModFn.ofTExprE` reads
    off it, its constants unbound, when `te` with the closed constants bound reads no free
    name that is not a parameter; otherwise the refusal of `ModFn.ofTExprE`. The module that
    `compileA` reads is `bindModule` of the module of these functions. -/
def closedFnE (consts : List (String × TExpr)) (name : String) (te : TExpr) :
    Except ModuleRefusal ModFn :=
  let ps := texprPrelude 64 te
  let te' := bindClosed (ps.map (·.1)) consts te
  match modFnParamsE ps with
  | .error x => .error (.calleeShape name s!"parameter {x} has a type outside the domain")
  | .ok params =>
      match modFnTy te.ty with
      | none => .error (.calleeShape name "the result has a type outside the domain")
      | some r =>
          if (freeVars te'.erase).all fun x => ps.any (·.1 == x) then
            .ok ⟨name, params, r, te⟩
          else
            .error (.calleeShape name s!"free name {(((freeVars te'.erase).find?
              fun x => !ps.any (·.1 == x)).getD "")}")

/-- The functions `closedFnE` makes of the extractions `gs`, or the first refusal. -/
def closedFnsE (consts : List (String × TExpr)) (gs : List (String × TExpr)) :
    Except ModuleRefusal (List ModFn) :=
  gs.mapM fun g => closedFnE consts g.1 g.2

/-- `modFnParamsE` keeps the names of the parameters. -/
theorem map_fst_modFnParamsE :∀ {ps : List (String × _root_.Hax.ImpType)}
    {qs : List (String × CatCrypt.Crypto.SecureCompilation.VIR.NFDialect.NfTy)},
    modFnParamsE ps = .ok qs → qs.map (·.1) = ps.map (·.1)
  | [], qs, h => by
    simp only [modFnParamsE, Except.ok.injEq] at h
    simp [← h]
  | p :: ps, qs, h => by
    unfold modFnParamsE at h
    split at h
    · cases hq : modFnParamsE ps with
      | error x => simp [hq, Except.map] at h
      | ok qs' =>
        simp only [hq, Except.map, Except.ok.injEq] at h
        simp [← h, map_fst_modFnParamsE hq]
    · cases h

/-- **`ModFn.ofTExprE` is the literal case**: on constants with distinct names and literal
    bodies, `closedFnE` followed by the binding gives the function or the refusal of
    `ModFn.ofTExprE` on their values. -/
theorem closedFnE_literal (consts : List (String × TExpr)) (name : String) (te : TExpr)
    (hn : (consts.map (·.1)).Nodup) (hl : ∀ c ∈ consts, (bodyLit c.2.erase).isSome = true) :
    (closedFnE consts name te).map (bindFn consts) =
      ModFn.ofTExprE name te (litVals consts) := by
  have hb : bindClosed ((texprPrelude 64 te).map (·.1)) consts te =
      bindConsts ((litVals consts).filter fun c =>
        (freeVars te.erase).eraseDups.contains c.1 &&
          !(texprPrelude 64 te).any (·.1 == c.1)) te := by
    rw [bindClosed_literal _ _ _ hn hl]
    congr 1
    refine List.filter_congr fun c _ => ?_
    grind [List.mem_eraseDups]
  unfold closedFnE ModFn.ofTExprE
  simp only [← hb]
  cases hp : modFnParamsE (texprPrelude 64 te) with
  | error x => rfl
  | ok params =>
    cases modFnTy te.ty with
    | none => rfl
    | some r =>
      simp only
      split
      · simp [Except.map, bindFn, map_fst_modFnParamsE hp]
      · rfl

/-- **`modFnsE` is the literal case**: on constants with distinct names and literal bodies,
    `closedFnsE` followed by the bindings gives the functions or the refusal of `modFnsE`. -/
theorem closedFnsE_literal (consts : List (String × TExpr)) (gs : List (String × TExpr))
    (hn : (consts.map (·.1)).Nodup) (hl : ∀ c ∈ consts, (bodyLit c.2.erase).isSome = true) :
    (closedFnsE consts gs).map (List.map (bindFn consts)) = modFnsE (litVals consts) gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [closedFnsE, List.mapM_cons, modFnsE, ← ih, ← closedFnE_literal consts g.1 g.2 hn hl]
    cases closedFnE consts g.1 g.2 with
    | error x => rfl
    | ok f => cases gs.mapM (fun g => closedFnE consts g.1 g.2) <;> rfl

/-! ## An instance -/

section Instance

/-- The constants of the instance: `B` reads `A`, whose body is `repeat(0, 4)`, and stands
    before it. -/
def exConsts : List (String × TExpr) :=
  let τ : _root_.Hax.ImpType := .array (.uint .w64) 4
  [("B", .mk (.tuple [.mk (.var "A") τ, .mk (.var "A") τ]) (.tuple [τ, τ])),
    ("A", .mk (.app "repeat"
      [.mk (.lit (.int 0)) (.uint .w64), .mk (.lit (.int 4)) (.uint .wsize)]) τ)]

/-- The entry of the instance reads `B`. -/
def exEntry : TExpr :=
  let τ : _root_.Hax.ImpType := .array (.uint .w64) 4
  .mk (.var "B") (.tuple [τ, τ])

/-- The layout of the instance has no parameter. -/
def exLayout : AbiLayout := AbiLayout.mk [] [] (.reg "%rax") [] (-256) (-8) [] []

/-- A test of the pre-pass: on the instance it binds `A` before `B`. -/
theorem closedConsts_ex :
    closedConsts exLayout.envNames exConsts exEntry = exConsts.reverse := by
  rfl

/-- **The hypothesis of `haxc_correct_closed` has an instance**: from every entry state the
    source with the constants of the instance runs to the pair of the array of four zeros. -/
theorem haxRunsC_ex (sa : AState) :
    haxRunsC exConsts exLayout exEntry sa
      (.tuple [.array (List.replicate 4 (.int 0)), .array (List.replicate 4 (.int 0))]) := by
  have hrep : hax64WExit "repeat" [.int 0, .int 4] =
      some (.array (List.replicate 4 (.int 0))) := by rfl
  let a : Value := .array (List.replicate 4 (.int 0))
  let ρ : Env := (Env.empty.extend "A" a).extend "B" (.tuple [a, a])
  refine ⟨Env.empty, 0, 0, ρ, overlay Env.empty ρ, ?_, ?_, ?_, rfl⟩
  · simp [AbiLayout.EnvOf, exLayout, Env.empty]
  · change constsEnv hax64WExit 0 (closedConsts exLayout.envNames exConsts exEntry) Env.empty = _
    rw [closedConsts_ex]
    simp [exConsts, constsEnv, constBody, bodyLit, _root_.Hax.TExpr.erase, denote',
      _root_.Hax.denoteApp', _root_.Hax.denoteArgs', hrep, outVal, StateT.run, bind, StateT.bind,
      pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, Value.ofLit, Env.extend, ρ, a]
  · simp [tableC, HaxModule.single, refBiC, HaxModule.linkTable, CatCrypt.Crypto.Hax.linkBi_nil,
      exEntry, _root_.Hax.TExpr.erase, denoteSpine, denote', StateT.run, bind, StateT.bind, pure,
      StateT.pure, get, getThe, MonadStateOf.get, StateT.get, overlay, Env.empty, Env.extend,
      ρ, a]

end Instance

end CatCrypt.Crypto.SecureCompilation.Haxc.ClosedConsts
