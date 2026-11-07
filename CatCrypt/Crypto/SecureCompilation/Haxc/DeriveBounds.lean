/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import HaxLean.TExpr

@[expose] public section

set_option autoImplicit false

/-!
# The parts of a derived layout read off the body of an extraction

The layout `Census.deriveAbi` reads off the parameter prelude and the result type of an
extraction. This module gives it two readings of the body.

* **The result type.** The extraction may leave the node type of a binding or a sequence of the
  statement spine unknown; the type of `let x = v; c` and of `a; c` is the type of `c`, so the
  result type is read at the first node of the spine with a known type (`spineTy`). Where the
  root type is known the reading is the root type (`spineTy_of_ne_unknown`), so no layout the
  derivation gave before changes.
* **The bounds of the runtime counts.** A scalar parameter `p` that is the upper bound of a
  counted loop `for i in lo..p` on the statement spine, whose body leaves no trip early and
  indexes an array variable of known length `L` at `i + c` on every trip, bounds the trips: a
  trip `i = max lo (L - c)` exists when `p > max lo (L - c)` and its access at `L` or beyond is
  out of range, which the source semantics makes a panic. The same holds for an access at `p`
  itself on the spine (`p ≤ L - 1`). `capsOf K p e` lists these caps and `deriveBounds` binds
  each scalar parameter with a cap to the least of them. Only accesses every trip reaches count:
  the strict part of the body (`strictCaps`), up to the first node that may leave the trip early
  (`cfFree`), and never under a conditional or an inner loop, whose accesses some runs do not
  reach.

  The semantics threads one environment through every node, so a binding inside a node
  outlives it. The walk therefore reads the length of an array from a table `K` of names whose
  length it knows, not from the type annotation of the node: at the root the array parameters
  of the layout (`arrLens`), less every name a head binds (`writes`, `dropW`, `bindK`); in a
  loop body, less the counter and every name the body binds. It stops at a head that binds the
  counter or `p` other than by `let p = p`. A loop counts only when its whole body leaves no trip
  early, since a trip that breaks before the access ends the loop.

## Soundness

A layout is an input of the compiler, not part of its trusted base: the correctness and
constant-time theorems of `compileA` (`haxc_correct_auto`, `haxc_ct_proved_all`) hold at every
layout, so a derived layout cannot make a compiled function wrong; it fixes the entry states of
the theorem. A bound is a precondition on the caller (`AbiLayout.Regions`) and makes its
parameter public (`AbiLayout.argPub`); a loop bound is leaked by the trip count already, and the
level check refuses a secret one. A derived bound excludes no entry state at which the source
has a run with a value (`deriveAbi_bounds_hold` in `DeriveBoundsSound`).

## Main results

* `spineTy`, `spineTy_of_ne_unknown` — the result type read off the spine.
* `writes`, `dropW`, `bindK`, `arrLens` — the names a node binds and the table of known lengths.
* `strictCaps`, `capsOf` — the caps of the accesses that bound a counted loop over `p`.
* `deriveBounds`, `mem_deriveBounds` — the bound of each scalar parameter with a cap, on its
  register; each derived bound is the least cap of its parameter (`deriveBounds_le_cap`).
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds

open _root_.Hax (TExpr TExprKind ImpType ImpLit)

/-- The type `t`, or `k ()` where `t` is unknown. -/
def knownOr (t : ImpType) (k : Unit → ImpType) : ImpType :=
  match t with
  | .unknown => k ()
  | t => t

/-- **The result type of a body read off its statement spine**: the node type, or, where the
    extraction leaves the type of a binding or a sequence unknown, the type of its
    continuation. -/
def spineTy : TExpr → ImpType
  | .mk (.letBind _ _ c) t => knownOr t fun _ => spineTy c
  | .mk (.seq _ b) t => knownOr t fun _ => spineTy b
  | .mk _ t => t

/-- Where the root type is known, `spineTy` is the root type. -/
theorem spineTy_of_ne_unknown {te : TExpr} (h : te.ty ≠ .unknown) : spineTy te = te.ty := by
  obtain ⟨k, t⟩ := te
  have ht : knownOr t = fun _ => t := by
    funext _
    cases t <;> first | rfl | exact absurd rfl h
  cases k <;> simp only [spineTy, ht, TExpr.ty]

/-- The checked additions of the call typing, whose overflow is a panic. -/
def checkedAdd (f : String) : Bool := f == "Add" || f == "Add#size" || f == "Add#64"

/-- The offset of an index from the counter `i`: `0` at `i`, `c` at a checked `i + c`. -/
def ctrOff? (i : String) : TExpr → Option Nat
  | .mk (.var x) _ => if x == i then some 0 else none
  | .mk (.app f [.mk (.var x) _, .mk (.lit (.int c)) _]) _ =>
      if x == i && checkedAdd f && decide (0 ≤ c) then some c.toNat else none
  | _ => none

/-- The array operand and the index operand of an access: `index(a, e)` and
    `array_update(a, e, v)`. -/
def access? : TExpr → Option (TExpr × TExpr)
  | .mk (.app "index" [a, e]) _ => some (a, e)
  | .mk (.app "array_update" [a, e, _]) _ => some (a, e)
  | _ => none

/-- The name of a variable node. -/
def varNodeName? : TExpr → Option String
  | .mk (.var x) _ => some x
  | _ => none

/-- The cap of an access at offset `c` from the counter `i` into the array variable `x` of
    length `L` in the table of lengths `K`: `L - c`, the number of trips before the access
    leaves the array. -/
def siteCap? (K : List (String × Nat)) (i : String) (e : TExpr) : Option Nat := do
  let (a, ix) ← access? e
  let x ← varNodeName? a
  let l ← List.lookup x K
  let c ← ctrOff? i ix
  pure (l - c)

mutual

/-- A node that leaves no trip early: literals, names, the unit value, calls, tuples,
    bindings, sequences, conditionals and counted loops of such nodes. A node of any other
    kind may produce a control-flow value. -/
def cfFree : TExpr → Bool
  | .mk (.lit _) _ | .mk (.var _) _ | .mk .unitVal _ => true
  | .mk (.app _ args) _ => cfFreeList args
  | .mk (.tuple es) _ => cfFreeList es
  | .mk (.letBind _ v c) _ => cfFree v && cfFree c
  | .mk (.seq a b) _ => cfFree a && cfFree b
  | .mk (.ifThenElse c a b) _ => cfFree c && cfFree a && cfFree b
  | .mk (.forFold _ lo hi b) _ => cfFree lo && cfFree hi && cfFree b
  | .mk (.ann e) _ => cfFree e
  | _ => false

/-- `cfFree` of every member of a list. -/
def cfFreeList : List TExpr → Bool
  | [] => true
  | e :: es => cfFree e && cfFreeList es

end

mutual

/-- **The names a node may bind**: the names of its bindings and the counters of its loops.
    The semantics threads the environment through every node, so a binding inside a node
    outlives it; on a node with `cfFree` these are the only names its run changes
    (`cfFree_run` in `DeriveBoundsSound`). -/
def writes : TExpr → List String
  | .mk (.app _ args) _ => writesList args
  | .mk (.tuple es) _ => writesList es
  | .mk (.letBind x v c) _ => x :: (writes v ++ writes c)
  | .mk (.seq a b) _ => writes a ++ writes b
  | .mk (.ifThenElse c a b) _ => writes c ++ (writes a ++ writes b)
  | .mk (.forFold i lo hi b) _ => i :: (writes lo ++ (writes hi ++ writes b))
  | .mk (.ann e) _ => writes e
  | _ => []

/-- `writes` of the members of a list. -/
def writesList : List TExpr → List String
  | [] => []
  | e :: es => writes e ++ writesList es

end

/-- The table of array lengths `K` without the names `ws`. -/
def dropW (K : List (String × Nat)) (ws : List String) : List (String × Nat) :=
  K.filter fun q => !ws.contains q.1

mutual

/-- **The caps of the accesses every trip reaches** in a loop body with counter `i`, for the
    array variables of known length in `K`: the accesses at an offset from `i` in the strict
    part of the body, the arguments of calls, the members of tuples, the bound values and
    the continuations of bindings and sequences whose head leaves no trip early and binds
    neither `i` nor a name the continuation reads at a known length, and the condition of a
    conditional; not the arms of a conditional nor the body of an inner loop. -/
def strictCaps (K : List (String × Nat)) (i : String) : TExpr → List Nat
  | .mk (.app f args) t =>
      (siteCap? K i (.mk (.app f args) t)).toList ++ strictCapsList K i args
  | .mk (.tuple es) _ => strictCapsList K i es
  | .mk (.letBind x v c) _ =>
      strictCaps K i v ++
        (if cfFree v && x != i && !(writes v).contains i then
          strictCaps (dropW K (x :: writes v)) i c else [])
  | .mk (.seq a b) _ =>
      strictCaps K i a ++
        (if cfFree a && !(writes a).contains i then strictCaps (dropW K (writes a)) i b
        else [])
  | .mk (.ifThenElse c _ _) _ => strictCaps K i c
  | .mk (.ann e) _ => strictCaps K i e
  | _ => []

/-- `strictCaps` of the members of a list, each evaluated in turn. -/
def strictCapsList (K : List (String × Nat)) (i : String) : List TExpr → List Nat
  | [] => []
  | e :: es =>
      strictCaps K i e ++
        (if cfFree e && !(writes e).contains i then strictCapsList (dropW K (writes e)) i es
        else [])

end

/-- The binding `let x = x`. -/
def selfBind (x : String) : TExpr → Bool
  | .mk (.var y) _ => y == x
  | _ => false

/-- The table of lengths after the binding `let x = v`: unchanged at `let x = x`, otherwise
    without `x` and the names `v` binds. -/
def bindK (K : List (String × Nat)) (x : String) (v : TExpr) : List (String × Nat) :=
  if selfBind x v then K else dropW K (x :: writes v)

/-- **The caps of a head of the spine for the parameter `p`**, for the array variables of
    known length in `K`: at a counted loop `for i in lo..p` with a nonnegative literal `lo`
    whose body leaves no trip early, the caps of its body, for the lengths the body keeps,
    each raised to `lo`; at an access of an array variable of known length whose index is
    `p`, the length less one. -/
def headCaps (K : List (String × Nat)) (p : String) : TExpr → List Nat
  | .mk (.forFold i (.mk (.lit (.int lo)) _) (.mk (.var q) _) b) _ =>
      if q == p && decide (0 ≤ lo) && cfFree b then
        (strictCaps (dropW K (i :: writes b)) i b).map (max lo.toNat)
      else []
  | e =>
      match access? e with
      | some (a, .mk (.var q) _) =>
          if q == p then
            (((varNodeName? a).bind fun x => List.lookup x K).map (· - 1)).toList
          else []
      | _ => []

/-- **The caps of the parameter `p` along the statement spine** of a body, for the array
    variables of known length in `K`: the caps of each head (`headCaps`), up to the first head
    that may leave the body early or binds `p` other than by `let p = p`. -/
def capsOf (K : List (String × Nat)) (p : String) : TExpr → List Nat
  | .mk (.letBind x v c) _ =>
      headCaps K p v ++
        (if cfFree v && (x != p || selfBind x v) && !(writes v).contains p then
          capsOf (bindK K x v) p c else [])
  | .mk (.seq a b) _ =>
      headCaps K p a ++
        (if cfFree a && !(writes a).contains p then capsOf (dropW K (writes a)) p b else [])
  | e => headCaps K p e

/-- The array parameters with their lengths in words. -/
def arrLens (args : List AbiArg) : List (String × Nat) :=
  args.filterMap fun a =>
    match a.kind with
    | .words n => some (a.name, n)
    | .scalar => none

/-- The least member of a nonempty list. -/
def minCap : List Nat → Option Nat
  | [] => none
  | c :: cs => some (cs.foldl min c)

/-- The least member is at most every member. -/
theorem minCap_le {l : List Nat} {m : Nat} (h : minCap l = some m) : ∀ c ∈ l, m ≤ c := by
  cases l with
  | nil => simp [minCap] at h
  | cons c cs =>
      simp only [minCap, Option.some.injEq] at h
      subst h
      have key : ∀ (cs : List Nat) (a : Nat),
          cs.foldl min a ≤ a ∧ ∀ d ∈ cs, cs.foldl min a ≤ d := by
        intro cs
        induction cs with
        | nil => simp
        | cons d ds ih =>
            intro a
            obtain ⟨h1, h2⟩ := ih (min a d)
            refine ⟨le_trans h1 (Nat.min_le_left _ _), ?_⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact le_trans h1 (Nat.min_le_right _ _)
            · exact h2 e he
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact (key cs d).1
      · exact (key cs c).2 d hd

/-- The least member of a nonempty list is a member. -/
theorem minCap_mem {l : List Nat} {m : Nat} (h : minCap l = some m) : m ∈ l := by
  cases l with
  | nil => simp [minCap] at h
  | cons c cs =>
      simp only [minCap, Option.some.injEq] at h
      subst h
      have key : ∀ (cs : List Nat) (a : Nat), cs.foldl min a = a ∨ cs.foldl min a ∈ cs := by
        intro cs
        induction cs with
        | nil => simp
        | cons d ds ih =>
            intro a
            rcases ih (min a d) with h | h
            · rw [List.foldl_cons, h]
              rcases le_total a d with hd | hd
              · exact .inl (Nat.min_eq_left hd)
              · exact .inr (List.mem_cons.mpr (.inl (Nat.min_eq_right hd)))
            · exact .inr (List.mem_cons_of_mem _ h)
      rcases key cs c with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h

/-- **The derived bounds** of a body: for each scalar parameter with a cap along the spine,
    its register bound by its least cap. -/
def deriveBounds (args : List AbiArg) (te : TExpr) : List (String × Nat) :=
  args.filterMap fun a =>
    match a.kind with
    | .scalar => (minCap (capsOf (arrLens args) a.name te)).map fun k => (a.reg, k)
    | .words _ => none

/-- **Each derived bound is on the register of a scalar parameter, at its least cap**: the
    parameter has a cap along the spine, and the bound is at most each of its caps. -/
theorem mem_deriveBounds {args : List AbiArg} {te : TExpr} {b : String × Nat}
    (h : b ∈ deriveBounds args te) :
    ∃ a ∈ args, a.kind = .scalar ∧ a.reg = b.1 ∧
      minCap (capsOf (arrLens args) a.name te) = some b.2 := by
  obtain ⟨a, ha, hb⟩ := List.mem_filterMap.mp h
  cases hk : a.kind with
  | words n => simp [hk] at hb
  | scalar =>
      rw [hk] at hb
      obtain ⟨k, hk', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, ha, hk, rfl, hk'⟩

/-- A derived bound is at most every cap of its parameter. -/
theorem deriveBounds_le_cap {args : List AbiArg} {te : TExpr} {b : String × Nat}
    (h : b ∈ deriveBounds args te) :
    ∃ a ∈ args, a.kind = .scalar ∧ a.reg = b.1 ∧
      ∀ c ∈ capsOf (arrLens args) a.name te, b.2 ≤ c := by
  obtain ⟨a, ha, hk, hr, hm⟩ := mem_deriveBounds h
  exact ⟨a, ha, hk, hr, minCap_le hm⟩

/-- Without scalar parameters there is no derived bound. -/
theorem deriveBounds_nil_of_no_scalar {args : List AbiArg} (te : TExpr)
    (h : ∀ a ∈ args, a.kind ≠ .scalar) : deriveBounds args te = [] := by
  rw [deriveBounds, List.filterMap_eq_nil_iff]
  intro a ha
  cases hk : a.kind with
  | scalar => exact absurd hk (h a ha)
  | words n => rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds
