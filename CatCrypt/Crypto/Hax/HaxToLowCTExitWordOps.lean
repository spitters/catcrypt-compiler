/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTSignedOps
public import CatCrypt.Crypto.Hax.HaxToLowCTWordOps
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ExitTyped

/-!
# Word operations of the typed exit front computed in the scalar heap

The typed exit front (`haxToLowCTKT`, `HaxToLowCTSim_ExitTyped`) lowers a binding
`let n = f(x₁, …, xₖ)` of a call that is not a scalar operation of `scalarOpExprT`, with
scalar arguments and a scalar result, by `callHeadAt`: each argument `xᵢ` is stored into
limb `0` of the fresh tower slot `exitMarshalName xᵢ`, the call writes the reserved slot
`exitCallName`, and limb `0` of that slot is copied into `n`:

```
RSeq (RLetZero exitCallName dr (marshal (RCall f ⟨exitCallName, dr⟩ ls)))
  (RSeq (RScalarSetExpr n (SLimb exitCallName 0)) b)
```

`scalarizeExitIn W I` replaces every such call of a word operation by the scalar
assignment `RScalarSetExpr n se` of its scalar expression `se` on the argument names
(`exitOpSExpr`): the `u64` word calls (`wordOpSExpr`), the width-tagged word calls
(`narrowOpSExpr`), the casts to at most `64` bits of a name of `W` and the complements
(`narrowUnSExpr`), the signed operations (`SignedOp.sexpr`), the signed comparisons of two
names of `I` (`SignedCmp.sexpr`), and the signed and residue conversions of a name of
`W ++ I` (`signedUnSExpr`).  `W` is the list of names holding unsigned words below `2^64`,
`I` the list of names holding signed values.

The exit front assigns a comparison `Lt`, `Gt`, `Le`, `Ge` of two scalar names in its
unsigned form (`scalarOpExprT`), which on the two's complements of negative values differs
from the signed comparison.  The pass assigns the signed form `SignedCmp.sexpr` when both
names are in `I` (`signedCmpFix`).

The scalar expression of each construct is the one the passes `scalarizeWordOps`,
`scalarizeNarrowIn` and `scalarizeSignedIn` assign inside `RLetU64Zero n`
(`exitOpSExpr_word` and the lemmas after it), so the step lemma of the construct is its
simulation lemma here (`HaxToLowCTExitWordOpsSim`).

## Main definitions

* `sexprReads` — whether a scalar expression reads a name.
* `exitOpSExpr` — the scalar expression of a word call on scalar names.
* `exitCallArgs`, `exitLowerCall` — the call and scalar arguments of a marshalled call.
* `signedCmpFix` — the signed form of a comparison of two signed names.
* `scalarizeExitIn`, `scalarizeExitOps` — the lowering pass.

## Main results

* `exitOpSExpr_reads`, `signedCmpFix_reads` — the scalar expression of a call reads only
  its arguments, and the signed form of a comparison the names of its unsigned form.
* `exitOpSExpr_word`, `exitOpSExpr_narrow`, `exitOpSExpr_cast`, `exitOpSExpr_not`,
  `exitOpSExpr_signed`, `exitOpSExpr_signedCmp`, `exitOpSExpr_signedCast`,
  `exitOpSExpr_residue` — the scalar expression of each construct.
* `scalarizeExitIn_callHead` — on the lowering `callHeadAt` gives a binding with scalar
  arguments and a scalar result, the pass assigns the scalar expression of the call.
* `scalarizeExitIn_cmp` — on the unsigned form of a comparison of two signed names, the
  pass assigns the signed comparison.
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.Ascent (sextSExpr asrSExpr sltSExpr signMaskSExpr
  sOrExpr sNotExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt (ltExpr carryExpr)

/-- Whether the scalar expression `e` reads the name `x`. -/
def sexprReads (x : String) : SExpr → Bool
  | .SVar y => y == x
  | .SLit _ | .SLimb _ _ => false
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b | .SXor a b
  | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b | .SMulHiS a b =>
      sexprReads x a || sexprReads x b

/-! ### The scalar expressions of the word calls -/

/-- The scalar expression of the word call `f` on the scalar names `xs`, with `W` the
    names holding unsigned words below `2^64` and `I` the names holding signed values:
    for two arguments a `u64` word call (`wordOpSExpr`), a width-tagged word call
    (`narrowOpSExpr`), a signed operation (`SignedOp.sexpr`) or a signed comparison of two
    names of `I` (`SignedCmp.sexpr`); for one argument a cast of a name of `W` or a
    complement (`narrowUnSExpr W`), or a signed or residue conversion of a name of
    `W ++ I` (`signedUnSExpr`). -/
def exitOpSExpr (W I : List String) (f : String) : List String → Option SExpr
  | [a, b] =>
      wordOpSExpr f (.SVar a) (.SVar b) <|> narrowOpSExpr f (.SVar a) (.SVar b) <|>
        (signedOpOf f).map (fun p => p.2.sexpr p.1 (.SVar a) (.SVar b)) <|>
        (if a ∈ I ∧ b ∈ I then (signedCmpOf f).map (fun c => c.sexpr (.SVar a) (.SVar b))
         else none)
  | [a] => narrowUnSExpr W f a <|> signedUnSExpr (W ++ I) f a
  | _ => none

/-- The `u64` word calls are no width-tagged calls. -/
theorem narrowOpSExpr_of_word {f : String} {a b se : SExpr}
    (h : wordOpSExpr f a b = some se) : narrowOpSExpr f a b = none := by
  unfold wordOpSExpr at h
  split at h <;> (try cases h) <;> rfl

/-- The signed operations are neither `u64` word calls nor width-tagged calls. -/
theorem wordOpSExpr_of_signed {f : String} {w : Nat} {op : SignedOp}
    (h : signedOpOf f = some (w, op)) (a b : SExpr) :
    wordOpSExpr f a b = none ∧ narrowOpSExpr f a b = none := by
  unfold signedOpOf at h
  split at h <;> (try cases h) <;> exact ⟨rfl, rfl⟩

/-- The comparisons are no word calls of another kind. -/
theorem wordOpSExpr_of_cmp {f : String} {c : SignedCmp} (h : signedCmpOf f = some c)
    (a b : SExpr) :
    wordOpSExpr f a b = none ∧ narrowOpSExpr f a b = none ∧ signedOpOf f = none := by
  unfold signedCmpOf at h
  split at h <;> (try cases h) <;> exact ⟨rfl, rfl, rfl⟩

/-- The signed and residue conversions are neither casts to unsigned widths nor
    complements. -/
theorem narrowUnSExpr_of_signedUn {W : List String} {f a : String}
    (h : (signedCastOf f).isSome ∨ (residueCastOf f).isSome) : narrowUnSExpr W f a = none := by
  rcases h with h | h
  · unfold signedCastOf at h
    split at h <;> (try cases h) <;> rfl
  · unfold residueCastOf at h
    split at h <;> (try cases h) <;> rfl

theorem exitOpSExpr_word {W I : List String} {f a b : String} {se : SExpr}
    (h : wordOpSExpr f (.SVar a) (.SVar b) = some se) : exitOpSExpr W I f [a, b] = some se := by
  simp [exitOpSExpr, h]

theorem exitOpSExpr_narrow {W I : List String} {f a b : String} {w : Nat} {op : NarrowOp}
    (h : narrowOpOf f = some (w, op)) :
    exitOpSExpr W I f [a, b] = some (op.sexpr w (.SVar a) (.SVar b)) := by
  have hw : wordOpSExpr f (.SVar a) (.SVar b) = none := by
    rcases hs : wordOpSExpr f (.SVar a) (.SVar b) with _ | se
    · rfl
    · have := narrowOpSExpr_of_word hs
      simp [narrowOpSExpr, h] at this
  simp [exitOpSExpr, hw, narrowOpSExpr, h]

theorem exitOpSExpr_signed {W I : List String} {f a b : String} {w : Nat} {op : SignedOp}
    (h : signedOpOf f = some (w, op)) :
    exitOpSExpr W I f [a, b] = some (op.sexpr w (.SVar a) (.SVar b)) := by
  obtain ⟨h1, h2⟩ := wordOpSExpr_of_signed h (.SVar a) (.SVar b)
  simp [exitOpSExpr, h1, h2, h]

theorem exitOpSExpr_signedCmp {W I : List String} {f a b : String} {c : SignedCmp}
    (h : signedCmpOf f = some c) (ha : a ∈ I) (hb : b ∈ I) :
    exitOpSExpr W I f [a, b] = some (c.sexpr (.SVar a) (.SVar b)) := by
  obtain ⟨h1, h2, h3⟩ := wordOpSExpr_of_cmp h (.SVar a) (.SVar b)
  simp [exitOpSExpr, h1, h2, h3, h, ha, hb]

theorem exitOpSExpr_cast {W I : List String} {f a : String} {w : Nat}
    (h : narrowCastOf f = some w) (ha : a ∈ W) :
    exitOpSExpr W I f [a] = some (narrowMask w (.SVar a)) := by
  simp [exitOpSExpr, narrowUnSExpr, h, ha]

theorem exitOpSExpr_not {W I : List String} {f a : String} {w : Nat}
    (h : narrowNotOf f = some w) :
    exitOpSExpr W I f [a] = some (narrowNotSExpr w (.SVar a)) := by
  have hc : narrowCastOf f = none := by
    unfold narrowNotOf at h
    split at h <;> (try cases h) <;> rfl
  simp [exitOpSExpr, narrowUnSExpr, hc, h]

theorem exitOpSExpr_signedCast {W I : List String} {f a : String} {w : Nat}
    (h : signedCastOf f = some w) (ha : a ∈ W ∨ a ∈ I) :
    exitOpSExpr W I f [a] = some (sextSExpr w (.SVar a)) := by
  have hn := narrowUnSExpr_of_signedUn (W := W) (f := f) (a := a) (Or.inl (by simp [h]))
  have ha' : a ∈ W ++ I := List.mem_append.mpr ha
  simp [exitOpSExpr, hn, signedUnSExpr, h, ha']

theorem exitOpSExpr_residue {W I : List String} {f a : String} {w : Nat}
    (h : residueCastOf f = some w) (ha : a ∈ W ∨ a ∈ I) :
    exitOpSExpr W I f [a] = some (.SAnd (.SVar a) (.SLit (2 ^ w - 1))) := by
  have hn := narrowUnSExpr_of_signedUn (W := W) (f := f) (a := a) (Or.inr (by simp [h]))
  have hs : signedCastOf f = none := by
    unfold residueCastOf at h
    split at h <;> (try cases h) <;> rfl
  have ha' : a ∈ W ++ I := List.mem_append.mpr ha
  simp [exitOpSExpr, hn, signedUnSExpr, h, hs, ha']

/-! ### The names a scalar expression reads -/

@[simp] theorem sexprReads_narrowMask (x : String) (w : Nat) (e : SExpr) :
    sexprReads x (narrowMask w e) = sexprReads x e := by
  simp [narrowMask, sexprReads]

@[simp] theorem sexprReads_sNotExpr (x : String) (e : SExpr) :
    sexprReads x (sNotExpr e) = sexprReads x e := by
  simp [sNotExpr, sexprReads]

@[simp] theorem sexprReads_sOrExpr (x : String) (a b : SExpr) :
    sexprReads x (sOrExpr a b) = (sexprReads x a || sexprReads x b) := by
  simp [sOrExpr, sexprReads]

@[simp] theorem sexprReads_sextSExpr (x : String) (w : Nat) (e : SExpr) :
    sexprReads x (sextSExpr w e) = sexprReads x e := by
  unfold sextSExpr
  split <;> simp [sexprReads]

@[simp] theorem sexprReads_asrSExpr (x : String) (a k : SExpr) :
    sexprReads x (asrSExpr a k) = (sexprReads x a || sexprReads x k) := by
  simp only [asrSExpr, signMaskSExpr, sexprReads]
  cases sexprReads x a <;> cases sexprReads x k <;> rfl

@[simp] theorem sexprReads_sltSExpr (x : String) (a b : SExpr) :
    sexprReads x (sltSExpr a b) = (sexprReads x a || sexprReads x b) := by
  simp only [sltSExpr, ltExpr, carryExpr, sexprReads]
  cases sexprReads x a <;> cases sexprReads x b <;> rfl

/-- **The scalar expression of a call reads only its arguments.** -/
theorem exitOpSExpr_reads {W I : List String} {f x : String} {xs : List String} {se : SExpr}
    (h : exitOpSExpr W I f xs = some se) (hx : x ∉ xs) : sexprReads x se = false := by
  match xs, h with
  | [a, b], h =>
    have ha : (a == x) = false := by simp only [beq_eq_false_iff_ne]; rintro rfl; simp at hx
    have hb : (b == x) = false := by simp only [beq_eq_false_iff_ne]; rintro rfl; simp at hx
    simp only [exitOpSExpr] at h
    rcases hw : wordOpSExpr f (.SVar a) (.SVar b) with _ | se₁
    · rw [hw] at h
      rcases hn : narrowOpSExpr f (.SVar a) (.SVar b) with _ | se₂
      · rw [hn] at h
        rcases hs : signedOpOf f with _ | ⟨w, op⟩
        · rw [hs] at h
          split at h
          · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp (by simpa using h)
            cases c <;> simp [SignedCmp.sexpr, sexprReads, ha, hb]
          · simp at h
        · simp only [hs, Option.map_some, Option.orElse_eq_orElse, Option.orElse_eq_or,
            Option.none_or, Option.some_or, Option.some.injEq] at h
          subst h
          cases op <;> simp [SignedOp.sexpr, sexprReads, ha, hb]
      · simp only [hn, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.none_or,
          Option.some_or, Option.some.injEq] at h
        subst h
        obtain ⟨⟨w, op⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hn
        cases op <;> simp [NarrowOp.sexpr, narrowRotSExpr, narrowAmt, sexprReads, ha, hb]
    · simp only [hw, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or,
        Option.some.injEq] at h
      subst h
      unfold wordOpSExpr at hw
      split at hw <;> (try cases hw) <;> simp [sexprReads, ha, hb]
  | [a], h =>
    have ha : (a == x) = false := by simp only [beq_eq_false_iff_ne]; rintro rfl; simp at hx
    simp only [exitOpSExpr] at h
    rcases hn : narrowUnSExpr W f a with _ | se₁
    · rw [hn] at h
      simp only [Option.orElse_eq_orElse, Option.orElse_eq_or, Option.none_or,
        signedUnSExpr] at h
      split at h
      · split at h
        · cases h; simp [sexprReads, ha]
        · obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
          simp [sexprReads, ha]
      · cases h
    · simp only [hn, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or,
        Option.some.injEq] at h
      subst h
      unfold narrowUnSExpr at hn
      split at hn
      · split at hn
        · cases hn; simp [sexprReads, ha]
        · cases hn
      · obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp hn
        simp [narrowNotSExpr, sexprReads, ha]

/-! ### The lowering pass -/

/-- The call name and the scalar argument names of a marshalled call `k` into
    `exitCallName`: `k` stores the scalar `xᵢ` into limb `0` of a zeroed tower slot `mᵢ`
    for each argument and calls `f` on the slots; `ms` holds the pairs `(mᵢ, xᵢ)` of the
    stores outside `k`. -/
def exitCallArgs (ms : List (String × String)) : LowCT → Option (String × List String)
  | .RLetZero m _ (.RSeq (.RLimbStoreExpr l 0 (.SVar x)) k) =>
      if l.locVar = m then exitCallArgs ((m, x) :: ms) k else none
  | .RCall f d ls =>
      if d.locVar = exitCallName then (ls.mapM fun l => ms.lookup l.locVar).map (f, ·) else none
  | _ => none

/-- The scalar expression of the marshalled call `k` into the slot `c` whose limb `0` is
    read from the slot `c'`, when both are `exitCallName`. -/
def exitLowerCall (W I : List String) (c c' : String) (k : LowCT) : Option SExpr :=
  if c = exitCallName ∧ c' = exitCallName then
    (exitCallArgs [] k).bind fun p => exitOpSExpr W I p.1 p.2
  else none

/-- The signed form of a comparison the exit front assigns in its unsigned form
    (`scalarOpExprT`) on two names of `I`: `SLt a b`, the form of `Lt(a, b)` and of
    `Gt(b, a)`, is `SignedCmp.lt.sexpr a b`; `SSub 1 (SLt a b)`, the form of `Ge(a, b)` and
    of `Le(b, a)`, is `SignedCmp.ge.sexpr a b`. -/
def signedCmpFix (I : List String) : SExpr → Option SExpr
  | .SLt (.SVar a) (.SVar b) =>
      if a ∈ I ∧ b ∈ I then some (SignedCmp.lt.sexpr (.SVar a) (.SVar b)) else none
  | .SSub (.SLit 1) (.SLt (.SVar a) (.SVar b)) =>
      if a ∈ I ∧ b ∈ I then some (SignedCmp.ge.sexpr (.SVar a) (.SVar b)) else none
  | _ => none

/-- The pass replacing every marshalled word call whose limb `0` is copied into a scalar
    name `n` by the scalar assignment of `exitOpSExpr W I` to `n`, and every comparison of
    two names of `I` the exit front assigns in its unsigned form by its signed form
    (`signedCmpFix`), through sequences, bindings, branches, loops and blocks. -/
def scalarizeExitIn (W I : List String) : LowCT → LowCT
  | .RSeq (.RLetZero c dr k) (.RSeq (.RScalarSetExpr n (.SLimb c' 0)) b) =>
      match exitLowerCall W I c c' k with
      | some se => .RSeq (.RScalarSetExpr n se) (scalarizeExitIn W I b)
      | none =>
          .RSeq (.RLetZero c dr k)
            (.RSeq (.RScalarSetExpr n (.SLimb c' 0)) (scalarizeExitIn W I b))
  | .RScalarSetExpr n e => .RScalarSetExpr n ((signedCmpFix I e).getD e)
  | .RSeq a b => .RSeq (scalarizeExitIn W I a) (scalarizeExitIn W I b)
  | .RLetZero x t b => .RLetZero x t (scalarizeExitIn W I b)
  | .RLetU64Zero x b => .RLetU64Zero x (scalarizeExitIn W I b)
  | .RIfNz v t e => .RIfNz v (scalarizeExitIn W I t) (scalarizeExitIn W I e)
  | .RWhileNz v b => .RWhileNz v (scalarizeExitIn W I b)
  | .RFor x n b => .RFor x n (scalarizeExitIn W I b)
  | .RForRuntime x bound b => .RForRuntime x bound (scalarizeExitIn W I b)
  | .RBlock b => .RBlock (scalarizeExitIn W I b)
  | c => c

/-- `scalarizeExitIn` from the names `W` of unsigned word type and the names `I` of signed
    type. -/
def scalarizeExitOps (W I : List String) : LowCT → LowCT := scalarizeExitIn W I

/-! ### The pass on the lowering of a call -/

/-- The pair of the marshalling slot of `x` and `x`. -/
def exitMarshalPair (x : String) : String × String := (exitMarshalName x, x)

/-- With every argument scalar, `callMarshal` stores each argument `x` into the slot
    `exitMarshalName x`, and `exitCallArgs` peels the stores, recording the pairs of the
    slots and the arguments. -/
theorem exitCallArgs_callMarshal (A : ExitTowers) (dt : TowerType) :
    ∀ (xs : List String) (ctx : LowCT → LowCT) (ls : List Located),
      (∀ x ∈ xs, A.lookup x = none) →
      callMarshal A dt (xs.map ImpExpr.var) = some (ctx, ls) →
      ls = xs.map (fun x => ⟨exitMarshalName x, dt⟩) ∧
      ∀ (ms : List (String × String)) (c : LowCT),
        exitCallArgs ms (ctx c) = exitCallArgs (xs.reverse.map exitMarshalPair ++ ms) c := by
  intro xs
  induction xs with
  | nil =>
      intro ctx ls _ h
      simp only [List.map_nil, callMarshal, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, fun _ _ => rfl⟩
  | cons x xs ih =>
      intro ctx ls hsc h
      have hx : A.lookup x = none := hsc x (by simp)
      simp only [List.map_cons, callMarshal] at h
      rcases hm : callMarshal A dt (xs.map ImpExpr.var) with _ | ⟨ctx', ls'⟩
      · simp [hm] at h
      · obtain ⟨hls, hctx⟩ := ih ctx' ls' (fun y hy => hsc y (by simp [hy])) hm
        simp only [hm, hx] at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by simp [hls], fun ms c => ?_⟩
          simp only [exitCallArgs, ite_true, hctx, List.reverse_cons, List.map_append,
            List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
          rfl
        · cases h

/-- The marshalling slot of an argument `x` of `zs` finds `x` in the pairs of `zs`
    followed by any list. -/
theorem lookup_exitMarshalPair (ms : List (String × String)) :
    ∀ (zs : List String) (x : String), x ∈ zs →
      (zs.map exitMarshalPair ++ ms).lookup (exitMarshalName x) = some x := by
  intro zs
  induction zs with
  | nil => intro x hx; cases hx
  | cons z zs ih =>
      intro x hx
      simp only [List.map_cons, List.cons_append, List.lookup, exitMarshalPair]
      by_cases hxz : x = z
      · subst hxz; simp
      · have hne : (exitMarshalName x == exitMarshalName z) = false := by
          simp only [beq_eq_false_iff_ne]
          exact fun h => hxz (exitMarshalName_inj h)
        rw [hne]
        exact ih x (by simpa [hxz] using hx)

/-- Reading back the arguments of a call on the marshalling slots of `ys`. -/
theorem mapM_lookup_exitMarshal (L : List (String × String)) (dt : TowerType) :
    ∀ ys : List String, (∀ y ∈ ys, L.lookup (exitMarshalName y) = some y) →
      (ys.map (fun y => (⟨exitMarshalName y, dt⟩ : Located))).mapM
        (fun l => L.lookup l.locVar) = some ys := by
  intro ys
  induction ys with
  | nil => intro _; rfl
  | cons y ys ih =>
      intro h
      simp only [List.map_cons, List.mapM_cons, h y (by simp),
        ih (fun z hz => h z (by simp [hz]))]
      rfl

/-- **The pass on the lowering of a call.** When `callHeadAt` lowers `let n = f(xs)` with
    every argument and `n` held in the scalar heap, and `f` has the scalar expression `se`
    on `xs`, the pass replaces the call by the assignment `RScalarSetExpr n se`. -/
theorem scalarizeExitIn_callHead {W I : List String} {A : ExitTowers} {n f : String}
    {dt dr : TowerType} {xs : List String} {k : LowCT → LowCT} {se : SExpr}
    (hk : callHeadAt A n f dt dr (xs.map ImpExpr.var) = some k)
    (hsc : ∀ x ∈ xs, A.lookup x = none) (hn : A.lookup n = none)
    (hse : exitOpSExpr W I f xs = some se) (b : LowCT) :
    scalarizeExitIn W I (k b) = .RSeq (.RScalarSetExpr n se) (scalarizeExitIn W I b) := by
  unfold callHeadAt at hk
  rcases hm : callMarshal A dt (xs.map ImpExpr.var) with _ | ⟨ctx, ls⟩
  · simp [hm] at hk
  · simp only [hm, hn, Option.some.injEq] at hk
    subst hk
    obtain ⟨hls, hctx⟩ := exitCallArgs_callMarshal A dt xs ctx ls hsc hm
    have hargs : exitCallArgs [] (ctx (.RCall f ⟨exitCallName, dr⟩ ls)) = some (f, xs) := by
      rw [hctx, List.append_nil, exitCallArgs, ite_eq_left rfl, hls,
        mapM_lookup_exitMarshal _ dt xs (fun y hy =>
          by simpa using lookup_exitMarshalPair [] xs.reverse y (List.mem_reverse.mpr hy))]
      rfl
    simp only [scalarizeExitIn, exitLowerCall, and_self, ite_true, hargs, Option.bind_some, hse]

/-- **The pass on a comparison of two signed names.** The unsigned form `scalarOpExprT`
    gives a comparison `f(a, b)` of two names of `I` becomes the scalar expression of the
    signed comparison, the shape of `step_signedCmp`. -/
theorem scalarizeExitIn_cmp {W I : List String} {n f a b : String} {c : SignedCmp}
    {e : SExpr} (hf : signedCmpOf f = some c) (he : scalarOpExprT f (.SVar a) (.SVar b) = some e)
    (ha : a ∈ I) (hb : b ∈ I) :
    scalarizeExitIn W I (.RScalarSetExpr n e) = .RScalarSetExpr n (c.sexpr (.SVar a) (.SVar b)) := by
  unfold signedCmpOf at hf
  split at hf <;> (try cases hf) <;> simp only [scalarOpExprT, Option.some.injEq] at he <;>
    subst he <;> simp [scalarizeExitIn, signedCmpFix, ha, hb, SignedCmp.sexpr]

/-- The signed form of a comparison reads the names its unsigned form reads. -/
theorem signedCmpFix_reads {I : List String} {e e' : SExpr} (h : signedCmpFix I e = some e')
    (x : String) : sexprReads x e' = sexprReads x e := by
  unfold signedCmpFix at h
  split at h
  · split at h
    · cases h; simp [SignedCmp.sexpr, sexprReads]
    · cases h
  · split at h
    · cases h; simp [SignedCmp.sexpr, sexprReads]
    · cases h
  · cases h

end CatCrypt.Crypto.Hax
