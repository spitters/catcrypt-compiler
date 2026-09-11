/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.MlkemPolyAddCapstone
public import CatCrypt.Crypto.SecureCompilation.Ascent.KeystoneControl

/-!
# The ML-KEM ascent fold-lift: per-coefficient tie ↦ whole-polynomial op

`Ascent.MlkemFieldLeaf` proves the **per-coefficient** correspondence
`corres_setExpr_fqAdd` (one unreduced `ZMod 3329` add `r := a + b` refines its
`φ a + φ b` spec), and `Ascent.MlkemPolyAddCapstone` composes a *single*
coefficient step (`polyAddCoeff_corres`).  Its frontier note records the exact
gap this module attacks:

> The 256-coefficient loop needs a heterogeneous `corresH_for` at loop level,
> **which does not exist**.  `corres_for` (`Ascent.Control`) is homogeneous and,
> crucially, hardwired to an **index-independent** abstract step (`nfold fa`, the
> *same* `fa` each trip) — a poly loop runs a *different* step per coefficient.

This file closes the loop-rule gap and delivers the whole-polynomial tie.

## What lands here (all verified, no `sorry`, no new axioms)

* **`corres_for_indexed`** — the missing combinator.  The **index-dependent**
  bounded-loop rule over the real `semScalar`/`semRForD` `RFor` semantics: from a
  per-trip body `Corres SR P (fa n) (RSeq (RScalarSet x n) body)` whose abstract
  step `fa n` may depend on the trip index `n`, plus the invariant `P`, the
  `N`-fold loop refines the *index-folded* iterate `ifold fa N`.  `corres_for` is
  recovered as the constant-step special case (`corres_for_of_indexed`).  This is
  the `semScalar` twin of `corresJ_loop` (`Ascent.RunBlockCorres`, over
  `runBlock`) and the counted (`RFor`) sibling of `corres_while_iter`
  (`Ascent.While`, the fuel `while`): a `while` has no counter bind, so an
  index-varying poly body needs the `semRForD` counter-driven loop, not the
  `while`.

* **The index-dependence is exercised, not vacuous** — `accLoop_corres` lifts the
  index-varying accumulator loop `for i in 0..N { acc := acc + i }` to
  its clean `ZMod 2^64` step, and `accLoop_acc` reads the closed form
  `acc + ∑_{k<N} k` off the fold.  A constant-step `corres_for` cannot state this.

* **`corres_rseqUpto`** — the fold-lift for the *unrolled* chain: a per-index body
  family folds through the homogeneous `corres_seq` into one `Corres` over the
  index-folded step.  (The `RSeq` twin of `corres_for_indexed`; the two share
  `ifold`.)

* **`SRfqMixed` + `corres_setExpr_fqAddMixed`** — the loop-invariant relation that
  makes the poly-add fold *homogeneous*.  A poly-add reads canonical inputs and
  writes a NON-canonical output (`< 6658`), so no single range invariant survives
  a coefficient (`MlkemFieldLeaf`'s heterogeneous `CorresH`).  But the inputs are
  read-only and the outputs are write-only, so the mixed relation "canonical on
  the input names, value-only elsewhere" IS a loop invariant, and the coefficient
  add is a homogeneous `Corres (SRfqMixed inputs)` leaf.

* **`polyAdd_fold_corres`** — the whole-polynomial tie.  For every width `n`, the
  emitted `n`-coefficient poly-add loop (`rseqUpto polyAddBody n`, over the
  `i`-indexed source names `a{i}`/`b{i}`/`r{i}`) refines `ifold polyAddStep n`, the
  composition of `n` coefficient-wise `ZMod 3329` ring adds
  (`polyAddStep i φ (r{i}) = φ (a{i}) + φ (b{i})`, the ring op by definition).
  This is `poly_add ≈ 256 pointwise `ZMod 3329` adds` as one machine-checked
  `Corres`, welded from the per-lane leaf + the loop invariant.

## Frontier — see the module-end note for the precise remaining lemmas.

`polyAdd_fold_corres` is over the **unrolled** `RSeq` chain with per-index scalar
names.  Fusing it into a single *counter-driven* `RFor` over `Array` memory (the
shape the extracted Rust actually lowers to) is the residual, and `corres_for_indexed`
is exactly the loop rule that will consume it once the array-load leaf exists.

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`);
see `Corres.lean`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## §1  The index-folded abstract iterate `ifold`

`ifold fa N = fa (N-1) ∘ … ∘ fa 1 ∘ fa 0`, peeling the LAST application — the exact
mirror of `semRForD`'s structural recursion (`n+1 ↦ bind counter, run body`), but
with a **per-index** step `fa : Nat → AState → AState`.  Generalizes `nfold`
(`Ascent.Control`, the index-independent iterate) and matches `loopStep`
(`Ascent.RunBlockCorres`). -/

/-- `N`-fold application of the **index-dependent** step `fa`, peeling the last
    trip (`n+1 ↦ fa n ∘ ifold fa n`) to match `semRForD`. -/
def ifold {A : Type} (fa : Nat → A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => fa n (ifold fa n a)

/-- The index-folded iterate preserves any predicate preserved by every step. -/
theorem ifold_invariant {A : Type} {fa : Nat → A → A} {P : A → Prop}
    (hinv : ∀ n a, P a → P (fa n a)) : ∀ (N : Nat) (a : A), P a → P (ifold fa N a) := by
  intro N
  induction N with
  | zero => intro a ha; exact ha
  | succ n ih => intro a ha; exact hinv n _ (ih a ha)

/-- When the step does not use the index, `ifold` collapses to `nfold`
    (`Ascent.Control`) — witnessing that `corres_for_indexed` strictly generalizes
    `corres_for`. -/
theorem ifold_const {A : Type} (fa : A → A) :
    ∀ (N : Nat) (a : A), ifold (fun _ => fa) N a = nfold fa N a := by
  intro N
  induction N with
  | zero => intro a; rfl
  | succ n ih => intro a; simp only [ifold, nfold, ih]

/-! ## §2  The index-dependent bounded-loop rule `corres_for_indexed` -/

variable {AState : Type} (SR : SEnvScalar → AState → Prop)

/-- **The index-dependent for-loop rule.**  `semScalar (RFor x N body)` is the
    structural recursion `semRForD`, which per trip binds the counter `x := n` then
    runs the body — the transition `semScalar (RSeq (RScalarSet x n) body)`.  From a
    per-trip-**index** body `Corres` realizing the (index-dependent) abstract step
    `fa n`, and every `fa n` preserving the precondition `P`, the `N`-fold loop
    realizes the index-folded iterate `ifold fa N`.  Generic in `SR` / `AState`.

    This is the exact generalization the `MlkemPolyAddCapstone` frontier flagged as
    missing: `corres_for` is the special case `fa n = fa` (`corres_for_of_indexed`),
    which cannot describe a loop whose body varies with the coefficient index. -/
theorem corres_for_indexed (x : String) (body : LowCT) {P : AState → Prop}
    {fa : Nat → AState → AState}
    (hbody : ∀ n : Nat, Corres SR P (fa n) (.RSeq (.RScalarSet x n) body))
    (hinv : ∀ n a, P a → P (fa n a)) :
    ∀ N : Nat, Corres SR P (ifold fa N) (.RFor x N body) := by
  intro N
  induction N with
  | zero =>
      intro env a hSR _
      exact ⟨env, rfl, hSR⟩
  | succ n ih =>
      intro env a hSR hP
      obtain ⟨envPre, hstepPre, hSRPre⟩ := ih env a hSR hP
      have hPpre : P (ifold fa n a) := ifold_invariant hinv n a hP
      obtain ⟨env', hstep', hSR'⟩ := hbody n envPre (ifold fa n a) hSRPre hPpre
      refine ⟨env', ?_, hSR'⟩
      -- `semScalar (RFor x (n+1) body)` peels the last trip: run trips `0..n-1`
      -- (`hstepPre`), bind `x := n`, run the body (`hstep'`).
      have hstepPre' : semRForD (fun e => semScalar body e) x n env = some envPre := hstepPre
      have hstep'' : semScalar body (envPre.upd x (t := .sword 64) (BitVec.ofNat 64 n))
          = some env' := by
        have := hstep'
        simpa only [semScalar, Option.bind_some] using this
      show semRForD (fun e => semScalar body e) x (n + 1) env = some env'
      simp only [semRForD, hstepPre', hstep'']

/-- `corres_for` (`Ascent.Control`) recovered: the constant-step special case of
    `corres_for_indexed`, via `ifold (fun _ => fa) = nfold fa`. -/
theorem corres_for_of_indexed (x : String) (body : LowCT) {P : AState → Prop}
    {fa : AState → AState}
    (hbody : ∀ n : Nat, Corres SR P fa (.RSeq (.RScalarSet x n) body))
    (hinv : ∀ a, P a → P (fa a)) (N : Nat) :
    Corres SR P (nfold fa N) (.RFor x N body) := by
  have h := corres_for_indexed SR x body (fa := fun _ => fa) hbody (fun _ a ha => hinv a ha) N
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := h env a hSR hP
  exact ⟨env', hstep, by rw [ifold_const] at hSR'; exact hSR'⟩

/-! ## §3  The unrolled fold-lift `corres_rseqUpto`

The `RSeq` twin of `corres_for_indexed`: an unrolled chain `body 0; body 1; …;
body (n-1)` of per-index bodies folds through the homogeneous `corres_seq` into one
`Corres` over the same index-folded step `ifold step n`.  This is what lifts a
family of per-coefficient leaves to a whole-polynomial statement without a
counter. -/

/-- The unrolled body chain `body 0; body 1; …; body (n-1)` (body 0 runs first),
    built to match `ifold`'s last-trip peeling. -/
def rseqUpto (body : Nat → LowCT) : Nat → LowCT
  | 0 => .RSkip
  | n + 1 => .RSeq (rseqUpto body n) (body n)

/-- **The unrolled fold-lift.**  If each per-index body `body i` refines its abstract
    step `step i` and `P` is preserved by every step, the `n`-body chain
    `rseqUpto body n` refines the index-folded iterate `ifold step n`.  Assembled by
    induction on `n` through `corres_seq` — the `Corres`/`semScalar` analogue of
    `corresJ_loop`'s `corresJ_append` assembly. -/
theorem corres_rseqUpto {P : AState → Prop} {step : Nat → AState → AState}
    {body : Nat → LowCT}
    (hstep : ∀ i, Corres SR P (step i) (body i))
    (hinv : ∀ i a, P a → P (step i a)) :
    ∀ n : Nat, Corres SR P (ifold step n) (rseqUpto body n) := by
  intro n
  induction n with
  | zero => intro env a hSR _; exact ⟨env, rfl, hSR⟩
  | succ k ih =>
      show Corres SR P (fun a => step k (ifold step k a)) (.RSeq (rseqUpto body k) (body k))
      exact corres_seq SR ih (hstep k) (fun a ha => ifold_invariant hinv k a ha)

end CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## §4  An index-dependent instantiation over the word layer (non-vacuity)

The accumulator loop `for i in 0..N { acc := acc + i }` — a body whose effect
depends on the trip index `i` — lifts through `corres_for_indexed` to its
clean `ZMod 2^64` iterate.  A constant-step `corres_for` cannot even state this
(its abstract step is the same each trip).  This is the word-layer witness that the
index-dependence in `corres_for_indexed` is real. -/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-- The accumulator loop's clean per-index abstract step: `acc := acc + i`, and the
    counter `i := n` bind the body performs. -/
def accStep (n : Nat) : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)) :=
  fun a s => if s = "acc" then a "acc" + (n : ZMod (2 ^ 64))
             else if s = "i" then (n : ZMod (2 ^ 64)) else a s

/-- The per-trip body `i := n; acc := acc + i` realizes the index-dependent step
    `accStep n`, glued from the counter leaf `corres_setScalar_NT` and the
    arithmetic-expression leaf `corres_setExpr`, re-based by `corres_fa_congr`. -/
theorem accBody_corres (n : Nat) :
    Corres SRwordNT (fun _ => True) (accStep n)
      (.RSeq (.RScalarSet "i" n)
        (.RScalarSetExpr "acc" (.SAdd (.SVar "acc") (.SVar "i")))) := by
  have hstep :=
    corres_seq (SR := SRwordNT) (corres_setScalar_NT "i" n)
      (corres_setExpr "acc" (.SAdd (.SVar "acc") (.SVar "i"))
        ⟨notTmp_of_short "acc" (by decide), notTmp_of_short "i" (by decide)⟩)
      (fun _ _ => trivial)
  refine corres_fa_congr hstep ?_
  intro a
  funext s
  simp only [accStep, evalZMod]
  by_cases hacc : s = "acc"
  · simp [hacc]
  · by_cases hi : s = "i" <;> simp [hacc, hi]

/-- **The accumulator loop ascends (index-dependent non-vacuity).**  The word-layer
    loop `for i in 0..N { acc := acc + i }` refines the index-folded iterate
    `ifold accStep N`, via `corres_for_indexed`. -/
theorem accLoop_corres (N : Nat) :
    Corres SRwordNT (fun _ => True) (ifold accStep N)
      (.RFor "i" N (.RScalarSetExpr "acc" (.SAdd (.SVar "acc") (.SVar "i")))) :=
  corres_for_indexed SRwordNT "i" _ accBody_corres (fun _ _ _ => trivial) N

/-- **Closed form of the fold.**  After `N` trips the accumulator holds
    `acc + ∑_{k<N} k` in `ZMod 2^64` — the loop sums the trip indices,
    which only an index-dependent step can express. -/
theorem accLoop_acc (N : Nat) (a : String → ZMod (2 ^ 64)) :
    ifold accStep N a "acc" = a "acc" + ∑ k ∈ Finset.range N, (k : ZMod (2 ^ 64)) := by
  induction N with
  | zero => simp [ifold]
  | succ n ih =>
      have hstep : accStep n (ifold accStep n a) "acc"
          = ifold accStep n a "acc" + (n : ZMod (2 ^ 64)) := by simp [accStep]
      simp only [ifold, hstep, ih, Finset.sum_range_succ]
      ring

/-! ## §5  The mixed loop-invariant relation for the `ZMod 3329` poly-add

An unreduced coefficient add `r := a + b` takes canonical inputs (`< 3329`) to a
NON-canonical output (`< 6658`), so `SRfqCanon` is not preserved and the leaf is
heterogeneous (`CorresH SRfqCanon SRfqVal`, `MlkemFieldLeaf`).  In a *poly*-add,
though, the input names are read-only and the output names are write-only, so the
relation "canonical on a designated input set, value-only elsewhere" IS preserved
across every coefficient — making the whole loop **homogeneous** over that mixed
relation, which is what lets the fold-lift `corres_rseqUpto` apply. -/

/-- The mixed loop-invariant relation: every non-temp name holds a `.sword 64` whose
    `fqEnc` is the abstract coefficient, and names in the input set `inputs` are
    additionally canonical (`< 3329`).  `SRfqCanon = SRfqMixed (fun _ => True)` in
    spirit; `SRfqVal = SRfqMixed (fun _ => False)`.  It is preserved by an add that
    reads `inputs` names and writes a non-`inputs` name. -/
def SRfqMixed (inputs : String → Prop) (env : SEnvScalar) (a : String → ZMod 3329) : Prop :=
  ∀ x, ¬ isTmpName x →
    ∃ w : BitVec 64, env x = some ⟨.sword 64, w⟩ ∧ (inputs x → w.toNat < 3329) ∧ fqEnc w = a x

/-- **The homogeneous coefficient-add leaf.**  A single unreduced add
    `r := a + b` where `a`, `b` are canonical input names and `r` is a non-input
    output name refines its `ZMod 3329` spec `φ a + φ b`, as a *homogeneous*
    `Corres (SRfqMixed inputs)` — the mixed relation is preserved because the write
    lands on a non-input name (no canonicity obligation) and leaves the input names
    untouched.  The value transfer is `fqEnc_add_of_canonical`, its no-overflow
    hypothesis discharged from the inputs' canonicity; progress is
    `semLowerSExpr_ok'`, exactly as in `corres_setExpr_fqAdd`. -/
theorem corres_setExpr_fqAddMixed (inputs : String → Prop)
    (aName bName rName : String)
    (hna : ¬ isTmpName aName) (hnb : ¬ isTmpName bName)
    (hia : inputs aName) (hib : inputs bName) (hir : ¬ inputs rName) :
    Corres (SRfqMixed inputs) (fun _ => True)
      (fun φ s => if s = rName then φ aName + φ bName else φ s)
      (.RScalarSetExpr rName (.SAdd (.SVar aName) (.SVar bName))) := by
  intro env a hSR _
  set e : SExpr := .SAdd (.SVar aName) (.SVar bName) with he
  have hclean : srcClean e := ⟨hna, hnb⟩
  set rs : RustState := ⟨fun _ => none, fun y => (envReader env y).toNat⟩ with hrs
  have hEB : EnvBoundOn rs env (fun _ => True) := by
    intro y _ hnt
    obtain ⟨w, hw, _, _⟩ := hSR y hnt
    have hr : envReader env y = w := by simp only [envReader, hw]
    have hround : BitVec.ofNat 64 w.toNat = w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt w.isLt
    show env y = some ⟨.sword 64, BitVec.ofNat 64 ((envReader env y).toNat)⟩
    rw [hr, hround]; exact hw
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ :=
    semLowerSExpr_ok' rs (fun _ => True) e env 0 hEB (varsBoundIn_true e) hclean
  -- the two canonical source coefficients (canonicity from `inputs`)
  obtain ⟨wa, hwa, hwacan, hwaEnc⟩ := hSR aName hna
  obtain ⟨wb, hwb, hwbcan, hwbEnc⟩ := hSR bName hnb
  have hwalt : wa.toNat < 3329 := hwacan hia
  have hwblt : wb.toNat < 3329 := hwbcan hib
  have hra : envReader env aName = wa := by simp only [envReader, hwa]
  have hrb : envReader env bName = wb := by simp only [envReader, hwb]
  have hev : SExpr.evalBV (envReader env) e = wa + wb := by
    simp only [he, SExpr.evalBV, hra, hrb]
  have hval : fqEnc (SExpr.evalBV (envReader env) e) = a aName + a bName := by
    rw [hev, fqEnc_add_of_canonical wa wb hwalt hwblt, hwaEnc, hwbEnc]
  refine ⟨env2.upd rName (t := .sword 64) (SExpr.evalBV (envReader env) e), ?_, ?_⟩
  · simp only [semScalar, hsem]
  · intro y hnt
    by_cases hyx : y = rName
    · refine ⟨SExpr.evalBV (envReader env) e, ?_, ?_, ?_⟩
      · simp only [SEnvScalar.upd, if_pos hyx]
      · -- `y = rName` is a non-input name, so no canonicity obligation fires
        intro hin; exact absurd (hyx ▸ hin) hir
      · show fqEnc (SExpr.evalBV (envReader env) e)
          = if y = rName then a aName + a bName else a y
        rw [if_pos hyx]; exact hval
    · obtain ⟨w, hw, hwcan, hwEnc⟩ := hSR y hnt
      refine ⟨w, ?_, ?_, ?_⟩
      · simp only [SEnvScalar.upd, if_neg hyx]
        rw [hotb y (Or.inl hnt)]; exact hw
      · exact hwcan
      · show fqEnc w = if y = rName then a aName + a bName else a y
        rw [if_neg hyx]; exact hwEnc

/-! ## §6  String helpers: source coefficient names are never fresh temps

The `i`-indexed coefficient names `a{i}`/`b{i}`/`r{i}` (length grows with `i`, so
`notTmp_of_short` does not cover them) are non-temp by their **front character**:
`tmpName k = "__sx" ++ …` starts with `'_'`, while a coefficient name starts with
its prefix letter. -/

/-- A string whose `toList` starts with a non-`'_'` character is never a fresh temp
    (`tmpName k` starts with `'_'`). -/
theorem notTmp_of_headNe (s : String) (c : Char) (t : List Char)
    (hs : s.toList = c :: t) (hc : c ≠ '_') : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  have hd := congrArg String.toList hk
  rw [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms.tmpName,
      String.toList_append, hs] at hd
  simp only [show "__sx".toList = ['_', '_', 's', 'x'] from rfl,
    List.cons_append, List.nil_append] at hd
  injection hd with h1 _
  exact hc h1

/-- A one-character-prefixed name `p ++ t`, with `p.toList = [c]` and `c ≠ '_'`, is
    never a fresh temp. -/
theorem notTmp_appPrefix (c : Char) (hc : c ≠ '_') (p t : String)
    (hp : p.toList = [c]) : ¬ isTmpName (p ++ t) :=
  notTmp_of_headNe (p ++ t) c t.toList
    (by rw [String.toList_append, hp]; rfl) hc

/-- Two one-character-prefixed names with distinct prefix letters are distinct. -/
theorem appPrefix_ne (c d : Char) (hne : c ≠ d) (p q s t : String)
    (hp : p.toList = [c]) (hq : q.toList = [d]) : p ++ s ≠ q ++ t := by
  intro h
  have hd := congrArg String.toList h
  rw [String.toList_append, String.toList_append, hp, hq] at hd
  injection hd with h1 _
  exact hne h1

/-! ## §7  The whole-polynomial fold-lift for `ZMod 3329` poly-add

The `i`-indexed source-name model of a poly-add: coefficient `i` reads `a{i}`,
`b{i}` and writes `r{i}`.  The input set is the `a`/`b` names; each coefficient's
abstract step is a `ZMod 3329` ring add by definition.  `corres_rseqUpto` over the
mixed loop invariant lifts the per-lane leaf to the whole `n`-coefficient loop. -/

/-- The `i`-th coefficient source name (`a`-operand). -/
def aNm (i : Nat) : String := "a" ++ toString i
/-- The `i`-th coefficient source name (`b`-operand). -/
def bNm (i : Nat) : String := "b" ++ toString i
/-- The `i`-th coefficient output name. -/
def rNm (i : Nat) : String := "r" ++ toString i

/-- The input set of the poly-add: exactly the `a{i}` and `b{i}` names. -/
def polyInputs (x : String) : Prop := ∃ i, x = aNm i ∨ x = bNm i

/-- The `i`-th coefficient body `r{i} := a{i} + b{i}` (an `RScalarSetExpr` add). -/
def polyAddBody (i : Nat) : LowCT :=
  .RScalarSetExpr (rNm i) (.SAdd (.SVar (aNm i)) (.SVar (bNm i)))

/-- The `i`-th coefficient abstract step — a `ZMod 3329` ring add by definition:
    `polyAddStep i φ (r{i}) = φ (a{i}) + φ (b{i})`. -/
def polyAddStep (i : Nat) : (String → ZMod 3329) → (String → ZMod 3329) :=
  fun φ s => if s = rNm i then φ (aNm i) + φ (bNm i) else φ s

theorem notTmp_aNm (i : Nat) : ¬ isTmpName (aNm i) :=
  notTmp_appPrefix 'a' (by decide) "a" (toString i) rfl
theorem notTmp_bNm (i : Nat) : ¬ isTmpName (bNm i) :=
  notTmp_appPrefix 'b' (by decide) "b" (toString i) rfl
theorem notTmp_rNm (i : Nat) : ¬ isTmpName (rNm i) :=
  notTmp_appPrefix 'r' (by decide) "r" (toString i) rfl

/-- An output name `r{i}` is never an input name (front character `'r'` vs
    `'a'`/`'b'`). -/
theorem notInput_rNm (i : Nat) : ¬ polyInputs (rNm i) := by
  rintro ⟨j, hj | hj⟩
  · exact appPrefix_ne 'r' 'a' (by decide) "r" "a" (toString i) (toString j) rfl rfl hj
  · exact appPrefix_ne 'r' 'b' (by decide) "r" "b" (toString i) (toString j) rfl rfl hj

/-- The per-coefficient leaf as a homogeneous `Corres (SRfqMixed polyInputs)`. -/
theorem polyAddBody_corres (i : Nat) :
    Corres (SRfqMixed polyInputs) (fun _ => True) (polyAddStep i) (polyAddBody i) :=
  corres_setExpr_fqAddMixed polyInputs (aNm i) (bNm i) (rNm i)
    (notTmp_aNm i) (notTmp_bNm i)
    ⟨i, Or.inl rfl⟩ ⟨i, Or.inr rfl⟩ (notInput_rNm i)

/-- **The whole-polynomial fold-lift.**  For every width `n`, the emitted
    `n`-coefficient poly-add loop `rseqUpto polyAddBody n` refines
    `ifold polyAddStep n` — the composition of `n` coefficient-wise `ZMod 3329` ring
    adds — as one machine-checked `Corres` over the mixed loop invariant.  At
    `n = 256` this is the ML-KEM `poly_add` correspondence: the per-lane tie
    (`corres_setExpr_fqAddMixed`) lifted over the poly loop (`corres_rseqUpto`) via
    the loop invariant (`SRfqMixed polyInputs`).  Each folded step is the field's
    ring add by definition of `polyAddStep`, so the whole statement is
    `poly_add ≈ pointwise `ZMod 3329` addition`. -/
theorem polyAdd_fold_corres (n : Nat) :
    Corres (SRfqMixed polyInputs) (fun _ => True)
      (ifold polyAddStep n) (rseqUpto polyAddBody n) :=
  corres_rseqUpto (SRfqMixed polyInputs) polyAddBody_corres (fun _ _ _ => trivial) n

/-- The folded abstract op is the field ring add at each coefficient — recorded
    explicitly so the tie to the `ZMod 3329` ring operation is visible at the top
    level. -/
theorem polyAddStep_is_ring_add (i : Nat) (φ : String → ZMod 3329) :
    polyAddStep i φ (rNm i) = φ (aNm i) + φ (bNm i) := by
  simp only [polyAddStep, if_pos]

/-! ## §8  Frontier — the residual to a source→bytes 256-coefficient array poly-add

`polyAdd_fold_corres` closes the ascent leg for the **unrolled** poly-add over
per-index scalar names.  Three residual pieces separate it from a single
*counter-driven* `RFor` over `Array` memory (the shape the extracted Rust lowers to):

1. **The array-load leaf `corres_arrLoad` (`RArrLoad`).**  A counter-driven body
   reads `a[i]`/`b[i]` and writes `r[i]` through the array ops `RArrLoad`/`RArrStore`,
   not scalar names.  The store leaf `corres_arrStore` exists; the load leaf is the
   open dual.  Once it lands, the counter-driven body is exactly the per-trip body
   `corres_for_indexed` (§2) already consumes — the loop rule is ready, only the
   array-indexed leaf is missing.  (The abstract state then becomes `Vector Zq3329
   256`, and the coefficient at index `i` is selected by the counter, replacing the
   `i`-indexed scalar names here.)

2. **Width-16 lanes.**  The deployed ML-KEM emit carries coefficients as 16-bit SIMD
   lanes; `SRfqMixed` / `fqEnc` here are at the reused `.sword 64` slot.  Relating a
   16-bit lane to `ZMod 3329` needs `semScalar`/`SExpr.evalBV`/`semLowerSExpr_ok'`
   re-indexed at width 16 — the same width-parametricity lift `MlkemFieldLeaf` notes.

3. **A per-coefficient emit weld + decimal-index injectivity.**  Reading the final
   `r{j}` off `ifold polyAddStep n` (to phrase the output as a `Vector`) needs
   `rNm` injective (`toString` decimal injectivity) so later trips do not alias
   `r{j}`; and welding one coefficient to bytes is `keystone_emit_fq`
   (`MlkemPolyAddCapstone`) fed the concrete emit data, a mechanical clone of
   `FeAddEndToEnd` at canonical literals.

None of the three is a gap in the loop rule: §2's `corres_for_indexed` is the
index-dependent counted-loop combinator the capstone frontier named as missing, and
§7 is the whole-polynomial `ZMod 3329` tie via the per-lane leaf + the loop
invariant. -/

end CatCrypt.Crypto.SecureCompilation.Ascent
