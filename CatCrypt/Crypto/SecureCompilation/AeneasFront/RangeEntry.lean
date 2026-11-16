/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.RangeSpec
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.DenoteToRustM
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyComplete
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.SignedGuard
public import CatCrypt.Crypto.SecureCompilation.VIR.NFRangeLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.NFRangeCover
public meta import CatCrypt.Crypto.SecureCompilation.AeneasFront.SignedGuard
public meta import CatCrypt.Crypto.SecureCompilation.AeneasFront.RangeSpec
public meta import CatCrypt.Crypto.SecureCompilation.VIR.NFRangeCover

/-!
# Absence of panics of an Aeneas function on an input range

An Aeneas function `f` read by `reifyAeneas%` as the NF program `R.prog`, with the complete
direction of the reading (`completeAeneas%`), has a value at every argument in the input ranges
that the interval checker `NFRange.check` accepts: the checker gives a value of the denotation
of `R.prog` with the leaf table `aeTable` (`NFRange.check_sound'`, `aeSpec_sound`), the
denotation gives the value of the reading (`nfToRustM_of_denote`), and completeness gives a value
of `f`.

The entry checks the input ranges by `NFRange.checkCover`: a range the checker refuses is
bisected at its widest interval, within `coverBudget` checks. A signed argument is read through
the pattern of its word: an interval `[lo, hi]` of nonnegative values is the interval of the
patterns, one of negative values is shifted by `2 ^ n`, and one with values of both signs is the
case split into the two (`memI_cases`), each checked on its own.

## Main results

* `noPanic_of_complete`, `noPanic_of_cover`: the argument at one valuation
* `aeneas_noPanic`: the argument for every argument of the function
* `memI`, `memI_neg`, `memI_cases`: the patterns of a signed argument in an interval
* `aeneasRange% f [I₁, …]`: the proof of
  `∀ xs, lo₁ ≤ x₁ ∧ x₁ ≤ hi₁ → … → ∃ y, f xs = .ok y` for the intervals `Iᵢ = (loᵢ, hiᵢ)`, or
  `_` for an argument without hypothesis; a refusal names the step that fails
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFRange
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyComplete (CompleteG)
open Ctxt (Var Valuation)

namespace RangeEntry

/-! ## The entry theorems -/

/-- **No panic at one valuation.** A computation `m` whose reading `p` is complete at `V`, with
    `p` free of `whileLoop` and accepted by the interval checker from an abstract environment
    that holds of `V`, has a value. -/
theorem noPanic_of_complete {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {m : RustM α} {Γ : Ctxt nfDialect} {V : Valuation Γ} {p : NFProg nfDialect Γ ts}
    {A : AEnv Γ} {B : AVals ts} (C : CompleteG E m V p) (hw : p.whileFree = true)
    (hc : check aeSpec A p = some B) (hV : A.Sat V) : ∃ y, m = .ok y := by
  obtain ⟨W, hW, -⟩ := check_sound' aeSpec_sound hc hV
  obtain ⟨y, hy, -⟩ := C W (nfToRustM_of_denote p hw (hW 0))
  exact ⟨y, hy⟩

/-- No panic at one valuation, with the acceptance of the checker as a Boolean. -/
theorem noPanic_of_isSome {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {m : RustM α} {Γ : Ctxt nfDialect} {V : Valuation Γ} {p : NFProg nfDialect Γ ts}
    {A : AEnv Γ} (C : CompleteG E m V p) (hw : p.whileFree = true)
    (hc : (check aeSpec A p).isSome = true) (hV : A.Sat V) : ∃ y, m = .ok y :=
  noPanic_of_complete C hw (Option.some_get hc).symm hV

/-- The number of checks of the interval checker on a subdivided range in the entry. -/
def coverBudget : Nat := 256

/-- No panic at one valuation, with the acceptance of the checker on the range of `A`
    subdivided within `n` checks (`checkCover`). -/
theorem noPanic_of_cover {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {m : RustM α} {Γ : Ctxt nfDialect} {V : Valuation Γ} {p : NFProg nfDialect Γ ts}
    {A : AEnv Γ} {n : Nat} (C : CompleteG E m V p) (hw : p.whileFree = true)
    (hc : checkCover aeSpec p n [A] = true) (hV : A.Sat V) : ∃ y, m = .ok y := by
  obtain ⟨W, hW⟩ := checkCover_sound aeSpec_sound n [A] hc A (List.mem_singleton_self A) hV
  obtain ⟨y, hy, -⟩ := C W (nfToRustM_of_denote p hw (hW 0))
  exact ⟨y, hy⟩

end RangeEntry

/-- **No panic of an Aeneas function on an input range.** For a reading `R` of `f` whose
    complete direction `C` holds at every argument, with `R.prog` free of `whileLoop` and
    accepted by the interval checker from `A`, `f` has a value at every argument whose
    valuation `A` holds of. -/
theorem aeneas_noPanic {ι α : Type} {Γ : Ctxt nfDialect} {t : NfTy}
    {S : NFProg nfDialect Γ [t] → Prop} (R : Reified S) {E : α → Valuation (d := nfDialect) [t]}
    {f : ι → RustM α} {V : ι → Valuation Γ} (C : ∀ xs, CompleteG E (f xs) (V xs) R.prog)
    (hw : R.prog.whileFree = true) {A : AEnv Γ} {B : AVals [t]}
    (hc : check aeSpec A R.prog = some B) : ∀ xs, A.Sat (V xs) → ∃ y, f xs = .ok y :=
  fun xs hV => RangeEntry.noPanic_of_complete (C xs) hw hc hV

namespace RangeEntry

/-! ## The abstract values of the arguments -/

/-- A word in `[lo, hi]` lies in the interval `(lo, hi)`. -/
theorem memU {ty : UScalarTy} [Le64 ty] (x : UScalar ty) (lo hi : Int)
    (h : lo ≤ (x.val : Int) ∧ (x.val : Int) ≤ hi) :
    AVal.Mem (.word 64) ((lo, hi) : Iv) (embW x) := by
  grind [AVal.Mem, Iv.Has, embW, BitVec.toNat_ofNat, lt64]

/-- A nonnegative signed word in `[lo, hi]` has its pattern in the interval `(lo, hi)`. -/
theorem memI {ity : IScalarTy} [Le64 (uOf ity)] (x : IScalar ity) (lo hi : Int) (h0 : 0 ≤ lo)
    (h : lo ≤ x.val ∧ x.val ≤ hi) :
    AVal.Mem (.word 64) ((lo, hi) : Iv) (embW (toU x)) := by
  have hb := lt64 (toU x)
  have e : ((toU x).val : Int) = x.val := by
    have h1 : (toU x).val = x.bv.toNat := rfl
    have h2 : x.val = x.bv.toInt := rfl
    rw [h2, BitVec.toInt_eq_toNat_cond] at h
    rw [h1, h2, BitVec.toInt_eq_toNat_cond]
    split <;> grind
  simp only [AVal.Mem, Iv.Has, embW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  omega

/-- The pattern of a signed word: its value, and its value plus `2 ^ n` when negative, at the
    width `n` of the type. -/
theorem toU_val_int {ity : IScalarTy} (x : IScalar ity) :
    ((toU x).val : Int) = if x.val < 0 then x.val + 2 ^ ity.numBits else x.val := by
  have h1 : (toU x).val = x.bv.toNat := rfl
  have h2 : x.val = x.bv.toInt := rfl
  have hl := x.bv.isLt
  rw [h1, h2, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> grind

/-- **A signed word in `[lo, hi]` has its pattern in one of two intervals**: the nonnegative
    values `[max lo 0, hi]`, or the negative values shifted by `2 ^ n`,
    `[lo + 2 ^ n, min hi (-1) + 2 ^ n]`, at the width `n` of the type. -/
theorem memI_cases {ity : IScalarTy} [Le64 (uOf ity)] (x : IScalar ity) (lo hi : Int)
    (h : lo ≤ x.val ∧ x.val ≤ hi) :
    AVal.Mem (.word 64) ((max lo 0, hi) : Iv) (embW (toU x)) ∨
      AVal.Mem (.word 64) ((lo + 2 ^ ity.numBits, min hi (-1) + 2 ^ ity.numBits) : Iv)
        (embW (toU x)) := by
  have hb := lt64 (toU x)
  have e := toU_val_int x
  simp only [AVal.Mem, Iv.Has, embW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  split at e <;> omega

/-- A negative signed word in `[lo, hi]` has its pattern in `[lo + 2 ^ n, hi + 2 ^ n]`, at the
    width `n` of the type. -/
theorem memI_neg {ity : IScalarTy} [Le64 (uOf ity)] (x : IScalar ity) (lo hi : Int)
    (h1 : hi < 0) (h : lo ≤ x.val ∧ x.val ≤ hi) :
    AVal.Mem (.word 64) ((lo + 2 ^ ity.numBits, hi + 2 ^ ity.numBits) : Iv)
      (embW (toU x)) := by
  have hb := lt64 (toU x)
  have e := toU_val_int x
  simp only [AVal.Mem, Iv.Has, embW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  split at e <;> omega

/-- A Boolean whose bit is in `[lo, hi]` has its word in the interval `(lo, hi)`. -/
theorem memB (b : Bool) (lo hi : Int) (h : lo ≤ (b.toNat : Int) ∧ (b.toNat : Int) ≤ hi) :
    AVal.Mem (.word 64) ((lo, hi) : Iv) (boolW b) := by
  cases b <;> grind [AVal.Mem, Iv.Has, boolW, BitVec.toNat_ofNat]

/-- An array of words in `[lo, hi]` has its element interval `(lo, hi)`. -/
theorem memA {ty : UScalarTy} [Le64 ty] {n : Usize} (a : Aeneas.Std.Array (UScalar ty) n)
    (lo hi : Int) (h : ∀ v ∈ a.val, lo ≤ (v.val : Int) ∧ (v.val : Int) ≤ hi) :
    AVal.Mem (.arr n.val (.word 64)) ((lo, hi) : Iv) (embA a) := by
  intro j
  exact memU _ lo hi (h _ (List.getElem_mem _))

/-- The empty abstract environment holds of the empty valuation. -/
theorem sat_nil : AEnv.Sat (Γ := []) .nil .nil := by
  grind [AEnv.sat_iff]

/-- An abstract environment with a word in front holds of a valuation with a word in front. -/
theorem sat_cons_word {w : Nat} {Γ : Ctxt nfDialect} (a : AVal (.word w)) (A : AEnv Γ)
    (x : BitVec w) (V : Valuation Γ) (ha : AVal.Mem (.word w) a x) (hA : A.Sat V) :
    AEnv.Sat (.cons a A) (.cons (t := .word w) x V) := by
  rw [AEnv.sat_iff] at hA ⊢
  exact ⟨⟨ha, trivial⟩, AVals.Ok.mono
    (fun _ hf => Fact.Holds.append (xs := [.word w]) (.cons x .nil) hf) hA⟩

/-- An abstract environment with an array in front holds of a valuation with an array in
    front. -/
theorem sat_cons_arr {n : Nat} {t : NfTy} {Γ : Ctxt nfDialect} (a : AVal (.arr n t))
    (A : AEnv Γ) (x : (NfTy.arr n t).denote) (V : Valuation Γ) (ha : AVal.Mem (.arr n t) a x)
    (hA : A.Sat V) : AEnv.Sat (.cons a A) (.cons (t := .arr n t) x V) := by
  rw [AEnv.sat_iff] at hA ⊢
  exact ⟨⟨ha, trivial⟩, AVals.Ok.mono (fun _ hf => Fact.Holds.append (.cons x .nil) hf) hA⟩

/-! ## The elaborator -/

namespace RangeMeta

open Lean Meta Elab Term

/-- The bounds `lo`, `hi` of an interval term `(lo, hi)`. -/
meta def boundsOf (stx : Term) : TermElabM (Expr × Expr) := do
  let ty ← mkAppM ``Prod #[mkConst ``Int, mkConst ``Int]
  let e ← elabTermEnsuringType stx (some ty)
  synthesizeSyntheticMVarsNoPostponing
  let e ← whnfR (← instantiateMVars e)
  unless e.isAppOfArity ``Prod.mk 4 do
    throwError "aeneasRange%: not an interval (lo, hi){indentExpr e}"
  return (e.getArg! 2, e.getArg! 3)

/-- The proof of `P` by evaluation, or the error `msg` when `P` evaluates to false. -/
meta def decideOr (P : Expr) (msg : MessageData) : MetaM Expr := do
  let d ← mkDecide P
  let r ← withAtLeastTransparency .default <| whnf d
  unless r.isConstOf ``Bool.true do throwError msg
  mkDecideProof P

/-- Whether `P` evaluates to true. -/
meta def decides (P : Expr) : MetaM Bool := do
  let r ← withAtLeastTransparency .default <| whnf (← mkDecide P)
  return r.isConstOf ``Bool.true

/-- The interval of the membership `AVal.Mem t a v`. -/
meta def ivOfMem (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  unless e.isAppOfArity ``AVal.Mem 3 do
    throwError "aeneasRange%: not a membership{indentExpr e}"
  return e.getArg! 1

/-- The membership lemma of an argument `x` in the interval `(lo, hi)`, by the type of `x`:
    the interval `a₁` and a proof of `∀ h : H, AVal.Mem t a₁ v` for the hypothesis `H` on `x`,
    or, for a signed `x` whose interval holds negative and nonnegative values, the intervals
    `a₁`, `a₂` of the nonnegative and the negative patterns and a proof of
    `∀ h : H, AVal.Mem t a₁ v ∨ AVal.Mem t a₂ v` (`memI_cases`). -/
meta def memOf (x lo hi : Expr) : MetaM (Expr × Option Expr × Expr) := do
  let ty ← whnfR (← inferType x)
  let iv ← mkAppM ``Prod.mk #[lo, hi]
  if ty.isConstOf ``Bool then return (iv, none, ← mkAppM ``memB #[x, lo, hi])
  if ty.isAppOf ``UScalar then return (iv, none, ← mkAppM ``memU #[x, lo, hi])
  if ty.isAppOf ``IScalar then
    let P0 ← mkAppM ``LE.le #[toExpr (0 : Int), lo]
    if ← decides P0 then
      return (iv, none, ← mkAppM ``memI #[x, lo, hi, ← mkDecideProof P0])
    let Pn ← mkAppM ``LT.lt #[hi, toExpr (0 : Int)]
    if ← decides Pn then
      let pf ← mkAppM ``memI_neg #[x, lo, hi, ← mkDecideProof Pn]
      let a ← forallTelescope (← inferType pf) fun _ b => ivOfMem b
      return (a, none, pf)
    let pf ← mkAppM ``memI_cases #[x, lo, hi]
    let (a₁, a₂) ← forallTelescope (← inferType pf) fun _ b => do
      let b ← whnfR b
      return (← ivOfMem (b.getArg! 0), ← ivOfMem (b.getArg! 1))
    return (a₁, some a₂, pf)
  if ty.isAppOf ``Aeneas.Std.Array then return (iv, none, ← mkAppM ``memA #[x, lo, hi])
  throwError "aeneasRange%: no interval reading of the argument {x} of type{indentExpr ty}"

/-- The entries of a valuation `vCons x₁ (… vNil)`: the type and the value of each. -/
meta partial def entries (V : Expr) : MetaM (Array (Expr × Expr)) := do
  let V ← whnfR V
  if V.isAppOfArity ``HVector.cons 6 then
    return #[(V.getArg! 2, V.getArg! 4)] ++ (← entries (V.getArg! 5))
  if V.isAppOfArity ``HVector.nil 2 then return #[]
  throwError "aeneasRange%: not a valuation of the arguments{indentExpr V}"

/-- The abstract environment `A` of the abstract values `as` at the types `ts`, with the proof
    of `A.Sat V` from the memberships `ms` of the entries `es` of `V`. -/
meta def envSat (es : List (Expr × Expr)) (as ms : List Expr) : MetaM (Expr × Expr × Expr) := do
  match es, as, ms with
  | [], [], [] =>
    let nil ← mkAppOptM ``HVector.nil #[mkConst ``NfTy, mkConst ``AVal]
    let vnil ← mkAppOptM ``HVector.nil #[mkConst ``NfTy, mkConst ``NfTy.denote]
    return (nil, vnil, mkConst ``sat_nil)
  | (t, v) :: es, a :: as, m :: ms =>
    let (A, V, hA) ← envSat es as ms
    let Γ ← mkListLit (mkConst ``NfTy) (es.map (·.1))
    let A' ← mkAppOptM ``HVector.cons #[mkConst ``NfTy, mkConst ``AVal, t, Γ, a, A]
    let V' ← mkAppOptM ``HVector.cons #[mkConst ``NfTy, mkConst ``NfTy.denote, t, Γ, v, V]
    let t ← whnf t
    let h ← if t.isAppOfArity ``NfTy.word 1 then
        mkAppOptM ``sat_cons_word #[t.getArg! 0, Γ, a, A, v, V, m, hA]
      else if t.isAppOfArity ``NfTy.arr 2 then
        mkAppOptM ``sat_cons_arr #[t.getArg! 0, t.getArg! 1, Γ, a, A, v, V, m, hA]
      else throwError "aeneasRange%: an argument of the type {t} is outside the entry"
    return (A', V', h)
  | _, _, _ => throwError "aeneasRange%: the arguments and the valuation differ in length"

/-- The reason the checker refuses `prog` from `A`, by evaluation, or a generic one. -/
meta def refusalOf (A prog : Expr) : TermElabM String := do
  try
    let e ← mkAppM ``NFRange.refusal #[mkConst ``NFRange.aeSpec, A, prog]
    let e ← mkAppM ``Option.getD #[e, toExpr "range check refused"]
    let n ← mkAuxDeclName `aeneasRangeRefusal
    let d := mkDefinitionValEx n [] (mkConst ``String) e ReducibilityHints.opaque
      DefinitionSafety.safe []
    addAndCompile (Declaration.defnDecl d)
    ofExcept <| unsafe (← getEnv).evalConst String (← getOptions) n (checkMeta := false)
  catch e => return s!"range check refused {← e.toMessageData.toString}"

/-- The value of the closed Boolean term `e`, by compiled evaluation; `false` when it does not
    compile. -/
meta def evalBool (e : Expr) : TermElabM Bool := do
  try
    let n ← mkAuxDeclName `aeneasRangeCover
    let d := mkDefinitionValEx n [] (mkConst ``Bool) e ReducibilityHints.opaque
      DefinitionSafety.safe []
    addAndCompile (Declaration.defnDecl d)
    ofExcept <| unsafe (← getEnv).evalConst Bool (← getOptions) n (checkMeta := false)
  catch _ => return false

/-- `aeneasRange% f [I₁, …]`: for the Aeneas function `f` with one interval `Iᵢ = (loᵢ, hiᵢ)`,
    or `_`, per argument, the proof of `∀ xs, H₁ → … → ∃ y, f xs = .ok y`, where `Hᵢ` states
    `loᵢ ≤ xᵢ ≤ hiᵢ` (of the value of a word, of the bit of a Boolean, of each element of an
    array). It reads `f` (`reifyAeneas%`), proves the reading complete (`completeAeneas%`),
    decides that the program is free of `whileLoop` and that the interval checker accepts it
    from the intervals, and applies `RangeEntry.noPanic_of_isSome`. Each failing step is a
    refusal that names it. -/
elab "aeneasRange% " f:ident " [" Is:term,* "]" : term => do
  let C ← try withoutErrToSorry <| elabTerm (← `(completeAeneas% (reifyAeneas% $f))) none
    catch e => throwError "aeneasRange%: the reading or its completeness refuses: {e.toMessageData}"
  let C ← instantiateMVars C
  forallTelescope (← inferType C) fun xs body => do
    unless body.isAppOfArity ``CompleteG 7 do
      throwError "aeneasRange%: not a completeness statement{indentExpr body}"
    let V := body.getArg! 5
    let prog := body.getArg! 6
    let Is := Is.getElems
    unless Is.size == xs.size do
      throwError "aeneasRange%: {Is.size} intervals for {xs.size} arguments"
    let es ← entries V
    unless es.size == xs.size do
      throwError "aeneasRange%: an argument is not one entry of the valuation (a structure)"
    let hw ← decideOr (← mkEq (← mkAppM ``NFProg.whileFree #[prog]) (toExpr true))
      m!"aeneasRange%: the program has an exit-flag loop (whileLoop)"
    -- per argument: its abstract value `a₁`, a second one `a₂` when its hypothesis gives one
    -- of two memberships, the membership proof or the lemma that gives it from the hypothesis,
    -- and whether there is a hypothesis
    let mut mems : Array (Expr × Option Expr × Expr × Bool) := #[]
    for x in xs, I in Is, (t, v) in es do
      if I.raw.isOfKind ``Lean.Parser.Term.hole then
        mems := mems.push (← mkAppM ``AVal.top #[t], none, ← mkAppM ``AVal.mem_top #[t, v],
          false)
      else
        let (lo, hi) ← boundsOf I
        let (a₁, a₂, pf) ← memOf x lo hi
        mems := mems.push (a₁, a₂, pf, true)
    let rec go (rest : List (Expr × Option Expr × Expr × Bool)) (as ms : List Expr) :
        TermElabM Expr := do
      match rest with
      | (a, _, m, false) :: rest => go rest (as ++ [a]) (ms ++ [m])
      | (a, none, pf, true) :: rest =>
        let H := (← whnfR (← inferType pf)).bindingDomain!
        withLocalDeclD `h H fun h => do
          mkLambdaFVars #[h] (← go rest (as ++ [a]) (ms ++ [mkApp pf h]))
      | (a₁, some a₂, pf, true) :: rest =>
        let H := (← whnfR (← inferType pf)).bindingDomain!
        withLocalDeclD `h H fun h => do
          let hor := mkApp pf h
          let orTy ← whnfR (← inferType hor)
          let l ← withLocalDeclD `m (orTy.getArg! 0) fun m => do
            mkLambdaFVars #[m] (← go rest (as ++ [a₁]) (ms ++ [m]))
          let r ← withLocalDeclD `m (orTy.getArg! 1) fun m => do
            mkLambdaFVars #[m] (← go rest (as ++ [a₂]) (ms ++ [m]))
          mkLambdaFVars #[h] (← mkAppM ``Or.elim #[hor, l, r])
      | [] =>
        let (A, _, sat) ← envSat es.toList as ms
        let P ← mkEq (← mkAppM ``NFRange.checkCover #[mkConst ``NFRange.aeSpec, prog,
          mkConst ``coverBudget, ← mkListLit (← inferType A) [A]]) (toExpr true)
        unless ← evalBool P.appFn!.appArg! do
          throwError "aeneasRange%: the interval check refuses: {← refusalOf A prog}"
        mkAppM ``noPanic_of_cover #[mkAppN C xs, hw, ← mkDecideProof P, sat]
    let prf ← go mems.toList [] []
    mkLambdaFVars xs prf

end RangeMeta

end RangeEntry

end CatCrypt.Crypto.SecureCompilation.AeneasFront
