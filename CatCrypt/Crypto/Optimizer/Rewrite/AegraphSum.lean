/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphField
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
public import Std.Data.HashMap.AdditionalOperations

/-!
# Rule sets and leakage models on an operation sum of dialects

For two dialects `⟨O₁, T⟩` and `⟨O₂, T⟩` over a shared type alphabet `T`, the rule sets of
the generic acyclic e-graph (`AegraphGeneric.RuleSet`) and the leakage models
(`ComLevelCheck.LeakModel`) of the summands give those of the operation sum
`Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩`.

A rule of the left summand, lifted to the sum (`ruleInl`), fires on an expression of the
sum only when its operation is tagged `.inl`; it reads the expression as one of the
summand (`projL`) and the definition table of the sum restricted to its `.inl` entries
(`restrictL`), and returns its alternatives included into the sum (`altInl`). Its
soundness is the rule's own soundness: the restricted table is sound whenever the table
of the sum is (`dsound_restrictL`), and inclusion preserves denotation (`altInl_denote`).
The right summand is symmetric. The cost, the extraction weight and the merge predicate
of a combined rule set (`sumRules`) are case splits on the tag; `inlRules R` combines `R`
with the rule set `idleRules`, which has no rules and merges no binding, so the
operations of the other summand are left as they are.

The leakage model of the sum (`leakSum`) takes the event class of an operation from its
summand. Both summands read values of the shared alphabet `T`, and `LeakModel.valNat` is
a reading per type, not per operation, so the sum takes the reading of the left model;
the right summand's events are its own when the two readings agree.

## Main definitions

* `ruleInl`, `ruleInr`: a rule of a summand as a rule of the sum.
* `sumRules`, `inlRules`, `inrRules`: rule sets of the sum.
* `leakSum`: the leakage model of the sum.

## Main results

* `rulesIndep_sumRules`, `rulesIndep_inlRules`, `rulesIndep_inrRules`: `RulesIndep` for
  the rule sets of the sum, from that of the summands.
* `Witness.mixedOpt_denote`, `Witness.mixedOpt_constantTime`: the field rule set lifted to
  the sum of `fieldDialect` with a two-operation dialect, applied by `aegraphOptOf`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphSum

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

variable {O₁ O₂ T : Type}

/-! ## 1. Expressions and alternatives along the inclusions -/

section Embed

variable [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)]

/-- An expression of the left summand as an expression of the operation sum. -/
def inlExpr {Δ : List T} {s : T} (e : Expr ⟨O₁, T⟩ Δ s) :
    Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s :=
  { op := .inl e.op, retTy_eq := e.retTy_eq, args := castArgs e.args }

/-- An expression of the right summand as an expression of the operation sum. -/
def inrExpr {Δ : List T} {s : T} (e : Expr ⟨O₂, T⟩ Δ s) :
    Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s :=
  { op := .inr e.op, retTy_eq := e.retTy_eq, args := castArgs e.args }

/-- An expression of the sum whose operation is tagged `.inl`, as an expression of the
    left summand. -/
def projL {Δ : List T} {s : T} :
    Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s → Option (Expr ⟨O₁, T⟩ Δ s)
  | ⟨.inl o, h, args⟩ => some ⟨o, h, castArgs args⟩
  | ⟨.inr _, _, _⟩ => none

/-- An expression of the sum whose operation is tagged `.inr`, as an expression of the
    right summand. -/
def projR {Δ : List T} {s : T} :
    Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s → Option (Expr ⟨O₂, T⟩ Δ s)
  | ⟨.inl _, _, _⟩ => none
  | ⟨.inr o, h, args⟩ => some ⟨o, h, castArgs args⟩

/-- An alternative of the left summand as an alternative of the sum. -/
def altInl {Δ : List T} {s : T} :
    Alt (d := ⟨O₁, T⟩) Δ s → Alt (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s
  | .var v => .var (castVar v)
  | .one e => .one (inlExpr e)
  | .two e1 e2 => .two (inlExpr e1) (inlExpr e2)

/-- An alternative of the right summand as an alternative of the sum. -/
def altInr {Δ : List T} {s : T} :
    Alt (d := ⟨O₂, T⟩) Δ s → Alt (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s
  | .var v => .var (castVar v)
  | .one e => .one (inrExpr e)
  | .two e1 e2 => .two (inrExpr e1) (inrExpr e2)

variable [TyDenote T] [DialectDenote (⟨O₁, T⟩ : Dialect)] [DialectDenote (⟨O₂, T⟩ : Dialect)]

theorem inlExpr_denote {Δ : List T} {s : T} (e : Expr ⟨O₁, T⟩ Δ s)
    (V : Ctxt.Valuation (d := ⟨O₁, T⟩) Δ) :
    (inlExpr (O₂ := O₂) e).denote V = e.denote V := by
  obtain ⟨op, rfl, args⟩ := e
  show DialectDenote.denote (d := ⟨O₁, T⟩) op
      (Expr.lookupArgs (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (castArgs args) V) = _
  rw [lookupArgs_castArgs args V]
  rfl

theorem inrExpr_denote {Δ : List T} {s : T} (e : Expr ⟨O₂, T⟩ Δ s)
    (V : Ctxt.Valuation (d := ⟨O₂, T⟩) Δ) :
    (inrExpr (O₁ := O₁) e).denote V = e.denote V := by
  obtain ⟨op, rfl, args⟩ := e
  show DialectDenote.denote (d := ⟨O₂, T⟩) op
      (Expr.lookupArgs (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (castArgs args) V) = _
  rw [lookupArgs_castArgs args V]
  rfl

theorem altInl_denote {Δ : List T} {s : T} (a : Alt (d := ⟨O₁, T⟩) Δ s)
    (V : Ctxt.Valuation (d := ⟨O₁, T⟩) Δ) :
    (altInl (O₂ := O₂) a).denote V = a.denote V := by
  cases a with
  | var v => exact lookup_castVar v V
  | one e => exact inlExpr_denote e V
  | two e1 e2 =>
      show (inlExpr e2).denote (V.extend ((inlExpr e1).denote V)) = _
      rw [inlExpr_denote, inlExpr_denote]
      rfl

theorem altInr_denote {Δ : List T} {s : T} (a : Alt (d := ⟨O₂, T⟩) Δ s)
    (V : Ctxt.Valuation (d := ⟨O₂, T⟩) Δ) :
    (altInr (O₁ := O₁) a).denote V = a.denote V := by
  cases a with
  | var v => exact lookup_castVar v V
  | one e => exact inrExpr_denote e V
  | two e1 e2 =>
      show (inrExpr e2).denote (V.extend ((inrExpr e1).denote V)) = _
      rw [inrExpr_denote, inrExpr_denote]
      rfl

theorem projL_denote {Δ : List T} {s : T} {e : Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s}
    {e' : Expr ⟨O₁, T⟩ Δ s} (h : projL e = some e') (V : Ctxt.Valuation (d := ⟨O₁, T⟩) Δ) :
    e'.denote V = e.denote V := by
  obtain ⟨op, hop, args⟩ := e
  cases op with
  | inl o =>
      cases h
      cases hop
      show DialectDenote.denote (d := ⟨O₁, T⟩) o
          (Expr.lookupArgs (d := ⟨O₁, T⟩) (castArgs args) V) = _
      rw [lookupArgs_castArgs args V]
      rfl
  | inr o => cases h

theorem projR_denote {Δ : List T} {s : T} {e : Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s}
    {e' : Expr ⟨O₂, T⟩ Δ s} (h : projR e = some e') (V : Ctxt.Valuation (d := ⟨O₂, T⟩) Δ) :
    e'.denote V = e.denote V := by
  obtain ⟨op, hop, args⟩ := e
  cases op with
  | inl o => cases h
  | inr o =>
      cases h
      cases hop
      show DialectDenote.denote (d := ⟨O₂, T⟩) o
          (Expr.lookupArgs (d := ⟨O₂, T⟩) (castArgs args) V) = _
      rw [lookupArgs_castArgs args V]
      rfl

end Embed

/-! ## 2. The definition table of a summand -/

section Restrict

/-- The definition table of the left summand: the entries of a table of the sum whose
    operation is tagged `.inl`. -/
def restrictL (D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)) : Defs ⟨O₁, T⟩ :=
  D.filterMap fun _ p => match p.1 with
    | .inl o => some (o, p.2)
    | .inr _ => none

/-- The definition table of the right summand: the entries of a table of the sum whose
    operation is tagged `.inr`. -/
def restrictR (D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)) : Defs ⟨O₂, T⟩ :=
  D.filterMap fun _ p => match p.1 with
    | .inl _ => none
    | .inr o => some (o, p.2)

theorem restrictL_getElem? {D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)} {l : Nat}
    {p : O₁ × List Nat} (h : (restrictL D)[l]? = some p) : D[l]? = some (.inl p.1, p.2) := by
  simp only [restrictL, Std.HashMap.getElem?_filterMap] at h
  rcases hD : D[l]? with _ | ⟨op, lv⟩ <;> simp [hD] at h
  rcases op with o | o <;> simp at h
  obtain rfl := h
  rfl

theorem restrictR_getElem? {D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)} {l : Nat}
    {p : O₂ × List Nat} (h : (restrictR D)[l]? = some p) : D[l]? = some (.inr p.1, p.2) := by
  simp only [restrictR, Std.HashMap.getElem?_filterMap] at h
  rcases hD : D[l]? with _ | ⟨op, lv⟩ <;> simp [hD] at h
  rcases op with o | o <;> simp at h
  obtain rfl := h
  rfl

variable [TyDenote T]

/-- Reading a valuation at a de Bruijn index does not depend on the operations of the
    dialect. -/
theorem getDepth_congr {O O' : Type} : ∀ {Γ : List T} (V : Ctxt.Valuation (d := ⟨O, T⟩) Γ)
    (k : Nat), getDepth (d := ⟨O, T⟩) V k = getDepth (d := ⟨O', T⟩) V k
  | [], .nil, _ => rfl
  | _ :: _, .cons _ _, 0 => rfl
  | _ :: _, .cons _ V, k + 1 => getDepth_congr (O' := O') V k

/-- Reading a valuation at a level does not depend on the operations of the dialect. -/
theorem getLvl_congr {O O' : Type} {Γ : List T} (V : Ctxt.Valuation (d := ⟨O, T⟩) Γ)
    (l : Nat) : getLvl (d := ⟨O, T⟩) V l = getLvl (d := ⟨O', T⟩) V l := by
  unfold getLvl
  rw [getDepth_congr (O' := O')]

variable [DecidableEq T]

/-- Gathering argument values does not depend on the operations of the dialect. -/
theorem gatherArgs_congr {O O' : Type} {Γ : List T} (V : Ctxt.Valuation (d := ⟨O, T⟩) Γ) :
    ∀ (tys : List T) (ls : List Nat),
      gatherArgs (d := ⟨O, T⟩) V tys ls = gatherArgs (d := ⟨O', T⟩) V tys ls
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | ty :: tys, l :: ls => by
      simp only [gatherArgs]
      rw [getLvl_congr (O' := O') V l, gatherArgs_congr (O' := O') V tys ls]
      simp only [castTo?]
      cases (getLvl (d := ⟨O', T⟩) V l).bind
          fun x => if h : x.fst = ty then some (h ▸ x.snd) else none <;>
        cases gatherArgs (d := ⟨O', T⟩) V tys ls <;> rfl

variable [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)]
  [DialectDenote (⟨O₁, T⟩ : Dialect)] [DialectDenote (⟨O₂, T⟩ : Dialect)]

theorem evalKey_inl {Γ : List T} (V : Ctxt.Valuation (d := ⟨O₁, T⟩) Γ) (o : O₁)
    (lv : List Nat) :
    evalKey (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) V (.inl o) lv = evalKey V o lv := by
  unfold evalKey
  exact congrArg (Option.map _)
    (gatherArgs_congr (O := O₁ ⊕ O₂) (O' := O₁) V (DialectSignature.sig (d := ⟨O₁, T⟩) o) lv)

theorem evalKey_inr {Γ : List T} (V : Ctxt.Valuation (d := ⟨O₂, T⟩) Γ) (o : O₂)
    (lv : List Nat) :
    evalKey (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) V (.inr o) lv = evalKey V o lv := by
  unfold evalKey
  exact congrArg (Option.map _)
    (gatherArgs_congr (O := O₁ ⊕ O₂) (O' := O₂) V (DialectSignature.sig (d := ⟨O₂, T⟩) o) lv)

/-- The restriction of a sound definition table of the sum to the left summand is sound. -/
theorem dsound_restrictL {Γ : List T} {V : Ctxt.Valuation (d := ⟨O₁, T⟩) Γ}
    {D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)}
    (hD : DSound (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) V D) : DSound V (restrictL D) := by
  intro l p h
  obtain ⟨x, h1, h2⟩ := hD l _ (restrictL_getElem? h)
  exact ⟨x, (evalKey_inl V p.1 p.2).symm.trans h1,
    (getLvl_congr (O := O₁) (O' := O₁ ⊕ O₂) V l).trans h2⟩

/-- The restriction of a sound definition table of the sum to the right summand is
    sound. -/
theorem dsound_restrictR {Γ : List T} {V : Ctxt.Valuation (d := ⟨O₂, T⟩) Γ}
    {D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)}
    (hD : DSound (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) V D) : DSound V (restrictR D) := by
  intro l p h
  obtain ⟨x, h1, h2⟩ := hD l _ (restrictR_getElem? h)
  exact ⟨x, (evalKey_inr V p.1 p.2).symm.trans h1,
    (getLvl_congr (O := O₂) (O' := O₁ ⊕ O₂) V l).trans h2⟩

end Restrict

/-! ## 3. Rules and rule sets of the sum -/

section Rules

variable [TyDenote T] [DecidableEq T]
  [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)]
  [DialectDenote (⟨O₁, T⟩ : Dialect)] [DialectDenote (⟨O₂, T⟩ : Dialect)]

/-- The alternatives of a rule of the left summand on an expression of the sum: none when
    the operation is tagged `.inr`, otherwise those of the rule on the expression read in
    the summand, under the `.inl` entries of the definition table, included into the
    sum. -/
def applyInl (r : Rule ⟨O₁, T⟩) (D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)) {Δ : List T}
    {s : T} (e : Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s) :
    List (Alt (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s) :=
  match projL e with
  | some e' => (r.apply (restrictL D) e').map altInl
  | none => []

/-- The alternatives of a rule of the right summand on an expression of the sum. -/
def applyInr (r : Rule ⟨O₂, T⟩) (D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)) {Δ : List T}
    {s : T} (e : Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s) :
    List (Alt (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s) :=
  match projR e with
  | some e' => (r.apply (restrictR D) e').map altInr
  | none => []

omit [DialectDenote (⟨O₂, T⟩ : Dialect)] in
theorem mem_applyInl {r : Rule ⟨O₁, T⟩} {D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)}
    {Δ : List T} {s : T} {e : Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s}
    {a : Alt (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s} (h : a ∈ applyInl r D e) :
    ∃ e', projL e = some e' ∧ ∃ a' ∈ r.apply (restrictL D) e', a = altInl a' := by
  unfold applyInl at h
  split at h
  · rename_i e' he
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp h
    exact ⟨e', he, a', ha', rfl⟩
  · simp at h

omit [DialectDenote (⟨O₁, T⟩ : Dialect)] in
theorem mem_applyInr {r : Rule ⟨O₂, T⟩} {D : Defs (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩)}
    {Δ : List T} {s : T} {e : Expr (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s}
    {a : Alt (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) Δ s} (h : a ∈ applyInr r D e) :
    ∃ e', projR e = some e' ∧ ∃ a' ∈ r.apply (restrictR D) e', a = altInr a' := by
  unfold applyInr at h
  split at h
  · rename_i e' he
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp h
    exact ⟨e', he, a', ha', rfl⟩
  · simp at h

/-- **A rule of the left summand as a rule of the sum.** It fires only on operations tagged
    `.inl`, reads the `.inl` entries of the definition table (`restrictL`), and its
    soundness is that of `r`. -/
def ruleInl (r : Rule ⟨O₁, T⟩) : Rule (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) where
  apply D _ _ e := applyInl r D e
  sound D Δ V hD s e a ha := by
    obtain ⟨e', he, a', ha', rfl⟩ := mem_applyInl ha
    rw [altInl_denote, r.sound _ V (dsound_restrictL hD) e' a' ha', projL_denote he]

/-- **A rule of the right summand as a rule of the sum.** It fires only on operations
    tagged `.inr`, reads the `.inr` entries of the definition table (`restrictR`), and its
    soundness is that of `r`. -/
def ruleInr (r : Rule ⟨O₂, T⟩) : Rule (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) where
  apply D _ _ e := applyInr r D e
  sound D Δ V hD s e a ha := by
    obtain ⟨e', he, a', ha', rfl⟩ := mem_applyInr ha
    rw [altInr_denote, r.sound _ V (dsound_restrictR hD) e' a' ha', projR_denote he]

/-- **The combined rule set** of the sum: the rules of both summands, each lifted, over the
    operation traits of the sum (`OpTraits.opSum`), which take every trait of an operation
    from its summand. -/
def sumRules (R₁ : RuleSet ⟨O₁, T⟩) (R₂ : RuleSet ⟨O₂, T⟩) :
    RuleSet (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) where
  toOpTraits := R₁.toOpTraits.opSum R₂.toOpTraits
  rules := R₁.rules.map ruleInl ++ R₂.rules.map ruleInr

/-- The rule set with no rules over the operation traits `OpTraits.idle`: it merges no
    binding, and each operation has cost one and extraction weight three. -/
def idleRules (O : Type) [DialectSignature (⟨O, T⟩ : Dialect)]
    [DialectDenote (⟨O, T⟩ : Dialect)] : RuleSet ⟨O, T⟩ where
  toOpTraits := OpTraits.idle _
  rules := []

/-- **A rule set of the left summand as a rule set of the sum**: the operations of the
    right summand are neither rewritten nor merged. -/
def inlRules (R : RuleSet ⟨O₁, T⟩) : RuleSet (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) :=
  sumRules R (idleRules O₂)

/-- **A rule set of the right summand as a rule set of the sum**: the operations of the
    left summand are neither rewritten nor merged. -/
def inrRules (R : RuleSet ⟨O₂, T⟩) : RuleSet (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) :=
  sumRules (idleRules O₁) R

end Rules

/-! ## 4. The leakage model of the sum -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

variable [TyDenote T] [DialectSignature (⟨O₁, T⟩ : Dialect)]
  [DialectSignature (⟨O₂, T⟩ : Dialect)]

/-- **The leakage model of the sum**: the event class of an operation is that of its
    summand; values are read by the reading of the left model. -/
def leakSum (L₁ : LeakModel ⟨O₁, T⟩) (L₂ : LeakModel ⟨O₂, T⟩) :
    LeakModel (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) where
  kind := Sum.elim L₁.kind L₂.kind
  valNat := L₁.valNat

omit [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)] in
/-- The readings of a list of values agree under two leakage models with the same reading
    of values. -/
theorem valsNat_congr {O O' : Type} [DialectSignature (⟨O, T⟩ : Dialect)]
    [DialectSignature (⟨O', T⟩ : Dialect)] (M : LeakModel ⟨O, T⟩) (M' : LeakModel ⟨O', T⟩)
    (hv : M.valNat = M'.valNat) :
    ∀ {tys : List T} (vals : HVector (fun t => ⟦t⟧) tys), valsNat M vals = valsNat M' vals
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show M.valNat _ v :: valsNat M rest = M'.valNat _ v :: valsNat M' rest
      rw [hv, valsNat_congr M M' hv rest]

/-- The events of an included left expression are its events in the left summand. -/
theorem ctLeak_inlExpr (L₁ : LeakModel ⟨O₁, T⟩) (L₂ : LeakModel ⟨O₂, T⟩) {Δ : List T}
    {s : T} (e : Expr ⟨O₁, T⟩ Δ s) (V : Ctxt.Valuation (d := ⟨O₁, T⟩) Δ) :
    Expr.ctLeak (leakSum L₁ L₂) (inlExpr e) V = Expr.ctLeak L₁ e V := by
  obtain ⟨op, h, args⟩ := e
  simp only [Expr.ctLeak, inlExpr]
  rw [lookupArgs_castArgs args V]
  unfold opLeak
  rw [valsNat_congr (leakSum L₁ L₂) L₁ rfl]
  rfl

/-- The events of an included right expression are its events in the right summand, when
    the two models read values alike. -/
theorem ctLeak_inrExpr (L₁ : LeakModel ⟨O₁, T⟩) (L₂ : LeakModel ⟨O₂, T⟩)
    (hv : L₁.valNat = L₂.valNat) {Δ : List T} {s : T} (e : Expr ⟨O₂, T⟩ Δ s)
    (V : Ctxt.Valuation (d := ⟨O₂, T⟩) Δ) :
    Expr.ctLeak (leakSum L₁ L₂) (inrExpr e) V = Expr.ctLeak L₂ e V := by
  obtain ⟨op, h, args⟩ := e
  simp only [Expr.ctLeak, inrExpr]
  rw [lookupArgs_castArgs args V]
  unfold opLeak
  rw [valsNat_congr (leakSum L₁ L₂) L₂ hv]
  rfl

theorem indep_altInl (L₁ : LeakModel ⟨O₁, T⟩) (L₂ : LeakModel ⟨O₂, T⟩) {Δ : List T}
    {s : T} (a : Alt (d := ⟨O₁, T⟩) Δ s) (h : a.Indep L₁) :
    (altInl (O₂ := O₂) a).Indep (leakSum L₁ L₂) := by
  cases a with
  | var v => trivial
  | one e =>
      intro V₁ V₂
      rw [ctLeak_inlExpr, ctLeak_inlExpr]
      exact h V₁ V₂
  | two e1 e2 =>
      refine ⟨fun V₁ V₂ => ?_, fun V₁ V₂ => ?_⟩
      · rw [ctLeak_inlExpr, ctLeak_inlExpr]
        exact h.1 V₁ V₂
      · rw [ctLeak_inlExpr, ctLeak_inlExpr]
        exact h.2 V₁ V₂

theorem indep_altInr (L₁ : LeakModel ⟨O₁, T⟩) (L₂ : LeakModel ⟨O₂, T⟩)
    (hv : L₁.valNat = L₂.valNat) {Δ : List T} {s : T} (a : Alt (d := ⟨O₂, T⟩) Δ s)
    (h : a.Indep L₂) : (altInr (O₁ := O₁) a).Indep (leakSum L₁ L₂) := by
  cases a with
  | var v => trivial
  | one e =>
      intro V₁ V₂
      rw [ctLeak_inrExpr L₁ L₂ hv, ctLeak_inrExpr L₁ L₂ hv]
      exact h V₁ V₂
  | two e1 e2 =>
      refine ⟨fun V₁ V₂ => ?_, fun V₁ V₂ => ?_⟩
      · rw [ctLeak_inrExpr L₁ L₂ hv, ctLeak_inrExpr L₁ L₂ hv]
        exact h.1 V₁ V₂
      · rw [ctLeak_inrExpr L₁ L₂ hv, ctLeak_inrExpr L₁ L₂ hv]
        exact h.2 V₁ V₂

variable [DecidableEq T] [DialectDenote (⟨O₁, T⟩ : Dialect)]
  [DialectDenote (⟨O₂, T⟩ : Dialect)]

/-- **Independence of the combined rule set** from that of the summands, when the two
    leakage models read values alike. -/
theorem rulesIndep_sumRules {L₁ : LeakModel ⟨O₁, T⟩} {L₂ : LeakModel ⟨O₂, T⟩}
    {R₁ : RuleSet ⟨O₁, T⟩} {R₂ : RuleSet ⟨O₂, T⟩} (h₁ : RulesIndep L₁ R₁)
    (h₂ : RulesIndep L₂ R₂) (hv : L₁.valNat = L₂.valNat) :
    RulesIndep (leakSum L₁ L₂) (sumRules R₁ R₂) := by
  intro D Δ s e alt h
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r₁, hr₁, rfl⟩ := List.mem_map.mp hr
    obtain ⟨e', -, a', ha', rfl⟩ := mem_applyInl ha
    exact indep_altInl L₁ L₂ a' (h₁ _ e' a' (List.mem_flatMap.mpr ⟨r₁, hr₁, ha'⟩))
  · obtain ⟨r₂, hr₂, rfl⟩ := List.mem_map.mp hr
    obtain ⟨e', -, a', ha', rfl⟩ := mem_applyInr ha
    exact indep_altInr L₁ L₂ hv a' (h₂ _ e' a' (List.mem_flatMap.mpr ⟨r₂, hr₂, ha'⟩))

/-- **Independence of a lifted left rule set** from that of the summand, for every
    leakage model of the right summand. -/
theorem rulesIndep_inlRules {L₁ : LeakModel ⟨O₁, T⟩} (L₂ : LeakModel ⟨O₂, T⟩)
    {R : RuleSet ⟨O₁, T⟩} (h : RulesIndep L₁ R) :
    RulesIndep (leakSum L₁ L₂) (inlRules (O₂ := O₂) R) := by
  intro D Δ s e alt hm
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp hm
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r₁, hr₁, rfl⟩ := List.mem_map.mp hr
    obtain ⟨e', -, a', ha', rfl⟩ := mem_applyInl ha
    exact indep_altInl L₁ L₂ a' (h _ e' a' (List.mem_flatMap.mpr ⟨r₁, hr₁, ha'⟩))
  · simp [idleRules] at hr

/-- **Independence of a lifted right rule set** from that of the summand, when the two
    leakage models read values alike. -/
theorem rulesIndep_inrRules (L₁ : LeakModel ⟨O₁, T⟩) {L₂ : LeakModel ⟨O₂, T⟩}
    {R : RuleSet ⟨O₂, T⟩} (h : RulesIndep L₂ R) (hv : L₁.valNat = L₂.valNat) :
    RulesIndep (leakSum L₁ L₂) (inrRules (O₁ := O₁) R) := by
  intro D Δ s e alt hm
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp hm
  rcases List.mem_append.mp hr with hr | hr
  · simp [idleRules] at hr
  · obtain ⟨r₂, hr₂, rfl⟩ := List.mem_map.mp hr
    obtain ⟨e', -, a', ha', rfl⟩ := mem_applyInr ha
    exact indep_altInr L₁ L₂ hv a' (h _ e' a' (List.mem_flatMap.mpr ⟨r₂, hr₂, ha'⟩))

end Leak

/-! ## 5. The field rule set on a sum with `fieldDialect`

A two-operation dialect over `FieldTy`, summed with `fieldDialect`. In the program below a
field addition consumes the result of a doubling of the second summand and a field
constant zero; the field rule `x + 0 = x` of `AegraphField.fieldRules`, lifted by
`inlRules`, applies to it. -/

namespace Witness

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphField (fieldRules fieldRules_indep)

/-- The operations of the test dialect. -/
inductive DblOp where
  /-- Doubling in `ZMod p`. -/
  | dbl (p : Nat)
  /-- Squaring in `ZMod p`. -/
  | sq (p : Nat)
  deriving DecidableEq

/-- The test dialect: `Op` is `DblOp`, `Ty` is `FieldTy`. -/
@[reducible] def dblDialect : Dialect := { Op := DblOp, Ty := FieldTy }

instance : DialectSignature dblDialect where
  sig
    | .dbl p => [.fp p]
    | .sq p => [.fp p]
  ret
    | .dbl p => .fp p
    | .sq p => .fp p

instance : DialectDenote dblDialect where
  denote
    | .dbl p => fun args =>
        let a : ZMod p := args.head
        a + a
    | .sq p => fun args =>
        let a : ZMod p := args.head
        a * a

/-- The operation sum of `fieldDialect` and the test dialect. -/
@[reducible] def mixedDialect : Dialect := Dialect.opSum fieldDialect dblDialect

/-- A three-binding program over the operation sum, with one `fp p` input `x`:

    ```
    let z : fp p = inl (fConst p 0)
    let y : fp p = inr (dbl p) x
    let w : fp p = inl (fAdd p) y z
    ret w
    ``` -/
def mixedProg (p : Nat) : Com mixedDialect [FieldTy.fp p] (FieldTy.fp p) :=
  .var (t := FieldTy.fp p) ⟨.inl (.fConst p 0), rfl, .nil⟩
    (.var (t := FieldTy.fp p) ⟨.inr (.dbl p), rfl, .cons (.there .here) .nil⟩
      (.var (t := FieldTy.fp p) ⟨.inl (.fAdd p), rfl, .cons .here (.cons (.there .here) .nil)⟩
        (.ret .here)))

/-- `mixedProg p` denotes `x + x + 0`. -/
theorem mixedProg_denote (p : Nat) (x : ZMod p) :
    (mixedProg p).denote (.cons x .nil) = x + x + 0 := rfl

/-- The field rule set lifted to the sum. -/
def mixedRules : RuleSet mixedDialect := inlRules fieldRules

/-- **Denotation of the pass on the mixed program**, the instance of
    `aegraphOptOf_denote` at the lifted field rule set. -/
theorem mixedOpt_denote (p : Nat) :
    (aegraphOptOf mixedRules (mixedProg p)).denote = (mixedProg p).denote :=
  aegraphOptOf_denote mixedRules (mixedProg p)

/-- **Constant time of the pass on the sum**: for leakage models of both summands, the
    lifted field rule set preserves constant time under the leakage model of the sum,
    the instance of `aegraphOptOf_constantTime`. -/
theorem mixedOpt_constantTime (L₁ : LeakModel fieldDialect) (L₂ : LeakModel dblDialect)
    {Γ : Ctxt mixedDialect} {t : FieldTy} (c : Com mixedDialect Γ t)
    (P : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime P (Com.ctLeak (leakSum L₁ L₂) c)) :
    ConstantTime P (Com.ctLeak (leakSum L₁ L₂) (aegraphOptOf mixedRules c)) :=
  aegraphOptOf_constantTime mixedRules (rulesIndep_inlRules L₂ fieldRules_indep) c P h

end Witness

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphSum
