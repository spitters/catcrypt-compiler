/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.UnitarySoundFull
public meta import CatCrypt.Quantum.Optimization.UnitarySoundFull

/-!
# A single left-to-right template pass

`templatePass ts gs` rewrites a gate list with the templates of a family
`ts : Gate n → List (Template n)`, where `ts g` lists the templates whose pattern
may end with the gate `g`. The pass keeps a stack of processed gates, most
recent first. It pushes the next input gate `g` and looks for a template of
`ts g` whose reversed pattern is a prefix of the stack. On a match it pops the
pattern and puts the replacement in front of the remaining input, so the
replacement gates pass through the same check and a rewrite that exposes a new
match (`H X X H`) is found without a rescan from the start.

A template is applied only when its replacement is shorter than its pattern.
The pass terminates by the lexicographic measure (stack length plus input
length, input length), with no fuel.

## Main definitions

* `CTemplate`, `compileTemplate` — a template as its reversed pattern gate list and
  its replacement gate list, computed once per template; the pass matches against
  this form, so each stack position costs only the prefix comparisons.
* `matchStackC`, `matchStack` — the first template of a list that matches the top
  of the stack.
* `templatePassAuxC`, `compiledPass`, `compiledPassC` — the pass with a compiled
  family; `templatePassAux`, `templatePass`, `templatePassC` — the pass with a
  template family, compiled at each gate.
* `level1Family` — the family selecting single-qubit templates by the qubit of
  a one-qubit gate and two-qubit templates by the qubits of a `CNOT`.
* `level1Table`, `level1Pass` — the Level 1 family with the single-qubit templates
  of all qubits compiled once into an array, and the pass over it.

## Main results

* `unitaryDenote_templatePass` — the pass preserves `unitaryDenote` when every
  template of the family is `CorrectU`.
* `length_templatePass_le`, `gateCount_templatePass_le` — the output has at
  most as many gates as the input.
* `level1Pass_eq` — the Level 1 pass is the template pass of `level1Family`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.TemplateMatching
open CatCrypt.Quantum.Optimization.FullOptimizer
open CatCrypt.Quantum.Optimization.UnitarySound
open CatCrypt.Quantum.Optimization.UnitarySoundFull

namespace CatCrypt.Quantum.Optimization.TemplatePass

variable {n : ℕ}

/-! ## Compiled templates -/

/-- A template in the form the pass matches against: the pattern gates in reverse
circuit order, the replacement gates in circuit order, and the fact that the
replacement is shorter than the pattern. -/
structure CTemplate (n : ℕ) where
  /-- The pattern gates, last gate first. -/
  revPat : List (Gate n)
  /-- The replacement gates in circuit order. -/
  rep : List (Gate n)
  /-- The replacement is shorter than the pattern. -/
  shrinks : rep.length < revPat.length

/-- A compiled template is sound when its pattern and its replacement have the same
`unitaryDenote`. -/
def CTemplate.Sound (c : CTemplate n) : Prop :=
  unitaryDenote (Circuit.ofList c.revPat.reverse) = unitaryDenote (Circuit.ofList c.rep)

/-- The compiled form of a template whose replacement is shorter than its pattern,
and `none` for any other template. -/
def compileTemplate (t : Template n) : Option (CTemplate n) :=
  if h : (circuitToList t.replacement).length < (circuitToList t.pattern).length then
    some ⟨(circuitToList t.pattern).reverse, circuitToList t.replacement, by simpa using h⟩
  else none

/-- The compiled forms of the shrinking templates of a list, in list order. -/
def compileList (ts : List (Template n)) : List (CTemplate n) :=
  ts.filterMap compileTemplate

/-- The compiled family of a template family, compiling `ts g` at each gate `g`. -/
def compileFamily (ts : Gate n → List (Template n)) (g : Gate n) : List (CTemplate n) :=
  compileList (ts g)

/-- A compiled template of `compileList ts` comes from a template of `ts`: its
reversed pattern and replacement are those of the template, and the replacement is
shorter than the pattern. -/
theorem mem_compileList {ts : List (Template n)} {c : CTemplate n}
    (hc : c ∈ compileList ts) :
    ∃ t ∈ ts, c.revPat = (circuitToList t.pattern).reverse ∧
      c.rep = circuitToList t.replacement ∧
      (circuitToList t.replacement).length < (circuitToList t.pattern).length := by
  obtain ⟨t, ht, hct⟩ := List.mem_filterMap.mp hc
  unfold compileTemplate at hct
  split at hct
  · next hlt =>
    cases hct
    exact ⟨t, ht, rfl, rfl, hlt⟩
  · cases hct

/-- A compiled family of templates whose patterns and replacements agree under a
gate-list semantics `S` has compiled templates that agree under `S`. -/
theorem compileFamily_preserves {β : Type*} (S : List (Gate n) → β)
    {P : Template n → Prop}
    (hP : ∀ t, P t → S (circuitToList t.pattern) = S (circuitToList t.replacement))
    {ts : Gate n → List (Template n)} (hts : ∀ g, ∀ t ∈ ts g, P t) :
    ∀ g, ∀ c ∈ compileFamily ts g, S c.revPat.reverse = S c.rep := by
  intro g c hc
  obtain ⟨t, ht, hp, hr, -⟩ := mem_compileList hc
  rw [hp, hr, List.reverse_reverse]
  exact hP t (hts g t ht)

/-- The compiled templates of a family of `CorrectU` templates are sound. -/
theorem sound_compileFamily {ts : Gate n → List (Template n)}
    (hts : ∀ g, ∀ t ∈ ts g, CorrectU t) :
    ∀ g, ∀ c ∈ compileFamily ts g, c.Sound :=
  compileFamily_preserves (fun l => unitaryDenote (Circuit.ofList l)) (P := CorrectU)
    (fun t ht => by rw [unitaryDenote_circuitToList, unitaryDenote_circuitToList]; exact ht) hts

/-! ## Matching and the pass -/

/-- The first compiled template of `cs` whose reversed pattern is a prefix of the
stack `stk`. The result is the stack below the matched pattern and the replacement
gate list. -/
def matchStackC : List (CTemplate n) → List (Gate n) → Option (List (Gate n) × List (Gate n))
  | [], _ => none
  | c :: cs, stk =>
    match matchPrefix c.revPat stk with
    | some rest => some (rest, c.rep)
    | none => matchStackC cs stk

/-- A match of `matchStackC` comes from a compiled template of the list: the stack
is its reversed pattern above the returned remainder and the returned gates are its
replacement. -/
theorem matchStackC_spec :
    ∀ {cs : List (CTemplate n)} {stk rest rep : List (Gate n)},
      matchStackC cs stk = some (rest, rep) →
      ∃ c ∈ cs, stk = c.revPat ++ rest ∧ rep = c.rep := by
  intro cs
  induction cs with
  | nil => intro stk rest rep h; simp [matchStackC] at h
  | cons c cs ih =>
    intro stk rest rep h
    simp only [matchStackC] at h
    split at h
    · next rest' hm =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c, List.mem_cons_self, matchPrefix_eq_append hm, rfl⟩
    · obtain ⟨c', hc', h'⟩ := ih h
      exact ⟨c', List.mem_cons_of_mem c hc', h'⟩

/-- The first template of `ts` whose replacement is shorter than its pattern and
whose reversed pattern is a prefix of the stack `stk`. The result is the stack
below the matched pattern and the replacement gate list. -/
def matchStack (ts : List (Template n)) (stk : List (Gate n)) :
    Option (List (Gate n) × List (Gate n)) :=
  matchStackC (compileList ts) stk

/-- A match of `matchStack` comes from a template of the list: the stack is the
reversed pattern above the returned remainder, the returned gates are the
replacement, and the replacement is shorter than the pattern. -/
theorem matchStack_spec :
    ∀ {ts : List (Template n)} {stk rest rep : List (Gate n)},
      matchStack ts stk = some (rest, rep) →
      ∃ t ∈ ts, stk = (circuitToList t.pattern).reverse ++ rest ∧
        rep = circuitToList t.replacement ∧
        rep.length < (circuitToList t.pattern).length := by
  intro ts stk rest rep h
  obtain ⟨c, hc, hstk, rfl⟩ := matchStackC_spec h
  obtain ⟨t, ht, hp, hr, hlt⟩ := mem_compileList hc
  exact ⟨t, ht, hp ▸ hstk, hr, hr ▸ hlt⟩

/-- The pass on a compiled family `cs` with an explicit stack `stk` of processed
gates (most recent first) and the remaining input `todo`. -/
def templatePassAuxC (cs : Gate n → List (CTemplate n)) :
    List (Gate n) → List (Gate n) → List (Gate n)
  | stk, [] => stk.reverse
  | stk, g :: todo =>
    match _h : matchStackC (cs g) (g :: stk) with
    | some (rest, rep) => templatePassAuxC cs rest (rep ++ todo)
    | none => templatePassAuxC cs (g :: stk) todo
termination_by stk todo => (stk.length + todo.length, todo.length)
decreasing_by
  · obtain ⟨c, -, hstk, rfl⟩ := matchStackC_spec _h
    have hl := congrArg List.length hstk
    have hlt := c.shrinks
    simp only [List.length_cons, List.length_append] at hl
    apply Prod.Lex.left
    simp only [List.length_append, List.length_cons]
    omega
  · simp only [List.length_cons, Prod.lex_def]
    omega

/-- The pass with an explicit stack `stk` of processed gates (most recent first)
and the remaining input `todo`. -/
def templatePassAux (ts : Gate n → List (Template n)) :
    List (Gate n) → List (Gate n) → List (Gate n) :=
  templatePassAuxC (compileFamily ts)

/-- The single left-to-right pass over a gate list with a compiled family. -/
def compiledPass (cs : Gate n → List (CTemplate n)) (gs : List (Gate n)) : List (Gate n) :=
  templatePassAuxC cs [] gs

/-- The pass with a compiled family on circuits, through their gate lists. -/
def compiledPassC (cs : Gate n → List (CTemplate n)) (c : Circuit n) : Circuit n :=
  Circuit.ofList (compiledPass cs (circuitToList c))

/-- **The single left-to-right template pass** over a gate list. -/
def templatePass (ts : Gate n → List (Template n)) (gs : List (Gate n)) : List (Gate n) :=
  compiledPass (compileFamily ts) gs

/-- The template pass on circuits, through their gate lists. -/
def templatePassC (ts : Gate n → List (Template n)) (c : Circuit n) : Circuit n :=
  compiledPassC (compileFamily ts) c

/-- The compiled pass preserves every gate-list semantics `S` that is a congruence
for `++` and under which each compiled template's pattern and replacement agree. -/
theorem templatePassAuxC_preserves {β : Type*} (S : List (Gate n) → β)
    (hS : ∀ a b b' c : List (Gate n), S b = S b' → S (a ++ (b ++ c)) = S (a ++ (b' ++ c)))
    (cs : Gate n → List (CTemplate n))
    (hcs : ∀ g, ∀ c ∈ cs g, S c.revPat.reverse = S c.rep) (stk todo : List (Gate n)) :
    S (templatePassAuxC cs stk todo) = S (stk.reverse ++ todo) := by
  fun_induction templatePassAuxC cs stk todo with
  | case1 stk => simp
  | case2 stk g todo rest rep h ih =>
    obtain ⟨c, hc, hstk, rfl⟩ := matchStackC_spec h
    have hsplit : stk.reverse ++ g :: todo =
        rest.reverse ++ (c.revPat.reverse ++ todo) := by
      have := congrArg List.reverse hstk
      simp only [List.reverse_cons, List.reverse_append] at this
      rw [← List.append_assoc, ← this, List.append_assoc, List.singleton_append]
    rw [ih, hsplit]
    exact hS _ _ _ _ (hcs g c hc).symm
  | case3 stk g todo h ih =>
    rw [ih]
    simp

/-- Each step of the compiled pass preserves the denotation of the stack (in
circuit order) followed by the remaining input. -/
theorem unitaryDenote_templatePassAuxC (cs : Gate n → List (CTemplate n))
    (hcs : ∀ g, ∀ c ∈ cs g, c.Sound) (stk todo : List (Gate n)) :
    unitaryDenote (Circuit.ofList (templatePassAuxC cs stk todo)) =
      unitaryDenote (Circuit.ofList (stk.reverse ++ todo)) :=
  templatePassAuxC_preserves (fun l => unitaryDenote (Circuit.ofList l))
    (fun _ _ _ _ h => by simp only [unitaryDenote_ofList_append, h]) cs hcs stk todo

/-- Each step of the pass preserves the denotation of the stack (in circuit
order) followed by the remaining input. -/
theorem unitaryDenote_templatePassAux (ts : Gate n → List (Template n))
    (hts : ∀ g, ∀ t ∈ ts g, CorrectU t) (stk todo : List (Gate n)) :
    unitaryDenote (Circuit.ofList (templatePassAux ts stk todo)) =
      unitaryDenote (Circuit.ofList (stk.reverse ++ todo)) :=
  unitaryDenote_templatePassAuxC _ (sound_compileFamily hts) stk todo

/-- The compiled pass preserves `unitaryDenote` when every compiled template of
the family is sound. -/
theorem unitaryDenote_compiledPass (cs : Gate n → List (CTemplate n))
    (hcs : ∀ g, ∀ c ∈ cs g, c.Sound) (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (compiledPass cs gs)) =
      unitaryDenote (Circuit.ofList gs) := by
  simp [compiledPass, unitaryDenote_templatePassAuxC cs hcs]

/-- The compiled pass on circuits preserves `unitaryDenote`. -/
theorem unitaryDenote_compiledPassC (cs : Gate n → List (CTemplate n))
    (hcs : ∀ g, ∀ c ∈ cs g, c.Sound) (c : Circuit n) :
    unitaryDenote (compiledPassC cs c) = unitaryDenote c := by
  rw [compiledPassC, unitaryDenote_compiledPass cs hcs, unitaryDenote_circuitToList]

/-- **The template pass preserves the unitary-channel semantics** when every
template the family can return is `CorrectU`. -/
theorem unitaryDenote_templatePass (ts : Gate n → List (Template n))
    (hts : ∀ g, ∀ t ∈ ts g, CorrectU t) (gs : List (Gate n)) :
    unitaryDenote (Circuit.ofList (templatePass ts gs)) =
      unitaryDenote (Circuit.ofList gs) :=
  unitaryDenote_compiledPass _ (sound_compileFamily hts) gs

/-- The pass on circuits preserves `unitaryDenote`. -/
theorem unitaryDenote_templatePassC (ts : Gate n → List (Template n))
    (hts : ∀ g, ∀ t ∈ ts g, CorrectU t) (c : Circuit n) :
    unitaryDenote (templatePassC ts c) = unitaryDenote c :=
  unitaryDenote_compiledPassC _ (sound_compileFamily hts) c

/-- The length of a compiled pass step's output is at most the stack and input
lengths together. -/
theorem length_templatePassAuxC_le (cs : Gate n → List (CTemplate n))
    (stk todo : List (Gate n)) :
    (templatePassAuxC cs stk todo).length ≤ stk.length + todo.length := by
  fun_induction templatePassAuxC cs stk todo with
  | case1 stk => simp
  | case2 stk g todo rest rep h ih =>
    obtain ⟨c, -, hstk, rfl⟩ := matchStackC_spec h
    have hl := congrArg List.length hstk
    have hlt := c.shrinks
    simp only [List.length_cons, List.length_append] at hl ih
    simp only [List.length_cons]
    omega
  | case3 stk g todo h ih =>
    simp only [List.length_cons] at ih ⊢
    omega

/-- The length of a pass step's output is at most the stack and input lengths together. -/
theorem length_templatePassAux_le (ts : Gate n → List (Template n))
    (stk todo : List (Gate n)) :
    (templatePassAux ts stk todo).length ≤ stk.length + todo.length :=
  length_templatePassAuxC_le _ stk todo

/-- The length of the compiled pass output is at most the input length. -/
theorem length_compiledPass_le (cs : Gate n → List (CTemplate n)) (gs : List (Gate n)) :
    (compiledPass cs gs).length ≤ gs.length := by
  simpa [compiledPass] using length_templatePassAuxC_le cs [] gs

/-- The compiled pass on circuits does not increase the gate count. -/
theorem gateCount_compiledPassC_le (cs : Gate n → List (CTemplate n)) (c : Circuit n) :
    (compiledPassC cs c).gateCount ≤ c.gateCount := by
  rw [compiledPassC, gateCount_ofList, ← circuitToList_length]
  exact length_compiledPass_le cs _

/-- **The length of the pass output is at most the input length.** -/
theorem length_templatePass_le (ts : Gate n → List (Template n)) (gs : List (Gate n)) :
    (templatePass ts gs).length ≤ gs.length :=
  length_compiledPass_le _ gs

/-- **The pass on circuits does not increase the gate count.** -/
theorem gateCount_templatePass_le (ts : Gate n → List (Template n)) (c : Circuit n) :
    (templatePassC ts c).gateCount ≤ c.gateCount :=
  gateCount_compiledPassC_le _ c

/-! ## The Level 1 family -/

/-- The template family of Level 1: the templates `single q` for a one-qubit
gate on qubit `q`, the templates `two c t` for `CNOT c t` with `c ≠ t`, and none
otherwise. -/
def level1Family (single : Fin n → List (Template n))
    (two : Fin n → Fin n → List (Template n)) : Gate n → List (Template n)
  | .H q | .X q | .Y q | .Z q | .T q | .Tdg q | .S q => single q
  | .Rz q _ | .RzQ q _ => single q
  | .CNOT c t => if c = t then [] else two c t
  | .CZ _ _ => []

/-- Every template of `level1Family` has a property `P` when those of `single` have
it and those of `two` have it on distinct qubits. -/
theorem level1Family_forall {single : Fin n → List (Template n)}
    {two : Fin n → Fin n → List (Template n)} {P : Template n → Prop}
    (hs : ∀ q, ∀ t ∈ single q, P t) (ht : ∀ c t, c ≠ t → ∀ u ∈ two c t, P u) :
    ∀ g, ∀ t ∈ level1Family single two g, P t := by
  intro g t hmem
  cases g <;> simp only [level1Family] at hmem <;> grind

/-- Every template of `level1Family` is `CorrectU` when those of `single` are and
those of `two` are on distinct qubits. -/
theorem level1Family_correctU {single : Fin n → List (Template n)}
    {two : Fin n → Fin n → List (Template n)}
    (hs : ∀ q, ∀ t ∈ single q, CorrectU t)
    (ht : ∀ c t, c ≠ t → ∀ u ∈ two c t, CorrectU u) :
    ∀ g, ∀ t ∈ level1Family single two g, CorrectU t :=
  level1Family_forall hs ht

/-- The compiled Level 1 family as data: the compiled single-qubit templates of
each qubit, in an array indexed by the qubit, and the compiled two-qubit templates
of each pair of qubits. -/
structure Level1Table (n : ℕ) where
  /-- The compiled single-qubit templates of qubit `q` at index `q`. -/
  single : Array (List (CTemplate n))
  /-- The compiled two-qubit templates of `CNOT c t`. -/
  two : Fin n → Fin n → List (CTemplate n)

/-- The Level 1 table of the template families `single` and `two`: the single-qubit
templates of all qubits compiled once into an array. -/
def level1Table (single : Fin n → List (Template n))
    (two : Fin n → Fin n → List (Template n)) : Level1Table n where
  single := Array.ofFn fun q => compileList (single q)
  two c t := compileList (two c t)

/-- The compiled templates a Level 1 table selects for a gate, by the qubit of a
one-qubit gate and by the qubits of a `CNOT` on distinct qubits. -/
def Level1Table.select (tb : Level1Table n) : Gate n → List (CTemplate n)
  | .H q | .X q | .Y q | .Z q | .T q | .Tdg q | .S q => tb.single.getD q.val []
  | .Rz q _ | .RzQ q _ => tb.single.getD q.val []
  | .CNOT c t => if c = t then [] else tb.two c t
  | .CZ _ _ => []

/-- The table entry of qubit `q` is the compiled list of `single q`. -/
theorem getD_level1Table_single (single : Fin n → List (Template n))
    (two : Fin n → Fin n → List (Template n)) (q : Fin n) :
    (level1Table single two).single.getD q.val [] = compileList (single q) := by
  simp [level1Table, Array.getD]

/-- The Level 1 table selects, at each gate, the compiled templates of
`level1Family`. -/
theorem select_level1Table (single : Fin n → List (Template n))
    (two : Fin n → Fin n → List (Template n)) :
    (level1Table single two).select = compileFamily (level1Family single two) := by
  funext g
  cases g <;>
    simp only [Level1Table.select, getD_level1Table_single, compileFamily, level1Family] <;>
    grind [level1Table, compileList]

/-- The Level 1 template pass on circuits, with the single-qubit templates of all
qubits compiled once before the pass. -/
def level1Pass (single : Fin n → List (Template n))
    (two : Fin n → Fin n → List (Template n)) (c : Circuit n) : Circuit n :=
  compiledPassC (level1Table single two).select c

/-- The Level 1 pass is the template pass of `level1Family`. -/
theorem level1Pass_eq (single : Fin n → List (Template n))
    (two : Fin n → Fin n → List (Template n)) :
    level1Pass single two = templatePassC (level1Family single two) := by
  funext c
  rw [level1Pass, select_level1Table, templatePassC]

/-! ## Checks -/

/-- A test family: `H;H` and `X;X` cancellation and CNOT cancellation. -/
def testFamily : Gate 3 → List (Template 3) :=
  level1Family (fun q => [cancelHH q, cancelXX q]) cnotTemplates

-- `H X X H` cancels in one pass: `X X` goes first, exposing `H H`.
set_option linter.hashCommand false in
#guard (templatePass testFamily [.H 0, .X 0, .X 0, .H 0]).isEmpty

-- Two CNOTs with a qubit-2 gate between them are not adjacent and all three gates stay.
set_option linter.hashCommand false in
#guard (templatePass testFamily [.CNOT 0 1, .H 2, .CNOT 0 1]).length == 3

-- Two adjacent CNOTs cancel, which exposes `H 2; H 2`, which cancels.
set_option linter.hashCommand false in
#guard (templatePass testFamily [.H 2, .CNOT 0 1, .CNOT 0 1, .H 2]).isEmpty

end CatCrypt.Quantum.Optimization.TemplatePass
