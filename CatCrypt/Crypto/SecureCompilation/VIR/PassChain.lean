/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# Chains of partial compiler passes and their certificates

A compiler front is a sequence of partial steps between program types: a step may
refuse its input. This module separates the sequence, which is data, from its
correctness certificate, which carries the semantics.

* The data is a `Chain P Q`: a list of named partial functions `Step`, each from
  the program type the previous one produces. `Chain.run` is their Kleisli
  composition in `Option`. The data carries no semantic parameter, so a compiler
  defined as a chain depends on no fuel, builtin table or leak parameter.
* A semantics `Sem P` of a program type gives an input type, an output type and a
  partial denotation. A `StepCert f S T` is a forward simulation of the step `f`
  on successful runs, up to a relation on inputs and one on outputs. A
  `Cert c S T` holds one step certificate per step of `c`; its input and output
  relations are the relational compositions of the steps' relations.
* A leak semantics `LeakSem P` gives the event list of a successful run. Its
  two-run semantics `LeakSem.twoRun` has pairs of inputs and returns the pair of
  event lists of two successful runs. A certificate between two-run semantics
  whose output relation implies `ctRel` (equal source events give equal target
  events) yields the constant-time statement `Cert.ct`. A `CTCert` builds such a
  certificate step by step, and `CTCert.ct` is the resulting statement.

## Main definitions

* `Step`, `Chain`, `Chain.run`, `Chain.append`: the chain as data.
* `Chain.runTrace`: the run that reports the index and name of the first step
  that refuses.
* `Sem`, `StepCert`, `Cert`, `Cert.relIn`, `Cert.relOut`, `Cert.append`: the
  certificate.
* `StepCert.ofRefines`, `StepCert.ofDenoteEq`, `StepCert.id`: certificates of an
  endo-pass that keeps successful runs, of one that preserves the denotation, and
  of the identity step.
* `StepCert.ofTransport`: the certificate of a step between program types whose
  output denotes the transport of the source denotation at the transported input.
* `LeakSem`, `LeakSem.twoRun`, `ctRel`, `CTCert`, `CTCert.toCert`: the two-run
  semantics and the constant-time certificate.

## Main results

* `Chain.run_append`: running an appended chain runs the two parts in sequence.
* `Chain.runTrace_eq_run`: the reporting run agrees with `Chain.run`.
* `Cert.sound`: a certified chain preserves successful runs up to the composed
  input and output relations.
* `Cert.ct`: at two-run semantics, with an output relation implying `ctRel`,
  equal source events at related input pairs give equal target events.
* `CTCert.ct`: the same statement for a chain certified step by step at
  `ctRel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PassChain

/-! ## 1. Chains as data -/

/-- A named partial step from programs of type `P` to programs of type `Q`. -/
structure Step (P Q : Type) where
  /-- The name reported when the step refuses. -/
  name : String
  /-- The step; `none` is a refusal. -/
  run : P → Option Q

/-- The identity step. -/
def Step.id (P : Type) : Step P P := ⟨"id", some⟩

/-- A chain of steps, each from the program type the previous one produces. -/
inductive Chain : Type → Type → Type 1 where
  /-- The empty chain. -/
  | nil (P : Type) : Chain P P
  /-- A step followed by a chain. -/
  | cons {P Q R : Type} (s : Step P Q) (rest : Chain Q R) : Chain P R

namespace Chain

/-- Run the steps in order; the run refuses when one step refuses. -/
def run : {P Q : Type} → Chain P Q → P → Option Q
  | _, _, .nil _ => some
  | _, _, .cons s rest => fun p => (s.run p).bind rest.run

/-- The chain that runs `c` and then `d`. -/
def append : {P Q R : Type} → Chain P Q → Chain Q R → Chain P R
  | _, _, _, .nil _, d => d
  | _, _, _, .cons s rest, d => .cons s (rest.append d)

/-- Running an appended chain runs the two parts in sequence. -/
theorem run_append {P Q R : Type} (c : Chain P Q) (d : Chain Q R) (p : P) :
    (c.append d).run p = (c.run p).bind d.run := by
  induction c with
  | nil => rfl
  | cons s rest ih =>
    simp only [append, run]
    cases s.run p with
    | none => rfl
    | some q => exact ih d q

/-- The run from step index `i` that reports the index and name of the first step
    that refuses. -/
def runTraceFrom : {P Q : Type} → Chain P Q → Nat → P → Except (Nat × String) Q
  | _, _, .nil _, _, p => .ok p
  | _, _, .cons s rest, i, p =>
    match s.run p with
    | none => .error (i, s.name)
    | some q => rest.runTraceFrom (i + 1) q

/-- The run that reports the index (from `0`) and name of the first step that
    refuses. -/
def runTrace {P Q : Type} (c : Chain P Q) (p : P) : Except (Nat × String) Q :=
  c.runTraceFrom 0 p

theorem runTraceFrom_toOption {P Q : Type} (c : Chain P Q) (i : Nat) (p : P) :
    (c.runTraceFrom i p).toOption = c.run p := by
  induction c generalizing i with
  | nil => rfl
  | cons s rest ih =>
    simp only [runTraceFrom, run]
    cases s.run p with
    | none => rfl
    | some q => exact ih (i + 1) q

/-- The reporting run agrees with `Chain.run`. -/
theorem runTrace_eq_run {P Q : Type} (c : Chain P Q) (p : P) :
    (c.runTrace p).toOption = c.run p :=
  c.runTraceFrom_toOption 0 p

end Chain

/-! ## 2. Semantics and certificates -/

/-- A semantics of programs of type `P`: a partial denotation from inputs to
    outputs. -/
structure Sem (P : Type) where
  /-- The inputs. -/
  In : Type
  /-- The outputs. -/
  Out : Type
  /-- The denotation; `none` is a failed run. -/
  den : P → In → Option Out

/-- A forward simulation of the partial function `f` on successful runs, up to a
    relation on inputs and a relation on outputs. -/
structure StepCert {P Q : Type} (f : P → Option Q) (S : Sem P) (T : Sem Q) where
  /-- The input relation. -/
  relIn : S.In → T.In → Prop
  /-- The output relation. -/
  relOut : S.Out → T.Out → Prop
  /-- A successful source run at related inputs gives a successful target run
      with a related output. -/
  sound : ∀ {p q V W o}, f p = some q → relIn V W → S.den p V = some o →
    ∃ o', T.den q W = some o' ∧ relOut o o'

namespace StepCert

/-- The certificate of an endo-pass whose output keeps every successful run of
    its input, with equal inputs and outputs. -/
def ofRefines {P : Type} {f : P → Option P} (S : Sem P)
    (h : ∀ p q V o, f p = some q → S.den p V = some o → S.den q V = some o) :
    StepCert f S S where
  relIn := Eq
  relOut := Eq
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    exact ⟨o, h p q V o hf hd, rfl⟩

/-- The certificate of an endo-pass whose output has the denotation of its
    input. -/
def ofDenoteEq {P : Type} {f : P → Option P} (S : Sem P)
    (h : ∀ p q, f p = some q → S.den q = S.den p) : StepCert f S S :=
  ofRefines S fun p q V o hf hd => by rw [h p q hf]; exact hd

/-- The certificate of the identity step. -/
def id {P : Type} (S : Sem P) : StepCert (Step.id P).run S S :=
  ofDenoteEq S fun p q hf => by cases hf; rfl

/-- The certificate of a step whose output denotes, at the transported input, the
    transport of the denotation of its input. The input relation is the graph of
    `mapIn` and the output relation the graph of `mapOut`. -/
def ofTransport {P Q : Type} {f : P → Option Q} (S : Sem P) (T : Sem Q)
    (mapIn : S.In → T.In) (mapOut : S.Out → T.Out)
    (h : ∀ p q V, f p = some q → T.den q (mapIn V) = (S.den p V).map mapOut) :
    StepCert f S T where
  relIn V W := W = mapIn V
  relOut o o' := o' = mapOut o
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    exact ⟨mapOut o, by rw [h p q V hf, hd]; rfl, rfl⟩

end StepCert

/-- A certificate of a chain: one step certificate per step, each between the
    semantics the previous one ends at. -/
inductive Cert : {P Q : Type} → Chain P Q → Sem P → Sem Q → Type 1 where
  /-- The certificate of the empty chain. -/
  | nil {P : Type} (S : Sem P) : Cert (.nil P) S S
  /-- A step certificate followed by a certificate of the rest. -/
  | cons {P Q R : Type} {s : Step P Q} {rest : Chain Q R} {S : Sem P} {T : Sem Q}
      {U : Sem R} (h : StepCert s.run S T) (C : Cert rest T U) : Cert (.cons s rest) S U

namespace Cert

/-- The composed input relation: equality for the empty chain, the relational
    composition of the steps' input relations otherwise. -/
def relIn : {P Q : Type} → {c : Chain P Q} → {S : Sem P} → {T : Sem Q} →
    Cert c S T → S.In → T.In → Prop
  | _, _, _, _, _, .nil _ => Eq
  | _, _, _, _, _, .cons h C => fun V W => ∃ X, h.relIn V X ∧ C.relIn X W

/-- The composed output relation: equality for the empty chain, the relational
    composition of the steps' output relations otherwise. -/
def relOut : {P Q : Type} → {c : Chain P Q} → {S : Sem P} → {T : Sem Q} →
    Cert c S T → S.Out → T.Out → Prop
  | _, _, _, _, _, .nil _ => Eq
  | _, _, _, _, _, .cons h C => fun o o' => ∃ x, h.relOut o x ∧ C.relOut x o'

/-- A certified chain preserves successful runs: a successful source run at
    inputs related by the composed input relation gives a successful target run
    whose output is related by the composed output relation. -/
theorem sound {P Q : Type} {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T)
    {p : P} {q : Q} {V : S.In} {W : T.In} {o : S.Out} (hrun : c.run p = some q)
    (hVW : C.relIn V W) (hden : S.den p V = some o) :
    ∃ o', T.den q W = some o' ∧ C.relOut o o' := by
  induction C with
  | nil S =>
    cases hrun
    cases hVW
    exact ⟨o, hden, rfl⟩
  | cons h C ih =>
    simp only [Chain.run, Option.bind_eq_some_iff] at hrun
    obtain ⟨p', hs, hrest⟩ := hrun
    obtain ⟨X, hVX, hXW⟩ := hVW
    obtain ⟨x, hx, hox⟩ := h.sound hs hVX hden
    obtain ⟨o', ho', hxo'⟩ := ih hrest hXW hx
    exact ⟨o', ho', x, hox, hxo'⟩

/-- The certificate of an appended chain. -/
def append : {P Q R : Type} → {c : Chain P Q} → {d : Chain Q R} → {S : Sem P} →
    {T : Sem Q} → {U : Sem R} → Cert c S T → Cert d T U → Cert (c.append d) S U
  | _, _, _, _, _, _, _, _, .nil _, D => D
  | _, _, _, _, _, _, _, _, .cons h C, D => .cons h (C.append D)

end Cert

/-! ## 3. Constant time -/

/-- A leak semantics of programs of type `P`: the event list of a successful
    run. -/
structure LeakSem (P : Type) where
  /-- The inputs. -/
  In : Type
  /-- The events. -/
  Ev : Type
  /-- The event list of a run; `none` is a failed run. -/
  leak : P → In → Option (List Ev)

/-- The two-run semantics of a leak semantics: an input is a pair of inputs, and
    the denotation is the pair of event lists of two successful runs. -/
def LeakSem.twoRun {P : Type} (L : LeakSem P) : Sem P where
  In := L.In × L.In
  Out := List L.Ev × List L.Ev
  den p V := (L.leak p V.1).bind fun l₁ => (L.leak p V.2).map fun l₂ => (l₁, l₂)

theorem LeakSem.twoRun_den {P : Type} (L : LeakSem P) (p : P) (V₁ V₂ : L.In)
    (l₁ l₂ : List L.Ev) (h₁ : L.leak p V₁ = some l₁) (h₂ : L.leak p V₂ = some l₂) :
    L.twoRun.den p (V₁, V₂) = some (l₁, l₂) := by
  simp [twoRun, h₁, h₂]

theorem LeakSem.twoRun_den_eq_some {P : Type} (L : LeakSem P) {p : P} {V₁ V₂ : L.In}
    {o : List L.Ev × List L.Ev} (h : L.twoRun.den p (V₁, V₂) = some o) :
    L.leak p V₁ = some o.1 ∧ L.leak p V₂ = some o.2 := by
  simp only [twoRun, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := h
  exact ⟨h₁, h₂⟩

/-- The constant-time output relation: equal source events give equal target
    events. -/
def ctRel {E E' : Type} (a : List E × List E) (b : List E' × List E') : Prop :=
  a.1 = a.2 → b.1 = b.2

/-- Constant time through a certified chain at two-run semantics: when the
    composed output relation implies `ctRel`, equal source events of two
    successful runs at an input pair related to a target input pair give equal
    events of two successful target runs. -/
theorem Cert.ct {P Q : Type} {c : Chain P Q} {L : LeakSem P} {L' : LeakSem Q}
    (C : Cert c L.twoRun L'.twoRun) (hC : ∀ a b, C.relOut a b → ctRel a b)
    {p : P} {q : Q} {V₁ V₂ : L.In} {W₁ W₂ : L'.In} {l₁ l₂ : List L.Ev}
    (hrun : c.run p = some q) (hVW : C.relIn (V₁, V₂) (W₁, W₂))
    (h₁ : L.leak p V₁ = some l₁) (h₂ : L.leak p V₂ = some l₂) (hl : l₁ = l₂) :
    ∃ m₁ m₂, L'.leak q W₁ = some m₁ ∧ L'.leak q W₂ = some m₂ ∧ m₁ = m₂ := by
  obtain ⟨o', ho', hrel⟩ := C.sound hrun hVW (L.twoRun_den p V₁ V₂ l₁ l₂ h₁ h₂)
  obtain ⟨hm₁, hm₂⟩ := L'.twoRun_den_eq_some ho'
  exact ⟨o'.1, o'.2, hm₁, hm₂, hC _ _ hrel hl⟩

/-- A constant-time certificate: a certificate between two-run semantics whose
    step output relations each imply `ctRel`. -/
inductive CTCert : {P Q : Type} → Chain P Q → LeakSem P → LeakSem Q → Type 1 where
  /-- The certificate of the empty chain. -/
  | nil {P : Type} (L : LeakSem P) : CTCert (.nil P) L L
  /-- A step certificate whose output relation implies `ctRel`, followed by a
      certificate of the rest. -/
  | cons {P Q R : Type} {s : Step P Q} {rest : Chain Q R} {L : LeakSem P}
      {L' : LeakSem Q} {L'' : LeakSem R} (h : StepCert s.run L.twoRun L'.twoRun)
      (hct : ∀ a b, h.relOut a b → ctRel a b) (C : CTCert rest L' L'') :
      CTCert (.cons s rest) L L''

namespace CTCert

/-- The underlying certificate between two-run semantics. -/
def toCert : {P Q : Type} → {c : Chain P Q} → {L : LeakSem P} → {L' : LeakSem Q} →
    CTCert c L L' → Cert c L.twoRun L'.twoRun
  | _, _, _, _, _, .nil L => .nil L.twoRun
  | _, _, _, _, _, .cons h _ C => .cons h C.toCert

/-- The composed output relation of a constant-time certificate implies
    `ctRel`. -/
theorem toCert_relOut {P Q : Type} {c : Chain P Q} {L : LeakSem P} {L' : LeakSem Q}
    (C : CTCert c L L') : ∀ a b, C.toCert.relOut a b → ctRel a b := by
  induction C with
  | nil L =>
    intro a b hab
    cases hab
    exact _root_.id
  | cons h hct C ih =>
    intro a b ⟨x, hax, hxb⟩ hl
    exact ih x b hxb (hct a x hax hl)

/-- Constant time through a chain certified step by step: equal source events of
    two successful runs at an input pair related to a target input pair give
    equal events of two successful target runs. -/
theorem ct {P Q : Type} {c : Chain P Q} {L : LeakSem P} {L' : LeakSem Q}
    (C : CTCert c L L') {p : P} {q : Q} {V₁ V₂ : L.In} {W₁ W₂ : L'.In}
    {l₁ l₂ : List L.Ev} (hrun : c.run p = some q) (hVW : C.toCert.relIn (V₁, V₂) (W₁, W₂))
    (h₁ : L.leak p V₁ = some l₁) (h₂ : L.leak p V₂ = some l₂) (hl : l₁ = l₂) :
    ∃ m₁ m₂, L'.leak q W₁ = some m₁ ∧ L'.leak q W₂ = some m₂ ∧ m₁ = m₂ :=
  C.toCert.ct C.toCert_relOut hrun hVW h₁ h₂ hl

end CTCert

/-! ## 4. A two-step chain over natural-number programs -/

namespace Witness

/-- The step that refuses the program `0`. -/
def nonzero : Step Nat Nat := ⟨"nonzero", fun p => if p = 0 then none else some p⟩

/-- The step from natural-number programs to integer programs. -/
def toInt : Step Nat Int := ⟨"toInt", fun p => some (p : Int)⟩

/-- The two-step chain. -/
def chain : Chain Nat Int := .cons nonzero (.cons toInt (.nil Int))

/-- A natural-number program `p` adds `p` to its input. -/
abbrev natSem : Sem Nat := ⟨Nat, Nat, fun p V => some (p + V)⟩

/-- An integer program `p` adds `p` to its input. -/
abbrev intSem : Sem Int := ⟨Int, Int, fun p W => some (p + W)⟩

/-- The certificate of the translation to integers. -/
def toIntCert : StepCert toInt.run natSem intSem where
  relIn V W := W = (V : Int)
  relOut o o' := o' = (o : Int)
  sound := by
    intro p q V W o hf hVW hd
    simp only [toInt, Option.some.injEq] at hf
    simp only [Option.some.injEq] at hd
    subst hf hVW hd
    exact ⟨_, rfl, by simp⟩

theorem nonzero_refines (p q : Nat) (V : natSem.In) (o : natSem.Out)
    (hf : nonzero.run p = some q) (hd : natSem.den p V = some o) : natSem.den q V = some o := by
  simp only [nonzero] at hf
  split at hf
  · cases hf
  · cases hf; exact hd

/-- The certificate of the two-step chain. -/
def cert : Cert chain natSem intSem :=
  .cons (StepCert.ofRefines natSem nonzero_refines) (.cons toIntCert (.nil intSem))

/-- Preservation for the two-step chain. -/
theorem chain_sound {p : Nat} {q : Int} (hrun : chain.run p = some q) (V : Nat) :
    intSem.den q (V : Int) = some ((p + V : Nat) : Int) := by
  obtain ⟨o', ho', x, rfl, y, hy, rfl⟩ :=
    cert.sound (V := V) (W := (V : Int)) (o := p + V) hrun ⟨V, rfl, (V : Int), rfl, rfl⟩ rfl
  subst hy
  exact ho'

end Witness

end CatCrypt.Crypto.SecureCompilation.VIR.PassChain
