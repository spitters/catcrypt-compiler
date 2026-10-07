/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain
public import CatCryptCore.ForMathlib.CategoryTheory.ThinDoubleCategory

/-!
# Certified pass chains as squares of a thin double category

This module places the certificates of `PassChain` in the thin double category
`CategoryTheory.ThinDoubleCategory.ofRelSemantics` of lax squares over a relational
semantics.

## The double category

* Objects: a semantic program type `L : SemType` (a program type with a `Sem`) has two
  objects, `Pt.inp L` with carrier the inputs and `Pt.out L` with carrier the outputs.
* Horizontal category: the identities and, for every program `p` of `L`, one arrow
  `Pt.HHom.prog L p` from `Pt.inp L` to `Pt.out L`. No two generators are composable, so
  this is the free category on the programs.
* Semantics: a program denotes the graph of its partial denotation, relating an input `V`
  to an output `o` when `den p V = some o`.
* Vertical category: relations between the carriers (`relCategory`).
* Squares: lax squares `f ; ⟦w⟧ ⊆ ⟦u⟧ ; g`, in which the top arrow simulates the bottom
  one. A certificate is a forward simulation of the source by the target, so the target
  program is the top side, the source program is the bottom side, and the vertical sides
  are the converses `StepCert.vIn`, `StepCert.vOut` of the certificate's relations, read
  from the target to the source.

## Main definitions

* `SemType`, `Pt`, `Pt.carrier`, `Pt.HHom`, `Pt.sem`, `Pt.relSemantics`: the objects, the
  horizontal arrows and their relational semantics.
* `Sem.inp`, `Sem.out`, `Sem.prog`: the two objects and the horizontal arrows of a
  semantics.
* `StepCert.vIn`, `StepCert.vOut`, `Cert.vIn`, `Cert.vOut`: the vertical sides.
* `StepCert.ofSq`: the step certificate of a family of squares.
* The category on `SemType`: an arrow is a chain with its certificate, composed by
  `Chain.append` and `Cert.append`.
* `inFunctor`, `outFunctor`: the functors from the opposite of that category to the
  vertical category, sending a certified chain to its two vertical sides.

## Main results

* `sq_prog_iff`: the square with two programs as top and bottom, unfolded.
* `forall_sq_iff_sound`: the squares over all accepted programs are the soundness
  statement of a step certificate.
* `Cert.relIn_append`, `Cert.relOut_append`: the relations of an appended certificate are
  the relational composites.
* `Cert.sq`: the square of a certified chain on an accepted program, obtained by vertical
  pasting of the squares of its steps.
* `Cert.sq_append`: the square of an appended certificate is the vertical composite of the
  squares of its parts.
* `Cert.sound_of_sq`: the statement of `Cert.sound`, from the square.
* `sq_functor`: every accepted program has the square over the image of a certified chain
  under `inFunctor` and `outFunctor`.
* `Cert.sq_vcomp`: a square below the source program pastes with the square of a certified
  chain to one square below the target program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PassChain

open CategoryTheory ThinDoubleCategory

/-! ## 1. Objects, horizontal arrows and their semantics -/

/-- A semantic program type: a type of programs with a semantics. -/
structure SemType : Type 1 where
  /-- The programs. -/
  P : Type
  /-- Their semantics. -/
  S : Sem P

/-- The objects of the double category: the input side and the output side of each
semantic program type. -/
inductive Pt : Type 1 where
  /-- The input side, with carrier the inputs. -/
  | inp (L : SemType) : Pt
  /-- The output side, with carrier the outputs. -/
  | out (L : SemType) : Pt

namespace Pt

/-- The carrier of an object. -/
def carrier : Pt → Type
  | .inp L => L.S.In
  | .out L => L.S.Out

/-- Horizontal arrows: the identities, and one arrow from the input side to the output
side for every program. -/
inductive HHom : Pt → Pt → Type 1 where
  /-- The identity. -/
  | id (a : Pt) : HHom a a
  /-- The arrow of a program. -/
  | prog (L : SemType) (p : L.P) : HHom (.inp L) (.out L)

/-- Horizontal composition. A program arrow composes only with identities. -/
def HHom.comp : {a b c : Pt} → HHom a b → HHom b c → HHom a c
  | _, _, _, .id _, g => g
  | _, _, _, .prog L p, .id _ => .prog L p

/-- The horizontal category: the free category on the program arrows. -/
instance : Category (Hor Pt) where
  Hom := HHom
  id := HHom.id
  comp := HHom.comp
  id_comp := by intro a b f; rfl
  comp_id := by intro a b f; cases f <;> rfl
  assoc := by
    intro a b c d f g h
    cases f
    · rfl
    · cases g; rfl

/-- The relation a horizontal arrow denotes: equality for an identity, the graph of the
partial denotation for a program. -/
def sem : {a b : Pt} → HHom a b → carrier a → carrier b → Prop
  | _, _, .id _ => (· = ·)
  | _, _, .prog L p => fun V o => L.S.den p V = some o

/-- The relational semantics of the horizontal category. -/
def relSemantics : RelSemantics (C := Pt) carrier where
  sem := sem
  sem_id _ := rfl
  sem_comp := by
    intro a b c u v
    cases u with
    | id =>
      funext x z; apply propext
      exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩
    | prog L p =>
      cases v
      funext x z; apply propext
      exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨_, h1, h2⟩ => h2 ▸ h1⟩

/-- The vertical category: relations between the carriers. -/
instance : Category Pt := relCategory carrier

/-- The thin double category of lax squares of relations over the program semantics. -/
instance : ThinDoubleCategory Pt := ofRelSemantics relSemantics

end Pt

variable {P Q R : Type}

/-- The input object of a semantics. -/
abbrev Sem.inp (S : Sem P) : Pt := .inp ⟨P, S⟩

/-- The output object of a semantics. -/
abbrev Sem.out (S : Sem P) : Pt := .out ⟨P, S⟩

/-- The horizontal arrow of a program. -/
def Sem.prog (S : Sem P) (p : P) : Hor.of S.inp ⟶ Hor.of S.out := Pt.HHom.prog ⟨P, S⟩ p

/-! ## 2. Squares and step certificates -/

/-- The square with the program `q` on top and the program `p` at the bottom: every
successful run of `p` at an input related by the left side is matched by a successful run
of `q` with an output related by the right side. -/
theorem sq_prog_iff {S : Sem P} {T : Sem Q} (q : Q) (p : P) (f : T.inp ⟶ S.inp)
    (g : T.out ⟶ S.out) :
    Sq (T.prog q) f g (S.prog p) ↔
      ∀ (W : T.In) (V : S.In) (o : S.Out), f W V → S.den p V = some o →
        ∃ o' : T.Out, T.den q W = some o' ∧ g o' o :=
  Iff.rfl

/-- The squares over all programs a partial function accepts, with the converses of two
relations as vertical sides, are the soundness statement of a step certificate with these
relations. -/
theorem forall_sq_iff_sound {S : Sem P} {T : Sem Q} (f : P → Option Q)
    (rI : S.In → T.In → Prop) (rO : S.Out → T.Out → Prop) :
    (∀ p q, f p = some q →
        Sq (a := T.inp) (b := T.out) (c := S.inp) (d := S.out) (T.prog q)
          (fun W V => rI V W) (fun o' o => rO o o') (S.prog p)) ↔
      ∀ p q V W o, f p = some q → rI V W → S.den p V = some o →
        ∃ o', T.den q W = some o' ∧ rO o o' :=
  ⟨fun h p q V W o hf hVW hd => h p q hf W V o hVW hd,
    fun h p q hf W V o hVW hd => h p q V W o hf hVW hd⟩

namespace StepCert

variable {f : P → Option Q} {S : Sem P} {T : Sem Q}

/-- The left side of the squares of a step certificate: the converse of its input
relation, from the target inputs to the source inputs. -/
def vIn (C : StepCert f S T) : T.inp ⟶ S.inp := fun W V => C.relIn V W

/-- The right side of the squares of a step certificate: the converse of its output
relation, from the target outputs to the source outputs. -/
def vOut (C : StepCert f S T) : T.out ⟶ S.out := fun o' o => C.relOut o o'

/-- The square of a certified step on an accepted program: the output program on top, the
input program at the bottom. -/
theorem sq (C : StepCert f S T) {p : P} {q : Q} (hf : f p = some q) :
    Sq (T.prog q) C.vIn C.vOut (S.prog p) :=
  (forall_sq_iff_sound f C.relIn C.relOut).2 (fun _ _ _ _ _ => C.sound) p q hf

/-- The step certificate of a family of squares over the accepted programs. -/
def ofSq (rI : S.In → T.In → Prop) (rO : S.Out → T.Out → Prop)
    (h : ∀ p q, f p = some q →
      Sq (a := T.inp) (b := T.out) (c := S.inp) (d := S.out) (T.prog q)
        (fun W V => rI V W) (fun o' o => rO o o') (S.prog p)) :
    StepCert f S T where
  relIn := rI
  relOut := rO
  sound := fun {p q V W o} => (forall_sq_iff_sound f rI rO).1 h p q V W o

end StepCert

/-! ## 3. Chains: vertical pasting -/

namespace Cert

/-- The left side of the squares of a certificate: the converse of its composed input
relation. -/
def vIn {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) : T.inp ⟶ S.inp :=
  fun W V => C.relIn V W

/-- The right side of the squares of a certificate: the converse of its composed output
relation. -/
def vOut {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) : T.out ⟶ S.out :=
  fun o' o => C.relOut o o'

/-- The input relation of an appended certificate is the relational composite. -/
theorem relIn_append {c : Chain P Q} {d : Chain Q R} {S : Sem P} {T : Sem Q} {U : Sem R}
    (C : Cert c S T) (D : Cert d T U) :
    (C.append D).relIn = Relation.Comp C.relIn D.relIn := by
  induction C with
  | nil S =>
    funext V W; apply propext
    exact ⟨fun h => ⟨V, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩
  | cons h C ih =>
    funext V W; apply propext
    simp only [append, relIn, ih, Relation.Comp]
    exact ⟨fun ⟨X, h1, m, h2, h3⟩ => ⟨m, ⟨X, h1, h2⟩, h3⟩,
      fun ⟨m, ⟨X, h1, h2⟩, h3⟩ => ⟨X, h1, m, h2, h3⟩⟩

/-- The output relation of an appended certificate is the relational composite. -/
theorem relOut_append {c : Chain P Q} {d : Chain Q R} {S : Sem P} {T : Sem Q} {U : Sem R}
    (C : Cert c S T) (D : Cert d T U) :
    (C.append D).relOut = Relation.Comp C.relOut D.relOut := by
  induction C with
  | nil S =>
    funext V W; apply propext
    exact ⟨fun h => ⟨V, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩
  | cons h C ih =>
    funext V W; apply propext
    simp only [append, relOut, ih, Relation.Comp]
    exact ⟨fun ⟨X, h1, m, h2, h3⟩ => ⟨m, ⟨X, h1, h2⟩, h3⟩,
      fun ⟨m, ⟨X, h1, h2⟩, h3⟩ => ⟨X, h1, m, h2, h3⟩⟩

/-- The left side of the empty certificate is the vertical identity. -/
theorem vIn_nil (S : Sem P) : (Cert.nil S).vIn = 𝟙 S.inp := by
  funext W V; apply propext
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- The right side of the empty certificate is the vertical identity. -/
theorem vOut_nil (S : Sem P) : (Cert.nil S).vOut = 𝟙 S.out := by
  funext W V; apply propext
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- The left side of `Cert.cons` is the vertical composite, the rest first. -/
theorem vIn_cons {s : Step P Q} {rest : Chain Q R} {S : Sem P} {T : Sem Q} {U : Sem R}
    (h : StepCert s.run S T) (C : Cert rest T U) :
    (Cert.cons h C).vIn = C.vIn ≫ h.vIn := by
  funext W V; apply propext
  exact ⟨fun ⟨X, h1, h2⟩ => ⟨X, h2, h1⟩, fun ⟨X, h2, h1⟩ => ⟨X, h1, h2⟩⟩

/-- The right side of `Cert.cons` is the vertical composite, the rest first. -/
theorem vOut_cons {s : Step P Q} {rest : Chain Q R} {S : Sem P} {T : Sem Q} {U : Sem R}
    (h : StepCert s.run S T) (C : Cert rest T U) :
    (Cert.cons h C).vOut = C.vOut ≫ h.vOut := by
  funext W V; apply propext
  exact ⟨fun ⟨X, h1, h2⟩ => ⟨X, h2, h1⟩, fun ⟨X, h2, h1⟩ => ⟨X, h1, h2⟩⟩

/-- The left side of an appended certificate is the vertical composite, the second part
first. -/
theorem vIn_append {c : Chain P Q} {d : Chain Q R} {S : Sem P} {T : Sem Q} {U : Sem R}
    (C : Cert c S T) (D : Cert d T U) : (C.append D).vIn = D.vIn ≫ C.vIn := by
  funext W V; apply propext
  simp only [vIn, relIn_append]
  exact ⟨fun ⟨X, h1, h2⟩ => ⟨X, h2, h1⟩, fun ⟨X, h2, h1⟩ => ⟨X, h1, h2⟩⟩

/-- The right side of an appended certificate is the vertical composite, the second part
first. -/
theorem vOut_append {c : Chain P Q} {d : Chain Q R} {S : Sem P} {T : Sem Q} {U : Sem R}
    (C : Cert c S T) (D : Cert d T U) : (C.append D).vOut = D.vOut ≫ C.vOut := by
  funext W V; apply propext
  simp only [vOut, relOut_append]
  exact ⟨fun ⟨X, h1, h2⟩ => ⟨X, h2, h1⟩, fun ⟨X, h2, h1⟩ => ⟨X, h1, h2⟩⟩

/-- The square of a certified chain on an accepted program: the output program on top,
the input program at the bottom. It is the vertical identity square for the empty chain
and the vertical composite of the square of the rest with the square of the first step
otherwise. -/
theorem sq {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) {p : P} {q : Q}
    (hrun : c.run p = some q) : Sq (T.prog q) C.vIn C.vOut (S.prog p) := by
  induction C with
  | nil S =>
    cases hrun
    exact (vid (S.prog p)).congr rfl (vIn_nil S).symm (vOut_nil S).symm rfl
  | cons h C ih =>
    simp only [Chain.run, Option.bind_eq_some_iff] at hrun
    obtain ⟨p', hs, hrest⟩ := hrun
    exact (vcomp (ih hrest) (h.sq hs)).congr rfl (vIn_cons h C).symm (vOut_cons h C).symm rfl

/-- The square of an appended certificate is the vertical composite of the square of the
second part with the square of the first. -/
theorem sq_append {c : Chain P Q} {d : Chain Q R} {S : Sem P} {T : Sem Q} {U : Sem R}
    (C : Cert c S T) (D : Cert d T U) {p : P} {q : Q} {r : R} (hc : c.run p = some q)
    (hd : d.run q = some r) :
    Sq (U.prog r) (C.append D).vIn (C.append D).vOut (S.prog p) :=
  (vcomp (D.sq hd) (C.sq hc)).congr rfl (vIn_append C D).symm (vOut_append C D).symm rfl

/-- The statement of `Cert.sound`, read off the square of the chain. -/
theorem sound_of_sq {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) {p : P}
    {q : Q} {V : S.In} {W : T.In} {o : S.Out} (hrun : c.run p = some q)
    (hVW : C.relIn V W) (hden : S.den p V = some o) :
    ∃ o', T.den q W = some o' ∧ C.relOut o o' :=
  (sq_prog_iff q p C.vIn C.vOut).1 (C.sq hrun) W V o hVW hden

/-- A square below the source program pastes with the square of a certified chain to a
square below the target program. With `w` the arrow of a specification and `f`, `g` a
correspondence between the source level and the specification, the composite relates the
target level to the specification. -/
theorem sq_vcomp {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) {p : P} {q : Q}
    (hrun : c.run p = some q) {a b : Pt} {f : S.inp ⟶ a} {g : S.out ⟶ b}
    {w : Hor.of a ⟶ Hor.of b} (hspec : Sq (S.prog p) f g w) :
    Sq (T.prog q) (C.vIn ≫ f) (C.vOut ≫ g) w :=
  vcomp (C.sq hrun) hspec

/-- `Cert.sq_vcomp` with a program of a third semantics as the specification, unfolded: if
every successful run of the specification `u` is matched by the source program `p` up to
`f` and `g`, then it is matched by the compiled program `q` up to the composites with the
relations of the certificate. -/
theorem sound_spec {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) {p : P} {q : Q}
    (hrun : c.run p = some q) {A : Type} {U : Sem A} {u : A} {f : S.In → U.In → Prop}
    {g : S.Out → U.Out → Prop}
    (hspec : ∀ V x o, f V x → U.den u x = some o → ∃ m, S.den p V = some m ∧ g m o)
    {W : T.In} {V : S.In} {x : U.In} {o : U.Out} (hVW : C.relIn V W) (hVx : f V x)
    (hu : U.den u x = some o) :
    ∃ o' m, T.den q W = some o' ∧ C.relOut m o' ∧ g m o := by
  obtain ⟨o', ho', m, hm, hg⟩ :=
    (sq_prog_iff q u (C.vIn ≫ f) (C.vOut ≫ g)).1
      (C.sq_vcomp hrun ((sq_prog_iff p u f g).2 hspec)) W x o ⟨V, hVW, hVx⟩ hu
  exact ⟨o', m, ho', hm, hg⟩

/-- Appending the empty certificate, as an equality of chains with certificates. -/
theorem append_nil_sigma {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) :
    (⟨c.append (.nil Q), C.append (.nil T)⟩ : Σ c : Chain P Q, Cert c S T) = ⟨c, C⟩ := by
  induction C with
  | nil S => rfl
  | @cons _ _ _ s _ S T U h C ih =>
    exact congrArg
      (fun x : Σ c, Cert c T U => (⟨.cons s x.1, .cons h x.2⟩ : Σ c, Cert c S U)) ih

/-- Associativity of appending, as an equality of chains with certificates. -/
theorem append_assoc_sigma {A : Type} {c : Chain P Q} {d : Chain Q R} {e : Chain R A}
    {S : Sem P} {T : Sem Q} {U : Sem R} {Z : Sem A} (C : Cert c S T) (D : Cert d T U)
    (E : Cert e U Z) :
    (⟨(c.append d).append e, (C.append D).append E⟩ : Σ c : Chain P A, Cert c S Z) =
      ⟨c.append (d.append e), C.append (D.append E)⟩ := by
  induction C with
  | nil S => rfl
  | @cons _ _ _ s _ S T U' h C ih =>
    exact congrArg
      (fun x : Σ c, Cert c T Z => (⟨.cons s x.1, .cons h x.2⟩ : Σ c, Cert c S Z)) (ih D)

end Cert

/-! ## 4. The category of certified chains and its functors to the vertical category -/

/-- The category of semantic program types and certified chains: an arrow is a chain
together with its certificate, the identity is the empty chain, and composition is
`Chain.append` with `Cert.append`. -/
instance : Category SemType where
  Hom L L' := Σ c : Chain L.P L'.P, Cert c L.S L'.S
  id L := ⟨.nil L.P, .nil L.S⟩
  comp F G := ⟨F.1.append G.1, F.2.append G.2⟩
  id_comp _ := rfl
  comp_id F := Cert.append_nil_sigma F.2
  assoc F G H := Cert.append_assoc_sigma F.2 G.2 H.2

/-- The functor from the opposite of the category of certified chains to the vertical
category that sends a semantic program type to its input object and a certified chain to
the converse of its input relation. -/
def inFunctor : SemTypeᵒᵖ ⥤ Pt where
  obj L := .inp L.unop
  map F := F.unop.2.vIn
  map_id L := Cert.vIn_nil L.unop.S
  map_comp F G := Cert.vIn_append G.unop.2 F.unop.2

/-- The functor from the opposite of the category of certified chains to the vertical
category that sends a semantic program type to its output object and a certified chain to
the converse of its output relation. -/
def outFunctor : SemTypeᵒᵖ ⥤ Pt where
  obj L := .out L.unop
  map F := F.unop.2.vOut
  map_id L := Cert.vOut_nil L.unop.S
  map_comp F G := Cert.vOut_append G.unop.2 F.unop.2

/-- Every program accepted by a certified chain has the square over the image of the
chain under `inFunctor` and `outFunctor`: the compiled program on top, the source program
at the bottom. -/
theorem sq_functor {L L' : SemType} (F : L ⟶ L') {p : L.P} {q : L'.P}
    (hrun : F.1.run p = some q) :
    Sq (L'.S.prog q) (inFunctor.map F.op) (outFunctor.map F.op) (L.S.prog p) :=
  F.2.sq hrun

end CatCrypt.Crypto.SecureCompilation.VIR.PassChain
