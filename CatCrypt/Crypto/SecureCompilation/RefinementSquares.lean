/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.WRPRelSemantics
public import CatCrypt.Crypto.SecureCompilation.VIR.PassChainDouble
public import CatCrypt.Hax.Ascent.SquareDouble
public import CatCrypt.Crypto.SecureCompilation.Ascent.SquareStrictDouble
public import CatCrypt.Crypto.SecureCompilation.Ascent.RustMSquareDouble

/-!
# The compiler's squares as refinement squares

The compiler's thin double categories of lax squares, each built with
`CategoryTheory.ThinDoubleCategory.ofRelSemantics` from a relational semantics, map into the
refinement squares of predicate transformers by the thin double functor
`WRPRelSemantics.relDouble`, which is full on squares (`WRPRelSemantics.relDouble_sq_iff`).
A program denotes the demonic weakest precondition of its relation, and a lax square with top
`u` and bottom `w` is the refinement square in which the bottom `w` refines the top `u`: every
postcondition that `u` establishes from an input related to `y` by the left side, `w`
establishes from `y` up to the right side (`relDouble_sq_iff_box`).

The four double categories and the orientation of their squares:

* Pass chains (`VIR/PassChainDouble`): the compiled program is the top, the source program
  the bottom, the vertical sides are the converses of the certificate's relations. The
  source program refines the compiled program.
* Source-level ascent (`Hax/Ascent/SquareDouble`): a list of legs at the concrete level is
  the top, a state-indexed value transformer at the abstract level the bottom.
* Machine-side ascent (`Ascent/SquareStrictDouble`): a block of instructions is the top, an
  abstract step the bottom.
* `RustM` ascent (`Ascent/RustMSquareDouble`): a state-passing continuation is the top, a
  state-indexed value map the bottom.

In the three ascent double categories the code is the top, so the image square says that the
abstract side refines the code. A lax square whose top is deterministic and whose bottom is
total transposes (`RelSemantics.laxSq_converse`). The code semantics of each ascent level is
deterministic and each abstract arrow is a total function, so each ascent judgment also gives
the refinement square with the abstract function on top, the code at the bottom and the
converse relations as sides, in which the code refines its specification.

The soundness of a certified pass chain is vertical pasting of refinement squares: the
refinement square of a chain on an accepted program is the vertical identity for the empty
chain and the vertical composite of the refinement square of the rest with that of the first
step otherwise (`PassChain.Cert.refSq`), and appending certificates pastes their refinement
squares vertically (`PassChain.Cert.refSq_append`).

## Main results

* `PassChain.sq_iff_refSq`, `CLevel.sq_iff_refSq`, `JLevel.sq_iff_refSq`,
  `MLevel.sq_iff_refSq`: a square of each double category is a refinement square.
* `PassChain.sq_prog_iff_refSq`, `PassChain.forall_refSq_iff_sound`,
  `PassChain.StepCert.refSq`: the refinement squares of programs and of a step certificate.
* `PassChain.Cert.refSq`, `PassChain.Cert.refSq_append`, `PassChain.Cert.sound_of_refSq`,
  `PassChain.refSq_functor`: soundness of a certified chain as vertical pasting.
* `CLevel.sq_conc_iff_refSq`, `CLevel.refSq_single_of_corres`,
  `CLevel.corres_of_refSq_single`, `JLevel.sq_mach_iff_refSq`, `JLevel.corresJ_iff_refSq`,
  `JLevel.runBlockTriple_iff_refSq`, `MLevel.sq_conc_iff_refSq`, `MLevel.corresM_iff_refSq`:
  the ascent judgments as refinement squares.
* `CLevel.refSq_spec_of_corres`, `JLevel.corresJ_iff_refSq_spec`,
  `JLevel.runBlockTriple_iff_refSq_spec`, `MLevel.refSq_spec_of_corresM`: the ascent
  judgments as refinement squares in which the code refines its specification.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory ThinDoubleCategory CatCrypt.Refinement.WRPRelSemantics

/-! ## Pass chains -/

namespace CatCrypt.Crypto.SecureCompilation.VIR.PassChain

variable {P Q R : Type}

/-- A square of the pass-chain double category is a refinement square: the bottom refines
the top. -/
theorem sq_iff_refSq {a b c d : Pt} (u : Hor.of a ⟶ Hor.of b) (f : a ⟶ c) (g : b ⟶ d)
    (w : Hor.of c ⟶ Hor.of d) :
    Sq u f g w ↔
      Sq ((relDouble Pt.relSemantics).mapH u) ((relDouble Pt.relSemantics).mapV f)
        ((relDouble Pt.relSemantics).mapV g) ((relDouble Pt.relSemantics).mapH w) :=
  relDouble_sq_iff Pt.relSemantics u f g w

/-- The refinement square of two programs: the source program `p` at the bottom refines the
compiled program `q` on top along `f` and `g` exactly when every successful run of `p` is
matched by a successful run of `q`. -/
theorem sq_prog_iff_refSq {S : Sem P} {T : Sem Q} (q : Q) (p : P) (f : T.inp ⟶ S.inp)
    (g : T.out ⟶ S.out) :
    (∀ (W : T.In) (V : S.In) (o : S.Out), f W V → S.den p V = some o →
        ∃ o' : T.Out, T.den q W = some o' ∧ g o' o) ↔
      Sq ((relDouble Pt.relSemantics).mapH (T.prog q)) ((relDouble Pt.relSemantics).mapV f)
        ((relDouble Pt.relSemantics).mapV g) ((relDouble Pt.relSemantics).mapH (S.prog p)) :=
  (sq_prog_iff q p f g).symm.trans (sq_iff_refSq _ f g _)

/-- The refinement squares over all programs a partial function accepts, with the converses
of two relations as vertical sides, are the soundness statement of a step certificate with
these relations. -/
theorem forall_refSq_iff_sound {S : Sem P} {T : Sem Q} (f : P → Option Q)
    (rI : S.In → T.In → Prop) (rO : S.Out → T.Out → Prop) :
    (∀ p q, f p = some q →
        Sq ((relDouble Pt.relSemantics).mapH (T.prog q))
          ((relDouble Pt.relSemantics).mapV (a := T.inp) (c := S.inp) (fun W V => rI V W))
          ((relDouble Pt.relSemantics).mapV (a := T.out) (c := S.out) (fun o' o => rO o o'))
          ((relDouble Pt.relSemantics).mapH (S.prog p))) ↔
      ∀ p q V W o, f p = some q → rI V W → S.den p V = some o →
        ∃ o', T.den q W = some o' ∧ rO o o' :=
  (forall_congr' fun p => forall_congr' fun q => forall_congr' fun _ =>
    (sq_iff_refSq (a := T.inp) (b := T.out) (c := S.inp) (d := S.out) (T.prog q)
      (fun W V => rI V W) (fun o' o => rO o o') (S.prog p)).symm).trans
    (forall_sq_iff_sound f rI rO)

/-- The refinement square of a certified step on an accepted program: the input program
refines the output program. -/
theorem StepCert.refSq {f : P → Option Q} {S : Sem P} {T : Sem Q} (C : StepCert f S T) {p : P}
    {q : Q} (hf : f p = some q) :
    Sq ((relDouble Pt.relSemantics).mapH (T.prog q)) ((relDouble Pt.relSemantics).mapV C.vIn)
      ((relDouble Pt.relSemantics).mapV C.vOut) ((relDouble Pt.relSemantics).mapH (S.prog p)) :=
  (sq_iff_refSq _ _ _ _).1 (C.sq hf)

/-- The refinement square of a certified chain on an accepted program, by vertical pasting:
the vertical identity square for the empty chain, and the vertical composite of the
refinement square of the rest with the refinement square of the first step otherwise. -/
theorem Cert.refSq {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) {p : P} {q : Q}
    (hrun : c.run p = some q) :
    Sq ((relDouble Pt.relSemantics).mapH (T.prog q)) ((relDouble Pt.relSemantics).mapV C.vIn)
      ((relDouble Pt.relSemantics).mapV C.vOut) ((relDouble Pt.relSemantics).mapH (S.prog p)) := by
  induction C with
  | nil S =>
    cases hrun
    exact (vid _).congr rfl
      (by rw [Cert.vIn_nil, (relDouble Pt.relSemantics).mapV_id])
      (by rw [Cert.vOut_nil, (relDouble Pt.relSemantics).mapV_id]) rfl
  | cons h C ih =>
    simp only [Chain.run, Option.bind_eq_some_iff] at hrun
    obtain ⟨p', hs, hrest⟩ := hrun
    exact (vcomp (ih hrest) (h.refSq hs)).congr rfl
      (by rw [Cert.vIn_cons, (relDouble Pt.relSemantics).mapV_comp])
      (by rw [Cert.vOut_cons, (relDouble Pt.relSemantics).mapV_comp]) rfl

/-- The refinement square of an appended certificate is the vertical composite of the
refinement square of the second part with that of the first. -/
theorem Cert.refSq_append {c : Chain P Q} {d : Chain Q R} {S : Sem P} {T : Sem Q} {U : Sem R}
    (C : Cert c S T) (D : Cert d T U) {p : P} {q : Q} {r : R} (hc : c.run p = some q)
    (hd : d.run q = some r) :
    Sq ((relDouble Pt.relSemantics).mapH (U.prog r))
      ((relDouble Pt.relSemantics).mapV (C.append D).vIn)
      ((relDouble Pt.relSemantics).mapV (C.append D).vOut)
      ((relDouble Pt.relSemantics).mapH (S.prog p)) :=
  (vcomp (D.refSq hd) (C.refSq hc)).congr rfl
    (by rw [Cert.vIn_append, (relDouble Pt.relSemantics).mapV_comp])
    (by rw [Cert.vOut_append, (relDouble Pt.relSemantics).mapV_comp]) rfl

/-- The statement of `Cert.sound`, read off the refinement square of the chain. -/
theorem Cert.sound_of_refSq {c : Chain P Q} {S : Sem P} {T : Sem Q} (C : Cert c S T) {p : P}
    {q : Q} {V : S.In} {W : T.In} {o : S.Out} (hrun : c.run p = some q)
    (hVW : C.relIn V W) (hden : S.den p V = some o) :
    ∃ o', T.den q W = some o' ∧ C.relOut o o' :=
  (sq_prog_iff_refSq q p C.vIn C.vOut).2 (C.refSq hrun) W V o hVW hden

/-- Every program accepted by a certified chain has the refinement square over the image of
the chain under `inFunctor` and `outFunctor`. -/
theorem refSq_functor {L L' : SemType} (F : L ⟶ L') {p : L.P} {q : L'.P}
    (hrun : F.1.run p = some q) :
    Sq ((relDouble Pt.relSemantics).mapH (L'.S.prog q))
      ((relDouble Pt.relSemantics).mapV (inFunctor.map F.op))
      ((relDouble Pt.relSemantics).mapV (outFunctor.map F.op))
      ((relDouble Pt.relSemantics).mapH (L.S.prog p)) :=
  F.2.refSq hrun

end CatCrypt.Crypto.SecureCompilation.VIR.PassChain

/-! ## Source-level ascent squares -/

namespace Hax.Ascent.CLevel

variable {bi : Builtins} {S : Type}

/-- A square of the source-level double category is a refinement square: the bottom refines
the top. -/
theorem sq_iff_refSq {a b c d : CLevel bi S} (u : Hor.of a ⟶ Hor.of b) (f : a ⟶ c)
    (g : b ⟶ d) (w : Hor.of c ⟶ Hor.of d) :
    Sq u f g w ↔
      Sq ((relDouble (relSemantics (bi := bi) (S := S))).mapH u)
        ((relDouble (relSemantics (bi := bi) (S := S))).mapV f)
        ((relDouble (relSemantics (bi := bi) (S := S))).mapV g)
        ((relDouble (relSemantics (bi := bi) (S := S))).mapH w) :=
  relDouble_sq_iff relSemantics u f g w

/-- The refinement square at the concrete-over-abstract boundary, with the legs `l` on top and
the value transformer `W` at the bottom. -/
theorem sq_conc_iff_refSq (l : List ImpExpr) (R R' : Env × Value → S × Value → Prop)
    (W : S → Value → Value) :
    (∀ x σ v, R x (σ, v) → ∃ x', blockSem bi l x x' ∧ R' x' (σ, W σ v)) ↔
      Sq ((relDouble (relSemantics (bi := bi) (S := S))).mapH (a := .conc) (b := .conc) l)
        ((relDouble (relSemantics (bi := bi) (S := S))).mapV (a := .conc) (c := .abs) R)
        ((relDouble (relSemantics (bi := bi) (S := S))).mapV (a := .conc) (c := .abs) R')
        ((relDouble (relSemantics (bi := bi) (S := S))).mapH (a := .abs) (b := .abs) W) :=
  (sq_conc_iff l R R' W).symm.trans
    (sq_iff_refSq (a := .conc) (b := .conc) (c := .abs) (d := .abs) l R R' W)

/-- A `Corres` square whose value is plain under the guard gives the refinement square over
the one-leg list `[e]`. -/
theorem refSq_single_of_corres {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q)
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    Sq ((relDouble (relSemantics (bi := bi) (S := S))).mapH (a := .conc) (b := .conc) [e])
      ((relDouble (relSemantics (bi := bi) (S := S))).mapV (a := .conc) (c := .abs)
        (entryRel P G))
      ((relDouble (relSemantics (bi := bi) (S := S))).mapV (a := .conc) (c := .abs)
        (exitRel Q))
      ((relDouble (relSemantics (bi := bi) (S := S))).mapH (a := .abs) (b := .abs)
        (fun σ _ => V σ)) :=
  (sq_iff_refSq (a := .conc) (b := .conc) _ _ _ _).1 (sq_single_of_corres h hplain)

/-- The refinement square over the one-leg list `[e]` gives the `Corres` square of `e`. -/
theorem corres_of_refSq_single {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value}
    (h : Sq ((relDouble (relSemantics (bi := bi) (S := S))).mapH (a := .conc) (b := .conc) [e])
      ((relDouble (relSemantics (bi := bi) (S := S))).mapV (a := .conc) (c := .abs)
        (entryRel P G))
      ((relDouble (relSemantics (bi := bi) (S := S))).mapV (a := .conc) (c := .abs)
        (exitRel Q))
      ((relDouble (relSemantics (bi := bi) (S := S))).mapH (a := .abs) (b := .abs)
        (fun σ _ => V σ))) :
    Corres bi P G e V Q :=
  corres_of_sq_single ((sq_iff_refSq (a := .conc) (b := .conc) _ _ _ _).2 h)

/-- A leg relates an input to at most one output. -/
theorem leafSem_deterministic {e : ImpExpr} {x y₁ y₂ : Env × Value}
    (h₁ : leafSem bi e x y₁) (h₂ : leafSem bi e x y₂) : y₁ = y₂ := by
  obtain ⟨_, f₁, hr₁⟩ := h₁
  obtain ⟨_, f₂, hr₂⟩ := h₂
  have h := (hr₁ (max f₁ f₂) (le_max_left _ _)).symm.trans (hr₂ (max f₁ f₂) (le_max_right _ _))
  grind [Prod.ext_iff]

/-- A list of legs relates an input to at most one output. -/
theorem blockSem_deterministic :
    ∀ (l : List ImpExpr) (x y₁ y₂ : Env × Value), blockSem bi l x y₁ → blockSem bi l x y₂ →
      y₁ = y₂
  | [], _, _, _, h₁, h₂ => h₁.symm.trans h₂
  | _ :: es, _, _, _, ⟨_, hm₁, h₁⟩, ⟨_, hm₂, h₂⟩ => by
    cases leafSem_deterministic hm₁ hm₂
    exact blockSem_deterministic es _ _ _ h₁ h₂

/-- A `Corres` square whose value is plain under the guard gives the refinement square in
which the leg `e` refines its specification: the value transformer `fun σ _ => V σ` is the
top, the one-leg list `[e]` the bottom, and the converses of `entryRel P G` and `exitRel Q`
the sides. It is the transpose of `refSq_single_of_corres`, by the determinism of the leg
semantics (`blockSem_deterministic`) and the totality of the transformer. -/
theorem refSq_spec_of_corres {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q)
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    Sq ((relDouble (relSemantics (bi := bi) (S := S))).mapH (a := .abs) (b := .abs)
        (fun σ _ => V σ))
      ((relDouble (relSemantics (bi := bi) (S := S))).mapV (a := .abs) (c := .conc)
        (fun y x => entryRel P G x y))
      ((relDouble (relSemantics (bi := bi) (S := S))).mapV (a := .abs) (c := .conc)
        (fun y x => exitRel Q x y))
      ((relDouble (relSemantics (bi := bi) (S := S))).mapH (a := .conc) (b := .conc) [e]) :=
  (sq_iff_refSq (a := .abs) (b := .abs) (c := .conc) (d := .conc) _ _ _ _).1
    (RelSemantics.laxSq_converse relSemantics (blockSem_deterministic [e])
      (fun _ => ⟨_, rfl⟩) (sq_single_of_corres h hplain))

end Hax.Ascent.CLevel

/-! ## Machine-side ascent squares -/

namespace CatCrypt.Crypto.SecureCompilation.Ascent.JLevel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

variable {A : Type}

/-- A square of the machine-side double category is a refinement square: the bottom refines
the top. -/
theorem sq_iff_refSq {a b c d : JLevel A} (u : Hor.of a ⟶ Hor.of b) (f : a ⟶ c) (g : b ⟶ d)
    (w : Hor.of c ⟶ Hor.of d) :
    Sq u f g w ↔
      Sq ((relDouble (relSemantics (A := A))).mapH u) ((relDouble (relSemantics (A := A))).mapV f)
        ((relDouble (relSemantics (A := A))).mapV g) ((relDouble (relSemantics (A := A))).mapH w) :=
  relDouble_sq_iff relSemantics u f g w

/-- The refinement square with a block `c` on top and an abstract step `fa` at the bottom is
the forward simulation of `fa` by `c`. -/
theorem sq_mach_iff_refSq (c : List (JInstr 64)) (R R' : JState 64 → A → Prop) (fa : A → A) :
    (∀ st a, R st a → R' (runBlock st c) (fa a)) ↔
      Sq ((relDouble (relSemantics (A := A))).mapH (a := .mach) (b := .mach) c)
        ((relDouble (relSemantics (A := A))).mapV (a := .mach) (c := .abs) R)
        ((relDouble (relSemantics (A := A))).mapV (a := .mach) (c := .abs) R')
        ((relDouble (relSemantics (A := A))).mapH (a := .abs) (b := .abs) fa) :=
  (sq_mach_iff c R R' fa).symm.trans
    (sq_iff_refSq (a := .mach) (b := .mach) (c := .abs) (d := .abs) c R R' fa)

/-- `CorresJ SR P fa c` is the refinement square with left side `SR` restricted to `P`, right
side `SR`, top `c` and bottom `fa`. -/
theorem corresJ_iff_refSq (SR : JState 64 → A → Prop) (P : A → Prop) (fa : A → A)
    (c : List (JInstr 64)) :
    CorresJ SR P fa c ↔
      Sq ((relDouble (relSemantics (A := A))).mapH (a := .mach) (b := .mach) c)
        ((relDouble (relSemantics (A := A))).mapV (a := .mach) (c := .abs)
          (fun st a => SR st a ∧ P a))
        ((relDouble (relSemantics (A := A))).mapV (a := .mach) (c := .abs) SR)
        ((relDouble (relSemantics (A := A))).mapH (a := .abs) (b := .abs) fa) :=
  (corresJ_iff_sq SR P fa c).trans (sq_iff_refSq (a := .mach) (b := .mach) _ _ _ _)

/-- `RunBlockTriple P c Q` is the refinement square over the one-point abstract state with
the identity step at the bottom and the predicates `P`, `Q` as the sides. -/
theorem runBlockTriple_iff_refSq (P Q : JState 64 → Prop) (c : List (JInstr 64)) :
    RunBlockTriple P c Q ↔
      Sq ((relDouble (relSemantics (A := Unit))).mapH (a := .mach) (b := .mach) c)
        ((relDouble (relSemantics (A := Unit))).mapV (a := .mach) (c := .abs)
          (fun st _ => P st))
        ((relDouble (relSemantics (A := Unit))).mapV (a := .mach) (c := .abs)
          (fun st _ => Q st))
        ((relDouble (relSemantics (A := Unit))).mapH (a := .abs) (b := .abs) id) :=
  (runBlockTriple_iff_sq P Q c).trans (sq_iff_refSq (a := .mach) (b := .mach) _ _ _ _)

/-- A block relates a machine state to at most one machine state. -/
theorem sem_mach_deterministic (c : List (JInstr 64)) (st st₁ st₂ : JState 64)
    (h₁ : (relSemantics (A := A)).sem (a := .mach) (b := .mach) c st st₁)
    (h₂ : (relSemantics (A := A)).sem (a := .mach) (b := .mach) c st st₂) : st₁ = st₂ :=
  (show runBlock st c = st₁ from h₁).symm.trans h₂

/-- An abstract step relates a state to at most one state. -/
theorem sem_abs_deterministic (fa : A → A) (x x₁ x₂ : A)
    (h₁ : (relSemantics (A := A)).sem (a := .abs) (b := .abs) fa x x₁)
    (h₂ : (relSemantics (A := A)).sem (a := .abs) (b := .abs) fa x x₂) : x₁ = x₂ :=
  (show fa x = x₁ from h₁).symm.trans h₂

/-- The square with a block `c` on top and an abstract step `fa` at the bottom transposes
to the square with `fa` on top, `c` at the bottom and the converse sides, and back: both
semantics are graphs of functions. -/
theorem sq_mach_iff_sq_spec (c : List (JInstr 64)) (R R' : JState 64 → A → Prop)
    (fa : A → A) :
    Sq (C := JLevel A) (a := .mach) (b := .mach) (c := .abs) (d := .abs) c R R' fa ↔
      Sq (C := JLevel A) (a := .abs) (b := .abs) (c := .mach) (d := .mach) fa
        (fun a st => R st a) (fun a st => R' st a) c :=
  ⟨RelSemantics.laxSq_converse relSemantics (sem_mach_deterministic c) (fun _ => ⟨_, rfl⟩),
    RelSemantics.laxSq_converse relSemantics (sem_abs_deterministic fa) (fun _ => ⟨_, rfl⟩)⟩

/-- `CorresJ SR P fa c` is the refinement square in which the block `c` refines its
specification: the abstract step `fa` is the top, `c` the bottom, and the converses of `SR`
restricted to `P` and of `SR` the sides. It is the transpose of `corresJ_iff_refSq`. -/
theorem corresJ_iff_refSq_spec (SR : JState 64 → A → Prop) (P : A → Prop) (fa : A → A)
    (c : List (JInstr 64)) :
    CorresJ SR P fa c ↔
      Sq ((relDouble (relSemantics (A := A))).mapH (a := .abs) (b := .abs) fa)
        ((relDouble (relSemantics (A := A))).mapV (a := .abs) (c := .mach)
          (fun a st => SR st a ∧ P a))
        ((relDouble (relSemantics (A := A))).mapV (a := .abs) (c := .mach)
          (fun a st => SR st a))
        ((relDouble (relSemantics (A := A))).mapH (a := .mach) (b := .mach) c) :=
  ((corresJ_iff_sq SR P fa c).trans (sq_mach_iff_sq_spec c _ SR fa)).trans
    (sq_iff_refSq (a := .abs) (b := .abs) (c := .mach) (d := .mach) _ _ _ _)

/-- `RunBlockTriple P c Q` is the refinement square over the one-point abstract state in
which the block `c` refines the identity step: `id` is the top, `c` the bottom, and the
predicates `P`, `Q` the sides. It is the transpose of `runBlockTriple_iff_refSq`. -/
theorem runBlockTriple_iff_refSq_spec (P Q : JState 64 → Prop) (c : List (JInstr 64)) :
    RunBlockTriple P c Q ↔
      Sq ((relDouble (relSemantics (A := Unit))).mapH (a := .abs) (b := .abs) id)
        ((relDouble (relSemantics (A := Unit))).mapV (a := .abs) (c := .mach)
          (fun _ st => P st))
        ((relDouble (relSemantics (A := Unit))).mapV (a := .abs) (c := .mach)
          (fun _ st => Q st))
        ((relDouble (relSemantics (A := Unit))).mapH (a := .mach) (b := .mach) c) :=
  ((runBlockTriple_iff_sq P Q c).trans (sq_mach_iff_sq_spec (A := Unit) c _ _ id)).trans
    (sq_iff_refSq (a := .abs) (b := .abs) (c := .mach) (d := .mach) _ _ _ _)

end CatCrypt.Crypto.SecureCompilation.Ascent.JLevel

/-! ## `RustM` ascent squares -/

namespace Hax.Ascent.RustM.MLevel

variable {C S : Type}

/-- A square of the `RustM` double category is a refinement square: the bottom refines the
top. -/
theorem sq_iff_refSq {a b c d : MLevel C S} (u : Hor.of a ⟶ Hor.of b) (f : a ⟶ c) (g : b ⟶ d)
    (w : Hor.of c ⟶ Hor.of d) :
    Sq u f g w ↔
      Sq ((relDouble (relSemantics (C := C) (S := S))).mapH u)
        ((relDouble (relSemantics (C := C) (S := S))).mapV f)
        ((relDouble (relSemantics (C := C) (S := S))).mapV g)
        ((relDouble (relSemantics (C := C) (S := S))).mapH w) :=
  relDouble_sq_iff relSemantics u f g w

/-- The refinement square at the concrete-over-abstract boundary, with the continuation `f`
on top and the value map `W` at the bottom. -/
theorem sq_conc_iff_refSq {A B : Type} (f : A → C → Aeneas.Std.RustM (B × C))
    (R : A × C → A × S → Prop) (R' : B × C → B × S → Prop) (W : S → A → B) :
    (∀ x a σ, R x (a, σ) → ∃ y, f x.1 x.2 = .ok y ∧ R' y (W σ a, σ)) ↔
      Sq ((relDouble (relSemantics (C := C) (S := S))).mapH (a := .conc A) (b := .conc B) f)
        ((relDouble (relSemantics (C := C) (S := S))).mapV (a := .conc A) (c := .abs A) R)
        ((relDouble (relSemantics (C := C) (S := S))).mapV (a := .conc B) (c := .abs B) R')
        ((relDouble (relSemantics (C := C) (S := S))).mapH (a := .abs A) (b := .abs B) W) :=
  (sq_conc_iff f R R' W).symm.trans
    (sq_iff_refSq (a := .conc A) (b := .conc B) (c := .abs A) (d := .abs B) f R R' W)

/-- `CorresM P G p V Q` is the refinement square from `conc Unit` to `conc A` over `abs Unit`
to `abs A` with top the program `p` and bottom the value map `V`. -/
theorem corresM_iff_refSq {A : Type} (P Q : C → S → Prop) (G : S → Prop)
    (p : C → Aeneas.Std.RustM (A × C)) (V : S → A) :
    CorresM P G p V Q ↔
      Sq ((relDouble (relSemantics (C := C) (S := S))).mapH (a := .conc Unit) (b := .conc A)
          (fun (_ : Unit) c => p c))
        ((relDouble (relSemantics (C := C) (S := S))).mapV (a := .conc Unit) (c := .abs Unit)
          (fun x y => P x.2 y.2 ∧ G y.2))
        ((relDouble (relSemantics (C := C) (S := S))).mapV (a := .conc A) (c := .abs A)
          (fun x y => Q x.2 y.2 ∧ x.1 = y.1))
        ((relDouble (relSemantics (C := C) (S := S))).mapH (a := .abs Unit) (b := .abs A)
          (fun σ _ => V σ)) :=
  (corresM_iff_sq P Q G p V).trans
    (sq_iff_refSq (a := .conc Unit) (b := .conc A) (c := .abs Unit) (d := .abs A) _ _ _ _)

/-- A continuation relates an input to at most one output: its `.ok` result. -/
theorem sem_conc_deterministic {A B : Type} (f : A → C → Aeneas.Std.RustM (B × C))
    (x : A × C) (y₁ y₂ : B × C)
    (h₁ : (relSemantics (C := C) (S := S)).sem (a := .conc A) (b := .conc B) f x y₁)
    (h₂ : (relSemantics (C := C) (S := S)).sem (a := .conc A) (b := .conc B) f x y₂) :
    y₁ = y₂ := by
  have h : Aeneas.Std.RustM.ok y₁ = .ok y₂ :=
    (show f x.1 x.2 = .ok y₁ from h₁).symm.trans h₂
  cases h
  rfl

/-- `CorresM P G p V Q` gives the refinement square in which the program `p` refines its
specification: the value map `fun σ _ => V σ` from `abs Unit` to `abs A` is the top, `p`
from `conc Unit` to `conc A` the bottom, and the converses of the sides of
`corresM_iff_refSq` the sides. It is the transpose of `corresM_iff_refSq`, by the
determinism of `RustM` continuations (`sem_conc_deterministic`) and the totality of the
value map; it constrains the `.ok` results of `p` only. -/
theorem refSq_spec_of_corresM {A : Type} {P Q : C → S → Prop} {G : S → Prop}
    {p : C → Aeneas.Std.RustM (A × C)} {V : S → A} (h : CorresM P G p V Q) :
    Sq ((relDouble (relSemantics (C := C) (S := S))).mapH (a := .abs Unit) (b := .abs A)
        (fun σ _ => V σ))
      ((relDouble (relSemantics (C := C) (S := S))).mapV (a := .abs Unit) (c := .conc Unit)
        (fun y x => P x.2 y.2 ∧ G y.2))
      ((relDouble (relSemantics (C := C) (S := S))).mapV (a := .abs A) (c := .conc A)
        (fun y x => Q x.2 y.2 ∧ x.1 = y.1))
      ((relDouble (relSemantics (C := C) (S := S))).mapH (a := .conc Unit) (b := .conc A)
        (fun (_ : Unit) c => p c)) :=
  (sq_iff_refSq (a := .abs Unit) (b := .abs A) (c := .conc Unit) (d := .conc A) _ _ _ _).1
    (RelSemantics.laxSq_converse relSemantics
      (sem_conc_deterministic (S := S) (fun (_ : Unit) c => p c)) (fun _ => ⟨_, rfl⟩)
      ((corresM_iff_sq P Q G p V).1 h))

end Hax.Ascent.RustM.MLevel
