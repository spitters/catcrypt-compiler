/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy

/-!
# The write set of the emitted secp256k1 field-multiply brick

`Secp256k1PointOpFront.emitFOp idx (.mul o a b)` is the command list the
half-limb operand-scanning multiply, four Solinas folds, conditional subtract and
branch-free select emit for one `mul` entry of a point-op schedule. Every command
it emits is an `RScalarSetExpr`, and the name each one binds is either inside the
brick's private `op{idx}` namespace or one of the eight half-limb slots
`s!"{o}h{k}"` of the output field element.

That write set determines the non-interference half of
`Secp256k1PointOpFrontDenote.BrickStep` at the `mul` arm: a schedule field
element other than the output keeps its half-limb residue readout `feVal` across
the brick. The proof is generator-level — it carries the write-set predicate
through the `Id`-monad loops of `genMul` / `genAdd` / `genSub` / `genFold` with
`Secp256k1PointOpFrontCovered.forIn_range_inv`, so no generated command list is
reduced.

The value half — that the output field element ends holding
`fm (feVal env a) (feVal env b)` — needs entry conditions that `BrickStep` does
not carry. `MulEntry` states them (the reduction constants at their intended
values, both operands held in proper 32-bit half-limbs, both canonical residues
mod `p`), `MulBrickValue` states the value half under them, and
`brickStepMul_of_value` assembles the two halves into the `mul` arm of the
per-brick step.

## Main results

* `HeadIs`, `HeadIs.append`, `hName_inj` — first-character and half-limb-name
  hygiene: a half-limb name determines its field element.
* `WritesIn`, `envReader_seqAll_frame` — a command list whose bindings all satisfy
  a name predicate leaves every other non-temporary slot's word reader alone.
* `genMul_writes`, `genAdd_writes`, `genSub_writes`, `genFold_writes`,
  `feMulHalves_writes`, `feAddHalves_writes`, `feSubHalves_writes` — each limb
  builder and each of the three field bricks binds only names in its private
  prefix's namespace.
* `emitFOp_mul_writes` — the emitted `mul` brick binds only `op{idx}`-namespace
  names and the output field element's half-limb slots.
* `feVal_frame_mul` — a schedule field element other than the output keeps its
  half-limb residue readout across the brick.
* `MulEntry`, `MulBrickValue`, `brickStepMul_of_value` — the entry conditions,
  the residual value obligation over them, and the `mul` arm of the per-brick
  step assembled from the value obligation and the frame.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickFrame

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
  (envReader_setExpr_off)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
  (genMul genAdd genFold genSub seqAll sv pNat mask32 pl32 cc0 cc1)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional (stepFOpG envUpd)

/-! ## 1. First characters and half-limb names -/

/-- A name whose first character is `c`. -/
def HeadIs (c : Char) (s : String) : Prop := ∃ t, s.toList = c :: t

theorem HeadIs.append {c : Char} {s : String} (h : HeadIs c s) (u : String) :
    HeadIs c (s ++ u) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t ++ u.toList, by rw [String.toList_append, ht]; rfl⟩

theorem HeadIs.headOk {c : Char} {s : String} (h : HeadIs c s) (hc : c ≠ '_') :
    HeadOk s := by
  obtain ⟨t, ht⟩ := h
  exact ⟨c, t, ht, hc⟩

/-- The name `s!"{fe}h{k}"` of a field element's half-limb slot, for a
    single-digit index, determines the field element. -/
theorem hName_inj (o fe : String) (k k' : Nat) (hk : k < 8) (hk' : k' < 8)
    (h : s!"{o}h{k}" = s!"{fe}h{k'}") : o = fe := by
  have h2 := congrArg String.toList h
  simp only [String.toList_append, List.append_assoc] at h2
  refine String.ext ?_
  refine (List.append_inj' h2 ?_).1
  interval_cases k <;> interval_cases k' <;> rfl

/-- A half-limb name inherits the field element's first character. -/
theorem headIs_hName {c : Char} {fe : String} (h : HeadIs c fe) (k : Nat) :
    HeadIs c s!"{fe}h{k}" := (h.append _).append _

/-- A schedule field-element name starts with an upper-case letter. -/
theorem headIs_of_schedNameB {fe : String} (h : schedNameB fe = true) :
    ∃ c, HeadIs c fe ∧ c.isUpper = true := by
  unfold schedNameB at h
  match hfe : fe.toList with
  | [] => rw [hfe] at h; exact absurd h (by decide)
  | c :: t => exact ⟨c, ⟨t, hfe⟩, by rw [hfe] at h; simpa using h⟩

/-! ## 2. The write set of a command list

`WritesIn P l` says every command of `l` is a scalar assignment whose destination
satisfies `P`. Under it the word reader is stable off `P`. -/

/-- Every command of `l` binds a scalar slot whose name satisfies `P`. -/
def WritesIn (P : String → Prop) (l : List LowCT) : Prop :=
  ∀ c ∈ l, ∃ x e, c = LowCT.RScalarSetExpr x e ∧ P x

theorem writesIn_nil (P : String → Prop) : WritesIn P [] := by intro c hc; cases hc

theorem writesIn_append {P : String → Prop} {l₁ l₂ : List LowCT}
    (h₁ : WritesIn P l₁) (h₂ : WritesIn P l₂) : WritesIn P (l₁ ++ l₂) := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · exact h₁ d h
  · exact h₂ d h

theorem writesIn_snoc {P : String → Prop} {l : List LowCT} {x : String} {e : SExpr}
    (hl : WritesIn P l) (hx : P x) : WritesIn P (l ++ [LowCT.RScalarSetExpr x e]) :=
  writesIn_append hl (by intro d hd; rcases List.mem_singleton.mp hd with rfl; exact ⟨x, e, rfl, hx⟩)

theorem writesIn_cons {P : String → Prop} {x : String} {e : SExpr} {l : List LowCT}
    (hx : P x) (hl : WritesIn P l) : WritesIn P (LowCT.RScalarSetExpr x e :: l) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | h
  · exact ⟨x, e, rfl, hx⟩
  · exact hl d h

theorem writesIn_mono {P Q : String → Prop} (hPQ : ∀ x, P x → Q x) {l : List LowCT}
    (h : WritesIn P l) : WritesIn Q l := by
  intro d hd
  obtain ⟨x, e, rfl, hx⟩ := h d hd
  exact ⟨x, e, rfl, hPQ x hx⟩

theorem writesIn_map_range {P : String → Prop} (n : Nat) (f : Nat → String)
    (g : Nat → SExpr) (hf : ∀ i, i < n → P (f i)) :
    WritesIn P ((List.range n).map (fun i => LowCT.RScalarSetExpr (f i) (g i))) := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  exact ⟨f i, g i, rfl, hf i (List.mem_range.mp hi)⟩

/-- **A command list that binds only `P`-names leaves every other non-temporary
    slot's word reader alone.** -/
theorem envReader_seqAll_frame (P : String → Prop) :
    ∀ (l : List LowCT), WritesIn P l →
      ∀ (env env' : SEnvScalar), semScalar (seqAll l) env = some env' →
        ∀ s, ¬ isTmpName s → ¬ P s → envReader env' s = envReader env s := by
  intro l
  induction l with
  | nil =>
      intro _ env env' hsem s _ _
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      rfl
  | cons c cs ih =>
      intro hw env env' hsem s hts hps
      obtain ⟨x, e, rfl, hx⟩ := hw c (.head _)
      rw [semScalar_seqAll_cons] at hsem
      cases hc : semScalar (LowCT.RScalarSetExpr x e) env with
      | none => rw [hc] at hsem; simp at hsem
      | some e1 =>
          rw [hc] at hsem
          simp only [Option.bind_some] at hsem
          have hne : s ≠ x := by rintro rfl; exact hps hx
          rw [ih (fun d hd => hw d (.tail _ hd)) e1 env' hsem s hts hps,
            envReader_setExpr_off hc s hts hne]

/-! ## 3. The limb builders bind only names in their private prefix's namespace

Each builder's `Id`-monad loop is the one `Secp256k1PointOpFrontCovered` mirrors;
the write-set predicate rides the same invariant. `Q` ranges over name predicates
closed under suffix extension, which is what a private-prefix namespace is. -/

/-- A name predicate closed under suffix extension. -/
def SuffixClosed (Q : String → Prop) : Prop := ∀ (s u : String), Q s → Q (s ++ u)

/-- **`genMul` binds only names extending its private prefix.** -/
theorem genMul_writes {Q : String → Prop} (hQ : SuffixClosed Q)
    (zero : String) (aN bN : List String) (pfx : String) (hp : Q pfx) :
    WritesIn Q (genMul zero aN bN pfx).1 := by
  have hstep : ∀ (i j : Nat) (s s' : MulI),
      WritesIn Q s.snd.snd → genMulInnerStep zero aN bN pfx i j s = ForInStep.yield s' →
        WritesIn Q s'.snd.snd := by
    intro i j s s' hs hy
    simp only [genMulInnerStep] at hy
    injection hy with hy
    subst hy
    exact writesIn_snoc (writesIn_snoc (writesIn_snoc hs
        (hQ _ _ (hQ _ _ (hQ _ _ (hQ _ _ hp)))))
      (hQ _ _ (hQ _ _ (hQ _ _ (hQ _ _ hp)))))
      (hQ _ _ (hQ _ _ (hQ _ _ (hQ _ _ hp))))
  have houter : ∀ (i : Nat) (s s' : MulO),
      WritesIn Q s.snd → genMulOuterStep zero aN bN pfx i s = ForInStep.yield s' →
        WritesIn Q s'.snd := by
    intro i s s' hs hy
    simp only [genMulOuterStep] at hy
    injection hy with hy
    subst hy
    refine forIn_range_inv (fun r : MulI => WritesIn Q r.snd.snd) _ _ _ hs
      (hstep i) ?_
    intro j t t' _ hd
    simp only [genMulInnerStep] at hd
    injection hd
  have key : WritesIn Q (genMulRun zero aN bN pfx).snd := by
    unfold genMulRun
    refine forIn_range_inv (fun r : MulO => WritesIn Q r.snd) aN.length
      (genMulOuterStep zero aN bN pfx) _ (writesIn_nil Q) houter ?_
    intro i t t' _ hd
    simp only [genMulOuterStep] at hd
    injection hd
  rw [genMul_eq]
  exact key

/-- **`genAdd` binds only names extending its private prefix.** -/
theorem genAdd_writes {Q : String → Prop} (hQ : SuffixClosed Q)
    (zero : String) (aN bN : List String) (pfx : String) (hp : Q pfx) :
    WritesIn Q (genAdd zero aN bN pfx).1 := by
  have hstep : ∀ (i : Nat) (s s' : AddS),
      WritesIn Q s.snd.fst → genAddStep zero aN bN pfx i s = ForInStep.yield s' →
        WritesIn Q s'.snd.fst := by
    intro i s s' hs hy
    simp only [genAddStep] at hy
    injection hy with hy
    subst hy
    exact writesIn_snoc (writesIn_snoc (writesIn_snoc hs
        (hQ _ _ (hQ _ _ hp))) (hQ _ _ (hQ _ _ hp))) (hQ _ _ (hQ _ _ hp))
  have key : WritesIn Q (genAddRun zero aN bN pfx).snd.fst := by
    unfold genAddRun
    refine forIn_range_inv (fun r : AddS => WritesIn Q r.snd.fst) _
      (genAddStep zero aN bN pfx) _ (writesIn_nil Q) hstep ?_
    intro i t t' _ hd
    simp only [genAddStep] at hd
    injection hd
  rw [genAdd_eq]
  exact key

/-- **`genSub` binds only names extending its private prefix.** -/
theorem genSub_writes {Q : String → Prop} (hQ : SuffixClosed Q)
    (zero : String) (aN pN : List String) (pfx : String) (hp : Q pfx) :
    WritesIn Q (genSub zero aN pN pfx).1 := by
  have hstep : ∀ (i : Nat) (s s' : SubS),
      WritesIn Q s.snd.fst → genSubStep zero aN pN pfx i s = ForInStep.yield s' →
        WritesIn Q s'.snd.fst := by
    intro i s s' hs hy
    simp only [genSubStep] at hy
    injection hy with hy
    subst hy
    exact writesIn_snoc (writesIn_snoc (writesIn_snoc (writesIn_snoc hs
        (hQ _ _ (hQ _ _ hp))) (hQ _ _ (hQ _ _ hp))) (hQ _ _ (hQ _ _ hp)))
      (hQ _ _ (hQ _ _ hp))
  have key : WritesIn Q (genSubRun zero aN pN pfx).snd.fst := by
    unfold genSubRun
    refine forIn_range_inv (fun r : SubS => WritesIn Q r.snd.fst) _
      (genSubStep zero aN pN pfx) _ (writesIn_nil Q) hstep ?_
    intro i t t' _ hd
    simp only [genSubStep] at hd
    injection hd
  rw [genSub_eq]
  exact key

/-- **`genFold` binds only names extending its private prefix.** -/
theorem genFold_writes {Q : String → Prop} (hQ : SuffixClosed Q)
    (zero c0N c1N : String) (full : List String) (pfx : String) (hp : Q pfx) :
    WritesIn Q (genFold zero c0N c1N full pfx).1 := by
  have hgen : genFold zero c0N c1N full pfx =
      if (full.drop 8).isEmpty then ([], full)
      else ((genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).1
              ++ (genAdd zero (full.take 8)
                    (genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).2 (pfx ++ "a")).1,
            (genAdd zero (full.take 8)
              (genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).2 (pfx ++ "a")).2) := rfl
  rw [hgen]
  split
  · exact writesIn_nil Q
  · exact writesIn_append (genMul_writes hQ _ _ _ _ (hQ _ _ hp))
      (genAdd_writes hQ _ _ _ _ (hQ _ _ hp))

/-- Every index of a name list built by mapping over `List.range n` reads either a
    mapped name or the empty default. -/
theorem map_range_getBang_or_empty {Q : String → Prop} (n : Nat) (f : Nat → String)
    (hf : ∀ k, Q (f k)) (i : Nat) :
    Q ((List.range n).map f)[i]! ∨ ((List.range n).map f)[i]! = "" := by
  rw [List.getElem!_eq_getElem?_getD]
  cases hl : ((List.range n).map f)[i]? with
  | none => exact Or.inr (by simp)
  | some v =>
      refine Or.inl ?_
      simp only [List.getElem?_map] at hl
      cases hr : (List.range n)[i]? with
      | none => rw [hr] at hl; simp at hl
      | some w =>
          rw [hr] at hl
          simp only [Option.map_some, Option.some.injEq] at hl
          subst hl
          simpa using hf w

/-- **The `feMul` brick binds only names extending its private prefix**, up to the
    empty name an out-of-range builder index reads. -/
theorem feMulHalves_writes {Q : String → Prop} (hQ : SuffixClosed Q)
    (pfx : String) (A B : List String) (hp : Q pfx) :
    WritesIn (fun x => Q x ∨ x = "") (feMulHalves pfx A B).1 := by
  have h1 : ∀ u : String, Q (pfx ++ u) := fun u => hQ pfx u hp
  have h2 : ∀ u v : String, Q (pfx ++ u ++ v) := fun u v => hQ (pfx ++ u) v (h1 u)
  have hw : ∀ u : String, (fun x => Q x ∨ x = "") (pfx ++ u) := fun u => Or.inl (h1 u)
  unfold feMulHalves
  refine forIn_range_inv (WritesIn (fun x => Q x ∨ x = "")) 8 _ _ ?_ ?_ ?_
  · refine writesIn_append (writesIn_mono (fun x hx => Or.inl hx) ?_)
      (writesIn_cons (hw _) (writesIn_cons (hw _) (writesIn_cons (hw _) (writesIn_nil _))))
    exact writesIn_append (writesIn_append (writesIn_append
        (writesIn_append (writesIn_append
          (genMul_writes hQ _ _ _ _ (h1 _)) (genFold_writes hQ _ _ _ _ _ (h1 _)))
          (genFold_writes hQ _ _ _ _ _ (h1 _))) (genFold_writes hQ _ _ _ _ _ (h1 _)))
          (genFold_writes hQ _ _ _ _ _ (h1 _))) (genSub_writes hQ _ _ _ _ (h1 _))
  · intro i s s' hs hy
    injection hy with hy
    subst hy
    exact writesIn_snoc hs (map_range_getBang_or_empty 8 _ (fun k => h2 _ _) i)
  · intro i s s' _ hd
    injection hd


/-- **The `feAdd` brick binds only names extending its private prefix**, up to the
    empty name an out-of-range builder index reads. -/
theorem feAddHalves_writes {Q : String → Prop} (hQ : SuffixClosed Q)
    (pfx : String) (A B : List String) (hp : Q pfx) :
    WritesIn (fun x => Q x ∨ x = "") (feAddHalves pfx A B).1 := by
  have h1 : ∀ u : String, Q (pfx ++ u) := fun u => hQ pfx u hp
  have h2 : ∀ u v : String, Q (pfx ++ u ++ v) := fun u v => hQ (pfx ++ u) v (h1 u)
  have hw : ∀ u : String, (fun x => Q x ∨ x = "") (pfx ++ u) := fun u => Or.inl (h1 u)
  unfold feAddHalves
  refine forIn_range_inv (WritesIn (fun x => Q x ∨ x = "")) 8 _ _ ?_ ?_ ?_
  · refine writesIn_append (writesIn_mono (fun x hx => Or.inl hx) ?_)
      (writesIn_cons (hw _) (writesIn_cons (hw _) (writesIn_cons (hw _) (writesIn_nil _))))
    exact writesIn_append (genAdd_writes hQ _ _ _ _ (h1 _))
      (genSub_writes hQ _ _ _ _ (h1 _))
  · intro i s s' hs hy
    injection hy with hy
    subst hy
    exact writesIn_snoc hs (map_range_getBang_or_empty 8 _ (fun k => h2 _ _) i)
  · intro i s s' _ hd
    injection hd

/-- **The `feSub` brick binds only names extending its private prefix**, up to the
    empty name an out-of-range builder index reads. -/
theorem feSubHalves_writes {Q : String → Prop} (hQ : SuffixClosed Q)
    (pfx : String) (A B : List String) (hp : Q pfx) :
    WritesIn (fun x => Q x ∨ x = "") (feSubHalves pfx A B).1 := by
  have h1 : ∀ u : String, Q (pfx ++ u) := fun u => hQ pfx u hp
  have h2 : ∀ u v : String, Q (pfx ++ u ++ v) := fun u v => hQ (pfx ++ u) v (h1 u)
  have hw : ∀ u : String, (fun x => Q x ∨ x = "") (pfx ++ u) := fun u => Or.inl (h1 u)
  unfold feSubHalves
  refine writesIn_append ?_
    (writesIn_mono (fun x hx => Or.inl hx) (genAdd_writes hQ _ _ _ _ (h1 _)))
  refine forIn_range_inv (WritesIn (fun x => Q x ∨ x = "")) 8 _ _ ?_ ?_ ?_
  · exact writesIn_append
      (writesIn_mono (fun x hx => Or.inl hx) (genSub_writes hQ _ _ _ _ (h1 _)))
      (writesIn_cons (hw _) (writesIn_cons (hw _) (writesIn_nil _)))
  · intro i s s' hs hy
    injection hy with hy
    subst hy
    exact writesIn_snoc hs (map_range_getBang_or_empty 8 _ (fun k => h2 _ _) i)
  · intro i s s' _ hd
    injection hd

/-! ## 4. The write set of the emitted multiply brick -/

/-- The names one emitted `mul` brick binds: the private `op{idx}` namespace,
    which every internal name of the builders extends, the empty name an
    out-of-range builder index reads, and the eight half-limb slots of the output
    field element. -/
def MulWrites (o : String) (x : String) : Prop :=
  HeadIs 'o' x ∨ x = "" ∨ ∃ k, k < 8 ∧ x = s!"{o}h{k}"

theorem suffixClosed_headIs (c : Char) : SuffixClosed (HeadIs c) :=
  fun _ u h => h.append u

theorem headIs_op (idx : Nat) : HeadIs 'o' s!"op{idx}" :=
  HeadIs.append (⟨['p'], rfl⟩ : HeadIs 'o' "op") _

/-- **The emitted `mul` brick binds only `op{idx}`-namespace names and the output
    field element's half-limb slots.** -/
theorem emitFOp_mul_writes (idx : Nat) (o a b : String) :
    WritesIn (MulWrites o) (emitFOp idx (FOp.mul o a b)) := by
  refine writesIn_append
    (writesIn_mono (fun x hx => hx.imp id Or.inl)
      (feMulHalves_writes (suffixClosed_headIs 'o') s!"op{idx}" (feH a) (feH b)
        (headIs_op idx)))
    (writesIn_map_range 8 _ _ (fun k hk => Or.inr (Or.inr ⟨k, hk, rfl⟩)))

/-! ## 5. The frame half of the per-brick step at the multiply -/

/-- A schedule field element other than the brick's output is untouched by the
    brick's write set. -/
theorem not_mulWrites_hName {o fe : String} (hfe : schedNameB fe = true) (hne : fe ≠ o)
    (k : Nat) (hk : k < 8) : ¬ MulWrites o s!"{fe}h{k}" := by
  obtain ⟨c, hc, hup⟩ := headIs_of_schedNameB hfe
  obtain ⟨t, ht⟩ := headIs_hName hc k
  rintro (hO | hE | ⟨k', hk', hEq⟩)
  · obtain ⟨t', ht'⟩ := hO
    rw [ht] at ht'
    injection ht' with hcc
    rw [hcc] at hup
    exact absurd hup (by decide)
  · rw [hE] at ht
    exact absurd ht (by simp)
  · exact hne (hName_inj fe o k k' hk hk' hEq)

/-- **A schedule field element other than the brick's output keeps its half-limb
    residue readout across the emitted `mul` brick.** -/
theorem feVal_frame_mul (idx : Nat) (o a b fe : String) (env env' : SEnvScalar)
    (hsem : semScalar (seqAll (emitFOp idx (FOp.mul o a b))) env = some env')
    (hfe : schedNameB fe = true) (hne : fe ≠ o) : feVal env' fe = feVal env fe := by
  obtain ⟨c, hc, hup⟩ := headIs_of_schedNameB hfe
  simp only [feVal]
  congr 1
  refine List.map_congr_left (fun k hk => ?_)
  have hk8 : k < 8 := List.mem_range.mp hk
  rw [envReader_seqAll_frame (MulWrites o) _ (emitFOp_mul_writes idx o a b) env env' hsem
    s!"{fe}h{k}" ((headIs_hName hc k).headOk (by rintro rfl; exact absurd hup (by decide))).notTmp
    (not_mulWrites_hName hfe hne k hk8)]

/-! ## 6. The entry conditions and the residual value obligation

The multiply brick's operand-scanning schedule is carry-free only while every
half-limb is below `2 ^ 32`, and its single conditional subtract of `p`
canonicalises only from a bounded fold result, which needs both operands to be
canonical residues. It also reads the reduction constants `ZZ` / `CC0` / `CC1`
and the eight limbs `PL0 .. PL7` of `p` from the environment the enclosing body's
`constInit` bound. -/

/-- The entry conditions the emitted `mul` brick's arithmetic is written for. -/
structure MulEntry (env : SEnvScalar) (a b : String) : Prop where
  /-- The zero slot the accumulators start from holds `0`. -/
  zero : (envReader env "ZZ").toNat = 0
  /-- The low limb of the Solinas constant holds `977`. -/
  constLo : (envReader env "CC0").toNat = cc0
  /-- The high limb of the Solinas constant holds `1`. -/
  constHi : (envReader env "CC1").toNat = cc1
  /-- The eight modulus slots hold the 32-bit limbs of `p`. -/
  modulus : ∀ i, i < 8 → (envReader env s!"PL{i}").toNat = pl32.getD i 0
  /-- The first operand is held in proper 32-bit half-limbs. -/
  limbA : ∀ k, k < 8 → (envReader env s!"{a}h{k}").toNat < 2 ^ 32
  /-- The second operand is held in proper 32-bit half-limbs. -/
  limbB : ∀ k, k < 8 → (envReader env s!"{b}h{k}").toNat < 2 ^ 32
  /-- The first operand is a canonical residue. -/
  ltA : feVal env a < pNat
  /-- The second operand is a canonical residue. -/
  ltB : feVal env b < pNat

/-- The value half of the per-brick step at the `mul` arm, at schedule names and
    over the entry conditions: the output field element ends holding the field
    product of the operands' half-limb residue readout. The three `schedNameB`
    hypotheses separate a schedule field element from the brick's own temporaries,
    whose names the emitter reserves under the `op{idx}` and `_` prefixes. -/
def MulBrickValue : Prop :=
  ∀ (idx : Nat) (o a b : String) (env env' : SEnvScalar),
    schedNameB o = true → schedNameB a = true → schedNameB b = true →
    MulEntry env a b →
    semScalar (seqAll (emitFOp idx (FOp.mul o a b))) env = some env' →
    feVal env' o = fm (feVal env a) (feVal env b)

/-- **The `mul` arm of the per-brick step, from the value obligation and the
    frame.** At the output field element the value obligation applies; at every
    other schedule field element both sides are the entry readout. -/
theorem brickStepMul_of_value (hV : MulBrickValue) (idx : Nat) (o a b : String)
    (ho : schedNameB o = true) (ha : schedNameB a = true) (hb : schedNameB b = true)
    (env env' : SEnvScalar) (hE : MulEntry env a b)
    (hsem : semScalar (seqAll (emitFOp idx (FOp.mul o a b))) env = some env') :
    ∀ fe, schedNameB fe = true →
      feVal env' fe = stepFOpG fm fa fs (feVal env) (FOp.mul o a b) fe := by
  intro fe hfe
  by_cases h : fe = o
  · subst h
    rw [hV idx fe a b env env' hfe ha hb hE hsem]
    simp [stepFOpG, envUpd]
  · rw [feVal_frame_mul idx o a b fe env env' hsem hfe h]
    simp [stepFOpG, envUpd, h]

end CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulBrickFrame
