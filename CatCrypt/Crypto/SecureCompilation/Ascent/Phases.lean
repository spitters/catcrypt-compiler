/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import CatCrypt.Hax.Ascent.Refines

/-!
# The ascent calculus as composable AutoCorres phases

The live `Ascent.Corres` step (`Corres SRword P fa c`) abstracts a LowCT command in
**one** monolithic move: from the concrete `semScalar` operational semantics straight
to a clean `ZMod 2^64` pure-function spec. AutoCorres (which `Corres` ports) instead
abstracts in *ordered, separately-proven phases* — L1 (imperative→nondet monad),
L2 (locals→λ-bound), HL (byte-heap→typed split-heap), **WA** (machine word→ring, with
overflow guards, ARITHMETIC only), **TS** (nondet→weakest pure/option monad). Each
phase is a `corres` and they compose transitively.

The AutoCorres-to-Lean port ("AutoCorres2 in Lean") was begun by **Sebastian Graf**
(`sgraf812/ascent`); this phase framing follows that lineage.

This module exhibits that the monolithic `Corres SRword`
factors as the two crypto-relevant AutoCorres phases:

* **TS (type-strengthen).** The refinement of a LowCT command to a *pure total word
  transformer* `fw : AWord → AWord` over the total word relation `SRW`. This is
  `Corres SRW` — the abstract side is a `gets`/`State`-monad pure function (not a
  set-valued nondet map) and progress is deterministic (`semScalar c = some _`). The
  values are still machine words `BitVec 64`; no ring abstraction has happened yet.

* **WA (word abstraction).** The unconditional value-representation change
  `wEnc : BitVec 64 → ZMod 2^64`, lifting a word-level `Corres SRW` to the field-level
  `Corres SRword`. This is `corres_WA` below. AutoCorres' discipline: **WA applies to
  ARITHMETIC only** — the encoding must be a homomorphism for the op. `+`/`-`/`*` have
  registered `RelatedBinOp wEnc` squares (`ringWA`); the bitwise ops `^^^`/`&&&`/`<<<`
  /`>>>` do **not**, so they stay at the word level (the identity phase `wordWA`).

The factoring is exhibited concretely: the live leaf `corres_setScalar` is
**re-derived** here as `corres_WA` applied to a word-level literal set
(`corres_setScalar_via_phases`), and horizontal composition (`corres_seq`) commutes
through the WA lift (`corres_two_sets_via_phases`).

The WA/bitwise distinction becomes a first-class **phase choice** (`ringWA` vs
`wordWA`), not an ad-hoc per-leaf decision: `ringWA` is valid exactly for the three
ring ops, `wordWA` (= identity on `BitVec 64`, AutoCorres' `IdWA`) is valid for every
op and is where the bitwise spec lives.

The field relation is recovered from the word relation with `Classical.choice`, used
once to extract a word witness from the existential field relation.

## TS as the choice of a result monad

The last section re-exports the result-monad side of TS from hax-lean's
`CatCrypt/Hax/Ascent/Refines.lean` (namespace `Hax.Ascent`), generic in the concrete and
abstract state types, and states `corres_iff_refinesP`. An abstract program is `AbsProg ε A B`: a pure function
`A → B`, an `Option`-valued one (`none` is guard failure), or an exception program
`A → Option (Except ε B)` (a thrown value is an early exit). `MonadLevel` orders the
three as `pure ≤ option ≤ except`. `RefinesP` is the forward simulation of a pure
function under a precondition and `RefinesO` that of an `Option`-valued one; the
exception level is `RefinesO` at `Except ε B`. `AbsProg.Refines` reads each level
over one output relation on `Except ε B`, and the lifting lemmas
`refinesP_iff_refinesO_guard`, `refinesO_iff_refinesO_mapOk` and
`AbsProg.refines_iff_toExcept` state that a program strengthened to a lower level
has the same correspondence as its image one level up. The pass that picks the
level for a kernel is `Ascent/Strengthen.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## The WA phase type and its two instances (`ringWA` / `wordWA`)

A WA phase is a pointwise value encoding `W → F` from the machine-word type `W` to the
abstract ring/field `F`. AutoCorres' word-abstraction phase is exactly this, and its
central discipline is that it may only be *applied* where the encoding is a homomorphism
for the operation in question — captured by `WAPhase.valid`. -/

/-- A word-abstraction phase: a pointwise encoding of the machine word `W` into the
    abstract value domain `F`. -/
structure WAPhase (W F : Type) where
  /-- The pointwise value encoding (word → ring/field element). -/
  wenc : W → F

/-- The phase `p` is *valid* for the concrete op `op` (abstracted to `bop`) when its
    encoding is a homomorphism for it — the commuting square AutoCorres needs before it
    may abstract that op. WA may only be applied to ops for which this holds. -/
@[reducible] def WAPhase.valid {W F : Type} (p : WAPhase W F)
    (op : W → W → W) (bop : F → F → F) : Prop :=
  ∀ x y, p.wenc (op x y) = bop (p.wenc x) (p.wenc y)

/-- The **arithmetic** WA phase: the word→ring encoding `wEnc : BitVec 64 → ZMod 2^64`.
    Valid for `+`/`-`/`*` (the registered `RelatedBinOp wEnc` squares), and only those. -/
def ringWA : WAPhase (BitVec 64) (ZMod (2 ^ 64)) := ⟨wEnc⟩

/-- The **identity / bitwise** WA phase (AutoCorres' `IdWA`): the abstraction is the
    identity on `BitVec 64`, so the clean spec stays in the word algebra. This is where
    the bitwise ops `^^^`/`&&&`/`<<<`/`>>>` live — they are not `ZMod`-ring ops, so they
    cannot ride `ringWA` and instead keep their spec at the word level. -/
def wordWA : WAPhase (BitVec 64) (BitVec 64) := ⟨id⟩

/-! ### `ringWA` is valid for exactly the ring ops -/

/-- `ringWA` abstracts word addition to `ZMod` addition — the `wEncAdd` square. -/
theorem ringWA_valid_add : ringWA.valid (· + ·) (· + ·) := fun x y => wEncAdd.comm x y

/-- `ringWA` abstracts word subtraction to `ZMod` subtraction — the `wEncSub` square. -/
theorem ringWA_valid_sub : ringWA.valid (· - ·) (· - ·) := fun x y => wEncSub.comm x y

/-- `ringWA` abstracts word multiplication to `ZMod` multiplication — the `wEncMul`
    square. -/
theorem ringWA_valid_mul : ringWA.valid (· * ·) (· * ·) := fun x y => wEncMul.comm x y

/-- **The discipline, made non-vacuous.** `ringWA` is *not* a homomorphism for the
    bitwise `^^^`: no `ZMod` addition target works, witnessed at `1 ^^^ 1 = 0` versus
    `wEnc 1 + wEnc 1 = 2 ≠ 0`. So a bitwise op cannot be abstracted by the
    arithmetic phase — the phase framework *forces* the `wordWA` choice below, rather
    than leaving it to an ad-hoc per-leaf convention. -/
theorem ringWA_not_valid_xor : ¬ ringWA.valid (· ^^^ ·) (· + ·) := by
  intro h
  have hkey : wEnc (BitVec.ofNat 64 1 ^^^ BitVec.ofNat 64 1)
      = wEnc (BitVec.ofNat 64 1) + wEnc (BitVec.ofNat 64 1) :=
    h (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
  have hx : BitVec.ofNat 64 1 ^^^ BitVec.ofNat 64 1 = 0 := by bv_decide
  rw [hx] at hkey
  have e0 : wEnc (0 : BitVec 64) = (0 : ZMod (2 ^ 64)) := by simp [wEnc]
  have e1 : wEnc (BitVec.ofNat 64 1) = (1 : ZMod (2 ^ 64)) := by
    simp [wEnc, BitVec.toNat_ofNat]
  rw [e0, e1, one_add_one_eq_two] at hkey
  -- hkey : (0 : ZMod (2^64)) = 2
  have h2 : (2 : ZMod (2 ^ 64)) ≠ 0 := by
    intro hc
    have hnat : ((2 : ℕ) : ZMod (2 ^ 64)) = 0 := by exact_mod_cast hc
    rw [CharP.cast_eq_zero_iff (ZMod (2 ^ 64)) (2 ^ 64)] at hnat
    exact absurd (Nat.le_of_dvd (by norm_num) hnat) (by norm_num)
  exact h2 hkey.symm

/-! ### `wordWA` (`IdWA`) is valid for every op — in particular all bitwise ops

The identity encoding is trivially a homomorphism for any operation, so `wordWA` may
abstract `^^^`/`&&&`/`<<<`/`>>>` — but the "abstraction" is the identity, so the clean
spec IS the word computation, exactly the batch-C "bitwise keeps its spec in `BitVec`"
behaviour, now a phase choice. -/

/-- `wordWA` is valid for *every* binary word op (the identity is a homomorphism for
    all of them). In particular for the bitwise ops with no `ZMod`-ring square. -/
theorem wordWA_valid (op : BitVec 64 → BitVec 64 → BitVec 64) : wordWA.valid op op :=
  fun _ _ => rfl

/-- A `wordWA` "abstraction" is the identity on states: the spec never leaves the word
    algebra. This is why the bitwise leaf (`corres_setExprBitwise`) needs no WA lift. -/
theorem wordWA_wenc_id (w : BitVec 64) : wordWA.wenc w = w := rfl

/-! ## The two phase layers as `Corres` relations

* `SRW` — the *total* word relation: every name holds a `.sword 64` whose word is the
  abstract `BitVec 64` value *directly* (identity value abstraction). `Corres SRW P fw c`
  is the post-TS word-level refinement — a pure total word transformer `fw`.
* `SRword` (from `Ascent.Corres`) — the field relation: the abstract value is the
  `wEnc`-encoding of the held word. The image of `SRW` under the WA phase. -/

/-- Word-level abstract state: a total valuation of names by machine words. -/
abbrev AWord := String → BitVec 64

/-- Field-level abstract state: a total valuation of names by `ZMod 2^64` elements. -/
abbrev AField := String → ZMod (2 ^ 64)

/-- The **total** word-phase state relation (the TS-phase relation): every name holds a
    `.sword 64` whose word is the abstract value directly (identity encoding). This is
    the waist of the TS phase — values are still machine words. -/
def SRW (env : SEnvScalar) (φ : AWord) : Prop :=
  ∀ x, env x = some ⟨.sword 64, φ x⟩

/-- The WA phase acting on states: post-compose each word value with the `ringWA`
    encoding `wEnc`, turning a word valuation into a field valuation. -/
def waLift (φ : AWord) : AField := fun x => wEnc (φ x)

/-! ### The phase-boundary lemmas relating `SRW` and `SRword` through `waLift` -/

/-- **WA lifts the relation forward.** A word-related env is field-related to the
    `waLift`-image: `SRW env φ → SRword env (waLift φ)`. This is the phase boundary —
    the total word relation composed with the WA encoding is the field relation. -/
theorem SRW_to_SRword {env : SEnvScalar} {φ : AWord}
    (h : SRW env φ) : SRword env (waLift φ) :=
  fun x => ⟨φ x, h x, rfl⟩

/-- **The field relation is the WA-image of the word relation.** Every field-related
    env arises as `waLift` of a word-related one; the word witness is extracted from the
    existential field relation (this is the single use of `Classical.choice`). Together
    with `SRW_to_SRword` this says `SRword = waLift ∘ SRW`: `WA` is exactly the phase
    that turns the word relation into the field relation. -/
theorem SRword_to_exists_word {env : SEnvScalar} {a : AField}
    (h : SRword env a) : ∃ φ : AWord, SRW env φ ∧ waLift φ = a := by
  refine ⟨fun x => (h x).choose, fun x => (h x).choose_spec.1, ?_⟩
  funext x
  exact (h x).choose_spec.2

/-! ## The WA composition lemma: `Corres SRword = corres_WA ∘ Corres SRW`

This is the crux: any TS-phase word refinement `Corres SRW Pw fw c` lifts, through the
WA encoding, to a field refinement `Corres SRword Pf fa c`, provided the abstract word
transformer `fw` and the abstract field transformer `fa` form a **naturality square**
for `waLift` (`waLift ∘ fw = fa ∘ waLift`) — WA commutes with the state update. This is
the phase-composition theorem `TS`-then-`WA`. -/

/-- **WA ∘ TS composition.** From a word-level (TS) refinement `hw : Corres SRW Pw fw c`,
    the WA naturality square `hcomm : waLift (fw φ) = fa (waLift φ)`, and a precondition
    pullback `hpre`, obtain the field-level refinement `Corres SRword Pf fa c`. The proof
    runs the word refinement on the word witness extracted from the field relation, then
    pushes the result forward through `SRW_to_SRword`; `hcomm` identifies the two
    abstract results. -/
theorem corres_WA {Pw : AWord → Prop} {fw : AWord → AWord} {c : LowCT}
    (hw : Corres SRW Pw fw c)
    {Pf : AField → Prop} {fa : AField → AField}
    (hcomm : ∀ φ, waLift (fw φ) = fa (waLift φ))
    (hpre : ∀ φ, Pf (waLift φ) → Pw φ) :
    Corres SRword Pf fa c := by
  intro env a hSR hP
  obtain ⟨φ, hSRW, rfl⟩ := SRword_to_exists_word hSR
  obtain ⟨env', hstep, hSRW'⟩ := hw env φ hSRW (hpre φ hP)
  refine ⟨env', hstep, ?_⟩
  rw [← hcomm φ]
  exact SRW_to_SRword hSRW'

/-! ## The TS-phase leaf: a word-level literal set (`Corres SRW`)

The word-level (post-TS, pre-WA) counterpart of the live `corres_setScalar`: the same
`RScalarSet` command, refined to a pure *word* transformer over the total word relation
`SRW`. This is the TS phase at the word level — machine words, deterministic pure update. -/

/-- `RScalarSet name n` at the **word level** (TS phase): the pure word transformer sets
    `name` to `BitVec.ofNat 64 n`, discharged against the real `semScalar` `RScalarSet`
    arm over the total word relation `SRW`. -/
theorem corres_setScalarW (name : String) (n : Nat) :
    Corres SRW (fun _ => True)
      (fun φ s => if s = name then BitVec.ofNat 64 n else φ s)
      (.RScalarSet name n) := by
  intro env φ _ _
  refine ⟨env.upd name (t := .sword 64) (BitVec.ofNat 64 n), rfl, ?_⟩
  intro x
  by_cases hx : x = name
  · subst hx; simp [SEnvScalar.upd]
  · simp only [SEnvScalar.upd, if_neg hx]
    exact (‹SRW env φ›) x

/-! ## Worked example 1: the live `corres_setScalar` re-derived as `WA ∘ TS`

The monolithic field-level leaf is recovered *purely by phase composition*: run the
word-level set `corres_setScalarW` (TS phase), then lift it through `corres_WA` (WA
phase). The naturality square is the literal-value fact `wEnc (ofNat 64 n) = (n : ZMod)`
on the updated slot and reflexivity elsewhere. The resulting statement is **identical**
to `Ascent.corres_setScalar`. -/

/-- The live `corres_setScalar` leaf, re-derived as the WA lift of the word-level TS
    leaf. Same statement as `Ascent.corres_setScalar`, obtained by phase composition. -/
theorem corres_setScalar_via_phases (name : String) (n : Nat) :
    Corres SRword (fun _ => True)
      (fun a s => if s = name then (n : ZMod (2 ^ 64)) else a s)
      (.RScalarSet name n) := by
  refine corres_WA (corres_setScalarW name n) ?_ (fun _ _ => trivial)
  intro φ
  funext s
  simp only [waLift]
  by_cases hs : s = name
  · subst hs; simp [wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]
  · simp [hs]

/-- Sanity: the phase-composed leaf has exactly the type of the live monolithic leaf. -/
example (name : String) (n : Nat) :
    Corres SRword (fun _ => True)
      (fun a s => if s = name then (n : ZMod (2 ^ 64)) else a s)
      (.RScalarSet name n) :=
  corres_setScalar_via_phases name n

/-! ## Worked example 2: horizontal composition commutes through the WA lift

Two word-level sets sequenced with `corres_seq` (structural / L2 composition), then
WA-lifted as a whole — showing the phase framework composes both horizontally
(`corres_seq` at the word level) and vertically (`corres_WA`). -/

/-- Two sequenced literal sets, refined at the field level by first composing at the word
    level (`corres_seq`) and then applying the WA lift once. -/
theorem corres_two_sets_via_phases (n m : Nat) :
    Corres SRword (fun _ => True)
      (fun a s => if s = "y" then (m : ZMod (2 ^ 64))
                  else if s = "x" then (n : ZMod (2 ^ 64)) else a s)
      (.RSeq (.RScalarSet "x" n) (.RScalarSet "y" m)) := by
  have hseq :
      Corres SRW (fun _ => True)
        (fun φ => (fun ψ s => if s = "y" then BitVec.ofNat 64 m else ψ s)
                  ((fun ψ s => if s = "x" then BitVec.ofNat 64 n else ψ s) φ))
        (.RSeq (.RScalarSet "x" n) (.RScalarSet "y" m)) :=
    corres_seq (SR := SRW) (corres_setScalarW "x" n) (corres_setScalarW "y" m)
      (fun _ _ => trivial)
  refine corres_WA hseq ?_ (fun _ _ => trivial)
  intro φ
  funext s
  simp only [waLift]
  by_cases hy : s = "y"
  · subst hy; simp [wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]
  · by_cases hx : s = "x"
    · subst hx; simp [hy, wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]
    · simp [hy, hx]

/-! ## The bitwise fragment sits at `wordWA` (`IdWA`) — no WA lift

The `ExprLeaf` module already provides the two concrete value leaves that this phase
split explains:

* the **arithmetic** leaf `corres_setExpr` targets `String → ZMod 2^64` — the `ringWA`
  target: its value transfer is `wEnc_evalBV_evalZMod`, built from the `ringWA`-valid
  squares (`wEncAdd`/`wEncSub`/`wEncMul`), i.e. it is exactly a `ringWA`-phase leaf;
* the **bitwise** leaf `corres_setExprBitwise` targets `String → BitVec 64` — the
  `wordWA`/`IdWA` target: its clean spec never leaves the word algebra (its value step
  is a reader-agreement congruence, *not* a ring square), because no `ringWA` square
  exists for `^^^`/`&&&`/`<<<`/`>>>` (`ringWA_not_valid_xor`).

So the `ExprLeaf` arith/bitwise split is precisely the `ringWA`-vs-`wordWA` **phase
choice** made first-class here: `wordWA_valid` says the identity phase covers every
bitwise op, and `wordWA_wenc_id` says a `wordWA` lift is the identity on states, so the
bitwise leaf needs no WA step — its spec *is* the word computation. (Those leaves live
in `ExprLeaf`, imported by consumers of both modules; this module states the phase
algebra they instantiate without importing that module.) -/

/-! ## TS: the result monad of an abstract program

The three result monads, the refinement relations at each level and the lifting lemmas
are the parametric layer `Hax.Ascent` of hax-lean (`CatCrypt/Hax/Ascent/Refines.lean`),
re-exported here under their names in this namespace. -/

export _root_.Hax.Ascent (MonadLevel MonadLevel.pure MonadLevel.option MonadLevel.except
  MonadLevel.rank RefinesP RefinesO optGuard refinesP_iff_refinesO_guard
  refinesP_true_iff_refinesO_some refinesO_iff_refinesO_mapOk exceptOk
  exceptOk_mapOk_of_noThrow refinesO_except_iff_exceptOk refinesO_iff_refinesP_of_total
  AbsProg AbsProg.pure AbsProg.option AbsProg.except AbsProg.level AbsProg.toExcept
  AbsProg.lift AbsProg.Refines AbsProg.refines_lift_iff AbsProg.refines_iff_toExcept
  liftOk refinesO_exceptOk)

section Strengthen

/-- `Corres` is `RefinesP` at the concrete semantics `semScalar c`. -/
theorem corres_iff_refinesP {AState : Type} (SR : SEnvScalar → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : LowCT) :
    Corres SR P fa c ↔ RefinesP (fun env => semScalar c env) SR SR P fa := Iff.rfl

end Strengthen

end CatCrypt.Crypto.SecureCompilation.Ascent
