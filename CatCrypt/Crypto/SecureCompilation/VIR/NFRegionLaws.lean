/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFRegionSig
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel

/-!
# Laws of the control operations of structured programs

The relational congruence, the fuel monotonicity and the leak events of the region
constructors of `NFProg` are laws of the operation denotation `RegionDenote.denote`
on region values. Each law is one definition over a control signature; it is proved
for `RegionSig.scf`, for `RegionSig.func` and for sums, and one theorem per law for
`NFProg.region` follows by `NFProg.denote_region`.

A relation of values is a family `R : ValRel d` of relations between two valuations
of one list of types. The two sides of a law run one operation at two denotations of
the signature, so that a call may consult two call environments, on related
arguments and related region values.

* `RegionDenote.Rel` relates the two results by `Option.Rel` at one fuel.
* `RegionDenote.Fwd` relates a successful left run at the fuel `n` to a successful
  right run at a fuel `m ≥ n`.
* `RegionDenote.Mono` is the fuel monotonicity of an operation on a family of region
  values indexed by the fuel; it is `RegionDenote.Fwd` at the equality family.

Structured control flow satisfies the first two laws at every family compatible with
the trip count, the trip index and the bits (`ScfCompat`). A call satisfies them when
the two environments send related arguments to related results (`CallRel`).

The leak events of an operation are a class `RegionLeak`: the events an operation
emits from its arguments (`RegionLeak.events`), and its run on the leak runs of its
regions (`RegionLeak.run`). `NFProg.leakRun_region` states `NFProg.leakRun` at
`NFProg.region` as the events of the operation, then those of its run, then those of
the continuation.

## Main definitions

* `ValRel`, `ValRel.eq`, `SegsRel`, `RegionValsRel` — families of relations of
  valuations, and their lifting to bound segments and to region values.
* `OptLift`, `OptLift.rel`, `OptLift.fwd` — the two liftings of a relation to `Option`.
* `RegionDenote.Respects`, `RegionDenote.Rel`, `RegionDenote.Fwd`, `RegionDenote.Mono`
  — the laws.
* `ScfCompat`, `CallRel` — the hypotheses of the laws at `scf` and at `func`.
* `RegionDenote.sumOf`, `RegionDenote.funcOf`, `RegionDenote.ofEnv`,
  `NFProg.denoteRegionsAt` — the operation denotation and the region values at an
  explicit call environment.
* `RegionLeakVal`, `RegionLeak`, `NFProg.leakRegions` — the leak run of a region, the
  leak events of the operations, and the leak runs of the regions of an operation.

## Main results

* `RegionDenote.scf_rel`, `RegionDenote.scf_fwd`, `RegionDenote.func_respects`,
  `RegionDenote.respects_sum_inl`, `RegionDenote.respects_sum_inr`,
  `RegionDenote.ofEnv_rel`, `RegionDenote.ofEnv_fwd` — the laws at the signatures.
* `RegionDenote.Fwd.mono` — the forward law at the equality family is fuel
  monotonicity.
* `NFProg.denoteAt_region` — the denotation of `region` at an explicit environment.
* `NFProg.denoteAt_region_rel`, `NFProg.denoteAt_region_fwd`,
  `NFProg.denoteAt_region_mono` — the congruence and the monotonicity of `region`.
* `NFProg.denoteAt_fuel_mono` — a run at a fuel is a run at every larger fuel, by
  `NFProg.regionRec`.
* `NFProg.leakRun_region` — the leak run of `region`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-! ## 1. Relations of valuations and of region values -/

section Relations

variable {d : Dialect.{0, 0}} [TyDenote d.Ty]

/-- A family of relations between two valuations of one list of types. -/
abbrev ValRel (d : Dialect.{0, 0}) [TyDenote d.Ty] : Type :=
  (ts : List d.Ty) → Valuation (d := d) ts → Valuation (d := d) ts → Prop

/-- The family of equalities. -/
abbrev ValRel.eq : ValRel d := fun _ a a' => a = a'

/-- The bound segments of a region are related segment by segment. -/
def SegsRel (R : ValRel d) : {bs : List (List d.Ty)} →
    HVector (fun b : List d.Ty => Valuation (d := d) b) bs →
    HVector (fun b : List d.Ty => Valuation (d := d) b) bs → Prop
  | [], .nil, .nil => True
  | _ :: _, .cons b B, .cons b' B' => R _ b b' ∧ SegsRel R B B'

/-- The empty lists of segments are related. -/
theorem SegsRel.nil {R : ValRel d} : SegsRel R .nil .nil := trivial

/-- Related segments in front of related lists of segments are related. -/
theorem SegsRel.cons {R : ValRel d} {b : List d.Ty} {bs : List (List d.Ty)}
    {x x' : Valuation (d := d) b}
    {B B' : HVector (fun b : List d.Ty => Valuation (d := d) b) bs} (h : R b x x')
    (hB : SegsRel R B B') : SegsRel R (.cons x B) (.cons x' B') := ⟨h, hB⟩

/-- Segments related at the equality family are equal. -/
theorem segsRel_eq : {bs : List (List d.Ty)} →
    {B B' : HVector (fun b : List d.Ty => Valuation (d := d) b) bs} →
    SegsRel ValRel.eq B B' → B = B'
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, h => by
      obtain ⟨h₁, h₂⟩ := h
      cases h₁
      rw [segsRel_eq h₂]

/-- A lifting of a relation on a type to a relation on its `Option`. -/
abbrev OptLift : Type 1 := (α : Type) → (α → α → Prop) → Option α → Option α → Prop

/-- The bisimulation lifting: both fail, or both succeed with related values. -/
abbrev OptLift.rel : OptLift := fun _ R => Option.Rel R

/-- The forward lifting: a successful left computation has a successful right
    computation with a related value. -/
abbrev OptLift.fwd : OptLift := fun _ R o o' => ∀ b, o = some b → ∃ b', o' = some b' ∧ R b b'

/-- Two lists of region values are related: each pair sends related bound segments to
    results related through the lifting `L`. -/
def RegionValsRel (L : OptLift) (R : ValRel d) : {rs : List (List (List d.Ty) × List d.Ty)} →
    HVector (RegionVal (d := d)) rs → HVector (RegionVal (d := d)) rs → Prop
  | [], .nil, .nil => True
  | r :: _, .cons v vs, .cons v' vs' =>
      (∀ B B', SegsRel R B B' → L _ (R r.2) (v B) (v' B')) ∧ RegionValsRel L R vs vs'

/-- `Option.Rel` is monotone in the relation. -/
theorem optionRel_imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b)
    {o : Option α} {o' : Option β} (ho : Option.Rel R o o') : Option.Rel S o o' := by
  cases ho with
  | none => exact .none
  | some hr => exact .some (h _ _ hr)

end Relations

/-! ## 2. The laws -/

section Laws

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] {S : RegionSig d.Ty}

/-- **The relational law of an operation.** At fuels related by `F`, the denotations
    `D` and `D'` of the operation `o` send `R`-related arguments and `R`-related region
    values to results related through the lifting `L`. -/
def RegionDenote.Respects (L : OptLift) (F : Nat → Nat → Prop) (D D' : RegionDenote d S)
    (R : ValRel d) (o : S.Op) : Prop :=
  ∀ fuel fuel', F fuel fuel' → ∀ a a', R _ a a' → ∀ rv rv', RegionValsRel L R rv rv' →
    L _ (R _) (D.denote o fuel a rv) (D'.denote o fuel' a' rv')

/-- **Relational congruence of an operation**, bisimulation form at one fuel. -/
abbrev RegionDenote.Rel (D D' : RegionDenote d S) (R : ValRel d) (o : S.Op) : Prop :=
  RegionDenote.Respects OptLift.rel Eq D D' R o

/-- **Relational congruence of an operation**, forward form from a fuel to a larger
    one. -/
abbrev RegionDenote.Fwd (D D' : RegionDenote d S) (R : ValRel d) (o : S.Op) : Prop :=
  RegionDenote.Respects OptLift.fwd (· ≤ ·) D D' R o

/-- **Fuel monotonicity of an operation.** On a family of region values indexed by the
    fuel in which a result at a fuel persists at every larger fuel, a result of the
    operation at a fuel persists at every larger fuel. -/
def RegionDenote.Mono (D : RegionDenote d S) (o : S.Op) : Prop :=
  ∀ rv : Nat → HVector (RegionVal (d := d)) (S.regs o),
    (∀ n m, n ≤ m → RegionValsRel OptLift.fwd ValRel.eq (rv n) (rv m)) →
    ∀ n m, n ≤ m → ∀ a out, D.denote o n a (rv n) = some out → D.denote o m a (rv m) = some out

/-- The forward law at the equality family is fuel monotonicity. -/
theorem RegionDenote.Fwd.mono {D : RegionDenote d S} {o : S.Op}
    (h : RegionDenote.Fwd D D ValRel.eq o) : RegionDenote.Mono D o := by
  intro rv hrv n m hnm a out hout
  obtain ⟨out', h', he⟩ := h n m hnm a a rfl (rv n) (rv m) (hrv n m hnm) out hout
  cases he
  exact h'

/-- The denotation of a sum of signatures from denotations of the summands. -/
abbrev RegionDenote.sumOf {S₁ S₂ : RegionSig d.Ty} (D₁ : RegionDenote d S₁)
    (D₂ : RegionDenote d S₂) : RegionDenote d (S₁.sum S₂) :=
  letI := D₁
  letI := D₂
  inferInstance

/-- The law of a sum at an operation of the left summand is the law of that summand. -/
theorem RegionDenote.respects_sum_inl {S₁ S₂ : RegionSig d.Ty} {L : OptLift}
    {F : Nat → Nat → Prop} {D₁ D₁' : RegionDenote d S₁} (D₂ D₂' : RegionDenote d S₂)
    {R : ValRel d} {o : S₁.Op} (h : RegionDenote.Respects L F D₁ D₁' R o) :
    RegionDenote.Respects L F (RegionDenote.sumOf D₁ D₂) (RegionDenote.sumOf D₁' D₂') R
      (.inl o) := h

/-- The law of a sum at an operation of the right summand is the law of that summand. -/
theorem RegionDenote.respects_sum_inr {S₁ S₂ : RegionSig d.Ty} {L : OptLift}
    {F : Nat → Nat → Prop} (D₁ D₁' : RegionDenote d S₁) {D₂ D₂' : RegionDenote d S₂}
    {R : ValRel d} {o : S₂.Op} (h : RegionDenote.Respects L F D₂ D₂' R o) :
    RegionDenote.Respects L F (RegionDenote.sumOf D₁ D₂) (RegionDenote.sumOf D₁' D₂') R
      (.inr o) := h

end Laws

/-! ## 3. The laws of structured control flow -/

section Scf

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- A family of relations is compatible with structured control flow: related tuples
    headed by a word read as the same trip count and have related tails, a trip index
    is related to itself, and related tuples headed by a bit read as the same `Bool`
    and have related tails. -/
structure ScfCompat (R : ValRel d) : Prop where
  /-- Related tuples headed by a word read as the same number. -/
  word_toNat : ∀ {cs : List d.Ty} {a a' : Valuation (d := d) (HasWord64.word (d := d) :: cs)},
    R _ a a' → HasWord64.toNat (d := d) a.head = HasWord64.toNat (d := d) a'.head
  /-- Related tuples headed by a word have related tails. -/
  word_tail : ∀ {cs : List d.Ty} {a a' : Valuation (d := d) (HasWord64.word (d := d) :: cs)},
    R _ a a' → R cs a.tail a'.tail
  /-- A trip index is related to itself. -/
  index : ∀ i : Nat, R [HasWord64.word (d := d)] (.cons (HasWord64.ofNat (d := d) i) .nil)
    (.cons (HasWord64.ofNat (d := d) i) .nil)
  /-- Related tuples headed by a bit read as the same `Bool`. -/
  bit_toBool : ∀ {cs : List d.Ty} {a a' : Valuation (d := d) (HasBitType.bit (d := d) :: cs)},
    R _ a a' → HasBoolBit.toBool (d := d) a.head = HasBoolBit.toBool (d := d) a'.head
  /-- Related tuples headed by a bit have related tails. -/
  bit_tail : ∀ {cs : List d.Ty} {a a' : Valuation (d := d) (HasBitType.bit (d := d) :: cs)},
    R _ a a' → R cs a.tail a'.tail

omit [DialectSignature d] in
/-- The equality family is compatible with structured control flow. -/
theorem ScfCompat.eq : ScfCompat (ValRel.eq (d := d)) where
  word_toNat h := by cases h; rfl
  word_tail h := by cases h; rfl
  index _ := rfl
  bit_toBool h := by cases h; rfl
  bit_tail h := by cases h; rfl

omit [DialectSignature d] in
/-- **Structured control flow satisfies the congruence law**, bisimulation form, at
    every compatible family. -/
theorem RegionDenote.scf_rel {R : ValRel d} (hR : ScfCompat R)
    (o : RegionSig.ScfOp d.Ty) :
    RegionDenote.Rel (RegionDenote.scf (d := d)) RegionDenote.scf R o := by
  rintro fuel _ rfl a a' ha rv rv' hrv
  rcases o with cs | cs | rs
  · match rv, rv', hrv with
    | .cons body .nil, .cons body' .nil, hrv =>
      show Option.Rel (R cs)
        ((List.range (HasWord64.toNat (d := d) a.head)).foldlM
          (fun acc i => body (.cons acc (.cons (.cons (HasWord64.ofNat (d := d) i) .nil) .nil)))
          a.tail)
        ((List.range (HasWord64.toNat (d := d) a'.head)).foldlM
          (fun acc i => body' (.cons acc (.cons (.cons (HasWord64.ofNat (d := d) i) .nil) .nil)))
          a'.tail)
      rw [← hR.word_toNat ha]
      exact NFProg.foldlM_rel _
        (fun i _ acc acc' h => hrv.1 _ _ (.cons h (.cons (hR.index i) .nil))) _ _
        (hR.word_tail ha)
  · match rv, rv', hrv with
    | .cons body .nil, .cons body' .nil, hrv =>
      exact NFProg.whileIter_rel (fun acc acc' h => optionRel_imp
        (fun r r' hr => ⟨hR.bit_tail hr, hR.bit_toBool hr⟩) (hrv.1 _ _ (.cons h .nil))) fuel a a' ha
  · match rv, rv', hrv with
    | .cons thn (.cons els .nil), .cons thn' (.cons els' .nil), hrv =>
      exact NFProg.ite_rel (hR.bit_toBool ha) (hrv.1 .nil .nil trivial)
        (hrv.2.1 .nil .nil trivial)

omit [DialectSignature d] in
/-- **Structured control flow satisfies the congruence law**, forward form, at every
    compatible family. -/
theorem RegionDenote.scf_fwd {R : ValRel d} (hR : ScfCompat R)
    (o : RegionSig.ScfOp d.Ty) :
    RegionDenote.Fwd (RegionDenote.scf (d := d)) RegionDenote.scf R o := by
  intro fuel fuel' hle a a' ha rv rv' hrv
  rcases o with cs | cs | rs
  · match rv, rv', hrv with
    | .cons body .nil, .cons body' .nil, hrv =>
      show ∀ b, (List.range (HasWord64.toNat (d := d) a.head)).foldlM
          (fun acc i => body (.cons acc (.cons (.cons (HasWord64.ofNat (d := d) i) .nil) .nil)))
          a.tail = some b →
        ∃ b', (List.range (HasWord64.toNat (d := d) a'.head)).foldlM
          (fun acc i => body' (.cons acc (.cons (.cons (HasWord64.ofNat (d := d) i) .nil) .nil)))
          a'.tail = some b' ∧ R cs b b'
      rw [← hR.word_toNat ha]
      exact fun b => NFProg.foldlM_rel_fwd (R := R cs) _
        (fun i _ acc acc' b h => hrv.1 _ _ (.cons h (.cons (hR.index i) .nil)) b) _ _ b
        (hR.word_tail ha)
  · match rv, rv', hrv with
    | .cons body .nil, .cons body' .nil, hrv =>
      exact fun b => NFProg.whileIter_fwd_le (fun acc acc' r h hb => by
        obtain ⟨r', hr', hrr⟩ := hrv.1 _ _ (.cons h .nil) r hb
        exact ⟨r', hr', hR.bit_tail hrr, hR.bit_toBool hrr⟩) fuel fuel' hle a a' b ha
  · match rv, rv', hrv with
    | .cons thn (.cons els .nil), .cons thn' (.cons els' .nil), hrv =>
      exact NFProg.ite_rel_fwd (hR.bit_toBool ha) (hrv.1 .nil .nil trivial)
        (hrv.2.1 .nil .nil trivial)

end Scf

/-! ## 4. The laws of calls and of the signature of structured programs -/

section Func

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- The denotation of calls at the call environment `E`. -/
abbrev RegionDenote.funcOf (E : CallEnv d) : RegionDenote d (RegionSig.func (T := d.Ty)) :=
  letI : CallDenote d := ⟨E⟩
  inferInstance

/-- The denotation of the operations of structured programs at the call environment
    `E`. -/
abbrev RegionDenote.ofEnv (E : CallEnv d) : RegionDenote d (NFProg.regionSig d) :=
  RegionDenote.sumOf RegionDenote.scf (RegionDenote.funcOf E)

/-- The hypothesis of the laws at an operation of structured programs, on two call
    environments: none at structured control flow; at a call, the two callees of its
    symbol and signature send related arguments to results related through `L`. -/
def CallRel (L : OptLift) (E E' : CallEnv d) (R : ValRel d) : (NFProg.regionSig d).Op → Prop
  | .inl _ => True
  | .inr (.call f as rs) =>
      ∀ a a', R as a a' → L _ (R rs) (E.call f as rs a) (E'.call f as rs a')

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] in
/-- **A call satisfies the relational law** at two environments whose callees of its
    symbol and signature send related arguments to related results. -/
theorem RegionDenote.func_respects {L : OptLift} {F : Nat → Nat → Prop} (E E' : CallEnv d)
    {R : ValRel d} (f : String) (as rs : List d.Ty)
    (hcall : ∀ a a', R as a a' → L _ (R rs) (E.call f as rs a) (E'.call f as rs a')) :
    RegionDenote.Respects L F (RegionDenote.funcOf E) (RegionDenote.funcOf E') R
      (.call f as rs) :=
  fun _ _ _ a a' ha _ _ _ => hcall a a' ha

omit [DialectSignature d] in
/-- **The operations of structured programs satisfy the congruence law**, bisimulation
    form, at a compatible family and two environments related at the operation. -/
theorem RegionDenote.ofEnv_rel {E E' : CallEnv d} {R : ValRel d} (hR : ScfCompat R)
    (o : (NFProg.regionSig d).Op) (hc : CallRel OptLift.rel E E' R o) :
    RegionDenote.Rel (RegionDenote.ofEnv E) (RegionDenote.ofEnv E') R o := by
  rcases o with o | ⟨f, as, rs⟩
  · exact RegionDenote.respects_sum_inl _ _ (RegionDenote.scf_rel hR o)
  · exact RegionDenote.respects_sum_inr _ _ (RegionDenote.func_respects E E' f as rs hc)

omit [DialectSignature d] in
/-- **The operations of structured programs satisfy the congruence law**, forward
    form, at a compatible family and two environments related at the operation. -/
theorem RegionDenote.ofEnv_fwd {E E' : CallEnv d} {R : ValRel d} (hR : ScfCompat R)
    (o : (NFProg.regionSig d).Op) (hc : CallRel OptLift.fwd E E' R o) :
    RegionDenote.Fwd (RegionDenote.ofEnv E) (RegionDenote.ofEnv E') R o := by
  rcases o with o | ⟨f, as, rs⟩
  · exact RegionDenote.respects_sum_inl _ _ (RegionDenote.scf_fwd hR o)
  · exact RegionDenote.respects_sum_inr _ _ (RegionDenote.func_respects E E' f as rs hc)

omit [DialectSignature d] in
/-- **The operations of structured programs are monotone in the fuel.** -/
theorem RegionDenote.ofEnv_mono (E : CallEnv d) (o : (NFProg.regionSig d).Op) :
    RegionDenote.Mono (RegionDenote.ofEnv E) o :=
  RegionDenote.Fwd.mono (RegionDenote.ofEnv_fwd ScfCompat.eq o (by
    rcases o with o | ⟨f, as, rs⟩
    · trivial
    · rintro a _ rfl b hb
      exact ⟨b, hb, rfl⟩))

end Func

/-! ## 5. The laws of `NFProg.region` -/

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option]

/-- The denotations of the regions `regs` at the call environment `E`. -/
def denoteRegionsAt (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d} (V : Valuation Γ)
    {rs : List (List (List d.Ty) × List d.Ty)} (regs : Regions d Γ rs) :
    HVector (RegionVal (d := d)) rs :=
  letI : CallDenote d := ⟨E⟩
  denoteRegions fuel V regs

/-- The program of an operation denotes, at the call environment `E`, the operation
    denotation at `E` followed by its continuation. -/
theorem denoteAt_region (E : CallEnv d) {Γ : Ctxt d} {ts : List d.Ty}
    (o : (regionSig d).Op) (args : HVector (fun t => Var Γ t) ((regionSig d).args o))
    (regs : Regions d Γ ((regionSig d).regs o))
    (k : NFProg d ((regionSig d).outs o ++ Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (region o args regs k).denoteAt E fuel V =
      (RegionDenote.ofEnv E).denote o fuel (Expr.lookupArgs args V)
          (denoteRegionsAt E fuel V regs) >>= fun r =>
        k.denoteAt E fuel (hvAppend r V) := by
  let _ : CallDenote d := ⟨E⟩
  exact denote_region o args regs k fuel V

/-- **Relational congruence of `region`**, bisimulation form. Two programs of one
    operation satisfying the congruence law, over possibly different contexts and call
    environments, with related arguments, related region values and continuations that
    send related outputs to `S`-related results, denote `S`-related results. -/
theorem denoteAt_region_rel (E E' : CallEnv d) {R : ValRel d} {o : (regionSig d).Op}
    (hop : RegionDenote.Rel (RegionDenote.ofEnv E) (RegionDenote.ofEnv E') R o)
    {Γ Γ' : Ctxt d} {ts ts' : List d.Ty} {S : Valuation ts → Valuation ts' → Prop}
    (args : HVector (fun t => Var Γ t) ((regionSig d).args o))
    (regs : Regions d Γ ((regionSig d).regs o)) (k : NFProg d ((regionSig d).outs o ++ Γ) ts)
    (args' : HVector (fun t => Var Γ' t) ((regionSig d).args o))
    (regs' : Regions d Γ' ((regionSig d).regs o))
    (k' : NFProg d ((regionSig d).outs o ++ Γ') ts')
    (fuel : Nat) (V : Valuation Γ) (V' : Valuation Γ')
    (hargs : R _ (Expr.lookupArgs args V) (Expr.lookupArgs args' V'))
    (hregs : RegionValsRel OptLift.rel R (denoteRegionsAt E fuel V regs)
      (denoteRegionsAt E' fuel V' regs'))
    (hk : ∀ r r', R _ r r' →
      Option.Rel S (k.denoteAt E fuel (hvAppend r V)) (k'.denoteAt E' fuel (hvAppend r' V'))) :
    Option.Rel S ((region o args regs k).denoteAt E fuel V)
      ((region o args' regs' k').denoteAt E' fuel V') := by
  rw [denoteAt_region, denoteAt_region]
  exact bind_rel (hop fuel fuel rfl _ _ hargs _ _ hregs) hk

/-- **Relational congruence of `region`**, forward form from the fuel `n` to a fuel
    `m ≥ n`. -/
theorem denoteAt_region_fwd (E E' : CallEnv d) {R : ValRel d} {o : (regionSig d).Op}
    (hop : RegionDenote.Fwd (RegionDenote.ofEnv E) (RegionDenote.ofEnv E') R o)
    {Γ Γ' : Ctxt d} {ts ts' : List d.Ty} {S : Valuation ts → Valuation ts' → Prop}
    (args : HVector (fun t => Var Γ t) ((regionSig d).args o))
    (regs : Regions d Γ ((regionSig d).regs o)) (k : NFProg d ((regionSig d).outs o ++ Γ) ts)
    (args' : HVector (fun t => Var Γ' t) ((regionSig d).args o))
    (regs' : Regions d Γ' ((regionSig d).regs o))
    (k' : NFProg d ((regionSig d).outs o ++ Γ') ts')
    {n m : Nat} (hnm : n ≤ m) (V : Valuation Γ) (V' : Valuation Γ')
    (hargs : R _ (Expr.lookupArgs args V) (Expr.lookupArgs args' V'))
    (hregs : RegionValsRel OptLift.fwd R (denoteRegionsAt E n V regs)
      (denoteRegionsAt E' m V' regs'))
    (hk : ∀ r r' b, R _ r r' → k.denoteAt E n (hvAppend r V) = some b →
      ∃ b', k'.denoteAt E' m (hvAppend r' V') = some b' ∧ S b b')
    (out : Valuation ts) (h : (region o args regs k).denoteAt E n V = some out) :
    ∃ out', (region o args' regs' k').denoteAt E' m V' = some out' ∧ S out out' := by
  rw [denoteAt_region] at h
  rw [denoteAt_region]
  exact bind_rel_fwd (hop n m hnm _ _ hargs _ _ hregs) hk out h

/-- The motive of monotonicity from the environment `E₁` at the fuel `n` to the
    environment `E₂` at the fuel `m`: a run at the former is a run at the latter. -/
abbrev RunsPersist (E₁ E₂ : CallEnv d) (n m : Nat) (Γ : Ctxt d) (ts : List d.Ty)
    (p : NFProg d Γ ts) : Prop :=
  ∀ V out, p.denoteAt E₁ n V = some out → p.denoteAt E₂ m V = some out

/-- Regions whose runs persist have region values related forward at the equality
    family. -/
theorem regionValsRel_of_runsPersist (E₁ E₂ : CallEnv d) (n m : Nat) {Γ : Ctxt d}
    (V : Valuation Γ) : {rs : List (List (List d.Ty) × List d.Ty)} → (regs : Regions d Γ rs) →
    RegionsHyps (RunsPersist E₁ E₂ n m) regs →
    RegionValsRel OptLift.fwd ValRel.eq (denoteRegionsAt E₁ n V regs)
      (denoteRegionsAt E₂ m V regs)
  | [], .nil, _ => trivial
  | _ :: _, .cons _ ps, h =>
      ⟨fun B B' hB b hb => by
        cases segsRel_eq hB
        exact ⟨b, h.1 _ _ hb, rfl⟩,
        regionValsRel_of_runsPersist E₁ E₂ n m V ps h.2⟩

/-- **Monotonicity of `region`** in the fuel and the call environment. If the callee
    of the operation persists from `E₁` to `E₂`, and the runs of the regions and of the
    continuation persist from `E₁` at the fuel `n` to `E₂` at a fuel `m ≥ n`, so do the
    runs of the program of the operation. -/
theorem denoteAt_region_mono (E₁ E₂ : CallEnv d) {n m : Nat} (hnm : n ≤ m) {Γ : Ctxt d}
    {ts : List d.Ty} (o : (regionSig d).Op) (hc : CallRel OptLift.fwd E₁ E₂ ValRel.eq o)
    (args : HVector (fun t => Var Γ t) ((regionSig d).args o))
    (regs : Regions d Γ ((regionSig d).regs o)) (k : NFProg d ((regionSig d).outs o ++ Γ) ts)
    (hregs : RegionsHyps (RunsPersist E₁ E₂ n m) regs) (hk : RunsPersist E₁ E₂ n m _ ts k) :
    RunsPersist E₁ E₂ n m Γ ts (region o args regs k) := by
  intro V out h
  obtain ⟨out', h', he⟩ := denoteAt_region_fwd (S := Eq) E₁ E₂
    (RegionDenote.ofEnv_fwd ScfCompat.eq o hc) args regs k args regs k hnm V V rfl
    (regionValsRel_of_runsPersist E₁ E₂ n m V regs hregs)
    (fun r r' b hr hb => by cases hr; exact ⟨b, hk _ _ hb, rfl⟩) out h
  cases he
  exact h'

/-- **Fuel monotonicity.** A run of a structured program at a fuel is a run at every
    larger fuel, with the same result. -/
theorem denoteAt_fuel_mono (E : CallEnv d) {n m : Nat} (hnm : n ≤ m) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (V : Valuation Γ) (out : Valuation ts)
    (h : p.denoteAt E n V = some out) : p.denoteAt E m V = some out :=
  regionRec (motive := RunsPersist E E n m)
    (fun _ _ _ h => h)
    (fun e k ih V out h => by
      unfold denoteAt at h ⊢
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨x, hx, hk⟩ := h
      exact ⟨x, hx, ih _ _ hk⟩)
    (fun o args regs k ihr ihk =>
      denoteAt_region_mono E E hnm o (by
        rcases o with o | ⟨f, as, rs⟩
        · trivial
        · rintro a _ rfl b hb
          exact ⟨b, hb, rfl⟩) args regs k ihr ihk)
    p V out h

end NFProg

/-! ## 6. The existing rules of the constructors as instances -/

section Instances

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option]

open NFProg

/-- The counted-loop case of `NFProg.denoteAt_mono`. -/
example (E₁ E₂ : CallEnv d) (fuel : Nat) {Γ : Ctxt d} {cs ts : List d.Ty}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (ihb : RunsPersist E₁ E₂ fuel fuel _ _ body) (ihk : RunsPersist E₁ E₂ fuel fuel _ _ k) :
    RunsPersist E₁ E₂ fuel fuel _ _ (.forLoop count inits body k) :=
  denoteAt_region_mono E₁ E₂ (Nat.le_refl _) (.inl (.for cs)) trivial (.cons count inits)
    (.cons body .nil) k ⟨ihb, ⟨⟩⟩ ihk

/-- The exit-flag-loop case of `NFProg.denoteAt_mono`. -/
example (E₁ E₂ : CallEnv d) (fuel : Nat) {Γ : Ctxt d} {cs ts : List d.Ty}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts)
    (ihb : RunsPersist E₁ E₂ fuel fuel _ _ body) (ihk : RunsPersist E₁ E₂ fuel fuel _ _ k) :
    RunsPersist E₁ E₂ fuel fuel _ _ (.whileLoop inits body k) :=
  denoteAt_region_mono E₁ E₂ (Nat.le_refl _) (.inl (.while cs)) trivial inits
    (.cons body .nil) k ⟨ihb, ⟨⟩⟩ ihk

/-- The branch case of `NFProg.denoteAt_mono`. -/
example (E₁ E₂ : CallEnv d) (fuel : Nat) {Γ : Ctxt d} {rs ts : List d.Ty}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts)
    (iht : RunsPersist E₁ E₂ fuel fuel _ _ thn) (ihe : RunsPersist E₁ E₂ fuel fuel _ _ els)
    (ihk : RunsPersist E₁ E₂ fuel fuel _ _ k) :
    RunsPersist E₁ E₂ fuel fuel _ _ (.ifThenElse cond thn els k) :=
  denoteAt_region_mono E₁ E₂ (Nat.le_refl _) (.inl (.if rs)) trivial (.cons cond .nil)
    (.cons thn (.cons els .nil)) k ⟨iht, ihe, ⟨⟩⟩ ihk

/-- The call case of `NFProg.denoteAt_mono`. -/
example (E₁ E₂ : CallEnv d) (fuel : Nat) {Γ : Ctxt d} {as rs ts : List d.Ty} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts)
    (h : ∀ (x : Valuation as) (y : Valuation rs),
      E₁.call f as rs x = some y → E₂.call f as rs x = some y)
    (ihk : RunsPersist E₁ E₂ fuel fuel _ _ k) :
    RunsPersist E₁ E₂ fuel fuel _ _ (.call (rs := rs) f args k) :=
  denoteAt_region_mono E₁ E₂ (Nat.le_refl _) (.inr (.call f as rs))
    (fun a a' ha b hb => by cases ha; exact ⟨b, h _ _ hb, rfl⟩) args .nil k ⟨⟩ ihk

/-- `NFProg.denote_forLoop_rel` at one dialect, one carried tuple and the relations of
    a compatible family. -/
example (E E' : CallEnv d) {R : ValRel d} (hR : ScfCompat R) (fuel : Nat) {Γ Γ' : Ctxt d}
    {cs ts ts' : List d.Ty} {S : Valuation ts → Valuation ts' → Prop}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (count' : Var Γ' (HasWord64.word (d := d))) (inits' : HVector (fun t => Var Γ' t) cs)
    (body' : NFProg d (cs ++ HasWord64.word (d := d) :: Γ') cs) (k' : NFProg d (cs ++ Γ') ts')
    (V : Valuation Γ) (V' : Valuation Γ')
    (hargs : R _ (Expr.lookupArgs (HVector.cons count inits) V)
      (Expr.lookupArgs (HVector.cons count' inits') V'))
    (hbody : ∀ i i', R [HasWord64.word (d := d)] i i' → ∀ a a', R cs a a' → Option.Rel (R cs)
      (body.denoteAt E fuel (hvAppend a (hvAppend i V)))
      (body'.denoteAt E' fuel (hvAppend a' (hvAppend i' V'))))
    (hk : ∀ a a', R cs a a' →
      Option.Rel S (k.denoteAt E fuel (hvAppend a V)) (k'.denoteAt E' fuel (hvAppend a' V'))) :
    Option.Rel S ((NFProg.forLoop count inits body k).denoteAt E fuel V)
      ((NFProg.forLoop count' inits' body' k').denoteAt E' fuel V') :=
  denoteAt_region_rel E E' (RegionDenote.ofEnv_rel hR (.inl (.for cs)) trivial)
    (.cons count inits) (.cons body .nil) k (.cons count' inits') (.cons body' .nil) k' fuel V V'
    hargs
    ⟨fun B B' hB =>
      match B, B', hB with
      | .cons a (.cons i .nil), .cons a' (.cons i' .nil), hB => hbody i i' hB.2.1 a a' hB.1,
      trivial⟩ hk

/-- `NFProg.denote_whileLoop_rel` at one dialect, one carried tuple and the relations of
    a compatible family. -/
example (E E' : CallEnv d) {R : ValRel d} (hR : ScfCompat R) (fuel : Nat) {Γ Γ' : Ctxt d}
    {cs ts ts' : List d.Ty} {S : Valuation ts → Valuation ts' → Prop}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts)
    (inits' : HVector (fun t => Var Γ' t) cs)
    (body' : NFProg d (cs ++ Γ') (HasBitType.bit (d := d) :: cs)) (k' : NFProg d (cs ++ Γ') ts')
    (V : Valuation Γ) (V' : Valuation Γ')
    (hinits : R cs (Expr.lookupArgs inits V) (Expr.lookupArgs inits' V'))
    (hbody : ∀ a a', R cs a a' → Option.Rel (R (HasBitType.bit (d := d) :: cs))
      (body.denoteAt E fuel (hvAppend a V)) (body'.denoteAt E' fuel (hvAppend a' V')))
    (hk : ∀ a a', R cs a a' →
      Option.Rel S (k.denoteAt E fuel (hvAppend a V)) (k'.denoteAt E' fuel (hvAppend a' V'))) :
    Option.Rel S ((NFProg.whileLoop inits body k).denoteAt E fuel V)
      ((NFProg.whileLoop inits' body' k').denoteAt E' fuel V') :=
  denoteAt_region_rel E E' (RegionDenote.ofEnv_rel hR (.inl (.while cs)) trivial)
    inits (.cons body .nil) k inits' (.cons body' .nil) k' fuel V V' hinits
    ⟨fun B B' hB =>
      match B, B', hB with
      | .cons a .nil, .cons a' .nil, hB => hbody a a' hB.1,
      trivial⟩ hk

/-- `NFProg.denote_ifThenElse_rel` at one dialect, one result tuple and the relations
    of a compatible family. -/
example (E E' : CallEnv d) {R : ValRel d} (hR : ScfCompat R) (fuel : Nat) {Γ Γ' : Ctxt d}
    {rs ts ts' : List d.Ty} {S : Valuation ts → Valuation ts' → Prop}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts)
    (cond' : Var Γ' (HasBitType.bit (d := d))) (thn' els' : NFProg d Γ' rs)
    (k' : NFProg d (rs ++ Γ') ts')
    (V : Valuation Γ) (V' : Valuation Γ')
    (hcond : R _ (Expr.lookupArgs (HVector.cons cond .nil) V)
      (Expr.lookupArgs (HVector.cons cond' .nil) V'))
    (hthn : Option.Rel (R rs) (thn.denoteAt E fuel V) (thn'.denoteAt E' fuel V'))
    (hels : Option.Rel (R rs) (els.denoteAt E fuel V) (els'.denoteAt E' fuel V'))
    (hk : ∀ a a', R rs a a' →
      Option.Rel S (k.denoteAt E fuel (hvAppend a V)) (k'.denoteAt E' fuel (hvAppend a' V'))) :
    Option.Rel S ((NFProg.ifThenElse cond thn els k).denoteAt E fuel V)
      ((NFProg.ifThenElse cond' thn' els' k').denoteAt E' fuel V') :=
  denoteAt_region_rel E E' (RegionDenote.ofEnv_rel hR (.inl (.if rs)) trivial)
    (.cons cond .nil) (.cons thn (.cons els .nil)) k (.cons cond' .nil)
    (.cons thn' (.cons els' .nil)) k' fuel V V' hcond
    ⟨fun B B' _ => match B, B' with | .nil, .nil => hthn,
      fun B B' _ => match B, B' with | .nil, .nil => hels, trivial⟩ hk

/-- `NFProg.denote_call_rel` at one dialect, one symbol and signature and the relations
    of a compatible family. -/
example (E E' : CallEnv d) {R : ValRel d} (hR : ScfCompat R) (fuel : Nat) {Γ Γ' : Ctxt d}
    {as rs ts ts' : List d.Ty} {S : Valuation ts → Valuation ts' → Prop} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts)
    (args' : HVector (fun t => Var Γ' t) as) (k' : NFProg d (rs ++ Γ') ts')
    (V : Valuation Γ) (V' : Valuation Γ')
    (hargs : R as (Expr.lookupArgs args V) (Expr.lookupArgs args' V'))
    (hcall : ∀ a a', R as a a' → Option.Rel (R rs) (E.call f as rs a) (E'.call f as rs a'))
    (hk : ∀ r r', R rs r r' →
      Option.Rel S (k.denoteAt E fuel (hvAppend r V)) (k'.denoteAt E' fuel (hvAppend r' V'))) :
    Option.Rel S ((NFProg.call (rs := rs) f args k).denoteAt E fuel V)
      ((NFProg.call (rs := rs) f args' k').denoteAt E' fuel V') :=
  denoteAt_region_rel E E' (RegionDenote.ofEnv_rel hR (.inr (.call f as rs)) hcall)
    args .nil k args' .nil k' fuel V V' hargs trivial hk

end Instances

/-! ## 7. The leak events of the operations -/

/-- The leak run of a region: a partial function from the valuations of its bound
    segments to the valuation of its results and the list of its events. -/
abbrev RegionLeakVal {d : Dialect.{0, 0}} [TyDenote d.Ty]
    (r : List (List d.Ty) × List d.Ty) : Type :=
  HVector (fun b : List d.Ty => Valuation (d := d) b) r.1 →
    Option (Valuation (d := d) r.2 × List CTLeak)

/-- The leak events of the operations of the signature `S`: the events an operation
    emits from its arguments, and its run on the leak runs of its regions, with the
    events of the regions in execution order. -/
class RegionLeak (d : Dialect.{0, 0}) [TyDenote d.Ty] (S : RegionSig d.Ty) where
  /-- The events the operation `o` emits from its arguments, ahead of its regions. -/
  events : (o : S.Op) → Valuation (d := d) (S.args o) → List CTLeak
  /-- The run of the operation `o` at the fuel `fuel` on the leak runs of its regions. -/
  run : (o : S.Op) → (fuel : Nat) → Valuation (d := d) (S.args o) →
    HVector (RegionLeakVal (d := d)) (S.regs o) →
    Option (Valuation (d := d) (S.outs o) × List CTLeak)

section Leak

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- The leak events of structured control flow, as `NFProg.leakRun` emits them: the
    counted loop emits `trip n` for its trip count and runs `forIterLeak`; the exit-flag
    loop emits nothing ahead of its body and runs `whileIterLeak`, which emits
    `branch b` after each run of the body; the branch emits `branch b` for its bit and
    runs the arm the bit selects. -/
instance RegionLeak.scf :
    RegionLeak d (RegionSig.scf (HasWord64.word (d := d)) (HasBitType.bit (d := d))) where
  events
    | .for _, a => [.trip (HasWord64.toNat (d := d) a.head)]
    | .while _, _ => []
    | .if _, a => [.branch (HasBoolBit.toBool (d := d) a.head)]
  run
    | .for _, _, a, .cons body .nil =>
        forIterLeak
          (fun i acc => body (.cons acc (.cons (.cons (HasWord64.ofNat (d := d) i) .nil) .nil)))
          (List.range (HasWord64.toNat (d := d) a.head)) a.tail
    | .while _, fuel, a, .cons body .nil =>
        whileIterLeak (fun acc => body (.cons acc .nil)) fuel a
    | .if _, _, a, .cons thn (.cons els .nil) =>
        if HasBoolBit.toBool (d := d) a.head then thn .nil else els .nil

/-- A call has no modelled leakage: its run fails, as `NFProg.leakRun` does at a
    `call` node. -/
instance RegionLeak.func : RegionLeak d (RegionSig.func (T := d.Ty)) where
  events _ _ := []
  run _ _ _ _ := none

/-- The leak events of a sum of signatures are those of the summands. -/
instance RegionLeak.sum {S₁ S₂ : RegionSig d.Ty} [RegionLeak d S₁] [RegionLeak d S₂] :
    RegionLeak d (S₁.sum S₂) where
  events
    | .inl o => RegionLeak.events (d := d) (S := S₁) o
    | .inr o => RegionLeak.events (d := d) (S := S₂) o
  run
    | .inl o => RegionLeak.run (d := d) (S := S₁) o
    | .inr o => RegionLeak.run (d := d) (S := S₂) o

variable [DialectDenote d]

/-- The leak runs of the regions `regs` at the fuel `fuel` inside the valuation `V` of
    the enclosing context. -/
def NFProg.leakRegions (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} (V : Valuation Γ) :
    {rs : List (List (List d.Ty) × List d.Ty)} → NFProg.Regions d Γ rs →
    HVector (RegionLeakVal (d := d)) rs
  | [], .nil => .nil
  | _ :: _, .cons p ps =>
      .cons (fun B => NFProg.leakRun M fuel p (NFProg.scopeVal B V))
        (NFProg.leakRegions M fuel V ps)

/-- **The leak run of the program of an operation**: the run of the operation on the
    leak runs of its regions, then the continuation at the outputs; the events are those
    of the operation, then those of its run, then those of the continuation. -/
theorem NFProg.leakRun_region (M : LeakModel d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty}
    (o : (NFProg.regionSig d).Op)
    (args : HVector (fun t => Var Γ t) ((NFProg.regionSig d).args o))
    (regs : NFProg.Regions d Γ ((NFProg.regionSig d).regs o))
    (k : NFProg d ((NFProg.regionSig d).outs o ++ Γ) ts) (V : Valuation Γ) :
    NFProg.leakRun M fuel (NFProg.region o args regs k) V =
      (RegionLeak.run (d := d) (S := NFProg.regionSig d) o fuel (Expr.lookupArgs args V)
          (NFProg.leakRegions M fuel V regs)).bind fun r =>
        (NFProg.leakRun M fuel k (hvAppend r.1 V)).map fun q =>
          (q.1, RegionLeak.events (d := d) (S := NFProg.regionSig d) o (Expr.lookupArgs args V) ++
            (r.2 ++ q.2)) := by
  rcases o with (cs | cs | rs) | ⟨f, as, rs⟩
  · match args, regs with
    | .cons count inits, .cons body .nil => rfl
  · match regs with
    | .cons body .nil => rfl
  · match args, regs with
    | .cons cond .nil, .cons thn (.cons els .nil) => rfl
  · match regs with
    | .nil => rfl

end Leak

end CatCrypt.Crypto.SecureCompilation.VIR
