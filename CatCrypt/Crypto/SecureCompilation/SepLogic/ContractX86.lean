/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.Contract
public import CatCrypt.Crypto.SecureCompilation.SepLogic.X86State
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSig

/-!
# Callee specifications as contracts over `AState`

Two address states that agree on every location (`X86.Loc`: registers, flags, memory bytes)
are equal (`X86.eq_of_agreeOn_univ`), so every predicate on `AState` is an assertion with
the footprint `Set.univ` (`X86.stateAssert`).

The write set of a callee interface `c` at the entry state `s` (`X86.calleeWrites c s`) is
made of the registers of the clobber set other than `%rsp`, the five flags, and the memory
bytes of the footprint `c.foot s`. The contract `X86.calleeContract c` has the entry state as
its logical variable: the precondition at `a` says that the state is `a` and satisfies
`c.pre`, the postcondition at `a` is `c.post a`, and the public relation is `c.pub`.

## Main definitions

* `X86.stateAssert`: a predicate on `AState` as an assertion with the full footprint.
* `X86.calleeWrites`: the locations a callee of an interface may change.
* `X86.calleeContract`: the contract of a callee interface.

## Main results

* `X86.eq_of_agreeOn_univ`: agreement on every location is equality.
* `X86.calleeSpec_iff_contract`: `CalleeSpec X c` holds exactly when `X` meets
  `calleeContract c`.
* `X86.calleeSpec_of_contract`: a run relation that meets a contract whose preconditions
  cover `c.pre`, whose postconditions imply `c.post` and whose write sets lie in
  `calleeWrites c` meets `c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic.X86

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.CT
open Footprinted SAssert

/-- Two address states that agree on every location are equal. -/
theorem eq_of_agreeOn_univ {s t : AState} (h : AgreeOn Set.univ s t) : s = t := by
  obtain ⟨rs, ⟨c₁, p₁, z₁, s₁, o₁⟩, ms⟩ := s
  obtain ⟨rt, ⟨c₂, p₂, z₂, s₂, o₂⟩, mt⟩ := t
  have hr : rs = rt := funext fun r => h (.reg r) trivial
  have hm : ms = mt := funext fun a => h (.mem a) trivial
  have hc : c₁ = c₂ := h (.flag .cf) trivial
  have hp : p₁ = p₂ := h (.flag .pf) trivial
  have hz : z₁ = z₂ := h (.flag .zf) trivial
  have hs : s₁ = s₂ := h (.flag .sf) trivial
  have ho : o₁ = o₂ := h (.flag .of) trivial
  subst hr hm hc hp hz hs ho
  rfl

/-- A predicate on address states as an assertion with the full footprint. -/
def stateAssert (p : AState → Prop) : SAssert AState Loc where
  fp := Set.univ
  holds := p
  supp _ _ h hs := eq_of_agreeOn_univ h ▸ hs

@[simp] theorem holds_stateAssert (p : AState → Prop) (s : AState) :
    (stateAssert p).holds s ↔ p s := Iff.rfl

/-- The locations a callee of the interface `c` may change from the entry state `s`: the
    registers of the clobber set other than `%rsp`, the flags, and the memory bytes of the
    footprint. -/
def calleeWrites (c : CalleeSig) (s : AState) : Set Loc := fun l =>
  match l with
  | .reg r => c.clob r = true ∧ r ≠ "%rsp"
  | .flag _ => True
  | .mem x => c.foot s x

/-- The contract of the callee interface `c`, with the entry state as logical variable. -/
def calleeContract (c : CalleeSig) : ContractSpec AState Loc AState where
  pre a := stateAssert fun s => s = a ∧ c.pre s
  post a := stateAssert (c.post a)
  writes _ s := calleeWrites c s
  pub := c.pub

/-- **A callee specification is a contract.** `CalleeSpec X c` holds exactly when the run
    relation `X` meets `calleeContract c`. -/
theorem calleeSpec_iff_contract {X : CalleeRun} {c : CalleeSig} :
    CalleeSpec X c ↔ SContract X (calleeContract c) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro a s ⟨-, hs⟩
      exact h.halts s hs
    · rintro a s t s' ⟨rfl, hs⟩ hX
      exact h.post s t s' hs hX
    · rintro a s t s' ⟨-, hs⟩ hX (r | _ | x) hl
      · change ¬ (c.clob r = true ∧ r ≠ "%rsp") at hl
        change s.regs r = s'.regs r
        by_cases hr : r = "%rsp"
        · subst hr
          exact (h.rsp s t s' hs hX).symm
        · exact (h.keep s t s' hs hX _ (by simpa [hr] using hl)).symm
      · exact absurd trivial hl
      · exact (h.frame s t s' hs hX x hl).symm
    · rintro a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' ⟨-, h₁⟩ ⟨-, h₂⟩ hp hX₁ hX₂
      exact h.ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂
  · intro h
    refine ⟨fun s hs => h.halts s s ⟨rfl, hs⟩, fun s t s' hs hX => ?_,
      fun s t s' hs hX r hr => ?_, fun s t s' hs hX x hx => ?_,
      fun s t s' hs hX => h.post s s t s' ⟨rfl, hs⟩ hX,
      fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ =>
        h.ct s₁ s₂ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, h₁⟩ ⟨rfl, h₂⟩ hp hX₁ hX₂⟩
    · exact (h.keep s s t s' ⟨rfl, hs⟩ hX (.reg "%rsp") fun hl => hl.2 rfl).symm
    · exact (h.keep s s t s' ⟨rfl, hs⟩ hX (.reg r) fun hl =>
        Bool.noConfusion (hl.1.symm.trans hr)).symm
    · exact (h.keep s s t s' ⟨rfl, hs⟩ hX (.mem x) hx).symm

/-- **A callee specification from a contract.** If every entry state satisfying `c.pre`
    satisfies a precondition of `C` whose postcondition implies `c.post` and whose write set
    lies in `calleeWrites c`, and `c.pub` implies the public relation of `C`, then a run
    relation meeting `C` meets `c`. -/
theorem calleeSpec_of_contract {α : Type} {X : CalleeRun} {C : ContractSpec AState Loc α}
    {c : CalleeSig} (h : SContract X C)
    (hpre : ∀ s, c.pre s → ∃ a, (C.pre a).holds s ∧
      (∀ s', (C.post a).holds s' → c.post s s') ∧ C.writes a s ⊆ calleeWrites c s)
    (hpub : ∀ s₁ s₂, c.pub s₁ s₂ → C.pub s₁ s₂) : CalleeSpec X c :=
  calleeSpec_iff_contract.2 <| h.adapt
    (fun b s ⟨hb, hs⟩ => by
      subst hb
      exact hpre s hs)
    hpub

/-! ## Example: an eight-byte store as a callee -/

section Examples

/-- The callee that stores `v` at the eight bytes from `a`, with an empty trace. -/
def storeRun (a v : BitVec 64) : CalleeRun := detRun (setMem64 a v) fun _ => []

/-- The footprinted contract of the store: the old value `x` is the logical variable. -/
def storeContract (a v : BitVec 64) : ContractSpec AState Loc (BitVec 64) where
  pre x := memPts 8 a x
  post _ := memPts 8 a v
  writes _ _ := Loc.mem '' (⟨a, 8⟩ : Rng 64).toSet
  pub _ _ := True

theorem storeRun_contract (a v : BitVec 64) : SContract (storeRun a v) (storeContract a v) :=
  sContract_detRun_iff.2 ⟨fun x => triple_setMem64 a x v,
    fun _ s _ => writesIn_setMem64 a v s, fun _ _ _ _ _ _ _ => rfl⟩

/-- The interface of the store: no register clobbered, the eight bytes from `a` as
    footprint, and `v` read back at `a`. -/
def storeSig (a v : BitVec 64) : CalleeSig where
  args := []
  res := none
  clob _ := false
  pre _ := True
  foot _ x := x ∈ (⟨a, 8⟩ : Rng 64).toSet
  post _ s' := readLE 8 s'.mem a = v
  pub _ _ := True

/-- The store meets its interface, from its footprinted contract. -/
example (a v : BitVec 64) : CalleeSpec (storeRun a v) (storeSig a v) :=
  calleeSpec_of_contract (storeRun_contract a v)
    (fun s _ => ⟨readLE 8 s.mem a, rfl, fun _ h => h, by
      rintro _ ⟨x, hx, rfl⟩
      exact hx⟩)
    (fun _ _ _ => trivial)

end Examples

end CatCrypt.Crypto.SecureCompilation.SepLogic.X86
