/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm

/-!
# Register-allocation soundness for the 64-bit bignum path (`BInst`/`BState`)

`ArmRegAlloc.renameABlock_runABlock` proves that an injective register renaming
commutes with `runABlock` for the 32-bit ChaCha path (`AInst`/`AState`), and the
generic `GenericRegAlloc.renameBlock_runBlock` recovers it via a `RegMachine`
instance. Neither covers the **64-bit bignum/field path** (`BInst`/`BState`) — the
path the main lowering theorem `ComToArm.regToBOp_denote` runs over — because
`BInst` carries flag-setting instructions (`ADDS`/`ADCS`/`SUBS`/`SBCS`/`CSEL`) that
read and write the carry flag `cf`. The flag is **global** machine state, not a
named register, so the single-`writtenName` `RegMachine` shape does not fit; we
prove the renaming-soundness theorem directly here, with the `Reindexed` relation
additionally pinning the carry flag (which a register renaming leaves untouched).

This is the **register-allocation-inside-the-equality** result for the bignum
backend: `regToBOp_alloc_denote` states that running the *renamed* (allocated)
lowered block on a reindexed state computes, at the renamed names, exactly the
source program's denotation `armTarget.denote p`. Allocation, modelled as the
register renaming `ρ` the `GpAlloc` map induces, is thereby brought *inside* a
proved semantic equality, in addition to the byte-length fact `compiled_length`.

`Reindexed ρ s t` says `t` is `s` with every name `n` relabelled to `ρ n` (on the
non-`xzr` names) and the same carry flag. For an **injective**, `xzr`-preserving
`ρ` — the validity condition a non-aliasing allocation satisfies — renaming
commutes with the machine semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmBInstRegAlloc

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.ScalarLin

/-! ## 1. `BState` register-file laws not already in `ArmModel` -/

/-- A register write leaves the carry flag unchanged. -/
@[simp] theorem cf_set (s : BState) (r : String) (v : X64) : (s.set r v).cf = s.cf := by
  simp only [BState.set]; split <;> rfl

/-- A register write leaves every *other* register unchanged. -/
theorem get_set_other (s : BState) (r r' : String) (v : X64) (h : r ≠ r') :
    (s.set r' v).get r = s.get r := by
  by_cases hr' : r' = "xzr"
  · simp [BState.set, hr']
  · simp [BState.set, BState.get, hr', h]

/-- A flag-setting write leaves every *other* register unchanged. -/
theorem get_setC_other (s : BState) (r r' : String) (v : X64) (c : Bool) (h : r ≠ r') :
    (s.setC r' v c).get r = s.get r := by
  by_cases hr' : r' = "xzr"
  · simp [BState.setC, BState.get, hr']
  · simp [BState.setC, BState.get, hr', h]

/-! ## 2. The renaming and the `Reindexed` relation -/

/-- Apply a register renaming `ρ` to every register operand of a `BInst`
    (immediates, shift amounts, and condition codes are untouched). -/
def renameBInst (ρ : String → String) : BInst → BInst
  | .add d a b => .add (ρ d) (ρ a) (ρ b)
  | .sub d a b => .sub (ρ d) (ρ a) (ρ b)
  | .adds d a b => .adds (ρ d) (ρ a) (ρ b)
  | .adcs d a b => .adcs (ρ d) (ρ a) (ρ b)
  | .adc d a b => .adc (ρ d) (ρ a) (ρ b)
  | .subs d a b => .subs (ρ d) (ρ a) (ρ b)
  | .sbcs d a b => .sbcs (ρ d) (ρ a) (ρ b)
  | .sbc d a b => .sbc (ρ d) (ρ a) (ρ b)
  | .mul d a b => .mul (ρ d) (ρ a) (ρ b)
  | .umulh d a b => .umulh (ρ d) (ρ a) (ρ b)
  | .and d a b => .and (ρ d) (ρ a) (ρ b)
  | .orr d a b => .orr (ρ d) (ρ a) (ρ b)
  | .eor d a b => .eor (ρ d) (ρ a) (ρ b)
  | .csel d a b c => .csel (ρ d) (ρ a) (ρ b) c
  | .movz d imm16 => .movz (ρ d) imm16
  | .movk d imm16 hw => .movk (ρ d) imm16 hw
  | .mov d a => .mov (ρ d) (ρ a)
  | .lsr d a m => .lsr (ρ d) (ρ a) m
  | .lsl d a m => .lsl (ρ d) (ρ a) m

/-- Apply a renaming to a whole block. -/
def renameBBlock (ρ : String → String) (block : List BInst) : List BInst :=
  block.map (renameBInst ρ)

/-- `Reindexed ρ s t`: `t` is `s` relabelled by `ρ` — reading `ρ n` in `t` gives
    `s`'s value at `n` (for every name whose image is not the discard register
    `xzr`), and the carry flag agrees. -/
def Reindexed (ρ : String → String) (s t : BState) : Prop :=
  (∀ n, ρ n ≠ "xzr" → t.get (ρ n) = s.get n) ∧ t.cf = s.cf

/-- **Renamed read = source read.** For an injective, `xzr`-preserving `ρ`, reading
    `ρ a` in the reindexed state `t` equals reading `a` in `s` (if `ρ a = xzr` then
    `a = xzr` by injectivity, and both read the fixed `0`). -/
theorem reindexed_get (ρ : String → String) (hinj : Function.Injective ρ)
    (hxzr : ρ "xzr" = "xzr") (s t : BState) (h : Reindexed ρ s t) (a : String) :
    t.get (ρ a) = s.get a := by
  by_cases ha : ρ a = "xzr"
  · have : a = "xzr" := hinj (by rw [ha, hxzr])
    subst this; rw [hxzr]; simp [BState.get]
  · exact h.1 a ha

/-! ## 3. The renaming theorem -/

/-- **One step commutes with renaming.** Running the renamed instruction on the
    reindexed state `t` is reindexed to running the original on `s`. The flag-out
    agrees because it is computed from the (agreeing) read values and the
    (agreeing) carry-in. -/
theorem evalBInst_rename_reindexed (ρ : String → String) (hinj : Function.Injective ρ)
    (hxzr : ρ "xzr" = "xzr") (s t : BState) (i : BInst) (h : Reindexed ρ s t) :
    Reindexed ρ (evalBInst s i) (evalBInst t (renameBInst ρ i)) := by
  have hget : ∀ a, t.get (ρ a) = s.get a := reindexed_get ρ hinj hxzr s t h
  have hcf : t.cf = s.cf := h.2
  -- `reindexed_set`: a write at `ρ d`/`d` of the same value preserves `Reindexed`.
  have hset : ∀ (d : String) (v : X64), Reindexed ρ (s.set d v) (t.set (ρ d) v) := by
    intro d v
    refine ⟨?_, by simp [cf_set, hcf]⟩
    intro n hn
    by_cases hd : ρ d = "xzr"
    · have hdx : d = "xzr" := hinj (by rw [hd, hxzr])
      subst hdx
      rw [hxzr]
      simp only [BState.set]
      exact h.1 n hn
    · have hdx : d ≠ "xzr" := fun hc => hd (by rw [hc, hxzr])
      by_cases hnd : n = d
      · subst hnd
        rw [BState.get_set_same _ _ _ hd, BState.get_set_same _ _ _ hdx]
      · have hne : ρ n ≠ ρ d := fun hc => hnd (hinj hc)
        rw [get_set_other _ _ _ _ hne, get_set_other _ _ _ _ hnd]
        exact h.1 n hn
  -- `reindexed_setC`: a flag-setting write of the same value/flag preserves `Reindexed`.
  have hsetC : ∀ (d : String) (v : X64) (c : Bool),
      Reindexed ρ (s.setC d v c) (t.setC (ρ d) v c) := by
    intro d v c
    refine ⟨?_, by simp [BState.cf_setC]⟩
    intro n hn
    by_cases hd : ρ d = "xzr"
    · have hdx : d = "xzr" := hinj (by rw [hd, hxzr])
      subst hdx
      rw [hxzr]
      simp only [BState.setC]
      exact h.1 n hn
    · have hdx : d ≠ "xzr" := fun hc => hd (by rw [hc, hxzr])
      by_cases hnd : n = d
      · subst hnd
        rw [BState.get_setC_same _ _ _ _ hd, BState.get_setC_same _ _ _ _ hdx]
      · have hne : ρ n ≠ ρ d := fun hc => hnd (hinj hc)
        rw [get_setC_other _ _ _ _ _ hne, get_setC_other _ _ _ _ _ hnd]
        exact h.1 n hn
  cases i <;>
    simp only [evalBInst, renameBInst, addWithCarry, subWithBorrow, hget, hcf] <;>
    first
      | exact hset _ _
      | exact hsetC _ _ _

/-- **Block renaming soundness (the bignum-path renaming theorem).** For an injective,
    `xzr`-preserving renaming `ρ`, running the renamed block on a reindexed state
    is reindexed to running the original block — the `BInst`/`BState` analogue of
    `ArmRegAlloc.renameABlock_runABlock`, with the carry flag tracked. -/
theorem renameBBlock_runBBlock (ρ : String → String) (hinj : Function.Injective ρ)
    (hxzr : ρ "xzr" = "xzr") (block : List BInst) (s t : BState) (h : Reindexed ρ s t) :
    Reindexed ρ (runBBlock s block) (runBBlock t (renameBBlock ρ block)) := by
  induction block generalizing s t with
  | nil => simpa [renameBBlock] using h
  | cons i is ih =>
    simp only [renameBBlock, List.map_cons, runBBlock_cons]
    exact ih (evalBInst s i) (evalBInst t (renameBInst ρ i))
      (evalBInst_rename_reindexed ρ hinj hxzr s t i h)

/-! ## 4. Allocation inside the waist equality -/

/-- **Register allocation preserves the source denotation.** Running the *renamed*
    (allocated) lowered block on a reindexed state `t` computes, at the renamed
    names, exactly the source program's denotation `armTarget.denote p`. Composes
    the lowering theorem `regToBOp_denote` (allocation-free, virtual names) with the
    renaming theorem `renameBBlock_runBBlock`: register allocation — modelled as
    the injective renaming an aliasing-free `GpAlloc` induces — is *inside* a
    proved semantic equality, in addition to the byte-length fact. -/
theorem regToBOp_alloc_denote (ρ : String → String) (hinj : Function.Injective ρ)
    (hxzr : ρ "xzr" = "xzr") (p : RegProg) (s t : BState) (h : Reindexed ρ s t) :
    Reindexed ρ (armTarget.denote p s)
      (runBBlock t (renameBBlock ρ (lowerBBlock (regToBOp p)))) := by
  have hb := renameBBlock_runBBlock ρ hinj hxzr (lowerBBlock (regToBOp p)) s t h
  rwa [regToBOp_denote] at hb

/-! ## 5. Injective-on-block-names: tying the renaming theorem to the concrete allocator

The global-injectivity hypothesis above is the standard "validated renaming" shape,
but the *concrete* allocation map `gpOf alloc` the encoder uses is **not** globally
injective (it returns a distinct `<UNALLOCATED:n>` sentinel off-domain, and `wzr`/
`xzr` are fixed points). What an aliasing-free allocation actually guarantees is
injectivity on the **register names the block uses**. We weaken the renaming theorem to that
hypothesis (`ReindexedOn`/`RenInjOn` scoped to a name list `ns ⊇ block names`), then
discharge it for the real `gpOf alloc` via an `allocValidOn` no-alias certificate —
so the soundness statement is about the encoder's actual register substitution
`renameBBlock (gpOf alloc)` (the encoder resolves every operand through `gpOf alloc`). -/

/-- The register names one `BInst` mentions (destination then sources). -/
def bNames : BInst → List String
  | .add d a b | .sub d a b | .adds d a b | .adcs d a b | .adc d a b
  | .subs d a b | .sbcs d a b | .sbc d a b | .mul d a b | .umulh d a b
  | .and d a b | .orr d a b | .eor d a b | .csel d a b _ => [d, a, b]
  | .movz d _ => [d]
  | .movk d _ _ => [d]
  | .mov d a => [d, a]
  | .lsr d a _ | .lsl d a _ => [d, a]

/-- Every register name a block mentions. -/
def bBlockNames (block : List BInst) : List String := block.flatMap bNames

/-- `ρ` is injective on the name list `ns`. -/
def RenInjOn (ns : List String) (ρ : String → String) : Prop :=
  ∀ a ∈ ns, ∀ b ∈ ns, ρ a = ρ b → a = b

/-- `Reindexed` restricted to a name list `ns`: agreement at `ρ n` only for `n ∈ ns`. -/
def ReindexedOn (ns : List String) (ρ : String → String) (s t : BState) : Prop :=
  (∀ n ∈ ns, ρ n ≠ "xzr" → t.get (ρ n) = s.get n) ∧ t.cf = s.cf

/-- Renamed read = source read, on `ns` (with `"xzr" ∈ ns` so the discard case closes
    by `ns`-injectivity). -/
theorem reindexedOn_get (ns : List String) (ρ : String → String) (hinj : RenInjOn ns ρ)
    (hxzr : ρ "xzr" = "xzr") (hxzrmem : "xzr" ∈ ns) (s t : BState)
    (h : ReindexedOn ns ρ s t) (a : String) (ha : a ∈ ns) :
    t.get (ρ a) = s.get a := by
  by_cases hax : ρ a = "xzr"
  · have : a = "xzr" := hinj a ha "xzr" hxzrmem (by rw [hax, hxzr])
    subst this; rw [hxzr]; simp [BState.get]
  · exact h.1 a ha hax

/-- One step commutes with renaming, on `ns`. -/
theorem evalBInst_rename_reindexedOn (ns : List String) (ρ : String → String)
    (hinj : RenInjOn ns ρ) (hxzr : ρ "xzr" = "xzr") (hxzrmem : "xzr" ∈ ns)
    (s t : BState) (i : BInst) (hsub : ∀ n ∈ bNames i, n ∈ ns) (h : ReindexedOn ns ρ s t) :
    ReindexedOn ns ρ (evalBInst s i) (evalBInst t (renameBInst ρ i)) := by
  have hcf : t.cf = s.cf := h.2
  have hset : ∀ d ∈ ns, ∀ v : X64, ReindexedOn ns ρ (s.set d v) (t.set (ρ d) v) := by
    intro d hdns v
    refine ⟨?_, by simp [cf_set, hcf]⟩
    intro n hnns hn
    by_cases hd : ρ d = "xzr"
    · have hdx : d = "xzr" := hinj d hdns "xzr" hxzrmem (by rw [hd, hxzr])
      subst hdx; rw [hxzr]; simp only [BState.set]; exact h.1 n hnns hn
    · have hdx : d ≠ "xzr" := fun hc => hd (by rw [hc, hxzr])
      by_cases hnd : n = d
      · subst hnd; rw [BState.get_set_same _ _ _ hd, BState.get_set_same _ _ _ hdx]
      · have hne : ρ n ≠ ρ d := fun hc => hnd (hinj n hnns d hdns hc)
        rw [get_set_other _ _ _ _ hne, get_set_other _ _ _ _ hnd]
        exact h.1 n hnns hn
  have hsetC : ∀ d ∈ ns, ∀ (v : X64) (c : Bool),
      ReindexedOn ns ρ (s.setC d v c) (t.setC (ρ d) v c) := by
    intro d hdns v c
    refine ⟨?_, by simp [BState.cf_setC]⟩
    intro n hnns hn
    by_cases hd : ρ d = "xzr"
    · have hdx : d = "xzr" := hinj d hdns "xzr" hxzrmem (by rw [hd, hxzr])
      subst hdx; rw [hxzr]; simp only [BState.setC]; exact h.1 n hnns hn
    · have hdx : d ≠ "xzr" := fun hc => hd (by rw [hc, hxzr])
      by_cases hnd : n = d
      · subst hnd; rw [BState.get_setC_same _ _ _ _ hd, BState.get_setC_same _ _ _ _ hdx]
      · have hne : ρ n ≠ ρ d := fun hc => hnd (hinj n hnns d hdns hc)
        rw [get_setC_other _ _ _ _ _ hne, get_setC_other _ _ _ _ _ hnd]
        exact h.1 n hnns hn
  have hg : ∀ a ∈ bNames i, t.get (ρ a) = s.get a :=
    fun a ha => reindexedOn_get ns ρ hinj hxzr hxzrmem s t h a (hsub a ha)
  cases i <;>
    simp only [bNames, List.mem_cons, List.not_mem_nil, forall_eq_or_imp] at hg <;>
    simp only [evalBInst, renameBInst, addWithCarry, subWithBorrow, hcf, hg] <;>
    first
      | exact hset _ (hsub _ (List.mem_cons_self ..)) _
      | exact hsetC _ (hsub _ (List.mem_cons_self ..)) _ _

/-- **Block renaming soundness, scoped to the block's names.** Only injectivity on
    `ns ⊇ bBlockNames block` (plus `"xzr" ∈ ns`) is required — the property an
    aliasing-free allocation actually has. -/
theorem renameBBlock_runBBlock_on (ns : List String) (ρ : String → String)
    (hinj : RenInjOn ns ρ) (hxzr : ρ "xzr" = "xzr") (hxzrmem : "xzr" ∈ ns)
    (block : List BInst) (hsub : ∀ n ∈ bBlockNames block, n ∈ ns)
    (s t : BState) (h : ReindexedOn ns ρ s t) :
    ReindexedOn ns ρ (runBBlock s block) (runBBlock t (renameBBlock ρ block)) := by
  induction block generalizing s t with
  | nil => simpa [renameBBlock] using h
  | cons i is ih =>
    have hi : ∀ n ∈ bNames i, n ∈ ns := fun n hn =>
      hsub n (by simp only [bBlockNames, List.flatMap_cons, List.mem_append]; exact Or.inl hn)
    have his : ∀ n ∈ bBlockNames is, n ∈ ns := fun n hn =>
      hsub n (by simp only [bBlockNames, List.flatMap_cons, List.mem_append]; exact Or.inr hn)
    simp only [renameBBlock, List.map_cons, runBBlock_cons]
    exact ih his (evalBInst s i) (evalBInst t (renameBInst ρ i))
      (evalBInst_rename_reindexedOn ns ρ hinj hxzr hxzrmem s t i hi h)

/-- The scoped allocation-inside-the-equality result: the renamed (allocated) block,
    run on a `ns`-reindexed state, computes the source denotation at the renamed names,
    under injectivity only on the block's names. -/
theorem regToBOp_alloc_denote_on (ns : List String) (ρ : String → String)
    (hinj : RenInjOn ns ρ) (hxzr : ρ "xzr" = "xzr") (hxzrmem : "xzr" ∈ ns) (p : RegProg)
    (hsub : ∀ n ∈ bBlockNames (lowerBBlock (regToBOp p)), n ∈ ns) (s t : BState)
    (h : ReindexedOn ns ρ s t) :
    ReindexedOn ns ρ (armTarget.denote p s)
      (runBBlock t (renameBBlock ρ (lowerBBlock (regToBOp p)))) := by
  have hb := renameBBlock_runBBlock_on ns ρ hinj hxzr hxzrmem
    (lowerBBlock (regToBOp p)) hsub s t h
  rwa [regToBOp_denote] at hb

/-! ## 6. Discharging the hypothesis for the concrete `gpOf alloc` -/

/-- `gpOf alloc` fixes the discard register `xzr` (its second branch). -/
@[simp] theorem gpOf_xzr (alloc : GpAlloc) : gpOf alloc "xzr" = "xzr" := by
  simp [gpOf]

/-- **No-alias allocation certificate.** `gpOf alloc` is injective on the block's
    names (and `xzr`) — exactly the translation-validation check that no two live
    names share a physical register and no name is left `<UNALLOCATED>`-colliding. -/
def allocValidOn (alloc : GpAlloc) (block : List BInst) : Prop :=
  RenInjOn ("xzr" :: bBlockNames block) (gpOf alloc)

/-- **Allocation inside the equality, for the concrete emitted renaming.** Under the
    `allocValidOn` no-alias certificate, the block renamed by the encoder's own
    substitution `gpOf alloc` computes the source denotation `armTarget.denote p` at
    the allocated names. This is `regToBOp_alloc_denote` discharged for the real
    `GpAlloc` the AArch64 encoder uses — the `<UNALLOCATED>` sentinel is a proof
    obligation (`allocValidOn`), not a trusted runtime check. -/
theorem regToBOp_concreteAlloc_denote (alloc : GpAlloc) (p : RegProg)
    (hvalid : allocValidOn alloc (lowerBBlock (regToBOp p))) (s t : BState)
    (h : ReindexedOn ("xzr" :: bBlockNames (lowerBBlock (regToBOp p))) (gpOf alloc) s t) :
    ReindexedOn ("xzr" :: bBlockNames (lowerBBlock (regToBOp p))) (gpOf alloc)
      (armTarget.denote p s)
      (runBBlock t (renameBBlock (gpOf alloc) (lowerBBlock (regToBOp p)))) :=
  regToBOp_alloc_denote_on _ (gpOf alloc) hvalid (gpOf_xzr alloc)
    (List.mem_cons_self ..) p (fun _ hn => List.mem_cons_of_mem _ hn) s t h

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmBInstRegAlloc
