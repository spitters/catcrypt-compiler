/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight

@[expose] public section

set_option autoImplicit false

/-!
# Array versions of a straight chain coalesced into in-place stores

A straight chain of typed memory instructions in SSA form writes every array store
(`STOREIDX`) to a fresh array name: the store `d := b[i ↦ v]` reads the array `b` and
writes the updated copy to `d`. For a renaming `σ` of array names, the coalesced chain
`is.map (renRM σ)` writes `σ d` from `σ b`; when `σ` sends the versions `b` and `d` of one
array to the same name, the store updates that name in place.

The coalescing is sound when no array version is read after a later version with the same
image under `σ` is written. `coalesceB σ is obs` decides this for the chain `is` and the
names `obs` read after it: `σ` fixes every register name of the chain; no instruction
reads or writes the compile-time-offset word memory; and for every store writing `d`,
every array name `r ≠ d` read later (`liveArr`) has `σ r ≠ σ d`.

## Main definitions

* `arrReads`, `liveArr`: the array names an instruction reads, and the array names read by
  a chain and after it.
* `coStepB`, `coalesceB`: the check of one instruction and of a chain.
* `CoRel`: two states with equal registers, word memory and flags, whose arrays agree
  through `σ` on a list of names.

## Main results

* `renLinstrR_of_fix`: a renaming that fixes every name of an instruction leaves it
  unchanged.
* `lsemStepMem_coalesce`: one step of an instruction accepted by `coStepB` is matched by a
  step of its renamed form.
* `lsemStraightMem_coalesce`: a run of a chain accepted by `coalesceB` is matched by a run
  of the coalesced chain into a state related on the names read after the chain.
* `straight_chain_abi_arr`: the chain of an array-returning program in the fragment
  `arrMemNB`, run from an ABI entry, halts with the program's denotation at its return
  name.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (lsemStepCast)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renOperand renLinstrR renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames
  loadStruct?_ren storeStruct?_ren)

/-! ## 1. The check -/

/-- The array names an instruction reads: the base of a runtime-indexed load or store. -/
def arrReads (i : LinstrRM) : List String :=
  match i.2 with
  | .load _ _ => match loadStruct? i.1 with
    | some (_, b, _) => [b]
    | none => []
  | .store _ _ => match storeStruct? i.1 with
    | some (_, b, _, _) => [b]
    | none => []
  | _ => []

/-- The array name an instruction writes: the destination of a runtime-indexed store. -/
def arrWrite (i : LinstrRM) : Option String :=
  match i.2 with
  | .store _ _ => (storeStruct? i.1).map (·.1)
  | _ => none

/-- The array names live before the chain `is` when the names `obs` are read after it:
    the names read by an instruction, and the names live after it other than the name it
    writes. -/
def liveArr : List LinstrRM → List String → List String
  | [], obs => obs
  | i :: is, obs => arrReads i ++ (liveArr is obs).filter fun r => some r != arrWrite i

/-- `σ` fixes every name of the instruction `i`. -/
def fixB (σ : String → String) (i : LinstrR) : Bool := (instrNames i).all fun n => σ n == n

/-- **The check of one instruction** followed by reads of the array names `after`: a load
    whose destination and index `σ` fixes; a store whose index and value `σ` fixes and
    whose destination `d` has an image under `σ` that no later-read name `r ≠ d` shares;
    a register instruction whose names `σ` fixes; never a compile-time-offset memory
    access. -/
def coStepB (σ : String → String) (i : LinstrRM) (after : List String) : Bool :=
  match i.2 with
  | .load _ _ => match loadStruct? i.1 with
    | some (d, _, x) => σ d == d && σ x == x
    | none => fixB σ i.1
  | .store _ _ => match storeStruct? i.1 with
    | some (d, _, x, v) => σ x == x && σ v == v && after.all fun r => r == d || σ r != σ d
    | none => fixB σ i.1
  | .reg _ => fixB σ i.1
  | .loadC | .storeC => false

/-- **The coalescing check** of the chain `is` with the names `obs` read after it. -/
def coalesceB (σ : String → String) : List LinstrRM → List String → Bool
  | [], _ => true
  | i :: is, obs => coStepB σ i (liveArr is obs) && coalesceB σ is obs

/-! ## 2. The relation and the step -/

/-- Two states with equal registers, word memory and flags, whose arrays agree through `σ`
    on the names `L`: the array `σ r` of `s'` is the array `r` of `s`. -/
structure CoRel (σ : String → String) (L : List String) (s s' : LstateM) : Prop where
  /-- The registers. -/
  reg : s'.reg = s.reg
  /-- The word memory. -/
  mem : s'.lmem = s.lmem
  /-- The carry flag. -/
  cf : s'.cf = s.cf
  /-- The overflow flag. -/
  of : s'.of = s.of
  /-- The arrays on `L`. -/
  arr : ∀ r ∈ L, s'.larr (σ r) = s.larr r

theorem CoRel.mono {σ : String → String} {L L' : List String} {s s' : LstateM}
    (h : CoRel σ L s s') (hL : ∀ r ∈ L', r ∈ L) : CoRel σ L' s s' :=
  ⟨h.reg, h.mem, h.cf, h.of, fun r hr => h.arr r (hL r hr)⟩

theorem CoRel.getArr {σ : String → String} {L : List String} {s s' : LstateM}
    (h : CoRel σ L s s') {r : String} (hr : r ∈ L) (w n : Nat) :
    s'.getArr (σ r) w n = s.getArr r w n := by
  unfold LstateM.getArr
  rw [h.arr r hr]

theorem renOperand_of_fix (σ : String → String) (o : LOperand)
    (h : ∀ n ∈ opNames o, σ n = n) : renOperand σ o = o := by
  cases o <;> simp_all [renOperand, opNames]

theorem renLinstrR_of_fix (σ : String → String) (i : LinstrR)
    (h : ∀ n ∈ instrNames i, σ n = n) : renLinstrR σ i = i := by
  cases i with
  | Lopn d o s =>
      simp only [instrNames, List.flatMap_append, List.mem_append, List.mem_flatMap] at h
      simp only [renLinstrR, LinstrR.Lopn.injEq, true_and]
      refine ⟨(List.map_congr_left fun x hx => ?_).trans (List.map_id d),
        (List.map_congr_left fun x hx => ?_).trans (List.map_id s)⟩
      · exact renOperand_of_fix σ x fun n hn => h n (Or.inl ⟨x, hx, hn⟩)
      · exact renOperand_of_fix σ x fun n hn => h n (Or.inr ⟨x, hx, hn⟩)
  | _ => rfl

theorem fixB_spec {σ : String → String} {i : LinstrR} (h : fixB σ i = true) :
    renLinstrR σ i = i :=
  renLinstrR_of_fix σ i fun n hn => by
    simpa using (List.all_eq_true.mp h) n hn

/-- **One step of a coalesced instruction.** For an instruction accepted by `coStepB`
    with the later reads `after`, a step from `s` is matched by a step of the renamed
    instruction from a state related on the instruction's reads and the names of `after`
    it does not write, into a state related on `after`. -/
theorem lsemStepMem_coalesce {σ : String → String} {i : LinstrRM} {after : List String}
    (hc : coStepB σ i after = true) {s s' t : LstateM}
    (hR : CoRel σ (arrReads i ++ after.filter fun r => some r != arrWrite i) s s')
    (h : lsemStepMem i s = some t) :
    ∃ t', lsemStepMem (renRM σ i) s' = some t' ∧ CoRel σ after t t' := by
  obtain ⟨wire, tag⟩ := i
  have hnone : arrWrite (wire, tag) = none → CoRel σ after s s' := fun hw =>
    hR.mono fun r hr => List.mem_append_right _ (List.mem_filter.mpr ⟨hr, by rw [hw]; simp⟩)
  have hcast : arrWrite (wire, tag) = none → ∀ (cd : Option Nat), renLinstrR σ wire = wire →
      (lsemStepCast (wire, cd) s.reg).map (fun r => { s with reg := r }) = some t →
      ∃ t', (lsemStepCast (renLinstrR σ wire, cd) s'.reg).map
          (fun r => { s' with reg := r }) = some t' ∧ CoRel σ after t t' := by
    intro hw cd hwire h
    have hA := hnone hw
    rw [hwire, hR.reg]
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨{ s' with reg := r }, by rw [hr]; rfl, ⟨rfl, hA.mem, hA.cf, hA.of, hA.arr⟩⟩
  cases tag with
  | reg cd => exact hcast rfl cd (fixB_spec hc) h
  | load w n =>
      simp only [coStepB] at hc
      unfold lsemStepMem at h ⊢
      simp only [renRM] at h ⊢
      rw [loadStruct?_ren]
      cases hl : loadStruct? wire with
      | none =>
          rw [hl] at hc h
          exact hcast rfl none (fixB_spec hc) h
      | some p =>
          obtain ⟨d, b, x⟩ := p
          rw [hl] at hc h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          have hA := hnone rfl
          have hb : b ∈ arrReads (wire, .load w n)
              ++ after.filter fun r => some r != arrWrite (wire, .load w n) := by
            simp [arrReads, hl]
          simp only [Option.map_some, hc.1, hc.2, hR.getArr hb, hR.reg] at h ⊢
          cases ha : s.getArr b w n with
          | none => simp [ha] at h
          | some arr =>
            cases hi : s.reg.getW x 64 with
            | none => simp [ha, hi] at h
            | some vi =>
              simp only [ha, hi, Option.some.injEq] at h
              subst h
              refine ⟨_, rfl, ⟨?_, hA.mem, hA.cf, hA.of, hA.arr⟩⟩
              simp only [LstateM.nextPc, LstateM.setReg, hR.reg]
  | store w n =>
      simp only [coStepB] at hc
      unfold lsemStepMem at h ⊢
      simp only [renRM] at h ⊢
      rw [storeStruct?_ren]
      cases hl : storeStruct? wire with
      | none =>
          rw [hl] at hc h
          exact hcast (by simp [arrWrite, hl]) none (fixB_spec hc) h
      | some p =>
          obtain ⟨d, b, x, v⟩ := p
          rw [hl] at hc h
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
            bne_iff_ne, ne_eq] at hc
          obtain ⟨⟨hx, hv⟩, hd⟩ := hc
          have hb : b ∈ arrReads (wire, .store w n)
              ++ after.filter fun r => some r != arrWrite (wire, .store w n) := by
            simp [arrReads, hl]
          simp only [Option.map_some, hx, hv, hR.getArr hb, hR.reg] at h ⊢
          cases ha : s.getArr b w n with
          | none => simp [ha] at h
          | some arr =>
            cases hi : s.reg.getW x 64 with
            | none => simp [ha, hi] at h
            | some vi =>
              cases hvv : s.reg.getW v w with
              | none => simp [ha, hi, hvv] at h
              | some vv =>
                simp only [ha, hi, hvv, Option.some.injEq] at h
                subst h
                refine ⟨_, rfl, ⟨?_, hR.mem, hR.cf, hR.of, fun r hr => ?_⟩⟩
                · simp only [LstateM.nextPc, LstateM.setArr, hR.reg]
                · simp only [LstateM.nextPc, LstateM.setArr]
                  by_cases hrd : r = d
                  · subst hrd
                    simp
                  · have hne : σ r ≠ σ d := by
                      rcases hd r hr with h' | h'
                      · exact absurd h' hrd
                      · exact h'
                    simp only [hne, hrd, if_false]
                    exact hR.arr r (List.mem_append_right _
                      (List.mem_filter.mpr ⟨hr, by simp [arrWrite, hl, hrd]⟩))
  | loadC => simp [coStepB] at hc
  | storeC => simp [coStepB] at hc

/-! ## 3. The chain -/

/-- **The coalesced chain.** For a chain `is` accepted by `coalesceB σ is obs`, a run of
    `is` from `s` is matched by a run of the coalesced chain `is.map (renRM σ)` from a state
    related to `s` on the array names `liveArr is obs`, into a state related to the final
    state on `obs`. -/
theorem lsemStraightMem_coalesce {σ : String → String} :
    ∀ (is : List LinstrRM) (obs : List String), coalesceB σ is obs = true →
      ∀ {s s' t : LstateM}, CoRel σ (liveArr is obs) s s' → lsemStraightMem is s = some t →
        ∃ t', lsemStraightMem (is.map (renRM σ)) s' = some t' ∧ CoRel σ obs t t'
  | [], _, _, s, s', t, hR, h => by
      cases h
      exact ⟨s', rfl, hR⟩
  | i :: is, obs, hc, s, s', t, hR, h => by
      simp only [coalesceB, Bool.and_eq_true] at hc
      rw [lsemStraightMem_cons] at h
      cases hs : lsemStepMem i s with
      | none => simp [hs] at h
      | some s₁ =>
          rw [hs] at h
          obtain ⟨s₁', h₁, hR₁⟩ := lsemStepMem_coalesce hc.1 hR hs
          obtain ⟨t', h', hRt⟩ := lsemStraightMem_coalesce is obs hc.2 hR₁ h
          refine ⟨t', ?_, hRt⟩
          rw [List.map_cons, lsemStraightMem_cons, h₁]
          exact h'

/-! ## 4. The chain of an array-returning program from the ABI entry -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
  (arrMemN_straightOpsMem_plain)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (arrMemNB arrMemNB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf AbiEntryM
  storeAgreesM_of_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight (lsemFuelMemF_plain_halts)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- **The chain of an array-returning program realises it.** For a program returning a
    word array that passes `arrMemNB`, every valuation `V` a layout `σ` reads off an entry
    state `sa` (`AbiValOf`) and every flag-machine state `b0` that is the ABI entry of `sa`
    (`AbiEntryM`), the chain `straightOpsMem` run by `lsemFuelMemF` from `b0` halts, and
    the array at its return name `comRetReg` is the program's denotation at `V`. The
    array analogue of `ExportCertStraight.straight_chain_abi`. -/
theorem straight_chain_abi_arr {Γ : Ctxt jasminDialect} {w m : Nat}
    (com : Com jasminDialect Γ (.stackArr w m)) (hmem : arrMemNB com = true) :
    ∀ (σ : AbiLayout) (sa : AState) (V : Ctxt.Valuation Γ) (fn : String) (b0 : LstateM)
      (zf : Bool), AbiValOf σ sa V → AbiEntryM σ sa b0 →
      ∃ (k : Nat) (t : LstateMF),
        lsemFuelMemF (singletonProgM fn (straightOpsMem Γ.length com Γ.length)) k
            { prog := { base := b0, lfn := fn }, zf := zf } = some t
          ∧ t.prog.base.getArr (comRetReg Γ.length argName com Γ.length) w m
              = some (com.denote V) := by
  intro σ sa V fn b0 zf hV hb
  have hm := arrMemNB_sound com hmem
  obtain ⟨b, hrun, -, harr⟩ := hm.straightOps_full rfl le_rfl (storeAgreesM_of_abi hV hb)
  obtain ⟨c, o, hh⟩ := lsemFuelMemF_plain_halts fn _
    (arrMemN_straightOpsMem_plain hm _ _) b0 b zf hb.pc hrun
  exact ⟨_, _, hh, harr⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
