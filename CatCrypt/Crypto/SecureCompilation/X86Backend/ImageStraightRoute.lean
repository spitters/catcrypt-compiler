/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute

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
* `straightRouteB`, `straight_image_bytes`: the checks of `ImageAddrRoute.routeB` without
  the loop, the renaming and the fusion, on the virtual body `argBind ++ C` of a straight
  chain `C`; a run of `C` is matched by a halting run of the decoded bytes of the printed
  body, with each slot's array in memory at its entry base.
* `chainAlias`, `straightArrB`, `straight_arr_bytes`: the coalescing renaming of a chain
  (the export's alias map `arrChainAlias`), the gate of an array-returning straight-line
  program, and its correctness at the bytes: from every separated entry state, the decoded
  bytes of the printed body halt in a state from which the layout reads back the words of
  the program's denotation.
* `straightRouteOutB`, `straight_image_reg_bytes`: the checks of `straightRouteB` with
  observed registers, and the value of an observed general-purpose register at the end of
  the decoded bytes.
* `straightRegB`, `straight_reg_bytes`: the gate of a straight-line program returning a
  `64`-bit register (its chain followed by the copy of its return name into the export
  register of the result) and its correctness at the bytes: from every separated entry
  state, the decoded bytes of the printed body halt in a state from which the layout reads
  back the program's denotation in the result register.

The coalesced chain is `chain.map (renRM ρ)` with `ρ = chainAlias chain`; the physical-ABI
export applies the same alias map (`canonicalizeMemrefThread`) to its virtual body, so the
stores of the printed body write the output parameter in place, and `ownedCheckMC` relates
the coalesced chain to the printed body.
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

/-! ## 5. A straight chain through the image of the printed body -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_lpc lsemFuelMemF_segF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (argBind slotArrOf slotRen
  entryA entryV entryB entryB_spec argBind_entryV boundFacts_entryV imgRel_entryV
  imgSep_slotRen frameE)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameNames frameMark
  frameOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (imgGateB cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiBase abiReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (read64)

/-- **A chain of `Lopn`s halts on the flag machine** in the state its straight-line run
    reaches, from program counter `0`. -/
theorem lsemFuelMemF_of_runStraightF (fn : String) (seg : List LinstrRM)
    (hl : ∀ i ∈ seg, IsLopn i) (b0 b : LstateM) (zf z : Bool) (hpc : b0.lpc = 0)
    (hrun : runStraightF seg b0 zf = some (b, z)) :
    lsemFuelMemF (singletonProgM fn seg) seg.length
        { prog := { base := b0, lfn := fn }, zf := zf }
      = some { prog := { base := b, lfn := fn }, zf := z } := by
  have hseg := lsemFuelMemF_segF (singletonProgM fn seg) fn rfl seg b0 zf 0 hl
    (fun k _ => by rw [hpc, Nat.zero_add]; rfl)
  rw [Nat.add_zero] at hseg
  rw [hseg, hrun, Option.bind_some]
  have hlpc : b.lpc = seg.length := by
    rw [runStraightF_lpc seg b0 zf b z hrun, hpc, Nat.zero_add]
  unfold lsemFuelMemF
  simp only [JasminLsemMemLoop.findInstrMem, singletonProgM, if_true]
  rw [hlpc, List.getElem?_eq_none (le_refl _)]

/-- The state `entryV` at the frame map of the printed body `body` and the identity name
    map, after the copies of the parameter registers: its program counter is the number of
    parameters. -/
def afterArgs (σ : AbiLayout) (body : Lcmd) (sa : AState) : LstateM :=
  let b0 := entryV σ (frameE body sa) sa fun x => x
  { b0 with reg := { b0.reg with lpc := σ.args.length } }

/-- **The check of the straight image route** of the chain `C` against the printed body
    `body`: with the virtual body `argBind σ nm ++ C` and the slot map `slotArrOf σ nm`
    (array names unrenamed), the register allocation check `ownedCheckMC` of the virtual
    body against the image of the printed body, the bounds invariant of the virtual body,
    the printed body in the covered class and the image class, the gate of the image
    simulation, the frame check and the entry check. The conjuncts are those of
    `ImageAddrRoute.routeB` without the loop, the renaming and the fusion. -/
def straightRouteB (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (C : List LinstrRM) : Bool :=
  let B := argBind σ nm ++ C
  let sl := slotRen (slotArrOf σ nm) fun x => x
  ownedCheckMC [] B (virtImg sl body)
    && idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B
    && printedAddrB body && physImgB sl body
    && imgGateB (frameMark (frameNames body)) sl body
    && frameOkB σ body && entryB σ nm body

/-- **A straight chain on the decoded bytes through the image route.** Let the printed body
    `body` and the chain `C` of `Lopn`s pass `straightRouteB`, and let `A` be the array of
    `n` words of the slot `q`. From every machine state `sa` satisfying `σ.Regions`, a run
    of `C` from the state `afterArgs` to `b` is matched by a halting run of the decoded bytes
    of the printed body from `sa`, at the end of which the words at the entry base of `A`
    are the array `A` of `b`. -/
theorem straight_image_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {C : List LinstrRM} (hg : straightRouteB σ nm body C = true) (hC : ∀ i ∈ C, IsLopn i)
    {q A : String} {n : Nat} (hq : slotArrOf σ nm q = some (A, n)) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) (b : LstateM) (z : Bool)
    (hrun : runStraightF C (afterArgs σ body sa) false = some (b, z)) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr, b.getArr A 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j)
          = arr ⟨j, hj⟩ := by
  simp only [straightRouteB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨hck, hidx⟩, hpr⟩, hphys⟩, hgate⟩, hfr⟩, hent⟩ := hg
  have E := entryB_spec hent sa
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (fr := frameE body sa)
    (un := fun x => x) E.argF E.argG E.regs false
  have hB : runStraightF (argBind σ nm ++ C) (entryV σ (frameE body sa) sa fun x => x) false
      = some (b, z) := by
    rw [JasminLsemAddrMem.runStraightF_append, hpr0, Option.bind_some]
    exact hrun
  have hl : ∀ i ∈ argBind σ nm ++ C, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
    · exact hC i hi
  have hrun' := lsemFuelMemF_of_runStraightF fn _ hl _ b false z rfl hB
  have hents := boundFacts_entryV (nm := nm) (fr := frameE body sa) (un := fun x => x)
    hreg E.bnds
  have hok := runIdxOk_of_idxInvCheckB hidx fn _ _ rfl rfl hents _ hrun'
  have hgate' : imgGateB (frameE body sa) (slotRen (slotArrOf σ nm) fun x => x) body
      = true := by
    rw [ImageAddrFrame.imgGateB_frameMark]
    exact hgate
  have hsep := imgSep_slotRen (ren := fun x => x) (un := fun x => x)
    (ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot) fun _ _ _ _ => rfl
  obtain ⟨prog, sa', hdec, hh, -, hcells⟩ := ImageAddrFrame.virt_bytes hck hpr hphys hgate'
    hsep fn _ _ rfl rfl (entryA σ sa) false (imgRel_entryV (fun a ha =>
      ⟨(E.regs a ha).1, (E.regs a ha).2.1⟩) fun _ _ => rfl) rfl (fun R hR => by
        have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (DecodePrinted.phys R)⟩ := by
          simp only [entryA, hR, if_true]
        unfold JasminLsemWidthN.LstateN.getW
        rw [hl]
        simp) rfl _ hrun' hok
  obtain ⟨arr, h1, h2⟩ := hcells q A n (by simp [slotRen, hq])
  exact ⟨prog, sa', hdec, hh, arr, h1, h2⟩

/-! ## 6. An array-returning program at the bytes -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (arrChainAlias canonMemrefName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (PlainLopnBody cmpArgs?
  movRegArgs?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn
  runStraightF_of_lsemStraightMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryV_abiEntry resultOf_words)

/-- The coalescing renaming of a chain: the alias map `arrChainAlias` of the physical-ABI
    export, which sends the destination of every store to the root of its base. -/
def chainAlias (is : List LinstrRM) : String → String :=
  canonMemrefName (arrChainAlias (is.map fun i => ⟨0, i.1⟩))

/-- A decision of `PlainLopnBody`. -/
def plainB (is : List LinstrRM) : Bool :=
  is.all fun i => isLopnB i && (cmpArgs? i).isNone && (movRegArgs? i).isNone

theorem plainB_sound {is : List LinstrRM} (h : plainB is = true) : PlainLopnBody is := by
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact ⟨isLopnB_isLopn this.1.1, this.1.2, this.2⟩

/-- **The gate of an array-returning straight-line program.** For a program returning a
    word array of `m` words: the fragment `arrMemNB`; with its chain `straightOpsMem`, its
    return name `ret` and the coalescing renaming `ρ := chainAlias` of the chain, the
    coalescing check `coalesceB ρ chain [ret]`, `ρ` fixing every array name live at the
    entry, the coalesced chain plain; the result of `σ` the `m` words at the register `RA`
    of the parameter `ρ ret`, whose slot holds the array `ρ ret`; and the straight image
    route `straightRouteB` of the coalesced chain against the printed body `body`. -/
def straightArrB (σ : AbiLayout) (nm : String → String) (body : Lcmd) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | Γ, .stackArr 64 m, com =>
      let ch := straightOpsMem Γ.length com Γ.length
      let ret := comRetReg Γ.length argName com Γ.length
      let ρ := chainAlias ch
      let C := ch.map (renRM ρ)
      arrMemNB com && coalesceB ρ ch [ret] && (liveArr ch [ret]).all (fun r => ρ r == r)
        && plainB C
        && (match σ.result with
          | .words RA k => k == m && abiReg σ (ρ ret) == some RA
              && slotArrOf σ nm (slotOfReg (nm RA)) == some (ρ ret, m)
          | _ => false)
        && straightRouteB σ nm body C
  | _, _, _ => false

/-- A program accepted by `straightArrB` returns a word array. -/
theorem straightArrB_ty {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {c : Com jasminDialect Γ t}
    (h : straightArrB σ nm body c = true) : ∃ m, t = .stackArr 64 m := by
  unfold straightArrB at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

theorem storeAgreesM_lpc {nArgs d : Nat} {Γ : Ctxt jasminDialect} {V : Ctxt.Valuation Γ}
    {s : LstateM} (k : Nat) (h : StoreAgreesM nArgs d s V) :
    StoreAgreesM nArgs d { s with reg := { s.reg with lpc := k } } V :=
  ⟨fun v => h.1 v, fun v => h.2 v⟩

/-- **An array-returning straight-line program at the bytes.** For a program returning a
    word array of `m` words that passes `straightArrB` against the printed body `body`:
    from every entry state `sa` satisfying `σ.Regions`, at every valuation `V` the layout
    reads off `sa` (`AbiValOf`), the decoded bytes of `body` halt in a state from which `σ`
    reads back the words of the program's denotation. -/
theorem straight_arr_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {m : Nat} (com : Com jasminDialect Γ (.stackArr 64 m))
    (hg : straightArrB σ nm body com = true) (sa : AState) (V : Ctxt.Valuation Γ)
    (hV : AbiValOf σ sa V) (hreg : σ.Regions sa) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (.array ((List.range m).map fun j =>
          .int (stackGet (com.denote V) j).toNat)) := by
  simp only [straightArrB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨hmem, hco⟩, hfix⟩, hpl⟩, hres⟩, hroute⟩ := hg
  have hroute' := hroute
  simp only [straightRouteB, Bool.and_eq_true] at hroute'
  have E := entryB_spec hroute'.2 sa
  have habi := entryV_abiEntry (un := fun x => x) (sa := sa) E.argF E.argG fun _ _ => rfl
  have hagr := storeAgreesM_lpc σ.args.length (storeAgreesM_of_abi hV habi)
  obtain ⟨b, hrun, -, harr⟩ :=
    (arrMemNB_sound com hmem).straightOps_full rfl le_rfl hagr
  set ch := straightOpsMem Γ.length com Γ.length with hch
  set ret := comRetReg Γ.length argName com Γ.length with hret
  set ρ := chainAlias ch with hρ
  have hR0 : CoRel ρ (liveArr ch [ret]) (afterArgs σ body sa) (afterArgs σ body sa) :=
    ⟨rfl, rfl, rfl, rfl, fun r hr => by
      rw [show ρ r = r from by simpa using (List.all_eq_true.mp hfix) r hr]⟩
  obtain ⟨b', hrun', hR⟩ := lsemStraightMem_coalesce ch [ret] hco hR0 hrun
  obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem _ (plainB_sound hpl) _ b' false hrun'
  have hC : ∀ i ∈ ch.map (renRM ρ), IsLopn i := fun i hi => (plainB_sound hpl i hi).1
  split at hres
  · rename_i RA k hσ
    simp only [Bool.and_eq_true, beq_iff_eq] at hres
    obtain ⟨⟨hk, hA⟩, hslot⟩ := hres
    subst hk
    obtain ⟨prog, sa', hdec, hh, arr, h1, h2⟩ :=
      straight_image_bytes hroute hC hslot sa hreg "" _ _ hF
    refine ⟨prog, sa', hdec, hh, ?_⟩
    have he : arr = com.denote V := by
      have h3 : ({ b' with cf := c, of := o } : LstateM).getArr (ρ ret) 64 k
          = b.getArr ret 64 k := by
        unfold LstateM.getArr
        rw [show ({ b' with cf := c, of := o } : LstateM).larr (ρ ret) = b.larr ret from
          hR.arr ret (List.mem_singleton_self _)]
      rw [h1, harr] at h3
      exact Option.some.inj h3
    have hb : abiBase (abiReg σ) sa (ρ ret) = sa.regs RA := by
      simp [abiBase, hA]
    rw [hb] at h2
    have hR' := resultOf_words (σ := σ) (sa' := sa') hσ h2
    rw [he] at hR'
    exact hR'
  · cases hres

/-! ## 7. A register-returning program at the bytes -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (scalarMemNB scalarMemNB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (frameE_none)

/-- **The check of the straight image route with observed registers** `outs`: the conjuncts
    of `straightRouteB` with the register allocation check `ownedCheckMC outs`, which
    relates the values of the registers `outs` at the end of the virtual body and of the
    image. -/
def straightRouteOutB (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (outs : List String) (C : List LinstrRM) : Bool :=
  let B := argBind σ nm ++ C
  let sl := slotRen (slotArrOf σ nm) fun x => x
  ownedCheckMC outs B (virtImg sl body)
    && idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B
    && printedAddrB body && physImgB sl body
    && imgGateB (frameMark (frameNames body)) sl body
    && frameOkB σ body && entryB σ nm body

theorem getW_congr {s s' : JasminLsemWidthN.LstateN} {r : String} (w : Nat)
    (h : s.lvm r = s'.lvm r) : s.getW r w = s'.getW r w := by
  unfold JasminLsemWidthN.LstateN.getW
  rw [h]

/-- The copy of `x` into `y` leaves at `y` the tagged value of `x`. -/
theorem movesState_single_lvm (s : LstateM) (x y : String) :
    (JasminLsemRenameLoop.movesState [(x, y)] s).reg.lvm y = s.reg.lvm x := by
  simp [JasminLsemRenameLoop.movesState, LstateM.setReg, LstateM.nextPc,
    JasminLsemWidthN.LstateN.nextPc, JasminLsemWidthN.LstateN.setReg]

/-- **A straight chain on the decoded bytes through the image route, at a register.** Let
    the printed body `body` and the chain `C` of `Lopn`s pass `straightRouteOutB` with the
    observed register `R`, a general-purpose register with no frame slot. From every machine
    state `sa` satisfying `σ.Regions`, a run of `C` from the state `afterArgs` to `b` is
    matched by a halting run of the decoded bytes of the printed body from `sa`, at the end
    of which the machine register of `R` holds the value of `R` in `b`. -/
theorem straight_image_reg_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {C : List LinstrRM} {R : String} (hg : straightRouteOutB σ nm body [R] C = true)
    (hC : ∀ i ∈ C, IsLopn i) (hR : gpOk R = true)
    (hfR : (frameMark (frameNames body) R).isNone = true) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) (b : LstateM) (z : Bool)
    (hrun : runStraightF C (afterArgs σ body sa) false = some (b, z)) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ b.reg.getW R 64 = some (sa'.regs (phys R)) := by
  simp only [straightRouteOutB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨hck, hidx⟩, hpr⟩, hphys⟩, hgate⟩, hfr⟩, hent⟩ := hg
  have E := entryB_spec hent sa
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (fr := frameE body sa)
    (un := fun x => x) E.argF E.argG E.regs false
  have hB : runStraightF (argBind σ nm ++ C) (entryV σ (frameE body sa) sa fun x => x) false
      = some (b, z) := by
    rw [JasminLsemAddrMem.runStraightF_append, hpr0, Option.bind_some]
    exact hrun
  have hl : ∀ i ∈ argBind σ nm ++ C, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
    · exact hC i hi
  have hrun' := lsemFuelMemF_of_runStraightF fn _ hl _ b false z rfl hB
  have hents := boundFacts_entryV (nm := nm) (fr := frameE body sa) (un := fun x => x)
    hreg E.bnds
  have hok := runIdxOk_of_idxInvCheckB hidx fn _ _ rfl rfl hents _ hrun'
  have hgate' : imgGateB (frameE body sa) (slotRen (slotArrOf σ nm) fun x => x) body
      = true := by
    rw [ImageAddrFrame.imgGateB_frameMark]
    exact hgate
  have hsep := imgSep_slotRen (ren := fun x => x) (un := fun x => x)
    (ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot) fun _ _ _ _ => rfl
  have hck' := JasminLsemMemChecked.lsemFuelMemFk_of_runIdxOk true _ _ _ _ hrun' hok
  obtain ⟨f', t', hr', hobs⟩ := OwnedLprogTVChecked.ownedCheckMC_sound hck fn _ _ rfl rfl _ hck'
  obtain ⟨fuel', s', zf', hrA, hrel', hsafe⟩ :=
    ImageAddrSim.image_addr_sim hsep hphys hgate' fn f' _ t' (entryA σ sa) false rfl
      (imgRel_entryV (fun a ha => ⟨(E.regs a ha).1, (E.regs a ha).2.1⟩) fun _ _ => rfl) hr'
  rw [ImageAddrFrame.runA_frameIn] at hrA
  rw [ImageAddrFrame.runSafe_frameIn] at hsafe
  obtain ⟨prog, sa', hdec, hh, -, hregs, -⟩ :=
    DecodePrintedCFG.printedAddr_sim body hpr sa (entryA σ sa) false rfl (fun R hR => by
        have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (phys R)⟩ := by
          simp only [entryA, hR, if_true]
        unfold JasminLsemWidthN.LstateN.getW
        rw [hl]
        simp) rfl fuel' (s', zf') hrA hsafe
  refine ⟨prog, sa', hdec, hh, ?_⟩
  have h1 : t'.prog.base.reg.lvm R = b.reg.lvm R := hobs.1 R (List.mem_singleton_self _)
  have h2 : t'.prog.base.reg.lvm R = s'.reg.lvm R := hrel'.regs R (frameE_none sa hfR)
  rw [← hregs R hR]
  exact getW_congr 64 (h1.symm.trans h2)

/-- **The gate of a register-returning straight-line program.** For a program returning a
    `64`-bit register: the stack-memory fragment `scalarMemNB`; the result of `σ` the
    register `RA`, whose export name `nm RA` is a general-purpose register with machine
    register `RA` and no frame slot; and the straight image route `straightRouteOutB`,
    observing `nm RA`, of the chain `straightOpsMem` followed by the copy of its return name
    into `nm RA`, against the printed body `body`. -/
def straightRegB (σ : AbiLayout) (nm : String → String) (body : Lcmd) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | Γ, .reg w, com =>
      let ch := straightOpsMem Γ.length com Γ.length
      let ret := comRetReg Γ.length argName com Γ.length
      scalarMemNB com && w == 64
        && (match σ.result with
          | .reg RA => gpOk (nm RA) && phys (nm RA) == RA
              && (frameMark (frameNames body) (nm RA)).isNone
              && straightRouteOutB σ nm body [nm RA]
                (ch ++ JasminLsemRenameLoop.movesOf [(ret, nm RA)])
          | _ => false)
  | _, _, _ => false

/-- A program accepted by `straightRegB` returns a `64`-bit register. -/
theorem straightRegB_ty {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {c : Com jasminDialect Γ t}
    (h : straightRegB σ nm body c = true) : t = .reg 64 := by
  unfold straightRegB at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.2]
  · cases h

/-- **A register-returning straight-line program at the bytes.** For a program returning a
    `64`-bit register that passes `straightRegB` against the printed body `body`: from every
    entry state `sa` satisfying `σ.Regions`, at every valuation `V` the layout reads off `sa`
    (`AbiValOf`), the decoded bytes of `body` halt in a state from which `σ` reads back the
    program's denotation. -/
theorem straight_reg_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} (com : Com jasminDialect Γ (.reg 64))
    (hg : straightRegB σ nm body com = true) (sa : AState) (V : Ctxt.Valuation Γ)
    (hV : AbiValOf σ sa V) (hreg : σ.Regions sa) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (.int (com.denote V).toNat) := by
  simp only [straightRegB, Bool.and_eq_true] at hg
  obtain ⟨⟨hmem, -⟩, hres⟩ := hg
  split at hres
  · rename_i RA hσ
    simp only [Bool.and_eq_true, beq_iff_eq] at hres
    obtain ⟨⟨⟨hgp, hph⟩, hfr⟩, hroute⟩ := hres
    have hroute' := hroute
    simp only [straightRouteOutB, Bool.and_eq_true] at hroute'
    have E := entryB_spec hroute'.2 sa
    have habi := entryV_abiEntry (un := fun x => x) (sa := sa) E.argF E.argG fun _ _ => rfl
    have hagr := storeAgreesM_lpc σ.args.length (storeAgreesM_of_abi hV habi)
    have hm := scalarMemNB_sound com hmem
    obtain ⟨b, hrun, -, -, hval⟩ := lsemStraightMem_straightOps_full hm rfl rfl le_rfl hagr
    have hpl := JasminLsemMemFlagArrLoop.straightOpsMem_plain Γ.length com
      (JasminLsemMemFlagArrLoop.scalarMemN_comOpsPlain hm) Γ.length
    obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem _ hpl _ b false hrun
    set ret := comRetReg Γ.length argName com Γ.length with hret
    have hF2 : runStraightF (straightOpsMem Γ.length com Γ.length
          ++ JasminLsemRenameLoop.movesOf [(ret, nm RA)]) (afterArgs σ body sa) false
        = some (JasminLsemRenameLoop.movesState [(ret, nm RA)] { b with cf := c, of := o },
          false) := by
      have hF' : runStraightF (straightOpsMem Γ.length com Γ.length) (afterArgs σ body sa) false
          = some ({ b with cf := c, of := o }, false) := hF
      rw [JasminLsemAddrMem.runStraightF_append, hF', Option.bind_some]
      exact JasminLsemRenameLoop.runStraightF_movesOf _ _ _
    have hC : ∀ i ∈ straightOpsMem Γ.length com Γ.length
        ++ JasminLsemRenameLoop.movesOf [(ret, nm RA)], IsLopn i := by
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact (hpl i hi).1
      · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
    obtain ⟨prog, sa', hdec, hh, hR⟩ := straight_image_reg_bytes hroute hC hgp hfr sa hreg "" _ _ hF2
    refine ⟨prog, sa', hdec, hh, ?_⟩
    have h0 : b.reg.getW ret 64 = some (com.denote V) := by
      simpa only [JasminLsemWidthN.evalOperandN] using hval
    have hv : (JasminLsemRenameLoop.movesState [(ret, nm RA)]
        { b with cf := c, of := o }).reg.getW (nm RA) 64 = some (com.denote V) := by
      rw [← h0]
      unfold JasminLsemWidthN.LstateN.getW
      rw [movesState_single_lvm]
    rw [hv, hph] at hR
    have hx := Option.some.inj hR
    unfold AbiLayout.ResultOf
    rw [hσ]
    simp only [Haxc.ResultKind.read, hx]
  · cases hres

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
