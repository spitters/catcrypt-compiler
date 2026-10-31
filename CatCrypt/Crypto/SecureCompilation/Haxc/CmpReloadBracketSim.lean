/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.LsemExpandQ
public import CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracket

/-!
# The compare reload on bodies with `R15` brackets: the simulation

For a body passing the bracket-aware check `CmpReloadBracket.cmpReloadBrOK`, every halting run
of the typed body on the flag machine is matched by a halting run of the typed body of
`cmpReload body`. The simulation is an instance of `LsemExpandQ.lsemFuelMemF_expandQ` at the
position-indexed relation `brRel`: at a source position inside a bracket (`syncAt`) the bases
are equal up to the program counter (`EqPc`), elsewhere they agree outside `R15` and have equal
arrays `R15` (`AgreeL`).

## Main results

* `fstepF_larr_r15`: an `Lopn` naming no `R15` leaves the array `R15`.
* `instrOKQ_cmpReloadBr`: the per-instruction condition of the indexed simulation.
* `cmpReloadBr_lsemFuelMemF`: the reload preserves halting runs of bodies passing
  `cmpReloadBrOK`, with at most twice the fuel; the final bases agree outside `R15` and have
  equal arrays `R15`.
* `cmpReloadBrOK_of_cmpReloadOK`: a body passing `cmpReloadOK` passes `cmpReloadBrOK`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracketSim

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
  (NoArrWriteAt evalInstrPMemF_larr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
  (Agree KeptN fstepF_agree clsB clsB_spec CtlI)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames mulxFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (typeBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
open CatCrypt.Crypto.SecureCompilation.Haxc.LsemExpandQ
open CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracket

/-! ## The array `R15` under a step naming no `R15` -/

/-- An instruction whose wire names no `R15` writes no array `R15`. -/
theorem noArrWriteAt_r15 {w : LinstrR} (tg : MemTag) (hn : ∀ n ∈ instrNames w, KeptN n) :
    NoArrWriteAt "R15" (w, tg) := by
  refine ⟨fun dst base idx val h => ?_, fun dst h => ?_, fun dst base val k h => ?_⟩
  · change storeStruct? w = _ at h
    unfold storeStruct? at h
    split at h
    · split at h
      · cases h; exact hn _ (by simp [instrNames, opNames])
      · cases h
    · cases h
  · change zeroStruct? w = _ at h
    unfold zeroStruct? at h
    split at h
    · split at h
      · cases h; exact hn _ (by simp [instrNames, opNames])
      · cases h
    · cases h
  · change storeImmStruct? w = _ at h
    unfold storeImmStruct? at h
    split at h
    · split at h
      · cases h; exact hn _ (by simp [instrNames, opNames])
      · cases h
    · cases h

/-- **The array `R15` under a step naming no `R15`.** An `Lopn` whose wire names no `R15`
    leaves the array `R15`. -/
theorem fstepF_larr_r15 {i : LinstrRM} (hl : IsLopn i) (hn : ∀ n ∈ instrNames i.1, KeptN n)
    {s t : LstateM} {zf zt : Bool} (h : fstepF i s zf = some (t, zt)) :
    t.larr "R15" = s.larr "R15" := by
  obtain ⟨w, tg⟩ := i
  have he : evalInstrPMemF ⟨"", []⟩ (w, tg) { prog := { base := s, lfn := "" }, zf := zf }
      = some { prog := { base := t, lfn := "" }, zf := zt } := by
    rw [evalInstrPMemF_isLopn _ _ _ hl]
    change (fstepF (w, tg) s zf).map _ = _
    rw [h]; rfl
  exact evalInstrPMemF_larr "R15" _ (w, tg) _ _ (noArrWriteAt_r15 tg hn) he

/-! ## The position-indexed relation -/

/-- The relation at source position `k` of `body`: equality up to the program counter inside a
    bracket, `AgreeL` outside. -/
def brRel (tag : LinstrR → MemTag) (body : Lcmd) (k : Nat) (a b : LstateM) : Prop :=
  if syncAt tag false body k = true then EqPc a b else AgreeL a b

/-- The relation at every position implies `AgreeL`. -/
theorem brRel.agreeL {tag : LinstrR → MemTag} {body : Lcmd} {k : Nat} {a b : LstateM}
    (h : brRel tag body k a b) : AgreeL a b := by
  unfold brRel at h
  split at h
  · exact AgreeL.of_eqPc h
  · exact h

/-- Outside a bracket, `AgreeL` gives the relation. -/
theorem brRel_of_false {tag : LinstrR → MemTag} {body : Lcmd} {k : Nat} {a b : LstateM}
    (hk : syncAt tag false body k = false) (h : AgreeL a b) : brRel tag body k a b := by
  simp [brRel, hk, h]

/-- Inside a bracket, equality up to the program counter gives the relation. -/
theorem brRel_of_true {tag : LinstrR → MemTag} {body : Lcmd} {k : Nat} {a b : LstateM}
    (hk : syncAt tag false body k = true) (h : EqPc a b) : brRel tag body k a b := by
  simp [brRel, hk, h]

/-- The flag after position `k` of the typed body is `brStep` of the flag before it. -/
theorem syncAt_succ_typed {tag : LinstrR → MemTag} {sy : Bool} {body : Lcmd} {k : Nat}
    {i : LinstrRM} (hk : (typeBody tag body)[k]? = some i) :
    syncAt tag sy body (k + 1) = brStep tag (syncAt tag sy body k) i.1 := by
  simp only [typeBody, List.getElem?_map] at hk
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hk
  exact syncAt_succ tag sy hj

/-- The flag after a label of the typed body is reset. -/
theorem syncAt_label {tag : LinstrR → MemTag} {sy : Bool} {body : Lcmd} {l : LLabel}
    {pc : Nat} (hpc : findLabelMem l (typeBody tag body) = some pc) :
    syncAt tag sy body (pc + 1) = false := by
  obtain ⟨x, hx, hlab⟩ := JasminLsemLabeled.findLabel_sound l _ pc hpc
  rw [List.getElem?_map] at hx
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hx
  rw [syncAt_succ_typed hi]
  unfold JasminLsemLabeled.isLabel at hlab
  split at hlab
  · rename_i heq; rw [heq]; rfl
  · cases hlab

/-! ## The per-instruction condition -/

/-- **The per-instruction condition of the indexed simulation** at position `k` of the typed
    body, for a body passing `cmpReloadBrOK`. -/
theorem instrOKQ_cmpReloadBr {tag : LinstrR → MemTag} {body : Lcmd}
    (h : cmpReloadBrOK tag body = true) (fn : String) {k : Nat} {i : LinstrRM}
    (hk : (typeBody tag body)[k]? = some i) :
    InstrOKQ (brRel tag body) (cmpReloadRM tag) (singletonProgM fn (typeBody tag body)) k i := by
  obtain ⟨w, tg⟩ := i
  obtain ⟨hi, hok⟩ := brScan_sound_typeBody h hk
  simp only [Prod.mk.injEq, true_and] at hi
  subst hi
  have hnext := syncAt_succ_typed (sy := false) hk
  obtain ⟨hcls, hsome, hnone⟩ := brOKI_spec hok
  cases hsp : spillCmp? w with
  | some p =>
      obtain ⟨opn, d, s⟩ := p
      obtain ⟨rfl, hkept⟩ := hsome _ _ _ hsp
      obtain ⟨rfl, -⟩ := spillCmp?_eq_some hsp
      have hs1 : syncAt tag false body (k + 1) = false := by
        rw [hnext]; simp [brStep, hsp]
      have hexp : cmpReloadRM tag
          (.Lopn [.reg d] (withWidthTag 64 "CMP") [.reg d, s],
            tag (.Lopn [.reg d] (withWidthTag 64 "CMP") [.reg d, s]))
          = [(.Lopn [.reg reloadScratch] (movOf (withWidthTag 64 "CMP")) [.reg d],
               tag (.Lopn [.reg reloadScratch] (movOf (withWidthTag 64 "CMP")) [.reg d])),
             (.Lopn [.reg reloadScratch] (withWidthTag 64 "CMP") [.reg reloadScratch, s],
               tag (.Lopn [.reg reloadScratch] (withWidthTag 64 "CMP")
                 [.reg reloadScratch, s]))] := by
        have hr : x86Abi.reload = reloadScratch := rfl
        simp [cmpReloadRM, cmpReloadI, hsp, typeBody, hr]
      refine Or.inl ⟨⟨_, _, _, rfl⟩, fun j hj => ?_, fun a a' t zf zt hR hst => ?_⟩
      · simp only [hexp, List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
      · simp only [hexp]
        obtain ⟨t', hrun, hA⟩ := reload_agreeL d s _ _ _
          (hkept d (by simp [instrNames, opNames]))
          (fun n hn' => hkept n (by simp only [instrNames, List.cons_append, List.nil_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
                                    exact Or.inr (Or.inr hn'))) hR.agreeL hst
        exact ⟨t', hrun, brRel_of_false hs1 hA⟩
  | none =>
      have hself : cmpReloadRM tag (w, tag w) = [(w, tag w)] := by
        simp [cmpReloadRM, cmpReloadI, hsp, typeBody]
      rcases clsB_spec hcls with hl | hc
      · have hs1 : syncAt tag false body (k + 1)
            = (opensBracket w || syncAt tag false body k) := by
          rw [hnext]
          obtain ⟨d, o, s, hw⟩ := hl
          simp only at hw
          subst hw
          simp [brStep, hsp]
        refine Or.inl ⟨hl, fun j hj => ?_, fun a a' t zf zt hR hst => ?_⟩
        · simp only [hself, List.mem_singleton] at hj
          subst hj
          exact hl
        · simp only [hself]
          by_cases hob : opensBracket w = true
          · obtain ⟨t', h', hE⟩ := fstepF_opensBracket hob (tag w) hR.agreeL hst
            exact ⟨t', by rw [runStraightF_cons, h']; rfl,
              brRel_of_true (by rw [hs1, hob]; rfl) hE⟩
          · by_cases hsy : syncAt tag false body k = true
            · have hE : EqPc a a' := by simpa [brRel, hsy] using hR
              obtain ⟨t', h', hE'⟩ := fstepF_replay _ hE hst
              exact ⟨t', by rw [runStraightF_cons, h']; rfl,
                brRel_of_true (by rw [hs1, hsy]; simp) hE'⟩
            · have hA : AgreeL a a' := hR.agreeL
              obtain ⟨hn, hm⟩ := ((hnone hsp).resolve_left hob).resolve_left hsy
              obtain ⟨t', h', hA'⟩ := fstepF_agree hl hn hm hA.agree hst
              have r1 := fstepF_larr_r15 hl hn hst
              have r2 := fstepF_larr_r15 hl hn h'
              exact ⟨t', by rw [runStraightF_cons, h']; rfl,
                brRel_of_false (by simp [hs1, hob, hsy]) ⟨hA', by rw [r2, r1, hA.r15]⟩⟩
      · refine Or.inr ⟨hself, ?_⟩
        have hN : ∀ k', syncAt tag false body k' = false → NextQ (brRel tag body) k k' :=
          fun k' hk' a b p q hR => brRel_of_false hk' (hR.agreeL.setLpc p q)
        have hJ : ∀ l, JumpQ (brRel tag body) (singletonProgM fn (typeBody tag body)) k l :=
          fun l pc hpc => hN _ (syncAt_label hpc)
        rcases hc with ⟨kd, l, hw⟩ | ⟨c, l, hw, hcc⟩ | ⟨tgt, hw⟩
        · exact Or.inl ⟨kd, l, hw, hN _ (by rw [hnext]; simp only at hw; rw [hw]; rfl)⟩
        · obtain ⟨pl, hpl⟩ := Option.ne_none_iff_exists'.mp hcc
          exact Or.inr (Or.inl ⟨c, l, pl, hw, hpl,
            hN _ (by rw [hnext]; simp only at hw; rw [hw]; rfl), hJ _⟩)
        · exact Or.inr (Or.inr ⟨tgt.1, tgt.2, hw, hJ _⟩)

/-! ## The simulation -/

/-- **`cmpReloadBr_lsemFuelMemF`: the reload of spilled compare operands preserves halting
    runs of bodies with `R15` brackets.** For a body that passes `cmpReloadBrOK tag`, every
    halting run of the typed body from program counter `0` is matched by a halting run of the
    typed body of `cmpReload body` from the same state, with at most twice the fuel; the final
    bases agree on every register and array other than `R15`, on the word memory, the carry
    and overflow flags, and have equal arrays `R15`; the zero flags and function names agree,
    and the final program counter is the `pcMap` image. -/
theorem cmpReloadBr_lsemFuelMemF {tag : LinstrR → MemTag} {body : Lcmd}
    (h : cmpReloadBrOK tag body = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn (typeBody tag body)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 2
      ∧ lsemFuelMemF (singletonProgM fn (typeBody tag (cmpReload body))) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.prog.base.larr "R15" = t.prog.base.larr "R15"
      ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn
      ∧ t'.prog.base.lpc = pcMap (cmpReloadRM tag) (typeBody tag body) t.prog.base.lpc := by
  have hP : ExpProgQ (brRel tag body) (cmpReloadRM tag) (singletonProgM fn (typeBody tag body))
      (singletonProgM fn (typeBody tag (cmpReload body))) :=
    ⟨rfl, typeBody_cmpReload tag body, fun _ _ hk => instrOKQ_cmpReloadBr h fn hk⟩
  have hlen : ∀ i ∈ (singletonProgM fn (typeBody tag body)).body,
      (cmpReloadRM tag i).length ≤ 2 := by
    intro i _
    unfold cmpReloadRM cmpReloadI typeBody
    simp only
    split <;> simp
  have hR : RelXQ (brRel tag body) (cmpReloadRM tag) (singletonProgM fn (typeBody tag body))
      s s := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · rw [hpc]; rfl
    · rw [hpc]; exact brRel_of_false (syncAt_zero _ _ _) (AgreeL.refl _)
  obtain ⟨fuel', t', hf, hrun', hRt⟩ := lsemFuelMemF_expandQ hP hlen fuel hR hrun
  have hA := hRt.base.agreeL
  exact ⟨fuel', t', hf, hrun', hA.agree, hA.r15, hRt.zf, hRt.lfn, hRt.pc⟩

/-! ## The check subsumes `cmpReloadOK` -/

/-- An instruction passing `cmpReloadOKI` passes `brOKI` at every flag. -/
theorem brOKI_of_cmpReloadOKI {tag : LinstrR → MemTag} {w : LinstrR} (sy : Bool)
    (h : cmpReloadOKI tag w = true) : brOKI tag sy w = true := by
  simp only [cmpReloadOKI, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hcls, hn⟩, hm⟩, hw⟩ := h
  have hr : x86Abi.reload = "R15" := rfl
  have hn' : noR15 w = true := by
    simp only [noR15, List.all_eq_true, bne_iff_ne, ne_eq]
    intro x hx; exact hr ▸ hn x hx
  unfold brOKI
  cases hsp : spillCmp? w with
  | none => simp [hcls, hn', hm]
  | some p =>
      obtain ⟨opn, d, s⟩ := p
      rw [hsp] at hw
      simp_all

/-- A body all of whose instructions pass `cmpReloadOKI` passes the scan from every flag. -/
theorem brScan_of_all {tag : LinstrR → MemTag} :
    ∀ (sy : Bool) (body : Lcmd), body.all (fun i => cmpReloadOKI tag i.li_i) = true →
      brScan tag sy body = true
  | _, [], _ => rfl
  | sy, j :: js, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp only [brScan, brOKI_of_cmpReloadOKI sy h.1, brScan_of_all _ js h.2, Bool.and_self]

/-- **The bracket-aware check subsumes the side conditions of the reload**: a body passing
    `cmpReloadOK` passes `cmpReloadBrOK`. -/
theorem cmpReloadBrOK_of_cmpReloadOK {tag : LinstrR → MemTag} {body : Lcmd}
    (h : cmpReloadOK tag body = true) : cmpReloadBrOK tag body = true :=
  brScan_of_all false body h

end CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracketSim
