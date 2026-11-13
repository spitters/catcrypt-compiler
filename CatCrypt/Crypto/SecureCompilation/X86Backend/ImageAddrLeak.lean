/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertGate

@[expose] public section

set_option autoImplicit false

/-!
# The leakage of the virtual body of the image route

The trace, in the events `instrLeakF` of the traced flag machine `lsemFuelMemFLeak`, of the
virtual body `virtB` of the image route: the copies of the parameter registers, the seeds,
the copies of the loop-carried names and the renamed loop, fused when the route asks for it.

The copies emit no event. When the seeds emit no event and the loop has no compile-time
array operand (`NoCArr`), the virtual body emits the trace of the node `seeds ++ loop` with
each array base renamed by `renOf ps` (`renEv`); the fusion of the widening multiplies keeps
the trace. For the certified single-loop node the node trace is `loopT` of the source events
(`JasminLsemMemFLeakLoop.singleLoop_leak_abi`), so the trace of the virtual body is a function
of the source events, and constant time of the source gives constant time of the virtual body
from the entry states of the image route.

## Main definitions

* `NoCArr`: an instruction with no compile-time array operand.
* `routeEntry`, `RouteEntryPub`: the entry state of the virtual body at a machine state, and
  two entry states whose valuations agree on the public labels.

## Main results

* `lsemFuelMemFLeak_prefix_eq`: the traced run behind a prefix of `Lopn`s.
* `instrLeakF_renRM`, `lsemFuelMemFLeak_map_renRM`: a renamed instruction and a renamed
  body emit the events of the original with renamed array bases.
* `renameLoop_leak`, `src_chain_leak`: the traced forms of `renameLoop_sim` and
  `ImageAddrSrc.src_chain`.
* `lsemFuelMemFLeak_expI`, `fuseMulHi_lsemFuelMemFLeak_pre`: an expansion by index, and the
  fusion of the loop part of a body, keep the trace.
* `virtB_leak`: the trace of the virtual body from the trace of the node.
* `certNode_noCArr`, `loopSeedsRM_quiet`: the certified node has no compile-time array
  operand, and its seed moves emit no event.
* `virtB_leak_source`, `virtB_memFCT`: the trace of the virtual body from the source events,
  and constant time of the virtual body from the source.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF fstepF
  runStraightF_cons evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR
  renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)

/-! ## 1. The traced run behind a prefix -/

/-- The events of an instruction do not read the program counter. -/
theorem instrLeakB_lpc (r : LstateN) (p : Nat) (i : LinstrRM) :
    instrLeakB { r with lpc := p } i = instrLeakB r i := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o ss => rfl
  | Lcond c l =>
      simp only [instrLeakB]
      cases c <;> rfl
  | _ => rfl

theorem instrLeakF_shiftS (d : Nat) (i : LinstrRM) (s : LstateMF) :
    instrLeakF i (shiftS d s) = instrLeakF i s := by
  unfold instrLeakF
  split
  · rfl
  · exact instrLeakB_lpc _ _ i

/-- **The traced run behind a prefix, as an equation.** The traced run of `pre ++ B` from the
    moved state is the traced run of `B` with the final state moved and the same trace. -/
theorem lsemFuelMemFLeak_prefix_eq (fn : String) (pre B : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, CtlOK i) :
    ∀ (fuel : Nat) (s : LstateMF),
      lsemFuelMemFLeak (singletonProgM fn (pre ++ B)) fuel (shiftS pre.length s)
        = (lsemFuelMemFLeak (singletonProgM fn B) fuel s).map
            fun r => (shiftS pre.length r.1, r.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s
      unfold lsemFuelMemFLeak
      rw [findInstrMem_prefix fn pre B (shiftRel_shiftS _ s)]
      cases findInstrMem (singletonProgM fn B) s.prog <;> rfl
  | succ n ih =>
      intro s
      unfold lsemFuelMemFLeak
      rw [findInstrMem_prefix fn pre B (shiftRel_shiftS _ s)]
      cases hf : findInstrMem (singletonProgM fn B) s.prog with
      | none => rfl
      | some i =>
          have hiB : i ∈ B := by
            unfold findInstrMem at hf
            split at hf
            · exact List.mem_of_getElem? hf
            · cases hf
          simp only
          rw [evalInstrPMemF_prefix_eq fn pre B hpre (hB i hiB) s, instrLeakF_shiftS]
          cases evalInstrPMemF (singletonProgM fn B) i s with
          | none => rfl
          | some u =>
              simp only [Option.map_some]
              rw [ih u, Option.map_map, Option.map_map]
              rfl

/-! ## 2. A renamed body on the traced flag machine -/

/-- An instruction with no compile-time array operand. -/
def NoCArr : LinstrR → Prop
  | .Lopn ds _ ss => ∀ o ∈ ds ++ ss, ∀ b k, o ≠ .arr b k
  | _ => True

/-- The constant-index store event of a renamed instruction is the event of the instruction
    with its array base renamed. -/
theorem storeImmEv_renRM_any (σ : String → String) (i : LinstrRM) :
    storeImmEv (renRM σ i) = (storeImmEv i).map (renEv σ) := by
  obtain ⟨w, tag⟩ := i
  unfold storeImmEv renRM
  cases tag <;> try rfl
  dsimp only
  rw [storeImmStruct?_ren]
  cases storeImmStruct? w <;> rfl

/-- **The events of a renamed instruction.** For an instruction with no compile-time array
    operand that branches on the zero flag only, whose names lie in `N`, the renamed
    instruction emits from a state related by `RelF σ N` the events of the instruction with
    renamed array bases. -/
theorem instrLeakF_renRM {σ : String → String} {N : String → Prop} (i : LinstrRM)
    (hi : ∀ n ∈ instrNames i.1, N n) (hc : CondOK i) (ha : NoCArr i.1) {s s' : LstateMF}
    (hR : RelF σ N s s') :
    instrLeakF (renRM σ i) s' = (instrLeakF i s).map (renEv σ) := by
  unfold instrLeakF
  rw [flagCondCC?_ren]
  cases h : flagCondCC? i with
  | some p =>
      obtain ⟨pol, l⟩ := p
      simp only [hR.2.2.1]
      rfl
  | none =>
      simp only
      obtain ⟨w, tag⟩ := i
      cases w with
      | Lopn ds o ss =>
          simp only [instrLeakB, renRM, renLinstrR, ← List.map_append, List.flatMap_map]
          split_ifs
          · rfl
          rw [List.map_append, List.map_flatMap]
          congr 1
          swap
          · exact storeImmEv_renRM_any σ (.Lopn ds o ss, tag)
          refine List.flatMap_congr fun x hx => ?_
          cases x with
          | reg q => rfl
          | imm v => rfl
          | arr b k => exact absurd rfl (ha _ hx b k)
          | arrIdx b q sc =>
              have hq : s'.prog.base.reg.lvm (σ q) = s.prog.base.reg.lvm q :=
                hR.1.1.2 q (hi q (by
                  simp only [instrNames, List.mem_flatMap]
                  exact ⟨_, hx, by simp [opNames]⟩))
              simp only [opLeakF, renOperand, renEv, idxVal, List.map_cons, List.map_nil]
              rw [hq]
      | Lcond c l => exact absurd h (hc.1 c l rfl)
      | _ => rfl

/-- **A renamed body on the traced flag machine.** For `σ` usable on `N` and a body whose
    instructions mention names of `N` only, branch on the zero flag only and have no
    compile-time array operand, every terminating traced run of the body is matched, with the
    same fuel, by a terminating traced run of the renamed body from a related state, into a
    related state, with the trace of the body with renamed array bases. -/
theorem lsemFuelMemFLeak_map_renRM {σ : String → String} {N : String → Prop}
    (hσ : RenOn σ N) (fn : String) (body : List LinstrRM)
    (hn : ∀ i ∈ body, ∀ n ∈ instrNames i.1, N n) (hc : ∀ i ∈ body, CondOK i)
    (ha : ∀ i ∈ body, NoCArr i.1) :
    ∀ (fuel : Nat) {s s' : LstateMF} {r : LstateMF × List CTLeak}, RelF σ N s s' →
      lsemFuelMemFLeak (singletonProgM fn body) fuel s = some r →
      ∃ t', lsemFuelMemFLeak (singletonProgM fn (body.map (renRM σ))) fuel s'
          = some (t', r.2.map (renEv σ)) ∧ RelF σ N r.1 t' := by
  have hP := renProg_map (σ := σ) (N := N) fn body (Nat.zero_le 1)
    (fun _ i _ hi => hn i (List.mem_of_getElem? hi))
    (fun _ i _ hi => hc i (List.mem_of_getElem? hi))
  have hfetch : ∀ {s s' : LstateMF}, RelF σ N s s' →
      findInstrMem (singletonProgM fn (body.map (renRM σ))) s'.prog
        = (findInstrMem (singletonProgM fn body) s.prog).map (renRM σ) := by
    intro s s' hR
    unfold findInstrMem
    rw [hR.2.1, hP.lfn]
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
    split
    · rw [hpc]; exact hP.body _ (Nat.zero_le _)
    · rfl
  have hmem : ∀ {s : LstateMF} {i : LinstrRM},
      findInstrMem (singletonProgM fn body) s.prog = some i → i ∈ body := by
    intro s i hf
    unfold findInstrMem at hf
    split at hf
    · exact List.mem_of_getElem? hf
    · cases hf
  intro fuel
  induction fuel with
  | zero =>
      intro s s' r hR h
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          rw [lsemFuelMemFLeak_halt _ _ _ hf] at h
          cases h
          exact ⟨s', lsemFuelMemFLeak_halt _ _ _ (by rw [hfetch hR, hf]; rfl), hR⟩
      | some i => simp [lsemFuelMemFLeak, hf] at h
  | succ n ih =>
      intro s s' r hR h
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          rw [lsemFuelMemFLeak_halt _ _ _ hf] at h
          cases h
          exact ⟨s', lsemFuelMemFLeak_halt _ _ _ (by rw [hfetch hR, hf]; rfl), hR⟩
      | some i =>
          have hi := hmem hf
          cases he : evalInstrPMemF (singletonProgM fn body) i s with
          | none => simp [lsemFuelMemFLeak, hf, he] at h
          | some u =>
              rw [lsemFuelMemFLeak_step _ _ _ _ _ hf he] at h
              obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨u', hu', hRu, -⟩ := evalInstrPMemF_ren hσ hP i (hn i hi) (hc i hi) hR
                (Nat.zero_le _) he
              obtain ⟨t', ht', hRt⟩ := ih hRu hq
              refine ⟨t', ?_, hRt⟩
              rw [lsemFuelMemFLeak_step _ _ _ _ _ (by rw [hfetch hR, hf]; rfl) hu', ht',
                instrLeakF_renRM i (hn i hi) (hc i hi) (ha i hi) hR]
              simp

/-! ## 3. The loop renamed behind the copies -/

/-- The copies emit nothing. -/
theorem movesOf_quiet (ps : List (String × String)) :
    ∀ i ∈ movesOf ps, ∀ r, instrLeakB r i = [] := by
  intro i hi r
  simp only [movesOf, List.mem_map] at hi
  obtain ⟨p, -, rfl⟩ := hi
  rfl

/-- **The trace of the loop renamed behind the copies.** Under the hypotheses of
    `renameLoop_sim`, for a loop with no compile-time array operand, a terminating traced run
    of `pre ++ loop` from a base at program counter `0` emits the events of the prefix followed
    by events `T`, and the renamed body `pre ++ movesOf ps ++ map (renRM (renOf ps)) loop`
    halts from the same base with the events of the prefix followed by `T` with renamed array
    bases. -/
theorem renameLoop_leak (fn : String) (pre loop : List LinstrRM) (ps : List (String × String))
    (N : String → Prop) (hpre : ∀ i ∈ pre, IsLopn i) (hloop : ∀ i ∈ loop, CtlOK i)
    (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (ha : ∀ i ∈ loop, NoCArr i.1) (b0 : LstateM) (zf : Bool)
    (h0 : b0.lpc = 0)
    (hA : ∀ b1 z1, runStraightF pre b0 zf = some (b1, z1) →
      ∀ r, N r → b1.larr (renOf ps r) = b1.larr r)
    (fuel : Nat) (t : LstateMF) (ℓ : List CTLeak)
    (hrun : lsemFuelMemFLeak (singletonProgM fn (pre ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some (t, ℓ)) :
    ∃ T, ℓ = straightLeakFF pre b0 zf ++ T ∧ ∃ fuel' t',
      lsemFuelMemFLeak
        (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        fuel' { prog := { base := b0, lfn := fn }, zf := zf }
        = some (t', straightLeakFF pre b0 zf ++ T.map (renEv (renOf ps))) := by
  have hpos : ∀ j, j < pre.length →
      (singletonProgM fn (pre ++ loop)).body[b0.lpc + j]? = pre[j]? := fun j hj => by
    simp only [singletonProgM, h0, Nat.zero_add]
    exact List.getElem?_append_left hj
  have hu : lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t := by
    rw [← lsemFuelMemFLeak_fst, hrun]
    rfl
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le
    (lsemFuelMemF_seg_fuel _ fn rfl pre b0 zf fuel t hpre hpos hu)
  cases hp : runStraightF pre b0 zf with
  | none =>
      rw [JasminLsemMemFlagNestJoin.lsemFuelMemF_segF _ fn rfl pre b0 zf f hpre hpos, hp] at hu
      cases hu
  | some bz =>
      obtain ⟨b1, z1⟩ := bz
      rw [lsemFuelMemFLeak_segF _ fn rfl pre b0 zf f (b1, z1) hpre hpos hp] at hrun
      obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hrun
      have hpc : b1.lpc = pre.length := by
        rw [JasminLsemMemFlagNestJoin.runStraightF_lpc pre b0 zf b1 z1 hp, h0, Nat.zero_add]
      have hsh : ({ prog := { base := b1, lfn := fn }, zf := z1 } : LstateMF)
          = shiftS pre.length { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } := by
        simp only [shiftS, LstateM.lpc_setLpc, Nat.zero_add, ← hpc]
        rfl
      rw [hsh, lsemFuelMemFLeak_prefix_eq fn pre loop hpre hloop] at hq
      obtain ⟨ql, hql, rfl⟩ := Option.map_eq_some_iff.mp hq
      have hR : RelF (renOf ps) N { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 }
          { prog := { base := (movesState ps b1).setLpc 0, lfn := fn }, zf := z1 } := by
        obtain ⟨hl, hm, hc, ho⟩ := movesState_larr ps b1
        refine ⟨⟨⟨rfl, fun r hr => ?_⟩, fun r hr => ?_, hm⟩, rfl, rfl, hc, ho⟩
        · show (movesState ps b1).reg.lvm (renOf ps r) = b1.reg.lvm r
          by_cases hm' : r ∈ ps.map Prod.fst
          · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hm'
            rw [hren p hp']
            exact movesState_target ps hnd hts b1 p hp'
          · rw [renOf_of_not_mem hm']
            refine movesState_other ps b1 r fun hmem => ?_
            obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hmem
            exact hfresh p hp' hr
        · show (movesState ps b1).larr (renOf ps r) = b1.larr r
          rw [hl]
          exact hA b1 z1 hp r hr
      obtain ⟨tl', htl', -⟩ := lsemFuelMemFLeak_map_renRM hσ fn loop hn hcond ha f hR hql
      have hpre' : ∀ i ∈ pre ++ movesOf ps, IsLopn i := by
        intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact hpre i hi
        · exact movesOf_isLopn ps i hi
      have hB' : ∀ i ∈ loop.map (renRM (renOf ps)), CtlOK i := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        exact ctlOK_renRM _ (hloop j hj)
      have hrunPre : runStraightF (pre ++ movesOf ps) b0 zf = some (movesState ps b1, z1) := by
        rw [JasminLsemAddrMem.runStraightF_append, hp, Option.bind_some,
          runStraightF_movesOf]
      have hpos' : ∀ j, j < (pre ++ movesOf ps).length →
          (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps)))).body[b0.lpc + j]?
            = (pre ++ movesOf ps)[j]? := fun j hj => by
        simp only [singletonProgM, h0, Nat.zero_add]
        exact List.getElem?_append_left hj
      have hpc2 : (movesState ps b1).lpc = (pre ++ movesOf ps).length := by
        rw [movesState_lpc, hpc, List.length_append, movesOf_length]
      have hsh2 : ({ prog := { base := movesState ps b1, lfn := fn }, zf := z1 } : LstateMF)
          = shiftS (pre ++ movesOf ps).length
              { prog := { base := (movesState ps b1).setLpc 0, lfn := fn }, zf := z1 } := by
        simp only [shiftS, LstateM.lpc_setLpc, Nat.zero_add, ← hpc2]
        rfl
      refine ⟨ql.2, ?_, (pre ++ movesOf ps).length + f, shiftS (pre ++ movesOf ps).length tl', ?_⟩
      · rw [← (Prod.mk.inj hqe).2]
      · rw [lsemFuelMemFLeak_segF _ fn rfl (pre ++ movesOf ps) b0 zf f _ hpre' hpos' hrunPre,
          hsh2, lsemFuelMemFLeak_prefix_eq fn (pre ++ movesOf ps) _ hpre' hB', htl',
          straightLeakFF_append pre (movesOf ps) b0 zf (b1, z1) hp,
          straightLeakFF_quiet (movesOf ps) (movesOf_quiet ps)]
        simp

/-- **The trace of the virtual body from the exported node.** Under the hypotheses of
    `ImageAddrSrc.src_chain`, for a quiet prefix `pre0`, quiet seeds and a loop with no
    compile-time array operand, a terminating traced run of the node `seeds ++ loop` from
    `b0` with trace `ℓ` is matched by a terminating traced run of
    `pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))` from `b0` with trace `ℓ` with
    renamed array bases. -/
theorem src_chain_leak (fn : String) (pre0 seeds loop : List LinstrRM)
    (ps : List (String × String)) (N : String → Prop) (hpre0 : ∀ i ∈ pre0, IsLopn i)
    (hseeds : ∀ i ∈ seeds, IsLopn i)
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (ha : ∀ i ∈ loop, NoCArr i.1)
    (hq0 : ∀ i ∈ pre0, ∀ r, instrLeakB r i = []) (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = [])
    (b0 b1 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hpr : runStraightF pre0 b0 zf = some (b1, zf)) (hb1 : b1.setLpc 0 = b0)
    (hA : ∀ b2 z2, runStraightF (pre0 ++ seeds) b0 zf = some (b2, z2) →
      ∀ r, N r → b2.larr (renOf ps r) = b2.larr r)
    (fuel : Nat) (t : LstateMF) (ℓ : List CTLeak)
    (hrun : lsemFuelMemFLeak (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some (t, ℓ)) :
    ∃ fuel' t', lsemFuelMemFLeak
        (singletonProgM fn (pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        fuel' { prog := { base := b0, lfn := fn }, zf := zf }
      = some (t', ℓ.map (renEv (renOf ps))) := by
  have hB : ∀ i ∈ seeds ++ loop, CtlOK i := by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact Or.inl (hseeds i h)
    · exact hloop i h
  have hpre : ∀ i ∈ pre0 ++ seeds, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact hpre0 i h
    · exact hseeds i h
  have hpos : ∀ j, j < pre0.length →
      (singletonProgM fn (pre0 ++ (seeds ++ loop))).body[b0.lpc + j]? = pre0[j]? :=
    fun j hj => by
      simp only [singletonProgM, h0, Nat.zero_add]
      exact List.getElem?_append_left hj
  have hpc1 : b1.lpc = pre0.length := by
    rw [JasminLsemMemFlagNestJoin.runStraightF_lpc pre0 b0 zf b1 zf hpr, h0, Nat.zero_add]
  have hsh : ({ prog := { base := b1, lfn := fn }, zf := zf } : LstateMF)
      = shiftS pre0.length { prog := { base := b0, lfn := fn }, zf := zf } := by
    rw [← hb1]
    simp only [shiftS, LstateM.lpc_setLpc, Nat.zero_add, ← hpc1]
    rfl
  have hrun0 : lsemFuelMemFLeak (singletonProgM fn (pre0 ++ seeds ++ loop))
      (pre0.length + fuel) { prog := { base := b0, lfn := fn }, zf := zf }
        = some (shiftS pre0.length t, ℓ) := by
    rw [List.append_assoc, lsemFuelMemFLeak_segF _ fn rfl pre0 b0 zf fuel (b1, zf) hpre0 hpos hpr,
      hsh, lsemFuelMemFLeak_prefix_eq fn pre0 _ hpre0 hB, hrun,
      straightLeakFF_quiet pre0 hq0]
    rfl
  obtain ⟨T, hT, fuel', t', ht'⟩ := renameLoop_leak fn (pre0 ++ seeds) loop ps N hpre hloop
    hcond hσ hn hnd hts hren hfresh ha b0 zf h0 hA _ _ _ hrun0
  have hq : ∀ i ∈ pre0 ++ seeds, ∀ r, instrLeakB r i = [] := by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact hq0 i h
    · exact hqs i h
  rw [straightLeakFF_quiet _ hq, List.nil_append] at hT ht'
  subst hT
  exact ⟨fuel', t', ht'⟩

/-! ## 4. An expansion by index on the traced flag machine -/

section Exp

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

variable {Q : LstateM → LstateM → Prop} {G : LstateM → Prop}
  {Inv : Nat → LstateM → Bool → Prop} {e : Nat → LinstrRM → List LinstrRM}

/-- A control instruction emits the same events from two states with the same zero flag. -/
theorem instrLeakF_ctl {i : LinstrRM} (hc : CtlI i) {s s' : LstateMF} (hz : s'.zf = s.zf) :
    instrLeakF i s' = instrLeakF i s := by
  unfold instrLeakF
  cases hcc : flagCondCC? i with
  | some p => simp only [hz]
  | none =>
      simp only
      obtain ⟨w, tag⟩ := i
      rcases hc with ⟨kd, l, hw⟩ | ⟨c, l, hw, hn⟩ | ⟨tgt, hw⟩
      · simp only at hw; subst hw; rfl
      · exact absurd hcc hn
      · simp only at hw; subst hw; rfl

/-- **One control step under an expansion.** A successful step of a control instruction of
    the source is matched by the same instruction of the expanded body from a related state,
    into a related state. -/
theorem evalInstrPMemF_expI_ctl {fn : String} {body : List LinstrRM}
    (h : ExpInv Q G Inv e body) {s s' u : LstateMF} {i : LinstrRM}
    (hR : RelI Q Inv e body s s') (hget : body[s.prog.base.lpc]? = some i) (hctl : CtlI i)
    (he : evalInstrPMemF (singletonProgM fn body) i s = some u) :
    ∃ u', evalInstrPMemF (singletonProgM fn (expI e body 0)) i s' = some u'
      ∧ RelI Q Inv e body u u' := by
  set k := s.prog.base.lpc with hk
  have hself : e k i = [i] := by
    rcases h.cls k i hget with ⟨d, o, ss, hd⟩ | ⟨_, hs⟩
    · rcases hctl with ⟨_, _, hw⟩ | ⟨_, _, hw, _⟩ | ⟨_, hw⟩ <;> rw [hd] at hw <;> cases hw
    · exact hs
  have hG : G s.prog.base := h.ginv _ _ _ hR.inv
  have hnext : pcI e body (k + 1) = s'.prog.base.lpc + 1 := by
    rw [pcI_succ e hget, hself, hR.pc]; rfl
  have hinvN : ∀ z, Inv (k + 1) s.prog.base.nextPc z := fun z =>
    h.start k i hget hctl _ z (h.gpc _ _ hG)
  have hQN : Q s.prog.base.nextPc s'.prog.base.nextPc := h.qpc _ _ _ _ hR.base
  obtain ⟨wire, tag⟩ := i
  rcases hctl with ⟨kd, l, hw⟩ | ⟨c, l, hw, hcc⟩ | ⟨tgt, hw⟩
  · obtain rfl : wire = LinstrR.Llabel kd l := hw
    rw [JasminLsemMemFlagNestJoin.evalInstrPMemF_label] at he
    cases he
    exact ⟨_, JasminLsemMemFlagNestJoin.evalInstrPMemF_label _ kd l tag s',
      ⟨hR.lfn, hR.zf, hnext.symm, hQN, hinvN _⟩⟩
  · obtain rfl : wire = LinstrR.Lcond c l := hw
    have h1 : cmpArgs? (LinstrR.Lcond c l, tag) = none := rfl
    have h2 : movRegArgs? (LinstrR.Lcond c l, tag) = none := rfl
    cases h3 : flagCondCC? (LinstrR.Lcond c l, tag) with
    | none => exact absurd h3 hcc
    | some pl =>
        obtain ⟨pol, lbl⟩ := pl
        unfold evalInstrPMemF at he
        simp only [h1, h2, h3] at he
        split at he
        · rename_i hz
          obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
          obtain ⟨q', hq', hQq, hfq, hpq, hiq⟩ := evalJumpMem_expI h lbl hR.base hG hR.lfn hq
          refine ⟨{ s' with prog := q' }, ?_, ⟨hfq, hR.zf, hpq, hQq, hiq _⟩⟩
          unfold evalInstrPMemF
          simp only [h1, h2, h3]
          rw [ite_eq_left (hR.zf.trans hz), hq']; rfl
        · rename_i hz
          cases he
          refine ⟨{ s' with prog := { s'.prog with base := s'.prog.base.nextPc } }, ?_,
            ⟨hR.lfn, hR.zf, hnext.symm, hQN, hinvN _⟩⟩
          unfold evalInstrPMemF
          simp only [h1, h2, h3]
          rw [ite_eq_right (fun h => hz (hR.zf.symm.trans h))]
  · obtain rfl : wire = LinstrR.Lgoto tgt := hw
    obtain ⟨gfn, l⟩ := tgt
    have hev : ∀ (R : LprogM) (x : LstateMF),
        evalInstrPMemF R (LinstrR.Lgoto (gfn, l), tag) x
          = (if gfn = R.lfn then evalJumpMem R l x.prog else none).map
              (fun p => { x with prog := p }) := fun R x => by
      rw [evalInstrPMemF_delegate R _ x rfl rfl rfl rfl rfl rfl]; rfl
    rw [hev] at he
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
    split at hq
    · rename_i hf
      obtain ⟨q', hq', hQq, hfq, hpq, hiq⟩ := evalJumpMem_expI h l hR.base hG hR.lfn hq
      refine ⟨{ s' with prog := q' }, ?_, ⟨hfq, hR.zf, hpq, hQq, hiq _⟩⟩
      rw [hev, ite_eq_left (show gfn = (singletonProgM fn (expI e body 0)).lfn from hf), hq']; rfl
    · exact absurd hq (by simp)

/-- **An expansion by index on the traced flag machine.** Under the conditions `ExpInv` of an
    expansion simulation, when the expansion of each `Lopn` emits, from a `Q`-related state,
    the events of the `Lopn`, every terminating traced run of the source body is matched,
    from a related state, by a terminating traced run of the expanded body into a related
    state with the same trace. -/
theorem lsemFuelMemFLeak_expI {fn : String} {body : List LinstrRM}
    (h : ExpInv Q G Inv e body)
    (hleak : ∀ k i, body[k]? = some i → IsLopn i → ∀ (s s' : LstateM) (zf : Bool),
      Inv k s zf → Q s s' → straightLeakFF (e k i) s' zf = instrLeakB s.reg i) :
    ∀ (fuel : Nat) {s s' : LstateMF} {r : LstateMF × List CTLeak}, RelI Q Inv e body s s' →
      lsemFuelMemFLeak (singletonProgM fn body) fuel s = some r →
      ∃ fuel' t', lsemFuelMemFLeak (singletonProgM fn (expI e body 0)) fuel' s'
          = some (t', r.2) ∧ RelI Q Inv e body r.1 t' := by
  have hhalt : ∀ {s s' : LstateMF}, RelI Q Inv e body s s' →
      findInstrMem (singletonProgM fn body) s.prog = none →
      findInstrMem (singletonProgM fn (expI e body 0)) s'.prog = none := by
    intro s s' hR hf
    unfold findInstrMem at hf ⊢
    rw [hR.lfn]
    split
    · rename_i hfn
      rw [ite_eq_left (show s.prog.lfn = (singletonProgM fn body).lfn from hfn)] at hf
      rw [hR.pc]
      exact getElem?_expI_pcI_none e (body := body) hf
    · rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s s' r hR hrun
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          rw [lsemFuelMemFLeak_halt _ _ _ hf] at hrun
          cases hrun
          exact ⟨0, s', lsemFuelMemFLeak_halt _ 0 s' (hhalt hR hf), hR⟩
      | some i => simp [lsemFuelMemFLeak, hf] at hrun
  | succ n ih =>
      intro s s' r hR hrun
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          rw [lsemFuelMemFLeak_halt _ _ _ hf] at hrun
          cases hrun
          exact ⟨0, s', lsemFuelMemFLeak_halt _ 0 s' (hhalt hR hf), hR⟩
      | some i =>
          have hfg : s.prog.lfn = fn ∧ body[s.prog.base.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact ⟨by assumption, hf⟩
            · simp at hf
          have hfn' : s'.prog.lfn = fn := hR.lfn.trans hfg.1
          have hpos : ∀ j, j < (e s.prog.base.lpc i).length →
              (expI e body 0)[s'.prog.base.lpc + j]? = (e s.prog.base.lpc i)[j]? := by
            intro j hj
            rw [hR.pc]
            exact getElem?_expI_pcI e hfg.2 hj
          cases he : evalInstrPMemF (singletonProgM fn body) i s with
          | none => simp [lsemFuelMemFLeak, hf, he] at hrun
          | some u =>
              rw [lsemFuelMemFLeak_step _ _ _ _ _ hf he] at hrun
              obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hrun
              rcases h.cls _ i hfg.2 with hlopn | ⟨hctl, hself⟩
              · obtain ⟨hex, hstep⟩ := h.lopn _ i hfg.2 hlopn
                rw [evalInstrPMemF_isLopn _ i s hlopn] at he
                obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp he
                obtain ⟨b, z⟩ := bz
                obtain ⟨hinv, b', hb', hQb⟩ := hstep _ _ _ _ _ hR.inv hR.base hb
                have hL := hleak _ i hfg.2 hlopn _ _ _ hR.inv hR.base
                rw [← hR.zf] at hb' hL
                have hRu : RelI Q Inv e body { prog := { base := b, lfn := s.prog.lfn }, zf := z }
                    { prog := { base := b', lfn := s'.prog.lfn }, zf := z } := by
                  have h1 := JasminLsemMemFlagNestJoin.runStraightF_lpc _ _ _ _ _ hb'
                  have h2 := JasminLsemMemFlagNestJoin.fstepF_lpc_succ _ _ _ _ _ hb
                  refine ⟨hR.lfn, rfl, ?_, hQb, ?_⟩
                  · show b'.lpc = pcI e body b.lpc
                    rw [h1, h2, pcI_succ e hfg.2, hR.pc]
                  · show Inv b.lpc b z
                    rw [h2]; exact hinv
                obtain ⟨f', t', ht', hRt⟩ := ih hRu hq
                refine ⟨(e s.prog.base.lpc i).length + f', t', ?_, hRt⟩
                have hseg := lsemFuelMemFLeak_segF (singletonProgM fn (expI e body 0))
                  s'.prog.lfn hfn' (e s.prog.base.lpc i) s'.prog.base s'.zf f' (b', z) hex hpos
                  hb'
                have hs' : ({ prog := ⟨s'.prog.base, s'.prog.lfn⟩, zf := s'.zf } : LstateMF)
                    = s' := rfl
                rw [ht', hs'] at hseg
                rw [hseg, hL, instrLeakF_of_lopn hlopn]
                rfl
              · obtain ⟨u', hu', hRu⟩ := evalInstrPMemF_expI_ctl h hR hfg.2 hctl he
                obtain ⟨f', t', ht', hRt⟩ := ih hRu hq
                have hfetch : findInstrMem (singletonProgM fn (expI e body 0)) s'.prog
                    = some i := by
                  unfold findInstrMem
                  rw [ite_eq_left (show s'.prog.lfn = (singletonProgM fn (expI e body 0)).lfn
                    from hfn')]
                  have := hpos 0 (by rw [hself]; simp)
                  simpa [hself, singletonProgM] using this
                refine ⟨f' + 1, t', ?_, hRt⟩
                rw [lsemFuelMemFLeak_step _ _ _ _ _ hfetch hu', ht', instrLeakF_ctl hctl hR.zf]
                rfl

end Exp

/-! ## 5. The fusion on the traced flag machine -/

section Fuse

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

/-- An `Lopn` emits the same events from two register files that agree on its names. -/
theorem instrLeakB_agree {i : LinstrRM} (hl : IsLopn i) {r r' : LstateN}
    (h : ∀ n ∈ instrNames i.1, r'.lvm n = r.lvm n) : instrLeakB r' i = instrLeakB r i := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨ds, o, ss, hd⟩ := hl
  simp only at hd
  subst hd
  simp only [instrLeakB]
  split_ifs
  · rfl
  congr 1
  refine List.flatMap_congr fun x hx => ?_
  cases x with
  | arrIdx b q sc =>
      have hq : r'.lvm q = r.lvm q := h q (by
        simp only [instrNames, List.mem_flatMap]
        exact ⟨_, hx, by simp [opNames]⟩)
      simp only [opLeakF, idxVal]
      rw [hq]
  | _ => rfl

theorem straightLeakFF_single (i : LinstrRM) (s : LstateM) (zf : Bool) :
    straightLeakFF [i] s zf = instrLeakB s.reg i := by
  simp only [straightLeakFF]
  cases fstepF i s zf <;> simp

/-- The expansion of an `Lopn` of a body that passes `fuseOKL` emits, from an agreeing base,
    the events of the `Lopn`. -/
theorem fuseE_leak {E : List String} {L : List (Option String)} {c : List LinstrRM}
    (h : fuseOKL E L c = true) {k : Nat} {i : LinstrRM} (hk : c[k]? = some i)
    (hl : IsLopn i) (s s' : LstateM) (zf : Bool) (hA : Agree s s') :
    straightLeakFF (fuseE L k i) s' zf = instrLeakB s.reg i := by
  obtain ⟨-, hw, -⟩ := instr_of h hk
  have hone : straightLeakFF [i] s' zf = instrLeakB s.reg i := by
    rw [straightLeakFF_single]
    exact instrLeakB_agree hl fun n hn => hA.reg n (keptN_of_nameOK (nameOK_of_mem hw hn))
  unfold fuseE
  split
  · unfold fuseSiteExp
    split
    · rename_i hd o h1 s2 heq
      rw [straightLeakFF_quiet _ (by
        intro j hj r
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;>
          simp only [instrLeakB, storeImmEv, storeImmStruct?] <;> split <;> (try split) <;>
          simp [opLeakF])]
      obtain ⟨w, tag⟩ := i
      simp only at heq
      subst heq
      simp only [instrLeakB, storeImmEv, storeImmStruct?]
      split <;> (try split) <;> simp [opLeakF]
    · exact hone
  · exact hone

/-- **The fusion of the loop part of a body on the traced flag machine.** Under the
    hypotheses of `fuseMulHi_lsemFuelMemF_pre`, every terminating traced run of `pre ++ loop`
    from program counter `0` is matched by a terminating traced run of
    `pre ++ fuseMulHiRM loop` from the same state with the same trace. -/
theorem fuseMulHi_lsemFuelMemFLeak_pre {E : List String} {pre loop : List LinstrRM}
    (h : fuseOKL E (fuseLoPre pre loop) (pre ++ loop) = true) (fn : String) (s : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (r : LstateMF × List CTLeak)
    (hrun : lsemFuelMemFLeak (singletonProgM fn (pre ++ loop)) fuel s = some r) :
    ∃ fuel' t', lsemFuelMemFLeak (singletonProgM fn (pre ++ fuseMulHiRM loop)) fuel' s
      = some (t', r.2) := by
  have hw : ∀ i ∈ loop, wireOK i.1 = true := fun i hi =>
    wireOK_of_fuseOKL h i (List.mem_append_right _ hi)
  have heq : expI (fuseE (fuseLoPre pre loop)) (pre ++ loop) 0 = pre ++ fuseMulHiRM loop := by
    rw [expI_append, Nat.zero_add, fuseMulHiRM_eq loop hw]
    congr 1
    · exact expI_fuseE_none pre 0 (fun k hk => by
        rw [Nat.zero_add, fuseLoPre,
          List.getElem?_append_left (by rw [List.length_replicate]; exact hk)]
        simp [hk])
    · have := expI_fuseE_shift (L := fuseLoPre pre loop) (L' := fuseLo loop) pre.length
        (fun k => by simp [fuseLoPre, List.getElem?_append_right]) loop 0
      rwa [Nat.add_zero] at this
  have hR : RelI Agree (FInv E (pre ++ loop)) (fuseE (fuseLoPre pre loop)) (pre ++ loop) s s := by
    refine ⟨rfl, rfl, ?_, Agree.refl _, ?_⟩
    · rw [hpc]; rfl
    · rw [hpc]
      exact finv_start E _ 0 _ _ (blk_zero _) hE
  obtain ⟨fuel', t', ht', -⟩ := lsemFuelMemFLeak_expI (fn := fn) (expInv_fuse h)
    (fun k i hk hl s s' zf _ hA => fuseE_leak h hk hl s s' zf hA) fuel hR hrun
  rw [heq] at ht'
  exact ⟨fuel', t', ht'⟩

end Fuse

/-! ## 6. The virtual body of the image route -/

section Route

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiEntryM abiEntryM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)

/-- The flag-machine entry state of the virtual body of the image route at the machine
    state `sa`: the base `entryV` at the frame of the printed body `body`, the function
    `fn`, the zero flag clear. -/
abbrev routeEntry (σ : AbiLayout) (body : Lcmd) (ps : List (String × String)) (fn : String)
    (sa : AState) : LstateMF :=
  { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }

/-- **The trace of the virtual body of the image route.** Let the printed body `body`, the
    node `seeds ++ loop`, the renaming `ps`, the fusion flag `fuse` and the output `out` pass
    `routeB`, the seeds emit no event and the loop have no compile-time array operand. At a
    machine state with the stack parameters at entry (`AbiLayout.StackIn`), every
    terminating traced run of the node from `routeEntry` with trace `ℓ` is matched by a
    terminating traced run of the virtual body `virtB` from the same state with trace `ℓ` with
    array bases renamed by `renOf ps`. -/
theorem virtB_leak {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    (hg : routeB σ nm body seeds loop ps fuse out = true)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = []) (ha : ∀ i ∈ loop, NoCArr i.1)
    (sa : AState) (hst : σ.StackIn sa) (fn : String) (fuel : Nat) (t : LstateMF)
    (ℓ : List CTLeak)
    (hrun : lsemFuelMemFLeak (singletonProgM fn (seeds ++ loop)) fuel
      (routeEntry σ body ps fn sa) = some (t, ℓ)) :
    ∃ fuel' t', lsemFuelMemFLeak (singletonProgM fn (virtB σ nm seeds loop ps fuse)) fuel'
      (routeEntry σ body ps fn sa) = some (t', ℓ.map (renEv (renOf ps))) := by
  simp only [routeB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    List.contains_eq_mem, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hent⟩, hren⟩, hfuse⟩, -⟩ := hg
  have E := entryB_spec hent sa
  have R := renB_spec hren
  set fr := frameE body sa with hfrdef
  set b0 := entryV σ fr sa (unren ps) with hb0
  have habi : AbiEntryM σ sa b0 := entryV_abiEntry E.argF E.argG fun j hj => (R.unr j hj).1
  have hS := E.argSrc hst
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (un := unren ps) E.argF E.argG hS false
  have hb1 : ({ b0 with reg := { b0.reg with lpc := σ.args.length } } : LstateM).setLpc 0
      = b0 := rfl
  have hA : ∀ b2 z2, runStraightF (argBind σ nm ++ seeds) b0 false = some (b2, z2) →
      ∀ r, r ∈ loopNames loop → b2.larr (renOf ps r) = b2.larr r := by
    intro b2 z2 hb2 r _
    have hl := runStraightF_larr R.store hb2
    rw [hl]
    rcases renOf_cases ps r with he | ⟨p, hp, rfl, he⟩
    · rw [he]
    · rw [he]
      show (abiEntryM σ sa).larr (unren ps p.2) = (abiEntryM σ sa).larr (unren ps p.1)
      rw [unren_target R.nd hp, unren_of_not_target fun q hq => R.ts p hp q hq]
  obtain ⟨f1, t1, ht1⟩ := src_chain_leak fn (argBind σ nm) seeds loop ps (· ∈ loopNames loop)
    (movesOf_isLopn _) R.lopn R.ctl R.cond R.ren R.names R.nd R.ts R.tgt R.fresh ha
    (movesOf_quiet _) hqs b0 _ false rfl hpr0 hb1 hA fuel t ℓ hrun
  cases fuse with
  | false => exact ⟨f1, t1, ht1⟩
  | true =>
      simp only [Bool.true_eq_false, false_or] at hfuse
      obtain ⟨f2, t2, ht2⟩ := fuseMulHi_lsemFuelMemFLeak_pre hfuse.1 fn _ rfl (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact e64_of_abiEntryM habi x hx
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          exact congrArg (·.1) (entryV_srcOf (un := unren ps) hS ha)) f1 _ ht1
      exact ⟨f2, t2, ht2⟩

end Route

/-! ## 7. The certified node has no compile-time array operand -/

section Cert

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (loopAdvanceRM loopTouchRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon (canonNodeRM canonSeedsRM
  canonBodyRM canonFeedback)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd (ComExpOK
  forLoopLcmdNRtRM_map_eq_canonNodeRM_expand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert (exportCertB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop (certNode loopCertB
  loopCertB_spec loopInvOps)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (ComOpsPlain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (immShiftExpand)

theorem noCArr_of_arrOK {i : LinstrR} (h : ArrOK i) : NoCArr i := by
  cases i with
  | Lopn ds o ss =>
      intro x hx b k he
      subst he
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨r, hr⟩ := h.1 _ hx
        cases hr
      · exact h.2 _ hx b k rfl
  | _ => trivial

theorem noCArr_renRM (τ : String → String) {i : LinstrRM} (h : NoCArr i.1) :
    NoCArr (renRM τ i).1 := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o ss =>
      intro x hx b k he
      subst he
      simp only [← List.map_append, List.mem_map] at hx
      obtain ⟨y, hy, hye⟩ := hx
      rw [renOperand_eq_arr] at hye
      exact h y hy b k hye
  | _ => trivial

theorem noCArr_shiftImage {i : LinstrRM} (h : NoCArr i.1) : NoCArr (shiftImage i).1 := by
  unfold shiftImage immShiftExpand
  split
  · split <;> simp [NoCArr]
  · exact h

/-- Every instruction of the canonicalised node of an update in the fragment's op set has no
    compile-time array operand. -/
theorem canonNodeRM_noCArr {invTys : Ctxt jasminDialect} (τ : String → String)
    (d : Nat) (out c : String) {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hops : ComOpsPlain update) (absent : Bool) (regs : List String) :
    ∀ i ∈ canonNodeRM τ d out c update absent regs, NoCArr i.1 := by
  intro i hi
  simp only [canonNodeRM, guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge,
    canonBodyRM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hi
  rcases hi with hi | (rfl | rfl | rfl | ((⟨j, hj, rfl⟩ | (hi | hi) | hi) | rfl | rfl)) | rfl
  · simp only [canonSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [NoCArr]
  · simp [NoCArr]
  · trivial
  · trivial
  · exact noCArr_renRM τ (noCArr_of_arrOK (straightOpsMem_arrOK _ update hops _ j hj))
  · unfold canonFeedback at hi
    split at hi
    · simp at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      simp [NoCArr]
  · simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp [NoCArr]
  · simp only [loopTouchRM, List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    simp [NoCArr]
  · simp [NoCArr]
  · trivial
  · trivial

/-- **The certified node has no compile-time array operand.** For a single-loop program whose
    update is `ComExpOK` and which passes `loopCertB`, every instruction of `certNode` has no
    compile-time array operand. -/
theorem certNode_noCArr {Γ : Ctxt jasminDialect} {w n : Nat} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c) :
    ∀ i ∈ certNode update invs out c, NoCArr i.1 := by
  obtain ⟨out', c', hi', hc', hx, -⟩ := loopCertB_spec hcert
  rw [hi] at hi'
  cases hi'
  rw [hcn] at hc'
  cases hc'
  have hX := exportCertB_sound hx
  unfold certNode
  rw [forLoopLcmdNRtRM_map_eq_canonNodeRM_expand _ update (ComExpOK.opsPlain _ hexp)
    hX.loopRen hX.nodeRen hX.ret, flatMap_immShiftExpand]
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact noCArr_shiftImage (canonNodeRM_noCArr _ _ _ _ update (ComExpOK.opsPlain _ hexp) _ _ j hj)

/-- The renamed seed moves of a loop node from registers emit no event. -/
theorem loopSeedsRM_quiet (τ : String → String) (d : Nat) (acc out c : String) :
    ∀ i ∈ (JasminLsemExportLift.loopSeedsRM d acc (.reg out) (.reg c)).map (renRM τ),
      ∀ r, instrLeakB r i = [] := by
  intro i hi r
  simp only [JasminLsemExportLift.loopSeedsRM, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

/-! ## 8. The virtual body from the source events -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (routeB virtB entryV frameE
  unren routeB_abiEntry)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf
  singleLoop_export_faithful_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (singleLoop)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels PubEqV)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- **The trace of the virtual body of the image route from the source events.** Let the
    single-loop program pass `loopCertB` with an update in `ArrMemN` with `ComExpOK`, and let
    its certified node be `seeds ++ loop` with seeds that emit no event, passing `routeB`
    against the printed body `body`. Every terminating traced run of the virtual body `virtB`
    from `routeEntry` at a machine state `sa` with the stack parameters at entry emits `loopT`
    of the source events at the valuation `σ` reads off `sa`, with array bases renamed by
    `renOf ps`. -/
theorem virtB_leak_source (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    {σ : AbiLayout} {nm : String → String} {body : Lcmd} {seeds loop : List LinstrRM}
    {ps : List (String × String)} {fuse : Bool} {outR : String}
    (hg : routeB σ nm body seeds loop ps fuse outR = true)
    (hnode : seeds ++ loop = certNode update invs out c)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = [])
    (sa : AState) (hst : σ.StackIn sa) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V)
    (fn : String) {ℓ : List CTLeak}
    (hr : FRun (singletonProgM fn (virtB σ nm seeds loop ps fuse)) (routeEntry σ body ps fn sa)
      ℓ) :
    ℓ = (loopT Pj (X86Backend.ExportCertFaithful.certTau Γ.length (regName Γ.length) out update
        (loopInvOps invs)) update
      (ComL.ctLeak (jLeakModel Pj) (singleLoop update count init invs) V)).map
        (renEv (renOf ps)) := by
  have habi := routeB_abiEntry hg sa
  obtain ⟨out', c', hi', hc', -, hrun⟩ :=
    singleLoop_export_faithful_abi update count init invs outArg inArgs abiArgs hupd hexp hcert
  rw [hi] at hi'
  cases hi'
  rw [hcn] at hc'
  cases hc'
  obtain ⟨k, t, hk, -⟩ := hrun σ sa V fn _ false hV habi
  have hfst := lsemFuelMemFLeak_fst (singletonProgM fn (certNode update invs out c)) k
    (routeEntry σ body ps fn sa)
  rw [hk] at hfst
  obtain ⟨r0, hr0, -⟩ := Option.map_eq_some_iff.mp hfst
  have hsrc := singleLoop_leak_abi Pj update count init invs outArg inArgs abiArgs hupd hexp
    hcert out c hi hcn σ sa V fn _ false hV habi ⟨k, r0.1, hr0⟩
  have ha : ∀ i ∈ loop, NoCArr i.1 := fun i hi0 =>
    certNode_noCArr update count init invs outArg inArgs abiArgs hexp hcert out c hi hcn i
      (hnode ▸ List.mem_append_right _ hi0)
  rw [← hnode] at hr0
  obtain ⟨f', t', ht'⟩ := virtB_leak hg hqs ha sa hst fn k r0.1 r0.2 hr0
  rw [fRun_unique hr ⟨f', t', ht'⟩, hsrc]

/-- Two entry states of the virtual body of the image route at machine states with the
    stack parameters at entry whose valuations, as `σ` reads them off, agree on the positions
    `L` marks public. -/
def RouteEntryPub (σ : AbiLayout) (body : Lcmd) (ps : List (String × String)) (fn : String)
    {Γ : Ctxt jasminDialect} (L : Labels Γ) (s₁ s₂ : LstateMF) : Prop :=
  ∃ (sa₁ sa₂ : AState) (V₁ V₂ : Ctxt.Valuation Γ), AbiValOf σ sa₁ V₁ ∧ AbiValOf σ sa₂ V₂
    ∧ PubEqV L V₁ V₂ ∧ σ.StackIn sa₁ ∧ σ.StackIn sa₂ ∧ s₁ = routeEntry σ body ps fn sa₁
    ∧ s₂ = routeEntry σ body ps fn sa₂

/-- **Constant time of the virtual body of the image route from the source.** Under the
    hypotheses of `virtB_leak_source`, if the source events of the single-loop program are
    constant time for the labels `L`, the virtual body is constant time on the flag machine
    from the entry states `routeEntry` of machine states whose valuations agree on the public
    labels. -/
theorem virtB_memFCT (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    {σ : AbiLayout} {nm : String → String} {body : Lcmd} {seeds loop : List LinstrRM}
    {ps : List (String × String)} {fuse : Bool} {outR : String}
    (hg : routeB σ nm body seeds loop ps fuse outR = true)
    (hnode : seeds ++ loop = certNode update invs out c)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = []) (L : Labels Γ) (fn : String)
    (hct : CT.ConstantTime (PubEqV L)
      (ComL.ctLeak (jLeakModel Pj) (singleLoop update count init invs))) :
    MemFCT (singletonProgM fn (virtB σ nm seeds loop ps fuse))
      (RouteEntryPub σ body ps fn L) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨sa₁, sa₂, V₁, V₂, hV₁, hV₂, hp, hs₁, hs₂, rfl, rfl⟩ r₁ r₂
  rw [virtB_leak_source Pj update count init invs outArg inArgs abiArgs hupd hexp hcert out c
      hi hcn hg hnode hqs sa₁ hs₁ V₁ hV₁ fn r₁,
    virtB_leak_source Pj update count init invs outArg inArgs abiArgs hupd hexp hcert out c
      hi hcn hg hnode hqs sa₂ hs₂ V₂ hV₂ fn r₂, hct V₁ V₂ hp]

end Cert

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak
