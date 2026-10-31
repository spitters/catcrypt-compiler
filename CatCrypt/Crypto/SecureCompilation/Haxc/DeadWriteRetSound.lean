/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend

@[expose] public section

set_option autoImplicit false

/-!
# Soundness of the dead-write elimination of the region post-pass

`deadWriteRet` (the last stage of `regionPostFuse`) removes, from a body that is
straight-line up to a final `Lret`, the candidate pure register writes that
`OwnedLprogTV.deadWriteMarks` marks: a `MUL`, `IMUL`, `MOV`, `MOVQ` or `LOAD:64` into a
register whose next access among the kept instructions after it is a write of a widening
multiply `MULX` (`OwnedLprogTV.killedByMulx`).

This module proves that the marks are dead at the level of the symbolic step
(`OwnedLprogTV.dropOkW`), which is the liveness condition of the completeness theorem
`OwnedLprogTV.dropDeadWrite_ownedCheckM_complete`. The proof follows the definition of the
marks: a register is pending while it is killed by a later `MULX` (`killedByMulx`); a kept
instruction does not read a pending register; the `MULX` that kills it writes it and ends
its pending state; no register is killed at the end of the body. Together with the
soundness of the checker, `OwnedLprogTV.ownedCheckM_sound`, this gives the semantic
theorem at the flag machine `lsemFuelMemF` (the x86 instance of `VIR.LprogIsa.Isa.lsemFuelMemF`).

The halting runs are those of the typed body without its trailing `Lret`
(`OwnedLprogTV.dropRet`): the flag machine takes no step at `Lret`, so a run of a body that
returns is the run of its straight part to its end.

## Side conditions

* `deadWriteStepOK tg x`, checked on every instruction: the symbolic step of a candidate
  pure register write into `d` writes no name other than `d` (`OwnedLprogTV.wrOf`); a
  widening multiply writes both of its destinations in its symbolic step. These are
  properties of single instructions under the typing `tg`, independent of the elimination;
  they are statements about the symbolic memory step `symMem` at an arbitrary typing (under
  an array tag the step of a move can write an array name, and outside the symbolic fragment
  `wrOf` is empty), so they are hypotheses, decided per instruction. That a candidate write
  is flag-quiet holds at every typing (`flagQuiet_of_pureWrDst`).
* `symRun (dropRet (typeBody tg body)) SSt.start ≠ .unk`: the symbolic run of the source
  body is inside the fragment of the symbolic step.

## Main results

* `flagQuiet_of_pureWrDst`: a candidate pure register write is flag-quiet at every typing.
* `dropOkW_deadWriteMarks`: the marks of `deadWriteMarks` are dead flag-quiet writes.
* `keptL_deadWriteMarks_ne_nil`: the elimination keeps an instruction of a non-empty body.
* `dropDeadWriteBody_lsemFuelMemF`: the elimination on a straight-line body preserves
  halting runs up to the observed registers, the arrays and the word memory.
* `deadWriteRet_lsemFuelMemF`: the same for `deadWriteRet` on a body ending in `Lret`;
  `deadWriteRet_x86Isa_lsemFuelMemF`: the same at the run of the x86 instruction-set record.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.DeadWriteRetSound

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF LstateMF cmpArgs?
  carryArgs? aluFlagOp?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-! ## 1. The per-instruction side condition -/

/-- A widening multiply `MULX [lo, hi] [b]` (or `MULXMEM`, at any width tag): its two
    destinations. -/
def mulxDsts? (x : LinstrR) : Option (String × String) :=
  match x with
  | .Lopn [.reg lo, .reg hi] opn [_] =>
      if stripWidthTag opn == "MULX" || stripWidthTag opn == "MULXMEM" then some (lo, hi)
      else none
  | _ => none

/-- **The side condition of one instruction** under the typing `tg`: the symbolic step of
    a candidate pure register write into `d` (`pureWrDst?`) writes no name other than `d`;
    the symbolic step of a widening multiply writes both of its destinations. -/
def deadWriteStepOK (tg : LinstrR → MemTag) (x : LinstrR) : Bool :=
  (match pureWrDst? x with
    | some d => (wrOf (x, tg x)).all (· == d)
    | none => true) &&
  (match mulxDsts? x with
    | some (lo, hi) => (wrOf (x, tg x)).contains lo && (wrOf (x, tg x)).contains hi
    | none => true)

/-- **A candidate pure register write is flag-quiet** under every tag: its mnemonic
    (`MUL`, `IMUL`, `MOV` at any width tag, `MOVQ`, `LOAD:64`) is no flag compare, no
    carry-family operation, no arithmetic or logical operation whose flags the machine
    records, and no indexed store. -/
theorem flagQuiet_of_pureWrDst {x : LinstrR} {d : String} (h : pureWrDst? x = some d)
    (t : MemTag) : flagQuiet (x, t) = true := by
  unfold pureWrDst? at h
  split at h
  · next d' opn srcs =>
      split_ifs at h with hm
      have ne : ∀ m ∈ ["CMP", "ADC", "SBB", "ADCX", "ADOX", "ADD", "SUB", "AND", "OR", "XOR"],
          opn ≠ withWidthTag 64 m := by
        intro m hm' e
        subst e
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
        rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          revert hm <;> decide +kernel
      have ns : opn ≠ "STOREIDX" := by
        rintro rfl
        revert hm
        decide +kernel
      have nz : opn ≠ "ZEROARR" := by
        rintro rfl
        revert hm
        decide +kernel
      have nsi : opn ≠ "STOREIMM" := by
        rintro rfl
        revert hm
        decide +kernel
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at ne
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := ne
      unfold flagQuiet cmpArgs? carryArgs? aluFlagOp? arrQuiet
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · split <;> simp_all
      · split <;> simp_all
      · split <;> simp_all
      · split
        · simp only [storeStruct?]
          split <;> simp_all
        · split <;> simp_all
        · simp only [storeImmStruct?]
          split <;> simp_all
        · rfl
  · cases h

theorem mulxDsts?_of_mulxWrites {q : String} {x : LinstrR} (h : mulxWrites q x = true) :
    ∃ lo hi, mulxDsts? x = some (lo, hi) ∧ (q = lo ∨ q = hi) := by
  unfold mulxWrites at h
  split at h
  · next lo hi opn b =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      refine ⟨lo, hi, ?_, h.2⟩
      simp only [mulxDsts?]
      rw [ite_eq_left (by simpa using h.1)]
  · cases h

/-- A widening multiply that passes the side condition writes, in its symbolic step, every
    register it kills. -/
theorem mem_wrOf_of_mulxWrites {tg : LinstrR → MemTag} {q : String} {x : LinstrR}
    (hok : deadWriteStepOK tg x = true) (h : mulxWrites q x = true) :
    q ∈ wrOf (x, tg x) := by
  obtain ⟨lo, hi, hm, hq⟩ := mulxDsts?_of_mulxWrites h
  simp only [deadWriteStepOK, hm, Bool.and_eq_true, List.contains_iff_mem] at hok
  rcases hq with rfl | rfl
  · exact hok.2.1
  · exact hok.2.2

/-! ## 2. The marks are dead flag-quiet writes -/

/-- **The liveness condition of the elimination.** For a body whose instructions pass
    `deadWriteStepOK tg`, and a list `D` of registers each killed by a later widening
    multiply (`killedByMulx`) among the kept instructions of `deadWriteMarks body`, the
    typed marks pass `dropOkW D`: every marked instruction is flag-quiet, no kept
    instruction reads a pending register, and no register is pending at the end. -/
theorem dropOkW_deadWriteMarks (tg : LinstrR → MemTag) :
    ∀ (body : Lcmd) (D : List String), (∀ i ∈ body, deadWriteStepOK tg i.li_i = true) →
      (∀ q ∈ D, killedByMulx q (deadWriteMarks body) = true) →
      dropOkW D (typeMarks tg (deadWriteMarks body)) = true
  | [], D, _, hD => by
      cases D with
      | nil => rfl
      | cons q _ =>
          have := hD q List.mem_cons_self
          simp [deadWriteMarks, killedByMulx] at this
  | i :: is, D, hs, hD => by
      have hsi := hs i List.mem_cons_self
      have hsr : ∀ j ∈ is, deadWriteStepOK tg j.li_i = true :=
        fun j hj => hs j (List.mem_cons_of_mem _ hj)
      generalize hb : (match pureWrDst? i.li_i with
        | some d => straightR i.li_i && killedByMulx d (deadWriteMarks is)
        | none => false) = b
      have hM : deadWriteMarks (i :: is) = (i, b) :: deadWriteMarks is := by
        rw [← hb]; rfl
      rw [hM] at hD ⊢
      cases b with
      | true =>
          cases hd : pureWrDst? i.li_i with
          | none => rw [hd] at hb; cases hb
          | some d =>
              rw [hd] at hb
              simp only [Bool.and_eq_true] at hb
              simp only [deadWriteStepOK, hd, Bool.and_eq_true, List.all_eq_true,
                beq_iff_eq] at hsi
              simp only [typeMarks, List.map_cons, dropOkW, Bool.and_eq_true]
              refine ⟨flagQuiet_of_pureWrDst hd _, ?_⟩
              refine dropOkW_deadWriteMarks tg is _ hsr (fun q hq => ?_)
              rcases List.mem_append.mp hq with hq | hq
              · rw [hsi.1 q hq]
                exact hb.2
              · have := hD q hq
                simpa [killedByMulx] using this
      | false =>
          simp only [typeMarks, List.map_cons, dropOkW, Bool.and_eq_true, List.all_eq_true]
          have hk : ∀ q ∈ D, (straightR i.li_i = true ∧ q ∉ symReads i.li_i) ∧
              (mulxWrites q i.li_i = true ∨
                (namesDstB q i.li_i = false ∧ killedByMulx q (deadWriteMarks is) = true)) := by
            intro q hq
            have := hD q hq
            simpa [killedByMulx] using this
          refine ⟨fun q hq => by simpa using (hk q hq).1.2, ?_⟩
          refine dropOkW_deadWriteMarks tg is _ hsr (fun q hq => ?_)
          obtain ⟨hqD, hqw⟩ := List.mem_filter.mp hq
          rcases (hk q hqD).2 with hm | ⟨-, hkq⟩
          · have := mem_wrOf_of_mulxWrites hsi hm
            simp [this] at hqw
          · exact hkq

/-- The last instruction of a non-empty body is unmarked: no register is killed after it. -/
theorem exists_unmarked_deadWriteMarks : ∀ (body : Lcmd), body ≠ [] →
    ∃ i, (i, false) ∈ deadWriteMarks body
  | [], h => absurd rfl h
  | [i], _ => ⟨i, by
      simp only [deadWriteMarks, List.mem_singleton, Prod.mk.injEq, true_and]
      split <;> simp [killedByMulx]⟩
  | i :: j :: rest, _ => by
      obtain ⟨k, hk⟩ := exists_unmarked_deadWriteMarks (j :: rest) (List.cons_ne_nil _ _)
      exact ⟨k, List.mem_cons_of_mem _ hk⟩

/-- The elimination keeps an instruction of a non-empty body: the last instruction is never
    marked, since no register is killed after it. -/
theorem keptL_deadWriteMarks_ne_nil (body : Lcmd) (h : body ≠ []) :
    keptL (deadWriteMarks body) ≠ [] := by
  obtain ⟨k, hk⟩ := exists_unmarked_deadWriteMarks body h
  intro he
  have : k ∈ keptL (deadWriteMarks body) :=
    List.mem_map.2 ⟨(k, false), List.mem_filter.2 ⟨hk, rfl⟩, rfl⟩
  rw [he] at this
  exact List.not_mem_nil this

/-! ## 3. The semantic theorems -/

/-- **The dead-write elimination on a straight-line body.** Let every instruction of `body`
    be straight-line (`straightR`) and pass `deadWriteStepOK tg`, and let the symbolic run
    of the typed body be inside the fragment. Every halting run of the flag machine on the
    typed body from a state at pc `0` of its function is matched by a halting run of the
    typed body `dropDeadWriteBody body` from the same state, and the end states agree on
    the registers `outs`, on the arrays and on the word memory (`Obs outs`). -/
theorem dropDeadWriteBody_lsemFuelMemF (outs : List String) (tg : LinstrR → MemTag)
    (body : Lcmd) (hs : ∀ i ∈ body, straightR i.li_i = true)
    (hok : ∀ i ∈ body, deadWriteStepOK tg i.li_i = true)
    (hfrag : symRun (typeBody tg body) SSt.start ≠ .unk)
    (fn : String) (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (fuel : Nat) (hrun : lsemFuelMemF (singletonProgM fn (typeBody tg body)) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemF (singletonProgM fn (typeBody tg (dropDeadWriteBody body)))
        fuel' s = some t' ∧ Obs outs t t' := by
  cases body with
  | nil => exact ⟨fuel, t, hrun, fun _ _ => rfl, rfl, rfl⟩
  | cons i is =>
      have hne : dropDeadWriteBody (i :: is) ≠ [] :=
        keptL_deadWriteMarks_ne_nil _ (List.cons_ne_nil _ _)
      have hw := dropOkW_deadWriteMarks tg (i :: is) [] hok (fun _ h => absurd h (by simp))
      have hc := dropDeadWrite_ownedCheckM_complete outs tg (i :: is) hne hs hw hfrag
      exact ownedCheckM_sound hc fn s t hfn hpc fuel hrun

/-- The typed body of a body ending in `Lret`, without its `Lret`, is the typed body of
    the instructions before it. -/
theorem dropRet_typeBody_of_ret (tg : LinstrR → MemTag) (pre : Lcmd) (r : Linstr)
    (hr : r.li_i = .Lret) : dropRet (typeBody tg (pre ++ [r])) = typeBody tg pre := by
  simp [dropRet, typeBody, hr, List.getLast?_append]

/-- **`deadWriteRet_lsemFuelMemF`: the dead-write elimination of the region post-pass
    preserves halting runs.** Let every instruction of `body` pass `deadWriteStepOK tg`
    and let the symbolic run of the typed body without its trailing `Lret` be inside the
    fragment. Every halting run of the flag machine on the typed body without its `Lret`
    (`dropRet`), from a state at pc `0` of its function, is matched by a halting run of the
    typed `deadWriteRet body` without its `Lret` from the same state; the end states agree
    on the registers `outs`, on the arrays and on the word memory (`Obs outs`). When
    `deadWriteRet` keeps the body, the two runs are the same run. -/
theorem deadWriteRet_lsemFuelMemF (outs : List String) (tg : LinstrR → MemTag)
    (body : Lcmd) (hok : ∀ i ∈ body, deadWriteStepOK tg i.li_i = true)
    (hfrag : symRun (dropRet (typeBody tg body)) SSt.start ≠ .unk)
    (fn : String) (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg body))) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemF (singletonProgM fn (dropRet (typeBody tg (deadWriteRet body))))
        fuel' s = some t' ∧ Obs outs t t' := by
  unfold deadWriteRet
  split
  · next r hr =>
      split
      · next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
          have hb : body = body.dropLast ++ [r] :=
            (List.dropLast_append_getLast? r hr).symm
          rw [hb, dropRet_typeBody_of_ret tg _ r hc.1] at hfrag hrun
          rw [dropRet_typeBody_of_ret tg _ r hc.1]
          exact dropDeadWriteBody_lsemFuelMemF outs tg _ hc.2
            (fun i hi => hok i (List.dropLast_subset _ hi)) hfrag fn s t hfn hpc fuel hrun
      · exact ⟨fuel, t, hrun, fun _ _ => rfl, rfl, rfl⟩
  · exact ⟨fuel, t, hrun, fun _ _ => rfl, rfl, rfl⟩

/-- **`deadWriteRet_lsemFuelMemF` at the run of the instruction-set record**: the same
    statement for the generic run `LprogIsa.Isa.lsemFuelMemF` at the x86 record
    `X86Isa.x86Isa`, which is the flag machine (`X86Isa.x86Isa_lsemFuelMemF`). -/
theorem deadWriteRet_x86Isa_lsemFuelMemF (outs : List String) (tg : LinstrR → MemTag)
    (body : Lcmd) (hok : ∀ i ∈ body, deadWriteStepOK tg i.li_i = true)
    (hfrag : symRun (dropRet (typeBody tg body)) SSt.start ≠ .unk)
    (fn : String) (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (fuel : Nat)
    (hrun : X86Backend.X86Isa.x86Isa.lsemFuelMemF
      (singletonProgM fn (dropRet (typeBody tg body))) fuel s = some t) :
    ∃ fuel' t', X86Backend.X86Isa.x86Isa.lsemFuelMemF
        (singletonProgM fn (dropRet (typeBody tg (deadWriteRet body)))) fuel' s = some t'
      ∧ Obs outs t t' := by
  rw [X86Backend.X86Isa.x86Isa_lsemFuelMemF] at hrun ⊢
  exact deadWriteRet_lsemFuelMemF outs tg body hok hfrag fn s t hfn hpc fuel hrun

end CatCrypt.Crypto.SecureCompilation.Haxc.DeadWriteRetSound
