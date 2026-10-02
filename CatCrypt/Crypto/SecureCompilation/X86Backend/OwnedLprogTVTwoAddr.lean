/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVDeadImm

/-!
# Completeness of the value checker for every route of two-address legalisation

`TwoAddrLegalize.legalizeInstr` rewrites an untied instruction `opn d, [a, b]` by one of four
routes: the flag route (`CMP`, `TEST`: the destination becomes the first source), the copy
route (`mov d, a; opn d, [d, b]`), the commutative route (`opn d, [d, a]` when `b = d`), and
the scratch route (`mov R15, a; opn R15, [R15, b]; mov d, R15`). This module proves that
`ownedCheckM` accepts a straight-line body against its legalisation `twoAddrBody` whenever each
instruction is accepted by its route (`twoAddrRouteWF`).

## Method

`twoAddrRoute` classifies an instruction by the branch `legalizeInstr` takes, and `legalR`
is the legalisation on the instruction alone (`legalizeInstr_eq_legalR`). The flag and the
commutative routes give one target instruction whose symbolic step equals the source step
(`chunk_of_symStep_eq`); the copy route is `chunk_copy`. The scratch route writes the scratch
register, which the source does not: when the body does not name the scratch register, the
runs proceed from states that agree off it (`SSt.EqvOn [reloadScratch]`). A chunk whose
instructions do not read the scratch register lifts to that relation (`chunkOn_of_chunk`,
through `tRun_on`); the scratch chunk is the copy chunk at the scratch register followed by a
move into the destination (`chunkOn_scratch`). The final check needs agreement on the observed
registers only (`ownedCheckM_of_resOn`), and the scratch register is not observed.

## Main definitions

* `TwoAddrRoute`, `twoAddrRoute`, `legalR`: the routes and the legalisation of an instruction.
* `twoAddrRouteWF`: an instruction whose route the checker accepts.
* `ResOn`, `ChunkOn`: agreement of runs off a set of registers.

## Main results

* `legalizeInstr_eq_legalR`, `twoAddrBody_typedR`: legalisation through `legalR`.
* `twoAddrRouteWF_of_twoAddrWF`: the copy-route condition implies the route condition.
* `chunk_route`, `chunkOn_route`, `chunkOn_scratch`: the chunks of the routes.
* `tRun_on`: runs of a list that does not read `D` from states that agree off `D`.
* `tRun_lockOn`: runs in lockstep off `D`.
* `ownedCheckM_of_resOn`: runs agreeing on the observed registers pass `ownedCheckM`.
* `twoAddr_ownedCheckM_complete`, `twoAddr_ownedCheckM_complete_const`: completeness of
  `ownedCheckM` for `TwoAddrLegalize.twoAddrBody` under `twoAddrRouteWF`;
  `twoAddr_ownedCheckM_complete_of_twoAddrWF`: under the copy-route condition `twoAddrWF`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLICM (operandReads instrReadRegs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
  (needsTie movFor tieBase commBases isRegOrImm legalizeInstr twoAddrBody bodyAvoids
   instrAvoids opAvoids mentionsScratch tiedOk)

/-! ## 1. Routes -/

/-- The branch `TwoAddrLegalize.legalizeInstr` takes on an instruction. -/
inductive TwoAddrRoute where
  /-- The instruction is kept. -/
  | keep
  /-- The flag route of `CMP` and `TEST`. -/
  | flag
  /-- The copy route, with the copy mnemonic. -/
  | copy (m : String)
  /-- The commutative route. -/
  | comm
  /-- The scratch route, with the copy mnemonic. -/
  | scratch (m : String)

/-- The route of an instruction, read off the branches of `legalizeInstr`. -/
def twoAddrRoute : LinstrR → TwoAddrRoute
  | .Lopn [.reg d] opn [a, b] =>
      if needsTie opn b && a != .reg d then
        match movFor opn with
        | none => .keep
        | some m =>
          if tieBase opn == "CMP" || tieBase opn == "TEST" then
            match a with
            | .reg _ => .flag
            | _ => .keep
          else if !isRegOrImm a then .keep
          else if !(LprogLeak.opNames b).contains d &&
              !(LprogAsmPrinter.isMemOperand (.reg d) && LprogAsmPrinter.isMemOperand a) then
            .copy m
          else if commBases.contains (tieBase opn) && b == .reg d
              && !(LprogAsmPrinter.isMemOperand (.reg d) && LprogAsmPrinter.isMemOperand a) then
            .comm
          else .scratch m
      else .keep
  | _ => .keep

/-- The legalisation of an instruction; `ok` enables the scratch route. -/
def legalR (ok : Bool) (x : LinstrR) : List LinstrR :=
  match x with
  | .Lopn [.reg d] opn [a, b] =>
      match twoAddrRoute x with
      | .keep => [x]
      | .flag =>
          match a with
          | .reg y => [.Lopn [.reg y] opn [.reg y, b]]
          | _ => [x]
      | .copy m => [.Lopn [.reg d] m [a], .Lopn [.reg d] opn [.reg d, b]]
      | .comm => [.Lopn [.reg d] opn [.reg d, a]]
      | .scratch m =>
          if ok then
            [.Lopn [.reg reloadScratch] m [a],
             .Lopn [.reg reloadScratch] opn [.reg reloadScratch, b],
             .Lopn [.reg d] m [.reg reloadScratch]]
          else [x]
  | _ => [x]

theorem legalizeInstr_eq_legalR (ok : Bool) (i : Linstr) :
    legalizeInstr ok i = (legalR ok i.li_i).map (fun y => ⟨i.li_ii, y⟩) := by
  obtain ⟨ii, x⟩ := i
  unfold legalizeInstr legalR twoAddrRoute
  dsimp only
  split
  · rename_i d opn a b
    dsimp only
    split_ifs <;> cases movFor opn <;> (try cases a) <;> rfl
  · rename_i hx
    split
    · rename_i d opn a b
      exact absurd rfl (hx d opn a b)
    · rfl

theorem twoAddrBody_typedR (tg : LinstrR → MemTag) (body : Lcmd) :
    typeBody tg (twoAddrBody body) =
      (typeBody tg body).flatMap
        (fun p => (legalR (bodyAvoids body) p.1).map fun x => (x, tg x)) := by
  unfold twoAddrBody LegalizeShiftImm.legalizeBody typeBody
  rw [List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  rw [legalizeInstr_eq_legalR, List.map_map]
  rfl

/-! ## 2. Routes the checker accepts -/

/-- The checker accepts the route of the instruction, for the observed registers `outs` and
    the typing `tg`: a kept instruction; the flag route, its target typed as the source; the
    copy route from a register; the commutative route from a register, its target typed as
    the source; the scratch route from a register, when the scratch register is not
    observed, the source is not a commutative operation reading its destination as second
    source, and the operation on the scratch register is typed as the source. -/
def twoAddrRouteWF (outs : List String) (tg : LinstrR → MemTag) (x : LinstrR) : Bool :=
  match x with
  | .Lopn [.reg d] opn [a, b] =>
      match twoAddrRoute x with
      | .keep => true
      | .flag =>
          match a with
          | .reg y => tg (.Lopn [.reg y] opn [.reg y, b]) == tg x
          | _ => true
      | .copy _ =>
          match a with
          | .reg _ => true
          | _ => false
      | .comm =>
          match a with
          | .reg y => tg (.Lopn [.reg d] opn [.reg d, .reg y]) == tg x
          | _ => false
      | .scratch _ =>
          match a with
          | .reg _ =>
              !outs.contains reloadScratch &&
                !(commBases.contains (stripWidthTag opn) && b == .reg d)
                && tg (.Lopn [.reg reloadScratch] opn [.reg reloadScratch, b]) == tg x
          | _ => false
  | _ => true

/-- The facts of the branch of an untied instruction with a copy mnemonic. -/
theorem twoAddrRoute_untied {d opn : String} {a b : LOperand} {r : TwoAddrRoute}
    (h : twoAddrRoute (.Lopn [.reg d] opn [a, b]) = r) (hr : r ≠ .keep) :
    needsTie opn b = true ∧ a ≠ .reg d ∧ ∃ m, movFor opn = some m := by
  unfold twoAddrRoute at h
  dsimp only at h
  by_cases h1 : (needsTie opn b && a != LOperand.reg d) = true
  · rw [if_pos h1] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
    cases hm : movFor opn with
    | none => rw [hm] at h; exact absurd h.symm hr
    | some m => exact ⟨h1.1, h1.2, m, rfl⟩
  · rw [if_neg h1] at h
    exact absurd h.symm hr

theorem twoAddrRoute_flag {d opn : String} {a b : LOperand}
    (h : twoAddrRoute (.Lopn [.reg d] opn [a, b]) = .flag) :
    (tieBase opn = "CMP" ∨ tieBase opn = "TEST") ∧ ∃ m, movFor opn = some m := by
  unfold twoAddrRoute at h
  dsimp only at h
  by_cases h1 : (needsTie opn b && a != LOperand.reg d) = true
  · rw [if_pos h1] at h
    cases hm : movFor opn with
    | none => rw [hm] at h; cases h
    | some m =>
        rw [hm] at h
        dsimp only at h
        refine ⟨?_, m, rfl⟩
        split_ifs at h with h2
        · simpa using h2
  · rw [if_neg h1] at h; cases h

theorem twoAddrRoute_copy {d opn m : String} {a b : LOperand}
    (h : twoAddrRoute (.Lopn [.reg d] opn [a, b]) = .copy m) :
    movFor opn = some m ∧ (LprogLeak.opNames b).contains d = false ∧
      tieBase opn ≠ "CMP" ∧ tieBase opn ≠ "TEST" := by
  unfold twoAddrRoute at h
  dsimp only at h
  by_cases h1 : (needsTie opn b && a != LOperand.reg d) = true
  · rw [if_pos h1] at h
    cases hm : movFor opn with
    | none => rw [hm] at h; cases h
    | some m' =>
        rw [hm] at h
        dsimp only at h
        split_ifs at h with h2 h3 h4
        · split at h <;> cases h
        · cases h
          simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h2
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at h4
          exact ⟨rfl, h4.1, h2.1, h2.2⟩
  · rw [if_neg h1] at h; cases h

theorem twoAddrRoute_comm {d opn : String} {a b : LOperand}
    (h : twoAddrRoute (.Lopn [.reg d] opn [a, b]) = .comm) :
    commBases.contains (tieBase opn) = true ∧ b = .reg d ∧ ∃ m, movFor opn = some m := by
  unfold twoAddrRoute at h
  dsimp only at h
  by_cases h1 : (needsTie opn b && a != LOperand.reg d) = true
  · rw [if_pos h1] at h
    cases hm : movFor opn with
    | none => rw [hm] at h; cases h
    | some m' =>
        rw [hm] at h
        dsimp only at h
        split_ifs at h with h2 h3 h4 h5
        · split at h <;> cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at h5
        exact ⟨h5.1.1, h5.1.2, m', rfl⟩
  · rw [if_neg h1] at h; cases h

theorem twoAddrRoute_scratch {d opn m : String} {a b : LOperand}
    (h : twoAddrRoute (.Lopn [.reg d] opn [a, b]) = .scratch m) :
    movFor opn = some m ∧ tieBase opn ≠ "CMP" ∧ tieBase opn ≠ "TEST" := by
  unfold twoAddrRoute at h
  dsimp only at h
  by_cases h1 : (needsTie opn b && a != LOperand.reg d) = true
  · rw [if_pos h1] at h
    cases hm : movFor opn with
    | none => rw [hm] at h; cases h
    | some m' =>
        rw [hm] at h
        dsimp only at h
        split_ifs at h with h2 h3 h4 h5
        · split at h <;> cases h
        · cases h
          simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h2
          exact ⟨rfl, h2.1, h2.2⟩
  · rw [if_neg h1] at h; cases h

theorem twoAddrRouteWF_of_twoAddrWF (outs : List String) (tg : LinstrR → MemTag) (x : LinstrR)
    (h : twoAddrWF x = true) : twoAddrRouteWF outs tg x = true := by
  simp only [twoAddrWF, Bool.or_eq_true] at h
  unfold twoAddrRouteWF
  split
  · rename_i d opn a b
    rcases h with h | h
    · have hk : twoAddrRoute (.Lopn [.reg d] opn [a, b]) = .keep := by
        simp only [tiedOk, Bool.or_eq_true, Bool.not_eq_true'] at h
        unfold twoAddrRoute
        rcases h with h | h
        · simp [h]
        · have : a = .reg d := by simpa using h
          simp [this]
      rw [hk]
    · match a, h with
      | .reg y, h =>
          simp only [copyRouteOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isSome_iff_exists]
            at h
          obtain ⟨⟨⟨⟨⟨⟨hn, hyd⟩, ⟨m, hm⟩⟩, hc⟩, ht⟩, hb⟩, hmem⟩ := h
          have hk : twoAddrRoute (.Lopn [.reg d] opn [.reg y, b]) = .copy m := by
            have hyd' : (LOperand.reg y != LOperand.reg d) = true := by simpa using hyd
            unfold twoAddrRoute
            simp only [hn, hyd', Bool.and_self, ↓reduceIte, hm, isRegOrImm, Bool.not_true,
              Bool.false_eq_true, hb, hmem]
            rw [if_neg (by simp [hc, ht])]
          rw [hk]
  · rfl

/-! ## 3. Chunks of the routes from states with one word for every name -/

/-- A target instruction whose symbolic step is the step of the source instruction from
    every state simulates it. -/
theorem chunk_of_symStep_eq {i j : LinstrRM} (h : ∀ ss, symStep j ss = symStep i ss) :
    Chunk i [j] := by
  intro ss ss' T T' e hI hS
  have hc := chunk_self i ss ss' T T' e hI hS
  have hj : tRun [j] ss' T' = tRun [i] ss' T' := by simp only [tRun, h]
  rw [hj]
  exact hc

theorem opn_of_movFor {opn m : String} (hm : movFor opn = some m) (base : String)
    (hb : tieBase opn = base) : opn = base ∨ opn = base ++ ":64" := by
  rcases TwoAddrLegalize.movFor_some hm with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl (h.trans hb)
  · exact Or.inr (h.trans (by rw [hb]))

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (sarStruct?) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
  (mulhiStruct? adcxStruct? adcxhiStruct? sbbStruct? sbbhiStruct?) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (castStruct? movImmStruct?) in
/-- The symbolic step of a flag operation does not depend on its destination. -/
theorem symStep_flag_dst {opn : String}
    (hopn : opn = "CMP" ∨ opn = "CMP:64" ∨ opn = "TEST" ∨ opn = "TEST:64")
    (d d' : String) (a b : LOperand) (τ : MemTag) (ss : SSt) :
    symStep (.Lopn [.reg d'] opn [a, b], τ) ss = symStep (.Lopn [.reg d] opn [a, b], τ) ss := by
  rcases hopn with rfl | rfl | rfl | rfl <;>
    cases τ <;> cases a <;> cases b <;> rfl

theorem opn_flag {opn m : String} (hm : movFor opn = some m)
    (h : tieBase opn = "CMP" ∨ tieBase opn = "TEST") :
    opn = "CMP" ∨ opn = "CMP:64" ∨ opn = "TEST" ∨ opn = "TEST:64" := by
  rcases h with h | h
  · rcases opn_of_movFor hm _ h with h' | h' <;> simp [h']
  · rcases opn_of_movFor hm _ h with h' | h' <;> simp [h']

theorem opn_comm {opn m : String} (hm : movFor opn = some m)
    (h : commBases.contains (tieBase opn) = true) : opn ∈ commOpns := by
  simp only [commBases, List.contains_iff_mem, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h | h <;> rcases opn_of_movFor hm _ h with h' | h' <;>
    (rw [h']; decide)

theorem avoidsReg_of_contains {d : String} {b : LOperand}
    (h : (LprogLeak.opNames b).contains d = false) : avoidsReg d b := by
  intro hd
  have : (LprogLeak.opNames b).contains d = true := List.contains_iff_mem.mpr hd
  rw [h] at this
  cases this

theorem opn_ne_cmp64 {opn : String} (h : tieBase opn ≠ "CMP") :
    opn ≠ withWidthTag 64 "CMP" := by
  rintro rfl
  exact h tieBase_cmp64

/-- **The chunk of a route.** An instruction whose route the checker accepts, and which is not
    rewritten through the scratch register, is simulated by its legalisation, for a typing that
    gives a two-source operation one tag whatever its first source. -/
theorem chunk_route {tg : LinstrR → MemTag} (htg : TagFirstSrc tg) {outs : List String}
    {ok : Bool} {x : LinstrR} (hw : twoAddrRouteWF outs tg x = true)
    (hs : ∀ m, twoAddrRoute x = .scratch m → ok = false) :
    Chunk (x, tg x) ((legalR ok x).map fun y => (y, tg y)) := by
  unfold legalR
  split
  · rename_i d opn a b
    cases hr : twoAddrRoute (.Lopn [.reg d] opn [a, b]) with
    | keep => exact chunk_self _
    | flag =>
        obtain ⟨hb, m, hm⟩ := twoAddrRoute_flag hr
        cases a with
        | reg y =>
            simp only [twoAddrRouteWF, hr, beq_iff_eq] at hw
            simp only [List.map_cons, List.map_nil, hw]
            exact chunk_of_symStep_eq (fun ss => symStep_flag_dst (opn_flag hm hb) d y _ b _ ss)
        | _ => exact chunk_self _
    | copy m =>
        obtain ⟨hm, hb, hc, -⟩ := twoAddrRoute_copy hr
        cases a with
        | reg y =>
            simp only [List.map_cons, List.map_nil]
            rw [htg d opn (.reg d) (.reg y) b]
            exact chunk_copy d y opn m b _ _ (TwoAddrLegalize.stripWidthTag_movFor hm)
              (avoidsReg_of_contains hb) (opn_ne_cmp64 hc)
        | _ => simp [twoAddrRouteWF, hr] at hw
    | comm =>
        obtain ⟨hc, rfl, m, hm⟩ := twoAddrRoute_comm hr
        obtain ⟨-, hyd, -⟩ := twoAddrRoute_untied hr (by simp)
        cases a with
        | reg y =>
            simp only [twoAddrRouteWF, hr, beq_iff_eq] at hw
            simp only [List.map_cons, List.map_nil, hw]
            have hyd' : y ≠ d := fun h => hyd (by rw [h])
            exact chunk_of_symStep_eq (fun ss => (symStep_comm (opn_comm hm hc) hyd' _ ss).symm)
        | _ => simp [twoAddrRouteWF, hr] at hw
    | scratch m =>
        rw [hs m hr]
        exact chunk_self _
  · exact chunk_self _

/-! ## 4. Runs from states that agree off a set of registers -/

/-- Two shared runs agree off the registers `D`: both succeed in one table with equal guards
    and states that agree off `D`, or both fail, or both are outside the fragment. -/
def ResOn (D : List String) : Tbl × SOut → Tbl × SOut → Prop
  | (T1, .ok s g), (T2, .ok s' g') => T1 = T2 ∧ s.EqvOn D s' ∧ g = g'
  | (_, .fail), (_, .fail) => True
  | (_, .unk), (_, .unk) => True
  | _, _ => False

/-- **Runs of a list that does not read `D`.** From states that agree off `D`, in one table,
    the runs of a list none of whose instructions reads a register of `D` agree off `D`. -/
theorem tRun_on (D : List String) : ∀ (js : List LinstrRM) (s1 s2 : SSt) (T : Tbl),
    (∀ j ∈ js, ∀ q ∈ symReads j.1, q ∉ D) → s1.EqvOn D s2 →
      ResOn D (tRun js s1 T) (tRun js s2 T)
  | [], _, _, _, _, e => ⟨rfl, e, rfl⟩
  | j :: js, s1, s2, T, hD, e => by
      have hR : ∀ q ∈ symReads j.1, s1.regs q = s2.regs q :=
        fun q hq => e.2 q (hD j (List.mem_cons_self ..) q hq)
      have hc := symStep_congr e.1 j hR
      rw [tRun_cons, tRun_cons]
      cases hs : symStep j s1 with
      | ok t1 g1 =>
          cases hs' : symStep j s2 with
          | ok t1' g1' =>
              rw [hs, hs'] at hc
              obtain ⟨rfl, hSame, ds, hw, hw', hds⟩ := hc
              dsimp only
              rw [SSt.Frm.ds_eq hw, SSt.Frm.ds_eq hw']
              obtain ⟨ds0, hw0, hr0⟩ := symStep_frm j hs
              have hd0 : ds = ds0 := List.append_cancel_right (hw.symm.trans hw0)
              obtain ⟨ds1, hw1, hr1⟩ := symStep_frm j hs'
              have hd1 : ds = ds1 := List.append_cancel_right (hw'.symm.trans hw1)
              obtain ⟨ht, hSm, hag, -⟩ := Tbl.internSt_on T ds hSame hds
              have eD : (T.internSt t1 ds).2.EqvOn D (T.internSt t1' ds).2 := by
                refine ⟨hSm, fun q hq => ?_⟩
                by_cases hqd : q ∈ ds
                · exact hag q hqd
                · rw [Tbl.internSt_keep _ _ _ q hqd, Tbl.internSt_keep _ _ _ q hqd,
                    hr0 q (hd0 ▸ hqd), hr1 q (hd1 ▸ hqd)]
                  exact e.2 q hq
              have ih := tRun_on D js _ _ (T.internSt t1 ds).1
                (fun j' hj' => hD j' (List.mem_cons_of_mem _ hj')) eD
              rw [ht]
              generalize tRun js (T.internSt t1 ds).2 (T.internSt t1 ds).1 = r1 at ih ⊢
              generalize tRun js (T.internSt t1' ds).2 (T.internSt t1 ds).1 = r2 at ih ⊢
              obtain ⟨R1, o1⟩ := r1
              obtain ⟨R2, o2⟩ := r2
              cases o1 <;> cases o2 <;> simp_all [ResOn, runAfter, SOut.after]
          | fail => rw [hs, hs'] at hc; cases hc
          | unk => rw [hs, hs'] at hc; cases hc
      | fail =>
          cases hs' : symStep j s2 <;> rw [hs, hs'] at hc <;> simp only [SOut.RelOn] at hc
          trivial
      | unk =>
          cases hs' : symStep j s2 <;> rw [hs, hs'] at hc <;> simp only [SOut.RelOn] at hc
          trivial

theorem SSt.EqvOn.of_eqv {D : List String} {s t u : SSt} (h1 : s.Eqv t) (h2 : t.EqvOn D u) :
    s.EqvOn D u :=
  ⟨⟨h1.2.1.trans h2.1.1, h1.2.2.1.trans h2.1.2.1, h1.2.2.2.1.trans h2.1.2.2.1,
    h1.2.2.2.2.trans h2.1.2.2.2⟩, fun q hq => (congrFun h1.1 q).trans (h2.2 q hq)⟩

/-- The source description `o` and the target run `r` agree off the registers `D`. -/
def ResD (D : List String) (T' : Tbl) : SOut → Tbl × SOut → Prop
  | .ok s g, (T'', .ok s' g') => T'' = T' ∧ s.EqvOn D s' ∧ g = g'
  | .fail, (_, .fail) => True
  | .unk, (_, .unk) => True
  | _, _ => False

/-- The target instructions `js` simulate the source instruction `i` off the registers `D`:
    from states that agree off `D`, the run of `js` in a table holding what the run of `i`
    interns agrees off `D` with the run of `i`. -/
def ChunkOn (D : List String) (i : LinstrRM) (js : List LinstrRM) : Prop :=
  ∀ (ss ss' : SSt) (T T' : Tbl), ss.EqvOn D ss' → ss.Inv T.ents.size →
    (tRun [i] ss T).1.Sub T' → ResD D T' (tRun [i] ss T).2 (tRun js ss' T')

/-- The state `ss'` with the registers of `D` taken from `ss`. -/
def SSt.takeOn (D : List String) (ss ss' : SSt) : SSt :=
  { ss' with regs := fun q => if q ∈ D then ss.regs q else ss'.regs q }

theorem SSt.EqvOn.eqv_takeOn {D : List String} {ss ss' : SSt} (e : ss.EqvOn D ss') :
    ss.Eqv (SSt.takeOn D ss ss') := by
  refine ⟨funext fun q => ?_, e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2⟩
  by_cases hq : q ∈ D
  · simp [SSt.takeOn, hq]
  · simp [SSt.takeOn, hq, e.2 q hq]

theorem SSt.takeOn_eqvOn (D : List String) (ss ss' : SSt) :
    (SSt.takeOn D ss ss').EqvOn D ss' :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, fun q hq => by simp [SSt.takeOn, hq]⟩

/-- **A chunk that does not read `D` simulates off `D`.** -/
theorem chunkOn_of_chunk {D : List String} {i : LinstrRM} {js : List LinstrRM}
    (hc : Chunk i js) (hD : ∀ j ∈ js, ∀ q ∈ symReads j.1, q ∉ D) : ChunkOn D i js := by
  intro ss ss' T T' e hI hS
  have h1 := hc ss (SSt.takeOn D ss ss') T T' e.eqv_takeOn hI hS
  have h2 := tRun_on D js (SSt.takeOn D ss ss') ss' T' hD (SSt.takeOn_eqvOn D ss ss')
  generalize (tRun [i] ss T).2 = o at h1 ⊢
  generalize tRun js (SSt.takeOn D ss ss') T' = r1 at h1 h2
  generalize tRun js ss' T' = r2 at h2 ⊢
  obtain ⟨R1, o1⟩ := r1
  obtain ⟨R2, o2⟩ := r2
  cases o <;> cases o1 <;> cases o2 <;> simp only [Res, ResOn, ResD] at h1 h2 ⊢
  · obtain ⟨rfl, e1, rfl⟩ := h1
    obtain ⟨rfl, e2, rfl⟩ := h2
    exact ⟨rfl, SSt.EqvOn.of_eqv e1 e2, rfl⟩

/-- **Runs in lockstep off `D`.** -/
theorem tRun_lockOn (D : List String) (f : LinstrRM → List LinstrRM) : ∀ (is : List LinstrRM),
    (∀ i ∈ is, ChunkOn D i (f i)) → ∀ (ss ss' : SSt) (T T' : Tbl), ss.EqvOn D ss' →
      ss.Inv T.ents.size → (tRun is ss T).1.Sub T' →
        ResD D T' (tRun is ss T).2 (tRun (is.flatMap f) ss' T')
  | [], _, ss, ss', T, T', e, _, _ => ⟨rfl, e, rfl⟩
  | i :: is, hf, ss, ss', T, T', e, hI, hS => by
      have hc := hf i (List.mem_cons_self ..)
      have hc' := hc ss ss' T T' e hI
      rw [List.flatMap_cons, tRun_append]
      rw [tRun_cons] at hS ⊢
      rw [tRun_cons] at hc'
      simp only [tRun] at hc'
      cases hs : symStep i ss with
      | ok s1 g1 =>
          rw [hs] at hS hc'
          dsimp only at hS hc' ⊢
          generalize hds : s1.wr.take (s1.wr.length - ss.wr.length) = ds at hS hc' ⊢
          generalize hp : T.internSt s1 ds = p at hS hc' ⊢
          obtain ⟨P, ps⟩ := p
          simp only [runAfter] at hS hc' ⊢
          have hc2 := hc' ((tRun_sub is ps P).trans hS)
          generalize hq : tRun (f i) ss' T' = q at hc2 ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo with
          | ok s'' g'' =>
              obtain ⟨hQ, e2, hg⟩ := hc2
              rw [hQ] at hq
              simp only [List.append_nil] at hg
              subst hg
              have hR1 := symStep_refsLt i hI.1 hs
              obtain ⟨ds0, hw0, hr0⟩ := symStep_frm i hs
              have hd0 : ds = ds0 := hds ▸ SSt.Frm.ds_eq hw0
              have hI2 : ps.Inv P.ents.size := by
                have := Tbl.internSt_inv (T := T) ds hR1.1 (fun r hr => by
                  rw [hr0 r (hd0 ▸ hr)]; exact hI.2.1 r)
                rw [hp] at this
                exact this
              have ih := tRun_lockOn D f is (fun j hj => hf j (List.mem_cons_of_mem _ hj)) ps
                s'' P T' e2 hI2 hS
              rw [hQ]
              simp only [runThen, runAfter]
              generalize tRun is ps P = r1 at ih ⊢
              generalize tRun (is.flatMap f) s'' T' = r2 at ih ⊢
              obtain ⟨R1, o1⟩ := r1
              obtain ⟨R2, o2⟩ := r2
              cases o1 <;> cases o2 <;> simp_all [ResD, SOut.after]
          | fail => simp [ResD, SOut.after] at hc2
          | unk => simp [ResD, SOut.after] at hc2
      | fail =>
          rw [hs] at hc'
          dsimp only at hc' ⊢
          generalize tRun (f i) ss' T' = q at hc' ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo <;> simp_all [ResD, runThen]
      | unk =>
          rw [hs] at hc'
          dsimp only at hc' ⊢
          generalize tRun (f i) ss' T' = q at hc' ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo <;> simp_all [ResD, runThen]

/-! ## 5. The check of runs that agree on the observed registers -/

/-- **The check of one falling block, on the observed registers.** `blockOkR_fall` with
    states that agree on the observed registers and on every array. -/
theorem blockOkR_fall_on {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} {b b' : AllocCheck.LcmdCFG.Block} {T1 : Tbl} {s s' : SSt}
    {g : List SG} (he : ∀ r ∈ outs, s.regs r = s'.regs r) (ha : s.arrs = s'.arrs)
    (hI : s.Inv T1.ents.size) (hg : ∀ x ∈ g, x.refsLt T1.ents.size = true)
    (hE : TBnd T1.ents)
    (hL : LiveCov (L 0) (blockNeed outs L (.fall none) (T1, .ok s g, .ok s' g) B b))
    (hlast : ∀ p, B[b.stop - 1]? = some p → AllocCheck.LcmdCFG.isTermR p.1 = false) :
    blockOkR outs L 0 (.fall none) (T1, .ok s g, .ok s' g) B B' b b' = true := by
  simp only [blockNeed, AllocCheck.LcmdCFG.Term.succs, AllocCheck.LcmdCFG.Term.halts,
    Option.toList, List.flatMap_nil, List.any_nil, ↓reduceIte, Bool.false_or,
    Bool.or_false, Bool.true_and, Option.map_none, Option.getD_none, List.append_nil] at hL
  simp only [blockOkR, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [guardsT, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    refine ⟨fun x hx => hx.elim (hg x) (hg x), fun x hx => ⟨by simpa using hx, ?_⟩⟩
    simp only [okInGT, Bool.and_eq_true]
    obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
    refine ⟨SG.normT_refsLt hE (hg y hy) x hxy, okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
    · simp only [List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl ⟨x, hx, hv⟩)
    · simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inl (Or.inl ⟨x, hx, h⟩)
  · cases hb : B[b.stop - 1]? with
    | none => simp [termAgreeT]
    | some p =>
        have hp := hlast p hb
        obtain ⟨x, τ⟩ := p
        cases x <;> simp_all [termAgreeT, AllocCheck.LcmdCFG.isTermR]
  · simp only [exitAgreeT, AllocCheck.LcmdCFG.Term.succs, Option.toList, List.all_nil,
      AllocCheck.LcmdCFG.Term.halts, Bool.not_true, Bool.false_or, Bool.true_and,
      Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    refine ⟨fun r hr => ⟨he r hr, ?_⟩, fun q hq => ⟨congrFun ha q, ?_⟩⟩
    · simp only [okInT, Bool.and_eq_true]
      refine ⟨hI.1.1 r, okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
      · simp only [List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨r, hr, hv⟩)
      · simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inl (Or.inr ⟨r, hr, h⟩)
    · simp only [okInAT, Bool.and_eq_true]
      refine ⟨hI.1.2.1 q, okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
      · simp only [List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨q, by simpa using hq, hv⟩
      · simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨q, by simpa using hq, h⟩

/-- **Completeness for straight-line bodies, off unobserved registers.** Two non-empty
    straight-line typed bodies whose shared runs agree off registers `D` none of which is
    observed, the source run being inside the fragment, pass `ownedCheckM`. -/
theorem ownedCheckM_of_resOn (outs : List String) (D : List String) (hD : ∀ q ∈ D, q ∉ outs)
    {B B' : List LinstrRM} (hne : B ≠ [])
    (hne' : B' ≠ []) (hs : ∀ p ∈ B, straightR p.1 = true)
    (hs' : ∀ p ∈ B', straightR p.1 = true)
    (hres : ResD D (tRun B SSt.start Tbl.empty).1 (tRun B SSt.start Tbl.empty).2
      (tRun B' SSt.start (tRun B SSt.start Tbl.empty).1))
    (hunk : (tRun B SSt.start Tbl.empty).2 ≠ .unk) : ownedCheckM outs B B' = true := by
  have hG := cfgOf_straight (wl := B.map Prod.fst) (by simpa using hne)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs p hp)
  have hG' := cfgOf_straight (wl := B'.map Prod.fst) (by simpa using hne')
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hs' p hp)
  unfold ownedCheckM
  rw [hG, hG']
  dsimp only
  have hsz : ∀ n, (straightCFG n).blocks.size = 1 := fun _ => rfl
  have hterm : ∀ n, ((straightCFG n).blk 0).term = .fall none := fun _ => rfl
  generalize hp : tRun B SSt.start Tbl.empty = p at hres hunk
  obtain ⟨T1, o⟩ := p
  have hR : (runsOf B B' (straightCFG (B.map Prod.fst).length)
      (straightCFG (B'.map Prod.fst).length))[0]? =
      some (blockRuns B B' ((straightCFG (B.map Prod.fst).length).blk 0)
        ((straightCFG (B'.map Prod.fst).length).blk 0) (.fall none)) := by
    simp [runsOf, hsz, hterm]
  have hBR : blockRuns B B' ((straightCFG (B.map Prod.fst).length).blk 0)
      ((straightCFG (B'.map Prod.fst).length).blk 0) (.fall none) =
      ((tRun B' SSt.start T1).1, o, (tRun B' SSt.start T1).2) := by
    simp only [blockRuns, bodyAt_straight, hp]
  rw [hBR] at hR
  simp only [ownedCheckWithR, hsz, hterm, hR, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Nat.lt_one_iff, forall_eq, beq_self_eq_true, true_and]
  refine ⟨by simp [hne, hne'], ?_⟩
  cases o with
  | unk => exact absurd rfl hunk
  | fail => simp [blockOkR]
  | ok s g =>
      generalize hq : tRun B' SSt.start T1 = q at hres hR
      obtain ⟨Q, o'⟩ := q
      cases o' with
      | ok s' g' =>
          obtain ⟨hQ, e, rfl⟩ := hres
          simp only at hQ
          simp only [hQ] at hR ⊢
          have hinv := tRun_inv B SSt.start Tbl.empty SSt.inv_start hp
          have hE : TBnd T1.ents := by
            have := tRun_valid B SSt.start Tbl.empty tValid_empty
            rw [hp] at this
            exact this.2
          refine blockOkR_fall_on (fun r hr => e.2 r (fun hq => hD r hq hr)) e.1.1
            hinv.1 hinv.2 hE ?_ ?_
          · refine liveIter_single (hsz _) _ hR (fun L => ?_)
            simp only [blockNeed, hterm, AllocCheck.LcmdCFG.Term.succs,
              AllocCheck.LcmdCFG.Term.halts, Option.toList, List.flatMap_nil, List.any_nil]
          · intro p hp'
            have hmem : p ∈ B := List.mem_of_getElem? hp'
            have := hs p hmem
            simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
            exact this.1.1
      | fail => simp [ResD] at hres
      | unk => simp [ResD] at hres

/-! ## 6. One operation into two destinations -/

/-- `ss` with register `n` set to `t` and the carry and overflow flags set to `c` and `o`. -/
def SSt.wrF (ss : SSt) (n : String) (t c o : STerm) : SSt :=
  { ss.setR n t with cf := c, of := o }

/-- The step descriptions `o` and `o'` from `ss` differ in their destination only: `o`
    writes a word to `d` where `o'` writes it to `r`, with equal flags and guards; or both
    fail, or both are outside the fragment. -/
def SOut.Ren (ss : SSt) (d r : String) : SOut → SOut → Prop
  | .ok s g, .ok s' g' => g = g' ∧ ∃ t c o, s = ss.wrF d t c o ∧ s' = ss.wrF r t c o
  | .fail, .fail => True
  | .unk, .unk => True
  | _, _ => False

/-- The register-file description `ρ` with its destination replaced by `d`. -/
def ROut.rn (d : String) : ROut → ROut
  | .set _ t gs => .set d t gs
  | o => o

/-- Neither source order of `opn n, [a, b]` is exchanged by `commSwap`. -/
def NoSwap (opn n : String) (a b : LOperand) : Prop :=
  ∀ ra rb, a = .reg ra → b = .reg rb → commSwap opn n ra rb = false

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (sarStruct?) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
  (mulhiStruct? adcxStruct? adcxhiStruct? sbbStruct? sbbhiStruct?) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (castStruct? movImmStruct?) in
theorem symCast_ren (R : String → STerm) (d r opn : String) (a b : LOperand) (cd : Option Nat)
    (h1 : NoSwap opn d a b) (h2 : NoSwap opn r a b) :
    symCast (.Lopn [.reg d] opn [a, b], cd) R =
      (symCast (.Lopn [.reg r] opn [a, b], cd) R).rn d := by
  cases a <;> cases b <;> simp only [symCast, movImmStruct?_pair] <;>
    dsimp only [castStruct?, symMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
      sbbStruct?, sbbhiStruct?, symSh, sarStruct?, symN] <;>
    (try split_ifs) <;> simp_all [ROut.rn, NoSwap]

theorem liftR_ren (ss : SSt) (d r : String) {ρ : ROut} (hρ : ρ.WritesOnly r) :
    SOut.Ren ss d r (liftR ss (ρ.rn d)) (liftR ss ρ) := by
  cases ρ with
  | set r' t gs =>
      simp only [ROut.WritesOnly] at hρ
      subst hρ
      exact ⟨rfl, t, ss.cf, ss.of, rfl, rfl⟩
  | nop => cases hρ
  | fail => trivial
  | unk => trivial

theorem symMem_ren (ss : SSt) (d r opn : String) (a b : LOperand) (τ : MemTag)
    (hst : opn ≠ "STOREIDX") (h1 : NoSwap opn d a b) (h2 : NoSwap opn r a b) :
    SOut.Ren ss d r (symMem (.Lopn [.reg d] opn [a, b], τ) ss)
      (symMem (.Lopn [.reg r] opn [a, b], τ) ss) := by
  have hc : ∀ cd, symCast (.Lopn [.reg d] opn [a, b], cd) ss.regs =
      (symCast (.Lopn [.reg r] opn [a, b], cd) ss.regs).rn d :=
    fun cd => symCast_ren _ _ _ _ _ _ _ h1 h2
  cases τ with
  | load w n =>
      have e1 : loadStruct? (.Lopn [.reg d] opn [a, b]) = none := by
        unfold loadStruct?; split <;> simp_all
      have e2 : loadStruct? (.Lopn [.reg r] opn [a, b]) = none := by
        unfold loadStruct?; split <;> simp_all
      simp only [symMem, e1, e2, hc]
      exact liftR_ren ss d r (symCast_writesOnly _ _ _ _ _ _)
  | store w n =>
      have e1 : storeStruct? (.Lopn [.reg d] opn [a, b]) = none := by
        unfold storeStruct?; split <;> simp_all
      have e2 : storeStruct? (.Lopn [.reg r] opn [a, b]) = none := by
        unfold storeStruct?; split <;> simp_all
      simp only [symMem, e1, e2, hc]
      exact liftR_ren ss d r (symCast_writesOnly _ _ _ _ _ _)
  | loadC => trivial
  | storeC => trivial
  | reg cd =>
      simp only [symMem, hc]
      exact liftR_ren ss d r (symCast_writesOnly _ _ _ _ _ _)

theorem aluFlT_ren (ss : SSt) (d r opn : String) (a b : LOperand) (τ : MemTag)
    (h1 : NoSwap opn d a b) (h2 : NoSwap opn r a b) (bo : Bool) :
    aluFlT (.Lopn [.reg d] opn [a, b], τ) ss bo =
      aluFlT (.Lopn [.reg r] opn [a, b], τ) ss bo := by
  have s1 : aluSwap (.Lopn [.reg d] opn [a, b], τ) = false := by
    cases a <;> cases b <;> simp_all [aluSwap, NoSwap]
  have s2 : aluSwap (.Lopn [.reg r] opn [a, b], τ) = false := by
    cases a <;> cases b <;> simp_all [aluSwap, NoSwap]
  simp only [aluFlT, s1, s2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem aluFl_ren (ss : SSt) (d r opn : String) (a b : LOperand) (τ : MemTag)
    (h1 : NoSwap opn d a b) (h2 : NoSwap opn r a b) {o o' : SOut} (h : SOut.Ren ss d r o o') :
    SOut.Ren ss d r (aluFl (.Lopn [.reg d] opn [a, b], τ) ss o)
      (aluFl (.Lopn [.reg r] opn [a, b], τ) ss o') := by
  cases o <;> cases o' <;> simp only [SOut.Ren, aluFl] at h ⊢
  obtain ⟨rfl, t, c, o, rfl, rfl⟩ := h
  refine ⟨rfl, t, _, _, rfl, ?_⟩
  rw [aluFlT_ren ss d r opn a b τ h1 h2, aluFlT_ren ss d r opn a b τ h1 h2]
  rfl

theorem symCarry_ren (ss : SSt) (op : CarryOp) (d r : String) (a b : LOperand) :
    SOut.Ren ss d r (symCarry op d a b ss) (symCarry op r a b ss) := by
  unfold symCarry
  split
  · cases op
    all_goals exact ⟨rfl, _, _, _, rfl, rfl⟩
  · trivial

/-- **One operation into two destinations.** For a two-source operation other than the flag
    `CMP` and the two-source `MOV`, whose sources are exchanged by `commSwap` for neither
    destination, the steps into `d` and into `r` from one state differ in their destination
    only. -/
theorem symStep_ren (ss : SSt) (d r opn : String) (a b : LOperand) (τ : MemTag)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmov : opn ≠ withWidthTag 64 "MOV")
    (hst : opn ≠ "STOREIDX") (h1 : NoSwap opn d a b) (h2 : NoSwap opn r a b) :
    SOut.Ren ss d r (symStep (.Lopn [.reg d] opn [a, b], τ) ss)
      (symStep (.Lopn [.reg r] opn [a, b], τ) ss) := by
  unfold symStep
  simp only [cmpArgs?, hcmp, if_false, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, hmov]
  split_ifs <;> dsimp only <;>
    first
    | exact symCarry_ren ss _ d r a b
    | exact aluFl_ren ss d r opn a b τ h1 h2 (symMem_ren ss d r opn a b τ hst h1 h2)

/-! ## 7. The scratch chunk -/

theorem tRun_single_ok {i : LinstrRM} {ss s : SSt} {g : List SG} {ds : List String} (T : Tbl)
    (h : symStep i ss = .ok s g) (hw : s.wr = ds ++ ss.wr) :
    tRun [i] ss T = ((T.internSt s ds).1, .ok (T.internSt s ds).2 g) := by
  rw [tRun_cons, h]
  dsimp only
  rw [SSt.Frm.ds_eq hw]
  simp only [runAfter, tRun, SOut.after, List.append_nil]

theorem symStep_movReg {mv d x : String} (hmv : stripWidthTag mv = "MOV") (τ : MemTag)
    (s : SSt) : symStep (.Lopn [.reg d] mv [.reg x], τ) s = .ok (s.setR d (s.regs x)) [] := by
  simp [symStep, cmpArgs?, movRegArgs?, hmv]

/-- A register move from an atom, in a state whose flags are atoms, interns nothing. -/
theorem tRun_movReg {mv d x : String} (hmv : stripWidthTag mv = "MOV") (τ : MemTag) {s : SSt}
    (T : Tbl) (hx : (s.regs x).atom = true) (hc : s.cf.atom = true) (ho : s.of.atom = true) :
    tRun [(.Lopn [.reg d] mv [.reg x], τ)] s T = (T, .ok (s.setR d (s.regs x)) []) := by
  rw [tRun_single_ok (ds := [d]) T (symStep_movReg hmv τ s) rfl]
  have hint : T.internSt (s.setR d (s.regs x)) [d] = (T, s.setR d (s.regs x)) := by
    simp only [Tbl.internSt, Tbl.internRegs]
    simp only [SSt.setR, ite_true, Tbl.intern_atom T hx, Tbl.intern_atom T hc,
      Tbl.intern_atom T ho, Prod.mk.injEq, true_and]
    congr 1
    funext q
    split <;> simp_all
  rw [hint]

/-- **The scratch chunk.** For a scratch register `r` that neither the first source `y`, the
    destination `d` nor the second source `b` reads, the move of `y` into `r`, the operation on
    `r` and the move of `r` into `d` simulate `opn d, [y, b]` off `r`, when `opn` is not the
    flag `CMP`, the two-source `MOV` or `STOREIDX`, and neither destination has its sources
    exchanged by `commSwap`. -/
theorem chunkOn_scratch (r d y opn m : String) (b : LOperand) (τ τ1 τ3 : MemTag)
    (hmv : stripWidthTag m = "MOV") (hyr : y ≠ r) (hb : avoidsReg r b)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmov : opn ≠ withWidthTag 64 "MOV")
    (hst : opn ≠ "STOREIDX") (h1 : NoSwap opn d (.reg y) b) (h2 : NoSwap opn r (.reg y) b) :
    ChunkOn [r] (.Lopn [.reg d] opn [.reg y, b], τ)
      [(.Lopn [.reg r] m [.reg y], τ1), (.Lopn [.reg r] opn [.reg r, b], τ),
        (.Lopn [.reg d] m [.reg r], τ3)] := by
  intro ss ss' T T' e hI hS
  have e'' := e.eqv_takeOn
  have hfirst : ∀ rest : List LinstrRM, tRun ((.Lopn [.reg r] m [.reg y], τ1) :: rest) ss' T' =
      tRun ((.Lopn [.reg r] m [.reg y], τ1) :: rest) (SSt.takeOn [r] ss ss') T' := by
    intro rest
    have heq : (SSt.takeOn [r] ss ss').setR r ((SSt.takeOn [r] ss ss').regs y) =
        ss'.setR r (ss'.regs y) := by
      simp only [SSt.setR, SSt.takeOn, List.mem_singleton, hyr, if_false]
      congr 1
      funext q
      split <;> simp_all
    rw [tRun_cons, tRun_cons, symStep_movReg hmv, symStep_movReg hmv, heq]
    rfl
  rw [hfirst, show ((.Lopn [.reg r] m [.reg y], τ1) :: [(.Lopn [.reg r] opn [.reg r, b], τ),
      (.Lopn [.reg d] m [.reg r], τ3)] : List LinstrRM) =
      [(.Lopn [.reg r] m [.reg y], τ1), (.Lopn [.reg r] opn [.reg r, b], τ)] ++
        [(.Lopn [.reg d] m [.reg r], τ3)] from rfl, tRun_append]
  have hcp := chunk_copy r y opn m b τ τ1 hmv hb hcmp ss _ T T' e''
  have hren := symStep_ren ss d r opn (.reg y) b τ hcmp hmov hst h1 h2
  generalize hsd : symStep (.Lopn [.reg d] opn [.reg y, b], τ) ss = od at hren
  generalize hsr : symStep (.Lopn [.reg r] opn [.reg y, b], τ) ss = or' at hren
  cases od with
  | ok sd g =>
      cases or' with
      | ok sr g' =>
          obtain ⟨rfl, t, c, o, rfl, rfl⟩ := hren
          rw [tRun_single_ok (ds := [d]) T hsd rfl] at hS ⊢
          have hT : (T.internSt (ss.wrF r t c o) [r]).1 = (T.internSt (ss.wrF d t c o) [d]).1 := by
            simp [Tbl.internSt, Tbl.internRegs, SSt.wrF, SSt.setR]
          have hcp' := hcp hI (by rw [tRun_single_ok (ds := [r]) T hsr rfl, hT]; exact hS)
          rw [tRun_single_ok (ds := [r]) T hsr rfl] at hcp'
          have hInv : (T.internSt (ss.wrF d t c o) [d]).2.Inv
              (T.internSt (ss.wrF d t c o) [d]).1.ents.size :=
            Tbl.internSt_inv (T := T) [d] (symStep_refsLt _ hI.1 hsd).1 (fun q hq => by
              have hqd : q ≠ d := by simpa using hq
              simp only [SSt.wrF, SSt.setR, hqd, if_false]
              exact hI.2.1 q)
          have hPr : ∀ q, (T.internSt (ss.wrF r t c o) [r]).2.regs q =
              if q = r then (T.internSt (ss.wrF d t c o) [d]).2.regs d else
                if q = d then ss.regs d else (T.internSt (ss.wrF d t c o) [d]).2.regs q := by
            intro q
            simp only [Tbl.internSt, Tbl.internRegs, SSt.wrF, SSt.setR]
            by_cases hqr : q = r <;> by_cases hqd : q = d <;> simp_all
          have hcf : (T.internSt (ss.wrF r t c o) [r]).2.cf =
              (T.internSt (ss.wrF d t c o) [d]).2.cf := by
            simp [Tbl.internSt, Tbl.internRegs, SSt.wrF, SSt.setR]
          have hof : (T.internSt (ss.wrF r t c o) [r]).2.of =
              (T.internSt (ss.wrF d t c o) [d]).2.of := by
            simp [Tbl.internSt, Tbl.internRegs, SSt.wrF, SSt.setR]
          have harr : (T.internSt (ss.wrF r t c o) [r]).2.arrs =
              (T.internSt (ss.wrF d t c o) [d]).2.arrs := by
            simp [Tbl.internSt, Tbl.internRegs, SSt.wrF, SSt.setR]
          have hzf : (T.internSt (ss.wrF r t c o) [r]).2.zf =
              (T.internSt (ss.wrF d t c o) [d]).2.zf := by
            simp [Tbl.internSt, Tbl.internRegs, SSt.wrF, SSt.setR]
          generalize tRun [(.Lopn [.reg r] m [.reg y], τ1), (.Lopn [.reg r] opn [.reg r, b], τ)]
            (SSt.takeOn [r] ss ss') T' = q at hcp' ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo with
          | ok s2 g2 =>
              obtain ⟨rfl, e2, rfl⟩ := hcp'
              have hx : (s2.regs r).atom = true := by
                rw [← congrFun e2.1 r, hPr r, if_pos rfl]
                exact hInv.2.1 d
              have hc2 : s2.cf.atom = true := by rw [← e2.2.2.2.1, hcf]; exact hInv.2.2.1
              have ho2 : s2.of.atom = true := by rw [← e2.2.2.2.2, hof]; exact hInv.2.2.2
              simp only [runThen, runAfter, tRun_movReg hmv τ3 _ hx hc2 ho2, SOut.after,
                List.append_nil]
              refine ⟨rfl, ⟨⟨?_, ?_, ?_, ?_⟩, fun q hq => ?_⟩, rfl⟩
              · exact harr.symm.trans e2.2.1
              · exact hzf.symm.trans e2.2.2.1
              · exact hcf.symm.trans e2.2.2.2.1
              · exact hof.symm.trans e2.2.2.2.2
              · have hqr : q ≠ r := by simpa using hq
                simp only [SSt.setR]
                rw [← congrFun e2.1 r, ← congrFun e2.1 q, hPr r, hPr q, if_pos rfl, if_neg hqr]
                by_cases hqd : q = d
                · subst hqd; simp
                · simp [hqd]
          | fail => simp [Res] at hcp'
          | unk => simp [Res] at hcp'
      | fail => cases hren
      | unk => cases hren
  | fail =>
      cases or' with
      | fail =>
          have hd : tRun [(.Lopn [.reg d] opn [.reg y, b], τ)] ss T = (T, .fail) := by
            rw [tRun_cons, hsd]
          have hr : tRun [(.Lopn [.reg r] opn [.reg y, b], τ)] ss T = (T, .fail) := by
            rw [tRun_cons, hsr]
          rw [hd] at hS ⊢
          have hcp' := hcp hI (by rw [hr]; exact hS)
          rw [hr] at hcp'
          generalize tRun [(.Lopn [.reg r] m [.reg y], τ1), (.Lopn [.reg r] opn [.reg r, b], τ)]
            (SSt.takeOn [r] ss ss') T' = q at hcp' ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo <;> simp_all [Res, ResD, runThen]
      | _ => cases hren
  | unk =>
      cases or' with
      | unk =>
          have hd : tRun [(.Lopn [.reg d] opn [.reg y, b], τ)] ss T = (T, .unk) := by
            rw [tRun_cons, hsd]
          have hr : tRun [(.Lopn [.reg r] opn [.reg y, b], τ)] ss T = (T, .unk) := by
            rw [tRun_cons, hsr]
          rw [hd] at hS ⊢
          have hcp' := hcp hI (by rw [hr]; exact hS)
          rw [hr] at hcp'
          generalize tRun [(.Lopn [.reg r] m [.reg y], τ1), (.Lopn [.reg r] opn [.reg r, b], τ)]
            (SSt.takeOn [r] ss ss') T' = q at hcp' ⊢
          obtain ⟨Q, qo⟩ := q
          cases qo <;> simp_all [Res, ResD, runThen]
      | _ => cases hren

/-! ## 8. Chunks off the scratch register -/

theorem reloadScratch_not_symReads {x : LinstrR} (h : instrAvoids x = true) :
    reloadScratch ∉ symReads x := by
  intro hq
  unfold symReads at hq
  rw [List.mem_append] at hq
  rcases hq with hq | hq
  · cases x with
    | Lopn ds opn ss =>
        simp only [instrReadRegs, List.mem_flatMap] at hq
        obtain ⟨o, ho, hqo⟩ := hq
        simp only [instrAvoids, Bool.and_eq_true, List.all_eq_true] at h
        have hn : reloadScratch ∈ LprogLeak.opNames o := by
          cases o <;> simp_all [operandReads, LprogLeak.opNames]
        exact TwoAddrLegalize.ne_of_opAvoids (h.2 o ho) _ hn rfl
    | _ => simp [instrReadRegs] at hq
  · rw [List.mem_append] at hq
    rcases hq with hq | hq
    · cases x with
      | Lopn ds opn ss =>
          simp only [instrAvoids, Bool.and_eq_true, List.all_eq_true] at h
          unfold leaReads at hq
          split at hq
          · rename_i b i sc heq
            injection heq with _ _ hs
            subst hs
            split_ifs at hq
            · simp only [List.mem_singleton] at hq
              have ha := h.2 _ (List.mem_singleton_self _)
              subst hq
              simp [TwoAddrLegalize.opAvoids, TwoAddrLegalize.mentionsScratch] at ha
            · cases hq
          · cases hq
      | _ => simp [leaReads] at hq
    · cases x with
      | Lopn ds opn ss =>
          dsimp only at hq
          split_ifs at hq
          · simp only [List.mem_singleton] at hq
            exact absurd hq (by decide)
          · cases hq
      | _ => cases hq

theorem legalR_ne_nil (ok : Bool) (x : LinstrR) : legalR ok x ≠ [] := by
  unfold legalR
  split
  · split <;> (try split) <;> simp
  · simp

theorem legalR_straight (ok : Bool) {x : LinstrR} (h : straightR x = true) :
    ∀ y ∈ legalR ok x, straightR y = true := by
  intro y hy
  unfold legalR at hy
  split at hy
  · split at hy <;> (try split at hy) <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy <;>
      rcases hy with rfl | rfl | rfl <;> exact h
  · simp only [List.mem_singleton] at hy
    subst hy
    exact h

theorem legalR_avoids (ok : Bool) {x : LinstrR} (h : instrAvoids x = true)
    (hns : ∀ m, twoAddrRoute x ≠ .scratch m) : ∀ y ∈ legalR ok x, instrAvoids y = true := by
  intro y hy
  unfold legalR at hy
  split at hy
  · rename_i d opn a b
    simp only [instrAvoids, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
    obtain ⟨hd, ha, hb⟩ := h
    split at hy
    · simp only [List.mem_singleton] at hy; subst hy; simp [instrAvoids, hd, ha, hb]
    · split at hy
      · simp only [List.mem_singleton] at hy; subst hy; simp_all [instrAvoids]
      · simp only [List.mem_singleton] at hy; subst hy; simp [instrAvoids, hd, ha, hb]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> simp [instrAvoids, hd, ha, hb]
    · simp only [List.mem_singleton] at hy; subst hy; simp [instrAvoids, hd, ha]
    · rename_i m hr; exact absurd hr (hns m)
  · simp only [List.mem_singleton] at hy
    subst hy
    exact h

theorem needsTie_mov64 (b : LOperand) : needsTie (withWidthTag 64 "MOV") b = false := by
  cases b <;> rfl

theorem needsTie_storeIdx (b : LOperand) : needsTie "STOREIDX" b = false := by
  cases b <;> rfl

theorem twoAddrRouteWF_scratch_outs {outs : List String} {tg : LinstrR → MemTag} {x : LinstrR}
    {m : String} (hw : twoAddrRouteWF outs tg x = true) (hr : twoAddrRoute x = .scratch m) :
    reloadScratch ∉ outs := by
  unfold twoAddrRouteWF at hw
  split at hw
  · rw [hr] at hw
    dsimp only at hw
    split at hw
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
      intro h
      have : outs.contains reloadScratch = true := List.contains_iff_mem.mpr h
      rw [this] at hw
      cases hw.1.1
    · cases hw
  · rename_i hx
    unfold twoAddrRoute at hr
    split at hr
    · rename_i d opn a b
      exact absurd rfl (hx d opn a b)
    · cases hr

/-- **The chunk of a route off the scratch register.** In a body that does not name the scratch
    register, an instruction whose route the checker accepts is simulated off the scratch
    register by its legalisation with the scratch route on. -/
theorem chunkOn_route {tg : LinstrR → MemTag} (htg : TagFirstSrc tg) {outs : List String}
    {x : LinstrR} (hw : twoAddrRouteWF outs tg x = true) (hav : instrAvoids x = true) :
    ChunkOn [reloadScratch] (x, tg x) ((legalR true x).map fun y => (y, tg y)) := by
  by_cases hsc : ∃ m, twoAddrRoute x = .scratch m
  · obtain ⟨m, hm⟩ := hsc
    have hm' := hm
    unfold twoAddrRoute at hm'
    split at hm'
    · rename_i d opn a b
      obtain ⟨hmv, hc, -⟩ := twoAddrRoute_scratch hm
      obtain ⟨hn, -, -⟩ := twoAddrRoute_untied hm (by simp)
      simp only [instrAvoids, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hav
      obtain ⟨hd, ha, hb⟩ := hav
      cases a with
      | reg y =>
          simp only [twoAddrRouteWF, hm, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hw
          obtain ⟨⟨-, hsw⟩, htag⟩ := hw
          simp only [legalR, hm, ↓reduceIte, List.map_cons, List.map_nil, htag]
          have hyr : y ≠ reloadScratch :=
            TwoAddrLegalize.ne_of_opAvoids ha y (by simp [LprogLeak.opNames])
          have hbr : avoidsReg reloadScratch b :=
            fun h => TwoAddrLegalize.ne_of_opAvoids hb _ h rfl
          refine chunkOn_scratch reloadScratch d y opn m b _ _ _
            (TwoAddrLegalize.stripWidthTag_movFor hmv) hyr hbr (opn_ne_cmp64 hc) ?_ ?_ ?_ ?_
          · rintro rfl; rw [needsTie_mov64] at hn; cases hn
          · rintro rfl; rw [needsTie_storeIdx] at hn; cases hn
          · rintro ra rb hra rfl
            simp only [commSwap, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
              Bool.eq_false_iff]
            rintro ⟨⟨h1, rfl⟩, -⟩
            rw [h1] at hsw
            simp at hsw
          · rintro ra rb hra rfl
            simp only [commSwap, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
              Bool.eq_false_iff]
            rintro ⟨⟨-, rfl⟩, -⟩
            exact hbr (by simp [LprogLeak.opNames])
      | _ => simp [twoAddrRouteWF, hm] at hw
    · cases hm'
  · have hns : ∀ m, twoAddrRoute x ≠ .scratch m := fun m h => hsc ⟨m, h⟩
    refine chunkOn_of_chunk (chunk_route htg hw (fun m h => absurd h (hns m))) ?_
    intro j hj q hq hqD
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hj
    simp only [List.mem_singleton] at hqD
    subst hqD
    exact reloadScratch_not_symReads (legalR_avoids true hav hns y hy) hq

/-! ## 9. Completeness -/

/-- **Completeness of the value checker for two-address legalisation.** For a non-empty
    straight-line body whose instructions are accepted by their routes (`twoAddrRouteWF`) and
    whose symbolic run lies inside the described fragment, `ownedCheckM` accepts the body
    against its legalisation `TwoAddrLegalize.twoAddrBody`, for the observed list `outs` and
    every typing `tg` that gives a two-source operation one tag whatever its first source. -/
theorem twoAddr_ownedCheckM_complete (outs : List String) {tg : LinstrR → MemTag}
    (htg : TagFirstSrc tg) (body : Lcmd)
    (hne : body ≠ []) (hs : ∀ i ∈ body, straightR i.li_i = true)
    (hwf : ∀ i ∈ body, twoAddrRouteWF outs tg i.li_i = true)
    (hfrag : symRun (typeBody tg body) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody tg body) (typeBody tg (twoAddrBody body)) = true := by
  rw [twoAddrBody_typedR tg body]
  have hB : ∀ p ∈ typeBody tg body, straightR p.1 = true ∧
      twoAddrRouteWF outs tg p.1 = true ∧ p.2 = tg p.1 ∧
      (bodyAvoids body = true → instrAvoids p.1 = true) := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    refine ⟨hs i hi, hwf i hi, rfl, fun h => ?_⟩
    simp only [bodyAvoids, List.all_eq_true] at h
    exact h i hi
  have hne1 : typeBody tg body ≠ [] := by simpa [typeBody] using hne
  have hne' : (typeBody tg body).flatMap
      (fun p => (legalR (bodyAvoids body) p.1).map fun x => (x, tg x)) ≠ [] := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne1
    intro h
    have := List.flatMap_eq_nil_iff.mp h p hp
    simp only [List.map_eq_nil_iff] at this
    exact legalR_ne_nil _ _ this
  have hsB : ∀ p ∈ typeBody tg body, straightR p.1 = true := fun p hp => (hB p hp).1
  have hs' : ∀ q ∈ (typeBody tg body).flatMap
      (fun p => (legalR (bodyAvoids body) p.1).map fun x => (x, tg x)), straightR q.1 = true := by
    intro q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    exact legalR_straight _ (hB p hp).1 y hy
  have hunk : (tRun (typeBody tg body) SSt.start Tbl.empty).2 ≠ .unk := by
    rwa [ne_eq, tRun_unk_iff]
  by_cases hA : bodyAvoids body = true ∧ reloadScratch ∉ outs
  · refine ownedCheckM_of_resOn outs [reloadScratch] (by simpa using hA.2) hne1 hne' hsB hs' ?_
      hunk
    refine tRun_lockOn [reloadScratch] _ _ (fun p hp => ?_) SSt.start SSt.start Tbl.empty _
      ⟨SSt.Same.refl _, fun _ _ => rfl⟩ SSt.inv_start (Tbl.Sub.refl _)
    obtain ⟨-, hw, hτ, hav⟩ := hB p hp
    obtain ⟨x, τ'⟩ := p
    simp only at hτ
    subst hτ
    rw [hA.1]
    exact chunkOn_route htg hw (hav hA.1)
  · refine ownedCheckM_of_res outs hne1 hne' hsB hs' ?_ hunk
    refine tRun_lock _ _ (fun p hp => ?_) SSt.start SSt.start Tbl.empty _
      (SSt.Eqv.refl _) SSt.inv_start (Tbl.Sub.refl _)
    obtain ⟨-, hw, hτ, hav⟩ := hB p hp
    obtain ⟨x, τ'⟩ := p
    simp only at hτ
    subst hτ
    refine chunk_route htg hw (fun m hm => ?_)
    by_contra hok
    simp only [Bool.not_eq_false] at hok
    exact hA ⟨hok, twoAddrRouteWF_scratch_outs hw hm⟩

/-- **Completeness at a constant typing.** -/
theorem twoAddr_ownedCheckM_complete_const (outs : List String) (τ : MemTag) (body : Lcmd)
    (hne : body ≠ []) (hs : ∀ i ∈ body, straightR i.li_i = true)
    (hwf : ∀ i ∈ body, twoAddrRouteWF outs (fun _ => τ) i.li_i = true)
    (hfrag : symRun (typeBody (fun _ => τ) body) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody (fun _ => τ) body)
      (typeBody (fun _ => τ) (twoAddrBody body)) = true :=
  twoAddr_ownedCheckM_complete outs (tagFirstSrc_const τ) body hne hs hwf hfrag

/-- **Completeness under the copy-route condition.** -/
theorem twoAddr_ownedCheckM_complete_of_twoAddrWF (outs : List String) {tg : LinstrR → MemTag}
    (htg : TagFirstSrc tg) (body : Lcmd)
    (hne : body ≠ []) (hs : ∀ i ∈ body, straightR i.li_i = true)
    (hwf : ∀ i ∈ body, twoAddrWF i.li_i = true)
    (hfrag : symRun (typeBody tg body) SSt.start ≠ .unk) :
    ownedCheckM outs (typeBody tg body) (typeBody tg (twoAddrBody body)) = true :=
  twoAddr_ownedCheckM_complete outs htg body hne hs
    (fun i hi => twoAddrRouteWF_of_twoAddrWF outs tg _ (hwf i hi)) hfrag

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
