/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTVSound

@[expose] public section

set_option autoImplicit false

/-!
# Translation validation of a straight-line loop body

A loop body is a list of `Lopn` instructions, run by the flag machine's straight-line run
`runStraightF`. `straightCheck bind outs B B'` compares two such bodies over different names
by symbolic execution (`OwnedLprogTV.symRun`): `B` from the symbolic start state, `B'` from
the start state in which each name bound by `bind` holds the start value of its partner in
`B` (`startWith`). The guards of `B'` are guards of `B`, and the final symbolic states agree
on each pair of names of `outs` and on every array written. `straightCheck_sound` states
that every run of `B` from a state `b` is matched by a run of `B'` from every state related
to `b` by the binding (`BindRel`), the end states agreeing on the pairs of `outs` and on
every array. `guardsOK W sh gs` decides that the guards `gs` hold at every state whose names
`W` hold words of width `64` and whose arrays have the shapes `sh`; `runStraightF_of_guardsOK`
gives the run of `B` from such a state.

## Main results

* `runL_isLopn` — the run `OwnedLprogTV.runL` of `Lopn` instructions is `runStraightF`.
* `startWith`, `BindRel`, `straightCheck`, `straightCheck_sound` — the comparison of two
  bodies and its soundness.
* `w64`, `guardOK`, `guardsOK`, `runStraightF_of_guardsOK` — the run of a body from a state
  of known widths.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoopTVLeg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-- The flag-machine state of a base state and a zero flag, in the function `""`. -/
def wrapF (b : LstateM) (zf : Bool) : LstateMF := { prog := { base := b, lfn := "" }, zf := zf }

/-- The run `runL` of `Lopn` instructions is the straight-line run `runStraightF`. -/
theorem runL_isLopn (P : LprogM) :
    ∀ (is : List LinstrRM), (∀ i ∈ is, IsLopn i) → ∀ (s : LstateMF),
      runL P is s = (runStraightF is s.prog.base s.zf).map
        (fun bz => { prog := { s.prog with base := bz.1 }, zf := bz.2 })
  | [], _, s => by simp [runL]
  | i :: is, h, s => by
      rw [runL, evalInstrPMemF_isLopn P i s (h i List.mem_cons_self), runStraightF_cons]
      cases hf : fstepF i s.prog.base s.zf with
      | none => rfl
      | some bz =>
          simp only [Option.map_some, Option.bind_some]
          rw [runL_isLopn P is (fun j hj => h j (List.mem_cons_of_mem _ hj))]

/-- The symbolic start state of `B'` under the binding `bind` of its names to names of `B`:
    a bound name holds the start value of its partner, every other name its own. -/
def startWith (bind : List (String × String)) : SSt :=
  { SSt.start with
    regs := fun n => match bind.lookup n with
      | some v => .reg v
      | none => .reg n
    wr := bind.map (·.1) }

theorem startWith_good (bind : List (String × String)) : (startWith bind).Good := by
  refine ⟨fun r hr => ?_, fun _ _ => rfl⟩
  have : bind.lookup r = none := by
    cases h : bind.lookup r with
    | none => rfl
    | some v =>
        exact absurd (List.mem_map.mpr ⟨(r, v), DecodeLoopTVSound.mem_of_lookup h, rfl⟩) hr
  simp [startWith, this]

/-- **The comparison of two straight-line bodies.** The symbolic run of `B` from the start
    state and the symbolic run of `B'` from `startWith bind` succeed, every guard of the
    normal form of `B'`'s guards is one of `B`'s, the final symbolic states agree on each
    pair `(v, n)` of `outs` (the name `v` of `B`, the name `n` of `B'`), and they agree on
    every array either body writes. -/
def straightCheck (bind outs : List (String × String)) (B B' : List LinstrRM) : Bool :=
  match symRun B SSt.start, symRun B' (startWith bind) with
  | .ok ss gs, .ok ss' gs' =>
      (normG gs').all (fun g => (normG gs).contains g)
        && outs.all (fun p => ss.regs p.1 == ss'.regs p.2)
        && (ss.awr ++ ss'.awr).all (fun q => ss.arrs q == ss'.arrs q)
  | _, _ => false

/-- The flag-machine state of `B'` under the binding `bind` from the state `b` of `B`: a
    bound name holds the value of its partner. -/
def BindRel (bind : List (String × String)) (b bL : LstateM) : Prop :=
  (∀ n, bL.reg.lvm n = match bind.lookup n with
      | some v => b.reg.lvm v
      | none => b.reg.lvm n) ∧ bL.larr = b.larr ∧ bL.cf = b.cf ∧ bL.of = b.of

theorem holds_startWith {bind : List (String × String)} {b bL : LstateM} (zf : Bool)
    (h : BindRel bind b bL) :
    Holds b.reg.lvm b.larr b.cf b.of zf (startWith bind) (wrapF bL zf) := by
  refine ⟨fun q => ?_, fun q => ?_, rfl, ?_, ?_⟩
  · show bL.reg.lvm q = _
    rw [h.1 q]
    simp only [startWith]
    split <;> rfl
  · show bL.larr q = _
    rw [h.2.1]; rfl
  · show bL.cf = _
    simp [startWith, SSt.start, STerm.ev, bitOf, h.2.2.1]
  · show bL.of = _
    simp [startWith, SSt.start, STerm.ev, bitOf, h.2.2.2]

/-- The run `runL` of `Lopn` instructions from a wrapped state. -/
theorem runL_wrap {is : List LinstrRM} (h : ∀ i ∈ is, IsLopn i) (b : LstateM) (zf : Bool) :
    runL (singletonProgM "" []) is (wrapF b zf) = (runStraightF is b zf).map
      (fun bz => wrapF bz.1 bz.2) :=
  runL_isLopn _ is h _

/-- **The comparison is sound.** Every straight-line run of `B` from a state `b` is matched
    by a run of `B'` from a state related to `b` by the binding, the end states agreeing on
    each pair of `outs` and on every array. -/
theorem straightCheck_sound {bind outs : List (String × String)} {B B' : List LinstrRM}
    (h : straightCheck bind outs B B' = true) (hB : ∀ i ∈ B, IsLopn i)
    (hB' : ∀ i ∈ B', IsLopn i) {b bL t : LstateM} {zf zt : Bool} (hbL : BindRel bind b bL)
    (hrun : runStraightF B b zf = some (t, zt)) :
    ∃ t' zt', runStraightF B' bL zf = some (t', zt')
      ∧ (∀ p ∈ outs, t'.reg.lvm p.2 = t.reg.lvm p.1) ∧ ∀ q, t'.larr q = t.larr q := by
  unfold straightCheck at h
  split at h
  · rename_i ss gs ss' gs' hs hs'
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq] at h
    obtain ⟨⟨hg, ho⟩, ha⟩ := h
    have hst := holds_start (wrapF b zf)
    have d := symRun_sound (singletonProgM "" []) B SSt.start _ _ _ _ _ _ hst
    have d' := symRun_sound (singletonProgM "" []) B' (startWith bind) _ _ _ _ _ _
      (holds_startWith zf hbL)
    rw [hs] at d
    rw [hs'] at d'
    rw [runL_wrap hB, hrun, Option.map_some] at d
    rw [runL_wrap hB'] at d'
    obtain ⟨hgs, hH, -⟩ := d.1 _ rfl
    have hgs' : AllG (wrapF b zf).prog.base.reg.lvm (wrapF b zf).prog.base.larr
        (wrapF b zf).prog.base.cf (wrapF b zf).prog.base.of gs' := by
      rw [← allG_normG] at hgs ⊢
      exact fun g hg' => hgs g (hg g hg')
    obtain ⟨⟨t', zt'⟩, hr'⟩ := Option.isSome_iff_exists.mp (d'.2 hgs')
    obtain ⟨⟨t'', zt''⟩, hr'', he⟩ := Option.map_eq_some_iff.mp hr'
    obtain ⟨-, hH', -⟩ := d'.1 _ hr'
    refine ⟨t'', zt'', hr'', fun p hp => ?_, fun q => ?_⟩
    · have e1 := hH'.1 p.2
      have e2 := hH.1 p.1
      rw [← he] at e1
      simp only [wrapF] at e1 e2
      rw [e1, e2, ho p hp]
    · have e1 := hH'.2.1 q
      have e2 := hH.2.1 q
      rw [← he] at e1
      simp only [wrapF] at e1 e2
      rw [e1, e2]
      by_cases hq : q ∈ ss.awr ++ ss'.awr
      · rw [ha q hq]
      · simp only [List.mem_append, not_or] at hq
        rw [(symRun_good B SSt.good_start hs).2 q hq.1,
          (symRun_good B' (startWith_good bind) hs').2 q hq.2]
  · cases h

/-- A symbolic word of width `64` at every state whose names `W` hold words of width `64`: a
    start name of `W`, or a word whose outermost constructor fixes the width `64`. -/
def w64 (W : List String) : STerm → Bool
  | .reg r => W.contains r
  | t => t.wknown == some 64

/-- A guard that holds at every state whose names `W` hold words of width `64` and whose
    arrays have the shapes `sh`: a word of width `64` (`w64`), two such words, a start array
    of `sh` at its shape and width `64`, or a written array at the shape it is written at. -/
def guardOK (W : List String) (sh : List (String × Nat)) : SG → Bool
  | .wid t w => w == 64 && w64 W t
  | .eqW x y => w64 W x && w64 W y
  | .shp (.cell A) w n => w == 64 && sh.contains (A, n)
  | .shp (.aset _ w n _ _) w' n' => w == w' && n == n'

theorem w64_ev {W : List String} {V : String → Σ w, BitVec w} {A : String → ArrCell}
    {C O : Bool} (hW : ∀ r ∈ W, (V r).1 = 64) {t : STerm} (h : w64 W t = true) :
    (t.ev V A C O).1 = 64 := by
  unfold w64 at h
  split at h
  · rename_i r
    exact hW r (List.contains_iff_mem.mp h)
  · exact STerm.wknown_ev V A C O (beq_iff_eq.mp h)

/-- Every guard of the normal form of `gs` passes `guardOK`. -/
def guardsOK (W : List String) (sh : List (String × Nat)) (gs : List SG) : Bool :=
  (normG gs).all (guardOK W sh)

theorem guardOK_holds {W : List String} {sh : List (String × Nat)}
    {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    (hW : ∀ r ∈ W, (V r).1 = 64) (hsh : ∀ p ∈ sh, (A p.1).1 = 64 ∧ (A p.1).2.1 = p.2) :
    ∀ g : SG, guardOK W sh g = true → g.holds V A C O := by
  intro g h
  unfold guardOK at h
  split at h
  · rename_i t w
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact w64_ev hW h
  · rename_i x y
    simp only [Bool.and_eq_true] at h
    show (x.ev V A C O).1 = (y.ev V A C O).1
    rw [w64_ev hW h.1, w64_ev hW h.2]
  · rename_i A' w n
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
    obtain ⟨rfl, h⟩ := h
    exact hsh _ h
  · rename_i a w n i v w' n'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

/-- **The run of a body from a state of known widths.** When the guards of the symbolic run
    of `B` pass `guardsOK W sh`, the straight-line run of `B` succeeds from every state whose
    names `W` hold words of width `64` and whose arrays have the shapes `sh`. -/
theorem runStraightF_of_guardsOK {B : List LinstrRM} (hB : ∀ i ∈ B, IsLopn i) {ss : SSt}
    {gs : List SG} (hs : symRun B SSt.start = .ok ss gs) {W : List String}
    {sh : List (String × Nat)} (hg : guardsOK W sh gs = true) {b : LstateM} (zf : Bool)
    (hW : ∀ r ∈ W, (b.reg.lvm r).1 = 64)
    (hsh : ∀ p ∈ sh, (b.larr p.1).1 = 64 ∧ (b.larr p.1).2.1 = p.2) :
    ∃ t zt, runStraightF B b zf = some (t, zt) := by
  have d := symRun_sound (singletonProgM "" []) B SSt.start _ _ _ _ _ _ (holds_start (wrapF b zf))
  rw [hs, runL_wrap hB] at d
  have hall : AllG (wrapF b zf).prog.base.reg.lvm (wrapF b zf).prog.base.larr
      (wrapF b zf).prog.base.cf (wrapF b zf).prog.base.of gs := by
    rw [← allG_normG]
    intro g hgm
    exact guardOK_holds hW hsh g (List.all_eq_true.mp hg g hgm)
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (d.2 hall)
  obtain ⟨⟨t, zt⟩, ht, -⟩ := Option.map_eq_some_iff.mp hx
  exact ⟨t, zt, ht⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoopTVLeg
