/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTVSound
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode

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
* `headSt`, `headBind`, `headOuts`, `bodyTV`, `decSim_body_tv` — the loop body against its
  decoded machine body: the read-back body (`DecodeLoopTV.liftRun`) from the loop-head
  reading state, compared with the virtual body at the head binding; the decoded body
  simulates the virtual body from `MCorr` with the names held in frame words
  (`DecodeGenNode.FrameNames`) back to it (`liftRun_sound`, `straightCheck_sound`).
* `nodeCheckTV`, `decNodeAbi_halts_tv`, `decNodeAbi_result_tv` — the node check with the
  loop body by translation validation, and the conclusions of `decNodeAbi_halts` and
  `decNodeAbi_result` for a node it accepts (through `DecodeGenNode.decNodeMem_halts_fr`).
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

/-! ## The loop body against its decoded machine body -/

section Body

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState Disjoint8 disjoint8_add_ofInt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep (DecSim DecLsemCorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (FrameNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTVSound

/-- The reading state at the loop head: the index register `R` holds a valid index, the
    registers of the live names `L0` are live, and the frame words of `Fr` are live. -/
def headSt (E : MemEnv) (L0 : List String) (Fr : List (String × Int)) (R : String) : LiftSt :=
  { bnd := [(R, 0)]
    dead := liftRegs.filter fun X => !L0.any fun v => E.pi v == X
    slive := Fr.map (·.2) }

/-- The binding of the read-back names to the live names at the loop head: the register of
    each name of `L0`, and the frame word of each name of `Fr`. -/
def headBind (E : MemEnv) (L0 : List String) (Fr : List (String × Int)) :
    List (String × String) :=
  L0.map (fun v => (liftReg (E.pi v), v)) ++ Fr.map fun q => (slotName q.2, q.1)

/-- The live names at the loop head with their read-back names. -/
def headOuts (E : MemEnv) (L0 : List String) (Fr : List (String × Int)) :
    List (String × String) :=
  L0.map (fun v => (v, liftReg (E.pi v))) ++ Fr.map fun q => (q.1, slotName q.2)

/-- The shapes of the nonempty regions. -/
def arrShapes (rs : List Region) : List (String × Nat) :=
  (rs.filter fun g => decide (0 < regLen rs g.name)).map fun g => (g.name, regLen rs g.name)

/-- The frame offsets `S` are eight apart from one another and from the pointer slots. -/
def slotSepB (rs : List Region) (S : List Int) : Bool :=
  S.all fun o =>
    S.all (fun o' => o == o' ||
        (decide (8 ≤ (o - o').natAbs) && decide ((o - o').natAbs ≤ 2 ^ 64 - 8)))
      && rs.all fun g =>
        decide (8 ≤ (o - g.off).natAbs) && decide ((o - g.off).natAbs ≤ 2 ^ 64 - 8)

/-- **The loop-body check by translation validation.** The decoded body `js` is read back
    from the loop-head reading state with the frame offsets `S`; the frame offsets are
    separated; the read-back body and the virtual body `body` are `Lopn` instructions; the
    virtual body runs from every loop-head state (`guardsOK`); `straightCheck` relates them at
    the head binding; and at the end of the read-back body the registers of `L0` and the
    frame words of `Fr` are live. -/
def bodyTV (E : MemEnv) (L0 : List String) (Fr : List (String × Int)) (R : String)
    (S : List Int) (body : List LinstrRM) (js : List (JInstr 64)) : Bool :=
  match liftRun ⟨E.rs, S, E.nb⟩ (headSt E L0 Fr R) js with
  | some (stF, ls) =>
      body.all isLopnB && ls.all isLopnB && L0.all (fun v => liftRegs.contains (E.pi v))
        && Fr.all (fun q => S.contains q.2) && slotSepB E.rs S
        && straightCheck (headBind E L0 Fr) (headOuts E L0 Fr) body ls
        && (match symRun body SSt.start with
            | .ok _ gs => guardsOK (L0 ++ Fr.map (·.1)) (arrShapes E.rs) gs
            | _ => false)
        && L0.all (fun v => stF.live (E.pi v)) && Fr.all (fun q => stF.slive.contains q.2)
  | none => false

/-- The flag-machine state of the read-back body at the loop head: each bound name holds the
    value of its partner. -/
def headState (bind : List (String × String)) (b : LstateM) : LstateM :=
  { b with reg := { b.reg with lvm := fun n => match bind.lookup n with
      | some v => b.reg.lvm v
      | none => b.reg.lvm n } }

theorem bindRel_headState (bind : List (String × String)) (b : LstateM) :
    BindRel bind b (headState bind b) :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

theorem getW_of_lvm {s s' : LstateN} {r r' : String} (h : s.lvm r = s'.lvm r') (w : Nat) :
    s.getW r w = s'.getW r' w := by
  unfold LstateN.getW; rw [h]

theorem width_of_getW {s : LstateN} {r : String} {w : Nat} {v : BitVec w}
    (h : s.getW r w = some v) : (s.lvm r).1 = w := by
  unfold LstateN.getW at h
  split at h
  · assumption
  · cases h

theorem shape_of_getArr {s : LstateM} {r : String} {w n : Nat} {a : Fin n → BitVec w}
    (h : s.getArr r w n = some a) : (s.larr r).1 = w ∧ (s.larr r).2.1 = n := by
  unfold LstateM.getArr at h
  split at h
  · split at h
    · rename_i h1 h2; exact ⟨h1, h2⟩
    · cases h
  · cases h

/-- A key with a pair in a list of pairs has a value there. -/
theorem lookup_isSome_of_mem {α : Type} {l : List (String × α)} {k : String} {v : α}
    (h : (k, v) ∈ l) : ∃ v', l.lookup k = some v' := by
  induction l with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk; exact ⟨b, by simp [List.lookup]⟩
    · rcases List.mem_cons.mp h with he | ht
      · simp only [Prod.mk.injEq] at he
        exact absurd he.1 hk
      · obtain ⟨v', hv'⟩ := ih ht
        have hb : (k == a) = false := by simp [hk]
        exact ⟨v', by simp only [List.lookup, hb, hv']⟩

theorem lookup_append_of_isSome {α : Type} {l₁ l₂ : List (String × α)} {k : String} {v : α}
    (h : l₁.lookup k = some v) : (l₁ ++ l₂).lookup k = some v := by
  induction l₁ with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk; simpa [List.lookup] using h
    · have hb : (k == a) = false := by simp [hk]
      simp only [List.lookup, List.cons_append, hb] at h ⊢
      exact ih h

theorem lookup_append_of_none {α : Type} {l₁ l₂ : List (String × α)} {k : String}
    (h : ∀ p ∈ l₁, p.1 ≠ k) : (l₁ ++ l₂).lookup k = l₂.lookup k := by
  induction l₁ with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hk : k ≠ a := fun e => h (a, b) List.mem_cons_self e.symm
    have hb : (k == a) = false := by simp [hk]
    simp only [List.lookup, List.cons_append, hb]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- **The loop body by translation validation.** For a body accepted by `bodyTV`, under the
    separation of the regions and of the frame words `S` from the cells, the decoded body
    simulates the virtual body from `MCorr` on `L0` with the names `Fr` held in frame words and
    a valid index in `R`, back to `MCorr` on `L0` with the names `Fr` held in frame words. -/
theorem decSim_body_tv {E : MemEnv} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : MemSep E.rs base rsp) (hsp : E.sp = "%rsp") {L0 : List String}
    {Fr : List (String × Int)} {R : String} {S : List Int} {body : List LinstrRM}
    {js : List (JInstr 64)} (h : bodyTV E L0 Fr R S body js = true)
    (hcell : ∀ off ∈ S, ∀ A j, regK E.rs A j →
      Disjoint8 ((regLay E.rs base).addr A j) (rsp + BitVec.ofInt 64 off)) :
    DecSim (fun sa b zf => (MCorr E base rsp (L0, Abs.empty) False sa b zf
        ∧ FrameNames Fr rsp sa b) ∧ (sa.regs R).toNat < E.nb)
      (fun sa b zf => MCorr E base rsp (L0, Abs.empty) False sa b zf ∧ FrameNames Fr rsp sa b)
      body js := by
  unfold bodyTV at h
  split at h
  · rename_i stF ls hlift
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hBl, hLl⟩, hL0r⟩, hFrS⟩, hsl⟩, htv⟩, hgd⟩, hendL⟩, hendF⟩ := h
    have hB : ∀ i ∈ body, JasminLsemMemLoop.IsLopn i :=
      fun i hi => isLopnB_isLopn (hBl i hi)
    have hB' : ∀ i ∈ ls, JasminLsemMemLoop.IsLopn i :=
      fun i hi => isLopnB_isLopn (hLl i hi)
    obtain ⟨ssB, gsB, hsB, hg⟩ : ∃ ss gs, symRun body SSt.start = .ok ss gs
        ∧ guardsOK (L0 ++ Fr.map (·.1)) (arrShapes E.rs) gs = true := by
      split at hgd
      · rename_i ss gs hs; exact ⟨ss, gs, hs, hgd⟩
      · cases hgd
    unfold slotSepB at hsl
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq] at hsl
    have hlsep : LSep ⟨E.rs, S, E.nb⟩ base rsp :=
      { mem := hsep
        cell := hcell
        word := fun o ho o' ho' hne => by
          rcases (hsl o ho).1 o' ho' with he | ⟨h1, h2⟩
          · exact absurd he hne
          · exact disjoint8_add_ofInt rsp o o' h1 h2
        slot := fun o ho q a ha => by
          simp only [regFrame, Option.map_eq_some_iff] at ha
          obtain ⟨g, hg, rfl⟩ := ha
          obtain ⟨h1, h2⟩ := (hsl o ho).2 g (List.mem_of_find?_eq_some hg)
          exact disjoint8_add_ofInt rsp o g.off h1 h2 }
    intro sa b zf ⟨⟨hM, hFN⟩, hidx⟩
    -- the binding at a live register and at a live frame word
    have hreg : ∀ X, (headSt E L0 Fr R).live X = true →
        ∃ v, (headBind E L0 Fr).lookup (liftReg X) = some v ∧ v ∈ L0 ∧ E.pi v = X := by
      intro X hX
      have hXL := mem_liftRegs_of_live hX
      have hXd := not_dead_of_live hX
      simp only [headSt, List.mem_filter, hXL, true_and, Bool.not_eq_true',
        Bool.not_eq_false, List.any_eq_true, beq_iff_eq] at hXd
      obtain ⟨v, hv, hvX⟩ := hXd
      have hm : (liftReg X, v) ∈ L0.map (fun v => (liftReg (E.pi v), v)) :=
        List.mem_map.mpr ⟨v, hv, by rw [hvX]⟩
      obtain ⟨v', hv'⟩ := lookup_isSome_of_mem hm
      obtain ⟨v'', hv'', he⟩ := List.mem_map.mp (DecodeLoopTVSound.mem_of_lookup hv')
      simp only [Prod.mk.injEq] at he
      obtain ⟨he1, rfl⟩ := he
      exact ⟨v'', lookup_append_of_isSome hv', hv'',
        liftReg_inj (hL0r v'' hv'') hXL he1⟩
    have hslot : ∀ off ∈ Fr.map (·.2),
        ∃ v, (headBind E L0 Fr).lookup (slotName off) = some v ∧ (v, off) ∈ Fr := by
      intro off ho
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
      have hn : ∀ p ∈ L0.map (fun v => (liftReg (E.pi v), v)), p.1 ≠ slotName q.2 := by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
        exact liftReg_ne_slotName (hL0r v hv) q.2
      have hm : (slotName q.2, q.1) ∈ Fr.map (fun q => (slotName q.2, q.1)) :=
        List.mem_map.mpr ⟨q, hq, rfl⟩
      obtain ⟨v', hv'⟩ := lookup_isSome_of_mem hm
      obtain ⟨q', hq', he⟩ := List.mem_map.mp (DecodeLoopTVSound.mem_of_lookup hv')
      simp only [Prod.mk.injEq] at he
      obtain ⟨he1, rfl⟩ := he
      refine ⟨q'.1, by rw [headBind, lookup_append_of_none hn]; exact hv', ?_⟩
      rw [← slotName_inj he1]
      exact hq'
    -- the read-back state at the loop head
    let bL := headState (headBind E L0 Fr) b
    have hLC : LCorr ⟨E.rs, S, E.nb⟩ base rsp (headSt E L0 Fr R) sa bL zf :=
      { corr :=
          { regs := by
              rintro n ⟨X, hX, rfl⟩
              obtain ⟨v, hv, hvL, hvX⟩ := hreg X hX
              rw [unlift_liftReg (mem_liftRegs_of_live hX)]
              have h1 : bL.reg.getW (liftReg X) 64 = b.reg.getW v 64 :=
                getW_of_lvm (by simp only [bL, headState, hv]) 64
              rw [h1, hM.1.regs v hvL, hvX]
            zfEq := fun hz => by simp [headSt] at hz
            cells := fun A j hk => hM.1.cells A j hk
            slots := hM.1.slots }
        sp := by rw [← hsp]; exact hM.2.1
        sliveS := fun off ho => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
          exact hFrS q hq
        slots := fun off ho => by
          obtain ⟨v, hv, hvF⟩ := hslot off ho
          rw [← hFN (v, off) hvF]
          exact getW_of_lvm (by simp only [bL, headState, hv]) 64
        facts :=
          { ptr := fun p hp => by simp [headSt] at hp
            imm := fun p hp => by simp [headSt] at hp
            cp := fun p hp => by simp [headSt] at hp
            lo := fun p hp => by simp [headSt] at hp
            bnd := fun p hp => by
              simp only [headSt, List.mem_singleton] at hp
              subst hp
              simpa using hidx } }
    -- the read-back run
    obtain ⟨bL', zL', hrunL, hLC'⟩ := liftRun_sound hlsep hlift sa bL zf hLC
    -- the virtual run
    have hW : ∀ r ∈ L0 ++ Fr.map (·.1), (b.reg.lvm r).1 = 64 := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact width_of_getW (hM.1.regs r hr)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact width_of_getW (hFN q hq)
    have hsh : ∀ p ∈ arrShapes E.rs, (b.larr p.1).1 = 64 ∧ (b.larr p.1).2.1 = p.2 := by
      intro p hp
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
      have hpos : 0 < regLen E.rs g.name := by simpa using (List.mem_filter.mp hg).2
      obtain ⟨-, arr, harr, -⟩ := hM.1.cells g.name 0 hpos
      exact shape_of_getArr harr
    obtain ⟨t, zt, hrunV⟩ := runStraightF_of_guardsOK hB hsB hg zf hW hsh
    -- the comparison
    obtain ⟨t', zt', hrun', houts, harr⟩ :=
      straightCheck_sound htv hB hB' (bindRel_headState _ b) hrunV
    rw [hrunL] at hrun'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrun')
    refine ⟨t, zt, hrunV, ⟨⟨fun v hv => ?_, fun hz => hz.elim, fun A j hk => ?_,
      hLC'.corr.slots⟩, ⟨by rw [hsp]; exact hLC'.sp, Abs.holds_empty _ _ _⟩⟩, fun q hq => ?_⟩
    · have ho : (v, liftReg (E.pi v)) ∈ headOuts E L0 Fr :=
        List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
      have := hLC'.corr.regs (liftReg (E.pi v)) ⟨E.pi v, hendL v hv, rfl⟩
      rw [unlift_liftReg (hL0r v hv)] at this
      rw [← this]
      exact getW_of_lvm (houts _ ho).symm 64
    · obtain ⟨hj, arr, ha, hr⟩ := hLC'.corr.cells A j hk
      refine ⟨hj, arr, ?_, hr⟩
      unfold LstateM.getArr at ha ⊢
      rw [← harr A]
      exact ha
    · have ho : (q.1, slotName q.2) ∈ headOuts E L0 Fr :=
        List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
      rw [← hLC'.slots q.2 (hendF q hq)]
      exact getW_of_lvm (houts _ ho).symm 64
  · cases h

end Body

/-! ## The node with its loop body by translation validation -/

section Node

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState Disjoint8 read64)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim (decrOnce)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep (DecSim)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)

/-- **The node check with the loop body by translation validation.** `nodeCheck` with the
    loop-body check `loopOK` replaced by `bodyTV` at the names `Fr` held in frame words and
    the frame offsets `S`: the prologue records the names of `Fr` (`frameRes`), and the frame
    offsets lie in the frame range of `σ` at the loop-head stack pointer. -/
def nodeCheckTV (σ : AbiLayout) (E : MemEnv) (seeds body : List LinstrRM) (top endL : LLabel)
    (ctr R : String) (L0 : List String) (Fr : List (String × Int)) (S : List Int)
    (pre post : List (JInstr 64)) (l : XLoop 64) : Bool :=
  E.sp == "%rsp" && rsOK σ E.rs
    && (match preRes E (abiReg σ) σ.bounds σ.frameLo σ.frameHi L0 ctr R seeds pre with
      | some p => S.all fun o => decide (σ.frameLo ≤ p.sp + o) && decide (p.sp + o ≤ σ.frameHi)
      | none => false)
    && frameRes (abiReg σ) σ.frameLo σ.frameHi Fr seeds pre
    && seeds.all isLopnB && body.all isLopnB && top != endL
    && bodyTV E L0 Fr R S body l.body && decide (ctr ∈ L0) && l.ctr == E.pi ctr
    && decrOnce (E.pi ctr) l.body && incrOnce R l.body && post.all noStoreB

/-- **The node from the System V entry, with the loop body by translation validation.** The
    conclusion of `decNodeAbi_halts` for a node that passes `nodeCheckTV`. -/
theorem decNodeAbi_halts_tv (σ : AbiLayout) (E : MemEnv) (fn : String)
    (seeds body : List LinstrRM) (top endL : LLabel) (ctr R : String) (L0 : List String)
    (Fr : List (String × Int)) (S : List Int) (pre post : List (JInstr 64)) (l : XLoop 64)
    (hchk : nodeCheckTV σ E seeds body top endL ctr R L0 Fr S pre post l = true)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hreg : σ.Regions sa)
    (hent : NodeEntry (abiReg σ) E.rs sa b) :
    ∃ sa' t k, Halts aMachine (nodeLayout pre l post) 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∀ A j, regK E.rs A j → ∃ arr : Fin (regLen E.rs A) → BitVec 64,
          t.prog.base.getArr A 64 (regLen E.rs A) = some arr
            ∧ read64 sa'.mem ((regLay E.rs (abiBase (abiReg σ) sa)).addr A j)
              = stackGet arr j := by
  simp only [nodeCheckTV, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp, hrs⟩, hS⟩, hfr⟩, hsL⟩, hbL⟩, htop⟩, hbody⟩, hctr⟩, hlctr⟩, hdec⟩,
    hinc⟩, hpost⟩ := hchk
  split at hS
  · rename_i p hp
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hS
    have hsep := memSep_of_regions hrs hreg p.sp (preRes_slots hp)
    have hcell : ∀ off ∈ S, ∀ A j, regK E.rs A j →
        Disjoint8 ((regLay E.rs (abiBase (abiReg σ) sa)).addr A j)
          (sa.regs "%rsp" + BitVec.ofInt 64 p.sp + BitVec.ofInt 64 off) := by
      intro off ho A j hk
      have := frameSep_of_regions hrs hreg A j hk (p.sp + off) (hS off ho).1 (hS off ho).2
      rw [BitVec.ofInt_add, ← BitVec.add_assoc] at this
      exact this.symm
    exact decNodeMem_halts_fr fn seeds body top endL ctr R L0 Fr pre post l hsL hbL htop
      (decSim_body_tv hsep hsp hbody hcell) hctr hlctr hdec hinc hpost _
      (decSim_pre_fr hsp hp hfr sa (frameSep_of_regions hrs hreg) hreg.1)
      sa b zf hpc ⟨rfl, hent⟩
  · cases hS

/-- **The decoded bytes of a node realise the result read-back**, with the loop body by
    translation validation: the conclusion of `decNodeAbi_result` for a node that passes
    `nodeCheckTV`. -/
theorem decNodeAbi_result_tv (σ : AbiLayout) (E : MemEnv) (fn : String)
    (seeds body : List LinstrRM) (top endL : LLabel) (ctr R : String) (L0 : List String)
    (Fr : List (String × Int)) (S : List Int) (pre post : List (JInstr 64)) (l : XLoop 64)
    (bytes : List (BitVec 8))
    (hdec : LprogBytesDecode.decodeLprog bytes = some (nodeLayout pre l post))
    (hchk : nodeCheckTV σ E seeds body top endL ctr R L0 Fr S pre post l = true)
    (A RA : String) (hA : abiReg σ A = some RA)
    (hres : σ.result = .words RA (regLen E.rs A)) (hn : 0 < regLen E.rs A)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hreg : σ.Regions sa)
    (hent : NodeEntry (abiReg σ) E.rs sa b) :
    ∃ prog sa' t k, LprogBytesDecode.decodeLprog bytes = some prog
      ∧ Halts aMachine prog 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∃ arr : Fin (regLen E.rs A) → BitVec 64,
          t.prog.base.getArr A 64 (regLen E.rs A) = some arr
            ∧ σ.ResultOf sa sa'
                (.array ((List.range (regLen E.rs A)).map fun j => .int (stackGet arr j).toNat)) := by
  obtain ⟨sa', t, k, hh, hrun, hcells⟩ := decNodeAbi_halts_tv σ E fn seeds body top endL ctr R
    L0 Fr S pre post l hchk sa b zf hpc hreg hent
  obtain ⟨arr, ha, hR⟩ := result_of_cells σ E A RA hA hres hn sa sa' t hcells
  exact ⟨_, sa', t, k, hdec, hh, hrun, arr, ha, hR⟩

end Node

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoopTVLeg
