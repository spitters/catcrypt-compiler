/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage

@[expose] public section

set_option autoImplicit false

/-!
# The name-keyed image of a printed body simulated on the address machine

`JasminLsemAddrImage.virtImg` rewrites a printed physical body to a body the name-keyed
machine `lsemFuelMemF` runs. This module relates a step of the image to a step of the
address machine `JasminLsemAddrRun.stepA` on the printed body.

## A register instruction through its symbolic description

A register instruction is stepped by both machines through the step `fstepF` on a register
file, from two register files that differ at the frame-slot names. The symbolic step
`OwnedLprogTV.symStep` from the start state describes the step exactly by terms over the
start registers. When the guards and the written terms of the description read no array
(`termArrFree`), two states that agree on the names the description reads and on the flags
step to states that agree on the written registers and the flags, and each keeps its other
registers and its arrays (`step_congr`).

## The relation

`ImgRel` relates a state of the image to an address state: equal program counters, flags
and names without a frame word; a frame-word name holds its frame word; each array holds the
words at its base; the frame word of an array pointer holds the base once its save has run;
after a reload the reloaded register holds the frame word. `ImgSep` is the separation of
frame words, array words and the red-zone word. `imgGateB` is the decided condition on the
body: each instruction is a label, a branch on a condition code, an indexed access through a
reloaded array pointer, a frame-word move or compare, or a register instruction whose
symbolic description reads and writes no frame word and no array (`regGateB`); and every
reload of an array pointer follows its save (`reloadSavedB`).

## Main results

* `termArrFree`, `termArrFree_ev`: a term reading no array has one value for all arrays.
* `descReads`, `descArrFree`, `step_congr`: the congruence of a described step.
* `reg_step`: a register instruction on the two machines.
* `rel_reg`, `rel_sload`, `rel_sstore`, `rel_scmp`, `rel_ldx`, `rel_stx`, `rel_label`,
  `rel_jump`: each kind of instruction keeps the relation.
* `img_step`: one checked step of the image is one or two steps of the address machine.
* `image_addr_sim`: a halting checked run of the image is matched by a halting run of the
  address machine on the body, with the relation at the end and every indexed load outside
  the red-zone word (`RunSafe`, `LoadSafeAt`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-! ## 1. Terms that read no array -/

/-- The symbolic word reads no array. -/
def termArrFree : STerm → Bool
  | .reg _ => true
  | .immW _ _ => true
  | .immAt _ x => termArrFree x
  | .bin _ x y => termArrFree x && termArrFree y
  | .un _ x => termArrFree x
  | .shImm _ _ x => termArrFree x
  | .aget _ _ _ _ => false
  | .cin _ => true
  | .aluF _ _ x y o => termArrFree x && termArrFree y && termArrFree o
  | .carryW _ x y c => termArrFree x && termArrFree y && termArrFree c
  | .carryF _ _ x y c => termArrFree x && termArrFree y && termArrFree c
  | .mulx _ x y => termArrFree x && termArrFree y
  | .ref _ => true

/-- A term reading no array has one value for all arrays. -/
theorem termArrFree_ev (V : String → Σ w, BitVec w) (A A' : String → ArrCell) (C O : Bool) :
    ∀ t : STerm, termArrFree t = true → t.ev V A C O = t.ev V A' C O
  | .reg _, _ => rfl
  | .immW _ _, _ => rfl
  | .immAt _ x, h => by
      rw [STerm.ev, STerm.ev, termArrFree_ev V A A' C O x (by simpa [termArrFree] using h)]
  | .bin _ x y, h => by
      simp only [termArrFree, Bool.and_eq_true] at h
      rw [STerm.ev, STerm.ev, termArrFree_ev V A A' C O x h.1, termArrFree_ev V A A' C O y h.2]
  | .un _ x, h => by
      rw [STerm.ev, STerm.ev, termArrFree_ev V A A' C O x (by simpa [termArrFree] using h)]
  | .shImm _ _ x, h => by
      rw [STerm.ev, STerm.ev, termArrFree_ev V A A' C O x (by simpa [termArrFree] using h)]
  | .aget _ _ _ _, h => by simp [termArrFree] at h
  | .cin _, _ => rfl
  | .aluF _ _ x y o, h => by
      simp only [termArrFree, Bool.and_eq_true] at h
      rw [STerm.ev, STerm.ev, termArrFree_ev V A A' C O x h.1.1,
        termArrFree_ev V A A' C O y h.1.2, termArrFree_ev V A A' C O o h.2]
  | .carryW _ x y c, h => by
      simp only [termArrFree, Bool.and_eq_true] at h
      rw [STerm.ev, STerm.ev, termArrFree_ev V A A' C O x h.1.1,
        termArrFree_ev V A A' C O y h.1.2, termArrFree_ev V A A' C O c h.2]
  | .carryF _ _ x y c, h => by
      simp only [termArrFree, Bool.and_eq_true] at h
      rw [STerm.ev, STerm.ev, termArrFree_ev V A A' C O x h.1.1,
        termArrFree_ev V A A' C O y h.1.2, termArrFree_ev V A A' C O c h.2]
  | .mulx _ x y, h => by
      simp only [termArrFree, Bool.and_eq_true] at h
      rw [STerm.ev, STerm.ev, termArrFree_ev V A A' C O x h.1, termArrFree_ev V A A' C O y h.2]
  | .ref _, _ => rfl

/-- The guard reads no array. -/
def guardArrFree : SG → Bool
  | .wid t _ => termArrFree t
  | .eqW x y => termArrFree x && termArrFree y
  | .shp _ _ _ => false

theorem guardArrFree_holds (V : String → Σ w, BitVec w) (A A' : String → ArrCell)
    (C O : Bool) (g : SG) (h : guardArrFree g = true) : g.holds V A C O ↔ g.holds V A' C O := by
  cases g with
  | wid t w => simp only [SG.holds, termArrFree_ev V A A' C O t h]
  | eqW x y =>
      simp only [guardArrFree, Bool.and_eq_true] at h
      simp only [SG.holds, termArrFree_ev V A A' C O x h.1, termArrFree_ev V A A' C O y h.2]
  | shp _ _ _ => simp [guardArrFree] at h

/-- The symbolic zero flag reads no array. -/
def flagArrFree : SFlag → Bool
  | .init => true
  | .cmp x y => termArrFree x && termArrFree y

theorem flagArrFree_ev (V : String → Σ w, BitVec w) (A A' : String → ArrCell) (C O Z : Bool)
    (f : SFlag) (h : flagArrFree f = true) : f.ev V A C O Z = f.ev V A' C O Z := by
  cases f with
  | init => rfl
  | cmp x y =>
      simp only [flagArrFree, Bool.and_eq_true] at h
      simp only [SFlag.ev, termArrFree_ev V A A' C O x h.1, termArrFree_ev V A A' C O y h.2]

/-! ## 2. The congruence of a described step -/

/-- The start registers a one-step description `ss`, `gs` reads: in its guards, its written
    registers, its carry and overflow flags and its zero flag. -/
def descReads (ss : SSt) (gs : List SG) : List String :=
  gs.flatMap SG.vars ++ ss.wr.flatMap (fun r => (ss.regs r).vars) ++ ss.cf.vars ++ ss.of.vars
    ++ ss.zf.vars

/-- The one-step description reads no array and writes none. -/
def descArrFree (ss : SSt) (gs : List SG) : Bool :=
  gs.all guardArrFree && ss.wr.all (fun r => termArrFree (ss.regs r)) && termArrFree ss.cf
    && termArrFree ss.of && flagArrFree ss.zf && ss.awr.isEmpty

/-- **The congruence of a described step.** Let the symbolic step of `i` from the start
    state be `ok ss gs`, reading no array. From two states that agree on the registers the
    description reads and on the zero, carry and overflow flags, a successful step from the
    first is matched by a successful step from the second; the two results agree on the
    registers written and on the flags, and each keeps the other registers and the arrays of
    its start. -/
theorem step_congr (P P' : LprogM) (i : LinstrRM) {ss : SSt} {gs : List SG}
    (h : symStep i SSt.start = .ok ss gs) (ha : descArrFree ss gs = true) (s s' t : LstateMF)
    (hv : ∀ r ∈ descReads ss gs, s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
    (hz : s'.zf = s.zf) (hc : s'.prog.base.cf = s.prog.base.cf)
    (ho : s'.prog.base.of = s.prog.base.of)
    (hs : evalInstrPMemF P i s = some t) :
    ∃ t', evalInstrPMemF P' i s' = some t'
      ∧ (∀ r, r ∈ ss.wr → t'.prog.base.reg.lvm r = t.prog.base.reg.lvm r)
      ∧ (∀ r, r ∉ ss.wr → t'.prog.base.reg.lvm r = s'.prog.base.reg.lvm r)
      ∧ (∀ r, r ∉ ss.wr → t.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
      ∧ t'.zf = t.zf ∧ t'.prog.base.cf = t.prog.base.cf ∧ t'.prog.base.of = t.prog.base.of
      ∧ t'.prog.base.larr = s'.prog.base.larr ∧ t.prog.base.larr = s.prog.base.larr
      ∧ t'.prog.base.reg.lpc = s'.prog.base.reg.lpc + 1
      ∧ t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1
      ∧ (∀ r, t'.prog.base.reg.lvm r =
          (ss.regs r).ev s'.prog.base.reg.lvm s'.prog.base.larr s.prog.base.cf
            s.prog.base.of) := by
  simp only [descArrFree, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at ha
  obtain ⟨⟨⟨⟨⟨hag, haw⟩, hacf⟩, haof⟩, hazf⟩, hawr⟩ := ha
  have hg := symStep_good i SSt.good_start h
  have hD := symStep_sound P i SSt.start s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf
    s.prog.base.of s.zf s (holds_start s)
  have hD' := symStep_sound P' i SSt.start s'.prog.base.reg.lvm s'.prog.base.larr
    s.prog.base.cf s.prog.base.of s'.zf s' (by rw [← hc, ← ho]; exact holds_start s')
  rw [h] at hD hD'
  obtain ⟨hG, hH, hF⟩ := hD.1 t hs
  -- a term read by the description has one value at the two starts
  have hterm : ∀ x : STerm, termArrFree x = true → (∀ r ∈ x.vars, r ∈ descReads ss gs) →
      x.ev s'.prog.base.reg.lvm s'.prog.base.larr s.prog.base.cf s.prog.base.of
        = x.ev s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf s.prog.base.of := by
    intro x hx hxv
    rw [termArrFree_ev _ s'.prog.base.larr s.prog.base.larr _ _ x hx]
    exact STerm.ev_congr _ x (fun r hr => hv r (hxv r hr)) (fun _ => ⟨rfl, rfl⟩)
  have hG' : AllG s'.prog.base.reg.lvm s'.prog.base.larr s.prog.base.cf s.prog.base.of gs := by
    intro g hgm
    rw [guardArrFree_holds _ s'.prog.base.larr s.prog.base.larr _ _ g (hag g hgm)]
    refine (SG.holds_congr _ g (fun r hr => hv r ?_) (fun _ => ⟨rfl, rfl⟩)).mpr (hG g hgm)
    simp only [descReads, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨g, hgm, hr⟩)))
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hD'.2 hG')
  obtain ⟨-, hH', hF'⟩ := hD'.1 t' ht'
  refine ⟨t', ht', fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hF.2.1, hH'.1⟩
  · rw [hH'.1 r, hH.1 r]
    refine hterm _ (haw r hr) fun q hq => ?_
    simp only [descReads, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨r, hr, hq⟩)))
  · rw [hH'.1 r, hg.1 r hr]; rfl
  · rw [hH.1 r, hg.1 r hr]; rfl
  · rw [hH'.2.2.1, hH.2.2.1, hz,
      flagArrFree_ev _ s'.prog.base.larr s.prog.base.larr _ _ _ ss.zf hazf]
    exact SFlag.ev_congr _ ss.zf (fun r hr => hv r (by
        simp only [descReads, List.mem_append]; exact Or.inr hr))
      (fun _ => ⟨rfl, rfl, rfl⟩)
  · rw [hH'.2.2.2.1, hH.2.2.2.1]
    congr 1
    refine hterm _ hacf fun q hq => ?_
    simp only [descReads, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hq))
  · rw [hH'.2.2.2.2, hH.2.2.2.2]
    congr 1
    refine hterm _ haof fun q hq => ?_
    simp only [descReads, List.mem_append]
    exact Or.inl (Or.inr hq)
  · funext q
    rw [hH'.2.1 q, hg.2 q (by simp [hawr])]
    rfl
  · funext q
    rw [hH.2.1 q, hg.2 q (by simp [hawr])]
    rfl
  · exact hF'.2.1

/-! ## 3. A register instruction on the two machines -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (baseOf fstepA_of_reg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
  (read64 write64 read64_write64_same read64_write64_of_disjoint)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackSet stackGet_id)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk isRetB)

/-- **The gate condition of a register instruction** at the frame `frame`: it moves and
    compares no frame word, its symbolic step from the start is described, reads no array,
    and reads and writes only names without a frame word. -/
def regOkB (frame : String → Option (BitVec 64)) (x : LinstrR) : Bool :=
  (slotMov? x).all (fun ds => (frame ds.1).isNone && (frame ds.2).isNone)
    && (slotCmp? x).all (fun dxq => (frame dxq.2.2).isNone)
    && match symStep (x, .reg none) SSt.start with
      | .ok ss gs => descArrFree ss gs && (descReads ss gs).all (fun r => (frame r).isNone)
          && ss.wr.all (fun r => (frame r).isNone)
      | _ => false

/-- The symbolic word has width `64` when every general-purpose name has width `64`: its
    width base (`STerm.wbase`) is a general-purpose name or has the known width `64`. -/
def wid64B (t : STerm) : Bool :=
  match t.wbase with
  | .reg x => gpOk x
  | u => u.wknown == some 64

/-- `regOkB`, and every general-purpose name the instruction writes receives a word of width
    `64`. -/
def regGateB (frame : String → Option (BitVec 64)) (x : LinstrR) : Bool :=
  regOkB frame x &&
    match symStep (x, .reg none) SSt.start with
    | .ok ss _ => ss.wr.all (fun r => !gpOk r || wid64B (ss.regs r))
    | _ => false

theorem wid64B_ev {t : STerm} (h : wid64B t = true) {V : String → Σ w, BitVec w}
    (A : String → ArrCell) (C O : Bool) (hV : ∀ r, gpOk r = true → (V r).1 = 64) :
    (t.ev V A C O).1 = 64 := by
  rw [← STerm.wbase_ev V A C O t]
  unfold wid64B at h
  split at h
  · rename_i x hx
    rw [hx]
    exact hV x h
  · exact STerm.wknown_ev V A C O (by simpa using h)

/-- **A register instruction.** A step of the name-keyed machine on a register instruction
    that passes `regGateB` is matched by a step of the address machine from a state that
    agrees with it off the frame words and on the flags: the address machine keeps its
    memory, the results agree off the frame words and on the flags, the name-keyed step
    keeps the frame-word names and the arrays, and the general-purpose names keep width
    `64`. -/
theorem reg_step {frame : String → Option (BitVec 64)} {x : LinstrR}
    (hx : IsLopn (x, MemTag.reg none)) (hgate : regGateB frame x = true) (P : LprogM)
    (s t : LstateMF) (sa : LstateA) (zf : Bool)
    (hregs : ∀ r, frame r = none → s.prog.base.reg.lvm r = sa.reg.lvm r)
    (hz : s.zf = zf) (hc : sa.cf = s.prog.base.cf) (ho : sa.of = s.prog.base.of)
    (hwid : ∀ r, gpOk r = true → (sa.reg.lvm r).1 = 64)
    (hs : evalInstrPMemF P (x, .reg none) s = some t) :
    ∃ sa', fstepA frame (x, .reg none) sa zf = some (sa', t.zf) ∧ sa'.mem = sa.mem
      ∧ (∀ r, frame r = none → t.prog.base.reg.lvm r = sa'.reg.lvm r)
      ∧ (∀ r, frame r ≠ none → t.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
      ∧ sa'.cf = t.prog.base.cf ∧ sa'.of = t.prog.base.of
      ∧ sa'.reg.lpc = sa.reg.lpc + 1 ∧ t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1
      ∧ t.prog.base.larr = s.prog.base.larr
      ∧ (∀ r, gpOk r = true → (sa'.reg.lvm r).1 = 64) := by
  simp only [regGateB, Bool.and_eq_true] at hgate
  obtain ⟨hok, hwg⟩ := hgate
  simp only [regOkB, Bool.and_eq_true] at hok
  obtain ⟨⟨hmov, hcmp⟩, hsym⟩ := hok
  have hmov' : ∀ d s, slotMov? (x, MemTag.reg none).fst = some (d, s) →
      frame s = none ∧ frame d = none := by
    intro d s' h
    rw [h] at hmov
    simp only [Option.all_some, Bool.and_eq_true, Option.isNone_iff_eq_none] at hmov
    exact ⟨hmov.2, hmov.1⟩
  have hcmp' : ∀ d y q, slotCmp? (x, MemTag.reg none).fst = some (d, y, q) → frame q = none := by
    intro d y q h
    rw [h] at hcmp
    simpa using hcmp
  cases hS : symStep (x, .reg none) SSt.start with
  | fail => rw [hS] at hsym; cases hsym
  | unk => rw [hS] at hsym; cases hsym
  | ok ss gs =>
    rw [hS] at hsym
    simp only [Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at hsym
    obtain ⟨⟨hA, hR⟩, hW⟩ := hsym
    let sMF : LstateMF := ⟨⟨baseOf sa, s.prog.lfn⟩, zf⟩
    rw [hS] at hwg
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hwg
    obtain ⟨t', ht', hwr, hkeep', hkeep, hzf, hcf, hof, -, hlarr, -, hlpc, hval⟩ :=
      step_congr P P (x, .reg none) hS hA s sMF t
        (fun r hr => (hregs r (hR r hr)).symm) hz.symm hc ho hs
    rw [evalInstrPMemF_isLopn P _ sMF hx] at ht'
    obtain ⟨⟨b, z⟩, hb, rfl⟩ := Option.map_eq_some_iff.mp ht'
    refine ⟨{ sa with reg := b.reg, cf := b.cf, of := b.of }, ?_, rfl, fun r hr => ?_,
      fun r hr => ?_, hcf, hof, ?_, hlpc, ?_, fun r hr => ?_⟩
    · rw [fstepA_of_reg frame rfl hmov' hcmp']
      simp only [regStepA]
      rw [show ({ reg := sa.reg, cf := sa.cf, of := sa.of } : LstateM) = baseOf sa from rfl, hb]
      simp only [Option.map_some]
      rw [← hzf]
    · by_cases hw : r ∈ ss.wr
      · exact (hwr r hw).symm
      · rw [hkeep r hw, hregs r hr]
        exact (hkeep' r hw).symm
    · exact hkeep r (fun hw => hr (hW r hw))
    · exact JasminLsemMemFlagNestJoin.fstepF_lpc_succ _ _ _ _ _ hb
    · exact hlarr
    · show (b.reg.lvm r).1 = 64
      by_cases hw : r ∈ ss.wr
      · have e := hval r
        simp only at e
        rw [e]
        rcases hwg r hw with h1 | h1
        · rw [hr] at h1; cases h1
        · exact wid64B_ev h1 _ _ _ hwid
      · have e := hkeep' r hw
        simp only at e
        rw [e]
        exact hwid r hr

/-! ## 4. Frame-word moves and compares -/

theorem slotMov?_cases {x : LinstrR} {d q : String} (h : slotMov? x = some (d, q)) :
    x = .Lopn [.reg d] "MOVQ" [.reg q] ∨ x = .Lopn [.reg d] "MOV:64" [.reg q] := by
  unfold slotMov? at h
  split at h
  · split_ifs at h with hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rcases hm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · cases h

/-- The name-keyed step of a frame-word move copies the source register. -/
theorem eval_slotMov (P : LprogM) {x : LinstrR} {d q : String} (h : slotMov? x = some (d, q))
    (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (x, tag) s = some { s with prog := { s.prog with
      base := (s.prog.base.setReg d (s.prog.base.reg.lvm q).2).nextPc } } := by
  have hc : cmpArgs? (x, tag) = none := by
    rcases slotMov?_cases h with rfl | rfl <;> rfl
  have hm : movRegArgs? (x, tag) = some (d, q) := by
    rcases slotMov?_cases h with rfl | rfl
    · simp only [movRegArgs?, show stripWidthTag "MOVQ" = "MOVQ" by decide +kernel]
      rfl
    · simp only [movRegArgs?, show stripWidthTag "MOV:64" = "MOV" by decide +kernel]
      rfl
  unfold evalInstrPMemF
  rw [hc]
  simp only []
  rw [hm]
  rfl

/-- **A frame-word load.** The address machine loads the frame word into the destination. -/
theorem fstepA_slotLoad (frame : String → Option (BitVec 64)) {x : LinstrR} {d q : String}
    (h : slotMov? x = some (d, q)) {a : BitVec 64} (ha : frame q = some a) (sa : LstateA)
    (zf : Bool) :
    fstepA frame (x, .reg none) sa zf
      = some ({ sa with reg := (sa.reg.setReg d (read64 sa.mem a)).nextPc }, zf) := by
  simp [fstepA, h, ha]

/-- **A frame-word store.** The address machine stores the source register at the frame
    word of the destination. -/
theorem fstepA_slotStore (frame : String → Option (BitVec 64)) {x : LinstrR} {q S : String}
    (h : slotMov? x = some (q, S)) (hS : frame S = none) {a : BitVec 64} (ha : frame q = some a)
    (sa : LstateA) (zf : Bool) {v : BitVec 64} (hv : sa.reg.getW S 64 = some v) :
    fstepA frame (x, .reg none) sa zf
      = some ({ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a v }, zf) := by
  simp [fstepA, h, ha, hS, hv]

theorem slotCmp?_eq {x : LinstrR} {d y q : String} (h : slotCmp? x = some (d, y, q)) :
    x = .Lopn [.reg d] "CMP:64" [.reg y, .reg q] := by
  unfold slotCmp? at h
  split at h
  · split_ifs at h with hm
    obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
    rw [hm]
  · cases h

theorem withWidthTag_CMP : withWidthTag 64 "CMP" = "CMP:64" := by decide +kernel

/-- The name-keyed step of a compare against a frame-word name compares at width `64`. -/
theorem eval_slotCmp (P : LprogM) {x : LinstrR} {d y q : String}
    (h : slotCmp? x = some (d, y, q)) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (x, tag) s =
      match s.prog.base.reg.getW y 64, s.prog.base.reg.getW q 64 with
      | some va, some vb =>
          some { prog := { s.prog with base := s.prog.base.nextPc }, zf := va == vb }
      | _, _ => none := by
  rw [slotCmp?_eq h]
  have hc : cmpArgs? (LinstrR.Lopn [.reg d] "CMP:64" [.reg y, .reg q], tag)
      = some (.reg y, .reg q) := by
    simp only [cmpArgs?, withWidthTag_CMP, if_true]
  unfold evalInstrPMemF
  rw [hc]
  rfl

/-- **A compare against a frame word.** The address machine compares at width `64` with
    the frame word. -/
theorem fstepA_slotCmp (frame : String → Option (BitVec 64)) {x : LinstrR} {d y q : String}
    (h : slotCmp? x = some (d, y, q)) {a : BitVec 64} (ha : frame q = some a) (sa : LstateA)
    (zf : Bool) :
    fstepA frame (x, .reg none) sa zf =
      match sa.reg.getW y 64 with
      | some va => some ({ sa with reg := sa.reg.nextPc }, va == read64 sa.mem a)
      | none => none := by
  have hx := slotCmp?_eq h
  have hm : slotMov? x = none := by rw [hx]; rfl
  simp only [fstepA, hm, h, ha, regStepA, fstepF, cmpArgs?, withWidthTag_CMP, if_true,
    evalOperandN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  cases sa.reg.getW y 64 <;> rfl

/-! ## 5. Indexed loads and stores -/

/-- The name-keyed step of an indexed load of the array `A` at shape `(64, n)`. -/
theorem eval_loadIdx (P : LprogM) (d A idx : String) (n : Nat) (s : LstateMF) :
    evalInstrPMemF P (.Lopn [.reg d] "LOADIDX" [.arrIdx A idx 8], .load 64 n) s =
      match s.prog.base.getArr A 64 n, s.prog.base.reg.getW idx 64 with
      | some arr, some vi =>
          some { s with prog := { s.prog with
            base := (s.prog.base.setReg d (stackGet arr vi.toNat)).nextPc } }
      | _, _ => none := by
  rw [evalInstrPMemF_isLopn P _ s ⟨_, _, _, rfl⟩]
  simp only [fstepF, cmpArgs?, movRegArgs?]
  rw [stepMemF_of_quiet rfl rfl rfl]
  simp only [lsemStepMem, loadStruct?, if_true]
  cases s.prog.base.getArr A 64 n <;> cases s.prog.base.reg.getW idx 64 <;> rfl

/-- The name-keyed step of an indexed store into the array `A` at shape `(64, n)`. -/
theorem eval_storeIdx (P : LprogM) (A idx v : String) (n : Nat) (s : LstateMF) :
    evalInstrPMemF P (.Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v], .store 64 n) s =
      match s.prog.base.getArr A 64 n, s.prog.base.reg.getW idx 64, s.prog.base.reg.getW v 64 with
      | some arr, some vi, some vv =>
          some { s with prog := { s.prog with
            base := (s.prog.base.setArr A (stackSet arr vi.toNat vv)).nextPc } }
      | _, _, _ => none := by
  rw [evalInstrPMemF_isLopn P _ s ⟨_, _, _, rfl⟩]
  simp only [fstepF, cmpArgs?, movRegArgs?]
  rw [stepMemF_of_quiet rfl rfl rfl]
  simp only [lsemStepMem, storeStruct?, if_true]
  cases s.prog.base.getArr A 64 n <;> cases s.prog.base.reg.getW idx 64 <;>
    cases s.prog.base.reg.getW v 64 <;> rfl

/-- The address-machine step of an indexed load through the register `b`. -/
theorem fstepA_loadIdx (frame : String → Option (BitVec 64)) (d b idx : String) (n : Nat)
    (sa : LstateA) (zf : Bool) :
    fstepA frame (.Lopn [.reg d] "LOADIDX" [.arrIdx b idx 8], .load 64 n) sa zf =
      match sa.reg.getW b 64, sa.reg.getW idx 64 with
      | some p, some vi => some ({ sa with reg := (sa.reg.setReg d
          (read64 sa.mem (p + BitVec.ofNat 64 (8 * vi.toNat)))).nextPc }, zf)
      | _, _ => none := by
  simp only [fstepA, loadIdxA?, if_true]
  cases sa.reg.getW b 64 <;> cases sa.reg.getW idx 64 <;> rfl

/-- The address-machine step of an indexed store through the register `b`. -/
theorem fstepA_storeIdx (frame : String → Option (BitVec 64)) (d b idx v : String) (n : Nat)
    (sa : LstateA) (zf : Bool) :
    fstepA frame (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v], .store 64 n) sa zf =
      match sa.reg.getW b 64, sa.reg.getW idx 64, sa.reg.getW v 64 with
      | some p, some vi, some vv =>
          some ({ sa with
            reg := sa.reg.nextPc
            mem := write64 sa.mem (p + BitVec.ofNat 64 (8 * vi.toNat)) vv }, zf)
      | _, _, _ => none := by
  simp only [fstepA, storeIdxA?, if_true]
  cases sa.reg.getW b 64 <;> cases sa.reg.getW idx 64 <;> cases sa.reg.getW v 64 <;> rfl

/-! ## 6. Labels and branches -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel)

theorem isLabel_imgInstr (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (i : LinstrR) (l : LLabel) :
    isLabel l (imgInstr slotArr body k i).1 = isLabelB l i := by
  cases i with
  | Lopn ds o ss =>
      have h : ∀ p : LinstrRM, (∃ ds' o' ss', p.1 = .Lopn ds' o' ss') → isLabel l p.1 = false := by
        rintro p ⟨ds', o', ss', hp⟩
        rw [hp]; rfl
      rw [h _ ?_]
      · rfl
      · unfold imgInstr
        repeat' split
        all_goals exact ⟨_, _, _, rfl⟩
  | Llabel ii l' =>
      simp only [imgInstr, normA, isLabel, isLabelB]
      cases h : (l == l') <;> cases h' : (l' == l) <;> simp_all [beq_iff_eq]
  | _ => rfl

/-- **The labels of the image are the labels of the body**, when the final instruction of
    the body is no label. -/
theorem findLabel_virtImg (slotArr : String → Option (String × Nat)) (body : Lcmd) (l : LLabel)
    (hlast : ∀ r ∈ body.getLast?, isLabelB l r.li_i = false) :
    findLabel l ((virtImg slotArr body).map Prod.fst) = labelAt body l := by
  have hmap : ((virtImg slotArr body).map Prod.fst).map (isLabel l)
      = body.dropLast.map (fun i => isLabelB l i.li_i) := by
    apply List.ext_getElem
    · simp [virtImg]
    · intro n h1 h2
      simp only [virtImg, List.getElem_map, List.getElem_mapIdx]
      exact isLabel_imgInstr slotArr body n _ l
  have e1 : findLabel l ((virtImg slotArr body).map Prod.fst)
      = (((virtImg slotArr body).map Prod.fst).map (isLabel l)).findIdx? id := by
    rw [List.findIdx?_map]; rfl
  rw [e1, hmap, List.findIdx?_map]
  unfold labelAt
  cases hb : body.getLast? with
  | none =>
      rw [List.getLast?_eq_none_iff] at hb
      subst hb
      rfl
  | some r =>
      have hr := hlast r (by simp [hb])
      conv_rhs => rw [← List.dropLast_append_getLast? r hb]
      rw [List.findIdx?_append]
      simp [hr]

/-- The name-keyed step of a label advances the program counter. -/
theorem eval_label (P : LprogM) (ii : _) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (.Llabel ii l, tag) s =
      some { s with prog := { s.prog with base := s.prog.base.nextPc } } := by
  rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl rfl]
  rfl

theorem ccPol_reg (cc : String) : ccPol (.reg cc) = condPol cc := by
  unfold ccPol condPol
  split <;> simp_all

/-- The name-keyed step of a branch on a condition code: to one past the label when the
    zero flag has the polarity of the code, to the next instruction otherwise. -/
theorem eval_cond (fn : String) (B : List LinstrRM) (cc : String) (l : LLabel) (tag : MemTag)
    {pol : Bool} (hpol : condPol cc = some pol) {q : Nat}
    (hq : findLabel l (B.map Prod.fst) = some q) (s : LstateMF) :
    evalInstrPMemF (singletonProgM fn B) (.Lcond (.reg cc) l, tag) s =
      if s.zf = pol then
        some { s with prog := { s.prog with base := s.prog.base.setLpc (q + 1) } }
      else some { s with prog := { s.prog with base := s.prog.base.nextPc } } := by
  rw [evalInstrPMemF_cond]
  simp only [decC, ccPol_reg, hpol, beq_iff_eq, evalJumpMem_single hq, Option.map_some]

/-! ## 7. The gate, the separation and the relation -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (Disjoint8)

/-- The kind of an instruction of a printed body for the image simulation. -/
inductive ICase where
  /-- A label. -/
  | label
  /-- A branch on the condition code `cc` to `l`. -/
  | cond (cc : String) (l : LLabel)
  /-- An indexed load `d := [b + 8·idx]`. -/
  | ldx (d b idx : String)
  /-- An indexed store `[b + 8·idx] := v`. -/
  | stx (d b idx v : String)
  /-- A load of the frame word `q` into `d`. -/
  | sload (d q : String)
  /-- A store of `S` into the frame word `q`. -/
  | sstore (q S : String)
  /-- A compare of `y` against the frame word `q`. -/
  | scmp (d y q : String)
  /-- A register instruction. -/
  | reg
  /-- Any other instruction. -/
  | other

/-- The kind of an instruction at the frame `frame`. -/
def icase (frame : String → Option (BitVec 64)) : LinstrR → ICase
  | .Llabel _ _ => .label
  | .Lcond (.reg cc) l => .cond cc l
  | .Lopn [.reg d] o [.arrIdx b idx 8] => if o = "LOADIDX" then .ldx d b idx else .other
  | .Lopn [.reg d] o [.arrIdx b idx 8, .reg v] =>
      if o = "STOREIDX" then .stx d b idx v else .other
  | .Lopn ds o ss =>
      if o = "LOADIDX" ∨ o = "STOREIDX" then .other
      else
        match slotMov? (.Lopn ds o ss) with
        | some (d, q) =>
            match frame d, frame q with
            | none, some _ => .sload d q
            | some _, none => .sstore d q
            | none, none => .reg
            | some _, some _ => .other
        | none =>
            match slotCmp? (.Lopn ds o ss) with
            | some (d, y, q) => if (frame q).isSome then .scmp d y q else .reg
            | none => .reg
  | _ => .other

theorem icase_ldx {frame : String → Option (BitVec 64)} {x : LinstrR} {d b idx : String}
    (h : icase frame x = .ldx d b idx) : x = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx 8] := by
  unfold icase at h
  repeat' split at h
  all_goals first
    | (simp only [ICase.ldx.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; subst_vars; rfl)
    | cases h

theorem icase_stx {frame : String → Option (BitVec 64)} {x : LinstrR} {d b idx v : String}
    (h : icase frame x = .stx d b idx v) :
    x = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v] := by
  unfold icase at h
  repeat' split at h
  all_goals first
    | (simp only [ICase.stx.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; subst_vars; rfl)
    | cases h

theorem icase_sload {frame : String → Option (BitVec 64)} {x : LinstrR} {d q : String}
    (h : icase frame x = .sload d q) :
    slotMov? x = some (d, q) ∧ frame d = none ∧ (frame q).isSome = true := by
  unfold icase at h
  repeat' split at h
  all_goals first
    | (simp only [ICase.sload.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp_all)
    | cases h

theorem icase_sstore {frame : String → Option (BitVec 64)} {x : LinstrR} {q S : String}
    (h : icase frame x = .sstore q S) :
    slotMov? x = some (q, S) ∧ frame S = none ∧ (frame q).isSome = true := by
  unfold icase at h
  repeat' split at h
  all_goals first
    | (simp only [ICase.sstore.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp_all)
    | cases h

theorem icase_scmp {frame : String → Option (BitVec 64)} {x : LinstrR} {d y q : String}
    (h : icase frame x = .scmp d y q) :
    slotCmp? x = some (d, y, q) ∧ (frame q).isSome = true := by
  unfold icase at h
  repeat' split at h
  all_goals first
    | (simp only [ICase.scmp.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp_all)
    | cases h

theorem icase_reg {frame : String → Option (BitVec 64)} {x : LinstrR}
    (h : icase frame x = .reg) :
    ∃ ds o ss, x = .Lopn ds o ss ∧ o ≠ "LOADIDX" ∧ o ≠ "STOREIDX" := by
  unfold icase at h
  repeat' split at h
  all_goals first
    | (subst_vars; exact ⟨_, _, _, rfl, by simp_all, by simp_all⟩)
    | cases h

theorem icase_label {frame : String → Option (BitVec 64)} {x : LinstrR}
    (h : icase frame x = .label) : ∃ ii l, x = .Llabel ii l := by
  unfold icase at h
  repeat' split at h
  all_goals first
    | exact ⟨_, _, rfl⟩
    | cases h

theorem icase_cond {frame : String → Option (BitVec 64)} {x : LinstrR} {cc : String}
    {l : LLabel} (h : icase frame x = .cond cc l) : x = .Lcond (.reg cc) l := by
  unfold icase at h
  repeat' split at h
  all_goals first
    | (simp only [ICase.cond.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
    | cases h

/-- **The gate of instruction `k` of a printed body**: a label; a branch on a condition code
    to a label of the body; an indexed load or store through a reloaded array pointer, with
    index, base, value and destination names without a frame word and a general-purpose
    destination of a load; a load of a frame word into a general-purpose name; a store of a
    general-purpose name into a frame word; a compare against a frame word; or a register
    instruction passing `regGateB`. -/
def instrGateB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (x : LinstrR) : Bool :=
  match icase frame x with
  | .label => true
  | .cond cc l => (condPol cc).isSome && (labelAt body l).isSome
  | .ldx d b idx => (accArr slotArr body k b).isSome && gpOk d && (frame d).isNone
      && (frame idx).isNone && (frame b).isNone
  | .stx _ b idx v => (accArr slotArr body k b).isSome && (frame idx).isNone
      && (frame b).isNone && (frame v).isNone
  | .sload d _ => gpOk d
  | .sstore _ S => gpOk S
  | .scmp _ y _ => (frame y).isNone
  | .reg => regGateB frame (normA x)
  | .other => false

/-- Every reload of the pointer of an array follows a save of that pointer. -/
def reloadSavedB (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  (List.range body.length).all fun k =>
    match body[k]? with
    | some i =>
        match slotMov? i.li_i with
        | some (_, q) =>
            (slotArr q).isNone || (List.range k).any fun j =>
              (body[j]?).any fun i' => isSaveB i'.li_i && ((slotMov? i'.li_i).map Prod.fst == some q)
        | none => true
    | none => true

/-- **The gate of the image simulation**: every instruction but the last passes
    `instrGateB`, the last is the return, and every array-pointer reload follows a save. -/
def imgGateB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all (fun k =>
      (body[k]?).all fun i => instrGateB frame slotArr body k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- The address of word `j` of the array at `p`. -/
abbrev cellAt (p : BitVec 64) (j : Nat) : BitVec 64 := p + BitVec.ofNat 64 (8 * j)

/-- **The separation of the image simulation**: distinct frame words are disjoint; the
    words of the arrays are disjoint from every frame word, from the red-zone word and from
    each other; and an array name has one length. -/
structure ImgSep (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) : Prop where
  frames : ∀ q q' a a', frame q = some a → frame q' = some a' → q ≠ q' → Disjoint8 a a'
  cellFrame : ∀ q A n j, slotArr q = some (A, n) → j < n → ∀ q' a, frame q' = some a →
    Disjoint8 (cellAt (base A) j) a
  cells : ∀ q A n q' A' n' j j', slotArr q = some (A, n) → slotArr q' = some (A', n') →
    j < n → j' < n' → (A ≠ A' ∨ j ≠ j') → Disjoint8 (cellAt (base A) j) (cellAt (base A') j')
  len : ∀ q q' A n n', slotArr q = some (A, n) → slotArr q' = some (A, n') → n = n'
  red : ∀ q A n j, slotArr q = some (A, n) → j < n → Disjoint8 (redW rsp) (cellAt (base A) j)
  gp : ∀ r, gpOk r = true → frame r = none
  slotFrame : ∀ q A n, slotArr q = some (A, n) → ∃ a, frame q = some a

/-- The save of the register `R` into its frame word `qsave.R` is instruction `k`. -/
def SaveAt (body : Lcmd) (k : Nat) (R : String) : Prop :=
  ∃ i, body[k]? = some i ∧ slotMov? i.li_i = some (slotOfReg R, R)

/-- **The relation of the image simulation** between a state `s` of the name-keyed machine
    on the image and a state `sa` of the address machine with zero flag `zf` on the body:
    the program counters, the names without a frame word, the zero, carry and overflow flags
    are equal; a frame-word name holds its frame word; a general-purpose name has width `64`;
    each array holds the words at its base; the frame word of an array pointer holds the
    base once its save has run, and the saved register holds it before; and after a reload
    the reloaded register holds the frame word. -/
structure ImgRel (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (body : Lcmd) (s : LstateMF) (sa : LstateA) (zf : Bool) :
    Prop where
  pc : sa.reg.lpc = s.prog.base.reg.lpc
  regs : ∀ r, frame r = none → s.prog.base.reg.lvm r = sa.reg.lvm r
  slots : ∀ q a, frame q = some a → s.prog.base.reg.lvm q = ⟨64, read64 sa.mem a⟩
  zf : s.zf = zf
  cf : sa.cf = s.prog.base.cf
  of : sa.of = s.prog.base.of
  wid : ∀ r, gpOk r = true → (sa.reg.lvm r).1 = 64
  cells : ∀ q A n, slotArr q = some (A, n) → ∃ arr, s.prog.base.getArr A 64 n = some arr ∧
    ∀ j (hj : j < n), read64 sa.mem (cellAt (base A) j) = arr ⟨j, hj⟩
  saved : ∀ k R A n a, SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
    frame (slotOfReg R) = some a →
      (k < sa.reg.lpc → read64 sa.mem a = base A)
        ∧ (sa.reg.lpc ≤ k → sa.reg.getW R 64 = some (base A))
  reload : ∀ b q a i, 1 ≤ sa.reg.lpc → body[sa.reg.lpc - 1]? = some i →
    slotMov? i.li_i = some (b, q) → frame q = some a → frame b = none →
      sa.reg.lvm b = ⟨64, read64 sa.mem a⟩

/-! ## 8. Facts of the class `physImgB` and of the gate -/

theorem entryRegB_spec {body : Lcmd} {k : Nat} {R : String} (h : entryRegB body k R = true)
    {j : Nat} (hj : j < k) {i : Linstr} (hi : body[j]? = some i) :
    ∃ d src, slotMov? i.li_i = some (d, src) ∧ d ≠ R := by
  unfold entryRegB at h
  rw [List.all_eq_true] at h
  have hm : i ∈ body.take k := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, by rw [List.getElem?_take, if_pos hj, hi]⟩
  have := h i hm
  cases hs : slotMov? i.li_i with
  | none => rw [hs] at this; cases this
  | some p =>
      obtain ⟨d, src⟩ := p
      rw [hs] at this
      exact ⟨d, src, rfl, by simpa using this⟩

theorem physImgB_at {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : physImgB slotArr body = true) {k : Nat} {i : Linstr} (hi : body[k]? = some i) :
    accOkB slotArr body k i.li_i = true ∧ slotWriteB slotArr body k i.li_i = true := by
  unfold physImgB at h
  rw [List.all_eq_true] at h
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have := h k (List.mem_range.mpr hk)
  rw [hi] at this
  simpa using this

/-- A store into the frame word of an array pointer is the save of the register that the
    frame word names, at a point where that register holds its entry value. -/
theorem physImgB_slotStore {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : physImgB slotArr body = true) {k : Nat} {i : Linstr} (hi : body[k]? = some i)
    {q S : String} (hm : slotMov? i.li_i = some (q, S)) (hq : (slotArr q).isSome = true) :
    q = slotOfReg S ∧ entryRegB body k S = true := by
  have hw := (physImgB_at h hi).2
  rcases slotMov?_cases hm with hx | hx <;>
  · rw [hx] at hw hm
    simp only [slotWriteB, List.all_cons, List.all_nil, Bool.and_true, Bool.or_eq_true,
      Option.isNone_iff_eq_none] at hw
    rcases hw with hw | hw
    · rw [hw] at hq; cases hq
    · rw [hm] at hw
      simp only [Bool.and_eq_true, beq_iff_eq] at hw
      exact hw

theorem accArr_spec {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {b A : String} {n : Nat} (h : accArr slotArr body k b = some (A, n)) :
    ∃ k', k = k' + 1 ∧ ∃ i q, body[k']? = some i ∧ slotMov? i.li_i = some (b, q)
      ∧ slotArr q = some (A, n) := by
  unfold accArr at h
  split at h
  · cases h
  · rename_i k'
    refine ⟨k', rfl, ?_⟩
    split at h
    · rename_i j hj
      split at h
      · rename_i d q hdq
        split_ifs at h with hd
        subst hd
        exact ⟨j, q, hj, hdq, h⟩
      · cases h
    · cases h

theorem reloadSavedB_spec {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : reloadSavedB slotArr body = true) {k : Nat} {i : Linstr} (hi : body[k]? = some i)
    {b q : String} (hm : slotMov? i.li_i = some (b, q)) (hq : (slotArr q).isSome = true) :
    ∃ j R, j < k ∧ SaveAt body j R ∧ q = slotOfReg R := by
  unfold reloadSavedB at h
  rw [List.all_eq_true] at h
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have := h k (List.mem_range.mpr hk)
  rw [hi] at this
  simp only [hm, Bool.or_eq_true, Option.isNone_iff_eq_none, List.any_eq_true,
    List.mem_range] at this
  rcases this with hn | ⟨j, hj, hany⟩
  · rw [hn] at hq; cases hq
  · cases hb : body[j]? with
    | none => rw [hb] at hany; cases hany
    | some i' =>
        rw [hb] at hany
        simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hany
        obtain ⟨hs, hq'⟩ := hany
        cases hs' : slotMov? i'.li_i with
        | none => rw [hs'] at hq'; cases hq'
        | some p =>
            obtain ⟨q', R⟩ := p
            rw [hs'] at hq'
            simp only [Option.map_some, Option.some.injEq] at hq'
            subst hq'
            unfold isSaveB at hs
            rw [hs'] at hs
            simp only [beq_iff_eq] at hs
            subst hs
            exact ⟨j, R, hj, ⟨i', hb, hs'⟩, rfl⟩

theorem imgGateB_last {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateB frame slotArr body = true) :
    ∃ r, body.getLast? = some r ∧ r.li_i = .Lret := by
  simp only [imgGateB, Bool.and_eq_true] at h
  obtain ⟨⟨-, h2⟩, -⟩ := h
  cases hl : body.getLast? with
  | none => rw [hl] at h2; cases h2
  | some r =>
      rw [hl] at h2
      simp only [Option.any_some] at h2
      refine ⟨r, rfl, ?_⟩
      revert h2
      cases r.li_i <;> simp [isRetB]

/-- An instruction of the body other than the return is before the last position, where the
    gate holds. -/
theorem imgGateB_at {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateB frame slotArr body = true) {k : Nat} {i : Linstr} (hi : body[k]? = some i)
    (hr : i.li_i ≠ .Lret) :
    k + 1 < body.length ∧ instrGateB frame slotArr body k i.li_i = true := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have hk1 : k + 1 < body.length := by
    by_contra hc
    have he : k = body.length - 1 := by omega
    obtain ⟨r, hr', hret⟩ := imgGateB_last h
    rw [List.getLast?_eq_getElem?, ← he, hi] at hr'
    cases hr'
    exact hr hret
  refine ⟨hk1, ?_⟩
  simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.1 k (by omega)
  rw [hi] at this
  simpa using this

theorem slotMov?_normA (x : LinstrR) : slotMov? (normA x) = slotMov? x := by
  cases x with
  | Lopn ds o ss =>
      simp only [normA]
      split_ifs with ho
      · subst ho
        have h1 : ∀ o', o' ≠ "MOVQ" → o' ≠ "MOV:64" → slotMov? (.Lopn ds o' ss) = none := by
          intro o' h1 h2
          unfold slotMov?
          split <;> simp_all
        rw [h1 _ (by decide +kernel) (by decide +kernel), h1 _ (by decide) (by decide)]
      · rfl
  | _ => rfl

/-- The register a save copies has no frame word. -/
theorem save_frame {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (h : imgGateB frame slotArr body = true)
    {k : Nat} {R : String} (hs : SaveAt body k R) {A : String} {n : Nat}
    (hA : slotArr (slotOfReg R) = some (A, n)) : frame R = none := by
  obtain ⟨i, hi, hm⟩ := hs
  have hnr : i.li_i ≠ .Lret := by
    intro e; rw [e] at hm; cases hm
  obtain ⟨-, hg⟩ := imgGateB_at h hi hnr
  obtain ⟨a, ha⟩ := hsep.slotFrame _ _ _ hA
  cases hR : frame R with
  | none => rfl
  | some a' =>
      exfalso
      rcases slotMov?_cases hm with hx | hx <;>
      · rw [hx] at hg
        simp [instrGateB, icase, slotMov?, ha, hR] at hg

theorem regGateB_slotMov {frame : String → Option (BitVec 64)} {x : LinstrR}
    (h : regGateB frame x = true) {d src : String} (hm : slotMov? x = some (d, src)) :
    frame d = none ∧ frame src = none := by
  simp only [regGateB, regOkB, Bool.and_eq_true] at h
  have h1 := h.1.1.1
  rw [hm] at h1
  simpa using h1

theorem getArr_congr {s s' : LstateM} (h : s.larr = s'.larr) (A : String) (w n : Nat) :
    s.getArr A w n = s'.getArr A w n := by
  unfold LstateM.getArr; rw [h]

theorem getW_congr {r r' : LstateN} {R : String} (h : r.lvm R = r'.lvm R) (w : Nat) :
    r.getW R w = r'.getW R w := by
  unfold LstateN.getW; rw [h]

/-! ## 9. One step of the image on the address machine -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (LoadSafeAt RunSafe labelAt_spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next)

/-- **A register instruction keeps the relation.** -/
theorem rel_reg {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64} {body : Lcmd}
    (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hc : icase frame bi.li_i = .reg)
    (hg : regGateB frame (normA bi.li_i) = true)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRel frame slotArr base body t sa' t.zf := by
  obtain ⟨ds, o, ss, hx, -, -⟩ := icase_reg hc
  have hl : IsLopn (normA bi.li_i, MemTag.reg none) := by
    rw [hx]; exact ⟨ds, _, ss, rfl⟩
  obtain ⟨sa', hst, hmem, hregs', hkeepF, hcf, hof, hlpcA, hlpcI, hlarr, hwid'⟩ :=
    reg_step hl hg P s t sa zf hrel.regs hrel.zf hrel.cf hrel.of hrel.wid hs
  have hmovF : ∀ d src, slotMov? bi.li_i = some (d, src) → frame d = none ∧ frame src = none :=
    fun d src hm => regGateB_slotMov hg (by rw [slotMov?_normA]; exact hm)
  refine ⟨sa', hst, ⟨?_, hregs', ?_, rfl, hcf, hof, hwid', ?_, ?_, ?_⟩⟩
  · rw [hlpcA, hlpcI, hrel.pc]
  · intro q a ha
    rw [hkeepF q (by rw [ha]; simp), hrel.slots q a ha, hmem]
  · intro q A n hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    exact ⟨arr, by rw [getArr_congr hlarr]; exact h1, fun j hj => by rw [hmem]; exact h2 j hj⟩
  · intro k R A n a hS hA ha
    rw [hlpcA]
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [hmem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (hrel.saved k R A n a hS hA ha).1 hk
      · exfalso
        obtain ⟨i', hi', hm'⟩ := hS
        rw [hb] at hi'
        cases hi'
        rw [(hmovF _ _ hm').1] at ha
        cases ha
    · have hR := save_frame hsep hgate hS hA
      obtain ⟨i', hi', hm'⟩ := hS
      have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
      obtain ⟨d, src, hm, hdR⟩ := entryRegB_spec hent (show sa.reg.lpc < k by omega) hb
      have ht := eval_slotMov P (by rw [slotMov?_normA]; exact hm) (MemTag.reg none) s
      rw [hs] at ht
      cases ht
      have e : sa'.reg.lvm R = sa.reg.lvm R := by
        rw [← hregs' R hR, ← hrel.regs R hR]
        simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, Ne.symm hdR]
      rw [getW_congr e]
      exact (hrel.saved k R A n a ⟨i', hi', hm'⟩ hA ha).2 (by omega)
  · intro b q a i hpc hbi hm hq hbf
    rw [hlpcA, Nat.add_sub_cancel, hb] at hbi
    cases hbi
    rw [(hmovF _ _ hm).2] at hq
    cases hq

theorem normA_of_slotMov {x : LinstrR} {d q : String} (h : slotMov? x = some (d, q)) :
    normA x = x := by
  rcases slotMov?_cases h with rfl | rfl <;> rfl

theorem slotOfReg_inj {R S : String} (h : slotOfReg R = slotOfReg S) : R = S := by
  simpa [slotOfReg] using h

/-- **A load of a frame word keeps the relation.** -/
theorem rel_sload {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d q : String} (hc : icase frame bi.li_i = .sload d q)
    (hgd : gpOk d = true)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRel frame slotArr base body t sa' t.zf := by
  obtain ⟨hm, hd, hq⟩ := icase_sload hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  rw [normA_of_slotMov hm] at hs ⊢
  rw [eval_slotMov P hm] at hs
  cases hs
  have hz := hrel.zf
  subst hz
  have hsq := hrel.slots q a ha
  refine ⟨{ sa with reg := (sa.reg.setReg d (read64 sa.mem a)).nextPc },
    fstepA_slotLoad frame hm ha sa _, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    by_cases e : r = d
    · subst e
      simp [LstateM.setReg, LstateM.nextPc, hsq]
    · simp [LstateM.setReg, LstateM.nextPc, e, hrel.regs r hr]
  · intro q' a' ha'
    have e : q' ≠ d := fun e => by rw [e, hd] at ha'; cases ha'
    simp [LstateM.setReg, LstateM.nextPc, e, hrel.slots q' a' ha']
  · intro r hr
    by_cases e : r = d
    · subst e; simp
    · simp [e, hrel.wid r hr]
  · intro q' A n hq'
    obtain ⟨arr, h1, h2⟩ := hrel.cells q' A n hq'
    exact ⟨arr, by simpa using h1, h2⟩
  · intro k R A n a' hS hA ha'
    simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg]
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (hrel.saved k R A n a' hS hA ha').1 hk
      · exfalso
        obtain ⟨i', hi', hm'⟩ := hS
        rw [hb] at hi'
        cases hi'
        rw [hm] at hm'
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hm')
        rw [hd] at ha'
        cases ha'
    · obtain ⟨i', hi', hm'⟩ := hS
      have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
      obtain ⟨d', src, hm2, hdR⟩ := entryRegB_spec hent (show sa.reg.lpc < k by omega) hb
      rw [hm] at hm2
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hm2)
      rw [getW_congr (r' := sa.reg) (by simp [Ne.symm hdR])]
      exact (hrel.saved k R A n a' ⟨i', hi', hm'⟩ hA ha').2 (by omega)
  · intro b q' a' i hpc hbi hm' hq' hbf
    simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, Nat.add_sub_cancel, hb] at hbi
    cases hbi
    rw [hm] at hm'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
    rw [ha] at hq'
    cases hq'
    simp

/-- **A store into a frame word keeps the relation.** -/
theorem rel_sstore {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {q S : String} (hc : icase frame bi.li_i = .sstore q S)
    (hgS : gpOk S = true)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRel frame slotArr base body t sa' t.zf := by
  obtain ⟨hm, hS, hq⟩ := icase_sstore hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  rw [normA_of_slotMov hm] at hs ⊢
  rw [eval_slotMov P hm] at hs
  cases hs
  have hz := hrel.zf
  subst hz
  have hw := hrel.wid S hgS
  have hv : sa.reg.getW S 64 = some (castW (sa.reg.lvm S) 64) := by rw [getW_eq, if_pos hw]
  have hSv : s.prog.base.reg.lvm S = ⟨64, castW (sa.reg.lvm S) 64⟩ := by
    rw [hrel.regs S hS, sigma_of_castW hw]
  refine ⟨{ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a (castW (sa.reg.lvm S) 64) },
    fstepA_slotStore frame hm hS ha sa _ hv, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    have e : r ≠ q := fun e => by rw [e, ha] at hr; cases hr
    simp [LstateM.setReg, LstateM.nextPc, e, hrel.regs r hr]
  · intro q' a' ha'
    by_cases e : q' = q
    · subst e
      rw [ha] at ha'
      cases ha'
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, if_true,
        read64_write64_same]
      rw [hSv]
    · simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
        if_false]
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' ha ha' (Ne.symm e))]
      exact hrel.slots q' a' ha'
  · intro r hr
    simpa using hrel.wid r hr
  · intro q' A n hq'
    obtain ⟨arr, h1, h2⟩ := hrel.cells q' A n hq'
    refine ⟨arr, by simpa using h1, fun j hj => ?_⟩
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q' A n j hq' hj q a ha).symm]
    exact h2 j hj
  · intro k R A n a' hS' hA ha'
    simp only [LstateN.lpc_nextPc]
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · by_cases hqR : slotOfReg R = q
      · subst hqR
        rw [ha] at ha'
        cases ha'
        rw [read64_write64_same]
        obtain ⟨hqS, -⟩ := physImgB_slotStore hphys hb hm (by rw [hA]; rfl)
        have hRS := slotOfReg_inj hqS
        subst hRS
        have := (hrel.saved sa.reg.lpc R A n a ⟨bi, hb, hm⟩ hA ha).2 (le_refl _)
        rw [hv] at this
        exact Option.some.inj this
      · rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q _ a a' ha ha' (Ne.symm hqR))]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact (hrel.saved k R A n a' hS' hA ha').1 hk
        · exfalso
          obtain ⟨i', hi', hm'⟩ := hS'
          rw [hb] at hi'
          cases hi'
          rw [hm] at hm'
          exact hqR (Prod.mk.inj (Option.some.inj hm')).1.symm
    · rw [getW_congr (r := sa.reg.nextPc) (r' := sa.reg) rfl]
      exact (hrel.saved k R A n a' hS' hA ha').2 (by omega)
  · intro b q' a' i hpc hbi hm' hq' hbf
    simp only [LstateN.lpc_nextPc, Nat.add_sub_cancel, hb] at hbi
    cases hbi
    rw [hm] at hm'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
    rw [ha] at hbf
    cases hbf

/-- A step that only advances the program counter, at an instruction that is no move,
    keeps the save and reload components of the relation. -/
theorem saved_reload_next {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa sa' : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hnm : slotMov? bi.li_i = none)
    (hpc : sa'.reg.lpc = sa.reg.lpc + 1)
    (hmem : ∀ q a, frame q = some a → read64 sa'.mem a = read64 sa.mem a) :
    (∀ k R A n a, SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
      frame (slotOfReg R) = some a →
        (k < sa'.reg.lpc → read64 sa'.mem a = base A)
          ∧ (sa'.reg.lpc ≤ k → sa'.reg.getW R 64 = some (base A)))
    ∧ (∀ b q a i, 1 ≤ sa'.reg.lpc → body[sa'.reg.lpc - 1]? = some i →
      slotMov? i.li_i = some (b, q) → frame q = some a → frame b = none →
        sa'.reg.lvm b = ⟨64, read64 sa'.mem a⟩) := by
  refine ⟨fun k R A n a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩, fun b q a i _ hbi hm _ _ => ?_⟩
  · rw [hmem _ a ha]
    rw [hpc] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact (hrel.saved k R A n a hS hA ha).1 hk
    · exfalso
      obtain ⟨i', hi', hm'⟩ := hS
      rw [hb] at hi'
      cases hi'
      rw [hnm] at hm'
      cases hm'
  · exfalso
    obtain ⟨i', hi', hm'⟩ := hS
    have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
    obtain ⟨d, src, hm2, -⟩ := entryRegB_spec hent (show sa.reg.lpc < k by omega) hb
    rw [hnm] at hm2
    cases hm2
  · rw [hpc, Nat.add_sub_cancel, hb] at hbi
    cases hbi
    rw [hnm] at hm
    cases hm

/-- **A compare against a frame word keeps the relation.** -/
theorem rel_scmp {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d y q : String} (hc : icase frame bi.li_i = .scmp d y q)
    (hy : frame y = none)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRel frame slotArr base body t sa' t.zf := by
  obtain ⟨hk, hq⟩ := icase_scmp hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  have hx := slotCmp?_eq hk
  have hn : normA bi.li_i = bi.li_i := by rw [hx]; rfl
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  rw [hn] at hs ⊢
  rw [eval_slotCmp P hk] at hs
  have hqv : s.prog.base.reg.getW q 64 = some (read64 sa.mem a) := by
    rw [getW_eq, hrel.slots q a ha]; simp [castW]
  rw [hqv, getW_congr (hrel.regs y hy)] at hs
  rw [fstepA_slotCmp frame hk ha]
  cases hva : sa.reg.getW y 64 with
  | none => rw [hva] at hs; cases hs
  | some va =>
    rw [hva] at hs
    cases hs
    obtain ⟨hsv, hrl⟩ := saved_reload_next (sa' := { sa with reg := sa.reg.nextPc }) hphys hrel
      hb hnm rfl (fun _ _ _ => rfl)
    exact ⟨_, rfl, ⟨by simp [LstateM.nextPc, hrel.pc],
      fun r hr => by simpa [LstateM.nextPc] using hrel.regs r hr,
      fun q' a' ha' => by simpa [LstateM.nextPc] using hrel.slots q' a' ha', rfl, hrel.cf,
      hrel.of, fun r hr => by simpa using hrel.wid r hr,
      fun q' A n hq' => by simpa using hrel.cells q' A n hq', hsv, hrl⟩⟩

/-- At an indexed access whose pointer register was reloaded from the frame word of an
    array, the pointer register holds the base of the array. -/
theorem ptr_of_reload {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateB frame slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {b A : String} {n : Nat}
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n)) (hbf : frame b = none) :
    ∃ q, slotArr q = some (A, n) ∧ sa.reg.getW b 64 = some (base A) := by
  obtain ⟨k', hk', i, q, hi, hm, hq⟩ := accArr_spec hacc
  obtain ⟨a, ha⟩ := hsep.slotFrame q A n hq
  have hrl := hrel.reload b q a i (by omega) (by rw [hk', Nat.add_sub_cancel]; exact hi) hm ha hbf
  have hrs : reloadSavedB slotArr body = true := by
    simp only [imgGateB, Bool.and_eq_true] at hgate; exact hgate.2
  obtain ⟨j, R, hj, hS, hqR⟩ := reloadSavedB_spec hrs hi hm (by rw [hq]; rfl)
  subst hqR
  have hp := (hrel.saved j R A n a hS hq ha).1 (by omega)
  refine ⟨slotOfReg R, hq, ?_⟩
  rw [getW_eq, hrl]
  simp [castW, hp]

theorem imgInstr_ldx (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {d b idx A : String} {n : Nat} (h : accArr slotArr body k b = some (A, n)) :
    imgInstr slotArr body k (.Lopn [.reg d] "LOADIDX" [.arrIdx b idx 8])
      = (.Lopn [.reg d] "LOADIDX" [.arrIdx A idx 8], .load 64 n) := by
  simp [imgInstr, h]

theorem imgInstr_stx (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {d b idx v A : String} {n : Nat} (h : accArr slotArr body k b = some (A, n)) :
    imgInstr slotArr body k (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v])
      = (.Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v], .store 64 n) := by
  simp [imgInstr, h]

/-- **An indexed load keeps the relation**, and reads outside the red-zone word. -/
theorem rel_ldx {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64} {body : Lcmd}
    (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d b idx A : String} {n : Nat}
    (hx : bi.li_i = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx 8])
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n)) (hgd : gpOk d = true)
    (hd : frame d = none) (hidx : frame idx = none) (hbf : frame b = none)
    (hs : evalInstrPMemFk true P (.Lopn [.reg d] "LOADIDX" [.arrIdx A idx 8], .load 64 n) s
      = some t) :
    LoadSafeAt rsp body sa ∧ ∃ sa', fstepA frame (bi.li_i, .load 64 0) sa zf = some (sa', t.zf)
      ∧ ImgRel frame slotArr base body t sa' t.zf := by
  have hok := idxOkB_of_checked hs
  have hs' := evalInstrPMemF_of_k hs
  obtain ⟨q, hq, hp⟩ := ptr_of_reload hsep hgate hrel hacc hbf
  obtain ⟨arr, harr, hcell⟩ := hrel.cells q A n hq
  rw [eval_loadIdx, harr] at hs'
  have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regs idx hidx) 64
  cases hvi : sa.reg.getW idx 64 with
  | none => rw [hidxe, hvi] at hs'; cases hs'
  | some vi =>
  rw [hidxe, hvi] at hs'
  cases hs'
  have hlt : vi.toNat < n := by
    simp only [idxOkB, loadStruct?, if_true, idxBelowB, hidxe, hvi] at hok
    simpa using hok
  have hz := hrel.zf
  subst hz
  have hval : read64 sa.mem (cellAt (base A) vi.toNat) = stackGet arr vi.toNat := by
    rw [hcell vi.toNat hlt]
    exact (stackGet_id arr ⟨vi.toNat, hlt⟩).symm
  refine ⟨?_, ?_⟩
  · intro ii D B I hbI p v hp' hv'
    rw [hb] at hbI
    have e := Option.some.inj hbI
    subst e
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
      LOperand.arrIdx.injEq, and_true] at hx
    obtain ⟨-, -, rfl, rfl⟩ := hx
    rw [hp] at hp'
    cases hp'
    rw [hvi] at hv'
    cases hv'
    exact hsep.red q A n vi.toNat hq hlt
  rw [hx, fstepA_loadIdx, hp, hvi]
  simp only
  obtain ⟨hsv, hrl⟩ := saved_reload_next (sa' := { sa with reg := (sa.reg.setReg d
      (read64 sa.mem (base A + BitVec.ofNat 64 (8 * vi.toNat)))).nextPc })
    hphys hrel hb (by rw [hx]; rfl) (by simp) (fun _ _ _ => rfl)
  refine ⟨_, rfl, ⟨by simp [LstateM.setReg, LstateM.nextPc, hrel.pc], ?_, ?_, rfl, hrel.cf,
    hrel.of, ?_, fun q' A' n' hq' => by simpa using hrel.cells q' A' n' hq', hsv, hrl⟩⟩
  · intro r hr
    by_cases e : r = d
    · subst e
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg,
        if_true]
      rw [← hval]
    · simp [LstateM.setReg, LstateM.nextPc, e, hrel.regs r hr]
  · intro q' a' ha'
    have e : q' ≠ d := fun e => by rw [e, hd] at ha'; cases ha'
    simp [LstateM.setReg, LstateM.nextPc, e, hrel.slots q' a' ha']
  · intro r hr
    by_cases e : r = d
    · subst e; simp
    · simp [e, hrel.wid r hr]

/-- **An indexed store keeps the relation.** -/
theorem rel_stx {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64} {body : Lcmd}
    (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d b idx v A : String} {n : Nat}
    (hx : bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v])
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n))
    (hidx : frame idx = none) (hbf : frame b = none) (hv : frame v = none)
    (hs : evalInstrPMemFk true P
      (.Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v], .store 64 n) s = some t) :
    ∃ sa', fstepA frame (bi.li_i, .store 64 0) sa zf = some (sa', t.zf)
      ∧ ImgRel frame slotArr base body t sa' t.zf := by
  have hok := idxOkB_of_checked hs
  have hs' := evalInstrPMemF_of_k hs
  obtain ⟨q, hq, hp⟩ := ptr_of_reload hsep hgate hrel hacc hbf
  obtain ⟨arr, harr, hcell⟩ := hrel.cells q A n hq
  rw [eval_storeIdx, harr] at hs'
  have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regs idx hidx) 64
  have hve := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regs v hv) 64
  cases hvi : sa.reg.getW idx 64 with
  | none => rw [hidxe, hvi] at hs'; cases hs'
  | some vi =>
  cases hvv : sa.reg.getW v 64 with
  | none => rw [hidxe, hvi, hve, hvv] at hs'; cases hs'
  | some vv =>
  rw [hidxe, hvi, hve, hvv] at hs'
  cases hs'
  have hlt : vi.toNat < n := by
    simp only [idxOkB, storeStruct?, if_true, idxBelowB, hidxe, hvi] at hok
    simpa using hok
  have hz := hrel.zf
  subst hz
  rw [hx, fstepA_storeIdx, hp, hvi, hvv]
  simp only
  obtain ⟨hsv, hrl⟩ := saved_reload_next (sa' := { sa with
      reg := sa.reg.nextPc
      mem := write64 sa.mem (base A + BitVec.ofNat 64 (8 * vi.toNat)) vv })
    hphys hrel hb (by rw [hx]; rfl) rfl
    (fun q' a ha => read64_write64_of_disjoint _ _ _ _
      (hsep.cellFrame q A n vi.toNat hq hlt q' a ha))
  refine ⟨_, rfl, ⟨by simp [LstateM.setArr, LstateM.nextPc, hrel.pc],
    fun r hr => by simpa [LstateM.setArr, LstateM.nextPc] using hrel.regs r hr, ?_, rfl,
    hrel.cf, hrel.of, fun r hr => by simpa using hrel.wid r hr, ?_, hsv, hrl⟩⟩
  · intro q' a ha
    simp only [LstateM.setArr, LstateM.nextPc, LstateN.lvm_nextPc]
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q A n vi.toNat hq hlt q' a ha)]
    exact hrel.slots q' a ha
  · intro q' A' n' hq'
    obtain ⟨arr', harr', hcell'⟩ := hrel.cells q' A' n' hq'
    by_cases eA : A' = A
    · subst eA
      have hn := hsep.len q' q A' n' n hq' hq
      subst hn
      refine ⟨stackSet arr vi.toNat vv, by simp, fun j hj => ?_⟩
      rw [← stackGet_id (stackSet arr vi.toNat vv) ⟨j, hj⟩]
      by_cases ej : j = vi.toNat
      · subst ej
        rw [read64_write64_same, stackGet_stackSet_same _ _ _ hlt]
      · rw [read64_write64_of_disjoint _ _ _ _
          (hsep.cells q A' n' q A' n' vi.toNat j hq hq hlt hj (Or.inr (Ne.symm ej))),
          stackGet_stackSet_ne _ _ _ _ hlt hj ej, hcell j hj, stackGet_id arr ⟨j, hj⟩]
    · refine ⟨arr', by simpa [eA] using harr', fun j hj => ?_⟩
      rw [read64_write64_of_disjoint _ _ _ _
        (hsep.cells q A n q' A' n' vi.toNat j hq hq' hlt hj (Or.inl (Ne.symm eA)))]
      exact hcell' j hj

/-- A move of the program counters keeps the relation, given its save and reload
    components at the new counters. -/
theorem rel_pc {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {body : Lcmd} {s t : LstateMF} {sa sa' : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf)
    (hlvm : t.prog.base.reg.lvm = s.prog.base.reg.lvm) (hlarr : t.prog.base.larr = s.prog.base.larr)
    (hz : t.zf = s.zf) (hc : t.prog.base.cf = s.prog.base.cf)
    (ho : t.prog.base.of = s.prog.base.of) (hreg : sa'.reg.lvm = sa.reg.lvm)
    (hmem : sa'.mem = sa.mem) (hc' : sa'.cf = sa.cf) (ho' : sa'.of = sa.of)
    (hpc : sa'.reg.lpc = t.prog.base.reg.lpc)
    (hsv : ∀ k R A n a, SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
      frame (slotOfReg R) = some a →
        (k < sa'.reg.lpc → read64 sa'.mem a = base A)
          ∧ (sa'.reg.lpc ≤ k → sa'.reg.getW R 64 = some (base A)))
    (hrl : ∀ b q a i, 1 ≤ sa'.reg.lpc → body[sa'.reg.lpc - 1]? = some i →
      slotMov? i.li_i = some (b, q) → frame q = some a → frame b = none →
        sa'.reg.lvm b = ⟨64, read64 sa'.mem a⟩) :
    ImgRel frame slotArr base body t sa' zf := by
  refine ⟨hpc, fun r hr => ?_, fun q a ha => ?_, by rw [hz, hrel.zf], by rw [hc', hc, hrel.cf],
    by rw [ho', ho, hrel.of], fun r hr => ?_, fun q A n hq => ?_, hsv, hrl⟩
  · rw [hlvm, hreg]; exact hrel.regs r hr
  · rw [hlvm, hmem]; exact hrel.slots q a ha
  · rw [hreg]; exact hrel.wid r hr
  · obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    exact ⟨arr, by rw [getArr_congr hlarr]; exact h1, fun j hj => by rw [hmem]; exact h2 j hj⟩

/-- **A label keeps the relation.** -/
theorem rel_label {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hnm : slotMov? bi.li_i = none) :
    ImgRel frame slotArr base body
      { s with prog := { s.prog with base := s.prog.base.nextPc } }
      (sa.setLpc (sa.reg.lpc + 1)) zf := by
  obtain ⟨hsv, hrl⟩ := saved_reload_next (sa' := sa.setLpc (sa.reg.lpc + 1)) hphys hrel hb
    hnm rfl (fun _ _ _ => rfl)
  exact rel_pc hrel rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [LstateA.setLpc, LstateM.nextPc, hrel.pc]) hsv hrl

/-- **A branch taken keeps the relation**: the image jumps one past the label, the address
    machine to the label and then over it. -/
theorem rel_jump {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hnm : slotMov? bi.li_i = none) {p : Nat}
    {bp : Linstr} (hbp : body[p]? = some bp) (hpl : slotMov? bp.li_i = none) :
    ImgRel frame slotArr base body
      { s with prog := { s.prog with base := s.prog.base.setLpc (p + 1) } }
      (sa.setLpc (p + 1)) zf := by
  refine rel_pc hrel rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun k R A n a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩) (fun b q a i _ hbi hm _ _ => ?_)
  · have hk' : k < sa.reg.lpc := by
      by_contra hc
      obtain ⟨i', hi', hm'⟩ := hS
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hc) with hlt | heq
      · have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
        obtain ⟨d, src, hm2, -⟩ := entryRegB_spec hent hlt hb
        rw [hnm] at hm2; cases hm2
      · rw [← heq, hb] at hi'
        cases hi'
        rw [hnm] at hm'; cases hm'
    exact (hrel.saved k R A n a hS hA ha).1 hk'
  · show sa.reg.getW R 64 = some (base A)
    by_cases hk' : sa.reg.lpc ≤ k
    · exact (hrel.saved k R A n a hS hA ha).2 hk'
    · exfalso
      obtain ⟨i', hi', hm'⟩ := hS
      have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
      have hpk : p < k := by
        simp only [LstateA.setLpc] at hk
        omega
      obtain ⟨d, src, hm2, -⟩ := entryRegB_spec hent hpk hbp
      rw [hpl] at hm2; cases hm2
  · simp only [LstateA.setLpc, Nat.add_sub_cancel] at hbi
    rw [hbp] at hbi
    cases hbi
    rw [hpl] at hm; cases hm

/-! ## 10. The dispatch over the kinds of instruction -/

theorem imgInstr_reg (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {ds : List LOperand} {o : String} {ss : List LOperand} (h1 : o ≠ "LOADIDX")
    (h2 : o ≠ "STOREIDX") :
    imgInstr slotArr body k (.Lopn ds o ss) = (normA (.Lopn ds o ss), .reg none) := by
  unfold imgInstr
  split <;> simp_all

theorem tagA_reg {ds : List LOperand} {o : String} {ss : List LOperand} (h1 : o ≠ "LOADIDX")
    (h2 : o ≠ "STOREIDX") : tagA (.Lopn ds o ss) = .reg none := by
  simp [tagA, h1, h2]

theorem stepA_lopn (frame : String → Option (BitVec 64)) {body : Lcmd} {sa : LstateA}
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ds : List LOperand} {o : String}
    {ss : List LOperand} (hx : bi.li_i = .Lopn ds o ss) (zf : Bool) :
    stepA frame body sa zf = fstepA frame (normA bi.li_i, tagA bi.li_i) sa zf := by
  obtain ⟨ii, li⟩ := bi
  simp only at hx
  subst hx
  simp [stepA, hb]

theorem haltedA_of {body : Lcmd} {sa : LstateA} {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hr : bi.li_i ≠ .Lret) : haltedA body sa = false := by
  obtain ⟨ii, li⟩ := bi
  simp only at hr
  unfold haltedA
  rw [hb]
  cases li <;> simp_all

theorem loadSafe_of {rsp : BitVec 64} {body : Lcmd} {sa : LstateA} {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi)
    (hn : ∀ D B I, bi.li_i ≠ .Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) :
    LoadSafeAt rsp body sa := by
  intro ii D B I hbI
  rw [hb] at hbI
  cases Option.some.inj hbI
  exact absurd rfl (hn D B I)

theorem icase_loadIdx {frame : String → Option (BitVec 64)} {D B I : String} :
    icase frame (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) = .ldx D B I := by
  simp [icase]

theorem evalInstrPMemFk_reg (P : LprogM) (x : LinstrR) (s : LstateMF) :
    evalInstrPMemFk true P (x, .reg none) s = evalInstrPMemF P (x, .reg none) s := by
  simp [evalInstrPMemFk, idxOkB]

theorem notLoad_of_icase {frame : String → Option (BitVec 64)} {x : LinstrR}
    (h : ∀ d b idx, icase frame x ≠ .ldx d b idx) :
    ∀ D B I, x ≠ .Lopn [.reg D] "LOADIDX" [.arrIdx B I 8] := by
  intro D B I e
  subst e
  exact h D B I icase_loadIdx

/-- **One step of the image.** From related states, a checked step of the image of a body
    that passes the gate is matched by one step of the address machine, or by two when the
    image takes a branch (the address machine stops at the label); the address machine does
    not halt and reads outside the red-zone word at each state it steps from. -/
theorem img_step {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (fn : String) {s t : LstateMF}
    (hfn : s.prog.lfn = fn) {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {i : LinstrRM}
    (hfetch : findInstrMem (singletonProgM fn (virtImg slotArr body)) s.prog = some i)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr body)) i s = some t) :
    haltedA body sa = false ∧ LoadSafeAt rsp body sa ∧ t.prog.lfn = fn ∧
      ∃ sa1 z1, stepA frame body sa zf = some (sa1, z1) ∧
        (ImgRel frame slotArr base body t sa1 z1 ∨
          (haltedA body sa1 = false ∧ LoadSafeAt rsp body sa1 ∧
            ∃ sa2 z2, stepA frame body sa1 z1 = some (sa2, z2)
              ∧ ImgRel frame slotArr base body t sa2 z2)) := by
  set P := singletonProgM fn (virtImg slotArr body)
  have hlfn : t.prog.lfn = fn :=
    (evalInstrPMemF_next P i s t (evalInstrPMemF_of_k hstep)).1.trans hfn
  rw [findInstrMem_single hfn, virtImg_getElem?, ← hrel.pc, List.getElem?_dropLast] at hfetch
  split at hfetch
  case isFalse => cases hfetch
  rename_i hlt
  obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hfetch
  have hg : instrGateB frame slotArr body sa.reg.lpc bi.li_i = true := by
    simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  have hz := hrel.zf
  subst hz
  unfold instrGateB at hg
  cases hc : icase frame bi.li_i with
  | other => rw [hc] at hg; cases hg
  | label =>
      obtain ⟨ii, l, hx⟩ := icase_label hc
      have hi : imgInstr slotArr body sa.reg.lpc bi.li_i = (bi.li_i, .reg none) := by
        rw [hx]; rfl
      rw [hi, evalInstrPMemFk_reg, hx, eval_label] at hstep
      cases hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), hlfn,
        sa.setLpc (sa.reg.lpc + 1), s.zf, ?_, Or.inl (rel_label hphys hrel hb (by rw [hx]; rfl))⟩
      obtain ⟨ii0, li⟩ := bi
      simp only at hx
      subst hx
      simp [stepA, hb]
  | cond cc l =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hg
      obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hg
      have hx := icase_cond hc
      have hi : imgInstr slotArr body sa.reg.lpc bi.li_i = (bi.li_i, .reg none) := by
        rw [hx]; rfl
      obtain ⟨r, hr, hret⟩ := imgGateB_last hgate
      have hfl := findLabel_virtImg slotArr body l (fun r' hr' => by
        rw [hr] at hr'
        cases hr'
        rw [hret]; rfl)
      rw [hp] at hfl
      rw [hi, evalInstrPMemFk_reg, hx, eval_cond fn _ cc l _ hpol hfl] at hstep
      have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
      obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
      have hbp : body[p]? = some body[p] := List.getElem?_eq_getElem hpl
      have hlabp : ∃ ii', body[p].li_i = .Llabel ii' l := by
        revert hlab
        cases body[p].li_i <;> simp [isLabelB]
      obtain ⟨ii', hli⟩ := hlabp
      have hstepA : stepA frame body sa s.zf = if s.zf = pol then some (sa.setLpc p, s.zf)
          else some (sa.setLpc (sa.reg.lpc + 1), s.zf) := by
        obtain ⟨ii0, li⟩ := bi
        simp only at hx
        subst hx
        simp only [stepA, hb, hpol, hp, Option.map_some]
      refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), hlfn, ?_⟩
      by_cases hzp : s.zf = pol
      · rw [if_pos hzp] at hstep hstepA
        cases hstep
        refine ⟨_, _, hstepA, Or.inr ⟨haltedA_of (bi := body[p]) (by simp [LstateA.setLpc])
          (by rw [hli]; simp), loadSafe_of (bi := body[p]) (by simp [LstateA.setLpc])
          (by rw [hli]; simp), sa.setLpc (p + 1), s.zf,
          ?_, rel_jump hphys hrel hb hnm hbp (by rw [hli]; rfl)⟩⟩
        have hb' : body[p]? = some body[p] := hbp
        generalize body[p] = bp at hli hb'
        obtain ⟨ii1, li1⟩ := bp
        simp only at hli
        subst hli
        simp [stepA, LstateA.setLpc, hb']
      · rw [if_neg hzp] at hstep hstepA
        cases hstep
        exact ⟨_, _, hstepA, Or.inl (rel_label hphys hrel hb hnm)⟩
  | ldx d b idx =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
      obtain ⟨⟨⟨⟨⟨An, hacc⟩, hgd⟩, hd⟩, hidx⟩, hbf⟩ := hg
      obtain ⟨A, n⟩ := An
      have hx := icase_ldx hc
      rw [hx, imgInstr_ldx slotArr body _ hacc] at hstep
      obtain ⟨hsafe, sa', hst, hr⟩ :=
        rel_ldx hsep hphys hgate P hrel hb hx hacc hgd hd hidx hbf hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, hlfn, sa', t.zf, ?_, Or.inl hr⟩
      rw [stepA_lopn frame hb hx, ← hst, hx]
      rfl
  | stx d b idx v =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
      obtain ⟨⟨⟨⟨An, hacc⟩, hidx⟩, hbf⟩, hv⟩ := hg
      obtain ⟨A, n⟩ := An
      have hx := icase_stx hc
      rw [hx, imgInstr_stx slotArr body _ hacc] at hstep
      obtain ⟨sa', hst, hr⟩ := rel_stx hsep hphys hgate P hrel hb hx hacc hidx hbf hv hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), hlfn, sa',
        t.zf, ?_, Or.inl hr⟩
      rw [stepA_lopn frame hb hx, ← hst, hx]
      rfl
  | sload d q =>
      rw [hc] at hg
      have hm := (icase_sload hc).1
      have hsafe := loadSafe_of (rsp := rsp) hb
        (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
      rcases slotMov?_cases hm with hx | hx <;>
      · rw [hx, imgInstr_reg slotArr body _ (by decide) (by decide), evalInstrPMemFk_reg,
          ← hx] at hstep
        obtain ⟨sa', hst, hr⟩ := rel_sload hphys P hrel hb hc hg hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, hlfn, sa', t.zf, ?_, Or.inl hr⟩
        rw [stepA_lopn frame hb hx, ← hst, hx, tagA_reg (by decide) (by decide)]
  | sstore q S =>
      rw [hc] at hg
      have hm := (icase_sstore hc).1
      have hsafe := loadSafe_of (rsp := rsp) hb
        (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
      rcases slotMov?_cases hm with hx | hx <;>
      · rw [hx, imgInstr_reg slotArr body _ (by decide) (by decide), evalInstrPMemFk_reg,
          ← hx] at hstep
        obtain ⟨sa', hst, hr⟩ := rel_sstore hsep hphys P hrel hb hc hg hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, hlfn, sa', t.zf, ?_, Or.inl hr⟩
        rw [stepA_lopn frame hb hx, ← hst, hx, tagA_reg (by decide) (by decide)]
  | scmp d y q =>
      rw [hc] at hg
      have hx := slotCmp?_eq (icase_scmp hc).1
      have hsafe := loadSafe_of (rsp := rsp) hb
        (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
      rw [hx, imgInstr_reg slotArr body _ (by decide) (by decide), evalInstrPMemFk_reg,
        ← hx] at hstep
      obtain ⟨sa', hst, hr⟩ := rel_scmp hphys P hrel hb hc (by simpa using hg) hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, hlfn, sa', t.zf, ?_, Or.inl hr⟩
      rw [stepA_lopn frame hb hx, ← hst, hx, tagA_reg (by decide) (by decide)]
  | reg =>
      rw [hc] at hg
      obtain ⟨ds, o, ss, hx, ho1, ho2⟩ := icase_reg hc
      have hsafe := loadSafe_of (rsp := rsp) hb
        (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
      rw [hx, imgInstr_reg slotArr body _ ho1 ho2, evalInstrPMemFk_reg, ← hx] at hstep
      obtain ⟨sa', hst, hr⟩ := rel_reg hsep hphys hgate P hrel hb hc hg hstep
      refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, hlfn, sa', t.zf, ?_, Or.inl hr⟩
      rw [stepA_lopn frame hb hx, ← hst, hx, tagA_reg ho1 ho2]

/-- Where the image halts, the address machine has halted: the program counter is at the
    final return of the body or past its end. -/
theorem haltedA_of_img {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hgate : imgGateB frame slotArr body = true) (fn : String) {s : LstateMF}
    (hfn : s.prog.lfn = fn) {sa : LstateA} (hpc : sa.reg.lpc = s.prog.base.reg.lpc)
    (h : findInstrMem (singletonProgM fn (virtImg slotArr body)) s.prog = none) :
    haltedA body sa = true := by
  rw [findInstrMem_single hfn, virtImg_getElem?, ← hpc, List.getElem?_dropLast] at h
  have hge : ¬ sa.reg.lpc < body.length - 1 := by
    intro hlt
    rw [if_pos hlt] at h
    have hl : sa.reg.lpc < body.length := by omega
    rw [List.getElem?_eq_getElem hl] at h
    cases h
  unfold haltedA
  by_cases hl : sa.reg.lpc < body.length
  · obtain ⟨r, hr, hret⟩ := imgGateB_last hgate
    have he : sa.reg.lpc = body.length - 1 := by omega
    rw [List.getLast?_eq_getElem?, ← he] at hr
    rw [hr]
    obtain ⟨ii, li⟩ := r
    simp only at hret
    subst hret
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-- **The image simulated by the address machine.** For a printed body that passes the gate
    `imgGateB` and the class `physImgB`, at a separation `ImgSep`, every halting checked run
    of the name-keyed machine on the image `virtImg` from a state related to an address
    state is matched by a halting run of the address machine on the body from that state,
    whose final state is related to the final state of the image, and whose indexed loads
    read outside the red-zone word. -/
theorem image_addr_sim {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (fn : String) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base body s sa zf →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) fuel s = some t →
      ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
        ∧ ImgRel frame slotArr base body t sa' zf'
        ∧ RunSafe frame body (LoadSafeAt rsp body) fuel' sa zf := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hfn hrel hrun
      cases hf : findInstrMem (singletonProgM fn (virtImg slotArr body)) s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact ⟨0, sa, zf, runA_halt frame body 0 sa zf
            (haltedA_of_img hgate fn hfn hrel.pc hf), hrel, trivial⟩
  | succ f ih =>
      intro s t sa zf hfn hrel hrun
      cases hf : findInstrMem (singletonProgM fn (virtImg slotArr body)) s.prog with
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact ⟨0, sa, zf, runA_halt frame body 0 sa zf
            (haltedA_of_img hgate fn hfn hrel.pc hf), hrel, trivial⟩
      | some i =>
          simp only [lsemFuelMemFk, hf] at hrun
          cases he : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr body)) i s with
          | none => rw [he] at hrun; cases hrun
          | some s1 =>
              rw [he] at hrun
              obtain ⟨hh, hsafe, hfn1, sa1, z1, hst1, hcase⟩ :=
                img_step hsep hphys hgate fn hfn hrel hf he
              rcases hcase with hrel1 | ⟨hh1, hsafe1, sa2, z2, hst2, hrel2⟩
              · obtain ⟨f', sa', zf', hr', hrel', hsafe'⟩ := ih s1 t sa1 z1 hfn1 hrel1 hrun
                refine ⟨f' + 1, sa', zf', ?_, hrel', hsafe, fun s' zf'' hs' => ?_⟩
                · rw [runA_step frame body f' sa zf hh, hst1]
                  exact hr'
                · rw [hst1] at hs'
                  cases hs'
                  exact hsafe'
              · obtain ⟨f', sa', zf', hr', hrel', hsafe'⟩ := ih s1 t sa2 z2 hfn1 hrel2 hrun
                refine ⟨f' + 2, sa', zf', ?_, hrel', hsafe, fun s' zf'' hs' => ?_⟩
                · rw [runA_step frame body (f' + 1) sa zf hh, hst1]
                  simp only [Option.bind_some]
                  rw [runA_step frame body f' sa1 z1 hh1, hst2]
                  exact hr'
                · rw [hst1] at hs'
                  cases hs'
                  refine ⟨hsafe1, fun s'' z'' hs'' => ?_⟩
                  rw [hst2] at hs''
                  cases hs''
                  exact hsafe'

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
