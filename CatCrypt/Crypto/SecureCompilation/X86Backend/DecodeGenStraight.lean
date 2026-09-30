/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

@[expose] public section

set_option autoImplicit false

/-!
# A checked straight-line body from the System V entry

`DecodeGenNode.decNodeAbi_result` relates the decoded bytes of a single-loop node to its
flag-machine run. This module states the same for a straight-line body: a chain of
flag-machine instructions `ops` with no loop, against a decoded function that is one machine
block followed by `ret` (`lineLayout`).

## The check

The machine block is split into a prologue, a middle and an epilogue (`LineWit`). The
prologue is run symbolically by `DecodeGenNode.prun` (`preLine`): every live name at the
start of the chain and the machine register of it hold the entry value of the name's System
V register, and the frame slot of every region holds the entry value of the region's
register. The middle is checked against `ops` by `DecodeGenMem.mbodyOK`, ending with the
return name live. The epilogue is run symbolically from the state after the middle
(`postLine`): the result register of the layout holds the value the machine register of the
return name holds before it. `lineCheck` collects these conditions.

## Main results

* `decodeLprog_line_gen`: the function bytes of a straight-line body with computed shapes
  decode to `lineLayout` over the frame `lea`, the decoded body and the closing `lea`.
* `decSim_preLine`: an accepted prologue simulates the empty chain from the entry
  correspondence `NodeEntry` to `MCorr` with no machine facts.
* `postLine_sound`: an accepted epilogue moves the value of one register to the result
  register.
* `lineCheck`: the Boolean check of a straight-line body against a witness `LineWit`.
* `decLine_result`: for a body that passes `lineCheck` and bytes that decode to its layout,
  every halting flag-machine run of `ops` from a System V entry state whose return name holds
  `x` is matched by a halting machine run whose result read-back is `x`.
* `decLine_entry`: the same from an entry map, in the shape of the straight-line decode leg
  of the general compiler theorem.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenStraight

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (dispOk32)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (lsemFuelMemF_det)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout ResultKind)

/-! ## 1. The decoded layout -/

/-- The decoded layout of a straight-line function: the machine block `js` and `ret`. -/
def lineLayout (js : List (JInstr 64)) : List RInstr := js.map .op ++ [.ret]

/-- **The decoded bytes of a straight-line body, over computed shapes.** A body that saves
    no register by `push`, with a non-zero frame in `rel32` range, laid out as a
    straight-line segment `P1` with computed straight-line shapes followed by the return,
    whose branches are well formed, decodes to the frame `lea`, the decoded instructions of
    `P1`, the closing `lea` and `ret`. -/
theorem decodeLprog_line_gen (body P1 : Lcmd) (r : Linstr) (hbody : body = P1 ++ [r])
    (h1 : straightOK (Params.ofBody body) P1 = true) (hr : r.li_i = .Lret)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : (Int.ofNat (Params.ofBody body).frame) ≠ 0)
    (hF : dispOk32 (Int.ofNat (Params.ofBody body).frame) = true)
    (hF' : dispOk32 (-(Int.ofNat (Params.ofBody body).frame)) = true)
    (hbr : branchOK (fundefItemsL body (shapesD (Params.ofBody body) P1 ++ [.one .skip])) 0
      (fundefItemsL body (shapesD (Params.ofBody body) P1 ++ [.one .skip])) = true) :
    decodeLprog (encodeLfundefBytes body)
      = some (lineLayout
          (leaFrame (-(Int.ofNat (Params.ofBody body).frame)) :: opsD (Params.ofBody body) P1
            ++ [leaFrame (Int.ofNat (Params.ofBody body).frame)])) := by
  set P := Params.ofBody body with hP
  have hF1 := forall₂_of_straightOK h1
  have hall : List.Forall₂ (fun instr sh => DShapeOK P instr.li_i sh) body
      (shapesD P P1 ++ [.one .skip]) := by
    rw [hbody]
    exact List.rel_append (hF1.imp fun _ _ h => h.1)
      (.cons (by rw [hr]; exact shapeOK_ret P) .nil)
  rw [decodeLprog_encodeLfundefBytes_shapes body _ hsaves hF0 hF hF' hall hbr, fundefItemsL]
  rw [← hP]
  obtain ⟨o, e⟩ := itemsFromL_append' P P1 [r] (shapesD P P1) [.one .skip] hF1.length_eq 0
  conv_lhs => rw [hbody, e]
  obtain ⟨hA, eA⟩ := itemsFromL_opItems P hF1 0
  have hlea : ∀ d : Int, OpItems [mkLea d] := fun d it hit => by
    rw [List.mem_singleton] at hit; subst hit; exact ⟨rfl, rfl, Or.inr ⟨_, rfl⟩⟩
  have hrI : OpItems (itemsFromL P o [r] [.one .skip]) := by
    intro it hit
    simp only [itemsFromL, dItems, List.append_nil, List.mem_singleton] at hit
    subst hit
    exact ⟨by simp [hr, labelOf], rfl, Or.inl rfl⟩
  have hxs := ((hlea (-(Int.ofNat P.frame))).append (hA.append hrI)).append
    (hlea (Int.ofNat P.frame))
  have key := expectedFrom_opItems_append
    (mkLea (-(Int.ofNat P.frame)) :: (itemsFromL P 0 P1 (shapesD P P1)
      ++ itemsFromL P o [r] [.one .skip] ++ [mkLea (Int.ofNat P.frame), mkRet]))
    ([mkLea (-(Int.ofNat P.frame))] ++ (itemsFromL P 0 P1 (shapesD P P1)
      ++ itemsFromL P o [r] [.one .skip]) ++ [mkLea (Int.ofNat P.frame)]) [mkRet] hxs
  simp only [List.cons_append, List.nil_append, List.append_assoc] at key ⊢
  rw [key]
  have hoa : ∀ xs ys : List Item, opsOf (xs ++ ys) = opsOf xs ++ opsOf ys := fun xs ys => by
    simp [opsOf, List.filterMap_append]
  have hoc : ∀ (d : Int) (xs : List Item), opsOf (mkLea d :: xs) = leaFrame d :: opsOf xs :=
    fun _ _ => rfl
  have hor : opsOf (itemsFromL P o [r] [.one .skip]) = [] := by
    simp [itemsFromL, dItems, opsOf, Shape.dec]
  have hol : opsOf [mkLea (Int.ofNat P.frame)] = [leaFrame (Int.ofNat P.frame)] := rfl
  simp only [expectedFrom, mkRet, Option.map_some]
  rw [hoc, hoa, hoa, hor, hol, eA]
  simp [lineLayout, opsD]

/-! ## 2. The prologue and the epilogue -/

/-- **The prologue check of a straight-line body.** The symbolic prologue is accepted in the
    frame range `[lo, hi]`; every live name of `L0` has a System V register whose entry
    value the machine register of the name holds; the frame slot of every region lies in
    `[lo, hi]` and holds the entry value of the region's register. Returns the symbolic
    machine state after the prologue. -/
def preLine (E : MemEnv) (abi : String → Option String) (lo hi : Int) (L0 : List String)
    (pre : List (JInstr 64)) : Option PSt :=
  match prun lo hi PSt.init pre with
  | some p =>
      if L0.all (fun r => (fdflt abi r).isSome && fdflt abi r == p.get (E.pi r))
          && E.rs.all (fun g => decide (lo ≤ p.sp + g.off) && decide (p.sp + g.off ≤ hi)
            && (abi g.name).isSome && stkGet p.stk (p.sp + g.off) == (abi g.name).map SVal.ent)
      then some p else none
  | none => none

/-- The pointer slots of an accepted prologue lie in the frame range. -/
theorem preLine_slots {E : MemEnv} {abi : String → Option String} {lo hi : Int}
    {L0 : List String} {pre : List (JInstr 64)} {p : PSt}
    (hres : preLine E abi lo hi L0 pre = some p) :
    ∀ g ∈ E.rs, lo ≤ p.sp + g.off ∧ p.sp + g.off ≤ hi := by
  unfold preLine at hres
  split at hres
  · split at hres
    · rename_i hc
      obtain rfl := Option.some.inj hres
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      exact fun g hg => (hc.2 g hg).1.1
    · exact absurd hres (by simp)
  · exact absurd hres (by simp)

/-- **The prologue of a straight-line body.** For an accepted prologue with final symbolic
    state `p`, from the entry correspondence at the entry state `sa0`, whose region cells
    are disjoint from the frame words `[lo, hi]`, the empty chain simulates the machine
    prologue to `MCorr` on the live names `L0` with no machine facts, at the stack pointer
    `sa0.regs "%rsp" + p.sp`. -/
theorem decSim_preLine {E : MemEnv} {abi : String → Option String} {lo hi : Int}
    {L0 : List String} {pre : List (JInstr 64)} {p : PSt} (hsp : E.sp = "%rsp")
    (hres : preLine E abi lo hi L0 pre = some p) (sa0 : AState)
    (hfr : ∀ A j, regK E.rs A j → ∀ o : Int, lo ≤ o → o ≤ hi →
      Disjoint8 (sa0.regs "%rsp" + BitVec.ofInt 64 o) ((regLay E.rs (abiBase abi sa0)).addr A j)) :
    DecSim (fun sa b _ => sa = sa0 ∧ NodeEntry abi E.rs sa b)
      (MCorr E (abiBase abi sa0) (sa0.regs "%rsp" + BitVec.ofInt 64 p.sp) (L0, Abs.empty) False)
      [] pre := by
  unfold preLine at hres
  split at hres
  · rename_i p' hp
    split at hres
    · rename_i hc
      obtain rfl := Option.some.inj hres
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
        Option.isSome_iff_exists] at hc
      obtain ⟨hL, hrs⟩ := hc
      rintro sa b zf ⟨rfl, hent⟩
      have hpi := prun_sound pre _ _ sa hp (pInv_init lo hi sa)
      refine ⟨b, zf, rfl, ⟨⟨fun r hr => ?_, fun hz => hz.elim, fun A j hk => ?_,
        fun A q hq => ?_⟩, ?_, Abs.holds_empty _ _ _⟩⟩
      · obtain ⟨⟨v, hv⟩, he⟩ := hL r hr
        simp only [fdflt, Option.map_eq_some_iff] at hv
        obtain ⟨R', hR', rfl⟩ := hv
        rw [hent.regs r R' hR', hpi.regs (E.pi r) (.ent R') (by rw [← he]; simp [fdflt, hR'])]
        rfl
      · obtain ⟨arr, ha, hc⟩ := hent.cells A j hk
        exact ⟨hk, arr, ha, by rw [hpi.mem _ (hfr A j hk)]; exact hc⟩
      · have hq' : (regFind E.rs A).isSome = true ∧ A = q := by
          simp only [regLay] at hq
          split at hq
          · rename_i hs; exact ⟨hs, Option.some.inj hq⟩
          · exact absurd hq (by simp)
        obtain ⟨hs, rfl⟩ := hq'
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨hgm, hgn⟩ := regFind_spec hg
        obtain ⟨⟨⟨_, _⟩, ⟨R', hR'⟩⟩, hst⟩ := hrs g hgm
        rw [hR'] at hst
        refine ⟨sa.regs "%rsp" + BitVec.ofInt 64 (p'.sp + g.off), ?_, ?_⟩
        · simp [regFrame, hg, BitVec.ofInt_add, BitVec.add_assoc]
        · rw [hpi.stk _ (stkGet_mem _ _ (.ent R') hst), ← hgn]
          show sa.regs R' = abiBase abi sa g.name
          simp only [abiBase, hR']
      · rw [hsp]; exact hpi.sp
    · exact absurd hres (by simp)
  · exact absurd hres (by simp)

/-- **The epilogue check.** The symbolic run of `post` in the frame range `[lo, hi]` is
    accepted and ends with the register `RA` holding the value `R` held before it. -/
def postLine (lo hi : Int) (RA R : String) (post : List (JInstr 64)) : Bool :=
  (prun lo hi PSt.init post).any (fun p => p.get RA == some (.ent R))

/-- An accepted epilogue moves the value of `R` to `RA`. -/
theorem postLine_sound {lo hi : Int} {RA R : String} {post : List (JInstr 64)}
    (h : postLine lo hi RA R post = true) (sa : AState) :
    (aMachine.runBlock sa post).regs RA = sa.regs R := by
  unfold postLine at h
  cases hp : prun lo hi PSt.init post with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some p =>
    rw [hp] at h
    have hpi := prun_sound post _ _ sa hp (pInv_init lo hi sa)
    exact hpi.regs RA (.ent R) (by simpa using h)

/-! ## 3. The check and the body -/

/-- The witness of a straight-line check: the machine environment, the live names at the
    start of the chain, the decoded machine block, and the lengths of its prologue and
    middle. -/
structure LineWit where
  /-- The machine environment. -/
  E : MemEnv
  /-- The live names at the start of the chain. -/
  L0 : List String
  /-- The decoded machine block. -/
  js : List (JInstr 64)
  /-- The length of the prologue. -/
  nPre : Nat
  /-- The length of the middle. -/
  nMid : Nat

/-- The prologue of a witness. -/
def LineWit.pre (W : LineWit) : List (JInstr 64) := W.js.take W.nPre

/-- The middle of a witness. -/
def LineWit.mid (W : LineWit) : List (JInstr 64) := (W.js.drop W.nPre).take W.nMid

/-- The epilogue of a witness. -/
def LineWit.post (W : LineWit) : List (JInstr 64) := (W.js.drop W.nPre).drop W.nMid

theorem LineWit.js_eq (W : LineWit) : W.js = W.pre ++ (W.mid ++ W.post) := by
  simp only [LineWit.pre, LineWit.mid, LineWit.post, List.take_append_drop]

/-- **The check of a straight-line body.** The stack register, the regions of `σ`, the
    all-`Lopn` chain, the prologue check at the frame range of `σ`, the middle checked
    against the chain by `mbodyOK` with the return name `ret` live at its end, and, for a
    register result `RA` of `σ`, the epilogue check moving the machine register of `ret`
    to `RA`. -/
def lineCheck (σ : AbiLayout) (W : LineWit) (ops : List LinstrRM) (ret : String) : Bool :=
  W.E.sp == "%rsp" && rsOK σ W.E.rs && ops.all isLopnB
    && (preLine W.E (abiReg σ) σ.frameLo σ.frameHi W.L0 W.pre).isSome
    && (mbodyOK W.E (fun s => decide (ret ∈ s.1)) (W.L0, Abs.empty) ops W.mid).isSome
    && match σ.result with
      | .reg RA => postLine σ.frameLo σ.frameHi RA (W.E.pi ret) W.post
      | _ => false

/-- A chain of `Lopn`s whose straight fold runs from `b` to `b1` halts under
    `lsemFuelMemF` in the state with base `b1`. -/
theorem lsemFuelMemF_line (fn : String) (ops : List LinstrRM) (hL : ∀ i ∈ ops, IsLopn i)
    (b b1 : LstateM) (zf z1 : Bool) (hpc : b.lpc = 0)
    (hr : runStraightF ops b zf = some (b1, z1)) :
    lsemFuelMemF (singletonProgM fn ops) ops.length
        { prog := { base := b, lfn := fn }, zf := zf }
      = some { prog := { base := b1, lfn := fn }, zf := z1 } := by
  have hseg := lsemFuelMemF_segF (singletonProgM fn ops) fn rfl ops b zf 0 hL
    (fun k _ => by rw [hpc, Nat.zero_add]; rfl)
  rw [Nat.add_zero] at hseg
  rw [hseg, hr, Option.bind_some]
  refine lsemFuelMemF_halt _ 0 _ ?_
  show findInstrMem (singletonProgM fn ops)
    ({ base := b1, lfn := (singletonProgM fn ops).lfn } : LstatePM) = none
  rw [findInstrMemF_self]
  apply List.getElem?_eq_none
  rw [runStraightF_lpc ops b zf b1 z1 hr, hpc, Nat.zero_add]
  exact le_refl _

/-- **The decoded bytes of a straight-line body realise the result read-back.** For bytes
    that decode to the layout of the witness's machine block and a chain `ops` that passes
    `lineCheck` against `σ` with the return name `ret`, from an entry state satisfying
    `σ.Regions` and the entry correspondence, with the flag machine at program counter `0`:
    every halting run of `ops` whose return name holds the word `x` is matched by a halting
    run of the decoded program from which `σ` reads back `x`. -/
theorem decLine_result (σ : AbiLayout) (W : LineWit) (fn : String) (ops : List LinstrRM)
    (ret : String) (bytes : List (BitVec 8)) (hdec : decodeLprog bytes = some (lineLayout W.js))
    (hchk : lineCheck σ W ops ret = true)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hreg : σ.Regions sa)
    (hent : NodeEntry (abiReg σ) W.E.rs sa b) {w : Nat} (hw : w = 64) (k : Nat)
    (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn ops) k
      { prog := { base := b, lfn := fn }, zf := zf } = some t)
    (x : BitVec w) (hx : t.prog.base.reg.getW ret w = some x) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (.int x.toNat) := by
  subst hw
  simp only [lineCheck, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hsp, hrs⟩, hopsL⟩, hpre⟩, hmid⟩, hpost⟩ := hchk
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hpre
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hmid
  have hsep := memSep_of_regions hrs hreg p.sp (preLine_slots hp)
  obtain ⟨hfin, hdm⟩ := mbodyOK_sound hsep _ ops _ s' W.mid False hs'
  have hsim := (decSim_preLine hsp hp sa (frameSep_of_regions hrs hreg)).append hdm
  rw [List.nil_append] at hsim
  obtain ⟨b1, z1, hr1, hJ⟩ := hsim sa b zf ⟨rfl, hent⟩
  have hL : ∀ i ∈ ops, IsLopn i := fun i hi => isLopnB_isLopn (List.all_eq_true.mp hopsL i hi)
  have hrun1 := lsemFuelMemF_line fn ops hL b b1 zf z1 hpc hr1
  obtain rfl := lsemFuelMemF_det _ k ops.length _ t _ hrun hrun1
  have hret : ret ∈ s'.1 := by simpa using hfin
  have hv := hJ.1.regs ret hret
  rw [hx] at hv
  obtain rfl := Option.some.inj hv
  split at hpost
  · rename_i RA hRA
    refine ⟨lineLayout W.js, aMachine.runBlock sa W.js, hdec,
      ⟨W.js.length, ?_, ?_⟩, ?_⟩
    · have h := reaches_ops aMachine [] W.js [.ret] sa
      simpa [lineLayout] using h
    · simp [lineLayout]
    · show _ = σ.result.read sa _
      rw [hRA]
      simp only [ResultKind.read]
      have e : aMachine.runBlock sa (W.pre ++ W.mid ++ W.post)
          = aMachine.runBlock (aMachine.runBlock sa (W.pre ++ W.mid)) W.post :=
        Machine.runBlock_append ..
      rw [W.js_eq, ← List.append_assoc, e, postLine_sound hpost]
  · exact absurd hpost (by simp)

/-- The regions of a witness accepted by `lineCheck` are accepted by `rsOK`. -/
theorem lineCheck_rsOK {σ : AbiLayout} {W : LineWit} {ops : List LinstrRM} {ret : String}
    (h : lineCheck σ W ops ret = true) : rsOK σ W.E.rs = true := by
  simp only [lineCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

/-- **The decode leg of a straight-line chain from an entry map.** For a chain `ops` that
    passes `lineCheck` with the return name `ret` and bytes that decode to the witness's
    layout, and an entry map `entry` whose states sit at program counter `0` and satisfy the
    entry correspondence: from every entry state satisfying `σ.Regions`, every halting run
    of `ops` from `entry sa` whose return name holds the width-`64` word `x` is matched by a
    halting run of the decoded program from which `σ` reads back `x`. -/
theorem decLine_entry (σ : AbiLayout) (W : LineWit) (ops : List LinstrRM) (ret : String)
    (bytes : List (BitVec 8)) (hdec : decodeLprog bytes = some (lineLayout W.js))
    (hchk : lineCheck σ W ops ret = true) (entry : AState → LstateM)
    (hpc : ∀ sa, (entry sa).lpc = 0) (hent : ∀ sa, NodeEntry (abiReg σ) W.E.rs sa (entry sa))
    {w : Nat} (hw : w = 64) :
    ∀ (sa : AState) (k : Nat) (t : LstateMF), σ.Regions sa →
      lsemFuelMemF (singletonProgM "" ops) k
          { prog := { base := entry sa, lfn := "" }, zf := false } = some t →
      ∀ x : BitVec w, t.prog.base.reg.getW ret w = some x →
      ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
        ∧ σ.ResultOf sa sa' (.int x.toNat) :=
  fun sa k t hreg hrun x hx =>
    decLine_result σ W "" ops ret bytes hdec hchk sa (entry sa) false (hpc sa) hreg (hent sa) hw
      k t hrun x hx

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenStraight
