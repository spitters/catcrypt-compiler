/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys

/-!
# The pointer load of a frame array

The pointer load of a frame array is the address load `LEA:64 d, q` of a frame-array name `q`
(`faB`) that is the slot of an array (`faLoad?`). On the address machine it writes the frame
address of `q` to `d` and accesses no memory. On the name-keyed image the name `q` holds that
address (`ImageAddrSim.frameVal`), so the cast `CASTW_64_64 d, q` at the tag `.reg (some 64)`,
the form of the reload of a base, writes the same word to `d`.

The symbolic step fails on the load, so the register gates `regGateB` and `regGateBW` refuse
it and the width analysis is the same before and after it.

## Main results

* `regGateB_faLoad`, `regGateBW_faLoad`: the two register gates refuse the load.
* `oneBitStep_faLoad`, `oneBitAt_succ_faLoad`: the width analysis does not change at the load.
* `instrLeakA_leaFa`: the address load of a frame-array name has no event.
* `faLoad_stepW`: from states related by `ImgRelW`, the step of the cast on the image is the
  step of the load on the address machine, and the two successors satisfy every field of
  `ImgRelW` other than `reload`.
* `faLoad_relW_of_reload`: with the field `reload` at the successor, the successors are
  related by `ImgRelW`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FrameArrLoad

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (instrLeakA)

/-! ## The reader -/

/-- The pointer load of a frame array: the address load `LEA:64 d, q` of a frame-array name
    `q` (`faB`) that is the slot of an array in `slotArr`, as `(d, q)`. -/
def faLoad? (slotArr : String → Option (String × Nat)) : LinstrR → Option (String × String)
  | .Lopn [.reg d] o [.reg q] =>
      if o = "LEA:64" ∧ faB q = true ∧ (slotArr q).isSome = true then some (d, q) else none
  | _ => none

/-- The instructions that `faLoad?` reads are the address loads of the frame-array names that
    are array slots. -/
theorem faLoad?_eq_some {slotArr : String → Option (String × Nat)} {i : LinstrR}
    {d q : String} :
    faLoad? slotArr i = some (d, q) ↔
      i = .Lopn [.reg d] "LEA:64" [.reg q] ∧ faB q = true ∧ (slotArr q).isSome = true := by
  unfold faLoad?
  grind

section Reader

variable {slotArr : String → Option (String × Nat)} {i : LinstrR} {d q : String}

/-- The pointer load of a frame array is its own normal form on the address machine. -/
theorem normA_faLoad (h : faLoad? slotArr i = some (d, q)) : normA i = i := by
  obtain ⟨rfl, -⟩ := faLoad?_eq_some.1 h
  rw [normA_of_caret_free (by decide)]
  simp

/-- The pointer load of a frame array is no move between names. -/
theorem slotMov?_faLoad (h : faLoad? slotArr i = some (d, q)) : slotMov? i = none := by
  obtain ⟨rfl, -⟩ := faLoad?_eq_some.1 h
  simp [slotMov?]

/-- The tag of the pointer load of a frame array at a position is the register tag. -/
theorem tagAt_faLoad (h : faLoad? slotArr i = some (d, q)) (body : Lcmd) (k : Nat) :
    tagAt body k i = .reg none := by
  obtain ⟨rfl, -⟩ := faLoad?_eq_some.1 h
  exact tagAt_reg_of_caret_free (by decide) (by decide) (by decide)
    (bitMovB_of_ne (by simp [movImmStruct?]))

/-- The pointer load of a frame array has the kind of a register instruction at every
    frame. -/
theorem icase_faLoad (h : faLoad? slotArr i = some (d, q))
    (frame : String → Option (BitVec 64)) : icase frame i = .reg := by
  obtain ⟨rfl, -⟩ := faLoad?_eq_some.1 h
  have hu : LprogAsmPrinter.untagCaret "LEA:64" = "LEA:64" :=
    LprogAsmPrinter.untagCaret_of_caret_free (by decide)
  simp [icase, hu, castTagW, slotMov?, slotCmp?, normA]

/-! ## The refusal by the register gates -/

/-- The symbolic step fails on the pointer load of a frame array. -/
theorem symStep_faLoad (h : faLoad? slotArr i = some (d, q)) :
    symStep (i, .reg none) SSt.start = .fail := by
  obtain ⟨rfl, -⟩ := faLoad?_eq_some.1 h
  have h1 : stripWidthTag "LEA:64" = "LEA" := by decide +kernel
  have h2 : JasminImmShiftMnem.immShiftMnem? "LEA:64" = none := by decide +kernel
  simp [h1, h2, symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, symMem,
    symCast, castStruct?, movImmStruct?, symMC, symSh, symN,
    JasminLsemMulCarry.mulhiStruct?, JasminLsemMulCarry.adcxStruct?,
    JasminLsemMulCarry.adcxhiStruct?, JasminLsemMulCarry.sbbStruct?,
    JasminLsemMulCarry.sbbhiStruct?, VIR.JasminLsemShift.sarStruct?, liftR, aluFl]

/-- **The register gate refuses the pointer load of a frame array.** -/
theorem regGateB_faLoad (h : faLoad? slotArr i = some (d, q))
    (frame : String → Option (BitVec 64)) : regGateB frame i = false := by
  simp [regGateB, symStep_faLoad h]

/-- **The register gate over a width analysis refuses the pointer load of a frame array.** -/
theorem regGateBW_faLoad (h : faLoad? slotArr i = some (d, q))
    (frame : String → Option (BitVec 64)) (W : List String) :
    regGateBW frame W i = false := by
  simp [regGateBW, symStep_faLoad h]

/-! ## The width analysis -/

/-- **The step of the width analysis at the pointer load of a frame array is the identity.** -/
theorem oneBitStep_faLoad (h : faLoad? slotArr i = some (d, q))
    (frame : String → Option (BitVec 64)) (W : List String) : oneBitStep frame W i = W := by
  have hc : carryI? i = none := by
    obtain ⟨rfl, -⟩ := faLoad?_eq_some.1 h
    simp [carryI?]
  have hm : movImmStruct? i = none := by
    obtain ⟨rfl, -⟩ := faLoad?_eq_some.1 h
    simp [movImmStruct?]
  simp [oneBitStep, hc, hm, icase_faLoad h, normA_faLoad h, regOut, symStep_faLoad h,
    copyOut_of_slotMov_none (slotMov?_faLoad h)]

/-- **The width analysis one past the pointer load of a frame array is the analysis at the
    load.** -/
theorem oneBitAt_succ_faLoad (frame : String → Option (BitVec 64)) {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) (h : faLoad? slotArr bi.li_i = some (d, q)) :
    oneBitAt frame body (k + 1) = oneBitAt frame body k := by
  have hx := (faLoad?_eq_some.1 h).1
  have hs : bitStore? body k bi.li_i = none := by
    rw [hx]
    exact bitStore?_of_ne (by simp)
  rw [oneBitAt_succ hb hs (seedAt_of_eq hx (by simp)), oneBitStep_faLoad h]

end Reader

/-! ## The events -/

/-- **The address load of a frame-array name accesses no memory**: it has no event on the
    address machine. -/
theorem instrLeakA_leaFa (frame : String → Option (BitVec 64)) {d q : String}
    (hq : faB q = true) (sa : LstateA) :
    instrLeakA frame (.Lopn [.reg d] "LEA:64" [.reg q], .reg none) sa = [] := by
  simp [instrLeakA, slotMov?, slotCmp?, cellA?, cellParts?_of_faB hq, slotCarry?, slotImm?,
    slotCmov?, LprogAsmPrinter.untagCaret_of_caret_free (by decide : '^' ∉ "LEA:64".toList)]

/-! ## The step -/

section Step

variable {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
  {base : String → BitVec 64} {body : Lcmd}

/-- **The pointer load of a frame array against the cast on the image.** Let the states be
    related by `ImgRelW` at the load `LEA:64 d, q` of the frame-array name `q` at the frame
    address `a`, let `d` have no frame word, and let `q`, if it lies in the width analysis, be
    written by no untagged immediate move of the body (`movlNames`). Where the image steps the
    cast `CASTW_64_64 d, q` at the tag `.reg (some 64)` to `t`, the address machine steps the
    load to the state `sa'` that has `a` in `d`, and `t` and `sa'` satisfy each field of
    `ImgRelW` other than `reload`, in the order of the structure: `pc`, `regs`, `slots`, `zf`,
    `cf`, `of`, `wid`, `cells`, `saved`, `held`, `bits`. -/
theorem faLoad_stepW (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF}
    {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d q : String}
    (hl : faLoad? slotArr bi.li_i = some (d, q)) (hd : frame d = none) {a : BitVec 64}
    (ha : frame q = some a)
    (hqN : q ∈ oneBitAt frame body sa.reg.lpc → q ∉ movlNames body)
    (hs : evalInstrPMemFk true P (.Lopn [.reg d] "CASTW_64_64" [.reg q], .reg (some 64)) s
      = some t) :
    let sa' : LstateA := { sa with reg := (sa.reg.setReg d a).nextPc }
    fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ sa'.reg.lpc = t.prog.base.reg.lpc
      ∧ (∀ r, frame r = none →
          RegVal (oneBitAt frame body sa'.reg.lpc) r (t.prog.base.reg.lvm r) (sa'.reg.lvm r))
      ∧ (∀ q' a', frame q' = some a' →
          SlotVal (movlNames body) (oneBitAt frame body sa'.reg.lpc) q'
            (t.prog.base.reg.lvm q') (frameVal sa'.mem q' a'))
      ∧ t.zf = zf
      ∧ sa'.cf = t.prog.base.cf
      ∧ sa'.of = t.prog.base.of
      ∧ (∀ r, gpOk r = true → r ∉ oneBitAt frame body sa'.reg.lpc → (sa'.reg.lvm r).1 = 64)
      ∧ (∀ q' A n, slotArr q' = some (A, n) → ∃ arr, t.prog.base.getArr A 64 n = some arr ∧
          ∀ j (hj : j < n), read64 sa'.mem (cellAt (base A) j) = arr ⟨j, hj⟩)
      ∧ (∀ k R A n a', SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
          frame (slotOfReg R) = some a' →
            (k < sa'.reg.lpc → read64 sa'.mem a' = base A)
              ∧ (sa'.reg.lpc ≤ k → sa'.reg.getW R 64 = some (base A)))
      ∧ HeldAt frame slotArr base sa'.mem
      ∧ (∀ r, gpOk r = true → r ∉ castDsts body →
          (sa'.reg.lvm r).1 = 64 ∨ (sa'.reg.lvm r).1 = 1) := by
  intro sa'
  obtain ⟨hx, hfa, -⟩ := faLoad?_eq_some.1 hl
  have hnm := slotMov?_faLoad hl
  have hW := oneBitAt_succ_faLoad frame hb hl
  have hpc : sa'.reg.lpc = sa.reg.lpc + 1 := by simp [sa']
  have hsq := hrel.slots q a ha
  rw [frameVal_of_fa hfa] at hsq
  -- the word that the cast writes is the frame address
  have hv : (s.prog.base.reg.lvm q).2.zeroExtend 64 = a := by
    rcases hsq with h | ⟨hqW, h, hz⟩
    · rw [h]; simp
    · rw [h]; simpa using hz (hqN hqW)
  rw [eval_cast64, hv] at hs
  cases hs
  refine ⟨?_, ?_, fun r hr => ?_, fun q' a' ha' => ?_, hrel.zf, hrel.cf, hrel.of,
    fun r hr hrW => ?_, fun q' A n hq' => ?_, fun k R A n a' hS hA ha' => ?_, hrel.held,
    bits_setReg hrel.bits d a (Or.inl rfl)⟩
  · rw [normA_faLoad hl, hx, fstepA_leaFa frame hfa ha, hrel.zf]
  · simp [sa', LstateM.setReg, LstateM.nextPc, hrel.pc]
  · rw [hpc, hW]
    by_cases e : r = d
    · exact Or.inl (by simp [sa', LstateM.setReg, LstateM.nextPc, e])
    · exact (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e])
        (by simp [sa', e]) id
  · rw [hpc, hW]
    have e : q' ≠ d := by grind
    exact (hrel.slots q' a' ha').of_eq (by simp [LstateM.setReg, LstateM.nextPc, e]) rfl id
  · rw [hpc, hW] at hrW
    by_cases e : r = d
    · simp [sa', e]
    · simp [sa', e, hrel.wid r hr hrW]
  · obtain ⟨arr, h1, h2⟩ := hrel.cells q' A n hq'
    exact ⟨arr, by simpa using h1, h2⟩
  · -- the load is no save, and no save follows an instruction that is no move
    obtain ⟨i', hi', hm'⟩ := hS
    rw [hpc]
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · have hlt : k < sa.reg.lpc := by grind
      exact (hrel.saved k R A n a' ⟨i', hi', hm'⟩ hA ha').1 hlt
    · have hent := (physImgB_slotStore hphys hi' hm' (by simp [hA])).2
      obtain ⟨d', src, hm2, -⟩ := entryRegB_spec hent (show sa.reg.lpc < k by omega) hb
      simp [hnm] at hm2

/-- **The pointer load of a frame array keeps `ImgRelW` where it keeps `reload`**: in the
    setting of `faLoad_stepW`, the field `reload` at the successor of the address machine
    gives `ImgRelW` at the two successors. -/
theorem faLoad_relW_of_reload (hphys : physImgB slotArr body = true) (P : LprogM)
    {s t : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {d q : String}
    (hl : faLoad? slotArr bi.li_i = some (d, q)) (hd : frame d = none) {a : BitVec 64}
    (ha : frame q = some a)
    (hqN : q ∈ oneBitAt frame body sa.reg.lpc → q ∉ movlNames body)
    (hs : evalInstrPMemFk true P (.Lopn [.reg d] "CASTW_64_64" [.reg q], .reg (some 64)) s
      = some t)
    (hreload : ∀ b q' a' A n, reloadOf slotArr body (sa.reg.lpc + 1) b = some q' →
      slotArr q' = some (A, n) → frame q' = some a' → frame b = none →
        ((sa.reg.setReg d a).nextPc).lvm b = ⟨64, frameVal sa.mem q' a'⟩) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨hst, hpc, hregs, hslots, -, hcf, hof, hwid, hcells, hsaved, hheld, hbits⟩ :=
    faLoad_stepW hphys P hrel hb hl hd ha hqN hs
  exact ⟨_, hst, hpc, hregs, hslots, rfl, hcf, hof, hwid, hcells, hsaved,
    by simpa using hreload, hheld, hbits⟩

end Step

/-- The hypotheses of `faLoad_relW_of_reload`, and with them those of each theorem of the module,
    hold at the one-instruction body `LEA:64 RAX, fa.0.1` for every frame address and memory. -/
example (P : LprogM) (a : BitVec 64) (mem : AMem) :
    ∃ (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
      (base : String → BitVec 64) (body : Lcmd) (s t : LstateMF) (sa sa' : LstateA)
      (bi : Linstr) (d q : String),
      body[sa.reg.lpc]? = some bi ∧ faLoad? slotArr bi.li_i = some (d, q)
        ∧ frame d = none ∧ frame q = some a ∧ sa.mem = mem
        ∧ fstepA frame (normA bi.li_i, .reg none) sa s.zf = some (sa', t.zf)
        ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  let frame : String → Option (BitVec 64) := fun q => if q = "fa.0.1" then some a else none
  let slotArr : String → Option (String × Nat) :=
    fun q => if q = "fa.0.1" then some ("A", 1) else none
  let bi : Linstr := ⟨0, .Lopn [.reg "RAX"] "LEA:64" [.reg "fa.0.1"]⟩
  let regs : LstateN := { lvm := fun r => ⟨64, if r = "fa.0.1" then a else 0⟩ }
  let cells : ArrCell := ⟨64, 1, fun j => read64 mem (cellAt a j)⟩
  let s : LstateMF := { prog := { base := { reg := regs, larr := fun _ => cells }, lfn := "f" } }
  let sa : LstateA := { reg := regs, mem := mem }
  have hfa : faB "fa.0.1" = true := by decide +kernel
  have hns : ∀ R, slotArr (slotOfReg R) = none := fun R => by grind [faB_slotOfReg]
  have hl : faLoad? slotArr bi.li_i = some ("RAX", "fa.0.1") := by simp [faLoad?, slotArr, bi, hfa]
  have hphys : physImgB slotArr [bi] = true := by
    simp [physImgB, slotArr, bi, accOkB, slotWriteB, slotMov?]
  have hrel : ImgRelW frame (slotArr) (fun _ => a) [bi] s sa s.zf :=
    { pc := rfl
      regs := fun r _ => Or.inl rfl
      slots := fun q a' h => Or.inl (by grind [frameVal])
      zf := rfl
      cf := rfl
      of := rfl
      wid := fun _ _ _ => rfl
      cells := fun q A n h => by
        obtain rfl : n = 1 := by grind
        refine ⟨_, by simp [LstateM.getArr, s, cells]; rfl, fun j hj => ?_⟩
        grind
      saved := fun k R A n a' _ h _ => by simp [hns R] at h
      reload := fun b q a' A n h => by simp [sa, regs, reloadOf] at h
      held := fun R A n a' _ h _ => by simp [hns R] at h
      bits := fun _ _ _ => Or.inl rfl }
  obtain ⟨sa', hst, hr⟩ := faLoad_relW_of_reload hphys P hrel (bi := bi) rfl hl
    (by simp [frame]) (a := a) (by simp [frame])
    (fun h => by simp [sa, regs, oneBitAt_zero] at h) (eval_cast64 P "RAX" "fa.0.1" s)
    (fun b q a' A n h => by simp [sa, regs, bi, reloadOf, slotMov?] at h)
  exact ⟨frame, slotArr, _, _, s, _, sa, sa', bi, _, _, rfl, hl, by simp [frame],
    by simp [frame], rfl, hst, hr⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.FrameArrLoad
