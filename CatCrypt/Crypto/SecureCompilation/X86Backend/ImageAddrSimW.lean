/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

@[expose] public section

set_option autoImplicit false

/-!
# The image simulation with carry chains

`ImageAddrSim.ImgRel` gives every general-purpose name the width `64`. A carry chain reads its
carry-in at width `1` (`lsemStepMC`, `fstepA`) and `ADCXHI:64` writes a one-bit carry-out, so
under `ImgRel` no step of a carry chain on general-purpose names is possible. This module
relates the image and the address machine at mixed width.

## The width analysis

`oneBitAt frame body k` is a decided over-approximation of the general-purpose names that may
hold a one-bit value at instruction `k`: the carry-out of `ADCXHI:64` and the destination of a
carry constant (`JasminLsemAddrRun.bitMovB`, stepped at the one-bit tag) enter it, and a name
written at width `64` leaves it. `ImgRelW` is `ImgRel` with the width condition restricted to
the names outside `oneBitAt` at the program counter. `imgGateBW` is the gate of
`ImageAddrSim.imgGateB` over the analysis: a carry-chain instruction `ADCX:64`/`ADCXHI:64` on
three sources is accepted with register or frame-slot word sources and a register carry-in, a
register instruction writes width-`64` words from names outside the analysis, a store into a
frame word stores a name outside it, an immediate move into a frame word writes a word that
holds no array pointer, a select `CMOV:64` reads a frame-word value at its frame word, a branch
is taken only where the analysis is empty, and every name an
instruction reads, other than a carry-in or the condition of a `CMOV:64` select
(`DecodePrintedAddrW.carryIns`), lies outside the analysis.

## Main results

* `oneBitAt_succ`: the analysis at the next instruction.
* `imgRelW_of`: `ImgRel` gives `ImgRelW` where the analysis is empty.
* `reg_stepW`, `rel_regW`, `rel_sloadW`, `rel_sstoreW`, `rel_scmpW`, `rel_ldxW`, `rel_stxW`,
  `rel_labelW`: each kind of instruction keeps `ImgRelW`.
* `rel_scarry`: a carry-chain instruction with register or frame-slot operands keeps
  `ImgRelW`.
* `rel_bmovW`: a carry constant keeps `ImgRelW`.
* `rel_stiW`: an immediate move into a frame word without an array pointer keeps `ImgRelW`.
* `rel_scmovW`: a select with a frame-word value keeps `ImgRelW`.
* `img_stepW`: one step of the image at a position without a branch is one step of the
  address machine.
* `haltedA_of_imgW`, `ptr_of_reloadW`, `wideSafe_of_gateW`, `imgGateBW_congr`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackSet stackGet_id)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk isRetB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (redW)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (LoadSafeAt RunSafe labelAt_spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames cellBase readsI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (carryIns WideSafeAt fstepA_adcx3 fstepA_adcxhi)

/-! ## 1. The carry-chain instructions on both machines -/

/-- The carry-chain instruction `ADCX:64 d, a, s, c` (`false`) or `ADCXHI:64 d, a, s, c`
    (`true`) on three register-named sources. -/
def carryI? : LinstrR → Option (Bool × String × String × String × String)
  | .Lopn [.reg d] m [.reg a, .reg s, .reg c] =>
      if m = "ADCX:64" then some (false, d, a, s, c)
      else if m = "ADCXHI:64" then some (true, d, a, s, c) else none
  | _ => none

theorem carryI?_eq {x : LinstrR} {hi : Bool} {d a s c : String}
    (h : carryI? x = some (hi, d, a, s, c)) :
    x = .Lopn [.reg d] (if hi then "ADCXHI:64" else "ADCX:64") [.reg a, .reg s, .reg c] := by
  unfold carryI? at h
  split at h
  · split_ifs at h with h1 h2
    · cases h; subst h1; rfl
    · cases h; subst h2; rfl
  · cases h

/-- The flag machine steps `ADCX:64 D, A, S, C` from 64-bit `A` and `S` by writing
    `addCarryWord` of them and the one-bit `C` to `D`. -/
theorem fstepF_adcx (D A S C : String) (m : LstateM) (zf : Bool) {va vb : BitVec 64}
    (hA : m.reg.getW A 64 = some va) (hS : m.reg.getW S 64 = some vb) :
    fstepF (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C], .reg none) m zf
      = (m.reg.getW C 1).map fun vc =>
          ({ m with reg := (m.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc },
            zf) := by
  cases hc : m.reg.getW C 1 <;>
    simp (config := { decide := true }) [fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem,
      lsemStepCast, castStruct?, movImmStruct?, lsemStepMC, mulhiStruct?, adcxStruct?,
      readReg_of_getW hA, hS, hc, withALUFlags, aluFlagOp?, carryArgs?, wideArgs?]

/-- The flag machine steps `ADCXHI:64 O, A, S, C` from 64-bit `A` and `S` by writing the
    one-bit `carryOutBit` of them and the one-bit `C` to `O`. -/
theorem fstepF_adcxhi (O A S C : String) (m : LstateM) (zf : Bool) {va vb : BitVec 64}
    (hA : m.reg.getW A 64 = some va) (hS : m.reg.getW S 64 = some vb) :
    fstepF (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C], .reg none) m zf
      = (m.reg.getW C 1).map fun vc =>
          ({ m with reg := (m.reg.setReg O (VIR.JasminDialect.carryOutBit va vb vc)).nextPc },
            zf) := by
  cases hc : m.reg.getW C 1 <;>
    simp (config := { decide := true }) [fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem,
      lsemStepCast, castStruct?, movImmStruct?, lsemStepMC, mulhiStruct?, adcxStruct?,
      adcxhiStruct?, readReg_of_getW hA, hS, hc, withALUFlags, aluFlagOp?, carryArgs?,
      wideArgs?]

/-! ## 2. The width analysis and the gate -/

/-- The names an `Lopn` reads as words: the implicit multiplicand `RDX`, the names of its
    source operands and the base registers of its cell operands (the names of `readsI` other
    than the empty name). -/
def readNames : LinstrR → List String
  | .Lopn ds _ ss => "RDX" :: (ss.flatMap srcNames ++ (ds ++ ss).filterMap cellBase)
  | _ => []

/-- The names possibly holding a one-bit value after a register instruction: those of `W`
    the symbolic description of the instruction does not write. -/
def regOut (W : List String) (x : LinstrR) : List String :=
  match symStep (x, .reg none) SSt.start with
  | .ok ss _ => W.filter fun r => !ss.wr.contains r
  | _ => W

/-- **One step of the width analysis.** The carry-out of `ADCXHI:64` and the destination of
    an untagged immediate move (a carry constant where the gate accepts it) enter the names
    possibly holding a one-bit value; the destination of `ADCX:64`, of an indexed load and
    of a load of a frame word, and the names a register instruction writes, leave it. -/
def oneBitStep (frame : String → Option (BitVec 64)) (W : List String) (x : LinstrR) :
    List String :=
  match carryI? x with
  | some (false, d, _, _, _) => W.filter (· != d)
  | some (true, o, _, _, _) => o :: W
  | none =>
      match icase frame x with
      | .ldx d _ _ => W.filter (· != d)
      | .sload d _ => W.filter (· != d)
      | .reg =>
          match movImmStruct? x with
          | some (d, _) => d :: W
          | none => regOut W (normA x)
      | _ => W

/-- **The width analysis** at instruction `k` of a body: the names that may hold a one-bit
    value there, over the straight-line prefix of the body. -/
def oneBitAt (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) : List String :=
  (body.take k).foldl (fun W i => oneBitStep frame W i.li_i) []

theorem oneBitAt_zero (frame : String → Option (BitVec 64)) (body : Lcmd) :
    oneBitAt frame body 0 = [] := by
  simp [oneBitAt]

theorem oneBitAt_succ {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) :
    oneBitAt frame body (k + 1) = oneBitStep frame (oneBitAt frame body k) bi.li_i := by
  unfold oneBitAt
  rw [List.take_add_one, hb]
  simp [List.foldl_append]

theorem regOut_slotImm (W : List String) (q : String) (v : Nat) {r : String} (hr : r ≠ q)
    (h : r ∉ regOut W (.Lopn [.reg q] "MOV:64" [.imm v])) : r ∉ W := by
  intro hW
  apply h
  have hm : stripWidthTag "MOV:64" = "MOV" := by decide +kernel
  have hn : ∀ R, symN (.Lopn [.reg q] "MOV:64" [.imm v]) R
      = .set q (.immW (widthFromTag "MOV:64") v) [] := fun R => by
    unfold symN
    simp only [hm, if_true]
  have hd : ∀ R, symMC (.Lopn [.reg q] "MOV:64" [.imm v]) R
      = .set q (.immW (widthFromTag "MOV:64") v) [] := fun R => by
    simp only [symMC, symSh, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?,
      VIR.JasminLsemShift.sarStruct?, hn]
  have hmi : movImmStruct? (.Lopn [.reg q] "MOV:64" [.imm v]) = none := by
    unfold movImmStruct?
    split
    · rename_i heq
      injection heq with _ h2 _
      exact absurd h2 (by decide +kernel)
    · rfl
  have hs : symStep (.Lopn [.reg q] "MOV:64" [.imm v], .reg none) SSt.start
      = .ok (SSt.start.setR q (.immW (widthFromTag "MOV:64") v)) [] := by
    simp [symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, symMem, symCast,
      castStruct?, hmi, hd, liftR, aluFl, aluFlT, aluFlagOp?, SSt.setR]
  simp only [regOut, hs]
  simp [SSt.setR, SSt.start, hW, hr]

theorem not_mem_filter_ne {W : List String} {d r : String} (h : r ∉ W.filter (· != d))
    (hr : r ≠ d) : r ∉ W := fun hm =>
  h (List.mem_filter.2 ⟨hm, by simpa using hr⟩)

/-- The symbolic word has width `64` when every general-purpose name outside `W` has width
    `64`: its width base is a general-purpose name outside `W` or has the known width `64`. -/
def wid64WB (W : List String) (t : STerm) : Bool :=
  match t.wbase with
  | .reg x => gpOk x && !W.contains x
  | u => u.wknown == some 64

theorem wid64WB_ev {W : List String} {t : STerm} (h : wid64WB W t = true)
    {V : String → Σ w, BitVec w} (A : String → ArrCell) (C O : Bool)
    (hV : ∀ r, gpOk r = true → r ∉ W → (V r).1 = 64) : (t.ev V A C O).1 = 64 := by
  rw [← STerm.wbase_ev V A C O t]
  unfold wid64WB at h
  split at h
  · rename_i x hx
    rw [hx]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact hV x h.1 (by simpa using h.2)
  · exact STerm.wknown_ev V A C O (by simpa using h)

/-- `regOkB`, and every general-purpose name the instruction writes receives a word of width
    `64` when the names outside `W` have width `64`. -/
def regGateBW (frame : String → Option (BitVec 64)) (W : List String) (x : LinstrR) : Bool :=
  regOkB frame x &&
    match symStep (x, .reg none) SSt.start with
    | .ok ss _ => ss.wr.all (fun r => !gpOk r || wid64WB W (ss.regs r))
    | _ => false

/-- The conditions of a carry-chain instruction `ADCX:64 d, a, s, c` (`hi = false`) or
    `ADCXHI:64 d, a, s, c` (`hi = true`): a general-purpose carry-in, word sources that are
    general-purpose names or frame slots, and a destination that is a general-purpose name or,
    for `ADCX:64`, a frame slot that holds no array pointer; the word sources are not the
    carry-in. -/
def carryOkB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (hi : Bool) (d a s c : String) : Bool :=
  (frame c).isNone && gpOk c && (gpOk a || (frame a).isSome) && (gpOk s || (frame s).isSome)
    && (if hi then gpOk d && (frame d).isNone
        else gpOk d || ((frame d).isSome && (slotArr d).isNone))
    && a != c && s != c

/-- Every general-purpose name an `Lopn` reads, other than a carry-in, lies outside `W`. -/
def readOkB (W : List String) (x : LinstrR) : Bool :=
  (readNames x).all fun r => !gpOk r || (carryIns x).contains r || !W.contains r

theorem readOkB_spec {W : List String} {x : LinstrR} (h : readOkB W x = true) {r : String}
    (hr : r ∈ readNames x) (hg : gpOk r = true) (hc : r ∉ carryIns x) : r ∉ W := by
  unfold readOkB at h
  have := List.all_eq_true.1 h r hr
  simp only [hg, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h1 | h1
  · exact absurd (by simpa using h1) hc
  · simpa using h1

/-- An immediate move `MOV:64 q, #v` into a frame word `q` that holds no array pointer. -/
def sImmB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat)) :
    LinstrR → Bool
  | .Lopn [.reg q] o [.imm _] => o == "MOV:64" && (frame q).isSome && (slotArr q).isNone
  | _ => false

theorem sImmB_spec {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {x : LinstrR}
    (h : sImmB frame slotArr x = true) :
    ∃ q v a, x = .Lopn [.reg q] "MOV:64" [.imm v] ∧ frame q = some a ∧ slotArr q = none := by
  unfold sImmB at h
  split at h
  · rename_i q o v
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists,
      Option.isNone_iff_eq_none] at h
    obtain ⟨⟨rfl, a, ha⟩, hs⟩ := h
    exact ⟨q, v, a, rfl, ha, hs⟩
  · cases h

/-- A select `CMOV:64 d, [c, a, b]` with a frame-word value: a destination and a condition
    without a frame word, a true value that is a general-purpose name or a frame word other
    than the condition, and a frame word among the two values. -/
def sCmovB (frame : String → Option (BitVec 64)) : LinstrR → Bool
  | .Lopn [.reg d] o [.reg c, .reg a, .reg b] =>
      o == "CMOV:64" && (frame d).isNone && (frame c).isNone && (gpOk a || (frame a).isSome)
        && a != c && ((frame a).isSome || (frame b).isSome)
  | _ => false

theorem sCmovB_spec {frame : String → Option (BitVec 64)} {x : LinstrR}
    (h : sCmovB frame x = true) :
    ∃ d c a b, x = .Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b] ∧ frame d = none
      ∧ frame c = none ∧ (gpOk a = true ∨ (frame a).isSome = true) ∧ a ≠ c
      ∧ ((frame a).isSome || (frame b).isSome) = true := by
  unfold sCmovB at h
  split at h
  · rename_i d o c a b
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, Bool.or_eq_true,
      bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨⟨rfl, hd⟩, hc⟩, ha⟩, hac⟩, hsl⟩ := h
    exact ⟨d, c, a, b, rfl, hd, hc, ha, hac, by simpa using hsl⟩
  · cases h

/-- **The gate of instruction `k` at the analysis `W`**: the names read lie outside `W`
    (`readOkB`), and the instruction is a carry-chain instruction passing `carryOkB`, a label,
    a branch where `W` is empty, an indexed access, a frame-word move or compare as in
    `instrGateB`, a carry constant (`bitMovB`) into a general-purpose name without a frame
    word, an immediate move into a frame word without an array pointer (`sImmB`), a select
    with a frame-word value (`sCmovB`), or a register instruction other than an untagged
    immediate move passing `regGateBW`. -/
def gateAtW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (W : List String) (x : LinstrR) : Bool :=
  readOkB W x &&
    match carryI? x with
    | some (hi, d, a, s, c) => carryOkB frame slotArr hi d a s c
    | none =>
        match icase frame x with
        | .label => true
        | .cond cc l => W.isEmpty && (condPol cc).isSome && (labelAt body l).isSome
        | .ldx d b idx => (accArr slotArr body k b).isSome && gpOk d && (frame d).isNone
            && (frame idx).isNone && (frame b).isNone
        | .stx _ b idx v => (accArr slotArr body k b).isSome && (frame idx).isNone
            && (frame b).isNone && (frame v).isNone
        | .sload d _ => gpOk d
        | .sstore _ S => gpOk S
        | .scmp _ y _ => (frame y).isNone
        | .reg =>
            match movImmStruct? x with
            | some (d, _) => bitMovB body k x && gpOk d && (frame d).isNone
            | none => sImmB frame slotArr x || sCmovB frame x || regGateBW frame W (normA x)
        | .other => false

/-- The gate of instruction `k` of a body at its width analysis. -/
def instrGateBW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (x : LinstrR) : Bool :=
  gateAtW frame slotArr body k (oneBitAt frame body k) x

/-- **The gate of the image simulation with carry chains**: every instruction but the last
    passes `instrGateBW`, the last is the return, and every array-pointer reload follows a
    save. -/
def imgGateBW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all (fun k =>
      (body[k]?).all fun i => instrGateBW frame slotArr body k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- **The relation of the image simulation with carry chains**: `ImgRel` with the width
    condition on the general-purpose names outside the width analysis at the program
    counter. -/
structure ImgRelW (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (body : Lcmd)
    (s : LstateMF) (sa : LstateA) (zf : Bool) : Prop where
  pc : sa.reg.lpc = s.prog.base.reg.lpc
  regs : ∀ r, frame r = none → s.prog.base.reg.lvm r = sa.reg.lvm r
  slots : ∀ q a, frame q = some a → s.prog.base.reg.lvm q = ⟨64, read64 sa.mem a⟩
  zf : s.zf = zf
  cf : sa.cf = s.prog.base.cf
  of : sa.of = s.prog.base.of
  wid : ∀ r, gpOk r = true → r ∉ oneBitAt frame body sa.reg.lpc → (sa.reg.lvm r).1 = 64
  cells : ∀ q A n, slotArr q = some (A, n) → ∃ arr, s.prog.base.getArr A 64 n = some arr ∧
    ∀ j (hj : j < n), read64 sa.mem (cellAt (base A) j) = arr ⟨j, hj⟩
  saved : ∀ k R A n a, SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
    frame (slotOfReg R) = some a →
      (k < sa.reg.lpc → read64 sa.mem a = base A)
        ∧ (sa.reg.lpc ≤ k → sa.reg.getW R 64 = some (base A))
  reload : ∀ b q a i, 1 ≤ sa.reg.lpc → body[sa.reg.lpc - 1]? = some i →
    slotMov? i.li_i = some (b, q) → frame q = some a → frame b = none →
      sa.reg.lvm b = ⟨64, read64 sa.mem a⟩

/-- `ImgRel` is `ImgRelW` where the width analysis is empty. -/
theorem imgRelW_of {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} (h : ImgRel frame slotArr base body s sa zf) :
    ImgRelW frame slotArr base body s sa zf :=
  ⟨h.pc, h.regs, h.slots, h.zf, h.cf, h.of, fun r hr _ => h.wid r hr, h.cells, h.saved,
    h.reload⟩

/-- `ImgRelW` is `ImgRel` where the width analysis is empty. -/
theorem imgRel_of_W {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} (h : ImgRelW frame slotArr base body s sa zf)
    (hW : oneBitAt frame body sa.reg.lpc = []) : ImgRel frame slotArr base body s sa zf :=
  ⟨h.pc, h.regs, h.slots, h.zf, h.cf, h.of, fun r hr => h.wid r hr (by rw [hW]; simp),
    h.cells, h.saved, h.reload⟩

/-! ## 3. Facts of the gate -/

theorem imgGateBW_last {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW frame slotArr body = true) :
    ∃ r, body.getLast? = some r ∧ r.li_i = .Lret := by
  simp only [imgGateBW, Bool.and_eq_true] at h
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
theorem imgGateBW_at {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW frame slotArr body = true) {k : Nat} {i : Linstr} (hi : body[k]? = some i)
    (hr : i.li_i ≠ .Lret) :
    k + 1 < body.length ∧ instrGateBW frame slotArr body k i.li_i = true := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have hk1 : k + 1 < body.length := by
    by_contra hc
    have he : k = body.length - 1 := by omega
    obtain ⟨r, hr', hret⟩ := imgGateBW_last h
    rw [List.getLast?_eq_getElem?, ← he, hi] at hr'
    cases hr'
    exact hr hret
  refine ⟨hk1, ?_⟩
  simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.1 k (by omega)
  rw [hi] at this
  simpa using this

/-- The register a save copies has no frame word. -/
theorem save_frameW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (h : imgGateBW frame slotArr body = true)
    {k : Nat} {R : String} (hs : SaveAt body k R) {A : String} {n : Nat}
    (hA : slotArr (slotOfReg R) = some (A, n)) : frame R = none := by
  obtain ⟨i, hi, hm⟩ := hs
  have hnr : i.li_i ≠ .Lret := by
    intro e; rw [e] at hm; cases hm
  obtain ⟨-, hg⟩ := imgGateBW_at h hi hnr
  obtain ⟨a, ha⟩ := hsep.slotFrame _ _ _ hA
  cases hR : frame R with
  | none => rfl
  | some a' =>
      exfalso
      rcases slotMov?_cases hm with hx | hx <;>
      · rw [hx] at hg
        simp [instrGateBW, gateAtW, carryI?, icase, slotMov?, ha, hR] at hg

/-- At an indexed access whose pointer register was reloaded from the frame word of an
    array, the pointer register holds the base of the array. -/
theorem ptr_of_reloadW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateBW frame slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {b A : String} {n : Nat}
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n)) (hbf : frame b = none) :
    ∃ q, slotArr q = some (A, n) ∧ sa.reg.getW b 64 = some (base A) := by
  obtain ⟨k', hk', i, q, hi, hm, hq⟩ := accArr_spec hacc
  obtain ⟨a, ha⟩ := hsep.slotFrame q A n hq
  have hrl := hrel.reload b q a i (by omega) (by rw [hk', Nat.add_sub_cancel]; exact hi) hm ha hbf
  have hrs : reloadSavedB slotArr body = true := by
    simp only [imgGateBW, Bool.and_eq_true] at hgate; exact hgate.2
  obtain ⟨j, R, hj, hS, hqR⟩ := reloadSavedB_spec hrs hi hm (by rw [hq]; rfl)
  subst hqR
  have hp := (hrel.saved j R A n a hS hq ha).1 (by omega)
  refine ⟨slotOfReg R, hq, ?_⟩
  rw [getW_eq, hrl]
  simp [castW, hp]

/-- A step at an instruction that is no move, advancing the program counter and keeping the
    frame words of the array pointers, keeps the save and reload components of the
    relation. -/
theorem saved_reload_nextW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa sa' : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hnm : slotMov? bi.li_i = none)
    (hpc : sa'.reg.lpc = sa.reg.lpc + 1)
    (hmem : ∀ q a, (slotArr q).isSome = true → frame q = some a →
      read64 sa'.mem a = read64 sa.mem a) :
    (∀ k R A n a, SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
      frame (slotOfReg R) = some a →
        (k < sa'.reg.lpc → read64 sa'.mem a = base A)
          ∧ (sa'.reg.lpc ≤ k → sa'.reg.getW R 64 = some (base A)))
    ∧ (∀ b q a i, 1 ≤ sa'.reg.lpc → body[sa'.reg.lpc - 1]? = some i →
      slotMov? i.li_i = some (b, q) → frame q = some a → frame b = none →
        sa'.reg.lvm b = ⟨64, read64 sa'.mem a⟩) := by
  refine ⟨fun k R A n a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩, fun b q a i _ hbi hm _ _ => ?_⟩
  · rw [hmem _ a (by rw [hA]; rfl) ha]
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

theorem regGateBW_slotMov {frame : String → Option (BitVec 64)} {W : List String}
    {x : LinstrR} (h : regGateBW frame W x = true) {d src : String}
    (hm : slotMov? x = some (d, src)) : frame d = none ∧ frame src = none := by
  simp only [regGateBW, regOkB, Bool.and_eq_true] at h
  have h1 := h.1.1.1.2
  rw [hm] at h1
  simpa using h1

/-! ## 4. Register instructions -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (baseOf fstepA_of_reg)

/-- **A register instruction at mixed width.** `ImageAddrSim.reg_step` with the width
    condition on the names outside `W`: the general-purpose names outside `regOut W x` have
    width `64` after the step. -/
theorem reg_stepW {frame : String → Option (BitVec 64)} {W : List String} {x : LinstrR}
    (hx : IsLopn (x, MemTag.reg none)) (hgate : regGateBW frame W x = true) (P : LprogM)
    (s t : LstateMF) (sa : LstateA) (zf : Bool)
    (hregs : ∀ r, frame r = none → s.prog.base.reg.lvm r = sa.reg.lvm r)
    (hz : s.zf = zf) (hc : sa.cf = s.prog.base.cf) (ho : sa.of = s.prog.base.of)
    (hwid : ∀ r, gpOk r = true → r ∉ W → (sa.reg.lvm r).1 = 64)
    (hs : evalInstrPMemF P (x, .reg none) s = some t) :
    ∃ sa', fstepA frame (x, .reg none) sa zf = some (sa', t.zf) ∧ sa'.mem = sa.mem
      ∧ (∀ r, frame r = none → t.prog.base.reg.lvm r = sa'.reg.lvm r)
      ∧ (∀ r, frame r ≠ none → t.prog.base.reg.lvm r = s.prog.base.reg.lvm r)
      ∧ sa'.cf = t.prog.base.cf ∧ sa'.of = t.prog.base.of
      ∧ sa'.reg.lpc = sa.reg.lpc + 1 ∧ t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1
      ∧ t.prog.base.larr = s.prog.base.larr
      ∧ (∀ r, gpOk r = true → r ∉ regOut W x → (sa'.reg.lvm r).1 = 64) := by
  simp only [regGateBW, Bool.and_eq_true] at hgate
  obtain ⟨hok, hwg⟩ := hgate
  have hsi' : slotImm? frame (x, MemTag.reg none).fst = none := slotImm?_none_of_regOkB hok
  have hsv' : slotCmov? frame (x, MemTag.reg none).fst = none := slotCmov?_none_of_regOkB hok
  simp only [regOkB, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hcell, hsc⟩, hmov⟩, hcmp⟩, hsym⟩ := hok
  have hcell' : cellA? (x, MemTag.reg none).fst = none := Option.isNone_iff_eq_none.1 hcell
  have hsc' : slotCarry? frame (x, MemTag.reg none).fst = none := Option.isNone_iff_eq_none.1 hsc
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
      fun r hr => ?_, hcf, hof, ?_, hlpc, ?_, fun r hr hrW => ?_⟩
    · rw [fstepA_of_reg frame rfl hmov' hcmp' hcell' hsc' hsi' hsv']
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
        · exact wid64WB_ev h1 _ _ _ hwid
      · have e := hkeep' r hw
        simp only at e
        rw [e]
        refine hwid r hr fun hm => hrW ?_
        simp only [regOut, hS, List.mem_filter, hm, true_and]
        simpa using hw

theorem oneBitStep_noCarry {frame : String → Option (BitVec 64)} {W : List String}
    {x : LinstrR} (hci : carryI? x = none) :
    oneBitStep frame W x = match icase frame x with
      | .ldx d _ _ => W.filter (· != d)
      | .sload d _ => W.filter (· != d)
      | .reg =>
          match movImmStruct? x with
          | some (d, _) => d :: W
          | none => regOut W (normA x)
      | _ => W := by
  simp only [oneBitStep, hci]

/-- **A register instruction keeps `ImgRelW`.** -/
theorem rel_regW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateBW frame slotArr body = true) (P : LprogM) {s t : LstateMF}
    {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hc : icase frame bi.li_i = .reg)
    (hci : carryI? bi.li_i = none) (hmi : movImmStruct? bi.li_i = none)
    (hg : regGateBW frame (oneBitAt frame body sa.reg.lpc) (normA bi.li_i) = true)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨ds, o, ss, hx, -, -⟩ := icase_reg hc
  have hl : IsLopn (normA bi.li_i, MemTag.reg none) := by
    rw [hx]; exact ⟨ds, _, ss, rfl⟩
  obtain ⟨sa', hst, hmem, hregs', hkeepF, hcf, hof, hlpcA, hlpcI, hlarr, hwid'⟩ :=
    reg_stepW hl hg P s t sa zf hrel.regs hrel.zf hrel.cf hrel.of hrel.wid hs
  have hmovF : ∀ d src, slotMov? bi.li_i = some (d, src) → frame d = none ∧ frame src = none :=
    fun d src hm => regGateBW_slotMov hg (by rw [slotMov?_normA]; exact hm)
  refine ⟨sa', hst, ⟨?_, hregs', ?_, rfl, hcf, hof, fun r hr hW => hwid' r hr ?_, ?_, ?_, ?_⟩⟩
  · rw [hlpcA, hlpcI, hrel.pc]
  · intro q a ha
    rw [hkeepF q (by rw [ha]; simp), hrel.slots q a ha, hmem]
  · rwa [hlpcA, oneBitAt_succ hb, oneBitStep_noCarry hci, hc, hmi] at hW
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
    · have hR := save_frameW hsep hgate hS hA
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

/-- The flag machine steps the untagged `MOV D, #n` at the one-bit tag by writing the bit `n`
    to `D`. -/
theorem fstepF_bitMov (D : String) (n : Nat) (m : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg D] "MOV" [.imm n], .reg (some 1)) m zf
      = some ((m.setReg D (BitVec.ofNat 1 n)).nextPc, zf) := by
  simp (config := { decide := true }) [fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem,
    lsemStepCast, castStruct?, movImmStruct?, withALUFlags, aluFlagOp?]
  rfl

/-- The untagged immediate move is a register instruction outside the carry chain. -/
theorem icase_movImm (frame : String → Option (BitVec 64)) (D : String) (n : Nat) :
    icase frame (.Lopn [.reg D] "MOV" [.imm n]) = .reg ∧
      carryI? (.Lopn [.reg D] "MOV" [.imm n]) = none := by
  simp (config := { decide := true }) [icase, slotMov?, slotCmp?, carryI?]

/-- **A carry constant keeps `ImgRelW`.** The image and the address machine step the
    untagged `MOV D, #n` at the one-bit tag by writing the bit `n` to `D`, which enters the
    width analysis. -/
theorem rel_bmovW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {D : String} {n : Nat}
    (hx : bi.li_i = .Lopn [.reg D] "MOV" [.imm n]) (hD : frame D = none)
    (hs : evalInstrPMemF P (bi.li_i, .reg (some 1)) s = some t) :
    ∃ sa', fstepA frame (bi.li_i, .reg (some 1)) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hl : IsLopn (bi.li_i, MemTag.reg (some 1)) := by rw [hx]; exact ⟨_, _, _, rfl⟩
  rw [evalInstrPMemF_isLopn P _ s hl, hx, fstepF_bitMov] at hs
  obtain rfl := Option.some.inj hs
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  refine ⟨{ sa with reg := (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc }, ?_, ⟨?_, ?_, ?_, ?_,
    hrel.cf, hrel.of, ?_, ?_, ?_, ?_⟩⟩
  · rw [hx, CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun.fstepA_bitMov, hrel.zf]
  · simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hrel.pc]
  · intro r hr
    by_cases hrD : r = D
    · subst hrD
      simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc]
    · simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hrD, hrel.regs r hr]
  · intro q a ha
    have hqD : q ≠ D := fun e => by rw [e, hD] at ha; cases ha
    simpa [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hqD] using
      hrel.slots q a ha
  · rfl
  · intro r hr hW
    have hpc : (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc = sa.reg.lpc + 1 := by
      simp [LstateN.setReg, LstateN.nextPc]
    rw [hpc, oneBitAt_succ hb, hx] at hW
    obtain ⟨hic, hci⟩ := icase_movImm frame D n
    simp only [oneBitStep, hci, hic, movImmStruct?, List.mem_cons, not_or] at hW
    show ((sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lvm r).1 = 64
    simp only [LstateN.setReg, LstateN.nextPc, if_neg hW.1]
    exact hrel.wid r hr hW.2
  · intro q A m hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A m hq
    exact ⟨arr, h1, h2⟩
  · intro k R A m a hS hA ha
    have hpc : (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc = sa.reg.lpc + 1 := by
      simp [LstateN.setReg, LstateN.nextPc]
    show (k < (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc → _) ∧
      ((sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc ≤ k → _)
    rw [hpc]
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (hrel.saved k R A m a hS hA ha).1 hk
      · exfalso
        obtain ⟨i', hi', hm'⟩ := hS
        rw [hb] at hi'
        cases hi'
        rw [hnm] at hm'
        cases hm'
    · exfalso
      obtain ⟨i', hi', hm'⟩ := hS
      have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
      obtain ⟨d, src, hm, -⟩ := entryRegB_spec hent (show sa.reg.lpc < k by omega) hb
      rw [hnm] at hm
      cases hm
  · intro b q a i hpc hbi hm hq hbf
    have hpc' : (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc = sa.reg.lpc + 1 := by
      simp [LstateN.setReg, LstateN.nextPc]
    rw [hpc', Nat.add_sub_cancel, hb] at hbi
    cases hbi
    rw [hnm] at hm
    cases hm

/-! ## 5. Frame-word moves and compares, indexed accesses, labels -/

/-- **A load of a frame word keeps `ImgRelW`.** -/
theorem rel_sloadW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d q : String} (hc : icase frame bi.li_i = .sload d q)
    (hci : carryI? bi.li_i = none) (hgd : gpOk d = true)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨hm, hd, hq⟩ := icase_sload hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  have hW1 := oneBitAt_succ (frame := frame) hb
  rw [oneBitStep_noCarry hci, hc] at hW1
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
  · intro r hr hW
    simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1] at hW
    by_cases e : r = d
    · subst e; simp
    · simp [e, hrel.wid r hr (not_mem_filter_ne hW e)]
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

/-- **A store into a frame word keeps `ImgRelW`**, for a stored name outside the width
    analysis. -/
theorem rel_sstoreW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {q S : String} (hc : icase frame bi.li_i = .sstore q S)
    (hci : carryI? bi.li_i = none) (hgS : gpOk S = true)
    (hSW : S ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨hm, hS, hq⟩ := icase_sstore hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  have hW1 := oneBitAt_succ (frame := frame) hb
  rw [oneBitStep_noCarry hci, hc] at hW1
  rw [normA_of_slotMov hm] at hs ⊢
  rw [eval_slotMov P hm] at hs
  cases hs
  have hz := hrel.zf
  subst hz
  have hw := hrel.wid S hgS hSW
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
  · intro r hr hW
    simp only [LstateN.lpc_nextPc, hW1] at hW
    simpa using hrel.wid r hr hW
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

/-- **An immediate move into a frame word keeps `ImgRelW`.** The image writes the 64-bit value
    of `v` to the frame-word name `q`, and the address machine stores it at the frame word of
    `q`, which holds no array pointer. -/
theorem rel_stiW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {q : String} {v : Nat} {a : BitVec 64}
    (hx : bi.li_i = .Lopn [.reg q] "MOV:64" [.imm v]) (hq : frame q = some a)
    (hA : slotArr q = none)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hnA : normA bi.li_i = .Lopn [.reg q] "MOV:64" [.imm v] := by
    rw [hx]; simp (config := { decide := true }) [normA]
  rw [hnA] at hs ⊢
  have hl : IsLopn (LinstrR.Lopn [.reg q] "MOV:64" [.imm v], MemTag.reg none) := ⟨_, _, _, rfl⟩
  rw [evalInstrPMemF_isLopn P _ s hl,
    show fstepF (LinstrR.Lopn [.reg q] "MOV:64" [.imm v], MemTag.reg none) s.prog.base s.zf
      = some ((s.prog.base.setReg q (BitVec.ofNat 64 v)).nextPc, s.zf) from
      X86Backend.DecodedLsemStep.fstepF_movII q v s.prog.base s.zf] at hs
  obtain rfl := Option.some.inj hs
  have hz := hrel.zf
  subst hz
  have hW1 := oneBitAt_succ (frame := frame) hb
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  refine ⟨{ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a (BitVec.ofNat 64 v) },
    fstepA_slotImm frame hq v none sa s.zf, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    have e : r ≠ q := fun e => by rw [e, hq] at hr; cases hr
    simp [LstateM.setReg, LstateM.nextPc, e, hrel.regs r hr]
  · intro q' a' ha'
    by_cases e : q' = q
    · subst e
      rw [hq] at ha'
      cases ha'
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, if_true,
        read64_write64_same]
    · simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
        if_false]
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' hq ha' (Ne.symm e))]
      exact hrel.slots q' a' ha'
  · intro r hr hW
    have hci : carryI? bi.li_i = none := by rw [hx]; simp [carryI?]
    have hic : icase frame bi.li_i = .reg := by
      rw [hx]; simp (config := { decide := true }) [icase, slotMov?, slotCmp?]
    have hmi : movImmStruct? bi.li_i = none := by rw [hx]; simp [movImmStruct?]
    simp only [LstateN.lpc_nextPc, hW1, oneBitStep_noCarry hci, hic, hmi, hnA] at hW
    have hrq : r ≠ q := fun e => by
      have h0 := hsep.gp r hr
      rw [e, hq] at h0
      cases h0
    simpa using hrel.wid r hr (regOut_slotImm _ q v hrq hW)
  · intro q' A n hq'
    obtain ⟨arr, h1, h2⟩ := hrel.cells q' A n hq'
    refine ⟨arr, by simpa using h1, fun j hj => ?_⟩
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q' A n j hq' hj q a hq).symm]
    exact h2 j hj
  · intro k R A n a' hS' hA' ha'
    simp only [LstateN.lpc_nextPc]
    have hqR : slotOfReg R ≠ q := fun e => by rw [e, hA] at hA'; cases hA'
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q _ a a' hq ha' (Ne.symm hqR))]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (hrel.saved k R A n a' hS' hA' ha').1 hk
      · exfalso
        obtain ⟨i', hi', hm'⟩ := hS'
        rw [hb] at hi'
        cases hi'
        rw [hnm] at hm'
        cases hm'
    · rw [getW_congr (r := sa.reg.nextPc) (r' := sa.reg) rfl]
      exact (hrel.saved k R A n a' hS' hA' ha').2 (by omega)
  · intro b q' a' i hpc hbi hm' hq' hbf
    simp only [LstateN.lpc_nextPc, Nat.add_sub_cancel, hb] at hbi
    cases hbi
    rw [hnm] at hm'
    cases hm'

/-- The flag machine steps `CMOV:64 D, [C, A, B]`, with `A` at width `64`, by writing the
    select of the one-bit value of `C` between the 64-bit values of `A` and `B` to `D`. -/
theorem fstepF_cmov64 (D C A B : String) (m : LstateM) (zf : Bool) {va : BitVec 64}
    (ha : m.reg.getW A 64 = some va) :
    fstepF (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none) m zf
      = match m.reg.getW C 1, m.reg.getW B 64 with
        | some vc, some vb => some ((m.setReg D (JasminDialect.selectW vc va vb)).nextPc, zf)
        | _, _ => none := by
  cases hc : m.reg.getW C 1 <;> cases hb : m.reg.getW B 64 <;>
    simp (config := { decide := true }) [fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem,
      lsemStepCast, castStruct?, movImmStruct?, lsemStepMC, mulhiStruct?, adcxStruct?,
      adcxhiStruct?, sbbStruct?, sbbhiStruct?, VIR.JasminLsemShift.lsemStepSh,
      VIR.JasminLsemShift.sarStruct?, lsemStepN, readReg_of_getW ha, hb, hc, withALUFlags,
      aluFlagOp?, carryArgs?, wideArgs?, evalOperandN, operandName, LstateM.setReg,
      LstateM.nextPc]

/-- The symbolic step of the select `CMOV:64 D, [C, A, B]` from the start writes `D` only. -/
theorem regOut_cmov (W : List String) (D C A B : String) {r : String} (hr : r ≠ D)
    (h : r ∉ regOut W (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B])) : r ∉ W := by
  intro hW
  apply h
  have hm : stripWidthTag "CMOV:64" = "CMOV" := by decide +kernel
  have hn : ∀ R, symN (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]) R
      = .set D (.sel (R A) (R B) (R C)) [.wid (R C) 1, .eqW (R A) (R B)] := fun R => by
    unfold symN
    simp only [hm, if_true]
  have hd : ∀ R, symMC (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]) R
      = .set D (.sel (R A) (R B) (R C)) [.wid (R C) 1, .eqW (R A) (R B)] := fun R => by
    simp [symMC, symSh, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?,
      VIR.JasminLsemShift.sarStruct?, hn, hm]
  have hs : symStep (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none) SSt.start
      = .ok (SSt.start.setR D (.sel (.reg A) (.reg B) (.reg C)))
        [.wid (.reg C) 1, .eqW (.reg A) (.reg B)] := by
    simp [symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, symMem, symCast,
      castStruct?, movImmStruct?, hd, liftR, aluFl, aluFlT, aluFlagOp?, SSt.start, SSt.setR]
  simp only [regOut, hs]
  simp [SSt.setR, SSt.start, hW, hr]

/-- **A select with a frame-word value keeps `ImgRelW`.** The image reads the values of
    `CMOV:64 D, [C, A, B]` from its names, the address machine reads a frame-word value at
    its frame word; both write the select to `D`. -/
theorem rel_scmovW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {D C A B : String}
    (hx : bi.li_i = .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]) (hD : frame D = none)
    (hC : frame C = none) (hA : gpOk A = true ∨ (frame A).isSome = true)
    (hAW : gpOk A = true → A ∉ oneBitAt frame body sa.reg.lpc)
    (hsl : ((frame A).isSome || (frame B).isSome) = true)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hnA : normA bi.li_i = .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B] := by
    rw [hx]; simp (config := { decide := true }) [normA]
  rw [hnA] at hs ⊢
  have hl : IsLopn (LinstrR.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], MemTag.reg none) :=
    ⟨_, _, _, rfl⟩
  have hcongr : ∀ x, frame x = none → ∀ w, s.prog.base.reg.getW x w = sa.reg.getW x w := by
    intro x hx w
    unfold LstateN.getW
    rw [hrel.regs x hx]
  have hword : ∀ x, wordA frame sa x = s.prog.base.reg.getW x 64 := by
    intro x
    unfold wordA
    split
    · rename_i ad hfa
      rw [getW_eq_some_iff.2 (hrel.slots x ad hfa)]
    · rename_i hfa
      exact (hcongr x hfa 64).symm
  obtain ⟨va, hva⟩ : ∃ v, s.prog.base.reg.getW A 64 = some v := by
    cases hfa : frame A with
    | some ad => exact ⟨_, getW_eq_some_iff.2 (hrel.slots A ad hfa)⟩
    | none =>
      have hgA : gpOk A = true := by
        rcases hA with h | h
        · exact h
        · rw [hfa] at h; cases h
      have hw := hrel.wid A hgA (hAW hgA)
      rw [← hrel.regs A hfa] at hw
      rcases e : s.prog.base.reg.lvm A with ⟨w, v⟩
      rw [e] at hw
      simp only at hw
      subst hw
      exact ⟨v, getW_eq_some_iff.2 e⟩
  rw [evalInstrPMemF_isLopn P _ s hl, fstepF_cmov64 D C A B _ _ hva] at hs
  cases hgc : s.prog.base.reg.getW C 1 with
  | none => rw [hgc] at hs; simp at hs
  | some vc =>
  cases hgb : s.prog.base.reg.getW B 64 with
  | none => rw [hgc, hgb] at hs; simp at hs
  | some vb =>
  rw [hgc, hgb] at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  subst hs
  have hz := hrel.zf
  subst hz
  have hstA := fstepA_slotCmov frame (C := C) hD hsl none sa s.zf (by rw [hword]; exact hva)
    (by rw [hword]; exact hgb)
  rw [← hcongr C hC 1, hgc] at hstA
  simp only [Option.map_some] at hstA
  have hW1 := oneBitAt_succ (frame := frame) hb
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  refine ⟨_, hstA, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    by_cases e : r = D
    · subst e
      simp [LstateM.setReg, LstateM.nextPc]
    · simp [LstateM.setReg, LstateM.nextPc, e, hrel.regs r hr]
  · intro q a ha
    have e : q ≠ D := fun e => by rw [e, hD] at ha; cases ha
    simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
      if_false]
    exact hrel.slots q a ha
  · intro r hr hW
    have hci : carryI? bi.li_i = none := by rw [hx]; simp [carryI?]
    have hic : icase frame bi.li_i = .reg := by
      rw [hx]; simp (config := { decide := true }) [icase, slotMov?, slotCmp?]
    have hmi : movImmStruct? bi.li_i = none := by rw [hx]; simp [movImmStruct?]
    change r ∉ oneBitAt frame body (sa.reg.lpc + 1) at hW
    simp only [hW1, oneBitStep_noCarry hci, hic, hmi, hnA] at hW
    by_cases e : r = D
    · subst e
      simp
    · simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg, e, if_false]
      exact hrel.wid r hr (regOut_cmov _ D C A B e hW)
  · intro q A' n hq'
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq'
    exact ⟨arr, by simpa using h1, h2⟩
  all_goals
    have hsr := saved_reload_nextW
      (sa' := { sa with reg := (sa.reg.setReg D (JasminDialect.selectW vc va vb)).nextPc })
      hphys hrel hb hnm rfl (fun _ _ _ _ => rfl)
  · exact hsr.1
  · exact hsr.2

/-- **A compare against a frame word keeps `ImgRelW`.** -/
theorem rel_scmpW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d y q : String} (hc : icase frame bi.li_i = .scmp d y q)
    (hci : carryI? bi.li_i = none) (hy : frame y = none)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨hk, hq⟩ := icase_scmp hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  have hW1 := oneBitAt_succ (frame := frame) hb
  rw [oneBitStep_noCarry hci, hc] at hW1
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
    obtain ⟨hsv, hrl⟩ := saved_reload_nextW (sa' := { sa with reg := sa.reg.nextPc }) hphys hrel
      hb hnm rfl (fun _ _ _ _ => rfl)
    refine ⟨{ sa with reg := sa.reg.nextPc }, rfl, ⟨by simp [LstateM.nextPc, hrel.pc],
      fun r hr => by simpa [LstateM.nextPc] using hrel.regs r hr,
      fun q' a' ha' => by simpa [LstateM.nextPc] using hrel.slots q' a' ha', rfl, hrel.cf,
      hrel.of, fun r hr hW => ?_,
      fun q' A n hq' => by simpa using hrel.cells q' A n hq', hsv, hrl⟩⟩
    simp only [LstateN.lpc_nextPc, hW1] at hW
    simpa using hrel.wid r hr hW

/-- **An indexed load keeps `ImgRelW`**, and reads outside the red-zone word. -/
theorem rel_ldxW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateBW frame slotArr body = true) (P : LprogM) {s t : LstateMF}
    {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d b idx A : String} {n : Nat}
    (hx : bi.li_i = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx 8])
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n)) (hgd : gpOk d = true)
    (hd : frame d = none) (hidx : frame idx = none) (hbf : frame b = none)
    (hs : evalInstrPMemFk true P (.Lopn [.reg d] "LOADIDX" [.arrIdx A idx 8], .load 64 n) s
      = some t) :
    LoadSafeAt rsp body sa ∧ ∃ sa', fstepA frame (bi.li_i, .load 64 0) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hW1 := oneBitAt_succ (frame := frame) hb
  rw [oneBitStep_noCarry (by rw [hx]; rfl), hx, icase_loadIdx] at hW1
  have hok := idxOkB_of_checked hs
  have hs' := evalInstrPMemF_of_k hs
  obtain ⟨q, hq, hp⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
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
  obtain ⟨hsv, hrl⟩ := saved_reload_nextW (sa' := { sa with reg := (sa.reg.setReg d
      (read64 sa.mem (base A + BitVec.ofNat 64 (8 * vi.toNat)))).nextPc })
    hphys hrel hb (by rw [hx]; rfl) (by simp) (fun _ _ _ _ => rfl)
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
  · intro r hr hW
    simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1] at hW
    by_cases e : r = d
    · subst e; simp
    · simp [e, hrel.wid r hr (not_mem_filter_ne hW e)]

/-- **An indexed store keeps `ImgRelW`.** -/
theorem rel_stxW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateBW frame slotArr body = true) (P : LprogM) {s t : LstateMF}
    {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d b idx v A : String} {n : Nat}
    (hx : bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v])
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n))
    (hidx : frame idx = none) (hbf : frame b = none) (hv : frame v = none)
    (hs : evalInstrPMemFk true P
      (.Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v], .store 64 n) s = some t) :
    ∃ sa', fstepA frame (bi.li_i, .store 64 0) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hW1 := oneBitAt_succ (frame := frame) hb
  rw [oneBitStep_noCarry (by rw [hx]; rfl), hx] at hW1
  have hok := idxOkB_of_checked hs
  have hs' := evalInstrPMemF_of_k hs
  obtain ⟨q, hq, hp⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
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
  obtain ⟨hsv, hrl⟩ := saved_reload_nextW (sa' := { sa with
      reg := sa.reg.nextPc
      mem := write64 sa.mem (base A + BitVec.ofNat 64 (8 * vi.toNat)) vv })
    hphys hrel hb (by rw [hx]; rfl) rfl
    (fun q' a _ ha => read64_write64_of_disjoint _ _ _ _
      (hsep.cellFrame q A n vi.toNat hq hlt q' a ha))
  refine ⟨_, rfl, ⟨by simp [LstateM.setArr, LstateM.nextPc, hrel.pc],
    fun r hr => by simpa [LstateM.setArr, LstateM.nextPc] using hrel.regs r hr, ?_, rfl,
    hrel.cf, hrel.of, fun r hr hW => ?_, ?_, hsv, hrl⟩⟩
  · intro q' a ha
    simp only [LstateM.setArr, LstateM.nextPc, LstateN.lvm_nextPc]
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q A n vi.toNat hq hlt q' a ha)]
    exact hrel.slots q' a ha
  · simp only [LstateN.lpc_nextPc, hW1] at hW
    simpa using hrel.wid r hr (by simpa [icase] using hW)
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

/-- **A label keeps `ImgRelW`.** -/
theorem rel_labelW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {ii : _} {l : LLabel} (hx : bi.li_i = .Llabel ii l) :
    ImgRelW frame slotArr base body
      { s with prog := { s.prog with base := s.prog.base.nextPc } }
      (sa.setLpc (sa.reg.lpc + 1)) zf := by
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  have hW1 := oneBitAt_succ (frame := frame) hb
  rw [oneBitStep_noCarry (by rw [hx]; rfl), hx] at hW1
  obtain ⟨hsv, hrl⟩ := saved_reload_nextW (sa' := sa.setLpc (sa.reg.lpc + 1)) hphys hrel hb
    hnm rfl (fun _ _ _ _ => rfl)
  refine ⟨by simp [LstateA.setLpc, LstateM.nextPc, hrel.pc], fun r hr => hrel.regs r hr,
    fun q a ha => hrel.slots q a ha, hrel.zf, hrel.cf, hrel.of, fun r hr hW => ?_,
    fun q A n hq => hrel.cells q A n hq, hsv, hrl⟩
  simp only [LstateA.setLpc] at hW ⊢
  rw [hW1] at hW
  exact hrel.wid r hr (by simpa [icase] using hW)

/-! ## 6. Carry-chain instructions -/

/-- A word source of a carry-chain instruction, a general-purpose name outside the width
    analysis or a frame slot, reads one 64-bit word on the image and on the address
    machine. -/
theorem word_virt {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) {s : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {A : String}
    (hk : gpOk A = true ∨ (frame A).isSome = true)
    (hw : gpOk A = true → A ∉ oneBitAt frame body sa.reg.lpc) :
    ∃ va, s.prog.base.reg.getW A 64 = some va ∧ wordA frame sa A = some va := by
  rcases hk with hg | hs
  · have hf := hsep.gp A hg
    have hw' := hrel.wid A hg (hw hg)
    refine ⟨castW (sa.reg.lvm A) 64, ?_, ?_⟩
    · rw [getW_congr (hrel.regs A hf), getW_eq, if_pos hw']
    · simp only [wordA, hf]
      rw [getW_eq, if_pos hw']
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    refine ⟨read64 sa.mem a, ?_, by simp [wordA, ha]⟩
    rw [getW_eq, hrel.slots A a ha]
    simp [castW]

theorem oneBitStep_adcx (frame : String → Option (BitVec 64)) (W : List String)
    (D A S C : String) :
    oneBitStep frame W (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]) = W.filter (· != D) :=
  by simp [oneBitStep, carryI?]

theorem oneBitStep_adcxhi (frame : String → Option (BitVec 64)) (W : List String)
    (O A S C : String) :
    oneBitStep frame W (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]) = O :: W := by
  simp (config := { decide := true }) [oneBitStep, carryI?]

/-- **`ADCX:64` keeps `ImgRelW`**: the add with register or frame-slot word sources and a
    register carry-in, into a register or into a frame slot that holds no array pointer. -/
theorem rel_adcxW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {D A S C : String}
    (hx : bi.li_i = .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C])
    (hok : carryOkB frame slotArr false D A S C = true)
    (hAW : gpOk A = true → A ∉ oneBitAt frame body sa.reg.lpc)
    (hSW : gpOk S = true → S ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  simp only [carryOkB, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none,
    Bool.false_eq_true, if_false] at hok
  obtain ⟨⟨⟨⟨⟨⟨hfC, -⟩, hAk⟩, hSk⟩, hDk⟩, -⟩, -⟩ := hok
  have hW1 := oneBitAt_succ (frame := frame) hb
  rw [hx, oneBitStep_adcx] at hW1
  obtain ⟨va, hvA, hwA⟩ := word_virt hsep hrel hAk hAW
  obtain ⟨vb, hvS, hwS⟩ := word_virt hsep hrel hSk hSW
  have hC := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regs C hfC) 1
  have hl : IsLopn (bi.li_i, MemTag.reg none) := by rw [hx]; exact ⟨_, _, _, rfl⟩
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  rw [evalInstrPMemF_isLopn P _ s hl, hx, fstepF_adcx D A S C _ _ hvA hvS, hC] at hs
  have hz := hrel.zf
  subst hz
  cases hgc : sa.reg.getW C 1 with
  | none => rw [hgc] at hs; cases hs
  | some vc =>
  rw [hgc] at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  subst hs
  cases hfD : frame D with
  | some aD =>
    have hDs : slotArr D = none := by
      rcases hDk with hg | ⟨-, h2⟩
      · rw [hsep.gp D hg] at hfD; cases hfD
      · exact h2
    have hst : fstepA frame (bi.li_i, .reg none) sa s.zf = some ({ sa with
        reg := sa.reg.nextPc
        mem := write64 sa.mem aD (VIR.JasminDialect.addCarryWord va vb vc) }, s.zf) := by
      rw [hx, fstepA_adcxSlot frame D A S C sa s.zf (by simp [hfD]) hwA hwS, hgc]
      simp [hfD]
    refine ⟨_, hst, ?_⟩
    obtain ⟨hsv, hrl⟩ := saved_reload_nextW (sa' := { sa with
        reg := sa.reg.nextPc
        mem := write64 sa.mem aD (VIR.JasminDialect.addCarryWord va vb vc) })
      hphys hrel hb hnm rfl (fun q a hq ha => read64_write64_of_disjoint _ _ _ _
        (hsep.frames D q aD a hfD ha (fun e => by rw [← e, hDs] at hq; cases hq)))
    refine ⟨by simp [hrel.pc], fun r hr => ?_,
      fun q a ha => ?_, rfl, hrel.cf, hrel.of, fun r hr hW => ?_, fun q A' n hq => ?_, hsv,
      hrl⟩
    · have e : r ≠ D := fun e => by rw [e, hfD] at hr; cases hr
      simp [e, hrel.regs r hr]
    · by_cases e : q = D
      · subst e
        rw [hfD] at ha
        cases ha
        simp [read64_write64_same]
      · simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg, e, if_false]
        rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames D q aD a hfD ha (Ne.symm e))]
        exact hrel.slots q a ha
    · have e : r ≠ D := fun e => by subst e; rw [hsep.gp r hr] at hfD; cases hfD
      simp only [LstateN.lpc_nextPc, hW1] at hW
      simpa using hrel.wid r hr (not_mem_filter_ne hW e)
    · obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq
      refine ⟨arr, (getArr_congr rfl _ _ _).trans h1, fun j hj => ?_⟩
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q A' n j hq hj D aD hfD).symm]
      exact h2 j hj
  | none =>
    have hDg : gpOk D = true := by
      rcases hDk with hg | ⟨h1, -⟩
      · exact hg
      · rw [hfD] at h1; cases h1
    have hst : fstepA frame (bi.li_i, .reg none) sa s.zf = some ({ sa with
        reg := (sa.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc }, s.zf) := by
      by_cases hsl : ((frame A).isSome || (frame S).isSome) = true
      · rw [hx, fstepA_adcxSlot frame D A S C sa s.zf (by simp [hfD, hsl]) hwA hwS, hgc]
        simp [hfD]
      · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
          Option.isNone_iff_eq_none] at hsl
        obtain ⟨hfA, hfS⟩ := hsl
        simp only [wordA, hfA, hfS] at hwA hwS
        rw [hx, fstepA_adcx3 frame D A S C sa s.zf hfD hfA hfS hwA hwS, hgc]
        rfl
    refine ⟨_, hst, ?_⟩
    obtain ⟨hsv, hrl⟩ := saved_reload_nextW (sa' := { sa with
        reg := (sa.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc })
      hphys hrel hb hnm (by simp) (fun _ _ _ _ => rfl)
    refine ⟨by simp [hrel.pc], fun r hr => ?_,
      fun q a ha => ?_, rfl, hrel.cf, hrel.of, fun r hr hW => ?_, fun q A' n hq => ?_, hsv, hrl⟩
    · by_cases e : r = D
      · subst e; simp
      · simp [e, hrel.regs r hr]
    · have e : q ≠ D := fun e => by rw [e, hfD] at ha; cases ha
      simp [e, hrel.slots q a ha]
    · simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1] at hW
      by_cases e : r = D
      · subst e; simp
      · simp [e, hrel.wid r hr (not_mem_filter_ne hW e)]
    · obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq
      exact ⟨arr, (getArr_congr rfl _ _ _).trans h1, h2⟩

/-- **`ADCXHI:64` keeps `ImgRelW`**: the carry-out binding with register or frame-slot word
    sources and a register carry-in into a register, which enters the width analysis. -/
theorem rel_adcxhiW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {O A S C : String}
    (hx : bi.li_i = .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C])
    (hok : carryOkB frame slotArr true O A S C = true)
    (hAW : gpOk A = true → A ∉ oneBitAt frame body sa.reg.lpc)
    (hSW : gpOk S = true → S ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  simp only [carryOkB, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none,
    if_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hfC, -⟩, hAk⟩, hSk⟩, -, hfO⟩, -⟩, -⟩ := hok
  have hW1 := oneBitAt_succ (frame := frame) hb
  rw [hx, oneBitStep_adcxhi] at hW1
  obtain ⟨va, hvA, hwA⟩ := word_virt hsep hrel hAk hAW
  obtain ⟨vb, hvS, hwS⟩ := word_virt hsep hrel hSk hSW
  have hC := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regs C hfC) 1
  have hl : IsLopn (bi.li_i, MemTag.reg none) := by rw [hx]; exact ⟨_, _, _, rfl⟩
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  rw [evalInstrPMemF_isLopn P _ s hl, hx, fstepF_adcxhi O A S C _ _ hvA hvS, hC] at hs
  have hz := hrel.zf
  subst hz
  cases hgc : sa.reg.getW C 1 with
  | none => rw [hgc] at hs; cases hs
  | some vc =>
  rw [hgc] at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  subst hs
  have hst : fstepA frame (bi.li_i, .reg none) sa s.zf = some ({ sa with
      reg := (sa.reg.setReg O (VIR.JasminDialect.carryOutBit va vb vc)).nextPc }, s.zf) := by
    by_cases hsl : ((frame A).isSome || (frame S).isSome) = true
    · rw [hx, fstepA_adcxhiSlot frame O A S C sa s.zf (by simp [hfO, hsl]) hwA hwS, hgc]
      rfl
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none] at hsl
      obtain ⟨hfA, hfS⟩ := hsl
      simp only [wordA, hfA, hfS] at hwA hwS
      rw [hx, fstepA_adcxhi frame O A S C sa s.zf hfO hfA hfS hwA hwS, hgc]
      rfl
  refine ⟨_, hst, ?_⟩
  obtain ⟨hsv, hrl⟩ := saved_reload_nextW (sa' := { sa with
      reg := (sa.reg.setReg O (VIR.JasminDialect.carryOutBit va vb vc)).nextPc })
    hphys hrel hb hnm (by simp) (fun _ _ _ _ => rfl)
  refine ⟨by simp [hrel.pc], fun r hr => ?_,
    fun q a ha => ?_, rfl, hrel.cf, hrel.of, fun r hr hW => ?_, fun q A' n hq => ?_, hsv, hrl⟩
  · by_cases e : r = O
    · subst e; simp
    · simp [e, hrel.regs r hr]
  · have e : q ≠ O := fun e => by rw [e, hfO] at ha; cases ha
    simp [e, hrel.slots q a ha]
  · simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1, List.mem_cons, not_or] at hW
    simp [hW.1, hrel.wid r hr hW.2]
  · obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq
    exact ⟨arr, (getArr_congr rfl _ _ _).trans h1, h2⟩

/-! ## 7. One step of the image -/

/-- **One step of the image at a position without a branch.** From states related by
    `ImgRelW`, a checked step of the image of a body that passes `imgGateBW` is matched by one
    step of the address machine, which does not halt and reads outside the red-zone word. -/
theorem img_stepW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr c = true)
    (hgate : imgGateBW frame slotArr c = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base c s sa s.zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hnc : ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    haltedA c sa = false ∧ LoadSafeAt rsp c sa
      ∧ ∃ sa1, stepA frame c sa s.zf = some (sa1, t.zf)
        ∧ ImgRelW frame slotArr base c t sa1 t.zf := by
  have hg : instrGateBW frame slotArr c sa.reg.lpc bi.li_i = true := by
    simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  simp only [instrGateBW, gateAtW, Bool.and_eq_true] at hg
  obtain ⟨hrd, hg⟩ := hg
  cases hci : carryI? bi.li_i with
  | some p =>
    obtain ⟨hi, d, a, s', cc⟩ := p
    rw [hci] at hg
    have hx0 := carryI?_eq hci
    have hok := hg
    simp only [carryOkB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨-, hac⟩, hsc⟩ := hok
    have hcI : carryIns bi.li_i = [cc] := by
      rw [hx0]; cases hi <;> simp [carryIns]
    have hAW : gpOk a = true → a ∉ oneBitAt frame c sa.reg.lpc := fun hgA =>
      readOkB_spec hrd (by rw [hx0]; simp [readNames, srcNames]) hgA
        (by rw [hcI]; simpa using hac)
    have hSW : gpOk s' = true → s' ∉ oneBitAt frame c sa.reg.lpc := fun hgS =>
      readOkB_spec hrd (by rw [hx0]; simp [readNames, srcNames]) hgS
        (by rw [hcI]; simpa using hsc)
    have hld : (if hi then "ADCXHI:64" else "ADCX:64") ≠ "LOADIDX" := by cases hi <;> decide
    have hsd : (if hi then "ADCXHI:64" else "ADCX:64") ≠ "STOREIDX" := by cases hi <;> decide
    have hnA : normA bi.li_i = bi.li_i := by
      rw [hx0]; cases hi <;> simp (config := { decide := true }) [normA]
    have hsafe := loadSafe_of (rsp := rsp) hb (by
      intro D B I e; rw [hx0] at e; cases hi <;> simp at e)
    have hnr : bi.li_i ≠ .Lret := by rw [hx0]; simp
    have h3 : bitMovB c sa.reg.lpc (.Lopn [.reg d] (if hi then "ADCXHI:64" else "ADCX:64")
        [.reg a, .reg s', .reg cc]) = false :=
      bitMovB_of_ne (by cases hi <;> simp [movImmStruct?])
    rw [hx0, imgInstr_reg slotArr c _ hld hsd h3, evalInstrPMemFk_reg, ← hx0, hnA] at hstep
    have hstepA : stepA frame c sa s.zf = fstepA frame (bi.li_i, .reg none) sa s.zf := by
      rw [stepA_lopn frame hb hx0, hnA, hx0, tagAt_reg hld hsd h3]
    obtain ⟨sa', hst, hr⟩ : ∃ sa', fstepA frame (bi.li_i, .reg none) sa s.zf = some (sa', t.zf)
        ∧ ImgRelW frame slotArr base c t sa' t.zf := by
      cases hi
      · exact rel_adcxW hsep hphys P hrel hb (by simpa using hx0) hg hAW hSW hstep
      · exact rel_adcxhiW hsep hphys P hrel hb (by simpa using hx0) hg hAW hSW hstep
    exact ⟨haltedA_of hb hnr, hsafe, sa', by rw [hstepA, hst], hr⟩
  | none =>
    rw [hci] at hg
    cases hc : icase frame bi.li_i with
    | other => rw [hc] at hg; cases hg
    | cond cc l => exact absurd (icase_cond hc) (hnc (.reg cc) l)
    | label =>
        obtain ⟨ii, l, hx⟩ := icase_label hc
        have hi : imgInstr slotArr c sa.reg.lpc bi.li_i = (bi.li_i, .reg none) := by
          rw [hx]; rfl
        rw [hi, evalInstrPMemFk_reg, hx, eval_label] at hstep
        cases hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp),
          sa.setLpc (sa.reg.lpc + 1), ?_, rel_labelW hphys hrel hb hx⟩
        obtain ⟨ii0, li⟩ := bi
        simp only at hx
        subst hx
        simp [stepA, hb]
    | ldx d b idx =>
        rw [hc] at hg
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
        obtain ⟨⟨⟨⟨⟨An, hacc⟩, hgd⟩, hd⟩, hidx⟩, hbf⟩ := hg
        obtain ⟨A, n⟩ := An
        have hx := icase_ldx hc
        rw [hx, imgInstr_ldx slotArr c _ hacc] at hstep
        obtain ⟨hsafe, sa', hst, hr⟩ :=
          rel_ldxW hsep hphys hgate P hrel hb hx hacc hgd hd hidx hbf hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
        rw [stepA_lopn frame hb hx, ← hst, hx]
        rfl
    | stx d b idx v =>
        rw [hc] at hg
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
        obtain ⟨⟨⟨⟨An, hacc⟩, hidx⟩, hbf⟩, hv⟩ := hg
        obtain ⟨A, n⟩ := An
        have hx := icase_stx hc
        rw [hx, imgInstr_stx slotArr c _ hacc] at hstep
        obtain ⟨sa', hst, hr⟩ := rel_stxW hsep hphys hgate P hrel hb hx hacc hidx hbf hv hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), sa', ?_,
          hr⟩
        rw [stepA_lopn frame hb hx, ← hst, hx]
        rfl
    | sload d q =>
        rw [hc] at hg
        have hm := (icase_sload hc).1
        have hsafe := loadSafe_of (rsp := rsp) hb
          (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
        have h3 : bitMovB c sa.reg.lpc bi.li_i = false := bitMovB_of_slotMov hm
        rcases slotMov?_cases hm with hx | hx <;>
        · rw [hx] at h3
          rw [hx, imgInstr_reg slotArr c _ (by decide) (by decide) h3, evalInstrPMemFk_reg,
            ← hx] at hstep
          obtain ⟨sa', hst, hr⟩ := rel_sloadW hphys P hrel hb hc hci hg hstep
          refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
          rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg (by decide) (by decide) h3]
    | sstore q S =>
        rw [hc] at hg
        have hm := (icase_sstore hc).1
        have hsafe := loadSafe_of (rsp := rsp) hb
          (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
        have h3 : bitMovB c sa.reg.lpc bi.li_i = false := bitMovB_of_slotMov hm
        rcases slotMov?_cases hm with hx | hx <;>
        · have hSW := readOkB_spec hrd (by rw [hx]; simp [readNames, srcNames]) hg
            (by rw [hx]; simp [carryIns])
          rw [hx] at h3
          rw [hx, imgInstr_reg slotArr c _ (by decide) (by decide) h3, evalInstrPMemFk_reg,
            ← hx] at hstep
          obtain ⟨sa', hst, hr⟩ := rel_sstoreW hsep hphys P hrel hb hc hci hg hSW hstep
          refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
          rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg (by decide) (by decide) h3]
    | scmp d y q =>
        rw [hc] at hg
        have hx := slotCmp?_eq (icase_scmp hc).1
        have hsafe := loadSafe_of (rsp := rsp) hb
          (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
        have h3 : bitMovB c sa.reg.lpc (.Lopn [.reg d] "CMP:64" [.reg y, .reg q]) = false :=
          bitMovB_of_ne (by simp [movImmStruct?])
        rw [hx, imgInstr_reg slotArr c _ (by decide) (by decide) h3, evalInstrPMemFk_reg,
          ← hx] at hstep
        obtain ⟨sa', hst, hr⟩ := rel_scmpW hphys P hrel hb hc hci (by simpa using hg) hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
        rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg (by decide) (by decide) h3]
    | reg =>
        rw [hc] at hg
        obtain ⟨ds, o, ss, hx, ho1, ho2⟩ := icase_reg hc
        have hsafe := loadSafe_of (rsp := rsp) hb
          (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
        cases hmi : movImmStruct? bi.li_i with
        | some p =>
          -- a carry constant
          obtain ⟨D, n⟩ := p
          rw [hmi] at hg
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
          obtain ⟨⟨hbit, -⟩, hD⟩ := hg
          obtain ⟨D', n', hx', -, -, -⟩ := bitMovB_spec hbit
          have hDD : D' = D := by
            rw [hx'] at hmi
            simp only [movImmStruct?, Option.some.injEq, Prod.mk.injEq] at hmi
            exact hmi.1
          subst hDD
          have hbit' := hbit
          rw [hx'] at hbit'
          have hi : imgInstr slotArr c sa.reg.lpc bi.li_i = (bi.li_i, .reg (some 1)) := by
            rw [hx']
            simp [imgInstr, tagAt, hbit', normA]
          rw [hi] at hstep
          have hstep' : evalInstrPMemF P (bi.li_i, .reg (some 1)) s = some t := by
            simpa [evalInstrPMemFk, idxOkB] using hstep
          obtain ⟨sa', hst, hr⟩ := rel_bmovW hphys P hrel hb hx' hD hstep'
          refine ⟨haltedA_of hb (by rw [hx']; simp), hsafe, sa', ?_, hr⟩
          rw [stepA_lopn frame hb hx', ← hst, hx']
          simp [tagAt, hbit', normA]
        | none =>
          rw [hmi] at hg
          have h3 : bitMovB c sa.reg.lpc bi.li_i = false := bitMovB_of_ne hmi
          rw [hx] at h3
          rw [hx, imgInstr_reg slotArr c _ ho1 ho2 h3, evalInstrPMemFk_reg, ← hx] at hstep
          obtain ⟨sa', hst, hr⟩ : ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa s.zf
              = some (sa', t.zf) ∧ ImgRelW frame slotArr base c t sa' t.zf := by
            cases hsi : sImmB frame slotArr bi.li_i with
            | true =>
              -- an immediate move into a frame word
              obtain ⟨q, v, a, hx', hq, hA⟩ := sImmB_spec hsi
              exact rel_stiW hsep P hrel hb hx' hq hA hstep
            | false =>
              cases hsv : sCmovB frame bi.li_i with
              | true =>
                -- a select with a frame-word value
                obtain ⟨D, C, A, B, hx', hD, hC, hA, hAC, hsl⟩ := sCmovB_spec hsv
                have hAW : gpOk A = true → A ∉ oneBitAt frame c sa.reg.lpc := fun hgA =>
                  readOkB_spec hrd (by rw [hx']; simp [readNames, srcNames]) hgA
                    (by rw [hx']; simp [carryIns, hAC])
                exact rel_scmovW hphys P hrel hb hx' hD hC hA hAW hsl hstep
              | false =>
                have hg' : regGateBW frame (oneBitAt frame c sa.reg.lpc) (normA bi.li_i)
                    = true := by
                  simpa [hsi, hsv] using hg
                exact rel_regW hsep hphys hgate P hrel hb hc hci hmi hg' hstep
          refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
          rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg ho1 ho2 h3]

/-! ## 8. Halting, the read widths, and the frame -/

/-- Where the image halts, the address machine has halted: the program counter is at the
    final return of the body or past its end. -/
theorem haltedA_of_imgW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hgate : imgGateBW frame slotArr body = true) (fn : String) {s : LstateMF}
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
  · obtain ⟨r, hr, hret⟩ := imgGateBW_last hgate
    have he : sa.reg.lpc = body.length - 1 := by omega
    rw [List.getLast?_eq_getElem?, ← he] at hr
    rw [hr]
    obtain ⟨ii, li⟩ := r
    simp only at hret
    subst hret
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-- **The read widths.** Under `ImgRelW` at a body passing `imgGateBW`, no general-purpose
    name the instruction at the program counter reads, other than a carry-in, holds a one-bit
    value. -/
theorem wideSafe_of_gateW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hgate : imgGateBW frame slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) : WideSafeAt body sa := by
  intro ii ds o ss hb r hr hg hc
  obtain ⟨-, hgk⟩ := imgGateBW_at hgate hb (by simp)
  simp only [instrGateBW, gateAtW, Bool.and_eq_true] at hgk
  have hmem : r ∈ readNames (.Lopn ds o ss) := by
    rcases hr with rfl | rfl | hr' | hr'
    · exact absurd hg (by decide)
    · simp [readNames]
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hr')
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hr')
  have := hrel.wid r hg (readOkB_spec hgk.1 hmem hg hc)
  omega

section Congr

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (icase_congr regOkB_congr)

variable {frame frame' : String → Option (BitVec 64)}

theorem oneBitStep_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (W : List String)
    (x : LinstrR) : oneBitStep frame W x = oneBitStep frame' W x := by
  simp only [oneBitStep, icase_congr h]

theorem oneBitAt_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (body : Lcmd)
    (k : Nat) : oneBitAt frame body k = oneBitAt frame' body k := by
  simp only [oneBitAt, oneBitStep_congr h]

theorem regGateBW_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (W : List String)
    (x : LinstrR) : regGateBW frame W x = regGateBW frame' W x := by
  simp only [regGateBW, regOkB_congr h]

theorem sImmB_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome)
    (slotArr : String → Option (String × Nat)) (x : LinstrR) :
    sImmB frame slotArr x = sImmB frame' slotArr x := by
  unfold sImmB
  split <;> simp only [h]

theorem sCmovB_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (x : LinstrR) :
    sCmovB frame x = sCmovB frame' x := by
  have hn : ∀ q, (frame q).isNone = (frame' q).isNone := fun q => by
    have := h q; cases e : frame q <;> cases e' : frame' q <;> simp_all
  unfold sCmovB
  split <;> simp only [h, hn]

/-- `imgGateBW` reads only which names have a frame word. -/
theorem imgGateBW_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome)
    (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    imgGateBW frame slotArr body = imgGateBW frame' slotArr body := by
  have hn : ∀ q, (frame q).isNone = (frame' q).isNone := fun q => by
    have := h q; cases e : frame q <;> cases e' : frame' q <;> simp_all
  have hi : ∀ k x, instrGateBW frame slotArr body k x = instrGateBW frame' slotArr body k x := by
    intro k x
    simp only [instrGateBW, gateAtW, carryOkB, oneBitAt_congr h, icase_congr h,
      regGateBW_congr h, sImmB_congr h, sCmovB_congr h, hn, h]
  simp only [imgGateBW, hi]

end Congr

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
