/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.NarrowTyping

@[expose] public section

set_option autoImplicit false

/-!
# The image simulation with carry chains

`ImageAddrSim.ImgRel` gives every general-purpose name the width `64`. A carry chain reads its
carry-in at width `1` (`lsemStepMC`, `fstepA`) and `ADCXHI:64` writes a one-bit carry-out, so
under `ImgRel` no step of a carry chain on general-purpose names is possible. This module
relates the image and the address machine at mixed width.

## The width analysis

`oneBitAt frame body k` is a decided over-approximation of the names that may hold a one-bit
value at instruction `k`: the carry-out of `ADCXHI:64`, the destination of a carry constant
(`JasminLsemAddrRun.bitMovB`, stepped at the one-bit tag) and the destination of a stored carry
constant (`JasminLsemAddrImage.bitStore?`, a one-bit write on the image) and a name a register
instruction writes with a word of the fixed width `1` (`STerm.wknown`, for instance the result of
`SET<cc>`) enter it, the destination of a load of a frame word of the analysis (the reload of a
spilled bit) enters it, and a name written at width `64` leaves it. `ImgRelW` is `ImgRel` with
the width condition restricted to the general-purpose names outside `oneBitAt` at the program
counter, with a frame-slot name of `oneBitAt` allowed to hold the low bit of its frame word, the
word being the zero-extension of the bit unless an untagged immediate move (`movl`) of the body
writes the frame word (`SlotVal`, `movlNames`), with a general-purpose name of `oneBitAt`
allowed to hold a bit on the image and its zero-extension at width `64` on the address machine
(`RegVal`), and with every general-purpose name outside `castDsts` at width `64` or `1`.
`imgGateBW` is the gate of `ImageAddrSim.imgGateB` over the analysis: a carry-chain instruction
`ADCX:64`/`ADCXHI:64` on three sources is accepted with register or frame-slot word sources,
carry-in and destination, a carry constant into a register or a frame word, a register
instruction writes width-`64` words from names outside the analysis, a store into a frame word
stores a name outside it or a name that no cast of the body writes at a narrow width
(`castDsts`), whose frame word then enters the analysis, an immediate move into a frame word
writes a word that holds no array pointer, a select `CMOV:64` reads a frame-word value or writes a frame-word destination
at its frame word, a branch is taken only where every name of the analysis is in the analysis
one past its label, every name an
instruction reads, other than a carry-in, the condition of a `CMOV:64` select
(`DecodePrintedAddrW.carryIns`), the stored name of a frame-word store and the frame word of a
frame-word load (`gateReadSet`), lies outside the analysis; a load of a frame word of the analysis
loads one that is no general-purpose name and no name of `movlNames`, and a register select
whose condition lies in the analysis has general-purpose operands and values other than the
condition (`cmovCondOkB`). `retOutsB` is the check that no
name of a list of observed names lies in the analysis at the return.

The destination of a width-carrying cast `CASTW_<w>_<w'>` (`DecodePrintedAddrW.classifyK`)
enters the analysis at the destination widths `16` and `32` and leaves it at `64`
(`castOut`). The gate accepts a cast between general-purpose names without a frame word
(`castGateB`); its source lies outside the analysis or has an entry in the cast width analysis
`DecodePrintedAddrW.narrowIn` (`castReadB`). `rel_castW` is the step of a cast.

## Main results

* `oneBitAt_succ`: the analysis at the next instruction.
* `oneBitAt_succ_label`: one past a label the analysis joins the names that the analysis
  without a join `oneBitAt0` has at the later branches to the label (`backNames`).
* `oneBitAt_eq_oneBitAt0`, `imgGateBW_of_old`: without a seed the analysis is `oneBitAt0`,
  and a body with an empty `oneBitAt0` at every branch (`imgGateBW0`) passes `imgGateBW`.
* `rel_condFallW`, `rel_condJumpW`, `gateAtW_condIncl`: a branch keeps `ImgRelW` where the
  analysis at the branch is included in the analysis one past the label, which the gate
  checks.
* `imgGateBW_eq_impl` (`@[csimp]`): the gate is evaluated with the frame map tabulated over
  the names of the body and the instruction gates decided in one pass of the analysis.
* `imgRelW_of`: `ImgRel` gives `ImgRelW` where the analysis is empty.
* `retOutsB_eq_impl` (`@[csimp]`): `retOutsB` is evaluated with the frame map tabulated.
* `imgGateB_eq_impl` (`@[csimp]`): `imgGateB` is evaluated with the frame map tabulated.
* `not_mem_oneBitAt_of_halted`: under `imgGateBW`, at a halt a name outside the analysis at
  the return is outside the analysis.
* `not_mem_of_retOutsB`: under `retOutsB`, an observed name is outside the analysis at the
  return.
* `reg_stepW`, `rel_regW`, `rel_sloadW`, `rel_sstoreW`, `rel_scmpW`, `rel_ldxW`, `rel_stxW`,
  `rel_labelW`: each kind of instruction keeps `ImgRelW`; `rel_regW` carries a register
  instruction to the address state through a state that agrees with the image on every name
  without a frame word (`shadowA`) and the congruence of `fstepA` on the names read.
* `rel_sloadW1`: the reload of a spilled bit keeps `ImgRelW`; its destination holds the bit on
  the image and its zero-extension on the address machine and enters the analysis.
* `gateAtW_notW`: under the gate, the names an instruction reads, other than the one-bit reads,
  lie outside the analysis.
* `bit_virt`, `rel_adcxW`, `rel_adcxhiW`: a carry-chain instruction with register or
  frame-slot operands keeps `ImgRelW`.
* `rel_bmovW`, `rel_bmovSlotW`: a carry constant into a register or a frame word keeps
  `ImgRelW`.
* `rel_bstoreW`: a stored carry constant into a frame word keeps `ImgRelW`.
* `rel_stiW`: an immediate move into a frame word without an array pointer keeps `ImgRelW`.
* `rel_scmovW`, `rel_scmovDstW`: a select into a register or into a frame word keeps
  `ImgRelW`; the address machine reads the condition through `bitA`.
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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames cellBase readsI
  readsRdx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (carryIns WideSafeAt fstepA_adcx3 fstepA_adcxhi classifyK classifyK_spec narrowIn narrowSrc
  fstepA_castW lsemStepCast_castW castStruct?_of_castMovBits bitSrc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)

/-- The untagged `MOV` is an immediate-move mnemonic. -/
theorem isMovImmMnem_mov : isMovImmMnem "MOV" = true := isMovImmMnem_iff.2 (Or.inl rfl)

/-- The 64-bit `MOV:64` is no immediate-move mnemonic of `movImmStruct?`. -/
theorem isMovImmMnem_mov64 : isMovImmMnem "MOV:64" = false := by decide +kernel

/-- `normA` reads an immediate-move mnemonic (`MOV` or `MOV^w`, `w ≠ 64`) as `MOV`. -/
theorem normA_movImm {ds ss : List LOperand} {o : String} (h : isMovImmMnem o = true) :
    normA (.Lopn ds o ss) = .Lopn ds "MOV" ss := by
  rcases isMovImmMnem_iff.1 h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · rw [normA_untag hw (by decide), normA_of_caret_free (by decide)]; simp

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

/-- The names an `Lopn` reads as words: the implicit multiplicand `RDX` of a widening multiply
    (`readsRdx`), the names of its source operands and the base registers of its cell operands
    (the names of `readsI` other than the empty name). -/
def readNames : LinstrR → List String
  | .Lopn ds o ss =>
      (if readsRdx (.Lopn ds o ss) then ["RDX"] else []) ++
        (ss.flatMap srcNames ++ (ds ++ ss).filterMap cellBase)
  | _ => []

/-- The names possibly holding a one-bit value after a register instruction: those of `W`
    the symbolic description of the instruction does not write, and the names it writes with
    a word whose outermost constructor fixes the width `1` (`STerm.wknown`), such as the
    result of a materialised comparison `SET<cc>`. -/
def regOut (W : List String) (x : LinstrR) : List String :=
  match symStep (x, .reg none) SSt.start with
  | .ok ss _ => W.filter (fun r => !ss.wr.contains r)
      ++ ss.wr.filter fun r => (ss.regs r).wknown == some 1
  | _ => W

/-- The names possibly holding a value of a width other than `64` after a width-carrying cast
    (`DecodePrintedAddrW.classifyK`): the destination leaves `W` at the destination width `64`
    and enters it at the widths `16` and `32`; `W` after any other instruction. -/
def castOut (W : List String) (x : LinstrR) : List String :=
  match classifyK x with
  | some (d, _, _, w) => if w = 64 then W.filter (· != d) else d :: W
  | none => W

/-- **One step of the width analysis.** The carry-out of `ADCXHI:64` and the destination of
    an untagged immediate move (a carry constant where the gate accepts it) enter the names
    possibly holding a one-bit value; the destination of `ADCX:64`, of an indexed load and
    of a load of a frame word outside the analysis, and the names a register instruction
    writes, leave it; the frame word of a store of a name of the analysis enters it, and the
    destination of a load of a frame word of the analysis (the reload of a spilled bit) enters
    it. -/
def oneBitStep (frame : String → Option (BitVec 64)) (W : List String) (x : LinstrR) :
    List String :=
  match carryI? x with
  | some (false, d, _, _, _) => W.filter (· != d)
  | some (true, o, _, _, _) => o :: W
  | none =>
      match icase frame x with
      | .ldx d _ _ => W.filter (· != d)
      | .sload d q => if W.contains q then d :: W else W.filter (· != d)
      | .sstore q S => if W.contains S then q :: W else W
      | .reg =>
          match movImmStruct? x with
          | some (d, _) => d :: W
          | none => regOut W (normA x)
      | .other => castOut W x
      | _ => W

/-- **One step of the width analysis at instruction `k` of a body.** The destination of a
    stored carry constant (`bitStore?`, a one-bit write on the image) enters the names
    possibly holding a one-bit value; every other instruction steps by `oneBitStep`. -/
def oneBitStepAt0 (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat)
    (W : List String) (x : LinstrR) : List String :=
  match bitStore? body k x with
  | some (d, _) => d :: W
  | none => oneBitStep frame W x

/-- **The width analysis without a join at labels** at instruction `k` of a body: the fold
    of `oneBitStepAt0` over the prefix of the body, from no name. -/
def oneBitAt0 (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) : List String :=
  ((body.take k).zipIdx).foldl (fun W p => oneBitStepAt0 frame body p.2 W p.1.li_i) []

/-- The names of `oneBitAt0` at the conditional branches after position `p` that target the
    label `l`. -/
def backNames (frame : String → Option (BitVec 64)) (body : Lcmd) (p : Nat) (l : LLabel) :
    List String :=
  ((body.zipIdx).drop (p + 1)).flatMap fun q =>
    match q.1.li_i with
    | .Lcond _ l' => if l' = l then oneBitAt0 frame body q.2 else []
    | _ => []

/-- **The seed of the width analysis at instruction `k`**: at a label, the names of
    `oneBitAt0` at the later branches that target it (`backNames`); no name at any other
    instruction. -/
def seedAt (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) :
    LinstrR → List String
  | .Llabel _ l => backNames frame body k l
  | _ => []

/-- An instruction equal to one that is no label has no seed. -/
theorem seedAt_of_eq {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {x y : LinstrR} (hx : x = y) (hy : ∀ ii l, y ≠ .Llabel ii l) :
    seedAt frame body k x = [] := by
  subst hx
  cases x <;> first | rfl | exact absurd rfl (hy _ _)

/-- A frame-word move has no seed. -/
theorem seedAt_of_slotMov {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {x : LinstrR} {p : String × String} (h : slotMov? x = some p) :
    seedAt frame body k x = [] := by
  cases x <;> first | rfl | simp [slotMov?] at h

/-- **One step of the width analysis at instruction `k` of a body.** The destination of a
    stored carry constant (`bitStore?`, a one-bit write on the image) enters the names
    possibly holding a one-bit value; every other instruction steps by `oneBitStep`, and a
    label adds its seed `seedAt`. -/
def oneBitStepAt (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat)
    (W : List String) (x : LinstrR) : List String :=
  match bitStore? body k x with
  | some (d, _) => d :: W
  | none => oneBitStep frame W x ++ seedAt frame body k x

/-- **The width analysis** at instruction `k` of a body: the names that may hold a one-bit
    value there, the fold of `oneBitStepAt` over the prefix of the body. A label joins the
    names that the analysis without a join has at the later branches to it. -/
def oneBitAt (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) : List String :=
  ((body.take k).zipIdx).foldl (fun W p => oneBitStepAt frame body p.2 W p.1.li_i) []

theorem oneBitAt_zero (frame : String → Option (BitVec 64)) (body : Lcmd) :
    oneBitAt frame body 0 = [] := by
  simp [oneBitAt]

/-- Without a seed at any instruction the width analysis is the analysis without a join. -/
theorem oneBitAt_eq_oneBitAt0 {frame : String → Option (BitVec 64)} {body : Lcmd}
    (h : ∀ k x, seedAt frame body k x = []) (k : Nat) :
    oneBitAt frame body k = oneBitAt0 frame body k := by
  have hs : ∀ j W x, oneBitStepAt frame body j W x = oneBitStepAt0 frame body j W x := by
    intro j W x
    unfold oneBitStepAt oneBitStepAt0
    split
    · rfl
    · rw [h, List.append_nil]
  simp only [oneBitAt, oneBitAt0, hs]

/-- The analysis at the next instruction: one step of `oneBitStepAt`. -/
theorem oneBitAt_succ_at {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) :
    oneBitAt frame body (k + 1) = oneBitStepAt frame body k (oneBitAt frame body k) bi.li_i := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hb).1
  unfold oneBitAt
  rw [List.take_add_one, hb, Option.toList_some, List.zipIdx_append, List.foldl_append,
    List.length_take, Nat.min_eq_left hk.le]
  simp

/-- The analysis at the next instruction, past an instruction that is no stored carry
    constant: one step of `oneBitStep`. -/
theorem oneBitAt_succ {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) (hs : bitStore? body k bi.li_i = none)
    (hl : seedAt frame body k bi.li_i = []) :
    oneBitAt frame body (k + 1) = oneBitStep frame (oneBitAt frame body k) bi.li_i := by
  rw [oneBitAt_succ_at hb, oneBitStepAt, hs]
  simp only [hl, List.append_nil]

/-- The analysis one past a label: the analysis at the label and the seed of the label. -/
theorem oneBitAt_succ_label {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) {ii : _} {l : LLabel}
    (hx : bi.li_i = .Llabel ii l) :
    oneBitAt frame body (k + 1) = oneBitAt frame body k ++ backNames frame body k l := by
  rw [oneBitAt_succ_at hb, hx]
  rfl

/-- An instruction equal to one of another form than a 64-bit immediate move is no stored
    carry constant. -/
theorem bitStore?_of_eq {body : Lcmd} {k : Nat} {x y : LinstrR} (hx : x = y)
    (hy : ∀ d n, y ≠ .Lopn [.reg d] "MOV:64" [.imm n]) : bitStore? body k x = none := by
  subst hx
  exact bitStore?_of_ne hy

/-- The analysis at the next instruction, past a stored carry constant into `d`: `d` enters
    it. -/
theorem oneBitAt_succ_store {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) {d : String} {n : Nat}
    (hs : bitStore? body k bi.li_i = some (d, n)) :
    oneBitAt frame body (k + 1) = d :: oneBitAt frame body k := by
  rw [oneBitAt_succ_at hb, oneBitStepAt, hs]

theorem regOut_slotImm (W : List String) (q : String) (v : Nat) {r : String} (hr : r ≠ q)
    (h : r ∉ regOut W (.Lopn [.reg q] "MOV:64" [.imm v])) : r ∉ W := by
  intro hW
  apply h
  have hm : stripWidthTag "MOV:64" = "MOV" := by decide +kernel
  have hn : ∀ R, symN (.Lopn [.reg q] "MOV:64" [.imm v]) R
      = .set q (.immW (widthFromTag "MOV:64") v) [] := fun R => by
    unfold symN
    simp only [hm, ite_true]
  have hd : ∀ R, symMC (.Lopn [.reg q] "MOV:64" [.imm v]) R
      = .set q (.immW (widthFromTag "MOV:64") v) [] := fun R => by
    simp only [symMC, symSh, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?,
      VIR.JasminLsemShift.sarStruct?, hn]
  have hmi : movImmStruct? (.Lopn [.reg q] "MOV:64" [.imm v]) = none := by
    simp [movImmStruct?, isMovImmMnem_mov64]
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
    `64` when the names outside `W` have width `64`, or a word whose outermost constructor
    fixes the width `1` (such a name enters the width analysis through `regOut`). -/
def regGateBW (frame : String → Option (BitVec 64)) (W : List String) (x : LinstrR) : Bool :=
  regOkB frame x &&
    match symStep (x, .reg none) SSt.start with
    | .ok ss _ => ss.wr.all (fun r => !gpOk r || wid64WB W (ss.regs r)
        || (ss.regs r).wknown == some 1)
    | _ => false

/-- The conditions of a carry-chain instruction `ADCX:64 d, a, s, c` or
    `ADCXHI:64 d, a, s, c`: a carry-in and word sources that are general-purpose names or
    frame slots, and a destination that is a general-purpose name or a frame slot that holds
    no array pointer; the word sources are not the carry-in. -/
def carryOkB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (d a s c : String) : Bool :=
  (gpOk c || (frame c).isSome) && (gpOk a || (frame a).isSome) && (gpOk s || (frame s).isSome)
    && (gpOk d || ((frame d).isSome && (slotArr d).isNone))
    && a != c && s != c

/-- Every name an `Lopn` reads, other than a carry-in, lies outside `W`. -/
def readOkB (W : List String) (x : LinstrR) : Bool :=
  (readNames x).all fun r => (carryIns x).contains r || !W.contains r

theorem readOkB_spec {W : List String} {x : LinstrR} (h : readOkB W x = true) {r : String}
    (hr : r ∈ readNames x) (hc : r ∉ carryIns x) : r ∉ W := by
  unfold readOkB at h
  have := List.all_eq_true.1 h r hr
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h1 | h1
  · exact absurd (by simpa using h1) hc
  · simpa using h1

/-- A select `CMOV:64 d, [c, a, b]` whose condition `c` lies in `W` has general-purpose
    operands and values other than the condition; every other instruction passes. -/
def cmovCondOkB (W : List String) : LinstrR → Bool
  | .Lopn [.reg d] o [.reg c, .reg a, .reg b] =>
      o != "CMOV:64" || !W.contains c
        || (gpOk d && gpOk c && gpOk a && gpOk b && a != c && b != c)
  | _ => true

/-- The names `readOkB` checks against at an instruction: `W` without the stored name of a
    frame-word store and without the frame word of a frame-word load, all of `W` at every other
    instruction. -/
def gateReadSet (frame : String → Option (BitVec 64)) (W : List String) (x : LinstrR) :
    List String :=
  match icase frame x with
  | .sstore _ S => W.filter (· != S)
  | .sload _ q => W.filter (· != q)
  | _ => W

/-- Under `readOkB` at `gateReadSet`, a name read other than a carry-in, the stored name of a
    frame-word store and the frame word of a frame-word load lies outside `W`. -/
theorem readOkB_gateReadSet_spec {frame : String → Option (BitVec 64)} {W : List String}
    {x : LinstrR} (h : readOkB (gateReadSet frame W x) x = true) {r : String}
    (hr : r ∈ readNames x) (hc : r ∉ carryIns x) (hs : ∀ q, icase frame x ≠ .sstore q r)
    (hl : ∀ d, icase frame x ≠ .sload d r) :
    r ∉ W := by
  have h1 := readOkB_spec h hr hc
  unfold gateReadSet at h1
  split at h1
  · rename_i q S heq
    have hne : r ≠ S := fun e => hs q (by rw [heq, e])
    intro hm
    exact h1 (List.mem_filter.2 ⟨hm, by simpa using hne⟩)
  · rename_i d q heq
    have hne : r ≠ q := fun e => hl d (by rw [heq, e])
    intro hm
    exact h1 (List.mem_filter.2 ⟨hm, by simpa using hne⟩)
  · exact h1

/-- The destinations of the untagged immediate moves `MOV d, #n` of a body. Into a frame word
    such a move is `movl $n, off(%rsp)`, which keeps the high 32 bits of the word. -/
def movlNames (body : Lcmd) : List String :=
  body.filterMap fun i => (movImmStruct? i.li_i).map Prod.fst

/-- The destination of an untagged immediate move of the body is a name of `movlNames`. -/
theorem mem_movlNames {body : Lcmd} {k : Nat} {bi : Linstr} (hb : body[k]? = some bi)
    {d : String} {n : Nat} (hm : movImmStruct? bi.li_i = some (d, n)) : d ∈ movlNames body := by
  unfold movlNames
  rw [List.mem_filterMap]
  exact ⟨bi, List.mem_of_getElem? hb, by simp [hm]⟩

/-- The destinations of the width-carrying casts of a body to a width other than `64`. -/
def castDsts (body : Lcmd) : List String :=
  body.filterMap fun i =>
    match classifyK i.li_i with
    | some (d, _, _, w) => if w = 64 then none else some d
    | none => none

/-- The destination of a cast to a width other than `64` at an instruction of the body is a
    name of `castDsts`. -/
theorem mem_castDsts {body : Lcmd} {k : Nat} {bi : Linstr} (hb : body[k]? = some bi)
    {d a : String} {m w : Nat} (hk : classifyK bi.li_i = some (d, a, m, w)) (hw : w ≠ 64) :
    d ∈ castDsts body := by
  unfold castDsts
  rw [List.mem_filterMap]
  exact ⟨bi, List.mem_of_getElem? hb, by simp [hk, hw]⟩

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

/-- A select `CMOV:64 d, [c, a, b]` with a frame word among its values or as its destination:
    a destination without a frame word or a frame word that holds no array pointer, a
    condition without a frame word, a true value that is a general-purpose name or a frame
    word other than the condition, and a frame word among the destination and the two
    values. -/
def sCmovB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat)) :
    LinstrR → Bool
  | .Lopn [.reg d] o [.reg c, .reg a, .reg b] =>
      o == "CMOV:64" && ((frame d).isNone || (slotArr d).isNone) && (frame c).isNone
        && (gpOk a || (frame a).isSome) && a != c
        && ((frame d).isSome || (frame a).isSome || (frame b).isSome)
  | _ => false

theorem sCmovB_spec {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {x : LinstrR}
    (h : sCmovB frame slotArr x = true) :
    ∃ d c a b, x = .Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b]
      ∧ (frame d = none ∨ slotArr d = none)
      ∧ frame c = none ∧ (gpOk a = true ∨ (frame a).isSome = true) ∧ a ≠ c
      ∧ ((frame d).isSome || (frame a).isSome || (frame b).isSome) = true := by
  unfold sCmovB at h
  split at h
  · rename_i d o c a b
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, Bool.or_eq_true,
      bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨⟨rfl, hd⟩, hc⟩, ha⟩, hac⟩, hsl⟩ := h
    exact ⟨d, c, a, b, rfl, hd, hc, ha, hac, by simpa using hsl⟩
  · cases h

/-- A register instruction accepted by the register arm of the gate with carry chains, an
    immediate move into a frame word (`sImmB`), a select with a frame-word operand
    (`sCmovB`) or an instruction passing `regGateBW`, is no indexed store through a cell. -/
theorem cellIdxStore?_of_regArmW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {x : LinstrR}
    (h : (sImmB frame slotArr x || sCmovB frame slotArr x
      || (regGateBW frame W (normA x) && cmovCondOkB W x)) = true) :
    cellIdxStore? slotArr body k x = none := by
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (h | h) | ⟨h, -⟩
  · obtain ⟨q, v, a, rfl, -⟩ := sImmB_spec h
    exact cellIdxStore?_of_ne slotArr (by simp)
  · obtain ⟨d, c, a, b, rfl, -⟩ := sCmovB_spec h
    exact cellIdxStore?_of_ne slotArr (by simp)
  · cases hs : cellIdxStore? slotArr body k x with
    | none => rfl
    | some p =>
        obtain ⟨h1, h2⟩ := ImageAddrSim.cellA?_of_cellIdxStore hs
        obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp h1
        rw [h2] at h
        simp [regGateBW, regOkB, hop] at h

/-- The instruction at position `k` is a width-carrying cast whose source has an entry in the
    cast width analysis `DecodePrintedAddrW.narrowIn`. -/
def castReadB (body : Lcmd) (k : Nat) (x : LinstrR) : Bool :=
  match classifyK x with
  | some (_, a, _, _) => ((narrowIn body k).lookup a).isSome
  | none => false

/-- A width-carrying cast between general-purpose names without a frame word. -/
def castGateB (frame : String → Option (BitVec 64)) (x : LinstrR) : Bool :=
  match classifyK x with
  | some (d, a, _, _) => gpOk d && gpOk a && (frame d).isNone && (frame a).isNone
  | none => false

/-- **The gate of instruction `k` at the analysis `W`**: the names read, other than the stored
    name of a frame-word store and the frame word of a frame-word load, lie outside `W`
    (`readOkB` at `gateReadSet`) or the instruction is a
    cast whose source has an entry in the cast width analysis (`castReadB`), and the
    instruction is a width-carrying cast between general-purpose names (`castGateB`), a
    carry-chain instruction passing `carryOkB`, a label, a branch on a condition code with a
    polarity to a label of the body one past which the width analysis includes every name of
    `W`, an indexed access, a frame-word move or compare as in `instrGateB`, where a frame-word
    load of a frame word of `W` loads one that is no general-purpose name and that no untagged
    immediate move of the body writes (`movlNames`), and a frame-word
    store `q := S` stores a general-purpose name `S` outside `W`, or one that no cast of the
    body writes at a narrow width (`castDsts`) into a frame word `q` that is neither a
    general-purpose name nor a cell name `mem.B.off`, a carry constant (`bitMovB`) into a general-purpose name without a frame
    word or into a frame word without an array pointer, an immediate move into a frame word
    without an array pointer (`sImmB`), which is the only form a stored carry constant
    (`bitStore?`) takes, a select with a frame-word value or destination (`sCmovB`), or a
    register instruction other than an untagged immediate move passing `regGateBW`, whose
    select on a condition of `W` has general-purpose operands and values other than the
    condition (`cmovCondOkB`). -/
def gateAtW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (W : List String) (x : LinstrR) : Bool :=
  (readOkB (gateReadSet frame W x) x || castReadB body k x) &&
    match carryI? x with
    | some (_, d, a, s, c) => carryOkB frame slotArr d a s c
    | none =>
        match icase frame x with
        | .label => true
        | .cond cc l => (condPol cc).isSome && (labelAt body l).any fun p =>
            W.isEmpty || W.all fun r => (oneBitAt frame body (p + 1)).contains r
        | .ldx d b idx => (accArr slotArr body k b).isSome && gpOk d && (frame d).isNone
            && (frame idx).isNone && (frame b).isNone
        | .stx _ b idx v => (accArr slotArr body k b).isSome && (frame idx).isNone
            && (frame b).isNone && (frame v).isNone
        | .sload d q => gpOk d
            && (!W.contains q || (!(movlNames body).contains q && !gpOk q))
        | .sstore q S => gpOk S
            && (!W.contains S
              || (!(castDsts body).contains S && !gpOk q && !hasPrefix q "mem."))
        | .scmp _ y _ => (frame y).isNone
        | .reg =>
            match movImmStruct? x with
            | some (d, _) => bitMovB body k x
                && (gpOk d && (frame d).isNone || (frame d).isSome && (slotArr d).isNone)
            | none =>
                match bitStore? body k x with
                | some _ => sImmB frame slotArr x
                | none => sImmB frame slotArr x || sCmovB frame slotArr x
                    || (regGateBW frame W (normA x) && cmovCondOkB W x)
        | .zarr .. => false
        | .simm .. => false
        | .other => castGateB frame x

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

/-- The check that no name of the observed names `outs` is in the width analysis at the last
    instruction of the body. -/
def retOutsB (frame : String → Option (BitVec 64)) (body : Lcmd) (outs : List String) : Bool :=
  let W := oneBitAt frame body (body.length - 1)
  outs.all fun r => !W.contains r

/-- Under `retOutsB`, an observed name is not in the width analysis at the last instruction. -/
theorem not_mem_of_retOutsB {frame : String → Option (BitVec 64)} {body : Lcmd}
    {outs : List String} (h : retOutsB frame body outs = true) {r : String} (hr : r ∈ outs) :
    r ∉ oneBitAt frame body (body.length - 1) := by
  intro hm
  have := List.all_eq_true.mp h r hr
  simp [hm] at this

/-- The instruction gates of `imgGateBW` in one pass: from position `k` with the width
    analysis `W` at `k` and the remaining instructions, the gate `gateAtW` of at most `n`
    instructions, the analysis advanced by `oneBitStepAt` after each. -/
def gateLoop (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Nat → Nat → List String → Lcmd → Bool
  | 0, _, _, _ => true
  | _ + 1, _, _, [] => true
  | n + 1, k, W, i :: rest =>
      gateAtW frame slotArr body k W i.li_i && gateLoop frame slotArr body n (k + 1)
        (oneBitStepAt frame body k W i.li_i) rest

/-- From position `k` at the width analysis `oneBitAt frame body k`, the one-pass loop
    decides the instruction gates `instrGateBW` at positions `k` to `k + n - 1`. -/
theorem gateLoop_eq (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    ∀ n k, gateLoop frame slotArr body n k (oneBitAt frame body k) (body.drop k)
      = (List.range' k n).all (fun j =>
          (body[j]?).all fun i => instrGateBW frame slotArr body j i.li_i) := by
  intro n
  induction n with
  | zero => intro k; simp [gateLoop]
  | succ n ih =>
      intro k
      cases hd : body.drop k with
      | nil =>
          have hk : body.length ≤ k := by simpa using hd
          rw [gateLoop]
          symm
          rw [List.all_eq_true]
          intro j hj
          rw [List.mem_range'_1] at hj
          rw [List.getElem?_eq_none (by omega)]
          rfl
      | cons i rest =>
          have hi : body[k]? = some i := by
            rw [← List.head?_drop, hd]; rfl
          have hr : body.drop (k + 1) = rest := by
            rw [← List.drop_drop, hd]; rfl
          rw [List.range'_succ, List.all_cons, hi, Option.all_some, gateLoop, ← ih (k + 1),
            hr, oneBitAt_succ_at hi]
          rfl

/-- The frame map read through the table `T`: the entry of `T` at `q` when there is one,
    and `frame q` otherwise. -/
def tabFrame (frame : String → Option (BitVec 64)) (T : List (String × Option (BitVec 64)))
    (q : String) : Option (BitVec 64) :=
  match T.lookup q with
  | some v => v
  | none => frame q

/-- A table of the values of `frame` at a list of names reads back `frame`. -/
theorem tabFrame_eq (frame : String → Option (BitVec 64)) (N : List String) :
    tabFrame frame (N.map fun q => (q, frame q)) = frame := by
  funext q
  induction N with
  | nil => rfl
  | cons a N ih =>
      unfold tabFrame at ih ⊢
      by_cases h : q = a
      · subst h
        simp
      · have hb : (q == a) = false := by simpa using h
        simp only [List.map_cons, List.lookup, hb]
        exact ih

/-- `imgGateBW` evaluated with the frame map tabulated over the names of the body and the
    instruction gates decided in one pass (`gateLoop`). -/
def imgGateBWImpl (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  let fr := tabFrame frame ((ImageAddrFrame.bodyNamesI body).eraseDups.map fun q => (q, frame q))
  gateLoop fr slotArr body (body.length - 1) 0 [] body
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- The gate `imgGateBW` is evaluated as `imgGateBWImpl`. -/
@[csimp] theorem imgGateBW_eq_impl : @imgGateBW = @imgGateBWImpl := by
  funext frame slotArr body
  have h := gateLoop_eq frame slotArr body (body.length - 1) 0
  simp only [oneBitAt_zero, List.drop_zero] at h
  simp only [imgGateBWImpl, tabFrame_eq]
  rw [imgGateBW, h, List.range_eq_range']

/-- `retOutsB` evaluated with the frame map tabulated over the names of the body. -/
def retOutsBImpl (frame : String → Option (BitVec 64)) (body : Lcmd) (outs : List String) :
    Bool :=
  retOutsB (tabFrame frame ((ImageAddrFrame.bodyNamesI body).eraseDups.map fun q => (q, frame q)))
    body outs

/-- The check `retOutsB` is evaluated as `retOutsBImpl`. -/
@[csimp] theorem retOutsB_eq_impl : @retOutsB = @retOutsBImpl := by
  funext frame body outs
  simp only [retOutsBImpl, tabFrame_eq]

/-- `imgGateB` evaluated with the frame map tabulated over the names of the body. -/
def imgGateBImpl (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  imgGateB (tabFrame frame ((ImageAddrFrame.bodyNamesI body).eraseDups.map fun q => (q, frame q)))
    slotArr body

/-- The gate `imgGateB` is evaluated as `imgGateBImpl`. -/
@[csimp] theorem imgGateB_eq_impl : @imgGateB = @imgGateBImpl := by
  funext frame slotArr body
  simp only [imgGateBImpl, tabFrame_eq]

/-- The value `v` of a frame-slot name `q` on the image against the word `m` at its frame
    address: the whole word, or, for a name of the width analysis `W`, the low bit of the
    word, the word being the zero-extension of its low bit unless `q` is a name of `N` (the
    frame words an untagged immediate move `movl` writes, `movlNames`). -/
def SlotVal (N W : List String) (q : String) (v : Σ w, BitVec w) (m : BitVec 64) : Prop :=
  v = ⟨64, m⟩ ∨ (q ∈ W ∧ v = ⟨1, m.setWidth 1⟩ ∧ (q ∉ N → (m.setWidth 1).setWidth 64 = m))

/-- Outside the width analysis a frame-slot name holds the whole word. -/
theorem SlotVal.word {N W : List String} {q : String} {v : Σ w, BitVec w} {m : BitVec 64}
    (h : SlotVal N W q v m) (hq : q ∉ W) : v = ⟨64, m⟩ :=
  h.resolve_right fun h' => hq h'.1

/-- `SlotVal` transported along equal values and words and a larger width analysis. -/
theorem SlotVal.of_eq {N W W' : List String} {q : String} {v v' : Σ w, BitVec w}
    {m m' : BitVec 64} (h : SlotVal N W q v m) (hv : v' = v) (hm : m' = m)
    (hW : q ∈ W → q ∈ W') : SlotVal N W' q v' m' := by
  subst hv hm
  exact h.imp id fun h' => ⟨hW h'.1, h'.2⟩

/-- A 64-bit read of a frame-slot name on the image returns the word at its frame address. -/
theorem SlotVal.getW64 {N W : List String} {q : String} {r : LstateN} {m : BitVec 64}
    (h : SlotVal N W q (r.lvm q) m) {v : BitVec 64} (hv : r.getW q 64 = some v) : v = m := by
  rw [getW_eq_some_iff] at hv
  rcases h with h | ⟨-, h, -⟩ <;> rw [hv] at h <;> simp_all

/-- The one-bit value of a frame-slot name: its bit is the low bit of the word, and the word
    is the zero-extension of the bit unless `q` is a name of `N`. -/
theorem SlotVal.bit {N W : List String} {q : String} {v : Σ w, BitVec w} {m : BitVec 64}
    (h : SlotVal N W q v m) {b : BitVec 1} (hv : v = ⟨1, b⟩) :
    q ∈ W ∧ m.setWidth 1 = b ∧ (q ∉ N → m = b.setWidth 64) := by
  rcases h with h | ⟨hq, h, hz⟩
  · rw [hv] at h; cases h
  · rw [hv] at h
    obtain rfl := eq_of_heq (Sigma.mk.inj h).2
    exact ⟨hq, rfl, fun hn => (hz hn).symm⟩

/-- A frame-slot name of `W` holding a bit whose zero-extension is the word. -/
theorem SlotVal.of_zext {N W : List String} {q : String} (hq : q ∈ W) (b : BitVec 1) :
    SlotVal N W q ⟨1, b⟩ (b.setWidth 64) :=
  Or.inr ⟨hq, by simp, fun _ => by simp⟩

/-- The value `v` of a name `r` on the image against its value `v'` on the address machine:
    the same value, or, for a general-purpose name of the width analysis `W`, a bit on the
    image and its zero-extension at width `64` on the address machine (a reloaded spilled
    bit). -/
def RegVal (W : List String) (r : String) (v v' : Σ w, BitVec w) : Prop :=
  v = v' ∨ (r ∈ W ∧ gpOk r = true ∧ ∃ b : BitVec 1, v = ⟨1, b⟩ ∧ v' = ⟨64, b.setWidth 64⟩)

/-- Outside the width analysis a name holds the same value on both machines. -/
theorem RegVal.eq {W : List String} {r : String} {v v' : Σ w, BitVec w} (h : RegVal W r v v')
    (hr : r ∉ W) : v = v' :=
  h.resolve_right fun h' => hr h'.1

/-- `RegVal` transported along equal values and a larger width analysis. -/
theorem RegVal.of_eq {W W' : List String} {r : String} {v v' u u' : Σ w, BitVec w}
    (h : RegVal W r v v') (hu : u = v) (hu' : u' = v') (hW : r ∈ W → r ∈ W') :
    RegVal W' r u u' := by
  subst hu hu'
  exact h.imp id fun h' => ⟨hW h'.1, h'.2⟩

/-- A one-bit read agrees on related values: the bit of the address value (`regBit`). -/
theorem RegVal.regBit {W : List String} {r : String} {s s' : LstateN}
    (h : RegVal W r (s.lvm r) (s'.lvm r)) {b : BitVec 1} (hb : s.getW r 1 = some b) :
    regBit s' r = some b := by
  rcases h with h | ⟨-, -, b', h1, h2⟩
  · rw [regBit_of_lvm h.symm]; exact regBit_of_getW1 hb
  · rw [getW_eq_some_iff, h1] at hb
    obtain rfl := eq_of_heq (Sigma.mk.inj hb).2
    exact regBit_of_lvm64 h2

/-- A 64-bit read agrees on related values. -/
theorem RegVal.getW64 {W : List String} {r : String} {s s' : LstateN}
    (h : RegVal W r (s.lvm r) (s'.lvm r)) {v : BitVec 64} (hv : s.getW r 64 = some v) :
    s'.getW r 64 = some v := by
  rcases h with h | ⟨-, -, b', h1, -⟩
  · unfold LstateN.getW at hv ⊢
    rw [← h]; exact hv
  · rw [getW_eq_some_iff, h1] at hv
    cases hv

/-- `RegVal` at a width analysis `W'` that keeps every name of `W` holding a bit on the
    image. -/
theorem RegVal.keep {W W' : List String} {r : String} {v v' : Σ w, BitVec w}
    (h : RegVal W r v v') (hk : r ∈ W → gpOk r = true → v.1 = 1 → r ∈ W') :
    RegVal W' r v v' := by
  rcases h with h | ⟨hr, hg, b, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨hk hr hg (by rw [h1]), hg, b, h1, h2⟩

/-- On related values the address machine holds a 64-bit value wherever the image does. -/
theorem RegVal.wid {W : List String} {r : String} {v v' : Σ w, BitVec w}
    (h : RegVal W r v v') (hv : v.1 = 64) : v'.1 = 64 := by
  rcases h with h | ⟨-, -, b, h1, h2⟩
  · rw [← h]; exact hv
  · rw [h2]

/-- **The relation of the image simulation with carry chains**: `ImgRel` with the width
    condition on the general-purpose names outside the width analysis at the program
    counter, a frame-slot name of the width analysis holding the low bit of its frame
    word, which is the zero-extension of that bit for a frame word no untagged immediate move
    writes (`SlotVal`), a name without a frame word of the width analysis holding the same
    value on both machines or a bit on the image and its zero-extension on the address machine
    (`RegVal`), and a general-purpose name that no cast of the body writes at a narrow width
    (`castDsts`) holding a value of width `64` or `1`. -/
structure ImgRelW (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (body : Lcmd)
    (s : LstateMF) (sa : LstateA) (zf : Bool) : Prop where
  pc : sa.reg.lpc = s.prog.base.reg.lpc
  regs : ∀ r, frame r = none →
    RegVal (oneBitAt frame body sa.reg.lpc) r (s.prog.base.reg.lvm r) (sa.reg.lvm r)
  slots : ∀ q a, frame q = some a →
    SlotVal (movlNames body) (oneBitAt frame body sa.reg.lpc) q (s.prog.base.reg.lvm q)
      (read64 sa.mem a)
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
  reload : ∀ b q a A n, reloadOf slotArr body sa.reg.lpc b = some q →
    slotArr q = some (A, n) → frame q = some a → frame b = none →
      sa.reg.lvm b = ⟨64, read64 sa.mem a⟩
  held : HeldAt frame slotArr base sa.mem
  bits : ∀ r, gpOk r = true → r ∉ castDsts body →
    (sa.reg.lvm r).1 = 64 ∨ (sa.reg.lvm r).1 = 1

/-- Outside the width analysis a name without a frame word holds the same value on both
    machines. -/
theorem ImgRelW.regsEq {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} (h : ImgRelW frame slotArr base body s sa zf)
    {r : String} (hf : frame r = none) (hr : r ∉ oneBitAt frame body sa.reg.lpc) :
    s.prog.base.reg.lvm r = sa.reg.lvm r :=
  (h.regs r hf).eq hr

/-- `ImgRel` is `ImgRelW` where the width analysis is empty. -/
theorem imgRelW_of {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} (h : ImgRel frame slotArr base body s sa zf) :
    ImgRelW frame slotArr base body s sa zf :=
  ⟨h.pc, fun r hr => Or.inl (h.regs r hr), fun q a ha => Or.inl (h.slots q a ha), h.zf, h.cf, h.of,
    fun r hr _ => h.wid r hr, h.cells, h.saved, h.reload, h.held,
    fun r hr _ => Or.inl (h.wid r hr)⟩

/-- The width condition of `ImgRelW.bits` after a write of a value of width `64` or `1` and an
    advance of the program counter. -/
theorem bits_setReg {body : Lcmd} {r0 : LstateN}
    (h : ∀ r, gpOk r = true → r ∉ castDsts body → (r0.lvm r).1 = 64 ∨ (r0.lvm r).1 = 1)
    (D : String) {w : Nat} (v : BitVec w) (hw : w = 64 ∨ w = 1) :
    ∀ r, gpOk r = true → r ∉ castDsts body →
      ((r0.setReg D v).nextPc.lvm r).1 = 64 ∨ ((r0.setReg D v).nextPc.lvm r).1 = 1 := by
  intro r hr hc
  by_cases e : r = D
  · subst e
    simpa [LstateN.setReg, LstateN.nextPc] using hw
  · simpa [LstateN.setReg, LstateN.nextPc, e] using h r hr hc

/-- `ImgRelW` is `ImgRel` where the width analysis is empty. -/
theorem imgRel_of_W {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} (h : ImgRelW frame slotArr base body s sa zf)
    (hW : oneBitAt frame body sa.reg.lpc = []) : ImgRel frame slotArr base body s sa zf :=
  ⟨h.pc, fun r hr => h.regsEq hr (by rw [hW]; simp),
    fun q a ha => (h.slots q a ha).word (by rw [hW]; simp), h.zf, h.cf, h.of,
    fun r hr => h.wid r hr (by rw [hW]; simp), h.cells, h.saved, h.reload, h.held⟩

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

/-- **The gate with an empty analysis at every branch**: `imgGateBW` over the analysis
    without a join `oneBitAt0`, where no name is in the analysis at a conditional branch. -/
def imgGateBW0 (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all (fun k =>
      (body[k]?).all fun i =>
        gateAtW frame slotArr body k (oneBitAt0 frame body k) i.li_i
          && (match i.li_i with
              | .Lcond _ _ => (oneBitAt0 frame body k).isEmpty
              | _ => true))
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- **A body with an empty analysis at every branch has no seed**: its width analysis is the
    analysis without a join. -/
theorem oneBitAt_of_old {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW0 frame slotArr body = true) (k0 : Nat) :
    oneBitAt frame body k0 = oneBitAt0 frame body k0 := by
  simp only [imgGateBW0, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hall, hlast⟩, hrs⟩ := h
  have hret : ∀ k i, body[k]? = some i → ¬ k < body.length - 1 →
      ∀ c l, i.li_i ≠ .Lcond c l := by
    intro k i hi hk c l hc
    have hkl : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
    have hg : body.getLast? = some i := by
      rw [List.getLast?_eq_getElem?, ← hi]
      congr 1
      omega
    rw [hg] at hlast
    simp [hc, isRetB] at hlast
  have hseed : ∀ k x, seedAt frame body k x = [] := by
    intro k x
    cases x with
    | Llabel ii l =>
        simp only [seedAt, backNames, List.flatMap_eq_nil_iff]
        intro q hq
        have hq' := List.mem_of_mem_drop hq
        obtain ⟨a, j⟩ := q
        have hj : body[j]? = some a := by
          simpa [List.mem_zipIdx_iff_getElem?] using hq'
        split
        · rename_i c l' hc
          split
          · by_cases hjl : j < body.length - 1
            · have := hall j hjl
              rw [hj] at this
              simp only [Option.all_some, Bool.and_eq_true] at this
              simp only at hc
              rw [hc] at this
              simpa using this.2
            · exact absurd hc (hret j a hj hjl _ _)
          · rfl
        · rfl
    | _ => rfl
  exact oneBitAt_eq_oneBitAt0 hseed k0

/-- The check `retOutsB` over the analysis without a join `oneBitAt0`. -/
def retOutsB0 (frame : String → Option (BitVec 64)) (body : Lcmd) (outs : List String) : Bool :=
  let W := oneBitAt0 frame body (body.length - 1)
  outs.all fun r => !W.contains r

/-- For a body with an empty analysis at every branch, `retOutsB` is `retOutsB0`. -/
theorem retOutsB_of_old {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW0 frame slotArr body = true) (outs : List String) :
    retOutsB frame body outs = retOutsB0 frame body outs := by
  simp only [retOutsB, retOutsB0, oneBitAt_of_old h]

/-- **A body with an empty analysis at every branch passes `imgGateBW`**: no label has a
    seed, so the width analysis is the analysis without a join. -/
theorem imgGateBW_of_old {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW0 frame slotArr body = true) : imgGateBW frame slotArr body = true := by
  have he : ∀ k, oneBitAt frame body k = oneBitAt0 frame body k := oneBitAt_of_old h
  simp only [imgGateBW0, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hall, hlast⟩, hrs⟩ := h
  simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨fun k hk => ?_, hlast⟩, hrs⟩
  have := hall k hk
  cases hb : body[k]? with
  | none => rfl
  | some i =>
      rw [hb] at this
      simp only [Option.all_some, Bool.and_eq_true] at this ⊢
      rw [instrGateBW, he]
      exact this.1

/-- A register instruction passing `regOkB` keeps every name with a frame word in the width
    analysis. -/
theorem mem_regOut_of_frame {frame : String → Option (BitVec 64)} {W : List String}
    {x : LinstrR} (hok : regOkB frame x = true) {q : String} (hq : (frame q).isSome = true)
    (h : q ∈ W) : q ∈ regOut W x := by
  unfold regOut
  split
  · rename_i ss gs hS
    simp only [regOkB, hS, Bool.and_eq_true, List.all_eq_true] at hok
    refine List.mem_append_left _ (List.mem_filter.2 ⟨h, ?_⟩)
    cases hw : ss.wr.contains q
    · rfl
    · have := hok.2.2 q (by simpa using hw)
      rw [Option.isNone_iff_eq_none] at this
      rw [this] at hq
      cases hq
  · exact h

/-- **At a halt the width analysis is the analysis at the return**, for a body passing
    `imgGateBW`: the program counter is at the final return or past the end of the body, so a
    name outside the analysis at the last instruction is outside the analysis at the halt. -/
theorem not_mem_oneBitAt_of_halted {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hgate : imgGateBW frame slotArr body = true) {sa : LstateA}
    (hh : haltedA body sa = true) {q : String}
    (hW : q ∉ oneBitAt frame body (body.length - 1)) :
    q ∉ oneBitAt frame body sa.reg.lpc := by
  obtain ⟨r, hr, hret⟩ := imgGateBW_last hgate
  have hlen : 0 < body.length := by
    cases body with
    | nil => cases hr
    | cons _ _ => simp
  have hlast : body[body.length - 1]? = some r := by
    rw [← List.getLast?_eq_getElem?]; exact hr
  have hge : body.length - 1 ≤ sa.reg.lpc := by
    by_contra hlt
    have hk : sa.reg.lpc < body.length := by omega
    obtain ⟨bi, hb⟩ : ∃ bi, body[sa.reg.lpc]? = some bi :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    have hbr : bi.li_i = .Lret := by
      unfold haltedA at hh
      rw [hb] at hh
      obtain ⟨ii, li⟩ := bi
      cases li <;> simp_all
    simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc (by omega)
    rw [hb] at this
    simp [instrGateBW, gateAtW, hbr, carryI?, icase, castGateB, classifyK] at this
  rcases Nat.lt_or_ge sa.reg.lpc body.length with hk | hk
  · rwa [show sa.reg.lpc = body.length - 1 by omega]
  · have e : oneBitAt frame body sa.reg.lpc = oneBitAt frame body (body.length - 1) := by
      have e1 : oneBitAt frame body sa.reg.lpc = oneBitAt frame body body.length := by
        unfold oneBitAt
        rw [List.take_of_length_le hk, List.take_of_length_le (le_refl _)]
      have e2 : oneBitAt frame body (body.length - 1 + 1)
          = oneBitAt frame body (body.length - 1) := by
        rw [oneBitAt_succ_at hlast, hret]
        simp [oneBitStepAt, seedAt, bitStore?, oneBitStep, carryI?, icase, castOut, classifyK]
      rw [show body.length - 1 + 1 = body.length by omega] at e2
      rw [e1, e2]
    rw [e]
    exact hW

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
      rcases slotMov?_cases hm with hx | hx
      · rw [hx] at hg
        simp [instrGateBW, gateAtW, carryI?, icase, slotMov?, ha, hR, castGateB, classifyK,
          castTagW] at hg
      · rw [hx] at hg hm
        have hc : (cellParts? (slotOfReg R)).isSome = false ∧ (cellParts? R).isSome = false := by
          simp only [slotMov?] at hm
          split_ifs at hm with h1 h2
          simp_all
        simp [instrGateBW, gateAtW, carryI?, icase, slotMov?, ha, hR, castGateB, classifyK,
          castTagW, hc] at hg

/-- At an indexed access whose pointer register was reloaded from the frame word of an
    array, the pointer register holds the base of the array. -/
theorem ptr_of_reloadW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateBW frame slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {b A : String} {n : Nat}
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n)) (hbf : frame b = none) :
    ∃ q, slotArr q = some (A, n) ∧ sa.reg.getW b 64 = some (base A) := by
  obtain ⟨q, hr, hq, k', i, b', hk', hi, hm⟩ := accArr_spec hacc
  obtain ⟨a, ha⟩ := hsep.slotFrame q A n hq
  have hrl := hrel.reload b q a A n hr hq ha hbf
  have hrs : reloadSavedB slotArr body = true := by
    simp only [imgGateBW, Bool.and_eq_true] at hgate; exact hgate.2
  have hp : read64 sa.mem a = base A := by
    rcases reloadSavedB_spec hrs hi hm (by rw [hq]; rfl) with ⟨j, R, hj, hS, hqR⟩ | ⟨R, hqR, hR⟩
    · subst hqR
      exact (hrel.saved j R A n a hS hq ha).1 (by omega)
    · subst hqR
      exact hrel.held R A n a hR hq ha
  refine ⟨q, hq, ?_⟩
  rw [getW_eq, hrl]
  simp [castW, hp]

/-- A step at an instruction that is no move, advancing the program counter and keeping the
    frame words of the array pointers, keeps the save, reload and entry-held components of
    the relation. -/
theorem saved_reload_nextW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa sa' : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hnm : slotMov? bi.li_i = none)
    (hpc : sa'.reg.lpc = sa.reg.lpc + 1)
    (hmem : ∀ q a, (slotArr q).isSome = true → frame q = some a →
      read64 sa'.mem a = read64 sa.mem a)
    (hreg : ∀ b, frame b = none → b ∉ dstNames bi.li_i → sa'.reg.lvm b = sa.reg.lvm b) :
    (∀ k R A n a, SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
      frame (slotOfReg R) = some a →
        (k < sa'.reg.lpc → read64 sa'.mem a = base A)
          ∧ (sa'.reg.lpc ≤ k → sa'.reg.getW R 64 = some (base A)))
    ∧ (∀ b q a A n, reloadOf slotArr body sa'.reg.lpc b = some q →
      slotArr q = some (A, n) → frame q = some a → frame b = none →
        sa'.reg.lvm b = ⟨64, read64 sa'.mem a⟩)
    ∧ HeldAt frame slotArr base sa'.mem := by
  refine ⟨fun k R A n a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩, fun b q a A n hbi _ _ _ => ?_,
    fun R A n a hR hA ha => (hmem _ a (by rw [hA]; rfl) ha).trans (hrel.held R A n a hR hA ha)⟩
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
  · rename_i hq ha hbf
    rw [hpc] at hbi
    obtain ⟨ds, o, ss, hx, hnd, h'⟩ := reloadOf_succ_none_eq hb hnm b hbi
    have hbd : b ∉ dstNames bi.li_i := by rw [hx]; exact not_mem_dstNames_of_dstHit hnd
    rw [hreg b hbf hbd, hmem q a (by rw [hq]; rfl) ha]
    exact hrel.reload b q a A n h' hq ha hbf

theorem regGateBW_slotMov {frame : String → Option (BitVec 64)} {W : List String}
    {x : LinstrR} (h : regGateBW frame W x = true) {d src : String}
    (hm : slotMov? x = some (d, src)) : frame d = none ∧ frame src = none := by
  simp only [regGateBW, regOkB, Bool.and_eq_true] at h
  have h1 := h.1.1.1.2
  rw [hm] at h1
  simpa using h1

/-! ## 4. Register instructions -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (baseOf fstepA_of_reg fstepA_of_reg_some)

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
      ∧ (∀ r, gpOk r = true → r ∉ regOut W x → (sa'.reg.lvm r).1 = 64)
      ∧ (∀ r, gpOk r = true → ((sa.reg.lvm r).1 = 64 ∨ (sa.reg.lvm r).1 = 1) →
          (sa'.reg.lvm r).1 = 64 ∨ (sa'.reg.lvm r).1 = 1) := by
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
      fun r hr => ?_, hcf, hof, ?_, hlpc, ?_, fun r hr hrW => ?_, fun r hr h01 => ?_⟩
    · refine fstepA_of_reg_some frame rfl hmov' hcmp' hcell' hsc' hsi' hsv' ?_
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
        rcases hwg r hw with (h1 | h1) | h1
        · rw [hr] at h1; cases h1
        · exact wid64WB_ev h1 _ _ _ hwid
        · refine absurd ?_ hrW
          simp only [regOut, hS, List.mem_append, List.mem_filter]
          exact Or.inr ⟨hw, h1⟩
      · have e := hkeep' r hw
        simp only at e
        rw [e]
        refine hwid r hr fun hm => hrW ?_
        simp only [regOut, hS, List.mem_append, List.mem_filter, hm, true_and]
        exact Or.inl (by simpa using hw)
    · show (b.reg.lvm r).1 = 64 ∨ (b.reg.lvm r).1 = 1
      by_cases hw : r ∈ ss.wr
      · have e := hval r
        simp only at e
        rw [e]
        rcases hwg r hw with (h1 | h1) | h1
        · rw [hr] at h1; cases h1
        · exact Or.inl (wid64WB_ev h1 _ _ _ hwid)
        · exact Or.inr (STerm.wknown_ev _ _ _ _ (by simpa using h1))
      · have e := hkeep' r hw
        simp only at e
        rw [e]
        exact h01

theorem oneBitStep_noCarry {frame : String → Option (BitVec 64)} {W : List String}
    {x : LinstrR} (hci : carryI? x = none) :
    oneBitStep frame W x = match icase frame x with
      | .ldx d _ _ => W.filter (· != d)
      | .sload d q => if W.contains q then d :: W else W.filter (· != d)
      | .sstore q S => if W.contains S then q :: W else W
      | .reg =>
          match movImmStruct? x with
          | some (d, _) => d :: W
          | none => regOut W (normA x)
      | .other => castOut W x
      | _ => W := by
  simp only [oneBitStep, hci]

/-- The address state `sa` with the values of the image register file `img` at every name
    without a frame word. -/
def shadowA (frame : String → Option (BitVec 64)) (img : LstateN) (sa : LstateA) : LstateA :=
  { sa with reg := { sa.reg with
      lvm := fun r => if frame r = none then img.lvm r else sa.reg.lvm r } }

/-- A general-purpose name an instruction reads (`readsI`) is a name of `readNames`. -/
theorem readNames_of_readsI {ds : List LOperand} {o : String} {ss : List LOperand} {r : String}
    (hr : readsI (.Lopn ds o ss) r) (hg : gpOk r = true) : r ∈ readNames (.Lopn ds o ss) := by
  rcases hr with rfl | ⟨rfl, hx⟩ | hr' | hr'
  · exact absurd hg (by decide)
  · simp [readNames, hx]
  · exact List.mem_append_right _ (List.mem_append_left _ hr')
  · exact List.mem_append_right _ (List.mem_append_right _ hr')

/-- A one-bit name an instruction reads (`carryIns`) is the carry-in of `ADCX:64` or
    `ADCXHI:64` or the condition of `CMOV:64`. -/
theorem carryIns_cases {x : LinstrR} {r : String} (h : r ∈ carryIns x) :
    ∃ d m a s c, x = .Lopn [.reg d] m [.reg a, .reg s, .reg c]
      ∧ (((m = "ADCX:64" ∨ m = "ADCXHI:64") ∧ r = c) ∨ (m = "CMOV:64" ∧ r = a)) := by
  unfold carryIns at h
  split at h
  · split_ifs at h with h1 h2
    · simp only [List.mem_singleton] at h
      exact ⟨_, _, _, _, _, rfl, Or.inl ⟨h1, h⟩⟩
    · simp only [List.mem_singleton] at h
      exact ⟨_, _, _, _, _, rfl, Or.inr ⟨h2, h⟩⟩
    · simp at h
  · simp at h

/-- The flag machine steps a register move `MOVQ d, q` or `MOV:64 d, q` by copying the value
    of `q` to `d`. -/
theorem fstepF_slotMov (P : LprogM) {x : LinstrR} {d q : String} (h : slotMov? x = some (d, q))
    (m : LstateM) (zf : Bool) :
    fstepF (x, .reg none) m zf = some ((m.setReg d (m.reg.lvm q).2).nextPc, zf) := by
  have hl : IsLopn (x, MemTag.reg none) := by
    rcases slotMov?_cases h with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  have e := eval_slotMov P h (.reg none) ⟨⟨m, ""⟩, zf⟩
  rw [evalInstrPMemF_isLopn P _ _ hl] at e
  obtain ⟨⟨b, z⟩, hbz, he⟩ := Option.map_eq_some_iff.mp e
  simp only [LstateMF.mk.injEq, LstatePM.mk.injEq] at he
  obtain ⟨⟨rfl, -⟩, rfl⟩ := he
  exact hbz

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
  simp [icase, slotMov?, slotCmp?, carryI?, width_tag, castTagW]

/-- **A carry constant keeps `ImgRelW`.** The image and the address machine step the
    immediate move `om D, #n` (`om` is `MOV` or `MOV^w`, `w ≠ 64`), which `normA` reads as
    the untagged `MOV D, #n`, at the one-bit tag by writing the bit `n` to `D`, which enters
    the width analysis. -/
theorem rel_bmovW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {D om : String} {n : Nat}
    (hx : bi.li_i = .Lopn [.reg D] om [.imm n]) (hmo : isMovImmMnem om = true)
    (hic : icase frame bi.li_i = .reg) (hci : carryI? bi.li_i = none) (hD : frame D = none)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg (some 1)) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg (some 1)) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hnA : normA bi.li_i = .Lopn [.reg D] "MOV" [.imm n] := by
    rw [hx]; exact normA_movImm hmo
  have ho64 : om ≠ "MOV:64" := fun e => by rw [e, isMovImmMnem_mov64] at hmo; cases hmo
  have hbs : bitStore? body sa.reg.lpc bi.li_i = none := by
    rw [hx]
    exact bitStore?_of_ne fun d m h => ho64 (by injection h)
  have hic' : icase frame (.Lopn [.reg D] om [.imm n]) = .reg := hx ▸ hic
  have hci' : carryI? (.Lopn [.reg D] om [.imm n]) = none := hx ▸ hci
  have hl : IsLopn (normA bi.li_i, MemTag.reg (some 1)) := by rw [hnA]; exact ⟨_, _, _, rfl⟩
  rw [evalInstrPMemF_isLopn P _ s hl, hnA, fstepF_bitMov] at hs
  obtain rfl := Option.some.inj hs
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  refine ⟨{ sa with reg := (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc }, ?_, ⟨?_, ?_, ?_, ?_,
    hrel.cf, hrel.of, ?_, ?_, ?_, ?_, hrel.held,
    bits_setReg hrel.bits D (BitVec.ofNat 1 n) (Or.inr rfl)⟩⟩
  · rw [hnA, CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun.fstepA_bitMov _ D n sa zf hD,
      hrel.zf]
  · simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hrel.pc]
  · intro r hr
    by_cases hrD : r = D
    · subst hrD
      exact Or.inl (by simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc])
    · refine (hrel.regs r hr).of_eq
        (by simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hrD])
        (by simp [LstateN.setReg, LstateN.nextPc, hrD]) fun h => ?_
      have hpc : (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc = sa.reg.lpc + 1 := by
        simp [LstateN.setReg, LstateN.nextPc]
      change r ∈ oneBitAt frame body (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc
      rw [hpc, oneBitAt_succ hb hbs (seedAt_of_eq hx (by simp)), hx]
      simp only [oneBitStep, hci', hic', movImmStruct?, hmo, ite_true, List.mem_cons]
      exact Or.inr h
  · intro q a ha
    have hqD : q ≠ D := fun e => by rw [e, hD] at ha; cases ha
    refine (hrel.slots q a ha).of_eq
      (by simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hqD]) rfl
      fun h => ?_
    have hpc : (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc = sa.reg.lpc + 1 := by
      simp [LstateN.setReg, LstateN.nextPc]
    change q ∈ oneBitAt frame body (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc
    rw [hpc, oneBitAt_succ hb hbs (seedAt_of_eq hx (by simp)), hx]
    simp only [oneBitStep, hci', hic', movImmStruct?, hmo, ite_true, List.mem_cons]
    exact Or.inr h
  · rfl
  · intro r hr hW
    have hpc : (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc = sa.reg.lpc + 1 := by
      simp [LstateN.setReg, LstateN.nextPc]
    rw [hpc, oneBitAt_succ hb hbs (seedAt_of_eq hx (by simp)), hx] at hW
    simp only [oneBitStep, hci', hic', movImmStruct?, hmo, ite_true, List.mem_cons, not_or] at hW
    show ((sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lvm r).1 = 64
    simp only [LstateN.setReg, LstateN.nextPc, ite_eq_right hW.1]
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
  · intro b q a A m hbi hq ha hbf
    have hpc' : (sa.reg.setReg D (BitVec.ofNat 1 n)).nextPc.lpc = sa.reg.lpc + 1 := by
      simp [LstateN.setReg, LstateN.nextPc]
    rw [hpc'] at hbi
    obtain ⟨ds, o, ss, hx', hnd, h'⟩ := reloadOf_succ_none_eq hb hnm b hbi
    have hbd : b ∉ dstNames bi.li_i := by rw [hx']; exact not_mem_dstNames_of_dstHit hnd
    have hbD : b ≠ D := fun e => hbd (by rw [hx]; simp [e, dstNames, JasminLsemExportRewrites.opNames])
    have := hrel.reload b q a A m h' hq ha hbf
    simpa [LstateN.setReg, LstateN.nextPc, hbD] using this

/-- The flag machine steps a width-carrying cast at its descriptor tag by writing the value of
    the source at the descriptor width to the destination. -/
theorem fstepF_castW (D A o : String) (w' : Nat)
    (hcs : castStruct? (.Lopn [.reg D] o [.reg A]) = some (D, A)) (m : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg D] o [.reg A], .reg (some w')) m zf
      = some ((m.setReg D ((m.reg.lvm A).2.zeroExtend w')).nextPc, zf) := by
  have hop : o = "ZEROEXT" ∨ o = "TRUNC" ∨ o = "CASTW_32_32" ∨ o = "CASTW_32_64"
      ∨ o = "CASTW_64_32" ∨ o = "CASTW_64_64" ∨ o = "CASTW_64_16"
      ∨ o = "CASTW_16_64" ∨ o = "CASTW_16_16" ∨ o = "CASTW_16_32"
      ∨ o = "CASTW_32_16" := by
    simp only [castStruct?] at hcs
    split at hcs
    · assumption
    · cases hcs
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem,
      lsemStepCast, castStruct?, withALUFlags, aluFlagOp?, readReg] <;> rfl

/-- A width-carrying cast is no carry-chain instruction, no register instruction of the image
    gate, no immediate move and no frame-word move. -/
theorem cast_facts (frame : String → Option (BitVec 64)) {x : LinstrR} {d a : String}
    {m w : Nat} (h : classifyK x = some (d, a, m, w)) :
    ∃ o, x = .Lopn [.reg d] o [.reg a] ∧ LprogBytes.castMovBits o = some m
      ∧ castTagW o = some w ∧ carryI? x = none ∧ icase frame x = .other
      ∧ movImmStruct? x = none ∧ slotMov? x = none := by
  obtain ⟨o, rfl, hm, hw⟩ := classifyK_spec h
  have h1 : o ≠ "MOVQ" := by rintro rfl; simp [castTagW] at hw
  have h2 : o ≠ "MOV:64" := by rintro rfl; simp [castTagW] at hw
  refine ⟨o, rfl, hm, hw, by simp [carryI?], by simp [icase, hw,
    LprogAsmPrinter.untagCaret_of_caret_free (castTagW_caret_free hw)], by simp [movImmStruct?], ?_⟩
  simp [slotMov?, h1, h2]

/-- **A width-carrying cast keeps `ImgRelW`.** The image and the address machine step the
    cast `o D, A` between names without a frame word at the descriptor tag by writing the
    value of `A` at the destination width to `D`, which leaves the width analysis at the
    width `64` and enters it otherwise. -/
theorem rel_castW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {D A : String} {m w : Nat}
    (hk : classifyK bi.li_i = some (D, A, m, w)) (hD : frame D = none) (hA : frame A = none)
    (hs : evalInstrPMemF P (bi.li_i, .reg (some w)) s = some t) :
    ∃ sa', fstepA frame (bi.li_i, .reg (some w)) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨o, hx, hm, hw, hci, hic, hmi, hnm⟩ := cast_facts frame hk
  have hcs := castStruct?_of_castMovBits hm D A
  have hl : IsLopn (bi.li_i, MemTag.reg (some w)) := by rw [hx]; exact ⟨_, _, _, rfl⟩
  rw [evalInstrPMemF_isLopn P _ s hl, hx, fstepF_castW D A o w hcs] at hs
  obtain rfl := Option.some.inj hs
  have hAv : (s.prog.base.reg.lvm A).2.zeroExtend w = (sa.reg.lvm A).2.zeroExtend w := by
    rcases hrel.regs A hA with h | ⟨-, -, b, h1, h2⟩
    · rw [h]
    · rw [h1, h2]
      show BitVec.zeroExtend w b = BitVec.zeroExtend w (b.setWidth 64)
      simp only [BitVec.zeroExtend_eq_setWidth]
      rw [BitVec.setWidth_setWidth (by omega)]
  have hbs : bitStore? body sa.reg.lpc bi.li_i = none := by
    rw [hx]; exact bitStore?_of_ne (by simp)
  have hstepW : oneBitAt frame body (sa.reg.lpc + 1)
      = if w = 64 then (oneBitAt frame body sa.reg.lpc).filter (· != D)
        else D :: oneBitAt frame body sa.reg.lpc := by
    rw [oneBitAt_succ hb hbs (seedAt_of_eq hx (by simp))]
    simp only [oneBitStep, hci, hic, castOut, hk]
  have hpc : (sa.reg.setReg D ((sa.reg.lvm A).2.zeroExtend w)).nextPc.lpc = sa.reg.lpc + 1 := by
    simp [LstateN.setReg, LstateN.nextPc]
  refine ⟨{ sa with reg := (sa.reg.setReg D ((sa.reg.lvm A).2.zeroExtend w)).nextPc }, ?_, ⟨?_,
    ?_, ?_, ?_, hrel.cf, hrel.of, ?_, ?_, ?_, ?_, hrel.held, fun r hr hc => ?_⟩⟩
  rotate_right
  · by_cases e : r = D
    · subst e
      by_cases hw64 : w = 64
      · left
        simp [LstateN.setReg, LstateN.nextPc, hw64]
      · exact absurd (mem_castDsts hb hk hw64) hc
    · simpa [LstateN.setReg, LstateN.nextPc, e] using hrel.bits r hr hc
  · rw [hx, fstepA_castW _ D A o w hcs, lsemStepCast_castW D A o w hcs, hrel.zf]
    rfl
  · simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hrel.pc]
  · intro r hr
    by_cases hrD : r = D
    · subst hrD
      refine Or.inl ?_
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, ite_true]
      rw [hAv]
    · refine (hrel.regs r hr).of_eq
        (by simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hrD])
        (by simp [LstateN.setReg, LstateN.nextPc, hrD]) fun h => ?_
      change r ∈ oneBitAt frame body (sa.reg.setReg D ((sa.reg.lvm A).2.zeroExtend w)).nextPc.lpc
      rw [hpc, hstepW]
      split_ifs
      · exact List.mem_filter.2 ⟨h, by simpa using hrD⟩
      · exact List.mem_cons_of_mem _ h
  · intro q a ha
    have hqD : q ≠ D := fun e => by rw [e, hD] at ha; cases ha
    refine (hrel.slots q a ha).of_eq
      (by simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hqD]) rfl
      fun h => ?_
    change q ∈ oneBitAt frame body (sa.reg.setReg D ((sa.reg.lvm A).2.zeroExtend w)).nextPc.lpc
    rw [hpc, hstepW]
    split_ifs
    · exact List.mem_filter.2 ⟨h, by simpa using hqD⟩
    · exact List.mem_cons_of_mem _ h
  · rfl
  · intro r hr hW
    rw [hpc, hstepW] at hW
    show ((sa.reg.setReg D ((sa.reg.lvm A).2.zeroExtend w)).nextPc.lvm r).1 = 64
    by_cases hrD : r = D
    · subst hrD
      split_ifs at hW with h64
      · subst h64
        simp [LstateN.setReg, LstateN.nextPc]
      · exact absurd (List.mem_cons_self) hW
    · simp only [LstateN.setReg, LstateN.nextPc, ite_eq_right hrD]
      refine hrel.wid r hr ?_
      split_ifs at hW
      · exact not_mem_filter_ne hW hrD
      · exact fun h => hW (List.mem_cons_of_mem _ h)
  · intro q A' n hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq
    exact ⟨arr, h1, h2⟩
  · intro k R A' n a hS hA' ha
    show (k < (sa.reg.setReg D ((sa.reg.lvm A).2.zeroExtend w)).nextPc.lpc → _) ∧
      ((sa.reg.setReg D ((sa.reg.lvm A).2.zeroExtend w)).nextPc.lpc ≤ k → _)
    rw [hpc]
    refine ⟨fun hk' => ?_, fun hk' => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
      · exact (hrel.saved k R A' n a hS hA' ha).1 hk'
      · exfalso
        obtain ⟨i', hi', hm'⟩ := hS
        rw [hb] at hi'
        cases hi'
        rw [hnm] at hm'
        cases hm'
    · exfalso
      obtain ⟨i', hi', hm'⟩ := hS
      have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA']; rfl)).2
      obtain ⟨d, src, hm2, -⟩ := entryRegB_spec hent (show sa.reg.lpc < k by omega) hb
      rw [hnm] at hm2
      cases hm2
  · intro b q a A' n hbi hq ha hbf
    rw [hpc] at hbi
    obtain ⟨ds, o', ss, hx', hnd, h'⟩ := reloadOf_succ_none_eq hb hnm b hbi
    have hbd : b ∉ dstNames bi.li_i := by rw [hx']; exact not_mem_dstNames_of_dstHit hnd
    have hbD : b ≠ D := fun e => hbd (by
      rw [hx]; simp [e, dstNames, JasminLsemExportRewrites.opNames])
    have := hrel.reload b q a A' n h' hq ha hbf
    simpa [LstateN.setReg, LstateN.nextPc, hbD] using this

/-! ## 5. Frame-word moves and compares, indexed accesses, labels -/

/-- **A load of a frame word keeps `ImgRelW`**, for a frame word outside the width analysis
    or one that no untagged immediate move of the body writes (`movlNames`). The image copies
    the value of the frame-word name `q` to `d`, the address machine the word at the frame
    address of `q`: the same value, or, for a frame word of the analysis holding a bit, the bit
    on the image and its zero-extension on the address machine, and then `d` enters the
    analysis. -/
theorem rel_sloadW_gen {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d q : String} (hc : icase frame bi.li_i = .sload d q)
    (hci : carryI? bi.li_i = none) (hgd : gpOk d = true)
    (hqN : q ∈ oneBitAt frame body sa.reg.lpc → q ∉ movlNames body)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨hm, hd, hq⟩ := icase_sload hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_slotMov hm)
    (seedAt_of_slotMov hm)
  rw [oneBitStep_noCarry hci, hc] at hW1
  simp only at hW1
  have hWk : ∀ r, r ≠ d → r ∈ oneBitAt frame body sa.reg.lpc →
      r ∈ oneBitAt frame body (sa.reg.lpc + 1) := by
    intro r e h
    rw [hW1]
    split
    · exact List.mem_cons_of_mem _ h
    · exact List.mem_filter.2 ⟨h, by simpa using e⟩
  have hWn : ∀ r, r ≠ d → r ∉ oneBitAt frame body (sa.reg.lpc + 1) →
      r ∉ oneBitAt frame body sa.reg.lpc := fun r e h h' => h (hWk r e h')
  rw [normA_of_slotMov hm] at hs ⊢
  rw [eval_slotMov P hm] at hs
  cases hs
  have hz := hrel.zf
  subst hz
  refine ⟨{ sa with reg := (sa.reg.setReg d (read64 sa.mem a)).nextPc },
    fstepA_slotLoad frame hm ha sa _, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_,
      hrel.held, bits_setReg hrel.bits d _ (Or.inl rfl)⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    by_cases e : r = d
    · subst e
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg,
        ite_true, LstateN.lpc_nextPc, LstateN.lpc_setReg]
      rcases hrel.slots q a ha with h | ⟨hqW, h, hz⟩
      · exact Or.inl (by rw [h])
      · refine Or.inr ⟨?_, hgd, (read64 sa.mem a).setWidth 1, by rw [h], ?_⟩
        · rw [hW1, ite_eq_left (by simpa using hqW)]
          exact List.mem_cons_self
        · rw [hz (hqN hqW)]
    · exact (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e])
        (by simp [e]) (hWk r e)
  · intro q' a' ha'
    have e : q' ≠ d := fun e => by rw [e, hd] at ha'; cases ha'
    exact (hrel.slots q' a' ha').of_eq (by simp [LstateM.setReg, LstateM.nextPc, e]) rfl
      (hWk q' e)
  · intro r hr hW
    simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg] at hW
    by_cases e : r = d
    · subst e; simp
    · simp [e, hrel.wid r hr (hWn r e hW)]
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
  · refine reload_succ hrel.reload hb (by simp) (fun r h => hsep.gp r h) (hsep.slotFrameB)
      (fun b q' a' A n hm' _ hq' _ => ?_)
      (fun b q' hm' hg _ => by
        rw [hm] at hm'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
        rw [hsep.gp _ hg] at ha; cases ha)
      (fun d' q0 b hm' _ hbd _ => ?_) (fun _ _ _ _ _ _ _ _ _ _ => rfl)
      (fun h' => by rw [hm] at h'; cases h') (fun h' => by rw [hm] at h'; cases h')
    · rw [hm] at hm'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
      rw [ha] at hq'
      cases hq'
      simp
    · rw [hm] at hm'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
      simp [hbd]

/-- **A load of a frame word outside the width analysis keeps `ImgRelW`**: both machines
    copy the word to `d`. -/
theorem rel_sloadW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d q : String} (hc : icase frame bi.li_i = .sload d q)
    (hci : carryI? bi.li_i = none) (hgd : gpOk d = true)
    (hqW : q ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf :=
  rel_sloadW_gen hsep hphys P hrel hb hc hci hgd (fun h => absurd h hqW) hs

/-- **The reload of a spilled bit keeps `ImgRelW`.** At `MOV:64 d, q` (or `MOVQ d, q`) with
    `q` a frame word of the width analysis that no untagged immediate move of the body writes,
    the image copies the value of `q` to `d`, the address machine the word at the frame
    address of `q`: where the image holds a bit, the word is its zero-extension (`SlotVal`),
    so `d` holds the bit on the image and its zero-extension on the address machine
    (`RegVal`), and `d` enters the width analysis (`oneBitStep`). -/
theorem rel_sloadW1 {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d q : String} (hc : icase frame bi.li_i = .sload d q)
    (hci : carryI? bi.li_i = none) (hgd : gpOk d = true)
    (hqW : q ∈ oneBitAt frame body sa.reg.lpc) (hqN : q ∉ movlNames body)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf
      ∧ d ∈ oneBitAt frame body (sa.reg.lpc + 1) := by
  obtain ⟨sa', h1, h2⟩ := rel_sloadW_gen hsep hphys P hrel hb hc hci hgd (fun _ => hqN) hs
  refine ⟨sa', h1, h2, ?_⟩
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_slotMov (icase_sload hc).1)
    (seedAt_of_slotMov (icase_sload hc).1)
  rw [oneBitStep_noCarry hci, hc] at hW1
  simp only at hW1
  rw [hW1, ite_eq_left (by simpa using hqW)]
  exact List.mem_cons_self

/-- **A store into a frame word keeps `ImgRelW`**, for a stored name outside the width
    analysis, or one that no cast of the body writes at a narrow width (`castDsts`): such a
    name holds a 64-bit word, stored whole, or a bit, stored zero-extended, and the frame word
    then enters the width analysis. -/
theorem rel_sstoreW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {q S : String} (hc : icase frame bi.li_i = .sstore q S)
    (hci : carryI? bi.li_i = none) (hgS : gpOk S = true)
    (hSW : S ∉ oneBitAt frame body sa.reg.lpc ∨ S ∉ castDsts body)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨hm, hS, hq⟩ := icase_sstore hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_slotMov hm)
    (seedAt_of_slotMov hm)
  rw [oneBitStep_noCarry hci, hc] at hW1
  simp only at hW1
  have hWsub : ∀ r, r ∈ oneBitAt frame body sa.reg.lpc →
      r ∈ oneBitAt frame body (sa.reg.lpc + 1) := by
    intro r hr
    rw [hW1]
    split <;> simp [hr]
  rw [normA_of_slotMov hm] at hs ⊢
  rw [eval_slotMov P hm] at hs
  cases hs
  have hz := hrel.zf
  subst hz
  have hw01 : (sa.reg.lvm S).1 = 64 ∨ (sa.reg.lvm S).1 = 1 := by
    rcases hSW with h | h
    · exact Or.inl (hrel.wid S hgS h)
    · exact hrel.bits S hgS h
  obtain ⟨v, hst, hslot, hsav⟩ : ∃ v : BitVec 64,
      fstepA frame (bi.li_i, .reg none) sa s.zf
        = some ({ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a v }, s.zf)
      ∧ SlotVal (movlNames body) (oneBitAt frame body (sa.reg.lpc + 1)) q
          (s.prog.base.reg.lvm S) v
      ∧ ∀ p, sa.reg.getW S 64 = some p → v = p := by
    rcases hw01 with hw | hw
    · have hv : sa.reg.getW S 64 = some (castW (sa.reg.lvm S) 64) := by
        rw [getW_eq, ite_eq_left hw]
      refine ⟨castW (sa.reg.lvm S) 64, fstepA_slotStore frame hm hS ha sa _ hv, ?_,
        fun p hp => by rw [hv] at hp; exact Option.some.inj hp⟩
      rcases hrel.regs S hS with h | ⟨hSW', -, b, h1, h2⟩
      · exact Or.inl (by rw [h, sigma_of_castW hw])
      · -- a reloaded bit, held as its zero-extension, is stored as that word
        have hcw : castW (sa.reg.lvm S) 64 = b.setWidth 64 := by
          rw [h2]; rfl
        rw [hcw, h1]
        refine Or.inr ⟨?_, by simp, fun _ => by simp⟩
        rw [hW1]
        simp [hSW']
    · generalize hc1 : sa.reg.lvm S = c at hw
      obtain ⟨w, b⟩ := c
      simp only at hw
      subst hw
      have hSW' : S ∈ oneBitAt frame body sa.reg.lpc := by
        by_contra hn
        have := hrel.wid S hgS hn
        rw [hc1] at this
        cases this
      have hSv : s.prog.base.reg.lvm S = ⟨1, b⟩ := by
        rcases hrel.regs S hS with h | ⟨-, -, b', -, h2⟩
        · rw [h, hc1]
        · rw [hc1] at h2; cases h2
      refine ⟨b.setWidth 64, fstepA_slotStore1 frame hm hS ha sa _ hc1, ?_,
        fun p hp => by rw [getW_eq_some_iff, hc1] at hp; cases hp⟩
      rw [hSv]
      refine SlotVal.of_zext ?_ b
      rw [hW1]
      simp [hSW']
  refine ⟨{ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a v }, hst,
    ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_, ?_,
      fun r hr hc => by simpa using hrel.bits r hr hc⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    have e : r ≠ q := fun e => by rw [e, ha] at hr; cases hr
    exact (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e]) (by simp)
      (fun h => by simpa using hWsub r h)
  · intro q' a' ha'
    by_cases e : q' = q
    · subst e
      rw [ha] at ha'
      cases ha'
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, ite_true,
        read64_write64_same, LstateN.lpc_nextPc]
      exact hslot
    · simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
        ite_false]
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' ha ha' (Ne.symm e))]
      exact (hrel.slots q' a' ha').of_eq rfl rfl fun h => by simpa using hWsub q' h
  · intro r hr hW
    simp only [LstateN.lpc_nextPc] at hW
    simpa using hrel.wid r hr fun h => hW (hWsub r h)
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
        exact hsav _ ((hrel.saved sa.reg.lpc R A n a ⟨bi, hb, hm⟩ hA ha).2 (le_refl _))
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
  · refine reload_succ hrel.reload hb (by simp) (fun r h => hsep.gp r h) (hsep.slotFrameB)
      (fun b q' a' A n hm' _ _ hbf => ?_)
      (fun b q' hm' _ hbf => by
        rw [hm] at hm'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
        rw [ha] at hbf; cases hbf)
      (fun _ _ _ _ _ _ _ => by simp) (fun d q0 q' a' A n hm' hd hq' ha' => ?_)
      (fun h' => by rw [hm] at h'; cases h') (fun h' => by rw [hm] at h'; cases h')
    · rw [hm] at hm'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
      rw [ha] at hbf
      cases hbf
    · rw [hm] at hm'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
      have hne : q ≠ q' := fun e => by rw [e, hq'] at hd; cases hd
      exact read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' ha ha' hne)
  · intro R A n a' hR hA ha'
    by_cases hqR : slotOfReg R = q
    · exfalso
      rw [← hqR] at hm
      obtain ⟨hqS, -⟩ := physImgB_slotStore hphys hb hm (by rw [hA]; rfl)
      have h0 := abiStackOff?_of_gpOk hgS
      rw [← slotOfReg_inj hqS] at h0
      rw [h0] at hR
      cases hR
    · show read64 (write64 sa.mem a _) a' = base A
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q _ a a' ha ha' (Ne.symm hqR))]
      exact hrel.held R A n a' hR hA ha'

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
    (hA : slotArr q = none) (hbs : bitStore? body sa.reg.lpc bi.li_i = none)
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
  have hW1 := oneBitAt_succ (frame := frame) hb hbs (seedAt_of_eq hx (by simp))
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  refine ⟨{ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a (BitVec.ofNat 64 v) },
    fstepA_slotImm frame hq v none sa s.zf, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_,
      fun R A' n' a' hR hA' ha' => by
        have hqR : slotOfReg R ≠ q := fun e => by rw [e, hA] at hA'; cases hA'
        show read64 (write64 sa.mem a _) a' = base A'
        rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q _ a a' hq ha' (Ne.symm hqR))]
        exact hrel.held R A' n' a' hR hA' ha',
      fun r hr hc => by simpa using hrel.bits r hr hc⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    have e : r ≠ q := fun e => by rw [e, hq] at hr; cases hr
    refine (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e]) (by simp)
      fun h => ?_
    have hci : carryI? bi.li_i = none := by rw [hx]; simp [carryI?]
    have hic : icase frame bi.li_i = .reg := by
      rw [hx]; simp (config := { decide := true }) [icase, slotMov?, slotCmp?, normA_of_caret_free]
    have hmi : movImmStruct? bi.li_i = none := by
      rw [hx]; simp [movImmStruct?, isMovImmMnem_mov64]
    simp only [LstateN.lpc_nextPc, hW1, oneBitStep_noCarry hci, hic, hmi, hnA]
    by_contra hn
    exact regOut_slotImm _ q v e hn h
  · intro q' a' ha'
    by_cases e : q' = q
    · subst e
      rw [hq] at ha'
      cases ha'
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, ite_true,
        read64_write64_same]
      exact Or.inl rfl
    · simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
        ite_false]
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' hq ha' (Ne.symm e))]
      refine (hrel.slots q' a' ha').of_eq rfl rfl fun h => ?_
      have hci : carryI? bi.li_i = none := by rw [hx]; simp [carryI?]
      have hic : icase frame bi.li_i = .reg := by
        rw [hx]; simp (config := { decide := true }) [icase, slotMov?, slotCmp?, normA_of_caret_free]
      have hmi : movImmStruct? bi.li_i = none := by
        rw [hx]; simp [movImmStruct?, isMovImmMnem_mov64]
      simp only [LstateN.lpc_nextPc, hW1, oneBitStep_noCarry hci, hic, hmi, hnA]
      by_contra hn
      exact regOut_slotImm _ q v e hn h
  · intro r hr hW
    have hci : carryI? bi.li_i = none := by rw [hx]; simp [carryI?]
    have hic : icase frame bi.li_i = .reg := by
      rw [hx]; simp (config := { decide := true }) [icase, slotMov?, slotCmp?, normA_of_caret_free]
    have hmi : movImmStruct? bi.li_i = none := by
      rw [hx]; simp [movImmStruct?, isMovImmMnem_mov64]
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
  · intro b q' a' A' n' hbi hq' ha' hbf
    simp only [LstateN.lpc_nextPc] at hbi
    obtain ⟨ds, o, ss, hx', hnd, h'⟩ := reloadOf_succ_none_eq hb hnm b hbi
    have hqq : q ≠ q' := fun e => by rw [e, hq'] at hA; cases hA
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' hq ha' hqq)]
    simpa using hrel.reload b q' a' A' n' h' hq' ha' hbf

/-- **A carry constant into a frame word keeps `ImgRelW`.** The image steps the immediate move
    `om q, #n` (`om` is `MOV` or `MOV^w`, `w ≠ 64`), which `normA` reads as the untagged
    `MOV q, #n`, at the one-bit tag by writing the bit `n` to the frame-word name `q`, which
    enters the width analysis; the address machine writes the low 32 bits of `n` at the frame
    word of `q`, which holds no array pointer, so the low bit of the word is the bit `n`. -/
theorem rel_bmovSlotW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {q om : String} {n : Nat} {a : BitVec 64}
    (hx : bi.li_i = .Lopn [.reg q] om [.imm n]) (hmo : isMovImmMnem om = true)
    (hic : icase frame bi.li_i = .reg) (hci : carryI? bi.li_i = none) (hq : frame q = some a)
    (hA : slotArr q = none)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg (some 1)) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg (some 1)) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hnA : normA bi.li_i = .Lopn [.reg q] "MOV" [.imm n] := by
    rw [hx]; exact normA_movImm hmo
  have ho64 : om ≠ "MOV:64" := fun e => by rw [e, isMovImmMnem_mov64] at hmo; cases hmo
  have hbs : bitStore? body sa.reg.lpc bi.li_i = none := by
    rw [hx]
    exact bitStore?_of_ne fun d m h => ho64 (by injection h)
  have hic' : icase frame (.Lopn [.reg q] om [.imm n]) = .reg := hx ▸ hic
  have hci' : carryI? (.Lopn [.reg q] om [.imm n]) = none := hx ▸ hci
  have hl : IsLopn (normA bi.li_i, MemTag.reg (some 1)) := by rw [hnA]; exact ⟨_, _, _, rfl⟩
  rw [evalInstrPMemF_isLopn P _ s hl, hnA, fstepF_bitMov] at hs
  obtain rfl := Option.some.inj hs
  have hz := hrel.zf
  subst hz
  have hW1 := oneBitAt_succ (frame := frame) hb hbs (seedAt_of_eq hx (by simp))
  rw [hx] at hW1
  simp only [oneBitStep, hci', hic', movImmStruct?, hmo, ite_true] at hW1
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  obtain ⟨w, hw⟩ : ∃ w, w = (read64 sa.mem a &&& 0xFFFFFFFF00000000#64)
      ||| BitVec.ofNat 64 (n % 2 ^ 32) := ⟨_, rfl⟩
  have hlow : w.setWidth 1 = BitVec.ofNat 1 n := by
    rw [hw]; exact immWordA_mov_setWidth [.reg q] [.imm n] (read64 sa.mem a) n
  refine ⟨{ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a w },
    ?_, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_,
      fun R A' n' a' hR hA' ha' => by
        have hqR : slotOfReg R ≠ q := fun e => by rw [e, hA] at hA'; cases hA'
        show read64 (write64 sa.mem a _) a' = base A'
        rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q _ a a' hq ha' (Ne.symm hqR))]
        exact hrel.held R A' n' a' hR hA' ha',
      fun r hr hc => by simpa using hrel.bits r hr hc⟩⟩
  · rw [hnA, fstepA_slotBit frame hq n (some 1) sa s.zf, hw]
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    have e : r ≠ q := fun e => by rw [e, hq] at hr; cases hr
    refine (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e]) (by simp)
      fun h => ?_
    simp only [LstateN.lpc_nextPc, hW1]
    exact List.mem_cons_of_mem _ h
  · intro q' a' ha'
    by_cases e : q' = q
    · subst e
      rw [hq] at ha'
      cases ha'
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, ite_true,
        read64_write64_same]
      refine Or.inr ⟨?_, by rw [hlow], fun hn =>
        absurd (mem_movlNames (n := n) hb (by rw [hx]; simp [movImmStruct?, hmo])) hn⟩
      simp only [LstateN.lpc_nextPc, hW1]
      exact List.mem_cons_self
    · simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
        ite_false]
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' hq ha' (Ne.symm e))]
      refine (hrel.slots q' a' ha').of_eq rfl rfl fun h => ?_
      simp only [LstateN.lpc_nextPc, hW1]
      exact List.mem_cons_of_mem _ h
  · intro r hr hW
    simp only [LstateN.lpc_nextPc, hW1, List.mem_cons, not_or] at hW
    simpa using hrel.wid r hr hW.2
  · intro q' A n' hq'
    obtain ⟨arr, h1, h2⟩ := hrel.cells q' A n' hq'
    refine ⟨arr, by simpa using h1, fun j hj => ?_⟩
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q' A n' j hq' hj q a hq).symm]
    exact h2 j hj
  · intro k R A n' a' hS' hA' ha'
    simp only [LstateN.lpc_nextPc]
    have hqR : slotOfReg R ≠ q := fun e => by rw [e, hA] at hA'; cases hA'
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q _ a a' hq ha' (Ne.symm hqR))]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (hrel.saved k R A n' a' hS' hA' ha').1 hk
      · exfalso
        obtain ⟨i', hi', hm'⟩ := hS'
        rw [hb] at hi'
        cases hi'
        rw [hnm] at hm'
        cases hm'
    · rw [getW_congr (r := sa.reg.nextPc) (r' := sa.reg) rfl]
      exact (hrel.saved k R A n' a' hS' hA' ha').2 (by omega)
  · intro b q' a' A' n' hbi hq' ha' hbf
    simp only [LstateN.lpc_nextPc] at hbi
    obtain ⟨ds, o, ss, hx', hnd, h'⟩ := reloadOf_succ_none_eq hb hnm b hbi
    have hqq : q ≠ q' := fun e => by rw [e, hq'] at hA; cases hA
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' hq ha' hqq)]
    simpa using hrel.reload b q' a' A' n' h' hq' ha' hbf

/-- The low bit of the 64-bit word of `n` is the bit `n`. -/
theorem ofNat64_setWidth_one (n : Nat) : (BitVec.ofNat 64 n).setWidth 1 = BitVec.ofNat 1 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- **A stored carry constant keeps `ImgRelW`.** At a stored carry constant `MOV:64 q, #n`
    (`bitStore?`) into a frame word without an array pointer, the image steps the one-bit move
    `MOV q, #n` by writing the bit `n` to the frame-word name `q`, which enters the width
    analysis (`oneBitAt_succ_store`); the address machine writes the 64-bit word of `n` at the
    frame word of `q`, whose low bit is the bit `n`. -/
theorem rel_bstoreW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {q : String} {n : Nat} {a : BitVec 64}
    (hbs : bitStore? body sa.reg.lpc bi.li_i = some (q, n)) (hq : frame q = some a)
    (hA : slotArr q = none)
    (hs : evalInstrPMemF P (.Lopn [.reg q] "MOV" [.imm n], .reg (some 1)) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨hx, -⟩ := bitStore?_spec hbs
  have hnA : normA bi.li_i = .Lopn [.reg q] "MOV:64" [.imm n] := by
    rw [hx]; simp (config := { decide := true }) [normA]
  have hl : IsLopn (LinstrR.Lopn [.reg q] "MOV" [.imm n], MemTag.reg (some 1)) :=
    ⟨_, _, _, rfl⟩
  rw [evalInstrPMemF_isLopn P _ s hl, fstepF_bitMov] at hs
  obtain rfl := Option.some.inj hs
  have hz := hrel.zf
  subst hz
  have hW1 := oneBitAt_succ_store (frame := frame) hb hbs
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  refine ⟨{ sa with reg := sa.reg.nextPc, mem := write64 sa.mem a (BitVec.ofNat 64 n) },
    ?_, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_,
      fun R A' n' a' hR hA' ha' => by
        have hqR : slotOfReg R ≠ q := fun e => by rw [e, hA] at hA'; cases hA'
        show read64 (write64 sa.mem a _) a' = base A'
        rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q _ a a' hq ha' (Ne.symm hqR))]
        exact hrel.held R A' n' a' hR hA' ha',
      fun r hr hc => by simpa using hrel.bits r hr hc⟩⟩
  · rw [hnA, fstepA_slotImm frame hq n none sa s.zf]
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    have e : r ≠ q := fun e => by rw [e, hq] at hr; cases hr
    refine (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e]) (by simp)
      fun h => ?_
    simp only [LstateN.lpc_nextPc, hW1]
    exact List.mem_cons_of_mem _ h
  · intro q' a' ha'
    by_cases e : q' = q
    · subst e
      rw [hq] at ha'
      cases ha'
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, ite_true,
        read64_write64_same]
      have hn2 := (bitStore?_spec hbs).2.1
      refine Or.inr ⟨?_, by rw [ofNat64_setWidth_one], fun _ => ?_⟩
      · simp only [LstateN.lpc_nextPc, hW1]
        exact List.mem_cons_self
      · rw [ofNat64_setWidth_one]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega
    · simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
        ite_false]
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' hq ha' (Ne.symm e))]
      refine (hrel.slots q' a' ha').of_eq rfl rfl fun h => ?_
      simp only [LstateN.lpc_nextPc, hW1]
      exact List.mem_cons_of_mem _ h
  · intro r hr hW
    simp only [LstateN.lpc_nextPc, hW1, List.mem_cons, not_or] at hW
    simpa using hrel.wid r hr hW.2
  · intro q' A n' hq'
    obtain ⟨arr, h1, h2⟩ := hrel.cells q' A n' hq'
    refine ⟨arr, by simpa using h1, fun j hj => ?_⟩
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q' A n' j hq' hj q a hq).symm]
    exact h2 j hj
  · intro k R A n' a' hS' hA' ha'
    simp only [LstateN.lpc_nextPc]
    have hqR : slotOfReg R ≠ q := fun e => by rw [e, hA] at hA'; cases hA'
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q _ a a' hq ha' (Ne.symm hqR))]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (hrel.saved k R A n' a' hS' hA' ha').1 hk
      · exfalso
        obtain ⟨i', hi', hm'⟩ := hS'
        rw [hb] at hi'
        cases hi'
        rw [hnm] at hm'
        cases hm'
    · rw [getW_congr (r := sa.reg.nextPc) (r' := sa.reg) rfl]
      exact (hrel.saved k R A n' a' hS' hA' ha').2 (by omega)
  · intro b q' a' A' n' hbi hq' ha' hbf
    simp only [LstateN.lpc_nextPc] at hbi
    obtain ⟨ds, o, ss, hx', hnd, h'⟩ := reloadOf_succ_none_eq hb hnm b hbi
    have hqq : q ≠ q' := fun e => by rw [e, hq'] at hA; cases hA
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames q q' a a' hq ha' hqq)]
    simpa using hrel.reload b q' a' A' n' h' hq' ha' hbf

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
    simp only [hm, ite_true]
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

/-- **A select into a register keeps `ImgRelW`.** The image reads the values of
    `CMOV:64 D, [C, A, B]` from its names and its condition at width `1`, the address machine
    reads a frame-word value at its frame word and the condition through `bitA` (a reloaded
    bit held as its zero-extension is read as that bit); both write the select to `D`. -/
theorem rel_scmovW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {D C A B : String}
    (hx : bi.li_i = .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]) (hD : frame D = none)
    (hC : frame C = none) (hA : gpOk A = true ∨ (frame A).isSome = true)
    (hAW : A ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hnA : normA bi.li_i = .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B] := by
    rw [hx]; simp (config := { decide := true }) [normA]
  rw [hnA] at hs ⊢
  have hl : IsLopn (LinstrR.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], MemTag.reg none) :=
    ⟨_, _, _, rfl⟩
  have hword : ∀ x v, s.prog.base.reg.getW x 64 = some v → wordA frame sa x = some v := by
    intro x v hv
    unfold wordA
    split
    · rename_i ad hfa
      rw [(hrel.slots x ad hfa).getW64 hv]
    · rename_i hfa
      exact (hrel.regs x hfa).getW64 hv
  obtain ⟨va, hva⟩ : ∃ v, s.prog.base.reg.getW A 64 = some v := by
    cases hfa : frame A with
    | some ad => exact ⟨_, getW_eq_some_iff.2 ((hrel.slots A ad hfa).word hAW)⟩
    | none =>
      have hgA : gpOk A = true := by
        rcases hA with h | h
        · exact h
        · rw [hfa] at h; cases h
      have hw := hrel.wid A hgA hAW
      rw [← hrel.regsEq hfa hAW] at hw
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
  have hbC : bitA frame sa C = some vc := by
    rw [bitA_of_none hC]
    exact (hrel.regs C hC).regBit hgc
  have hstA : fstepA frame (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none) sa
      s.zf = some ({ sa with reg := (sa.reg.setReg D (JasminDialect.selectW vc va vb)).nextPc },
        s.zf) := by
    by_cases hsl : ((frame A).isSome || (frame B).isSome) = true
    · rw [fstepA_slotCmov frame hD hsl none sa s.zf (hword A va hva) (hword B vb hgb), hbC]
      rfl
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none] at hsl
      have hwa := hword A va hva
      have hwb := hword B vb hgb
      simp only [wordA, hsl.1, hsl.2] at hwa hwb
      rw [DecodePrintedAddrW.fstepA_cmovF frame D C A B hD hC hsl.1 hsl.2 sa s.zf hwa hwb,
        ← bitA_of_none hC, hbC]
      rfl
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hx (by simp))
    (seedAt_of_eq hx (by simp))
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  have hci : carryI? bi.li_i = none := by rw [hx]; simp [carryI?]
  have hic : icase frame bi.li_i = .reg := by
    rw [hx]; simp (config := { decide := true }) [icase, slotMov?, slotCmp?, normA_of_caret_free]
  have hmi : movImmStruct? bi.li_i = none := by rw [hx]; simp [movImmStruct?]
  have hWD : ∀ r, r ≠ D → r ∈ oneBitAt frame body sa.reg.lpc →
      r ∈ oneBitAt frame body (sa.reg.lpc + 1) := by
    intro r e h
    simp only [hW1, oneBitStep_noCarry hci, hic, hmi, hnA]
    by_contra hn
    exact regOut_cmov _ D C A B e hn h
  refine ⟨_, hstA, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, ?_, ?_, ?_,
    bits_setReg hrel.bits D _ (Or.inl rfl)⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    by_cases e : r = D
    · subst e
      exact Or.inl (by simp [LstateM.setReg, LstateM.nextPc])
    · exact (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e])
        (by simp [e]) (hWD r e)
  · intro q a ha
    have e : q ≠ D := fun e => by rw [e, hD] at ha; cases ha
    simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
      ite_false]
    exact (hrel.slots q a ha).of_eq rfl rfl (hWD q e)
  · intro r hr hW
    change r ∉ oneBitAt frame body (sa.reg.lpc + 1) at hW
    simp only [hW1, oneBitStep_noCarry hci, hic, hmi, hnA] at hW
    by_cases e : r = D
    · subst e
      simp
    · simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg, e, ite_false]
      exact hrel.wid r hr (regOut_cmov _ D C A B e hW)
  · intro q A' n hq'
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq'
    exact ⟨arr, by simpa using h1, h2⟩
  all_goals
    have hsr := saved_reload_nextW
      (sa' := { sa with reg := (sa.reg.setReg D (JasminDialect.selectW vc va vb)).nextPc })
      hphys hrel hb hnm rfl (fun _ _ _ _ => rfl)
      (fun r _ hr => by
        rw [hx] at hr
        have hrD : r ≠ D := fun e => hr (by simp [e, dstNames, JasminLsemExportRewrites.opNames])
        simp [LstateN.setReg, LstateN.nextPc, hrD])
  · exact hsr.1
  · exact hsr.2.1
  · exact hsr.2.2

/-- **A register instruction keeps `ImgRelW`.** A select whose condition lies in the width
    analysis is the select of `rel_scmovW`; every other instruction reads only names outside
    the analysis, which hold the same value on both machines, and is stepped from a state
    that agrees with the image on every name without a frame word (`reg_stepW`) and carried
    to the address state by the congruence of `fstepA` on the names read. -/
theorem rel_regW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {s t : LstateMF}
    {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hc : icase frame bi.li_i = .reg)
    (hci : carryI? bi.li_i = none) (hmi : movImmStruct? bi.li_i = none)
    (hbs : bitStore? body sa.reg.lpc bi.li_i = none)
    (hg : regGateBW frame (oneBitAt frame body sa.reg.lpc) (normA bi.li_i) = true)
    (hrd : readOkB (oneBitAt frame body sa.reg.lpc) bi.li_i = true)
    (hcm : cmovCondOkB (oneBitAt frame body sa.reg.lpc) bi.li_i = true)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨ds, o, ss, hx, -, -⟩ := icase_reg hc
  by_cases hcv : ∃ D C A B, bi.li_i = .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]
      ∧ C ∈ oneBitAt frame body sa.reg.lpc
  · obtain ⟨D, C, A, B, hx', hCW⟩ := hcv
    rw [hx'] at hcm
    have hcm' : gpOk D = true ∧ gpOk C = true ∧ gpOk A = true ∧ gpOk B = true ∧ A ≠ C
        ∧ B ≠ C := by
      simpa [cmovCondOkB, hCW, and_assoc] using hcm
    have hAW : A ∉ oneBitAt frame body sa.reg.lpc :=
      readOkB_spec hrd (by rw [hx']; simp [readNames, srcNames])
        (by rw [hx']; simp [carryIns, hcm'.2.2.2.2.1])
    exact rel_scmovW hphys P hrel hb hx' (hsep.gp D hcm'.1) (hsep.gp C hcm'.2.1)
      (Or.inl hcm'.2.2.1) hAW hs
  have hRW : ∀ r, r ∈ readNames bi.li_i → r ∉ oneBitAt frame body sa.reg.lpc := by
    intro r hr hrW
    by_cases hcr : r ∈ carryIns bi.li_i
    · obtain ⟨d', m', a', s', c', hx', hcase⟩ := carryIns_cases hcr
      rcases hcase with ⟨h1, -⟩ | ⟨h2, rfl⟩
      · rw [hx'] at hci
        rcases h1 with rfl | rfl <;> simp [carryI?] at hci
      · exact hcv ⟨d', r, s', c', by rw [hx', h2], hrW⟩
    · exact readOkB_spec hrd hr hcr hrW
  have hl : IsLopn (normA bi.li_i, MemTag.reg none) := by
    rw [hx]; exact ⟨ds, _, ss, rfl⟩
  -- the state that agrees with the image on every name without a frame word
  obtain ⟨sa₀, h0r, h0f, h0lpc, h0mem, h0cf, h0of⟩ : ∃ sa₀ : LstateA,
      (∀ r, frame r = none → s.prog.base.reg.lvm r = sa₀.reg.lvm r)
      ∧ (∀ r, frame r ≠ none → sa₀.reg.lvm r = sa.reg.lvm r) ∧ sa₀.reg.lpc = sa.reg.lpc
      ∧ sa₀.mem = sa.mem ∧ sa₀.cf = sa.cf ∧ sa₀.of = sa.of :=
    ⟨shadowA frame s.prog.base.reg sa, fun r hr => by simp [shadowA, hr],
      fun r hr => by simp [shadowA, hr], rfl, rfl, rfl, rfl⟩
  have h0w : ∀ r, gpOk r = true → r ∉ oneBitAt frame body sa.reg.lpc →
      (sa₀.reg.lvm r).1 = 64 := fun r hgr hW => by
    rw [← h0r r (hsep.gp r hgr), hrel.regsEq (hsep.gp r hgr) hW]
    exact hrel.wid r hgr hW
  obtain ⟨sa₀', hst0, hmem0, hregs0, hkeepF0, hcf0, hof0, hlpcA0, hlpcI, hlarr, hwid0, hbits0⟩ :=
    reg_stepW hl hg P s t sa₀ zf h0r hrel.zf (by rw [h0cf]; exact hrel.cf)
      (by rw [h0of]; exact hrel.of) h0w hs
  -- the step on the address state
  have hag : JasminLsemAddrCongr.AAgree (readsI (normA bi.li_i)) sa₀ sa := by
    refine ⟨⟨h0lpc, fun r hr => ?_⟩, h0mem, h0cf, h0of⟩
    by_cases hf : frame r = none
    · rw [← h0r r hf]
      rcases hrel.regs r hf with h | ⟨hrW, hgr, -⟩
      · exact h
      · exfalso
        have hr' := (DecodePrintedAddrW.readsI_normA _ _).1 hr
        rw [hx] at hr'
        have hn := readNames_of_readsI hr' hgr
        rw [← hx] at hn
        exact hRW r hn hrW
    · exact h0f r hf
  have hcg := JasminLsemAddrCongr.fstepA_congr frame (normA bi.li_i, .reg none) hag zf
  rw [hst0] at hcg
  obtain ⟨sa', z', hst, hA⟩ : ∃ sa' z', fstepA frame (normA bi.li_i, .reg none) sa zf
      = some (sa', z') ∧ JasminLsemAddrCongr.AStep sa₀ sa (sa₀', t.zf) (sa', z') := by
    revert hcg
    cases fstepA frame (normA bi.li_i, .reg none) sa zf with
    | none => intro h; cases h
    | some p => intro h; cases h with | some h => exact ⟨p.1, p.2, rfl, h⟩
  obtain ⟨⟨hpc', hN⟩, hmem', hcf', hof', hz'⟩ := hA
  simp only at hz'
  subst hz'
  have hmemA : sa'.mem = sa.mem := by rw [← hmem', hmem0, h0mem]
  have hlpcA : sa'.reg.lpc = sa.reg.lpc + 1 := by rw [← hpc', hlpcA0, h0lpc]
  have hkeepA : ∀ r, r ∉ dstNames bi.li_i → sa'.reg.lvm r = sa.reg.lvm r := fun r hr =>
    NarrowTyping.fstepA_lvm_of_not_dst hst (by rw [dstNames_normA]; exact hr)
  have hW1 : oneBitAt frame body (sa.reg.lpc + 1)
      = regOut (oneBitAt frame body sa.reg.lpc) (normA bi.li_i) := by
    rw [oneBitAt_succ hb hbs (seedAt_of_eq hx (by simp)), oneBitStep_noCarry hci, hc, hmi]
  have hmovF : ∀ d src, slotMov? bi.li_i = some (d, src) → frame d = none ∧ frame src = none :=
    fun d src hm => regGateBW_slotMov hg (slotMov?_normA hm)
  refine ⟨sa', hst, ⟨?_, fun r hr => ?_, fun q a ha => ?_, rfl, ?_, ?_, fun r hr hW => ?_,
    ?_, ?_, ?_, by rw [hmemA]; exact hrel.held, fun r hr hcd => ?_⟩⟩
  · rw [hlpcA, hlpcI, hrel.pc]
  · -- the values of the names without a frame word
    rw [hregs0 r hr]
    rcases hN r with h | ⟨h1, h2⟩
    · exact Or.inl h
    · rw [h1, h2, ← h0r r hr]
      refine (hrel.regs r hr).keep fun hrW hgr h1w => ?_
      rw [hlpcA, hW1]
      by_contra hn
      have := hwid0 r hgr hn
      rw [h1, ← h0r r hr, h1w] at this
      cases this
  · refine (hrel.slots q a ha).of_eq (hkeepF0 q (by rw [ha]; simp)) (by rw [hmemA]) fun h => ?_
    rw [hlpcA, hW1]
    exact mem_regOut_of_frame (by simp only [regGateBW, Bool.and_eq_true] at hg; exact hg.1)
      (by rw [ha]; rfl) h
  · rw [← hcf', hcf0]
  · rw [← hof', hof0]
  · rw [hlpcA, hW1] at hW
    rcases hN r with h | ⟨h1, h2⟩
    · rw [← h]; exact hwid0 r hr hW
    · rw [h2]
      have h64 := hwid0 r hr hW
      rw [h1, ← h0r r (hsep.gp r hr)] at h64
      exact (hrel.regs r (hsep.gp r hr)).wid h64
  · intro q A n hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    exact ⟨arr, by rw [getArr_congr hlarr]; exact h1, fun j hj => by rw [hmemA]; exact h2 j hj⟩
  · intro k R A n a hS hA ha
    rw [hlpcA]
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [hmemA]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (hrel.saved k R A n a hS hA ha).1 hk
      · exfalso
        obtain ⟨i', hi', hm'⟩ := hS
        rw [hb] at hi'
        cases hi'
        rw [(hmovF _ _ hm').1] at ha
        cases ha
    · obtain ⟨i', hi', hm'⟩ := hS
      have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
      obtain ⟨d, src, hm, hdR⟩ := entryRegB_spec hent (show sa.reg.lpc < k by omega) hb
      have e : sa'.reg.lvm R = sa.reg.lvm R := hkeepA R (by
        rcases slotMov?_cases hm with h | h <;> rw [h] <;>
          simp [dstNames, JasminLsemExportRewrites.opNames, Ne.symm hdR])
      rw [getW_congr e]
      exact (hrel.saved k R A n a ⟨i', hi', hm'⟩ hA ha).2 (by omega)
  · refine reload_succ hrel.reload hb hlpcA (fun r h => hsep.gp r h) (hsep.slotFrameB)
      (fun b q a A n hm _ hq _ => ?_) (fun b q hm hgq hbf => ?_)
      (fun d q0 b hm _ hbd hbf => ?_) (fun _ _ q a _ _ _ _ _ _ => by rw [hmemA])
      (fun _ b hbf hbd => hkeepA b hbd) (fun _ _ _ _ _ _ _ _ => by rw [hmemA])
    · rw [(hmovF _ _ hm).2] at hq
      cases hq
    · -- the copy `b := q` of a register
      have hqf := (hmovF _ _ hm).2
      have hqW : q ∉ oneBitAt frame body sa.reg.lpc :=
        hRW q (by rcases slotMov?_cases hm with h | h <;> rw [h] <;>
          simp [readNames, srcNames])
      have ht := eval_slotMov P (slotMov?_normA hm) (MemTag.reg none) s
      rw [hs] at ht
      have htb : t.prog.base.reg.lvm b = s.prog.base.reg.lvm q := by
        rw [Option.some.inj ht]
        simp [LstateM.setReg, LstateM.nextPc]
      rcases hN b with h | ⟨h1, h2⟩
      · rw [← h, ← hregs0 b hbf, htb, hrel.regsEq hqf hqW]
      · rw [h2]
        have hsb : s.prog.base.reg.lvm b = s.prog.base.reg.lvm q := by
          rw [← htb, hregs0 b hbf, h1, ← h0r b hbf]
        rcases hrel.regs b hbf with hb' | ⟨-, -, c, hc1, -⟩
        · rw [← hb', hsb, hrel.regsEq hqf hqW]
        · exfalso
          have hw := hrel.wid q hgq hqW
          rw [← hrel.regsEq hqf hqW, ← hsb, hc1] at hw
          cases hw
    · exact hkeepA b (by
        rcases slotMov?_cases hm with h | h <;> rw [h] <;>
          simp [dstNames, JasminLsemExportRewrites.opNames, hbd])
  · -- the widths `64` or `1`
    rcases hN r with h | ⟨h1, h2⟩
    · rw [← h]
      refine hbits0 r hr ?_
      rw [← h0r r (hsep.gp r hr)]
      rcases hrel.regs r (hsep.gp r hr) with h' | ⟨-, -, c, hc1, -⟩
      · rw [h']; exact hrel.bits r hr hcd
      · rw [hc1]; exact Or.inr rfl
    · rw [h2]; exact hrel.bits r hr hcd

/-- **A select into a frame word keeps `ImgRelW`.** The image writes the select of
    `CMOV:64 D, [C, A, B]` to the frame-word name `D`, the address machine writes it at the
    frame word of `D`, which holds no array pointer. -/
theorem rel_scmovDstW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {D C A B : String} {aD : BitVec 64}
    (hx : bi.li_i = .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B])
    (hD : frame D = some aD) (hDs : slotArr D = none)
    (hC : frame C = none) (hA : gpOk A = true ∨ (frame A).isSome = true)
    (hAW : A ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hnA : normA bi.li_i = .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B] := by
    rw [hx]; simp (config := { decide := true }) [normA]
  rw [hnA] at hs ⊢
  have hl : IsLopn (LinstrR.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], MemTag.reg none) :=
    ⟨_, _, _, rfl⟩
  have hword : ∀ x v, s.prog.base.reg.getW x 64 = some v → wordA frame sa x = some v := by
    intro x v hv
    unfold wordA
    split
    · rename_i ad hfa
      rw [(hrel.slots x ad hfa).getW64 hv]
    · rename_i hfa
      exact (hrel.regs x hfa).getW64 hv
  obtain ⟨va, hva⟩ : ∃ v, s.prog.base.reg.getW A 64 = some v := by
    cases hfa : frame A with
    | some ad => exact ⟨_, getW_eq_some_iff.2 ((hrel.slots A ad hfa).word hAW)⟩
    | none =>
      have hgA : gpOk A = true := by
        rcases hA with h | h
        · exact h
        · rw [hfa] at h; cases h
      have hw := hrel.wid A hgA hAW
      rw [← hrel.regsEq hfa hAW] at hw
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
  have hstA := fstepA_slotCmovDst frame (C := C) hD none sa s.zf (hword A va hva)
    (hword B vb hgb)
  rw [bitA_of_none hC, (hrel.regs C hC).regBit hgc] at hstA
  simp only [Option.map_some] at hstA
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hx (by simp))
    (seedAt_of_eq hx (by simp))
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?]
  have hci : carryI? bi.li_i = none := by rw [hx]; simp [carryI?]
  have hic : icase frame bi.li_i = .reg := by
    rw [hx]; simp (config := { decide := true }) [icase, slotMov?, slotCmp?, normA_of_caret_free]
  have hmi : movImmStruct? bi.li_i = none := by rw [hx]; simp [movImmStruct?]
  obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with
      reg := sa.reg.nextPc
      mem := write64 sa.mem aD (JasminDialect.selectW vc va vb) })
    hphys hrel hb hnm rfl (fun q a hq ha => read64_write64_of_disjoint _ _ _ _
      (hsep.frames D q aD a hD ha (fun e => by rw [← e, hDs] at hq; cases hq)))
    (fun _ _ _ => rfl)
  refine ⟨_, hstA, ⟨?_, ?_, ?_, rfl, hrel.cf, hrel.of, ?_, ?_, hsv, hrl, hhd,
    fun r hr hc => by simpa using hrel.bits r hr hc⟩⟩
  · simp [LstateM.setReg, LstateM.nextPc, hrel.pc]
  · intro r hr
    have e : r ≠ D := fun e => by rw [e, hD] at hr; cases hr
    refine (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e]) (by simp)
      fun h => ?_
    change r ∈ oneBitAt frame body (sa.reg.lpc + 1)
    simp only [hW1, oneBitStep_noCarry hci, hic, hmi, hnA]
    by_contra hn
    exact regOut_cmov _ D C A B e hn h
  · intro q a ha
    by_cases e : q = D
    · subst e
      rw [hD] at ha
      cases ha
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, ite_true,
        read64_write64_same]
      exact Or.inl rfl
    · simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg, e,
        ite_false]
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames D q aD a hD ha (Ne.symm e))]
      refine (hrel.slots q a ha).of_eq rfl rfl fun h => ?_
      change q ∈ oneBitAt frame body (sa.reg.lpc + 1)
      simp only [hW1, oneBitStep_noCarry hci, hic, hmi, hnA]
      by_contra hn
      exact regOut_cmov _ D C A B e hn h
  · intro r hr hW
    change r ∉ oneBitAt frame body (sa.reg.lpc + 1) at hW
    simp only [hW1, oneBitStep_noCarry hci, hic, hmi, hnA] at hW
    have e : r ≠ D := fun e => by subst e; rw [hsep.gp _ hr] at hD; cases hD
    simpa using hrel.wid r hr (regOut_cmov _ D C A B e hW)
  · intro q A' n hq'
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq'
    refine ⟨arr, by simpa using h1, fun j hj => ?_⟩
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q A' n j hq' hj D aD hD).symm]
    exact h2 j hj

/-- **A compare against a frame word keeps `ImgRelW`.** -/
theorem rel_scmpW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d y q : String} (hc : icase frame bi.li_i = .scmp d y q)
    (hci : carryI? bi.li_i = none) (hy : frame y = none)
    (hyW : y ∉ oneBitAt frame body sa.reg.lpc) (hqW : q ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  obtain ⟨hk, hq⟩ := icase_scmp hc
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
  obtain ⟨o, -, hxr⟩ := eq_of_normA_lopn (slotCmp?_eq hk) (by simp [withWidthTag])
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hxr (by simp))
    (seedAt_of_eq hxr (by simp))
  rw [oneBitStep_noCarry hci, hc] at hW1
  have hnm : slotMov? bi.li_i = none := by rw [hxr]; simp [slotMov?]
  rw [eval_slotCmp P hk] at hs
  have hqv : s.prog.base.reg.getW q 64 = some (read64 sa.mem a) := by
    rw [getW_eq, (hrel.slots q a ha).word hqW]; simp [castW]
  rw [hqv, getW_congr (hrel.regsEq hy hyW)] at hs
  rw [fstepA_slotCmp frame hk ha]
  cases hva : sa.reg.getW y 64 with
  | none => rw [hva] at hs; cases hs
  | some va =>
    rw [hva] at hs
    cases hs
    obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with reg := sa.reg.nextPc }) hphys hrel
      hb hnm rfl (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    refine ⟨{ sa with reg := sa.reg.nextPc }, rfl, ⟨by simp [LstateM.nextPc, hrel.pc],
      fun r hr => (hrel.regs r hr).of_eq (by simp [LstateM.nextPc]) (by simp)
        (fun h => by simpa [hW1] using h),
      fun q' a' ha' => (hrel.slots q' a' ha').of_eq (by simp [LstateM.nextPc]) rfl
        (fun h => by simpa [hW1] using h), rfl, hrel.cf,
      hrel.of, fun r hr hW => ?_,
      fun q' A n hq' => by simpa using hrel.cells q' A n hq', hsv, hrl, hhd,
      fun r hr hc => by simpa using hrel.bits r hr hc⟩⟩
    simp only [LstateN.lpc_nextPc, hW1] at hW
    simpa using hrel.wid r hr hW

/-- **An indexed load keeps `ImgRelW`**, and reads outside the red-zone word. -/
theorem rel_ldxW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateBW frame slotArr body = true) (P : LprogM) {s t : LstateMF}
    {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d b idx A : String} {n : Nat} {o : String}
    (hx : bi.li_i = .Lopn [.reg d] o [.arrIdx b idx 8])
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n)) (hgd : gpOk d = true)
    (hd : frame d = none) (hidx : frame idx = none) (hbf : frame b = none)
    (hidxW : idx ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemFk true P (.Lopn [.reg d] "LOADIDX" [.arrIdx A idx 8], .load 64 n) s
      = some t) (ho : LprogAsmPrinter.untagCaret o = "LOADIDX" := by simp [width_tag]) :
    LoadSafeAt rsp body sa
      ∧ ∃ sa', fstepA frame (normA bi.li_i, .load 64 0) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hn : normA bi.li_i = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx 8] := by
    rw [hx]; simp [normA, ho]
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hx (by simp))
    (seedAt_of_eq hx (by simp))
  rw [oneBitStep_noCarry (by rw [hx]; rfl), hx, icase_loadIdx_of_untagCaret ho] at hW1
  have hok := idxOkB_of_checked hs
  have hs' := evalInstrPMemF_of_k hs
  obtain ⟨q, hq, hp⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
  obtain ⟨arr, harr, hcell⟩ := hrel.cells q A n hq
  rw [eval_loadIdx, harr] at hs'
  have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regsEq hidx hidxW) 64
  cases hvi : sa.reg.getW idx 64 with
  | none => rw [hidxe, hvi] at hs'; cases hs'
  | some vi =>
  rw [hidxe, hvi] at hs'
  cases hs'
  have hlt : vi.toNat < n := by
    simp only [idxOkB, loadStruct?, ite_true, idxBelowB, hidxe, hvi] at hok
    simpa using hok
  have hz := hrel.zf
  subst hz
  have hval : read64 sa.mem (cellAt (base A) vi.toNat) = stackGet arr vi.toNat := by
    rw [hcell vi.toNat hlt]
    exact (stackGet_id arr ⟨vi.toNat, hlt⟩).symm
  refine ⟨?_, ?_⟩
  · intro ii x D B I hbI hnx p v hp' hv'
    rw [hb] at hbI
    have e := Option.some.inj hbI
    subst e
    rw [hn] at hnx
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
      LOperand.arrIdx.injEq, and_true] at hnx
    obtain ⟨-, -, rfl, rfl⟩ := hnx
    rw [hp] at hp'
    cases hp'
    rw [hvi] at hv'
    cases hv'
    exact hsep.red q A n vi.toNat hq hlt
  rw [hn, fstepA_loadIdx, hp, hvi]
  simp only
  obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with reg := (sa.reg.setReg d
      (read64 sa.mem (base A + BitVec.ofNat 64 (8 * vi.toNat)))).nextPc })
    hphys hrel hb (by rw [hx]; rfl) (by simp) (fun _ _ _ _ => rfl)
    (fun r _ hr => by
      rw [hx] at hr
      have hrd : r ≠ d := fun e => hr (by simp [e, dstNames, JasminLsemExportRewrites.opNames])
      simp [LstateN.setReg, LstateN.nextPc, hrd])
  refine ⟨_, rfl, ⟨by simp [LstateM.setReg, LstateM.nextPc, hrel.pc], ?_, ?_, rfl, hrel.cf,
    hrel.of, ?_, fun q' A' n' hq' => by simpa using hrel.cells q' A' n' hq', hsv, hrl, hhd,
    bits_setReg hrel.bits d _ (Or.inl rfl)⟩⟩
  · intro r hr
    by_cases e : r = d
    · subst e
      refine Or.inl ?_
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg,
        ite_true]
      rw [← hval]
    · refine (hrel.regs r hr).of_eq (by simp [LstateM.setReg, LstateM.nextPc, e])
        (by simp [e]) fun h => ?_
      simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1]
      exact List.mem_filter.2 ⟨h, by simpa using e⟩
  · intro q' a' ha'
    have e : q' ≠ d := fun e => by rw [e, hd] at ha'; cases ha'
    refine (hrel.slots q' a' ha').of_eq (by simp [LstateM.setReg, LstateM.nextPc, e]) rfl
      fun h => ?_
    simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1]
    exact List.mem_filter.2 ⟨h, by simpa using e⟩
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
    (hb : body[sa.reg.lpc]? = some bi) {d b idx v A : String} {n : Nat} {o : String}
    (hx : bi.li_i = .Lopn [.reg d] o [.arrIdx b idx 8, .reg v])
    (hacc : accArr slotArr body sa.reg.lpc b = some (A, n))
    (hidx : frame idx = none) (hbf : frame b = none) (hv : frame v = none)
    (hidxW : idx ∉ oneBitAt frame body sa.reg.lpc) (hvW : v ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemFk true P
      (.Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v], .store 64 n) s = some t)
    (ho : LprogAsmPrinter.untagCaret o = "STOREIDX" := by simp [width_tag]) :
    ∃ sa', fstepA frame (normA bi.li_i, .store 64 0) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hn : normA bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v] := by
    rw [hx]; simp [normA, ho]
  have hic : icase frame bi.li_i = .stx d b idx v := by rw [hx]; simp [icase, ho]
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hx (by simp))
    (seedAt_of_eq hx (by simp))
  rw [oneBitStep_noCarry (by rw [hx]; rfl), hic] at hW1
  have hok := idxOkB_of_checked hs
  have hs' := evalInstrPMemF_of_k hs
  obtain ⟨q, hq, hp⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
  obtain ⟨arr, harr, hcell⟩ := hrel.cells q A n hq
  rw [eval_storeIdx, harr] at hs'
  have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regsEq hidx hidxW) 64
  have hve := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regsEq hv hvW) 64
  cases hvi : sa.reg.getW idx 64 with
  | none => rw [hidxe, hvi] at hs'; cases hs'
  | some vi =>
  cases hvv : sa.reg.getW v 64 with
  | none => rw [hidxe, hvi, hve, hvv] at hs'; cases hs'
  | some vv =>
  rw [hidxe, hvi, hve, hvv] at hs'
  cases hs'
  have hlt : vi.toNat < n := by
    simp only [idxOkB, storeStruct?, ite_true, idxBelowB, hidxe, hvi] at hok
    simpa using hok
  have hz := hrel.zf
  subst hz
  rw [hn, fstepA_storeIdx, hp, hvi, hvv]
  simp only
  obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with
      reg := sa.reg.nextPc
      mem := write64 sa.mem (base A + BitVec.ofNat 64 (8 * vi.toNat)) vv })
    hphys hrel hb (by rw [hx]; rfl) rfl
    (fun q' a _ ha => read64_write64_of_disjoint _ _ _ _
      (hsep.cellFrame q A n vi.toNat hq hlt q' a ha)) (fun _ _ _ => rfl)
  refine ⟨_, rfl, ⟨by simp [LstateM.setArr, LstateM.nextPc, hrel.pc],
    fun r hr => (hrel.regs r hr).of_eq (by simp [LstateM.setArr, LstateM.nextPc]) (by simp)
      (fun h => by simpa [hW1] using h), ?_, rfl,
    hrel.cf, hrel.of, fun r hr hW => ?_, ?_, hsv, hrl, hhd,
    fun r hr hc => by simpa using hrel.bits r hr hc⟩⟩
  · intro q' a ha
    simp only [LstateM.setArr, LstateM.nextPc, LstateN.lvm_nextPc]
    rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q A n vi.toNat hq hlt q' a ha)]
    exact (hrel.slots q' a ha).of_eq rfl rfl fun h => by simpa [hW1] using h
  · simp only [LstateN.lpc_nextPc, hW1] at hW
    simpa using hrel.wid r hr hW
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
  have hW1 := oneBitAt_succ_label (frame := frame) hb hx
  obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := sa.setLpc (sa.reg.lpc + 1)) hphys hrel hb
    hnm rfl (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  refine ⟨by simp [LstateA.setLpc, LstateM.nextPc, hrel.pc],
    fun r hr => (hrel.regs r hr).of_eq (by simp [LstateM.nextPc]) rfl fun h => by
      simp only [LstateA.setLpc]; rw [hW1]; exact List.mem_append_left _ h,
    fun q a ha => (hrel.slots q a ha).of_eq (by simp [LstateM.nextPc]) rfl fun h => by
      simp only [LstateA.setLpc]; rw [hW1]; exact List.mem_append_left _ h,
    hrel.zf, hrel.cf, hrel.of, fun r hr hW => ?_,
    fun q A n hq => hrel.cells q A n hq, hsv, hrl, hhd, fun r hr hc => hrel.bits r hr hc⟩
  simp only [LstateA.setLpc] at hW ⊢
  rw [hW1] at hW
  exact hrel.wid r hr fun h => hW (List.mem_append_left _ h)

/-- **A branch not taken keeps `ImgRelW`.** -/
theorem rel_condFallW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {cnd : _} {l : LLabel}
    (hx : bi.li_i = .Lcond cnd l) :
    ImgRelW frame slotArr base body
      { s with prog := { s.prog with base := s.prog.base.nextPc } }
      (sa.setLpc (sa.reg.lpc + 1)) zf := by
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  have hW1 : oneBitAt frame body (sa.reg.lpc + 1) = oneBitAt frame body sa.reg.lpc := by
    rw [oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hx (by simp))
      (seedAt_of_eq hx (by simp)), oneBitStep_noCarry (by rw [hx]; rfl), hx]
    cases cnd <;> simp [icase, castOut, classifyK]
  obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := sa.setLpc (sa.reg.lpc + 1)) hphys hrel hb
    hnm rfl (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  refine ⟨by simp [LstateA.setLpc, LstateM.nextPc, hrel.pc],
    fun r hr => (hrel.regs r hr).of_eq (by simp [LstateM.nextPc]) rfl fun h => by
      simp only [LstateA.setLpc]; rw [hW1]; exact h,
    fun q a ha => (hrel.slots q a ha).of_eq (by simp [LstateM.nextPc]) rfl fun h => by
      simp only [LstateA.setLpc]; rw [hW1]; exact h,
    hrel.zf, hrel.cf, hrel.of, fun r hr hW => ?_,
    fun q A n hq => hrel.cells q A n hq, hsv, hrl, hhd, fun r hr hc => hrel.bits r hr hc⟩
  simp only [LstateA.setLpc] at hW ⊢
  rw [hW1] at hW
  exact hrel.wid r hr hW

/-- **A branch taken keeps `ImgRelW`** where the width analysis at the branch is included in
    the analysis one past the label: the image jumps one past the label, the address machine
    to the label and then over it. -/
theorem rel_condJumpW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hnm : slotMov? bi.li_i = none) {p : Nat}
    {bp : Linstr} (hbp : body[p]? = some bp) (hpl : slotMov? bp.li_i = none)
    (hpx : ∀ ds o ss, bp.li_i ≠ .Lopn ds o ss)
    (hW : ∀ r, r ∈ oneBitAt frame body sa.reg.lpc → r ∈ oneBitAt frame body (p + 1)) :
    ImgRelW frame slotArr base body
      { s with prog := { s.prog with base := s.prog.base.setLpc (p + 1) } }
      (sa.setLpc (p + 1)) zf := by
  refine ⟨rfl, fun r hr => (hrel.regs r hr).of_eq rfl rfl (hW r),
    fun q a ha => (hrel.slots q a ha).of_eq rfl rfl (hW q), hrel.zf, hrel.cf, hrel.of,
    fun r hr hn => hrel.wid r hr (fun h => hn (hW r h)), fun q A n hq => hrel.cells q A n hq,
    fun k R A n a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩, fun b q a A n hbi _ _ _ => ?_,
    hrel.held, fun r hr hc => hrel.bits r hr hc⟩
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
  · simp only [LstateA.setLpc] at hbi
    rw [reloadOf_succ_other hbp hpl hpx] at hbi
    cases hbi

/-- **The gate of a branch**: the branch is on a condition code with a polarity, its label
    is a label of the body, and every name of the width analysis `W` is in the analysis one
    past the label. -/
theorem gateAtW_condIncl {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd} {k : Nat} {W : List String}
    {cnd : _} {l : LLabel} (hg : gateAtW frame slotArr c k W (.Lcond cnd l) = true) :
    ∃ cc pol p, cnd = .reg cc ∧ condPol cc = some pol ∧ labelAt c l = some p
      ∧ ∀ r, r ∈ W → r ∈ oneBitAt frame c (p + 1) := by
  cases cnd with
  | reg cc =>
      simp only [gateAtW, carryI?, icase, Bool.and_eq_true, Option.isSome_iff_exists,
        Option.any_eq_true, Bool.or_eq_true, List.isEmpty_iff, List.all_eq_true,
        List.contains_eq_mem, decide_eq_true_eq] at hg
      obtain ⟨-, ⟨pol, hpol⟩, p, hp, hW⟩ := hg
      refine ⟨cc, pol, p, rfl, hpol, hp, fun r hr => ?_⟩
      rcases hW with hW | hW
      · rw [hW] at hr; cases hr
      · exact hW r hr
  | _ => simp [gateAtW, carryI?, icase, castGateB, classifyK] at hg

/-- **The reads of the gate.** Under the gate, a name an instruction other than a cast reads,
    other than a carry-in, the stored name of a frame-word store and the frame word of a
    frame-word load, lies outside the width analysis. -/
theorem gateAtW_notW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {x : LinstrR} (hg : gateAtW frame slotArr body k W x = true) (hk : classifyK x = none)
    {r : String} (hr : r ∈ readNames x) (hc : r ∉ carryIns x)
    (hs : ∀ q, icase frame x ≠ .sstore q r) (hl : ∀ d, icase frame x ≠ .sload d r) :
    r ∉ W := by
  simp only [gateAtW, Bool.and_eq_true] at hg
  have hro : readOkB (gateReadSet frame W x) x = true := by
    simpa [castReadB, hk] using hg.1
  exact readOkB_gateReadSet_spec hro hr hc hs hl

/-! ## 6. Carry-chain instructions -/

/-- A word source of a carry-chain instruction, a general-purpose name or a frame slot outside
    the width analysis, reads one 64-bit word on the image and on the address machine. -/
theorem word_virt {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) {s : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf) {A : String}
    (hk : gpOk A = true ∨ (frame A).isSome = true)
    (hw : A ∉ oneBitAt frame body sa.reg.lpc) :
    ∃ va, s.prog.base.reg.getW A 64 = some va ∧ wordA frame sa A = some va := by
  rcases hk with hg | hs
  · have hf := hsep.gp A hg
    have hw' := hrel.wid A hg hw
    refine ⟨castW (sa.reg.lvm A) 64, ?_, ?_⟩
    · rw [getW_congr (hrel.regsEq hf hw), getW_eq, ite_eq_left hw']
    · simp only [wordA, hf]
      rw [getW_eq, ite_eq_left hw']
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    refine ⟨read64 sa.mem a, ?_, by simp [wordA, ha]⟩
    rw [getW_eq, (hrel.slots A a ha).word hw]
    simp [castW]

/-- A carry-in the image reads as one bit reads the same bit on the address machine: the low
    bit of the frame word for a frame slot, the register value otherwise. -/
theorem bit_virt {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf)
    {C : String} {vc : BitVec 1} (h : s.prog.base.reg.getW C 1 = some vc) :
    bitA frame sa C = some vc := by
  unfold bitA
  split
  · rename_i ad hfa
    rw [getW_eq_some_iff] at h
    rcases hrel.slots C ad hfa with e | ⟨-, e, -⟩
    · rw [h] at e
      cases e
    · rw [h] at e
      cases e
      rfl
  · rename_i hfa
    exact (hrel.regs C hfa).regBit h

theorem oneBitStep_adcx (frame : String → Option (BitVec 64)) (W : List String)
    (D A S C : String) :
    oneBitStep frame W (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]) = W.filter (· != D) :=
  by simp [oneBitStep, carryI?]

theorem oneBitStep_adcxhi (frame : String → Option (BitVec 64)) (W : List String)
    (O A S C : String) :
    oneBitStep frame W (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]) = O :: W := by
  simp (config := { decide := true }) [oneBitStep, carryI?]

/-- **`ADCX:64` keeps `ImgRelW`**: the add with register or frame-slot word sources and
    carry-in, into a register or into a frame slot that holds no array pointer. -/
theorem rel_adcxW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {D A S C : String}
    (hx : bi.li_i = .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C])
    (hok : carryOkB frame slotArr D A S C = true)
    (hAW : A ∉ oneBitAt frame body sa.reg.lpc)
    (hSW : S ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  simp only [carryOkB, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hok
  obtain ⟨⟨⟨⟨⟨-, hAk⟩, hSk⟩, hDk⟩, -⟩, -⟩ := hok
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hx (by simp))
    (seedAt_of_eq hx (by simp))
  rw [hx, oneBitStep_adcx] at hW1
  obtain ⟨va, hvA, hwA⟩ := word_virt hsep hrel hAk hAW
  obtain ⟨vb, hvS, hwS⟩ := word_virt hsep hrel hSk hSW
  have hl : IsLopn (bi.li_i, MemTag.reg none) := by rw [hx]; exact ⟨_, _, _, rfl⟩
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  rw [evalInstrPMemF_isLopn P _ s hl, hx, fstepF_adcx D A S C _ _ hvA hvS] at hs
  have hz := hrel.zf
  subst hz
  cases hgc : s.prog.base.reg.getW C 1 with
  | none => rw [hgc] at hs; cases hs
  | some vc =>
  rw [hgc] at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  subst hs
  have hbC := bit_virt hrel hgc
  have hst0 : fstepA frame (bi.li_i, .reg none) sa s.zf = some ((match frame D with
      | some ad => { sa with
          reg := sa.reg.nextPc
          mem := write64 sa.mem ad (VIR.JasminDialect.addCarryWord va vb vc) }
      | none => { sa with
          reg := (sa.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc }), s.zf) := by
    by_cases hsl : ((frame D).isSome || (frame A).isSome || (frame S).isSome
        || (frame C).isSome) = true
    · rw [hx, fstepA_adcxSlotBit frame D A S C sa s.zf hsl hwA hwS, hbC]
      rfl
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none] at hsl
      obtain ⟨⟨⟨hfD, hfA⟩, hfS⟩, hfC⟩ := hsl
      simp only [wordA, hfA, hfS] at hwA hwS
      rw [hx, fstepA_adcx3 frame D A S C sa s.zf hfD hfA hfS hfC hwA hwS, ← bitA_of_none hfC,
        hbC]
      simp [hfD]
  cases hfD : frame D with
  | some aD =>
    have hDs : slotArr D = none := by
      rcases hDk with hg | ⟨-, h2⟩
      · rw [hsep.gp D hg] at hfD; cases hfD
      · exact h2
    have hst : fstepA frame (bi.li_i, .reg none) sa s.zf = some ({ sa with
        reg := sa.reg.nextPc
        mem := write64 sa.mem aD (VIR.JasminDialect.addCarryWord va vb vc) }, s.zf) := by
      rw [hst0, hfD]
    refine ⟨_, hst, ?_⟩
    obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with
        reg := sa.reg.nextPc
        mem := write64 sa.mem aD (VIR.JasminDialect.addCarryWord va vb vc) })
      hphys hrel hb hnm rfl (fun q a hq ha => read64_write64_of_disjoint _ _ _ _
        (hsep.frames D q aD a hfD ha (fun e => by rw [← e, hDs] at hq; cases hq)))
      (fun _ _ _ => rfl)
    refine ⟨by simp [hrel.pc], fun r hr => ?_,
      fun q a ha => ?_, rfl, hrel.cf, hrel.of, fun r hr hW => ?_, fun q A' n hq => ?_, hsv,
      hrl, hhd, fun r hr hc => by simpa using hrel.bits r hr hc⟩
    · have e : r ≠ D := fun e => by rw [e, hfD] at hr; cases hr
      refine (hrel.regs r hr).of_eq (by simp [e]) (by simp) fun h => ?_
      simp only [LstateN.lpc_nextPc, hW1]
      exact List.mem_filter.2 ⟨h, by simpa using e⟩
    · by_cases e : q = D
      · subst e
        rw [hfD] at ha
        cases ha
        simp only [read64_write64_same]
        exact Or.inl (by simp)
      · simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg, e, ite_false]
        rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames D q aD a hfD ha (Ne.symm e))]
        refine (hrel.slots q a ha).of_eq rfl rfl fun h => ?_
        simp only [LstateN.lpc_nextPc, hW1]
        exact List.mem_filter.2 ⟨h, by simpa using e⟩
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
      rw [hst0, hfD]
    refine ⟨_, hst, ?_⟩
    obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with
        reg := (sa.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc })
      hphys hrel hb hnm (by simp) (fun _ _ _ _ => rfl)
      (fun r _ hr => by
        rw [hx] at hr
        have hrD : r ≠ D := fun e => hr (by simp [e, dstNames, JasminLsemExportRewrites.opNames])
        simp [LstateN.setReg, LstateN.nextPc, hrD])
    refine ⟨by simp [hrel.pc], fun r hr => ?_,
      fun q a ha => ?_, rfl, hrel.cf, hrel.of, fun r hr hW => ?_, fun q A' n hq => ?_, hsv, hrl, hhd,
      bits_setReg hrel.bits D _ (Or.inl rfl)⟩
    · by_cases e : r = D
      · subst e; exact Or.inl (by simp)
      · refine (hrel.regs r hr).of_eq (by simp [e]) (by simp [e]) fun h => ?_
        simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1]
        exact List.mem_filter.2 ⟨h, by simpa using e⟩
    · have e : q ≠ D := fun e => by rw [e, hfD] at ha; cases ha
      refine (hrel.slots q a ha).of_eq (by simp [e]) rfl fun h => ?_
      simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1]
      exact List.mem_filter.2 ⟨h, by simpa using e⟩
    · simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1] at hW
      by_cases e : r = D
      · subst e; simp
      · simp [e, hrel.wid r hr (not_mem_filter_ne hW e)]
    · obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq
      exact ⟨arr, (getArr_congr rfl _ _ _).trans h1, h2⟩

/-- **`ADCXHI:64` keeps `ImgRelW`**: the carry-out binding with register or frame-slot word
    sources and carry-in, into a register or into the low byte of a frame slot that holds no
    array pointer; the destination enters the width analysis. -/
theorem rel_adcxhiW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {O A S C : String}
    (hx : bi.li_i = .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C])
    (hok : carryOkB frame slotArr O A S C = true)
    (hAW : A ∉ oneBitAt frame body sa.reg.lpc)
    (hSW : S ∉ oneBitAt frame body sa.reg.lpc)
    (hs : evalInstrPMemF P (bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  simp only [carryOkB, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hok
  obtain ⟨⟨⟨⟨⟨-, hAk⟩, hSk⟩, hOk⟩, -⟩, -⟩ := hok
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hx (by simp))
    (seedAt_of_eq hx (by simp))
  rw [hx, oneBitStep_adcxhi] at hW1
  obtain ⟨va, hvA, hwA⟩ := word_virt hsep hrel hAk hAW
  obtain ⟨vb, hvS, hwS⟩ := word_virt hsep hrel hSk hSW
  have hl : IsLopn (bi.li_i, MemTag.reg none) := by rw [hx]; exact ⟨_, _, _, rfl⟩
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  rw [evalInstrPMemF_isLopn P _ s hl, hx, fstepF_adcxhi O A S C _ _ hvA hvS] at hs
  have hz := hrel.zf
  subst hz
  cases hgc : s.prog.base.reg.getW C 1 with
  | none => rw [hgc] at hs; cases hs
  | some vc =>
  rw [hgc] at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  subst hs
  have hbC := bit_virt hrel hgc
  have hst0 : fstepA frame (bi.li_i, .reg none) sa s.zf = some ((match frame O with
      | some ad => { sa with
          reg := sa.reg.nextPc
          mem := write64 sa.mem ad
            ((VIR.JasminDialect.carryOutBit va vb vc).setWidth 64) }
      | none => { sa with
          reg := (sa.reg.setReg O (VIR.JasminDialect.carryOutBit va vb vc)).nextPc }),
        s.zf) := by
    by_cases hsl : ((frame O).isSome || (frame A).isSome || (frame S).isSome
        || (frame C).isSome) = true
    · rw [hx, fstepA_adcxhiSlotBit frame O A S C sa s.zf hsl hwA hwS, hbC]
      rfl
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none] at hsl
      obtain ⟨⟨⟨hfO, hfA⟩, hfS⟩, hfC⟩ := hsl
      simp only [wordA, hfA, hfS] at hwA hwS
      rw [hx, fstepA_adcxhi frame O A S C sa s.zf hfO hfA hfS hfC hwA hwS, ← bitA_of_none hfC,
        hbC]
      simp [hfO]
  cases hfO : frame O with
  | some aO =>
    have hOs : slotArr O = none := by
      rcases hOk with hg | ⟨-, h2⟩
      · rw [hsep.gp O hg] at hfO; cases hfO
      · exact h2
    have hst : fstepA frame (bi.li_i, .reg none) sa s.zf = some ({ sa with
        reg := sa.reg.nextPc
        mem := write64 sa.mem aO
          ((VIR.JasminDialect.carryOutBit va vb vc).setWidth 64) }, s.zf) := by
      rw [hst0, hfO]
    refine ⟨_, hst, ?_⟩
    obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with
        reg := sa.reg.nextPc
        mem := write64 sa.mem aO
          ((VIR.JasminDialect.carryOutBit va vb vc).setWidth 64) })
      hphys hrel hb hnm rfl (fun q a hq ha => read64_write64_of_disjoint _ _ _ _
        (hsep.frames O q aO a hfO ha (fun e => by rw [← e, hOs] at hq; cases hq)))
      (fun _ _ _ => rfl)
    refine ⟨by simp [hrel.pc], fun r hr => ?_,
      fun q a ha => ?_, rfl, hrel.cf, hrel.of, fun r hr hW => ?_, fun q A' n hq => ?_, hsv,
      hrl, hhd, fun r hr hc => by simpa using hrel.bits r hr hc⟩
    · have e : r ≠ O := fun e => by rw [e, hfO] at hr; cases hr
      refine (hrel.regs r hr).of_eq (by simp [e]) (by simp) fun h => ?_
      simp only [LstateN.lpc_nextPc, hW1]
      exact List.mem_cons_of_mem _ h
    · by_cases e : q = O
      · subst e
        rw [hfO] at ha
        cases ha
        simp only [read64_write64_same]
        refine Or.inr ⟨?_, by simp, fun _ => by simp⟩
        simp only [LstateN.lpc_nextPc, hW1]
        exact List.mem_cons_self
      · simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg, e, ite_false]
        rw [read64_write64_of_disjoint _ _ _ _ (hsep.frames O q aO a hfO ha (Ne.symm e))]
        refine (hrel.slots q a ha).of_eq rfl rfl fun h => ?_
        simp only [LstateN.lpc_nextPc, hW1]
        exact List.mem_cons_of_mem _ h
    · simp only [LstateN.lpc_nextPc, hW1, List.mem_cons, not_or] at hW
      simpa using hrel.wid r hr hW.2
    · obtain ⟨arr, h1, h2⟩ := hrel.cells q A' n hq
      refine ⟨arr, (getArr_congr rfl _ _ _).trans h1, fun j hj => ?_⟩
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q A' n j hq hj O aO hfO).symm]
      exact h2 j hj
  | none =>
  have hst : fstepA frame (bi.li_i, .reg none) sa s.zf = some ({ sa with
      reg := (sa.reg.setReg O (VIR.JasminDialect.carryOutBit va vb vc)).nextPc }, s.zf) := by
    rw [hst0, hfO]
  refine ⟨_, hst, ?_⟩
  obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with
      reg := (sa.reg.setReg O (VIR.JasminDialect.carryOutBit va vb vc)).nextPc })
    hphys hrel hb hnm (by simp) (fun _ _ _ _ => rfl)
    (fun r _ hr => by
      rw [hx] at hr
      have hrO : r ≠ O := fun e => hr (by simp [e, dstNames, JasminLsemExportRewrites.opNames])
      simp [LstateN.setReg, LstateN.nextPc, hrO])
  refine ⟨by simp [hrel.pc], fun r hr => ?_,
    fun q a ha => ?_, rfl, hrel.cf, hrel.of, fun r hr hW => ?_, fun q A' n hq => ?_, hsv, hrl, hhd,
    bits_setReg hrel.bits O _ (Or.inr rfl)⟩
  · by_cases e : r = O
    · subst e; exact Or.inl (by simp)
    · refine (hrel.regs r hr).of_eq (by simp [e]) (by simp [e]) fun h => ?_
      simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1]
      exact List.mem_cons_of_mem _ h
  · have e : q ≠ O := fun e => by rw [e, hfO] at ha; cases ha
    refine (hrel.slots q a ha).of_eq (by simp [e]) rfl fun h => ?_
    simp only [LstateN.lpc_nextPc, LstateN.lpc_setReg, hW1]
    exact List.mem_cons_of_mem _ h
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
  obtain ⟨hrd0, hg⟩ := hg
  rcases hkc : classifyK bi.li_i with _ | ⟨D, A, m, w⟩
  swap
  · -- a width-carrying cast
    obtain ⟨o, hx, hm, hw, hci, hic, hmi, hnm⟩ := cast_facts frame hkc
    rw [hci, hic] at hg
    simp only [castGateB, hkc, Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
    obtain ⟨⟨⟨-, -⟩, hfD⟩, hfA⟩ := hg
    have himg : imgInstr slotArr c sa.reg.lpc bi.li_i = (bi.li_i, .reg (some w)) := by
      rw [hx]
      simp only [imgInstr]
      rw [bitStore?_of_ne (by simp)]
      simp only
      rw [cellIdxStore?_of_ne slotArr (by
        intro c' v' he
        simp only [LinstrR.Lopn.injEq] at he
        rw [he.2.1] at hw
        simp [castTagW] at hw)]
      simp only
      have hu := LprogAsmPrinter.untagCaret_of_caret_free (castTagW_caret_free hw)
      rw [normA_castW hw, tagAt_castW _ _ hw,
        arrImmImg_of_ne slotArr c _ (by rw [hu]; exact (castTagW_ne_arr hw).1)
          (by rw [hu]; exact (castTagW_ne_arr hw).2)]
    rw [himg] at hstep
    have hstep' : evalInstrPMemF P (bi.li_i, .reg (some w)) s = some t := by
      simpa [evalInstrPMemFk, idxOkB] using hstep
    obtain ⟨sa', hst, hr⟩ := rel_castW hphys P hrel hb hkc hfD hfA hstep'
    refine ⟨haltedA_of hb (by rw [hx]; simp),
      loadSafe_of hb (by intro D' B I e; rw [hx] at e; simp [normA] at e), sa', ?_, hr⟩
    rw [stepA_lopn frame hb hx, ← hst, hx, normA_castW hw, tagAt_castW _ _ hw]
  have hrd : readOkB (gateReadSet frame (oneBitAt frame c sa.reg.lpc) bi.li_i) bi.li_i = true := by
    simpa [castReadB, hkc] using hrd0
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
    have hns : ∀ q r, icase frame bi.li_i ≠ .sstore q r := by
      intro q r h
      have h1 := (icase_sstore h).1
      rw [hx0] at h1
      cases hi <;> simp [slotMov?] at h1
    have hnl : ∀ d r, icase frame bi.li_i ≠ .sload d r := by
      intro d r h
      have h1 := (icase_sload h).1
      rw [hx0] at h1
      cases hi <;> simp [slotMov?] at h1
    have hAW : a ∉ oneBitAt frame c sa.reg.lpc :=
      readOkB_gateReadSet_spec hrd (by rw [hx0]; simp [readNames, srcNames])
        (by rw [hcI]; simpa using hac) (fun q => hns q a) (fun d => hnl d a)
    have hSW : s' ∉ oneBitAt frame c sa.reg.lpc :=
      readOkB_gateReadSet_spec hrd (by rw [hx0]; simp [readNames, srcNames])
        (by rw [hcI]; simpa using hsc) (fun q => hns q s') (fun d => hnl d s')
    have hld : (if hi then "ADCXHI:64" else "ADCX:64") ≠ "LOADIDX" := by cases hi <;> decide
    have hsd : (if hi then "ADCXHI:64" else "ADCX:64") ≠ "STOREIDX" := by cases hi <;> decide
    have hkd : castTagW (if hi then "ADCXHI:64" else "ADCX:64") = none := by
      cases hi <;> decide
    have hnA : normA bi.li_i = bi.li_i := by
      rw [hx0]; cases hi <;> simp (config := { decide := true }) [normA]
    have hsafe := loadSafe_of (rsp := rsp) hb (by
      intro D B I e; rw [hnA, hx0] at e; cases hi <;> simp at e)
    have hnr : bi.li_i ≠ .Lret := by rw [hx0]; simp
    have h3 : bitMovB c sa.reg.lpc (.Lopn [.reg d] (if hi then "ADCXHI:64" else "ADCX:64")
        [.reg a, .reg s', .reg cc]) = false :=
      bitMovB_of_ne (by cases hi <;> simp [movImmStruct?])
    rw [hx0, imgInstr_reg_of_caret_free slotArr c _ hld hsd hkd h3
      (bitStore?_of_ne (by cases hi <;> simp))
      (cellIdxStore?_of_ne slotArr (by cases hi <;> simp)) (by cases hi <;> decide)
      (by cases hi <;> decide) (by cases hi <;> decide), evalInstrPMemFk_reg, ← hx0,
      hnA] at hstep
    have hstepA : stepA frame c sa s.zf = fstepA frame (bi.li_i, .reg none) sa s.zf := by
      rw [stepA_lopn frame hb hx0, hnA, hx0, tagAt_reg_of_caret_free hld hsd hkd h3
        (by cases hi <;> decide) (by cases hi <;> decide) (by cases hi <;> decide)]
    obtain ⟨sa', hst, hr⟩ : ∃ sa', fstepA frame (bi.li_i, .reg none) sa s.zf = some (sa', t.zf)
        ∧ ImgRelW frame slotArr base c t sa' t.zf := by
      cases hi
      · exact rel_adcxW hsep hphys P hrel hb (by simpa using hx0) hg hAW hSW hstep
      · exact rel_adcxhiW hsep hphys P hrel hb (by simpa using hx0) hg hAW hSW hstep
    exact ⟨haltedA_of hb hnr, hsafe, sa', by rw [hstepA, hst], hr⟩
  | none =>
    rw [hci] at hg
    cases hc : icase frame bi.li_i with
    | other => rw [hc] at hg; simp [castGateB, hkc] at hg
    | zarr => rw [hc] at hg; cases hg
    | simm => rw [hc] at hg; cases hg
    | cond cc l => exact absurd (icase_cond hc) (hnc (.reg cc) l)
    | label =>
        obtain ⟨ii, l, hx⟩ := icase_label hc
        have hi : imgInstr slotArr c sa.reg.lpc bi.li_i = (bi.li_i, .reg none) := by
          rw [hx]; rfl
        rw [hi, evalInstrPMemFk_reg, hx, eval_label] at hstep
        cases hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp [normA]),
          sa.setLpc (sa.reg.lpc + 1), ?_, rel_labelW hphys hrel hb hx⟩
        obtain ⟨ii0, li⟩ := bi
        simp only at hx
        subst hx
        simp [stepA, hb]
    | ldx d b idx =>
        rw [hc] at hg
        simp only [gateReadSet, hc] at hrd
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
        obtain ⟨⟨⟨⟨⟨An, hacc⟩, hgd⟩, hd⟩, hidx⟩, hbf⟩ := hg
        obtain ⟨A, n⟩ := An
        obtain ⟨o, ho, hx⟩ := icase_ldx hc
        have hidxW : idx ∉ oneBitAt frame c sa.reg.lpc :=
          readOkB_spec hrd (by rw [hx]; simp [readNames, srcNames]) (by rw [hx]; simp [carryIns])
        rw [hx, imgInstr_ldx_of_untagCaret slotArr c _ hacc ho] at hstep
        obtain ⟨hsafe, sa', hst, hr⟩ :=
          rel_ldxW hsep hphys hgate P hrel hb hx hacc hgd hd hidx hbf hidxW hstep ho
        refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
        have ht : tagAt c sa.reg.lpc bi.li_i = .load 64 0 := by
          rw [hx, tagAt_of_not (bitMovB_of_ne (by simp [movImmStruct?]))]
          simp [tagA, ho]
        rw [stepA_lopn frame hb hx, ← hst, ht]
    | stx d b idx v =>
        rw [hc] at hg
        simp only [gateReadSet, hc] at hrd
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
        obtain ⟨⟨⟨⟨An, hacc⟩, hidx⟩, hbf⟩, hv⟩ := hg
        obtain ⟨A, n⟩ := An
        obtain ⟨o, ho, hx⟩ := icase_stx hc
        have hidxW : idx ∉ oneBitAt frame c sa.reg.lpc :=
          readOkB_spec hrd (by rw [hx]; simp [readNames, srcNames]) (by rw [hx]; simp [carryIns])
        have hvW : v ∉ oneBitAt frame c sa.reg.lpc :=
          readOkB_spec hrd (by rw [hx]; simp [readNames, srcNames]) (by rw [hx]; simp [carryIns])
        rw [hx, imgInstr_stx_of_untagCaret slotArr c _ hacc ho] at hstep
        obtain ⟨sa', hst, hr⟩ :=
          rel_stxW hsep hphys hgate P hrel hb hx hacc hidx hbf hv hidxW hvW hstep ho
        refine ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp [normA]), sa',
          ?_, hr⟩
        have ht : tagAt c sa.reg.lpc bi.li_i = .store 64 0 := by
          rw [hx, tagAt_of_not (bitMovB_of_ne (by simp [movImmStruct?]))]
          simp [tagA, ho]
        rw [stepA_lopn frame hb hx, ← hst, ht]
    | sload d q =>
        rw [hc] at hg
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
          decide_eq_false_iff_not] at hg
        obtain ⟨hgd, hqN⟩ := hg
        have hm := (icase_sload hc).1
        have hsafe := loadSafe_of (rsp := rsp) hb
          (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
        have h3 : bitMovB c sa.reg.lpc bi.li_i = false := bitMovB_of_slotMov hm
        have h4 : bitStore? c sa.reg.lpc bi.li_i = none := bitStore?_of_slotMov hm
        have h5 : cellIdxStore? slotArr c sa.reg.lpc bi.li_i = none := cellIdxStore?_of_slotMov hm
        rcases slotMov?_cases hm with hx | hx <;>
        · rw [hx] at h3 h4 h5
          rw [hx, imgInstr_reg_of_caret_free slotArr c _ (by decide) (by decide) (by decide) h3
            h4 h5, evalInstrPMemFk_reg, ← hx] at hstep
          obtain ⟨sa', hst, hr⟩ := rel_sloadW_gen hsep hphys P hrel hb hc hci hgd
            (fun h => (hqN.resolve_left (fun h' => h' h)).1) hstep
          refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
          rw [stepA_lopn frame hb hx, ← hst, hx,
            tagAt_reg_of_caret_free (by decide) (by decide) (by decide) h3]
    | sstore q S =>
        rw [hc] at hg
        have hm := (icase_sstore hc).1
        have hsafe := loadSafe_of (rsp := rsp) hb
          (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
        have h3 : bitMovB c sa.reg.lpc bi.li_i = false := bitMovB_of_slotMov hm
        have h4 : bitStore? c sa.reg.lpc bi.li_i = none := bitStore?_of_slotMov hm
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
          decide_eq_false_iff_not] at hg
        obtain ⟨hgS, hSW⟩ := hg
        have hSW' : S ∉ oneBitAt frame c sa.reg.lpc ∨ S ∉ castDsts c :=
          hSW.imp id fun h => h.1.1
        have h5 : cellIdxStore? slotArr c sa.reg.lpc bi.li_i = none := cellIdxStore?_of_slotMov hm
        rcases slotMov?_cases hm with hx | hx <;>
        · rw [hx] at h3 h4 h5
          rw [hx, imgInstr_reg_of_caret_free slotArr c _ (by decide) (by decide) (by decide) h3
            h4 h5, evalInstrPMemFk_reg, ← hx] at hstep
          obtain ⟨sa', hst, hr⟩ := rel_sstoreW hsep hphys P hrel hb hc hci hgS hSW' hstep
          refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
          rw [stepA_lopn frame hb hx, ← hst, hx,
            tagAt_reg_of_caret_free (by decide) (by decide) (by decide) h3]
    | scmp d y q =>
        rw [hc] at hg
        simp only [gateReadSet, hc] at hrd
        have hn := slotCmp?_eq (icase_scmp hc).1
        obtain ⟨o, ho, hx⟩ := eq_of_normA_lopn hn (by simp [withWidthTag])
        have hyW : y ∉ oneBitAt frame c sa.reg.lpc :=
          readOkB_spec hrd (by rw [hx]; simp [readNames, srcNames]) (by rw [hx]; simp [carryIns])
        have hsafe := loadSafe_of (rsp := rsp) hb
          (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
        have h3 : bitMovB c sa.reg.lpc (.Lopn [.reg d] o [.reg y, .reg q]) = false :=
          bitMovB_of_ne (by simp [movImmStruct?])
        rw [hx, imgInstr_reg slotArr c _ (by simp [ho]) (by simp [ho]) (by simp [ho, castTagW])
          h3 (bitStore?_of_ne (by simp)) (cellIdxStore?_of_ne slotArr (by simp)) (by simp [ho])
          (by simp [ho]), evalInstrPMemFk_reg, ← hx] at hstep
        obtain ⟨sa', hst, hr⟩ := rel_scmpW hphys P hrel hb hc hci (by simpa using hg) hyW
          (readOkB_spec hrd (by rw [hx]; simp [readNames, srcNames])
            (by rw [hx]; simp [carryIns])) hstep
        refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
        rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg (by simp [ho]) (by simp [ho])
          (by simp [ho, castTagW]) h3 (by simp [ho]) (by simp [ho])]
    | reg =>
        rw [hc] at hg
        simp only [gateReadSet, hc] at hrd
        obtain ⟨ds, o, ss, hx, ho1, ho2, hko, hz1, hz2⟩ := icase_reg_untagCaret hc
        have hsafe := loadSafe_of (rsp := rsp) hb
          (notLoad_of_icase (by intro d' b' idx'; rw [hc]; simp))
        cases hmi : movImmStruct? bi.li_i with
        | some p =>
          -- a carry constant
          obtain ⟨D, n⟩ := p
          rw [hmi] at hg
          simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hg
          obtain ⟨hbit, hD⟩ := hg
          obtain ⟨D', n', ⟨om, hx'⟩, -, -, -⟩ := bitMovB_spec hbit
          obtain ⟨hmo, rfl⟩ : isMovImmMnem om = true ∧ D' = D := by
            rw [hx'] at hmi
            simp only [movImmStruct?] at hmi
            split_ifs at hmi with h
            simp only [Option.some.injEq, Prod.mk.injEq] at hmi
            exact ⟨h, hmi.1⟩
          have hbit' := hbit
          rw [hx'] at hbit'
          have ho64 : om ≠ "MOV:64" := fun e => by rw [e, isMovImmMnem_mov64] at hmo; cases hmo
          have hi : imgInstr slotArr c sa.reg.lpc bi.li_i = (normA bi.li_i, .reg (some 1)) := by
            rw [hx']; simp [imgInstr, bitStore?, cellIdxStore?, arrImmImg, tagAt, hbit', ho64]
          rw [hi] at hstep
          have hstep' : evalInstrPMemF P (normA bi.li_i, .reg (some 1)) s = some t := by
            simpa [evalInstrPMemFk, idxOkB] using hstep
          obtain ⟨sa', hst, hr⟩ : ∃ sa', fstepA frame (normA bi.li_i, .reg (some 1)) sa s.zf
              = some (sa', t.zf) ∧ ImgRelW frame slotArr base c t sa' t.zf := by
            rcases hD with ⟨-, hD⟩ | ⟨hDs, hDa⟩
            · exact rel_bmovW hphys P hrel hb hx' hmo hc hci hD hstep'
            · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hDs
              exact rel_bmovSlotW hsep P hrel hb hx' hmo hc hci ha hDa hstep'
          refine ⟨haltedA_of hb (by rw [hx']; simp), hsafe, sa', ?_, hr⟩
          rw [stepA_lopn frame hb hx', ← hst]
          simp [tagAt, hbit]
        | none =>
          rw [hmi] at hg
          have h3 : bitMovB c sa.reg.lpc bi.li_i = false := bitMovB_of_ne hmi
          rw [hx] at h3
          cases hbs : bitStore? c sa.reg.lpc bi.li_i with
          | some p =>
            -- a stored carry constant
            obtain ⟨q, n⟩ := p
            rw [hbs] at hg
            obtain ⟨q', v, a, hx', hq, hA⟩ := sImmB_spec hg
            have hqv := hx'.symm.trans (bitStore?_spec hbs).1
            simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
              LOperand.imm.injEq, and_true, true_and] at hqv
            obtain ⟨rfl, rfl⟩ := hqv
            rw [imgInstr_bitStore slotArr hbs] at hstep
            have hstep' : evalInstrPMemF P (.Lopn [.reg q'] "MOV" [.imm v], .reg (some 1)) s
                = some t := by
              simpa [evalInstrPMemFk, idxOkB] using hstep
            obtain ⟨sa', hst, hr⟩ := rel_bstoreW hsep P hrel hb hbs hq hA hstep'
            refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
            rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg ho1 ho2 hko h3 hz1 hz2]
          | none =>
            have h4 : bitStore? c sa.reg.lpc (.Lopn ds o ss) = none := by rw [← hx]; exact hbs
            rw [hbs] at hg
            have h5 : cellIdxStore? slotArr c sa.reg.lpc (.Lopn ds o ss) = none := by
              rw [← hx]; exact cellIdxStore?_of_regArmW hg
            rw [hx, imgInstr_reg slotArr c _ ho1 ho2 hko h3 h4 h5 hz1 hz2, evalInstrPMemFk_reg, ← hx]
              at hstep
            obtain ⟨sa', hst, hr⟩ : ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa s.zf
                = some (sa', t.zf) ∧ ImgRelW frame slotArr base c t sa' t.zf := by
              cases hsi : sImmB frame slotArr bi.li_i with
              | true =>
                -- an immediate move into a frame word
                obtain ⟨q, v, a, hx', hq, hA⟩ := sImmB_spec hsi
                exact rel_stiW hsep P hrel hb hx' hq hA hbs hstep
              | false =>
                cases hsv : sCmovB frame slotArr bi.li_i with
                | true =>
                  -- a select with a frame-word value or destination
                  obtain ⟨D, C, A, B, hx', hD, hC, hA, hAC, hsl⟩ := sCmovB_spec hsv
                  have hAW : A ∉ oneBitAt frame c sa.reg.lpc :=
                    readOkB_spec hrd (by rw [hx']; simp [readNames, srcNames])
                      (by rw [hx']; simp [carryIns, hAC])
                  cases hfD : frame D with
                  | none =>
                    exact rel_scmovW hphys P hrel hb hx' hfD hC hA hAW hstep
                  | some aD =>
                    exact rel_scmovDstW hsep hphys P hrel hb hx' hfD
                      (hD.resolve_left (by simp [hfD])) hC hA hAW hstep
                | false =>
                  have hg' : regGateBW frame (oneBitAt frame c sa.reg.lpc) (normA bi.li_i)
                      = true ∧ cmovCondOkB (oneBitAt frame c sa.reg.lpc) bi.li_i = true := by
                    simpa [hsi, hsv] using hg
                  exact rel_regW hsep hphys P hrel hb hc hci hmi hbs hg'.1 hrd hg'.2 hstep
            refine ⟨haltedA_of hb (by rw [hx]; simp), hsafe, sa', ?_, hr⟩
            rw [stepA_lopn frame hb hx, ← hst, hx, tagAt_reg ho1 ho2 hko h3 hz1 hz2]

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
    rw [ite_eq_left hlt] at h
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

/-- **The read widths.** Under `ImgRelW` at a body passing `imgGateBW`, every general-purpose
    name the instruction at the program counter reads, other than a carry-in, the source of a
    cast with an entry in the cast width analysis and the one-bit source of a frame-word store
    (`bitSrc`), holds a 64-bit value. -/
theorem wideSafe_of_gateW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hgate : imgGateBW frame slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) : WideSafeAt body sa := by
  intro ii ds o ss hb r hr hg hc hn
  obtain ⟨-, hgk⟩ := imgGateBW_at hgate hb (by simp)
  simp only [instrGateBW, gateAtW, Bool.and_eq_true, Bool.or_eq_true] at hgk
  have hro : readOkB (gateReadSet frame (oneBitAt frame body sa.reg.lpc) (.Lopn ds o ss))
      (.Lopn ds o ss) = true := by
    rcases hgk.1 with h | hcr
    · exact h
    · exfalso
      apply hn
      unfold castReadB at hcr
      split at hcr
      · rename_i d a m w heq
        obtain ⟨o', hx, -, hw, hci, hic, -, -⟩ := cast_facts frame heq
        simp only [LinstrR.Lopn.injEq] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        have hG := hgk.2
        rw [hci, hic] at hG
        simp only [castGateB, heq, Bool.and_eq_true] at hG
        obtain ⟨⟨⟨hgd, hga⟩, -⟩, -⟩ := hG
        have hra : r = a := by
          rcases hr with rfl | ⟨-, hx⟩ | hr' | hr'
          · exact absurd hg (by decide)
          · simp [readsRdx, JasminLsemAddrCongr.rdxShape] at hx
          · simpa [srcNames] using hr'
          · simp [cellBase, DecodePrintedAddr.cellParts?_gp hgd,
              DecodePrintedAddr.cellParts?_gp hga] at hr'
        subst hra
        simp [narrowSrc, hb, heq, hcr]
      · cases hcr
  have hmem : r ∈ readNames (.Lopn ds o ss) := by
    rcases hr with rfl | ⟨rfl, hx⟩ | hr' | hr'
    · exact absurd hg (by decide)
    · simp [readNames, hx]
    · exact List.mem_append_right _ (List.mem_append_left _ hr')
    · exact List.mem_append_right _ (List.mem_append_right _ hr')
  by_cases hst : ∃ q, icase frame (.Lopn ds o ss) = .sstore q r
  · obtain ⟨q, hq⟩ := hst
    have hm := (icase_sstore hq).1
    have hcn : carryI? (.Lopn ds o ss) = none := by
      rcases slotMov?_cases hm with hx | hx <;> rw [hx] <;> rfl
    have hG := hgk.2
    rw [hcn, hq] at hG
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hG
    rcases hG.2 with h | ⟨⟨hcd, hgq⟩, hcp⟩
    · exact hrel.wid r hg h
    · rcases hrel.bits r hg hcd with h | h
      · exact h
      · exfalso
        apply hn
        apply List.mem_append_right
        unfold bitSrc
        rw [hb]
        simp only
        rw [hm]
        simp [hgq, hcp, h]
  · push Not at hst
    by_cases hsl : ∃ d, icase frame (.Lopn ds o ss) = .sload d r
    · obtain ⟨d, hd⟩ := hsl
      have hm := (icase_sload hd).1
      have hcn : carryI? (.Lopn ds o ss) = none := by
        rcases slotMov?_cases hm with hx | hx <;> rw [hx] <;> rfl
      have hG := hgk.2
      rw [hcn, hd] at hG
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hG
      rcases hG.2 with h | ⟨-, h⟩
      · exact hrel.wid r hg h
      · rw [hg] at h; cases h
    · push Not at hsl
      exact hrel.wid r hg (readOkB_gateReadSet_spec hro hmem hc hst hsl)

section Congr

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (icase_congr regOkB_congr)

variable {frame frame' : String → Option (BitVec 64)}

theorem oneBitStep_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (W : List String)
    (x : LinstrR) : oneBitStep frame W x = oneBitStep frame' W x := by
  simp only [oneBitStep, icase_congr h]

theorem oneBitAt0_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (body : Lcmd)
    (k : Nat) : oneBitAt0 frame body k = oneBitAt0 frame' body k := by
  simp only [oneBitAt0, oneBitStepAt0, oneBitStep_congr h]

theorem seedAt_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (body : Lcmd)
    (k : Nat) (x : LinstrR) : seedAt frame body k x = seedAt frame' body k x := by
  cases x <;> simp only [seedAt, backNames, oneBitAt0_congr h]

theorem oneBitAt_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (body : Lcmd)
    (k : Nat) : oneBitAt frame body k = oneBitAt frame' body k := by
  simp only [oneBitAt, oneBitStepAt, oneBitStep_congr h, seedAt_congr h]

theorem gateReadSet_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (W : List String)
    (x : LinstrR) : gateReadSet frame W x = gateReadSet frame' W x := by
  simp only [gateReadSet, icase_congr h]

theorem regGateBW_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (W : List String)
    (x : LinstrR) : regGateBW frame W x = regGateBW frame' W x := by
  simp only [regGateBW, regOkB_congr h]

theorem sImmB_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome)
    (slotArr : String → Option (String × Nat)) (x : LinstrR) :
    sImmB frame slotArr x = sImmB frame' slotArr x := by
  unfold sImmB
  split <;> simp only [h]

theorem sCmovB_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome)
    (slotArr : String → Option (String × Nat)) (x : LinstrR) :
    sCmovB frame slotArr x = sCmovB frame' slotArr x := by
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
    have hcg : castGateB frame x = castGateB frame' x := by simp only [castGateB, hn]
    simp only [instrGateBW, gateAtW, carryOkB, oneBitAt_congr h, icase_congr h, gateReadSet_congr h,
      regGateBW_congr h, sImmB_congr h, sCmovB_congr h, hcg, hn, h]
  simp only [imgGateBW, hi]

/-- `retOutsB` reads only which names have a frame word. -/
theorem retOutsB_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (body : Lcmd)
    (outs : List String) : retOutsB frame body outs = retOutsB frame' body outs := by
  simp only [retOutsB, oneBitAt_congr h]

end Congr

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
