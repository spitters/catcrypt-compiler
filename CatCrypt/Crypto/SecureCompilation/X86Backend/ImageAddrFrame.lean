/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode

@[expose] public section

set_option autoImplicit false

/-!
# The frame and the separation of the image simulation

`ImageAddrSim.image_addr_sim` is stated for a frame map `frame` and a separation
`ImageAddrSim.ImgSep`. The frame of a printed body is `DecodePrintedAddr.frameP` at the
stack pointer `DecodePrintedCFG.frameRsp`, which gives an address to every spill and save
name, also to names the body does not mention. The address machine reads the frame only at
the names of the instruction it steps (`fstepA_congr`), so its runs at `frameP` are its runs
at the frame restricted to the names of the body (`frameIn`, `runA_frameIn`,
`runSafe_frameIn`).

At the restricted frame the separation follows from the entry precondition of the layout
(`AbiLayout.Regions`) and from decided checks on the body and the layout: the frame offsets
of the names of the body lie in the frame range of the layout and are pairwise at least eight
bytes apart, and so is the red-zone word (`frameOkB`); the regions pass `rsOK`
(`imgSep_of_regions`).

## Main results

* `bodyNamesI`, `frameIn`: the names of a body and the frame restricted to them.
* `fstepA_congr`, `stepA_congr`, `runA_congr`, `runSafe_congr`, `runA_frameIn`,
  `runSafe_frameIn`: the address machine reads the frame only at the names of the body.
* `frameOkB`, `imgSep_of_regions`: the separation from the layout.
* `imgRel_entry`: the relation at entry.
* `icase_congr`, `imgGateB_congr`, `frameIn_isSome`: the gate reads only which names have a
  frame word, so it may be decided at any stack pointer.
* `image_bytes`: a halting checked run of the image on the decoded bytes, with its arrays in
  memory (`image_addr_sim`, `printedAddr_sim`).
* `virt_bytes`: a halting run in bounds of a virtual body that `ownedCheckMC` accepts against
  the image, on the decoded bytes, with its arrays in memory.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (LoadSafeAt RunSafe)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (slotMov?_cases slotCmp?_eq)

/-! ## 1. The frame at the names of a body -/

/-- The register names the instructions of a body mention. -/
def bodyNamesI (body : Lcmd) : List String := body.flatMap fun i => instrNames i.li_i

/-- The frame `frame` restricted to the names of `body`. -/
def frameIn (body : Lcmd) (frame : String → Option (BitVec 64)) (q : String) :
    Option (BitVec 64) :=
  if q ∈ bodyNamesI body then frame q else none

theorem instrNames_normA (x : LinstrR) : instrNames (normA x) = instrNames x := by
  cases x <;> rfl

/-- The address machine reads the frame only at the names of the instruction it steps. -/
theorem fstepA_congr {frame frame' : String → Option (BitVec 64)} {x : LinstrR}
    (h : ∀ q ∈ instrNames x, frame q = frame' q) (tag : MemTag) (sa : LstateA) (zf : Bool) :
    fstepA frame (x, tag) sa zf = fstepA frame' (x, tag) sa zf := by
  unfold fstepA
  cases tag with
  | reg c =>
      simp only
      cases hm : slotMov? x with
      | some ds =>
          obtain ⟨d, s⟩ := ds
          have hd : d ∈ instrNames x ∧ s ∈ instrNames x := by
            rcases slotMov?_cases hm with rfl | rfl <;> simp [instrNames,
              JasminLsemExportRewrites.opNames]
          simp only
          rw [h s hd.2, h d hd.1]
      | none =>
          simp only
          cases hk : slotCmp? x with
          | some dyq =>
              obtain ⟨d, y, q⟩ := dyq
              have hq : q ∈ instrNames x := by
                rw [slotCmp?_eq hk]; simp [instrNames, JasminLsemExportRewrites.opNames]
              simp only
              rw [h q hq]
          | none => rfl
  | _ => rfl

theorem stepA_congr {frame frame' : String → Option (BitVec 64)} {body : Lcmd}
    (h : ∀ q ∈ bodyNamesI body, frame q = frame' q) (s : LstateA) (zf : Bool) :
    stepA frame body s zf = stepA frame' body s zf := by
  unfold stepA
  cases hb : body[s.reg.lpc]? with
  | none => rfl
  | some i =>
      obtain ⟨ii, li⟩ := i
      cases li with
      | Lopn ds o ss =>
          simp only
          refine fstepA_congr (fun q hq => h q ?_) _ s zf
          rw [instrNames_normA] at hq
          simp only [bodyNamesI, List.mem_flatMap]
          exact ⟨⟨ii, .Lopn ds o ss⟩, List.mem_of_getElem? hb, hq⟩
      | Lcond c l => cases c <;> rfl
      | _ => rfl

theorem runA_congr {frame frame' : String → Option (BitVec 64)} {body : Lcmd}
    (h : ∀ q ∈ bodyNamesI body, frame q = frame' q) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool),
      runA frame body fuel s zf = runA frame' body fuel s zf
  | 0, _, _ => rfl
  | fuel + 1, s, zf => by
      simp only [runA, stepA_congr h s zf]
      cases stepA frame' body s zf with
      | none => rfl
      | some bz => simp only [Option.bind_some, runA_congr h fuel bz.1 bz.2]

theorem runSafe_congr {frame frame' : String → Option (BitVec 64)} {body : Lcmd}
    (h : ∀ q ∈ bodyNamesI body, frame q = frame' q) (Q : LstateA → Prop) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool),
      RunSafe frame body Q fuel s zf ↔ RunSafe frame' body Q fuel s zf
  | 0, _, _ => Iff.rfl
  | fuel + 1, s, zf => by
      simp only [RunSafe, stepA_congr h s zf]
      constructor
      · rintro ⟨hq, hn⟩
        exact ⟨hq, fun s' z' hs => (runSafe_congr h Q fuel s' z').mp (hn s' z' hs)⟩
      · rintro ⟨hq, hn⟩
        exact ⟨hq, fun s' z' hs => (runSafe_congr h Q fuel s' z').mpr (hn s' z' hs)⟩

theorem frameIn_eq {body : Lcmd} {frame : String → Option (BitVec 64)} :
    ∀ q ∈ bodyNamesI body, frameIn body frame q = frame q := by
  intro q hq
  simp [frameIn, hq]

/-- The runs of the address machine at the restricted frame are its runs at the frame. -/
theorem runA_frameIn (body : Lcmd) (frame : String → Option (BitVec 64)) (fuel : Nat)
    (s : LstateA) (zf : Bool) :
    runA (frameIn body frame) body fuel s zf = runA frame body fuel s zf :=
  runA_congr frameIn_eq fuel s zf

theorem runSafe_frameIn (body : Lcmd) (frame : String → Option (BitVec 64))
    (Q : LstateA → Prop) (fuel : Nat) (s : LstateA) (zf : Bool) :
    RunSafe (frameIn body frame) body Q fuel s zf ↔ RunSafe frame body Q fuel s zf :=
  runSafe_congr frameIn_eq Q fuel s zf

/-! ## 2. The separation from the layout -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (spillQsaveOff cmovRedZone)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (frameSize bodyIsU64 qsaveBytesFor)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP frameP_gp redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen regK regLay)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode
  (rsOK abiBase abiReg cells_disjoint frameSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState Disjoint8 disjoint8_add_ofInt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep cellAt)

/-- The frame offset of a name in the printed body, from the stack pointer after the
    prologue. -/
def offOf (body : Lcmd) (q : String) : Option Int :=
  spillQsaveOff (Params.ofBody body).frame (Params.ofBody body).spillW q
    (Params.ofBody body).qsaveB

/-- The frame offsets of the distinct names of a body that have one, from the stack pointer
    after the prologue. The frame size, spill width and save block are those of
    `Params.ofBody`, computed once. -/
def frameOffs (body : Lcmd) : List Int :=
  let F := frameSize body
  let W := if bodyIsU64 body then 64 else 32
  let Q := qsaveBytesFor body
  (bodyNamesI body).eraseDups.filterMap fun q => spillQsaveOff F W q Q

/-- Two frame offsets are at least eight and at most `2 ^ 64 - 8` bytes apart. -/
def sep8B (o o' : Int) : Bool := decide (8 ≤ (o - o').natAbs ∧ (o - o').natAbs ≤ 2 ^ 64 - 8)

/-- Every two entries at distinct positions of a list of frame offsets pass `sep8B`. -/
def pairSepB : List Int → Bool
  | [] => true
  | o :: os => os.all (sep8B o) && pairSepB os

/-- **The frame check.** The frame word of each name of the body and the red-zone word lie
    in the frame range of the layout, from the entry stack pointer; the frame words of two
    distinct names of the body are at least eight bytes apart. -/
def frameOkB (σ : AbiLayout) (body : Lcmd) : Bool :=
  let F : Int := frameSize body
  let os := frameOffs body
  os.all (fun o => decide (σ.frameLo ≤ o - F ∧ o - F ≤ σ.frameHi))
    && decide (σ.frameLo ≤ cmovRedZone - F ∧ cmovRedZone - F ≤ σ.frameHi)
    && pairSepB os

theorem sep8B_comm (o o' : Int) : sep8B o o' = sep8B o' o := by
  have h : (o - o').natAbs = (o' - o).natAbs := by rw [← Int.natAbs_neg, Int.neg_sub]
  simp only [sep8B, h]

theorem pairSepB_pairwise : ∀ {os : List Int}, pairSepB os = true →
    os.Pairwise (fun a b => sep8B a b = true)
  | [], _ => List.Pairwise.nil
  | o :: os, h => by
    simp only [pairSepB, Bool.and_eq_true, List.all_eq_true] at h
    exact List.pairwise_cons.mpr ⟨h.1, pairSepB_pairwise h.2⟩

/-- Two distinct members of a list pairwise related by a symmetric relation are related. -/
theorem pairwise_of_ne {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | _ :: _, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hne
    · exact h.1 b hb'
    · exact hs _ _ (h.1 a ha')
    · exact pairwise_of_ne hs h.2 ha' hb' hne

theorem mem_frameOffs {body : Lcmd} {q : String} {o : Int} (hq : q ∈ bodyNamesI body)
    (ho : offOf body q = some o) : o ∈ frameOffs body := by
  simp only [frameOffs, List.mem_filterMap, List.mem_eraseDups]
  exact ⟨q, hq, ho⟩

theorem frameOkB_range {σ : AbiLayout} {body : Lcmd} (hf : frameOkB σ body = true)
    {q : String} {o : Int} (hq : q ∈ bodyNamesI body) (ho : offOf body q = some o) :
    σ.frameLo ≤ o - (Params.ofBody body).frame ∧ o - (Params.ofBody body).frame ≤ σ.frameHi := by
  simp only [frameOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hf
  exact hf.1.1 o (mem_frameOffs hq ho)

theorem frameOkB_red {σ : AbiLayout} {body : Lcmd} (hf : frameOkB σ body = true) :
    σ.frameLo ≤ cmovRedZone - (Params.ofBody body).frame
      ∧ cmovRedZone - (Params.ofBody body).frame ≤ σ.frameHi := by
  simp only [frameOkB, Bool.and_eq_true, decide_eq_true_eq] at hf
  exact hf.1.2

theorem frameOkB_pair {σ : AbiLayout} {body : Lcmd} (hf : frameOkB σ body = true)
    {q q' : String} {o o' : Int} (hq : q ∈ bodyNamesI body) (hq' : q' ∈ bodyNamesI body)
    (hne : q ≠ q') (ho : offOf body q = some o) (ho' : offOf body q' = some o') :
    8 ≤ (o - o').natAbs ∧ (o - o').natAbs ≤ 2 ^ 64 - 8 := by
  simp only [frameOkB, Bool.and_eq_true] at hf
  have hp := pairSepB_pairwise hf.2
  simp only [frameOffs, List.pairwise_filterMap] at hp
  have h := pairwise_of_ne (fun a b hab x hx y hy => by rw [sep8B_comm]; exact hab y hy x hx)
    hp (List.mem_eraseDups.mpr hq) (List.mem_eraseDups.mpr hq') hne o ho o' ho'
  simpa only [sep8B, decide_eq_true_eq] using h

theorem frameIn_some {body : Lcmd} {sa : AState} {q : String} {a : BitVec 64}
    (h : frameIn body (frameP (Params.ofBody body) (frameRsp body sa)) q = some a) :
    q ∈ bodyNamesI body ∧ ∃ o, offOf body q = some o
      ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 (o - (Params.ofBody body).frame) := by
  unfold frameIn at h
  split at h
  · rename_i hq
    refine ⟨hq, ?_⟩
    unfold frameP at h
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨o, ho, ?_⟩
    simp only [frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
    congr 2
    simp only [Int.ofNat_eq_natCast]
    omega
  · cases h

/-- **The separation from the layout.** At the entry state `sa` of a layout `σ` whose
    regions `rs` pass `rsOK`, under the entry precondition `σ.Regions sa` and the frame check,
    the restricted frame of the body, an array map whose arrays are the regions at their
    lengths and have frame words, and the entry bases of the regions are separated. -/
theorem imgSep_of_regions {σ : AbiLayout} {rs : List Region} (hrs : rsOK σ rs = true)
    {sa : AState} (h : σ.Regions sa) {body : Lcmd} (hf : frameOkB σ body = true)
    {slotArr : String → Option (String × Nat)}
    (hsl : ∀ q A n, slotArr q = some (A, n) → regLen rs A = n)
    (hslf : ∀ q A n, slotArr q = some (A, n) →
      ∃ a, frameIn body (frameP (Params.ofBody body) (frameRsp body sa)) q = some a) :
    ImgSep (frameIn body (frameP (Params.ofBody body) (frameRsp body sa))) slotArr
      (abiBase (abiReg σ) sa) (frameRsp body sa) := by
  have hred := frameOkB_red hf
  have hword : ∀ q a, frameIn body (frameP (Params.ofBody body) (frameRsp body sa)) q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o := by
    intro q a ha
    obtain ⟨hq, o, ho, rfl⟩ := frameIn_some ha
    have := frameOkB_range hf hq ho
    exact ⟨_, this.1, this.2, rfl⟩
  have hcell : ∀ q A n j, slotArr q = some (A, n) → j < n → regK rs A j := by
    intro q A n j hq hj
    unfold regK
    rw [hsl q A n hq]
    exact hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hslf⟩
  · intro q q' a a' ha ha' hne
    obtain ⟨hq, o, ho, rfl⟩ := frameIn_some ha
    obtain ⟨hq', o', ho', rfl⟩ := frameIn_some ha'
    have hd := frameOkB_pair hf hq hq' hne ho ho'
    have he : (o - ↑(Params.ofBody body).frame - (o' - ↑(Params.ofBody body).frame)) = o - o' := by
      omega
    apply disjoint8_add_ofInt
    · rw [he]; exact hd.1
    · rw [he]; exact hd.2
  · intro q A n j hq hj q' a ha
    obtain ⟨o, h1, h2, rfl⟩ := hword q' a ha
    exact (frameSep_of_regions hrs h A j (hcell q A n j hq hj) o h1 h2).symm
  · intro q A n q' A' n' j j' hq hq' hj hj' hne
    exact cells_disjoint hrs h (hcell q A n j hq hj) (hcell q' A' n' j' hq' hj') (by
      rintro ⟨rfl, rfl⟩
      rcases hne with hne | hne <;> exact hne rfl)
  · intro q q' A n n' hq hq'
    rw [← hsl q A n hq, ← hsl q' A n' hq']
  · intro q A n j hq hj
    have hr : redW (frameRsp body sa)
        = sa.regs "%rsp" + BitVec.ofInt 64 (cmovRedZone - (Params.ofBody body).frame) := by
      simp only [redW, frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
      congr 2
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hr]
    exact frameSep_of_regions hrs h A j (hcell q A n j hq hj) _ hred.1 hred.2
  · intro r hr
    unfold frameIn
    split
    · exact frameP_gp hr
    · rfl

/-! ## 3. The relation at entry -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (read64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgRel)

/-- **The relation at entry.** At program counter `0`, a name-keyed state and an address
    state are related when they agree off the frame words and on the flags, every frame-word
    name holds its frame word, every general-purpose name of the address state has width
    `64`, every array holds the words at its base, and every register whose frame word is the
    pointer of an array holds the base of the array. -/
theorem imgRel_entry {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hpc : sa.reg.lpc = 0)
    (hspc : s.prog.base.reg.lpc = 0)
    (hregs : ∀ r, frame r = none → s.prog.base.reg.lvm r = sa.reg.lvm r)
    (hslots : ∀ q a, frame q = some a → s.prog.base.reg.lvm q = ⟨64, read64 sa.mem a⟩)
    (hz : s.zf = zf) (hc : sa.cf = s.prog.base.cf) (ho : sa.of = s.prog.base.of)
    (hwid : ∀ r, gpOk r = true → (sa.reg.lvm r).1 = 64)
    (hcells : ∀ q A n, slotArr q = some (A, n) →
      s.prog.base.getArr A 64 n = some (fun i => read64 sa.mem (cellAt (base A) i.val)))
    (hptr : ∀ R A n, slotArr (slotOfReg R) = some (A, n) → sa.reg.getW R 64 = some (base A)) :
    ImgRel frame slotArr base body s sa zf := by
  refine ⟨by rw [hpc, hspc], hregs, hslots, hz, hc, ho, hwid,
    fun q A n hq => ⟨_, hcells q A n hq, fun j hj => rfl⟩,
    fun k R A n a _ hA _ => ⟨fun hk => by omega, fun _ => hptr R A n hA⟩,
    fun b q a i h1 => by omega⟩

/-! ## 4. The gate reads which names have a frame word -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
  (icase instrGateB regGateB regOkB imgGateB ICase)

section Congr

variable {frame frame' : String → Option (BitVec 64)}

theorem icase_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (x : LinstrR) :
    icase frame x = icase frame' x := by
  unfold icase
  split
  all_goals try rfl
  split_ifs
  · rfl
  · rename_i _ ds o ss _ _ _
    cases hm : slotMov? (LinstrR.Lopn ds o ss) with
    | some p =>
        obtain ⟨d, q⟩ := p
        simp only
        have hd := h d
        have hq := h q
        cases e1 : frame d <;> cases e2 : frame' d <;> cases e3 : frame q <;>
          cases e4 : frame' q <;> simp_all
    | none =>
        simp only
        cases hk : slotCmp? (LinstrR.Lopn ds o ss) with
        | some p =>
            obtain ⟨d, y, q⟩ := p
            simp only [h q]
        | none => rfl

theorem regOkB_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (x : LinstrR) :
    regOkB frame x = regOkB frame' x := by
  have hn : ∀ q, (frame q).isNone = (frame' q).isNone := fun q => by
    have := h q; cases e : frame q <;> cases e' : frame' q <;> simp_all
  simp only [regOkB, hn]

theorem regGateB_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome) (x : LinstrR) :
    regGateB frame x = regGateB frame' x := by
  simp only [regGateB, regOkB_congr h]

theorem imgGateB_congr (h : ∀ q, (frame q).isSome = (frame' q).isSome)
    (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    imgGateB frame slotArr body = imgGateB frame' slotArr body := by
  have hn : ∀ q, (frame q).isNone = (frame' q).isNone := fun q => by
    have := h q; cases e : frame q <;> cases e' : frame' q <;> simp_all
  have hi : ∀ k x, instrGateB frame slotArr body k x = instrGateB frame' slotArr body k x := by
    intro k x
    simp only [instrGateB, icase_congr h, regGateB_congr h, hn]
  simp only [imgGateB, hi]

end Congr

theorem frameIn_isSome (body : Lcmd) (r r' : BitVec 64) (q : String) :
    (frameIn body (frameP (Params.ofBody body) r) q).isSome
      = (frameIn body (frameP (Params.ofBody body) r') q).isSome := by
  unfold frameIn frameP
  split <;> simp

/-- The distinct names of a body that have a frame word. The frame size, spill width and
    save block are those of `Params.ofBody`, computed once. -/
def frameNames (body : Lcmd) : List String :=
  let F := frameSize body
  let W := if bodyIsU64 body then 64 else 32
  let Q := qsaveBytesFor body
  (bodyNamesI body).eraseDups.filter fun q => (spillQsaveOff F W q Q).isSome

/-- The frame map that gives the word `0` to the names of `N` and no word to other names. -/
def frameMark (N : List String) (q : String) : Option (BitVec 64) :=
  if q ∈ N then some 0 else none

/-- The names with a frame word under `frameMark (frameNames body)` are those under the
    restricted frame of the body at any stack pointer. -/
theorem frameMark_isSome (body : Lcmd) (r : BitVec 64) (q : String) :
    (frameMark (frameNames body) q).isSome
      = (frameIn body (frameP (Params.ofBody body) r) q).isSome := by
  by_cases hq : q ∈ bodyNamesI body
  · have e2 : frameIn body (frameP (Params.ofBody body) r) q
        = frameP (Params.ofBody body) r q := if_pos hq
    rw [e2]
    unfold frameP
    rw [Option.isSome_map]
    by_cases ho : (offOf body q).isSome = true
    · have h1 : q ∈ frameNames body := by
        simp only [frameNames, List.mem_filter, List.mem_eraseDups]
        exact ⟨hq, ho⟩
      have e1 : frameMark (frameNames body) q = some 0 := if_pos h1
      rw [e1]
      exact ho.symm
    · have h1 : q ∉ frameNames body := by
        simp only [frameNames, List.mem_filter, List.mem_eraseDups, not_and]
        exact fun _ => ho
      have e1 : frameMark (frameNames body) q = none := if_neg h1
      rw [e1]
      exact (Bool.eq_false_iff.mpr ho).symm
  · have h1 : q ∉ frameNames body := by
      simp only [frameNames, List.mem_filter, List.mem_eraseDups, not_and]
      exact fun h => absurd h hq
    have e1 : frameMark (frameNames body) q = none := if_neg h1
    have e2 : frameIn body (frameP (Params.ofBody body) r) q = none := if_neg hq
    rw [e1, e2]

/-- The gate of the image simulation at the restricted frame of a body, at any stack
    pointer, is the gate at `frameMark (frameNames body)`. -/
theorem imgGateB_frameMark (body : Lcmd) (r : BitVec 64)
    (slotArr : String → Option (String × Nat)) :
    imgGateB (frameIn body (frameP (Params.ofBody body) r)) slotArr body
      = imgGateB (frameMark (frameNames body)) slotArr body :=
  imgGateB_congr (fun q => (frameMark_isSome body r q).symm) slotArr body

/-! ## 5. The image on the decoded bytes -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (read64_eq_of_agree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB printedAddr_sim)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (imgGateB image_addr_sim)

/-- **The image on the decoded bytes.** For a printed body in the class `printedAddrB` that
    passes the gates of the image simulation at its frame and is separated, every halting
    checked run of the image from a state related to an address state at program counter
    `0` that corresponds to the machine state `sa` is matched by a halting run of the decoded
    bytes from `sa`, in which every array of the image at the end of its run is the words at
    its base. -/
theorem image_bytes {slotArr : String → Option (String × Nat)} {base : String → BitVec 64}
    {body : Lcmd} {sa : AState} (hpr : printedAddrB body = true)
    (hphys : physImgB slotArr body = true)
    (hgate : imgGateB (frameIn body (frameP (Params.ofBody body) (frameRsp body sa))) slotArr
      body = true)
    (hsep : ImgSep (frameIn body (frameP (Params.ofBody body) (frameRsp body sa))) slotArr base
      (frameRsp body sa))
    (fn : String) (b t : LstateMF) (hfn : b.prog.lfn = fn) (s : LstateA) (zf : Bool)
    (hrel : ImgRel (frameIn body (frameP (Params.ofBody body) (frameRsp body sa))) slotArr base
      body b s zf)
    (hpc : s.reg.lpc = 0) (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat)
    (hrun : lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) fuel b = some t) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ q A n, slotArr q = some (A, n) → ∃ arr, t.prog.base.getArr A 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (base A) j) = arr ⟨j, hj⟩ := by
  obtain ⟨fuel', s', zf', hrA, hrel', hsafe⟩ :=
    image_addr_sim hsep hphys hgate fn fuel b t s zf hfn hrel hrun
  rw [runA_frameIn] at hrA
  rw [runSafe_frameIn] at hsafe
  obtain ⟨prog, sa', hdec, hh, hrsp, -, hm'⟩ :=
    printedAddr_sim body hpr sa s zf hpc hent hmem fuel' (s', zf') hrA hsafe
  refine ⟨prog, sa', hdec, hh, hrsp, fun q A n hq => ?_⟩
  obtain ⟨arr, h1, h2⟩ := hrel'.cells q A n hq
  refine ⟨arr, h1, fun j hj => ?_⟩
  rw [← h2 j hj]
  exact (read64_eq_of_agree hm' (hsep.red q A n j hq hj)).symm

/-! ## 6. A virtual body, its image and the decoded bytes -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
  (RunIdxOk lsemFuelMemFk_of_runIdxOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
  (ownedCheckMC ownedCheckMC_sound)

/-- **A virtual body on the decoded bytes of its printed body.** Let the register allocation
    checker `ownedCheckMC` accept a virtual body `B` against the image of a printed body that
    passes the gates and is separated. A halting run of `lsemFuelMemF` on `B` from a state
    related to an address state that corresponds to the machine state `sa`, whose accesses
    are in bounds, is matched by a halting run of the decoded bytes from `sa`, in which every
    array of the image is, at the end, the words at its base, and equals the array of the
    same name at the end of the run of `B`. -/
theorem virt_bytes {slotArr : String → Option (String × Nat)} {base : String → BitVec 64}
    {body : Lcmd} {sa : AState} {outs : List String} {B : List LinstrRM}
    (hck : ownedCheckMC outs B (virtImg slotArr body) = true)
    (hpr : printedAddrB body = true) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB (frameIn body (frameP (Params.ofBody body) (frameRsp body sa))) slotArr
      body = true)
    (hsep : ImgSep (frameIn body (frameP (Params.ofBody body) (frameRsp body sa))) slotArr base
      (frameRsp body sa))
    (fn : String) (b t : LstateMF) (hfn : b.prog.lfn = fn) (hbpc : b.prog.base.reg.lpc = 0)
    (s : LstateA) (zf : Bool)
    (hrel : ImgRel (frameIn body (frameP (Params.ofBody body) (frameRsp body sa))) slotArr base
      body b s zf)
    (hpc : s.reg.lpc = 0) (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel b = some t)
    (hok : RunIdxOk (singletonProgM fn B) fuel b) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ q A n, slotArr q = some (A, n) → ∃ arr, t.prog.base.getArr A 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (base A) j) = arr ⟨j, hj⟩ := by
  have hck' := lsemFuelMemFk_of_runIdxOk true _ fuel b t hrun hok
  obtain ⟨f', t', hr', hobs⟩ := ownedCheckMC_sound hck fn b t hfn hbpc fuel hck'
  obtain ⟨prog, sa', hdec, hh, hrsp, hcells⟩ :=
    image_bytes hpr hphys hgate hsep fn b t' hfn s zf hrel hpc hent hmem f' hr'
  refine ⟨prog, sa', hdec, hh, hrsp, fun q A n hq => ?_⟩
  obtain ⟨arr, h1, h2⟩ := hcells q A n hq
  exact ⟨arr, by rw [ImageAddrSim.getArr_congr hobs.2.1.symm]; exact h1, h2⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame
