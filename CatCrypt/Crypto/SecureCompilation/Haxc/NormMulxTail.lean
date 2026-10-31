/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxFold
public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalfBase
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg

/-!
# The tail of the printed program commutes with the width reading of `MULX`

`RegionPostFuseLift.normMulxBody` reads every two-output `MULX` of a body at its width `MULX:64`.
The three passes after the fold stage leave both spellings of `MULX` verbatim and emit no
`MULX` of their own:

* the register re-allocation `LprogGpRealloc.reallocBody` re-allocates only runs of the
  fragment, whose alphabet excludes both spellings, and keeps every other instruction as a
  barrier;
* the two-address legaliser `TwoAddrLegalize.twoAddrBody` rewrites only a mnemonic the
  instruction set ties, and reads the body otherwise only through its operand names;
* the compare reload `CmpSpillReload.cmpReload` rewrites only a mnemonic of base `CMP`.

Composed with the basic-block optimiser (`NormMulxOpt.optimizeBasicBlocks_normMulxBody`) and the
fold stage (`NormMulxFold.foldIndexedBody_normMulxBody`), the printed program of the back half
commutes with `normMulxBody` on every function body.

## Main results

* `reallocBody_normMulxBody`: the register re-allocation commutes with `normMulxBody`.
* `twoAddrBody_normMulxBody`: the two-address legaliser commutes with `normMulxBody`.
* `cmpReload_normMulxBody`: the compare reload commutes with `normMulxBody`.
* `printedLprog_mapBodies_normMulxBody`: the printed program commutes with `normMulxBody` on every
  function body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxTail

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi IsaData)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (normMulx)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseLift (normMulxBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxOpt
  (normI normI_of_mnem stripWidthTag_mulx stripWidthTag_mulx64 optimizeBasicBlocks_normMulxBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxFold
  (normI_cases MulxShaped foldIndexedBody_normMulxBody withWidthTag_mulx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (instrMnem isRecognizedOpn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg
  (rstep reallocBody_eq reallocRun_out)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
  (legalizeInstr twoAddrBody bodyAvoids instrAvoids scratchRoute x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
  (spillCmp? cmpReloadI cmpReload movOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
  (foldIndexedBody constIndexFoldBody dropDeadCore bodyParams)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (bodyIsU64 stripAbiTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
  (mapBodies ownedLprog optimizeBasicBlocks)

/-! ## 1. The register re-allocation -/

/-- Unfolding lemma of `normMulxBody`: the width reading `normI` of every instruction. -/
theorem normMulxBody_eq_map (b : Lcmd) : normMulxBody b = b.map normI := rfl

/-- The width reading keeps the frame cells an instruction names. -/
theorem instrFrames_normMulx (r : LinstrR) : instrFrames (normMulx r) = instrFrames r := by
  cases r <;> simp [normMulx, instrFrames]

/-- The fragment view of an instruction is unchanged by the width reading when the alphabet
    excludes both spellings of `MULX`. -/
theorem fragOf?_normI {recog : String → Bool} (h1 : recog "MULX" = false)
    (h2 : recog "MULX:64" = false) (li : Linstr) :
    fragOf? (normI li) recog = fragOf? li recog := by
  rcases normI_cases li with h | ⟨ii, ds, ss, rfl, h⟩
  · rw [h]
  · rw [h]
    unfold fragOf?
    grind

/-- An instruction of the fragment is well formed and its mnemonic is in the alphabet. -/
theorem fragOf?_spec {recog : String → Bool} {li : Linstr} {i : FI}
    (h : fragOf? li recog = some i) : recog i.opn = true ∧ i.wf = true := by
  unfold fragOf? at h
  split at h
  · grind
  · simp at h

/-- The width reading of a piece: a barrier instruction is read at its width, a run is
    kept. -/
def normPiece : Piece → Piece
  | .run is => .run is
  | .bar li => .bar (normI li)

/-- The width reading keeps the frame cells of a piece. -/
theorem frames_normPiece (p : Piece) : (normPiece p).frames = p.frames := by
  cases p <;> simp [normPiece, Piece.frames, normI, instrFrames_normMulx]

/-- The pieces of a body commute with the width reading when the alphabet excludes both
    spellings of `MULX`. -/
theorem pieces_map_normI {recog : String → Bool} (h1 : recog "MULX" = false)
    (h2 : recog "MULX:64" = false) (b : Lcmd) :
    pieces (b.map normI) recog = (pieces b recog).map normPiece := by
  induction b with
  | nil => rfl
  | cons li rest ih =>
    have hfr : ∀ (l : Linstr) (c : Lcmd), pieces (l :: c) recog =
        (match fragOf? l recog with
          | some i =>
              match pieces c recog with
              | Piece.run is :: tl => Piece.run (i :: is) :: tl
              | _ => Piece.run [i] :: pieces c recog
          | none => Piece.bar l :: pieces c recog) := fun _ _ => rfl
    rw [List.map_cons, hfr, hfr, fragOf?_normI h1 h2, ih]
    cases fragOf? li recog with
    | none => rfl
    | some i => rcases pieces rest recog with _ | ⟨_ | _, _⟩ <;> rfl

/-- Every run of the pieces of a body consists of well-formed instructions of the
    alphabet. -/
theorem pieces_runs {recog : String → Bool} (b : Lcmd) :
    ∀ is, Piece.run is ∈ pieces b recog → ∀ i ∈ is, recog i.opn = true ∧ i.wf = true := by
  induction b with
  | nil => intro is h; simp [pieces] at h
  | cons li rest ih =>
    intro is h
    have hfr : pieces (li :: rest) recog =
        (match fragOf? li recog with
          | some i =>
              match pieces rest recog with
              | Piece.run is :: tl => Piece.run (i :: is) :: tl
              | _ => Piece.run [i] :: pieces rest recog
          | none => Piece.bar li :: pieces rest recog) := rfl
    rw [hfr] at h
    cases hf : fragOf? li recog with
    | none =>
      rw [hf] at h
      simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact ih is h
    | some i =>
      rw [hf] at h
      have hi := fragOf?_spec hf
      revert h ih
      rcases pieces rest recog with _ | ⟨_ | _, _⟩ <;> intro ih h <;> simp_all <;> grind

/-- The frame cells live out of every run are unchanged by the width reading. -/
theorem labelLiveFrames_map_normI (b : Lcmd) :
    labelLiveFrames (b.map normI) = labelLiveFrames b := by
  have hl : ∀ r : LinstrR, (match normMulx r with | .Llabel _ _ => true | _ => false)
      = (match r with | .Llabel _ _ => true | _ => false) := by
    intro r
    cases r <;> simp [normMulx]
  have ha : ((b.map normI).any fun li => match li.li_i with | .Llabel _ _ => true | _ => false)
      = b.any fun li => match li.li_i with | .Llabel _ _ => true | _ => false := by
    rw [List.any_map]
    exact congrArg _ (funext fun li => hl li.li_i)
  have hf : (b.map normI).flatMap (fun li => instrFrames li.li_i)
      = b.flatMap (fun li => instrFrames li.li_i) := by
    simp only [List.flatMap_map, normI, instrFrames_normMulx]
  grind [labelLiveFrames]

/-- One step of the re-allocation commutes with the width reading on a piece whose run has
    no `MULX` and only well-formed instructions. -/
theorem rstep_normPiece (res : List String) (abi : IsaAbi) (p : Piece)
    (hp : ∀ is, p = .run is → ∀ i ∈ is, i.opn ≠ "MULX" ∧ i.wf = true)
    (acc : Lcmd × Std.HashSet String) :
    rstep res abi (normPiece p) (acc.1.map normI, acc.2)
      = ((rstep res abi p acc).1.map normI, (rstep res abi p acc).2) := by
  rcases acc with ⟨X, S⟩
  cases p with
  | bar li =>
    simp [rstep, normPiece, Piece.frames, normI, instrFrames_normMulx]
  | run is =>
    have hwf : ∀ i ∈ is, i.wf = true := fun i hi => (hp is rfl i hi).2
    have hfix : ∀ L, ((reallocRun L is abi).map FI.toL).map normI
        = (reallocRun L is abi).map FI.toL := by
      intro L
      refine (List.map_congr_left fun j hj => ?_).trans (List.map_id _)
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hj
      obtain ⟨⟨i, hi, he⟩, _⟩ := (reallocRun_out L is hwf).2 k hk
      refine normI_of_mnem _ ?_
      change some k.opn ≠ some "MULX"
      rw [he]
      exact fun h => (hp is rfl i hi).1 (Option.some.inj h)
    simp only [rstep, normPiece, List.map_append, hfix]
    rcases X with _ | ⟨⟨ii, r⟩, X⟩
    · rfl
    · cases r <;> simp [normI, normMulx]

/-- The fold of the re-allocation commutes with the width reading. -/
theorem foldr_rstep_normPiece (res : List String) (abi : IsaAbi) (ps : List Piece)
    (hps : ∀ is, Piece.run is ∈ ps → ∀ i ∈ is, i.opn ≠ "MULX" ∧ i.wf = true)
    (acc : Lcmd × Std.HashSet String) :
    (ps.map normPiece).foldr (rstep res abi) (acc.1.map normI, acc.2)
      = ((ps.foldr (rstep res abi) acc).1.map normI, (ps.foldr (rstep res abi) acc).2) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons,
      ih fun is h => hps is (List.mem_cons_of_mem _ h)]
    exact rstep_normPiece res abi _
      (fun is h => by subst h; exact hps is List.mem_cons_self) _

/-- **The register re-allocation commutes with `normMulxBody`** at every register file and every
    alphabet that excludes both spellings of `MULX`. -/
theorem reallocBody_normMulxBody_of (res : List String) (abi : IsaAbi) {recog : String → Bool}
    (h1 : recog "MULX" = false) (h2 : recog "MULX:64" = false) (b : Lcmd) :
    reallocBody res (normMulxBody b) abi recog = normMulxBody (reallocBody res b abi recog) := by
  have hps : ∀ is, Piece.run is ∈ pieces b recog → ∀ i ∈ is, i.opn ≠ "MULX" ∧ i.wf = true := by
    intro is h i hi
    obtain ⟨hr, hw⟩ := pieces_runs b is h i hi
    exact ⟨fun he => by rw [he, h1] at hr; exact absurd hr (by decide), hw⟩
  have h := foldr_rstep_normPiece res abi (pieces b recog) hps ([], labelLiveFrames b)
  rw [normMulxBody_eq_map, normMulxBody_eq_map, reallocBody_eq, reallocBody_eq,
    pieces_map_normI h1 h2, labelLiveFrames_map_normI]
  exact congrArg Prod.fst h

/-- `MULX` is a prefix of itself. -/
theorem isPrefixOf_mulx : "MULX".isPrefixOf "MULX" = true := by
  grind only [X86Backend.LprogGpReallocCfg.isPrefixOf_list, = List.isPrefixOf_iff_prefix,
    ← List.prefix_rfl]

/-- The x86 alphabet excludes `MULX`. -/
theorem isRecognizedOpn_mulx : isRecognizedOpn "MULX" = false := by
  have h : stripAbiTag "MULX" = "MULX" := by decide +kernel
  exact X86Backend.LcmdCopyPropagate.isRecognizedOpn_eq_false_of_implicitReads
    (by simp [X86Backend.LcmdCopyPropagate.implicitReads, h, isPrefixOf_mulx])

/-- The x86 alphabet excludes `MULX:64`. -/
theorem isRecognizedOpn_mulx64 : isRecognizedOpn "MULX:64" = false := by
  have h : stripAbiTag "MULX:64" = "MULX" := by decide +kernel
  exact X86Backend.LcmdCopyPropagate.isRecognizedOpn_eq_false_of_implicitReads
    (by simp [X86Backend.LcmdCopyPropagate.implicitReads, h, isPrefixOf_mulx])

/-- **The register re-allocation of the owned back end commutes with `normMulxBody`**, at every
    register file and the x86 alphabet `isRecognizedOpn`. -/
theorem reallocBody_normMulxBody (res : List String) (abi : IsaAbi) (b : Lcmd) :
    reallocBody res (normMulxBody b) abi = normMulxBody (reallocBody res b abi) :=
  reallocBody_normMulxBody_of res abi isRecognizedOpn_mulx isRecognizedOpn_mulx64 b

/-! ## 2. The two-address legaliser -/

/-- An instruction set ties neither spelling of `MULX` and names no copy mnemonic `MULX`. -/
def MulxUntied (I : IsaData) : Prop :=
  (∀ b, I.tied "MULX" b = false) ∧ (∀ b, I.tied "MULX:64" b = false)
    ∧ ∀ o, I.copyMnemonic o ≠ some "MULX"

/-- The x86 instruction-set data ties neither spelling of `MULX` and names no copy mnemonic
    `MULX`. -/
theorem mulxUntied_x86Data : MulxUntied x86Data := by
  refine ⟨fun b => ?_, fun b => ?_, fun o => ?_⟩
  · simp [X86Backend.TwoAddrLegalize.needsTie, X86Backend.TwoAddrLegalize.tieBase,
      X86Backend.TwoAddrLegalize.tiedBases]
  · simp [X86Backend.TwoAddrLegalize.needsTie, X86Backend.TwoAddrLegalize.tieBase,
      X86Backend.TwoAddrLegalize.tiedBases]
  · have key : ∀ s : String, "MOV^" ++ s ≠ "MULX" := by
      intro s h
      have := congrArg String.toList h
      simp at this
    change X86Backend.TwoAddrLegalize.movFor o ≠ some "MULX"
    unfold X86Backend.TwoAddrLegalize.movFor withWidthTag
    grind

/-- The width reading keeps the scratch-register test of an instruction. -/
theorem instrAvoids_normMulx (r : LinstrR) (I : IsaData) :
    instrAvoids (normMulx r) I = instrAvoids r I := by
  cases r <;> simp [normMulx, instrAvoids]

/-- The width reading keeps the scratch-register test of a body. -/
theorem bodyAvoids_map_normI (b : Lcmd) (I : IsaData) :
    bodyAvoids (b.map normI) I = bodyAvoids b I := by
  simp [bodyAvoids, List.all_map, Function.comp_def, normI, instrAvoids_normMulx]

/-- The legalisation of an instruction without `MULX` emits no `MULX`. -/
theorem legalizeInstr_mnem {I : IsaData} (hI : MulxUntied I) (ok : Bool) {i : Linstr}
    (hi : instrMnem i ≠ some "MULX") :
    ∀ j ∈ legalizeInstr ok i I, instrMnem j ≠ some "MULX" := by
  obtain ⟨-, -, hc⟩ := hI
  intro j hj
  unfold legalizeInstr scratchRoute at hj
  split at hj <;> (repeat' split at hj) <;> grind [instrMnem]

/-- The legalisation of one instruction commutes with the width reading. -/
theorem legalizeInstr_normI {I : IsaData} (hI : MulxUntied I) (ok : Bool) (i : Linstr) :
    legalizeInstr ok (normI i) I = (legalizeInstr ok i I).map normI := by
  by_cases hm : instrMnem i = some "MULX"
  · obtain ⟨h1, h2, -⟩ := hI
    rcases i with ⟨ii, r⟩
    cases r <;> simp only [instrMnem, Option.some.injEq, reduceCtorEq] at hm
    subst hm
    simp only [normI, normMulx, ite_true, withWidthTag_mulx]
    unfold legalizeInstr
    split <;> simp_all [normI, normMulx, withWidthTag_mulx]
  · rw [normI_of_mnem i hm]
    exact ((List.map_congr_left fun j hj => normI_of_mnem j
      (legalizeInstr_mnem hI ok hm j hj)).trans (List.map_id _)).symm

/-- **The two-address legaliser commutes with `normMulxBody`** at every instruction set that ties
    neither spelling of `MULX` and names no copy mnemonic `MULX`. -/
theorem twoAddrBody_normMulxBody {I : IsaData} (hI : MulxUntied I) (b : Lcmd) :
    twoAddrBody (normMulxBody b) I = normMulxBody (twoAddrBody b I) := by
  simp only [normMulxBody_eq_map, twoAddrBody, bodyAvoids_map_normI,
    X86Backend.LegalizeShiftImm.legalizeBody, List.flatMap_map, legalizeInstr_normI hI,
    List.map_flatMap]

/-! ## 3. The compare reload -/

/-- A compare on a spilled first operand has a mnemonic of base `CMP`. -/
theorem spillCmp?_cmp {w : LinstrR} {abi : IsaAbi} {opn d : String} {s : LOperand}
    (h : spillCmp? w abi = some (opn, d, s)) : stripWidthTag opn = "CMP" := by
  unfold spillCmp? at h
  split at h
  · split at h <;> grind
  · simp at h

/-- The reload of one instruction commutes with the width reading. -/
theorem cmpReloadI_normI (abi : IsaAbi) (i : Linstr) :
    cmpReloadI (normI i) abi = (cmpReloadI i abi).map normI := by
  by_cases hm : instrMnem i = some "MULX"
  · rcases i with ⟨ii, r⟩
    cases r <;> simp only [instrMnem, Option.some.injEq, reduceCtorEq] at hm
    subst hm
    rename_i ds ss
    have hn : ∀ o, stripWidthTag o = "MULX" → spillCmp? (.Lopn ds o ss) abi = none := by
      intro o ho
      unfold spillCmp?
      split <;> simp_all
    simp only [normI, normMulx, ite_true, cmpReloadI, hn _ stripWidthTag_mulx,
      hn _ stripWidthTag_mulx64, List.map_cons, List.map_nil]
  · rw [normI_of_mnem i hm]
    refine ((List.map_congr_left fun j hj => normI_of_mnem j ?_).trans (List.map_id _)).symm
    unfold cmpReloadI at hj
    split at hj
    · rename_i opn d s hs
      have hc := spillCmp?_cmp hs
      have hne : opn ≠ "MULX" := fun h => by
        rw [h, stripWidthTag_mulx] at hc
        exact absurd hc (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · simp only [instrMnem, movOf, ne_eq, Option.some.injEq]
        split <;> decide
      · simpa only [instrMnem, ne_eq, Option.some.injEq] using hne
    · rw [List.mem_singleton] at hj
      subst hj
      exact hm

/-- **The compare reload commutes with `normMulxBody`** at every register file. -/
theorem cmpReload_normMulxBody (abi : IsaAbi) (b : Lcmd) :
    cmpReload (normMulxBody b) abi = normMulxBody (cmpReload b abi) := by
  simp only [normMulxBody_eq_map, cmpReload, List.flatMap_map, cmpReloadI_normI, List.map_flatMap]

/-! ## 4. The printed program -/

/-- **The printed program of the back half commutes with `normMulxBody` on every function
    body**, at an instruction set that ties neither spelling of `MULX` and names no copy
    mnemonic `MULX`, when the optimised body `b` of every function satisfies the hypotheses of
    `NormMulxFold.foldIndexedBody_normMulxBody`: every `MULX` of `b` has two register destinations
    and one source, `b` has the width class `64`, and its dead-move core after the fold keeps
    the width class `64`. -/
theorem printedLprog_mapBodies_normMulxBody (P : Lprog) {I : IsaData} (hI : MulxUntied I)
    (hP : ∀ nf ∈ P.lp_funcs,
      MulxShaped (optimizeBasicBlocks nf.2.lfd_body) = true
        ∧ bodyIsU64 (optimizeBasicBlocks nf.2.lfd_body) = true
        ∧ bodyIsU64 (dropDeadCore (bodyParams (optimizeBasicBlocks nf.2.lfd_body))
            (constIndexFoldBody (optimizeBasicBlocks nf.2.lfd_body))) = true) :
    printedLprog (mapBodies normMulxBody P) I = mapBodies normMulxBody (printedLprog P I) := by
  unfold printedLprog ownedLprog X86Backend.LprogOptPipeline.optimizeLprogBasicBlocks
    X86Backend.ConstIndexFold.foldIndexedLprog reallocLprog mapBodies
  simp only [List.map_map, Lprog.mk.injEq, true_and]
  refine List.map_congr_left fun nf hnf => ?_
  obtain ⟨hs, hb, hd⟩ := hP nf hnf
  simp only [Function.comp_apply, optimizeBasicBlocks_normMulxBody,
    foldIndexedBody_normMulxBody _ hs hb hd, reallocBody_normMulxBody, twoAddrBody_normMulxBody hI,
    cmpReload_normMulxBody]

end CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxTail
