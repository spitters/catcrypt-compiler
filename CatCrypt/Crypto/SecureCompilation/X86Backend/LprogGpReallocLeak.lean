/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak

/-!
# The register re-allocation preserves constant time along the executed trace

`LprogGpRealloc.reallocLprog` re-allocates each maximal run of fragment
instructions of a function body and keeps every other instruction. This module
proves that it preserves constant time from function entry (`LprogLeak.EntryCT`)
for every leakage model `LprogLeak.LeakFn`, over the labelled semantics
(`findInstr`, `evalInstrP`), on bodies with labels, jumps and conditional
branches.

## The simulation

The source body is the concatenation of its pieces (`pieces_flatten`) and the
re-allocated body is the concatenation of their images (`reallocBody_eq`): a
kept instruction for an instruction outside the fragment, the re-allocated run
for a run. A run emits no events in either program. A source state at the start
of piece `j` is related to a target state at the start of the image of piece
`j` when the two agree on memory and on every name `Need j` names: every name
that is not a location, the general-purpose registers unless piece `j` is a
return, and the frame cells live at `j` (`labelLiveFrames` and the frame cells
named from piece `j` on). Across a run, the check's soundness `goAcc_sound`
(or the liveness of the unchanged run) re-establishes the relation at the next
piece; across a kept instruction, the two states read the same values, emit the
same events and step to related states; a jump reaches a label that is a kept
instruction at the same piece index in both bodies.

Constant time transfers because two source runs with equal leakage for every
fuel stay at the same program counter and emit the same events step by step
(`LprogLeak.lprogLeak_split`), and a target run moves through the same pieces
as the source run it is related to.

## Hypotheses (`ReallocOk`)

* every fragment instruction of the body steps from every state (an `Lopn`
  whose mnemonic the semantics interprets at its arity);
* every `Lgoto` targets the function it is in;
* no result register of the function is a frame cell.

## Main results

* `reallocRun_rel`: the pass on one run is sound from every state related to
  the source state on the names live at the start of the run.
* `reallocLprog_entryCT`: `EntryCT L P pub → EntryCT L (reallocLprog P) pub`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCT (fragOf?_wf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP physGPs nameReads)

/-! ## 1. Pieces -/

/-- The instructions a piece stands for. -/
def Piece.toLcmd : Piece → Lcmd
  | .run is => is.map FI.toL
  | .bar li => [li]

/-- Whether a piece is a run. -/
def Piece.isRun : Piece → Bool
  | .run _ => true
  | .bar _ => false

theorem fragOf?_toL {li : Linstr} {i : FI} (h : fragOf? li = some i) : i.toL = li := by
  obtain ⟨ii, ir⟩ := li
  unfold fragOf? at h
  simp only at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

theorem pieces_cons (li : Linstr) (rest : Lcmd) :
    pieces (li :: rest) =
      (match fragOf? li with
        | some i =>
            match pieces rest with
            | Piece.run is :: tl => Piece.run (i :: is) :: tl
            | _ => Piece.run [i] :: pieces rest
        | none => Piece.bar li :: pieces rest) := rfl

/-- The pieces of a body concatenate to the body. -/
theorem pieces_flatten (body : Lcmd) : ((pieces body).map Piece.toLcmd).flatten = body := by
  induction body with
  | nil => rfl
  | cons li rest ih =>
      rw [pieces_cons]
      cases hf : fragOf? li with
      | none => simp [Piece.toLcmd, ih]
      | some i =>
          have hi := fragOf?_toL hf
          dsimp only
          revert ih
          cases pieces rest with
          | nil => intro ih; simp [Piece.toLcmd, hi, ← ih]
          | cons p tl =>
              cases p with
              | run is => intro ih; simp [Piece.toLcmd, hi, ← ih]
              | bar l => intro ih; simp [Piece.toLcmd, hi, ← ih]

/-- A well-formed piece: a run is a non-empty list of fragment instructions, a
    kept instruction is outside the fragment. -/
def Piece.Good : Piece → Prop
  | .run is => is ≠ [] ∧ ∀ i ∈ is, fragOf? i.toL = some i
  | .bar li => fragOf? li = none

theorem pieces_good (body : Lcmd) : ∀ p ∈ pieces body, Piece.Good p := by
  induction body with
  | nil => intro p hp; simp [pieces] at hp
  | cons li rest ih =>
      intro p hp
      rw [pieces_cons] at hp
      cases hf : fragOf? li with
      | none =>
          rw [hf] at hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact hf
          · exact ih p hp
      | some i =>
          rw [hf] at hp
          have hi : fragOf? i.toL = some i := by rw [fragOf?_toL hf]; exact hf
          dsimp only at hp
          revert ih hp
          cases pieces rest with
          | nil =>
              intro _ hp
              rw [List.mem_singleton] at hp
              subst hp
              exact ⟨by simp, by simpa using hi⟩
          | cons q tl =>
              cases q with
              | run is =>
                  intro ih hp
                  rcases List.mem_cons.1 hp with rfl | hp
                  · obtain ⟨_, his⟩ := ih (.run is) (List.mem_cons_self ..)
                    refine ⟨by simp, fun j hj => ?_⟩
                    rcases List.mem_cons.1 hj with rfl | hj
                    · exact hi
                    · exact his j hj
                  · exact ih p (List.mem_cons_of_mem _ hp)
              | bar l =>
                  intro ih hp
                  rcases List.mem_cons.1 hp with rfl | hp
                  · exact ⟨by simp, by simpa using hi⟩
                  · exact ih p hp

/-- No two runs are adjacent. -/
def noAdjRuns : List Piece → Bool
  | [] => true
  | .bar _ :: rest => noAdjRuns rest
  | .run _ :: rest => (match rest with | .run _ :: _ => false | _ => true) && noAdjRuns rest

theorem pieces_noAdjRuns (body : Lcmd) : noAdjRuns (pieces body) = true := by
  induction body with
  | nil => rfl
  | cons li rest ih =>
      rw [pieces_cons]
      cases hf : fragOf? li with
      | none => exact ih
      | some i =>
          dsimp only
          revert ih
          cases pieces rest with
          | nil => intro _; rfl
          | cons p tl =>
              cases p with
              | run is => intro ih; exact ih
              | bar l => intro ih; simpa [noAdjRuns] using ih

theorem noAdjRuns_getElem : ∀ (l : List Piece), noAdjRuns l = true →
    ∀ (j : Nat) (is : List FI), l[j]? = some (.run is) →
      ∀ p, l[j + 1]? = some p → Piece.isRun p = false := by
  intro l
  induction l with
  | nil => intro _ j is h; simp at h
  | cons a l ih =>
      intro hl j is hj p hp
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          cases l with
          | nil => simp at hp
          | cons b tl =>
              simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
                Option.some.injEq] at hp
              subst hp
              cases b with
              | run _ => simp [noAdjRuns] at hl
              | bar _ => rfl
      | succ j =>
          have hl' : noAdjRuns l = true := by
            cases a with
            | bar _ => exact hl
            | run _ =>
                simp only [noAdjRuns, Bool.and_eq_true] at hl
                exact hl.2
          exact ih hl' j is (by simpa using hj) p (by simpa using hp)

theorem flatMap_frames_eq (ps : List Piece) :
    ps.flatMap Piece.frames =
      (ps.map Piece.toLcmd).flatten.flatMap (fun li => instrFrames li.li_i) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [List.flatMap_cons, ih, List.map_cons, List.flatten_cons, List.flatMap_append]
      congr 1
      cases p with
      | run is =>
          simp only [Piece.frames, Piece.toLcmd, List.flatMap_map]
          rfl
      | bar li => simp [Piece.frames, Piece.toLcmd]

/-- The frame cells the pieces name are the frame cells the body names. -/
theorem pieces_frames (body : Lcmd) :
    (pieces body).flatMap Piece.frames = body.flatMap (fun li => instrFrames li.li_i) := by
  rw [flatMap_frames_eq, pieces_flatten]

/-! ## 2. The re-allocated body as a concatenation -/

/-- The registers live after a run followed by `l`. -/
def regsAfter (res : List String) (l : Lcmd) : List String :=
  match l with
  | ⟨_, .Lret⟩ :: _ => retLive res
  | _ => physGPs

/-- The image of a piece, given the output and the frame set after it. -/
def outSeg (res : List String) (p : Piece) (acc : Lcmd × Std.HashSet String) : Lcmd :=
  match p with
  | .run is => (reallocRun (regsAfter res acc.1 ++ acc.2.toList) is).map FI.toL
  | .bar li => [li]

/-- The step of the fold `reallocBody` computes. -/
def stepF (res : List String) (p : Piece) (acc : Lcmd × Std.HashSet String) :
    Lcmd × Std.HashSet String :=
  (outSeg res p acc ++ acc.1, acc.2.insertMany p.frames)

/-- The images of the pieces. -/
def outSegs (res : List String) (lf : Std.HashSet String) : List Piece → List Lcmd
  | [] => []
  | p :: ps => outSeg res p (ps.foldr (stepF res) ([], lf)) :: outSegs res lf ps

theorem outSegs_length (res : List String) (lf : Std.HashSet String) :
    ∀ ps : List Piece, (outSegs res lf ps).length = ps.length := by
  intro ps; induction ps with
  | nil => rfl
  | cons p ps ih => simp [outSegs, ih]

theorem foldr_stepF_fst (res : List String) (lf : Std.HashSet String) :
    ∀ ps : List Piece, (ps.foldr (stepF res) ([], lf)).1 = (outSegs res lf ps).flatten := by
  intro ps; induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.foldr_cons, stepF, outSegs, List.flatten_cons, ih]

theorem mem_foldr_stepF_snd (res : List String) (lf : Std.HashSet String) (x : String) :
    ∀ ps : List Piece, x ∈ (ps.foldr (stepF res) ([], lf)).2 ↔
      x ∈ lf ∨ x ∈ ps.flatMap Piece.frames := by
  intro ps; induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.foldr_cons, stepF, Std.HashSet.mem_insertMany_list, ih,
        List.contains_iff_mem, List.flatMap_cons, List.mem_append]
      tauto

theorem outSegs_getElem (res : List String) (lf : Std.HashSet String) :
    ∀ (ps : List Piece) (j : Nat) (hj : j < ps.length),
      (outSegs res lf ps)[j]'(by rw [outSegs_length]; exact hj) =
        outSeg res ps[j] ((ps.drop (j + 1)).foldr (stepF res) ([], lf)) := by
  intro ps
  induction ps with
  | nil => intro j hj; simp at hj
  | cons p ps ih =>
      intro j hj
      cases j with
      | zero => rfl
      | succ j => simpa [outSegs] using ih j (by simpa using hj)

/-- **The re-allocated body is the concatenation of the images of the pieces.** -/
theorem reallocBody_eq (res : List String) (body : Lcmd) :
    reallocBody res body = (outSegs res (labelLiveFrames body) (pieces body)).flatten := by
  rw [← foldr_stepF_fst]
  unfold reallocBody
  dsimp only
  congr 1
  congr 1
  funext p acc
  cases p <;> rfl

/-! ## 3. Positions in a concatenation -/

/-- The position of the start of segment `k`. -/
def bdry (segs : List Lcmd) (k : Nat) : Nat := ((segs.take k).flatten).length

@[simp] theorem bdry_zero (segs : List Lcmd) : bdry segs 0 = 0 := by simp [bdry]

theorem bdry_cons_succ (a : Lcmd) (segs : List Lcmd) (k : Nat) :
    bdry (a :: segs) (k + 1) = a.length + bdry segs k := by
  simp [bdry]

theorem bdry_succ (segs : List Lcmd) (k : Nat) (hk : k < segs.length) :
    bdry segs (k + 1) = bdry segs k + segs[k].length := by
  unfold bdry
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.flatten_append,
    List.length_append]
  simp

theorem bdry_length (segs : List Lcmd) : bdry segs segs.length = segs.flatten.length := by
  simp [bdry]

theorem flatten_split (segs : List Lcmd) (k : Nat) (hk : k < segs.length) :
    segs.flatten = (segs.take k).flatten ++ (segs[k] ++ (segs.drop (k + 1)).flatten) := by
  conv_lhs => rw [← List.take_append_drop k segs, List.drop_eq_getElem_cons hk]
  rw [List.flatten_append, List.flatten_cons]

/-- The instruction at offset `o` of segment `k`. -/
theorem seg_fetch (segs : List Lcmd) (k : Nat) (hk : k < segs.length) (o : Nat)
    (ho : o < segs[k].length) :
    (segs.flatten.map Linstr.li_i)[bdry segs k + o]? = some (segs[k][o]).li_i := by
  rw [List.getElem?_map, flatten_split segs k hk, bdry,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left ho, List.getElem?_eq_getElem ho]
  rfl

/-! ## 4. Labels -/

/-- Segments related for label resolution: equal single instructions, or two
    segments without a label. -/
def SegRel (a b : Lcmd) : Prop :=
  (a = b ∧ a.length = 1) ∨
    ((∀ lbl, ∀ x ∈ a, isLabel lbl x.li_i = false) ∧ (∀ lbl, ∀ x ∈ b, isLabel lbl x.li_i = false))

theorem SegRel.symm {a b : Lcmd} (h : SegRel a b) : SegRel b a := by
  rcases h with ⟨rfl, h⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨hb, ha⟩

/-- **Label resolution through related segments.** A label found in the
    concatenation of `A` is the single instruction of a segment `k`, and the
    concatenation of `B` resolves it to the start of its segment `k`. -/
theorem findLabel_segs (lbl : LLabel) :
    ∀ (A B : List Lcmd), List.Forall₂ SegRel A B →
      ∀ pc, findLabel lbl (A.flatten.map Linstr.li_i) = some pc →
        ∃ k, k < A.length ∧ pc = bdry A k ∧
          findLabel lbl (B.flatten.map Linstr.li_i) = some (bdry B k) ∧
          bdry A (k + 1) = bdry A k + 1 ∧ bdry B (k + 1) = bdry B k + 1 := by
  intro A B h
  induction h with
  | nil => intro pc hpc; simp [findLabel] at hpc
  | @cons a b A B hab _ ih =>
      intro pc hpc
      simp only [findLabel, List.flatten_cons, List.map_append, List.findIdx?_append] at hpc ⊢
      rcases hab with ⟨rfl, hlen⟩ | ⟨ha, hb⟩
      · obtain ⟨x, rfl⟩ : ∃ x, a = [x] := by
          match a, hlen with
          | [x], _ => exact ⟨x, rfl⟩
        by_cases hx : isLabel lbl x.li_i = true
        · simp only [List.map_cons, List.map_nil, List.findIdx?_singleton, hx, ite_true,
            Option.some_or, Option.some.injEq] at hpc ⊢
          subst hpc
          exact ⟨0, by simp, by simp, by simp, by simp [bdry_cons_succ], by simp [bdry_cons_succ]⟩
        · simp only [Bool.not_eq_true] at hx
          simp only [List.map_cons, List.map_nil, List.findIdx?_singleton, hx,
            Bool.false_eq_true, ite_false, Option.none_or, List.length_singleton] at hpc ⊢
          obtain ⟨pc', hpc', rfl⟩ := Option.map_eq_some_iff.1 hpc
          obtain ⟨k, hk, rfl, hB, hA1, hB1⟩ := ih pc' hpc'
          simp only [findLabel] at hB
          refine ⟨k + 1, by simpa using hk, by simp [bdry_cons_succ]; omega, ?_, ?_, ?_⟩
          · rw [hB]; simp [bdry_cons_succ]; omega
          · simp only [bdry_cons_succ, List.length_singleton, hA1]; omega
          · simp only [bdry_cons_succ, List.length_singleton, hB1]; omega
      · have hna : (a.map Linstr.li_i).findIdx? (isLabel lbl) = none :=
          List.findIdx?_eq_none_iff.2 (by simpa using ha lbl)
        have hnb : (b.map Linstr.li_i).findIdx? (isLabel lbl) = none :=
          List.findIdx?_eq_none_iff.2 (by simpa using hb lbl)
        rw [hna, Option.none_or] at hpc
        rw [hnb, Option.none_or]
        obtain ⟨pc', hpc', rfl⟩ := Option.map_eq_some_iff.1 hpc
        obtain ⟨k, hk, rfl, hB, hA1, hB1⟩ := ih pc' hpc'
        simp only [findLabel] at hB
        refine ⟨k + 1, by simpa using hk, by simp [bdry_cons_succ]; omega, ?_, ?_, ?_⟩
        · rw [hB]; simp [bdry_cons_succ]; omega
        · simp only [bdry_cons_succ, hA1]; omega
        · simp only [bdry_cons_succ, hB1]; omega

/-! ## 5. One run from a related state -/

theorem renOp_empty (o : LOperand) : renOp ({} : Cur) o = o := by
  cases o with
  | reg n => simp only [renOp, look_empty]; split <;> rfl
  | _ => rfl

/-- **The unchanged run from a related state.** A run started from a state that
    agrees with the source state on memory, on every name that is not a location
    and on every location live at the start ends in a state that agrees with the
    source run's final state on memory, on every name that is not a location and
    on every live-out name. -/
theorem runWith_rel_id {w : Nat} (sem : String → List (BitVec w) → Option (BitVec w))
    (lend : List String) :
    ∀ (is : List FI) (σ σ' τ : Lstate w), (∀ i ∈ is, i.wf = true) →
      Rel {} (annotate lend is).2 σ τ → runWith sem is σ = some σ' →
      ∃ τ', runWith sem is τ = some τ' ∧ Final lend σ' τ' := by
  intro is
  induction is with
  | nil =>
      intro σ σ' τ _ hR h
      simp only [runWith, Option.some.injEq] at h
      subst h
      refine ⟨τ, rfl, hR.1, fun x hx => ?_⟩
      by_cases hl : isLoc x = true
      · rcases hx with hx | hx
        · rw [hl] at hx; cases hx
        · have := (hR.2.2 x hx hl).2
          rwa [look_empty] at this
      · exact hR.2.1 x (by simpa using hl)
  | cons i is ih =>
      intro σ σ' τ hwf hR h
      rw [annotate_cons] at hR
      have hwi := hwf i (List.mem_cons_self ..)
      have hev := map_eval_renOp (m := {}) hR (fun n hn => reads_mem_liveBefore hn)
        (wf_of_srcs hwi)
      have hid : i.srcs.map (fun o => renOp ({} : Cur) o) = i.srcs := by
        conv_rhs => rw [← List.map_id i.srcs]
        exact List.map_congr_left (fun o _ => renOp_empty o)
      rw [hid] at hev
      simp only [runWith, stepWith] at h ⊢
      rw [hev]
      cases hv : sem i.opn (i.srcs.map (evalOperand σ)) with
      | none => rw [hv] at h; cases h
      | some v =>
          rw [hv] at h
          refine ih _ _ _ (fun j hj => hwf j (List.mem_cons_of_mem _ hj)) ?_ h
          refine ⟨hR.1, fun x hx => ?_, fun n hn hl => ?_⟩
          · simp only [Lstate.nextPc, Lstate.lvm_setReg]
            split
            · rfl
            · exact hR.2.1 x hx
          · rw [look_empty]
            refine ⟨hl, ?_⟩
            simp only [Lstate.nextPc, Lstate.lvm_setReg]
            split
            · rfl
            · rename_i hne
              have := (hR.2.2 n (mem_liveBefore hn hne) hl).2
              rwa [look_empty] at this

/-- **The pass on one run from a related state.** From a state related to the
    source state on the names live at the start of the run, the re-allocated run
    ends in a state that agrees with the source run's final state on memory, on
    every name that is not a location and on every live-out name; every
    instruction of the re-allocated run is in the fragment. -/
theorem reallocRun_rel {w : Nat} (lend : List String) (is : List FI)
    (hwf : ∀ i ∈ is, i.wf = true) (σ σ' τ : Lstate w) (hR : Rel {} (annotate lend is).2 σ τ)
    (h : runWith semL is σ = some σ') :
    (∀ j ∈ reallocRun lend is, j.wf = true) ∧
      ∃ τ', runWith semL (reallocRun lend is) τ = some τ' ∧ Final lend σ' τ' := by
  unfold reallocRun reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨rest, τ', hout, hwr, hr, hfin⟩ :=
      goAcc_sound semL (fun opn a hc => semL_copy opn a hc) lend is {} cs [] out σ σ' τ hwf
        hcs hR h
    simp only [List.reverse_nil, List.nil_append] at hout
    subst hout
    exact ⟨hwr, τ', hr, hfin⟩
  · exact ⟨hwf, runWith_rel_id semL lend is σ σ' τ hwf hR h⟩

/-! ## 6. Liveness facts -/

theorem isPhysGP_of_loc {x : String} (hl : isLoc x = true) (hf : isFrame x = false) :
    isPhysGP x = true := by
  simp only [isLoc_x86, isFrame, Bool.or_eq_true] at hl hf
  rcases hl with hl | hl
  · exact hl
  · rw [hl] at hf; cases hf

theorem baseRegs_gp {n x : String} (h : x ∈ baseRegs n) : isPhysGP x = true := by
  rw [baseRegs_x86] at h
  unfold nameReads at h
  split_ifs at h with h1 h2
  · simp only [List.mem_singleton] at h; subst h; exact h2
  · split at h
    · split_ifs at h with h4
      · simp only [List.mem_singleton] at h; subst h; exact h4
      · simp at h
    · simp at h
  · simp at h

theorem mem_annotate_snd (lend : List String) :
    ∀ (is : List FI) (n : String), n ∈ (annotate lend is).2 →
      n ∈ lend ∨ ∃ i ∈ is, n ∈ i.reads := by
  intro is
  induction is with
  | nil => intro n h; exact Or.inl h
  | cons i is ih =>
      intro n h
      rw [annotate_cons] at h
      rcases (mem_addNew _ _ _).1 h with h | h
      · exact Or.inr ⟨i, List.mem_cons_self .., h⟩
      · rcases ih n (List.mem_filter.1 h).1 with h | ⟨j, hj, hn⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hn⟩

/-- A location an instruction of the fragment reads is a general-purpose register or
    a frame cell the instruction names. -/
theorem reads_need {i : FI} {n : String} (h : n ∈ i.reads) (hl : isLoc n = true) :
    isPhysGP n = true ∨ n ∈ instrFrames i.toR := by
  simp only [FI.reads, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨o, ho, hn⟩ | h
  · cases o with
    | reg m =>
        simp only [opReads] at hn
        split at hn
        · simp only [List.mem_singleton] at hn
          subst hn
          by_cases hf : isFrame n = true
          · right
            simp only [FI.toR, instrFrames, List.mem_append, List.mem_flatMap]
            exact Or.inr ⟨.reg n, ho, by simp [opFrames, hf]⟩
          · exact Or.inl (isPhysGP_of_loc hl (by simpa using hf))
        · exact Or.inl (baseRegs_gp hn)
    | _ => simp [opReads] at hn
  · exact Or.inl (baseRegs_gp h)

theorem isPhysGP_mem_physGPs {x : String} (h : isPhysGP x = true) : x ∈ physGPs := by
  simpa [isPhysGP] using h

theorem retLive_gp (res : List String) (hres : ∀ x ∈ res, isFrame x = false) {x : String}
    (hx : x ∈ retLive res) (hl : isLoc x = true) : isPhysGP x = true := by
  simp only [retLive_x86, List.mem_append, List.mem_filter] at hx
  rcases hx with hx | ⟨hx, _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [isPhysGP, physGPs]
  · exact isPhysGP_of_loc hl (hres x hx)

theorem regsAfter_gp (res : List String) (hres : ∀ x ∈ res, isFrame x = false) (l : Lcmd)
    {x : String} (hx : x ∈ regsAfter res l) (hl : isLoc x = true) : isPhysGP x = true := by
  unfold regsAfter at hx
  split at hx
  · exact retLive_gp res hres hx hl
  · simpa [isPhysGP] using hx

/-- The frame cells named after a label-bearing body's every point: all of them. -/
theorem mem_labelLiveFrames {body : Lcmd} (hlab : ∃ li ∈ body, ∃ k l, li.li_i = .Llabel k l)
    {x : String} (hx : x ∈ body.flatMap (fun li => instrFrames li.li_i)) :
    x ∈ labelLiveFrames body := by
  obtain ⟨li, hli, k, l, hk⟩ := hlab
  unfold labelLiveFrames
  rw [ite_eq_left (List.any_eq_true.2 ⟨li, hli, by simp [hk]⟩), Std.HashSet.mem_insertMany_list]
  exact Or.inr (List.contains_iff_mem.2 hx)

/-! ## 7. The relation at piece boundaries -/

/-- The piece at `j` is a return. -/
def RetAt (ps : List Piece) (j : Nat) : Prop := ∃ ii, ps[j]? = some (.bar ⟨ii, .Lret⟩)

/-- The names on which a source state and a target state at piece `j` agree:
    every name that is not a location, the general-purpose registers unless piece
    `j` is a return, and the frame cells in `lf` or named from piece `j` on. -/
def Need (ps : List Piece) (lf : Std.HashSet String) (j : Nat) (x : String) : Prop :=
  isLoc x = false ∨ (isPhysGP x = true ∧ ¬ RetAt ps j) ∨ x ∈ lf ∨
    x ∈ (ps.drop j).flatMap Piece.frames

/-- Agreement at piece `j`: equal memory and equal values on `Need j`. -/
def Inv {w : Nat} (ps : List Piece) (lf : Std.HashSet String) (j : Nat) (σ τ : Lstate w) :
    Prop :=
  τ.lmem = σ.lmem ∧ ∀ x, Need ps lf j x → τ.lvm x = σ.lvm x

theorem mem_flatMap_drop {f : Piece → List String} {ps : List Piece} {j j' : Nat}
    (hj : j ≤ j') {x : String} (h : x ∈ (ps.drop j').flatMap f) : x ∈ (ps.drop j).flatMap f := by
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 h
  refine List.mem_flatMap.2 ⟨p, ?_, hx⟩
  have : ps.drop j' = (ps.drop j).drop (j' - j) := by rw [List.drop_drop]; congr 1; omega
  rw [this] at hp
  exact List.mem_of_mem_drop hp

theorem Need_mono {ps : List Piece} {lf : Std.HashSet String} {j j' : Nat} (hj : j ≤ j')
    (hr : ¬ RetAt ps j) {x : String} (h : Need ps lf j' x) : Need ps lf j x := by
  rcases h with h | ⟨h, _⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, hr⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (mem_flatMap_drop hj h)))

theorem Need_of_allFrames {ps : List Piece} {lf : Std.HashSet String}
    (hall : ∀ x ∈ ps.flatMap Piece.frames, x ∈ lf) {j j' : Nat}
    (hr : ¬ RetAt ps j) {x : String} (h : Need ps lf j' x) : Need ps lf j x := by
  rcases h with h | ⟨h, _⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, hr⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl (hall x (mem_flatMap_drop (Nat.zero_le _) h))))

theorem drop_eq_cons {ps : List Piece} {j : Nat} {p : Piece} (h : ps[j]? = some p) :
    ps.drop j = p :: ps.drop (j + 1) := by
  have hj : j < ps.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.drop_eq_getElem_cons hj, List.getElem?_eq_getElem hj] at *
  simp only [Option.some.injEq] at h
  rw [h]

theorem not_retAt_run {ps : List Piece} {j : Nat} {is : List FI}
    (h : ps[j]? = some (.run is)) : ¬ RetAt ps j := by
  rintro ⟨ii, hr⟩
  rw [h] at hr
  cases hr

theorem not_retAt_bar {ps : List Piece} {j : Nat} {li : Linstr}
    (h : ps[j]? = some (.bar li)) (hli : li.li_i ≠ .Lret) : ¬ RetAt ps j := by
  rintro ⟨ii, hr⟩
  rw [h] at hr
  simp only [Option.some.injEq, Piece.bar.injEq] at hr
  exact hli (by rw [hr])

/-- The live-out set of the run at piece `j`. -/
def lendAt (res : List String) (lf : Std.HashSet String) (ps : List Piece) (j : Nat) :
    List String :=
  regsAfter res (outSegs res lf (ps.drop (j + 1))).flatten ++
    ((ps.drop (j + 1)).foldr (stepF res) ([], lf)).2.toList

theorem outSeg_run_eq (res : List String) (lf : Std.HashSet String) (ps : List Piece) (j : Nat)
    (is : List FI) :
    outSeg res (.run is) ((ps.drop (j + 1)).foldr (stepF res) ([], lf)) =
      (reallocRun (lendAt res lf ps j) is).map FI.toL := by
  simp only [outSeg, lendAt, foldr_stepF_fst]

/-- **Agreement at the start of a run gives the check's relation.** -/
theorem inv_run_rel {w : Nat} (res : List String) (hres : ∀ x ∈ res, isFrame x = false)
    (lf : Std.HashSet String) (ps : List Piece) (j : Nat) (is : List FI)
    (hj : ps[j]? = some (.run is)) (σ τ : Lstate w) (hI : Inv ps lf j σ τ) :
    Rel {} (annotate (lendAt res lf ps j) is).2 σ τ := by
  refine ⟨hI.1, fun x hx => hI.2 x (Or.inl hx), fun n hn hl => ?_⟩
  rw [look_empty]
  refine ⟨hl, hI.2 n ?_⟩
  have hrun := not_retAt_run hj
  rcases mem_annotate_snd _ is n hn with hn | ⟨i, hi, hn⟩
  · simp only [lendAt, List.mem_append] at hn
    rcases hn with hn | hn
    · exact Or.inr (Or.inl ⟨regsAfter_gp res hres _ hn hl, hrun⟩)
    · rw [Std.HashSet.mem_toList, mem_foldr_stepF_snd] at hn
      rcases hn with hn | hn
      · exact Or.inr (Or.inr (Or.inl hn))
      · exact Or.inr (Or.inr (Or.inr (mem_flatMap_drop (Nat.le_succ j) hn)))
  · rcases reads_need hn hl with hg | hf
    · exact Or.inr (Or.inl ⟨hg, hrun⟩)
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [drop_eq_cons hj, List.flatMap_cons, List.mem_append]
      left
      simp only [Piece.frames, List.mem_flatMap]
      exact ⟨i, hi, hf⟩

/-- **The check's final relation gives agreement at the next piece.** -/
theorem final_inv {w : Nat} (res : List String) (lf : Std.HashSet String) (ps : List Piece)
    (hadj : noAdjRuns ps = true) (j : Nat) (is : List FI) (hj : ps[j]? = some (.run is))
    (σ τ : Lstate w) (hF : Final (lendAt res lf ps j) σ τ) : Inv ps lf (j + 1) σ τ := by
  refine ⟨hF.1, fun x hx => hF.2 x ?_⟩
  rcases hx with hx | ⟨hg, hr⟩ | hx | hx
  · exact Or.inl hx
  · right
    simp only [lendAt, List.mem_append]
    left
    have hregs : regsAfter res (outSegs res lf (ps.drop (j + 1))).flatten = physGPs := by
      cases hp : ps[j + 1]? with
      | none =>
          rw [List.drop_eq_nil_of_le (by
            by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hp; cases hp)]
          rfl
      | some p =>
          have hnr := noAdjRuns_getElem ps hadj j is hj p hp
          cases p with
          | run _ => cases hnr
          | bar li =>
              rw [drop_eq_cons hp]
              simp only [outSegs, outSeg, List.flatten_cons, List.cons_append,
                List.nil_append]
              obtain ⟨ii, ir⟩ := li
              cases ir with
              | Lret => exact absurd ⟨ii, hp⟩ hr
              | _ => rfl
    rw [hregs]
    exact isPhysGP_mem_physGPs hg
  · right
    simp only [lendAt, List.mem_append, Std.HashSet.mem_toList, mem_foldr_stepF_snd]
    exact Or.inr (Or.inl hx)
  · right
    simp only [lendAt, List.mem_append, Std.HashSet.mem_toList, mem_foldr_stepF_snd]
    exact Or.inr (Or.inr hx)

/-! ## 8. Fetching from the two bodies -/

theorem seg_fetch' {segs : List Lcmd} {j : Nat} {seg : Lcmd} (h : segs[j]? = some seg)
    (o : Nat) (ho : o < seg.length) :
    (segs.flatten.map Linstr.li_i)[bdry segs j + o]? = some (seg[o]).li_i := by
  obtain ⟨hk, hseg⟩ := List.getElem?_eq_some_iff.1 h
  subst hseg
  exact seg_fetch segs j hk o ho

theorem bdry_succ' {segs : List Lcmd} {j : Nat} {seg : Lcmd} (h : segs[j]? = some seg) :
    bdry segs (j + 1) = bdry segs j + seg.length := by
  obtain ⟨hk, hseg⟩ := List.getElem?_eq_some_iff.1 h
  subst hseg
  exact bdry_succ segs j hk

theorem outSegs_getElem? (res : List String) (lf : Std.HashSet String) :
    ∀ (ps : List Piece) (j : Nat), (outSegs res lf ps)[j]? =
      ps[j]?.map (fun p => outSeg res p ((ps.drop (j + 1)).foldr (stepF res) ([], lf))) := by
  intro ps
  induction ps with
  | nil => intro j; simp [outSegs]
  | cons p ps ih =>
      intro j
      cases j with
      | zero => rfl
      | succ j => simpa [outSegs] using ih j

theorem forall₂_segRel (res : List String) (lf : Std.HashSet String) :
    ∀ ps : List Piece, List.Forall₂ SegRel (ps.map Piece.toLcmd) (outSegs res lf ps) := by
  intro ps
  induction ps with
  | nil => exact List.Forall₂.nil
  | cons p ps ih =>
      refine List.Forall₂.cons ?_ ih
      cases p with
      | bar li => exact Or.inl ⟨rfl, rfl⟩
      | run is =>
          refine Or.inr ⟨?_, ?_⟩ <;>
            · intro lbl x hx
              simp only [Piece.toLcmd, outSeg, List.mem_map] at hx
              obtain ⟨i, _, rfl⟩ := hx
              rfl

theorem bar_mem_body {body : Lcmd} {j : Nat} {li : Linstr}
    (h : (pieces body)[j]? = some (.bar li)) : li ∈ body := by
  have hp : Piece.bar li ∈ pieces body := List.mem_of_getElem? h
  rw [← pieces_flatten body]
  exact List.mem_flatten.2 ⟨[li], List.mem_map_of_mem hp, List.mem_singleton_self _⟩

theorem run_mem_body {body : Lcmd} {j : Nat} {is : List FI}
    (h : (pieces body)[j]? = some (.run is)) {i : FI} (hi : i ∈ is) : i.toL ∈ body := by
  have hp : Piece.run is ∈ pieces body := List.mem_of_getElem? h
  rw [← pieces_flatten body]
  exact List.mem_flatten.2 ⟨is.map FI.toL, List.mem_map_of_mem hp, List.mem_map_of_mem hi⟩

theorem getFundef_reallocLprog (P : Lprog) (fn : String) :
    getFundef (reallocLprog P) fn =
      (getFundef P fn).map (fun fd => { fd with lfd_body := reallocBody fd.lfd_res fd.lfd_body }) := by
  simp only [getFundef, reallocLprog, List.find?_map, Option.map_map]
  rfl

theorem runWith_total {w : Nat} (sem : String → List (BitVec w) → Option (BitVec w)) :
    ∀ (is : List FI), (∀ i ∈ is, ∀ s : Lstate w, (stepWith sem i s).isSome) →
      ∀ s : Lstate w, ∃ b, runWith sem is s = some b := by
  intro is
  induction is with
  | nil => intro _ s; exact ⟨s, rfl⟩
  | cons i is ih =>
      intro h s
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 (h i (List.mem_cons_self ..) s)
      obtain ⟨b, hb⟩ := ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) s'
      exact ⟨b, by simp only [runWith, hs', hb]⟩

/-- The names a kept instruction reads are in `Need` at its piece. -/
theorem bar_reads_need {ps : List Piece} {lf : Std.HashSet String} {j : Nat} {li : Linstr}
    (hj : ps[j]? = some (.bar li))
    {x : String} (hx : x ∈ readNames li.li_i) : Need ps lf j x := by
  by_cases hl : isLoc x = true
  · have hnr : ¬ RetAt ps j := by
      refine not_retAt_bar hj ?_
      intro hret
      rw [hret] at hx
      simp [readNames] at hx
    by_cases hf : isFrame x = true
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [drop_eq_cons hj, List.flatMap_cons, List.mem_append]
      left
      simp only [Piece.frames]
      obtain ⟨ii, ir⟩ := li
      cases ir with
      | Lopn ds opn ss =>
          simp only [readNames, List.mem_flatMap] at hx
          obtain ⟨o, ho, hxo⟩ := hx
          simp only [instrFrames, ← List.flatMap_append, List.mem_flatMap]
          refine ⟨o, ho, ?_⟩
          cases o with
          | reg n =>
              simp only [opNames, List.mem_singleton] at hxo
              subst hxo
              simp [opFrames, hf]
          | arrIdx b y sc =>
              simp only [opNames, List.mem_singleton] at hxo
              subst hxo
              simp [opFrames, hf]
          | _ => simp [opNames] at hxo
      | Lcond c l =>
          simp only [readNames] at hx
          simp only [instrFrames]
          cases c with
          | reg n =>
              simp only [opNames, List.mem_singleton] at hx
              subst hx
              simp [opFrames, hf]
          | arrIdx b y sc =>
              simp only [opNames, List.mem_singleton] at hx
              subst hx
              simp [opFrames, hf]
          | _ => simp [opNames] at hx
      | _ => simp [readNames] at hx
    · exact Or.inr (Or.inl ⟨isPhysGP_of_loc hl (by simpa using hf), hnr⟩)
  · exact Or.inl (by simpa using hl)

/-! ## 9. The simulation -/

/-- The hypotheses on one function body under which the pass preserves constant
    time. -/
structure ReallocOk (w : Nat) (fn : String) (fd : Lfundef) : Prop where
  /-- Every fragment instruction steps from every state. -/
  frag_total : ∀ li ∈ fd.lfd_body, ∀ i, fragOf? li = some i →
    ∀ s : Lstate w, (stepWith semL i s).isSome
  /-- Every `Lgoto` targets this function. -/
  goto_local : ∀ li ∈ fd.lfd_body, ∀ (fn' : String) (l : LLabel),
    li.li_i = .Lgoto (fn', l) → fn' = fn
  /-- No result register is a frame cell. -/
  res_noFrame : ∀ x ∈ fd.lfd_res, isFrame x = false

/-- The segments of a source body: its pieces. -/
abbrev srcSegs (fd : Lfundef) : List Lcmd := (pieces fd.lfd_body).map Piece.toLcmd

/-- The segments of the re-allocated body: the images of the pieces. -/
abbrev tgtSegs (fd : Lfundef) : List Lcmd :=
  outSegs fd.lfd_res (labelLiveFrames fd.lfd_body) (pieces fd.lfd_body)

/-- The simulation relation for two target states at the image of piece `j`: two
    source states at piece `j`, each in agreement with its target state, with
    equal leakage for every fuel. -/
def JAt {w : Nat} {ε : Type} (L : LeakFn w ε) (P : Lprog) (fn : String) (fd : Lfundef) (j : Nat)
    (τ₁ τ₂ : LstateP w) : Prop :=
  ∃ σ₁ σ₂ : LstateP w,
    j ≤ (pieces fd.lfd_body).length ∧
    σ₁.lfn = fn ∧ σ₂.lfn = fn ∧ τ₁.lfn = fn ∧ τ₂.lfn = fn ∧
    σ₁.base.lpc = bdry (srcSegs fd) j ∧ σ₂.base.lpc = bdry (srcSegs fd) j ∧
    τ₁.base.lpc = bdry (tgtSegs fd) j ∧ τ₂.base.lpc = bdry (tgtSegs fd) j ∧
    Inv (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j σ₁.base τ₁.base ∧
    Inv (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j σ₂.base τ₂.base ∧
    ∀ m, lprogLeak L P m σ₁ = lprogLeak L P m σ₂

theorem src_fetch {P : Lprog} {fn : String} {fd : Lfundef} (hfd : getFundef P fn = some fd)
    {w : Nat} (u : LstateP w) (hu : u.lfn = fn) :
    findInstr P u = ((srcSegs fd).flatten.map Linstr.li_i)[u.base.lpc]? := by
  simp only [findInstr, hu, hfd, List.getElem?_map, srcSegs, pieces_flatten]

theorem tgt_fetch {P : Lprog} {fn : String} {fd : Lfundef} (hfd : getFundef P fn = some fd)
    {w : Nat} (u : LstateP w) (hu : u.lfn = fn) :
    findInstr (reallocLprog P) u = ((tgtSegs fd).flatten.map Linstr.li_i)[u.base.lpc]? := by
  simp only [findInstr, hu, getFundef_reallocLprog, hfd, Option.map_some, List.getElem?_map,
    tgtSegs, reallocBody_eq]

theorem srcSegs_getElem? (fd : Lfundef) (j : Nat) :
    (srcSegs fd)[j]? = (pieces fd.lfd_body)[j]?.map Piece.toLcmd := by
  simp [srcSegs]

theorem tgtSegs_getElem?_run (fd : Lfundef) {j : Nat} {is : List FI}
    (hj : (pieces fd.lfd_body)[j]? = some (.run is)) :
    (tgtSegs fd)[j]? = some ((reallocRun (lendAt fd.lfd_res (labelLiveFrames fd.lfd_body)
      (pieces fd.lfd_body) j) is).map FI.toL) := by
  rw [tgtSegs, outSegs_getElem?, hj, Option.map_some, outSeg_run_eq]

theorem tgtSegs_getElem?_bar (fd : Lfundef) {j : Nat} {li : Linstr}
    (hj : (pieces fd.lfd_body)[j]? = some (.bar li)) : (tgtSegs fd)[j]? = some [li] := by
  rw [tgtSegs, outSegs_getElem?, hj]
  rfl

theorem run_fetch {segs : List Lcmd} {j : Nat} {is : List FI}
    (h : segs[j]? = some (is.map FI.toL)) :
    ∀ (k : Nat) (hk : k < (is.map FI.toR).length),
      (segs.flatten.map Linstr.li_i)[bdry segs j + k]? = some (is.map FI.toR)[k] := by
  intro k hk
  rw [seg_fetch' h k (by simpa using hk)]
  simp [FI.toL]

theorem run_silent {w : Nat} {ε : Type} (L : LeakFn w ε) {is : List FI}
    (hwf : ∀ i ∈ is, i.wf = true) :
    ∀ i ∈ is.map FI.toR, IsStraightLine i = true ∧ ∀ t : Lstate w, L.ev t i = [] := by
  intro i hi
  obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hi
  exact ⟨rfl, fun t => L.frag t _ _ _ (wf_of_srcs (hwf i' hi'))⟩

/-- **The run case.** Across a run, both target states reach the image of the
    next piece, silently and in the same number of steps, in the relation. -/
theorem sim_run {w : Nat} {ε : Type} (L : LeakFn w ε) (P : Lprog) (fn : String) (fd : Lfundef)
    (hfd : getFundef P fn = some fd) (hok : ReallocOk w fn fd) (j : Nat) (is : List FI)
    (hj : (pieces fd.lfd_body)[j]? = some (.run is)) (τ₁ τ₂ : LstateP w)
    (hJ : JAt L P fn fd j τ₁ τ₂) :
    ∃ (k : Nat) (τ₁' τ₂' : LstateP w), JAt L P fn fd (j + 1) τ₁' τ₂' ∧
      (∀ n, lprogLeak L (reallocLprog P) n τ₁ = lprogLeak L (reallocLprog P) (n - k) τ₁') ∧
      (∀ n, lprogLeak L (reallocLprog P) n τ₂ = lprogLeak L (reallocLprog P) (n - k) τ₂') := by
  obtain ⟨σ₁, σ₂, hjle, hσ1, hσ2, hτ1, hτ2, hs1pc, hs2pc, ht1pc, ht2pc, hI1, hI2, hEq⟩ := hJ
  have hjlt : j < (pieces fd.lfd_body).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hgood := pieces_good fd.lfd_body (.run is) (List.mem_of_getElem? hj)
  have hfrag : ∀ i ∈ is, fragOf? i.toL = some i := hgood.2
  have hwf : ∀ i ∈ is, i.wf = true := fun i hi => fragOf?_wf (hfrag i hi)
  have htot : ∀ i ∈ is, ∀ s : Lstate w, (stepWith semL i s).isSome :=
    fun i hi s => hok.frag_total _ (run_mem_body hj hi) i (hfrag i hi) s
  have hsl := run_silent L hwf
  have hsrcj : (srcSegs fd)[j]? = some (is.map FI.toL) := by
    rw [srcSegs_getElem?, hj]; rfl
  have hstr : ∀ (out : List FI), (∀ i ∈ out, i.wf = true) → ∀ (s b : Lstate w),
      runWith semL out s = some b → lsemStraight (out.map FI.toR) s = some b := by
    intro out hw s b h
    rw [lsemStraight_map_toR out hw]
    exact h
  -- the source runs
  obtain ⟨b₁, hb₁⟩ := runWith_total semL is htot σ₁.base
  obtain ⟨b₂, hb₂⟩ := runWith_total semL is htot σ₂.base
  have hs1 := lprogLeak_silent L P fn _ (src_fetch hfd) (is.map FI.toR) hsl _ (run_fetch hsrcj)
    σ₁ hσ1 hs1pc b₁ (hstr is hwf _ _ hb₁)
  have hs2 := lprogLeak_silent L P fn _ (src_fetch hfd) (is.map FI.toR) hsl _ (run_fetch hsrcj)
    σ₂ hσ2 hs2pc b₂ (hstr is hwf _ _ hb₂)
  have hb1pc : b₁.lpc = bdry (srcSegs fd) (j + 1) := by
    rw [lsemStraight_lpc _ _ _ (fun i hi => (hsl i hi).1) (hstr is hwf _ _ hb₁), hs1pc,
      bdry_succ' hsrcj]
    simp
  have hb2pc : b₂.lpc = bdry (srcSegs fd) (j + 1) := by
    rw [lsemStraight_lpc _ _ _ (fun i hi => (hsl i hi).1) (hstr is hwf _ _ hb₂), hs2pc,
      bdry_succ' hsrcj]
    simp
  -- the target runs
  have hR1 := inv_run_rel fd.lfd_res hok.res_noFrame _ _ j is hj σ₁.base τ₁.base hI1
  have hR2 := inv_run_rel fd.lfd_res hok.res_noFrame _ _ j is hj σ₂.base τ₂.base hI2
  obtain ⟨hwo, c₁, hc₁, hF₁⟩ := reallocRun_rel _ is hwf σ₁.base b₁ τ₁.base hR1 hb₁
  obtain ⟨_, c₂, hc₂, hF₂⟩ := reallocRun_rel _ is hwf σ₂.base b₂ τ₂.base hR2 hb₂
  have htgtj := tgtSegs_getElem?_run fd hj
  have hslo := run_silent L hwo
  have ht1 := lprogLeak_silent L (reallocLprog P) fn _ (tgt_fetch hfd) _ hslo _
    (run_fetch htgtj) τ₁ hτ1 ht1pc c₁ (hstr _ hwo _ _ hc₁)
  have ht2 := lprogLeak_silent L (reallocLprog P) fn _ (tgt_fetch hfd) _ hslo _
    (run_fetch htgtj) τ₂ hτ2 ht2pc c₂ (hstr _ hwo _ _ hc₂)
  have hc1pc : c₁.lpc = bdry (tgtSegs fd) (j + 1) := by
    rw [lsemStraight_lpc _ _ _ (fun i hi => (hslo i hi).1) (hstr _ hwo _ _ hc₁), ht1pc,
      bdry_succ' htgtj]
    simp
  have hc2pc : c₂.lpc = bdry (tgtSegs fd) (j + 1) := by
    rw [lsemStraight_lpc _ _ _ (fun i hi => (hslo i hi).1) (hstr _ hwo _ _ hc₂), ht2pc,
      bdry_succ' htgtj]
    simp
  refine ⟨_, ⟨c₁, fn⟩, ⟨c₂, fn⟩, ⟨⟨b₁, fn⟩, ⟨b₂, fn⟩, by omega, rfl, rfl, rfl, rfl, hb1pc, hb2pc,
    hc1pc, hc2pc, final_inv _ _ _ (pieces_noAdjRuns _) j is hj _ _ hF₁,
    final_inv _ _ _ (pieces_noAdjRuns _) j is hj _ _ hF₂, fun m => ?_⟩, ht1, ht2⟩
  have h := hEq (m + (is.map FI.toR).length)
  rw [hs1, hs2, Nat.add_sub_cancel] at h
  exact h

theorem forall₂_segRel_swap : ∀ {A B : List Lcmd}, List.Forall₂ SegRel A B →
    List.Forall₂ SegRel B A
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h.symm (forall₂_segRel_swap t)

theorem label_of_findLabel {body : Lcmd} {l : LLabel} {pc : Nat}
    (h : findLabel l (body.map Linstr.li_i) = some pc) :
    ∃ li ∈ body, ∃ k l', li.li_i = .Llabel k l' := by
  obtain ⟨ir, hir, hlab⟩ := findLabel_sound l _ pc h
  rw [List.getElem?_map] at hir
  obtain ⟨li, hli, rfl⟩ := Option.map_eq_some_iff.1 hir
  refine ⟨li, List.mem_of_getElem? hli, ?_⟩
  cases h' : li.li_i
  all_goals first
    | exact ⟨_, _, rfl⟩
    | (rw [h'] at hlab; simp [isLabel] at hlab)

/-- **The jump case.** A jump to a label of the function from two related pairs
    fails on both target states or reaches, on both, the image of the piece after
    the label, in the relation. -/
theorem sim_jump {w : Nat} {ε : Type} (L : LeakFn w ε) (P : Lprog) (fn : String) (fd : Lfundef)
    (hfd : getFundef P fn = some fd) (j : Nat) (σ₁ σ₂ τ₁ τ₂ : LstateP w)
    (hI1 : Inv (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j σ₁.base τ₁.base)
    (hI2 : Inv (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j σ₂.base τ₂.base)
    (hnr : ¬ RetAt (pieces fd.lfd_body) j) (l : LLabel)
    (hnext : ∀ a b, evalJump P (fn, l) σ₁ = some a → evalJump P (fn, l) σ₂ = some b →
      ∀ m, lprogLeak L P m a = lprogLeak L P m b) :
    (evalJump (reallocLprog P) (fn, l) τ₁ = none ∧ evalJump (reallocLprog P) (fn, l) τ₂ = none) ∨
      ∃ x y j', evalJump (reallocLprog P) (fn, l) τ₁ = some x ∧
        evalJump (reallocLprog P) (fn, l) τ₂ = some y ∧ JAt L P fn fd j' x y := by
  have hF2 : List.Forall₂ SegRel (tgtSegs fd) (srcSegs fd) :=
    forall₂_segRel_swap (forall₂_segRel _ _ _)
  simp only [evalJump, getFundef_reallocLprog, hfd, Option.map_some]
  rw [reallocBody_eq]
  cases ht : findLabel l ((tgtSegs fd).flatten.map Linstr.li_i) with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some pc' =>
      right
      obtain ⟨k, hk, rfl, hs, hA1, hB1⟩ := findLabel_segs l _ _ hF2 pc' ht
      have hsb : findLabel l (fd.lfd_body.map Linstr.li_i) = some (bdry (srcSegs fd) k) := by
        have hb : fd.lfd_body = (srcSegs fd).flatten := (pieces_flatten _).symm
        rw [hb]
        exact hs
      have hall : ∀ x ∈ (pieces fd.lfd_body).flatMap Piece.frames,
          x ∈ labelLiveFrames fd.lfd_body := by
        intro x hx
        rw [pieces_frames] at hx
        exact mem_labelLiveFrames (label_of_findLabel hsb) hx
      have hk' : k < (pieces fd.lfd_body).length := by
        simpa [tgtSegs, outSegs_length] using hk
      have hj1 : evalJump P (fn, l) σ₁ = some (σ₁.setcpc fn (bdry (srcSegs fd) k + 1)) := by
        simp only [evalJump, hfd, hsb]
      have hj2 : evalJump P (fn, l) σ₂ = some (σ₂.setcpc fn (bdry (srcSegs fd) k + 1)) := by
        simp only [evalJump, hfd, hsb]
      refine ⟨_, _, k + 1, rfl, rfl, σ₁.setcpc fn (bdry (srcSegs fd) k + 1),
        σ₂.setcpc fn (bdry (srcSegs fd) k + 1), by omega, rfl, rfl, rfl, rfl,
        hB1.symm, hB1.symm, hA1.symm, hA1.symm,
        ⟨hI1.1, fun x hx => hI1.2 x (Need_of_allFrames hall hnr hx)⟩,
        ⟨hI2.1, fun x hx => hI2.2 x (Need_of_allFrames hall hnr hx)⟩, hnext _ _ hj1 hj2⟩

/-- **The kept-instruction and end cases.** At the image of a piece that is not a
    run, the two target states emit the same events for every fuel, given that
    related pairs do so for every smaller fuel. -/
theorem sim_bar {w : Nat} {ε : Type} (L : LeakFn w ε) (P : Lprog) (fn : String) (fd : Lfundef)
    (hfd : getFundef P fn = some fd) (hok : ReallocOk w fn fd) (n : Nat)
    (IH : ∀ m < n, ∀ j (τ₁ τ₂ : LstateP w), JAt L P fn fd j τ₁ τ₂ →
      lprogLeak L (reallocLprog P) m τ₁ = lprogLeak L (reallocLprog P) m τ₂)
    (j : Nat) (τ₁ τ₂ : LstateP w) (hJ : JAt L P fn fd j τ₁ τ₂)
    (hnr : ∀ is, (pieces fd.lfd_body)[j]? ≠ some (.run is)) :
    lprogLeak L (reallocLprog P) n τ₁ = lprogLeak L (reallocLprog P) n τ₂ := by
  obtain ⟨σ₁, σ₂, hjle, hσ1, hσ2, hτ1, hτ2, hs1pc, hs2pc, ht1pc, ht2pc, hI1, hI2, hEq⟩ := hJ
  cases n with
  | zero => rfl
  | succ m =>
  cases hp : (pieces fd.lfd_body)[j]? with
  | none =>
      have hjeq : j = (pieces fd.lfd_body).length := by
        have := List.getElem?_eq_none_iff.1 hp
        omega
      have hnone : ∀ τ : LstateP w, τ.lfn = fn → τ.base.lpc = bdry (tgtSegs fd) j →
          findInstr (reallocLprog P) τ = none := by
        intro τ hf hpc
        rw [tgt_fetch hfd τ hf, hpc, hjeq,
          ← outSegs_length fd.lfd_res (labelLiveFrames fd.lfd_body) (pieces fd.lfd_body),
          bdry_length]
        simp only [List.getElem?_map, List.getElem?_eq_none (Nat.le_refl _), Option.map_none]
      rw [lprogLeak_of_findInstr_none _ _ _ (hnone τ₁ hτ1 ht1pc),
        lprogLeak_of_findInstr_none _ _ _ (hnone τ₂ hτ2 ht2pc)]
  | some p =>
  cases p with
  | run is => exact absurd hp (hnr is)
  | bar li =>
  have hlt : j < (pieces fd.lfd_body).length := (List.getElem?_eq_some_iff.1 hp).1
  have hli : li ∈ fd.lfd_body := bar_mem_body hp
  have hsrcj : (srcSegs fd)[j]? = some [li] := by rw [srcSegs_getElem?, hp]; rfl
  have htgtj := tgtSegs_getElem?_bar fd hp
  have hfs : ∀ σ : LstateP w, σ.lfn = fn → σ.base.lpc = bdry (srcSegs fd) j →
      findInstr P σ = some li.li_i := by
    intro σ hf hpc
    rw [src_fetch hfd σ hf, hpc, ← Nat.add_zero (bdry _ j), seg_fetch' hsrcj 0 (by simp)]
    rfl
  have hft : ∀ τ : LstateP w, τ.lfn = fn → τ.base.lpc = bdry (tgtSegs fd) j →
      findInstr (reallocLprog P) τ = some li.li_i := by
    intro τ hf hpc
    rw [tgt_fetch hfd τ hf, hpc, ← Nat.add_zero (bdry _ j), seg_fetch' htgtj 0 (by simp)]
    rfl
  have hf1 := hfs σ₁ hσ1 hs1pc
  have hf2 := hfs σ₂ hσ2 hs2pc
  obtain ⟨hev12, _, hnext12⟩ := lprogLeak_split L P hEq (hσ1.trans hσ2.symm) hf1 hf2
  have hreads : ∀ x ∈ readNames li.li_i,
      Need (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j x :=
    fun x hx => bar_reads_need hp hx
  have hevt : ∀ σ τ : LstateP w,
      Inv (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j σ.base τ.base →
      L.ev τ.base li.li_i = L.ev σ.base li.li_i :=
    fun σ τ hI => L.congr _ _ _ hI.1 (fun x hx => hI.2 x (hreads x hx))
  rw [lprogLeak_succ_of_findInstr L _ m (hft τ₁ hτ1 ht1pc),
    lprogLeak_succ_of_findInstr L _ m (hft τ₂ hτ2 ht2pc),
    hevt σ₁ τ₁ hI1, hevt σ₂ τ₂ hI2, hev12]
  congr 1
  have tail : ∀ a b : Option (LstateP w),
      ((a = none ∧ b = none) ∨ ∃ x y j', a = some x ∧ b = some y ∧ JAt L P fn fd j' x y) →
      (match a with
        | some s' => lprogLeak L (reallocLprog P) m s'
        | none => []) =
      (match b with
        | some s' => lprogLeak L (reallocLprog P) m s'
        | none => []) := by
    rintro a b (⟨rfl, rfl⟩ | ⟨x, y, j', rfl, rfl, hxy⟩)
    · rfl
    · exact IH m (Nat.lt_succ_self m) j' x y hxy
  apply tail
  have hsucc : ∀ (segs : List Lcmd), segs[j]? = some [li] → bdry segs j + 1 = bdry segs (j + 1) :=
    fun segs h => (bdry_succ' h).symm
  -- a straight-line kept instruction
  have hstraight : IsStraightLine li.li_i = true →
      (evalInstrP (reallocLprog P) li.li_i τ₁ = none ∧
        evalInstrP (reallocLprog P) li.li_i τ₂ = none) ∨
      ∃ x y j', evalInstrP (reallocLprog P) li.li_i τ₁ = some x ∧
        evalInstrP (reallocLprog P) li.li_i τ₂ = some y ∧ JAt L P fn fd j' x y := by
    intro hsl
    have hnret : ¬ RetAt (pieces fd.lfd_body) j :=
      not_retAt_bar hp (by intro h; rw [h] at hsl; cases hsl)
    rw [evalInstrP_straightLine _ _ τ₁ hsl, evalInstrP_straightLine _ _ τ₂ hsl]
    have hA1 := lsemStep_agreeOn (Need (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j)
      li.li_i (s := σ₁.base) (t := τ₁.base) hI1.1.symm
      (fun x hx => (hI1.2 x (hreads x hx)).symm) (fun x hx => (hI1.2 x hx).symm)
    have hA2 := lsemStep_agreeOn (Need (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j)
      li.li_i (s := σ₂.base) (t := τ₂.base) hI2.1.symm
      (fun x hx => (hI2.2 x (hreads x hx)).symm) (fun x hx => (hI2.2 x hx).symm)
    have h12 := lsemStep_isSome_congr li.li_i σ₁.base σ₂.base
    cases hs1 : lsemStep li.li_i σ₁.base with
    | none =>
        rw [hs1] at hA1 h12
        have ht1 : lsemStep li.li_i τ₁.base = none :=
          Option.isNone_iff_eq_none.1 (by simpa using hA1.1.symm)
        have hs2 : lsemStep li.li_i σ₂.base = none :=
          Option.isNone_iff_eq_none.1 (by simpa using h12.symm)
        rw [hs2] at hA2
        have ht2 : lsemStep li.li_i τ₂.base = none :=
          Option.isNone_iff_eq_none.1 (by simpa using hA2.1.symm)
        left
        simp [ht1, ht2]
    | some s₁' =>
        rw [hs1] at hA1 h12
        obtain ⟨t₁', ht1⟩ := Option.isSome_iff_exists.1 (by simpa using hA1.1.symm)
        obtain ⟨s₂', hs2⟩ := Option.isSome_iff_exists.1 (by simpa using h12.symm)
        rw [hs2] at hA2
        obtain ⟨t₂', ht2⟩ := Option.isSome_iff_exists.1 (by simpa using hA2.1.symm)
        obtain ⟨hm1, hv1⟩ := hA1.2 s₁' t₁' rfl ht1
        obtain ⟨hm2, hv2⟩ := hA2.2 s₂' t₂' rfl ht2
        have he1 : evalInstrP P li.li_i σ₁ = some { σ₁ with base := s₁' } := by
          rw [evalInstrP_straightLine _ _ _ hsl, hs1]; rfl
        have he2 : evalInstrP P li.li_i σ₂ = some { σ₂ with base := s₂' } := by
          rw [evalInstrP_straightLine _ _ _ hsl, hs2]; rfl
        right
        refine ⟨{ τ₁ with base := t₁' }, { τ₂ with base := t₂' }, j + 1,
          by rw [ht1]; rfl, by rw [ht2]; rfl, { σ₁ with base := s₁' }, { σ₂ with base := s₂' },
          by omega, hσ1, hσ2, hτ1, hτ2, ?_, ?_, ?_, ?_,
          ⟨hm1.symm, fun x hx => (hv1 x (Need_mono (Nat.le_succ j) hnret hx)).symm⟩,
          ⟨hm2.symm, fun x hx => (hv2 x (Need_mono (Nat.le_succ j) hnret hx)).symm⟩,
          (hnext12 _ _ he1 he2).2.2⟩
        · show s₁'.lpc = _
          rw [lsemStep_lpc_succ _ _ _ hsl hs1, hs1pc, hsucc _ hsrcj]
        · show s₂'.lpc = _
          rw [lsemStep_lpc_succ _ _ _ hsl hs2, hs2pc, hsucc _ hsrcj]
        · show t₁'.lpc = _
          rw [lsemStep_lpc_succ _ _ _ hsl ht1, ht1pc, hsucc _ htgtj]
        · show t₂'.lpc = _
          rw [lsemStep_lpc_succ _ _ _ hsl ht2, ht2pc, hsucc _ htgtj]
  obtain ⟨ii, ir⟩ := li
  cases ir with
  | Lopn ds opn ss => exact hstraight rfl
  | Llabel k l => exact hstraight rfl
  | Lalign => exact hstraight rfl
  | Lgoto d =>
      obtain ⟨fn', l⟩ := d
      have hfn' := hok.goto_local _ hli fn' l rfl
      subst hfn'
      have hnret : ¬ RetAt (pieces fd.lfd_body) j := not_retAt_bar hp (by simp)
      exact sim_jump L P fn' fd hfd j σ₁ σ₂ τ₁ τ₂ hI1 hI2 hnret l
        (fun a b ha hb => (hnext12 a b ha hb).2.2)
  | Lcond c l =>
      have hnret : ¬ RetAt (pieces fd.lfd_body) j := not_retAt_bar hp (by simp)
      have hc12 := L.cond _ _ c l hev12
      have hcτ : ∀ σ τ : LstateP w,
          Inv (pieces fd.lfd_body) (labelLiveFrames fd.lfd_body) j σ.base τ.base →
          evalOperand τ.base c = evalOperand σ.base c := by
        intro σ τ hI
        exact evalOperand_agreeOn hI.1 c (fun x hx => hI.2 x (hreads x (by simpa [readNames] using hx)))
      simp only [evalInstrP] at hnext12 ⊢
      rw [hcτ σ₁ τ₁ hI1, hcτ σ₂ τ₂ hI2, hτ1, hτ2]
      rw [hσ1, hσ2] at hnext12
      by_cases h1 : evalOperand σ₁.base c ≠ 0
      · have h2 := hc12.1 h1
        simp only [h1, h2, ite_true, ne_eq, not_false_eq_true] at hnext12 ⊢
        exact sim_jump L P fn fd hfd j σ₁ σ₂ τ₁ τ₂ hI1 hI2 hnret l
          (fun a b ha hb => (hnext12 a b ha hb).2.2)
      · have h2 : ¬ evalOperand σ₂.base c ≠ 0 := fun h => h1 (hc12.2 h)
        simp only [h1, h2, ite_false] at hnext12 ⊢
        right
        refine ⟨τ₁.nextPc, τ₂.nextPc, j + 1, rfl, rfl, σ₁.nextPc, σ₂.nextPc, by omega,
          hσ1, hσ2, hτ1, hτ2, ?_, ?_, ?_, ?_,
          ⟨hI1.1, fun x hx => hI1.2 x (Need_mono (Nat.le_succ j) hnret hx)⟩,
          ⟨hI2.1, fun x hx => hI2.2 x (Need_mono (Nat.le_succ j) hnret hx)⟩,
          (hnext12 _ _ rfl rfl).2.2⟩
        · simp only [LstateP.lpc_nextPc, hs1pc]; exact hsucc _ hsrcj
        · simp only [LstateP.lpc_nextPc, hs2pc]; exact hsucc _ hsrcj
        · simp only [LstateP.lpc_nextPc, ht1pc]; exact hsucc _ htgtj
        · simp only [LstateP.lpc_nextPc, ht2pc]; exact hsucc _ htgtj
  | Ligoto _ => exact Or.inl ⟨rfl, rfl⟩
  | Lcall _ _ => exact Or.inl ⟨rfl, rfl⟩
  | Lret => exact Or.inl ⟨rfl, rfl⟩
  | LstoreLabel _ _ => exact Or.inl ⟨rfl, rfl⟩
  | Lsyscall _ => exact Or.inl ⟨rfl, rfl⟩

/-- **The simulation.** Two target states in the relation at any piece have equal
    leakage for every fuel. -/
theorem sim_main {w : Nat} {ε : Type} (L : LeakFn w ε) (P : Lprog) (fn : String) (fd : Lfundef)
    (hfd : getFundef P fn = some fd) (hok : ReallocOk w fn fd) :
    ∀ (n j : Nat) (τ₁ τ₂ : LstateP w), JAt L P fn fd j τ₁ τ₂ →
      lprogLeak L (reallocLprog P) n τ₁ = lprogLeak L (reallocLprog P) n τ₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
      intro j τ₁ τ₂ hJ
      by_cases hr : ∃ is, (pieces fd.lfd_body)[j]? = some (.run is)
      · obtain ⟨is, hj⟩ := hr
        obtain ⟨k, τ₁', τ₂', hJ', h1, h2⟩ := sim_run L P fn fd hfd hok j is hj τ₁ τ₂ hJ
        rw [h1 n, h2 n]
        refine sim_bar L P fn fd hfd hok (n - k) (fun m hm => IH m (by omega)) (j + 1) τ₁' τ₂'
          hJ' ?_
        intro is' hj'
        have := noAdjRuns_getElem _ (pieces_noAdjRuns fd.lfd_body) j is hj _ hj'
        cases this
      · exact sim_bar L P fn fd hfd hok n IH j τ₁ τ₂ hJ (fun is h => hr ⟨is, h⟩)

/-- **The register re-allocation preserves constant time from function entry**, for
    every leakage model `L` and every relation `pub` on entry states, when every
    function of `P` satisfies `ReallocOk`. -/
theorem reallocLprog_entryCT {w : Nat} {ε : Type} (L : LeakFn w ε) (P : Lprog)
    (pub : LstateP w → LstateP w → Prop)
    (hok : ∀ fn fd, getFundef P fn = some fd → ReallocOk w fn fd)
    (h : EntryCT L P pub) : EntryCT L (reallocLprog P) pub := by
  intro s₁ s₂ hpub hfn hpc₁ hpc₂ n
  cases hg : getFundef P s₁.lfn with
  | none =>
      have hnone : ∀ s : LstateP w, s.lfn = s₁.lfn → findInstr (reallocLprog P) s = none := by
        intro s hs
        simp only [findInstr, hs, getFundef_reallocLprog, hg, Option.map_none]
      rw [lprogLeak_of_findInstr_none _ _ _ (hnone s₁ rfl),
        lprogLeak_of_findInstr_none _ _ _ (hnone s₂ hfn.symm)]
  | some fd =>
      refine sim_main L P s₁.lfn fd hg (hok _ _ hg) n 0 s₁ s₂
        ⟨s₁, s₂, Nat.zero_le _, rfl, hfn.symm, rfl, hfn.symm, ?_, ?_, ?_, ?_,
          ⟨rfl, fun _ _ => rfl⟩, ⟨rfl, fun _ _ => rfl⟩,
          h s₁ s₂ hpub hfn hpc₁ hpc₂⟩
      all_goals simp [hpc₁, hpc₂]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak
