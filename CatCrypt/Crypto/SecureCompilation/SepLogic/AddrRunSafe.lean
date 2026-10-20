/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.AddrRun
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG

/-!
# The memory accessed by a run of the address machine

For a set of bytes `M`, `StoreIn M frame c s` says that the memory part of the write
footprint of the step at the program counter of `s` (`stepWrites`, the bytes of the range
`storeR?`) lies in `M`; `LoadIn M frame c s` says the same of the read footprint
(`stepReads`, the bytes of the words of `loadsA`); `AccessIn` is their conjunction.

The run predicate `RunSafe frame c Q fuel s zf` (every state that a run of at most `fuel`
steps steps from satisfies `Q`) is monotone in `Q`, closed under conjunction, and holds
from any state satisfying an invariant that every step preserves and that implies `Q`. Under
`RunSafe` for `StoreIn M` the memory locations of `runWrites` lie in `M`, and conversely;
under `RunSafe` for `LoadIn M` the memory locations of `runReads` lie in `M`, and conversely.
A byte outside `M` keeps its value through a halting run.

## Main definitions

* `Addr.StoreIn`, `Addr.LoadIn`, `Addr.AccessIn`.

## Main results

* `DecodePrintedCFG.RunSafe.mono`, `DecodePrintedCFG.RunSafe.and`: closure of the run
  predicate.
* `DecodePrintedCFG.runSafe_of_stepInv`: the run predicate from an invariant preserved by
  every step.
* `Addr.runSafe_storeIn_iff`, `Addr.runWrites_mem_sub`: the memory write footprint of a run.
* `Addr.runSafe_loadIn_iff`, `Addr.runReads_mem_sub`: the memory read footprint of a run.
* `Addr.runA_keep_mem`: a byte outside `M` keeps its value through a halting run.
* `Addr.runSafe_storeMoveBody_storeIn`, `Addr.runA_storeMoveBody_keep_mem`: the cell store
  followed by a register move of `storeMoveBody` stores inside the stored word.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

/-- `RunSafe` is monotone in the state predicate. -/
theorem RunSafe.mono {frame : String → Option (BitVec 64)} {body : Lcmd}
    {P Q : LstateA → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ {fuel : Nat} {s : LstateA} {zf : Bool},
      RunSafe frame body P fuel s zf → RunSafe frame body Q fuel s zf
  | 0, _, _, _ => trivial
  | _ + 1, s, _, h => ⟨hPQ s h.1, fun s' zf' hst => RunSafe.mono hPQ (h.2 s' zf' hst)⟩

/-- `RunSafe` for two state predicates is `RunSafe` for their conjunction. -/
theorem RunSafe.and {frame : String → Option (BitVec 64)} {body : Lcmd}
    {P Q : LstateA → Prop} :
    ∀ {fuel : Nat} {s : LstateA} {zf : Bool},
      RunSafe frame body P fuel s zf → RunSafe frame body Q fuel s zf →
      RunSafe frame body (fun t => P t ∧ Q t) fuel s zf
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, hP, hQ =>
      ⟨⟨hP.1, hQ.1⟩, fun s' zf' hst => RunSafe.and (hP.2 s' zf' hst) (hQ.2 s' zf' hst)⟩

/-- **`RunSafe` from a step invariant.** If `I` is preserved by every step of the address
    machine on `body` and every state satisfying `I` satisfies `Q`, then every run from a state
    satisfying `I` is safe for `Q`. -/
theorem runSafe_of_stepInv {frame : String → Option (BitVec 64)} {body : Lcmd}
    {I : LstateA → Bool → Prop} {Q : LstateA → Prop} (hQ : ∀ s zf, I s zf → Q s)
    (hI : ∀ s zf s' zf', I s zf →
      VIR.JasminLsemAddrRun.stepA frame body s zf = some (s', zf') → I s' zf') :
    ∀ {fuel : Nat} {s : LstateA} {zf : Bool}, I s zf → RunSafe frame body Q fuel s zf
  | 0, _, _, _ => trivial
  | _ + 1, s, zf, h =>
      ⟨hQ s zf h, fun s' zf' hst => runSafe_of_stepInv hQ hI (hI s zf s' zf' h hst)⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG

namespace CatCrypt.Crypto.SecureCompilation.SepLogic.Addr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe)
open Footprinted

/-- The memory part of the write footprint of the step of `c` at the program counter of `s`
    lies in `M`. -/
def StoreIn (M : Set (BitVec 64)) (frame : String → Option (BitVec 64)) (c : Lcmd)
    (s : LstateA) : Prop :=
  ∀ x, Loc.mem x ∈ stepWrites frame c s → x ∈ M

/-- The memory part of the read footprint of the step of `c` at the program counter of `s`
    lies in `M`. -/
def LoadIn (M : Set (BitVec 64)) (frame : String → Option (BitVec 64)) (c : Lcmd)
    (s : LstateA) : Prop :=
  ∀ x, Loc.mem x ∈ stepReads frame c s → x ∈ M

/-- The memory parts of the write and the read footprints of the step of `c` at the program
    counter of `s` lie in `M`. -/
def AccessIn (M : Set (BitVec 64)) (frame : String → Option (BitVec 64)) (c : Lcmd)
    (s : LstateA) : Prop :=
  StoreIn M frame c s ∧ LoadIn M frame c s

/-- At an `Lopn`, `StoreIn` says that the byte range `storeR?` lies in `M`. -/
theorem storeIn_lopn_iff {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} {s : LstateA} {ii : Nat} {ds : List LOperand} {o : String}
    {ss : List LOperand} (hc : c[s.reg.lpc]? = some ⟨ii, .Lopn ds o ss⟩) :
    StoreIn M frame c s ↔ ∀ R, storeR? frame (normA (.Lopn ds o ss),
      tagAt c s.reg.lpc (.Lopn ds o ss)) s.reg = some R → ∀ x ∈ R, x ∈ M := by
  unfold StoreIn stepWrites
  rw [hc]
  exact ⟨fun h R hR x hx => h x ⟨R, hR, hx⟩, fun h x ⟨R, hR, hx⟩ => h R hR x hx⟩

/-- At a halted state the step footprints hold no memory location and the step fails. -/
theorem halted_step {frame : String → Option (BitVec 64)} {c : Lcmd} {s : LstateA}
    (zf : Bool) (h : haltedA c s = true) :
    (∀ x, Loc.mem x ∉ stepWrites frame c s) ∧ (∀ x, Loc.mem x ∉ stepReads frame c s) ∧
      stepA frame c s zf = none := by
  unfold haltedA at h
  unfold stepWrites stepReads stepA
  split at h
  · rename_i hc
    rw [hc]
    refine ⟨fun x hx => ?_, fun x hx => ?_, rfl⟩
    · exact Loc.noConfusion (Set.mem_singleton_iff.1 hx)
    · rcases hx with hx | hx <;> exact Loc.noConfusion hx
  · rename_i hc
    rw [hc]
    refine ⟨fun x hx => ?_, fun x hx => ?_, rfl⟩
    · exact Loc.noConfusion (Set.mem_singleton_iff.1 hx)
    · rcases hx with hx | hx <;> exact Loc.noConfusion hx
  · exact absurd h Bool.false_ne_true

/-- **The memory write footprint of a run.** A run of at most `n` steps stores only in `M`
    at every step it takes exactly when the memory locations of `runWrites` lie in `M`. -/
theorem runSafe_storeIn_iff {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} :
    ∀ {n : Nat} {s : LstateA} {zf : Bool},
      RunSafe frame c (StoreIn M frame c) n s zf ↔
        ∀ x, Loc.mem x ∈ runWrites frame c n s zf → x ∈ M
  | 0, _, _ => ⟨fun _ _ hx => absurd hx (Set.notMem_empty _), fun _ => trivial⟩
  | n + 1, s, zf => by
    cases hs : haltedA c s with
    | true =>
      obtain ⟨hw, -, hst⟩ := halted_step (frame := frame) zf hs
      unfold runWrites
      rw [if_pos hs]
      refine ⟨fun _ _ hx => absurd hx (Set.notMem_empty _), fun _ => ?_⟩
      exact ⟨fun x hx => absurd hx (hw x), fun s' zf' h => by rw [hst] at h; cases h⟩
    | false =>
      unfold runWrites
      rw [if_neg (by simp [hs])]
      constructor
      · rintro ⟨h1, h2⟩ x (hx | hx)
        · exact h1 x hx
        · revert hx h2
          cases stepA frame c s zf with
          | none => intro _ hx; exact absurd hx (Set.notMem_empty _)
          | some p => intro h2 hx; exact runSafe_storeIn_iff.1 (h2 p.1 p.2 rfl) x hx
      · intro h
        refine ⟨fun x hx => h x (Or.inl hx), fun s' zf' hst => ?_⟩
        refine runSafe_storeIn_iff.2 fun x hx => h x (Or.inr ?_)
        rw [hst]
        exact hx

/-- Under `RunSafe` for `StoreIn M` the memory locations of `runWrites` lie in `M`. -/
theorem runWrites_mem_sub {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} {n : Nat} {s : LstateA} {zf : Bool}
    (h : RunSafe frame c (StoreIn M frame c) n s zf) {x : BitVec 64}
    (hx : Loc.mem x ∈ runWrites frame c n s zf) : x ∈ M :=
  runSafe_storeIn_iff.1 h x hx

/-- **The memory read footprint of a run.** A run of at most `n` steps loads only from `M`
    at every step it takes exactly when the memory locations of `runReads` lie in `M`. -/
theorem runSafe_loadIn_iff {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} :
    ∀ {n : Nat} {s : LstateA} {zf : Bool},
      RunSafe frame c (LoadIn M frame c) n s zf ↔
        ∀ x, Loc.mem x ∈ runReads frame c n s zf → x ∈ M
  | 0, _, _ => ⟨fun _ _ hx => Loc.noConfusion (Set.mem_singleton_iff.1 hx), fun _ => trivial⟩
  | n + 1, s, zf => by
    cases hs : haltedA c s with
    | true =>
      obtain ⟨-, hr, hst⟩ := halted_step (frame := frame) zf hs
      unfold runReads
      rw [if_pos hs]
      refine ⟨fun _ _ hx => Loc.noConfusion (Set.mem_singleton_iff.1 hx), fun _ => ?_⟩
      exact ⟨fun x hx => absurd hx (hr x), fun s' zf' h => by rw [hst] at h; cases h⟩
    | false =>
      unfold runReads
      rw [if_neg (by simp [hs])]
      constructor
      · rintro ⟨h1, h2⟩ x (hx | hx)
        · exact h1 x hx
        · revert hx h2
          cases stepA frame c s zf with
          | none => intro _ hx; exact absurd hx (Set.notMem_empty _)
          | some p => intro h2 hx; exact runSafe_loadIn_iff.1 (h2 p.1 p.2 rfl) x hx
      · intro h
        refine ⟨fun x hx => h x (Or.inl hx), fun s' zf' hst => ?_⟩
        refine runSafe_loadIn_iff.2 fun x hx => h x (Or.inr ?_)
        rw [hst]
        exact hx

/-- Under `RunSafe` for `LoadIn M` the memory locations of `runReads` lie in `M`. -/
theorem runReads_mem_sub {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} {n : Nat} {s : LstateA} {zf : Bool}
    (h : RunSafe frame c (LoadIn M frame c) n s zf) {x : BitVec 64}
    (hx : Loc.mem x ∈ runReads frame c n s zf) : x ∈ M :=
  runSafe_loadIn_iff.1 h x hx

/-- `RunSafe` for `AccessIn M` is `RunSafe` for `StoreIn M` and for `LoadIn M`. -/
theorem runSafe_accessIn_iff {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} {n : Nat} {s : LstateA} {zf : Bool} :
    RunSafe frame c (AccessIn M frame c) n s zf ↔
      RunSafe frame c (StoreIn M frame c) n s zf ∧ RunSafe frame c (LoadIn M frame c) n s zf :=
  ⟨fun h => ⟨h.mono fun _ ht => ht.1, h.mono fun _ ht => ht.2⟩, fun h => h.1.and h.2⟩

/-- **A run keeps the memory outside `M`.** A halting run that stores only in `M` at every
    step leaves every byte outside `M` unchanged. -/
theorem runA_keep_mem {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)} {c : Lcmd}
    {n : Nat} {s : LstateA} {zf : Bool} {p : LstateA × Bool}
    (h : runA frame c n s zf = some p) (hs : RunSafe frame c (StoreIn M frame c) n s zf)
    {x : BitVec 64} (hx : x ∉ M) : p.1.mem x = s.mem x :=
  (runA_writesIn frame c h (Loc.mem x) fun hw => hx (runWrites_mem_sub hs hw)).symm

/-! ## A cell store followed by a register move -/

/-- Two steps of `storeMoveBody` from the first instruction store only in the word at the
    address in `B`. -/
theorem runSafe_storeMoveBody_storeIn {s : LstateA} (zf : Bool) (hpc : s.reg.lpc = 0)
    {p v : BitVec 64} (hB : s.reg.getW "B" 64 = some p) (hV : s.reg.getW "V" 64 = some v) :
    RunSafe (fun _ => none) storeMoveBody
      (StoreIn (⟨p + BitVec.ofNat 64 0, 8⟩ : Rng 64).toSet (fun _ => none) storeMoveBody)
      2 s zf := by
  refine runSafe_storeIn_iff.2 fun x hx => ?_
  rw [runWrites_storeMoveBody zf hpc hB hV] at hx
  exact hx

/-- **Non-vacuity of `runA_keep_mem`.** Two steps of `storeMoveBody` from the first
    instruction halt and keep every byte outside the word at the address in `B`. -/
theorem runA_storeMoveBody_keep_mem {s : LstateA} (zf : Bool) (hpc : s.reg.lpc = 0)
    {p v : BitVec 64} (hB : s.reg.getW "B" 64 = some p) (hV : s.reg.getW "V" 64 = some v) :
    ∃ q, runA (fun _ => none) storeMoveBody 2 s zf = some q ∧
      ∀ x, x ∉ (⟨p + BitVec.ofNat 64 0, 8⟩ : Rng 64).toSet → q.1.mem x = s.mem x := by
  obtain ⟨q, hq, -⟩ := runA_storeMoveBody_frame (a := 0) (xs := []) zf hpc hB hV
    (by simp [arrAt]) (by simp [arrPts]; trivial)
  exact ⟨q, hq, fun x hx => runA_keep_mem hq (runSafe_storeMoveBody_storeIn zf hpc hB hV) hx⟩

end CatCrypt.Crypto.SecureCompilation.SepLogic.Addr
