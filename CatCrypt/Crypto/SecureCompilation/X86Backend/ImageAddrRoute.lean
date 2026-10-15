/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi

@[expose] public section

set_option autoImplicit false

/-!
# The virtual body of a looped program and its entry states

The register allocation check of a looped program compares the image of its printed body
with a virtual body built from the certified node `seeds ++ loop`: the copies `argBind σ nm`
of the register of each parameter (named by `nm`) into its argument name, the seeds, the
copies of the loop-carried names into their renamed names and the renamed loop. This module
gives the pieces of that virtual body, the renaming `synthRen` the route computes, and the
two entry states the image simulation starts from: the address state `entryA` of a machine
state and the name-keyed state `entryV`, which agree off the frame words and hold the frame
words at the frame names.

## Main definitions

* `srcOf`, `argPairs`, `argBind`: the copies of the parameter registers, or of the caller
  slots `qsave.RSP+off` of stack parameters, into the argument names.
* `ArgSrc`: the sources of the parameters at entry.
* `stackArgB`, `stackReadFreeB`: the stack clauses of the entry check.
* `slotArrOf`: the array, with its length, whose pointer a frame slot holds.
* `synthRen`: the renaming of the loop-carried names synthesised from the virtual body and
  the image.
* `noStoreB`, `fstepF_larr`, `runStraightF_larr`: a straight run without array stores keeps
  the arrays.
* `movesState_same`: copies that write the value their target holds change only the program
  counter.
* `entryA`, `entryV`: the entry states.
* `slotRen`, `unren`: the slot map with renamed array names, and the inverse of a renaming
  on its targets.
* `virtB`, `routeB`: the virtual body and the decided checks of the route.

## Main results

* `entryV_abiEntry`, `argBind_entryV`, `boundFacts_entryV`, `imgRel_entryV`: the entry states
  are an ABI entry, the copies leave them unchanged, the register bounds hold, and they are
  related by the relation of the image simulation.
* `frameE_stack`, `EntryFacts.argSrc`: the caller slot of a stack word is `off` bytes above
  the entry stack pointer, and under `AbiLayout.StackIn` the entry check gives `ArgSrc`.
* `entryB_save`, `imgRel_entryS`: no save reads a stack-argument name, and the entry pair is
  related under the entry check.
* `imgSep_slotRen`: the separation carries over to the renamed slot map.
* `image_route_bytes`: a halting run of the node from `entryV` is matched by a halting run of
  the decoded bytes of the printed body, with the output array in memory at its entry base.
* `resultOf_words`: the read-back of a word-array result.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF fstepF
  runStraightF_cons)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf movesState)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout AbiArg)

/-! ## 1. The copies of the parameter registers -/

/-- **The source name of a parameter** whose register has the name `R`: the caller slot
    `qsave.R` of a stack-argument name `R` (`abiStackOff?`), which the prologue loads, and `R`
    itself otherwise. -/
def srcOf (R : String) : String := if (abiStackOff? R).isSome then slotOfReg R else R

/-- The pairs `(srcOf (nm R), argName j)` of the register `R` of each parameter `j` of `σ`. -/
def argPairs (σ : AbiLayout) (nm : String → String) : List (String × String) :=
  σ.args.mapIdx fun j a => (srcOf (nm a.reg), argName j)

/-- The copies `argName j := srcOf (nm R)` of the register `R` of each parameter `j` of `σ`
    into its argument name. -/
def argBind (σ : AbiLayout) (nm : String → String) : List LinstrRM := movesOf (argPairs σ nm)

/-- The array, with its length, whose pointer the slot `q` holds under the layout `σ` with
    register names `nm`: the word-array parameter `j` whose register `R` has the slot
    `qsave.(nm R)`, under the name `argName j`. -/
def slotArrOf (σ : AbiLayout) (nm : String → String) (q : String) : Option (String × Nat) :=
  match σ.args.findIdx? (fun a => slotOfReg (nm a.reg) == q) with
  | some j =>
      match σ.args[j]? with
      | some ⟨_, _, .words n⟩ => some (argName j, n)
      | _ => none
  | none => none

/-- The names an instruction reads and the registers it writes: the operand names of its
    sources and the base and index of an indexed destination, and its register
    destinations. -/
def rdWr : LinstrR → List String × List String
  | .Lopn ds _ ss =>
      (ss.flatMap JasminLsemExportRewrites.opNames ++
          ds.flatMap (fun | .arrIdx b i _ => [b, i] | _ => []),
        ds.flatMap (fun | .reg d => [d] | _ => []))
  | _ => ([], [])

/-- The names a list of instructions reads before it writes them, in order of first read. -/
def exposed (is : List LinstrR) : List String :=
  (is.foldl (fun (acc : List String × List String) i =>
    let rw := rdWr i
    (acc.1 ++ (rw.1.filter fun x => !acc.2.contains x && !acc.1.contains x).eraseDups,
      acc.2 ++ rw.2)) ([], [])).1

/-- A name that is no frame slot or other dotted name. -/
def plainB (y : String) : Bool := !y.toList.contains '.'

/-- A spill slot `k.N`. -/
def spillB (y : String) : Bool := y.startsWith "k."

/-- **The renaming of the loop-carried names**, synthesised from the virtual body
    `src = pre ++ loop` (with `loop` from index `k0`) and the image `img`: each name the loop
    reads before writing it is paired with a name the image's loop block reads before
    writing it, that is not a name of the loop, holds the same symbolic value at the end of
    the first block, and keeps its start value through the loop block exactly when the loop
    name does; registers before spill slots `k.N` before other dotted names, each image name
    at most once. A name that is both a pointer register and an array base is renamed in both
    roles; the slot map of the image is renamed alongside (`slotRen`). The checks of the route
    (`routeB`) check the result; the pairing carries no trust. -/
def synthRen (src img : List LinstrRM) (k0 : Nat) : List (String × String) :=
  match AllocCheck.LcmdCFG.cfgOf (src.map Prod.fst),
      AllocCheck.LcmdCFG.cfgOf (img.map Prod.fst) with
  | some G, some G' =>
      let R := OwnedLprogTV.runsOf src img G G'
      match R[0]?, R[1]? with
      | some r, some r1 =>
          match r.2.1, r.2.2, r1.2.1, r1.2.2 with
          | .ok ss _, .ok ss' _, .ok ss1 _, .ok ss1' _ =>
              let loopIs := (src.drop k0).map Prod.fst
              let names := loopIs.flatMap JasminLsemExportRewrites.instrNames
              let b' := G'.blk 1
              let ys0 := (exposed (((img.drop b'.start).take (b'.stop - b'.start)).map
                Prod.fst)).filter fun y => !names.contains y
              let ys := ys0.filter plainB ++ ys0.filter (fun y => !plainB y && spillB y)
                ++ ys0.filter fun y => !plainB y && !spillB y
              (exposed loopIs).foldl (fun acc x =>
                match ys.find? (fun y => !acc.any (·.2 == y) && ss'.regs y == ss.regs x
                    && (ss1'.regs y == .reg y) == (ss1.regs x == .reg x)) with
                | some y => acc ++ [(x, y)]
                | none => acc) []
          | _, _, _, _ => []
      | _, _ => []
  | _, _ => []

/-! ## 2. Straight runs without array stores -/

/-- The instruction is no array store and no array zeroing. -/
def noStoreB (i : LinstrRM) : Bool :=
  match i.2 with
  | .store _ _ => false
  | .zero _ _ => false
  | _ => true

theorem fstepF_larr {i : LinstrRM} (hi : noStoreB i = true) {s b : LstateM} {zf z : Bool}
    (h : fstepF i s zf = some (b, z)) : b.larr = s.larr := by
  unfold fstepF at h
  split at h
  · split at h
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); rfl
    · cases h
  · split at h
    · split at h
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); rfl
      · cases h
    · obtain ⟨b', hb', hbe⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, -⟩ := Prod.mk.inj hbe
      unfold stepMemF at hb'
      split at hb'
      · rename_i b1 h1
        obtain rfl := Option.some.inj hb'
        rw [withALUFlags_larr]
        unfold lsemStepMem at h1
        unfold noStoreB at hi
        split at h1
        · split at h1
          · split at h1
            · obtain rfl := Option.some.inj h1; rfl
            · cases h1
          · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h1; rfl
        · rename_i heq; rw [heq] at hi; cases hi
        · split at h1
          · obtain rfl := Option.some.inj h1; rfl
          · cases h1
        · split at h1
          · split at h1
            · obtain rfl := Option.some.inj h1; rfl
            · cases h1
          · cases h1
        · rename_i heq; rw [heq] at hi; cases hi
        · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h1; rfl
      · split at hb'
        · unfold carryStep at hb'
          split at hb'
          · split at hb' <;> (obtain rfl := Option.some.inj hb'; rfl)
          · cases hb'
        · split at hb'
          · unfold wideStep at hb'
            split at hb'
            · split at hb'
              · obtain rfl := Option.some.inj hb'; rfl
              · cases hb'
            · split at hb'
              · obtain rfl := Option.some.inj hb'; rfl
              · cases hb'
          · cases hb'

theorem runStraightF_larr : ∀ {is : List LinstrRM}, is.all noStoreB = true →
    ∀ {s b : LstateM} {zf z : Bool}, runStraightF is s zf = some (b, z) → b.larr = s.larr
  | [], _, s, b, zf, z, h => by
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); rfl
  | i :: is, hall, s, b, zf, z, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [runStraightF_cons] at h
    obtain ⟨bz, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    rw [runStraightF_larr hall.2 h2, fstepF_larr hall.1 h1]

/-! ## 3. Copies that write the value their target holds -/

/-- The copies of `ps` from a base whose every target holds the value of its source change
    the base only at the program counter. -/
theorem movesState_same : ∀ (ps : List (String × String)) (b : LstateM),
    (∀ p ∈ ps, b.reg.lvm p.2 = b.reg.lvm p.1) →
      movesState ps b = { b with reg := { b.reg with lpc := b.reg.lpc + ps.length } }
  | [], b, _ => by simp [movesState]
  | p :: ps, b, h => by
    have hb : (b.setReg p.2 (b.reg.lvm p.1).2).nextPc
        = { b with reg := { b.reg with lpc := b.reg.lpc + 1 } } := by
      have hl : (fun r' => if r' = p.2 then (⟨(b.reg.lvm p.1).1, (b.reg.lvm p.1).2⟩ :
          Σ w, BitVec w) else b.reg.lvm r') = b.reg.lvm := by
        funext r'
        split
        · rename_i hr; subst hr; exact (h p (List.mem_cons_self ..)).symm
        · rfl
      simp only [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hl]
    rw [movesState, hb, movesState_same ps { b with reg := { b.reg with lpc := b.reg.lpc + 1 } }
      (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp only [List.length_cons]
    congr 2
    omega

/-! ## 4. The entry states -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (LstateA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiEntryM abiEntryM
  abiEntryM_spec abiEntryM_lookup)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiBase abiReg abiArgOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgRel cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (IdxFact boundFacts
  boundFacts_holds)

/-- **The address state at entry** of the machine state `sa`: each general-purpose name holds
    its machine register at width `64`, every other name its value in the canonical
    flag-machine entry `abiEntryM`; the memory of `sa`; program counter `0`. -/
def entryA (σ : AbiLayout) (sa : AState) : LstateA where
  reg :=
    { lvm := fun r => if gpOk r then ⟨64, sa.regs (phys r)⟩ else (abiEntryM σ sa).reg.lvm r
      lpc := 0 }
  mem := sa.mem

/-- **The name-keyed state at entry** of the machine state `sa` under the frame map `fr` and
    the name map `un`: a name with a frame word holds the word at it, every other name its
    value in `entryA`; the name `x` holds the array of `abiEntryM` at `un x`; program counter
    `0`. -/
def entryV (σ : AbiLayout) (fr : String → Option (BitVec 64)) (sa : AState)
    (un : String → String) : LstateM where
  reg :=
    { lvm := fun r => match fr r with
        | some a => ⟨64, read64 sa.mem a⟩
        | none => (entryA σ sa).reg.lvm r
      lpc := 0 }
  larr := fun x => (abiEntryM σ sa).larr (un x)

theorem abiArgOf_argName {σ : AbiLayout} {j : Nat} {a : AbiArg} (h : σ.args[j]? = some a) :
    abiArgOf σ (argName j) = some a :=
  abiEntryM_lookup h

theorem abiBase_argName {σ : AbiLayout} {j : Nat} {a : AbiArg} (h : σ.args[j]? = some a)
    (sa : AState) : abiBase (abiReg σ) sa (argName j) = sa.regs a.reg := by
  simp [abiBase, abiReg, abiArgOf_argName h]

/-- The register of an argument name in `entryV`, when the name has no frame word and is no
    general-purpose name. -/
theorem entryV_argName {σ : AbiLayout} {fr : String → Option (BitVec 64)} {sa : AState}
    {un : String → String} {j : Nat} {a : AbiArg} (h : σ.args[j]? = some a)
    (hF : fr (argName j) = none) (hG : gpOk (argName j) = false) :
    (entryV σ fr sa un).reg.lvm (argName j) = ⟨64, sa.regs a.reg⟩ := by
  simp only [entryV, entryA, hF, hG, abiEntryM, abiEntryM_lookup h]
  rfl

/-- `entryV` is an ABI entry of the flag machine when no argument name has a frame word or
    is a general-purpose name, and `un` fixes the argument names. -/
theorem entryV_abiEntry {σ : AbiLayout} {fr : String → Option (BitVec 64)} {sa : AState}
    {un : String → String}
    (hF : ∀ j, j < σ.args.length → fr (argName j) = none)
    (hG : ∀ j, j < σ.args.length → gpOk (argName j) = false)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) :
    AbiEntryM σ sa (entryV σ fr sa un) where
  pc := rfl
  reg := fun j a h => by
    have hj := (List.getElem?_eq_some_iff.mp h).1
    unfold LstateN.getW
    rw [entryV_argName h (hF j hj) (hG j hj)]
    simp
  arr := fun j a n h hk => by
    have hj := (List.getElem?_eq_some_iff.mp h).1
    have he : (entryV σ fr sa un).getArr (argName j) 64 n
        = (abiEntryM σ sa).getArr (argName j) 64 n :=
      JasminLsemExportCanon.getArr_congr_cell (show (abiEntryM σ sa).larr (un (argName j)) = _
        by rw [hU j hj]) 64 n
    rw [he]
    exact (abiEntryM_spec σ sa).arr j a n h hk

/-- **The sources of the parameters at entry** under the frame map `fr` at the machine state
    `sa`: the register of each parameter is named by a general-purpose name of that machine
    register without a frame word, or by a stack-argument name (`abiStackOff?`) whose caller
    slot has a frame word that holds the entry value of the parameter. -/
def ArgSrc (σ : AbiLayout) (nm : String → String) (fr : String → Option (BitVec 64))
    (sa : AState) : Prop :=
  ∀ a ∈ σ.args, (gpOk (nm a.reg) = true ∧ phys (nm a.reg) = a.reg ∧ fr (nm a.reg) = none)
    ∨ ((abiStackOff? (nm a.reg)).isSome = true
      ∧ ∃ w, fr (slotOfReg (nm a.reg)) = some w ∧ read64 sa.mem w = sa.regs a.reg)

theorem srcOf_of_gpOk {R : String} (h : gpOk R = true) : srcOf R = R := by
  simp [srcOf, ImageAddrSim.abiStackOff?_of_gpOk h]

theorem srcOf_of_stack {R : String} (h : (abiStackOff? R).isSome = true) :
    srcOf R = slotOfReg R := by
  simp [srcOf, h]

/-- Parameters named by general-purpose names without a frame word have their sources. -/
theorem ArgSrc.of_gp {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState}
    (h : ∀ a ∈ σ.args, gpOk (nm a.reg) = true ∧ phys (nm a.reg) = a.reg ∧ fr (nm a.reg) = none) :
    ArgSrc σ nm fr sa :=
  fun a ha => Or.inl (h a ha)

/-- The sources carry over to a frame map that agrees on the general-purpose names and on the
    slots `qsave.R`. -/
theorem ArgSrc.congr {σ : AbiLayout} {nm : String → String}
    {fr fr' : String → Option (BitVec 64)} {sa : AState} (h : ArgSrc σ nm fr sa)
    (hg : ∀ x, gpOk x = true → fr' x = fr x) (hs : ∀ R, fr' (slotOfReg R) = fr (slotOfReg R)) :
    ArgSrc σ nm fr' sa := by
  intro a ha
  rcases h a ha with ⟨h1, h2, h3⟩ | ⟨h1, w, hw, hv⟩
  · exact Or.inl ⟨h1, h2, by rw [hg _ h1, h3]⟩
  · exact Or.inr ⟨h1, w, by rw [hs, hw], hv⟩

/-- The source name of a parameter holds the entry value of the parameter in `entryV`. -/
theorem entryV_srcOf {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState} {un : String → String}
    (hR : ArgSrc σ nm fr sa) {a : AbiArg} (ha : a ∈ σ.args) :
    (entryV σ fr sa un).reg.lvm (srcOf (nm a.reg)) = ⟨64, sa.regs a.reg⟩ := by
  rcases hR a ha with ⟨h1, h2, h3⟩ | ⟨h1, w, hw, hv⟩
  · rw [srcOf_of_gpOk h1]
    simp only [entryV, entryA, h3, h1, if_true, h2]
  · rw [srcOf_of_stack h1]
    simp only [entryV, hw, hv]

/-- **The copies of the parameter registers leave `entryV` unchanged** but for the program
    counter, when each parameter has its source (`ArgSrc`). -/
theorem argBind_entryV {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState} {un : String → String}
    (hF : ∀ j, j < σ.args.length → fr (argName j) = none)
    (hG : ∀ j, j < σ.args.length → gpOk (argName j) = false)
    (hR : ArgSrc σ nm fr sa) (zf : Bool) :
    runStraightF (argBind σ nm) (entryV σ fr sa un) zf
      = some ({ entryV σ fr sa un with reg := { (entryV σ fr sa un).reg with
          lpc := σ.args.length } }, zf) := by
  unfold argBind
  rw [JasminLsemRenameLoop.runStraightF_movesOf, movesState_same]
  · simp [argPairs, entryV]
  · intro p hp
    simp only [argPairs, List.mem_mapIdx] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    have ha : σ.args[j]? = some σ.args[j] := List.getElem?_eq_getElem hj
    rw [entryV_argName ha (hF j hj) (hG j hj), entryV_srcOf hR (List.getElem_mem hj)]

/-- The register bounds of `σ` hold at `entryV` at the names `nm`, at every array state,
    when each bounded register is named by a general-purpose name of that machine register
    without a frame word. -/
theorem boundFacts_entryV {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState} {un : String → String}
    (hreg : σ.Regions sa)
    (hB : ∀ b ∈ σ.bounds, gpOk (nm b.1) = true ∧ phys (nm b.1) = b.1 ∧ fr (nm b.1) = none) :
    ∀ (A : String → ArrCell), ∀ f ∈ boundFacts σ nm, f.holds (entryV σ fr sa un).reg.lvm A :=
  fun _ => boundFacts_holds hreg fun b hb => by
    obtain ⟨h1, h2, h3⟩ := hB b hb
    simp only [entryV, entryA, h3, h1, if_true, h2]

/-- A slot of `slotArrOf`: the parameter whose register it saves, an array of the slot's
    length under its argument name. -/
theorem slotArrOf_some {σ : AbiLayout} {nm : String → String} {q A : String} {n : Nat}
    (h : slotArrOf σ nm q = some (A, n)) :
    ∃ j a, σ.args[j]? = some a ∧ a.kind = .words n ∧ A = argName j
      ∧ slotOfReg (nm a.reg) = q := by
  unfold slotArrOf at h
  split at h
  · rename_i j hj
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
    have hg : σ.args[j]? = some σ.args[j] := List.getElem?_eq_getElem hlt
    rw [hg] at h
    split at h
    · rename_i nm' r' n' he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨j, σ.args[j], hg, by rw [Option.some.inj he], rfl, ?_⟩
      simpa using hp
    · cases h
  · cases h

/-- The slot map `sl` with its array names renamed by `ren`. -/
def slotRen (sl : String → Option (String × Nat)) (ren : String → String) (q : String) :
    Option (String × Nat) :=
  (sl q).map fun p => (ren p.1, p.2)

theorem slotRen_some {sl : String → Option (String × Nat)} {ren : String → String}
    {q A' : String} {n : Nat} (h : slotRen sl ren q = some (A', n)) :
    ∃ A, sl q = some (A, n) ∧ A' = ren A := by
  unfold slotRen at h
  obtain ⟨⟨A, m⟩, hA, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨A, hA, rfl⟩

/-- **The separation under a renaming of the array names.** A separation of the slot map `sl`
    at the bases `base` is a separation of the renamed slot map at the bases `base ∘ un`, when
    `un` undoes the renaming on the array names of `sl`. -/
theorem imgSep_slotRen {fr : String → Option (BitVec 64)} {sl : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64} {ren un : String → String}
    (h : ImageAddrSim.ImgSep fr sl base rsp)
    (hun : ∀ q A n, sl q = some (A, n) → un (ren A) = A) :
    ImageAddrSim.ImgSep fr (slotRen sl ren) (fun A => base (un A)) rsp := by
  refine ⟨h.frames, fun q A' n j hq hj q' a ha => ?_, fun q A' n q' B' n' j j' hq hq' hj hj' hne => ?_,
    fun q q' A' n n' hq hq' => ?_, fun q A' n j hq hj => ?_, h.gp, fun q A' n hq => ?_⟩
  · obtain ⟨A, hA, rfl⟩ := slotRen_some hq
    rw [hun q A n hA]
    exact h.cellFrame q A n j hA hj q' a ha
  · obtain ⟨A, hA, rfl⟩ := slotRen_some hq
    obtain ⟨B, hB, rfl⟩ := slotRen_some hq'
    rw [hun q A n hA, hun q' B n' hB]
    refine h.cells q A n q' B n' j j' hA hB hj hj' ?_
    rcases hne with hne | hne
    · exact Or.inl fun he => hne (by rw [he])
    · exact Or.inr hne
  · obtain ⟨A, hA, he⟩ := slotRen_some hq
    obtain ⟨B, hB, he'⟩ := slotRen_some hq'
    have hAB : A = B := by rw [← hun q A n hA, ← hun q' B n' hB, ← he, ← he']
    subst hAB
    exact h.len q q' A n n' hA hB
  · obtain ⟨A, hA, rfl⟩ := slotRen_some hq
    rw [hun q A n hA]
    exact h.red q A n j hA hj
  · obtain ⟨A, hA, -⟩ := slotRen_some hq
    exact h.slotFrame q A n hA

/-- **The entry pair is related.** `entryV` at the name map `un` and `entryA` are related by
    the relation of the image simulation at the frame map `fr`, the slots of `slotArrOf σ nm`
    with their array names renamed by `ren`, and the entry bases of the parameters at the
    names `un` gives, when `un` undoes `ren` on the argument names of the array parameters,
    each parameter has its source (`ArgSrc`), and no save of the body reads a stack-argument
    name. -/
theorem imgRel_entryV {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState} {body : Lcmd} {fn : String}
    {ren un : String → String}
    (hS : ArgSrc σ nm fr sa)
    (hsv : ∀ k R, ImageAddrSim.SaveAt body k R → abiStackOff? R = none)
    (hUR : ∀ j, j < σ.args.length → un (ren (argName j)) = argName j) :
    ImgRel fr (slotRen (slotArrOf σ nm) ren) (fun A => abiBase (abiReg σ) sa (un A)) body
      { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } (entryA σ sa)
      false := by
  refine ImageAddrFrame.imgRel_entry rfl rfl (fun r h => ?_) (fun q a h => ?_) rfl rfl rfl
    (fun r h => ?_) (fun q A n h => ?_) (fun k R A n hs h => ?_) (fun R A n w hR h hw => ?_)
  · simp [entryV, h]
  · simp [entryV, entryA, h]
  · simp [entryA, h]
  · obtain ⟨A0, h0, rfl⟩ := slotRen_some h
    obtain ⟨j, a, hj, hk, rfl, -⟩ := slotArrOf_some h0
    have hu := hUR j (List.getElem?_eq_some_iff.mp hj).1
    have he : (entryV σ fr sa un).getArr (ren (argName j)) 64 n
        = (abiEntryM σ sa).getArr (argName j) 64 n :=
      JasminLsemExportCanon.getArr_congr_cell
        (show (abiEntryM σ sa).larr (un (ren (argName j))) = _ by rw [hu]) 64 n
    show (entryV σ fr sa un).getArr (ren (argName j)) 64 n = _
    rw [he, hu, abiBase_argName hj]
    exact (abiEntryM_spec σ sa).arr j a n hj hk
  · have hgR := hsv k R hs
    obtain ⟨A0, h0, rfl⟩ := slotRen_some h
    obtain ⟨j, a, hj, -, rfl, hq⟩ := slotArrOf_some h0
    have hu := hUR j (List.getElem?_eq_some_iff.mp hj).1
    have hR : nm a.reg = R := by simpa [slotOfReg] using hq
    rcases hS a (List.mem_of_getElem? hj) with ⟨h1, h2, -⟩ | ⟨h1, -⟩
    · have hl : (entryA σ sa).reg.lvm (nm a.reg) = ⟨64, sa.regs a.reg⟩ := by
        simp only [entryA, h1, if_true, h2]
      show _ = some (abiBase (abiReg σ) sa (un (ren (argName j))))
      rw [hu, abiBase_argName hj, ← hR]
      unfold LstateN.getW
      rw [hl]
      simp
    · rw [hR, hgR] at h1
      cases h1
  · obtain ⟨A0, h0, rfl⟩ := slotRen_some h
    obtain ⟨j, a, hj, -, rfl, hq⟩ := slotArrOf_some h0
    have hu := hUR j (List.getElem?_eq_some_iff.mp hj).1
    have hR' : nm a.reg = R := by simpa [slotOfReg] using hq
    rcases hS a (List.mem_of_getElem? hj) with ⟨h1, -, -⟩ | ⟨-, w', hw', hv⟩
    · rw [← hR', ImageAddrSim.abiStackOff?_of_gpOk h1] at hR
      cases hR
    · rw [hR', hw] at hw'
      cases hw'
      show read64 sa.mem w = abiBase (abiReg σ) sa (un (ren (argName j)))
      rw [hu, abiBase_argName hj]
      exact hv

/-! ## 5. The checks of the route -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames RenOn CondOK
  mulxFree)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (clsB fuseMulHiRM fuseOKL
  fuseLoPre KeptN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (abiArgNames e64_of_abiEntryM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (argIdxOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp printedAddrB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (rsOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn frameNames frameMark
  frameMark_isSome frameOkB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (imgGateB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot)

theorem clsB_ctl_cond {i : LinstrRM} (h : clsB i = true) (hm : mulxFree i = true) :
    CtlOK i ∧ CondOK i := by
  unfold clsB at h
  refine ⟨?_, fun c l he => ?_, hm⟩
  · split at h
    · exact Or.inl ⟨_, _, _, by assumption⟩
    · exact Or.inr (Or.inl ⟨_, _, by assumption⟩)
    · rename_i c l he
      exact Or.inr (Or.inr (Or.inl ⟨c, l, he, Option.isSome_iff_ne_none.mp h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨_, by assumption⟩))
    · cases h
  · rw [he] at h
    exact Option.isSome_iff_ne_none.mp h

/-- The frame map of a printed body at the entry machine state `sa`: the frame words of the
    names of the body, from the stack pointer after the prologue. -/
abbrev frameE (body : Lcmd) (sa : AState) : String → Option (BitVec 64) :=
  frameIn body (frameP (Params.ofBody body) (frameRsp body sa))

/-- The names of a loop, with the empty name. -/
def loopNames (loop : List LinstrRM) : List String :=
  "" :: loop.flatMap fun i => instrNames i.1

/-- The renamed loop, fused when `fuse` holds. -/
def loopOf (loop : List LinstrRM) (ps : List (String × String)) (fuse : Bool) :
    List LinstrRM :=
  if fuse then fuseMulHiRM (loop.map (renRM (renOf ps))) else loop.map (renRM (renOf ps))

/-- **The virtual body**: the copies of the parameter registers, the seeds, the copies of the
    loop-carried names into their renamed names and the renamed loop, fused when `fuse`
    holds. -/
def virtB (σ : AbiLayout) (nm : String → String) (seeds loop : List LinstrRM)
    (ps : List (String × String)) (fuse : Bool) : List LinstrRM :=
  argBind σ nm ++ seeds ++ movesOf ps ++ loopOf loop ps fuse

/-- The inverse of the renaming `renOf ps` on its targets: a target `y` to the source of its
    first pair, the identity off the targets. -/
def unren (ps : List (String × String)) (y : String) : String :=
  ((ps.find? (·.2 == y)).map (·.1)).getD y

theorem unren_of_not_target {ps : List (String × String)} {y : String}
    (h : ∀ q ∈ ps, q.2 ≠ y) : unren ps y = y := by
  unfold unren
  rw [List.find?_eq_none.mpr (fun q hq => by simpa using h q hq)]
  rfl

theorem unren_target {ps : List (String × String)} (hnd : (ps.map Prod.snd).Nodup)
    {p : String × String} (hp : p ∈ ps) : unren ps p.2 = p.1 := by
  unfold unren
  cases hf : ps.find? (·.2 == p.2) with
  | none => exact absurd (List.find?_eq_none.mp hf p hp) (by simp)
  | some q =>
      have hq := List.mem_of_find?_eq_some hf
      have he : q.2 = p.2 := by simpa using List.find?_some hf
      have := List.inj_on_of_nodup_map hnd hq hp he
      subst this
      rfl

/-- The regions of the array parameters of `σ`, under their argument names. -/
def rsOf (σ : AbiLayout) : List Region :=
  (List.range σ.args.length).filterMap fun j =>
    match σ.args[j]? with
    | some a => match a.kind with
      | .words n => some ⟨argName j, n, 0⟩
      | .scalar => none
    | none => none

/-- The map of the renaming `renOf ps`: each source to the target of its first pair. -/
def renMapOf (ps : List (String × String)) : Std.HashMap String String :=
  ps.foldr (fun p m => m.insert p.1 p.2) {}

/-- The renaming of the map `m`: a key to its value, the identity off the keys. -/
def renOfH (m : Std.HashMap String String) (n : String) : String := m.getD n n

/-- **The renaming through its map is `renOf`.** -/
theorem renOfH_eq (ps : List (String × String)) (n : String) :
    renOfH (renMapOf ps) n = renOf ps n := by
  induction ps with
  | nil => simp [renOfH, renMapOf, renOf]
  | cons p ps ih =>
      simp only [renOfH, renMapOf, List.foldr_cons, Std.HashMap.getD_insert] at ih ⊢
      rw [ih]
      unfold renOf
      by_cases h : p.1 = n <;> simp [h]

/-- One step of the injectivity fold at the name `a`: the image map from `f a` to `a`, or
    `none` once two distinct names share an image. -/
def injHashStep (f : String → String) (acc : Option (Std.HashMap String String))
    (a : String) : Option (Std.HashMap String String) :=
  acc.bind fun m => match m[f a]? with
    | some b => if b == a then some m else none
    | none => some (m.insert (f a) a)

/-- **Injectivity of `f` on the names `Ns`**, by a fold of the image map. -/
def injHashB (f : String → String) (Ns : List String) : Bool :=
  (Ns.foldl (injHashStep f) (some {})).isSome

/-- The image map of the injectivity fold sends the image of each name folded to the name. -/
theorem injHash_fold (f : String → String) : ∀ (Ns P : List String)
    (acc : Option (Std.HashMap String String)),
    (∀ m, acc = some m → ∀ a ∈ P, m[f a]? = some a) →
    ∀ m, Ns.foldl (injHashStep f) acc = some m → ∀ a ∈ P ++ Ns, m[f a]? = some a
  | [], P, acc, h, m, hm => by simpa using h m hm
  | x :: Ns, P, acc, h, m, hm => by
      rw [List.foldl_cons] at hm
      have := injHash_fold f Ns (P ++ [x]) _ ?_ m hm
      · simpa using this
      intro m' hm' a ha
      cases acc with
      | none => simp [injHashStep] at hm'
      | some m0 =>
        have h0 := h m0 rfl
        simp only [injHashStep, Option.bind_some] at hm'
        split at hm'
        · split at hm'
          · cases hm'
            rcases List.mem_append.mp ha with ha | ha
            · exact h0 a ha
            · simp at ha; subst ha; simp_all
          · cases hm'
        · cases hm'
          rw [Std.HashMap.getElem?_insert]
          rcases List.mem_append.mp ha with ha | ha
          · have h1 := h0 a ha
            split
            · rename_i he
              have : f x = f a := by simpa using he
              rw [← this] at h1; simp_all
            · exact h1
          · simp at ha; subst ha; simp

/-- **The injectivity fold decides injectivity**: if `injHashB f Ns` accepts, `f` is
    injective on the members of `Ns`. -/
theorem injHashB_spec {f : String → String} {Ns : List String} (h : injHashB f Ns = true) :
    ∀ a ∈ Ns, ∀ b ∈ Ns, f a = f b → a = b := by
  unfold injHashB at h
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
  have H := injHash_fold f Ns [] (some {}) (by simp) m hm
  intro a ha b hb he
  have h1 := H a (by simpa using ha)
  have h2 := H b (by simpa using hb)
  rw [he, h2] at h1
  exact (Option.some.inj h1).symm

/-- **The renaming check**: the seeds are `Lopn`s, the loop is in the covered classes and
    reads no implicit register, the renaming is injective on the names of the loop and fixes
    the empty name, its targets are distinct, no source and not names of the loop, it sends
    each source to its target, the copies and seeds store no array, and `unren ps` fixes each
    argument name and undoes the renaming on it. -/
def renB (σ : AbiLayout) (nm : String → String) (seeds loop : List LinstrRM)
    (ps : List (String × String)) : Bool :=
  let Ns := loopNames loop
  let S : Std.HashSet String := Std.HashSet.ofList Ns
  let r := renOfH (renMapOf ps)
  seeds.all isLopnB && loop.all (fun i => clsB i && mulxFree i)
    && injHashB r Ns
    && r "" == ""
    && decide ((ps.map Prod.snd).Nodup) && ps.all (fun p => ps.all fun q => q.2 != p.1)
    && ps.all (fun p => r p.1 == p.2) && ps.all (fun p => !S.contains p.2)
    && (argBind σ nm ++ seeds).all noStoreB
    && (List.range σ.args.length).all (fun j => unren ps (argName j) == argName j
      && unren ps (renOf ps (argName j)) == argName j)

/-- No move of `body` reads a stack-argument name (`abiStackOff?`): the caller's stack words
    are read through their slots `qsave.RSP+off` only. -/
def stackReadFreeB (body : Lcmd) : Bool :=
  body.all fun i => match JasminLsemAddrMem.slotMov? i.li_i with
    | some (_, s) => (abiStackOff? s).isNone
    | none => true

/-- No save of a body that passes `stackReadFreeB` reads a stack-argument name. -/
theorem stackReadFreeB_save {body : Lcmd} (h : stackReadFreeB body = true) {k : Nat}
    {R : String} (hs : ImageAddrSim.SaveAt body k R) : abiStackOff? R = none := by
  obtain ⟨i, hi, hm⟩ := hs
  have := List.all_eq_true.mp h i (List.mem_of_getElem? hi)
  rw [hm] at this
  simpa using this

/-- **The stack clause of the entry check** for the parameter `a` under the frame map `fm`:
    the register of `a` is the carrier name `%rsp+off` of a stack word, `off` a multiple of
    `8`, named by the stack-argument name `RSP+off`, whose caller slot has a frame word. -/
def stackArgB (nm : String → String) (fm : String → Option (BitVec 64)) (a : AbiArg) : Bool :=
  match abiStackOff? (nm a.reg) with
  | some off => off % 8 == 0 && a.reg == "%rsp+" ++ toString off
      && nm a.reg == "RSP+" ++ toString off && (fm (slotOfReg (nm a.reg))).isSome
  | none => false

theorem stackArgB_spec {nm : String → String} {fm : String → Option (BitVec 64)} {a : AbiArg}
    (h : stackArgB nm fm a = true) :
    ∃ k, a.reg = Haxc.stackArgReg k ∧ nm a.reg = "RSP+" ++ toString (8 * k)
      ∧ (fm (slotOfReg (nm a.reg))).isSome = true := by
  unfold stackArgB at h
  split at h
  · rename_i off _
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h8, h1⟩, h2⟩, h3⟩ := h
    have hk : 8 * (off / 8) = off := by omega
    exact ⟨off / 8, by rw [Haxc.stackArgReg, hk, h1], by rw [hk, h2], h3⟩
  · cases h

/-- **The entry check**: no argument name is a general-purpose name or has a frame word; the
    register of each parameter is named by a general-purpose name of that machine register
    without a frame word or passes the stack clause `stackArgB`; each bounded register is
    named by a general-purpose name of that machine register without a frame word; the slot
    of each array parameter has a frame word; no move of the body reads a stack-argument
    name. -/
def entryB (σ : AbiLayout) (nm : String → String) (body : Lcmd) : Bool :=
  let fm := frameMark (frameNames body)
  (List.range σ.args.length).all (fun j => !gpOk (argName j) && (fm (argName j)).isNone)
    && σ.args.all (fun a => (gpOk (nm a.reg) && phys (nm a.reg) == a.reg
      && (fm (nm a.reg)).isNone) || stackArgB nm fm a)
    && σ.bounds.all (fun b => gpOk (nm b.1) && phys (nm b.1) == b.1 && (fm (nm b.1)).isNone)
    && σ.args.all (fun a => match a.kind with
      | .words _ => (fm (slotOfReg (nm a.reg))).isSome
      | .scalar => true)
    && rsOK σ (rsOf σ)
    && (List.range σ.args.length).all (fun j => match σ.args[j]? with
      | some a => match a.kind with
        | .words n => regLen (rsOf σ) (argName j) == n
        | .scalar => true
      | none => true)
    && stackReadFreeB body

/-- The names the fusion check reads at width `64` at entry: the argument names and the
    source names (`srcOf`) of the parameter registers. -/
def fuseRegs (σ : AbiLayout) (nm : String → String) : List String :=
  abiArgNames σ ++ σ.args.map fun a => srcOf (nm a.reg)

/-- **The check of the image route** of the node `seeds ++ loop` with the renaming `ps`, the
    fusion flag `fuse` and the output array `out`, against the printed body `body`: the
    register allocation check `ownedCheckMC` of the virtual body against the image of the
    printed body, the bounds invariant of the virtual body from the register bounds, the
    printed body in the covered class and the image class, the gate of the image simulation,
    the frame check, the entry check, the renaming check, the fusion check when `fuse` holds,
    and the output array a name of the loop that the renaming fixes. -/
def routeB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (seeds loop : List LinstrRM)
    (ps : List (String × String)) (fuse : Bool) (out : String) : Bool :=
  let B := virtB σ nm seeds loop ps fuse
  let pre := argBind σ nm ++ seeds ++ movesOf ps
  let L := loop.map (renRM (renOf ps))
  let sl := slotRen (slotArrOf σ nm) (renOf ps)
  ownedCheckMC [] B (virtImg sl body)
    && idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B
    && printedAddrB body && physImgB sl body
    && imgGateB (frameMark (frameNames body)) sl body
    && frameOkB σ body && entryB σ nm body && renB σ nm seeds loop ps
    && (!fuse || (fuseOKL (fuseRegs σ nm) (fuseLoPre pre L) (pre ++ L)
      && renOf ps out != "R15"))
    && (loopNames loop).contains out

/-! ## 6. The checks discharge the hypotheses of the image route -/

theorem frameE_none {body : Lcmd} (sa : AState) {x : String}
    (h : (frameMark (frameNames body) x).isNone = true) : frameE body sa x = none := by
  have he := frameMark_isSome body (frameRsp body sa) x
  rw [Option.isNone_iff_eq_none.mp h] at he
  show frameIn body (frameP (Params.ofBody body) (frameRsp body sa)) x = none
  cases hfr : frameIn body (frameP (Params.ofBody body) (frameRsp body sa)) x with
  | none => rfl
  | some v => rw [hfr] at he; simp at he

theorem frameE_some {body : Lcmd} (sa : AState) {x : String}
    (h : (frameMark (frameNames body) x).isSome = true) : ∃ a, frameE body sa x = some a := by
  rw [frameMark_isSome body (frameRsp body sa) x] at h
  exact Option.isSome_iff_exists.mp h

/-- The facts the entry check decides. -/
structure EntryFacts (σ : AbiLayout) (nm : String → String) (fr : String → Option (BitVec 64)) :
    Prop where
  argF : ∀ j, j < σ.args.length → fr (argName j) = none
  argG : ∀ j, j < σ.args.length → gpOk (argName j) = false
  regs : ∀ a ∈ σ.args, (gpOk (nm a.reg) = true ∧ phys (nm a.reg) = a.reg ∧ fr (nm a.reg) = none)
    ∨ ∃ k, a.reg = Haxc.stackArgReg k ∧ nm a.reg = "RSP+" ++ toString (8 * k)
      ∧ (fr (slotOfReg (nm a.reg))).isSome = true
  bnds : ∀ b ∈ σ.bounds, gpOk (nm b.1) = true ∧ phys (nm b.1) = b.1 ∧ fr (nm b.1) = none
  slot : ∀ q A n, slotArrOf σ nm q = some (A, n) → ∃ a, fr q = some a
  rs : rsOK σ (rsOf σ) = true
  len : ∀ q A n, slotArrOf σ nm q = some (A, n) → regLen (rsOf σ) A = n

theorem entryB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    (h : entryB σ nm body = true) (sa : AState) : EntryFacts σ nm (frameE body sa) := by
  simp only [entryB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩ := h
  refine ⟨fun j hj => frameE_none sa (h1 j hj).2, fun j hj => (h1 j hj).1,
    fun a ha => ?_,
    fun b hb => ⟨(h3 b hb).1.1, (h3 b hb).1.2, frameE_none sa (h3 b hb).2⟩,
    fun q A n hq => ?_, h5, fun q A n hq => ?_⟩
  · rcases Bool.or_eq_true_iff.mp (h2 a ha) with h | h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact Or.inl ⟨h.1.1, h.1.2, frameE_none sa h.2⟩
    · obtain ⟨k, hk, hn, hs⟩ := stackArgB_spec h
      obtain ⟨w, hw⟩ := frameE_some sa hs
      exact Or.inr ⟨k, hk, hn, by rw [hw]; rfl⟩
  · obtain ⟨j, a, hj, hk, rfl, rfl⟩ := slotArrOf_some hq
    have := h4 a (List.mem_of_getElem? hj)
    rw [hk] at this
    exact frameE_some sa this
  · obtain ⟨j, a, hj, hk, rfl, -⟩ := slotArrOf_some hq
    have := h6 j (List.getElem?_eq_some_iff.mp hj).1
    rw [hj] at this
    simp only [hk, beq_iff_eq] at this
    exact this

/-- No save of a body that passes the entry check reads a stack-argument name. -/
theorem entryB_save {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    (h : entryB σ nm body = true) {k : Nat} {R : String} (hs : ImageAddrSim.SaveAt body k R) :
    abiStackOff? R = none := by
  simp only [entryB, Bool.and_eq_true] at h
  exact stackReadFreeB_save h.2 hs

/-- **The entry pair is related under the entry check**: `imgRel_entryV` for a printed body
    that passes `entryB`. -/
theorem imgRel_entryS {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState} {body : Lcmd} {fn : String}
    {ren un : String → String}
    (hS : ArgSrc σ nm fr sa) (hent : entryB σ nm body = true)
    (hUR : ∀ j, j < σ.args.length → un (ren (argName j)) = argName j) :
    ImgRel fr (slotRen (slotArrOf σ nm) ren) (fun A => abiBase (abiReg σ) sa (un A)) body
      { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } (entryA σ sa)
      false :=
  imgRel_entryV hS (fun _ _ hs => entryB_save hent hs) hUR

/-- The caller slot `qsave.RSP+off` is `off` bytes above a frame of any shape. -/
theorem spillQsaveOff_rsp (F W Q off : Nat) :
    LprogBytes.spillQsaveOff F W (slotOfReg ("RSP+" ++ toString off)) Q
      = some (Int.ofNat F + Int.ofNat off) := by
  unfold LprogBytes.spillQsaveOff
  have h1 : hasPrefix (slotOfReg ("RSP+" ++ toString off)) "k." = false := by
    simp [hasPrefix, slotOfReg, List.isPrefixOf]
  have h2 : hasPrefix (slotOfReg ("RSP+" ++ toString off)) "qsave." = true := by
    simp [hasPrefix, slotOfReg]
  have h3 : String.ofList ((slotOfReg ("RSP+" ++ toString off)).toList.drop 6)
      = "RSP+" ++ toString off := by
    rw [slotOfReg, String.toList_append, show (6 : Nat) = "qsave.".toList.length from rfl,
      List.drop_left, String.ofList_toList]
  rw [if_neg (by rw [h1]; exact Bool.false_ne_true), if_pos h2, h3,
    LprogAsmPrinter.qsaveFrameOff_rsp]

/-- **The caller slot of a stack word at entry**: the frame word of the caller slot
    `qsave.RSP+off`, when it has one, is the word `off` bytes above the entry stack
    pointer. -/
theorem frameE_stack {body : Lcmd} (sa : AState) (off : Nat)
    (h : (frameE body sa (slotOfReg ("RSP+" ++ toString off))).isSome = true) :
    frameE body sa (slotOfReg ("RSP+" ++ toString off))
      = some (sa.regs "%rsp" + BitVec.ofNat 64 off) := by
  have hq : slotOfReg ("RSP+" ++ toString off) ∈ ImageAddrFrame.bodyNamesI body := by
    by_contra hn
    rw [show frameE body sa (slotOfReg ("RSP+" ++ toString off)) = none from if_neg hn] at h
    cases h
  show ImageAddrFrame.frameIn body _ _ = _
  rw [ImageAddrFrame.frameIn, if_pos hq, frameP, spillQsaveOff_rsp, Option.map_some,
    frameRsp]
  congr 1
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp
  omega

/-- **The sources of the parameters from the entry check**: under the entry facts at the frame
    of the printed body and the stack parameters at entry (`AbiLayout.StackIn`), each parameter
    has its source. -/
theorem EntryFacts.argSrc {σ : AbiLayout} {nm : String → String} {body : Lcmd} {sa : AState}
    (E : EntryFacts σ nm (frameE body sa)) (hst : σ.StackIn sa) :
    ArgSrc σ nm (frameE body sa) sa := by
  intro a ha
  rcases E.regs a ha with h | ⟨k, hk, hn, hs⟩
  · exact Or.inl h
  · rw [hn] at hs ⊢
    refine Or.inr ⟨by rw [abiStackOff?_rsp]; rfl, _, frameE_stack sa _ hs, ?_⟩
    exact (hst a ha k hk).symm

/-- The facts the renaming check decides, for the names `N` of the loop. -/
structure RenFacts (σ : AbiLayout) (nm : String → String) (seeds loop : List LinstrRM)
    (ps : List (String × String)) : Prop where
  lopn : ∀ i ∈ seeds, IsLopn i
  ctl : ∀ i ∈ loop, CtlOK i
  cond : ∀ i ∈ loop, CondOK i
  ren : RenOn (renOf ps) (· ∈ loopNames loop)
  names : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, n ∈ loopNames loop
  nd : (ps.map Prod.snd).Nodup
  ts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1
  tgt : ∀ p ∈ ps, renOf ps p.1 = p.2
  fresh : ∀ p ∈ ps, ¬ p.2 ∈ loopNames loop
  store : (argBind σ nm ++ seeds).all noStoreB = true
  unr : ∀ j, j < σ.args.length → unren ps (argName j) = argName j
    ∧ unren ps (renOf ps (argName j)) = argName j

theorem renB_spec {σ : AbiLayout} {nm : String → String} {seeds loop : List LinstrRM}
    {ps : List (String × String)} (h : renB σ nm seeds loop ps = true) :
    RenFacts σ nm seeds loop ps := by
  have hr : renOfH (renMapOf ps) = renOf ps := funext (renOfH_eq ps)
  simp only [renB, hr, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, Bool.not_eq_true', Std.HashSet.contains_ofList, List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨fun i hi => isLopnB_isLopn (h1 i hi), fun i hi => (clsB_ctl_cond (h2 i hi).1
    (h2 i hi).2).1, fun i hi => (clsB_ctl_cond (h2 i hi).1 (h2 i hi).2).2,
    ⟨fun a b ha hb he => injHashB_spec h3 a ha b hb he, List.mem_cons_self .., h4⟩,
    fun i hi n hn => ?_, h5, h6, h7, h8, ?_, fun j hj => h10 j (List.mem_range.mpr hj)⟩
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, hi, hn⟩)
  · simpa only [List.all_eq_true] using h9

/-- The renaming sends a name to a target of `ps` or fixes it. -/
theorem renOf_cases (ps : List (String × String)) (r : String) :
    renOf ps r = r ∨ ∃ p ∈ ps, p.1 = r ∧ renOf ps r = p.2 := by
  unfold renOf
  cases hf : ps.find? (·.1 == r) with
  | none => exact Or.inl rfl
  | some p =>
      refine Or.inr ⟨p, List.mem_of_find?_eq_some hf, ?_, rfl⟩
      simpa using List.find?_some hf

/-! ## 7. The image route -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (runIdxOk_of_idxInvCheckB)

/-- Under the route check, `entryV` at the frame of the printed body is an ABI entry. -/
theorem routeB_abiEntry {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    (hg : routeB σ nm body seeds loop ps fuse out = true) (sa : AState) :
    AbiEntryM σ sa (entryV σ (frameE body sa) sa (unren ps)) := by
  simp only [routeB, Bool.and_eq_true] at hg
  have E := entryB_spec hg.1.1.1.2 sa
  exact entryV_abiEntry E.argF E.argG fun j hj => ((renB_spec hg.1.1.2).unr j hj).1

/-- **The node on the decoded bytes through the image route.** Let the printed body `body`,
    the node `seeds ++ loop`, the renaming `ps`, the fusion flag `fuse` and the output array
    `out` of the slot `q` of length `n` pass `routeB`. From every machine state `sa`
    satisfying `σ.Regions`, every halting run of the node from the entry state `entryV` is
    matched by a halting run of the decoded bytes of the printed body from `sa`, at the end of
    which the words at the entry base of `out` are the array `out` at the end of the run of the
    node. -/
theorem image_route_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {seeds loop : List LinstrRM} {ps : List (String × String)} {fuse : Bool} {out : String}
    (hg : routeB σ nm body seeds loop ps fuse out = true) {q : String} {n : Nat}
    (hq : slotArrOf σ nm q = some (out, n)) (sa : AState) (hreg : σ.Regions sa) (fn : String)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := entryV σ (frameE body sa) sa (unren ps), lfn := fn }, zf := false }
        = some t) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr, t.prog.base.getArr out 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa out) j) = arr ⟨j, hj⟩ := by
  simp only [routeB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    List.contains_eq_mem, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hidx⟩, hpr⟩, hphys⟩, hgate⟩, hfr⟩, hent⟩, hren⟩, hfuse⟩, hout⟩ := hg
  have E := entryB_spec hent sa
  have R := renB_spec hren
  set fr := frameE body sa with hfrdef
  set b0 := entryV σ fr sa (unren ps) with hb0
  have habi : AbiEntryM σ sa b0 := entryV_abiEntry E.argF E.argG fun j hj => (R.unr j hj).1
  have hS := E.argSrc hreg.stackIn
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (un := unren ps) E.argF E.argG hS false
  have hb1 : ({ b0 with reg := { b0.reg with lpc := σ.args.length } } : LstateM).setLpc 0
      = b0 := rfl
  have hA : ∀ b2 z2, runStraightF (argBind σ nm ++ seeds) b0 false = some (b2, z2) →
      ∀ r, r ∈ loopNames loop → b2.larr (renOf ps r) = b2.larr r := by
    intro b2 z2 hb2 r _
    have hl := runStraightF_larr R.store hb2
    rw [hl]
    rcases renOf_cases ps r with he | ⟨p, hp, rfl, he⟩
    · rw [he]
    · rw [he]
      show (abiEntryM σ sa).larr (unren ps p.2) = (abiEntryM σ sa).larr (unren ps p.1)
      rw [unren_target R.nd hp, unren_of_not_target fun q hq => R.ts p hp q hq]
  have hun : ∀ q A n, slotArrOf σ nm q = some (A, n) → unren ps (renOf ps A) = A := by
    intro q A n h
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
    exact (R.unr j (List.getElem?_eq_some_iff.mp hj).1).2
  have hq' : slotRen (slotArrOf σ nm) (renOf ps) q = some (renOf ps out, n) := by
    simp [slotRen, hq]
  -- the virtual body from the node
  obtain ⟨fuel', t', hrun', harr⟩ : ∃ fuel' t', lsemFuelMemF
      (singletonProgM fn (virtB σ nm seeds loop ps fuse)) fuel'
        { prog := { base := b0, lfn := fn }, zf := false } = some t'
      ∧ t'.prog.base.getArr (renOf ps out) 64 n = t.prog.base.getArr out 64 n := by
    cases fuse with
    | false =>
        exact ImageAddrSrc.src_chain fn (argBind σ nm) seeds loop ps (· ∈ loopNames loop)
            (JasminLsemRenameLoop.movesOf_isLopn _) R.lopn R.ctl R.cond R.ren R.names R.nd
            R.ts R.tgt R.fresh b0 _ false rfl hpr0 hb1 hA fuel t hrun out hout 64 n
    | true =>
        simp only [Bool.true_eq_false, false_or] at hfuse
        exact ImageAddrSrc.src_chain_fuse fn (argBind σ nm) seeds loop ps (· ∈ loopNames loop)
          (JasminLsemRenameLoop.movesOf_isLopn _) R.lopn R.ctl R.cond R.ren R.names R.nd
          R.ts R.tgt R.fresh b0 _ false rfl hpr0 hb1 hA hfuse.1 (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact e64_of_abiEntryM habi x hx
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              exact congrArg (·.1) (entryV_srcOf (un := unren ps) hS ha))
          fuel t hrun out hout hfuse.2 64 n
  -- the bounds invariant
  have hents := boundFacts_entryV (nm := nm) (fr := fr) (un := unren ps) hreg E.bnds
  have hok := runIdxOk_of_idxInvCheckB hidx fn _ t' rfl rfl (hents _) fuel' hrun'
  -- the image simulation
  have hgate' : imgGateB fr (slotRen (slotArrOf σ nm) (renOf ps)) body = true := by
    rw [hfrdef, ImageAddrFrame.imgGateB_frameMark]; exact hgate
  have hsep := imgSep_slotRen (ren := renOf ps)
    (ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot) hun
  obtain ⟨prog, sa', hdec, hh, -, hcells⟩ := ImageAddrFrame.virt_bytes hck hpr hphys hgate'
    hsep fn _ t' rfl rfl (entryA σ sa) false (imgRel_entryS hS hent
      fun j hj => (R.unr j hj).2) rfl (fun R hR => by
        have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (phys R)⟩ := by
          simp only [entryA, hR, if_true]
        unfold LstateN.getW
        rw [hl]
        simp) rfl fuel' hrun' hok
  refine ⟨prog, sa', hdec, hh, ?_⟩
  obtain ⟨arr, h1, h2⟩ := hcells q (renOf ps out) n hq'
  refine ⟨arr, ?_, fun j hj => ?_⟩
  · rw [← harr, h1]
  · have := h2 j hj
    rwa [hun q out n hq] at this

/-- The read-back of a word-array result is the array whose words are at the entry value of
    its register. -/
theorem resultOf_words {σ : AbiLayout} {sa sa' : AState} {RA : String} {n : Nat}
    {arr : Fin n → BitVec 64} (hres : σ.result = .words RA n)
    (hw : ∀ j (hj : j < n), read64 sa'.mem (cellAt (sa.regs RA) j) = arr ⟨j, hj⟩) :
    σ.ResultOf sa sa' (.array ((List.range n).map fun j =>
      .int (JasminDialect.stackGet arr j).toNat)) := by
  unfold AbiLayout.ResultOf
  rw [hres]
  simp only [Haxc.ResultKind.read, Haxc.wordsAt, _root_.Hax.Value.array.injEq]
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < n := List.mem_range.mp hj
  rw [show j = (⟨j, hj'⟩ : Fin n).val from rfl, JasminDialect.stackGet_id, ← hw j hj']

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
