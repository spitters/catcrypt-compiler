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

* `argPairs`, `argBind`: the copies of the parameter registers into the argument names.
* `slotArrOf`: the array, with its length, whose pointer a frame slot holds.
* `synthRen`: the renaming of the loop-carried names synthesised from the virtual body and
  the image.
* `noStoreB`, `fstepF_larr`, `runStraightF_larr`: a straight run without array stores keeps
  the arrays.
* `movesState_same`: copies that write the value their target holds change only the program
  counter.
* `entryA`, `entryV`: the entry states.
* `virtB`, `routeB`: the virtual body and the decided checks of the route.

## Main results

* `entryV_abiEntry`, `argBind_entryV`, `boundFacts_entryV`, `imgRel_entryV`: the entry states
  are an ABI entry, the copies leave them unchanged, the register bounds hold, and they are
  related by the relation of the image simulation.
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

/-- The pairs `(nm R, argName j)` of the register `R` of each parameter `j` of `σ`. -/
def argPairs (σ : AbiLayout) (nm : String → String) : List (String × String) :=
  σ.args.mapIdx fun j a => (nm a.reg, argName j)

/-- The copies `argName j := nm R` of the register `R` of each parameter `j` of `σ` into its
    argument name. -/
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
    at most once. The checks of the route (`routeB`) check the result; the pairing carries no
    trust. -/
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

/-- The instruction is no array store. -/
def noStoreB (i : LinstrRM) : Bool :=
  match i.2 with
  | .store _ _ => false
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

/-- **The name-keyed state at entry** of the machine state `sa` under the frame map `fr`: a
    name with a frame word holds the word at it, every other name its value in `entryA`; the
    arrays of `abiEntryM`; program counter `0`. -/
def entryV (σ : AbiLayout) (fr : String → Option (BitVec 64)) (sa : AState) : LstateM where
  reg :=
    { lvm := fun r => match fr r with
        | some a => ⟨64, read64 sa.mem a⟩
        | none => (entryA σ sa).reg.lvm r
      lpc := 0 }
  larr := (abiEntryM σ sa).larr

theorem abiArgOf_argName {σ : AbiLayout} {j : Nat} {a : AbiArg} (h : σ.args[j]? = some a) :
    abiArgOf σ (argName j) = some a :=
  abiEntryM_lookup h

theorem abiBase_argName {σ : AbiLayout} {j : Nat} {a : AbiArg} (h : σ.args[j]? = some a)
    (sa : AState) : abiBase (abiReg σ) sa (argName j) = sa.regs a.reg := by
  simp [abiBase, abiReg, abiArgOf_argName h]

/-- The register of an argument name in `entryV`, when the name has no frame word and is no
    general-purpose name. -/
theorem entryV_argName {σ : AbiLayout} {fr : String → Option (BitVec 64)} {sa : AState}
    {j : Nat} {a : AbiArg} (h : σ.args[j]? = some a) (hF : fr (argName j) = none)
    (hG : gpOk (argName j) = false) :
    (entryV σ fr sa).reg.lvm (argName j) = ⟨64, sa.regs a.reg⟩ := by
  simp only [entryV, entryA, hF, hG, abiEntryM, abiEntryM_lookup h]
  rfl

/-- `entryV` is an ABI entry of the flag machine when no argument name has a frame word or
    is a general-purpose name. -/
theorem entryV_abiEntry {σ : AbiLayout} {fr : String → Option (BitVec 64)} {sa : AState}
    (hF : ∀ j, j < σ.args.length → fr (argName j) = none)
    (hG : ∀ j, j < σ.args.length → gpOk (argName j) = false) :
    AbiEntryM σ sa (entryV σ fr sa) where
  pc := rfl
  reg := fun j a h => by
    have hj := (List.getElem?_eq_some_iff.mp h).1
    unfold LstateN.getW
    rw [entryV_argName h (hF j hj) (hG j hj)]
    simp
  arr := fun j a n h hk => (abiEntryM_spec σ sa).arr j a n h hk

/-- **The copies of the parameter registers leave `entryV` unchanged** but for the program
    counter, when each parameter register is named by a general-purpose name of that
    machine register without a frame word. -/
theorem argBind_entryV {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState}
    (hF : ∀ j, j < σ.args.length → fr (argName j) = none)
    (hG : ∀ j, j < σ.args.length → gpOk (argName j) = false)
    (hR : ∀ a ∈ σ.args, gpOk (nm a.reg) = true ∧ phys (nm a.reg) = a.reg
      ∧ fr (nm a.reg) = none) (zf : Bool) :
    runStraightF (argBind σ nm) (entryV σ fr sa) zf
      = some ({ entryV σ fr sa with reg := { (entryV σ fr sa).reg with
          lpc := σ.args.length } }, zf) := by
  unfold argBind
  rw [JasminLsemRenameLoop.runStraightF_movesOf, movesState_same]
  · simp [argPairs, entryV]
  · intro p hp
    simp only [argPairs, List.mem_mapIdx] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    have ha : σ.args[j]? = some σ.args[j] := List.getElem?_eq_getElem hj
    obtain ⟨h1, h2, h3⟩ := hR _ (List.getElem_mem hj)
    rw [entryV_argName ha (hF j hj) (hG j hj)]
    simp only [entryV, entryA, h3, h1, if_true, h2]

/-- The register bounds of `σ` hold at `entryV` at the names `nm`, when each bounded
    register is named by a general-purpose name of that machine register without a frame
    word. -/
theorem boundFacts_entryV {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState} (hreg : σ.Regions sa)
    (hB : ∀ b ∈ σ.bounds, gpOk (nm b.1) = true ∧ phys (nm b.1) = b.1 ∧ fr (nm b.1) = none) :
    ∀ f ∈ boundFacts σ nm, f.holds (entryV σ fr sa).reg.lvm :=
  boundFacts_holds hreg fun b hb => by
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

/-- **The entry pair is related.** `entryV` and `entryA` are related by the relation of the
    image simulation at the frame map `fr`, the slots of `slotArrOf σ nm` and the entry bases
    of the parameters, when the register of each parameter is named by a general-purpose name
    of that machine register. -/
theorem imgRel_entryV {σ : AbiLayout} {nm : String → String}
    {fr : String → Option (BitVec 64)} {sa : AState} {body : Lcmd} {fn : String}
    (hS : ∀ a ∈ σ.args, gpOk (nm a.reg) = true ∧ phys (nm a.reg) = a.reg) :
    ImgRel fr (slotArrOf σ nm) (abiBase (abiReg σ) sa) body
      { prog := { base := entryV σ fr sa, lfn := fn }, zf := false } (entryA σ sa) false := by
  refine ImageAddrFrame.imgRel_entry rfl rfl (fun r h => ?_) (fun q a h => ?_) rfl rfl rfl
    (fun r h => ?_) (fun q A n h => ?_) (fun R A n h => ?_)
  · simp [entryV, h]
  · simp [entryV, entryA, h]
  · simp [entryA, h]
  · obtain ⟨j, a, hj, hk, rfl, -⟩ := slotArrOf_some h
    rw [abiBase_argName hj]
    exact (abiEntryM_spec σ sa).arr j a n hj hk
  · obtain ⟨j, a, hj, -, rfl, hq⟩ := slotArrOf_some h
    have hR : nm a.reg = R := by simpa [slotOfReg] using hq
    obtain ⟨h1, h2⟩ := hS a (List.mem_of_getElem? hj)
    have hl : (entryA σ sa).reg.lvm (nm a.reg) = ⟨64, sa.regs a.reg⟩ := by
      simp only [entryA, h1, if_true, h2]
    rw [abiBase_argName hj, ← hR]
    unfold LstateN.getW
    rw [hl]
    simp

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

/-- The array cell of the name `x` in `abiEntryM` is the default cell: `x` names no array
    parameter. -/
def larrDefB (σ : AbiLayout) (x : String) : Bool :=
  match (argIdxOf σ.args.length x).bind (σ.args[·]?) with
  | some a => match a.kind with
    | .words _ => false
    | .scalar => true
  | none => true

/-- The regions of the array parameters of `σ`, under their argument names. -/
def rsOf (σ : AbiLayout) : List Region :=
  (List.range σ.args.length).filterMap fun j =>
    match σ.args[j]? with
    | some a => match a.kind with
      | .words n => some ⟨argName j, n, 0⟩
      | .scalar => none
    | none => none

/-- **The renaming check**: the seeds are `Lopn`s, the loop is in the covered classes and
    reads no implicit register, the renaming is injective on the names of the loop and fixes
    the empty name, its targets are distinct, no source and not names of the loop, it sends
    each source to its target, the copies and seeds store no array, and no source or target
    names an array parameter. -/
def renB (σ : AbiLayout) (nm : String → String) (seeds loop : List LinstrRM)
    (ps : List (String × String)) : Bool :=
  let Ns := loopNames loop
  seeds.all isLopnB && loop.all (fun i => clsB i && mulxFree i)
    && Ns.all (fun a => Ns.all fun b => !(renOf ps a == renOf ps b) || a == b)
    && renOf ps "" == ""
    && decide ((ps.map Prod.snd).Nodup) && ps.all (fun p => ps.all fun q => q.2 != p.1)
    && ps.all (fun p => renOf ps p.1 == p.2) && ps.all (fun p => !Ns.contains p.2)
    && (argBind σ nm ++ seeds).all noStoreB
    && ps.all (fun p => larrDefB σ p.1 && larrDefB σ p.2)

/-- **The entry check**: no argument name is a general-purpose name or has a frame word; the
    register of each parameter and each bounded register is named by a general-purpose name
    of that machine register without a frame word; the slot of each array parameter has a
    frame word. -/
def entryB (σ : AbiLayout) (nm : String → String) (body : Lcmd) : Bool :=
  let fm := frameMark (frameNames body)
  (List.range σ.args.length).all (fun j => !gpOk (argName j) && (fm (argName j)).isNone)
    && σ.args.all (fun a => gpOk (nm a.reg) && phys (nm a.reg) == a.reg
      && (fm (nm a.reg)).isNone)
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
  ownedCheckMC [] B (virtImg (slotArrOf σ nm) body)
    && idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B
    && printedAddrB body && physImgB (slotArrOf σ nm) body
    && imgGateB (frameMark (frameNames body)) (slotArrOf σ nm) body
    && frameOkB σ body && entryB σ nm body && renB σ nm seeds loop ps
    && (!fuse || (fuseOKL (abiArgNames σ) (fuseLoPre pre L) (pre ++ L)
      && out != "R15" && out != "RDX"))
    && (loopNames loop).contains out && !(ps.any (·.1 == out))

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
  regs : ∀ a ∈ σ.args, gpOk (nm a.reg) = true ∧ phys (nm a.reg) = a.reg ∧ fr (nm a.reg) = none
  bnds : ∀ b ∈ σ.bounds, gpOk (nm b.1) = true ∧ phys (nm b.1) = b.1 ∧ fr (nm b.1) = none
  slot : ∀ q A n, slotArrOf σ nm q = some (A, n) → ∃ a, fr q = some a
  rs : rsOK σ (rsOf σ) = true
  len : ∀ q A n, slotArrOf σ nm q = some (A, n) → regLen (rsOf σ) A = n

theorem entryB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    (h : entryB σ nm body = true) (sa : AState) : EntryFacts σ nm (frameE body sa) := by
  simp only [entryB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun j hj => frameE_none sa (h1 j hj).2, fun j hj => (h1 j hj).1,
    fun a ha => ⟨(h2 a ha).1.1, (h2 a ha).1.2, frameE_none sa (h2 a ha).2⟩,
    fun b hb => ⟨(h3 b hb).1.1, (h3 b hb).1.2, frameE_none sa (h3 b hb).2⟩,
    fun q A n hq => ?_, h5, fun q A n hq => ?_⟩
  · obtain ⟨j, a, hj, hk, rfl, rfl⟩ := slotArrOf_some hq
    have := h4 a (List.mem_of_getElem? hj)
    rw [hk] at this
    exact frameE_some sa this
  · obtain ⟨j, a, hj, hk, rfl, -⟩ := slotArrOf_some hq
    have := h6 j (List.getElem?_eq_some_iff.mp hj).1
    rw [hj] at this
    simp only [hk, beq_iff_eq] at this
    exact this

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
  dflt : ∀ p ∈ ps, larrDefB σ p.1 = true ∧ larrDefB σ p.2 = true

theorem renB_spec {σ : AbiLayout} {nm : String → String} {seeds loop : List LinstrRM}
    {ps : List (String × String)} (h : renB σ nm seeds loop ps = true) :
    RenFacts σ nm seeds loop ps := by
  simp only [renB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨fun i hi => isLopnB_isLopn (h1 i hi), fun i hi => (clsB_ctl_cond (h2 i hi).1
    (h2 i hi).2).1, fun i hi => (clsB_ctl_cond (h2 i hi).1 (h2 i hi).2).2,
    ⟨fun a b ha hb he => ?_, List.mem_cons_self .., h4⟩, fun i hi n hn => ?_, h5, h6, h7,
    h8, ?_, fun p hp => h10 p hp⟩
  · have := h3 a ha b hb
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      beq_iff_eq] at this
    rcases this with h | h
    · exact absurd he h
    · exact h
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, hi, hn⟩)
  · simpa only [List.all_eq_true] using h9

/-- The cell of a name that `larrDefB` accepts in `abiEntryM` is the default cell. -/
theorem larr_of_larrDefB {σ : AbiLayout} {sa : AState} {x : String}
    (h : larrDefB σ x = true) : (abiEntryM σ sa).larr x = ArrCell.default := by
  unfold larrDefB at h
  simp only [abiEntryM]
  split at h
  · rename_i a ha
    rw [ha]
    split at h
    · cases h
    · rename_i hk
      simp only [hk]
  · rename_i ha
    rw [ha]

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
    AbiEntryM σ sa (entryV σ (frameE body sa) sa) := by
  simp only [routeB, Bool.and_eq_true] at hg
  have E := entryB_spec hg.1.1.1.1.2 sa
  exact entryV_abiEntry E.argF E.argG

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
      { prog := { base := entryV σ (frameE body sa) sa, lfn := fn }, zf := false } = some t) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr, t.prog.base.getArr out 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa out) j) = arr ⟨j, hj⟩ := by
  simp only [routeB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    List.contains_eq_mem, decide_eq_true_eq, List.any_eq_false, beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hidx⟩, hpr⟩, hphys⟩, hgate⟩, hfr⟩, hent⟩, hren⟩, hfuse⟩, hout⟩,
    hnps⟩ := hg
  have E := entryB_spec hent sa
  have R := renB_spec hren
  set fr := frameE body sa with hfrdef
  set b0 := entryV σ fr sa with hb0
  have habi : AbiEntryM σ sa b0 := entryV_abiEntry E.argF E.argG
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) E.argF E.argG E.regs false
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
      show (abiEntryM σ sa).larr p.2 = (abiEntryM σ sa).larr p.1
      rw [larr_of_larrDefB (R.dflt p hp).2, larr_of_larrDefB (R.dflt p hp).1]
  have hfix : renOf ps out = out := JasminLsemRenameLoop.renOf_of_not_mem (by
    intro hm
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
    exact hnps p hp he)
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
          R.ts R.tgt R.fresh b0 _ false rfl hpr0 hb1 hA hfuse.1.1 (e64_of_abiEntryM habi)
          fuel t hrun out hout (by rw [hfix]; exact ⟨hfuse.1.2, hfuse.2⟩) 64 n
  -- the bounds invariant
  have hents := boundFacts_entryV (nm := nm) (fr := fr) hreg E.bnds
  have hok := runIdxOk_of_idxInvCheckB hidx fn _ t' rfl rfl hents fuel' hrun'
  -- the image simulation
  have hgate' : imgGateB fr (slotArrOf σ nm) body = true := by
    rw [hfrdef, ImageAddrFrame.imgGateB_frameMark]; exact hgate
  have hsep := ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot
  obtain ⟨prog, sa', hdec, hh, -, hcells⟩ := ImageAddrFrame.virt_bytes hck hpr hphys hgate'
    hsep fn _ t' rfl rfl (entryA σ sa) false (imgRel_entryV (fun a ha =>
      ⟨(E.regs a ha).1, (E.regs a ha).2.1⟩)) rfl (fun R hR => by
        have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (phys R)⟩ := by
          simp only [entryA, hR, if_true]
        unfold LstateN.getW
        rw [hl]
        simp) rfl fuel' hrun' hok
  refine ⟨prog, sa', hdec, hh, ?_⟩
  obtain ⟨arr, h1, h2⟩ := hcells q out n hq
  refine ⟨arr, ?_, h2⟩
  rw [← harr, hfix, h1]

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
