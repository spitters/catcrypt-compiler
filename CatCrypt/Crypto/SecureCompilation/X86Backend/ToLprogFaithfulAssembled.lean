/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProlog

/-!
# The whole-function register-allocation faithfulness theorem

`toLprogPhysAbi_faithful_uniform` runs the assembled function body of the owned
x86 export — `buildPrologue`, the argument materialization `argMatSeq`, the
physical two-address body `physBody`, and the terminating `Lret` — under the
`JasminLsem` whole-function fold `lsemRun` from an entry state, for a
`UniformRegArith` `Com`, and reads the composed virtual store at the physical
result register. It composes the three proved legs:

* the prologue run and frame (`ToLprogFaithfulProlog.buildPrologue_lsem`,
  `buildPrologue_frame`);
* the materialization run and frame (`ToLprogFaithfulWholeFn.argMatSeq_reads`,
  `argMatSeq_frame`);
* the body run (`ToLprogFaithfulNary.physBody_lsem_result_uniform`).

The composition is `ToLprogFaithfulWholeFn.toLprogPhysAbi_lsem`; this module
supplies its `hProlog`, `hrel` and `hbodyNoLret` inputs:

* `Lret_not_mem_of_lsemStraight_some`: a successful `lsemStraight` run contains
  no `Lret` (`lsemStep .Lret` is `none`), so `hbodyNoLret` follows from the
  three runs;
* `argMatSeq_establishes_StoreRel`: the store relation after materialization
  follows from the store relation off the materialization destinations
  (`StoreRelOff`) and the ABI condition that each pair's source holds the
  virtual value of every name renamed onto the pair's destination
  (`ArgMatAbi`); `buildPrologue_preserves_StoreRelOff` transports `StoreRelOff`
  from the entry state through the prologue under `PrologueFrameDisjoint`.

## Main results

* `toLprogPhysAbi_faithful_uniform`: the whole emitted function body, run under
  `lsemRun` from an ABI entry state, leaves the composed virtual store's result
  in the physical result register, for any binding count.
* `toLprogPhysAbi_faithful_uniform_twoPtr`: the same at the canonical
  `[RDI, RSI]` materialization pairs, with the well-formedness hypotheses
  discharged from the frame and memref hypotheses.
* `toLprogPhysAbi_faithful_uniform_epilogue`: the same with the callee-save
  restore epilogue before the `Lret`.
* `Lret_not_mem_of_lsemStraight_some`: a block with a successful
  `lsemStraight` run contains no `Lret`.
* `argMatSeq_establishes_StoreRel`: the store relation after the argument
  materialization, from `StoreRelOff` and `ArgMatAbi`.

## The two-pointer instance

`twoPtrPairs` is the materialization pair list of the canonical `[RDI, RSI]`
ABI: `argName 0` from `qsave.RDI` and `argName 1` from `qsave.RSI`.
`toLprogPhysAbi_faithful_uniform_twoPtr` instantiates the theorem at these
pairs: `SourcesFresh` follows from `PrologueFrameDisjoint`, `DestsDistinct` is
`MemrefPtrsDistinct`, and `ArgMatAbi` reduces to the entry values of `RDI` and
`RSI` (`prologueState_lvm_abiSaveRdi`, `prologueState_lvm_abiSaveRsi`).

## The callee-save restore epilogue

`calleeSaveRestoreEpilogue_lsem` runs the six-`MOVQ` restore sequence to the
explicit `epilogueState`, and `calleeSaveRestoreEpilogue_frame` confines its
writes to the six callee-saved registers `epilogueWritten`.
`toLprogPhysAbi_faithful_uniform_epilogue` places the epilogue before the
`Lret`, as `insertEpilogue` does, under the hypothesis that the physical result
register is not one of the six.

## Explicit hypotheses

* `hbody` / `hcd`: the body is the binop prefix `bindingHeads … com d`, and the
  per-binding `CoverData` carries the head naming, the two-address collapse
  `hcol`, and (inside each `BinopBinding`) the live-out interference condition
  `hinj` and carry condition `hcarry` — the register-allocator obligations
  `ToLprogFaithfulNary` scopes. `hch` chains the bindings' live sets from the
  entry set `L` to the exit set `N`, and the result name is live at `N`.
* `hdisjFrame : PrologueFrameDisjoint`: the renaming avoids the nine
  prologue-written cells.
* `hfresh` / `hdist` (general form) or `hmemref` (two-pointer form): the
  materialization pairs are well-formed.
* The instruction list is `prologue ++ argMatSeq pairs ++ physBody ++ Lret ::
  rest`. The shipped `comToLfundefPhysAbiFromVirt` body on the two-pointer,
  call-free, store-free path is `buildPrologue … ++ buildArgPtrMaterialize …
  ++ (physBodyWithStores …).dropLast ++ calleeSaveRestoreEpilogue ++ [Lret]`;
  the identification of `buildArgPtrMaterialize` with `argMatSeq (twoPtrPairs
  …)` and of `(physBodyWithStores …).dropLast` with `physBody` on that path is
  not proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulAssembled

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProlog

/-! ## 1. `Lret`-freeness of a successful straight-line run -/

/-- A successful `lsemStraight` run contains no `Lret`: `lsemStep .Lret` is
    `none`, so a run through an `Lret` short-circuits. -/
theorem Lret_not_mem_of_lsemStraight_some {w : Nat} (is : List LinstrR)
    (s s' : Lstate w) (h : lsemStraight is s = some s') : .Lret ∉ is := by
  induction is generalizing s with
  | nil => simp
  | cons i is ih =>
      obtain ⟨s1, hstep, hrun⟩ := lsemStraight_cons_inv i is s s' h
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · simp [lsemStep] at hstep
      · exact ih s1 hrun hmem'

/-! ## 2. The materialization establishes the store relation -/

/-- The store relation off a list of physical registers, at the live set `L`: the
    physical store `sP` reads, at the renamed register of every name of `L` that
    lies outside `dests`, the virtual value. -/
def StoreRelOff {w : Nat} (body : Lcmd) (tbl : Array Nat) (L : List String)
    (dests : List String) (s sP : Lstate w) : Prop :=
  ∀ m ∈ L, physRename body tbl m ∉ dests → sP.lvm (physRename body tbl m) = s.lvm m

/-- The ABI condition on a materialization pair list, at the live set `L`: each
    pair's source register holds in `sP` the virtual value of every name of `L`
    renamed onto the pair's destination. -/
def ArgMatAbi {w : Nat} (body : Lcmd) (tbl : Array Nat) (L : List String)
    (pairs : List (String × String)) (s sP : Lstate w) : Prop :=
  ∀ p ∈ pairs, ∀ m ∈ L, physRename body tbl m = p.1 → sP.lvm p.2 = s.lvm m

/-- Running `argMatSeq pairs` from a state related to the virtual store off the
    destinations, with the ABI condition on the pairs, reaches a state related to
    the virtual store at every renamed register. A destination reads its pair's
    source (`argMatSeq_reads`); every other register is unchanged
    (`argMatSeq_frame`). -/
theorem argMatSeq_establishes_StoreRel {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (L : List String)
    (pairs : List (String × String)) (hfresh : SourcesFresh pairs)
    (hdist : DestsDistinct pairs) (s sP sMat : Lstate w)
    (hoff : StoreRelOff body tbl L (pairs.map Prod.fst) s sP)
    (habi : ArgMatAbi body tbl L pairs s sP)
    (hrun : lsemStraight (argMatSeq pairs) sP = some sMat) :
    StoreRel body tbl L s sMat := by
  intro m hmL
  by_cases hd : physRename body tbl m ∈ pairs.map Prod.fst
  · obtain ⟨p, hp, hpm⟩ := List.mem_map.mp hd
    obtain ⟨sMat', hrun', hread⟩ := argMatSeq_reads pairs hfresh hdist sP
    have heq : sMat' = sMat := Option.some.inj (hrun'.symm.trans hrun)
    subst heq
    rw [← hpm, hread p hp]
    exact habi p hp m hmL hpm.symm
  · rw [argMatSeq_frame pairs hrun (physRename body tbl m)
      (fun p hp hpm => hd (List.mem_map.mpr ⟨p, hp, hpm.symm⟩))]
    exact hoff m hmL hd

/-- The prologue transports `StoreRelOff` from the entry state to
    `prologueState`, under `PrologueFrameDisjoint`. -/
theorem buildPrologue_preserves_StoreRelOff {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (L : List String) (dests : List String) (s sEntry : Lstate w)
    (hdisj : PrologueFrameDisjoint body tbl L)
    (hoff : StoreRelOff body tbl L dests s sEntry) :
    StoreRelOff body tbl L dests s (prologueState sEntry) := by
  intro m hmL hm
  rw [buildPrologue_frame sEntry (physRename body tbl m) (hdisj m hmL)]
  exact hoff m hmL hm

/-! ## 3. The assembled whole-function theorem -/

/-- The straight-line core: running `prologue ++ argMatSeq pairs ++ physBody`
    under `lsemStraight` from the entry state reaches a state whose physical
    result register reads the composed virtual store, and the list is
    `Lret`-free. Obtained from `toLprogPhysAbi_lsem` at `rest := []` with the
    prologue run `buildPrologue_lsem`, the store relation from
    `argMatSeq_establishes_StoreRel`, and `Lret`-freeness from the three runs. -/
theorem prologue_argMat_body_lsemStraight {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N) :
    .Lret ∉ ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
        ++ (physBody (fun _ => none) body).map (·.li_i))
    ∧ ∃ sEnd,
      lsemStraight
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i)) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hoffP :=
    buildPrologue_preserves_StoreRelOff body (bodyPhysTable body) L _ s sEntry
      hdisjFrame hoff
  have hrel : ∀ sMat,
      lsemStraight (argMatSeq pairs) (prologueState sEntry) = some sMat →
        StoreRel body (bodyPhysTable body) L s sMat :=
    fun sMat hrun => argMatSeq_establishes_StoreRel body (bodyPhysTable body) L pairs
      hfresh hdist s _ sMat hoffP habi hrun
  obtain ⟨sMat, hrunMat, _⟩ := argMatSeq_reads pairs hfresh hdist (prologueState sEntry)
  obtain ⟨sB, hrunBody, _⟩ :=
    physBody_lsem_result_uniform body nArgs d com bs hbody hcd L N hch s sMat
      (hrel sMat hrunMat) nRes hnRes
  have hnoLret : .Lret ∉
      ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
        ++ (physBody (fun _ => none) body).map (·.li_i)) := by
    intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact Lret_not_mem_of_lsemStraight_some _ _ _
          (buildPrologue_lsem virt tbl0 inLoadMap sEntry) hmem
      · exact Lret_not_mem_of_lsemStraight_some _ _ _ hrunMat hmem
    · exact Lret_not_mem_of_lsemStraight_some _ _ _ hrunBody hmem
  obtain ⟨sEnd, hrun, hread⟩ :=
    toLprogPhysAbi_lsem body nArgs d com bs
      ((buildPrologue virt tbl0 inLoadMap).map (·.li_i)) [] pairs hfresh hdist
      hbody hcd hmemref L N hch sEntry s hnoLret (prologueState sEntry)
      (buildPrologue_lsem virt tbl0 inLoadMap sEntry) hrel nRes hnRes
  rw [lsemRun_body_ret _ _ _ hnoLret] at hrun
  exact ⟨hnoLret, sEnd, hrun, hread⟩

/-- **Whole-function register-allocation faithfulness.** For a
    `UniformRegArith` `Com` whose binop prefix is `body`, with the per-binding
    `CoverData`, running the assembled function body `buildPrologue ++
    argMatSeq pairs ++ physBody ++ Lret :: rest` under the whole-function fold
    `lsemRun` from an entry state related to the virtual store off the
    materialization destinations (`hoff`), whose renaming avoids the prologue
    cells (`hdisjFrame`) and whose materialization sources carry the argument
    values (`habi`), reaches a state whose physical result register reads the
    composed virtual store. -/
theorem toLprogPhysAbi_faithful_uniform {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  obtain ⟨hnoLret, sEnd, hrun, hread⟩ :=
    prologue_argMat_body_lsemStraight body nArgs d com bs virt tbl0 inLoadMap pairs
      hfresh hdist hbody hcd hmemref L N hch sEntry s hdisjFrame hoff habi nRes hnRes
  rw [lsemRun_body_ret _ _ _ hnoLret]
  exact ⟨sEnd, hrun, hread⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulAssembled.toLprogPhysAbi_faithful_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toLprogPhysAbi_faithful_uniform

/-! ## 4. The two-pointer instance -/

/-- The materialization pairs of the canonical `[RDI, RSI]` ABI: the renamed
    `argName 0` from the red-zone save `qsave.RDI`, the renamed `argName 1` from
    `qsave.RSI`. -/
def twoPtrPairs (body : Lcmd) (tbl : Array Nat) : List (String × String) :=
  [(physRename body tbl (argName 0), abiSaveRdiName),
   (physRename body tbl (argName 1), abiSaveRsiName)]

/-- The two-pointer sources are fresh: the renaming avoids the save slots
    (`PrologueFrameDisjoint`). -/
theorem twoPtrPairs_sourcesFresh (body : Lcmd) (tbl : Array Nat) (L : List String)
    (hdisj : PrologueFrameDisjoint body tbl L)
    (hm0 : argName 0 ∈ L) (hm1 : argName 1 ∈ L) :
    SourcesFresh (twoPtrPairs body tbl) := by
  intro p hp q hq
  have h0 := hdisj (argName 0) hm0
  have h1 := hdisj (argName 1) hm1
  simp only [prologueWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at h0 h1
  simp only [twoPtrPairs, List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact Ne.symm h0.1
  · exact Ne.symm h1.1
  · exact Ne.symm h0.2.1
  · exact Ne.symm h1.2.1

/-- The two-pointer destinations are distinct: `MemrefPtrsDistinct`. -/
theorem twoPtrPairs_destsDistinct (body : Lcmd) (tbl : Array Nat)
    (hmemref : MemrefPtrsDistinct body tbl) : DestsDistinct (twoPtrPairs body tbl) := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact hmemref
  · intro q hq
    simp at hq

/-- The prologue leaves `qsave.RDI` holding the entry value of `RDI`. -/
theorem prologueState_lvm_abiSaveRdi {w : Nat} (sEntry : Lstate w) :
    (prologueState sEntry).lvm abiSaveRdiName = sEntry.lvm "RDI" := by
  simp +decide [prologueState, prologueStep, abiSaveRdiName, abiSaveRsiName, reloadScratch2]

/-- The prologue leaves `qsave.RSI` holding the entry value of `RSI`. -/
theorem prologueState_lvm_abiSaveRsi {w : Nat} (sEntry : Lstate w) :
    (prologueState sEntry).lvm abiSaveRsiName = sEntry.lvm "RSI" := by
  simp +decide [prologueState, prologueStep, abiSaveRdiName, abiSaveRsiName, reloadScratch2]

/-- **Whole-function faithfulness at the two-pointer ABI.** The instance of
    `toLprogPhysAbi_faithful_uniform` at `twoPtrPairs`: the entry state carries
    the virtual store off the two argument registers, `RDI` holds the virtual
    value of every name renamed onto `argName 0`'s register, and `RSI` that of
    every name renamed onto `argName 1`'s register. -/
theorem toLprogPhysAbi_faithful_uniform_twoPtr {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hm0 : argName 0 ∈ L) (hm1 : argName 1 ∈ L)
    (hoff : StoreRelOff body (bodyPhysTable body) L
      [physRename body (bodyPhysTable body) (argName 0),
       physRename body (bodyPhysTable body) (argName 1)] s sEntry)
    (hRdi : ∀ m ∈ L, physRename body (bodyPhysTable body) m
      = physRename body (bodyPhysTable body) (argName 0) → sEntry.lvm "RDI" = s.lvm m)
    (hRsi : ∀ m ∈ L, physRename body (bodyPhysTable body) m
      = physRename body (bodyPhysTable body) (argName 1) → sEntry.lvm "RSI" = s.lvm m)
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i)
          ++ argMatSeq (twoPtrPairs body (bodyPhysTable body))
          ++ (physBody (fun _ => none) body).map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  refine toLprogPhysAbi_faithful_uniform body nArgs d com bs virt tbl0 inLoadMap rest _
    (twoPtrPairs_sourcesFresh _ _ L hdisjFrame hm0 hm1)
    (twoPtrPairs_destsDistinct _ _ hmemref)
    hbody hcd hmemref L N hch sEntry s hdisjFrame hoff ?_ nRes hnRes
  intro p hp m hmL hpm
  simp only [twoPtrPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · dsimp only
    rw [prologueState_lvm_abiSaveRdi]
    exact hRdi m hmL hpm
  · dsimp only
    rw [prologueState_lvm_abiSaveRsi]
    exact hRsi m hmL hpm

/-! ## 5. The callee-save restore epilogue -/

/-- The explicit end state of running `calleeSaveRestoreEpilogue`: the six
    `MOVQ` restores `RBX ← qsave.RBX`, …, `R15 ← qsave.R15`, as the left fold
    of `prologueStep` over the six `(dst, src)` pairs. -/
def epilogueState {w : Nat} (s : Lstate w) : Lstate w :=
  prologueStep (prologueStep (prologueStep (prologueStep (prologueStep (prologueStep s
    ("RBX", "qsave.RBX"))
    ("RBP", "qsave.RBP"))
    ("R12", "qsave.R12"))
    ("R13", "qsave.R13"))
    ("R14", "qsave.R14"))
    ("R15", "qsave.R15")

/-- Running `calleeSaveRestoreEpilogue` under `lsemStraight` reaches
    `epilogueState`. -/
theorem calleeSaveRestoreEpilogue_lsem {w : Nat} (s : Lstate w) :
    lsemStraight (calleeSaveRestoreEpilogue.map (·.li_i)) s = some (epilogueState s) := by
  simp only [calleeSaveRestoreEpilogue, List.map_cons, List.map_nil, lsemStraight,
    lsemStep, stripWidthTag_MOVQ, evalOperand, applyOpn, epilogueState, prologueStep]

/-- The six registers the callee-save restore epilogue writes. -/
def epilogueWritten : List String := ["RBX", "RBP", "R12", "R13", "R14", "R15"]

/-- The epilogue writes only `epilogueWritten`. -/
theorem calleeSaveRestoreEpilogue_frame {w : Nat} (s : Lstate w) (y : String)
    (hy : y ∉ epilogueWritten) : (epilogueState s).lvm y = s.lvm y := by
  simp only [epilogueWritten, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hy
  simp only [epilogueState, prologueStep, Lstate.lvm_nextPc, Lstate.lvm_setReg,
    if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]

/-- **Whole-function faithfulness with the callee-save restore epilogue.** The
    function body `buildPrologue ++ argMatSeq pairs ++ physBody ++
    calleeSaveRestoreEpilogue ++ Lret :: rest`, as `insertEpilogue` lays it out,
    run under `lsemRun`; the physical result register is read after the restore,
    so it must not be one of the six callee-saved registers (`hResFree`). -/
theorem toLprogPhysAbi_faithful_uniform_epilogue {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N)
    (hResFree : physRename body (bodyPhysTable body) nRes ∉ epilogueWritten) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i)
          ++ calleeSaveRestoreEpilogue.map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  obtain ⟨hnoLret, sB, hrun, hread⟩ :=
    prologue_argMat_body_lsemStraight body nArgs d com bs virt tbl0 inLoadMap pairs
      hfresh hdist hbody hcd hmemref L N hch sEntry s hdisjFrame hoff habi nRes hnRes
  have hnoLretEpi : .Lret ∉ calleeSaveRestoreEpilogue.map (·.li_i) :=
    Lret_not_mem_of_lsemStraight_some _ _ _ (calleeSaveRestoreEpilogue_lsem sB)
  have hnoLret' : .Lret ∉
      ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
        ++ (physBody (fun _ => none) body).map (·.li_i)
        ++ calleeSaveRestoreEpilogue.map (·.li_i)) := by
    intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hnoLret hmem
    · exact hnoLretEpi hmem
  rw [lsemRun_body_ret _ _ _ hnoLret', lsemStraight_append, hrun, Option.bind_some,
    calleeSaveRestoreEpilogue_lsem]
  exact ⟨epilogueState sB, rfl, by rw [calleeSaveRestoreEpilogue_frame sB _ hResFree]; exact hread⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulAssembled
