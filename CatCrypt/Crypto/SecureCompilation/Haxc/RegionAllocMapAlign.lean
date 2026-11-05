/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCertInj

@[expose] public section

set_option autoImplicit false

/-!
# The allocation certificate of a region export against the reference

The allocation `regionLprogC a p none ex` of a region export returns the allocated program and
an allocation certificate, and the check `regionMergeB` of the region gate merges the register
names of the reference `regionCoParts` by the pairs `certMerge` of that certificate. This
module states the certificate on both allocation paths as `allocCertOf` of one body, the body
the allocator scans, and reduces the separation field of the merge conditions `MergeSep` to
conditions on the live ranges of that body.

## Main definitions

* `regionAllocBody`: the body the allocation certifies, on the register-result path and on
  the array-result path.
* `regionAllocTbl`: its allocation table without output stores.
* `MergeSepField`: the field `sep` of `MergeSep` as a proposition on the parts.

## Main results

* `regionLprogC_cert`: the certificate of `regionLprogC` is `allocCertOf` of
  `regionAllocBody` over `regionAllocTbl`.
* `regionCoBody_names_alloc`: the merge pairs of the parts at that certificate send a
  certified name kept at `crossNames (pre ++ ren)` to its `allocName` and every other name to
  itself.
* `outs_regionCoParts`: the targets of the result copy are fixed by the merge when the
  export name of the result register is a hardware register name (field `outs`).
* `sep_regionLprogC`: `MergeSepField` of the parts from the size bound of the allocation, the
  absence of a straight-line call, written names that are plain except a hardware register
  name written by the last instruction, and a common trace position of a live and a written
  certified kept name (`allocName_injOn_liveAt`).
* `exportR_resCopy_defined`: the source and the buffer of the array result copy are
  definitely assigned or argument names when the output array is an argument name.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames regDefs
  arrDefs arrUse? jumpLabel?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference (LiveAt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open RegionAllocMapComplete RegionExportDefInit

/-! ## 1. The certificate of the allocation -/

/-- **The body the allocation of a region export certifies**, for the names `a`, the argument
    count `nArgs`, the result types `ts` and the export `r`, without a callee. With
    `ac := regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] rr` at the
    result alias `rr := resAliasOf none (some a.outArg) ts r.res`, the code given to the
    allocation, and the virtual body `ac` followed by a return: for one register result,
    the liveness instruction reading the argument names `argName j`, `j < nArgs`, followed by
    `canonicalizeMemrefThread` of the virtual body with its call shadows expanded, followed by
    the result-liveness pin `resLivePin` reading the name of the returned operand; for every
    other result, the liveness instruction reading the argument names below
    `a.abiArgs.length` when there are four or more, followed by `canonicalizeMemrefThread` of
    the virtual body preceded by the entry pin `arrBasePins a ac`. -/
def regionAllocBody (a : AbiNames) (nArgs : Nat) (ts : List JasminTy) (r : Exported) : Lcmd :=
  let ac := regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
    (resAliasOf none (some a.outArg) ts r.res)
  let body : Lcmd := ac.map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]
  match ts with
  | [.reg _] =>
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
        ((List.range nArgs).map fun j => (.reg (argName j) : LOperand))⟩]
        ++ canonicalizeMemrefThread (expandCallShadows body)
        ++ resLivePin true [] (r.res.map JasminLsemWidthN.operandName)
  | _ =>
      (if a.abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range a.abiArgs.length).map fun j => (.reg (argName j) : LOperand))⟩]
       else []) ++ canonicalizeMemrefThread (arrBasePins a ac ++ body)

/-- The split configuration of the allocation of a region export with the result types `ts`
    and the body `B`: none for one register result, whose allocation
    `comToLfundefPhysAbiFromVirtCert` does not split, and `bodySplitOpt B` otherwise, the
    configuration of `calleeAllocCert` without a table. -/
def regionSplitAt (ts : List JasminTy) (B : Lcmd) : Option SplitCfg :=
  match ts with
  | [.reg _] => none
  | _ => bodySplitOpt B

/-- At result types other than one register the split configuration is `bodySplitOpt`. -/
theorem regionSplitAt_of_ne {ts : List JasminTy} (B : Lcmd) (h : ∀ w, ts ≠ [.reg w]) :
    regionSplitAt ts B = bodySplitOpt B := by
  unfold regionSplitAt
  split
  · exact (h _ rfl).elim
  · rfl

/-- The allocation table of a body without output stores and reserved vector registers, at
    the result types `ts`: the scan table `physTableOut` at the split configuration
    `regionSplitAt ts B`, with the straight-line call relocation composed in. -/
def regionAllocTbl (ts : List JasminTy) (B : Lcmd) : Array Nat :=
  straightCallComposeTable B (physTableOut B [] [] (split := regionSplitAt ts B))

/-- **The certificate of the allocation of a region export** (`regionLprogC_cert`): when the
    allocation `regionLprogC a p none ex` returns the program `P` and the certificate `cert`,
    the program has an export `r0` with webs `r = regionWebsAt ex none r0`, and on both
    allocation paths the certificate is `allocCertOf` of the body
    `regionAllocBody a Γ.length ts r` over its table. -/
theorem regionLprogC_cert (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r0 r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ cert = allocCertOf (regionAllocBody a Γ.length ts r)
        (regionAllocTbl ts (regionAllocBody a Γ.length ts r)) := by
  unfold regionLprogC regionAllocC at hP
  cases hr : exportR Γ.length a.fname p Γ.length 0 x86Data with
  | none =>
    rw [hr] at hP
    cases hP
  | some r =>
    refine ⟨r, _, rfl, rfl, ?_⟩
    simp only [exportRLfundef, hr, Option.bind_some, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hP
    obtain ⟨-, rfl⟩ := hP
    unfold regionAllocBody regionAllocTbl
    split
    · simp only [comToLfundefPhysAbiFromVirtCert, List.length_map, List.length_range,
        Bool.or_true, ite_true, regionWebsAt_none, regionWebs_res]
      rfl
    · rename_i hts
      dsimp only
      split
      · exact (hts _ rfl).elim
      · rw [regionSplitAt_of_ne _ hts]
        rfl

/-! ## 2. The merge pairs against the certified names -/

/-- **The merge of the parts at the certificate of the allocation** (`regionCoBody_names_alloc`):
    when `regionLprogC a p none ex` returns the certificate `cert`, the program has an export
    `r0` with webs `r = regionWebsAt ex none r0`, and for every layout `σ`, export naming `nm`,
    printed body `body` and result type `t`
    the merge pairs `tau` of the parts `regionCoParts σ nm body t r.code r.res cert` send a
    name `n` to its image `allocName` in the certified body `regionAllocBody a Γ.length ts r`
    when `n` is a certified name of that body that the merge keeps at the names
    `crossNames (pre ++ ren)` of the parts, and to itself otherwise. -/
theorem regionCoBody_names_alloc (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r0 r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ ∀ (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy) (n : String),
        renOf (regionCoParts σ nm body t r.code r.res cert none).tau n
          = if n ∈ allocCertNames (regionAllocBody a Γ.length ts r)
              ∧ certMergeKeep σ (regionCoParts σ nm body t r.code r.res cert none).arrs
                  (crossNames ((regionCoParts σ nm body t r.code r.res cert none).pre
                    ++ (regionCoParts σ nm body t r.code r.res cert none).ren)) n = true then
              allocName (regionAllocBody a Γ.length ts r)
                (regionAllocTbl ts (regionAllocBody a Γ.length ts r)) n
            else n := by
  obtain ⟨r0, r, hr, rfl, rfl⟩ := regionLprogC_cert a p ex hP
  exact ⟨r0, _, hr, rfl, fun σ nm body t n => renOf_certMerge_allocCertOf _ _ _ _ _ _ n⟩

/-- **The targets of the result copy are hardware register names** when the export name
    `nm RA` of a result register `RA` of the layout is one. -/
theorem outs_hw_regionCoParts {σ : AbiLayout} {nm : String → String} (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab)
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) :
    ∀ y ∈ (regionCoParts σ nm body t code res cert callee).outs, isHwRegName y = true := by
  intro y hy
  change y ∈ (regionRet σ nm t res).toList.map Prod.snd at hy
  unfold regionRet at hy
  split at hy
  · split at hy
    · rename_i RA _ hRes
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy
      exact hRA RA hRes
    · simp at hy
  · simp at hy

/-- **The merge fixes the targets of the result copy** (the field `outs` of `MergeSep`) when
    the export name `nm RA` of a result register `RA` of the layout is a hardware register
    name: the merge keeps no hardware register name. -/
theorem outs_regionCoParts {σ : AbiLayout} {nm : String → String} (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab)
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) :
    ∀ y ∈ (regionCoParts σ nm body t code res cert callee).outs,
      renOf (regionCoParts σ nm body t code res cert callee).tau y = y := by
  intro y hy
  have hw := outs_hw_regionCoParts body t code res cert callee hRA y hy
  exact renOf_certMerge_of_not (by simp [certMergeKeep, hw])

/-! ## 3. The separation of the merge from the live ranges -/

/-- **The separation field of the merge conditions** at the parts `d`: at every position `k`
    of the renamed code, a name of the liveness table at `k + 1` and a name the instruction at
    `k` writes have distinct images under the merge `renOf d.tau` unless they are equal. It is
    the field `sep` of `MergeSep`. -/
def MergeSepField (d : CoParts) : Prop :=
  ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
    ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, y ≠ x → renOf d.tau y ≠ renOf d.tau x

/-- **The separation of the merge from the live ranges of the allocation**
    (`sep_regionLprogC`). Let `regionLprogC a p none ex` return the certificate `cert`, let
    `r` be the webs `regionWebsAt ex none r0` of the export `r0` and `B := regionAllocBody a
    Γ.length ts r` the certified body, and let
    `d` be the parts `regionCoParts σ nm body t r.code r.res cert`. Under the export name
    `nm RA` of a result register `RA` of the layout being a hardware register name, the size
    bound `hfit` of the allocation of `B`, a body `B` without a straight-line call, names
    written in the renamed code that are plain (`PlainName`) except a hardware register name
    written by the last instruction (the result move `nm RA := res` of a register result), and
    the two conditions on the live ranges of `B`: a live name and a written name, both
    certified and kept by the merge, are live at one position of the trace
    `bodyTraceOut B []`; and a live name that is not plain differs from the image of a
    certified written name kept by the merge, the merge satisfies the field `sep` of
    `MergeSep` (`MergeSepField`). After the last instruction only the targets of the result
    copy are live, and the merge fixes them and every hardware register name. -/
theorem sep_regionLprogC (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r0 r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r0
      ∧ r = regionWebsAt ex none r0
      ∧ ∀ (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy),
        let B := regionAllocBody a Γ.length ts r
        let d := regionCoParts σ nm body t r.code r.res cert none
        let K : String → Prop := fun n => n ∈ allocCertNames B
          ∧ certMergeKeep σ d.arrs (crossNames (d.pre ++ d.ren)) n = true
        (∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) →
        numGPRegs + (physLiveItems (bodyTraceOut B [])).length ≤ vectorBase →
        bodyStraightCall B = false →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ x ∈ regDefs i, PlainName x
            ∨ (k + 1 = (d.pre ++ d.ren).length ∧ isHwRegName x = true)) →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, y ≠ x → K y → K x →
            ∃ pos, LiveAt (bodyTraceOut B []) pos (nameSlot B y)
              ∧ LiveAt (bodyTraceOut B []) pos (nameSlot B x)) →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, ¬ PlainName y → K x →
            y ≠ allocName B (regionAllocTbl ts B) x) →
        MergeSepField d := by
  obtain ⟨r0, r, hr, rfl, rfl⟩ := regionLprogC_cert a p ex hP
  refine ⟨r0, _, hr, rfl, fun σ nm body t => ?_⟩
  intro B d K hRA hfit hsc hpl hcov hnp k i hk hi y hy x hx hyx
  rcases hpl k i hk hi x hx with hxp | ⟨hlast, hxw⟩
  · have hcls : bodyStraightCall B = true →
        ∀ (s : Nat) (h : s < (physTableOut B [] [] (split := regionSplitAt ts B)).size),
          slotIsVec (bodyVecSlots B) s
            = decide (vectorBase ≤ (physTableOut B [] [] (split := regionSplitAt ts B))[s]) :=
      fun h => absurd h (by simp [hsc])
    have hsp : bodyStraightCall B = true →
        gpSpillBase (bodyVecSlots B) (physTableOut B [] [] (split := regionSplitAt ts B))
          + numGPRegs ≤ vectorBase :=
      fun h => absurd h (by simp [hsc])
    have hIr : ¬ K y → K x → y ≠ allocName B (regionAllocTbl ts B) x := by
      intro _ hKx
      by_cases hyp : PlainName y
      · exact (allocName_ne hyp (Ne.symm hyx)).symm
      · exact hnp k i hk hi y hy x hx hyp hKx
    by_cases hb : K y ∧ K x
    · obtain ⟨pos, h1, h2⟩ := hcov k i hk hi y hy x hx hyx hb.1 hb.2
      exact certMerge_ne_of_liveAt (outStoreMap := []) (reservedVec := [])
        (split := regionSplitAt ts B) (pos := pos) hfit
        hcls hsp hyx (fun _ _ _ _ => ⟨h1, h2⟩) (fun _ _ => allocName_ne hxp hyx) hIr
    · exact certMerge_ne_of_liveAt (outStoreMap := []) (reservedVec := [])
        (split := regionSplitAt ts B) (pos := 0) hfit
        hcls hsp hyx (fun h1 h2 h3 h4 => absurd ⟨⟨h1, h2⟩, h3, h4⟩ hb)
        (fun _ _ => allocName_ne hxp hyx) hIr
  · have hy' : y ∈ tabAt (liveRegTab (d.pre ++ d.ren) d.outs) (d.pre ++ d.ren).length := by
      rw [← hlast]
      exact hy
    rw [liveRegTab_end] at hy'
    have hxf : renOf d.tau x = x := renOf_certMerge_of_not (by simp [certMergeKeep, hxw])
    rw [outs_regionCoParts body t _ _ _ none hRA y hy', hxf]
    exact hyx

/-! ## 4. The premises of the input of the allocation -/

/-- **The result copy reads defined names**: for an export `r` of a program on x86 and a
    certificate `D` of its code that holds the names of the returned operands at the end, the
    source and the buffer of the array result copy `resCopyOf a.outArg t r.code r.res` are in
    `D` at the end or in `ExportE`, when the output array `a.outArg` is an argument name below
    `Γ.length`. The source is the name of the returned register operand. -/
theorem exportR_resCopy_defined (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (a : AbiNames)
    (hout : ArgName Γ.length a.outArg) {D : Nat → String → Prop}
    (hres : ∀ x ∈ r.res.flatMap opNames, D r.code.length x ∨ ExportE Γ.length r.code x) :
    ∀ t src Dn m, ts = [t] → resCopyOf a.outArg t r.code r.res = some (src, Dn, m) →
      (D r.code.length src ∨ ExportE Γ.length r.code src)
        ∧ (D r.code.length Dn ∨ ExportE Γ.length r.code Dn) := by
  intro t src Dn m _ hc
  unfold resCopyOf at hc
  split at hc
  · rename_i op hr _
    split_ifs at hc
    cases hc
    have hmem : op ∈ r.res := by
      rw [hr]
      exact List.mem_singleton_self op
    refine ⟨hres _ (List.mem_flatMap.mpr ⟨op, hmem, ?_⟩), Or.inr (Or.inl hout)⟩
    have hop := exportR_res_isReg Γ.length fn p _ _ r h op hmem
    rw [hop]
    simp [opNames, JasminLsemWidthN.operandName]
  · cases hc

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign
