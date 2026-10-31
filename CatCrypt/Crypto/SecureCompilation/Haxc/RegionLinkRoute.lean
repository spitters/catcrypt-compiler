/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets

@[expose] public section

set_option autoImplicit false

/-!
# Correctness of a compiled body with one linked kernel

A program with a `call` that `compileRegion` compiles at the callee data `c` of one linked
word kernel runs on its bytes through the call of the kernel code: the run of
the reference of the gate at the procedure table (`RegionLinkCompose.regionCo_bytes_callee`)
gives the run of the image of the calling body (`RegionLinkCompose.calleeBody_imgRun_at`),
which the linked image theorem carries to the decoded bytes of the caller followed by the
kernel block (`CheckedIsaCall.haltsC_of_linkedChecksK`), and to the caller program under
the oracle of the kernel guarded by its precondition
(`ImageAddrCall.haltsO_of_linkedChecks`). A kernel with an out result, which writes the
array of one of its arguments, takes the same route through
`ImageAddrCallOutChain.haltsO_of_linkedChecks_out` at the call site `calleeSite`.

The declarations lie in the namespace `Haxc.RegionLinkCall`; the module `RegionLinkCall`
states the runs of the bytes of `compileA` and the compiler theorems over them.

## Main results

* `reloadOf_slotRen`, `accArr_slotRen`: the reload scan and the array of an access at a
  slot map with renamed arrays.
* `cellBody_of_cellArrsOf_nil`, `cellArrsOf_nil_of_regionCells_nil`: without a cell array of
  the region back half, the cell body of a printed body is the body.
* `imgGateCB_congr`, `imgGateCB_frameMark`: the gate of a calling body reads only which
  names have a frame word.
* `compileRegion_spec_linked`: a result of `compileRegion σ a p [c]` on a program with a
  `call` has a word-array result, an export and a printed body that passes `regionCoB` at
  `c`, with bytes `calleeBytes`.
* `calleeBytes_some`: the byte hypotheses of the linked image theorem from `calleeBytes`,
  with the prologue as first instruction of the caller program.
* `calleeBytes_items`: the caller part of `calleeBytes` is the bytes of an item list whose
  layout resolves to the caller program.
* `calleeSpec_guard`: a callee guarded by its precondition meets its specification.
* `compileRegion_correct_linked`: the bytes of a calling body with one linked word kernel
  whose code meets its word interface halt through the call, and the caller halts under the
  oracle of the guarded kernel, in a state from which the layout reads back the source value
  of the result.
* `compileRegion_singleton`, `linkedEnv`, `extAgree_linkedDecls_linkTable`,
  `haxEntry_run_linkedEnv`: the callee of a calling body alone, and the source run of a
  module as a run of the chain's program at the environment of its linked functions alone.
* `wordCallee_linkedSummary`, `LinkedFn.CallSitePre`, `LinkedWordKernel`: the summary of a
  linked word kernel, the precondition of a linked function under the resources of its
  calls, and the machine contract of a linked function with scalar parameters and a word
  result, whose code meets its word interface and whose precondition holds under the
  resources of every call at whose arguments its meaning is defined.
* `regions_of_entryAt`: the entry conditions of a layout with at most one read-only pointer
  region from the resources of a call.
* `LinkedWordKernel.of_sig`, `LinkedWordKernel.wordCallee`: a linked word kernel from code
  meeting the interface of its data, and its summary at its call sites.
* `find?_name_of_nodup`: the linked function of a name among functions with distinct names.
* `linkedEnvAt`, `summaryTable`, `callsTo`, `procsAgree_summaryTable`: the environment and the
  table of one linked function alone, and their agreement.
* `callsTo_of_exportR`, `callsTo_of_compileRegion`, `denoteAt_linkedEnvAt`: every `call` of a
  program the back half compiles at one callee names the callee, and such a program denotes
  the same at the environment of the callee alone as at that of all linked functions.
* `linkedSummary_eq_outSummary`: the summary of a linked function with an array result is
  its out summary `LinkedFnCallee.outSummary`.
* `CallRoom`, `callRoom_of_forall`: the precondition of a linked function at its call
  sites, and its instance at a precondition that holds at every entry state.
* `compileRegion_correct_linked_outO`: the program of a calling body with one linked out
  kernel, one of whose parameters is the destination array and which satisfies its
  precondition at its call sites, halts under the oracle of the guarded kernel in a state
  from which the layout reads back the source value of the result;
  `compileRegion_correct_linked_out`: with the kernel the leaky runs of its decoded bytes,
  the bytes of the calling body halt through the call.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (reloadOf accArr dstHitB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotRen slotArrOf
  slotArrOf_some)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody cellMove
  cellBody_getElem?)

/-! ## 1. The cell body of a calling body with no cell array -/

/-- The scan `reloadOf` reads the slot map only through which names it holds, so it is the
    same at a slot map with renamed arrays. -/
theorem reloadOf_slotRen (sl : String → Option (String × Nat)) (ren : String → String)
    (body : Lcmd) (k : Nat) (b : String) :
    reloadOf (slotRen sl ren) body k b = reloadOf sl body k b := by
  have hn : ∀ q, (slotRen sl ren q).isNone = (sl q).isNone := fun q => by
    simp [slotRen]
  have hs : ∀ q, (slotRen sl ren q).isSome = (sl q).isSome := fun q => by
    simp [slotRen]
  have hd : ∀ b, dstHitB (slotRen sl ren) b = dstHitB sl b := fun b => funext fun x => by
    cases x <;> simp [dstHitB, hs]
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    simp only [reloadOf, hn, hd, ih]

/-- The array of an access at a slot map with renamed arrays is the renamed array. -/
theorem accArr_slotRen (sl : String → Option (String × Nat)) (ren : String → String)
    (body : Lcmd) (k : Nat) (b : String) :
    accArr (slotRen sl ren) body k b = (accArr sl body k b).map fun p => (ren p.1, p.2) := by
  simp only [accArr, reloadOf_slotRen]
  cases reloadOf sl body k b <;> simp [slotRen]

/-- An access whose base register holds the pointer of an array of `slotArrOf σ nm` is an
    access of a cell array of `σ`: a body with an access at position `k` whose array is
    found has that array among `cellArrsOf`. -/
theorem mem_cellArrsOf_of_accArr {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {k : Nat} {i : Linstr} (hb : body[k]? = some i) {B : String}
    (hB : (JasminLsemAddrMem.cellA? i.li_i).any (fun
      | .ld _ B' _ => B' == B
      | .st B' _ _ => B' == B
      | .lea _ _ _ => false) = true)
    {A : String} {n : Nat} (hA : accArr (slotArrOf σ nm) body k B = some (A, n)) :
    (A, n) ∈ cellArrsOf (slotArrOf σ nm) (X86Backend.ImageStraightCells.cellArrs σ) body := by
  obtain ⟨q, -, hq⟩ := Option.bind_eq_some_iff.mp hA
  obtain ⟨j, a, hj, hk, rfl, -⟩ := slotArrOf_some hq
  refine List.mem_filter.mpr ⟨X86Backend.ImageAddrRouteW.mem_cellArrs hj hk, ?_⟩
  refine List.any_eq_true.mpr ⟨k, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hb).1, ?_⟩
  rw [hb]
  cases hc : JasminLsemAddrMem.cellA? i.li_i with
  | none => rw [hc] at hB; cases hB
  | some op =>
    rw [hc] at hB
    cases op with
    | ld D B' off =>
      simp only [Option.any_some, beq_iff_eq] at hB
      subst hB
      simp [hc, hA]
    | st B' off S =>
      simp only [Option.any_some, beq_iff_eq] at hB
      subst hB
      simp [hc, hA]
    | lea D B' off => simp at hB

/-- **The cell body of a body without cell array is the body.** If no array of `σ` is
    accessed through a cell access of `body` (`cellArrsOf` is empty), then the cell body at
    the slot map `slotArrOf σ nm` with its arrays renamed by `ren` is `body`. -/
theorem cellBody_of_cellArrsOf_nil {σ : AbiLayout} {nm : String → String}
    (ren : String → String) {body : Lcmd}
    (h : cellArrsOf (slotArrOf σ nm) (X86Backend.ImageStraightCells.cellArrs σ) body = []) :
    cellBody (slotRen (slotArrOf σ nm) ren) body = body := by
  refine List.ext_getElem? fun k => ?_
  rw [cellBody_getElem?]
  cases hb : body[k]? with
  | none => rfl
  | some i =>
    simp only [Option.map_some, Option.some.injEq]
    unfold cellMove
    have hnone : ∀ B, (JasminLsemAddrMem.cellA? i.li_i).any (fun
        | .ld _ B' _ => B' == B
        | .st B' _ _ => B' == B
        | .lea _ _ _ => false) = true → accArr (slotArrOf σ nm) body k B = none := by
      intro B hB
      cases hA : accArr (slotArrOf σ nm) body k B with
      | none => rfl
      | some p =>
        have := mem_cellArrsOf_of_accArr hb hB hA
        rw [h] at this
        cases this
    split
    · rename_i D B off hc
      rw [accArr_slotRen, hnone B (by simp [hc])]
      rfl
    · rename_i B off S hc
      rw [accArr_slotRen, hnone B (by simp [hc])]
      rfl
    · rfl

/-- Without a cell array of the region back half, no array of `σ` is accessed through a cell
    access of the printed body. -/
theorem cellArrsOf_nil_of_regionCells_nil {σ : AbiLayout} {nm : String → String}
    {ps : List (String × String)} {body : Lcmd} {code : List JasminLsemMem.LinstrRM}
    (h : regionCells σ nm ps body code = []) :
    cellArrsOf (slotArrOf σ nm) (X86Backend.ImageStraightCells.cellArrs σ) body = [] := by
  unfold regionCells at h
  dsimp only at h
  split_ifs at h with hc
  · exact List.isEmpty_iff.mp hc
  · exfalso
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (fun e => hc (List.isEmpty_iff.mpr e))
    have hp' : p ∈ X86Backend.ImageStraightCells.cellArrs σ := (List.mem_filter.mp hp).1
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
    exact h p hp' (by simp [hp])

/-! ## 2. The gate of a calling body at the frame of an entry state -/

/-- The gate `imgGateCB` reads the frame map only through which names have a frame word. -/
theorem imgGateCB_congr {frame frame' : String → Option (BitVec 64)}
    (h : ∀ q, (frame q).isSome = (frame' q).isSome)
    (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    X86Backend.ImageAddrCall.imgGateCB frame slotArr body
      = X86Backend.ImageAddrCall.imgGateCB frame' slotArr body := by
  have hn : ∀ q, (frame q).isNone = (frame' q).isNone := fun q => by
    have := h q; cases e : frame q <;> cases e' : frame' q <;> simp_all
  have hi : ∀ k x, X86Backend.ImageAddrSim.instrGateB frame slotArr body k x
      = X86Backend.ImageAddrSim.instrGateB frame' slotArr body k x := by
    intro k x
    simp only [X86Backend.ImageAddrSim.instrGateB, X86Backend.ImageAddrFrame.icase_congr h,
      X86Backend.ImageAddrFrame.regGateB_congr h, hn]
  simp only [X86Backend.ImageAddrCall.imgGateCB, hi]

/-- The gate of a calling body at the restricted frame of the body at any stack pointer is
    the gate at `frameMark (frameNames body)`. -/
theorem imgGateCB_frameMark (body : Lcmd) (r : BitVec 64)
    (slotArr : String → Option (String × Nat)) :
    X86Backend.ImageAddrCall.imgGateCB (X86Backend.ImageAddrFrame.frameIn body
        (X86Backend.DecodePrintedAddr.frameP (X86Backend.LprogBytesDecode.Params.ofBody body) r))
        slotArr body
      = X86Backend.ImageAddrCall.imgGateCB
        (X86Backend.ImageAddrFrame.frameMark (X86Backend.ImageAddrFrame.frameNames body))
        slotArr body :=
  imgGateCB_congr (fun q => (X86Backend.ImageAddrFrame.frameMark_isSome body r q).symm)
    slotArr body

/-! ## 3. The back half at one linked function -/

/-- A program for which `regionCallee` finds a callee has a word-array result. -/
theorem regionCallee_some_stackArr {linked : List CalleeData} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {code : List JasminLsemMem.LinstrRM}
    {c : CalleeData} (h : regionCallee linked p code = some (some c)) :
    ∃ w m, t = .stackArr w m := by
  unfold regionCallee at h
  split at h
  · cases h
  · split at h
    · exact ⟨_, _, rfl⟩
    · cases h

/-- **A result of the back half at one linked function on a program with `call`.** For a
    result of `compileRegion σ a p [c]` on a program `p` with a `call`, the result type is a
    word array, the program passes `regionExportableB`, has an export `r0` with the webs
    `r = regionWebs (regionWebsEx σ exportReg) r0 (calleeAA (some c)) (calleeAO (some c))`,
    and a printed body `b` whose bytes at the callee `c` (`calleeBytes`) are the result's
    bytes and that passes the gate `regionCoB` at `c` and the function name `a.fname` at the
    code and returned operands of `r` and the allocation certificate `cert` of
    `regionLprogC`. -/
theorem compileRegion_spec_linked {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {c : CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p [c] = some (P, bytes))
    (hcf : p.callFree = false) :
    (∃ w m, t = .stackArr w m) ∧ regionExportableB (legalizeRegion p) = true
      ∧ ∃ r0 r b cert, exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 = some r0
      ∧ regionWebs (regionWebsEx σ exportReg) r0 (calleeAA (some c)) (calleeAO (some c)) = r
      ∧ calleeBytes (some c) b = some bytes
      ∧ regionCoB σ exportReg b t r.code r.res cert (some c) a.fname = true
      ∧ ∃ P0, regionLprogC a (legalizeRegion p) (some c) (regionWebsEx σ exportReg)
          = some (P0, cert) := by
  unfold compileRegion at h
  split at h
  · rename_i hB
    split at h
    · rename_i r hr
      split at h
      · rename_i callee hc
        cases callee with
        | none =>
          rw [← legalizeRegion_callFree_eq, regionCallee_callFree hc] at hcf
          cases hcf
        | some c' =>
          obtain rfl : c' = c := List.mem_singleton.mp (regionCallee_mem hc)
          split at h
          · rename_i P0 cert hP
            obtain ⟨b, hbs, hg⟩ := regionEncode_spec_callee h
            rw [Bool.and_eq_true] at hg
            exact ⟨regionCallee_some_stackArr hc, hB, r, _, b, cert, hr, rfl, hbs, hg.1, P0, hP⟩
          · cases h
      · cases h
    · cases h
  · cases h

/-- **The bytes of a calling body.** The bytes `calleeBytes` at the callee `c` of a printed
    body `b` are the bytes of the relocating encoder at the symbol map `calleeSym c b`
    followed by the code of `c`, which is nonempty; the instructions of `b` have the shapes
    `ds`; and the items of `b` at that symbol map pass the branch check and denote a
    program `prog` whose first instruction is the prologue `leaFrame` of the frame of `b`.
    These are the byte hypotheses of `CheckedIsaCall.haltsC_of_linkedChecksK`. -/
theorem calleeBytes_some {c : CalleeData} {b : Lcmd} {bytes : List (BitVec 8)}
    (h : calleeBytes (some c) b = some bytes) :
    bytes = X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym c b) b ++ c.bytes
      ∧ c.bytes ≠ []
      ∧ ∃ ds prog,
        X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
        ∧ X86Backend.LprogBytesLinkReloc.branchOKReloc
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)
          (X86Backend.LprogBytesDecode.decCount
            (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
              (X86Backend.LprogBytesDecode.Params.ofBody b) b ds))
          (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym c b) b).length 0
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds) = true
        ∧ X86Backend.LprogBytesLinkReloc.expectedReloc
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)
          (X86Backend.LprogBytesDecode.decCount
            (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
              (X86Backend.LprogBytesDecode.Params.ofBody b) b ds))
          (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym c b) b).length
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds) = some prog
        ∧ prog[0]? = some (.op (X86Backend.PhysAbiShape.leaFrame
          (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody b).frame)))) := by
  simp only [calleeBytes] at h
  split at h
  · rename_i hc
    obtain rfl := (Option.some.inj h).symm
    simp only [calleeLinkB, Bool.and_eq_true] at hc
    obtain ⟨hne, hm⟩ := hc
    refine ⟨rfl, by simpa using hne, ?_⟩
    cases hss : X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b
      with
    | none => simp only [hss] at hm; cases hm
    | some ds =>
      simp only [hss, Bool.and_eq_true] at hm
      obtain ⟨hbr, hP⟩ := hm
      obtain ⟨prog, hprog⟩ := Option.isSome_iff_exists.mp hP
      refine ⟨ds, prog, rfl, hbr, hprog, ?_⟩
      have h2 := hprog
      conv at h2 => lhs; arg 4; unfold X86Backend.LprogBytesLinkReloc.fundefItemsRelocL
      simp only [X86Backend.LprogBytesLinkReloc.expectedReloc,
        X86Backend.LprogBytesLinkReloc.expectedRelocMap, X86Backend.LprogBytesDecode.mkLea,
        Option.map_eq_some_iff] at h2
      obtain ⟨rest, -, rfl⟩ := h2
      rfl
  · cases h

/-- **The bytes of a calling body as items.** Let the bytes `calleeBytes` at the callee `c`
    of a printed body `b` of the class `ImageAddrCall.printedAddrCB` at the frame of `c` be
    `bytes`, and let `prog` be the program `calleeProg c b` of the function. Then `bytes`
    are the bytes of an item list `items` (the items `fundefItemsRelocL` of `b`) followed by
    the code of `c`; every item of `items` passes `ItemOK`; and the layout of `items`
    resolves to `prog` inside the layout of `items` followed by any layout whose first
    instruction starts at the byte length of `items`
    (`LprogBytesLinkReloc.encodeLfundefBytesReloc_eq_itemBytesL`,
    `LprogBytesLinkReloc.resolveAll_layout_reloc`). -/
theorem calleeBytes_items {c : CalleeData} {b : Lcmd} {bytes : List (BitVec 8)}
    (h : calleeBytes (some c) b = some bytes)
    (hpr : X86Backend.ImageAddrCall.printedAddrCB c.frame b = true)
    {prog : List X86Backend.LprogBytesDecode.RInstr} (hprog : calleeProg c b = some prog) :
    ∃ items : List X86Backend.LprogBytesDecode.Item,
      bytes = X86Backend.LprogBytesDecode.itemBytes items ++ c.bytes
      ∧ (∀ it ∈ items, X86Backend.LprogBytesDecode.ItemOK it)
      ∧ ∀ e x tl, X86Backend.LprogBytesDecode.resolveAll
          (X86Backend.LprogBytesDecode.layoutAt 0 items
            ++ ((X86Backend.LprogBytesDecode.itemBytes items).length, e, x) :: tl)
          (X86Backend.LprogBytesDecode.layoutAt 0 items) = some prog := by
  obtain ⟨rfl, -, ds, prog', hss, hbr, hP, -⟩ := calleeBytes_some h
  have hpp : prog' = prog := by
    simp only [calleeProg, hss] at hprog
    rw [hP] at hprog
    exact Option.some.inj hprog
  subst hpp
  obtain ⟨hsaves, hF0, hFr⟩ := X86Backend.ImageAddrCall.printedAddrCB_reloc hpr
  have hsh := X86Backend.LprogBytesLinkReloc.relocDShapeOK_of_shapes _ hss
  have hbytes := X86Backend.LprogBytesLinkReloc.encodeLfundefBytesReloc_eq_itemBytesL
    (calleeSym c b) b ds hsaves hsh
  have hok := X86Backend.LprogBytesLinkReloc.fundefItemsRelocL_ok (calleeSym c b)
    (X86Backend.LprogBytesDecode.Params.ofBody b) b ds hF0 hFr hsh
  refine ⟨_, by rw [hbytes], hok, fun e x tl => ?_⟩
  rw [hbytes] at hbr hP
  rw [X86Backend.LprogBytesLinkReloc.resolveAll_layout_reloc _ hok _ _ _ (fun q hq => ?_) _ 0
    hbr]
  · exact hP
  · have hlt : ∀ z ∈ X86Backend.LprogBytesDecode.layoutAt 0
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds),
        z.1 < (X86Backend.LprogBytesDecode.itemBytes
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)).length :=
      fun z hz => by simpa using X86Backend.LprogBytesLink.layoutAt_start_lt _ hok 0 z hz
    have hnone : (X86Backend.LprogBytesDecode.layoutAt 0
        (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
          (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)).findIdx?
        (fun z => decide (z.1 = (X86Backend.LprogBytesDecode.itemBytes
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym c b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)).length)) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro z hz
      have := hlt z hz
      exact decide_eq_false (by omega)
    simp [List.findIdx?_append, hnone, List.findIdx?_cons, hq,
      X86Backend.LprogBytesDecode.layoutAt_length]

/-! ## 4. Correctness of a calling body with one linked word kernel -/

section Linked

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (ProcTable ProcSummary)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (keepCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee (wordSummary wordSig)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel (regionPre)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)

/-- **A callee guarded by its precondition meets the specification of the callee.** The runs
    of `X` from entry states that satisfy `c.pre` meet `c` when the runs of `X` do. -/
theorem calleeSpec_guard {X : X86Backend.Callee.CalleeRun} {c : X86Backend.Callee.CalleeSig}
    (h : X86Backend.Callee.CalleeSpec X c) :
    X86Backend.Callee.CalleeSpec (fun s tr s' => c.pre s ∧ X s tr s') c where
  halts s hs := let ⟨tr, s', hx⟩ := h.halts s hs; ⟨tr, s', hs, hx⟩
  rsp s tr s' hp hx := h.rsp s tr s' hp hx.2
  keep s tr s' hp hx := h.keep s tr s' hp hx.2
  frame s tr s' hp hx := h.frame s tr s' hp hx.2
  post s tr s' hp hx := h.post s tr s' hp hx.2
  ct s₁ s₂ t₁ t₂ s₁' s₂' hp₁ hp₂ hpub hx₁ hx₂ := h.ct s₁ s₂ t₁ t₂ s₁' s₂' hp₁ hp₂ hpub hx₁.2 hx₂.2

/-- **Correctness of a calling body with one linked word kernel.** Let `c` be the callee
    data of the linked function `l`, whose layout passes the arguments in the
    general-purpose names `c.args` as scalars and the result in the general-purpose name
    `c.resReg`, which it clobbers (`WordLayout`). Let the code of `c` decode to the block
    `qk` without `call`, whose leaky runs under `ctRegime` meet the word interface
    `wordSig l c.args c.resReg` and write only among the `c.frame` bytes below the entry
    stack register; let `pr` be a summary with as many arguments as `c` that reads that
    interface at entry states satisfying `room` (`WordCallee`), and let every entry state
    of a call satisfy `room`.

    Let `compileRegion σ a p [c]` give the bytes `bytes` on a program `p` with a `call`,
    and let the table `T`
    agree with the call environment `Ec`, hold summaries on words with word results only,
    and give the symbol of `c` the summary `pr`. From every entry state `sa`
    satisfying `σ.Regions`, at every valuation `V` that `σ` reads off `sa` at which `p`
    denotes `v` in `Ec` at some fuel, the bytes decode to the program `pc` of the caller
    followed by the shifted block `qk`, and:

    * the linked program halts through the call (`HaltsC`) from `sa` at index `0` in a state
      from which `σ` reads back the source value of the result;
    * the program `pc` halts from `sa` at index `0`, its call answered by the oracle
      `oracleAt pc.length` of the leaky runs of `qk` under `ctRegime` from entry states that
      satisfy the precondition of `wordSig l c.args c.resReg` (the guarded callee
      `DecodedCTCall.guarded`), in a state from which `σ` reads back the same value.

    The reference run is `regionCo_bytes_callee`, the image run is
    `calleeBody_imgRun_at`, the run through the call is
    `CheckedIsaCall.haltsC_of_linkedChecksK` and the run under the oracle is
    `ImageAddrCall.haltsO_of_linkedChecks`, both at the interface `wordSig l c.args c.resReg`,
    with the end the words of the arrays of the slot map at their bases; the first step is
    the prologue `leaFrame` of the caller. -/
theorem compileRegion_correct_linked {l : CatCrypt.Crypto.Hax.LinkedFn}
    {c : CalleeData} (hc : l.calleeData = some c)
    (hL : X86Backend.LinkedFnCallee.WordLayout l c.args c.resReg) {qk : List RInstr}
    (hqk : decodeLprog c.bytes = some qk) (hnc : ∀ tg, RInstr.call tg ∉ qk)
    (hX : X86Backend.Callee.CalleeSpec (X86Backend.Callee.runOf ctRegime qk)
      (wordSig l c.args c.resReg))
    (hF : X86Backend.ImageAddrCall.FootBelow (wordSig l c.args c.resReg) c.frame)
    {pr : ProcSummary} {room : AState → Prop}
    (hw : X86Backend.ImageAddrCall.WordCallee (wordSig l c.args c.resReg) c.resReg pr room)
    (hpar : pr.arity = c.args.length)
    (hroom : ∀ ret (sA : AState), room (entryOf ret sA))
    {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion σ a p [c] = some (P, bytes)) (hcf : p.callFree = false)
    {Ec : CallEnv jasminDialect} {T : ProcTable} (hT : ProcsAgree Ec T)
    (hwo : ∀ f pr, T f = some pr → pr.WordOnly) (hrw : ∀ f pr, T f = some pr → pr.RetWord)
    (hTc : T c.name = some pr)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denoteAt Ec fuel V = some v) :
    ∃ pc : List RInstr,
      decodeLprog bytes = some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length qk)
      ∧ (∃ sa', HaltsC aMachine (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length qk) 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
      ∧ ∃ sa', X86Backend.Callee.HaltsO aMachine
          (X86Backend.Callee.oracleAt pc.length (fun s tr s' =>
            (wordSig l c.args c.resReg).pre s ∧ X86Backend.Callee.runOf ctRegime qk s tr s'))
          pc 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)) := by
  obtain ⟨⟨w, m, rfl⟩, hB, rx0, r, b, cert, hrx, hwb, hbs, hg, -⟩ :=
    compileRegion_spec_linked h hcf
  generalize hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCode (some c) r.code) r.res
    cert (some c) = d
  -- The array positions and the result of `c`: word arguments and a word result.
  have hcaa : c.arrArgs = fun _ => none := by
    rw [(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc).2.2.2.2.2.2.2.2.2.2.2]
    apply CatCrypt.Crypto.Hax.insArrArgs_of_scalars
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
    have hm : (a.reg, a.kind) ∈ c.args.map fun w => (phys w, ArgKind.scalar) := by
      rw [← hL.args]
      exact List.mem_map_of_mem (f := fun a => (a.reg, a.kind)) ha
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hm
    exact (Prod.mk.inj hw).2.symm
  obtain ⟨r0, hr0⟩ : ∃ r, c.res = .reg r := by
    cases hcr : c.res with
    | reg r => exact ⟨r, rfl⟩
    | out n =>
        have h1 := (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc).1
        rw [hcr] at h1
        simp [CatCrypt.Crypto.Hax.LinkedFn.calleeRes, hL.result] at h1
  have haa : LprogIsa.Isa.procArrArgs T = calleeAA (some c) := by
    funext f
    cases hf : T f with
    | none => simp [LprogIsa.Isa.procArrArgs, calleeAA, hf, hcaa]
    | some pr =>
        have hw : pr.arrArgs = fun _ => none := hwo f pr hf
        simp [LprogIsa.Isa.procArrArgs, calleeAA, hf, hw, hcaa]
  have hao : LprogIsa.Isa.procOut T = calleeAO (some c) := by
    funext f
    cases hf : T f with
    | none => simp [LprogIsa.Isa.procOut, calleeAO, hf, hr0]
    | some pr =>
        have hw : pr.out = none := hrw f pr hf
        simp [LprogIsa.Isa.procOut, calleeAO, hf, hw, hr0]
  obtain ⟨k, u, hu, hcb, hsep, hrelF, hacorr, hpc0, hbnd, hread⟩ :=
    RegionLinkCompose.regionCo_bytes_callee (regionExportableB_sound hB) hrx hwb hg hd hT
      (fun f pr h => LprogIsa.ProcSummary.kinded_of_retWord (hrw f pr h)) haa hao hTc sa V hV
      hreg fuel ((legalizeRegion_denoteAt Ec fuel p V).trans hv)
  -- The conjuncts of the gate.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg'
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  rw [hcells] at himg
  simp only [renImageB, X86Backend.ImageAddrRouteW.slotArrC_nil, calleeImgB,
    Bool.and_eq_true] at himg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hphys⟩, hcls, hgate⟩, -⟩, hent⟩, -⟩, -⟩ := himg
  -- The printed body has no cell access of an array of the slot map.
  have hcellsE : d.cells = regionCells σ exportReg d.ps b (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hcb0 : cellBody (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b = b :=
    cellBody_of_cellArrsOf_nil _ (cellArrsOf_nil_of_regionCells_nil (hcellsE ▸ hcells))
  rw [hcb0] at hphys hrelF
  -- The fields of the callee data.
  obtain ⟨-, -, -, hcclob, -⟩ := CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc
  have hcsig : c.res.reg? = some c.resReg := by
    simp only [CalleeData.resReg, hr0, CalleeRes.reg?]
  -- The checks of the calling body.
  have hcb' := hcb
  simp only [calleeBodyB, calleeSite_of_reg hr0 hcaa, calleeDeadB_of_reg hr0 hcaa,
    Bool.and_eq_true] at hcb'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hsi⟩, -⟩, -⟩, hsites⟩, ⟨hdead, -⟩⟩, hflags⟩, hcond⟩, hseg⟩,
    hlive⟩, -⟩, -⟩, hroomB⟩, hnn⟩ := hcb'
  -- The bytes of the calling body.
  obtain ⟨rfl, hne, ds, prog, hss, hbr, hP, hp0⟩ := calleeBytes_some hbs
  -- The image run at the table.
  obtain ⟨fuel', t', himgrun, hobs⟩ := RegionLinkCompose.calleeBody_imgRun_at hcb hTc hpar
    ⟨⟨X86Backend.ImageAddrRoute.entryV σ (X86Backend.ImageAddrRoute.frameE b sa) sa
      (X86Backend.ImageAddrRoute.unren d.ps), a.fname⟩, false⟩
    u rfl rfl hbnd k hu (.inl (hrw _ _ hTc))
  rw [calleeSite_of_reg hr0 hcaa] at himgrun
  -- The caller separation at the renamed slot map.
  have RF := X86Backend.ImageAddrRoute.renB_spec hren
  have E := X86Backend.ImageAddrRoute.entryB_spec hent sa
  have hun : ∀ q A n, slotArrOf σ exportReg q = some (A, n) →
      X86Backend.ImageAddrRoute.unren d.ps (renOf d.ps A) = A := by
    intro q A n hq
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some hq
    exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
  have hS0 := X86Backend.CalleeStackRoom.callerSep_of_regions E.rs hreg hroomB hnn
    (slotArr := slotArrOf σ exportReg) E.len
  have hS : X86Backend.ImageAddrCall.CallerSep (X86Backend.ImageAddrRoute.frameE b sa)
      (slotRen (slotArrOf σ exportReg) (renOf d.ps)) (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
      (X86Backend.DecodePrintedCFG.frameRsp b sa) c.frame := by
    refine ⟨hS0.frames, fun q A' n j hq hj x hx => ?_⟩
    obtain ⟨A, hA, rfl⟩ := X86Backend.ImageAddrRoute.slotRen_some hq
    have hb : X86Backend.ImageAddrRouteW.baseR σ sa d.ps (renOf d.ps A)
        = abiBase (abiReg σ) sa A := by
      simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hA]
    rw [hb] at hx
    exact hS0.cells q A n j hA hj x hx
  -- The end of the run: the words of the arrays of the slot map at their bases.
  let Fin : LstateMF → AState → Prop := fun t sA => ∀ q A n,
    slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (A, n) →
      ∃ arr, t.prog.base.getArr A 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sA.mem
          (cellAt (X86Backend.ImageAddrRouteW.baseR σ sa d.ps A) j) = arr ⟨j, hj⟩
  have hfin : ∀ t0 sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b t0 sa0 zf →
      X86Backend.LprogBytesLinkReloc.FinLea (X86Backend.DecodePrintedCFG.frameRsp b sa)
        (X86Backend.LprogBytesDecode.Params.ofBody b).frame sa0 sA → Fin t0 sA := by
    rintro t0 sa0 zf sA hrel ⟨sB, hcB, rfl⟩ q A n hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    refine ⟨arr, h1, fun j hj => ?_⟩
    rw [(X86Backend.DecodePrinted.evalInstrA_leaFrame sB _).2,
      ← X86Backend.DecodePrintedAddr.read64_eq_of_agree hcB.mem (hsep.red q A n j hq hj)]
    exact h2 j hj
  have hFin : ∀ t1 t2 sA, X86Backend.ImageAddrCall.AgreeOffF
      ((deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        c.resReg (c.args.map LOperand.reg) b) d.outs).dead t1.prog.base.reg.lpc) t1 t2 →
      Fin t2 sA → Fin t1 sA := by
    intro t1 t2 sA hag hF2 q A n hq
    obtain ⟨arr, h1, h2⟩ := hF2 q A n hq
    exact ⟨arr, by rw [X86Backend.ImageAddrSim.getArr_congr hag.arr]; exact h1, h2⟩
  have hdead' : X86Backend.ImageAddrCall.callDeadB (wordSig l c.args c.resReg) c.resReg
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        c.resReg (c.args.map LOperand.reg) b) d.outs).dead b = true := by
    unfold X86Backend.ImageAddrCall.callDeadB X86Backend.ImageAddrCall.exemptC at hdead ⊢
    simpa [X86Backend.LinkedFnCallee.wordSig, CalleeData.sig, hcclob, hcsig] using hdead
  have hbne : b ≠ [] := by
    intro hb
    simp [X86Backend.ImageAddrCall.printedAddrCB, hb] at hcls
  have hlen : (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc < b.length := by
    rw [hpc0]
    exact List.length_pos_iff.mpr hbne
  have hLv : (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
      (renOf d.ps)) c.resReg (c.args.map LOperand.reg) b) d.outs).live
      (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc = false := by
    rw [hpc0]
    simpa using hlive
  obtain ⟨hdec, sA', hhalt, hfinal⟩ := X86Backend.CheckedIsaCall.haltsC_of_linkedChecksK hsep
    hphys ((imgGateCB_frameMark b _ _).trans hgate) hsites ctRegime hX hnc hw hS hF
    (fun ret sA _ => hroom ret sA) hcls hss
    (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq) (calleeSym c b)
    hqk hne hbr hP hdead' hflags hcond hTc hsi hseg hfin hFin fuel' himgrun rfl
    hlen hLv (hrelF _) hacorr
  -- The run under the oracle of the guarded callee.
  obtain ⟨sO, hhaltO, hfinalO⟩ := X86Backend.ImageAddrCall.haltsO_of_linkedChecks hsep
    hphys ((imgGateCB_frameMark b _ _).trans hgate) hsites (calleeSpec_guard hX) hw hS hF
    (fun ret sA _ => hroom ret sA) hcls hss
    (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq) (calleeSym c b) hP hdead' hflags
    hcond hTc hsi X86Backend.CheckedIsaCall.x86IsaK_checked
    (X86Backend.CheckedIsaCall.deadSteps_x86K hseg) hfin hFin fuel' himgrun rfl hlen hLv
    (hrelF _) hacorr
  rw [← X86Backend.LprogBytesLinkReloc.expectedReloc_length _ _ _ _ _ hP] at hhaltO
  rw [hpc0] at hhalt hhaltO
  have hpos : X86Backend.DecodePrintedCFG.posOf ds 0
      = 0 + 1 := by
    simp [X86Backend.DecodePrintedCFG.posOf]
  rw [hpos] at hhalt hhaltO
  have hlen0 : 0 < prog.length := by
    rcases hq : prog with _ | ⟨x, xs⟩
    · rw [hq] at hp0; cases hp0
    · simp
  -- The read-back of the result: the arrays of the slot map, no observed register.
  have houts : d.outs = (regionRet σ exportReg (.stackArr w m) r.res).toList.map Prod.snd := by
    rw [← hd]; rfl
  have hR : ∀ sA, Fin t' sA → σ.ResultOf sa sA (denVal (.stackArr w m)
      (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m) .here
        v)) := by
    intro sA hfinal
    refine hread sA (fun q A n hq => ?_) (fun y hy => ?_)
    · have hq' : slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (renOf d.ps A, n) := by
        simp [slotRen, hq]
      obtain ⟨arr, h1, h2⟩ := hfinal q _ n hq'
      refine ⟨arr, ?_, fun j hj => ?_⟩
      · rw [X86Backend.ImageAddrSim.getArr_congr hobs.2.1.symm]
        exact h1
      · have h2' := h2 j hj
        simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hq] at h2'
        exact h2'
    · rw [houts] at hy
      simp [regionRet] at hy
  refine ⟨prog, hdec, ⟨sA', .go ?_ hhalt, hR sA' hfinal⟩, sO, .go ?_ hhaltO, hR sO hfinalO⟩
  · simp only [X86Backend.RInstrSemantics.step, List.getElem?_append_left hlen0, hp0]
    rfl
  · simp only [X86Backend.RInstrSemantics.step, hp0]
    rfl

/-! ## 5. Correctness of a calling body with one linked out kernel -/

/-- **The precondition of a linked function at its call sites.** For every frame map
    `frame`, slot map `slotArr`, array bases `base` and stack register `rsp` that are
    separated (`ImageAddrSim.ImgSep`) and separated from the return word and the frame of
    `l` below `rsp` (`ImageAddrCall.CallerSep`), every address state `sa` and byte state `sA`
    that correspond at `rsp` (`DecodePrintedAddr.ACorr`), and every list `args` of operands
    that pass the parameters `ins` at `sa` (`LinkedFnCallee.ParamAt`: the register of an
    array parameter holds the base of an array of `slotArr`) and are pairwise distinct when
    the bytes of `l` do not decode, the entry state of a call from `sA` satisfies the
    precondition of `l` at every return index. -/
def CallRoom (l : CatCrypt.Crypto.Hax.LinkedFn) (ins : List (String × ArgKind)) : Prop :=
  ∀ (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) (sa : VIR.JasminLsemAddrMem.LstateA)
    (sA : AState) (args : List String),
    X86Backend.ImageAddrSim.ImgSep frame slotArr base rsp →
    X86Backend.ImageAddrCall.CallerSep frame slotArr base rsp l.frame →
    X86Backend.DecodePrintedAddr.ACorr rsp sA sa →
    List.Forall₂ (X86Backend.LinkedFnCallee.ParamAt slotArr base sa) ins args →
    (decodeLprog l.bytes = none → args.Nodup) →
    ∀ ret, l.pre (entryOf ret sA)

/-- A linked function whose precondition holds at the entry state of every call satisfies
    it at its call sites. -/
theorem callRoom_of_forall {l : CatCrypt.Crypto.Hax.LinkedFn} (ins : List (String × ArgKind))
    (h : ∀ ret (sA : AState), l.pre (entryOf ret sA)) : CallRoom l ins :=
  fun _ _ _ _ _ sA _ _ _ _ _ _ ret => h ret sA

/-- **The summary of a linked function with an array result is its out summary.** If the
    parameter kinds `linkedKinds l` of `l` are the kinds of `ins` and the result type of `l`
    is an array of `n` values, the summary `linkedSummary l` is
    `LinkedFnCallee.outSummary l ins n`: the meaning decodes at the result type
    (`LinkedFn.sem_res`), hence to a source array, which no word decoding accepts. -/
theorem linkedSummary_eq_outSummary {l : CatCrypt.Crypto.Hax.LinkedFn}
    {ins : List (String × ArgKind)} {n : Nat} (hk : linkedKinds l = ins.map (·.2))
    (hn : arrLen? l.res = some n) :
    linkedSummary l = X86Backend.LinkedFnCallee.outSummary l ins n := by
  obtain ⟨tl, hres⟩ : ∃ tl, l.res = .arr n tl := by
    cases h : l.res <;> simp_all [arrLen?]
  simp only [linkedSummary, X86Backend.LinkedFnCallee.outSummary, hk, hn]
  congr 1
  funext ws
  cases hs : l.sem (CatCrypt.Crypto.Hax.insVals (ins.map (·.2)) ws) with
  | none => rfl
  | some v =>
      have hd := l.sem_res _ v hs
      rw [hres] at hd
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hd
      obtain ⟨vs, rfl, -⟩ := dec_arr_eq_some hy
      simp [CatCrypt.Crypto.Hax.ImpToNF.dec]

/-- **Correctness of a calling body with one linked out kernel, under the oracle of the
    callee.** Let `l` be a linked function with the out layout `OutLayout l ins po n` (its
    parameter at some position the destination, an array of `n` words at the register of
    `po`), whose
    callee data `c` has the parameters `ins` and as many arguments as `l` has parameters,
    let `X` meet the out interface `outSig l ins n`, and let `l` satisfy its precondition at
    its call sites (`CallRoom l ins`).

    Let `compileRegion σ a p [c]` give the bytes `bytes` on a program `p` with a `call`, and
    let the table `T` agree with the call environment `Ec`, hold summaries on words with word
    results at every other symbol, and give the symbol of `c` the summary
    `outSummary l ins n`. From every entry state `sa` satisfying `σ.Regions`, at every
    valuation `V` that `σ` reads off `sa` at which `p` denotes `v` in `Ec` at some fuel, the
    bytes are the bytes of an item list `items` of the caller, each passing `ItemOK`,
    followed by the bytes of `l`; the layout of `items` resolves to the caller program `pc`
    in front of every layout starting at the byte length of `items`; `pc` followed by the
    shifted block of the bytes of `l` is the decoding of `bytes` whenever the bytes of `l`
    decode; and `pc` halts from `sa` at index `0`, its calls answered by the oracle
    `oracleAt pc.length` of the runs of `X` from entry states that satisfy the precondition
    of `outSig l ins n`, in a state from which `σ` reads back the source value of the
    result.

    The reference run is `regionCo_bytes_callee` at the array positions and the result
    length of `outSummary`, the image run is `calleeBody_imgRun_at` at the call site
    `calleeSite`, whose destination is in its operands, and the run under the oracle is
    `ImageAddrCallOutChain.haltsO_of_linkedChecks_out`, with the destination array of the
    slot map from `calleeSite_dest`, the summary input and the precondition at the entry of
    a call from `callParamsB_forall₂`, `calleeBodyB_nodup` and
    `LinkedFnCallee.readIns_entry`, and the items from `calleeBytes_items`. -/
theorem compileRegion_correct_linked_outO
    {l : CatCrypt.Crypto.Hax.LinkedFn} {c : CalleeData} (hc : l.calleeData = some c)
    {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : X86Backend.LinkedFnCallee.OutLayout l ins po n) (hins : c.ins = ins)
    (hpar : l.params.length = c.args.length)
    {X : X86Backend.Callee.CalleeRun}
    (hX : X86Backend.Callee.CalleeSpec X (X86Backend.LinkedFnCallee.outSig l ins n))
    (hroom : CallRoom l ins)
    {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion σ a p [c] = some (P, bytes)) (hcf : p.callFree = false)
    {Ec : CallEnv jasminDialect} {T : ProcTable} (hT : ProcsAgree Ec T)
    (hwo : ∀ f pr, f ≠ c.name → T f = some pr → pr.WordOnly)
    (hrw : ∀ f pr, f ≠ c.name → T f = some pr → pr.RetWord)
    (hTc : T c.name = some (X86Backend.LinkedFnCallee.outSummary l ins n))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denoteAt Ec fuel V = some v) :
    ∃ (pc : List RInstr) (items : List X86Backend.LprogBytesDecode.Item),
      bytes = X86Backend.LprogBytesDecode.itemBytes items ++ l.bytes
      ∧ (∀ it ∈ items, X86Backend.LprogBytesDecode.ItemOK it)
      ∧ (∀ e x tl, X86Backend.LprogBytesDecode.resolveAll
          (X86Backend.LprogBytesDecode.layoutAt 0 items
            ++ ((X86Backend.LprogBytesDecode.itemBytes items).length, e, x) :: tl)
          (X86Backend.LprogBytesDecode.layoutAt 0 items) = some pc)
      ∧ (∀ q, decodeLprog l.bytes = some q →
        decodeLprog bytes = some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length q))
      ∧ ∃ sa', X86Backend.Callee.HaltsO aMachine
          (X86Backend.Callee.oracleAt pc.length (fun s tr s' =>
            (X86Backend.LinkedFnCallee.outSig l ins n).pre s ∧ X s tr s'))
          pc 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)) := by
  obtain ⟨⟨w, m, rfl⟩, hB, rx0, r, b, cert, hrx, hwb, hbs, hg, -⟩ :=
    compileRegion_spec_linked h hcf
  generalize hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCode (some c) r.code) r.res
    cert (some c) = d
  obtain ⟨hcres, -, -, hcclob, hcframe, hcbytes, -, -, -, -, -, hcaa⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc
  -- The out result of `c`, at its destination position `kd`.
  obtain ⟨n0, kd, hcr⟩ : ∃ n0 kd, c.res = .out n0 kd := by
    cases h' : c.res with
    | reg r =>
        rw [h'] at hcres
        simp [CatCrypt.Crypto.Hax.LinkedFn.calleeRes, hL.result] at hcres
    | out n0 kd => exact ⟨n0, kd, rfl⟩
  obtain ⟨r0, a0, hres0, hak, har, hakd⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeRes_out (hcr ▸ hcres)
  rw [hL.result] at hres0
  cases hres0
  -- The parameter at the destination position is the destination.
  have hdk : ins[kd]? = some (po, ArgKind.words n) := by
    have h1 := congrArg (·[kd]?) hL.args
    simp only [List.getElem?_map, hak, Option.map_some] at h1
    cases hik : ins[kd]? with
    | none => rw [hik] at h1; cases h1
    | some q =>
        rw [hik] at h1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        have hpo : q.1 = po := X86Backend.DecodePrinted.phys_inj
          (hL.ins_gp q (List.mem_of_getElem? hik)) hL.po_gp (h1.1.symm.trans har)
        exact congrArg some (Prod.ext hpo (h1.2.symm.trans hakd))
  -- The array positions of `c` are those of the kinds of the parameters.
  have hkinds : l.layout.args.map (·.kind) = ins.map (·.2) := by
    have h2 := congrArg (List.map Prod.snd) hL.args
    simpa [List.map_map, Function.comp_def] using h2
  have hcaa' : c.arrArgs
      = CatCrypt.Crypto.Hax.insArrArgs (ins.map (·.2)) := by
    rw [hcaa, hkinds]
  have haa : LprogIsa.Isa.procArrArgs T = calleeAA (some c) := by
    funext f
    by_cases hf : f = c.name
    · subst hf
      simp [LprogIsa.Isa.procArrArgs, calleeAA, hTc, X86Backend.LinkedFnCallee.outSummary,
        hcaa']
    · cases hTf : T f with
      | none => simp [LprogIsa.Isa.procArrArgs, calleeAA, hTf, hf]
      | some pr =>
          have hw : pr.arrArgs = fun _ => none := hwo f pr hf hTf
          simp [LprogIsa.Isa.procArrArgs, calleeAA, hTf, hf, hw]
  have hao : LprogIsa.Isa.procOut T = calleeAO (some c) := by
    funext f
    by_cases hf : f = c.name
    · subst hf
      simp [LprogIsa.Isa.procOut, calleeAO, hTc, X86Backend.LinkedFnCallee.outSummary, hcr]
    · cases hTf : T f with
      | none => simp [LprogIsa.Isa.procOut, calleeAO, hTf, hf]
      | some pr =>
          have hw : pr.out = none := hrw f pr hf hTf
          simp [LprogIsa.Isa.procOut, calleeAO, hTf, hf, hw]
  have hk : ∀ f pr, T f = some pr → pr.Kinded := by
    intro f pr hf
    by_cases hfc : f = c.name
    · subst hfc
      rw [hTc] at hf
      cases hf
      intro _ _ _
      rfl
    · exact LprogIsa.ProcSummary.kinded_of_retWord (hrw f pr hfc hf)
  obtain ⟨k, u, hu, hcb, hsep, hrelF, hacorr, hpc0, hbnd, hread⟩ :=
    RegionLinkCompose.regionCo_bytes_callee (regionExportableB_sound hB) hrx hwb hg hd hT hk haa
      hao
      hTc sa V hV hreg fuel ((legalizeRegion_denoteAt _ fuel p V).trans hv)
  -- The conjuncts of the gate.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg'
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  rw [hcells] at himg
  simp only [renImageB, X86Backend.ImageAddrRouteW.slotArrC_nil, calleeImgB,
    Bool.and_eq_true] at himg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hphys⟩, hcls, hgate⟩, -⟩, hent⟩, -⟩, -⟩ := himg
  have hcellsE : d.cells = regionCells σ exportReg d.ps b (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hcb0 : cellBody (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b = b :=
    cellBody_of_cellArrsOf_nil _ (cellArrsOf_nil_of_regionCells_nil (hcellsE ▸ hcells))
  rw [hcb0] at hphys hrelF
  -- The checks of the calling body.
  have hcb' := hcb
  simp only [calleeBodyB, Bool.and_eq_true] at hcb'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hsi⟩, -⟩, -⟩, hsites⟩, hdead⟩, hflags⟩, hcond⟩, hseg⟩,
    hlive⟩, -⟩, -⟩, hroomB⟩, hnn⟩ := hcb'
  have hdead2 := hdead
  simp only [calleeDeadB, hcr, Bool.and_eq_true] at hdead2
  obtain ⟨⟨hdo, -⟩, hparB⟩ := hdead2
  -- The destination array and the dead names at the out interface.
  obtain ⟨qA, hqA⟩ := calleeSite_dest hcr hdead (po := po) (n := n) (by rw [hins]; exact hdk)
  have hdead' : X86Backend.ImageAddrCallOutChain.callDeadOutB
      (X86Backend.LinkedFnCallee.outSig l ins n)
      (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).1
        ((calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2.map LOperand.reg)
        b) d.outs).dead b = true := by
    unfold X86Backend.ImageAddrCallOutChain.callDeadOutB X86Backend.ImageAddrCall.exemptC
      at hdo ⊢
    simpa [X86Backend.LinkedFnCallee.outSig, CalleeData.sig, hcclob, hcr, CalleeRes.reg?]
      using hdo
  -- The bytes of the calling body.
  obtain ⟨rfl, hne, ds, prog, hss, hbr, hP, hp0⟩ := calleeBytes_some hbs
  -- The image run at the table, at the call site, whose destination is an operand.
  have hmem : (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).1
      ∈ (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2 := by
    have hkd : kd < (c.siteArgs (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b
        ((firstCall b).getD 0)).length := by
      simpa [CalleeData.siteArgs, hins] using (List.getElem?_eq_some_iff.mp hdk).1
    simp only [calleeSite, hcr]
    rw [List.getD_eq_getElem _ _ hkd]
    exact List.getElem_mem hkd
  obtain ⟨fuel', t', himgrun, hobs⟩ := RegionLinkCompose.calleeBody_imgRun_at hcb hTc hpar
    ⟨⟨X86Backend.ImageAddrRoute.entryV σ (X86Backend.ImageAddrRoute.frameE b sa) sa
      (X86Backend.ImageAddrRoute.unren d.ps), a.fname⟩, false⟩
    u rfl rfl hbnd k hu (.inr hmem)
  -- The caller separation at the renamed slot map.
  have RF := X86Backend.ImageAddrRoute.renB_spec hren
  have E := X86Backend.ImageAddrRoute.entryB_spec hent sa
  have hun : ∀ q A n, slotArrOf σ exportReg q = some (A, n) →
      X86Backend.ImageAddrRoute.unren d.ps (renOf d.ps A) = A := by
    intro q A n hq
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some hq
    exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
  have hS0 := X86Backend.CalleeStackRoom.callerSep_of_regions E.rs hreg hroomB hnn
    (slotArr := slotArrOf σ exportReg) E.len
  have hS : X86Backend.ImageAddrCall.CallerSep (X86Backend.ImageAddrRoute.frameE b sa)
      (slotRen (slotArrOf σ exportReg) (renOf d.ps)) (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
      (X86Backend.DecodePrintedCFG.frameRsp b sa) l.frame := by
    rw [← hcframe]
    refine ⟨hS0.frames, fun q A' n j hq hj x hx => ?_⟩
    obtain ⟨A, hA, rfl⟩ := X86Backend.ImageAddrRoute.slotRen_some hq
    have hb : X86Backend.ImageAddrRouteW.baseR σ sa d.ps (renOf d.ps A)
        = abiBase (abiReg σ) sa A := by
      simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hA]
    rw [hb] at hx
    exact hS0.cells q A n j hA hj x hx
  -- The operands at the entry of a call.
  have hgateI : X86Backend.ImageAddrSim.ImgGate (X86Backend.ImageAddrRoute.frameE b sa)
      (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b :=
    X86Backend.ImageAddrCall.imgGate_of_imgGateCB ((imgGateCB_frameMark b _ _).trans hgate)
  have hentry : ∀ s sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b s sa0 zf →
      X86Backend.DecodePrintedAddr.ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa0 →
      (∃ bi ra t, b[sa0.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      sa0.reg.getW po 64 = some (X86Backend.ImageAddrRouteW.baseR σ sa d.ps
          (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).1)
        ∧ ∀ ret vs, LprogIsa.argsRead
            (X86Backend.LinkedFnCallee.outSummary l ins n).arrArgs
            s.prog.base 0
            ((calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2.map
              LOperand.reg) = some vs →
          X86Backend.LinkedFnCallee.readIns ins (entryOf ret sA) = vs := by
    intro s sa0 zf sA hrel hac hcall
    have hF2 := callParamsB_forall₂ hparB hsep hgateI hrel hcall
    rw [hins] at hF2
    refine ⟨?_, fun ret vs hvs =>
      X86Backend.LinkedFnCallee.readIns_entry hsep hS hrel hac ret hF2 hvs⟩
    have hsite : calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b
        = ((calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2.getD kd "",
          (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2) := by
      simp only [calleeSite, hcr]
    rw [hsite]
    generalize (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2 = ops at hF2 ⊢
    obtain ⟨hk, hik⟩ := List.getElem?_eq_some_iff.mp hdk
    have hk2 : kd < ops.length := hF2.length_eq ▸ hk
    have hR := List.Forall₂.get hF2 hk hk2
    rw [List.getD_eq_getElem _ _ hk2]
    simp only [List.get_eq_getElem, hik] at hR
    exact hR.2.2
  -- The end of the run: the words of the arrays of the slot map at their bases.
  let Fin : LstateMF → AState → Prop := fun t sA => ∀ q A n,
    slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (A, n) →
      ∃ arr, t.prog.base.getArr A 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sA.mem
          (cellAt (X86Backend.ImageAddrRouteW.baseR σ sa d.ps A) j) = arr ⟨j, hj⟩
  have hfin : ∀ t0 sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b t0 sa0 zf →
      X86Backend.LprogBytesLinkReloc.FinLea (X86Backend.DecodePrintedCFG.frameRsp b sa)
        (X86Backend.LprogBytesDecode.Params.ofBody b).frame sa0 sA → Fin t0 sA := by
    rintro t0 sa0 zf sA hrel ⟨sB, hcB, rfl⟩ q A n hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    refine ⟨arr, h1, fun j hj => ?_⟩
    rw [(X86Backend.DecodePrinted.evalInstrA_leaFrame sB _).2,
      ← X86Backend.DecodePrintedAddr.read64_eq_of_agree hcB.mem (hsep.red q A n j hq hj)]
    exact h2 j hj
  have hFin : ∀ t1 t2 sA, X86Backend.ImageAddrCall.AgreeOffF
      ((deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).1
        ((calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2.map LOperand.reg)
        b) d.outs).dead t1.prog.base.reg.lpc) t1 t2 →
      Fin t2 sA → Fin t1 sA := by
    intro t1 t2 sA hag hF2 q A n hq
    obtain ⟨arr, h1, h2⟩ := hF2 q A n hq
    exact ⟨arr, by rw [X86Backend.ImageAddrSim.getArr_congr hag.arr]; exact h1, h2⟩
  have hbne : b ≠ [] := by
    intro hb
    simp [X86Backend.ImageAddrCall.printedAddrCB, hb] at hcls
  have hlen : (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc < b.length := by
    rw [hpc0]
    exact List.length_pos_iff.mpr hbne
  have hL0 : (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
      (renOf d.ps)) (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).1
      ((calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2.map LOperand.reg)
      b) d.outs).live (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc = false := by
    rw [hpc0]
    simpa using hlive
  have hclsL : X86Backend.ImageAddrCall.printedAddrCB l.frame b = true := hcframe ▸ hcls
  -- The precondition at the entry of a call.
  have hnd : decodeLprog l.bytes = none →
      (calleeSite c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b).2.Nodup := fun hd =>
    calleeBodyB_nodup hcb (by rw [hcbytes]; exact hd)
  have hpre : ∀ s sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b s sa0 zf →
      X86Backend.DecodePrintedAddr.ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa0 →
      (∃ bi ra t, b[sa0.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      ∀ ret, l.pre (entryOf ret sA) := by
    intro s sa0 zf sA hrel hac hcall ret
    have hF2 := callParamsB_forall₂ hparB hsep hgateI hrel hcall
    rw [hins] at hF2
    exact hroom _ _ _ _ sa0 sA _ hsep hS hac hF2 hnd ret
  -- The run under the oracle of the guarded callee.
  obtain ⟨sO, hhaltO, hfinalO⟩ := X86Backend.ImageAddrCallOutChain.haltsO_of_linkedChecks_out
    hsep hphys ((imgGateCB_frameMark b _ _).trans hgate) hsites hL (calleeSpec_guard hX) hS
    hpre hqA hentry hclsL hss
    (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq) (calleeSym c b) hP hdead' hflags
    hcond hTc hsi X86Backend.CheckedIsaCall.x86IsaK_checked
    (X86Backend.CheckedIsaCall.deadSteps_x86K hseg) hfin hFin fuel' himgrun rfl hlen hL0
    (hrelF _) hacorr
  rw [← X86Backend.LprogBytesLinkReloc.expectedReloc_length _ _ _ _ _ hP] at hhaltO
  rw [hpc0] at hhaltO
  have hpos : X86Backend.DecodePrintedCFG.posOf ds 0
      = 0 + 1 := by
    simp [X86Backend.DecodePrintedCFG.posOf]
  rw [hpos] at hhaltO
  -- The read-back of the result: the arrays of the slot map, no observed register.
  have houts : d.outs = (regionRet σ exportReg (.stackArr w m) r.res).toList.map Prod.snd := by
    rw [← hd]; rfl
  have hR : ∀ sA, Fin t' sA → σ.ResultOf sa sA (denVal (.stackArr w m)
      (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m) .here
        v)) := by
    intro sA hfinal
    refine hread sA (fun q A n hq => ?_) (fun y hy => ?_)
    · have hq' : slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (renOf d.ps A, n) := by
        simp [slotRen, hq]
      obtain ⟨arr, h1, h2⟩ := hfinal q _ n hq'
      refine ⟨arr, ?_, fun j hj => ?_⟩
      · rw [X86Backend.ImageAddrSim.getArr_congr hobs.2.1.symm]
        exact h1
      · have h2' := h2 j hj
        simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hq] at h2'
        exact h2'
    · rw [houts] at hy
      simp [regionRet] at hy
  -- The decoding of the bytes when the bytes of the callee decode.
  have hprog : calleeProg c b = some prog := by
    simp only [calleeProg, hss]
    exact hP
  obtain ⟨items, hbi, hok, hres⟩ := calleeBytes_items hbs hcls hprog
  refine ⟨prog, items, by rw [← hcbytes]; exact hbi, hok, hres, fun q hq => ?_, sO,
    .go ?_ hhaltO, hR sO hfinalO⟩
  · obtain ⟨pr, hpr, hdec⟩ := calleeBytes_decode hbs hcls (hcbytes ▸ hq)
    rw [hprog] at hpr
    cases hpr
    exact hdec
  · simp only [X86Backend.RInstrSemantics.step, hp0]
    rfl

/-- **Correctness of a calling body with one linked out kernel, through the call.** Under the
    hypotheses of `compileRegion_correct_linked_outO`, with `X` the leaky runs under
    `ctRegime` of the block `qk` the bytes of `l` decode to: the bytes decode to the caller
    program `pc` followed by the shifted block `qk`, and this program halts through the call
    (`HaltsC`) from `sa` at index `0` in a state from which `σ` reads back the source value of
    the result. The block `qk` has no `call` (`regionCoB_callee`), so the oracle run of
    `compileRegion_correct_linked_outO` links with it
    (`Callee.haltsC_append_of_haltsO_runOf`). -/
theorem compileRegion_correct_linked_out
    {l : CatCrypt.Crypto.Hax.LinkedFn} {c : CalleeData} (hc : l.calleeData = some c)
    {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : X86Backend.LinkedFnCallee.OutLayout l ins po n) (hins : c.ins = ins)
    (hpar : l.params.length = c.args.length)
    {qk : List RInstr} (hqk : decodeLprog l.bytes = some qk)
    (hX : X86Backend.Callee.CalleeSpec (X86Backend.Callee.runOf ctRegime qk)
      (X86Backend.LinkedFnCallee.outSig l ins n))
    (hroom : CallRoom l ins)
    {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion σ a p [c] = some (P, bytes)) (hcf : p.callFree = false)
    {Ec : CallEnv jasminDialect} {T : ProcTable} (hT : ProcsAgree Ec T)
    (hwo : ∀ f pr, f ≠ c.name → T f = some pr → pr.WordOnly)
    (hrw : ∀ f pr, f ≠ c.name → T f = some pr → pr.RetWord)
    (hTc : T c.name = some (X86Backend.LinkedFnCallee.outSummary l ins n))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denoteAt Ec fuel V = some v) :
    ∃ pc : List RInstr,
      decodeLprog bytes = some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length qk)
      ∧ ∃ sa', HaltsC aMachine (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length qk) 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)) := by
  obtain ⟨pc, -, -, -, -, hdec, sa', hO, hR⟩ := compileRegion_correct_linked_outO hc hL hins
    hpar hX hroom h hcf hT hwo hrw hTc sa V hV hreg fuel hv
  obtain ⟨-, -, -, r, b, cert, -, -, -, hg, -⟩ := compileRegion_spec_linked h hcf
  obtain ⟨-, hnc⟩ := regionCoB_callee hg
  have hcb : c.bytes = l.bytes := (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc).2.2.2.2.2.1
  exact ⟨pc, hdec qk hqk, sa', X86Backend.Callee.haltsC_append_of_haltsO_runOf ctRegime pc qk
    (hnc qk (by rw [hcb]; exact hqk))
    (hO.mono fun _ _ _ ho => ⟨ho.1, ho.2.imp fun _ hx => hx.2⟩), hR⟩

/-! ## 6. The hax compiler on a module with linked word kernels -/

/-- **A callee found among linked functions is the callee at that function alone.** For a
    result of `compileRegion σ a p linked` on a program `p` with a `call`, some `c` among
    `linked` gives the same result as `compileRegion σ a p [c]`. -/
theorem compileRegion_singleton {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData}
    {r : Lprog × List (BitVec 8)} (h : compileRegion σ a p linked = some r)
    (hcf : p.callFree = false) : ∃ c ∈ linked, compileRegion σ a p [c] = some r := by
  unfold compileRegion at h
  split at h
  · rename_i hB
    split at h
    · rename_i r' hr
      split at h
      · rename_i callee hc
        cases callee with
        | none => rw [← legalizeRegion_callFree_eq, regionCallee_callFree hc] at hcf; cases hcf
        | some c =>
            refine ⟨c, regionCallee_mem hc, ?_⟩
            have hc1 : regionCallee [c] (legalizeRegion p) r'.code = some (some c) := by
              unfold regionCallee at hc ⊢
              rw [ite_eq_right (by rw [legalizeRegion_callFree_eq, hcf]; simp)] at hc ⊢
              split at hc
              · obtain ⟨c', hc', hcc⟩ := Option.map_eq_some_iff.mp hc
                obtain rfl := Option.some.inj hcc
                simp [(List.find?_some hc')]
              · cases hc
            unfold compileRegion
            rw [ite_eq_left hB]
            simp only [hr, hc1]
            exact h
      · cases h
    · cases h
  · cases h

open CatCrypt.Crypto.Hax (HaxModule LinkedFn linkBi linkBi_of_find_some insVals wordVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee (WordLayout
  wordCallee_of_linkedFn read_wordLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (WordCallee FootBelow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSpec HaltsO oracleAt runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall (guarded)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)

/-- At the name of a linked function of `ls`, the tables of the linked functions of `ls` over
    any two base tables are equal. -/
theorem linkBi_name_eq {ls : List LinkedFn} {l : LinkedFn} (hl : l ∈ ls)
    (bi bi' : _root_.Hax.Builtins) : linkBi ls bi l.name = linkBi ls bi' l.name := by
  cases hf : ls.find? (·.name == l.name) with
  | none => exact absurd (List.find?_eq_none.mp hf l hl) (by simp)
  | some l' =>
      funext vals
      rw [linkBi_of_find_some _ _ hf, linkBi_of_find_some _ _ hf]

/-- **The call environment of the linked functions of a module alone**: `tableEnv` at the
    table of the linked functions of `m` over the table that answers no call. A call of a
    linked function is answered by its meaning `LinkedFn.sem`; every other call refuses. -/
def linkedEnv (m : HaxModule) : CallEnv jasminDialect :=
  tableEnv (m.linkTable fun _ _ => none)

/-- **The declared procedures of a module agree with the environment of its linked functions
    over every base table.** The function of each declaration at the table
    `m.linkTable bi` is the call of that table at the name of a linked function, which is the
    call of `m.linkTable bi'` (`linkBi_name_eq`); the environment of that table implements
    it (`implementedBy_tableEnv`). -/
theorem extAgree_linkedDecls_linkTable (m : HaxModule) (bi bi' : _root_.Hax.Builtins) :
    CatCrypt.Crypto.Hax.NFToCat.ExtAgree (m.linkTable bi)
      (catEnvOf (tableEnv (m.linkTable bi'))) (linkedDecls m (m.linkTable bi)) := by
  intro d hd
  obtain ⟨l, hl, hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨as, has, rfl⟩ := List.mem_map.mp hd
  have hr : linkResOk l.res = true := by
    have := (List.mem_filter.mp hl).2
    simp only [Bool.and_eq_true] at this
    exact this.2
  have he : (CatCrypt.Crypto.Hax.ImpToNF.tableOf (m.linkTable bi)).call l.name as l.res =
      (CatCrypt.Crypto.Hax.ImpToNF.tableOf (m.linkTable bi')).call l.name as l.res := by
    funext xs
    show (m.linkTable bi l.name _).bind _ = (m.linkTable bi' l.name _).bind _
    rw [HaxModule.linkTable, HaxModule.linkTable,
      linkBi_name_eq (List.mem_filter.mp hl).1 bi bi']
  refine ⟨fun _ => rfl, ?_⟩
  rw [he]
  exact implementedBy_tableEnv _ l.name as l.res hr
    (List.all_eq_true.mp (List.mem_filter.mp has).2)

/-- **A source run of a module is a run of the chain's program at the linked functions
    alone.** Let the translation of the hax entry return `q` on the module `m` and the chain
    with the declared procedures of `m` return `p` on `q`. For every value `v` of a source
    run from an entry state `sa` satisfying `σ.Regions` there are a fuel `k`, a valuation
    `V` that `σ` reads off `sa` and a value `x` with source value `v` such that `p` denotes
    `x` at `V` and the fuel `k` in the environment `linkedEnv m`, which answers the calls of
    the linked functions of `m` by their meanings and refuses every other call. The chain is
    sound at every environment that implements the declared procedures (`extChain_entry`),
    and `linkedEnv m` implements them (`extAgree_linkedDecls_linkTable`). -/
theorem haxEntry_run_linkedEnv {σ : AbiLayout} {m : HaxModule}
    {q : Σ t : NFDialect.NfTy,
      NFProg NFDialect.nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hq : haxEntry.toNF σ m = some q)
    {p : NFProg jasminDialect (nfCtx σ)
      [CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q.1)]}
    (hp : (extChain (haxEntry.decls m) _ q.1).run q.2 = some p)
    {sa : AState} {v : _root_.Hax.Value} (hreg : σ.Regions sa) (hrun : haxRuns σ m sa v) :
    ∃ (k : Nat) (V : Ctxt.Valuation (nfCtx σ)) (x : _),
      AbiValOf σ sa V
      ∧ v = denVal (CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q.1)) x
      ∧ p.denoteAt (linkedEnv m) k V = some (HVector.cons x .nil) := by
  obtain ⟨k, -, env, V, y, -, hsub, -, henv, hV, ⟨tf, hle, hden⟩, hv⟩ :=
    haxEntry.sound σ m q hq sa v hreg hrun
  replace hp : (extChain (linkedDecls m (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) _
      q.1).run q.2 = some p := by
    rw [extChain_congr (declared_linkedDecls m
      (m.linkTable CatCrypt.Crypto.Hax.hax64WExit) CatCrypt.Crypto.Hax.hax64WExit)]
    exact hp
  obtain ⟨hA, x, hx, hxv⟩ := extChain_entry hsub (haxEntry.fieldCalls σ m q hq k)
    (haxEntry.fieldCallsWide σ m q hq k) tf k (linkedEnv m)
    (extAgree_linkedDecls_linkTable m _ _) henv q.2 hp V hV hden hle
  exact ⟨k, _, x, hA, hv.trans hxv.symm, hx⟩

/-- The argument values `insVals` at scalar kinds, one per word, are the words as source
    integers. -/
theorem insVals_scalars : ∀ (ks : List ArgKind) (xs : List (BitVec 64)),
    (∀ k ∈ ks, k = .scalar) → ks.length = xs.length → insVals ks xs = xs.map wordVal
  | [], [], _, _ => rfl
  | k :: ks, x :: xs, h, hl => by
      rw [h k List.mem_cons_self]
      simp only [insVals, List.headD_cons, List.tail_cons, List.map_cons]
      rw [insVals_scalars ks xs (fun k hk => h k (List.mem_cons_of_mem _ hk))
        (Nat.succ.inj hl)]
  | [], _ :: _, _, hl => by cases hl
  | _ :: _, [], _, hl => by cases hl

/-- **The summary of a linked word function reads its word interface.** With a word layout
    at the names `ws`, as many scalar parameters as names and no array result, the summary
    `linkedSummary l` agrees with `wordSummary l` on argument lists of that length, so it is
    a `WordCallee` at `wordSig l ws res` (`wordCallee_of_linkedFn`) on every predicate
    `room` that gives the precondition of `l` at a state at whose argument words
    `wordSummary l` is defined (`hpre`; `room := l.pre` is one). -/
theorem wordCallee_linkedSummary {l : LinkedFn} {ws : List String} {res : String}
    (hL : WordLayout l ws res)
    (hs : ∀ q ∈ l.params, kindOfTy (CryptoToJasminCom.mapTy
      (CatCrypt.Crypto.Hax.NFToCat.catTy q.2)) = .scalar)
    (hn : l.params.length = ws.length) (hr : ∀ n t, l.res ≠ .arr n t)
    {room : AState → Prop}
    (hpre : ∀ s, room s →
      ((wordSummary l).run (ws.map fun a => s.regs (phys a))).isSome = true → l.pre s) :
    WordCallee (wordSig l ws res) res (linkedSummary l) room := by
  have W := wordCallee_of_linkedFn hL
  have key : ∀ s : AState,
      (linkedSummary l).run ((wordSig l ws res).args.map fun a => s.regs (phys a))
      = (wordSummary l).run ((wordSig l ws res).args.map fun a => s.regs (phys a)) := by
    intro s
    show (l.sem (insVals (linkedKinds l) _)).bind _ = (l.sem (List.map wordVal _)).bind _
    rw [insVals_scalars]
    · intro k hk
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hk
      exact hs q hq
    · simp [linkedKinds, hn, X86Backend.LinkedFnCallee.wordSig]
  exact
    { args_gp := W.args_gp
      res_eq := W.res_eq
      res_gp := W.res_gp
      res_clob := W.res_clob
      pre := fun s h hd =>
        have hd' : ((wordSummary l).run ((wordSig l ws res).args.map
            fun a => s.regs (phys a))).isSome = true := by
          rw [← key]; exact hd
        W.pre s (hpre s h hd') hd'
      post := fun s s' h hp => (key s).trans (W.post s s' h hp)
      wordOnly := linkedSummary_wordOnly hs
      wordRet := linkedSummary_retWord hr }

open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (CallVar arrOwn fp_arrOwn
  isResRegion holds_entryAt stackRoom)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (eq_of_isResRegion)
open CatCrypt.Crypto.SecureCompilation.SepLogic (SAssert Footprinted)
open CatCrypt.Crypto.SecureCompilation.SepLogic.SAssert (conj emp bigSep mem_fp_bigSep)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordLocs regionWords mem_regions
  disjoint_wordLocs_iff)

/-- **The precondition of a linked function at its call sites**: at every state where the
    resources of a call (`LinkedFn.entryAt`) hold at logical variables whose argument values
    satisfy the predicate `D`, the precondition of `l` holds. -/
def _root_.CatCrypt.Crypto.Hax.LinkedFn.CallSitePre (l : LinkedFn)
    (D : List _root_.Hax.Value → Prop) : Prop :=
  ∀ (a : CallVar) (s : AState), (l.entryAt a).holds s → D a.vals → l.pre s

/-- The call-site precondition at a predicate `D` gives the call-site precondition at every
    predicate stronger than `D`. -/
theorem _root_.CatCrypt.Crypto.Hax.LinkedFn.CallSitePre.mono {l : LinkedFn}
    {D D' : List _root_.Hax.Value → Prop} (h : l.CallSitePre D)
    (hD : ∀ vals, D' vals → D vals) : l.CallSitePre D' :=
  fun a s hs hd => h a s hs (hD _ hd)

/-- The word at `sp + o`, `-F ≤ o ≤ -8`, lies in the `F` bytes below `sp`. -/
theorem wordLocs_subset_stackRoom {sp : BitVec 64} {F : Nat} {o : Int} (h1 : -(F : Int) ≤ o)
    (h2 : o ≤ -8) : wordLocs (sp + BitVec.ofInt 64 o) ⊆ stackRoom sp F := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  have hx' : (x - (sp + BitVec.ofInt 64 o)).toNat < 8 := hx
  show (x - (sp + BitVec.ofInt 64 (-(F : Int)))).toNat < F
  have := sp.isLt
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt] at hx' ⊢
  omega

/-- The locations of an entry of a mapped list lie in the locations of its `conj`. -/
theorem subset_fp_foldr_conj {σ' L ι : Type} [Footprinted σ' L] {f : ι → SAssert σ' L}
    {p : ι} : ∀ {ps : List ι}, p ∈ ps → (f p).fp ⊆ ((ps.map f).foldr conj emp).fp
  | [], h => absurd h List.not_mem_nil
  | _ :: _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Set.subset_union_left
    · exact (subset_fp_foldr_conj h).trans Set.subset_union_right

/-- Two entries of a list of length at most one are equal. -/
theorem eq_of_mem_of_length_le_one {α : Type} {p q : α} :
    ∀ {l : List α}, l.length ≤ 1 → p ∈ l → q ∈ l → p = q
  | [x], _, hp, hq => by simp at hp hq; rw [hp, hq]
  | _ :: _ :: _, hl, _, _ => by simp at hl

/-- **The entry conditions of the layout from the resources of a call.** Let the layout of
    `l` have no bounded register, distinct pointer regions, at most one pointer region other
    than the region of an out result, and its frame words `%rsp + o`,
    `frameLo ≤ o ≤ frameHi`, among the `l.frame` bytes below the entry stack register
    (`-l.frame ≤ frameLo` and `frameHi ≤ -8`). Then the entry conditions `l.layout.Regions`
    hold at every state where the resources of a call hold: the separation of the pointer
    regions from each other and from the stack room gives the disjointness of their words
    (`disjoint_wordLocs_iff`), and the stack parameters give `StackIn`. -/
theorem regions_of_entryAt {l : LinkedFn} (hb : l.layout.bounds = [])
    (hnd : l.layout.regions.Nodup)
    (hro : (l.layout.regions.filter fun p => !isResRegion l.layout p).length ≤ 1)
    (hlo : -(l.frame : Int) ≤ l.layout.frameLo) (hhi : l.layout.frameHi ≤ -8)
    {a : CallVar} {s : AState} (h : (l.entryAt a).holds s) : l.layout.Regions s := by
  obtain ⟨hregs, hsp, -⟩ := holds_entryAt h
  obtain ⟨⟨-, -, hd2, ⟨⟨hdro, -, -⟩, -⟩, -⟩, hst, -⟩ := h
  have hreg : ∀ p ∈ l.layout.regions, s.regs p.1 = a.rv p.1 := fun p hp => by
    obtain ⟨b, hb, hbr⟩ := mem_regions hp
    exact hregs _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.2 ⟨b, hb, hbr⟩)))
  have hword : ∀ p ∈ l.layout.regions, ∀ k, k < p.2 →
      wordLocs (s.regs p.1 + BitVec.ofNat 64 (8 * k)) ⊆ (arrOwn (a.rv p.1) p.2).fp := by
    intro p hp k hk
    rw [hreg p hp, fp_arrOwn]
    exact Set.subset_biUnion_of_mem (u := wordLocs)
      (show _ ∈ regionWords _ _ from ⟨k, hk, rfl⟩)
  have hG1 : ∀ p ∈ l.layout.regions, isResRegion l.layout p = false → ∀ k, k < p.2 →
      wordLocs (s.regs p.1 + BitVec.ofNat 64 (8 * k)) ⊆
        (((l.layout.regions.filter fun p => !isResRegion l.layout p).map
          fun p => arrOwn (a.rv p.1) p.2).foldr conj emp).fp := by
    intro p hp hr k hk
    have hm : p ∈ l.layout.regions.filter (fun p => !isResRegion l.layout p) :=
      List.mem_filter.2 ⟨hp, by rw [hr]; rfl⟩
    refine (hword p hp k hk).trans ?_
    exact (subset_fp_foldr_conj (f := fun p => arrOwn (a.rv p.1) p.2) (p := p) hm :)
  have hG2 : ∀ p ∈ l.layout.regions, isResRegion l.layout p = true → ∀ k, k < p.2 →
      wordLocs (s.regs p.1 + BitVec.ofNat 64 (8 * k)) ⊆
        (bigSep ((l.layout.regions.filter fun p => isResRegion l.layout p).map
          fun p => arrOwn (a.rv p.1) p.2)).fp := by
    intro p hp hr k hk y hy
    have hm : arrOwn (a.rv p.1) p.2 ∈ (l.layout.regions.filter fun p => isResRegion l.layout p).map
        fun p => arrOwn (a.rv p.1) p.2 := List.mem_map_of_mem (List.mem_filter.2 ⟨hp, hr⟩)
    exact mem_fp_bigSep.2 ⟨_, hm, hword p hp k hk hy⟩
  refine ⟨by simp [hb], ?_, ?_, ?_⟩
  · intro i j p q hij hp hq k k' hk hk'
    have hpm := List.mem_of_getElem? hp
    have hqm := List.mem_of_getElem? hq
    have hpq : p ≠ q := by
      rintro rfl
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hp
      obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.1 hq
      exact hij ((List.Nodup.getElem_inj_iff hnd).1 he.symm)
    rw [← disjoint_wordLocs_iff]
    cases hpr : isResRegion l.layout p <;> cases hqr : isResRegion l.layout q
    · exact absurd (eq_of_mem_of_length_le_one hro (List.mem_filter.2 ⟨hpm, by simp [hpr]⟩)
        (List.mem_filter.2 ⟨hqm, by simp [hqr]⟩)) hpq
    · exact hdro.mono (hG1 p hpm hpr k hk) (hG2 q hqm hqr k' hk')
    · exact (hdro.mono (hG1 q hqm hqr k' hk') (hG2 p hpm hpr k hk)).symm
    · obtain ⟨r, n, hr, rfl⟩ := eq_of_isResRegion hpr
      obtain ⟨r', n', hr', rfl⟩ := eq_of_isResRegion hqr
      rw [hr] at hr'
      cases hr'
      exact absurd rfl hpq
  · intro p hp k hk o h1 h2
    rw [← disjoint_wordLocs_iff, hsp]
    refine Disjoint.mono ?_ ?_ hd2.symm
    · exact (wordLocs_subset_stackRoom (F := l.frame) (by omega) (by omega)).trans
        fun x hx => Or.inr (Or.inr (Or.inr hx))
    · intro x hx
      refine Or.inl ?_
      cases hr : isResRegion l.layout p
      · exact Or.inl (hG1 p hp hr k hk hx)
      · exact Or.inr (hG2 p hp hr k hk hx)
  · intro b hb k hk
    rw [hregs b.reg (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map_of_mem hb))), hregs "%rsp" List.mem_cons_self]
    exact hst b hb k hk

/-- **A linked word kernel**: a linked function with scalar parameters, a word result, a
    meaning defined only on arguments of its parameter kinds, a precondition that holds at
    the entry of every call at whose arguments the meaning is defined
    (`LinkedFn.CallSitePre`), and, when the region back half reads its data `c`, a word
    layout at the argument names and the result name of `c`, as many parameters as
    arguments, and code that decodes to a block whose leaky runs under `ctRegime` meet the
    word interface `wordSig l c.args c.resReg`, whose precondition carries the definedness
    of the summary at the argument words, and write only among the `c.frame` bytes below
    the entry stack register. -/
structure LinkedWordKernel (l : LinkedFn) : Prop where
  /-- Every parameter is a scalar. -/
  params_scalar : ∀ q ∈ l.params, kindOfTy (CryptoToJasminCom.mapTy
    (CatCrypt.Crypto.Hax.NFToCat.catTy q.2)) = .scalar
  /-- The result is no array. -/
  res_arr : ∀ n t, l.res ≠ .arr n t
  /-- The result is no slice. -/
  res_slice : ∀ t, l.res ≠ .slice t
  /-- The meaning returns values only on arguments of the parameter kinds. -/
  sem_kinds : ∀ vals v, l.sem vals = some v → vals.map valKind = linkedKinds l
  /-- The precondition holds under the resources of every call at whose arguments the
      meaning is defined. -/
  callSite : l.CallSitePre fun vals => (l.sem vals).isSome = true
  /-- The word layout of the data of the function. -/
  layout : ∀ c, l.calleeData = some c → WordLayout l c.args c.resReg
  /-- As many parameters as arguments of the layout. -/
  arity : l.params.length = l.layout.args.length
  /-- The contract of the code at the word interface. -/
  code : ∀ c, l.calleeData = some c → ∃ q, decodeLprog c.bytes = some q
    ∧ CalleeSpec (runOf ctRegime q) (wordSig l c.args c.resReg)
    ∧ FootBelow (wordSig l c.args c.resReg) c.frame

/-- The result register of the data of a linked function with a word layout is the result
    name. -/
theorem resReg_of_wordLayout {l : LinkedFn} {c : CalleeData} (hc : l.calleeData = some c)
    (hL : WordLayout l c.args c.resReg) : c.res.reg? = some c.resReg := by
  obtain ⟨r0, hr0⟩ : ∃ r, c.res = .reg r := by
    cases hcr : c.res with
    | reg r => exact ⟨r, rfl⟩
    | out n =>
        have h1 := (LinkedFn.calleeData_eq hc).1
        rw [hcr] at h1
        simp [LinkedFn.calleeRes, hL.result] at h1
  simp only [CalleeData.resReg, hr0, CalleeRes.reg?]

/-- **The word interface of the data of a linked function** is the interface of the data
    with the precondition of the word interface. -/
theorem wordSig_eq_sig {l : LinkedFn} {c : CalleeData} (hc : l.calleeData = some c)
    (hL : WordLayout l c.args c.resReg) :
    wordSig l c.args c.resReg = { c.sig with pre := (wordSig l c.args c.resReg).pre } := by
  obtain ⟨-, -, -, hcclob, -, -, -, hcfoot, hcpost, hcpub, -⟩ := LinkedFn.calleeData_eq hc
  simp only [X86Backend.LinkedFnCallee.wordSig, CalleeData.sig, resReg_of_wordLayout hc hL,
    hcclob, hcfoot, hcpost, hcpub]

/-- **A linked word kernel from the interface of its data.** A linked function with scalar
    parameters, a word result, a meaning defined only on arguments of its parameter kinds,
    a precondition that holds at the entry of every call at whose arguments a predicate `D`
    holds, where `D` holds wherever the meaning is defined, a word layout, as many
    parameters as arguments, and code that meets the interface `c.sig` of its data is a
    linked word kernel: the word interface has the stronger precondition
    (`CalleeSpec.restrictPre`). At `D := fun _ => True` the call-site precondition is a
    precondition at the entry of every call. -/
theorem LinkedWordKernel.of_sig {l : LinkedFn} {D : List _root_.Hax.Value → Prop}
    (params_scalar : ∀ q ∈ l.params, kindOfTy (CryptoToJasminCom.mapTy
      (CatCrypt.Crypto.Hax.NFToCat.catTy q.2)) = .scalar)
    (res_arr : ∀ n t, l.res ≠ .arr n t) (res_slice : ∀ t, l.res ≠ .slice t)
    (sem_kinds : ∀ vals v, l.sem vals = some v → vals.map valKind = linkedKinds l)
    (callSite : l.CallSitePre D) (hD : ∀ vals, (l.sem vals).isSome = true → D vals)
    (layout : ∀ c, l.calleeData = some c → WordLayout l c.args c.resReg)
    (arity : l.params.length = l.layout.args.length)
    (code : ∀ c, l.calleeData = some c → ∃ q, decodeLprog c.bytes = some q
      ∧ CalleeSpec (runOf ctRegime q) c.sig ∧ FootBelow c.sig c.frame) :
    LinkedWordKernel l where
  params_scalar := params_scalar
  res_arr := res_arr
  res_slice := res_slice
  sem_kinds := sem_kinds
  callSite := callSite.mono hD
  layout := layout
  arity := arity
  code c hc := by
    obtain ⟨q, hq, hX, hF⟩ := code c hc
    have hL := layout c hc
    have hcpre := (LinkedFn.calleeData_eq hc).2.2.2.2.2.2.1
    have hcfoot := (LinkedFn.calleeData_eq hc).2.2.2.2.2.2.2.1
    refine ⟨q, hq, ?_, fun s y hy => hF s y (by show c.foot s y; rw [hcfoot]; exact hy)⟩
    rw [wordSig_eq_sig hc hL]
    exact X86Backend.LinkedFnCallee.CalleeSpec.restrictPre hX fun s h => by
      show c.pre s
      rw [hcpre]
      exact h.1

/-- **The summary of a linked word kernel at its call sites**: `linkedSummary l` reads the
    word interface at the data `c` of `l` on the entry states at whose arguments the
    definedness of the meaning gives the precondition of `l`. -/
theorem LinkedWordKernel.wordCallee {l : LinkedFn} (K : LinkedWordKernel l) {c : CalleeData}
    (hc : l.calleeData = some c) :
    WordCallee (wordSig l c.args c.resReg) c.resReg (linkedSummary l)
      (fun s => (l.sem (l.layout.args.map (·.read s))).isSome = true → l.pre s) := by
  have hL := K.layout c hc
  have hn : l.params.length = c.args.length := by
    rw [(LinkedFn.calleeData_eq hc).2.2.1, List.length_map]
    exact K.arity
  refine wordCallee_linkedSummary hL K.params_scalar hn K.res_arr fun s h hd => h ?_
  rw [read_wordLayout hL s]
  exact Option.isSome_of_isSome_bind hd

/-- At the name of a function of a list with distinct names, the first function with that
    name is the function. -/
theorem find?_name_of_nodup {ls : List LinkedFn} (hnd : (ls.map (·.name)).Nodup)
    {l : LinkedFn} (hl : l ∈ ls) : ls.find? (·.name == l.name) = some l := by
  cases hf : ls.find? (·.name == l.name) with
  | none => exact absurd (List.find?_eq_none.mp hf l hl) (by simp)
  | some l' =>
      have h1 := List.mem_of_find?_eq_some hf
      have h2 : l'.name = l.name := by simpa using List.find?_some hf
      rw [List.inj_on_of_nodup_map hnd h1 hl h2]

/-! ## 7. The source run at the table of the callee alone -/

/-- The environment of the linked functions of `m` restricted to the name `f`. -/
def linkedEnvAt (m : HaxModule) (f : String) : CallEnv jasminDialect :=
  tableEnv fun g vals => if g = f then m.linkTable (fun _ _ => none) g vals else none

/-- The table with the summary of `l` alone. -/
def summaryTable (l : LinkedFn) : LprogIsa.ProcTable :=
  fun f => if f = l.name then some (linkedSummary l) else none

/-- Every `call` of the program names `f` (the name-level form of `ExportNF.onlyCalls`). -/
def callsTo (f : String) : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => callsTo f k
  | _, _, .forLoop _ _ body k => callsTo f body && callsTo f k
  | _, _, .ifThenElse _ thn els k => callsTo f thn && callsTo f els && callsTo f k
  | _, _, .whileLoop _ body k => callsTo f body && callsTo f k
  | _, _, .call g _ k => (g == f) && callsTo f k

/-- `callsTo f` reads only the calls. -/
theorem callTest_callsTo (f : String) : CallTest (fun g => g == f) (callsTo f) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- **The region legalisation keeps the value of `callsTo f`.** -/
theorem callsTo_legalizeRegion (f : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : callsTo f (legalizeRegion p) = callsTo f p :=
  legalizeRegion_callTest (callTest_callsTo f) p

/-- **The table of the callee alone agrees with the environment of the callee alone.** For
    a linked function `l` of a module whose linked functions have distinct names, whose
    meaning returns values only on arguments of its parameter kinds and whose result type is
    no slice, `summaryTable l` agrees with `linkedEnvAt m l.name`: both are the table and the
    environment of the module with `l` as its only linked function
    (`procsAgree_tableEnv_linkTable`). -/
theorem procsAgree_summaryTable {m : HaxModule} (hnd : (m.linked.map (·.name)).Nodup)
    {l : LinkedFn} (hl : l ∈ m.linked)
    (hargs : ∀ vals v, l.sem vals = some v → vals.map valKind = linkedKinds l)
    (hres : ∀ t, l.res ≠ .slice t) :
    ProcsAgree (linkedEnvAt m l.name) (summaryTable l) := by
  have hbi : (fun g vals => if g = l.name then m.linkTable (fun _ _ => none) g vals else none)
      = ({ m with linked := [l] } : HaxModule).linkTable (fun _ _ => none) := by
    funext g vals
    by_cases hg : g = l.name
    · subst hg
      simp [HaxModule.linkTable, linkBi, find?_name_of_nodup hnd hl]
    · have hg' : (l.name == g) = false := beq_eq_false_iff_ne.mpr (Ne.symm hg)
      simp [HaxModule.linkTable, linkBi, hg, hg']
  have htab : summaryTable l
      = procTableOf ({ m with linked := [l] } : HaxModule) LprogIsa.ProcTable.empty := by
    funext g
    by_cases hg : g = l.name
    · subst hg
      simp [summaryTable, procTableOf]
    · have hg' : (l.name == g) = false := beq_eq_false_iff_ne.mpr (Ne.symm hg)
      simp [summaryTable, procTableOf, hg, hg', LprogIsa.ProcTable.empty]
  unfold linkedEnvAt
  rw [hbi, htab]
  exact procsAgree_tableEnv_linkTable _
    (fun l' hl' => by rw [List.mem_singleton.mp hl']; exact hargs)
    (fun l' hl' => by rw [List.mem_singleton.mp hl']; exact hres)
    (procsAgree_tableEnv_empty fun _ _ _ h => by cases h)

/-- **The calls of an exported program are among its shadow instructions**: when every
    shadow instruction of the export of `p` names `f`, every `call` of `p` names `f`. -/
theorem callsTo_of_exportR {nArgs : Nat} {fn f : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {I : LprogIsa.IsaData}
    {r : Exported} (h : exportR nArgs fn p d n I = some r)
    (hsh : ∀ i ∈ r.code, ∀ v, LprogIsa.shadowCall? i.fst = some v → v.2.1 = f) :
    callsTo f p = true := by
  induction p generalizing d n r with
  | ret vs => rfl
  | var e k ih =>
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      exact ih hk fun i hi => hsh i (by simp [Exported.prepend, hi])
  | forLoop count inits body k ihb ihk =>
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      simp only [callsTo, Bool.and_eq_true]
      exact ⟨ihb hb fun i hi => hsh i (by simp [Exported.prepend, forArrFrame, hi]),
        ihk hk fun i hi => hsh i (by simp [Exported.prepend, hi])⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨rt, ht, re, he, rk, hk, rfl⟩ := h
      simp only [callsTo, Bool.and_eq_true]
      exact ⟨⟨iht ht fun i hi => hsh i (by simp [Exported.prepend, ifFrame, hi]),
        ihe he fun i hi => hsh i (by simp [Exported.prepend, ifFrame, hi])⟩,
        ihk hk fun i hi => hsh i (by simp [Exported.prepend, hi])⟩
  | whileLoop inits body k ihb ihk =>
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      simp only [callsTo, Bool.and_eq_true]
      exact ⟨ihb hb fun i hi => hsh i (by simp [Exported.prepend, whileFrame, hi]),
        ihk hk fun i hi => hsh i (by simp [Exported.prepend, hi])⟩
  | call g args k ih =>
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      simp only [callsTo, Bool.and_eq_true, beq_iff_eq]
      refine ⟨?_, ih hk fun i hi => hsh i (by simp [Exported.prepend, hi])⟩
      exact hsh (callI (regName d) g (exprArgsHV d nArgs argName (fun _ => none) args))
        (by simp [Exported.prepend]) _ (LprogIsa.shadowCall?_callShadow _ _ _)

/-- **Every call of a program the back half compiles at one callee names the callee.**
    `regionCallee` accepts a program with a `call` at `[c]` only when the shadow
    instructions of its export name one symbol, the symbol of `c`, and every `call` of the
    program is a shadow instruction of the export (`callsTo_of_exportR`). -/
theorem callsTo_of_compileRegion {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {c : CalleeData}
    {r : Lprog × List (BitVec 8)}
    (h : compileRegion σ a p [c] = some r) (hcf : p.callFree = false) :
    callsTo c.name p = true := by
  unfold compileRegion at h
  split at h
  · split at h
    · rename_i r0 hr0
      split at h
      · rename_i callee hc
        rw [← callsTo_legalizeRegion]
        refine callsTo_of_exportR hr0 fun i hi v hv => ?_
        unfold regionCallee at hc
        rw [ite_eq_right (by rw [legalizeRegion_callFree_eq, hcf]; simp)] at hc
        split at hc
        · rename _ = [_] => hl
          obtain ⟨c', hc', -⟩ := Option.map_eq_some_iff.mp hc
          have hcc : c' = c := List.mem_singleton.mp (List.mem_of_find?_eq_some hc')
          have hcn := List.find?_some hc'
          simp only [hcc, beq_iff_eq] at hcn
          have hmem : v.2.1 ∈ (r0.code.filterMap fun i =>
              (LprogIsa.shadowCall? i.fst).map (·.2.1)).eraseDups := by
            rw [List.mem_eraseDups]
            exact List.mem_filterMap.mpr ⟨i, hi, by rw [hv]; rfl⟩
          rw [hl, List.mem_singleton] at hmem
          rw [hmem, hcn]
        · cases hc
      · cases h
    · cases h
  · cases h

/-- **A program whose calls name `f` denotes the same at the environment restricted to
    `f`**: the two environments answer every call of `f` alike. -/
theorem denoteAt_linkedEnvAt {m : HaxModule} {f : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : callsTo f p = true)
    (k : Nat) (V : Ctxt.Valuation Γ) :
    p.denoteAt (linkedEnvAt m f) k V = p.denoteAt (linkedEnv m) k V := by
  unfold NFProg.denoteAt
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.denote, ih hp]
  | forLoop count inits body k ihb ihk =>
      simp only [callsTo, Bool.and_eq_true] at hp
      simp only [NFProg.denote, ihb hp.1, ihk hp.2]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [callsTo, Bool.and_eq_true] at hp
      simp only [NFProg.denote, iht hp.1.1, ihe hp.1.2, ihk hp.2]
  | whileLoop inits body k ihb ihk =>
      simp only [callsTo, Bool.and_eq_true] at hp
      simp only [NFProg.denote, ihb hp.1, ihk hp.2]
  | call g args k ih =>
      simp only [callsTo, Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, hk⟩ := hp
      simp only [NFProg.denote, ih hk, linkedEnvAt, linkedEnv, tableEnv, ite_true]

end Linked

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
