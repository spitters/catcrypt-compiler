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
# Correctness of a compiled body with linked kernels

A program with `call`s that `compileRegion` compiles at a table `T` of linked functions runs on
its bytes through the calls of the code of the table (`compileRegion_correct_linked_multi`):
the reference run of the gate at the procedure table (`RegionLinkCompose.regionCo_bytes_tab`)
gives the run of the image of the calling body (`RegionLinkCompose.calleeBody_imgRun_tab`),
which the chains of the calling class carry to the caller program under an oracle that answers
each callee by the specification of its kind (`ImageAddrCallMeets.haltsO_of_contracts`) and,
when the code of each function but the last is an item stream, to the decoded bytes of the
caller followed by the region of the blocks of the table
(`ImageAddrCallMeets.haltsC_of_contracts`, `CalleeTab.regionBlocks`). The hypotheses of the
calls of each symbol come from the top hypotheses of its kind (`CalleeKind.Top.ok`). The
correctness theorems at one linked function are its instances at `linked = [c]`.

At one linked word kernel the route reads as follows: the run of
the reference of the gate at the procedure table (`RegionLinkCompose.regionCo_bytes_callee`)
gives the run of the image of the calling body (`RegionLinkCompose.calleeBody_imgRun_at`),
which the linked image theorem carries to the decoded bytes of the caller followed by the
kernel block (`CheckedIsaCall.haltsC_of_linkedChecksKW`), and to the caller program under
the oracle of the kernel guarded by its precondition
(`ImageAddrCallW.haltsO_of_linkedChecksOne`), over the wide class
`ImageAddrCallW.printedAddrCWB` and the gate `ImageAddrCallW.imgGateCBW`. A kernel with an out
result, which writes the array of one of its arguments, takes the same route through
`ImageAddrCallOutChain.haltsO_of_linkedChecksW_out` at the call sites `calleeSiteAt`.

The declarations lie in the namespace `Haxc.RegionLinkCall`; the module `RegionLinkCall`
states the runs of the bytes of `compileA` and the compiler theorems over them.

## Main results

* `reloadOf_slotRen`, `accArr_slotRen`: the reload scan and the array of an access at a
  slot map with renamed arrays.
* `cellBody_of_cellArrsOf_nil`, `cellArrsOf_nil_of_regionCells_nil`: without a cell array of
  the region back half, the cell body of a printed body is the body.
* `imgGateCBW_congr`, `imgGateCBW_frameMark`, `bitsDeadB_congr`, `bitsDeadB_frameMark`: the
  gate of a calling body and its width check read only which names have a frame word.
* `callParamsB_forall₂W`: the operands of a call site pass the parameters of the callee under
  the wide gate.
* `compileRegion_spec_linked`: a result of `compileRegion σ a p [c]` on a program with a
  `call` has a word-array result, an export and a printed body that passes `regionCoB` at
  `c`, with bytes `calleeBytes`.
* `callParamsAtB_forall₂W`: the operands of a call that pass `callParamsAtB` pass the
  parameters of the callee under the wide gate.
* `regionCallee_fns_ne_nil`, `compileRegion_spec_tab`, `compileRegion_tab`: a result of the
  back half on a program with a `call` at its table, and the table found among linked
  functions is found at its own functions, with the same result (`compileRegion_singleton` at
  one function).
* `calleeBytes_tab`, `lookup_of_call`, `remoteSym_mem_names`: the bytes of a calling body at a
  table, and every call of a calling body names a function of the table.
* `callsToAny`, `callsToAny_of_exportR`, `callsToAny_of_regionCallee`, `linkedEnvOn`,
  `summaryTableL`, `denoteAt_linkedEnvOn`, `procsAgree_summaryTableL`: every `call` of a program
  the back half compiles at a table names a function of the table, and such a program denotes
  the same at the environment of these functions alone, whose table of summaries agrees with
  it. `callsTo`, `linkedEnvAt`, `summaryTable` are these at one function.
* `CallRoom`, `sContract_guarded`, `CalleeKind.spec_guard`: the precondition of a linked
  function at its call sites, and a run relation that meets the specification of a kind meets
  it when guarded by the precondition of the interface of the kind.
* `CalleeKind.Top`, `outCallee_facts`, `regCallee_facts`, `wordCallee_arrArgs`,
  `CalleeKind.Top.facts`, `CalleeKind.Top.ok`: the top hypotheses of a callee of a kind, and
  the summary, the interface and the hypotheses of the calls of a symbol of a table they give.
* `CalleeTab.eq_one_of_sublist`, `compileRegion_correct_linked_multi`: the correctness of a
  calling body with a table of linked kernels, under the oracle of the callees and, at blocks
  that are item streams, through the calls.
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
* `find?_name_of_nodup`: the linked function of a name among functions with distinct names.
* `wordCallee_linkedSummary`, `LinkedFn.CallSitePre`, `LinkedWordKernel`: the summary of a
  linked word kernel, the precondition of a linked function under the resources of its
  calls, and the machine contract of a linked function with scalar parameters and a word
  result, whose code meets its word interface and whose precondition holds under the
  resources of every call at whose arguments its meaning is defined.
* `regions_of_entryAt`: the entry conditions of a layout with at most one read-only pointer
  region from the resources of a call.
* `LinkedWordKernel.of_sig`, `LinkedWordKernel.wordCallee`: a linked word kernel from code
  meeting the interface of its data, and its summary at its call sites.
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

/-- The gate `imgGateCBW` reads the frame map only through which names have a frame word. -/
theorem imgGateCBW_congr {frame frame' : String → Option (BitVec 64)}
    (h : ∀ q, (frame q).isSome = (frame' q).isSome)
    (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    X86Backend.ImageAddrCallW.imgGateCBW frame slotArr body
      = X86Backend.ImageAddrCallW.imgGateCBW frame' slotArr body := by
  have hn : ∀ q, (frame q).isNone = (frame' q).isNone := fun q => by
    have := h q; cases e : frame q <;> cases e' : frame' q <;> simp_all
  have hi : ∀ k x, X86Backend.ImageAddrSimW.instrGateBW frame slotArr body k x
      = X86Backend.ImageAddrSimW.instrGateBW frame' slotArr body k x := by
    intro k x
    have hcg : X86Backend.ImageAddrSimW.castGateB frame x
        = X86Backend.ImageAddrSimW.castGateB frame' x := by
      simp only [X86Backend.ImageAddrSimW.castGateB, hn]
    simp only [X86Backend.ImageAddrSimW.instrGateBW, X86Backend.ImageAddrSimW.gateAtW,
      X86Backend.ImageAddrSimW.carryOkB, X86Backend.ImageAddrSimW.oneBitAt_congr h,
      X86Backend.ImageAddrFrame.icase_congr h, X86Backend.ImageAddrSimW.gateReadSet_congr h,
      X86Backend.ImageAddrSimW.regGateBW_congr h, X86Backend.ImageAddrSimW.sImmB_congr h,
      X86Backend.ImageAddrSimW.sCmovB_congr h, hcg, hn, h]
  have hc : ∀ k x, X86Backend.ImageAddrCallW.cidxArmCW frame slotArr body k x
      = X86Backend.ImageAddrCallW.cidxArmCW frame' slotArr body k x := by
    intro k x
    simp only [X86Backend.ImageAddrCallW.cidxArmCW, X86Backend.ImageAddrCidx.cidxArmB,
      X86Backend.ImageAddrCidx.cidxArmAt, X86Backend.ImageAddrSimW.oneBitAt_congr h, hn]
  simp only [X86Backend.ImageAddrCallW.imgGateCBW, hi, hc]

/-- The gate of a calling body at the restricted frame of the body at any stack pointer is
    the gate at `frameMark (frameNames body)`. -/
theorem imgGateCBW_frameMark (body : Lcmd) (r : BitVec 64)
    (slotArr : String → Option (String × Nat)) :
    X86Backend.ImageAddrCallW.imgGateCBW (X86Backend.ImageAddrFrame.frameIn body
        (X86Backend.DecodePrintedAddr.frameP (X86Backend.LprogBytesDecode.Params.ofBody body) r))
        slotArr body
      = X86Backend.ImageAddrCallW.imgGateCBW
        (X86Backend.ImageAddrFrame.frameMark (X86Backend.ImageAddrFrame.frameNames body))
        slotArr body :=
  imgGateCBW_congr (fun q => (X86Backend.ImageAddrFrame.frameMark_isSome body r q).symm)
    slotArr body

/-- The check `bitsDeadB` reads the frame map only through which names have a frame word. -/
theorem bitsDeadB_congr {frame frame' : String → Option (BitVec 64)}
    (h : ∀ q, (frame q).isSome = (frame' q).isSome) (D : X86Backend.ImageAddrCall.DeadTab)
    (body : Lcmd) :
    X86Backend.ImageAddrCallW.bitsDeadB frame D body
      = X86Backend.ImageAddrCallW.bitsDeadB frame' D body := by
  simp only [X86Backend.ImageAddrCallW.bitsDeadB, X86Backend.ImageAddrSimW.oneBitAt_congr h]

/-- The check `bitsDeadB` at the restricted frame of the body at any stack pointer is the
    check at `frameMark (frameNames body)`. -/
theorem bitsDeadB_frameMark (body : Lcmd) (r : BitVec 64) (D : X86Backend.ImageAddrCall.DeadTab) :
    X86Backend.ImageAddrCallW.bitsDeadB (X86Backend.ImageAddrFrame.frameIn body
        (X86Backend.DecodePrintedAddr.frameP (X86Backend.LprogBytesDecode.Params.ofBody body) r))
        D body
      = X86Backend.ImageAddrCallW.bitsDeadB
        (X86Backend.ImageAddrFrame.frameMark (X86Backend.ImageAddrFrame.frameNames body)) D body :=
  bitsDeadB_congr (fun q => (X86Backend.ImageAddrFrame.frameMark_isSome body r q).symm) D body

/-- **Soundness of `callParamsAtB` at the wide gate.** Under `ImgSep`, the positionwise gate
    `ImageAddrSimW.ImgGateW` at any exempt set and `ImgRel`, when the operands at the position
    of the address state pass `callParamsAtB` against `c`, the operands of the call site
    `calleeSiteAt` at that position pass the parameters of `c` (`LinkedFnCallee.ParamAt`): a
    scalar parameter is its operand, and the register of an array parameter holds the base of
    the array of its operand, an array of the slot map of the length of the parameter
    (`ImageAddrSimW.ImgGateW.ptr_of_reloadW`). -/
theorem callParamsAtB_forall₂W {c : CalleeData} {sl : String → Option (String × Nat)}
    {body : Lcmd} {frame : String → Option (BitVec 64)} {base : String → BitVec 64}
    {rsp : BitVec 64} (hsep : X86Backend.ImageAddrSim.ImgSep frame sl base rsp)
    {X : Nat → Prop} (hgate : X86Backend.ImageAddrSimW.ImgGateW frame sl body X)
    {s : JasminLsemMemFlagGuard.LstateMF} {sa : VIR.JasminLsemAddrMem.LstateA} {zf : Bool}
    (hrel : X86Backend.ImageAddrSim.ImgRel frame sl base body s sa zf)
    (h : callParamsAtB c sl body sa.reg.lpc = true) :
    List.Forall₂ (X86Backend.LinkedFnCallee.ParamAt sl base sa) c.ins
      (calleeSiteAt c sl body sa.reg.lpc).2 := by
  have hp := (callParamsAtB_spec h).1
  rw [calleeSiteAt_snd]
  refine List.forall₂_iff_zip.mpr
    ⟨(c.siteArgs_length sl body _).symm, fun {q x} hqx => ?_⟩
  have hq := hp (q, x) hqx
  simp only [paramAtB, Bool.and_eq_true] at hq
  obtain ⟨hgp, hk⟩ := hq
  refine ⟨hgp, ?_⟩
  obtain ⟨pn, k⟩ := q
  cases k with
  | scalar => simpa using hk
  | words m =>
      simp only [beq_iff_eq] at hk
      obtain ⟨q, hq, hptr⟩ := X86Backend.ImageAddrSimW.ImgGateW.ptr_of_reloadW hsep hgate
        (X86Backend.ImageAddrSimW.imgRelW_of hrel) hk (hsep.gp pn hgp)
      exact ⟨⟨q, hq⟩, hptr⟩

/-- **Soundness of `callParamsB` at the wide gate**: `callParamsAtB_forall₂W` at a call, whose
    operands pass `callParamsAtB` under `callParamsB`. -/
theorem callParamsB_forall₂W {c : CalleeData} {sl : String → Option (String × Nat)}
    {body : Lcmd} (h : callParamsB c sl body = true)
    {frame : String → Option (BitVec 64)} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : X86Backend.ImageAddrSim.ImgSep frame sl base rsp) {X : Nat → Prop}
    (hgate : X86Backend.ImageAddrSimW.ImgGateW frame sl body X)
    {s : JasminLsemMemFlagGuard.LstateMF} {sa : VIR.JasminLsemAddrMem.LstateA} {zf : Bool}
    (hrel : X86Backend.ImageAddrSim.ImgRel frame sl base body s sa zf)
    (hcall : ∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) :
    List.Forall₂ (X86Backend.LinkedFnCallee.ParamAt sl base sa) c.ins
      (calleeSiteAt c sl body sa.reg.lpc).2 := by
  obtain ⟨bi, ra, t, hb, hbi⟩ := hcall
  refine callParamsAtB_forall₂W hsep hgate hrel ?_
  simp only [callParamsB, callParamsSelB, List.all_eq_true, List.mem_range] at h
  have hp := h _ (List.getElem?_eq_some_iff.mp hb).1
  rw [hb] at hp
  simpa [hbi, X86Backend.ImageAddrCall.isCallB] using hp

/-! ## 3. The back half at a table of linked functions -/

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
      ∧ calleeBytes (some (CalleeTab.one c)) b = some bytes
      ∧ regionCoB σ exportReg b t r.code r.res cert (some (CalleeTab.one c)) a.fname = true
      ∧ ∃ P0, regionLprogC a (legalizeRegion p) (some (CalleeTab.one c)) (regionWebsEx σ exportReg)
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
        | some T' =>
          obtain rfl := regionCallee_singleton hc
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
    body `b` are the bytes of the relocating encoder at the symbol map
    `calleeSym (CalleeTab.one c) b`
    followed by the code of `c`, which is nonempty; the instructions of `b` have the shapes
    `ds`; and the items of `b` at that symbol map pass the branch check and denote a
    program `prog` whose first instruction is the prologue `leaFrame` of the frame of `b`.
    These are the byte hypotheses of `CheckedIsaCall.haltsC_of_linkedChecksKW`. -/
theorem calleeBytes_some {c : CalleeData} {b : Lcmd} {bytes : List (BitVec 8)}
    (h : calleeBytes (some (CalleeTab.one c)) b = some bytes) :
    bytes = X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym (CalleeTab.one c) b) b
        ++ c.bytes
      ∧ c.bytes ≠ []
      ∧ ∃ ds prog,
        X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
        ∧ X86Backend.LprogBytesLinkReloc.branchOKReloc
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)
          (X86Backend.LprogBytesDecode.decCount
            (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
              (X86Backend.LprogBytesDecode.Params.ofBody b) b ds))
          (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym (CalleeTab.one c) b) b).length 0
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds) = true
        ∧ X86Backend.LprogBytesLinkReloc.expectedReloc
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)
          (X86Backend.LprogBytesDecode.decCount
            (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
              (X86Backend.LprogBytesDecode.Params.ofBody b) b ds))
          (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym (CalleeTab.one c) b) b).length
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds) = some prog
        ∧ prog[0]? = some (.op (X86Backend.PhysAbiShape.leaFrame
          (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody b).frame)))) := by
  simp only [calleeBytes, CalleeTab.bytes_one] at h
  split at h
  · rename_i hc
    obtain rfl := (Option.some.inj h).symm
    simp only [calleeLinkB_one, Bool.and_eq_true] at hc
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
    of a printed body `b` of the class `ImageAddrCallW.printedAddrCWB` at the frame of `c` be
    `bytes`, and let `prog` be the program `calleeProg (CalleeTab.one c) b` of the function. Then
    `bytes`
    are the bytes of an item list `items` (the items `fundefItemsRelocL` of `b`) followed by
    the code of `c`; every item of `items` passes `ItemOK`; and the layout of `items`
    resolves to `prog` inside the layout of `items` followed by any layout whose first
    instruction starts at the byte length of `items`
    (`LprogBytesLinkReloc.encodeLfundefBytesReloc_eq_itemBytesL`,
    `LprogBytesLinkReloc.resolveAll_layout_reloc`). -/
theorem calleeBytes_items {c : CalleeData} {b : Lcmd} {bytes : List (BitVec 8)}
    (h : calleeBytes (some (CalleeTab.one c)) b = some bytes)
    (hpr : X86Backend.ImageAddrCallW.printedAddrCWB c.frame b = true)
    {prog : List X86Backend.LprogBytesDecode.RInstr}
    (hprog : calleeProg (CalleeTab.one c) b = some prog) :
    ∃ items : List X86Backend.LprogBytesDecode.Item,
      bytes = X86Backend.LprogBytesDecode.itemBytes items ++ c.bytes
      ∧ (∀ it ∈ items, X86Backend.LprogBytesDecode.ItemOK it)
      ∧ ∀ e x tl, X86Backend.LprogBytesDecode.resolveAll
          (X86Backend.LprogBytesDecode.layoutAt 0 items
            ++ ((X86Backend.LprogBytesDecode.itemBytes items).length, e, x) :: tl)
          (X86Backend.LprogBytesDecode.layoutAt 0 items) = some prog := by
  obtain ⟨rfl, -, ds, prog', hss, hbr, hP, -⟩ := calleeBytes_some h
  have hpp : prog' = prog := by
    simp only [calleeProg_one, hss] at hprog
    rw [hP] at hprog
    exact Option.some.inj hprog
  subst hpp
  obtain ⟨hsaves, hF0, hFr⟩ := X86Backend.ImageAddrCallW.printedAddrCWB_reloc hpr
  have hsh := X86Backend.LprogBytesLinkReloc.relocDShapeOK_of_shapes _ hss
  have hbytes := X86Backend.LprogBytesLinkReloc.encodeLfundefBytesReloc_eq_itemBytesL
    (calleeSym (CalleeTab.one c) b) b ds hsaves hsh
  have hok := X86Backend.LprogBytesLinkReloc.fundefItemsRelocL_ok (calleeSym (CalleeTab.one c) b)
    (X86Backend.LprogBytesDecode.Params.ofBody b) b ds hF0 hFr hsh
  refine ⟨_, by rw [hbytes], hok, fun e x tl => ?_⟩
  rw [hbytes] at hbr hP
  rw [X86Backend.LprogBytesLinkReloc.resolveAll_layout_reloc _ hok _ _ _ (fun q hq => ?_) _ 0
    hbr]
  · exact hP
  · have hlt : ∀ z ∈ X86Backend.LprogBytesDecode.layoutAt 0
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds),
        z.1 < (X86Backend.LprogBytesDecode.itemBytes
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)).length :=
      fun z hz => by simpa using X86Backend.LprogBytesLink.layoutAt_start_lt _ hok 0 z hz
    have hnone : (X86Backend.LprogBytesDecode.layoutAt 0
        (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
          (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)).findIdx?
        (fun z => decide (z.1 = (X86Backend.LprogBytesDecode.itemBytes
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym (CalleeTab.one c) b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)).length)) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro z hz
      have := hlt z hz
      exact decide_eq_false (by omega)
    simp [List.findIdx?_append, hnone, List.findIdx?_cons, hq,
      X86Backend.LprogBytesDecode.layoutAt_length]

/-- The table `regionCallee` finds is nonempty. -/
theorem regionCallee_fns_ne_nil {linked : List CalleeData} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {code : List JasminLsemMem.LinstrRM}
    {T : CalleeTab} (h : regionCallee linked p code = some (some T)) : T.fns ≠ [] := by
  obtain ⟨-, hne, hall, rfl⟩ := regionCallee_tab h
  obtain ⟨f, fs, hfs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨c, hc, rfl⟩ := hall f (by simp [hfs])
  exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hc, by simp [hfs]⟩)

/-- **A result of the back half on a program with `call`, at its table.** For a result of
    `compileRegion σ a p linked` on a program `p` with a `call`, the legalised program has an
    export `r0` at whose code `regionCallee` finds the table `T`, the result type is a word
    array, the program passes `regionExportableB`, and a printed body `b` has the bytes
    `calleeBytes` at `T`, passes the gate `regionCoB` at `T` and the function name `a.fname`
    at the code and returned operands of the webs `r` and the allocation certificate `cert` of
    `regionLprogC`, and passes the constant-time check `calleeCtB` at `T`. -/
theorem compileRegion_spec_tab {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) :
    ∃ (T : CalleeTab) (r0 : Exported),
      exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 = some r0
      ∧ regionCallee linked (legalizeRegion p) r0.code = some (some T)
      ∧ (∃ w m, t = .stackArr w m) ∧ regionExportableB (legalizeRegion p) = true
      ∧ ∃ r b cert,
        regionWebs (regionWebsEx σ exportReg) r0 (calleeAAT (some T)) (calleeAOT (some T)) = r
        ∧ calleeBytes (some T) b = some bytes
        ∧ regionCoB σ exportReg b t r.code r.res cert (some T) a.fname = true
        ∧ calleeCtB σ exportReg (some T) b t r.code r.res cert = true
        ∧ ∃ P0, regionLprogC a (legalizeRegion p) (some T) (regionWebsEx σ exportReg)
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
        | some T =>
          split at h
          · rename_i P0 cert hP
            obtain ⟨b, hbs, hg⟩ := regionEncode_spec_callee h
            rw [Bool.and_eq_true] at hg
            exact ⟨T, r, hr, hc, regionCallee_some_stackArr hc, hB, _, b, cert, rfl, hbs, hg.1,
              hg.2, P0, hP⟩
          · cases h
      · cases h
    · cases h
  · cases h

/-- **A table found among linked functions is found at its own functions.** For a result of
    `compileRegion σ a p linked` on a program `p` with a `call`, the table `T` the back half
    finds is a nonempty sublist of `linked`, and `compileRegion σ a p T.fns` gives the same
    result. At one linked function the table is that function (`compileRegion_singleton`). -/
theorem compileRegion_tab {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData}
    {r : Lprog × List (BitVec 8)} (h : compileRegion σ a p linked = some r)
    (hcf : p.callFree = false) :
    ∃ T : CalleeTab, T.fns.Sublist linked ∧ T.fns ≠ [] ∧ compileRegion σ a p T.fns = some r := by
  unfold compileRegion at h
  split at h
  · rename_i hB
    split at h
    · rename_i r' hr
      split at h
      · rename_i callee hc
        cases callee with
        | none =>
          rw [← legalizeRegion_callFree_eq, regionCallee_callFree hc] at hcf
          cases hcf
        | some T =>
          refine ⟨T, regionCallee_sublist hc, regionCallee_fns_ne_nil hc, ?_⟩
          unfold compileRegion
          rw [ite_eq_left hB]
          simp only [hr, regionCallee_self hc]
          exact h
      · cases h
    · cases h
  · cases h

/-- **The bytes of a calling body at a table.** The bytes `calleeBytes` at the table `T` of a
    printed body `b` are the bytes of the relocating encoder at the symbol map `calleeSym T b`
    followed by the code of `T`, the code of each function of `T` is nonempty, the instructions
    of `b` have the shapes `ds`, and the items of `b` at that symbol map pass the branch check
    and denote the program `prog` of the function (`calleeProg T b`) under the target map
    `CalleeTab.linkMap` at the instruction count and the byte length of the function; the
    first instruction of `prog` is the prologue `leaFrame` of the frame of `b`. -/
theorem calleeBytes_tab {T : CalleeTab} {b : Lcmd} {bytes : List (BitVec 8)}
    (h : calleeBytes (some T) b = some bytes) :
    bytes = X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym T b) b ++ T.bytes
      ∧ (∀ c ∈ T.fns, c.bytes ≠ [])
      ∧ ∃ ds prog,
        X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
        ∧ X86Backend.LprogBytesLinkReloc.branchOKRelocMap
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym T b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)
          (X86Backend.LprogBytesLinkReloc.symTgt (T.linkMap
            (X86Backend.LprogBytesDecode.decCount
              (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym T b)
                (X86Backend.LprogBytesDecode.Params.ofBody b) b ds))
            (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym T b) b).length)) 0
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym T b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds) = true
        ∧ X86Backend.LprogBytesLinkReloc.expectedRelocMap
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym T b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds)
          (X86Backend.LprogBytesLinkReloc.symTgt (T.linkMap
            (X86Backend.LprogBytesDecode.decCount
              (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym T b)
                (X86Backend.LprogBytesDecode.Params.ofBody b) b ds))
            (X86Backend.LprogBytes.encodeLfundefBytesReloc (calleeSym T b) b).length))
          (X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (calleeSym T b)
            (X86Backend.LprogBytesDecode.Params.ofBody b) b ds) = some prog
        ∧ calleeProg T b = some prog
        ∧ prog[0]? = some (.op (X86Backend.PhysAbiShape.leaFrame
          (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody b).frame)))) := by
  simp only [calleeBytes] at h
  split at h
  · rename_i hc
    obtain rfl := (Option.some.inj h).symm
    simp only [calleeLinkB, Bool.and_eq_true] at hc
    obtain ⟨⟨hne, -⟩, hm⟩ := hc
    refine ⟨rfl, fun c hc' => by simpa using List.all_eq_true.mp hne c hc', ?_⟩
    cases hss : X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b
      with
    | none => simp only [hss] at hm; cases hm
    | some ds =>
      simp only [hss, Bool.and_eq_true] at hm
      obtain ⟨hbr, hP⟩ := hm
      obtain ⟨prog, hprog⟩ := Option.isSome_iff_exists.mp hP
      refine ⟨ds, prog, rfl, hbr, hprog, by simp only [calleeProg, hss]; exact hprog, ?_⟩
      have h2 := hprog
      conv at h2 => lhs; arg 3; unfold X86Backend.LprogBytesLinkReloc.fundefItemsRelocL
      simp only [X86Backend.LprogBytesLinkReloc.expectedRelocMap,
        X86Backend.LprogBytesDecode.mkLea, Option.map_eq_some_iff] at h2
      obtain ⟨rest, -, rfl⟩ := h2
      rfl
  · cases h

/-- **Every call of a calling body names a function of the table**: under the decode
    `decodeSites` at the table and a closing return. -/
theorem lookup_of_call {T : CalleeTab} {sl : String → Option (String × Nat)} {body : Lcmd}
    (hd : (decodeSites T.lookup sl body).isSome = true)
    (hl : body.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true)
    {p : Nat} {bi : Linstr} {ra : Option String} {f : String} {l : LLabel}
    (hb : body[p]? = some bi) (hbi : bi.li_i = .Lcall ra (f, l)) :
    ∃ c, T.lookup f = some c := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb
  by_cases hp : p < body.length - 1
  · exact Option.isSome_iff_exists.mp
      (X86Backend.ImageAddrCall.bodyCallSymsB_spec (bodyCallSymsB_of_decodeSites hd) hb hp hbi)
  · have hpl : p = body.length - 1 := by omega
    subst hpl
    simp [List.getLast?_eq_getElem?, hb, hbi, X86Backend.DecodePrinted.isRetB] at hl

/-- **The remote symbols of a calling body of the class are symbols of the table**: under the
    class `printedAddrCWB` and the decode `decodeSites` at the table, every remote transfer of
    the body is a call of a symbol of the table (`lookup_of_call`). -/
theorem remoteSym_mem_names {T : CalleeTab} {sl : String → Option (String × Nat)} {b : Lcmd}
    {G : Nat} (hpr : X86Backend.ImageAddrCallW.printedAddrCWB G b = true)
    (hd : (decodeSites T.lookup sl b).isSome = true) :
    ∀ i ∈ b, ∀ f, X86Backend.LprogBytes.remoteSym i.li_i = some f → f ∈ T.names := by
  intro i hi f hf
  obtain ⟨ra, l, hli⟩ := X86Backend.ImageAddrCallW.printedAddrCWB_remote hpr hi hf
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hi
  have hl : b.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true := by
    simp only [X86Backend.ImageAddrCallW.printedAddrCWB, Bool.and_eq_true] at hpr
    exact hpr.1.1.1.2
  obtain ⟨c, hc⟩ := lookup_of_call hd hl hp hli
  obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
  exact List.mem_map_of_mem hcm

/-! ## 4. Guarded callees -/

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

/-! ## 5. The source run at the functions of a table -/

/-- **The call environment of the linked functions of a module alone**: `tableEnv` at the
    table of the linked functions of `m` over the table that answers no call. A call of a
    linked function is answered by its meaning `LinkedFn.sem`; every other call refuses. -/
def linkedEnv (m : CatCrypt.Crypto.Hax.HaxModule) : CallEnv jasminDialect :=
  tableEnv (m.linkTable fun _ _ => none)

/-- At the name of a function of a list with distinct names, the first function with that
    name is the function. -/
theorem find?_name_of_nodup {ls : List CatCrypt.Crypto.Hax.LinkedFn} (hnd : (ls.map (·.name)).Nodup)
    {l : CatCrypt.Crypto.Hax.LinkedFn} (hl : l ∈ ls) : ls.find? (·.name == l.name) = some l := by
  cases hf : ls.find? (·.name == l.name) with
  | none => exact absurd (List.find?_eq_none.mp hf l hl) (by simp)
  | some l' =>
      have h1 := List.mem_of_find?_eq_some hf
      have h2 : l'.name = l.name := by simpa using List.find?_some hf
      rw [List.inj_on_of_nodup_map hnd h1 hl h2]


/-- **Every `call` of the program names a symbol of `fs`** (the name-level form of
    `ExportNF.onlyCalls`). -/
def callsToAny (fs : List String) : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => callsToAny fs k
  | _, _, .forLoop _ _ body k => callsToAny fs body && callsToAny fs k
  | _, _, .ifThenElse _ thn els k => callsToAny fs thn && callsToAny fs els && callsToAny fs k
  | _, _, .whileLoop _ body k => callsToAny fs body && callsToAny fs k
  | _, _, .call g _ k => fs.contains g && callsToAny fs k

/-- `callsToAny fs` reads only the calls. -/
theorem callTest_callsToAny (fs : List String) :
    CallTest (fun g => fs.contains g) (callsToAny fs) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- **The region legalisation keeps the value of `callsToAny fs`.** -/
theorem callsToAny_legalizeRegion (fs : List String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : callsToAny fs (legalizeRegion p) = callsToAny fs p :=
  legalizeRegion_callTest (callTest_callsToAny fs) p

/-- **The calls of an exported program are among its shadow instructions**: when every
    shadow instruction of the export of `p` names a symbol of `fs`, every `call` of `p` names
    a symbol of `fs`. -/
theorem callsToAny_of_exportR {nArgs : Nat} {fn : String} {fs : List String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat}
    {I : LprogIsa.IsaData} {r : Exported} (h : exportR nArgs fn p d n I = some r)
    (hsh : ∀ i ∈ r.code, ∀ v, LprogIsa.shadowCall? i.fst = some v → v.2.1 ∈ fs) :
    callsToAny fs p = true := by
  induction p generalizing d n r with
  | ret vs => rfl
  | var e k ih =>
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      exact ih hk fun i hi => hsh i (by simp [Exported.prepend, hi])
  | forLoop count inits body k ihb ihk =>
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      simp only [callsToAny, Bool.and_eq_true]
      exact ⟨ihb hb fun i hi => hsh i (by simp [Exported.prepend, forArrFrame, hi]),
        ihk hk fun i hi => hsh i (by simp [Exported.prepend, hi])⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨rt, ht, re, he, rk, hk, rfl⟩ := h
      simp only [callsToAny, Bool.and_eq_true]
      exact ⟨⟨iht ht fun i hi => hsh i (by simp [Exported.prepend, ifFrame, hi]),
        ihe he fun i hi => hsh i (by simp [Exported.prepend, ifFrame, hi])⟩,
        ihk hk fun i hi => hsh i (by simp [Exported.prepend, hi])⟩
  | whileLoop inits body k ihb ihk =>
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      simp only [callsToAny, Bool.and_eq_true]
      exact ⟨ihb hb fun i hi => hsh i (by simp [Exported.prepend, whileFrame, hi]),
        ihk hk fun i hi => hsh i (by simp [Exported.prepend, hi])⟩
  | call g args k ih =>
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      simp only [callsToAny, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq]
      refine ⟨?_, ih hk fun i hi => hsh i (by simp [Exported.prepend, hi])⟩
      exact hsh (callI (regName d) g (exprArgsHV d nArgs argName (fun _ => none) args))
        (by simp [Exported.prepend]) _ (LprogIsa.shadowCall?_callShadow _ _ _)

/-- **Every call of a program the back half compiles at a table names a function of the
    table.** `regionCallee` takes the table of the linked functions of the symbols the shadow
    instructions of the export call, and every `call` of the program is a shadow instruction
    of the export (`callsToAny_of_exportR`). -/
theorem callsToAny_of_regionCallee {fn : String} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {r0 : Exported} {linked : List CalleeData}
    {T : CalleeTab} (hr0 : exportR Γ.length fn (legalizeRegion p) Γ.length 0 = some r0)
    (hc : regionCallee linked (legalizeRegion p) r0.code = some (some T)) :
    callsToAny T.names p = true := by
  rw [← callsToAny_legalizeRegion]
  refine callsToAny_of_exportR hr0 fun i hi v hv => ?_
  obtain ⟨-, -, hall, hT⟩ := regionCallee_tab hc
  have hmem : v.2.1 ∈ codeCallSyms r0.code := by
    rw [codeCallSyms, List.mem_eraseDups]
    exact List.mem_filterMap.mpr ⟨i, hi, by rw [hv]; rfl⟩
  obtain ⟨d, hd, hdv⟩ := hall _ hmem
  rw [hT]
  exact List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hd, by simp [hdv, hmem]⟩, hdv⟩

/-- **The environment of the linked functions of `m` restricted to the names `fs`.** -/
def linkedEnvOn (m : CatCrypt.Crypto.Hax.HaxModule) (fs : List String) :
    CallEnv jasminDialect :=
  tableEnv fun g vals => if g ∈ fs then m.linkTable (fun _ _ => none) g vals else none

/-- **The table of the summaries of the linked functions `ls`**: the summary `linkedSummary`
    of the first function of `ls` with a name. -/
def summaryTableL (ls : List CatCrypt.Crypto.Hax.LinkedFn) : LprogIsa.ProcTable := fun f =>
  (ls.find? (·.name == f)).map linkedSummary

/-- **A program whose calls name symbols of `fs` denotes the same at the environment restricted
    to `fs`**: the two environments answer every call of a symbol of `fs` alike. -/
theorem denoteAt_linkedEnvOn {m : CatCrypt.Crypto.Hax.HaxModule} {fs : List String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : callsToAny fs p = true) (k : Nat) (V : Ctxt.Valuation Γ) :
    p.denoteAt (linkedEnvOn m fs) k V = p.denoteAt (linkedEnv m) k V := by
  unfold NFProg.denoteAt
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.denote, ih hp]
  | forLoop count inits body k ihb ihk =>
      simp only [callsToAny, Bool.and_eq_true] at hp
      simp only [NFProg.denote, ihb hp.1, ihk hp.2]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [callsToAny, Bool.and_eq_true] at hp
      simp only [NFProg.denote, iht hp.1.1, ihe hp.1.2, ihk hp.2]
  | whileLoop inits body k ihb ihk =>
      simp only [callsToAny, Bool.and_eq_true] at hp
      simp only [NFProg.denote, ihb hp.1, ihk hp.2]
  | call g args k ih =>
      simp only [callsToAny, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hp
      obtain ⟨hg, hk⟩ := hp
      simp only [NFProg.denote, ih hk, linkedEnvOn, linkedEnv, tableEnv, hg, ↓reduceIte]

/-- **The table of the summaries of linked functions of a module agrees with the environment of
    these functions alone.** For linked functions `ls` of a module whose linked functions have
    distinct names, whose meanings return values only on arguments of their parameter kinds
    and whose result types are no slice, `summaryTableL ls` agrees with
    `linkedEnvOn m (ls.map (·.name))`: both are the table and the environment of the module with
    the functions of `ls` as its linked functions (`procsAgree_tableEnv_linkTable`). -/
theorem procsAgree_summaryTableL {m : CatCrypt.Crypto.Hax.HaxModule}
    (hnd : (m.linked.map (·.name)).Nodup) {ls : List CatCrypt.Crypto.Hax.LinkedFn}
    (hls : ∀ l ∈ ls, l ∈ m.linked)
    (hargs : ∀ l ∈ ls, ∀ vals v, l.sem vals = some v → vals.map valKind = linkedKinds l)
    (hres : ∀ l ∈ ls, ∀ t, l.res ≠ .slice t) :
    ProcsAgree (linkedEnvOn m (ls.map (·.name))) (summaryTableL ls) := by
  have hfind : ∀ g, g ∈ ls.map (·.name) → ∃ l ∈ ls,
      m.linked.find? (·.name == g) = some l ∧ ls.find? (·.name == g) = some l := by
    intro g hg
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
    refine ⟨l, hl, find?_name_of_nodup hnd (hls l hl), ?_⟩
    cases hf : ls.find? (·.name == l.name) with
    | none => exact absurd (List.find?_eq_none.mp hf l hl) (by simp)
    | some l' =>
        have h1 := List.mem_of_find?_eq_some hf
        have h2 : l'.name = l.name := by simpa using List.find?_some hf
        rw [List.inj_on_of_nodup_map hnd (hls l' h1) (hls l hl) h2]
  have hnone : ∀ g, g ∉ ls.map (·.name) → ls.find? (·.name == g) = none := by
    intro g hg
    refine List.find?_eq_none.mpr fun l hl hlg => hg ?_
    exact List.mem_map.mpr ⟨l, hl, by simpa using hlg⟩
  have hbi : (fun g vals => if g ∈ ls.map (·.name)
        then m.linkTable (fun _ _ => none) g vals else none)
      = ({ m with linked := ls } : CatCrypt.Crypto.Hax.HaxModule).linkTable
          (fun _ _ => none) := by
    funext g vals
    by_cases hg : g ∈ ls.map (·.name)
    · obtain ⟨l, -, hm, hs⟩ := hfind g hg
      simp [CatCrypt.Crypto.Hax.HaxModule.linkTable, CatCrypt.Crypto.Hax.linkBi, hg, hm, hs]
    · simp [CatCrypt.Crypto.Hax.HaxModule.linkTable, CatCrypt.Crypto.Hax.linkBi, hg,
        hnone g hg]
  have htab : summaryTableL ls
      = procTableOf ({ m with linked := ls } : CatCrypt.Crypto.Hax.HaxModule)
          LprogIsa.ProcTable.empty := by
    funext g
    simp only [summaryTableL, procTableOf]
    cases ls.find? (·.name == g) <;> rfl
  unfold linkedEnvOn
  rw [hbi, htab]
  exact procsAgree_tableEnv_linkTable _ hargs hres
    (procsAgree_tableEnv_empty fun _ _ _ h => by cases h)

/-! ## 6. Correctness of a calling body with a table of linked kernels -/

section Table

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind CallAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain (InsLayout insSummary
  insSummary_retWord)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee (WordLayout OutLayout outSig
  outSummary ParamAt readIns readIns_entry)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (WordCallee FootBelow CallerSep
  exemptC)
open CatCrypt.Crypto.SecureCompilation.SepLogic (SContract)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall (guarded)

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

/-- **A run relation that meets the contract of `l` meets it when guarded** by the
    precondition of the interface `l.contractSig args res`: an entry state that satisfies
    the precondition of the contract at some logical variables satisfies that of the
    interface. -/
theorem sContract_guarded {l : CatCrypt.Crypto.Hax.LinkedFn} {X : CalleeRun}
    (h : SContract X l.contract) (args : List String) (res : Option String) :
    SContract (guarded (l.contractSig args res) X) l.contract where
  halts a s hs := let ⟨t, s', hx⟩ := h.halts a s hs; ⟨t, s', ⟨a, hs⟩, hx⟩
  post a s t s' hs hx := h.post a s t s' hs hx.2
  keep a s t s' hs hx := h.keep a s t s' hs hx.2
  ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hx₁ hx₂ :=
    h.ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hx₁.2 hx₂.2

/-- **A run relation that meets the specification of a kind meets it when guarded** by the
    precondition of the interface of the kind (`calleeSpec_guard`, `sContract_guarded`). -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets.CalleeKind.spec_guard
    {X : CalleeRun} {k : CalleeKind} (h : k.Spec X) : k.Spec (guarded k.sig X) := by
  cases k with
  | word c res pr room => exact calleeSpec_guard h
  | outO l ins po n => exact calleeSpec_guard h
  | ins l ins res => exact sContract_guarded h _ _
  | outC l ins po n => exact sContract_guarded h _ _

/-- **The top hypotheses of a callee of a kind**, at its callee data `c`: the hypotheses of the
    correctness theorems at one linked function of that kind (`compileRegion_correct_linked`,
    `compileRegion_correct_linked_outO`, `RegionLinkArr.compileRegion_correct_contract_ins`,
    `RegionLinkArr.compileRegion_correct_contract_out`), less the specification of the
    callee and the summary of its symbol.

    * A word callee `.word sig res pr room` is the data of a linked function `l` with the word
      layout at the argument names and the result register of `c`, at the interface
      `sig = wordSig l c.args c.resReg` with the footprint below the frame of `c`, a word
      callee at the summary `pr` of the arity of `c`, and `room` at every entry state.
    * An out callee `.outO l ins po n` is the data of `l` with the out layout at the
      parameters `ins = c.ins`, as many parameters as `c` has arguments, and its precondition
      at its call sites (`CallRoom`).
    * A contract callee `.ins l ins res` or `.outC l ins po n` is the data of `l` with the
      layout of its kind at `ins = c.ins`, as many parameters as `c` has arguments, distinct
      argument registers and a frame and return word below `2 ^ 64`. -/
def _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets.CalleeKind.Top
    (c : CalleeData) : CalleeKind → Prop
  | .word sig res pr room => ∃ l : CatCrypt.Crypto.Hax.LinkedFn, l.calleeData = some c
      ∧ WordLayout l c.args c.resReg ∧ sig = wordSig l c.args c.resReg ∧ res = c.resReg
      ∧ FootBelow sig c.frame ∧ WordCallee sig res pr room ∧ pr.arity = c.args.length
      ∧ ∀ ret (sA : AState), room (entryOf ret sA)
  | .outO l ins po n => l.calleeData = some c ∧ OutLayout l ins po n ∧ c.ins = ins
      ∧ l.params.length = c.args.length ∧ CallRoom l ins
  | .ins l ins res => l.calleeData = some c ∧ InsLayout l ins res ∧ ins = c.ins
      ∧ res = c.resReg ∧ l.params.length = c.args.length
      ∧ (l.layout.args.map (·.reg)).Nodup ∧ l.frame + 8 ≤ 2 ^ 64
  | .outC l ins po n => l.calleeData = some c ∧ OutLayout l ins po n ∧ c.ins = ins
      ∧ l.params.length = c.args.length
      ∧ (l.layout.args.map (·.reg)).Nodup ∧ l.frame + 8 ≤ 2 ^ 64

/-- **The data of a linked function with an out layout**: an out result of the length of the
    destination at a position `kd` whose parameter is the destination, the array positions of
    the kinds of the parameters, and the clobbered registers, the frame and the bytes of the
    linked function. -/
theorem outCallee_facts {l : CatCrypt.Crypto.Hax.LinkedFn} {c : CalleeData}
    (hc : l.calleeData = some c) {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : OutLayout l ins po n) (hins : c.ins = ins) :
    ∃ kd, c.res = .out n kd ∧ c.ins[kd]? = some (po, .words n)
      ∧ c.arrArgs = CatCrypt.Crypto.Hax.insArrArgs (ins.map (·.2))
      ∧ c.clob = l.clob ∧ c.frame = l.frame ∧ c.bytes = l.bytes := by
  obtain ⟨hcres, -, -, hcclob, hcframe, hcbytes, -, -, -, -, -, hcaa⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc
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
  have hkinds : l.layout.args.map (·.kind) = ins.map (·.2) := by
    have h2 := congrArg (List.map Prod.snd) hL.args
    simpa [List.map_map, Function.comp_def] using h2
  exact ⟨kd, hcr, hins ▸ hdk, by rw [hcaa, hkinds], hcclob, hcframe, hcbytes⟩

/-- **The data of a linked function with a register result**: a register result, and the
    clobbered registers, the frame, the bytes and the array positions of the layout of the
    linked function. -/
theorem regCallee_facts {l : CatCrypt.Crypto.Hax.LinkedFn} {c : CalleeData}
    (hc : l.calleeData = some c) {res : String} (hres : l.layout.result = .reg (phys res)) :
    (∃ r, c.res = .reg r) ∧ c.clob = l.clob ∧ c.frame = l.frame ∧ c.bytes = l.bytes
      ∧ c.arrArgs = CatCrypt.Crypto.Hax.insArrArgs (l.layout.args.map (·.kind)) := by
  obtain ⟨hcres, -, -, hcclob, hcframe, hcbytes, -, -, -, -, -, hcaa⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc
  refine ⟨?_, hcclob, hcframe, hcbytes, hcaa⟩
  cases hcr : c.res with
  | reg r => exact ⟨r, rfl⟩
  | out n kd =>
      rw [hcr] at hcres
      simp [CatCrypt.Crypto.Hax.LinkedFn.calleeRes, hres] at hcres

/-- **The summary and the interface of a callee of a kind under its top hypotheses**: the
    summary has the arity, the array positions and the result length of the data `c`, and its
    declared result kind; the kind is an out kind at an out result of `c`; the interface of the
    kind has the clobbered registers and the result register of the interface of `c`; and the
    summary has no word-array result or the destination of each call site of `c` is among its
    operands. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets.CalleeKind.Top.facts
    {c : CalleeData} {k : CalleeKind} (h : k.Top c) :
    k.summary.arity = c.args.length ∧ k.summary.arrArgs = c.arrArgs
      ∧ k.summary.out = (match c.res with | .out n _ => some n | .reg _ => none)
      ∧ k.summary.Kinded
      ∧ k.isOut = (match c.res with | .out _ _ => true | .reg _ => false)
      ∧ k.sig.clob = c.sig.clob ∧ k.sig.res = c.sig.res
      ∧ (k.summary.RetWord ∨ ∀ (sl : String → Option (String × Nat)) (body : Lcmd) (q : Nat),
          (calleeSiteAt c sl body q).1 ∈ (calleeSiteAt c sl body q).2) := by
  have hmemOut : ∀ {n kd : Nat} {po : String}, c.res = .out n kd →
      c.ins[kd]? = some (po, .words n) → ∀ (sl : String → Option (String × Nat)) (body : Lcmd)
        (q : Nat), (calleeSiteAt c sl body q).1 ∈ (calleeSiteAt c sl body q).2 := by
    intro n kd po hcr hdk sl body q
    have hkd : kd < (c.siteArgs sl body q).length := by
      rw [CalleeData.siteArgs_length]
      exact (List.getElem?_eq_some_iff.mp hdk).1
    simp only [calleeSiteAt, hcr]
    rw [List.getD_eq_getElem _ _ hkd]
    exact List.getElem_mem hkd
  cases k with
  | word sig res pr room =>
    obtain ⟨l, hc, hL, rfl, rfl, -, hw, hpar, -⟩ := h
    obtain ⟨⟨r0, hr0⟩, hcclob, -, -, hcaa⟩ := regCallee_facts hc hL.result
    have hcaa0 : c.arrArgs = fun _ => none := by
      rw [hcaa]
      apply CatCrypt.Crypto.Hax.insArrArgs_of_scalars
      intro k hk
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
      have hm : (a.reg, a.kind) ∈ c.args.map fun w => (phys w, ArgKind.scalar) := by
        rw [← hL.args]
        exact List.mem_map_of_mem (f := fun a => (a.reg, a.kind)) ha
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hm
      exact (Prod.mk.inj hw).2.symm
    refine ⟨hpar, ?_, ?_, LprogIsa.ProcSummary.kinded_of_retWord hw.wordRet, ?_, ?_, ?_,
      .inl hw.wordRet⟩
    · rw [hcaa0]
      exact hw.wordOnly
    · rw [hr0]
      exact hw.wordRet
    · simp [X86Backend.ImageAddrCallMeets.CalleeKind.isOut, hr0]
    · funext x
      simp [X86Backend.ImageAddrCallMeets.CalleeKind.sig, X86Backend.LinkedFnCallee.wordSig,
        CalleeData.sig, hcclob]
    · simp [X86Backend.ImageAddrCallMeets.CalleeKind.sig, X86Backend.LinkedFnCallee.wordSig,
        CalleeData.sig, CalleeData.resReg, hr0, CalleeRes.reg?]
  | outO l ins po n =>
    obtain ⟨hc, hL, hins, hpar, -⟩ := h
    obtain ⟨kd, hcr, hdk, hcaa, hcclob, -, -⟩ := outCallee_facts hc hL hins
    refine ⟨hpar, hcaa.symm, by simp [X86Backend.ImageAddrCallMeets.CalleeKind.summary,
      outSummary, hcr], fun _ _ _ => rfl, by simp [X86Backend.ImageAddrCallMeets.CalleeKind.isOut,
      hcr], ?_, ?_, .inr (hmemOut hcr hdk)⟩
    · funext x
      simp [X86Backend.ImageAddrCallMeets.CalleeKind.sig, outSig, CalleeData.sig, hcclob]
    · simp [X86Backend.ImageAddrCallMeets.CalleeKind.sig, outSig, CalleeData.sig, hcr,
        CalleeRes.reg?]
  | ins l ins res =>
    obtain ⟨hc, hL, rfl, rfl, hpar, -, -⟩ := h
    obtain ⟨⟨r0, hr0⟩, hcclob, -, -, hcaa⟩ := regCallee_facts hc hL.result
    have hkinds : l.layout.args.map (·.kind) = c.ins.map (·.2) := by
      have h2 := congrArg (List.map Prod.snd) hL.args
      simpa [List.map_map, Function.comp_def] using h2
    refine ⟨hpar, by rw [hcaa, hkinds]; rfl,
      by simp [X86Backend.ImageAddrCallMeets.CalleeKind.summary,
      insSummary, hr0], LprogIsa.ProcSummary.kinded_of_retWord (insSummary_retWord l c.ins),
      by simp [X86Backend.ImageAddrCallMeets.CalleeKind.isOut, hr0], ?_, ?_,
      .inl (insSummary_retWord l c.ins)⟩
    · funext x
      simp [X86Backend.ImageAddrCallMeets.CalleeKind.sig,
        CatCrypt.Crypto.Hax.LinkedFn.contractSig, CalleeData.sig, hcclob]
    · simp [X86Backend.ImageAddrCallMeets.CalleeKind.sig,
        CatCrypt.Crypto.Hax.LinkedFn.contractSig, CalleeData.sig, CalleeData.resReg, hr0,
        CalleeRes.reg?]
  | outC l ins po n =>
    obtain ⟨hc, hL, hins, hpar, -, -⟩ := h
    obtain ⟨kd, hcr, hdk, hcaa, hcclob, -, -⟩ := outCallee_facts hc hL hins
    refine ⟨hpar, hcaa.symm, by simp [X86Backend.ImageAddrCallMeets.CalleeKind.summary,
      outSummary, hcr], fun _ _ _ => rfl, by simp [X86Backend.ImageAddrCallMeets.CalleeKind.isOut,
      hcr], ?_, ?_, .inr (hmemOut hcr hdk)⟩
    · funext x
      simp [X86Backend.ImageAddrCallMeets.CalleeKind.sig,
        CatCrypt.Crypto.Hax.LinkedFn.contractSig, CalleeData.sig, hcclob]
    · simp [X86Backend.ImageAddrCallMeets.CalleeKind.sig,
        CatCrypt.Crypto.Hax.LinkedFn.contractSig, CalleeData.sig, hcr, CalleeRes.reg?]

/-- The data of a linked function with a word layout has no array argument. -/
theorem wordCallee_arrArgs {l : CatCrypt.Crypto.Hax.LinkedFn} {c : CalleeData}
    (hc : l.calleeData = some c) (hL : WordLayout l c.args c.resReg) :
    c.arrArgs = fun _ => none := by
  rw [(regCallee_facts hc hL.result).2.2.2.2]
  apply CatCrypt.Crypto.Hax.insArrArgs_of_scalars
  intro k hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
  have hm : (a.reg, a.kind) ∈ c.args.map fun w => (phys w, ArgKind.scalar) := by
    rw [← hL.args]
    exact List.mem_map_of_mem (f := fun a => (a.reg, a.kind)) ha
  obtain ⟨w, -, hw⟩ := List.mem_map.mp hm
  exact (Prod.mk.inj hw).2.symm

/-- **The hypotheses of the calls of a symbol of a table at its kind.** Let the frame map,
    the slot map `sl`, the array bases and the stack register be separated, with the wide
    gate `ImageAddrSimW.ImgGateW` on `body` and the caller separation at the frame bound
    `G`, and let the operands and the code of the calls of `body` pass `callParamsBT` and
    `calleeCodeBT` at the table `T`. For a symbol `f` whose function `c` in `T` has a frame
    of at most `G` bytes and meets the top hypotheses of the kind `k`, the calls of `f` meet
    the hypotheses `CalleeKind.Ok` of `k` at the site function `siteFn T.lookup sl body`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets.CalleeKind.Top.ok
    {frame : String → Option (BitVec 64)} {sl : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64} {body : Lcmd}
    (hsep : X86Backend.ImageAddrSim.ImgSep frame sl base rsp) {Xg : Nat → Prop}
    (hgate : X86Backend.ImageAddrSimW.ImgGateW frame sl body Xg) {G : Nat}
    (hS : CallerSep frame sl base rsp G) {T : CalleeTab} (hpar : callParamsBT T sl body = true)
    (hcode : calleeCodeBT T sl body = true) {f : String} {c : CalleeData}
    (hc : T.lookup f = some c) (hG : c.frame ≤ G) {k : CalleeKind} (h : k.Top c) :
    k.Ok frame sl base rsp body (siteFn T.lookup sl body) f G := by
  have hsite : ∀ p, CallAt body f p → siteFn T.lookup sl body p = calleeSiteAt c sl body p :=
    fun p ⟨bi, ra, l, hb, hbi⟩ =>
      siteFn_of_callSym (callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩) hc
  have hpa : ∀ p, CallAt body f p → callParamsAtB c sl body p = true :=
    fun p ⟨_, _, _, hb, hbi⟩ => callParamsAtB_of_tab hpar hb hbi hc
  have hF2 : ∀ s sa zf, X86Backend.ImageAddrSim.ImgRel frame sl base body s sa zf →
      CallAt body f sa.reg.lpc →
      List.Forall₂ (ParamAt sl base sa) c.ins (siteFn T.lookup sl body sa.reg.lpc).2 := by
    intro s sa zf hrel hcall
    rw [hsite _ hcall]
    exact callParamsAtB_forall₂W hsep hgate hrel (hpa _ hcall)
  have hnd : ∀ p, CallAt body f p → decodeLprog c.bytes = none →
      (siteFn T.lookup sl body p).2.Nodup := by
    intro p hcall hd
    obtain ⟨bi, ra, l, hb, hbi⟩ := hcall
    rw [hsite p ⟨bi, ra, l, hb, hbi⟩, calleeSiteAt_snd]
    exact calleeCodeBT_nodup hcode hb hbi hc hd
  cases k with
  | word sig res pr room =>
    obtain ⟨l, hlc, hL, rfl, rfl, hF, hw, -, hroom⟩ := h
    obtain ⟨⟨r0, hr0⟩, -, -, -, -⟩ := regCallee_facts hlc hL.result
    exact ⟨hw, hF.mono hG, fun ret sA _ => hroom ret sA, fun p hp => by
      rw [hsite p hp, calleeSiteAt_of_reg hr0 (wordCallee_arrArgs hlc hL)]
      rfl⟩
  | outO l ins po n =>
    obtain ⟨hlc, hL, hins, -, hroom⟩ := h
    obtain ⟨kd, hcr, hdk, -, -, hcframe, hcbytes⟩ := outCallee_facts hlc hL hins
    have hGl : l.frame ≤ G := hcframe ▸ hG
    refine ⟨hL, hGl, fun s sa zf sA hrel hac hcall ret => ?_,
      fun s sa zf sA hrel hac hcall => ?_, fun p hp => ?_⟩
    · have h2 := hF2 s sa zf hrel hcall
      rw [hins] at h2
      exact hroom _ _ _ _ sa sA _ hsep (hS.mono hGl) hac h2
        (fun hd => hnd _ hcall (hcbytes ▸ hd)) ret
    · have h2 := hF2 s sa zf hrel hcall
      rw [hins] at h2
      refine ⟨?_, fun ret vs hvs => readIns_entry hsep hS hrel hac ret h2 hvs⟩
      have hsite' : calleeSiteAt c sl body sa.reg.lpc
          = ((calleeSiteAt c sl body sa.reg.lpc).2.getD kd "",
            (calleeSiteAt c sl body sa.reg.lpc).2) := by
        simp only [calleeSiteAt, hcr]
      rw [hsite _ hcall] at h2 ⊢
      rw [hsite']
      generalize (calleeSiteAt c sl body sa.reg.lpc).2 = ops at h2 ⊢
      rw [hins] at hdk
      obtain ⟨hk, hik⟩ := List.getElem?_eq_some_iff.mp hdk
      have hk2 : kd < ops.length := h2.length_eq ▸ hk
      have hR := List.Forall₂.get h2 hk hk2
      rw [List.getD_eq_getElem _ _ hk2]
      simp only [List.get_eq_getElem, hik] at hR
      exact hR.2.2
    · rw [hsite p hp]
      exact calleeSite_destAt hcr (hpa p hp) hdk
  | ins l ins res =>
    obtain ⟨hlc, hL, rfl, rfl, -, hnd', hfb⟩ := h
    obtain ⟨⟨r0, hr0⟩, -, hcframe, -, -⟩ := regCallee_facts hlc hL.result
    exact ⟨hL, hnd', hfb, hcframe ▸ hG, fun s sa zf _ hrel _ hcall => hF2 s sa zf hrel hcall,
      fun p hp => by rw [hsite p hp]; simp [calleeSiteAt, hr0, CalleeData.resReg]⟩
  | outC l ins po n =>
    obtain ⟨hlc, hL, hins, -, hnd', hfb⟩ := h
    obtain ⟨kd, hcr, hdk, -, -, hcframe, -⟩ := outCallee_facts hlc hL hins
    obtain ⟨hk, hik⟩ := List.getElem?_eq_some_iff.mp hdk
    refine ⟨hL, hnd', hfb, hcframe ▸ hG, fun p hp => ?_, fun p hp => ?_,
      fun s sa zf _ hrel _ hcall => hins ▸ hF2 s sa zf hrel hcall, ?_⟩
    · rw [hsite p hp]
      exact calleeSite_destAt hcr (hpa p hp) hdk
    · rw [hsite p hp, ← hins]
      have hsite' : calleeSiteAt c sl body p
          = ((calleeSiteAt c sl body p).2.getD kd "", (calleeSiteAt c sl body p).2) := by
        simp only [calleeSiteAt, hcr]
      have hk2 : kd < (calleeSiteAt c sl body p).2.length := by
        rw [calleeSiteAt_snd, CalleeData.siteArgs_length]
        exact hk
      rw [List.mem_iff_getElem]
      refine ⟨kd, by simp [hk, hk2], ?_⟩
      simp only [List.getElem_zip, hik]
      conv_rhs => rw [hsite']
      rw [List.getD_eq_getElem _ _ hk2]
    · rintro p hp r1 n1 hr1 q x hqx hs hpr q' x' hqx' hq'r
      rw [hL.result] at hr1
      cases hr1
      rw [hsite p hp, calleeSiteAt_snd, ← hins] at hqx hqx'
      have hod := (outDestB_iff hcr hdk).1 (callParamsAtB_spec (hpa p hp)).2
      exact hod q x hqx hs (fun he => hpr (by rw [he])) q' x' hqx'
        (X86Backend.DecodePrinted.phys_inj (hL.ins_gp q' (hins ▸ (List.of_mem_zip hqx').1))
          hL.po_gp hq'r)

/-- A nonempty table whose functions are a sublist of `[c]` is the table of `c`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.CalleeTab.eq_one_of_sublist
    {T : CalleeTab} {c : CalleeData} (h : T.fns.Sublist [c]) (hne : T.fns ≠ []) :
    T = CalleeTab.one c := by
  obtain ⟨fns⟩ := T
  have h1 : fns = [c] := h.eq_of_length_le (by
    cases fns with
    | nil => exact absurd rfl hne
    | cons _ _ => simp)
  rw [h1]
  rfl

/-- **Correctness of a calling body with a table of linked kernels.** For a result
    `(P, bytes)` of `compileRegion σ a p linked` on a program `p` with a `call`, the back half
    finds a nonempty table `T` of linked functions, a sublist of `linked` with distinct symbols,
    every `call` of `p` names a symbol of `T`, and the block the code of each function of `T`
    decodes to has no `call`. Let each function `c` of `T` have a kind
    `kind c.name` whose top hypotheses it meets (`CalleeKind.Top`) and whose specification the
    run relation `X c.name` meets, and let the procedure table `PT` agree with the call
    environment `Ec`, give the symbol of each function of `T` the summary of its kind, and hold
    summaries on words with word results at every other symbol. From every entry state `sa`
    satisfying `σ.Regions`, at every valuation `V` that `σ` reads off `sa` at which `p` denotes
    `v` in `Ec` at some fuel, there is a caller program `pc`, the program `calleeProg T b` of a
    printed body `b` of the class `ImageAddrCallW.printedAddrCWB` whose bytes at `T` are
    `bytes`, such that:

    * `pc` halts from `sa` at index `0`, its calls answered by the oracle `Callee.oracleOf` of
      the symbols of `T`, at the index `pc.length + T.entryIdx (T.symPos f)` of the entry of
      the function of each symbol `f`, by the run relation `X f` guarded by the precondition of
      the interface of its kind, in a state from which `σ` reads back the source value of the
      result;
    * when the code of each function `c` of `T` decodes to the block `q c` without `call`, the
      code of each function but the last is an item stream
      (`LprogBytesLinkReloc.KernelItems`) and `X c.name` is the leaky run of `q c` under
      `ctRegime`, the bytes decode to `pc` followed by the region `regionProg` of the blocks
      `q c` with its targets raised by `pc.length`, and this program halts through the calls
      (`HaltsC`) from `sa` at index `0` in a state from which `σ` reads back the same value.

    The reference run is `RegionLinkCompose.regionCo_bytes_tab`, the image run
    `RegionLinkCompose.calleeBody_imgRun_tab`, the run under the oracle
    `ImageAddrCallMeets.haltsO_of_contracts` and the run through the calls
    `ImageAddrCallMeets.haltsC_of_contracts`, with the hypotheses of the calls of each symbol
    from `CalleeKind.Top.ok` and the region of the code of `T` from `CalleeTab.regionBlocks`.
    The correctness theorems at one linked function are its instances at `linked = [c]`. -/
theorem compileRegion_correct_linked_multi {σ : AbiLayout} {a : AbiNames}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {linked : List CalleeData} {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion σ a p linked = some (P, bytes)) (hcf : p.callFree = false) :
    ∃ T : CalleeTab, T.fns.Sublist linked ∧ T.fns ≠ [] ∧ T.names.Nodup
      ∧ callsToAny T.names p = true
      ∧ (∀ c ∈ T.fns, ∀ q, decodeLprog c.bytes = some q → ∀ tg, RInstr.call tg ∉ q)
      ∧ ∀ (kind : String → CalleeKind) (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name)) →
        ∀ {Ec : CallEnv jasminDialect} {PT : ProcTable}, ProcsAgree Ec PT →
        (∀ f pr, f ∉ T.names → PT f = some pr → pr.WordOnly ∧ pr.RetWord) →
        (∀ c ∈ T.fns, PT c.name = some (kind c.name).summary) →
        ∀ (sa : AState) (V : Ctxt.Valuation Γ), AbiValOf σ sa V → σ.Regions sa →
        ∀ (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]},
        p.denoteAt Ec fuel V = some v →
        ∃ pc : List RInstr,
          (∃ b, calleeBytes (some T) b = some bytes
            ∧ X86Backend.ImageAddrCallW.printedAddrCWB T.frame b = true
            ∧ calleeProg T b = some pc)
          ∧ (∃ sa', X86Backend.Callee.HaltsO aMachine
              (X86Backend.Callee.oracleOf T.names
                (fun f => pc.length + T.entryIdx (T.symPos f))
                (fun f => guarded (kind f).sig (X f)))
              pc 0 sa sa'
            ∧ σ.ResultOf sa sa' (denVal t
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
          ∧ ∀ q : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (q c)) →
            (∀ c ∈ T.fns, ∀ tg, RInstr.call tg ∉ q c) →
            (∀ c ∈ T.fns.dropLast, X86Backend.LprogBytesLinkReloc.KernelItems c.bytes) →
            (∀ c ∈ T.fns, X c.name = X86Backend.Callee.runOf ctRegime (q c)) →
            decodeLprog bytes = some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length
              (X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries q)))
            ∧ ∃ sa', HaltsC aMachine (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length
                (X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries q))) 0 sa sa'
              ∧ σ.ResultOf sa sa' (denVal t
                (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)) := by
  obtain ⟨T, r0, hr0, hcT, hst, hB, r, b, cert, hwb, hbs, hg, -, -⟩ := compileRegion_spec_tab h hcf
  have hnd : T.names.Nodup := by
    have hg' := hg
    simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
    obtain ⟨⟨⟨⟨⟨⟨hnd0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg'
    exact of_decide_eq_true hnd0
  refine ⟨T, regionCallee_sublist hcT, regionCallee_fns_ne_nil hcT, hnd,
    callsToAny_of_regionCallee hr0 hcT, (regionCoB_callee hg).2, ?_⟩
  intro kind X hK Ec PT hT hwo hTc sa V hV hreg fuel v hv
  obtain ⟨w, m, rfl⟩ := hst
  generalize hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res
    cert (some T) = d
  -- The summaries of the procedure table at the symbols of the table and elsewhere.
  have hTf : ∀ f c, T.lookup f = some c → PT f = some (kind f).summary := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    exact hTc c hcm
  have hnames : ∀ f, T.lookup f = none → f ∉ T.names := by
    intro f hf hmem
    have h1 := congrFun T.lookup_isSome f
    simp only [hf, Option.isSome_none] at h1
    have h2 : T.names.contains f = true := by simpa using hmem
    rw [← h1] at h2
    cases h2
  have haa : LprogIsa.Isa.procArrArgs PT = calleeAAT (some T) := by
    funext f
    cases hl : T.lookup f with
    | some c =>
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hl
      have hF := (hK c hcm).1.facts
      simp [LprogIsa.Isa.procArrArgs, calleeAAT, hl, hTc c hcm, hF.2.1]
    | none =>
      cases hPf : PT f with
      | none => simp [LprogIsa.Isa.procArrArgs, calleeAAT, hl, hPf]
      | some pr =>
        have hw : pr.arrArgs = fun _ => none := (hwo f pr (hnames f hl) hPf).1
        simp [LprogIsa.Isa.procArrArgs, calleeAAT, hl, hPf, hw]
  have hao : LprogIsa.Isa.procOut PT = calleeAOT (some T) := by
    funext f
    cases hl : T.lookup f with
    | some c =>
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hl
      have hF := (hK c hcm).1.facts
      simp only [LprogIsa.Isa.procOut, calleeAOT, hl, hTc c hcm, hF.2.2.1, Option.bind_some]
      cases c.res <;> rfl
    | none =>
      cases hPf : PT f with
      | none => simp [LprogIsa.Isa.procOut, calleeAOT, hl, hPf]
      | some pr =>
        have hw : pr.out = none := (hwo f pr (hnames f hl) hPf).2
        simp [LprogIsa.Isa.procOut, calleeAOT, hl, hPf, hw]
  have hkd : ∀ f pr, PT f = some pr → pr.Kinded := by
    intro f pr hf
    cases hl : T.lookup f with
    | some c =>
      rw [hTf f c hl] at hf
      cases hf
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hl
      exact (hK c hcm).1.facts.2.2.2.1
    | none => exact LprogIsa.ProcSummary.kinded_of_retWord (hwo f pr (hnames f hl) hf).2
  obtain ⟨k, u, hu, hcb, hsep, hrelF, hacorr, hpc0, hbnd, hread⟩ :=
    RegionLinkCompose.regionCo_bytes_tab (regionExportableB_sound hB) hr0 ⟨w, m, rfl⟩ hwb hg hd
      hT hkd haa hao (fun f c hc => by rw [hTf f c hc]; rfl) sa V hV hreg fuel
      ((legalizeRegion_denoteAt Ec fuel p V).trans hv)
  -- The conjuncts of the gate.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg'
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  rw [hcells] at himg
  simp only [renImageB, X86Backend.ImageAddrRouteW.slotArrC_nil, calleeImgBT,
    Bool.and_eq_true] at himg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hphys⟩, hcls, hgate⟩, -⟩, hent⟩, -⟩, -⟩ := himg
  have hcellsE : d.cells = regionCells σ exportReg d.ps b (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hcb0 : cellBody (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b = b :=
    cellBody_of_cellArrsOf_nil _ (cellArrsOf_nil_of_regionCells_nil (hcellsE ▸ hcells))
  rw [hcb0] at hphys hrelF
  -- The checks of the calling body.
  have hok := calleeBodyBT_spec.mp hcb
  have hsites := hok.callSites
  have hdead := hok.dead
  have hflags := hok.flags
  have hcond := hok.condLive
  have hseg := hok.deadSeg
  have hlive := hok.live0
  have hroomB := hok.stackRoom
  have hnn := hok.frameNonneg
  have hcode := hok.code
  simp only [calleeDeadBT, Bool.and_eq_true] at hdead
  obtain ⟨hdo, hparB⟩ := hdead
  have hl : b.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true := by
    have h1 := hcls
    simp only [X86Backend.ImageAddrCallW.printedAddrCWB, Bool.and_eq_true] at h1
    exact h1.1.1.1.2
  have hcall : ∀ {q : Nat} {bi : Linstr} {ra : Option String} {f : String} {l : LLabel},
      b[q]? = some bi → bi.li_i = .Lcall ra (f, l) → ∃ c, T.lookup f = some c :=
    fun hb hbi => lookup_of_call hok.decode hl hb hbi
  -- The dead names at the interfaces and the result kinds of the kinds.
  have hdead' : X86Backend.ImageAddrCall.callDeadSymB (fun f => (kind f).sig)
      (fun f => (kind f).isOut) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b) d.outs).dead b
      = true := by
    refine (callDeadSymB_congr_exempt fun q bi ra f l hb hbi => ?_).trans hdo
    obtain ⟨c, hc⟩ := hcall hb hbi
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨-, -, -, -, hout, hclob, hres, -⟩ := (hK c hcm).1.facts
    refine ⟨?_, ?_, rfl⟩
    · simp only [CalleeTab.sigOf, hc]
      unfold X86Backend.ImageAddrCall.exemptC
      rw [hclob, hres]
    · simp only [CalleeTab.outOf, hc, Option.any_some, hout]
      cases c.res <;> rfl
  -- The summaries at the call sites of the image.
  have hsit : X86Backend.ImageAddrCall.SitesOf PT
      (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b)
      (fun q => (kind ((callSymAt b q).getD "")).summary)
      (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) :=
    X86Backend.ImageAddrCall.sitesOf_callImg _ hsites fun q bi ra f l hb hbi => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      simp only [callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩, Option.getD_some]
      exact hTf f c hc
  have hpr : ∀ q f, X86Backend.ImageAddrCallMeets.CallAt b f q →
      (kind ((callSymAt b q).getD "")).summary = (kind f).summary := by
    rintro q f ⟨bi, ra, l, hb, hbi⟩
    simp only [callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩, Option.getD_some]
  -- The image run at the table.
  obtain ⟨fuel', t', himgrun, hobs⟩ := RegionLinkCompose.calleeBody_imgRun_tab hcb
    (fun f c hc => by
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
      obtain ⟨har, -, -, -, -, -, -, hrw⟩ := (hK c hcm).1.facts
      exact ⟨_, hTc c hcm, har, hrw.imp id fun hall q _ => hall _ _ q⟩)
    ⟨⟨X86Backend.ImageAddrRoute.entryV σ (X86Backend.ImageAddrRoute.frameE b sa) sa
      (X86Backend.ImageAddrRoute.unren d.ps), a.fname⟩, false⟩
    u rfl rfl hbnd k hu
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
      (X86Backend.DecodePrintedCFG.frameRsp b sa) T.frame := by
    refine ⟨hS0.frames, fun q A' n j hq hj x hx => ?_⟩
    obtain ⟨A, hA, rfl⟩ := X86Backend.ImageAddrRoute.slotRen_some hq
    have hb : X86Backend.ImageAddrRouteW.baseR σ sa d.ps (renOf d.ps A)
        = abiBase (abiReg σ) sa A := by
      simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hA]
    rw [hb] at hx
    exact hS0.cells q A n j hA hj x hx
  -- The hypotheses of the calls of each symbol at its kind.
  have hgateW :=
    (imgGateCBW_frameMark b (X86Backend.DecodePrintedCFG.frameRsp b sa) _).trans hgate
  have hgateI := X86Backend.ImageAddrCallW.imgGateW_of_imgGateCBW hgateW
  have hOk : ∀ f, X86Backend.ImageAddrCall.CalledIn b f →
      (kind f).Ok (X86Backend.ImageAddrRoute.frameE b sa)
        (slotRen (slotArrOf σ exportReg) (renOf d.ps)) (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
        (X86Backend.DecodePrintedCFG.frameRsp b sa) b
        (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) f T.frame := by
    rintro f ⟨q, bi, ra, l, hb, hbi⟩
    obtain ⟨c, hc⟩ := hcall hb hbi
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    exact (hK c hcm).1.ok hsep hgateI hS hparB hcode hc (CalleeTab.frame_le hcm)
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
        (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b) b) d.outs).dead
        t1.prog.base.reg.lpc) t1 t2 →
      Fin t2 sA → Fin t1 sA := by
    intro t1 t2 sA hag hF2 q A n hq
    obtain ⟨arr, h1, h2⟩ := hF2 q A n hq
    exact ⟨arr, by rw [X86Backend.ImageAddrSim.getArr_congr hag.arr]; exact h1, h2⟩
  have hbne : b ≠ [] := by
    intro hb
    simp [X86Backend.ImageAddrCallW.printedAddrCWB, hb] at hcls
  have hlen : (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc < b.length := by
    rw [hpc0]
    exact List.length_pos_iff.mpr hbne
  -- The bytes of the calling body.
  obtain ⟨hbytes, hne, ds, prog, hss, hbr, hP, hprog, hp0⟩ := calleeBytes_tab hbs
  have hLv : X86Backend.ImageAddrCallW.liveW
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
        (renOf d.ps)) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
        b) d.outs) (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b
      (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc = false := by
    rw [hpc0]
    exact X86Backend.ImageAddrCallW.liveW_zero (by simpa using hlive)
      (X86Backend.ImageAddrCallW.callFacts_of_printedAddrCWB hcls hss).carry
  have hbits : X86Backend.ImageAddrCallW.bitsDeadB (X86Backend.ImageAddrRoute.frameE b sa)
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
        (renOf d.ps)) (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
        b) d.outs) b = true :=
    (bitsDeadB_frameMark b _ _).trans hok.bitsDead
  have hlenP := X86Backend.LprogBytesLinkReloc.expectedRelocMap_length _ _ _ _ hP
  -- The run under the oracle of the guarded callees.
  obtain ⟨sO, hhaltO, hfinalO⟩ := X86Backend.ImageAddrCallMeets.haltsO_of_contracts hsep hphys
    hgateW hsites (kind := kind) (X := fun f => guarded (kind f).sig (X f))
    (fun f ⟨_, bi, ra, l, hb, hbi⟩ => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
      exact X86Backend.ImageAddrCallMeets.CalleeKind.spec_guard (hK c hcm).2)
    hS hOk hcls hss (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq) (calleeSym T b) _
    (fun f => prog.length + T.entryIdx (T.symPos f))
    (fun it f j t _ hs ht => by
      simp only [X86Backend.LprogBytesLinkReloc.symTgt, hs, Option.bind_some,
        CalleeTab.linkMap, Option.some.injEq, Prod.mk.injEq] at ht
      rw [← ht.1, hlenP])
    hP
    (O := X86Backend.Callee.oracleOf T.names (fun f => prog.length + T.entryIdx (T.symPos f))
      (fun f => guarded (kind f).sig (X f)))
    (fun f ⟨_, bi, ra, l, hb, hbi⟩ s tr s' hx => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
      exact ⟨c.name, List.mem_map_of_mem hcm, rfl, tr, hx⟩)
    hbits hdead' hflags hcond hsit hpr X86Backend.CheckedIsaCall.x86IsaK_checked
    (X86Backend.CheckedIsaCall.deadSteps_x86K hseg) hfin hFin fuel' himgrun rfl hlen hLv
    (hrelF _) hacorr
  rw [hpc0] at hhaltO
  have hpos : X86Backend.DecodePrintedCFG.posOf ds 0 = 0 + 1 := by
    simp [X86Backend.DecodePrintedCFG.posOf]
  rw [hpos] at hhaltO
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
  refine ⟨prog, ⟨b, hbs, hcls, hprog⟩, ⟨sO, .go ?_ hhaltO, hR sO hfinalO⟩,
    fun q hdecq hnoc hit hXq => ?_⟩
  · simp only [X86Backend.RInstrSemantics.step, hp0]
    rfl
  -- The run through the calls, at the region of the blocks of the table.
  have hfsR := remoteSym_mem_names hcls hok.decode
  have hRB := T.regionBlocks (regionCallee_fns_ne_nil hcT) q hdecq hne hnoc hit T.names
    (fun _ hf => hf)
  have hag := symTgt_linkMap_regionTgt T (calleeSym T b)
    (X86Backend.LprogBytesDecode.Params.ofBody b) b ds hfsR
  have hbr' := hbr
  rw [X86Backend.LprogBytesLinkReloc.branchOKRelocMap_congr _ _ (hag _ _)] at hbr'
  have hP' := hP
  rw [X86Backend.LprogBytesLinkReloc.expectedRelocMap_congr _ _ (hag _ _)] at hP'
  have hfsB : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => decide (g ∈ T.names)) b = true := by
    have h1 := bodyCallSymsB_of_decodeSites hok.decode
    rw [CalleeTab.lookup_isSome] at h1
    simpa using h1
  obtain ⟨hdec, sA', hhalt, hfinal⟩ := X86Backend.ImageAddrCallMeets.haltsC_of_contracts hsep
    hphys hgateW hsites ctRegime hRB (kind := kind)
    (fun f ⟨_, bi, ra, l, hb, hbi⟩ => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
      rw [CalleeTab.regionCode_lookup T q hc, ← hXq c hcm]
      exact (hK c hcm).2)
    hfsB hS hOk hcls hss (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq) (calleeSym T b)
    hbr' hP' hbits hdead' hflags hcond hsit hpr X86Backend.CheckedIsaCall.x86IsaK_checked
    (X86Backend.CheckedIsaCall.deadSteps_x86K hseg) hfin hFin fuel' himgrun rfl hlen hLv
    (hrelF _) hacorr
  rw [hpc0, hpos] at hhalt
  refine ⟨hbytes ▸ hdec, sA', .go ?_ hhalt, hR sA' hfinal⟩
  simp only [X86Backend.RInstrSemantics.step, List.getElem?_append_left hlen0, hp0]
  rfl

end Table

/-! ## 7. Correctness of a calling body with one linked word kernel -/

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

    It is `compileRegion_correct_linked_multi` at the table of `c` and the word kind
    `.word (wordSig l c.args c.resReg) c.resReg pr room`, whose region is the block `qk`. -/
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
  obtain ⟨T, hsub, hne, -, -, -, hrest⟩ := compileRegion_correct_linked_multi h hcf
  obtain rfl := CalleeTab.eq_one_of_sublist hsub hne
  have hmem : ∀ c' ∈ (CalleeTab.one c).fns, c' = c := fun c' hc' => List.mem_singleton.mp hc'
  obtain ⟨pc, -, ⟨sO, hO, hRO⟩, hC⟩ :=
    hrest (fun _ => .word (wordSig l c.args c.resReg) c.resReg pr room)
      (fun _ => X86Backend.Callee.runOf ctRegime qk)
      (fun c' hc' => by
        obtain rfl := hmem c' hc'
        exact ⟨⟨l, hc, hL, rfl, rfl, hF, hw, hpar, hroom⟩, hX⟩)
      hT (fun f pr' _ hf => ⟨hwo f pr' hf, hrw f pr' hf⟩)
      (fun c' hc' => by obtain rfl := hmem c' hc'; exact hTc) sa V hV hreg fuel hv
  obtain ⟨hdec, sC, hhC, hRC⟩ := hC (fun _ => qk)
    (fun c' hc' => by obtain rfl := hmem c' hc'; exact hqk)
    (fun c' hc' => by obtain rfl := hmem c' hc'; exact hnc) (by simp [CalleeTab.one])
    (fun _ _ => rfl)
  have hQ : X86Backend.LprogBytesLinkReloc.regionProg
      ((CalleeTab.one c).regionEntries fun _ => qk) = qk := by
    simp [CalleeTab.regionEntries, CalleeTab.one, X86Backend.LprogBytesLinkReloc.regionProg,
      X86Backend.LprogBytesLink.shiftProg]
  rw [hQ] at hdec hhC
  refine ⟨pc, hdec, ⟨sC, hhC, hRC⟩, sO, hO.mono fun t s s' ho => ?_, hRO⟩
  obtain ⟨f, -, ht, tr, hx⟩ := ho
  simp only [CalleeTab.symPos_one, CalleeTab.entryIdx_zero, Nat.add_zero] at ht
  exact ⟨ht.symm, tr, hx⟩

/-! ## 8. Correctness of a calling body with one linked out kernel -/

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

    The run under the oracle is `compileRegion_correct_linked_multi` at the table of `c` and
    the out kind `.outO l ins po n`; the items are `calleeBytes_items` and the decoded bytes
    `calleeBytes_decode_one` at the printed body it gives. -/
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
  obtain ⟨T, hsub, hne, -, -, -, hrest⟩ := compileRegion_correct_linked_multi h hcf
  obtain rfl := CalleeTab.eq_one_of_sublist hsub hne
  have hmem : ∀ c' ∈ (CalleeTab.one c).fns, c' = c := fun c' hc' => List.mem_singleton.mp hc'
  obtain ⟨pc, ⟨b, hbs, hpr, hprog⟩, ⟨sO, hO, hRO⟩, -⟩ :=
    hrest (fun _ => .outO l ins po n) (fun _ => X)
      (fun c' hc' => by
        obtain rfl := hmem c' hc'
        exact ⟨⟨hc, hL, hins, hpar, hroom⟩, hX⟩)
      hT (fun f pr' hf hp => by
        have hf' : f ≠ c.name := by simpa using hf
        exact ⟨hwo f pr' hf' hp, hrw f pr' hf' hp⟩)
      (fun c' hc' => by obtain rfl := hmem c' hc'; exact hTc) sa V hV hreg fuel hv
  rw [CalleeTab.frame_one] at hpr
  have hcbytes : c.bytes = l.bytes := (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc).2.2.2.2.2.1
  obtain ⟨items, hbi, hok, hres⟩ := calleeBytes_items hbs hpr hprog
  refine ⟨pc, items, by rw [← hcbytes]; exact hbi, hok, hres, fun q hq => ?_, sO,
    hO.mono fun t s s' ho => ?_, hRO⟩
  · obtain ⟨pr', hpr', hdec⟩ := calleeBytes_decode_one hbs hpr (hcbytes ▸ hq)
    rw [hprog] at hpr'
    cases hpr'
    exact hdec
  · obtain ⟨f, -, ht, tr, hx⟩ := ho
    simp only [CalleeTab.symPos_one, CalleeTab.entryIdx_zero, Nat.add_zero] at ht
    exact ⟨ht.symm, tr, hx⟩

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
    (hnc c (by simp [CalleeTab.one]) qk (by rw [hcb]; exact hqk))
    (hO.mono fun _ _ _ ho => ⟨ho.1, ho.2.imp fun _ hx => hx.2⟩), hR⟩

/-! ## 9. The hax compiler on a module with linked word kernels -/

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
        | some T =>
            have hc1 := regionCallee_self hc
            split at h
            · rename_i P0 cert hP
              obtain ⟨b, -, hg⟩ := regionEncode_spec_callee h
              rw [Bool.and_eq_true] at hg
              obtain ⟨c, rfl⟩ := calleeCtB_some hg.2
              refine ⟨c, regionCallee_mem hc c (by simp [CalleeTab.one]), ?_⟩
              have hc1' : regionCallee [c] (legalizeRegion p) r'.code
                  = some (some (CalleeTab.one c)) := hc1
              unfold compileRegion
              rw [ite_eq_left hB]
              simp only [hr, hc1', hP]
              exact h
            · cases h
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

/-! ## 10. The source run at the table of the callee alone -/

/-- The environment of the linked functions of `m` restricted to the name `f`: `linkedEnvOn` at
    `[f]`. -/
abbrev linkedEnvAt (m : HaxModule) (f : String) : CallEnv jasminDialect :=
  linkedEnvOn m [f]

/-- The table with the summary of `l` alone: `summaryTableL` at `[l]`. -/
abbrev summaryTable (l : LinkedFn) : LprogIsa.ProcTable := summaryTableL [l]

/-- Every `call` of the program names `f`: `callsToAny` at `[f]`. -/
abbrev callsTo (f : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : Bool :=
  callsToAny [f] p

/-- **The region legalisation keeps the value of `callsTo f`.** -/
theorem callsTo_legalizeRegion (f : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : callsTo f (legalizeRegion p) = callsTo f p :=
  callsToAny_legalizeRegion [f] p

/-- **The table of the callee alone agrees with the environment of the callee alone**:
    `procsAgree_summaryTableL` at the one linked function `l`. -/
theorem procsAgree_summaryTable {m : HaxModule} (hnd : (m.linked.map (·.name)).Nodup)
    {l : LinkedFn} (hl : l ∈ m.linked)
    (hargs : ∀ vals v, l.sem vals = some v → vals.map valKind = linkedKinds l)
    (hres : ∀ t, l.res ≠ .slice t) :
    ProcsAgree (linkedEnvAt m l.name) (summaryTable l) :=
  procsAgree_summaryTableL (ls := [l]) hnd
    (fun l' hl' => by rw [List.mem_singleton.mp hl']; exact hl)
    (fun l' hl' => by rw [List.mem_singleton.mp hl']; exact hargs)
    (fun l' hl' => by rw [List.mem_singleton.mp hl']; exact hres)

/-- **The calls of an exported program are among its shadow instructions**: when every
    shadow instruction of the export of `p` names `f`, every `call` of `p` names `f`
    (`callsToAny_of_exportR`). -/
theorem callsTo_of_exportR {nArgs : Nat} {fn f : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {d n : Nat} {I : LprogIsa.IsaData}
    {r : Exported} (h : exportR nArgs fn p d n I = some r)
    (hsh : ∀ i ∈ r.code, ∀ v, LprogIsa.shadowCall? i.fst = some v → v.2.1 = f) :
    callsTo f p = true :=
  callsToAny_of_exportR h fun i hi v hv => List.mem_singleton.mpr (hsh i hi v hv)

/-- **Every call of a program the back half compiles at one callee names the callee**:
    `callsToAny_of_regionCallee` at the table of the callee (`regionCallee_singleton`). -/
theorem callsTo_of_compileRegion {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {c : CalleeData}
    {r : Lprog × List (BitVec 8)}
    (h : compileRegion σ a p [c] = some r) (hcf : p.callFree = false) :
    callsTo c.name p = true := by
  obtain ⟨P, bytes⟩ := r
  obtain ⟨T, r0, hr0, hc, -⟩ := compileRegion_spec_tab h hcf
  have h1 := callsToAny_of_regionCallee hr0 hc
  rw [regionCallee_singleton hc, CalleeTab.names_one] at h1
  exact h1

/-- **A program whose calls name `f` denotes the same at the environment restricted to
    `f`** (`denoteAt_linkedEnvOn`). -/
theorem denoteAt_linkedEnvAt {m : HaxModule} {f : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (hp : callsTo f p = true)
    (k : Nat) (V : Ctxt.Valuation Γ) :
    p.denoteAt (linkedEnvAt m f) k V = p.denoteAt (linkedEnv m) k V :=
  denoteAt_linkedEnvOn hp k V

end Linked

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
