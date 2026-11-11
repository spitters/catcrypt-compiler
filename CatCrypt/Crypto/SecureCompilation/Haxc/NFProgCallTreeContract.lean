/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose

/-!
# The event relation of the back half against the separation contracts

The back half relates a call event of the program of `jasminDialect` to a linked call event of
the target by `NFProgCallTreeRefBack.BackRE T`: the linked call names the symbol of the event,
and the argument words of the event are the registers of the arguments of the callee of the
table at the entry state. The statement `R3StatementF` relates the source events to the target
events by `contractRE`: the linked call of the target event is the source call, at the values the
layout of the linked function reads at the entry state (`linkRead`), and the entry state
satisfies the precondition `LinkedFn.pre`.

For a linked kernel whose parameters are scalars, both follow at the entry state of every call,
the precondition where the meaning is defined at the arguments: the resources of the call
(`LinkedFn.entryAt`) hold at the entry state after the stack operations of the call whatever the
caller (`entryAt_entryOf_scalar`), and the kernel gives its precondition under these resources at
a defined meaning (`LinkedKernel.callSite`). At a call where the meaning is undefined the source
handler answers `none` and the precondition is not available; the relation `contractREG` guards
the precondition by the definedness of the meaning, and is implied by `contractRE`.

## Main definitions

* `contractREG`: the event relation `contractRE` with the precondition guarded by the definedness
  of the meaning at the arguments.

## Main results

* `entryAt_entryOf_scalar`: the resources of a call of a linked function with scalar parameters
  hold at the entry state of every call.
* `pre_entryOf_scalar`: the precondition of a linked kernel with scalar parameters at the entry
  state of every call at whose arguments the meaning is defined.
* `linkRead_of_backRE`: at a target event related to a call event by `BackRE T`, the values the
  layout reads at the entry state are the argument words of the event.
* `contractREG_of_backRE`: a source call at the argument words of a call event related by
  `BackRE T` to a target call event is related to it by `contractREG`.
* `contractREG_of_contractRE`: `contractRE` implies `contractREG`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (LstateN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (LstateA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (wordsOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (entryAt_at_call callVarOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (CallerSep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain (InsLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee (ParamAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn wordVal)
open _root_.Hax

/-! ## The precondition at the entry of a call -/

/-- The image state that reads every general-purpose name at the register of its machine name and
    has the memory of `sA`. -/
def imgOfState (sA : AState) : LstateA :=
  { reg := { lvm := fun r => ⟨64, sA.regs (phys r)⟩ }, mem := sA.mem }

/-- The image state of `sA` corresponds to `sA` at its stack register. -/
theorem aCorr_imgOfState (sA : AState) : ACorr (sA.regs "%rsp") sA (imgOfState sA) where
  regs r _ := by simp [imgOfState, LstateN.getW]
  sp := rfl
  mem _ _ := rfl

/-- The empty frame and slot maps are separated. -/
theorem imgSep_empty (base : String → BitVec 64) (rsp : BitVec 64) :
    ImgSep (fun _ => none) (fun _ => none) base rsp where
  frames _ _ _ _ h := nomatch h
  cellFrame _ _ _ _ h := nomatch h
  cells _ _ _ _ _ _ _ _ h := nomatch h
  len _ _ _ _ _ h := nomatch h
  red _ _ _ _ h := nomatch h
  gp _ _ := rfl
  slotFrame _ _ _ h := nomatch h
  faBase _ _ _ _ h := nomatch h

/-- A caller without frame and slots is separated at every frame bound. -/
theorem callerSep_empty (base : String → BitVec 64) (rsp : BitVec 64) (G : Nat) :
    CallerSep (fun _ => none) (fun _ => none) base rsp G where
  frames _ _ h := nomatch h
  cells _ _ _ _ h := nomatch h

/-- **The resources of a call of a linked function with scalar parameters.** For a layout of
    scalar parameters in distinct registers of general-purpose names, with a register result and
    a frame that fits below `2 ^ 64`, the resources `LinkedFn.entryAt` of the call hold at the
    entry state after the stack operations of every call, at the logical variables of the call
    (`callVarOf`). -/
theorem entryAt_entryOf_scalar {l : LinkedFn} {ins : List (String × ArgKind)} {res : String}
    (hL : InsLayout l ins res) (hsc : ∀ p ∈ ins, p.2 = .scalar)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64) (ret : Nat)
    (sA : AState) : (l.entryAt (callVarOf l ret sA)).holds (entryOf ret sA) := by
  refine entryAt_at_call (imgSep_empty (fun _ => 0) (sA.regs "%rsp")) hL.args hnd hfb
    (callerSep_empty (fun _ => 0) (sA.regs "%rsp") l.frame) (aCorr_imgOfState sA)
    (args := ins.map Prod.fst) ?_ ?_ ret
  · rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun p hp => ⟨hL.ins_gp p hp, ?_⟩
    rw [hsc p hp]
  · intro r n hr
    rw [hL.result] at hr
    cases hr

/-- **The precondition of a linked kernel with scalar parameters at the entry of a call.** At
    the entry state after the stack operations of every call, if the meaning is defined at the
    values the layout reads there, the precondition of the kernel holds. -/
theorem pre_entryOf_scalar {l : LinkedFn} (K : LinkedKernel l) {ins : List (String × ArgKind)}
    {res : String} (hL : InsLayout l ins res) (hsc : ∀ p ∈ ins, p.2 = .scalar) (ret : Nat)
    (sA : AState) (hd : (l.sem (l.layout.args.map (·.read (entryOf ret sA)))).isSome = true) :
    l.pre (entryOf ret sA) :=
  K.callSite (callVarOf l ret sA) (entryOf ret sA)
    (entryAt_entryOf_scalar hL hsc K.args_nodup K.frame_fit ret sA) hd

/-! ## The values the layout reads at the entry -/

/-- The value a scalar parameter reads is the word of its register. -/
theorem read_scalar {a : AbiArg} (h : a.kind = .scalar) (s : AState) :
    a.read s = wordVal (s.regs a.reg) := by
  simp only [AbiArg.read, h]
  rfl

/-- **The values of the layout at a target event related by `BackRE`.** Let the callee `c` of the
    symbol of a call event `ev` in the table `T` be the data of the linked function `l` of `m`
    found at that symbol, with the layout `InsLayout l c.ins res` of scalar parameters. At a
    target event related to `ev` by `BackRE T`, the values the layout of `l` reads at the entry
    state are the argument words of `ev`. -/
theorem linkRead_of_backRE {m : HaxModule} {T : CalleeTab} {ev : NFCall JasminDialect.jasminDialect}
    {e₂ : (kSig AState).Event} {l : LinkedFn} {c : CalleeData} {res : String}
    (hl : m.linked.find? (·.name == ev.name) = some l) (hc : T.lookup ev.name = some c)
    (hL : InsLayout l c.ins res) (hsc : ∀ p ∈ c.ins, p.2 = .scalar) (h : BackRE T ev e₂) :
    linkRead m ev.name e₂.entry = (wordsOf ev.args).map wordVal := by
  obtain ⟨-, c', hc', hw⟩ := h
  rw [hc] at hc'
  obtain rfl := Option.some.inj hc'
  have hregs : l.layout.args.map (·.reg) = c.args.map phys := by
    have h1 := congrArg (List.map Prod.fst) hL.args
    simp only [List.map_map] at h1
    rw [← CalleeData.ins_map_fst c, List.map_map]
    exact h1
  have hk : ∀ a ∈ l.layout.args, a.kind = .scalar := by
    intro a ha
    have h1 : (a.reg, a.kind) ∈ c.ins.map fun p => (phys p.1, p.2) := by
      rw [← hL.args]
      exact List.mem_map_of_mem ha
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h1
    rw [← (Prod.mk.inj hpe).2]
    exact hsc p hp
  simp only [linkRead, hl]
  rw [List.map_congr_left fun a ha => read_scalar (hk a ha) e₂.entry, hw, List.map_map]
  have h2 : l.layout.args.map (fun a => wordVal (e₂.entry.regs a.reg))
      = (l.layout.args.map (·.reg)).map fun r => wordVal (e₂.entry.regs r) := by
    rw [List.map_map]
    rfl
  rw [h2, hregs, List.map_map]
  rfl

/-! ## The event relation with a guarded precondition -/

/-- **The event relation of the contracts with a guarded precondition**: the relation
    `contractRE`, in which the precondition of the linked function at the entry state is required
    only where its meaning is defined at the arguments of the call. -/
def contractREG (m : HaxModule) (e₁ : linkSig.Event) (e₂ : (kSig AState).Event) : Prop :=
  KCall.call e₂ = e₁ ∧ ∃ l, m.linked.find? (·.name == LinkCall.name e₁) = some l ∧
    ((l.sem (LinkCall.args e₁)).isSome = true → l.pre (KCall.entry e₂)) ∧
    LinkCall.args e₁ = l.layout.args.map (·.read (KCall.entry e₂))

/-- `contractRE` implies `contractREG`. -/
theorem contractREG_of_contractRE {m : HaxModule} {e₁ : linkSig.Event}
    {e₂ : (kSig AState).Event} (h : contractRE m e₁ e₂) : contractREG m e₁ e₂ := by
  obtain ⟨hc, l, hl, hpre, ha⟩ := h
  exact ⟨hc, l, hl, fun _ => hpre, ha⟩

/-- **A source call at the words of a call event related by `BackRE`.** Let the callee `c` of
    the symbol of a call event `ev` in the table `T` be the data of a linked kernel `l` of `m`
    found at that symbol, with the layout `InsLayout l c.ins res` of scalar parameters, and let a
    target event of the linked reader `linkRead m` at the symbol of `ev`, whose entry state is
    the entry of a call, be related to `ev` by `BackRE T`. The source call of the symbol at the
    argument words of `ev` is related to the target event by `contractREG`. -/
theorem contractREG_of_backRE {m : HaxModule} {T : CalleeTab}
    {ev : NFCall JasminDialect.jasminDialect} {l : LinkedFn} {c : CalleeData} {res : String}
    (K : LinkedKernel l) (hl : m.linked.find? (·.name == ev.name) = some l)
    (hc : T.lookup ev.name = some c) (hL : InsLayout l c.ins res)
    (hsc : ∀ p ∈ c.ins, p.2 = .scalar) (ret : Nat) (sA : AState)
    (h : BackRE T ev
      (⟨⟨ev.name, linkRead m ev.name (entryOf ret sA)⟩, entryOf ret sA⟩ : KCall AState)) :
    contractREG m ⟨ev.name, (wordsOf ev.args).map wordVal⟩
      (⟨⟨ev.name, linkRead m ev.name (entryOf ret sA)⟩, entryOf ret sA⟩ : KCall AState) := by
  have hr := linkRead_of_backRE hl hc hL hsc h
  have hrd : linkRead m ev.name (entryOf ret sA) = l.layout.args.map (·.read (entryOf ret sA)) := by
    simp only [linkRead, hl]
  refine ⟨?_, l, hl, fun hd => pre_entryOf_scalar K hL hsc ret sA ?_, ?_⟩
  · show (⟨ev.name, linkRead m ev.name (entryOf ret sA)⟩ : LinkCall) = _
    rw [hr]
  · rw [← hrd, hr]
    exact hd
  · show (wordsOf ev.args).map wordVal = _
    rw [← hrd, hr]

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract
