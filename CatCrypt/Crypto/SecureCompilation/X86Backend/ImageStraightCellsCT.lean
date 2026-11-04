/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightArrLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrWLeak

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the decoded bytes of the straight cell route from the source

The gate `straightCellB` of `ImageStraightCells` compiles an array-returning straight-line
program through the cell fold of its coalesced chain `arrChain`. The coalesced chain emits
`straightT` of the source events of the program with array names renamed by the alias map
(`ImageStraightArrLeak.arrChain_run_of`), so constant time of the source gives equal traces
of the chain between public-equal entries (`ChainCT`).

The passage from the address machine on the printed body to the decoded bytes is the
statement `BytesTraceW`. It follows from a traced simulation of the class with carry chains
`printedAddrWB` in which a step at program counter `pc` emits, on the decoded bytes, the
image under a map `stepGW rsp body pc` of the events of the address machine: the decoded
instructions of the carry add with a slot carry-in and of the select with a slot false value
access the frame words in an order other than that of the address machine, and several arms
add accesses of the red-zone word. A cell access and an indexed access emit the event of the
address machine; every other arm emits addresses that depend on the frame address and the
operand names only.

## Main definitions

* `straightCellComLB`: the check on traced runs of the cell route of a program,
  `straightCellLB` at the cell fold of the coalesced chain and the cells of the result.
* `runALeakG`: the address machine with the events of each step mapped by `G` at its program
  counter.
* `TracedSimW`: the traced simulation of a body by its decoded bytes for the step maps `G`.
* `gW`, `stepGW`: the step maps of the class with carry chains.
* `ArmLeaksW`: the events of the decoded instructions of the arms, one statement per arm.

## Main results

* `chainCT_of_straightCellB`: `ChainCT` of the coalesced chain from constant time of the
  source, under the gate `straightCellB`.
* `runALeakG_transfer`: two runs of the address machine with equal traces have equal mapped
  traces, over a body whose step event lengths are functions of the program counter.
* `bytesTraceW_of_tracedSim`: `BytesTraceW` from `TracedSimW` and `StepLenDet`.
* `lopn_stepW`: one `Lopn` step of the simulation of the class with carry chains, with the
  events of the decoded instructions.
* `run_simWL`, `tracedSimW_of_armLeaks`: the traced simulation from the events of the arms.
* `armLeaksW`: the events of every arm.
* `stepLenDetW`: the step event lengths of a body in `printedAddrWB` are functions of the
  program counter.
* `bytesTraceW_of_printedAddrWB`: `BytesTraceW` for every body in `printedAddrWB`.
* `straightCell_bytes_ct'`: constant time of the decoded bytes of the cell route from the
  source, under `straightCellB`, `straightCellComLB` and `BytesTraceW`.
* `straightCell_bytes_ct_src`: constant time of the decoded bytes of the cell route from the
  source, under `straightCellB` and `straightCellComLB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (renEv)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (straightT)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (LstateA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (stepA haltedA runA runA_step
  runA_halt)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightArrLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (ARun runALeak stepLeakA
  runALeak_step runALeak_halt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp RunSafe)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (SafeW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (Entry StepLenDet
  stepA_lpc_det haltedA_congr runL_det)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime ConstantTimeRel)

/-! ## 1. The coalesced chain of the cell route -/

/-- **Equal traces of the coalesced chain of the cell route from the source.** For an
    array-returning program that passes `straightCellB` against the printed body `body`: if
    the source events of the program are constant time for the labels `L`, the coalesced
    chain `arrChain` runs and emits equal traces from the states behind the copies of the
    parameter registers of machine states related by `StraightPub`. -/
theorem chainCT_of_straightCellB (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {fuse : Bool} {Γ : Ctxt jasminDialect} {m : Nat}
    (com : Com jasminDialect Γ (.stackArr 64 m))
    (hg : straightCellB σ nm body fuse com = true) (L : Labels Γ)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com)) :
    ChainCT σ L body (arrChain com) := by
  obtain ⟨-, C2, -, hroute⟩ := straightCellB_spec hg
  have hent := cellRouteB_entryB hroute
  simp only [straightCellB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨hmem, hco⟩, hfix⟩, hpl⟩, -⟩, -⟩, -⟩ := hg
  refine chainCT_of_trace
    (fun V => (straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V)).map
      (renEv (chainAlias (straightOpsMem Γ.length com Γ.length))))
    (fun sa V hV => ?_) (fun V₁ V₂ hp => by rw [hct V₁ V₂ hp])
  obtain ⟨-, hrun, hT⟩ := arrChain_run_of Pj com hmem hco hfix hpl hent sa V hV
  exact ⟨hrun, hT⟩

/-- **The check on traced runs of the cell route of a program**: on a program returning an
    array of `m` words of `64` bits whose coalesced chain has the cell fold `C2`,
    `straightCellLB` on `C2` with the cells of the result observed, the pair that
    `straightCellB` compares with `ownedCheckMC`; `false` otherwise. -/
def straightCellComLB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (fuse : Bool) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | Γ, .stackArr 64 m, com =>
      match cellFold (cellArrs σ) [] (arrChain com) with
      | some C2 =>
          straightCellLB σ nm body ((List.range m).map fun j =>
            memName (chainAlias (straightOpsMem Γ.length com Γ.length)
              (comRetReg Γ.length argName com Γ.length)) (8 * j)) C2 fuse
      | none => false
  | _, _, _ => false

/-- **Constant time of the decoded bytes of the cell route from the source.** Let the
    program `com` pass the gate `straightCellB` at the fusion flag `fuse` and the check on
    traced runs `straightCellComLB` against the printed body `body`. If the source events of
    `com` are constant time for the labels `L`, then, given the passage `BytesTraceW` from
    the address machine on `body` to its decoded bytes, every decoding of the function bytes
    of `body` is constant time under the regime `doitm` and any side condition between entry
    machine states related by `StraightPub`. -/
theorem straightCell_bytes_ct' (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {fuse : Bool} {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (hg : straightCellB σ nm body fuse com = true)
    (hlk : straightCellComLB σ nm body fuse com = true) (L : Labels Γ)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com))
    (hB : BytesTraceW body) (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (StraightPub σ L) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  obtain ⟨m, rfl⟩ := straightCellB_ty hg
  have hC := chainCT_of_straightCellB Pj com hg L hct
  obtain ⟨hN, C2, hfold, hroute⟩ := straightCellB_spec hg
  have hfold' : cellFold (cellArrs σ) [] (arrChain com) = some C2 := hfold
  simp only [straightCellComLB, hfold'] at hlk
  exact straightCell_bytes_ct hroute hlk hN hfold' hC hB ok hdec

/-! ## 2. The address machine with mapped step events -/

/-- **The address machine with the events of each step mapped by `G`**: the recursion of
    `runALeak`, a step from a state at program counter `pc` emitting `G pc` of its events
    `stepLeakA`. -/
def runALeakG (G : Nat → List CTLeak → List CTLeak) (frame : String → Option (BitVec 64))
    (c : Lcmd) : Nat → LstateA → Bool → Option ((LstateA × Bool) × List CTLeak)
  | 0, s, zf => if haltedA c s then some ((s, zf), []) else none
  | fuel + 1, s, zf =>
      if haltedA c s then some ((s, zf), [])
      else (stepA frame c s zf).bind fun bz =>
        (runALeakG G frame c fuel bz.1 bz.2).map fun r =>
          (r.1, G s.reg.lpc (stepLeakA frame c s zf) ++ r.2)

theorem runALeakG_halt (G : Nat → List CTLeak → List CTLeak)
    (frame : String → Option (BitVec 64)) (c : Lcmd) (fuel : Nat) (s : LstateA) (zf : Bool)
    (h : haltedA c s = true) : runALeakG G frame c fuel s zf = some ((s, zf), []) := by
  cases fuel <;> simp [runALeakG, h]

theorem runALeakG_step (G : Nat → List CTLeak → List CTLeak)
    (frame : String → Option (BitVec 64)) (c : Lcmd) (fuel : Nat) (s : LstateA) (zf : Bool)
    (h : haltedA c s = false) :
    runALeakG G frame c (fuel + 1) s zf
      = (stepA frame c s zf).bind fun bz =>
          (runALeakG G frame c fuel bz.1 bz.2).map fun r =>
            (r.1, G s.reg.lpc (stepLeakA frame c s zf) ++ r.2) := by
  simp [runALeakG, h]

/-- With the identity maps the run is `runALeak`. -/
theorem runALeakG_id (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool),
      runALeakG (fun _ ℓ => ℓ) frame c fuel s zf = runALeak frame c fuel s zf := by
  intro fuel
  induction fuel with
  | zero => intro s zf; rfl
  | succ n ih =>
    intro s zf
    cases hh : haltedA c s
    · rw [runALeakG_step _ _ _ _ _ _ hh, runALeak_step _ _ _ _ _ hh]
      simp only [ih]
    · rw [runALeakG_halt _ _ _ _ _ _ hh, runALeak_halt _ _ _ _ _ hh]

/-- The state component of the run with mapped events is `runA`. -/
theorem runALeakG_fst (G : Nat → List CTLeak → List CTLeak)
    (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool),
      (runALeakG G frame c fuel s zf).map Prod.fst = runA frame c fuel s zf := by
  intro fuel
  induction fuel with
  | zero =>
    intro s zf
    cases hh : haltedA c s <;> simp [runALeakG, runA, hh]
  | succ n ih =>
    intro s zf
    cases hh : haltedA c s
    · rw [runALeakG_step G frame c n s zf hh, runA_step frame c n s zf hh]
      cases stepA frame c s zf with
      | none => rfl
      | some bz =>
        simp only [Option.bind_some]
        rw [← ih bz.1 bz.2, Option.map_map]
        rfl
    · rw [runALeakG_halt G frame c _ s zf hh, runA_halt frame c _ s zf hh]
      rfl

/-- A terminating run of the address machine has a trace with mapped events. -/
theorem runALeakG_of_runA (G : Nat → List CTLeak → List CTLeak)
    {frame : String → Option (BitVec 64)} {c : Lcmd} {fuel : Nat} {s : LstateA} {zf : Bool}
    {t : LstateA × Bool} (h : runA frame c fuel s zf = some t) :
    ∃ ℓ, runALeakG G frame c fuel s zf = some (t, ℓ) := by
  rw [← runALeakG_fst G] at h
  obtain ⟨⟨t', ℓ⟩, h1, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨ℓ, h1⟩

/-- **Transfer of equal traces to mapped traces.** Over a body whose step event lengths are
    functions of the program counter, two terminating runs of the address machine from one
    program counter with equal traces have equal traces with the events of each step mapped
    by `G`. -/
theorem runALeakG_transfer {frame : String → Option (BitVec 64)} {c : Lcmd}
    (hlen : StepLenDet frame c) (G : Nat → List CTLeak → List CTLeak) :
    ∀ (f₁ f₂ : Nat) (s₁ s₂ : LstateA) (zf₁ zf₂ : Bool) (r₁ r₂ q₁ q₂ : LstateA × Bool)
      (ℓ m₁ m₂ : List CTLeak), s₁.reg.lpc = s₂.reg.lpc →
      runALeak frame c f₁ s₁ zf₁ = some (r₁, ℓ) → runALeak frame c f₂ s₂ zf₂ = some (r₂, ℓ) →
      runALeakG G frame c f₁ s₁ zf₁ = some (q₁, m₁) →
      runALeakG G frame c f₂ s₂ zf₂ = some (q₂, m₂) → m₁ = m₂ := by
  intro f₁
  induction f₁ with
  | zero =>
    intro f₂ s₁ s₂ zf₁ zf₂ r₁ r₂ q₁ q₂ ℓ m₁ m₂ hpc hA₁ hA₂ hX₁ hX₂
    cases hh : haltedA c s₁
    · simp [runALeak, hh] at hA₁
    · have hh₂ : haltedA c s₂ = true := by rw [← haltedA_congr hpc, hh]
      rw [runALeakG_halt _ _ _ _ _ _ hh] at hX₁
      rw [runALeakG_halt _ _ _ _ _ _ hh₂] at hX₂
      cases hX₁; cases hX₂; rfl
  | succ f ih =>
    intro f₂ s₁ s₂ zf₁ zf₂ r₁ r₂ q₁ q₂ ℓ m₁ m₂ hpc hA₁ hA₂ hX₁ hX₂
    cases hh : haltedA c s₁
    · have hh₂ : haltedA c s₂ = false := by rw [← haltedA_congr hpc, hh]
      cases f₂ with
      | zero => simp [runALeak, hh₂] at hA₂
      | succ g =>
        rw [runALeak_step _ _ _ _ _ hh] at hA₁
        rw [runALeak_step _ _ _ _ _ hh₂] at hA₂
        rw [runALeakG_step _ _ _ _ _ _ hh] at hX₁
        rw [runALeakG_step _ _ _ _ _ _ hh₂] at hX₂
        cases hs₁ : stepA frame c s₁ zf₁ with
        | none => rw [hs₁] at hA₁; cases hA₁
        | some b₁ =>
          cases hs₂ : stepA frame c s₂ zf₂ with
          | none => rw [hs₂] at hA₂; cases hA₂
          | some b₂ =>
            rw [hs₁, Option.bind_some] at hA₁ hX₁
            rw [hs₂, Option.bind_some] at hA₂ hX₂
            obtain ⟨⟨r₁', ℓ₁⟩, hA₁', e₁⟩ := Option.map_eq_some_iff.mp hA₁
            obtain ⟨⟨r₂', ℓ₂⟩, hA₂', e₂⟩ := Option.map_eq_some_iff.mp hA₂
            obtain ⟨⟨q₁', m₁'⟩, hX₁', e₃⟩ := Option.map_eq_some_iff.mp hX₁
            obtain ⟨⟨q₂', m₂'⟩, hX₂', e₄⟩ := Option.map_eq_some_iff.mp hX₂
            simp only [Prod.mk.injEq] at e₁ e₂ e₃ e₄
            have happ := e₁.2.trans e₂.2.symm
            obtain ⟨hst, hrest⟩ :=
              List.append_inj happ (hlen s₁ s₂ zf₁ zf₂ b₁ b₂ hpc hs₁ hs₂)
            have hpc' := stepA_lpc_det hpc hs₁ hs₂ hst
            subst hrest
            have hm := ih g b₁.1 b₂.1 b₁.2 b₂.2 r₁' r₂' q₁' q₂' ℓ₁ m₁' m₂' hpc' hA₁' hA₂' hX₁' hX₂'
            rw [← e₃.2, ← e₄.2, hst, hpc, hm]
    · have hh₂ : haltedA c s₂ = true := by rw [← haltedA_congr hpc, hh]
      rw [runALeakG_halt _ _ _ _ _ _ hh] at hX₁
      rw [runALeakG_halt _ _ _ _ _ _ hh₂] at hX₂
      cases hX₁; cases hX₂; rfl

/-! ## 3. The decoded bytes from the traced simulation -/

/-- **The traced simulation of a body by its decoded bytes** for the step maps `G`, which
    depend on the frame address: from a machine state `sa` and an address state at the entry
    correspondence `Entry`, every terminating run of the address machine that is safe in the
    sense of `SafeW`, with the trace `ℓ` of `runALeakG`, is matched by a run with leakage `ℓ`
    of a decoding of the function bytes under the regime `doitm`.
    `DecodePrintedAddrLeak.printedAddr_simL` is this statement for the class `printedAddrB`,
    with the maps that append the red-zone accesses of an arm. -/
def TracedSimW (G : BitVec 64 → Nat → List CTLeak → List CTLeak) (body : Lcmd) : Prop :=
  ∀ (sa : AState) (s : LstateA) (zf : Bool), Entry sa s →
    ∀ (fuel : Nat) (t : LstateA × Bool) (ℓ : List CTLeak),
      runALeakG (G (frameRsp body sa)) (frameP (Params.ofBody body) (frameRsp body sa)) body
        fuel s zf = some (t, ℓ) →
      RunSafe (frameP (Params.ofBody body) (frameRsp body sa)) body
        (SafeW (frameRsp body sa) body) fuel s zf →
      ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
        ∧ RunL .doitm (fun _ _ => True) prog 0 sa ℓ sa'

/-- **Equal traces of the decoded bytes from the traced simulation.** For a body with a
    traced simulation `TracedSimW` at step maps `G`, whose step event lengths on the address
    machine are functions of the program counter at every frame address, equal traces of the
    address machine give equal traces of the decoded bytes: `BytesTraceW`. -/
theorem bytesTraceW_of_tracedSim {G : BitVec 64 → Nat → List CTLeak → List CTLeak}
    {body : Lcmd} (hsim : TracedSimW G body)
    (hlen : ∀ rsp, StepLenDet (frameP (Params.ofBody body) rsp) body) : BytesTraceW body := by
  rintro prog hdec rsp sa₁ sa₂ hr₁ hr₂ a₁ a₂ he₁ he₂ ⟨f₁, t₁, hrA₁, hs₁⟩ ⟨f₂, t₂, hrA₂, hs₂⟩
    hℓ ok₁ ok₂ u₁ u₂ sa₁' sa₂' hb₁ hb₂
  obtain ⟨m₁, hX₁⟩ := runALeakG_of_runA (G rsp) hrA₁
  obtain ⟨m₂, hX₂⟩ := runALeakG_of_runA (G rsp) hrA₂
  obtain ⟨ℓ₁, hA₁⟩ := runALeakG_of_runA (fun _ ℓ => ℓ) hrA₁
  obtain ⟨ℓ₂, hA₂⟩ := runALeakG_of_runA (fun _ ℓ => ℓ) hrA₂
  rw [runALeakG_id] at hA₁ hA₂
  subst hr₁
  obtain ⟨p₁, c₁, hd₁, hL₁⟩ := hsim sa₁ a₁.1 a₁.2 he₁ f₁ t₁ m₁ hX₁ hs₁
  obtain ⟨p₂, c₂, hd₂, hL₂⟩ := hsim sa₂ a₂.1 a₂.2 he₂ f₂ t₂ m₂
    (by rw [hr₂]; exact hX₂) (by rw [hr₂]; exact hs₂)
  rw [hdec] at hd₁ hd₂
  cases hd₁; cases hd₂
  have e₁ := (runL_det hb₁ hL₁).1
  have e₂ := (runL_det hb₂ hL₂).1
  have hl : ℓ₁ = ℓ₂ := hℓ ℓ₁ ℓ₂ ⟨f₁, t₁, hA₁⟩ ⟨f₂, t₂, hA₂⟩
  subst hl
  rw [e₁, e₂]
  exact runALeakG_transfer (hlen _) (G _) f₁ f₂ a₁.1 a₂.1 a₁.2 a₂.2
    t₁ t₂ t₁ t₂ ℓ₁ m₁ m₂ (by rw [he₁.1, he₂.1]) hA₁ hA₂ hX₁ hX₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrWLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL blockLeakA opLeak resolveEv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (instrLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak (BytesTraceW
  instrLeakA_cellLd)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel DoitRegime X86Mnem)

attribute [local simp] VIR.WidthTagSimp.untagCaret_load64 VIR.WidthTagSimp.untagCaret_store64
  VIR.WidthTagSimp.untagCaret_lea64 VIR.WidthTagSimp.untagCaret_mov64

/-- An immediate move `o D, #n` at an immediate-move mnemonic `o` (`MOV` or `MOV^w`,
    `w ≠ 64`) carries the register tag without width. -/
private theorem tagA_movImm {D o : String} {n : Nat}
    (h : JasminLsemCast.isMovImmMnem o = true) :
    tagA (.Lopn [.reg D] o [.imm n]) = .reg none := by
  rcases JasminLsemCast.isMovImmMnem_iff.1 h with rfl | ⟨w, hw, rfl⟩
  · simp (config := { decide := true }) [tagA]
  · simp (disch := decide +kernel) [tagA, width_tag,
      LprogAsmPrinter.untagCaret_withWidthTag hw (m := "MOV") (by decide +kernel)]

/-- An immediate-move mnemonic (`MOV` or `MOV^w`, `w ≠ 64`) encodes to the bytes of `MOV`. -/
private theorem encodeLopn_movImm_eq (frame spillW : Nat) (ds : List LOperand) {o : String}
    (h : JasminLsemCast.isMovImmMnem o = true) (ss : List LOperand) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn ds o ss) qsaveB
      = encodeLopn frame spillW (.Lopn ds "MOV" ss) qsaveB := by
  rcases JasminLsemCast.isMovImmMnem_iff.1 h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · exact encodeLopn_retag32 frame spillW ds hw (by decide) (by decide +kernel)
      (by decide +kernel) ss qsaveB

/-! ## 4. The step maps of the class with carry chains -/

/-- The events of the decoded instructions of a carry arm with frame-slot operands: the
    frame words of the slot operands in the order the machine instructions access them, with
    the accesses of the red-zone word `redW rsp` of the save and restore of the scratch. -/
def sLeakW (P : Params) (rsp : BitVec 64) : SArm → List CTLeak
  | .adcx D A S _ =>
      if isSpillOrQsave D then
        evA (redW rsp) :: (fEv P rsp A ++ fEv P rsp S ++ fEv P rsp D ++ [evA (redW rsp)])
      else fEv P rsp A ++ fEv P rsp S
  | .adcxhi _ _ _ _ => []
  | .adcxc D A S C =>
      evA (redW rsp) :: fEv P rsp C
        ++ (if isSpillOrQsave D then
              fEv P rsp A ++ fEv P rsp S ++ fEv P rsp D ++ [evA (redW rsp)]
            else evA (redW rsp) :: (fEv P rsp A ++ fEv P rsp S))

/-- The events of the decoded instructions of an immediate store into the frame slot `q`:
    the frame word of `q`, between two accesses of the red-zone word when the value does not
    sign-extend from 32 bits. -/
def iLeakW (P : Params) (rsp : BitVec 64) (q : String) (v : Nat) : List CTLeak :=
  if ScalarEncoder.fitsImm32S v then [evA (rsp + BitVec.ofInt 64 (slotOff P q))]
  else [evA (redW rsp), evA (rsp + BitVec.ofInt 64 (slotOff P q)), evA (redW rsp)]

/-- **The step map of an instruction of the class with carry chains**: the events of its
    decoded instructions under `doitm` from the events `ℓ` of the address machine. A cell
    access emits `ℓ`; an arm of `DecodePrintedAddr` emits `ℓ` and its red-zone accesses; every
    other instruction emits frame and red-zone addresses that depend on the frame address
    and the operand names only. The cases follow `instrOKWB`. -/
def gW (P : Params) (rsp : BitVec 64) (i : LinstrR) (ℓ : List CTLeak) : List CTLeak :=
  match classifyK i with
  | some _ => []
  | none =>
  match movImmStruct? i with
  | some _ => []
  | none =>
  match classifyS i with
  | some c => sLeakW P rsp c
  | none =>
  match classifyC i with
  | some _ => []
  | none =>
  match classifyM i with
  | some _ => ℓ
  | none =>
  match classifyI i with
  | some (q, v) => iLeakW P rsp q v
  | none =>
  match classifyL i with
  | some _ => []
  | none =>
  match classifyV i with
  | some (_, _, a, b) => fEv P rsp b ++ fEv P rsp a
  | none =>
  match classifyE i with
  | some _ => []
  | none =>
  match classifyX i with
  | some _ => []
  | none =>
  match classifyEI i with
  | some _ => []
  | none =>
  match classifyR i with
  | some _ => []
  | none =>
  match classifyA i with
  | some a => ℓ ++ redLeak rsp a
  | none => ℓ

/-- The step map of a body at the program counter `k`: `gW` at an `Lopn`, the identity at a
    label, a branch and the return. -/
def stepGW (rsp : BitVec 64) (body : Lcmd) (k : Nat) (ℓ : List CTLeak) : List CTLeak :=
  match body[k]? with
  | some ⟨_, .Lopn ds o ss⟩ => gW (Params.ofBody body) rsp (.Lopn ds o ss) ℓ
  | _ => ℓ

/-- **The events of the decoded instructions of the select with a slot false value whose true
    value is the destination.** Under `doitm`, from a machine state whose stack register holds
    `rsp`: the access of the frame word of the false value. -/
theorem leak_cmovSlotFE (P : Params) (rsp : BitVec 64) (D C B : String)
    (h : vfOk P D C D B = true) (sa : AState) (hsp : sa.regs "%rsp" = rsp) :
    blockLeakA .doitm sa ((vePieces P D C B).map Prod.snd) = fEv P rsp B ++ fEv P rsp D := by
  simp only [vfOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, -⟩, hBs⟩, hBk⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hsp1 : (evalInstrA sa (.test (phys C) (.reg (phys C)))).regs "%rsp" = rsp := by
    simpa [evalInstrA, evalInstr, AState.view, JState.writeB5] using hsp
  rw [fEv_slot hBk hBs, fEv_gp hD]
  simp [vePieces, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
    DoitRegime.leaksOperands, X86Mnem.timing, evA, hsp1]

/-- **The events of the decoded instructions of the arms** of the class with carry chains at
    the parameters `P` and the frame address `rsp`, under the regime `doitm`, one statement
    per arm: the carry constant and the 32-bit constant (`zmov`), the carry arms with
    frame-slot operands (`sarm`), the carry arms on registers (`carm`), the cell load, store
    and moves into and out of a cell (`ldm`, `stm`, `stv`, `ldv`), the immediate store into a
    slot (`imm`), the wide immediate
    (`lmov`), the register select and the select with a slot true value (`vreg`, `vt`), the
    materialised comparison against a register and an immediate (`sete`, `seteImm`), the
    register-count shift (`shrx`), the arithmetic right shift by an immediate (`sarImm`), and
    the arms of `DecodePrintedAddr` on the correspondence with narrow names (`aarm`). The
    width cast and the select with a slot false value are
    `DecodePrintedAddrWLeak.leak_castW`, `leak_cmovSlotF` and `leak_cmovSlotFE`. -/
structure ArmLeaksW (P : Params) (rsp : BitVec 64) : Prop where
  zmov : ∀ (D : String) (n : Nat) (sa : AState),
    blockLeakA .doitm sa ((zPieces D n).map Prod.snd) = []
  sarm : ∀ c : SArm, c.ok P = true → ∀ sa : AState, sa.regs "%rsp" = rsp →
    blockLeakA .doitm sa (c.js P) = sLeakW P rsp c
  carm : ∀ (c : CArm) (sa : AState), blockLeakA .doitm sa c.js = []
  ldm : ∀ (D n B : String) (off : Nat), (MArm.ldm D n B off).ok = true →
    ∀ (sa : AState) (s : LstateA), ACorrW rsp sa s → (s.reg.lvm B).1 = 64 →
      blockLeakA .doitm sa (MArm.ldm D n B off).js
        = instrLeakA (frameP P rsp) ((MArm.ldm D n B off).instr, .reg none) s
  stm : ∀ (n B : String) (off : Nat) (S : String), (MArm.stm n B off S).ok = true →
    ∀ (sa : AState) (s : LstateA), ACorrW rsp sa s → (s.reg.lvm B).1 = 64 →
      blockLeakA .doitm sa (MArm.stm n B off S).js
        = instrLeakA (frameP P rsp) ((MArm.stm n B off S).instr, .reg none) s
  stv : ∀ (n B : String) (off : Nat) (S : String), (MArm.stv n B off S).ok = true →
    ∀ (sa : AState) (s : LstateA), ACorrW rsp sa s → (s.reg.lvm B).1 = 64 →
      blockLeakA .doitm sa (MArm.stv n B off S).js
        = instrLeakA (frameP P rsp) ((MArm.stv n B off S).instr, .reg none) s
  ldv : ∀ (D n B : String) (off : Nat), (MArm.ldv D n B off).ok = true →
    ∀ (sa : AState) (s : LstateA), ACorrW rsp sa s → (s.reg.lvm B).1 = 64 →
      blockLeakA .doitm sa (MArm.ldv D n B off).js
        = instrLeakA (frameP P rsp) ((MArm.ldv D n B off).instr, .reg none) s
  imm : ∀ (q : String) (v : Nat), iOk P q v = true → ∀ sa : AState, sa.regs "%rsp" = rsp →
    blockLeakA .doitm sa ((iPieces P q v).map Prod.snd) = iLeakW P rsp q v
  lmov : ∀ (D : String) (v : Nat) (sa : AState),
    blockLeakA .doitm sa ((lPieces D v).map Prod.snd) = []
  vreg : ∀ D C A B : String, vOk D C A B = true → ∀ sa : AState,
    blockLeakA .doitm sa ((vPieces D C A B).map Prod.snd) = fEv P rsp B ++ fEv P rsp A
  vt : ∀ D C A B : String, vtOk P D C A B = true → ∀ sa : AState, sa.regs "%rsp" = rsp →
    blockLeakA .doitm sa ((vtPieces P D C A B).map Prod.snd) = fEv P rsp B ++ fEv P rsp A
  sete : ∀ (n : Bool) (D A B : String) (sa : AState),
    blockLeakA .doitm sa ((ePieces n D A B).map Prod.snd) = []
  seteImm : ∀ (n : Bool) (D A : String) (v : Nat) (sa : AState),
    blockLeakA .doitm sa ((eiPieces n D A v).map Prod.snd) = []
  shrx : ∀ (l : Bool) (D A B : String) (sa : AState),
    blockLeakA .doitm sa ((xPieces l D A B).map Prod.snd) = []
  sarImm : ∀ (D : String) (k : Nat) (sa : AState),
    blockLeakA .doitm sa ((rPieces D k).map Prod.snd) = []
  aarm : ∀ a : AArm, a.ok P = true → ∀ (sa : AState) (s : LstateA), ACorrW rsp sa s →
    WideAt s a.li.fst →
      blockLeakA .doitm sa (a.js P) = instrLeakA (frameP P rsp) a.li s ++ redLeak rsp a

/-! ## 5. One step of the traced simulation -/

/-- **One `Lopn` step on both machines, with leakage.** At an `Lopn` at position `k` of a
    body in `printedAddrWB`, from states related by `ACorrW` with the carry-out requirement
    and the safety condition `SafeWN`, a step of the address machine is matched by the
    decoded instructions `js` of the shape at `k`: the address machine moves to `k + 1`, the
    states after `js` are related by `ACorrW`, the machine zero flag is the flag before a
    conditional branch, the carry-out requirement holds at `k + 1`, and the events of `js`
    under `doitm` are `gW` of the events of the step. -/
theorem lopn_stepW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs)
    (rsp : BitVec 64) (hAL : ArmLeaksW (Params.ofBody body) rsp) {k : Nat}
    (hk : k < body.length) (hkn : k + 1 < body.length) (hks : k < shs.length) {ii : Nat}
    {ds : List LOperand} {o : String} {ss : List LOperand}
    (hbk : body[k]'hk = ⟨ii, .Lopn ds o ss⟩) (sa : AState) (s : LstateA) (zf : Bool)
    (hpc : s.reg.lpc = k) (hc : ACorrW rsp sa s)
    (hcy : CarryReq (frameP (Params.ofBody body) rsp) body k sa s)
    (hsafe : SafeWN rsp body s) (s' : LstateA) (zf' : Bool)
    (hst : stepA (frameP (Params.ofBody body) rsp) body s zf = some (s', zf')) :
    ∃ js, (shs[k]'hks).ops' = js ∧ s'.reg.lpc = k + 1
      ∧ ACorrW rsp (aMachine.runBlock sa js) s'
      ∧ (isCondB (body[k + 1]'hkn).li_i = true →
          (aMachine.runBlock sa js).flags.zf.getD false = zf')
      ∧ CarryReq (frameP (Params.ofBody body) rsp) body (k + 1) (aMachine.runBlock sa js) s'
      ∧ blockLeakA .doitm sa js = gW (Params.ofBody body) rsp (.Lopn ds o ss)
          (stepLeakA (frameP (Params.ofBody body) rsp) body s zf) := by
  set P := Params.ofBody body with hP
  set frame := frameP P rsp
  obtain ⟨hl, hsh⟩ := shapesOf_spec P body shs hF.shapes
  have hok := hF.instr k hkn
  have hget : body[s.reg.lpc]? = some (body[k]'hk) := by
    rw [hpc]; exact List.getElem?_eq_getElem hk
  have hshk := hsh k hk hks
  have hnoadd : (∀ ii d a s c, body[k]? ≠
      some ⟨ii, .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩) →
      ∀ sa s, CarryReq frame body (k + 1) sa s :=
    fun h sa s => no_carryReq hF hkn h frame sa s
  have hcondNext : isCondB (body[k + 1]'hkn).li_i = true →
      ((classifyA (body[k]'hk).li_i).any cmpArmB) = true := by
    intro hcnd
    have hc2 := hF.cond (k + 1) hkn
    unfold condPrevB at hc2
    rw [List.getElem?_eq_getElem hkn] at hc2
    revert hc2 hcnd
    rcases body[k + 1] with ⟨ii', li'⟩
    cases li' <;> simp [isCondB, List.getElem?_eq_getElem hk]
  rw [hbk] at hok hget hshk hcondNext
  simp only at hok hshk hcondNext
  have hbk? : body[k]? = some ⟨ii, .Lopn ds o ss⟩ := by rw [body_get hk, hbk]
  have hGl : stepLeakA frame body s zf
      = instrLeakA frame (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) s := by
    simp only [stepLeakA, hget]
  have hstepEq : stepA frame body s zf
      = fstepA frame (normA (.Lopn ds o ss), tagAt body k (.Lopn ds o ss)) s zf := by
    simp only [stepA, hget]
    rw [hpc]
  rw [hstepEq] at hst
  simp only [instrOKWB] at hok
  split at hok
  · -- a width-carrying cast
    rename_i D A m w' hclK
    obtain ⟨o', hia, hm, hw⟩ := classifyK_spec hclK
    simp only [LinstrR.Lopn.injEq] at hia
    obtain ⟨rfl, rfl, rfl⟩ := hia
    simp only [castOk, Bool.and_eq_true] at hok
    rw [normA_castW hw, tagAt_castW body k hw] at hst
    have hmin : m = min (s.reg.lvm A).1 w' := by
      have hcp := hF.cast k hk
      simp only [castPosB, hbk?, Option.all_some, hclK, beq_iff_eq] at hcp
      cases hl : (narrowIn body k).lookup A with
      | none =>
        rw [hl] at hcp
        have h64 := hsafe.2.1 ii _ _ _ (by rw [hget]) A (reg_reads (by simp)) hok.2
          (by simp [carryIns]) (by
            have hsm : slotMov? (.Lopn [.reg D] o [.reg A]) = none := by
              have ho : ¬(o = "MOVQ" ∨ o = "MOV:64") := by
                rintro (rfl | rfl) <;> simp [castTagW] at hw
              simp only [slotMov?, ite_eq_right ho]
            rw [hpc]
            simp only [narrowSrc, hbk?, hclK, hl, List.mem_append, not_or]
            exact ⟨by simp, not_mem_bitSrc hget hsm A⟩)
        rw [h64]
        simpa using hcp
      | some w0 =>
        rw [hl] at hcp
        have hw0 := hsafe.2.2.2 _ hget (by rw [hclK]; rfl) A w0 (by rw [hpc]; exact hl)
        rw [hw0]
        simpa using hcp
    obtain ⟨hc', -⟩ := sim_castW_bytes P rsp o D A w' m hm hok.1 hok.2 (castTagW_width hw)
      sa s zf hc hmin s' zf' hst
    have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
    have hz' : isCondB (body[k + 1]'hkn).li_i = true →
        (aMachine.runBlock sa ((castPieces m D A).map Prod.snd)).flags.zf.getD false
          = zf' := by
      intro hcnd
      have hcm := hcondNext hcnd
      simp only [classifyA] at hcm
      split_ifs at hcm <;> simp [cmpArmB, Option.any_map] at hcm
    have hna : ∀ ii' d a s c, body[k]? ≠
        some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩ := by
      intro ii' d a s c h
      rw [hbk?] at h
      simp at h
    obtain ⟨hb, hp⟩ := castBytes P o D A m hm hok.1 hok.2
    have hops : shs[k].ops' = (castPieces m D A).map Prod.snd :=
      shapeOf_lopn_ops _ hb hp hshk
    have hlk : blockLeakA .doitm sa ((castPieces m D A).map Prod.snd)
        = gW P rsp (.Lopn [.reg D] o [.reg A]) (stepLeakA frame body s zf) := by
      rw [leak_castW]
      simp only [gW, hclK]
    exact ⟨_, hops, hpc', hc', hz', hnoadd hna _ _, hlk⟩
  rename_i hclK
  by_cases h1b : bitSrc body s = []
  swap
  · -- a frame-word store of a one-bit name
    obtain ⟨S, hS1⟩ := List.exists_mem_of_ne_nil _ h1b
    obtain ⟨i, q, bS, hi, hmv, hq, hpre, hbS⟩ := bitSrc_spec hS1
    have hcq : cellParts? q = none := by simp [cellParts?, hpre]
    rw [hget] at hi
    cases hi
    obtain ⟨m, hia, hm⟩ : ∃ m, LinstrR.Lopn ds o ss = .Lopn [.reg q] m [.reg S]
        ∧ (m = "MOVQ" ∨ m = "MOV:64") := by
      unfold slotMov? at hmv
      split at hmv
      · next dst opn src heq =>
        split_ifs at hmv with hm0
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmv)
        exact ⟨_, heq, hm0⟩
      · cases hmv
    simp only [LinstrR.Lopn.injEq] at hia
    obtain ⟨rfl, rfl, rfl⟩ := hia
    have hcl : classifyA (.Lopn [.reg q] o [.reg S]) = some (.st o q S) := by
      rcases hm with rfl | rfl <;> simp [classifyA, isMovM, hq]
    have hcS : o = "MOV:64" → cellParts? S = none := by
      rintro rfl
      cases h : cellParts? S with
      | none => rfl
      | some p => simp [slotMov?, h] at hmv
    have hok' : (AArm.st o q S).ok P = true := by
      rcases hm with rfl | rfl <;>
        simpa (config := { decide := true }) [movImmStruct?, classifyS, classifyC,
          classifyM, classifyI, classifyL, classifyV, classifyE, classifyX, classifyEI,
          classifyR, hcl, hcq, hcS]
          using hok
    have hli := AArm.li_eq hok'
    have hgw : gW P rsp (.Lopn [.reg q] o [.reg S]) (stepLeakA frame body s zf)
        = instrLeakA frame (AArm.st o q S).li s ++ redLeak rsp (.st o q S) := by
      have h1 : gW P rsp (.Lopn [.reg q] o [.reg S]) (stepLeakA frame body s zf)
          = stepLeakA frame body s zf ++ redLeak rsp (.st o q S) := by
        rcases hm with rfl | rfl <;>
          simp (config := { decide := true }) [gW, hclK, movImmStruct?, classifyS, classifyC,
            classifyM, classifyI, classifyL, classifyV, classifyE, classifyX, classifyEI,
            classifyR, hcl, hcq, hcS]
      rw [h1, hGl, show LinstrR.Lopn [.reg q] o [.reg S] = (AArm.st o q S).instr from rfl, hli]
    rw [tagAt_of_not (bitMovB_of_ne (by rcases hm with rfl | rfl <;> rfl))] at hst
    rw [show LinstrR.Lopn [.reg q] o [.reg S] = (AArm.st o q S).instr from rfl, hli] at hst
    have hc' := AArm.simW_st1 P rsp o q S hok' sa s zf hc hbS s' zf' hst
    have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
    have hz' : isCondB (body[k + 1]'hkn).li_i = true →
        (aMachine.runBlock sa ((AArm.st o q S).js P)).flags.zf.getD false = zf' := by
      intro hcnd
      have hcm := hcondNext hcnd
      rw [hcl] at hcm
      simp [cmpArmB] at hcm
    have hna : ∀ ii' d a s c, body[k]? ≠
        some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩ := by
      intro ii' d a s c h
      rw [hbk?] at h
      simp only [Option.some.injEq, Linstr.mk.injEq, LinstrR.Lopn.injEq] at h
      rcases hm with rfl | rfl <;> simp at h
    have hcS : cellParts? S = none := by
      have h := hok'
      simp only [AArm.ok, Bool.and_eq_true] at h
      exact cellParts?_gp h.1.1.1.1
    have hcell : cellA? (AArm.st o q S).instr = none := by
      rcases hm with rfl | rfl <;>
        simp (disch := decide) [AArm.instr, cellA?, hcq, hcS,
          LprogAsmPrinter.untagCaret_of_caret_free]
    have hlk : blockLeakA .doitm sa ((AArm.st o q S).js P)
        = gW P rsp (.Lopn [.reg q] o [.reg S]) (stepLeakA frame body s zf) := by
      rw [hgw, AArm.leak P rsp _ hok' sa (widenS sa s) hc.widen]
      congr 1
      simp only [AArm.li]
      exact instrLeakA_reg_indep hcell none _ _
    exact ⟨_, AArm.shape_ops hok' hshk, hpc', hc', hz', hnoadd hna _ _, hlk⟩
  have hws : ∀ r, readsI (.Lopn ds o ss) r → gpOk r = true →
      r ∉ carryIns (.Lopn ds o ss) → (s.reg.lvm r).1 = 64 := fun r h1 h2 h3 =>
    hsafe.2.1 ii ds o ss (by rw [hget]) r h1 h2 h3 (by simp [narrowSrc, hget, hclK, h1b])
  split at hok
  · -- an untagged immediate move: a carry constant or a 32-bit constant
    rename_i D n hmv
    have hmo : JasminLsemCast.isMovImmMnem o = true := by
      unfold movImmStruct? at hmv
      split at hmv
      · rename_i heq
        simp only [LinstrR.Lopn.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        split at hmv
        · assumption
        · cases hmv
      · cases hmv
    have hia : LinstrR.Lopn ds o ss = .Lopn [.reg D] o [.imm n] := by
      obtain ⟨o', h'⟩ := JasminLsemCast.movImmStruct?_spec hmv
      rw [h']
      simp only [LinstrR.Lopn.injEq] at h'
      rw [h'.2.1]
    have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
    have hc' : ACorrW rsp (aMachine.runBlock sa ((zPieces D n).map Prod.snd)) s' := by
      cases hbit : bitMovB body k (.Lopn ds o ss) with
      | true =>
        have hz : zOk D n = true := by
          have hb := hbit
          simp only [bitMovB, hmv, Bool.and_eq_true, decide_eq_true_eq] at hb
          simp only [imm32Ok, Bool.and_eq_true] at hok
          simp [zOk, hok.1, hb.1.1]
        have hli : (normA (.Lopn ds o ss), tagAt body k (.Lopn ds o ss))
            = (.Lopn [.reg D] "MOV" [.imm n], MemTag.reg (some 1)) := by
          rw [tagAt, ite_eq_left hbit, hia, ImageAddrSimW.normA_movImm hmo]
        rw [hli] at hst
        exact (sim_bmov P rsp D n hz sa s zf hc s' zf' hst).1
      | false =>
        have hli : (normA (.Lopn ds o ss), tagAt body k (.Lopn ds o ss))
            = (.Lopn [.reg D] "MOV" [.imm n], MemTag.reg none) := by
          rw [tagAt_of_not hbit, hia, ImageAddrSimW.normA_movImm hmo, tagA_movImm hmo]
        rw [hli] at hst
        exact (sim_imov P rsp D n hok sa s zf hc s' zf' hst).1
    have hz' : isCondB (body[k + 1]'hkn).li_i = true →
        (aMachine.runBlock sa ((zPieces D n).map Prod.snd)).flags.zf.getD false = zf' := by
      intro hcnd
      have hcm := hcondNext hcnd
      have ho64 : o ≠ "MOV:64" := fun e => by
        rw [e, ImageAddrSimW.isMovImmMnem_mov64] at hmo; cases hmo
      rw [hia] at hcm
      simp [classifyA, classify, ho64] at hcm
    have hna : ∀ ii' d a s c, body[k]? ≠
        some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩ := by
      intro ii' d a s c h
      rw [hbk?, hia] at h
      simp at h
    obtain ⟨hb, hp⟩ := imm32Bytes P D n hok
    have hops : shs[k].ops' = (zPieces D n).map Prod.snd :=
      shapeOf_lopn_ops (ds := [.reg D]) (o := o) (ss := [.imm n]) _
        ((encodeLopn_movImm_eq _ _ _ hmo _ _).trans hb) hp (by rw [← hia]; exact hshk)
    have hlk : blockLeakA .doitm sa ((zPieces D n).map Prod.snd)
        = gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) := by
      rw [hAL.zmov]
      simp only [gW, hclK, hmv]
    exact ⟨_, hops, hpc', hc', hz', hnoadd hna _ _, hlk⟩
  rename_i hmv
  rw [tagAt_of_ne hmv] at hst
  split at hok
  · -- a slot carry arm
    rename_i c hcl
    have hia := classifyS_instr hcl
    have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) = (c.instr, MemTag.reg none) := by
      rw [← hia]
      cases c <;> simp (config := { decide := true }) [normA, tagA, SArm.instr]
    rw [hli] at hst
    have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
    have hz' : ∀ sa' : AState, isCondB (body[k + 1]'hkn).li_i = true →
        sa'.flags.zf.getD false = zf' := by
      intro sa' hcnd
      have hcm := hcondNext hcnd
      rw [← hia] at hcm
      cases c <;> simp [SArm.instr, classifyA_three_not_cmp] at hcm
    have hops := SArm.shape_ops hok (by rw [hia]; exact hshk)
    have hlk : blockLeakA .doitm sa (c.js P)
        = gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) := by
      rw [hAL.sarm c hok sa hc.sp]
      simp only [gW, hclK, hmv, hcl]
    cases c with
    | adcx D A S C =>
      have hok' := hok
      simp only [SArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
      obtain ⟨⟨⟨⟨⟨⟨⟨-, hAC⟩, hSC⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok'
      simp only [SArm.instr] at hia
      simp only [← hia] at hws hbk?
      have hwA : gpOk A = true → (s.reg.lvm A).1 = 64 := fun hA =>
        hws A (reg_reads (by simp)) hA (by simp [carryIns, hAC])
      have hwS : gpOk S = true → (s.reg.lvm S).1 = 64 := fun hS =>
        hws S (reg_reads (by simp)) hS (by simp [carryIns, hSC])
      obtain ⟨hc', hzz, hcyo⟩ := sim_sadcx P rsp D A S C hok sa s zf hc hwA hwS s' zf' hst
      have hcy' : CarryReq frame body (k + 1)
          (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' := by
        intro ii' O A' S' C' hb
        have hc2 := hF.carry (k + 1) hkn
        unfold carryPrevB at hc2
        rw [hb] at hc2
        simp only [ite_true, Nat.add_sub_cancel, hbk?] at hc2
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
          Nat.add_one_ne_zero, not_false_eq_true, true_and] at hc2
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, hDA⟩, hDS⟩, hDC⟩, hsa⟩, hss⟩, -⟩ := hc2
        exact hcyo hDA hDS hDC hsa hss
      exact ⟨_, hops, hpc', hc', hz' _, hcy', hlk⟩
    | adcxhi O A S C =>
      have hok' := hok
      simp only [SArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
      obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hAC⟩, hSC⟩, -⟩, -⟩, -⟩ := hok'
      simp only [SArm.instr] at hia
      simp only [← hia] at hws hbk?
      have hwA : gpOk A = true → (s.reg.lvm A).1 = 64 := fun hA =>
        hws A (reg_reads (by simp)) hA (by simp [carryIns, hAC])
      have hwS : gpOk S = true → (s.reg.lvm S).1 = 64 := fun hS =>
        hws S (reg_reads (by simp)) hS (by simp [carryIns, hSC])
      have hcyk := hcy ii O A S C hbk?
      obtain ⟨hc', -, -⟩ :=
        sim_sadcxhi P rsp O A S C hok sa s zf hc hwA hwS hcyk s' zf' hst
      have hcy' := hnoadd (fun ii' d a' s'' c' h => by
        rw [hbk?] at h
        simp at h) (aMachine.runBlock sa ((SArm.adcxhi O A S C).js P)) s'
      exact ⟨_, hops, hpc', hc', hz' _, hcy', hlk⟩
    | adcxc D A S C =>
      obtain ⟨hCs, -, -, -, -, -⟩ := adcxc_facts hok
      simp only [SArm.instr] at hia
      simp only [← hia] at hws hbk?
      have hwA : gpOk A = true → (s.reg.lvm A).1 = 64 := fun hA =>
        hws A (reg_reads (by simp)) hA (by simp [carryIns, ne_of_gp_slot hA hCs])
      have hwS : gpOk S = true → (s.reg.lvm S).1 = 64 := fun hS =>
        hws S (reg_reads (by simp)) hS (by simp [carryIns, ne_of_gp_slot hS hCs])
      obtain ⟨hc', hzz, hcyo⟩ := sim_sadcxc P rsp D A S C hok sa s zf hc hwA hwS s' zf' hst
      have hcy' : CarryReq frame body (k + 1)
          (aMachine.runBlock sa ((SArm.adcxc D A S C).js P)) s' := by
        intro ii' O A' S' C' hb
        have hc2 := hF.carry (k + 1) hkn
        unfold carryPrevB at hc2
        rw [hb] at hc2
        simp only [ite_true, Nat.add_sub_cancel, hbk?] at hc2
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
          Nat.add_one_ne_zero, not_false_eq_true, true_and] at hc2
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, hDA⟩, hDS⟩, -⟩, hsa⟩, hss⟩, hsc⟩ := hc2
        exact hcyo hDA hDS hsa hss hsc
      exact ⟨_, hops, hpc', hc', hz' _, hcy', hlk⟩
  rename_i hclS
  split at hok
  · -- a carry arm
    rename_i c hcl
    have hia := classifyC_instr hcl
    have hlk : blockLeakA .doitm sa c.js
        = gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) := by
      rw [hAL.carm]
      simp only [gW, hclK, hmv, hclS, hcl]
    cases c with
    | adcx D A S C =>
      simp only [CArm.instr] at hia
      simp only [← hia] at hst hws hshk hbk? hcondNext
      have hli : (normA (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]),
          tagA (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]))
          = ((CArm.adcx D A S C).instr, MemTag.reg none) := by
        simp (config := { decide := true }) [normA, tagA, CArm.instr]
      rw [hli] at hst
      have hok' := hok
      simp only [CArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
      obtain ⟨⟨⟨⟨⟨⟨-, hA⟩, hS⟩, -⟩, hAC⟩, hSC⟩, -⟩ := hok'
      have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
        (by simp [carryIns, hAC])
      have hwS : (s.reg.lvm S).1 = 64 := hws S (reg_reads (by simp)) hS
        (by simp [carryIns, hSC])
      obtain ⟨hc', hzz, hcyo⟩ := sim_adcx P rsp D A S C hok sa s zf hc hwA hwS s' zf' hst
      subst zf'
      have hpc' : s'.reg.lpc = k + 1 := by
        rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
      have hz' : isCondB (body[k + 1]'hkn).li_i = true →
          (aMachine.runBlock sa (CArm.adcx D A S C).js).flags.zf.getD false = zf := by
        intro hcnd
        have := hcondNext hcnd
        rw [classifyA_three_not_cmp] at this
        cases this
      have hcy' : CarryReq frame body (k + 1) (aMachine.runBlock sa (CArm.adcx D A S C).js)
          s' := by
        intro ii' O A' S' C' hb
        have hc2 := hF.carry (k + 1) hkn
        unfold carryPrevB at hc2
        rw [hb] at hc2
        simp only [ite_true, Nat.add_sub_cancel, hbk?] at hc2
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
          Nat.add_one_ne_zero, not_false_eq_true, true_and] at hc2
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, hDA⟩, hDS⟩, hDC⟩, -⟩, -⟩, -⟩ := hc2
        exact hcyo hDA hDS hDC
      have hops := CArm.shape_ops hok (by rw [show (CArm.adcx D A S C).instr
        = .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C] from rfl]; exact hshk)
      exact ⟨_, hops, hpc', hc', hz', hcy', hlk⟩
    | adcxhi O A S C =>
      simp only [CArm.instr] at hia
      simp only [← hia] at hst hws hshk hbk? hcondNext
      have hli : (normA (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]),
          tagA (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]))
          = ((CArm.adcxhi O A S C).instr, MemTag.reg none) := by
        simp (config := { decide := true }) [normA, tagA, CArm.instr]
      rw [hli] at hst
      have hok' := hok
      simp only [CArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
      obtain ⟨⟨⟨⟨⟨-, hA⟩, hS⟩, -⟩, hAC⟩, hSC⟩ := hok'
      have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
        (by simp [carryIns, hAC])
      have hwS : (s.reg.lvm S).1 = 64 := hws S (reg_reads (by simp)) hS
        (by simp [carryIns, hSC])
      have hcyk := hcy ii O A S C hbk?
      obtain ⟨hc', hzz, hfl⟩ :=
        sim_adcxhi P rsp O A S C hok sa s zf hc hwA hwS hcyk s' zf' hst
      subst zf'
      have hpc' : s'.reg.lpc = k + 1 := by
        rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
      have hz' : isCondB (body[k + 1]'hkn).li_i = true →
          (aMachine.runBlock sa (CArm.adcxhi O A S C).js).flags.zf.getD false = zf := by
        intro hcnd
        have := hcondNext hcnd
        rw [classifyA_three_not_cmp] at this
        cases this
      have hcy' := hnoadd (fun ii' d a' s'' c' h => by
        rw [hbk?] at h
        simp at h) (aMachine.runBlock sa (CArm.adcxhi O A S C).js) s'
      have hops := CArm.shape_ops hok (by rw [show (CArm.adcxhi O A S C).instr
        = .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C] from rfl]; exact hshk)
      exact ⟨_, hops, hpc', hc', hz', hcy', hlk⟩
  · rename_i hclC
    have hnotadd : ∀ ii' d a' s'' c', body[k]? ≠
        some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a', .reg s'', .reg c']⟩ := by
      intro ii' d a' s'' c' h
      rw [hbk?] at h
      simp only [Option.some.injEq, Linstr.mk.injEq] at h
      obtain ⟨-, h2⟩ := h
      rw [h2] at hclC
      simp [classifyC] at hclC
    split at hok
    · -- a cell arm
      rename_i m hclM
      have hia := classifyM_instr hclM
      have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) = (m.instr, MemTag.reg none) := by
        rw [← hia]
        cases m <;> simp (config := { decide := true }) [normA, tagA, MArm.instr]
      rw [hli] at hst
      have hgw : gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf)
          = instrLeakA frame (m.instr, MemTag.reg none) s := by
        rw [hGl, hli]
        simp only [gW, hclK, hmv, hclS, hclC, hclM]
      have hz' : ∀ sa' : AState, isCondB (body[k + 1]'hkn).li_i = true →
          sa'.flags.zf.getD false = zf' := by
        intro sa' hcnd
        have hcm := hcondNext hcnd
        rw [← hia, MArm.cmpArm_false hok] at hcm
        cases hcm
      have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
      cases m with
      | ldm D n B off =>
        have hok' := hok
        simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
        obtain ⟨⟨⟨hn, -⟩, hB⟩, -⟩ := hok'
        simp only [MArm.instr] at hia
        have hwB : (s.reg.lvm B).1 = 64 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
          hB (by rw [← hia]; simp [carryIns])
        have hsafeM : ∀ p, s.reg.getW B 64 = some p →
            Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off) := fun p hp =>
          hsafe.2.2.1 ii (.Lopn [.reg D] "LOAD:64" [.reg n]) D B off p
            (by rw [hget, ← hia]) (by simp [cellA?, hn]) hp
        obtain ⟨hc', -⟩ := sim_ldm P rsp D n B off hok sa s zf hc hwB hsafeM s' zf' hst
        have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
        exact ⟨_, hops, hpc', hc', hz' _, hnoadd hnotadd _ _,
          (hAL.ldm D n B off hok sa s hc hwB).trans hgw.symm⟩
      | stm n B off S =>
        have hok' := hok
        simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
        obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := hok'
        simp only [MArm.instr] at hia
        have hwB : (s.reg.lvm B).1 = 64 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
          hB (by rw [← hia]; simp [carryIns])
        have hwS : (s.reg.lvm S).1 = 64 := hws S (by rw [← hia]; exact reg_reads (by simp))
          hS (by rw [← hia]; simp [carryIns])
        obtain ⟨hc', -⟩ := sim_stm P rsp n B off S hok sa s zf hc hwB hwS s' zf' hst
        have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
        exact ⟨_, hops, hpc', hc', hz' _, hnoadd hnotadd _ _,
          (hAL.stm n B off S hok sa s hc hwB).trans hgw.symm⟩
      | stv n B off S =>
        have hok' := hok
        simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
        obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := hok'
        simp only [MArm.instr] at hia
        have hwB : (s.reg.lvm B).1 = 64 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
          hB (by rw [← hia]; simp [carryIns])
        have hwS : (s.reg.lvm S).1 = 64 := hws S (by rw [← hia]; exact reg_reads (by simp))
          hS (by rw [← hia]; simp [carryIns])
        obtain ⟨hc', -⟩ := sim_stv P rsp n B off S hok sa s zf hc hwB hwS s' zf' hst
        have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
        exact ⟨_, hops, hpc', hc', hz' _, hnoadd hnotadd _ _,
          (hAL.stv n B off S hok sa s hc hwB).trans hgw.symm⟩
      | ldv D n B off =>
        have hok' := hok
        simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
        obtain ⟨⟨⟨hn, hD⟩, hB⟩, -⟩ := hok'
        simp only [MArm.instr] at hia
        have hwB : (s.reg.lvm B).1 = 64 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
          hB (by rw [← hia]; simp [carryIns])
        have hsafeM : ∀ p, s.reg.getW B 64 = some p →
            Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off) := fun p hp =>
          hsafe.2.2.1 ii (.Lopn [.reg D] "MOV:64" [.reg n]) D B off p
            (by rw [hget, ← hia]) (by simp [cellA?, hn, cellParts?_gp hD]) hp
        obtain ⟨hc', -⟩ := sim_ldv P rsp D n B off hok sa s zf hc hwB hsafeM s' zf' hst
        have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
        exact ⟨_, hops, hpc', hc', hz' _, hnoadd hnotadd _ _,
          (hAL.ldv D n B off hok sa s hc hwB).trans hgw.symm⟩
    · rename_i hclM
      split at hok
      · -- an immediate store into a frame slot
        rename_i q v hclI
        have hia := classifyI_instr hclI
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
            = (.Lopn [.reg q] "MOV:64" [.imm v], MemTag.reg none) := by
          rw [hia]; simp (config := { decide := true }) [normA, tagA]
        rw [hli] at hst
        obtain ⟨hc', -⟩ := sim_sti P rsp q v hok sa s zf hc s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((iPieces P q v).map Prod.snd)).flags.zf.getD false
              = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hia] at hcm
          simp [classifyA, classify, cmpArmB] at hcm
        obtain ⟨hb, hp⟩ := iBytes P q v hok
        have hops : shs[k].ops' = (iPieces P q v).map Prod.snd :=
          shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
        have hlk : blockLeakA .doitm sa ((iPieces P q v).map Prod.snd)
            = gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) := by
          rw [hAL.imm q v hok sa hc.sp]
          simp only [gW, hclK, hmv, hclS, hclC, hclM, hclI]
        exact ⟨_, hops, hpc', hc', hz', hnoadd hnotadd _ _, hlk⟩
      rename_i hclI
      split at hok
      · -- a wide immediate
        rename_i D v hclL
        obtain ⟨hia, -⟩ := classifyL_instr hclL
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
            = (.Lopn [.reg D] "MOV:64" [.imm v], MemTag.reg none) := by
          rw [hia]; simp (config := { decide := true }) [normA, tagA]
        rw [hli] at hst
        obtain ⟨hc', -⟩ := sim_lmov P rsp D v hok sa s zf hc s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((lPieces D v).map Prod.snd)).flags.zf.getD false
              = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hia] at hcm
          simp [classifyA, classify, cmpArmB] at hcm
        obtain ⟨hb, hp⟩ := lBytes P D v hok
        have hops : shs[k].ops' = (lPieces D v).map Prod.snd :=
          shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
        have hlk : blockLeakA .doitm sa ((lPieces D v).map Prod.snd)
            = gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) := by
          rw [hAL.lmov]
          simp only [gW, hclK, hmv, hclS, hclC, hclM, hclI, hclL]
        exact ⟨_, hops, hpc', hc', hz', hnoadd hnotadd _ _, hlk⟩
      rename_i hclL
      split at hok
      · -- a register select
        rename_i D C A B hclV
        have hia := classifyV_instr hclV
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
            = (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], MemTag.reg none) := by
          rw [hia]; simp (config := { decide := true }) [normA, tagA]
        rw [hli] at hst
        have hgw : gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf)
            = fEv P rsp B ++ fEv P rsp A := by
          simp only [gW, hclK, hmv, hclS, hclC, hclM, hclI, hclL, hclV]
        rw [hia] at hws
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : ∀ sa' : AState, isCondB (body[k + 1]'hkn).li_i = true →
            sa'.flags.zf.getD false = zf' := by
          intro sa' hcnd
          have hcm := hcondNext hcnd
          rw [hia, classifyA_three_not_cmp] at hcm
          cases hcm
        rcases Bool.or_eq_true_iff.mp hok with hok | hok
        · have hok' := hok
          simp only [vOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hA⟩, hB⟩, -⟩, hAC⟩, hBC⟩ := hok'
          have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
            (by simp [carryIns, hAC])
          have hwB : (s.reg.lvm B).1 = 64 := hws B (reg_reads (by simp)) hB
            (by simp [carryIns, hBC])
          obtain ⟨hc', -⟩ := sim_cmov P rsp D C A B hok sa s zf hc hwA hwB s' zf' hst
          obtain ⟨hb, hp⟩ := vBytes P D C A B hok
          have hops : shs[k].ops' = (vPieces D C A B).map Prod.snd :=
            shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
          exact ⟨_, hops, hpc', hc', hz' _, hnoadd hnotadd _ _,
            (hAL.vreg D C A B hok sa).trans hgw.symm⟩
        rcases Bool.or_eq_true_iff.mp hok with hok | hok
        · -- a select with a slot true value
          have hok' := hok
          simp only [vtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hB⟩, -⟩, -⟩, -⟩, hBC⟩ := hok'
          have hwB : (s.reg.lvm B).1 = 64 := hws B (reg_reads (by simp)) hB
            (by simp [carryIns, hBC])
          obtain ⟨hc', -⟩ := sim_cmovSlot P rsp D C A B hok sa s zf hc hwB s' zf' hst
          obtain ⟨hb, hp⟩ := vtBytes P D C A B hok
          have hops : shs[k].ops' = (vtPieces P D C A B).map Prod.snd :=
            shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
          exact ⟨_, hops, hpc', hc', hz' _, hnoadd hnotadd _ _,
            (hAL.vt D C A B hok sa hc.sp).trans hgw.symm⟩
        · -- a select with a slot false value
          have hok' := hok
          simp only [vfOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨⟨hDg, -⟩, -⟩, -⟩, -⟩, -⟩, hAC⟩, -⟩ := hok'
          have hwA : gpOk A = true → (s.reg.lvm A).1 = 64 := fun hA =>
            hws A (reg_reads (by simp)) hA (by simp [carryIns, hAC])
          by_cases hAD : A = D
          · subst hAD
            obtain ⟨hc', -⟩ := sim_cmovSlotFE P rsp A C B hok sa s zf hc (hwA hDg) s' zf' hst
            obtain ⟨hb, hp⟩ := veBytes P A C B hok
            have hops : shs[k].ops' = (vePieces P A C B).map Prod.snd :=
              shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
            exact ⟨_, hops, hpc', hc', hz' _, hnoadd hnotadd _ _,
              (leak_cmovSlotFE P rsp A C B hok sa hc.sp).trans hgw.symm⟩
          obtain ⟨hc', -⟩ := sim_cmovSlotF P rsp D C A B hok hAD sa s zf hc hwA s' zf' hst
          obtain ⟨hb, hp⟩ := vfBytes P D C A B hok hAD
          have hops : shs[k].ops' = (vfPieces P D C A B).map Prod.snd :=
            shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
          exact ⟨_, hops, hpc', hc', hz' _, hnoadd hnotadd _ _,
            (leak_cmovSlotF P rsp D C A B hok sa hc.sp).trans hgw.symm⟩
      rename_i hclV
      split at hok
      · -- a materialised comparison
        rename_i n D A B hclE
        have hia := classifyE_instr hclE
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
            = (eInstr n D A B, MemTag.reg none) := by
          rw [hia]; cases n <;> simp (config := { decide := true }) [eInstr, eMnem, normA, tagA]
        rw [hli] at hst
        have hgw : gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) = [] := by
          simp only [gW, hclK, hmv, hclS, hclC, hclM, hclI, hclL, hclV, hclE]
        rw [hia] at hws
        have hok' := hok
        simp only [eOk, Bool.and_eq_true] at hok'
        obtain ⟨⟨-, hA⟩, hB⟩ := hok'
        have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
          (by simp [eInstr, carryIns])
        have hwB : (s.reg.lvm B).1 = 64 := hws B (reg_reads (by simp)) hB
          (by simp [eInstr, carryIns])
        obtain ⟨hc', -⟩ := sim_sete P rsp n D A B hok sa s zf hc hwA hwB s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((ePieces n D A B).map Prod.snd)).flags.zf.getD false
              = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hia] at hcm
          cases n <;> simp [eInstr, eMnem, classifyA, classify] at hcm <;>
            split_ifs at hcm <;> simp [cmpArmB] at hcm
        obtain ⟨hb, hp⟩ := eBytes P n D A B hok
        have hops : shs[k].ops' = (ePieces n D A B).map Prod.snd :=
          shapeOf_lopn_ops _ hb hp (by rw [hia] at hshk; exact hshk)
        exact ⟨_, hops, hpc', hc', hz', hnoadd hnotadd _ _,
          (hAL.sete n D A B sa).trans hgw.symm⟩
      rename_i hclE
      split at hok
      · -- a register-count shift
        rename_i l D A B hclX
        have hia := classifyX_instr hclX
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
            = (xInstr l D A B, MemTag.reg none) := by
          rw [hia]; cases l <;> simp (config := { decide := true }) [xInstr, xMnem, normA, tagA]
        rw [hli] at hst
        have hgw : gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) = [] := by
          simp only [gW, hclK, hmv, hclS, hclC, hclM, hclI, hclL, hclV, hclE, hclX]
        rw [hia] at hws
        have hok' := hok
        simp only [xOk, Bool.and_eq_true] at hok'
        obtain ⟨⟨-, hA⟩, hB⟩ := hok'
        have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
          (by simp [xInstr, carryIns])
        have hwB : (s.reg.lvm B).1 = 64 := hws B (reg_reads (by simp)) hB
          (by simp [xInstr, carryIns])
        obtain ⟨hc', -⟩ := sim_shrx P rsp l D A B hok sa s zf hc hwA hwB s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((xPieces l D A B).map Prod.snd)).flags.zf.getD false
              = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hia] at hcm
          cases l <;> simp [xInstr, xMnem, classifyA, classify] at hcm <;>
            split_ifs at hcm <;> simp [cmpArmB] at hcm
        obtain ⟨hb, hp⟩ := xBytes P l D A B hok
        have hops : shs[k].ops' = (xPieces l D A B).map Prod.snd :=
          shapeOf_lopn_ops _ hb hp (by rw [hia] at hshk; exact hshk)
        exact ⟨_, hops, hpc', hc', hz', hnoadd hnotadd _ _,
          (hAL.shrx l D A B sa).trans hgw.symm⟩
      rename_i hclX
      split at hok
      · -- a materialised comparison with an immediate
        rename_i n D A v hclEI
        have hia := classifyEI_instr hclEI
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
            = (eiInstr n D A v, MemTag.reg none) := by
          rw [hia]; cases n <;> simp (config := { decide := true }) [eiInstr, eMnem, normA, tagA]
        rw [hli] at hst
        have hgw : gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) = [] := by
          simp only [gW, hclK, hmv, hclS, hclC, hclM, hclI, hclL, hclV, hclE, hclX, hclEI]
        rw [hia] at hws
        have hok' := hok
        simp only [eiOk, Bool.and_eq_true] at hok'
        obtain ⟨⟨-, hA⟩, -⟩ := hok'
        have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
          (by simp [eiInstr, carryIns])
        obtain ⟨hc', -⟩ := sim_seteImm P rsp n D A v hok sa s zf hc hwA s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((eiPieces n D A v).map Prod.snd)).flags.zf.getD false
              = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hia] at hcm
          cases n <;> simp [eiInstr, eMnem, classifyA, classify] at hcm <;>
            split_ifs at hcm <;> simp [cmpArmB] at hcm
        obtain ⟨hb, hp⟩ := eiBytes P n D A v hok
        have hops : shs[k].ops' = (eiPieces n D A v).map Prod.snd :=
          shapeOf_lopn_ops _ hb hp (by rw [hia] at hshk; exact hshk)
        exact ⟨_, hops, hpc', hc', hz', hnoadd hnotadd _ _,
          (hAL.seteImm n D A v sa).trans hgw.symm⟩
      rename_i hclEI
      split at hok
      · -- an arithmetic right shift by an immediate
        rename_i D kc hclR
        have hia := classifyR_instr hclR
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
            = (rInstr D kc, MemTag.reg none) := by
          rw [hia]; simp (config := { decide := true }) [rInstr, normA, tagA]
        rw [hli] at hst
        have hgw : gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf) = [] := by
          simp only [gW, hclK, hmv, hclS, hclC, hclM, hclI, hclL, hclV, hclE, hclX, hclEI, hclR]
        rw [hia] at hws
        have hok' := hok
        simp only [rOk, Bool.and_eq_true] at hok'
        obtain ⟨⟨hD, -⟩, -⟩ := hok'
        have hwD : (s.reg.lvm D).1 = 64 := hws D (reg_reads (by simp)) hD
          (by simp [rInstr, carryIns])
        obtain ⟨hc', -⟩ := sim_sarImm P rsp D kc hok sa s zf hc hwD s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((rPieces D kc).map Prod.snd)).flags.zf.getD false
              = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hia] at hcm
          simp [rInstr, classifyA, classify] at hcm
          split_ifs at hcm <;> simp [cmpArmB] at hcm
        obtain ⟨hb, hp⟩ := rBytes_encode P D kc hok
        have hops : shs[k].ops' = (rPieces D kc).map Prod.snd :=
          shapeOf_lopn_ops _ hb hp (by rw [hia] at hshk; exact hshk)
        exact ⟨_, hops, hpc', hc', hz', hnoadd hnotadd _ _,
          (hAL.sarImm D kc sa).trans hgw.symm⟩
      rename_i hclR
      -- an arm of `DecodePrintedAddr`
      split at hok
      · rename_i ar hcl
        have hia := classifyA_instr hcl
        have hli := AArm.li_eq hok
        have hgw : gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf)
            = instrLeakA frame ar.li s ++ redLeak rsp ar := by
          have h1 : gW P rsp (.Lopn ds o ss) (stepLeakA frame body s zf)
              = stepLeakA frame body s zf ++ redLeak rsp ar := by
            simp only [gW, hclK, hmv, hclS, hclC, hclM, hclI, hclL, hclV, hclE, hclX, hclEI,
              hclR, hcl]
          rw [h1, hGl, ← hia, hli]
        rw [← hia, hli] at hst
        have hsafeA : ar.LoadSafe rsp s := by
          cases ar with
          | ldx D B' I =>
            intro p vi hp hvi
            exact hsafe.1 ii _ D B' I (by rw [hget, ← hia]) (by simp [AArm.instr, width_tag])
              p vi hp hvi
          | _ => trivial
        have hw : WideAt s ar.li.fst := by
          intro r hr hg
          have hfst : ar.li.fst = normA ar.instr := by rw [← hli]
          rw [hfst, readsI_normA, hia] at hr
          exact hws r hr hg (by rw [carryIns_of_classifyC hclC hclV]; simp)
        obtain ⟨hc', hzf'⟩ := AArm.simW P rsp ar hok sa s zf hc hw hsafeA s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa (ar.js P)).flags.zf.getD false = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hcl] at hcm
          exact hzf' (by simpa using hcm)
        have hops : shs[k].ops' = ar.js P := AArm.shape_ops hok (by rw [hia]; exact hshk)
        exact ⟨_, hops, hpc', hc', hz', hnoadd hnotadd _ _,
          (hAL.aarm ar hok sa s hc hw).trans hgw.symm⟩
      · cases hok

/-! ## 6. The traced simulation -/

/-- **The run on both machines, with carry chains and leakage.** From states related by
    `ACorrW` at instruction `k` of a body in `printedAddrWB`, with the machine zero flag equal
    to the flag at a conditional branch and the carry-out requirement, every terminating run
    of the address machine that is safe in the sense of `SafeWN`, with trace `ℓ` of
    `runALeakG (stepGW rsp body)`, is matched by a run with leakage `ℓ` of the decoded program
    from the index of `k`, under the regime `doitm`. -/
theorem run_simWL {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs)
    (rsp : BitVec 64) (hAL : ArmLeaksW (Params.ofBody body) rsp) (a b : JInstr 64)
    (hb : ∀ sa, opLeak .doitm sa b = []) :
    ∀ (fuel k : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool)
      (ℓ : List CTLeak),
      s.reg.lpc = k → (hk : k < body.length) → ACorrW rsp sa s →
      (isCondB (body[k]'hk).li_i = true → sa.flags.zf.getD false = zf) →
      CarryReq (frameP (Params.ofBody body) rsp) body k sa s →
      runALeakG (stepGW rsp body) (frameP (Params.ofBody body) rsp) body fuel s zf
        = some (t, ℓ) →
      RunSafe (frameP (Params.ofBody body) rsp) body (SafeWN rsp body) fuel s zf →
      ∃ sa', RunL .doitm (fun _ _ => True)
        (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret])) (posOf shs k) sa ℓ sa' := by
  set prog : List RInstr := .op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret])
  obtain ⟨hl, hsh⟩ := shapesOf_spec (Params.ofBody body) body shs hF.shapes
  have hskip : shs[shs.length - 1]'(by have := hF.pos; omega) = .one .skip := by
    have hsk := hsh (body.length - 1) (by have := hF.pos; omega) (by have := hF.pos; omega)
    have hlast := hF.last
    revert hsk hlast
    rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
    intro hsk hlast
    simp only at hlast hsk
    subst hlast
    simp only [shapeOf, Option.some.injEq] at hsk
    simp only [hl] at hsk ⊢
    exact hsk.symm
  obtain ⟨he1, he2⟩ := prog_end body shs a b (by have := hF.pos; omega) hskip
  rw [hl] at he1 he2
  have hhalt : ∀ (fuel : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool)
      (ℓ : List CTLeak), s.reg.lpc = body.length - 1 →
      runALeakG (stepGW rsp body) (frameP (Params.ofBody body) rsp) body fuel s zf
        = some (t, ℓ) →
      ∃ sa', RunL .doitm (fun _ _ => True) prog (posOf shs (body.length - 1)) sa ℓ sa' := by
    intro fuel sa s zf t ℓ hpc hrun
    have hh : haltedA body s = true := by
      unfold haltedA
      rw [hpc, List.getElem?_eq_getElem (by have := hF.pos; omega)]
      have := hF.last
      revert this
      rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
      intro h
      simp only at h
      subst h
      rfl
    rw [runALeakG_halt _ _ _ _ _ _ hh] at hrun
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hrun)
    have := RunL.op (r := .doitm) (ok := fun _ _ => True) (sa := sa) he1 trivial (.ret he2)
    rw [hb, List.append_nil] at this
    exact ⟨_, this⟩
  intro fuel
  induction fuel with
  | zero =>
    intro k sa s zf t ℓ hpc hk _ _ _ hrun _
    by_cases hkn : k + 1 < body.length
    · simp [runALeakG, haltedA_eq_falseW hF hpc hkn] at hrun
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt 0 sa s zf t ℓ hpc hrun
  | succ f ih =>
    intro k sa s zf t ℓ hpc hk hc hz hcy hrun hsafe
    by_cases hkn : k + 1 < body.length
    swap
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt (f + 1) sa s zf t ℓ hpc hrun
    rw [runALeakG_step _ _ _ _ _ _ (haltedA_eq_falseW hF hpc hkn)] at hrun
    have hok := hF.instr k hkn
    have hget : body[s.reg.lpc]? = some (body[k]'hk) := by
      rw [hpc]; exact List.getElem?_eq_getElem hk
    have hks : k < shs.length := by omega
    have hshk := hsh k hk hks
    obtain ⟨A, B, hsplit, hA⟩ := prog_split body shs a b k hks
    have hnoadd : (∀ ii d a s c, body[k]? ≠
        some ⟨ii, .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩) →
        ∀ sa s, CarryReq (frameP (Params.ofBody body) rsp) body (k + 1) sa s :=
      fun h sa s => no_carryReq hF hkn h _ sa s
    have hcondNext : isCondB (body[k + 1]'hkn).li_i = true →
        ((classifyA (body[k]'hk).li_i).any cmpArmB) = true := by
      intro hcnd
      have hc2 := hF.cond (k + 1) hkn
      unfold condPrevB at hc2
      rw [List.getElem?_eq_getElem hkn] at hc2
      revert hc2 hcnd
      rcases body[k + 1] with ⟨ii', li'⟩
      cases li' <;> simp [isCondB, List.getElem?_eq_getElem hk]
    rcases hbk : body[k]'hk with ⟨ii, li⟩
    rw [hbk] at hok hget hshk hz hcondNext
    simp only at hok hshk hz hcondNext
    have hbk? : body[k]? = some ⟨ii, li⟩ := by rw [body_get hk, hbk]
    cases li with
    | Lopn ds o ss =>
      cases hst : stepA (frameP (Params.ofBody body) rsp) body s zf with
      | none => simp [hst] at hrun
      | some p =>
        obtain ⟨s', zf'⟩ := p
        obtain ⟨js, hops, hpc', hc', hz', hcy', hlk⟩ :=
          lopn_stepW hF rsp hAL hk hkn hks hbk sa s zf hpc hc hcy hsafe.1 s' zf' hst
        have hG : stepGW rsp body s.reg.lpc
              (stepLeakA (frameP (Params.ofBody body) rsp) body s zf)
            = gW (Params.ofBody body) rsp (.Lopn ds o ss)
              (stepLeakA (frameP (Params.ofBody body) rsp) body s zf) := by
          simp only [stepGW, hget]
        rw [hst, Option.bind_some, hG] at hrun
        obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
        obtain ⟨-, rfl⟩ := Prod.mk.inj heq
        obtain ⟨sa', hR⟩ := ih (k + 1) _ s' zf' t' ℓ' hpc' hkn hc' hz' hcy' hrun'
          (hsafe.2 s' zf' hst)
        obtain ⟨hblk, hn⟩ := blkOf_lopn (body := body) (shs := shs) hshk
        have hprog : prog = A ++ js.map RInstr.op ++ B := by
          show RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]) = _
          rw [hsplit, hblk, hops]
        have hpos : posOf shs (k + 1) = A.length + js.length := by
          rw [posOf_succ shs k hks, hn, hops, hA]
        rw [hpos, aMachine_runBlock] at hR
        have h0 := runL_ops B js A sa hprog hR
        rw [hlk, hA] at h0
        exact ⟨sa', h0⟩
    | Llabel kd l =>
      have hstep : stepA (frameP (Params.ofBody body) rsp) body s zf
          = some (s.setLpc (k + 1), zf) := by
        unfold stepA
        rw [hget]
        simp only [hpc]
      have hleak : stepLeakA (frameP (Params.ofBody body) rsp) body s zf = [] := by
        simp only [stepLeakA, hget]
      have hG : stepGW rsp body s.reg.lpc [] = [] := by
        simp only [stepGW, hget]
      rw [hstep, Option.bind_some, hleak, hG] at hrun
      obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
      obtain ⟨-, rfl⟩ := Prod.mk.inj heq
      have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
        intro hcnd
        have := hcondNext hcnd
        simp [classifyA, cmpArmB, Option.any_map] at this
      have hcy' := hnoadd (fun ii' d a' s'' c' h => by rw [hbk?] at h; simp at h) sa
        (s.setLpc (k + 1))
      obtain ⟨sa', hR⟩ := ih (k + 1) sa (s.setLpc (k + 1)) zf t' ℓ' rfl hkn
        (acorrW_setLpc hc _) hz' hcy' hrun' (hsafe.2 _ _ hstep)
      refine ⟨sa', ?_⟩
      rw [posOf_succ shs k hks] at hR
      have hsk : shs[k] = .one .skip := by
        simp [shapeOf] at hshk; exact hshk.symm
      rw [hsk] at hR
      simpa [nOf] using hR
    | Lcond c l =>
      cases c with
      | reg cc =>
        simp only [instrOKWB, Bool.and_eq_true, Option.isSome_iff_exists] at hok
        obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hok
        obtain ⟨hpl, hlabp, -⟩ := labelAt_spec hp
        have hsk : shs[k] = .one (.jcc (ccNibble cc) l) := by
          simp [shapeOf] at hshk; exact hshk.symm
        have hj : prog[posOf shs k]? = some (.jcc (ccNibble cc) (posOf shs p)) := by
          show (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))[posOf shs k]? = _
          rw [hsplit, hsk, ← hA, List.append_assoc, List.getElem?_append_right (by omega)]
          simp [blkOf, hp]
        have hzf : sa.flags.zf.getD false = zf := hz rfl
        obtain ⟨cd, hcd, hcb⟩ := jcc_pol sa hpol
        rw [hzf] at hcb
        have hleak : stepLeakA (frameP (Params.ofBody body) rsp) body s zf
            = [.branch (zf == pol)] := by
          simp only [stepLeakA, hget, hpol]
        have hG : stepGW rsp body s.reg.lpc [CTLeak.branch (zf == pol)]
            = [.branch (zf == pol)] := by
          simp only [stepGW, hget]
        by_cases hzp : zf = pol
        · have hstep : stepA (frameP (Params.ofBody body) rsp) body s zf
              = some (s.setLpc p, zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hp]
          rw [hstep, Option.bind_some, hleak, hG] at hrun
          obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
          obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          have hz' : isCondB (body[p]'hpl).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            revert hlabp hcnd
            rcases body[p] with ⟨ii', li'⟩
            cases li' <;> simp [isCondB, isLabelB]
          have hcy' : CarryReq (frameP (Params.ofBody body) rsp) body p sa (s.setLpc p) := by
            intro ii' O A' S' C' hb
            rw [List.getElem?_eq_getElem hpl] at hb
            rw [Option.some.inj hb] at hlabp
            simp [isLabelB] at hlabp
          obtain ⟨sa', hR⟩ := ih p sa (s.setLpc p) zf t' ℓ' rfl hpl (acorrW_setLpc hc _) hz'
            hcy' hrun' (hsafe.2 _ _ hstep)
          have hb' : sa.view.condB cd = true := by rw [hcb, hzp]; simp
          refine ⟨sa', ?_⟩
          have := RunL.jcc (r := .doitm) (ok := fun _ _ => True) hj hcd
            (by rw [hb', ite_eq_left rfl]; exact hR)
          rw [hb'] at this
          simpa [hzp] using this
        · have hstep : stepA (frameP (Params.ofBody body) rsp) body s zf
              = some (s.setLpc (k + 1), zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hpc]
          rw [hstep, Option.bind_some, hleak, hG] at hrun
          obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
          obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            have := hcondNext hcnd
            simp [classifyA, cmpArmB, Option.any_map] at this
          have hcy' := hnoadd (fun ii' d a' s'' c' h => by rw [hbk?] at h; simp at h) sa
            (s.setLpc (k + 1))
          obtain ⟨sa', hR⟩ := ih (k + 1) sa (s.setLpc (k + 1)) zf t' ℓ' rfl hkn
            (acorrW_setLpc hc _) hz' hcy' hrun' (hsafe.2 _ _ hstep)
          rw [posOf_succ shs k hks, hsk] at hR
          have hb' : sa.view.condB cd = false := by
            rw [hcb]; cases zf <;> cases pol <;> simp_all
          refine ⟨sa', ?_⟩
          have := RunL.jcc (r := .doitm) (ok := fun _ _ => True) hj hcd
            (by rw [hb', ite_eq_right (by simp)]; simpa [nOf] using hR)
          rw [hb'] at this
          have hzb : (zf == pol) = false := by cases zf <;> cases pol <;> simp_all
          simpa [hzb] using this
      | _ => simp [instrOKWB] at hok
    | _ => simp [instrOKWB] at hok

/-- **The traced simulation of the class with carry chains from the events of its arms.**
    For a body in `printedAddrWB`, given the events `ArmLeaksW` of the decoded instructions of
    the arms at every frame address, the decoded bytes simulate the address machine with the
    step maps `stepGW`: `TracedSimW`. -/
theorem tracedSimW_of_armLeaks {body : Lcmd} (h : printedAddrWB body = true)
    (hAL : ∀ rsp, ArmLeaksW (Params.ofBody body) rsp) :
    TracedSimW (fun rsp => stepGW rsp body) body := by
  rintro sa s zf ⟨hpc, hent, hmem⟩ fuel t ℓ hrun hsafe
  obtain ⟨shs, hF⟩ := bodyFactsW_of h
  have hdec : decodableLcmd body = true := by
    simp only [printedAddrWB, Bool.and_eq_true] at h
    exact h.1.1.1.1.1
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  set P := Params.ofBody body
  set F := P.frame
  set rsp := frameRsp body sa with hrsp
  set prog : List RInstr := .op (leaFrame (-(Int.ofNat F)))
    :: (shs.flatMap (blkOf body shs) ++ [.op (leaFrame (Int.ofNat F)), .ret]) with hprog
  have hdecode : decodeLprog (encodeLfundefBytes body) = some prog := by
    refine decodeLprog_encodeLfundefBytes hdec ?_
    rw [fundefLayout, fundefItems,
      show shapesD P body = shs by
        rw [shapesD, show shapesOf P body = some shs from hF.shapes]; rfl]
    exact expectedFrom_fundef body shs hl.symm (targetsOK_ofW hF)
  obtain ⟨hl1, hm1⟩ := evalInstrA_leaFrame sa (-(Int.ofNat F))
  set sa1 := evalInstrA sa (leaFrame (-(Int.ofNat F)))
  have hc0 : ACorrW rsp sa1 s :=
    { regs := fun R hR => by
        rw [hl1, ite_eq_right (fun e => (gpFacts hR).physNe e)]
        exact Or.inl (hent R hR)
      sp := by rw [hl1, ite_eq_left rfl, hrsp]; rfl
      mem := fun x _ => by rw [hmem, hm1] }
  have hz0 : isCondB (body[0]'hF.pos).li_i = true → sa1.flags.zf.getD false = zf := by
    intro hcnd
    have hc := hF.cond 0 hF.pos
    revert hc hcnd
    unfold condPrevB
    rw [List.getElem?_eq_getElem hF.pos]
    rcases body[0]'hF.pos with ⟨ii, li⟩
    cases li <;> simp [isCondB]
  have hcy0 : CarryReq (frameP P rsp) body 0 sa1 s := by
    intro ii O A S C hb
    have hc := hF.carry 0 hF.pos
    unfold carryPrevB at hc
    rw [hb] at hc
    simp at hc
  have hI : NarrowInv body s := fun i _ _ r w hl => by
    rw [hpc, narrowIn_zero] at hl; cases hl
  obtain ⟨sa2, hR⟩ := run_simWL hF rsp (hAL rsp) _ _ (fun sa => opLeak_leaFrame sa _) fuel 0
    sa1 s zf t ℓ hpc hF.pos hc0 hz0 hcy0 hrun (runSafe_narrow fuel s zf hI hsafe)
  have hpos0 : posOf shs 0 = 1 := by simp [posOf]
  rw [hpos0] at hR
  have := RunL.op (r := .doitm) (ok := fun _ _ => True) (prog := prog) (pc := 0) (sa := sa)
    (i := leaFrame (-(Int.ofNat F))) rfl trivial hR
  rw [opLeak_leaFrame, List.nil_append] at this
  exact ⟨prog, sa2, hdecode, this⟩

/-! ## 7. The events of the arms -/

/-- A machine instruction that does not write the stack register keeps its value. -/
theorem evalInstrA_keep_rsp {rsp : BitVec 64} (sa : AState) (j : JInstr 64)
    (hj : "%rsp" ∉ dsts j) (h : sa.regs "%rsp" = rsp) : (evalInstrA sa j).regs "%rsp" = rsp := by
  rw [DecodedLsemStep.evalInstrA_regs_of_not_mem_dsts _ _ _ hj]
  exact h

/-- The carry constant and the 32-bit constant emit no event. -/
theorem leak_zmov (D : String) (n : Nat) (sa : AState) :
    blockLeakA .doitm sa ((zPieces D n).map Prod.snd) = [] := by
  simp [zPieces, blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
    X86Mnem.timing]

/-- The wide immediate emits no event. -/
theorem leak_lmov (D : String) (v : Nat) (sa : AState) :
    blockLeakA .doitm sa ((lPieces D v).map Prod.snd) = [] := by
  simp [lPieces, blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
    X86Mnem.timing]

/-- The materialised comparison on registers emits no event. -/
theorem leak_sete (n : Bool) (D A B : String) (sa : AState) :
    blockLeakA .doitm sa ((ePieces n D A B).map Prod.snd) = [] := by
  cases n <;>
    simp [ePieces, blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
      X86Mnem.timing]

/-- The materialised comparison with an immediate emits no event. -/
theorem leak_seteImm (n : Bool) (D A : String) (v : Nat) (sa : AState) :
    blockLeakA .doitm sa ((eiPieces n D A v).map Prod.snd) = [] := by
  cases n <;>
    simp [eiPieces, blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
      X86Mnem.timing]

/-- The register-count shift `shlx`/`shrx` emits no event. -/
theorem leak_shrx (l : Bool) (D A B : String) (sa : AState) :
    blockLeakA .doitm sa ((xPieces l D A B).map Prod.snd) = [] := by
  cases l <;>
    simp [xPieces, xJ, blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
      X86Mnem.timing]

/-- The arithmetic right shift by an immediate `sar $k` emits no event. -/
theorem leak_sarImm (D : String) (k : Nat) (sa : AState) :
    blockLeakA .doitm sa ((rPieces D k).map Prod.snd) = [] := by
  simp [rPieces, blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
    X86Mnem.timing]

/-- A carry arm on registers emits no event. -/
theorem leak_carm (c : CArm) (sa : AState) : blockLeakA .doitm sa c.js = [] := by
  cases c with
  | adcx D A S C =>
    by_cases h : A = D <;>
      simp [CArm.js, CArm.pieces, h, blockLeakA, opLeak, instrLeak, JInstr.mnem,
        DoitRegime.leaksOperands, X86Mnem.timing]
  | adcxhi O A S C =>
    simp [CArm.js, CArm.pieces, blockLeakA, opLeak, instrLeak, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing]

/-- The register select emits no event. -/
theorem leak_vreg (P : Params) (rsp : BitVec 64) (D C A B : String)
    (h : vOk D C A B = true) (sa : AState) :
    blockLeakA .doitm sa ((vPieces D C A B).map Prod.snd) = fEv P rsp B ++ fEv P rsp A := by
  simp only [vOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hA⟩, hB⟩, -⟩, -⟩, -⟩ := h
  rw [fEv_gp hA, fEv_gp hB]
  by_cases hAD : A = D <;> by_cases hBD : B = D <;>
    simp [vPieces, hAD, hBD, blockLeakA, opLeak, instrLeak, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing]

/-- The select with a slot true value accesses the frame word of the true value. -/
theorem leak_vt (P : Params) (rsp : BitVec 64) (D C A B : String)
    (h : vtOk P D C A B = true) (sa : AState) (hsp : sa.regs "%rsp" = rsp) :
    blockLeakA .doitm sa ((vtPieces P D C A B).map Prod.snd) = fEv P rsp B ++ fEv P rsp A := by
  simp only [vtOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, -⟩, hB⟩, hAs⟩, hAk⟩, -⟩, -⟩ := h
  have hRsp : "%rsp" ≠ phys D := fun e => (gpFacts hD).physNe e.symm
  rw [fEv_gp hB, fEv_slot hAk hAs]
  have hsp1 : ∀ sa1 : AState, sa1.regs "%rsp" = rsp →
      (evalInstrA sa1 (.test (phys C) (.reg (phys C)))).regs "%rsp" = rsp := fun sa1 h1 =>
    evalInstrA_keep_rsp sa1 _ (by simp [dsts]) h1
  have hsp2 : (evalInstrA sa (.mov (phys D) (.reg (phys B)))).regs "%rsp" = rsp :=
    evalInstrA_keep_rsp sa _ (by simp [dsts, hRsp]) hsp
  by_cases hBD : B = D
  · simp [vtPieces, hBD, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, evA, hsp1 sa hsp]
  · simp [vtPieces, hBD, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing, evA, hsp1 _ hsp2]

/-- The cell load accesses the address of the cell. -/
theorem leak_ldm (P : Params) (rsp : BitVec 64) (D n B : String) (off : Nat)
    (h : (MArm.ldm D n B off).ok = true) (sa : AState) (s : LstateA) (hc : ACorrW rsp sa s)
    (hw : (s.reg.lvm B).1 = 64) :
    blockLeakA .doitm sa (MArm.ldm D n B off).js
      = instrLeakA (frameP P rsp) ((MArm.ldm D n B off).instr, .reg none) s := by
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, -⟩, hB⟩, -⟩ := h
  rw [show (MArm.ldm D n B off).instr = .Lopn [.reg D] "LOAD:64" [.reg n] from rfl,
    instrLeakA_ldm _ hn (hc.wide hB hw)]
  simp [MArm.js, MArm.pieces, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
    DoitRegime.leaksOperands, X86Mnem.timing, evA, BitVec.ofInt_natCast]

/-- The cell store accesses the address of the cell. -/
theorem leak_stm (P : Params) (rsp : BitVec 64) (n B : String) (off : Nat) (S : String)
    (h : (MArm.stm n B off S).ok = true) (sa : AState) (s : LstateA) (hc : ACorrW rsp sa s)
    (hw : (s.reg.lvm B).1 = 64) :
    blockLeakA .doitm sa (MArm.stm n B off S).js
      = instrLeakA (frameP P rsp) ((MArm.stm n B off S).instr, .reg none) s := by
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, -⟩, hB⟩, -⟩ := h
  rw [show (MArm.stm n B off S).instr = .Lopn [.reg n] "STORE:64" [.reg S] from rfl,
    instrLeakA_stm _ hn (hc.wide hB hw)]
  simp [MArm.js, MArm.pieces, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
    DoitRegime.leaksOperands, X86Mnem.timing, evA, BitVec.ofInt_natCast]

/-- The move into a cell accesses the address of the cell. -/
theorem leak_stv (P : Params) (rsp : BitVec 64) (n B : String) (off : Nat) (S : String)
    (h : (MArm.stv n B off S).ok = true) (sa : AState) (s : LstateA) (hc : ACorrW rsp sa s)
    (hw : (s.reg.lvm B).1 = 64) :
    blockLeakA .doitm sa (MArm.stv n B off S).js
      = instrLeakA (frameP P rsp) ((MArm.stv n B off S).instr, .reg none) s := by
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := h
  rw [show (MArm.stv n B off S).instr = .Lopn [.reg n] "MOV:64" [.reg S] from rfl,
    instrLeakA_stv _ hn (hc.wide hB hw)]
  simp [MArm.js, MArm.pieces, blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem,
    DoitRegime.leaksOperands, X86Mnem.timing, evA, BitVec.ofInt_natCast]

/-- The move out of a cell accesses the address of the cell. -/
theorem leak_ldv (P : Params) (rsp : BitVec 64) (D n B : String) (off : Nat)
    (h : (MArm.ldv D n B off).ok = true) (sa : AState) (s : LstateA) (hc : ACorrW rsp sa s)
    (hw : (s.reg.lvm B).1 = 64) :
    blockLeakA .doitm sa (MArm.ldv D n B off).js
      = instrLeakA (frameP P rsp) ((MArm.ldv D n B off).instr, .reg none) s := by
  have hok : (MArm.ldm D n B off).ok = true := h
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hD⟩, hB⟩, -⟩ := h
  have hcl : cellA? (.Lopn [.reg D] "MOV:64" [.reg n]) = some (.ld D B off) := by
    simp [cellA?, hn, cellParts?_gp hD]
  have e : instrLeakA (frameP P rsp) ((MArm.ldv D n B off).instr, .reg none) s
      = instrLeakA (frameP P rsp) ((MArm.ldm D n B off).instr, .reg none) s := by
    rw [show (MArm.ldv D n B off).instr = .Lopn [.reg D] "MOV:64" [.reg n] from rfl,
      show (MArm.ldm D n B off).instr = .Lopn [.reg D] "LOAD:64" [.reg n] from rfl,
      instrLeakA_ldm _ hn (hc.wide hB hw), instrLeakA_cellLd _ hcl (hc.wide hB hw)]
  rw [e]
  exact leak_ldm P rsp D n B off hok sa s hc hw

/-- **The events of an arm of `DecodePrintedAddr` on the correspondence with narrow
    names**: `AArm.leak` from `ACorrW`, for an arm that reads its names at width `64`. -/
theorem leak_aarmW (P : Params) (rsp : BitVec 64) (a : AArm) (h : a.ok P = true)
    (sa : AState) (s : LstateA) (hc : ACorrW rsp sa s) (hw : WideAt s a.li.fst) :
    blockLeakA .doitm sa (a.js P) = instrLeakA (frameP P rsp) a.li s ++ redLeak rsp a := by
  rw [AArm.leak P rsp a h sa (widenS sa s) hc.widen]
  congr 1
  cases a with
  | ldx D B I =>
    have hB : readsI (AArm.ldx D B I).li.fst B := by
      show readsI (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) B
      exact base_reads (List.mem_singleton_self _)
    have hI : readsI (AArm.ldx D B I).li.fst I := by
      show readsI (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) I
      exact idx_reads (List.mem_singleton_self _)
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨-, hBg⟩, hIg⟩, -⟩ := h
    rw [show (AArm.ldx D B I).li = (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8], .load 64 0)
      from rfl, instrLeakA_ldx _ D B I 8 64 0 (hc.widen.regs B hBg) (hc.widen.regs I hIg),
      instrLeakA_ldx _ D B I 8 64 0 (hc.wide hBg (hw B hB hBg)) (hc.wide hIg (hw I hI hIg))]
  | stx d B I V =>
    have hB : readsI (AArm.stx d B I V).li.fst B := by
      show readsI (.Lopn [.reg d] "STOREIDX" [.arrIdx B I 8, .reg V]) B
      exact base_reads (List.Mem.head _)
    have hI : readsI (AArm.stx d B I V).li.fst I := by
      show readsI (.Lopn [.reg d] "STOREIDX" [.arrIdx B I 8, .reg V]) I
      exact idx_reads (List.Mem.head _)
    simp only [AArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hBg, hIg⟩, -⟩, -⟩ := h
    rw [show (AArm.stx d B I V).li = (.Lopn [.reg d] "STOREIDX" [.arrIdx B I 8, .reg V],
      .store 64 0) from rfl,
      instrLeakA_stx _ d B I V 8 64 0 (hc.widen.regs B hBg) (hc.widen.regs I hIg),
      instrLeakA_stx _ d B I V 8 64 0 (hc.wide hBg (hw B hB hBg)) (hc.wide hIg (hw I hI hIg))]
  | reg a =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    simp only [AArm.li, AArm.instr]
    exact instrLeakA_reg_indep (regArm_cell h.1.1 h.1.2) none _ _
  | st m q S =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
      simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at h; exact h.2.symm
    have hcell : cellA? (AArm.st m q S).instr = none := by
      rcases hm' with rfl | rfl <;>
        simp [AArm.instr, cellA?, cellParts?_of_spillOff h.1.1.2, cellParts?_gp h.1.1.1.1]
    simp only [AArm.li]
    exact instrLeakA_reg_indep hcell none _ _
  | ld m D q =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
      simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at h; exact h.2.symm
    have hcell : cellA? (AArm.ld m D q).instr = none := by
      rcases hm' with rfl | rfl <;>
        simp [AArm.instr, cellA?, cellParts?_of_spillOff h.1.1.1.2, cellParts?_gp h.1.1.1.1.1]
    simp only [AArm.li]
    exact instrLeakA_reg_indep hcell none _ _
  | cmpR c r =>
    simp only [AArm.li]; exact instrLeakA_reg_indep (by simp [AArm.instr, cellA?]) none _ _
  | cmpI c k =>
    simp only [AArm.li]; exact instrLeakA_reg_indep (by simp [AArm.instr, cellA?]) none _ _
  | cmpM c q =>
    simp only [AArm.li]; exact instrLeakA_reg_indep (by simp [AArm.instr, cellA?]) none _ _
  | mul D S =>
    simp only [AArm.li]; exact instrLeakA_reg_indep (by simp [AArm.instr, cellA?]) none _ _
  | mulxS H S =>
    simp only [AArm.li]; exact instrLeakA_reg_indep (by simp [cellA?]) none _ _
  | mulx L H S =>
    simp only [AArm.li]; exact instrLeakA_reg_indep (by simp [cellA?]) none _ _
  | zero B n =>
    have hB : readsI (AArm.zero B n).li.fst B := reg_reads (by simp)
    have hg := getW_widen (sa := sa) hw hB 64
    simp only [AArm.li] at hg ⊢
    simp only [instrLeakA, zeroArrA?, ite_true, hg]
  | simm d B V k =>
    have hB : readsI (AArm.simm d B V k).li.fst B := reg_reads (by simp)
    have hg := getW_widen (sa := sa) hw hB 64
    simp only [AArm.li] at hg ⊢
    simp only [instrLeakA, storeImmStruct?, ite_true, hg]
  | leaF d q =>
    have hq : X86Backend.LprogAsmPrinter.faB q = true := by
      simp only [AArm.ok, Bool.and_eq_true] at h; exact h.1.2
    simp only [AArm.li]
    exact instrLeakA_reg_indep (by simp [AArm.instr, cellA?, cellParts?_of_faB hq]) none _ _

/-- The copy of an operand into an accumulator other than the stack register keeps the stack
    register. -/
theorem rsp_sMv (P : Params) (rsp : BitVec 64) (D A : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) (hne : "%rsp" ≠ SailX86Decoder.regName acc) :
    (aMachine.runBlock sa ((sMv P D A acc).map Prod.snd)).regs "%rsp" = rsp := by
  by_cases hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ acc = gpNumU D)
  · rw [(run_sMv P rsp D A acc sa hsp hlay).1, ite_eq_right hne, hsp]
  · simp only [not_or, Bool.not_eq_true, not_not] at hlay
    obtain ⟨hAs, rfl, hacc⟩ := hlay
    have he : sMv P A A acc = [] := by simp [sMv, hAs, hacc]
    rw [he]
    exact hsp

/-- The add of an operand into an accumulator other than the stack register keeps the stack
    register. -/
theorem rsp_sAd (P : Params) (rsp : BitVec 64) (S : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) (hne : "%rsp" ≠ SailX86Decoder.regName acc) :
    (aMachine.runBlock sa ((sAd P S acc).map Prod.snd)).regs "%rsp" = rsp := by
  rw [(run_sAd P rsp S acc sa hsp).1, ite_eq_right hne, hsp]

/-- **The events of the decoded instructions of a carry arm with frame-slot operands**:
    `sLeakW`. -/
theorem leak_sarm (P : Params) (rsp : BitVec 64) (c : SArm) (h : c.ok P = true) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) : blockLeakA .doitm sa (c.js P) = sLeakW P rsp c := by
  cases c with
  | adcxc D A S C => exact SArm.leak_adcxc P rsp D A S C h sa hsp
  | adcxhi O A S C =>
    simp [SArm.js, SArm.pieces, sLeakW, blockLeakA, opLeak, instrLeak, JInstr.mnem,
      DoitRegime.leaksOperands, X86Mnem.timing]
  | adcx D A S C =>
    have h' := h
    simp only [SArm.ok, Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨⟨⟨⟨hC, -⟩, -⟩, hD⟩, hA⟩, hS⟩, -⟩, -⟩ := h'
    have hbt : ∀ sa1 : AState, opLeak .doitm sa1 (.bt (phys C) (.imm 0)) = [] := fun sa1 => by
      simp [opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]
    have hbtsp : ∀ sa1 : AState, sa1.regs "%rsp" = rsp →
        (evalInstrA sa1 (.bt (phys C) (.imm 0))).regs "%rsp" = rsp := fun sa1 h1 =>
      evalInstrA_keep_rsp sa1 _ (by simp [dsts]) h1
    by_cases hDs : isSpillOrQsave D = true
    · obtain ⟨hRg, -, -, -⟩ := scratchS_spec A S C
      have hRsp : "%rsp" ≠ SailX86Decoder.regName (gpNumU (scratchS A S C)) := fun e =>
        (gpFacts hRg).physNe e.symm
      have hjs : (SArm.adcx D A S C).js P
          = [.bt (phys C) (.imm 0), .storeMem "%rsp" cmovRedZone
              (.reg (SailX86Decoder.regName (gpNumU (scratchS A S C))))]
            ++ ((sMv P D A (gpNumU (scratchS A S C))).map Prod.snd
            ++ ((sAd P S (gpNumU (scratchS A S C))).map Prod.snd
            ++ [.storeMem "%rsp" (slotOff P D)
                  (.reg (SailX86Decoder.regName (gpNumU (scratchS A S C)))),
                .loadMem (SailX86Decoder.regName (gpNumU (scratchS A S C))) "%rsp"
                  cmovRedZone])) := by
        simp [SArm.js, SArm.pieces, hDs, List.map_append]
      obtain ⟨r2, -⟩ := evalInstrA_storeMem_eq (evalInstrA sa (.bt (phys C) (.imm 0))) "%rsp"
        (SailX86Decoder.regName (gpNumU (scratchS A S C))) cmovRedZone
      have hsp2 : (aMachine.runBlock sa [.bt (phys C) (.imm 0), .storeMem "%rsp" cmovRedZone
          (.reg (SailX86Decoder.regName (gpNumU (scratchS A S C))))]).regs "%rsp" = rsp := by
        show (evalInstrA (evalInstrA sa (.bt (phys C) (.imm 0))) _).regs "%rsp" = rsp
        rw [r2, hbtsp sa hsp]
      have hsp3 := rsp_sMv P rsp D A (gpNumU (scratchS A S C)) _ hsp2 hRsp
      have hsp4 := rsp_sAd P rsp S (gpNumU (scratchS A S C)) _ hsp3 hRsp
      obtain ⟨r5, -⟩ := evalInstrA_storeMem_eq
        (aMachine.runBlock (aMachine.runBlock (aMachine.runBlock sa
          [.bt (phys C) (.imm 0), .storeMem "%rsp" cmovRedZone
            (.reg (SailX86Decoder.regName (gpNumU (scratchS A S C))))])
          ((sMv P D A (gpNumU (scratchS A S C))).map Prod.snd))
          ((sAd P S (gpNumU (scratchS A S C))).map Prod.snd)) "%rsp"
        (SailX86Decoder.regName (gpNumU (scratchS A S C))) (slotOff P D)
      rw [hjs, blockLeakA_append, blockLeakA_append, blockLeakA_append,
        leak_sMv P rsp D A _ _ hsp2 hA, leak_sAd P rsp S _ _ hsp3 hS]
      simp only [blockLeakA, opLeak_storeRsp, opLeak_loadRsp, hbt, r5, hsp4, hbtsp sa hsp,
        sLeakW, hDs, ite_true, fEv_slot hD hDs, List.nil_append, List.append_nil]
      simp [redW]
    · have hDg : gpOk D = true := kOk_gp hD (by simpa using hDs)
      have hRsp : "%rsp" ≠ SailX86Decoder.regName (gpNumU D) := fun e =>
        (gpFacts hDg).physNe e.symm
      have hjs : (SArm.adcx D A S C).js P
          = (sMv P D A (gpNumU D)).map Prod.snd
            ++ ([.bt (phys C) (.imm 0)] ++ (sAd P S (gpNumU D)).map Prod.snd) := by
        simp [SArm.js, SArm.pieces, hDs, List.map_append]
      have hsp1 := rsp_sMv P rsp D A (gpNumU D) sa hsp hRsp
      have hsp2 : (aMachine.runBlock (aMachine.runBlock sa
          ((sMv P D A (gpNumU D)).map Prod.snd)) [.bt (phys C) (.imm 0)]).regs "%rsp" = rsp :=
        hbtsp _ hsp1
      rw [hjs, blockLeakA_append, blockLeakA_append, leak_sMv P rsp D A _ sa hsp hA,
        leak_sAd P rsp S _ _ hsp2 hS]
      simp [blockLeakA, hbt, sLeakW, hDs]

/-- The register of `RAX` is not the stack register. -/
theorem rsp_ne_rax : "%rsp" ≠ phys "RAX" := fun e =>
  (gpFacts (r := "RAX") (by decide)).physNe e.symm

/-- The save of a register `R` other than the stack register in the red-zone word, the move
    of an immediate into `R`, the store of `R` at `off` below the stack register and the
    restore of `R` access the red-zone word, the word at `off` and the red-zone word. -/
theorem leak_stiWide (rsp : BitVec 64) (R : String) (v : Nat) (off : Int)
    (hR : "%rsp" ≠ R) (sa : AState) (hsp : sa.regs "%rsp" = rsp) :
    blockLeakA .doitm sa [.storeMem "%rsp" cmovRedZone (.reg R), .mov R (.imm v),
        .storeMem "%rsp" off (.reg R), .loadMem R "%rsp" cmovRedZone]
      = [evA (redW rsp), evA (rsp + BitVec.ofInt 64 off), evA (redW rsp)] := by
  obtain ⟨r1, -⟩ := evalInstrA_storeMem_eq sa "%rsp" R cmovRedZone
  obtain ⟨r2, -⟩ := evalInstrA_movImm_eq (evalInstrA sa (.storeMem "%rsp" cmovRedZone (.reg R)))
    R v
  have hsp2 : (evalInstrA (evalInstrA sa (.storeMem "%rsp" cmovRedZone (.reg R)))
      (.mov R (.imm v))).regs "%rsp" = rsp := by
    rw [r2, ite_eq_right hR, r1, hsp]
  obtain ⟨r3, -⟩ := evalInstrA_storeMem_eq
    (evalInstrA (evalInstrA sa (.storeMem "%rsp" cmovRedZone (.reg R))) (.mov R (.imm v)))
    "%rsp" R off
  have hmv : ∀ sa1 : AState, opLeak .doitm sa1 (.mov R (.imm v)) = [] := fun sa1 => by
    simp [opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]
  simp only [blockLeakA, opLeak_storeRsp, opLeak_loadRsp, hmv, r3, hsp, hsp2, List.nil_append,
    List.append_nil, redW, List.cons_append]

/-- **The events of the decoded instructions of an immediate store into a frame slot**:
    `iLeakW`. -/
theorem leak_imm (P : Params) (rsp : BitVec 64) (q : String) (v : Nat)
    (_h : iOk P q v = true) (sa : AState) (hsp : sa.regs "%rsp" = rsp) :
    blockLeakA .doitm sa ((iPieces P q v).map Prod.snd) = iLeakW P rsp q v := by
  unfold iPieces iLeakW
  split
  · simp [blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem, DoitRegime.leaksOperands,
      X86Mnem.timing, evA, hsp]
  · exact leak_stiWide rsp (phys "RAX") v (slotOff P q) rsp_ne_rax sa hsp

/-- **The events of the decoded instructions of every arm** of the class with carry chains,
    at every parameters and frame address. -/
theorem armLeaksW (P : Params) (rsp : BitVec 64) : ArmLeaksW P rsp where
  zmov := leak_zmov
  sarm := leak_sarm P rsp
  carm := leak_carm
  ldm := leak_ldm P rsp
  stm := leak_stm P rsp
  stv := leak_stv P rsp
  ldv := leak_ldv P rsp
  imm := leak_imm P rsp
  lmov := leak_lmov
  vreg := leak_vreg P rsp
  vt := leak_vt P rsp
  sete := leak_sete
  seteImm := leak_seteImm
  shrx := leak_shrx
  sarImm := leak_sarImm
  aarm := leak_aarmW P rsp

/-! ## 8. The lengths of the step events and the decoded bytes -/

/-- The events of a register-tagged instruction that accesses no cell have a length
    independent of the state. -/
theorem instrLeakA_length_reg {frame : String → Option (BitVec 64)} {x : LinstrR}
    {tg : MemTag} {y : LinstrR} {t : Option Nat} (he : (x, tg) = (y, MemTag.reg t))
    (hcell : cellA? y = none) (s₁ s₂ : LstateA) :
    (instrLeakA frame (x, tg) s₁).length = (instrLeakA frame (x, tg) s₂).length := by
  rw [he, instrLeakA_reg_indep hcell t s₁ s₂]

/-- **The step event lengths of a body in `printedAddrWB` are functions of the program
    counter.** -/
theorem stepLenDetW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs)
    (frame : String → Option (BitVec 64)) : StepLenDet frame body := by
  intro s₁ s₂ zf₁ zf₂ b₁ b₂ hpc h₁ h₂
  unfold stepA at h₁ h₂
  unfold stepLeakA
  rw [hpc] at h₁ ⊢
  cases hb : body[s₂.reg.lpc]? with
  | none => rfl
  | some i =>
    obtain ⟨ii, li⟩ := i
    rw [hb] at h₁ h₂
    cases li with
    | Lopn ds o ss =>
      simp only at h₁ h₂ ⊢
      obtain ⟨hk, hbk⟩ := List.getElem?_eq_some_iff.mp hb
      have hkn : s₂.reg.lpc + 1 < body.length := by
        by_contra hc
        have hlast := hF.last
        have he : s₂.reg.lpc = body.length - 1 := by omega
        simp only [he] at hbk
        rw [hbk] at hlast
        cases hlast
      have hok := hF.instr _ hkn
      rw [hbk] at hok
      simp only [instrOKWB] at hok
      split at hok
      · rename_i D A m w' hclK
        obtain ⟨o', hia, hm, hw⟩ := classifyK_spec hclK
        simp only [LinstrR.Lopn.injEq] at hia
        obtain ⟨rfl, rfl, rfl⟩ := hia
        obtain ⟨h1, h2, -, -⟩ := castTagW_ne hw
        obtain ⟨h3, h4⟩ := castTagW_ne_arr hw
        refine instrLeakA_length_reg (y := .Lopn [.reg D] o [.reg A]) (t := castTagW o)
          (by rw [normA_castW hw, tagA_lopn_of_caret_free h1 h2 h3 h4 (castTagW_caret_free hw)])
          ?_ s₁ s₂
        have hl : o ≠ "LOAD:64" := by rintro rfl; simp [castTagW] at hw
        have hs : o ≠ "STORE:64" := by rintro rfl; simp [castTagW] at hw
        have hle : o ≠ "LEA:64" := by rintro rfl; simp [castTagW] at hw
        have hmo : o ≠ "MOV:64" := by rintro rfl; simp [castTagW] at hw
        simp [cellA?, LprogAsmPrinter.untagCaret_of_caret_free (castTagW_caret_free hw), hl, hs,
          hle, hmo]
      split at hok
      · rename_i D n hmv
        have hmo : JasminLsemCast.isMovImmMnem o = true := by
          unfold movImmStruct? at hmv
          split at hmv
          · rename_i heq
            simp only [LinstrR.Lopn.injEq] at heq
            obtain ⟨-, rfl, -⟩ := heq
            split at hmv
            · assumption
            · cases hmv
          · cases hmv
        have hia : LinstrR.Lopn ds o ss = .Lopn [.reg D] o [.imm n] := by
          obtain ⟨o', h'⟩ := JasminLsemCast.movImmStruct?_spec hmv
          rw [h']
          simp only [LinstrR.Lopn.injEq] at h'
          rw [h'.2.1]
        rw [hia]
        exact instrLeakA_length_reg (y := .Lopn [.reg D] "MOV" [.imm n]) (t := none)
          (by rw [ImageAddrSimW.normA_movImm hmo, tagA_movImm hmo])
          (by simp [cellA?]) s₁ s₂
      rename_i hmv
      rw [tagAt_of_ne hmv] at h₁ h₂
      split at hok
      · rename_i c hcl
        have hia := classifyS_instr hcl
        refine instrLeakA_length_reg (y := c.instr) (t := none) ?_ ?_ s₁ s₂
        · rw [← hia]
          cases c <;> simp (config := { decide := true }) [normA, tagA, SArm.instr]
        · cases c <;> simp [SArm.instr, cellA?]
      split at hok
      · rename_i c hcl
        have hia := classifyC_instr hcl
        refine instrLeakA_length_reg (y := c.instr) (t := none) ?_ ?_ s₁ s₂
        · rw [← hia]
          cases c <;> simp (config := { decide := true }) [normA, tagA, CArm.instr]
        · cases c <;> simp [CArm.instr, cellA?]
      split at hok
      · rename_i m hclM
        have hia := classifyM_instr hclM
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
            = (m.instr, MemTag.reg none) := by
          rw [← hia]
          cases m <;> simp (config := { decide := true }) [normA, tagA, MArm.instr]
        rw [hli] at h₁ h₂ ⊢
        cases m with
        | ldm D n B off =>
          simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨⟨⟨hn, -⟩, -⟩, -⟩ := hok
          cases hB₁ : s₁.reg.getW B 64 with
          | none => simp [MArm.instr, fstepA, slotMov?, slotCmp?, cellA?, hn, hB₁] at h₁
          | some p₁ =>
            cases hB₂ : s₂.reg.getW B 64 with
            | none => simp [MArm.instr, fstepA, slotMov?, slotCmp?, cellA?, hn, hB₂] at h₂
            | some p₂ =>
              simp [MArm.instr, instrLeakA, slotMov?, slotCmp?, cellA?, hn, hB₁, hB₂]
        | stm n B off S =>
          simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨⟨⟨hn, -⟩, -⟩, -⟩ := hok
          cases hB₁ : s₁.reg.getW B 64 with
          | none => simp [MArm.instr, fstepA, slotMov?, slotCmp?, cellA?, hn, hB₁] at h₁
          | some p₁ =>
            cases hB₂ : s₂.reg.getW B 64 with
            | none => simp [MArm.instr, fstepA, slotMov?, slotCmp?, cellA?, hn, hB₂] at h₂
            | some p₂ =>
              simp [MArm.instr, instrLeakA, slotMov?, slotCmp?, cellA?, hn, hB₁, hB₂]
        | stv n B off S =>
          simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨⟨⟨hn, -⟩, -⟩, -⟩ := hok
          cases hB₁ : s₁.reg.getW B 64 with
          | none => simp [MArm.instr, fstepA, slotMov?, slotCmp?, cellA?, hn, hB₁] at h₁
          | some p₁ =>
            cases hB₂ : s₂.reg.getW B 64 with
            | none => simp [MArm.instr, fstepA, slotMov?, slotCmp?, cellA?, hn, hB₂] at h₂
            | some p₂ =>
              simp [MArm.instr, instrLeakA, slotMov?, slotCmp?, cellA?, hn, hB₁, hB₂]
        | ldv D n B off =>
          simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨⟨⟨hn, hD⟩, -⟩, -⟩ := hok
          have hcD := cellParts?_gp hD
          cases hB₁ : s₁.reg.getW B 64 with
          | none => simp [MArm.instr, fstepA, slotMov?, slotCmp?, cellA?, hn, hcD, hB₁] at h₁
          | some p₁ =>
            cases hB₂ : s₂.reg.getW B 64 with
            | none => simp [MArm.instr, fstepA, slotMov?, slotCmp?, cellA?, hn, hcD, hB₂] at h₂
            | some p₂ =>
              simp [MArm.instr, instrLeakA, slotMov?, slotCmp?, cellA?, hn, hcD, hB₁, hB₂]
      split at hok
      · rename_i q v hclI
        have hia := classifyI_instr hclI
        rw [hia]
        exact instrLeakA_length_reg (y := .Lopn [.reg q] "MOV:64" [.imm v]) (t := none)
          (by simp (config := { decide := true }) [normA, tagA]) (by simp [cellA?]) s₁ s₂
      split at hok
      · rename_i D v hclL
        obtain ⟨hia, -⟩ := classifyL_instr hclL
        rw [hia]
        exact instrLeakA_length_reg (y := .Lopn [.reg D] "MOV:64" [.imm v]) (t := none)
          (by simp (config := { decide := true }) [normA, tagA]) (by simp [cellA?]) s₁ s₂
      split at hok
      · rename_i D C A B hclV
        have hia := classifyV_instr hclV
        rw [hia]
        exact instrLeakA_length_reg
          (y := .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]) (t := none)
          (by simp (config := { decide := true }) [normA, tagA]) (by simp [cellA?]) s₁ s₂
      split at hok
      · rename_i n D A B hclE
        have hia := classifyE_instr hclE
        rw [hia]
        exact instrLeakA_length_reg (y := eInstr n D A B) (t := none)
          (by cases n <;> simp (config := { decide := true }) [eInstr, eMnem, normA, tagA])
          (by cases n <;> simp [eInstr, eMnem, cellA?]) s₁ s₂
      split at hok
      · rename_i l D A B hclX
        have hia := classifyX_instr hclX
        rw [hia]
        exact instrLeakA_length_reg (y := xInstr l D A B) (t := none)
          (by cases l <;> simp (config := { decide := true }) [xInstr, xMnem, normA, tagA])
          (by cases l <;> simp [xInstr, xMnem, cellA?]) s₁ s₂
      split at hok
      · rename_i n D A v hclEI
        have hia := classifyEI_instr hclEI
        rw [hia]
        exact instrLeakA_length_reg (y := eiInstr n D A v) (t := none)
          (by cases n <;> simp (config := { decide := true }) [eiInstr, eMnem, normA, tagA])
          (by cases n <;> simp [eiInstr, eMnem, cellA?]) s₁ s₂
      split at hok
      · rename_i D kc hclR
        have hia := classifyR_instr hclR
        rw [hia]
        exact instrLeakA_length_reg (y := rInstr D kc) (t := none)
          (by simp (config := { decide := true }) [rInstr, normA, tagA])
          (by simp [rInstr, cellA?]) s₁ s₂
      split at hok
      · rename_i ar hcl
        have hia := classifyA_instr hcl
        have hli := AArm.li_eq hok
        rw [← hia, hli] at h₁ h₂
        rw [← hia, hli]
        exact AArm.leak_length hok h₁ h₂
      · cases hok
    | Lcond cnd l =>
      cases cnd with
      | reg cc => simp only; cases condPol cc <;> rfl
      | _ => rfl
    | _ => rfl

/-- **Equal traces of the decoded bytes of a body in the class with carry chains.** For a
    body in `printedAddrWB`, equal traces of the address machine at the frame below the stack
    register give equal traces of the decoded bytes under the regime `doitm`: `BytesTraceW`. -/
theorem bytesTraceW_of_printedAddrWB {body : Lcmd} (h : printedAddrWB body = true) :
    BytesTraceW body := by
  obtain ⟨shs, hF⟩ := bodyFactsW_of h
  exact bytesTraceW_of_tracedSim
    (tracedSimW_of_armLeaks h fun rsp => armLeaksW (Params.ofBody body) rsp)
    fun rsp => stepLenDetW hF _

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime ConstantTimeRel)

/-- **Constant time of the decoded bytes of the cell route from the source.** Let the
    program `com` pass the gate `straightCellB` at the fusion flag `fuse` and the check on
    traced runs `straightCellComLB` against the printed body `body`. If the source events of
    `com` are constant time for the labels `L`, every decoding of the function bytes of
    `body` is constant time under the regime `doitm` and any side condition between entry
    machine states related by `StraightPub`: valuations that agree on the public labels, both
    states separated, equal stack registers and equal array-parameter registers. -/
theorem straightCell_bytes_ct_src (Pj : JLeakParams) {σ : AbiLayout}
    {nm : String → String} {body : Lcmd} {fuse : Bool} {Γ : Ctxt jasminDialect}
    {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightCellB σ nm body fuse com = true)
    (hlk : straightCellComLB σ nm body fuse com = true) (L : Labels Γ)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com))
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (StraightPub σ L) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  have hpr : DecodePrintedAddrW.printedAddrWB body = true := by
    obtain ⟨m, rfl⟩ := straightCellB_ty hg
    obtain ⟨-, C2, -, hroute⟩ := straightCellB_spec hg
    simp only [cellRouteB, Bool.and_eq_true] at hroute
    exact hroute.1.1.1.1.1.1.1.1.1.1.2
  exact straightCell_bytes_ct' Pj com hg hlk L hct (bytesTraceW_of_printedAddrWB hpr) ok hdec

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT
