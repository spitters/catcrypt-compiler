/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieEmitted

@[expose] public section

/-!
# The leakage of the runtime-count loop node on the flag machine

The events, in the model `instrLeakF` of `JasminLsemMemFLeak`, of the typed export node of
`ComL.forLoopNRt` on the flag machine, as a function of the source events
`ComL.ctLeak (jLeakModel Pj)`.

* The array-returning fragment `ArrMemN` (of `JasminLsemMemSourceTieArrUncond`, the
  fragment `ExportCertFragment.arrMemNB` decides) is a chain of `ScalarMemN` register heads
  and stores. Its chain `straightOpsMem` emits `straightT` of the source events.
* A renaming `τ` of the operands (`renRM`) renames the array base of each address event
  (`renEv τ`) and keeps its offset when the index registers are related. Along the thread
  renaming of the canonicalised node, the renamed chain emits the renamed events of the
  model chain.
* The zero-trip-guarded flag loop emits the events of its prefix, the zero-trip branch and,
  per pass, the events of the body and the back-edge branch (`gNode_leak_pos`,
  `gNode_leak_zero`). A pass of the canonicalised body emits the renamed transformed events
  of the update at the trip valuation (`canonBody_leak`).
* The immediate-shift expansion keeps every terminating traced run
  (`lsemFuelMemFLeak_expand`).

`loopT Pj τ update` maps the source events `trip m :: ℓ` to the zero-trip branch and, per
pass, `straightT` of the next `comLeakLen` source events with renamed bases and the
back-edge branch, taken iff another pass follows. The branch outcomes are functions of the
trip count `m`, the address offsets of the source index values.

## Main definitions

* `renEv`, `ArrOK` — the renaming of an address event; an `Lopn` with register destinations
  and no compile-time array source.
* `straightLeakFF`, `passLeak` — the events along the extended straight fold and of the
  passes of a loop.
* `machPass`, `canonLoopLeak` — the events of a pass and of the canonicalised node.
* `shiftImage` — the instruction the immediate-shift expansion produces.
* `comLeakLen`, `loopChunks`, `loopT` — the leakage transformer of the loop node.

## Main results

* `straightLeakF_straightOps_arr` — the transformer of an `ArrMemN` chain.
* `instrLeakB_renRM`, `straightLeakF_thread` — the events of a renamed instruction and of the
  renamed chain under a thread certificate.
* `lsemFuelMemFLeak_segF`, `gLoop_run`, `gNode_leak_pos`, `gNode_leak_zero` — the traced
  zero-trip-guarded flag loop.
* `canonBody_leak`, `passLeak_canon`, `canonNode_leak` — the events of the canonicalised node.
* `lsemFuelMemFLeak_expand` — the expansion on the traced flag machine.
* `chainLeak_of_denote` — the events of the emitted node are `loopT` of the source events.
* `chainLeak_eq_of_ctLeak_eq` — equal source events give equal machine traces.
* `singleLoop_leak_abi`, `singleLoop_abiEntryCT` — the certified single-loop export from ABI
  entries, and constant time from the source.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (lsemStraightMem_append)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
  (ArrMemN RegHeadMemN straightOpsMem_var_split)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)

/-! ## 1. The chain of an array-returning update -/

/-- The events of a concatenated chain: those of the first part, then those of the second
    from the state the first part reaches. -/
theorem straightLeakF_append :
    ∀ (xs ys : List LinstrRM) (s s' : LstateM), lsemStraightMem xs s = some s' →
      straightLeakF (xs ++ ys) s = straightLeakF xs s ++ straightLeakF ys s'
  | [], ys, s, s', h => by
      simp only [lsemStraightMem_nil, Option.some.injEq] at h
      subst h
      simp [straightLeakF]
  | i :: is, ys, s, s', h => by
      rw [lsemStraightMem_cons] at h
      cases hstep : lsemStepMem i s with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hstep] at h
          simp only [] at h
          rw [List.cons_append, straightLeakF_cons_of_step hstep,
            straightLeakF_cons_of_step hstep, straightLeakF_append is ys s1 s' h,
            List.append_assoc]

/-- **The transformer of an array-returning chain.** For an update in `ArrMemN` and a state
    agreeing with `V` at depth `d = |Γ|`, the chain `straightOpsMem` emits along the
    straight-line fold `straightT` of the source events at `V`. -/
theorem straightLeakF_straightOps_arr (Pj : JLeakParams) {w n : Nat} {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (JasminTy.stackArr w n)} (hcom : ArrMemN com) :
    ∀ {nArgs d : Nat} {st : LstateM} {V : Ctxt.Valuation Γ},
      Γ.length = d → nArgs ≤ d → StoreAgreesM nArgs d st V →
      straightLeakF (straightOpsMem nArgs com d) st
        = straightT Pj nArgs com d (Com.ctLeak (jLeakModel Pj) com V) := by
  induction hcom with
  | ret v =>
      intro nArgs d st V _ _ _
      rfl
  | reg e he hbody ih =>
      intro nArgs d st V hlen harg hagree
      obtain ⟨st1, hrun1, hAg1, -⟩ :=
        lsemStraightMem_straightOps_store he (nArgs := nArgs) (curDepth := d) hlen harg hagree
      simp only [comLen, comDenoteLets] at hAg1
      have hhead := straightLeakF_straightOps Pj he hlen harg hagree
      rw [straightOpsMem_var_split, straightLeakF_append _ _ _ _ hrun1, hhead,
        ih (by simp [hlen]) (by omega) hAg1, comCtLeak_var, comCtLeak_var,
        straightT_var _ _ _ _ _ _ (exprCtLeak_length Pj _ V),
        straightT_var _ _ _ _ _ _ (exprCtLeak_length Pj _ V)]
      simp only [Nat.zero_add, List.append_assoc]
      rfl
  | store heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_store (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        heq args hagree
      have hagree' := StoreAgreesM.stepArr
        ((⟨JasminOp.stackStore _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_store, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_var _ _ _ _ _ _ (exprCtLeak_length Pj _ V),
        ← ih (by simp [hlen]) (by omega) hagree']
      congr 1
      match args with
      | .cons arr (.cons idx (.cons val .nil)) =>
        have hidx : st.reg.getW
            (operandName (resolveVar d nArgs argName (fun _ => none) idx)) 64
            = some (idx.lookup V) := by
          have := hagree.reg idx
          rwa [evalOperandN_resolveVar] at this
        rw [exprArgs_store heq arr idx val, resolveVar_isReg arr, resolveVar_isReg idx,
          resolveVar_isReg val]
        simp [memOpB, opToLinstrR, instrLeakB, opLeakF, idxVal_of_getW hidx, siteOf,
          addrSite, Expr.ctLeak, opLeak, jLeakModel, jKind]
        exact Or.inl rfl

/-! ## 2. Renaming -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (OpPlain ComOpsPlain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (shiftLinstr)

/-- The renaming of the array base of an address event; every other event unchanged. -/
def renEv (τ : String → String) : CTLeak → CTLeak
  | .addr b k => .addr (τ b) k
  | e => e

/-- An `Lopn` whose destinations are registers and whose sources include no compile-time
    array element; every other instruction. -/
def ArrOK : LinstrR → Prop
  | .Lopn ds _ ss => (∀ o ∈ ds, ∃ r, o = .reg r) ∧ ∀ o ∈ ss, ∀ b k, o ≠ .arr b k
  | _ => True

/-- **The events of a renamed instruction.** For an `ArrOK` `Lopn` whose source names hold
    in `r'` at their images the values they hold in `r`, the renamed instruction emits at
    `r'` the events of the instruction at `r` with renamed array bases. -/
theorem instrLeakB_renRM (τ : String → String) (r r' : LstateN) (i : LinstrRM)
    (hl : IsLopn i) (hok : ArrOK i.1) (hu : ∀ x ∈ useNames i.1, r'.lvm (τ x) = r.lvm x) :
    instrLeakB r' (renRM τ i) = (instrLeakB r i).map (renEv τ) := by
  obtain ⟨li, tag⟩ := i
  obtain ⟨ds, o, ss, hd⟩ := hl
  simp only at hd
  subst hd
  obtain ⟨hds, hss⟩ := hok
  simp only [instrLeakB, renRM, renLinstrR, List.map_append, List.flatMap_append,
    List.map_flatMap, List.flatMap_map]
  split_ifs
  · rfl
  simp only [List.map_append, List.map_flatMap]
  congr 1
  · rw [List.flatMap_eq_nil_iff.mpr, List.flatMap_eq_nil_iff.mpr]
    · intro x hx
      obtain ⟨q, rfl⟩ := hds x hx
      rfl
    · intro x hx
      obtain ⟨q, rfl⟩ := hds x hx
      rfl
  · refine List.flatMap_congr (fun x hx => ?_)
    cases x with
    | reg q => rfl
    | imm v => rfl
    | arr b k => exact absurd rfl (hss _ hx b k)
    | arrIdx b q sc =>
        have hq : r'.lvm (τ q) = r.lvm q :=
          hu q (by simp only [useNames, List.mem_flatMap]; exact ⟨_, hx, by simp [opNames]⟩)
        simp only [opLeakF, renOperand, renEv, idxVal, List.map_cons, List.map_nil]
        rw [hq]

/-- An instruction of the fragment's op set from register sources is `ArrOK`. -/
theorem opToLinstrR_arrOK (op : JasminOp) (hop : OpPlain op) (dst : String)
    (srcs : List LOperand) (hs : ∀ o ∈ srcs, ∃ r, o = .reg r) :
    ArrOK (opToLinstrR op dst srcs) := by
  have hna : ∀ o ∈ srcs, ∀ b k, o ≠ .arr b k := by
    intro o ho b k he
    obtain ⟨r, rfl⟩ := hs o ho
    cases he
  cases op <;> simp only [OpPlain] at hop
  all_goals first
    | exact ⟨by simp, hna⟩
    | skip
  all_goals simp only [opToLinstrR]
  all_goals first
    | exact ⟨by simp, by simp⟩
    | (split <;> exact ⟨by simp, hna⟩)
    | skip
  · split
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, hna⟩
  · split
    · rename_i base idx val
      refine ⟨by simp, ?_⟩
      intro o ho b k he
      subst he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with h | h
      · cases h
      · exact hna _ (by simp [← h]) b k rfl
    · exact ⟨by simp, hna⟩

/-- The resolved operands of an expression are registers. -/
theorem exprArgs_go_reg (d nArgs : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ exprArgs.go d nArgs argName (fun _ => none) hv, ∃ r, o = .reg r
  | [], _ => by simp [exprArgs.go]
  | _ :: _, .cons v rest => by
      intro o ho
      rcases List.mem_cons.mp ho with h | h
      · rw [h, resolveVar_isReg]; exact ⟨_, rfl⟩
      · exact exprArgs_go_reg d nArgs rest o h

/-- **The chain is `ArrOK`.** Every instruction of the chain of a program whose ops lie in
    the fragment's op set is an `ArrOK` `Lopn`. -/
theorem straightOpsMem_arrOK (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (hcom : ComOpsPlain com) (d : Nat) :
    ∀ i ∈ straightOpsMem nArgs com d, ArrOK i.1 := by
  induction com generalizing d with
  | ret v => intro i hi; simp [straightOpsMem] at hi
  | var e body ih =>
      obtain ⟨hop, hbody⟩ := hcom
      have hs := exprArgs_go_reg d nArgs e.args
      intro i hi
      simp only [straightOpsMem, List.mem_cons] at hi
      rcases hi with rfl | hi
      · split
        · exact opToLinstrR_arrOK _ (by simp_all) _ _ hs
        · exact opToLinstrR_arrOK _ (by simp_all) _ _ hs
        · exact opToLinstrR_arrOK _ (by simp_all) _ _ hs
        · exact opToLinstrR_arrOK _ (by simp_all) _ _ hs
        · split
          all_goals first
            | exact opToLinstrR_arrOK _ hop _ _ hs
            | (refine ⟨by simp, ?_⟩
               intro o ho b k he
               subst he
               simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
               rcases ho with h | h
               · rename_i src _ hsrc
                 obtain ⟨q, rfl⟩ := hs src (by
                   show src ∈ exprArgs d nArgs argName (fun _ => none) e
                   rw [hsrc]; simp)
                 cases h
               · cases h)
      · exact ih hbody (d + 1) i hi

/-! ## 3. The chain under the thread renaming -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
  (RelM2 Keeps memRegDefs memArrDefs storeHit? lsemStepMem_live defNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
  (ThreadRen ThreadNr ThreadNa ThreadCert ThreadNr.of_resolved)

/-- **The events of the chain under the thread renaming.** For a chain of `ArrOK` `Lopn`s
    with a thread certificate, a run of the chain from `s` and the renamed chain from a state
    `s'` related to `s` (as in `JasminLsemExportCanon.lsemStraightMem_thread`): the renamed
    chain emits from `s'` the events of the chain from `s` with renamed array bases. -/
theorem straightLeakF_thread {τ : String → String} {d nArgs : Nat} {S : Nat → Prop}
    {out : String} (hτ : ThreadRen τ d nArgs S out) :
    ∀ (chain : List LinstrRM), (∀ i ∈ chain, IsLopn i ∧ ArrOK i.1) →
      ∀ (cd : Nat) (h hE : String), nArgs ≤ cd → τ h = out →
      ThreadCert τ nArgs S out chain cd h hE →
      ∀ {s s' t : LstateM},
        RelM2 τ (ThreadNr τ d nArgs S cd) (ThreadNa τ out h) s s' →
        lsemStraightMem chain s = some t →
        straightLeakF (chain.map (renRM τ)) s' = (straightLeakF chain s).map (renEv τ) := by
  intro chain
  induction chain with
  | nil =>
      intro _ _ _ _ _ _ _ _ _ _ _ _
      rfl
  | cons i is ih =>
      intro hok cd h hE hcd hh hc s s' t hR hrun
      obtain ⟨hl, hao⟩ := hok i (by simp)
      have hok' : ∀ j ∈ is, IsLopn j ∧ ArrOK j.1 := fun j hj => hok j (by simp [hj])
      obtain ⟨hu, hau, hshape⟩ := hc
      rw [lsemStraightMem_cons] at hrun
      cases hstep : lsemStepMem i s with
      | none => rw [hstep] at hrun; exact absurd hrun (by simp)
      | some s1 =>
      rw [hstep] at hrun
      have hemp : ThreadNr τ d nArgs S cd "" := ThreadNr.of_resolved hτ (Or.inl rfl)
      have huN : ∀ n ∈ useNames i.1, ThreadNr τ d nArgs S cd n :=
        fun n hn => ThreadNr.of_resolved hτ (hu n hn)
      have hev : instrLeakB s'.reg (renRM τ i) = (instrLeakB s.reg i).map (renEv τ) :=
        instrLeakB_renRM τ s.reg s'.reg i hl hao (fun x hx => hR.1.2 x (huN x hx))
      rcases hshape with ⟨hst, hdef, hS, hrest⟩ | ⟨hst, hS, hrest⟩
      · have hKr : Keeps τ (ThreadNr τ d nArgs S cd) (ThreadNr τ d nArgs S (cd + 1))
            (memRegDefs i) := by
          rw [show memRegDefs i = [regName cd] from by simp [memRegDefs, hst, hdef]]
          intro r hr
          by_cases hrd : r = regName cd
          · exact Or.inl (by rw [hrd])
          · refine Or.inr ⟨fun k hk hkc => hr k hk (by omega), ?_⟩
            intro x hx
            obtain rfl : x = regName cd := by simpa using hx
            rw [hτ.tmp cd hcd hS]
            exact fun he => hrd (hr cd hcd (by omega) hS he)
        have hKa : Keeps τ (ThreadNa τ out h) (ThreadNa τ out h) (memArrDefs i) := by
          rw [show memArrDefs i = [] from by simp [memArrDefs, hst]]
          exact fun r hr => Or.inr ⟨hr, by simp⟩
        obtain ⟨s1', hs1', hR1⟩ := lsemStepMem_live hemp hτ.fix i huN
          (fun b hb => hau b hb) hKr hKa hR hstep
        rw [List.map_cons, straightLeakF_cons_of_step hs1', straightLeakF_cons_of_step hstep,
          List.map_append, hev, ih hok' (cd + 1) h hE (by omega) hh hrest hR1 hrun]
      · have hKr : Keeps τ (ThreadNr τ d nArgs S cd) (ThreadNr τ d nArgs S (cd + 1))
            (memRegDefs i) := by
          rw [show memRegDefs i = [] from by simp [memRegDefs, hst]]
          intro r hr
          refine Or.inr ⟨fun k hk hkc => hr k hk (by omega), by simp⟩
        have hKa : Keeps τ (ThreadNa τ out h) (ThreadNa τ out (regName cd)) (memArrDefs i) := by
          rw [show memArrDefs i = [regName cd] from by simp [memArrDefs, hst]]
          intro r hr
          by_cases hrd : r = regName cd
          · exact Or.inl (by rw [hrd])
          · refine Or.inr ⟨fun he => absurd (hr he) hrd, ?_⟩
            intro x hx
            obtain rfl : x = regName cd := by simpa using hx
            rw [hτ.thr cd hcd hS]
            exact fun he => hrd (hr he)
        obtain ⟨s1', hs1', hR1⟩ := lsemStepMem_live hemp hτ.fix i huN
          (fun b hb => hau b hb) hKr hKa hR hstep
        rw [List.map_cons, straightLeakF_cons_of_step hs1', straightLeakF_cons_of_step hstep,
          List.map_append, hev, ih hok' (cd + 1) (regName cd) hE (by omega)
            (hτ.thr cd hcd hS) hrest hR1 hrun]

/-! ## 4. Straight segments with flag moves -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
  (fstepF runStraightF runStraightF_cons evalInstrPMemF_isLopn fstepF_lpc_succ runStraightF_lpc
    runBoundedStraightF evalInstrPMemF_label)

/-- The events of a segment along the extended straight fold `runStraightF`; a failing step
    emits the events of its instruction and stops. -/
def straightLeakFF : List LinstrRM → LstateM → Bool → List CTLeak
  | [], _, _ => []
  | i :: is, s, zf =>
      instrLeakB s.reg i ++
        match fstepF i s zf with
        | some bz => straightLeakFF is bz.1 bz.2
        | none => []

theorem straightLeakFF_cons_of_step {i : LinstrRM} {is : List LinstrRM} {s : LstateM}
    {zf : Bool} {bz : LstateM × Bool} (h : fstepF i s zf = some bz) :
    straightLeakFF (i :: is) s zf = instrLeakB s.reg i ++ straightLeakFF is bz.1 bz.2 := by
  simp [straightLeakFF, h]

/-- **A segment of `Lopn`s on the traced flag machine.** An all-`Lopn` segment at positions
    `lpc .. lpc + |seg| - 1` of `P` runs as the extended fold `runStraightF`, emits
    `straightLeakFF`, and continues with `f` fuel. -/
theorem lsemFuelMemFLeak_segF (P : LprogM) (fn : String) (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b0 : LstateM) (zf : Bool) (f : Nat) (bz : LstateM × Bool),
      (∀ i ∈ seg, IsLopn i) →
      (∀ k, k < seg.length → P.body[b0.lpc + k]? = seg[k]?) →
      runStraightF seg b0 zf = some bz →
      lsemFuelMemFLeak P (seg.length + f) { prog := { base := b0, lfn := fn }, zf := zf }
        = (lsemFuelMemFLeak P f { prog := { base := bz.1, lfn := fn }, zf := bz.2 }).map
            fun r => (r.1, straightLeakFF seg b0 zf ++ r.2) := by
  intro seg
  induction seg with
  | nil =>
      intro b0 zf f bz _ _ hrun
      simp only [runStraightF, Option.some.injEq] at hrun
      subst hrun
      simp only [List.length_nil, Nat.zero_add, straightLeakFF, List.nil_append]
      cases lsemFuelMemFLeak P f _ <;> rfl
  | cons i is ih =>
      intro b0 zf f bz hlopn hpos hrun
      have hi : IsLopn i := hlopn i (by simp)
      have his : ∀ j ∈ is, IsLopn j := fun j hj => hlopn j (by simp [hj])
      rw [runStraightF_cons] at hrun
      cases hstep : fstepF i b0 zf with
      | none => rw [hstep] at hrun; exact absurd hrun (by simp)
      | some b1 =>
          rw [hstep, Option.bind_some] at hrun
          have hfetch : findInstrMem P
              ({ prog := { base := b0, lfn := fn }, zf := zf } : LstateMF).prog = some i := by
            show findInstrMem P { base := b0, lfn := fn } = some i
            unfold findInstrMem
            rw [if_pos (show ({ base := b0, lfn := fn } : LstatePM).lfn = P.lfn from hfn)]
            have := hpos 0 (by simp)
            simp only [Nat.add_zero, List.getElem?_cons_zero] at this
            exact this
          have heval : evalInstrPMemF P i { prog := { base := b0, lfn := fn }, zf := zf }
              = some ⟨⟨b1.1, fn⟩, b1.2⟩ := by
            rw [evalInstrPMemF_isLopn P i _ hi, hstep]
            rfl
          have hb_lpc : b1.1.lpc = b0.lpc + 1 :=
            fstepF_lpc_succ i b0 b1.1 zf b1.2 (by rw [hstep])
          have hpos' : ∀ k, k < is.length → P.body[b1.1.lpc + k]? = is[k]? := by
            intro k hk
            have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
            rw [hb_lpc, show b0.lpc + 1 + k = b0.lpc + (k + 1) from by omega, hp]
            simp
          rw [List.length_cons, show is.length + 1 + f = (is.length + f) + 1 from by omega,
            lsemFuelMemFLeak_step P _ i _ _ hfetch heval, ih b1.1 b1.2 f bz his hpos' hrun,
            Option.map_map, straightLeakFF_cons_of_step hstep, instrLeakF_of_lopn hi]
          simp only [Function.comp_def, List.append_assoc]

/-! ## 5. The zero-trip-guarded flag loop -/

/-- The layout of the guarded loop: the guard compare and branch, the top label, the body,
    the back-edge compare and branch, the skip label. -/
theorem guarded_getElem (top endL : LLabel) (nReg : String) (B : List LinstrRM) :
    (guardedFlagLoopLinstrRM top endL nReg B)[0]?
        = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], MemTag.reg none)
      ∧ (guardedFlagLoopLinstrRM top endL nReg B)[1]?
        = some (.Lcond (.reg "Z") endL, MemTag.reg none)
      ∧ (guardedFlagLoopLinstrRM top endL nReg B)[2]?
        = some (.Llabel .internal top, MemTag.reg none)
      ∧ (∀ j, j < B.length → (guardedFlagLoopLinstrRM top endL nReg B)[3 + j]? = B[j]?)
      ∧ (guardedFlagLoopLinstrRM top endL nReg B)[3 + B.length]?
        = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], MemTag.reg none)
      ∧ (guardedFlagLoopLinstrRM top endL nReg B)[4 + B.length]?
        = some (.Lcond (.reg "NZ") top, MemTag.reg none)
      ∧ (guardedFlagLoopLinstrRM top endL nReg B)[5 + B.length]?
        = some (.Llabel .internal endL, MemTag.reg none)
      ∧ (guardedFlagLoopLinstrRM top endL nReg B)[6 + B.length]? = none := by
  unfold guardedFlagLoopLinstrRM flagLoopLinstrRM flagBackedge
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [show 3 + j = j + 1 + 1 + 1 from by omega]
    simp only [List.cons_append, List.getElem?_cons_succ, List.append_assoc]
    rw [List.getElem?_append_left hj]
  all_goals
    rw [show ∀ k, k + B.length = B.length + k from fun k => Nat.add_comm _ _]
    simp

/-- The events of `k` passes of the loop body from `s`, pc reset to `q` per pass: the
    events of the body, then the branch event of the back-edge, which is taken while the
    counter is not zero. -/
def passLeak (B : List LinstrRM) (nReg : String) (q : Nat) : Nat → LstateM → List CTLeak
  | 0, _ => []
  | k + 1, s =>
      match runStraightF B s false with
      | some bz =>
          straightLeakFF B s false ++ [.branch (!(bz.1.reg.getW nReg 64 == some 0#64))]
            ++ passLeak B nReg q k (bz.1.setLpc q)
      | none => straightLeakFF B s false

section Guarded

variable (fn : String) (pre : List LinstrRM) (top endL : LLabel) (nReg : String)
  (B : List LinstrRM)

/-- The program of a prefix followed by a guarded loop. -/
abbrev gProg : LprogM := singletonProgM fn (pre ++ guardedFlagLoopLinstrRM top endL nReg B)

theorem gProg_get (k : Nat) :
    (gProg fn pre top endL nReg B).body[pre.length + k]?
      = (guardedFlagLoopLinstrRM top endL nReg B)[k]? := by
  show (pre ++ guardedFlagLoopLinstrRM top endL nReg B)[pre.length + k]? = _
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem gProg_fetch (x : LstateM) :
    findInstrMem (gProg fn pre top endL nReg B) ({ base := x, lfn := fn } : LstatePM)
      = (pre ++ guardedFlagLoopLinstrRM top endL nReg B)[x.lpc]? := by
  unfold findInstrMem
  exact if_pos rfl

/-- The flag compare emits nothing. -/
theorem instrLeakF_cmp (s : LstateMF) :
    instrLeakF (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], MemTag.reg none) s
      = [] := rfl

/-- **A taken pass.** From the loop top with `zf` clear, a pass of the body that leaves a
    nonzero counter emits the events of the body and a taken back-edge, and returns to the
    loop top. -/
theorem gPass_taken (hB : ∀ i ∈ B, IsLopn i)
    (htopL : findLabelMem top (pre ++ guardedFlagLoopLinstrRM top endL nReg B)
      = some (pre.length + 2))
    (s : LstateM) (hs : s.lpc = pre.length + 3) (bz : LstateM × Bool)
    (hrun : runStraightF B s false = some bz) (v : BitVec 64)
    (hv : bz.1.reg.getW nReg 64 = some v) (hv0 : (v == 0#64) = false) (f : Nat) :
    lsemFuelMemFLeak (gProg fn pre top endL nReg B) (B.length + (f + 2))
        { prog := { base := s, lfn := fn }, zf := false }
      = (lsemFuelMemFLeak (gProg fn pre top endL nReg B) f
          { prog := { base := bz.1.setLpc (pre.length + 3), lfn := fn }, zf := false }).map
          fun r => (r.1, straightLeakFF B s false ++ [.branch true] ++ r.2) := by
  obtain ⟨g0, g1, g2, gB, gC, gN, gE, gH⟩ := guarded_getElem top endL nReg B
  rw [lsemFuelMemFLeak_segF _ fn rfl B s false (f + 2) bz hB (fun k hk => by
    rw [hs, show pre.length + 3 + k = pre.length + (3 + k) from by omega, gProg_get, gB k hk])
    hrun]
  have hl : bz.1.lpc = pre.length + 3 + B.length := by
    rw [runStraightF_lpc B s false bz.1 bz.2 hrun, hs]
  have hf1 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := bz.1, lfn := fn }, zf := bz.2 } : LstateMF).prog
      = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], MemTag.reg none) := by
    show findInstrMem _ { base := bz.1, lfn := fn } = _
    rw [gProg_fetch, show bz.1.lpc = pre.length + (3 + B.length) from by omega]
    exact (gProg_get fn pre top endL nReg B _).trans gC
  have he1 := evalInstrPMemF_cmp (gProg fn pre top endL nReg B) (.reg nReg) nReg
    (MemTag.reg none) { prog := { base := bz.1, lfn := fn }, zf := bz.2 } v hv
  rw [lsemFuelMemFLeak_step _ _ _ _ _ hf1 he1]
  have hf2 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := bz.1.nextPc, lfn := fn }, zf := v == 0#64 } : LstateMF).prog
      = some (.Lcond (.reg "NZ") top, MemTag.reg none) := by
    show findInstrMem _ { base := bz.1.nextPc, lfn := fn } = _
    rw [gProg_fetch, show bz.1.nextPc.lpc = pre.length + (4 + B.length) from by
      show bz.1.lpc + 1 = _; omega]
    exact (gProg_get fn pre top endL nReg B _).trans gN
  have he2 : evalInstrPMemF (gProg fn pre top endL nReg B) (.Lcond (.reg "NZ") top, MemTag.reg none)
      { prog := { base := bz.1.nextPc, lfn := fn }, zf := v == 0#64 }
      = some { prog := { base := bz.1.setLpc (pre.length + 3), lfn := fn }, zf := false } := by
    rw [evalInstrPMemF_jne, hv0, if_pos rfl]
    unfold evalJumpMem
    rw [show (gProg fn pre top endL nReg B).body = pre ++ guardedFlagLoopLinstrRM top endL nReg B
      from rfl, htopL]
    rfl
  rw [lsemFuelMemFLeak_step _ _ _ _ _ hf2 he2]
  simp only [Option.map_map, Function.comp_def, instrLeakF, flagCondCC?, hv0, instrLeakB,
    List.append_assoc]
  rfl

/-- **The exit pass.** From the loop top with `zf` clear, a pass of the body that leaves a
    zero counter emits the events of the body and an untaken back-edge, and the program
    halts behind the skip label. -/
theorem gPass_exit (hB : ∀ i ∈ B, IsLopn i) (s : LstateM) (hs : s.lpc = pre.length + 3)
    (bz : LstateM × Bool) (hrun : runStraightF B s false = some bz)
    (hv : bz.1.reg.getW nReg 64 = some 0#64) (f : Nat) :
    lsemFuelMemFLeak (gProg fn pre top endL nReg B) (B.length + (f + 3))
        { prog := { base := s, lfn := fn }, zf := false }
      = some (⟨⟨bz.1.setLpc (pre.length + 6 + B.length), fn⟩, true⟩,
          straightLeakFF B s false ++ [.branch false]) := by
  obtain ⟨g0, g1, g2, gB, gC, gN, gE, gH⟩ := guarded_getElem top endL nReg B
  rw [lsemFuelMemFLeak_segF _ fn rfl B s false (f + 3) bz hB (fun k hk => by
    rw [hs, show pre.length + 3 + k = pre.length + (3 + k) from by omega, gProg_get, gB k hk])
    hrun]
  have hl : bz.1.lpc = pre.length + 3 + B.length := by
    rw [runStraightF_lpc B s false bz.1 bz.2 hrun, hs]
  have hf1 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := bz.1, lfn := fn }, zf := bz.2 } : LstateMF).prog
      = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], MemTag.reg none) := by
    show findInstrMem _ { base := bz.1, lfn := fn } = _
    rw [gProg_fetch, show bz.1.lpc = pre.length + (3 + B.length) from by omega]
    exact (gProg_get fn pre top endL nReg B _).trans gC
  have he1 := evalInstrPMemF_cmp (gProg fn pre top endL nReg B) (.reg nReg) nReg
    (MemTag.reg none) { prog := { base := bz.1, lfn := fn }, zf := bz.2 } _ hv
  rw [show f + 3 = (f + 2) + 1 from rfl, lsemFuelMemFLeak_step _ _ _ _ _ hf1 he1]
  have hf2 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := bz.1.nextPc, lfn := fn }, zf := (0#64 == 0#64) } : LstateMF).prog
      = some (.Lcond (.reg "NZ") top, MemTag.reg none) := by
    show findInstrMem _ { base := bz.1.nextPc, lfn := fn } = _
    rw [gProg_fetch, show bz.1.nextPc.lpc = pre.length + (4 + B.length) from by
      show bz.1.lpc + 1 = _; omega]
    exact (gProg_get fn pre top endL nReg B _).trans gN
  have he2 : evalInstrPMemF (gProg fn pre top endL nReg B) (.Lcond (.reg "NZ") top, MemTag.reg none)
      { prog := { base := bz.1.nextPc, lfn := fn }, zf := (0#64 == 0#64) }
      = some { prog := { base := bz.1.nextPc.nextPc, lfn := fn }, zf := true } := by
    rw [evalInstrPMemF_jne]
    rfl
  rw [lsemFuelMemFLeak_step _ _ _ _ _ hf2 he2]
  have hf3 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := bz.1.nextPc.nextPc, lfn := fn }, zf := true } : LstateMF).prog
      = some (.Llabel .internal endL, MemTag.reg none) := by
    show findInstrMem _ { base := bz.1.nextPc.nextPc, lfn := fn } = _
    rw [gProg_fetch, show bz.1.nextPc.nextPc.lpc = pre.length + (5 + B.length) from by
      show bz.1.lpc + 1 + 1 = _; omega]
    exact (gProg_get fn pre top endL nReg B _).trans gE
  rw [lsemFuelMemFLeak_step _ _ _ _ _ hf3 (evalInstrPMemF_label _ _ _ _ _)]
  rw [lsemFuelMemFLeak_halt]
  · simp only [Option.map_some, instrLeakF, flagCondCC?, instrLeakB, List.append_nil,
      List.nil_append]
    refine congrArg some (Prod.ext ?_ ?_)
    · show (⟨⟨bz.1.nextPc.nextPc.nextPc, fn⟩, true⟩ : LstateMF) = _
      congr 2
      show bz.1.setLpc (bz.1.lpc + 3) = _
      rw [hl]
      congr 1
      omega
    · rfl
  · show findInstrMem _ { base := bz.1.nextPc.nextPc.nextPc, lfn := fn } = none
    rw [gProg_fetch, show bz.1.nextPc.nextPc.nextPc.lpc = pre.length + (6 + B.length) from by
      show bz.1.lpc + 1 + 1 + 1 = _; omega]
    exact (gProg_get fn pre top endL nReg B _).trans gH

/-- **The passes of the loop.** From the loop top with `zf` clear, if the first `k` passes
    leave a nonzero counter and pass `k + 1` leaves a zero counter, the program halts with
    the events `passLeak` of the `k + 1` passes. -/
theorem gLoop_run (hB : ∀ i ∈ B, IsLopn i)
    (htopL : findLabelMem top (pre ++ guardedFlagLoopLinstrRM top endL nReg B)
      = some (pre.length + 2)) :
    ∀ (k : Nat) (s : LstateM), s.lpc = pre.length + 3 →
      (∀ i, i < k → ∀ bi, runBoundedStraightF B (pre.length + 3) i s = some bi →
        ∀ bz, runStraightF B bi false = some bz →
          ∃ v, bz.1.reg.getW nReg 64 = some v ∧ (v == 0#64) = false) →
      (∃ bk, runBoundedStraightF B (pre.length + 3) k s = some bk
        ∧ ∃ bz, runStraightF B bk false = some bz ∧ bz.1.reg.getW nReg 64 = some 0#64) →
      ∃ N t, lsemFuelMemFLeak (gProg fn pre top endL nReg B) N
          { prog := { base := s, lfn := fn }, zf := false }
        = some (t, passLeak B nReg (pre.length + 3) (k + 1) s) := by
  intro k
  induction k with
  | zero =>
      intro s hs _ hlast
      obtain ⟨bk, hbk, bz, hbz, hz⟩ := hlast
      simp only [runBoundedStraightF, Option.some.injEq] at hbk
      subst hbk
      refine ⟨B.length + (0 + 3), ⟨⟨bz.1.setLpc (pre.length + 6 + B.length), fn⟩, true⟩, ?_⟩
      rw [gPass_exit fn pre top endL nReg B hB s hs bz hbz hz 0]
      simp [passLeak, hbz, hz]
  | succ k ih =>
      intro s hs htaken hlast
      cases hbz : runStraightF B s false with
      | none =>
          obtain ⟨bk, hbk, -⟩ := hlast
          simp [runBoundedStraightF, hbz] at hbk
      | some bz =>
          obtain ⟨v, hv, hv0⟩ := htaken 0 (by omega) s rfl bz hbz
          have hs' : (bz.1.setLpc (pre.length + 3)).lpc = pre.length + 3 := rfl
          obtain ⟨N, t, hN⟩ := ih (bz.1.setLpc (pre.length + 3)) hs'
            (fun i hi bi hbi bz' hbz' => htaken (i + 1) (by omega) bi
              (by simp only [runBoundedStraightF, hbz, Option.bind_some]; exact hbi) bz' hbz')
            (by
              obtain ⟨bk, hbk, rest⟩ := hlast
              exact ⟨bk, by simpa [runBoundedStraightF, hbz] using hbk, rest⟩)
          refine ⟨B.length + (N + 2), t, ?_⟩
          rw [gPass_taken fn pre top endL nReg B hB htopL s hs bz hbz v hv hv0 N, hN]
          simp [passLeak, hbz, hv, hv0]

/-- The prefix and the guard compare: from program counter `0` the prefix runs to `b1`, whose
    counter reads `v0`, and the compare sets `zf` to `v0 = 0`. -/
theorem gGuard_cmp (hpre : ∀ i ∈ pre, IsLopn i) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (b1 : LstateM × Bool) (hrun : runStraightF pre b0 zf = some b1) (v0 : BitVec 64)
    (hv : b1.1.reg.getW nReg 64 = some v0) (f : Nat) :
    lsemFuelMemFLeak (gProg fn pre top endL nReg B) (pre.length + (f + 1))
        { prog := { base := b0, lfn := fn }, zf := zf }
      = (lsemFuelMemFLeak (gProg fn pre top endL nReg B) f
          ⟨⟨b1.1.nextPc, fn⟩, v0 == 0#64⟩).map
          fun r => (r.1, straightLeakFF pre b0 zf ++ r.2) := by
  obtain ⟨g0, -⟩ := guarded_getElem top endL nReg B
  have hpos : ∀ k, k < pre.length → (gProg fn pre top endL nReg B).body[b0.lpc + k]? = pre[k]? := by
    intro k hk
    rw [hpc, Nat.zero_add]
    exact List.getElem?_append_left hk
  rw [lsemFuelMemFLeak_segF _ fn rfl pre b0 zf (f + 1) b1 hpre hpos hrun]
  have hl : b1.1.lpc = pre.length := by rw [runStraightF_lpc pre b0 zf b1.1 b1.2 hrun, hpc]; omega
  have hf1 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := b1.1, lfn := fn }, zf := b1.2 } : LstateMF).prog
      = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], MemTag.reg none) := by
    show findInstrMem _ { base := b1.1, lfn := fn } = _
    rw [gProg_fetch, show b1.1.lpc = pre.length + 0 from hl]
    exact (gProg_get fn pre top endL nReg B _).trans g0
  have he1 := evalInstrPMemF_cmp (gProg fn pre top endL nReg B) (.reg nReg) nReg
    (MemTag.reg none) { prog := { base := b1.1, lfn := fn }, zf := b1.2 } v0 hv
  rw [lsemFuelMemFLeak_step _ _ _ _ _ hf1 he1]
  simp only [Option.map_map, Function.comp_def, instrLeakF_cmp, List.nil_append]

/-- **The node with a nonzero count.** The prefix, the guard compare, the untaken zero-trip
    branch and the top label run to the loop top. -/
theorem gNode_pos (hpre : ∀ i ∈ pre, IsLopn i) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (b1 : LstateM × Bool) (hrun : runStraightF pre b0 zf = some b1) (v0 : BitVec 64)
    (hv : b1.1.reg.getW nReg 64 = some v0) (hv0 : (v0 == 0#64) = false) (f : Nat) :
    lsemFuelMemFLeak (gProg fn pre top endL nReg B) (pre.length + (f + 3))
        { prog := { base := b0, lfn := fn }, zf := zf }
      = (lsemFuelMemFLeak (gProg fn pre top endL nReg B) f
          ⟨⟨b1.1.setLpc (pre.length + 3), fn⟩, false⟩).map
          fun r => (r.1, straightLeakFF pre b0 zf ++ [.branch false] ++ r.2) := by
  obtain ⟨-, g1, g2, -⟩ := guarded_getElem top endL nReg B
  have hl : b1.1.lpc = pre.length := by rw [runStraightF_lpc pre b0 zf b1.1 b1.2 hrun, hpc]; omega
  rw [show f + 3 = (f + 2) + 1 from rfl, gGuard_cmp fn pre top endL nReg B hpre b0 zf hpc b1 hrun
    v0 hv, hv0]
  have hf2 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := b1.1.nextPc, lfn := fn }, zf := false } : LstateMF).prog
      = some (.Lcond (.reg "Z") endL, MemTag.reg none) := by
    show findInstrMem _ { base := b1.1.nextPc, lfn := fn } = _
    rw [gProg_fetch, show b1.1.nextPc.lpc = pre.length + 1 from by
      show b1.1.lpc + 1 = _; omega]
    exact (gProg_get fn pre top endL nReg B _).trans g1
  have he2 : evalInstrPMemF (gProg fn pre top endL nReg B) (.Lcond (.reg "Z") endL, MemTag.reg none)
      { prog := { base := b1.1.nextPc, lfn := fn }, zf := false }
      = some ⟨⟨b1.1.nextPc.nextPc, fn⟩, false⟩ := by
    rw [evalInstrPMemF_je]
    rfl
  rw [lsemFuelMemFLeak_step _ _ _ _ _ hf2 he2]
  have hf3 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := b1.1.nextPc.nextPc, lfn := fn }, zf := false } : LstateMF).prog
      = some (.Llabel .internal top, MemTag.reg none) := by
    show findInstrMem _ { base := b1.1.nextPc.nextPc, lfn := fn } = _
    rw [gProg_fetch, show b1.1.nextPc.nextPc.lpc = pre.length + 2 from by
      show b1.1.lpc + 1 + 1 = _; omega]
    exact (gProg_get fn pre top endL nReg B _).trans g2
  rw [lsemFuelMemFLeak_step _ _ _ _ _ hf3 (evalInstrPMemF_label _ _ _ _ _)]
  have hb : b1.1.nextPc.nextPc.nextPc = b1.1.setLpc (pre.length + 3) := by
    show b1.1.setLpc (b1.1.lpc + 3) = _
    rw [hl]
  simp only [Option.map_map, Function.comp_def, instrLeakF, flagCondCC?, instrLeakB,
    List.nil_append, List.append_assoc]
  rw [show ({ prog := { ({ base := b1.1.nextPc.nextPc, lfn := fn } : LstatePM) with
      base := b1.1.nextPc.nextPc.nextPc }, zf := false } : LstateMF)
      = ⟨⟨b1.1.setLpc (pre.length + 3), fn⟩, false⟩ from by rw [← hb]]
  rfl

/-- **The node with a zero count.** The prefix, the guard compare and the taken zero-trip
    branch, which jumps past the skip label, where the program halts. -/
theorem gNode_zero (hpre : ∀ i ∈ pre, IsLopn i)
    (hendL : findLabelMem endL (pre ++ guardedFlagLoopLinstrRM top endL nReg B)
      = some (pre.length + B.length + 5))
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (b1 : LstateM × Bool) (hrun : runStraightF pre b0 zf = some b1)
    (hv : b1.1.reg.getW nReg 64 = some 0#64) (f : Nat) :
    lsemFuelMemFLeak (gProg fn pre top endL nReg B) (pre.length + (f + 2))
        { prog := { base := b0, lfn := fn }, zf := zf }
      = some (⟨⟨b1.1.nextPc.setLpc (pre.length + B.length + 6), fn⟩, true⟩,
          straightLeakFF pre b0 zf ++ [.branch true]) := by
  obtain ⟨-, g1, -, -, -, -, -, gH⟩ := guarded_getElem top endL nReg B
  have hl : b1.1.lpc = pre.length := by rw [runStraightF_lpc pre b0 zf b1.1 b1.2 hrun, hpc]; omega
  rw [gGuard_cmp fn pre top endL nReg B hpre b0 zf hpc b1 hrun _ hv]
  have hf2 : findInstrMem (gProg fn pre top endL nReg B)
      ({ prog := { base := b1.1.nextPc, lfn := fn }, zf := (0#64 == 0#64) } : LstateMF).prog
      = some (.Lcond (.reg "Z") endL, MemTag.reg none) := by
    show findInstrMem _ { base := b1.1.nextPc, lfn := fn } = _
    rw [gProg_fetch, show b1.1.nextPc.lpc = pre.length + 1 from by
      show b1.1.lpc + 1 = _; omega]
    exact (gProg_get fn pre top endL nReg B _).trans g1
  have he2 : evalInstrPMemF (gProg fn pre top endL nReg B) (.Lcond (.reg "Z") endL, MemTag.reg none)
      { prog := { base := b1.1.nextPc, lfn := fn }, zf := (0#64 == 0#64) }
      = some ⟨⟨b1.1.nextPc.setLpc (pre.length + B.length + 6), fn⟩, true⟩ := by
    rw [evalInstrPMemF_je]
    split
    · unfold evalJumpMem
      rw [show (gProg fn pre top endL nReg B).body
        = pre ++ guardedFlagLoopLinstrRM top endL nReg B from rfl, hendL]
      rfl
    · rename_i h
      simp at h
  rw [lsemFuelMemFLeak_step _ _ _ _ _ hf2 he2, lsemFuelMemFLeak_halt]
  · rfl
  · show findInstrMem _ { base := b1.1.nextPc.setLpc (pre.length + B.length + 6), lfn := fn }
      = none
    rw [gProg_fetch, show (b1.1.nextPc.setLpc (pre.length + B.length + 6)).lpc
      = pre.length + (6 + B.length) from by show pre.length + B.length + 6 = _; omega]
    exact (gProg_get fn pre top endL nReg B _).trans gH

/-- **The trace of the node with a nonzero count.** If the prefix runs to `b1` with a nonzero
    counter, the first `k` passes leave a nonzero counter and pass `k + 1` a zero counter,
    then every terminating traced run of the node emits the events of the prefix, the
    untaken zero-trip branch and the `k + 1` passes. -/
theorem gNode_leak_pos (hpre : ∀ i ∈ pre, IsLopn i) (hB : ∀ i ∈ B, IsLopn i)
    (htopL : findLabelMem top (pre ++ guardedFlagLoopLinstrRM top endL nReg B)
      = some (pre.length + 2))
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (b1 : LstateM × Bool) (hrun : runStraightF pre b0 zf = some b1) (v0 : BitVec 64)
    (hv : b1.1.reg.getW nReg 64 = some v0) (hv0 : (v0 == 0#64) = false) (k : Nat)
    (htaken : ∀ i, i < k → ∀ bi,
      runBoundedStraightF B (pre.length + 3) i (b1.1.setLpc (pre.length + 3)) = some bi →
        ∀ bz, runStraightF B bi false = some bz →
          ∃ v, bz.1.reg.getW nReg 64 = some v ∧ (v == 0#64) = false)
    (hlast : ∃ bk,
      runBoundedStraightF B (pre.length + 3) k (b1.1.setLpc (pre.length + 3)) = some bk
        ∧ ∃ bz, runStraightF B bk false = some bz ∧ bz.1.reg.getW nReg 64 = some 0#64)
    {ℓ : List CTLeak}
    (hr : FRun (gProg fn pre top endL nReg B) { prog := { base := b0, lfn := fn }, zf := zf } ℓ) :
    ℓ = straightLeakFF pre b0 zf ++ [.branch false]
      ++ passLeak B nReg (pre.length + 3) (k + 1) (b1.1.setLpc (pre.length + 3)) := by
  obtain ⟨N, t, hN⟩ := gLoop_run fn pre top endL nReg B hB htopL k _ rfl htaken hlast
  have h := gNode_pos fn pre top endL nReg B hpre b0 zf hpc b1 hrun v0 hv hv0 N
  rw [hN, Option.map_some] at h
  exact fRun_unique hr ⟨_, _, h⟩

/-- **The trace of the node with a zero count.** If the prefix runs to `b1` with a zero
    counter, every terminating traced run of the node emits the events of the prefix and the
    taken zero-trip branch. -/
theorem gNode_leak_zero (hpre : ∀ i ∈ pre, IsLopn i)
    (hendL : findLabelMem endL (pre ++ guardedFlagLoopLinstrRM top endL nReg B)
      = some (pre.length + B.length + 5))
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (b1 : LstateM × Bool) (hrun : runStraightF pre b0 zf = some b1)
    (hv : b1.1.reg.getW nReg 64 = some 0#64) {ℓ : List CTLeak}
    (hr : FRun (gProg fn pre top endL nReg B) { prog := { base := b0, lfn := fn }, zf := zf } ℓ) :
    ℓ = straightLeakFF pre b0 zf ++ [.branch true] :=
  fRun_unique hr ⟨_, _, gNode_zero fn pre top endL nReg B hpre hendL b0 zf hpc b1 hrun hv 0⟩

end Guarded

/-! ## 6. One pass of the canonicalised body -/

/-- A segment whose instructions emit nothing at every register file emits nothing. -/
theorem straightLeakFF_quiet :
    ∀ (seg : List LinstrRM), (∀ i ∈ seg, ∀ r, instrLeakB r i = []) →
      ∀ (s : LstateM) (zf : Bool), straightLeakFF seg s zf = []
  | [], _, _, _ => rfl
  | i :: is, h, s, zf => by
      simp only [straightLeakFF, h i (by simp), List.nil_append]
      cases fstepF i s zf with
      | none => rfl
      | some bz => exact straightLeakFF_quiet is (fun j hj => h j (by simp [hj])) _ _

/-- The events of a concatenated segment along `runStraightF`. -/
theorem straightLeakFF_append :
    ∀ (xs ys : List LinstrRM) (s : LstateM) (zf : Bool) (bz : LstateM × Bool),
      runStraightF xs s zf = some bz →
      straightLeakFF (xs ++ ys) s zf = straightLeakFF xs s zf ++ straightLeakFF ys bz.1 bz.2
  | [], ys, s, zf, bz, h => by
      simp only [runStraightF, Option.some.injEq] at h
      subst h
      rfl
  | i :: is, ys, s, zf, bz, h => by
      rw [runStraightF_cons] at h
      cases hstep : fstepF i s zf with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some b1 =>
          rw [hstep, Option.bind_some] at h
          rw [List.cons_append, straightLeakFF_cons_of_step hstep,
            straightLeakFF_cons_of_step hstep, straightLeakFF_append is ys _ _ bz h,
            List.append_assoc]

/-- On a plain segment that the straight-line fold runs, the events along `runStraightF`
    from the state with any carry and overflow flags are those along `lsemStraightMem`. -/
theorem straightLeakFF_plain :
    ∀ (seg : List LinstrRM), PlainLopnBody seg →
      ∀ (s b : LstateM) (c o zf : Bool), lsemStraightMem seg s = some b →
        straightLeakFF seg { s with cf := c, of := o } zf = straightLeakF seg s
  | [], _, s, b, c, o, zf, _ => rfl
  | i :: is, hplain, s, b, c, o, zf, hrun => by
      obtain ⟨_, hc, hm⟩ := hplain i (by simp)
      have his : PlainLopnBody is := fun j hj => hplain j (by simp [hj])
      rw [lsemStraightMem_cons] at hrun
      cases hstep : lsemStepMem i s with
      | none => rw [hstep] at hrun; exact absurd hrun (by simp)
      | some s1 =>
          rw [hstep] at hrun
          simp only [] at hrun
          have h1 : lsemStepMem i { s with cf := c, of := o }
              = some { s1 with cf := c, of := o } := by
            rw [lsemStepMem_setFlags, hstep]; rfl
          obtain ⟨c1, o1, hw⟩ := withALUFlags_eq i { s with cf := c, of := o }
            { s1 with cf := c, of := o }
          have hf : fstepF i { s with cf := c, of := o } zf
              = some ({ s1 with cf := c1, of := o1 }, zf) := by
            simp only [fstepF, hc, hm]
            rw [stepMemF_of_lsemStepMem h1, hw]
            rfl
          rw [straightLeakFF_cons_of_step hf, straightLeakF_cons_of_step hstep,
            straightLeakFF_plain is his s1 b c1 o1 zf hrun]

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
  (CanonRen canonBodyRM canonFeedback pullM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (loopAdvanceRM loopTouchRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (tripValArrMN accRegMN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (loopBodyRetArrMN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie (straightOpsMem_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
  (runStraightF_of_lsemStraightMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (straightOpsMem_plain)

/-- The feedback move, the index and counter updates and the invariant touches emit
    nothing. -/
theorem canonTail_quiet (d : Nat) (out : String) (absent : Bool) (regs : List String) :
    ∀ i ∈ canonFeedback out absent ++ loopAdvanceRM d ++ loopTouchRM d regs,
      ∀ r, instrLeakB r i = [] := by
  intro i hi r
  simp only [canonFeedback, loopAdvanceRM, loopTouchRM, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hi
  rcases hi with (hi | hi | hi) | ⟨q, -, rfl⟩
  · split at hi
    · simp at hi
    · simp only [List.mem_singleton] at hi
      subst hi
      rfl
  · subst hi; rfl
  · subst hi; rfl
  · rfl

/-- **The events of one pass of the canonicalised body.** From a state whose pullback along
    `τ` agrees with the trip-`t` valuation, a pass of the canonicalised body emits the events
    `straightT` of the update at that valuation, with array bases renamed by `τ`. -/
theorem canonBody_leak (Pj : JLeakParams) {τ : String → String} {d : Nat} {S : Nat → Prop}
    {out : String} {invTys : Ctxt jasminDialect} {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hops : ComOpsPlain update)
    (hτ : CanonRen τ d invTys.length S out)
    (hcert : ThreadCert τ (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (absent : Bool) (regs : List String)
    (invs : Ctxt.Valuation invTys) (t : Nat) (arrt : Fin n → BitVec w) (s' : LstateM)
    (hag : StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ s')
      (tripValArrMN invs t arrt)) (zf : Bool) :
    straightLeakFF (canonBodyRM τ d out update absent regs) s' zf
      = (straightT Pj (invTys.length + 2) update (invTys.length + 2)
          (Com.ctLeak (jLeakModel Pj) update (tripValArrMN invs t arrt))).map (renEv τ) := by
  set chain := straightOpsMem (invTys.length + 2) update (invTys.length + 2) with hchain
  obtain ⟨stc, hrunC, -, -⟩ :=
    JasminLsemMemSourceTieArrUncond.ArrMemN.straightOps_full hupd
      (nArgs := invTys.length + 2) (curDepth := invTys.length + 2) rfl le_rfl hag
  have hR0 : RelM2 τ (ThreadNr τ d (invTys.length + 2) S (invTys.length + 2))
      (ThreadNa τ out (accRegMN invTys)) (pullM τ s') s' :=
    ⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl, rfl⟩
  obtain ⟨t', hrun', -, -⟩ := JasminLsemExportCanon.lsemStraightMem_thread hτ.toThreadRen _ _ _ _
    le_rfl hτ.acc hcert hR0 hrunC
  have hok : ∀ i ∈ chain, IsLopn i ∧ ArrOK i.1 := fun i hi =>
    ⟨straightOpsMem_isLopn update _ _ i hi, straightOpsMem_arrOK _ update hops _ i hi⟩
  have hplain : PlainLopnBody (chain.map (renRM τ)) :=
    JasminLsemExportCanon.plainLopnBody_map_renRM τ (straightOpsMem_plain _ update hops _)
  obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem _ hplain s' t' zf hrun'
  unfold canonBodyRM
  rw [straightLeakFF_append _ _ _ _ _ hF, straightLeakFF_quiet _ (canonTail_quiet d out absent regs),
    List.append_nil,
    show s' = { s' with cf := s'.cf, of := s'.of } from rfl,
    straightLeakFF_plain _ hplain s' t' s'.cf s'.of zf hrun',
    straightLeakF_thread hτ.toThreadRen chain hok _ _ _ le_rfl hτ.acc hcert hR0 hrunC]
  exact congrArg (List.map (renEv τ))
    (straightLeakF_straightOps_arr Pj hupd (nArgs := invTys.length + 2)
      (d := invTys.length + 2) (by simp) le_rfl hag)

/-! ## 7. The passes of the canonicalised node -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (JLoopBodyN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (getW_setLpc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (StoreAgreesM.setLpc)

/-- The events of pass `t` of a loop of `m` passes from the accumulator `acc`: the renamed
    transformed events of the update at the trip-`t` valuation, then the back-edge, taken
    iff another pass follows. -/
def machPass (Pj : JLeakParams) (τ : String → String) {invTys : Ctxt jasminDialect}
    {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : Ctxt.Valuation invTys) (m t : Nat) (acc : Fin n → BitVec w) : List CTLeak :=
  (straightT Pj (invTys.length + 2) update (invTys.length + 2)
      (Com.ctLeak (jLeakModel Pj) update (tripValArrMN invs t acc))).map (renEv τ)
    ++ [.branch (decide (t + 1 < m))]

/-- A pass of `passLeak` that runs. -/
theorem passLeak_succ_of_run {B : List LinstrRM} {nReg : String} {q k : Nat} {s : LstateM}
    {bz : LstateM × Bool} (h : runStraightF B s false = some bz) :
    passLeak B nReg q (k + 1) s
      = straightLeakFF B s false ++ [.branch (!(bz.1.reg.getW nReg 64 == some 0#64))]
          ++ passLeak B nReg q k (bz.1.setLpc q) := by
  simp only [passLeak, h]

/-- **The passes of the canonicalised body.** From a state whose pullback agrees with the
    trip-`t` valuation at `arr`, whose invariant base registers read, and whose counter reads
    `m - t`, the remaining `k + 1 = m - t` passes emit `machPass` along the source fold. -/
theorem passLeak_canon (Pj : JLeakParams) {τ : String → String} {d : Nat} {S : Nat → Prop}
    {out : String} {invTys : Ctxt jasminDialect} {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hops : ComOpsPlain update)
    (hτ : CanonRen τ d invTys.length S out)
    (hcert : ThreadCert τ (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < invTys.length ∧ r = τ (argName j))
    (invs : Ctxt.Valuation invTys) (q m : Nat) (hm64 : m < 2 ^ 64) :
    ∀ (k t : Nat) (s : LstateM) (arr : Fin n → BitVec w), t + k + 1 = m →
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ s)
        (tripValArrMN invs t arr) →
      (∀ j, j < invTys.length → (s.reg.getW (τ (argName j)) 64).isSome) →
      s.reg.getW (loopCtr d) 64 = some (BitVec.ofNat 64 m - BitVec.ofNat 64 t) →
      passLeak (canonBodyRM τ d out update absent regs) (loopCtr d) q (k + 1) s
        = iterLeak (machPass Pj τ update invs m) (fun t acc => JLoopBodyN.stepC update invs t acc)
            (List.range' t (k + 1)) arr := by
  intro k
  induction k with
  | zero =>
      intro t s arr htm hag hinv hcnt
      obtain ⟨s'', zf', hrun, -, -, hn⟩ := JasminLsemExportCanon.canonBody_trip update hupd hτ
        hcert absent regs hregs invs t arr s hag hinv _ hcnt false
      have hz : BitVec.ofNat 64 m - BitVec.ofNat 64 t - 1#64 = 0#64 := by
        rw [show m = t + 1 from by omega, BitVec.ofNat_add, BitVec.sub_sub]
        simp
      rw [passLeak_succ_of_run (B := canonBodyRM τ d out update absent regs) hrun, canonBody_leak Pj update hupd hops hτ hcert absent regs
        invs t arr s hag false, hn, hz]
      simp [List.range'_succ, iterLeak, machPass, passLeak, show ¬ t + 1 < m from by omega]
  | succ k ih =>
      intro t s arr htm hag hinv hcnt
      obtain ⟨s'', zf', hrun, hag'', hinv'', hn⟩ := JasminLsemExportCanon.canonBody_trip update
        hupd hτ hcert absent regs hregs invs t arr s hag hinv _ hcnt false
      have hn' : s''.reg.getW (loopCtr d) 64
          = some (BitVec.ofNat 64 m - BitVec.ofNat 64 (t + 1)) := by
        rw [hn, BitVec.ofNat_add, BitVec.sub_sub]
      have hnz : (BitVec.ofNat 64 m - BitVec.ofNat 64 (t + 1) == 0#64) = false := by
        have := JasminLsemMemFlagArrLoop.ofNat_sub_ofNat_ne_zero m (t + 1) hm64 (by omega)
        simpa using this
      have ih' := ih (t + 1) (s''.setLpc q) (JLoopBodyN.stepC update invs t arr) (by omega)
        (StoreAgreesM.setLpc hag'' q) (fun j hj => by rw [getW_setLpc]; exact hinv'' j hj)
        (by rw [getW_setLpc]; exact hn')
      have hb : (!(some (BitVec.ofNat 64 m - BitVec.ofNat 64 (t + 1)) == some 0#64))
          = decide (t + 1 < m) := by
        rw [decide_eq_true (show t + 1 < m from by omega)]
        simpa using hnz
      rw [passLeak_succ_of_run (B := canonBodyRM τ d out update absent regs) hrun,
        canonBody_leak Pj update hupd hops hτ hcert absent regs invs t arr s hag false, hn', ih',
        hb, show List.range' t (k + 1 + 1) = t :: List.range' (t + 1) (k + 1) from rfl,
        iterLeak]
      simp only [machPass, List.append_assoc, List.singleton_append]

/-! ## 8. The canonicalised node -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
  (canonNodeRM canonSeedsRM canonBodyRM_isLopn canonBodyRM_run canonSeedsRM_run
    findLabelMem_canonSeedsRM pullM_getW pullM_getArr pullM_setLpc StoreAgreesM.congr_args)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (findLabelMem_guarded_top)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagInvTouch
  (runBoundedStraightF_succ_right)

/-- The events of the loop of the canonicalised node with `m` passes from the seed `arr0`:
    the zero-trip branch, taken iff `m = 0`, then the passes. -/
def canonLoopLeak (Pj : JLeakParams) (τ : String → String) {invTys : Ctxt jasminDialect}
    {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : Ctxt.Valuation invTys) (arr0 : Fin n → BitVec w) (m : Nat) : List CTLeak :=
  .branch (decide (m = 0)) ::
    iterLeak (machPass Pj τ update invs m) (fun t acc => JLoopBodyN.stepC update invs t acc)
      (List.range m) arr0

/-- **The trace of the canonicalised node.** Under the hypotheses of
    `JasminLsemExportCanon.canonNodeRM_faithful`, with the update's ops in the fragment's op
    set, every terminating traced run of the canonicalised node from the entry state emits
    `canonLoopLeak` of the trip count. -/
theorem canonNode_leak (Pj : JLeakParams) {τ : String → String} {d : Nat} {S : Nat → Prop}
    {out : String} {invTys : Ctxt jasminDialect} {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hops : ComOpsPlain update)
    (hτ : CanonRen τ d invTys.length S out)
    (hcert : ThreadCert τ (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < invTys.length ∧ r = τ (argName j))
    (invs : Ctxt.Valuation invTys) (fn : String) (c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (pullM τ (b0.setReg (loopIdx d) (0#64))) (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < invTys.length → (b0.reg.getW (τ (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64) (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m))
    {ℓ : List CTLeak}
    (hr : FRun (singletonProgM fn (canonNodeRM τ d out c update absent regs))
      { prog := { base := b0, lfn := fn }, zf := zf } ℓ) :
    ℓ = canonLoopLeak Pj τ update invs arr0 m := by
  have hBlopn := canonBodyRM_isLopn τ d out update absent regs
  have hpre : ∀ i ∈ canonSeedsRM d out c, IsLopn i := by
    intro i hi
    simp only [canonSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  have hseedsQ : straightLeakFF (canonSeedsRM d out c) b0 zf = [] := by
    refine straightLeakFF_quiet _ (fun i hi r => ?_) _ _
    simp only [canonSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl
  obtain ⟨b3, hseeds, hl3, hr3, hc3⟩ := canonSeedsRM_run d out c hc b0 zf
  have hargCtr : ∀ j, j < invTys.length + 2 → τ (argName j) ≠ loopCtr d := by
    intro j hj
    by_cases h1 : j = invTys.length + 1
    · subst h1; rw [hτ.acc]; exact hτ.outCtr
    · by_cases h2 : j = invTys.length
      · subst h2; rw [hτ.idx]; exact hτ.idxCtr
      · exact hτ.invCtr j (by omega)
  have hAg3 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ b3)
      (tripValArrMN invs 0 arr0) := by
    refine StoreAgreesM.congr_args rfl hseed ?_ ?_
    · intro j hj w'
      rw [pullM_getW, pullM_getW]
      exact hr3 _ w' (hargCtr j hj)
    · intro j hj w' n'
      rw [pullM_getArr, pullM_getArr, LstateM.getArr_setReg]
      exact JasminLsemMemSourceTieUncond.LstateM.getArr_congr_larr hl3 _ _ _
  have hinv3 : ∀ j, j < invTys.length → (b3.reg.getW (τ (argName j)) 64).isSome := by
    intro j hj
    rw [hr3 _ 64 (hτ.invCtr j hj), LstateM.reg_setReg,
      LstateN.getW_setReg_other _ _ _ _ _ (hτ.invIdx j hj)]
    exact hinv j hj
  have hv3 : b3.reg.getW (loopCtr d) 64 = some (BitVec.ofNat 64 m) := (hc3 64).trans hcnt
  have hP : canonNodeRM τ d out c update absent regs
      = canonSeedsRM d out c ++ guardedFlagLoopLinstrRM d (d + 0x40000000) (loopCtr d)
          (canonBodyRM τ d out update absent regs) := rfl
  rw [hP] at hr
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hendL : findLabelMem (d + 0x40000000) (canonSeedsRM d out c
        ++ guardedFlagLoopLinstrRM d (d + 0x40000000) (loopCtr d)
          (canonBodyRM τ d out update absent regs))
        = some ((canonSeedsRM d out c).length
          + (canonBodyRM τ d out update absent regs).length + 5) := by
      rw [findLabelMem_canonSeedsRM, findLabelMem_guarded_endL _ _ _ _ hBlopn
        (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide)))]
      simp only [Option.map_some, canonSeedsRM, List.length_cons, List.length_nil]
      congr 1
      omega
    rw [gNode_leak_zero fn _ _ _ _ _ hpre hendL b0 zf hpc (b3, zf) hseeds hv3 hr, hseedsQ]
    simp [canonLoopLeak, iterLeak]
  · have htopL : findLabelMem d (canonSeedsRM d out c
        ++ guardedFlagLoopLinstrRM d (d + 0x40000000) (loopCtr d)
          (canonBodyRM τ d out update absent regs))
        = some ((canonSeedsRM d out c).length + 2) := by
      rw [findLabelMem_canonSeedsRM, findLabelMem_guarded_top]
      rfl
    have hl3' : b3.lpc = 3 := by
      have := JasminLsemMemFlagNestJoin.runStraightF_lpc _ b0 zf b3 zf hseeds
      rw [this, hpc]
      rfl
    set q := (canonSeedsRM d out c).length + 3 with hq
    have hq6 : q = 6 := rfl
    have hrunB := canonBodyRM_run update hupd hτ hcert absent regs hregs invs q
      (b3.setLpc q) arr0
      (by rw [pullM_setLpc]; exact StoreAgreesM.setLpc hAg3 _)
      (fun j hj => by rw [getW_setLpc]; exact hinv3 j hj)
      (BitVec.ofNat 64 m) (by rw [getW_setLpc]; exact hv3)
    have hpass : ∀ i bi, runBoundedStraightF (canonBodyRM τ d out update absent regs) q i
        (b3.setLpc q) = some bi → ∀ bz,
        runStraightF (canonBodyRM τ d out update absent regs) bi false = some bz →
        bz.1.reg.getW (loopCtr d) 64 = some (BitVec.ofNat 64 m - BitVec.ofNat 64 (i + 1)) := by
      intro i bi hbi bz hbz
      obtain ⟨bi1, hbi1, -, -, hn1⟩ := hrunB (i + 1)
      rw [runBoundedStraightF_succ_right, hbi, Option.bind_some, hbz, Option.map_some,
        Option.some.injEq] at hbi1
      rw [← hbi1, getW_setLpc] at hn1
      exact hn1
    have hL := gNode_leak_pos fn _ _ _ _ _ hpre hBlopn htopL b0 zf hpc (b3, zf) hseeds
      (BitVec.ofNat 64 m) hv3
      (by simpa using JasminLsemMemFlagArrLoop.ofNat_sub_ofNat_ne_zero m 0 hm64 hm)
      (m - 1)
      (fun i hi bi hbi bz hbz => ⟨_, hpass i bi hbi bz hbz, by
        simpa using JasminLsemMemFlagArrLoop.ofNat_sub_ofNat_ne_zero m (i + 1) hm64 (by omega)⟩)
      (by
        obtain ⟨bk, hbk, -, -, -⟩ := hrunB (m - 1)
        obtain ⟨bm, hbm, -, -, -⟩ := hrunB m
        rw [show m = (m - 1) + 1 from by omega, runBoundedStraightF_succ_right, hbk,
          Option.bind_some] at hbm
        obtain ⟨bz, hbz, -⟩ := Option.map_eq_some_iff.mp hbm
        refine ⟨bk, hbk, bz, hbz, ?_⟩
        rw [hpass (m - 1) bk hbk bz hbz, show m - 1 + 1 = m from by omega]
        simp)
      hr
    have hL' : ℓ = [] ++ [.branch false] ++ passLeak (canonBodyRM τ d out update absent regs)
        (loopCtr d) q (m - 1 + 1) (b3.setLpc q) := by
      rw [hL, hseedsQ]
    rw [hL', passLeak_canon Pj update hupd hops hτ hcert absent regs hregs invs q m hm64 (m - 1) 0
        (b3.setLpc q) arr0 (by omega) (by rw [pullM_setLpc]; exact StoreAgreesM.setLpc hAg3 _)
        (fun j hj => by rw [getW_setLpc]; exact hinv3 j hj)
        (by rw [getW_setLpc, hv3]; simp)]
    simp only [canonLoopLeak, List.range_eq_range', show m - 1 + 1 = m from by omega,
      decide_eq_false (show ¬ m = 0 from by omega), List.nil_append, List.singleton_append]

/-! ## 9. The immediate-shift expansion -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (immShiftExpand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (InstrOK EqPc)

/-- The instruction the immediate-shift expansion sends an instruction to. -/
def shiftImage (i : LinstrRM) : LinstrRM := (immShiftExpand i).headD i

/-- The expansion of an instruction is a single instruction. -/
theorem immShiftExpand_eq (i : LinstrRM) : immShiftExpand i = [shiftImage i] := by
  unfold shiftImage immShiftExpand
  split
  · split <;> rfl
  · rfl

/-- The expansion of a body is the body mapped by `shiftImage`. -/
theorem flatMap_immShiftExpand (body : List LinstrRM) :
    body.flatMap immShiftExpand = body.map shiftImage := by
  induction body with
  | nil => rfl
  | cons i is ih => rw [List.flatMap_cons, immShiftExpand_eq, ih]; rfl

/-- The expansion keeps the events of an instruction. -/
theorem instrLeakF_shiftImage (i : LinstrRM) (s : LstateMF) :
    instrLeakF (shiftImage i) s = instrLeakF i s := by
  unfold shiftImage immShiftExpand
  split
  · split <;> simp [instrLeakF, instrLeakB, opLeakF, flagCondCC?]
  · rfl

/-- The expansion keeps labels and their positions. -/
theorem findLabelMem_map_shiftImage (l : LLabel) (body : List LinstrRM) :
    findLabelMem l (body.map shiftImage) = findLabelMem l body := by
  have h : ∀ i : LinstrRM,
      JasminLsemLabeled.isLabel l (shiftImage i).1 = JasminLsemLabeled.isLabel l i.1 := by
    intro i
    unfold shiftImage immShiftExpand
    split
    · split <;> rfl
    · rfl
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_map, List.findIdx?_map, List.findIdx?_map]
  congr 1
  funext i
  exact h i

/-- The flag machine's step depends on the program through its function name and its label
    positions only. -/
theorem evalInstrPMemF_congr {P P' : LprogM} (hfn : P.lfn = P'.lfn)
    (hl : ∀ l, findLabelMem l P.body = findLabelMem l P'.body) (i : LinstrRM) (s : LstateMF) :
    evalInstrPMemF P i s = evalInstrPMemF P' i s := by
  have hj : ∀ l (p : LstatePM), evalJumpMem P l p = evalJumpMem P' l p := by
    intro l p
    unfold evalJumpMem
    rw [hl]
  have hL : ∀ (p : LstatePM), evalInstrPMemL P i p = evalInstrPMemL P' i p := by
    intro p
    unfold evalInstrPMemL
    split <;> simp only [hj, hfn]
  unfold evalInstrPMemF
  simp only [hj, hL]

/-- `setLpc` at the program counter a state holds is the identity. -/
theorem LstateM.setLpc_self (t : LstateM) : t.setLpc t.lpc = t := rfl

/-- **The expansion on the traced flag machine.** A terminating traced run of a singleton
    program whose instructions satisfy the per-instruction condition of the immediate-shift
    expansion is a terminating traced run of the expanded program, with the same final state
    and the same trace. -/
theorem lsemFuelMemFLeak_expand (fn : String) (body : List LinstrRM)
    (hbody : ∀ i ∈ body, InstrOK EqPc immShiftExpand i) :
    ∀ (f : Nat) (s : LstateMF) (r : LstateMF × List CTLeak),
      lsemFuelMemFLeak (singletonProgM fn body) f s = some r →
      lsemFuelMemFLeak (singletonProgM fn (body.flatMap immShiftExpand)) f s = some r := by
  have hfetch : ∀ (p : LstatePM), findInstrMem (singletonProgM fn (body.flatMap immShiftExpand)) p
      = (findInstrMem (singletonProgM fn body) p).map shiftImage := by
    intro p
    by_cases h : p.lfn = fn <;>
      simp [findInstrMem, singletonProgM, h, flatMap_immShiftExpand, List.getElem?_map]
  have hev : ∀ (i : LinstrRM) (s : LstateMF),
      evalInstrPMemF (singletonProgM fn (body.flatMap immShiftExpand)) i s
        = evalInstrPMemF (singletonProgM fn body) i s := by
    intro i s
    refine evalInstrPMemF_congr (P := singletonProgM fn (body.flatMap immShiftExpand))
      (P' := singletonProgM fn body) rfl (fun l => ?_) i s
    show findLabelMem l (body.flatMap immShiftExpand) = findLabelMem l body
    rw [flatMap_immShiftExpand, findLabelMem_map_shiftImage]
  intro f
  induction f with
  | zero =>
      intro s r h
      simp only [lsemFuelMemFLeak, hfetch] at h ⊢
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none => rw [hf] at h; simpa using h
      | some i => rw [hf] at h; cases h
  | succ n ih =>
      intro s r h
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          rw [lsemFuelMemFLeak_halt _ _ _ hf] at h
          rw [lsemFuelMemFLeak_halt _ _ _ (by rw [hfetch, hf]; rfl)]
          exact h
      | some i =>
          have hmem : i ∈ body := by
            unfold findInstrMem at hf
            split at hf
            · exact List.mem_of_getElem? hf
            · cases hf
          cases he : evalInstrPMemF (singletonProgM fn body) i s with
          | none => simp [lsemFuelMemFLeak, hf, he] at h
          | some s' =>
              rw [lsemFuelMemFLeak_step _ _ _ _ _ hf he] at h
              obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
              have he' : evalInstrPMemF (singletonProgM fn (body.flatMap immShiftExpand))
                  (shiftImage i) s = some s' := by
                rw [hev]
                rcases hbody i hmem with ⟨hi, hj, hsim⟩ | ⟨hx, -⟩
                · rw [evalInstrPMemF_isLopn _ i _ hi] at he
                  obtain ⟨tz, htz, rfl⟩ := Option.map_eq_some_iff.mp he
                  obtain ⟨t', hrun, hq'⟩ := hsim s.prog.base s.prog.base tz.1 s.zf tz.2 rfl htz
                  have hj' : IsLopn (shiftImage i) := hj _ (by rw [immShiftExpand_eq]; simp)
                  have hst : fstepF (shiftImage i) s.prog.base s.zf = some (t', tz.2) := by
                    rw [immShiftExpand_eq, runStraightF_cons] at hrun
                    cases hs : fstepF (shiftImage i) s.prog.base s.zf with
                    | none => rw [hs] at hrun; cases hrun
                    | some bz =>
                        rw [hs, Option.bind_some] at hrun
                        simp only [runStraightF, Option.some.injEq] at hrun
                        exact congrArg some hrun
                  have hl1 := fstepF_lpc_succ i _ _ _ _ htz
                  have hl2 := fstepF_lpc_succ _ _ _ _ _ hst
                  have ht : t' = tz.1 := by
                    rw [hq', show t'.lpc = tz.1.lpc from by omega, LstateM.setLpc_self]
                  rw [evalInstrPMemF_isLopn _ _ _ hj', hst, ht]
                  rfl
                · have hsi : shiftImage i = i := by
                    unfold shiftImage
                    rw [hx]
                    rfl
                  rw [hsi, he]
              rw [lsemFuelMemFLeak_step _ _ _ _ _ (by rw [hfetch, hf]; rfl) he', ih s' q hq,
                instrLeakF_shiftImage]
              rfl

/-! ## 10. The transformer of the loop node -/

/-- The number of events of a program: the sum of `kindLen` over its bindings. -/
def comLeakLen (M : LeakModel jasminDialect) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var e body => kindLen (M.kind e.op) + comLeakLen M body

/-- The number of events of a program does not depend on the valuation. -/
theorem comCtLeak_length (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) :
    ∀ V : Ctxt.Valuation Γ, (Com.ctLeak M c V).length = comLeakLen M c := by
  induction c with
  | ret v => intro V; rfl
  | var e body ih =>
      intro V
      rw [comCtLeak_var, List.length_append, ih]
      show (opLeak M e.op _).length + _ = _
      rw [opLeak_length]
      rfl

/-- The passes of the loop transformer: per pass, the image `f t` of the next `L` source
    events, then the back-edge branch of pass `t` of `m`. -/
def loopChunks (m L : Nat) (f : Nat → List CTLeak → List CTLeak) :
    Nat → Nat → List CTLeak → List CTLeak
  | _, 0, _ => []
  | t, k + 1, ℓ =>
      f t (ℓ.take L) ++ [.branch (decide (t + 1 < m))] ++ loopChunks m L f (t + 1) k (ℓ.drop L)

/-- **The leakage transformer of the loop node.** From the source events `trip m :: ℓ` of a
    runtime-count loop over `update`: the zero-trip branch, then per pass the transformer
    `straightT` of the `comLeakLen` events of the pass with array bases renamed by `τ`, and
    the back-edge branch. A function of the program, the renaming and the source trace. -/
def loopT (Pj : JLeakParams) (τ : String → String) {invTys : Ctxt jasminDialect}
    {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n)) :
    List CTLeak → List CTLeak
  | .trip m :: ℓ =>
      .branch (decide (m = 0)) ::
        loopChunks m (comLeakLen (jLeakModel Pj) update)
          (fun _ c => (straightT Pj (invTys.length + 2) update (invTys.length + 2) c).map
            (renEv τ)) 0 m ℓ
  | _ => []

/-- The passes of the transformer on the source passes are the machine passes. -/
theorem loopChunks_iterLeak (Pj : JLeakParams) (τ : String → String)
    {invTys : Ctxt jasminDialect} {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : Ctxt.Valuation invTys) (m : Nat) :
    ∀ (k t : Nat) (acc : Fin n → BitVec w),
      loopChunks m (comLeakLen (jLeakModel Pj) update)
          (fun _ c => (straightT Pj (invTys.length + 2) update (invTys.length + 2) c).map
            (renEv τ)) t k
          (iterLeak (fun t acc => Com.ctLeak (jLeakModel Pj) update (tripValArrMN invs t acc))
            (fun t acc => JLoopBodyN.stepC update invs t acc) (List.range' t k) acc)
        = iterLeak (machPass Pj τ update invs m) (fun t acc => JLoopBodyN.stepC update invs t acc)
            (List.range' t k) acc := by
  intro k
  induction k with
  | zero => intro t acc; rfl
  | succ k ih =>
      intro t acc
      have hl := comCtLeak_length (jLeakModel Pj) update (tripValArrMN invs t acc)
      rw [show List.range' t (k + 1) = t :: List.range' (t + 1) k from rfl, iterLeak, iterLeak,
        loopChunks, List.take_left' hl, List.drop_left' hl, ih]
      simp only [machPass, List.append_assoc]

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (forLoopLcmdNRtRM invRegsOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (LoopRen)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon (NodeRen canonNodeRM_faithful)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd
  (ComExpOK forLoopLcmdNRtRM_map_eq_canonNodeRM_expand canonNodeRM_instrOK)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieEmitted (invRegs_eq_comp)

/-- **The leakage of the emitted runtime-count loop node.** Under the hypotheses of
    `JasminLsemMemSourceTieEmitted.forLoopLcmdNRtRM_export_faithful_comL`, every terminating
    traced run of the typed export node renamed by `ρ`, from the entry state, emits `loopT`
    of the source events of `ComL.forLoopNRt` at `V`. -/
theorem chainLeak_of_denote (Pj : JLeakParams) {Γ : Ctxt jasminDialect}
    {d w n : Nat} {invTys : Ctxt jasminDialect} {σ ρ : String → String} {S : Nat → Prop}
    {acc out c : String}
    (invOps : List LOperand)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hσ : LoopRen σ d invTys.length acc (invRegsOf invOps))
    (hρ : NodeRen ρ d acc out c (invRegsOf invOps))
    (hret : ρ (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 = out)
    (hτ : CanonRen (ρ ∘ σ) d invTys.length S out)
    (hcert : ThreadCert (ρ ∘ σ) (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (pullM (ρ ∘ σ) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hinv : ∀ j, j < invTys.length → (b0.reg.getW ((ρ ∘ σ) (argName j)) 64).isSome)
    (hcnt : b0.reg.getW c 64 = some (count.lookup V)) {ℓ : List CTLeak}
    (hr : FRun (singletonProgM fn
        ((forLoopLcmdNRtRM d acc (.reg out) (.reg c) update invOps (fun _ => none)).map
          (renRM ρ))) { prog := { base := b0, lfn := fn }, zf := zf } ℓ) :
    ℓ = loopT Pj (ρ ∘ σ) update
      (ComL.ctLeak (jLeakModel Pj) (ComL.forLoopNRt update count initV invsV (.ret .here)) V) := by
  have hcnt' : b0.reg.getW c 64 = some (BitVec.ofNat 64 (count.lookup V).toNat) := by
    rw [hcnt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hops : ComOpsPlain update := ComExpOK.opsPlain _ hexp
  set absent := (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 == acc with habsent
  obtain ⟨k, t, hrun, -⟩ := canonNodeRM_faithful update hupd hτ hcert absent (invRegsOf invOps)
    (invRegs_eq_comp hσ hρ) (Expr.lookupArgs invsV V) fn c hc b0 zf hpc (initV.lookup V) hseed
    hinv (count.lookup V).toNat (count.lookup V).isLt hcnt'
  have hfst := lsemFuelMemFLeak_fst (singletonProgM fn
    (canonNodeRM (ρ ∘ σ) d out c update absent (invRegsOf invOps))) k
    { prog := { base := b0, lfn := fn }, zf := zf }
  rw [hrun] at hfst
  obtain ⟨r0, hr0, hr0t⟩ := Option.map_eq_some_iff.mp hfst
  have hcanon := canonNode_leak Pj update hupd hops hτ hcert absent (invRegsOf invOps)
    (invRegs_eq_comp hσ hρ) (Expr.lookupArgs invsV V) fn c hc b0 zf hpc (initV.lookup V)
    hseed hinv (count.lookup V).toNat (count.lookup V).isLt hcnt' (ℓ := r0.2) ⟨k, r0.1, hr0⟩
  have hexpd := lsemFuelMemFLeak_expand fn _
    (canonNodeRM_instrOK _ d out c update hexp _ _) k _ r0 hr0
  rw [← forLoopLcmdNRtRM_map_eq_canonNodeRM_expand invOps update hops hσ hρ hret] at hexpd
  rw [fRun_unique hr ⟨k, r0.1, hexpd⟩, hcanon]
  simp only [ComL.ctLeak, canonLoopLeak, loopT, List.append_nil]
  rw [List.range_eq_range']
  have := loopChunks_iterLeak Pj (ρ ∘ σ) update (Expr.lookupArgs invsV V)
    (count.lookup V).toNat (count.lookup V).toNat 0 (initV.lookup V)
  rw [← this]
  rfl

/-- **Constant time of the emitted loop node from the source.** Under the hypotheses of
    `chainLeak_of_denote` at two valuations with equal source events, the terminating
    traced runs of the node from their entry states have equal traces. -/
theorem chainLeak_eq_of_ctLeak_eq (Pj : JLeakParams) {Γ : Ctxt jasminDialect}
    {d w n : Nat} {invTys : Ctxt jasminDialect} {σ ρ : String → String} {S : Nat → Prop}
    {acc out c : String}
    (invOps : List LOperand)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hσ : LoopRen σ d invTys.length acc (invRegsOf invOps))
    (hρ : NodeRen ρ d acc out c (invRegsOf invOps))
    (hret : ρ (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 = out)
    (hτ : CanonRen (ρ ∘ σ) d invTys.length S out)
    (hcert : ThreadCert (ρ ∘ σ) (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (fn : String) (hc : c ≠ loopIdx d)
    {V₁ V₂ : Ctxt.Valuation Γ}
    (hV : ComL.ctLeak (jLeakModel Pj) (ComL.forLoopNRt update count initV invsV (.ret .here)) V₁
      = ComL.ctLeak (jLeakModel Pj) (ComL.forLoopNRt update count initV invsV (.ret .here)) V₂)
    {b₁ b₂ : LstateM} {zf₁ zf₂ : Bool} (hpc₁ : b₁.lpc = 0) (hpc₂ : b₂.lpc = 0)
    (hseed₁ : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (pullM (ρ ∘ σ) (b₁.setReg (loopIdx d) (0#64)))
      (tripValArrMN (Expr.lookupArgs invsV V₁) 0 (initV.lookup V₁)))
    (hseed₂ : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (pullM (ρ ∘ σ) (b₂.setReg (loopIdx d) (0#64)))
      (tripValArrMN (Expr.lookupArgs invsV V₂) 0 (initV.lookup V₂)))
    (hinv₁ : ∀ j, j < invTys.length → (b₁.reg.getW ((ρ ∘ σ) (argName j)) 64).isSome)
    (hinv₂ : ∀ j, j < invTys.length → (b₂.reg.getW ((ρ ∘ σ) (argName j)) 64).isSome)
    (hcnt₁ : b₁.reg.getW c 64 = some (count.lookup V₁))
    (hcnt₂ : b₂.reg.getW c 64 = some (count.lookup V₂)) {ℓ₁ ℓ₂ : List CTLeak}
    (r₁ : FRun (singletonProgM fn
        ((forLoopLcmdNRtRM d acc (.reg out) (.reg c) update invOps (fun _ => none)).map
          (renRM ρ))) { prog := { base := b₁, lfn := fn }, zf := zf₁ } ℓ₁)
    (r₂ : FRun (singletonProgM fn
        ((forLoopLcmdNRtRM d acc (.reg out) (.reg c) update invOps (fun _ => none)).map
          (renRM ρ))) { prog := { base := b₂, lfn := fn }, zf := zf₂ } ℓ₂) :
    ℓ₁ = ℓ₂ := by
  rw [chainLeak_of_denote Pj invOps update hupd hexp hσ hρ hret hτ hcert count initV invsV V₁ fn
      hc b₁ zf₁ hpc₁ hseed₁ hinv₁ hcnt₁ r₁,
    chainLeak_of_denote Pj invOps update hupd hexp hσ hρ hret hτ hcert count initV invsV V₂ fn
      hc b₂ zf₂ hpc₂ hseed₂ hinv₂ hcnt₂ r₂, hV]

/-! ## 11. The single-loop export from ABI entries -/

section Abi

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert (exportCertB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (singleLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
  (certNode loopCertB loopCertB_spec loopInvOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
  (AbiValOf AbiEntryM storeAgreesM_of_abi certSeed_of_storeAgreesM invRegsOf_mem)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)

/-- **The leakage of the certified single-loop export from an ABI entry.** For the program
    with one runtime-count loop node that passes `loopCertB`, whose update is in `ArrMemN`
    with `ComExpOK`, every terminating traced run of `certNode` from an ABI entry of `sa`
    emits `loopT` of the source events at the valuation `σ` reads off `sa`. -/
theorem singleLoop_leak_abi (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    (σ : AbiLayout) (sa : Ascent.AddrMem.AState) (V : Ctxt.Valuation Γ) (fn : String)
    (b0 : LstateM) (zf : Bool) (hV : AbiValOf σ sa V) (hb : AbiEntryM σ sa b0)
    {ℓ : List CTLeak}
    (hr : FRun (singletonProgM fn (certNode update invs out c))
      { prog := { base := b0, lfn := fn }, zf := zf } ℓ) :
    ℓ = loopT Pj (X86Backend.ExportCertFaithful.certTau Γ.length (regName Γ.length) out update
        (loopInvOps invs)) update
      (ComL.ctLeak (jLeakModel Pj) (singleLoop update count init invs) V) := by
  obtain ⟨out', c', hi', hc', hx, -⟩ := loopCertB_spec hcert
  rw [hi] at hi'
  cases hi'
  rw [hcn] at hc'
  cases hc'
  have hag := storeAgreesM_of_abi hV hb
  have hX := exportCertB_sound hx
  have hinv : ∀ j, j < invTys.length → (b0.reg.getW
      (X86Backend.ExportCertFaithful.certTau Γ.length (regName Γ.length) out update
        (loopInvOps invs) (argName j)) 64).isSome := by
    intro j hj
    have hmem : JasminLsemExportCert.certSigma Γ.length invTys.length (regName Γ.length)
        (invRegsOf (loopInvOps invs)) (argName j) ∈ invRegsOf (loopInvOps invs) := by
      rw [JasminLsemExportCert.certSigma_inv hj]
      exact JasminLsemExportCert.getD_mem_of_lt (by rw [hX.loopRen.len]; omega) _
    show (b0.reg.getW (JasminLsemExportCert.certRho Γ.length (regName Γ.length) out
      (JasminLsemExportCert.certSlots update)
      (JasminLsemExportCert.certSigma Γ.length invTys.length (regName Γ.length)
        (invRegsOf (loopInvOps invs)) (argName j))) 64).isSome
    rw [hX.nodeRen.invFix _ hmem]
    obtain ⟨t, v, hrv⟩ := invRegsOf_mem invs _ hmem
    rw [hrv]
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hV.arg v)
    rw [hb.reg _ _ ha]
    rfl
  have hcnt : b0.reg.getW c 64 = some (count.lookup V) := by
    have hg := hag.reg count
    rw [hcn, evalOperandN] at hg
    exact hg
  exact chainLeak_of_denote Pj (loopInvOps invs) update hupd hexp hX.loopRen hX.nodeRen hX.ret
    hX.canon hX.thread count init invs V fn hX.cntIdx b0 zf hb.pc
    (certSeed_of_storeAgreesM update init invs hi hx V b0 hag) hinv hcnt hr

/-- **Constant time of the certified single-loop export transfers to the flag machine.** If
    the source events of the single-loop program are constant time for the labels `L`, its
    certified node is constant time on the flag machine from ABI entries. -/
theorem singleLoop_abiEntryCT (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    (σ : AbiLayout) (L : Labels Γ) (fn : String)
    (hct : CT.ConstantTime (PubEqV L)
      (ComL.ctLeak (jLeakModel Pj) (singleLoop update count init invs))) :
    AbiEntryCT (singletonProgM fn (certNode update invs out c)) fn σ L := by
  rintro ⟨sa₁, V₁, b₁⟩ ⟨sa₂, V₂, b₂⟩ ℓ₁ ℓ₂ ⟨hV₁, hb₁, hV₂, hb₂, hp⟩ r₁ r₂
  rw [singleLoop_leak_abi Pj update count init invs outArg inArgs abiArgs hupd hexp hcert out c
      hi hcn σ sa₁ V₁ fn b₁ false hV₁ hb₁ r₁,
    singleLoop_leak_abi Pj update count init invs outArg inArgs abiArgs hupd hexp hcert out c
      hi hcn σ sa₂ V₂ fn b₂ false hV₂ hb₂ r₂, hct V₁ V₂ hp]

end Abi

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop
