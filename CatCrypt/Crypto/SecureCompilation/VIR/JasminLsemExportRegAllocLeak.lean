/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak

@[expose] public section

set_option autoImplicit false

/-!
# The leakage of a body renamed under a liveness certificate

`JasminLsemExportRegAlloc.lsemFuelMemF_live` matches a halting run of a program `P` by a run
of a program `P'` that holds the instructions of `P` renamed by `σ`, under a liveness
certificate `LiveCert`. This module states the same simulation for the traced flag machine
`lsemFuelMemFLeak`, and the transport of constant time `MemFCT` across three steps that
rewrite a body behind a prefix of operations: the renaming under a liveness certificate, the
coalescing of array names, and the renaming by pairs behind their copies.

The renaming `renRM σ` renames the base and the index of an indexed array operand and keeps
a compile-time array element. The two runs read equal index values, so the event of an
indexed operand has its base renamed by `σ` and the same offset. The event of a compile-time
element is kept; it is its own image under `renEv σ` when `σ` fixes its base. A conditional
on the zero flag emits the same branch event in both runs. The trace of the renamed run is
the trace of the original mapped by `renEv σ`.

## Main definitions

* `idxNames`, `cArrBases`: the index registers and the compile-time array bases of the
  operands whose events an instruction emits.
* `LeakCert`, `leakLiveB`: the index registers are related before each step and `σ` fixes
  the compile-time array bases; the check of one instruction.
* `LiveStart`, `LivePub`: the entry states `lsemFuelMemF_live` relates, and the
  public-equality relation of the renamed program.
* `EntryAt`, `SimPub`: a state at position `0` of a function, and public-equal states of a
  set from each of which the original program has a terminating run.
* `RenStart`: the array condition of `renameLoop_sim` at an entry state.

## Main results

* `instrLeakF_live`: the events of the renamed instruction from a related state.
* `lsemFuelMemFLeak_live`, `fRun_live`, `memFCT_live`: the traced run under a liveness
  certificate and the transport of constant time.
* `fRun_live_prefix`, `memFCT_live_prefix`: the same for code behind a prefix of operations,
  from one state at position `0`.
* `fRun_coalesce_prefix`, `memFCT_coalesce_prefix`: the coalescing of the code behind a
  prefix of operations.
* `fRun_renameLoop`, `memFCT_renameLoop`: the renaming by pairs behind their copies.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAllocLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_lpc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK shiftS)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR
  renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf
  lsemFuelMemF_seg_fuel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (renEv straightLeakFF
  straightLeakFF_quiet lsemFuelMemFLeak_segF)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (coCfgB renArr ctlOK_renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak (leakFixCfgB
  lsemFuelMemFLeak_coalesce)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (NoCArr renameLoop_leak
  lsemFuelMemFLeak_prefix_eq)

variable {σ : String → String}

/-! ## 1. The events of a renamed instruction -/

/-- The index register of an indexed array operand. -/
def idxNamesOf : LOperand → List String
  | .arrIdx _ x _ => [x]
  | _ => []

/-- The base of a compile-time array element. -/
def cArrBasesOf : LOperand → List String
  | .arr b _ => [b]
  | _ => []

/-- The index registers of the operands whose events an instruction emits: those of the
    indexed array operands of an `Lopn` other than a load-effective-address `LEA`. -/
def idxNames : LinstrR → List String
  | .Lopn ds o ss => if stripWidthTag o = "LEA" then [] else (ds ++ ss).flatMap idxNamesOf
  | _ => []

/-- The bases of the compile-time array elements whose events an instruction emits: those of
    the operands of an `Lopn` other than a load-effective-address `LEA`. -/
def cArrBases : LinstrR → List String
  | .Lopn ds o ss => if stripWidthTag o = "LEA" then [] else (ds ++ ss).flatMap cArrBasesOf
  | _ => []

/-- The event of a renamed operand, at a register file that holds at the image of the index
    register the cell of the index register, for a renaming that fixes the base of a
    compile-time element: the event of the operand with its base renamed. -/
theorem opLeakF_ren (r r' : LstateN) (o : LOperand)
    (hx : ∀ x ∈ idxNamesOf o, r'.lvm (σ x) = r.lvm x) (hb : ∀ b ∈ cArrBasesOf o, σ b = b) :
    opLeakF r' (renOperand σ o) = (opLeakF r o).map (renEv σ) := by
  cases o with
  | reg q => rfl
  | imm v => rfl
  | arr b k =>
      have hfix := hb b (by simp [cArrBasesOf])
      simp [opLeakF, renOperand, renEv, hfix]
  | arrIdx b q sc =>
      have hq := hx q (by simp [idxNamesOf])
      simp only [opLeakF, renOperand, renEv, idxVal, List.map_cons, List.map_nil]
      rw [hq]

/-- The events of a renamed instruction that is not a conditional, at a register file that
    holds at the image of each index register the cell of that register, for a renaming that
    fixes the compile-time array bases: the events of the instruction with renamed bases. -/
theorem instrLeakB_live (r r' : LstateN) (i : LinstrRM)
    (hnc : ∀ c l, i.1 ≠ LinstrR.Lcond c l)
    (hx : ∀ x ∈ idxNames i.1, r'.lvm (σ x) = r.lvm x) (hb : ∀ b ∈ cArrBases i.1, σ b = b) :
    instrLeakB r' (renRM σ i) = (instrLeakB r i).map (renEv σ) := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o ss =>
      simp only [idxNames, cArrBases] at hx hb
      simp only [instrLeakB, renRM, renLinstrR, ← List.map_append, List.flatMap_map]
      split_ifs with hlea
      · rfl
      · rw [ite_eq_right hlea] at hx hb
        rw [List.map_flatMap]
        exact List.flatMap_congr fun op hop =>
          opLeakF_ren r r' op (fun x hx' => hx x (List.mem_flatMap.mpr ⟨op, hop, hx'⟩))
            (fun b hb' => hb b (List.mem_flatMap.mpr ⟨op, hop, hb'⟩))
  | Lcond c l => exact absurd rfl (hnc c l)
  | _ => rfl

/-- **The events of an instruction renamed under a liveness relation.** For an instruction
    whose conditionals read the zero flag, whose index registers lie in `Nr` and whose
    compile-time array bases `σ` fixes, the renamed instruction emits, from a state related
    on `Nr`, the events of the instruction with renamed array bases. -/
theorem instrLeakF_live {Nr Na : String → Prop} (i : LinstrRM) (hc : CondOK i)
    (hx : ∀ x ∈ idxNames i.1, Nr x) (hb : ∀ b ∈ cArrBases i.1, σ b = b) {s s' : LstateMF}
    (hR : RelF2 σ Nr Na s s') :
    instrLeakF (renRM σ i) s' = (instrLeakF i s).map (renEv σ) := by
  unfold instrLeakF
  rw [flagCondCC?_ren]
  cases h : flagCondCC? i with
  | some p =>
      obtain ⟨pol, l⟩ := p
      simp only [hR.2.2.1]
      rfl
  | none =>
      exact instrLeakB_live _ _ i (fun c l hi => hc.1 c l hi h)
        (fun x hx' => hR.1.1.2 x (hx x hx')) hb

/-! ## 2. The traced run under a liveness certificate -/

/-- **The certificate of the events** of a program `P` renamed by `σ` from index `k0` on, at
    the register names `Lr k` related at program counter `k`: the index registers of the
    instruction at `k` lie in `Lr k`, and `σ` fixes its compile-time array bases. -/
structure LeakCert (σ : String → String) (k0 : Nat) (P : LprogM)
    (Lr : Nat → String → Prop) : Prop where
  /-- The index registers are related before the step. -/
  idx : ∀ k i, k0 ≤ k → P.body[k]? = some i → ∀ x ∈ idxNames i.1, Lr k x
  /-- The compile-time array bases are fixed. -/
  fix : ∀ k i, k0 ≤ k → P.body[k]? = some i → ∀ b ∈ cArrBases i.1, σ b = b

/-- The check of the events of one instruction against the register names `N` related before
    it: its index registers are in `N` and `σ` fixes its compile-time array bases. -/
def leakLiveB (σ : String → String) (N : List String) (i : LinstrRM) : Bool :=
  (idxNames i.1).all N.contains && (cArrBases i.1).all fun b => σ b == b

/-- A program whose instructions from `k0` on pass `leakLiveB` at the lists `Lr` has the
    certificate `LeakCert` at the membership in `Lr`. -/
theorem leakCert_of_leakLiveB {k0 : Nat} {P : LprogM} {Lr : Nat → List String}
    (h : ∀ k i, k0 ≤ k → P.body[k]? = some i → leakLiveB σ (Lr k) i = true) :
    LeakCert σ k0 P (fun k r => r ∈ Lr k) where
  idx := fun k i hk hi x hx => by
    have := (Bool.and_eq_true_iff.mp (h k i hk hi)).1
    simpa using List.all_eq_true.mp this x hx
  fix := fun k i hk hi b hb => by
    have := (Bool.and_eq_true_iff.mp (h k i hk hi)).2
    simpa using List.all_eq_true.mp this b hb

variable {k0 : Nat} {P P' : LprogM} {Lr La : Nat → String → Prop}

/-- **The traced flag machine under a liveness certificate.** For a program `P`, a renaming
    `σ` and a program `P'` with the certificates `LiveCert` and `LeakCert` from `k0` on, a
    halting traced run of `P` with trace `ℓ` from a state at program counter `k ≥ k0` is
    matched, with the same fuel, by a halting traced run of `P'` from a state related on the
    sets at `k`, into a state related on the sets at the final program counter, with the
    trace `ℓ.map (renEv σ)`. -/
theorem lsemFuelMemFLeak_live (hC : LiveCert σ k0 P P' Lr La) (hX : LeakCert σ k0 P Lr) :
    ∀ (fuel : Nat) {s s' t : LstateMF} {ℓ : List CTLeak},
      RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s' → k0 ≤ s.prog.base.lpc →
      lsemFuelMemFLeak P fuel s = some (t, ℓ) →
      ∃ t', lsemFuelMemFLeak P' fuel s' = some (t', ℓ.map (renEv σ))
        ∧ RelF2 σ (Lr t.prog.base.lpc) (La t.prog.base.lpc) t t' := by
  have hfetch : ∀ {s s' : LstateMF},
      RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s' → k0 ≤ s.prog.base.lpc →
      findInstrMem P' s'.prog = (findInstrMem P s.prog).map (renRM σ) := by
    intro s s' hR hk
    unfold findInstrMem
    rw [hR.2.1, hC.lfn]
    have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
    split
    · rw [hpc]; exact hC.body _ hk
    · rfl
  have hhalt : ∀ (fuel : Nat) {s s' t : LstateMF} {ℓ : List CTLeak},
      RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s' → k0 ≤ s.prog.base.lpc →
      findInstrMem P s.prog = none → lsemFuelMemFLeak P fuel s = some (t, ℓ) →
      ∃ t', lsemFuelMemFLeak P' fuel s' = some (t', ℓ.map (renEv σ))
        ∧ RelF2 σ (Lr t.prog.base.lpc) (La t.prog.base.lpc) t t' := by
    intro fuel s s' t ℓ hR hk hf h
    rw [lsemFuelMemFLeak_halt _ _ s hf] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨s', lsemFuelMemFLeak_halt _ _ s' (by rw [hfetch hR hk, hf]; rfl), hR⟩
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t ℓ hR hk h
      cases hf : findInstrMem P s.prog with
      | none => exact hhalt 0 hR hk hf h
      | some i => simp [lsemFuelMemFLeak, hf] at h
  | succ n ih =>
      intro s s' t ℓ hR hk h
      cases hf : findInstrMem P s.prog with
      | none => exact hhalt (n + 1) hR hk hf h
      | some i =>
          have hget : P.body[s.prog.base.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact hf
            · simp at hf
          cases he : evalInstrPMemF P i s with
          | none => simp [lsemFuelMemFLeak, hf, he] at h
          | some u =>
              rw [lsemFuelMemFLeak_step _ _ i s u hf he] at h
              obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
              obtain ⟨u', hu', hRu, hku⟩ := evalInstrPMemF_live hC i hk hget hR he
              obtain ⟨t', ht', hRt⟩ := ih hRu hku hq
              refine ⟨t', ?_, hRt⟩
              rw [lsemFuelMemFLeak_step _ _ (renRM σ i) s' u' (by rw [hfetch hR hk, hf]; rfl) hu',
                ht', Option.map_some, List.map_append,
                instrLeakF_live i (hC.cond _ i hk hget) (hX.idx _ i hk hget)
                  (hX.fix _ i hk hget) hR]

/-! ## 3. Constant time under a liveness certificate -/

/-- **The entry states of the renaming under a certificate.** `s` is at a program counter
    `k ≥ k0` and `s'` is related to `s` on the sets at `k`. -/
def LiveStart (σ : String → String) (k0 : Nat) (Lr La : Nat → String → Prop)
    (s s' : LstateMF) : Prop :=
  RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s' ∧ k0 ≤ s.prog.base.lpc

/-- **A terminating run of the renamed program.** Under the certificates, a terminating run
    of `P` from `s` with trace `ℓ` gives a terminating run of `P'` from every `s'` with
    `LiveStart σ k0 Lr La s s'`, with trace `ℓ.map (renEv σ)`. -/
theorem fRun_live (hC : LiveCert σ k0 P P' Lr La) (hX : LeakCert σ k0 P Lr)
    {s s' : LstateMF} {ℓ : List CTLeak} (hs : LiveStart σ k0 Lr La s s') (h : FRun P s ℓ) :
    FRun P' s' (ℓ.map (renEv σ)) := by
  obtain ⟨fuel, t, h⟩ := h
  obtain ⟨t', ht', -⟩ := lsemFuelMemFLeak_live hC hX fuel hs.1 hs.2 h
  exact ⟨fuel, t', ht'⟩

/-- **The public-equality relation of the renamed program.** Two states are related when
    they are the images, by `LiveStart σ k0 Lr La`, of two states related by `pubEq` from
    each of which `P` has a terminating run. -/
def LivePub (σ : String → String) (k0 : Nat) (P : LprogM) (Lr La : Nat → String → Prop)
    (pubEq : LstateMF → LstateMF → Prop) (s₁' s₂' : LstateMF) : Prop :=
  ∃ s₁ s₂, pubEq s₁ s₂ ∧ LiveStart σ k0 Lr La s₁ s₁' ∧ LiveStart σ k0 Lr La s₂ s₂'
    ∧ (∃ ℓ, FRun P s₁ ℓ) ∧ (∃ ℓ, FRun P s₂ ℓ)

/-- **Constant time of the renamed program.** Under the certificates `LiveCert` and
    `LeakCert`, constant time of `P` on the flag machine at `pubEq` gives constant time of
    `P'` at `LivePub σ k0 P Lr La pubEq`. -/
theorem memFCT_live (hC : LiveCert σ k0 P P' Lr La) (hX : LeakCert σ k0 P Lr)
    {pubEq : LstateMF → LstateMF → Prop} (hct : MemFCT P pubEq) :
    MemFCT P' (LivePub σ k0 P Lr La pubEq) := by
  rintro s₁' s₂' ℓ₁' ℓ₂' ⟨s₁, s₂, hp, h₁, h₂, ⟨ℓ₁, r₁⟩, ⟨ℓ₂, r₂⟩⟩ hr₁ hr₂
  rw [fRun_unique hr₁ (fRun_live hC hX h₁ r₁), fRun_unique hr₂ (fRun_live hC hX h₂ r₂),
    hct s₁ s₂ ℓ₁ ℓ₂ hp r₁ r₂]

/-! ## 4. Constant time across a step that keeps the entry state -/

/-- A state of the function `fn` at position `0`. -/
def EntryAt (fn : String) (s : LstateMF) : Prop := s.prog.lfn = fn ∧ s.prog.base.lpc = 0

/-- **Public-equal states of a set with terminating runs.** Two states related by `pubEq`,
    both in `G`, from each of which `P` has a terminating run. -/
def SimPub (P : LprogM) (G : LstateMF → Prop) (pubEq : LstateMF → LstateMF → Prop)
    (s₁ s₂ : LstateMF) : Prop :=
  pubEq s₁ s₂ ∧ G s₁ ∧ G s₂ ∧ (∃ ℓ, FRun P s₁ ℓ) ∧ (∃ ℓ, FRun P s₂ ℓ)

/-- **Constant time across a trace map.** If every terminating run of `P` from a state of
    `G` with trace `ℓ` gives a terminating run of `P'` from that state with trace `f ℓ`,
    constant time of `P` at `pubEq` gives constant time of `P'` at `SimPub P G pubEq`. -/
theorem memFCT_of_fRun_map {P P' : LprogM} {G : LstateMF → Prop}
    (f : List CTLeak → List CTLeak)
    (hsim : ∀ s ℓ, G s → FRun P s ℓ → FRun P' s (f ℓ))
    {pubEq : LstateMF → LstateMF → Prop} (hct : MemFCT P pubEq) :
    MemFCT P' (SimPub P G pubEq) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨hp, g₁, g₂, ⟨v₁, r₁⟩, ⟨v₂, r₂⟩⟩ hr₁ hr₂
  rw [fRun_unique hr₁ (hsim s₁ v₁ g₁ r₁), fRun_unique hr₂ (hsim s₂ v₂ g₂ r₂),
    hct s₁ s₂ v₁ v₂ hp r₁ r₂]

/-! ## 5. The traced run through a prefix of operations -/

/-- A halting traced run of `pre ++ X` from position `0`, for a prefix `pre` of operations:
    the prefix runs as `runStraightF` to a base at position `pre.length`, and the trace is
    the events of the prefix followed by the trace of the run from that base. -/
theorem lsemFuelMemFLeak_prefix_split (fn : String) (pre X : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (b0 : LstateM) (zf : Bool) (h0 : b0.lpc = 0) (fuel : Nat)
    (t : LstateMF) (ℓ : List CTLeak)
    (hrun : lsemFuelMemFLeak (singletonProgM fn (pre ++ X)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some (t, ℓ)) :
    ∃ (f : Nat) (b1 : LstateM) (z1 : Bool) (T : List CTLeak),
      runStraightF pre b0 zf = some (b1, z1) ∧ b1.lpc = pre.length
        ∧ ℓ = straightLeakFF pre b0 zf ++ T
        ∧ lsemFuelMemFLeak (singletonProgM fn (pre ++ X)) f
            { prog := { base := b1, lfn := fn }, zf := z1 } = some (t, T) := by
  have hpos : ∀ j, j < pre.length →
      (singletonProgM fn (pre ++ X)).body[b0.lpc + j]? = pre[j]? := fun j hj => by
    simp only [singletonProgM, h0, Nat.zero_add]
    exact List.getElem?_append_left hj
  have hu : lsemFuelMemF (singletonProgM fn (pre ++ X)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t := by
    rw [← lsemFuelMemFLeak_fst, hrun]
    rfl
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le
    (lsemFuelMemF_seg_fuel _ fn rfl pre b0 zf fuel t hpre hpos hu)
  cases hp : runStraightF pre b0 zf with
  | none =>
      rw [JasminLsemMemFlagNestJoin.lsemFuelMemF_segF _ fn rfl pre b0 zf f hpre hpos, hp] at hu
      cases hu
  | some bz =>
      obtain ⟨b1, z1⟩ := bz
      rw [lsemFuelMemFLeak_segF _ fn rfl pre b0 zf f (b1, z1) hpre hpos hp] at hrun
      obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
      exact ⟨f, b1, z1, q.2, rfl,
        by rw [runStraightF_lpc pre b0 zf b1 z1 hp, h0, Nat.zero_add], rfl, hq⟩

/-- A halting traced run of `pre ++ X` from the base the prefix `pre` of operations reaches
    from position `0`, with the prefix in front: the trace gains the events of the prefix. -/
theorem lsemFuelMemFLeak_prefix_join (fn : String) (pre X : List LinstrRM)
    (hpre : ∀ i ∈ pre, IsLopn i) (b0 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (b1 : LstateM) (z1 : Bool) (hp : runStraightF pre b0 zf = some (b1, z1)) (f : Nat)
    (t : LstateMF) (T : List CTLeak)
    (h : lsemFuelMemFLeak (singletonProgM fn (pre ++ X)) f
      { prog := { base := b1, lfn := fn }, zf := z1 } = some (t, T)) :
    lsemFuelMemFLeak (singletonProgM fn (pre ++ X)) (pre.length + f)
      { prog := { base := b0, lfn := fn }, zf := zf }
        = some (t, straightLeakFF pre b0 zf ++ T) := by
  have hpos : ∀ j, j < pre.length →
      (singletonProgM fn (pre ++ X)).body[b0.lpc + j]? = pre[j]? := fun j hj => by
    simp only [singletonProgM, h0, Nat.zero_add]
    exact List.getElem?_append_left hj
  rw [lsemFuelMemFLeak_segF _ fn rfl pre b0 zf f (b1, z1) hpre hpos hp, h]
  rfl

/-! ## 6. The register merge behind a prefix -/

/-- **A terminating run of code renamed behind a prefix.** Let `pre` be a prefix of
    operations and let the programs `pre ++ C` and `pre ++ C.map (renRM τ)` have the
    certificates `LiveCert` and `LeakCert` of `τ` from the first position of `C`, with `τ`
    fixing the register names and the array names related at that position. A terminating
    run of `pre ++ C` from a base at position `0` emits the events of the prefix followed by
    events `T`, and `pre ++ C.map (renRM τ)` has a terminating run from the same base with
    the events of the prefix followed by `T.map (renEv τ)`. -/
theorem fRun_live_prefix {τ : String → String} {pre C : List LinstrRM} {fn : String}
    {Lr La : Nat → String → Prop} (hpre : ∀ i ∈ pre, IsLopn i)
    (hC : LiveCert τ pre.length (singletonProgM fn (pre ++ C))
      (singletonProgM fn (pre ++ C.map (renRM τ))) Lr La)
    (hX : LeakCert τ pre.length (singletonProgM fn (pre ++ C)) Lr)
    (hr : ∀ r, Lr pre.length r → τ r = r) (ha : ∀ r, La pre.length r → τ r = r)
    (b0 : LstateM) (zf : Bool) (h0 : b0.lpc = 0) {ℓ : List CTLeak}
    (h : FRun (singletonProgM fn (pre ++ C))
      { prog := { base := b0, lfn := fn }, zf := zf } ℓ) :
    ∃ T, ℓ = straightLeakFF pre b0 zf ++ T
      ∧ FRun (singletonProgM fn (pre ++ C.map (renRM τ)))
          { prog := { base := b0, lfn := fn }, zf := zf }
          (straightLeakFF pre b0 zf ++ T.map (renEv τ)) := by
  obtain ⟨fuel, t, hrun⟩ := h
  obtain ⟨f, b1, z1, T, hp, hpc, rfl, hq⟩ :=
    lsemFuelMemFLeak_prefix_split fn pre C hpre b0 zf h0 fuel t ℓ hrun
  have hR : RelF2 τ (Lr b1.lpc) (La b1.lpc)
      { prog := { base := b1, lfn := fn }, zf := z1 }
      { prog := { base := b1, lfn := fn }, zf := z1 } := by
    rw [hpc]
    refine ⟨⟨⟨rfl, fun r hr' => ?_⟩, fun r hr' => ?_, rfl⟩, rfl, rfl, rfl, rfl⟩
    · rw [hr r hr']
    · rw [ha r hr']
  obtain ⟨t', ht', -⟩ := lsemFuelMemFLeak_live hC hX f hR (Nat.le_of_eq hpc.symm) hq
  exact ⟨T, rfl, pre.length + f, t',
    lsemFuelMemFLeak_prefix_join fn pre _ hpre b0 zf h0 b1 z1 hp f t' _ ht'⟩

/-- **Constant time of code renamed behind a prefix.** Under the hypotheses of
    `fRun_live_prefix`, for a prefix whose instructions emit no event, constant time of
    `pre ++ C` at `pubEq` gives constant time of `pre ++ C.map (renRM τ)` between
    `pubEq`-related states of the function `fn` at position `0` from each of which
    `pre ++ C` has a terminating run. -/
theorem memFCT_live_prefix {τ : String → String} {pre C : List LinstrRM} {fn : String}
    {Lr La : Nat → String → Prop} (hpre : ∀ i ∈ pre, IsLopn i)
    (hq : ∀ i ∈ pre, ∀ r, instrLeakB r i = [])
    (hC : LiveCert τ pre.length (singletonProgM fn (pre ++ C))
      (singletonProgM fn (pre ++ C.map (renRM τ))) Lr La)
    (hX : LeakCert τ pre.length (singletonProgM fn (pre ++ C)) Lr)
    (hr : ∀ r, Lr pre.length r → τ r = r) (ha : ∀ r, La pre.length r → τ r = r)
    {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (pre ++ C)) pubEq) :
    MemFCT (singletonProgM fn (pre ++ C.map (renRM τ)))
      (SimPub (singletonProgM fn (pre ++ C)) (EntryAt fn) pubEq) := by
  refine memFCT_of_fRun_map (List.map (renEv τ)) (fun s ℓ hg h => ?_) hct
  obtain ⟨⟨b0, lfn⟩, zf⟩ := s
  obtain ⟨rfl, h0⟩ := hg
  obtain ⟨T, rfl, hT⟩ := fRun_live_prefix hpre hC hX hr ha b0 zf h0 h
  rw [straightLeakFF_quiet pre hq, List.nil_append] at hT ⊢
  exact hT

/-! ## 7. The coalescing behind a prefix -/

/-- **A terminating run of code coalesced behind a prefix.** Let `pre` be a prefix of
    operations and `C` code in the classes of `CtlOK` accepted by `coCfgB ρ C L obs` and
    `leakFixCfgB ρ`, with `ρ` fixing the names `L` gives the first position. A terminating
    run of `pre ++ C` from a base at position `0` emits the events of the prefix followed by
    events `T`, and `pre ++ C.map (renArr ρ)` has a terminating run from the same base with
    the events of the prefix followed by `T.map (renEv ρ)`. -/
theorem fRun_coalesce_prefix {ρ : String → String} {fn : String} {pre C : List LinstrRM}
    {L : Nat → List String} {obs : List String} (hpre : ∀ i ∈ pre, IsLopn i)
    (hcl : ∀ i ∈ C, CtlOK i) (hc : coCfgB ρ C L obs = true) (hx : leakFixCfgB ρ C = true)
    (hfix : ∀ r ∈ L 0, ρ r = r) (b0 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    {ℓ : List CTLeak}
    (h : FRun (singletonProgM fn (pre ++ C))
      { prog := { base := b0, lfn := fn }, zf := zf } ℓ) :
    ∃ T, ℓ = straightLeakFF pre b0 zf ++ T
      ∧ FRun (singletonProgM fn (pre ++ C.map (renArr ρ)))
          { prog := { base := b0, lfn := fn }, zf := zf }
          (straightLeakFF pre b0 zf ++ T.map (renEv ρ)) := by
  obtain ⟨fuel, t, hrun⟩ := h
  obtain ⟨f, b1, z1, T, hp, hpc, rfl, hq⟩ :=
    lsemFuelMemFLeak_prefix_split fn pre C hpre b0 zf h0 fuel t ℓ hrun
  have hsh : ({ prog := { base := b1, lfn := fn }, zf := z1 } : LstateMF)
      = shiftS pre.length { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } := by
    simp only [shiftS, LstateM.lpc_setLpc, Nat.zero_add, ← hpc]
    rfl
  rw [hsh, lsemFuelMemFLeak_prefix_eq fn pre C hpre hcl] at hq
  obtain ⟨ql, hql, hqe⟩ := Option.map_eq_some_iff.mp hq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
  obtain ⟨tl', htl', -, -⟩ := lsemFuelMemFLeak_coalesce (fn := fn) hc hx f
    (s := { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 })
    (s' := { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 }) rfl (Nat.zero_le _)
    ⟨rfl, rfl, rfl, rfl, fun r hr => by rw [hfix r hr]⟩ rfl rfl hql
  have hcl' : ∀ i ∈ C.map (renArr ρ), CtlOK i := fun i hi => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact ctlOK_renArr _ (hcl j hj)
  refine ⟨ql.2, rfl, pre.length + f, shiftS pre.length tl',
    lsemFuelMemFLeak_prefix_join fn pre _ hpre b0 zf h0 b1 z1 hp f _ _ ?_⟩
  rw [hsh, lsemFuelMemFLeak_prefix_eq fn pre _ hpre hcl', htl']
  rfl

/-- **Constant time of code coalesced behind a prefix.** Under the hypotheses of
    `fRun_coalesce_prefix`, for a prefix whose instructions emit no event, constant time of
    `pre ++ C` at `pubEq` gives constant time of `pre ++ C.map (renArr ρ)` between
    `pubEq`-related states of the function `fn` at position `0` from each of which
    `pre ++ C` has a terminating run. -/
theorem memFCT_coalesce_prefix {ρ : String → String} {fn : String} {pre C : List LinstrRM}
    {L : Nat → List String} {obs : List String} (hpre : ∀ i ∈ pre, IsLopn i)
    (hq : ∀ i ∈ pre, ∀ r, instrLeakB r i = [])
    (hcl : ∀ i ∈ C, CtlOK i) (hc : coCfgB ρ C L obs = true) (hx : leakFixCfgB ρ C = true)
    (hfix : ∀ r ∈ L 0, ρ r = r) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (pre ++ C)) pubEq) :
    MemFCT (singletonProgM fn (pre ++ C.map (renArr ρ)))
      (SimPub (singletonProgM fn (pre ++ C)) (EntryAt fn) pubEq) := by
  refine memFCT_of_fRun_map (List.map (renEv ρ)) (fun s ℓ hg h => ?_) hct
  obtain ⟨⟨b0, lfn⟩, zf⟩ := s
  obtain ⟨rfl, h0⟩ := hg
  obtain ⟨T, rfl, hT⟩ := fRun_coalesce_prefix hpre hcl hc hx hfix b0 zf h0 h
  rw [straightLeakFF_quiet pre hq, List.nil_append] at hT ⊢
  exact hT

/-! ## 8. The renaming by pairs behind their copies -/

/-- **The array condition of the renaming by pairs** at an entry state: in the base the
    prefix `pre` reaches, the array of the image of each name of `N` is the array of the
    name. -/
def RenStart (pre : List LinstrRM) (ps : List (String × String)) (N : String → Prop)
    (s : LstateMF) : Prop :=
  ∀ b1 z1, runStraightF pre s.prog.base s.zf = some (b1, z1) →
    ∀ r, N r → b1.larr (renOf ps r) = b1.larr r

/-- **A terminating run of the loop renamed behind the copies.** Under the hypotheses of
    `renameLoop_sim`, for a prefix whose instructions emit no event and a loop with no
    compile-time array operand, a terminating run of `pre ++ loop` with trace `ℓ` from a
    state of the function `fn` at position `0` that meets `RenStart` gives a terminating
    run of `pre ++ movesOf ps ++ loop.map (renRM (renOf ps))` from that state with trace
    `ℓ.map (renEv (renOf ps))`. -/
theorem fRun_renameLoop (fn : String) (pre loop : List LinstrRM)
    (ps : List (String × String)) (N : String → Prop) (hpre : ∀ i ∈ pre, IsLopn i)
    (hq : ∀ i ∈ pre, ∀ r, instrLeakB r i = [])
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (ha : ∀ i ∈ loop, NoCArr i.1) {s : LstateMF}
    {ℓ : List CTLeak} (hs : EntryAt fn s) (hA : RenStart pre ps N s)
    (h : FRun (singletonProgM fn (pre ++ loop)) s ℓ) :
    FRun (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps)))) s
      (ℓ.map (renEv (renOf ps))) := by
  obtain ⟨⟨b0, lfn⟩, zf⟩ := s
  obtain ⟨rfl, h0⟩ := hs
  obtain ⟨fuel, t, hrun⟩ := h
  obtain ⟨T, rfl, fuel', t', ht'⟩ := renameLoop_leak _ pre loop ps N hpre hloop hcond hσ hn
    hnd hts hren hfresh ha b0 zf h0 hA fuel t ℓ hrun
  rw [straightLeakFF_quiet pre hq, List.nil_append] at ht' ⊢
  exact ⟨fuel', t', ht'⟩

/-- **Constant time of the loop renamed behind the copies.** Under the hypotheses of
    `fRun_renameLoop`, constant time of `pre ++ loop` at `pubEq` gives constant time of
    `pre ++ movesOf ps ++ loop.map (renRM (renOf ps))` between `pubEq`-related states of the
    function `fn` at position `0` that meet `RenStart` and from each of which `pre ++ loop`
    has a terminating run. -/
theorem memFCT_renameLoop (fn : String) (pre loop : List LinstrRM)
    (ps : List (String × String)) (N : String → Prop) (hpre : ∀ i ∈ pre, IsLopn i)
    (hq : ∀ i ∈ pre, ∀ r, instrLeakB r i = [])
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (ha : ∀ i ∈ loop, NoCArr i.1)
    {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (pre ++ loop)) pubEq) :
    MemFCT (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps))))
      (SimPub (singletonProgM fn (pre ++ loop))
        (fun s => EntryAt fn s ∧ RenStart pre ps N s) pubEq) :=
  memFCT_of_fRun_map (List.map (renEv (renOf ps)))
    (fun _ _ hg h => fRun_renameLoop fn pre loop ps N hpre hq hloop hcond hσ hn hnd hts hren
      hfresh ha hg.1 hg.2 h) hct

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAllocLeak
