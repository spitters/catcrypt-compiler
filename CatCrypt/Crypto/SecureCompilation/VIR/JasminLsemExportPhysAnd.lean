/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChainLogic
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd
public import CatCryptCore.Tactics.KatGuard
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill

/-!
# The `mpn_and_n` chain at the physical register assignment

`JasminLsemExportChainLogic.and_chain_machine_val` states the value of the
canonicalised `mpn_and_n` chain after register allocation by a renaming `σ` and
two-address lowering, under the interval certificates `RangeCert`, the jump
condition `JumpOK`, the lowering side conditions `LowerOK` and the entry relations
`RelF2` and `RelX`. This module discharges those hypotheses at the linear scan's
own assignment for the chain at loop depth `4`.

The chain is the body naming of `logicTau`: the invariant base registers are
`a0` and `a1`, the accumulator is `a3` and the count register `a2`. The
certificate conditions are stated as Boolean checks over the body (`bodyAll`,
`interfB`, `jumpOKB`, `srcB`, `ctlB`), each with a soundness lemma, so that an
instance is one kernel evaluation whose cost is linear in the body.

## Main results

* `andChain_node_eq` — the canonicalised chain at `logicTau 4 8 "a3"` is the
  literal `andChainRM`.
* `andChainSigma` — the linear scan's assignment on the chain's export command
  `andChainCmd`; the `#kat` checks it against `physSigma andChainCmd`.
* `andChain_regCert`, `andChain_arrCert`, `andChain_jumpOK_reg`,
  `andChain_jumpOK_arr`, `andChain_lowerOK`, `andChain_cond`, `andChain_uses`,
  `andChain_arrUses` — the hypotheses of `and_chain_machine_val` at the intervals
  `andRr`, `andRa`, for every renaming agreeing with `andChainSigma` on the
  chain's names.
* `and_chain_machine_val_phys` — the allocated and lowered chain computes the
  elementwise conjunction, with hypotheses on the entry state only.
* `and_chain_machine_val_physSigma` — the same at `physSigma andChainCmd`, the
  agreement with `andChainSigma` being the fact the `#kat` checks.
-/

public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportPhysAnd

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportChainLogic
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill (physRename)

/-! ## 1. Decidable forms of the certificate conditions -/

/-- The Boolean form of `LiveIn`, for a decidable input set `InB`. -/
def liveInB (rng : String → Nat × Nat) (InB : String → Bool) (k : Nat) (n : String) : Bool :=
  decide (k ≤ (rng n).2) && (decide ((rng n).1 < k) || InB n)

/-- The Boolean form of `Live`. -/
def liveB (rng : String → Nat × Nat) (InB : String → Bool) (k : Nat) (n : String) : Bool :=
  n == "" || liveInB rng InB k n

theorem liveIn_of_liveInB {rng : String → Nat × Nat} {In : String → Prop} {InB : String → Bool}
    (hIn : ∀ n, InB n = true → In n) {k : Nat} {n : String} (h : liveInB rng InB k n = true) :
    LiveIn rng In k n := by
  simp only [liveInB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  exact ⟨h.1, h.2.elim Or.inl (fun h2 => Or.inr (hIn n h2))⟩

theorem liveInB_of_liveIn {rng : String → Nat × Nat} {In : String → Prop} {InB : String → Bool}
    (hIn : ∀ n, In n → InB n = true) {k : Nat} {n : String} (h : LiveIn rng In k n) :
    liveInB rng InB k n = true := by
  simp only [liveInB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  exact ⟨h.1, h.2.elim Or.inl (fun h2 => Or.inr (hIn n h2))⟩

theorem live_of_liveB {rng : String → Nat × Nat} {In : String → Prop} {InB : String → Bool}
    (hIn : ∀ n, InB n = true → In n) {k : Nat} {n : String} (h : liveB rng InB k n = true) :
    Live rng In k n := by
  simp only [liveB, Bool.or_eq_true, beq_iff_eq] at h
  exact h.elim Or.inl (fun h => Or.inr (liveIn_of_liveInB hIn h))

/-- A check at every program counter of a body. -/
def bodyAll (body : List LinstrRM) (p : Nat → LinstrRM → Bool) : Bool :=
  (List.range body.length).all fun k =>
    match body[k]? with
    | some i => p k i
    | none => true

theorem bodyAll_sound {body : List LinstrRM} {p : Nat → LinstrRM → Bool}
    (h : bodyAll body p = true) {k : Nat} {i : LinstrRM} (hget : body[k]? = some i) :
    p k i = true := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hget).1
  simp only [bodyAll, List.all_eq_true, List.mem_range] at h
  have := h k hk
  rw [hget] at this
  exact this

/-- The Boolean form of `CondOK`. -/
def condOKB (i : LinstrRM) : Bool :=
  (match i.1 with
    | .Lcond _ _ => (flagCondCC? i).isSome
    | _ => true) && mulxFree i

theorem condOK_of_B {i : LinstrRM} (h : condOKB i = true) : CondOK i := by
  unfold condOKB at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun c l he => ?_, h.2⟩
  have h' : (flagCondCC? i).isSome = true := by
    have h1 := h.1
    rw [he] at h1
    exact h1
  exact Option.isSome_iff_ne_none.mp h'

theorem cond_of_B {body : List LinstrRM} (h : bodyAll body (fun _ => condOKB) = true) :
    ∀ k i, 0 ≤ k → body[k]? = some i → CondOK i :=
  fun _ _ _ hget => condOK_of_B (bodyAll_sound h hget)

/-- The Boolean form of the read-liveness condition at one instruction. -/
def usesB (rng : String → Nat × Nat) (InB : String → Bool) (k : Nat) (i : LinstrRM) : Bool :=
  (useNames i.1).all (liveB rng InB k)

theorem uses_of_B {body : List LinstrRM} {rng : String → Nat × Nat} {In : String → Prop}
    {InB : String → Bool} (hIn : ∀ n, InB n = true → In n)
    (h : bodyAll body (usesB rng InB) = true) :
    ∀ k i, 0 ≤ k → body[k]? = some i → ∀ n ∈ useNames i.1, Live rng In k n := by
  intro k i _ hget n hn
  have := bodyAll_sound h hget
  simp only [usesB, List.all_eq_true] at this
  exact live_of_liveB hIn (this n hn)

/-- The Boolean form of the array-read liveness condition at one instruction. -/
def arrUseB (rng : String → Nat × Nat) (InB : String → Bool) (k : Nat) (i : LinstrRM) : Bool :=
  match arrUse? i with
  | some b => liveB rng InB k b
  | none => true

theorem arrUses_of_B {body : List LinstrRM} {rng : String → Nat × Nat} {In : String → Prop}
    {InB : String → Bool} (hIn : ∀ n, InB n = true → In n)
    (h : bodyAll body (arrUseB rng InB) = true) :
    ∀ k i, 0 ≤ k → body[k]? = some i → ∀ b, arrUse? i = some b → Live rng In k b := by
  intro k i _ hget b hb
  have := bodyAll_sound h hget
  unfold arrUseB at this
  rw [hb] at this
  exact live_of_liveB hIn this

/-- The Boolean form of `RangeCert.single`. -/
def singleB (defs : LinstrRM → List String) (_ : Nat) (i : LinstrRM) : Bool :=
  decide ((defs i).length ≤ 1)

/-- The Boolean form of `RangeCert.defCov`. -/
def defCovB (defs : LinstrRM → List String) (rng : String → Nat × Nat) (k : Nat)
    (i : LinstrRM) : Bool :=
  (defs i).all fun d => d == "" || decide ((rng d).1 ≤ k ∧ k ≤ (rng d).2)

/-- The Boolean form of `RangeCert.start`, over the names `names` that carry an
    interval. -/
def startB (names : List String) (defs : LinstrRM → List String) (rng : String → Nat × Nat)
    (InB : String → Bool) (k : Nat) (i : LinstrRM) : Bool :=
  names.all fun n => n == "" || InB n || decide ((rng n).1 ≠ k) || decide ((rng n).2 ≤ k)
    || decide (n ∈ defs i)

/-- The Boolean form of `Interf`, over the names that carry an interval. -/
def interfB (names : List String) (σ : String → String) (rng : String → Nat × Nat) : Bool :=
  names.all fun a => names.all fun b =>
    a == b || decide ((rng a).2 < (rng b).1) || decide ((rng b).2 < (rng a).1) || σ a != σ b

theorem interf_of_B {names : List String} {σ : String → String} {rng : String → Nat × Nat}
    (hsupp : ∀ n k, Covers (rng n) k → n ∈ names) (h : interfB names σ rng = true) :
    Interf σ rng := by
  intro a b k hab ha hb hca hcb
  have ha' := hsupp a k hca
  have hb' := hsupp b k hcb
  simp only [interfB, List.all_eq_true] at h
  have hchk := h a ha' b hb'
  simp only [Bool.or_eq_true] at hchk
  rcases hchk with ((h | h) | h) | h
  · exact absurd (beq_iff_eq.mp h) hab
  · have := of_decide_eq_true h; exfalso; unfold Covers at hca hcb; omega
  · have := of_decide_eq_true h; exfalso; unfold Covers at hca hcb; omega
  · exact bne_iff_ne.mp h

/-- **A range certificate from Boolean checks.** -/
theorem rangeCert_of_B {σ : String → String} {body : List LinstrRM}
    {defs : LinstrRM → List String} {rng : String → Nat × Nat} {inputs names : List String}
    (hsupp : ∀ n k, Covers (rng n) k → n ∈ names)
    (hsingle : bodyAll body (singleB defs) = true)
    (hinEarly : inputs.all (fun n => decide ((rng n).1 ≤ 0)) = true)
    (hdefCov : bodyAll body (defCovB defs rng) = true)
    (hstart : bodyAll body (startB names defs rng (fun n => decide (n ∈ inputs))) = true)
    (hinterf : Interf σ rng) :
    RangeCert σ 0 body defs rng (fun n => n ∈ inputs) where
  single := fun _ _ _ hget => by
    have := bodyAll_sound hsingle hget
    simpa [singleB] using this
  inEarly := fun n hn => by
    simp only [List.all_eq_true, decide_eq_true_eq] at hinEarly
    exact hinEarly n hn
  defCov := fun k i _ hget d hd hd0 => by
    have := bodyAll_sound hdefCov hget
    simp only [defCovB, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact (this d hd).resolve_left hd0
  start := fun k i n _ hget hn hIn hst hlt => by
    have hmem := hsupp n k ⟨hst.le, hlt.le⟩
    have := bodyAll_sound hstart hget
    simp only [startB, List.all_eq_true] at this
    have hchk := this n hmem
    simp only [Bool.or_eq_true] at hchk
    rcases hchk with (((h | h) | h) | h) | h
    · exact absurd (beq_iff_eq.mp h) hn
    · exact absurd (of_decide_eq_true h) hIn
    · exact absurd hst (of_decide_eq_true h)
    · have := of_decide_eq_true h; omega
    · exact of_decide_eq_true h
  interf := hinterf

/-- The Boolean form of `JumpOK` at one instruction, over the names that carry an
    interval. -/
def jumpOKB (names : List String) (rng : String → Nat × Nat) (InB : String → Bool)
    (body : List LinstrRM) (k : Nat) (i : LinstrRM) : Bool :=
  match jumpLabel? i.1 with
  | none => true
  | some l =>
    match findLabelMem l body with
    | none => true
    | some pc => names.all fun r => !liveInB rng InB (pc + 1) r
        || ((!decide (pc + 1 ≤ k) || decide (k ≤ (rng r).2))
          && (!decide (k < pc + 1) || decide ((rng r).1 < k) || InB r))

theorem jumpOK_of_B {names : List String} {rng : String → Nat × Nat} {inputs : List String}
    {body : List LinstrRM}
    (hsupp : ∀ r k, LiveIn rng (fun n => n ∈ inputs) k r → r ∈ names)
    (h : bodyAll body (jumpOKB names rng (fun n => decide (n ∈ inputs)) body) = true) :
    JumpOK body 0 rng (fun n => n ∈ inputs) := by
  intro k i l pc _ hget hl hf r hr
  have := bodyAll_sound h hget
  unfold jumpOKB at this
  simp only [hl, hf, List.all_eq_true] at this
  have hr' := this r (hsupp r (pc + 1) hr)
  rw [liveInB_of_liveIn (fun n hn => decide_eq_true hn) hr] at hr'
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hr'
  obtain ⟨hA, hB⟩ := hr'
  refine ⟨fun hle => ?_, fun hlt => ?_⟩
  · rw [decide_eq_true hle] at hA
    simpa using hA
  · rw [decide_eq_true hlt] at hB
    simpa using hB

/-- The Boolean form of `LowerOK.src` at one instruction. -/
def srcB (isB : String → Bool) (_ : Nat) (i : LinstrRM) : Bool :=
  match i with
  | (.Lopn [.reg d] opn [.reg s0, s1], .reg _) => !isB opn || d == s0 || s1 != .reg d
  | _ => true

/-- The Boolean form of `LowerOK.ctl` at one instruction. -/
def ctlB (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn _ _ _ => true
  | .Llabel _ _ => true
  | .Lcond _ _ => (flagCondCC? i).isSome
  | .Lgoto _ => true
  | _ => false

/-- **The lowering side conditions from Boolean checks.** -/
theorem lowerOK_of_B {isB : String → Bool} {movFor : String → String} {P : LprogM}
    (hmov : ∀ opn, isB opn = true → stripWidthTag (movFor opn) = "MOV")
    (hcmp : ∀ opn, isB opn = true → opn ≠ withWidthTag 64 "CMP")
    (hsrc : bodyAll P.body (srcB isB) = true) (hctl : bodyAll P.body (fun _ => ctlB) = true) :
    LowerOK isB movFor P where
  mov := hmov
  cmp := hcmp
  src := fun k d opn s0 s1 cd hget hb hne => by
    have := bodyAll_sound hsrc hget
    simp only [srcB, binopWire, Bool.or_eq_true] at this
    rcases this with (h | h) | h
    · simp [hb] at h
    · exact absurd (beq_iff_eq.mp h) hne
    · exact bne_iff_ne.mp h
  ctl := fun k i hget => by
    have := bodyAll_sound hctl hget
    obtain ⟨w, tag⟩ := i
    cases w
    all_goals
      first
        | exact Or.inl ⟨_, _, _, rfl⟩
        | exact Or.inr (Or.inl ⟨_, _, rfl⟩)
        | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
        | exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, Option.isSome_iff_ne_none.mp this⟩))
        | exact Bool.noConfusion this

/-! ## 2. The chain as a literal -/

/-- The model chain of the `mpn_and_n` limb body in the body naming: the two
    loads through the invariant arrays, the conjunction, the width shift and the
    store through the accumulator argument. -/
def andBodyOps : List LinstrRM :=
  [ (.Lopn [.reg "r4"] "LOADIDX" [.arrIdx "a1" "a2" 8], .load 64 8)
  , (.Lopn [.reg "r5"] "LOADIDX" [.arrIdx "a0" "a2" 8], .load 64 8)
  , (.Lopn [.reg "r6"] "AND:64" [.reg "r4", .reg "r5"], .reg none)
  , (.Lopn [.reg "r7"] "SHL:64" [.reg "r6", .imm 0], .reg none)
  , (.Lopn [.reg "r8"] "STOREIDX" [.arrIdx "a3" "a2" 8, .reg "r7"], .store 64 8) ]

/-- The straight-line walk of the front's `mpn_and_n` body is `andBodyOps`. -/
theorem straightOpsMem_andUpdate : straightOpsMem 4 (andUpdate ()) 4 = andBodyOps := by
  rfl

/-- The canonicalised `mpn_and_n` chain at loop depth `4`, accumulator `a3`,
    count register `a2` and invariant base registers `a0`, `a1`. -/
def andChainRM : List LinstrRM :=
  [ (.Lopn [.reg "a3"] "MOV:64" [.reg "a3"], .reg none)
  , (.Lopn [.reg "Lidx4"] "MOV:64" [.imm 0], .reg none)
  , (.Lopn [.reg "Lctr4"] "MOV:64" [.reg "a2"], .reg none)
  , (.Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0], .reg none)
  , (.Lcond (.reg "Z") 1073741828, .reg none)
  , (.Llabel .internal 4, .reg none)
  , (.Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8], .load 64 8)
  , (.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a0" "Lidx4" 8], .load 64 8)
  , (.Lopn [.reg "L4_r6"] "AND:64" [.reg "L4_r4", .reg "L4_r5"], .reg none)
  , (.Lopn [.reg "L4_r7"] "SHL:64" [.reg "L4_r6", .imm 0], .reg none)
  , (.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "Lidx4" 8, .reg "L4_r7"], .store 64 8)
  , (.Lopn [.reg "a3"] "MOV:64" [.reg "a3"], .reg none)
  , (.Lopn [.reg "Lidx4"] "ADD:64" [.reg "Lidx4", .imm 1], .reg none)
  , (.Lopn [.reg "Lctr4"] "SUB:64" [.reg "Lctr4", .imm 1], .reg none)
  , (.Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a0"], .reg none)
  , (.Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .reg "a1"], .reg none)
  , (.Lopn [.reg "Lctr4"] "CMP:64" [.reg "Lctr4", .imm 0], .reg none)
  , (.Lcond (.reg "NZ") 4, .reg none)
  , (.Llabel .internal 1073741828, .reg none) ]

/-- **The canonicalised chain is the literal.** -/
theorem andChain_node_eq :
    canonNodeRM (logicTau 4 8 "a3") 4 "a3" "a2" (andUpdate ()) false ["a0", "a1"] = andChainRM := by
  have h4 : logicTau 4 8 "a3" "r4" = "L4_r4" :=
    logicTau_regName (d := 4) (sl := 8) (out := "a3") (k := 4) (by decide)
  have h5 : logicTau 4 8 "a3" "r5" = "L4_r5" :=
    logicTau_regName (d := 4) (sl := 8) (out := "a3") (k := 5) (by decide)
  have h6 : logicTau 4 8 "a3" "r6" = "L4_r6" :=
    logicTau_regName (d := 4) (sl := 8) (out := "a3") (k := 6) (by decide)
  have h7 : logicTau 4 8 "a3" "r7" = "L4_r7" :=
    logicTau_regName (d := 4) (sl := 8) (out := "a3") (k := 7) (by decide)
  have h8 : logicTau 4 8 "a3" "r8" = "a3" := logicTau_regName_store (d := 4) (sl := 8) (out := "a3")
  have ha0 : logicTau 4 8 "a3" "a0" = "a0" :=
    logicTau_argName_lt (d := 4) (sl := 8) (out := "a3") (j := 0) (by decide)
  have ha1 : logicTau 4 8 "a3" "a1" = "a1" :=
    logicTau_argName_lt (d := 4) (sl := 8) (out := "a3") (j := 1) (by decide)
  have ha2 : logicTau 4 8 "a3" "a2" = "Lidx4" := logicTau_argName2 (d := 4) (sl := 8) (out := "a3")
  have ha3 : logicTau 4 8 "a3" "a3" = "a3" := logicTau_argName3 (d := 4) (sl := 8) (out := "a3")
  simp only [canonNodeRM, canonSeedsRM, guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge,
    canonBodyRM, Nat.reduceAdd, canonFeedback, loopAdvanceRM, loopTouchRM]
  erw [straightOpsMem_andUpdate]
  simp only [andBodyOps, List.map, renRM, renLinstrR, renOperand, h4, h5, h6, h7, h8, ha0, ha1,
    ha2, ha3]
  rfl

/-! ## 3. The allocator's assignment -/

/-- The chain as an export command: the argument pin, the chain, the return. -/
def andChainCmd : Lcmd :=
  ⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" [.reg "a0", .reg "a1", .reg "a2", .reg "a3"]⟩
    :: andChainRM.map (fun i => ⟨0, i.1⟩) ++ [⟨0, .Lret⟩]

/-- The names of the chain. -/
def andChainNames : List String :=
  ["a0", "a1", "a2", "a3", "Lidx4", "Lctr4", "L4_r4", "L4_r5", "L4_r6", "L4_r7"]

/-- The register assignment of the linear scan on `andChainCmd`: the count
    register and the two body temporaries `L4_r4`, `L4_r7`, whose live ranges are
    pairwise disjoint, share `RDX`. -/
def andChainSigma (n : String) : String :=
  if n = "a0" then "RBX" else if n = "a1" then "RCX" else if n = "a2" then "RDX"
  else if n = "a3" then "RSI" else if n = "Lidx4" then "RAX" else if n = "Lctr4" then "RDI"
  else if n = "L4_r4" then "RDX" else if n = "L4_r5" then "RBP" else if n = "L4_r6" then "R8"
  else if n = "L4_r7" then "RDX" else n

theorem physSigma_eq_physRename (body : Lcmd) {n : String} (hn : n ≠ "") :
    physSigma body n = physRename body (bodyPhysTable body) n := by
  simp [physSigma, hn]

-- Static check: the linear scan on `andChainCmd` assigns `andChainSigma` on the
-- chain's names, read through one allocation table. The check evaluates in 7 ms
-- once the interpreter has loaded the allocator's code; the first evaluation of a
-- module pays that load, measured at 260 ms in the language server and 477 ms in a
-- batch build, which is what the budget covers.
set_option kat.ms 1000 in
#kat (let tbl := bodyPhysTable andChainCmd
      andChainNames.all (fun n => physRename andChainCmd tbl n == andChainSigma n))

/-! ## 4. The live ranges -/

/-- The register intervals of the chain, by program counter. -/
def andRr (n : String) : Nat × Nat :=
  if n = "a0" then (0, 18) else if n = "a1" then (0, 18) else if n = "a2" then (0, 2)
  else if n = "a3" then (0, 18) else if n = "Lidx4" then (1, 18) else if n = "Lctr4" then (2, 18)
  else if n = "L4_r4" then (6, 8) else if n = "L4_r5" then (7, 8) else if n = "L4_r6" then (8, 9)
  else if n = "L4_r7" then (9, 10) else (1, 0)

/-- The register inputs of the chain: the four argument registers. -/
def andInputsR : List String := ["a0", "a1", "a2", "a3"]

/-- The array intervals of the chain: the two source arrays and the accumulator,
    live through the whole body. -/
def andRa (n : String) : Nat × Nat :=
  if n = "a0" then (0, 19) else if n = "a1" then (0, 19) else if n = "a3" then (0, 19) else (1, 0)

/-- The array inputs of the chain. -/
def andInputsA : List String := ["a0", "a1", "a3"]

theorem andRr_covers_mem {n : String} {k : Nat} (h : Covers (andRr n) k) : n ∈ andChainNames := by
  unfold Covers andRr at h
  split_ifs at h <;> simp_all [andChainNames]
  all_goals omega

theorem andRa_covers_mem {n : String} {k : Nat} (h : Covers (andRa n) k) : n ∈ andChainNames := by
  unfold Covers andRa at h
  split_ifs at h <;> simp_all [andChainNames]
  all_goals omega

theorem andRr_liveIn_mem {r : String} {k : Nat} (h : LiveIn andRr (fun n => n ∈ andInputsR) k r) :
    r ∈ andChainNames := by
  unfold LiveIn andRr at h
  split_ifs at h <;> simp_all [andChainNames, andInputsR]
  all_goals omega

theorem andRa_liveIn_mem {r : String} {k : Nat} (h : LiveIn andRa (fun n => n ∈ andInputsA) k r) :
    r ∈ andChainNames := by
  unfold LiveIn andRa at h
  split_ifs at h <;> simp_all [andChainNames, andInputsA]
  all_goals omega

/-- Interference freedom transfers between renamings that agree on every name
    with a covered program counter. -/
theorem Interf.of_agree {σ σ' : String → String} {rng : String → Nat × Nat}
    (h : Interf σ' rng) (hag : ∀ n k, n ≠ "" → Covers (rng n) k → σ n = σ' n) : Interf σ rng := by
  intro a b k hab ha hb hca hcb
  rw [hag a k ha hca, hag b k hb hcb]
  exact h a b k hab ha hb hca hcb

theorem andChainSigma_interf : Interf andChainSigma andRr :=
  interf_of_B (fun _ _ h => andRr_covers_mem h) (by decide +kernel)

theorem andChainSigma_interfA : Interf andChainSigma andRa :=
  interf_of_B (fun _ _ h => andRa_covers_mem h) (by decide +kernel)

/-! ## 5. The certificates -/

theorem andChain_cond : ∀ k i, 0 ≤ k → andChainRM[k]? = some i → CondOK i :=
  cond_of_B (by decide +kernel)

theorem andChain_uses : ∀ k i, 0 ≤ k → andChainRM[k]? = some i →
    ∀ n ∈ useNames i.1, Live andRr (fun n => n ∈ andInputsR) k n :=
  uses_of_B (fun _ h => of_decide_eq_true h) (by decide +kernel)

theorem andChain_arrUses : ∀ k i, 0 ≤ k → andChainRM[k]? = some i →
    ∀ b, arrUse? i = some b → Live andRa (fun n => n ∈ andInputsA) k b :=
  arrUses_of_B (fun _ h => of_decide_eq_true h) (by decide +kernel)

/-- **The register interval certificate of the chain**, for every renaming that
    agrees with the allocator's assignment on the chain's names. -/
theorem andChain_regCert (σ : String → String)
    (hσ : ∀ n ∈ andChainNames, σ n = andChainSigma n) :
    RangeCert σ 0 andChainRM regDefs andRr (fun n => n ∈ andInputsR) :=
  rangeCert_of_B (fun _ _ h => andRr_covers_mem h) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (Interf.of_agree andChainSigma_interf (fun n _ _ hc => hσ n (andRr_covers_mem hc)))

/-- **The array interval certificate of the chain.** -/
theorem andChain_arrCert (σ : String → String)
    (hσ : ∀ n ∈ andChainNames, σ n = andChainSigma n) :
    RangeCert σ 0 andChainRM arrDefs andRa (fun n => n ∈ andInputsA) :=
  rangeCert_of_B (fun _ _ h => andRa_covers_mem h) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (Interf.of_agree andChainSigma_interfA (fun n _ _ hc => hσ n (andRa_covers_mem hc)))

/-- **The jump condition of the register intervals.** -/
theorem andChain_jumpOK_reg : JumpOK andChainRM 0 andRr (fun n => n ∈ andInputsR) :=
  jumpOK_of_B (fun _ _ h => andRr_liveIn_mem h) (by decide +kernel)

/-- **The jump condition of the array intervals.** -/
theorem andChain_jumpOK_arr : JumpOK andChainRM 0 andRa (fun n => n ∈ andInputsA) :=
  jumpOK_of_B (fun _ _ h => andRa_liveIn_mem h) (by decide +kernel)

/-! ## 6. The two-address lowering -/

/-- The binop test of the chain's two-address lowering: the four register binops
    the chain carries. -/
def andIsB (opn : String) : Bool :=
  opn == "AND:64" || opn == "SHL:64" || opn == "ADD:64" || opn == "SUB:64"

/-- The copy mnemonic of the chain's two-address lowering. -/
def andMovFor (_ : String) : String := "MOV:64"

/-- Renaming the chain by `σ` is renaming it by the allocator's assignment when
    the two agree on the chain's names. -/
theorem andChainRM_map_congr (σ : String → String)
    (hσ : ∀ n ∈ andChainNames, σ n = andChainSigma n) :
    andChainRM.map (renRM σ) = andChainRM.map (renRM andChainSigma) := by
  have h0 := hσ "a0" (by decide)
  have h1 := hσ "a1" (by decide)
  have h2 := hσ "a2" (by decide)
  have h3 := hσ "a3" (by decide)
  have h4 := hσ "Lidx4" (by decide)
  have h5 := hσ "Lctr4" (by decide)
  have h6 := hσ "L4_r4" (by decide)
  have h7 := hσ "L4_r5" (by decide)
  have h8 := hσ "L4_r6" (by decide)
  have h9 := hσ "L4_r7" (by decide)
  simp [andChainRM, renRM, renLinstrR, renOperand, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem andChainPhys_srcB :
    bodyAll (andChainRM.map (renRM andChainSigma)) (srcB andIsB) = true := by
  decide +kernel

theorem andChainPhys_ctlB :
    bodyAll (andChainRM.map (renRM andChainSigma)) (fun _ => ctlB) = true := by
  decide +kernel

/-- **The lowering side conditions of the allocated chain.** -/
theorem andChain_lowerOK (σ : String → String)
    (hσ : ∀ n ∈ andChainNames, σ n = andChainSigma n) (fn : String) :
    LowerOK andIsB andMovFor (singletonProgM fn (andChainRM.map (renRM σ))) := by
  rw [andChainRM_map_congr σ hσ]
  refine lowerOK_of_B ?_ ?_ andChainPhys_srcB andChainPhys_ctlB
  · intro opn _
    show stripWidthTag "MOV:64" = "MOV"
    decide +kernel
  · intro opn h hc
    subst hc
    revert h
    decide +kernel

/-! ## 7. The state relations at entry -/

/-- The pullback of a state along `σ` is related to the state by `RelF2 σ` on every
    name set. -/
theorem relF2_pullM (σ : String → String) (Nr Na : String → Prop) (p0 : LstateM)
    (fn : String) (zf : Bool) :
    RelF2 σ Nr Na { prog := { base := pullM σ p0, lfn := fn }, zf := zf }
      { prog := { base := p0, lfn := fn }, zf := zf } :=
  ⟨⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

/-- A state at program counter `0` is related to itself by `RelX EqPc`. -/
theorem relX_self (expand : LinstrRM → List LinstrRM) (P : LprogM) (s : LstateMF)
    (h : s.prog.base.lpc = 0) : RelX EqPc expand P s s :=
  ⟨rfl, rfl, by rw [h, JasminLsemExportLower.pcMap_zero], rfl⟩

/-! ## 8. The value theorem at the physical assignment -/

/-- **The allocated and lowered `mpn_and_n` chain computes the elementwise
    conjunction**, for every renaming `σ` that agrees with the allocator's
    assignment on the chain's names. The entry state `p0` holds the seed arrays at
    the images of `a3`, `a0`, `a1`, readable invariant base registers and the
    trip count at the image of `a2`. -/
theorem and_chain_machine_val_phys (σ : String → String)
    (hfix : σ "" = "") (hne : ∀ n, n ≠ "" → σ n ≠ "")
    (hσ : ∀ n ∈ andChainNames, σ n = andChainSigma n)
    (V : Ctxt.Valuation Gouter) (hn : (logicCount.lookup V).toNat ≤ NL)
    (fn : String) (p0 : LstateM) (zf : Bool) (hpc : p0.lpc = 0)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (pullM (logicTau 4 8 "a3") ((pullM σ p0).setReg (loopIdx 4) (0#64)))
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hinv : ∀ j, j < 2 → (p0.reg.getW (σ (argName j)) 64).isSome)
    (hm64 : (logicCount.lookup V).toNat < 2 ^ 64)
    (hcnt : p0.reg.getW (σ "a2") 64 = some (BitVec.ofNat 64 (logicCount.lookup V).toNat)) :
    ∃ (fuel : Nat) (t : LstateMF) (o : Fin NL → BitVec 64),
      lsemFuelMemF ⟨fn, (andChainRM.map (renRM σ)).flatMap (lowerRM andIsB andMovFor)⟩ fuel
          { prog := { base := p0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (σ "a3") 64 NL = some o
        ∧ cells o (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x &&& y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  have hnode := andChain_node_eq
  have h := and_chain_machine_val (d := 4) (out := "a3") (σ := σ) (rr := andRr) (ra := andRa)
    (InR := fun n => n ∈ andInputsR) (InA := fun n => n ∈ andInputsA) (isB := andIsB)
    (movFor := andMovFor) V hn
    (fun k => argName_ne_loopReg (d := 4) 3 k) (by decide) (by decide)
    (fun j hj => by interval_cases j <;> decide) false ["a0", "a1"]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, by decide, (logicTau_argName_lt (d := 4) (sl := 8) (out := "a3") (j := 0)
          (by decide)).symm⟩
      · exact ⟨1, by decide, (logicTau_argName_lt (d := 4) (sl := 8) (out := "a3") (j := 1)
          (by decide)).symm⟩)
    fn "a2" (by decide) (pullM σ p0) zf hpc hseed
    (fun j hj => by
      rw [logicTau_argName_lt (d := 4) (sl := 8) (out := "a3") hj, pullM_getW]
      exact hinv j hj)
    hm64 hcnt 0 hfix hne
    (by rw [hnode]; exact andChain_cond)
    (fun _ _ _ => Nat.zero_le _)
    (by rw [hnode]; exact andChain_regCert σ hσ)
    (by rw [hnode]; exact andChain_arrCert σ hσ)
    (by rw [hnode]; exact andChain_uses)
    (by rw [hnode]; exact andChain_arrUses)
    (by rw [hnode]; exact andChain_jumpOK_reg)
    (by rw [hnode]; exact andChain_jumpOK_arr)
    (by rw [hnode]; exact andChain_lowerOK σ hσ fn)
    { prog := { base := p0, lfn := fn }, zf := zf } { prog := { base := p0, lfn := fn }, zf := zf }
    (relF2_pullM σ _ _ p0 fn zf) (Nat.le_refl 0)
    (relX_self _ _ _ hpc)
    (by
      rw [hnode]
      intro pc hpc
      have h19 : (andRa "a3").2 = 19 := by decide
      have hlen : andChainRM.length = 19 := by decide
      rw [hlen] at hpc
      exact Or.inr ⟨by rw [h19]; exact hpc, Or.inr (by decide)⟩)
  rw [hnode] at h
  exact h

/-- `and_chain_machine_val_phys` at the allocator's assignment `physSigma andChainCmd`;
    the agreement with `andChainSigma` is the fact the `#kat` above checks. -/
theorem and_chain_machine_val_physSigma
    (hσ : ∀ n ∈ andChainNames, physSigma andChainCmd n = andChainSigma n)
    (V : Ctxt.Valuation Gouter) (hn : (logicCount.lookup V).toNat ≤ NL)
    (fn : String) (p0 : LstateM) (zf : Bool) (hpc : p0.lpc = 0)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2)
      (pullM (logicTau 4 8 "a3") ((pullM (physSigma andChainCmd) p0).setReg (loopIdx 4) (0#64)))
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hinv : ∀ j, j < 2 → (p0.reg.getW (physSigma andChainCmd (argName j)) 64).isSome)
    (hm64 : (logicCount.lookup V).toNat < 2 ^ 64)
    (hcnt : p0.reg.getW (physSigma andChainCmd "a2") 64
      = some (BitVec.ofNat 64 (logicCount.lookup V).toNat)) :
    ∃ (fuel : Nat) (t : LstateMF) (o : Fin NL → BitVec 64),
      lsemFuelMemF ⟨fn, (andChainRM.map (renRM (physSigma andChainCmd))).flatMap
          (lowerRM andIsB andMovFor)⟩ fuel
          { prog := { base := p0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (physSigma andChainCmd "a3") 64 NL = some o
        ∧ cells o (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x &&& y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) :=
  and_chain_machine_val_phys (physSigma andChainCmd) (physSigma_fix _)
    (physSigma_ne_empty _) hσ V hn fn p0 zf hpc hseed hinv hm64 hcnt

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportPhysAnd
