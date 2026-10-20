/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT

@[expose] public section

set_option autoImplicit false

/-!
# Simulation of the address machine by a step relation

A run of `VIR.JasminLsemAddrRun.runA` on a printed body is simulated by a target machine as
soon as one step of the address machine is: this module proves the fuel induction once, for
the untraced run against the reachability of an `RInstrSemantics.Machine` and for a traced run
in continuation form, and the instruction-level facts that the simulations of a label, a
conditional branch on the zero flag and the closing return use on both sides.

## Main results

* `runA_reaches_of_step`: from states related by `Rel`, if every step of the address machine
  is matched by a path of `M` between the images `pos` of the two program counters, ending in
  `Rel`, and a halted state reaches `e` ending in `Fin`, then every terminating run whose
  states satisfy `Safe` is matched by a path of `M` to `e` ending in `Fin`.
* `runALeakX_sim_of_step`: the traced form, for any run with the recursion of `runA` that
  emits the events `L s zf` at each step: a goal `Goal` on the trace holds at every state of
  a terminating safe run as soon as it holds at the halt and is carried back over each step.
* `stepA_label`, `stepA_cond`, `haltedA_ret`: the address machine at a label, at a branch on
  the zero flag, and at the return.
* `decProg`, `reaches_label`, `reaches_cond`: the decoded program of a body and its paths over
  the decoded instructions of a label and of a branch (`posOf_label`, `posOf_cond`,
  `decProg_cond`).
* `runL_seg`: a segment of `op`s runs with the leakage of the block.
* `runL_lopn`, `runL_label`, `runL_cond`, `runL_halt`: the traced runs `DecodedCT.RunL` of the
  decoded program over an `Lopn`, a label, a branch and the closing `lea` and `ret`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunASim

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL blockLeakA opLeak BlockOk)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak DoitRegime)

/-! ## 1. The fuel induction -/

/-- **A run of the address machine simulated step by step.** From states `a` and `s` related
    by `Rel`, if every step of the address machine from a safe, unhalted state is matched by a
    path of `M` on `prog` from the image of its program counter to the image of the next one,
    ending in `Rel`, and every halted state in `Rel` reaches `e` ending in `Fin`, then every
    terminating run of `runA` whose states before a step satisfy `Safe` is matched by a path
    of `M` from the image of the first program counter to `e`, ending in `Fin` with the final
    state. -/
theorem runA_reaches_of_step {σ : Type} (M : Machine σ) (prog : List RInstr) (pos : Nat → Nat)
    (e : Nat) {frame : String → Option (BitVec 64)} {body : Lcmd} {Safe : LstateA → Prop}
    (Rel : σ → LstateA → Bool → Prop) (Fin : σ → LstateA → Prop)
    (hhalt : ∀ a s zf, Rel a s zf → haltedA body s = true →
      ∃ a', Reaches M prog (pos s.reg.lpc) a e a' ∧ Fin a' s)
    (hstep : ∀ a s zf s' zf', Rel a s zf → haltedA body s = false → Safe s →
      stepA frame body s zf = some (s', zf') →
      ∃ a', Reaches M prog (pos s.reg.lpc) a (pos s'.reg.lpc) a' ∧ Rel a' s' zf') :
    ∀ (fuel : Nat) (a : σ) (s : LstateA) (zf : Bool) (t : LstateA × Bool), Rel a s zf →
      runA frame body fuel s zf = some t → RunSafe frame body Safe fuel s zf →
      ∃ a', Reaches M prog (pos s.reg.lpc) a e a' ∧ Fin a' t.1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro a s zf t hR hrun _
    cases hh : haltedA body s
    · simp [runA, hh] at hrun
    · rw [runA_halt _ _ _ _ _ hh] at hrun
      obtain rfl := Option.some.inj hrun
      exact hhalt a s zf hR hh
  | succ f ih =>
    intro a s zf t hR hrun hsafe
    cases hh : haltedA body s
    · rw [runA_step _ _ _ _ _ hh] at hrun
      cases hst : stepA frame body s zf with
      | none => rw [hst] at hrun; cases hrun
      | some bz =>
        obtain ⟨s', zf'⟩ := bz
        rw [hst, Option.bind_some] at hrun
        obtain ⟨a', hP, hR'⟩ := hstep a s zf s' zf' hR hh hsafe.1 hst
        obtain ⟨a'', hP', hF⟩ := ih a' s' zf' t hR' hrun (hsafe.2 s' zf' hst)
        exact ⟨a'', hP.trans hP', hF⟩
    · rw [runA_halt _ _ _ _ _ hh] at hrun
      obtain rfl := Option.some.inj hrun
      exact hhalt a s zf hR hh

/-- **A traced run of the address machine simulated step by step, in continuation form.**
    `R` is a run with the recursion of `runA` whose step from `s` with flag `zf` emits the
    events `L s zf` before those of the rest of the run. From states `a` and `s` related by
    `Rel`, if `Goal` holds with the empty trace at every halted state in `Rel` that is the final
    pair `t`, and every step from a safe, unhalted state leads to a state in `Rel` from which
    `Goal` with trace `ℓ` gives `Goal` with trace `L s zf ++ ℓ`, then `Goal` holds with the
    trace of every terminating run of `R` to `t` whose states before a step satisfy `Safe`. -/
theorem runALeakX_sim_of_step {σ : Type} {frame : String → Option (BitVec 64)} {body : Lcmd}
    {Safe : LstateA → Prop} (L : LstateA → Bool → List CTLeak)
    (R : Nat → LstateA → Bool → Option ((LstateA × Bool) × List CTLeak))
    (hR0 : ∀ s zf, R 0 s zf = if haltedA body s then some ((s, zf), []) else none)
    (hRs : ∀ n s zf, R (n + 1) s zf =
      if haltedA body s then some ((s, zf), [])
      else (stepA frame body s zf).bind fun bz =>
        (R n bz.1 bz.2).map fun r => (r.1, L s zf ++ r.2))
    (t : LstateA × Bool) (Rel : σ → LstateA → Bool → Prop)
    (Goal : σ → LstateA → List CTLeak → Prop)
    (hhalt : ∀ a s zf, Rel a s zf → haltedA body s = true → (s, zf) = t → Goal a s [])
    (hstep : ∀ a s zf s' zf', Rel a s zf → haltedA body s = false → Safe s →
      stepA frame body s zf = some (s', zf') →
      ∃ a', Rel a' s' zf' ∧ ∀ ℓ, Goal a' s' ℓ → Goal a s (L s zf ++ ℓ)) :
    ∀ (fuel : Nat) (a : σ) (s : LstateA) (zf : Bool) (ℓ : List CTLeak), Rel a s zf →
      R fuel s zf = some (t, ℓ) → RunSafe frame body Safe fuel s zf → Goal a s ℓ := by
  intro fuel
  induction fuel with
  | zero =>
    intro a s zf ℓ hR hrun _
    rw [hR0] at hrun
    cases hh : haltedA body s
    · simp [hh] at hrun
    · simp only [hh, if_true, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨h1, rfl⟩ := hrun
      exact hhalt a s zf hR hh h1
  | succ f ih =>
    intro a s zf ℓ hR hrun hsafe
    rw [hRs] at hrun
    cases hh : haltedA body s
    · simp only [hh, Bool.false_eq_true, if_false] at hrun
      cases hst : stepA frame body s zf with
      | none => rw [hst] at hrun; cases hrun
      | some bz =>
        obtain ⟨s', zf'⟩ := bz
        rw [hst, Option.bind_some] at hrun
        obtain ⟨⟨t', ℓ'⟩, hrun', heq⟩ := Option.map_eq_some_iff.mp hrun
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨a', hR', hk⟩ := hstep a s zf s' zf' hR hh hsafe.1 hst
        exact hk ℓ' (ih a' s' zf' ℓ' hR' hrun' (hsafe.2 s' zf' hst))
    · simp only [hh, if_true, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨h1, rfl⟩ := hrun
      exact hhalt a s zf hR hh h1

/-! ## 2. The address machine at a label, a branch and the return -/

/-- The program counter of `s.setLpc p` is `p`. -/
@[simp] theorem setLpc_reg_lpc (s : LstateA) (p : Nat) : (s.setLpc p).reg.lpc = p := rfl

/-- The address machine at a label steps to the next instruction. -/
theorem stepA_label (frame : String → Option (BitVec 64)) {body : Lcmd} {s : LstateA}
    {ii : Nat} {kd : LabelKind} {l : LLabel}
    (h : body[s.reg.lpc]? = some ⟨ii, .Llabel kd l⟩) (zf : Bool) :
    stepA frame body s zf = some (s.setLpc (s.reg.lpc + 1), zf) := by
  simp only [stepA, h]

/-- The address machine at a branch on the zero flag of polarity `pol` to a label at position
    `p` steps to `p` when the flag is the polarity, to the next instruction otherwise. -/
theorem stepA_cond (frame : String → Option (BitVec 64)) {body : Lcmd} {s : LstateA}
    {ii : Nat} {cc : String} {l : LLabel} {pol : Bool} {p : Nat}
    (h : body[s.reg.lpc]? = some ⟨ii, .Lcond (.reg cc) l⟩) (hpol : condPol cc = some pol)
    (hp : labelAt body l = some p) (zf : Bool) :
    stepA frame body s zf = some (s.setLpc (if zf = pol then p else s.reg.lpc + 1), zf) := by
  by_cases hz : zf = pol <;> simp [stepA, h, hpol, hp, hz]

/-- The address machine has halted at the return. -/
theorem haltedA_ret {body : Lcmd} {s : LstateA} {ii : Nat}
    (h : body[s.reg.lpc]? = some ⟨ii, .Lret⟩) : haltedA body s = true := by
  simp only [haltedA, h]

/-! ## 3. The decoded program -/

/-- The decoded program of a body with shapes `shs`: the frame `lea` `a`, the decoded
    instructions of each body instruction, the closing `lea` `b` and `ret`. -/
abbrev decProg (a b : JInstr 64) (body : Lcmd) (shs : List DShape) : List RInstr :=
  .op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret])

/-- A label decodes to no instruction: its decoded index is that of the next instruction. -/
theorem posOf_label {body : Lcmd} {shs : List DShape} {k : Nat} (hks : k < shs.length)
    {kd : LabelKind} {l : LLabel}
    (hshk : shapeOf (Params.ofBody body) (.Llabel kd l) = some shs[k]) :
    posOf shs (k + 1) = posOf shs k := by
  have hsk : shs[k] = .one .skip := by simp [shapeOf] at hshk; exact hshk.symm
  rw [posOf_succ shs k hks, hsk]
  simp [nOf]

/-- A path of a machine on the decoded program from the index of the instruction after a label
    is a path from the index of the label. -/
theorem reaches_label {σ : Type} {M : Machine σ} {a b : JInstr 64} {body : Lcmd}
    {shs : List DShape} {k : Nat} (hks : k < shs.length) {kd : LabelKind} {l : LLabel}
    (hshk : shapeOf (Params.ofBody body) (.Llabel kd l) = some shs[k]) {x : σ} {e : Nat}
    {x' : σ} (hR : Reaches M (decProg a b body shs) (posOf shs (k + 1)) x e x') :
    Reaches M (decProg a b body shs) (posOf shs k) x e x' := by
  rwa [posOf_label hks hshk] at hR

/-- The decoded instruction of a branch on the zero flag at position `k` to a label at
    position `p`. -/
theorem decProg_cond {a b : JInstr 64} {body : Lcmd} {shs : List DShape} {k : Nat}
    (hks : k < shs.length) {cc : String} {l : LLabel} {p : Nat}
    (hshk : shapeOf (Params.ofBody body) (.Lcond (.reg cc) l) = some shs[k])
    (hp : labelAt body l = some p) :
    (decProg a b body shs)[posOf shs k]? = some (.jcc (ccNibble cc) (posOf shs p)) := by
  obtain ⟨A, B, hsplit, hA⟩ := prog_split body shs a b k hks
  have hsk : shs[k] = .one (.jcc (ccNibble cc) l) := by
    simp [shapeOf] at hshk; exact hshk.symm
  show (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))[posOf shs k]? = _
  rw [hsplit, hsk, ← hA, List.append_assoc, List.getElem?_append_right (by omega)]
  simp [blkOf, hp]

/-- A branch on the zero flag decodes to one instruction. -/
theorem posOf_cond {body : Lcmd} {shs : List DShape} {k : Nat} (hks : k < shs.length)
    {cc : String} {l : LLabel}
    (hshk : shapeOf (Params.ofBody body) (.Lcond (.reg cc) l) = some shs[k]) :
    posOf shs (k + 1) = posOf shs k + 1 := by
  have hsk : shs[k] = .one (.jcc (ccNibble cc) l) := by
    simp [shapeOf] at hshk; exact hshk.symm
  rw [posOf_succ shs k hks, hsk]
  rfl

/-- The machine `aMachine` steps over the decoded branch on the zero flag at position `k` of
    polarity `pol` to the index of its target `p` when the machine flag is the polarity, to
    the index of the next instruction otherwise. -/
theorem reaches_cond {a b : JInstr 64} {body : Lcmd} {shs : List DShape} {k : Nat}
    (hks : k < shs.length) {cc : String} {l : LLabel} {pol : Bool} {p : Nat}
    (hshk : shapeOf (Params.ofBody body) (.Lcond (.reg cc) l) = some shs[k])
    (hpol : condPol cc = some pol) (hp : labelAt body l = some p) (sa : AState) :
    Reaches aMachine (decProg a b body shs) (posOf shs k) sa
      (posOf shs (if sa.flags.zf.getD false = pol then p else k + 1)) sa := by
  have hms := step_jcc_pol (decProg a b body shs) (posOf shs k) (posOf shs p) sa cc pol hpol
    (decProg_cond hks hshk hp)
  by_cases hz : sa.flags.zf.getD false = pol
  · rw [if_pos hz] at hms ⊢
    exact .single hms
  · rw [if_neg hz] at hms ⊢
    rw [posOf_cond hks hshk]
    exact .single hms

/-! ## 4. Traced runs of the decoded program -/

/-- A segment of `op`s of a program, each satisfying `ok`, runs with the leakage of the
    block. -/
theorem runL_seg {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {prog : List RInstr}
    (B : List RInstr) :
    ∀ (ops : List (JInstr 64)) (A : List RInstr) (sa : AState) {ℓ : List CTLeak} {sa' : AState},
      prog = A ++ ops.map RInstr.op ++ B → BlockOk ok sa ops →
      RunL r ok prog (A.length + ops.length) (runBlockA sa ops) ℓ sa' →
      RunL r ok prog A.length sa (blockLeakA r sa ops ++ ℓ) sa' := by
  intro ops
  induction ops with
  | nil =>
    intro A sa ℓ sa' _ _ h
    simpa [blockLeakA] using h
  | cons i is ih =>
    intro A sa ℓ sa' hp hok h
    have hp' : prog = (A ++ [RInstr.op i]) ++ is.map RInstr.op ++ B := by simp [hp]
    have h' : RunL r ok prog ((A ++ [RInstr.op i]).length + is.length)
        (runBlockA (evalInstrA sa i) is) ℓ sa' := by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h
    have hr := ih (A ++ [RInstr.op i]) (evalInstrA sa i) hp' hok.2 h'
    have hi : prog[A.length]? = some (.op i) := by simp [hp]
    have := RunL.op (r := r) (ok := ok) hi hok.1 (by simpa using hr)
    simpa [blockLeakA, List.append_assoc] using this

/-- The decoded instructions `js` of an `Lopn` at position `k` run from its decoded index to
    the decoded index of `k + 1`, with the leakage of the block. -/
theorem runL_lopn {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {a b : JInstr 64}
    {body : Lcmd} {shs : List DShape} {k : Nat} (hks : k < shs.length) {ds : List LOperand}
    {o : String} {ss : List LOperand}
    (hshk : shapeOf (Params.ofBody body) (.Lopn ds o ss) = some shs[k])
    {js : List (JInstr 64)} (hops : shs[k].ops' = js) {sa : AState} (hok : BlockOk ok sa js)
    {ℓ : List CTLeak} {sa' : AState}
    (hR : RunL r ok (decProg a b body shs) (posOf shs (k + 1)) (runBlockA sa js) ℓ sa') :
    RunL r ok (decProg a b body shs) (posOf shs k) sa (blockLeakA r sa js ++ ℓ) sa' := by
  obtain ⟨A, B, hsplit, hA⟩ := prog_split body shs a b k hks
  obtain ⟨hblk, hn⟩ := blkOf_lopn (body := body) (shs := shs) hshk
  have hprog : decProg a b body shs = A ++ js.map RInstr.op ++ B := by
    show RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]) = _
    rw [hsplit, hblk, hops]
  have hpos : posOf shs (k + 1) = A.length + js.length := by
    rw [posOf_succ shs k hks, hn, hops, hA]
  rw [hpos] at hR
  have h0 := runL_seg B js A sa hprog hok hR
  rwa [hA] at h0

/-- A traced run of the decoded program from the index of the instruction after a label is a
    traced run from the index of the label. -/
theorem runL_label {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {a b : JInstr 64}
    {body : Lcmd} {shs : List DShape} {k : Nat} (hks : k < shs.length) {kd : LabelKind}
    {l : LLabel} (hshk : shapeOf (Params.ofBody body) (.Llabel kd l) = some shs[k])
    {sa : AState} {ℓ : List CTLeak} {sa' : AState}
    (hR : RunL r ok (decProg a b body shs) (posOf shs (k + 1)) sa ℓ sa') :
    RunL r ok (decProg a b body shs) (posOf shs k) sa ℓ sa' := by
  rwa [posOf_label hks hshk] at hR

/-- The decoded branch on the zero flag at position `k` of polarity `pol` runs on to the
    index of its target `p` when the machine flag is the polarity, to the index of the next
    instruction otherwise, emitting the decision. -/
theorem runL_cond {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {a b : JInstr 64}
    {body : Lcmd} {shs : List DShape} {k : Nat} (hks : k < shs.length) {cc : String}
    {l : LLabel} {pol : Bool} {p : Nat}
    (hshk : shapeOf (Params.ofBody body) (.Lcond (.reg cc) l) = some shs[k])
    (hpol : condPol cc = some pol) (hp : labelAt body l = some p) {sa : AState}
    {ℓ : List CTLeak} {sa' : AState}
    (hR : RunL r ok (decProg a b body shs)
      (posOf shs (if sa.flags.zf.getD false = pol then p else k + 1)) sa ℓ sa') :
    RunL r ok (decProg a b body shs) (posOf shs k) sa
      (.branch (sa.flags.zf.getD false == pol) :: ℓ) sa' := by
  have hj := decProg_cond (a := a) (b := b) hks hshk hp
  have hf : sa.view.flagB (·.zf) = sa.flags.zf.getD false := rfl
  obtain ⟨c, hc, hcb⟩ : ∃ c, condtOfNibble (ccNibble cc) = some c
      ∧ sa.view.condB c = (sa.flags.zf.getD false == pol) := by
    rcases condPol_spec hpol with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
    · rw [hn]
      refine ⟨_, condtOfNibble_four, ?_⟩
      rw [condB_e, hf]
      cases sa.flags.zf.getD false <;> rfl
    · rw [hn]
      refine ⟨_, condtOfNibble_five, ?_⟩
      rw [condB_ne, hf]
      cases sa.flags.zf.getD false <;> rfl
  rw [← hcb]
  refine RunL.jcc hj hc ?_
  rw [hcb]
  by_cases hz : sa.flags.zf.getD false = pol
  · rw [if_pos hz] at hR
    simpa [hz] using hR
  · rw [if_neg hz, posOf_cond hks hshk] at hR
    have hb : (sa.flags.zf.getD false == pol) = false := by simpa using hz
    simpa [hb] using hR

/-- From the index of the last instruction of a body whose last shape is the skip, the decoded
    program runs the closing `lea` `b` and returns. -/
theorem runL_halt {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {a b : JInstr 64}
    {body : Lcmd} {shs : List DShape} (hn : 0 < shs.length)
    (hlast : shs[shs.length - 1] = .one .skip) {sa : AState} (hok : ok sa b) :
    RunL r ok (decProg a b body shs) (posOf shs (shs.length - 1)) sa (opLeak r sa b)
      (evalInstrA sa b) := by
  obtain ⟨he1, he2⟩ := prog_end body shs a b hn hlast
  have := RunL.op (r := r) (ok := ok) (sa := sa) he1 hok (.ret he2)
  simpa using this

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunASim
