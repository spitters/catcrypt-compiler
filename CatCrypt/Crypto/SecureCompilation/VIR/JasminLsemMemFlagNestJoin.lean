/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestInline
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestInline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86IsaDef

@[expose] public section

set_option autoImplicit false

/-!
# Inline-nest regions on the FLAG machine

`JasminLsemMemLoopNestInline` closes the arbitrary-depth INLINE nest, but
its regions are guarded by the **counter register** (`Lcond (.reg nReg) top` —
the `loopLinstrRM` back-edge) and its machine is the call-resolving
`lsemFuelMemLC`.  The EMITTED nested shape (`forLoopLcmdNRtNested`) guards each
level with the **flag idiom** — `CMP ctr,#0 ; Lcond NZ top` back-edge plus the
`CMP ctr,#0 ; Lcond Z endL … Llabel endL` zero-trip top guard — which only the
flag machine `lsemFuelMemF` (`JasminLsemMemFlagGuard`) steps, and
`JasminLsemMemFlagGuard` covers only the SINGLE loop.  This module joins the two:
`IBlock`-style region blocks over the flag machine, at both region shapes
`JasminLsemMemFlagGuard` pins to the lowering.

## The flag block grammar (`FBlock`)

* `straight seg` — an all-`Lopn` segment stepped by the **extended straight
  step `fstepF`** (`Lopn ∪ reg-copy MOV ∪ flag-CMP`): the feedback
  `MOV acc, L<d>_r<k>`, the counter seeds `MOV Lctr, a<k>` / `MOV Lctr, cntRet`,
  and the invariant-touch `CMP ctr, invBase` the lowering emits inside loop
  bodies all step here (they have no `lsemStepMem` arm).
* `region top nReg body` — the bare flag-guarded loop `flagLoopLinstrRM`
  (`Llabel top :: flat ++ [CMP nReg,#0 ; Lcond NZ top]` — the pinned flag back-edge
  idiom, one `CMP` more than the counter-register region).
* `guarded top endL nReg body` — the zero-trip-guarded region
  `guardedFlagLoopLinstrRM` (`CMP nReg,#0 ; Lcond Z endL` forward-skip in front,
  `Llabel endL` behind) — the FULL per-level skeleton `forLoopLcmdNRtNested`
  emits, so a zero-trip inner/outer nest denotes the `m = 0` fold.

Regions nest to arbitrary depth (the block tree is the depth index), and the
spec fold (`runFB`/`runFBsL`/`runFRegionF`) runs a region as a data-dependent
do-while whose back-edge decision is a **counter read** (`getW`) — the
emitted `CMP` evaluates its operand, so the guard-equivalence direction
(`zf`-after-`CMP` = ¬`condNZ`) is used per taken/exit decision.

## The closed theorems

* `segFCore` / `segFBlocks` — the control-flow-aware segment lemma over
  `lsemFuelMemF`: a **fresh strong induction on the back-edge budget**
  mirroring the inline nest's `segCore` with the `CMP` step absorbed into each
  back-edge (a transport from `segCore` is not available: the flag programs are
  syntactically different instruction streams — two extra guard instructions
  and one extra back-edge instruction per region — so there is no state-level
  simulation of the counter-register machine run to transport; the per-region guard REWRITE is
  exactly `zf_after_cmp_eq_not_condNZ`, applied at every back-edge decision).
* `flagNest_closed` — the whole-program closed theorem: the singleton program
  whose body IS the flattened block tree (the emitted nest), run from pc `0`,
  halts on exactly the spec fold's out-state.
* `runFB_guarded_zeroTrip` / `guardedRegion_zeroTrip_machine` — the `Lcond Z`
  forward-skip arm at region granularity: a zero counter at a guarded region's
  head skips the whole region (register store and array carrier untouched —
  the `m = 0` fold).
* `runFRegionF_of_schedule` + `guardedFlagLoop_runBounded_general` — the
  OFFSET-GENERAL guarded single-loop theorem: the full `forLoopLcmdNRt`
  skeleton (guard at pc 0–1, loop at pc-offset 2) for a NONZERO runtime count —
  the guard falls through and the machine realises the bounded fold at the
  shifted base (pc 3), halting past the skip label with `zf = true`.  The fold
  is `runBoundedStraightF` (passes of the extended step `fstepF`), so the body
  may contain the feedback reg-copy `MOV` and the invariant-touch `CMP` —
  `flagLoop_runBounded` covers neither (its body-fold is
  `lsemStraightMemF`) and sits at loop-offset 0 without the guard.

## Validate: the REAL rendered `forLoopLcmdNRtNested` stream

`nestSmokeBody` is the actual `comLToBody` rendering of a small
`ComL.forLoopNRtNested` (outer runtime count `D`, inner trip recomputed per
outer pass as `num >>> (jd+1)`, innermost `acc += 2` — the GGM shape).  The
rendered stream contains every emitted form at once: reg-copy seed/feedback
`MOV`s, both zero-trip guards, both flag back-edges, and the invariant-touch
`CMP Lctr,a0`.  `nestBlks_flat` checks the block tree flattens to the rendered
stream **exactly**; the machine value comes from `flagNest_closed` (not from a
`native_decide` on the interpreter), and `native_decide` evaluates only the
SPEC fold, which equals `ComL.denote` = `ggmNestedFold` at the GGM small sizes
(`num = 8 ↦ 14`, `num = 16 ↦ 28`), plus outer zero-trip (`D = 0`) and inner
zero-trip (`num = 1`: every inner trip `0`) cases.

**All goals closed; axioms ⊆ {propext, Classical.choice, Quot.sound}** for the segment
lemma and the closed theorems (+ `Lean.ofReduceBool` for the `native_decide`
SPEC-fold evaluations in the validate).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth (ggmNestedFold)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestInline
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

/-! ## 1. The extended straight step: `Lopn ∪ reg-copy MOV ∪ flag-CMP`

The flag segment lemma (`lsemFuelMemF_seg`) covers only `PlainLopnBody` segments —
plain `Lopn`s stepped by `stepMemF`.  The emitted loop bodies also carry
the reg-copy `MOV`s (seeds/feedback) and the invariant-touch `CMP ctr,invBase`,
which the flag machine steps through its two additive arms.  `fstepF` is the
per-instruction spec of the flag machine on an arbitrary `Lopn`: the flag-`CMP`
arm, the reg-copy `MOV` arm, and the step `stepMemF` — the extended
straight-step function the generic fold ties below run over. -/

/-- One extended straight step over the bundled base + flag: the flag-`CMP`
    (sets `zf`, store untouched), the reg-copy `MOV` (writes `dst := src`), or
    the flag machine's straight-line step `stepMemF` (`zf` threaded; carry family and
    carry and overflow flags on the base).  Mirrors the non-jump arms of
    `evalInstrPMemF` exactly. -/
def fstepF (i : LinstrRM) (s : LstateM) (zf : Bool) : Option (LstateM × Bool) :=
  match cmpArgs? i with
  | some (a, b) =>
      match evalOperandN s.reg 64 a, evalOperandN s.reg 64 b with
      | some va, some vb => some (s.nextPc, va == vb)
      | _, _ => none
  | none =>
  match movRegArgs? i with
  | some (dst, src) =>
      match readReg s.reg (.reg src) with
      | some ⟨_, v⟩ => some ((s.setReg dst v).nextPc, zf)
      | none => none
  | none => (stepMemF i s).map (fun b => (b, zf))

/-- **The extended straight-step tie** (`Lopn ∪ MOV ∪ CMP`).  On ANY `Lopn`
    instruction — including the emitted flag-`CMP` (immediate or register
    second operand: the back-edge compare AND the invariant touch) and the
    reg-copy `MOV` — the flag machine's eval arm is exactly `fstepF` on the
    wrapped base. -/
theorem evalInstrPMemF_isLopn (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (hi : IsLopn i) :
    evalInstrPMemF P i s
      = (fstepF i s.prog.base s.zf).map
          (fun bz => { prog := { s.prog with base := bz.1 }, zf := bz.2 }) := by
  have hf : flagCondCC? i = none := by
    obtain ⟨d, o, src, hd⟩ := hi
    unfold flagCondCC?
    rw [hd]
  unfold evalInstrPMemF fstepF stepMemF
  cases hc : cmpArgs? i with
  | some ab =>
      obtain ⟨a, b⟩ := ab
      simp only []
      cases ha : evalOperandN s.prog.base.reg 64 a with
      | none => cases hb : evalOperandN s.prog.base.reg 64 b <;> rfl
      | some va =>
          cases hb : evalOperandN s.prog.base.reg 64 b with
          | none => rfl
          | some vb => rfl
  | none =>
      simp only []
      cases hm : movRegArgs? i with
      | some ds =>
          obtain ⟨dst, src⟩ := ds
          simp only []
          cases hr : readReg s.prog.base.reg (.reg src) with
          | none => rfl
          | some wv => obtain ⟨w, v⟩ := wv; rfl
      | none =>
          simp only [hf]
          rw [evalInstrPMemL_lopn P i s.prog hi]
          cases lsemStepMem i s.prog.base with
          | some b => rfl
          | none =>
              simp only [Option.map_none]
              cases carryArgs? i with
              | none =>
                  cases wideArgs? i with
                  | none => rfl
                  | some w =>
                      simp only []
                      cases wideStep w s.prog.base <;> rfl
              | some q =>
                  obtain ⟨op, d, a, b⟩ := q
                  simp only []
                  cases carryStep op d a b s.prog.base <;> rfl

/-- Every successful extended straight step advances the pc by one. -/
theorem fstepF_lpc_succ (i : LinstrRM) (s b : LstateM) (zf zb : Bool)
    (h : fstepF i s zf = some (b, zb)) : b.lpc = s.lpc + 1 := by
  unfold fstepF at h
  repeat' split at h
  all_goals
    first
      | (obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
         simp [LstateM.lpc_nextPc])
      | (obtain ⟨bz, hbz, hrfl⟩ := Option.map_eq_some_iff.mp h
         obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hrfl
         exact stepMemF_lpc_succ i s bz hbz)
      | simp at h

/-- The extended straight fold: iterate `fstepF` over a segment, threading the
    flag. -/
def runStraightF : List LinstrRM → LstateM → Bool → Option (LstateM × Bool)
  | [], s, zf => some (s, zf)
  | i :: is, s, zf => (fstepF i s zf).bind (fun bz => runStraightF is bz.1 bz.2)

@[simp] theorem runStraightF_nil (s : LstateM) (zf : Bool) :
    runStraightF [] s zf = some (s, zf) := rfl

theorem runStraightF_cons (i : LinstrRM) (is : List LinstrRM) (s : LstateM) (zf : Bool) :
    runStraightF (i :: is) s zf
      = (fstepF i s zf).bind (fun bz => runStraightF is bz.1 bz.2) := rfl

/-- The extended fold advances the pc by the segment length. -/
theorem runStraightF_lpc :
    ∀ (seg : List LinstrRM) (s : LstateM) (zf : Bool) (b : LstateM) (zb : Bool),
      runStraightF seg s zf = some (b, zb) → b.lpc = s.lpc + seg.length := by
  intro seg
  induction seg with
  | nil =>
      intro s zf b zb h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      simp
  | cons i is ih =>
      intro s zf b zb h
      rw [runStraightF_cons] at h
      cases hstep : fstepF i s zf with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some bz =>
          rw [hstep, Option.bind_some] at h
          have h1 := fstepF_lpc_succ i s bz.1 zf bz.2 (by rw [hstep])
          have h2 := ih bz.1 bz.2 b zb h
          rw [h2, h1, List.length_cons]
          omega

/-- On a `PlainLopnBody` segment (no flag-`CMP`, no reg-copy `MOV`) the
    extended fold IS the flag body-fold `lsemStraightMemF` with `zf` threaded
    unchanged. -/
theorem runStraightF_plain :
    ∀ (seg : List LinstrRM), PlainLopnBody seg →
      ∀ (s : LstateM) (zf : Bool),
        runStraightF seg s zf = (lsemStraightMemF seg s).map (fun b => (b, zf)) := by
  intro seg
  induction seg with
  | nil => intro _ s zf; simp
  | cons i is ih =>
      intro hplain s zf
      obtain ⟨_, hc, hm⟩ := hplain i (by simp)
      have his : PlainLopnBody is := fun j hj => hplain j (by simp [hj])
      rw [runStraightF_cons, lsemStraightMemF_cons]
      unfold fstepF
      rw [hc, hm]
      cases hstep : stepMemF i s with
      | none => simp
      | some b =>
          simp only [Option.map_some, Option.bind_some]
          exact ih his b zf

/-- **The extended fold against the straight-line body-fold.**  On a `PlainLopnBody`
    segment that `lsemStraightMem` runs to `b`, the extended fold runs to `b` up to the
    carry and overflow flags, with `zf` threaded unchanged. -/
theorem runStraightF_of_lsemStraightMem (seg : List LinstrRM) (hplain : PlainLopnBody seg)
    (s b : LstateM) (zf : Bool) (h : lsemStraightMem seg s = some b) :
    ∃ c o, runStraightF seg s zf = some ({ b with cf := c, of := o }, zf) := by
  obtain ⟨c, o, hc⟩ := lsemStraightMemF_of_lsemStraightMem seg s b s.cf s.of h
  refine ⟨c, o, ?_⟩
  rw [runStraightF_plain seg hplain s zf]
  have hs : ({ s with cf := s.cf, of := s.of } : LstateM) = s := rfl
  rw [hs] at hc
  rw [hc]
  rfl

section Calls

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-- **A straight segment at an instruction set that contains `x86Isa`.** When the extended
    fold `runStraightF` runs an all-`Lopn` segment at positions `lpc .. lpc+|seg|-1` to a
    state, an instruction set `I` whose steps contain those of `x86Isa` runs the segment to the
    same state and continues with `f` fuel. -/
theorem lsemFuelMemF_segF_of_some {I : Isa} (hle : x86Isa.StepLe I) (P : LprogM) (fn : String)
    (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b0 : LstateM) (zf : Bool) (f : Nat) (bz : LstateM × Bool),
      (∀ i ∈ seg, IsLopn i) →
      (∀ k, k < seg.length → P.body[b0.lpc + k]? = seg[k]?) →
      runStraightF seg b0 zf = some bz →
      I.lsemFuelMemF P (seg.length + f) { prog := { base := b0, lfn := fn }, zf := zf }
        = I.lsemFuelMemF P f { prog := { base := bz.1, lfn := fn }, zf := bz.2 } := by
  intro seg
  induction seg with
  | nil =>
      intro b0 zf f bz _ _ h
      simp only [runStraightF_nil, Option.some.injEq] at h
      subst h
      simp only [List.length_nil, Nat.zero_add]
  | cons i is ih =>
      intro b0 zf f bz hlopn hpos h
      have hi : IsLopn i := hlopn i (by simp)
      have his : ∀ j ∈ is, IsLopn j := fun j hj => hlopn j (by simp [hj])
      have hfetch : findInstrMem P
          ({ prog := { base := b0, lfn := fn }, zf := zf } : LstateMF).prog = some i := by
        show findInstrMem P { base := b0, lfn := fn } = some i
        unfold findInstrMem
        rw [ite_eq_left (show ({ base := b0, lfn := fn } : LstatePM).lfn = P.lfn from hfn)]
        have := hpos 0 (by simp)
        simpa using this
      rw [runStraightF_cons] at h
      cases hstep : fstepF i b0 zf with
      | none => rw [hstep] at h; cases h
      | some bz1 =>
          rw [hstep, Option.bind_some] at h
          have hx : x86Isa.step P i { prog := { base := b0, lfn := fn }, zf := zf }
              = some { prog := { base := bz1.1, lfn := fn }, zf := bz1.2 } := by
            change evalInstrPMemF P i _ = _
            rw [evalInstrPMemF_isLopn P i _ hi]
            simp only [hstep, Option.map_some]
          rw [List.length_cons, show is.length + 1 + f = (is.length + f) + 1 from by omega,
            I.lsemFuelMemF_step P _ i _ _ hfetch (hle _ _ _ _ hx)]
          have hb_lpc : bz1.1.lpc = b0.lpc + 1 :=
            fstepF_lpc_succ i b0 bz1.1 zf bz1.2 (by rw [hstep])
          have hpos' : ∀ k, k < is.length → P.body[bz1.1.lpc + k]? = is[k]? := by
            intro k hk
            have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
            rw [hb_lpc, show b0.lpc + 1 + k = b0.lpc + (k + 1) from by omega, hp]
            simp
          exact ih bz1.1 bz1.2 f bz his hpos' h

/-- **Extended straight-line segment run at an instruction set that agrees with `x86Isa` on
    the segment.** For an instruction set `I` whose step at every instruction of an all-`Lopn`
    segment is the step of `x86Isa`, the segment at positions `lpc .. lpc+|seg|-1` executes
    the extended fold `runStraightF` and continues with `f` fuel. An instruction set whose
    steps contain those of `x86Isa` and whose further steps are local calls agrees with
    `x86Isa` at every instruction that is no shadow instruction of a call
    (`Isa.CallLocal.step_eq`). -/
theorem lsemFuelMemF_segF_agree {I : Isa} (P : LprogM) (fn : String) (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b0 : LstateM) (zf : Bool) (f : Nat),
      (∀ i ∈ seg, IsLopn i) →
      (∀ i ∈ seg, ∀ (Q : LprogM) (s : LstateMF), I.step Q i s = x86Isa.step Q i s) →
      (∀ k, k < seg.length → P.body[b0.lpc + k]? = seg[k]?) →
      I.lsemFuelMemF P (seg.length + f) { prog := { base := b0, lfn := fn }, zf := zf }
        = (runStraightF seg b0 zf).bind
            (fun bz => I.lsemFuelMemF P f
              { prog := { base := bz.1, lfn := fn }, zf := bz.2 }) := by
  intro seg
  induction seg with
  | nil =>
      intro b0 zf f _ _ _
      simp only [List.length_nil, Nat.zero_add, runStraightF_nil, Option.bind_some]
  | cons i is ih =>
      intro b0 zf f hlopn hns hpos
      have hi : IsLopn i := hlopn i (by simp)
      have his : ∀ j ∈ is, IsLopn j := fun j hj => hlopn j (by simp [hj])
      have hns' : ∀ j ∈ is, ∀ (Q : LprogM) (s : LstateMF), I.step Q j s = x86Isa.step Q j s :=
        fun j hj => hns j (by simp [hj])
      have hfetch : findInstrMem P
          ({ prog := { base := b0, lfn := fn }, zf := zf } : LstateMF).prog = some i := by
        show findInstrMem P { base := b0, lfn := fn } = some i
        unfold findInstrMem
        rw [ite_eq_left (show ({ base := b0, lfn := fn } : LstatePM).lfn = P.lfn from hfn)]
        have := hpos 0 (by simp)
        simpa using this
      rw [List.length_cons, show is.length + 1 + f = (is.length + f) + 1 from by omega,
        Isa.lsemFuelMemF, hfetch]
      simp only []
      rw [hns i (by simp) P]
      change (match evalInstrPMemF P i _ with
        | some s' => I.lsemFuelMemF P (is.length + f) s'
        | none => none) = _
      rw [evalInstrPMemF_isLopn P i _ hi]
      cases hstep : fstepF i b0 zf with
      | none =>
          simp only [Option.map_none]
          rw [runStraightF_cons, hstep]
          rfl
      | some bz =>
          simp only [Option.map_some]
          rw [runStraightF_cons, hstep, Option.bind_some]
          have hb_lpc : bz.1.lpc = b0.lpc + 1 :=
            fstepF_lpc_succ i b0 bz.1 zf bz.2 (by rw [hstep])
          have hpos' : ∀ k, k < is.length → P.body[bz.1.lpc + k]? = is[k]? := by
            intro k hk
            have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
            rw [hb_lpc, show b0.lpc + 1 + k = b0.lpc + (k + 1) from by omega, hp]
            simp
          exact ih bz.1 bz.2 f his hns' hpos'

/-- **Extended straight-line segment run with continuation fuel.**  The
    `Lopn ∪ MOV ∪ CMP` extension of `lsemFuelMemF_seg`: an all-`Lopn`
    segment (reg-copy `MOV`s and flag-`CMP`s allowed) at positions
    `lpc .. lpc+|seg|-1` executes the extended fold `runStraightF` and
    continues with `f` fuel. -/
theorem lsemFuelMemF_segF (P : LprogM) (fn : String) (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b0 : LstateM) (zf : Bool) (f : Nat),
      (∀ i ∈ seg, IsLopn i) →
      (∀ k, k < seg.length → P.body[b0.lpc + k]? = seg[k]?) →
      lsemFuelMemF P (seg.length + f) { prog := { base := b0, lfn := fn }, zf := zf }
        = (runStraightF seg b0 zf).bind
            (fun bz => lsemFuelMemF P f
              { prog := { base := bz.1, lfn := fn }, zf := bz.2 }) := by
  intro seg b0 zf f hl hpos
  rw [← X86Backend.X86Isa.x86Isa_lsemFuelMemF]
  exact lsemFuelMemF_segF_agree P fn hfn seg b0 zf f hl (fun _ _ _ _ => rfl) hpos

end Calls

/-! ## 2. The flag block grammar: straight segments and flag-guarded regions

`FBlock` is the flag-machine analogue of the inline nest's `IBlock`: a straight all-`Lopn`
segment (reg-copy `MOV`s and flag-`CMP`s included — stepped by `fstepF`), a
bare flag-guarded loop region (`flagLoopLinstrRM` — the pinned flag back-edge
idiom), or a zero-trip-guarded region (`guardedFlagLoopLinstrRM` — the full
per-level `forLoopLcmdNRtNested` skeleton).  Regions nest to arbitrary depth
(the block tree is the depth index). -/

/-- A flag-machine segment block. -/
inductive FBlock : Type where
  /-- A straight all-`Lopn` segment (`Lopn ∪ reg-copy MOV ∪ flag-CMP`). -/
  | straight (seg : List LinstrRM) : FBlock
  /-- A bare flag-guarded loop region at label `top` with counter `nReg`:
      `Llabel top :: flat ++ [CMP nReg,#0 ; Lcond NZ top]`. -/
  | region (top : LLabel) (nReg : String) (body : List FBlock) : FBlock
  /-- A zero-trip-guarded region: `CMP nReg,#0 ; Lcond Z endL` in front of the
      bare region, `Llabel endL` behind — the emitted per-level skeleton. -/
  | guarded (top endL : LLabel) (nReg : String) (body : List FBlock) : FBlock

mutual
/-- The flattened instruction stream of a flag block. -/
def FBlock.flat : FBlock → List LinstrRM
  | .straight seg => seg
  | .region top nReg body => flagLoopLinstrRM top nReg (flatFL body)
  | .guarded top endL nReg body => guardedFlagLoopLinstrRM top endL nReg (flatFL body)
/-- The flattened instruction stream of a flag block list. -/
def flatFL : List FBlock → List LinstrRM
  | [] => []
  | b :: rest => b.flat ++ flatFL rest
end

@[simp] theorem fflat_straight (seg : List LinstrRM) :
    (FBlock.straight seg).flat = seg := by rw [FBlock.flat]

@[simp] theorem fflat_region (top : LLabel) (nReg : String) (body : List FBlock) :
    (FBlock.region top nReg body).flat = flagLoopLinstrRM top nReg (flatFL body) := by
  rw [FBlock.flat]

@[simp] theorem fflat_guarded (top endL : LLabel) (nReg : String) (body : List FBlock) :
    (FBlock.guarded top endL nReg body).flat
      = guardedFlagLoopLinstrRM top endL nReg (flatFL body) := by
  rw [FBlock.flat]

@[simp] theorem fflatFL_nil : flatFL [] = [] := by rw [flatFL]

@[simp] theorem fflatFL_cons (b : FBlock) (rest : List FBlock) :
    flatFL (b :: rest) = b.flat ++ flatFL rest := by rw [flatFL]

/-- The bare flag-loop shape's length: label + body + `CMP` + `Lcond`. -/
theorem flagLoop_length (top : LLabel) (nReg : String) (body : List LinstrRM) :
    (flagLoopLinstrRM top nReg body).length = body.length + 3 := by
  simp [flagLoopLinstrRM, flagBackedge]

/-- The guarded shape's length: guard `CMP`/`Lcond Z` + bare loop + `Llabel endL`. -/
theorem guardedFlagLoop_length (top endL : LLabel) (nReg : String)
    (body : List LinstrRM) :
    (guardedFlagLoopLinstrRM top endL nReg body).length = body.length + 6 := by
  simp [guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge]

mutual
/-- Flag-block well-formedness: a straight block is all-`Lopn` (the extended
    step covers the reg-copy `MOV` and flag-`CMP` forms, which ARE `Lopn`s);
    region bodies are recursively well-formed. -/
def FBlockOK : FBlock → Prop
  | .straight seg => ∀ i ∈ seg, IsLopn i
  | .region _ _ body => FBlocksOK body
  | .guarded _ _ _ body => FBlocksOK body
/-- Flag-block-list well-formedness. -/
def FBlocksOK : List FBlock → Prop
  | [] => True
  | b :: rest => FBlockOK b ∧ FBlocksOK rest
end

@[simp] theorem FBlockOK_straight (seg : List LinstrRM) :
    FBlockOK (.straight seg) = ∀ i ∈ seg, IsLopn i := by rw [FBlockOK]

@[simp] theorem FBlockOK_region (top : LLabel) (nReg : String) (body : List FBlock) :
    FBlockOK (.region top nReg body) = FBlocksOK body := by rw [FBlockOK]

@[simp] theorem FBlockOK_guarded (top endL : LLabel) (nReg : String)
    (body : List FBlock) :
    FBlockOK (.guarded top endL nReg body) = FBlocksOK body := by rw [FBlockOK]

@[simp] theorem FBlocksOK_nil : FBlocksOK [] = True := by rw [FBlocksOK]

@[simp] theorem FBlocksOK_cons (b : FBlock) (rest : List FBlock) :
    FBlocksOK (b :: rest) = (FBlockOK b ∧ FBlocksOK rest) := by rw [FBlocksOK]

mutual
/-- Label resolution at absolute position `p`: each region's `top` (and, for a
    guarded region, its `endL`) is the FIRST occurrence of that label in the
    whole program body — labels distinct per nesting depth, as the lowering
    guarantees (`d` vs `d+1` tops, `d+0x40000000` ends). -/
def FBlockResolves (P : LprogM) : FBlock → Nat → Prop
  | .straight _, _ => True
  | .region top _ body, p =>
      findLabelMem top P.body = some p ∧ FBlocksResolve P body (p + 1)
  | .guarded top endL _ body, p =>
      findLabelMem top P.body = some (p + 2)
        ∧ findLabelMem endL P.body = some (p + (flatFL body).length + 5)
        ∧ FBlocksResolve P body (p + 3)
/-- Label resolution for a flag block list starting at absolute position `p`. -/
def FBlocksResolve (P : LprogM) : List FBlock → Nat → Prop
  | [], _ => True
  | b :: rest, p => FBlockResolves P b p ∧ FBlocksResolve P rest (p + b.flat.length)
end

@[simp] theorem FBlockResolves_straight (P : LprogM) (seg : List LinstrRM) (p : Nat) :
    FBlockResolves P (.straight seg) p = True := by rw [FBlockResolves]

@[simp] theorem FBlockResolves_region (P : LprogM) (top : LLabel) (nReg : String)
    (body : List FBlock) (p : Nat) :
    FBlockResolves P (.region top nReg body) p
      = (findLabelMem top P.body = some p ∧ FBlocksResolve P body (p + 1)) := by
  rw [FBlockResolves]

@[simp] theorem FBlockResolves_guarded (P : LprogM) (top endL : LLabel) (nReg : String)
    (body : List FBlock) (p : Nat) :
    FBlockResolves P (.guarded top endL nReg body) p
      = (findLabelMem top P.body = some (p + 2)
          ∧ findLabelMem endL P.body = some (p + (flatFL body).length + 5)
          ∧ FBlocksResolve P body (p + 3)) := by
  rw [FBlockResolves]

@[simp] theorem FBlocksResolve_nil (P : LprogM) (p : Nat) :
    FBlocksResolve P [] p = True := by rw [FBlocksResolve]

@[simp] theorem FBlocksResolve_cons (P : LprogM) (b : FBlock) (rest : List FBlock)
    (p : Nat) :
    FBlocksResolve P (b :: rest) p
      = (FBlockResolves P b p ∧ FBlocksResolve P rest (p + b.flat.length)) := by
  rw [FBlocksResolve]

/-! ## 3. The spec fold: straight blocks via `runStraightF`, regions as
data-dependent do-whiles with a counter read

`runFRegionF nReg body q` is the do-while from the top of a region's body
(pc `q`): run the body blocks (flag threaded), READ the counter (`getW` — the
emitted `CMP` evaluates its operand, so a read miss is stuck, not a fall
through), loop while non-zero (pc back to `q`, flag `false` — the just-run
`CMP` saw non-zero), exit at `q + |flat| + 2` (past the back-edge) with flag
`true` (the exit compare saw zero).  The fuel bounds taken back-edges. -/

mutual
/-- Run one flag block from its own position (`s.lpc`). -/
def runFB : Nat → FBlock → LstateM → Bool → Option (LstateM × Bool)
  | _, .straight seg, s, zf => runStraightF seg s zf
  | wf, .region _ nReg body, s, zf =>
      runFRegionF wf nReg body (s.lpc + 1) (s.setLpc (s.lpc + 1)) zf
  | wf, .guarded _ _ nReg body, s, _ =>
      match s.reg.getW nReg 64 with
      | none => none
      | some v =>
          if v == 0#64 then
            some (s.setLpc (s.lpc + (flatFL body).length + 6), true)
          else
            (runFRegionF wf nReg body (s.lpc + 3) (s.setLpc (s.lpc + 3)) false).map
              (fun bz => (bz.1.setLpc (s.lpc + (flatFL body).length + 6), bz.2))
  termination_by wf blk _ _ => (wf, sizeOf blk, 1)
/-- Run a flag block list in sequence, threading state and flag. -/
def runFBsL : Nat → List FBlock → LstateM → Bool → Option (LstateM × Bool)
  | _, [], s, zf => some (s, zf)
  | wf, b :: rest, s, zf => (runFB wf b s zf).bind (fun bz => runFBsL wf rest bz.1 bz.2)
  termination_by wf blks _ _ => (wf, sizeOf blks, 2)
/-- The region do-while from the top of the body (pc `q`). -/
def runFRegionF : Nat → String → List FBlock → Nat → LstateM → Bool →
    Option (LstateM × Bool)
  | 0, _, _, _, _, _ => none
  | wf + 1, nReg, body, q, s, zf =>
      (runFBsL wf body s zf).bind (fun bz =>
        match bz.1.reg.getW nReg 64 with
        | none => none
        | some v =>
            if v == 0#64 then
              some (bz.1.setLpc (q + (flatFL body).length + 2), true)
            else runFRegionF wf nReg body q (bz.1.setLpc q) false)
  termination_by wf _ body _ _ _ => (wf, sizeOf body, 0)
end

theorem runFB_straight (wf : Nat) (seg : List LinstrRM) (s : LstateM) (zf : Bool) :
    runFB wf (.straight seg) s zf = runStraightF seg s zf := by rw [runFB]

theorem runFB_region (wf : Nat) (top : LLabel) (nReg : String) (body : List FBlock)
    (s : LstateM) (zf : Bool) :
    runFB wf (.region top nReg body) s zf
      = runFRegionF wf nReg body (s.lpc + 1) (s.setLpc (s.lpc + 1)) zf := by rw [runFB]

theorem runFB_guarded (wf : Nat) (top endL : LLabel) (nReg : String)
    (body : List FBlock) (s : LstateM) (zf : Bool) :
    runFB wf (.guarded top endL nReg body) s zf
      = match s.reg.getW nReg 64 with
        | none => none
        | some v =>
            if v == 0#64 then
              some (s.setLpc (s.lpc + (flatFL body).length + 6), true)
            else
              (runFRegionF wf nReg body (s.lpc + 3) (s.setLpc (s.lpc + 3)) false).map
                (fun bz => (bz.1.setLpc (s.lpc + (flatFL body).length + 6), bz.2)) := by
  rw [runFB]

@[simp] theorem runFBsL_nil (wf : Nat) (s : LstateM) (zf : Bool) :
    runFBsL wf [] s zf = some (s, zf) := by rw [runFBsL]

theorem runFBsL_cons (wf : Nat) (b : FBlock) (rest : List FBlock) (s : LstateM)
    (zf : Bool) :
    runFBsL wf (b :: rest) s zf
      = (runFB wf b s zf).bind (fun bz => runFBsL wf rest bz.1 bz.2) := by rw [runFBsL]

@[simp] theorem runFRegionF_zero (nReg : String) (body : List FBlock) (q : Nat)
    (s : LstateM) (zf : Bool) : runFRegionF 0 nReg body q s zf = none := by
  rw [runFRegionF]

theorem runFRegionF_succ (wf : Nat) (nReg : String) (body : List FBlock) (q : Nat)
    (s : LstateM) (zf : Bool) :
    runFRegionF (wf + 1) nReg body q s zf
      = (runFBsL wf body s zf).bind (fun bz =>
          match bz.1.reg.getW nReg 64 with
          | none => none
          | some v =>
              if v == 0#64 then
                some (bz.1.setLpc (q + (flatFL body).length + 2), true)
              else runFRegionF wf nReg body q (bz.1.setLpc q) false) := by
  rw [runFRegionF]

/-! ### The step count of the spec fold

`stepsFB`/`stepsFBsL`/`stepsFRegionF` count the flag-machine steps of a terminating spec
fold, by the recursion of `runFB`/`runFBsL`/`runFRegionF`: a straight segment takes its
length, a region label one step, each back-edge two (`CMP`, `Lcond NZ`), a guard two
(`CMP`, `Lcond Z`) and a skip label one.  On a fold that does not terminate the count is
that of the prefix that ran. -/

mutual
/-- The flag-machine steps of one block run by `runFB`. -/
def stepsFB : Nat → FBlock → LstateM → Bool → Nat
  | _, .straight seg, _, _ => seg.length
  | wf, .region _ nReg body, s, zf =>
      1 + stepsFRegionF wf nReg body (s.lpc + 1) (s.setLpc (s.lpc + 1)) zf
  | wf, .guarded _ _ nReg body, s, _ =>
      match s.reg.getW nReg 64 with
      | none => 0
      | some v =>
          if v == 0#64 then 2
          else
            2 + 1 + stepsFRegionF wf nReg body (s.lpc + 3) (s.setLpc (s.lpc + 3)) false + 1
  termination_by wf blk _ _ => (wf, sizeOf blk, 1)
/-- The flag-machine steps of a block list run by `runFBsL`. -/
def stepsFBsL : Nat → List FBlock → LstateM → Bool → Nat
  | _, [], _, _ => 0
  | wf, b :: rest, s, zf =>
      stepsFB wf b s zf +
        match runFB wf b s zf with
        | none => 0
        | some bz => stepsFBsL wf rest bz.1 bz.2
  termination_by wf blks _ _ => (wf, sizeOf blks, 2)
/-- The flag-machine steps of the region do-while run by `runFRegionF`. -/
def stepsFRegionF : Nat → String → List FBlock → Nat → LstateM → Bool → Nat
  | 0, _, _, _, _, _ => 0
  | wf + 1, nReg, body, q, s, zf =>
      stepsFBsL wf body s zf +
        match runFBsL wf body s zf with
        | none => 0
        | some bz =>
            match bz.1.reg.getW nReg 64 with
            | none => 0
            | some v =>
                if v == 0#64 then 2
                else 2 + stepsFRegionF wf nReg body q (bz.1.setLpc q) false
  termination_by wf _ body _ _ _ => (wf, sizeOf body, 0)
end

theorem stepsFB_straight (wf : Nat) (seg : List LinstrRM) (s : LstateM) (zf : Bool) :
    stepsFB wf (.straight seg) s zf = seg.length := by rw [stepsFB]

theorem stepsFB_region (wf : Nat) (top : LLabel) (nReg : String) (body : List FBlock)
    (s : LstateM) (zf : Bool) :
    stepsFB wf (.region top nReg body) s zf
      = 1 + stepsFRegionF wf nReg body (s.lpc + 1) (s.setLpc (s.lpc + 1)) zf := by
  rw [stepsFB]

theorem stepsFB_guarded (wf : Nat) (top endL : LLabel) (nReg : String)
    (body : List FBlock) (s : LstateM) (zf : Bool) :
    stepsFB wf (.guarded top endL nReg body) s zf
      = match s.reg.getW nReg 64 with
        | none => 0
        | some v =>
            if v == 0#64 then 2
            else
              2 + 1 + stepsFRegionF wf nReg body (s.lpc + 3) (s.setLpc (s.lpc + 3)) false
                + 1 := by
  rw [stepsFB]

@[simp] theorem stepsFBsL_nil (wf : Nat) (s : LstateM) (zf : Bool) :
    stepsFBsL wf [] s zf = 0 := by rw [stepsFBsL]

theorem stepsFBsL_cons (wf : Nat) (b : FBlock) (rest : List FBlock) (s : LstateM)
    (zf : Bool) :
    stepsFBsL wf (b :: rest) s zf
      = stepsFB wf b s zf +
          match runFB wf b s zf with
          | none => 0
          | some bz => stepsFBsL wf rest bz.1 bz.2 := by rw [stepsFBsL]

@[simp] theorem stepsFRegionF_zero (nReg : String) (body : List FBlock) (q : Nat)
    (s : LstateM) (zf : Bool) : stepsFRegionF 0 nReg body q s zf = 0 := by
  rw [stepsFRegionF]

theorem stepsFRegionF_succ (wf : Nat) (nReg : String) (body : List FBlock) (q : Nat)
    (s : LstateM) (zf : Bool) :
    stepsFRegionF (wf + 1) nReg body q s zf
      = stepsFBsL wf body s zf +
          match runFBsL wf body s zf with
          | none => 0
          | some bz =>
              match bz.1.reg.getW nReg 64 with
              | none => 0
              | some v =>
                  if v == 0#64 then 2
                  else 2 + stepsFRegionF wf nReg body q (bz.1.setLpc q) false := by
  rw [stepsFRegionF]

/-- The steps of a single straight block are its length. -/
theorem stepsFBsL_straight (wf : Nat) (seg : List LinstrRM) (s : LstateM) (zf : Bool) :
    stepsFBsL wf [.straight seg] s zf = seg.length := by
  rw [stepsFBsL_cons, stepsFB_straight]
  cases runFB wf (.straight seg) s zf <;> simp

/-- The fuel bound of a zero-trip-guarded loop of a straight body of `len` instructions at
    back-edge budget `m`: `len + 2` steps for each pass, and four for the guard, the loop
    label and the skip label. -/
def guardedLoopFuel (len m : Nat) : Nat := m * (len + 2) + 4

@[simp] theorem guardedLoopFuel_eq (len m : Nat) :
    guardedLoopFuel len m = m * (len + 2) + 4 := rfl

theorem guardedLoopFuel_mono (len : Nat) {m m' : Nat} (h : m ≤ m') :
    guardedLoopFuel len m ≤ guardedLoopFuel len m' :=
  Nat.add_le_add_right (Nat.mul_le_mul_right _ h) 4

/-- A region do-while of a straight body takes at most `|body| + 2` steps for each unit of
    back-edge budget. -/
theorem stepsFRegionF_straight_le (nReg : String) (body : List LinstrRM) (q : Nat) :
    ∀ (wf : Nat) (s : LstateM) (zf : Bool),
      stepsFRegionF wf nReg [.straight body] q s zf ≤ wf * (body.length + 2) := by
  intro wf
  induction wf with
  | zero => intro s zf; rw [stepsFRegionF_zero]; exact Nat.zero_le _
  | succ w ih =>
      intro s zf
      rw [stepsFRegionF_succ, stepsFBsL_straight, Nat.succ_mul]
      cases runFBsL w [.straight body] s zf with
      | none => simp only []; omega
      | some bz =>
          simp only []
          cases bz.1.reg.getW nReg 64 with
          | none => simp only []; omega
          | some v =>
              simp only []
              have := ih (bz.1.setLpc q) false
              split <;> omega

/-- A zero-trip-guarded loop of a straight body takes at most `guardedLoopFuel` steps. -/
theorem stepsFB_guarded_straight_le (wf : Nat) (top endL : LLabel) (nReg : String)
    (body : List LinstrRM) (s : LstateM) (zf : Bool) :
    stepsFB wf (.guarded top endL nReg [.straight body]) s zf
      ≤ guardedLoopFuel body.length wf := by
  rw [stepsFB_guarded, guardedLoopFuel_eq]
  cases s.reg.getW nReg 64 with
  | none => simp only []; omega
  | some v =>
      simp only []
      have := stepsFRegionF_straight_le nReg body (s.lpc + 3) wf (s.setLpc (s.lpc + 3)) false
      split <;> omega

/-! ### pc-faithfulness of the spec fold -/

/-- A region do-while exits past its back-edge (`q + |flat| + 2`). -/
theorem runFRegionF_lpc (nReg : String) (body : List FBlock) (q : Nat) :
    ∀ (wf : Nat) (s : LstateM) (zf : Bool) (b : LstateM) (zb : Bool),
      runFRegionF wf nReg body q s zf = some (b, zb) →
      b.lpc = q + (flatFL body).length + 2 := by
  intro wf
  induction wf with
  | zero => intro s zf b zb h; rw [runFRegionF_zero] at h; exact absurd h (by simp)
  | succ w ih =>
      intro s zf b zb h
      rw [runFRegionF_succ] at h
      cases hb1 : runFBsL w body s zf with
      | none => rw [hb1] at h; simp at h
      | some bz =>
          rw [hb1, Option.bind_some] at h
          cases hv : bz.1.reg.getW nReg 64 with
          | none => rw [hv] at h; simp at h
          | some v =>
              rw [hv] at h
              simp only [] at h
              by_cases hz : (v == 0#64) = true
              · rw [ite_eq_left hz] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                simp
              · rw [ite_eq_right hz] at h
                exact ih _ _ b zb h

/-- A region do-while exits with the flag SET (the exit compare saw zero). -/
theorem runFRegionF_zf (nReg : String) (body : List FBlock) (q : Nat) :
    ∀ (wf : Nat) (s : LstateM) (zf : Bool) (b : LstateM) (zb : Bool),
      runFRegionF wf nReg body q s zf = some (b, zb) → zb = true := by
  intro wf
  induction wf with
  | zero => intro s zf b zb h; rw [runFRegionF_zero] at h; exact absurd h (by simp)
  | succ w ih =>
      intro s zf b zb h
      rw [runFRegionF_succ] at h
      cases hb1 : runFBsL w body s zf with
      | none => rw [hb1] at h; simp at h
      | some bz =>
          rw [hb1, Option.bind_some] at h
          cases hv : bz.1.reg.getW nReg 64 with
          | none => rw [hv] at h; simp at h
          | some v =>
              rw [hv] at h
              simp only [] at h
              by_cases hz : (v == 0#64) = true
              · rw [ite_eq_left hz] at h
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
                rfl
              · rw [ite_eq_right hz] at h
                exact ih _ _ b zb h

/-- A successful flag-block run advances the pc by the block's flat length. -/
theorem runFB_lpc (wf : Nat) (blk : FBlock) (s : LstateM) (zf : Bool) (b : LstateM)
    (zb : Bool) (h : runFB wf blk s zf = some (b, zb)) :
    b.lpc = s.lpc + blk.flat.length := by
  cases blk with
  | straight seg =>
      rw [runFB_straight] at h
      rw [fflat_straight]
      exact runStraightF_lpc seg s zf b zb h
  | region top nReg body =>
      rw [runFB_region] at h
      have := runFRegionF_lpc nReg body (s.lpc + 1) wf _ _ b zb h
      rw [fflat_region, flagLoop_length]
      omega
  | guarded top endL nReg body =>
      rw [runFB_guarded] at h
      cases hv : s.reg.getW nReg 64 with
      | none => rw [hv] at h; simp at h
      | some v =>
          rw [hv] at h
          simp only [] at h
          by_cases hz : (v == 0#64) = true
          · rw [ite_eq_left hz] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
            rw [fflat_guarded, guardedFlagLoop_length]
            simp only [LstateM.lpc_setLpc]
            omega
          · rw [ite_eq_right hz] at h
            obtain ⟨bz, hbz, hrfl⟩ := Option.map_eq_some_iff.mp h
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hrfl
            rw [fflat_guarded, guardedFlagLoop_length]
            simp only [LstateM.lpc_setLpc]
            omega

/-- A successful flag-block-list run advances the pc by the flattened length. -/
theorem runFBsL_lpc :
    ∀ (blks : List FBlock) (wf : Nat) (s : LstateM) (zf : Bool) (b : LstateM)
      (zb : Bool),
      runFBsL wf blks s zf = some (b, zb) → b.lpc = s.lpc + (flatFL blks).length := by
  intro blks
  induction blks with
  | nil =>
      intro wf s zf b zb h
      rw [runFBsL_nil] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      simp
  | cons blk rest ih =>
      intro wf s zf b zb h
      rw [runFBsL_cons] at h
      cases hb1 : runFB wf blk s zf with
      | none => rw [hb1] at h; simp at h
      | some bz =>
          rw [hb1, Option.bind_some] at h
          have h1 := runFB_lpc wf blk s zf bz.1 bz.2 (by rw [hb1])
          have h2 := ih wf bz.1 bz.2 b zb h
          rw [h2, h1, fflatFL_cons, List.length_append]
          omega

/-! ## 4. Position and label facts for the two region shapes

The bare shape's positions are `flagLoop_body_pos`/`flagLoop_cmp_pos`/
`flagLoop_cond_pos`; the guarded shape peels its two-instruction guard and its
trailing skip label onto them. -/

/-- Guarded shape, index 0: the zero-trip guard `CMP nReg,#0`. -/
theorem guarded_get_cmp0 (top endL : LLabel) (nReg : String) (body : List LinstrRM) :
    (guardedFlagLoopLinstrRM top endL nReg body)[0]?
      = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0],
          MemTag.reg none) := rfl

/-- Guarded shape, index 1: the forward skip `Lcond Z endL`. -/
theorem guarded_get_condZ (top endL : LLabel) (nReg : String) (body : List LinstrRM) :
    (guardedFlagLoopLinstrRM top endL nReg body)[1]?
      = some (.Lcond (.reg "Z") endL, MemTag.reg none) := rfl

/-- Guarded shape, index `2 + j` (`j < |body| + 3`): the bare loop shape at `j`. -/
theorem guarded_get_shift (top endL : LLabel) (nReg : String) (body : List LinstrRM)
    (j : Nat) (hj : j < body.length + 3) :
    (guardedFlagLoopLinstrRM top endL nReg body)[2 + j]?
      = (flagLoopLinstrRM top nReg body)[j]? := by
  unfold guardedFlagLoopLinstrRM
  rw [List.getElem?_append_left
    (by simp only [List.length_cons, flagLoop_length]; omega)]
  rw [show 2 + j = (j + 1) + 1 from by omega, List.getElem?_cons_succ,
    List.getElem?_cons_succ]

/-- Guarded shape, index `|body| + 5`: the skip label `Llabel endL`. -/
theorem guarded_get_endL (top endL : LLabel) (nReg : String) (body : List LinstrRM) :
    (guardedFlagLoopLinstrRM top endL nReg body)[body.length + 5]?
      = some (.Llabel .internal endL, MemTag.reg none) := by
  unfold guardedFlagLoopLinstrRM
  rw [List.getElem?_append_right
    (by simp only [List.length_cons, flagLoop_length]; omega)]
  simp only [List.length_cons, flagLoop_length]
  rw [show body.length + 5 - (body.length + 3 + 1 + 1) = 0 from by omega]
  rfl

/-! ## 5. Machine-step helpers -/

/-- Fetch against the program's own function name reads the body at the pc. -/
theorem findInstrMemF_self (P : LprogM) (x : LstateM) :
    findInstrMem P ({ base := x, lfn := P.lfn } : LstatePM) = P.body[x.lpc]? := by
  unfold findInstrMem
  rw [ite_eq_left rfl]

/-- The flag machine steps a label as the counter-register delegate: pc bump, flag unchanged. -/
theorem evalInstrPMemF_label (P : LprogM) (lk : LabelKind) (lbl : LLabel)
    (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (.Llabel lk lbl, tag) s
      = some { s with prog := { s.prog with base := s.prog.base.nextPc } } := rfl

/-- `nextPc` then `setLpc` collapses to the `setLpc`. -/
theorem LstateM.nextPc_setLpc' (x : LstateM) (a : Nat) :
    x.nextPc.setLpc a = x.setLpc a := rfl

/-- Two fall-through steps are a pc write. -/
theorem LstateM.nextPc_nextPc' (x : LstateM) : x.nextPc.nextPc = x.setLpc (x.lpc + 2) :=
  rfl

/-- Three fall-through steps are a pc write. -/
theorem LstateM.nextPc_nextPc_nextPc' (x : LstateM) :
    x.nextPc.nextPc.nextPc = x.setLpc (x.lpc + 3) := rfl

/-- A fall-through step after a pc write is a pc write. -/
theorem LstateM.setLpc_nextPc' (x : LstateM) (a : Nat) :
    (x.setLpc a).nextPc = x.setLpc (a + 1) := rfl

/-! ## 6. The control-flow-aware segment lemma over the flag machine (`segFCore`)

The joint statement at back-edge budget `wf`, proved by a fresh strong
induction on `wf` mirroring the inline nest's `segCore` — the CMP step is absorbed into each
back-edge decision (fetch the `CMP`, materialise `zf = (counter == 0)`, then
the `Lcond NZ`/`Z` reads it; `zf_after_cmp_eq_not_condNZ` content, applied
here as the two `by_cases` arms on the counter read). -/

/-- The block-list segment lemma at budget `wf` (the induction carrier). -/
def SegFBlocksAt (P : LprogM) (wf : Nat) : Prop :=
  ∀ (blks : List FBlock) (b0 : LstateM) (zf : Bool) (b : LstateM) (zb : Bool),
    FBlocksOK blks →
    (∀ k, k < (flatFL blks).length → P.body[b0.lpc + k]? = (flatFL blks)[k]?) →
    FBlocksResolve P blks b0.lpc →
    runFBsL wf blks b0 zf = some (b, zb) →
    ∀ f,
      lsemFuelMemF P (stepsFBsL wf blks b0 zf + f)
          { prog := { base := b0, lfn := P.lfn }, zf := zf }
        = lsemFuelMemF P f { prog := { base := b, lfn := P.lfn }, zf := zb }

/-- The region-run lemma at budget `wf` (the induction carrier): from the top
    of a region's body (pc = `tp + 1`, one past the region's `Llabel`), a
    terminating region do-while is realised by the machine.  The back-edge
    segment (`CMP nReg,#0` at `tp+1+|flat|`, `Lcond NZ top` at `tp+2+|flat|`)
    and the label resolution are given positionally, so the SAME carrier serves
    the bare and the guarded region shapes. -/
def SegFRegionAt (P : LprogM) (wf : Nat) : Prop :=
  ∀ (top : LLabel) (nReg : String) (body : List FBlock) (tp : Nat)
    (b0 : LstateM) (zf : Bool) (b : LstateM) (zb : Bool),
    FBlocksOK body →
    (∀ k, k < (flatFL body).length → P.body[tp + 1 + k]? = (flatFL body)[k]?) →
    P.body[tp + 1 + (flatFL body).length]?
      = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0],
          MemTag.reg none) →
    P.body[tp + 2 + (flatFL body).length]?
      = some (.Lcond (.reg "NZ") top, MemTag.reg none) →
    findLabelMem top P.body = some tp →
    FBlocksResolve P body (tp + 1) →
    b0.lpc = tp + 1 →
    runFRegionF wf nReg body (tp + 1) b0 zf = some (b, zb) →
    ∀ f,
      lsemFuelMemF P (stepsFRegionF wf nReg body (tp + 1) b0 zf + f)
          { prog := { base := b0, lfn := P.lfn }, zf := zf }
        = lsemFuelMemF P f { prog := { base := b, lfn := P.lfn }, zf := zb }

/-- **The control-flow-aware segment lemma over the flag machine** (joint form).
    Strong induction on the back-edge budget; regions recurse through the
    budget, blocks through the list.  The fuel consumed is the step count of the
    spec fold (`stepsFRegionF`, `stepsFBsL`). -/
theorem segFCore (P : LprogM) :
    ∀ wf : Nat, SegFRegionAt P wf ∧ SegFBlocksAt P wf := by
  intro wf
  induction wf using Nat.strongRecOn with
  | ind wf ih =>
    -- ── the region half at `wf` ──
    have hreg : SegFRegionAt P wf := by
      cases wf with
      | zero =>
          intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun
          rw [runFRegionF_zero] at hrun
          exact absurd hrun (by simp)
      | succ w =>
          intro top nReg body tp b0 zf b zb hok hpos hcmpP hcondP hlbl hres hpc hrun
          rw [runFRegionF_succ] at hrun
          cases hb1 : runFBsL w body b0 zf with
          | none => rw [hb1] at hrun; simp at hrun
          | some bz =>
              rw [hb1, Option.bind_some] at hrun
              -- the body pass, via the block lemma at budget `w`
              have hposB : ∀ k, k < (flatFL body).length →
                  P.body[b0.lpc + k]? = (flatFL body)[k]? := by
                intro k hk
                rw [hpc]
                exact hpos k hk
              have hn1 := (ih w (Nat.lt_succ_self w)).2 body b0 zf bz.1 bz.2
                hok hposB (by rw [hpc]; exact hres) (by rw [hb1])
              generalize hn1e : stepsFBsL w body b0 zf = n1 at hn1
              -- the state after the body sits at the back-edge `CMP`
              have hbz_lpc : bz.1.lpc = tp + 1 + (flatFL body).length := by
                have := runFBsL_lpc body w b0 zf bz.1 bz.2 (by rw [hb1])
                rw [hpc] at this
                exact this
              cases hv : bz.1.reg.getW nReg 64 with
              | none => rw [hv] at hrun; simp at hrun
              | some v =>
                  rw [hv] at hrun
                  simp only [] at hrun
                  -- machine: fetch + step the back-edge `CMP`
                  have hfetchCmp : findInstrMem P
                      ({ prog := { base := bz.1, lfn := P.lfn }, zf := bz.2 }
                        : LstateMF).prog
                        = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP")
                            [.reg nReg, .imm 0], MemTag.reg none) := by
                    show findInstrMem P ({ base := bz.1, lfn := P.lfn } : LstatePM) = _
                    rw [findInstrMemF_self, hbz_lpc]
                    exact hcmpP
                  have hevalCmp := evalInstrPMemF_cmp P (.reg nReg) nReg
                    (MemTag.reg none)
                    { prog := { base := bz.1, lfn := P.lfn }, zf := bz.2 } v hv
                  -- machine: fetch the back-edge `Lcond NZ`
                  have hfetchCond : findInstrMem P
                      ({ prog := { base := bz.1.nextPc, lfn := P.lfn },
                         zf := (v == 0#64) } : LstateMF).prog
                        = some (.Lcond (.reg "NZ") top, MemTag.reg none) := by
                    show findInstrMem P ({ base := bz.1.nextPc, lfn := P.lfn }
                      : LstatePM) = _
                    rw [findInstrMemF_self, LstateM.lpc_nextPc, hbz_lpc,
                      show tp + 1 + (flatFL body).length + 1
                        = tp + 2 + (flatFL body).length from by omega]
                    exact hcondP
                  by_cases hz : (v == 0#64) = true
                  · -- EXIT: the compare saw zero; `Lcond NZ` falls through
                    rw [ite_eq_left hz] at hrun
                    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrun
                    have hbase2 : bz.1.nextPc.nextPc
                        = bz.1.setLpc (tp + 1 + (flatFL body).length + 2) := by
                      rw [LstateM.nextPc_nextPc', hbz_lpc]
                    have hevalCond : evalInstrPMemF P
                        (.Lcond (.reg "NZ") top, MemTag.reg none)
                        { prog := { base := bz.1.nextPc, lfn := P.lfn },
                          zf := v == 0#64 }
                          = some { prog :=
                              { base := bz.1.setLpc
                                  (tp + 1 + (flatFL body).length + 2),
                                lfn := P.lfn }, zf := true } := by
                      rw [evalInstrPMemF_jne]
                      rw [ite_eq_right (by simp [hz])]
                      show (some (⟨⟨bz.1.nextPc.nextPc, P.lfn⟩,
                        v == 0#64⟩ : LstateMF) = _)
                      rw [hbase2, hz]
                    have hsteps : stepsFRegionF (w + 1) nReg body (tp + 1) b0 zf = n1 + 2 := by
                      rw [stepsFRegionF_succ, hn1e, hb1]
                      simp only [hv, hz, ite_true]
                    intro f
                    rw [hsteps, show n1 + 2 + f = n1 + (2 + f) from by omega, hn1 (2 + f),
                      show 2 + f = (1 + f) + 1 from by omega,
                      lsemFuelMemF_step P (1 + f) _ _ _ hfetchCmp hevalCmp,
                      show 1 + f = f + 1 from by omega,
                      lsemFuelMemF_step P f _ _ _ hfetchCond hevalCond]
                  · -- TAKEN: the compare saw non-zero; `Lcond NZ` jumps to `top`
                    rw [ite_eq_right hz] at hrun
                    have hz' : (v == 0#64) = false := by simpa using hz
                    have hevalCond : evalInstrPMemF P
                        (.Lcond (.reg "NZ") top, MemTag.reg none)
                        { prog := { base := bz.1.nextPc, lfn := P.lfn },
                          zf := v == 0#64 }
                          = some { prog :=
                              { base := bz.1.setLpc (tp + 1),
                                lfn := P.lfn }, zf := false } := by
                      rw [evalInstrPMemF_jne]
                      rw [ite_eq_left hz']
                      unfold evalJumpMem
                      rw [hlbl]
                      simp only [Option.map_some]
                      show (some (⟨⟨bz.1.nextPc.setLpc (tp + 1), P.lfn⟩,
                        v == 0#64⟩ : LstateMF) = _)
                      rw [LstateM.nextPc_setLpc', hz']
                    -- recurse through the budget at the region's own label
                    have hn2 := (ih w (Nat.lt_succ_self w)).1 top nReg body tp
                      (bz.1.setLpc (tp + 1)) false b zb hok hpos hcmpP hcondP hlbl hres
                      (by simp) hrun
                    generalize hn2e : stepsFRegionF w nReg body (tp + 1)
                      (bz.1.setLpc (tp + 1)) false = n2 at hn2
                    have hsteps : stepsFRegionF (w + 1) nReg body (tp + 1) b0 zf
                        = n1 + 2 + n2 := by
                      rw [stepsFRegionF_succ, hn1e, hb1]
                      simp only [hv, hz', Bool.false_eq_true, ite_false, hn2e]
                      omega
                    intro f
                    rw [hsteps, show n1 + 2 + n2 + f = n1 + (2 + (n2 + f)) from by omega,
                      hn1 (2 + (n2 + f)),
                      show 2 + (n2 + f) = (1 + (n2 + f)) + 1 from by omega,
                      lsemFuelMemF_step P (1 + (n2 + f)) _ _ _ hfetchCmp hevalCmp,
                      show 1 + (n2 + f) = (n2 + f) + 1 from by omega,
                      lsemFuelMemF_step P (n2 + f) _ _ _ hfetchCond hevalCond]
                    exact hn2 f
    -- ── the single-block lemma at `wf` (from the region half) ──
    have hblk : ∀ (blk : FBlock) (b0 : LstateM) (zf : Bool) (b : LstateM) (zb : Bool),
        FBlockOK blk →
        (∀ k, k < blk.flat.length → P.body[b0.lpc + k]? = blk.flat[k]?) →
        FBlockResolves P blk b0.lpc →
        runFB wf blk b0 zf = some (b, zb) →
        ∀ f,
          lsemFuelMemF P (stepsFB wf blk b0 zf + f)
              { prog := { base := b0, lfn := P.lfn }, zf := zf }
            = lsemFuelMemF P f { prog := { base := b, lfn := P.lfn }, zf := zb } := by
      intro blk b0 zf b zb hok hpos hres hrun
      cases blk with
      | straight seg =>
          -- straight block: the extended segment lemma, never re-proved
          rw [runFB_straight] at hrun
          simp only [fflat_straight] at hpos
          rw [FBlockOK_straight] at hok
          intro f
          rw [stepsFB_straight, lsemFuelMemF_segF P P.lfn rfl seg b0 zf f hok hpos, hrun,
            Option.bind_some]
      | region top nReg body =>
          -- bare region: label step, then the region do-while at `tp := b0.lpc`
          rw [runFB_region] at hrun
          simp only [fflat_region] at hpos
          rw [FBlockOK_region] at hok
          rw [FBlockResolves_region] at hres
          obtain ⟨hlbl, hresB⟩ := hres
          have hfetchL : findInstrMem P
              ({ prog := { base := b0, lfn := P.lfn }, zf := zf } : LstateMF).prog
                = some (.Llabel .internal top, MemTag.reg none) := by
            show findInstrMem P ({ base := b0, lfn := P.lfn } : LstatePM) = _
            rw [findInstrMemF_self]
            have h0 := hpos 0 (by rw [flagLoop_length]; omega)
            rw [Nat.add_zero] at h0
            rw [h0]
            rfl
          have hn2 := hreg top nReg body b0.lpc (b0.setLpc (b0.lpc + 1)) zf b zb
            hok
            (by intro k hk
                have h1 := hpos (1 + k) (by rw [flagLoop_length]; omega)
                rw [show b0.lpc + 1 + k = b0.lpc + (1 + k) from by omega, h1]
                exact flagLoop_body_pos top nReg (flatFL body) k hk)
            (by have h1 := hpos (1 + (flatFL body).length)
                  (by rw [flagLoop_length]; omega)
                rw [show b0.lpc + 1 + (flatFL body).length
                    = b0.lpc + (1 + (flatFL body).length) from by omega, h1]
                exact flagLoop_cmp_pos top nReg (flatFL body))
            (by have h1 := hpos (2 + (flatFL body).length)
                  (by rw [flagLoop_length]; omega)
                rw [show b0.lpc + 2 + (flatFL body).length
                    = b0.lpc + (2 + (flatFL body).length) from by omega, h1]
                exact flagLoop_cond_pos top nReg (flatFL body))
            hlbl hresB (by simp) hrun
          generalize hn2e : stepsFRegionF wf nReg body (b0.lpc + 1)
            (b0.setLpc (b0.lpc + 1)) zf = n2 at hn2
          intro f
          rw [stepsFB_region, hn2e, show 1 + n2 + f = (n2 + f) + 1 from by omega,
            lsemFuelMemF_step P (n2 + f) _ _ _ hfetchL
              (evalInstrPMemF_label P .internal top (MemTag.reg none) _)]
          have hb1 : ({ prog := { base := b0, lfn := P.lfn }, zf := zf }
              : LstateMF).prog.base.nextPc = b0.setLpc (b0.lpc + 1) :=
            LstateM.nextPc_eq_setLpc b0
          rw [hb1]
          exact hn2 f
      | guarded top endL nReg body =>
          -- guarded region: guard `CMP` + `Lcond Z`, then label + do-while + `Llabel endL`
          rw [runFB_guarded] at hrun
          simp only [fflat_guarded] at hpos
          rw [FBlockOK_guarded] at hok
          rw [FBlockResolves_guarded] at hres
          obtain ⟨hlblT, hlblE, hresB⟩ := hres
          cases hv : b0.reg.getW nReg 64 with
          | none => rw [hv] at hrun; simp at hrun
          | some v =>
              rw [hv] at hrun
              simp only [] at hrun
              -- machine: the guard `CMP` at the region head
              have hfetchCmp : findInstrMem P
                  ({ prog := { base := b0, lfn := P.lfn }, zf := zf } : LstateMF).prog
                    = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP")
                        [.reg nReg, .imm 0], MemTag.reg none) := by
                show findInstrMem P ({ base := b0, lfn := P.lfn } : LstatePM) = _
                rw [findInstrMemF_self]
                have h0 := hpos 0 (by rw [guardedFlagLoop_length]; omega)
                rw [Nat.add_zero] at h0
                rw [h0]
                exact guarded_get_cmp0 top endL nReg (flatFL body)
              have hevalCmp := evalInstrPMemF_cmp P (.reg nReg) nReg (MemTag.reg none)
                { prog := { base := b0, lfn := P.lfn }, zf := zf } v hv
              -- machine: the guard `Lcond Z` at head + 1
              have hfetchCond : findInstrMem P
                  ({ prog := { base := b0.nextPc, lfn := P.lfn }, zf := (v == 0#64) }
                    : LstateMF).prog
                    = some (.Lcond (.reg "Z") endL, MemTag.reg none) := by
                show findInstrMem P ({ base := b0.nextPc, lfn := P.lfn }
                  : LstatePM) = _
                rw [findInstrMemF_self, LstateM.lpc_nextPc]
                have h1 := hpos 1 (by rw [guardedFlagLoop_length]; omega)
                rw [h1]
                exact guarded_get_condZ top endL nReg (flatFL body)
              by_cases hz : (v == 0#64) = true
              · -- ZERO-TRIP: `Lcond Z` jumps over the whole region
                rw [ite_eq_left hz] at hrun
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrun
                have hevalCond : evalInstrPMemF P
                    (.Lcond (.reg "Z") endL, MemTag.reg none)
                    { prog := { base := b0.nextPc, lfn := P.lfn }, zf := (v == 0#64) }
                      = some { prog :=
                          { base := b0.setLpc (b0.lpc + (flatFL body).length + 6),
                            lfn := P.lfn }, zf := true } := by
                  rw [evalInstrPMemF_je]
                  rw [ite_eq_left hz]
                  unfold evalJumpMem
                  rw [hlblE]
                  simp only [Option.map_some]
                  show (some (⟨⟨b0.nextPc.setLpc
                    (b0.lpc + (flatFL body).length + 5 + 1), P.lfn⟩,
                    v == 0#64⟩ : LstateMF) = _)
                  have hb6 : b0.nextPc.setLpc (b0.lpc + (flatFL body).length + 5 + 1)
                      = b0.setLpc (b0.lpc + (flatFL body).length + 6) := by
                    rw [LstateM.nextPc_setLpc']
                  rw [hb6, hz]
                have hsteps : stepsFB wf (.guarded top endL nReg body) b0 zf = 2 := by
                  rw [stepsFB_guarded]
                  simp only [hv, hz, ite_true]
                intro f
                rw [hsteps, show 2 + f = (1 + f) + 1 from by omega,
                  lsemFuelMemF_step P (1 + f) _ _ _ hfetchCmp hevalCmp,
                  show 1 + f = f + 1 from by omega,
                  lsemFuelMemF_step P f _ _ _ hfetchCond hevalCond]
              · -- NONZERO: `Lcond Z` falls through; label; do-while; `Llabel endL`
                rw [ite_eq_right hz] at hrun
                obtain ⟨bz, hbz, hrfl⟩ := Option.map_eq_some_iff.mp hrun
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hrfl
                have hz' : (v == 0#64) = false := by simpa using hz
                have hevalCond : evalInstrPMemF P
                    (.Lcond (.reg "Z") endL, MemTag.reg none)
                    { prog := { base := b0.nextPc, lfn := P.lfn }, zf := (v == 0#64) }
                      = some { prog :=
                          { base := b0.setLpc (b0.lpc + 2),
                            lfn := P.lfn }, zf := false } := by
                  rw [evalInstrPMemF_je]
                  rw [ite_eq_right (by simp [hz'])]
                  show (some (⟨⟨b0.nextPc.nextPc, P.lfn⟩,
                    v == 0#64⟩ : LstateMF) = _)
                  rw [LstateM.nextPc_nextPc', hz']
                -- the region's own `Llabel top` at head + 2
                have hfetchL : findInstrMem P
                    ({ prog := { base := b0.setLpc (b0.lpc + 2), lfn := P.lfn },
                       zf := false } : LstateMF).prog
                      = some (.Llabel .internal top, MemTag.reg none) := by
                  show findInstrMem P ({ base := b0.setLpc (b0.lpc + 2), lfn := P.lfn }
                    : LstatePM) = _
                  rw [findInstrMemF_self, LstateM.lpc_setLpc]
                  have h2 := hpos 2 (by rw [guardedFlagLoop_length]; omega)
                  rw [h2, guarded_get_shift top endL nReg (flatFL body) 0 (by omega)]
                  rfl
                -- the do-while from the loop top (`tp := b0.lpc + 2`)
                have hn2 := hreg top nReg body (b0.lpc + 2)
                  (b0.setLpc (b0.lpc + 3)) false bz.1 bz.2 hok
                  (by intro k hk
                      have h1 := hpos (3 + k) (by rw [guardedFlagLoop_length]; omega)
                      rw [show b0.lpc + 2 + 1 + k = b0.lpc + (3 + k) from by omega, h1,
                        show 3 + k = 2 + (1 + k) from by omega,
                        guarded_get_shift top endL nReg (flatFL body) (1 + k)
                          (by omega)]
                      exact flagLoop_body_pos top nReg (flatFL body) k hk)
                  (by have h1 := hpos (3 + (flatFL body).length)
                        (by rw [guardedFlagLoop_length]; omega)
                      rw [show b0.lpc + 2 + 1 + (flatFL body).length
                          = b0.lpc + (3 + (flatFL body).length) from by omega, h1,
                        show 3 + (flatFL body).length
                          = 2 + (1 + (flatFL body).length) from by omega,
                        guarded_get_shift top endL nReg (flatFL body)
                          (1 + (flatFL body).length) (by omega)]
                      exact flagLoop_cmp_pos top nReg (flatFL body))
                  (by have h1 := hpos (4 + (flatFL body).length)
                        (by rw [guardedFlagLoop_length]; omega)
                      rw [show b0.lpc + 2 + 2 + (flatFL body).length
                          = b0.lpc + (4 + (flatFL body).length) from by omega, h1,
                        show 4 + (flatFL body).length
                          = 2 + (2 + (flatFL body).length) from by omega,
                        guarded_get_shift top endL nReg (flatFL body)
                          (2 + (flatFL body).length) (by omega)]
                      exact flagLoop_cond_pos top nReg (flatFL body))
                  hlblT
                  (by rw [show b0.lpc + 2 + 1 = b0.lpc + 3 from by omega]
                      exact hresB)
                  (by simp)
                  (by rw [show b0.lpc + 2 + 1 = b0.lpc + 3 from by omega]
                      exact hbz)
                rw [show b0.lpc + 2 + 1 = b0.lpc + 3 from by omega] at hn2
                generalize hn2e : stepsFRegionF wf nReg body (b0.lpc + 3)
                  (b0.setLpc (b0.lpc + 3)) false = n2 at hn2
                have hsteps : stepsFB wf (.guarded top endL nReg body) b0 zf
                    = 2 + 1 + n2 + 1 := by
                  rw [stepsFB_guarded]
                  simp only [hv, hz', Bool.false_eq_true, ite_false, hn2e]
                -- the do-while exits at the `Llabel endL`; step it
                have hbz_lpc : bz.1.lpc = b0.lpc + (flatFL body).length + 5 := by
                  have := runFRegionF_lpc nReg body (b0.lpc + 3) wf _ _ bz.1 bz.2 hbz
                  omega
                have hfetchE : findInstrMem P
                    ({ prog := { base := bz.1, lfn := P.lfn }, zf := bz.2 }
                      : LstateMF).prog
                      = some (.Llabel .internal endL, MemTag.reg none) := by
                  show findInstrMem P ({ base := bz.1, lfn := P.lfn }
                    : LstatePM) = _
                  rw [findInstrMemF_self, hbz_lpc]
                  have h1 := hpos ((flatFL body).length + 5)
                    (by rw [guardedFlagLoop_length]; omega)
                  rw [show b0.lpc + (flatFL body).length + 5
                      = b0.lpc + ((flatFL body).length + 5) from by omega, h1]
                  exact guarded_get_endL top endL nReg (flatFL body)
                intro f
                rw [hsteps, show 2 + 1 + n2 + 1 + f = ((1 + (1 + (n2 + (f + 1)))) + 1)
                    from by omega,
                  lsemFuelMemF_step P _ _ _ _ hfetchCmp hevalCmp,
                  show 1 + (1 + (n2 + (f + 1))) = (1 + (n2 + (f + 1))) + 1
                    from by omega,
                  lsemFuelMemF_step P _ _ _ _ hfetchCond hevalCond,
                  show 1 + (n2 + (f + 1)) = (n2 + (f + 1)) + 1 from by omega,
                  lsemFuelMemF_step P _ _ _ _ hfetchL
                    (evalInstrPMemF_label P .internal top (MemTag.reg none) _)]
                have hstep3 : ({ prog :=
                      { base := b0.setLpc (b0.lpc + 2),
                        lfn := P.lfn }, zf := false } : LstateMF).prog.base.nextPc
                      = b0.setLpc (b0.lpc + 3) := LstateM.setLpc_nextPc' b0 _
                rw [hstep3]
                rw [hn2 (f + 1)]
                rw [lsemFuelMemF_step P f _ _ _ hfetchE
                  (evalInstrPMemF_label P .internal endL (MemTag.reg none) _)]
                have hstepE : ({ prog := { base := bz.1, lfn := P.lfn }, zf := bz.2 }
                    : LstateMF).prog.base.nextPc
                      = bz.1.setLpc (b0.lpc + (flatFL body).length + 6) := by
                  rw [LstateM.nextPc_eq_setLpc, hbz_lpc]
                rw [hstepE]
    -- ── the block-list lemma at `wf` (inner list induction) ──
    refine ⟨hreg, ?_⟩
    intro blks
    induction blks with
    | nil =>
        intro b0 zf b zb _ _ _ hrun
        rw [runFBsL_nil] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrun
        intro f
        rw [stepsFBsL_nil, Nat.zero_add]
    | cons blk rest ihrest =>
        intro b0 zf b zb hok hpos hres hrun
        rw [runFBsL_cons] at hrun
        rw [FBlocksOK_cons] at hok
        rw [FBlocksResolve_cons] at hres
        obtain ⟨hokB, hokR⟩ := hok
        obtain ⟨hresB, hresR⟩ := hres
        cases hb1 : runFB wf blk b0 zf with
        | none => rw [hb1] at hrun; simp at hrun
        | some bz =>
            rw [hb1, Option.bind_some] at hrun
            have hposHead : ∀ k, k < blk.flat.length →
                P.body[b0.lpc + k]? = blk.flat[k]? := by
              intro k hk
              have h1 := hpos k (by rw [fflatFL_cons, List.length_append]; omega)
              rw [h1, fflatFL_cons, List.getElem?_append_left hk]
            have hn1 := hblk blk b0 zf bz.1 bz.2 hokB hposHead hresB
              (by rw [hb1])
            have hbz_lpc := runFB_lpc wf blk b0 zf bz.1 bz.2 (by rw [hb1])
            have hposRest : ∀ k, k < (flatFL rest).length →
                P.body[bz.1.lpc + k]? = (flatFL rest)[k]? := by
              intro k hk
              have h1 := hpos (blk.flat.length + k)
                (by rw [fflatFL_cons, List.length_append]; omega)
              rw [hbz_lpc, show b0.lpc + blk.flat.length + k
                  = b0.lpc + (blk.flat.length + k) from by omega, h1, fflatFL_cons,
                List.getElem?_append_right (by omega)]
              congr 1
              omega
            have hresRest : FBlocksResolve P rest bz.1.lpc := by
              rw [hbz_lpc]
              exact hresR
            have hn2 := ihrest bz.1 bz.2 b zb hokR hposRest hresRest hrun
            intro f
            rw [stepsFBsL_cons, hb1]
            simp only []
            rw [Nat.add_assoc, hn1 (stepsFBsL wf rest bz.1 bz.2 + f)]
            exact hn2 f

/-- **The segment lemma over the flag machine, with its fuel** (`segFBlocks_fuel`).  If
    the flattened flag-block segment occupies its positions in the program body,
    every region label (and skip label) resolves to its own position, and the
    spec fold terminates within back-edge budget `wf`, then `lsemFuelMemF`
    consumes the fuel `stepsFBsL wf blks b0 zf` and continues from the fold's
    out-state — each complete region (bare or zero-trip-guarded) acts as one
    composite step whose effect is the region do-while. -/
theorem segFBlocks_fuel (P : LprogM) (wf : Nat) (blks : List FBlock)
    (b0 : LstateM) (zf : Bool) (b : LstateM) (zb : Bool)
    (hok : FBlocksOK blks)
    (hpos : ∀ k, k < (flatFL blks).length → P.body[b0.lpc + k]? = (flatFL blks)[k]?)
    (hres : FBlocksResolve P blks b0.lpc)
    (hrun : runFBsL wf blks b0 zf = some (b, zb)) :
    ∀ f,
      lsemFuelMemF P (stepsFBsL wf blks b0 zf + f)
          { prog := { base := b0, lfn := P.lfn }, zf := zf }
        = lsemFuelMemF P f { prog := { base := b, lfn := P.lfn }, zf := zb } :=
  (segFCore P wf).2 blks b0 zf b zb hok hpos hres hrun

/-- **The segment lemma over the flag machine** (`segFBlocks`): `segFBlocks_fuel` with
    the fuel existentially quantified. -/
theorem segFBlocks (P : LprogM) (wf : Nat) (blks : List FBlock)
    (b0 : LstateM) (zf : Bool) (b : LstateM) (zb : Bool)
    (hok : FBlocksOK blks)
    (hpos : ∀ k, k < (flatFL blks).length → P.body[b0.lpc + k]? = (flatFL blks)[k]?)
    (hres : FBlocksResolve P blks b0.lpc)
    (hrun : runFBsL wf blks b0 zf = some (b, zb)) :
    ∃ n, ∀ f,
      lsemFuelMemF P (n + f) { prog := { base := b0, lfn := P.lfn }, zf := zf }
        = lsemFuelMemF P f { prog := { base := b, lfn := P.lfn }, zf := zb } :=
  ⟨_, segFBlocks_fuel P wf blks b0 zf b zb hok hpos hres hrun⟩

/-! ## 7. The closed inline-nest theorem on the flag machine -/

/-- **The flag-machine inline-nest closed theorem.**  For the singleton program
    whose body IS the flattened flag-block list (the emitted nest — regions in
    regions to any depth, with data-dependent per-level trip counts and the
    emitted `CMP`/`Jcc` guards), the machine run from pc `0` halts on exactly
    the spec fold's out-state (flag included), at every fuel from the fold's
    step count `stepsFBsL wf blks b0 zf` on. -/
theorem flagNest_closed_fuel (fn : String) (blks : List FBlock) (wf : Nat)
    (b0 : LstateM) (zf : Bool) (b : LstateM) (zb : Bool)
    (hpc : b0.lpc = 0)
    (hok : FBlocksOK blks)
    (hres : FBlocksResolve (singletonProgM fn (flatFL blks)) blks 0)
    (hrun : runFBsL wf blks b0 zf = some (b, zb)) :
    ∀ k, stepsFBsL wf blks b0 zf ≤ k →
      lsemFuelMemF (singletonProgM fn (flatFL blks)) k
          { prog := { base := b0, lfn := fn }, zf := zf }
        = some { prog := { base := b, lfn := fn }, zf := zb } := by
  intro k hk
  set P := singletonProgM fn (flatFL blks) with hP
  have hfn : fn = P.lfn := rfl
  have hpos : ∀ k, k < (flatFL blks).length →
      P.body[b0.lpc + k]? = (flatFL blks)[k]? := by
    intro k hk
    rw [hpc, Nat.zero_add]
    rfl
  have hn := segFBlocks_fuel P wf blks b0 zf b zb hok hpos
    (by rw [hpc]; exact hres) hrun
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h0 := hn f
  rw [show ({ prog := { base := b0, lfn := fn }, zf := zf } : LstateMF)
    = { prog := { base := b0, lfn := P.lfn }, zf := zf } from rfl, h0]
  apply lsemFuelMemF_halt
  show findInstrMem P ({ base := b, lfn := P.lfn } : LstatePM) = none
  rw [findInstrMemF_self]
  have hb := runFBsL_lpc blks wf b0 zf b zb hrun
  rw [hpc, Nat.zero_add] at hb
  rw [hb]
  exact List.getElem?_eq_none (le_refl _)

/-- `flagNest_closed_fuel` with the fuel existentially quantified. -/
theorem flagNest_closed (fn : String) (blks : List FBlock) (wf : Nat)
    (b0 : LstateM) (zf : Bool) (b : LstateM) (zb : Bool)
    (hpc : b0.lpc = 0)
    (hok : FBlocksOK blks)
    (hres : FBlocksResolve (singletonProgM fn (flatFL blks)) blks 0)
    (hrun : runFBsL wf blks b0 zf = some (b, zb)) :
    ∃ n, lsemFuelMemF (singletonProgM fn (flatFL blks)) n
        { prog := { base := b0, lfn := fn }, zf := zf }
      = some { prog := { base := b, lfn := fn }, zf := zb } :=
  ⟨_, flagNest_closed_fuel fn blks wf b0 zf b zb hpc hok hres hrun _ (Nat.le_refl _)⟩

/-! ## 8. The zero-trip region arm (the `Lcond Z endL` forward skip) -/

/-- The counter read ignores the pc. -/
@[simp] theorem getW_setLpc (s : LstateM) (pc : Nat) (r : String) (w : Nat) :
    (s.setLpc pc).reg.getW r w = s.reg.getW r w := rfl

/-- **Zero-trip region arm (fold).**  A guarded region entered with a ZERO
    counter is the `m = 0` fold: the whole region is skipped, the register
    store and array carrier untouched (only the pc moves past the region), the
    flag set by the guard compare. -/
theorem runFB_guarded_zeroTrip (wf : Nat) (top endL : LLabel) (nReg : String)
    (body : List FBlock) (s : LstateM) (zf : Bool)
    (hzero : s.reg.getW nReg 64 = some 0#64) :
    runFB wf (.guarded top endL nReg body) s zf
      = some (s.setLpc (s.lpc + (flatFL body).length + 6), true) := by
  rw [runFB_guarded, hzero]
  simp

/-- **Zero-trip region arm (machine).**  The singleton guarded-region program
    run from its head with a zero counter halts with the register store and
    the array carrier exactly the entry's — no body instruction executed. -/
theorem guardedRegion_zeroTrip_machine (fn : String) (top endL : LLabel)
    (nReg : String) (body : List FBlock) (b0 : LstateM) (zf : Bool)
    (hpc : b0.lpc = 0)
    (hok : FBlocksOK [FBlock.guarded top endL nReg body])
    (hres : FBlocksResolve
      (singletonProgM fn (flatFL [FBlock.guarded top endL nReg body]))
      [FBlock.guarded top endL nReg body] 0)
    (hzero : b0.reg.getW nReg 64 = some 0#64) :
    ∃ (n : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn (flatFL [FBlock.guarded top endL nReg body])) n
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ t.prog.base.reg.lvm = b0.reg.lvm ∧ t.prog.base.larr = b0.larr
        ∧ t.zf = true := by
  have hrun : runFBsL 1 [FBlock.guarded top endL nReg body] b0 zf
      = some (b0.setLpc (b0.lpc + (flatFL body).length + 6), true) := by
    rw [runFBsL_cons, runFB_guarded_zeroTrip 1 top endL nReg body b0 zf hzero,
      Option.bind_some, runFBsL_nil]
  obtain ⟨n, hn⟩ := flagNest_closed fn _ 1 b0 zf _ _ hpc hok hres hrun
  exact ⟨n, _, hn, rfl, rfl, rfl⟩

/-! ## 9. Fuel monotonicity and the bounded fold -/

/-- **Fuel monotonicity**: a fold that terminates within back-edge budget `wf`
    gives the same result at budget `wf + 1`. -/
theorem monoFCore :
    ∀ wf : Nat,
      (∀ (blks : List FBlock) (s : LstateM) (zf : Bool) (bz : LstateM × Bool),
          runFBsL wf blks s zf = some bz → runFBsL (wf + 1) blks s zf = some bz) ∧
      (∀ (nReg : String) (body : List FBlock) (q : Nat) (s : LstateM) (zf : Bool)
          (bz : LstateM × Bool),
          runFRegionF wf nReg body q s zf = some bz →
            runFRegionF (wf + 1) nReg body q s zf = some bz) := by
  intro wf
  induction wf using Nat.strongRecOn with
  | ind wf ih =>
    have hreg : ∀ (nReg : String) (body : List FBlock) (q : Nat) (s : LstateM)
        (zf : Bool) (bz : LstateM × Bool),
        runFRegionF wf nReg body q s zf = some bz →
          runFRegionF (wf + 1) nReg body q s zf = some bz := by
      cases wf with
      | zero =>
          intro _ _ _ _ _ _ h
          rw [runFRegionF_zero] at h
          exact absurd h (by simp)
      | succ w =>
          intro nReg body q s zf bz h
          rw [runFRegionF_succ] at h
          rw [runFRegionF_succ]
          cases h1 : runFBsL w body s zf with
          | none => rw [h1] at h; simp at h
          | some b1 =>
              rw [h1, Option.bind_some] at h
              rw [(ih w (Nat.lt_succ_self w)).1 body s zf b1 h1, Option.bind_some]
              cases hv : b1.1.reg.getW nReg 64 with
              | none => rw [hv] at h; simp at h
              | some v =>
                  rw [hv] at h
                  simp only [] at h ⊢
                  by_cases hz : (v == 0#64) = true
                  · rw [ite_eq_left hz] at h ⊢
                    exact h
                  · rw [ite_eq_right hz] at h ⊢
                    exact (ih w (Nat.lt_succ_self w)).2 nReg body q _ false bz h
    have hblk : ∀ (blk : FBlock) (s : LstateM) (zf : Bool) (bz : LstateM × Bool),
        runFB wf blk s zf = some bz → runFB (wf + 1) blk s zf = some bz := by
      intro blk s zf bz h
      cases blk with
      | straight seg => rw [runFB_straight] at h ⊢; exact h
      | region top nReg body =>
          rw [runFB_region] at h ⊢
          exact hreg nReg body (s.lpc + 1) _ zf bz h
      | guarded top endL nReg body =>
          rw [runFB_guarded] at h ⊢
          cases hv : s.reg.getW nReg 64 with
          | none => rw [hv] at h; simp at h
          | some v =>
              rw [hv] at h
              simp only [] at h ⊢
              by_cases hz : (v == 0#64) = true
              · rw [ite_eq_left hz] at h ⊢
                exact h
              · rw [ite_eq_right hz] at h ⊢
                obtain ⟨bz0, hbz0, hrfl⟩ := Option.map_eq_some_iff.mp h
                rw [hreg nReg body (s.lpc + 3) _ false bz0 hbz0, Option.map_some,
                  hrfl]
    refine ⟨?_, hreg⟩
    intro blks
    induction blks with
    | nil => intro s zf bz h; rwa [runFBsL_nil] at h ⊢
    | cons blk rest ihr =>
        intro s zf bz h
        rw [runFBsL_cons] at h ⊢
        cases h1 : runFB wf blk s zf with
        | none => rw [h1] at h; simp at h
        | some b1 =>
            rw [h1, Option.bind_some] at h
            rw [hblk blk s zf b1 h1, Option.bind_some]
            exact ihr b1.1 b1.2 bz h

/-- Block-list fuel monotonicity, lifted to any budget increase. -/
theorem runFBsL_mono_add (wf : Nat) (blks : List FBlock) (s : LstateM) (zf : Bool)
    (bz : LstateM × Bool) (h : runFBsL wf blks s zf = some bz) :
    ∀ j, runFBsL (wf + j) blks s zf = some bz := by
  intro j
  induction j with
  | zero => simpa using h
  | succ n ihn =>
      rw [show wf + (n + 1) = (wf + n) + 1 from by omega]
      exact (monoFCore (wf + n)).1 blks s zf bz ihn

/-- The fixed-trip bounded fold of a region body: `m` passes of the block-list
    fold (each entered with the flag CLEAR — the just-run guard/back-edge `CMP`
    saw non-zero), pc reset to the loop top `q` after each pass. -/
def runBoundedFBs (wf : Nat) (body : List FBlock) (q : Nat) :
    Nat → LstateM → Option LstateM
  | 0, s => some s
  | k + 1, s =>
      (runFBsL wf body s false).bind
        (fun bz => runBoundedFBs wf body q k (bz.1.setLpc q))

@[simp] theorem runBoundedFBs_zero (wf : Nat) (body : List FBlock) (q : Nat)
    (s : LstateM) : runBoundedFBs wf body q 0 s = some s := rfl

@[simp] theorem runBoundedFBs_succ (wf : Nat) (body : List FBlock) (q : Nat)
    (k : Nat) (s : LstateM) :
    runBoundedFBs wf body q (k + 1) s
      = (runFBsL wf body s false).bind
          (fun bz => runBoundedFBs wf body q k (bz.1.setLpc q)) := rfl

/-! ## 10. The schedule direction and the OFFSET-GENERAL guarded theorem

`runFRegionF_of_schedule` builds the region do-while FROM the bounded fold and
its counter schedule (the converse of a reconstruction); composed with
`flagNest_closed` at a single guarded region over a straight body it yields the
general theorem for the full `forLoopLcmdNRt` skeleton — guard at pc 0–1, loop
at pc-offset 2 — at a NONZERO runtime count, which `JasminLsemMemFlagGuard` validates only
concretely. -/

/-- **Schedule → do-while.**  If the bounded `m`-fold of the region body runs
    (`m ≥ 1`), the counter is non-zero after each of the first `m - 1` passes,
    and it reads ZERO after the `m`-th, then the region do-while terminates at
    budget `wf + m` on exactly the fold's out-state (exit pc, flag set). -/
theorem runFRegionF_of_schedule (nReg : String) (body : List FBlock) (q wf : Nat) :
    ∀ (m : Nat) (s : LstateM), 0 < m →
      ∀ bfin : LstateM,
        runBoundedFBs wf body q m s = some bfin →
        (∀ i, 0 < i → i < m → ∀ bi, runBoundedFBs wf body q i s = some bi →
          condNZ bi (.reg nReg) = true) →
        bfin.reg.getW nReg 64 = some 0#64 →
        runFRegionF (wf + m) nReg body q s false
          = some (bfin.setLpc (q + (flatFL body).length + 2), true) := by
  intro m
  induction m with
  | zero => intro s h; omega
  | succ k ihm =>
      intro s _ bfin hbound hsched hzero
      rw [runBoundedFBs_succ] at hbound
      cases h1 : runFBsL wf body s false with
      | none => rw [h1] at hbound; simp at hbound
      | some bz =>
          rw [h1, Option.bind_some] at hbound
          rw [show wf + (k + 1) = (wf + k) + 1 from by omega, runFRegionF_succ,
            runFBsL_mono_add wf body s false bz h1 k, Option.bind_some]
          cases k with
          | zero =>
              rw [runBoundedFBs_zero] at hbound
              obtain rfl := Option.some.inj hbound
              have hz0 : bz.1.reg.getW nReg 64 = some 0#64 := by
                simpa using hzero
              rw [hz0]
              simp
          | succ k' =>
              have hc1 : condNZ (bz.1.setLpc q) (.reg nReg) = true := by
                apply hsched 1 (by omega) (by omega)
                rw [runBoundedFBs_succ, h1, Option.bind_some, runBoundedFBs_zero]
              rw [condNZ_setLpc] at hc1
              obtain ⟨v, hvread, hvne⟩ := condNZ_true_getW hc1
              rw [hvread]
              simp only []
              rw [ite_eq_right (by simp [hvne])]
              exact ihm (bz.1.setLpc q) (by omega) bfin hbound
                (fun i hi him bi hbi => hsched (i + 1) (by omega) (by omega) bi
                  (by rw [runBoundedFBs_succ, h1, Option.bind_some]; exact hbi))
                hzero

/-- The bounded fold of a STRAIGHT body: `m` passes of the extended straight
    fold `runStraightF` (each entered flag-clear), pc reset to `q` per pass —
    the `runBoundedLoopMem` analogue over the `Lopn ∪ MOV ∪ CMP` step. -/
def runBoundedStraightF (body : List LinstrRM) (q : Nat) :
    Nat → LstateM → Option LstateM
  | 0, s => some s
  | k + 1, s =>
      (runStraightF body s false).bind
        (fun bz => runBoundedStraightF body q k (bz.1.setLpc q))

@[simp] theorem runBoundedStraightF_zero (body : List LinstrRM) (q : Nat)
    (s : LstateM) : runBoundedStraightF body q 0 s = some s := rfl

@[simp] theorem runBoundedStraightF_succ (body : List LinstrRM) (q : Nat) (k : Nat)
    (s : LstateM) :
    runBoundedStraightF body q (k + 1) s
      = (runStraightF body s false).bind
          (fun bz => runBoundedStraightF body q k (bz.1.setLpc q)) := rfl

/-- The block-list fold of a single straight block is the straight fold. -/
theorem runFBsL_straight (wf : Nat) (body : List LinstrRM) (s : LstateM) (zf : Bool) :
    runFBsL wf [FBlock.straight body] s zf = runStraightF body s zf := by
  rw [runFBsL_cons, runFB_straight]
  cases runStraightF body s zf with
  | none => rfl
  | some bz => rw [Option.bind_some, runFBsL_nil]

/-- The bounded fold of a single straight block is the straight bounded fold
    (budget-independent). -/
theorem runBoundedFBs_straight (wf : Nat) (body : List LinstrRM) (q : Nat) :
    ∀ (k : Nat) (s : LstateM),
      runBoundedFBs wf [FBlock.straight body] q k s
        = runBoundedStraightF body q k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ n ihn =>
      intro s
      rw [runBoundedFBs_succ, runBoundedStraightF_succ, runFBsL_straight]
      cases runStraightF body s false with
      | none => rfl
      | some bz => rw [Option.bind_some, Option.bind_some]; exact ihn _

/-- The guarded shape's own `top` label is at index 2 (behind the two guard
    instructions). -/
theorem findLabelMem_guarded_top (top endL : LLabel) (nReg : String)
    (body : List LinstrRM) :
    findLabelMem top (guardedFlagLoopLinstrRM top endL nReg body) = some 2 := by
  unfold findLabelMem guardedFlagLoopLinstrRM flagLoopLinstrRM
    JasminLsemLabeled.findLabel
  simp only [List.map_append, List.map_cons, List.cons_append, List.findIdx?_cons]
  rw [show JasminLsemLabeled.isLabel top (.Lopn [.reg nReg] (withWidthTag 64 "CMP")
      [.reg nReg, .imm 0]) = false from rfl]
  rw [show JasminLsemLabeled.isLabel top (.Lcond (.reg "Z") endL) = false from rfl]
  rw [show JasminLsemLabeled.isLabel top (.Llabel .internal top) = true from by
    simp [JasminLsemLabeled.isLabel]]
  rfl

/-- **The OFFSET-GENERAL guarded single-loop theorem.**  The full
    `forLoopLcmdNRt` loop skeleton — zero-trip guard at pc 0–1, `Llabel top` at
    pc 2, body at pc-offset 3, back-edge + skip label behind (pin:
    `forLoopLcmdNRt_guard` / `forLoopLcmdNRt_backedge`) — run as a singleton
    program from pc 0 with a NONZERO runtime count:

    the guard `CMP` reads the counter (`some v0`, `v0 ≠ 0`), the
    `Lcond Z` falls through, and given the counter schedule over the extended
    bounded fold `runBoundedStraightF body 3` **at the shifted base** (pc 3 —
    the loop top of the guarded shape), the machine halts past the skip label
    in a state agreeing with the fold on the register store and the array
    carrier, with `zf = true`.  The per-pass fold is `runStraightF`, so the
    body may contain the feedback reg-copy `MOV` and the invariant-touch
    `CMP ctr,invBase` (the two emitted forms `flagLoop_runBounded`, whose
    fold is `lsemStraightMemF`, cannot step) — `JasminLsemMemFlagGuard` validates
    this shape only concretely (`rtLoopRM`). -/
theorem guardedFlagLoop_runBounded_general (fn : String) (top endL : LLabel)
    (nReg : String) (body : List LinstrRM)
    (hlopn : ∀ i ∈ body, IsLopn i) (hne : top ≠ endL)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (v0 : BitVec 64) (hv0 : b0.reg.getW nReg 64 = some v0)
    (hv0ne : (v0 == 0#64) = false)
    (m : Nat) (hm : 0 < m) (bfin : LstateM)
    (hbound : runBoundedStraightF body 3 m (b0.setLpc 3) = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedStraightF body 3 i (b0.setLpc 3) = some bi →
      condNZ bi (.reg nReg) = true)
    (hzero : bfin.reg.getW nReg 64 = some 0#64) :
    ∃ (n : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn (guardedFlagLoopLinstrRM top endL nReg body)) n
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ t.prog.base.reg.lvm = bfin.reg.lvm ∧ t.prog.base.larr = bfin.larr
        ∧ t.zf = true := by
  have hfb : flatFL [FBlock.straight body] = body := by simp
  have hgg : flatFL [FBlock.guarded top endL nReg [FBlock.straight body]]
      = guardedFlagLoopLinstrRM top endL nReg body := by
    simp
  -- the do-while from the schedule (budget `m`)
  have hsched := runFRegionF_of_schedule nReg [FBlock.straight body] 3 0 m
    (b0.setLpc 3) hm bfin
    (by rw [runBoundedFBs_straight]; exact hbound)
    (fun i hi him bi hbi => htaken i hi him bi
      (by rwa [runBoundedFBs_straight] at hbi))
    hzero
  rw [Nat.zero_add, hfb] at hsched
  -- the guarded region block from its head
  have hrunFB : runFB m (.guarded top endL nReg [FBlock.straight body]) b0 zf
      = some (bfin.setLpc (body.length + 6), true) := by
    rw [runFB_guarded, hv0]
    simp only []
    rw [ite_eq_right (by simp [hv0ne])]
    rw [hpc, hfb]
    simp only [Nat.zero_add]
    rw [hsched]
    simp only [Option.map_some, LstateM.setLpc_setLpc]
  have hrunL : runFBsL m [FBlock.guarded top endL nReg [FBlock.straight body]] b0 zf
      = some (bfin.setLpc (body.length + 6), true) := by
    rw [runFBsL_cons, hrunFB, Option.bind_some, runFBsL_nil]
  -- well-formedness + resolution of the singleton guarded program
  have hok : FBlocksOK [FBlock.guarded top endL nReg [FBlock.straight body]] := by
    simp only [FBlocksOK_cons, FBlocksOK_nil, FBlockOK_guarded, FBlockOK_straight,
      and_true]
    exact hlopn
  have hPbody : (singletonProgM fn
      (flatFL [FBlock.guarded top endL nReg [FBlock.straight body]])).body
        = guardedFlagLoopLinstrRM top endL nReg body := hgg
  have hres : FBlocksResolve
      (singletonProgM fn (flatFL [FBlock.guarded top endL nReg [FBlock.straight body]]))
      [FBlock.guarded top endL nReg [FBlock.straight body]] 0 := by
    simp only [FBlocksResolve_cons, FBlocksResolve_nil, FBlockResolves_guarded,
      FBlockResolves_straight, and_true, hfb, Nat.zero_add]
    rw [hPbody]
    exact ⟨findLabelMem_guarded_top top endL nReg body,
      findLabelMem_guarded_endL top endL nReg body hlopn hne⟩
  obtain ⟨n, hn⟩ := flagNest_closed fn
    [FBlock.guarded top endL nReg [FBlock.straight body]] m b0 zf _ _ hpc hok hres hrunL
  rw [hgg] at hn
  exact ⟨n, _, hn, rfl, rfl, rfl⟩

/-! ## 11. Validate: the REAL rendered `forLoopLcmdNRtNested` stream through the
closed theorem

`nestSmokeProg` is a small `ComL.forLoopNRtNested` — outer runtime count `D`
(arg 2), accumulator seed (arg 1), runtime invariant `num` (arg 0); the inner
trip is recomputed per outer pass as `num >>> (jd + 1)` and the innermost body
is `acc := acc + 2` — the GGM Phase-3 shape, so the denotation is
`ggmNestedFold D num 2` at seed `0`.  `nestSmokeBody` is its ACTUAL
`comLToBody` rendering (the real nested `CMP`/flag stream: reg-copy
seed/feedback `MOV`s, two zero-trip guards, two flag back-edges, and the
invariant-touch `CMP Lctr3,a0` — `invOps = [num]` is a register, so the
lowering emits the touch).  The machine value is derived through
`flagNest_closed`; `native_decide` evaluates only the SPEC fold. -/

/-- Inner-count body `num >>> (jd + 1)` over the context `[jd, num]`. -/
def nestCntCom : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64]
    (JasminTy.reg 64) :=
  .var (.mk (.regConst 64 1) rfl .nil)
    (.var (.mk (.regArith .add 64) rfl (.cons (.there .here) (.cons .here .nil)))
      (.var (.mk (.regArith .shr 64) rfl
          (.cons (.there (.there (.there .here))) (.cons .here .nil)))
        (.ret .here)))

/-- Innermost body `acc + 2` over the context `[acc, t, jd, num]`. -/
def nestUpdCom : Com jasminDialect
    [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64]
    (JasminTy.reg 64) :=
  .var (.mk (.regConst 64 2) rfl .nil)
    (.var (.mk (.regArith .add 64) rfl (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- The nested runtime loop: args (newest-first) `[D, seed, num]`; outer count
    `D`, accumulator seed `seed`, invariant `num`. -/
def nestSmokeProg : ComL [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64]
    (JasminTy.reg 64) :=
  .forLoopNRtNested nestCntCom nestUpdCom .here (.there .here)
    (.cons (.there (.there .here)) .nil) (.ret .here)

/-- The ACTUAL rendered lowering (top-level, `nArgs = 3`, outer depth 3 —
    labels `3`/`4`, counters `Lctr3`/`Lctr4`, accumulator `r3`). -/
def nestSmokeBody : Lcmd := comLToBody 3 argName (fun _ => none) nestSmokeProg 3

/-- The rendered stream lifted to the typed instruction list (register
    bindings only in this kernel), the trailing `Lret` dropped (function
    return is outside the loop idiom; program-end is the halt). -/
def nestRM : List LinstrRM :=
  (nestSmokeBody.map (fun i => (i.li_i, MemTag.reg none))).dropLast

/-- The rendered nested loop as a singleton program. -/
def nestProg : LprogM := singletonProgM "f" nestRM

/-! ### Decidable checkers for the closed theorem's side conditions -/

deriving instance DecidableEq for LinstrR

/-- Boolean `Lopn` recognizer (for `native_decide`-discharged side conditions). -/
def isLopnB (i : LinstrRM) : Bool :=
  match i.fst with
  | .Lopn _ _ _ => true
  | _ => false

/-- The Boolean recognizer is sound for `IsLopn`. -/
theorem isLopnB_isLopn {i : LinstrRM} (h : isLopnB i = true) : IsLopn i := by
  unfold isLopnB at h
  split at h
  · next d o srcs heq => exact ⟨d, o, srcs, heq⟩
  · exact absurd h (by simp)

mutual
/-- Boolean well-formedness checker. -/
def fblockOKb : FBlock → Bool
  | .straight seg => seg.all isLopnB
  | .region _ _ body => fblocksOKb body
  | .guarded _ _ _ body => fblocksOKb body
/-- Boolean list well-formedness checker. -/
def fblocksOKb : List FBlock → Bool
  | [] => true
  | b :: rest => fblockOKb b && fblocksOKb rest
end

mutual
/-- The Boolean checker is sound for `FBlockOK`. -/
theorem fblockOKb_sound : ∀ b : FBlock, fblockOKb b = true → FBlockOK b
  | .straight seg, h => by
      rw [FBlockOK_straight]
      intro i hi
      rw [fblockOKb] at h
      exact isLopnB_isLopn (List.all_eq_true.mp h i hi)
  | .region t n body, h => by
      rw [FBlockOK_region]
      rw [fblockOKb] at h
      exact fblocksOKb_sound body h
  | .guarded t e n body, h => by
      rw [FBlockOK_guarded]
      rw [fblockOKb] at h
      exact fblocksOKb_sound body h
/-- The Boolean list checker is sound for `FBlocksOK`. -/
theorem fblocksOKb_sound : ∀ bs : List FBlock, fblocksOKb bs = true → FBlocksOK bs
  | [], _ => by rw [FBlocksOK_nil]; trivial
  | b :: rest, h => by
      rw [FBlocksOK_cons]
      rw [fblocksOKb] at h
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      exact ⟨fblockOKb_sound b h1, fblocksOKb_sound rest h2⟩
end

mutual
/-- Boolean label-resolution checker. -/
def fblockResB (P : LprogM) : FBlock → Nat → Bool
  | .straight _, _ => true
  | .region top _ body, p =>
      (findLabelMem top P.body == some p) && fblocksResB P body (p + 1)
  | .guarded top endL _ body, p =>
      (findLabelMem top P.body == some (p + 2))
        && (findLabelMem endL P.body == some (p + (flatFL body).length + 5))
        && fblocksResB P body (p + 3)
/-- Boolean list label-resolution checker. -/
def fblocksResB (P : LprogM) : List FBlock → Nat → Bool
  | [], _ => true
  | b :: rest, p => fblockResB P b p && fblocksResB P rest (p + b.flat.length)
end

mutual
/-- The Boolean resolution checker is sound for `FBlockResolves`. -/
theorem fblockResB_sound (P : LprogM) :
    ∀ (b : FBlock) (p : Nat), fblockResB P b p = true → FBlockResolves P b p
  | .straight seg, p, _ => by rw [FBlockResolves_straight]; trivial
  | .region t n body, p, h => by
      rw [FBlockResolves_region]
      rw [fblockResB] at h
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      exact ⟨beq_iff_eq.mp h1, fblocksResB_sound P body (p + 1) h2⟩
  | .guarded t e n body, p, h => by
      rw [FBlockResolves_guarded]
      rw [fblockResB] at h
      obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
      exact ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2,
        fblocksResB_sound P body (p + 3) h3⟩
/-- The Boolean list resolution checker is sound for `FBlocksResolve`. -/
theorem fblocksResB_sound (P : LprogM) :
    ∀ (bs : List FBlock) (p : Nat), fblocksResB P bs p = true → FBlocksResolve P bs p
  | [], p, _ => by rw [FBlocksResolve_nil]; trivial
  | b :: rest, p, h => by
      rw [FBlocksResolve_cons]
      rw [fblocksResB] at h
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      exact ⟨fblockResB_sound P b p h1,
        fblocksResB_sound P rest (p + b.flat.length) h2⟩
end

/-! ### The rendered stream as a flag block tree -/

/-- `nestRM` as an `FBlock` tree: the three seed `MOV`s, then the guarded
    outer region (label `3`, counter `Lctr3`) containing the inner-count
    recompute + inner seeds, the guarded inner region (label `4`, counter
    `Lctr4`) over the innermost body + feedback + advance, and the outer
    advance + invariant-touch `CMP Lctr3,a0`. -/
def nestBlks : List FBlock :=
  [ .straight (nestRM.take 3)
  , .guarded 3 (3 + 0x40000000) "Lctr3"
      [ .straight ((nestRM.drop 6).take 5)
      , .guarded 4 (4 + 0x40000000) "Lctr4"
          [ .straight ((nestRM.drop 14).take 5) ]
      , .straight ((nestRM.drop 22).take 3) ] ]

/-- **The block tree flattens to EXACTLY the rendered stream** — the closed
    theorem below therefore speaks about the actual `comLToBody` rendering of
    `ComL.forLoopNRtNested`, not an imitation. -/
theorem nestBlks_flat : flatFL nestBlks = nestRM := by native_decide

/-- The singleton program over the flattened tree IS the rendered program. -/
theorem nestBlks_prog : singletonProgM "f" (flatFL nestBlks) = nestProg := by
  rw [nestBlks_flat]
  rfl

/-- Entry state: `a2 = D` (outer count), `a1 = seed`, `a0 = num`, pc 0. -/
def nestStart (D seed num : Nat) : LstateM :=
  ((({} : LstateM).setReg "a0" (BitVec.ofNat 64 num)).setReg "a1"
      (BitVec.ofNat 64 seed)).setReg "a2" (BitVec.ofNat 64 D)

/-! ### The SPEC-fold gates (`native_decide` evaluates only the fold) -/

/-- The spec fold decodes the accumulator to the SOURCE denotation
    (`D = 3`, seed `0`, `num = 8`). -/
theorem nest_fold_denote_8 :
    (runFBsL 64 nestBlks (nestStart 3 0 8) false).map (fun bz => decodeM bz.1 "r3" 64)
      = some (some (ComL.denote nestSmokeProg
          (.cons (BitVec.ofNat 64 3)
            (.cons (BitVec.ofNat 64 0) (.cons (BitVec.ofNat 64 8) .nil))))) := by
  native_decide

/-- The spec fold decodes to the GGM nested fold (`= 14`): outer 3, inner
    trips `8>>1, 8>>2, 8>>3 = 4, 2, 1`, `+2` innermost. -/
theorem nest_fold_ggm_8 :
    (runFBsL 64 nestBlks (nestStart 3 0 8) false).map (fun bz => decodeM bz.1 "r3" 64)
      = some (some (BitVec.ofNat 64 (ggmNestedFold 3 8 2))) := by native_decide

/-- Recompute sensitivity: at `num = 16` the same program folds to
    `ggmNestedFold 3 16 2 = 28` — the inner trip is read from the `a0`
    register each outer pass, not baked in. -/
theorem nest_fold_denote_16 :
    (runFBsL 64 nestBlks (nestStart 3 0 16) false).map (fun bz => decodeM bz.1 "r3" 64)
      = some (some (BitVec.ofNat 64 (ggmNestedFold 3 16 2)))
      ∧ ggmNestedFold 3 8 2 = 14 ∧ ggmNestedFold 3 16 2 = 28 := by native_decide

/-- Outer zero-trip (`D = 0`): the fold is the seed — the outer `Lcond Z`
    skips the whole nest (`= ComL.denote` at outer count `0`). -/
theorem nest_fold_zeroOuter :
    (runFBsL 64 nestBlks (nestStart 0 5 8) false).map (fun bz => decodeM bz.1 "r3" 64)
      = some (some (ComL.denote nestSmokeProg
          (.cons (BitVec.ofNat 64 0)
            (.cons (BitVec.ofNat 64 5) (.cons (BitVec.ofNat 64 8) .nil)))))
      ∧ (runFBsL 64 nestBlks (nestStart 0 5 8) false).map
            (fun bz => decodeM bz.1 "r3" 64)
          = some (some (5#64)) := by native_decide

/-- Inner zero-trip (`num = 1`, `D = 2`): every recomputed inner trip is `0`
    (`1>>1 = 1>>2 = 0`), so the outer loop runs twice but the inner `Lcond Z`
    skips both times — the fold is the seed. -/
theorem nest_fold_zeroInner :
    (runFBsL 64 nestBlks (nestStart 2 7 1) false).map (fun bz => decodeM bz.1 "r3" 64)
      = some (some (ComL.denote nestSmokeProg
          (.cons (BitVec.ofNat 64 2)
            (.cons (BitVec.ofNat 64 7) (.cons (BitVec.ofNat 64 1) .nil)))))
      ∧ (runFBsL 64 nestBlks (nestStart 2 7 1) false).map
            (fun bz => decodeM bz.1 "r3" 64)
          = some (some (7#64)) := by native_decide

/-! ### The machine value THROUGH the closed theorem -/

/-- **The rendered nested stream, re-derived through `flagNest_closed`.**  The
    flag machine runs the ACTUAL `comLToBody` rendering of
    `ComL.forLoopNRtNested` (both zero-trip guards, both flag back-edges, the
    reg-copy seeds/feedback, the invariant touch) and halts at a state whose
    accumulator decodes to `ggmNestedFold 3 8 2 = 14` — the machine side from
    the closed theorem, `native_decide` only on the SPEC fold. -/
theorem nest_rendered_rederived_8 :
    ∃ (n : Nat) (t : LstateMF),
      lsemFuelMemF nestProg n
          { prog := { base := nestStart 3 0 8, lfn := "f" }, zf := false } = some t
        ∧ decodeM t.prog.base "r3" 64 = some (BitVec.ofNat 64 (ggmNestedFold 3 8 2)) := by
  cases hb : runFBsL 64 nestBlks (nestStart 3 0 8) false with
  | none =>
      have h1 := nest_fold_denote_8
      rw [hb] at h1
      simp at h1
  | some bz =>
      have hdec : decodeM bz.1 "r3" 64
          = some (BitVec.ofNat 64 (ggmNestedFold 3 8 2)) := by
        have h1 := nest_fold_ggm_8
        rw [hb] at h1
        simpa using h1
      obtain ⟨n, hn⟩ := flagNest_closed "f" nestBlks 64 (nestStart 3 0 8) false
        bz.1 bz.2 rfl
        (fblocksOKb_sound nestBlks (by native_decide))
        (fblocksResB_sound _ nestBlks 0 (by native_decide))
        (by rw [hb])
      rw [nestBlks_prog] at hn
      exact ⟨n, _, hn, hdec⟩

/-- **Outer zero-trip, re-derived through the closed theorem** (`D = 0`): the
    machine halts with the accumulator = the untouched seed — the outer
    `Lcond Z` forward-skip arm at region granularity. -/
theorem nest_rendered_zeroOuter :
    ∃ (n : Nat) (t : LstateMF),
      lsemFuelMemF nestProg n
          { prog := { base := nestStart 0 5 8, lfn := "f" }, zf := false } = some t
        ∧ decodeM t.prog.base "r3" 64 = some (5#64) := by
  cases hb : runFBsL 64 nestBlks (nestStart 0 5 8) false with
  | none =>
      have h1 := nest_fold_zeroOuter.1
      rw [hb] at h1
      simp at h1
  | some bz =>
      have hdec : decodeM bz.1 "r3" 64 = some (5#64) := by
        have h1 := nest_fold_zeroOuter.2
        rw [hb] at h1
        simpa using h1
      obtain ⟨n, hn⟩ := flagNest_closed "f" nestBlks 64 (nestStart 0 5 8) false
        bz.1 bz.2 rfl
        (fblocksOKb_sound nestBlks (by native_decide))
        (fblocksResB_sound _ nestBlks 0 (by native_decide))
        (by rw [hb])
      rw [nestBlks_prog] at hn
      exact ⟨n, _, hn, hdec⟩

/-- **Inner zero-trip, re-derived through the closed theorem** (`num = 1`,
    `D = 2`): both outer passes run, both inner regions zero-trip — the
    accumulator is the untouched seed. -/
theorem nest_rendered_zeroInner :
    ∃ (n : Nat) (t : LstateMF),
      lsemFuelMemF nestProg n
          { prog := { base := nestStart 2 7 1, lfn := "f" }, zf := false } = some t
        ∧ decodeM t.prog.base "r3" 64 = some (7#64) := by
  cases hb : runFBsL 64 nestBlks (nestStart 2 7 1) false with
  | none =>
      have h1 := nest_fold_zeroInner.1
      rw [hb] at h1
      simp at h1
  | some bz =>
      have hdec : decodeM bz.1 "r3" 64 = some (7#64) := by
        have h1 := nest_fold_zeroInner.2
        rw [hb] at h1
        simpa using h1
      obtain ⟨n, hn⟩ := flagNest_closed "f" nestBlks 64 (nestStart 2 7 1) false
        bz.1 bz.2 rfl
        (fblocksOKb_sound nestBlks (by native_decide))
        (fblocksResB_sound _ nestBlks 0 (by native_decide))
        (by rw [hb])
      rw [nestBlks_prog] at hn
      exact ⟨n, _, hn, hdec⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
