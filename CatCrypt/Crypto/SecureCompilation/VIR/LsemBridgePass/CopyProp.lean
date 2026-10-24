/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86

/-!
# Copy propagation over the uniform-width run with flags

`LcmdCopyPropagate.copyPropagateBody` rewrites the register sources of recognised
instructions by move facts (phase 1, `propagateAux`) and then deletes dead moves (phase 2,
`deadElimBody`). This module proves that the pass preserves the run
`LsemBridge.lsemStraightFlag`, the uniform-width run that carries the flags `cf`, `of`:
where the input body runs, the output body runs to a state with the same registers, the
same word memory and the same flags.

The step `lsemStepFlag` reads an instruction through three recognizers, `aluFlagOp?`,
`carryArgs?` and `wideArgs?`, each of which returns source operands of the instruction
unchanged. The recognizers are natural in a map over the sources (`aluFlagOp?_map`,
`carryArgs?_map`, `wideArgs?_map`), so a rewriting of the sources that preserves the value
`evalRI` of each operand preserves the step (`lsemStepFlag_rewrite_eq`). Phase 2 deletes
only instructions of `moveShape`; such an instruction has one source, so none of the three
recognizers accepts it and its step keeps both flags.

`lsemStepFlag` does not read the memory tag of an instruction (`lsemStepFlag_tag`), so the
statements hold for any tagging of the wire instructions.

## Main definitions

* `mapWide` — a map over the source operand of a `WideOp`.

## Main results

* `aluFlagOp?_map`, `carryArgs?_map`, `wideArgs?_map` — the recognizers of the flag layer
  are natural in a map over the sources.
* `lsemStepFlag_rewrite_eq`, `propagateAux_lsemStraightFlag` — phase 1 preserves the step
  and the run with flags.
* `lsemStepFlag_liveAgree`, `deadElim_simF` — phase 2 is a forward simulation up to the live
  set, with the flags equal.
* `copyPropagateBody_lsemStraightFlag` — the pass preserves the run with flags.
* `copyPropagateBody_lsemStraightMemF_F` — the transport to the flag machine through
  `lsemStraightMemF_transportF`, for an input and an output body in `fragFB` whose
  in-bounds runs succeed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyProp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend (WellFormedX86.isPrefixOf_eq_hasPrefix)

/-! ## 1. The recognizers of the flag layer under a map of the sources -/

/-- `lsemStepFlag` does not read the memory tag. -/
theorem lsemStepFlag_tag (i : LinstrR) (tg tg' : MemTag) (l : Lstate 64) :
    lsemStepFlag (i, tg) l = lsemStepFlag (i, tg') l := rfl

/-- Destructure the destination and source lists of an `Lopn` far enough for the three
    recognizers to reduce, and close the cases in which they reject. -/
local macro "shapes" dsts:ident srcs:ident : tactic =>
  `(tactic| (
    rcases $dsts:ident with _ | ⟨d, _ | ⟨d2, _ | ⟨d3, dr⟩⟩⟩ <;>
    rcases $srcs:ident with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
    (try cases d) <;> (try cases d2) <;> (try rfl)))

theorem aluFlagOp?_map (f : LOperand → LOperand) (dsts : List LOperand) (opn : String)
    (srcs : List LOperand) (tg tg' : MemTag) :
    aluFlagOp? (.Lopn dsts opn (srcs.map f), tg)
      = (aluFlagOp? (.Lopn dsts opn srcs, tg')).map fun p => (p.1, f p.2.1, f p.2.2) := by
  shapes dsts srcs
  all_goals
    simp only [aluFlagOp?, List.map_cons, List.map_nil]
    split_ifs <;> rfl

theorem carryArgs?_map (f : LOperand → LOperand) (dsts : List LOperand) (opn : String)
    (srcs : List LOperand) (tg tg' : MemTag) :
    carryArgs? (.Lopn dsts opn (srcs.map f), tg)
      = (carryArgs? (.Lopn dsts opn srcs, tg')).map
          fun p => (p.1, p.2.1, f p.2.2.1, f p.2.2.2) := by
  shapes dsts srcs
  all_goals
    simp only [carryArgs?, List.map_cons, List.map_nil]
    split_ifs <;> rfl

/-- A map over the source operand of a flag-quiet lift instruction. -/
def mapWide (f : LOperand → LOperand) : WideOp → WideOp
  | .mov d b => .mov d (f b)
  | .mulx lo hi b => .mulx lo hi (f b)

theorem wideArgs?_map (f : LOperand → LOperand) (dsts : List LOperand) (opn : String)
    (srcs : List LOperand) (tg tg' : MemTag) :
    wideArgs? (.Lopn dsts opn (srcs.map f), tg)
      = (wideArgs? (.Lopn dsts opn srcs, tg')).map (mapWide f) := by
  shapes dsts srcs
  all_goals
    simp only [wideArgs?, List.map_cons, List.map_nil]
    split_ifs <;> rfl

/-- **A value-preserving rewriting of the sources preserves the step with flags.** -/
theorem lsemStepFlag_map_eq {s : Lstate 64} (f : LOperand → LOperand)
    (hf : ∀ o, evalRI s (f o) = evalRI s o) (dsts : List LOperand) (opn : String)
    (srcs : List LOperand) (tg tg' : MemTag)
    (hstep : lsemStep (.Lopn dsts opn (srcs.map f)) s = lsemStep (.Lopn dsts opn srcs) s) :
    lsemStepFlag (.Lopn dsts opn (srcs.map f), tg) s
      = lsemStepFlag (.Lopn dsts opn srcs, tg') s := by
  unfold lsemStepFlag
  simp only [hstep, carryArgs?_map f dsts opn srcs tg tg', wideArgs?_map f dsts opn srcs tg tg']
  cases lsemStep (.Lopn dsts opn srcs) s with
  | some b =>
    simp only [Option.some.injEq]
    unfold withALUFlagsL
    rw [aluFlagOp?_map f dsts opn srcs tg tg']
    cases aluFlagOp? (.Lopn dsts opn srcs, tg') with
    | none => rfl
    | some p =>
      obtain ⟨op, a, b'⟩ := p
      simp only [Option.map_some, hf]
  | none =>
    simp only
    cases carryArgs? (.Lopn dsts opn srcs, tg') with
    | some p =>
      obtain ⟨op, d, a, b'⟩ := p
      simp only [Option.map_some, carryStepL, hf]
    | none =>
      simp only [Option.map_none]
      cases wideArgs? (.Lopn dsts opn srcs, tg') with
      | none => rfl
      | some w => cases w <;> simp only [Option.map_some, mapWide, wideStepL, hf]

/-! ## 2. Phase 1: forward move propagation -/

/-- A fact source has the value `evalOperand` gives it. -/
theorem evalRI_factSrc {s : Lstate 64} {o : LOperand} (ho : isFactSrc o = true) :
    evalRI s o = some (evalOperand s o) := by
  cases o <;> first | rfl | simp [isFactSrc] at ho

/-- A rewritten source has the value of the source. -/
theorem evalRI_rewriteOperand {facts : List MoveFact} {s : Lstate 64}
    (hok : FactsOk facts s) (ew : Nat) (ai : Bool) (dstSelf : Option String)
    (op : LOperand) :
    evalRI s (rewriteOperand facts ew ai dstSelf op) = evalRI s op := by
  cases op with
  | reg u =>
    simp only [rewriteOperand]
    split
    · split
      · rename_i v fw hp
        split
        · obtain ⟨-, hsrc, hval⟩ := hok _ (lookupFact_mem hp)
          rw [evalRI_factSrc hsrc]
          exact congrArg some hval.symm
        · rfl
      · rfl
    · rfl
  | imm _ => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

/-- Rewriting the sources of an instruction by valid facts leaves the step with flags
    unchanged. -/
theorem lsemStepFlag_rewrite_eq {facts : List MoveFact} {s : Lstate 64}
    (hok : FactsOk facts s) (dsts : List LOperand) (opn : String) (srcs : List LOperand)
    (ew : Nat) (ai : Bool) (dstSelf : Option String) (tg tg' : MemTag) :
    lsemStepFlag (.Lopn dsts opn (srcs.map (rewriteOperand facts ew ai dstSelf)), tg) s
      = lsemStepFlag (.Lopn dsts opn srcs, tg') s :=
  lsemStepFlag_map_eq _ (evalRI_rewriteOperand hok ew ai dstSelf) dsts opn srcs tg tg'
    (lsemStep_rewrite_eq hok dsts opn srcs ew ai dstSelf)

/-- `FactsOk` reads the state through the register map only. -/
theorem FactsOk_of_lvm {facts : List MoveFact} {s s₁ : Lstate 64} (hok : FactsOk facts s)
    (h : s₁.lvm = s.lvm) : FactsOk facts s₁ := by
  intro f hf
  obtain ⟨p1, p2, p3⟩ := hok f hf
  exact ⟨p1, p2, by rw [evalOperand_lvm_eq h p2, h]; exact p3⟩

/-- Split a recognizer equation `X? i = some p` into the instruction's shape. -/
local macro "recog" hx:ident : tactic =>
  `(tactic| (repeat' split at $hx:ident) <;> (try simp only [Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq] at $hx:ident) <;> (try casesm* _ ∧ _) <;> subst_vars)

/-- **The shape of a step that `lsemStep` does not take.** A carry-family step or a
    two-source copy writes one register; a widening multiply writes two. The word memory is
    unchanged. -/
theorem lsemStepFlag_none_inv (w : LinstrR) (tg : MemTag) {s s₁ : Lstate 64}
    (hst : lsemStep w s = none) (hstep : lsemStepFlag (w, tg) s = some s₁) :
    (∃ d opn a b v, w = .Lopn [.reg d] opn [a, b] ∧ s₁.lvm = (s.setReg d v).lvm
        ∧ s₁.lmem = s.lmem)
    ∨ (∃ lo hi opn b v v', w = .Lopn [.reg lo, .reg hi] opn [b]
        ∧ s₁.lvm = ((s.setReg lo v).setReg hi v').lvm ∧ s₁.lmem = s.lmem) := by
  cases hk : carryArgs? (w, tg) with
  | some p =>
    obtain ⟨op, d, a, b⟩ := p
    rw [lsemStepFlag_carry hst hk] at hstep
    unfold carryArgs? at hk
    simp only at hk
    recog hk
    all_goals
      simp only [carryStepL] at hstep
      generalize evalRI s _ = ea at hstep
      generalize evalRI s _ = eb at hstep
      cases ea <;> cases eb <;> simp only [reduceCtorEq, Option.some.injEq] at hstep
      subst hstep
      exact Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩
  | none =>
    cases hw : wideArgs? (w, tg) with
    | none =>
      unfold lsemStepFlag at hstep
      simp only [hst, hk, hw, reduceCtorEq] at hstep
    | some p =>
      rw [lsemStepFlag_wide hst hk hw] at hstep
      unfold wideArgs? at hw
      simp only at hw
      recog hw
      all_goals
        simp only [wideStepL] at hstep
        generalize evalRI s _ = eb at hstep
        cases eb <;> simp only [reduceCtorEq, Option.some.injEq] at hstep
        subst hstep
        first
          | exact Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩
          | exact Or.inr ⟨_, _, _, _, _, _, rfl, rfl, rfl⟩

/-- The fact set `propagateAux` carries past a recognised op is valid in the state that op
    steps to under `lsemStepFlag`. -/
theorem FactsOk_stepF {facts : List MoveFact} {s s₁ : Lstate 64}
    (hok : FactsOk facts s) {i' : Linstr} {dsts : List LOperand} {opn : String}
    {srcs' : List LOperand} (hi' : i'.li_i = .Lopn dsts opn srcs') (tg : MemTag)
    (hstep : lsemStepFlag (i'.li_i, tg) s = some s₁) :
    FactsOk (match moveShape i' with
             | some (d, src, ww) =>
                 if src == LOperand.reg d then (regDefsOf dsts).foldl killFacts facts
                 else (d, src, ww) :: (regDefsOf dsts).foldl killFacts facts
             | none => (regDefsOf dsts).foldl killFacts facts) s₁ := by
  cases hst : lsemStep i'.li_i s with
  | some b =>
    rw [lsemStepFlag_of_lsemStep hst, Option.some.injEq] at hstep
    subst hstep
    exact FactsOk_of_lvm (FactsOk_step hok hi' hst) (withALUFlagsL_lvm _ _ _)
  | none =>
    have hms : moveShape i' = none := by
      cases hm : moveShape i' with
      | none => rfl
      | some q =>
        have := moveShape_lsemStep_isSome hm s
        rw [hst] at this
        exact absurd this (by simp)
    rw [hms]
    rcases lsemStepFlag_none_inv i'.li_i tg hst hstep with
      ⟨d, opn', a, b, v, hw, hv, -⟩ | ⟨lo, hi, opn', b, v, v', hw, hv, -⟩
    · rw [hi'] at hw
      injection hw with hd _ _
      subst hd
      exact FactsOk_of_lvm (FactsOk_write (dst := d) (v := v) hok) hv
    · rw [hi'] at hw
      injection hw with hd _ _
      subst hd
      have e : regDefsOf [LOperand.reg lo, LOperand.reg hi]
          = regDefsOf [LOperand.reg lo] ++ regDefsOf [LOperand.reg hi] := by
        show regDefsOf ([LOperand.reg lo] ++ [LOperand.reg hi]) = _
        unfold regDefsOf
        rw [List.filterMap_append]
      rw [e, List.foldl_append]
      exact FactsOk_of_lvm
        (FactsOk_write (dst := hi) (v := v') (FactsOk_write (dst := lo) (v := v) hok)) hv

/-- **Phase 1 preserves the run with flags.** Under a valid fact set, forward propagation
    leaves `lsemStraightFlag` unchanged on every start state, for any tagging of the input
    and of the output. -/
theorem propagateAux_lsemStraightFlag (tag tag' : LinstrR → MemTag) (body : Lcmd) :
    ∀ (facts : List MoveFact) (s : Lstate 64), FactsOk facts s →
      lsemStraightFlag ((propagateAux facts body).map fun i => (i.li_i, tag' i.li_i)) s
        = lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s := by
  have hnil : ∀ (t : Lstate 64), FactsOk ([] : List MoveFact) t := by
    intro t f hf; exact absurd hf (by simp)
  induction body with
  | nil => intro facts s _; rfl
  | cons i rest ih =>
    intro facts s hok
    rw [propagateAux]
    split
    · rename_i dsts opn srcs hi
      split
      · rename_i hrec
        simp only [List.map_cons, lsemStraightFlag_cons]
        rw [hi]
        rw [lsemStepFlag_rewrite_eq hok dsts opn srcs (effWidth opn) _ _ _
          (tag (.Lopn dsts opn srcs))]
        cases hst : lsemStepFlag (.Lopn dsts opn srcs, tag (.Lopn dsts opn srcs)) s with
        | none => rfl
        | some s₁ =>
          refine ih _ s₁ ?_
          refine FactsOk_stepF hok rfl (tag (.Lopn dsts opn srcs)) ?_
          rw [lsemStepFlag_rewrite_eq hok dsts opn srcs (effWidth opn) _ _ _
            (tag (.Lopn dsts opn srcs))]
          exact hst
      · simp only [List.map_cons, lsemStraightFlag_cons]
        rw [lsemStepFlag_tag i.li_i (tag' i.li_i) (tag i.li_i)]
        cases hst : lsemStepFlag (i.li_i, tag i.li_i) s with
        | none => rfl
        | some s₁ => exact ih [] s₁ (hnil s₁)
    · simp only [List.map_cons, lsemStraightFlag_cons]
      rw [lsemStepFlag_tag i.li_i (tag' i.li_i) (tag i.li_i)]
      cases hst : lsemStepFlag (i.li_i, tag i.li_i) s with
      | none => rfl
      | some s₁ => exact ih [] s₁ (hnil s₁)

/-! ## 3. The step with flags from two agreeing states -/

theorem aluFlagOp?_inv {w : LinstrR} {tg : MemTag} {op : AluOp} {a b : LOperand}
    (h : aluFlagOp? (w, tg) = some (op, a, b)) : ∃ d opn, w = .Lopn [.reg d] opn [a, b] := by
  unfold aluFlagOp? at h
  simp only at h
  recog h
  all_goals exact ⟨_, _, rfl⟩

theorem carryArgs?_inv {w : LinstrR} {tg : MemTag} {op : CarryOp} {d : String}
    {a b : LOperand} (h : carryArgs? (w, tg) = some (op, d, a, b)) :
    ∃ opn, w = .Lopn [.reg d] opn [a, b] := by
  unfold carryArgs? at h
  simp only at h
  recog h
  all_goals exact ⟨_, rfl⟩

theorem wideArgs?_inv_mov {w : LinstrR} {tg : MemTag} {d : String} {b : LOperand}
    (h : wideArgs? (w, tg) = some (.mov d b)) : ∃ opn a, w = .Lopn [.reg d] opn [a, b] := by
  unfold wideArgs? at h
  simp only at h
  repeat' split at h
  all_goals try simp only [Option.some.injEq, WideOp.mov.injEq, reduceCtorEq] at h
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, rfl⟩

theorem wideArgs?_inv_mulx {w : LinstrR} {tg : MemTag} {lo hi : String} {b : LOperand}
    (h : wideArgs? (w, tg) = some (.mulx lo hi b)) :
    w = .Lopn [.reg lo, .reg hi] (withWidthTag 64 "MULX") [b]
      ∨ w = .Lopn [.reg lo, .reg hi] (withWidthTag 64 "MULXMEM") [b] := by
  unfold wideArgs? at h
  simp only at h
  repeat' split at h
  all_goals try simp only [Option.some.injEq, WideOp.mulx.injEq, reduceCtorEq] at h
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := h
    rename_i hor
    rcases hor with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The widening multiplies are not recognised by the pass. `String.isPrefixOf` is a prefix
    test of the character lists, which the kernel decides. -/
theorem isRecognizedOpn_MULX64 : isRecognizedOpn (withWidthTag 64 "MULX") = false :=
  isRecognizedOpn_MULX (by
    rw [WellFormedX86.isPrefixOf_eq_hasPrefix]
    decide +kernel)

theorem isRecognizedOpn_MULXMEM64 : isRecognizedOpn (withWidthTag 64 "MULXMEM") = false :=
  isRecognizedOpn_MULX (by
    rw [WellFormedX86.isPrefixOf_eq_hasPrefix]
    decide +kernel)

/-- A register or immediate operand whose physical-GP read is live has the same value in
    two `LiveAgree` states. -/
theorem evalRI_liveAgree {L : List String} {s t : Lstate 64} (h : LiveAgree L s t)
    (o : LOperand) (hcov : ∀ r, (operandReads o).contains r = true → L.contains r = true) :
    evalRI s o = evalRI t o := by
  cases o with
  | reg n =>
    simp only [evalRI]
    refine congrArg some (h.2 n ?_)
    by_cases hp : isPhysGP n = true
    · exact Or.inr (hcov n (by simp [operandReads, nameReads, hp]))
    · exact Or.inl (by simpa using hp)
  | imm _ => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

/-- The flags `withALUFlagsL` writes agree from two states that give the sources the same
    values, on post-states with equal flags. -/
theorem withALUFlagsL_flags_congr {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} (tg : MemTag) {s t b b' : Lstate 64}
    (hE : ∀ o ∈ srcs, evalRI s o = evalRI t o) (hc : b.cf = b'.cf) (ho : b.of = b'.of) :
    (withALUFlagsL (.Lopn dsts opn srcs, tg) s b).cf
        = (withALUFlagsL (.Lopn dsts opn srcs, tg) t b').cf
      ∧ (withALUFlagsL (.Lopn dsts opn srcs, tg) s b).of
        = (withALUFlagsL (.Lopn dsts opn srcs, tg) t b').of := by
  unfold withALUFlagsL
  cases hx : aluFlagOp? (.Lopn dsts opn srcs, tg) with
  | none => exact ⟨hc, ho⟩
  | some p =>
    obtain ⟨op, a, b2⟩ := p
    obtain ⟨d, opn', hw⟩ := aluFlagOp?_inv hx
    injection hw with _ _ hs
    subst hs
    simp only
    rw [← hE a (by simp), ← hE b2 (by simp)]
    cases evalRI s a <;> cases evalRI s b2 <;> exact ⟨by first | rfl | exact hc,
      by first | rfl | exact ho⟩

/-- The program counter is not read by `evalRI`. -/
theorem evalRI_setPc (s : Lstate 64) (p : Nat) : evalRI { s with lpc := p } = evalRI s := by
  funext o; cases o <;> rfl

theorem lsemStep_setPc (i : LinstrR) (s : Lstate 64) (p : Nat) :
    lsemStep i { s with lpc := p } = (lsemStep i s).map fun x => { x with lpc := p + 1 } := by
  have hev : evalOperand ({ s with lpc := p } : Lstate 64) = evalOperand s := by
    funext x; cases x <;> rfl
  unfold lsemStep
  simp only [hev]
  repeat' split
  all_goals rfl

/-- The step with flags reads the program counter only to advance it. -/
theorem lsemStepFlag_setPc (i : LinstrRM) (s : Lstate 64) (p : Nat) :
    lsemStepFlag i { s with lpc := p }
      = (lsemStepFlag i s).map fun x => { x with lpc := p + 1 } := by
  unfold lsemStepFlag
  rw [lsemStep_setPc]
  cases lsemStep i.1 s with
  | some b =>
    simp only [Option.map_some, Option.some.injEq]
    unfold withALUFlagsL
    simp only [evalRI_setPc]
    cases aluFlagOp? i with
    | none => rfl
    | some q =>
      obtain ⟨op, a, b'⟩ := q
      simp only
      cases evalRI s a <;> cases evalRI s b' <;> rfl
  | none =>
    simp only [Option.map_none]
    cases carryArgs? i with
    | some q =>
      obtain ⟨op, d, a, b⟩ := q
      simp only [carryStepL, evalRI_setPc]
      cases evalRI s a <;> cases evalRI s b <;> cases op <;> rfl
    | none =>
      simp only
      cases wideArgs? i with
      | none => rfl
      | some w =>
        cases w <;> simp only [wideStepL, evalRI_setPc] <;> generalize evalRI s _ = e <;>
          cases e <;> rfl

/-- From states with the same registers, word memory and flags, every instruction steps
    under `lsemStepFlag` to states with the same registers, word memory and flags. -/
theorem lsemStepFlag_congr_full (i : LinstrRM) {s t : Lstate 64} (hv : s.lvm = t.lvm)
    (hm : s.lmem = t.lmem) (hc : s.cf = t.cf) (ho : s.of = t.of) {s₁ : Lstate 64}
    (hst : lsemStepFlag i s = some s₁) :
    ∃ t₁, lsemStepFlag i t = some t₁ ∧ s₁.lvm = t₁.lvm ∧ s₁.lmem = t₁.lmem
      ∧ s₁.cf = t₁.cf ∧ s₁.of = t₁.of := by
  have ht : t = { s with lpc := t.lpc } := by
    cases s; cases t; simp_all
  rw [ht, lsemStepFlag_setPc, hst]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- **The step with flags from two `LiveAgree` states with equal flags.** An op other than a
    widening multiply, all of whose physical-GP source reads are live, steps in lockstep:
    it writes the same word to its destination in both states and keeps the word memory
    (left disjunct), or it leaves the register map and writes equal memory (right
    disjunct); the flags of the two results are equal. -/
theorem lsemStepFlag_liveAgree {L : List String} {s t : Lstate 64} (h : LiveAgree L s t)
    (hcf : s.cf = t.cf) (hof : s.of = t.of) {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} (tg : MemTag)
    (hcov : ∀ o ∈ srcs, ∀ r, (operandReads o).contains r = true → L.contains r = true)
    (hmx : ∀ lo hi b, wideArgs? (.Lopn dsts opn srcs, tg) ≠ some (.mulx lo hi b))
    {s₁ : Lstate 64} (hstep : lsemStepFlag (.Lopn dsts opn srcs, tg) s = some s₁) :
    ∃ t₁ dst, lsemStepFlag (.Lopn dsts opn srcs, tg) t = some t₁
      ∧ dsts = [LOperand.reg dst] ∧ s₁.cf = t₁.cf ∧ s₁.of = t₁.of ∧
      ((∃ v, s₁.lvm = (s.setReg dst v).lvm ∧ t₁.lvm = (t.setReg dst v).lvm
          ∧ s₁.lmem = s.lmem ∧ t₁.lmem = t.lmem)
       ∨ (s₁.lvm = s.lvm ∧ t₁.lvm = t.lvm ∧ s₁.lmem = t₁.lmem
          ∧ fullDefsOf dsts opn = [])) := by
  have hE : ∀ o ∈ srcs, evalRI s o = evalRI t o :=
    fun o ho => evalRI_liveAgree h o (hcov o ho)
  cases hst : lsemStep (.Lopn dsts opn srcs) s with
  | some b =>
    rw [lsemStepFlag_of_lsemStep (i := (.Lopn dsts opn srcs, tg)) hst,
      Option.some.injEq] at hstep
    subst hstep
    obtain ⟨hbc, hbo⟩ := lsemStep_flags _ _ _ hst
    obtain ⟨dst, hd, hcase⟩ := lsemStep_liveAgree h hcov hst
    rcases hcase with ⟨v, hb, hts⟩ | ⟨t₁, hts, hsv, htv, hmemeq, hfd⟩
    · obtain ⟨f1, f2⟩ := withALUFlagsL_flags_congr (dsts := dsts) (opn := opn) tg (b := b)
        (b' := (t.setReg dst v).nextPc) hE (by rw [hbc]; exact hcf) (by rw [hbo]; exact hof)
      refine ⟨_, dst, lsemStepFlag_of_lsemStep (i := (.Lopn dsts opn srcs, tg)) hts, hd,
        f1, f2, Or.inl ⟨v, ?_, ?_, ?_, ?_⟩⟩
      · rw [withALUFlagsL_lvm, hb]; rfl
      · rw [withALUFlagsL_lvm]; rfl
      · rw [withALUFlagsL_lmem, hb]; rfl
      · rw [withALUFlagsL_lmem]; rfl
    · obtain ⟨tc, tof⟩ := lsemStep_flags _ _ _ hts
      obtain ⟨f1, f2⟩ := withALUFlagsL_flags_congr (dsts := dsts) (opn := opn) tg (b := b)
        (b' := t₁) hE (by rw [hbc, tc]; exact hcf) (by rw [hbo, tof]; exact hof)
      exact ⟨_, dst, lsemStepFlag_of_lsemStep (i := (.Lopn dsts opn srcs, tg)) hts, hd,
        f1, f2, Or.inr ⟨by rw [withALUFlagsL_lvm]; exact hsv,
          by rw [withALUFlagsL_lvm]; exact htv,
          by rw [withALUFlagsL_lmem, withALUFlagsL_lmem]; exact hmemeq, hfd⟩⟩
  | none =>
    have hstt : lsemStep (.Lopn dsts opn srcs) t = none := by
      have := lsemStep_isSome_indep (.Lopn dsts opn srcs) s t
      rw [hst] at this
      cases ht : lsemStep (.Lopn dsts opn srcs) t with
      | none => rfl
      | some x => rw [ht] at this; exact absurd this (by simp)
    cases hk : carryArgs? (.Lopn dsts opn srcs, tg) with
    | some p =>
      obtain ⟨op, d, a, b⟩ := p
      obtain ⟨opn', hw⟩ := carryArgs?_inv hk
      injection hw with hd _ hs
      subst hd
      subst hs
      rw [lsemStepFlag_carry (i := (.Lopn [.reg d] opn [a, b], tg)) hst hk] at hstep
      rw [lsemStepFlag_carry (i := (.Lopn [.reg d] opn [a, b], tg)) hstt hk]
      simp only [carryStepL] at hstep ⊢
      rw [← hE a (by simp), ← hE b (by simp), ← hcf, ← hof]
      generalize evalRI s a = ea at hstep ⊢
      generalize evalRI s b = eb at hstep ⊢
      cases ea <;> cases eb <;> simp only [reduceCtorEq] at hstep
      cases op <;> simp only [Option.some.injEq] at hstep <;> subst hstep <;>
        exact ⟨_, d, rfl, rfl, by first | rfl | exact hcf, by first | rfl | exact hof,
          Or.inl ⟨_, rfl, rfl, rfl, rfl⟩⟩
    | none =>
      cases hw : wideArgs? (.Lopn dsts opn srcs, tg) with
      | none =>
        unfold lsemStepFlag at hstep
        simp only [hst, hk, hw, reduceCtorEq] at hstep
      | some wd =>
        cases wd with
        | mulx lo hi b => exact absurd hw (hmx lo hi b)
        | mov d b =>
          obtain ⟨opn', a, hww⟩ := wideArgs?_inv_mov hw
          injection hww with hd _ hs
          subst hd
          subst hs
          rw [lsemStepFlag_wide (i := (.Lopn [.reg d] opn [a, b], tg)) hst hk hw] at hstep
          rw [lsemStepFlag_wide (i := (.Lopn [.reg d] opn [a, b], tg)) hstt hk hw]
          simp only [wideStepL] at hstep ⊢
          rw [← hE b (by simp)]
          generalize evalRI s b = eb at hstep ⊢
          cases eb <;> simp only [reduceCtorEq, Option.some.injEq] at hstep
          subst hstep
          exact ⟨_, d, rfl, rfl, hcf, hof, Or.inl ⟨_, rfl, rfl, rfl, rfl⟩⟩

/-! ## 4. Phase 2: backward dead-move elimination -/

/-- The live-set update of a kept op that writes its destination. -/
theorem liveAgree_write {Lr : List String} {dst opn : String} {srcs : List LOperand}
    {s t s₁ t₁ : Lstate 64}
    (h : LiveAgree (addRegs (Lr.filter fun r => !((fullDefsOf [LOperand.reg dst] opn).contains r))
      (instrUses [LOperand.reg dst] opn srcs)) s t)
    {v : BitVec 64} (hs : s₁.lvm = (s.setReg dst v).lvm) (ht : t₁.lvm = (t.setReg dst v).lvm)
    (hsm : s₁.lmem = s.lmem) (htm : t₁.lmem = t.lmem) : LiveAgree Lr s₁ t₁ := by
  refine ⟨by rw [hsm, htm]; exact h.1, ?_⟩
  intro r hr
  rw [hs, ht]
  simp only [Lstate.lvm_setReg]
  by_cases hrd : r = dst
  · rw [ite_eq_left hrd, ite_eq_left hrd]
  · rw [ite_eq_right hrd, ite_eq_right hrd]
    refine h.2 r ?_
    rcases hr with hp | hm
    · exact Or.inl hp
    · refine Or.inr (contains_addRegs_left _ _ ?_)
      have hmem : r ∈ Lr := by simpa using hm
      have hpred : (!((fullDefsOf [LOperand.reg dst] opn).contains r)) = true := by
        rw [contains_fullDefsOf_false hrd]; rfl
      have hfil : r ∈ Lr.filter (fun x => !((fullDefsOf [LOperand.reg dst] opn).contains x)) :=
        List.mem_filter.mpr ⟨hmem, hpred⟩
      simpa using hfil

/-- The live-set update of a kept op that writes no register. -/
theorem liveAgree_nowrite {Lr : List String} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {s t s₁ t₁ : Lstate 64}
    (h : LiveAgree (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
      (instrUses dsts opn srcs)) s t)
    (hfd : fullDefsOf dsts opn = []) (hs : s₁.lvm = s.lvm) (ht : t₁.lvm = t.lvm)
    (hm : s₁.lmem = t₁.lmem) : LiveAgree Lr s₁ t₁ := by
  refine ⟨hm, ?_⟩
  intro r hr
  rw [hs, ht]
  refine h.2 r ?_
  rcases hr with hp | hm
  · exact Or.inl hp
  · refine Or.inr (contains_addRegs_left _ _ ?_)
    have hmem : r ∈ Lr := by simpa using hm
    have hpred : (!((fullDefsOf dsts opn).contains r)) = true := by simp [hfd]
    have hfil : r ∈ Lr.filter (fun x => !((fullDefsOf dsts opn).contains x)) :=
      List.mem_filter.mpr ⟨hmem, hpred⟩
    simpa using hfil

/-- **Phase 2 is a forward simulation up to the live set, with the flags equal.** From
    states agreeing off the computed live-in set and on the flags, a body that runs to
    completion under `lsemStraightFlag` is matched by the swept body, ending in states
    agreeing off the end live set and on the flags. -/
theorem deadElim_simF (tag : LinstrR → MemTag) (body : Lcmd) :
    ∀ (Lend : List String) (s t : Lstate 64),
      LiveAgree (body.foldr deadElimStep (Lend, [])).1 s t → s.cf = t.cf → s.of = t.of →
      ∀ s₂, lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s = some s₂ →
        ∃ t₂, lsemStraightFlag
            ((body.foldr deadElimStep (Lend, [])).2.map fun i => (i.li_i, tag i.li_i)) t
              = some t₂
          ∧ LiveAgree Lend s₂ t₂ ∧ s₂.cf = t₂.cf ∧ s₂.of = t₂.of := by
  induction body with
  | nil =>
    intro Lend s t h hcf hof s₂ hrun
    simp only [List.map_nil, lsemStraightFlag_nil, Option.some.injEq] at hrun
    subst hrun
    exact ⟨t, rfl, h, hcf, hof⟩
  | cons i rest ih =>
    intro Lend s t h hcf hof s₂ hrun
    simp only [List.map_cons, lsemStraightFlag_cons] at hrun
    have ih' := ih Lend
    obtain ⟨Lr, outR, hP⟩ : ∃ a b, rest.foldr deadElimStep (Lend, []) = (a, b) := ⟨_, _, rfl⟩
    rw [hP] at ih'
    rw [List.foldr_cons, hP] at h ⊢
    cases hst : lsemStepFlag (i.li_i, tag i.li_i) s with
    | none => rw [hst] at hrun; exact absurd hrun (by simp)
    | some s₁ =>
      rw [hst, Option.bind_some] at hrun
      have hcases :
          (∃ dsts opn srcs, i.li_i = LinstrR.Lopn dsts opn srcs ∧ isRecognizedOpn opn = true)
          ∨ (∀ (live : List String) (acc : Lcmd),
              deadElimStep i (live, acc) = (physGPs, i :: acc)) := by
        cases hLi : i.li_i with
        | Lopn dsts opn srcs =>
          by_cases hr : isRecognizedOpn opn = true
          · exact Or.inl ⟨dsts, opn, srcs, rfl, hr⟩
          · refine Or.inr (fun live acc => deadElimStep_barrier i live acc ?_)
            intro d o sc he
            rw [hLi] at he
            injection he with _ h2 _
            rw [← h2]
            simpa using hr
        | _ =>
          exact Or.inr (fun live acc => deadElimStep_barrier i live acc (by
            intro d o sc he; rw [hLi] at he; exact absurd he (by simp)))
      rcases hcases with ⟨dsts, opn, srcs, hLi, hrec⟩ | hbar
      · have hkeep : deadElimStep i (Lr, outR)
              = (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
                  (instrUses dsts opn srcs), i :: outR) →
            ∃ t₂, lsemStraightFlag
                ((deadElimStep i (Lr, outR)).2.map fun i => (i.li_i, tag i.li_i)) t = some t₂
              ∧ LiveAgree Lend s₂ t₂ ∧ s₂.cf = t₂.cf ∧ s₂.of = t₂.of := by
          intro hk
          rw [hk] at h ⊢
          dsimp only at h ⊢
          have hcov : ∀ o ∈ srcs, ∀ r, (operandReads o).contains r = true →
              (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
                (instrUses dsts opn srcs)).contains r = true :=
            fun o ho r hr => contains_addRegs_right _ _ (contains_instrUses_of_src ho hr)
          have hmx : ∀ lo hi b, wideArgs? (.Lopn dsts opn srcs, tag (.Lopn dsts opn srcs))
              ≠ some (.mulx lo hi b) := by
            intro lo hi b hw
            rcases wideArgs?_inv_mulx hw with e | e
            · injection e with _ ho _
              rw [ho, isRecognizedOpn_MULX64] at hrec
              exact absurd hrec (by simp)
            · injection e with _ ho _
              rw [ho, isRecognizedOpn_MULXMEM64] at hrec
              exact absurd hrec (by simp)
          rw [hLi] at hst
          obtain ⟨t₁, dst, hts, hd, f1, f2, hcase⟩ :=
            lsemStepFlag_liveAgree h hcf hof _ hcov hmx hst
          simp only [List.map_cons, lsemStraightFlag_cons, hLi, hts, Option.bind_some]
          subst hd
          rcases hcase with ⟨v, a1, a2, a3, a4⟩ | ⟨a1, a2, a3, hfd⟩
          · exact ih' s₁ t₁ (liveAgree_write h a1 a2 a3 a4) f1 f2 s₂ hrun
          · exact ih' s₁ t₁ (liveAgree_nowrite h hfd a1 a2 a3) f1 f2 s₂ hrun
        cases hcs : moveShape i with
        | none => exact hkeep (deadElimStep_keep_none Lr outR hLi hrec hcs)
        | some q =>
          obtain ⟨d, src, ww⟩ := q
          by_cases hdr : ((ww == 64 && src == LOperand.reg d) || !(Lr.contains d)) = true
          · rw [deadElimStep_drop Lr outR hLi hrec hcs hdr] at h ⊢
            dsimp only at h ⊢
            obtain ⟨opn2, hi2, hd, hsr, hmov2⟩ := moveShape_inv hcs
            have hsome := moveShape_lsemStep_isSome hcs s
            cases hb : lsemStep i.li_i s with
            | none => rw [hb] at hsome; exact absurd hsome (by simp)
            | some b =>
              rw [lsemStepFlag_of_lsemStep (i := (i.li_i, tag i.li_i)) hb,
                Option.some.injEq] at hst
              have hfl : withALUFlagsL (i.li_i, tag i.li_i) s b = b := by
                unfold withALUFlagsL
                rw [show aluFlagOp? (i.li_i, tag i.li_i) = none from by rw [hi2]; rfl]
              rw [hfl] at hst
              subst hst
              obtain ⟨c1, c2⟩ := lsemStep_flags _ _ _ hb
              refine ih' b t ?_ (c1.trans hcf) (c2.trans hof) s₂ hrun
              have hnm : opn2 ≠ "LOADIDX" ∧ opn2 ≠ "STOREIDX" :=
                ⟨fun hc => by rw [moveShape_none_of_mem hi2 (Or.inl hc)] at hcs
                              simp at hcs,
                 fun hc => by rw [moveShape_none_of_mem hi2 (Or.inr hc)] at hcs
                              simp at hcs⟩
              rw [hi2] at hb
              obtain ⟨dst, v, hdd, happ, hs₁⟩ := lsemStep_Lopn_inv hnm hb
              have hdst : dst = d := by
                injection hdd with h1 _; injection h1 with h2; exact h2.symm
              subst hdst
              have hv : v = evalOperand s src := by
                simp only [List.map_cons, List.map_nil] at happ
                exact applyOpn_singleton hmov2 happ
              refine ⟨?_, ?_⟩
              · rw [hs₁]; exact h.1
              · intro r hr
                rw [hs₁]
                simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
                by_cases hrd : r = dst
                · rcases (Bool.or_eq_true _ _).mp hdr with hself | hdead
                  · have hds : src = LOperand.reg dst :=
                      eq_of_beq ((Bool.and_eq_true _ _).mp hself).2
                    rw [ite_eq_left hrd, hv, hds]
                    simp only [evalOperand]
                    rw [← hrd]
                    exact h.2 r hr
                  · exfalso
                    have hnc : Lr.contains dst = false := by simpa using hdead
                    rcases hr with hp | hm
                    · rw [hrd] at hp; rw [hp] at hd; exact absurd hd (by simp)
                    · rw [hrd, hnc] at hm; exact absurd hm (by simp)
                · rw [ite_eq_right hrd]; exact h.2 r hr
          · exact hkeep (deadElimStep_keep_some Lr outR hLi hrec hcs (by simpa using hdr))
      · rw [hbar Lr outR] at h ⊢
        dsimp only at h ⊢
        obtain ⟨hvv, hmm⟩ := LiveAgree.full h
        obtain ⟨t₁, hts, e1, e2, e3, e4⟩ :=
          lsemStepFlag_congr_full (i.li_i, tag i.li_i) hvv hmm hcf hof hst
        simp only [List.map_cons, lsemStraightFlag_cons, hts, Option.bind_some]
        exact ih' s₁ t₁ ⟨e2, fun r _ => congrFun e1 r⟩ e3 e4 s₂ hrun

/-! ## 5. The pass -/

/-- **Copy propagation preserves the run with flags.** On every body and every start state
    from which the input runs to completion under `lsemStraightFlag`, the output runs to
    completion and reaches a state with the same register map, the same word memory and the
    same flags, for any tagging of the input and of the output. The program counter is
    lower by the number of deleted instructions. -/
theorem copyPropagateBody_lsemStraightFlag (tag tag' : LinstrR → MemTag) (body : Lcmd)
    (s s₂ : Lstate 64)
    (hrun : lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((copyPropagateBody body).map fun i => (i.li_i, tag' i.li_i)) s
        = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem ∧ t₂.cf = s₂.cf ∧ t₂.of = s₂.of := by
  have h1 : lsemStraightFlag ((propagateAux [] body).map fun i => (i.li_i, tag' i.li_i)) s
      = some s₂ := by
    rw [propagateAux_lsemStraightFlag tag tag' body [] s (fun f hf => absurd hf (by simp))]
    exact hrun
  obtain ⟨t₂, ht, hag, c, o⟩ := deadElim_simF tag' (propagateAux [] body) physGPs s s
    (LiveAgree.refl _ s) rfl rfl s₂ h1
  exact ⟨t₂, ht, hag.full.1.symm, hag.full.2.symm, c.symm, o.symm⟩

/-- **Copy propagation on the flag machine through the bridge with flags.** Let the input
    body and the output body of the pass be bodies of the fragment with flags whose
    in-bounds runs from `l` succeed. From a state related to `l` with its flags, both run
    under `lsemStraightMemF`, to states with the same registers, arrays, word memory and
    flags. -/
theorem copyPropagateBody_lsemStraightMemF_F {A : String → Option Nat}
    (tag : LinstrR → MemTag) (b : Lcmd)
    (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true)
    (hfrag' : ∀ i ∈ copyPropagateBody b, fragFB A (i.li_i, tag i.li_i) = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRelF A s l)
    (hib : (runIBF (b.map fun i => (i.li_i, tag i.li_i)) l).isSome)
    (hib' : (runIBF ((copyPropagateBody b).map fun i => (i.li_i, tag i.li_i)) l).isSome) :
    ∃ u u',
      lsemStraightMemF ((copyPropagateBody b).map fun i => (i.li_i, tag i.li_i)) s = some u ∧
      lsemStraightMemF (b.map fun i => (i.li_i, tag i.li_i)) s = some u' ∧
      u.reg.lvm = u'.reg.lvm ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem ∧
      u.cf = u'.cf ∧ u.of = u'.of := by
  have hB : ∀ i ∈ (copyPropagateBody b).map (fun i => (i.li_i, tag i.li_i)),
      fragFB A i = true := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hfrag' j hj
  have hB' : ∀ i ∈ b.map (fun i => (i.li_i, tag i.li_i)), fragFB A i = true := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hfrag j hj
  obtain ⟨u, u', t, t', hu, hu', ht, ht', hO, hA, hM, hc, ho, hc', ho'⟩ :=
    lsemStraightMemF_transportF (O := fun _ => True) hB hB' hr hib' hib
      (fun t t' ht ht' => by
        obtain ⟨t₂, h2, hl, hm, -, -⟩ := copyPropagateBody_lsemStraightFlag tag tag b l t' ht'
        rw [ht] at h2
        obtain rfl := Option.some.inj h2
        exact ⟨fun r _ => congrFun hl r, fun B n _ k _ => congrFun (congrFun hm B) _⟩)
  obtain ⟨t₂, h2, -, -, fc, fo⟩ := copyPropagateBody_lsemStraightFlag tag tag b l t' ht'
  rw [ht] at h2
  obtain rfl := Option.some.inj h2
  exact ⟨u, u', hu, hu', funext fun r => hO r trivial, hA, hM,
    by rw [hc, hc', fc], by rw [ho, ho', fo]⟩

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyProp
