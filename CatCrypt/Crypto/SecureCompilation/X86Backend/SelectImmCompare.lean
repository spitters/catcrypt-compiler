/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront

/-!
# The dialect select against a constant, compared in place

An opt-in `Lprog → Lprog` pass over the owned-RA linear body
(`JasminLprogExport.Lcmd`) that folds a materialised constant into the second
operand of the materialised comparison that reads it.

The `RSelect` arm of `TranslateDialectDirectArms.translateDialectFull` emits
`z := bvConst 64 0 ; b := bvEq 64 s z ; r := ite b a c`, and
`VIR.DialectToJasminCom.toJExprD` maps the `bvEq` to `JasminOp.cmp .eq 64`. The
exported body therefore holds `Lopn [z] MOV:64 [.imm k]` followed by
`Lopn [b] SET<cc>:64 [.reg x, .reg z]`, printed

    movq $k, z ; cmpq z, x ; movq $0, b ; set<cc> b

The pass deletes the constant move and rewrites the comparison to
`Lopn [b] SET<cc>:64 [.reg x, .imm k]`, which `LprogAsmPrinter.renderLopn`
prints as `cmpq $k, x ; movq $0, b ; set<cc> b`, so the constant is never held
in a register. `LprogCmovTestElim.cmpFuseBody` then drops the materialisation of
`b` as well, leaving `cmpq $k, x` and two-address conditional moves.

## The rewrite

The sweep carries the register whose constant only the original body holds,
together with that constant.

* At `Lopn [z] MOV:64 [.imm k]` with `z` a pool register
  (`LcmdCopyPropagate.isPhysGP`) and the lookahead `immWorth` finding a
  comparison against `z` before any other use of `z`, the move is deleted and
  `(z, k)` becomes carried; `z` leaves the agreement set.
* At `Lopn [b] SET<cc>:64 [.reg x, .reg z]` on the carried register, with `x`
  in the agreement set and `x ≠ z`, the comparison becomes
  `Lopn [b] SET<cc>:64 [.reg x, .imm k]` and the carry is dropped.
* Every other instruction is kept, under `LprogCmovTestElim.keepOk`: each
  register it reads is in the agreement set, so an instruction reading `z`
  fails the sweep. The carry is dropped at any single-register write of `z`
  and at every instruction outside the single-register-write shape.
* The sweep fails when a kept instruction reads a register outside the
  agreement set, and at the end of the body when a register of `liveOut` is
  outside it. `immFuseBody` returns the body unchanged on failure.

`LcmdCopyPropagate.rewriteOperand` performs the same fold for the mnemonics of
`LcmdCopyPropagate.isImmFoldable`, which does not list `SET<cc>`.

## Semantics

The preservation theorem is stated over `LprogCmovTestElim.fsem`, the
flag-extended fold the sibling passes use, and relates the two runs by
`LprogCmovTestElim.FinalRel liveOut`: both stuck, or both finished with equal
memory and equal words in every register of `liveOut` and every name outside
the register pool. The deleted move and the two comparison forms are
flag-silent-or-flag-clearing in the same way, so the zero flag is equal on both
sides throughout (`LprogCmovTestElim.Sim L true`).

## Main results

* `immFuseBody`, `immFuseFundef`, `immFuseLprog`: the pass.
* `fstep_movImm`, `fstep_lvm_of_ne`: the flag-extended step of a constant move,
  and that a single-register write leaves every other register alone.
* `movImm_step`, `immSet_step`: the deletion of the move and the rewrite of the
  comparison, each from related states to related states.
* `immGo_sound`, `immFuseBody_sound`, `immFuseFundef_sound`: the pass preserves
  memory and the live-out registers.
* `immCmovFuseLprog`: the pass followed by `LprogCmovTestElim.cmpFuseFundef` and
  `LprogCmovTestElim.cmovTestElimFundef` on every function of an `Lprog`, and
  `immCmovFuse_sound`: that composition preserves memory and the live-out
  registers.
* `combSelectImmAsmN`, `combSelectImmLines`, `combSelectImmClean`,
  `combSelectImmHasCmov`: the comb-select rendering through that composition,
  its line count, the absence of an `UNHANDLED` sentinel and the presence of a
  `cmov` mnemonic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SelectImmCompare

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP physGPs instrUses fullDefsOf LiveAgree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCmovTestElim

/-! ## 1. Instruction shapes -/

/-- `Lopn [z] MOV:64 [.imm k]`: the destination and the constant. -/
def movImm? : LinstrR → Option (String × Nat)
  | .Lopn [.reg z] opn [.imm k] => if opn = movMn then some (z, k) else none
  | _ => none

/-- `Lopn [b] SET<cc>:64 [.reg x, .reg z]` on the register `z`: the sense, the
    destination and the first compared register. -/
def setImmHead? (z : String) (i : LinstrR) : Option (Bool × String × String) :=
  match cmpHead? i with
  | some (ne, b, .reg x, .reg y) =>
      if y == z && x != z && isPhysGP b then some (ne, b, x) else none
  | _ => none

/-- Lookahead for a constant move into `z`: a comparison against `z` is reached
    before any other read or write of `z`. -/
def immWorth (z : String) : Lcmd → Bool
  | [] => false
  | k :: rest =>
      if (setImmHead? z k.li_i).isSome then true
      else
        match k.li_i with
        | .Lopn dsts opn srcs =>
            if (instrUses dsts opn srcs).contains z then false
            else if (fullDefsOf dsts opn).contains z then false
            else immWorth z rest
        | _ => false

/-- The constant move the sweep deletes: a `MOV:64` of an immediate into a pool
    register, with no carry in flight and a comparison against it ahead. -/
def immStart? (cur : Option (String × Nat)) (i : LinstrR) (rest : Lcmd) :
    Option (String × Nat) :=
  match cur with
  | none =>
      match movImm? i with
      | some (z, k) => if isPhysGP z && immWorth z rest then some (z, k) else none
      | none => none
  | some _ => none

/-- The comparison the sweep rewrites: a comparison against the carried
    register whose first operand is in the agreement set. -/
def immSet? (L : List String) (cur : Option (String × Nat)) (i : LinstrR) :
    Option (Bool × String × String × Nat) :=
  match cur with
  | some (z, k) =>
      match setImmHead? z i with
      | some (ne, b, x) => if L.contains x then some (ne, b, x, k) else none
      | none => none
  | none => none

/-- The carried constant after a kept instruction: kept across a
    single-register write of another register, dropped otherwise. -/
def nextImmCur (cur : Option (String × Nat)) (i : LinstrR) : Option (String × Nat) :=
  match cur, i with
  | some (z, k), .Lopn [.reg x] _ _ => if x != z then some (z, k) else none
  | _, _ => none

/-- The rewritten comparison `Lopn [b] SET<cc>:64 [.reg x, .imm k]`. -/
def setImmL (ii : Nat) (ne : Bool) (b x : String) (k : Nat) : Linstr :=
  ⟨ii, .Lopn [.reg b] (headMn ne) [.reg x, .imm k]⟩

/-- The sweep. `none` when a kept instruction reads a register outside the
    agreement set, or when the body ends with a register of `liveOut` outside
    it. -/
def immGo (liveOut : List String) :
    List String → Option (String × Nat) → Lcmd → Option Lcmd
  | L, _, [] => if liveOut.all L.contains then some [] else none
  | L, cur, k0 :: rest =>
      match immSet? L cur k0.li_i with
      | some (ne, b, x, k) =>
          (immGo liveOut (b :: L) none rest).map (setImmL k0.li_ii ne b x k :: ·)
      | none =>
        match immStart? cur k0.li_i rest with
        | some (z, k) => immGo liveOut (L.filter (· != z)) (some (z, k)) rest
        | none =>
          if keepOk L true k0.li_i then
            (immGo liveOut (nextL L k0.li_i) (nextImmCur cur k0.li_i) rest).map (k0 :: ·)
          else none

/-- The pass on one body, for the registers `liveOut` read after it. The body is
    returned unchanged when the sweep fails. -/
def immFuseBody (liveOut : List String) (body : Lcmd) : Lcmd :=
  (immGo liveOut physGPs none body).getD body

/-- The pass on one `Lfundef` (body only). -/
def immFuseFundef (liveOut : List String) (f : Lfundef) : Lfundef :=
  { f with lfd_body := immFuseBody liveOut f.lfd_body }

/-- The pass on every function body of an `Lprog`, for the result registers of
    each function. -/
def immFuseLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) => (n, immFuseFundef f.lfd_res f) }

/-! ## 2. The two rewritten steps -/

/-- The constant move in the flag-extended step: it writes the constant and
    keeps the zero flag. -/
theorem fstep_movImm {w : Nat} (z : String) (k : Nat) (x : FState w) :
    fstep (.Lopn [.reg z] movMn [.imm k]) x =
      some ⟨(x.st.setReg z (BitVec.ofNat w k)).nextPc, x.zf⟩ := by
  simp [fstep, cmovArgs?, testArgs?, cmpArgs?, cmovccArgs?, lsemStep, applyOpn,
    stripWidthTag_movMn, evalOperand, flagSilentInstr, isFlagSilent_movMn]

/-- A step of a single-register write leaves every other register unchanged. -/
theorem fstep_lvm_of_ne {w : Nat} {r opn : String} {srcs : List LOperand}
    {x x' : FState w} {z : String} (h : fstep (.Lopn [.reg r] opn srcs) x = some x')
    (hne : z ≠ r) : x'.st.lvm z = x.st.lvm z := by
  unfold fstep at h
  split at h
  · rename_i d c t f hc
    have hs := cmovArgs?_spec hc
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at hs
    obtain ⟨⟨hrd, -⟩, -, -⟩ := hs
    cases h
    simp [Lstate.setReg, hrd ▸ hne]
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · split at h
        · rename_i ne d a b hc
          have hs := cmovccArgs?_spec hc
          obtain ⟨mn, hs⟩ := hs
          simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at hs
          obtain ⟨⟨hrd, -⟩, -, -⟩ := hs
          split at h
          · cases h; simp [Lstate.setReg, hrd ▸ hne]
          · cases h
        · rcases hl : lsemStep (.Lopn [.reg r] opn srcs) x.st with _ | s'
          · rw [hl] at h; cases h
          · rw [hl] at h
            cases h
            exact lsemStep_lvm_of_ne hl hne

/-- The original state holds the carried constant in the carried register. -/
def ImmFact {w : Nat} (cur : Option (String × Nat)) (o : FState w) : Prop :=
  ∀ z k, cur = some (z, k) → o.st.lvm z = BitVec.ofNat w k

/-- **The deleted constant move.** The original body writes the constant to `z`;
    the rewritten body does not step, and `z` leaves the agreement set. -/
theorem movImm_step {w : Nat} {L : List String} {o n : FState w} (hs : Sim L true o n)
    {z : String} (hz : isPhysGP z = true) (k : Nat) :
    ∃ o', fstep (.Lopn [.reg z] movMn [.imm k]) o = some o' ∧
      Sim (L.filter (· != z)) true o' n ∧ ImmFact (some (z, k)) o' := by
  refine ⟨_, fstep_movImm z k o, ⟨?_, ?_⟩, ?_⟩
  · have := LiveAgree.setReg_left hs.1 (b := z) hz (BitVec.ofNat w k)
    exact ⟨this.1, this.2⟩
  · intro _; exact hs.2 rfl
  · intro z' k' hc
    cases hc
    simp [Lstate.setReg]

/-- **The rewritten comparison.** From the carried constant, the comparison
    against the carried register and the comparison against the immediate write
    the same word and leave the same flag. -/
theorem immSet_step {w : Nat} {L : List String} {o n : FState w} (hs : Sim L true o n)
    (ii : Nat) (ne : Bool) {b x z : String} {k : Nat} (hf : ImmFact (some (z, k)) o)
    (hx : L.contains x = true) :
    ∃ o' n', fstep (.Lopn [.reg b] (headMn ne) [.reg x, .reg z]) o = some o' ∧
      fstep (setImmL ii ne b x k).li_i n = some n' ∧ Sim (b :: L) true o' n' := by
  refine ⟨_, _, fstep_head ne b x (.reg z) o, fstep_head ne b x (.imm k) n, ?_, ?_⟩
  · have hxv : o.st.lvm x = n.st.lvm x := hs.1.2 x (Or.inr hx)
    have hzv : evalOperand o.st (.reg z) = evalOperand n.st (.imm k) := hf z k rfl
    rw [hxv, hzv]
    exact LiveAgree.setReg_both hs.1 b _
  · intro _; rfl

/-- The carried constant stays correct across a kept instruction. -/
theorem immFact_keep {w : Nat} {cur : Option (String × Nat)} {i : LinstrR} {o o' : FState w}
    (hf : ImmFact cur o) (ho : fstep i o = some o') : ImmFact (nextImmCur cur i) o' := by
  intro z k hc
  unfold nextImmCur at hc
  split at hc
  · rename_i z0 k0 r opn srcs
    split_ifs at hc with hne
    cases hc
    simp only [bne_iff_ne, ne_eq] at hne
    rw [fstep_lvm_of_ne ho (Ne.symm hne)]
    exact hf z k rfl
  · cases hc

/-! ## 3. The sweep -/

/-- `movImm?` recognises exactly the constant-move shape. -/
theorem movImm?_spec {i : LinstrR} {z : String} {k : Nat} (h : movImm? i = some (z, k)) :
    i = .Lopn [.reg z] movMn [.imm k] := by
  unfold movImm? at h
  split at h
  · split_ifs at h with hop
    cases h
    rw [hop]
  · cases h

/-- `setImmHead?` recognises a comparison whose second operand is the given
    register. -/
theorem setImmHead?_spec {z : String} {i : LinstrR} {ne : Bool} {b x : String}
    (h : setImmHead? z i = some (ne, b, x)) :
    i = .Lopn [.reg b] (headMn ne) [.reg x, .reg z] := by
  unfold setImmHead? at h
  split at h
  · rename_i ne' b' x' y' hc
    split_ifs at h with hg
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨⟨hy, -⟩, -⟩ := hg
    rw [cmpHead?_spec hc, hy]
  · cases h

/-- `immStart?` recognises a constant move into a pool register. -/
theorem immStart?_spec {cur : Option (String × Nat)} {i : LinstrR} {rest : Lcmd}
    {z : String} {k : Nat} (h : immStart? cur i rest = some (z, k)) :
    cur = none ∧ i = .Lopn [.reg z] movMn [.imm k] ∧ isPhysGP z = true := by
  unfold immStart? at h
  split at h
  · split at h
    · rename_i z' k' hm
      split_ifs at h with hg
      cases h
      simp only [Bool.and_eq_true] at hg
      exact ⟨rfl, movImm?_spec hm, hg.1⟩
    · cases h
  · cases h

/-- `immSet?` recognises a comparison against the carried register. -/
theorem immSet?_spec {L : List String} {cur : Option (String × Nat)} {i : LinstrR}
    {ne : Bool} {b x : String} {k : Nat} (h : immSet? L cur i = some (ne, b, x, k)) :
    ∃ z, cur = some (z, k) ∧ i = .Lopn [.reg b] (headMn ne) [.reg x, .reg z] ∧
      L.contains x = true := by
  unfold immSet? at h
  split at h
  · rename_i z k0
    split at h
    · rename_i ne' b' x' hc
      split_ifs at h with hg
      cases h
      exact ⟨z, rfl, setImmHead?_spec hc, hg⟩
    · cases h
  · cases h

/-- **The sweep relates the two runs.** From related states in which the carried
    constant holds, the body the sweep returns and the original body are both
    stuck, or finish in states agreeing on memory and on `liveOut`. -/
theorem immGo_sound {w : Nat} (liveOut : List String) :
    ∀ (body : Lcmd) (L : List String) (cur : Option (String × Nat)) (out : Lcmd)
      (o n : FState w),
      immGo liveOut L cur body = some out → Sim L true o n → ImmFact cur o →
      FinalRel liveOut (fsem (body.map Linstr.li_i) o) (fsem (out.map Linstr.li_i) n)
  | [], L, cur, out, o, n, hgo, hs, _ => by
      simp only [immGo] at hgo
      split_ifs at hgo with hall
      cases hgo
      simp only [List.all_eq_true] at hall
      exact LiveAgree.mono hs.1 fun r hr => hall r (by simpa using hr)
  | k0 :: rest, L, cur, out, o, n, hgo, hs, hf => by
      simp only [immGo] at hgo
      cases hset : immSet? L cur k0.li_i with
      | some q =>
        obtain ⟨ne, b, x, k⟩ := q
        rw [hset] at hgo
        simp only [Option.map_eq_some_iff] at hgo
        obtain ⟨out', hgo', rfl⟩ := hgo
        obtain ⟨z, hcur, hk, hx⟩ := immSet?_spec hset
        subst hcur
        obtain ⟨o', n', ho, hn, hs'⟩ := immSet_step hs k0.li_ii ne hf hx
        simp only [List.map_cons, fsem, hk]
        rw [ho, hn]
        exact immGo_sound liveOut rest _ _ _ _ _ hgo' hs' (fun _ _ h => by cases h)
      | none =>
        rw [hset] at hgo
        cases hst : immStart? cur k0.li_i rest with
        | some q =>
          obtain ⟨z, k⟩ := q
          rw [hst] at hgo
          obtain ⟨-, hk, hz⟩ := immStart?_spec hst
          obtain ⟨o', ho, hs', hf'⟩ := movImm_step hs hz k
          simp only [List.map_cons, fsem, hk, ho]
          exact immGo_sound liveOut rest _ _ _ _ _ hgo hs' hf'
        | none =>
          rw [hst] at hgo
          split_ifs at hgo with hkeep
          simp only [Option.map_eq_some_iff] at hgo
          obtain ⟨out', hgo', rfl⟩ := hgo
          rcases keep_step hs hkeep with ⟨ho, hn⟩ | ⟨o', n', ho, hn, hs'⟩
          · simp only [List.map_cons, fsem, ho, hn]
            trivial
          · simp only [List.map_cons, fsem, ho, hn]
            exact immGo_sound liveOut rest _ _ _ _ _ hgo' hs' (immFact_keep hf ho)

/-- **The pass preserves memory and the live-out registers.** On every body and
    every start state, the rewritten body and the original body are both stuck
    under `fsem`, or both finish with equal memory and equal words in every
    register of `liveOut` and in every name outside the register pool. -/
theorem immFuseBody_sound {w : Nat} (liveOut : List String) (body : Lcmd) (x : FState w) :
    FinalRel liveOut (fsem (body.map Linstr.li_i) x)
      (fsem ((immFuseBody liveOut body).map Linstr.li_i) x) := by
  unfold immFuseBody
  cases hgo : immGo liveOut physGPs none body with
  | none => exact FinalRel.refl _ _
  | some out =>
    exact immGo_sound liveOut body _ _ _ x x hgo ⟨LiveAgree.refl _ _, fun _ => rfl⟩
      (fun _ _ h => by cases h)

/-- The pass on one `Lfundef` preserves memory and the live-out registers of its
    body. -/
theorem immFuseFundef_sound {w : Nat} (liveOut : List String) (f : Lfundef) (x : FState w) :
    FinalRel liveOut (fsem (f.lfd_body.map Linstr.li_i) x)
      (fsem ((immFuseFundef liveOut f).lfd_body.map Linstr.li_i) x) :=
  immFuseBody_sound liveOut f.lfd_body x

/-! ## 4. The comb-select pipeline through the in-place comparison -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront

/-- The constant fold, the comparison fusion and the shared-test rewrite on
    every function of an `Lprog`, for the result registers of each function. -/
def immCmovFuseLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) =>
      (n, cmovTestElimFundef (cmpFuseFundef f.lfd_res (immFuseFundef f.lfd_res f))) }

/-- Agreement on memory and on the registers of `L` is transitive. -/
theorem LiveAgree.trans' {w : Nat} {L : List String} {s t u : Lstate w}
    (h1 : LiveAgree L s t) (h2 : LiveAgree L t u) : LiveAgree L s u :=
  ⟨h1.1.trans h2.1, fun r hr => (h1.2 r hr).trans (h2.2 r hr)⟩

/-- The relation of two runs is transitive. -/
theorem FinalRel.trans' {w : Nat} {liveOut : List String} {a b c : Option (FState w)}
    (h1 : FinalRel liveOut a b) (h2 : FinalRel liveOut b c) : FinalRel liveOut a c := by
  cases a <;> cases b <;> cases c <;> first
    | exact LiveAgree.trans' h1 h2
    | exact h1.elim
    | exact h2.elim
    | trivial

/-- Equal observed states give the relation of two runs. -/
theorem finalRel_of_fview {w : Nat} (liveOut : List String) {a b : Option (FState w)}
    (h : Option.map fview a = Option.map fview b) : FinalRel liveOut a b := by
  cases a <;> cases b <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h
  · trivial
  · obtain ⟨hs, -⟩ : (_ : (_ × _)) = _ ∧ _ := Prod.mk.injEq _ _ _ _ ▸ h
    obtain ⟨hv, hm⟩ := Prod.mk.injEq _ _ _ _ ▸ hs
    exact ⟨hm, fun r _ => congrFun hv r⟩

/-- **The composition preserves memory and the live-out registers.** On every
    body and every start state, the body after the constant fold, the comparison
    fusion and the shared-test rewrite, and the original body, are both stuck
    under `fsem`, or both finish with equal memory and equal words in every
    register of `liveOut` and in every name outside the register pool. -/
theorem immCmovFuse_sound {w : Nat} (liveOut : List String) (f : Lfundef) (x : FState w) :
    FinalRel liveOut (fsem (f.lfd_body.map Linstr.li_i) x)
      (fsem ((cmovTestElimFundef (cmpFuseFundef liveOut (immFuseFundef liveOut f))).lfd_body.map
        Linstr.li_i) x) :=
  FinalRel.trans' (immFuseFundef_sound liveOut f x)
    (FinalRel.trans' (cmpFuseFundef_sound liveOut (immFuseFundef liveOut f) x)
      (finalRel_of_fview liveOut
        (cmovTestElimFundef_fview (cmpFuseFundef liveOut (immFuseFundef liveOut f)) x).symm))

/-- `CombSelectCmovFront.combSelectCmovCoalescedLprog` after
    `immCmovFuseLprog`: the body the printer receives. -/
def combSelectImmFusedLprog (name : String) (N : Nat) : Option Lprog :=
  (combSelectCmovCoalescedLprog name N).map immCmovFuseLprog

/-- The owned AT&T rendering of `combSelectImmFusedLprog`. -/
def combSelectImmAsmN (name : String) (N : Nat) : Option String :=
  (combSelectImmFusedLprog name N).map (fun p => LprogAsmPrinter.renderLprogAtt p)

/-- The line count of the rendered `N`-entry select. -/
def combSelectImmLines (N : Nat) : Option Nat :=
  (combSelectImmAsmN "ed25519_comb_select_cmov_x86_from_lean" N).map
    LprogCopyCoalesce.lineCount

/-- The rendered `N`-entry select exists and has no `UNHANDLED` sentinel. -/
def combSelectImmClean (N : Nat) : Bool :=
  match combSelectImmAsmN "ed25519_comb_select_cmov_x86_from_lean" N with
  | some t => !LprogCopyCoalesce.hasUnhandled t
  | none => false

/-- The rendered `N`-entry select contains a `cmov` mnemonic. -/
def combSelectImmHasCmov (N : Nat) : Bool :=
  match combSelectImmAsmN "ed25519_comb_select_cmov_x86_from_lean" N with
  | some t => (t.splitOn "cmov").length != 1
  | none => false

/-- The number of `cmpq $` lines of the rendered `N`-entry select: the
    comparisons against an immediate. -/
def combSelectImmCmpImm (N : Nat) : Nat :=
  match combSelectImmAsmN "ed25519_comb_select_cmov_x86_from_lean" N with
  | some t => (t.splitOn "cmpq $").length - 1
  | none => 0

/-! ## 5. Static pins of the rule set

The `#guard`s pin the shape the sweep returns on a three-instruction body in
the shape of a comb-select entry: a constant move, the comparison reading it
and one select. They are static checks of the rule set, evaluated at
elaboration on a list of three instructions. -/

/-- A zero materialised into `RCX`, an equality comparison of `R9` against it
    into `RDX`, and a select on that result. -/
def pinImm : Lcmd :=
  [ ⟨0, .Lopn [.reg "RCX"] movMn [.imm 0]⟩
  , ⟨0, .Lopn [.reg "RDX"] seteMn [.reg "R9", .reg "RCX"]⟩
  , ⟨0, .Lopn [.reg "RAX"] cmovMn [.reg "RDX", .reg "RBX", .reg "RAX"]⟩ ]

/-- The number of instructions of a body whose second source is an
    immediate. -/
def countImmSrc (mn : String) (b : Lcmd) : Nat :=
  b.countP fun k => match k.li_i with
    | .Lopn _ opn [_, .imm _] => opn == mn
    | _ => false

/- With `RCX` dead after the body, the constant move is deleted and the
   comparison reads the immediate. With `RCX` live after the body, the body is
   unchanged. -/
#guard countMn movMn (immFuseBody ["RAX"] pinImm) == 0
#guard countImmSrc seteMn (immFuseBody ["RAX"] pinImm) == 1
#guard (immFuseBody ["RAX"] pinImm).length == 2
#guard countMn movMn (immFuseBody ["RAX", "RCX"] pinImm) == 1
#guard countImmSrc seteMn (immFuseBody ["RAX", "RCX"] pinImm) == 0

end CatCrypt.Crypto.SecureCompilation.X86Backend.SelectImmCompare
