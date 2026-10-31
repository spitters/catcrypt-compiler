/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower

/-!
# The compare reload on bodies with `R15` brackets

The side condition `CmpSpillReload.cmpReloadOK` of the compare reload accepts a body only if
no instruction names the reload scratch `R15` and no instruction is a `MULX`. A body fused by
`FuseMulHi` holds brackets `MOV R15, RDX … MULX:64 … MOV RDX, R15`, which name `R15` and use
`MULX`; `R15` is dead outside these brackets.

This module defines the decided check `cmpReloadBrOK` for such bodies and the per-step facts
of its simulation. The check scans the body with an in-bracket flag: a copy into `R15`
(`opensBracket`) sets it, a control instruction or a compare on a spilled first operand resets it.
Inside a bracket every instruction is accepted, and the source and target states are equal up
to the program counter (`EqPc`). Outside a bracket an instruction names no `R15` and is no
`MULX`, and the states agree outside the register `R15` (`AgreeL`).

## Main definitions

* `opensBracket`: a register copy into `R15` from another register.
* `brStep`, `brOKI`, `brScan`, `cmpReloadBrOK`: the flag update, the per-instruction check,
  the scan and the check on a body.
* `syncAt`: the flag of the scan before position `k`.
* `AgreeL`: `JasminLsemFuseMulHi.Agree` together with equality of the array `R15`.

## Main results

* `brScan_sound`: a passing scan yields `brOKI` at every position, at the flag `syncAt`.
* `fstepF_replay`: a step of any instruction, a `MULX` included, is replayed on a state equal
  up to the program counter.
* `fstepF_opensBracket`: a copy into `R15` stepped from `AgreeL`-related states reaches states equal
  up to the program counter.
* `reload_agreeL`: the reload of a compare on a spilled first operand keeps `AgreeL` and the
  zero flag.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracket

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (Agree KeptN clsB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames mulxFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (typeBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

/-! ## The check -/

/-- The wire names no `R15`. -/
def noR15 (w : LinstrR) : Bool := (instrNames w).all (fun n => n != "R15")

/-- **A copy into `R15`**: `Lopn [R15] opn [s]` with a register `s` other than `R15` and a
    copy mnemonic (stripping to `MOV`, or a `copyQ` mnemonic). -/
def opensBracket (w : LinstrR) : Bool :=
  match w with
  | .Lopn [.reg d] opn [.reg s] =>
      d == "R15" && s != "R15" && (stripWidthTag opn == "MOV" || copyQ opn)
  | _ => false

/-- **The in-bracket flag after an instruction**: reset at a control instruction and at a
    compare on a spilled first operand, set at a copy into `R15`, kept otherwise. -/
def brStep (_tag : LinstrR → MemTag) (sy : Bool) (w : LinstrR) : Bool :=
  match w with
  | .Lopn _ _ _ => if (spillCmp? w).isSome then false else opensBracket w || sy
  | _ => false

/-- **The check of one instruction at the in-bracket flag `sy`**: the instruction is in the
    classes of the simulation (`clsB`); a compare on a spilled first operand is the flag
    compare and names no `R15`; any other instruction is a copy into `R15`, lies inside a
    bracket, or names no `R15` and is no `MULX`. -/
def brOKI (tag : LinstrR → MemTag) (sy : Bool) (w : LinstrR) : Bool :=
  clsB (w, tag w) &&
    match spillCmp? w with
    | some (opn, _, _) => opn == withWidthTag 64 "CMP" && noR15 w
    | none => opensBracket w || sy || (noR15 w && mulxFree (w, tag w))

/-- **The scan of a body** from the flag `sy`: `brOKI` at each instruction, threading
    `brStep`. -/
def brScan (tag : LinstrR → MemTag) : Bool → Lcmd → Bool
  | _, [] => true
  | sy, i :: is => brOKI tag sy i.li_i && brScan tag (brStep tag sy i.li_i) is

/-- **The check of the compare reload on a body with `R15` brackets**: the scan from outside
    a bracket. -/
def cmpReloadBrOK (tag : LinstrR → MemTag) (body : Lcmd) : Bool := brScan tag false body

/-- The in-bracket flag of the scan from `sy` before position `k` of `body`. -/
def syncAt (tag : LinstrR → MemTag) (sy : Bool) (body : Lcmd) (k : Nat) : Bool :=
  (body.take k).foldl (fun s i => brStep tag s i.li_i) sy

@[simp] theorem syncAt_zero (tag : LinstrR → MemTag) (sy : Bool) (body : Lcmd) :
    syncAt tag sy body 0 = sy := by
  simp [syncAt]

/-- The flag after position `k` is `brStep` of the flag before it. -/
theorem syncAt_succ (tag : LinstrR → MemTag) (sy : Bool) {body : Lcmd} {k : Nat} {i : Linstr}
    (h : body[k]? = some i) :
    syncAt tag sy body (k + 1) = brStep tag (syncAt tag sy body k) i.li_i := by
  simp [syncAt, List.take_add_one, h, List.foldl_append]

theorem syncAt_cons_succ (tag : LinstrR → MemTag) (sy : Bool) (i : Linstr) (body : Lcmd)
    (k : Nat) : syncAt tag sy (i :: body) (k + 1) = syncAt tag (brStep tag sy i.li_i) body k := by
  simp [syncAt]

/-- **The scan is sound**: a passing scan from `sy` yields `brOKI` at every position `k`, at
    the flag `syncAt tag sy body k`. -/
theorem brScan_sound {tag : LinstrR → MemTag} :
    ∀ {sy : Bool} {body : Lcmd}, brScan tag sy body = true →
      ∀ (k : Nat) (i : Linstr), body[k]? = some i → brOKI tag (syncAt tag sy body k) i.li_i = true
  | _, [], _, k, i, hk => by simp at hk
  | sy, j :: js, h, k, i, hk => by
      simp only [brScan, Bool.and_eq_true] at h
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          simpa using h.1
      | succ k =>
          rw [syncAt_cons_succ]
          exact brScan_sound h.2 k i (by simpa using hk)

/-- **The scan on the typed body**: at position `k` of `typeBody tag body` stands the typed
    wire `(w, tag w)`, and `brOKI` holds at `w` and the flag `syncAt tag sy body k`. -/
theorem brScan_sound_typeBody {tag : LinstrR → MemTag} {sy : Bool} {body : Lcmd}
    (h : brScan tag sy body = true) {k : Nat} {i : LinstrRM}
    (hk : (typeBody tag body)[k]? = some i) :
    i = (i.1, tag i.1) ∧ brOKI tag (syncAt tag sy body k) i.1 = true := by
  simp only [typeBody, List.getElem?_map] at hk
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hk
  exact ⟨rfl, brScan_sound h k j hj⟩

/-- **The facts of the per-instruction check.** -/
theorem brOKI_spec {tag : LinstrR → MemTag} {sy : Bool} {w : LinstrR}
    (h : brOKI tag sy w = true) :
    clsB (w, tag w) = true
      ∧ (∀ opn d s, spillCmp? w = some (opn, d, s) →
          opn = withWidthTag 64 "CMP" ∧ ∀ n ∈ instrNames w, KeptN n)
      ∧ (spillCmp? w = none →
          opensBracket w = true ∨ sy = true ∨
            ((∀ n ∈ instrNames w, KeptN n) ∧ mulxFree (w, tag w))) := by
  unfold brOKI at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hc, hm⟩ := h
  refine ⟨hc, fun opn d s hs => ?_, fun hs => ?_⟩
  · rw [hs] at hm
    simp only [Bool.and_eq_true, beq_iff_eq, noR15, List.all_eq_true, bne_iff_ne, ne_eq] at hm
    exact ⟨hm.1, hm.2⟩
  · rw [hs] at hm
    simp only [Bool.or_eq_true, Bool.and_eq_true, noR15, List.all_eq_true, bne_iff_ne,
      ne_eq] at hm
    rcases hm with (h1 | h2) | ⟨h3, h4⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h3, h4⟩)

/-! ## The relations -/

/-- Two bases agree outside the register `R15` (`Agree`), and their arrays `R15` are equal. -/
structure AgreeL (s s' : LstateM) : Prop where
  /-- The bases agree outside `R15`. -/
  agree : Agree s s'
  /-- The arrays `R15` are equal. -/
  r15 : s'.larr "R15" = s.larr "R15"

theorem AgreeL.refl (s : LstateM) : AgreeL s s := ⟨Agree.refl s, rfl⟩

theorem AgreeL.setLpc {a b : LstateM} (h : AgreeL a b) (p q : Nat) :
    AgreeL (a.setLpc p) (b.setLpc q) := ⟨h.agree.setLpc p q, h.r15⟩

/-- Two bases equal up to the program counter are `AgreeL`-related. -/
theorem AgreeL.of_eqPc {a b : LstateM} (h : EqPc a b) : AgreeL a b := by
  unfold EqPc at h
  rw [h]
  exact ⟨⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Two `AgreeL`-related bases with equal registers `R15` are equal up to the program
    counter. -/
theorem eqPc_of_agreeL {a b : LstateM} (h : AgreeL a b)
    (h15 : b.reg.lvm "R15" = a.reg.lvm "R15") : EqPc a b := by
  have hreg : b.reg.lvm = a.reg.lvm := funext fun r => by
    by_cases hr : r = "R15"
    · subst hr; exact h15
    · exact h.agree.reg r hr
  have harr : b.larr = a.larr := funext fun r => by
    by_cases hr : r = "R15"
    · subst hr; exact h.r15
    · exact h.agree.arr r hr
  have hm := h.agree.mem
  have hc := h.agree.cf
  have ho := h.agree.of
  obtain ⟨⟨bl, bp⟩, ba, bm, bc, bo⟩ := b
  obtain ⟨⟨al, ap⟩, aa, am, ac, ao⟩ := a
  simp only at hreg harr hm hc ho
  subst hreg harr hm hc ho
  rfl

/-! ## The steps -/

/-- **A step replayed up to the program counter.** A step of any instruction from a base is
    matched by a step of the same instruction from every base equal to it up to the program
    counter, with the same zero flag and results equal up to the program counter. No `MULX`
    side condition is needed. -/
theorem fstepF_replay (i : LinstrRM) {s s' t : LstateM} {zf zt : Bool} (hE : EqPc s s')
    (h : fstepF i s zf = some (t, zt)) :
    ∃ t', fstepF i s' zf = some (t', zt) ∧ EqPc t t' := by
  unfold EqPc at hE
  rw [hE, fstepF_setLpc, h]
  exact ⟨_, rfl, EqPc.refl_setLpc _ _⟩

/-- **The opening copy of a bracket.** A copy into `R15` stepped from `AgreeL`-related bases
    reaches bases equal up to the program counter, with the same zero flag. -/
theorem fstepF_opensBracket {w : LinstrR} (hw : opensBracket w = true) (tg : MemTag)
    {a a' t : LstateM} {zf zt : Bool} (hA : AgreeL a a') (h : fstepF (w, tg) a zf = some (t, zt)) :
    ∃ t', fstepF (w, tg) a' zf = some (t', zt) ∧ EqPc t t' := by
  unfold opensBracket at hw
  split at hw
  · rename_i d opn s
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true] at hw
    obtain ⟨⟨rfl, hs⟩, hm⟩ := hw
    rw [fstepF_copyWire _ _ _ _ hm] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, fstepF_copyWire _ _ _ _ hm a' zf, ?_⟩
    rw [hA.agree.reg s hs]
    refine eqPc_of_agreeL ⟨⟨fun r hr => ?_, fun r hr => hA.agree.arr r hr, hA.agree.mem,
      hA.agree.cf, hA.agree.of⟩, hA.r15⟩ ?_
    · have hr' : r ≠ "R15" := hr
      simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, hr', hA.agree.reg r hr]
    · simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc]
  · cases hw

/-- A flag compare steps to the advanced base. -/
theorem fstepF_eq_nextPc_of_cmpArgs {i : LinstrRM} {p : LOperand × LOperand}
    (hc : cmpArgs? i = some p) {s t : LstateM} {zf zt : Bool}
    (h : fstepF i s zf = some (t, zt)) : t = s.nextPc := by
  obtain ⟨x, y⟩ := p
  unfold fstepF at h
  rw [hc] at h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  · cases h

/-- **The reload of a spilled compare at `AgreeL`.** When the flag compare `CMP d, s` steps
    from a base, the pair `MOV R15, d ; CMP R15, s` runs from every `AgreeL`-related base to
    an `AgreeL`-related base, with the same zero flag, provided neither `d` nor `s` names
    `R15`. -/
theorem reload_agreeL (d : String) (s : LOperand) (tg t1 t2 : MemTag)
    (hd : KeptN d) (hs : ∀ n ∈ opNames s, KeptN n) {a a' t : LstateM} {zf zt : Bool}
    (hA : AgreeL a a')
    (h : fstepF (.Lopn [.reg d] (withWidthTag 64 "CMP") [.reg d, s], tg) a zf = some (t, zt)) :
    ∃ t', runStraightF
        [(.Lopn [.reg reloadScratch] (movOf (withWidthTag 64 "CMP")) [.reg d], t1),
         (.Lopn [.reg reloadScratch] (withWidthTag 64 "CMP") [.reg reloadScratch, s], t2)] a' zf
        = some (t', zt) ∧ AgreeL t t' := by
  obtain ⟨t', hrun, hAg⟩ := fstepF_cmpReload d s tg t1 t2 hd hs hA.agree h
  refine ⟨t', hrun, hAg, ?_⟩
  have ht : t = a.nextPc :=
    fstepF_eq_nextPc_of_cmpArgs (p := (.reg d, s)) (by simp [cmpArgs?]) h
  have hmv := fstepF_movWire reloadScratch d _ t1 movOf_cmp64 a' zf
  unfold movWire at hmv
  rw [runStraightF_cons, hmv, Option.bind_some, runStraightF_cons] at hrun
  obtain ⟨⟨u, zu⟩, hu, hr⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have hu' := fstepF_eq_nextPc_of_cmpArgs (p := (.reg reloadScratch, s))
    (by simp [cmpArgs?]) hu
  rw [hu', ht]
  exact hA.r15

end CatCrypt.Crypto.SecureCompilation.Haxc.CmpReloadBracket
