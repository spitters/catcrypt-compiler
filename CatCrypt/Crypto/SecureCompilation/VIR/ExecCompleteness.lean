/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
public import CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy


@[expose] public section
set_option autoImplicit false

/-!
# Completeness + full adequacy: the fuel-bounded executor exactly characterises
the reference relational semantics

`ExecAdequacy.lean` proved **soundness** (`execInstrR … = .ok s' → SemIr … s i s'`):
a successful executor run witnesses the reference relational big-step judgement
(the mechanical port of Coq `psem.v`'s `Inductive sem … with sem_I … with sem_i …
with sem_for … with sem_call`).

This file proves the **converse direction, completeness**:

  `SemIr … s i s' → ∃ fuel, execInstrR … fuel s i prog = .ok s'`

and the analogues for `Sem`/`SemI`/`SemFor`/`SemCall`. Together with soundness
this gives **full adequacy**: the fuel-bounded executor *exactly* characterises
the reference relational semantics (the ∃-fuel form `… = .ok s' ↔ SemIr …`).

## Proof architecture

Completeness needs two ingredients:

1. **Fuel monotonicity** (§2, the main lemma). The executor's result is preserved
   when fuel grows:

     `execInstrR … fuel s i prog = .ok s' → execInstrR … (fuel+1) s i prog = .ok s'`

   (and the `execInstr`/`execCmd`/`execFor`/`execCall` analogues). This is what
   lets the derivation-induction take the `max` of the sub-derivations' fuels and
   lift every sub-run to that common bound. The five entry points recurse on a
   shared fuel, so monotonicity is proved as one **single-step** bundle
   (`monoStepAt n : execX n = .ok → execX (n+1) = .ok`) by strong induction on
   `n`, then iterated to the `≤` form (`execInstrR_mono` etc.).

2. **Derivation-tree induction** (§3). Completeness is proved by mutual induction
   on the `Sem`/`SemI`/`SemIr`/`SemFor`/`SemCall` derivation (Lean generates a
   joint recursor for the mutual inductive block). Each constructor hands us its
   sub-derivations' `∃ fuel_k` witnesses; we take `fuel = max … + 1`, use
   monotonicity to lift each sub-run to that common fuel, and the executor's own
   branch returns `.ok` by its `_eq` characterisation (the `OpSemCoverage` /
   `CifLowering` / `WhileLowering` / `CallLowering` / `CmdRun` lemmas, reused
   in the forward direction here).

## Constructor coverage (honest)

**All constructors of all five judgements are covered.** Concretely:

| Judgement | Constructors | Status |
|---|---|---|
| `Sem`     | `Eskip`, `Eseq`                              | both covered |
| `SemI`    | `EmkI`                                        | covered |
| `SemIr`   | `Eassgn`,`Eopn`,`Eif_true`,`Eif_false`,`Ewhile_true`,`Ewhile_false`,`Efor`,`Ecall` | all covered |
| `SemFor`  | `EForDone`, `EForOne`                          | both covered |
| `SemCall` | `EcallRun`                                     | covered |

`SemIr` has **no** `Csyscall` constructor (the mirror's §6 omits it), so there is
nothing to prove there — faithful to soundness, where the `Csyscall` *executor*
branch is a deferral error that never returns `.ok`.

## What this establishes

The fuel-bounded functional executor and the reference relational big-step
semantics are **interderivable** (∃-fuel form). Any `#eval`/`native_decide` KAT
on `execCmd`/`execInstrR` witnesses a `psem.v` derivation (soundness), and every
`psem.v` derivation is *reachable* at some fuel by the executor (completeness).
That is full adequacy of the fuel-bounded executor against the ported reference
big-step semantics.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.ExecCompleteness

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR

variable {SyscallState Mem : Type} [MemModel Mem]
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-! ## §1. `JResult`-bind composition lemma

The forward (`bind`-building) companion of `ExecAdequacy.bind_eq_ok`: if `r`
succeeds with `a` and `f a` succeeds with `c`, the whole `bind` succeeds with
`c`. Each monotonicity / completeness step reassembles a `do`-block from the
successes of its parts; this is the one structural lemma that does it. -/

/-- `r = .ok a → f a = .ok c → JResult.bind r f = .ok c`. The forward direction
    of `bind_eq_ok`: assemble a successful `bind` from successful parts. -/
theorem bind_ok_of {α β : Type} {r : JResult α} {f : α → JResult β} {a : α} {c : β}
    (hr : r = .ok a) (hf : f a = .ok c) : JResult.bind r f = .ok c := by
  subst hr; exact hf

/-! ## §2. Fuel monotonicity (the main lemma)

The executor's result is preserved when fuel grows. We prove the **single-step**
bundle `monoStepAt n` (each entry point at fuel `n` succeeding implies it
succeeds at fuel `n+1`) by strong induction on `n`, because the five entry
points are mutually recursive on a shared fuel. The recursive branches at fuel
`n+1 = m+2` recurse at fuel `m+1`, and the single-step bundle at `m < n` lifts
those sub-runs from `m` to `m+1`. We then iterate to the general `≤` form. -/

/-- The five-way single-step monotonicity bundle at fuel `n`: each executor
    entry point that succeeds at fuel `n` also succeeds at fuel `n+1`. -/
def monoStepAt (n : Nat) : Prop :=
  (∀ (s s' : Estate SyscallState Mem) (i : InstrR),
      execInstrR (Mem := Mem) aS opS gd n s i prog = .ok s' →
      execInstrR (Mem := Mem) aS opS gd (n+1) s i prog = .ok s')
  ∧ (∀ (s s' : Estate SyscallState Mem) (i : Instr),
      execInstr (Mem := Mem) aS opS gd n s i prog = .ok s' →
      execInstr (Mem := Mem) aS opS gd (n+1) s i prog = .ok s')
  ∧ (∀ (s s' : Estate SyscallState Mem) (c : Cmd),
      execCmd (Mem := Mem) aS opS gd n s c prog = .ok s' →
      execCmd (Mem := Mem) aS opS gd (n+1) s c prog = .ok s')
  ∧ (∀ (v : VarI) (ws : List Int) (body : Cmd) (s s' : Estate SyscallState Mem),
      execFor (Mem := Mem) aS opS gd n v ws body s prog = .ok s' →
      execFor (Mem := Mem) aS opS gd (n+1) v ws body s prog = .ok s')
  ∧ (∀ (scs1 : SyscallState) (m1 : Mem) (fn : FunName) (vargs' : Values)
        (res : SyscallState × Mem × Values),
      execCall (Mem := Mem) aS opS gd n scs1 m1 fn vargs' prog = .ok res →
      execCall (Mem := Mem) aS opS gd (n+1) scs1 m1 fn vargs' prog = .ok res)

/-- **The single-step monotonicity bundle holds at every fuel.** Strong
    induction on `n`; the recursive executor branches at fuel `n+1` recurse at
    the strictly smaller fuel and are lifted by the bundle at that smaller fuel. -/
theorem monoStepAt_all (n : Nat) :
    monoStepAt (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have ihIr : ∀ m, m < n → ∀ (s s' : Estate SyscallState Mem) (i : InstrR),
        execInstrR (Mem := Mem) aS opS gd m s i prog = .ok s' →
        execInstrR (Mem := Mem) aS opS gd (m+1) s i prog = .ok s' :=
      fun m hm => (ih m hm).1
    have ihCmd : ∀ m, m < n → ∀ (s s' : Estate SyscallState Mem) (c : Cmd),
        execCmd (Mem := Mem) aS opS gd m s c prog = .ok s' →
        execCmd (Mem := Mem) aS opS gd (m+1) s c prog = .ok s' :=
      fun m hm => (ih m hm).2.2.1
    have ihFor : ∀ m, m < n → ∀ (v : VarI) (ws : List Int) (body : Cmd)
        (s s' : Estate SyscallState Mem),
        execFor (Mem := Mem) aS opS gd m v ws body s prog = .ok s' →
        execFor (Mem := Mem) aS opS gd (m+1) v ws body s prog = .ok s' :=
      fun m hm => (ih m hm).2.2.2.1
    have ihCall : ∀ m, m < n → ∀ (scs1 : SyscallState) (m1 : Mem) (fn : FunName)
        (vargs' : Values) (res : SyscallState × Mem × Values),
        execCall (Mem := Mem) aS opS gd m scs1 m1 fn vargs' prog = .ok res →
        execCall (Mem := Mem) aS opS gd (m+1) scs1 m1 fn vargs' prog = .ok res :=
      fun m hm => (ih m hm).2.2.2.2
    -- InstrR component.
    have hIr : ∀ (s s' : Estate SyscallState Mem) (i : InstrR),
        execInstrR (Mem := Mem) aS opS gd n s i prog = .ok s' →
        execInstrR (Mem := Mem) aS opS gd (n+1) s i prog = .ok s' := by
      cases n with
      | zero =>
        intro s s' i hexec
        rw [execInstrR] at hexec
        exact absurd hexec (by simp)
      | succ m =>
        have hlt : m < m + 1 := Nat.lt_succ_self m
        intro s s' i hexec
        cases i with
        | Cassgn lv tag ty e =>
          rw [OpSemCoverage.execInstrR_Cassgn_eq] at hexec ⊢
          exact hexec
        | Copn xs tag o es =>
          rw [OpSemCoverage.execInstrR_Copn_eq] at hexec ⊢
          exact hexec
        | Cif cond cthen celse =>
          rw [execInstrR] at hexec ⊢
          obtain ⟨vc, hsem, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨b, htb, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          refine bind_ok_of hsem (bind_ok_of htb ?_)
          cases b with
          | true => exact ihCmd m hlt s s' cthen (by simpa using hexec)
          | false => exact ihCmd m hlt s s' celse (by simpa using hexec)
        | Cwhile al cbefore cond ii cafter =>
          rw [execInstrR] at hexec ⊢
          obtain ⟨s2, hbefore, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨vc, hsem, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨b, htb, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          refine bind_ok_of (ihCmd m hlt s s2 cbefore hbefore)
            (bind_ok_of hsem (bind_ok_of htb ?_))
          cases b with
          | true =>
            obtain ⟨s3, hafter, hloop⟩ := ExecAdequacy.bind_eq_ok (by simpa using hexec)
            exact bind_ok_of (ihCmd m hlt s2 s3 cafter hafter)
              (ihIr m hlt s3 s' (.Cwhile al cbefore cond ii cafter) hloop)
          | false => simpa using hexec
        | Cfor v r body =>
          rw [OpSemCoverage.execInstrR_Cfor_eq] at hexec
          rw [OpSemCoverage.execInstrR_Cfor_eq]
          obtain ⟨vloV, hlo, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨vlo, hloI, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨vhiV, hhi, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨vhi, hhiI, hfor⟩ := ExecAdequacy.bind_eq_ok hexec
          refine bind_ok_of hlo (bind_ok_of hloI (bind_ok_of hhi (bind_ok_of hhiI ?_)))
          exact ihFor m hlt v (wrange r.dir vlo vhi) body s s' hfor
        | Ccall xs fn args =>
          rw [execInstrR] at hexec ⊢
          obtain ⟨vargs, hargs, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨tup, hcall, hwrite⟩ := ExecAdequacy.bind_eq_ok hexec
          refine bind_ok_of hargs (bind_ok_of (ihCall m hlt s.escs s.emem fn vargs tup hcall) ?_)
          exact hwrite
        | Csyscall xs o es =>
          rw [OpSemCoverage.execInstrR_Csyscall_err] at hexec
          exact absurd hexec (by simp)
    -- Instr component (re-tag of InstrR).
    have hI : ∀ (s s' : Estate SyscallState Mem) (i : Instr),
        execInstr (Mem := Mem) aS opS gd n s i prog = .ok s' →
        execInstr (Mem := Mem) aS opS gd (n+1) s i prog = .ok s' := by
      rintro s s' ⟨ii, ir⟩ hexec
      rw [execInstr] at hexec ⊢
      exact hIr s s' ir hexec
    -- Cmd component (list fold of Instr; same fuel, so list induction).
    have hCmd : ∀ (s s' : Estate SyscallState Mem) (c : Cmd),
        execCmd (Mem := Mem) aS opS gd n s c prog = .ok s' →
        execCmd (Mem := Mem) aS opS gd (n+1) s c prog = .ok s' := by
      intro s s' c
      induction c generalizing s with
      | nil =>
        intro hexec
        rw [CmdRun.execCmd_nil] at hexec ⊢
        exact hexec
      | cons i c ih_c =>
        intro hexec
        rw [CmdRun.execCmd_cons] at hexec ⊢
        obtain ⟨s2, hhead, htail⟩ := ExecAdequacy.bind_eq_ok hexec
        exact bind_ok_of (hI s s2 i hhead) (ih_c s2 htail)
    -- For component.
    have hFor : ∀ (v : VarI) (ws : List Int) (body : Cmd)
        (s s' : Estate SyscallState Mem),
        execFor (Mem := Mem) aS opS gd n v ws body s prog = .ok s' →
        execFor (Mem := Mem) aS opS gd (n+1) v ws body s prog = .ok s' := by
      cases n with
      | zero =>
        intro v ws body s s' hexec
        rw [execFor] at hexec
        exact absurd hexec (by simp)
      | succ m =>
        have hlt : m < m + 1 := Nat.lt_succ_self m
        intro v ws body s s' hexec
        cases ws with
        | nil =>
          rw [execFor] at hexec ⊢
          exact hexec
        | cons w ws' =>
          rw [execFor] at hexec ⊢
          obtain ⟨s1', hwrite, hrest⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨s2, hbody, hfor⟩ := ExecAdequacy.bind_eq_ok hrest
          exact bind_ok_of hwrite
            (bind_ok_of (ihCmd m hlt s1' s2 body hbody)
              (ihFor m hlt v ws' body s2 s' hfor))
    -- Call component.
    have hCall : ∀ (scs1 : SyscallState) (m1 : Mem) (fn : FunName)
        (vargs' : Values) (res : SyscallState × Mem × Values),
        execCall (Mem := Mem) aS opS gd n scs1 m1 fn vargs' prog = .ok res →
        execCall (Mem := Mem) aS opS gd (n+1) scs1 m1 fn vargs' prog = .ok res := by
      cases n with
      | zero =>
        intro scs1 m1 fn vargs' res hexec
        rw [execCall] at hexec
        exact absurd hexec (by simp)
      | succ m =>
        have hlt : m < m + 1 := Nat.lt_succ_self m
        intro scs1 m1 fn vargs' res hexec
        rw [execCall] at hexec ⊢
        cases hfd : getFunDef prog fn with
        | none =>
          rw [hfd] at hexec
          exact absurd hexec (by simp)
        | some f =>
          rw [hfd] at hexec
          obtain ⟨vargs, hargs, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨s1, hwrite, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨s2, hbody, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨vres, hrets, hexec⟩ := ExecAdequacy.bind_eq_ok hexec
          obtain ⟨vresB, hout, hfinal⟩ := ExecAdequacy.bind_eq_ok hexec
          refine bind_ok_of hargs (bind_ok_of hwrite
            (bind_ok_of (ihCmd m hlt s1 s2 f.body hbody)
              (bind_ok_of hrets (bind_ok_of hout ?_))))
          exact hfinal
    exact ⟨hIr, hI, hCmd, hFor, hCall⟩

/-! ### §2.a. The general `≤` monotonicity corollaries

Iterating the single-step bundle along the fuel gap gives monotonicity for any
`fuel ≤ fuel'`. These are the workhorses the completeness derivation calls to
lift each sub-run to the common `max`-fuel. -/

/-- **`execInstrR` fuel monotonicity.** A successful raw-instruction run is
    preserved under any fuel increase. -/
theorem execInstrR_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {s s' : Estate SyscallState Mem} {i : InstrR}
    (h : execInstrR (Mem := Mem) aS opS gd fuel s i prog = .ok s') :
    execInstrR (Mem := Mem) aS opS gd fuel' s i prog = .ok s' := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoStepAt_all aS opS gd prog _).1 _ _ _ ih

/-- **`execInstr` fuel monotonicity.** -/
theorem execInstr_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {s s' : Estate SyscallState Mem} {i : Instr}
    (h : execInstr (Mem := Mem) aS opS gd fuel s i prog = .ok s') :
    execInstr (Mem := Mem) aS opS gd fuel' s i prog = .ok s' := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoStepAt_all aS opS gd prog _).2.1 _ _ _ ih

/-- **`execCmd` fuel monotonicity.** A successful whole-command run is preserved
    under any fuel increase — the law that lets a derivation-induction take the
    `max` of the head- and tail-run fuels. -/
theorem execCmd_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {s s' : Estate SyscallState Mem} {c : Cmd}
    (h : execCmd (Mem := Mem) aS opS gd fuel s c prog = .ok s') :
    execCmd (Mem := Mem) aS opS gd fuel' s c prog = .ok s' := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoStepAt_all aS opS gd prog _).2.2.1 _ _ _ ih

/-- **`execFor` fuel monotonicity.** -/
theorem execFor_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {v : VarI} {ws : List Int} {body : Cmd} {s s' : Estate SyscallState Mem}
    (h : execFor (Mem := Mem) aS opS gd fuel v ws body s prog = .ok s') :
    execFor (Mem := Mem) aS opS gd fuel' v ws body s prog = .ok s' := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoStepAt_all aS opS gd prog _).2.2.2.1 _ _ _ _ _ ih

/-- **`execCall` fuel monotonicity.** -/
theorem execCall_mono {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {scs1 : SyscallState} {m1 : Mem} {fn : FunName} {vargs' : Values}
    {res : SyscallState × Mem × Values}
    (h : execCall (Mem := Mem) aS opS gd fuel scs1 m1 fn vargs' prog = .ok res) :
    execCall (Mem := Mem) aS opS gd fuel' scs1 m1 fn vargs' prog = .ok res := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoStepAt_all aS opS gd prog _).2.2.2.2 _ _ _ _ _ ih

/-! ## §3. Completeness (mutual induction on the derivation)

Every reference relational derivation is reachable by the executor at some fuel.
Proved by mutual induction on the `Sem`/`SemI`/`SemIr`/`SemFor`/`SemCall`
derivation, via the joint recursor `SemIr.rec`. The five motives are the
∃-fuel reachability predicates; each constructor's sub-derivations hand us their
fuel witnesses, we take `max … + 1`, and `*_mono` lifts every sub-run to that
common bound so the executor's own branch (`_eq` lemmas) returns `.ok`. -/

/-- The five-way completeness bundle, packaged as the result of one application
    of the joint recursor `SemIr.rec`. Each component is the ∃-fuel reachability
    statement for one judgement. -/
theorem completeness_bundle :
    (∀ {s s' : Estate SyscallState Mem} {c : Cmd},
        Sem (Mem := Mem) aS opS gd prog s c s' →
        ∃ fuel, execCmd (Mem := Mem) aS opS gd fuel s c prog = .ok s')
    ∧ (∀ {s s' : Estate SyscallState Mem} {i : Instr},
        SemI (Mem := Mem) aS opS gd prog s i s' →
        ∃ fuel, execInstr (Mem := Mem) aS opS gd fuel s i prog = .ok s')
    ∧ (∀ {s s' : Estate SyscallState Mem} {i : InstrR},
        SemIr (Mem := Mem) aS opS gd prog s i s' →
        ∃ fuel, execInstrR (Mem := Mem) aS opS gd fuel s i prog = .ok s')
    ∧ (∀ {v : VarI} {ws : List Int} {body : Cmd} {s s' : Estate SyscallState Mem},
        SemFor (Mem := Mem) aS opS gd prog v ws s body s' →
        ∃ fuel, execFor (Mem := Mem) aS opS gd fuel v ws body s prog = .ok s')
    ∧ (∀ {scs1 : SyscallState} {m1 : Mem} {fn : FunName} {vargs' : Values}
          {scs2 : SyscallState} {m2 : Mem} {vres' : Values},
        SemCall (Mem := Mem) aS opS gd prog scs1 m1 fn vargs' scs2 m2 vres' →
        ∃ fuel, execCall (Mem := Mem) aS opS gd fuel scs1 m1 fn vargs' prog
            = .ok (scs2, m2, vres')) := by
  refine ⟨@fun s s' c h => ?_, @fun s s' i h => ?_, @fun s s' i h => ?_,
    @fun v ws body s s' h => ?_, @fun scs1 m1 fn vargs' scs2 m2 vres' h => ?_⟩ <;>
  · -- Each component is one projection of the joint recursor, applied to `h`.
    refine h.rec
      (motive_1 := fun s c s' _ => ∃ fuel,
        execCmd (Mem := Mem) aS opS gd fuel s c prog = .ok s')
      (motive_2 := fun s i s' _ => ∃ fuel,
        execInstr (Mem := Mem) aS opS gd fuel s i prog = .ok s')
      (motive_3 := fun s i s' _ => ∃ fuel,
        execInstrR (Mem := Mem) aS opS gd fuel s i prog = .ok s')
      (motive_4 := fun v ws s body s' _ => ∃ fuel,
        execFor (Mem := Mem) aS opS gd fuel v ws body s prog = .ok s')
      (motive_5 := fun scs1 m1 fn vargs' scs2 m2 vres' _ => ∃ fuel,
        execCall (Mem := Mem) aS opS gd fuel scs1 m1 fn vargs' prog
          = .ok (scs2, m2, vres'))
      ?Eskip ?Eseq ?EmkI ?Eassgn ?Eopn ?Eif_true ?Eif_false
      ?Ewhile_true ?Ewhile_false ?Efor ?Ecall ?EForDone ?EForOne ?EcallRun
    -- §3 cases below.
    case Eskip =>
      intro s
      exact ⟨1, by rw [CmdRun.execCmd_nil]⟩
    case Eseq =>
      rintro s1 s2 s3 i c _ _ ⟨f1, hf1⟩ ⟨f2, hf2⟩
      refine ⟨max f1 f2, ?_⟩
      rw [CmdRun.execCmd_cons]
      exact bind_ok_of (execInstr_mono aS opS gd prog (le_max_left f1 f2) hf1)
        (execCmd_mono aS opS gd prog (le_max_right f1 f2) hf2)
    case EmkI =>
      rintro ii i s1 s2 _ ⟨f, hf⟩
      exact ⟨f, by rw [execInstr]; exact hf⟩
    case Eassgn =>
      rintro s1 s2 x tag ty e v v' hsem htrunc hwrite
      refine ⟨1, ?_⟩
      rw [show (1 : Nat) = 0 + 1 from rfl, OpSemCoverage.execInstrR_Cassgn_eq]
      exact bind_ok_of hsem (bind_ok_of htrunc hwrite)
    case Eopn =>
      rintro s1 s2 t o xs es hsem
      refine ⟨1, ?_⟩
      rw [show (1 : Nat) = 0 + 1 from rfl, OpSemCoverage.execInstrR_Copn_eq]
      exact hsem
    case Eif_true =>
      rintro s1 s2 e c1 c2 hcond _ ⟨f, hf⟩
      refine ⟨f + 1, ?_⟩
      rw [CifLowering.execInstrR_Cif_true _ _ _ _ _ _ _ _ _ hcond]
      exact hf
    case Eif_false =>
      rintro s1 s2 e c1 c2 hcond _ ⟨f, hf⟩
      refine ⟨f + 1, ?_⟩
      rw [CifLowering.execInstrR_Cif_false _ _ _ _ _ _ _ _ _ hcond]
      exact hf
    case Ewhile_true =>
      rintro s1 s2 s3 s4 a c e ii c' _ hcond _ _ ⟨fb, hfb⟩ ⟨fa, hfa⟩ ⟨fl, hfl⟩
      refine ⟨max (max fb fa) fl + 1, ?_⟩
      rw [execInstrR]
      refine bind_ok_of
        (execCmd_mono aS opS gd prog (le_trans (le_max_left fb fa)
          (le_max_left (max fb fa) fl)) hfb) ?_
      refine bind_ok_of hcond ?_
      refine bind_ok_of (a := true) rfl ?_
      simp only [if_true]
      refine bind_ok_of
        (execCmd_mono aS opS gd prog (le_trans (le_max_right fb fa)
          (le_max_left (max fb fa) fl)) hfa) ?_
      exact execInstrR_mono aS opS gd prog (le_max_right (max fb fa) fl) hfl
    case Ewhile_false =>
      rintro s1 s2 a c e ii c' _ hcond ⟨fb, hfb⟩
      refine ⟨fb + 1, ?_⟩
      rw [execInstrR]
      refine bind_ok_of hfb ?_
      refine bind_ok_of hcond ?_
      exact bind_ok_of (a := false) rfl rfl
    case Efor =>
      rintro s1 s2 i d lo hi c vlo vhi hlo hhi _ ⟨f, hf⟩
      refine ⟨f + 1, ?_⟩
      rw [OpSemCoverage.execInstrR_Cfor_eq]
      refine bind_ok_of hlo ?_
      refine bind_ok_of (a := vlo) rfl ?_
      refine bind_ok_of hhi ?_
      refine bind_ok_of (a := vhi) rfl ?_
      exact hf
    case Ecall =>
      rintro s1 s2 xs fn args escs2 emem2 vargs vres hargs _ hwrite ⟨f, hf⟩
      refine ⟨f + 1, ?_⟩
      rw [execInstrR]
      refine bind_ok_of hargs ?_
      exact bind_ok_of (a := (escs2, emem2, vres)) hf hwrite
    case EForDone =>
      intro s i c
      exact ⟨1, by rw [show (1 : Nat) = 0 + 1 from rfl, execFor]⟩
    case EForOne =>
      rintro s1 s1' s2 s3 i w ws c hwrite _ _ ⟨fb, hfb⟩ ⟨ff, hff⟩
      refine ⟨max fb ff + 1, ?_⟩
      rw [execFor]
      refine bind_ok_of hwrite ?_
      exact bind_ok_of
        (execCmd_mono aS opS gd prog (le_max_left fb ff) hfb)
        (execFor_mono aS opS gd prog (le_max_right fb ff) hff)
    case EcallRun =>
      rintro scs1 m1 fn f vargs vargs' s0 s1 s2 vres vres'
        hfd hin hs0 hwrite _ hrets hout ⟨fb, hfb⟩
      refine ⟨fb + 1, ?_⟩
      rw [execCall, hfd]
      subst hs0
      refine bind_ok_of hin ?_
      refine bind_ok_of hwrite ?_
      refine bind_ok_of hfb ?_
      refine bind_ok_of hrets ?_
      exact bind_ok_of hout rfl

/-! ### §3.a. The public completeness corollaries

The clean per-judgement projections of the completeness bundle. Each says: *every
reference relational derivation is reachable by the executor at some fuel.* These
are the converses of `ExecAdequacy.execInstrR_sound` & co. -/

/-- **Instruction-level completeness (`SemIr`).** Every reference relational raw-
    instruction step is reachable by the executor at some fuel. The converse of
    `ExecAdequacy.execInstrR_sound`. -/
theorem execInstrR_complete {s s' : Estate SyscallState Mem} {i : InstrR}
    (h : SemIr (Mem := Mem) aS opS gd prog s i s') :
    ∃ fuel, execInstrR (Mem := Mem) aS opS gd fuel s i prog = .ok s' :=
  (completeness_bundle aS opS gd prog).2.2.1 h

/-- **Annotated-instruction completeness (`SemI`).** -/
theorem execInstr_complete {s s' : Estate SyscallState Mem} {i : Instr}
    (h : SemI (Mem := Mem) aS opS gd prog s i s') :
    ∃ fuel, execInstr (Mem := Mem) aS opS gd fuel s i prog = .ok s' :=
  (completeness_bundle aS opS gd prog).2.1 h

/-- **Command-level completeness (`Sem`).** Every reference relational whole-
    command big-step is reachable by the executor at some fuel. The converse of
    `ExecAdequacy.execCmd_sound`. -/
theorem execCmd_complete {s s' : Estate SyscallState Mem} {c : Cmd}
    (h : Sem (Mem := Mem) aS opS gd prog s c s') :
    ∃ fuel, execCmd (Mem := Mem) aS opS gd fuel s c prog = .ok s' :=
  (completeness_bundle aS opS gd prog).1 h

/-- **For-loop completeness (`SemFor`).** -/
theorem execFor_complete {v : VarI} {ws : List Int} {body : Cmd}
    {s s' : Estate SyscallState Mem}
    (h : SemFor (Mem := Mem) aS opS gd prog v ws s body s') :
    ∃ fuel, execFor (Mem := Mem) aS opS gd fuel v ws body s prog = .ok s' :=
  (completeness_bundle aS opS gd prog).2.2.2.1 h

/-- **Call completeness (`SemCall`).** Every reference relational function-call
    derivation is reachable by the executor at some fuel. The converse of
    `ExecAdequacy.execCall_sound`. -/
theorem execCall_complete {scs1 : SyscallState} {m1 : Mem} {fn : FunName}
    {vargs' : Values} {scs2 : SyscallState} {m2 : Mem} {vres' : Values}
    (h : SemCall (Mem := Mem) aS opS gd prog scs1 m1 fn vargs' scs2 m2 vres') :
    ∃ fuel, execCall (Mem := Mem) aS opS gd fuel scs1 m1 fn vargs' prog
        = .ok (scs2, m2, vres') :=
  (completeness_bundle aS opS gd prog).2.2.2.2 h

/-! ## §4. Full adequacy: the ∃-fuel `↔` characterisations

Soundness (`ExecAdequacy.*_sound`) + completeness (§3.a) give the **iff**: a
successful executor run *at some fuel* and the reference relational derivation
are interderivable. This is the headline result — the fuel-bounded functional
executor *exactly* characterises the ported Coq `psem.v` big-step semantics. -/

/-- **Full instruction-level adequacy (`SemIr`).** A raw-instruction step holds in
    the reference relational semantics **iff** the executor reaches `s'` from `s`
    at some fuel. The mechanical port of Coq `sem_i` (`psem.v:60`), exactly
    characterised by `execInstrR`. -/
theorem execInstrR_adequacy {s s' : Estate SyscallState Mem} {i : InstrR} :
    (∃ fuel, execInstrR (Mem := Mem) aS opS gd fuel s i prog = .ok s')
      ↔ SemIr (Mem := Mem) aS opS gd prog s i s' :=
  ⟨fun ⟨_, h⟩ => ExecAdequacy.execInstrR_sound aS opS gd prog h,
   fun h => execInstrR_complete aS opS gd prog h⟩

/-- **Full annotated-instruction adequacy (`SemI`).** Mirrors Coq `sem_I`
    (`psem.v:55`). -/
theorem execInstr_adequacy {s s' : Estate SyscallState Mem} {i : Instr} :
    (∃ fuel, execInstr (Mem := Mem) aS opS gd fuel s i prog = .ok s')
      ↔ SemI (Mem := Mem) aS opS gd prog s i s' :=
  ⟨fun ⟨_, h⟩ => ExecAdequacy.execInstr_sound aS opS gd prog h,
   fun h => execInstr_complete aS opS gd prog h⟩

/-- **Full command-level adequacy (`Sem`).** A whole-command big-step holds in the
    reference relational semantics **iff** the executor reaches `s'` from `s` at
    some fuel. The mechanical port of Coq `sem` (`psem.v:48`), exactly
    characterised by `execCmd`. -/
theorem execCmd_adequacy {s s' : Estate SyscallState Mem} {c : Cmd} :
    (∃ fuel, execCmd (Mem := Mem) aS opS gd fuel s c prog = .ok s')
      ↔ Sem (Mem := Mem) aS opS gd prog s c s' :=
  ⟨fun ⟨_, h⟩ => ExecAdequacy.execCmd_sound aS opS gd prog h,
   fun h => execCmd_complete aS opS gd prog h⟩

/-- **Full for-loop adequacy (`SemFor`).** Mirrors Coq `sem_for` (`psem.v:111`). -/
theorem execFor_adequacy {v : VarI} {ws : List Int} {body : Cmd}
    {s s' : Estate SyscallState Mem} :
    (∃ fuel, execFor (Mem := Mem) aS opS gd fuel v ws body s prog = .ok s')
      ↔ SemFor (Mem := Mem) aS opS gd prog v ws s body s' :=
  ⟨fun ⟨_, h⟩ => ExecAdequacy.execFor_sound aS opS gd prog h,
   fun h => execFor_complete aS opS gd prog h⟩

/-- **Full call adequacy (`SemCall`).** A function-call derivation holds in the
    reference relational semantics **iff** the executor reaches the result triple
    at some fuel. The mechanical port of Coq `sem_call` (`psem.v:121`), exactly
    characterised by `execCall`. -/
theorem execCall_adequacy {scs1 : SyscallState} {m1 : Mem} {fn : FunName}
    {vargs' : Values} {scs2 : SyscallState} {m2 : Mem} {vres' : Values} :
    (∃ fuel, execCall (Mem := Mem) aS opS gd fuel scs1 m1 fn vargs' prog
        = .ok (scs2, m2, vres'))
      ↔ SemCall (Mem := Mem) aS opS gd prog scs1 m1 fn vargs' scs2 m2 vres' :=
  ⟨fun ⟨_, h⟩ => ExecAdequacy.execCall_sound aS opS gd prog h,
   fun h => execCall_complete aS opS gd prog h⟩

/-! ## §5. Worked example: a `SemIr` derivation is reachable by the executor

Reusing `OpSemCoverage.AssignExample` (the `x := y + 1` assignment from §4 of
`ExecAdequacy`), we exhibit completeness concretely: the reference relational
step `SemIr.Eassgn` for `x := y + 1` from `y = 5` is *reachable* by the executor,
and (via the full-adequacy iff) the executor run at the witnessed fuel lands in
the same post-state the derivation specifies. -/

namespace WorkedExample

open OpSemCoverage.AssignExample
open ExecAdequacy.WorkedExample

/-- The reference relational `SemIr.Eassgn` derivation for `x := y + 1` from
    `y = 5` — the same derivation `ExecAdequacy.WorkedExample` produced by
    *soundness*; here we treat it as a hypothesis to feed *completeness*. -/
theorem assignXY_semIr :
    SemIr (Mem := TrivialMem) addAsmSem addOpSem [] Prog.empty
      (startState 5) assignXY assignXY_post :=
  ExecAdequacy.execInstrR_sound _ _ _ _ assignXY_run_ok

/-- **Completeness made concrete.** The reference relational step
    `SemIr.Eassgn` for `x := y + 1` from `y = 5` is *reachable* by the executor:
    there is a fuel at which `execInstrR` lands in the derivation's post-state.
    Obtained by promoting the `SemIr` derivation through `execInstrR_complete`. -/
theorem assignXY_semIr_reachable :
    ∃ fuel, execInstrR (Mem := TrivialMem) addAsmSem addOpSem [] fuel
      (startState 5) assignXY Prog.empty = .ok assignXY_post :=
  execInstrR_complete _ _ _ _ assignXY_semIr

/-- **The full-adequacy iff, concrete.** For `x := y + 1` from `y = 5`, the
    ∃-fuel executor run and the reference relational `SemIr.Eassgn` derivation are
    *interderivable* — the iff `execInstrR_adequacy` instantiated at the example. -/
theorem assignXY_adequacy_iff :
    (∃ fuel, execInstrR (Mem := TrivialMem) addAsmSem addOpSem [] fuel
        (startState 5) assignXY Prog.empty = .ok assignXY_post)
      ↔ SemIr (Mem := TrivialMem) addAsmSem addOpSem [] Prog.empty
          (startState 5) assignXY assignXY_post :=
  execInstrR_adequacy _ _ _ _

end WorkedExample

end CatCrypt.Crypto.SecureCompilation.VIR.ExecCompleteness
