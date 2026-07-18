/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CmdRun

set_option autoImplicit false

/-!
# Adequacy: the fuel-bounded executor implements the reference relational semantics

`JasminCoqSemMirror.lean` carries **two** semantics for the ported jasmin
operational core:

* the *reference relational big-step* judgement — the mechanical port of
  Coq `psem.v`'s `Inductive sem … with sem_I … with sem_i … with sem_for …
  with sem_call` (here the mutual `Sem` / `SemI` / `SemIr` / `SemFor` /
  `SemCall`); and
* the *functional fuel-bounded executor* `execInstrR` / `execInstr` /
  `execCmd` / `execFor` / `execCall`, used for `#eval` smoke tests.

Every just-landed operational file (`CifLowering`, `WhileLowering`,
`CallLowering`, `OpSemCoverage`, `CmdRun`) characterises the executor's
*branch* result (e.g. `execInstrR_Cassgn_eq`, `execInstrR_Cif_eq_ite`,
`execCmd_cons`) but none ties the executor back to the **reference relational
semantics** itself. The mirror's §7 header records this as the shared residual:

  > "The functional and relational definitions agree by construction on
  >  straight-line code (Phase C: prove this as `semCmd_sound`)."

This file discharges that residual in the **soundness** direction (the natural
one): *if the executor succeeds (`= .ok s'`), the relational judgement holds*.

  `execInstrR … (fuel'+1) s i prog = .ok s' → SemIr … s i s'`
  `execCmd    … (fuel'+1) s c prog = .ok s' → Sem   … s c s'`

This lifts the operational layer from "functional executor" to "agrees with
the reference relational semantics": any `#eval`/`native_decide` KAT on
`execCmd`/`execInstrR` now *witnesses* the corresponding `Sem`/`SemIr`
derivation in `psem.v`'s ported inductive.

## What is proved

The five executor entry points (`execInstrR`, `execInstr`, `execCmd`,
`execFor`, `execCall`) are *mutually recursive on a shared fuel*, and the
target relations (`SemIr`, `SemI`, `Sem`, `SemFor`, `SemCall`) are a *mutual
inductive*. Soundness therefore proves them **together**, by strong induction
on the fuel `n`: `execAdequacy_aux n` bundles the five implications, and the
recursive executor branches (which always recurse at the *strictly smaller*
fuel `fuel'`) feed the induction hypothesis at `fuel' < fuel'+1 = n`.

**All seven `SemIr` constructors are covered** (all goals closed):

| Constructor | Executor branch | Relational rule |
|---|---|---|
| `Cassgn` | `semPexpr; truncateVal; writeLval` | `SemIr.Eassgn` |
| `Copn`   | `semSopn`                            | `SemIr.Eopn`   |
| `Cif`    | `semPexpr; toBool; execCmd`          | `SemIr.Eif_true`/`Eif_false` |
| `Cwhile` | `execCmd; semPexpr; (loop ∣ stop)`   | `SemIr.Ewhile_true`/`Ewhile_false` |
| `Cfor`   | `semPexpr×2; execFor`                | `SemIr.Efor` (via `SemFor`) |
| `Ccall`  | `semPexprs; execCall; writeLvals`    | `SemIr.Ecall` (via `SemCall`) |
| `Csyscall` | deferral error                     | (vacuous — never `.ok`)      |

`Csyscall` is the honest exception: its executor branch is a *deferral error*
(`.otherErr "…deferred to Phase C"`, see `OpSemCoverage.execInstrR_Csyscall_err`),
so the `= .ok s'` hypothesis is **unsatisfiable** — the case closes by
contradiction, and there is no `Csyscall` constructor on `SemIr` to target
(the mirror's §6 deliberately omits it). This is faithful: a syscall run can
never succeed, so it never witnesses a (non-existent) relational step.

## The remaining direction (honest note)

This file proves **soundness only** (executor ⟹ relation). The converse,
**completeness** (`SemIr … s i s' → ∃ fuel, execInstrR … fuel s i s' = .ok s'`),
is *not* proved here: it requires exhibiting a fuel bound from a derivation
tree (a separate strong induction *on the derivation*, with a fuel-monotonicity
lemma `execInstrR … fuel = .ok → execInstrR … (fuel+1) = .ok`). The executor
is deterministic, so soundness already pins the *result* of any successful run
to the unique relational image; completeness would additionally show every
relational step is *reachable* at some fuel. That is left for a follow-up.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy

open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## §1. `JResult`-bind inversion

To invert a successful `do`-block, we repeatedly peel `JResult.bind r f = .ok c`
into `∃ a, r = .ok a ∧ f a = .ok c`. This is the one structural lemma the
soundness proof needs: every executor branch is a `bind`-chain that ends in
`.ok s'`, and each peel exposes the intermediate `semPexpr`/`toBool`/… success
that the matching relational constructor takes as a hypothesis. -/

/-- `JResult.bind r f = .ok c` forces `r` to succeed (with some `a`) and `f a` to
    succeed with `c`. The inversion lemma that drives the whole soundness proof. -/
theorem bind_eq_ok {α β : Type} {r : JResult α} {f : α → JResult β} {c : β}
    (h : JResult.bind r f = .ok c) : ∃ a, r = .ok a ∧ f a = .ok c := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | typeError => exact absurd h (by simp [JResult.bind])
  | undefError => exact absurd h (by simp [JResult.bind])
  | addrUndef => exact absurd h (by simp [JResult.bind])
  | otherErr m => exact absurd h (by simp [JResult.bind])

/-- `v.toBool = .ok b` forces `v = .Vbool b` (the only success arm of `toBool`).
    Bridges the executor's `toBool`-peel to the relational `… = .ok (.Vbool b)`
    hypothesis the `Cif`/`Cwhile` constructors take. -/
theorem toBool_eq_ok {v : Value} {b : Bool} (h : v.toBool = .ok b) :
    v = .Vbool b := by
  cases v with
  | Vbool b' => cases h; rfl
  | Vint _ => exact absurd h (by simp [Value.toBool])
  | Varr _ _ => exact absurd h (by simp [Value.toBool])
  | Vword _ _ => exact absurd h (by simp [Value.toBool])
  | Vundef t =>
    cases t <;> exact absurd h (by simp [Value.toBool])

/-- `v.toInt = .ok z` forces `v = .Vint z` (the only success arm of `toInt`).
    Bridges the executor's `toInt`-peel to the relational `… = .ok (.Vint z)`
    hypothesis the `Cfor` constructor (`Efor`) takes. -/
theorem toInt_eq_ok {v : Value} {z : Int} (h : v.toInt = .ok z) :
    v = .Vint z := by
  cases v with
  | Vbool _ => exact absurd h (by simp [Value.toInt])
  | Vint z' => cases h; rfl
  | Varr _ _ => exact absurd h (by simp [Value.toInt])
  | Vword _ _ => exact absurd h (by simp [Value.toInt])
  | Vundef t =>
    cases t <;> exact absurd h (by simp [Value.toInt])

/-! ## §2. The mutual adequacy bundle (strong induction on fuel)

The five executor entry points recurse on a shared fuel and the five reference
relations are a mutual inductive, so soundness is proved as one bundle by strong
induction on fuel. `execAdequacy_aux n` states all five implications at fuel `n`;
the recursive executor branches always recurse at `fuel' < fuel'+1 = n`, feeding
the strong-induction hypothesis `ih : ∀ m < n, execAdequacy_aux m`. -/

variable {SyscallState Mem : Type} [MemModel Mem]
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- The five-way adequacy bundle at a fixed fuel `n`. Soundness of each executor
    entry point against its reference relation. -/
def execAdequacyAt (n : Nat) : Prop :=
  (∀ (s s' : Estate SyscallState Mem) (i : InstrR),
      execInstrR (Mem := Mem) aS opS gd n s i prog = .ok s' →
      SemIr (Mem := Mem) aS opS gd prog s i s')
  ∧ (∀ (s s' : Estate SyscallState Mem) (i : Instr),
      execInstr (Mem := Mem) aS opS gd n s i prog = .ok s' →
      SemI (Mem := Mem) aS opS gd prog s i s')
  ∧ (∀ (s s' : Estate SyscallState Mem) (c : Cmd),
      execCmd (Mem := Mem) aS opS gd n s c prog = .ok s' →
      Sem (Mem := Mem) aS opS gd prog s c s')
  ∧ (∀ (v : VarI) (ws : List Int) (body : Cmd) (s s' : Estate SyscallState Mem),
      execFor (Mem := Mem) aS opS gd n v ws body s prog = .ok s' →
      SemFor (Mem := Mem) aS opS gd prog v ws s body s')
  ∧ (∀ (scs1 : SyscallState) (m1 : Mem) (fn : FunName) (vargs' : Values)
        (scs2 : SyscallState) (m2 : Mem) (vres' : Values),
      execCall (Mem := Mem) aS opS gd n scs1 m1 fn vargs' prog
          = .ok (scs2, m2, vres') →
      SemCall (Mem := Mem) aS opS gd prog scs1 m1 fn vargs' scs2 m2 vres')

/-- **The adequacy bundle holds at every fuel.** Strong induction on `n`. -/
theorem execAdequacyAt_all (n : Nat) :
    execAdequacyAt (SyscallState := SyscallState) (Mem := Mem) aS opS gd prog n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- Unpack the strong IH into the five per-judgement hypotheses, at any `m < n`.
    have ihIr : ∀ m, m < n → ∀ (s s' : Estate SyscallState Mem) (i : InstrR),
        execInstrR (Mem := Mem) aS opS gd m s i prog = .ok s' →
        SemIr (Mem := Mem) aS opS gd prog s i s' :=
      fun m hm => (ih m hm).1
    have ihI : ∀ m, m < n → ∀ (s s' : Estate SyscallState Mem) (i : Instr),
        execInstr (Mem := Mem) aS opS gd m s i prog = .ok s' →
        SemI (Mem := Mem) aS opS gd prog s i s' :=
      fun m hm => (ih m hm).2.1
    have ihCmd : ∀ m, m < n → ∀ (s s' : Estate SyscallState Mem) (c : Cmd),
        execCmd (Mem := Mem) aS opS gd m s c prog = .ok s' →
        Sem (Mem := Mem) aS opS gd prog s c s' :=
      fun m hm => (ih m hm).2.2.1
    have ihFor : ∀ m, m < n → ∀ (v : VarI) (ws : List Int) (body : Cmd)
        (s s' : Estate SyscallState Mem),
        execFor (Mem := Mem) aS opS gd m v ws body s prog = .ok s' →
        SemFor (Mem := Mem) aS opS gd prog v ws s body s' :=
      fun m hm => (ih m hm).2.2.2.1
    have ihCall : ∀ m, m < n → ∀ (scs1 : SyscallState) (m1 : Mem) (fn : FunName)
        (vargs' : Values) (scs2 : SyscallState) (m2 : Mem) (vres' : Values),
        execCall (Mem := Mem) aS opS gd m scs1 m1 fn vargs' prog = .ok (scs2, m2, vres') →
        SemCall (Mem := Mem) aS opS gd prog scs1 m1 fn vargs' scs2 m2 vres' :=
      fun m hm => (ih m hm).2.2.2.2
    -- We prove the five components in dependency order. `InstrR@n`, `For@n`,
    -- `Call@n` recurse only at strictly smaller fuel (`fuel' < fuel'+1 = n`),
    -- so they need only `ih`. `Instr@n` is `InstrR@n` re-tagged; `Cmd@n` is the
    -- list fold of `Instr@n`.
    have hIr : ∀ (s s' : Estate SyscallState Mem) (i : InstrR),
        execInstrR (Mem := Mem) aS opS gd n s i prog = .ok s' →
        SemIr (Mem := Mem) aS opS gd prog s i s' := by
      cases n with
      | zero =>
        intro s s' i hexec
        rw [execInstrR] at hexec
        exact absurd hexec (by simp)
      | succ fuel' =>
        have hlt : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
        intro s s' i hexec
        cases i with
        | Cassgn lv tag ty e =>
          -- `execInstrR_Cassgn_eq` : branch = `assignExec` = eval; truncate; write.
          rw [OpSemCoverage.execInstrR_Cassgn_eq] at hexec
          unfold OpSemCoverage.assignExec at hexec
          obtain ⟨v, hsem, hexec⟩ := bind_eq_ok hexec
          obtain ⟨v', htrunc, hwrite⟩ := bind_eq_ok hexec
          exact SemIr.Eassgn s s' lv tag ty e v v' hsem htrunc hwrite
        | Copn xs tag o es =>
          rw [OpSemCoverage.execInstrR_Copn_eq] at hexec
          exact SemIr.Eopn s s' tag o xs es hexec
        | Cif cond cthen celse =>
          -- Peel the executor's own `Cif` branch: eval cond, toBool, then branch.
          rw [execInstrR] at hexec
          obtain ⟨vc, hsem, hexec⟩ := bind_eq_ok hexec
          obtain ⟨b, htb, hexec⟩ := bind_eq_ok hexec
          rw [toBool_eq_ok htb] at hsem
          -- `hsem : semPexpr … cond = .ok (.Vbool b)`; `hexec : (if b = true …) = .ok s'`.
          cases b with
          | true =>
            exact SemIr.Eif_true s s' cond cthen celse hsem
              (ihCmd fuel' hlt s s' cthen hexec)
          | false =>
            exact SemIr.Eif_false s s' cond cthen celse hsem
              (ihCmd fuel' hlt s s' celse hexec)
        | Cwhile al cbefore cond ii cafter =>
          rw [execInstrR] at hexec
          obtain ⟨s2, hbefore, hexec⟩ := bind_eq_ok hexec
          obtain ⟨vc, hsem, hexec⟩ := bind_eq_ok hexec
          obtain ⟨b, htb, hexec⟩ := bind_eq_ok hexec
          rw [toBool_eq_ok htb] at hsem
          cases b with
          | true =>
            obtain ⟨s3, hafter, hloop⟩ := bind_eq_ok hexec
            exact SemIr.Ewhile_true s s2 s3 s' al cbefore cond ii cafter
              (ihCmd fuel' hlt s s2 cbefore hbefore) hsem
              (ihCmd fuel' hlt s2 s3 cafter hafter)
              (ihIr fuel' hlt s3 s' (.Cwhile al cbefore cond ii cafter) hloop)
          | false =>
            cases hexec
            exact SemIr.Ewhile_false s s' al cbefore cond ii cafter
              (ihCmd fuel' hlt s s' cbefore hbefore) hsem
        | Cfor v r body =>
          rw [OpSemCoverage.execInstrR_Cfor_eq] at hexec
          obtain ⟨vloV, hlo, hexec⟩ := bind_eq_ok hexec
          obtain ⟨vlo, hloI, hexec⟩ := bind_eq_ok hexec
          obtain ⟨vhiV, hhi, hexec⟩ := bind_eq_ok hexec
          obtain ⟨vhi, hhiI, hfor⟩ := bind_eq_ok hexec
          have hvlo : vloV = .Vint vlo := toInt_eq_ok hloI
          have hvhi : vhiV = .Vint vhi := toInt_eq_ok hhiI
          subst hvlo; subst hvhi
          -- Reassemble `r = ⟨r.dir, r.lo, r.hi⟩` so the `Efor` target matches.
          obtain ⟨d, lo, hi⟩ := r
          exact SemIr.Efor s s' v d lo hi body vlo vhi hlo hhi
            (ihFor fuel' hlt v (wrange d vlo vhi) body s s' hfor)
        | Ccall xs fn args =>
          rw [execInstrR] at hexec
          obtain ⟨vargs, hargs, hexec⟩ := bind_eq_ok hexec
          obtain ⟨tup, hcall, hwrite⟩ := bind_eq_ok hexec
          obtain ⟨escs2, emem2, vres⟩ := tup
          exact SemIr.Ecall s s' xs fn args escs2 emem2 vargs vres hargs
            (ihCall fuel' hlt s.escs s.emem fn vargs escs2 emem2 vres hcall) hwrite
        | Csyscall xs o es =>
          rw [OpSemCoverage.execInstrR_Csyscall_err] at hexec
          exact absurd hexec (by simp)
    have hI : ∀ (s s' : Estate SyscallState Mem) (i : Instr),
        execInstr (Mem := Mem) aS opS gd n s i prog = .ok s' →
        SemI (Mem := Mem) aS opS gd prog s i s' := by
      rintro s s' ⟨ii, ir⟩ hexec
      rw [execInstr] at hexec
      exact SemI.EmkI ii ir s s' (hIr s s' ir hexec)
    have hCmd : ∀ (s s' : Estate SyscallState Mem) (c : Cmd),
        execCmd (Mem := Mem) aS opS gd n s c prog = .ok s' →
        Sem (Mem := Mem) aS opS gd prog s c s' := by
      intro s s' c
      induction c generalizing s with
      | nil =>
        intro hexec
        rw [CmdRun.execCmd_nil] at hexec
        cases hexec
        exact Sem.Eskip s'
      | cons i c ih_c =>
        intro hexec
        rw [CmdRun.execCmd_cons] at hexec
        obtain ⟨s2, hhead, htail⟩ := bind_eq_ok hexec
        exact Sem.Eseq s s2 s' i c (hI s s2 i hhead) (ih_c s2 htail)
    have hFor : ∀ (v : VarI) (ws : List Int) (body : Cmd)
        (s s' : Estate SyscallState Mem),
        execFor (Mem := Mem) aS opS gd n v ws body s prog = .ok s' →
        SemFor (Mem := Mem) aS opS gd prog v ws s body s' := by
      cases n with
      | zero =>
        intro v ws body s s' hexec
        rw [execFor] at hexec
        exact absurd hexec (by simp)
      | succ fuel' =>
        have hlt : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
        intro v ws body s s' hexec
        cases ws with
        | nil =>
          rw [execFor] at hexec
          cases hexec
          exact SemFor.EForDone s v body
        | cons w ws' =>
          rw [execFor] at hexec
          obtain ⟨s1', hwrite, hrest⟩ := bind_eq_ok hexec
          obtain ⟨s2, hbody, hfor⟩ := bind_eq_ok hrest
          exact SemFor.EForOne s s1' s2 s' v w ws' body hwrite
            (ihCmd fuel' hlt s1' s2 body hbody)
            (ihFor fuel' hlt v ws' body s2 s' hfor)
    have hCall : ∀ (scs1 : SyscallState) (m1 : Mem) (fn : FunName)
        (vargs' : Values) (scs2 : SyscallState) (m2 : Mem) (vres' : Values),
        execCall (Mem := Mem) aS opS gd n scs1 m1 fn vargs' prog = .ok (scs2, m2, vres') →
        SemCall (Mem := Mem) aS opS gd prog scs1 m1 fn vargs' scs2 m2 vres' := by
      cases n with
      | zero =>
        intro scs1 m1 fn vargs' scs2 m2 vres' hexec
        rw [execCall] at hexec
        exact absurd hexec (by simp)
      | succ fuel' =>
        have hlt : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
        intro scs1 m1 fn vargs' scs2 m2 vres' hexec
        rw [execCall] at hexec
        cases hfd : getFunDef prog fn with
        | none =>
          rw [hfd] at hexec
          exact absurd hexec (by simp)
        | some f =>
          rw [hfd] at hexec
          obtain ⟨vargs, hargs, hexec⟩ := bind_eq_ok hexec
          obtain ⟨s1, hwrite, hexec⟩ := bind_eq_ok hexec
          obtain ⟨s2, hbody, hexec⟩ := bind_eq_ok hexec
          obtain ⟨vres, hrets, hexec⟩ := bind_eq_ok hexec
          obtain ⟨vresB, hout, hfinal⟩ := bind_eq_ok hexec
          -- `hfinal : .ok (s2.escs, s2.emem, vresB) = .ok (scs2, m2, vres')`
          simp only [JResult.ok.injEq, Prod.mk.injEq] at hfinal
          obtain ⟨he1, he2, he3⟩ := hfinal
          subst he1; subst he2; subst he3
          exact SemCall.EcallRun scs1 m1 fn f vargs vargs'
            { escs := scs1, emem := m1, evm := Vm.init } s1 s2 vres vresB
            hfd hargs rfl hwrite (ihCmd fuel' hlt _ _ f.body hbody) hrets hout
    exact ⟨hIr, hI, hCmd, hFor, hCall⟩

/-! ## §3. The public adequacy corollaries

The clean per-judgement statements, projected out of the bundle. Each says:
*a successful executor run is a witness of the reference relational judgement*.
These are the deliverables — "the executor implements `psem.v`'s relation". -/

/-- **Instruction-level adequacy (`SemIr`).** A successful raw-instruction run
    witnesses the reference relational step `SemIr` (the port of Coq `sem_i`,
    `psem.v:60`). Covers all of `Cassgn`/`Copn`/`Cif`/`Cwhile`/`Cfor`/`Ccall`;
    `Csyscall` never succeeds (deferral error), so the implication is vacuous
    there. -/
theorem execInstrR_sound {n : Nat} {s s' : Estate SyscallState Mem} {i : InstrR}
    (h : execInstrR (Mem := Mem) aS opS gd n s i prog = .ok s') :
    SemIr (Mem := Mem) aS opS gd prog s i s' :=
  (execAdequacyAt_all aS opS gd prog n).1 s s' i h

/-- **Annotated-instruction adequacy (`SemI`).** Mirrors Coq `sem_I`
    (`psem.v:55`). -/
theorem execInstr_sound {n : Nat} {s s' : Estate SyscallState Mem} {i : Instr}
    (h : execInstr (Mem := Mem) aS opS gd n s i prog = .ok s') :
    SemI (Mem := Mem) aS opS gd prog s i s' :=
  (execAdequacyAt_all aS opS gd prog n).2.1 s s' i h

/-- **Command-level adequacy (`Sem`).** A successful whole-command run witnesses
    the reference relational big-step `Sem` (the port of Coq `sem`, `psem.v:48`).
    This is the `semCmd_sound` residual the mirror's §7 header names. -/
theorem execCmd_sound {n : Nat} {s s' : Estate SyscallState Mem} {c : Cmd}
    (h : execCmd (Mem := Mem) aS opS gd n s c prog = .ok s') :
    Sem (Mem := Mem) aS opS gd prog s c s' :=
  (execAdequacyAt_all aS opS gd prog n).2.2.1 s s' c h

/-- **For-loop adequacy (`SemFor`).** Mirrors Coq `sem_for` (`psem.v:111`). -/
theorem execFor_sound {n : Nat} {v : VarI} {ws : List Int} {body : Cmd}
    {s s' : Estate SyscallState Mem}
    (h : execFor (Mem := Mem) aS opS gd n v ws body s prog = .ok s') :
    SemFor (Mem := Mem) aS opS gd prog v ws s body s' :=
  (execAdequacyAt_all aS opS gd prog n).2.2.2.1 v ws body s s' h

/-- **Call adequacy (`SemCall`).** A successful function-call run witnesses the
    reference relational `SemCall` (the port of Coq `sem_call`, `psem.v:121`). -/
theorem execCall_sound {n : Nat} {scs1 : SyscallState} {m1 : Mem} {fn : FunName}
    {vargs' : Values} {scs2 : SyscallState} {m2 : Mem} {vres' : Values}
    (h : execCall (Mem := Mem) aS opS gd n scs1 m1 fn vargs' prog = .ok (scs2, m2, vres')) :
    SemCall (Mem := Mem) aS opS gd prog scs1 m1 fn vargs' scs2 m2 vres' :=
  (execAdequacyAt_all aS opS gd prog n).2.2.2.2 scs1 m1 fn vargs' scs2 m2 vres' h

/-! ## §4. Worked example: a concrete `.ok` run exhibits its `SemIr` derivation

We reuse `OpSemCoverage.AssignExample` (trivial memory, an `OpSem` covering
integer add, the assignment `x := y + 1` on integer variables). Started at
`y = 5`, the executor produces a state; `execInstrR_sound` turns that successful
run into the corresponding `SemIr.Eassgn` derivation of the reference semantics.

This is the adequacy bridge made concrete: the `#eval`-checkable run
(`assignXY` from `y = 5`) is *also* a `psem.v` relational step. -/

namespace WorkedExample

open OpSemCoverage.AssignExample

/-- The post-state `assignExec` produces for `x := y + 1` from `y = 5`
    (`x = 6`). Naming it via `assignExec` keeps the example `rfl`-pinned. -/
def assignXY_post : Estate Unit TrivialMem :=
  match OpSemCoverage.assignExec (Mem := TrivialMem) addOpSem [] (.Lvar xVar) .aint rhs
          (startState 5) with
  | .ok s => s
  | _ => startState 5

/-- The executor's `x := y + 1` run from `y = 5` succeeds and lands in
    `assignXY_post`. Reduced via the landed `Cassgn` keystone, then `rfl`. -/
theorem assignXY_run_ok :
    execInstrR (Mem := TrivialMem) addAsmSem addOpSem [] 1 (startState 5) assignXY
      = .ok assignXY_post := by
  show execInstrR (Mem := TrivialMem) addAsmSem addOpSem [] (0 + 1) (startState 5)
        (.Cassgn (.Lvar xVar) .AT_none .aint rhs) Prog.empty = _
  rw [OpSemCoverage.execInstrR_Cassgn_eq]
  rfl

/-- **Adequacy made concrete.** The successful run `x := y + 1` from `y = 5`
    *witnesses* the reference relational step `SemIr.Eassgn`: the executor result
    is also a `psem.v` derivation, obtained by promoting the `.ok` run through
    `execInstrR_sound`. Also confirms (`readX`) the witnessed post-state holds
    `x = 6`. -/
theorem assignXY_run_witnesses_SemIr :
    SemIr (Mem := TrivialMem) addAsmSem addOpSem [] Prog.empty
      (startState 5) assignXY assignXY_post
    ∧ readX assignXY_post = some 6 :=
  ⟨execInstrR_sound _ _ _ _ assignXY_run_ok, rfl⟩

end WorkedExample

end CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
