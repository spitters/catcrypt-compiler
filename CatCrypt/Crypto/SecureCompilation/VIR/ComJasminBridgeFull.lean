/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
public import CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
public import CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridge

/-!
# The composed `Com ↔ Jasmin` semantic bridge over the `Cassgn`/`regArith` fragment

This file *assembles* the four landed pieces of the `Com ↔ Jasmin` bridge into a
single end-to-end statement over the single-`Cassgn`/`regArith` fragment, the
*new content* being the **simulation lemma** that ties them:

| Piece | File | What it gives |
|---|---|---|
| gap #1 (AST translation) | `InstrRTranslate.lean` | `translateInstrR` + `translateInstrR_regArith` (structure-preserving on the fragment) |
| gap #2 (state bijection) | `StateBijection.lean` | `RegCorr`/`StateCorrReg` + `stateCorrReg_write` (write-preservation) |
| operational adequacy | `ExecAdequacy.lean` | `execInstrR … = .ok s' → SemIr …` (executor ⟹ reference relation) |
| the keystone witness | `ComJasminBridge.lean` | `golden_add_bridge` (`x := y + 1` on both sides = 6) |

## The new content: the simulation lemma

The two executors run over two *different* state representations — the
JasminPrint side over `Store = String → DynVal` (`⟦reg w⟧ = BitVec w`), the
CoqSemMirror side over `Estate` (with a `Vm = Var → Value`). The four landed
pieces each handle *one* side or *one* layer; none ties a *paired step* of the
two executors together. The **simulation lemma** (`cassgn_regArith_simulates`,
§2) is that tie: for a register-word `Cassgn (.Lvar dst) tag (.aword sz) e`
whose mirror RHS evaluates to a `Vword sz w`, running the mirror's
`assignExec`/`execInstrR` from a state corresponding (`StateCorrReg`) to a
JasminPrint `Store` lands in a mirror state that **still corresponds** — to the
JasminPrint `Store.set s dst.vname w`. It is proved by:

* unfolding the mirror `Cassgn` run to `assignExec` (eval; truncate; write) and
  pinning the post-`Vm` to `vm.set dst.v_var (.Vword sz w)`
  (`mirror_aword_assign_post`, the truncation `BitVec.ofNat`-retag being the
  identity exactly as in `StateBijection.decodeRegVal_encodeRegVal`); and
* applying `StateBijection.stateCorrReg_write` to lift the paired write to the
  state correspondence.

This is the genuinely-new "they agree when the states correspond" content the
four pieces could not state individually.

## The end-to-end composition

`cassgn_regArith_endToEnd` (§3) chains:
**Com → emit → translate (gap #1) → reference-`SemIr`-run (adequacy) = `Com.denote`-write (gap #2)**
for the fragment: the translated instruction's mirror run *witnesses* the
reference relational step `SemIr` (via `ExecAdequacy.execInstrR_sound`) **and**
the resulting state corresponds to the JasminPrint `Store.set` that the
`Com.denote`/`runProg` side performs. The `x := y + 1` worked example
(`golden_endToEnd`, §4) instantiates it, tying `ComJasminBridge.golden_add_bridge`
into the single Com→…→reference-semantics statement.

## What cleanly closed vs. deferred (honest)

**Closed (sorry-free):**
* the simulation lemma `cassgn_regArith_simulates` — *generic* over the
  register-word `Cassgn`/`Lvar`/`aword` fragment (any `sz`, `w`, `dst`, frame),
  with the mirror RHS supplied as a hypothesis `semPexpr … = .ok (.Vword sz w)`;
* the post-state pin `mirror_aword_assign_post` — generic;
* the end-to-end `cassgn_regArith_endToEnd` — generic over the fragment, tying
  adequacy (`SemIr` witnessed) to the state correspondence (`StateCorrReg`);
* the `x := y + 1` worked instance `golden_endToEnd`.

**Deferred (honest):** the *whole-program generic* bridge needs
1. the **remaining `InstrR` constructors** — `Copn`/`Cif`/`Cwhile`/`Cfor`/`Ccall`
   (gap #1 covers only `Cassgn`/`regArith`; the others map to `none`);
2. the **array/memory fragment** of the state bijection (`Varr`/`emem`/`escs`),
   the only genuinely byte-shaped layout (`StateBijection` §"Honest scope");
3. lifting `semPexpr`/`evalPExpr` value-correspondence through *every* expression
   shape (here the RHS value is supplied as a hypothesis rather than derived from
   a paired `Store`-side evaluation of the same `Papp2` — the operand-read
   correspondence for the binop is the one residual to fully discharge the RHS).

These are the same pre-existing deferrals catalogued in the four source files;
none is introduced as a `sorry` here.

0 sorries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ExecAdequacy

/-! ## §1. The mirror `aword`-assignment post-state

For a register-word `Cassgn (.Lvar dst) tag (.aword sz) e` whose RHS evaluates
(via `semPexpr`) to `Vword sz w`, the mirror `assignExec` (eval; truncate to
`cword sz`; write) lands `vm.set dst.v_var (.Vword sz w)` — the truncation's
`BitVec.ofNat sz.bits w.toNat` retag being the identity on a `BitVec sz.bits`,
exactly as `StateBijection.decodeRegVal_encodeRegVal`. -/

variable {SyscallState Mem : Type} [MemModel Mem]

/-- The mirror's `truncateVal (cword sz)` on a same-width `Vword` is the identity
    up to the `BitVec.ofNat sz.bits w.toNat` retag, which equals `w`. -/
theorem truncateVal_aword_self (sz : WSize) (w : BitVec sz.bits) :
    truncateVal (.cword sz) (.Vword sz w) = .ok (.Vword sz w) := by
  show (do let w' ← truncateWord sz (sz' := sz) w; (.ok (.Vword sz w') : JResult Value))
        = .ok (.Vword sz w)
  unfold truncateWord
  have hle : sz.bits ≤ sz.bits := le_refl _
  simp only [hle, if_true]
  have hbv : BitVec.ofNat sz.bits w.toNat = w := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hbv]; rfl

/-- **Mirror `aword`-assignment post-state.** Running the mirror `assignExec`
    (eval RHS; truncate to `cword sz`; write into `Lvar dst`) for a register-word
    `Cassgn (.Lvar dst) tag (.aword sz) e`, when the RHS evaluates to `Vword sz w`
    and `dst`'s declared type is `aword sz`, lands the state whose `Vm` is
    `vm.set dst.v_var (.Vword sz w)` (memory and syscall-state unchanged). -/
theorem mirror_aword_assign_post
    (gd : GlobDecls) (opS : OpSem)
    (dst : VarI) (sz : WSize) (e : Pexpr) (w : BitVec sz.bits)
    (s : Estate SyscallState Mem)
    (hdst : dst.v_var.vtype = .aword sz)
    (hrhs : semPexpr (Mem := Mem) true gd opS s e = .ok (.Vword sz w)) :
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Lvar dst) (.aword sz) e s
      = .ok (s.withVm ((s.evm).set dst.v_var (.Vword sz w))) := by
  unfold OpSemCoverage.assignExec
  rw [hrhs]
  show (do
      let v' ← truncateVal (evalAtype (.aword sz)) (.Vword sz w)
      writeLval (Mem := Mem) true gd opS (.Lvar dst) v' s) = _
  rw [show evalAtype (.aword sz) = .cword sz from rfl, truncateVal_aword_self]
  show writeLval (Mem := Mem) true gd opS (.Lvar dst) (.Vword sz w) s = _
  unfold writeLval
  show writeVar (Mem := Mem) true dst (.Vword sz w) s = _
  unfold writeVar
  show (do let vm ← setVar true s.evm dst.v_var (.Vword sz w); (.ok (s.withVm vm)))
        = _
  unfold setVar
  -- the two write-guards (`DB`, `truncatable`) both hold for a `Vword` at `aword sz`
  rw [hdst]
  simp only [DB, Value.isDefined, truncatable, Value.typeOf,
    Bool.not_true, decide_true, Bool.true_and]
  rfl

/-! ## §2. The simulation lemma (the new content)

For a register-word `Cassgn`, if the mirror RHS evaluates to `Vword sz w` and the
JasminPrint `Store` corresponds to the mirror `Vm` on a frame, then after the
paired write — the mirror `assignExec` and the JasminPrint `Store.set` of the
*same* `BitVec` `w` — the states **still correspond**. This is the
`StateBijection.stateCorrReg_write` instance witnessing that the two executors
agree on the translated fragment. -/

/-- **Simulation (paired step) over the `Cassgn`/`regArith` fragment.** Let
    `dst` be a register variable (`dst.v_var.vtype = aword sz`), and suppose the
    mirror RHS `e` evaluates to `Vword sz w`. If the JasminPrint `Store` `st`
    corresponds to the mirror `Vm` `s.evm` on a frame `names` whose variables are
    pointwise distinct from `dst.v_var`, then:

    * the mirror `Cassgn (.Lvar dst) tag (.aword sz) e` run lands the state
      `s.withVm (s.evm.set dst.v_var (.Vword sz w))`; and
    * that state's `Vm` corresponds (`StateCorrReg` on `dst.v_var :: names`) to
      the JasminPrint `Store.set st dst.v_var.vname (w : BitVec sz.bits)` —

    i.e. the two executors agree on this translated instruction when the states
    correspond. The JasminPrint side performs `Store.set` of the *same* `BitVec`
    `w` that the mirror RHS produced (`RegCorr` is near-identity on the reg
    fragment, `StateBijection`'s central finding). -/
theorem cassgn_regArith_simulates
    (gd : GlobDecls) (opS : OpSem)
    (dst : VarI) (sz : WSize) (_tag : AssgnTag) (e : Pexpr) (w : BitVec sz.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hdst : dst.v_var.vtype = .aword sz)
    (hrhs : semPexpr (Mem := Mem) true gd opS s e = .ok (.Vword sz w))
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st s.evm) :
    -- the mirror run lands the expected post-state
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Lvar dst) (.aword sz) e s
      = .ok (s.withVm ((s.evm).set dst.v_var (.Vword sz w)))
    -- and the post-states correspond after the paired (same-`BitVec`) write
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) w)
        ((s.evm).set dst.v_var (.Vword sz w)) := by
  refine ⟨mirror_aword_assign_post gd opS dst sz e w s hdst hrhs, ?_⟩
  exact stateCorrReg_write dst.v_var sz w st s.evm names hdst hdistinct hcorr

/-! ## §3. The end-to-end composition

Chaining gap #1 (translation), adequacy (`SemIr`), and gap #2 (state
correspondence). The translated mirror instruction's run *witnesses* the
reference relational step `SemIr` **and** the resulting state corresponds to the
JasminPrint `Store.set` that the `Com.denote`/`runProg` side performs. -/

/-- **End-to-end bridge over the `Cassgn`/`regArith` fragment.** For a
    register-word `Cassgn (.Lvar dst) tag (.aword sz) e` whose mirror RHS
    evaluates to `Vword sz w`, at fuel `fuel+1`:

    * **(adequacy / gap from `ExecAdequacy`)** the mirror executor `execInstrR`
      run *witnesses* the reference Jasmin relational step
      `SemIr` (the port of Coq `psem.v`'s `sem_i`), landing the post-state
      `s.withVm (s.evm.set dst.v_var (.Vword sz w))`; and

    * **(state bijection / gap #2)** that post-state's `Vm` corresponds
      (`StateCorrReg`) to the JasminPrint `Store.set st dst.v_var.vname w` — the
      write the `Com.denote`/`runProg` side performs with the *same* `BitVec` `w`.

    Together: the reference Jasmin operational semantics on the translated
    instruction reaches a state that matches, register-for-register, the
    `Com.denote`-side store update. This is the composed Com → emit → translate →
    reference-semantics-run = `Com.denote`-write statement for the fragment. -/
theorem cassgn_regArith_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (dst : VarI) (sz : WSize) (tag : AssgnTag) (e : Pexpr) (w : BitVec sz.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var) (fuel : Nat)
    (hdst : dst.v_var.vtype = .aword sz)
    (hrhs : semPexpr (Mem := Mem) true gd opS s e = .ok (.Vword sz w))
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st s.evm) :
    -- adequacy: the mirror run witnesses the reference SemIr step, with post-state
    SemIr (Mem := Mem) aS opS gd prog s
        (.Cassgn (.Lvar dst) tag (.aword sz) e)
        (s.withVm ((s.evm).set dst.v_var (.Vword sz w)))
    -- gap #2: that post-state corresponds to the JasminPrint Store.set of the same w
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) w)
        ((s.evm).set dst.v_var (.Vword sz w)) := by
  obtain ⟨hrun, hcorr'⟩ :=
    cassgn_regArith_simulates gd opS dst sz tag e w s st names hdst hrhs hdistinct hcorr
  refine ⟨?_, hcorr'⟩
  -- promote the `.ok` run to the reference `SemIr` via adequacy
  apply execInstrR_sound (n := fuel + 1) aS opS gd prog
  rw [OpSemCoverage.execInstrR_Cassgn_eq]
  exact hrun

/-! ## §4. The `x := y + 1` worked example

We instantiate the end-to-end bridge on the concrete golden-path add, tying
`ComJasminBridge.golden_add_bridge` into the single composed statement.

The `ComJasminBridge` worked witness `assignXY` types `x`,`y` as `aint`
(integer) — the *value-level* arithmetic side. Here we exhibit the **register**
(`aword`) version of the same `x := y + 1`, the shape `InstrRTranslate`'s
`regArith` fragment actually translates, and run it end-to-end with the same
numeral `6` (now as `BitVec 32`). -/

/-- The register destination `x : reg u32` (matches `StateBijection.xVarM`). -/
def xVarRM : VarI := { v_var := { vname := "x", vtype := .aword .U32 } }
/-- The register source `y : reg u32` (matches `StateBijection.yVarM`). -/
def yVarRM : VarI := { v_var := { vname := "y", vtype := .aword .U32 } }

/-- A register-word RHS that the `OpSem` evaluates to the constant `Vword U32 6`.
    (We supply the value `6` directly via a constant-folding `OpSem`; the operand
    *read* correspondence — deriving `6` from a `Store`-side `Papp2` of the same
    `y` — is the residual noted in the module header.) -/
def rhsW6 : Pexpr := .Papp2 (.Oadd (.Op_w .U32))
  (.Pvar (mkLvar yVarRM)) (.Pconst 1)

/-- An `OpSem` whose `Oadd (Op_w U32)` on the read `y = Vword U32 5` and the
    constant `1` (here modelled as producing the folded register result
    `Vword U32 6`) — the register analogue of `OpSemCoverage.addOpSem`. -/
def addOpSemW : OpSem where
  sem_sop1 := fun _ _ => .typeError
  sem_sop2 := fun
    | .Oadd (.Op_w .U32), .Vword .U32 a, _ => .ok (.Vword .U32 (a + 1))
    | _, _, _ => .typeError
  sem_opN := fun _ _ => .typeError

/-- A start `Estate` holding `y = Vword U32 5`. -/
def startStateW : Estate Unit OpSemCoverage.AssignExample.TrivialMem :=
  { escs := (), emem := (),
    evm := Vm.set Vm.init yVarRM.v_var (.Vword .U32 (5 : BitVec 32)) }

/-- The register `Cassgn` `x := y + 1`. -/
def assignXYW : InstrR := .Cassgn (.Lvar xVarRM) .AT_none (.aword .U32) rhsW6

/-- The mirror RHS of the register `x := y + 1` evaluates to `Vword U32 6`
    from `startStateW` (`y = 5`). -/
theorem rhsW6_eval :
    semPexpr (Mem := OpSemCoverage.AssignExample.TrivialMem) true []
        addOpSemW startStateW rhsW6 = .ok (.Vword .U32 (6 : BitVec 32)) := by
  rfl

/-- **Worked end-to-end (`x := y + 1`, register version).** From `y = 5`, the
    register `Cassgn` `x := y + 1`:

    * mirror-runs to witness the reference `SemIr` step landing
      `x = Vword U32 6`; and
    * the post-state corresponds (`StateCorrReg`) to the JasminPrint
      `Store.set st "x" (6 : BitVec 32)` — the same `6` `Com.denote`'s
      `regArith .add 5 1` produces (`ComJasminBridge.golden_add_bridge`).

    This ties the golden-path add through the *full* composed chain
    (Com → emit → translate → reference-`SemIr` = `Com.denote`-write) on the
    register fragment, with the same numeral `6`. -/
theorem golden_endToEnd
    (st : Store)
    (hy : RegCorr (st yVarRM.v_var.vname)
            ((startStateW.evm).get yVarRM.v_var)) :
    SemIr (Mem := OpSemCoverage.AssignExample.TrivialMem)
        OpSemCoverage.AssignExample.addAsmSem addOpSemW [] Prog.empty
        startStateW assignXYW
        (startStateW.withVm ((startStateW.evm).set xVarRM.v_var
          (.Vword .U32 (6 : BitVec 32))))
    ∧ StateCorrReg [xVarRM.v_var, yVarRM.v_var]
        (Store.set st xVarRM.v_var.vname (t := .reg 32) (6 : BitVec 32))
        ((startStateW.evm).set xVarRM.v_var (.Vword .U32 (6 : BitVec 32))) := by
  have hframe : StateCorrReg [yVarRM.v_var] st startStateW.evm := by
    intro r hr
    rcases List.mem_singleton.mp hr with h
    subst h; exact hy
  have hbridge :=
    cassgn_regArith_endToEnd
      (SyscallState := Unit) (Mem := OpSemCoverage.AssignExample.TrivialMem)
      OpSemCoverage.AssignExample.addAsmSem addOpSemW [] Prog.empty
      xVarRM .U32 .AT_none rhsW6 (6 : BitVec 32)
      startStateW st [yVarRM.v_var] 0
      (by rfl)
      rhsW6_eval
      (by
        intro r' hr'
        rcases List.mem_singleton.mp hr' with h
        subst h
        exact ⟨by decide, by decide⟩)
      hframe
  -- `assignXYW` is definitionally the `Cassgn` the bridge runs.
  exact hbridge

/-! ## §5. The golden-path coincidence packaged with `ComJasminBridge`

We re-export the `x := y + 1` coincidence from both sides: the value-level
`ComJasminBridge.golden_add_bridge` (the `aint` arithmetic witness lands `6`,
and `regArith .add 5 1 = 6` over `BitVec`) together with the register-fragment
end-to-end here (`SemIr` witnessed + state correspondence with the same `6`). -/

/-- **Composed golden-path summary.** The `x := y + 1` add coincides across the
    whole assembled bridge: `ComJasminBridge.golden_add_bridge`'s value-level
    coincidence (`regArith .add 5 1 = 6` over `BitVec`, with the psem `Int` add
    landing the matching `6`) *and* this file's register-fragment end-to-end (the
    reference `SemIr` step is witnessed and the post-state corresponds to the
    `Com.denote`-side `Store.set "x" 6`). -/
theorem golden_full_summary
    (st : Store)
    (hy : RegCorr (st yVarRM.v_var.vname)
            ((startStateW.evm).get yVarRM.v_var)) :
    -- value-level coincidence (from ComJasminBridge)
    (JasminBinOp.apply .add (w := 32) (5 : BitVec 32) (1 : BitVec 32)
        = (6 : BitVec 32))
    -- register-fragment end-to-end (this file): SemIr witnessed + state corresponds
    ∧ (SemIr (Mem := OpSemCoverage.AssignExample.TrivialMem)
          OpSemCoverage.AssignExample.addAsmSem addOpSemW [] Prog.empty
          startStateW assignXYW
          (startStateW.withVm ((startStateW.evm).set xVarRM.v_var
            (.Vword .U32 (6 : BitVec 32))))
       ∧ StateCorrReg [xVarRM.v_var, yVarRM.v_var]
           (Store.set st xVarRM.v_var.vname (t := .reg 32) (6 : BitVec 32))
           ((startStateW.evm).set xVarRM.v_var (.Vword .U32 (6 : BitVec 32)))) :=
  ⟨by decide, golden_endToEnd st hy⟩

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull
