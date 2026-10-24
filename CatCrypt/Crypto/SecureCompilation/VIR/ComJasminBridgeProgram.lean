/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeMem
public import CatCrypt.Crypto.SecureCompilation.VIR.ExecCompleteness
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# Whole-program rules for `Copn`, `Cfor` and `Ccall` over the `psem.v` mirror

The per-instruction bridges `ComJasminBridgeCopn`, `ComJasminBridgeFor` and
`ComJasminBridgeCall` relate one emitted instruction of a fixed shape to the
JasminPrint store: the rotate `Copn`, a counted loop whose body is a block of
assignments and rotates, and a call whose callee run is a hypothesis. This module
states rules over the relational semantics `Sem` / `SemIr` of
`JasminCoqSemMirror` that compose: a loop body and a callee body are arbitrary
commands, related by the same correspondence judgment as the enclosing program.

## The correspondence

`CorresSem aS opS gd prog SR P fa c` is the forward simulation of `Ascent.Corres`
(over `semScalar`) and `Ascent.CorresJ` (over `runBlock`) stated over `Sem`: from a
mirror state `s` related by `SR` to an abstract state `a` with `P a`, the command
`c` has a derivation `Sem s c s'` to a state related to `fa a`. `CorresSemIr` is
the same for one raw instruction. `corresSem_append` sequences, `corresSem_instr`
lifts an instruction, and `corresSem_exec` reads a correspondence back as a run of
the fuel-bounded executor (`ExecCompleteness.execCmd_adequacy`).

## `Copn` over registers and flags

`OpnArg` is an operand of an asm operation (a word register, a flag variable, or
an integer immediate) and `OpnOut` a result (a word written to a register, a flag
written to a boolean variable, or a flag discarded through `Lnone`).
`copn_regs_semIr` states the effect of `Copn (outs.map lval) tag o (args.map expr)`
when the asm semantics maps the operand values to the result values: the variable
map is `applyOuts outs`, and memory and syscall state are unchanged, since no
result is written through `Lmem`. `stateCorrReg_applyOuts` carries `StateCorrReg`
across the writes. `x86AsmSem` gives `MULX_64`, `ADCX_64` and `CMOVcc_64` the
result tuples of `X86Backend.Jasmin.x86_MULX_lo_hi`, `x86_ADCX` and `x86_CMOVcc`,
in the output order of Jasmin's instruction descriptors (`MULX`: low then high
word; `ADCX`: carry flag then word).

## `Cfor`

`corresSem_for` is the counted-loop rule for the emitted range
`ComJasminBridgeFor.forRange n`: when the body, run from a state with the index
written to `k`, corresponds at the abstract step `step k` for every `k < n`, the
loop corresponds at `forFold step n`. `forFold` has the recursion of
`Ascent.loopStep` (the abstract loop of `corresJ_loop`) and of `Ascent.nfold` (the
abstract loop of `corres_for`); `Ascent.JasminMirrorTie` proves the equations.

## `Cwhile`

`corresSem_while` is the rule for `while (e) { body }` with an empty prefix command:
when the guard evaluates to `cond a` from every related state, the body corresponds at
`step` while the guard holds, and `count a` is an iteration count at which the guard
first fails, the loop corresponds at `iterFold step (count a)`, the `count a`-fold
iterate of `step` (`forFold` at an index-independent step). `semIr_while_iter` is the
derivation of the `Ewhile_true`/`Ewhile_false` chain by induction on the count.

## `Ccall`

`ccall_words_semIr` is the call rule for a callee defined in the program whose
parameters and results are word registers: from a derivation of the callee body
started at the parameter map `paramVm ps Vm.init`, with the result registers
holding their words at its end, the call writes the results into the caller's
l-values and the caller resumes with the callee's memory and syscall state. The
callee body derivation is itself produced by these rules, so nested calls compose.
`ccall_leaf_of_body` derives the conclusion of
`ComJasminBridgeCall.ccall_leaf_endToEnd` for the emitted one-result call from a
callee body derivation.

## Worked instance

`MulhiLoop.mainLoop_sem`: the loop `for i = 0 to n { h = mulhi(h, b) }`, where
`mulhi` is a function whose body is one `MULX_64` `Copn`, runs under `x86AsmSem`
to a state holding `forFold (hiStep b) n h0` at `h`, with memory unchanged.

## Main results

* `corresSem_nil`, `corresSem_append`, `corresSem_instr`, `corresSem_weaken`: the
  empty command, sequencing, one instruction and precondition strengthening.
* `corresSem_exec`: a correspondence is realised by `execCmd` at some fuel.
* `copn_regs_semIr`: the effect of a register-and-flag `Copn` whose asm semantics
  maps the operand values to the result values.
* `stateCorrReg_applyOuts`: `StateCorrReg` is carried across the result writes.
* `corresSem_for`: the counted loop `Cfor i (0..n) body` corresponds at `forFold step n`.
* `corresSem_while`: the loop `while (e) { body }` corresponds at
  `iterFold step (count a)`, given the guard and a first-failing iteration count.
* `ccall_words_semIr`: the call rule for word parameters and results.
* `ccall_leaf_of_body`: the emitted one-result call from a callee body derivation.
* `MulhiLoop.mainLoop_sem`: the worked instance above.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. The correspondence over `Sem` -/

section Rules
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- Derivations of `Sem` compose along command concatenation. -/
theorem sem_append {s s1 s2 : Estate SyscallState Mem} {c1 c2 : Cmd}
    (h1 : Sem aS opS gd prog s c1 s1) (h2 : Sem aS opS gd prog s1 c2 s2) :
    Sem aS opS gd prog s (c1 ++ c2) s2 := by
  induction c1 generalizing s with
  | nil => cases h1; exact h2
  | cons i c ih =>
    cases h1 with
    | Eseq _ s' _ _ _ hi hc => exact .Eseq _ _ _ _ _ hi (ih hc)

/-- `CorresSem aS opS gd prog SR P fa c`: from every mirror state `s` related by
    `SR` to an abstract state `a` with `P a`, the command `c` has a `Sem`
    derivation to a state related to `fa a`. -/
def CorresSem {A : Type} (SR : Estate SyscallState Mem → A → Prop) (P : A → Prop)
    (fa : A → A) (c : Cmd) : Prop :=
  ∀ s a, SR s a → P a → ∃ s', Sem aS opS gd prog s c s' ∧ SR s' (fa a)

/-- `CorresSem` for one raw instruction, over `SemIr`. -/
def CorresSemIr {A : Type} (SR : Estate SyscallState Mem → A → Prop) (P : A → Prop)
    (fa : A → A) (i : InstrR) : Prop :=
  ∀ s a, SR s a → P a → ∃ s', SemIr aS opS gd prog s i s' ∧ SR s' (fa a)

variable {aS opS gd prog} {A : Type} (SR : Estate SyscallState Mem → A → Prop)

/-- The empty command corresponds at the identity. -/
theorem corresSem_nil : CorresSem aS opS gd prog SR (fun _ => True) id [] :=
  fun s _ hSR _ => ⟨s, .Eskip s, hSR⟩

/-- Strengthening the precondition. -/
theorem corresSem_weaken {P P' : A → Prop} {fa : A → A} {c : Cmd}
    (h : CorresSem aS opS gd prog SR P fa c) (hP : ∀ a, P' a → P a) :
    CorresSem aS opS gd prog SR P' fa c :=
  fun s a hSR hP' => h s a hSR (hP a hP')

/-- Sequencing: `c1 ++ c2` corresponds at `ga ∘ fa` when `fa` preserves `P`. -/
theorem corresSem_append {P : A → Prop} {fa ga : A → A} {c1 c2 : Cmd}
    (h1 : CorresSem aS opS gd prog SR P fa c1) (h2 : CorresSem aS opS gd prog SR P ga c2)
    (hinv : ∀ a, P a → P (fa a)) :
    CorresSem aS opS gd prog SR P (fun a => ga (fa a)) (c1 ++ c2) := by
  intro s a hSR hP
  obtain ⟨s1, hs1, hSR1⟩ := h1 s a hSR hP
  obtain ⟨s2, hs2, hSR2⟩ := h2 s1 (fa a) hSR1 (hinv a hP)
  exact ⟨s2, sem_append aS opS gd prog hs1 hs2, hSR2⟩

/-- A corresponding raw instruction is a corresponding one-instruction command. -/
theorem corresSem_instr {P : A → Prop} {fa : A → A} {i : InstrR} (ii : InstrInfo)
    (h : CorresSemIr aS opS gd prog SR P fa i) :
    CorresSem aS opS gd prog SR P fa [.MkI ii i] := by
  intro s a hSR hP
  obtain ⟨s', hs', hSR'⟩ := h s a hSR hP
  exact ⟨s', .Eseq _ _ _ _ _ (.EmkI ii i _ _ hs') (.Eskip _), hSR'⟩

/-- A correspondence is realised by the fuel-bounded executor `execCmd` at some
    fuel. -/
theorem corresSem_exec {P : A → Prop} {fa : A → A} {c : Cmd}
    (h : CorresSem aS opS gd prog SR P fa c) (s : Estate SyscallState Mem) (a : A)
    (hSR : SR s a) (hP : P a) :
    ∃ s' fuel, execCmd aS opS gd fuel s c prog = .ok s' ∧ SR s' (fa a) := by
  obtain ⟨s', hs', hSR'⟩ := h s a hSR hP
  obtain ⟨fuel, hrun⟩ := (ExecCompleteness.execCmd_adequacy aS opS gd prog).2 hs'
  exact ⟨s', fuel, hrun, hSR'⟩

end Rules

/-! ## §2. `Copn` over registers and flags -/

section Copn

/-- An operand of an asm operation: a word register holding `w`, a boolean flag
    variable holding `b`, or the integer immediate `z`. -/
inductive OpnArg where
  | word (src : VarI) (sz : WSize) (w : BitVec sz.bits)
  | flag (src : VarI) (b : Bool)
  | imm (z : Int)

/-- The operand expression. -/
def OpnArg.expr : OpnArg → Pexpr
  | .word src _ _ => .Pvar (mkLvar src)
  | .flag src _ => .Pvar (mkLvar src)
  | .imm z => .Pconst z

/-- The operand value. -/
def OpnArg.value : OpnArg → Value
  | .word _ sz w => .Vword sz w
  | .flag _ b => .Vbool b
  | .imm z => .Vint z

/-- The state holds the operand's value at its variable. -/
def OpnArg.Holds (s : Estate SyscallState Mem) : OpnArg → Prop
  | .word src sz w => (s.evm).get src.v_var = .Vword sz w
  | .flag src b => (s.evm).get src.v_var = .Vbool b
  | .imm _ => True

/-- A result of an asm operation: a word written to the register `dst`, a flag
    written to the boolean variable `dst`, or a flag value discarded by `Lnone`. -/
inductive OpnOut where
  | word (dst : VarI) (sz : WSize) (w : BitVec sz.bits)
  | flag (dst : VarI) (b : Bool)
  | drop (f : Value)

/-- The l-value receiving the result. -/
def OpnOut.lval : OpnOut → Lval
  | .word dst _ _ => .Lvar dst
  | .flag dst _ => .Lvar dst
  | .drop _ => .Lnone () .abool

/-- The result value. -/
def OpnOut.value : OpnOut → Value
  | .word _ sz w => .Vword sz w
  | .flag _ b => .Vbool b
  | .drop f => f

/-- The l-value accepts the result: the register or flag variable has the result's
    type, and a discarded value is a writable flag. -/
def OpnOut.Typed : OpnOut → Prop
  | .word dst sz _ => dst.v_var.vtype = .aword sz
  | .flag dst _ => dst.v_var.vtype = .abool
  | .drop f => ComJasminBridgeCopn.FlagWritable f

/-- The variable-map update of one result. -/
def OpnOut.applyVm : OpnOut → Vm → Vm
  | .word dst sz w, vm => vm.set dst.v_var (.Vword sz w)
  | .flag dst b, vm => vm.set dst.v_var (.Vbool b)
  | .drop _, vm => vm

/-- The variable-map update of a list of results, left to right. -/
def applyOuts (outs : List OpnOut) (vm : Vm) : Vm :=
  outs.foldl (fun vm o => o.applyVm vm) vm

/-- The mirror evaluates operands to their values. -/
theorem semPexprs_opnArgs (gd : GlobDecls) (opS : OpSem)
    (s : Estate SyscallState Mem) :
    ∀ (args : List OpnArg), (∀ a ∈ args, a.Holds s) →
      semPexprs (Mem := Mem) true gd opS s (args.map OpnArg.expr)
        = .ok (args.map OpnArg.value)
  | [], _ => rfl
  | a :: rest, h => by
    have ha : semPexpr (Mem := Mem) true gd opS s a.expr = .ok a.value := by
      have hh := h a List.mem_cons_self
      cases a with
      | word src sz w => exact OperandReadCorr.semPexpr_pvar_vword gd opS s src sz w hh
      | flag src b =>
        show getGvar true gd s.evm (mkLvar src) = _
        unfold getGvar
        rw [show (mkLvar src).isLvar = true from rfl]
        simp only [ite_true]
        show getVar true s.evm (mkLvar src).gv.v_var = _
        unfold getVar
        rw [show (mkLvar src).gv.v_var = src.v_var from rfl]
        simp only [OpnArg.Holds] at hh
        rw [hh]
        rfl
      | imm z => rfl
    have hrest := semPexprs_opnArgs gd opS s rest
      (fun b hb => h b (List.mem_cons_of_mem a hb))
    show (do
        let v ← semPexpr (Mem := Mem) true gd opS s a.expr
        let vs ← semPexprList (Mem := Mem) true gd opS s (rest.map OpnArg.expr)
        .ok (v :: vs)) = _
    rw [ha]
    show (do
        let vs ← semPexprs (Mem := Mem) true gd opS s (rest.map OpnArg.expr)
        (.ok (a.value :: vs) : JResult Values)) = _
    rw [hrest]
    rfl

/-- Writing a typed result updates only the variable map. -/
theorem writeLval_opnOut (gd : GlobDecls) (opS : OpSem)
    (s : Estate SyscallState Mem) (o : OpnOut) (ho : o.Typed) :
    writeLval (Mem := Mem) true gd opS o.lval o.value s = .ok (s.withVm (o.applyVm s.evm)) := by
  cases o with
  | word dst sz w =>
    show writeVar (Mem := Mem) true dst (.Vword sz w) s = _
    unfold writeVar setVar
    simp only [OpnOut.Typed] at ho
    rw [ho]
    simp only [DB, Value.isDefined, truncatable, Value.typeOf,
      Bool.not_true, decide_true, Bool.true_and]
    rfl
  | flag dst b =>
    show writeVar (Mem := Mem) true dst (.Vbool b) s = _
    unfold writeVar setVar
    simp only [OpnOut.Typed] at ho
    rw [ho]
    simp only [DB, Value.isDefined, truncatable, Value.typeOf,
      Bool.not_true, decide_true, Bool.true_and]
    rfl
  | drop f =>
    show writeNone (Mem := Mem) s .cbool f = _
    rw [ComJasminBridgeCopn.writeNone_flag s f ho]
    rfl

/-- Writing a list of typed results is `applyOuts` on the variable map. -/
theorem writeLvals_opnOuts (gd : GlobDecls) (opS : OpSem) :
    ∀ (outs : List OpnOut) (s : Estate SyscallState Mem), (∀ o ∈ outs, o.Typed) →
      writeLvals (Mem := Mem) true gd opS s (outs.map OpnOut.lval) (outs.map OpnOut.value)
        = .ok (s.withVm (applyOuts outs s.evm))
  | [], s, _ => rfl
  | o :: rest, s, h => by
    show (do
        let s1 ← writeLval (Mem := Mem) true gd opS o.lval o.value s
        writeLvals (Mem := Mem) true gd opS s1 (rest.map OpnOut.lval) (rest.map OpnOut.value))
      = _
    rw [writeLval_opnOut gd opS s o (h o List.mem_cons_self)]
    show writeLvals (Mem := Mem) true gd opS (s.withVm (o.applyVm s.evm))
        (rest.map OpnOut.lval) (rest.map OpnOut.value) = _
    rw [writeLvals_opnOuts gd opS rest _ (fun b hb => h b (List.mem_cons_of_mem o hb))]
    rfl

/-- **The `Copn` step over registers and flags.** When the operands hold their
    values and the asm semantics maps the operand values to the result values,
    `semSopn` updates the variable map by `applyOuts outs` and leaves memory and
    syscall state unchanged. -/
theorem copn_regs_semSopn (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (o : Sopn) (args : List OpnArg) (outs : List OpnOut) (s : Estate SyscallState Mem)
    (hargs : ∀ a ∈ args, a.Holds s)
    (hasm : aS.sopn_sem o (args.map OpnArg.value) = .ok (outs.map OpnOut.value))
    (htyped : ∀ x ∈ outs, x.Typed) :
    semSopn (Mem := Mem) aS opS gd o s (outs.map OpnOut.lval) (args.map OpnArg.expr)
      = .ok (s.withVm (applyOuts outs s.evm)) := by
  unfold semSopn
  rw [semPexprs_opnArgs gd opS s args hargs]
  show (do let rs ← aS.sopn_sem o (args.map OpnArg.value)
           writeLvals (Mem := Mem) true gd opS s (outs.map OpnOut.lval) rs) = _
  rw [hasm]
  exact writeLvals_opnOuts gd opS outs s htyped

/-- The relational `SemIr` form of `copn_regs_semSopn`. -/
theorem copn_regs_semIr (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (tag : AssgnTag) (o : Sopn) (args : List OpnArg) (outs : List OpnOut)
    (s : Estate SyscallState Mem)
    (hargs : ∀ a ∈ args, a.Holds s)
    (hasm : aS.sopn_sem o (args.map OpnArg.value) = .ok (outs.map OpnOut.value))
    (htyped : ∀ x ∈ outs, x.Typed) :
    SemIr aS opS gd prog s (.Copn (outs.map OpnOut.lval) tag o (args.map OpnArg.expr))
      (s.withVm (applyOuts outs s.evm)) :=
  .Eopn _ _ tag o _ _ (copn_regs_semSopn aS opS gd o args outs s hargs hasm htyped)

/-- The rotate `Copn` of `ComJasminBridgeCopn` is an instance of the operand and
    result lists: two discarded flags and one word, over a word register and an
    immediate. -/
theorem ror_as_opn (dst src : VarI) (sz : WSize) (n : Nat) (w : BitVec sz.bits)
    (f1 f2 : Value) :
    ComJasminBridgeCopn.rorLvals dst
        = [OpnOut.drop f1, .drop f2, .word dst sz (w.rotateRight n)].map OpnOut.lval
    ∧ ComJasminBridgeCopn.rorArgs src n
        = [OpnArg.word src sz w, .imm (Int.ofNat n)].map OpnArg.expr :=
  ⟨rfl, rfl⟩

/-- The results are fresh for the register frame: each written register is
    distinct from the frame at the point of its write, and each written flag
    variable is outside the frame. -/
def OutsFresh : List Var → List OpnOut → Prop
  | _, [] => True
  | names, .word dst _ _ :: rest =>
      (∀ r ∈ names, r ≠ dst.v_var ∧ r.vname ≠ dst.v_var.vname) ∧
        OutsFresh (dst.v_var :: names) rest
  | names, .flag dst _ :: rest => (∀ r ∈ names, r ≠ dst.v_var) ∧ OutsFresh names rest
  | names, .drop _ :: rest => OutsFresh names rest

/-- The register frame after the results: each written register is added. -/
def outsFrame : List Var → List OpnOut → List Var
  | names, [] => names
  | names, .word dst _ _ :: rest => outsFrame (dst.v_var :: names) rest
  | names, _ :: rest => outsFrame names rest

open JasminPrintSemCorrect in
/-- The JasminPrint store after the results: each word result is stored at its
    register. -/
def outsStore : Store → List OpnOut → Store
  | st, [] => st
  | st, .word dst sz w :: rest =>
      outsStore (Store.set st dst.v_var.vname (t := .reg sz.bits) w) rest
  | st, _ :: rest => outsStore st rest

open StateBijection JasminPrintSemCorrect in
/-- `StateCorrReg` is carried across the result writes of a `Copn`. -/
theorem stateCorrReg_applyOuts :
    ∀ (outs : List OpnOut) (names : List Var) (st : Store) (vm : Vm),
      (∀ x ∈ outs, x.Typed) → OutsFresh names outs → StateCorrReg names st vm →
      StateCorrReg (outsFrame names outs) (outsStore st outs) (applyOuts outs vm)
  | [], _, _, _, _, _, h => h
  | .word dst sz w :: rest, names, st, vm, ht, hf, h =>
      stateCorrReg_applyOuts rest _ _ _ (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hf.2
        (stateCorrReg_write dst.v_var sz w st vm names (ht _ List.mem_cons_self) hf.1 h)
  | .flag dst b :: rest, names, st, vm, ht, hf, h =>
      stateCorrReg_applyOuts rest _ _ _ (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hf.2
        (ComJasminBridgeFor.stateCorrReg_set_outside names st vm dst.v_var (.Vbool b) hf.1 h)
  | .drop _ :: rest, _, _, _, ht, hf, h =>
      stateCorrReg_applyOuts rest _ _ _ (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hf h

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin in
/-- Asm semantics for three 64-bit x86 operations, with the result tuples of the
    x86 transcription `X86Backend.Jasmin`: `MULX_64 a b` returns the low and high
    words of `x86_MULX_lo_hi`; `ADCX_64 a b c` returns the carry flag and the word
    of `x86_ADCX`; `CMOVcc_64 c a b` returns `x86_CMOVcc c a b`. Every other
    application is a type error. -/
def x86AsmSem : AsmSem where
  sopn_sem := fun
    | .Oasm op, [.Vword .U64 a, .Vword .U64 b] =>
        if op = "MULX_64" then
          .ok [.Vword .U64 (x86_MULX_lo_hi a b).1, .Vword .U64 (x86_MULX_lo_hi a b).2]
        else .typeError
    | .Oasm op, [.Vword .U64 a, .Vword .U64 b, .Vbool c] =>
        if op = "ADCX_64" then
          .ok [.Vbool ((x86_ADCX a b c).1.getD false), .Vword .U64 (x86_ADCX a b c).2]
        else .typeError
    | .Oasm op, [.Vbool c, .Vword .U64 a, .Vword .U64 b] =>
        if op = "CMOVcc_64" then .ok [.Vword .U64 (x86_CMOVcc c a b)]
        else .typeError
    | _, _ => .typeError

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin in
/-- `MULX_64` under `x86AsmSem`. -/
theorem x86AsmSem_mulx (a b : BitVec 64) :
    x86AsmSem.sopn_sem (.Oasm "MULX_64") [.Vword .U64 a, .Vword .U64 b]
      = .ok [.Vword .U64 (x86_MULX_lo_hi a b).1, .Vword .U64 (x86_MULX_lo_hi a b).2] := by
  show (if "MULX_64" = "MULX_64" then
      (.ok [.Vword .U64 (x86_MULX_lo_hi a b).1, .Vword .U64 (x86_MULX_lo_hi a b).2] :
        JResult Values) else .typeError) = _
  rw [ite_eq_left rfl]

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin in
/-- `ADCX_64` under `x86AsmSem`. -/
theorem x86AsmSem_adcx (a b : BitVec 64) (c : Bool) :
    x86AsmSem.sopn_sem (.Oasm "ADCX_64") [.Vword .U64 a, .Vword .U64 b, .Vbool c]
      = .ok [.Vbool ((x86_ADCX a b c).1.getD false), .Vword .U64 (x86_ADCX a b c).2] := by
  show (if "ADCX_64" = "ADCX_64" then
      (.ok [.Vbool ((x86_ADCX a b c).1.getD false), .Vword .U64 (x86_ADCX a b c).2] :
        JResult Values) else .typeError) = _
  rw [ite_eq_left rfl]

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin in
/-- `CMOVcc_64` under `x86AsmSem`. -/
theorem x86AsmSem_cmov (a b : BitVec 64) (c : Bool) :
    x86AsmSem.sopn_sem (.Oasm "CMOVcc_64") [.Vbool c, .Vword .U64 a, .Vword .U64 b]
      = .ok [.Vword .U64 (x86_CMOVcc c a b)] := by
  show (if "CMOVcc_64" = "CMOVcc_64" then
      (.ok [.Vword .U64 (x86_CMOVcc c a b)] : JResult Values) else .typeError) = _
  rw [ite_eq_left rfl]

end Copn

/-! ## §3. The counted loop -/

section For
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- The abstract counted loop `step (n-1) ∘ … ∘ step 0`. -/
def forFold {A : Type} (step : Nat → A → A) : Nat → A → A
  | 0 => id
  | n + 1 => fun a => step n (forFold step n a)

/-- `forFold` preserves an invariant of every step. -/
theorem forFold_preserves {A : Type} {P : A → Prop} {step : Nat → A → A}
    (hinv : ∀ k a, P a → P (step k a)) : ∀ n a, P a → P (forFold step n a) := by
  intro n
  induction n with
  | zero => intro a ha; exact ha
  | succ k ih => intro a ha; exact hinv k _ (ih a ha)

/-- The iterations `k, …, n-1` of the loop, from a state related to
    `forFold step k a`, have a `SemFor` derivation to a state related to
    `forFold step n a`. -/
theorem semFor_range {A : Type} (SR : Estate SyscallState Mem → A → Prop) (P : A → Prop)
    (step : Nat → A → A) (i : VarI) (n : Nat) (body : Cmd)
    (hi : i.v_var.vtype = .aint)
    (hbody : ∀ k < n, ∀ s a, SR s a → P a → ∃ s',
        Sem aS opS gd prog (s.withVm ((s.evm).set i.v_var (.Vint (Int.ofNat k)))) body s'
          ∧ SR s' (step k a))
    (hinv : ∀ k a, P a → P (step k a)) (a : A) (hP : P a) :
    ∀ m k s, k + m = n → SR s (forFold step k a) → ∃ s',
      SemFor aS opS gd prog i ((List.range' k m).map Int.ofNat) s body s'
        ∧ SR s' (forFold step n a) := by
  intro m
  induction m with
  | zero =>
    intro k s hk hSR
    simp only [Nat.add_zero] at hk
    subst hk
    exact ⟨s, .EForDone s i body, hSR⟩
  | succ m ih =>
    intro k s hk hSR
    obtain ⟨s1, hs1, hSR1⟩ := hbody k (by omega) s (forFold step k a) hSR
      (forFold_preserves hinv k a hP)
    obtain ⟨s2, hs2, hSR2⟩ := ih (k + 1) s1 (by omega) hSR1
    refine ⟨s2, ?_, hSR2⟩
    rw [List.range'_succ, List.map_cons]
    exact .EForOne _ _ _ _ i _ _ body
      (ComJasminBridgeFor.writeVar_index i _ s hi) hs1 hs2

/-- **The counted-loop rule.** Let the index `i` be an `int` variable. If for
    every `k < n` the body, run from a state related to `a` with the index written
    to `k`, corresponds at `step k`, and every step preserves `P`, then the emitted
    loop `Cfor i (0..n) body` corresponds at `forFold step n`. -/
theorem corresSem_for {A : Type} (SR : Estate SyscallState Mem → A → Prop) (P : A → Prop)
    (step : Nat → A → A) (i : VarI) (n : Nat) (body : Cmd)
    (hi : i.v_var.vtype = .aint)
    (hbody : ∀ k < n, ∀ s a, SR s a → P a → ∃ s',
        Sem aS opS gd prog (s.withVm ((s.evm).set i.v_var (.Vint (Int.ofNat k)))) body s'
          ∧ SR s' (step k a))
    (hinv : ∀ k a, P a → P (step k a)) :
    CorresSemIr aS opS gd prog SR P (forFold step n)
      (.Cfor i (ComJasminBridgeFor.forRange n) body) := by
  intro s a hSR hP
  obtain ⟨s', hs', hSR'⟩ :=
    semFor_range aS opS gd prog SR P step i n body hi hbody hinv a hP n 0 s (Nat.zero_add n) hSR
  refine ⟨s', ?_, hSR'⟩
  refine .Efor _ _ i .UpTo _ _ body 0 (n : Int) rfl rfl ?_
  rw [ComJasminBridgeFor.wrange_upTo_zero]
  exact hs'

end For

/-! ## §3b. `Cwhile` -/

section While
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

/-- The abstract loop body `step` iterated `k` times: `forFold` at a step that does
    not read the iteration index. -/
def iterFold {A : Type} (step : A → A) (k : Nat) : A → A :=
  forFold (fun _ => step) k

theorem iterFold_zero {A : Type} (step : A → A) (a : A) : iterFold step 0 a = a := rfl

theorem iterFold_succ {A : Type} (step : A → A) (k : Nat) (a : A) :
    iterFold step (k + 1) a = step (iterFold step k a) := rfl

/-- Iterating from `step a` is one more iteration from `a`. -/
theorem iterFold_step {A : Type} (step : A → A) :
    ∀ (k : Nat) (a : A), iterFold step k (step a) = iterFold step (k + 1) a
  | 0, _ => rfl
  | k + 1, a => by
    rw [iterFold_succ, iterFold_step step k a]
    rfl

/-- The loop `while (e) { body }` whose guard is `cond` on the abstract state and whose
    body corresponds at `step` while the guard holds: from a state related to `a` from
    which the guard holds for the first `k` iterates and fails at the `k`-th, the loop
    has a derivation to a state related to `iterFold step k a`. -/
theorem semIr_while_iter {A : Type} (SR : Estate SyscallState Mem → A → Prop) (P : A → Prop)
    (cond : A → Bool) (step : A → A) (al : Align) (e : Pexpr) (ii : InstrInfo) (body : Cmd)
    (hcond : ∀ s a, SR s a → P a → semPexpr (Mem := Mem) true gd opS s e = .ok (.Vbool (cond a)))
    (hbody : ∀ s a, SR s a → P a → cond a = true → ∃ s',
        Sem aS opS gd prog s body s' ∧ SR s' (step a))
    (hinv : ∀ a, P a → cond a = true → P (step a)) :
    ∀ (k : Nat) (a : A) (s : Estate SyscallState Mem), SR s a → P a →
      (∀ j < k, cond (iterFold step j a) = true) → cond (iterFold step k a) = false →
      ∃ s', SemIr aS opS gd prog s (.Cwhile al [] e ii body) s' ∧ SR s' (iterFold step k a) := by
  intro k
  induction k with
  | zero =>
    intro a s hSR hP _ hfalse
    refine ⟨s, .Ewhile_false s s al [] e ii body (.Eskip s) ?_, hSR⟩
    rw [hcond s a hSR hP, iterFold_zero] at *
    rw [hfalse]
  | succ k ih =>
    intro a s hSR hP htrue hfalse
    have h0 : cond a = true := htrue 0 (Nat.succ_pos k)
    obtain ⟨s1, hs1, hSR1⟩ := hbody s a hSR hP h0
    obtain ⟨s', hs', hSR'⟩ := ih (step a) s1 hSR1 (hinv a hP h0)
      (fun j hj => by rw [iterFold_step]; exact htrue (j + 1) (by omega))
      (by rw [iterFold_step]; exact hfalse)
    refine ⟨s', .Ewhile_true s s s1 s' al [] e ii body (.Eskip s) ?_ hs1 hs', ?_⟩
    · rw [hcond s a hSR hP, h0]
    · rw [iterFold_step] at hSR'
      exact hSR'

/-- **The loop rule.** Let the guard `e` evaluate to `cond a` from every state related to
    `a` with `P a`, let the body correspond at `step` when the guard holds, let `step`
    preserve `P` when the guard holds, and let `count a` be an iteration count at which
    the guard first fails. Then `while (e) { body }` corresponds at
    `fun a => iterFold step (count a) a`. -/
theorem corresSem_while {A : Type} (SR : Estate SyscallState Mem → A → Prop) (P : A → Prop)
    (cond : A → Bool) (step : A → A) (count : A → Nat)
    (al : Align) (e : Pexpr) (ii : InstrInfo) (body : Cmd)
    (hcond : ∀ s a, SR s a → P a → semPexpr (Mem := Mem) true gd opS s e = .ok (.Vbool (cond a)))
    (hbody : ∀ s a, SR s a → P a → cond a = true → ∃ s',
        Sem aS opS gd prog s body s' ∧ SR s' (step a))
    (hinv : ∀ a, P a → cond a = true → P (step a))
    (hcount : ∀ a, P a → (∀ j < count a, cond (iterFold step j a) = true) ∧
        cond (iterFold step (count a) a) = false) :
    CorresSemIr aS opS gd prog SR P (fun a => iterFold step (count a) a)
      (.Cwhile al [] e ii body) := by
  intro s a hSR hP
  exact semIr_while_iter aS opS gd prog SR P cond step al e ii body hcond hbody hinv
    (count a) a s hSR hP (hcount a hP).1 (hcount a hP).2

end While

/-! ## §4. Calls to functions with word parameters and results -/

section Call
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall (CallArg)

/-- The variable map with the parameters `ps` bound to their words, left to right. -/
def paramVm (ps : List CallArg) (vm : Vm) : Vm :=
  ps.foldl (fun vm p => vm.set p.src.v_var (.Vword p.sz p.w)) vm

/-- Truncating words at their own word types is the identity. -/
theorem truncate_words : ∀ ps : List CallArg,
    JResult.mapM (fun p : Atype × Value => truncateVal (evalAtype p.fst) p.snd)
      ((ps.map (fun p : CallArg => Atype.aword p.sz)).zip (ps.map CallArg.value))
      = .ok (ps.map CallArg.value)
  | [] => rfl
  | p :: ps => by
    show (do
        let b ← truncateVal (.cword p.sz) (.Vword p.sz p.w)
        let bs ← JResult.mapM (fun p : Atype × Value => truncateVal (evalAtype p.fst) p.snd)
          ((ps.map (fun p : CallArg => Atype.aword p.sz)).zip (ps.map CallArg.value))
        (.ok (b :: bs) : JResult Values)) = _
    rw [ComJasminBridgeFull.truncateVal_aword_self, truncate_words ps]
    rfl

omit [MemModel Mem] in
/-- Binding word parameters of their declared types is `paramVm`. -/
theorem writeVars_words : ∀ (ps : List CallArg) (s : Estate SyscallState Mem),
    (∀ p ∈ ps, p.src.v_var.vtype = .aword p.sz) →
    writeVars (Mem := Mem) true (ps.map (fun p : CallArg => p.src)) (ps.map CallArg.value) s
      = .ok (s.withVm (paramVm ps s.evm))
  | [], s, _ => rfl
  | p :: ps, s, h => by
    show (do
        let s1 ← writeVar (Mem := Mem) true p.src (.Vword p.sz p.w) s
        writeVars (Mem := Mem) true (ps.map (fun p : CallArg => p.src))
          (ps.map CallArg.value) s1) = _
    have hw : writeVar (Mem := Mem) true p.src (.Vword p.sz p.w) s
        = .ok (s.withVm ((s.evm).set p.src.v_var (.Vword p.sz p.w))) := by
      unfold writeVar setVar
      rw [h p List.mem_cons_self]
      simp only [DB, Value.isDefined, truncatable, Value.typeOf,
        Bool.not_true, decide_true, Bool.true_and]
      rfl
    rw [hw]
    show writeVars (Mem := Mem) true (ps.map (fun p : CallArg => p.src)) (ps.map CallArg.value)
        (s.withVm ((s.evm).set p.src.v_var (.Vword p.sz p.w))) = _
    rw [writeVars_words ps _ (fun q hq => h q (List.mem_cons_of_mem p hq))]
    rfl

/-- Reading result registers that hold words. -/
theorem getVarIs_words (vm : Vm) : ∀ rs : List CallArg,
    (∀ r ∈ rs, vm.get r.src.v_var = .Vword r.sz r.w) →
    getVarIs true vm (rs.map (fun p : CallArg => p.src)) = .ok (rs.map CallArg.value)
  | [], _ => rfl
  | r :: rs, h => by
    show (do
        let b ← getVar true vm r.src.v_var
        let bs ← getVarIs true vm (rs.map (fun p : CallArg => p.src))
        (.ok (b :: bs) : JResult Values)) = _
    have hg : getVar true vm r.src.v_var = .ok (.Vword r.sz r.w) := by
      unfold getVar
      rw [h r List.mem_cons_self]
      rfl
    rw [hg, getVarIs_words vm rs (fun q hq => h q (List.mem_cons_of_mem r hq))]
    rfl

/-- **The call rule.** Let `fn` be defined in `prog` by `f`, with word parameters
    `ps` receiving the caller's argument words `args` and word results `rs`. If the
    callee body, started at the parameter map with the caller's memory and syscall
    state, has a derivation to `s2` in which the result registers hold their words,
    then the call `Ccall (dsts.map lval) fn (args.map expr)` writes the results
    into `dsts` and resumes with the memory and syscall state of `s2`. -/
theorem ccall_words_semIr (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (fn : FunName) (f : FunDef) (hf : getFunDef prog fn = some f)
    (args ps rs : List CallArg) (dsts : List OpnOut)
    (s s2 : Estate SyscallState Mem)
    (hargs : ∀ a ∈ args, (s.evm).get a.src.v_var = .Vword a.sz a.w)
    (hps : ps.map CallArg.value = args.map CallArg.value)
    (htyin : f.tyin = ps.map (fun p : CallArg => Atype.aword p.sz))
    (hparams : f.params = ps.map (fun p : CallArg => p.src))
    (hpty : ∀ p ∈ ps, p.src.v_var.vtype = .aword p.sz)
    (hbody : Sem aS opS gd prog
        { escs := s.escs, emem := s.emem, evm := paramVm ps Vm.init } f.body s2)
    (hrets : ∀ r ∈ rs, (s2.evm).get r.src.v_var = .Vword r.sz r.w)
    (htyout : f.tyout = rs.map (fun r : CallArg => Atype.aword r.sz))
    (hretv : f.rets = rs.map (fun p : CallArg => p.src))
    (hdsts : dsts.map OpnOut.value = rs.map CallArg.value)
    (htyped : ∀ x ∈ dsts, x.Typed) :
    SemIr aS opS gd prog s (.Ccall (dsts.map OpnOut.lval) fn (args.map CallArg.expr))
      { escs := s2.escs, emem := s2.emem, evm := applyOuts dsts s.evm } := by
  refine .Ecall s _ _ fn _ s2.escs s2.emem (args.map CallArg.value) (dsts.map OpnOut.value)
    (ComJasminBridgeCall.semPexprs_callArgs gd opS s args hargs) ?_ ?_
  · rw [hdsts]
    refine .EcallRun s.escs s.emem fn f (ps.map CallArg.value) (args.map CallArg.value)
      _ _ s2 (rs.map CallArg.value) (rs.map CallArg.value) hf ?_ rfl ?_ hbody ?_ ?_
    · rw [htyin, ← hps]; exact truncate_words ps
    · rw [hparams]; exact writeVars_words ps _ hpty
    · rw [hretv]; exact getVarIs_words _ rs hrets
    · rw [htyout]; exact truncate_words rs
  · exact writeLvals_opnOuts gd opS dsts _ htyped

open StateBijection JasminPrintSemCorrect in
/-- **The emitted one-result call from a callee body.** For the call
    `ComJasminBridgeCall.callInstr dst fn args` to a function with word parameters
    and one word result `ret`, a derivation of the callee body gives the `SemIr`
    step, the argument reads of the JasminPrint store, and `StateCorrReg` after the
    result write: the conclusion of `ComJasminBridgeCall.ccall_leaf_endToEnd`,
    whose callee-run hypothesis is replaced by the callee body derivation. -/
theorem ccall_leaf_of_body (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (fn : FunName) (f : FunDef) (hf : getFunDef prog fn = some f)
    (dst : VarI) (args ps : List CallArg) (ret : VarI) (sz : WSize) (r : BitVec sz.bits)
    (s s2 : Estate SyscallState Mem) (st : Store) (names : List Var)
    (hdst : dst.v_var.vtype = .aword sz)
    (hargs : ComJasminBridgeCall.CallArgsRead names s args)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm))
    (hps : ps.map CallArg.value = args.map CallArg.value)
    (htyin : f.tyin = ps.map (fun p : CallArg => Atype.aword p.sz))
    (hparams : f.params = ps.map (fun p : CallArg => p.src))
    (hpty : ∀ p ∈ ps, p.src.v_var.vtype = .aword p.sz)
    (hbody : Sem aS opS gd prog
        { escs := s.escs, emem := s.emem, evm := paramVm ps Vm.init } f.body s2)
    (hret : (s2.evm).get ret.v_var = .Vword sz r)
    (htyout : f.tyout = [.aword sz]) (hretv : f.rets = [ret]) :
    SemIr aS opS gd prog s (ComJasminBridgeCall.callInstr dst fn args)
        { escs := s2.escs, emem := s2.emem, evm := (s.evm).set dst.v_var (.Vword sz r) }
    ∧ (∀ a ∈ args, Store.get st a.src.v_var.vname (.reg a.sz.bits) = a.w)
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg sz.bits) r)
        ((s.evm).set dst.v_var (.Vword sz r)) := by
  refine ⟨?_, ComJasminBridgeCall.store_get_callArgs gd opS s st names args hcorr hargs,
    stateCorrReg_write dst.v_var sz r st s.evm names hdst hdistinct hcorr⟩
  exact ccall_words_semIr aS opS gd prog fn f hf args ps [⟨ret, sz, r⟩] [.word dst sz r] s s2
    (fun a ha => (hargs a ha).2) hps htyin hparams hpty hbody
    (fun q hq => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      subst hq; exact hret)
    htyout hretv rfl
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      subst hx; exact hdst)

end Call

/-! ## §5. Worked instance: a loop calling a `MULX` function -/

namespace MulhiLoop
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall (CallArg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- The `u64` register named `x`. -/
def wv (x : String) : VarI := { v_var := { vtype := .aword .U64, vname := x } }

/-- The loop index `i : int`. -/
def iV : VarI := { v_var := { vtype := .aint, vname := "i" } }

/-- The callee name. -/
def mulhiFn : FunName := { name := "mulhi" }

/-- The callee body `lo, hi = #MULX_64(a, b)`. -/
def mulhiBody : Cmd :=
  [.MkI () (.Copn [.Lvar (wv "lo"), .Lvar (wv "hi")] .AT_none (.Oasm "MULX_64")
    [.Pvar (mkLvar (wv "a")), .Pvar (mkLvar (wv "b"))])]

/-- `fn mulhi(u64 a, u64 b) -> u64 { lo, hi = #MULX_64(a, b); return hi; }`. -/
def mulhiDef : FunDef :=
  { tyin := [.aword .U64, .aword .U64], params := [wv "a", wv "b"], body := mulhiBody,
    tyout := [.aword .U64], rets := [wv "hi"] }

/-- The program holding `mulhi`. -/
def prog : Prog := { pFuncs := [(mulhiFn, mulhiDef)], pGlobs := [] }

/-- The call `h = mulhi(h, b)`. -/
def callStep : InstrR :=
  .Ccall [.Lvar (wv "h")] mulhiFn [.Pvar (mkLvar (wv "h")), .Pvar (mkLvar (wv "b"))]

/-- The loop `for i = 0 to n { h = mulhi(h, b); }`. -/
def mainLoop (n : Nat) : InstrR :=
  .Cfor iV (ComJasminBridgeFor.forRange n) [.MkI () callStep]

/-- One abstract iteration: the high word of `h * b`. -/
def hiStep (b : BitVec 64) (_ : Nat) (h : BitVec 64) : BitVec 64 := (x86_MULX_lo_hi h b).2

/-- `mulhi` is found in `prog`. -/
theorem getFunDef_mulhi : getFunDef prog mulhiFn = some mulhiDef := by
  simp [getFunDef, prog, mulhiFn]

/-- **The loop runs to the iterated high word.** From a state holding `h0` at `h`
    and `b` at `b`, the loop has a `SemIr` derivation under `x86AsmSem` to a state
    holding `forFold (hiStep b) n h0` at `h`, with the memory unchanged. Each
    iteration is the call rule `ccall_words_semIr`, whose callee body is the `Copn`
    rule `copn_regs_semIr` at `x86AsmSem_mulx`; the loop is `corresSem_for`. -/
theorem mainLoop_sem (opS : OpSem) (gd : GlobDecls) (n : Nat) (h0 b : BitVec 64)
    (s : Estate SyscallState Mem)
    (hh : (s.evm).get (wv "h").v_var = .Vword .U64 h0)
    (hb : (s.evm).get (wv "b").v_var = .Vword .U64 b) :
    ∃ s', SemIr x86AsmSem opS gd prog s (mainLoop n) s'
      ∧ (s'.evm).get (wv "h").v_var = .Vword .U64 (forFold (hiStep b) n h0)
      ∧ s'.emem = s.emem := by
  let SR : Estate SyscallState Mem → BitVec 64 → Prop := fun t h =>
    (t.evm).get (wv "h").v_var = .Vword .U64 h ∧ (t.evm).get (wv "b").v_var = .Vword .U64 b
      ∧ t.emem = s.emem
  have hloop := corresSem_for x86AsmSem opS gd prog SR (fun _ => True) (hiStep b) iV n
    [.MkI () callStep] rfl ?_ (fun _ _ _ => trivial)
  · obtain ⟨s', hs', hSR'⟩ := hloop s h0 ⟨hh, hb, rfl⟩ trivial
    exact ⟨s', hs', hSR'.1, hSR'.2.2⟩
  intro k _ t h ⟨th, tb, tm⟩ _
  let tk := t.withVm ((t.evm).set iV.v_var (.Vint (Int.ofNat k)))
  have tkh : (tk.evm).get (wv "h").v_var = .Vword .U64 h := by
    simp [tk, Estate.withVm, Vm.get, Vm.set, iV, wv] at th ⊢; exact th
  have tkb : (tk.evm).get (wv "b").v_var = .Vword .U64 b := by
    simp [tk, Estate.withVm, Vm.get, Vm.set, iV, wv] at tb ⊢; exact tb
  let ps : List CallArg := [⟨wv "a", .U64, h⟩, ⟨wv "b", .U64, b⟩]
  let outs : List OpnOut :=
    [.word (wv "lo") .U64 (x86_MULX_lo_hi h b).1, .word (wv "hi") .U64 (x86_MULX_lo_hi h b).2]
  let c0 : Estate SyscallState Mem :=
    { escs := tk.escs, emem := tk.emem, evm := paramVm ps Vm.init }
  have hcopn := copn_regs_semIr (Mem := Mem) x86AsmSem opS gd prog .AT_none (.Oasm "MULX_64")
    [.word (wv "a") .U64 h, .word (wv "b") .U64 b] outs c0
    (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;>
        simp [OpnArg.Holds, c0, ps, paramVm, Vm.get, Vm.set, wv])
    (x86AsmSem_mulx h b)
    (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false, outs] at hx
      rcases hx with rfl | rfl <;> rfl)
  have hcall := ccall_words_semIr (Mem := Mem) x86AsmSem opS gd prog mulhiFn mulhiDef
    getFunDef_mulhi
    [⟨wv "h", .U64, h⟩, ⟨wv "b", .U64, b⟩] ps [⟨wv "hi", .U64, (x86_MULX_lo_hi h b).2⟩]
    [.word (wv "h") .U64 (x86_MULX_lo_hi h b).2] tk (c0.withVm (applyOuts outs c0.evm))
    (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl
      · exact tkh
      · exact tkb)
    rfl rfl rfl
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false, ps] at hp
      rcases hp with rfl | rfl <;> rfl)
    (.Eseq _ _ _ _ _ (.EmkI () _ _ _ hcopn) (.Eskip _))
    (by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      subst hr
      simp [c0, outs, applyOuts, OpnOut.applyVm, Estate.withVm, Vm.get, Vm.set, wv])
    rfl rfl rfl
    (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      subst hx; rfl)
  refine ⟨_, .Eseq _ _ _ _ _ (.EmkI () _ _ _ hcall) (.Eskip _), ?_, ?_, ?_⟩
  · simp [applyOuts, OpnOut.applyVm, Vm.get, Vm.set, hiStep]
  · simp only [applyOuts, List.foldl, OpnOut.applyVm]
    simp [Vm.get, Vm.set, wv] at tkb ⊢
    exact tkb
  · exact tm

end MulhiLoop

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram
