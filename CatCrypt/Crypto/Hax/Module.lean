/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.Hax.NFInline
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import HaxLean.Phase.InlineLocalClosures
public import HaxLean.TExpr

/-!
# Modules of the hax compiler

A module `HaxModule` is an entry function, the functions the entry may call, and an inlining
depth. The entry is an extraction `TExpr`. The functions are callees `CrateFn`: a name, typed
parameters, a result type and a prepared body. A single function is the module with no callee
and depth `0` (`HaxModule.single`), and a `TExpr` coerces to it.

The table of a module, `HaxModule.table m bi fuelC`, is `ImpToNF.crateBi` at the functions and
the depth of the module: the builtins `bi` extended by the functions of the module, each run
to the call depth `m.depth` at the fuel `fuelC`.

The source relation of a module, `HaxModule.Runs bi σ m sa v`, is a run of the reference
reading `denoteSpine` of the entry at the table of the module, from an environment the layout
`σ` reads off the entry state `sa`, to the value `v`. The source meaning of a call of a
function of the module is therefore the run of the prepared body `CrateFn.body` of the callee
under the table, from the environment binding its parameters to the argument values; the
reference reading `denoteSpine` applies to the entry only.

The inlining of the calls of a module is `NFInline.crateInline?`: the program after `n` rounds
of `NFProg.inline?` at the library `crateLib fs`, on a program accepted by the check
`crateInlineOk fs n`, and a refusal otherwise. As a chain step (`crateInlineStep`) it has the
certificate `crateInlineCert`, from the semantics at the table `crateBi fs bi fuelC n` to the
semantics at `bi`, with equality as input and output relation, under the typing
`TypedCalls bi hax64SigOf` of the base table.

At the module of a single function the call typing is `hax64SigOf`, the table is `bi`, the
source relation is the run of the entry at `bi`, and the inlining returns its argument.

## Main definitions

* `NFInline.crateInline?` — the rounds of inlining at the library of a list of callees, under
  their check.
* `NFInline.crateInlineStep`, `NFInline.crateInlineCert` — the checked inlining as a chain
  step, and its certificate between the two tables.
* `HaxModule`, `HaxModule.single` — a module, and the module of one function.
* `HaxModule.sigOf`, `HaxModule.table` — the call typing and the builtin table of a module.
* `HaxModule.Runs` — the source relation of a module at a base table and a layout.
* `HaxModule.inline?`, `HaxModule.inlineStep`, `HaxModule.inlineCert` — the inlining of the
  calls of a module, as a function, as a chain step, and its certificate.

## Main results

* `crateSigOf_nil`, `crateBi_nil` — with no callee the call typing and the table are the base
  ones.
* `crateCallOp_nil`, `noCrateCall_nil`, `crateInlineOk_nil_zero`, `crateInline?_nil_zero` —
  with no callee no operation is a call of a callee, the check of `0` rounds accepts every
  program, and the inlining returns its argument.
* `crateInline?_eq_some`, `denote_crateInline?` — a result of the inlining is the program
  after the rounds under the check, and a run of the argument at the table with the callees is
  a run of the result at the base table.
* `HaxModule.sigOf_single`, `HaxModule.table_single`, `HaxModule.runs_single`,
  `HaxModule.inline?_single` — the four statements at the module of a single function.
* `HaxModule.denote_inline?` — a run at the table of the module is a run of the inlined
  program at the base table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFInline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (nfSem)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf hax64SigOf tableOf TypedCalls crateBi
  PDenP)
open _root_.Hax (Builtins)
open Ctxt (Valuation)

/-! ## 1. The empty list of callees -/

/-- The call typing with no callee is the base typing. -/
theorem crateSigOf_nil (base : String → List NfTy → Option NfTy) : crateSigOf [] base = base :=
  rfl

/-- The builtins with no callee are the base builtins, at every fuel and call depth. -/
theorem crateBi_nil (bi : Builtins) (fuel n : Nat) : crateBi [] bi fuel n = bi := by
  cases n <;> rfl

/-- No operation is a call of a callee of the empty list. -/
theorem crateCallOp_nil : ∀ o : NfOp, crateCallOp [] o = false := by
  intro o
  induction o <;> simp_all [crateCallOp]

/-- Every program is without calls of a callee of the empty list. -/
theorem noCrateCall_nil {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    noCrateCall [] p = true :=
  (noCrateCall_iff [] p).mpr fun o _ => crateCallOp_nil o

/-- The check of `0` rounds of inlining at the empty list of callees accepts every program. -/
theorem crateInlineOk_nil_zero {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : crateInlineOk [] 0 p = true := by
  simp [crateInlineOk, NFProg.inlineIterOk, NFProg.inlineIter, noCrateCall_nil]

/-! ## 2. The rounds of inlining under their check -/

/-- **The program after `n` rounds of inlining at the library of the callees `fs`**, on a
    program accepted by `crateInlineOk fs n`, and a refusal otherwise. -/
def crateInline? (fs : List CrateFn) (n : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Option (NFProg nfDialect Γ ts) :=
  if crateInlineOk fs n p = true then some (p.inlineIter (crateLib fs) n) else none

/-- A result of `crateInline? fs n p` is the program after the `n` rounds, and the check
    `crateInlineOk fs n` accepts `p`. -/
theorem crateInline?_eq_some {fs : List CrateFn} {n : Nat} {Γ : Ctxt nfDialect}
    {ts : List NfTy} {p p' : NFProg nfDialect Γ ts} (h : crateInline? fs n p = some p') :
    crateInlineOk fs n p = true ∧ p' = p.inlineIter (crateLib fs) n := by
  unfold crateInline? at h
  split at h
  · exact ⟨‹_›, (Option.some.inj h).symm⟩
  · cases h

/-- With no callee and `0` rounds the inlining returns its argument. -/
theorem crateInline?_nil_zero {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : crateInline? [] 0 p = some p := by
  simp [crateInline?, crateInlineOk_nil_zero, NFProg.inlineIter]

/-- **The checked inlining keeps every successful run, from the builtins with the callees to
    the base builtins.** Under the typing of the builtins `bi`, a successful run of `p` at the
    builtins with the callees `fs` to the call depth `n` (the callees run their bodies at the
    fuel `fuelC`) is a run of a result of `crateInline? fs n p` at `bi`, with the same
    result. -/
theorem denote_crateInline? (fs : List CrateFn) (bi : Builtins)
    (hT : TypedCalls bi hax64SigOf) (fuelC tf n : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p p' : NFProg nfDialect Γ ts} (h : crateInline? fs n p = some p') {V : Valuation Γ}
    {out : Valuation (d := nfDialect) ts}
    (hp : PDenP (crateBi fs bi fuelC n) tf p V = some out) : PDenP bi tf p' V = some out := by
  obtain ⟨hok, rfl⟩ := crateInline?_eq_some h
  exact denote_inlineIter_crate fs bi hT fuelC tf n p hok hp

/-- The checked inlining at the callees `fs` with `n` rounds as a chain step. -/
def crateInlineStep (fs : List CrateFn) (n : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.Step (NFProg nfDialect Γ ts) (NFProg nfDialect Γ ts) :=
  ⟨"crateInline", crateInline? fs n⟩

/-- **The certificate of the checked inlining**: from the semantics of structured programs of
    `nfDialect` at the leaf table of the builtins with the callees, `crateBi fs bi fuelC n`,
    to the semantics at the leaf table of `bi`, both at the fuel `tf`, with equality as input
    and output relation. It is `denote_crateInline?`. -/
def crateInlineCert (fs : List CrateFn) {bi : Builtins} (hT : TypedCalls bi hax64SigOf)
    (fuelC tf n : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.StepCert (crateInlineStep fs n Γ ts).run
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf (crateBi fs bi fuelC n))) _ Γ ts)
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ Γ ts) where
  relIn V W := V = W
  relOut o o' := o = o'
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    exact ⟨o, denote_crateInline? fs bi hT fuelC tf n hf hd, rfl⟩

end CatCrypt.Crypto.Hax.NFInline

/-! ## 3. Modules -/

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (nfSem)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf hax64SigOf tableOf TypedCalls crateBi
  PDenP)
open CatCrypt.Crypto.Hax.NFInline
open _root_.Hax (TExpr Builtins Value Env)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open Ctxt (Valuation)

/-- **A module**: an entry function, the functions the entry may call, and the depth to which
    their calls are inlined. A callee is a `CrateFn`: its name, its typed parameters, its
    result type and its prepared body. -/
structure HaxModule where
  /-- The extraction of the entry function. -/
  entry : TExpr
  /-- The functions the entry may call; the first function with a name is the one called. -/
  fns : List CrateFn
  /-- The call depth to which the functions run, and the number of rounds of inlining. -/
  depth : Nat

namespace HaxModule

/-- The module of the single function `te`: no callee, depth `0`. -/
def single (te : TExpr) : HaxModule := ⟨te, [], 0⟩

instance : Coe TExpr HaxModule := ⟨single⟩

/-- The call typing of a module: `crateSigOf` at its functions over `hax64SigOf`. -/
def sigOf (m : HaxModule) : String → List NfTy → Option NfTy := crateSigOf m.fns hax64SigOf

/-- The call typing of the module of a single function is `hax64SigOf`. -/
theorem sigOf_single (te : TExpr) : (single te).sigOf = hax64SigOf := rfl

/-- **The table of a module**: the builtins `bi` with the functions of the module, each run
    at the fuel `fuelC` to the call depth of the module (`crateBi`). -/
def table (m : HaxModule) (bi : Builtins) (fuelC : Nat) : Builtins :=
  crateBi m.fns bi fuelC m.depth

/-- The table of the module of a single function is the base table. -/
theorem table_single (te : TExpr) (bi : Builtins) (fuelC : Nat) :
    (single te).table bi fuelC = bi := rfl

/-- **The source relation of a module** at the base table `bi` and the layout `σ`: the
    reference reading `denoteSpine` of the entry, at the table of the module for some fuel of
    the callees, runs from an environment `σ` reads off the entry state `sa` to the value `v`,
    which is not a control-flow value. A call of a function of the module in the entry is
    answered by the table: the run of the prepared body of the callee from the environment
    binding its parameters to the argument values. -/
def Runs (bi : Builtins) (σ : AbiLayout) (m : HaxModule) (sa : AState) (v : Value) : Prop :=
  ∃ env fuel fuelC env', σ.EnvOf sa env ∧
    (denoteSpine (m.table bi fuelC) fuel m.entry.erase).run env = (.val v, env') ∧
      v.isControlFlow = false

/-- The source relation of the module of a single function is the run of the reference
    reading of the function at the base table. -/
theorem runs_single (bi : Builtins) (σ : AbiLayout) (te : TExpr) (sa : AState) (v : Value) :
    Runs bi σ (single te) sa v ↔
      ∃ env fuel env', σ.EnvOf sa env ∧
        (denoteSpine bi fuel te.erase).run env = (.val v, env') ∧ v.isControlFlow = false :=
  ⟨fun ⟨env, fuel, _, env', h⟩ => ⟨env, fuel, env', h⟩,
    fun ⟨env, fuel, env', h⟩ => ⟨env, fuel, 0, env', h⟩⟩

/-- **The inlining of the calls of a module** in a structured program: `crateInline?` at the
    functions and the depth of the module. -/
def inline? (m : HaxModule) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Option (NFProg nfDialect Γ ts) :=
  crateInline? m.fns m.depth p

/-- The inlining of the module of a single function returns its argument. -/
theorem inline?_single (te : TExpr) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : (single te).inline? p = some p :=
  crateInline?_nil_zero p

/-- **The inlining of the calls of a module keeps every successful run, from the table of the
    module to the base table**, under the typing of the base table. -/
theorem denote_inline? (m : HaxModule) {bi : Builtins} (hT : TypedCalls bi hax64SigOf)
    (fuelC tf : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy} {p p' : NFProg nfDialect Γ ts}
    (h : m.inline? p = some p') {V : Valuation Γ} {out : Valuation (d := nfDialect) ts}
    (hp : PDenP (m.table bi fuelC) tf p V = some out) : PDenP bi tf p' V = some out :=
  denote_crateInline? m.fns bi hT fuelC tf m.depth h hp

/-- The inlining of the calls of a module as a chain step. -/
def inlineStep (m : HaxModule) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.Step (NFProg nfDialect Γ ts) (NFProg nfDialect Γ ts) :=
  crateInlineStep m.fns m.depth Γ ts

/-- **The certificate of the inlining of the calls of a module**: from the semantics of
    structured programs at the leaf table of the module's table to the semantics at the leaf
    table of the base table `bi`, with equality as input and output relation. -/
def inlineCert (m : HaxModule) {bi : Builtins} (hT : TypedCalls bi hax64SigOf)
    (fuelC tf : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.StepCert (m.inlineStep Γ ts).run
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf (m.table bi fuelC))) _ Γ ts)
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ Γ ts) :=
  crateInlineCert m.fns hT fuelC tf m.depth Γ ts

end HaxModule

end CatCrypt.Crypto.Hax
