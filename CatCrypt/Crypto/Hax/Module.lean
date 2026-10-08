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
depth. The entry is an extraction `TExpr`. A function is a `ModFn`: a name, typed parameters,
a result type and the extraction `TExpr`. A single function is the module with no callee and
depth `0` (`HaxModule.single`), and a `TExpr` coerces to it.

The reference table `refBi fs bi fuel n` answers a call of a function of `fs` by the run of
the reference reading `denoteSpine` of the extraction of the callee, from the environment
binding the names of its parameters to the argument values, to the call depth `n`. The table
of a module, `HaxModule.table m bi fuelC`, is the reference table at the functions and the
depth of the module.

The source relation of a module, `HaxModule.Runs bi σ m sa v`, is a run of the reference
reading of the entry at the table of the module, from an environment the layout `σ` reads off
the entry state `sa`, to the value `v`. The source meaning of a call of a function of the
module is the run of the reference reading of the extraction of the callee.

The bodies the compiler inlines are prepared from the extractions by a preparation
`P : TExpr → ImpExpr`, a parameter of the definitions of this file: `ModFn.prep P f` is the
callee `CrateFn` with the body `P f.texpr`, and `HaxModule.prepared P m` the prepared callees
of a module. For a preparation that keeps the runs of each function at each depth of the
reference table (`ModFn.PrepSim`), the reference tables are a family of tables for the
prepared callees, so the inlining of the calls of a module keeps the runs from the table of
the module to the base table (`HaxModule.denote_inline?`).

The inlining of calls is `NFInline.crateInline?`: the program after `n` rounds of
`NFProg.inline?` at the library `crateLib fs`, on a program accepted by the check
`crateInlineOk fs n`, and a refusal otherwise. As a chain step (`crateInlineStep`) it has the
certificate `crateInlineCert`, from the semantics at the table `crateBi fs bi fuelC n` to the
semantics at `bi`, with equality as input and output relation, under the typing
`TypedCalls bi hax64SigOf` of the base table.

At the module of a single function the call typing is `hax64SigOf`, the table is `bi`, the
source relation is the run of the entry at `bi`, and the inlining returns its argument.

A module also carries linked functions (`LinkedFn`, the field `HaxModule.linked`, empty
unless given): functions the compiled entry calls by a machine call. The call typing of a
module types a call of a linked function from its parameter and result types
(`HaxModule.sigOf`), the inlining leaves the call in place, and the table of the module has
no entry for it, so the source relation `HaxModule.Runs` gives a run that calls a linked
function the value the base table gives the name. For a module without linked functions the
call typing is that of the prepared callees (`HaxModule.sigOf_of_linked_nil`), and the table,
the source relation and the inlining do not read the field.

A family of tables along the call depth, `NFInline.CrateTables fs bi T`, states what the
inlining uses of a table of callees: names of no callee are answered by `bi`, depth `0` answers
no callee, and a value of a call at depth `n + 1` decodes at the result type and is the value
of a run of the body of the callee, at some fuel, at depth `n`. The fuel may differ from call
to call. `crateBi fs bi fuel` is such a family, and the checked inlining keeps the runs from
every such family to `bi` (`CrateTables.denote_crateInline?`).

## Main definitions

* `NFInline.crateInline?` — the rounds of inlining at the library of a list of callees, under
  their check.
* `NFInline.crateInlineStep`, `NFInline.crateInlineCert` — the checked inlining as a chain
  step, and its certificate between the two tables.
* `NFInline.CrateTables` — a family of tables along the call depth for a list of callees.
* `ModFn`, `ModFn.prep`, `ModFn.PrepSim` — a function of a module by its extraction, its
  prepared callee, and the preparation keeping its runs at a table.
* `refBi` — the reference table of a list of functions.
* `HaxModule`, `HaxModule.single`, `HaxModule.prepared` — a module, the module of one
  function, and the prepared callees of a module.
* `LinkedFn`, `HaxModule.linkedFns` — a linked function of a module, and the linked
  functions of a module as callees of the call typing.
* `HaxModule.sigOf`, `HaxModule.table` — the call typing and the table of a module.
* `HaxModule.Runs` — the source relation of a module at a base table and a layout.
* `HaxModule.inline?`, `HaxModule.inlineStep`, `HaxModule.inlineCert` — the inlining of the
  calls of a module, as a function, as a chain step, and its certificate.

## Main results

* `crateSigOf_nil`, `crateBi_nil` — with no callee the call typing and the table are the base
  ones.
* `crateSigOf_append`, `typedCalls_crateSigOf` — the call typing of two lists of callees is
  the typing of the first over the typing of the second, and the typing with callees whose
  names a table does not answer is sound for the table.
* `HaxModule.linkedFns_of_linked_nil`, `HaxModule.sigOf_of_linked_nil` — a module without
  linked functions has the call typing of its prepared callees.
* `crateCallOp_nil`, `noCrateCall_nil`, `crateInlineOk_nil_zero`, `crateInline?_nil_zero` —
  with no callee no operation is a call of a callee, the check of `0` rounds accepts every
  program, and the inlining returns its argument.
* `crateInline?_eq_some`, `denote_crateInline?` — a result of the inlining is the program
  after the rounds under the check, and a run of the argument at the table with the callees is
  a run of the result at the base table.
* `NFInline.crateTables_crateBi`, `NFInline.CrateTables.typedCalls`,
  `NFInline.CrateTables.denote_crateInline?` — `crateBi` is a family of tables; every table of
  a family is typed by the call typing of the callees; the checked inlining keeps the runs
  from a family to the base table.
* `refBi_nil`, `refBi_succ`, `crateTables_refBi` — the reference table with no function is
  the base table; a call at depth `n + 1` is the run of the extraction at depth `n`; under
  `ModFn.PrepSim` the reference tables are a family for the prepared callees.
* `HaxModule.prepared_single`, `HaxModule.sigOf_single`, `HaxModule.table_single`,
  `HaxModule.runs_single`, `HaxModule.inline?_single` — the statements at the module of a
  single function.
* `HaxModule.table_typedCalls`, `HaxModule.denote_inline?` — the table of a module is typed by
  the call typing of its prepared callees, and a run at the table of the module is a run of
  the inlined program at the base table.
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

/-- The call typing with the callees `A ++ L` is the call typing with `A` over the call
    typing with `L`. -/
theorem crateSigOf_append (A L : List CrateFn) (base : String → List NfTy → Option NfTy) :
    crateSigOf (A ++ L) base = crateSigOf A (crateSigOf L base) := by
  funext f as
  unfold crateSigOf
  rw [List.find?_append]
  cases A.find? (·.name == f) <;> rfl

/-- **The call typing with callees a table does not answer is sound for the table**: when
    `base` is sound for `bi` and `bi` answers the name of no function of `L`, the call typing
    `crateSigOf L base` is sound for `bi`. -/
theorem typedCalls_crateSigOf {bi : Builtins} {base : String → List NfTy → Option NfTy}
    (hT : TypedCalls bi base) (L : List CrateFn)
    (hL : ∀ c ∈ L, ∀ vals, bi c.name vals = none) : TypedCalls bi (crateSigOf L base) := by
  intro f as r hsig xs v hb
  unfold crateSigOf at hsig
  split at hsig
  · rename_i c hf
    have hn : c.name = f := by simpa using List.find?_some hf
    rw [← hn, hL c (List.mem_of_find?_eq_some hf)] at hb
    cases hb
  · exact hT f as r hsig xs v hb

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

/-! ## 3. Families of tables along the call depth -/

namespace CatCrypt.Crypto.Hax.NFInline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf hax64SigOf tableOf TypedCalls crateBi
  crateBi_of_find_none PDenP PDenP_plug_ret paramsEnv dec dec_sound impToNF_sound entryEnv)
open _root_.Hax (Builtins Value Env denote')
open Ctxt (Valuation)

/-- **A family of tables along the call depth, for the callees `fs` over the builtins `bi`.**
    At every depth a name no callee has is answered by `bi`; at depth `0` a call of a callee
    fails; a call of the callee `c` at depth `n + 1` that returns `v` has a run of the body of
    `c`, at some fuel and the table of depth `n`, from the environment binding its parameters
    to the argument values, to `v`, and `dec` decodes `v` at the result type of `c`. -/
structure CrateTables (fs : List CrateFn) (bi : Builtins) (T : Nat → Builtins) : Prop where
  /-- A name no callee has is answered by `bi`. -/
  base : ∀ n {f : String}, fs.find? (·.name == f) = none → ∀ vals, T n f vals = bi f vals
  /-- At depth `0` a call of a callee fails. -/
  zero : ∀ {f : String} {c : CrateFn}, fs.find? (·.name == f) = some c →
    ∀ vals, T 0 f vals = none
  /-- A value of a call at depth `n + 1` decodes at the result type and is the value of a run
      of the body at depth `n`. -/
  call : ∀ n {f : String} {c : CrateFn}, fs.find? (·.name == f) = some c →
    ∀ vals v, T (n + 1) f vals = some v →
      (dec c.res v).isSome ∧ ∃ fuel s,
        (denote' (T n) fuel c.body).run (paramsEnv (c.params.map (·.1)) vals) = (.val v, s)

/-- The builtins with a crate `crateBi fs bi fuel` are a family of tables for `fs` over `bi`,
    with the fuel `fuel` at every call. -/
theorem crateTables_crateBi (fs : List CrateFn) (bi : Builtins) (fuel : Nat) :
    CrateTables fs bi (crateBi fs bi fuel) where
  base n _ hf vals := crateBi_of_find_none fs bi fuel n hf vals
  zero hf vals := by simp only [crateBi, hf]
  call n f c hf vals v hv := by
    simp only [crateBi, hf] at hv
    split at hv
    · rename_i w hrun
      split at hv
      · rename_i hd
        cases hv
        exact ⟨hd, fuel, _, Prod.ext hrun rfl⟩
      · cases hv
    · cases hv

namespace CrateTables

variable {fs : List CrateFn} {bi : Builtins} {T : Nat → Builtins}

/-- **The call typing with the callees is sound for every table of a family**, when `base` is
    sound for `bi`. -/
theorem typedCalls (h : CrateTables fs bi T) {base : String → List NfTy → Option NfTy}
    (hT : TypedCalls bi base) : ∀ n, TypedCalls (T n) (crateSigOf fs base) := by
  intro n f as r hsig xs v hb
  unfold crateSigOf at hsig
  split at hsig
  · rename_i c hf
    split at hsig
    · cases hsig
      cases n with
      | zero =>
          rw [h.zero hf] at hb
          cases hb
      | succ n =>
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h.call n hf _ v hb).1
          exact ⟨y, hy, dec_sound _ _ _ hy⟩
    · cases hsig
  · rename_i hf
    rw [h.base n hf] at hb
    exact hT f as r hsig xs v hb

/-- An operation that calls no callee denotes at every table of a family as at `bi`. -/
theorem nfDenoteOp_eq (h : CrateTables fs bi T) (m : Nat) :
    ∀ (o : NfOp), crateCallOp fs o = false → ∀ x,
      nfDenoteOp (tableOf (T m)) o x = nfDenoteOp (tableOf bi) o x := by
  intro o
  induction o with
  | call f as r =>
      intro hc x
      simp only [crateCallOp, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hc
      simp only [nfDenoteOp, tableOf, h.base m hc]
  | named _ o ih =>
      intro hc x
      exact ih hc x
  | _ =>
      intro _ _
      rfl

/-- **A call of a callee at depth `m + 1` is a run of its translated body at depth `m`**, at
    every fuel `tf`, with the same result, under the typing of `bi`. -/
theorem crateOp_sound (h : CrateTables fs bi T) (hT : TypedCalls bi hax64SigOf) (m tf : Nat) :
    ∀ (o : NfOp) (b : NFProg nfDialect o.sig [o.ret]), crateOp fs o = some b → ∀ x y,
      nfDenoteOp (tableOf (T (m + 1))) o x = some y →
        PDenP (T m) tf b x = some (.cons y .nil) := by
  intro o
  induction o with
  | call f as r =>
      intro b hb x y hy
      simp only [crateOp, Option.bind_eq_some_iff] at hb
      obtain ⟨c, hc, hb⟩ := hb
      simp only [crateBody, Option.bind_eq_some_iff] at hb
      obtain ⟨o', ho', hb⟩ := hb
      split at hb
      · rename_i hty
        cases hb
        obtain ⟨rfl, rfl⟩ := hty
        simp only [nfDenoteOp, tableOf, Option.bind_eq_some_iff] at hy
        obtain ⟨v, hv, hd⟩ := hy
        obtain ⟨-, fuel, s, hrun⟩ := h.call m hc _ v hv
        obtain ⟨W, hpre, -, hvW⟩ := impToNF_sound (T m) (crateSigOf fs hax64SigOf)
          (h.typedCalls hT m) c.body none (entryEnv c.params) ho' fuel _ x v s
          (entryEnv_rel_paramsEnv c.params x) hrun tf
        have hy' : y = o'.res.lookup W :=
          enc_inj _ _ _ ((dec_sound _ _ _ hd).symm.trans hvW)
        subst hy'
        exact PDenP_plug_ret _ tf o'.pre (.cons o'.res .nil) x hpre
      · cases hb
  | named _ o ih =>
      intro b hb x y hy
      exact ih b hb x y hy
  | _ =>
      intro b hb
      cases hb

/-- **The library of the callees is sound from depth `m + 1` to depth `m` of a family**, for
    the operations that call no callee. -/
theorem soundStep (h : CrateTables fs bi T) (hT : TypedCalls bi hax64SigOf) (m tf : Nat) :
    (crateLib fs).SoundStep (nfDenote (tableOf (T (m + 1)))) (nfDenote (tableOf (T m)))
      (fun o => !crateCallOp fs o) tf where
  op := h.crateOp_sound hT m tf
  keep o ho x y hy := by
    simp only [Bool.not_eq_true'] at ho
    simp only [nfDenote_denoteM] at hy ⊢
    rw [h.nfDenoteOp_eq m o ho]
    rwa [h.nfDenoteOp_eq (m + 1) o ho] at hy
  call _ _ _ _ hb := by cases hb

/-- A program without calls of the callees denotes at every table of a family as at `bi`. -/
theorem PDenP_of_noCrateCall (h : CrateTables fs bi T) (m tf : Nat) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) (hp : noCrateCall fs p = true)
    (V : Valuation Γ) : PDenP (T m) tf p V = PDenP bi tf p V :=
  NFProg.denote_congr_ops (nfDenote (tableOf (T m))) (nfDenote (tableOf bi))
    (fun o => !crateCallOp fs o)
    (fun o ho x => h.nfDenoteOp_eq m o (by simpa using ho) x) tf p hp V

/-- **The checked inlining keeps every successful run, from the table of depth `n` of a family
    to the base builtins**, under the typing of `bi`. -/
theorem denote_crateInline? (h : CrateTables fs bi T) (hT : TypedCalls bi hax64SigOf)
    (tf n : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy} {p p' : NFProg nfDialect Γ ts}
    (hi : crateInline? fs n p = some p') {V : Valuation Γ}
    {out : Valuation (d := nfDialect) ts} (hp : PDenP (T n) tf p V = some out) :
    PDenP bi tf p' V = some out := by
  obtain ⟨hok, rfl⟩ := crateInline?_eq_some hi
  obtain ⟨hit, hno⟩ := Bool.and_eq_true_iff.mp hok
  rw [← h.PDenP_of_noCrateCall 0 tf _ hno V]
  exact NFProg.denote_inlineIter_step (fun m => nfDenote (tableOf (T m)))
    (fun m => h.soundStep hT m tf) n p hit hp

end CrateTables

end CatCrypt.Crypto.Hax.NFInline

/-! ## 4. The reference table of a module -/

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (nfSem)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf hax64SigOf tableOf TypedCalls PDenP
  paramsEnv dec)
open CatCrypt.Crypto.Hax.NFInline
open _root_.Hax (TExpr ImpExpr Builtins Value Env denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open Ctxt (Valuation)

/-- `dec` decodes a control-flow value at no type. -/
theorem dec_controlFlow (t : NfTy) (b : Bool) (w : Value) : dec t (.controlFlow b w) = none := by
  cases t <;> rfl

/-- A value `dec` decodes at a type is not a control-flow value. -/
theorem isControlFlow_of_dec {t : NfTy} {v : Value} (h : (dec t v).isSome) :
    v.isControlFlow = false := by
  cases v with
  | controlFlow b w => simp [dec_controlFlow] at h
  | _ => rfl

/-- **A function of a module**: its name, its parameters with their types, its result type and
    its extraction. -/
structure ModFn where
  /-- The name the callers call it by. -/
  name : String
  /-- The parameters, each the name the extraction reads it by with its type. -/
  params : List (String × NfTy)
  /-- The result type. -/
  res : NfTy
  /-- The extraction of the function. -/
  texpr : TExpr

namespace ModFn

/-- The callee of a function of a module under the preparation `P` of bodies: the name, the
    parameters and the result type of the function, with the body `P` makes of its
    extraction. -/
def prep (P : TExpr → ImpExpr) (f : ModFn) : CrateFn := ⟨f.name, f.params, f.res, P f.texpr⟩

/-- **The preparation `P` keeps the runs of the function `f` at the table `bi`**: a run of the
    reference reading `denoteSpine` of the extraction of `f`, from any environment, to a value
    that is not a control-flow value is matched by a run of `denote'` of the body `P` makes,
    at some fuel, from the same environment to the same value. -/
def PrepSim (P : TExpr → ImpExpr) (f : ModFn) (bi : Builtins) : Prop :=
  ∀ (fuel : Nat) (env env' : Env) (v : Value),
    (denoteSpine bi fuel f.texpr.erase).run env = (.val v, env') → v.isControlFlow = false →
      ∃ fuel' s, (denote' bi fuel' (P f.texpr)).run env = (.val v, s)

end ModFn

/-- The first callee with a name among the prepared functions is the callee of the first
    function with the name. -/
theorem find?_prep (P : TExpr → ImpExpr) (fs : List ModFn) (g : String) :
    (fs.map (ModFn.prep P)).find? (·.name == g) =
      (fs.find? (·.name == g)).map (ModFn.prep P) := by
  rw [List.find?_map]
  rfl

/-- **The reference table of the functions `fs` of a module**, to the call depth `n`. A call
    of a function of `fs` runs the reference reading `denoteSpine` of its extraction at the
    fuel `fuel` with the table of depth `n - 1`, from the environment binding the names of
    its parameters to the argument values (`paramsEnv`), and returns the value of the run when
    `dec` decodes it at the result type; at depth `0`, and on a run that ends otherwise, the
    call fails. Every other call is a call of `bi`. -/
def refBi (fs : List ModFn) (bi : Builtins) (fuel : Nat) : Nat → Builtins
  | 0, g, vals =>
      match fs.find? (·.name == g) with
      | some _ => none
      | none => bi g vals
  | n + 1, g, vals =>
      match fs.find? (·.name == g) with
      | some f =>
          match ((denoteSpine (refBi fs bi fuel n) fuel f.texpr.erase).run
              (paramsEnv (f.params.map (·.1)) vals)).1 with
          | .val v => if (dec f.res v).isSome then some v else none
          | _ => none
      | none => bi g vals

/-- At a name no function of `fs` has, the reference table is `bi`. -/
theorem refBi_of_find_none (fs : List ModFn) (bi : Builtins) (fuel n : Nat) {g : String}
    (hg : fs.find? (·.name == g) = none) (vals : List Value) :
    refBi fs bi fuel n g vals = bi g vals := by
  cases n <;> simp only [refBi, hg]

/-- The reference table with no function is the base table, at every fuel and call depth. -/
theorem refBi_nil (bi : Builtins) (fuel n : Nat) : refBi [] bi fuel n = bi := by
  cases n <;> rfl

/-- **A call of a function at depth `n + 1` of the reference table** is the run of the
    reference reading of its extraction at depth `n`, from the environment binding its
    parameters to the argument values. -/
theorem refBi_succ (fs : List ModFn) (bi : Builtins) (fuel n : Nat) {g : String} {f : ModFn}
    (hg : fs.find? (·.name == g) = some f) (vals : List Value) :
    refBi fs bi fuel (n + 1) g vals =
      match ((denoteSpine (refBi fs bi fuel n) fuel f.texpr.erase).run
          (paramsEnv (f.params.map (·.1)) vals)).1 with
      | .val v => if (dec f.res v).isSome then some v else none
      | _ => none := by
  simp only [refBi, hg]

/-- **The reference tables are a family of tables for the prepared callees**, when the
    preparation `P` keeps the runs of every function at every depth of the reference table. -/
theorem crateTables_refBi (P : TExpr → ImpExpr) (fs : List ModFn) (bi : Builtins) (fuel : Nat)
    (hsim : ∀ n, ∀ f ∈ fs, f.PrepSim P (refBi fs bi fuel n)) :
    CrateTables (fs.map (ModFn.prep P)) bi (refBi fs bi fuel) where
  base n g hg vals := by
    rw [find?_prep, Option.map_eq_none_iff] at hg
    exact refBi_of_find_none fs bi fuel n hg vals
  zero {g c} hg vals := by
    rw [find?_prep] at hg
    obtain ⟨f, hf, -⟩ := Option.map_eq_some_iff.mp hg
    simp only [refBi, hf]
  call n g c hg vals v hv := by
    rw [find?_prep] at hg
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hg
    rw [refBi_succ fs bi fuel n hf] at hv
    split at hv
    · rename_i w hrun
      split at hv
      · rename_i hd
        cases hv
        obtain ⟨fuel', s, hs⟩ := hsim n f (List.mem_of_find?_eq_some hf) fuel _ _ v
          (Prod.ext hrun rfl) (isControlFlow_of_dec hd)
        exact ⟨hd, fuel', s, hs⟩
      · cases hv
    · cases hv

/-! ## 5. Modules -/

/-- **A linked function of a module**: a function the compiled entry calls by a machine call,
    and whose calls are not inlined. It is a function `fn` of a module with the layout
    `layout` it is compiled under, the machine registers `clob` its code may change, the size
    `frame` in bytes of its stack frame, and its machine code `bytes`. The typed front reads
    the name, the parameter types and the result type of `fn`; the other fields are data of
    the back half of a calling body. -/
structure LinkedFn where
  /-- The function: its name, its typed parameters, its result type and its extraction. -/
  fn : ModFn
  /-- The layout the function is compiled under. -/
  layout : AbiLayout
  /-- The machine registers the code of the function may change. -/
  clob : List String
  /-- The size in bytes of the stack frame of the function. -/
  frame : Nat
  /-- The machine code of the function. -/
  bytes : List (BitVec 8)

/-- **A module**: an entry function, the functions the entry may call, the depth to which
    their calls are inlined, and the linked functions, whose calls stay calls. A function is
    a `ModFn`: its name, its typed parameters, its result type and its extraction. A module
    has no linked function unless one is given. -/
structure HaxModule where
  /-- The extraction of the entry function. -/
  entry : TExpr
  /-- The functions the entry may call; the first function with a name is the one called. -/
  fns : List ModFn
  /-- The call depth to which the functions run, and the number of rounds of inlining. -/
  depth : Nat
  /-- The linked functions: a call of one of them is kept as a call. A name that is also
      the name of a function of `fns` is called as that function. -/
  linked : List LinkedFn := []

namespace HaxModule

/-- The module of the single function `te`: no callee, depth `0`, no linked function. -/
def single (te : TExpr) : HaxModule := ⟨te, [], 0, []⟩

instance : Coe TExpr HaxModule := ⟨single⟩

/-- The prepared callees of a module, under the preparation `P` of bodies. -/
def prepared (P : TExpr → ImpExpr) (m : HaxModule) : List CrateFn := m.fns.map (ModFn.prep P)

/-- The module of a single function has no prepared callee. -/
theorem prepared_single (P : TExpr → ImpExpr) (te : TExpr) : (single te).prepared P = [] := rfl

/-- The linked functions of a module as callees, under the preparation `P` of bodies. The
    call typing reads their names, their parameter types and their result types. -/
def linkedFns (P : TExpr → ImpExpr) (m : HaxModule) : List CrateFn :=
  m.linked.map fun l => l.fn.prep P

/-- A module without linked functions has no linked callee. -/
theorem linkedFns_of_linked_nil (P : TExpr → ImpExpr) {m : HaxModule} (h : m.linked = []) :
    m.linkedFns P = [] := by
  rw [linkedFns, h, List.map_nil]

/-- The module of a single function has no linked callee. -/
theorem linkedFns_single (P : TExpr → ImpExpr) (te : TExpr) : (single te).linkedFns P = [] :=
  rfl

/-- The call typing of a module under the preparation `P`: `crateSigOf` at its prepared
    callees followed by its linked functions, over `hax64SigOf`. A call of a linked function
    on arguments whose types fit its parameter types has its result type. -/
def sigOf (P : TExpr → ImpExpr) (m : HaxModule) : String → List NfTy → Option NfTy :=
  crateSigOf (m.prepared P ++ m.linkedFns P) hax64SigOf

/-- The call typing of the module of a single function is `hax64SigOf`. -/
theorem sigOf_single (P : TExpr → ImpExpr) (te : TExpr) : (single te).sigOf P = hax64SigOf :=
  rfl

/-- The call typing of a module without linked functions is `crateSigOf` at its prepared
    callees over `hax64SigOf`. -/
theorem sigOf_of_linked_nil (P : TExpr → ImpExpr) {m : HaxModule} (h : m.linked = []) :
    m.sigOf P = crateSigOf (m.prepared P) hax64SigOf := by
  rw [sigOf, linkedFns_of_linked_nil P h, List.append_nil]

/-- **The table of a module**: the reference table `refBi` at its functions and its depth,
    each function run at the fuel `fuelC`. A linked function has no entry in the table: its
    name is answered by the base table `bi`. -/
def table (m : HaxModule) (bi : Builtins) (fuelC : Nat) : Builtins :=
  refBi m.fns bi fuelC m.depth

/-- The table of the module of a single function is the base table. -/
theorem table_single (te : TExpr) (bi : Builtins) (fuelC : Nat) :
    (single te).table bi fuelC = bi := rfl

/-- **The source relation of a module** at the base table `bi` and the layout `σ`: the
    reference reading `denoteSpine` of the entry, at the table of the module for some fuel of
    the callees, runs from an environment `σ` reads off the entry state `sa` to the value `v`,
    which is not a control-flow value. A call of a function of the module is the run of the
    reference reading of the extraction of the callee, from the environment binding the names
    of its parameters to the argument values. A call of a linked function is a call of the
    base table `bi` at its name. At a base table that answers the name by no value, a run
    that calls a linked function has no value, and the relation holds of no such run: the
    relation states the source meaning of the inlined calls only. -/
def Runs(bi : Builtins) (σ : AbiLayout) (m : HaxModule) (sa : AState) (v : Value) : Prop :=
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

/-- **The inlining of the calls of a module** in a structured program, under the preparation
    `P`: `crateInline?` at the prepared callees and the depth of the module. -/
def inline? (P : TExpr → ImpExpr) (m : HaxModule) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Option (NFProg nfDialect Γ ts) :=
  crateInline? (m.prepared P) m.depth p

/-- The inlining of the module of a single function returns its argument. -/
theorem inline?_single (P : TExpr → ImpExpr) (te : TExpr) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) : (single te).inline? P p = some p :=
  crateInline?_nil_zero p

/-- **The call typing of a module is sound for the table of the module**, under the typing
    of the base table, when the preparation `P` keeps the runs of every function at every
    depth of the reference table and the base table answers the name of no linked function.
    The hypothesis on the linked functions holds for every module without one. -/
theorem table_typedCalls (P : TExpr → ImpExpr) (m : HaxModule) {bi : Builtins}
    (hT : TypedCalls bi hax64SigOf) (fuelC : Nat)
    (hsim : ∀ n, ∀ f ∈ m.fns, f.PrepSim P (refBi m.fns bi fuelC n))
    (hL : ∀ l ∈ m.linked, ∀ vals, bi l.fn.name vals = none) :
    TypedCalls (m.table bi fuelC) (m.sigOf P) := by
  rw [sigOf, crateSigOf_append]
  refine (crateTables_refBi P m.fns bi fuelC hsim).typedCalls
    (typedCalls_crateSigOf hT _ fun c hc vals => ?_) m.depth
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact hL l hl vals

/-- **The inlining of the calls of a module keeps every successful run, from the table of the
    module to the base table**, under the typing of the base table, when the preparation `P`
    keeps the runs of every function at every depth of the reference table. -/
theorem denote_inline? (P : TExpr → ImpExpr) (m : HaxModule) {bi : Builtins}
    (hT : TypedCalls bi hax64SigOf) (fuelC tf : Nat)
    (hsim : ∀ n, ∀ f ∈ m.fns, f.PrepSim P (refBi m.fns bi fuelC n))
    {Γ : Ctxt nfDialect} {ts : List NfTy} {p p' : NFProg nfDialect Γ ts}
    (h : m.inline? P p = some p') {V : Valuation Γ} {out : Valuation (d := nfDialect) ts}
    (hp : PDenP (m.table bi fuelC) tf p V = some out) : PDenP bi tf p' V = some out :=
  (crateTables_refBi P m.fns bi fuelC hsim).denote_crateInline? hT tf m.depth h hp

/-- The inlining of the calls of a module as a chain step. -/
def inlineStep (P : TExpr → ImpExpr) (m : HaxModule) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.Step (NFProg nfDialect Γ ts) (NFProg nfDialect Γ ts) :=
  crateInlineStep (m.prepared P) m.depth Γ ts

/-- **The certificate of the inlining of the calls of a module**: from the semantics of
    structured programs at the leaf table of the module's table to the semantics at the leaf
    table of the base table `bi`, with equality as input and output relation, when the
    preparation `P` keeps the runs of every function at every depth of the reference
    table. -/
def inlineCert (P : TExpr → ImpExpr) (m : HaxModule) {bi : Builtins}
    (hT : TypedCalls bi hax64SigOf) (fuelC tf : Nat)
    (hsim : ∀ n, ∀ f ∈ m.fns, f.PrepSim P (refBi m.fns bi fuelC n))
    (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.StepCert (m.inlineStep P Γ ts).run
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf (m.table bi fuelC))) _ Γ ts)
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ Γ ts) where
  relIn V W := V = W
  relOut o o' := o = o'
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    exact ⟨o, m.denote_inline? P hT fuelC tf hsim hf hd, rfl⟩

end HaxModule

end CatCrypt.Crypto.Hax
