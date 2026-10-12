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
public import HaxAscent.Ascent.TableCongr

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
depth of the module, over the table of its linked functions.

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
the module to the table of its linked functions (`HaxModule.denote_inline?`).

The inlining of calls is `NFInline.crateInline?`: the program after `n` rounds of
`NFProg.inline?` at the library `crateLib fs`, on a program accepted by the check
`crateInlineOk fs n`, and a refusal otherwise. As a chain step (`crateInlineStep`) it has the
certificate `crateInlineCert`, from the semantics at the table `crateBi fs bi fuelC n` to the
semantics at `bi`, with equality as input and output relation, under the typing
`TypedCalls bi hax64SigOf` of the base table.

At the module of a single function the call typing is `hax64SigOf`, the table is `bi`, the
source relation is the run of the entry at `bi`, and the inlining returns its argument.

A module also carries linked functions (`LinkedFn`, the field `HaxModule.linked`, empty
unless given): kernels the compiled entry calls by a machine call. A linked function is a
kernel record: its typed interface, its meaning `sem` on argument values, its layout, its
machine contract (precondition, footprint, postcondition and public relation, with the
value-level contract `LinkedFn.post_sem` relating the postcondition to `sem`), and its
machine code. The call typing of a module types a call of a linked function from its
parameter and result types (`HaxModule.sigOf`), and the inlining leaves the call in place.
The table of the module answers the name of a linked function by its meaning
(`HaxModule.linkTable`, the table `linkBi` of the linked functions); the functions of the
module run over that table. The source meaning of a call of a linked function is therefore
the meaning of the kernel, and the inlining keeps the runs from the table of the module to
the table of the linked functions (`HaxModule.denote_inline?`). For a module without linked functions the call typing is that
of the prepared callees (`HaxModule.sigOf_of_linked_nil`), the table of the linked
functions is the base table (`HaxModule.linkTable_of_linked_nil`), and the table of the
module is the reference table of its functions over the base table
(`HaxModule.table_of_linked_nil`).

A function `f` of a module can be replaced by a linked function `l` of its name
(`HaxModule.linkFn`). When the meaning of `l` returns every value the reference meaning of `f`
(`ModFn.refSem`) returns, at every fuel of the callees and every depth of the reference table,
a call the table of the module answers by a value is answered by the same value in the module
with `l` linked, and every run of the source relation of the module is a run of the module
with `l` linked (`HaxModule.runs_linkFn`). The reverse inclusion does not hold: in the module a
call of `f` at depth `0` fails, while the linked function answers it.

The inlining at the library of a list of callees translates their bodies at a call typing over
a typing `base` of the other calls (`hax64SigOf` unless given). At the call typing of the
linked functions of a module, `HaxModule.linkSig`, a body may call a linked function, and the
inlining keeps the runs from the table of the module to the table of its linked functions
(`HaxModule.denote_crateInline?_linkSig`).

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
* `LinkedFn`, `LinkedFn.callee`, `linkBi`, `HaxModule.linkedFns` — a linked function of a
  module as a kernel record, its callee in the call typing, the table of a list of linked
  functions, and the linked functions of a module as callees of the call typing.
* `wordVal`, `insVals`, `insArrArgs` — a word as a source integer, the source values of a
  list of argument words under a list of parameter kinds, and the array positions of a list
  of parameter kinds.
* `HaxModule.sigOf`, `HaxModule.linkTable`, `HaxModule.table` — the call typing, the table
  of the linked functions and the table of a module.
* `HaxModule.Runs` — the source relation of a module at a base table and a layout.
* `HaxModule.inline?`, `HaxModule.inlineStep`, `HaxModule.inlineCert` — the inlining of the
  calls of a module, as a function, as a chain step, and its certificate.
* `HaxModule.linkSig` — the call typing of the linked functions of a module.
* `ModFn.refSem` — the reference meaning of a function of a module at a table and a fuel.
* `HaxModule.linkFn` — the module with a function replaced by a linked function.

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
* `typedCalls_refBi` — the reference table of a list of functions is typed by the call
  typing of their prepared callees over a typing of the base table.
* `linkBi_nil`, `linkBi_of_find_none`, `linkBi_of_find_some`, `typedCalls_linkBi` — the
  table of the linked functions with none is the base table, answers a name of none by the
  base table and a name of one by its meaning, and is typed by the call typing of their
  callees.
* `dec_wordVal`, `insArrArgs_of_scalars` — the word decoding of a word as a source integer
  is the word, and scalar parameter kinds have no array position.
* `HaxModule.linkTable_of_linked_nil`, `HaxModule.table_of_linked_nil` — without linked
  functions the table of the linked functions is the base table, and the table of the module
  is the reference table of its functions over the base table.
* `HaxModule.table_typedCalls`, `HaxModule.denote_inline?` — the table of a module is typed by
  the call typing of the module, and a run at the table of the module is a run of the
  inlined program at the table of the linked functions.
* `typedCalls_linkBi_callees`, `HaxModule.linkTable_typedCalls_linkSig`,
  `HaxModule.denote_crateInline?_linkSig` — the table of the linked functions is typed by the
  call typing of their callees over every typing of it, and the inlining whose callee bodies
  are translated at the call typing of the linked functions keeps the runs from the table of
  the module to the table of its linked functions.
* `callsOK_all`, `denote'_val_of_le`, `closureTable_le`, `denoteSpine_val_of_le` — a run of
  `denote'` or of the reference reading `denoteSpine` to a value is the run at every larger
  table.
* `ModFn.refSem_le`, `refBi_succ_refSem` — the reference meaning at a larger table is larger,
  and a call at depth `n + 1` of the reference table is the reference meaning at depth `n`.
* `HaxModule.refBi_le_linkFn`, `HaxModule.table_le_linkFn`, `HaxModule.runs_linkFn` — when the
  meaning of a linked function returns every value the reference meaning of the function of
  its name returns, the tables of the module are below those of the module with the function
  linked, and a run of the module is a run of the module with the function linked.
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

/-- **The program after `n` rounds of inlining at the library of the callees `fs`**, at the
    typing `base` of the other calls (`hax64SigOf` unless given), on a program accepted by
    `crateInlineOk fs n`, and a refusal otherwise. -/
def crateInline? (fs : List CrateFn) (n : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (base : String → List NfTy → Option NfTy := hax64SigOf) :
    Option (NFProg nfDialect Γ ts) :=
  if crateInlineOk fs n p base = true then some (p.inlineIter (crateLib fs base) n) else none

/-- A result of `crateInline? fs n p` is the program after the `n` rounds, and the check
    `crateInlineOk fs n` accepts `p`. -/
theorem crateInline?_eq_some {fs : List CrateFn} {n : Nat} {Γ : Ctxt nfDialect}
    {ts : List NfTy} {p p' : NFProg nfDialect Γ ts} {base : String → List NfTy → Option NfTy}
    (h : crateInline? fs n p base = some p') :
    crateInlineOk fs n p base = true ∧ p' = p.inlineIter (crateLib fs base) n := by
  unfold crateInline? at h
  split at h
  · exact ⟨‹_›, (Option.some.inj h).symm⟩
  · cases h

/-- With no callee and `0` rounds the inlining returns its argument. -/
theorem crateInline?_nil_zero {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : crateInline? [] 0 p = some p := by
  simp [crateInline?, crateInlineOk_nil_zero, NFProg.inlineIter]

/-- **The checked inlining keeps every successful run, from the builtins with the callees to
    the base builtins.** Under a typing `base` of the builtins `bi`, a successful run of `p` at
    the builtins with the callees `fs` to the call depth `n` (the callees run their bodies at
    the fuel `fuelC`) is a run of a result of `crateInline? fs n p base` at `bi`, with the same
    result. -/
theorem denote_crateInline? (fs : List CrateFn) (bi : Builtins)
    {base : String → List NfTy → Option NfTy} (hT : TypedCalls bi base) (fuelC tf n : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p p' : NFProg nfDialect Γ ts} (h : crateInline? fs n p base = some p') {V : Valuation Γ}
    {out : Valuation (d := nfDialect) ts}
    (hp : PDenP (crateBi fs bi fuelC n) tf p V = some out) : PDenP bi tf p' V = some out := by
  obtain ⟨hok, rfl⟩ := crateInline?_eq_some h
  exact denote_inlineIter_crate fs bi hT fuelC tf n p hok hp

/-- The checked inlining at the callees `fs` with `n` rounds, at the typing `base` of the
    other calls, as a chain step. -/
def crateInlineStep (fs : List CrateFn) (n : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy)
    (base : String → List NfTy → Option NfTy := hax64SigOf) :
    PassChain.Step (NFProg nfDialect Γ ts) (NFProg nfDialect Γ ts) :=
  ⟨"crateInline", fun p => crateInline? fs n p base⟩

/-- **The certificate of the checked inlining**: from the semantics of structured programs of
    `nfDialect` at the leaf table of the builtins with the callees, `crateBi fs bi fuelC n`,
    to the semantics at the leaf table of `bi`, both at the fuel `tf`, with equality as input
    and output relation, under a typing `base` of `bi`. It is `denote_crateInline?`. -/
def crateInlineCert (fs : List CrateFn) {bi : Builtins}
    {base : String → List NfTy → Option NfTy} (hT : TypedCalls bi base)
    (fuelC tf n : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.StepCert (crateInlineStep fs n Γ ts base).run
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
    every fuel `tf`, with the same result, under a typing `base` of `bi`. -/
theorem crateOp_sound (h : CrateTables fs bi T) {base : String → List NfTy → Option NfTy}
    (hT : TypedCalls bi base) (m tf : Nat) :
    ∀ (o : NfOp) (b : NFProg nfDialect o.sig [o.ret]), crateOp fs o base = some b → ∀ x y,
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
        obtain ⟨W, hpre, -, hvW⟩ := impToNF_sound (T m) (crateSigOf fs base)
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
    the operations that call no callee, under a typing `base` of `bi`. -/
theorem soundStep (h : CrateTables fs bi T) {base : String → List NfTy → Option NfTy}
    (hT : TypedCalls bi base) (m tf : Nat) :
    (crateLib fs base).SoundStep (nfDenote (tableOf (T (m + 1)))) (nfDenote (tableOf (T m)))
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
    to the base builtins**, under a typing `base` of `bi`. -/
theorem denote_crateInline? (h : CrateTables fs bi T) {base : String → List NfTy → Option NfTy}
    (hT : TypedCalls bi base) (tf n : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p p' : NFProg nfDialect Γ ts} (hi : crateInline? fs n p base = some p') {V : Valuation Γ}
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
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout ArgKind)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf hax64SigOf tableOf TypedCalls PDenP
  paramsEnv dec dec_sound)
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

/-- **The reference table of the functions `fs` is typed by the call typing of their
    prepared callees**, over a typing `base` of the base table, at every depth and under
    every preparation `P`: a value of a call of a function of `fs` is one `dec` decodes at
    its result type. -/
theorem typedCalls_refBi (P : TExpr → ImpExpr) (fs : List ModFn) {bi : Builtins}
    {base : String → List NfTy → Option NfTy} (hT : TypedCalls bi base) (fuel : Nat) :
    ∀ n, TypedCalls (refBi fs bi fuel n) (crateSigOf (fs.map (ModFn.prep P)) base) := by
  intro n f as r hsig xs v hb
  unfold crateSigOf at hsig
  rw [find?_prep] at hsig
  cases hf : fs.find? (·.name == f) with
  | none =>
      rw [hf] at hsig
      rw [refBi_of_find_none fs bi fuel n hf] at hb
      exact hT f as r hsig xs v hb
  | some g =>
      rw [hf] at hsig
      simp only [Option.map_some] at hsig
      split at hsig
      · cases hsig
        cases n with
        | zero =>
            simp only [refBi, hf] at hb
            cases hb
        | succ n =>
            rw [refBi_succ fs bi fuel n hf] at hb
            split at hb
            · split at hb
              · rename_i hd
                cases hb
                obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hd
                exact ⟨y, hy, dec_sound _ _ _ hy⟩
              · cases hb
            · cases hb
      · cases hsig

/-! ## 5. Modules -/

/-- **A linked function of a module**: a kernel the compiled entry calls by a machine call,
    whose calls are not inlined. The typed front reads its name `name`, its typed parameters
    `params` and its result type `res`. Its meaning is `sem` on the argument values, whose
    values decode at the result type (`sem_res`). The layout `layout` places its arguments and
    its result in machine states. Its machine contract has the shape of the interface
    `X86Backend.Callee.CalleeSig`: the precondition `pre` on entry states, the addresses
    `foot` it may write, the postcondition `post` relating the entry state and the return
    state, and the relation `pub` between entry states that agree on the public arguments,
    which holds between any two states agreeing on `%rsp` and on the registers of the public
    parameters of the layout (`pub_of_regs`). From an entry state satisfying `pre`, every state `post` relates to it holds, in the
    result read-back of the layout, the value of `sem` at the arguments the layout reads
    (`post_sem`), the value-level contract of `ProtocolEmitRealizes.KernelRealizes` at the
    layout. Its machine code is `bytes`, which may change the registers `clob` and uses a
    stack frame of `frame` bytes. -/
structure LinkedFn where
  /-- The name the callers call it by. -/
  name : String
  /-- The parameters, each a name with its type. -/
  params : List (String × NfTy)
  /-- The result type. -/
  res : NfTy
  /-- The meaning of the kernel on the argument values. -/
  sem : List Value → Option Value
  /-- A value of the meaning decodes at the result type. -/
  sem_res : ∀ vals v, sem vals = some v → (dec res v).isSome = true
  /-- The placement of the arguments and of the result in machine states. -/
  layout : AbiLayout
  /-- The precondition on the state at the entry of the kernel. -/
  pre : AState → Prop
  /-- The addresses the kernel may write, from the state at its entry. -/
  foot : AState → BitVec 64 → Prop
  /-- The relation between the entry state and the return state. -/
  post : AState → AState → Prop
  /-- The relation between two entry states that agree on the public arguments. -/
  pub : AState → AState → Prop
  /-- Two entry states that agree on the stack pointer and on the register of each public
      parameter of the layout are related by `pub`. -/
  pub_of_regs : ∀ s₁ s₂, s₁.regs "%rsp" = s₂.regs "%rsp" →
    (∀ a ∈ layout.args, layout.argPub a = true → s₁.regs a.reg = s₂.regs a.reg) → pub s₁ s₂
  /-- **The value-level contract**: from an entry state satisfying the precondition, a return
      state the postcondition relates to it holds, in the result read-back of the layout, the
      value of the meaning at the arguments the layout reads. -/
  post_sem : ∀ sa sa' v, pre sa → post sa sa' →
    sem (layout.args.map (·.read sa)) = some v → layout.ResultOf sa sa' v
  /-- The machine registers the code may change. -/
  clob : List String
  /-- The size in bytes of the stack frame. -/
  frame : Nat
  /-- The machine code. -/
  bytes : List (BitVec 8)

namespace LinkedFn

/-- The callee of a linked function in the call typing: its name, its parameters and its
    result type, with the call of the function on its parameters as body. -/
def callee (l : LinkedFn) : CrateFn :=
  ⟨l.name, l.params, l.res, .app l.name (l.params.map fun p => .var p.1)⟩

end LinkedFn

/-- A word as a source integer. -/
def wordVal (x : BitVec 64) : Value := .int x.toNat

/-- The word decoding of a word as a source integer is the word. -/
theorem dec_wordVal (x : BitVec 64) : dec (.word 64) (wordVal x) = some x := by
  have h : ((x.toNat : Int)).toNat = x.toNat := Int.toNat_natCast _
  simp only [wordVal, dec, h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [if_pos ⟨Int.natCast_nonneg _, by exact_mod_cast x.isLt⟩]

/-- The source values of a list of argument words under a list of parameter kinds: a scalar
    takes one word as a source integer, an array of `m` words takes the next `m` words as a
    source array. -/
def insVals : List ArgKind → List (BitVec 64) → List Value
  | [], _ => []
  | .scalar :: ks, xs => wordVal (xs.headD 0) :: insVals ks xs.tail
  | .words m :: ks, xs => .array ((xs.take m).map wordVal) :: insVals ks (xs.drop m)

/-- The positions of the array parameters of a list of parameter kinds, with the length of
    each array in words; `none` at a scalar position and past the end of the list. -/
def insArrArgs : List ArgKind → Nat → Option Nat
  | [], _ => none
  | .words m :: _, 0 => some m
  | .scalar :: _, 0 => none
  | _ :: ks, i + 1 => insArrArgs ks i

/-- A list of scalar parameter kinds has no array position. -/
theorem insArrArgs_of_scalars : ∀ {ks : List ArgKind}, (∀ k ∈ ks, k = .scalar) →
    insArrArgs ks = fun _ => none
  | [], _ => by funext i; cases i <;> rfl
  | k :: ks, h => by
      obtain rfl := h k List.mem_cons_self
      funext i
      cases i with
      | zero => rfl
      | succ i =>
          exact congrFun (insArrArgs_of_scalars fun k hk => h k (List.mem_cons_of_mem _ hk)) i

/-- **The table of the linked functions `ls` over the table `bi`**: the first linked function
    with a name answers a call by its meaning `sem` on the argument values; every other call
    is a call of `bi`. -/
def linkBi (ls : List LinkedFn) (bi : Builtins) : Builtins := fun g vals =>
  match ls.find? (·.name == g) with
  | some l => l.sem vals
  | none => bi g vals

/-- At a name no linked function of `ls` has, the table of the linked functions is `bi`. -/
theorem linkBi_of_find_none (ls : List LinkedFn) (bi : Builtins) {g : String}
    (hg : ls.find? (·.name == g) = none) (vals : List Value) : linkBi ls bi g vals = bi g vals :=
  by simp only [linkBi, hg]

/-- At the name of a linked function the table of the linked functions is its meaning. -/
theorem linkBi_of_find_some (ls : List LinkedFn) (bi : Builtins) {g : String} {l : LinkedFn}
    (hg : ls.find? (·.name == g) = some l) (vals : List Value) :
    linkBi ls bi g vals = l.sem vals := by
  simp only [linkBi, hg]

/-- With no linked function the table of the linked functions is the base table. -/
theorem linkBi_nil (bi : Builtins) : linkBi [] bi = bi := rfl

/-- The first callee with a name among the callees of linked functions is the callee of the
    first linked function with the name. -/
theorem find?_callee (ls : List LinkedFn) (g : String) :
    (ls.map LinkedFn.callee).find? (·.name == g) = (ls.find? (·.name == g)).map LinkedFn.callee
    := by
  rw [List.find?_map]
  rfl

/-- **The table of the linked functions `ls` is typed by the call typing of their callees**
    over a typing `base` of the base table: a value of a call of a linked function is the value
    of its meaning, which decodes at its result type (`LinkedFn.sem_res`). -/
theorem typedCalls_linkBi (ls : List LinkedFn) {bi : Builtins}
    {base : String → List NfTy → Option NfTy} (hT : TypedCalls bi base) :
    TypedCalls (linkBi ls bi) (crateSigOf (ls.map LinkedFn.callee) base) := by
  intro f as r hsig xs v hb
  unfold crateSigOf at hsig
  rw [find?_callee] at hsig
  cases hf : ls.find? (·.name == f) with
  | none =>
      rw [hf] at hsig
      rw [linkBi_of_find_none ls bi hf] at hb
      exact hT f as r hsig xs v hb
  | some l =>
      rw [hf] at hsig
      simp only [Option.map_some] at hsig
      split at hsig
      · cases hsig
        rw [linkBi_of_find_some ls bi hf] at hb
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (l.sem_res _ _ hb)
        exact ⟨y, hy, dec_sound _ _ _ hy⟩
      · cases hsig

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

/-- The linked functions of a module as callees (`LinkedFn.callee`). The call typing reads
    their names, their parameter types and their result types. -/
def linkedFns (m : HaxModule) : List CrateFn :=
  m.linked.map LinkedFn.callee

/-- A module without linked functions has no linked callee. -/
theorem linkedFns_of_linked_nil {m : HaxModule} (h : m.linked = []) : m.linkedFns = [] := by
  rw [linkedFns, h, List.map_nil]

/-- The module of a single function has no linked callee. -/
theorem linkedFns_single (te : TExpr) : (single te).linkedFns = [] :=
  rfl

/-- The call typing of a module under the preparation `P`: `crateSigOf` at its prepared
    callees followed by its linked functions, over `hax64SigOf`. A call of a linked function
    on arguments whose types fit its parameter types has its result type. -/
def sigOf (P : TExpr → ImpExpr) (m : HaxModule) : String → List NfTy → Option NfTy :=
  crateSigOf (m.prepared P ++ m.linkedFns) hax64SigOf

/-- The call typing of the module of a single function is `hax64SigOf`. -/
theorem sigOf_single (P : TExpr → ImpExpr) (te : TExpr) : (single te).sigOf P = hax64SigOf :=
  rfl

/-- The call typing of a module without linked functions is `crateSigOf` at its prepared
    callees over `hax64SigOf`. -/
theorem sigOf_of_linked_nil (P : TExpr → ImpExpr) {m : HaxModule} (h : m.linked = []) :
    m.sigOf P = crateSigOf (m.prepared P) hax64SigOf := by
  rw [sigOf, linkedFns_of_linked_nil h, List.append_nil]

/-- **The table of the linked functions of a module**: `linkBi` at its linked functions over
    the base table `bi`. A call of a linked function is the value of its meaning `sem` on the
    argument values; every other call is a call of `bi`. The first linked function with a name
    is the one called. -/
def linkTable (m : HaxModule) (bi : Builtins) : Builtins :=
  linkBi m.linked bi

/-- Without linked functions the table of the linked functions is the base table. -/
theorem linkTable_of_linked_nil {m : HaxModule} (h : m.linked = []) (bi : Builtins) :
    m.linkTable bi = bi := by
  rw [linkTable, h, linkBi_nil]

/-- **The table of a module**: the reference table `refBi` at its functions and its depth,
    over the table `linkTable` of its linked functions, each function run at the fuel
    `fuelC`. A call of a function of the module is the run of the reference reading of its
    extraction to the depth of the module; a call of a linked function, from the entry or
    from a function of the module, is the value of the meaning `sem` of the linked function
    on the argument values. A name that both a function and a linked function have is called
    as the function.

    For a module with linked functions this table gives a call of a linked function a
    source meaning. The compiler `compileA` passes the linked word kernels of such a module
    to `compileRegion`; the theorem for its bytes is `RegionLinkCall.compileRegion_correct_linked`,
    and `haxc_correct_auto` states the correctness of `compileA` when every linked function
    is a word kernel. For
    a module without linked functions the table is the reference table of its functions
    over `bi` (`table_of_linked_nil`). -/
def table (m : HaxModule) (bi : Builtins) (fuelC : Nat) : Builtins :=
  refBi m.fns (m.linkTable bi) fuelC m.depth

/-- The table of the module of a single function is the base table. -/
theorem table_single (te : TExpr) (bi : Builtins) (fuelC : Nat) :
    (single te).table bi fuelC = bi := rfl

/-- **The table of a module without linked functions** is the reference table of its
    functions and its depth over the base table. -/
theorem table_of_linked_nil {m : HaxModule} (h : m.linked = []) (bi : Builtins)
    (fuelC : Nat) : m.table bi fuelC = refBi m.fns bi fuelC m.depth := by
  rw [table, linkTable_of_linked_nil h]

/-- **The source relation of a module** at the base table `bi` and the layout `σ`: the
    reference reading `denoteSpine` of the entry, at the table of the module for some fuel of
    the callees, runs from an environment `σ` reads off the entry state `sa` to the value `v`,
    which is not a control-flow value. A call of a function of the module is the run of the
    reference reading of the extraction of the callee, from the environment binding the names
    of its parameters to the argument values. A call of a linked function is the value of its
    meaning `sem` on the argument values (`HaxModule.linkTable`). -/
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
    of the base table: the table of the linked functions is typed by the call typing of the
    linked functions over `hax64SigOf` (`typedCalls_linkBi`), and the table of the module by
    the call typing of the prepared callees over that (`typedCalls_refBi`). -/
theorem table_typedCalls (P : TExpr → ImpExpr) (m : HaxModule) {bi : Builtins}
    (hT : TypedCalls bi hax64SigOf) (fuelC : Nat) :
    TypedCalls (m.table bi fuelC) (m.sigOf P) := by
  rw [sigOf, crateSigOf_append]
  exact typedCalls_refBi P m.fns (typedCalls_linkBi m.linked hT) fuelC m.depth

/-- **The inlining of the calls of a module keeps every successful run, from the table of the
    module to the table of its linked functions**, under the typing `hax64SigOf` of the
    table of the linked functions, when the preparation `P` keeps the runs of every function
    at every depth of the reference table over it. For a module without linked functions the
    table of the linked functions is the base table (`linkTable_of_linked_nil`). -/
theorem denote_inline? (P : TExpr → ImpExpr) (m : HaxModule) {bi : Builtins} {fuelC : Nat}
    (hT : TypedCalls (m.linkTable bi) hax64SigOf) (tf : Nat)
    (hsim : ∀ n, ∀ f ∈ m.fns, f.PrepSim P (refBi m.fns (m.linkTable bi) fuelC n))
    {Γ : Ctxt nfDialect} {ts : List NfTy} {p p' : NFProg nfDialect Γ ts}
    (h : m.inline? P p = some p') {V : Valuation Γ} {out : Valuation (d := nfDialect) ts}
    (hp : PDenP (m.table bi fuelC) tf p V = some out) :
    PDenP (m.linkTable bi) tf p' V = some out :=
  (crateTables_refBi P m.fns _ fuelC hsim).denote_crateInline? hT tf m.depth h hp

/-- The inlining of the calls of a module as a chain step. -/
def inlineStep (P : TExpr → ImpExpr) (m : HaxModule) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.Step (NFProg nfDialect Γ ts) (NFProg nfDialect Γ ts) :=
  crateInlineStep (m.prepared P) m.depth Γ ts

/-- **The certificate of the inlining of the calls of a module**: from the semantics of
    structured programs at the leaf table of the module's table to the semantics at the leaf
    table of the table of its linked functions, with equality as input and output relation,
    when the preparation `P` keeps the runs of every function at every depth of the
    reference table over the table of the linked functions. -/
def inlineCert (P : TExpr → ImpExpr) (m : HaxModule) {bi : Builtins} {fuelC : Nat}
    (hT : TypedCalls (m.linkTable bi) hax64SigOf) (tf : Nat)
    (hsim : ∀ n, ∀ f ∈ m.fns, f.PrepSim P (refBi m.fns (m.linkTable bi) fuelC n))
    (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.StepCert (m.inlineStep P Γ ts).run
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf (m.table bi fuelC))) _ Γ ts)
      (@nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf (m.linkTable bi))) _ Γ ts) where
  relIn V W := V = W
  relOut o o' := o = o'
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    exact ⟨o, m.denote_inline? P hT tf hsim hf hd, rfl⟩

end HaxModule

/-! ## 6. The bodies of the callees at the call typing of the linked functions -/

/-- **The table of the linked functions `ls` is typed by the call typing of their callees over
    every typing `base` of the table**: a value of a call of a linked function is the value of
    its meaning, which decodes at its result type (`LinkedFn.sem_res`). -/
theorem typedCalls_linkBi_callees (ls : List LinkedFn) {bi : Builtins}
    {base : String → List NfTy → Option NfTy} (hT : TypedCalls (linkBi ls bi) base) :
    TypedCalls (linkBi ls bi) (crateSigOf (ls.map LinkedFn.callee) base) := by
  intro f as r hsig xs v hb
  unfold crateSigOf at hsig
  rw [find?_callee] at hsig
  cases hf : ls.find? (·.name == f) with
  | none =>
      rw [hf] at hsig
      exact hT f as r hsig xs v hb
  | some l =>
      rw [hf] at hsig
      simp only [Option.map_some] at hsig
      split at hsig
      · cases hsig
        rw [linkBi_of_find_some ls bi hf] at hb
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (l.sem_res _ _ hb)
        exact ⟨y, hy, dec_sound _ _ _ hy⟩
      · cases hsig

namespace HaxModule

/-- **The call typing of the linked functions of a module**: `crateSigOf` at their callees over
    `hax64SigOf`. A call of a linked function on arguments whose types fit its parameter types
    has its result type. -/
def linkSig (m : HaxModule) : String → List NfTy → Option NfTy :=
  crateSigOf m.linkedFns hax64SigOf

/-- The call typing of a module is the call typing of its prepared callees over the call
    typing of its linked functions. -/
theorem sigOf_eq_linkSig (P : TExpr → ImpExpr) (m : HaxModule) :
    m.sigOf P = crateSigOf (m.prepared P) m.linkSig :=
  crateSigOf_append _ _ _

/-- Without linked functions the call typing of the linked functions is `hax64SigOf`. -/
theorem linkSig_of_linked_nil {m : HaxModule} (h : m.linked = []) : m.linkSig = hax64SigOf := by
  rw [linkSig, linkedFns_of_linked_nil h]
  rfl

/-- **The call typing of the linked functions is sound for the table of the linked
    functions**, under the typing `hax64SigOf` of that table. -/
theorem linkTable_typedCalls_linkSig (m : HaxModule) {bi : Builtins}
    (hT : TypedCalls (m.linkTable bi) hax64SigOf) : TypedCalls (m.linkTable bi) m.linkSig :=
  typedCalls_linkBi_callees m.linked hT

/-- **The inlining whose callee bodies call the linked functions keeps every successful run,
    from the table of the module to the table of its linked functions.** The bodies of the
    prepared callees are translated at the call typing `crateSigOf (m.prepared P) m.linkSig`,
    in which a call of a linked function has its result type; the hypotheses are those of
    `denote_inline?`. -/
theorem denote_crateInline?_linkSig (P : TExpr → ImpExpr) (m : HaxModule) {bi : Builtins}
    {fuelC : Nat} (hT : TypedCalls (m.linkTable bi) hax64SigOf) (tf : Nat)
    (hsim : ∀ n, ∀ f ∈ m.fns, f.PrepSim P (refBi m.fns (m.linkTable bi) fuelC n))
    {Γ : Ctxt nfDialect} {ts : List NfTy} {p p' : NFProg nfDialect Γ ts}
    (h : crateInline? (m.prepared P) m.depth p m.linkSig = some p') {V : Valuation Γ}
    {out : Valuation (d := nfDialect) ts}
    (hp : PDenP (m.table bi fuelC) tf p V = some out) :
    PDenP (m.linkTable bi) tf p' V = some out :=
  (crateTables_refBi P m.fns _ fuelC hsim).denote_crateInline?
    (m.linkTable_typedCalls_linkSig hT) tf m.depth h hp

end HaxModule

/-! ## 7. The reference reading over a larger table -/

open _root_.Hax (Outcome ImpPat)
open _root_.Hax.InlineLocalClosures (closureTable bindAll)
open _root_.Hax.Ascent (callsOK denote'_mono)

/-- Every expression of a list whose expressions pass `callsOK ok` passes `callsOKList ok`. -/
theorem callsOKList_of {ok : String → Bool} :
    ∀ {l : List ImpExpr}, (∀ a ∈ l, callsOK ok a = true) → callsOK.callsOKList ok l = true
  | [], _ => rfl
  | a :: l, h => by
      simp only [callsOK.callsOKList, Bool.and_eq_true]
      exact ⟨h a List.mem_cons_self, callsOKList_of fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

/-- The arms of a match whose bodies pass `callsOK ok` pass `callsOKArms ok`. -/
theorem callsOKArms_of {ok : String → Bool} :
    ∀ {l : List (ImpPat × ImpExpr)}, (∀ pa ∈ l, callsOK ok pa.2 = true) →
      callsOK.callsOKArms ok l = true
  | [], _ => rfl
  | a :: l, h => by
      simp only [callsOK.callsOKArms, Bool.and_eq_true]
      exact ⟨h a List.mem_cons_self, callsOKArms_of fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

/-- Every expression passes `callsOK` at the predicate accepting every name. -/
theorem callsOK_all (e : ImpExpr) : callsOK (fun _ => true) e = true := by
  induction e using _root_.Hax.ImpExpr.ind with
  | app f args ih => simpa [callsOK] using callsOKList_of ih
  | tuple elems ih => simpa [callsOK] using callsOKList_of ih
  | match_ s arms ihs iha => simpa [callsOK, ihs] using callsOKArms_of iha
  | _ => simp_all [callsOK]

/-- **A run of `denote'` to a value is the run at every larger table**: a table `bi'` that
    returns the value `bi` returns wherever `bi` returns one. -/
theorem denote'_val_of_le {bi bi' : Builtins}
    (hsub : ∀ g vals v, bi g vals = some v → bi' g vals = some v) {e : ImpExpr} {fuel : Nat}
    {env env' : Env} {v : Value} (h : denote' bi fuel e env = (.val v, env')) :
    denote' bi' fuel e env = (.val v, env') :=
  denote'_mono (ok := fun _ => true) (fun g _ => hsub g) (callsOK_all e) fuel env v env' h

/-- The table of a closure over a larger table is larger. -/
theorem closureTable_le {bi bi' : Builtins}
    (hsub : ∀ g vals v, bi g vals = some v → bi' g vals = some v) (fuel : Nat) (f : String)
    (ps : List String) (body : ImpExpr) (ρ : Env) :
    ∀ g vals v, closureTable bi fuel f ps body ρ g vals = some v →
      closureTable bi' fuel f ps body ρ g vals = some v := by
  intro g vals v h
  unfold closureTable at h ⊢
  split at h
  · split at h
    · split at h
      · rename_i w hw
        cases h
        have hr : denote' bi fuel body (bindAll ρ ps vals) =
            (.val v, (denote' bi fuel body (bindAll ρ ps vals)).2) := Prod.ext hw rfl
        rw [if_pos ‹_›, if_pos ‹_›]
        simp only [StateT.run]
        rw [denote'_val_of_le hsub hr]
      · cases h
    · cases h
  · rw [if_neg ‹_›]
    exact hsub g vals v h

/-- **A run of the reference reading to a value is the run at every larger table**: a table
    `bi'` that returns the value `bi` returns wherever `bi` returns one gives the run of
    `denoteSpine` the same value and final environment. -/
theorem denoteSpine_val_of_le (fuel : Nat) : ∀ (bi : Builtins) (e : ImpExpr) {bi' : Builtins},
    (∀ g vals v, bi g vals = some v → bi' g vals = some v) →
    ∀ (env env' : Env) (v : Value), (denoteSpine bi fuel e).run env = (.val v, env') →
      (denoteSpine bi' fuel e).run env = (.val v, env') := by
  intro bi e
  induction bi, e using _root_.Hax.InlineLocalClosures.denoteSpine.induct fuel with
  | case1 bi f ps body cont hc ih =>
      intro bi' hsub env env' v h
      simp only [denoteSpine, hc, if_true] at h ⊢
      exact ih env (closureTable_le hsub fuel f ps body env) env env' v h
  | case2 bi f ps body cont hc =>
      intro bi' hsub env env' v h
      simp only [denoteSpine, hc] at h ⊢
      exact denote'_val_of_le hsub h
  | case3 bi x w cont hw ih =>
      intro bi' hsub env env' v h
      rw [denoteSpine.eq_2 _ _ _ _ _ hw] at h ⊢
      rcases hr : denote' bi fuel w env with ⟨o, s⟩
      simp only [StateT.run, bind, StateT.bind, hr] at h
      rcases o with (u|u|u|_|u)
      case val =>
        simp only [StateT.run, bind, StateT.bind, denote'_val_of_le hsub hr]
        cases u
        case controlFlow => exact h
        all_goals
          simp only [StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet] at h ⊢
          exact ih hsub _ _ _ h
      all_goals
        exfalso
        revert h
        simp only [pure, StateT.pure]
        intro h
        cases h
  | case4 bi a b ih =>
      intro bi' hsub env env' v h
      rw [denoteSpine.eq_3] at h ⊢
      rcases hr : denote' bi fuel a env with ⟨o, s⟩
      simp only [StateT.run, bind, StateT.bind, hr] at h
      rcases o with (u|u|u|_|u)
      case val =>
        simp only [StateT.run, bind, StateT.bind, denote'_val_of_le hsub hr]
        cases u
        case controlFlow => exact h
        all_goals exact ih hsub _ _ _ h
      all_goals
        exfalso
        revert h
        simp only [pure, StateT.pure]
        intro h
        cases h
  | case5 bi e h1 h2 h3 =>
      intro bi' hsub env env' v h
      rw [denoteSpine.eq_4 _ _ _ h1 h2 h3] at h ⊢
      exact denote'_val_of_le hsub h

/-! ## 8. A function of a module as a linked function -/

namespace ModFn

/-- **The reference meaning of a function of a module** at the table `T` and the fuel `fuel`:
    the value of the run of the reference reading `denoteSpine` of its extraction, from the
    environment binding the names of its parameters to the argument values, when `dec`
    decodes it at the result type; `none` otherwise. A call of the function at depth `n + 1`
    of the reference table is its reference meaning at the table of depth `n`
    (`refBi_succ_refSem`). -/
def refSem (f : ModFn) (T : Builtins) (fuel : Nat) (vals : List Value) : Option Value :=
  match ((denoteSpine T fuel f.texpr.erase).run (paramsEnv (f.params.map (·.1)) vals)).1 with
  | .val v => if (dec f.res v).isSome then some v else none
  | _ => none

/-- The reference meaning at a larger table is larger. -/
theorem refSem_le (f : ModFn) {T T' : Builtins}
    (hsub : ∀ g vals v, T g vals = some v → T' g vals = some v) (fuel : Nat) :
    ∀ vals v, f.refSem T fuel vals = some v → f.refSem T' fuel vals = some v := by
  intro vals v h
  unfold refSem at h ⊢
  split at h
  · rename_i w hw
    rw [denoteSpine_val_of_le fuel T f.texpr.erase hsub _ _ w (Prod.ext hw rfl)]
    exact h
  · cases h

end ModFn

/-- A call of a function at depth `n + 1` of the reference table is its reference meaning at
    the table of depth `n`. -/
theorem refBi_succ_refSem (fs : List ModFn) (bi : Builtins) (fuel n : Nat) {g : String}
    {f : ModFn} (hg : fs.find? (·.name == g) = some f) (vals : List Value) :
    refBi fs bi fuel (n + 1) g vals = f.refSem (refBi fs bi fuel n) fuel vals :=
  refBi_succ fs bi fuel n hg vals

/-- The first function with the name `g` among the functions of another name than `a` is
    none at `g = a`, and the first function with the name `g` otherwise. -/
theorem find?_filter_name (fs : List ModFn) (a g : String) :
    (fs.filter (·.name != a)).find? (·.name == g) =
      if g = a then none else fs.find? (·.name == g) := by
  induction fs with
  | nil => split <;> rfl
  | cons x xs ih =>
      by_cases hx : x.name = a <;> by_cases hg : g = a <;>
        (simp_all [List.find?_cons]; try simp [beq_false_of_ne (Ne.symm hg)])

/-- The table of the linked functions `l :: ls` answers the name of `l` by the meaning of `l`
    and every other name as the table of `ls`. -/
theorem linkBi_cons (l : LinkedFn) (ls : List LinkedFn) (bi : Builtins) (g : String)
    (vals : List Value) :
    linkBi (l :: ls) bi g vals = if l.name = g then l.sem vals else linkBi ls bi g vals := by
  by_cases h : l.name = g <;> simp [linkBi, h]

namespace HaxModule

/-- **The module with a function linked**: the linked function `l` placed before the linked
    functions of the module, and the functions of the module of the name of `l` removed. A call
    of the name of `l` is the value of the meaning of `l`; every other call is answered as in
    the module. -/
def linkFn (m : HaxModule) (l : LinkedFn) : HaxModule :=
  { m with fns := m.fns.filter (·.name != l.name), linked := l :: m.linked }

/-- **The reference tables of a module are below those of the module with a function
    linked.** Let `f` be the function of the module called by the name of the linked function
    `l`, and let the meaning of `l` return every value the reference meaning of `f` returns at
    each depth of the reference table of the module over its linked functions, at the fuel
    `fuelC`. Then at every depth a call the reference table of the module answers by a value is
    answered by the same value in the module with `l` linked: a call of `f` by the meaning of
    `l`, a call of another function of the module by the run of its extraction at a larger
    table (`denoteSpine_val_of_le`), and every other call by the same linked function or base
    table. -/
theorem refBi_le_linkFn (m : HaxModule) (bi : Builtins) (fuelC : Nat) {f : ModFn}
    {l : LinkedFn} (hf : m.fns.find? (·.name == l.name) = some f)
    (hsem : ∀ n vals v, f.refSem (refBi m.fns (m.linkTable bi) fuelC n) fuelC vals = some v →
      l.sem vals = some v) :
    ∀ n g vals v, refBi m.fns (m.linkTable bi) fuelC n g vals = some v →
      refBi (m.linkFn l).fns ((m.linkFn l).linkTable bi) fuelC n g vals = some v := by
  have hfs : ∀ g, g ≠ l.name →
      (m.linkFn l).fns.find? (·.name == g) = m.fns.find? (·.name == g) := fun g hg => by
    simp only [linkFn]
    rw [find?_filter_name, if_neg hg]
  have hl : (m.linkFn l).fns.find? (·.name == l.name) = none := by
    simp only [linkFn]
    rw [find?_filter_name, if_pos rfl]
  have hlk : ∀ g, g ≠ l.name → ∀ vals,
      (m.linkFn l).linkTable bi g vals = m.linkTable bi g vals := fun g hg vals => by
    simp only [linkFn, linkTable]
    rw [linkBi_cons, if_neg fun h => hg h.symm]
  have hnone : ∀ n g vals v, m.fns.find? (·.name == g) = none →
      refBi m.fns (m.linkTable bi) fuelC n g vals = some v →
        refBi (m.linkFn l).fns ((m.linkFn l).linkTable bi) fuelC n g vals = some v := by
    intro n g vals v hg h
    have hgl : g ≠ l.name := fun h' => by rw [h', hf] at hg; cases hg
    rw [refBi_of_find_none _ _ _ _ hg] at h
    rw [refBi_of_find_none _ _ _ _ ((hfs g hgl).trans hg), hlk g hgl]
    exact h
  intro n
  induction n with
  | zero =>
      intro g vals v h
      cases hg : m.fns.find? (·.name == g) with
      | none => exact hnone 0 g vals v hg h
      | some h' => simp only [refBi, hg] at h; cases h
  | succ k ih =>
      intro g vals v h
      by_cases hgl : g = l.name
      · subst hgl
        rw [refBi_succ_refSem _ _ _ _ hf] at h
        rw [refBi_of_find_none _ _ _ _ hl]
        simp only [linkFn, linkTable]
        rw [linkBi_cons, if_pos rfl]
        exact hsem k vals v h
      · cases hg : m.fns.find? (·.name == g) with
        | none => exact hnone (k + 1) g vals v hg h
        | some h' =>
            rw [refBi_succ_refSem _ _ _ _ hg] at h
            rw [refBi_succ_refSem _ _ _ _ ((hfs g hgl).trans hg)]
            exact h'.refSem_le (ih) fuelC vals v h

/-- **The table of a module is below the table of the module with a function linked**, under
    the hypotheses of `refBi_le_linkFn`: a call the table of the module answers by a value is
    answered by the same value. -/
theorem table_le_linkFn (m : HaxModule) (bi : Builtins) (fuelC : Nat) {f : ModFn}
    {l : LinkedFn} (hf : m.fns.find? (·.name == l.name) = some f)
    (hsem : ∀ n vals v, f.refSem (refBi m.fns (m.linkTable bi) fuelC n) fuelC vals = some v →
      l.sem vals = some v) :
    ∀ g vals v, m.table bi fuelC g vals = some v → (m.linkFn l).table bi fuelC g vals = some v :=
  refBi_le_linkFn m bi fuelC hf hsem m.depth

/-- **A run of a module is a run of the module with a function linked.** Let `f` be the
    function of the module called by the name of the linked function `l`, and let the meaning
    of `l` return every value the reference meaning of `f` returns at every fuel `fuelC` of the
    callees and every depth of the reference table of the module. Then the source relation of
    the module, at the base table `bi` and the layout `σ`, from the state `sa` to the value `v`
    is the source relation of the module in which `f` is the linked function `l`, from `sa` to
    `v`. -/
theorem runs_linkFn (bi : Builtins) (σ : AbiLayout) (m : HaxModule) {f : ModFn} {l : LinkedFn}
    (hf : m.fns.find? (·.name == l.name) = some f)
    (hsem : ∀ fuelC n vals v,
      f.refSem (refBi m.fns (m.linkTable bi) fuelC n) fuelC vals = some v → l.sem vals = some v)
    {sa : AState} {v : Value} (h : Runs bi σ m sa v) : Runs bi σ (m.linkFn l) sa v := by
  obtain ⟨env, fuel, fuelC, env', henv, hrun, hcf⟩ := h
  exact ⟨env, fuel, fuelC, env', henv,
    denoteSpine_val_of_le fuel _ _ (m.table_le_linkFn bi fuelC hf (hsem fuelC)) _ _ _ hrun, hcf⟩

end HaxModule

end CatCrypt.Crypto.Hax
