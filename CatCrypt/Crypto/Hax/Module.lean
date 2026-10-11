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

end CatCrypt.Crypto.Hax
