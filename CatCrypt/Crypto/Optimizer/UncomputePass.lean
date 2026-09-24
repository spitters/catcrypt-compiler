/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.Rewrite.Egraph
public import CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-!
# IR-level uncompute-after-last-use (dead-store elimination) for `Com`

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A **dead-in-continuation** pass over the typed VIR framework: a value bound by
`.var e body` whose result (`.here` in `body`) is **never read anywhere in
`body`** can be freed — its compute step is uncomputed because the value is
dead from the binding point onward.

## Relation to `ComDCE`

`ComDCE.comDCE` handles only the **trailing** dead-binding case: it deletes a
binder whose (already-cleaned) body has collapsed to a bare `.ret v` ignoring
the binder. That requires no interior reindex — only the single outermost
return variable is strengthened.

This pass handles the strictly more general **interior** case:

    let a = e_a              let a = e_a
    let b = e_b(a)     ↦      ret a            (b dead: never read by c or ret)
    let c = e_c(a)           let c = e_c(a)
    ret c                    ret c

Here `b` is interior — there are binders (`c`) *and* a return below it that
ignore it. Dropping `b` changes the intrinsic type of everything below it: each
variable in the continuation must be **strengthened** past the removed binding
(its De Bruijn index drops by one). That strengthening is the content of this
file: `strengthenCom`, which recurses through the body and, at every level,
strengthens variables out of the removed slot — total exactly because the
removed value is provably never read (`comReadsHere body = false`).

## The quantum lever (compute/uncompute ancilla)

In measurement-based / reversible quantum compilation an ancilla is allocated,
*computed* into, used, and then **uncomputed** (run in reverse) to return it to
`|0⟩` so it can be freed. The uncompute is "free" precisely when the ancilla's
value is dead — no later gate reads it. At the classical IR level this is
exactly dead-store elimination: a `.var e body` whose result is dead in `body`
is the compute step of an ancilla that is never read, so the whole binding
(compute + the implicit uncompute) can be dropped. `comReadsHere` is the
IR-level "is the ancilla still live?" test; `strengthenCom`/`uncompute` is the
free reclamation of the slot.

## Contents

* `varStrengthen` / `argsReadSlot` / `comReadsSlot` — the IR last-use / liveness
  oracle. `comReadsSlot [] body = false` ⇒ `body` never reads its head binder, so
  that binder is dead in the continuation and may be uncomputed.
* `varStrengthen!` / `strengthenArgs` / `strengthenExpr` / `strengthenCom` —
  remove the head binding (or any interior slot) from a body that does not read
  it, with full De Bruijn reindexing. Total because the no-read hypothesis
  discharges every `varStrengthen = none` branch.
* `varStrengthen_lookup`, `strengthenArgs_lookup`, `strengthenExpr_denote`,
  `strengthenCom_denote` — lookup/denotation invariance of strengthening.
* `uncompute` — the `Com → Com` interior-dead-binding elimination.
* `uncompute_denote` — **denotation preservation**, by induction. **Not `rfl`.**
* `comLen_strengthenCom`, `comLen_uncompute_le` — the pass is binder-non-
  increasing (it frees, never grows).

All goals closed. `uncompute_denote` checks against only `propext`
and `Quot.sound`. -/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.UncomputePass

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open Ctxt (Var)

/-! ## 1. The liveness oracle: does a body read its head binder?

A binder `.var e body` introduces a fresh head type; inside `body` the bound
value is the De Bruijn index `.here`. The binder is **dead in the continuation**
iff `.here` is never read in `body`. As we descend past each nested binder, the
index we are tracking shifts by one `.there`.

We work relative to a prefix `Δ` of binders descended past: the removed slot
sits at `Δ ++ t :: Γ`, i.e. it is `.there^(|Δ|) .here`. -/

/-- Strengthen a variable out of an interior slot `t` sitting after a prefix
`Δ`: the slot to delete is the head of the `Γ` half of `Δ ++ t :: Γ`. Returns
`none` exactly when the variable *is* that slot, otherwise reindexes it into
`Δ ++ Γ`. -/
def varStrengthen {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t s : d.Ty} :
    (Δ : Ctxt d) → Var (Δ ++ t :: Γ) s → Option (Var (Δ ++ Γ) s)
  | [], .here    => none
  | [], .there v => some v
  | _ :: _, .here    => some .here
  | _ :: Δ', .there v => (varStrengthen Δ' v).map .there

/-- Does an `HVector` of argument variables read the interior slot? `true` iff
some argument *is* the removed slot (i.e. `varStrengthen` returns `none`). -/
def argsReadSlot {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t : d.Ty} :
    (Δ : Ctxt d) → {tys : List d.Ty} →
    HVector (fun ty => Var (Δ ++ t :: Γ) ty) tys → Bool
  | _, [], .nil => false
  | Δ, _ :: _, .cons v rest =>
      (varStrengthen Δ v).isNone || argsReadSlot Δ rest

/-- Number of binders in a `Com` (length of its straight-line let-chain),
independent of the intrinsic context index. Used as the structural-recursion
measure for context-shifting walks. -/
def comLen {d : Dialect} [DialectSignature d] :
    {Γ : Ctxt d} → {u : d.Ty} → Com d Γ u → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => comLen body + 1

@[simp] theorem comLen_var {d : Dialect} [DialectSignature d] {Γ : Ctxt d}
    {t u : d.Ty} (e : Expr d Γ t) (body : Com d (t :: Γ) u) :
    comLen (Com.var e body) = comLen body + 1 := rfl

/-- Does a `Com` body read the interior slot at prefix `Δ`? Descends past each
binder, extending `Δ`. The headline use is `Δ = []`: "does `body` read its head
binder `.here`?". -/
def comReadsSlot {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t : d.Ty} :
    (Δ : Ctxt d) → {u : d.Ty} → Com d (Δ ++ t :: Γ) u → Bool
  | Δ, _, .ret v => (varStrengthen Δ v).isNone
  | Δ, _, .var e body =>
      argsReadSlot Δ e.args || comReadsSlot (_ :: Δ) body
  termination_by _ u c => comLen c
  decreasing_by simp_wf

/-! ## 2. The strengthening rewrite

Given a body that provably does not read the slot, every variable in it can be
strengthened (its `varStrengthen` is `some`). We thread the boolean liveness
hypotheses to discharge the `none` branches, producing a body over the
slot-removed context `Δ ++ Γ`. -/

/-- Strengthen a single variable, given a proof it is not the removed slot. -/
def varStrengthen! {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t s : d.Ty}
    (Δ : Ctxt d) (v : Var (Δ ++ t :: Γ) s)
    (h : (varStrengthen Δ v).isSome) : Var (Δ ++ Γ) s :=
  (varStrengthen Δ v).get h

/-- Strengthen an `HVector` of argument variables, given a proof none of them is
the removed slot. -/
def strengthenArgs {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t : d.Ty} :
    (Δ : Ctxt d) → {tys : List d.Ty} →
    (args : HVector (fun ty => Var (Δ ++ t :: Γ) ty) tys) →
    argsReadSlot Δ args = false →
    HVector (fun ty => Var (Δ ++ Γ) ty) tys
  | _, [], .nil, _ => .nil
  | Δ, _ :: _, .cons v rest, h => by
      simp only [argsReadSlot, Bool.or_eq_false_iff] at h
      exact .cons (varStrengthen! Δ v (by
              simpa [Option.isNone_iff_eq_none, ← Option.isSome_iff_ne_none,
                Bool.not_eq_true] using h.1))
            (strengthenArgs Δ rest h.2)

/-- Strengthen an expression past the removed slot. -/
def strengthenExpr {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t u : d.Ty}
    (Δ : Ctxt d) (e : Expr d (Δ ++ t :: Γ) u)
    (h : argsReadSlot Δ e.args = false) : Expr d (Δ ++ Γ) u where
  op := e.op
  retTy_eq := e.retTy_eq
  args := strengthenArgs Δ e.args h

/-- **The strengthening rewrite.** Remove the slot from a body that does not read
it (`comReadsSlot Δ body = false`), reindexing every variable. Total because the
no-read hypothesis discharges every `varStrengthen = none` branch. -/
def strengthenCom {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t : d.Ty} :
    (Δ : Ctxt d) → {u : d.Ty} → (c : Com d (Δ ++ t :: Γ) u) →
    comReadsSlot Δ c = false → Com d (Δ ++ Γ) u
  | Δ, _, .ret v, h => by
      refine .ret (varStrengthen! Δ v ?_)
      simp only [comReadsSlot] at h
      simpa [Option.isSome_iff_ne_none] using h
  | Δ, _, .var e body, h => by
      simp only [comReadsSlot, Bool.or_eq_false_iff] at h
      exact .var (strengthenExpr Δ e h.1) (strengthenCom (_ :: Δ) body h.2)
  termination_by _ u c => comLen c
  decreasing_by simp_wf

/-! ## 3. Denotation preservation

We relate a valuation over the slot-removed context `Δ ++ Γ` to one over the
original `Δ ++ t :: Γ` by inserting an arbitrary value `x` at the slot. The key
lemma is that strengthening commutes with lookup: a variable that does not read
the slot reads the same value before and after, for *any* inserted `x`. -/

/-- Insert a value `x` at the slot of a slot-removed valuation, producing a
valuation over the original context `Δ ++ t :: Γ`. -/
def valInsert {d : Dialect} [DialectSignature d] [TyDenote d.Ty] {Γ : Ctxt d}
    {t : d.Ty} (x : ⟦t⟧) :
    (Δ : Ctxt d) → Ctxt.Valuation (Δ ++ Γ) → Ctxt.Valuation (Δ ++ t :: Γ)
  | [], V => V.extend x
  | _ :: _, .cons h V => .cons h (valInsert x _ V)

/-- **Lookup invariance of `varStrengthen`.** A variable that is not the removed
slot reads the same value whether or not the slot's value `x` is present. -/
theorem varStrengthen_lookup {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    {Γ : Ctxt d} {t s : d.Ty} (x : ⟦t⟧) :
    ∀ (Δ : Ctxt d) (v : Var (Δ ++ t :: Γ) s) (h : (varStrengthen Δ v).isSome)
      (V : Ctxt.Valuation (Δ ++ Γ)),
      v.lookup (valInsert x Δ V) = (varStrengthen! Δ v h).lookup V
  | [], .here, h, _ => by simp [varStrengthen] at h
  | [], .there w, _, V => by
      simp only [varStrengthen!, varStrengthen, Option.get_some, valInsert]
      rfl
  | _ :: _, .here, _, .cons _ _ => by
      simp [varStrengthen!, varStrengthen, valInsert, Var.lookup]
  | a :: Δ', .there w, h, .cons hx V => by
      simp only [varStrengthen] at h
      have hw : (varStrengthen Δ' w).isSome := by
        cases hc : varStrengthen Δ' w with
        | none => simp [hc] at h
        | some => simp
      have ih := varStrengthen_lookup x Δ' w hw V
      -- LHS: (.there w).lookup (.cons hx (valInsert x Δ' V)) = w.lookup (valInsert x Δ' V)
      show w.lookup (valInsert x Δ' V) = _
      rw [ih]
      -- RHS: varStrengthen! (a::Δ') (.there w) h = .there (varStrengthen! Δ' w hw)
      have hrw : varStrengthen! (a :: Δ') (.there w) h = .there (varStrengthen! Δ' w hw) := by
        simp only [varStrengthen!, varStrengthen, Option.get_map]
      rw [hrw]
      rfl

/-- **Lookup invariance for `strengthenArgs`.** Resolving the strengthened
argument vector against `V` agrees with resolving the original against the
slot-inserted valuation. -/
theorem strengthenArgs_lookup {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    {Γ : Ctxt d} {t : d.Ty} (x : ⟦t⟧) (Δ : Ctxt d) :
    ∀ {tys : List d.Ty}
      (args : HVector (fun ty => Var (Δ ++ t :: Γ) ty) tys)
      (h : argsReadSlot Δ args = false) (V : Ctxt.Valuation (Δ ++ Γ)),
      Expr.lookupArgs (strengthenArgs Δ args h) V =
        Expr.lookupArgs args (valInsert x Δ V)
  | [], .nil, _, _ => rfl
  | _ :: _, .cons v rest, h, V => by
      simp only [argsReadSlot, Bool.or_eq_false_iff] at h
      simp only [strengthenArgs, Expr.lookupArgs]
      have hv : (varStrengthen Δ v).isSome := by
        cases hc : varStrengthen Δ v with
        | none => simp [hc] at h
        | some => rfl
      rw [varStrengthen_lookup x Δ v hv V]
      congr 1
      exact strengthenArgs_lookup x Δ rest h.2 V

/-- Strengthening an `Expr` preserves its denotation under `valInsert`. -/
theorem strengthenExpr_denote {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ : Ctxt d} {t u : d.Ty} (x : ⟦t⟧)
    (Δ : Ctxt d) (e : Expr d (Δ ++ t :: Γ) u)
    (h : argsReadSlot Δ e.args = false) (V : Ctxt.Valuation (Δ ++ Γ)) :
    (strengthenExpr Δ e h).denote V = e.denote (valInsert x Δ V) := by
  simp only [Expr.denote, strengthenExpr]
  rw [strengthenArgs_lookup x Δ e.args h V]

/-- **Denotation preservation for `strengthenCom`.** The strengthened body
denotes the same function, with the removed slot fed an arbitrary value `x` —
because the body provably never reads it. By induction over the let-chain. -/
theorem strengthenCom_denote {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ : Ctxt d} {t : d.Ty} (x : ⟦t⟧) :
    ∀ (Δ : Ctxt d) {u : d.Ty} (c : Com d (Δ ++ t :: Γ) u)
      (h : comReadsSlot Δ c = false) (V : Ctxt.Valuation (Δ ++ Γ)),
      (strengthenCom Δ c h).denote V = c.denote (valInsert x Δ V)
  | Δ, _, .ret v, h, V => by
      simp only [strengthenCom, Com.denote]
      have hv : (varStrengthen Δ v).isSome := by
        simp only [comReadsSlot] at h
        simpa [Option.isSome_iff_ne_none] using h
      exact (varStrengthen_lookup x Δ v hv V).symm
  | Δ, _, .var e body, h, V => by
      simp only [comReadsSlot, Bool.or_eq_false_iff] at h
      simp only [strengthenCom, Com.denote]
      have ih := strengthenCom_denote x (_ :: Δ) body h.2
        (V.extend ((strengthenExpr Δ e h.1).denote V))
      refine ih.trans ?_
      -- valInsert x (t✝::Δ) (V.extend y) = (valInsert x Δ V).extend y; and
      -- strengthenExpr denotes as e under valInsert (strengthenExpr_denote).
      rw [strengthenExpr_denote x Δ e h.1 V]
      rfl
  termination_by Δ u c => comLen c
  decreasing_by simp_wf

/-- `strengthenCom` preserves the number of binders (it only reindexes, never
adds or removes a binder). Needed for termination of the top-level pass. -/
theorem comLen_strengthenCom {d : Dialect} [DialectSignature d] {Γ : Ctxt d}
    {t : d.Ty} :
    ∀ (Δ : Ctxt d) {u : d.Ty} (c : Com d (Δ ++ t :: Γ) u)
      (h : comReadsSlot Δ c = false),
      comLen (strengthenCom Δ c h) = comLen c
  | _, _, .ret _, _ => by simp only [strengthenCom, comLen]
  | Δ, _, .var e body, h => by
      simp only [strengthenCom, comLen]
      congr 1
      exact comLen_strengthenCom (_ :: Δ) body _
  termination_by Δ u c => comLen c
  decreasing_by simp_wf

/-- `[]`-prefix specialization, stated over the context `t :: Γ` so it matches
syntactically (the general lemma's `?Δ ++ t :: Γ` does not unify against
`t :: Γ`). This is the form the top-level pass uses for termination. -/
@[simp] theorem comLen_strengthenCom_nil {d : Dialect} [DialectSignature d]
    {Γ : Ctxt d} {t u : d.Ty} (c : Com d (t :: Γ) u)
    (h : comReadsSlot [] c = false) :
    comLen (strengthenCom [] c h) = comLen c :=
  comLen_strengthenCom [] c h

/-! ## 4. The top-level uncompute pass

At a binder `.var e body`, if `body` does not read this binder
(`comReadsSlot [] body = false`), the bound value is dead from the binding point
on — the compute step is uncomputed and the binder is dropped, strengthening
`body` from `Com d (t :: Γ) s` to `Com d Γ s`. Otherwise the binder is kept and
we recurse into `body`. Unlike `ComDCE.comDCE` this handles **interior** dead
bindings (binders with further binders below them), via `strengthenCom`. -/

/-- **Uncompute-after-last-use.** Drop a binder whose result is dead in the
continuation (never read in `body`), strengthening the body past the removed
slot. Recurses into kept binders. Generic over any `Dialect` — VIR ops are pure,
so dropping a dead binding never drops an effect. -/
def uncompute {d : Dialect} [DialectSignature d] {Γ : Ctxt d} {t : d.Ty} :
    Com d Γ t → Com d Γ t
  | .ret v => .ret v
  | .var e body =>
      if h : comReadsSlot [] body = false then
        -- binder is dead in the continuation: uncompute it
        uncompute (strengthenCom [] body h)
      else
        .var e (uncompute body)
  termination_by c => comLen c
  decreasing_by
    · have e1 : comLen (strengthenCom [] body h) = comLen body :=
        comLen_strengthenCom_nil body h
      show comLen (strengthenCom [] body h) < comLen body + 1
      omega
    · show comLen body < comLen body + 1
      omega

/-- `valInsert` at the empty prefix is exactly `Valuation.extend`. -/
@[simp] theorem valInsert_nil {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    {Γ : Ctxt d} {t : d.Ty} (x : ⟦t⟧) (V : Ctxt.Valuation Γ) :
    valInsert x [] V = V.extend x := rfl

/-- **Denotation preservation for `uncompute`.** The uncomputed program denotes
the same function as the input. The dead-binder case discharges via
`strengthenCom_denote` (with the removed slot fed its now-irrelevant value);
the kept-binder case is the congruence on the continuation. By induction over
the let-chain. **Not `rfl`.** -/
theorem uncompute_denote {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] {Γ : Ctxt d} {t : d.Ty} :
    ∀ (c : Com d Γ t) (V : Ctxt.Valuation Γ), (uncompute c).denote V = c.denote V
  | .ret v, V => by rw [uncompute]
  | .var e body, V => by
      rw [uncompute]
      split
      · next h =>
          refine (uncompute_denote (strengthenCom [] body h) V).trans ?_
          refine (strengthenCom_denote (e.denote V) [] body h V).trans ?_
          simp only [valInsert_nil]
          rfl
      · next h =>
          simp only [Com.denote]
          exact uncompute_denote body (V.extend (e.denote V))
  termination_by c => comLen c
  decreasing_by
    all_goals
      simp only [comLen]
      try rw [comLen_strengthenCom_nil]
      omega

/-! ## 5. The pass is binder-non-increasing

`uncompute` only ever deletes binders (and reindexes survivors, which preserves
binder count). So the number of binders never rises — the headline "freed an
ancilla" guarantee at the count level. -/

/-- **`uncompute` is binder-non-increasing.** Each uncomputed binding lowers the
binder count by one; strengthening survivors preserves it. -/
theorem comLen_uncompute_le {d : Dialect} [DialectSignature d] {Γ : Ctxt d}
    {t : d.Ty} : ∀ c : Com d Γ t, comLen (uncompute c) ≤ comLen c
  | .ret v => by rw [uncompute]
  | .var e body => by
      rw [uncompute]
      split
      · -- dead branch: result is `uncompute (strengthenCom [] body _)`
        exact Nat.le_trans (comLen_uncompute_le _)
          (Nat.le_succ_of_le (Nat.le_of_eq (comLen_strengthenCom_nil _ _)))
      · -- kept branch: result is `.var e (uncompute body)`
        simp only [comLen]
        exact Nat.add_le_add_right (comLen_uncompute_le body) 1
  termination_by c => comLen c
  decreasing_by
    all_goals
      first
        | (simp only [comLen]; omega)
        | exact Nat.lt_succ_of_le (Nat.le_of_eq (comLen_strengthenCom_nil _ _))

/-! ## 6. Self-contained validation: an *interior* dead binding

The motivating case `ComDCE` cannot reach — a dead binder with a *live* binder
**and** a return below it:

    let v0 = x + x        -- live: read by the return
    let v1 = x + x        -- DEAD interior: read by neither v2 nor the return
    let v2 = x + x        -- live: read by the return
    ret v0  ⊕  …          -- (here we simply `ret v0`, v2 incidental)

`ComDCE.comDCE` only peels *trailing* dead binders (it would keep `v1` because
`v2` sits below it as a non-`ret`). `uncompute` removes `v1` and reindexes `v2`
and the return past the freed slot. The demo checks denotation preservation via
the general theorem and a concrete value. -/

/-- A `reg 32` binary `regArith` helper for the demo. -/
def binR32 {Γ : Ctxt jasminDialect} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 32)) : Expr jasminDialect Γ (.reg 32) :=
  { op := .regArith op 32, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The demo program over `[x : reg 32]`:

    v0 = x + x            -- ctx [v0, x];        x = .there .here
    v1 = x + x            -- ctx [v1, v0, x];    x = .there (.there .here)   ← DEAD
    v2 = v0 + v0          -- ctx [v2, v1, v0, x]; v0 = .there (.there .here)
    ret v0                -- v0 = .there (.there .here)

`v1` is interior dead: in context `[v1, v0, x]`, `v2`'s expression reads `v0`
(`.there .here`), not `v1` (`.here`); the `ret` reads `v0`. -/
def demoInteriorDead : Com jasminDialect [.reg 32] (.reg 32) :=
  -- context [x]: x = .here
  .var (binR32 .add .here .here)                                   -- v0 = x + x
    -- context [v0, x]: x = .there .here
    (.var (binR32 .add (.there .here) (.there .here))              -- v1 = x + x  (dead)
      -- context [v1, v0, x]: v0 = .there .here
      (.var (binR32 .add (.there .here) (.there .here))            -- v2 = v0 + v0
        -- context [v2, v1, v0, x]: v0 = .there (.there .here)
        (.ret (.there (.there .here)))))                           -- ret v0

/-- The continuation that sits *below the `v1` binder* of `demoInteriorDead`
(the `v2; ret v0` chain), as a `Com` over the context `[v1, v0, x]`. Its head
binder is `v1` — and it never reads it. -/
def demoContinuation :
    Com jasminDialect [JasminTy.reg 32, JasminTy.reg 32, JasminTy.reg 32]
      (JasminTy.reg 32) :=
  -- context [v1, v0, x]: v1 = .here, v0 = .there .here
  .var (binR32 .add (.there .here) (.there .here))                  -- v2 = v0 + v0
    -- context [v2, v1, v0, x]: v0 = .there (.there .here)
    (.ret (.there (.there .here)))                                  -- ret v0

/-- **The middle binder `v1` is interior dead**: the continuation
below it does not read its head binder. This is exactly the precondition
`uncompute` tests (`comReadsSlot [] body = false`), and it holds. -/
example : comReadsSlot [] demoContinuation = false := by native_decide

/-- **`uncompute` is binder-non-increasing on the demo** (general theorem). -/
example : comLen (uncompute demoInteriorDead) ≤ comLen demoInteriorDead :=
  comLen_uncompute_le demoInteriorDead

/-- **Denotation preserved** for the interior-dead demo, via the general
theorem. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (uncompute demoInteriorDead).denote V = demoInteriorDead.denote V :=
  uncompute_denote demoInteriorDead V

/-- The input valuation `x = 5` for the demo. -/
def demoVal5 : Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 32] :=
  .cons (5 : BitVec 32) .nil

/-- Concretely, on `x = 5`: `v0 = 10`, and the program returns `v0 = 10`. The
denotation is `rfl`-computable (unlike the WF-recursive `uncompute` itself). -/
example : demoInteriorDead.denote demoVal5 = (10 : BitVec 32) := rfl

/-- The uncomputed program agrees on `x = 5`, via the preservation theorem
(reducing the WF-recursive `uncompute` to the `rfl`-computable original). -/
example : (uncompute demoInteriorDead).denote demoVal5 = (10 : BitVec 32) :=
  (uncompute_denote demoInteriorDead demoVal5).trans rfl

/-- The body `ret .here` (a live single binder's continuation) *does* read its
head binder, so `comReadsSlot` reports `true` — `uncompute` keeps the binder. -/
example :
    comReadsSlot (Γ := [JasminTy.reg 32]) (t := JasminTy.reg 32) []
      (Com.ret (d := jasminDialect) Ctxt.Var.here) = true := by native_decide

end CatCrypt.Crypto.Optimizer.UncomputePass
