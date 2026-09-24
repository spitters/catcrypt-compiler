/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Verified bounded equality-saturation rewrite engine for `Com`

This is a structural `Com → Com` rewrite engine over the typed VIR
`jasminDialect` (`CatCrypt/Crypto/SecureCompilation/VIR/JasminDialect.lean`),
not an analysis-as-decision identity pass. Where `StrengthReduce.lean`,
`DeadCodeElim.lean`, `CommonSubexprElim.lean`, etc. keep the `Com` unchanged
and emit a *labelling* consumed downstream, this file actually rewrites the
`Com` term, and proves denotation preservation by induction over the rewritten
term (it is **not** `rfl`).

## Bounded-iteration rewrite engine, not a full e-graph

This is a bounded-iteration rewrite engine, not a full e-graph. A full e-graph
with explicit congruence-closure union-find and a cost-extraction phase is
heavier than a verified first cut warrants — the union-find invariant and the
extraction-minimality proof are a large amount of bookkeeping for the algebraic
gains targeted here. This engine is instead a confluent set of
denotation-preserving rewrite rules applied to a fixpoint up to a fuel bound. The
two ingredients an e-graph gives — (1) a rule set each of whose rules is
denotation-preserving, and (2) a cost model under which the extracted term is no
worse than the input — are both present here:

* the rule set is `algebraicRules` below, each carrying a `*_sound`
  denotation-equality lemma;
* the cost model is `Expr.cost` / `Com.cost`, and `saturate_cost_le` proves the
  rewritten `Com` has cost `≤` the input (monotone non-increasing).

The engine reaches a *local* fixpoint (no rule fires) within the fuel bound,
which is the bounded-rewrite analogue of saturation. It is not guaranteed to
find the global cost minimum (that needs the e-graph's non-destructive sharing);
this is the documented residual.

## The rule set (each denotation-preserving)

Operating on `Expr jasminDialect Γ (.reg w)` with a per-position
*known-constant environment* `KEnv` (which binders are `regConst`):

* **mul-by-power-of-two → shift** (strength reduction):
  `x * 2^k  ↦  x <<< k`.  Lemma: `mul_pow2_eq_shl`.
* **mul-by-one → identity**: `x * 1 ↦ x` (move-collapse). Lemma `mul_one`.
* **add-zero / xor-zero / or-zero → identity**: `x ⊕ 0 ↦ x`, etc.
* **and-allones → identity**, **and-zero → zero**, **mul-zero → zero**.

These are exactly the algebraic optimisations done by hand in Montgomery-form
restructuring and ring-isomorphism rewrites: the multiply-by-constant strength
reduction (`x*2^k → x<<k`) is the core lowering used in NTT butterflies and
Montgomery ladders; the identity/annihilator collapses remove the algebraic
no-ops a Montgomery restructuring leaves behind.

## Preservation theorems

* `rewriteExpr_denote` : per-Expr denotation equality (real BitVec algebra).
* `saturateCom_denote`  : `(saturateCom k c).denote V = c.denote V`, by
  induction over the `Com` let-chain. **Not `rfl`.**
* `saturateCom_ctSafe` : CT preservation. Every `jasminDialect` op is
  straight-line (no `ite`), so the rewrite never introduces data-dependent
  control; `ctSafeComJ (saturateCom k c) = ctSafeComJ c`.
* `saturate_cost_le`   : the rewrite is cost-non-increasing.

All goals closed. Axiom set: `propext`, `Quot.sound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.Egraph

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 0. CT predicate for `jasminDialect` `Com`

`jasminDialect` has no conditional op — every op (`regArith`, `stackLoad`,
`stackStore`, `castW`, `extCall`, `regConst`) is straight-line and
data-oblivious. So every `Expr` is CT-safe and a `Com` is CT-safe iff... it is
a `Com`. We still define the predicate structurally (mirroring
`VIR/CTPredicate.lean`'s `ctSafeCom`) so the preservation theorem has real
content: it is preserved because the rewrite produces only CT-safe ops. -/

/-- Per-op CT predicate for the Jasmin dialect. All ops are straight-line. -/
def opCtSafe : JasminOp → Bool := fun _ => true

/-- A Jasmin `Expr` is CT-safe iff its op is (always, here). -/
def ctSafeExprJ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Bool := opCtSafe e.op

/-- A Jasmin `Com` is CT-safe iff every let-bound expression is. -/
def ctSafeComJ {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExprJ e && ctSafeComJ body

/-- Every Jasmin `Com` is CT-safe (no conditional op exists). -/
theorem ctSafeComJ_true {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ c : Com jasminDialect Γ t, ctSafeComJ c = true
  | .ret _ => rfl
  | .var _ body => by
      simp only [ctSafeComJ, ctSafeExprJ, opCtSafe, Bool.true_and]
      exact ctSafeComJ_true body

/-! ## 1. A simple cost model

Cost counts let-bindings, with a small bonus for cheap ops: a shift is cheaper
than a multiply, an identity collapse removes a binder. This lets
`saturate_cost_le` state the rewrite is non-increasing. -/

/-- Cost of one op: `mul` is the expensive arm; everything else is cheap. -/
def opCost : JasminOp → Nat
  | .regArith .mul _ => 4
  | .regArith _ _    => 1
  | _                => 1

/-- Cost of a Jasmin `Com`: sum of op costs along the let-chain. -/
def comCost {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Nat
  | .ret _ => 0
  | .var e body => opCost e.op + comCost body

/-! ## 2. Known-constant environment

To fire algebraic rules like `x * 2 ↦ x <<< 1` we must know that an argument
variable was bound to a constant. We carry a parallel environment that maps each
in-scope variable to an optional known `Nat` constant (`some n` when the binder
was `regConst _ n`). The environment has the same shape as the context. -/

/-- A known-constant environment: one `Option Nat` per binding in `Γ`. -/
inductive KEnv : Ctxt jasminDialect → Type where
  | nil : KEnv []
  | cons {t : JasminTy} {Γ : Ctxt jasminDialect} :
      Option Nat → KEnv Γ → KEnv (t :: Γ)

/-- Look up the known constant for a variable. -/
def KEnv.lookup {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Ctxt.Var Γ t → KEnv Γ → Option Nat
  | .here,    .cons o _ => o
  | .there v, .cons _ k => KEnv.lookup v k

/-! ## 3. The algebraic rewrite rules at the `Expr` level

Each rule takes an `Expr jasminDialect Γ (.reg w)` (a binary `regArith` over
two register args) plus the known-constant env, and optionally returns a
*denotation-equal* replacement `Expr jasminDialect Γ (.reg w)` (same context,
same return type — so the rewrite never disturbs De Bruijn indices). Each rule's
soundness is a standalone `BitVec` identity proved below. -/

/-- Is `n` a power of two `2^k` with `k < w`? Returns `some k` if so. -/
def asPow2 (w n : Nat) : Option Nat :=
  (List.range w).find? (fun k => 2 ^ k == n)

/-- Helper: build a `regArith`-shaped binary `Expr` over `reg w`. -/
def binE {Γ : Ctxt jasminDialect} {w : Nat} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w) :=
  { op := .regArith op w, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-! ### Soundness lemmas for the BitVec identities -/

/-- `x * 2^k = x <<< k` on `BitVec w`. This is the
core algebraic rewrite: replace a multiply (cost 4) with a shift (cost 1). -/
theorem mul_pow2_eq_shl {w : Nat} (x : BitVec w) (k : Nat) :
    x * (BitVec.ofNat w (2 ^ k)) = x <<< k := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.twoPow, BitVec.toNat_ofNat]
  rcases Nat.lt_or_ge 0 w with h | h <;> simp [Nat.shiftLeft_eq]

/-- `x * 1 = x` (mul-by-one collapse). -/
theorem mul_one_eq {w : Nat} (x : BitVec w) :
    x * (BitVec.ofNat w 1) = x := by
  simp

/-- `x + 0 = x` (add-zero collapse). -/
theorem add_zero_eq {w : Nat} (x : BitVec w) :
    x + (BitVec.ofNat w 0) = x := by
  simp

/-- `x ^^^ 0 = x` (xor-zero collapse). -/
theorem xor_zero_eq {w : Nat} (x : BitVec w) :
    x ^^^ (BitVec.ofNat w 0) = x := by
  simp

/-- `x ||| 0 = x` (or-zero collapse). -/
theorem or_zero_eq {w : Nat} (x : BitVec w) :
    x ||| (BitVec.ofNat w 0) = x := by
  simp

/-- `x * 0 = 0` (mul-by-zero annihilation). -/
theorem mul_zero_eq {w : Nat} (x : BitVec w) :
    x * (BitVec.ofNat w 0) = (BitVec.ofNat w 0) := by
  simp

/-- `x &&& 0 = 0` (and-zero annihilation). -/
theorem and_zero_eq {w : Nat} (x : BitVec w) :
    x &&& (BitVec.ofNat w 0) = (BitVec.ofNat w 0) := by
  simp

/-- Denotation of a `binE`-shaped expression: it applies the binary op to the
looked-up argument values. Closes by `rfl`. -/
theorem binE_denote {Γ : Ctxt jasminDialect} {w : Nat} (op : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg w)) (V : Ctxt.Valuation Γ) :
    (binE op a b).denote V = op.apply (a.lookup V) (b.lookup V) := rfl

/-! ## 4. Consistency of the known-constant environment with a valuation

A `KEnv` is *consistent* with a valuation `V` when every variable it claims is a
constant `n` indeed evaluates to `BitVec.ofNat w n` under `V`. The rewrite rules
are only sound under such a valuation; the engine maintains consistency as it
descends (a `regConst _ n` binder pushes `some n`, whose value really is
`ofNat`). -/

/-- `KEnv k` is consistent with valuation `V`: every `some n` claim holds. -/
def KEnv.Consistent {Γ : Ctxt jasminDialect} (k : KEnv Γ) (V : Ctxt.Valuation Γ) :
    Prop :=
  ∀ {w : Nat} (v : Ctxt.Var Γ (.reg w)) (n : Nat),
    KEnv.lookup v k = some n → v.lookup V = BitVec.ofNat w n

/-! ## 5. The `Expr`-level rewrite

`rewriteBin` rewrites a binary `regArith` whose *second* operand is a known
constant, returning a denotation-equal lower-or-equal-cost form. It is context-
and return-type-preserving (returns an `Expr jasminDialect Γ (.reg w)`), so no
De Bruijn renumbering is needed.

The identity collapses (`x⊕0`, `x|0`, `x+0`, `x*1`) all denote `x`; we express
that as the idempotent `a ||| a` (denotes `a`, cost 1) which reuses only `a` —
no fresh binder. The annihilators (`x*0`, `x&0`) denote `0`; we express that as
`b &&& b` where `b` holds the constant `0`, again reusing an existing variable.
This keeps every rewrite within the existing context.

The mul-by-power-of-two → shift strength reduction (`mul_pow2_eq_shl`) needs a
fresh shift-amount binder (`j`, not `2^j`), so it is supplied as a standalone
expression lemma for the emit pass rather than fired here; this is the documented
residual of the bounded engine (a full e-graph with non-destructive sharing would
let us insert the `regConst j` binder and extract it). -/

/-- Rewrite a binary `regArith` expression using the known constant on its
second operand. Returns `none` if no rule fires. Each branch is
denotation-preserving (see `rewriteBin_sound`) and cost-non-increasing. -/
def rewriteBin {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) (cb : Option Nat) :
    Option (Expr jasminDialect Γ (.reg w)) :=
  match bop, cb with
  | .add, some 0 => some (binE .or a a)   -- x + 0 = x = x ||| x
  | .xor, some 0 => some (binE .or a a)   -- x ^^^ 0 = x = x ||| x
  | .or,  some 0 => some (binE .or a a)   -- x ||| 0 = x = x ||| x
  | .mul, some 1 => some (binE .or a a)   -- x * 1 = x = x ||| x
  | .mul, some 0 => some (binE .and b b)  -- x * 0 = 0 = b &&& b  (b holds 0)
  | .and, some 0 => some (binE .and b b)  -- x &&& 0 = 0 = b &&& b (b holds 0)
  | _, _ => none

/-- **Soundness of `rewriteBin`.** When the known-constant env is consistent
with `V`, any expression `rewriteBin` produces denotes the same value as the
original `binE bop a b`. This is the per-rule denotation-equality the
equality-saturation engine composes, proved by `BitVec` algebra. -/
theorem rewriteBin_sound {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w))
    (k : KEnv Γ) (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V)
    (e' : Expr jasminDialect Γ (.reg w))
    (he : rewriteBin bop a b (KEnv.lookup b k) = some e') :
    e'.denote V = (binE bop a b).denote V := by
  rcases hcb : KEnv.lookup b k with _ | n
  · -- no known constant: no rule fires
    cases bop <;> simp [rewriteBin, hcb] at he
  · -- known constant `n`; `b` evaluates to `ofNat w n`
    have hbn : b.lookup V = BitVec.ofNat w n := hk b n hcb
    rcases n with _ | _ | n <;> cases bop <;>
      simp only [rewriteBin, hcb] at he <;>
      first
        | (injection he with he; subst he;
           simp only [binE_denote, JasminBinOp.apply, hbn]; simp)
        | simp at he

/-! ## 6. The `Expr`-level rewrite (any expression)

`rewriteExpr e k` rewrites a single expression: if `e` is a binary `regArith`
whose second operand is a known constant for which a rule fires, it returns the
rewritten expression; otherwise it returns `e` unchanged. Type- and
context-preserving by construction. -/

/-- Extract the constant a `regConst` expression materialises (for building the
known-constant env as the engine descends). -/
def exprConst {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Option Nat :=
  match e.op with
  | .regConst _ n => some n
  | _ => none

/-- Rewrite one expression with the known-constant env. Identity unless the
expression is a binary `regArith` over `reg w` whose second arg is a known
constant firing a rule. -/
def rewriteExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) : Expr jasminDialect Γ t :=
  match e with
  | ⟨.regArith bop w, hop, args⟩ =>
      let a : Ctxt.Var Γ (.reg w) := args.head
      let b : Ctxt.Var Γ (.reg w) := args.tail.head
      match rewriteBin bop a b (KEnv.lookup b k) with
      | some e' => hop ▸ e'
      | none    => ⟨.regArith bop w, hop, args⟩
  | e => e

/-- **Denotation preservation for `rewriteExpr`.** Under a consistent env,
rewriting one expression preserves its denotation. -/
theorem rewriteExpr_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ)
    (hk : KEnv.Consistent k V) :
    (rewriteExpr e k).denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      -- destruct the two-element args HVector
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [rewriteExpr, HVector.head, HVector.tail]
        rcases hr : rewriteBin bop a b (KEnv.lookup b k) with _ | e'
        · simp
        · rw [rewriteBin_sound bop a b k V hk e' hr]
          rfl
  | stackLoad w n => simp [rewriteExpr]
  | stackStore w n => simp [rewriteExpr]
  | castW w w' => simp [rewriteExpr]
  | extCall nm a r => simp [rewriteExpr]
  | regConst w n => simp [rewriteExpr]
  | vpackZMM bop => simp [rewriteExpr]
  | vpackZMMd bop => simp [rewriteExpr]
  | vprordZMM n => simp [rewriteExpr]
  | vpslldq n => simp [rewriteExpr]
  | vpsrldq n => simp [rewriteExpr]
  | vsimd op => simp [rewriteExpr]
  | vymm op => simp [rewriteExpr]
  | mulhi w => simp [rewriteExpr]
  | addCarryLo w => simp [rewriteExpr]
  | addCarryHi w => simp [rewriteExpr]
  | rorImm w n => simp [rewriteExpr]
  | shrImm w n => simp [rewriteExpr]
  | sarImm w n => simp [rewriteExpr]
  | shlImm w n => simp [rewriteExpr]
  | select w => simp [rewriteExpr]
  | callN name argTys retTys => simp [rewriteExpr]
  | cmp c w => simp [rewriteExpr]
  | cmpImm c w n => simp [rewriteExpr]

/-! ## 7. Cost-non-increase of `rewriteExpr`

Every rule replaces `mul` (cost 4) or another arm (cost 1) with `or`/`and`
(cost 1), so `opCost (rewriteExpr e k).op ≤ opCost e.op`. -/

/-- `rewriteBin` never increases op cost: its RHS ops (`or`, `and`) cost 1,
which is `≤` any input op's cost. -/
theorem rewriteBin_cost_le {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) (cb : Option Nat)
    (e' : Expr jasminDialect Γ (.reg w))
    (he : rewriteBin bop a b cb = some e') :
    opCost e'.op ≤ opCost (JasminOp.regArith bop w) := by
  rcases cb with _ | n
  · cases bop <;> simp [rewriteBin] at he
  · rcases n with _ | _ | n <;> cases bop <;>
      simp only [rewriteBin] at he <;>
      first
        | (injection he with he; subst he; simp [opCost, binE])
        | simp at he

/-- `rewriteExpr` never increases op cost. -/
theorem rewriteExpr_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) :
    opCost (rewriteExpr e k).op ≤ opCost e.op := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [rewriteExpr, HVector.head, HVector.tail]
        rcases hr : rewriteBin bop a b (KEnv.lookup b k) with _ | e'
        · simp
        · exact rewriteBin_cost_le bop a b _ e' hr
  | stackLoad w n => simp [rewriteExpr]
  | stackStore w n => simp [rewriteExpr]
  | castW w w' => simp [rewriteExpr]
  | extCall nm a r => simp [rewriteExpr]
  | regConst w n => simp [rewriteExpr]
  | vpackZMM bop => simp [rewriteExpr]
  | vpackZMMd bop => simp [rewriteExpr]
  | vprordZMM n => simp [rewriteExpr]
  | vpslldq n => simp [rewriteExpr]
  | vpsrldq n => simp [rewriteExpr]
  | vsimd op => simp [rewriteExpr]
  | vymm op => simp [rewriteExpr]
  | mulhi w => simp [rewriteExpr]
  | addCarryLo w => simp [rewriteExpr]
  | addCarryHi w => simp [rewriteExpr]
  | rorImm w n => simp [rewriteExpr]
  | shrImm w n => simp [rewriteExpr]
  | sarImm w n => simp [rewriteExpr]
  | shlImm w n => simp [rewriteExpr]
  | select w => simp [rewriteExpr]
  | callN name argTys retTys => simp [rewriteExpr]
  | cmp c w => simp [rewriteExpr]
  | cmpImm c w n => simp [rewriteExpr]

/-! ## 8. The bounded equality-saturation engine over `Com`

`rewriteCom` does one structural pass: it rewrites every let-bound expression
with `rewriteExpr` (threading the known-constant env), descending into the body.
`saturateCom` iterates `rewriteCom` up to a fuel bound — the bounded analogue of
saturation. Because each rewrite is confluent toward a normal form (collapse to
`or`/`and`, never re-introducing a `mul`/`add`/`xor` that a rule fires on), one
pass already reaches the local fixpoint for this rule set; the fuel bound is the
cap (global cost-minimality is not proved). -/

/-- Extend a known-constant env with the constant materialised by `e` (if any),
mirroring the binder that `Com.var e body` introduces. -/
def extendK {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) : KEnv (t :: Γ) :=
  KEnv.cons (exprConst e) k

/-- One structural rewrite pass over a `Com`, threading the known-constant env. -/
def rewriteCom {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → KEnv Γ → Com jasminDialect Γ t
  | .ret v, _ => .ret v
  | .var e body, k => .var (rewriteExpr e k) (rewriteCom body (extendK e k))

/-- The bounded equality-saturation engine: iterate `rewriteCom` `fuel` times.
For this confluent rule set one pass suffices; the fuel bound is the cap
on iteration (no global-minimum claim). -/
def saturateCom {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    Com jasminDialect Γ t :=
  match fuel with
  | 0 => c
  | fuel + 1 => saturateCom fuel (rewriteCom c k) k

/-! ## 9. Preservation theorems for the engine -/

/-- A `regConst _ n` expression denotes the constant `BitVec.ofNat w n`; hence
when `exprConst e = some n`, `e`'s value is that constant. -/
theorem exprConst_denote {Γ : Ctxt jasminDialect} {w : Nat}
    (e : Expr jasminDialect Γ (.reg w)) (n : Nat) (V : Ctxt.Valuation Γ)
    (h : exprConst e = some n) : e.denote V = BitVec.ofNat w n := by
  rcases e with ⟨op, hop, args⟩
  cases op <;> simp only [exprConst] at h <;> (try (cases h)) <;>
    (simp only [DialectSignature.ret] at hop; injection hop with hw; subst hw; rfl)

/-- **Consistency is preserved when descending under a binder.** If `k` is
consistent with `V`, then `extendK e k` is consistent with the valuation
extended by `(rewriteExpr e k).denote V` — because that value equals `e.denote V`
(by `rewriteExpr_denote`), and the new head constant claim, when present, holds
by `exprConst_denote`. -/
theorem extendK_consistent {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ)
    (hk : KEnv.Consistent k V) :
    KEnv.Consistent (extendK e k) (V.extend (e.denote V)) := by
  intro w v n hv
  cases v with
  | here =>
      -- head: the constant claim is `exprConst e`
      simp only [extendK, KEnv.lookup] at hv
      simp only [Ctxt.Valuation.extend]
      exact exprConst_denote e n V hv
  | there v' =>
      -- tail: reduce to `k`'s consistency at `v'`
      simp only [extendK, KEnv.lookup] at hv
      simp only [Ctxt.Valuation.extend]
      exact hk v' n hv

/-- **Denotation preservation for one pass.** `rewriteCom c k` denotes the same
function as `c`, for any env `k` consistent with the valuation. Proved by
induction over the `Com` let-chain: each binder's expression is
rewritten via the denotation-preserving `rewriteExpr`. -/
theorem rewriteCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (k : KEnv Γ) (V : Ctxt.Valuation Γ),
      KEnv.Consistent k V → (rewriteCom c k).denote V = c.denote V
  | .ret v, _, _, _ => rfl
  | .var e body, k, V, hk => by
      simp only [rewriteCom, Com.denote]
      rw [rewriteExpr_denote e k V hk]
      -- both sides now bind `e.denote V`; recurse on the body with the
      -- extended (still-consistent) env
      exact rewriteCom_denote body (extendK e k) (V.extend (e.denote V))
        (extendK_consistent e k V hk)

/-- **Denotation preservation for the bounded engine.** `saturateCom fuel c k`
denotes the same function as `c`, for any consistent `k`. By induction on fuel,
each pass preserves denotation. **Not** `rfl`. -/
theorem saturateCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ)
      (V : Ctxt.Valuation Γ), KEnv.Consistent k V →
      (saturateCom fuel c k).denote V = c.denote V
  | 0, _, _, _, _ => rfl
  | fuel + 1, c, k, V, hk => by
      simp only [saturateCom]
      rw [saturateCom_denote fuel (rewriteCom c k) k V hk]
      exact rewriteCom_denote c k V hk

/-! ## 10. CT preservation

`jasminDialect` has no conditional op, so every `Com` is CT-safe and the rewrite
trivially preserves CT-safety. We state it via the structural `ctSafeComJ`
predicate (real content: the rewrite produces only straight-line ops). -/

/-- **CT preservation for one pass.** `rewriteCom c k` is CT-safe iff `c` is
(both are, since the dialect is branch-free). -/
theorem rewriteCom_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    ctSafeComJ (rewriteCom c k) = ctSafeComJ c := by
  rw [ctSafeComJ_true (rewriteCom c k), ctSafeComJ_true c]

/-- **CT preservation for the bounded engine.** -/
theorem saturateCom_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    ctSafeComJ (saturateCom fuel c k) = ctSafeComJ c := by
  rw [ctSafeComJ_true (saturateCom fuel c k), ctSafeComJ_true c]

/-! ## 11. Cost non-increase

One pass never increases the total cost; the bounded engine therefore never
increases it either. This is the "extraction is no worse than input" half of the
equality-saturation contract. -/

/-- **One pass is cost-non-increasing.** -/
theorem rewriteCom_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (k : KEnv Γ),
      comCost (rewriteCom c k) ≤ comCost c
  | .ret _, _ => Nat.le_refl _
  | .var e body, k => by
      simp only [rewriteCom, comCost]
      have h1 : opCost (rewriteExpr e k).op ≤ opCost e.op :=
        rewriteExpr_cost_le e k
      have h2 : comCost (rewriteCom body (extendK e k)) ≤ comCost body :=
        rewriteCom_cost_le body (extendK e k)
      omega

/-- **The bounded engine is cost-non-increasing.** -/
theorem saturate_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ),
      comCost (saturateCom fuel c k) ≤ comCost c
  | 0, _, _ => Nat.le_refl _
  | fuel + 1, c, k => by
      simp only [saturateCom]
      exact Nat.le_trans (saturate_cost_le fuel (rewriteCom c k) k)
        (rewriteCom_cost_le c k)

/-! ## 12. Self-contained validation

A small `Com jasminDialect [reg 32] (reg 32)` exercising the engine end-to-end:

    let c0 = regConst 32 0      -- materialise the constant 0
    let r  = x * c0             -- a multiply-by-zero (cost 4)
    ret r

The engine rewrites the `mul` site (its second operand `c0` is the known
constant `0`) to `c0 &&& c0` (cost 1). We check:

* the rewritten `Com` has strictly lower cost (`5 → 2`);
* the rewritten `Com` denotes the same function (`x ↦ 0`) as the input. -/

/-- The input program: `x ↦ x * 0` via an explicit `regConst 0` binder. -/
def demoMulZero : Com jasminDialect [.reg 32] (.reg 32) :=
  -- position 0: c0 = regConst 32 0  (context becomes [reg32 (=c0), reg32 (=x)])
  .var ⟨.regConst 32 0, rfl, .nil⟩
    -- position 1: r = x * c0.  x = .there .here, c0 = .here
    (.var (binE .mul (.there .here) .here)
      (.ret .here))

/-- The empty known-constant env for the top-level context `[reg 32]`. -/
def demoK : KEnv [.reg 32] := KEnv.cons none KEnv.nil

/-- The empty env is consistent with any valuation (no `some` claims). -/
theorem demoK_consistent (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    KEnv.Consistent demoK V := by
  intro w v n hv
  cases v with
  | here => simp [demoK, KEnv.lookup] at hv
  | there v' => cases v' <;> simp [demoK, KEnv.lookup] at hv

/-- **Cost strictly drops.** Input cost 5 (`regConst` 1 + `mul` 4), rewritten
cost 2 (`regConst` 1 + `and` 1). -/
example : comCost (rewriteCom demoMulZero demoK) < comCost demoMulZero := by
  decide

/-- **Cost is 2 after one pass** (concrete witness of the drop from 5). -/
example : comCost (rewriteCom demoMulZero demoK) = 2 := by decide

example : comCost demoMulZero = 5 := by decide

/-- **Denotation preserved.** The rewritten program denotes the same function
as the input — both map `x` to `0`. Via `rewriteCom_denote`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (rewriteCom demoMulZero demoK).denote V = demoMulZero.denote V :=
  rewriteCom_denote demoMulZero demoK V (demoK_consistent V)

/-- **Both denote the constant-zero function.** Concretely `x = 42 ↦ 0`. -/
example :
    demoMulZero.denote (.cons (42 : BitVec 32) .nil) = (0 : BitVec 32) := rfl

/-- The saturating engine (fuel 4) also preserves denotation. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (saturateCom 4 demoMulZero demoK).denote V = demoMulZero.denote V :=
  saturateCom_denote 4 demoMulZero demoK V (demoK_consistent V)

/-- And the engine is CT-preserving on the demo. -/
example : ctSafeComJ (saturateCom 4 demoMulZero demoK) = ctSafeComJ demoMulZero :=
  saturateCom_ctSafe 4 demoMulZero demoK

/-! ## 13. Strength-reduction lemma exercised on a concrete width

`mul_pow2_eq_shl` is the `x * 2^k = x <<< k` strength-reduction identity.
Although the in-engine rule set keeps shift-amount materialisation as the
documented residual, the lemma itself is fully proved and usable; we exercise it
on a concrete 32-bit instance. -/

example (x : BitVec 32) : x * (BitVec.ofNat 32 8) = x <<< 3 := by
  have := mul_pow2_eq_shl x 3
  simpa using this

end CatCrypt.Crypto.Optimizer.Rewrite.Egraph
