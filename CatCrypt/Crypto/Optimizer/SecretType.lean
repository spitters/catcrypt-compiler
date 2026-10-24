/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-!
# Secret/public taint qualifier for the `Com`/VIR substrate

A **secret / public taint qualifier** for the typed VIR `jasminDialect`
`Com` substrate, with a proof that one existing optimizer
pass (`peepCom`, the verified local peephole rewrite) preserves the taint
typing invariant. It is the seed of *CT-preservation as a compositional typing
invariant*: rather than re-deriving constant-time safety after every pass from
a global re-analysis, taint flows along the A-normal-form let-chain and each
pass is shown to keep it well-formed.

## The lattice

`SecretLevel` is the two-point lattice `public ⊑ secret` with join `⊔`
(`secret ⊔ _ = _ ⊔ secret = secret`; `public ⊔ public = public`). Joining is
the standard taint-propagation rule: an output is secret as soon as any input
is secret.

## The taint assignment

A `Taint Γ` assigns one `SecretLevel` to every variable in the De Bruijn
context `Γ` (parallel in shape to `Γ`, like the known-constant `KEnv`). Variable
lookup is `Taint.lookup`. The taint of an `Expr` is the join of the taints of
all its argument variables (`exprTaint`) — the data-flow output level.

## The typing invariant

`WellTainted (T : Taint Γ) c` holds when, along every let-binding of `c`, the
newly-bound variable carries exactly the join of its inputs' taints (so the
recorded level of a binder equals `exprTaint` of its expression), and the body
is well-tainted under the extended assignment. A `Com jasminDialect` is a
let-chain without branches, so the invariant tracks where secrecy flows without
over-approximating at a branch. The invariant does not constrain leakage: under a
leakage model a `stackLoad` or `stackStore` emits the address it reads or writes
(`ComLevelCheck.Com.ctLeak`).

## Two passes, two flavours of taint preservation

`peepCom_wellTainted` : `WellTainted T c → WellTainted T (peepCom c)`. The
peephole rewrites a binder `binE bop a b` to `binE bop' a b` reusing the *same*
argument variables `a, b`, so the join of input taints is unchanged
(`peepExpr_exprTaint`): the output level of every binder is preserved exactly.

The bounded equality-saturation engine (`saturateCom`/`rewriteCom`,
`Optimizer/Rewrite/Egraph.lean`) is a structurally different second pass. Its
algebraic collapses *change* a binder's argument set (`x + 0` ↦ `or x x`,
`x * 0` ↦ `and 0 0`), so they do not preserve `exprTaint` exactly. What they do
satisfy is the *declassification* discipline the lattice section describes: each
collapse only ever *drops* an input variable, so a binder's taint can only move
**down** the lattice, never up. We prove this two ways:
* `rewriteCom_taint_mono` : one pass declassifies per binder
  (`ComTaintLe`, threaded down the chain);
* `saturateCom_comMaxTaint_le` : the bounded engine never raises the program's
  overall secrecy level `comMaxTaint` (the join of all binder taints) — the
  transitively-composable scalar form, since the per-binder `ComTaintLe` is a
  conservative over-approximation and not transitive in the two-point lattice.

So the compositional-CT invariant extends across two passes: peephole *preserves*
taint, the egraph engine *declassifies monotonically* — both keep the program
within its taint budget. `WellTainted` itself is total (each binder's level is
*defined* as `exprTaint`), so the egraph pass's content here is the
monotonicity, not a bare `WellTainted` lift.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SecretType

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-! ## 1. The secrecy lattice -/

/-- The two-point secrecy lattice: a value is either `pub`(lic) or `sec`(ret).
    (`public`/`secret` are reserved tokens, so the constructors are `pub`/`sec`.) -/
inductive SecretLevel where
  /-- A public value (may be leaked through timing). -/
  | pub
  /-- A secret value (must not influence observable timing). -/
  | sec
  deriving DecidableEq, Repr

namespace SecretLevel

/-- Join of two secrecy levels: `sec` is absorbing (taint propagation —
    an output is secret as soon as any input is secret). -/
def join : SecretLevel → SecretLevel → SecretLevel
  | .sec, _ => .sec
  | _, .sec => .sec
  | .pub, .pub => .pub

@[inherit_doc] infixl:65 " ⊔ₛ " => join

/-- `sec` absorbs on the left: `sec ⊔ x = sec`. -/
@[simp] theorem sec_join (x : SecretLevel) : (SecretLevel.sec ⊔ₛ x) = .sec := rfl

/-- `sec` absorbs on the right: `x ⊔ sec = sec`. -/
@[simp] theorem join_sec (x : SecretLevel) : (x ⊔ₛ SecretLevel.sec) = .sec := by
  cases x <;> rfl

/-- `pub` is the join identity on the left. -/
@[simp] theorem pub_join (x : SecretLevel) : (SecretLevel.pub ⊔ₛ x) = x := by
  cases x <;> rfl

/-- `pub` is the join identity on the right. -/
@[simp] theorem join_pub (x : SecretLevel) : (x ⊔ₛ SecretLevel.pub) = x := by
  cases x <;> rfl

/-- Join is idempotent. -/
@[simp] theorem join_self (x : SecretLevel) : (x ⊔ₛ x) = x := by cases x <;> rfl

/-- Join is commutative. -/
theorem join_comm (x y : SecretLevel) : (x ⊔ₛ y) = (y ⊔ₛ x) := by
  cases x <;> cases y <;> rfl

/-- Join is associative. -/
theorem join_assoc (x y z : SecretLevel) : ((x ⊔ₛ y) ⊔ₛ z) = (x ⊔ₛ (y ⊔ₛ z)) := by
  cases x <;> cases y <;> cases z <;> rfl

end SecretLevel

/-! ## 2. The taint assignment over a De Bruijn context

`Taint Γ` carries one `SecretLevel` per binding in the typing context `Γ`,
parallel in shape to `Γ` exactly like the known-constant environment `KEnv`. -/

/-- A taint assignment: one `SecretLevel` per binding in `Γ`. -/
inductive Taint : Ctxt jasminDialect → Type where
  | nil : Taint []
  | cons {t : JasminTy} {Γ : Ctxt jasminDialect} :
      SecretLevel → Taint Γ → Taint (t :: Γ)

namespace Taint

/-- Look up the secrecy level recorded for a variable. -/
def lookup {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Ctxt.Var Γ t → Taint Γ → SecretLevel
  | .here,    .cons s _ => s
  | .there v, .cons _ T => lookup v T

end Taint

/-! ## 3. The taint of an expression = join of its argument taints

The output secrecy level of an operation is the join of the secrecy levels of
all its argument variables (data-flow taint propagation). We fold the lattice
join over the `HVector` of argument variables; the same rule applies to every op. -/

/-- Fold the secrecy join over an `HVector` of argument variables, starting from
    `pub` (the join identity). -/
def argsTaint {Γ : Ctxt jasminDialect} (T : Taint Γ) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → SecretLevel
  | [], .nil => .pub
  | _ :: _, .cons v rest => (T.lookup v) ⊔ₛ (argsTaint T rest)

/-- The output secrecy level of an expression: the join of its argument taints. -/
def exprTaint {Γ : Ctxt jasminDialect} {t : JasminTy}
    (T : Taint Γ) (e : Expr jasminDialect Γ t) : SecretLevel :=
  argsTaint T e.args

/-! ## 4. The taint-typing invariant `WellTainted`

`WellTainted T c` holds when each let-binding records, as the secrecy level of
its newly-bound variable, exactly the join of its inputs' taints, and the body
is well-tainted under that extended assignment. This makes "every operation's
output taint = join of input taints" a structural invariant of the program. -/

/-- The taint-typing invariant: every binder's recorded level equals the join of
    its inputs', all the way down the let-chain. -/
def WellTainted {Γ : Ctxt jasminDialect} {t : JasminTy}
    (T : Taint Γ) : Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body => WellTainted (T.cons (exprTaint T e)) body

/-! ## 5. Peephole preserves the argument taints

`peepBin` / `peepExpr` rewrite a binary `regArith` `binE bop a b` to
`binE bop' a b`, reusing the *same* argument variables `a, b`. Hence the join of
the argument taints — and therefore `exprTaint` — is unchanged. -/

/-- `peepBin` preserves the argument taints: the rewritten expression uses the
    same two variables `a, b`, so the join `lookup a ⊔ lookup b` is unchanged. -/
theorem peepBin_exprTaint {Γ : Ctxt jasminDialect} {w : Nat}
    (T : Taint Γ) (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w))
    (e' : Expr jasminDialect Γ (.reg w))
    (he : peepBin bop a b = some e') :
    exprTaint T e' = exprTaint T (binE bop a b) := by
  unfold peepBin at he
  by_cases hv : varEq a b
  · simp only [hv, ite_true] at he
    cases bop <;>
      first
        | (injection he with he; subst he; rfl)
        | simp at he
  · simp only [hv, Bool.false_eq_true, ite_false] at he
    exact absurd he (by simp)

/-- `peepExpr` preserves the output taint of an expression: it either leaves the
    expression unchanged or rewrites a binary `regArith` to one over the *same*
    argument variables. -/
theorem peepExpr_exprTaint {Γ : Ctxt jasminDialect} {t : JasminTy}
    (T : Taint Γ) (e : Expr jasminDialect Γ t) :
    exprTaint T (peepExpr e) = exprTaint T e := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [peepExpr, HVector.head, HVector.tail]
        rcases hr : peepBin bop a b with _ | e'
        · rfl
        · rw [peepBin_exprTaint T bop a b e' hr]; rfl
  | stackLoad w n => rfl
  | stackStore w n => rfl
  | castW w w' => rfl
  | extCall nm a r => rfl
  | regConst w n => rfl
  | vpackZMM bop => rfl
  | vpackZMMd bop => rfl
  | vprordZMM n => rfl
  | vpslldq n => rfl
  | vpsrldq n => rfl
  | vsimd op => rfl
  | vymm op => rfl
  | mulhi w => rfl
  | addCarryLo w => rfl
  | addCarryHi w => rfl
  | rorImm w n => rfl
  | shrImm w n => rfl
  | sarImm w n => rfl
  | shlImm w n => rfl
  | select w => rfl
  | callN name argTys retTys => rfl
  | cmp c w => rfl
  | cmpImm c w n => rfl
  | stackZero w n => rfl
  | stackStoreImm w n i => rfl

/-! ## 6. The compositional-CT seed: peephole preserves `WellTainted`

Because every binder's output taint is preserved by `peepExpr`
(`peepExpr_exprTaint`), the taint assignment threaded down the chain is the same
for `c` and `peepCom c`, so the invariant transfers binder-by-binder. This is
the first "a pass preserves the secret-type qualifier" lemma. -/

/-- **Peephole preserves the taint-typing invariant.** If `c` is well-tainted
    under `T`, so is `peepCom c`: the pass keeps every binder's output level
    equal to the join of its inputs'. The base case of compositional CT. -/
theorem peepCom_wellTainted {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (T : Taint Γ) (c : Com jasminDialect Γ t),
      WellTainted T c → WellTainted T (peepCom c)
  | _, .ret v, h => h
  | T, .var e body, h => by
      simp only [peepCom, WellTainted]
      simp only [WellTainted] at h
      rw [peepExpr_exprTaint T e]
      exact peepCom_wellTainted (T.cons (exprTaint T e)) body h

/-! ## 7. Self-contained validation

A small `Com jasminDialect [reg 32] (reg 32)` exercising the qualifier: with the
single input variable marked `sec`, the self-subtract demo `let z = x - x`
binds `z` at the join of its inputs `sec ⊔ sec = sec`. The peephole
rewrites the binder to `xor x x` and the program stays well-tainted under the
same assignment. -/

/-- The taint assignment marking the single input `[reg 32]` variable `sec`. -/
def demoTaint : Taint [.reg 32] := .cons .sec .nil

/-- The self-subtract demo is well-tainted under the `sec`-input assignment:
    `z = x - x` records the join `sec ⊔ sec = sec` for `z`. -/
example : WellTainted demoTaint demoSelfSub := by
  simp [WellTainted, demoSelfSub, demoTaint, binE]

/-- **The peephole preserves well-taintedness on the demo.** After rewriting
    `x - x` to the `xor x x` zeroing idiom, the program is still well-tainted
    under the same `sec`-input assignment. Via `peepCom_wellTainted`. -/
example : WellTainted demoTaint (peepCom demoSelfSub) :=
  peepCom_wellTainted demoTaint demoSelfSub (by
    simp [WellTainted, demoSelfSub, demoTaint, binE])

/-- The rewritten binder's output taint equals the original's: the rewrite
    `x - x ↦ xor x x` reuses `x`, so the join `sec ⊔ sec` is unchanged. -/
example :
    exprTaint demoTaint (peepExpr (binE .sub (Γ := [.reg 32]) .here .here))
      = exprTaint demoTaint (binE .sub (Γ := [.reg 32]) .here .here) :=
  peepExpr_exprTaint demoTaint _

/-! ## 8. A second, structurally-different pass: the egraph saturation
declassifies *monotonically*

The peephole pass (§6) preserves the binder taints **exactly**: it rewrites
`binE bop a b ↦ binE bop' a b` reusing the *same* argument variables. The
bounded equality-saturation engine `saturateCom`/`rewriteCom`
(`Optimizer/Rewrite/Egraph.lean`) is structurally different: its algebraic
collapses *change* the argument set of a binder — `x + 0` (args `x`, `zero`)
becomes `or x x` (args `x`, `x`); `x * 0` (args `x`, `zero`) becomes
`and zero zero`. So `exprTaint` is **not** preserved exactly.

What it satisfies is monotonicity: every rewrite only ever drops one of the two
input variables, so a binder's output taint can only **stay the same or move down**
the lattice (`⊑ₛ`) — never up. The engine never turns a public binder secret. We
capture this as `rewriteCom_taint_mono`: the rewritten
program's binder taints are pointwise `⊑ₛ` the originals, lifted along the
let-chain and through the fuel iteration to `saturateCom_taint_mono`.

This is the substantive content for this pass: `WellTainted` is *total* (each
binder's level is *defined* as `exprTaint`, so there is no separate recorded
level that could mismatch), hence a bare `WellTainted T c → WellTainted T (…)`
would be vacuous. The invariant the egraph pass adds over peephole's
exact preservation is taint-monotonicity (declassification-only). -/

namespace SecretLevel

/-- The lattice order: `pub ⊑ₛ sec`, reflexive. `x ⊑ₛ y` iff `x ⊔ₛ y = y`. -/
def leq : SecretLevel → SecretLevel → Prop
  | .pub, _ => True
  | .sec, .sec => True
  | .sec, .pub => False

@[inherit_doc] infixl:50 " ⊑ₛ " => leq

/-- The order is reflexive. -/
@[simp] theorem leq_refl (x : SecretLevel) : x ⊑ₛ x := by cases x <;> trivial

/-- A level is below any join it participates in (left). -/
theorem leq_join_left (x y : SecretLevel) : x ⊑ₛ (x ⊔ₛ y) := by
  cases x <;> cases y <;> trivial

/-- A level is below any join it participates in (right). -/
theorem leq_join_right (x y : SecretLevel) : y ⊑ₛ (x ⊔ₛ y) := by
  cases x <;> cases y <;> trivial

/-- The order is transitive. -/
theorem leq_trans {x y z : SecretLevel} (h1 : x ⊑ₛ y) (h2 : y ⊑ₛ z) : x ⊑ₛ z := by
  cases x <;> cases y <;> cases z <;>
    first
      | trivial
      | exact absurd h1 (by simp [leq])
      | exact absurd h2 (by simp [leq])

end SecretLevel

/-- `exprTaint` of a `binE`-shaped expression is exactly the join of its two
argument variables' taints (the trailing `⊔ₛ pub` from the empty tail collapses
by `join_pub`). -/
theorem exprTaint_binE {Γ : Ctxt jasminDialect} {w : Nat}
    (T : Taint Γ) (op : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) :
    exprTaint T (binE op a b) = (T.lookup a ⊔ₛ T.lookup b) := by
  show (T.lookup a ⊔ₛ (T.lookup b ⊔ₛ SecretLevel.pub)) = _
  rw [SecretLevel.join_pub]

/-- **`rewriteBin` is taint-non-increasing.** Each algebraic collapse rewrites
`binE bop a b` to either `binE .or a a` (drops `b`) or `binE .and b b` (drops
`a`), so the output taint is one of `lookup a`, `lookup b`, each `⊑ₛ` the input
join `lookup a ⊔ₛ lookup b`. The engine therefore only ever *declassifies*. -/
theorem rewriteBin_taint_le {Γ : Ctxt jasminDialect} {w : Nat}
    (T : Taint Γ) (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) (cb : Option Nat)
    (e' : Expr jasminDialect Γ (.reg w))
    (he : rewriteBin bop a b cb = some e') :
    exprTaint T e' ⊑ₛ exprTaint T (binE bop a b) := by
  rw [exprTaint_binE]
  rcases cb with _ | n
  · cases bop <;> simp [rewriteBin] at he
  · rcases n with _ | _ | n <;> cases bop <;>
      simp only [rewriteBin] at he <;>
      first
        | (injection he with he; subst he; rw [exprTaint_binE];
           simp only [SecretLevel.join_self];
           first | exact SecretLevel.leq_join_left _ _
                 | exact SecretLevel.leq_join_right _ _)
        | simp at he

/-- **`rewriteExpr` is taint-non-increasing.** Either the expression is left
unchanged (taint equal, hence `⊑ₛ` by reflexivity) or a `binE` collapse fires
(`rewriteBin_taint_le`). -/
theorem rewriteExpr_taint_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (T : Taint Γ) (e : Expr jasminDialect Γ t) (k : KEnv Γ) :
    exprTaint T (rewriteExpr e k) ⊑ₛ exprTaint T e := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [rewriteExpr, HVector.head, HVector.tail]
        rcases hr : rewriteBin bop a b (KEnv.lookup b k) with _ | e'
        · simp
        · -- the rewritten expr is `hop ▸ e'` = `e'`; its taint is bounded
          have := rewriteBin_taint_le T bop a b (KEnv.lookup b k) e' hr
          -- `binE bop a b` has the same args HVector as the original expr
          simpa [exprTaint, binE] using this
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
  | stackZero w n => simp [rewriteExpr]
  | stackStoreImm w n i => simp [rewriteExpr]

/-- Pointwise taint-monotonicity of two `Com`s of the same shape under the same
taint assignment `T`: `c'` declassifies `c` if every binder of `c'` has taint
`⊑ₛ` the corresponding binder of `c`, and the bodies relate under the extended
assignments. Since `rewriteExpr` can only *lower* a binder's taint, the two
assignments threaded down the chain may diverge — so we compare against the
input's threaded assignment on both sides (the conservative bound). -/
def ComTaintLe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (T : Taint Γ) : Com jasminDialect Γ t → Com jasminDialect Γ t → Prop
  | .ret _, .ret _ => True
  | @Com.var _ _ _ t1 _ e1 b1, @Com.var _ _ _ t2 _ e2 b2 =>
      if h : t1 = t2 then
        (exprTaint T e1 ⊑ₛ exprTaint T (h ▸ e2)) ∧
          ComTaintLe (T.cons (exprTaint T (h ▸ e2))) (h ▸ b1) b2
      else False
  | _, _ => False

/-- **The egraph pass declassifies monotonically (one pass).** Every binder of
`rewriteCom c k` has taint `⊑ₛ` the corresponding binder of `c`, threaded down
the let-chain. Structurally different from `peepCom_wellTainted` (§6): the
peephole *preserves* taint exactly, whereas the egraph collapses *drop* an
argument variable and so can only move taint *down* the lattice — the CT-safe
declassification discipline of the module header, as a proved invariant. -/
theorem rewriteCom_taint_mono {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (T : Taint Γ) (c : Com jasminDialect Γ t) (k : KEnv Γ),
      ComTaintLe T (rewriteCom c k) c
  | _, .ret _, _ => trivial
  | T, .var e body, k => by
      simp only [rewriteCom, ComTaintLe]
      exact ⟨rewriteExpr_taint_le T e k,
        rewriteCom_taint_mono (T.cons (exprTaint T e)) body (extendK e k)⟩

/-- `ComTaintLe` is reflexive (every binder is `⊑ₛ` itself). -/
theorem ComTaintLe_refl {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (T : Taint Γ) (c : Com jasminDialect Γ t), ComTaintLe T c c
  | _, .ret _ => trivial
  | T, .var e body => by
      simp only [ComTaintLe]
      exact ⟨SecretLevel.leq_refl _, ComTaintLe_refl (T.cons (exprTaint T e)) body⟩

/-! ### Transitivity of `ComTaintLe` (needed for the fuel iteration)

Iterating the pass composes per-pass declassifications, so we need `ComTaintLe`
to be transitive. The threaded assignments of the three programs differ (the
body env is advanced by the *reference* program's binder taint), so transitivity
rests on an **env-weakening** lemma: lowering an entry of the threaded
assignment can only lower `exprTaint`, hence preserves the `⊑ₛ` comparisons down
the chain. -/

/-- Join is monotone in both arguments. -/
theorem SecretLevel.join_mono {a a' b b' : SecretLevel}
    (ha : a ⊑ₛ a') (hb : b ⊑ₛ b') : (a ⊔ₛ b) ⊑ₛ (a' ⊔ₛ b') := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    first | trivial | exact absurd ha (by simp [SecretLevel.leq])
          | exact absurd hb (by simp [SecretLevel.leq])

/-- Pointwise order on taint assignments: `T ⊑ T'` if every variable's recorded
level in `T` is `⊑ₛ` its level in `T'`. -/
def TaintLe {Γ : Ctxt jasminDialect} (T T' : Taint Γ) : Prop :=
  ∀ {t : JasminTy} (v : Ctxt.Var Γ t), T.lookup v ⊑ₛ T'.lookup v

/-- `TaintLe` is reflexive. -/
theorem TaintLe.refl {Γ : Ctxt jasminDialect} (T : Taint Γ) : TaintLe T T :=
  fun _ => SecretLevel.leq_refl _

/-- Extending two ordered assignments by ordered head levels stays ordered. -/
theorem TaintLe.cons {Γ : Ctxt jasminDialect} {th : JasminTy} {T T' : Taint Γ}
    {s s' : SecretLevel} (hs : s ⊑ₛ s') (hT : TaintLe T T') :
    TaintLe (Γ := th :: Γ) (T.cons s) (T'.cons s') := by
  intro u v
  cases v with
  | here => exact hs
  | there v' => exact hT v'

/-- `argsTaint` is monotone in the assignment. -/
theorem argsTaint_mono {Γ : Ctxt jasminDialect} {T T' : Taint Γ} (hT : TaintLe T T') :
    ∀ {tys : List JasminTy} (args : HVector (fun ty => Ctxt.Var Γ ty) tys),
      argsTaint T args ⊑ₛ argsTaint T' args
  | [], .nil => trivial
  | _ :: _, .cons v rest =>
      SecretLevel.join_mono (hT v) (argsTaint_mono hT rest)

/-- `exprTaint` is monotone in the assignment. -/
theorem exprTaint_mono {Γ : Ctxt jasminDialect} {t : JasminTy} {T T' : Taint Γ}
    (hT : TaintLe T T') (e : Expr jasminDialect Γ t) :
    exprTaint T e ⊑ₛ exprTaint T' e :=
  argsTaint_mono hT e.args

/-! ### The program's overall secrecy level, and that the engine never raises it

`ComTaintLe` is a *conservative* per-binder comparison: it threads the body env
by the reference program's binder taint, which over-approximates the rewritten
program's. That over-approximation is sound for the one-pass claim
(`rewriteCom_taint_mono`) but it is **not** transitive — in the two-point
lattice, lowering or raising the shared env entry by the same amount does not
preserve a pairwise `⊑ₛ` between two binders' taints. So to iterate the pass over
the fuel bound we compose a *scalar* summary instead: `comMaxTaint`, the join of
every binder's taint down the let-chain — the program's overall secrecy level.

A join (max) **is** monotone in the threaded env (lowering an env entry lowers
each `exprTaint`, hence the join), so `comMaxTaint` composes cleanly:
`rewriteCom`/`saturateCom` never raise the program's overall secrecy level. This
is the transitively-composable form of the egraph pass's declassification
invariant. -/

/-- The overall secrecy level of a `Com`: the join of every binder's taint down
the let-chain (threading the assignment by the program's own binder taints). -/
def comMaxTaint {Γ : Ctxt jasminDialect} {t : JasminTy}
    (T : Taint Γ) : Com jasminDialect Γ t → SecretLevel
  | .ret _ => .pub
  | .var e body => exprTaint T e ⊔ₛ comMaxTaint (T.cons (exprTaint T e)) body

/-- **`comMaxTaint` is monotone in the threaded assignment.** Lowering the env
lowers every `exprTaint` (`exprTaint_mono`) and the head/body joins (`join_mono`),
so the overall secrecy level only drops. -/
theorem comMaxTaint_mono {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ {T T' : Taint Γ} (_ : TaintLe T T') (c : Com jasminDialect Γ t),
      comMaxTaint T c ⊑ₛ comMaxTaint T' c
  | _, _, _, .ret _ => trivial
  | _, _, hT, .var e body =>
      SecretLevel.join_mono (exprTaint_mono hT e)
        (comMaxTaint_mono (TaintLe.cons (exprTaint_mono hT e) hT) body)

/-- **One pass never raises the program's overall secrecy level.**
`comMaxTaint T (rewriteCom c k) ⊑ₛ comMaxTaint T c`: the head binder's taint
drops (`rewriteExpr_taint_le`), and the body's overall level drops both because
the body is itself rewritten (induction) and because the body env is lowered by
the head drop (`comMaxTaint_mono`). -/
theorem rewriteCom_comMaxTaint_le {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (T : Taint Γ) (c : Com jasminDialect Γ t) (k : KEnv Γ),
      comMaxTaint T (rewriteCom c k) ⊑ₛ comMaxTaint T c
  | _, .ret _, _ => trivial
  | T, .var e body, k => by
      simp only [rewriteCom, comMaxTaint]
      refine SecretLevel.join_mono (rewriteExpr_taint_le T e k) ?_
      -- body: rewritten body under the (lowered) rewritten-head env ⊑ original
      -- body under the original-head env.  Compose the program-induction bound
      -- with the env-monotonicity bound.
      refine SecretLevel.leq_trans
        (rewriteCom_comMaxTaint_le (T.cons (exprTaint T (rewriteExpr e k))) body (extendK e k))
        (comMaxTaint_mono (TaintLe.cons (rewriteExpr_taint_le T e k) (TaintLe.refl _)) body)

/-- **The bounded engine never raises the program's overall secrecy level.**
`comMaxTaint T (saturateCom fuel c k) ⊑ₛ comMaxTaint T c`. By induction on fuel,
composing the per-pass bound (`rewriteCom_comMaxTaint_le`) via transitivity of
`⊑ₛ` — the scalar summary is transitively composable where the per-binder
`ComTaintLe` is not. The egraph analogue of `peepCom_wellTainted`: this pass's
composable declassification invariant. -/
theorem saturateCom_comMaxTaint_le {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (fuel : Nat) (T : Taint Γ) (c : Com jasminDialect Γ t) (k : KEnv Γ),
      comMaxTaint T (saturateCom fuel c k) ⊑ₛ comMaxTaint T c
  | 0, T, c, _ => SecretLevel.leq_refl _
  | n + 1, T, c, k => by
      simp only [saturateCom]
      -- `saturateCom (n+1) c k = saturateCom n (rewriteCom c k) k`; inner
      -- saturation does not raise `rewriteCom c k`'s level (IH), which itself
      -- does not raise `c`'s (`rewriteCom_comMaxTaint_le`); compose.
      exact SecretLevel.leq_trans
        (saturateCom_comMaxTaint_le n T (rewriteCom c k) k)
        (rewriteCom_comMaxTaint_le T c k)

/-! ## 9. Validation of the egraph declassification on the demo

The `demoMulZero` program from `Egraph.lean` (`x * 0` via an explicit
`regConst 0` binder) under a `sec`-input assignment: the engine rewrites the
`mul x c0` binder (args `x`, `c0`) to `and c0 c0`, dropping the secret `x` and
keeping only the public constant `c0` — a declassification of that
binder from `sec` to `pub`. `ComTaintLe` records this drop per-binder; the
overall secrecy level of the whole program drops from `sec` to `pub`. -/

/-- The taint assignment marking the single `[reg 32]` input `sec`. -/
def egDemoTaint : Taint [.reg 32] := .cons .sec .nil

/-- **One egraph pass declassifies the demo (per binder).** Every binder of
`rewriteCom demoMulZero` is `⊑ₛ` the original — concretely the `mul` binder
drops from `sec` (`= sec ⊔ pub`, the secret `x` joined with the public constant)
to `pub` (only the public constant `c0` survives). Via `rewriteCom_taint_mono`. -/
example : ComTaintLe egDemoTaint (rewriteCom demoMulZero demoK) demoMulZero :=
  rewriteCom_taint_mono egDemoTaint demoMulZero demoK

/-- The original program's overall secrecy level is `sec` (the `mul x c0` binder
joins the secret `x`). -/
example : comMaxTaint egDemoTaint demoMulZero = .sec := by decide

/-- After saturation the maximum taint is `pub`: the secret flows into no
surviving binder. -/
example : comMaxTaint egDemoTaint (saturateCom 4 demoMulZero demoK) = .pub := by
  decide

/-- **The bounded engine never raises the demo's overall secrecy level.** Here it
strictly declassifies `sec ↦ pub`. Via `saturateCom_comMaxTaint_le`. -/
example :
    comMaxTaint egDemoTaint (saturateCom 4 demoMulZero demoK)
      ⊑ₛ comMaxTaint egDemoTaint demoMulZero :=
  saturateCom_comMaxTaint_le 4 egDemoTaint demoMulZero demoK

end CatCrypt.Crypto.Optimizer.SecretType
