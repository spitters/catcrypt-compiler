/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Rewrite.Egraph
import CatCrypt.Crypto.Optimizer.Rewrite.AbsentRewrites

/-!
# Verified double-negation elimination pass for `Com` (`neg(neg x) ↦ x`)

A denotation-preserving `Com → Com` optimizer pass over the typed
VIR `jasminDialect`, complementary to the bounded equality-saturation engine in
`Egraph.lean` and the local syntactic peephole in `Peephole.lean`. It eliminates
**double negation** at the expression level: `neg (neg x) ↦ x`.

## How negation is represented in `jasminDialect`

The Jasmin dialect (`SecureCompilation/VIR/JasminDialect.lean`) has **no
first-class unary `neg`/`not` op**. Its `JasminBinOp` alphabet is
`add/sub/mul/and/or/xor/shl/shr/andn`, and `JasminOp` adds `regConst`,
shifts, casts, carry words, etc. — but no unary negate.

Two's-complement negation is therefore the binary idiom `neg x = 0 - x`, i.e.
`binE .sub z x` where `z` is a `regConst _ 0` binder (the materialised zero).
Concretely, in the A-normal `Com` let-chain a doubled negation appears as

    let z  = regConst w 0       -- the zero constant
    let n1 = sub z x            -- n1 = 0 - x = -x
    let n2 = sub z n1           -- n2 = 0 - n1 = -(-x) = x

So the rewrite target is the inner sub-form **`0 - (0 - x) = x`** — exactly the
`BitVec`-level identity `AbsentRewrites.neg_neg_rewrite : - - x = x` composed
with `BitVec.zero_sub : 0 - x = -x`.

## The analysis: a negation-source environment

Detecting `n2 = sub z n1` as a *double* negation requires knowing two facts
about its operands that are not syntactically local to the `sub z n1`
expression:

* `z` was bound by `regConst _ 0` (so `sub z _` is a negation, not a general
  subtraction);
* `n1` was *itself* a negation `sub z' x` of some in-scope `x`.

We track both with a per-position environment `NEnv` (same shape as the
context `Γ`, like `Egraph.KEnv`): each binding carries an `NEntry`, recording
whether that binder is the zero constant (`.zeroC`) or the negation of an
in-scope source variable (`.negOf y`). The environment is threaded down the
let-chain (`extendN`), weakening every source variable under the new binder.

When the analysis reaches `sub z n1` with `z` a known zero and `n1 = .negOf y`,
the whole expression denotes `0 - (-(y)) = y`, so it is rewritten to the
identity form `binE .or y y` (which denotes `y ||| y = y`, cost 1, reuses the
already-in-scope `y` — no De Bruijn renumbering, exactly the identity-collapse
discipline of `Egraph.rewriteBin`).

## Preservation theorems

* `negElimExpr_denote` : per-`Expr` denotation equality under a consistent
  environment (real `BitVec` algebra: `0 - (0 - y) = y`, via
  `neg_neg_rewrite`).
* `negElimCom_denote`  : `(negElimCom c V₀).denote V = c.denote V`, by induction
  over the `Com` let-chain. **Not `rfl`.**
* `negElimCom_ctSafe`  : CT preservation (the dialect is branch-free).
* `negElimCom_cost_le` : cost-non-increasing.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.NegElimPass

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.AbsentRewrites

/-! ## 1. The negation-source environment

`NEnv Γ` carries, for every binding in `Γ`, an `NEntry Γ` describing what that
binder is:

* `.zeroC`  — the binder was `regConst _ 0` (the materialised zero constant);
* `.negOf y` — the binder is `0 - y` (a negation) for some in-scope source `y`;
* `.other`  — anything else (no information).

It mirrors `Egraph.KEnv`, but its `.negOf` payload is a *variable* of `Γ`, so it
must be weakened (`.there`) as the env descends under a new binder. -/

/-- What a binder is, w.r.t. negation analysis. Source variables are in `Γ`. -/
inductive NEntry (Γ : Ctxt jasminDialect) where
  /-- The binder is the zero constant `regConst _ 0`. -/
  | zeroC
  /-- The binder is `0 - y` (a negation) of the in-scope source `y : reg w`. -/
  | negOf {w : Nat} (y : Ctxt.Var Γ (.reg w))
  /-- No negation information. -/
  | other

/-- Weaken an `NEntry` under a new binder of type `t` (push every source var
through `.there`). -/
def NEntry.weaken {Γ : Ctxt jasminDialect} {t : JasminTy} :
    NEntry Γ → NEntry (t :: Γ)
  | .zeroC    => .zeroC
  | .negOf y  => .negOf y.there
  | .other    => .other

/-- A negation-source environment: one `NEntry` per binding in `Γ`. -/
inductive NEnv : Ctxt jasminDialect → Type where
  | nil : NEnv []
  | cons {t : JasminTy} {Γ : Ctxt jasminDialect} :
      NEntry (t :: Γ) → NEnv Γ → NEnv (t :: Γ)

/-- Look up the `NEntry` for a variable (entries already reference the full
current context, so no weakening is needed at lookup time). -/
def NEnv.lookup {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Ctxt.Var Γ t → NEnv Γ → NEntry Γ
  | .here,    .cons o _ => o
  | .there v, .cons _ k => (NEnv.lookup v k).weaken

/-! ## 2. Consistency of the environment with a valuation

`NEnv k` is consistent with valuation `V` when every claim it makes holds:

* a `.zeroC` binder really evaluates to `0`;
* a `.negOf y` binder really evaluates to `-(y.lookup V)`.

The rewrite is only sound under such a valuation; the pass maintains consistency
as it descends (`extendN_consistent`). -/

/-- The semantic claim made by an `NEntry` about a value `x` under `V`. -/
def NEntry.holds {Γ : Ctxt jasminDialect} {w : Nat}
    (V : Ctxt.Valuation Γ) (x : BitVec w) : NEntry Γ → Prop
  | .zeroC                => x = (0 : BitVec w)
  | @NEntry.negOf _ w' y  => ∃ h : w' = w, x = - (h ▸ y.lookup V)
  | .other                => True

/-- `NEnv k` is consistent with valuation `V`. -/
def NEnv.Consistent {Γ : Ctxt jasminDialect} (k : NEnv Γ) (V : Ctxt.Valuation Γ) :
    Prop :=
  ∀ {w : Nat} (v : Ctxt.Var Γ (.reg w)),
    (NEnv.lookup v k).holds V (v.lookup V)

/-! ## 3. Extracting an `NEntry` for a new binder

Given the expression a binder is bound to (and the env in scope at that point),
compute the `NEntry` it should carry. A `regConst _ 0` is `.zeroC`; a
`sub z x` whose first operand `z` is a known zero is `.negOf x`; everything
else is `.other`. -/

/-- The first/second register operands of a binary `regArith` expression. -/
def binArgs {Γ : Ctxt jasminDialect} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var Γ ty) [JasminTy.reg w, JasminTy.reg w]) :
    Ctxt.Var Γ (.reg w) × Ctxt.Var Γ (.reg w) :=
  (args.head, args.tail.head)

/-- Compute the `NEntry` of a freshly-bound expression `e`, given the env `k`
in scope (used to test whether `e`'s first operand is a known zero). The
resulting entry references the *outer* context `Γ`; the caller weakens it. -/
def exprEntry {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : NEnv Γ) : NEntry Γ :=
  match e with
  | ⟨.regConst _ 0, _, _⟩ => .zeroC
  | ⟨.regArith .sub w, _, args⟩ =>
      let a : Ctxt.Var Γ (.reg w) := args.head
      let b : Ctxt.Var Γ (.reg w) := args.tail.head
      match NEnv.lookup a k with
      | .zeroC => .negOf b      -- sub 0 b = -b
      | _      => .other
  | _ => .other

/-! ## 4. The `Expr`-level rewrite

Rewrite `sub z n1` to `or y y` when `z` is a known zero and `n1 = -y` (a
negation of in-scope `y`): then `sub z n1 = 0 - (-y) = y = y ||| y`. -/

/-- Rewrite a binary `regArith` whose pattern is a double negation. Returns
`none` if no pattern matches. -/
def negElimBin {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) (k : NEnv Γ) :
    Option (Expr jasminDialect Γ (.reg w)) :=
  match bop with
  | .sub =>
      match NEnv.lookup a k, NEnv.lookup b k with
      | .zeroC, .negOf (w := w') y =>
          -- a = 0, b = -y : sub a b = 0 - (-y) = y.  Need y at width w.
          if h : w' = w then some (binE .or (h ▸ y) (h ▸ y)) else none
      | _, _ => none
  | _ => none

/-! ### Soundness of the underlying `BitVec` identity -/

/-- `0 - (0 - y) = y` on `BitVec w`: the double-negation identity. Two's
complement `neg x = 0 - x` (`BitVec.zero_sub`), so this is `- - y = y`, i.e.
`AbsentRewrites.neg_neg_rewrite`. -/
theorem zsub_zsub {w : Nat} (y : BitVec w) :
    (0 : BitVec w) - ((0 : BitVec w) - y) = y := by
  rw [show (0 : BitVec w) - y = -y from BitVec.zero_sub y,
      show (0 : BitVec w) - -y = - -y from BitVec.zero_sub _]
  exact neg_neg_rewrite y

/-- The identity-collapse form actually emitted, in the shape that arises after
substituting the `.negOf`/`.zeroC` semantic claims: `0 - (-y) = y ||| y`. Two's
complement `neg x = 0 - x` (`BitVec.zero_sub`), so the LHS is `- - y`, collapsed
by `AbsentRewrites.neg_neg_rewrite` and re-expressed via `BitVec.or_self`. -/
theorem zsub_neg_or {w : Nat} (y : BitVec w) :
    (0 : BitVec w) - (-y) = y ||| y := by
  rw [show (0 : BitVec w) - (-y) = - -y from BitVec.zero_sub _, neg_neg_rewrite,
      BitVec.or_self]

/-- **Soundness of `negElimBin`.** Under a consistent env, any expression
`negElimBin` produces denotes the same value as the original `binE bop a b`.
A `BitVec`-algebra proof (the `0 - (0 - y) = y` double-negation
identity via `neg_neg_rewrite`), **not** `rfl`. -/
theorem negElimBin_sound {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) (k : NEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : NEnv.Consistent k V)
    (e' : Expr jasminDialect Γ (.reg w))
    (he : negElimBin bop a b k = some e') :
    e'.denote V = (binE bop a b).denote V := by
  unfold negElimBin at he
  split at he
  case h_2 => simp at he
  case h_1 =>
    split at he
    case h_1 _ _ w' y hla hlb =>
      have ha := hk a
      have hb := hk b
      rw [hla] at ha; rw [hlb] at hb
      simp only [NEntry.holds] at ha hb
      obtain ⟨hwz, hbz⟩ := hb
      by_cases hw : w' = w
      · subst hw
        rw [dif_pos rfl, Option.some.injEq] at he
        subst he
        rw [binE_denote, binE_denote, JasminBinOp.apply, JasminBinOp.apply,
          ha, hbz, zsub_neg_or]
      · rw [dif_neg hw] at he
        simp at he
    case h_2 => simp at he

/-- Apply the neg-elim rewrite at one expression. Identity unless the expression
is a binary `regArith` over `reg w` matching the double-negation pattern. -/
def negElimExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : NEnv Γ) : Expr jasminDialect Γ t :=
  match e with
  | ⟨.regArith bop w, hop, args⟩ =>
      let a : Ctxt.Var Γ (.reg w) := args.head
      let b : Ctxt.Var Γ (.reg w) := args.tail.head
      match negElimBin bop a b k with
      | some e' => hop ▸ e'
      | none    => ⟨.regArith bop w, hop, args⟩
  | e => e

/-- **Denotation preservation for `negElimExpr`.** Under a consistent env,
rewriting one expression preserves its denotation. -/
theorem negElimExpr_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : NEnv Γ) (V : Ctxt.Valuation Γ)
    (hk : NEnv.Consistent k V) :
    (negElimExpr e k).denote V = e.denote V := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [negElimExpr, HVector.head, HVector.tail]
        rcases hr : negElimBin bop a b k with _ | e'
        · simp
        · rw [negElimBin_sound bop a b k V hk e' hr]; rfl
  | stackLoad w n => simp [negElimExpr]
  | stackStore w n => simp [negElimExpr]
  | castW w w' => simp [negElimExpr]
  | extCall nm a r => simp [negElimExpr]
  | regConst w n => simp [negElimExpr]
  | vpackZMM bop => simp [negElimExpr]
  | vpackZMMd bop => simp [negElimExpr]
  | vprordZMM n => simp [negElimExpr]
  | vpslldq n => simp [negElimExpr]
  | vpsrldq n => simp [negElimExpr]
  | vsimd op => simp [negElimExpr]
  | vymm op => simp [negElimExpr]
  | mulhi w => simp [negElimExpr]
  | addCarryLo w => simp [negElimExpr]
  | addCarryHi w => simp [negElimExpr]
  | rorImm w n => simp [negElimExpr]
  | shrImm w n => simp [negElimExpr]
  | sarImm w n => simp [negElimExpr]
  | shlImm w n => simp [negElimExpr]
  | select w => simp [negElimExpr]
  | callN name argTys retTys => simp [negElimExpr]

/-! ## 5. Cost non-increase of `negElimExpr`

`sub` (cost 1) is replaced by `or` (cost 1), so cost is preserved. We state the
`≤` form for uniformity with the egraph / peephole passes. -/

/-- `negElimBin` never increases op cost. -/
theorem negElimBin_cost_le {Γ : Ctxt jasminDialect} {w : Nat}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) (k : NEnv Γ)
    (e' : Expr jasminDialect Γ (.reg w))
    (he : negElimBin bop a b k = some e') :
    opCost e'.op ≤ opCost (JasminOp.regArith bop w) := by
  unfold negElimBin at he
  split at he
  case h_2 => simp at he
  case h_1 =>
    split at he
    case h_1 _ _ w' y hla hlb =>
      by_cases hw : w' = w
      · subst hw
        rw [dif_pos rfl, Option.some.injEq] at he
        subst he
        simp [opCost, binE]
      · rw [dif_neg hw] at he
        simp at he
    case h_2 => simp at he

/-- `negElimExpr` never increases op cost. -/
theorem negElimExpr_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : NEnv Γ) :
    opCost (negElimExpr e k).op ≤ opCost e.op := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w =>
      subst hop
      match args, (rfl : args = args) with
      | .cons a (.cons b .nil), _ =>
        simp only [negElimExpr, HVector.head, HVector.tail]
        rcases hr : negElimBin bop a b k with _ | e'
        · simp
        · exact negElimBin_cost_le bop a b k e' hr
  | stackLoad w n => simp [negElimExpr]
  | stackStore w n => simp [negElimExpr]
  | castW w w' => simp [negElimExpr]
  | extCall nm a r => simp [negElimExpr]
  | regConst w n => simp [negElimExpr]
  | vpackZMM bop => simp [negElimExpr]
  | vpackZMMd bop => simp [negElimExpr]
  | vprordZMM n => simp [negElimExpr]
  | vpslldq n => simp [negElimExpr]
  | vpsrldq n => simp [negElimExpr]
  | vsimd op => simp [negElimExpr]
  | vymm op => simp [negElimExpr]
  | mulhi w => simp [negElimExpr]
  | addCarryLo w => simp [negElimExpr]
  | addCarryHi w => simp [negElimExpr]
  | rorImm w n => simp [negElimExpr]
  | shrImm w n => simp [negElimExpr]
  | sarImm w n => simp [negElimExpr]
  | shlImm w n => simp [negElimExpr]
  | select w => simp [negElimExpr]
  | callN name argTys retTys => simp [negElimExpr]

/-! ## 6. The `Com`-level pass

`negElimCom` rewrites every let-bound expression with `negElimExpr`, threading
the negation-source env, and descends into the body. -/

/-- Extend the env with the entry of a freshly-bound expression, weakened under
the new binder (mirroring the binder `Com.var e body` introduces). -/
def extendN {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : NEnv Γ) : NEnv (t :: Γ) :=
  NEnv.cons (exprEntry e k).weaken k

/-- One neg-elim pass over a `Com`, threading the negation-source env. -/
def negElimCom {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → NEnv Γ → Com jasminDialect Γ t
  | .ret v, _ => .ret v
  | .var e body, k => .var (negElimExpr e k) (negElimCom body (extendN e k))

/-! ## 7. Consistency preservation when descending under a binder -/

/-- The semantic content of `exprEntry`: under a consistent env, the entry
`exprEntry e k` (read in the *outer* context, applied to `e.denote V`) holds. -/
theorem exprEntry_holds {Γ : Ctxt jasminDialect} {w : Nat}
    (e : Expr jasminDialect Γ (.reg w)) (k : NEnv Γ) (V : Ctxt.Valuation Γ)
    (hk : NEnv.Consistent k V) :
    (exprEntry e k).holds V (e.denote V) := by
  obtain ⟨op, hop, args⟩ := e
  cases op with
  | regArith bop w' =>
      simp only [DialectSignature.ret] at hop
      injection hop with hw; subst hw
      cases bop with
      | sub =>
          -- the only interesting arm
          match args, (rfl : args = args) with
          | .cons a (.cons b .nil), _ =>
            show (exprEntry (binE JasminBinOp.sub a b) k).holds V _
            have ha := hk a
            rcases hla : NEnv.lookup a k with _ | y | _
            · -- a is a known zero: entry = negOf b
              have hee : exprEntry (binE JasminBinOp.sub a b) k = NEntry.negOf b := by
                show (match NEnv.lookup a k with | .zeroC => NEntry.negOf b | _ => .other)
                  = NEntry.negOf b
                rw [hla]
              rw [hee, NEntry.holds]
              rw [hla] at ha
              simp only [NEntry.holds] at ha
              refine ⟨rfl, ?_⟩
              show (binE JasminBinOp.sub a b).denote V = _
              rw [binE_denote, JasminBinOp.apply, ha]
              exact BitVec.zero_sub _
            · have hee : exprEntry (binE JasminBinOp.sub a b) k = NEntry.other := by
                show (match NEnv.lookup a k with | .zeroC => NEntry.negOf b | _ => .other)
                  = NEntry.other
                rw [hla]
              rw [hee]; trivial
            · have hee : exprEntry (binE JasminBinOp.sub a b) k = NEntry.other := by
                show (match NEnv.lookup a k with | .zeroC => NEntry.negOf b | _ => .other)
                  = NEntry.other
                rw [hla]
              rw [hee]; trivial
      | add => exact True.intro
      | mul => exact True.intro
      | and => exact True.intro
      | or => exact True.intro
      | xor => exact True.intro
      | shl => exact True.intro
      | shr => exact True.intro
      | andn => exact True.intro
  | regConst w' n =>
      simp only [DialectSignature.ret] at hop
      injection hop with hw; subst hw
      cases n with
      | zero => show (NEntry.zeroC).holds V _; simp only [NEntry.holds]; rfl
      | succ m => exact True.intro
  | stackLoad w n => exact True.intro
  | stackStore w n => exact True.intro
  | castW w w' => exact True.intro
  | extCall nm a r => exact True.intro
  | vpackZMM bop => exact True.intro
  | vpackZMMd bop => exact True.intro
  | vprordZMM n => exact True.intro
  | vpslldq n => exact True.intro
  | vpsrldq n => exact True.intro
  | vsimd op => exact True.intro
  | vymm op => exact True.intro
  | mulhi w => exact True.intro
  | addCarryLo w => exact True.intro
  | addCarryHi w => exact True.intro
  | rorImm w n => exact True.intro
  | shrImm w n => exact True.intro
  | sarImm w n => exact True.intro
  | shlImm w n => exact True.intro
  | select w => exact True.intro
  | callN name argTys retTys => exact True.intro

/-- `NEntry.weaken` preserves `holds` under the extended valuation: the source
variable, weakened by `.there`, looks up the same value. -/
theorem NEntry_weaken_holds {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
    (en : NEntry Γ) (V : Ctxt.Valuation Γ) (x : BitVec w) (vnew : ⟦s⟧)
    (h : en.holds V x) :
    en.weaken.holds (V.extend vnew) x := by
  cases en with
  | zeroC => simpa [NEntry.weaken, NEntry.holds] using h
  | negOf y =>
      simp only [NEntry.holds] at h
      obtain ⟨hw, hx⟩ := h
      refine ⟨hw, ?_⟩
      have hlk : (y.there : Ctxt.Var (s :: Γ) _).lookup (V.extend vnew) = y.lookup V := rfl
      show x = - (hw ▸ (y.there : Ctxt.Var (s :: Γ) _).lookup (V.extend vnew))
      rw [hlk]
      exact hx
  | other => trivial

/-- **Consistency preserved when descending under a binder.** If `k` is
consistent with `V`, then `extendN e k` is consistent with the valuation
extended by `(negElimExpr e k).denote V` — which equals `e.denote V`. -/
theorem extendN_consistent {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : NEnv Γ) (V : Ctxt.Valuation Γ)
    (hk : NEnv.Consistent k V) :
    NEnv.Consistent (extendN e k) (V.extend (e.denote V)) := by
  intro w v
  cases v with
  | here =>
      -- here forces the binder type `t = reg w`; the head entry is
      -- `(exprEntry e k).weaken`, and the new value is `e.denote V`
      simp only [extendN, NEnv.lookup, Ctxt.Valuation.extend]
      apply NEntry_weaken_holds
      exact exprEntry_holds e k V hk
  | there v' =>
      simp only [extendN, NEnv.lookup, Ctxt.Valuation.extend]
      exact NEntry_weaken_holds _ V _ _ (hk v')

/-! ## 8. Denotation preservation for the pass -/

/-- **Denotation preservation for the neg-elim pass.** `negElimCom c k` denotes
the same function as `c`, for any env `k` consistent with the valuation. By
induction over the `Com` let-chain — **not** `rfl`. -/
theorem negElimCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (k : NEnv Γ) (V : Ctxt.Valuation Γ),
      NEnv.Consistent k V → (negElimCom c k).denote V = c.denote V
  | .ret v, _, _, _ => rfl
  | .var e body, k, V, hk => by
      simp only [negElimCom, Com.denote]
      rw [negElimExpr_denote e k V hk]
      exact negElimCom_denote body (extendN e k) (V.extend (e.denote V))
        (extendN_consistent e k V hk)

/-! ## 9. CT preservation -/

/-- **CT preservation for the neg-elim pass.** The dialect is branch-free, so
both the input and the rewritten `Com` are CT-safe. -/
theorem negElimCom_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (k : NEnv Γ) :
    ctSafeComJ (negElimCom c k) = ctSafeComJ c := by
  rw [ctSafeComJ_true (negElimCom c k), ctSafeComJ_true c]

/-! ## 10. Cost non-increase -/

/-- **The neg-elim pass is cost-non-increasing.** -/
theorem negElimCom_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (k : NEnv Γ),
      comCost (negElimCom c k) ≤ comCost c
  | .ret _, _ => Nat.le_refl _
  | .var e body, k => by
      simp only [negElimCom, comCost]
      have h1 : opCost (negElimExpr e k).op ≤ opCost e.op := negElimExpr_cost_le e k
      have h2 : comCost (negElimCom body (extendN e k)) ≤ comCost body :=
        negElimCom_cost_le body (extendN e k)
      omega

/-! ## 11. Self-contained validation

A `Com jasminDialect [reg 32] (reg 32)` exercising the pass, encoding the
two's-complement double-negation `x ↦ -(-x)`:

    let z  = regConst 32 0     -- the zero constant
    let n1 = sub z x           -- n1 = -x
    let n2 = sub z n1          -- n2 = -(-x) = x
    ret n2

The pass rewrites the *outer* `sub z n1` site to the identity form `or x x`,
because `z` is a known zero and `n1` is recorded as the negation of `x`. We
check the denotation is preserved (both map `x` to `x`). -/

/-- The doubled-negation demo: `x ↦ -(-x)`, in A-normal form. Context starts
`[reg 32]` (just `x`, at `.here`). -/
def demoDoubleNeg : Com jasminDialect [.reg 32] (.reg 32) :=
  -- z = regConst 32 0.  After this binder, context is [z, x] = [reg32, reg32].
  .var ⟨.regConst 32 0, rfl, .nil⟩
    -- n1 = sub z x.  z = .here, x = .there .here.  Context becomes [n1, z, x].
    (.var (binE .sub .here (.there .here))
      -- n2 = sub z n1.  z = .there .here, n1 = .here.  Context becomes [n2,n1,z,x].
      (.var (binE .sub (.there .here) .here)
        (.ret .here)))

/-- The all-`.other` starting environment for a context `Γ`: no binder carries
any negation information. This is the correct env to begin a top-level pass with
(the free inputs are unknown). -/
def NEnv.allOther : (Γ : Ctxt jasminDialect) → NEnv Γ
  | [] => .nil
  | _ :: Γ => .cons .other (NEnv.allOther Γ)

/-- Looking up any variable in `allOther` yields `.other`. -/
theorem NEnv.lookup_allOther {Γ : Ctxt jasminDialect} {t : JasminTy}
    (v : Ctxt.Var Γ t) : NEnv.lookup v (NEnv.allOther Γ) = .other := by
  induction v with
  | here => rfl
  | there v' ih =>
      simp only [NEnv.allOther, NEnv.lookup, ih, NEntry.weaken]

/-- The all-`.other` environment is consistent with any valuation. -/
theorem NEnv.allOther_consistent {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) : NEnv.Consistent (NEnv.allOther Γ) V := by
  intro w v
  rw [NEnv.lookup_allOther]
  trivial

/-- The starting environment for the demo: the single free input `x` carries no
negation information. -/
def demoEnv : NEnv [.reg 32] := NEnv.allOther [.reg 32]

/-- **Denotation preserved on the demo.** The rewritten program denotes the same
function as the input — both map `x` to `x`. Via `negElimCom_denote`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (negElimCom demoDoubleNeg demoEnv).denote V = demoDoubleNeg.denote V :=
  negElimCom_denote demoDoubleNeg demoEnv V (NEnv.allOther_consistent V)

/-- Concretely, on `x = 42`, the source denotes `42` (`-(-42) = 42`). -/
example : demoDoubleNeg.denote (.cons (42 : BitVec 32) .nil) = (42 : BitVec 32) := by
  rfl

/-- And the rewritten program denotes the same on `x = 42`. -/
example :
    (negElimCom demoDoubleNeg demoEnv).denote (.cons (42 : BitVec 32) .nil)
      = (42 : BitVec 32) := by
  rfl

/-- **The pass rewrites the outer `sub` site to an `or` identity form.** The
recorded negation source of `n1` is `x` (at De Bruijn depth 2 in context
`[n1, z, x]`), so the outer `sub z n1` becomes `or x x`. -/
example :
    negElimCom demoDoubleNeg demoEnv =
      .var ⟨.regConst 32 0, rfl, .nil⟩
        (.var (binE .sub .here (.there .here))
          (.var (binE .or (.there (.there .here)) (.there (.there .here)))
            (.ret .here))) := by
  rfl

/-- **Cost non-increasing on the demo.** -/
example : comCost (negElimCom demoDoubleNeg demoEnv) ≤ comCost demoDoubleNeg :=
  negElimCom_cost_le demoDoubleNeg demoEnv

/-- **CT preserved on the demo.** -/
example : ctSafeComJ (negElimCom demoDoubleNeg demoEnv) = ctSafeComJ demoDoubleNeg :=
  negElimCom_ctSafe demoDoubleNeg demoEnv

end CatCrypt.Crypto.Optimizer.Rewrite.NegElimPass
