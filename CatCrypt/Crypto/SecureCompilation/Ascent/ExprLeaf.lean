/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-!
# The `corres_setExpr` value leaf — the arithmetic `RScalarSetExpr` fragment

The scalar-`SExpr` assignment leaf `RScalarSetExpr x e` for the **arithmetic**
source-clean fragment (`SVar` / `SLit` / `SAdd` / `SSub` / `SMul`), abstracting
the concrete 64-bit word expression to `ZMod 2^64`. This is what real field
kernels need — `feSub` is subtraction, `feAdd` addition, `feMul` multiplication,
all in this fragment.

The content splits into the two `Corres`/ParamTransfer halves (`Ascent.Corres`
module doc):

* **Value transfer (ParamTransfer core, `wEnc_evalBV_evalZMod`).** The word-tree
  representation change: `wEnc (SExpr.evalBV (envReader env) e) = evalZMod a e`,
  proved by recursion on the arithmetic expression using the `RelatedBinOp wEnc`
  `.comm` squares (`+`/`-`/`*`) for the nodes and the reader-agreement at the
  `SVar` leaves. Unconditional at the word level (no reduce side condition — the
  ambient ring is `ZMod 2^64`, matching `BitVec 64`).

* **Progress (`corres_setExpr`).** The Phase-0 `semScalar … = some _` obligation
  for `RScalarSetExpr`, which reduces to `semLowerSExpr env 0 e = some _`,
  discharged from the state relation via the proven fresh-temp success lemma
  `semLowerSExpr_ok'`.

## The temp-namespace subtlety (why `SRwordNT`, not the total `SRword`)

`semLowerSExpr` lowers `e` through a chain of fresh temporaries `tmpName k`, and
the resulting env — which the `RScalarSetExpr` arm carries into the post-state —
has those temp slots overwritten. The base `SRword` is *total* (it constrains
**every** name, temps included), so it is not preserved across a temp-adding
lowering such as a subtraction: the abstract post-state only updates `x`, while
the concrete env also scribbles `tmpName k`. The honest, true state relation for
this leaf is therefore `SRword` **restricted to non-temp names** (`SRwordNT`);
`srword_srwordNT` weakens the total relation into it, so every `SRword` context
supplies it for free. Non-temp names are exactly the source names a real kernel
reads and writes; the fresh-temp scribbles are invisible to it.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-! ## The arithmetic source-clean fragment and its `ZMod 2^64` evaluator -/

/-- The arithmetic sub-fragment of `srcClean`: variable/literal leaves plus the
    three ring operations (`+`/`-`/`*`). `SVar` leaves are non-temp source names
    and `SLit` literals are `< 2^64` (exactly the `srcClean` leaf conditions), so
    `IsArithClean e → srcClean e`. This is the value-transfer-clean fragment:
    every node has a registered `RelatedBinOp wEnc` square, so `evalBV` and the
    `ZMod`-level `evalZMod` agree; the bitwise / shift / high-multiply arms of
    `srcClean` are excluded (they are word-faithful but not `ZMod`-ring ops). -/
def IsArithClean : SExpr → Prop
  | .SVar x => ¬ isTmpName x
  | .SLit n => n < 2 ^ 64
  | .SAdd a b | .SSub a b | .SMul a b => IsArithClean a ∧ IsArithClean b
  | _ => False

/-- The arithmetic fragment is source-clean. -/
theorem isArithClean_srcClean : ∀ e, IsArithClean e → srcClean e := by
  intro e
  induction e with
  | SVar x => intro h; exact h
  | SLit n => intro h; exact h
  | SAdd a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | SSub a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | SMul a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | SAnd a b iha ihb => intro h; exact h.elim
  | SXor a b iha ihb => intro h; exact h.elim
  | SShl a b iha ihb => intro h; exact h.elim
  | SShr a b iha ihb => intro h; exact h.elim
  | SMulHiU a b iha ihb => intro h; exact h.elim
  | SLt a b iha ihb => intro h; exact h.elim
  | SAsr a b iha ihb => intro h; exact h.elim
  | SMulS a b iha ihb => intro h; exact h.elim
  | SMulHiS a b iha ihb => intro h; exact h.elim
  | SLimb v i => intro h; exact h.elim

/-- The abstract `ZMod 2^64` evaluator for the arithmetic fragment: the clean
    Lean spec the word expression abstracts to. Variables read the abstract
    valuation, literals cast, and the three ring nodes map to the `ZMod` ring
    operations. Non-arithmetic arms are `0` (they are outside `IsArithClean`). -/
def evalZMod (φ : String → ZMod (2 ^ 64)) : SExpr → ZMod (2 ^ 64)
  | .SVar x => φ x
  | .SLit n => (n : ZMod (2 ^ 64))
  | .SAdd a b => evalZMod φ a + evalZMod φ b
  | .SSub a b => evalZMod φ a - evalZMod φ b
  | .SMul a b => evalZMod φ a * evalZMod φ b
  | _ => 0

/-! ## The value transfer (ParamTransfer core) -/

/-- **The word-tree value transfer.** Under a reader that agrees with the abstract
    valuation on every non-temp name (`wEnc (envReader env x) = a x`), the
    `wEnc`-encoding of the concrete word evaluation of a `IsArithClean` expression
    equals its abstract `ZMod 2^64` evaluation. The recursion seats each `SVar`
    leaf at its reader-agreement and glues the `+`/`-`/`*` nodes with the
    registered `RelatedBinOp wEnc` squares (`wEncAdd`/`wEncSub`/`wEncMul`) — this
    is exactly the ParamTransfer word-op-tree transfer content. -/
theorem wEnc_evalBV_evalZMod (β : String → BitVec 64) (a : String → ZMod (2 ^ 64))
    (hread : ∀ x, ¬ isTmpName x → wEnc (β x) = a x) :
    ∀ e, IsArithClean e → wEnc (SExpr.evalBV β e) = evalZMod a e := by
  intro e
  induction e with
  | SVar x => intro h; exact hread x h
  | SLit n =>
      intro _
      simp only [SExpr.evalBV, evalZMod, wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]
  | SAdd a b iha ihb =>
      intro h
      rw [SExpr.evalBV, evalZMod, wEncAdd.comm, iha h.1, ihb h.2]
  | SSub a b iha ihb =>
      intro h
      rw [SExpr.evalBV, evalZMod, wEncSub.comm, iha h.1, ihb h.2]
  | SMul a b iha ihb =>
      intro h
      rw [SExpr.evalBV, evalZMod, wEncMul.comm, iha h.1, ihb h.2]
  | SAnd a b iha ihb => intro h; exact h.elim
  | SXor a b iha ihb => intro h; exact h.elim
  | SShl a b iha ihb => intro h; exact h.elim
  | SShr a b iha ihb => intro h; exact h.elim
  | SMulHiU a b iha ihb => intro h; exact h.elim
  | SLt a b iha ihb => intro h; exact h.elim
  | SAsr a b iha ihb => intro h; exact h.elim
  | SMulS a b iha ihb => intro h; exact h.elim
  | SMulHiS a b iha ihb => intro h; exact h.elim
  | SLimb v i => intro h; exact h.elim

/-- Every `SExpr` has all its `SVar` leaves in the trivial bound set. -/
theorem varsBoundIn_true : ∀ e, varsBoundIn (fun _ => True) e := by
  intro e
  induction e with
  | SVar x => trivial
  | SLit n => trivial
  | SAdd a b iha ihb => exact ⟨iha, ihb⟩
  | SSub a b iha ihb => exact ⟨iha, ihb⟩
  | SMul a b iha ihb => exact ⟨iha, ihb⟩
  | SAnd a b iha ihb => exact ⟨iha, ihb⟩
  | SXor a b iha ihb => exact ⟨iha, ihb⟩
  | SShl a b iha ihb => exact ⟨iha, ihb⟩
  | SShr a b iha ihb => exact ⟨iha, ihb⟩
  | SMulHiU a b iha ihb => exact ⟨iha, ihb⟩
  | SLt a b iha ihb => trivial
  | SAsr a b iha ihb => trivial
  | SMulS a b iha ihb => trivial
  | SMulHiS a b iha ihb => trivial
  | SLimb v i => trivial

/-! ## The non-temp-restricted state relation and the value leaf -/

/-- The word-phase state relation restricted to non-temp source names: every
    non-temp name holds a `.sword 64` whose ParamTransfer encoding `wEnc` is the
    abstract value. This is the honest relation for `RScalarSetExpr` — the lowering
    scribbles the fresh-temp namespace, which a source kernel never observes. -/
def SRwordNT (env : SEnvScalar) (a : String → ZMod (2 ^ 64)) : Prop :=
  ∀ x, ¬ isTmpName x → ∃ w : BitVec 64, env x = some ⟨.sword 64, w⟩ ∧ wEnc w = a x

/-- The total word relation weakens into its non-temp restriction — so every
    `SRword` context (from `Ascent.Corres`) supplies `SRwordNT` for free. -/
theorem srword_srwordNT {env : SEnvScalar} {a : String → ZMod (2 ^ 64)}
    (h : SRword env a) : SRwordNT env a :=
  fun x _ => h x

/-- `corres_setExpr` — the arithmetic `RScalarSetExpr x e` value leaf. From a
    concrete env `SRwordNT`-related to abstract `a`, the real `semScalar`
    `RScalarSetExpr` arm makes progress (`= some _`, discharged via
    `semLowerSExpr_ok'`) to an env related to the abstract state that sets `x` to
    `evalZMod a e` (the clean `ZMod 2^64` value from the ParamTransfer transfer)
    and leaves every other source name untouched. -/
theorem corres_setExpr (x : String) (e : SExpr) (he : IsArithClean e) :
    Corres SRwordNT (fun _ => True)
      (fun a s => if s = x then evalZMod a e else a s)
      (.RScalarSetExpr x e) := by
  intro env a hSR _
  -- A witnessing rust state whose scalar store reads back the env words; makes
  -- `EnvBoundOn` hold so the proven fresh-temp success lemma applies.
  set rs : RustState := ⟨fun _ => none, fun y => (envReader env y).toNat⟩ with hrs
  have hEB : EnvBoundOn rs env (fun _ => True) := by
    intro y _ hnt
    obtain ⟨w, hw, _⟩ := hSR y hnt
    have hr : envReader env y = w := by simp only [envReader, hw]
    have hround : BitVec.ofNat 64 w.toNat = w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt w.isLt
    show env y = some ⟨.sword 64, BitVec.ofNat 64 ((envReader env y).toNat)⟩
    rw [hr, hround]; exact hw
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ :=
    semLowerSExpr_ok' rs (fun _ => True) e env 0 hEB (varsBoundIn_true e)
      (isArithClean_srcClean e he)
  -- the value stored at `x`
  have hval : wEnc (SExpr.evalBV (envReader env) e) = evalZMod a e := by
    apply wEnc_evalBV_evalZMod (envReader env) a _ e he
    intro y hnt
    obtain ⟨w, hw, hwe⟩ := hSR y hnt
    have hr : envReader env y = w := by simp only [envReader, hw]
    rw [hr]; exact hwe
  refine ⟨env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e), ?_, ?_⟩
  · simp only [semScalar, hsem]
  · intro y hnt
    by_cases hyx : y = x
    · refine ⟨SExpr.evalBV (envReader env) e, ?_, ?_⟩
      · simp only [SEnvScalar.upd, if_pos hyx]
      · show wEnc (SExpr.evalBV (envReader env) e) = if y = x then evalZMod a e else a y
        rw [if_pos hyx]; exact hval
    · obtain ⟨w, hw, hwe⟩ := hSR y hnt
      refine ⟨w, ?_, ?_⟩
      · simp only [SEnvScalar.upd, if_neg hyx]
        rw [hotb y (Or.inl hnt)]; exact hw
      · show wEnc w = if y = x then evalZMod a e else a y
        rw [if_neg hyx]; exact hwe

end CatCrypt.Crypto.SecureCompilation.Ascent
