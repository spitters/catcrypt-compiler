/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

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

@[expose] public section

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

/-- `RScalarSet name n` over the non-temp relation `SRwordNT` — the literal leaf in
    the `SRwordNT`-based expression ascent (so a straight-line kernel that mixes
    literal sets and `RScalarSetExpr` terminals lifts uniformly). The `corres_setScalar`
    twin, restricted to non-temp names. -/
theorem corres_setScalar_NT (name : String) (n : Nat) :
    Corres SRwordNT (fun _ => True)
      (fun a s => if s = name then (n : ZMod (2 ^ 64)) else a s)
      (.RScalarSet name n) := by
  intro env a hSR _
  refine ⟨env.upd name (t := .sword 64) (BitVec.ofNat 64 n), rfl, ?_⟩
  intro x hnt
  by_cases hx : x = name
  · subst hx
    exact ⟨BitVec.ofNat 64 n, by simp [SEnvScalar.upd],
      by simp [wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]⟩
  · obtain ⟨w, hw, hwn⟩ := hSR x hnt
    exact ⟨w, by simp [SEnvScalar.upd, hx, hw], by simp [hx, hwn]⟩

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

/-! ## The bitwise value leaf — keeping the spec in the `BitVec 64` word algebra

The arithmetic leaf `corres_setExpr` abstracts words to `ZMod 2^64` through `wEnc`,
because `+`/`-`/`*` are `ZMod`-ring operations. The bitwise operations `^^^`/`&&&`
/`<<<`/`>>>` are **not** ring operations of `ZMod 2^64`, so there is no `wEnc`
square for them; the honest clean spec keeps the value in the `BitVec 64` word
algebra itself (`SExpr.evalBV`). The abstraction is the identity — the clean spec
IS the word computation — so the value transfer is definitional (no ring square),
unlike the arithmetic leaf's `wEnc_evalBV_evalZMod`. This is the coverable fragment
of SHA `Maj`/`Ch` (`&&&`/`^^^`) and all of Keccak `θ`/`ρ`/`χ` (`^^^`/`&&&`/rotate).

Width note: this is width **64** (covers Keccak / SHA-512 / any 64-bit bitwise
kernel). A width-parametric variant (32-bit, for ChaCha / SHA-256) is a separate
documented follow-on — it needs `evalBV` / `envReader` re-indexed at width 32.
-/

/-- The bitwise sub-fragment of `srcClean`: variable/literal leaves plus the four
    word-algebra bitwise ops (`^^^`/`&&&`/`<<<`/`>>>`). `SVar` leaves are non-temp
    source names and `SLit` literals are `< 2^64` (the `srcClean` leaf conditions),
    so `IsWordClean e → srcClean e`. A rotate `x <<<< k` is the derived shape
    `SXor (SShl x k) (SShr x (SLit (64-k)))`, itself `IsWordClean` — rotate composes
    from shifts + xor with no new node. -/
def IsWordClean : SExpr → Prop
  | .SVar x => ¬ isTmpName x
  | .SLit n => n < 2 ^ 64
  | .SXor a b | .SAnd a b | .SShl a b | .SShr a b => IsWordClean a ∧ IsWordClean b
  | _ => False

/-- The bitwise fragment is source-clean (`srcClean` covers the bitwise arms). -/
theorem isWordClean_srcClean : ∀ e, IsWordClean e → srcClean e := by
  intro e
  induction e with
  | SVar x => intro h; exact h
  | SLit n => intro h; exact h
  | SXor a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | SAnd a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | SShl a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | SShr a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | SAdd a b iha ihb => intro h; exact h.elim
  | SSub a b iha ihb => intro h; exact h.elim
  | SMul a b iha ihb => intro h; exact h.elim
  | SMulHiU a b iha ihb => intro h; exact h.elim
  | SLt a b iha ihb => intro h; exact h.elim
  | SAsr a b iha ihb => intro h; exact h.elim
  | SMulS a b iha ihb => intro h; exact h.elim
  | SMulHiS a b iha ihb => intro h; exact h.elim
  | SLimb v i => intro h; exact h.elim

/-- The bitwise word-phase state relation restricted to non-temp source names:
    every non-temp name holds a `.sword 64` whose word is the abstract `BitVec 64`
    value **directly**. The abstraction is the identity — the clean spec IS the
    `evalBV` word computation, with no `wEnc`/`ZMod` transfer. As with `SRwordNT`,
    the fresh-temp namespace the lowering scribbles is invisible to a source
    kernel, so the relation constrains only non-temp names. -/
def SRwordBV (env : SEnvScalar) (a : String → BitVec 64) : Prop :=
  ∀ x, ¬ isTmpName x → env x = some ⟨.sword 64, a x⟩

/-- `RScalarSet name n` over the bitwise non-temp relation `SRwordBV` — the literal
    leaf of the bitwise ascent. The abstract value is the word `BitVec.ofNat 64 n`
    itself (no `ZMod` abstraction), so a bitwise kernel that loads a round constant
    and then mixes it lifts through one fragment. -/
theorem corres_setScalar_BV (name : String) (n : Nat) :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = name then BitVec.ofNat 64 n else a s)
      (.RScalarSet name n) := by
  intro env a hSR _
  refine ⟨env.upd name (t := .sword 64) (BitVec.ofNat 64 n), rfl, ?_⟩
  intro x hnt
  by_cases hx : x = name
  · subst hx; simp [SEnvScalar.upd]
  · simp only [SEnvScalar.upd, if_neg hx]
    exact hSR x hnt

/-- `corres_setExprBitwise` — the bitwise `RScalarSetExpr x e` value leaf. From a
    concrete env `SRwordBV`-related to abstract `a : String → BitVec 64`, the real
    `semScalar` `RScalarSetExpr` arm makes progress (`= some _`, via
    `semLowerSExpr_ok'`) to an env related to the abstract state that sets `x` to
    `SExpr.evalBV a e` (the clean **word** value — no `ZMod` abstraction) and leaves
    every other source name untouched. The value step is `evalBV_congr_on` (reader
    agreement), not a ring square — the transfer is definitional for the bitwise
    fragment. -/
theorem corres_setExprBitwise (x : String) (e : SExpr) (he : IsWordClean e) :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = x then SExpr.evalBV a e else a s)
      (.RScalarSetExpr x e) := by
  intro env a hSR _
  -- A witnessing rust state whose scalar store reads back the env words, so the
  -- proven fresh-temp success lemma `semLowerSExpr_ok'` applies.
  set rs : RustState := ⟨fun _ => none, fun y => (a y).toNat⟩ with hrs
  have hEB : EnvBoundOn rs env (fun _ => True) := by
    intro y _ hnt
    have hround : BitVec.ofNat 64 (a y).toNat = a y := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (a y).isLt
    show env y = some ⟨.sword 64, BitVec.ofNat 64 ((a y).toNat)⟩
    rw [hround]; exact hSR y hnt
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ :=
    semLowerSExpr_ok' rs (fun _ => True) e env 0 hEB (varsBoundIn_true e)
      (isWordClean_srcClean e he)
  -- the stored value: `evalBV` under the env reader agrees with `evalBV a` since
  -- the reader agrees with `a` on every non-temp leaf (definitional, no ring square)
  have hval : SExpr.evalBV (envReader env) e = SExpr.evalBV a e := by
    apply evalBV_congr_on (fun _ => True) (envReader env) a e _ (varsBoundIn_true e)
      (isWordClean_srcClean e he)
    intro s _ hns
    simp only [envReader, hSR s hns]
  refine ⟨env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e), ?_, ?_⟩
  · simp only [semScalar, hsem]
  · intro y hnt
    by_cases hyx : y = x
    · show (env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e)) y
        = some ⟨.sword 64, if y = x then SExpr.evalBV a e else a y⟩
      rw [if_pos hyx]
      simp only [SEnvScalar.upd, if_pos hyx]
      rw [hval]
    · show (env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e)) y
        = some ⟨.sword 64, if y = x then SExpr.evalBV a e else a y⟩
      rw [if_neg hyx]
      simp only [SEnvScalar.upd, if_neg hyx]
      rw [hotb y (Or.inl hnt)]
      exact hSR y hnt

/-! ## A concrete bitwise kernel closes

A ChaCha-style quarter-round mix step `d := d ^^^ a` and a Keccak-`χ`-style step
`e := a ^^^ (¬b &&& c)` (with `¬b` spelled `SXor b (SLit (2^64-1))`, all-ones xor)
are both `IsWordClean`, so the leaf closes them — the exact bitwise shapes the
arithmetic leaf could not reach. -/

/-- Short source names are never fresh temps (`tmpName k = "__sx" ++ …` has length
    ≥ 5), so a length-`< 4` name is `¬ isTmpName`. -/
theorem notTmp_of_short (s : String) (hs : s.length < 4) : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  have hlen := congrArg String.length hk
  rw [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms.tmpName,
    String.length_append] at hlen
  have h2 : "__sx".length = 4 := rfl
  omega

/-- ChaCha-style `d := d ^^^ a` closes through the bitwise leaf. -/
example :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "d" then SExpr.evalBV a (.SXor (.SVar "d") (.SVar "a")) else a s)
      (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a"))) :=
  corres_setExprBitwise "d" (.SXor (.SVar "d") (.SVar "a"))
    ⟨notTmp_of_short "d" (by decide), notTmp_of_short "a" (by decide)⟩

/-- Keccak-`χ`-style `e := a ^^^ (¬b &&& c)`, with `¬b = b ^^^ (2^64-1)`, closes. -/
example :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "e" then
          SExpr.evalBV a (.SXor (.SVar "a")
            (.SAnd (.SXor (.SVar "b") (.SLit (2 ^ 64 - 1))) (.SVar "c")))
        else a s)
      (.RScalarSetExpr "e" (.SXor (.SVar "a")
        (.SAnd (.SXor (.SVar "b") (.SLit (2 ^ 64 - 1))) (.SVar "c")))) :=
  corres_setExprBitwise "e" _
    ⟨notTmp_of_short "a" (by decide),
     ⟨⟨notTmp_of_short "b" (by decide), Nat.sub_lt (by positivity) Nat.one_pos⟩,
      notTmp_of_short "c" (by decide)⟩⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
