/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteUnsat
public import CatCrypt.Hax.PrimeirBuiltins
public import CatCrypt.Hax.TExprTypingSpine
public import CatCrypt.Crypto.Hax.NFFieldSum
public import CatCrypt.Crypto.PrimeIR.Extraction.Fp256Mont_haxpipe
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteUnsat
public meta import CatCrypt.Hax.PrimeirBuiltins
public meta import CatCrypt.Hax.TExprTypingSpine
public meta import CatCrypt.Crypto.Hax.NFFieldSum
public meta import CatCrypt.Crypto.PrimeIR.Extraction.Fp256Mont_haxpipe

@[expose] public section

set_option autoImplicit false

/-!
# The hax compiler on a function over a prime field

A Rust function over the `primeir_hax::Field` trait is extracted with the field operations as
the bare calls `add`, `sub`, `mul`, `neg`, `square` and `double` on integers; the reference
interpreter reads them with the builtins `primeirBuiltins p`, which reduce modulo `p`.

The front `impToNF` carries each such call as the leaf call `NfOp.call f as .int` at the call
typing `fieldSigOf`; `fieldSigOf_typedCalls` is the typing hypothesis of `impToNF_sound` for
`primeirBuiltins p`. The translation `fieldOfNF primeirFieldTable p` of `NFFieldSum` takes
the program of `NFProg nfDialect`, through the field summand of
`Dialect.sum nfDialect fieldDialect`, to a program of `fieldDialect` over the prime field
`ZMod p`; `fieldOfNF_sound` states that it computes the residue the source computes.
The program of `fieldDialect` is lowered by the template `fieldTemplateOf p` chosen from the
modulus by the first arm that returns one: the unsaturated template of `FieldRouteUnsat` when
an unsaturated instance has modulus `p` (Curve25519, p448), the Solinas template when
`solinasParamsOf p` recognises `p = 2 ^ k - c`, the single-word template of `FieldRouteNarrow` when its bounds
certificate holds at `p` (BabyBear, KoalaBear, Mersenne-31), and the Montgomery template of
the record `limbParamsOf p` otherwise.

## Main definitions

* `fieldSigOf` — the call typing of the field calls.
* `limbParamsOf` — the Montgomery record of `n = ⌊log₂ p / 64⌋ + 1` limbs of an odd modulus.
* `solinasParamsOf` — the Solinas record of a modulus `2 ^ k - c` (from `FieldWideInline`).
* `solinasTemplateOf`, `montTemplateOf` — the Solinas and Montgomery arms.
* `fieldTemplateOf` — the field template of a modulus, the first arm of the chain
  `unsatTemplateOf p <|> solinasTemplateOf p <|> narrowTemplateOf p <|> montTemplateOf p`
  that returns one.
* `fldRen` — the renaming of the parameters to field variables of the summed dialect.
* `fieldFront`, `ArgsHold`, `fieldRuns`, `fieldLeg` — the front of a function over the field
  with the parameters `xs`, its source semantics through the layout `fieldAbi xs.length n`,
  and the front as a `FrontLegOf`.

## Main results

* `fieldSigOf_typedCalls` — the call typing is sound for `primeirBuiltins p`.
* `solinasParamsOf_spec`, `fieldTemplateOf_spec` — the records and templates have the
  modulus `p`; `fieldTemplateOf_of_unsat`, `fieldTemplateOf_of_solinas`,
  `fieldTemplateOf_of_narrow`, `fieldTemplateOf_of_mont` — the four cases of the choice.
* `limbParamsOf_limbs` — a Montgomery record at `p ≥ 2^64` has `fieldLimbs p` limbs.
* `wideTemplateOf_agrees` — at `p ≥ 2^64` outside the unsaturated and narrow arms, the scalar
  rule `fieldTemplateOf` and the wide rule `FieldWideInline.wideTemplateOf` return the
  Solinas templates of the same record or the Montgomery templates of the record
  `montParams p`.
* `fieldTemplateOf_babyBear`, `fieldTemplateOf_koalaBear`, `fieldTemplateOf_mersenne31` — the
  narrow template is chosen at the three single-word primes.
* `fieldTemplateOf_curve25519`, `fieldTemplateOf_p448` — the unsaturated template is chosen
  at `2 ^ 255 - 19` and `2 ^ 448 - 2 ^ 224 - 1`.
* `denoteSpine_eq_of_spineLamFree` — on a body whose spine binds no closure the spine reading
  is `denote'`.
* `field_correct_auto` — the halting run and the read-back of `haxc_correct_auto` without
  linked functions for the field front, at every modulus and every arity.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.Hax.ImpToNF (TypedCalls tableOf enc encAll)
open CatCrypt.Crypto.Hax.NFFieldSum (SRen SAgree inrCtx inrVal fieldOfNF fieldOfNF_sound
  primeirFieldTable primeirFieldTable_ok primeirFieldTable_agrees)
open Ctxt (Var Valuation)
open _root_.Hax (Value)
open CatCrypt.Hax (primeirBuiltins)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrLimbs arrTy encL encL_fp)

/-! ## 1. The call typing of the field calls -/

/-- The call typing of the field calls: an integer for `add`, `sub`, `mul` on two integers
    and for `neg`, `square`, `double` on one integer. -/
def fieldSigOf : String → List NfTy → Option NfTy
  | "add", [.int, .int] | "sub", [.int, .int] | "mul", [.int, .int] => some .int
  | "neg", [.int] | "square", [.int] | "double", [.int] => some .int
  | _, _ => none

/-- **The call typing of the field calls is sound** for `primeirBuiltins p`. -/
theorem fieldSigOf_typedCalls (p : Nat) : TypedCalls (primeirBuiltins p) fieldSigOf := by
  intro f as r h xs v hv
  unfold fieldSigOf at h
  split at h <;> first
    | (cases h
       rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨⟩⟩⟩
       simp only [encAll, enc, CatCrypt.Hax.primeirBuiltins_add,
         CatCrypt.Hax.primeirBuiltins_sub, CatCrypt.Hax.primeirBuiltins_mul,
         CatCrypt.Hax.primeirBuiltins_neg, CatCrypt.Hax.primeirBuiltins_square,
         CatCrypt.Hax.primeirBuiltins_double, Option.some.injEq] at hv
       subst hv
       exact ⟨_, rfl, rfl⟩)
    | cases h

/-- `primeirBuiltins p` has no `repeat` row, so it satisfies `RepeatCalls`. -/
theorem repeatCalls_primeirBuiltins (p : Nat) :
    CatCrypt.Crypto.Hax.ImpToNF.RepeatCalls (primeirBuiltins p) := by
  intro x N v _ h
  have h0 : primeirBuiltins p "repeat" [.int x, .int N] = none := rfl
  rw [h0] at h
  cases h

/-! ## 2. The Montgomery record of a modulus -/

/-- The inverse of an odd `p` modulo `2 ^ 64` by six Newton steps `x ↦ x (2 - p x)` from
    `x = p`, each doubling the number of correct low bits from three. -/
def invMod64 (p : Nat) : Nat :=
  (fun x => x * ((2 + 2 ^ 64 - (p * x) % 2 ^ 64) % 2 ^ 64) % 2 ^ 64)^[6] (p % 2 ^ 64)

/-- **The Montgomery record of the modulus `p`**: `n = ⌊log₂ p / 64⌋ + 1` limbs and
    `nInv = -p⁻¹ mod 2 ^ 64`, when `p` is odd and above `1` and the checks of the record
    hold; `none` otherwise. -/
def limbParamsOf (p : Nat) : Option (Σ n, LimbParams n) :=
  let n := Nat.log2 p / 64 + 1
  let nInv := (2 ^ 64 - invMod64 p) % 2 ^ 64
  if h : 1 < p ∧ p % 2 = 1 ∧ p < 2 ^ (64 * n) ∧ nInv < 2 ^ 64 ∧
      (p * nInv + 1) % 2 ^ 64 = 0 ∧ n < 2 ^ 64 then
    some ⟨n, ⟨p, nInv, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩⟩
  else none

theorem limbParamsOf_spec {p n : Nat} {P : LimbParams n}
    (h : limbParamsOf p = some ⟨n, P⟩) : P.p = p ∧ n < 2 ^ 64 := by
  unfold limbParamsOf at h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    exact ⟨rfl, hc.2.2.2.2.2⟩
  · cases h

/-! ## 3. The Solinas record of a modulus -/

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams)

/-! The Solinas record `solinasParamsOf p` of a modulus `2 ^ k - c` and its soundness
`solinasParamsOf_spec` are those of `FieldWideInline`, the rule of the wide templates. -/
export CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (solinasParamsOf
  solinasParamsOf_spec)

/-! ## 4. The front of a function over the field -/

open _root_.Hax (TExpr Env ImpExpr Builtins denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (spineLamFree isLamE)
open CatCrypt.Crypto.Hax.ImpToNF (impToNF entryEnv entryCtx EntryVals entryEnv_rel impToNF_sound
  PDenP PDenP_plug_ret)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (FieldTemplate montTemplate
  solinasTemplate fieldAbi fieldAbi2 fieldArgReg opVals abiValN abiValOf_fieldAbi
  FieldTemplate.route_abi_denote)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow (narrowFoldsOf narrowTemplate
  narrowTemplateOf narrowTemplateOf_spec narrowTemplateOf_of_narrowFoldsOf
  narrowTemplateOf_of_none narrowFoldsOf_babyBear narrowFoldsOf_koalaBear
  narrowFoldsOf_mersenne31)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteUnsat (unsatReprOf reprTemplate
  unsatTemplateOf unsatTemplateOf_spec unsatTemplateOf_of_unsatReprOf unsatTemplateOf_of_none
  unsatReprOf_curve25519 unsatReprOf_p448 p448)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatField (FieldReprTemplate
  curve25519Repr p448Repr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (wordsFn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend flatVal)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrCtx arrFlat)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-- On a body whose statement spine binds no closure, the spine reading `denoteSpine` is
    `denote'`. -/
theorem denoteSpine_eq_of_spineLamFree (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (h : spineLamFree e = true) : denoteSpine bi fuel e = denote' bi fuel e := by
  induction e using _root_.Hax.ImpExpr.ind with
  | letBind x v b _ ihb =>
      simp only [spineLamFree, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      cases v with
      | lam ps body => simp [isLamE] at h
      | _ =>
          rw [CatCrypt.Hax.TExprTypingSpine.denote'_letBind, ← ihb h.2]
          rfl
  | seq a b _ ihb =>
      rw [CatCrypt.Hax.TExprTypingSpine.denote'_seq, ← ihb h]
      rfl
  | _ => rfl

/-- Two word arrays with the same limbs from the index `j` agree at the indices
    `j, …, j + m - 1`. -/
theorem stackGet_eq_of_arrLimbs {n : Nat} {a b : Fin n → BitVec 64} :
    ∀ (m j : Nat), arrLimbs a m j = arrLimbs b m j →
      ∀ i, i < m → stackGet a (j + i) = stackGet b (j + i)
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, j, h, i, hi => by
      injection h with _ _ h1 h2
      cases i with
      | zero => exact h1
      | succ i =>
          rw [show j + (i + 1) = (j + 1) + i by omega]
          exact stackGet_eq_of_arrLimbs m (j + 1) h2 i (by omega)

/-- Two word arrays of `n` limbs with the same limbs have the same source value. -/
theorem arrVal_eq_of_arrLimbs {n : Nat} {a b : Fin n → BitVec 64}
    (h : arrLimbs a n 0 = arrLimbs b n 0) : arrVal a = arrVal b := by
  unfold arrVal
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  have := stackGet_eq_of_arrLimbs n 0 h j hj
  simp only [Nat.zero_add] at this
  rw [this]

/-- **The Solinas arm**: the Solinas template when `solinasParamsOf p` recognises
    `p = 2 ^ k - c`. -/
def solinasTemplateOf (p : Nat) : Option (Σ n, FieldTemplate n) :=
  match hs : solinasParamsOf p with
  | some ⟨n, S⟩ => some ⟨n, solinasTemplate S (solinasParamsOf_spec hs).2⟩
  | none => none

theorem solinasTemplateOf_spec {p n : Nat} {T : FieldTemplate n}
    (h : solinasTemplateOf p = some ⟨n, T⟩) : T.p = p := by
  unfold solinasTemplateOf at h
  split at h
  · rename_i hs
    cases h
    exact (solinasParamsOf_spec hs).1
  · cases h

/-- **The Montgomery arm**: the Montgomery template of the record `limbParamsOf p`. -/
def montTemplateOf (p : Nat) : Option (Σ n, FieldTemplate n) :=
  match hm : limbParamsOf p with
  | some ⟨n, P⟩ => some ⟨n, montTemplate P (limbParamsOf_spec hm).2⟩
  | none => none

theorem montTemplateOf_spec {p n : Nat} {T : FieldTemplate n}
    (h : montTemplateOf p = some ⟨n, T⟩) : T.p = p := by
  unfold montTemplateOf at h
  split at h
  · rename_i hm
    cases h
    exact (limbParamsOf_spec hm).1
  · cases h

/-- **The field template of the modulus `p`**: the first arm that returns a template, in the
    order unsaturated (an instance of `FieldRouteUnsat.unsatReprs` with modulus `p`), Solinas
    (`p = 2 ^ k - c` with `64 ≤ k`), narrow (a single-word prime certified by
    `FieldRouteNarrow.narrowCert`), Montgomery. -/
def fieldTemplateOf (p : Nat) : Option (Σ n, FieldTemplate n) :=
  unsatTemplateOf p <|> solinasTemplateOf p <|> narrowTemplateOf p <|> montTemplateOf p

theorem fieldTemplateOf_spec {p n : Nat} {T : FieldTemplate n}
    (h : fieldTemplateOf p = some ⟨n, T⟩) : T.p = p := by
  unfold fieldTemplateOf at h
  cases hu : unsatTemplateOf p with
  | some q =>
      rw [hu] at h
      change some q = some ⟨n, T⟩ at h
      cases h
      exact unsatTemplateOf_spec hu
  | none =>
  rw [hu] at h
  change (solinasTemplateOf p <|> narrowTemplateOf p <|> montTemplateOf p) = some ⟨n, T⟩ at h
  cases hs : solinasTemplateOf p with
  | some q =>
      rw [hs] at h
      change some q = some ⟨n, T⟩ at h
      cases h
      exact solinasTemplateOf_spec hs
  | none =>
      rw [hs] at h
      change (narrowTemplateOf p <|> montTemplateOf p) = some ⟨n, T⟩ at h
      cases hn : narrowTemplateOf p with
      | some q =>
          rw [hn] at h
          change some q = some ⟨n, T⟩ at h
          cases h
          exact narrowTemplateOf_spec hn
      | none =>
          rw [hn] at h
          exact montTemplateOf_spec h

/-- **The unsaturated case of the choice**: when `unsatReprOf p` returns the instance `R`,
    the field template of `p` is the unsaturated template of `R`. -/
theorem fieldTemplateOf_of_unsat {p : Nat} {R : FieldReprTemplate}
    (h : unsatReprOf p = some R) :
    ∃ hc, fieldTemplateOf p = some ⟨R.P.n, reprTemplate R hc⟩ := by
  obtain ⟨hc, hu⟩ := unsatTemplateOf_of_unsatReprOf h
  refine ⟨hc, ?_⟩
  rw [fieldTemplateOf, hu]
  rfl

/-- **The Solinas case of the choice**: when no unsaturated instance has modulus `p` (`hu`,
    decided at a concrete modulus) and `solinasParamsOf p` returns the record `S`, the field
    template of `p` is the Solinas template of `S`. -/
theorem fieldTemplateOf_of_solinas {p n : Nat} {S : SolinasParams n}
    (h : solinasParamsOf p = some ⟨n, S⟩)
    (hu : (unsatReprOf p).isNone = true := by decide +kernel) :
    ∃ hn, fieldTemplateOf p = some ⟨n, solinasTemplate S hn⟩ := by
  refine ⟨(solinasParamsOf_spec h).2, ?_⟩
  have hs : solinasTemplateOf p = some ⟨n, solinasTemplate S (solinasParamsOf_spec h).2⟩ := by
    unfold solinasTemplateOf
    split
    · rename_i hs
      rw [h] at hs
      cases hs
      rfl
    · rename_i hs
      rw [h] at hs
      cases hs
  rw [fieldTemplateOf, unsatTemplateOf_of_none hu, hs]
  rfl

theorem solinasTemplateOf_of_none {p : Nat} (hs : solinasParamsOf p = none) :
    solinasTemplateOf p = none := by
  unfold solinasTemplateOf
  split
  · rename_i hs'
    rw [hs] at hs'
    cases hs'
  · rfl

/-- **The narrow case of the choice**: when no unsaturated instance has modulus `p` (`hu`,
    decided at a concrete modulus), `solinasParamsOf p` is `none` and the certificate of the
    narrow template selects `k` folds at `p`, the field template of `p` is the narrow template
    at `k`. -/
theorem fieldTemplateOf_of_narrow {p k : Nat} (hs : solinasParamsOf p = none)
    (h : narrowFoldsOf p = some k)
    (hu : (unsatReprOf p).isNone = true := by decide +kernel) :
    ∃ hc, fieldTemplateOf p = some ⟨1, narrowTemplate p k hc⟩ := by
  obtain ⟨hc, hn⟩ := narrowTemplateOf_of_narrowFoldsOf h
  refine ⟨hc, ?_⟩
  rw [fieldTemplateOf, unsatTemplateOf_of_none hu, solinasTemplateOf_of_none hs, hn]
  rfl

/-- **The Montgomery case of the choice**: when `solinasParamsOf p` is `none`, the narrow
    certificate selects no fold count at `p` and no unsaturated instance has modulus `p`
    (`hw`, `hu`, decided at a concrete modulus), and `limbParamsOf p` returns the record `P`,
    the field template of `p` is the Montgomery template of `P`. -/
theorem fieldTemplateOf_of_mont {p n : Nat} {P : LimbParams n}
    (hs : solinasParamsOf p = none) (h : limbParamsOf p = some ⟨n, P⟩)
    (hw : narrowFoldsOf p = none := by decide +kernel)
    (hu : (unsatReprOf p).isNone = true := by decide +kernel) :
    ∃ hn, fieldTemplateOf p = some ⟨n, montTemplate P hn⟩ := by
  refine ⟨(limbParamsOf_spec h).2, ?_⟩
  have hm : montTemplateOf p = some ⟨n, montTemplate P (limbParamsOf_spec h).2⟩ := by
    unfold montTemplateOf
    split
    · rename_i hm
      rw [h] at hm
      cases hm
      rfl
    · rename_i hm
      rw [h] at hm
      cases hm
  rw [fieldTemplateOf, unsatTemplateOf_of_none hu, solinasTemplateOf_of_none hs,
    narrowTemplateOf_of_none hw, hm]
  rfl

/-- **A Montgomery record of the recogniser at `p ≥ 2^64` has `fieldLimbs p` limbs.** -/
theorem limbParamsOf_limbs {p n : Nat} {P : LimbParams n} (h64 : 2 ^ 64 ≤ p)
    (h : limbParamsOf p = some ⟨n, P⟩) : n = _root_.Hax.FieldTag.fieldLimbs p := by
  unfold limbParamsOf at h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨-, hodd, hlt, -⟩ := hc
    have hp0 : p ≠ 0 := by omega
    have hle := Nat.log2_self_le hp0
    have hlog : 64 ≤ Nat.log2 p := (Nat.le_log2 hp0).mpr h64
    have hne : 2 ^ Nat.log2 p ≠ p := by
      intro he
      have : 2 ^ Nat.log2 p % 2 = 0 := by
        rw [show Nat.log2 p = (Nat.log2 p - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
      omega
    have hlo : 2 ^ (64 * (Nat.log2 p / 64 + 1 - 1)) ≤ 2 ^ Nat.log2 p :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (FieldWideInline.fieldLimbs_eq (by omega) hlt.le).symm
  · cases h

open FieldWideInline (WideTemplate wideTemplateOf wideTemplateOf_eq_solinas
  wideTemplateOf_eq_mont montParams) in
/-- **The scalar and the wide rule return the same arithmetic.** At a modulus `p ≥ 2^64` with
    `fieldLimbs p < 2^64` at which the scalar rule takes neither the unsaturated nor the narrow
    arm (`hu`, `hw`), either `solinasParamsOf p` returns a record `S`, and the scalar rule
    returns the Solinas template of `S` and the wide rule the Solinas template
    `WideTemplate.ofSolinasAt S`; or `solinasParamsOf p` is `none`, and at every record `P` of
    `limbParamsOf p` the scalar rule returns the Montgomery template of `P`, `P` is the record
    `montParams p` over `fieldLimbs p` limbs, and the wide rule returns the canonical
    Montgomery template of `montParams p`. -/
theorem wideTemplateOf_agrees {p : Nat} (h64 : 2 ^ 64 ≤ p)
    (hn : _root_.Hax.FieldTag.fieldLimbs p < 2 ^ 64) (hu : (unsatReprOf p).isNone = true)
    (hw : narrowFoldsOf p = none) :
    (∃ (n : Nat) (S : SolinasParams n), solinasParamsOf p = some ⟨n, S⟩ ∧
      ∃ (hn' : n < 2 ^ 64) (hS : n = _root_.Hax.FieldTag.fieldLimbs (Solinas.p S))
        (hp : Solinas.p S = p),
        fieldTemplateOf p = some ⟨n, solinasTemplate S hn'⟩ ∧
        wideTemplateOf p = some ((WideTemplate.ofSolinasAt S hS hn').castP hp)) ∨
    (solinasParamsOf p = none ∧ ∀ (n : Nat) (P : LimbParams n),
      limbParamsOf p = some ⟨n, P⟩ →
      ∃ (hn' : n < 2 ^ 64) (h1 : 1 < p) (hp : p % 2 = 1)
        (e : n = _root_.Hax.FieldTag.fieldLimbs p),
        fieldTemplateOf p = some ⟨n, montTemplate P hn'⟩ ∧
        cast (congrArg LimbParams e) P = montParams p h1 hp ∧
        wideTemplateOf p = some (WideTemplate.ofMont (montParams p h1 hp) hn)) := by
  rcases hs : solinasParamsOf p with _ | ⟨n, S⟩
  · refine Or.inr ⟨rfl, fun n P h => ?_⟩
    obtain ⟨hn', hf⟩ := fieldTemplateOf_of_mont hs h hw hu
    have hPp := (limbParamsOf_spec h).1
    have hodd : p % 2 = 1 := hPp ▸ P.p_odd
    have h1 : 1 < p := hPp ▸ P.one_lt
    have e := limbParamsOf_limbs h64 h
    refine ⟨hn', h1, hodd, e, hf, ?_, wideTemplateOf_eq_mont h64 hodd hn hs⟩
    subst e
    have hi := FieldWideInline.LimbParams.nInv_eq_montNInv P
    obtain ⟨q, ni, _, _, _, _, _⟩ := P
    simp only at hPp hi
    subst hPp hi
    rfl
  · refine Or.inl ⟨n, S, rfl, ?_⟩
    obtain ⟨hn', hf⟩ := fieldTemplateOf_of_solinas hs hu
    exact ⟨hn', _, _, hf, wideTemplateOf_eq_solinas hs h64⟩

/-- **The narrow template at BabyBear**, `p = 2³¹ − 2²⁷ + 1`. -/
theorem fieldTemplateOf_babyBear :
    ∃ hc, fieldTemplateOf 2013265921 = some ⟨1, narrowTemplate 2013265921 8 hc⟩ :=
  fieldTemplateOf_of_narrow (by decide) narrowFoldsOf_babyBear

/-- **The narrow template at KoalaBear**, `p = 2³¹ − 2²⁴ + 1`. -/
theorem fieldTemplateOf_koalaBear :
    ∃ hc, fieldTemplateOf 2130706433 = some ⟨1, narrowTemplate 2130706433 5 hc⟩ :=
  fieldTemplateOf_of_narrow (by decide) narrowFoldsOf_koalaBear

/-- **The narrow template at Mersenne-31**, `p = 2³¹ − 1`. -/
theorem fieldTemplateOf_mersenne31 :
    ∃ hc, fieldTemplateOf 2147483647 = some ⟨1, narrowTemplate 2147483647 1 hc⟩ :=
  fieldTemplateOf_of_narrow (by decide) narrowFoldsOf_mersenne31

/-- **The unsaturated template at Curve25519**, `p = 2²⁵⁵ − 19`: five limbs of 51 bits. -/
theorem fieldTemplateOf_curve25519 :
    ∃ hc, fieldTemplateOf (2 ^ 255 - 19) =
      some ⟨curve25519Repr.P.n, reprTemplate curve25519Repr hc⟩ :=
  fieldTemplateOf_of_unsat unsatReprOf_curve25519

/-- **The unsaturated template at p448**, `p = 2⁴⁴⁸ − 2²²⁴ − 1`: eight limbs of 56 bits. -/
theorem fieldTemplateOf_p448 :
    ∃ hc, fieldTemplateOf p448 = some ⟨p448Repr.P.n, reprTemplate p448Repr hc⟩ :=
  fieldTemplateOf_of_unsat unsatReprOf_p448

/-- The parameters `xs` of a function over the field, as integers. -/
def fieldPs (xs : List String) : List (String × NfTy) := xs.map fun x => (x, .int)

/-- The context of field variables of the parameters `xs`. -/
abbrev fieldCtx (p : Nat) (xs : List String) : Ctxt fieldDialect :=
  (entryCtx (fieldPs xs)).map fun _ => FieldTy.fp p

theorem fieldCtx_length (p : Nat) (xs : List String) : (fieldCtx p xs).length = xs.length := by
  simp [fieldCtx, entryCtx, fieldPs]

/-- The renaming of the parameters `xs` into the right-summand image of `fieldCtx p xs`: each
    parameter is carried at the kind `fld` by the field variable of its slot. -/
def fldRen (p : Nat) :
    (xs : List String) → SRen p (entryCtx (fieldPs xs)) (inrCtx (fieldCtx p xs))
  | _ :: _, _, .here => ⟨.fld, .here⟩
  | _ :: xs, _, .there v => ⟨(fldRen p xs v).k, .there (fldRen p xs v).v⟩

/-- **The front of a function over the field** at the template `T`: the erased body, when its
    spine binds no closure and it has no `whileFold` (`ImpToNF.whileFoldFree`), translated by `impToNF` at the call typing `fieldSigOf` from the
    parameters `xs`, pruned by `NFProg.dce`, translated to `fieldDialect` at `T.p` by
    `fieldOfNF primeirFieldTable` from the renaming `fldRen`, and lowered to a route program
    by `T.route`. -/
def fieldFront {n : Nat} (T : FieldTemplate n) (xs : List String) (te : TExpr) :
    Option (RouteProg (arrCtx n (fieldCtx T.p xs) ++ [arrTy n]) (arrTy n)) :=
  if spineLamFree te.erase = true ∧ CatCrypt.Crypto.Hax.ImpToNF.whileFoldFree te.erase = true then
    (impToNF fieldSigOf none (entryEnv (fieldPs xs)) te.erase).bind fun o =>
      (fieldOfNF primeirFieldTable T.p (NFProg.dce o.prog) (fldRen T.p xs)).bind fun c =>
        T.route c
  else none

/-- **The operands at a machine state.** For the parameters `xs` and the field elements `A`:
    the array of each parameter, at the register of its slot in `fieldAbi xs.length n`, holds
    the limbs `T.enc` of its element, and the environment `env` binds its name to the
    representative of its element. -/
def ArgsHold {n : Nat} (T : FieldTemplate n) (sa : AState) (env : Env) :
    (xs : List String) → Valuation (fieldCtx T.p xs) → Prop
  | [], _ => True
  | x :: xs, .cons a A =>
      arrLimbs (wordsFn sa (sa.regs (fieldArgReg (xs.length + 1))) n) n 0 = T.enc a ∧
        env x = some (.int (ZMod.val (n := T.p) a : Int)) ∧ ArgsHold T sa env xs A

/-- The representatives of field elements, as the integer values of the parameters. -/
def intsOf {p : Nat} : (xs : List String) → Valuation (fieldCtx p xs) →
    Valuation (entryCtx (fieldPs xs))
  | [], _ => .nil
  | _ :: xs, .cons a A => .cons (ZMod.val (n := p) a : Int) (intsOf xs A)

theorem entryVals_of_argsHold {n : Nat} {T : FieldTemplate n} {sa : AState} {env : Env} :
    ∀ (xs : List String) (A : Valuation (fieldCtx T.p xs)), ArgsHold T sa env xs A →
      EntryVals env (fieldPs xs) (intsOf xs A)
  | [], _, _ => trivial
  | _ :: xs, .cons _ A, h => by
      obtain ⟨-, he, h⟩ := h
      exact ⟨he, entryVals_of_argsHold xs A h⟩

/-- The representatives of field elements agree with the elements along `fldRen`. -/
theorem sAgree_fldRen {p : Nat} [NeZero p] :
    ∀ (xs : List String) (A : Valuation (fieldCtx p xs)),
      SAgree (fldRen p xs) (intsOf xs A) (inrVal A)
  | [], _ => fun _ v => nomatch v
  | _ :: xs, .cons a A => fun t v => by
      cases v with
      | here =>
        change ((ZMod.val (n := p) a : Int) : ZMod p) = a
        simp
      | there v => exact sAgree_fldRen xs A t v

theorem arrFlat_of_argsHold {n : Nat} {T : FieldTemplate n} {sa : AState} {env : Env} :
    ∀ (xs : List String) (A : Valuation (fieldCtx T.p xs)), ArgsHold T sa env xs A →
      arrFlat (opVals n sa (fieldCtx T.p xs)) = flatVal (fun {t} x => T.encL (t := t) x) A
  | [], .nil, _ => rfl
  | _ :: xs, .cons a A, h => by
      obtain ⟨hl, -, h⟩ := h
      change hvAppend (arrLimbs (wordsFn sa (sa.regs (fieldArgReg
        ((fieldCtx T.p xs).length + 1))) n) n 0) (arrFlat (opVals n sa (fieldCtx T.p xs)))
        = hvAppend (T.encL (t := .fp T.p) a) (flatVal (fun {t} x => T.encL (t := t) x) A)
      rw [fieldCtx_length, hl, T.encL_fp, arrFlat_of_argsHold xs A h]
      rfl

/-- **The source semantics of a function over the field `ZMod p`** with the parameters `xs`,
    through the layout `fieldAbi xs.length n` of the template `T = fieldTemplateOf p`: the
    operand arrays hold the limbs `T.enc` of the elements `A` and the environment `env` binds
    the parameters to their representatives (`ArgsHold`); the spine reading of `te` with the
    builtins `primeirBuiltins T.p` returns the representative of `r`; and `v` is the source
    value of a word array holding the limbs `T.enc r`. -/
def fieldRuns (p : Nat) (xs : List String) (σ : AbiLayout) (te : TExpr) (sa : AState)
    (v : Value) : Prop :=
  ∃ (n : Nat) (T : FieldTemplate n), fieldTemplateOf p = some ⟨n, T⟩ ∧
    σ = fieldAbi xs.length n ∧
    ∃ (A : Valuation (fieldCtx T.p xs)) (r : ZMod T.p) (env : Env) (fuel : Nat) (env' : Env),
      ArgsHold T sa env xs A ∧
      (denoteSpine (primeirBuiltins T.p) fuel te.erase).run env =
        (.val (.int (r.val : Int)), env') ∧
      ∃ arr : Fin n → BitVec 64, arrLimbs arr n 0 = T.enc r ∧ v = arrVal arr

/-- The leg of the field front. -/
theorem fieldFront_leg {n : Nat} (T : FieldTemplate n) (xs : List String) (te : TExpr)
    (rp : RouteProg (arrCtx n (fieldCtx T.p xs) ++ [arrTy n]) (arrTy n))
    (hf : fieldFront T xs te = some rp) (sa : AState) (A : Valuation (fieldCtx T.p xs))
    (r : ZMod T.p) (env : Env) (fuel : Nat) (env' : Env) (hargs : ArgsHold T sa env xs A)
    (hrun : (denoteSpine (primeirBuiltins T.p) fuel te.erase).run env =
      (.val (.int (r.val : Int)), env')) :
    arrLimbs (rp.denote (abiValN n sa (fieldCtx T.p xs))) n 0 = T.enc r := by
  unfold fieldFront at hf
  split at hf
  · rename_i hsp
    obtain ⟨hsp, hwf⟩ := hsp
    obtain ⟨o, ho, hf⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨c, hc, hf⟩ := Option.bind_eq_some_iff.mp hf
    rw [denoteSpine_eq_of_spineLamFree _ _ _ hsp] at hrun
    have hNZ : NeZero T.p := ⟨by have := T.one_lt; omega⟩
    obtain ⟨Wn, hprog, -, hvW⟩ := CatCrypt.Crypto.Hax.ImpToNF.Sound.all_of_whileFree
      (impToNF_sound (primeirBuiltins T.p) fieldSigOf (fieldSigOf_typedCalls T.p)
        (repeatCalls_primeirBuiltins T.p) te.erase none (entryEnv (fieldPs xs)) ho fuel)
      (FrontComplete.whileFree_of_opsNB _ (FrontComplete.impToNF_prog_frontOp _ _ none _ o ho
        hwf))
      (entryEnv_rel (entryVals_of_argsHold xs A hargs)) hrun
    have hp : PDenP (primeirBuiltins T.p) 0 o.prog (intsOf xs A) =
        some (.cons (o.res.lookup Wn) .nil) :=
      hprog 0
    have hd : PDenP (primeirBuiltins T.p) 0 (NFProg.dce o.prog) (intsOf xs A) =
        some (.cons (o.res.lookup Wn) .nil) :=
      @NFProg.denote_dce nfDialect _ _ _ _ (nfDenote (tableOf (primeirBuiltins T.p))) _ _ _
        o.prog 0 _ _ hp
    obtain ⟨z, hz, hzc⟩ := fieldOfNF_sound primeirFieldTable primeirFieldTable_ok
      (primeirFieldTable_agrees T.p) _ (fldRen T.p xs) c hc _ A (sAgree_fldRen xs A) 0 _ hd
    rw [← hvW] at hz
    have hzr : z = (r.val : Int) := (Value.int.inj hz).symm
    subst hzr
    have hr : r = c.denote A := by simpa using hzc
    subst hr
    exact T.route_abi_denote hf sa A (arrFlat_of_argsHold xs A hargs)
  · cases hf

/-- **The field front as a `FrontLegOf`** at the modulus `p` and the parameter names `xs`:
    the extractions `TExpr` with the semantics `fieldRuns p xs`, compiled by `fieldFront` at
    the template `fieldTemplateOf p`, under the export names `nfAbiNames`. Retired: field
    operations reach `compileA` as tagged calls lowered by the field step of the chain
    (`DESIGN.md`, "Field operations in the chain"); no new statement is built on this leg. -/
def fieldLeg (p : Nat) (xs : List String) : FrontLegOf where
  Src := TExpr
  Runs := fieldRuns p xs
  front _ te := (fieldTemplateOf p).bind fun q =>
    (fieldFront q.2 xs te).map fun rp =>
      ⟨arrCtx q.1 (fieldCtx q.2.p xs) ++ [arrTy q.1], arrTy q.1, rp⟩
  names := nfAbiNames
  leg σ te q hf sa v _ hrun := by
    obtain ⟨n, T, hT, rfl, A, r, env, fuel, env', hargs, hrun, arr, harr, rfl⟩ := hrun
    rw [hT, Option.bind_some] at hf
    obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.mp hf
    refine ⟨abiValN n sa (fieldCtx T.p xs), ?_, ?_⟩
    · have h := abiValOf_fieldAbi n sa (fieldCtx T.p xs)
      rwa [fieldCtx_length] at h
    · exact arrVal_eq_of_arrLimbs (harr.trans
        (fieldFront_leg T xs te rp hrp sa A r env fuel env' hargs hrun).symm)

/-- **The compiler theorem for a function over the field `ZMod p`.** For the route program
    `q` of the field front `fieldLeg p xs` on `te`, the straight-line program `c` that
    `ComL.toCom?` reads from it, and a result `(P', bytes)` of the region back half
    `compileRegion` on `NFProg.ofCom c` under the export names `nfAbiNames fname σ`: from
    every entry state `sa` satisfying `σ.Regions`, every value `v` of a source run of `te`
    (`fieldRuns`: at the template `fieldTemplateOf p`, unsaturated at an unsaturated instance
    modulus, Solinas for `p = 2 ^ k - c`, the single-word template at a certified
    single-word prime, and Montgomery otherwise, the operand arrays hold the limbs of the
    elements bound to the parameters `xs`, the reference interpreter with `primeirBuiltins`
    returns the representative of `r`, and `v` is the source value of an array holding the limbs of `r`)
    is matched by a halting run of the machine on the decoded bytes from which `σ` reads back
    `v`. The conclusion is the halting run and the read-back of `haxc_correct_auto`; the
    modulus `p` and the parameters `xs` are parameters. The proof composes the leg of
    `fieldLeg p xs` with `compileRegion_correct_wide` at `NFProg.denote_ofCom`. -/
theorem field_correct_auto (p : Nat) (xs : List String) (te : TExpr) (σ : AbiLayout)
    (fname : String) {q : AnyRouteProg} (hf : (fieldLeg p xs).front σ te = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (P' : Lprog) (bytes : List (BitVec 8))
    (hc : compileRegion σ (nfAbiNames fname σ) (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : fieldRuns p xs σ te sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' v := by
  obtain ⟨V, hV, hv⟩ := (fieldLeg p xs).leg σ te q hf sa v hsep hrun
  have hd : q.2.2.denote V = c.denote V := by
    unfold RouteProg.denote
    rw [ComL.eq_comToComL_of_toCom? hcq]
    exact NFProgToComL.comToComL_denote c V
  rw [hv, hd]
  have hn : narrowArrB q.2.1 = false := by
    obtain ⟨T, -, hf'⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨rp, -, rfl⟩ := Option.map_eq_some_iff.mp hf'
    rfl
  obtain ⟨prog, sa', hdec, hh, hR, -⟩ :=
    compileRegion_correct_wide hc sa V hV hsep 0 (NFProg.denote_ofCom c 0 V) hn
  exact ⟨prog, sa', hdec, hh, hR⟩

/-! ## 5. Test moduli

The prime `1000003` (one limb, Montgomery), the prime `2 ^ 127 - 1` (two limbs, Solinas with
`k = 127`, `c = 1`) and the prime `2 ^ 128 - 159` (two limbs, Solinas with `k = 128`,
`c = 159`), with the per-operation callers `fe_add`, `fe_sub`, `fe_mul` (parameters `a`, `b`)
and `fe_sq`, `fe_neg` (parameter `a`) of the `primeir_hax` crate. -/

/-- A one-limb test modulus. -/
abbrev testP1 : Nat := 1000003

/-- A two-limb test modulus of the form `2 ^ k - 1`. -/
abbrev testP2 : Nat := 2 ^ 127 - 1

/-- A two-limb test modulus of the form `2 ^ k - c` with `k` a multiple of `64`. -/
abbrev testP3 : Nat := 2 ^ 128 - 159

theorem limbParamsOf_testP1 : (limbParamsOf testP1).isSome = true := by decide

theorem limbParamsOf_testP2 : (limbParamsOf testP2).isSome = true := by decide

theorem solinasParamsOf_testP1 : solinasParamsOf testP1 = none := by decide

theorem solinasParamsOf_testP2 : (solinasParamsOf testP2).isSome = true := by decide

theorem solinasParamsOf_testP3 : (solinasParamsOf testP3).isSome = true := by decide

/-- The field front accepts the three binary callers and the two unary callers at the
    one-limb test modulus. -/
theorem fieldFront_accepts_testP1 :
    [Primeir.fe_add_texpr, Primeir.fe_sub_texpr, Primeir.fe_mul_texpr].all
      (fun te => ((fieldLeg testP1 ["a", "b"]).front (fieldAbi2 1) te).isSome) = true ∧
    [Primeir.fe_sq_texpr, Primeir.fe_neg_texpr].all
      (fun te => ((fieldLeg testP1 ["a"]).front (fieldAbi 1 1) te).isSome) = true := by
  native_decide

/-- The field front accepts the three binary callers and the two unary callers at the
    test modulus `2 ^ 127 - 1`. -/
theorem fieldFront_accepts_testP2 :
    [Primeir.fe_add_texpr, Primeir.fe_sub_texpr, Primeir.fe_mul_texpr].all
      (fun te => ((fieldLeg testP2 ["a", "b"]).front (fieldAbi2 2) te).isSome) = true ∧
    [Primeir.fe_sq_texpr, Primeir.fe_neg_texpr].all
      (fun te => ((fieldLeg testP2 ["a"]).front (fieldAbi 1 2) te).isSome) = true := by
  native_decide

/-- The field front accepts the three binary callers and the two unary callers at the
    test modulus `2 ^ 128 - 159`. -/
theorem fieldFront_accepts_testP3 :
    [Primeir.fe_add_texpr, Primeir.fe_sub_texpr, Primeir.fe_mul_texpr].all
      (fun te => ((fieldLeg testP3 ["a", "b"]).front (fieldAbi2 2) te).isSome) = true ∧
    [Primeir.fe_sq_texpr, Primeir.fe_neg_texpr].all
      (fun te => ((fieldLeg testP3 ["a"]).front (fieldAbi 1 2) te).isSome) = true := by
  native_decide

/-- `field_correct_auto` for the caller `fe_mul` at the one-limb test modulus. -/
theorem fe_mul_correct_testP1 (fname : String) (P' : Lprog) (bytes : List (BitVec 8))
    {q : AnyRouteProg}
    (hf : (fieldLeg testP1 ["a", "b"]).front (fieldAbi2 1) Primeir.fe_mul_texpr = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (hc : compileRegion (fieldAbi2 1) (nfAbiNames fname (fieldAbi2 1)) (NFProg.ofCom c) =
      some (P', bytes))
    (sa : AState) (hsep : (fieldAbi2 1).Regions sa) (v : Value)
    (hrun : fieldRuns testP1 ["a", "b"] (fieldAbi2 1) Primeir.fe_mul_texpr sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi2 1).ResultOf sa sa' v :=
  field_correct_auto testP1 _ _ _ fname hf hcq P' bytes hc sa hsep v hrun

/-- `field_correct_auto` for the caller `fe_mul` at the test modulus `2 ^ 127 - 1`. -/
theorem fe_mul_correct_testP2 (fname : String) (P' : Lprog) (bytes : List (BitVec 8))
    {q : AnyRouteProg}
    (hf : (fieldLeg testP2 ["a", "b"]).front (fieldAbi2 2) Primeir.fe_mul_texpr = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (hc : compileRegion (fieldAbi2 2) (nfAbiNames fname (fieldAbi2 2)) (NFProg.ofCom c) =
      some (P', bytes))
    (sa : AState) (hsep : (fieldAbi2 2).Regions sa) (v : Value)
    (hrun : fieldRuns testP2 ["a", "b"] (fieldAbi2 2) Primeir.fe_mul_texpr sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi2 2).ResultOf sa sa' v :=
  field_correct_auto testP2 _ _ _ fname hf hcq P' bytes hc sa hsep v hrun

/-- `field_correct_auto` for the caller `fe_mul` at the test modulus `2 ^ 128 - 159`. -/
theorem fe_mul_correct_testP3 (fname : String) (P' : Lprog) (bytes : List (BitVec 8))
    {q : AnyRouteProg}
    (hf : (fieldLeg testP3 ["a", "b"]).front (fieldAbi2 2) Primeir.fe_mul_texpr = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (hc : compileRegion (fieldAbi2 2) (nfAbiNames fname (fieldAbi2 2)) (NFProg.ofCom c) =
      some (P', bytes))
    (sa : AState) (hsep : (fieldAbi2 2).Regions sa) (v : Value)
    (hrun : fieldRuns testP3 ["a", "b"] (fieldAbi2 2) Primeir.fe_mul_texpr sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi2 2).ResultOf sa sa' v :=
  field_correct_auto testP3 _ _ _ fname hf hcq P' bytes hc sa hsep v hrun

/-- `field_correct_auto` for the unary caller `fe_sq` at the one-limb test modulus. -/
theorem fe_sq_correct_testP1 (fname : String) (P' : Lprog) (bytes : List (BitVec 8))
    {q : AnyRouteProg}
    (hf : (fieldLeg testP1 ["a"]).front (fieldAbi 1 1) Primeir.fe_sq_texpr = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (hc : compileRegion (fieldAbi 1 1) (nfAbiNames fname (fieldAbi 1 1)) (NFProg.ofCom c) =
      some (P', bytes))
    (sa : AState) (hsep : (fieldAbi 1 1).Regions sa) (v : Value)
    (hrun : fieldRuns testP1 ["a"] (fieldAbi 1 1) Primeir.fe_sq_texpr sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi 1 1).ResultOf sa sa' v :=
  field_correct_auto testP1 _ _ _ fname hf hcq P' bytes hc sa hsep v hrun

/-- `field_correct_auto` for the unary caller `fe_neg` at the one-limb test modulus. -/
theorem fe_neg_correct_testP1 (fname : String) (P' : Lprog) (bytes : List (BitVec 8))
    {q : AnyRouteProg}
    (hf : (fieldLeg testP1 ["a"]).front (fieldAbi 1 1) Primeir.fe_neg_texpr = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (hc : compileRegion (fieldAbi 1 1) (nfAbiNames fname (fieldAbi 1 1)) (NFProg.ofCom c) =
      some (P', bytes))
    (sa : AState) (hsep : (fieldAbi 1 1).Regions sa) (v : Value)
    (hrun : fieldRuns testP1 ["a"] (fieldAbi 1 1) Primeir.fe_neg_texpr sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi 1 1).ResultOf sa sa' v :=
  field_correct_auto testP1 _ _ _ fname hf hcq P' bytes hc sa hsep v hrun

/-- `field_correct_auto` for the unary caller `fe_sq` at the test modulus `2 ^ 127 - 1`. -/
theorem fe_sq_correct_testP2 (fname : String) (P' : Lprog) (bytes : List (BitVec 8))
    {q : AnyRouteProg}
    (hf : (fieldLeg testP2 ["a"]).front (fieldAbi 1 2) Primeir.fe_sq_texpr = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (hc : compileRegion (fieldAbi 1 2) (nfAbiNames fname (fieldAbi 1 2)) (NFProg.ofCom c) =
      some (P', bytes))
    (sa : AState) (hsep : (fieldAbi 1 2).Regions sa) (v : Value)
    (hrun : fieldRuns testP2 ["a"] (fieldAbi 1 2) Primeir.fe_sq_texpr sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi 1 2).ResultOf sa sa' v :=
  field_correct_auto testP2 _ _ _ fname hf hcq P' bytes hc sa hsep v hrun

/-- `field_correct_auto` for the unary caller `fe_neg` at the test modulus `2 ^ 127 - 1`. -/
theorem fe_neg_correct_testP2 (fname : String) (P' : Lprog) (bytes : List (BitVec 8))
    {q : AnyRouteProg}
    (hf : (fieldLeg testP2 ["a"]).front (fieldAbi 1 2) Primeir.fe_neg_texpr = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (hc : compileRegion (fieldAbi 1 2) (nfAbiNames fname (fieldAbi 1 2)) (NFProg.ofCom c) =
      some (P', bytes))
    (sa : AState) (hsep : (fieldAbi 1 2).Regions sa) (v : Value)
    (hrun : fieldRuns testP2 ["a"] (fieldAbi 1 2) Primeir.fe_neg_texpr sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi 1 2).ResultOf sa sa' v :=
  field_correct_auto testP2 _ _ _ fname hf hcq P' bytes hc sa hsep v hrun

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect
