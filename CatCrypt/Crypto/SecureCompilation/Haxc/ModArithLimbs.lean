/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate
public import CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplateMont
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRaise
public import CatCrypt.Crypto.SecureCompilation.VIR.NFMapLeakBlockEv

/-!
# The limb templates of the field heads, and the chain stage from `mod_arith` to Jasmin

The template blocks that `fieldBody` gives the tagged field heads are instances of the class
`Algebraic.ModArithLimbTemplate p .canon`: the narrow single-word representation
`narrowFieldOf p` through `ModArithLimbTemplate.ofSingleWord`, a wide template
`wideTemplateOf p` on arrays of `fieldLimbs p` words (`ofWide`), and the one-limb
Montgomery record `montWordOf p` on a register (`ofMontWord`). The chooser
`modArithTemplateOf p r` returns, at `canon`, the first of these in the order of
`fieldBody`, and at a Montgomery representation `mont k` the template `ofCanonMont` of the
template at `canon`, which exists at every odd modulus `1 < p < 2^64`
(`modArithTemplateOf_cover_mont`). For every tagged head that
`fieldBody` has a body for, the chosen template exists, the signature of the body is that of
the template, and the body is the template body (`modArithTemplateOf_cover`,
`modArithTemplateOf_agrees`).

`modArithLimbsJ : PartialBlockLowering jasMod jasminDialect` keeps every operation of
`jasminDialect` and carries a residue of `ZMod p` in the carrier of the chosen template at
`(p, canon)`. Addition, subtraction, multiplication and negation become the template bodies
of the methods `add`, `sub`, `mul` and `neg` on the carriers of the arguments, an addition
or a multiplication of a variable with itself becomes the body of `double` or `square` on its
carrier, a copy is the argument, Montgomery multiplication `montMul p c` becomes
`ofCanonMontMul` at the literal `c` (`montBlock?`), and the word casts become the cast blocks
of the template; every other operation of `modArithDialect`, and every operation at a modulus without a
template, is refused.
`modArithLimbsStep` is `NFProgPasses.mapStep` along `modArithLimbsJ`, with the certificate
`modArithLimbsCert`. A block of a field operation or of a cast emits the same events at every
two valuations at leakage parameters with no variable-time operation, and an operation of
`jasminDialect` emits its own events, so two runs whose events agree give two runs of the
lowered program whose events agree (`modArithLimbsStep_leakRunC`).

The stage is the third stage of the field dialect step `FieldDialectStep.fieldDialectStep`,
the seventh step of `extChainCore`.

## Main definitions

* `ofWide`, `ofMontWord`, `narrowTmpl`: the templates of the field heads.
* `modArithTemplateOf`: the template of a modulus and a representation.
* `mapTy`, `transTy`, `mapVal`, `modArithLimbsJ`: the lowering and its transports.
* `modArithLimbsStep`, `modArithLimbsCert`: the chain stage and its certificate.

## Main results

* `modArithTemplateOf_cover`, `modArithTemplateOf_agrees`: the chosen template gives the
  bodies of `fieldBody`.
* `modArithLimbsJ_block_fwd`: a successful source expression has a successful block with the
  transported value.
* `modArithLimbsStep_leakRunC`: equal source events give equal events after the step.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ModArithLimbs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvToHom)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Algebraic (ModArithLimbTemplate)
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField canonEnc w64)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy)
open Ctxt (Var Valuation)
open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldLimbs)

/-! ## 1. The templates of the field heads -/

section Templates

/-- The template block of a method of a single-word representation is the embedding of its
    body. -/
theorem fieldBlockOf_eq {p : Nat} (F : SingleWordField p) (m : FieldMethod) :
    fieldBlockOf F m = NFProg.ofCom (singleBody F m) := by
  cases m <;> rfl

/-- The bodies of the narrow representation of a modulus have fixed events at leakage
    parameters with no variable-time operation. -/
theorem narrow_fixed {p : Nat} {F : SingleWordField p} (hn : narrowFieldOf p = some F)
    (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (m : FieldMethod) :
    LeakFixed (jLeakModel Pj) (singleBody F m) := by
  have hA : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet := fun bop w => by
    simp [jLeakModel, Dialects.JasminComLLeak.jKind, hV]
  have hK : ∀ w n, (jLeakModel Pj).kind (.regConst w n) = .quiet := fun w n => by
    simp [jLeakModel, Dialects.JasminComLLeak.jKind, hV]
  have key : ∀ V, ComLevelCheck.Com.ctLeak (jLeakModel Pj) (singleBody F m) V = [] := by
    intro V
    unfold narrowFieldOf at hn
    split at hn
    · rename_i k hk
      cases hn
      have hc := FieldRouteNarrow.narrowCert_of_narrowFoldsOf hk
      have fin : ∀ {Γ' : Ctxt jasminDialect} (c : Com jasminDialect Γ' w64) (V' : Valuation Γ'),
          (Dialects.NFLeak.NFProg.leakRunM (jLeakModel Pj) 0 (NFProg.ofCom c) V').map
            Prod.snd = some [] → ComLevelCheck.Com.ctLeak (jLeakModel Pj) c V' = [] := by
        intro Γ' c V' h
        rw [← Dialects.NFLeak.NFProg.leakRunMC_empty, FieldWideLeak.leakRunMC_ofCom,
          Option.map_some] at h
        exact Option.some.inj h
      cases m
      · exact fin _ V (fieldBlockOf_quiet (jLeakModel Pj) hA hK hc .add 0 V)
      · exact fin _ V (fieldBlockOf_quiet (jLeakModel Pj) hA hK hc .sub 0 V)
      · exact fin _ V (fieldBlockOf_quiet (jLeakModel Pj) hA hK hc .mul 0 V)
      · exact fin _ V (fieldBlockOf_quiet (jLeakModel Pj) hA hK hc .neg 0 V)
      · exact fin _ V (fieldBlockOf_quiet (jLeakModel Pj) hA hK hc .square 0 V)
      · exact fin _ V (fieldBlockOf_quiet (jLeakModel Pj) hA hK hc .double 0 V)
    · cases hn
  intro V₁ V₂
  rw [key, key]

/-- **The template of the narrow representation** `F = narrowFieldOf p`. -/
@[instance_reducible] def narrowTmpl (p : Nat) (F : SingleWordField p)
    (hn : narrowFieldOf p = some F) : ModArithLimbTemplate p .canon :=
  have hs := narrowFieldOf_spec hn
  haveI : NeZero p := ⟨by omega⟩
  ofSingleWord F (by omega) hs.2.2 (narrow_fixed hn)

/-- The body of a method at a wide template: the template call of the operation of the
    method on the parameters. -/
def wideLimbBody {p : Nat} (W : WideTemplate p (fieldLimbs p)) :
    (m : FieldMethod) → Com jasminDialect (limbSig (arrTy (fieldLimbs p)) m)
      (arrTy (fieldLimbs p))
  | .add => templateCall W.P (fieldOpOf .add p) (wideArgs p .add) (wideFirst .add)
  | .sub => templateCall W.P (fieldOpOf .sub p) (wideArgs p .sub) (wideFirst .sub)
  | .mul => templateCall W.P (fieldOpOf .mul p) (wideArgs p .mul) (wideFirst .mul)
  | .neg => templateCall W.P (fieldOpOf .neg p) (wideArgs p .neg) (wideFirst .neg)
  | .square => templateCall W.P (fieldOpOf .square p) (wideArgs p .square) (wideFirst .square)
  | .double => templateCall W.P (fieldOpOf .double p) (wideArgs p .double) (wideFirst .double)

/-- The body of a call at a wide template is the embedding of the template body. -/
theorem wideBlockOf_eq {p : Nat} (W : WideTemplate p (fieldLimbs p)) (m : FieldMethod) :
    wideBlockOf W m = NFProg.ofCom (wideLimbBody W m) := by
  cases m <;> rfl

/-- A modulus with a wide template is at least `2 ^ 64`. -/
theorem le_of_wideTemplateOf {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    (hw : wideTemplateOf p = some W) : 2 ^ 64 ≤ p := by
  by_contra h
  rw [wideTemplateOf_of_lt (by omega)] at hw
  cases hw

/-- The value of a method at `canon` is `fieldVal` of the canonical representatives. -/
theorem val_methodVal {p : Nat} [NeZero p] (m : FieldMethod) (x y : ZMod p) :
    (methodVal p .canon m x y).val = _root_.Hax.FieldTag.fieldVal m p x.val y.val := by
  have h := NFMontify.fieldVal_cast m x y
  have hm : methodVal p .canon m x y = NFMontify.fieldOp m x y := by cases m <;> rfl
  rw [hm, ← h, ZMod.val_natCast,
    Nat.mod_eq_of_lt (_root_.Hax.FieldTag.fieldVal_lt m (Nat.pos_of_neZero p) _ _)]

/-- **The body of a method at a wide template returns the canonical limbs of the value.** -/
theorem wideLimbBody_denote {p : Nat} (W : WideTemplate p (fieldLimbs p))
    (hw : wideTemplateOf p = some W) (m : FieldMethod) (x y : ZMod p) :
    (wideLimbBody W m).denote (limbVals m (FieldChainDialect.wordsOf 64 (fieldLimbs p) x.val)
        (FieldChainDialect.wordsOf 64 (fieldLimbs p) y.val)) =
      FieldChainDialect.wordsOf 64 (fieldLimbs p) (methodVal p .canon m x y).val := by
  have hp := le_of_wideTemplateOf hw
  have : NeZero p := ⟨by omega⟩
  have hdec : ∀ z : ZMod p, _root_.Hax.FieldTag.limbsDec
      (FieldWideInline.wordsOf (FieldChainDialect.wordsOf 64 (fieldLimbs p) z.val)) =
        some z.val := by
    intro z
    rw [FieldRaise.wordsOf_wordsOf, _root_.Hax.FieldTag.limbsDec_limbsOf,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt z) (_root_.Hax.FieldTag.le_pow_fieldLimbs p))]
  obtain ⟨y', hy', hw'⟩ := wideBlock_denoteAt W (m := m)
    (limbVals m (FieldChainDialect.wordsOf 64 (fieldLimbs p) x.val)
      (FieldChainDialect.wordsOf 64 (fieldLimbs p) y.val)) (a := x.val) (b := y.val)
    (by cases m <;> exact hdec x) (ZMod.val_lt x)
    (fun h => by
      cases m <;> first | exact ⟨hdec y, ZMod.val_lt y⟩ | exact absurd h (by decide))
    CallEnv.empty 0
  have e : NFProg.denoteAt CallEnv.empty 0 (wideBlockOf W m)
      (limbVals m (FieldChainDialect.wordsOf 64 (fieldLimbs p) x.val)
        (FieldChainDialect.wordsOf 64 (fieldLimbs p) y.val)) =
      some (.cons ((wideLimbBody W m).denote
        (limbVals m (FieldChainDialect.wordsOf 64 (fieldLimbs p) x.val)
          (FieldChainDialect.wordsOf 64 (fieldLimbs p) y.val))) .nil) := by
    unfold NFProg.denoteAt
    let _ : CallDenote jasminDialect := ⟨CallEnv.empty⟩
    cases m <;> exact NFProg.denote_ofCom _ 0 _
  rw [e] at hy'
  have hy := (HVector.cons.inj (Option.some.inj hy')).1
  have hd := FieldWideDecl.dec_wordsOf y'
  rw [hw'] at hd
  rw [hy, FieldRaise.dec_limbsOf hd, val_methodVal]

/-- The cast block of an array of `k` words into itself: the argument, at `w = 64` and
    `n = k`. -/
def arrOfWords (k w n : Nat) : Option (Com jasminDialect [.stackArr w n] (.stackArr 64 k)) :=
  if h : JasminTy.stackArr w n = .stackArr 64 k then
    some (cast (congrArg (Com jasminDialect [.stackArr w n]) h) (.ret .here))
  else none

/-- The cast block of an array of `k` words to an array of `n` words of `w` bits: the
    argument, at `w = 64` and `n = k`. -/
def arrToWords (k w n : Nat) : Option (Com jasminDialect [.stackArr 64 k] (.stackArr w n)) :=
  if h : JasminTy.stackArr 64 k = .stackArr w n then
    some (cast (congrArg (Com jasminDialect [.stackArr 64 k]) h) (.ret .here))
  else none

/-- **The template of a wide template** `W = wideTemplateOf p`: the residue carried by the
    array of its `fieldLimbs p` canonical limbs, the template calls as bodies, and the
    argument as the cast block at `fieldLimbs p` words of `64` bits. -/
@[instance_reducible] def ofWide {p : Nat} (W : WideTemplate p (fieldLimbs p))
    (hw : wideTemplateOf p = some W) : ModArithLimbTemplate p .canon where
  limbs := fieldLimbs p
  ty := arrTy (fieldLimbs p)
  enc x := FieldChainDialect.wordsOf 64 (fieldLimbs p) x.val
  body := wideLimbBody W
  body_denote := wideLimbBody_denote W hw
  body_fixed Pj hV m := by
    cases m <;> exact leakFixed_rename _ _ (fun V₁ V₂ =>
      FieldWideLeak.wideTemplateOf_evFix hV hw _ (arithOpB_fieldOpOf _ p) V₁ V₂)
  ofWords := arrOfWords (fieldLimbs p)
  ofWords_denote w n c hc A y hy := by
    unfold arrOfWords at hc
    split at hc
    · rename_i h
      cases hc
      injection h with h1 h2
      subst h1 h2
      rw [cast_eq]
      have h' : wordsVal (fieldLimbs p) A < p ∧
          ((wordsVal (fieldLimbs p) A : Nat) : ZMod p) = y := by
        simpa [fromWordsMF] using hy
      obtain ⟨hlt, rfl⟩ := h'
      show A = _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, wordsOf_wordsVal]
    · cases hc
  ofWords_fixed Pj _ w n c hc := by
    unfold arrOfWords at hc
    split at hc
    · rename_i h
      cases hc
      injection h with h1 h2
      subst h1 h2
      rw [cast_eq]
      intro V₁ V₂
      rfl
    · cases hc
  toWords := arrToWords (fieldLimbs p)
  toWords_denote w n c hc y := by
    unfold arrToWords at hc
    split at hc
    · rename_i h
      cases hc
      injection h with h1 h2
      subst h1 h2
      rw [cast_eq]
      rfl
    · cases hc
  toWords_fixed Pj _ w n c hc := by
    unfold arrToWords at hc
    split at hc
    · rename_i h
      cases hc
      injection h with h1 h2
      subst h1 h2
      rw [cast_eq]
      intro V₁ V₂
      rfl
    · cases hc

/-- The body of a method over one limb at a one-limb Montgomery record: the register block
    of the canonical Montgomery template on the parameters. -/
def montLimbBody (P : LimbParams 1) : (m : FieldMethod) → Com jasminDialect (limbSig w64 m) w64
  | .add => Com.rename (hvToHom (wordArgs P.p .add))
      (canonRegBlock P (fieldOpOf .add P.p)).toComHead
  | .sub => Com.rename (hvToHom (wordArgs P.p .sub))
      (canonRegBlock P (fieldOpOf .sub P.p)).toComHead
  | .mul => Com.rename (hvToHom (wordArgs P.p .mul))
      (canonRegBlock P (fieldOpOf .mul P.p)).toComHead
  | .neg => Com.rename (hvToHom (wordArgs P.p .neg))
      (canonRegBlock P (fieldOpOf .neg P.p)).toComHead
  | .square => Com.rename (hvToHom (wordArgs P.p .square))
      (canonRegBlock P (fieldOpOf .square P.p)).toComHead
  | .double => Com.rename (hvToHom (wordArgs P.p .double))
      (canonRegBlock P (fieldOpOf .double P.p)).toComHead

/-- The body of a call over one limb is the embedding of the template body. -/
theorem montWordBlockOf_eq (P : LimbParams 1) (m : FieldMethod) :
    montWordBlockOf P m = NFProg.ofCom (montLimbBody P m) := by
  cases m <;> rfl

/-- **The template of a one-limb Montgomery record** `P` at its modulus `p`: the canonical
    word in a register, the register blocks of the canonical Montgomery template as bodies,
    and the load and the store at one 64-bit word as cast blocks. -/
@[instance_reducible] def ofMontWord (P : LimbParams 1) {p : Nat} (hp : P.p = p) :
    ModArithLimbTemplate p .canon where
  limbs := 1
  ty := w64
  enc := canonEnc p
  body := montLimbBody P
  body_denote m x y := by
    subst hp
    have hp64 : P.p < 2 ^ 64 := by simpa using P.p_lt
    have : NeZero P.p := ⟨by have := P.one_lt; omega⟩
    have hx := Algebraic.FieldWord.canonEnc_toNat hp64.le x
    have hy := Algebraic.FieldWord.canonEnc_toNat hp64.le y
    have h := montWordBlock_denoteAt P (m := m) (limbVals m (canonEnc P.p x) (canonEnc P.p y))
      (by cases m <;> simp [wordNats, limbVals, hx, ZMod.val_lt])
      (fun hb => by
        cases m <;> first
          | exact absurd hb (by decide)
          | simp [wordNats, limbVals, hy, ZMod.val_lt]) CallEnv.empty 0
    have e : NFProg.denoteAt CallEnv.empty 0 (montWordBlockOf P m)
        (limbVals m (canonEnc P.p x) (canonEnc P.p y)) =
        some (.cons ((montLimbBody P m).denote
          (limbVals m (canonEnc P.p x) (canonEnc P.p y))) .nil) := by
      unfold NFProg.denoteAt
      let _ : CallDenote jasminDialect := ⟨CallEnv.empty⟩
      cases m <;> exact NFProg.denote_ofCom _ 0 _
    rw [e] at h
    rw [(HVector.cons.inj (Option.some.inj h)).1]
    have hv := val_methodVal m x y
    cases m <;> simp only [wordNats, limbVals, hx, hy] <;>
      exact (congrArg (BitVec.ofNat 64) hv).symm
  body_fixed Pj hV m := by
    cases m <;> exact leakFixed_rename _ _ (fun V₁ V₂ => by
      rw [FieldWideLeak.ctLeak_toComHead, FieldWideLeak.ctLeak_toComHead]
      exact FieldWideLeak.canonRegBlock_evFix P hV _ (arithOpB_fieldOpOf _ P.p) V₁ V₂)
  ofWords := singleOfWords
  ofWords_denote w n c hc A y hy := by
    subst hp
    have hp64 : P.p < 2 ^ 64 := by simpa using P.p_lt
    have : NeZero P.p := ⟨by have := P.one_lt; omega⟩
    unfold singleOfWords at hc
    split at hc
    · cases hc
      exact singleLoadBlk_denote hp64.le A y hy
    · cases hc
  ofWords_fixed Pj _ w n c hc := by
    unfold singleOfWords at hc
    split at hc
    · cases hc
      exact singleLoadBlk_fixed Pj
    · cases hc
  toWords := singleToWords
  toWords_denote w n c hc y := by
    unfold singleToWords at hc
    split at hc
    · cases hc
      exact singleStoreBlk_denote y
    · cases hc
  toWords_fixed Pj hV w n c hc := by
    unfold singleToWords at hc
    split at hc
    · cases hc
      exact singleStoreBlk_fixed Pj hV
    · cases hc

end Templates

/-! ## 2. The chooser -/

/-- The limb template of the modulus `p` at `canon`: the template of the narrow
    representation `narrowFieldOf p`, else of the wide template `wideTemplateOf p`, else of
    the one-limb Montgomery record `montWordOf p`. -/
def canonTemplateOf (p : Nat) : Option (ModArithLimbTemplate p .canon) :=
  match hn : narrowFieldOf p with
  | some F => some (narrowTmpl p F hn)
  | none =>
      match hw : wideTemplateOf p with
      | some W => some (ofWide W hw)
      | none =>
          match hm : montWordOf p with
          | some P => some (ofMontWord P (montWordOf_p hm))
          | none => none

/-- **The limb template of the modulus `p` at the representation `r`**: at `canon`, the
    template of the narrow representation `narrowFieldOf p`, else of the wide template
    `wideTemplateOf p`, else of the one-limb Montgomery record `montWordOf p`, the order in
    which `fieldBody` chooses the body of a tagged head; at `mont k`, `ofCanonMont` of the
    template at `canon` when it has the cast block from its `64`-bit words, `p` is odd and
    `p ≤ 2 ^ (64 * T.limbs)`. -/
def modArithTemplateOf (p : Nat) : (r : FieldRepr) → Option (ModArithLimbTemplate p r)
  | .canon => canonTemplateOf p
  | .mont k => (canonTemplateOf p).bind fun T =>
      if h : (T.ofWords 64 T.limbs).isSome = true ∧ Odd p ∧ p ≤ 2 ^ (64 * T.limbs) then
        some (ofCanonMont T k h.1 h.2.1 h.2.2)
      else none

/-- **Every odd modulus `1 < p < 2^64` has a template at `canon` with the cast block from
    its `64`-bit words**, and the modulus fits in its limbs: the narrow template, else the
    one-limb Montgomery record (no wide template is below `2^64`). -/
theorem canonTemplateOf_mont {p : Nat} (h1 : 1 < p) (hodd : p % 2 = 1) (hp : p < 2 ^ 64) :
    ∃ T, canonTemplateOf p = some T ∧ (T.ofWords 64 T.limbs).isSome = true ∧
      p ≤ 2 ^ (64 * T.limbs) := by
  have hle : p ≤ 2 ^ (64 * 1) := by omega
  unfold canonTemplateOf
  split
  · exact ⟨_, rfl, rfl, hle⟩
  · split
    · rename_i W hw
      have := le_of_wideTemplateOf hw
      omega
    · split
      · exact ⟨_, rfl, rfl, hle⟩
      · rename_i hm
        have := FieldWideInline.montWordOf_isSome h1 hodd hp
        rw [hm] at this
        cases this

/-- **Every odd modulus `1 < p < 2^64` has a template at every Montgomery representation**
    `mont k`: `ofCanonMont` of its template at `canon` (`canonTemplateOf_mont`). -/
theorem modArithTemplateOf_cover_mont {p : Nat} (k : Nat) (h1 : 1 < p) (hodd : p % 2 = 1)
    (hp : p < 2 ^ 64) : (modArithTemplateOf p (.mont k)).isSome = true := by
  obtain ⟨T, hT, hw, hpw⟩ := canonTemplateOf_mont h1 hodd hp
  have hodd' : Odd p := Nat.odd_iff.mpr hodd
  simp only [modArithTemplateOf, hT, Option.bind_some]
  rw [dite_eq_left ⟨hw, hodd', hpw⟩]
  rfl

/-- **Every tagged head with a body has a chosen template** at the signature of the body:
    when `fieldBody f as rs` returns a body for a head of the method `m` at the modulus `p`,
    the template of `(p, canon)` exists, `as` is the signature of `m` on its carriers and
    `rs` is its carrier. -/
theorem modArithTemplateOf_cover {f : String} {m : FieldMethod} {p : Nat}
    (ht : fieldTag? f = some (m, p)) {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : fieldBody f as rs = some b) :
    ∃ T, modArithTemplateOf p .canon = some T ∧ as = limbSig T.ty m ∧ rs = [T.ty] := by
  change ∃ T, canonTemplateOf p = some T ∧ _
  unfold fieldBody at hb
  rw [ht] at hb
  simp only at hb
  unfold canonTemplateOf
  split
  · rename_i F hn
    rw [hn] at hb
    simp only at hb
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨_, rfl, by cases m <;> rfl, rfl⟩
    · cases hb
  · rename_i hn
    rw [hn] at hb
    simp only [FieldWideDecl.wideBody, ht] at hb
    split
    · rename_i W hw
      rw [hw] at hb
      simp only at hb
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨_, rfl, by cases m <;> rfl, rfl⟩
      · cases hb
    · rename_i hw
      rw [hw] at hb
      simp only at hb
      split
      · rename_i P hm
        rw [hm] at hb
        simp only at hb
        split at hb
        · rename_i hs
          obtain ⟨rfl, rfl⟩ := hs
          exact ⟨_, rfl, by cases m <;> rfl, rfl⟩
        · cases hb
      · rename_i hm
        rw [hm] at hb
        cases hb

/-- **The chosen template gives the bodies of `fieldBody`.** For a tagged head of the method
    `m` at the modulus `p` and the template `T` of `(p, canon)`, `fieldBody` gives the head,
    at the signature of `m` on the carriers of `T`, the embedding of the body of `m` in
    `T`. -/
theorem modArithTemplateOf_agrees {f : String} {m : FieldMethod} {p : Nat}
    (ht : fieldTag? f = some (m, p)) {T : ModArithLimbTemplate p .canon}
    (hT : modArithTemplateOf p .canon = some T) :
    fieldBody f (limbSig T.ty m) [T.ty] = some (NFProg.ofCom (T.body m)) := by
  change canonTemplateOf p = some T at hT
  unfold canonTemplateOf at hT
  split at hT
  · rename_i F hn
    cases hT
    simp only [fieldBody, ht, hn]
    cases m <;> exact dite_eq_left ⟨rfl, rfl⟩
  · rename_i hn
    split at hT
    · rename_i W hw
      cases hT
      simp only [fieldBody, ht, hn, FieldWideDecl.wideBody, hw]
      cases m <;> exact dite_eq_left ⟨rfl, rfl⟩
    · rename_i hw
      split at hT
      · rename_i P hm
        cases hT
        simp only [fieldBody, ht, hn, FieldWideDecl.wideBody, hw, hm]
        cases m <;> exact dite_eq_left ⟨rfl, rfl⟩
      · cases hT

/-! ## 3. The lowering -/

/-- The carrier type of a residue under an optional template: the carrier of the template,
    and the 64-bit register without one. -/
def optTy {p : Nat} : Option (ModArithLimbTemplate p .canon) → JasminTy
  | some T => T.ty
  | none => .reg 64

/-- The carrier of a residue under an optional template. -/
def optEnc {p : Nat} : (o : Option (ModArithLimbTemplate p .canon)) → ZMod p → ⟦optTy o⟧
  | some T => T.enc
  | none => fun _ => (0 : BitVec 64)

/-- The type map: a type of `jasminDialect` is kept, `fp p` goes to the carrier of the
    template of `(p, canon)`, a word to the register of its width and a carry to the 1-bit
    register; a residue vector, which no block reads, goes to the 64-bit register. -/
@[reducible] def mapTy : JasminTy ⊕ ModArithTy → JasminTy
  | .inl t => t
  | .inr (.fp p) => optTy (canonTemplateOf p)
  | .inr (.fpVec _ _) => .reg 64
  | .inr (.word w) => .reg w
  | .inr .carry => .reg 1

/-- The variable map along `mapTy`. -/
def mapVar : {Γ : Ctxt jasMod} → {t : jasMod.Ty} → Var Γ t →
    Var (d := jasminDialect) (Γ.map mapTy) (mapTy t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVar v)

/-- The mapped argument variables of an operation of `jasminDialect`. -/
def argsJ {Γ : Ctxt jasMod} : {ts : List JasminTy} →
    HVector (fun t => Var Γ t) (ts.map (Sum.inl (β := ModArithTy))) →
    HVector (fun t => Var (d := jasminDialect) (Γ.map mapTy) t) ts
  | [], _ => .nil
  | _ :: _, .cons v vs => .cons (mapVar v) (argsJ vs)

/-- The body of a method under an optional template, renamed onto the argument
    variables. -/
def bodyBlock? {Δ : Ctxt jasminDialect} {p : Nat} :
    (o : Option (ModArithLimbTemplate p .canon)) → (m : FieldMethod) →
    HVector (fun t => Var Δ t) (limbSig (optTy o) m) → Option (Com jasminDialect Δ (optTy o))
  | some T, m, args => some (Com.rename (hvToHom args) (T.body m))
  | none, _, _ => none

/-- The block of `fromWordsM p w n` under an optional template, on the argument `a`. -/
def ofWordsBlock? {Δ : Ctxt jasminDialect} {p : Nat} :
    (o : Option (ModArithLimbTemplate p .canon)) → (w n : Nat) →
    Var Δ (.stackArr w n) → Option (Com jasminDialect Δ (optTy o))
  | some T, w, n, a => (T.ofWords w n).map fun c => Com.rename (hvToHom (.cons a .nil)) c
  | none, _, _, _ => none

/-- The block of `toWordsM p w n` under an optional template, on the argument `a`. -/
def toWordsBlock? {Δ : Ctxt jasminDialect} {p : Nat} :
    (o : Option (ModArithLimbTemplate p .canon)) → (w n : Nat) →
    Var Δ (optTy o) → Option (Com jasminDialect Δ (.stackArr w n))
  | some T, w, n, a => (T.toWords w n).map fun c => Com.rename (hvToHom (.cons a .nil)) c
  | none, _, _, _ => none

/-- The block of `montMul p c` under an optional template, on the arguments `a` and `b`:
    Montgomery multiplication at the literal `c` (`ofCanonMontMul`), when the template has the
    cast block from its `64`-bit words, `p ≠ 0` and `p ≤ 2 ^ (64 * T.limbs)`. -/
def montBlock? {Δ : Ctxt jasminDialect} {p : Nat} :
    (o : Option (ModArithLimbTemplate p .canon)) → ZMod p → Var Δ (optTy o) →
    Var Δ (optTy o) → Option (Com jasminDialect Δ (optTy o))
  | some T, c, a, b =>
      if h : (T.ofWords 64 T.limbs).isSome = true ∧ p ≠ 0 ∧ p ≤ 2 ^ (64 * T.limbs) then
        some (ofCanonMontMul T h.1 c a b)
      else none
  | none, _, _, _ => none

/-- The block of an operation of `modArithDialect`: the template bodies of `add`, `sub`,
    `mul` and `neg` for `modAdd`, `modSub`, `modMul` and `modNeg`, the bodies of `double` and
    `square` for `modAdd` and `modMul` of a variable with itself, the argument for `modCopy`,
    `montBlock?` for `montMul`,
    and `none` for every other operation. -/
def modBlock? {Γ : Ctxt jasMod} : (o : ModArithOp) →
    HVector (fun t => Var Γ t) ((DialectSignature.sig (d := modArithDialect) o).map
      (Sum.inr (α := JasminTy))) →
    Option (Com jasminDialect (Γ.map mapTy)
      (mapTy (.inr (DialectSignature.ret (d := modArithDialect) o))))
  | .modAdd p, args =>
      if args.head = args.tail.head then
        bodyBlock? (canonTemplateOf p) .double (.cons (mapVar args.head) .nil)
      else bodyBlock? (canonTemplateOf p) .add
        (.cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil))
  | .modSub p, args => bodyBlock? (canonTemplateOf p) .sub
      (.cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil))
  | .modMul p, args =>
      if args.head = args.tail.head then
        bodyBlock? (canonTemplateOf p) .square (.cons (mapVar args.head) .nil)
      else bodyBlock? (canonTemplateOf p) .mul
        (.cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil))
  | .modNeg p, args => bodyBlock? (canonTemplateOf p) .neg (.cons (mapVar args.head) .nil)
  | .modCopy _, args => some (.ret (mapVar args.head))
  | .montMul p c, args => montBlock? (canonTemplateOf p) c (mapVar args.head)
      (mapVar args.tail.head)
  | _, _ => none

/-- The block of a word cast: the cast blocks of the template. -/
def limbCastBlock? {Γ : Ctxt jasMod} : (o : ModWordCastOp) →
    HVector (fun t => Var Γ t) (DialectSignature.sig (d := modWordCastDialect) o) →
    Option (Com jasminDialect (Γ.map mapTy)
      (mapTy (DialectSignature.ret (d := modWordCastDialect) o)))
  | .fromWordsM p w n, args => ofWordsBlock? (canonTemplateOf p) w n (mapVar args.head)
  | .toWordsM p w n, args => toWordsBlock? (canonTemplateOf p) w n (mapVar args.head)

/-- The block of an operation of `jasMod`. -/
def limbOpBlock? {Γ : Ctxt jasMod} : (op : jasMod.Op) →
    HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasMod) op) →
    Option (Com jasminDialect (Γ.map mapTy) (mapTy (DialectSignature.ret (d := jasMod) op)))
  | .inl (.inl o), args => some (.var ⟨o, rfl, argsJ args⟩ (.ret .here))
  | .inl (.inr o), args => modBlock? o args
  | .inr o, args => limbCastBlock? o args

/-- The block of an expression of `jasMod`. -/
def limbLowerBlock? : {Γ : Ctxt jasMod} → {t : jasMod.Ty} → Expr jasMod Γ t →
    Option (Com jasminDialect (Γ.map mapTy) (mapTy t))
  | _, _, ⟨op, rfl, args⟩ => limbOpBlock? op args

/-- **The lowering of `jasMod` to `jasminDialect`.** The partial block lowering that keeps the
    operations of `jasminDialect` and lowers the field operations and the word casts to the
    blocks of the template of `(p, canon)`. -/
def modArithLimbsJ : PartialBlockLowering jasMod jasminDialect where
  mapTy := mapTy
  mapCtx := List.map mapTy
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVar
  lowerExprBlock? := limbLowerBlock?

/-! ## 4. The transports and the leaves -/

/-- The value transport: the identity on a value of `jasminDialect`, on a word and on a
    carry, the carrier `optEnc` of the template on a residue. -/
def transTy : {t : JasminTy ⊕ ModArithTy} → ⟦t⟧ → ⟦mapTy t⟧
  | .inl _, x => x
  | .inr (.fp p), x => optEnc (canonTemplateOf p) x
  | .inr (.fpVec _ _), _ => (0 : BitVec 64)
  | .inr (.word _), x => x
  | .inr .carry, x => x

/-- The valuation transport: `transTy` at every variable. -/
def mapVal {Γ : Ctxt jasMod} (V : Valuation Γ) : Valuation (d := jasminDialect) (Γ.map mapTy) :=
  transArgs mapTy transTy V

/-- A mapped variable reads the transported value. -/
theorem lookup_mapVar_mapVal : ∀ {Γ : Ctxt jasMod} {t : jasMod.Ty} (v : Var Γ t)
    (V : Valuation Γ), (mapVar v).lookup (mapVal V) = transTy (v.lookup V)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVar_mapVal v xs

/-- The variable leaf of `modArithLimbsJ`. -/
theorem modArithLimbsJ_varTransports :
    modArithLimbsJ.VarTransports (fun x => transTy x) (fun V => mapVal V) :=
  fun v V => lookup_mapVar_mapVal v V

/-- The binding leaf of `modArithLimbsJ`. -/
theorem modArithLimbsJ_mapValExtends :
    modArithLimbsJ.MapValExtends (fun x => transTy x) (fun V => mapVal V) :=
  fun _ _ => rfl

/-- The type map of `modArithLimbsJ` keeps the trip-counter type and the bit type. -/
theorem modArithLimbsJ_regionTypes : modArithLimbsJ.RegionTypes := ⟨rfl, rfl⟩

/-- The value transport of `modArithLimbsJ` is the identity on the trip counter and the
    bit. -/
theorem modArithLimbsJ_regionTransports :
    modArithLimbsJ.RegionTransports modArithLimbsJ_regionTypes (fun x => transTy x) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The mapped argument variables of an operation of `jasminDialect` read the argument
    values. -/
theorem lookupArgs_argsJ {Γ : Ctxt jasMod} (V : Valuation Γ) :
    {ts : List JasminTy} →
    (args : HVector (fun t => Var Γ t) (ts.map (Sum.inl (β := ModArithTy)))) →
    Expr.lookupArgs (argsJ args) (mapVal V) =
      unmapInl (e := modArithDialect) (Expr.lookupArgs args V)
  | [], _ => rfl
  | _ :: _, .cons v vs =>
      congrArg₂ HVector.cons (lookup_mapVar_mapVal v V) (lookupArgs_argsJ V vs)

/-- A straight-line program of `jasminDialect` denotes in `Option` its denotation. -/
theorem denoteM_jasmin : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Valuation Γ),
    c.denoteM (M := Option) V = some (c.denote V)
  | _, _, .ret _, _ => rfl
  | _, _, .var e k, V => by
      show e.denoteM (M := Option) V >>= _ = _
      rw [Expr.denoteM_option_eq_some, Option.bind_eq_bind, Option.bind_some,
        denoteM_jasmin k]
      rfl

/-- A body block under an optional template returns the carrier of the value of the method
    on arguments that hold the carriers of `x` and `y`. -/
theorem bodyBlock?_denote {Δ : Ctxt jasminDialect} {p : Nat}
    {o : Option (ModArithLimbTemplate p .canon)} {m : FieldMethod}
    {args : HVector (fun t => Var Δ t) (limbSig (optTy o) m)}
    {blk : Com jasminDialect Δ (optTy o)}
    (hb : bodyBlock? o m args = some blk) (W : Valuation Δ) (x y : ZMod p)
    (ha : MultiReturnCom.lookupVars args W = limbVals m (optEnc o x) (optEnc o y)) :
    blk.denote W = optEnc o (methodVal p .canon m x y) := by
  cases o with
  | none => cases hb
  | some T =>
      cases hb
      exact (FieldDialectBlockDescent.Com.denote_rename (hvToHom args) (T.body m) W).trans
        (by rw [MultiBlockLowering.pullV_hvToHom, ha]; exact T.body_denote m x y)

/-- The block of `fromWordsM` under an optional template returns the carrier of the residue
    the cast reads. -/
theorem ofWordsBlock?_denote {Δ : Ctxt jasminDialect} {p : Nat}
    {o : Option (ModArithLimbTemplate p .canon)} {w n : Nat} {a : Var Δ (.stackArr w n)}
    {blk : Com jasminDialect Δ (optTy o)} (hb : ofWordsBlock? o w n a = some blk)
    (W : Valuation Δ) (y : ZMod p) (hy : fromWordsMF p w n (a.lookup W) = some y) :
    blk.denote W = optEnc o y := by
  cases o with
  | none => cases hb
  | some T =>
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
      exact (FieldDialectBlockDescent.Com.denote_rename _ c W).trans
        (by rw [MultiBlockLowering.pullV_hvToHom]; exact T.ofWords_denote w n c hc _ y hy)

/-- The block of `toWordsM` under an optional template writes the words of the residue
    whose carrier it reads. -/
theorem toWordsBlock?_denote {Δ : Ctxt jasminDialect} {p : Nat}
    {o : Option (ModArithLimbTemplate p .canon)} {w n : Nat} {a : Var Δ (optTy o)}
    {blk : Com jasminDialect Δ (.stackArr w n)} (hb : toWordsBlock? o w n a = some blk)
    (W : Valuation Δ) (y : ZMod p) (hy : a.lookup W = optEnc o y) :
    blk.denote W = toWordsMF p w n y := by
  cases o with
  | none => cases hb
  | some T =>
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
      exact (FieldDialectBlockDescent.Com.denote_rename _ c W).trans
        (by
          rw [MultiBlockLowering.pullV_hvToHom]
          show c.denote (.cons (a.lookup W) .nil) = _
          rw [hy]
          exact T.toWords_denote w n c hc y)

/-- The block of `montMul p c` under an optional template returns the carrier of
    `montMulF c x y` on arguments that hold the carriers of `x` and `y`. -/
theorem montBlock?_denote {Δ : Ctxt jasminDialect} {p : Nat}
    {o : Option (ModArithLimbTemplate p .canon)} {c : ZMod p} {a b : Var Δ (optTy o)}
    {blk : Com jasminDialect Δ (optTy o)} (hb : montBlock? o c a b = some blk)
    (W : Valuation Δ) (x y : ZMod p) (ha : a.lookup W = optEnc o x)
    (hb' : b.lookup W = optEnc o y) :
    blk.denote W = optEnc o (montMulF c x y) := by
  cases o with
  | none => cases hb
  | some T =>
      simp only [montBlock?] at hb
      split at hb
      · rename_i h
        cases hb
        have : NeZero p := ⟨h.2.1⟩
        exact ofCanonMontMul_denote T h.1 h.2.2 c a b W x y ha hb'
      · cases hb

/-- **The block leaf of `modArithLimbsJ`, forward form.** A source expression that
    succeeds with `x` has a block that succeeds, on the transported valuation, with the
    transport of `x`. -/
theorem modArithLimbsJ_block_fwd {Γ : Ctxt jasMod} {t : jasMod.Ty} (e : Expr jasMod Γ t) blk
    (hb : modArithLimbsJ.lowerExprBlock? e = some blk) (V : Valuation Γ) (x : ⟦t⟧)
    (hx : e.denoteM (M := Option) V = some x) :
    blk.denoteM (M := Option) (mapVal V) = some (transTy x) := by
  refine (denoteM_jasmin blk (mapVal V)).trans (congrArg some ?_)
  obtain ⟨op, rfl, args⟩ := e
  rcases op with (o | o) | o
  · cases hb
    have hx' : some (DialectDenote.denote (d := jasminDialect) o
        (unmapInl (e := modArithDialect) (Expr.lookupArgs args V))) = some x := hx
    cases hx'
    show DialectDenote.denote (d := jasminDialect) o (Expr.lookupArgs (argsJ args) (mapVal V)) = _
    rw [lookupArgs_argsJ]
    rfl
  · cases o with
    | modAdd p =>
        match args with
        | .cons a (.cons b .nil) =>
            have hx' : some (modAddF (p := p) (a.lookup V) (b.lookup V)) = some x := hx
            cases hx'
            change modBlock? (Γ := Γ) (.modAdd p) (.cons a (.cons b .nil)) = some blk at hb
            simp only [modBlock?] at hb
            split at hb
            · rename_i hab
              obtain rfl : a = b := hab
              exact bodyBlock?_denote hb (mapVal V) (a.lookup V) (a.lookup V) (by
                show HVector.cons _ .nil = _
                rw [lookup_mapVar_mapVal]
                rfl)
            · exact bodyBlock?_denote hb (mapVal V) (a.lookup V) (b.lookup V) (by
                show HVector.cons _ (HVector.cons _ .nil) = _
                rw [lookup_mapVar_mapVal, lookup_mapVar_mapVal]
                rfl)
    | modSub p =>
        match args with
        | .cons a (.cons b .nil) =>
            have hx' : some (modSubF (p := p) (a.lookup V) (b.lookup V)) = some x := hx
            cases hx'
            exact bodyBlock?_denote hb (mapVal V) (a.lookup V) (b.lookup V) (by
              show HVector.cons _ (HVector.cons _ .nil) = _
              rw [lookup_mapVar_mapVal, lookup_mapVar_mapVal]
              rfl)
    | modMul p =>
        match args with
        | .cons a (.cons b .nil) =>
            have hx' : some (modMulF (p := p) (a.lookup V) (b.lookup V)) = some x := hx
            cases hx'
            change modBlock? (Γ := Γ) (.modMul p) (.cons a (.cons b .nil)) = some blk at hb
            simp only [modBlock?] at hb
            split at hb
            · rename_i hab
              obtain rfl : a = b := hab
              exact bodyBlock?_denote hb (mapVal V) (a.lookup V) (a.lookup V) (by
                show HVector.cons _ .nil = _
                rw [lookup_mapVar_mapVal]
                rfl)
            · exact bodyBlock?_denote hb (mapVal V) (a.lookup V) (b.lookup V) (by
                show HVector.cons _ (HVector.cons _ .nil) = _
                rw [lookup_mapVar_mapVal, lookup_mapVar_mapVal]
                rfl)
    | modNeg p =>
        match args with
        | .cons a .nil =>
            have hx' : some (modNegF (p := p) (a.lookup V)) = some x := hx
            cases hx'
            exact bodyBlock?_denote hb (mapVal V) (a.lookup V) (a.lookup V) (by
              show HVector.cons _ .nil = _
              rw [lookup_mapVar_mapVal]
              rfl)
    | modCopy p =>
        match args with
        | .cons a .nil =>
            cases hb
            have hx' : some (modCopyF (p := p) (a.lookup V)) = some x := hx
            cases hx'
            exact lookup_mapVar_mapVal a V
    | montMul p c =>
        match args with
        | .cons a (.cons b .nil) =>
            have hx' : some (montMulF c (a.lookup V) (b.lookup V)) = some x := hx
            cases hx'
            exact montBlock?_denote hb (mapVal V) (a.lookup V) (b.lookup V)
              (lookup_mapVar_mapVal a V) (lookup_mapVar_mapVal b V)
    | _ => cases hb
  · cases o with
    | fromWordsM p w n =>
        match args with
        | .cons a .nil =>
            exact ofWordsBlock?_denote hb (mapVal V) x (by rw [lookup_mapVar_mapVal]; exact hx)
    | toWordsM p w n =>
        match args with
        | .cons a .nil =>
            have hx' : some (toWordsMF p w n (a.lookup V)) = some x := hx
            cases hx'
            exact toWordsBlock?_denote hb (mapVal V) (a.lookup V) (lookup_mapVar_mapVal a V)

/-! ## 5. The events of the blocks of `modArithLimbsJ` -/

section Events

open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak.NFProg (leakRunMC)

variable (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none)
include hV

/-- A body block under an optional template has fixed events. -/
theorem bodyBlock?_fixed {Δ : Ctxt jasminDialect} {p : Nat}
    {o : Option (ModArithLimbTemplate p .canon)} {m : FieldMethod}
    {args : HVector (fun t => Var Δ t) (limbSig (optTy o) m)}
    {blk : Com jasminDialect Δ (optTy o)} (hb : bodyBlock? o m args = some blk) :
    LeakFixed (jLeakModel Pj) blk := by
  cases o with
  | none => cases hb
  | some T =>
      cases hb
      exact leakFixed_rename _ _ (T.body_fixed Pj hV m)

/-- The block of `fromWordsM` under an optional template has fixed events. -/
theorem ofWordsBlock?_fixed {Δ : Ctxt jasminDialect} {p : Nat}
    {o : Option (ModArithLimbTemplate p .canon)} {w n : Nat} {a : Var Δ (.stackArr w n)}
    {blk : Com jasminDialect Δ (optTy o)} (hb : ofWordsBlock? o w n a = some blk) :
    LeakFixed (jLeakModel Pj) blk := by
  cases o with
  | none => cases hb
  | some T =>
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
      exact leakFixed_rename _ _ (T.ofWords_fixed Pj hV w n c hc)

/-- The block of `toWordsM` under an optional template has fixed events. -/
theorem toWordsBlock?_fixed {Δ : Ctxt jasminDialect} {p : Nat}
    {o : Option (ModArithLimbTemplate p .canon)} {w n : Nat} {a : Var Δ (optTy o)}
    {blk : Com jasminDialect Δ (.stackArr w n)} (hb : toWordsBlock? o w n a = some blk) :
    LeakFixed (jLeakModel Pj) blk := by
  cases o with
  | none => cases hb
  | some T =>
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
      exact leakFixed_rename _ _ (T.toWords_fixed Pj hV w n c hc)

/-- The block of `montMul p c` under an optional template has fixed events. -/
theorem montBlock?_fixed {Δ : Ctxt jasminDialect} {p : Nat}
    {o : Option (ModArithLimbTemplate p .canon)} {c : ZMod p} {a b : Var Δ (optTy o)}
    {blk : Com jasminDialect Δ (optTy o)} (hb : montBlock? o c a b = some blk) :
    LeakFixed (jLeakModel Pj) blk := by
  cases o with
  | none => cases hb
  | some T =>
      simp only [montBlock?] at hb
      split at hb
      · rename_i h
        cases hb
        exact ofCanonMontMul_fixed T h.1 Pj hV c a b
      · cases hb

omit hV in
/-- An expression whose blocks have fixed events emits the same block events at every two
    valuations. -/
theorem blockEv_eq_of_fixed {Γ : Ctxt jasMod} {t : jasMod.Ty} (e : Expr jasMod Γ t)
    (h : ∀ blk, modArithLimbsJ.lowerExprBlock? e = some blk → LeakFixed (jLeakModel Pj) blk)
    (V₁ V₂ : Valuation Γ) :
    (blockEv modArithLimbsJ (fun V => mapVal V) (jLeakModel Pj)).ev _ _ e V₁ =
      (blockEv modArithLimbsJ (fun V => mapVal V) (jLeakModel Pj)).ev _ _ e V₂ := by
  cases hb : modArithLimbsJ.lowerExprBlock? e with
  | none => simp only [blockEv, hb]
  | some blk =>
      simp only [blockEv, hb]
      exact h blk hb _ _

omit hV in
/-- The readings of values under `jasModLeak M N` are those under `sumLeak M N`. -/
theorem valsNat_jasModLeak (M : LeakModel jasminDialect) (N : LeakModel modArithDialect) :
    ∀ {tys : List (JasminTy ⊕ ModArithTy)} (vals : HVector (fun t => ⟦t⟧) tys),
      ComLevelCheck.valsNat (jasModLeak M N) vals = ComLevelCheck.valsNat (sumLeak M N) vals
  | [], .nil => rfl
  | _ :: _, .cons _ vs => congrArg (List.cons _) (valsNat_jasModLeak M N vs)

/-- **The block events agree where the source events agree.** At leakage parameters of
    `jasminDialect` with no variable-time operation and every leakage model `N` of
    `modArithDialect`, an operation of `jasminDialect` emits in its block its own events, and
    every other block has fixed events. -/
theorem blockEv_agree (N : LeakModel modArithDialect) {Γ : Ctxt jasMod} {t : jasMod.Ty}
    (e : Expr jasMod Γ t) (V₁ V₂ : Valuation Γ)
    (h : ComLevelCheck.Expr.ctLeak (jasModLeak (jLeakModel Pj) N) e V₁ =
      ComLevelCheck.Expr.ctLeak (jasModLeak (jLeakModel Pj) N) e V₂) :
    (blockEv modArithLimbsJ (fun V => mapVal V) (jLeakModel Pj)).ev _ _ e V₁ =
      (blockEv modArithLimbsJ (fun V => mapVal V) (jLeakModel Pj)).ev _ _ e V₂ := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with (o | o) | o
  · have key : ∀ V : Valuation Γ,
        (blockEv modArithLimbsJ (fun V => mapVal V) (jLeakModel Pj)).ev _ _
          ⟨.inl (.inl o), rfl, args⟩ V =
        ComLevelCheck.Expr.ctLeak (jasModLeak (jLeakModel Pj) N) ⟨.inl (.inl o), rfl, args⟩ V :=
      fun V => by
        show ComLevelCheck.Com.ctLeak _ (.var ⟨o, rfl, argsJ args⟩ (.ret .here)) (mapVal V) = _
        simp only [ComLevelCheck.Com.ctLeak, List.append_nil, ComLevelCheck.Expr.ctLeak]
        rw [lookupArgs_argsJ]
        rw [← DialectCoproduct.opLeak_inl (jLeakModel Pj) N o]
        unfold ComLevelCheck.opLeak
        rw [valsNat_jasModLeak]
        rfl
    rw [key, key, h]
  · refine blockEv_eq_of_fixed Pj _ (fun blk hb => ?_) V₁ V₂
    change modBlock? o args = some blk at hb
    cases o with
    | modAdd p =>
        simp only [modBlock?] at hb
        split at hb <;> exact bodyBlock?_fixed Pj hV hb
    | modSub p => exact bodyBlock?_fixed Pj hV hb
    | modMul p =>
        simp only [modBlock?] at hb
        split at hb <;> exact bodyBlock?_fixed Pj hV hb
    | modNeg p => exact bodyBlock?_fixed Pj hV hb
    | modCopy p =>
        cases hb
        intro W₁ W₂
        rfl
    | montMul p c => exact montBlock?_fixed Pj hV hb
    | _ => cases hb
  · refine blockEv_eq_of_fixed Pj _ (fun blk hb => ?_) V₁ V₂
    change limbCastBlock? o args = some blk at hb
    cases o with
    | fromWordsM p w n => exact ofWordsBlock?_fixed Pj hV hb
    | toWordsM p w n => exact toWordsBlock?_fixed Pj hV hb

end Events

/-! ## 6. The chain stage -/

/-- **The chain stage `jasMod → jasminDialect`.** The lowering of structured programs along
    `modArithLimbsJ`. -/
def modArithLimbsStep (Γ : Ctxt jasMod) (ts : List jasMod.Ty) :
    PassChain.Step (NFProg jasMod Γ ts)
      (NFProg jasminDialect (Γ.map mapTy) (ts.map mapTy)) :=
  NFProgPasses.mapStep modArithLimbsJ modArithLimbsJ_regionTypes Γ ts

/-- **The certificate of the chain stage.** Under the agreement `hCall` of the call
    environments `E` and `E'` along the transport, `modArithLimbsStep Γ ts` is certified
    from the semantics at `E` to the semantics at `E'`, at every fuel, with the graph of
    `mapVal` as input relation and the graph of the transport of result tuples as output
    relation. -/
def modArithLimbsCert (E : CallEnv jasMod) (E' : CallEnv jasminDialect)
    (hCall : E.Transports E' (fun as => as.map mapTy)
      (fun x => transArgs mapTy (fun y => transTy y) x) (fun _ _ _ => True))
    (fuel : Nat) (Γ : Ctxt jasMod) (ts : List jasMod.Ty) :
    PassChain.StepCert (modArithLimbsStep Γ ts).run (NFProgPasses.nfSemE E fuel Γ ts)
      (NFProgPasses.nfSemE E' fuel (Γ.map mapTy) (ts.map mapTy)) :=
  PassChain.StepCert.ofMapAtM? modArithLimbsJ modArithLimbsJ_regionTypes (fun x => transTy x)
    (fun V => mapVal V) modArithLimbsJ_varTransports
    (fun e blk hb V x hx => modArithLimbsJ_block_fwd e blk hb V x hx)
    modArithLimbsJ_mapValExtends modArithLimbsJ_regionTransports E E' hCall fuel Γ ts

open CatCrypt.Crypto.SecureCompilation.CT (CTLeak) in
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (ExprEv) in
/-- **Two leakage runs before the stage give two runs of its result, with equal events from
    equal events.** At leakage parameters of `jasminDialect` with no variable-time operation,
    every leakage model `N` of `modArithDialect`, and call environments `E` and `E'` that
    agree along the transport at the calls of the source program, two runs of the source
    program at `E` are matched by runs of
    the lowered program at `E'` from the transported valuations to the transported results;
    when the source events are equal, so are the events of the two lowered runs. A block of a
    field operation or of a cast has fixed events (`blockEv_agree`), so the block events agree
    wherever the source events do (`leakRunMC_prefix_ev`), and the lowered program runs at the
    block events (`map?_leakRunMC_blockEv`). -/
theorem modArithLimbsStep_leakRunC {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (N : LeakModel modArithDialect) (E : CallEnv jasMod) (E' : CallEnv jasminDialect)
    (fuel : Nat) {Γ : Ctxt jasMod} {ts : List jasMod.Ty} {p : NFProg jasMod Γ ts}
    (hCall : E.Transports E' (fun as => as.map mapTy)
      (fun x => transArgs mapTy (fun y => transTy y) x) p.Calls)
    {q : NFProg jasminDialect (Γ.map mapTy) (ts.map mapTy)}
    (hf : (modArithLimbsStep Γ ts).run p = some q) {V₁ V₂ : Valuation Γ}
    {r₁ r₂ : Valuation ts × List CTLeak}
    (h₁ : Dialects.NFLeak.NFProg.leakRunMC (jasModLeak (jLeakModel Pj) N) E fuel p V₁ =
      some r₁)
    (h₂ : Dialects.NFLeak.NFProg.leakRunMC (jasModLeak (jLeakModel Pj) N) E fuel p V₂ =
      some r₂) :
    ∃ l₁ l₂,
      Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E' fuel q (mapVal V₁) =
          some (transArgs mapTy (fun y => transTy y) r₁.1, l₁) ∧
        Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E' fuel q (mapVal V₂) =
          some (transArgs mapTy (fun y => transTy y) r₂.1, l₂) ∧
        (r₁.2 = r₂.2 → l₁ = l₂) := by
  have hlen : ∀ {Γ : Ctxt jasMod} {t : jasMod.Ty} (e : Expr jasMod Γ t) (V₁ V₂ : Valuation Γ),
      ((jasModLeak (jLeakModel Pj) N : ExprEv jasMod).ev _ _ e V₁).length =
        ((jasModLeak (jLeakModel Pj) N : ExprEv jasMod).ev _ _ e V₂).length := by
    intro Γ t e V₁ V₂
    show (ComLevelCheck.Expr.ctLeak _ e V₁).length = (ComLevelCheck.Expr.ctLeak _ e V₂).length
    rw [Dialects.NFLeak.Expr.ctLeak_length, Dialects.NFLeak.Expr.ctLeak_length]
  obtain ⟨l₁, l₂, e₁, e₂, hl⟩ := leakRunMC_prefix_ev
    (jasModLeak (jLeakModel Pj) N : ExprEv jasMod)
    (blockEv modArithLimbsJ (fun V => mapVal V) (jLeakModel Pj)) hlen
    (fun e V₁ V₂ h => blockEv_agree Pj hV N e V₁ V₂ h) E fuel p h₁ h₂
  have hBlk : ∀ {Γ : Ctxt jasMod} {t : jasMod.Ty} (e : Expr jasMod Γ t) blk,
      modArithLimbsJ.lowerExprBlock? e = some blk → ∀ (V : Valuation Γ) (x : ⟦t⟧),
      e.denoteM (M := Option) V = some x → blk.denote (mapVal V) = transTy x :=
    fun e blk hb V x hx =>
      Option.some.inj ((denoteM_jasmin blk _).symm.trans (modArithLimbsJ_block_fwd e blk hb V x hx))
  have run := fun (V : Valuation Γ) r
      (hr : Dialects.NFLeak.NFProg.leakRunMC
        (blockEv modArithLimbsJ (fun V => mapVal V) (jLeakModel Pj)) E fuel p V = some r) =>
    map?_leakRunMC_blockEv modArithLimbsJ (fun x => transTy x) (fun V => mapVal V)
      (jLeakModel Pj) modArithLimbsJ_regionTypes modArithLimbsJ_varTransports hBlk
      modArithLimbsJ_mapValExtends modArithLimbsJ_regionTransports E E' fuel p hCall
      (fun v => v) V (mapVal V) (NFProg.renRel_id _) q hf r hr
  exact ⟨l₁, l₂, run _ _ e₁, run _ _ e₂, fun he => (hl [] [] (by rw [he])).1⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.ModArithLimbs
