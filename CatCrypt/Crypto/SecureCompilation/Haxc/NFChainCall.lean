/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFMontifyHint
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFFlattenTuplesLeak

/-!
# The linear route with calls of declared procedures, up to the export

`extChain D Γ t` is the tuple flattening `flatSameStep` followed by `extChainCore D Γ t`,
the chain `nfChainPre Γ t` with the translation `nfToCatExt` in place of `nfToCat` and one
step more after the translation to `jasminDialect`. The step `flatSameStep` runs
`NFFlattenTuples.flattenTuples` on a program whose context and result types are no tuple
types, at which the flattened context and result types are the source ones
(`flatCtx_of_noTuple`), and refuses a program at a tuple type or at `unit`
(`NFFlattenTuples.tyIsTuple`), whose values the flattening erases; the flattened program has
the denotation (`flatSame_denote`) and, under `NFFlattenTuples.TupleQuiet`, the events
(`flatSame_leakRunM`) of the source program. The translation
declares the procedures of `D` whose names are no field heads (`Hax.FieldTag.fieldHeadB`)
and, for each tagged field call of the program (a head `Hax.FieldTag.fieldTag?` reads as a method of the
prime-field interface), the declaration of the head (`fieldDeclsFor D p`): `fieldDecl` on
words at a modulus below `2⁶⁴`, `FieldWideDecl.wideDecl` on word arrays at a modulus of
several words. A declared call is translated to the node `call` of
`catCryptDialect`, and the later steps carry the node to `jasminDialect`. The montify step
`NFMontify.montifyStep`, after the conversion `map?`, keeps the words of the field values at
each modulus that passes `mont32Cert` as Montgomery representatives where the degree analysis
`NFMontify.degHint` places them, with the multiplications as reduce-multiply blocks; it never
refuses, and keeps the program at a modulus whose analysis the rewriter refuses. The field
step of the chain, after the montify step and before the select lowering, is
`FieldDialectStep.fieldDialectStep` (`Haxc/FieldDialectStep.lean`), which raises the tagged
calls into the field dialect and lowers them through `mod_arith` to the limb templates. The
inlining step `fieldInlineStep` of this module replaces each `call` of a tagged head at a
modulus the narrow template accepts by the block of that template (`fieldBlockOf`, from `FieldRouteNarrow.narrowField`), and each `call` at a modulus
with a wide template by the block `FieldWideDecl.wideBody` of that template, through the
inlining `NFProg.inline?` at the library `fieldLibJ`; it refuses a program that keeps a
`call` of a tagged head, which is a call at a modulus without a template. At leakage
parameters with no variable-time operation every body of a head runs at one list of events
(`fieldBody_leakRunMC`), so the library is sound for the leakage run with a fixed list of
events per head (`fieldLibJ_leakSound`). This module holds the steps and their
certificates; the chain `extChain`, its certificate `extChainCert` and the region front
`NFEntry.frontR` are in `Haxc/ExtChain.lean`.

The value certificate is stated at explicit call environments. The environment of
`jasminDialect` is a parameter `E'`. Up to the field step the certificate is stated at
`fieldEnv E'` (`Haxc/NFMontify.lean`), which answers a tagged head by the `u64` table and
every other
name by `E'`; the environment of `catCryptDialect` is `catEnvOf (fieldEnv E')` (`catEnvOf`
in `Haxc/NFChain.lean`). The library is sound at `fieldEnv E'` (`fieldLibJ_sound`): on
canonical arguments the template block of a method returns the value of its arm
(`fieldBlockOf_denoteAt`). The inlined program calls no tagged head, so it denotes the same
at `fieldEnv E'` and at `E'` (`fieldInlineCert`). The hypotheses of the certificate are
`SubTable bi`, `FieldLevel.FieldCalls bi`, `FieldLevel.FieldCallsWideEq bi` and
`ExtAgree bi (catEnvOf E') D`.

## Main definitions

* `aegraphEnvCert`, `lowerSelectsEnvCert`, `rangeEnvCert` — the certificates of the e-graph
  pass, of the select lowering and of the range stage `synRange` at an explicit call
  environment.
* `fieldBlockOf`, `narrowFieldOf`, `fieldBody`, `fieldLibJ` — the template block of a
  method, the narrow template at a modulus, and the inlining library of the tagged heads.
* `fieldFree`, `fieldInlineStep`, `fieldInlineCert` — the test that no `call` has a field
  head, the inlining step and its certificate.
* `fieldDecl`, `fieldDeclsOf`, `fieldDeclsFor` — the declaration of a tagged head, the
  declarations of the tagged calls of a program, and the declarations of the translation.
* `extCallStep`, `extCallCert` — the translation `nfToCatExt (fieldDeclsFor D p)` as a chain
  step, and its certificate from `nfToCatExt_sound`.
* `flatSame`, `flatSameStep`, `flatSameCert` — tuple flattening at a context and result
  types without tuple types, as a chain step, and its certificate.
* `declSigs` — the signatures of a list of declarations in `jasminDialect`, at which the
  region front `NFEntry.frontR` exports.
* `kindOfTy`, `valKind`, `arrLen?`, `linkedKinds` — the parameter kind of an argument type
  and of a source value, the length of an array result type, and the parameter kinds of a
  linked function.
* `linkedSummary`, `procTableOf` — the procedure summary of a linked function, with word and
  word-array parameters and a word or word-array result, and the table of procedure
  summaries of the linked functions of a module over a base table.

## Main results

* `fieldBlockOf_denoteAt`, `fieldLibJ_sound` — the template block of a method returns the
  canonical value of its arm, and the library is sound at `fieldEnv E'`.
* `fieldBody_leakRunMC`, `fieldLibJ_leakSound` — every body of a tagged head runs at one
  list of events, and the library is sound for the leakage run at `fieldEnv E'` with those
  events.
* `extAgree_fieldDeclsFor` — the declarations of the translation agree with the table and
  with `catEnvOf (fieldEnv E')`.
* `flatCtx_of_noTuple`, `flatV_heq` — a context without tuple types and its valuations are
  their own flattenings.
* `flatSame_denote`, `flatSame_leakRunM`, `flatSame_isSome` — tuple flattening keeps the
  denotation and the events at a leakage model with quiet tuple operations, and succeeds on
  the programs `flattenTuples` accepts.
* `nfToCatExt_congr` — the translation reads the declared names and signatures only.
* `extChain_mapStep_isSome` — the conversion step of the chain does not refuse.
* `insArrArgs_eq_arrArgsOf`, `insVals_wordsOf` — the array positions and the source values
  of the words of a valuation, read under the kinds of its types, are those of the
  valuation.
* `linkedSummary_wordOnly`, `linkedSummary_retWord` — the summary of a linked function with
  scalar parameters has only word arguments, and with a result type that is no array it has
  no word-array result.
* `linkedSummary_kinded` — the summary of a linked function has its declared result kind.
* `procsAgree_tableEnv_linkTable` — the summaries of the linked functions of a module agree
  with the environment of its table over a base table whose summaries agree;
  `procsAgree_tableEnv_empty` is the empty table at a base table without word or word-array
  values.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes catToJasmin_varTransports catToJasmin_block
  catToJasmin_mapValExtends catToJasmin_regionTransports)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower (ctBackTy ctTransTy_ctBackTy)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep synRangeCert)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_denote)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (RuleSet)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (enc PDenP entryCtx EntryVals tableOf dec encAll)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField canonEnc w64
  eq_canonEnc_of_toNat)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow (narrowField narrowFoldsOf
  narrowCert_of_narrowFoldsOf narrowCert_bounds)
open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldArm fieldVal fieldArgs fieldVal_lt
  fieldHeadB fieldTagM?)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montifyStep montifyStepCert
  montifyStep_of_callFree)
open Ctxt (Var Valuation)
open _root_.Hax (Env Builtins)

/-! ## The endo-passes at an explicit call environment -/

section EnvCerts

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- The certificate of the select lowering at the call environment `E`: `lowerSelectsCert`
    at the instance of `E`. -/
def lowerSelectsEnvCert [DialectDenoteM d Option] [HasSelect d] (E : CallEnv d) (fuel : Nat)
    (Γ : Ctxt d) (ts : List d.Ty) :
    StepCert (lowerSelectsStep Γ ts).run (nfSemE E fuel Γ ts) (nfSemE E fuel Γ ts) :=
  @lowerSelectsCert d _ _ _ _ _ _ ⟨E⟩ fuel Γ ts

/-- The certificate of the e-graph pass at the call environment `E`: `aegraphCert` at the
    instance of `E`. -/
def aegraphEnvCert [DecidableEq d.Ty] [DialectDenote d] [DecidableEq d.Op] (E : CallEnv d)
    (R : RuleSet d) (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    StepCert (aegraphStep R Γ ts).run (nfSemE E fuel Γ ts) (nfSemE E fuel Γ ts) :=
  @aegraphCert d _ _ _ _ _ _ _ ⟨E⟩ R fuel Γ ts

end EnvCerts

/-- The certificate of the range stage `synRange` at the call environment `E`: `synRangeCert`
    at the
    instance of `E`. -/
def rangeEnvCert (E : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) :
    StepCert (synRangeStep Γ ts).run (nfSemE E fuel Γ ts) (nfSemE E fuel Γ ts) :=
  @synRangeCert ⟨E⟩ fuel Γ ts

/-! ## The tagged field calls in `jasminDialect` -/

/-- **The template block of a method** of a single-word representation `F`: the block of
    `F` for the operation of the method on the parameters, as a program with one result.
    Squaring is the multiplication block and doubling the addition block on the one
    parameter. -/
def fieldBlockOf {p : Nat} (F : SingleWordField p) :
    (m : FieldMethod) → NFProg jasminDialect (fieldJSig m) [w64]
  | .add => NFProg.ofCom (F.addBlk .here (.there .here))
  | .sub => NFProg.ofCom (F.subBlk .here (.there .here))
  | .mul => NFProg.ofCom (F.mulBlk .here (.there .here))
  | .neg => NFProg.ofCom (F.negBlk .here)
  | .square => NFProg.ofCom (F.mulBlk .here .here)
  | .double => NFProg.ofCom (F.addBlk .here .here)

/-- **The template block of a method returns the value of its arm.** For a single-word
    representation `F` with the canonical encoding at a modulus `p ≤ 2³¹`, on arguments
    below `p` the block of the method `m` returns, at every call environment and fuel, the
    canonical representative of `fieldVal m p` of the arguments. -/
theorem fieldBlockOf_denoteAt {p : Nat} [NeZero p] (hp : p ≤ 2 ^ 31) (F : SingleWordField p)
    (hF : F.enc = canonEnc p) {m : FieldMethod} (x : Valuation (d := jasminDialect) (fieldJSig m))
    (ha : (fieldNats m x).1 < p) (hb : m.binary = true → (fieldNats m x).2 < p)
    (E : CallEnv jasminDialect) (fuel : Nat) :
    (fieldBlockOf F m).denoteAt E fuel x =
      some (.cons (canonEnc p
        ((fieldVal m p (fieldNats m x).1 (fieldNats m x).2 : Nat) : ZMod p)) .nil) := by
  have hp64 : p ≤ 2 ^ 64 := le_trans hp (by norm_num)
  have out : ∀ z : ZMod p, z.val = fieldVal m p (fieldNats m x).1 (fieldNats m x).2 →
      canonEnc p ((fieldVal m p (fieldNats m x).1 (fieldNats m x).2 : Nat) : ZMod p) =
        F.enc z := by
    intro z hz
    rw [hF, ← hz, ZMod.natCast_zmod_val]
  have enc : ∀ w : BitVec 64, w.toNat < p → w = F.enc (w.toNat : ZMod p) := fun w hw => by
    rw [hF]
    exact eq_canonEnc_of_toNat hp64 w _ (by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hw])
  unfold NFProg.denoteAt
  let _ : CallDenote jasminDialect := ⟨E⟩
  cases m with
  | add =>
    rcases x with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
    have hu : u.toNat < p := ha
    have hv : v.toNat < p := hb rfl
    refine (NFProg.denote_ofCom (d := jasminDialect) _ fuel _).trans ?_
    rw [out ((u.toNat : ZMod p) + (v.toNat : ZMod p)) (by
      simp only [fieldVal, fieldNats, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hu,
        Nat.mod_eq_of_lt hv])]
    exact congrArg (fun w => some (HVector.cons w .nil))
      (F.addBlk_denote (Γ := [w64, w64]) .here (.there .here) _ _ _ (enc u hu) (enc v hv))
  | sub =>
    rcases x with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
    have hu : u.toNat < p := ha
    have hv : v.toNat < p := hb rfl
    refine (NFProg.denote_ofCom (d := jasminDialect) _ fuel _).trans ?_
    rw [out ((u.toNat : ZMod p) - (v.toNat : ZMod p)) (by
      rw [show (u.toNat : ZMod p) - v.toNat = ((u.toNat + p - v.toNat : Nat) : ZMod p) by
        rw [Nat.cast_sub (by omega)]; push_cast; simp]
      exact ZMod.val_natCast _ _)]
    exact congrArg (fun w => some (HVector.cons w .nil))
      (F.subBlk_denote (Γ := [w64, w64]) .here (.there .here) _ _ _ (enc u hu) (enc v hv))
  | mul =>
    rcases x with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
    have hu : u.toNat < p := ha
    have hv : v.toNat < p := hb rfl
    refine (NFProg.denote_ofCom (d := jasminDialect) _ fuel _).trans ?_
    rw [out ((u.toNat : ZMod p) * (v.toNat : ZMod p)) (by
      simp only [fieldVal, fieldNats, ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hu,
        Nat.mod_eq_of_lt hv])]
    exact congrArg (fun w => some (HVector.cons w .nil))
      (F.mulBlk_denote (Γ := [w64, w64]) .here (.there .here) _ _ _ (enc u hu) (enc v hv))
  | neg =>
    rcases x with _ | ⟨u, _ | _⟩
    have hu : u.toNat < p := ha
    refine (NFProg.denote_ofCom (d := jasminDialect) _ fuel _).trans ?_
    rw [out (-(u.toNat : ZMod p)) (by
      rw [show -(u.toNat : ZMod p) = ((p - u.toNat : Nat) : ZMod p) by
        rw [Nat.cast_sub (by omega)]; simp]
      exact ZMod.val_natCast _ _)]
    exact congrArg (fun w => some (HVector.cons w .nil))
      (F.negBlk_denote (Γ := [w64]) .here _ _ (enc u hu))
  | square =>
    rcases x with _ | ⟨u, _ | _⟩
    have hu : u.toNat < p := ha
    refine (NFProg.denote_ofCom (d := jasminDialect) _ fuel _).trans ?_
    rw [out ((u.toNat : ZMod p) * (u.toNat : ZMod p)) (by
      simp only [fieldVal, fieldNats, ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hu])]
    exact congrArg (fun w => some (HVector.cons w .nil))
      (F.mulBlk_denote (Γ := [w64]) .here .here _ _ _ (enc u hu) (enc u hu))
  | double =>
    rcases x with _ | ⟨u, _ | _⟩
    have hu : u.toNat < p := ha
    refine (NFProg.denote_ofCom (d := jasminDialect) _ fuel _).trans ?_
    rw [out ((u.toNat : ZMod p) + (u.toNat : ZMod p)) (by
      simp only [fieldVal, fieldNats, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hu,
        two_mul])]
    exact congrArg (fun w => some (HVector.cons w .nil))
      (F.addBlk_denote (Γ := [w64]) .here .here _ _ _ (enc u hu) (enc u hu))

/-- **The narrow template at a modulus**: the single-word representation
    `FieldRouteNarrow.narrowField` at the fold count `narrowFoldsOf p`, and `none` when the
    certificate accepts no fold count. -/
def narrowFieldOf (p : Nat) : Option (SingleWordField p) :=
  match h : narrowFoldsOf p with
  | some n => some (narrowField p n (narrowCert_of_narrowFoldsOf h))
  | none => none

/-- A narrow template is at a modulus `1 < p ≤ 2³¹` and has the canonical encoding. -/
theorem narrowFieldOf_spec {p : Nat} {F : SingleWordField p} (h : narrowFieldOf p = some F) :
    1 < p ∧ p ≤ 2 ^ 31 ∧ F.enc = canonEnc p := by
  unfold narrowFieldOf at h
  split at h
  · rename_i n hn
    cases h
    exact ⟨(narrowCert_bounds (narrowCert_of_narrowFoldsOf hn)).1,
      (narrowCert_bounds (narrowCert_of_narrowFoldsOf hn)).2, rfl⟩
  · cases h

/-- **The body of a tagged head** at the signature `as → rs`: for a head of the method `m`
    at a modulus with a narrow template, at the signature of `m` with one `64`-bit result,
    the template block of `m`; at a modulus without a narrow template, the body
    `FieldWideDecl.wideBody` of a wide template; `none` otherwise. -/
def fieldBody (f : String) (as rs : List JasminTy) : Option (NFProg jasminDialect as rs) :=
  match fieldTag? f with
  | some (m, p) =>
      match narrowFieldOf p with
      | some F =>
          if hs : as = fieldJSig m ∧ rs = [w64] then
            some (hs.1 ▸ hs.2 ▸ fieldBlockOf F m)
          else none
      | none => FieldWideDecl.wideBody f as rs
  | none => none

/-- A head with a body `fieldBody` is a tagged head. -/
theorem fieldTag?_isSome_of_fieldBody {f : String} {as rs : List JasminTy}
    (h : (fieldBody f as rs).isSome = true) : (fieldTag? f).isSome = true := by
  unfold fieldBody at h
  split at h
  · rename_i m p ht
    simp [ht]
  · simp at h

/-- **The inlining library of the tagged heads**: no operation has a body, and a `call` of
    a tagged head has the body `fieldBody`. -/
def fieldLibJ : InlineLib jasminDialect where
  op _ := none
  call := fieldBody

/-- **The library of the tagged heads is sound at `fieldEnv E`**, at every fuel: a run of
    `fieldEnv E` at a tagged head with a body is a run of the `u64` table, which is defined
    on canonical arguments only, and on them the template block returns the same value
    (`tableEnv_field`, `fieldBlockOf_denoteAt`, and `FieldWideDecl.wideBody_sound` for a
    wide template). -/
theorem fieldLibJ_sound (E : CallEnv jasminDialect) (fuel : Nat) :
    @InlineLib.Sound jasminDialect _ _ _ _ _ ⟨fieldEnv E⟩ fieldLibJ fuel := by
  refine @InlineLib.Sound.mk jasminDialect _ _ _ _ _ ⟨fieldEnv E⟩ fieldLibJ fuel
    (fun o b hb => by cases hb) ?_
  intro f as rs b hb x y hy
  change fieldBody f as rs = some b at hb
  change (fieldEnv E).call f as rs x = some y at hy
  unfold fieldBody at hb
  split at hb
  · rename_i m p ht
    split at hb
    · rename_i F hF
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        obtain ⟨hp1, hp, hFe⟩ := narrowFieldOf_spec hF
        have : NeZero p := ⟨by omega⟩
        rw [fieldEnv_of_isSome E (by simp [ht])] at hy
        obtain ⟨ha, hb, rfl⟩ := tableEnv_field (by omega) ht x y hy
        exact fieldBlockOf_denoteAt hp F hFe x ha hb (fieldEnv E) fuel
      · cases hb
    · rw [fieldEnv_of_isSome E (by simp [ht])] at hy
      exact FieldWideDecl.wideBody_sound (fieldEnv E) fuel hb x y hy
  · cases hb

/-! ### The leakage of the template blocks -/

section Quiet

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (Com.OpsQuiet)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (spliceCom)

/-- A renamed straight-line program binds the operations of the source. -/
theorem opsQuiet_rename {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    (M : LeakModel d) : ∀ {Γ Γ' : Ctxt d} {t : d.Ty} (h : Ctxt.Hom Γ Γ') (c : Com d Γ t),
      Com.OpsQuiet M c → Com.OpsQuiet M (Com.rename h c)
  | _, _, _, _, .ret _, _ => trivial
  | _, _, _, h, .var _ body, hc => by
      obtain ⟨he, hb⟩ := hc
      exact And.intro he (opsQuiet_rename M h.lift body hb)

/-- The splice of two straight-line programs of quiet operations binds quiet operations. -/
theorem opsQuiet_spliceCom {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    (M : LeakModel d) : ∀ {Γ : Ctxt d} {t s : d.Ty} (c : Com d Γ t) (k : Com d (t :: Γ) s),
      Com.OpsQuiet M c → Com.OpsQuiet M k → Com.OpsQuiet M (spliceCom c k)
  | _, _, _, .ret _, k, _, hk => opsQuiet_rename M _ k hk
  | _, _, _, .var _ body, k, hc, hk => by
      obtain ⟨he, hb⟩ := hc
      exact And.intro he (opsQuiet_spliceCom M body _ hb (opsQuiet_rename M _ k hk))

variable (M : LeakModel jasminDialect) (hA : ∀ bop w, M.kind (.regArith bop w) = .quiet)
  (hK : ∀ w n, M.kind (.regConst w n) = .quiet)
include hA hK

/-- The conditional subtract binds register constants and register arithmetic only. -/
theorem opsQuiet_csubBlk {Γ : Ctxt jasminDialect} (P : Nat) (x : Var Γ w64) :
    Com.OpsQuiet M (Algebraic.FieldWord.csubBlk P x) :=
  And.intro (hK _ _) <| And.intro (hA _ _) <| And.intro (hK _ _) <| And.intro (hA _ _) <|
    And.intro (hK _ _) <| And.intro (hA _ _) <| And.intro (hA _ _) <| And.intro (hA _ _) trivial

omit hK in
/-- The binding of one register-arithmetic operation binds quiet operations. -/
theorem opsQuiet_binBlk {Γ : Ctxt jasminDialect} (op : JasminBinOp) (a b : Var Γ w64) :
    Com.OpsQuiet M (Algebraic.FieldWord.binBlk op a b) :=
  And.intro (hA _ _) trivial

omit hA in
/-- The binding of one register constant binds quiet operations. -/
theorem opsQuiet_litBlk {Γ : Ctxt jasminDialect} (k : Nat) :
    Com.OpsQuiet M (Algebraic.FieldWord.litBlk (Γ := Γ) k) :=
  And.intro (hK _ _) trivial

/-- A register constant and one register-arithmetic operation on it bind quiet
    operations. -/
theorem opsQuiet_binLitBlk {Γ : Ctxt jasminDialect} (op : JasminBinOp) (a : Var Γ w64)
    (k : Nat) : Com.OpsQuiet M (Algebraic.FieldWord.binLitBlk op a k) :=
  And.intro (hK _ _) (And.intro (hA _ _) trivial)

/-- The `n` folds bind register constants and register arithmetic only. -/
theorem opsQuiet_foldsBlk (c : Nat) :
    ∀ (n : Nat) {Γ : Ctxt jasminDialect} (x : Var Γ w64),
      Com.OpsQuiet M (Algebraic.FieldWord.foldsBlk c n x)
  | 0, _, _ => trivial
  | n + 1, _, _ =>
      opsQuiet_spliceCom M _ _
        (opsQuiet_spliceCom M _ _ (opsQuiet_binLitBlk M hA hK _ _ _) <|
          opsQuiet_spliceCom M _ _ (opsQuiet_binLitBlk M hA hK _ _ _) <|
          opsQuiet_spliceCom M _ _ (opsQuiet_binLitBlk M hA hK _ _ _)
            (opsQuiet_binBlk M hA _ _ _))
        (opsQuiet_foldsBlk c n _)

/-- **The template blocks of the narrow representation bind quiet operations**: register
    constants and register arithmetic only. -/
theorem fieldBlockOf_quiet {p n : Nat} (h : FieldRouteNarrow.narrowCert p n = true)
    (m : FieldMethod) (fuel : Nat) (x : Valuation (d := jasminDialect) (fieldJSig m)) :
    (Dialects.NFLeak.NFProg.leakRunM M fuel (fieldBlockOf (narrowField p n h) m) x).map
      Prod.snd = some [] := by
  have hadd : ∀ {Γ : Ctxt jasminDialect} (a b : Var Γ w64),
      Com.OpsQuiet M (Algebraic.FieldWord.addBlk p a b) := fun a b =>
    opsQuiet_spliceCom M _ _ (opsQuiet_binBlk M hA _ _ _) (opsQuiet_csubBlk M hA hK _ _)
  have hsub : ∀ {Γ : Ctxt jasminDialect} (a b : Var Γ w64),
      Com.OpsQuiet M (Algebraic.FieldWord.subBlk p a b) := fun a b =>
    opsQuiet_spliceCom M _ _ (opsQuiet_litBlk M hK _) <|
      opsQuiet_spliceCom M _ _ (opsQuiet_binBlk M hA _ _ _) <|
      opsQuiet_spliceCom M _ _ (opsQuiet_binBlk M hA _ _ _) (opsQuiet_csubBlk M hA hK _ _)
  have hneg : ∀ {Γ : Ctxt jasminDialect} (a : Var Γ w64),
      Com.OpsQuiet M (Algebraic.FieldWord.negBlk p a) := fun a =>
    opsQuiet_spliceCom M _ _ (opsQuiet_litBlk M hK _) <|
      opsQuiet_spliceCom M _ _ (opsQuiet_binBlk M hA _ _ _) (opsQuiet_csubBlk M hA hK _ _)
  have hmul : ∀ {Γ : Ctxt jasminDialect} (a b : Var Γ w64),
      Com.OpsQuiet M (FieldRouteNarrow.narrowMulBlk p n a b) := fun a b =>
    opsQuiet_spliceCom M _ _ (opsQuiet_binBlk M hA _ _ _) <|
      opsQuiet_spliceCom M _ _ (opsQuiet_foldsBlk M hA hK _ _ _) (opsQuiet_csubBlk M hA hK _ _)
  cases m with
  | add =>
    exact congrArg (Option.map Prod.snd)
      (Dialects.NFLeak.NFProg.leakRunM_ofCom_quiet M fuel _ (hadd .here (.there .here)) x)
  | sub =>
    exact congrArg (Option.map Prod.snd)
      (Dialects.NFLeak.NFProg.leakRunM_ofCom_quiet M fuel _ (hsub .here (.there .here)) x)
  | mul =>
    exact congrArg (Option.map Prod.snd)
      (Dialects.NFLeak.NFProg.leakRunM_ofCom_quiet M fuel _ (hmul .here (.there .here)) x)
  | neg =>
    exact congrArg (Option.map Prod.snd)
      (Dialects.NFLeak.NFProg.leakRunM_ofCom_quiet M fuel _ (hneg .here) x)
  | square =>
    exact congrArg (Option.map Prod.snd)
      (Dialects.NFLeak.NFProg.leakRunM_ofCom_quiet M fuel _ (hmul .here .here) x)
  | double =>
    exact congrArg (Option.map Prod.snd)
      (Dialects.NFLeak.NFProg.leakRunM_ofCom_quiet M fuel _ (hadd .here .here) x)

end Quiet

section LeakSound

open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel jKind)

variable {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
include hV

/-- **A body of a tagged head runs at a fixed list of events**: at leakage parameters of
    `jasminDialect` with no variable-time operation, there is one list of events at which
    every body of `fieldBody f as rs` runs, at every call environment, fuel and argument
    vector: the empty list for a narrow template (`fieldBlockOf_quiet`), the events of the
    wide block for a wide template (`FieldWideLeak.wideBody_leakRunMC`). -/
theorem fieldBody_leakRunMC (f : String) (as rs : List JasminTy) :
    ∃ ev, ∀ b, fieldBody f as rs = some b → ∀ (E : CallEnv jasminDialect) (fuel : Nat)
      (x : Valuation (d := jasminDialect) as),
      (Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E fuel b x).map Prod.snd =
        some ev := by
  unfold fieldBody
  split
  · rename_i m p _
    split
    · rename_i F hF
      refine ⟨[], fun b hb E fuel x => ?_⟩
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        unfold narrowFieldOf at hF
        split at hF
        · rename_i k hk
          cases hF
          have hcf : (fieldBlockOf (narrowField p k (FieldRouteNarrow.narrowCert_of_narrowFoldsOf
              hk)) m).callFree = true := by
            cases m <;> exact callFree_ofCom _
          rw [Dialects.NFLeak.NFProg.leakRunMC_of_callFree _ _ fuel _ hcf]
          exact fieldBlockOf_quiet (jLeakModel Pj)
            (fun _ _ => by simp only [jLeakModel, jKind, hV])
            (fun _ _ => by simp only [jLeakModel, jKind, hV]) _ m fuel x
        · cases hF
      · cases hb
    · exact FieldWideLeak.wideBody_leakRunMC hV f as rs
  · exact ⟨[], fun _ hb => by cases hb⟩

/-- **The library of the tagged heads is sound for the leakage run at `fieldEnv E`**, with a
    fixed list of events per head: a body runs as the `u64` table at its head
    (`fieldLibJ_sound`) and at the events `fieldBody_leakRunMC` fixes, at leakage parameters
    of `jasminDialect` with no variable-time operation. -/
theorem fieldLibJ_leakSound (E : CallEnv jasminDialect) (fuel : Nat) :
    ∃ ev, fieldLibJ.LeakSound (jLeakModel Pj) (fieldEnv E) fuel ev := by
  choose ev hev using fun f as rs => fieldBody_leakRunMC hV f as rs
  refine ⟨ev, fun o b hb => (by cases hb), ?_⟩
  intro f as rs b hb x y hy
  have hval := @InlineLib.Sound.call jasminDialect _ _ _ _ _ ⟨fieldEnv E⟩ fieldLibJ fuel
    (fieldLibJ_sound E fuel) f as rs b hb x y hy
  change b.denoteAt (fieldEnv E) fuel x = some y at hval
  rw [← Dialects.NFLeak.NFProg.leakRunMC_fst (jLeakModel Pj) (fieldEnv E) fuel b x] at hval
  have he := hev f as rs b hb (fieldEnv E) fuel x
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hval
  rw [hr, Option.map_some, Option.some.injEq] at he
  rw [hr, ← he]

end LeakSound

/-- **No `call` of the program has a field head** (`fieldHeadB`, a canonical or a Montgomery
    head). -/
def fieldFree {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => fieldFree k
  | _, _, .forLoop _ _ body k => fieldFree body && fieldFree k
  | _, _, .ifThenElse _ thn els k => fieldFree thn && fieldFree els && fieldFree k
  | _, _, .whileLoop _ body k => fieldFree body && fieldFree k
  | _, _, .call f _ k => !fieldHeadB f && fieldFree k

/-- A symbol a program that passes `fieldFree` calls is no field head. -/
theorem fieldHeadB_of_fieldFree {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : fieldFree p = true) {f : String} {as rs : List d.Ty} (hc : p.Calls f as rs) :
    fieldHeadB f = false := by
  induction p with
  | ret => exact hc.elim
  | var e k ih => exact ih hp hc
  | forLoop _ _ _ _ ihb ihk =>
      simp only [fieldFree, Bool.and_eq_true] at hp
      rcases hc with h | h
      exacts [ihb hp.1 h, ihk hp.2 h]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [fieldFree, Bool.and_eq_true] at hp
      rcases hc with h | h | h
      exacts [iht hp.1.1 h, ihe hp.1.2 h, ihk hp.2 h]
  | whileLoop _ _ _ ihb ihk =>
      simp only [fieldFree, Bool.and_eq_true] at hp
      rcases hc with h | h
      exacts [ihb hp.1 h, ihk hp.2 h]
  | call g _ k ih =>
      simp only [fieldFree, Bool.and_eq_true, Bool.not_eq_true'] at hp
      rcases hc with ⟨rfl, -, -⟩ | h
      exacts [hp.1, ih hp.2 h]

/-- A program without `call` passes `fieldFree`. -/
theorem fieldFree_of_callFree {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : p.callFree = true) : fieldFree p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldFree, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldFree, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldFree, ihb hp.1, ihk hp.2, Bool.and_self]
  | call _ _ _ _ => simp [NFProg.callFree] at hp

/-- **The inlining of the tagged calls as a chain step**: one round of `NFProg.inline?` at
    the library `fieldLibJ`, refused when the result keeps a `call` of a tagged head.
    `compileA` does not apply this step: its front inlines the calls of the functions of the
    module by `HaxModule.inline?`, and its chain `extChain` lowers the tagged calls by
    `FieldDialectStep.fieldDialectStep`. -/
def fieldInlineStep (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    Step (NFProg jasminDialect Γ ts) (NFProg jasminDialect Γ ts) :=
  ⟨"fieldInline", fun p => (NFProg.inline? fieldLibJ p).bind fun q =>
    if fieldFree q then some q else none⟩

/-- **The certificate of the inlining step**, from the semantics at `fieldEnv E` to the
    semantics at `E`, with equal inputs and outputs: inlining under the sound library keeps
    every run at `fieldEnv E` (`NFProg.denoteAt_inline?`), and the result calls no tagged
    head, at which alone the two environments differ (`NFProg.denoteAt_congr`). -/
def fieldInlineCert (E : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) :
    StepCert (fieldInlineStep Γ ts).run (nfSemE (fieldEnv E) fuel Γ ts) (nfSemE E fuel Γ ts) where
  relIn V W := W = V
  relOut o o' := o' = o
  sound := by
    rintro p q V W o hf rfl hd
    obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
    split at hif
    · rename_i hff
      have hq : q0 = q := Option.some.inj hif
      subst hq
      refine ⟨o, ?_, rfl⟩
      change NFProg.denoteAt E fuel q0 W = some o
      rw [NFProg.denoteAt_congr q0 E (fieldEnv E) (fun f as rs x hc =>
        (fieldEnv_of_none E (fieldHeadB_of_fieldFree q0 hff hc) as rs x).symm) fuel W]
      exact NFProg.denoteAt_inline? (fieldEnv E) (fieldLibJ_sound E fuel) p hq0 hd
    · cases hif

/-- An inlining library without operation bodies returns a program without `call`
    unchanged. -/
theorem inline?_of_callFree {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] (L : InlineLib d) (hL : ∀ o, L.op o = none) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.callFree = true) :
    NFProg.inline? L p = some p := by
  induction p with
  | ret => rfl
  | var e k ih =>
      obtain ⟨o, rfl, args⟩ := e
      simp only [NFProg.inline?, ih hp, Option.bind_some, NFProg.inlineVar, hL]
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, ihb hp.1, ihk hp.2, Option.bind_some, Option.map_some]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, iht hp.1.1, ihe hp.1.2, ihk hp.2, Option.bind_some,
        Option.map_some]
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, ihb hp.1, ihk hp.2, Option.bind_some, Option.map_some]
  | call _ _ _ _ => simp [NFProg.callFree] at hp

/-- **The inlining step keeps a program without `call`.** -/
theorem fieldInlineStep_of_callFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : p.callFree = true) :
    (fieldInlineStep Γ ts).run p = some p := by
  change (NFProg.inline? fieldLibJ p).bind (fun q => if fieldFree q then some q else none) = _
  rw [inline?_of_callFree fieldLibJ (fun _ => rfl) p hp, Option.bind_some,
    ite_eq_left (fieldFree_of_callFree p hp)]

/-! ## Programs without `call` through the translation and the conversion -/

/-- A program that calls no symbol has no `call`. -/
theorem callFree_of_not_calls {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (h : ∀ f as rs, ¬ p.Calls f as rs) : p.callFree = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih h
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true]
      exact ⟨ihb fun f as rs hc => h f as rs (Or.inl hc),
        ihk fun f as rs hc => h f as rs (Or.inr hc)⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true]
      exact ⟨⟨iht fun f as rs hc => h f as rs (Or.inl hc),
        ihe fun f as rs hc => h f as rs (Or.inr (Or.inl hc))⟩,
        ihk fun f as rs hc => h f as rs (Or.inr (Or.inr hc))⟩
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true]
      exact ⟨ihb fun f as rs hc => h f as rs (Or.inl hc),
        ihk fun f as rs hc => h f as rs (Or.inr hc)⟩
  | call f args k ih => exact absurd (Or.inl ⟨rfl, rfl, rfl⟩) (h _ _ _)

/-- A program `nfToCat` returns has no `call`: the translation without declarations keeps
    no call (`nfToCatExt_calls` at the empty list). -/
theorem nfToCat_callFree {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) {q : NFProg catCryptDialect Δ (ts.map catTy)}
    (h : nfToCat p σ = some q) : q.callFree = true := by
  replace h := nfToCatExt_nil p σ q h
  refine callFree_of_not_calls q fun f as rs hc => ?_
  obtain ⟨d, hd, -⟩ := nfToCatExt_calls [] p σ q h f as rs hc
  exact absurd hd List.not_mem_nil

/-- **A program the translation without declarations returns is returned at every list of
    declarations**, when it has no `call`. -/
theorem nfToCatExt_of_nfToCat (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy)),
      nfToCatExt [] p σ = some q → q.callFree = true → nfToCatExt D p σ = some q := by
  induction p with
  | ret vs =>
      intro Δ σ q h _
      exact h
  | var e k ih =>
      intro Δ σ q h hf
      obtain ⟨op, rfl, args⟩ := e
      change emitOp [] (fun σ' => nfToCatExt [] k σ') σ op rfl args = some q at h
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args = some q
      unfold emitOp at h ⊢
      split at h
      · rename_i res hres
        exact emitRes_callFree (fun σ' q' hq' hf' => ih σ' q' hq' hf') rfl res σ q h hf
      · rw [extArgs_nil] at h
        cases h
  | @forLoop _ cs _ count inits body k ihb ihk =>
      intro Δ σ q h hf
      refine pinAll_callFree (ts := .word 64 :: cs) ?_ σ _ q h hf
      intro Δ' σ' ws q' hq' hf'
      obtain ⟨b', hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq'
      simp only [NFProg.callFree, Bool.and_eq_true] at hf'
      simp only [ihb _ b' hb hf'.1, ihk _ k' hk hf'.2, Option.bind_some, Option.map_some]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ σ q h hf
      simp only [nfToCatExt] at h ⊢
      split at h
      · obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [NFProg.callFree, Bool.and_eq_true] at hf
        simp only [iht _ t' ht hf.1.1, ihe _ e' he hf.1.2, ihk _ k' hk hf.2,
          Option.bind_some, Option.map_some]
      · cases h
  | @whileLoop _ cs _ inits body k ihb ihk =>
      intro Δ σ q h hf
      refine pinAll_callFree (ts := cs) ?_ σ _ q h hf
      intro Δ' σ' ws q' hq' hf'
      obtain ⟨b', hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq'
      simp only [NFProg.callFree, Bool.and_eq_true] at hf'
      simp only [ihb _ b' hb hf'.1, ihk _ k' hk hf'.2, Option.bind_some, Option.map_some]
  | call f args k _ =>
      intro Δ σ q h
      cases h

/-- The traversal of the e-graph pass keeps the absence of `call`. -/
theorem nfGo_callFree {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]
    (R : RuleSet d) {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S)
    (p : NFProg d Γ ts) :
    (CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo R ρ S p).callFree = p.callFree := by
  induction p generalizing Δ S with
  | ret => rfl
  | var e k ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo]
      split <;> simp only [NFProg.callFree, ih]
  | forLoop _ _ _ _ ihb ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, NFProg.callFree, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, NFProg.callFree, iht, ihe,
        ihk]
  | whileLoop _ _ _ ihb ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, NFProg.callFree, ihb, ihk]
  | call _ _ _ ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, NFProg.callFree]

section MapCallFree

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- A block spliced before continuations that return programs without `call` gives a
    program without `call`. -/
theorem spliceNF?_callFree {ts : List d'.Ty} : {Δ : Ctxt d'} → {a : d'.Ty} →
    (blk : Com d' Δ a) →
    (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d' Δ' ts)) →
    (∀ {Δ' : Ctxt d'} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (q : NFProg d' Δ' ts),
      k ren res = some q → q.callFree = true) →
    ∀ {q : NFProg d' Δ ts}, NFProg.spliceNF? blk k = some q → q.callFree = true
  | _, _, .ret v, _, hk, _, h => hk _ v _ h
  | _, _, .var _ blk, k, hk, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact spliceNF?_callFree blk _ (fun ren res q hq => hk _ res q hq) hq'

/-- Carrying the first result type keeps the absence of `call`. -/
theorem castRetHead_callFree {Δ : Ctxt d} {a b : d.Ty} {ts : List d.Ty} (h : a = b)
    (p : NFProg d Δ (a :: ts)) : (NFProg.castRetHead h p).callFree = p.callFree := by
  subst h
  rfl

/-- **The conversion `map?` keeps the absence of `call`.** -/
theorem map?_callFree (P : PartialBlockLowering d d') (hT : P.RegionTypes) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.callFree = true) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) {q : NFProg d' Δ (ts.map P.mapTy)},
      NFProg.map? P hT p ren = some q → q.callFree = true := by
  induction p with
  | ret vs =>
      intro Δ ren q h
      cases h
      rfl
  | var e k ih =>
      intro Δ ren q h
      obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact spliceNF?_callFree _ _ (fun ren' res q' hq' => ih hp _ hq') h
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q h
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.callFree, ihb hp.1 _ hb, ihk hp.2 _ hk, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q h
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.callFree, iht hp.1.1 _ ht, ihe hp.1.2 _ he, ihk hp.2 _ hk,
        Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q h
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.callFree, castRetHead_callFree, ihb hp.1 _ hb, ihk hp.2 _ hk,
        Bool.and_self]
  | call f args k ih =>
      intro Δ ren q h
      simp [NFProg.callFree] at hp

end MapCallFree

/-! ## The declarations of the tagged field calls -/

/-- **The declaration of the tagged head `f` of the method `m`**: at the argument types of
    `m` and the result type of `64`-bit words, with the function of the `u64` table. -/
def fieldDecl (f : String) (m : FieldMethod) : ExtDecl :=
  ⟨f, m.sig, .word 64, (tableOf _root_.Hax.hax64Builtins).call f m.sig (.word 64)⟩

/-- The declaration of a leaf call of a field head: at a tagged head, `fieldDecl` at a
    modulus below `2⁶⁴` and `FieldWideDecl.wideDecl` at a modulus of several words; at a
    Montgomery head (`fieldTagM?`), `fieldDecl` at an odd modulus `1 < p < 2⁶⁴`; none for
    every other operation. -/
def opFieldDecls : NfOp → List ExtDecl
  | .call f _ _ =>
      match fieldTag? f with
      | some (m, p) => if p < 2 ^ 64 then [fieldDecl f m] else [FieldWideDecl.wideDecl f m p]
      | none =>
          match fieldTagM? f with
          | some (m, p, _) =>
              if 1 < p ∧ p % 2 = 1 ∧ p < 2 ^ 64 then [fieldDecl f m] else []
          | none => []
  | .named _ o => opFieldDecls o
  | _ => []

/-- **The declarations of the tagged calls of a program**: `opFieldDecls` at the operation
    of each binding, in every region. -/
def fieldDeclsOf : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts →
    List ExtDecl
  | _, _, .ret _ => []
  | _, _, .var ⟨o, _, _⟩ k => opFieldDecls o ++ fieldDeclsOf k
  | _, _, .forLoop _ _ body k => fieldDeclsOf body ++ fieldDeclsOf k
  | _, _, .ifThenElse _ thn els k => fieldDeclsOf thn ++ fieldDeclsOf els ++ fieldDeclsOf k
  | _, _, .whileLoop _ body k => fieldDeclsOf body ++ fieldDeclsOf k
  | _, _, .call _ _ k => fieldDeclsOf k

/-- **The declarations of the translation of a program**: the declarations of `D` whose
    names are no field heads (`fieldHeadB`), followed by the declarations of the tagged calls
    of the program. -/
def fieldDeclsFor (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : List ExtDecl :=
  D.filter (fun d => !fieldHeadB d.name) ++ fieldDeclsOf p

/-- A declaration of `opFieldDecls` is the declaration of a field head: at a tagged head,
    `fieldDecl` at a modulus below `2⁶⁴` and `FieldWideDecl.wideDecl` at a modulus of several
    words; at a Montgomery head, `fieldDecl` at an odd modulus `1 < p < 2⁶⁴`. -/
theorem mem_opFieldDecls {o : NfOp} {d : ExtDecl} (h : d ∈ opFieldDecls o) :
    (∃ m p, fieldTag? d.name = some (m, p) ∧ ((p < 2 ^ 64 ∧ d = fieldDecl d.name m) ∨
      (2 ^ 64 ≤ p ∧ d = FieldWideDecl.wideDecl d.name m p))) ∨
    ∃ m p k, fieldTagM? d.name = some (m, p, k) ∧ 1 < p ∧ p % 2 = 1 ∧ p < 2 ^ 64 ∧
      d = fieldDecl d.name m := by
  induction o with
  | call f as r =>
      simp only [opFieldDecls] at h
      split at h
      · rename_i m p ht
        split at h
        · rename_i hp
          obtain rfl := List.mem_singleton.mp h
          exact Or.inl ⟨m, p, ht, Or.inl ⟨hp, rfl⟩⟩
        · rename_i hp
          obtain rfl := List.mem_singleton.mp h
          exact Or.inl ⟨m, p, ht, Or.inr ⟨by omega, rfl⟩⟩
      · split at h
        · rename_i m p k ht
          split at h
          · rename_i hp
            obtain rfl := List.mem_singleton.mp h
            exact Or.inr ⟨m, p, k, ht, hp.1, hp.2.1, hp.2.2, rfl⟩
          · cases h
        · cases h
  | named n o ih => exact ih h
  | _ => cases h

/-- A declaration of `fieldDeclsOf` is the declaration of a field head: at a tagged head,
    `fieldDecl` at a modulus below `2⁶⁴` and `FieldWideDecl.wideDecl` at a modulus of several
    words; at a Montgomery head, `fieldDecl` at an odd modulus `1 < p < 2⁶⁴`. -/
theorem mem_fieldDeclsOf {Γ : Ctxt nfDialect} {ts : List NfTy} (q : NFProg nfDialect Γ ts)
    {d : ExtDecl} (h : d ∈ fieldDeclsOf q) :
    (∃ m p, fieldTag? d.name = some (m, p) ∧ ((p < 2 ^ 64 ∧ d = fieldDecl d.name m) ∨
      (2 ^ 64 ≤ p ∧ d = FieldWideDecl.wideDecl d.name m p))) ∨
    ∃ m p k, fieldTagM? d.name = some (m, p, k) ∧ 1 < p ∧ p % 2 = 1 ∧ p < 2 ^ 64 ∧
      d = fieldDecl d.name m := by
  induction q with
  | ret => cases h
  | var e k ih =>
      obtain ⟨o, _, _⟩ := e
      rcases List.mem_append.mp h with h | h
      exacts [mem_opFieldDecls h, ih h]
  | forLoop _ _ _ _ ihb ihk =>
      rcases List.mem_append.mp h with h | h
      exacts [ihb h, ihk h]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        exacts [iht h, ihe h]
      · exact ihk h
  | whileLoop _ _ _ ihb ihk =>
      rcases List.mem_append.mp h with h | h
      exacts [ihb h, ihk h]
  | call _ _ _ ih => exact ih h

/-- The encodings of arguments at the types of a method are the arguments `fieldArgs` of
    two numbers. -/
theorem encAll_sig (m : FieldMethod) (xs : HVector NfTy.denote m.sig) :
    ∃ a b : Nat, encAll m.sig xs = fieldArgs m a b := by
  cases m <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  all_goals first
    | exact ⟨a.toNat, b.toNat, rfl⟩
    | exact ⟨a.toNat, 0, rfl⟩

/-- **A table that answers the tagged heads by their arms has the declaration of a tagged
    head**: the table and the `u64` table agree at the head. -/
theorem fieldDecl_inTable {bi : Builtins} (hF : FieldLevel.FieldCalls bi)
    {f : String} {m : FieldMethod} {p : Nat} (ht : fieldTag? f = some (m, p))
    (hp : p < 2 ^ 64) : (fieldDecl f m).InTable bi := by
  intro xs
  obtain ⟨a, b, hab⟩ := encAll_sig m xs
  change ((bi f (encAll m.sig xs)).bind _) =
    ((_root_.Hax.hax64Builtins f (encAll m.sig xs)).bind _)
  rw [hab, hF.canon f m p ht hp a b, FieldLevel.fieldCalls_hax64Builtins.canon f m p ht hp a b]
  rfl

/-- **A table that answers the Montgomery heads by their arms has the declaration of a
    Montgomery head** at an odd modulus below `2⁶⁴`: the table and the `u64` table agree at
    the head. -/
theorem fieldDecl_inTable_mont {bi : Builtins} (hF : FieldLevel.FieldCalls bi)
    {f : String} {m : FieldMethod} {p k : Nat} (ht : fieldTagM? f = some (m, p, k))
    (hodd : p % 2 = 1) (hp : p < 2 ^ 64) : (fieldDecl f m).InTable bi := by
  intro xs
  obtain ⟨a, b, hab⟩ := encAll_sig m xs
  change ((bi f (encAll m.sig xs)).bind _) =
    ((_root_.Hax.hax64Builtins f (encAll m.sig xs)).bind _)
  rw [hab, hF.mont f m p k ht hodd hp a b,
    FieldLevel.fieldCalls_hax64Builtins.mont f m p k ht hodd hp a b]
  rfl

/-- A declaration implemented by an environment is implemented by every environment that
    answers its name the same way. -/
theorem implementedBy_congr {E E' : CallEnv catCryptDialect} {d : ExtDecl}
    (h : ∀ as rs x, E.call d.name as rs x = E'.call d.name as rs x)
    (hd : d.ImplementedBy E) : d.ImplementedBy E' := by
  intro xs ws y hws hy
  obtain ⟨v, hv, hr⟩ := hd xs ws y hws hy
  exact ⟨v, (h _ _ _).symm.trans hv, hr⟩

/-- `catEnvOf (fieldEnv E)` answers a tagged head as `catEnvOf` of the `u64` table. -/
theorem catEnvOf_fieldEnv_some (E : CallEnv jasminDialect) {f : String}
    (h : (fieldTag? f).isSome = true) (as rs : List CryptoTy)
    (x : Valuation (d := catCryptDialect) as) :
    (catEnvOf (fieldEnv E)).call f as rs x =
      (catEnvOf (tableEnv _root_.Hax.hax64Builtins)).call f as rs x := by
  change Option.map backArgs ((fieldEnv E).call f _ _ _) =
    Option.map backArgs ((tableEnv _root_.Hax.hax64Builtins).call f _ _ _)
  rw [fieldEnv_of_isSome E h]

/-- `catEnvOf (fieldEnv E)` answers a field head as `catEnvOf` of the `u64` table. -/
theorem catEnvOf_fieldEnv_of_fieldHeadB (E : CallEnv jasminDialect) {f : String}
    (h : fieldHeadB f = true) (as rs : List CryptoTy)
    (x : Valuation (d := catCryptDialect) as) :
    (catEnvOf (fieldEnv E)).call f as rs x =
      (catEnvOf (tableEnv _root_.Hax.hax64Builtins)).call f as rs x := by
  change Option.map backArgs ((fieldEnv E).call f _ _ _) =
    Option.map backArgs ((tableEnv _root_.Hax.hax64Builtins).call f _ _ _)
  rw [fieldEnv_of_fieldHeadB E h]

/-- `catEnvOf (fieldEnv E)` answers a name that is no field head as `catEnvOf E`. -/
theorem catEnvOf_fieldEnv_none (E : CallEnv jasminDialect) {f : String}
    (h : fieldHeadB f = false) (as rs : List CryptoTy)
    (x : Valuation (d := catCryptDialect) as) :
    (catEnvOf (fieldEnv E)).call f as rs x = (catEnvOf E).call f as rs x := by
  change Option.map backArgs ((fieldEnv E).call f _ _ _) =
    Option.map backArgs (E.call f _ _ _)
  rw [fieldEnv_of_none E h]

/-- **The declarations of the translation agree with the table and with
    `catEnvOf (fieldEnv E)`**, under `FieldLevel.FieldCalls bi`,
    `FieldLevel.FieldCallsWideEq bi` and the agreement of `bi` and `catEnvOf E` on `D`: a
    declaration of `D` kept by the filter has a name that is no
    field head, at which `fieldEnv E` is `E`; a declaration of a tagged head at a modulus
    below `2⁶⁴` is in the table by `fieldDecl_inTable` and implemented by the `u64` table
    (`implementedBy_tableEnv`), and one at a modulus of several words is in a table equal to
    the `u64` table at the wide heads (`FieldWideDecl.wideDecl_inTable`) and implemented by
    the `u64` table (`FieldWideDecl.wideDecl_implementedBy`). -/
theorem extAgree_fieldDeclsFor {bi : Builtins} (hF : FieldLevel.FieldCalls bi)
    (hW : FieldLevel.FieldCallsWideEq bi)
    {E : CallEnv jasminDialect} {D : List ExtDecl} (hD : ExtAgree bi (catEnvOf E) D)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (q : NFProg nfDialect Γ ts) :
    ExtAgree bi (catEnvOf (fieldEnv E)) (fieldDeclsFor D q) := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨hd, hn⟩ := List.mem_filter.mp hd
    obtain ⟨hT, hI⟩ := hD d hd
    exact ⟨hT, implementedBy_congr (fun as rs x => (catEnvOf_fieldEnv_none E
      (by simpa using hn) as rs x).symm) hI⟩
  · obtain ⟨m, p, ht, ⟨hp, hdm⟩ | ⟨hp, hdm⟩⟩ | ⟨m, p, k, ht, -, hodd, hp, hdm⟩ :=
      mem_fieldDeclsOf q hd
    · rw [hdm]
      refine ⟨fieldDecl_inTable hF ht hp, implementedBy_congr (fun as rs x =>
        (catEnvOf_fieldEnv_some E (by simp [fieldDecl, ht]) as rs x).symm) ?_⟩
      exact implementedBy_tableEnv _ d.name m.sig (.word 64) rfl (by cases m <;> decide)
    · rw [hdm]
      refine ⟨FieldWideDecl.wideDecl_inTable hW ht hp, implementedBy_congr (fun as rs x =>
        (catEnvOf_fieldEnv_some E (by simp [FieldWideDecl.wideDecl, ht]) as rs x).symm) ?_⟩
      exact FieldWideDecl.wideDecl_implementedBy d.name m p
    · rw [hdm]
      refine ⟨fieldDecl_inTable_mont hF ht hodd hp, implementedBy_congr (fun as rs x =>
        (catEnvOf_fieldEnv_of_fieldHeadB E
          (by simpa [fieldDecl] using _root_.Hax.FieldTag.fieldHeadB_of_fieldTagM? ht)
          as rs x).symm) ?_⟩
      exact implementedBy_tableEnv _ d.name m.sig (.word 64) rfl (by cases m <;> decide)

/-- The filter of the translation keeps the declared names and signatures that are no
    field heads. -/
theorem declared_filter_fieldTag (D : List ExtDecl) (f : String) (as : List NfTy)
    (r : NfTy) :
    declared (D.filter (fun d => !fieldHeadB d.name)) f as r =
      (!fieldHeadB f && declared D f as r) := by
  induction D with
  | nil => simp [declared]
  | cons d D ih =>
      simp only [declared] at ih ⊢
      have key : d.isAt f as r = true → d.name = f := fun hd => by
        simp only [ExtDecl.isAt, Bool.and_eq_true, decide_eq_true_eq] at hd
        exact hd.1.1.1
      rw [List.filter_cons]
      by_cases hd : d.isAt f as r = true
      · rw [key hd]
        cases hf : fieldHeadB f <;> simp [hd, ih, hf]
      · simp only [Bool.not_eq_true] at hd
        split <;> simp [hd, ih]

/-! ## The translation with declarations as a chain step -/

/-- The translation `nfToCatExt` at the declarations `fieldDeclsFor D p` of the program
    `p`, from the readings `TRd.id`, as a chain step, under the name of the step
    `nfToCatStep`. -/
def extCallStep (D : List ExtDecl) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    Step (NFProg nfDialect Γ ts) (NFProg catCryptDialect (Γ.map catTy) (ts.map catTy)) :=
  ⟨"nfToCat", fun p => nfToCatExt (fieldDeclsFor D p) p TRd.id⟩

/-- **The translation with declarations reads the declared names and signatures only**: two
    lists that declare the same names at the same signatures give the same translation. -/
theorem nfToCatExt_congr {D D' : List ExtDecl}
    (h : ∀ f as r, declared D f as r = declared D' f as r) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ), nfToCatExt D p σ = nfToCatExt D' p σ := by
  have hx : ∀ {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (op : NfOp)
      (args : HVector (fun t => Var Γ t) op.sig),
      extArgs D σ op args = extArgs D' σ op args := by
    intro Γ Δ σ op
    induction op with
    | named n op ih =>
        intro args
        exact ih args
    | call g bs r =>
        intro args
        simp only [extArgs, h]
    | _ =>
        intro args
        rfl
  induction p with
  | ret vs =>
      intro Δ σ
      rfl
  | var e k ih =>
      intro Δ σ
      obtain ⟨op, rfl, args⟩ := e
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args =
        emitOp D' (fun σ' => nfToCatExt D' k σ') σ op rfl args
      unfold emitOp
      simp only [ih, hx]
  | forLoop count inits body k ihb ihk =>
      intro Δ σ
      simp only [nfToCatExt, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ σ
      simp only [nfToCatExt, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk =>
      intro Δ σ
      simp only [nfToCatExt, ihb, ihk]
  | call f args k _ =>
      intro Δ σ
      rfl

/-- **The certificate of the translation with declarations**, from `nfToCatExt_sound`,
    between the source semantics at the builtin table `bi` and the semantics at the call
    environment `catEnvOf (fieldEnv E')`, under `SubTable bi`, `FieldLevel.FieldCalls bi`,
    `FieldLevel.FieldCallsWideEq bi` and `ExtAgree bi (catEnvOf E') D`, through
    `extAgree_fieldDeclsFor`, at a target fuel `cf` at least the source fuel `tf`: the input
    relation relates a valuation in range to its mapped valuation `mapVal`, and the output
    relation is `VRelL`. -/
def extCallCert {bi : Builtins} (hbi : SubTable bi) (hF : FieldLevel.FieldCalls bi)
    (hW : FieldLevel.FieldCallsWideEq bi) (tf cf : Nat) (hle : tf ≤ cf) {D : List ExtDecl}
    {E' : CallEnv jasminDialect}
    (hD : ExtAgree bi (catEnvOf E') D) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    StepCert (extCallStep D Γ ts).run (nfSemB bi tf Γ ts)
      (nfSemE (catEnvOf (fieldEnv E')) cf (Γ.map catTy) (ts.map catTy)) where
  relIn V W := W = mapVal V ∧ ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V)
  relOut o o' := VRelL ts o o'
  sound := by
    rintro p q V W o hf ⟨rfl, hin⟩ hd
    exact nfToCatExt_sound hbi tf (extAgree_fieldDeclsFor hF hW hD p) p TRd.id q hf V
      (mapVal V) o (TRd.agree_id V hin) hd cf hle

/-! ## Tuple flattening at a context and result types without tuples -/

section FlatSame

open CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples (flatTy flatCtx flatEnc flatV
  flattenTuples flattenTuples_sound flattenTuples_leakRunM flattenTuples_isSome NoTuple
  tyIsTuple TupleQuiet FlatOk)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-- The head and the tail of a list without tuple types have no tuple type. -/
theorem noTuple_cons {t : NfTy} {Γ : List NfTy} (h : NoTuple (t :: Γ)) :
    tyIsTuple t = false ∧ NoTuple Γ := by
  simpa [NoTuple] using h

/-- The components of a type that is no tuple type are the type itself. -/
theorem flatTy_of_tyIsTuple : ∀ t : NfTy, tyIsTuple t = false → flatTy t = [t]
  | .tnil, h | .tcons _ _, h | .unit, h => nomatch h
  | .bit, _ | .word _, _ | .arr _ _, _ | .pair _ _, _ | .uint _, _ | .sint _, _
  | .int, _ | .slice _, _ => rfl

/-- **A context without tuple types is its own flattening.** -/
theorem flatCtx_of_noTuple : ∀ {Γ : Ctxt nfDialect}, NoTuple Γ → flatCtx Γ = Γ
  | [], _ => rfl
  | t :: Γ, h => by
      have h' := noTuple_cons h
      show flatTy t ++ flatCtx Γ = t :: Γ
      rw [flatTy_of_tyIsTuple t h'.1, flatCtx_of_noTuple h'.2]
      rfl

/-- Extending heterogeneously equal valuations of equal contexts by one value gives
    heterogeneously equal valuations. -/
theorem valuation_cons_heq {t : NfTy} {Γ Γ' : Ctxt nfDialect} (h : Γ = Γ') (x : ⟦t⟧)
    {A : Valuation Γ} {B : Valuation Γ'} (hAB : HEq A B) :
    HEq (HVector.cons x A : Valuation (t :: Γ)) (HVector.cons x B : Valuation (t :: Γ')) := by
  subst h; cases hAB; rfl

/-- **The flattened valuation of a context without tuple types is the valuation.** -/
theorem flatV_heq : ∀ {Γ : Ctxt nfDialect}, NoTuple Γ → ∀ V : Valuation Γ, HEq (flatV V) V
  | [], _, .nil => HEq.rfl
  | t :: Γ, h, .cons x V => by
      have h' := noTuple_cons h
      have hc := flatCtx_of_noTuple h'.2
      show HEq (MultiBlockLowering.hvAppend (flatEnc x) (flatV V)) _
      cases t <;> first
        | exact valuation_cons_heq hc x (flatV_heq h'.2 V)
        | exact absurd h'.1 (by simp [tyIsTuple])

/-- An option mapped along a function heterogeneously equal to the identity is
    heterogeneously equal to the option. -/
theorem option_map_heq {α β : Type} (h : α = β) (f : β → α) (hf : ∀ x, HEq (f x) x)
    (o : Option β) : HEq (o.map f) o := by
  subst h
  have hf' : f = id := funext fun x => eq_of_heq (hf x)
  subst hf'
  cases o <;> rfl

instance instDecidableNoTuple (ss : List NfTy) : Decidable (NoTuple ss) :=
  inferInstanceAs (Decidable (_ = true))

/-- **Tuple flattening at a context and result types without tuple types**:
    `flattenTuples p`, at the source context and result types (`flatCtx_of_noTuple`); `none`
    at a tuple type of the context or of the results, and where `flattenTuples` refuses. -/
def flatSame {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    Option (NFProg nfDialect Γ ts) :=
  if h : NoTuple Γ ∧ NoTuple ts then
    (flattenTuples p).map (cast (by rw [flatCtx_of_noTuple h.1, flatCtx_of_noTuple h.2]))
  else none

/-- A function of a program and a valuation at a program cast along equal contexts and
    result types and a heterogeneously equal valuation is the function at the program and
    the valuation. -/
theorem app_cast_heq {β : Ctxt nfDialect → List NfTy → Type}
    (F : ∀ {Γ : Ctxt nfDialect} {ts : List NfTy}, NFProg nfDialect Γ ts → Valuation Γ → β Γ ts)
    {Γ Γ' : Ctxt nfDialect} {ts ts' : List NfTy} (hΓ : Γ' = Γ) (hts : ts' = ts)
    (e : NFProg nfDialect Γ' ts' = NFProg nfDialect Γ ts) (q : NFProg nfDialect Γ' ts')
    (V : Valuation Γ) (V' : Valuation Γ') (hV : HEq V' V) :
    HEq (F (cast e q) V) (F q V') := by
  subst hΓ hts; cases hV; rfl

/-- **A program `flatSame` returns is the flattened program.** The context and the result
    types have no tuple type, `flattenTuples p` returns a program `q0`, and every function
    of a program and a valuation at the result and `V` is the function at `q0` and the
    flattened `V`. -/
theorem flatSame_heq {β : Ctxt nfDialect → List NfTy → Type}
    (F : ∀ {Γ : Ctxt nfDialect} {ts : List NfTy}, NFProg nfDialect Γ ts → Valuation Γ → β Γ ts)
    {Γ : Ctxt nfDialect} {ts : List NfTy} {p q : NFProg nfDialect Γ ts}
    (hq : flatSame p = some q) (V : Valuation Γ) :
    NoTuple Γ ∧ NoTuple ts ∧
      ∃ q0, flattenTuples p = some q0 ∧ HEq (F q V) (F q0 (flatV V)) := by
  unfold flatSame at hq
  split at hq
  · rename_i h
    obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
    exact ⟨h.1, h.2, q0, hq0, app_cast_heq F (flatCtx_of_noTuple h.1)
      (flatCtx_of_noTuple h.2) _ q0 V (flatV V) (flatV_heq h.1 V)⟩
  · cases hq

/-- **`flatSame` keeps the denotation**, at every leaf table and fuel
    (`flattenTuples_sound`). -/
theorem flatSame_denote (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p q : NFProg nfDialect Γ ts} (hq : flatSame p = some q) (V : Valuation Γ) :
    @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts q V =
      @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts p V := by
  obtain ⟨-, hts, q0, hq0, hF⟩ := flatSame_heq (β := fun _ ts => Option (Valuation ts))
    (fun q V => @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel _ _ q V) hq V
  rw [flattenTuples_sound T fuel p hq0 V] at hF
  exact eq_of_heq (hF.trans (option_map_heq (congrArg Valuation (flatCtx_of_noTuple hts))
    flatV (flatV_heq hts) _))

/-- **`flatSame` keeps the events** of a leakage model in which every tuple operation is
    quiet, at every leaf table and fuel (`flattenTuples_leakRunM`). -/
theorem flatSame_leakRunM (M : ComLevelCheck.LeakModel nfDialect) (hM : TupleQuiet M)
    (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p q : NFProg nfDialect Γ ts} (hq : flatSame p = some q) (V : Valuation Γ) :
    (@NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel Γ ts q V).map Prod.snd =
      (@NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel Γ ts p V).map Prod.snd := by
  obtain ⟨-, -, q0, hq0, hF⟩ := flatSame_heq (β := fun _ _ => Option (List _))
    (fun q V => (@NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel _ _ q V).map
      Prod.snd) hq V
  rw [eq_of_heq hF, flattenTuples_leakRunM M hM T fuel p hq0 V, Option.map_map]
  rfl

/-- **`flatSame` succeeds** at a context and result types without tuple types on a program
    every operation of which `flattenTuples` accepts (`flattenTuples_isSome`). -/
theorem flatSame_isSome {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (hΓ : NoTuple Γ) (hts : NoTuple ts) (hp : FlatOk p) : (flatSame p).isSome = true := by
  unfold flatSame
  rw [dite_eq_left ⟨hΓ, hts⟩, Option.isSome_map]
  exact flattenTuples_isSome p hp

end FlatSame

/-- Tuple flattening at a context and result types without tuple types as a chain step. -/
def flatSameStep (Γ : Ctxt nfDialect) (ts : List NfTy) :
    Step (NFProg nfDialect Γ ts) (NFProg nfDialect Γ ts) :=
  ⟨"flattenTuples", flatSame⟩

/-- The certificate of `flatSameStep`, at equal inputs and outputs (`flatSame_denote`). -/
def flatSameCert (bi : Builtins) (tf : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    StepCert (flatSameStep Γ ts).run (nfSemB bi tf Γ ts) (nfSemB bi tf Γ ts) :=
  StepCert.ofRefines _ fun _ _ V _ hf hd =>
    (flatSame_denote (tableOf bi) tf hf V).trans hd

/-- **The conversion step of the chain with declarations does not refuse.** When the
    translation step returns `q` and the e-graph step at `catRules` returns `r` on `q`, the
    step `mapStep catToJasmin` returns a program on `r`
    (`isSome_map?_aegraphOptNF_nfToCatExt`). -/
theorem extChain_mapStep_isSome (D : List ExtDecl) (Γ : Ctxt nfDialect) (ts : List NfTy)
    (p : NFProg nfDialect Γ ts) (q r : NFProg catCryptDialect (Γ.map catTy) (ts.map catTy))
    (hq : (extCallStep D Γ ts).run p = some q)
    (hr : (aegraphStep catRules (Γ.map catTy) (ts.map catTy)).run q = some r) :
    ((mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) (ts.map catTy)).run
      r).isSome := by
  cases hr
  exact isSome_map?_aegraphOptNF_nfToCatExt (fieldDeclsFor D p) p TRd.id q hq (fun v => v)

/-! ## The region front of an entry -/

/-- The signatures of the declarations `D` in `jasminDialect`: the name of each, with the
    mapped types of its arguments and of its result. -/
def declSigs (D : List ExtDecl) : List (String × List JasminTy × List JasminTy) :=
  D.map fun d => (d.name, (d.args.map catTy).map mapTy, [mapTy (catTy d.ret)])

/-! ## The procedure summaries of the linked functions of a module -/

/-- The parameter kind of an argument type of a call: an array of `n` words at
    `stackArr _ n`, a scalar at every other type. -/
def kindOfTy : JasminTy → ArgKind
  | .stackArr _ n => .words n
  | _ => .scalar

/-- The parameter kind of a source value: an array of as many words as its elements, a
    scalar at every other value. -/
def valKind : _root_.Hax.Value → ArgKind
  | .array ys => .words ys.length
  | _ => .scalar

/-- The array positions of the kinds of argument types are the array positions of the
    types. -/
theorem insArrArgs_eq_arrArgsOf : ∀ as : List JasminTy,
    CatCrypt.Crypto.Hax.insArrArgs (as.map kindOfTy) = arrArgsOf as
  | [] => rfl
  | t :: as => by
      funext i
      cases i with
      | zero => cases t <;> rfl
      | succ i =>
          rw [arrArgsOf_cons_succ, ← insArrArgs_eq_arrArgsOf as]
          cases t <;> rfl

/-- **The source values of the words of a valuation of words and word arrays**, read under
    the kinds of its types, are the source values of the valuation. -/
theorem insVals_wordsOf : ∀ {as : List JasminTy}, (∀ t ∈ as, callArgTy t = true) →
    ∀ a : Valuation (d := jasminDialect) as,
      CatCrypt.Crypto.Hax.insVals (as.map kindOfTy) (wordsOf a) = denVals a
  | [], _, .nil => rfl
  | t :: as, h, .cons x W => by
      have ih := insVals_wordsOf (fun t ht => h t (List.mem_cons_of_mem _ ht)) W
      have ht := h t List.mem_cons_self
      cases t with
      | reg w =>
          obtain rfl : w = 64 := by simpa [callArgTy] using ht
          change CatCrypt.Crypto.Hax.wordVal (x.setWidth 64) ::
            CatCrypt.Crypto.Hax.insVals (as.map kindOfTy) (wordsOf W) =
              denVal (.reg 64) x :: denVals W
          rw [ih, BitVec.setWidth_eq]
          rfl
      | stackArr w n =>
          obtain rfl : w = 64 := by simpa [callArgTy] using ht
          have hl : (List.ofFn fun j => (x j).setWidth 64).length = n := List.length_ofFn
          change _root_.Hax.Value.array
              (((List.ofFn fun j => (x j).setWidth 64) ++ wordsOf W).take n |>.map
                CatCrypt.Crypto.Hax.wordVal) ::
            CatCrypt.Crypto.Hax.insVals (as.map kindOfTy)
              (((List.ofFn fun j => (x j).setWidth 64) ++ wordsOf W).drop n) =
              arrVal x :: denVals W
          rw [List.take_left' hl, List.drop_left' hl, ih]
          refine congrArg (· :: denVals W) (congrArg _root_.Hax.Value.array ?_)
          refine List.ext_getElem (by simp) fun j h1 h2 => ?_
          have hj : j < n := by simpa using h2
          simp only [List.getElem_map, List.getElem_ofFn, List.getElem_range,
            BitVec.setWidth_eq, CatCrypt.Crypto.Hax.wordVal]
          cases n with
          | zero => omega
          | succ k =>
              change _root_.Hax.Value.int (x ⟨j, _⟩).toNat =
                _root_.Hax.Value.int (x ⟨j % (k + 1), _⟩).toNat
              simp only [Nat.mod_eq_of_lt hj]
      | inlineInt => simp [callArgTy] at ht
      | bool => simp [callArgTy] at ht

/-- The kinds of the source values of a valuation of words and word arrays are the kinds of
    its types. -/
theorem map_valKind_denVals : ∀ {as : List JasminTy}, (∀ t ∈ as, callArgTy t = true) →
    ∀ a : Valuation (d := jasminDialect) as, (denVals a).map valKind = as.map kindOfTy
  | [], _, .nil => rfl
  | t :: as, h, .cons x W => by
      have ih := map_valKind_denVals (fun t ht => h t (List.mem_cons_of_mem _ ht)) W
      have ht := h t List.mem_cons_self
      cases t with
      | reg w =>
          obtain rfl : w = 64 := by simpa [callArgTy] using ht
          change valKind (denVal (.reg 64) x) :: (denVals W).map valKind = _
          rw [ih]
          rfl
      | stackArr w n =>
          obtain rfl : w = 64 := by simpa [callArgTy] using ht
          change valKind (arrVal x) :: (denVals W).map valKind = _
          rw [ih]
          simp [valKind, arrVal, kindOfTy]
      | inlineInt => simp [callArgTy] at ht
      | bool => simp [callArgTy] at ht

/-- The length of an array result type; `none` at every other type. -/
def arrLen? : NfTy → Option Nat
  | .arr n _ => some n
  | _ => none

/-- A value that `dec` decodes as an array of `n` values is a source array of `n`
    values. -/
theorem dec_arr_eq_some {n : Nat} {t : NfTy} {u : _root_.Hax.Value} {y : (NfTy.arr n t).denote}
    (h : dec (.arr n t) u = some y) : ∃ vs, u = .array vs ∧ vs.length = n := by
  cases u with
  | array vs =>
      refine ⟨vs, rfl, ?_⟩
      simp only [dec, Option.bind_eq_some_iff] at h
      obtain ⟨ys, hys, h⟩ := h
      split at h
      · rename_i hl
        rw [← hl, length_of_mapM_eq_some hys]
      · cases h
  | _ => simp [dec] at h

/-- A result type other than a slice at which `dec` decodes a source array is an array type
    of the length of the source array. -/
theorem arrLen?_of_dec {r : NfTy} (hr : ∀ t, r ≠ .slice t) {vs : List _root_.Hax.Value}
    (h : (dec r (.array vs)).isSome = true) : arrLen? r = some vs.length := by
  cases r with
  | arr k t =>
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨vs', he, hl⟩ := dec_arr_eq_some hy
      cases he
      rw [hl]
      rfl
  | slice t => exact absurd rfl (hr t)
  | _ => simp [dec] at h

/-- The parameter kinds of a linked function: the kind of the argument type of each
    parameter type in `jasminDialect`. -/
def linkedKinds (l : CatCrypt.Crypto.Hax.LinkedFn) : List ArgKind :=
  l.params.map fun p => kindOfTy (mapTy (catTy p.2))

/-- **The procedure summary of a linked function**: its arity is the number of its
    parameters and its array positions are those of its parameter kinds `linkedKinds`; its
    function reads the argument words under those kinds as source values (`insVals`),
    applies the meaning `LinkedFn.sem` and decodes the value as a `64`-bit word; its result
    length is the length of an array result type, and its array function decodes the value
    of the meaning as an array of words. -/
def linkedSummary (l : CatCrypt.Crypto.Hax.LinkedFn) : LprogIsa.ProcSummary where
  arity := l.params.length
  run ws := (l.sem (CatCrypt.Crypto.Hax.insVals (linkedKinds l) ws)).bind (dec (.word 64))
  arrArgs := CatCrypt.Crypto.Hax.insArrArgs (linkedKinds l)
  out := arrLen? l.res
  runOut n ws := (l.sem (CatCrypt.Crypto.Hax.insVals (linkedKinds l) ws)).bind
    (dec (.arr n (.word 64)))

/-- The summary of a linked function whose parameters are scalars has only word
    arguments. -/
theorem linkedSummary_wordOnly {l : CatCrypt.Crypto.Hax.LinkedFn}
    (h : ∀ p ∈ l.params, kindOfTy (mapTy (catTy p.2)) = .scalar) :
    (linkedSummary l).WordOnly :=
  CatCrypt.Crypto.Hax.insArrArgs_of_scalars fun k hk => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    exact h p hp

/-- The summary of a linked function whose result type is no array has no word-array
    result. -/
theorem linkedSummary_retWord {l : CatCrypt.Crypto.Hax.LinkedFn}
    (h : ∀ n t, l.res ≠ .arr n t) : (linkedSummary l).RetWord := by
  change arrLen? l.res = none
  cases hr : l.res with
  | arr n t => exact absurd hr (h n t)
  | _ => rfl

/-- **The summary of a linked function has its declared result kind.** With an array result
    type, the meaning decodes at that type (`LinkedFn.sem_res`), hence to a source array,
    which the word decoding of `run` refuses. -/
theorem linkedSummary_kinded (l : CatCrypt.Crypto.Hax.LinkedFn) : (linkedSummary l).Kinded := by
  intro n hn ws
  obtain ⟨tl, hres⟩ : ∃ tl, l.res = .arr n tl := by
    change arrLen? l.res = some n at hn
    cases h : l.res <;> simp_all [arrLen?]
  change (l.sem _).bind (dec (.word 64)) = none
  cases hs : l.sem (CatCrypt.Crypto.Hax.insVals (linkedKinds l) ws) with
  | none => rfl
  | some v =>
      have hd := l.sem_res _ v hs
      rw [hres] at hd
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hd
      obtain ⟨vs, rfl, -⟩ := dec_arr_eq_some hy
      simp [dec]

/-- **The table of procedure summaries of a module over the table `T`**: the summary
    `linkedSummary` of the first linked function with a name, and the summary of `T` at
    every other name. It reads its linked functions in the order of
    `HaxModule.linkTable`. -/
def procTableOf (m : CatCrypt.Crypto.Hax.HaxModule) (T : ProcTable) : ProcTable := fun f =>
  match m.linked.find? (·.name == f) with
  | some l => some (linkedSummary l)
  | none => T f

/-- At a name no linked function of `m` has, the environment of the table of the linked
    functions is the environment of the base table. -/
theorem tableEnv_linkTable_of_find_none {bi : Builtins} {m : CatCrypt.Crypto.Hax.HaxModule}
    {f : String} (hf : m.linked.find? (·.name == f) = none) (as rs : List JasminTy)
    (a : Valuation (d := jasminDialect) as) :
    (tableEnv (m.linkTable bi)).call f as rs a = (tableEnv bi).call f as rs a := by
  simp only [tableEnv, CatCrypt.Crypto.Hax.HaxModule.linkTable,
    CatCrypt.Crypto.Hax.linkBi_of_find_none _ _ hf]

/-- **The summaries of the linked functions of a module agree with the environment of its
    table.** Let every linked function of `m` return values only on argument lists whose
    kinds (`valKind`) are its parameter kinds `linkedKinds`, let no result type of a linked
    function be a slice, and let the table `T` agree with the environment `tableEnv bi` of the
    base table. Then the table `procTableOf m T` agrees with the environment
    `tableEnv (m.linkTable bi)` of the table of the linked functions of `m`, at word and at
    word-array results. -/
theorem procsAgree_tableEnv_linkTable {bi : Builtins} {T : ProcTable}
    (m : CatCrypt.Crypto.Hax.HaxModule)
    (hargs : ∀ l ∈ m.linked, ∀ vals v, l.sem vals = some v →
      vals.map valKind = linkedKinds l)
    (hres : ∀ l ∈ m.linked, ∀ t, l.res ≠ .slice t)
    (hT : ProcsAgree (tableEnv bi) T) :
    ProcsAgree (tableEnv (m.linkTable bi)) (procTableOf m T) := by
  have key : ∀ (l : CatCrypt.Crypto.Hax.LinkedFn), l ∈ m.linked → ∀ (as : List JasminTy),
      (∀ t ∈ as, callArgTy t = true) → ∀ (a : Valuation (d := jasminDialect) as) u,
      l.sem (denVals a) = some u →
      (linkedSummary l).arity = as.length ∧ (linkedSummary l).arrArgs = arrArgsOf as ∧
        CatCrypt.Crypto.Hax.insVals (linkedKinds l) (wordsOf a) = denVals a := by
    intro l hl as has a u hu
    have hk : as.map kindOfTy = linkedKinds l := by
      rw [← map_valKind_denVals has a]
      exact hargs l hl _ _ hu
    refine ⟨?_, ?_, ?_⟩
    · show l.params.length = as.length
      have := congrArg List.length hk
      simp only [linkedKinds, List.length_map] at this
      exact this.symm
    · show CatCrypt.Crypto.Hax.insArrArgs (linkedKinds l) = arrArgsOf as
      rw [← hk, insArrArgs_eq_arrArgsOf]
    · rw [← hk, insVals_wordsOf has]
  refine ⟨fun f as has a v hcall => ?_, fun f as n has a v hcall => ?_⟩
  · cases hf : m.linked.find? (·.name == f) with
    | none =>
        rw [tableEnv_linkTable_of_find_none hf] at hcall
        obtain ⟨pr, h1, h2, h3, h4⟩ := hT.1 f as has a v hcall
        exact ⟨pr, by simp only [procTableOf, hf, h1], h2, h3, h4⟩
    | some l =>
        have hc : ((l.sem (denVals a)).bind fun v =>
            (dec (.word 64) v).map fun y =>
              (HVector.cons y .nil : Valuation (d := jasminDialect) [.reg 64])) = some v := by
          simpa only [tableEnv, CatCrypt.Crypto.Hax.HaxModule.linkTable,
            CatCrypt.Crypto.Hax.linkBi_of_find_some _ _ hf] using hcall
        obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.mp hc
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hd
        obtain ⟨h1, h2, h3⟩ := key l (List.mem_of_find?_eq_some hf) as has a u hu
        refine ⟨linkedSummary l, by simp only [procTableOf, hf], h1, h2, ?_⟩
        show (l.sem (CatCrypt.Crypto.Hax.insVals (linkedKinds l) (wordsOf a))).bind
          (dec (.word 64)) = some y
        rw [h3, hu, Option.bind_some, hy]
  · cases hf : m.linked.find? (·.name == f) with
    | none =>
        rw [tableEnv_linkTable_of_find_none hf] at hcall
        obtain ⟨pr, h1, h2, h3, h4, h5, h6⟩ := hT.2 f as n has a v hcall
        exact ⟨pr, by simp only [procTableOf, hf, h1], h2, h3, h4, h5, h6⟩
    | some l =>
        have hl := List.mem_of_find?_eq_some hf
        have hc : ((l.sem (denVals a)).bind fun v =>
            (dec (.arr n (.word 64)) v).map fun y =>
              (HVector.cons y .nil : Valuation (d := jasminDialect) [.stackArr 64 n])) =
              some v := by
          simpa only [tableEnv, CatCrypt.Crypto.Hax.HaxModule.linkTable,
            CatCrypt.Crypto.Hax.linkBi_of_find_some _ _ hf] using hcall
        obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.mp hc
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hd
        obtain ⟨vs, rfl, hvs⟩ := dec_arr_eq_some hy
        obtain ⟨h1, h2, h3⟩ := key l hl as has a _ hu
        refine ⟨linkedSummary l, by simp only [procTableOf, hf], h1, h2, ?_, ?_, ?_⟩
        · show (l.sem (CatCrypt.Crypto.Hax.insVals (linkedKinds l) (wordsOf a))).bind
            (dec (.word 64)) = none
          rw [h3, hu, Option.bind_some]
          rfl
        · show arrLen? l.res = some n
          rw [arrLen?_of_dec (hres l hl) (l.sem_res _ _ hu), hvs]
        · show (l.sem (CatCrypt.Crypto.Hax.insVals (linkedKinds l) (wordsOf a))).bind
            (dec (.arr n (.word 64))) = some y
          rw [h3, hu, Option.bind_some, hy]

/-- The empty table agrees with the environment of a table none of whose values decodes as
    a `64`-bit word or as an array of `64`-bit words. -/
theorem procsAgree_tableEnv_empty {bi : Builtins}
    (h : ∀ f vals v, bi f vals = some v →
      dec (.word 64) v = none ∧ ∀ n, dec (.arr n (.word 64)) v = none) :
    ProcsAgree (tableEnv bi) LprogIsa.ProcTable.empty := by
  refine ⟨fun f as _ a v hcall => ?_, fun f as n _ a v hcall => ?_⟩
  · have hc : ((bi f (denVals a)).bind fun v =>
        (dec (.word 64) v).map fun y =>
          (HVector.cons y .nil : Valuation (d := jasminDialect) [.reg 64])) = some v := hcall
    obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.mp hc
    rw [(h f _ u hu).1] at hd
    cases hd
  · have hc : ((bi f (denVals a)).bind fun v =>
        (dec (.arr n (.word 64)) v).map fun y =>
          (HVector.cons y .nil : Valuation (d := jasminDialect) [.stackArr 64 n])) =
          some v := hcall
    obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.mp hc
    rw [(h f _ u hu).2 n] at hd
    cases hd

end CatCrypt.Crypto.SecureCompilation.Haxc
