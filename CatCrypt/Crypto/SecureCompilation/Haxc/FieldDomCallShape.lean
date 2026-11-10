/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomSplice
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomLetsOnly

/-!
# The store-chain shape of the output of the chain on the field domain

The translation of a member of the field domain binds the call of its tagged head and returns
it. Tuple flattening, dead-binding elimination, the translation to `catCryptDialect` (which
refuses no call of a tagged head in `catOp` and declares it), the e-graph pass and the lowering
to `jasminDialect` keep one call returned; the montify pass is the identity at a modulus of at
least `2 ^ 64`; and the field dialect step replaces the call by the lowered body of the head,
of the shape `LoadsChain`, before the return of its result. The later steps, the narrow-word
stages and the legalisation keep the shape.

## Main definitions

* `OpRet`: one binding of an operation, returned.
* `CallRet`: one call of a symbol, returned.

## Main results

* `fieldDom_haxToNF_opRet`: the translation of a member of the field domain binds the call of
  its head and returns it.
* `flatSame_callRet`, `dce_opRet`, `nfToCatExt_callRet`, `aegraphOptNF_callRet`,
  `map?_catToJasmin_callRet`: the steps before the field dialect step keep the call returned.
* `quietCall_of_tagged`, `catOp_tagged`: `catOp` refuses the call of a tagged head.
* `fieldDialectStep_loadsChain`: the field dialect step takes one call of a tagged head at a
  modulus without a narrow representation and with a wide template to a program of the shape
  `LoadsChain`.
* `extChain_loadsChain`, `fieldDom_chain_loadsChain`, `fieldDom_legalize_loadsChain`: the
  output of the chain on a member of the field domain, and the program the export receives,
  have the shape `LoadsChain`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open Ctxt (Var)

/-- **One binding of the operation `op`, returned**: the program binds `op` and returns the
    bound variable. -/
def OpRet {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d]
    (op : d.Op) {Γ : Ctxt d} {t : d.Ty} (p : NFProg d Γ [t]) : Prop :=
  ∃ (h : DialectSignature.ret op = t)
    (args : HVector (fun s => Var Γ s) (DialectSignature.sig op)),
    p = .var ⟨op, h, args⟩ (.ret (.cons .here .nil))

/-- The translation of `let t := f(x, a); t` binds the call `f` named `t` and returns it. -/
theorem impToNF_letCall_opRet {Γ : Ctxt nfDialect} (σ : CatCrypt.Crypto.Hax.ImpToNF.NfEnv Γ)
    (f a : String) (T : NfTy)
    (vx va : Var Γ T) (hx : σ.lookup "x" = some ⟨T, vx⟩) (ha : σ.lookup a = some ⟨T, va⟩)
    (hf : f ≠ "repeat") (hs : CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf f [T, T] = some T) :
    ∃ o, CatCrypt.Crypto.Hax.ImpToNF.impToNF CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf none σ
      (.letBind "t" (.app f [.var "x", .var a]) (.var "t")) = some o ∧
      OpRet (NfOp.named "t" (.call f [T, T] T)) o.prog := by
  simp [CatCrypt.Crypto.Hax.ImpToNF.impToNF, CatCrypt.Crypto.Hax.ImpToNF.impArgsNF,
    CatCrypt.Crypto.Hax.ImpToNF.atomOut, hx, ha, hf, hs,
    CatCrypt.Crypto.Hax.ImpToNF.NfEnv.lookup_cons,
    CatCrypt.Crypto.Hax.ImpToNF.Out.comp, CatCrypt.Crypto.Hax.ImpToNF.Out.prog,
    CatCrypt.Crypto.Hax.ImpToNF.mkEN, NFPre.plug, NFPre.append, OpRet]
  rfl

open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.Hax.ImpToNF (entryEnv NfEnv)
open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag? fieldLimbs)

/-- **The translation of a member of the field domain binds the call of its head and returns
    it**, at a modulus of at least `2 ^ 64` with a wide template. -/
theorem fieldDom_haxToNF_opRet {e : _root_.Hax.TExpr} {σ : AbiLayout} (h : fieldDomB e σ = true)
    {T : NfTy} {p0 : NFProg nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (abiEntry σ)) [T]}
    (hp : haxToNF σ (HaxModule.single e) = some ⟨T, p0⟩) :
    ∃ m p, fieldTag? (fieldHead m p) = some (m, p) ∧ 2 ^ 64 ≤ p ∧
      (FieldWideInline.wideTemplateOf p).isSome = true ∧
      T = NfTy.arr (fieldLimbs p) (.word 64) ∧
      OpRet (NfOp.named "t" (.call (fieldHead m p)
        [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)]
        (NfTy.arr (fieldLimbs p) (.word 64)))) p0 := by
  unfold fieldDomB at h
  split at h
  · rename_i k n hkn
    obtain ⟨m, p, hm, h64, hok, ht, rfl, he⟩ := fieldDomE_tag hkn
    have hW : (FieldWideInline.wideTemplateOf p).isSome = true := by
      have hok' := hok
      simp only [CatCrypt.Crypto.Hax.ImpToNF.fieldModOk, CatCrypt.Crypto.Hax.ImpToNF.fieldNarrowOk,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true]
        at hok'
      rcases hok' with ⟨⟨-, hodd⟩, hn⟩ | ⟨_, -, ⟨⟨-, hle⟩, -⟩⟩
      · obtain ⟨W, hW⟩ := FieldWideInline.wideTemplateOf_isSome h64 hodd hn
        simp [hW]
      · omega
    simp only [fieldAbiB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨⟨hargs, hc⟩, -⟩, -⟩, -⟩, -⟩ := h
    have hfr := fieldLit_front m p k
    have hsh : CatCrypt.Crypto.Hax.haxFrontShapeOk e = true := by
      rw [CatCrypt.Crypto.Hax.haxFrontShapeOk, he]
      exact hfr.1
    have hbody : nfBody e = fieldLit m p k := by
      rw [nfBody, he]
      exact hfr.2
    have hbin : m.binary = true := by
      simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | h <;>
        first | rfl | cases h
    have hsig := hax64SigOf_fieldHead hbin h64 hok ht
    have hk : k = 2 ∨ k = 1 := by
      simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at hm
      grind
    have hI : ∃ o, CatCrypt.Crypto.Hax.ImpToNF.impToNF CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf
        none (entryEnv (abiEntry σ)) (fieldLit m p k) = some o ∧
        OpRet (NfOp.named "t" (.call (fieldHead m p)
          [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)]
          (NfTy.arr (fieldLimbs p) (.word 64)))) o.prog := by
      rcases hk with rfl | rfl
      · rw [abiEntry_fieldAbi_two hargs]
        exact impToNF_letCall_opRet (entryEnv _) (fieldHead m p) "y" _ Var.here Var.here.there
          (by simp [entryEnv_lookup_cons]) (by simp [entryEnv_lookup_cons])
          (fieldHead_ne_repeat m p) hsig
      · rw [abiEntry_fieldAbi_one hargs]
        exact impToNF_letCall_opRet (entryEnv _) (fieldHead m p) "x" _ Var.here Var.here
          (by simp [entryEnv_lookup_cons]) (by simp [entryEnv_lookup_cons])
          (fieldHead_ne_repeat m p) hsig
    obtain ⟨o, ho, hop⟩ := hI
    have hot : o.t = NfTy.arr (fieldLimbs p) (.word 64) := by
      obtain ⟨h1, -, -⟩ := hop
      exact h1.symm
    have hp' : haxToNF σ (HaxModule.single e) = some ⟨o.t, o.prog⟩ := by
      rw [haxToNF_single, hc, bindConsts_nil]
      simp [nfSrcProg, hsh, hbody, ho, hot, entryResOk, outTyB]
    rw [hp] at hp'
    simp only [Option.some.injEq, Sigma.mk.injEq] at hp'
    obtain ⟨rfl, hq⟩ := hp'
    cases hq
    exact ⟨m, p, ht, h64, hW, hot, hop⟩
  · cases h

/-- `OpRet` is kept along an equality of contexts. -/
theorem opRet_heq {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] {op : d.Op} {Γ₁ Γ₂ : Ctxt d} {t : d.Ty} (hΓ : Γ₁ = Γ₂)
    {y : NFProg d Γ₂ [t]} {x : NFProg d Γ₁ [t]} (hxy : HEq y x) (hx : OpRet op x) :
    OpRet op y := by
  subst hΓ
  cases eq_of_heq hxy
  exact hx

/-- **Tuple flattening keeps one call bound and returned**, at an array type. -/
theorem flatSame_callRet {Γ : Ctxt nfDialect} {f : String} {n : Nat}
    {args : HVector (fun s => Var Γ s)
      (DialectSignature.sig (NfOp.named "t" (.call f [NfTy.arr n (.word 64), NfTy.arr n (.word 64)]
        (NfTy.arr n (.word 64)))))}
    {q : NFProg nfDialect Γ [NfTy.arr n (.word 64)]}
    (hq : flatSame (.var ⟨NfOp.named "t" (.call f [NfTy.arr n (.word 64), NfTy.arr n (.word 64)]
        (NfTy.arr n (.word 64))), rfl, args⟩ (.ret (.cons .here .nil))) = some q) :
    OpRet (NfOp.named "t" (.call f [NfTy.arr n (.word 64), NfTy.arr n (.word 64)]
      (NfTy.arr n (.word 64)))) q := by
  unfold flatSame at hq
  split at hq
  · rename_i hT
    obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
    simp only [NFFlattenTuples.flattenTuples, NFFlattenTuples.flatProg,
      NFFlattenTuples.tupleHom?, NFFlattenTuples.atomRet?] at hq0
    obtain ⟨args', -, hq0⟩ := Option.bind_eq_some_iff.mp hq0
    obtain rfl := Option.some.inj hq0
    exact opRet_heq (flatCtx_of_noTuple hT.1) (cast_heq _ _) ⟨rfl, args', rfl⟩
  · cases hq

/-- **One call bound and returned**: the program calls `f` with one result and returns it. -/
def CallRet {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] (f : String) {Γ : Ctxt d} {t : d.Ty} (p : NFProg d Γ [t]) : Prop :=
  ∃ (as : List d.Ty) (args : HVector (fun s => Var Γ s) as),
    p = .call (rs := [t]) f args (.ret (.cons .here .nil))

open CatCrypt.Crypto.Hax.NFToCat (quietCall TRd catOp)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)

/-- No quiet call is a tagged field head. -/
theorem quietCall_of_tagged {f : String} (hf : (fieldTag? f).isSome = true) :
    quietCall f = false := by
  have hn : ∀ g ∈ CatCrypt.Crypto.Hax.ImpToNF.hax64NFScalar (),
      (fieldTag? g).isSome = false := by
    decide
  cases hq : quietCall f
  · rfl
  · rcases CatCrypt.Crypto.Hax.NFToCat.quietCall_iff.mp hq with h' | rfl | rfl | rfl
    · rw [hn f h'] at hf
      cases hf
    all_goals exact absurd hf (by decide)

/-- **`catOp` refuses the call of a tagged field head.** -/
theorem catOp_tagged {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    (σ : TRd Γ Δ) {f : String} (hf : (fieldTag? f).isSome = true)
    (n : String) (as : List NfTy) (r : NfTy)
    (args : HVector (fun t => Var Γ t) (NfOp.named n (.call f as r)).sig) :
    catOp σ (NfOp.named n (.call f as r)) args = none := by
  cases h : catOp σ (NfOp.named n (.call f as r)) args with
  | none => rfl
  | some res =>
      simp only [catOp] at h
      rcases CatCrypt.Crypto.Hax.NFToCat.catCallRd_name h with rfl | rfl | hq
      · exact absurd rfl (CatCrypt.Crypto.Hax.NFToCat.ne_index_of_tagged hf).1
      · exact absurd rfl (CatCrypt.Crypto.Hax.NFToCat.ne_index_of_tagged hf).2
      · rw [quietCall_of_tagged hf] at hq
        cases hq

/-- Dead-binding elimination keeps one binding returned. -/
theorem dce_opRet {Γ : Ctxt nfDialect} {t : NfTy} {op : NfOp} {p : NFProg nfDialect Γ [t]}
    (hp : OpRet op p) : OpRet op p.dce := by
  obtain ⟨h, args, rfl⟩ := hp
  exact ⟨h, args, rfl⟩

/-- **The translation to `catCryptDialect` of one call of a tagged head bound and returned** is
    one call returned. -/
theorem nfToCatExt_callRet (D : List CatCrypt.Crypto.Hax.NFToCat.ExtDecl) {Γ : Ctxt nfDialect}
    {f : String} (hf : (fieldTag? f).isSome = true) {A : NfTy}
    {p : NFProg nfDialect Γ [A]} (hp : OpRet (NfOp.named "t" (.call f [A, A] A)) p)
    {r : NFProg catCryptDialect (Γ.map CatCrypt.Crypto.Hax.NFToCat.catTy)
      ([A].map CatCrypt.Crypto.Hax.NFToCat.catTy)}
    (hr : CatCrypt.Crypto.Hax.NFToCat.nfToCatExt D p TRd.id = some r) : CallRet f r := by
  obtain ⟨h, args, rfl⟩ := hp
  simp only [CatCrypt.Crypto.Hax.NFToCat.nfToCatExt, CatCrypt.Crypto.Hax.NFToCat.emitOp,
    catOp_tagged _ hf] at hr
  obtain ⟨c, hc, hr⟩ := Option.bind_eq_some_iff.mp hr
  simp only [CatCrypt.Crypto.Hax.NFToCat.extArgs] at hc
  split at hc
  · cases hc
    simp only [CatCrypt.Crypto.Hax.NFToCat.emitCall] at hr
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    rw [CatCrypt.Crypto.Hax.NFToCat.pinAll_of_pinVars _ _ _ _ rfl,
      CatCrypt.Crypto.Hax.NFToCat.pinAll_of_pinVars _ _ _ _ rfl] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    exact ⟨_, _, rfl⟩
  · cases hc

open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)

/-- **The e-graph pass at the rules of `catCryptDialect` keeps one call returned.** -/
theorem aegraphOptNF_callRet {f : String} {Γ : Ctxt catCryptDialect} {t : catCryptDialect.Ty}
    {p : NFProg catCryptDialect Γ [t]} (hp : CallRet f p) :
    CallRet f (CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF catRules p) := by
  obtain ⟨as, args, rfl⟩ := hp
  exact ⟨_, _, rfl⟩

/-- **The lowering to `jasminDialect` keeps one call returned.** -/
theorem map?_catToJasmin_callRet {f : String} {Γ : Ctxt catCryptDialect} {t : catCryptDialect.Ty}
    {p : NFProg catCryptDialect Γ [t]} (hp : CallRet f p) {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom (catToJasmin.mapCtx Γ) Δ)
    {q : NFProg jasminDialect Δ ([t].map catToJasmin.mapTy)}
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes p ren = some q) : CallRet f q := by
  obtain ⟨as, args, rfl⟩ := hp
  simp only [NFProg.map?, Option.map_some, Option.some.injEq] at hq
  subst hq
  exact ⟨_, _, rfl⟩

open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)

/-- The lowered body of a tagged head at a modulus without a narrow representation and with a
    wide template returns one array of `fieldLimbs p` words. -/
theorem fieldBodyD_rs {f : String} {m : FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : fieldTag? f = some (m, p))
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : FieldDialectStep.fieldBodyD f as rs = some b) :
    rs = [.stackArr 64 (fieldLimbs p)] := by
  obtain ⟨-, r₁, hr₁, -⟩ := FieldDialectStep.fieldBodyD_some hb
  unfold FieldRaise.raiseBody at hr₁
  rw [ht] at hr₁
  simp only [hn, hw] at hr₁
  unfold FieldRaise.raiseArr at hr₁
  split at hr₁
  · rename_i hs
    exact List.map_injective_iff.mpr Sum.inl_injective (hs.2.trans rfl)
  · cases hr₁

/-- **The field dialect step takes one call of a tagged head at a modulus without a narrow
    representation and with a wide template, returned, to a program of the shape
    `LoadsChain`**: the call is replaced by the lowered body (`fieldBodyD_loadsChain`), whose
    last stored array the continuation returns. -/
theorem fieldDialectStep_loadsChain {f : String} {m : FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : fieldTag? f = some (m, p))
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p₀ q : NFProg jasminDialect Γ [t]} (hp : CallRet f p₀)
    (hq : (FieldDialectStep.fieldDialectStep Γ [t]).run p₀ = some q) : LoadsChain q := by
  obtain ⟨as, args, rfl⟩ := hp
  have hf := _root_.Hax.FieldTag.fieldHeadB_of_fieldTag? ht
  change (if fieldFree (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil))) then
      some (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil))) else
    (NFProg.inline? FieldDialectStep.fieldLibD
      (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil)))).bind fun q =>
        if fieldFree q then some q else none) = some q at hq
  simp only [fieldFree, hf, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hq
  obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hq
  simp only [NFProg.inline?, Option.bind_some] at hq0
  split at hq0
  · rename_i b hb
    have ht' := fieldBodyD_rs ht hn hw hb
    obtain rfl : t = .stackArr 64 (fieldLimbs p) := List.head_eq_of_cons_eq ht'
    have hbl := FieldDomComplete.fieldBodyD_loadsChain ht hn hw hb
    split at hif
    · cases hif
      exact loadsChain_seq? hbl (.ret _) hq0
    · cases hif
  · cases hq0
    simp only [fieldFree, hf, Bool.not_true, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte] at hif
    cases hif

open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps (callsLoopsAll)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (opsNB)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (lowerSelectsStep aegraphStep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Hax.NFToCat (catTy nfToCatExt nfToCatExt_calls)

/-- **The chain takes one call of a tagged head at a modulus of at least `2 ^ 64` with a wide
    template, bound and returned, to a program of the shape `LoadsChain`.** -/
theorem extChain_loadsChain {Γ : Ctxt nfDialect} {m : FieldMethod} {p : Nat}
    (ht : fieldTag? (fieldHead m p) = some (m, p)) (h64 : 2 ^ 64 ≤ p)
    (hW : (wideTemplateOf p).isSome = true)
    {p₀ : NFProg nfDialect Γ [NfTy.arr (fieldLimbs p) (.word 64)]}
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy (NfTy.arr (fieldLimbs p) (.word 64)))]}
    (h : (extChain [] Γ (NfTy.arr (fieldLimbs p) (.word 64))).run p₀ = some q)
    (hp : opsNB wideOpB p₀ = true)
    (hs : OpRet (NfOp.named "t" (.call (fieldHead m p)
      [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)]
      (NfTy.arr (fieldLimbs p) (.word 64)))) p₀) : LoadsChain q := by
  obtain ⟨W, hw⟩ := Option.isSome_iff_exists.mp hW
  have hn : narrowFieldOf p = none := by
    cases hN : narrowFieldOf p with
    | none => rfl
    | some F =>
        have := (narrowFieldOf_spec hN).2.1
        omega
  have htag : (fieldTag? (fieldHead m p)).isSome = true := by rw [ht]; rfl
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3, r, hr, r1, hr1, j, hj, j1, hj1, j2, hj2, j3, hj3,
    j4, hj4, j5, hj5, hq⟩ := h
  obtain rfl := Option.some.inj hq
  change some (NFProg.abortElim NfOp.isAbort p₀) = some p0 at hp0
  cases hp0
  change flatSame (NFProg.abortElim NfOp.isAbort p₀) = some p1 at hp1
  change (if outTyB (NfTy.arr (fieldLimbs p) (.word 64)) then some p1 else none) = some p2 at hp2
  change some (NFProg.dce p2) = some p3 at hp3
  change nfToCatExt (fieldDeclsFor [] p3) p3 TRd.id = some r at hr
  have hp2' : p1 = p2 := by split at hp2 <;> cases hp2; rfl
  subst hp2'
  cases hp3; cases hr1; cases hj1
  have hab : NFProg.abortFree NfOp.isAbort p₀ = true :=
    FrontComplete.abortFree_of_opsNB (fun o ho => by
      simp only [wideOpB, Bool.and_eq_true, Bool.not_eq_true'] at ho
      exact ho.1) p₀ hp
  rw [NFProg.abortElim_of_abortFree _ p₀ hab] at hp1
  -- the montify pass is the identity, as in `extChain_callFree_of_wide`
  have hf : opsNB (fun o => !NFFlattenTuples.opIsTuple o && wideOpB o) p1 = true :=
    FrontComplete.opsNB_flatSame (W := fun _ => false) (fun _ h => h) hp1
      (FrontComplete.opsNB_mono_loop (fun o h => by simp [h]) (fun _ h => h) _ hp)
  have hd : opsNB wideOpB p1.dce = true :=
    FrontComplete.opsNB_dce _ (FrontComplete.opsNB_mono_loop
      (fun o h => by simp only [Bool.and_eq_true] at h; exact h.2) (fun _ h => h) _ hf)
  have hD : ∀ d ∈ fieldDeclsFor [] p1.dce, wideTagB d.name = true := by
    intro d hd'
    simp only [fieldDeclsFor, List.filter_nil, List.nil_append] at hd'
    exact fieldDeclsOf_wide _ hd d hd'
  have h0 : callsLoopsAll (fun f _ _ => wideTagB f) (fun _ => true) r = true :=
    ExportChainOps.callsLoopsAll_of_loops _ _ r (ExportChainOps.callsLoopsAll_true r)
      fun f as rs hc => by
        obtain ⟨d, hd', rfl, -⟩ := nfToCatExt_calls _ _ TRd.id r hr f as rs hc
        exact hD d hd'
  have h1 := (ExportChainOps.callsLoopsAll_nfGo (d := CatCryptDialect.catCryptDialect) _ _
    catRules (Ctxt.Hom.id _) (∅, ∅) r).trans h0
  have h2 := ExportChainOps.callsLoopsAll_map? catToJasmin catToJasmin_regionTypes
    (fun f _ _ => wideTagB f) (fun _ => true) _ h1 _ hj
  have hm := montifyPass_of_wideTag (Γ := mapCtx (List.map catTy Γ))
    (ts := [mapTy (catTy (NfTy.arr (fieldLimbs p) (.word 64)))]) j h2
  rw [hm] at hj2
  -- the shape through the steps
  obtain ⟨hh, args, hpe⟩ := hs
  rw [hpe] at hp1
  have g1 := flatSame_callRet hp1
  have g2 := nfToCatExt_callRet _ htag (dce_opRet g1) hr
  have g3 := map?_catToJasmin_callRet (aegraphOptNF_callRet g2) _ hj
  have g4 := fieldDialectStep_loadsChain ht hn hw g3 hj2
  exact loadsChain_aegraphStep
    (loadsChain_synRangeStep (loadsChain_lowerSelectsStep g4 hj3) hj4) hj5

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

/-- **The output of the chain on a member of the field domain has the shape `LoadsChain`.** -/
theorem fieldDom_chain_loadsChain {e : _root_.Hax.TExpr} {σ : AbiLayout} {t : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t]} (h : fieldDomB e σ = true)
    (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t, q⟩) : LoadsChain q := by
  obtain ⟨T, p0, hp, hops⟩ := fieldDom_haxToNF h
  obtain ⟨m, p, ht, h64, hW, hT, hs⟩ := fieldDom_haxToNF_opRet h hp
  subst hT
  simp only [NFEntry.chainNF, haxEntry, hp, Option.bind_some, Option.map_eq_some_iff] at hq
  obtain ⟨q', hq', heq⟩ := hq
  cases heq
  rw [linkedDecls_single] at hq'
  exact extChain_loadsChain ht h64 hW hq' hops hs

/-- **The program the export receives on a member of the field domain has the shape
    `LoadsChain`**: the narrow-word stages and the legalisation keep the shape of the output of
    the chain. -/
theorem fieldDom_legalize_loadsChain {e : _root_.Hax.TExpr} {σ : AbiLayout} {t0 : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t0]}
    {q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]}
    (h : fieldDomB e σ = true) (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩)
    (hq' : NarrowWords.narrowPrep q = some q') : LoadsChain (legalizeRegion q') :=
  loadsChain_legalizeRegion (loadsChain_narrowPrep (fieldDom_chain_loadsChain h hq) hq')

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
