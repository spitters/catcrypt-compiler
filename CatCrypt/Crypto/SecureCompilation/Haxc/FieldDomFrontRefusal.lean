/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFront

/-!
# The refusal stage and the calls of the front on the field domain

The fields `refusal` (`F1`) and `callFree` (`F7`) of `FieldDomComplete.FieldDomStages`, proved
as theorems with the types of the fields. On a member of the field domain the front passes
return the literal `fieldLit m p k` unchanged (`fieldLit_front`), and `impToNF` translates it,
from the parameters of `fieldAbi k n`, to one call of the head `fieldHead m p` at arrays of
`fieldLimbs p` words. The modulus is at least `2^64`, so the montify pass of the chain returns
its input and the field dialect step leaves no call.

## Main results

* `entryEnv_lookup_cons` — the variable of a name in the environment of the parameters.
* `fieldDom_haxToNF` — `haxToNF` returns a program whose field calls are tagged at moduli of
  at least `2^31`.
* `extChain_callFree_of_wide` — the chain returns a program without `call` on such a source.
* `fieldDom_refusal` — stage `F1`: the translation refuses no member of the field domain.
* `fieldDom_callFree` — stage `F7`: the output of the chain on the field domain has no `call`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi fieldArgName)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.Hax.ImpToNF (entryEnv NfEnv)
open _root_.Hax (ImpExpr)
open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag? fieldLimbs fieldHeadB)

/-- The prepared body of a field literal is the literal, and it passes the side conditions. -/
theorem fieldLit_front (m : FieldMethod) (p k : Nat) :
    CatCrypt.Crypto.Hax.haxFrontOkP CatCrypt.Crypto.Hax.shapeAccepts (fieldLit m p k) = true ∧
    CatCrypt.Crypto.Hax.haxFrontBodyP CatCrypt.Crypto.Hax.shapeAccepts (fieldLit m p k) =
      fieldLit m p k := by
  have hP : CatCrypt.Crypto.Hax.haxFrontPrep (fieldLit m p k) = fieldLit m p k := by
    by_cases hk : k = 2 <;> simp [hk, fieldLit, CatCrypt.Crypto.Hax.haxFrontPrep,
      Hax.InlineLocalClosures.inlineSpine, Hax.LetIntoBranches.letsInto,
      Hax.LetIntoBranches.bindInto, Hax.InlineMap.inlineMapClosures,
      Hax.InlineMap.nameMapSources, Hax.InlineMap.inlineMaps, Hax.InlineMap.mapSrc?,
      Hax.InlineMap.mapSite?]
  have hA : CatCrypt.Crypto.Hax.repeatCountInline (CatCrypt.Crypto.Hax.haxFrontAnf
      (fieldLit m p k)) = fieldLit m p k := by
    rw [CatCrypt.Crypto.Hax.haxFrontAnf, hP]
    by_cases hk : k = 2 <;> simp [hk, fieldLit, CatCrypt.Crypto.Hax.aNormalizeTotal,
      CatCrypt.Crypto.Hax.bindTails, CatCrypt.Crypto.Hax.aNormTBody,
      CatCrypt.Crypto.Hax.repeatCountInline, CatCrypt.Crypto.Hax.repeatCountBind,
      CatCrypt.Crypto.Hax.aNormTArgs, CatCrypt.Crypto.Hax.prependBindings,
      CatCrypt.Crypto.Hax.splitLetBinds, CatCrypt.Crypto.Hax.bindRhs,
      CatCrypt.Crypto.Hax.isTailBindable, CatCrypt.Crypto.Hax.isVar]
  have hS : CatCrypt.Crypto.Hax.prepShapeB (fieldLit m p k) = true := by
    by_cases hk : k = 2 <;> simp [hk, fieldLit, CatCrypt.Crypto.Hax.prepShapeB,
      CatCrypt.Crypto.Hax.isSomeRet]
  have hD : CatCrypt.Crypto.Hax.aNormTDenoteOk (fieldLit m p k) = true := by
    by_cases hk : k = 2 <;> simp [hk, fieldLit, CatCrypt.Crypto.Hax.aNormTDenoteOk,
      CatCrypt.Crypto.Hax.aNormalizeTotalCount, CatCrypt.Crypto.Hax.bindTails,
      CatCrypt.Crypto.Hax.aNormTBody, CatCrypt.Crypto.Hax.ANormDOk,
      CatCrypt.Crypto.Hax.ANormDOkList, CatCrypt.Crypto.Hax.aNormTArgs,
      CatCrypt.Crypto.Hax.isTailBindable, CatCrypt.Crypto.Hax.isVar,
      CatCrypt.Crypto.Hax.argsOrderOk, CatCrypt.Crypto.Hax.varKept,
      Hax.InlineLocalClosures.frameOk]
  simp [CatCrypt.Crypto.Hax.haxFrontOkP, CatCrypt.Crypto.Hax.haxFrontBodyP,
    CatCrypt.Crypto.Hax.haxFrontAnfEP, CatCrypt.Crypto.Hax.anfEPick,
    CatCrypt.Crypto.Hax.haxFrontRouteOkP, CatCrypt.Crypto.Hax.shapeAccepts, hP, hA, hS, hD]

/-- The variable of a name in the environment of names of the parameters `(x, t) :: ps`: the
    first parameter at `x`, and otherwise the variable of the name in the environment of `ps`,
    moved past the first parameter. -/
theorem entryEnv_lookup_cons (x : String) (t : NfTy) (ps : List (String × NfTy)) (y : String) :
    (entryEnv ((x, t) :: ps)).lookup y =
      if x = y then some ⟨t, Var.here⟩
      else ((entryEnv ps).lookup y).map fun q => ⟨q.1, Var.there q.2⟩ := by
  simp only [entryEnv, NfEnv.lookup_cons]
  congr 1
  exact NfEnv.lookup_mapV _ _ _

/-- **The translation of a call bound and returned**: when the environment of names reads
    `x` and `a` at the type `T` and the call typing gives `f` on `[T, T]` the type `T`,
    `impToNF` translates `let t := f(x, a); t` to a program of result type `T` whose one
    operation is the call `f` named `t`. -/
theorem impToNF_letCall {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (f a : String) (T : NfTy)
    (vx va : Var Γ T) (hx : σ.lookup "x" = some ⟨T, vx⟩) (ha : σ.lookup a = some ⟨T, va⟩)
    (hf : f ≠ "repeat") (hs : CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf f [T, T] = some T) :
    ∃ o, CatCrypt.Crypto.Hax.ImpToNF.impToNF CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf none σ
      (.letBind "t" (.app f [.var "x", .var a]) (.var "t")) = some o ∧ o.t = T ∧
      ∀ P : NfOp → Bool, P (.named "t" (.call f [T, T] T)) = true →
        FrontComplete.opsNB P o.prog = true := by
  simp [CatCrypt.Crypto.Hax.ImpToNF.impToNF, CatCrypt.Crypto.Hax.ImpToNF.impArgsNF,
    CatCrypt.Crypto.Hax.ImpToNF.atomOut, hx, ha, hf, hs, NfEnv.lookup_cons,
    CatCrypt.Crypto.Hax.ImpToNF.Out.comp, CatCrypt.Crypto.Hax.ImpToNF.Out.prog,
    FrontComplete.opsNB, CatCrypt.Crypto.Hax.ImpToNF.mkEN, NFPre.plug, NFPre.append]

/-- **A field expression is a tagged call at a modulus with a template**: the head reads back
    as its method and modulus, the modulus passes `fieldModOk` and is at least `2^64`, and
    `n = fieldLimbs p`. -/
theorem fieldDomE_tag {e : _root_.Hax.TExpr} {k n : Nat} (h : fieldDomE e = some (k, n)) :
    ∃ m p, (m, k) ∈ fieldMethods ∧ 2 ^ 64 ≤ p ∧
      CatCrypt.Crypto.Hax.ImpToNF.fieldModOk p = true ∧ fieldTag? (fieldHead m p) = some (m, p)
      ∧ n = fieldLimbs p ∧ e.erase = fieldLit m p k := by
  unfold fieldDomE at h
  split at h
  · rename_i v f a ta b tb tr w tw te
    split at h
    · rename_i m p hf
      simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem,
        Bool.or_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, hfl⟩, rfl⟩, rfl⟩, rfl⟩, hb⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h64⟩, hp⟩, hn⟩,
        rfl, rfl⟩ := h
      obtain rfl : f = fieldHead m p :=
        String.toList_inj.mp (by rw [hfl]; simp [fieldHead])
      refine ⟨m, p, hm, h64, ?_, hf, rfl, ?_⟩
      · simp [CatCrypt.Crypto.Hax.ImpToNF.fieldModOk, hp]
        omega
      · rcases hb with rfl | rfl <;> simp [_root_.Hax.TExpr.erase, fieldLit]
    · cases h
  · cases h

/-- A tagged head is not `repeat`. -/
theorem fieldHead_ne_repeat (m : FieldMethod) (p : Nat) : fieldHead m p ≠ "repeat" := by
  intro h
  have h' := congrArg String.toList h
  cases m <;> simp [fieldHead, FieldMethod.nameChars] at h'

/-- The parameters of a layout with the arguments of `fieldAbi k n`, as the entry of a program,
    for `k = 2`: the operands `x`, `y` and the output `out`, each an array of `n` words. -/
theorem abiEntry_fieldAbi_two {σ : AbiLayout} {n : Nat} (h : σ.args = (fieldAbi 2 n).args) :
    abiEntry σ = [("x", NfTy.arr n (.word 64)), ("y", NfTy.arr n (.word 64)),
      ("out", NfTy.arr n (.word 64))] := by
  simp [abiEntry, CatCrypt.Crypto.Hax.NFToCat.abiParamsArr, h, fieldAbi, List.range_succ,
    fieldArgName, CatCrypt.Crypto.Hax.NFToCat.abiKindArr]

/-- The parameters of a layout with the arguments of `fieldAbi 1 n`, as the entry of a
    program: the operand `x` and the output `out`, each an array of `n` words. -/
theorem abiEntry_fieldAbi_one {σ : AbiLayout} {n : Nat} (h : σ.args = (fieldAbi 1 n).args) :
    abiEntry σ = [("x", NfTy.arr n (.word 64)), ("out", NfTy.arr n (.word 64))] := by
  simp [abiEntry, CatCrypt.Crypto.Hax.NFToCat.abiParamsArr, h, fieldAbi, List.range_succ,
    fieldArgName, CatCrypt.Crypto.Hax.NFToCat.abiKindArr]

/-- The call typing gives a tagged head of a binary method at a modulus `p ≥ 2^64` with a
    template, on two arrays of `fieldLimbs p` words, the same array type. -/
theorem hax64SigOf_fieldHead {m : FieldMethod} {p : Nat} (hb : m.binary = true)
    (h64 : 2 ^ 64 ≤ p) (hok : CatCrypt.Crypto.Hax.ImpToNF.fieldModOk p = true)
    (ht : fieldTag? (fieldHead m p) = some (m, p)) :
    CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf (fieldHead m p)
      [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)] =
      some (NfTy.arr (fieldLimbs p) (.word 64)) := by
  have hs := CatCrypt.Crypto.Hax.ImpToNF.fieldTagSig_wide ht h64 hok
  simp only [FieldMethod.sigAt, hb, ite_true] at hs
  simp [CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf, hs]

/-! ## The calls of the chain on the field domain -/

section Calls

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps (callsLoopsAll)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montifyPass montifyMods fieldMods)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldDialectStep)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32 (mont32Cert)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (opsNB)

/-- A call to a head tagged at a modulus of at least `2^31`. -/
def wideTagB (f : String) : Bool := (fieldTag? f).any fun mp => decide (2 ^ 31 ≤ mp.2)

/-- An operation that does not abort and whose field declarations are of heads tagged at a
    modulus of at least `2^31`. -/
def wideOpB (o : NfOp) : Bool :=
  !NfOp.isAbort o && (opFieldDecls o).all fun d => wideTagB d.name

/-- **The translation of a member of the field domain**: `haxToNF` returns a program whose
    operations do not abort and declare only heads tagged at a modulus of at least `2^31`. -/
theorem fieldDom_haxToNF {e : _root_.Hax.TExpr} {σ : AbiLayout} (h : fieldDomB e σ = true) :
    ∃ T p0, haxToNF σ (HaxModule.single e) = some ⟨T, p0⟩ ∧ opsNB wideOpB p0 = true := by
  unfold fieldDomB at h
  split at h
  · rename_i k n hkn
    obtain ⟨m, p, hm, h64, hok, ht, rfl, he⟩ := fieldDomE_tag hkn
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
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | h <;> first | rfl | cases h
    have hsig := hax64SigOf_fieldHead hbin h64 hok ht
    have hk : k = 2 ∨ k = 1 := by
      simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at hm
      grind
    have hI : ∃ o, CatCrypt.Crypto.Hax.ImpToNF.impToNF CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf
        none (entryEnv (abiEntry σ)) (fieldLit m p k) = some o ∧
        o.t = NfTy.arr (fieldLimbs p) (.word 64) ∧
        ∀ P : NfOp → Bool, P (.named "t" (.call (fieldHead m p)
          [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)]
          (NfTy.arr (fieldLimbs p) (.word 64)))) = true → opsNB P o.prog = true := by
      rcases hk with rfl | rfl
      · rw [abiEntry_fieldAbi_two hargs]
        exact impToNF_letCall (entryEnv _) (fieldHead m p) "y" _ Var.here Var.here.there
          (by simp [entryEnv_lookup_cons]) (by simp [entryEnv_lookup_cons])
          (fieldHead_ne_repeat m p) hsig
      · rw [abiEntry_fieldAbi_one hargs]
        exact impToNF_letCall (entryEnv _) (fieldHead m p) "x" _ Var.here Var.here
          (by simp [entryEnv_lookup_cons]) (by simp [entryEnv_lookup_cons])
          (fieldHead_ne_repeat m p) hsig
    obtain ⟨o, ho, hot, hops⟩ := hI
    refine ⟨o.t, o.prog, ?_, hops _ ?_⟩
    · rw [haxToNF_single, hc, bindConsts_nil]
      simp [nfSrcProg, hsh, hbody, ho, hot, entryResOk, outTyB]
    · have hlt : ¬ p < 18446744073709551616 := by omega
      have h31 : 2147483648 ≤ p := by omega
      simp [wideOpB, NfOp.isAbort, opFieldDecls, ht, wideTagB, FieldWideDecl.wideDecl, hlt, h31]
  · cases h

/-- **Stage `F1`**: the translation `haxToNF` refuses no member of the field domain. -/
theorem fieldDom_refusal {e : _root_.Hax.TExpr} {σ : AbiLayout} (h : fieldDomB e σ = true) :
    (HaxModule.single e).refusal? σ = none := by
  obtain ⟨T, p0, hp, -⟩ := fieldDom_haxToNF h
  rw [HaxModule.refusal?_eq_none_iff, hp]
  rfl

/-- A program whose every call fails the test `fun _ _ _ => false` has no `call`. -/
theorem callFree_of_callsLoopsAll_false {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {W : List JasminTy → Bool} (p : NFProg jasminDialect Γ ts)
    (hp : callsLoopsAll (fun _ _ _ => false) W p = true) : p.callFree = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, ihb hp.1.2, ihk hp.2, Bool.and_self]
  | call => simp [callsLoopsAll] at hp

/-- A program without a call of a field head whose every call satisfies a test that holds only
    at field heads has no call that passes any test. -/
theorem callsLoopsAll_false_of_fieldFree {C : String → List JasminTy → List JasminTy → Bool}
    {W : List JasminTy → Bool} (hC : ∀ f as rs, C f as rs = true → fieldHeadB f = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hf : fieldFree p = true) (hp : callsLoopsAll C W p = true) :
    callsLoopsAll (fun _ _ _ => false) W p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hf hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, fieldFree, Bool.and_eq_true] at hp hf ⊢
      exact ⟨ihb hf.1 hp.1, ihk hf.2 hp.2⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, fieldFree, Bool.and_eq_true] at hp hf ⊢
      exact ⟨⟨iht hf.1.1 hp.1.1, ihe hf.1.2 hp.1.2⟩, ihk hf.2 hp.2⟩
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, fieldFree, Bool.and_eq_true] at hp hf ⊢
      exact ⟨⟨hp.1.1, ihb hf.1 hp.1.2⟩, ihk hf.2 hp.2⟩
  | call f _ _ _ =>
      simp only [callsLoopsAll, fieldFree, Bool.and_eq_true, Bool.not_eq_true'] at hp hf
      rw [hC _ _ _ hp.1] at hf
      cases hf.1

/-- The output of the field dialect step has no call of a field head. -/
theorem fieldFree_of_fieldDialectStep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hq : (fieldDialectStep Γ ts).run p = some q) :
    fieldFree q = true := by
  change (if fieldFree p then some p else
    (NFProg.inline? FieldDialectStep.fieldLibD p).bind fun q => if fieldFree q then some q
      else none) = some q at hq
  split at hq
  · cases hq
    assumption
  · obtain ⟨q0, -, hif⟩ := Option.bind_eq_some_iff.mp hq
    split at hif
    · cases hif
      assumption
    · cases hif

/-- The moduli of the tagged calls of a program whose every call is to a head tagged at a
    modulus of at least `2^31` are at least `2^31`. -/
theorem fieldMods_ge {W : List JasminTy → Bool} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : callsLoopsAll (fun f _ _ => wideTagB f) W p = true) :
    ∀ x ∈ fieldMods p, 2 ^ 31 ≤ x := by
  induction p with
  | ret => intro x hx; cases hx
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      intro x hx
      simp only [fieldMods, List.mem_append] at hx
      rcases hx with hx | hx
      exacts [ihb hp.1 x hx, ihk hp.2 x hx]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      intro x hx
      simp only [fieldMods, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      exacts [iht hp.1.1 x hx, ihe hp.1.2 x hx, ihk hp.2 x hx]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      intro x hx
      simp only [fieldMods, List.mem_append] at hx
      rcases hx with hx | hx
      exacts [ihb hp.1.2 x hx, ihk hp.2 x hx]
  | call f _ _ ih =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      intro x hx
      simp only [fieldMods, List.mem_append] at hx
      rcases hx with hx | hx
      · simp only [wideTagB] at hp
        cases ht : fieldTag? f with
        | none => simp [ht] at hx
        | some mp =>
            simp only [ht, Option.map_some, Option.toList_some, List.mem_singleton] at hx
            simp only [ht, Option.any_some, decide_eq_true_eq] at hp
            omega
      · exact ih hp.2 x hx

/-- The montify rounds at moduli that fail `mont32Cert` return the program. -/
theorem montifyMods_of_not_cert {Γ : Ctxt jasminDialect} {ts : List JasminTy} :
    ∀ (ps : List Nat) (prog : NFProg jasminDialect Γ ts), (∀ x ∈ ps, mont32Cert x = false) →
      montifyMods ps prog = prog
  | [], _, _ => rfl
  | p :: ps, prog, h => by
      simp only [montifyMods, h p List.mem_cons_self, Bool.false_eq_true, dite_false]
      exact montifyMods_of_not_cert ps prog fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- **The montify pass returns a program whose every call is to a head tagged at a modulus of
    at least `2^31`**: no such modulus passes `mont32Cert`. -/
theorem montifyPass_of_wideTag {W : List JasminTy → Bool} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hp : callsLoopsAll (fun f _ _ => wideTagB f) W prog = true) : montifyPass prog = prog := by
  refine montifyMods_of_not_cert _ prog fun x hx => ?_
  have hx' := fieldMods_ge prog hp x (List.mem_eraseDups.mp hx)
  simp only [mont32Cert, decide_eq_false_iff_not, not_and]
  omega

/-- The field declarations of a program of `opsNB wideOpB` are of heads tagged at a modulus of
    at least `2^31`. -/
theorem fieldDeclsOf_wide {W : List NfTy → Bool} {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hp : opsNB wideOpB p W = true) :
    ∀ d ∈ fieldDeclsOf p, wideTagB d.name = true := by
  induction p with
  | ret => intro d hd; cases hd
  | var e k ih =>
      obtain ⟨o, _, _⟩ := e
      simp only [opsNB, Bool.and_eq_true] at hp
      intro d hd
      simp only [fieldDeclsOf, List.mem_append] at hd
      rcases hd with hd | hd
      · simp only [wideOpB, Bool.and_eq_true, List.all_eq_true] at hp
        exact hp.1.2 d hd
      · exact ih hp.2 d hd
  | forLoop _ _ _ _ ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      intro d hd
      simp only [fieldDeclsOf, List.mem_append] at hd
      rcases hd with hd | hd
      exacts [ihb hp.1 d hd, ihk hp.2 d hd]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      intro d hd
      simp only [fieldDeclsOf, List.mem_append] at hd
      rcases hd with (hd | hd) | hd
      exacts [iht hp.1.1 d hd, ihe hp.1.2 d hd, ihk hp.2 d hd]
  | whileLoop _ _ _ ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      intro d hd
      simp only [fieldDeclsOf, List.mem_append] at hd
      rcases hd with hd | hd
      exacts [ihb hp.1.2 d hd, ihk hp.2 d hd]
  | call => simp [opsNB] at hp

open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)

/-- **The chain returns a program without `call` on a source whose field calls are tagged at
    moduli of at least `2^31`**: the declarations of the translation are those of the tagged
    calls (`fieldDeclsOf_wide`), so every call of the translated program is to such a head;
    the montify pass returns the program (`montifyPass_of_wideTag`), the field dialect step
    returns a program without a call of a field head (`fieldFree_of_fieldDialectStep`), and
    the later steps keep the absence of calls. -/
theorem extChain_callFree_of_wide {Γ : Ctxt nfDialect} {t : NfTy}
    {p : NFProg nfDialect Γ [t]} {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]} (h : (extChain [] Γ t).run p = some q)
    (hp : opsNB wideOpB p = true) : q.callFree = true := by
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3, r, hr, r1, hr1, j, hj, j1, hj1, j2, hj2, j3, hj3,
    j4, hj4, j5, hj5, hq⟩ := h
  obtain rfl := Option.some.inj hq
  change some (NFProg.abortElim NfOp.isAbort p) = some p0 at hp0
  cases hp0
  change flatSame (NFProg.abortElim NfOp.isAbort p) = some p1 at hp1
  change (if outTyB t then some p1 else none) = some p2 at hp2
  change some (NFProg.dce p2) = some p3 at hp3
  change nfToCatExt (fieldDeclsFor [] p3) p3 TRd.id = some r at hr
  have hp2' : p1 = p2 := by split at hp2 <;> cases hp2; rfl
  subst hp2'
  cases hp3; cases hr1; cases hj1; cases hj3; cases hj4; cases hj5
  have hab : NFProg.abortFree NfOp.isAbort p = true :=
    FrontComplete.abortFree_of_opsNB (fun o ho => by
      simp only [wideOpB, Bool.and_eq_true, Bool.not_eq_true'] at ho
      exact ho.1) p hp
  rw [NFProg.abortElim_of_abortFree _ p hab] at hp1
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
    (ts := [mapTy (catTy t)]) j h2
  rw [hm] at hj2
  have h4 := callsLoopsAll_false_of_fieldFree (fun f _ _ hw => by
      simp only [wideTagB] at hw
      cases ht : fieldTag? f with
      | none => simp [ht] at hw
      | some mp => exact _root_.Hax.FieldTag.fieldHeadB_of_fieldTag? ht)
    j2 (fieldFree_of_fieldDialectStep hj2)
    (ExportChainOps.callsLoopsAll_fieldDialect _ _ h2 hj2)
  have h5 := ExportChainOps.callsLoopsAll_lowerSel _ _ _ h4 (fun v => v)
  refine callFree_of_callsLoopsAll_false (W := fun _ => true) _ ?_
  unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF
    CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.loopRange
  rw [ExportChainOps.callsLoopsAll_nfGo (d := jasminDialect),
    ExportChainOps.callsLoopsAll_carriedGo]
  exact h5

/-- **Stage `F7`**: the output of the chain on the field domain has no `call`: the translation
    calls only the head of the member, tagged at a modulus of at least `2^64`
    (`fieldDom_haxToNF`), and the chain removes every such call (`extChain_callFree_of_wide`). -/
theorem fieldDom_callFree {e : _root_.Hax.TExpr} {σ : AbiLayout} {t : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t]} (h : fieldDomB e σ = true)
    (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t, q⟩) : q.callFree = true := by
  obtain ⟨T, p0, hp, hops⟩ := fieldDom_haxToNF h
  simp only [NFEntry.chainNF, haxEntry, hp, Option.bind_some, Option.map_eq_some_iff] at hq
  obtain ⟨q', hq', heq⟩ := hq
  cases heq
  rw [linkedDecls_single] at hq'
  exact extChain_callFree_of_wide hq' hops

end Calls

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
