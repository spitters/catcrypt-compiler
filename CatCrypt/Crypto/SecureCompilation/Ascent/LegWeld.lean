/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf
public import CatCrypt.Crypto.Hax.RustSubsetToLowCT

/-!
# The generic leg weld: descent refinement and ascent correspondence over one program

A straight-line word kernel is read by two legs of the pipeline. The descent leg
is the refinement `RRefines spec c` (`RustSubsetToLowCT`): under `RustExec`, the
`LowCT` term `c` advances the `Nat` scalar map by the source step `spec`, and for
a `RustSrc` source `src` the verified lowering supplies it as
`lowerRefines src : RRefines (RustSrc.exec src) (lower src)`. The ascent leg is
the correspondence `Corres SRwordNT P fa c` (`Ascent/Corres`, `ExprLeaf`): under
`semScalar`, the same `c` advances a `BitVec`-word environment by the abstract
step `fa` on `ZMod 2^64`. The emit leg
(`rustToJasminCom_endToEnd_unconditional`) reads the front's jasmin program for
`c` and states that it denotes to the `ctTransTy` image of the word `semScalar`
leaves at the tracked name.

`legWeld` composes the three over one `c`. Its hypotheses are

* `hRef : RRefines spec c` — the descent's refinement of `c`;
* `hRun : ∃ rs', AdeqRun c rs rs'` — the run of `c` from the entry state `rs`, with the
  `Nat`/`BitVec` reconciliation side conditions evaluated at the states of that
  run (each literal a `u64`, each expression assignment `srcClean` and in range
  where it is evaluated), and `hIR : ScalarInRange rs`;
* the reads-follow-writes scoping of the closed kernel, `readsOK (fun _ => False)
  c` and `afterB (fun _ => False) c name`, and the readout name `¬ isTmpName name`;
* `F : FrontOut c name` — the front's translation of `c` closed at `name`;
* `hCorres : Corres SRwordNT P fa c` with `P (derivedAbs rs)` — the ascent's
  correspondence of `c`.

Its conclusion is the closed capstone: the emitted jasmin program denotes to
`ctTransTy (BitVec.ofNat 64 (spec rs.rsScalar name))`, the source step's output
word at `name`, and that word's `ZMod 2^64` readout is `fa (derivedAbs rs) name`.
`legWeld_lower` is the instance at `spec := RustSrc.exec src` with `hRef`
supplied by `lowerRefines`, the front term related to `lower src` by `LitNorm`.

The program identity between the legs is the theorem's shape: `hRef`, `hRun`,
`F` and `hCorres` are all indexed by the same `c`. The two semantics of `c` are
reconciled once, by `agreeRun`: a `RustExec` run tracked by `AdeqRun` is matched
by a `semScalar` run whose output environment reflects the `Nat` scalars as their
`BitVec.ofNat 64` images. Run at the empty entry environment it supplies the emit
leg's `semScalar` premises; run at the reflected entry environment `derivedEnv rs`
it identifies the word the ascent's relation `SRwordNT` reads at `name`.

`AdeqRun` restates the `IsCoveredAdeqS` arms of `RustExecSemScalarBridge` with
the expression range condition at the run's state rather than at every in-range
state, which is what admits a subtraction or an addition whose operands are in
range along the run.

## Main definitions

* `AdeqRun`, `agreeRun` — the run-local word adequacy and its `semScalar` tracking
* `LitNorm`, `rrefines_of_litNorm` — literal-assignment normalisation, transporting
  `RRefines`
* `derivedAbs`, `srwordNT_derivedEnv` — the reflected entry abstract state
* `FrontOut`, `FrontOut.ofSome` — the front's artifacts for a kernel closed at a name
* `legWeld`, `legWeld_lower` — the generic weld and its `RustSrc` instance
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy CVar Ctx HVec)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.Hax.RustSubsetToLowCT (RustSrc lower lowerRefines RRefines)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## The run-local word adequacy -/

/-- A straight-line word run of `c` from `rs` to `rs'`, carrying the `Nat`/`BitVec`
    reconciliation side conditions at the states of the run: every literal is a
    `u64`, and every expression assignment is `srcClean` and in `u64` range at the
    state it reads. -/
inductive AdeqRun : LowCT → RustState → RustState → Prop
  | rSkip {rs : RustState} : AdeqRun .RSkip rs rs
  | rBlock {body : LowCT} {rs rs' : RustState} :
      AdeqRun body rs rs' → AdeqRun (.RBlock body) rs rs'
  | rSeq {c₁ c₂ : LowCT} {rs rs₁ rs₂ : RustState} :
      AdeqRun c₁ rs rs₁ → AdeqRun c₂ rs₁ rs₂ → AdeqRun (.RSeq c₁ c₂) rs rs₂
  | rLetU64Zero {name : String} {body : LowCT} {rs rs' : RustState} :
      AdeqRun body (rsSetScalar rs name 0) rs' → AdeqRun (.RLetU64Zero name body) rs rs'
  | rScalarSet {name : String} {n : Nat} {rs : RustState} (hn : n < 2 ^ 64) :
      AdeqRun (.RScalarSet name n) rs (rsSetScalar rs name n)
  | rScalarSetExpr {x : String} {e : SExpr} {rs : RustState} (hclean : srcClean e)
      (hir : e.inRange rs.rsScalar) :
      AdeqRun (.RScalarSetExpr x e) rs (rsSetScalar rs x (e.eval rs.rsScalar))

/-- The literal expression assignment `RScalarSetExpr x (.SLit n)`, the spelling
    `lower` gives a source `let`, as an `AdeqRun` step. -/
theorem AdeqRun.lit {x : String} {n : Nat} {rs : RustState} (hn : n < 2 ^ 64) :
    AdeqRun (.RScalarSetExpr x (.SLit n)) rs (rsSetScalar rs x n) :=
  .rScalarSetExpr (e := .SLit n) hn hn

/-- An `AdeqRun` program is in the covered straight-line fragment. -/
theorem AdeqRun.toIsCoveredS {c : LowCT} {rs rs' : RustState} (h : AdeqRun c rs rs') :
    IsCoveredS c := by
  induction h with
  | rSkip => exact .rSkip
  | rBlock _ ih => exact .rBlock ih
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rLetU64Zero _ ih => exact .rLetU64Zero ih
  | rScalarSet _ => exact .rScalarSet _ _
  | rScalarSetExpr hclean _ => exact .rScalarSetExpr _ _ hclean

/-- An `AdeqRun` program is in the control-extended covered fragment. -/
theorem AdeqRun.toIsCoveredSCtl {c : LowCT} {rs rs' : RustState} (h : AdeqRun c rs rs') :
    IsCoveredSCtl c :=
  .ofStraight h.toIsCoveredS

/-- A `RustExec` run tracked by `AdeqRun c rs rs'` ends at `rs'`, and from an entry
    environment `EnvBoundOn` the set `B`, with every read of `c` in scope
    (`readsOK B c`), the `semScalar` run is defined and its output environment is
    `EnvBoundOn` the write set `afterB B c` of the exit state. The `AdeqRun`
    counterpart of `RustExecSemScalarBridge.agreeS`. -/
theorem agreeRun {c : LowCT} {rs rs' : RustState} (h : AdeqRun c rs rs') :
    ∀ {N : Nat} {leafSpec : LeafSpec} {rs₁ : RustState} {env : SEnvScalar}
      {B : String → Prop},
      RustExec N leafSpec c rs rs₁ → EnvBoundOn rs env B → ScalarInRange rs → readsOK B c →
      rs₁ = rs' ∧ ∃ env', semScalar c env = some env' ∧ EnvBoundOn rs' env' (afterB B c)
        ∧ ScalarInRange rs' := by
  induction h with
  | rSkip =>
      intro N leafSpec rs₁ env B hexec henv hir _
      cases hexec
      exact ⟨rfl, env, rfl, henv, hir⟩
  | rBlock _ ih =>
      intro N leafSpec rs₁ env B hexec henv hir hreads
      cases hexec with | block _ _ _ hb =>
        obtain ⟨heq, env', hs, he, hi⟩ := ih hb henv hir hreads
        exact ⟨heq, env', by simp only [semScalar]; exact hs, he, hi⟩
  | rSeq _ _ ih₁ ih₂ =>
      intro N leafSpec rs₁ env B hexec henv hir hreads
      obtain ⟨hr1, hr2⟩ := hreads
      cases hexec with | seq _ _ _ _ _ h1 h2 =>
        obtain ⟨heq1, e1, hs1, he1, hi1⟩ := ih₁ h1 henv hir hr1
        subst heq1
        obtain ⟨heq2, e2, hs2, he2, hi2⟩ := ih₂ h2 he1 hi1 hr2
        exact ⟨heq2, e2, by simp only [semScalar, hs1]; exact hs2, he2, hi2⟩
  | rLetU64Zero _ ih =>
      intro N leafSpec rs₁ env B hexec henv hir hreads
      cases hexec with | letU64Zero _ _ _ _ hbody =>
        obtain ⟨heq, env', hs, he, hi⟩ :=
          ih hbody (by simpa using envBoundOn_upd henv _ 0)
            (scalarInRange_upd hir _ (by positivity)) hreads
        exact ⟨heq, env', by simp only [semScalar]; exact hs, he, hi⟩
  | rScalarSet hn =>
      intro N leafSpec rs₁ env B hexec henv hir _
      cases hexec
      exact ⟨rfl, _, rfl, envBoundOn_upd henv _ _, scalarInRange_upd hir _ hn⟩
  | @rScalarSetExpr x e rs hclean hir_e =>
      intro N leafSpec rs₁ env B hexec henv hir hreads
      cases hexec
      have hvb : varsBoundIn B e := hreads
      obtain ⟨env2, nm, cnt', hsem2, _, hotb2, _, _⟩ :=
        semLowerSExpr_ok' rs B e env 0 henv hvb hclean
      have hval : SExpr.evalBV (envReader env) e = BitVec.ofNat 64 (SExpr.eval rs.rsScalar e) := by
        rw [evalBV_congr_on B (envReader env) (SExpr.liftEnv rs.rsScalar) e
              (fun s hs hns => by rw [envReader_of_envBoundOn henv s hs hns]; rfl) hvb hclean]
        exact sexprTransfer rs.rsScalar e hir_e
      refine ⟨rfl, env2.upd x (t := .sword 64) (BitVec.ofNat 64 (SExpr.eval rs.rsScalar e)),
        by simp only [semScalar, hsem2]; rw [hval], ?_, ?_⟩
      · exact envBoundOn_updExpr henv hotb2 x _
      · exact scalarInRange_upd hir x (SExpr.eval_lt_of_inRange _ _ hir_e)

/-! ## Literal-assignment normalisation -/

/-- `LitNorm c c'`: `c'` is `c` with some expression assignments of a literal,
    `RScalarSetExpr x (.SLit n)`, replaced by the literal assignment
    `RScalarSet x n`, under the straight-line constructors. Relates the verified
    lowering's `lower src` to the front's spelling of the same kernel. -/
inductive LitNorm : LowCT → LowCT → Prop
  | refl (c : LowCT) : LitNorm c c
  | lit (x : String) (n : Nat) : LitNorm (.RScalarSetExpr x (.SLit n)) (.RScalarSet x n)
  | seq {c₁ c₁' c₂ c₂' : LowCT} :
      LitNorm c₁ c₁' → LitNorm c₂ c₂' → LitNorm (.RSeq c₁ c₂) (.RSeq c₁' c₂')
  | block {b b' : LowCT} : LitNorm b b' → LitNorm (.RBlock b) (.RBlock b')
  | letU64Zero {name : String} {b b' : LowCT} :
      LitNorm b b' → LitNorm (.RLetU64Zero name b) (.RLetU64Zero name b')

/-- `LitNorm`-related programs have the same `RustExec` runs. -/
theorem rustExec_litNorm {c c' : LowCT} (h : LitNorm c c') :
    ∀ {N : Nat} {leafSpec : LeafSpec} {rs rs' : RustState},
      RustExec N leafSpec c rs rs' → RustExec N leafSpec c' rs rs' := by
  induction h with
  | refl c => exact fun hexec => hexec
  | lit x n =>
      intro N leafSpec rs rs' hexec
      cases hexec
      exact RustExec.scalarSet x n _
  | seq _ _ ih₁ ih₂ =>
      intro N leafSpec rs rs' hexec
      cases hexec with | seq _ _ _ r1 _ h1 h2 =>
        exact RustExec.seq _ _ _ r1 _ (ih₁ h1) (ih₂ h2)
  | block _ ih =>
      intro N leafSpec rs rs' hexec
      cases hexec with | block _ _ _ hb => exact RustExec.block _ _ _ (ih hb)
  | letU64Zero _ ih =>
      intro N leafSpec rs rs' hexec
      cases hexec with | letU64Zero _ _ _ _ hb => exact RustExec.letU64Zero _ _ _ _ (ih hb)

/-- `RRefines` transports along `LitNorm`. -/
theorem rrefines_of_litNorm {spec : (String → Nat) → (String → Nat)} {c c' : LowCT}
    (h : LitNorm c c') (hr : RRefines spec c) : RRefines spec c' := by
  intro N leafSpec rs
  obtain ⟨rs', hexec, hσ⟩ := hr N leafSpec rs
  exact ⟨rs', rustExec_litNorm h hexec, hσ⟩

/-! ## The reflected entry state -/

/-- The abstract state reflecting a `RustState`: each name's `Nat` scalar, as the
    `ZMod 2^64` readout of its `BitVec.ofNat 64` image. -/
def derivedAbs (rs : RustState) : String → ZMod (2 ^ 64) :=
  fun s => wEnc (BitVec.ofNat 64 (rs.rsScalar s))

/-- The reflected environment `derivedEnv rs` is `SRwordNT`-related to the
    reflected abstract state `derivedAbs rs`. -/
theorem srwordNT_derivedEnv (rs : RustState) : SRwordNT (derivedEnv rs) (derivedAbs rs) := by
  intro s hs
  refine ⟨BitVec.ofNat 64 (rs.rsScalar s), ?_, rfl⟩
  simp only [derivedEnv, if_neg hs]

/-- The default state's scalars are all zero, hence in `u64` range. -/
theorem scalarInRange_default : ScalarInRange (default : RustState) :=
  fun _ => Nat.two_pow_pos 64

/-! ## The front's artifacts for a kernel closed at a name -/

/-- The front's translation of `c` closed at the tracked name: the translation
    output `o`, the word-typed slot `w` the name resolves to, the closed
    `catCryptDialect` program returning it, and its jasmin lowering. -/
structure FrontOut (c : LowCT) (name : String) where
  /-- The translation output. -/
  o : DTransOut ([] : Ctx)
  /-- The front translates `c` to `o`. -/
  hTrans : translateDialectControl VarMap.empty c = some o
  /-- The word-typed slot `name` resolves to. -/
  w : CVar o.Γ' (.sword 64)
  /-- The resolution of `name`. -/
  hName : o.vm.lookup name = some ⟨.sword 64, w⟩
  /-- The closed dialect program returning `w`. -/
  com : Com catCryptDialect ([] : Ctx) (.sword 64)
  /-- The continuation closed at `w`. -/
  hRet : o.cont (Com.ret (toVIRVar w)) = some com
  /-- The jasmin lowering of `com`. -/
  jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64))
  /-- `com` lowers to `jcom`. -/
  hCom : cryptoDialectToJasminCom com = some jcom

/-- A defined slot lookup of word type is `some ⟨.sword 64, w⟩` for the variable
    `w` it carries, cast along the slot type. -/
theorem lookup_eq_some_sword {Γ : Ctx} (l : Option ((t : CryptoTy) × CVar Γ t))
    (h : l.isSome) (ht : (l.get h).1 = .sword 64) :
    l = some ⟨.sword 64, cast (congrArg (CVar Γ) ht) (l.get h).2⟩ :=
  (Option.some_get h).symm.trans (congrArg some (Sigma.ext ht (cast_heq _ _).symm))

/-- The translation output of `c`, given that the front succeeds. -/
noncomputable def frontO (c : LowCT) (h₁ : (translateDialectControl VarMap.empty c).isSome) :
    DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty c).get h₁

/-- The word-typed slot `name` resolves to in the translation output of `c`. -/
noncomputable def frontW (c : LowCT) (name : String)
    (h₁ : (translateDialectControl VarMap.empty c).isSome)
    (h₂ : ((frontO c h₁).vm.lookup name).isSome)
    (h₃ : (((frontO c h₁).vm.lookup name).get h₂).1 = .sword 64) :
    CVar (frontO c h₁).Γ' (.sword 64) :=
  cast (congrArg (CVar (frontO c h₁).Γ') h₃) (((frontO c h₁).vm.lookup name).get h₂).2

/-- The closed dialect program of `c` returning the slot of `name`. -/
noncomputable def frontCom (c : LowCT) (name : String)
    (h₁ : (translateDialectControl VarMap.empty c).isSome)
    (h₂ : ((frontO c h₁).vm.lookup name).isSome)
    (h₃ : (((frontO c h₁).vm.lookup name).get h₂).1 = .sword 64)
    (h₄ : ((frontO c h₁).cont (Com.ret (toVIRVar (frontW c name h₁ h₂ h₃)))).isSome) :
    Com catCryptDialect ([] : Ctx) (.sword 64) :=
  ((frontO c h₁).cont (Com.ret (toVIRVar (frontW c name h₁ h₂ h₃)))).get h₄

/-- The front's artifacts from the five success facts of the closed-kernel route:
    the translation, the slot lookup, its word type, the closed continuation and
    the jasmin lowering are all defined. -/
noncomputable def FrontOut.ofSome (c : LowCT) (name : String)
    (h₁ : (translateDialectControl VarMap.empty c).isSome)
    (h₂ : ((frontO c h₁).vm.lookup name).isSome)
    (h₃ : (((frontO c h₁).vm.lookup name).get h₂).1 = .sword 64)
    (h₄ : ((frontO c h₁).cont (Com.ret (toVIRVar (frontW c name h₁ h₂ h₃)))).isSome)
    (h₅ : (cryptoDialectToJasminCom (frontCom c name h₁ h₂ h₃ h₄)).isSome) :
    FrontOut c name where
  o := frontO c h₁
  hTrans := (Option.some_get h₁).symm
  w := frontW c name h₁ h₂ h₃
  hName := lookup_eq_some_sword _ h₂ h₃
  com := frontCom c name h₁ h₂ h₃ h₄
  hRet := (Option.some_get h₄).symm
  jcom := (cryptoDialectToJasminCom (frontCom c name h₁ h₂ h₃ h₄)).get h₅
  hCom := (Option.some_get h₅).symm

/-! ## The weld -/

/-- **The generic leg weld.** For a `LowCT` term `c` with the descent's refinement
    `hRef : RRefines spec c`, a run `hRun : ∃ rs', AdeqRun c rs rs'` from an in-range
    entry state, the closed-kernel scoping at the non-temp readout `name`, the
    front's artifacts `F`, and the ascent's correspondence
    `hCorres : Corres SRwordNT P fa c` with `P` holding at the reflected entry
    state: the emitted jasmin program `F.jcom` denotes to the `ctTransTy` image of
    the source step's output word `BitVec.ofNat 64 (spec rs.rsScalar name)`, and
    that word's `ZMod 2^64` readout is `fa (derivedAbs rs) name`. -/
theorem legWeld
    (c : LowCT) (spec : (String → Nat) → (String → Nat))
    (hRef : RRefines spec c)
    {rs : RustState} (hRun : ∃ rs', AdeqRun c rs rs') (hIR : ScalarInRange rs)
    (name : String) (hNT : ¬ isTmpName name)
    (hReads : readsOK (fun _ => False) c) (hOut : afterB (fun _ => False) c name)
    (F : FrontOut c name)
    (fa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)))
    (P : (String → ZMod (2 ^ 64)) → Prop)
    (hCorres : Corres SRwordNT P fa c) (hP : P (derivedAbs rs)) :
    F.jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (spec rs.rsScalar name))
      ∧ wEnc (BitVec.ofNat 64 (spec rs.rsScalar name)) = fa (derivedAbs rs) name := by
  obtain ⟨rs', hRun⟩ := hRun
  obtain ⟨rs₁, hexec, hσ⟩ := hRef 0 canonicalLeafSpec rs
  obtain ⟨hrs, env', hSem, hBound', _⟩ :=
    agreeRun hRun hexec (B := fun _ => False) (env := fun _ => none)
      (fun _ hx _ => hx.elim) hIR hReads
  subst hrs
  have hVal : env' name = some ⟨.sword 64, BitVec.ofNat 64 (rs₁.rsScalar name)⟩ :=
    hBound' name hOut hNT
  have hEmit := (rustToJasminCom_endToEnd_unconditional VarMap.empty c F.o 0 canonicalLeafSpec
    rs rs₁ HVec.nil (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)) (fun _ => none)
    env' name F.w _ F.com F.jcom hRun.toIsCoveredSCtl F.hTrans hexec
    (CatCrypt.Crypto.SecureCompilation.BorrowSafety.entry_interp rs) consistentS_empty hSem
    F.hName hVal F.hRet F.hCom).2
  obtain ⟨envA, hSemA, hSRA⟩ :=
    hCorres (derivedEnv rs) (derivedAbs rs) (srwordNT_derivedEnv rs) hP
  obtain ⟨_, envB, hSemB, hBoundB, _⟩ :=
    agreeRun hRun hexec (envBoundOn_true_of_envRel (envRel_derivedEnv rs)) hIR (readsOK_true c)
  rw [hSemA] at hSemB
  obtain rfl := Option.some.inj hSemB
  obtain ⟨w, hw, hwenc⟩ := hSRA name hNT
  rw [hBoundB name (le_afterB c _ name trivial) hNT] at hw
  have hwv : w = BitVec.ofNat 64 (rs₁.rsScalar name) := by
    have := (Option.some.injEq _ _).mp hw.symm; simpa using this
  subst hwv
  rw [hσ] at hEmit hwenc
  exact ⟨hEmit, hwenc⟩

/-- **The weld at a `RustSrc` source.** The descent's refinement is the verified
    lowering `lowerRefines src`, transported along `hNorm : LitNorm (lower src) c`
    to the front's term `c`; the source step is `RustSrc.exec src`. -/
theorem legWeld_lower
    (src : RustSrc) (hIf : src.ifFree = true) {c : LowCT} (hNorm : LitNorm (lower src) c)
    {rs : RustState} (hRun : ∃ rs', AdeqRun c rs rs') (hIR : ScalarInRange rs)
    (name : String) (hNT : ¬ isTmpName name)
    (hReads : readsOK (fun _ => False) c) (hOut : afterB (fun _ => False) c name)
    (F : FrontOut c name)
    (fa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)))
    (P : (String → ZMod (2 ^ 64)) → Prop)
    (hCorres : Corres SRwordNT P fa c) (hP : P (derivedAbs rs)) :
    F.jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (RustSrc.exec src rs.rsScalar name))
      ∧ wEnc (BitVec.ofNat 64 (RustSrc.exec src rs.rsScalar name)) = fa (derivedAbs rs) name :=
  legWeld c (RustSrc.exec src) (rrefines_of_litNorm hNorm (lowerRefines src hIf))
    hRun hIR name hNT hReads hOut F fa P hCorres hP

end CatCrypt.Crypto.SecureCompilation.Ascent
