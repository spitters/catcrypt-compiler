/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Program
public import CatCrypt.Crypto.SecureCompilation.Ascent.PipelineWeld

/-!
# The source-word bridge

Two reference semantics meet here.  `CatCrypt.Hax.denote` (this repository,
`CatCrypt/Hax/Semantics.lean`) is the semantics the simulation
`haxToLowCT_simulates_program` runs over; its `Value` has the untyped `int`
constructor and `valueToScalar` reads a scalar from it.  `Hax.denote`
(`../hax-lean`) is the semantics `PipelineWeld` runs over; its `Value` has the
width-indexed `uint` constructor that `haxOutcomeWord` reads.  The two `ImpExpr`
types are distinct inductives.

§1 reads a word out of a `CatCrypt.Hax` outcome and derives it from the
simulation's exit agreement: for a program that returns a variable `r`, the word
of the source outcome is the word the `RustExec` run leaves in the scalar slot
`r`.  §2 lifts this to the program-level simulation.  §3 discharges
`PipelineWeld`'s `hBridge` for the `feSub` kernel by evaluating the hax-lean
reference semantics on the kernel's `ImpExpr` at the width-aware builtin table
(`defaultBuiltins` has no `sub` on `uint` values and returns an error outcome),
together with the loop-freeness and early-exit-freeness side conditions.  §4
is the emit weld on the program-level simulation, and §5 instantiates
`feSub_raw_source_to_bytes` at the `feSub` kernel.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec)
open CatCrypt.Crypto.Hax
  (evalImp valueToScalar envAgreesRust envAgreesRustFull ValueTowerBridge FullSimPreconds
   ProjPreconds ProgramSimArms TowerScope ScopeBound NamesFresh simScope scalarNames
   SimWellFormed haxToLowCT_simulates_program evalImp_seq_inv evalImp_var_inv)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## §1  The word of a `CatCrypt.Hax` outcome -/

/-- The 64-bit word of a `CatCrypt.Hax` reference-semantics outcome: a normally
    terminating non-negative integer value, reinterpreted as a `BitVec 64`. -/
def impOutcomeWord : CatCrypt.Hax.Outcome → Option (BitVec 64)
  | .val (.int n) => if 0 ≤ n then some (BitVec.ofNat 64 n.toNat) else none
  | _ => none

/-- A successful `evalImp` pins the outcome of `denote`. -/
theorem denote_fst_of_evalImp (bi : CatCrypt.Hax.Builtins) (fuel : Nat)
    (e : CatCrypt.Hax.ImpExpr) (env env' : CatCrypt.Hax.Env) (v : CatCrypt.Hax.Value)
    (h : evalImp bi fuel e env = some (v, env')) :
    (CatCrypt.Hax.denote bi fuel e env).1 = .val v := by
  unfold evalImp at h
  rcases hD : (CatCrypt.Hax.denote bi fuel e).run env with ⟨o, e2⟩
  rw [hD] at h
  cases o with
  | val w =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact congrArg Prod.fst hD
  | _ => cases h

/-- **`outcomeWord_of_agree`.**  For a source evaluation whose result `v` is the
    value of the variable `r` in the exit environment, and an exit state agreeing
    with it, the outcome's word is the scalar the state holds at `r`. -/
theorem outcomeWord_of_agree (bi : CatCrypt.Hax.Builtins) (fuel : Nat)
    (e : CatCrypt.Hax.ImpExpr) (env env' : CatCrypt.Hax.Env) (v : CatCrypt.Hax.Value)
    (rs' : RustState) (r : String) (n : Int)
    (hEval : evalImp bi fuel e env = some (v, env'))
    (hRet : env' r = some v) (hInt : v = .int n) (hNonneg : 0 ≤ n)
    (hAgree : envAgreesRust env' rs') :
    impOutcomeWord (CatCrypt.Hax.denote bi fuel e env).1
      = some (BitVec.ofNat 64 (rs'.rsScalar r)) := by
  rw [denote_fst_of_evalImp bi fuel e env env' v hEval, hInt]
  have hDec : valueToScalar (.int n) = some n.toNat := by
    simp [valueToScalar, hNonneg]
  have hScalar : rs'.rsScalar r = n.toNat := hAgree r v hRet n.toNat (hInt ▸ hDec)
  rw [hScalar]
  simp [impOutcomeWord, hNonneg]

/-! ## §2  The word bridge on the program-level simulation -/

/-- **`program_source_word`.**  For a checked program `body; r` returning the
    variable `r`, the `RustExec` run of its image leaves in the scalar slot `r`
    the word of the source outcome. -/
theorem program_source_word
    (bridge : ValueTowerBridge) (bi : CatCrypt.Hax.Builtins) (fuel N : Nat)
    (leafSpec : LeafSpec) (S : List String)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hProj : ProjPreconds bridge leafSpec)
    (hArms : ProgramSimArms bridge bi N leafSpec S)
    (body : CatCrypt.Hax.ImpExpr) (r : String) (Γ Γ' : TowerScope) (c : LowCT)
    (env env' : CatCrypt.Hax.Env) (rs : RustState) (n : Int)
    (hScope : simScope S Γ (.seq body (.var r)) = some Γ')
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : CatCrypt.Crypto.Hax.haxToLowCT (.seq body (.var r)) = some c)
    (hEval : evalImp bi fuel (.seq body (.var r)) env = some (.int n, env'))
    (hNonneg : 0 ≤ n)
    (hAgree : envAgreesRustFull bridge env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧
      impOutcomeWord (CatCrypt.Hax.denote bi fuel (.seq body (.var r)) env).1
        = some (BitVec.ofNat 64 (rs'.rsScalar r)) := by
  obtain ⟨rs', hExec, hAgree', _, _⟩ :=
    haxToLowCT_simulates_program bridge bi N leafSpec S hPre hProj hArms
      (.seq body (.var r)) fuel Γ Γ' c env env' rs (.int n)
      hScope hSB hSF hHax hEval hAgree
  refine ⟨rs', hExec, ?_⟩
  obtain ⟨_, env_mid, _, hVar⟩ := evalImp_seq_inv bi fuel body (.var r) env (.int n) env' hEval
  obtain ⟨hRet, henv⟩ := evalImp_var_inv bi fuel r env_mid (.int n) env' hVar
  subst henv
  exact outcomeWord_of_agree bi fuel _ env env' (.int n) rs' r n hEval hRet rfl hNonneg hAgree'.1

/-! ## §3  The `feSub` kernel on the hax-lean side -/

/-- The `feSub` kernel `r0 := a0 - b0` as a hax-lean `ImpExpr`: the two literal
    64-bit inputs, the subtraction, and the read of `r0`. -/
def feSubImp : _root_.Hax.ImpExpr :=
  .letBind "a0" (.lit (.uintLit .w64 av))
    (.letBind "b0" (.lit (.uintLit .w64 bv))
      (.seq (.assign "r0" (.app "sub" [.var "a0", .var "b0"])) (.var "r0")))

/-- The source word of the `feSub` kernel is the literal `av - bv`. -/
theorem feSubSourceWord_eq_lit : feSubSourceWord = BitVec.ofNat 64 776999927 := by
  unfold feSubSourceWord feSubSrc
  decide

/-- The hax-lean reference semantics of `feSubImp`, at the width-aware builtin
    table `widthAwareBuiltins` (whose `sub` accepts `uint` arguments), returns
    the word `feSubSourceWord`, from every environment and at every fuel. -/
theorem feSubImp_word (fuel : Nat) (env : _root_.Hax.Env) :
    haxOutcomeWord (_root_.Hax.denote _root_.Hax.widthAwareBuiltins fuel feSubImp env).1
      = some feSubSourceWord := by
  rw [feSubSourceWord_eq_lit]
  simp [feSubImp, _root_.Hax.denote, _root_.Hax.denoteArgs,
    bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, _root_.Hax.Value.ofLit,
    _root_.Hax.Env.extend, _root_.Hax.widthAwareBuiltins, _root_.Hax.widthOps,
    _root_.Hax.widthArithOps, _root_.Hax.wrapUint, _root_.Hax.IntWidth.modulus,
    _root_.Hax.IntWidth.bits, av, bv, haxOutcomeWord]

/-- `feSubImp` after the pipeline's reference-dropping and local-mutation phases
    contains no loop construct. -/
theorem feSubImp_noLoops :
    _root_.Hax.NoLoops (_root_.Hax.localMutation (_root_.Hax.mutatedVars feSubImp)
      (_root_.Hax.dropReferences feSubImp)) := by
  simp [feSubImp, _root_.Hax.localMutation, _root_.Hax.mutatedVars, _root_.Hax.dropReferences]
  repeat' first
    | constructor
    | (intro a ha
       simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
       rcases ha with rfl | rfl)

/-- `feSubImp` after the pipeline's reference-dropping and local-mutation phases
    contains no early exit. -/
theorem feSubImp_noEarlyExit :
    _root_.Hax.NoEarlyExit (_root_.Hax.localMutation (_root_.Hax.mutatedVars feSubImp)
      (_root_.Hax.dropReferences feSubImp)) :=
  _root_.Hax.checkNoEarlyExit_sound _ (by decide)

/-! ## §4  The emit weld on the program-level simulation -/

section WeldingProgram

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy CVar Ctx)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap RustStateInterp)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)

/-- **`welding_program`.** `welding` with the `RustExec` premise discharged by
    the program-level simulation `haxToLowCT_simulates_program`: the extracted
    `ImpExpr e`, accepted by the scope checker from the entry scope `Γ`,
    evaluated by `evalImp` to `(v, henv')`, in agreement with an entry state `rs`
    bound on `Γ` and fresh on the scalar names `S`, reaches the emitted bytes'
    clean `ZMod 2^64` spec. -/
theorem welding_program
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec)
    (env' : SEnvScalar) (name : String) (w : CVar o.Γ' (.sword 64)) (val : BitVec 64)
    (com : Com catCryptDialect ([] : Ctx) (.sword 64))
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)))
    (fa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)))
    (P : (String → ZMod (2 ^ 64)) → Prop)
    (env₀ : SEnvScalar) (a₀ : String → ZMod (2 ^ 64))
    (bridge : CatCrypt.Crypto.Hax.ValueTowerBridge) (bi : CatCrypt.Hax.Builtins)
    (fuel : Nat) (S : List String)
    (hPre : CatCrypt.Crypto.Hax.FullSimPreconds bi leafSpec bridge)
    (hProj : CatCrypt.Crypto.Hax.ProjPreconds bridge leafSpec)
    (hArms : CatCrypt.Crypto.Hax.ProgramSimArms bridge bi N leafSpec S)
    (e : CatCrypt.Hax.ImpExpr) (Γ Γ' : CatCrypt.Crypto.Hax.TowerScope)
    (henv henv' : CatCrypt.Hax.Env) (rs : RustState) (v : CatCrypt.Hax.Value)
    (hScope : CatCrypt.Crypto.Hax.simScope S Γ e = some Γ')
    (hSB : CatCrypt.Crypto.Hax.ScopeBound rs Γ)
    (hSF : CatCrypt.Crypto.Hax.NamesFresh rs S)
    (hHax : CatCrypt.Crypto.Hax.haxToLowCT e = some c)
    (hEval : CatCrypt.Crypto.Hax.evalImp bi fuel e henv = some (v, henv'))
    (hAgreeSrc : CatCrypt.Crypto.Hax.envAgreesRustFull bridge henv rs)
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl VarMap.empty c = some o)
    (hSem : semScalar c (fun _ => none) = some env')
    (hName : o.vm.lookup name = some ⟨.sword 64, w⟩)
    (hVal : env' name = some ⟨.sword 64, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hCorres : Corres SRword P fa c) (hSR : SRword env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩) :
    jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy val
      ∧ wEnc val = fa a₀ name := by
  obtain ⟨rs', hExec, _, _, _⟩ :=
    CatCrypt.Crypto.Hax.haxToLowCT_simulates_program bridge bi N leafSpec S hPre hProj hArms
      e fuel Γ Γ' c henv henv' rs v hScope hSB hSF hHax hEval hAgreeSrc
  exact keystone_emit c o N leafSpec rs rs' env' name w val com jcom fa P env₀ a₀
    hCov hTrans hExec hSem hName hVal hRet hCom hCorres hSR hP hAgree

/-! ## §5  The `feSub` kernel from raw source to bytes -/

/-- **`feSubImp_raw_source_to_bytes`.**  `feSub_raw_source_to_bytes` at the
    kernel `feSubImp` and the width-aware builtin table: the optimized program
    `pipeline feSubImp` evaluates to `feSubSourceWord`, that word reaches the
    emitted jasmin program `feJcom`, and its clean `ZMod 2^64` spec is
    `av - bv`.  The word bridge is `feSubImp_word`; the loop-freeness and
    early-exit-freeness side conditions are `feSubImp_noLoops` and
    `feSubImp_noEarlyExit`. -/
theorem feSubImp_raw_source_to_bytes (N : Nat) (leafSpec : LeafSpec) (fuel : Nat)
    (env : _root_.Hax.Env) :
    haxOutcomeWord (_root_.Hax.denote _root_.Hax.widthAwareBuiltins fuel
        (_root_.Hax.pipeline feSubImp) env).1 = some feSubSourceWord
      ∧ feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
          = ctTransTy feSubSourceWord
      ∧ wEnc feSubSourceWord
          = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) :=
  feSub_raw_source_to_bytes N leafSpec _root_.Hax.widthAwareBuiltins fuel env feSubImp
    feSubImp_noLoops feSubImp_noEarlyExit (feSubImp_word fuel env)

end WeldingProgram

end CatCrypt.Crypto.SecureCompilation.Ascent
