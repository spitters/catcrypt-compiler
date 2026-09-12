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

The simulation `haxToLowCT_simulates_program` and the weld `PipelineWeld` run
over one reference semantics, hax-lean's `Hax.denote`.  Its `Value` has the
width-indexed `uint` constructor; `valueToScalar` reads the scalar slot from it
and `haxOutcomeWord` reads the 64-bit word from it.

§1 derives the word of a source outcome from the simulation's exit agreement:
for a program that returns a variable `r` holding a `uint` value, the word of the
source outcome is the word the `RustExec` run leaves in the scalar slot `r`; a
second lemma gives the scalar slot for an `int` value, the value kind
`defaultBuiltins` produces.  §2 lifts this to the program-level simulation and
derives `raw_source_to_bytes_of_program`, which discharges
`feSub_raw_source_to_bytes`'s word identification `hBridge` from the
program-level simulation's side conditions and the output condition on the
lowered program.  §3 discharges `hBridge` for the `feSub` kernel by evaluating
the reference semantics on the kernel's `ImpExpr` at the width-aware builtin
table (`defaultBuiltins` has no `sub` on `uint` values and returns an error
outcome), together with the loop-freeness and early-exit-freeness side
conditions.  §4 is the emit weld on the program-level simulation, and §5
instantiates `feSub_raw_source_to_bytes` at the `feSub` kernel.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec)
open CatCrypt.Crypto.Hax
  (evalImp valueToScalar envAgreesRust envAgreesRustFull ValueTowerBridge FullSimPreconds
   ProjPreconds ProgramSimArms TowerScope ScopeBound NamesFresh simScope scalarNames
   SimWellFormed haxToLowCT_simulates_program evalImp_seq_inv evalImp_var_inv)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (Ctx)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## §1  The word of a source outcome -/

/-- A successful `evalImp` pins the outcome of `denote`. -/
theorem denote_fst_of_evalImp (bi : _root_.Hax.Builtins) (fuel : Nat)
    (e : _root_.Hax.ImpExpr) (env env' : _root_.Hax.Env) (v : _root_.Hax.Value)
    (h : evalImp bi fuel e env = some (v, env')) :
    (_root_.Hax.denote bi fuel e env).1 = .val v := by
  unfold evalImp at h
  rcases hD : (_root_.Hax.denote bi fuel e).run env with ⟨o, e2⟩
  rw [hD] at h
  cases o with
  | val w =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact congrArg Prod.fst hD
  | _ => cases h

/-- **`outcomeWord_of_agree`.**  For a source evaluation whose result `v` is the
    `uint` value of the variable `r` in the exit environment, and an exit state
    agreeing with it, the outcome's word is the scalar the state holds at `r`. -/
theorem outcomeWord_of_agree (bi : _root_.Hax.Builtins) (fuel : Nat)
    (e : _root_.Hax.ImpExpr) (env env' : _root_.Hax.Env) (v : _root_.Hax.Value)
    (rs' : RustState) (r : String) (w : _root_.Hax.IntWidth) (n : Nat)
    (hEval : evalImp bi fuel e env = some (v, env'))
    (hRet : env' r = some v) (hUint : v = .uint w n)
    (hAgree : envAgreesRust env' rs') :
    haxOutcomeWord (_root_.Hax.denote bi fuel e env).1
      = some (BitVec.ofNat 64 (rs'.rsScalar r)) := by
  rw [denote_fst_of_evalImp bi fuel e env env' v hEval, hUint]
  have hScalar : rs'.rsScalar r = n := hAgree r v hRet n (by rw [hUint]; rfl)
  rw [hScalar]
  rfl

/-- **`outcomeWord_of_agree_int`.**  The `int` form of `outcomeWord_of_agree`, for
    programs over `defaultBuiltins`, whose arithmetic produces `int` values: the
    source outcome is the value `.int n`, and the scalar the exit state holds at
    `r` is `n.toNat`. -/
theorem outcomeWord_of_agree_int (bi : _root_.Hax.Builtins) (fuel : Nat)
    (e : _root_.Hax.ImpExpr) (env env' : _root_.Hax.Env) (v : _root_.Hax.Value)
    (rs' : RustState) (r : String) (n : Int)
    (hEval : evalImp bi fuel e env = some (v, env'))
    (hRet : env' r = some v) (hInt : v = .int n) (hNonneg : 0 ≤ n)
    (hAgree : envAgreesRust env' rs') :
    (_root_.Hax.denote bi fuel e env).1 = .val (.int n)
      ∧ rs'.rsScalar r = n.toNat := by
  refine ⟨hInt ▸ denote_fst_of_evalImp bi fuel e env env' v hEval, ?_⟩
  have hDec : valueToScalar (.int n) = some n.toNat := by
    simp [valueToScalar, hNonneg]
  exact hAgree r v hRet n.toNat (hInt ▸ hDec)

/-! ## §2  The word bridge on the program-level simulation -/

/-- **`program_source_word`.**  For a checked program `body; r` returning the
    variable `r` with a `uint` value, the `RustExec` run of its image leaves in
    the scalar slot `r` the word of the source outcome. -/
theorem program_source_word
    (bridge : ValueTowerBridge) (bi : _root_.Hax.Builtins) (fuel N : Nat)
    (leafSpec : LeafSpec) (S : List String)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hProj : ProjPreconds bridge leafSpec)
    (hArms : ProgramSimArms bridge bi N leafSpec S)
    (body : _root_.Hax.ImpExpr) (r : String) (Γ Γ' : TowerScope) (c : LowCT)
    (env env' : _root_.Hax.Env) (rs : RustState) (w : _root_.Hax.IntWidth) (n : Nat)
    (hScope : simScope S Γ (.seq body (.var r)) = some Γ')
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : CatCrypt.Crypto.Hax.haxToLowCT (.seq body (.var r)) = some c)
    (hEval : evalImp bi fuel (.seq body (.var r)) env = some (.uint w n, env'))
    (hAgree : envAgreesRustFull bridge env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧
      haxOutcomeWord (_root_.Hax.denote bi fuel (.seq body (.var r)) env).1
        = some (BitVec.ofNat 64 (rs'.rsScalar r)) := by
  obtain ⟨rs', hExec, hAgree', _, _⟩ :=
    haxToLowCT_simulates_program bridge bi N leafSpec S hPre hProj hArms
      (.seq body (.var r)) fuel Γ Γ' c env env' rs (.uint w n)
      hScope hSB hSF hHax hEval hAgree
  refine ⟨rs', hExec, ?_⟩
  obtain ⟨_, env_mid, _, hVar⟩ :=
    evalImp_seq_inv bi fuel body (.var r) env (.uint w n) env' hEval
  obtain ⟨hRet, henv⟩ := evalImp_var_inv bi fuel r env_mid (.uint w n) env' hVar
  subst henv
  exact outcomeWord_of_agree bi fuel _ env env' (.uint w n) rs' r w n hEval hRet rfl hAgree'.1

/-- **`raw_source_to_bytes_of_program`.**  `feSub_raw_source_to_bytes` with the word
    identification `hBridge` discharged by the program-level simulation.

    The raw program is `body; r`, returning the variable `r` with a `uint` value.
    Its hypotheses are the program-level simulation's side conditions (the scope
    checker `simScope`, `ScopeBound` and `NamesFresh` on the entry state,
    `FullSimPreconds`, `ProjPreconds`, `ProgramSimArms`, the entry agreement), the
    loop-freeness and early-exit-freeness of its post-phase-1-2 form, and the
    output condition `hOut` on the lowered program `c`: every `RustExec` run of
    `c` from the entry state leaves the word `feSubSourceWord` in the scalar slot
    `r`.  The conclusion is `feSub_raw_source_to_bytes`'s: the optimized program
    `pipeline (body; r)` evaluates to `feSubSourceWord`, which reaches the emitted
    program `feJcom`, whose clean `ZMod 2^64` spec is `av - bv`. -/
theorem raw_source_to_bytes_of_program
    (bridge : ValueTowerBridge) (bi : _root_.Hax.Builtins) (fuel N : Nat)
    (leafSpec : LeafSpec) (S : List String)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hProj : ProjPreconds bridge leafSpec)
    (hArms : ProgramSimArms bridge bi N leafSpec S)
    (body : _root_.Hax.ImpExpr) (r : String) (Γ Γ' : TowerScope) (c : LowCT)
    (env env' : _root_.Hax.Env) (rs : RustState) (w : _root_.Hax.IntWidth) (n : Nat)
    (hScope : simScope S Γ (.seq body (.var r)) = some Γ')
    (hSB : ScopeBound rs Γ) (hSF : NamesFresh rs S)
    (hHax : CatCrypt.Crypto.Hax.haxToLowCT (.seq body (.var r)) = some c)
    (hEval : evalImp bi fuel (.seq body (.var r)) env = some (.uint w n, env'))
    (hAgree : envAgreesRustFull bridge env rs)
    (hOut : ∀ rs', RustExec N leafSpec c rs rs' →
      BitVec.ofNat 64 (rs'.rsScalar r) = feSubSourceWord)
    (hNoLoops : _root_.Hax.NoLoops
      (_root_.Hax.localMutation (_root_.Hax.mutatedVars (.seq body (.var r)))
        (_root_.Hax.dropReferences (.seq body (.var r)))))
    (hNoEE : _root_.Hax.NoEarlyExit
      (_root_.Hax.localMutation (_root_.Hax.mutatedVars (.seq body (.var r)))
        (_root_.Hax.dropReferences (.seq body (.var r))))) :
    haxOutcomeWord (_root_.Hax.denote bi fuel (_root_.Hax.pipeline (.seq body (.var r))) env).1
        = some feSubSourceWord
      ∧ feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
          = ctTransTy feSubSourceWord
      ∧ wEnc feSubSourceWord
          = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) := by
  obtain ⟨rs', hExec, hWord⟩ :=
    program_source_word bridge bi fuel N leafSpec S hPre hProj hArms body r Γ Γ' c
      env env' rs w n hScope hSB hSF hHax hEval hAgree
  exact feSub_raw_source_to_bytes N leafSpec bi fuel env (.seq body (.var r))
    hNoLoops hNoEE (hWord.trans (congrArg some (hOut rs' hExec)))

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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)

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
    (bridge : CatCrypt.Crypto.Hax.ValueTowerBridge) (bi : _root_.Hax.Builtins)
    (fuel : Nat) (S : List String)
    (hPre : CatCrypt.Crypto.Hax.FullSimPreconds bi leafSpec bridge)
    (hProj : CatCrypt.Crypto.Hax.ProjPreconds bridge leafSpec)
    (hArms : CatCrypt.Crypto.Hax.ProgramSimArms bridge bi N leafSpec S)
    (e : _root_.Hax.ImpExpr) (Γ Γ' : CatCrypt.Crypto.Hax.TowerScope)
    (henv henv' : _root_.Hax.Env) (rs : RustState) (v : _root_.Hax.Value)
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
