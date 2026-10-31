/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTStraight

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the bytes of `compileA` modulo declassification

The constant-time statement of `compileA` for a module whose source calls `declassify`. The
source leakage of a call `declassify x` is the value of `x` (`srcLeakNFD`); a source program
is constant time modulo declassification when two runs from environments agreeing on the
public variables that declassify the same sequence of values have equal leakage
(`SourceCTDOf`). For every sequence `d`, two decodings of the bytes of `compileA` run from
entry states that agree on the public data of the layout, satisfy its regions condition and
a precondition, and whose source runs declassify `d` (`HaxDeclIs`), have equal leakage
traces: this is `haxc_ct_proved_all` at the precondition `Pre ∧ HaxDeclIs d`, whose
constant-time hypothesis on the translation follows from `HaxToNFCTD`
(`haxDeclIs_haxToNFCTLOn`). The composition is checked by an `example`.

A source leakage that any two runs with the same declassified values leave equal is constant
time modulo declassification (`sourceCTDOf_of_decls_inj`). The body
`let y = declassify x; if y then a else b`, a branch on a declassified value, has the
leakage `declBranchLeak` at the value its call of `declassify` declassifies
(`srcLeakNFD_declBranch`), so it is constant time at the source modulo declassification
(`declBranch_sourceCTD`). The second `example` composes this with `haxToNFCTD_of_sourceCTD`,
`haxDeclIs_haxToNFCTLOn` and `haxc_ct_proved_all` on a module whose front body is that
program.

## Main definitions

* `HaxDeclIs` — the source runs from the valuations a layout reads off an entry state
  declassify the sequence `d`.
* `declArg`, `declBranch`, `branchLeak`, `declBranchLeak`

## Main results

* `haxDeclIs_haxToNFCTLOn` — on a module without linked functions, constant time of the
  translation modulo declassification gives the constant-time hypothesis of
  `haxc_ct_proved_all` at the precondition `Pre ∧ HaxDeclIs d`.
* `sourceCTDOf_of_decls_inj` — a leakage determined by its declassified values is constant
  time modulo declassification.
* `srcLeakNFD_declassify_var`, `srcLeakNFD_declBranch` — the leak trees of a call
  `declassify x` and of `declBranch`.
* `declBranch_sourceCTD` — `declBranch` is constant time at the source modulo
  declassification.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnvOf crateBi SrcDeclIs)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower (mapLabels)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open _root_.Hax (TExpr Value Env denote')
open CatCrypt.Crypto.Hax (hax64WExit HaxModule)

/-- **The declassified values of the source runs from an entry state**: for every valuation
    `V` of the parameters of `σ` whose lowered valuation `σ` reads off `sa`, every run of the
    body `nfBody (bindConsts σ.consts m.entry)` the front reads, under `hax64WExit`, from the
    entry environment of `V` that ends in a value declassifies the values `d`
    (`SrcDeclIs`). -/
def HaxDeclIs (σ : AbiLayout) (m : HaxModule) (d : List Value) (sa : AState) : Prop :=
  ∀ V : Ctxt.Valuation (entryCtx (abiEntry σ)),
    AbiValOf σ sa (VIR.DialectToJasminComCorrect.ctMapValD (mapVal V)) →
    SrcDeclIs hax64WExit (nfBody (bindConsts σ.consts m.entry)) d (entryEnvOf (abiEntry σ) V)

/-- **The constant-time hypothesis of `haxc_ct_proved_all` modulo declassification.** On a
    module whose `pairStage m σ` has no linked functions, constant time of the translation
    modulo declassification (`HaxToNFCTD`) gives `HaxToNFCTLOn` at the entry valuations of
    the states that satisfy `Regions` and the precondition `Pre ∧ HaxDeclIs d`.
    `haxc_ct_proved_all` with this lemma at that precondition is constant time of the bytes
    of `compileA` modulo declassification: two runs from entry states that agree on the
    public data of the layout and whose source runs declassify the same values `d` have
    equal leakage traces. -/
theorem haxDeclIs_haxToNFCTLOn {s : _root_.Hax.FnSecrecy} {m : HaxModule} {σ : AbiLayout}
    (hlk : (pairStage m σ).1.linked = [])
    (hct : HaxToNFCTD s (pairStage m σ).2 (pairStage m σ).1) (d : List Value)
    (Pre : AState → Prop) :
    HaxToNFCTLOn s (pairStage m σ).2 (pairStage m σ).1 (fun V => ∃ sa,
      (pairStage m σ).2.Regions sa ∧
      (Pre sa ∧ HaxDeclIs (pairStage m σ).2 (pairStage m σ).1 d sa) ∧
      AbiValOf (pairStage m σ).2 sa (VIR.DialectToJasminComCorrect.ctMapValD (mapVal V))) :=
  haxToNFCTLOn_of_haxToNFCTD hlk d _ (fun V hQ => by
    obtain ⟨_, -, ⟨-, hD⟩, hV⟩ := hQ
    exact hD V hV) hct

/- `haxc_ct_proved_all` at the precondition `Pre ∧ HaxDeclIs d`, with its constant-time
hypothesis given by `haxDeclIs_haxToNFCTLOn`. -/
example (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes)) (hlk : (pairStage m σ).1.linked = [])
    (F fuelC : Nat) (Pre : AState → Prop) (d : List Value)
    (hct : HaxToNFCTD s (pairStage m σ).2 (pairStage m σ).1)
    (hterm : ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2))),
      (pairStage m σ).2.Regions sa →
      (Pre sa ∧ HaxDeclIs (pairStage m σ).2 (pairStage m σ).1 d sa) →
      AbiValOf (pairStage m σ).2 sa (VIR.DialectToJasminComCorrect.ctMapValD (mapVal V)) →
      ∃ v env', (denote' (crateBi ((pairStage m σ).1.prepared nfBody)
        ((pairStage m σ).1.linkTable hax64WExit) fuelC (pairStage m σ).1.depth)
        F (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry))).run
          (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup) {prog : List RInstr}
    (hd : decodeLprog bytes = some prog) (hnd : (m.linked.map (·.name)).Nodup)
    (hk : ∀ l ∈ m.linked, RegionLinkCall.LinkedKernel l) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂
        ∧ (Pre s₁ ∧ HaxDeclIs (pairStage m σ).2 (pairStage m σ).1 d s₁)
        ∧ (Pre s₂ ∧ HaxDeclIs (pairStage m σ).2 (pairStage m σ).1 d s₂)
        ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  haxc_ct_proved_all s m σ fname P bytes hc F fuelC
    (fun sa => Pre sa ∧ HaxDeclIs (pairStage m σ).2 (pairStage m σ).1 d sa)
    (haxDeclIs_haxToNFCTLOn hlk hct d Pre) hterm hL hnds hd hnd hk

/-! ## A source leakage determined by its declassified values -/

open CatCrypt.Crypto.Hax (SrcLeak SrcEv SourceCTDOf contLeak)
open CatCrypt.Crypto.Hax.ImpToNF (srcLeakNFD srcLeakCl srcArgsLeakCl nfDeclCallLeak)
open _root_.Hax (ImpExpr ImpLit Builtins)

/-- **Source constant time modulo declassification of a leakage determined by its
    declassified values.** When any two leakages of `e` at one fuel with the same declassified
    values are equal, `e` is constant time at the source modulo declassification for `L`, at
    every level table. -/
theorem sourceCTDOf_of_decls_inj {bi : Builtins} {L : ImpExpr → Nat → Env → SrcLeak}
    {lt : CatCrypt.Crypto.Jasmin.LowCT.LevelTable} {e : ImpExpr}
    (h : ∀ fuel env₁ env₂, (L e fuel env₁).decls = (L e fuel env₂).decls →
      L e fuel env₁ = L e fuel env₂) : SourceCTDOf bi L lt e :=
  fun _ fuel env₁ env₂ _ _ _ _ _ _ _ _ _ hd₁ hd₂ => h fuel env₁ env₂ (hd₁.trans hd₂.symm)

/-- The value a call `declassify x` declassifies from `env`: the value of `x`, unless it is
    unbound or a control-flow value. -/
def declArg (env : Env) (x : String) : Option Value :=
  (env x).filter fun v => !v.isControlFlow

/-- The source leakage `srcLeakNFD` of a call `declassify x` is the leaf `declass v` at the
    value `v` the call declassifies (`declArg`), after the empty leakage of its argument. -/
theorem srcLeakNFD_declassify_var (bi : Builtins) (x : String) (fuel : Nat) (env : Env) :
    srcLeakNFD bi (.app "declassify" [.var x]) fuel env =
      .cat (.cat .nil .nil) ((declArg env x).elim .nil fun v => .ev (.declass v)) := by
  unfold declArg
  rcases hx : env x with _ | v
  · simp [srcLeakNFD, srcLeakCl, srcArgsLeakCl, contLeak, _root_.Hax.denoteArgs',
      _root_.Hax.denote', hx, StateT.run, get, getThe, MonadStateOf.get, StateT.get, bind,
      StateT.bind, pure, StateT.pure]
  · cases v <;> simp [srcLeakNFD, srcLeakCl, srcArgsLeakCl, contLeak, _root_.Hax.denoteArgs',
      _root_.Hax.denote', hx, StateT.run, get, getThe, MonadStateOf.get, StateT.get, bind,
      StateT.bind, pure, StateT.pure, nfDeclCallLeak, Option.filter, Value.isControlFlow]

/-- The body `let y = declassify x; if y then a else b`: a branch on a declassified value. -/
def declBranch (x y : String) (a b : ImpLit) : ImpExpr :=
  .letBind y (.app "declassify" [.var x]) (.ifThenElse (.var y) (.lit a) (.lit b))

/-- The leakage of the branch of `declBranch` on the result `w` of the call of `declassify`:
    the outcome of the condition when `w` is a Boolean. -/
def branchLeak : Value → SrcLeak
  | .bool true => .cat .nil (.cat (.ev (.branch true)) .nil)
  | .bool false => .cat .nil (.cat (.ev (.branch false)) .nil)
  | _ => .cat .nil .nil

/-- The leakage of `declBranch` at the declassified value `o`: the leaf `declass v` and, at
    the result `w` of the builtin `declassify` on `v`, the branch `branchLeak w`. -/
def declBranchLeak (bi : Builtins) : Option Value → SrcLeak
  | some v => .cat (.cat (.cat .nil .nil) (.ev (.declass v)))
      (match bi "declassify" [v] with
       | some (.controlFlow _ _) => .nil
       | some w => branchLeak w
       | none => .nil)
  | none => .cat (.cat (.cat .nil .nil) .nil) .nil

/-- **The leak tree of `declBranch`**: the source leakage `srcLeakNFD` of a run of
    `declBranch x y a b` from `env` is `declBranchLeak` at the value the call of `declassify`
    declassifies (`declArg`). -/
theorem srcLeakNFD_declBranch (bi : Builtins) (x y : String) (a b : ImpLit) (fuel : Nat)
    (env : Env) :
    srcLeakNFD bi (declBranch x y a b) fuel env = declBranchLeak bi (declArg env x) := by
  unfold declBranch declArg
  rcases hx : env x with _ | v
  · simp [srcLeakNFD, srcLeakCl, srcArgsLeakCl, contLeak, _root_.Hax.denoteArgs',
      _root_.Hax.denote', _root_.Hax.denoteApp', hx, StateT.run, get, getThe,
      MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, declBranchLeak]
  · have hlet : srcLeakNFD bi (.letBind y (.app "declassify" [.var x])
          (.ifThenElse (.var y) (.lit a) (.lit b))) fuel env =
        .cat (srcLeakNFD bi (.app "declassify" [.var x]) fuel env)
          (contLeak ((_root_.Hax.denote' bi fuel (.app "declassify" [.var x])).run env)
            fun w e1 => srcLeakNFD bi (.ifThenElse (.var y) (.lit a) (.lit b)) fuel
              (e1.extend y w)) := rfl
    have hargs : (_root_.Hax.denoteArgs' bi fuel [.var x]).run env =
        (if v.isControlFlow then none else some [v], env) := by
      grind only [Hax.ContinueFlag.args_cons_run, Hax.ContinueFlag.var_run,
        Hax.ContinueFlag.args_nil_run, args_cons_cf, Hax.args_cons_of]
    rw [hlet, srcLeakNFD_declassify_var, _root_.Hax.ContinueFlag.app_run, hargs]
    unfold declArg
    rw [hx]
    have hk : ∀ w, srcLeakNFD bi (.ifThenElse (.var y) (.lit a) (.lit b)) fuel
        (env.extend y w) = branchLeak w := by
      intro w
      simp only [srcLeakNFD, srcLeakCl, _root_.Hax.ContinueFlag.var_run,
        _root_.Hax.Env.extend_same]
      rcases w with ⟨⟨⟩⟩ <;> rfl
    cases hc : v.isControlFlow
    · simp only [Option.filter, hc, Bool.not_false, ite_true, ite_false, Bool.false_eq_true,
        Option.elim, declBranchLeak]
      generalize bi "declassify" [v] = r
      rcases r with _ | ⟨⟨⟩⟩ <;> first | rfl | exact congrArg _ (hk _)
    · simp only [Option.filter, hc, Bool.not_true, ite_true, ite_false, Bool.false_eq_true]
      rfl

/-- The declassified values of `declBranchLeak bi o` are the values of `o`. -/
theorem declBranchLeak_decls (bi : Builtins) (o : Option Value) :
    (declBranchLeak bi o).decls = o.toList := by
  have hb : ∀ w, (branchLeak w).decls = [] := fun w => by
    unfold branchLeak; split <;> rfl
  cases o with
  | none => rfl
  | some v =>
    simp only [declBranchLeak]
    split <;> simp [SrcLeak.decls, SrcEv.declOf, hb]

/-- **`declBranch` is constant time at the source modulo declassification**: its leakage
    `srcLeakNFD` is determined by its declassified values, at every level table. -/
theorem declBranch_sourceCTD (bi : Builtins) (x y : String) (a b : ImpLit)
    (lt : CatCrypt.Crypto.Jasmin.LowCT.LevelTable) :
    SourceCTDOf bi (srcLeakNFD bi) lt (declBranch x y a b) := by
  refine sourceCTDOf_of_decls_inj fun fuel env₁ env₂ h => ?_
  rw [srcLeakNFD_declBranch, srcLeakNFD_declBranch, declBranchLeak_decls,
    declBranchLeak_decls] at h
  rw [srcLeakNFD_declBranch, srcLeakNFD_declBranch]
  congr 1
  revert h
  cases declArg env₁ x <;> cases declArg env₂ x <;> simp

/- `haxc_ct_proved_all` on a module without callee, depth or linked function whose front
body is `declBranch x y a b`: constant time of the decoded bytes of `compileA` between entry
states whose source runs declassify the same values `d`. -/
example (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hfns : (pairStage m σ).1.fns = []) (hdep : (pairStage m σ).1.depth = 0)
    (hlk : (pairStage m σ).1.linked = [])
    (hps : ∀ p ∈ abiEntry (pairStage m σ).2, ∃ b, (p.1, b) ∈ s.params)
    (x y : String) (a b : ImpLit)
    (hb : nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry) =
      declBranch x y a b)
    (F : Nat) (Pre : AState → Prop) (d : List Value)
    (hterm : ∀ V : Ctxt.Valuation (entryCtx (abiEntry (pairStage m σ).2)), ∃ v env',
      (denote' hax64WExit F (declBranch x y a b)).run
        (entryEnvOf (abiEntry (pairStage m σ).2) V) = (.val v, env'))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup) {prog : List RInstr}
    (hd : decodeLprog bytes = some prog) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂
        ∧ (Pre s₁ ∧ HaxDeclIs (pairStage m σ).2 (pairStage m σ).1 d s₁)
        ∧ (Pre s₂ ∧ HaxDeclIs (pairStage m σ).2 (pairStage m σ).1 d s₂)
        ∧ (∃ v, haxRuns σ m s₁ v) ∧ (m.linked = [] ∨ ∃ v, haxRuns σ m s₂ v))
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  have hml : m.linked = [] := (pairStage_linked m σ).symm.trans hlk
  have hct : HaxToNFCTD s (pairStage m σ).2 (pairStage m σ).1 :=
    haxToNFCTD_of_sourceCTD s _ hfns hdep hlk hps
      (by rw [hb]; exact declBranch_sourceCTD hax64WExit x y a b _) F
      (by rw [hb]; exact hterm)
  refine haxc_ct_proved_all s m σ fname P bytes hc F 0
    (fun sa => Pre sa ∧ HaxDeclIs (pairStage m σ).2 (pairStage m σ).1 d sa)
    (haxDeclIs_haxToNFCTLOn hlk hct d Pre) ?_ hL hnds hd (by rw [hml]; exact List.nodup_nil)
    (fun l h => by simp [hml] at h)
  intro _ V _ _ _
  rw [crateBi_prepared_of_fns_nil hfns, HaxModule.linkTable_of_linked_nil hlk, hb]
  exact hterm V

end CatCrypt.Crypto.SecureCompilation.Haxc
