/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-!
# A concrete covered kernel through the `RustExec` value-adequacy bridge

`RustExecSemScalarBridge.rustExec_semScalar_agree` proves, on the covered word
fragment `IsCoveredAdeq`, that a `RustExec` `Nat`-model run is tracked by a
`semScalar` machine-word run related by `EnvRel`. This module instantiates that
bridge on ONE concrete straight-line kernel end-to-end and discharges its
**entry seam** — the entry environment reflecting the `RustExec` inputs.

## The kernel

```
kC := RScalarSet "a" 3 ;  RScalarSetExpr "r" (SXor (SVar "a") (SLit 5))
```

A two-statement closed straight-line body: write `3` to `a`, then set `r` to
the bitwise expression `a ^ 5`. Bitwise (not additive) so the hoisted
no-overflow bound of the `RScalarSetExpr` arm holds from `u64`-range inputs
alone (`SXor` carries no overflow side condition, unlike `SAdd`). The reference
`RustExec` output is `r = 3 ^ 5 = 6`.

## The entry seam (discharged)

The command-level bridge takes `EnvRel rs env` at entry — the source env must
reflect the `RustExec` inputs as their `ofNat` images. The bridge's own
`derivedEnv` / `envRel_derivedEnv` construct exactly such an env for any entry
state: the canonical fully-populated env `derivedEnv rs` satisfies `EnvRel rs`
by construction. This is the reusable per-kernel entry discharge: a
straight-line kernel run from any `ScalarInRange` entry state is tracked, with
the entry env supplied by `derivedEnv`.

## What this does NOT compose to

The value leg (`semScalar` output = `RustExec` output) is delivered here axiom
clean. Fusing it with the jasmin denotation leg
(`rustToJasminCom_endToEnd_rustexec_adeq`) additionally needs
`ConsistentS vm V env` for the SAME `env`. `ConsistentS` pins `env`'s domain to
`vm`'s (a finite `VarMap` over a finite context `Γ`), while `EnvRel` binds every
non-temp name; `NoAliasVM` (a field of `RustStateInterp`) forces the bound names
to inject into the finitely-many De Bruijn slots of `Γ`. The three are therefore
jointly unsatisfiable at any finite `Γ` — see `entry_trio_unsat_empty` for the
`VarMap.empty` witness of the clash. The genuine closed jasmin-leg result is
obtained instead through the empty-entry-env route
(`rustToJasminCom_endToEnd_topLevel_unconditional`), valid because a closed
straight-line kernel's reads all follow their writes, so `semScalar` succeeds
from the empty env with no entry `EnvRel` needed — see §D.
-/

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq

/-! ## The concrete kernel -/

/-- The bitwise scalar expression `a ^ 5`. Bitwise so its `inRange` needs only
    `u64`-range inputs (no additive overflow side condition). -/
def kE : SExpr := .SXor (.SVar "a") (.SLit 5)

/-- The kernel: `a := 3 ; r := a ^ 5`. -/
def kC : LowCT := .RSeq (.RScalarSet "a" 3) (.RScalarSetExpr "r" kE)

/-! ## Non-temporary names

The source variables `a`, `r` are not in the reserved `__sx` fresh-temp
namespace (`tmpName k = "__sx" ++ toString k` has length ≥ 4). -/

theorem not_isTmp_a : ¬ isTmpName "a" := by
  rintro ⟨k, hk⟩
  have hlen := congrArg String.length hk
  rw [TranslateDialectDirectArms.tmpName, String.length_append] at hlen
  have h1 : "a".length = 1 := rfl
  have h2 : "__sx".length = 4 := rfl
  omega

theorem not_isTmp_r : ¬ isTmpName "r" := by
  rintro ⟨k, hk⟩
  have hlen := congrArg String.length hk
  rw [TranslateDialectDirectArms.tmpName, String.length_append] at hlen
  have h1 : "r".length = 1 := rfl
  have h2 : "__sx".length = 4 := rfl
  omega

/-! ## `IsCoveredAdeq kC` -/

theorem kE_srcClean : srcClean kE :=
  ⟨not_isTmp_a, by norm_num [srcClean]⟩

/-- The hoisted no-overflow bound: given `u64` inputs, `a ^ 5` never overflows
    (bitwise ops preserve `u64`-range). -/
theorem kE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → kE.inRange σ :=
  fun σ h => ⟨h "a", by norm_num [SExpr.inRange]⟩

/-- The kernel is in the covered word-adequacy fragment. -/
theorem kC_adeq : IsCoveredAdeq kC :=
  .ofStraight
    (.rSeq (.rScalarSet "a" (by norm_num))
      (.rScalarSetExpr "r" kE kE_srcClean kE_inRange))

/-! ## The concrete `RustExec` reference run -/

/-- The entry state: every scalar `0` (the default `RustState`). -/
def rs0 : RustState := default

theorem scalarInRange_rs0 : ScalarInRange rs0 := by
  intro x; simp only [rs0]; positivity

/-- The mid state after `a := 3`. -/
def rs1 : RustState := rsSetScalar rs0 "a" 3

/-- The final state after `r := a ^ 5`. -/
def rs' : RustState := rsSetScalar rs1 "r" (kE.eval rs1.rsScalar)

/-- The concrete reference execution of `kC`. -/
theorem kC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec kC rs0 rs' :=
  .seq _ _ rs0 rs1 rs'
    (.scalarSet "a" 3 rs0)
    (.scalarSetExpr "r" kE rs1)

/-- The reference output: `r = 3 ^ 5 = 6`. -/
theorem rs'_output : rs'.rsScalar "r" = 6 := by
  simp only [rs', rsSetScalar, kE, SExpr.eval, rs1, rs0]
  decide

/-! ## The entry-seam discharge: `semScalar` output = `RustExec` output

Applying `rustExec_semScalar_agree` to `kC` with the entry env supplied by
`derivedEnv` (which satisfies `EnvRel` by `envRel_derivedEnv`): the source
machine-word semantics runs `kC` and leaves in `r` exactly the `ofNat 64` image
of the `RustExec` reference output. -/

/-- **Per-kernel value adequacy.** The `semScalar` machine-word run of `kC` from
    the `derivedEnv` entry env leaves in `r` the `ofNat 64` image of the
    `RustExec` reference output word `rs'.rsScalar "r" = 6`. The entry `EnvRel`
    seam is discharged by `envRel_derivedEnv`; `ScalarInRange` by
    `scalarInRange_rs0`. -/
theorem kC_semScalar_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    ∃ env', semScalar kC (derivedEnv rs0) = some env' ∧
      env' "r" = some ⟨.sword 64, BitVec.ofNat 64 (rs'.rsScalar "r")⟩ := by
  obtain ⟨env', hSem, hRel, _⟩ :=
    rustExec_semScalar_agree kC_adeq (kC_exec N leafSpec)
      (envRel_derivedEnv rs0) scalarInRange_rs0
  exact ⟨env', hSem, hRel "r" not_isTmp_r⟩

/-- The output word, concretely: `semScalar` leaves `ofNat 64 6` in `r`. -/
theorem kC_semScalar_output (N : Nat) (leafSpec : LeafSpec) :
    ∃ env', semScalar kC (derivedEnv rs0) = some env' ∧
      env' "r" = some ⟨.sword 64, BitVec.ofNat 64 6⟩ := by
  obtain ⟨env', hSem, hVal⟩ := kC_semScalar_eq_rustexec N leafSpec
  exact ⟨env', hSem, by rw [hVal, rs'_output]⟩

/-! ## §D — the full jasmin leg through the empty-entry-env route

The closed jasmin-bytes result the composed bridge could not deliver (its entry
trio is unsatisfiable, above) is obtained here for a minimal closed kernel
`dC := RScalarSet "r" 7` through `rustToJasminCom_endToEnd_topLevel_unconditional`.
Because `dC` is closed (its only write precedes any read — trivially, it has no
reads), `semScalar` succeeds from the EMPTY entry env, so no entry `EnvRel` is
needed: reads-follow-writes dissolves the seam. The verified pipeline's emitted
jasmin program denotes to the `ctTransTy` image of the `RustExec` reference
output word `rs''.rsScalar "r" = 7`. Axiom-free (all front/lowering facts by
`rfl`). This is the concrete `emitted-jasmin = RustExec-reference` capstone. -/

/-- The minimal closed kernel `r := 7`. -/
def dC : LowCT := .RScalarSet "r" 7

/-- Its `RustExec` reference post-state. -/
def rs'' : RustState := rsSetScalar rs0 "r" 7

theorem dC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec dC rs0 rs'' :=
  .scalarSet "r" 7 rs0

theorem rs''_output : rs''.rsScalar "r" = 7 := rfl

theorem dC_covered : IsCoveredSCtl dC :=
  .ofStraight (.rScalarSet "r" 7)

/-- The front-emitted dialect expression for `r := 7` (a `bvConst 7` node). -/
def dEConst : Expr catCryptDialect ([] : Ctx) (.sword 64) :=
  { op := .bvConst 64 (BitVec.ofNat 64 7), retTy_eq := rfl, args := .nil }

/-- The front output of translating `dC` from the empty varmap. -/
def dO : DTransOut ([] : Ctx) :=
  { Γ' := [.sword 64], cont := ComCont.varBind dEConst, vm := VarMap.empty.bind "r" }

/-- The tracked output slot for `r` (the freshly-bound `.here`). -/
def dW : CVar dO.Γ' (.sword 64) := CVar.here

/-- The complete dialect program returning the `r` slot. -/
def dCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  Com.var dEConst (Com.ret (toVIRVar dW))

theorem dHTrans : translateDialectControl VarMap.empty dC = some dO := rfl

theorem dHName : dO.vm.lookup "r" = some ⟨.sword 64, dW⟩ := rfl

theorem dHRet : dO.cont (Com.ret (toVIRVar dW)) = some dCom := rfl

/-- The entry semantics of `dC` from the empty env leaves `ofNat 64 7` in `r`. -/
def dEnv' : SEnvScalar :=
  SEnvScalar.upd (fun _ => none) "r" (t := .sword 64) (BitVec.ofNat 64 7)

theorem dHSem : semScalar dC (fun _ => none) = some dEnv' := rfl

theorem dHVal : dEnv' "r" = some ⟨.sword 64, BitVec.ofNat 64 7⟩ := rfl

theorem dHCom_isSome : (cryptoDialectToJasminCom dCom).isSome := rfl

/-- The emitted jasmin program. -/
noncomputable def dJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom dCom).get dHCom_isSome

theorem dHCom : cryptoDialectToJasminCom dCom = some dJcom :=
  (Option.some_get dHCom_isSome).symm

/-- **`emitted jasmin = RustExec reference output` (closed, axiom-free).** The
    verified pipeline's emitted jasmin program for `dC = (r := 7)` denotes to the
    `ctTransTy` image of the `RustExec` reference output word `rs''.rsScalar "r"`.
    The entry `EnvRel` seam is dissolved: a closed kernel's `semScalar` succeeds
    from the empty env, so `rustToJasminCom_endToEnd_topLevel_unconditional`
    applies with `consistentS_empty` and no entry-env reflection. -/
theorem dC_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec dO.Γ', RustStateInterp dO.vm rs'' Vb')
      ∧ dJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (rs''.rsScalar "r")) := by
  rw [rs''_output]
  exact rustToJasminCom_endToEnd_topLevel_unconditional dC dO N leafSpec rs0 rs''
    dEnv' "r" dW (BitVec.ofNat 64 7) dCom dJcom dC_covered dHTrans (dC_exec N leafSpec)
    dHSem dHName dHVal dHRet dHCom

/-! ## The P3-composition residual (why the jasmin leg cannot reuse this env)

`rustToJasminCom_endToEnd_rustexec_adeq` fuses the value leg above with the
jasmin denotation leg, and for that it needs `ConsistentS vm V env` for the
SAME entry `env` that satisfies `EnvRel rs env`. `ConsistentS` ties `env`'s
support to `vm`'s (`env s = none` wherever `vm.lookup s = none`), while `EnvRel`
binds every non-temp name. At the `VarMap.empty` entry the pipeline actually
starts from, `ConsistentS` forces `env` everywhere-`none`, directly
contradicting `EnvRel` on any non-temp name — the two are jointly
unsatisfiable, so the composed theorem's entry hypotheses cannot be discharged
at `VarMap.empty`. (For a non-empty finite `vm`, the same clash reappears
through `NoAliasVM`: `EnvRel` binds infinitely many non-temp names, which
`NoAliasVM` must inject into the finitely-many De Bruijn slots of a finite `Γ`.)
The genuine closed jasmin-leg result therefore takes the empty-entry-env route
(§D), where a closed kernel's reads-follow-writes make the empty env suffice. -/

/-- The entry-trio clash at the `VarMap.empty` pipeline entry: no env is both
    `EnvRel rs` (every non-temp name bound) and `ConsistentS VarMap.empty V`
    (every name `none`). Witnessed on the non-temp name `"r"`. -/
theorem entry_trio_unsat_empty
    (rs : RustState)
    (V : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)) (env : SEnvScalar)
    (hRel : EnvRel rs env) (hCons : ConsistentS VarMap.empty V env) : False := by
  have h1 : env "r" = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar "r")⟩ :=
    hRel "r" not_isTmp_r
  have h2 := hCons "r"
  rw [h1] at h2
  simp [VarMap.empty] at h2

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
