/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-!
# End-to-end front transport for data-dependent `while` (`RWhileNz`)

`CompilerCorrectnessExtracted.rustToJasminCom_endToEnd_unconditional` closes the
LowCT → `Com catCryptDialect` → `Com jasmin` value story over the *straight-line +
`RFor` + `RIfNz`-φ* sublanguage `IsCoveredSCtl`, whose control-covered front is
`translateDialectControl` and whose value waist is `semScalar`. That fragment does
**not** contain a data-dependent `while`: `IsCoveredSCtl` excludes `RWhileNz`, and
the value waist `semScalar` has no runtime-loop arm. (`IsCoveredCtl` — the
operational-simulation coverage — does have an `rWhileNz` arm, matching
`translateDialectControl`'s context-plumbing `RWhileNz` arm.)

The **front-preservation** of the `while`-carrying front is
`TranslateDialectScalar.transU_denote`
(`Dialects/TranslateDialectUnifiedDenote.lean`), the homomorphism for the unified
coverage predicate `IsCoveredSU` (closed under `RSeq`/`RBlock`/`RCond`/`RWhileNz`/
`RFor`, all shapes nesting all shapes) over the unified waist `semU` and the
env-threaded front descent `transU`. But that homomorphism stops at the
`catCryptDialect` `Com`.

This module composes it with
`DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'` (A1) down to a jasmin
`Com`. `transU_denote` exposes the
*same* output triple as `translateDialectControl_denote_ctl`
(a post-valuation `V'` with `ConsistentS o.vm V' env'` and, for any tracked tail,
a `com` with `o.cont tail = some com ∧ com.denote V = tail.denote V'`), so the
proof of `transU_to_jasminCom_endToEnd` below is the exact analogue of
`semScalarToJasminCom_denote_eq`, with only the front leg swapped
(`translateDialectControl_denote_ctl → transU_denote`, `translateDialectControl →
transU fuel`, `semScalar → semU fuel`, `IsCoveredSCtl → IsCoveredSU`).

## What is (and is not) delivered

* **Delivered — the value transport, `while` included.** For an `IsCoveredSU`-covered
  `c` (so `RWhileNz` is allowed, and nested `while`/`cond`/`for` with it), if the
  unified front `transU fuel` and the A1 lowering both succeed and the unified waist
  `semU fuel` runs `c` to `env'` leaving `val` in the tracked output `name`, the
  emitted jasmin program computes `val`:
  `jcom.denote (ctMapValD V) = ctTransTy val`. This composes `transU_denote`
  (front homomorphism, with `while`) with `cryptoDialectToJasminCom_denote_eq'` (A1,
  leaf agreement discharged internally by `dialectJasminLeafAgrees_holds`). All
  goals closed; no new axiom.

* **Value semantics — `semU`, as in the straight-line case.** The value leg is
  stated over `semU fuel` (the machine-word-faithful unified waist: `semScalar`
  on leaves, `bind` on `RSeq`, `semScalarCond` on the guarded conditional, and the
  fuel-bounded `semScalarWhile` on the runtime loop), for the same reason
  `semScalarToJasminCom_denote_eq` uses `semScalar` and not a `leafSpec`-oracle
  `RustExec` value — see `CompilerCorrectnessExtracted` §2c (opaque leaves ↦
  `CryptoTy.default`; wrapping-`u64` `SExpr.evalBV`). `semU` is the honest, provable
  value model for the compiled code, and it is the strongest a front-general
  theorem can state.

## The operational (`RustExec`) leg

`rustToJasminCom_endToEnd_unconditional` also carries a *byte-level* conjunct
`∃ Vb', RustStateInterp o.vm rs' Vb'` via
`CryptoDialectRustSim.rustExecSimulatesDialect`. That simulation is stated for the
control-covered front only: it requires `IsCoveredCtl c` and
`translateDialectControl vm c = some o`; `IsCoveredSU` has no `toIsCoveredCtl`
and `transU` is not `translateDialectControl`.

Bare existence of a post-state interpretation is in any case no constraint on the
execution. `RustStateInterp vm rs V` pins `V` to `rs` on the bound names, so
`RustStateSubstrate.noAlias_canonical_witness` realises it at an arbitrary
post-state under `NoAliasVM vm`; a conclusion of that shape alone holds whether or
not `rs'` is the state the program reaches. The operational obligation therefore
also pins the post-state valuation to the *source* semantics `semU`:

> **`RustExec ↔ semU` operational bridge for the unified front.** For
> `transU fuel vm env c = some o`, `RustExec N leafSpec c rs rs'`,
> `semU fuel c env = some env'`, and an entry `RustStateInterp vm rs Vb` together
> with the entry value reflection `EnvBoundOn rs env B`, produce `Vb' : HVec o.Γ'`
> with `RustStateInterp o.vm rs' Vb'` **and** `env' name = some ⟨.sword 64,
> w.lookup Vb'⟩` at every tracked non-temp write `name ↦ w` — the post-state
> valuation reads back the value the source semantics predicts.

`RustExecSimulatesUnified_Statement` below is that obligation verbatim, over the
coverage `IsCoveredAdeqU` (§ "The unified word-adequacy fragment"), and
`RustExecSimulatesUnified.rustExecSimulatesUnified_statement_holds` discharges it.
Pairing it with `transU_to_jasminCom_endToEnd` gives the two-conjunct shape of
`rustToJasminCom_endToEnd_unconditional` on that fragment.

`IsCoveredAdeqU` has no `RWhileNz` arm: `RustExec` tests the `while` guard before
the body while `semU`'s `semScalarWhile` waist is a do-while, and the two disagree
at a zero entry guard. `RustExecSimulatesUnified.RWhileNzUnifiedAgreement_Statement`
records that edge.

**All goals closed; no axioms beyond the front's existing set.**
-/

@[expose] public section

set_option autoImplicit true -- SSA IR front: many context/type variables

namespace CatCrypt.Crypto.SecureCompilation.VIR.RustToJasminComWhile

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Core

/-! ## The composition: unified front (with `while`) fused through A1 -/

/-- **End-to-end front value-transport for the `while`-carrying sublanguage
    (`IsCoveredSU`), adequacy discharged.**

    The `IsCoveredSU` analogue of
    `CompilerCorrectnessExtracted.semScalarToJasminCom_denote_eq`: identical
    conclusion and proof, with the front leg swapped from the straight-line
    `translateDialectControl_denote_ctl` (over `translateDialectControl`/`semScalar`)
    to the unified `transU_denote` (over `transU fuel`/`semU fuel`), whose coverage
    `IsCoveredSU` **includes data-dependent `RWhileNz`** (and nested
    `while`/`cond`/`for`).

    Given the unified front descent `transU fuel` and the A1 lowering both succeed,
    the entry valuation is consistent with the entry environment, and the unified
    waist `semU fuel` runs `c` to `env'` leaving `val` in the tracked output `name`
    (which the front's post-varmap resolves to the slot `w`), the emitted jasmin
    program computes `val`: `jcom.denote (ctMapValD V) = ctTransTy val`.

    Composes:
    * `TranslateDialectScalar.transU_denote` — the `while`-carrying front
      homomorphism (`transU`-emitted `Com`-prefix denotes the `semU` waist),
      supplying the post-valuation `V'` consistent with `env'` and the tracked-tail
      denotation agreement;
    * `ConsistentS.lookup_eq` — reads `val` out of the return slot;
    * `DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'` — A1, transports
      along the jasmin lowering (leaf agreement discharged by
      `dialectJasminLeafAgrees_holds`).

    Value semantics is `semU fuel` (see the module header for why, not a
    `leafSpec`-oracle `RustExec` value); the byte-level `RustExec` existence conjunct
    is the one named residual (module header + `RustExecSimulatesUnified_Statement`). -/
theorem transU_to_jasminCom_endToEnd
    {Γ : Ctx} {t : CryptoTy}
    (fuel : Nat)
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (name : String) (w : CVar o.Γ' t) (val : ⟦t⟧)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hCov : IsCoveredSU c)
    (hTrans : transU fuel vm env c = some o)
    (hCons : ConsistentS vm V env)
    (hSem : semU fuel c env = some env')
    (hName : o.vm.lookup name = some ⟨t, w⟩)
    (hVal : env' name = some ⟨t, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = ctTransTy val := by
  obtain ⟨V', hc', hcont⟩ :=
    transU_denote fuel hCov vm V env env' o hCons hTrans hSem
  obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar w))
  rw [hRet] at hcom'
  obtain rfl := Option.some.inj hcom'
  rw [cryptoDialectToJasminCom_denote_eq' com V jcom hCom, hden]
  exact congrArg ctTransTy (hc'.lookup_eq hName hVal)

/-- **Top-level specialisation** (`Γ = []`, `vm = VarMap.empty`,
    `V = HVec.nil`/`.nil`).  Entry consistency is discharged internally by
    `consistentS_empty`, mirroring
    `rustToJasminCom_endToEnd_topLevel_unconditional` for the `while`-carrying
    front.  The caller supplies only the coverage, the two front/lowering successes
    (`hTrans`, `hSem`, `hRet`, `hCom`), and the output tracking (`hName`, `hVal`). -/
theorem transU_to_jasminCom_endToEnd_topLevel
    {t : CryptoTy}
    (fuel : Nat)
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (env' : SEnvScalar) (name : String) (w : CVar o.Γ' t) (val : ⟦t⟧)
    (com : Com catCryptDialect ([] : Ctx) t)
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy t))
    (hCov : IsCoveredSU c)
    (hTrans : transU fuel VarMap.empty (fun _ => none) c = some o)
    (hSem : semU fuel c (fun _ => none) = some env')
    (hName : o.vm.lookup name = some ⟨t, w⟩)
    (hVal : env' name = some ⟨t, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote
        (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
      = ctTransTy val :=
  transU_to_jasminCom_endToEnd fuel VarMap.empty c o
    (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx))
    (fun _ => none) env' name w val com jcom
    hCov hTrans consistentS_empty hSem hName hVal hRet hCom

/-! ## The unified word-adequacy fragment

`RustExecSemScalarBridge.IsCoveredAdeq` is the straight-line-plus-`RFor`-plus-φ-`RIfNz`
word fragment on which the `RustExec` `Nat`-model run and the `semScalar`
`BitVec`-model run agree (`rustExec_semScalar_agree_scoped`). `IsCoveredAdeqU`
closes it under the unified combinators `semU`/`transU` special-case: `RSeq`,
`RBlock`, the guarded conditional `RIfNz name thenBlk RSkip`, and the counted
`RFor` whose body is again any `IsCoveredAdeqU` shape. It is the `IsCoveredSU`
sub-fragment on which the operational bridge below holds. -/

/-- The unified word-adequacy coverage: an `IsCoveredAdeq` leaf under the four
    unified combinators.

    * `ofAdeq` — a `notSeqLike` `IsCoveredAdeq` node, so `semU`/`transU` route it
      to the `semScalar`/`translateDialectControl` leaf fallback;
    * `rSeq`, `rBlock` — the sequencing closures;
    * `rCond` — the guarded do-once conditional, over a non-temp guard name whose
      word the entry reflection resolves;
    * `rFor` — the counted loop at a trip count within `u64` range, over any
      `IsCoveredAdeqU` body.

    There is no `RWhileNz` arm; see `RustExecSimulatesUnified`. -/
inductive IsCoveredAdeqU : LowCT → Prop
  | ofAdeq {c : LowCT} : IsCoveredAdeq c → isSeqLike c = false → IsCoveredAdeqU c
  | rSeq {c₁ c₂ : LowCT} :
      IsCoveredAdeqU c₁ → IsCoveredAdeqU c₂ → IsCoveredAdeqU (.RSeq c₁ c₂)
  | rBlock {body : LowCT} : IsCoveredAdeqU body → IsCoveredAdeqU (.RBlock body)
  | rCond {name : String} {thenBlk : LowCT} (hname : ¬ isTmpName name) :
      IsCoveredAdeqU thenBlk → IsCoveredAdeqU (.RIfNz name thenBlk .RSkip)
  | rFor {x : String} {N : Nat} {body : LowCT} (hN : N ≤ 2 ^ 64) :
      IsCoveredAdeqU body → IsCoveredAdeqU (.RFor x N body)

/-- Reads-follow-writes scoping for the unified fragment. `readsOK`'s `RIfNz` arm
    asks only that the guard name be bound, which suffices for the φ-merge
    conditional whose two branches are constant writes; the unified combinators put
    an arbitrary block under the guard and under the runtime loop, so those two
    arms scope their blocks as well. -/
def readsOKU (B : String → Prop) : LowCT → Prop
  | .RBlock b => readsOKU B b
  | .RSeq c₁ c₂ => readsOKU B c₁ ∧ readsOKU (afterB B c₁) c₂
  | .RLetU64Zero n b => readsOKU (fun y => B y ∨ y = n) b
  | .RScalarSetExpr _ e => varsBoundIn B e
  | .RFor x _ b => readsOKU (fun y => B y ∨ y = x) b
  | .RIfNz name t e => B name ∧ readsOKU B t ∧ readsOKU B e
  | .RWhileNz name b => B name ∧ readsOKU B b
  | _ => True

/-- The unified scoping refines the straight-line one, arm by arm. -/
theorem readsOKU.toReadsOK :
    ∀ (c : LowCT) (B : String → Prop), readsOKU B c → readsOK B c := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => exact fun B h => ⟨ih₁ B h.1, ih₂ _ h.2⟩
  | RBlock b ih => exact fun B h => ih B h
  | RLetU64Zero n b ih => exact fun B h => ih _ h
  | RScalarSetExpr _ e => exact fun _ h => h
  | RFor x _ b ih => exact fun B h => ih _ h
  | RIfNz name t e _ _ => exact fun _ h => h.1
  | _ => exact fun _ _ => trivial

/-- `IsCoveredAdeqU` is a sub-fragment of the unified coverage `IsCoveredSU`, so
    every `IsCoveredSU` consumer — the front homomorphism `transU_denote`, the
    end-to-end `transU_to_jasminCom_endToEnd`, the `NoAliasVM` preservation
    `transU_preserves_noAlias` — applies to it. -/
theorem IsCoveredAdeqU.toIsCoveredSU {c : LowCT} (h : IsCoveredAdeqU c) :
    IsCoveredSU c := by
  induction h with
  | ofAdeq hAdeq hns => exact .ofCtl hAdeq.toIsCoveredSCtl hns
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rBlock _ ih => exact .rBlock ih
  | rCond _ _ ih => exact .rCond ih
  | rFor _ _ ih => exact .rFor ih

-- The coverage is inhabited: a scalar write, then a counted loop of scalar writes.
example (name : String) :
    IsCoveredAdeqU (.RSeq (.RScalarSet name 1) (.RFor "i" 4 (.RScalarSet name 2))) :=
  .rSeq (.ofAdeq (.ofStraight (.rScalarSet name (by norm_num))) rfl)
    (.rFor (by norm_num) (.ofAdeq (.ofStraight (.rScalarSet name (by norm_num))) rfl))

/-! ## The operational bridge, as a statement

The obligation stated verbatim, in the shape the module header describes:
a post-state byte-layout witness that also reads back the values the source
semantics `semU` predicts. `RustExecSimulatesUnified.rustExecSimulatesUnified`
proves it and `rustExecSimulatesUnified_statement_holds` discharges this `Prop`. -/

/-- The operational bridge for the unified front, as a statement. For a covered
    `c` translated by `transU fuel` to `o`, a `RustExec` run `rs ↦ rs'`, a `semU`
    run `env ↦ env'`, an entry byte-layout witness `Vb` and an entry value
    reflection `EnvBoundOn rs env B` over a reads-follow-writes scoping, there is a
    post-state witness `Vb'` that satisfies the byte-layout invariant at `rs'` and
    whose value at every tracked non-temp write of `c` is the one `env'` carries.

    The second conjunct is what ties the conclusion to the execution: without it
    `noAlias_canonical_witness` realises the first conjunct at any post-state
    whatsoever. -/
def RustExecSimulatesUnified_Statement : Prop :=
  ∀ (fuel : Nat) {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState) (env env' : SEnvScalar)
    (B : String → Prop),
    IsCoveredAdeqU c →
    transU fuel vm env c = some o →
    RustExec N leafSpec c rs rs' →
    semU fuel c env = some env' →
    EnvBoundOn rs env B → ScalarInRange rs → readsOKU B c →
    ∀ Vb : HVec Γ, RustStateInterp vm rs Vb →
    ∃ Vb' : HVec o.Γ',
      RustStateInterp o.vm rs' Vb' ∧
      ∀ (name : String) (w : CVar o.Γ' (.sword 64)),
        afterB B c name → ¬ isTmpName name →
        o.vm.lookup name = some ⟨.sword 64, w⟩ →
        env' name = some ⟨.sword 64, w.lookup Vb'⟩

end CatCrypt.Crypto.SecureCompilation.VIR.RustToJasminComWhile
