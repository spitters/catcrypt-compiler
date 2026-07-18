/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront

set_option autoImplicit false

/-!
# secp256k1 point-op value-tie, COMPOSITIONALLY over the field-op schedule

`Secp256k1PointOpFront` front-generates `jacDbl` / `jacAdd` as ~6000-node
`Com jasminDialect` values (`jacDblFrontCom` / `jacAddFrontCom`), built
COMPOSITIONALLY from a 19- / 23-entry field-op schedule:

```
  jacDblSchedule : List FOp            -- 19 field ops (.mul/.add/.sub o a b)
    →(mapIdx emitFOp)→ List LowCT      -- one 4-limb field brick per FOp
    →(translateDialectControl)→ Com catCryptDialect
    →(cryptoDialectToJasminCom)→ Com jasminDialect  (the flat ~6000-node Com)
```

The whole-op `Com.denote = spec` byte-KAT is MEASURED INFEASIBLE: a single
`denote` of the flattened Com peaks at >11 GB RSS on a 14 GB host (see
`Secp256k1PointOpFront.selfCheck`'s docstring — `Com.denote` is
superlinear-memory in the flattened Com size). This module ties the point op to
its independent `Nat` spec (`jacDblSpec` / `jacAddSpec`) at the **schedule
granularity** — WITHOUT ever denoting the flattened Com — by giving the schedule
an abstract meaning over `ℤ/pℤ` residues and proving it equals the spec.

## What is proved here (the substantive value half — step 2)

`scheduleEval` runs a `List FOp` over a string-keyed residue environment, each
`FOp` interpreted by the SAME field ops `fm`/`fa`/`fs` (`(·*·)%p` / `(·+·)%p` /
`(·+p-·)%p`) that the spec threads. The two theorems

* `jacDblSchedule_realizes_spec` :
    reading `Xp`/`Yp`/`Zp` from `scheduleEval jacDblSchedule (dblEnv0 X Y Z)`
    yields exactly `jacDblSpec X Y Z`;
* `jacAddSchedule_realizes_spec` :
    likewise `scheduleEval jacAddSchedule (addEnv0 …)` = `jacAddSpec …`,

establish that the compositional schedule the front consumes realises the
`dbl-2009-l` / `add-2007-bl` formulas over the base field. This is pure ℤ/pℤ
arithmetic over the 19- / 23-op fold — it fits in memory and needs no `Com`
evaluation. It upgrades `Secp256k1PointOpFront`'s structural gate
(`jacDblSchedule_counts` — op-kind counts only) to a full DATAFLOW-value tie:
each named cell carries exactly the spec's sub-expression.

The proof is run through an op-generic layer (`scheduleEvalG` / `jacDblSpecG` /
`jacAddSpecG`, abstracted over the three field ops `FM`/`FA`/`FS`) so the field
ops stay OPAQUE during the schedule/spec dataflow match. That keeps the tie a
shallow structural `rfl` on the residue-DAG: were `fm`/`fa`/`fs` left reducible,
the kernel would expand their `(· ⬝ ·) % pNat` body — with `pNat` a 78-digit
literal — at every one of the ~250 schedule nodes, blowing the reduction stack.
The concrete `fm`/`fa`/`fs` are then substituted by a single application
(`…_realizes_specG fm fa fs`), and `scheduleEval` / `jacDblSpec` / `jacAddSpec`
are definitionally these generic forms at `fm`/`fa`/`fs`.

## What is NOT proved here — the lift to `Com.denote`, and the one missing lemma

Lifting `scheduleEval … = spec` to `jacDblFrontCom.denote = jacDblSpec` at
schedule granularity (avoiding the monolith) would need a **scalar
front-preservation homomorphism** — a scalar analogue of the SIMD
`TranslateDialectVsimdDenote.translateDialectControlV_denote`, namely

```
theorem translateDialectControl_denote {c : LowCT} (hcov : IsCoveredCtl c) :
    ∀ {Γ} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm c = some o →
      semScalar c env = some env' →
      ∃ V', ConsistentS o.vm V' env' ∧
        ∀ {t} (tail), ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V'
```

whose `rSeq`/block case gives the per-concatenation homomorphism
`denote (front (a ++ b)) = denote (front b) ∘ denote (front a)` — exactly the
shape the SIMD proof's `rSeq` arm already discharges via
`ComCont.comp o₁.cont o₂.cont` (`TranslateDialectVsimdDenote.lean` lines 174-194).
This lemma **does not exist** for the scalar `translateDialectControl` path: the
SIMD path (`translateDialectControlV` / `semV` / `ConsistentV`, over 128-bit
`SEnv`) is the ONLY front with a front-general preservation theorem. There is no
scalar `semScalar : LowCT → SEnvScalar → Option SEnvScalar` operational semantics
and no scalar `ConsistentS` consistency relation for the `RScalarSetExpr` /
`RArrLoad` / `RArrStore` alphabet these bricks use; both must be built before the
`IsCoveredCtl` induction can even be stated.

Even WITH that homomorphism, the per-brick step — that `emitFOp i (.mul o a b)`'s
scalar semantics writes `fm (env a) (env b)` into `o`'s eight half-limbs — is
currently established only via `native_decide` KAT at 4-limb granularity
(`Secp256k1PointOpFront.secp256k1FeMulFront_denote` /
`secp256k1FeAddFront_denote` / `secp256k1FeSubFront_denote`); a symbolic
(all-inputs) proof that the 32-bit operand-scanning multiply-plus-Solinas-fold
brick computes `(a·b) mod p` is a separate, deep field-arithmetic obligation that
`native_decide` sidesteps.

The homomorphism is therefore DEEP (needs new scalar-semantics infrastructure
PLUS symbolic per-brick field correctness), so this module STOPS at the
schedule-level value tie and records the missing lemma above rather than stubbing
it.

**0 sorries.**
-/

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional

open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp jacDblSchedule jacAddSchedule jacDblSpec jacAddSpec fm fa fs)

/-! ## 1. The schedule's abstract meaning over `ℤ/pℤ` residues

The interpreter is defined op-generically (over three field ops `FM`/`FA`/`FS`)
so the ops stay opaque through the dataflow proof; `scheduleEval` is the concrete
instance at the point-op field ops `fm`/`fa`/`fs`. -/

/-- Functional string-keyed residue environment update. -/
def envUpd (env : String → Nat) (k : String) (v : Nat) : String → Nat :=
  fun n => if n = k then v else env n

/-- Run one field-op call under generic field ops: read the two named input
    residues, apply the matching op, write the result into the output name. -/
def stepFOpG (FM FA FS : Nat → Nat → Nat) (env : String → Nat) : FOp → (String → Nat)
  | .mul o a b => envUpd env o (FM (env a) (env b))
  | .add o a b => envUpd env o (FA (env a) (env b))
  | .sub o a b => envUpd env o (FS (env a) (env b))

/-- Abstract meaning of a whole schedule under generic field ops: fold `stepFOpG`
    over the op list, so each named cell ends holding the field value the front's
    matching brick computes. NO `Com` evaluation — pure ℤ/pℤ arithmetic. -/
def scheduleEvalG (FM FA FS : Nat → Nat → Nat) (ops : List FOp) (env : String → Nat) :
    String → Nat :=
  ops.foldl (stepFOpG FM FA FS) env

/-- The point-op schedule interpreter at the base-field ops `fm`/`fa`/`fs`
    (`(·*·)%p` / `(·+·)%p` / `(·+p-·)%p`) — exactly the residue specs the point-op
    spec threads. -/
def scheduleEval (ops : List FOp) (env : String → Nat) : String → Nat :=
  scheduleEvalG fm fa fs ops env

/-! ## 2. Initial environments (input coordinates bound to their cell names) -/

/-- `jacDbl` input env: bind `X`, `Y`, `Z`; everything else `0`. -/
def dblEnv0 (X Y Z : Nat) : String → Nat :=
  fun n => if n = "X" then X else if n = "Y" then Y else if n = "Z" then Z else 0

/-- `jacAdd` input env: bind `X1,Y1,Z1,X2,Y2,Z2`; everything else `0`. -/
def addEnv0 (X1 Y1 Z1 X2 Y2 Z2 : Nat) : String → Nat :=
  fun n =>
    if n = "X1" then X1 else if n = "Y1" then Y1 else if n = "Z1" then Z1
    else if n = "X2" then X2 else if n = "Y2" then Y2 else if n = "Z2" then Z2
    else 0

/-! ## 3. Op-generic point-op specs (mirror `jacDblSpec` / `jacAddSpec` verbatim)

`jacDblSpecG FM FA FS = jacDblSpec` and `jacAddSpecG FM FA FS = jacAddSpec` at
`FM,FA,FS := fm,fa,fs` DEFINITIONALLY (the bodies are the same `let`-chains). -/

/-- Op-generic `dbl-2009-l` spec — `Secp256k1PointOpFront.jacDblSpec` verbatim with
    the field ops abstracted. -/
def jacDblSpecG (FM FA FS : Nat → Nat → Nat) (X Y Z : Nat) : Nat × Nat × Nat :=
  let YY := FM Y Y
  let XYY := FM X YY
  let S := FA (FA XYY XYY) (FA XYY XYY)
  let M := FA (FA (FM X X) (FM X X)) (FM X X)
  let Msq := FM M M
  let Xp := FS Msq (FA S S)
  let SmXp := FS S Xp
  let MSmXp := FM M SmXp
  let YYsq := FM YY YY
  let Y8 := FA (FA (FA YYsq YYsq) (FA YYsq YYsq)) (FA (FA YYsq YYsq) (FA YYsq YYsq))
  let Yp := FS MSmXp Y8
  let Zp := FA (FM Y Z) (FM Y Z)
  (Xp, Yp, Zp)

/-- Op-generic `add-2007-bl` spec — `Secp256k1PointOpFront.jacAddSpec` verbatim with
    the field ops abstracted. -/
def jacAddSpecG (FM FA FS : Nat → Nat → Nat) (X1 Y1 Z1 X2 Y2 Z2 : Nat) : Nat × Nat × Nat :=
  let Z1sq := FM Z1 Z1
  let Z2sq := FM Z2 Z2
  let Z1cu := FM Z1sq Z1
  let Z2cu := FM Z2sq Z2
  let U1 := FM X1 Z2sq
  let U2 := FM X2 Z1sq
  let S1 := FM Y1 Z2cu
  let S2 := FM Y2 Z1cu
  let H := FS U2 U1
  let r := FS S2 S1
  let Hsq := FM H H
  let Hcu := FM Hsq H
  let U1Hsq := FM U1 Hsq
  let Rsq := FM r r
  let Xp := FS (FS Rsq Hcu) (FA U1Hsq U1Hsq)
  let Yp := FS (FM r (FS U1Hsq Xp)) (FM S1 Hcu)
  let Zp := FM (FM Z1 Z2) H
  (Xp, Yp, Zp)

/-! ## 4. The schedule realises the independent `Nat` spec

Op-generic realization (`FM`/`FA`/`FS` opaque ⇒ shallow structural collapse),
then the concrete tie by substituting `fm`/`fa`/`fs`. -/

/-- Op-generic `jacDbl` realization: reading `Xp`/`Yp`/`Zp` from the doubling
    schedule under any field ops yields `jacDblSpecG`. -/
theorem jacDblSchedule_realizes_specG (FM FA FS : Nat → Nat → Nat) (X Y Z : Nat) :
    (scheduleEvalG FM FA FS jacDblSchedule (dblEnv0 X Y Z) "Xp",
     scheduleEvalG FM FA FS jacDblSchedule (dblEnv0 X Y Z) "Yp",
     scheduleEvalG FM FA FS jacDblSchedule (dblEnv0 X Y Z) "Zp")
      = jacDblSpecG FM FA FS X Y Z := by
  simp only [scheduleEvalG, jacDblSchedule, stepFOpG, dblEnv0, envUpd, jacDblSpecG,
    List.foldl_cons, List.foldl_nil, String.reduceEq, if_true, if_false]

/-- Op-generic `jacAdd` realization. -/
theorem jacAddSchedule_realizes_specG (FM FA FS : Nat → Nat → Nat)
    (X1 Y1 Z1 X2 Y2 Z2 : Nat) :
    (scheduleEvalG FM FA FS jacAddSchedule (addEnv0 X1 Y1 Z1 X2 Y2 Z2) "Xp",
     scheduleEvalG FM FA FS jacAddSchedule (addEnv0 X1 Y1 Z1 X2 Y2 Z2) "Yp",
     scheduleEvalG FM FA FS jacAddSchedule (addEnv0 X1 Y1 Z1 X2 Y2 Z2) "Zp")
      = jacAddSpecG FM FA FS X1 Y1 Z1 X2 Y2 Z2 := by
  simp only [scheduleEvalG, jacAddSchedule, stepFOpG, addEnv0, envUpd, jacAddSpecG,
    List.foldl_cons, List.foldl_nil, String.reduceEq, if_true, if_false]

/-- **`jacDblSchedule` realises `jacDblSpec` over `ℤ/pℤ`.** Running the 19-op
    doubling schedule with each `FOp` interpreted as its base-field-op residue
    spec, then reading the output cells `Xp`/`Yp`/`Zp`, yields exactly
    `jacDblSpec X Y Z`. Pure ℤ/pℤ arithmetic — no flattened-`Com` evaluation. -/
theorem jacDblSchedule_realizes_spec (X Y Z : Nat) :
    (scheduleEval jacDblSchedule (dblEnv0 X Y Z) "Xp",
     scheduleEval jacDblSchedule (dblEnv0 X Y Z) "Yp",
     scheduleEval jacDblSchedule (dblEnv0 X Y Z) "Zp")
      = jacDblSpec X Y Z :=
  jacDblSchedule_realizes_specG fm fa fs X Y Z

/-- **`jacAddSchedule` realises `jacAddSpec` over `ℤ/pℤ`.** Running the 23-op
    add schedule with each `FOp` interpreted as its base-field-op residue spec,
    then reading `Xp`/`Yp`/`Zp`, yields exactly `jacAddSpec …`. -/
theorem jacAddSchedule_realizes_spec (X1 Y1 Z1 X2 Y2 Z2 : Nat) :
    (scheduleEval jacAddSchedule (addEnv0 X1 Y1 Z1 X2 Y2 Z2) "Xp",
     scheduleEval jacAddSchedule (addEnv0 X1 Y1 Z1 X2 Y2 Z2) "Yp",
     scheduleEval jacAddSchedule (addEnv0 X1 Y1 Z1 X2 Y2 Z2) "Zp")
      = jacAddSpec X1 Y1 Z1 X2 Y2 Z2 :=
  jacAddSchedule_realizes_specG fm fa fs X1 Y1 Z1 X2 Y2 Z2

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional
