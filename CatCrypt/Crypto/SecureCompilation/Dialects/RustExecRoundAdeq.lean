/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed-kernel route reduces the front (`translateDialectControl`,
-- `semScalar`, `cryptoDialectToJasminCom`) by `rfl`/`decide`; under the module
-- system that reduction needs the front closure imported with `all`, and
-- `Nat.repr` (the front's slot names) exposed through `Init.Data.Repr`.
import all Init.Data.Repr
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCT
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq

/-!
# A real covered round through the closed-kernel `emitted = RustExec` route

`RustExecKernelAdeq.dC_emitted_eq_rustexec` proved, for the minimal closed kernel
`r := 7`, that the emitted jasmin program denotes to the `ctTransTy` image of the
`RustExec` reference output — axiom-free, through the SATISFIABLE
`rustToJasminCom_endToEnd_topLevel_unconditional` route (a closed kernel's reads
follow its writes, so `semScalar` succeeds from the empty entry env with no entry
`EnvRel` needed). This module applies that pattern to a REAL round function.

## The round: the SHA-256/512 `Maj` nonlinear round function

Each SHA-2 compression round applies the bitwise majority function

```
Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)
```

as the `T2` half of its round update. It is **purely bitwise** (`∧`, `⊕`), so
its covered-fragment `inRange` obligation holds for ALL `u64` inputs with **no**
side condition — `SXor`/`SAnd` carry only their operand conditions. The
nonlinear layer is therefore the largest SHA-2 fragment expressible in the
covered word alphabet: see §"Residual".

The kernel writes the three inputs as literals (the SHA-256 IV words `a,b,c`),
then computes `maj`. It is closed, so `semScalar` runs it from the empty entry
env.

The companion `Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)` (with `¬x = x ⊕ 0xFFFF…F`) is
covered identically — same `∧`/`⊕` alphabet, same all-`u64` hoisted `inRange` —
and composes into the same closed-kernel route unchanged (§"Generalization").

## Residual — why the ARX layer (`Σ`, `σ`, the additions) is NOT covered

The SHA-2 `Σ`/`σ` functions use **rotations** `ror(x,k) = (x ≫ k) ⊕ (x ≪ (w−k))`
and the round core uses **modular additions**. Both hit an input-dependent
`SExpr.inRange` overflow condition that the hoisted
`∀ σ, (∀y, σ y < 2^64) → e.inRange σ` cannot discharge:

* `SShl a b`  (`inRange` = `… ∧ a.eval σ ≪ b.eval σ < 2^64`) — a left shift of a
  full-range `u64` overflows the `Nat` model, so the left-shift half of every
  rotation fails the hoisted bound. (`SShr` by a literal `< 64` is fine.)
* `SAdd a b`  (`inRange` = `… ∧ a.eval σ + b.eval σ < 2^64`) — two near-`2^64`
  addends overflow, so the round's `T1 = h + Σ1(e) + Ch + K + W` additions fail
  the hoisted bound.

So the covered round is precisely the `∧`/`⊕`/`¬` layer; the `Σ`/`σ`/`+` layer
needs a per-kernel input bound (the `#250` `inRange` reconciliation), out of
scope for the input-agnostic hoisted arm.

## Generalization to the whole compression

`Maj` here is one closed straight-line kernel; the closed-kernel route scales to
the whole compression along three orthogonal axes, all mechanical given the
per-arm coverage:

* **More bitwise functions** — `Ch` is the same `∧`/`⊕`/`¬` alphabet, so
  appending its `RScalarSet` inputs and one `RScalarSetExpr` to `roundC`, adding
  its `IsCoveredAdeqS.rScalarSetExpr` arm (a `srcClean` + all-`u64` hoisted
  `inRange`, exactly as `majE_srcClean`/`majE_inRange`), and tracking its output
  slot reuses this file's `.get`/`rfl` scaffold verbatim.
* **The message schedule** — the `W[t]` recurrence's `⊕`/`≫` (logical
  right-shift by a literal `< 64`) parts are covered; its `≪`-rotations and `+`
  accumulations are the §"Residual" arms and need the per-kernel input bound.
* **Round iteration** — 64 rounds is an `RFor` (`IsCoveredAdeq.rFor`, `N ≤ 2^64`)
  over the round body, tracked by the loop bridge `agreeFor`; the closed-kernel
  empty-entry-env argument is unchanged because the unrolled body stays closed.

The remaining wall is the `Σ`/`σ`/`+` ARX layer (§"Residual"): closing it needs
the per-kernel `SExpr.inRange` reconciliation (a concrete input bound feeding
`SExpr.evalBV_eq_ofNat_eval`), not the input-agnostic hoisted arm used here.
-/

@[expose] public section

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

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq

/-! ## The SHA-2 nonlinear round expressions -/

/-- `Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)`. -/
def majE : SExpr :=
  .SXor (.SXor (.SAnd (.SVar "a") (.SVar "b")) (.SAnd (.SVar "a") (.SVar "c")))
    (.SAnd (.SVar "b") (.SVar "c"))

/-! ## The closed kernel -/

/-- The closed round kernel: write the three inputs as literals (SHA-256 IV
    words `a,b,c`), then compute `maj`. -/
def roundC : LowCT :=
  .RSeq (.RScalarSet "a" 1779033703)
    (.RSeq (.RScalarSet "b" 3144134277)
      (.RSeq (.RScalarSet "c" 1013904242)
        (.RScalarSetExpr "maj" majE)))

/-! ## Coverage: `IsCoveredAdeq roundC` -/

/-- Any string shorter than the 4-char `__sx` temp prefix is not a fresh temp. -/
theorem not_isTmp_short (s : String) (hs : s.length < 4) : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  have hlen := congrArg String.length hk
  rw [TranslateDialectDirectArms.tmpName, String.length_append] at hlen
  have h2 : "__sx".length = 4 := rfl
  omega

theorem majE_srcClean : srcClean majE :=
  ⟨⟨⟨not_isTmp_short "a" (by decide), not_isTmp_short "b" (by decide)⟩,
      ⟨not_isTmp_short "a" (by decide), not_isTmp_short "c" (by decide)⟩⟩,
    ⟨not_isTmp_short "b" (by decide), not_isTmp_short "c" (by decide)⟩⟩

theorem majE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → majE.inRange σ :=
  fun _σ h => ⟨⟨⟨h "a", h "b"⟩, ⟨h "a", h "c"⟩⟩, ⟨h "b", h "c"⟩⟩

theorem roundC_adeqS : IsCoveredAdeqS roundC :=
  .rSeq (.rScalarSet "a" (by norm_num))
    (.rSeq (.rScalarSet "b" (by norm_num))
      (.rSeq (.rScalarSet "c" (by norm_num))
        (.rScalarSetExpr "maj" majE majE_srcClean majE_inRange)))

theorem roundC_adeq : IsCoveredAdeq roundC := .ofStraight roundC_adeqS

theorem roundC_covered : IsCoveredSCtl roundC := roundC_adeq.toIsCoveredSCtl

/-! ## The `RustExec` reference run -/

def rs0 : RustState := default

def rs1 : RustState := rsSetScalar rs0 "a" 1779033703
def rs2 : RustState := rsSetScalar rs1 "b" 3144134277
def rs3 : RustState := rsSetScalar rs2 "c" 1013904242
def rsF : RustState := rsSetScalar rs3 "maj" (majE.eval rs3.rsScalar)

theorem roundC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec roundC rs0 rsF :=
  .seq _ _ rs0 rs1 rsF (.scalarSet "a" 1779033703 rs0)
    (.seq _ _ rs1 rs2 rsF (.scalarSet "b" 3144134277 rs1)
      (.seq _ _ rs2 rs3 rsF (.scalarSet "c" 1013904242 rs2)
        (.scalarSetExpr "maj" majE rs3)))

/-! ## Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem roundTransSome : (translateDialectControl VarMap.empty roundC).isSome := by rfl

noncomputable def roundO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty roundC).get roundTransSome

theorem roundHTrans : translateDialectControl VarMap.empty roundC = some roundO :=
  (Option.some_get roundTransSome).symm

theorem roundSemSome : (semScalar roundC (fun _ => none)).isSome := by rfl

noncomputable def roundEnv : SEnvScalar := (semScalar roundC (fun _ => none)).get roundSemSome

theorem roundHSem : semScalar roundC (fun _ => none) = some roundEnv :=
  (Option.some_get roundSemSome).symm

theorem roundNameSome : (roundO.vm.lookup "maj").isSome := by rfl

/-- The tracked slot's type is the 64-bit word: decided, since the slot name
    goes through `Nat.repr`, which the elaborator's definitional check does not
    reduce. -/
theorem roundNameTy : ((roundO.vm.lookup "maj").get roundNameSome).1 = .sword 64 := by
  decide

/-- The tracked output slot for `maj`. -/
noncomputable def roundW : CVar roundO.Γ' (.sword 64) :=
  cast (congrArg (CVar roundO.Γ') roundNameTy) ((roundO.vm.lookup "maj").get roundNameSome).2

theorem roundHName : roundO.vm.lookup "maj" = some ⟨.sword 64, roundW⟩ := by decide

theorem roundValSome : (roundEnv "maj").isSome := by rfl

theorem roundValTy : ((roundEnv "maj").get roundValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `maj`. -/
noncomputable def roundVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote roundValTy) ((roundEnv "maj").get roundValSome).2

theorem roundHVal : roundEnv "maj" = some ⟨.sword 64, roundVal⟩ := by
  rw [← Option.some_get roundValSome]
  exact congrArg some (Sigma.ext roundValTy
    (by unfold roundVal
        exact (cast_heq (congrArg CryptoTy.denote roundValTy)
          ((roundEnv "maj").get roundValSome).2).symm))

theorem roundRetSome : (roundO.cont (Com.ret (toVIRVar roundW))).isSome := by rfl

noncomputable def roundCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (roundO.cont (Com.ret (toVIRVar roundW))).get roundRetSome

theorem roundHRet : roundO.cont (Com.ret (toVIRVar roundW)) = some roundCom :=
  (Option.some_get roundRetSome).symm

theorem roundComSome : (cryptoDialectToJasminCom roundCom).isSome := by rfl

noncomputable def roundJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom roundCom).get roundComSome

theorem roundHCom : cryptoDialectToJasminCom roundCom = some roundJcom :=
  (Option.some_get roundComSome).symm

/-- The value `semScalar` leaves in `maj` is the `ofNat 64` image of the
    `RustExec` `Nat`-model reference output `rsF.rsScalar "maj"`. Both sides are
    concrete words; equality by `decide`. -/
theorem roundVal_eq_ref : roundVal = BitVec.ofNat 64 (rsF.rsScalar "maj") := by decide

/-! ## `emitted round = RustExec reference` -/

/-- **The real covered round: `emitted jasmin = RustExec reference output`.** The
    verified pipeline's emitted jasmin program for the SHA-2 `Maj` round kernel
    denotes to the `ctTransTy` image of the `RustExec` reference output word
    `rsF.rsScalar "maj"`. Obtained through the SATISFIABLE closed-kernel route
    `rustToJasminCom_endToEnd_topLevel_unconditional`: the kernel is closed, so
    `semScalar` succeeds from the empty entry env and no entry `EnvRel` seam is
    needed. Axiom-free. -/
theorem roundC_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec roundO.Γ', RustStateInterp roundO.vm rsF Vb')
      ∧ roundJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (rsF.rsScalar "maj")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional roundC roundO N leafSpec rs0 rsF
    roundEnv "maj" roundW roundVal roundCom roundJcom roundC_covered roundHTrans
    (roundC_exec N leafSpec) roundHSem roundHName roundHVal roundHRet roundHCom
  rwa [roundVal_eq_ref] at h

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq
