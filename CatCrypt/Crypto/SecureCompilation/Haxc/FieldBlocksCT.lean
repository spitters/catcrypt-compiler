/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLowerChainCT
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontInstances
meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLowerLeak
meta import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances
meta import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontInstances

/-!
# The blocks of the field template are constant time at the registry primes

`BlocksCT P Pj` (`FieldLowerLeak`) is the hypothesis of the constant-time certificate
`nfChainFCTCert` of the chain `nfChainF`: the events of each Montgomery block of `fieldCom`
do not depend on the words of its arrays. `blocksCT_of_check` derives it from the Boolean
level check `blocksCheck P Pj` of the seven blocks with every array secret.

This file evaluates that check at the leakage parameters `JLeakParams.owned` for the limb
parameters of five primes: P-256, secp256k1 and BN254 (four limbs, `Mont4Instances`) and
P-384 and BLS12-381 (six limbs, `MontInstances`). Each evaluation is a `native_decide` on a
closed Boolean. At these parameters the two constant-time theorems of the chain hold with
no hypothesis on the blocks, on the limb count or on the leakage model.

## Main definitions

This file defines no new object; it instantiates `BlocksCT` and the chain theorems.

## Main results

* `jLeakModel_owned_regArith_quiet` — the `regArith` operations are quiet at
  `JLeakParams.owned`.
* `nfChainF_ct_owned`, `nfChainF_ct_of_levelCheck'_owned` — the chain theorems at
  `JLeakParams.owned`, from the Boolean check `blocksCheck P .owned`.
* `blocksCheck_p256`, `blocksCheck_secp256k1`, `blocksCheck_bn254`, `blocksCheck_p384`,
  `blocksCheck_bls12381` — the level check of the seven blocks at each prime.
* `blocksCT_p256`, …, `blocksCT_bls12381` — `BlocksCT` at each prime.
* `nfChainF_ct_p256`, …, `nfChainF_ct_bls12381` — constant time through the chain of a
  function over the field at each prime.
* `nfChainF_ct_of_levelCheck'_p256`, …, `nfChainF_ct_of_levelCheck'_bls12381` — constant
  time of the exported program from the source level check at each prime.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax.NFFieldSum (nfFieldDialect nfFieldLeakModel SRen)
open CatCrypt.Hax.PrimeirNames (OpTable)
open Ctxt (Var Valuation)
open _root_.Hax (Builtins)

/-! ## 1. The chain theorems at the owned leakage parameters -/

/-- The `regArith` operations are quiet at the leakage parameters of the owned route. -/
theorem jLeakModel_owned_regArith_quiet (bop : JasminBinOp) (w : Nat) :
    (jLeakModel JLeakParams.owned).kind (.regArith bop w) = .quiet := rfl

section Owned

variable {n : Nat} (P : LimbParams n)

/-- **Constant time through the chain at the owned leakage parameters**, from the Boolean
    level check of the blocks: `nfChainF_ct` with `BlocksCT` given by `blocksCT_of_check`. -/
theorem nfChainF_ct_owned (T : OpTable) (hn : n < 2 ^ 64)
    (hc : blocksCheck P .owned = true) (bi : Builtins)
    (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) (prog : NFProg nfDialect Γ [.int])
    {rp : RouteProgJ Θ (arrTy n)} (h : (nfChainF P T σ ρ).run prog = some rp)
    {X₁ X₂ : Valuation Δ} {W₁ W₂ : Valuation Θ} (hA₁ : JAgree P ρ X₁ W₁)
    (hA₂ : JAgree P ρ X₂ W₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₂ = some l₂) (he : l₁ = l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct P T hn (blocksCT_of_check P .owned hc) jLeakModel_owned_regArith_quiet bi fuel
    σ ρ prog h hA₁ hA₂ h₁ h₂ he

/-- **Constant time of the exported program at the owned leakage parameters**, from the
    Boolean level check of the blocks and the level check of the source:
    `nfChainF_ct_of_levelCheck'` with `BlocksCT` given by `blocksCT_of_check`. -/
theorem nfChainF_ct_of_levelCheck'_owned (T : OpTable) (hn : n < 2 ^ 64)
    (hc : blocksCheck P .owned = true)
    (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy n)}
    (h : (nfChainF P T σ ρ).run prog = some rp)
    {q : NFProg nfFieldDialect Δ [.inr (.fp P.p)]}
    (hs : (sumStep P T σ).run (NFProg.dce prog) = some q) (L : Labels Δ)
    (hL : (NFProg.levelCheck' nfFieldLeakModel q L).isSome) {X₁ X₂ : Valuation Δ}
    {W₁ W₂ : Valuation Θ} (hA₁ : JAgree P ρ X₁ W₁) (hA₂ : JAgree P ρ X₂ W₂)
    (hp : PubEqV L X₁ X₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₂ = some l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_of_levelCheck' P T hn (blocksCT_of_check P .owned hc)
    jLeakModel_owned_regArith_quiet bi fuel σ ρ prog h hs L hL hA₁ hA₂ hp h₁ h₂

end Owned

/-! ## 2. P-256 -/

/-- The seven blocks of the template at P-256 pass the level check with every array
    secret, at the owned leakage parameters. -/
theorem blocksCheck_p256 : blocksCheck Mont4Instances.p256 .owned = true := by
  native_decide

/-- The events of the blocks of the template at P-256 do not depend on the valuation. -/
theorem blocksCT_p256 : BlocksCT Mont4Instances.p256 .owned :=
  blocksCT_of_check _ _ blocksCheck_p256

/-- **Constant time through the chain at P-256**: `nfChainF_ct` with no hypothesis on the
    blocks. -/
theorem nfChainF_ct_p256 (T : OpTable) (bi : Builtins)
    (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen (Mont4Instances.p256).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF Mont4Instances.p256 T σ ρ).run prog = some rp)
    {X₁ X₂ : Valuation Δ} {W₁ W₂ : Valuation Θ}
    (hA₁ : JAgree Mont4Instances.p256 ρ X₁ W₁)
    (hA₂ : JAgree Mont4Instances.p256 ρ X₂ W₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce Mont4Instances.p256 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce Mont4Instances.p256 T bi fuel σ).leak prog X₂ = some l₂)
    (he : l₁ = l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_owned _ T (by norm_num) blocksCheck_p256 bi fuel σ ρ prog h hA₁ hA₂
    h₁ h₂ he

/-- **Constant time of the exported program at P-256**: `nfChainF_ct_of_levelCheck'`
    with no hypothesis on the blocks. -/
theorem nfChainF_ct_of_levelCheck'_p256 (T : OpTable)
    (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen (Mont4Instances.p256).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF Mont4Instances.p256 T σ ρ).run prog = some rp)
    {q : NFProg nfFieldDialect Δ [.inr (.fp (Mont4Instances.p256).p)]}
    (hs : (sumStep Mont4Instances.p256 T σ).run (NFProg.dce prog) = some q) (L : Labels Δ)
    (hL : (NFProg.levelCheck' nfFieldLeakModel q L).isSome) {X₁ X₂ : Valuation Δ}
    {W₁ W₂ : Valuation Θ} (hA₁ : JAgree Mont4Instances.p256 ρ X₁ W₁)
    (hA₂ : JAgree Mont4Instances.p256 ρ X₂ W₂)
    (hp : PubEqV L X₁ X₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce Mont4Instances.p256 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce Mont4Instances.p256 T bi fuel σ).leak prog X₂ = some l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_of_levelCheck'_owned _ T (by norm_num) blocksCheck_p256 bi fuel σ ρ prog h hs L
    hL hA₁ hA₂ hp h₁ h₂

/-! ## 3. secp256k1 -/

/-- The seven blocks of the template at secp256k1 pass the level check with every array
    secret, at the owned leakage parameters. -/
theorem blocksCheck_secp256k1 : blocksCheck Mont4Instances.secp256k1 .owned = true := by
  native_decide

/-- The events of the blocks of the template at secp256k1 do not depend on the valuation. -/
theorem blocksCT_secp256k1 : BlocksCT Mont4Instances.secp256k1 .owned :=
  blocksCT_of_check _ _ blocksCheck_secp256k1

/-- **Constant time through the chain at secp256k1**: `nfChainF_ct` with no hypothesis on the
    blocks. -/
theorem nfChainF_ct_secp256k1 (T : OpTable) (bi : Builtins)
    (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen (Mont4Instances.secp256k1).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF Mont4Instances.secp256k1 T σ ρ).run prog = some rp)
    {X₁ X₂ : Valuation Δ} {W₁ W₂ : Valuation Θ}
    (hA₁ : JAgree Mont4Instances.secp256k1 ρ X₁ W₁)
    (hA₂ : JAgree Mont4Instances.secp256k1 ρ X₂ W₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce Mont4Instances.secp256k1 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce Mont4Instances.secp256k1 T bi fuel σ).leak prog X₂ = some l₂)
    (he : l₁ = l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_owned _ T (by norm_num) blocksCheck_secp256k1 bi fuel σ ρ prog h hA₁ hA₂
    h₁ h₂ he

/-- **Constant time of the exported program at secp256k1**: `nfChainF_ct_of_levelCheck'`
    with no hypothesis on the blocks. -/
theorem nfChainF_ct_of_levelCheck'_secp256k1 (T : OpTable)
    (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen (Mont4Instances.secp256k1).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF Mont4Instances.secp256k1 T σ ρ).run prog = some rp)
    {q : NFProg nfFieldDialect Δ [.inr (.fp (Mont4Instances.secp256k1).p)]}
    (hs : (sumStep Mont4Instances.secp256k1 T σ).run (NFProg.dce prog) = some q)
    (L : Labels Δ)
    (hL : (NFProg.levelCheck' nfFieldLeakModel q L).isSome) {X₁ X₂ : Valuation Δ}
    {W₁ W₂ : Valuation Θ} (hA₁ : JAgree Mont4Instances.secp256k1 ρ X₁ W₁)
    (hA₂ : JAgree Mont4Instances.secp256k1 ρ X₂ W₂)
    (hp : PubEqV L X₁ X₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce Mont4Instances.secp256k1 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce Mont4Instances.secp256k1 T bi fuel σ).leak prog X₂ = some l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_of_levelCheck'_owned _ T (by norm_num) blocksCheck_secp256k1 bi fuel σ ρ prog h
    hs L hL hA₁ hA₂ hp h₁ h₂

/-! ## 4. BN254 -/

/-- The seven blocks of the template at BN254 pass the level check with every array
    secret, at the owned leakage parameters. -/
theorem blocksCheck_bn254 : blocksCheck Mont4Instances.bn254 .owned = true := by
  native_decide

/-- The events of the blocks of the template at BN254 do not depend on the valuation. -/
theorem blocksCT_bn254 : BlocksCT Mont4Instances.bn254 .owned :=
  blocksCT_of_check _ _ blocksCheck_bn254

/-- **Constant time through the chain at BN254**: `nfChainF_ct` with no hypothesis on the
    blocks. -/
theorem nfChainF_ct_bn254 (T : OpTable) (bi : Builtins)
    (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen (Mont4Instances.bn254).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF Mont4Instances.bn254 T σ ρ).run prog = some rp)
    {X₁ X₂ : Valuation Δ} {W₁ W₂ : Valuation Θ}
    (hA₁ : JAgree Mont4Instances.bn254 ρ X₁ W₁)
    (hA₂ : JAgree Mont4Instances.bn254 ρ X₂ W₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce Mont4Instances.bn254 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce Mont4Instances.bn254 T bi fuel σ).leak prog X₂ = some l₂)
    (he : l₁ = l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_owned _ T (by norm_num) blocksCheck_bn254 bi fuel σ ρ prog h hA₁ hA₂
    h₁ h₂ he

/-- **Constant time of the exported program at BN254**: `nfChainF_ct_of_levelCheck'`
    with no hypothesis on the blocks. -/
theorem nfChainF_ct_of_levelCheck'_bn254 (T : OpTable)
    (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen (Mont4Instances.bn254).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF Mont4Instances.bn254 T σ ρ).run prog = some rp)
    {q : NFProg nfFieldDialect Δ [.inr (.fp (Mont4Instances.bn254).p)]}
    (hs : (sumStep Mont4Instances.bn254 T σ).run (NFProg.dce prog) = some q) (L : Labels Δ)
    (hL : (NFProg.levelCheck' nfFieldLeakModel q L).isSome) {X₁ X₂ : Valuation Δ}
    {W₁ W₂ : Valuation Θ} (hA₁ : JAgree Mont4Instances.bn254 ρ X₁ W₁)
    (hA₂ : JAgree Mont4Instances.bn254 ρ X₂ W₂)
    (hp : PubEqV L X₁ X₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce Mont4Instances.bn254 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce Mont4Instances.bn254 T bi fuel σ).leak prog X₂ = some l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_of_levelCheck'_owned _ T (by norm_num) blocksCheck_bn254 bi fuel σ ρ prog h hs L
    hL hA₁ hA₂ hp h₁ h₂

/-! ## 5. P-384 -/

/-- The seven blocks of the template at P-384 pass the level check with every array
    secret, at the owned leakage parameters. -/
theorem blocksCheck_p384 : blocksCheck MontInstances.p384 .owned = true := by
  native_decide

/-- The events of the blocks of the template at P-384 do not depend on the valuation. -/
theorem blocksCT_p384 : BlocksCT MontInstances.p384 .owned :=
  blocksCT_of_check _ _ blocksCheck_p384

/-- **Constant time through the chain at P-384**: `nfChainF_ct` with no hypothesis on the
    blocks. -/
theorem nfChainF_ct_p384 (T : OpTable) (bi : Builtins)
    (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen (MontInstances.p384).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF MontInstances.p384 T σ ρ).run prog = some rp)
    {X₁ X₂ : Valuation Δ} {W₁ W₂ : Valuation Θ}
    (hA₁ : JAgree MontInstances.p384 ρ X₁ W₁)
    (hA₂ : JAgree MontInstances.p384 ρ X₂ W₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce MontInstances.p384 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce MontInstances.p384 T bi fuel σ).leak prog X₂ = some l₂)
    (he : l₁ = l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_owned _ T (by norm_num) blocksCheck_p384 bi fuel σ ρ prog h hA₁ hA₂
    h₁ h₂ he

/-- **Constant time of the exported program at P-384**: `nfChainF_ct_of_levelCheck'`
    with no hypothesis on the blocks. -/
theorem nfChainF_ct_of_levelCheck'_p384 (T : OpTable)
    (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen (MontInstances.p384).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF MontInstances.p384 T σ ρ).run prog = some rp)
    {q : NFProg nfFieldDialect Δ [.inr (.fp (MontInstances.p384).p)]}
    (hs : (sumStep MontInstances.p384 T σ).run (NFProg.dce prog) = some q) (L : Labels Δ)
    (hL : (NFProg.levelCheck' nfFieldLeakModel q L).isSome) {X₁ X₂ : Valuation Δ}
    {W₁ W₂ : Valuation Θ} (hA₁ : JAgree MontInstances.p384 ρ X₁ W₁)
    (hA₂ : JAgree MontInstances.p384 ρ X₂ W₂)
    (hp : PubEqV L X₁ X₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce MontInstances.p384 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce MontInstances.p384 T bi fuel σ).leak prog X₂ = some l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_of_levelCheck'_owned _ T (by norm_num) blocksCheck_p384 bi fuel σ ρ prog h hs L
    hL hA₁ hA₂ hp h₁ h₂

/-! ## 6. BLS12-381 -/

/-- The seven blocks of the template at BLS12-381 pass the level check with every array
    secret, at the owned leakage parameters. -/
theorem blocksCheck_bls12381 : blocksCheck MontInstances.bls12381 .owned = true := by
  native_decide

/-- The events of the blocks of the template at BLS12-381 do not depend on the valuation. -/
theorem blocksCT_bls12381 : BlocksCT MontInstances.bls12381 .owned :=
  blocksCT_of_check _ _ blocksCheck_bls12381

/-- **Constant time through the chain at BLS12-381**: `nfChainF_ct` with no hypothesis on the
    blocks. -/
theorem nfChainF_ct_bls12381 (T : OpTable) (bi : Builtins)
    (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen (MontInstances.bls12381).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF MontInstances.bls12381 T σ ρ).run prog = some rp)
    {X₁ X₂ : Valuation Δ} {W₁ W₂ : Valuation Θ}
    (hA₁ : JAgree MontInstances.bls12381 ρ X₁ W₁)
    (hA₂ : JAgree MontInstances.bls12381 ρ X₂ W₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce MontInstances.bls12381 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce MontInstances.bls12381 T bi fuel σ).leak prog X₂ = some l₂)
    (he : l₁ = l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_owned _ T (by norm_num) blocksCheck_bls12381 bi fuel σ ρ prog h hA₁ hA₂
    h₁ h₂ he

/-- **Constant time of the exported program at BLS12-381**: `nfChainF_ct_of_levelCheck'`
    with no hypothesis on the blocks. -/
theorem nfChainF_ct_of_levelCheck'_bls12381 (T : OpTable)
    (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen (MontInstances.bls12381).p Γ Δ) (ρ : JRen _ Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy _)}
    (h : (nfChainF MontInstances.bls12381 T σ ρ).run prog = some rp)
    {q : NFProg nfFieldDialect Δ [.inr (.fp (MontInstances.bls12381).p)]}
    (hs : (sumStep MontInstances.bls12381 T σ).run (NFProg.dce prog) = some q) (L : Labels Δ)
    (hL : (NFProg.levelCheck' nfFieldLeakModel q L).isSome) {X₁ X₂ : Valuation Δ}
    {W₁ W₂ : Valuation Θ} (hA₁ : JAgree MontInstances.bls12381 ρ X₁ W₁)
    (hA₂ : JAgree MontInstances.bls12381 ρ X₂ W₂)
    (hp : PubEqV L X₁ X₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce MontInstances.bls12381 T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce MontInstances.bls12381 T bi fuel σ).leak prog X₂ = some l₂) :
    ∃ m, RouteProgJ.ctLeak .owned fuel rp W₁ = some m ∧
      RouteProgJ.ctLeak .owned fuel rp W₂ = some m :=
  nfChainF_ct_of_levelCheck'_owned _ T (by norm_num) blocksCheck_bls12381 bi fuel σ ρ prog h
    hs L hL hA₁ hA₂ hp h₁ h₂

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
