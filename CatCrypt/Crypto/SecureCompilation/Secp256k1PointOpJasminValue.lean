/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontValue
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

/-!
# The point-op spec at the jasmin dialect

`Secp256k1PointOpFrontValue` reads the point-op spec off the descended
`Com catCryptDialect`, conditional on the source semantics running.
`Secp256k1PointOpTotal` discharges that run. Composing the two removes the
hypothesis, and `DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`
carries the result one dialect further down, to the `Com jasminDialect` the
owned backend consumes.

`JasminValTransport.ctTransTy` is the identity on `.memref`, so the twelve cells
transport unchanged; the statement below is the same cell equation at the lower
dialect.

## Main results

* `jacDblFrontCom_denote_cells_total`, `jacAddFrontCom_denote_cells_total` — the
  `catCryptDialect` point-op `Com`s denote `pointCells` of their spec, with the
  source run discharged rather than assumed.
* `jacDblJasminCom_denote_cells`, `jacAddJasminCom_denote_cells` — the same, one
  dialect down, at the `Com jasminDialect` the backend lowers to `Lprog`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpJasminValue

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
  (cryptoDialectToJasminCom_denote_eq' ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect
  (ctTransTy ctTransTy_memref)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (inΓ2 inΓ3 inVM2 inVM3 jacDblBody jacAddBody jacDblSpec jacAddSpec pointCells)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue (PrologueEntry)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpAddVertical (AddPrologueEntry)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontValue
  (jacDblFrontCom_denote_cells)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpAddVertical
  (jacAddFrontCom_denote_cells)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal
  (jacDblBody_runs jacAddBody_runs)

/-! ## 1. The source run discharged -/

/-- **The descended doubling `Com` denotes the spec's cells, unconditionally.**
    `jacDblFrontCom_denote_cells` with its `semScalar` hypothesis supplied by
    `jacDblBody_runs`. -/
theorem jacDblFrontCom_denote_cells_total {n : Nat}
    (o : DTransOut inΓ2) (V : Ctxt.Valuation (d := catCryptDialect) inΓ2)
    (env : SEnvScalar) (w : CVar o.Γ' (.memref 12))
    (com : Com catCryptDialect inΓ2 (.memref 12))
    (a : Fin n → BitVec 64) (b : Fin 12 → BitVec 64) (X Y Z : Nat)
    (hE : PrologueEntry env a X Y Z)
    (hout : env "out" = some ⟨.memref 12, b⟩)
    (hTrans : translateDialectControl inVM2 jacDblBody = some o)
    (hCons : ConsistentS inVM2 V env)
    (hName : o.vm.lookup "out" = some ⟨.memref 12, w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com) :
    ∀ m : Fin 12,
      ((com.denote V) m).toNat = (pointCells (jacDblSpec X Y Z)).getD m.val 0 := by
  obtain ⟨env', hrun⟩ := jacDblBody_runs hE hout
  exact jacDblFrontCom_denote_cells o V env env' w com a b X Y Z hE hout hTrans hCons
    hrun hName hRet

/-- **The descended addition `Com` denotes the spec's cells, unconditionally.** -/
theorem jacAddFrontCom_denote_cells_total {n : Nat}
    (o : DTransOut inΓ3) (V : Ctxt.Valuation (d := catCryptDialect) inΓ3)
    (env : SEnvScalar) (w : CVar o.Γ' (.memref 12))
    (com : Com catCryptDialect inΓ3 (.memref 12))
    (a1 a2 : Fin n → BitVec 64) (b : Fin 12 → BitVec 64) (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hE : AddPrologueEntry env a1 a2 X1 Y1 Z1 X2 Y2 Z2)
    (hout : env "out" = some ⟨.memref 12, b⟩)
    (hTrans : translateDialectControl inVM3 jacAddBody = some o)
    (hCons : ConsistentS inVM3 V env)
    (hName : o.vm.lookup "out" = some ⟨.memref 12, w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com) :
    ∀ m : Fin 12,
      ((com.denote V) m).toNat
        = (pointCells (jacAddSpec X1 Y1 Z1 X2 Y2 Z2)).getD m.val 0 := by
  obtain ⟨env', hrun⟩ := jacAddBody_runs hE hout
  exact jacAddFrontCom_denote_cells o V env env' w com a1 a2 b X1 Y1 Z1 X2 Y2 Z2 hE hout
    hTrans hCons hrun hName hRet

/-! ## 2. One dialect down -/

/-- **The lowered doubling `Com jasminDialect` denotes the spec's cells.**
    `ctTransTy` is the identity on `.memref`, so the twelve cells cross the
    dialect boundary unchanged. -/
theorem jacDblJasminCom_denote_cells {n : Nat}
    (o : DTransOut inΓ2) (V : Ctxt.Valuation (d := catCryptDialect) inΓ2)
    (env : SEnvScalar) (w : CVar o.Γ' (.memref 12))
    (com : Com catCryptDialect inΓ2 (.memref 12))
    (jcom : Com jasminDialect (mapCtx inΓ2) (mapTy (.memref 12)))
    (a : Fin n → BitVec 64) (b : Fin 12 → BitVec 64) (X Y Z : Nat)
    (hE : PrologueEntry env a X Y Z)
    (hout : env "out" = some ⟨.memref 12, b⟩)
    (hTrans : translateDialectControl inVM2 jacDblBody = some o)
    (hCons : ConsistentS inVM2 V env)
    (hName : o.vm.lookup "out" = some ⟨.memref 12, w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hLower : cryptoDialectToJasminCom com = some jcom) :
    ∀ m : Fin 12,
      ((jcom.denote (ctMapValD V)) m).toNat
        = (pointCells (jacDblSpec X Y Z)).getD m.val 0 := by
  intro m
  rw [cryptoDialectToJasminCom_denote_eq' com V jcom hLower, ctTransTy_memref]
  exact jacDblFrontCom_denote_cells_total o V env w com a b X Y Z hE hout hTrans hCons
    hName hRet m

/-- **The lowered addition `Com jasminDialect` denotes the spec's cells.** -/
theorem jacAddJasminCom_denote_cells {n : Nat}
    (o : DTransOut inΓ3) (V : Ctxt.Valuation (d := catCryptDialect) inΓ3)
    (env : SEnvScalar) (w : CVar o.Γ' (.memref 12))
    (com : Com catCryptDialect inΓ3 (.memref 12))
    (jcom : Com jasminDialect (mapCtx inΓ3) (mapTy (.memref 12)))
    (a1 a2 : Fin n → BitVec 64) (b : Fin 12 → BitVec 64) (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hE : AddPrologueEntry env a1 a2 X1 Y1 Z1 X2 Y2 Z2)
    (hout : env "out" = some ⟨.memref 12, b⟩)
    (hTrans : translateDialectControl inVM3 jacAddBody = some o)
    (hCons : ConsistentS inVM3 V env)
    (hName : o.vm.lookup "out" = some ⟨.memref 12, w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hLower : cryptoDialectToJasminCom com = some jcom) :
    ∀ m : Fin 12,
      ((jcom.denote (ctMapValD V)) m).toNat
        = (pointCells (jacAddSpec X1 Y1 Z1 X2 Y2 Z2)).getD m.val 0 := by
  intro m
  rw [cryptoDialectToJasminCom_denote_eq' com V jcom hLower, ctTransTy_memref]
  exact jacAddFrontCom_denote_cells_total o V env w com a1 a2 b X1 Y1 Z1 X2 Y2 Z2 hE hout
    hTrans hCons hName hRet m

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpJasminValue
