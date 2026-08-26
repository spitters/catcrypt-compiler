/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody

/-!
# The front-compiled doubling kernel denotes its spec

`Secp256k1PointOpFrontDenote.jacDblFront_denote` ties the descended
`Com catCryptDialect` to the output frame the source semantics leaves at `out`,
and `Secp256k1PointOpWholeBody.jacDblBody_cells` says what that frame holds.
Composing them reads the point-op spec off the `Com`'s own denotation, without
evaluating the flattened `Com` anywhere: `Secp256k1PointOpFront.selfCheck`
records that a single `denote` of it peaks past this host's memory.

The `Com` here is the front's `ret out` cap. Its two matches appear as the
hypotheses `hTrans` and `hName` rather than by unfolding
`Secp256k1PointOpFront.jacDblFrontCom`, because rewriting that definition inside
a proof forces the match scrutinee `translateDialectControl inVM2 jacDblBody` —
the evaluation `selfCheck` measured as infeasible.

## Main results

* `jacDblFrontCom_denote_cells` — the descended doubling `Com`, applied to a
  valuation consistent with a `PrologueEntry` environment, denotes the 12-cell
  frame holding `pointCells (jacDblSpec X Y Z)`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontValue

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (inΓ2 inVM2 jacDblBody jacDblSpec pointCells)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote (jacDblFront_denote)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue (PrologueEntry)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody (jacDblBody_cells)

/-- **The descended doubling `Com` denotes the spec's cell frame.** On a
    valuation consistent with an entry environment in `PrologueEntry`, the
    front's `ret out` cap denotes the twelve cells of
    `pointCells (jacDblSpec X Y Z)`. -/
theorem jacDblFrontCom_denote_cells {n : Nat}
    (o : DTransOut inΓ2) (V : Ctxt.Valuation (d := catCryptDialect) inΓ2)
    (env env' : SEnvScalar) (w : CVar o.Γ' (.memref 12))
    (com : Com catCryptDialect inΓ2 (.memref 12))
    (a : Fin n → BitVec 64) (b : Fin 12 → BitVec 64) (X Y Z : Nat)
    (hE : PrologueEntry env a X Y Z)
    (hout : env "out" = some ⟨.memref 12, b⟩)
    (hTrans : translateDialectControl inVM2 jacDblBody = some o)
    (hCons : ConsistentS inVM2 V env)
    (hSem : semScalar jacDblBody env = some env')
    (hName : o.vm.lookup "out" = some ⟨.memref 12, w⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com) :
    ∀ m : Fin 12,
      ((com.denote V) m).toNat = (pointCells (jacDblSpec X Y Z)).getD m.val 0 := by
  obtain ⟨fr, hfr, hcells⟩ := jacDblBody_cells hE hout hSem
  rw [jacDblFront_denote o V env env' w fr com hTrans hCons hSem hName hfr hRet]
  exact hcells

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontValue
