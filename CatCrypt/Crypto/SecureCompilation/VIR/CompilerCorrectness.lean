/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintCorrect

/-!
# End-to-end compiler correctness on the `Com` chain

This file composes the per-stage results of the `Com`-based compiler into one
end-to-end statement for the ML-KEM NTT-multiplication route — the path the
whole jasmin ⇄ VIR convergence was built for:

```
Com[lattice]  ──optimizer rewrite──▶  Com[lattice]  ──A3 lowering──▶  Com[jasmin]  ──printer──▶ .jazz ──jasminc──▶ asm
  (poly_mul)     nttMul_rewrite          (ntt·basemul·invntt)   lowerLatticeToJasmin      lowerComToProg
```

## The headline

`latticeNttMul_compile_correct`: the *optimized and lowered* jasmin program
denotes to the **same function** as the source coefficient-form multiply,
**unconditionally** (no leaf-agreement hypothesis). It composes exactly two
verified facts:

* `LatticeDialect.nttMul_rewrite_denote_eq` — the NTT-domain rewrite
  `poly_mul a b = invntt (basemul (ntt a) (ntt b))` preserves `Com.denote`
  (the optimizer step);
* `LatticeToJasminDenoteUncond.tgtCom_denote_preserved_uncond` — the
  lattice→jasmin dialect lowering preserves `Com.denote` (A3: discharged via
  `JasminDialect.jasminExtSem`).

`latticeNttMul_emit_wellformed` then ties in the printer (A4): the emitted
`JasminProg` has exactly one instruction per source binding (four: the two
forward NTTs, the base multiply, the inverse NTT).

## Trust base (the parametric edges)

The end-to-end functional-correctness story bottoms out at four explicit edges,
each handled separately rather than hand-waved:

1. **extraction → LowCT** — `haxToLowCT_simulates_full`, discharged
   per-protocol by the bridge `Hyp_*` obligations.
2. **leaf-spec'd jasmin denotation** — for the lattice leaves this is
   *discharged* (A3, `jasminExtSem`); for external leaves (CryptoSSA
   `fp_*` intrinsics on the `cryptoDialectToJasminCom` front, A1) it stays parametric in
   `CryptoToJasminComCorrect.JasminLeafAgrees`.
3. **semantic printer faithfulness** — only the *structural* faithfulness is
   proved here (`JasminPrintCorrect`, instruction/parameter counts); the
   `JasminProg → .jazz` text and its parse are a later tier.
4. **`.jazz → x86`** — `jasminc`, the verified assembly backend, is the
   deliberate trusted base; we do not re-verify it.

The LowCT→CryptoSSA→Com[catCrypt] front (`LowCTToCryptoSSACorrect`,
`CryptoToVIRCorrect`) and the CProg→Com[jasmin] front (A1,
`cryptoDialectToJasminCom_denote_eq`) are the verified upstream halves; the lattice
route below is the verified optimizer+backend half.

0 sorries.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectness

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-! ## 1. The end-to-end denotational correctness (lattice route) -/

/-- **End-to-end compiler correctness (lattice NTT-mul route).** The jasmin
    program obtained by *optimizing* the source coefficient-form multiply into
    the NTT-domain sequence and *lowering* it across the lattice→jasmin dialect
    conversion denotes to the `transTy`-transport of the source program's
    denotation — for every input valuation, with **no hypothesis**.

    Since `transTy` is the (computed) identity transport `⟦t⟧ → ⟦tau t⟧`, this is
    exactly: *the compiled jasmin code computes the same polynomial product as
    the source `poly_mul`*. Composes the optimizer-rewrite soundness
    (`nttMul_rewrite_denote_eq`) with the A3 backend-lowering soundness
    (`tgtCom_denote_preserved_uncond`). -/
theorem latticeNttMul_compile_correct (q n : Nat)
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)).denote (mapVal V)
      = transTy ((LatticeDialect.srcCom q n).denote V) := by
  rw [tgtCom_denote_preserved_uncond, nttMul_rewrite_denote_eq]

/-! ## 2. The emission is well-formed (printer structure, A4) -/

/-- **Emission well-formedness.** The `JasminProg` emitted from the optimized,
    lowered ML-KEM multiply has exactly one instruction per source binding — the
    four NTT-domain operations `ntt a`, `ntt b`, `basemul`, `invntt`. Ties the
    A4 printer-faithfulness (`lowerComToProg_body_length`) to the lattice route. -/
theorem latticeNttMul_emit_wellformed (q n : Nat) :
    ((lowerComToProg "ntt_mul" (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)))
      |>.funcs.head?.map (fun fd => fd.body.length)) = some 4 := by
  rw [lowerComToProg_body_length]
  simp only [LatticeDialect.tgtCom, LatticeToJasmin.lowerLatticeToJasmin, Com.jOpCount]

/-- A single function is emitted (printer, A4). -/
theorem latticeNttMul_emit_one_func (q n : Nat) :
    (lowerComToProg "ntt_mul" (lowerLatticeToJasmin (LatticeDialect.tgtCom q n))).funcs.length
      = 1 := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectness
