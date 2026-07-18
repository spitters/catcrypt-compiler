/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CompilerLoweringRegistry
import CatCrypt.Crypto.Bridges.Transfer.CompilerRegistry

/-!
# The run-output read-back: splicing the dialect chain into the x86 ALU domain

## Scope

`EndToEndTransport.lean` composed the dialect-lowering transport with one x86
instruction step *as shapes* (both are `TransportSquare`s), on a representative
scalar carrier with `id` encodings — and named the obligation a genuine splice
needs: a read-back from the dialect chain's structured run-output to the
`BitVec`-word value model the x86 instruction transport consumes. This file
**builds that read-back** and **splices the two halves through it**.

The two value models, made precise:

* the dialect chain (`CompilerLoweringRegistry.registryChain_threePass'`) ends at
  `runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)`, whose Lean type
  is `⟦tau (.polyC q n)⟧ = ⟦.stackArr 16 n⟧ = (Fin n → BitVec 16)` — a *structured*
  stack-array run-output (the lowered ML-KEM NTT-mul result), equal by the chain to
  `transTy ((srcCom q n).denote V)`;
* the x86 instruction transport (`Bridges/Transfer/CompilerRegistry`,
  `RelatedBinOp id (·+·) x86Add`) reads a *scalar* `BitVec w` word, one ALU op at a
  time (`x86Add a b = a + b`).

`runOutputToWords` is the read-back: index the structured run-output at a slot
`i : Fin n` to obtain the `BitVec 16` word the x86 ALU consumes. It is the
`Com`-valuation/run-output ↦ machine-word interface `EndToEndTransport`'s `Scope`
named as missing.

The splice lemma `slot_runOutput_x86Add_eq` then composes the dialect chain (read
back at slot `i`) with the x86 `ADD` step: the i-th coefficient of the *source*
dialect program's denotation, realised by the emitted jasmin program's run-output
and read back to a `BitVec 16` word, added to a second operand `b` by the emitted
x86 `ADD` instruction, equals the abstract sum of that coefficient and `b`. This
closes the seam: it is one statement whose left factor is the genuine 3-pass
`registryChain_threePass'` (not a representative `id/id` square) and whose right
factor is the x86 instruction step, joined **through** `runOutputToWords` — not a
same-carrier shortcut.

### What is general vs. scalar-only

The read-back is **genuinely partial**, and the partiality is the structured
nature of the run-output, not a gap in this file:

* a **scalar slot** read-back is total and clean: index the `Fin n → BitVec 16`
  run-output at any `i : Fin n` and feed it to the (width-16) ALU. This is
  `runOutputToWords`, delivered here, and the splice above is proved on it.
* a **whole-array / multi-output / SIMD** read-back — turning the entire
  `Fin n → BitVec 16` run-output into the operand model of a *vector* or
  *multi-result* x86 step — is not a single word: it needs a per-lane (or packed
  `reg (16*k)`) read-back and a vector preservation lemma (`RelatedBinOp` is
  scalar-binary). That generalisation reads back each slot independently and the
  scalar splice here is the per-slot instance of it; the packed/lane interface is
  the remaining work, documented but not fabricated as a total map.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RunOutputReadback

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerLoweringRegistry
open Transfer

/-! ## 1. The read-back: structured stack-array run-output ↦ scalar ALU word

The dialect chain's run-output has type `⟦.stackArr 16 n⟧ = (Fin n → BitVec 16)`.
The x86 ALU consumes a single `BitVec 16`. The read-back reads the slot at a
chosen index `i : Fin n`. -/

/-- **The run-output read-back (scalar slot).** Read the `BitVec 16` word at slot
    `i : Fin n` out of a structured stack-array run-output `out : Fin n → BitVec 16`
    — the `Com`-valuation/run-output ↦ machine-word interface the x86 ALU domain
    consumes. This is total on a single slot; the whole-array (vector/SIMD)
    read-back is per-slot of this (see module `Scope`). -/
def runOutputToWords {n : Nat} (out : Fin n → BitVec 16) (i : Fin n) : BitVec 16 :=
  out i

/-- The read-back of the dialect chain's run-output at slot `i` is exactly the
    i-th coefficient of the `transTy`-transported source denotation — i.e. running
    the emitted jasmin program and reading back slot `i` computes the i-th
    coefficient of the source dialect program's denotation. Folds
    `registryChain_threePass'` through `runOutputToWords`. -/
theorem runOutputToWords_chain_eq (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n)) (i : Fin n) :
    runOutputToWords
        (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)) i
      = runOutputToWords (transTy ((srcCom q n).denote V)) i := by
  unfold runOutputToWords
  rw [registryChain_threePass' q n hLeaf hInj hPinj V]

/-! ## 2. The splice: dialect chain (read back) ∘ x86 instruction step

The genuine end-to-end statement. The left factor is the real 3-pass chain
`registryChain_threePass'` read back at slot `i` via `runOutputToWords`; the right
factor is the x86 `ADD` preservation. They join through the read-back: the slot's
word feeds the (width-16) x86 ALU step. -/

/-- **End-to-end splice through the read-back (scalar slot ⋆ x86 `ADD`).**

    Let `out` be the structured run-output of the emitted jasmin program
    (`runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)`), `i : Fin n`
    a slot, and `b : BitVec 16` a second operand. Then the emitted x86 `ADD`
    instruction applied to the **read-back** word `runOutputToWords out i` and `b`
    equals the abstract sum of (the i-th coefficient of the *source* dialect
    program's denotation) and `b`:

        x86Add (runOutputToWords out i) b
          = runOutputToWords (transTy ((srcCom q n).denote V)) i + b.

    This is the genuine end-to-end value-preservation: source-dialect denotation
    (`(srcCom q n).denote V`), read back to a machine word at slot `i`
    (`runOutputToWords … i`), realised by the emitted x86 instruction (`x86Add`),
    equal to the abstract op. Its left factor is the full 3-pass
    `registryChain_threePass'` (via `runOutputToWords_chain_eq`) — **not** the
    representative `id/id` square of `EndToEndTransport` — and its right factor is
    the registered x86 `ADD` preservation (`x86Add_eq` at width 16); the two are
    joined **through** `runOutputToWords`, closing the seam. -/
theorem slot_runOutput_x86Add_eq (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n)) (i : Fin n) (b : BitVec 16) :
    x86Add
        (runOutputToWords
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)) i) b
      = runOutputToWords (transTy ((srcCom q n).denote V)) i + b := by
  rw [x86Add_eq, runOutputToWords_chain_eq q n hLeaf hInj hPinj V i]

/-- **The same splice, stated with the read-back word named.** Choosing the second
    operand to also be a read-back slot `j` makes both ALU operands come from the
    emitted jasmin run-output: the emitted x86 `ADD` of coefficients `i` and `j` of
    the run-output equals the abstract sum of the source program's `i`-th and
    `j`-th coefficients. A two-operand instance of the splice, both operands
    crossing the run-output ↦ word seam. -/
theorem slot_runOutput_x86Add_eq_pair (q n : Nat)
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
        (v : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t)
        (v' : Ctxt.Var (d := jasminDialect) ((inCtxt q n).map tau) t'),
        (paramsAndMap ((inCtxt q n).map tau)).2 t v
          = (paramsAndMap ((inCtxt q n).map tau)).2 t' v' →
        (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (inCtxt q n)) (i j : Fin n) :
    x86Add
        (runOutputToWords
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)) i)
        (runOutputToWords
          (runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)) j)
      = runOutputToWords (transTy ((srcCom q n).denote V)) i
          + runOutputToWords (transTy ((srcCom q n).denote V)) j := by
  rw [x86Add_eq, runOutputToWords_chain_eq q n hLeaf hInj hPinj V i,
    runOutputToWords_chain_eq q n hLeaf hInj hPinj V j]

end CatCrypt.Crypto.SecureCompilation.VIR.RunOutputReadback
