/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringTransport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-!
# The lowering-pass registry — program transports + a derived 3-pass chain

`DialectLoweringTransport.lean` defines `TransportSquare g φin φout f`
— the engine-agnostic map₁ transport square `f (φin x) = φout (g x)` that every
program-level lowering preservation lemma
`(lower c).denote (mapVal V) = transTy (c.denote V)` inhabits — together with
`TransportSquare.comp`, the transitivity that pastes two adjacent passes, and a
**two-pass** pilot (optimizer rewrite ∘ A3 lattice→jasmin lowering) reproducing
the hand `rw`-chain `CompilerCorrectness.latticeNttMul_compile_correct`.

This module registers the program-level transports of the
ML-KEM NTT-multiplication route as `TransportSquare` values, then **derives a
three-pass end-to-end chain** by *iterated* `TransportSquare.comp` — one
transitivity tree in place of the hand composition — and records the `rfl`/defeq
witness that the derived chain refines the hand result rather than weakening it.

## The three program-level transports of the lattice route

All three carry the `f (φin V) = φout (g V)` square over `Com.denote`/`runProg`:

* **Pass 1 — optimizer rewrite** (lattice→lattice, **carrier-preserving**,
  `φin = φout = id`).  `LatticeDialect.nttMul_rewrite_denote_eq` rewrites the
  coefficient-form `poly_mul` into the NTT-domain sequence; the source denotation
  `(srcCom).denote` transports to the expanded `(tgtCom).denote`.  Registered as
  `regPass1_optimizer`.
* **Pass 2 — A3 lattice→jasmin lowering** (lattice→jasmin, **carrier-changing**,
  `φin = mapVal`, `φout = transTy`).
  `LatticeToJasminDenoteUncond.tgtCom_denote_preserved_uncond` lowers the expanded
  target across the dialect conversion.  The leaf-agreement obligation is
  *discharged* upstream (`latticeLeafAgrees`, via `JasminDialect.jasminExtSem`), so
  this transport carries **no** parametric hypothesis.  Registered as
  `regPass2_lowering`.
* **Pass 3 — A4 printer semantics** (jasmin `Com`→emitted `JasminProg` run,
  **carrier-preserving**, `φin = φout = id`).
  `JasminPrintSemCorrect.lowerComToProg_sem_eq` says running the *emitted* program
  (`runProg leafSem com`) on a valuation computes exactly `com.denote V` — the
  semantic half of printer faithfulness, on the straight-line fragment.  As a
  transport its abstract function is `(lowerLatticeToJasmin tgtCom).denote` and its
  realised function is `runProg leafSem (lowerLatticeToJasmin tgtCom)`.  This pass
  is **parametric** in the printer's edges — leaf agreement of the
  evaluator (`hLeaf : LeafAgrees leafSem`), fresh-name injectivity (`hInj`),
  parameter-resolver injectivity (`hPinj`), and straight-lineness of the emitted
  program (`hSL`, here discharged: the lowered NTT program is all `extCall`s, never
  the aliasing `stackStore`).  Those hypotheses are **threaded explicitly** as
  hypotheses of the registered transport `regPass3_printer …`.  Registered as
  `regPass3_printer`.

## The derived three-pass chain

`registryChain_threePass` pastes the three squares with two applications of
`TransportSquare.comp` — `(regPass1 ⋆ regPass2) ⋆ regPass3` — to obtain, with **no**
hand `rw`-chain over the three preservation lemmas,

    runProg leafSem (lowerLatticeToJasmin (tgtCom q n)) (mapVal V)
      = transTy ((srcCom q n).denote V).

The two adjacencies are `rfl` (each pass's abstract source *is* the previous
pass's realised target).  `registryChain_refines_handResult` records that
**dropping pass 3** (the first two passes of the same transitivity tree) is
*definitionally* the hand-chained
`CompilerCorrectness.latticeNttMul_compile_correct` — so the three-pass chain is a
faithful *extension* of the hand result (printer semantics appended), not a weaker
corollary.

## Scope — the L2/L3/L4/L4′ same-dialect lowerings are op-level, not registered here

`DialectLoweringChain.lean` composes the L2 ModArith / L3 Field / L4 EllipticCurve
/ L4′ Poly lowerings.  Those are **op-level identity realisations** — `realise op
args = denote op args` proved by `rfl` because each level's leaf *is* the
lower-level leaf (`fMulF = modMulF`, …), composed by transitivity of op-level
equalities (`curveChainDenote`, `extChainDenote`, `polyChainDenote`).  They are
**not** `Com`-program transports: there is no shared program-level `mapVal`/
`transTy` interface across those dialects, and the chain is over abstract math
values, not `Com.denote ∘ mapVal`.  We therefore **do not** force-fit them as
`TransportSquare` over `Com`; registering them as program transports would
misrepresent their op-granular content.  They remain
`DialectLoweringChain`'s op-level realisation facts, and only the three
program-level passes above are registered here.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompilerLoweringRegistry

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringTransport

variable (q n : Nat)

/-! ## 1. Pass 1 — optimizer rewrite (carrier-preserving)

The NTT-domain rewrite, as a `φin = φout = id` transport from the source
`poly_mul` denotation to the expanded `tgtCom` denotation.  Reuses the
`DialectLoweringTransport` wrapper directly (the same registration as its
two-pass pilot). -/

/-- **Registered pass 1.** The optimizer rewrite
    `LatticeDialect.nttMul_rewrite_denote_eq` as a carrier-preserving map₁
    transport `(srcCom).denote ↦ (tgtCom).denote` along `(id, id)`. -/
theorem regPass1_optimizer :
    TransportSquare
      (g := fun V : Ctxt.Valuation (LatticeDialect.inCtxt q n) =>
              (LatticeDialect.srcCom q n).denote V)
      (φin := id) (φout := id)
      (f := fun V => (LatticeDialect.tgtCom q n).denote V) :=
  ⟨fun V => (LatticeDialect.nttMul_rewrite_denote_eq q n V).symm⟩

/-! ## 2. Pass 2 — A3 lattice→jasmin lowering (carrier-changing, hypothesis-free)

The dialect lowering of the expanded target, as a `φin = mapVal`, `φout = transTy`
transport.  The leaf-agreement obligation is discharged upstream
(`latticeLeafAgrees`), so this transport carries no parametric hypothesis. -/

/-- **Registered pass 2.** The lattice→jasmin lowering
    `LatticeToJasminDenoteUncond.tgtCom_denote_preserved_uncond` as a
    carrier-changing map₁ transport `(tgtCom).denote ↦ (lowerLatticeToJasmin
    tgtCom).denote` along `(mapVal, transTy)`.  No leaf-agreement hypothesis: it is
    discharged by `latticeLeafAgrees`. -/
theorem regPass2_lowering :
    TransportSquare
      (g := fun V : Ctxt.Valuation (LatticeDialect.inCtxt q n) =>
              (LatticeDialect.tgtCom q n).denote V)
      (φin := mapVal) (φout := transTy)
      (f := fun V' => (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)).denote V') :=
  ⟨fun V => tgtCom_denote_preserved_uncond q n V⟩

/-! ## 3. Pass 3 — A4 printer semantics (carrier-preserving, parametric)

Running the *emitted* `JasminProg` computes the jasmin `Com.denote`
(`lowerComToProg_sem_eq`).  As a transport its abstract function is
`(lowerLatticeToJasmin tgtCom).denote` and its realised function is
`runProg leafSem (lowerLatticeToJasmin tgtCom)`; both read a
`Ctxt.Valuation (mapCtx …)`, so it is carrier-preserving (`φin = φout = id`).

Its parametric edges — the evaluator's leaf agreement, fresh-name
injectivity, parameter-resolver injectivity, and straight-lineness of the lowered
program — are taken as hypotheses of the registered transport.
`hSL` is itself dischargeable (the lowered NTT program is all `extCall`s), but we
keep it as a hypothesis to mirror the printer theorem's interface faithfully. -/

/-- **Registered pass 3.** The printer-semantics preservation
    `JasminPrintSemCorrect.lowerComToProg_sem_eq` as a carrier-preserving map₁
    transport `(lowerLatticeToJasmin tgtCom).denote ↦ runProg leafSem
    (lowerLatticeToJasmin tgtCom)` along `(id, id)`.

    Parametric in the printer's honest edges — leaf agreement (`hLeaf`), fresh-name
    injectivity (`hInj`), parameter-resolver injectivity (`hPinj`), and
    straight-lineness of the emitted program (`hSL`) — threaded as hypotheses. -/
theorem regPass3_printer {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hSL : StraightLine (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)))
    (hPinj : ∀ (t t' : JasminTy)
                (v : Ctxt.Var (d := jasminDialect) ((LatticeDialect.inCtxt q n).map tau) t)
                (v' : Ctxt.Var (d := jasminDialect) ((LatticeDialect.inCtxt q n).map tau) t'),
                (paramsAndMap ((LatticeDialect.inCtxt q n).map tau)).2 t v
                  = (paramsAndMap ((LatticeDialect.inCtxt q n).map tau)).2 t' v' →
                (∃ h : t = t', h ▸ v = v')) :
    TransportSquare
      (g := fun V' : Ctxt.Valuation (d := jasminDialect) ((LatticeDialect.inCtxt q n).map tau) =>
              (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)).denote V')
      (φin := id) (φout := id)
      (f := fun V' => runProg leafSem (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)) V') :=
  ⟨fun V' => lowerComToProg_sem_eq hLeaf hInj
      (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)) hSL hPinj V'⟩

/-! ## 4. The derived three-pass chain (two iterated `comp`s, no hand `rw`)

`TransportSquare.comp` delivers the *pointwise* pasted equation; to
chain **three** passes we re-package each pasted pair back as a `TransportSquare`
(via `compSquare`, a thin wrapper over `comp`) so the result is itself composable.
The three-pass chain is then `(pass1 ⋆ pass2) ⋆ pass3` — two iterated pastes, each
adjacency `rfl`. -/

/-- **Square-valued composition.** Re-package the pointwise
    `TransportSquare.comp` as a `TransportSquare` over the *composed* transports
    `(φin₂ ∘ φin₁, φout₂ ∘ φout₁)`, so adjacent pastes chain (`compSquare` of
    `compSquare`).  This is the associative form the multi-pass registry needs;
    `comp` itself only yields the pointwise equation. -/
theorem compSquare {X Y X' Z W Y' : Type}
    {g : X → Y} {φin₁ : X → X'} {φout₁ : Y → Y'} {f₁ : X' → Y'}
    {g₂ : X' → Y'} {φin₂ : X' → Z} {φout₂ : Y' → W} {f₂ : Z → W}
    (S12 : TransportSquare g φin₁ φout₁ f₁)
    (S23 : TransportSquare g₂ φin₂ φout₂ f₂)
    (adj : f₁ = g₂) :
    TransportSquare g (φin₂ ∘ φin₁) (φout₂ ∘ φout₁) f₂ :=
  ⟨fun x => S12.comp S23 adj x⟩

/-- **Three-pass chain, derived by transport transitivity.** For the ML-KEM
    NTT-mul route, *running the emitted jasmin program* on the transported
    valuation computes the `transTy`-transport of the *source* `poly_mul`
    denotation — obtained by pasting **three** registered transport squares
    (optimizer ∘ lowering ∘ printer-semantics) with two iterated
    `TransportSquare.comp`, with **no** hand `rw`-chain over the three preservation
    lemmas.

    The two adjacencies are `rfl`: pass 2's abstract source *is* pass 1's realised
    target `(tgtCom).denote`, and pass 3's abstract source *is* pass 2's realised
    target `(lowerLatticeToJasmin tgtCom).denote`.  Passes 1 and 3 are
    carrier-preserving (`id, id`), pass 2 carrier-changing (`mapVal, transTy`); the
    composed input transport is therefore `mapVal` and the composed output
    transport `transTy`.

    Parametric in pass 3's printer edges (`hLeaf`/`hInj`/`hSL`/`hPinj`), threaded
    as explicit hypotheses. -/
theorem registryChain_threePass {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hSL : StraightLine (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)))
    (hPinj : ∀ (t t' : JasminTy)
                (v : Ctxt.Var (d := jasminDialect) ((LatticeDialect.inCtxt q n).map tau) t)
                (v' : Ctxt.Var (d := jasminDialect) ((LatticeDialect.inCtxt q n).map tau) t'),
                (paramsAndMap ((LatticeDialect.inCtxt q n).map tau)).2 t v
                  = (paramsAndMap ((LatticeDialect.inCtxt q n).map tau)).2 t' v' →
                (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    runProg leafSem (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)) (mapVal V)
      = transTy ((LatticeDialect.srcCom q n).denote V) :=
  -- (pass1 ⋆ pass2) gives `(lowerLatticeToJasmin tgtCom).denote (mapVal V)
  --   = transTy (srcCom.denote V)`; pasting pass3 (carrier-preserving) on top
  -- transports that across the printer semantics.  Both `adj`s are `rfl`; the
  -- composed `id ∘ (mapVal ∘ id)` / `id ∘ (transTy ∘ id)` transports reduce to
  -- `mapVal` / `transTy` by `id`/`∘` defeq.
  (compSquare (compSquare (regPass1_optimizer q n) (regPass2_lowering q n) rfl)
    (regPass3_printer q n hLeaf hInj hSL hPinj) rfl).square V

/-! ## 5. The chain refines the existing hand result

Dropping pass 3 — the first two passes of the *same* transitivity tree — is the
two-pass composition the pilot derived, which is *definitionally* the
hand-chained `CompilerCorrectness.latticeNttMul_compile_correct`.  So the
three-pass chain is a faithful **extension** (printer semantics appended) of the
hand result, not a weaker or differently-shaped corollary. -/

/-- **The two-pass head of the chain is the hand result.** Pasting only passes 1
    and 2 (the optimizer-rewrite ∘ A3-lowering head of `registryChain_threePass`'s
    transitivity tree) yields *definitionally* the hand-chained
    `CompilerCorrectness.latticeNttMul_compile_correct` — same statement, same
    type.  The registered two-pass composition therefore stands in for the
    manual `rw [tgtCom_denote_preserved_uncond, nttMul_rewrite_denote_eq]` chain,
    and the three-pass chain `registryChain_threePass` extends exactly this. -/
theorem registryChain_refines_handResult
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    ((regPass1_optimizer q n).comp (regPass2_lowering q n) rfl V)
      = CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectness.latticeNttMul_compile_correct
          q n V :=
  rfl

/-! ## 6. Straight-lineness of the lowered NTT program is dischargeable

The lone parametric edge of pass 3 that is purely structural (not a TCB
edge like leaf agreement or name injectivity) is `hSL`.  We discharge it: the
lowered ML-KEM NTT-mul program `lowerLatticeToJasmin (tgtCom q n)` is the four
`extCall` binders (`ntt a`, `ntt b`, `basemul`, `invntt`) closed by `ret` — none
is the aliasing `stackStore`, so it is straight-line.  This lets a caller drop
`hSL` from `registryChain_threePass`, leaving only the printer-TCB edges
(`hLeaf`/`hInj`/`hPinj`). -/

/-- **The lowered NTT program is straight-line.** Every binder of
    `lowerLatticeToJasmin (tgtCom q n)` is an `extCall` (the four NTT-domain ops),
    never the aliasing `stackStore`, so `StraightLine` holds.  Discharges the
    `hSL` edge of `regPass3_printer` / `registryChain_threePass`. -/
theorem lowered_tgtCom_straightLine :
    StraightLine (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)) := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
    (intro w m; simp [LatticeToJasmin.lowerExpr, LatticeToJasmin.jasminOpOf])

/-- **Three-pass chain, `hSL` discharged.** `registryChain_threePass` with the
    straight-line edge supplied by `lowered_tgtCom_straightLine`, leaving only the
    printer-TCB edges (`hLeaf`/`hInj`/`hPinj`). -/
theorem registryChain_threePass' {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : JasminTy)
                (v : Ctxt.Var (d := jasminDialect) ((LatticeDialect.inCtxt q n).map tau) t)
                (v' : Ctxt.Var (d := jasminDialect) ((LatticeDialect.inCtxt q n).map tau) t'),
                (paramsAndMap ((LatticeDialect.inCtxt q n).map tau)).2 t v
                  = (paramsAndMap ((LatticeDialect.inCtxt q n).map tau)).2 t' v' →
                (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (LatticeDialect.inCtxt q n)) :
    runProg leafSem (lowerLatticeToJasmin (LatticeDialect.tgtCom q n)) (mapVal V)
      = transTy ((LatticeDialect.srcCom q n).denote V) :=
  registryChain_threePass q n hLeaf hInj (lowered_tgtCom_straightLine q n) hPinj V

end CatCrypt.Crypto.SecureCompilation.VIR.CompilerLoweringRegistry
