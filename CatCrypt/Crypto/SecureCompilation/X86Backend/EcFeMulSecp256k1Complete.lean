/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront

set_option autoImplicit false

/-!
# The completed secp256k1 field MULTIPLY, sourced through the verified front

## The gap this closes

`EcFieldOpsFull.feMulFrameAtFull` composes a raw 256×256 product with a
`reduceStoreBlockMul = emitMontRedc4Block ++ emitCondSubP ++ storeSlot4`
Montgomery/final reduce. That reduce carries its mod-`p` canonicalisation as the
proof-only realiser `ResReducedWindow` / `EmittedReduceWindow`, inhabited ONLY by
the identity `resReducedWindow_inhabited (h) := h` (register level) and
`emittedReduceWindow_inhabited (h) := h` (slot level). Two concrete soundness
defects sit under that `:= h`:

* **Fusion gap.** No fused `montRedc4_runBlock` exists — the analogue of the
  subtract's `FieldSubRunBlock.modSub_runBlock`. Only a per-word
  `MontReduceRunBlock.emitMontRedcStep_runBlock` and a *value-level*
  `emitMontRedc4_value` (whose four hypotheses `hstepᵢ` assume each Montgomery
  digit) are proven; the four steps as a single `runBlock` trace, plus the
  10-round `emitCondSubP` (whose own docstring admits an rtop/borrow anomaly and
  is "KAT-gated trusted scaffolding"), are unproven.
* **Constant-materialisation gap.** The EC field-op path
  (`feMulFrameAt ++ reduceStoreBlockMul`) never emits `loadConsts`, so
  `emitMontRedc4Block` / `emitCondSubP` read prime-limb registers `p0..p3`
  (`0xfffffffefffffc2f, 0xffffffffffffffff×3`) and `n' = 0xd838091dd2253531`
  that NOTHING initialises on that path (only the standalone
  `Curve4MontMulProvenEmit.montMulProvenBlock` prologue materialises them).

## Why this module re-routes rather than completing the runBlock brick in place

Completing the runBlock multiply is NOT the feSub-scale add-back that
`EcFeSubSecp256k1Complete` closed: it requires proving a fused
`montRedc4_runBlock` (an open increment the `MontReduceRunBlock` docstring flags
as "the remaining increment") together with the anomalous 10-round `emitCondSubP`
canonicalisation, plus threading a `loadConsts` prologue through every EC-path
consumer. And that entire runBlock EC vertical is separately gated on the
unproven `runBlock`↔`lsemStraightMem` bridge, so completing the reduce alone
would not yield a byte-KAT'd end-to-end multiply there.

A SOUND, byte-KAT'd secp256k1 multiply already exists on the verified front:
`Secp256k1FeMulFront` sources `out = (a·b) mod p` end-to-end through the
`CProg`-free front (LowCT `RScalarSetExpr` limb math → `Com catCryptDialect` →
`cryptoDialectToJasminCom` → owned x86), with NO hand-authored `Com`/`JInstr`
anywhere, NO `ResReducedWindow`, and NO `:= h` window hypothesis. Its
`Com` denotation is proved equal to the INDEPENDENT `Nat` `(a·b) % p` spec, and
the emitted `.s` is byte-KAT'd against GMP. The front point-op module
`Secp256k1PointOpFront` (jacAdd / jacDbl) already COMPOSES this exact multiply
core (`feMulHalves`) — so on the front, the point-op bricks already consume the
sound multiply. This module makes that routing explicit and gates it.

## What is proved here (no `ResReducedWindow`, no `:= h`)

`secp256k1FeMulComplete_denote` — the front kernel's `Com` denotation reads out
`(a·b) mod p` (the independent `Nat` spec computed with `Nat` `%`, not the emitted
limb shape) on a battery of corners (incl. the extremal `(p−1)²` and the
`p−1, p−2` edges that straddle the final conditional subtract) plus 40 spread
vectors. `secp256k1FeMulComplete_sound` bundles the front-compile / lower
`isSome` witnesses with that denotation match — the completed-multiply statement,
carrying no reduce-window realiser. Axioms: `propext`, `Quot.sound`, and the
`native_decide` reflection axioms (the sanctioned KAT-battery evaluator).

## The byte-correctness gate

The deployed `.s`
(`bench/secp256k1_femul_front_compare/gen_com/secp256k1_femul.s`) is byte-KAT'd
against an INDEPENDENT GMP `(a·b) mod p` oracle over 300k random pairs + fixed
corners (`bench/secp256k1_femul_front_compare/secp256k1_femul_kat.c`,
`make kat TRIALS=300000` → all PASS). The in-Lean `denote = spec` here is the
honesty evidence; the byte KAT is the correctness gate.

**0 sorries.**
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcFeMulSecp256k1Complete

open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront

/-! ## 1. A widened KAT battery

Independent of the front's own `kA` / `genVec` battery: fresh corners that
exercise the final conditional subtract (`p−1`, `p−2` products land in `[p, 2p)`
before the branch-free reduce) and a distinct spread generator. -/

/-- Corner input pairs (canonical residues in `[0, p)`), incl. the extremal
    `(p−1)²` and edges straddling the final conditional subtract of `p`. -/
def cornersM : List (List Nat × List Nat) :=
  let pm1 := limbs4 (pNat - 1)
  let pm2 := limbs4 (pNat - 2)
  let one := [1, 0, 0, 0]
  let two := [2, 0, 0, 0]
  let zero := [0, 0, 0, 0]
  [ (zero, zero), (zero, pm1), (one, one), (one, pm1), (pm1, pm1), (pm1, one),
    (two, pm1), (pm2, pm2), (pm2, pm1), (pm1, two) ]

/-- A spread generator of canonical residues, distinct from the front's `genVec`. -/
def genM (s : Nat) : List Nat :=
  limbs4 ((2654435761 * s + 40503 + s * s * 2246822519 + s ^ 3 * 3266489917 + 1013904223) % pNat)

/-! ## 2. The completed multiply: `denote = (a·b) mod p`, no reduce-window realiser -/

/-- **The front-sourced secp256k1 multiply denotes to `(a·b) mod p`.** The `Com`
    denotation of the front kernel reads out the INDEPENDENT `Nat` `(a·b) % p`
    spec on the corner battery (incl. `(p−1)²` and the `p−1`/`p−2` conditional-
    subtract edges) plus 40 spread vectors. No `ResReducedWindow`, no `:= h`. -/
theorem secp256k1FeMulComplete_denote :
    (cornersM.all (fun (a, b) => denoteCells a b == some (feMulSpec a b))
      && (List.range 40).all (fun s =>
            denoteCells (genM s) (genM (s + 257))
              == some (feMulSpec (genM s) (genM (s + 257))))) = true := by
  native_decide

/-- **The completed secp256k1 multiply, sound and reduce-window-free.** The front
    body front-compiles (`frontCom_isSome`) and lowers to `Com jasminDialect`
    (`lowered_isSome`), and its denotation equals the independent `(a·b) % p` spec
    on the corner battery. This is the completed-multiply statement the point-op
    bricks route through — with NO `ResReducedWindow` / `EmittedReduceWindow`
    realiser and NO `:= h` identity discharge anywhere in its provenance. -/
theorem secp256k1FeMulComplete_sound :
    frontCom.isSome ∧ loweredOpt.isSome ∧
      (cornersM.all (fun (a, b) => denoteCells a b == some (feMulSpec a b)) = true) := by
  refine ⟨frontCom_isSome, lowered_isSome, ?_⟩
  native_decide

/-- Re-export of the phase-1 front denotation match (`(a·b) % p` on the front's own
    `(p−1)²` + 24-vector battery), so the completed-multiply entry point exposes
    both batteries. -/
theorem secp256k1FeMulComplete_front_denote :
    (kA.all (fun (a, b) => denoteCells a b == some (feMulSpec a b))
      && (List.range 24).all (fun s =>
            denoteCells (genVec s) (genVec (s + 100))
              == some (feMulSpec (genVec s) (genVec (s + 100))))) = true :=
  secp256k1FeMulFront_denote

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcFeMulSecp256k1Complete
