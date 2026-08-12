/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# Per-op property structures for `CatCryptOp`

Mirrors VEIR's `Veir/Properties.lean` shape — one struct per family of ops
that shares non-trivial semantic flags. Lets the eventual `propertiesOf :
CatCryptOp → Type` (Track 2b) dispatch per op without inflating the `Op`
enum itself.

Crypto-specific (vs. VEIR's LLVM-style `nsw`/`nuw`/`exact`/`disjoint`):

* `ConstantTimeProperties` — op preserves timing-channel safety
* `PureProperties` — op has no SPComp side effects (sampling, memref store)
* `LinearProperties` — op is linear over a masking sharing (XOR-share friendly)
* `OverflowProperties` — BitVec wrap semantics; informative since CryptoSSA
  is wrap-by-default (mod 2^n) but downstream lowering may need to flag
  which wraps are *intended* vs. *exploited*.

Each struct has trivial constructors today; flags will be enriched as
peephole passes need them.

See [Veir/Properties.lean](https://github.com/opencompl/veir/blob/main/Veir/Properties.lean)
for the upstream pattern. VEIR-DIFF: their attrs are parsed from MLIR
`DictionaryAttr`; we author flags structurally since CatCrypt programs
originate in Lean.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.CatCryptOpProperties

open CatCryptDialect

/-! ## Constant-time properties -/

/-- `ConstantTimeProperties` is the **statement** that an op is CT-preserving:
    its timing is independent of any data-dependent value (no data-dependent
    branch, no data-dependent memory index). `CatCryptOp.propertiesOf`
    (`CatCryptOpInfo.lean`) selects it per op.

    The fields are declarative flags with all-true defaults, not proofs: this
    structure records an intent, it does not discharge it. The proved
    VIR-level CT obligations live in `CTPredicate.lean`. -/
structure ConstantTimeProperties where
  /-- Op cannot leak data through control flow. -/
  noDataDependentBranch : Bool := true
  /-- Op cannot leak data through memory index choice. -/
  noDataDependentMemIndex : Bool := true
deriving Inhabited, Repr, DecidableEq

/-! ## Purity properties -/

/-- `PureProperties op` is the statement that `op` is a pure function:
    no sampling, no observable state effect. CryptoSSA-level `isPure`
    lifts here. -/
structure PureProperties where
  /-- True iff op has no `SPComp.sample` in its denotation. -/
  noSampling : Bool := true
  /-- True iff op is a pure function (no heap, no store). -/
  isFunctional : Bool := true
deriving Inhabited, Repr, DecidableEq

/-! ## Masking-linear properties -/

/-- `LinearProperties op` is the statement that `op` is linear over a
    masking sharing (preserves XOR-share invariants under rewrites).
    Used by Track 3c (masking-preservation pass). -/
structure LinearProperties where
  /-- Op commutes with `⊕`-masking of operands. -/
  xorShareCommuting : Bool := true
deriving Inhabited, Repr, DecidableEq

/-! ## BitVec overflow properties -/

/-- `OverflowProperties op` reports the semantic intent of wrap behavior.
    CryptoSSA's BitVec arithmetic is *always* `mod 2^n`; this flag
    distinguishes "wrap is the spec" (e.g. ChaCha20 quarter-round) from
    "wrap would be UB in the source language" (e.g. Rust signed add).

    VEIR's `NswNuwProperties` covers the LLVM-side analogue. -/
structure OverflowProperties where
  /-- True iff the source language treats wrap as defined behavior. -/
  wrapsAreDefined : Bool := true
  /-- True iff this op may invoke UB when its result wraps (rare in
      crypto code; flagged for completeness). -/
  wrapIsUB : Bool := false
deriving Inhabited, Repr, DecidableEq

/-! ## Default instances per family -/

/-- Default: all-true CT-safe properties. -/
def defaultCT : ConstantTimeProperties := {}

/-- Default: pure + functional. -/
def defaultPure : PureProperties := {}

/-- Default: XOR-linear. -/
def defaultLinear : LinearProperties := {}

/-- Default: wrap-defined, never UB. CryptoSSA's BitVec arithmetic. -/
def defaultOverflow : OverflowProperties := {}

end CatCrypt.Crypto.SecureCompilation.VIR.CatCryptOpProperties
