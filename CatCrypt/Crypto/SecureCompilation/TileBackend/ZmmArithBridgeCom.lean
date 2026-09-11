/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# The ZMM packed-arithmetic bridge on the UNIFIED `Com jasminDialect`

`ZmmArithBridge.lean` consolidates the bespoke AVX-512 ZMM machine
(`Avx512Model`'s `ZInstr` / `ZState`) onto the shape-generic `Tile 8 64` lane
model. This module is the SIMD-dialect-unification companion: it re-expresses
the bridge's packed two-operand arithmetic core directly as `Com jasminDialect`
programs over `reg 512` ZMM registers, off the bespoke `Avx512Model` machine,
using the verified dialect's `JasminOp.vpackZMM (bop)` op (denote `zmmPackQ bop`,
the carry-free 8×u64 packed-lane op). This mirrors `ButterflyBlockCom.lean` and
`Poseidon2Avx512Jasmin.lean`, which route the same `vpackZMM` ops through the
`JasminPrint` / `JasminPrintSemCorrect` chain to AT&T `.s`.

## Which `ZInstr` ops migrate

`ZmmArithBridge.lean`'s `zinstToReg` maps the cleanly-corresponding two-operand
packed arithmetic onto the `regArith` binop alphabet. Each of those ops is a
carry-free 8×u64 packed-lane op, so it maps EXACTLY onto a `vpackZMM bop`:

| `ZInstr`   | lane op (`Avx512Model`) | `JasminBinOp` | denote        |
|------------|-------------------------|---------------|---------------|
| `vpaddq`   | `laneAddQ a b = a + b`   | `.add`        | `zmmPackQ .add` |
| `vpsubq`   | `laneSubQ a b = a - b`   | `.sub`        | `zmmPackQ .sub` |
| `vpmullq`  | `laneMullq a b = a * b`  | `.mul`        | `zmmPackQ .mul` |
| `vpandq`   | `laneAndQ a b = a &&& b` | `.and`        | `zmmPackQ .and` |
| `vporq`    | `laneOrQ a b  = a ||| b` | `.or`         | `zmmPackQ .or`  |
| `vpxorq`   | `laneXorQ a b = a ^^^ b` | `.xor`        | `zmmPackQ .xor` |

These six are exactly the `zinstToReg`-mapped subset of the bridge. They migrate
in full to `Com jasminDialect` here.

The verified dialect additionally carries `.shl` / `.shr` packed shifts, whose
`vpackZMM` semantics is the per-lane shift by that lane's count of the second
register (`a.qword[j] <<< b.qword[j].toNat`). That is exactly the
`Avx512Model` per-lane VARIABLE shift `laneSllvQ` / `laneSrlvQ` (the
`vpsllvq` / `vpsrlvq` ops), so those two cross-register variable shifts ALSO
migrate (they are register-amount shifts, not the `ZInstr` immediate shifts).
The immediate shifts (`vpsllq` / `vpsrlq` / `vpsraq`) take a compile-time `Nat`
count, not a second register, so they sit outside the two-register `vpackZMM`
alphabet — see the module-tail report and `ZmmArithBridge.lean` for the
non-migrating ops.

## What is proved here

For each migrated op a `Com jasminDialect` program over the input context
`[a, b]` (two `reg 512`) whose single binding is the matching `vpackZMM bop`,
plus a `rfl`-denote lemma pinning its denotation to `zmmPackQ bop a b` — the
verified-dialect packed-lane op the bespoke `ZInstr` computes lane-by-lane. The
denote lemmas elaborate by `rfl`: `Com.denote` of a one-binding straight-line
program unfolds definitionally through the `vpackZMM` denote arm to the
`zmmPackQ` call.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridgeCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridgeCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Register type and the two-input context

A single `reg 512` (one ZMM 8×u64 lane-vector) is the working type. Each packed
two-operand op consumes two of them, in de-Bruijn order `[a, b]`:

* `a` — first source (de Bruijn `0`, `.here`);
* `b` — second source (de Bruijn `1`, `.there .here`). -/

/-- The `reg 512` dialect type (one ZMM 8×u64 lane-vector), abbreviated. -/
abbrev r512 : JasminTy := .reg 512

/-- The two-input context of a packed ZMM binop: `[a, b]`, each `reg 512`. -/
abbrev binCtx : Ctxt jasminDialect := [r512, r512]

/-! ## 2. The dialect-native packed-arithmetic programs `Com jasminDialect`

```
let r = vpackZMM bop a b      -- r := bop-packed(a, b)
ret r
```

The single binding (`vpackZMM bop`) consumes `a` (`.here` in `binCtx`) and `b`
(`.there .here`), producing `r` at the front; the program returns it (`.here` in
the extended context `[r, a, b]`). One generic builder instantiates all six
two-operand ops. -/

/-- Generic one-op packed ZMM program: `r := bop-packed(a, b); ret r`, over the
    two-input context `[a, b]`. The dialect-native equivalent of one bespoke
    `ZInstr` packed-arithmetic op. -/
def packBinCom (bop : JasminBinOp) : Com jasminDialect binCtx r512 :=
  -- r := vpackZMM bop a b   (a = .here, b = .there .here)
  .var (.mk (.vpackZMM bop) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The migrated `vpaddq` op as a `Com jasminDialect`: packed 8×u64 add. -/
def vpaddqCom : Com jasminDialect binCtx r512 := packBinCom .add

/-- The migrated `vpsubq` op as a `Com jasminDialect`: packed 8×u64 subtract. -/
def vpsubqCom : Com jasminDialect binCtx r512 := packBinCom .sub

/-- The migrated `vpmullq` op as a `Com jasminDialect`: packed low-64 multiply. -/
def vpmullqCom : Com jasminDialect binCtx r512 := packBinCom .mul

/-- The migrated `vpandq` op as a `Com jasminDialect`: packed 8×u64 bitwise and. -/
def vpandqCom : Com jasminDialect binCtx r512 := packBinCom .and

/-- The migrated `vporq` op as a `Com jasminDialect`: packed 8×u64 bitwise or. -/
def vporqCom : Com jasminDialect binCtx r512 := packBinCom .or

/-- The migrated `vpxorq` op as a `Com jasminDialect`: packed 8×u64 bitwise xor. -/
def vpxorqCom : Com jasminDialect binCtx r512 := packBinCom .xor

/-! ## 3. Denotation characterization

Each program computes the verified-dialect packed-lane op `zmmPackQ bop`, with
`zmmPackQ` the 8×u64 packed-lane semantics (`= zmmOfLanes (lane-wise bop)`). The
proofs are `rfl`: `Com.denote` of the one-binding program unfolds definitionally
through the `vpackZMM` denote arm to the `zmmPackQ` call. -/

/-- **Generic packed-binop denotation pin.** On any input valuation `⟨a, b⟩`,
    `packBinCom bop` denotes to `zmmPackQ bop a b` — the verified-dialect packed
    8×u64 op the matching bespoke `ZInstr` computes lane-by-lane. -/
theorem packBinCom_denote (bop : JasminBinOp) (a b : BitVec 512) :
    (packBinCom bop).denote (.cons a (.cons b .nil)) = zmmPackQ bop a b :=
  rfl

/-- `vpaddqCom` denotes to `zmmPackQ .add a b` — packed 8×u64 add (the bespoke
    `evalZInstr (.vpaddq …)` via `laneAddQ`). -/
theorem vpaddqCom_denote (a b : BitVec 512) :
    vpaddqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .add a b := rfl

/-- `vpsubqCom` denotes to `zmmPackQ .sub a b` — packed 8×u64 subtract. -/
theorem vpsubqCom_denote (a b : BitVec 512) :
    vpsubqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .sub a b := rfl

/-- `vpmullqCom` denotes to `zmmPackQ .mul a b` — packed low-64 multiply. -/
theorem vpmullqCom_denote (a b : BitVec 512) :
    vpmullqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .mul a b := rfl

/-- `vpandqCom` denotes to `zmmPackQ .and a b` — packed 8×u64 bitwise and. -/
theorem vpandqCom_denote (a b : BitVec 512) :
    vpandqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .and a b := rfl

/-- `vporqCom` denotes to `zmmPackQ .or a b` — packed 8×u64 bitwise or. -/
theorem vporqCom_denote (a b : BitVec 512) :
    vporqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .or a b := rfl

/-- `vpxorqCom` denotes to `zmmPackQ .xor a b` — packed 8×u64 bitwise xor. -/
theorem vpxorqCom_denote (a b : BitVec 512) :
    vpxorqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .xor a b := rfl

/-! ## 4. The migrated arithmetic core, packaged

All six `zinstToReg`-mapped packed ops of `ZmmArithBridge.lean` realized as
`Com jasminDialect` programs whose denotations are the verified-dialect
`zmmPackQ` packed-lane ops. This is the dialect-native form of the bridge's
two-operand arithmetic core: the same packed `a + b`, `a − b`, `a · b`,
`a ∧ b`, `a ∨ b`, `a ⊕ b` the bespoke `ZState` machine computes lane-by-lane,
with no re-proof of the lane math (reuses `zmmPackQ`). -/

/-- **The migrated ZMM arithmetic core.** The six bridge-mapped packed ops are
    each realized as a `Com jasminDialect` whose denotation is the corresponding
    verified-dialect `zmmPackQ` op — the SIMD-dialect-unification image of
    `ZmmArithBridge.lean`'s two-operand arithmetic subset. -/
theorem zmmArithCore_realized (a b : BitVec 512) :
    vpaddqCom.denote  (.cons a (.cons b .nil)) = zmmPackQ .add a b ∧
    vpsubqCom.denote  (.cons a (.cons b .nil)) = zmmPackQ .sub a b ∧
    vpmullqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .mul a b ∧
    vpandqCom.denote  (.cons a (.cons b .nil)) = zmmPackQ .and a b ∧
    vporqCom.denote   (.cons a (.cons b .nil)) = zmmPackQ .or  a b ∧
    vpxorqCom.denote  (.cons a (.cons b .nil)) = zmmPackQ .xor a b :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5. The variable cross-register shifts also migrate

The verified dialect's `.shl` / `.shr` arms (`JasminBinOp.apply`:
`a <<< b.toNat` / `a >>> b.toNat`) lift through `vpackZMM` to a per-lane shift by
that lane's count of the second register — `zmmPackQ .shl a b` has lane `k`
equal to `(zmmLane a k) <<< (zmmLane b k).toNat`. That is exactly the bespoke
`Avx512Model` per-lane VARIABLE shift `laneSllvQ a sh = a <<< sh.toNat` /
`laneSrlvQ a sh = a >>> sh.toNat` (the `vpsllvq` / `vpsrlvq` ops), so those two
register-amount shifts migrate too. (The `ZInstr` IMMEDIATE shifts `vpsllq` /
`vpsrlq` / `vpsraq` take a compile-time `Nat`, not a second register, so they are
NOT in this two-register alphabet.) -/

/-- The migrated `vpsllvq` op (variable left shift) as a `Com jasminDialect`:
    per-lane `a.qword[k] <<< b.qword[k].toNat`. -/
def vpsllvqCom : Com jasminDialect binCtx r512 := packBinCom .shl

/-- The migrated `vpsrlvq` op (variable right shift) as a `Com jasminDialect`:
    per-lane `a.qword[k] >>> b.qword[k].toNat`. -/
def vpsrlvqCom : Com jasminDialect binCtx r512 := packBinCom .shr

/-- `vpsllvqCom` denotes to `zmmPackQ .shl a b` — the per-lane variable left
    shift the bespoke `evalZInstr (.vpsllvq …)` computes via `laneSllvQ`. -/
theorem vpsllvqCom_denote (a b : BitVec 512) :
    vpsllvqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .shl a b := rfl

/-- `vpsrlvqCom` denotes to `zmmPackQ .shr a b` — the per-lane variable right
    shift the bespoke `evalZInstr (.vpsrlvq …)` computes via `laneSrlvQ`. -/
theorem vpsrlvqCom_denote (a b : BitVec 512) :
    vpsrlvqCom.denote (.cons a (.cons b .nil)) = zmmPackQ .shr a b := rfl

end CatCrypt.Crypto.SecureCompilation.TileBackend.ZmmArithBridgeCom
