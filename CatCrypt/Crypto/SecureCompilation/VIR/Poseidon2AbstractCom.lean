/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec

/-!
# Abstract Poseidon2-round ties for the unified-`Com` AVX-512 realization (model-free)

`Poseidon2Avx512Jasmin.lean` routed **one** Poseidon2 AVX-512 lane op — the MDS /
round-constant linear-layer add (`#VPADD_8u64`) — through the verified jasmin
chain and pinned its 8 lanes to the abstract `Poseidon2LaneVec.padd`. Its sibling
bespoke realizations (`Poseidon2Realization.lean`,
`Poseidon2RoundRealization.lean`) carry the rest of the round — the S-box
`x ↦ x⁵`, the RC-add, the MDS mul-add — only as `runZBlock`-level *structural*
realizations over the bespoke `Avx512Model` (`ZInstr`/`ZState`/`runZBlock`)
machine, against bespoke `sboxSpec`/`addRcSpec`/`mds2Spec` lane formulas. They
never tie those round components to the abstract `Poseidon2LaneVec` lane spec on
the **verified** `Com jasminDialect` denotation.

This module is the **equal-strength abstract successor** for the three round
components, re-anchored onto the unified `Com jasminDialect` `zmmPackQ`
denotation, with no dependence on the bespoke `Avx512Model`: each component is a
straight-line `Com jasminDialect` over the carry-free `vpackZMM` alphabet, its
denotation is pinned to `zmmPackQ`, and the abstract Poseidon2 lane tie is proved
per sub-lane through `zmmLane`/`zmmPackQ_lane`.

## The carry-free `vpackZMM` alphabet covers the round components

| Poseidon2 round step | lane formula | `vpackZMM` arms | new op? |
|---|---|---|---|
| RC-add / linear layer | `padd a rc = a + rc` | `.add` | no |
| S-box `x⁵` | `x·x·x·x·x` | `.mul` (×4) | no |
| MDS mul-add | `pmul a m + b` | `.mul`, `.add` | no |

The unified `JasminBinOp` already carries `.mul` (`zmmPackQ .mul` = the
`#VPMULL_8u64` packed lane multiply, `JasminBinOp.apply .mul = (· * ·)`), so the
S-box `x⁵` is a four-`vpackZMM .mul` chain over the 8 `u64` lanes — exactly the
abstract `Poseidon2LaneVec` `mul`-chain `x²·x²·x`. The RC-add and the MDS combine
ride the same `.add`/`.mul` arms. No `vpermq` cross-lane permute and no new
`SimdOp`/`JInstr` op appears.

## What is proved (the abstract Poseidon2-round ties)

* `rcAddCom_lane_eq_padd` — lane `k` of `rcAddCom`'s denotation equals the
  abstract `Poseidon2LaneVec.padd` of the two input lanes (`a + rc`).
* `sboxCom_lane_eq_x5` — lane `k` of `sboxCom`'s denotation (the four-`.mul` chain)
  equals the abstract S-box `x⁵` of the input lane, in the `x·x·x·x·x` lane form
  the proven `Poseidon2LaneVec.sbox_via_dialect_mul_chain` / `poseidon2_sbox_lane_map`
  use.
* `mdsMulAddCom_lane_eq_pmul_padd` — lane `k` of `mdsMulAddCom`'s denotation equals
  `padd (pmul a m) b` — the MDS weighted accumulate of the lane.
* `poseidon2RoundCom_eq_abstract` — the conjunction, packaged as the equal-strength
  abstract successor of the bespoke `Poseidon2RoundRealization` structural
  realizations, now stated against the abstract `Poseidon2LaneVec` lane spec on the
  unified `Com` denotation.

There is no `runZBlock` / `ZInstr` / `ZState` / `jasminc` / `jasminc_preserves_ct`
in any theorem's `#print axioms`: the tie is between the verified
`Com jasminDialect` denotation and the abstract `Poseidon2LaneVec` lane spec.

## The field domain — Scope

The abstract lane defs are the model-free `Poseidon2LaneVec.padd`/`pmul`
(64-bit lane add / multiply, the un-reduced products before the Barrett fold).
For **BabyBear** (`P = 2³¹ − 2²⁷ + 1 < 2³¹`), residues are `< 2³¹`, so the
64-bit lane multiply computes the **exact** product of two residues (no overflow)
— the same regime the bespoke `Poseidon2Realization` is built for. The
per-multiply Montgomery/Barrett reduction is supplied by the same packed-REDC
kernels (`MlkemMontRedcAbstractCom` etc.); this file re-anchors the round's
*algebraic* lane steps (RC-add, `x⁵`, MDS mul-add), not the reduction.

## References
* Grassi, Khovratovich, Roy, Rechberger, Schofnegger — *Poseidon2* (2023).

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2AbstractCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2AbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec (padd pmul)

/-! ## 1. The RC-add / linear-layer step `rc = a + rc` (one `vpackZMM .add`)

The Poseidon2 round-constant add (and, lane-bundled, the linear-layer pointwise
add) is a single packed lane add — the abstract `Poseidon2LaneVec.padd`. Mirrors
the bespoke `addRcBlock`'s one `vpaddq`, on the unified `Com`. -/

/-- The RC-add input context `[a, rc]`, each `reg 512`: the state lane register and
    the broadcast round-constant register. -/
abbrev rcAddCtx : Ctxt jasminDialect := [r512, r512]

/-- The migrated Poseidon2 RC-add / linear-layer step as a `Com jasminDialect` over
    `reg 512` registers — the dialect-native equivalent of the bespoke
    `addRcBlock`: `rc = a + rc`, a single `vpackZMM .add` (8×u64 packed add, the
    `#VPADD_8u64` image). -/
def rcAddCom : Com jasminDialect rcAddCtx r512 :=
  -- out := a + rc   (a = .here, rc = .there .here)
  .var (.mk (.vpackZMM .add) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- **RC-add denotation pin.** On any valuation `⟨a, rc⟩`, `rcAddCom` denotes to
    `zmmPackQ .add a rc` — the verified-dialect packed `a + rc`. -/
theorem rcAddCom_denote (a rc : BitVec 512) :
    rcAddCom.denote (.cons a (.cons rc .nil))
      = zmmPackQ .add a rc := by
  rw [rcAddCom, denote_var_vpackZMM]
  rfl

/-- **RC-add abstract tie (per sub-lane).** Lane `k` of `rcAddCom`'s denotation,
    fed the state-lane register `a` and the round-constant register `rc`, equals
    `Poseidon2LaneVec.padd (zmmLane a k) (zmmLane rc k)` — the abstract Poseidon2
    per-lane RC-add `a + rc`. Abstract successor of the bespoke `addRcBlock_realizes`. -/
theorem rcAddCom_lane_eq_padd (a rc : BitVec 512) (k : Fin 8) :
    zmmLane (rcAddCom.denote (.cons a (.cons rc .nil))) k
      = padd (zmmLane a k) (zmmLane rc k) := by
  rw [rcAddCom_denote, zmmPackQ_lane]
  rfl

/-! ## 2. The S-box `x ↦ x⁵` as a four-`vpackZMM .mul` chain

`x⁵ = ((x·x)·(x·x))·x`. Each `·` is a packed `vpackZMM .mul` (the `#VPMULL_8u64`
lane multiply). Mirrors the bespoke S-box `x⁵` 3-multiply chain
(`Poseidon2Realization.sboxBlock`) and the abstract
`Poseidon2LaneVec.sbox_via_dialect_mul_chain`, on the unified `Com`. -/

/-- The S-box input context `[x]`, a single `reg 512` state lane register. -/
abbrev sboxCtx : Ctxt jasminDialect := [r512]

/-- The migrated Poseidon2 S-box `x ↦ x⁵` as a `Com jasminDialect` over one
    `reg 512` register: the `mul`-chain `x² = x·x`, `x⁴ = x²·x²`, `x⁵ = x⁴·x`,
    each a `vpackZMM .mul`. The dialect-native equivalent of the bespoke
    `sboxBlock` 3-multiply chain. -/
def sboxCom : Com jasminDialect sboxCtx r512 :=
  -- x2 := x · x      (x = .here)
  .var (.mk (.vpackZMM .mul) rfl
          (.cons .here (.cons .here .nil)))
    -- x4 := x2 · x2  (under [x2, x]: x2 = .here)
    (.var (.mk (.vpackZMM .mul) rfl
            (.cons .here (.cons .here .nil)))
      -- x5 := x4 · x  (under [x4, x2, x]: x4 = .here, x = .there (.there .here))
      (.var (.mk (.vpackZMM .mul) rfl
              (.cons .here (.cons (.there (.there .here)) .nil)))
        (.ret .here)))

/-- **S-box denotation pin.** On any valuation `⟨x⟩`, `sboxCom` denotes to
    `zmmPackQ .mul (zmmPackQ .mul (zmmPackQ .mul x x) (zmmPackQ .mul x x)) x` —
    the verified-dialect packed `x²·x²·x = x⁵`. -/
theorem sboxCom_denote (x : BitVec 512) :
    sboxCom.denote (.cons x .nil)
      = zmmPackQ .mul (zmmPackQ .mul (zmmPackQ .mul x x) (zmmPackQ .mul x x)) x := by
  rw [sboxCom, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- **S-box abstract tie (per sub-lane).** Lane `k` of `sboxCom`'s denotation, fed
    the state-lane register `x`, equals the abstract Poseidon2 S-box `x⁵` of the
    input lane, in the `x·x·x·x·x` lane form the proven
    `Poseidon2LaneVec.sbox_via_dialect_mul_chain` /
    `Poseidon2LaneVec.poseidon2_sbox_lane_map` use (per-lane
    independence). Abstract successor of the bespoke `sboxBlock_realizes`. -/
theorem sboxCom_lane_eq_x5 (x : BitVec 512) (k : Fin 8) :
    zmmLane (sboxCom.denote (.cons x .nil)) k
      = (let a := zmmLane x k; a * a * a * a * a) := by
  rw [sboxCom_denote]
  simp only [zmmPackQ_lane, JasminBinOp.applyLane]
  -- the chain is `(x·x)·(x·x)·x`; the abstract S-box is `x·x·x·x·x` — same up to
  -- associativity of the lane multiply.
  simp only [mul_assoc]

/-! ## 3. The MDS mul-add term `mds = (a · m) + b` (one `.mul`, one `.add`)

A single MDS weighted accumulate over two lanes: weight `a` by `m`, add `b`. Two
`vpackZMM` ops (`.mul` then `.add`). Mirrors the bespoke `mds2Block` /
`mdsCombineBlock` weighted accumulate, over the abstract `Poseidon2LaneVec`
`pmul`/`padd`. -/

/-- The MDS mul-add input context `[a, m, b]`, each `reg 512`: the weighted lane
    `a`, the MDS weight `m`, the accumulator lane `b`. -/
abbrev mdsMulAddCtx : Ctxt jasminDialect := [r512, r512, r512]

/-- The migrated Poseidon2 MDS mul-add term as a `Com jasminDialect` over `reg 512`
    registers: `mds = (a · m) + b`, one `vpackZMM .mul` then one `vpackZMM .add`. -/
def mdsMulAddCom : Com jasminDialect mdsMulAddCtx r512 :=
  -- am := a · m   (a = .here, m = .there .here)
  .var (.mk (.vpackZMM .mul) rfl
          (.cons .here (.cons (.there .here) .nil)))
    -- out := am + b   (under [am, a, m, b]: am = .here, b = .there (.there (.there .here)))
    (.var (.mk (.vpackZMM .add) rfl
            (.cons .here (.cons (.there (.there (.there .here))) .nil)))
      (.ret .here))

/-- **MDS mul-add denotation pin.** On any valuation `⟨a, m, b⟩`, `mdsMulAddCom`
    denotes to `zmmPackQ .add (zmmPackQ .mul a m) b` — the verified-dialect packed
    `(a · m) + b`. -/
theorem mdsMulAddCom_denote (a m b : BitVec 512) :
    mdsMulAddCom.denote (.cons a (.cons m (.cons b .nil)))
      = zmmPackQ .add (zmmPackQ .mul a m) b := by
  rw [mdsMulAddCom, denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- **MDS mul-add abstract tie (per sub-lane).** Lane `k` of `mdsMulAddCom`'s
    denotation, fed the weighted lane `a`, the MDS weight `m`, and the accumulator
    lane `b`, equals `Poseidon2LaneVec.padd (Poseidon2LaneVec.pmul (zmmLane a k)
    (zmmLane m k)) (zmmLane b k)` — the abstract Poseidon2 per-lane MDS weighted
    accumulate `(a·m) + b`. Abstract successor of the bespoke `mds2Block_realizes`. -/
theorem mdsMulAddCom_lane_eq_pmul_padd (a m b : BitVec 512) (k : Fin 8) :
    zmmLane (mdsMulAddCom.denote (.cons a (.cons m (.cons b .nil)))) k
      = padd (pmul (zmmLane a k) (zmmLane m k)) (zmmLane b k) := by
  rw [mdsMulAddCom_denote, zmmPackQ_lane, zmmPackQ_lane]
  rfl

/-! ## 4. The abstract Poseidon2-round ties packaged

The conjunction of the RC-add, S-box, and MDS-mul-add ties — each a per-sub-lane
equality between a packed `Com jasminDialect` denotation and the abstract
`Poseidon2LaneVec` lane spec (`padd` / `x⁵` / `pmul`+`padd`). Together these are
the algebraic lane steps of a Poseidon2 round, re-anchored on the unified `Com`
`zmmPackQ` denotation, with no dependence on the bespoke `Avx512Model`
(`ZInstr`/`ZState`/`runZBlock`) machine — the equal-strength successor of the
bespoke `Poseidon2RoundRealization` structural realizations. -/

/-- **The abstract Poseidon2-round ties for the unified-`Com` AVX-512 realization.**
    The conjunction of the RC-add, S-box `x⁵`, and MDS-mul-add ties — each a
    per-sub-lane equality between a packed `Com jasminDialect` denotation and the
    abstract `Poseidon2LaneVec` lane spec. The equal-strength successor of the
    bespoke `Poseidon2RoundRealization` structural realizations, now stated
    against the abstract lane spec with no dependence on the `Avx512Model`
    (`ZInstr`/`runZBlock`) machine. -/
theorem poseidon2RoundCom_eq_abstract
    (a rc m b x : BitVec 512) (k : Fin 8) :
    -- RC-add reproduces the abstract padd
    (zmmLane (rcAddCom.denote (.cons a (.cons rc .nil))) k
      = padd (zmmLane a k) (zmmLane rc k))
    -- S-box reproduces the abstract x⁵
    ∧ (zmmLane (sboxCom.denote (.cons x .nil)) k
      = (let v := zmmLane x k; v * v * v * v * v))
    -- MDS mul-add reproduces the abstract (a·m)+b
    ∧ (zmmLane (mdsMulAddCom.denote (.cons a (.cons m (.cons b .nil)))) k
      = padd (pmul (zmmLane a k) (zmmLane m k)) (zmmLane b k)) :=
  ⟨rcAddCom_lane_eq_padd a rc k,
   sboxCom_lane_eq_x5 x k,
   mdsMulAddCom_lane_eq_pmul_padd a m b k⟩

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2AbstractCom
