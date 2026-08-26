/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom

/-!
# Abstract FIPS-202 ρ/χ/ι ties for the unified-`Com` Keccak round (model-free)

`KeccakThetaPiAbstractCom.lean` re-anchored the cross-lane Keccak **θ/π**
SIMD block onto the unified `Com jasminDialect` `zmmPackQ` denotation and tied it
back to the abstract FIPS-202 spec (`Primitives.Keccak.theta` / `pi`), with no
dependence on the bespoke `Avx512Model` (`ZInstr`/`ZState`/`runZBlock`) machine.

This module is the companion for the three remaining Keccak-f[1600] step mappings —
**ρ** (lane rotation), **χ** (the non-linear combine), **ι** (round-constant xor) —
re-anchored the same way. The bespoke realizations
(`KeccakRoundRealization.lean`, `KeccakStepRealization.lean`,
`KeccakLaneRealization.lean`) carry these steps only as `runZBlock`-level
*structural* realizations against bespoke `rhoSpec`/`chiSpec`/`iotaSpec` lane
formulas — they never tie them to the abstract `Primitives.Keccak.rho`/`chi`/`iota`.
This file is the **equal-strength abstract successor**: it expresses each step as a
straight-line `Com jasminDialect` over the carry-free `vpackZMM` alphabet, pins its
denotation to `zmmPackQ`, and proves the FIPS-202 abstract tie per sub-lane through
`stateAt`/`zmmPackQ_lane`.

## The carry-free `vpackZMM` alphabet covers ρ/χ/ι

| FIPS-202 step | lane formula | `vpackZMM` arms | new op? |
|---|---|---|---|
| ρ | `rotl(a, s)` = `(a ≪ s) ||| (a ≫ (64−s))` | `.shl`, `.shr`, `.or` | no |
| χ | `a ⊕ ((¬b) ∧ c)` | `.andn` (`(~~~b) &&& c`), `.xor` | no |
| ι | `a ⊕ RC` | `.xor` | no |

Crucially, the unified `JasminBinOp` already carries `.andn`
(`andn a b = (~~~a) &&& b`, `JasminDialect.JasminBinOp.apply`), so the χ
complement-and-AND `(¬b) ∧ c` is a *single* `vpackZMM .andn` lane op — tighter than
the bespoke χ block, which lacked `vpandnq` and spelled `¬b` as `b ⊕ 1…1`. The ρ
rotate is the explicit shift-decomposition (the hardware form), recombined with
`.or`, equal to the 64-bit `rotateLeft s` by the `rotateLeftAux` identity.
No `vpermq` cross-lane permute and no new `SimdOp` op appears.

## What is proved (the abstract ρ/χ/ι ties)

* `rotateLeft_shift_decomp` — the BitVec identity licensing the rotate-insn
  selection: for `s < 64`, `a.rotateLeft s = (a ≪ s) ||| (a ≫ (64−s))`.
* `rhoCom_lane_eq_abstract_rho` — lane `k` of `rhoCom`'s denotation, fed the lane
  register `reg x y` and the broadcast amounts `s` / `64−s`, equals
  `Primitives.Keccak.rho (stateAt reg k) x y` (`= rotl(a[x,y], rotOffset x y)`)
  when `s = rotOffset x y`.
* `chiCom_lane_eq_abstract_chi` — lane `k` of `chiCom`'s denotation, fed the three
  row registers `a[x,y]` / `a[x+1,y]` / `a[x+2,y]`, equals
  `Primitives.Keccak.chi (stateAt reg k) x y` (`= a ⊕ ((¬a1) ∧ a2)`).
* `iotaCom_lane_eq_abstract_iota` — lane `k` of `iotaCom`'s denotation, fed the lane
  register `reg x y` and the broadcast round constant, equals
  `Primitives.Keccak.iota (stateAt reg k) rc x y` (the `(0,0)`-only xor with `RC`).
* `keccakRhoChiIotaCom_eq_abstract` — the conjunction, packaged as the equal-strength
  successor of the bespoke ρ/χ/ι structural realizations, now stated against the
  abstract FIPS-202 spec on the unified `Com` denotation.

There is no `runZBlock` / `ZInstr` / `ZState` / `jasminc` / `jasminc_preserves_ct`
in any theorem's `#print axioms`: the tie is between the verified
`Com jasminDialect` denotation and the abstract FIPS-202 spec.

## References
* FIPS 202 — SHA-3 Standard (ρ §3.2.2, χ §3.2.4, ι §3.2.5).

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.KeccakRhoChiIotaAbstractCom`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakRhoChiIotaAbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakThetaPiAbstractCom
open CatCrypt.Crypto.Primitives.Keccak

/-! ## 0. The rotate-insn-selection identity

ρ rotates a lane left by a fixed offset; the hardware realizes it as a
`vpsllvq | vpsrlvq | vporq` shift-decomposition. The BitVec identity below licenses
that selection: for an in-range amount `s < 64`, the 64-bit `rotateLeft s`
equals the explicit `(a ≪ s) ||| (a ≫ (64−s))`. (Generalizes the `s = 1` rotate
the θ diffusion uses.) -/

/-- **Rotate-by-`s` as the shift decomposition.** For any `s < 64`,
    `a.rotateLeft s = (a ≪ s) ||| (a ≫ (64 − s))` over `BitVec 64` — the
    `vpsllvq | vpsrlvq | vporq` hardware form of the fixed-offset lane rotate. This
    is `BitVec.rotateLeftAux` (which is *definitionally* `x <<< n ||| x >>> (w - n)`)
    applied through `rotateLeft_eq_rotateLeftAux_of_lt`. -/
theorem rotateLeft_shift_decomp (a : BitVec 64) (s : Nat) (hs : s < 64) :
    a.rotateLeft s = (a <<< s) ||| (a >>> (64 - s)) := by
  rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt hs]
  rfl

/-! ## 1. ρ lane rotation `rho = (a ≪ s) ||| (a ≫ (64−s))`

A three-`vpackZMM` block: one `.shl` (`a ≪ s`), one `.shr` (`a ≫ (64−s)`), one
`.or` (recombine to `rotl(a, s)`). Mirrors the bespoke `rhoBlock`'s
`vpsllvq`/`vpsrlvq`/`vporq`, on the unified `Com`. The shift amounts are supplied as
broadcast registers `s` / `c64` (each holding `s` / `64−s` in every lane). -/

/-- The ρ input context `[a, s, c64]`, each `reg 512`: the lane register `a` and the
    broadcast rotate amounts `s` (left shift) and `c64` (co-amount `64 − s`). -/
abbrev rhoCtx : Ctxt jasminDialect := [r512, r512, r512]

/-- The migrated ρ lane rotation as a `Com jasminDialect` over `reg 512` registers —
    the dialect-native equivalent of the bespoke `rhoBlock`: with the lane in `a`,
    the per-lane amounts `s` / `c64`, compute `rho = (a ≪ s) ||| (a ≫ c64)`. The
    bespoke `vpsllvq`/`vpsrlvq` variable per-lane shifts are `vpackZMM .shl`/`.shr`
    (`a <<< b.toNat` lane-wise). -/
def rhoCom : Com jasminDialect rhoCtx r512 :=
  -- rsl := a ≪ s   (a = .here, s = .there .here)
  .var (.mk (.vpackZMM .shl) rfl
          (.cons .here (.cons (.there .here) .nil)))
    -- rsr := a ≫ c64   (under [rsl,a,s,c64]: a = .there .here,
    --                    c64 = .there (.there (.there .here)))
    (.var (.mk (.vpackZMM .shr) rfl
            (.cons (.there .here)
              (.cons (.there (.there (.there .here))) .nil)))
      -- rout := rsl ||| rsr   (under [rsr,rsl,…]: rsl = .there .here, rsr = .here)
      (.var (.mk (.vpackZMM .or) rfl
              (.cons (.there .here) (.cons .here .nil)))
        (.ret .here)))

/-- **ρ denotation pin.** On any valuation `⟨a, s, c64⟩`, `rhoCom` denotes to
    `zmmPackQ .or (zmmPackQ .shl a s) (zmmPackQ .shr a c64)` — the verified-dialect
    packed `(a ≪ s) ||| (a ≫ c64)`, the explicit shift-decomposition rotate, the
    value the bespoke `rhoBlock` writes into `"zrho"` lane-by-lane. -/
theorem rhoCom_denote (a s c64 : BitVec 512) :
    rhoCom.denote (.cons a (.cons s (.cons c64 .nil)))
      = zmmPackQ .or (zmmPackQ .shl a s) (zmmPackQ .shr a c64) := by
  rw [rhoCom, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- **ρ abstract tie (per sub-lane).** Lane `k` of `rhoCom`'s denotation, fed the
    lane register `reg x y` and the broadcast amounts `constZmm s` / `constZmm (64−s)`
    with `s = rotOffset x y` (and `s < 64`, which holds since `rotOffset` is taken
    mod 64), equals `Primitives.Keccak.rho (stateAt reg k) x y` — the FIPS-202 lane
    rotation `rotl(a[x,y], rotOffset x y)`. The explicit `(a ≪ s) ||| (a ≫ (64−s))`
    shift-decomposition equals the 64-bit `rotateLeft s` by
    `rotateLeft_shift_decomp`. Abstract successor of the bespoke `rhoBlock_realizes`. -/
theorem rhoCom_lane_eq_abstract_rho
    (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) (x y : Fin 5)
    (s : Nat) (hs : s < 64) (hsrot : s = rotOffset x y) :
    zmmLane
        (rhoCom.denote
          (.cons (reg x y) (.cons (constZmm s) (.cons (constZmm (64 - s)) .nil)))) k
      = rho (stateAt reg k) x y := by
  rw [rhoCom_denote, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane]
  have hsk : zmmLane (constZmm s) k = BitVec.ofNat 64 s := by
    unfold constZmm; rw [zmmOfLanes_zmmLane']
  have hck : zmmLane (constZmm (64 - s)) k = BitVec.ofNat 64 (64 - s) := by
    unfold constZmm; rw [zmmOfLanes_zmmLane']
  simp only [JasminBinOp.apply, hsk, hck]
  have hsn : (BitVec.ofNat 64 s).toNat = s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hcn : (BitVec.ofNat 64 (64 - s)).toNat = 64 - s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hsn, hcn]
  rw [rho, stateAt, hsrot, ← rotateLeft_shift_decomp _ _ (hsrot ▸ hs)]

/-! ## 2. χ non-linear combine `chi = a ⊕ ((¬b) ∧ c)` (xor / andn)

A two-`vpackZMM` block: one `.andn` (`(¬b) ∧ c` in a SINGLE lane op — the unified
dialect has `andn`, unlike the bespoke χ block which lacked `vpandnq` and spelled
`¬b` as `b ⊕ 1…1`), one `.xor` (`a ⊕ …`). Mirrors `Primitives.Keccak.chi`. -/

/-- The χ input context `[a, b, c]`, each `reg 512`: the row lanes
    `a = a[x,y]`, `b = a[x+1,y]`, `c = a[x+2,y]`. -/
abbrev chiCtx : Ctxt jasminDialect := [r512, r512, r512]

/-- The migrated χ non-linear combine as a `Com jasminDialect` over `reg 512`
    registers: `chi = a ⊕ ((¬b) ∧ c)`, with the complement-and-AND as a single
    `vpackZMM .andn` (`andn b c = (~~~b) &&& c`). -/
def chiCom : Com jasminDialect chiCtx r512 :=
  -- cn := andn b c = (¬b) ∧ c   (b = .there .here, c = .there (.there .here))
  .var (.mk (.vpackZMM .andn) rfl
          (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    -- cout := a ⊕ cn   (under [cn,a,b,c]: a = .there .here, cn = .here)
    (.var (.mk (.vpackZMM .xor) rfl
            (.cons (.there .here) (.cons .here .nil)))
      (.ret .here))

/-- **χ denotation pin.** On any valuation `⟨a, b, c⟩`, `chiCom` denotes to
    `zmmPackQ .xor a (zmmPackQ .andn b c)` — the verified-dialect packed
    `a ⊕ ((¬b) ∧ c)`, the χ combine. -/
theorem chiCom_denote (a b c : BitVec 512) :
    chiCom.denote (.cons a (.cons b (.cons c .nil)))
      = zmmPackQ .xor a (zmmPackQ .andn b c) := by
  rw [chiCom, denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- **χ abstract tie (per sub-lane).** Lane `k` of `chiCom`'s denotation, fed the
    three row registers `reg x y` / `reg (x+1) y` / `reg (x+2) y`, equals
    `Primitives.Keccak.chi (stateAt reg k) x y` — the FIPS-202 non-linear combine
    `a[x,y] ⊕ ((¬a[x+1,y]) ∧ a[x+2,y])`. Abstract successor of the bespoke
    `chiBlock_realizes`. -/
theorem chiCom_lane_eq_abstract_chi
    (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) (x y : Fin 5) :
    zmmLane
        (chiCom.denote
          (.cons (reg x y)
            (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ y)
              (.cons (reg ⟨(x.val + 2) % 5, by omega⟩ y) .nil)))) k
      = chi (stateAt reg k) x y := by
  rw [chiCom_denote, zmmPackQ_lane, zmmPackQ_lane]
  simp only [JasminBinOp.apply, chi, stateAt]

/-! ## 3. ι round-constant xor `iota = a ⊕ RC` (at the (0,0) lane)

A single `vpackZMM .xor` of the lane with the broadcast round-constant register.
Mirrors the bespoke `iotaBlock`'s `vpxorq`. FIPS-202 ι touches only the `(0,0)`
lane; off `(0,0)` it is the identity. -/

/-- The ι input context `[a, rc]`, each `reg 512`: the lane register and the
    broadcast round-constant operand. -/
abbrev iotaCtx : Ctxt jasminDialect := [r512, r512]

/-- The migrated ι round-constant xor as a `Com jasminDialect` over `reg 512`
    registers: `iota = a ⊕ rc`, a single `vpackZMM .xor`. -/
def iotaCom : Com jasminDialect iotaCtx r512 :=
  -- iout := a ⊕ rc   (a = .here, rc = .there .here)
  .var (.mk (.vpackZMM .xor) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- **ι denotation pin.** On any valuation `⟨a, rc⟩`, `iotaCom` denotes to
    `zmmPackQ .xor a rc` — the verified-dialect packed `a ⊕ rc`. -/
theorem iotaCom_denote (a rc : BitVec 512) :
    iotaCom.denote (.cons a (.cons rc .nil))
      = zmmPackQ .xor a rc := by
  rw [iotaCom, denote_var_vpackZMM]
  rfl

/-- The per-lane ι round-constant operand: `RC` broadcast into the `(0,0)` lane,
    zero into every other lane. FIPS-202 ι is `a[x,y] ⊕ RC` at `(0,0)` and the
    identity elsewhere, so xoring with this per-lane operand reproduces ι exactly:
    `a ⊕ RC` at `(0,0)`, `a ⊕ 0 = a` elsewhere. This is how the round schedule
    broadcasts the round constant — into the `(0,0)` lane register only. -/
def iotaOperand (rc : BitVec 64) (x y : Fin 5) : BitVec 512 :=
  if x.val == 0 && y.val == 0 then constZmm rc.toNat else constZmm 0

/-- **ι abstract tie (per sub-lane).** Lane `k` of `iotaCom`'s denotation, fed the
    lane register `reg x y` and the per-lane round-constant operand `iotaOperand rc x y`
    (RC at `(0,0)`, zero elsewhere — exactly how ι is scheduled), equals
    `Primitives.Keccak.iota (stateAt reg k) rc x y` — the FIPS-202 round-constant xor
    `a[x,y] ⊕ RC` at `(0,0)`, the identity elsewhere. At `(0,0)` the packed xor is the
    real ι; elsewhere `a ⊕ 0 = a` matches ι's identity. Abstract successor of the
    bespoke `iotaBlock_realizes`. -/
theorem iotaCom_lane_eq_abstract_iota
    (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) (x y : Fin 5) (rc : BitVec 64) :
    zmmLane
        (iotaCom.denote
          (.cons (reg x y) (.cons (iotaOperand rc x y) .nil))) k
      = iota (stateAt reg k) rc x y := by
  rw [iotaCom_denote, zmmPackQ_lane]
  have hrc : zmmLane (constZmm rc.toNat) k = rc := by
    unfold constZmm; rw [zmmOfLanes_zmmLane']; simp
  have hz : zmmLane (constZmm 0) k = 0 := by
    unfold constZmm; rw [zmmOfLanes_zmmLane']; rfl
  simp only [JasminBinOp.apply, iota, stateAt, iotaOperand]
  by_cases h : (x.val == 0 && y.val == 0) = true
  · rw [h]; simp only [if_true, hrc]
  · rw [Bool.not_eq_true] at h
    rw [h]
    simp only [reduceCtorEq, if_false, hz]
    exact BitVec.xor_zero

/-! ## 4. The abstract ρ/χ/ι ties packaged

The conjunction of the ρ, χ, and ι ties — each a per-sub-lane equality between a
packed `Com jasminDialect` denotation and the abstract `Primitives.Keccak.rho` /
`chi` / `iota`. Together with `KeccakThetaPiAbstractCom`'s θ/π ties, this closes
the full FIPS-202 Keccak-f[1600] round `θ → ρ → π → χ → ι` on the unified `Com`
`zmmPackQ` denotation, with no dependence on the bespoke `Avx512Model`
(`ZInstr`/`ZState`/`runZBlock`) machine. -/

/-- **The abstract FIPS-202 ρ/χ/ι ties for the unified-`Com` Keccak round.** The
    conjunction of the ρ-rotation, χ-combine, and ι-round-constant ties — each a
    per-sub-lane equality between a packed `Com jasminDialect` denotation and the
    abstract `Primitives.Keccak.rho` / `chi` / `iota`. The equal-strength successor
    of the bespoke `KeccakRoundRealization` / `KeccakStepRealization`
    structural realizations, now stated against the abstract spec with no dependence
    on the `Avx512Model` (`ZInstr`/`runZBlock`) machine. -/
theorem keccakRhoChiIotaCom_eq_abstract
    (reg : Fin 5 → Fin 5 → BitVec 512) (k : Fin 8) (x y : Fin 5)
    (s : Nat) (hs : s < 64) (hsrot : s = rotOffset x y) (rc : BitVec 64) :
    -- ρ lane rotation reproduces FIPS-202 rho
    (zmmLane
        (rhoCom.denote
          (.cons (reg x y) (.cons (constZmm s) (.cons (constZmm (64 - s)) .nil)))) k
      = rho (stateAt reg k) x y)
    -- χ non-linear combine reproduces FIPS-202 chi
    ∧ (zmmLane
        (chiCom.denote
          (.cons (reg x y)
            (.cons (reg ⟨(x.val + 1) % 5, by omega⟩ y)
              (.cons (reg ⟨(x.val + 2) % 5, by omega⟩ y) .nil)))) k
      = chi (stateAt reg k) x y)
    -- ι round-constant xor reproduces FIPS-202 iota
    ∧ (zmmLane
        (iotaCom.denote (.cons (reg x y) (.cons (iotaOperand rc x y) .nil))) k
      = iota (stateAt reg k) rc x y) :=
  ⟨rhoCom_lane_eq_abstract_rho reg k x y s hs hsrot,
   chiCom_lane_eq_abstract_chi reg k x y,
   iotaCom_lane_eq_abstract_iota reg k x y rc⟩

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakRhoChiIotaAbstractCom
