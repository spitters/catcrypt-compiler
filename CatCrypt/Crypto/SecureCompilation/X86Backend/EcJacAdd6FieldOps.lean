/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6RunBlock
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Frame-wrapped six-limb field operations over the P-384 / BLS12-381 frame

`EcJacAdd6RunBlock.lean` builds the six-limb frame load/store layer (48-byte
slots, six 64-bit windows; the twelve-word product store `storeSlot12`). This
module is its field-op layer: the three frame-wrapped six-limb field ops the
P-384 / BLS12-381 Jacobian point-add composes — modular MULTIPLY, ADD and SUB —
each threading an *already-proven* six-limb field core over the frame.

Each op reads its input slots into register windows (`loadSlot6`), runs the
proven six-limb field brick over those windows, and (for add/sub) stores the
result window back to the output slot. The value lemmas are `runBlock`
derivations: the frame load (`loadSlot6_get`) lands each input slot's six limbs
in its window, so the window register map equals the slot's `slotLimbs6` value,
and the proven core then gives the field-op spec over that value.

## The three proven six-limb cores threaded

* **multiply** — `Curve6LimbTierA.p384_emit_montmul_runBlock` (the emitted
  384×384 schoolbook product over `runBlock`, `= valLimbs x · valLimbs y`, fed to
  the prime-parametric Montgomery reduce at `R = 2^384`). The product's twelve
  words are stored into the two-slot output region via `storeSlot12`.
* **add** — `FieldAddSubTierA.p384_modadd_runBlock` (the emitted ADC ripple-add
  over `runBlock`, recombined and canonicalised by the conditional subtract of
  `p`, `= (a + b) mod p`).
* **sub** — `FieldSubRunBlock.p384_modsub_runBlock` (the emitted SBB borrow chain
  over `runBlock`, canonicalised by the conditional add-back of `p`,
  `= (a − b) mod p`).

## What is proven (`runBlock` = spec)

* `feMulFrameAt6` / `feMulFrameAt6_value` — over a frame whose input slots hold
  reduced six-limb field elements, with the curve's `Nprime384` hypothesis, the
  twelve-word output region reconstructs (`valLimbs`) to the emitted
  product `valLimbs (slot a) · valLimbs (slot b)`, and `montgomeryReduce` of that
  stored value is the Montgomery field product (`< 2·p`, `· 2^384 ≡ a·b (mod p)`).
* `feAddFrameAt6` / `feAddFrameAt6_value` — the windows hold the slot limbs and
  the emitted ADC chain's reduced `runBlock` value is `(a + b) mod p`.
* `feSubFrameAt6` / `feSubFrameAt6_value` — the windows hold the slot limbs and
  the emitted SBB chain's reduced `runBlock` value is `(a − b) mod p`.

The product half is a real emitted+stored `runBlock` of a `List (JInstr 64)`; the
reduction is the prime-parametric `montgomeryMul_correct`. The add/sub reduced
values are read off the emitted chain `runBlock`, exactly as the Tier-A
six-limb headlines.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6FieldOps

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6RunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA

/-! ## 1. Frame-wrapped six-limb Montgomery field-multiply

`feMulFrameAt6` loads slot `a` into the product multiplicand window `xs`, slot `b`
into the multiplier window `ys`, runs the proven emitted schoolbook product
(`emitProductBlock6 accs xs ys hi lo`) over the twelve-word accumulator file
`accs`, and stores the twelve product words into the two-slot output region `o`
via `storeSlot12`. The accumulator file is set up cleared (and the carry flags
`CF = OF = 0`) as the proven product brick requires. -/

/-- Frame-wrapped six-limb Montgomery field-multiply: load slot `a` into the
    multiplicand window `xs`, slot `b` into the multiplier window `ys`, run the
    emitted 384×384 schoolbook product over the twelve-word accumulator file
    `accs`, and store the twelve product words into the output region rooted at
    slot `o`. The six-limb analogue of `EcJacAddMontMul.feMulFrameAt`. -/
def feMulFrameAt6 (xs ys accs : List String) (hi lo base : String) (o a b : Nat) :
    List (JInstr 64) :=
  match xs, ys, accs with
  | [x0, x1, x2, x3, x4, x5], [y0, y1, y2, y3, y4, y5],
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] =>
      loadSlot6 x0 x1 x2 x3 x4 x5 base a
        ++ loadSlot6 y0 y1 y2 y3 y4 y5 base b
        ++ emitProductBlock6 accs xs ys hi lo
        ++ storeSlot12 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 base o
  | _, _, _ => []

/-- **Frame-wrapped six-limb Montgomery field-multiply value.** Over a frame whose
    input slots `a`, `b` hold reduced six-limb P-384 field elements
    (`valLimbs < p384`), with the `ProdFresh` register layout, a cleared
    accumulator file, both carry flags clear after the two loads, the input windows
    fresh and disjoint, and the curve's Montgomery constant `Nprime384`:

    * the twelve-word output region rooted at slot `o` reconstructs (`valLimbs`) to
      the emitted product `valLimbs (slot a) · valLimbs (slot b)`
      (`p384_emit_montmul_runBlock` + `storeSlot12_load`); and
    * `montgomeryReduce p384 (2^384) Nprime384` of that stored value is the
      Montgomery field product — it lies in `[0, 2·p384)` and
      `· 2^384 ≡ valLimbs a · valLimbs b (mod p384)` (`montgomeryMul_correct`).

    The product is a real emitted+stored `runBlock` of a `List (JInstr 64)`; the
    reduction is applied to that value, mirroring `EcJacAddMontMul.feMulFrameAt_value`
    at the six-limb radix `R = 2^384`. -/
theorem feMulFrameAt6_value
    (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : String)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : String) (hi lo base : String)
    (o a b : Nat) (s : JState 64) (Nprime384 : Nat)
    -- input-window freshness
    (hx10 : x1 ≠ x0) (hx20 : x2 ≠ x0) (hx21 : x2 ≠ x1)
    (hx30 : x3 ≠ x0) (hx31 : x3 ≠ x1) (hx32 : x3 ≠ x2)
    (hx40 : x4 ≠ x0) (hx41 : x4 ≠ x1) (hx42 : x4 ≠ x2) (hx43 : x4 ≠ x3)
    (hx50 : x5 ≠ x0) (hx51 : x5 ≠ x1) (hx52 : x5 ≠ x2) (hx53 : x5 ≠ x3) (hx54 : x5 ≠ x4)
    (hy10 : y1 ≠ y0) (hy20 : y2 ≠ y0) (hy21 : y2 ≠ y1)
    (hy30 : y3 ≠ y0) (hy31 : y3 ≠ y1) (hy32 : y3 ≠ y2)
    (hy40 : y4 ≠ y0) (hy41 : y4 ≠ y1) (hy42 : y4 ≠ y2) (hy43 : y4 ≠ y3)
    (hy50 : y5 ≠ y0) (hy51 : y5 ≠ y1) (hy52 : y5 ≠ y2) (hy53 : y5 ≠ y3) (hy54 : y5 ≠ y4)
    -- the two windows are disjoint (each x distinct from each y)
    (hxy : ∀ d ∈ [x0, x1, x2, x3, x4, x5], ∀ e ∈ [y0, y1, y2, y3, y4, y5], d ≠ e)
    -- the accumulator file is disjoint from both input windows
    (hacc_x : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11],
      ∀ q ∈ [x0, x1, x2, x3, x4, x5], r ≠ q)
    (hacc_y : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11],
      ∀ q ∈ [y0, y1, y2, y3, y4, y5], r ≠ q)
    -- product register-layout freshness
    (hfresh : ProdFresh [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]
      [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5] hi lo)
    -- the accumulator file is cleared and both carry flags clear on entry
    (hacc0 : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11], s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    -- reduced inputs and the curve Montgomery constant
    (hx_red : valLimbs (slotLimbs6 s base a) < valLimbs p384Limbs)
    (hy_red : valLimbs (slotLimbs6 s base b) < valLimbs p384Limbs)
    (hNprime : (valLimbs p384Limbs * Nprime384) % 2 ^ 384 = 2 ^ 384 - 1) :
    valLimbs (slotLimbs12 (runBlock s
        (feMulFrameAt6 [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5]
          [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] hi lo base o a b)) base o)
        = valLimbs (slotLimbs6 s base a) * valLimbs (slotLimbs6 s base b) ∧
    Number.montgomeryReduce (valLimbs p384Limbs) (2 ^ 384) Nprime384
        (valLimbs (slotLimbs12 (runBlock s
          (feMulFrameAt6 [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5]
            [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] hi lo base o a b)) base o))
        < 2 * valLimbs p384Limbs ∧
    (Number.montgomeryReduce (valLimbs p384Limbs) (2 ^ 384) Nprime384
        (valLimbs (slotLimbs12 (runBlock s
          (feMulFrameAt6 [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5]
            [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] hi lo base o a b)) base o))) * 2 ^ 384
      ≡ valLimbs (slotLimbs6 s base a) * valLimbs (slotLimbs6 s base b) [MOD valLimbs p384Limbs] := by
  -- the input windows, the accumulator file, and the slot values
  set xs := [x0, x1, x2, x3, x4, x5] with hxsdef
  set ys := [y0, y1, y2, y3, y4, y5] with hysdef
  set accs := [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] with haccsdef
  set xv := slotLimbs6 s base a with hxv
  set yv := slotLimbs6 s base b with hyv
  -- the three intermediate states (`feMulFrameAt6` reduces to the four-block append)
  set s1 := runBlock s (loadSlot6 x0 x1 x2 x3 x4 x5 base a) with hs1def
  set s2 := runBlock s1 (loadSlot6 y0 y1 y2 y3 y4 y5 base b) with hs2def
  set s3 := runBlock s2 (emitProductBlock6 accs xs ys hi lo) with hs3def
  -- s1: the multiplicand window holds slot-a's limbs.
  obtain ⟨hs1x0, hs1x1, hs1x2, hs1x3, hs1x4, hs1x5⟩ :=
    loadSlot6_get x0 x1 x2 x3 x4 x5 base a s hx10 hx20 hx21 hx30 hx31 hx32
      hx40 hx41 hx42 hx43 hx50 hx51 hx52 hx53 hx54
  -- s2: the multiplier window holds slot-b's limbs.
  obtain ⟨hs2y0, hs2y1, hs2y2, hs2y3, hs2y4, hs2y5⟩ :=
    loadSlot6_get y0 y1 y2 y3 y4 y5 base b s1 hy10 hy20 hy21 hy30 hy31 hy32
      hy40 hy41 hy42 hy43 hy50 hy51 hy52 hy53 hy54
  -- the multiplicand window survives the b-load (windows disjoint).
  have hxy0 : ∀ e ∈ ys, x0 ≠ e := hxy x0 (by simp [hxsdef])
  have hxy1 : ∀ e ∈ ys, x1 ≠ e := hxy x1 (by simp [hxsdef])
  have hxy2 : ∀ e ∈ ys, x2 ≠ e := hxy x2 (by simp [hxsdef])
  have hxy3 : ∀ e ∈ ys, x3 ≠ e := hxy x3 (by simp [hxsdef])
  have hxy4 : ∀ e ∈ ys, x4 ≠ e := hxy x4 (by simp [hxsdef])
  have hxy5 : ∀ e ∈ ys, x5 ≠ e := hxy x5 (by simp [hxsdef])
  have hs2x0 : s2.get x0 = s.load base (slotOff6 a 0) := by
    rw [hs2def, loadSlot6_other y0 y1 y2 y3 y4 y5 base b s1 x0
      (hxy0 y0 (by simp [hysdef])) (hxy0 y1 (by simp [hysdef])) (hxy0 y2 (by simp [hysdef]))
      (hxy0 y3 (by simp [hysdef])) (hxy0 y4 (by simp [hysdef])) (hxy0 y5 (by simp [hysdef])), hs1x0]
  have hs2x1 : s2.get x1 = s.load base (slotOff6 a 1) := by
    rw [hs2def, loadSlot6_other y0 y1 y2 y3 y4 y5 base b s1 x1
      (hxy1 y0 (by simp [hysdef])) (hxy1 y1 (by simp [hysdef])) (hxy1 y2 (by simp [hysdef]))
      (hxy1 y3 (by simp [hysdef])) (hxy1 y4 (by simp [hysdef])) (hxy1 y5 (by simp [hysdef])), hs1x1]
  have hs2x2 : s2.get x2 = s.load base (slotOff6 a 2) := by
    rw [hs2def, loadSlot6_other y0 y1 y2 y3 y4 y5 base b s1 x2
      (hxy2 y0 (by simp [hysdef])) (hxy2 y1 (by simp [hysdef])) (hxy2 y2 (by simp [hysdef]))
      (hxy2 y3 (by simp [hysdef])) (hxy2 y4 (by simp [hysdef])) (hxy2 y5 (by simp [hysdef])), hs1x2]
  have hs2x3 : s2.get x3 = s.load base (slotOff6 a 3) := by
    rw [hs2def, loadSlot6_other y0 y1 y2 y3 y4 y5 base b s1 x3
      (hxy3 y0 (by simp [hysdef])) (hxy3 y1 (by simp [hysdef])) (hxy3 y2 (by simp [hysdef]))
      (hxy3 y3 (by simp [hysdef])) (hxy3 y4 (by simp [hysdef])) (hxy3 y5 (by simp [hysdef])), hs1x3]
  have hs2x4 : s2.get x4 = s.load base (slotOff6 a 4) := by
    rw [hs2def, loadSlot6_other y0 y1 y2 y3 y4 y5 base b s1 x4
      (hxy4 y0 (by simp [hysdef])) (hxy4 y1 (by simp [hysdef])) (hxy4 y2 (by simp [hysdef]))
      (hxy4 y3 (by simp [hysdef])) (hxy4 y4 (by simp [hysdef])) (hxy4 y5 (by simp [hysdef])), hs1x4]
  have hs2x5 : s2.get x5 = s.load base (slotOff6 a 5) := by
    rw [hs2def, loadSlot6_other y0 y1 y2 y3 y4 y5 base b s1 x5
      (hxy5 y0 (by simp [hysdef])) (hxy5 y1 (by simp [hysdef])) (hxy5 y2 (by simp [hysdef]))
      (hxy5 y3 (by simp [hysdef])) (hxy5 y4 (by simp [hysdef])) (hxy5 y5 (by simp [hysdef])), hs1x5]
  -- the multiplicand-window get-map = slot-a's limbs.
  have hxmap : xs.map s2.get = xv := by
    simp only [hxsdef, hxv, slotLimbs6, List.map_cons, List.map_nil, hs2x0, hs2x1, hs2x2,
      hs2x3, hs2x4, hs2x5]
  -- the multiplier-window get-map = slot-b's limbs.
  have hymap : ys.map s2.get = yv := by
    rw [← hs2def] at hs2y0 hs2y1 hs2y2 hs2y3 hs2y4 hs2y5
    simp only [hysdef, hyv, slotLimbs6, List.map_cons, List.map_nil, hs2y0, hs2y1, hs2y2,
      hs2y3, hs2y4, hs2y5, hs1def, loadSlot6_load]
  -- the accumulator file is still cleared in s2 (loads write only their windows).
  have hacc0_s2 : ∀ r ∈ accs, s2.get r = 0 := by
    intro r hr
    rw [hs2def, loadSlot6_other y0 y1 y2 y3 y4 y5 base b s1 r
        (fun h => hacc_y r hr y0 (by simp [hysdef]) h) (fun h => hacc_y r hr y1 (by simp [hysdef]) h)
        (fun h => hacc_y r hr y2 (by simp [hysdef]) h) (fun h => hacc_y r hr y3 (by simp [hysdef]) h)
        (fun h => hacc_y r hr y4 (by simp [hysdef]) h) (fun h => hacc_y r hr y5 (by simp [hysdef]) h)]
    rw [hs1def, loadSlot6_other x0 x1 x2 x3 x4 x5 base a s r
        (fun h => hacc_x r hr x0 (by simp [hxsdef]) h) (fun h => hacc_x r hr x1 (by simp [hxsdef]) h)
        (fun h => hacc_x r hr x2 (by simp [hxsdef]) h) (fun h => hacc_x r hr x3 (by simp [hxsdef]) h)
        (fun h => hacc_x r hr x4 (by simp [hxsdef]) h) (fun h => hacc_x r hr x5 (by simp [hxsdef]) h)]
    exact hacc0 r hr
  -- the carry flags are still clear in s2 (loads touch no flag).
  have hcf_s2 : s2.flagB (·.cf) = false := by
    rw [hs2def, loadSlot6_flagB, hs1def, loadSlot6_flagB, hcf]
  have hof_s2 : s2.flagB (·.of) = false := by
    rw [hs2def, loadSlot6_flagB, hs1def, loadSlot6_flagB, hof]
  -- lengths for the product brick (xs, ys length 6; accs length 12)
  have hxslen : xs.length = xv.length := by
    rw [hxsdef, hxv]; simp [slotLimbs6]
  have hyslen : ys.length = yv.length := by
    rw [hysdef, hyv]; simp [slotLimbs6]
  -- the proven emitted product + reduction (the six-limb Tier-A core).
  obtain ⟨hprodval, hrange, hcong⟩ := Curve6LimbTierA.p384_emit_montmul_runBlock
    accs xs ys xv yv hi lo s2 Nprime384 hxslen hyslen (by rw [hxsdef, hysdef, haccsdef]; simp)
    hfresh hxmap hymap hacc0_s2 hcf_s2 hof_s2 hx_red hy_red hNprime
  -- the product value over the twelve accumulator registers.
  have hprod : valLimbs (accs.map s3.get) = valLimbs xv * valLimbs yv := by
    rw [hs3def, emitProductBlock6]
    simpa only [runBlockProductValue] using hprodval
  -- the store-reconstruction over the twelve accumulator registers.
  have hstore := storeSlot12_load c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 base o s3
  -- the field-mul value: factor the runBlock through the loads + product + store.
  have hfinal : valLimbs (slotLimbs12 (runBlock s
        (feMulFrameAt6 xs ys accs hi lo base o a b)) base o) = valLimbs xv * valLimbs yv := by
    rw [show feMulFrameAt6 xs ys accs hi lo base o a b
        = loadSlot6 x0 x1 x2 x3 x4 x5 base a ++ loadSlot6 y0 y1 y2 y3 y4 y5 base b
          ++ emitProductBlock6 accs xs ys hi lo
          ++ storeSlot12 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 base o from rfl]
    rw [runBlock_append, runBlock_append, runBlock_append, ← hs1def, ← hs2def, ← hs3def, hstore]
    simp only [haccsdef, List.map_cons, List.map_nil] at hprod
    exact hprod
  -- assemble: the product half, then the reduction from the core.
  rw [hfinal]
  refine ⟨rfl, ?_, ?_⟩
  · rw [hprodval] at hrange
    exact hrange
  · rw [hprodval] at hcong
    exact hcong

/-! ## 2. Frame-wrapped six-limb modular add

`feAddFrameAt6` loads slot `a` into the destination window `dregs`, slot `b` into
the source window `sregs`, and runs the proven emitted ADC carry chain
(`emitAdcChain`) over the two windows. Its value lemma threads
`FieldAddSubTierA.p384_modadd_runBlock`: the frame loads supply the destination /
source register maps (`loadSlot6_get`), so the chain's reduced `runBlock` value
(`condSubP p (runBlockAddValue …)`) is `(a + b) mod p`. -/

/-- Frame-wrapped six-limb modular add: load slot `a` into the destination window
    `dregs`, slot `b` into the source window `sregs`, and run the emitted ADC carry
    chain over the two windows. The six-limb add-side analogue of
    `EcJacAddRunBlock.feAddFrameAt`. -/
def feAddFrameAt6 (dregs sregs : List String) (base : String) (a b : Nat) :
    List (JInstr 64) :=
  match dregs, sregs with
  | [d0, d1, d2, d3, d4, d5], [e0, e1, e2, e3, e4, e5] =>
      loadSlot6 d0 d1 d2 d3 d4 d5 base a
        ++ loadSlot6 e0 e1 e2 e3 e4 e5 base b
        ++ emitAdcChain dregs sregs
  | _, _ => []

/-- **Frame-wrapped six-limb modular add value.** Over a frame whose input slots
    `a`, `b` hold reduced six-limb P-384 field elements, the emitted ADC carry
    chain's reduced `runBlock` value — the destination registers' `addLimbs` sum
    canonicalised by the conditional subtract of `p` (`condSubP p
    (runBlockAddValue …)`) — equals `(valLimbs (slot a) + valLimbs (slot b)) mod p`.

    Composes `loadSlot6_get` (each input slot lands in its window, so the window
    get-maps equal the slot limbs) with the proven six-limb
    `FieldAddSubTierA.p384_modadd_runBlock` (the emitted ADC chain over `runBlock`,
    recombined and reduced). Entered with `CF = 0`, the carry-chain-entry
    condition. -/
theorem feAddFrameAt6_value
    (d0 d1 d2 d3 d4 d5 e0 e1 e2 e3 e4 e5 base : String) (a b : Nat) (s : JState 64)
    (hd10 : d1 ≠ d0) (hd20 : d2 ≠ d0) (hd21 : d2 ≠ d1)
    (hd30 : d3 ≠ d0) (hd31 : d3 ≠ d1) (hd32 : d3 ≠ d2)
    (hd40 : d4 ≠ d0) (hd41 : d4 ≠ d1) (hd42 : d4 ≠ d2) (hd43 : d4 ≠ d3)
    (hd50 : d5 ≠ d0) (hd51 : d5 ≠ d1) (hd52 : d5 ≠ d2) (hd53 : d5 ≠ d3) (hd54 : d5 ≠ d4)
    (he10 : e1 ≠ e0) (he20 : e2 ≠ e0) (he21 : e2 ≠ e1)
    (he30 : e3 ≠ e0) (he31 : e3 ≠ e1) (he32 : e3 ≠ e2)
    (he40 : e4 ≠ e0) (he41 : e4 ≠ e1) (he42 : e4 ≠ e2) (he43 : e4 ≠ e3)
    (he50 : e5 ≠ e0) (he51 : e5 ≠ e1) (he52 : e5 ≠ e2) (he53 : e5 ≠ e3) (he54 : e5 ≠ e4)
    (hde : ∀ d ∈ [d0, d1, d2, d3, d4, d5], ∀ e ∈ [e0, e1, e2, e3, e4, e5], d ≠ e)
    (hcf0 : s.flagB (·.cf) = false)
    (ha_red : valLimbs (slotLimbs6 s base a) < valLimbs p384Limbs)
    (hb_red : valLimbs (slotLimbs6 s base b) < valLimbs p384Limbs) :
    condSubP (valLimbs p384Limbs)
        (runBlockAddValue [d0, d1, d2, d3, d4, d5] [e0, e1, e2, e3, e4, e5]
          (runBlock (runBlock s (loadSlot6 d0 d1 d2 d3 d4 d5 base a))
            (loadSlot6 e0 e1 e2 e3 e4 e5 base b)))
      = (valLimbs (slotLimbs6 s base a) + valLimbs (slotLimbs6 s base b)) % valLimbs p384Limbs := by
  set ds := [d0, d1, d2, d3, d4, d5] with hdsdef
  set ss := [e0, e1, e2, e3, e4, e5] with hssdef
  set av := slotLimbs6 s base a with hav
  set bv := slotLimbs6 s base b with hbv
  -- the state after the two loads (the chain entry state)
  set s1 := runBlock s (loadSlot6 d0 d1 d2 d3 d4 d5 base a) with hs1def
  set s2 := runBlock s1 (loadSlot6 e0 e1 e2 e3 e4 e5 base b) with hs2def
  -- s1: the destination window holds slot-a's limbs.
  obtain ⟨hs1d0, hs1d1, hs1d2, hs1d3, hs1d4, hs1d5⟩ :=
    loadSlot6_get d0 d1 d2 d3 d4 d5 base a s hd10 hd20 hd21 hd30 hd31 hd32
      hd40 hd41 hd42 hd43 hd50 hd51 hd52 hd53 hd54
  -- s2: the source window holds slot-b's limbs.
  obtain ⟨hs2e0, hs2e1, hs2e2, hs2e3, hs2e4, hs2e5⟩ :=
    loadSlot6_get e0 e1 e2 e3 e4 e5 base b s1 he10 he20 he21 he30 he31 he32
      he40 he41 he42 he43 he50 he51 he52 he53 he54
  -- the destination window survives the b-load (windows disjoint).
  have hde0 : ∀ e ∈ ss, d0 ≠ e := hde d0 (by simp [hdsdef])
  have hde1 : ∀ e ∈ ss, d1 ≠ e := hde d1 (by simp [hdsdef])
  have hde2 : ∀ e ∈ ss, d2 ≠ e := hde d2 (by simp [hdsdef])
  have hde3 : ∀ e ∈ ss, d3 ≠ e := hde d3 (by simp [hdsdef])
  have hde4 : ∀ e ∈ ss, d4 ≠ e := hde d4 (by simp [hdsdef])
  have hde5 : ∀ e ∈ ss, d5 ≠ e := hde d5 (by simp [hdsdef])
  have hs2d0 : s2.get d0 = s.load base (slotOff6 a 0) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d0
      (hde0 e0 (by simp [hssdef])) (hde0 e1 (by simp [hssdef])) (hde0 e2 (by simp [hssdef]))
      (hde0 e3 (by simp [hssdef])) (hde0 e4 (by simp [hssdef])) (hde0 e5 (by simp [hssdef])), hs1d0]
  have hs2d1 : s2.get d1 = s.load base (slotOff6 a 1) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d1
      (hde1 e0 (by simp [hssdef])) (hde1 e1 (by simp [hssdef])) (hde1 e2 (by simp [hssdef]))
      (hde1 e3 (by simp [hssdef])) (hde1 e4 (by simp [hssdef])) (hde1 e5 (by simp [hssdef])), hs1d1]
  have hs2d2 : s2.get d2 = s.load base (slotOff6 a 2) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d2
      (hde2 e0 (by simp [hssdef])) (hde2 e1 (by simp [hssdef])) (hde2 e2 (by simp [hssdef]))
      (hde2 e3 (by simp [hssdef])) (hde2 e4 (by simp [hssdef])) (hde2 e5 (by simp [hssdef])), hs1d2]
  have hs2d3 : s2.get d3 = s.load base (slotOff6 a 3) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d3
      (hde3 e0 (by simp [hssdef])) (hde3 e1 (by simp [hssdef])) (hde3 e2 (by simp [hssdef]))
      (hde3 e3 (by simp [hssdef])) (hde3 e4 (by simp [hssdef])) (hde3 e5 (by simp [hssdef])), hs1d3]
  have hs2d4 : s2.get d4 = s.load base (slotOff6 a 4) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d4
      (hde4 e0 (by simp [hssdef])) (hde4 e1 (by simp [hssdef])) (hde4 e2 (by simp [hssdef]))
      (hde4 e3 (by simp [hssdef])) (hde4 e4 (by simp [hssdef])) (hde4 e5 (by simp [hssdef])), hs1d4]
  have hs2d5 : s2.get d5 = s.load base (slotOff6 a 5) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d5
      (hde5 e0 (by simp [hssdef])) (hde5 e1 (by simp [hssdef])) (hde5 e2 (by simp [hssdef]))
      (hde5 e3 (by simp [hssdef])) (hde5 e4 (by simp [hssdef])) (hde5 e5 (by simp [hssdef])), hs1d5]
  -- the destination window's get-map = slot-a's limbs; source window's = slot-b's.
  have hdmap : ds.map s2.get = av := by
    simp only [hdsdef, hav, slotLimbs6, List.map_cons, List.map_nil, hs2d0, hs2d1, hs2d2,
      hs2d3, hs2d4, hs2d5]
  have hsmap : ss.map s2.get = bv := by
    rw [← hs2def] at hs2e0 hs2e1 hs2e2 hs2e3 hs2e4 hs2e5
    simp only [hssdef, hbv, slotLimbs6, List.map_cons, List.map_nil, hs2e0, hs2e1, hs2e2,
      hs2e3, hs2e4, hs2e5, hs1def, loadSlot6_load]
  -- the flag is still 0 at the ADC entry (loads touch no flag).
  have hcf_s2 : s2.flagB (·.cf) = false := by
    rw [hs2def, loadSlot6_flagB, hs1def, loadSlot6_flagB, hcf0]
  -- ChainFresh for the two windows
  have hfresh : ChainFresh ds ss :=
    { ds_nodup := by
        rw [hdsdef]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          and_true, not_or, or_false, not_false_iff]
        refine ⟨⟨Ne.symm hd10, Ne.symm hd20, Ne.symm hd30, Ne.symm hd40, Ne.symm hd50⟩,
          ⟨Ne.symm hd21, Ne.symm hd31, Ne.symm hd41, Ne.symm hd51⟩,
          ⟨Ne.symm hd32, Ne.symm hd42, Ne.symm hd52⟩,
          ⟨Ne.symm hd43, Ne.symm hd53⟩, Ne.symm hd54⟩
      ds_ss := hde }
  -- length facts
  have hda : ds.length = av.length := by rw [hdsdef, hav]; simp [slotLimbs6]
  have hsb : ss.length = bv.length := by rw [hssdef, hbv]; simp [slotLimbs6]
  have hab : av.length = bv.length := by rw [hav, hbv]; simp [slotLimbs6]
  -- thread the proven six-limb reduced add core over the chain-entry state s2.
  have hcore := p384_modadd_runBlock ds ss av bv s2 hda hsb hab hfresh hdmap hsmap
    hcf_s2 ha_red hb_red
  exact hcore

/-! ## 3. Frame-wrapped six-limb modular sub

`feSubFrameAt6` loads slot `a` into the destination window `dregs`, slot `b` into
the source window `sregs`, and runs the proven emitted SBB borrow chain
(`emitSbbChain`) over the two windows. Its value lemma threads
`FieldSubRunBlock.p384_modsub_runBlock`: the frame loads supply the register maps,
so the chain's reduced `runBlock` value (`runBlockModSubValue p …`) is
`(a − b) mod p`. -/

/-- Frame-wrapped six-limb modular sub: load slot `a` into the destination window
    `dregs`, slot `b` into the source window `sregs`, and run the emitted SBB borrow
    chain over the two windows. The six-limb sub-side analogue of
    `EcJacAddRunBlock.feSubFrameAt`. -/
def feSubFrameAt6 (dregs sregs : List String) (base : String) (a b : Nat) :
    List (JInstr 64) :=
  match dregs, sregs with
  | [d0, d1, d2, d3, d4, d5], [e0, e1, e2, e3, e4, e5] =>
      loadSlot6 d0 d1 d2 d3 d4 d5 base a
        ++ loadSlot6 e0 e1 e2 e3 e4 e5 base b
        ++ emitSbbChain dregs sregs
  | _, _ => []

/-- **Frame-wrapped six-limb modular sub value.** Over a frame whose input slots
    `a`, `b` hold reduced six-limb P-384 field elements, the emitted SBB borrow
    chain's reduced `runBlock` value — the destination registers' `subLimbs`
    difference canonicalised by the conditional add-back of `p`
    (`runBlockModSubValue p …`) — equals `(valLimbs (slot a) + p − valLimbs
    (slot b)) mod p = (a − b) mod p`.

    Composes `loadSlot6_get` (each input slot lands in its window) with the proven
    six-limb `FieldSubRunBlock.p384_modsub_runBlock` (the emitted SBB chain over
    `runBlock`, reconstructed and reduced). Entered with `CF = 0`, the
    borrow-chain-entry condition. -/
theorem feSubFrameAt6_value
    (d0 d1 d2 d3 d4 d5 e0 e1 e2 e3 e4 e5 base : String) (a b : Nat) (s : JState 64)
    (hd10 : d1 ≠ d0) (hd20 : d2 ≠ d0) (hd21 : d2 ≠ d1)
    (hd30 : d3 ≠ d0) (hd31 : d3 ≠ d1) (hd32 : d3 ≠ d2)
    (hd40 : d4 ≠ d0) (hd41 : d4 ≠ d1) (hd42 : d4 ≠ d2) (hd43 : d4 ≠ d3)
    (hd50 : d5 ≠ d0) (hd51 : d5 ≠ d1) (hd52 : d5 ≠ d2) (hd53 : d5 ≠ d3) (hd54 : d5 ≠ d4)
    (he10 : e1 ≠ e0) (he20 : e2 ≠ e0) (he21 : e2 ≠ e1)
    (he30 : e3 ≠ e0) (he31 : e3 ≠ e1) (he32 : e3 ≠ e2)
    (he40 : e4 ≠ e0) (he41 : e4 ≠ e1) (he42 : e4 ≠ e2) (he43 : e4 ≠ e3)
    (he50 : e5 ≠ e0) (he51 : e5 ≠ e1) (he52 : e5 ≠ e2) (he53 : e5 ≠ e3) (he54 : e5 ≠ e4)
    (hde : ∀ d ∈ [d0, d1, d2, d3, d4, d5], ∀ e ∈ [e0, e1, e2, e3, e4, e5], d ≠ e)
    (hcf0 : s.flagB (·.cf) = false)
    (hp : valLimbs p384Limbs < (2 ^ 64) ^ 6)
    (ha_red : valLimbs (slotLimbs6 s base a) < valLimbs p384Limbs)
    (hb_red : valLimbs (slotLimbs6 s base b) < valLimbs p384Limbs) :
    runBlockModSubValue (valLimbs p384Limbs)
        [d0, d1, d2, d3, d4, d5] [e0, e1, e2, e3, e4, e5]
        (runBlock (runBlock s (loadSlot6 d0 d1 d2 d3 d4 d5 base a))
          (loadSlot6 e0 e1 e2 e3 e4 e5 base b))
      = (valLimbs (slotLimbs6 s base a) + valLimbs p384Limbs
          - valLimbs (slotLimbs6 s base b)) % valLimbs p384Limbs := by
  set ds := [d0, d1, d2, d3, d4, d5] with hdsdef
  set ss := [e0, e1, e2, e3, e4, e5] with hssdef
  set av := slotLimbs6 s base a with hav
  set bv := slotLimbs6 s base b with hbv
  set s1 := runBlock s (loadSlot6 d0 d1 d2 d3 d4 d5 base a) with hs1def
  set s2 := runBlock s1 (loadSlot6 e0 e1 e2 e3 e4 e5 base b) with hs2def
  obtain ⟨hs1d0, hs1d1, hs1d2, hs1d3, hs1d4, hs1d5⟩ :=
    loadSlot6_get d0 d1 d2 d3 d4 d5 base a s hd10 hd20 hd21 hd30 hd31 hd32
      hd40 hd41 hd42 hd43 hd50 hd51 hd52 hd53 hd54
  obtain ⟨hs2e0, hs2e1, hs2e2, hs2e3, hs2e4, hs2e5⟩ :=
    loadSlot6_get e0 e1 e2 e3 e4 e5 base b s1 he10 he20 he21 he30 he31 he32
      he40 he41 he42 he43 he50 he51 he52 he53 he54
  have hde0 : ∀ e ∈ ss, d0 ≠ e := hde d0 (by simp [hdsdef])
  have hde1 : ∀ e ∈ ss, d1 ≠ e := hde d1 (by simp [hdsdef])
  have hde2 : ∀ e ∈ ss, d2 ≠ e := hde d2 (by simp [hdsdef])
  have hde3 : ∀ e ∈ ss, d3 ≠ e := hde d3 (by simp [hdsdef])
  have hde4 : ∀ e ∈ ss, d4 ≠ e := hde d4 (by simp [hdsdef])
  have hde5 : ∀ e ∈ ss, d5 ≠ e := hde d5 (by simp [hdsdef])
  have hs2d0 : s2.get d0 = s.load base (slotOff6 a 0) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d0
      (hde0 e0 (by simp [hssdef])) (hde0 e1 (by simp [hssdef])) (hde0 e2 (by simp [hssdef]))
      (hde0 e3 (by simp [hssdef])) (hde0 e4 (by simp [hssdef])) (hde0 e5 (by simp [hssdef])), hs1d0]
  have hs2d1 : s2.get d1 = s.load base (slotOff6 a 1) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d1
      (hde1 e0 (by simp [hssdef])) (hde1 e1 (by simp [hssdef])) (hde1 e2 (by simp [hssdef]))
      (hde1 e3 (by simp [hssdef])) (hde1 e4 (by simp [hssdef])) (hde1 e5 (by simp [hssdef])), hs1d1]
  have hs2d2 : s2.get d2 = s.load base (slotOff6 a 2) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d2
      (hde2 e0 (by simp [hssdef])) (hde2 e1 (by simp [hssdef])) (hde2 e2 (by simp [hssdef]))
      (hde2 e3 (by simp [hssdef])) (hde2 e4 (by simp [hssdef])) (hde2 e5 (by simp [hssdef])), hs1d2]
  have hs2d3 : s2.get d3 = s.load base (slotOff6 a 3) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d3
      (hde3 e0 (by simp [hssdef])) (hde3 e1 (by simp [hssdef])) (hde3 e2 (by simp [hssdef]))
      (hde3 e3 (by simp [hssdef])) (hde3 e4 (by simp [hssdef])) (hde3 e5 (by simp [hssdef])), hs1d3]
  have hs2d4 : s2.get d4 = s.load base (slotOff6 a 4) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d4
      (hde4 e0 (by simp [hssdef])) (hde4 e1 (by simp [hssdef])) (hde4 e2 (by simp [hssdef]))
      (hde4 e3 (by simp [hssdef])) (hde4 e4 (by simp [hssdef])) (hde4 e5 (by simp [hssdef])), hs1d4]
  have hs2d5 : s2.get d5 = s.load base (slotOff6 a 5) := by
    rw [hs2def, loadSlot6_other e0 e1 e2 e3 e4 e5 base b s1 d5
      (hde5 e0 (by simp [hssdef])) (hde5 e1 (by simp [hssdef])) (hde5 e2 (by simp [hssdef]))
      (hde5 e3 (by simp [hssdef])) (hde5 e4 (by simp [hssdef])) (hde5 e5 (by simp [hssdef])), hs1d5]
  have hdmap : ds.map s2.get = av := by
    simp only [hdsdef, hav, slotLimbs6, List.map_cons, List.map_nil, hs2d0, hs2d1, hs2d2,
      hs2d3, hs2d4, hs2d5]
  have hsmap : ss.map s2.get = bv := by
    rw [← hs2def] at hs2e0 hs2e1 hs2e2 hs2e3 hs2e4 hs2e5
    simp only [hssdef, hbv, slotLimbs6, List.map_cons, List.map_nil, hs2e0, hs2e1, hs2e2,
      hs2e3, hs2e4, hs2e5, hs1def, loadSlot6_load]
  have hcf_s2 : s2.flagB (·.cf) = false := by
    rw [hs2def, loadSlot6_flagB, hs1def, loadSlot6_flagB, hcf0]
  have hfresh : ChainFresh ds ss :=
    { ds_nodup := by
        rw [hdsdef]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          and_true, not_or, or_false, not_false_iff]
        refine ⟨⟨Ne.symm hd10, Ne.symm hd20, Ne.symm hd30, Ne.symm hd40, Ne.symm hd50⟩,
          ⟨Ne.symm hd21, Ne.symm hd31, Ne.symm hd41, Ne.symm hd51⟩,
          ⟨Ne.symm hd32, Ne.symm hd42, Ne.symm hd52⟩,
          ⟨Ne.symm hd43, Ne.symm hd53⟩, Ne.symm hd54⟩
      ds_ss := hde }
  have hda : ds.length = av.length := by rw [hdsdef, hav]; simp [slotLimbs6]
  have hsb : ss.length = bv.length := by rw [hssdef, hbv]; simp [slotLimbs6]
  have hab : av.length = bv.length := by rw [hav, hbv]; simp [slotLimbs6]
  -- the `hp` hypothesis at the six-limb register layout (`|ds| = 6`).
  have hp6 : valLimbs p384Limbs < (2 ^ 64) ^ ds.length := by rw [hda, hav]; simpa [slotLimbs6] using hp
  have hcore := p384_modsub_runBlock ds ss av bv s2 hda hsb hab hfresh hdmap hsmap
    hcf_s2 hp6 ha_red hb_red
  exact hcore

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6FieldOps
