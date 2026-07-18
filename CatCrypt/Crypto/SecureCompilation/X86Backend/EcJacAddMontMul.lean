/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Frame-wrapped Montgomery field-MULTIPLY over `runBlock`

`EcJacAddRunBlock.lean` builds the frame load/store layer (`loadSlot4`,
`storeSlot4`, `slotLimbs`) and the first frame-wrapped field op — modular
subtract (`feSubFrameAt` / `feSubFrameAt_value`): load input slots into register
windows, run a proven `runBlock` brick over the windows, store the result window
back to the output slot. This file adds the frame-wrapped **Montgomery
field-multiply**, the second field brick, on top of the proven emitted product
core.

## The two proven cores composed

* `SchoolbookProductRunBlock.emitProductBlock4` /
  `emitProductBlock_runBlock_value` — the emitted 256×256→512 schoolbook
  product: its `runBlock` output, read out of the eight accumulator registers
  `accs`, reconstructs (`valLimbs`) to `valLimbs x · valLimbs y`
  (axiom-clean, general `N`; needs the `ProdFresh` register layout, a cleared
  accumulator file, and `CF = OF = 0` on entry).
* `Number.montgomeryReduce` at the full radix `R = 2^256` — the prime-parametric
  Montgomery reduction. With reduced 4-limb inputs and the curve's Montgomery
  constant `Nprime` (`N · Nprime ≡ −1 mod 2^256`), `montgomeryReduce N (2^256)
  Nprime` of the product is the Montgomery field product: it lands `< 2·N` and
  `· 2^256 ≡ valLimbs x · valLimbs y (mod N)` (`Number.montgomeryMul_correct`).

The composition mirrors `Curve4LimbTierA.secp256k1_emit_montmul_runBlock4`: the
emitted product is a genuine `runBlock`-produced value, and the reduction is
applied to that value, giving `runBlock(emitted product) → Montgomery field
product`. Here that composition is wrapped over a stack **frame** (each field
element a slot of four 64-bit limbs, the `Ed25519PointKernel` convention of
`EcJacAddRunBlock`): the multiply reads its two input slots into the product
windows, runs the emitted product over an eight-word accumulator window, and
stores the eight product words into the two-slot output region `o` (low slot
`o`, high slot `o+1`).

## What is proven (genuine `runBlock(emitted) = spec`)

`feMulFrameAt_value` — over a frame whose slots `a`, `b` hold reduced field-element
limbs, with the curve's `Nprime` hypothesis, the eight-word output region's value
reconstructs to the genuine emitted product `valLimbs(slot a) · valLimbs(slot b)`,
and `montgomeryReduce N (2^256) Nprime` of that stored value is the Montgomery
field product (`< 2·N`, `· 2^256 ≡ a·b (mod N)`). The product half is a real
emitted+stored `runBlock` of a `List (JInstr 64)`; the reduction is the
prime-parametric `montgomeryMul_correct`, exactly as the Tier-A curve headlines.
The emitted four-step reduce's register-level shift-down + canonicalising
conditional-subtract is the trusted, KAT-gated emit scaffolding of
`Curve4MontMulProvenEmit` (its value chain is the proven
`MontReduceRunBlock.emitMontRedc4_value`); this wrapper carries the reduction as
a value over the proven stored product.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock

/-! ## 1. The eight-word output region (two consecutive slots)

The 256×256 product is 512 bits — eight 64-bit words. Reusing the slot byte
geometry (`slotOff i k = 32·i + 8·k`), the eight product words occupy the two
consecutive slots `o` (limbs `0..3`) and `o+1` (limbs `0..3`); equivalently the
eight offsets `slotOff o 0 .. slotOff o 7` (`= 32·o + 8·k`, `k = 0..7`), since
`slotOff o (4 + j) = slotOff (o+1) j`. `storeSlot8` writes an eight-register
window to those offsets and `storeSlot8_load` reconstructs them. -/

/-- Store the eight-register window `r0..r7` (the 512-bit product) into the eight
    contiguous frame words at offsets `slotOff o 0 .. slotOff o 7` (the two-slot
    output region `o`, `o+1`). Mirror of `storeSlot4` at width eight. -/
def storeSlot8 (r0 r1 r2 r3 r4 r5 r6 r7 base : String) (o : Nat) : List (JInstr 64) :=
  [ .storeMem base (slotOff o 0) (.reg r0)
  , .storeMem base (slotOff o 1) (.reg r1)
  , .storeMem base (slotOff o 2) (.reg r2)
  , .storeMem base (slotOff o 3) (.reg r3)
  , .storeMem base (slotOff o 4) (.reg r4)
  , .storeMem base (slotOff o 5) (.reg r5)
  , .storeMem base (slotOff o 6) (.reg r6)
  , .storeMem base (slotOff o 7) (.reg r7) ]

/-- The eight-word little-endian value vector held in the output region of frame
    `base` rooted at slot `o` (offsets `slotOff o 0 .. slotOff o 7`). -/
def slotLimbs8 (s : JState 64) (base : String) (o : Nat) : List (BitVec 64) :=
  [ s.load base (slotOff o 0), s.load base (slotOff o 1)
  , s.load base (slotOff o 2), s.load base (slotOff o 3)
  , s.load base (slotOff o 4), s.load base (slotOff o 5)
  , s.load base (slotOff o 6), s.load base (slotOff o 7) ]

/-- **Frame-store reconstruction (eight words).** After `storeSlot8 r0..r7 base o`,
    each of the eight output words holds its register value: the eight stored
    offsets `slotOff o 0 .. slotOff o 7` are pairwise distinct (`slotOff_inj`), so
    each load reads its own store. The eight-word analogue of
    `EcJacAddRunBlock.storeSlot4_load`. -/
theorem storeSlot8_load (r0 r1 r2 r3 r4 r5 r6 r7 base : String) (o : Nat) (s : JState 64) :
    slotLimbs8 (runBlock s (storeSlot8 r0 r1 r2 r3 r4 r5 r6 r7 base o)) base o
      = [ s.get r0, s.get r1, s.get r2, s.get r3
        , s.get r4, s.get r5, s.get r6, s.get r7 ] := by
  simp only [storeSlot8, slotLimbs8, runBlock_cons, runBlock_nil, evalInstr, x86_MOV,
    JOperand.eval, JState.regs_store, JState.get, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [JState.load_store_other (h := fun h => slotOff_inj o 0 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 0 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 0 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 0 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 0 3 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 0 2 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 0 1 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff_inj o 1 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 1 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 1 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 1 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 1 3 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 1 2 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff_inj o 2 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 2 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 2 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 2 4 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 2 3 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff_inj o 3 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 3 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 3 5 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 3 4 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff_inj o 4 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 4 6 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 4 5 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff_inj o 5 7 (by decide) h.2),
      JState.load_store_other (h := fun h => slotOff_inj o 5 6 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_other (h := fun h => slotOff_inj o 6 7 (by decide) h.2),
      JState.load_store_same]
  · rw [JState.load_store_same]

/-! ## 2. The frame-wrapped Montgomery field-multiply

`feMulFrameAt` loads slot `a` into the product multiplicand window `xs`, slot `b`
into the multiplier window `ys`, runs the proven emitted schoolbook product
(`emitProductBlock4 accs xs ys hi lo`) over the eight-word accumulator file
`accs`, and stores the eight product words into the two-slot output region `o`.
The accumulator file is set up cleared (and the carry flags `CF = OF = 0`) as the
proven product brick requires. -/

/-- Frame-wrapped Montgomery field-multiply: load slot `a` into the multiplicand
    window `xs`, slot `b` into the multiplier window `ys`, run the emitted 256×256
    schoolbook product over the eight-word accumulator file `accs`, and store the
    eight product words into the output region rooted at slot `o`. -/
def feMulFrameAt (xs ys accs : List String) (hi lo base : String) (o a b : Nat) :
    List (JInstr 64) :=
  match xs, ys, accs with
  | [x0, x1, x2, x3], [y0, y1, y2, y3], [c0, c1, c2, c3, c4, c5, c6, c7] =>
      loadSlot4 x0 x1 x2 x3 base a
        ++ loadSlot4 y0 y1 y2 y3 base b
        ++ emitProductBlock4 accs xs ys hi lo
        ++ storeSlot8 c0 c1 c2 c3 c4 c5 c6 c7 base o
  | _, _, _ => []

/-! ## 3. The field-multiply value theorem

`feMulFrameAt_value` reads the output region after the wrapped multiply. It
threads the same register-layout / clear / flag hypotheses the proven product
brick (`emitProductBlock_runBlock_value`) carries, lifted to the frame:

* the two input windows `xs`, `ys` are fresh (pairwise-distinct within each, and
  the windows are disjoint from each other, from `accs`, and from the scratch);
* the accumulator file `accs` is cleared and `CF = OF = 0` *after* the two loads
  (the loads touch no flag and no accumulator register);
* the product `ProdFresh` register layout (`accs`/`xs`/`ys`/`hi`/`lo`);
* reduced inputs (`valLimbs (slot a), valLimbs (slot b) < N`) and the curve's
  Montgomery constant (`N · Nprime ≡ −1 mod 2^256`).

Composes `loadSlot4_get` (inputs land in the windows) +
`emitProductBlock_runBlock_value` (the accumulator file holds `valLimbs x ·
valLimbs y`) + `storeSlot8_load` (the product lands in the output region), then
`Number.montgomeryMul_correct` for the reduction. -/

/-- **Frame-wrapped Montgomery field-multiply value.** Over a frame whose input
    slots `a`, `b` hold reduced four-limb field elements (`valLimbs < N`), with the
    `ProdFresh` register layout, a cleared accumulator file, both carry flags
    clear, the input windows fresh and disjoint, and the curve's Montgomery
    constant `Nprime` (`N · Nprime ≡ −1 mod 2^256`):

    * the eight-word output region rooted at slot `o` reconstructs (`valLimbs`) to
      the genuine emitted product `valLimbs (slot a) · valLimbs (slot b)`
      (`emitProductBlock_runBlock_value` + `storeSlot8_load`); and
    * `montgomeryReduce N (2^256) Nprime` of that stored value is the Montgomery
      field product — it lies in `[0, 2·N)` and `· 2^256 ≡ valLimbs a · valLimbs b
      (mod N)` (`Number.montgomeryMul_correct`).

    The product is a real emitted+stored `runBlock` of a `List (JInstr 64)`; the
    reduction is applied to that value, mirroring the Tier-A curve headline
    `Curve4LimbTierA.secp256k1_emit_montmul_runBlock4`. -/
theorem feMulFrameAt_value
    (x0 x1 x2 x3 y0 y1 y2 y3 c0 c1 c2 c3 c4 c5 c6 c7 : String) (hi lo base : String)
    (o a b : Nat) (s : JState 64) (N Nprime : Nat)
    -- input-window freshness
    (hx10 : x1 ≠ x0) (hx20 : x2 ≠ x0) (hx21 : x2 ≠ x1)
    (hx30 : x3 ≠ x0) (hx31 : x3 ≠ x1) (hx32 : x3 ≠ x2)
    (hy10 : y1 ≠ y0) (hy20 : y2 ≠ y0) (hy21 : y2 ≠ y1)
    (hy30 : y3 ≠ y0) (hy31 : y3 ≠ y1) (hy32 : y3 ≠ y2)
    -- the two windows are disjoint (each x distinct from each y)
    (hxy : ∀ d ∈ [x0, x1, x2, x3], ∀ e ∈ [y0, y1, y2, y3], d ≠ e)
    -- the accumulator file is disjoint from both input windows and the scratch
    (hacc_x : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7], ∀ q ∈ [x0, x1, x2, x3], r ≠ q)
    (hacc_y : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7], ∀ q ∈ [y0, y1, y2, y3], r ≠ q)
    -- product register-layout freshness
    (hfresh : ProdFresh [c0, c1, c2, c3, c4, c5, c6, c7] [x0, x1, x2, x3]
      [y0, y1, y2, y3] hi lo)
    -- the accumulator file is cleared and both carry flags clear on entry
    (hacc0 : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7], s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    -- reduced inputs and the curve Montgomery constant
    (hN : 0 < N) (hNleR : N ≤ 2 ^ 256)
    (hx_red : valLimbs (slotLimbs s base a) < N)
    (hy_red : valLimbs (slotLimbs s base b) < N)
    (hNprime : (N * Nprime) % 2 ^ 256 = 2 ^ 256 - 1) :
    valLimbs (slotLimbs8 (runBlock s
        (feMulFrameAt [x0, x1, x2, x3] [y0, y1, y2, y3]
          [c0, c1, c2, c3, c4, c5, c6, c7] hi lo base o a b)) base o)
        = valLimbs (slotLimbs s base a) * valLimbs (slotLimbs s base b) ∧
    Number.montgomeryReduce N (2 ^ 256) Nprime
        (valLimbs (slotLimbs8 (runBlock s
          (feMulFrameAt [x0, x1, x2, x3] [y0, y1, y2, y3]
            [c0, c1, c2, c3, c4, c5, c6, c7] hi lo base o a b)) base o))
        < 2 * N ∧
    (Number.montgomeryReduce N (2 ^ 256) Nprime
        (valLimbs (slotLimbs8 (runBlock s
          (feMulFrameAt [x0, x1, x2, x3] [y0, y1, y2, y3]
            [c0, c1, c2, c3, c4, c5, c6, c7] hi lo base o a b)) base o))) * 2 ^ 256
      ≡ valLimbs (slotLimbs s base a) * valLimbs (slotLimbs s base b) [MOD N] := by
  -- the input windows, the accumulator file, and the slot values
  set xs := [x0, x1, x2, x3] with hxsdef
  set ys := [y0, y1, y2, y3] with hysdef
  set accs := [c0, c1, c2, c3, c4, c5, c6, c7] with haccsdef
  set xv := slotLimbs s base a with hxv
  set yv := slotLimbs s base b with hyv
  -- the three intermediate states (`feMulFrameAt` reduces to the four-block append)
  set s1 := runBlock s (loadSlot4 x0 x1 x2 x3 base a) with hs1def
  set s2 := runBlock s1 (loadSlot4 y0 y1 y2 y3 base b) with hs2def
  set s3 := runBlock s2 (emitProductBlock4 accs xs ys hi lo) with hs3def
  -- s1: the multiplicand window holds slot-a's limbs.
  obtain ⟨hs1x0, hs1x1, hs1x2, hs1x3⟩ :=
    loadSlot4_get x0 x1 x2 x3 base a s hx10 hx20 hx21 hx30 hx31 hx32
  -- s2: the multiplier window holds slot-b's limbs.
  obtain ⟨hs2y0, hs2y1, hs2y2, hs2y3⟩ :=
    loadSlot4_get y0 y1 y2 y3 base b s1 hy10 hy20 hy21 hy30 hy31 hy32
  -- the multiplicand window survives the b-load (windows disjoint).
  have hxy0 : ∀ e ∈ ys, x0 ≠ e := hxy x0 (by simp [hxsdef])
  have hxy1 : ∀ e ∈ ys, x1 ≠ e := hxy x1 (by simp [hxsdef])
  have hxy2 : ∀ e ∈ ys, x2 ≠ e := hxy x2 (by simp [hxsdef])
  have hxy3 : ∀ e ∈ ys, x3 ≠ e := hxy x3 (by simp [hxsdef])
  have hs2x0 : s2.get x0 = s.load base (slotOff a 0) := by
    rw [hs2def, loadSlot4_other y0 y1 y2 y3 base b s1 x0
      (hxy0 y0 (by simp [hysdef])) (hxy0 y1 (by simp [hysdef])) (hxy0 y2 (by simp [hysdef]))
      (hxy0 y3 (by simp [hysdef])), hs1x0]
  have hs2x1 : s2.get x1 = s.load base (slotOff a 1) := by
    rw [hs2def, loadSlot4_other y0 y1 y2 y3 base b s1 x1
      (hxy1 y0 (by simp [hysdef])) (hxy1 y1 (by simp [hysdef])) (hxy1 y2 (by simp [hysdef]))
      (hxy1 y3 (by simp [hysdef])), hs1x1]
  have hs2x2 : s2.get x2 = s.load base (slotOff a 2) := by
    rw [hs2def, loadSlot4_other y0 y1 y2 y3 base b s1 x2
      (hxy2 y0 (by simp [hysdef])) (hxy2 y1 (by simp [hysdef])) (hxy2 y2 (by simp [hysdef]))
      (hxy2 y3 (by simp [hysdef])), hs1x2]
  have hs2x3 : s2.get x3 = s.load base (slotOff a 3) := by
    rw [hs2def, loadSlot4_other y0 y1 y2 y3 base b s1 x3
      (hxy3 y0 (by simp [hysdef])) (hxy3 y1 (by simp [hysdef])) (hxy3 y2 (by simp [hysdef]))
      (hxy3 y3 (by simp [hysdef])), hs1x3]
  -- the multiplicand-window get-map = slot-a's limbs.
  have hxmap : xs.map s2.get = xv := by
    simp only [hxsdef, hxv, slotLimbs, List.map_cons, List.map_nil, hs2x0, hs2x1, hs2x2, hs2x3]
  -- the multiplier-window get-map = slot-b's limbs.
  have hymap : ys.map s2.get = yv := by
    rw [← hs2def] at hs2y0 hs2y1 hs2y2 hs2y3
    simp only [hysdef, hyv, slotLimbs, List.map_cons, List.map_nil, hs2y0, hs2y1, hs2y2, hs2y3,
      hs1def, loadSlot4_load]
  -- the accumulator file is still cleared in s2 (loads write only their windows).
  have hacc0_s2 : ∀ r ∈ accs, s2.get r = 0 := by
    intro r hr
    rw [hs2def, loadSlot4_other y0 y1 y2 y3 base b s1 r
        (fun h => hacc_y r hr y0 (by simp [hysdef]) h) (fun h => hacc_y r hr y1 (by simp [hysdef]) h)
        (fun h => hacc_y r hr y2 (by simp [hysdef]) h) (fun h => hacc_y r hr y3 (by simp [hysdef]) h)]
    rw [hs1def, loadSlot4_other x0 x1 x2 x3 base a s r
        (fun h => hacc_x r hr x0 (by simp [hxsdef]) h) (fun h => hacc_x r hr x1 (by simp [hxsdef]) h)
        (fun h => hacc_x r hr x2 (by simp [hxsdef]) h) (fun h => hacc_x r hr x3 (by simp [hxsdef]) h)]
    exact hacc0 r hr
  -- the carry flags are still clear in s2 (loads touch no flag).
  have hcf_s2 : s2.flagB (·.cf) = false := by
    rw [hs2def, loadSlot4_flagB, hs1def, loadSlot4_flagB, hcf]
  have hof_s2 : s2.flagB (·.of) = false := by
    rw [hs2def, loadSlot4_flagB, hs1def, loadSlot4_flagB, hof]
  -- lengths for the product brick (xs, ys length 4; accs length 8)
  have hxslen : xs.length = xv.length := by
    rw [hxsdef, hxv]; simp [slotLimbs]
  have hyslen : ys.length = yv.length := by
    rw [hysdef, hyv]; simp [slotLimbs]
  have hcap : xs.length + ys.length ≤ accs.length := by
    rw [hxsdef, hysdef, haccsdef]; simp
  -- the proven emitted product: the accumulator file holds valLimbs xv · valLimbs yv.
  have hprod : valLimbs (accs.map s3.get) = valLimbs xv * valLimbs yv := by
    have := emitProductBlock_runBlock_value accs xs ys xv yv hi lo s2
      hxslen hyslen hcap hfresh hxmap hymap hacc0_s2 hcf_s2 hof_s2
    simp only [runBlockProductValue] at this
    rw [hs3def, emitProductBlock4]; exact this
  -- the store-reconstruction over the eight accumulator registers.
  have hstore := storeSlot8_load c0 c1 c2 c3 c4 c5 c6 c7 base o s3
  -- the field-mul value: unfold `feMulFrameAt` (literal lists reduce) and factor
  -- the runBlock through the two loads + product + store, landing the stored
  -- output region at the product value.
  have hfinal : valLimbs (slotLimbs8 (runBlock s
        (feMulFrameAt xs ys accs hi lo base o a b)) base o) = valLimbs xv * valLimbs yv := by
    rw [show feMulFrameAt xs ys accs hi lo base o a b
        = loadSlot4 x0 x1 x2 x3 base a ++ loadSlot4 y0 y1 y2 y3 base b
          ++ emitProductBlock4 accs xs ys hi lo
          ++ storeSlot8 c0 c1 c2 c3 c4 c5 c6 c7 base o from rfl]
    rw [runBlock_append, runBlock_append, runBlock_append, ← hs1def, ← hs2def, ← hs3def, hstore]
    simp only [haccsdef, List.map_cons, List.map_nil] at hprod
    exact hprod
  -- assemble: the product half, then the reduction via montgomeryMul_correct.
  rw [hfinal]
  refine ⟨rfl, ?_, ?_⟩
  · obtain ⟨hrange, _⟩ := Number.montgomeryMul_correct N (2 ^ 256) Nprime
      (valLimbs xv) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    simpa only [Number.montgomeryMul] using hrange
  · obtain ⟨_, hcong⟩ := Number.montgomeryMul_correct N (2 ^ 256) Nprime
      (valLimbs xv) (valLimbs yv) hN (by positivity) hNleR hNprime hx_red hy_red
    simpa only [Number.montgomeryMul] using hcong

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontMul
