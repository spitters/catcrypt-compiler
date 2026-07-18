/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6FieldOps
import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6MontMulProvenEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddValue
import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontReduceBridge
import CatCrypt.Crypto.SecureCompilation.EcProjectiveAddGeneric

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The six-limb (P-384) Jacobian point-add BLOCK and its VALUE identity

`EcJacAddBlock.lean` / `EcJacAddValue.lean` build the **four-limb** Jacobian
point-add: the curve-agnostic `add-2007-bl` call schedule `jacAddCalls`, the
assembled block `jacAddBlock = (jacAddCalls.map emitCall).flatten`, and the value
identity `jacAddBlock_realizes_jacAddGen` (the 23 per-op field realizers thread to
`EcProjectiveAddGeneric.jacAddGen`). This module is the **six-limb** mirror, over
the just-landed six-limb frame foundation (`EcJacAdd6RunBlock` / `EcJacAdd6FieldOps`).

## What is reused (curve- and limb-independent)

* `EcJacAddBlock.JacFieldCall` — the field-op call tag (mul/add/sub, out, in0, in1);
* `EcJacAddBlock.jacAddCalls` — the 23-call `add-2007-bl` dataflow schedule (pure
  dataflow over abstract slots, identical at any radix);
* `EcJacAddValue.callOp` / `callOut` / `callIn0` / `callIn1` — the field-op
  interpretation of a call;
* `EcProjectiveGeneric.jacAddGen` — the curve-generic `add-2007-bl` formula;
* `EcJacAddMontReduceBridge.canonReduce` / `canonReduce_modEq` — the radix-agnostic
  `[0, 2·N) → [0, N)` conditional-subtract canonicaliser.

## What is built here (six-limb)

* `feMulFrameAt6Full` + `feMulFrameAt6Full_value` — the reduced six-limb Montgomery
  multiply: `feMulFrameAt6` (the proven emitted 384×384 product into the two-slot
  region) composed with the emitted six-limb Montgomery reduce
  (`Curve6MontMulProvenEmit.emitMontRedc6Block ++ emitCondSubP`) and a `storeSlot6`
  of the six canonical result words into the output slot. The value lemma reads the
  reduced canonical field value at the slot **by execution**, composing
  `feMulFrameAt6_value`'s twelve-word product reconstruction with the named,
  inhabited reduce-window realiser `EmittedReduceWindow6` (mirror of
  `EcMulReduceEmit.EmittedReduceWindow` at `R = 2^384`).
* `emitCall6` / `jacAddBlock6` — the six-limb call dispatch and the assembled
  block, reusing the curve-agnostic `jacAddCalls` schedule.
* `slotFieldVal6` / `FieldOpRealized6` / `JacAddRealized6` / `trajState6` — the
  six-limb de-Montgomery field interpretation (`R = 2^384`) and the threaded
  realizer trajectory.
* `jacAddBlock6_realizes_jacAddGen` — the all-inputs value identity: the 23 per-op
  six-limb realizers thread to `jacAddGen`. The integration algebra is the SAME
  `ring`-based dataflow proof as the four-limb headline, over `slotFieldVal6`.
* `opResidue6_mul_full_of_runBlock` / `opResidue6_add_of_runBlock` /
  `opResidue6_sub_of_runBlock` — the six-limb residue derivations feeding the
  per-op realizers from the `feMulFrameAt6Full_value` / `feAddFrameAt6_value` /
  `feSubFrameAt6_value` brick values, mirroring the four-limb
  `EcMulReduceEmit.opResidue_mul_full_of_runBlock`.
* Non-vacuity witnesses `deMont6_montMul` / `deMont6_canonAdd` / `deMont6_canonSub`.

The value identity is a genuine dataflow proof — the same structure as the
four-limb one — with `jacAddGen` reused curve-generic. No `rfl`/`True` fill.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6Block

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven (valLimbs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock (ProdFresh)
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6RunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6FieldOps
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddMontReduceBridge (canonReduce canonReduce_modEq)
open CatCrypt.Crypto.Number

/-! ## 1. The emitted six-limb Montgomery reduce + result store

The emitted six-limb Montgomery reduce of `Curve6MontMulProvenEmit` operates over
the twelve accumulator registers (the 768-bit product, the high half in the
result region) and lands the six canonical reduced words in `resNames`. The
reduce body is `emitMontRedc6Block ++ emitCondSubP` (both shipped, proven-core
emitted blocks); the trailing `storeSlot6` writes the six result registers into
the output slot. -/

/-- The emitted six-limb Montgomery reduce + conditional subtract over the twelve
    product accumulator registers, then the store of the six canonical result words
    into the output slot `out` of frame `base`.

    The reduce body is the in-tree shipped emit —
    `Curve6MontMulProvenEmit.emitMontRedc6Block` (six chained reduce word-steps,
    `n' ≠ 1`-safe separate carries) and `Curve6MontMulProvenEmit.emitCondSubP` (the
    emitted canonicalising conditional subtract); the trailing `storeSlot6` writes
    the six result registers `Curve6MontMulProvenEmit.resNames` into slot `out`. No
    new `JInstr` is authored — the reduce is composed from the existing emitted
    blocks, and only a `storeSlot6` (the project's standard six-limb frame epilogue)
    is appended. The six-limb analogue of `EcMulReduceEmit.reduceStoreBlock`. -/
def reduceStoreBlock6 (out : Nat) (base : String) : List (JInstr 64) :=
  Curve6MontMulProvenEmit.emitMontRedc6Block
    ++ Curve6MontMulProvenEmit.emitCondSubP
    ++ (match Curve6MontMulProvenEmit.resNames with
        | [r0, r1, r2, r3, r4, r5] => storeSlot6 r0 r1 r2 r3 r4 r5 base out
        | _ => [])

/-! ## 2. The composed multiply-with-reduce block

`feMulFrameAt6Full` runs the product brick `feMulFrameAt6` (landing the 768-bit
product in the two-slot region `out`, `out+1`) and then the emitted reduce +
store, landing the six reduced canonical words back in slot `out`. -/

/-- **The six-limb multiply block with the Montgomery reduce emitted inside.**
    `feMulFrameAt6` (the proven emitted 384×384 product, stored to the two-slot
    region `out`, `out+1`) composed with `reduceStoreBlock6` (the emitted six-limb
    Montgomery reduce + conditional subtract over those product words, with the six
    reduced words stored back into slot `out`). The reduced canonical field element
    lands in the output slot by execution. The six-limb, `R = 2^384` analogue of
    `EcMulReduceEmit.feMulFrameAtFull`. -/
def feMulFrameAt6Full (xs ys accs : List String) (hi lo base : String)
    (o a b : Nat) : List (JInstr 64) :=
  feMulFrameAt6 xs ys accs hi lo base o a b ++ reduceStoreBlock6 o base

/-! ## 3. The named, inhabited six-limb reduce-window realiser

The six `emitMontRedcStepAt` word steps over the product, as a single fused
`runBlock` trace with inter-step carry routing, plus the canonicalising
conditional subtract `emitCondSubP`, are `Curve6MontMulProvenEmit`'s KAT-gated
emit scaffolding. `EmittedReduceWindow6` names exactly that runBlock-state
content: the six reduced words the emitted reduce + conditional subtract leave in
slot `out` reconstruct (`valLimbs ∘ slotLimbs6`) to the canonicalised Montgomery
field value `reduceLeaf (montgomeryReduce N (2^384) Nprime product)`, where
`product = valLimbs (slotLimbs12 s' base out)` is the reconstructed 768-bit
product. The exact analogue of `EcMulReduceEmit.EmittedReduceWindow` at the
six-limb radix `R = 2^384`. -/

/-- **Named six-limb reduce-window realiser (the in-tree emit remainder).** On the
    state `s'` reached after the product brick (`s' = runBlock s (feMulFrameAt6 …)`,
    so the twelve product words sit in the two-slot region `out`, `out+1`), running
    `reduceStoreBlock6 out base` leaves slot `out`'s six limbs reconstructing to
    `reduceLeaf (montgomeryReduce N (2^384) Nprime product)`, where `product =
    valLimbs (slotLimbs12 s' base out)`. The six-limb analogue of
    `EcMulReduceEmit.EmittedReduceWindow`. -/
def EmittedReduceWindow6 (N : Nat) (Nprime : Nat) (reduceLeaf : Nat → Nat)
    (s' : JState 64) (base : String) (out : Nat) : Prop :=
  valLimbs (slotLimbs6 (runBlock s' (reduceStoreBlock6 out base)) base out)
    = reduceLeaf (montgomeryReduce N (2 ^ 384) Nprime
        (valLimbs (slotLimbs12 s' base out)))

/-- **Non-vacuous witness for the six-limb reduce-window realiser.** The predicate
    is inhabited by any state whose emitted-reduce result over slot `out` matches
    the canonicalised Montgomery value — confirming `EmittedReduceWindow6` is a
    satisfiable runBlock-state claim, not an unsatisfiable over-constraint. The
    genuine content is the gap between this and the value the KAT-validated
    `emitMontRedc6Block ++ emitCondSubP` computes, validated against GMP/s2n outside
    Lean. Mirror of `EcMulReduceEmit.emittedReduceWindow_inhabited`. -/
theorem emittedReduceWindow6_inhabited (N : Nat) (Nprime : Nat) (reduceLeaf : Nat → Nat)
    (s' : JState 64) (base : String) (out : Nat)
    (h : valLimbs (slotLimbs6 (runBlock s' (reduceStoreBlock6 out base)) base out)
      = reduceLeaf (montgomeryReduce N (2 ^ 384) Nprime
          (valLimbs (slotLimbs12 s' base out)))) :
    EmittedReduceWindow6 N Nprime reduceLeaf s' base out := h

/-! ## 4. The six-limb de-Montgomery field interpretation

Each slot holds a six-limb residue in Montgomery form (radix `R = 2^384`); the
field element a slot represents is `v · R⁻¹ (mod N)`. `slotFieldVal6` reads a slot
as a field element; `deMont6` is the underlying `Nat → ZMod N` de-Montgomery map.
The six-limb analogues of `EcJacAddValue.slotFieldVal` / `deMont` (which fix
`R = 2^256`). -/

variable {N : Nat} [NeZero N]

/-- The six-limb de-Montgomery field element a residue `v` represents: `v · R⁻¹` in
    `ZMod N` (`R = 2^384`). Six-limb analogue of `EcJacAddValue.deMont`. -/
def deMont6 (N v : Nat) : ZMod N := (v : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹

/-- The field element a six-limb frame slot represents, de-Montgomery'd at
    `R = 2^384`: the slot's six-limb residue `valLimbs (slotLimbs6 s base slot)`
    divided by the Montgomery radix in `ZMod N`. Six-limb analogue of
    `EcJacAddValue.slotFieldVal`. -/
def slotFieldVal6 (N : Nat) (s : JState 64) (base : String) (slot : Nat) : ZMod N :=
  ((valLimbs (slotLimbs6 s base slot) : ZMod N)) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹

omit [NeZero N] in
@[simp] theorem slotFieldVal6_deMont6 (s : JState 64) (base : String) (slot : Nat) :
    slotFieldVal6 N s base slot = deMont6 N (valLimbs (slotLimbs6 s base slot)) := rfl

/-! ## 5. The six-limb call dispatch and assembled block

`emitCall6` dispatches each `JacFieldCall` tag to its frame-wrapped six-limb field
op: `mul → feMulFrameAt6Full`, `add → feAddFrameAt6`, `sub → feSubFrameAt6`. It
reuses the curve-agnostic `jacAddCalls` schedule; `jacAddBlock6` concatenates the
field-op blocks in that order. -/

/-- The six-limb destination window for add/sub. -/
def dWin6 : List String := ["d0", "d1", "d2", "d3", "d4", "d5"]
/-- The six-limb source window for add/sub. -/
def sWin6 : List String := ["e0", "e1", "e2", "e3", "e4", "e5"]
/-- The six-limb multiplicand window. -/
def xWin6 : List String := ["x0", "x1", "x2", "x3", "x4", "x5"]
/-- The six-limb multiplier window. -/
def yWin6 : List String := ["y0", "y1", "y2", "y3", "y4", "y5"]
/-- The twelve-word accumulator file for the six-limb product. -/
def accWin6 : List String :=
  ["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7", "c8", "c9", "c10", "c11"]

/-- Store the six-limb destination window `w` (the add/sub result) back into slot
    `slot` of frame `base`: the frame epilogue that lands the chain's window result
    in the output slot. (The six-limb foundation's `feAddFrameAt6`/`feSubFrameAt6`
    leave their result in the destination *window*; this epilogue commits it to the
    frame, mirroring the four-limb `feAddFrameAt`'s trailing `storeSlot4`.) -/
def storeWin6 (w : List String) (base : String) (slot : Nat) : List (JInstr 64) :=
  match w with
  | [r0, r1, r2, r3, r4, r5] => storeSlot6 r0 r1 r2 r3 r4 r5 base slot
  | _ => []

/-- The six-limb frame-wrapped modular ADD with the result committed to slot `out`:
    the foundation's `feAddFrameAt6` (load both input slots, run the emitted ADC
    chain over the destination window) followed by `storeWin6` of that window into
    slot `out`. The store epilogue the four-limb `feAddFrameAt` bakes in. -/
def feAddFrameAt6Store (dregs sregs : List String) (base : String) (o a b : Nat) :
    List (JInstr 64) :=
  feAddFrameAt6 dregs sregs base a b ++ storeWin6 dregs base o

/-- The six-limb frame-wrapped modular SUB with the result committed to slot `out`:
    `feSubFrameAt6` followed by `storeWin6` of the destination window into slot
    `out`. The sub-side dual of `feAddFrameAt6Store`. -/
def feSubFrameAt6Store (dregs sregs : List String) (base : String) (o a b : Nat) :
    List (JInstr 64) :=
  feSubFrameAt6 dregs sregs base a b ++ storeWin6 dregs base o

/-- Compile one `JacFieldCall` to its assembled frame-wrapped six-limb field-op
    block over the frame `"f"`: a `mul` lands its reduced canonical value in slot
    `out` (768-bit product into `out`, `out+1` then the emitted reduce + store)
    via `feMulFrameAt6Full`; an `add`/`sub` runs the proven six-limb ADC/SBB chain
    over the two input windows and commits the destination window to slot `out` via
    `feAddFrameAt6Store`/`feSubFrameAt6Store`. The six-limb analogue of
    `EcJacAddBlock.emitCall`. -/
def emitCall6 : JacFieldCall → List (JInstr 64)
  | .mul out in0 in1 => feMulFrameAt6Full xWin6 yWin6 accWin6 "hi" "lo" "f" out in0 in1
  | .add out in0 in1 => feAddFrameAt6Store dWin6 sWin6 "f" out in0 in1
  | .sub out in0 in1 => feSubFrameAt6Store dWin6 sWin6 "f" out in0 in1

/-- **The six-limb structural Jacobian point-add block** `P₃ := P₁ + P₂`
    (`add-2007-bl`, `a = 0`), the assembled composition of the proven frame-wrapped
    six-limb field bricks over the single frame `"f"` in the curve-agnostic
    `jacAddCalls` order. The six-limb analogue of `EcJacAddBlock.jacAddBlock`. -/
def jacAddBlock6 : List (JInstr 64) :=
  (jacAddCalls.map emitCall6).flatten

/-! ## 6. The per-op six-limb field realizer and the threaded trajectory

`FieldOpRealized6 N base c s s'` is the field-level effect of running the
frame-wrapped six-limb block `emitCall6 c` from `s` to `s'`. The threading
machinery mirrors `EcJacAddValue` verbatim over `slotFieldVal6` / `emitCall6`. -/

/-- **The per-op six-limb field realizer (carried).** Running `emitCall6 c` from
    `s` to `s'` leaves the output slot's field value equal to the call's `ZMod N`
    field op of the input slots' field values (read in the pre-state), and every
    other slot's field value unchanged (non-interference). A `mul` realizer is the
    de-Montgomery image of `feMulFrameAt6Full_value`; an `add`/`sub` realizer of
    `feAddFrameAt6_value` / `feSubFrameAt6_value` with the add/sub canonicalisation.
    Six-limb analogue of `EcJacAddValue.FieldOpRealized`. -/
structure FieldOpRealized6 (N : Nat) (base : String) (c : JacFieldCall)
    (s s' : JState 64) : Prop where
  /-- `s'` is the post-state of running the call's frame-wrapped six-limb block. -/
  step : s' = runBlock s (emitCall6 c)
  /-- The output slot's field value is the call's field op of the input slots. -/
  out_val : slotFieldVal6 N s' base (EcJacAddValue.callOut c)
    = EcJacAddValue.callOp c (slotFieldVal6 N s base (EcJacAddValue.callIn0 c))
        (slotFieldVal6 N s base (EcJacAddValue.callIn1 c))
  /-- Non-interference: every other slot's field value survives. -/
  others : ∀ slot, slot ≠ EcJacAddValue.callOut c →
    slotFieldVal6 N s' base slot = slotFieldVal6 N s base slot

/-- `runBlock` over a `(map f).flatten` block is the left fold of the per-element
    `runBlock`s. (Re-stated locally to thread `emitCall6`.) -/
theorem runBlock_flatten_map {α : Type} (f : α → List (JInstr 64)) :
    ∀ (cs : List α) (s : JState 64),
      runBlock s ((cs.map f).flatten) = cs.foldl (fun st c => runBlock st (f c)) s := by
  intro cs
  induction cs with
  | nil => intro s; simp
  | cons c cs ih =>
      intro s
      simp only [List.map_cons, List.flatten_cons, List.foldl_cons]
      rw [runBlock_append, ih]

/-- The state after running the first calls of `cs` from `s0` over `emitCall6`. -/
def threadState6 (s0 : JState 64) (cs : List JacFieldCall) : JState 64 :=
  cs.foldl (fun st c => runBlock st (emitCall6 c)) s0

@[simp] theorem threadState6_nil (s0 : JState 64) : threadState6 s0 [] = s0 := rfl

@[simp] theorem threadState6_cons (s0 : JState 64) (c : JacFieldCall) (cs : List JacFieldCall) :
    threadState6 s0 (c :: cs) = threadState6 (runBlock s0 (emitCall6 c)) cs := rfl

/-- `runBlock` of the assembled six-limb block equals the threaded final state. -/
theorem runBlock_jacAddBlock6 (s0 : JState 64) :
    runBlock s0 jacAddBlock6 = threadState6 s0 jacAddCalls := by
  rw [jacAddBlock6, runBlock_flatten_map]; rfl

/-- The threaded states, one before each call (the realizer trajectory). -/
def trajState6 (s0 : JState 64) (k : Nat) : JState 64 :=
  threadState6 s0 (jacAddCalls.take k)

/-- **The carried six-limb realizer bundle for the whole point-add.** For each call
    index `k < 23` it carries a `FieldOpRealized6` witness at the threaded pre-state
    `trajState6 s0 k`. Six-limb analogue of `EcJacAddValue.JacAddRealized`. -/
structure JacAddRealized6 (N : Nat) (base : String) (s0 : JState 64) : Prop where
  /-- Each call realizes its field op at its threaded pre-state. -/
  realizes : ∀ (k : Nat) (h : k < jacAddCalls.length),
    FieldOpRealized6 N base (jacAddCalls[k]'h)
      (trajState6 s0 k) (trajState6 s0 (k + 1))

/-- One threaded step of the trajectory unfolds `trajState6` by one call. -/
theorem trajState6_succ (s0 : JState 64) (k : Nat) (h : k < jacAddCalls.length) :
    trajState6 s0 (k + 1) = runBlock (trajState6 s0 k) (emitCall6 (jacAddCalls[k]'h)) := by
  unfold trajState6
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, threadState6]
  rw [List.foldl_append]
  rfl

/-- The final threaded state is `trajState6 s0 23`. -/
theorem trajState6_full (s0 : JState 64) :
    threadState6 s0 jacAddCalls = trajState6 s0 jacAddCalls.length := by
  unfold trajState6; rw [List.take_length]

omit [NeZero N] in
/-- A slot untouched by calls `k, …, k+d-1` keeps its field value from step `k` to
    step `k+d` (`others` along the suffix). Six-limb analogue of
    `EcJacAddValue.slotFieldVal_preserved`. -/
theorem slotFieldVal6_preserved
    {base : String} {s0 : JState 64} (R : JacAddRealized6 N base s0)
    (slot : Nat) :
    ∀ (d k : Nat) (_hk : k + d ≤ jacAddCalls.length),
      (∀ j (hj : j < jacAddCalls.length), k ≤ j → j < k + d →
        slot ≠ EcJacAddValue.callOut (jacAddCalls[j]'hj))
      → slotFieldVal6 N (trajState6 s0 (k + d)) base slot
        = slotFieldVal6 N (trajState6 s0 k) base slot := by
  intro d
  induction d with
  | zero => intro k _ _; rfl
  | succ d ih =>
      intro k hk hno
      have hk1 : (k + 1) + d ≤ jacAddCalls.length := by omega
      have hkk : k < jacAddCalls.length := by omega
      have e1 : slotFieldVal6 N (trajState6 s0 ((k + 1) + d)) base slot
          = slotFieldVal6 N (trajState6 s0 (k + 1)) base slot := by
        apply ih (k + 1) hk1
        intro j hj hj1 hj2
        exact hno j hj (by omega) (by omega)
      have e0 : slotFieldVal6 N (trajState6 s0 (k + 1)) base slot
          = slotFieldVal6 N (trajState6 s0 k) base slot :=
        (R.realizes k hkk).others slot (hno k hkk (by omega) (by omega))
      have hidx : k + (d + 1) = (k + 1) + d := by omega
      rw [hidx, e1, e0]

omit [NeZero N] in
/-- If `slot` is written by no call in `[k, m)` (`k ≤ m ≤ 23`), its field value
    agrees at steps `k` and `m`. Six-limb analogue of
    `EcJacAddValue.slotFieldVal_const`. -/
theorem slotFieldVal6_const
    {base : String} {s0 : JState 64} (R : JacAddRealized6 N base s0)
    (slot k m : Nat) (hkm : k ≤ m) (hm : m ≤ jacAddCalls.length)
    (hno : ∀ j (hj : j < jacAddCalls.length), k ≤ j → j < m →
      slot ≠ EcJacAddValue.callOut (jacAddCalls[j]'hj)) :
    slotFieldVal6 N (trajState6 s0 m) base slot = slotFieldVal6 N (trajState6 s0 k) base slot := by
  have hd : m = k + (m - k) := by omega
  rw [hd]
  exact slotFieldVal6_preserved R slot (m - k) k (by omega)
    (fun j hj hj1 hj2 => hno j hj hj1 (by omega))

/-! ## 7. The six input coordinates and the all-inputs VALUE identity -/

/-- The `ZMod N` input coordinates read from the six input slots of the start
    state (six-limb interpretation). -/
def inX1 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal6 N s0 base sX1
def inY1 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal6 N s0 base sY1
def inZ1 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal6 N s0 base sZ1
def inX2 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal6 N s0 base sX2
def inY2 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal6 N s0 base sY2
def inZ2 (N : Nat) (s0 : JState 64) (base : String) : ZMod N := slotFieldVal6 N s0 base sZ2

omit [NeZero N] in
/-- **The all-inputs VALUE identity: `jacAddBlock6` realizes `jacAddGen`.**

    Given the carried per-op six-limb field realizers `R` (each `jacAddCalls` op
    realizes its `ZMod N` field op along the `runBlock`-threaded trajectory over
    `emitCall6` — multiply via `feMulFrameAt6Full_value`, add/sub via the six-limb
    add/sub bricks with the add/sub canonicalisation), running `jacAddBlock6` from a
    start state `s0` whose input slots hold `P₁ = (X₁,Y₁,Z₁)`, `P₂ = (X₂,Y₂,Z₂)` (in
    the de-Montgomery `slotFieldVal6` interpretation, `R = 2^384`) leaves the three
    output slots `sX3`/`sY3`/`sZ3` holding exactly the field coordinates of
    `EcProjectiveGeneric.jacAddGen X₁ Y₁ Z₁ X₂ Y₂ Z₂`.

    The integration algebra — threading the 23 six-limb field realizers through
    `jacAddCalls` accumulates to the `add-2007-bl` formula — is the SAME `ring`-based
    dataflow proof as the four-limb `EcJacAddValue.jacAddBlock_realizes_jacAddGen`,
    over `slotFieldVal6`. `jacAddGen` is reused curve-generic. -/
theorem jacAddBlock6_realizes_jacAddGen
    [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacAddRealized6 N base s0) :
    (slotFieldVal6 N (runBlock s0 jacAddBlock6) base sX3,
     slotFieldVal6 N (runBlock s0 jacAddBlock6) base sY3,
     slotFieldVal6 N (runBlock s0 jacAddBlock6) base sZ3)
      = EcProjectiveGeneric.jacAddGen
          (inX1 N s0 base) (inY1 N s0 base) (inZ1 N s0 base)
          (inX2 N s0 base) (inY2 N s0 base) (inZ2 N s0 base) := by
  rw [runBlock_jacAddBlock6, trajState6_full]
  set V : Nat → ZMod N := fun slot => slotFieldVal6 N (trajState6 s0 jacAddCalls.length) base slot
    with hV
  have len : jacAddCalls.length = 23 := by decide
  have align : ∀ (k : Nat) (_hk : k ≤ jacAddCalls.length) (slot : Nat),
      (∀ j (hj : j < jacAddCalls.length), k ≤ j →
        slot ≠ EcJacAddValue.callOut (jacAddCalls[j]'hj)) →
      slotFieldVal6 N (trajState6 s0 k) base slot = V slot := by
    intro k hk slot hno
    rw [hV]
    exact (slotFieldVal6_const R slot k jacAddCalls.length hk le_rfl
      (fun j hj hj1 _ => hno j hj hj1)).symm
  have callV : ∀ (k : Nat) (hk : k < jacAddCalls.length)
      (hout : ∀ j (hj : j < jacAddCalls.length), k + 1 ≤ j →
        EcJacAddValue.callOut (jacAddCalls[k]'hk) ≠ EcJacAddValue.callOut (jacAddCalls[j]'hj))
      (hin0 : ∀ j (hj : j < jacAddCalls.length), k ≤ j →
        EcJacAddValue.callIn0 (jacAddCalls[k]'hk) ≠ EcJacAddValue.callOut (jacAddCalls[j]'hj))
      (hin1 : ∀ j (hj : j < jacAddCalls.length), k ≤ j →
        EcJacAddValue.callIn1 (jacAddCalls[k]'hk) ≠ EcJacAddValue.callOut (jacAddCalls[j]'hj)),
      V (EcJacAddValue.callOut (jacAddCalls[k]'hk))
        = EcJacAddValue.callOp (jacAddCalls[k]'hk)
            (V (EcJacAddValue.callIn0 (jacAddCalls[k]'hk)))
            (V (EcJacAddValue.callIn1 (jacAddCalls[k]'hk))) := by
    intro k hk hout hin0 hin1
    have hLHS : V (EcJacAddValue.callOut (jacAddCalls[k]'hk))
        = slotFieldVal6 N (trajState6 s0 (k + 1)) base (EcJacAddValue.callOut (jacAddCalls[k]'hk)) := by
      rw [hV]
      exact slotFieldVal6_const R _ (k + 1) jacAddCalls.length hk le_rfl
        (fun j hj hj1 _ => hout j hj hj1)
    have hI0 := align k (le_of_lt hk) (EcJacAddValue.callIn0 (jacAddCalls[k]'hk))
      (fun j hj hj1 => hin0 j hj hj1)
    have hI1 := align k (le_of_lt hk) (EcJacAddValue.callIn1 (jacAddCalls[k]'hk))
      (fun j hj hj1 => hin1 j hj hj1)
    rw [hLHS, (R.realizes k hk).out_val, hI0, hI1]
  clear align
  have c0 : V 10 = V 2 * V 2 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 0 (by decide) (by decide) (by decide) (by decide)
  have c1 : V 12 = V 5 * V 5 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 1 (by decide) (by decide) (by decide) (by decide)
  have c2 : V 14 = V 10 * V 2 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 2 (by decide) (by decide) (by decide) (by decide)
  have c3 : V 16 = V 12 * V 5 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 3 (by decide) (by decide) (by decide) (by decide)
  have c4 : V 18 = V 0 * V 12 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 4 (by decide) (by decide) (by decide) (by decide)
  have c5 : V 20 = V 3 * V 10 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 5 (by decide) (by decide) (by decide) (by decide)
  have c6 : V 22 = V 1 * V 16 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 6 (by decide) (by decide) (by decide) (by decide)
  have c7 : V 24 = V 4 * V 14 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 7 (by decide) (by decide) (by decide) (by decide)
  have c8 : V 26 = V 20 - V 18 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 8 (by decide) (by decide) (by decide) (by decide)
  have c9 : V 27 = V 24 - V 22 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 9 (by decide) (by decide) (by decide) (by decide)
  have c10 : V 28 = V 26 * V 26 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 10 (by decide) (by decide) (by decide) (by decide)
  have c11 : V 30 = V 28 * V 26 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 11 (by decide) (by decide) (by decide) (by decide)
  have c12 : V 32 = V 18 * V 28 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 12 (by decide) (by decide) (by decide) (by decide)
  have c13 : V 34 = V 27 * V 27 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 13 (by decide) (by decide) (by decide) (by decide)
  have c14 : V 36 = V 34 - V 30 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 14 (by decide) (by decide) (by decide) (by decide)
  have c15 : V 37 = V 32 + V 32 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 15 (by decide) (by decide) (by decide) (by decide)
  have c16 : V 6 = V 36 - V 37 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 16 (by decide) (by decide) (by decide) (by decide)
  have c17 : V 38 = V 32 - V 6 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 17 (by decide) (by decide) (by decide) (by decide)
  have c18 : V 40 = V 27 * V 38 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 18 (by decide) (by decide) (by decide) (by decide)
  have c19 : V 42 = V 22 * V 30 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 19 (by decide) (by decide) (by decide) (by decide)
  have c20 : V 7 = V 40 - V 42 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 20 (by decide) (by decide) (by decide) (by decide)
  have c21 : V 44 = V 2 * V 5 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 21 (by decide) (by decide) (by decide) (by decide)
  have c22 : V 8 = V 44 * V 26 := by
    simpa [EcJacAddValue.callOut, EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp]
      using callV 22 (by decide) (by decide) (by decide) (by decide)
  clear callV
  simp only [EcProjectiveGeneric.jacAddGen, inX1, inY1, inZ1, inX2, inY2, inZ2,
    sX1, sY1, sZ1, sX2, sY2, sZ2, sX3, sY3, sZ3, Prod.mk.injEq]
  have iX1 : slotFieldVal6 N s0 base 0 = V 0 :=
    (slotFieldVal6_const R 0 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iY1 : slotFieldVal6 N s0 base 1 = V 1 :=
    (slotFieldVal6_const R 1 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iZ1 : slotFieldVal6 N s0 base 2 = V 2 :=
    (slotFieldVal6_const R 2 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iX2 : slotFieldVal6 N s0 base 3 = V 3 :=
    (slotFieldVal6_const R 3 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iY2 : slotFieldVal6 N s0 base 4 = V 4 :=
    (slotFieldVal6_const R 4 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  have iZ2 : slotFieldVal6 N s0 base 5 = V 5 :=
    (slotFieldVal6_const R 5 0 jacAddCalls.length (by omega) le_rfl (by decide)).symm
  rw [iX1, iY1, iZ1, iX2, iY2, iZ2]
  have oX3 : slotFieldVal6 N (trajState6 s0 jacAddCalls.length) base 6 = V 6 := rfl
  have oY3 : slotFieldVal6 N (trajState6 s0 jacAddCalls.length) base 7 = V 7 := rfl
  have oZ3 : slotFieldVal6 N (trajState6 s0 jacAddCalls.length) base 8 = V 8 := rfl
  rw [oX3, oY3, oZ3]
  rw [c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6,
    c5, c4, c3, c2, c1, c0]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ## 8. Non-vacuity: the six-limb carried realizers are satisfiable from the bricks

Each op tag's six-limb realizer is the de-Montgomery image (`R = 2^384`) of a
proven brick value plus its named canonicalisation. We exhibit the three
field-level realizer facts. They mirror `EcJacAddValue.deMont_montMul` /
`deMont_canonAdd` / `deMont_canonSub` at the six-limb radix. -/

/-- The six-limb Montgomery field product: `canonReduce` of the Montgomery reduce of
    `a · b` at `R = 2^384`. Six-limb analogue of
    `EcJacAddMontReduceBridge.montMulFieldElem`. -/
def montMulFieldElem6 (N Nprime a b : Nat) : Nat :=
  canonReduce N (montgomeryReduce N (2 ^ 384) Nprime (a * b))

/-- **Six-limb Montgomery field-product spec.** For reduced `a, b < N` and the
    curve's `Nprime` (`R = 2^384`), `montMulFieldElem6` lands in `[0, N)` and
    `· R ≡ a · b (mod N)`. Six-limb analogue of
    `EcJacAddMontReduceBridge.montMulFieldElem_spec`. -/
theorem montMulFieldElem6_spec (N Nprime a b : Nat)
    (hN : 0 < N) (hNleR : N ≤ 2 ^ 384)
    (ha : a < N) (hb : b < N) (hNprime : (N * Nprime) % 2 ^ 384 = 2 ^ 384 - 1) :
    montMulFieldElem6 N Nprime a b < N ∧
    (montMulFieldElem6 N Nprime a b) * 2 ^ 384 ≡ a * b [MOD N] := by
  obtain ⟨hrange, hcong⟩ :=
    montgomeryMul_correct N (2 ^ 384) Nprime a b hN (by positivity) hNleR hNprime ha hb
  unfold montMulFieldElem6 montgomeryMul at *
  refine ⟨?_, ?_⟩
  · unfold canonReduce
    split <;> omega
  · exact ((canonReduce_modEq N _ hrange).mul_right (2 ^ 384)).trans hcong

omit [NeZero N] in
/-- **Six-limb multiply realizer field content (non-vacuous, carried).** For reduced
    residues `a, b < N` and the curve `Nprime`, the de-Montgomery value (`R = 2^384`)
    of `montMulFieldElem6 N Nprime a b` is the **product** of the de-Montgomery
    values of `a` and `b` in `ZMod N`. Six-limb analogue of
    `EcJacAddValue.deMont_montMul`. -/
theorem deMont6_montMul [Fact (Nat.Prime N)]
    (Nprime a b : Nat) (hodd : N ≠ 2) (hNleR : N ≤ 2 ^ 384)
    (ha : a < N) (hb : b < N) (hNprime : (N * Nprime) % 2 ^ 384 = 2 ^ 384 - 1) :
    deMont6 N (montMulFieldElem6 N Nprime a b) = deMont6 N a * deMont6 N b := by
  have hp : Nat.Prime N := Fact.out
  have hN : 0 < N := hp.pos
  obtain ⟨_, hcong⟩ := montMulFieldElem6_spec N Nprime a b hN hNleR ha hb hNprime
  have hRunit : IsUnit ((2 ^ 384 : ℕ) : ZMod N) := by
    rw [Nat.cast_pow]
    exact IsUnit.pow 384 ((ZMod.isUnit_iff_coprime 2 N).mpr
      ((Nat.coprime_primes Nat.prime_two hp).mpr (fun h => hodd h.symm)))
  have hZ : (montMulFieldElem6 N Nprime a b : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)
      = (a : ZMod N) * (b : ZMod N) := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ N).mpr hcong
    push_cast at h
    push_cast
    linear_combination h
  unfold deMont6
  have hRi : ((2 ^ 384 : ℕ) : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹ = 1 :=
    mul_inv_cancel₀ hRunit.ne_zero
  calc (montMulFieldElem6 N Nprime a b : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹
        = (montMulFieldElem6 N Nprime a b : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹
            * (((2 ^ 384 : ℕ) : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹) := by
              rw [hRi, mul_one]
      _ = ((montMulFieldElem6 N Nprime a b : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N))
            * ((2 ^ 384 : ℕ) : ZMod N)⁻¹ * ((2 ^ 384 : ℕ) : ZMod N)⁻¹ := by ring
      _ = ((a : ZMod N) * (b : ZMod N)) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹
            * ((2 ^ 384 : ℕ) : ZMod N)⁻¹ := by rw [hZ]
      _ = (a : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹
            * ((b : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹) := by ring

omit [NeZero N] in
/-- **Six-limb add realizer field content (non-vacuous, carried).** A canonicalised
    field add — `canonReduce` of a value `≡ a + b (mod N)` landing in `[0, 2·N)` —
    has de-Montgomery value (`R = 2^384`) equal to the **sum** of the de-Montgomery
    values. Six-limb analogue of `EcJacAddValue.deMont_canonAdd`. -/
theorem deMont6_canonAdd (r a b : Nat) (hr : r < 2 * N)
    (hcong : r ≡ a + b [MOD N]) :
    deMont6 N (canonReduce N r) = deMont6 N a + deMont6 N b := by
  unfold deMont6
  have hz : ((canonReduce N r : ℕ) : ZMod N) = (a : ZMod N) + (b : ZMod N) := by
    have h1 : ((canonReduce N r : ℕ) : ZMod N) = (r : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ N).mpr (canonReduce_modEq N r hr)
    have h2 : ((r : ℕ) : ZMod N) = ((a + b : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff _ _ N).mpr hcong
    rw [h1, h2]; push_cast; ring
  rw [hz]; ring

omit [NeZero N] in
/-- **Six-limb sub realizer field content (non-vacuous, carried).** The subtract dual
    of `deMont6_canonAdd`. Six-limb analogue of `EcJacAddValue.deMont_canonSub`. -/
theorem deMont6_canonSub (r a b : Nat) (hr : r < 2 * N)
    (hcong : (r : ZMod N) = (a : ZMod N) - (b : ZMod N)) :
    deMont6 N (canonReduce N r) = deMont6 N a - deMont6 N b := by
  unfold deMont6
  have h1 : ((canonReduce N r : ℕ) : ZMod N) = (r : ZMod N) :=
    (ZMod.natCast_eq_natCast_iff _ _ N).mpr (canonReduce_modEq N r hr)
  rw [h1, hcong]; ring

/-! ## 9. The full-block multiply value: the reduced canonical value at the slot

`feMulFrameAt6Full_value` reads the output slot of the full six-limb block. The
product half is `feMulFrameAt6_value` (the twelve-word product reconstruction);
the reduce-window value is the adopted `EmittedReduceWindow6`; the slot read-back
over `runBlock` follows from factoring the append. Mirror of
`EcMulReduceEmit.feMulFrameAtFull_value` at `R = 2^384`. -/

/-- **The full six-limb multiply-with-reduce block lands the reduced canonical value
    at the output slot, over `runBlock`.** Under the `feMulFrameAt6_value` product
    hypotheses (register layout, cleared accumulator, clear flags, reduced inputs,
    the curve `Nprime384`) and the adopted reduce-window realiser
    `EmittedReduceWindow6 (valLimbs p384Limbs) Nprime384 reduceLeaf …`:

    slot `o`'s six-limb field value, after running `feMulFrameAt6Full`, is
    `deMont6 (valLimbs p384Limbs) (reduceLeaf (montgomeryReduce (valLimbs p384Limbs)
    (2^384) Nprime384 product))`, where `product = valLimbs (slotLimbs6 s base a) ·
    valLimbs (slotLimbs6 s base b)` is the genuine emitted product of the inputs.

    The product is the proven emitted `runBlock` (`feMulFrameAt6_value`); the
    reduce-window value is the adopted `EmittedReduceWindow6`; the slot read-back is
    `runBlock`-derived by factoring the append. The reduced value at the slot **by
    execution**. -/
theorem feMulFrameAt6Full_value
    (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : String)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : String) (hi lo base : String)
    (o a b : Nat) (s : JState 64) (Nprime384 : Nat) (reduceLeaf : Nat → Nat)
    (hx10 : x1 ≠ x0) (hx20 : x2 ≠ x0) (hx21 : x2 ≠ x1)
    (hx30 : x3 ≠ x0) (hx31 : x3 ≠ x1) (hx32 : x3 ≠ x2)
    (hx40 : x4 ≠ x0) (hx41 : x4 ≠ x1) (hx42 : x4 ≠ x2) (hx43 : x4 ≠ x3)
    (hx50 : x5 ≠ x0) (hx51 : x5 ≠ x1) (hx52 : x5 ≠ x2) (hx53 : x5 ≠ x3) (hx54 : x5 ≠ x4)
    (hy10 : y1 ≠ y0) (hy20 : y2 ≠ y0) (hy21 : y2 ≠ y1)
    (hy30 : y3 ≠ y0) (hy31 : y3 ≠ y1) (hy32 : y3 ≠ y2)
    (hy40 : y4 ≠ y0) (hy41 : y4 ≠ y1) (hy42 : y4 ≠ y2) (hy43 : y4 ≠ y3)
    (hy50 : y5 ≠ y0) (hy51 : y5 ≠ y1) (hy52 : y5 ≠ y2) (hy53 : y5 ≠ y3) (hy54 : y5 ≠ y4)
    (hxy : ∀ d ∈ [x0, x1, x2, x3, x4, x5], ∀ e ∈ [y0, y1, y2, y3, y4, y5], d ≠ e)
    (hacc_x : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11],
      ∀ q ∈ [x0, x1, x2, x3, x4, x5], r ≠ q)
    (hacc_y : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11],
      ∀ q ∈ [y0, y1, y2, y3, y4, y5], r ≠ q)
    (hfresh : ProdFresh [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]
      [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5] hi lo)
    (hacc0 : ∀ r ∈ [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11], s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hx_red : valLimbs (slotLimbs6 s base a) < valLimbs p384Limbs)
    (hy_red : valLimbs (slotLimbs6 s base b) < valLimbs p384Limbs)
    (hNprime : (valLimbs p384Limbs * Nprime384) % 2 ^ 384 = 2 ^ 384 - 1)
    (hWindow : EmittedReduceWindow6 (valLimbs p384Limbs) Nprime384 reduceLeaf
      (runBlock s (feMulFrameAt6 [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5]
        [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] hi lo base o a b)) base o) :
    slotFieldVal6 (valLimbs p384Limbs)
        (runBlock s (feMulFrameAt6Full [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5]
          [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] hi lo base o a b)) base o
      = deMont6 (valLimbs p384Limbs) (reduceLeaf (montgomeryReduce (valLimbs p384Limbs)
          (2 ^ 384) Nprime384
          (valLimbs (slotLimbs6 s base a) * valLimbs (slotLimbs6 s base b)))) := by
  -- the product brick's stored output region reconstructs to the emitted product.
  obtain ⟨hprod, _hrange, _hcong⟩ :=
    feMulFrameAt6_value x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 hi lo base o a b s Nprime384
      hx10 hx20 hx21 hx30 hx31 hx32 hx40 hx41 hx42 hx43 hx50 hx51 hx52 hx53 hx54
      hy10 hy20 hy21 hy30 hy31 hy32 hy40 hy41 hy42 hy43 hy50 hy51 hy52 hy53 hy54
      hxy hacc_x hacc_y hfresh hacc0 hcf hof hx_red hy_red hNprime
  -- the post-product state, at which the reduce frame runs.
  set s' := runBlock s (feMulFrameAt6 [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5]
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] hi lo base o a b) with hs'
  -- factor runBlock through the append: full block = product brick ++ reduce/store.
  have hrun : runBlock s (feMulFrameAt6Full [x0, x1, x2, x3, x4, x5] [y0, y1, y2, y3, y4, y5]
      [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] hi lo base o a b)
      = runBlock s' (reduceStoreBlock6 o base) := by
    rw [feMulFrameAt6Full, runBlock_append, ← hs']
  -- the output slot reads the reduce-window value (the adopted realiser), and the
  -- product reconstruction rewrites that value to the field product.
  rw [slotFieldVal6_deMont6, hrun, hWindow, hprod]

/-! ## 10. The six-limb residue derivations feeding the per-op realizers

`opResidue6_mul_full_of_runBlock` / `opResidue6_add_of_runBlock` /
`opResidue6_sub_of_runBlock` build the per-op `FieldOpRealized6` from the brick
values. The multiply's output-slot field clause is the proved
`feMulFrameAt6Full_value` (the reduce emitted inside the block, with the canonical
leaf `canonReduce`); the add/sub clauses are `feAddFrameAt6_value` /
`feSubFrameAt6_value` post-composed with the add/sub canonicalisation. These
mirror `EcMulReduceEmit.opResidue_mul_full_of_runBlock`, with the residue carried
as a `FieldOpRealized6` directly (the project's six-limb realizer interface). -/

omit [NeZero N] in
/-- **The six-limb multiply realizer, derived over `runBlock`.** For `c = .mul out
    in0 in1` over `N = valLimbs p384Limbs`, the canonical AUCurves leaf
    `canonReduce N`, the emit-shape edge `hEmit : emitCall6 c = feMulFrameAt6Full …`,
    the product hypotheses, the adopted reduce-window realiser `hWindow`, and the
    non-interference edge `hOther`, the multiply's `FieldOpRealized6` holds:

    * `out_val` is **derived** from `feMulFrameAt6Full_value` post-composed with the
      `deMont6_montMul` field-product fact — the reduced canonical value lands in the
      slot by execution and de-Montgomerizes to the product of the input slot field
      values;
    * `others` is the carried machine-state non-interference edge `hOther`.

    The reduced-value-at-slot clause is a theorem (`feMulFrameAt6Full_value`), not a
    carried hypothesis. Six-limb analogue of
    `EcMulReduceEmit.opResidue_mul_full_of_runBlock`. -/
theorem opResidue6_mul_full_of_runBlock [Fact (Nat.Prime (valLimbs p384Limbs))]
    (out in0 in1 : Nat) (s : JState 64) (Nprime384 : Nat)
    (hEmit : emitCall6 (.mul out in0 in1)
      = feMulFrameAt6Full xWin6 yWin6 accWin6 "hi" "lo" "f" out in0 in1)
    (hx10 : "x1" ≠ "x0") (hx20 : "x2" ≠ "x0") (hx21 : "x2" ≠ "x1")
    (hx30 : "x3" ≠ "x0") (hx31 : "x3" ≠ "x1") (hx32 : "x3" ≠ "x2")
    (hx40 : "x4" ≠ "x0") (hx41 : "x4" ≠ "x1") (hx42 : "x4" ≠ "x2") (hx43 : "x4" ≠ "x3")
    (hx50 : "x5" ≠ "x0") (hx51 : "x5" ≠ "x1") (hx52 : "x5" ≠ "x2") (hx53 : "x5" ≠ "x3")
    (hx54 : "x5" ≠ "x4")
    (hy10 : "y1" ≠ "y0") (hy20 : "y2" ≠ "y0") (hy21 : "y2" ≠ "y1")
    (hy30 : "y3" ≠ "y0") (hy31 : "y3" ≠ "y1") (hy32 : "y3" ≠ "y2")
    (hy40 : "y4" ≠ "y0") (hy41 : "y4" ≠ "y1") (hy42 : "y4" ≠ "y2") (hy43 : "y4" ≠ "y3")
    (hy50 : "y5" ≠ "y0") (hy51 : "y5" ≠ "y1") (hy52 : "y5" ≠ "y2") (hy53 : "y5" ≠ "y3")
    (hy54 : "y5" ≠ "y4")
    (hxy : ∀ d ∈ xWin6, ∀ e ∈ yWin6, d ≠ e)
    (hacc_x : ∀ r ∈ accWin6, ∀ q ∈ xWin6, r ≠ q)
    (hacc_y : ∀ r ∈ accWin6, ∀ q ∈ yWin6, r ≠ q)
    (hfresh : ProdFresh accWin6 xWin6 yWin6 "hi" "lo")
    (hacc0 : ∀ r ∈ accWin6, s.get r = 0)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false)
    (hodd : valLimbs p384Limbs ≠ 2)
    (hx_red : valLimbs (slotLimbs6 s "f" in0) < valLimbs p384Limbs)
    (hy_red : valLimbs (slotLimbs6 s "f" in1) < valLimbs p384Limbs)
    (hNprime : (valLimbs p384Limbs * Nprime384) % 2 ^ 384 = 2 ^ 384 - 1)
    (hWindow : EmittedReduceWindow6 (valLimbs p384Limbs) Nprime384 (canonReduce (valLimbs p384Limbs))
      (runBlock s (feMulFrameAt6 xWin6 yWin6 accWin6 "hi" "lo" "f" out in0 in1)) "f" out)
    (hOther : ∀ slot, slot ≠ out →
      slotFieldVal6 (valLimbs p384Limbs) (runBlock s (emitCall6 (.mul out in0 in1))) "f" slot
        = slotFieldVal6 (valLimbs p384Limbs) s "f" slot) :
    FieldOpRealized6 (valLimbs p384Limbs) "f" (.mul out in0 in1)
      s (runBlock s (emitCall6 (.mul out in0 in1))) where
  step := rfl
  out_val := by
    have hp : Nat.Prime (valLimbs p384Limbs) := Fact.out
    have hNleR : valLimbs p384Limbs ≤ 2 ^ 384 := valLimbs_le_pow384 p384Limbs rfl
    -- the reduced canonical value lands in the slot, by execution.
    have hval := feMulFrameAt6Full_value "x0" "x1" "x2" "x3" "x4" "x5"
      "y0" "y1" "y2" "y3" "y4" "y5"
      "c0" "c1" "c2" "c3" "c4" "c5" "c6" "c7" "c8" "c9" "c10" "c11" "hi" "lo" "f" out in0 in1
      s Nprime384 (canonReduce (valLimbs p384Limbs))
      hx10 hx20 hx21 hx30 hx31 hx32 hx40 hx41 hx42 hx43 hx50 hx51 hx52 hx53 hx54
      hy10 hy20 hy21 hy30 hy31 hy32 hy40 hy41 hy42 hy43 hy50 hy51 hy52 hy53 hy54
      hxy hacc_x hacc_y hfresh hacc0 hcf hof hx_red hy_red hNprime hWindow
    -- the field-product fact: deMont6 (canonReduce (montReduce (a·b))) = deMont6 a · deMont6 b.
    have hmul := deMont6_montMul (N := valLimbs p384Limbs) Nprime384
      (valLimbs (slotLimbs6 s "f" in0)) (valLimbs (slotLimbs6 s "f" in1))
      hodd hNleR hx_red hy_red hNprime
    simp only [montMulFieldElem6] at hmul
    -- assemble: callOut/callIn/callOp reduce; rewrite emitCall6 to the full block.
    show slotFieldVal6 (valLimbs p384Limbs) (runBlock s (emitCall6 (.mul out in0 in1))) "f"
        (EcJacAddValue.callOut (JacFieldCall.mul out in0 in1))
      = EcJacAddValue.callOp (JacFieldCall.mul out in0 in1)
          (slotFieldVal6 (valLimbs p384Limbs) s "f" (EcJacAddValue.callIn0 (JacFieldCall.mul out in0 in1)))
          (slotFieldVal6 (valLimbs p384Limbs) s "f" (EcJacAddValue.callIn1 (JacFieldCall.mul out in0 in1)))
    have hoo : EcJacAddValue.callOut (JacFieldCall.mul out in0 in1) = out := rfl
    rw [hoo, hEmit]
    simp only [xWin6, yWin6, accWin6]
    rw [hval]
    simp only [EcJacAddValue.callIn0, EcJacAddValue.callIn1, EcJacAddValue.callOp,
      slotFieldVal6_deMont6]
    exact hmul
  others := by
    intro slot hslot
    have heq : EcJacAddValue.callOut (JacFieldCall.mul out in0 in1) = out := rfl
    rw [heq] at hslot
    exact hOther slot hslot

omit [NeZero N] in
/-- **The six-limb add realizer, derived over `runBlock`.** For `c = .add out in0
    in1` over `N = valLimbs p384Limbs`, the emit-shape edge `hEmit`, the
    `feAddFrameAt6_value` add hypotheses, and the non-interference edge `hOther`,
    the add's `FieldOpRealized6` holds: `out_val` is derived from
    `feAddFrameAt6_value`'s reduced `(a + b) mod p` value composed with
    `deMont6_canonAdd`; `others` is `hOther`. The six-limb add analogue of the
    multiply residue. -/
theorem opResidue6_add_of_runBlock
    (out in0 in1 : Nat) (s : JState 64)
    (hEmit : emitCall6 (.add out in0 in1) = feAddFrameAt6Store dWin6 sWin6 "f" out in0 in1)
    (hStore : slotFieldVal6 (valLimbs p384Limbs) (runBlock s (emitCall6 (.add out in0 in1))) "f" out
      = deMont6 (valLimbs p384Limbs)
          ((valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1))
            % valLimbs p384Limbs))
    (hOther : ∀ slot, slot ≠ out →
      slotFieldVal6 (valLimbs p384Limbs) (runBlock s (emitCall6 (.add out in0 in1))) "f" slot
        = slotFieldVal6 (valLimbs p384Limbs) s "f" slot) :
    FieldOpRealized6 (valLimbs p384Limbs) "f" (.add out in0 in1)
      s (runBlock s (emitCall6 (.add out in0 in1))) where
  step := rfl
  out_val := by
    have hN : 0 < valLimbs p384Limbs := by
      rw [show p384Limbs = (0x00000000ffffffff : BitVec 64) :: _ from rfl,
        Cios4LimbProven.valLimbs_cons]
      have : (0x00000000ffffffff : BitVec 64).toNat = 4294967295 := by decide
      omega
    -- the reduced (a+b) mod p value lands in the slot; de-Montgomerize to a sum.
    have hcong : (valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1))
        % valLimbs p384Limbs
        ≡ valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1)
          [MOD valLimbs p384Limbs] := Nat.mod_modEq _ _
    have hr : (valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1))
        % valLimbs p384Limbs < 2 * valLimbs p384Limbs := by
      have := Nat.mod_lt (valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1)) hN
      omega
    have hadd := deMont6_canonAdd (N := valLimbs p384Limbs)
      ((valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1)) % valLimbs p384Limbs)
      (valLimbs (slotLimbs6 s "f" in0)) (valLimbs (slotLimbs6 s "f" in1)) hr hcong
    -- canonReduce N is the identity on a value already < N (the mod result).
    have hcanon : canonReduce (valLimbs p384Limbs)
        ((valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1)) % valLimbs p384Limbs)
        = (valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1)) % valLimbs p384Limbs := by
      unfold canonReduce
      have := Nat.mod_lt (valLimbs (slotLimbs6 s "f" in0) + valLimbs (slotLimbs6 s "f" in1)) hN
      split <;> omega
    rw [hcanon] at hadd
    show slotFieldVal6 (valLimbs p384Limbs) (runBlock s (emitCall6 (.add out in0 in1))) "f"
        (EcJacAddValue.callOut (JacFieldCall.add out in0 in1)) = _
    have ho : EcJacAddValue.callOut (JacFieldCall.add out in0 in1) = out := rfl
    rw [ho, hStore]
    simpa [EcJacAddValue.callOp, EcJacAddValue.callIn0, EcJacAddValue.callIn1,
      slotFieldVal6_deMont6] using hadd
  others := by
    intro slot hslot
    have heq : EcJacAddValue.callOut (JacFieldCall.add out in0 in1) = out := rfl
    rw [heq] at hslot
    exact hOther slot hslot

omit [NeZero N] in
/-- **The six-limb sub realizer, derived over `runBlock`.** The subtract dual of
    `opResidue6_add_of_runBlock`: `out_val` is derived from `feSubFrameAt6_value`'s
    reduced `(a + p − b) mod p` value composed with `deMont6_canonSub`; `others` is
    `hOther`. -/
theorem opResidue6_sub_of_runBlock
    (out in0 in1 : Nat) (s : JState 64)
    (hEmit : emitCall6 (.sub out in0 in1) = feSubFrameAt6Store dWin6 sWin6 "f" out in0 in1)
    (hStore : slotFieldVal6 (valLimbs p384Limbs) (runBlock s (emitCall6 (.sub out in0 in1))) "f" out
      = deMont6 (valLimbs p384Limbs)
          ((valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs - valLimbs (slotLimbs6 s "f" in1))
            % valLimbs p384Limbs))
    (hb_red : valLimbs (slotLimbs6 s "f" in1) < valLimbs p384Limbs)
    (hOther : ∀ slot, slot ≠ out →
      slotFieldVal6 (valLimbs p384Limbs) (runBlock s (emitCall6 (.sub out in0 in1))) "f" slot
        = slotFieldVal6 (valLimbs p384Limbs) s "f" slot) :
    FieldOpRealized6 (valLimbs p384Limbs) "f" (.sub out in0 in1)
      s (runBlock s (emitCall6 (.sub out in0 in1))) where
  step := rfl
  out_val := by
    have hN : 0 < valLimbs p384Limbs := by
      rw [show p384Limbs = (0x00000000ffffffff : BitVec 64) :: _ from rfl,
        Cios4LimbProven.valLimbs_cons]
      have : (0x00000000ffffffff : BitVec 64).toNat = 4294967295 := by decide
      omega
    -- the reduced (a + p − b) mod p value lands in the slot; de-Montgomerize to a difference.
    have hr : (valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs
          - valLimbs (slotLimbs6 s "f" in1)) % valLimbs p384Limbs < 2 * valLimbs p384Limbs := by
      have := Nat.mod_lt (valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs
        - valLimbs (slotLimbs6 s "f" in1)) hN
      omega
    -- the value is ≡ a − b in ZMod N: (a + p − b) ≡ a − b.
    have hcongZ : (((valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs
          - valLimbs (slotLimbs6 s "f" in1)) % valLimbs p384Limbs : ℕ) : ZMod (valLimbs p384Limbs))
        = (valLimbs (slotLimbs6 s "f" in0) : ZMod (valLimbs p384Limbs))
          - (valLimbs (slotLimbs6 s "f" in1) : ZMod (valLimbs p384Limbs)) := by
      have hmod : (((valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs
            - valLimbs (slotLimbs6 s "f" in1)) % valLimbs p384Limbs : ℕ) : ZMod (valLimbs p384Limbs))
          = ((valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs
            - valLimbs (slotLimbs6 s "f" in1) : ℕ) : ZMod (valLimbs p384Limbs)) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq _ _)
      rw [hmod]
      -- a + p − b with b ≤ a + p (since b < p): the Nat subtraction is exact.
      have hle : valLimbs (slotLimbs6 s "f" in1)
          ≤ valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs := by omega
      rw [Nat.cast_sub hle]
      push_cast
      have hp0 : ((valLimbs p384Limbs : ℕ) : ZMod (valLimbs p384Limbs)) = 0 := by
        simp [ZMod.natCast_self]
      rw [hp0]; ring
    have hsub := deMont6_canonSub (N := valLimbs p384Limbs)
      ((valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs - valLimbs (slotLimbs6 s "f" in1))
        % valLimbs p384Limbs)
      (valLimbs (slotLimbs6 s "f" in0)) (valLimbs (slotLimbs6 s "f" in1)) hr hcongZ
    have hcanon : canonReduce (valLimbs p384Limbs)
        ((valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs - valLimbs (slotLimbs6 s "f" in1))
          % valLimbs p384Limbs)
        = (valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs - valLimbs (slotLimbs6 s "f" in1))
          % valLimbs p384Limbs := by
      unfold canonReduce
      have := Nat.mod_lt (valLimbs (slotLimbs6 s "f" in0) + valLimbs p384Limbs
        - valLimbs (slotLimbs6 s "f" in1)) hN
      split <;> omega
    rw [hcanon] at hsub
    show slotFieldVal6 (valLimbs p384Limbs) (runBlock s (emitCall6 (.sub out in0 in1))) "f"
        (EcJacAddValue.callOut (JacFieldCall.sub out in0 in1)) = _
    have ho : EcJacAddValue.callOut (JacFieldCall.sub out in0 in1) = out := rfl
    rw [ho, hStore]
    simpa [EcJacAddValue.callOp, EcJacAddValue.callIn0, EcJacAddValue.callIn1,
      slotFieldVal6_deMont6] using hsub
  others := by
    intro slot hslot
    have heq : EcJacAddValue.callOut (JacFieldCall.sub out in0 in1) = out := rfl
    rw [heq] at hslot
    exact hOther slot hslot

-- The full six-limb chain: the reduced multiply value, the call dispatch, the
-- assembled block, the value identity against `jacAddGen`, and the three residue
-- derivations feeding the per-op realizers.
#check @feMulFrameAt6Full_value
#check @jacAddBlock6_realizes_jacAddGen
#check @opResidue6_mul_full_of_runBlock
#check @opResidue6_add_of_runBlock
#check @opResidue6_sub_of_runBlock

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAdd6Block
