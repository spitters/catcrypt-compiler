/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblValue
public import CatCrypt.Crypto.SecureCompilation.EcProjectiveGenericA

@[expose] public section

set_option autoImplicit false

/-!
# Structural and value Jacobian point-double for `a = −3` over the shared frame

`EcProjectiveGenericA.jacDoubleGenM3` is the inversion-free `dbl-2001-b` Jacobian
point-double for curves with `a = −3` (P-256, P-384):

```
S = 4·X·Y² ; M = 3·(X − Z²)·(X + Z²)
X' = M² − 2·S ; Y' = M·(S − X') − 8·Y⁴ ; Z' = 2·Y·Z
```

and `EcProjectiveGenericA.jacDoubleGenM3_eq` identifies it with
`jacDoubleGenA (−3)`. This module is the four-limb frame realisation of that formula,
built from the same parts as the `a = 0` double (`EcJacDblBlock`, `EcJacDblValue`):

* a slot layout for the input point, the output point and the intermediates over the
  single frame `"f"` (slot `i` limb `k` at byte offset `32·i + 8·k`);
* the call sequence `jacDblCallsA : List JacFieldCall` (8 multiplies, 10 adds,
  4 subtracts) and the block `jacDblBlockA := (jacDblCallsA.map emitCall).flatten`,
  over the frame-wrapped field bricks of `EcJacAddBlock.emitCall`;
* the lowering theorem `jacDblBlockA_lowering_correct` and the field-op counts;
* the realizer bundle `JacDblARealized` (one `EcJacAddValue.FieldOpRealized` per call
  along the `runBlock` trajectory) and the value identity
  `jacDblBlockA_realizes_jacDoubleGenA`: the output slots hold
  `jacDoubleGenA (−3) X Y Z` of the input slots.

The per-op realizer contents are those of the `a = 0` double
(`EcJacAddValue.deMont_montMul`, `deMont_canonAdd`, `deMont_canonSub`), since the
schedule uses the same three call tags.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblABlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacAddValue

/-! ## 1. Frame geometry

A `feMulFrameAt` writes its 512-bit product into slots `o`, `o+1`; each multiply output
is an even slot whose successor is written by no call. -/

-- input point P = (X, Y, Z)
def sX : Nat := 0
def sY : Nat := 1
def sZ : Nat := 2
-- output point P' = (X', Y', Z')
def sX3 : Nat := 3
def sY3 : Nat := 4
def sZ3 : Nat := 5
-- intermediates
def sZZ      : Nat := 6    -- Z²
def sXmZZ    : Nat := 8    -- X − Z²
def sXpZZ    : Nat := 9    -- X + Z²
def sMP      : Nat := 10   -- (X − Z²)·(X + Z²)
def sM2      : Nat := 12   -- 2·(X − Z²)·(X + Z²)
def sM       : Nat := 13   -- M = 3·(X − Z²)·(X + Z²)
def sYY      : Nat := 14   -- Y²
def sXYY     : Nat := 16   -- X·Y²
def sTwoXYY  : Nat := 18   -- 2·X·Y²
def sS       : Nat := 19   -- S = 4·X·Y²
def sMsq     : Nat := 20   -- M²
def sTwoS    : Nat := 22   -- 2·S
def sSmXp    : Nat := 23   -- S − X'
def sMSmXp   : Nat := 24   -- M·(S − X')
def sYYsq    : Nat := 26   -- Y⁴
def sTwoY4   : Nat := 28   -- 2·Y⁴
def sFourY4  : Nat := 29   -- 4·Y⁴
def sEightY4 : Nat := 30   -- 8·Y⁴
def sYZ      : Nat := 32   -- Y·Z

/-! ## 2. The call sequence

`Z², X−Z², X+Z², (X−Z²)(X+Z²), 2·, M=3·; Y², X·Y², 2X·Y², S=4X·Y²; M², 2S, X'=M²−2S;`
`S−X', M·(S−X'); Y⁴, 2Y⁴, 4Y⁴, 8Y⁴, Y'=M(S−X')−8Y⁴; Y·Z, Z'=2YZ`. -/

/-- The `a = −3` Jacobian-double call sequence, one abstract field op of
    `EcProjectiveGenericA.jacDoubleGenM3` per entry. -/
def jacDblCallsA : List JacFieldCall :=
  [ -- M = 3·(X − Z²)·(X + Z²)
    .mul sZZ sZ sZ                -- Z²
  , .sub sXmZZ sX sZZ            -- X − Z²
  , .add sXpZZ sX sZZ            -- X + Z²
  , .mul sMP sXmZZ sXpZZ         -- (X − Z²)·(X + Z²)
  , .add sM2 sMP sMP             -- 2·(X − Z²)·(X + Z²)
  , .add sM sM2 sMP              -- M
    -- S = 4·X·Y²
  , .mul sYY sY sY               -- Y²
  , .mul sXYY sX sYY             -- X·Y²
  , .add sTwoXYY sXYY sXYY       -- 2·X·Y²
  , .add sS sTwoXYY sTwoXYY      -- S = 4·X·Y²
    -- X' = M² − 2·S
  , .mul sMsq sM sM              -- M²
  , .add sTwoS sS sS             -- 2·S
  , .sub sX3 sMsq sTwoS          -- X' = M² − 2·S
    -- Y' = M·(S − X') − 8·Y⁴
  , .sub sSmXp sS sX3            -- S − X'
  , .mul sMSmXp sM sSmXp         -- M·(S − X')
  , .mul sYYsq sYY sYY           -- Y⁴
  , .add sTwoY4 sYYsq sYYsq      -- 2·Y⁴
  , .add sFourY4 sTwoY4 sTwoY4   -- 4·Y⁴
  , .add sEightY4 sFourY4 sFourY4 -- 8·Y⁴
  , .sub sY3 sMSmXp sEightY4     -- Y' = M·(S − X') − 8·Y⁴
    -- Z' = 2·Y·Z
  , .mul sYZ sY sZ               -- Y·Z
  , .add sZ3 sYZ sYZ ]           -- Z' = 2·Y·Z

/-! ## 3. The assembled block and its lowering -/

/-- The Jacobian point-double block `P' := 2·P` for `a = −3` (`dbl-2001-b`): the
    frame-wrapped field-op blocks of `jacDblCallsA` concatenated over the frame `"f"`. -/
def jacDblBlockA : List (JInstr 64) :=
  (jacDblCallsA.map emitCall).flatten

/-- Lowering `jacDblBlockA` to `Com (x86Dialect 64)` and denoting on the frame state
    `EcJacDblBlock.initFrame fr` equals `runBlock` on the source block. -/
theorem jacDblBlockA_lowering_correct (fr : Nat → Fin 4 → BitVec 64) :
    (lowerBlock (Γ := []) jacDblBlockA).denote
        (.cons (EcJacDblBlock.initFrame fr) .nil)
      = runBlock (EcJacDblBlock.initFrame fr) jacDblBlockA :=
  lowerBlock_denote_closed jacDblBlockA (EcJacDblBlock.initFrame fr)

/-! ## 4. Field-op counts -/

/-- `jacDblCallsA` has 22 calls: 8 `mul` + 10 `add` + 4 `sub`. -/
theorem jacDblCallsA_length : jacDblCallsA.length = 22 := by decide

/-- The multiply count: `Z²`, `(X−Z²)(X+Z²)`, `Y²`, `X·Y²`, `M²`, `M·(S−X')`, `Y⁴`, `Y·Z`. -/
theorem jacDblCallsA_mul_count :
    (jacDblCallsA.filter
        (fun c => match c with | .mul _ _ _ => true | _ => false)).length = 8 := by
  decide

/-- The add count: `X+Z²`, the doubling and tripling to `M`, `2X·Y²`, `S`, `2S`, `2Y⁴`,
    `4Y⁴`, `8Y⁴`, `Z'`. -/
theorem jacDblCallsA_add_count :
    (jacDblCallsA.filter
        (fun c => match c with | .add _ _ _ => true | _ => false)).length = 10 := by
  decide

/-- The subtract count: `X−Z²`, `X'`, `S−X'`, `Y'`. -/
theorem jacDblCallsA_sub_count :
    (jacDblCallsA.filter
        (fun c => match c with | .sub _ _ _ => true | _ => false)).length = 4 := by
  decide

/-! ## 5. Threading the call list -/

variable {N : Nat} [NeZero N]

/-- `runBlock` of `jacDblBlockA` is the left fold of `runBlock ∘ emitCall` over
    `jacDblCallsA`. -/
theorem runBlock_jacDblBlockA (s0 : JState 64) :
    runBlock s0 jacDblBlockA = EcJacDblValue.threadState s0 jacDblCallsA := by
  rw [jacDblBlockA, runBlock_flatten_map]; rfl

/-- The state before call `k` of `jacDblCallsA`, threaded from `s0`. -/
def trajState (s0 : JState 64) (k : Nat) : JState 64 :=
  EcJacDblValue.threadState s0 (jacDblCallsA.take k)

/-- The realizer bundle for the `a = −3` point-double: for each call index `k < 22`, a
    `FieldOpRealized` witness for `jacDblCallsA[k]` between the threaded states `k` and
    `k + 1`. -/
structure JacDblARealized (N : Nat) (base : String) (s0 : JState 64) : Prop where
  /-- Each call realizes its field op at its threaded pre-state. -/
  realizes : ∀ (k : Nat) (h : k < jacDblCallsA.length),
    FieldOpRealized N base (jacDblCallsA[k]'h)
      (trajState s0 k) (trajState s0 (k + 1))

/-- One step of the trajectory runs one call. -/
theorem trajState_succ (s0 : JState 64) (k : Nat) (h : k < jacDblCallsA.length) :
    trajState s0 (k + 1) = runBlock (trajState s0 k) (emitCall (jacDblCallsA[k]'h)) := by
  unfold trajState
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, EcJacDblValue.threadState]
  rw [List.foldl_append]
  rfl

/-- The final threaded state is `trajState s0 22`. -/
theorem trajState_full (s0 : JState 64) :
    EcJacDblValue.threadState s0 jacDblCallsA = trajState s0 jacDblCallsA.length := by
  unfold trajState; rw [List.take_length]

omit [NeZero N] in
/-- A slot written by none of the calls `k, …, k+d-1` keeps its field value from step `k`
    to step `k+d`. -/
theorem slotFieldVal_preserved
    {base : String} {s0 : JState 64} (R : JacDblARealized N base s0)
    (slot : Nat) :
    ∀ (d k : Nat) (_hk : k + d ≤ jacDblCallsA.length),
      (∀ j (hj : j < jacDblCallsA.length), k ≤ j → j < k + d →
        slot ≠ callOut (jacDblCallsA[j]'hj))
      → slotFieldVal N (trajState s0 (k + d)) base slot
        = slotFieldVal N (trajState s0 k) base slot := by
  intro d
  induction d with
  | zero => intro k _ _; rfl
  | succ d ih =>
      intro k hk hno
      have hk1 : (k + 1) + d ≤ jacDblCallsA.length := by omega
      have hkk : k < jacDblCallsA.length := by omega
      have e1 : slotFieldVal N (trajState s0 ((k + 1) + d)) base slot
          = slotFieldVal N (trajState s0 (k + 1)) base slot := by
        apply ih (k + 1) hk1
        intro j hj hj1 hj2
        exact hno j hj (by omega) (by omega)
      have e0 : slotFieldVal N (trajState s0 (k + 1)) base slot
          = slotFieldVal N (trajState s0 k) base slot :=
        (R.realizes k hkk).others slot (hno k hkk (by omega) (by omega))
      have hidx : k + (d + 1) = (k + 1) + d := by omega
      rw [hidx, e1, e0]

omit [NeZero N] in
/-- A slot written by no call in `[k, m)` has the same field value at steps `k` and `m`. -/
theorem slotFieldVal_const
    {base : String} {s0 : JState 64} (R : JacDblARealized N base s0)
    (slot k m : Nat) (hkm : k ≤ m) (hm : m ≤ jacDblCallsA.length)
    (hno : ∀ j (hj : j < jacDblCallsA.length), k ≤ j → j < m →
      slot ≠ callOut (jacDblCallsA[j]'hj)) :
    slotFieldVal N (trajState s0 m) base slot = slotFieldVal N (trajState s0 k) base slot := by
  have hd : m = k + (m - k) := by omega
  rw [hd]
  exact slotFieldVal_preserved R slot (m - k) k (by omega)
    (fun j hj hj1 hj2 => hno j hj hj1 (by omega))

/-! ## 6. The value identity against `jacDoubleGenA (−3)` -/

omit [NeZero N] in
/-- The value identity for the `a = −3` point-double. Given the realizer bundle `R`,
    running `jacDblBlockA` from `s0` leaves the output slots `sX3`/`sY3`/`sZ3` holding
    `EcProjectiveGenericA.jacDoubleGenA (−3) X Y Z`, where `X`, `Y`, `Z` are the
    de-Montgomery field values of the input slots of `s0` (`EcJacDblValue.inX`/`inY`/`inZ`,
    which read slots 0, 1, 2 as in the `a = 0` double). -/
theorem jacDblBlockA_realizes_jacDoubleGenA
    [Fact (Nat.Prime N)]
    {base : String} {s0 : JState 64} (R : JacDblARealized N base s0) :
    (slotFieldVal N (runBlock s0 jacDblBlockA) base sX3,
     slotFieldVal N (runBlock s0 jacDblBlockA) base sY3,
     slotFieldVal N (runBlock s0 jacDblBlockA) base sZ3)
      = EcProjectiveGenericA.jacDoubleGenA (-3)
          (EcJacDblValue.inX N s0 base) (EcJacDblValue.inY N s0 base)
          (EcJacDblValue.inZ N s0 base) := by
  rw [runBlock_jacDblBlockA, trajState_full]
  set V : Nat → ZMod N := fun slot => slotFieldVal N (trajState s0 jacDblCallsA.length) base slot
    with hV
  have align : ∀ (k : Nat) (_hk : k ≤ jacDblCallsA.length) (slot : Nat),
      (∀ j (hj : j < jacDblCallsA.length), k ≤ j → slot ≠ callOut (jacDblCallsA[j]'hj)) →
      slotFieldVal N (trajState s0 k) base slot = V slot := by
    intro k hk slot hno
    rw [hV]
    exact (slotFieldVal_const R slot k jacDblCallsA.length hk le_rfl
      (fun j hj hj1 _ => hno j hj hj1)).symm
  have callV : ∀ (k : Nat) (hk : k < jacDblCallsA.length)
      (hout : ∀ j (hj : j < jacDblCallsA.length), k + 1 ≤ j →
        callOut (jacDblCallsA[k]'hk) ≠ callOut (jacDblCallsA[j]'hj))
      (hin0 : ∀ j (hj : j < jacDblCallsA.length), k ≤ j →
        callIn0 (jacDblCallsA[k]'hk) ≠ callOut (jacDblCallsA[j]'hj))
      (hin1 : ∀ j (hj : j < jacDblCallsA.length), k ≤ j →
        callIn1 (jacDblCallsA[k]'hk) ≠ callOut (jacDblCallsA[j]'hj)),
      V (callOut (jacDblCallsA[k]'hk))
        = callOp (jacDblCallsA[k]'hk)
            (V (callIn0 (jacDblCallsA[k]'hk))) (V (callIn1 (jacDblCallsA[k]'hk))) := by
    intro k hk hout hin0 hin1
    have hLHS : V (callOut (jacDblCallsA[k]'hk))
        = slotFieldVal N (trajState s0 (k + 1)) base (callOut (jacDblCallsA[k]'hk)) := by
      rw [hV]
      exact slotFieldVal_const R _ (k + 1) jacDblCallsA.length hk le_rfl
        (fun j hj hj1 _ => hout j hj hj1)
    have hI0 := align k (le_of_lt hk) (callIn0 (jacDblCallsA[k]'hk))
      (fun j hj hj1 => hin0 j hj hj1)
    have hI1 := align k (le_of_lt hk) (callIn1 (jacDblCallsA[k]'hk))
      (fun j hj hj1 => hin1 j hj hj1)
    rw [hLHS, (R.realizes k hk).out_val, hI0, hI1]
  clear align
  have c0 : V 6 = V 2 * V 2 := callV 0 (by decide) (by decide) (by decide) (by decide)
  have c1 : V 8 = V 0 - V 6 := callV 1 (by decide) (by decide) (by decide) (by decide)
  have c2 : V 9 = V 0 + V 6 := callV 2 (by decide) (by decide) (by decide) (by decide)
  have c3 : V 10 = V 8 * V 9 := callV 3 (by decide) (by decide) (by decide) (by decide)
  have c4 : V 12 = V 10 + V 10 := callV 4 (by decide) (by decide) (by decide) (by decide)
  have c5 : V 13 = V 12 + V 10 := callV 5 (by decide) (by decide) (by decide) (by decide)
  have c6 : V 14 = V 1 * V 1 := callV 6 (by decide) (by decide) (by decide) (by decide)
  have c7 : V 16 = V 0 * V 14 := callV 7 (by decide) (by decide) (by decide) (by decide)
  have c8 : V 18 = V 16 + V 16 := callV 8 (by decide) (by decide) (by decide) (by decide)
  have c9 : V 19 = V 18 + V 18 := callV 9 (by decide) (by decide) (by decide) (by decide)
  have c10 : V 20 = V 13 * V 13 := callV 10 (by decide) (by decide) (by decide) (by decide)
  have c11 : V 22 = V 19 + V 19 := callV 11 (by decide) (by decide) (by decide) (by decide)
  have c12 : V 3 = V 20 - V 22 := callV 12 (by decide) (by decide) (by decide) (by decide)
  have c13 : V 23 = V 19 - V 3 := callV 13 (by decide) (by decide) (by decide) (by decide)
  have c14 : V 24 = V 13 * V 23 := callV 14 (by decide) (by decide) (by decide) (by decide)
  have c15 : V 26 = V 14 * V 14 := callV 15 (by decide) (by decide) (by decide) (by decide)
  have c16 : V 28 = V 26 + V 26 := callV 16 (by decide) (by decide) (by decide) (by decide)
  have c17 : V 29 = V 28 + V 28 := callV 17 (by decide) (by decide) (by decide) (by decide)
  have c18 : V 30 = V 29 + V 29 := callV 18 (by decide) (by decide) (by decide) (by decide)
  have c19 : V 4 = V 24 - V 30 := callV 19 (by decide) (by decide) (by decide) (by decide)
  have c20 : V 32 = V 1 * V 2 := callV 20 (by decide) (by decide) (by decide) (by decide)
  have c21 : V 5 = V 32 + V 32 := callV 21 (by decide) (by decide) (by decide) (by decide)
  clear callV
  simp only [EcProjectiveGenericA.jacDoubleGenA, EcJacDblValue.inX, EcJacDblValue.inY,
    EcJacDblValue.inZ, EcJacDblBlock.sX, EcJacDblBlock.sY, EcJacDblBlock.sZ,
    sX3, sY3, sZ3, Prod.mk.injEq]
  have iX : slotFieldVal N s0 base 0 = V 0 :=
    (slotFieldVal_const R 0 0 jacDblCallsA.length (by omega) le_rfl (by decide)).symm
  have iY : slotFieldVal N s0 base 1 = V 1 :=
    (slotFieldVal_const R 1 0 jacDblCallsA.length (by omega) le_rfl (by decide)).symm
  have iZ : slotFieldVal N s0 base 2 = V 2 :=
    (slotFieldVal_const R 2 0 jacDblCallsA.length (by omega) le_rfl (by decide)).symm
  rw [iX, iY, iZ]
  have oX3 : slotFieldVal N (trajState s0 jacDblCallsA.length) base 3 = V 3 := rfl
  have oY3 : slotFieldVal N (trajState s0 jacDblCallsA.length) base 4 = V 4 := rfl
  have oZ3 : slotFieldVal N (trajState s0 jacDblCallsA.length) base 5 = V 5 := rfl
  rw [oX3, oY3, oZ3]
  rw [c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4,
    c3, c2, c1, c0]
  refine ⟨?_, ?_, ?_⟩ <;> ring

end CatCrypt.Crypto.SecureCompilation.X86Backend.EcJacDblABlock
