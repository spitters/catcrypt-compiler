/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CarryChainZeroIn

/-!
# Two interleaved carry chains

`CarryChainTie.lowerCarryBlock_tie` ties a single carry chain, lowered to `adc`,
to its `Com jasminDialect` denotation. One chain is all `adc` can carry: the
instruction writes all five flags, so the carry of a second chain cannot survive
a step of the first. This module covers the two-chain form, over the `adcx` /
`adox` pair: `adcx` reads and writes `CF` and leaves the other four flags alone,
`adox` reads and writes `OF` and leaves the other four alone, so two chains,
one per flag, can share one instruction stream.

## The block type

`TwoChainBlock Γ cC cO` is indexed by two live carry variables: `cC` for the
chain held in `CF` and `cO` for the chain held in `OF`. A `stepCF` consumes `cC`,
binds a data word and a new carry-out, and continues with the bound carry-out as
its `CF` carry while its `OF` carry is `cO` transported through the two new
binders — the same variable, not a rebound one. `stepOF` is the mirror image.

## The correspondence

`TwoChainInterp` is `JStateInterpG` on the registers conjoined with two carry
clauses, one per flag. `JStateInterpG` is used unchanged.

## Scope

* The two chains are the two flags `CF` and `OF`. A third chain has no flag to
  live in, so the block type is fixed at two.
* `TwoChainInterp` constrains `CF` and `OF`. `PF`, `SF` and `ZF` are outside the
  correspondence; the lowered steps happen to leave them alone, which is not
  stated.
* The tie covers chains whose two carry-ins are variables of the entry context,
  with `TwoChainInterp` asserting that `CF` and `OF` already hold their values.
  Establishing a zero `CF` is `CarryChainZeroIn.clearCarry`; `JInstr` has no
  `OF`-clearing arm, so the corresponding prefix for the `OF` chain is not
  available here.
* A step allocates one fresh register for its data word. The carry-out stays in
  its flag and is not materialised.
* The two chains are independent on the dialect side by construction: each
  carry is an SSA variable and a step of one chain does not mention the other's.
  The content of the interleave is on the machine side, where both chains share
  one flag register file; it is carried by `lowerAdcx_of` and `lowerAdox_cf` and
  used in `lowerTwoChain_tie`. `interCF_denote_eq_cfOnly` and
  `interOF_denote_eq_ofOnly` are therefore statements about the block type, and
  it is composing them with the tie that says the machine run agrees.
* The witness fixes one interleaved shape, one register map, one fresh stream and
  one entry state. It is a value check on those, not a statement about the
  family.

## What is proved

* `addCarryWord_adcx`, `carryOutBit_adcx` — the dialect carry-step pair against
  `x86_ADCX`, the function backing both `adcx` and `adox`.
* `lowerAdcx`, `lowerAdox` and their per-step lemmas: the data word, the flag the
  step writes, the flag it leaves alone, and its register frame. `lowerAdcx_of`
  and `lowerAdox_cf` are the flag independence the interleave rests on.
* `TwoChainInterp` — the three-axis state correspondence.
* `TwoChainBlock`, `TwoChainBlock.toCom`, `lowerTwoChain`, `outRegT` — the
  two-chain block, its `Com jasminDialect` image and its machine lowering.
* `lowerTwoChain_tie` — the block tie.
* `interCF`, `interOF` — one interleaved seven-step witness, read at the `CF`
  chain's output and at the `OF` chain's output, with
  `lowerTwoChain_interCF_eq_interOF` recording that the two readings are of one
  instruction stream.
* `interCF_denote_eq_cfOnly`, `interOF_denote_eq_ofOnly` — the interleaved
  block's denotation at each output equals the denotation of that chain run on
  its own as a `CarryChainTie.CarryBlock`, for every valuation.
* `interCF_run`, `interOF_run` — the machine run of the interleaved lowering at
  the witness state and its two output registers.
* `interCF_denote_carryFlip`, `interOF_denote_carryFlip` — each output changes
  when its own chain's carry changes, so neither output is blind to the carry it
  threads.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.CarryChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## 1. `x86_ADCX` realises the dialect's carry-step pair

`x86_ADCX` is the machine model's shared body of `adcx` and `adox`: it returns
the carry bool and the low word of `waddcarry`. The instruction arms differ only
in which flag they route the carry to. -/

/-- **Data agreement.** The dialect's carry-add word is the `x86_ADCX` data
    output. -/
theorem addCarryWord_adcx (v1 v2 : BitVec 64) (c : Bool) :
    addCarryWord v1 v2 (BitVec.ofBool c) = (x86_ADCX v1 v2 c).2 := by
  apply BitVec.eq_of_toNat_eq
  cases c <;>
    simp [addCarryWord, x86_ADCX, waddcarry, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.mod_mod_of_dvd, Nat.add_mod]

/-- **Carry agreement.** The dialect's carry-out bit is the carry `x86_ADCX`
    returns. -/
theorem carryOutBit_adcx (v1 v2 : BitVec 64) (c : Bool) :
    carryOutBit v1 v2 (BitVec.ofBool c)
      = BitVec.ofBool ((x86_ADCX v1 v2 c).1.getD false) := by
  have hc : (BitVec.ofBool c).toNat = (if c then 1 else 0) := by cases c <;> rfl
  simp only [carryOutBit, x86_ADCX, waddcarry, Option.getD_some, hc]
  by_cases h : 2 ^ 64 ≤ v1.toNat + v2.toNat + (if c then 1 else 0)
  · simp [h, BitVec.ofBool]
  · simp [h, BitVec.ofBool]

/-! ## 2. The per-step machine lowerings

Each step primes its destination with a `mov` and then accumulates into it. The
`mov` is a register write, so both flags reach the accumulating instruction
unchanged. -/

/-- The machine block of one `CF`-chain step: `mov dst, ra ; adcx dst, rb`. -/
def lowerAdcx (ra rb dst : String) : List (JInstr 64) :=
  [ .mov dst (.reg ra)
  , .adcx dst (.reg rb) ]

/-- The machine block of one `OF`-chain step: `mov dst, ra ; adox dst, rb`. -/
def lowerAdox (ra rb dst : String) : List (JInstr 64) :=
  [ .mov dst (.reg ra)
  , .adox dst (.reg rb) ]

/-- **Data word of a `CF` step.** Reading `dst` after the lowered step yields the
    dialect's `addCarryLo 64` at the entry `CF`. Needs `dst ≠ rb` so the priming
    `mov` does not clobber the `b` read. -/
theorem lowerAdcx_get_dst (ra rb dst : String) (hne : dst ≠ rb) (s : JState 64) :
    (runBlock s (lowerAdcx ra rb dst)).get dst
      = addCarryWord (s.get ra) (s.get rb) (BitVec.ofBool (s.flagB (·.cf))) := by
  have hrb : rb ≠ dst := fun h => hne h.symm
  simp only [lowerAdcx, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, JState.flagB, if_true, if_neg hrb]
  exact (addCarryWord_adcx _ _ _).symm

/-- **Carry-out of a `CF` step.** The `CF` left by the step is the dialect's
    `addCarryHi 64` bit, which the chain's next step reads. -/
theorem lowerAdcx_cf (ra rb dst : String) (hne : dst ≠ rb) (s : JState 64) :
    BitVec.ofBool ((runBlock s (lowerAdcx ra rb dst)).flagB (·.cf))
      = carryOutBit (s.get ra) (s.get rb) (BitVec.ofBool (s.flagB (·.cf))) := by
  have hrb : rb ≠ dst := fun h => hne h.symm
  simp only [lowerAdcx, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, JState.flagB, if_neg hrb]
  exact (carryOutBit_adcx _ _ _).symm

/-- **A `CF` step leaves `OF` alone.** This is what lets the `OF` chain's carry
    survive a step of the `CF` chain. -/
theorem lowerAdcx_of (ra rb dst : String) (s : JState 64) :
    (runBlock s (lowerAdcx ra rb dst)).flagB (·.of) = s.flagB (·.of) := rfl

/-- **Register frame of a `CF` step.** The step writes only `dst`. -/
theorem lowerAdcx_get_other (ra rb dst r : String) (hr : r ≠ dst) (s : JState 64) :
    (runBlock s (lowerAdcx ra rb dst)).get r = s.get r := by
  simp only [lowerAdcx, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, if_neg hr]

/-- **Data word of an `OF` step.** Reading `dst` after the lowered step yields the
    dialect's `addCarryLo 64` at the entry `OF`. -/
theorem lowerAdox_get_dst (ra rb dst : String) (hne : dst ≠ rb) (s : JState 64) :
    (runBlock s (lowerAdox ra rb dst)).get dst
      = addCarryWord (s.get ra) (s.get rb) (BitVec.ofBool (s.flagB (·.of))) := by
  have hrb : rb ≠ dst := fun h => hne h.symm
  simp only [lowerAdox, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, JState.flagB, if_true, if_neg hrb]
  exact (addCarryWord_adcx _ _ _).symm

/-- **Carry-out of an `OF` step.** The `OF` left by the step is the dialect's
    `addCarryHi 64` bit. -/
theorem lowerAdox_of (ra rb dst : String) (hne : dst ≠ rb) (s : JState 64) :
    BitVec.ofBool ((runBlock s (lowerAdox ra rb dst)).flagB (·.of))
      = carryOutBit (s.get ra) (s.get rb) (BitVec.ofBool (s.flagB (·.of))) := by
  have hrb : rb ≠ dst := fun h => hne h.symm
  simp only [lowerAdox, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, JState.flagB, if_neg hrb]
  exact (carryOutBit_adcx _ _ _).symm

/-- **An `OF` step leaves `CF` alone.** This is what lets the `CF` chain's carry
    survive a step of the `OF` chain. -/
theorem lowerAdox_cf (ra rb dst : String) (s : JState 64) :
    (runBlock s (lowerAdox ra rb dst)).flagB (·.cf) = s.flagB (·.cf) := rfl

/-- **Register frame of an `OF` step.** The step writes only `dst`. -/
theorem lowerAdox_get_other (ra rb dst r : String) (hr : r ≠ dst) (s : JState 64) :
    (runBlock s (lowerAdox ra rb dst)).get r = s.get r := by
  simp only [lowerAdox, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, if_neg hr]

/-! ## 3. The three-axis state correspondence -/

/-- **The two-chain state correspondence.** The register axis is
    `JStateInterpG ρ V s`; the two carry axes say `CF` holds the value of the live
    `CF`-chain variable `cC` and `OF` that of the live `OF`-chain variable
    `cO`. -/
def TwoChainInterp {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ)
    (cC cO : Ctxt.Var Γ (.reg 1)) (V : Ctxt.Valuation Γ) (s : JState 64) : Prop :=
  JStateInterpG ρ V s
    ∧ BitVec.ofBool (s.flagB (·.cf)) = cC.lookup V
    ∧ BitVec.ofBool (s.flagB (·.of)) = cO.lookup V

/-! ## 4. The two-chain block and its `Com` image -/

/-- The context a step grows: the data word's `reg 64` slot and the carry-out's
    `reg 1` slot, in the order `toCom` binds them. -/
abbrev grow2 (Γ : Ctxt jasminDialect) : Ctxt jasminDialect :=
  .reg 1 :: .reg 64 :: Γ

/-- Transport a variable across the two slots a step binds. -/
def shift2Var {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (v : Ctxt.Var Γ t) : Ctxt.Var (grow2 Γ) t := .there (.there v)

/-- **Two carry chains over the context `Γ`, with live carries `cC` in `CF` and
    `cO` in `OF`.** A `stepCF` consumes `cC` and rebinds it, transporting `cO`
    unchanged; a `stepOF` is the mirror image. The block ends by returning a
    `reg 64` variable. -/
inductive TwoChainBlock : (Γ : Ctxt jasminDialect) →
    Ctxt.Var Γ (.reg 1) → Ctxt.Var Γ (.reg 1) → Type where
  /-- Return one `reg 64` variable — the block's output. -/
  | ret {Γ : Ctxt jasminDialect} {cC cO : Ctxt.Var Γ (.reg 1)}
      (v : Ctxt.Var Γ (.reg 64)) : TwoChainBlock Γ cC cO
  /-- One step of the `CF` chain: `d := a + b + cC ; cC' := carry-out`. The `OF`
      chain's live carry is `cO` transported across the two binders. -/
  | stepCF {Γ : Ctxt jasminDialect} {cC cO : Ctxt.Var Γ (.reg 1)}
      (a b : Ctxt.Var Γ (.reg 64))
      (rest : TwoChainBlock (grow2 Γ) Ctxt.Var.here (shift2Var cO)) :
      TwoChainBlock Γ cC cO
  /-- One step of the `OF` chain: `d := a + b + cO ; cO' := carry-out`. The `CF`
      chain's live carry is `cC` transported across the two binders. -/
  | stepOF {Γ : Ctxt jasminDialect} {cC cO : Ctxt.Var Γ (.reg 1)}
      (a b : Ctxt.Var Γ (.reg 64))
      (rest : TwoChainBlock (grow2 Γ) (shift2Var cC) Ctxt.Var.here) :
      TwoChainBlock Γ cC cO

/-- **Compile a `TwoChainBlock` to a `Com jasminDialect`.** Each step becomes the
    two nested binders `addCarryLo` then `addCarryHi` over its own chain's carry;
    `ret` is `Com.ret`. -/
def TwoChainBlock.toCom : {Γ : Ctxt jasminDialect} →
    {cC cO : Ctxt.Var Γ (.reg 1)} → TwoChainBlock Γ cC cO →
    Com jasminDialect Γ (.reg 64)
  | _, _, _, .ret v => .ret v
  | _, cC, _, .stepCF a b rest =>
      .var (carryLoExpr a b cC)
        (.var (carryHiExpr (.there a) (.there b) (.there cC)) rest.toCom)
  | _, _, cO, .stepOF a b rest =>
      .var (carryLoExpr a b cO)
        (.var (carryHiExpr (.there a) (.there b) (.there cO)) rest.toCom)

/-- **The two-chain machine lowering.** A `CF` step emits `lowerAdcx`, an `OF`
    step `lowerAdox`, each consuming one fresh register (`g 0`) for its data word;
    the `ret` emits nothing. -/
def lowerTwoChain : {Γ : Ctxt jasminDialect} →
    {cC cO : Ctxt.Var Γ (.reg 1)} → TwoChainBlock Γ cC cO →
    RegMapG Γ → (Nat → String) → List (JInstr 64)
  | _, _, _, .ret _, _, _ => []
  | _, _, _, .stepCF a b rest, ρ, g =>
      lowerAdcx (ρ a) (ρ b) (g 0)
        ++ lowerTwoChain rest (RegMapG.shiftBit (ρ.extend (g 0)))
             (fun k => g (k + 1))
  | _, _, _, .stepOF a b rest, ρ, g =>
      lowerAdox (ρ a) (ρ b) (g 0)
        ++ lowerTwoChain rest (RegMapG.shiftBit (ρ.extend (g 0)))
             (fun k => g (k + 1))

/-- The block's output register: the register of the returned variable under the
    accumulated register map. -/
def outRegT : {Γ : Ctxt jasminDialect} → {cC cO : Ctxt.Var Γ (.reg 1)} →
    TwoChainBlock Γ cC cO → RegMapG Γ → (Nat → String) → String
  | _, _, _, .ret v, ρ, _ => ρ v
  | _, _, _, .stepCF _ _ rest, ρ, g =>
      outRegT rest (RegMapG.shiftBit (ρ.extend (g 0))) (fun k => g (k + 1))
  | _, _, _, .stepOF _ _ rest, ρ, g =>
      outRegT rest (RegMapG.shiftBit (ρ.extend (g 0))) (fun k => g (k + 1))

/-! ## 5. The tie -/

/-- **The block tie for two interleaved carry chains.** For every
    `TwoChainBlock`, under the three-axis correspondence `TwoChainInterp` and a
    fresh allocation `FreshFor ρ g`, reading the block's output register after
    `runBlock` of the whole lowered stream equals the block's
    `Com jasminDialect` denotation on `V`. Structural induction: a `CF` step
    re-establishes the register axis from `lowerAdcx_get_dst` and
    `lowerAdcx_get_other`, its own carry axis from `lowerAdcx_cf`, and the other
    chain's carry axis from `lowerAdcx_of`; an `OF` step is the mirror image. -/
theorem lowerTwoChain_tie : {Γ : Ctxt jasminDialect} →
    {cC cO : Ctxt.Var Γ (.reg 1)} → (block : TwoChainBlock Γ cC cO) →
    (ρ : RegMapG Γ) → (g : Nat → String) → (s : JState 64) →
    (V : Ctxt.Valuation Γ) → TwoChainInterp ρ cC cO V s → FreshFor ρ g →
    (runBlock s (lowerTwoChain block ρ g)).get (outRegT block ρ g)
      = block.toCom.denote V
  | _, _, _, .ret v, ρ, g, s, V, hinterp, _ => by
      simp only [lowerTwoChain, outRegT, runBlock_nil, TwoChainBlock.toCom,
        Com.denote]
      exact hinterp.1 v
  | _, cC, cO, .stepCF a b rest, ρ, g, s, V, hinterp, hfresh => by
      obtain ⟨hreg, hcf, hof⟩ := hinterp
      have hdisj := hfresh.2 0
      have hne : g 0 ≠ ρ b := hdisj b
      have hinterp' : TwoChainInterp (RegMapG.shiftBit (ρ.extend (g 0)))
          Ctxt.Var.here (shift2Var cO)
          ((V.extend ((carryLoExpr a b cC).denote V)).extend
            ((carryHiExpr (.there a) (.there b) (.there cC)).denote
              (V.extend ((carryLoExpr a b cC).denote V))))
          (runBlock s (lowerAdcx (ρ a) (ρ b) (g 0))) := by
        refine ⟨?_, ?_, ?_⟩
        · intro w
          match w with
          | .there .here =>
              show (runBlock s (lowerAdcx (ρ a) (ρ b) (g 0))).get (g 0)
                  = addCarryWord (a.lookup V) (b.lookup V) (cC.lookup V)
              rw [lowerAdcx_get_dst (ρ a) (ρ b) (g 0) hne s, hreg a, hreg b, hcf]
          | .there (.there w0) =>
              show (runBlock s (lowerAdcx (ρ a) (ρ b) (g 0))).get (ρ w0)
                  = w0.lookup V
              rw [lowerAdcx_get_other (ρ a) (ρ b) (g 0) (ρ w0)
                (fun h => (hdisj w0) h.symm) s]
              exact hreg w0
        · show BitVec.ofBool
                ((runBlock s (lowerAdcx (ρ a) (ρ b) (g 0))).flagB (·.cf))
              = carryOutBit (a.lookup V) (b.lookup V) (cC.lookup V)
          rw [lowerAdcx_cf (ρ a) (ρ b) (g 0) hne s, hreg a, hreg b, hcf]
        · show BitVec.ofBool
                ((runBlock s (lowerAdcx (ρ a) (ρ b) (g 0))).flagB (·.of))
              = cO.lookup V
          rw [lowerAdcx_of (ρ a) (ρ b) (g 0) s]
          exact hof
      have hfresh' : FreshFor (RegMapG.shiftBit (ρ.extend (g 0)))
          (fun k => g (k + 1)) :=
        FreshFor_shiftBit _ _ (FreshFor_extend ρ g hfresh)
      have key := lowerTwoChain_tie rest (RegMapG.shiftBit (ρ.extend (g 0)))
        (fun k => g (k + 1)) (runBlock s (lowerAdcx (ρ a) (ρ b) (g 0)))
        ((V.extend ((carryLoExpr a b cC).denote V)).extend
          ((carryHiExpr (.there a) (.there b) (.there cC)).denote
            (V.extend ((carryLoExpr a b cC).denote V))))
        hinterp' hfresh'
      simpa only [lowerTwoChain, outRegT, TwoChainBlock.toCom, Com.denote,
        runBlock_append] using key
  | _, cC, cO, .stepOF a b rest, ρ, g, s, V, hinterp, hfresh => by
      obtain ⟨hreg, hcf, hof⟩ := hinterp
      have hdisj := hfresh.2 0
      have hne : g 0 ≠ ρ b := hdisj b
      have hinterp' : TwoChainInterp (RegMapG.shiftBit (ρ.extend (g 0)))
          (shift2Var cC) Ctxt.Var.here
          ((V.extend ((carryLoExpr a b cO).denote V)).extend
            ((carryHiExpr (.there a) (.there b) (.there cO)).denote
              (V.extend ((carryLoExpr a b cO).denote V))))
          (runBlock s (lowerAdox (ρ a) (ρ b) (g 0))) := by
        refine ⟨?_, ?_, ?_⟩
        · intro w
          match w with
          | .there .here =>
              show (runBlock s (lowerAdox (ρ a) (ρ b) (g 0))).get (g 0)
                  = addCarryWord (a.lookup V) (b.lookup V) (cO.lookup V)
              rw [lowerAdox_get_dst (ρ a) (ρ b) (g 0) hne s, hreg a, hreg b, hof]
          | .there (.there w0) =>
              show (runBlock s (lowerAdox (ρ a) (ρ b) (g 0))).get (ρ w0)
                  = w0.lookup V
              rw [lowerAdox_get_other (ρ a) (ρ b) (g 0) (ρ w0)
                (fun h => (hdisj w0) h.symm) s]
              exact hreg w0
        · show BitVec.ofBool
                ((runBlock s (lowerAdox (ρ a) (ρ b) (g 0))).flagB (·.cf))
              = cC.lookup V
          rw [lowerAdox_cf (ρ a) (ρ b) (g 0) s]
          exact hcf
        · show BitVec.ofBool
                ((runBlock s (lowerAdox (ρ a) (ρ b) (g 0))).flagB (·.of))
              = carryOutBit (a.lookup V) (b.lookup V) (cO.lookup V)
          rw [lowerAdox_of (ρ a) (ρ b) (g 0) hne s, hreg a, hreg b, hof]
      have hfresh' : FreshFor (RegMapG.shiftBit (ρ.extend (g 0)))
          (fun k => g (k + 1)) :=
        FreshFor_shiftBit _ _ (FreshFor_extend ρ g hfresh)
      have key := lowerTwoChain_tie rest (RegMapG.shiftBit (ρ.extend (g 0)))
        (fun k => g (k + 1)) (runBlock s (lowerAdox (ρ a) (ρ b) (g 0)))
        ((V.extend ((carryLoExpr a b cO).denote V)).extend
          ((carryHiExpr (.there a) (.there b) (.there cO)).denote
            (V.extend ((carryLoExpr a b cO).denote V))))
        hinterp' hfresh'
      simpa only [lowerTwoChain, outRegT, TwoChainBlock.toCom, Com.denote,
        runBlock_append] using key

/-! ## 6. An interleaved witness

The two chains alternate in the instruction stream: `CF`, `OF`, `CF`, `OF`, `CF`,
`OF`, `CF`. The operands are drawn from five `reg 64` variables holding
`2 ^ 64 - 1`, `1`, `0`, `5` and `7`.

Reading the chains separately at the witness valuation:

* the `CF` chain is `(M, 1)`, `(M, 0)`, `(M, 0)`, `(5, 7)` from carry `0`, whose
  carries are `1, 1, 1` and whose last word is `13`;
* the `OF` chain is `(M, 1)`, `(5, 7)`, `(M, 0)` from carry `0`, whose carries
  are `1, 0` and whose last word is `M`.

Each chain consumes a carry of `1`, and each output depends on the last carry of
its own chain: `interCF_denote_carryFlip` and `interOF_denote_carryFlip` give the
outputs `12` and `0` at valuations that change those carries. The two carry
sequences also diverge: the `CF` chain's third step is preceded by an `OF` step
leaving `0` where `CF` holds `1`, and the `OF` chain's third step is preceded by
a `CF` step leaving `1` where `OF` holds `0`. Each output would therefore change
if either flag were written by the other chain's instruction. -/

/-- The witness context: the two entry carries and the five operand values. -/
abbrev Γt : Ctxt jasminDialect :=
  [.reg 1, .reg 1, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64]

/-- The `CF` chain's entry carry. -/
abbrev cCt : Ctxt.Var Γt (.reg 1) := .here

/-- The `OF` chain's entry carry. -/
abbrev cOt : Ctxt.Var Γt (.reg 1) := .there .here

/-- The operand variable holding `2 ^ 64 - 1`. -/
abbrev vM : Ctxt.Var Γt (.reg 64) := .there (.there .here)

/-- The operand variable holding `1`. -/
abbrev vOne : Ctxt.Var Γt (.reg 64) := .there (.there (.there .here))

/-- The operand variable holding `0`. -/
abbrev vZero : Ctxt.Var Γt (.reg 64) := .there (.there (.there (.there .here)))

/-- The operand variable holding `5`. -/
abbrev vFive : Ctxt.Var Γt (.reg 64) :=
  .there (.there (.there (.there (.there .here))))

/-- The operand variable holding `7`. -/
abbrev vSeven : Ctxt.Var Γt (.reg 64) :=
  .there (.there (.there (.there (.there (.there .here)))))

/-- The context after the witness's seven steps. -/
abbrev Γend : Ctxt jasminDialect :=
  grow2 (grow2 (grow2 (grow2 (grow2 (grow2 (grow2 Γt))))))

/-- The interleaved seven-step witness, parametric in the variable it returns.
    The steps alternate `CF`, `OF`, `CF`, `OF`, `CF`, `OF`, `CF`. -/
def interBody (out : Ctxt.Var Γend (.reg 64)) : TwoChainBlock Γt cCt cOt :=
  .stepCF vM vOne
    (.stepOF (shift2Var vM) (shift2Var vOne)
      (.stepCF (shift2Var (shift2Var vM)) (shift2Var (shift2Var vZero))
        (.stepOF (shift2Var (shift2Var (shift2Var vFive)))
            (shift2Var (shift2Var (shift2Var vSeven)))
          (.stepCF (shift2Var (shift2Var (shift2Var (shift2Var vM))))
              (shift2Var (shift2Var (shift2Var (shift2Var vZero))))
            (.stepOF
                (shift2Var (shift2Var (shift2Var (shift2Var (shift2Var vM)))))
                (shift2Var (shift2Var (shift2Var (shift2Var (shift2Var vZero)))))
              (.stepCF
                  (shift2Var (shift2Var (shift2Var (shift2Var
                    (shift2Var (shift2Var vFive))))))
                  (shift2Var (shift2Var (shift2Var (shift2Var
                    (shift2Var (shift2Var vSeven))))))
                (.ret out)))))))

/-- The interleaved witness read at the `CF` chain's output: the data word of the
    last step, which is a `CF` step. -/
def interCF : TwoChainBlock Γt cCt cOt := interBody (.there .here)

/-- The interleaved witness read at the `OF` chain's output: the data word of the
    last `OF` step, two binders further down. -/
def interOF : TwoChainBlock Γt cCt cOt := interBody (shift2Var (.there .here))

/-- The two readings are of one instruction stream: a `ret` emits nothing, so the
    lowerings coincide. -/
theorem lowerTwoChain_interCF_eq_interOF (ρ : RegMapG Γt) (g : Nat → String) :
    lowerTwoChain interCF ρ g = lowerTwoChain interOF ρ g := rfl

/-! ### The same chains run on their own -/

/-- The `CF` chain of the witness as a single-chain `CarryChainTie.CarryBlock`. -/
def cfOnly : CarryBlock Γt cCt :=
  .step vM vOne
    (.step (.there (.there vM)) (.there (.there vZero))
      (.step (.there (.there (.there (.there vM))))
          (.there (.there (.there (.there vZero))))
        (.step (.there (.there (.there (.there (.there (.there vFive))))))
            (.there (.there (.there (.there (.there (.there vSeven))))))
          (.ret (.there .here)))))

/-- The `OF` chain of the witness as a single-chain `CarryChainTie.CarryBlock`. -/
def ofOnly : CarryBlock Γt cOt :=
  .step vM vOne
    (.step (.there (.there vFive)) (.there (.there vSeven))
      (.step (.there (.there (.there (.there vM))))
          (.there (.there (.there (.there vZero))))
        (.ret (.there .here))))

/-- **The `CF` chain is unaffected by the interleaved `OF` steps.** At the `CF`
    output, the interleaved block denotes what the `CF` chain denotes on its own,
    for every valuation. -/
theorem interCF_denote_eq_cfOnly (V : Ctxt.Valuation Γt) :
    interCF.toCom.denote V = cfOnly.toCom.denote V := rfl

/-- **The `OF` chain is unaffected by the interleaved `CF` steps.** At the `OF`
    output, the interleaved block denotes what the `OF` chain denotes on its own,
    for every valuation. -/
theorem interOF_denote_eq_ofOnly (V : Ctxt.Valuation Γt) :
    interOF.toCom.denote V = ofOnly.toCom.denote V := rfl

/-! ### The witness valuation, register map and machine state -/

/-- The witness valuation: both entry carries `0`, operands `2 ^ 64 - 1`, `1`,
    `0`, `5`, `7`. -/
def tVal : Ctxt.Valuation Γt :=
  .cons (0 : BitVec 1)
    (.cons (0 : BitVec 1)
      (.cons (BitVec.ofNat 64 (2 ^ 64 - 1))
        (.cons (1 : BitVec 64)
          (.cons (0 : BitVec 64)
            (.cons (5 : BitVec 64) (.cons (7 : BitVec 64) .nil))))))

/-- The `CF` chain's output at the witness valuation: the last word is `5 + 7`
    taken at the chain's third carry, which is `1`. -/
theorem interCF_denote_tVal : interCF.toCom.denote tVal = (13 : BitVec 64) := rfl

/-- The `OF` chain's output at the witness valuation: the last word is
    `(2 ^ 64 - 1) + 0` taken at the chain's second carry, which is `0`. -/
theorem interOF_denote_tVal :
    interOF.toCom.denote tVal = BitVec.ofNat 64 (2 ^ 64 - 1) := rfl

/-- The witness valuation with the `CF` chain's third carry flipped: `vZero`
    holds `1`, so the third `CF` step wraps and the output becomes `5 + 7 + 1`
    against the chain's own carry. Read with `interCF_denote_tVal`, the `CF`
    output is not blind to the carry its chain threads. -/
def tValCfFlip : Ctxt.Valuation Γt :=
  .cons (0 : BitVec 1)
    (.cons (0 : BitVec 1)
      (.cons (BitVec.ofNat 64 (2 ^ 64 - 1))
        (.cons (0 : BitVec 64)
          (.cons (0 : BitVec 64)
            (.cons (5 : BitVec 64) (.cons (7 : BitVec 64) .nil))))))

/-- The `CF` output changes when the `CF` chain's carries change. -/
theorem interCF_denote_carryFlip :
    interCF.toCom.denote tValCfFlip = (12 : BitVec 64) := rfl

/-- The witness valuation with the `OF` chain's second carry flipped: `vFive`
    holds `2 ^ 64 - 1`, so the `OF` chain's second step wraps and its third step
    reads a carry of `1`. -/
def tValOfFlip : Ctxt.Valuation Γt :=
  .cons (0 : BitVec 1)
    (.cons (0 : BitVec 1)
      (.cons (BitVec.ofNat 64 (2 ^ 64 - 1))
        (.cons (1 : BitVec 64)
          (.cons (0 : BitVec 64)
            (.cons (BitVec.ofNat 64 (2 ^ 64 - 1))
              (.cons (7 : BitVec 64) .nil))))))

/-- The `OF` output changes when the `OF` chain's carries change. -/
theorem interOF_denote_carryFlip :
    interOF.toCom.denote tValOfFlip = (0 : BitVec 64) := rfl

/-- The witness register map. -/
def tRho : RegMapG Γt
  | .there (.there .here) => "vM"
  | .there (.there (.there .here)) => "vOne"
  | .there (.there (.there (.there .here))) => "vZero"
  | .there (.there (.there (.there (.there .here)))) => "vFive"
  | .there (.there (.there (.there (.there (.there .here))))) => "vSeven"

/-- No name in `CarryChainZeroIn.dStream` is one of the witness map's registers:
    those begin with `v`, every stream name with `d`. -/
theorem dStream_ne_tRho (i : Nat) (v : Ctxt.Var Γt (.reg 64)) :
    dStream i ≠ tRho v := by
  match v with
  | .there (.there .here) =>
      show dStream i ≠ "vM"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h
  | .there (.there (.there .here)) =>
      show dStream i ≠ "vOne"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h
  | .there (.there (.there (.there .here))) =>
      show dStream i ≠ "vZero"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h
  | .there (.there (.there (.there (.there .here)))) =>
      show dStream i ≠ "vFive"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h
  | .there (.there (.there (.there (.there (.there .here))))) =>
      show dStream i ≠ "vSeven"
      intro h; simp only [dStream] at h; simpa using congrArg String.toList h

/-- The fresh invariant for the witness register map and stream. -/
theorem dStream_freshFor_tRho : FreshFor tRho dStream :=
  ⟨dStream_injective, fun i v => dStream_ne_tRho i v⟩

/-- The witness machine state: the five operand values in the registers `tRho`
    names, with both `CF` and `OF` cleared. -/
def tState : JState 64 :=
  { regs := fun r =>
      if r = "vM" then BitVec.ofNat 64 (2 ^ 64 - 1) else
      if r = "vOne" then 1 else
      if r = "vZero" then 0 else
      if r = "vFive" then 5 else
      if r = "vSeven" then 7 else 0
    flags := { cf := some false, of := some false } }

/-- The three-axis correspondence holds between `tState` and `tVal` under
    `tRho`. -/
theorem tState_interp : TwoChainInterp tRho cCt cOt tVal tState := by
  refine ⟨fun v => ?_, rfl, rfl⟩
  match v with
  | .there (.there .here) => rfl
  | .there (.there (.there .here)) => rfl
  | .there (.there (.there (.there .here))) => rfl
  | .there (.there (.there (.there (.there .here)))) => rfl
  | .there (.there (.there (.there (.there (.there .here))))) => rfl

/-- **The interleaved machine run at the `CF` output.** The lowered stream is
    seven alternating `adcx` / `adox` steps; the `CF` chain's output register
    holds `13`. -/
theorem interCF_run :
    (runBlock tState (lowerTwoChain interCF tRho dStream)).get
        (outRegT interCF tRho dStream) = (13 : BitVec 64) := by
  rw [lowerTwoChain_tie interCF tRho dStream tState tVal tState_interp
    dStream_freshFor_tRho]
  exact interCF_denote_tVal

/-- **The interleaved machine run at the `OF` output.** The same stream; the `OF`
    chain's output register holds `2 ^ 64 - 1`. -/
theorem interOF_run :
    (runBlock tState (lowerTwoChain interOF tRho dStream)).get
        (outRegT interOF tRho dStream) = BitVec.ofNat 64 (2 ^ 64 - 1) := by
  rw [lowerTwoChain_tie interOF tRho dStream tState tVal tState_interp
    dStream_freshFor_tRho]
  exact interOF_denote_tVal

end CatCrypt.Crypto.SecureCompilation.Ascent.CarryChain
