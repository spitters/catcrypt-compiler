/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockRealloc

/-!
# The block tie for a carry chain

`JasminComRunBlockRealloc.lowerBlockR_tie` ties a straight-line block of
two-input, single-`reg 64`-output ops (`arith`, `mulhi`) to its machine run. This
module adds the carry-chain step: the pair of dialect ops `addCarryLo 64` (the
data word `a + b + cin`) and `addCarryHi 64` (the propagated carry bit), lowered
to `mov dst, a ; adc dst, b`.

The dialect threads the carry as an explicit `reg 1` SSA variable; the machine
threads it in `JState.flags.cf`. The state correspondence therefore has two
axes, and `CarryInterp` is the pair: `JStateInterpG` on the registers, plus the
carry clause relating the live `reg 1` variable to `CF`. `JStateInterpG` is used
unchanged.

## The block type

`CarryBlock Γ c` is indexed by the live carry variable `c : Ctxt.Var Γ (.reg 1)`.
A `step` consumes `c` and its continuation is indexed by `.here` — the `reg 1`
slot that step bound. The chain shape is therefore part of the type: each step's
carry-in is the immediately preceding step's carry-out, and the first step's
carry-in is the index of the whole block.

## Scope

* The arm is a **new block type**, not an arm of `RegBlock`. The two cannot be
  mixed: `lowerArith2` emits a flag-setting ALU instruction (`x86_ADD` and the
  rest write all five flags through `JState.writeB5W`), so an `arith` step
  between two carry steps destroys the `CF` the chain reads. Interleaving needs
  the carry materialised into a register and read back, which is a different
  lowering from the one proved here.
* The tie covers chains whose carry-in is a variable of the entry context, with
  `CarryInterp` asserting that `CF` already holds its value. A chain starting
  from a literal zero carry is that statement with the entry variable valued `0`;
  nothing here emits the `clc`/`xor` that would establish it.
* The lowering is `adc`, not `adcx`. Both have the same data word and carry-out
  (`x86_ADC.word`/`.cf` and `x86_ADCX` are both `waddcarry`), and both read `CF`;
  they differ in the flags they clobber — `adc` writes all five, `adcx` only
  `CF`. `CarryInterp` constrains `CF` alone, so the extra clobber is outside the
  correspondence. A chain that needs `OF` preserved across the steps (the
  `adcx`/`adox` two-chain interleave) is not covered.
* A step allocates one fresh register for the data word. The carry-out is not
  materialised: it stays in `CF`, which is why `FreshFor` shifts by one.

## What is proved

* `addCarryWord_adc`, `carryOutBit_adc` — the dialect carry-step pair against
  `x86_ADC`, with `BitVec.ofBool` joining the `reg 1` carry to the machine flag.
* `lowerAdc`, `lowerAdc_get_dst`, `lowerAdc_cf`, `lowerAdc_get_other` — the
  per-step machine lowering, its data word, its carry-out and its register frame.
* `CarryInterp` — the two-axis state correspondence.
* `CarryBlock`, `CarryBlock.toCom`, `lowerCarryBlock`, `outRegC` — the carry-chain
  block, its `Com jasminDialect` image and its machine lowering.
* `lowerCarryBlock_tie` — the block tie: reading the output register after
  `runBlock` of the lowered chain equals the chain's `Com` denotation.
* `twoLimbBlock`, `twoLimbBlock_tie`, `twoLimbRun`, `twoLimb_carry_out_one` — a
  two-limb witness whose low limb overflows, so the high limb's result is
  `5 + 7 + 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.CarryChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## 1. `adc` realises the dialect's carry-step pair

`addCarryWord` and `carryOutBit` are the denotations of `addCarryLo 64` and
`addCarryHi 64`; `x86_ADC` is the machine step. The carry is a `BitVec 1` on the
dialect side and a `Bool` on the machine side, joined by `BitVec.ofBool`. -/

/-- **Data agreement.** The dialect's carry-add word is the `x86_ADC` data
    output. -/
theorem addCarryWord_adc (v1 v2 : BitVec 64) (c : Bool) :
    addCarryWord v1 v2 (BitVec.ofBool c) = (x86_ADC v1 v2 c).word := by
  apply BitVec.eq_of_toNat_eq
  cases c <;>
    simp [addCarryWord, x86_ADC, rflags_of_aluop, add_carry, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.mod_mod_of_dvd, Nat.add_mod]

/-- **Carry agreement.** The dialect's carry-out bit is the `x86_ADC` carry
    flag. -/
theorem carryOutBit_adc (v1 v2 : BitVec 64) (c : Bool) :
    carryOutBit v1 v2 (BitVec.ofBool c)
      = BitVec.ofBool ((x86_ADC v1 v2 c).cf.getD false) := by
  have key : ∀ n : Nat, (if n ≥ 2 ^ 64 then (1 : BitVec 1) else 0)
      = BitVec.ofBool (decide (n % 2 ^ 64 ≠ n)) := by
    intro n
    have hmod : n % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
    by_cases h : n ≥ 2 ^ 64
    · have hne : n % 2 ^ 64 ≠ n := by omega
      simp [h, hne, BitVec.ofBool]
    · have he : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
      simp [h, he, BitVec.ofBool]
  cases c <;>
    simp only [carryOutBit, x86_ADC, rflags_of_aluop, add_carry, wunsigned,
      Option.getD_some, BitVec.toNat_ofNat, BitVec.toNat_ofBool,
      Bool.toNat_true, Bool.toNat_false] <;>
    exact key _

/-! ## 2. The per-step machine lowering -/

/-- The machine block of one carry-chain step: `mov dst, ra ; adc dst, rb`. The
    carry-in is read from `CF` and the carry-out is written back to `CF`, so a
    chain is the concatenation of these blocks with no instruction between them. -/
def lowerAdc (ra rb dst : String) : List (JInstr 64) :=
  [ .mov dst (.reg ra)
  , .adc dst (.reg rb) ]

/-- The priming `mov` leaves the flag map alone, so the `adc` that follows reads
    the carry-in the step was entered with. -/
theorem mov_flags (dst ra : String) (s : JState 64) :
    (evalInstr s (.mov dst (.reg ra))).flags = s.flags := rfl

/-- **Per-step data word.** Reading `dst` after the lowered step yields
    `addCarryWord (s.get ra) (s.get rb) cin` with `cin` the entry `CF` — the
    value the dialect's `addCarryLo 64` denotes. Needs `dst ≠ rb` so the priming
    `mov` does not clobber the `b` read. -/
theorem lowerAdc_get_dst (ra rb dst : String) (hne : dst ≠ rb) (s : JState 64) :
    (runBlock s (lowerAdc ra rb dst)).get dst
      = addCarryWord (s.get ra) (s.get rb) (BitVec.ofBool (s.flagB (·.cf))) := by
  have hrb : rb ≠ dst := fun h => hne h.symm
  simp only [lowerAdc, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, JState.flagB, JState.writeB5W,
    ite_true, ite_eq_right hrb]
  exact (addCarryWord_adc _ _ _).symm

/-- **Per-step carry-out.** The `CF` left by the lowered step is the dialect's
    `addCarryHi 64` bit, which the next step reads as its carry-in. -/
theorem lowerAdc_cf (ra rb dst : String) (hne : dst ≠ rb) (s : JState 64) :
    BitVec.ofBool ((runBlock s (lowerAdc ra rb dst)).flagB (·.cf))
      = carryOutBit (s.get ra) (s.get rb) (BitVec.ofBool (s.flagB (·.cf))) := by
  have hrb : rb ≠ dst := fun h => hne h.symm
  simp only [lowerAdc, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, JState.flagB, JState.writeB5W,
    ite_eq_right hrb]
  exact (carryOutBit_adc _ _ _).symm

/-- **Per-step register frame.** The lowered step writes only `dst`; any other
    register falls through unchanged. -/
theorem lowerAdc_get_other (ra rb dst r : String) (hr : r ≠ dst) (s : JState 64) :
    (runBlock s (lowerAdc ra rb dst)).get r = s.get r := by
  simp only [lowerAdc, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MOV, JState.setReg, JState.get, JState.writeB5W, ite_eq_right hr]

/-! ## 3. The two-axis state correspondence

`JStateInterpG` relates the `reg 64` SSA variables to machine registers and says
nothing about flags. `CarryInterp` pairs it with the carry clause, which relates
one distinguished `reg 1` variable to `JState.flags.cf`. -/

/-- **The carry-chain state correspondence.** The register axis is
    `JStateInterpG ρ V s`; the carry axis says the machine carry flag holds the
    value of the live carry variable `c`. -/
def CarryInterp {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ)
    (c : Ctxt.Var Γ (.reg 1)) (V : Ctxt.Valuation Γ) (s : JState 64) : Prop :=
  JStateInterpG ρ V s ∧ BitVec.ofBool (s.flagB (·.cf)) = c.lookup V

/-- Shift a register map under a `reg 1` binder: the new slot is a carry bit, not
    a `reg 64` variable, so every `reg 64` variable of the grown context is an old
    one. The `reg 1` analogue of `RegMapG.shiftArr`. -/
def RegMapG.shiftBit {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ) :
    RegMapG (.reg 1 :: Γ) :=
  fun w =>
    match w with
    | .there w0 => ρ w0

/-- The fresh invariant is preserved across a `reg 1` binder: the carry slot takes
    no register, so the map only shifts and the fresh stream is untouched. -/
theorem FreshFor_shiftBit {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ)
    (g : Nat → String) (hfresh : FreshFor ρ g) :
    FreshFor (RegMapG.shiftBit ρ) g := by
  obtain ⟨hinj, hdisj⟩ := hfresh
  refine ⟨hinj, ?_⟩
  intro i v
  match v with
  | .there w0 => exact hdisj i w0

/-! ## 4. The carry-chain block and its `Com` image -/

/-- The `addCarryLo 64` expression on two `reg 64` operands and a `reg 1`
    carry-in. -/
def carryLoExpr {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
    (c : Ctxt.Var Γ (.reg 1)) : Expr jasminDialect Γ (.reg 64) :=
  .mk (.addCarryLo 64) rfl (.cons a (.cons b (.cons c .nil)))

/-- The `addCarryHi 64` expression on two `reg 64` operands and a `reg 1`
    carry-in. -/
def carryHiExpr {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
    (c : Ctxt.Var Γ (.reg 1)) : Expr jasminDialect Γ (.reg 1) :=
  .mk (.addCarryHi 64) rfl (.cons a (.cons b (.cons c .nil)))

/-- `carryLoExpr` denotes to `addCarryWord` of the three looked-up operands. -/
theorem carryLoExpr_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
    (c : Ctxt.Var Γ (.reg 1)) (V : Ctxt.Valuation Γ) :
    (carryLoExpr a b c).denote V
      = addCarryWord (a.lookup V) (b.lookup V) (c.lookup V) := rfl

/-- `carryHiExpr` denotes to `carryOutBit` of the three looked-up operands. -/
theorem carryHiExpr_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
    (c : Ctxt.Var Γ (.reg 1)) (V : Ctxt.Valuation Γ) :
    (carryHiExpr a b c).denote V
      = carryOutBit (a.lookup V) (b.lookup V) (c.lookup V) := rfl

/-- **A carry chain over the context `Γ` with live carry variable `c`.** A `step`
    reads two `reg 64` operands and the live carry, binds the data word and the
    carry-out, and continues with the bound carry-out as its live carry. The
    chain ends by returning a `reg 64` variable. -/
inductive CarryBlock : (Γ : Ctxt jasminDialect) → Ctxt.Var Γ (.reg 1) → Type where
  /-- Return one `reg 64` variable — the chain's output. -/
  | ret {Γ : Ctxt jasminDialect} {c : Ctxt.Var Γ (.reg 1)}
      (v : Ctxt.Var Γ (.reg 64)) : CarryBlock Γ c
  /-- One carry step `d := a + b + c ; c' := carry-out`, binding both, then
      continue with `c'` as the live carry. -/
  | step {Γ : Ctxt jasminDialect} {c : Ctxt.Var Γ (.reg 1)}
      (a b : Ctxt.Var Γ (.reg 64))
      (rest : CarryBlock (.reg 1 :: .reg 64 :: Γ) .here) : CarryBlock Γ c

/-- **Compile a `CarryBlock` to a `Com jasminDialect`.** A `step` becomes the two
    nested binders `addCarryLo` then `addCarryHi`, over the same three operands;
    `ret` is `Com.ret`. -/
def CarryBlock.toCom : {Γ : Ctxt jasminDialect} → {c : Ctxt.Var Γ (.reg 1)} →
    CarryBlock Γ c → Com jasminDialect Γ (.reg 64)
  | _, _, .ret v => .ret v
  | _, c, .step a b rest =>
      .var (carryLoExpr a b c)
        (.var (carryHiExpr (.there a) (.there b) (.there c)) rest.toCom)

/-- **The carry-chain machine lowering.** Each step consumes one fresh register
    for its data word (`g 0`) and leaves its carry-out in `CF`; the `ret` emits
    nothing. -/
def lowerCarryBlock : {Γ : Ctxt jasminDialect} → {c : Ctxt.Var Γ (.reg 1)} →
    CarryBlock Γ c → RegMapG Γ → (Nat → String) → List (JInstr 64)
  | _, _, .ret _, _, _ => []
  | _, _, .step a b rest, ρ, g =>
      lowerAdc (ρ a) (ρ b) (g 0)
        ++ lowerCarryBlock rest (RegMapG.shiftBit (ρ.extend (g 0)))
             (fun k => g (k + 1))

/-- The chain's output register: the register of the returned variable under the
    accumulated register map. -/
def outRegC : {Γ : Ctxt jasminDialect} → {c : Ctxt.Var Γ (.reg 1)} →
    CarryBlock Γ c → RegMapG Γ → (Nat → String) → String
  | _, _, .ret v, ρ, _ => ρ v
  | _, _, .step _ _ rest, ρ, g =>
      outRegC rest (RegMapG.shiftBit (ρ.extend (g 0))) (fun k => g (k + 1))

/-! ## 5. The tie -/

/-- **The block tie for a carry chain.** For every `CarryBlock`, under the
    two-axis correspondence `CarryInterp ρ c V s` and a fresh allocation
    `FreshFor ρ g`, reading the chain's output register after `runBlock` of the
    whole lowered chain equals the chain's `Com jasminDialect` denotation on `V`.
    Structural induction: each step re-establishes the register axis from
    `lowerAdc_get_dst` and `lowerAdc_get_other`, and the carry axis from
    `lowerAdc_cf`, at the context grown by the two binders. -/
theorem lowerCarryBlock_tie : {Γ : Ctxt jasminDialect} →
    {c : Ctxt.Var Γ (.reg 1)} → (block : CarryBlock Γ c) → (ρ : RegMapG Γ) →
    (g : Nat → String) → (s : JState 64) → (V : Ctxt.Valuation Γ) →
    CarryInterp ρ c V s → FreshFor ρ g →
    (runBlock s (lowerCarryBlock block ρ g)).get (outRegC block ρ g)
      = block.toCom.denote V
  | _, _, .ret v, ρ, g, s, V, hinterp, _ => by
      simp only [lowerCarryBlock, outRegC, runBlock_nil, CarryBlock.toCom,
        Com.denote]
      exact hinterp.1 v
  | _, c, .step a b rest, ρ, g, s, V, hinterp, hfresh => by
      obtain ⟨hreg, hcf⟩ := hinterp
      have hdisj := hfresh.2 0
      have hne : g 0 ≠ ρ b := hdisj b
      have hinterp' : CarryInterp (RegMapG.shiftBit (ρ.extend (g 0)))
          Ctxt.Var.here
          ((V.extend ((carryLoExpr a b c).denote V)).extend
            ((carryHiExpr (.there a) (.there b) (.there c)).denote
              (V.extend ((carryLoExpr a b c).denote V))))
          (runBlock s (lowerAdc (ρ a) (ρ b) (g 0))) := by
        refine ⟨?_, ?_⟩
        · intro w
          match w with
          | .there .here =>
              show (runBlock s (lowerAdc (ρ a) (ρ b) (g 0))).get (g 0)
                  = addCarryWord (a.lookup V) (b.lookup V) (c.lookup V)
              rw [lowerAdc_get_dst (ρ a) (ρ b) (g 0) hne s, hreg a, hreg b, hcf]
          | .there (.there w0) =>
              show (runBlock s (lowerAdc (ρ a) (ρ b) (g 0))).get (ρ w0)
                  = w0.lookup V
              rw [lowerAdc_get_other (ρ a) (ρ b) (g 0) (ρ w0)
                (fun h => (hdisj w0) h.symm) s]
              exact hreg w0
        · show BitVec.ofBool
                ((runBlock s (lowerAdc (ρ a) (ρ b) (g 0))).flagB (·.cf))
              = carryOutBit (a.lookup V) (b.lookup V) (c.lookup V)
          rw [lowerAdc_cf (ρ a) (ρ b) (g 0) hne s, hreg a, hreg b, hcf]
      have hfresh' : FreshFor (RegMapG.shiftBit (ρ.extend (g 0)))
          (fun k => g (k + 1)) :=
        FreshFor_shiftBit _ _ (FreshFor_extend ρ g hfresh)
      have key := lowerCarryBlock_tie rest (RegMapG.shiftBit (ρ.extend (g 0)))
        (fun k => g (k + 1)) (runBlock s (lowerAdc (ρ a) (ρ b) (g 0)))
        ((V.extend ((carryLoExpr a b c).denote V)).extend
          ((carryHiExpr (.there a) (.there b) (.there c)).denote
            (V.extend ((carryLoExpr a b c).denote V))))
        hinterp' hfresh'
      simpa only [lowerCarryBlock, outRegC, CarryBlock.toCom, Com.denote,
        runBlock_append] using key

/-! ## 6. A two-limb witness with a propagating carry

The entry context holds the two limb pairs and the entry carry. The low limb adds
`2 ^ 64 - 1` and `1`, which wraps, so the carry-out is `1` and the high limb's
result is `5 + 7 + 1 = 13` rather than `12`. -/

/-- The witness context: the entry carry and the four limb operands. -/
abbrev Γw : Ctxt jasminDialect :=
  [.reg 1, .reg 64, .reg 64, .reg 64, .reg 64]

/-- The entry carry variable. -/
abbrev cw : Ctxt.Var Γw (.reg 1) := .here

/-- The low limb's first operand. -/
abbrev a0w : Ctxt.Var Γw (.reg 64) := .there .here

/-- The low limb's second operand. -/
abbrev b0w : Ctxt.Var Γw (.reg 64) := .there (.there .here)

/-- The high limb's first operand. -/
abbrev a1w : Ctxt.Var Γw (.reg 64) := .there (.there (.there .here))

/-- The high limb's second operand. -/
abbrev b1w : Ctxt.Var Γw (.reg 64) := .there (.there (.there (.there .here)))

/-- The two-limb carry chain: add the low limbs, then the high limbs with the
    low limb's carry-out, and return the high limb's data word. -/
def twoLimbBlock : CarryBlock Γw cw :=
  .step a0w b0w
    (.step (.there (.there a1w)) (.there (.there b1w))
      (.ret (.there .here)))

/-- The chain denotes to the high limb's `addCarryWord` taken at the low limb's
    `carryOutBit`. -/
theorem twoLimbBlock_denote (V : Ctxt.Valuation Γw) :
    twoLimbBlock.toCom.denote V
      = addCarryWord (a1w.lookup V) (b1w.lookup V)
          (carryOutBit (a0w.lookup V) (b0w.lookup V) (cw.lookup V)) := rfl

/-- **The tie on the two-limb chain.** The machine run of the lowered chain reads
    exactly the high limb's data word at the low limb's carry-out. -/
theorem twoLimbBlock_tie (ρ : RegMapG Γw) (g : Nat → String) (s : JState 64)
    (V : Ctxt.Valuation Γw) (hinterp : CarryInterp ρ cw V s)
    (hfresh : FreshFor ρ g) :
    (runBlock s (lowerCarryBlock twoLimbBlock ρ g)).get
        (outRegC twoLimbBlock ρ g)
      = addCarryWord (a1w.lookup V) (b1w.lookup V)
          (carryOutBit (a0w.lookup V) (b0w.lookup V) (cw.lookup V)) := by
  rw [lowerCarryBlock_tie twoLimbBlock ρ g s V hinterp hfresh,
    twoLimbBlock_denote]

/-- The witness valuation: entry carry `0`, low limbs `2 ^ 64 - 1` and `1`, high
    limbs `5` and `7`. -/
def wVal : Ctxt.Valuation Γw :=
  .cons (0 : BitVec 1)
    (.cons (BitVec.ofNat 64 (2 ^ 64 - 1))
      (.cons (1 : BitVec 64)
        (.cons (5 : BitVec 64) (.cons (7 : BitVec 64) .nil))))

/-- The low limb overflows, so the carry the high limb reads is `1`. -/
theorem twoLimb_carry_out_one :
    carryOutBit (a0w.lookup wVal) (b0w.lookup wVal) (cw.lookup wVal) = 1 := by
  decide

/-- The chain's denotation on the witness valuation is `5 + 7 + 1`. Without the
    propagated carry it would be `12`. -/
theorem twoLimbBlock_denote_wVal :
    twoLimbBlock.toCom.denote wVal = (13 : BitVec 64) := rfl

/-- The witness machine state: the four limb operands in named registers and a
    cleared carry flag. -/
def wState : JState 64 :=
  { regs := fun r =>
      if r = "a0" then BitVec.ofNat 64 (2 ^ 64 - 1) else
      if r = "b0" then 1 else
      if r = "a1" then 5 else
      if r = "b1" then 7 else 0
    flags := { cf := some false } }

/-- The witness register map. -/
def wRho : RegMapG Γw
  | .there .here => "a0"
  | .there (.there .here) => "b0"
  | .there (.there (.there .here)) => "a1"
  | .there (.there (.there (.there .here))) => "b1"

/-- The witness fresh-register stream. -/
def wG : Nat → String
  | 0 => "d0"
  | _ => "d1"

/-- **The witness machine run.** Executing the lowered two-limb chain on the
    witness state and reading its output register gives `13`: the low limb's
    `adc` wraps and sets `CF`, and the high limb's `adc` reads it. -/
theorem twoLimbRun :
    (runBlock wState (lowerCarryBlock twoLimbBlock wRho wG)).get
        (outRegC twoLimbBlock wRho wG) = (13 : BitVec 64) := by
  decide

end CatCrypt.Crypto.SecureCompilation.Ascent.CarryChain
