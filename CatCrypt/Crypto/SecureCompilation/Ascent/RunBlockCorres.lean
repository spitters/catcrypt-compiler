/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# The ascent refinement calculus over `runBlock` — the flag-carrying `CorresJ`

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`);
see `Corres.lean`._


The ascent `Corres` of `Ascent/Corres.lean` is a forward simulation over the
scalar denotation `semScalar : LowCT → SEnvScalar → Option SEnvScalar`. That
denotation is the wrong shape for the EC field-emit / byte-backend kernels: the
concrete field add/sub bricks (`jacAddBlock` / `copyBankBlock` and their limb
loops) run over `runBlock : JState 64 → List (JInstr 64) → JState 64`, the total
fold of `evalInstr`, and — critically — their correctness is *about the carry
flag*: a subtract-with-borrow limb writes `CF`, the next limb reads it, and the
final conditional subtract masks on `0 − CF`. `SEnvScalar` has no flag component,
so the scalar `Corres` cannot even *state* a borrow-chain obligation. A three-batch
EC pilot found the whole EC vertical outside what the scalar `Corres` can express,
for exactly this reason (wrong state type, no carry flag).

This module supplies the `runBlock`-level dual, `CorresJ`, whose **state relation
`SR : JState 64 → AState → Prop` sees the full machine state — registers, memory,
and the flags** — so a carry-carrying relation is expressible. It proves the
structural core (`corresJ_nil`, `corresJ_append`, `corresJ_weaken`, and the
`corresJ_single` bridge) over `runBlock`'s left-fold-over-append, plus **one
flag leaf**: a subtract-with-borrow step (`corresJ_sbb`) whose `SR`
tracks `CF` against a clean integer-borrow specification. The leaf discharges the
non-trivial content the pilot flagged as inexpressible — the borrow-out bit equals
"the true signed difference underflowed" — and the two-limb example
(`corresJ_sbb_chain`) threads that `CF` from one limb to the next through
`corresJ_append`.

Relationship to `X86Backend/RunBlockLsemAgree.lean`: that module bridges
`runBlock` to the *machine wire* `lsemStraightMem`, and its flag phase
(`JLstateCorrF`, `adcx_case`) threads `CF`/`OF` for the `adcx`/`adox` ADX opcodes
through a designated-register correspondence. `CorresJ` is the complementary
*abstraction* leg: it relates `runBlock` upward to a clean Lean `AState` (a spec),
not sideways to another machine, and its `SR` carries `CF` in the *abstract* state.
The two share the `JState`/`runBlock` substrate; neither depends on the other.

The scalar-side value machinery (the ParamTransfer `wEnc : BitVec 64 ≅ ZMod 2^64`
word squares in `Ascent/Corres.lean`) plugs into an `SR` here unchanged; this file
keeps its dependencies to `JasminModel` and states the flag leaf with the concrete
`BitVec`/`Int` borrow arithmetic to stay self-contained and non-vacuous.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## `runBlock` distributes over append (left fold)

Reproved locally (the `Optimizer` copy lives behind a heavier import) so the
structural core needs only `JasminModel`. -/

/-- `runBlock` is the left fold: running `xs ++ ys` runs `xs`, then `ys` from the
    resulting state. The `List.foldl_append` analogue that the sequencing lemma
    `corresJ_append` rests on. -/
theorem runBlock_append {w : Nat} (s : JState w) (xs ys : List (JInstr w)) :
    runBlock s (xs ++ ys) = runBlock (runBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBlock_cons]; exact ih (evalInstr s i)

/-! ## The correspondence relation over `runBlock` -/

/-- `CorresJ SR P fa c`: from a concrete `JState 64` related by `SR` to an abstract
    state satisfying precondition `P`, running the straight-line block `c` under the
    **total** machine fold `runBlock` lands in a `JState` related to the abstract
    result `fa a`. A forward simulation generic in the state relation `SR` and the
    abstract state `AState`.

    Unlike the scalar `Ascent.Corres` — which is over `semScalar : LowCT →
    SEnvScalar → Option SEnvScalar` and whose `SEnvScalar` has no flag field —
    `SR` here ranges over the full `JState 64` (registers, memory, **and the five
    condition flags**), so a carry-tracking relation is expressible. `runBlock` is
    total, so no `Option`/failure arm is needed: the machine never gets stuck on the
    emitted subset. -/
def CorresJ {AState : Type} (SR : JState 64 → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : List (JInstr 64)) : Prop :=
  ∀ st a, SR st a → P a → SR (runBlock st c) (fa a)

variable {AState : Type} (SR : JState 64 → AState → Prop)

/-- The empty block: `runBlock st [] = st`, so it transports any `SR` at the
    identity abstraction. -/
theorem corresJ_nil : CorresJ SR (fun _ => True) id [] := by
  intro st a hSR _; simpa only [runBlock_nil, id_eq] using hSR

/-- **Sequencing** (the `corresJ_bind`), resting on `runBlock_append`. The first
    block must re-establish the second's precondition (`hpre`). This is the lemma a
    limb-by-limb carry chain is assembled with: each limb's post-state feeds the
    next. -/
theorem corresJ_append {P Q : AState → Prop} {fa ga : AState → AState}
    {c₁ c₂ : List (JInstr 64)}
    (h₁ : CorresJ SR P fa c₁) (h₂ : CorresJ SR Q ga c₂) (hpre : ∀ a, P a → Q (fa a)) :
    CorresJ SR P (fun a => ga (fa a)) (c₁ ++ c₂) := by
  intro st a hSR hP
  have hstep1 := h₁ st a hSR hP
  have hstep2 := h₂ (runBlock st c₁) (fa a) hstep1 (hpre a hP)
  rw [runBlock_append]; exact hstep2

/-- Strengthen the precondition (contravariant in `P`). -/
theorem corresJ_weaken {P P' : AState → Prop} {fa : AState → AState}
    {c : List (JInstr 64)} (h : CorresJ SR P fa c) (himp : ∀ a, P' a → P a) :
    CorresJ SR P' fa c := by
  intro st a hSR hP'; exact h st a hSR (himp a hP')

/-! ## The carry-carrying abstract state and its subtract-with-borrow transition

The flag leaf. `ACarry` is a clean abstract machine: a register valuation plus the
**carry bit** — the component `SEnvScalar` lacks and the whole point of moving to a
`JState`-level `SR`. `SRcarry` ties it to a `JState` on all three relevant axes
(registers, and the concrete carry flag `CF`). `sbbStep` is the *specification* of
one subtract-with-borrow limb, with the borrow-out stated as the clean integer
predicate "the true signed difference `x − y − b` underflowed". -/

/-- The abstract carry-machine state: a register valuation plus the carry bit. The
    carry bit is the field the scalar `SEnvScalar` has no room for. -/
structure ACarry where
  /-- Abstract register valuation. -/
  regs : String → BitVec 64
  /-- Abstract carry flag. -/
  cf : Bool

/-- `SRcarry`: the `JState`↔`ACarry` relation. Registers agree pointwise, and the
    concrete condition flag `CF` (read as a `Bool` via `JState.flagB`) equals the
    abstract carry bit. **This is the relation the scalar `Corres` could not state**
    — it constrains a flag. -/
def SRcarry (st : JState 64) (a : ACarry) : Prop :=
  (∀ r, st.regs r = a.regs r) ∧ st.flagB (·.cf) = a.cf

/-- The state relation `SRcarry` is non-empty. -/
theorem srcarry_satisfiable : ∃ st a, SRcarry st a := by
  refine ⟨{ regs := fun _ => 0, flags := { cf := some false, of := none } },
    { regs := fun _ => 0, cf := false }, ?_⟩
  exact ⟨fun _ => rfl, rfl⟩

/-- The abstract subtract-with-borrow limb `dst := dst − src − CF`, with the
    borrow-out written to the carry bit. The data word is the machine two's-complement
    `sub_borrow`; the carry-out is the **clean integer-underflow predicate**
    `x − y − b < 0` over `ℤ`. Proving `runBlock` realizes *this* carry — rather than
    restating `x86_SBB`'s internal `CF` expression — is the leaf's non-vacuous content
    (`corresJ_sbb`). -/
def sbbStep (dst src : String) (a : ACarry) : ACarry :=
  { regs := fun r => if r = dst then
      sub_borrow (a.regs dst) (a.regs src) (if a.cf then 1 else 0) else a.regs r
    cf := decide (((a.regs dst).toNat : Int) - (a.regs src).toNat
      - ((if a.cf then 1 else 0 : Nat) : Int) < 0) }

/-- **The borrow-out characterization** (the arithmetic the pilot named as
    inexpressible): `x86_SBB`'s internal `CF` — "the unsigned result word differs
    from the true integer difference" — coincides with the clean integer-underflow
    predicate "`x − y − b` is negative", at width 64 for a borrow-in `b ≤ 1`. Both
    fire exactly when the subtraction wrapped. -/
theorem sbb_borrow_eq (x y : BitVec 64) (b : Nat) (hb : b ≤ 1) :
    decide (((sub_borrow x y b).toNat : Int) ≠ (x.toNat : Int) - (y.toNat + b))
      = decide (((x.toNat : Int) - y.toNat - (b : Int) < 0)) := by
  rw [decide_eq_decide]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hy : y.toNat < 2 ^ 64 := y.isLt
  -- `BitVec.toNat_ofInt` gives the residue `D % ↑(2^64)`; peel `Int.toNat` off the
  -- non-negative residue, then `omega` decides the wrap ⇔ underflow equivalence.
  have hval : ((sub_borrow x y b).toNat : Int)
      = ((x.toNat : Int) - y.toNat - b) % ((2 ^ 64 : Nat) : Int) := by
    rw [sub_borrow, BitVec.toNat_ofInt, Int.toNat_of_nonneg]
    exact Int.emod_nonneg _ (by decide)
  rw [hval]
  omega

/-- **The subtract-with-borrow flag leaf.** Running the single instruction
    `sbb dst src` under `runBlock` refines the abstract `sbbStep` transition through
    the carry-tracking relation `SRcarry`: the destination register gets the
    two's-complement borrow difference, and the concrete
    `CF` after the step equals the abstract borrow-out bit. Discharges the obligation
    the scalar `Corres` could not even phrase. -/
theorem corresJ_sbb (dst src : String) :
    CorresJ SRcarry (fun _ => True) (sbbStep dst src) [.sbb dst (.reg src)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf⟩ := hSR
  -- `runBlock [sbb …] = evalInstr st (sbb …) = st.writeB5W dst (x86_SBB …)`; `hreg`
  -- rewrites every `st.regs r` to `a.regs r`, `hcf` the carry-in flag to `a.cf`.
  refine ⟨?_, ?_⟩
  · -- register agreement
    intro r
    by_cases hr : r = dst
    · subst hr
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_SBB, JState.writeB5W,
        sbbStep, JState.get, JOperand.eval, hcf, hreg]
    · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_SBB, JState.writeB5W,
        sbbStep, JState.get, JOperand.eval, hcf, hreg, if_neg hr]
  · -- carry-flag agreement
    -- bridge the CONCRETE carry-in `st.flags.cf` to the abstract `a.cf` (the simp
    -- below unfolds `flagB` in the goal, so `hcf` must be pre-unfolded to fire).
    have hcf' : Option.getD st.flags.cf false = a.cf := by simpa [JState.flagB] using hcf
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_SBB, JState.flagB,
      JState.writeB5W_flags, Option.getD_some, sbbStep, wunsigned, JState.get,
      JOperand.eval, hcf', hreg]
    exact sbb_borrow_eq (a.regs dst) (a.regs src) (if a.cf then 1 else 0)
      (by split <;> omega)

/-! ## Non-vacuity: a two-limb borrow chain

The point of a *flag*-carrying `SR`: the carry threads between limbs. Two
subtract-with-borrow steps compose through `corresJ_append` — the `CF` written by
limb 0 is exactly the `CF` limb 1 reads — with **no side condition on the
registers** (the abstract state carries the flag, so the chain is unconditional).
This is the borrow-chain shape the EC field-sub kernels run and the scalar `Corres`
could not reach. -/

/-- **A two-limb borrow chain bridges.** `[sbb d0 s0; sbb d1 s1]` refines the
    composed abstract transition `sbbStep d1 s1 ∘ sbbStep d0 s0`: the concrete `CF`
    produced by the first limb feeds the second, matched all the way by `SRcarry`.
    Assembled from `corresJ_sbb` twice via `corresJ_append`. -/
theorem corresJ_sbb_chain (d0 s0 d1 s1 : String) :
    CorresJ SRcarry (fun _ => True) (fun a => sbbStep d1 s1 (sbbStep d0 s0 a))
      [.sbb d0 (.reg s0), .sbb d1 (.reg s1)] := by
  have h := corresJ_append SRcarry (corresJ_sbb d0 s0) (corresJ_sbb d1 s1)
    (fun _ _ => trivial)
  simpa using h

/-! ## The add-with-carry flag leaf (the ADC dual of `corresJ_sbb`)

`adcStep` is the specification of one add-with-carry limb `dst := dst + src + CF`,
with the carry-out stated as the clean unsigned-overflow predicate "the true sum
`x + y + b` reached `2^64`". `corresJ_adc` proves `runBlock` realizes *this* carry
— the ADC mirror of the borrow leaf, the other half of a limb-by-limb bignum
add/sub. -/

/-- The abstract add-with-carry limb `dst := dst + src + CF`, with the carry-out
    written to the carry bit. The data word is the machine two's-complement
    `add_carry`; the carry-out is the **clean unsigned-overflow predicate**
    `2^64 ≤ x + y + b` over `ℕ`. Proving `runBlock` realizes *this* carry — rather
    than restating `x86_ADC`'s internal `CF` expression — is the leaf's non-vacuous
    content (`corresJ_adc`). -/
def adcStep (dst src : String) (a : ACarry) : ACarry :=
  { regs := fun r => if r = dst then
      add_carry (a.regs dst) (a.regs src) (if a.cf then 1 else 0) else a.regs r
    cf := decide (2 ^ 64 ≤ (a.regs dst).toNat + (a.regs src).toNat
      + (if a.cf then 1 else 0)) }

/-- **The carry-out characterization** (the ADC mirror of `sbb_borrow_eq`):
    `x86_ADC`'s internal `CF` — "the unsigned result word differs from the true
    integer sum" — coincides with the clean unsigned-overflow predicate
    "`x + y + b` reached `2^64`". Both fire exactly when the addition wrapped. -/
theorem add_carry_eq (x y : BitVec 64) (b : Nat) :
    decide ((add_carry x y b).toNat ≠ x.toNat + y.toNat + b)
      = decide (2 ^ 64 ≤ x.toNat + y.toNat + b) := by
  rw [decide_eq_decide]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hy : y.toNat < 2 ^ 64 := y.isLt
  -- `BitVec.toNat_ofNat` gives the residue `(x + y + b) % 2^64`; `omega` then
  -- decides the wrap ⇔ overflow equivalence.
  have hval : (add_carry x y b).toNat = (x.toNat + y.toNat + b) % 2 ^ 64 := by
    rw [add_carry, BitVec.toNat_ofNat]
  rw [hval]
  omega

/-- **The add-with-carry flag leaf.** Running the single instruction
    `adc dst src` under `runBlock` refines the abstract `adcStep` transition through
    the carry-tracking relation `SRcarry`: the destination register gets the
    two's-complement carry sum, and the concrete `CF` after the step equals the
    abstract carry-out bit. The ADC dual of `corresJ_sbb`, proved by the same
    register-agreement + carry-flag-agreement split with a pre-unfolded `flagB`
    hypothesis (`hcf'`). -/
theorem corresJ_adc (dst src : String) :
    CorresJ SRcarry (fun _ => True) (adcStep dst src) [.adc dst (.reg src)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf⟩ := hSR
  refine ⟨?_, ?_⟩
  · -- register agreement
    intro r
    by_cases hr : r = dst
    · subst hr
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADC, rflags_of_aluop,
        add_carry, JState.writeB5W, adcStep, JState.get, JOperand.eval, hcf, hreg]
    · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADC, rflags_of_aluop,
        add_carry, JState.writeB5W, adcStep, JState.get, JOperand.eval, hcf, hreg,
        if_neg hr]
  · -- carry-flag agreement
    have hcf' : Option.getD st.flags.cf false = a.cf := by simpa [JState.flagB] using hcf
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADC, rflags_of_aluop,
      JState.flagB, JState.writeB5W_flags, Option.getD_some, adcStep, wunsigned,
      JState.get, JOperand.eval, hcf', hreg]
    exact add_carry_eq (a.regs dst) (a.regs src) (if a.cf then 1 else 0)

/-! ## The multi-limb value relation `SRcarryLimbs`

Generalizing `SRcarry` from a single carry bit to a full **base-`2^64` limb
window**: a designated list of registers holds the little-endian limbs of one
big-integer value, and `limbVal` recomposes them. This is the minimum a
multi-limb `feAdd`/`feSub` capstone consumes — it lets a chain of `corresJ_sbb` /
`corresJ_adc` leaves speak about the recomposed multi-precision value, not just
the per-limb words. -/

/-- Little-endian base-`2^64` recomposition of a limb list: limb 0 is least
    significant. The `MachineLimbField.limbVal` shape, stated locally over
    `List (BitVec 64)` to keep the dependency at `JasminModel`. -/
def limbVal : List (BitVec 64) → Nat
  | [] => 0
  | x :: xs => x.toNat + 2 ^ 64 * limbVal xs

/-- Read the limb registers named by `names` out of a `JState`, in order. -/
def limbRegs (st : JState 64) (names : List String) : List (BitVec 64) :=
  names.map (fun r => st.regs r)

/-- The multi-limb carry-machine state: a register valuation, the carry bit, and
    the recomposed multi-precision `val` of a designated limb window. -/
structure ACarryLimbs where
  /-- Abstract register valuation. -/
  regs : String → BitVec 64
  /-- Abstract carry flag. -/
  cf : Bool
  /-- The abstract multi-limb value (base-`2^64` recomposition of the limb window). -/
  val : Nat

/-- `SRcarryLimbs names`: the `JState`↔`ACarryLimbs` relation over the limb window
    `names`. Registers agree pointwise, `CF` matches, and the concrete limb
    registers recompose (via `limbVal`) to the abstract multi-precision value. -/
def SRcarryLimbs (names : List String) (st : JState 64) (a : ACarryLimbs) : Prop :=
  (∀ r, st.regs r = a.regs r) ∧ st.flagB (·.cf) = a.cf ∧
    limbVal (limbRegs st names) = a.val

/-- **The multi-limb recomposition bridge.** Under `SRcarryLimbs`, the abstract
    limb registers — read through the register valuation `a.regs` — recompose to
    the stored multi-precision value `a.val`. This is the fact a multi-limb
    `feSub`/`feAdd` capstone consumes: the concrete limb window, lifted to the
    abstract state, denotes the big integer. -/
theorem srcarryLimbs_recompose (names : List String) (st : JState 64)
    (a : ACarryLimbs) (h : SRcarryLimbs names st a) :
    limbVal (names.map (fun r => a.regs r)) = a.val := by
  obtain ⟨hreg, _, hval⟩ := h
  have hrs : st.regs = a.regs := funext hreg
  rw [← hval, limbRegs, hrs]

/-! ## A counted-loop `CorresJ` combinator (the `runBlock` analogue of `corres_for`)

A limb loop is a per-index body concatenated `n` times. `corresJ_loop` lifts a
per-limb leaf (each `body i` refining `step i`) to the whole loop, provided the
precondition `P` is a loop invariant. Proved by induction on the count through
`corresJ_append` — the same sequencing that threads the carry from one limb to the
next in `corresJ_sbb_chain`, now for an arbitrary bounded count. -/

/-- The concrete limb loop: `body 0`, `body 1`, …, `body (n-1)` concatenated in
    order (limb 0 first). -/
def loopBlock (body : Nat → List (JInstr 64)) : Nat → List (JInstr 64)
  | 0 => []
  | n + 1 => loopBlock body n ++ body n

/-- The abstract limb loop: `step (n-1) ∘ … ∘ step 1 ∘ step 0` (limb 0 innermost),
    matching `loopBlock`'s execution order under `runBlock`. -/
def loopStep {AState : Type} (step : Nat → AState → AState) : Nat → AState → AState
  | 0 => id
  | n + 1 => fun a => step n (loopStep step n a)

/-- The loop invariant is preserved across the whole abstract loop, provided each
    per-limb step preserves it. -/
theorem loopStep_preserves {AState : Type} {P : AState → Prop}
    {step : Nat → AState → AState} (hinv : ∀ i a, P a → P (step i a)) :
    ∀ n a, P a → P (loopStep step n a) := by
  intro n
  induction n with
  | zero => intro a ha; exact ha
  | succ k ih => intro a ha; exact hinv k _ (ih a ha)

/-- **The counted-loop combinator.** If each per-limb body `body i` refines its
    abstract step `step i` (`hstep`) and the precondition `P` is preserved by every
    step (`hinv`), then the `n`-fold loop `loopBlock body n` refines the composed
    abstract loop `loopStep step n`. The `runBlock` analogue of `corres_for`,
    assembled by induction on `n` through `corresJ_append`. -/
theorem corresJ_loop {P : AState → Prop} {step : Nat → AState → AState}
    {body : Nat → List (JInstr 64)}
    (hstep : ∀ i, CorresJ SR P (step i) (body i))
    (hinv : ∀ i a, P a → P (step i a)) (n : Nat) :
    CorresJ SR P (loopStep step n) (loopBlock body n) := by
  induction n with
  | zero => exact corresJ_weaken SR (corresJ_nil SR) (fun _ _ => trivial)
  | succ k ih =>
    -- `show` pins the loop's unfolded shape so `corresJ_append`'s `fun a ↦ ga (fa a)`
    -- unifies with `loopStep step (k+1)` directly (else higher-order unification
    -- degenerates to `fa := id`).
    show CorresJ SR P (fun a => step k (loopStep step k a)) (loopBlock body k ++ body k)
    exact corresJ_append SR ih (hstep k)
      (fun a ha => loopStep_preserves hinv k a ha)

end CatCrypt.Crypto.SecureCompilation.Ascent
