/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumExec
import CatCrypt.Crypto.Jasmin.BignumExecDiffTest
import CatCrypt.Crypto.Jasmin.Hoare
import CatCrypt.Crypto.Jasmin.S2NBignumSSA
import CatCrypt.Crypto.Jasmin.BignumHoare.Sqr4Algebra
import CatCrypt.Tactics.PreservationCombinator

set_option autoImplicit false

/-!
# Hoare-judgment specialized to `BignumExec`

Wires the parameterized Hoare-triple framework in `Hoare.lean` to the
concrete `BignumExec` operational semantics, giving a working Hoare
logic for the bignum SSA fragment.

## What's here

- `bignumStep`: the `StepRel` for `bignumExec`, lifted through the
  `BignumState ↔ JasminMemState` coercion.
- `bignumStep_isLeftDet`: sequencing decomposes uniquely. Direct
  consequence of `bignumExec_append` (commit `412c2add`).
- `bignumTriple` notation: the specialized Hoare triple
  `{P} body {Q}` over `BignumState` directly (skips the
  `JasminMemState` indirection for ergonomics).
- A worked port theorem **shape** for `bignum_mod_p25519_4`:
  precondition + postcondition stated, decomposition strategy
  documented. Closing it requires per-instruction VC discharge
  which is straightforward but volumetric — the framework here
  reduces it to algebra over `BignumModP25519_4.algoNat_eq_specNat`
  (commit `5aef5df3`).

## What's deferred

- Full instruction-by-instruction VC discharge for the
  `bignum_mod_p25519_4` body. The structural framing
  (`bignumExec_append`-based chunk decomposition, `body_no_lmem_mem_frame`
  for the register-only chunk, `execInstr_storeOp_const` for the 4 stores)
  and the byte-memory bridging (the 4-read chain via
  `load64Mem_store64_self` + `load64Mem_store64_offset_const`) are fully
  Qed-closed in `bodyComputesAlgoNat` below. The remaining `sorry` is just
  the algorithmic kernel (BitVec arithmetic over the 31-instruction register
  computation, ~200 LoC of `simp [execInstr, ...]`).
- mvcgen attachment: the structural rules in `Hoare.lean` are
  the right shape; the tactic plugin is one more file (~1 week per
  estimate in `mvcgen-loom-evaluation.md`).
-/

namespace CatCrypt.Crypto.Jasmin.BignumHoare

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Hoare
open CatCrypt.Crypto.Jasmin.MemoryModel

/-! ## §1. The bignum step relation -/

/-- The step relation for the bignum semantics, expressed directly on
    `BignumState`. Used both standalone (more ergonomic for the bignum
    ports) and as the basis of the `JasminMemState`-flavored relation
    consumed by the generic Hoare framework. -/
def bignumStep (body : List InstrR) (s s' : BignumState) : Prop :=
  bignumExec body s = some s'

/-! ## §2. Sequencing is left-deterministic

Direct corollary of `bignumExec_append`. -/

theorem bignumStep_isLeftDet
    (b1 b2 : List InstrR) (s s' : BignumState)
    (h : bignumStep (b1 ++ b2) s s') :
    ∃ s_mid : BignumState, bignumStep b1 s s_mid ∧ bignumStep b2 s_mid s' := by
  unfold bignumStep at *
  exact bignumExec_append b1 b2 s s' h

/-! ## §3. Direct Hoare triple over `BignumState`

Lighter-weight than going through `JasminMemState`. Keeps the
preconditions simple (just `BignumState → Prop` predicates). -/

/-- `BignumTriple P body Q`: under `bignumExec`, every successful
    execution of `body` from a state satisfying `P` reaches a state
    satisfying `Q`. -/
def BignumTriple
    (P : BignumState → Prop) (body : List InstrR) (Q : BignumState → Prop) : Prop :=
  ∀ s s', P s → bignumStep body s s' → Q s'

/-- Consequence rule. -/
theorem BignumTriple.consequence
    {P P' : BignumState → Prop} {body : List InstrR}
    {Q Q' : BignumState → Prop}
    (h_pre : ∀ s, P' s → P s)
    (h_post : ∀ s, Q s → Q' s)
    (h : BignumTriple P body Q) :
    BignumTriple P' body Q' := by
  intro s s' hP hStep
  exact h_post s' (h s s' (h_pre s hP) hStep)

/-- Sequencing rule. -/
theorem BignumTriple.seq
    {P R Q : BignumState → Prop}
    {body1 body2 : List InstrR}
    (h1 : BignumTriple P body1 R)
    (h2 : BignumTriple R body2 Q) :
    BignumTriple P (body1 ++ body2) Q := by
  intro s s' hP hStep
  obtain ⟨s_mid, hS1, hS2⟩ := bignumStep_isLeftDet body1 body2 s s' hStep
  exact h2 s_mid s' (h1 s s_mid hP hS1) hS2

/-- Conjunction rule. -/
theorem BignumTriple.conj
    {P1 P2 Q1 Q2 : BignumState → Prop}
    {body : List InstrR}
    (h1 : BignumTriple P1 body Q1)
    (h2 : BignumTriple P2 body Q2) :
    BignumTriple (fun s => P1 s ∧ P2 s) body (fun s => Q1 s ∧ Q2 s) := by
  intro s s' hP hStep
  exact ⟨h1 s s' hP.1 hStep, h2 s s' hP.2 hStep⟩

/-! ## §4. Worked port-theorem shape: `bignum_mod_p25519_4`

This section gives the *signature* of the correctness theorem, the
decomposition strategy, and the residual algebraic obligation. The
per-instruction VCs are mechanical and deferred. -/

/-- The 4×64-limb little-endian Nat value of memory at `base`. Read
    8 bytes per limb; `none` if any byte is unallocated. -/
def memNat4 (base : UInt64) (m : Mem) : Option Nat := do
  let l0 ← BignumExec.load64Mem m base
  let l1 ← BignumExec.load64Mem m (base + 8)
  let l2 ← BignumExec.load64Mem m (base + 16)
  let l3 ← BignumExec.load64Mem m (base + 24)
  some (l0.toNat
        + l1.toNat * 2 ^ 64
        + l2.toNat * 2 ^ 128
        + l3.toNat * 2 ^ 192)

/-- Precondition for `bignum_mod_p25519_4`: memory at `base_a` holds a
    4-limb value `< 2p`, all bytes of the input range and the output
    range are allocated, and the input/output ranges are disjoint. -/
def bignumModPre (base_a base_op : UInt64) : BignumState → Prop := fun s =>
  s.regs "ap" = BitVec.ofNat 64 base_a.toNat
  ∧ s.regs "op" = BitVec.ofNat 64 base_op.toNat
  ∧ s.regs "zero" = 0  -- the helper register the body assumes is 0
  ∧ ∃ a_val, memNat4 base_a s.mem = some a_val ∧ a_val < 2 * (2^255 - 19)
  ∧ (∀ k : Fin 32, ∃ b, s.mem.loadByte (base_op + UInt64.ofNat k.val) = some b)

/-- Postcondition: memory at `base_op` holds the canonical reduction
    of the input value mod p. -/
def bignumModPost (base_a base_op : UInt64) : BignumState → Prop := fun s =>
  ∃ a_val, memNat4 base_a s.mem = some a_val ∧
  ∃ r_val, memNat4 base_op s.mem = some r_val ∧
  r_val = a_val % (2^255 - 19)

/-! ## §4'. Concrete-input correctness theorems (Qed, no sorries)

The universal `bignum_mod_p25519_4_correct` over an arbitrary
`BignumState` is a 200–300 LoC simp chain (the per-instruction VC
discharge). Until the mvcgen plugin lands (per Watch List item #4),
that universal proof is volumetric work.

What we *can* close right now without sorries: concrete-input
correctness theorems via `native_decide` on fully-instantiated
`runAndCheck` calls. These are real proofs that the SSA body of
`BignumModP25519_4` computes the algorithmically-correct answer for
specific RFC-relevant inputs.

Format: each theorem says `bignumExec body initial_state = some
final_state` where `final_state.mem at base_op` holds the canonical
reduction of `initial_state.mem at base_a`. Decided by `native_decide`
on the computable interpreter.

This gives concrete L1+L2 evidence (Lean side) for two real test
cases. The C-side differential gate extends to claim L2 for
those same two inputs across the JasminEmit ∘ jasminc compile chain.
-/

open CatCrypt.Crypto.Jasmin.BignumExecDiffTest in
/-- Lean-side correctness on the canonical TC1 input (a = 100, well
    below p). Output op-region holds the same value 100 (a is already
    canonical). Proved by `native_decide` on the concrete state. -/
theorem bignum_mod_p25519_4_correct_tc1 :
    runAndCheck tcModCanonical = true := by
  native_decide

open CatCrypt.Crypto.Jasmin.BignumExecDiffTest in
/-- Lean-side correctness on TC2 (a = p + 5; expected output = 5 after
    canonical reduction). Proved by `native_decide`. -/
theorem bignum_mod_p25519_4_correct_tc2 :
    runAndCheck tcModAboveP = true := by
  native_decide

/-! ## §4''. Universal correctness — structural skeleton

The full universal theorem says: every initial state satisfying the
precondition (input < 2p, output range allocated, input/output ranges
disjoint) leads, after executing the body, to a state whose output
range holds the canonical reduction `a mod p`.

The proof decomposes into:

  Step 1: Algebraic core (Qed): `algoNat_eq_specNat` — given `a < 2p`,
    the algorithmic transformation `if a ≥ p then a - p else a` equals
    `a mod p`. Already proved in `S2NBignumSSA.lean`.

  Step 2: Operational soundness (sketched): the 33-instruction body
    when run on a precondition-satisfying state computes exactly the
    `algoNat` transformation on the input limbs. This is a
    per-instruction VC discharge — mechanical but volumetric (~30 simp
    rewrites of `BignumExec.execInstr` over `Cassgn` / `Copn` shapes),
    parametric in `base_a` and `base_op`. The chain:
      `bignumExec body s = some s'`
      ⟹ `s'.regs "o0..o3" = (algoNat-of-input-as-bitvecs)`
      ⟹ `memNat4 base_op s'.mem = some (algoNat (memNat4 base_a s.mem))`

  Step 3: Frame (sketched): the body only writes to `base_op`-region
    memory. The disjointness hypothesis ensures `memNat4 base_a s'.mem
    = memNat4 base_a s.mem`, by `array64_storeByte_disjoint` over each
    of the 4 store instructions.

The theorem statement and decomposition skeleton are below, with the
two operational lemmas (`bodyComputesAlgoNat`, `bodyPreservesInput`)
captured as named conjectures. Both reduce to symbolic execution of
the body — a few hundred LoC of `simp`-on-`execInstr` discharge that
the mvcgen plugin (Watch List item #4) would automate. The algebraic
content is fully proved via `algoNat_eq_specNat`. -/

/-! ## §4'''. The universal theorem

Below: the universal correctness theorem, with proof reduced to two
named operational lemmas (`bodyComputesAlgoNat` and `bodyPreservesInput`).
The algebraic content (`algoNat_eq_specNat`) is fully proved.

The two operational lemmas are stated separately and connected by
a single `BignumTriple.consequence` step. Both lemmas are
straight-line symbolic execution of the 33-instruction body — see
the chunk decomposition in §5 for how they would be proved by
`BignumTriple.seq` chaining once the per-instruction VC tactic
lands. -/

/-! ### Frame helpers: instructions that don't write memory

The body has 33 instructions; only 4 of them are `Cassgn` of
`Lmem` (the four `store64` calls that write to `base_op`). The other
29 are register-only writes — `Cassgn (Lvar _)` and
`Copn _ _ (Oasm _) _`. We prove a structural lemma that says any
non-`Lmem` instruction preserves `mem`. -/

/-! `writeXBundle` mem-preservation is deduplicated against
    `CatCrypt.Tactics.PreservationCombinator` §4.1 (the per-bundle
    `write*Bundle_preserves_mem` helpers). The six private wrappers below —
    `writeSubBundle_mem`, `writeMulxBundle_mem`, `writeAdxBundle_mem`,
    `writeXorBundle_mem`, `writeDivBundle_mem`, `writeShiftBundle_mem` — are thin
    delegating proxies to the corresponding public lemma. -/

private theorem writeSubBundle_mem
    (s s' : BignumState) (lvs : List LVal) (cf r : BitVec 64)
    (h : BignumExec.writeSubBundle s lvs cf r = some s') :
    s'.mem = s.mem :=
  CatCrypt.Tactics.PreservationCombinator.writeSubBundle_preserves_mem
    s s' lvs cf r h

private theorem writeMulxBundle_mem
    (s s' : BignumState) (lvs : List LVal) (hi lo : BitVec 64)
    (h : BignumExec.writeMulxBundle s lvs hi lo = some s') :
    s'.mem = s.mem :=
  CatCrypt.Tactics.PreservationCombinator.writeMulxBundle_preserves_mem
    s s' lvs hi lo h

private theorem writeAdxBundle_mem
    (s s' : BignumState) (lvs : List LVal) (flag r : BitVec 64)
    (h : BignumExec.writeAdxBundle s lvs flag r = some s') :
    s'.mem = s.mem :=
  CatCrypt.Tactics.PreservationCombinator.writeAdxBundle_preserves_mem
    s s' lvs flag r h

private theorem writeXorBundle_mem
    (s s' : BignumState) (lvs : List LVal) (of cf r : BitVec 64)
    (h : BignumExec.writeXorBundle s lvs of cf r = some s') :
    s'.mem = s.mem :=
  CatCrypt.Tactics.PreservationCombinator.writeXorBundle_preserves_mem
    s s' lvs of cf r h

private theorem writeDivBundle_mem
    (s s' : BignumState) (lvs : List LVal) (q r : BitVec 64)
    (h : BignumExec.writeDivBundle s lvs q r = some s') :
    s'.mem = s.mem :=
  CatCrypt.Tactics.PreservationCombinator.writeDivBundle_preserves_mem
    s s' lvs q r h

private theorem writeShiftBundle_mem
    (s s' : BignumState) (lvs : List LVal) (r : BitVec 64)
    (h : BignumExec.writeShiftBundle s lvs r = some s') :
    s'.mem = s.mem :=
  CatCrypt.Tactics.PreservationCombinator.writeShiftBundle_preserves_mem
    s s' lvs r h

/-- An `execInstr` step preserves `mem` unless the instruction is a
    memory-store `Cassgn (Lmem ws base off) ...`. -/
private theorem execInstr_mem_preserve
    (s s' : BignumState) (i : InstrR)
    (hi : BignumExec.execInstr s i = some s')
    (hno : ∀ ws base off al sty rhs,
            i ≠ .Cassgn (.Lmem ws base off) al sty rhs) :
    s'.mem = s.mem := by
  cases i with
  | Cassgn lv al sty rhs =>
    match lv, hno with
    | .Lvar v, _ =>
      rw [show BignumExec.execInstr s (.Cassgn (.Lvar v) al sty rhs) =
            (BignumExec.evalPExpr s rhs).bind
              (fun w => some (BignumExec.setReg s v.var.vname w)) from rfl] at hi
      rcases h_w : BignumExec.evalPExpr s rhs with _ | w
      · rw [h_w] at hi; simp at hi
      · rw [h_w] at hi; simp at hi; subst hi; rfl
    | .Lmem ws base off, hno =>
      exact absurd rfl (hno ws base off al sty rhs)
    | .Lnone _ _, _ => simp [BignumExec.execInstr] at hi
    | .Laset _ _ _ _, _ => simp [BignumExec.execInstr] at hi
    | .Lasub _ _ _ _ _, _ => simp [BignumExec.execInstr] at hi
  | Copn lvs tag op args =>
    match op with
    | .Oasm o =>
      -- Dispatch on opname + args via split.
      simp only [BignumExec.execInstr] at hi
      split at hi
      · -- SUB_64 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeSubBundle_mem _ _ _ _ _ hi
      · -- SBB_64 case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeSubBundle_mem _ _ _ _ _ hi
      · -- ADD_64 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeSubBundle_mem _ _ _ _ _ hi
      · -- ADC_64 case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeSubBundle_mem _ _ _ _ _ hi
      · -- MULX case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeMulxBundle_mem _ _ _ _ _ hi
      · -- DIV_64 case
        rename_i eh el ed _
        rcases h_a : BignumExec.evalPExpr s eh with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s el with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ed with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeDivBundle_mem _ _ _ _ _ hi
      · -- ADCX case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeAdxBundle_mem _ _ _ _ _ hi
      · -- ADOX case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeAdxBundle_mem _ _ _ _ _ hi
      · -- XOR_64 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeXorBundle_mem _ _ _ _ _ _ hi
      · -- (Shift, additive) SHL_64 case
        rename_i ea ek _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_k : BignumExec.evalPExpr s ek with _ | k
          · rw [h_k] at hi; simp at hi
          · rw [h_k] at hi; simp at hi
            exact writeShiftBundle_mem _ _ _ _ hi
      · -- (Shift, additive) SHR_64 case
        rename_i ea ek _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_k : BignumExec.evalPExpr s ek with _ | k
          · rw [h_k] at hi; simp at hi
          · rw [h_k] at hi; simp at hi
            exact writeShiftBundle_mem _ _ _ _ hi
      · -- (Shift, additive) SHLD_64 case
        rename_i edst esrc ek _
        rcases h_a : BignumExec.evalPExpr s edst with _ | dst
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s esrc with _ | src
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_k : BignumExec.evalPExpr s ek with _ | k
            · rw [h_k] at hi; simp at hi
            · rw [h_k] at hi; simp at hi
              exact writeShiftBundle_mem _ _ _ _ hi
      · -- (Shift, additive) SHRD_64 case
        rename_i edst esrc ek _
        rcases h_a : BignumExec.evalPExpr s edst with _ | dst
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s esrc with _ | src
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_k : BignumExec.evalPExpr s ek with _ | k
            · rw [h_k] at hi; simp at hi
            · rw [h_k] at hi; simp at hi
              exact writeShiftBundle_mem _ _ _ _ hi
      · -- (U32, additive) SUB_32 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeSubBundle_mem _ _ _ _ _ hi
      · -- (U32, additive) ADD_32 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeSubBundle_mem _ _ _ _ _ hi
      · -- (U32, additive) ADC_32 case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeSubBundle_mem _ _ _ _ _ hi
      · -- (U32, additive) SBB_32 case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeSubBundle_mem _ _ _ _ _ hi
      · -- (U32, additive) MULX_32 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeMulxBundle_mem _ _ _ _ _ hi
      · simp at hi
  | Cif _ _ _ => simp [BignumExec.execInstr] at hi
  | Cfor _ _ _ => simp [BignumExec.execInstr] at hi
  | Cwhile _ _ _ => simp [BignumExec.execInstr] at hi
  | Ccall _ _ _ _ => simp [BignumExec.execInstr] at hi

/-- After a memory-store `Cassgn (Lmem .U64 base off) _ _ rhs`, the
    new memory differs from the old only in the 8 bytes
    `[addr, addr + 8)` where `addr` is the resolved store address. -/
private theorem execInstr_storeMem
    (s s' : BignumState) (base : VarI) (off : PExpr)
    (al : AssgnTag) (sty : SType) (rhs : PExpr)
    (hi : BignumExec.execInstr s
            (.Cassgn (.Lmem .U64 base off) al sty rhs) = some s') :
    ∃ addr w, BignumExec.resolveAddr s base off = some addr ∧
              BignumExec.evalPExpr s rhs = some w ∧
              s' = BignumExec.storeMem s addr (UInt64.ofNat w.toNat) := by
  rw [show BignumExec.execInstr s
        (.Cassgn (.Lmem .U64 base off) al sty rhs) =
        (BignumExec.evalPExpr s rhs).bind
          (fun w => (BignumExec.resolveAddr s base off).bind
                      (fun addr => some (BignumExec.storeMem s addr
                                          (UInt64.ofNat w.toNat)))) from rfl]
    at hi
  -- Track ow := evalPExpr s rhs.
  set ow := BignumExec.evalPExpr s rhs with h_w
  set oa := BignumExec.resolveAddr s base off with h_addr
  cases ow_eq : ow with
  | none =>
    rw [ow_eq] at hi; simp at hi
  | some w =>
    cases oa_eq : oa with
    | none => rw [ow_eq, oa_eq] at hi; simp at hi
    | some addr =>
      refine ⟨addr, w, ?_, ?_, ?_⟩
      · rw [← oa_eq]
      · rw [← ow_eq]
      · rw [ow_eq, oa_eq] at hi
        simp only [Option.bind_some] at hi
        exact (Option.some.inj hi).symm

/-- The `store64` helper from S2NBignumSSA's `BignumModP25519_4` namespace
    expands to `Cassgn (Lmem .U64 ...) ...`. The four stores in the body
    use offsets 0, 8, 16, 24 from `op`. -/
private theorem resolveAddr_op_offset
    (s : BignumState) (base_op : UInt64) (k : Int)
    (h_op : s.regs "op" = BitVec.ofNat 64 base_op.toNat) :
    BignumExec.resolveAddr s
        { var := S2NBignumSSA.v "op" } (.Pconst k) =
      some (UInt64.ofNat
              ((BitVec.ofNat 64 base_op.toNat + BitVec.ofInt 64 k).toNat)) := by
  unfold BignumExec.resolveAddr
  simp [S2NBignumSSA.v, h_op]


/-! ### Single-instruction register frame

If the instruction's `lvs` are all `Lvar` with names different from
`x` (or `Lnone`/`Lmem` which don't touch registers at all), then
`regs x` is preserved. -/

/-- Bridge between BignumHoare's ∀-on-membership form and
    PreservationCombinator's filterMap form for the `lvs` no-write
    predicate. -/
private theorem hno_to_filterMap (x : String) (lvs : List LVal)
    (h_no_x : ∀ v, .Lvar v ∈ lvs → v.var.vname ≠ x) :
    x ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none) := by
  intro h_in
  rw [List.mem_filterMap] at h_in
  obtain ⟨lv, h_mem, h_eq⟩ := h_in
  cases lv with
  | Lvar v => simp at h_eq; exact h_no_x v h_mem h_eq
  | _ => simp at h_eq

/-! Reg-preservation `writeXBundle_regs` helpers — thin proxies into the
    public `CatCrypt.Tactics.PreservationCombinator.writeXBundle_preserves`
    lemmas (§1 of that file). The hypothesis-shape conversion is via
    `hno_to_filterMap` above. -/

private theorem writeSubBundle_regs
    (s s' : BignumState) (lvs : List LVal) (cf r : BitVec 64) (x : String)
    (h : BignumExec.writeSubBundle s lvs cf r = some s')
    (h_no_x : ∀ v, .Lvar v ∈ lvs → v.var.vname ≠ x) :
    s'.regs x = s.regs x :=
  CatCrypt.Tactics.PreservationCombinator.writeSubBundle_preserves
    s s' lvs cf r x h (hno_to_filterMap x lvs h_no_x)

private theorem writeMulxBundle_regs
    (s s' : BignumState) (lvs : List LVal) (hi lo : BitVec 64) (x : String)
    (h : BignumExec.writeMulxBundle s lvs hi lo = some s')
    (h_no_x : ∀ v, .Lvar v ∈ lvs → v.var.vname ≠ x) :
    s'.regs x = s.regs x :=
  CatCrypt.Tactics.PreservationCombinator.writeMulxBundle_preserves
    s s' lvs hi lo x h (hno_to_filterMap x lvs h_no_x)

private theorem writeAdxBundle_regs
    (s s' : BignumState) (lvs : List LVal) (flag r : BitVec 64) (x : String)
    (h : BignumExec.writeAdxBundle s lvs flag r = some s')
    (h_no_x : ∀ v, .Lvar v ∈ lvs → v.var.vname ≠ x) :
    s'.regs x = s.regs x :=
  CatCrypt.Tactics.PreservationCombinator.writeAdxBundle_preserves
    s s' lvs flag r x h (hno_to_filterMap x lvs h_no_x)

private theorem writeXorBundle_regs
    (s s' : BignumState) (lvs : List LVal) (of cf r : BitVec 64) (x : String)
    (h : BignumExec.writeXorBundle s lvs of cf r = some s')
    (h_no_x : ∀ v, .Lvar v ∈ lvs → v.var.vname ≠ x) :
    s'.regs x = s.regs x :=
  CatCrypt.Tactics.PreservationCombinator.writeXorBundle_preserves
    s s' lvs of cf r x h (hno_to_filterMap x lvs h_no_x)

private theorem writeDivBundle_regs
    (s s' : BignumState) (lvs : List LVal) (q r : BitVec 64) (x : String)
    (h : BignumExec.writeDivBundle s lvs q r = some s')
    (h_no_x : ∀ v, .Lvar v ∈ lvs → v.var.vname ≠ x) :
    s'.regs x = s.regs x :=
  CatCrypt.Tactics.PreservationCombinator.writeDivBundle_preserves
    s s' lvs q r x h (hno_to_filterMap x lvs h_no_x)

private theorem writeShiftBundle_regs
    (s s' : BignumState) (lvs : List LVal) (r : BitVec 64) (x : String)
    (h : BignumExec.writeShiftBundle s lvs r = some s')
    (h_no_x : ∀ v, .Lvar v ∈ lvs → v.var.vname ≠ x) :
    s'.regs x = s.regs x :=
  CatCrypt.Tactics.PreservationCombinator.writeShiftBundle_preserves
    s s' lvs r x h (hno_to_filterMap x lvs h_no_x)

/-- Decidable predicate on a `List LVal` saying that no element writes
    to register `x`. -/
private def lvsNoWriteB (x : String) : List LVal → Bool
  | [] => true
  | (.Lvar v) :: rest => decide (v.var.vname ≠ x) && lvsNoWriteB x rest
  | _ :: rest => lvsNoWriteB x rest

/-- A `List LVal` predicate: no element writes to `x`. -/
private def lvsNoWrite (x : String) (lvs : List LVal) : Prop :=
  ∀ v, LVal.Lvar v ∈ lvs → v.var.vname ≠ x

private theorem lvsNoWrite_of_B (x : String) (lvs : List LVal) :
    lvsNoWriteB x lvs = true → lvsNoWrite x lvs := by
  intro h
  induction lvs with
  | nil => intro v hv; cases hv
  | cons lv rest ih =>
    intro v hv
    cases lv with
    | Lvar w =>
      simp [lvsNoWriteB] at h
      rw [List.mem_cons] at hv
      cases hv with
      | inl heq => cases heq; exact h.1
      | inr hin => exact ih h.2 v hin
    | Lnone _ _ =>
      simp [lvsNoWriteB] at h
      simp at hv
      exact ih h v hv
    | Lmem _ _ _ =>
      simp [lvsNoWriteB] at h
      simp at hv
      exact ih h v hv
    | Laset _ _ _ _ =>
      simp [lvsNoWriteB] at h
      simp at hv
      exact ih h v hv
    | Lasub _ _ _ _ _ =>
      simp [lvsNoWriteB] at h
      simp at hv
      exact ih h v hv

/-- Decidable predicate on an `InstrR`: it does not write to `x`. -/
def instrNoWriteB (x : String) : InstrR → Bool
  | .Cassgn (.Lvar v) _ _ _ => decide (v.var.vname ≠ x)
  | .Cassgn _ _ _ _ => true
  | .Copn lvs _ _ _ => lvsNoWriteB x lvs
  | _ => true

/-- A predicate on an `InstrR` saying it does not write to register `x`. -/
def instrNoWrite (x : String) : InstrR → Prop
  | .Cassgn (.Lvar v) _ _ _ => v.var.vname ≠ x
  | .Cassgn _ _ _ _ => True
  | .Copn lvs _ _ _ => lvsNoWrite x lvs
  | _ => True

theorem instrNoWrite_of_B (x : String) (i : InstrR) :
    instrNoWriteB x i = true → instrNoWrite x i := by
  intro h
  cases i with
  | Cassgn lv _ _ _ =>
    cases lv with
    | Lvar v =>
      unfold instrNoWriteB at h; unfold instrNoWrite
      simp at h; exact h
    | _ => trivial
  | Copn lvs _ _ _ =>
    unfold instrNoWriteB at h; unfold instrNoWrite
    exact lvsNoWrite_of_B x lvs h
  | _ => trivial

/-- Single-instruction register frame: if the instruction does not
    write to `x`, then `regs x` is preserved. -/
private theorem execInstr_regs_frame
    (s s' : BignumState) (i : InstrR) (x : String)
    (hi : BignumExec.execInstr s i = some s')
    (hno : instrNoWrite x i) :
    s'.regs x = s.regs x := by
  cases i with
  | Cassgn lv al sty rhs =>
    cases lv with
    | Lvar v =>
      rw [show BignumExec.execInstr s (.Cassgn (.Lvar v) al sty rhs) =
            (BignumExec.evalPExpr s rhs).bind
              (fun w => some (BignumExec.setReg s v.var.vname w)) from rfl] at hi
      rcases h_w : BignumExec.evalPExpr s rhs with _ | w
      · rw [h_w] at hi; simp at hi
      · rw [h_w] at hi; simp at hi
        subst hi
        unfold BignumExec.setReg
        unfold instrNoWrite at hno
        show (if x = v.var.vname then w else s.regs x) = s.regs x
        rw [if_neg (Ne.symm hno)]
    | Lmem ws base off =>
      cases ws with
      | U64 =>
        rw [show BignumExec.execInstr s (.Cassgn (.Lmem .U64 base off) al sty rhs) =
              (BignumExec.evalPExpr s rhs).bind
                (fun w => (BignumExec.resolveAddr s base off).bind
                            (fun addr => some (BignumExec.storeMem s addr
                                                 (UInt64.ofNat w.toNat))))
                from rfl] at hi
        rcases h_w : BignumExec.evalPExpr s rhs with _ | w
        · rw [h_w] at hi; simp at hi
        · rw [h_w] at hi; simp at hi
          rcases h_addr : BignumExec.resolveAddr s base off with _ | addr
          · rw [h_addr] at hi; simp at hi
          · rw [h_addr] at hi; simp at hi
            subst hi
            rfl
      | U32 =>
        -- (U32, additive) U32 store touches only memory ⇒ regs preserved.
        rw [show BignumExec.execInstr s (.Cassgn (.Lmem .U32 base off) al sty rhs) =
              (BignumExec.evalPExpr s rhs).bind
                (fun w => (BignumExec.resolveAddr s base off).bind
                            (fun addr => some (BignumExec.storeMem32 s addr
                                                 (UInt64.ofNat w.toNat))))
                from rfl] at hi
        rcases h_w : BignumExec.evalPExpr s rhs with _ | w
        · rw [h_w] at hi; simp at hi
        · rw [h_w] at hi; simp at hi
          rcases h_addr : BignumExec.resolveAddr s base off with _ | addr
          · rw [h_addr] at hi; simp at hi
          · rw [h_addr] at hi; simp at hi
            subst hi
            rfl
      | U8 =>
        -- (U8, additive) U8 byte store touches only memory ⇒ regs preserved.
        rw [show BignumExec.execInstr s (.Cassgn (.Lmem .U8 base off) al sty rhs) =
              (BignumExec.evalPExpr s rhs).bind
                (fun w => (BignumExec.resolveAddr s base off).bind
                            (fun addr => some (BignumExec.storeMem8 s addr
                                                 (UInt8.ofNat (w.toNat % 256)))))
                from rfl] at hi
        rcases h_w : BignumExec.evalPExpr s rhs with _ | w
        · rw [h_w] at hi; simp at hi
        · rw [h_w] at hi; simp at hi
          rcases h_addr : BignumExec.resolveAddr s base off with _ | addr
          · rw [h_addr] at hi; simp at hi
          · rw [h_addr] at hi; simp at hi
            subst hi
            rfl
      | _ => simp [BignumExec.execInstr] at hi
    | Lnone _ _ => simp [BignumExec.execInstr] at hi
    | Laset _ _ _ _ => simp [BignumExec.execInstr] at hi
    | Lasub _ _ _ _ _ => simp [BignumExec.execInstr] at hi
  | Copn lvs tag op args =>
    cases op with
    | Oasm o =>
      simp only [BignumExec.execInstr] at hi
      unfold instrNoWrite lvsNoWrite at hno
      split at hi
      · rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeSubBundle_regs _ _ _ _ _ _ hi hno
      · rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeSubBundle_regs _ _ _ _ _ _ hi hno
      · -- ADD_64 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeSubBundle_regs _ _ _ _ _ _ hi hno
      · -- ADC_64 case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeSubBundle_regs _ _ _ _ _ _ hi hno
      · -- MULX case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeMulxBundle_regs _ _ _ _ _ _ hi hno
      · -- DIV_64 case
        rename_i eh el ed _
        rcases h_a : BignumExec.evalPExpr s eh with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s el with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ed with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeDivBundle_regs _ _ _ _ _ _ hi hno
      · -- ADCX case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeAdxBundle_regs _ _ _ _ _ _ hi hno
      · -- ADOX case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeAdxBundle_regs _ _ _ _ _ _ hi hno
      · -- XOR_64 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeXorBundle_regs _ _ _ _ _ _ _ hi hno
      · -- (Shift, additive) SHL_64 case
        rename_i ea ek _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_k : BignumExec.evalPExpr s ek with _ | k
          · rw [h_k] at hi; simp at hi
          · rw [h_k] at hi; simp at hi
            exact writeShiftBundle_regs _ _ _ _ _ hi hno
      · -- (Shift, additive) SHR_64 case
        rename_i ea ek _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_k : BignumExec.evalPExpr s ek with _ | k
          · rw [h_k] at hi; simp at hi
          · rw [h_k] at hi; simp at hi
            exact writeShiftBundle_regs _ _ _ _ _ hi hno
      · -- (Shift, additive) SHLD_64 case
        rename_i edst esrc ek _
        rcases h_a : BignumExec.evalPExpr s edst with _ | dst
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s esrc with _ | src
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_k : BignumExec.evalPExpr s ek with _ | k
            · rw [h_k] at hi; simp at hi
            · rw [h_k] at hi; simp at hi
              exact writeShiftBundle_regs _ _ _ _ _ hi hno
      · -- (Shift, additive) SHRD_64 case
        rename_i edst esrc ek _
        rcases h_a : BignumExec.evalPExpr s edst with _ | dst
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s esrc with _ | src
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_k : BignumExec.evalPExpr s ek with _ | k
            · rw [h_k] at hi; simp at hi
            · rw [h_k] at hi; simp at hi
              exact writeShiftBundle_regs _ _ _ _ _ hi hno
      · -- (U32, additive) SUB_32 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeSubBundle_regs _ _ _ _ _ _ hi hno
      · -- (U32, additive) ADD_32 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeSubBundle_regs _ _ _ _ _ _ hi hno
      · -- (U32, additive) ADC_32 case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeSubBundle_regs _ _ _ _ _ _ hi hno
      · -- (U32, additive) SBB_32 case
        rename_i ea eb ec _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            rcases h_c : BignumExec.evalPExpr s ec with _ | c
            · rw [h_c] at hi; simp at hi
            · rw [h_c] at hi; simp at hi
              exact writeSubBundle_regs _ _ _ _ _ _ hi hno
      · -- (U32, additive) MULX_32 case
        rename_i ea eb _
        rcases h_a : BignumExec.evalPExpr s ea with _ | a
        · rw [h_a] at hi; simp at hi
        · rw [h_a] at hi; simp at hi
          rcases h_b : BignumExec.evalPExpr s eb with _ | b
          · rw [h_b] at hi; simp at hi
          · rw [h_b] at hi; simp at hi
            exact writeMulxBundle_regs _ _ _ _ _ _ hi hno
      · simp at hi
  | Cif _ _ _ => simp [BignumExec.execInstr] at hi
  | Cfor _ _ _ => simp [BignumExec.execInstr] at hi
  | Cwhile _ _ _ => simp [BignumExec.execInstr] at hi
  | Ccall _ _ _ _ => simp [BignumExec.execInstr] at hi

/-! ### Body-level register frame

If no instruction in the body writes to register `x`, then executing
the body preserves `regs x`. -/

/-- If every instruction in `body` does not write to register `x`,
    then executing `body` preserves `regs x`. -/
theorem bignumExec_regs_frame
    (x : String) :
    ∀ (body : List InstrR) (s s' : BignumState),
    BignumExec.bignumExec body s = some s' →
    (∀ i ∈ body, instrNoWrite x i) →
    s'.regs x = s.regs x := by
  intro body
  induction body with
  | nil =>
    intro s s' hexec _
    rw [show BignumExec.bignumExec [] s = some s from rfl] at hexec
    cases hexec; rfl
  | cons i is ih =>
    intro s s' hexec hno
    rw [show BignumExec.bignumExec (i :: is) s =
          (match BignumExec.execInstr s i with
           | some s' => BignumExec.bignumExec is s'
           | none => none) from rfl] at hexec
    cases h_step : BignumExec.execInstr s i with
    | none => rw [h_step] at hexec; simp at hexec
    | some s_mid =>
      rw [h_step] at hexec
      simp only at hexec
      have h_i_no : instrNoWrite x i := hno i (List.mem_cons_self)
      have h_step_eq : s_mid.regs x = s.regs x :=
        execInstr_regs_frame s s_mid i x h_step h_i_no
      have h_is_no : ∀ j ∈ is, instrNoWrite x j := by
        intro j hj; exact hno j (List.mem_cons_of_mem _ hj)
      have h_rest : s'.regs x = s_mid.regs x := ih s_mid s' hexec h_is_no
      rw [h_rest, h_step_eq]

/-! ### Frame for a single byte: by induction on the body's instructions

Strategy: prove by induction on a list `body` that any byte `a` whose
disjointness from every store-address the body emits is guaranteed by
some predicate `P` (instantiated to "a ∈ range base_a 32 ∧ this address is
disjoint from range base_op 32") is preserved.

To keep the proof modular, we factor out the address-disjointness side
condition as a hypothesis on each store. -/

/-- If executing a body from `s` reaches `s'`, and every memory-store
    instruction in the body resolves to a `store64`-footprint contained
    in `range base_op 32` (under any reachable intermediate state),
    then for any byte address `a` not in `range base_op 32`, the byte
    at `a` is unchanged. -/
private theorem bignumExec_loadByte_outside
    (base_op : UInt64) :
    ∀ (body : List InstrR) (s s' : BignumState),
    BignumExec.bignumExec body s = some s' →
    -- Side condition: every memory store in the body has a footprint
    -- (8 bytes from the store address) contained in `range base_op 32`.
    (∀ s_mid s_post b1 b2 ws base off al sty rhs,
      body = b1 ++ (.Cassgn (.Lmem ws base off) al sty rhs :: b2) →
      BignumExec.bignumExec b1 s = some s_mid →
      BignumExec.execInstr s_mid (.Cassgn (.Lmem ws base off) al sty rhs)
        = some s_post →
      ws = .U64 ∧
      ∃ addr, BignumExec.resolveAddr s_mid base off = some addr ∧
              ∀ k : Nat, k < 8 → MemoryModel.range base_op 32
                                    (addr + UInt64.ofNat k)) →
    ∀ a, ¬ MemoryModel.range base_op 32 a →
        s'.mem.loadByte a = s.mem.loadByte a := by
  intro body
  induction body with
  | nil =>
    intro s s' hexec _ a _
    rw [show BignumExec.bignumExec [] s = some s from rfl] at hexec
    cases hexec
    rfl
  | cons i is ih =>
    intro s s' hexec hstore_in a hOut
    -- Step on i to s_mid.
    rw [show BignumExec.bignumExec (i :: is) s =
          (match BignumExec.execInstr s i with
           | some s' => BignumExec.bignumExec is s'
           | none => none) from rfl] at hexec
    cases h_step : BignumExec.execInstr s i with
    | none =>
      rw [h_step] at hexec
      simp at hexec
    | some s_mid =>
      rw [h_step] at hexec
      -- Apply IH: bignumExec is s_mid = some s'.
      have h_rec : s'.mem.loadByte a = s_mid.mem.loadByte a := by
        simp only at hexec
        apply ih s_mid s' hexec _ a hOut
        intro s_mid' s_post b1 b2 ws base off al sty rhs hbody hexec_b1 hstep
        -- The store in `is` corresponds to a store in `i :: is` at offset (1 + index).
        apply hstore_in s_mid' s_post (i :: b1) b2 ws base off al sty rhs
        · rw [hbody]; rfl
        · rw [show BignumExec.bignumExec (i :: b1) s =
              (match BignumExec.execInstr s i with
               | some s'' => BignumExec.bignumExec b1 s''
               | none => none) from rfl, h_step]
          exact hexec_b1
        · exact hstep
      rw [h_rec]
      -- Show s_mid.mem.loadByte a = s.mem.loadByte a.
      -- Either i is a memory store at base_op (so the byte changes
      -- only at base_op + k for some k < 32 — disjoint from a) or it
      -- preserves mem entirely.
      by_cases hi_store : ∃ ws base off al sty rhs,
                              i = .Cassgn (.Lmem ws base off) al sty rhs
      · obtain ⟨ws, base, off, al, sty, rhs, h_eq⟩ := hi_store
        -- Use hstore_in with b1 = [], b2 = is.
        have h_props := hstore_in s s_mid [] is ws base off al sty rhs
                          (by rw [h_eq]; rfl)
                          (by rfl)
                          (by rw [h_eq] at h_step; exact h_step)
        obtain ⟨h_ws, addr, h_addr, h_in⟩ := h_props
        subst h_ws
        rw [h_eq] at h_step
        obtain ⟨addr', w, h_addr', h_w, h_eq_state⟩ :=
          execInstr_storeMem s s_mid base off al sty rhs h_step
        rw [h_addr] at h_addr'
        cases h_addr'
        rw [h_eq_state]
        -- s_mid.mem = (storeMem s addr ...)
        show ((s.mem.store64 addr (UInt64.ofNat w.toNat)).loadByte a) =
              s.mem.loadByte a
        -- Each storeByte affects only the address it targets.
        -- a is not in range base_op 32, but addr+k is for k ∈ [0, 8),
        -- so a ≠ addr + k.
        have h_ne0 : a ≠ addr := by
          intro h_a_eq
          apply hOut
          rw [h_a_eq, show addr = addr + UInt64.ofNat 0 from by simp]
          exact h_in 0 (by omega)
        have h_ne : ∀ k : Nat, k < 8 → a ≠ addr + UInt64.ofNat k := by
          intro k hk h_a_eq
          apply hOut
          rw [h_a_eq]
          exact h_in k hk
        -- Reduce 8 storeByte applications via address normalization.
        simp only [MemoryModel.Mem.store64]
        -- The store64 inlines `addr + 1`, `addr + 2`, ... via numeric
        -- literals; restate h_ne for those literal forms.
        have h_ne7 : addr + 7 ≠ a := by
          have : a ≠ addr + UInt64.ofNat 7 := h_ne 7 (by omega)
          exact fun h => this (by rw [← h]; rfl)
        have h_ne6 : addr + 6 ≠ a := by
          have : a ≠ addr + UInt64.ofNat 6 := h_ne 6 (by omega)
          exact fun h => this (by rw [← h]; rfl)
        have h_ne5 : addr + 5 ≠ a := by
          have : a ≠ addr + UInt64.ofNat 5 := h_ne 5 (by omega)
          exact fun h => this (by rw [← h]; rfl)
        have h_ne4 : addr + 4 ≠ a := by
          have : a ≠ addr + UInt64.ofNat 4 := h_ne 4 (by omega)
          exact fun h => this (by rw [← h]; rfl)
        have h_ne3 : addr + 3 ≠ a := by
          have : a ≠ addr + UInt64.ofNat 3 := h_ne 3 (by omega)
          exact fun h => this (by rw [← h]; rfl)
        have h_ne2 : addr + 2 ≠ a := by
          have : a ≠ addr + UInt64.ofNat 2 := h_ne 2 (by omega)
          exact fun h => this (by rw [← h]; rfl)
        have h_ne1 : addr + 1 ≠ a := by
          have : a ≠ addr + UInt64.ofNat 1 := h_ne 1 (by omega)
          exact fun h => this (by rw [← h]; rfl)
        rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm h_ne7)]
        rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm h_ne6)]
        rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm h_ne5)]
        rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm h_ne4)]
        rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm h_ne3)]
        rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm h_ne2)]
        rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm h_ne1)]
        rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h_ne0]
      · push_neg at hi_store
        have hno : ∀ ws base off al sty rhs,
                    i ≠ .Cassgn (.Lmem ws base off) al sty rhs := by
          intro ws base off al sty rhs heq
          exact hi_store ws base off al sty rhs heq
        rw [execInstr_mem_preserve s s_mid i h_step hno]

/-! ### Chunk decomposition of `bodyComputesAlgoNat`

The body has 35 instructions split into:
  - `pre31`: first 31 instructions — register-only computation
    (1 zero const + 4 loads + 3 p constants + 4 copies + SUB chain (4) +
    mask SBB + all_ones + nmask XOR + 12 mask-AND/OR). Produces
    `o0, o1, o2, o3` registers holding the four limbs of `algoNat a_val`.
  - `stores4`: last 4 instructions — `store64 op {0,8,16,24} oi` writes
    the four limbs to memory at `base_op`.

The structural framing (chunks 1 + 2 are well-typed via `bignumExec_append`,
mem-frame for chunk 1 holds via `body_no_lmem_mem_frame`, register frame
for `op` holds via `bignumExec_regs_frame`, the 4 stores chain via
`execInstr_storeOp_const`) is fully Qed-closed below.

The remaining conjecture is the **algorithmic kernel**: after chunk 1, the
four `oi` registers hold specific BitVec 64 values whose Nat decomposition
equals `algoNat a_val`. This is the genuinely-volumetric content of the
proof — symbolic execution through 29 instructions to track the BitVec 64
computation, plus the BitVec arithmetic showing the SUB/SBB chain
followed by mask-cmov produces the right limbs of `if a ≥ p then a - p
else a`. -/

/-! #### Helpers moved up here so `bodyComputesAlgoNat` can use them.

These were originally defined below, supporting `bodyPreservesInput`. -/

/-- Decidable boolean: instruction is not `Cassgn (Lmem ...) ...`. -/
def instrNotLmemB : InstrR → Bool
  | .Cassgn (.Lmem _ _ _) _ _ _ => false
  | _ => true

theorem instrNotLmem_of_B (i : InstrR)
    (h : instrNotLmemB i = true) :
    ∀ ws base off al sty rhs, i ≠ .Cassgn (.Lmem ws base off) al sty rhs := by
  intro ws base off al sty rhs h_eq
  rw [h_eq] at h
  simp [instrNotLmemB] at h

/-- If no instruction in the body is a memory store, then memory is
    fully preserved. -/
theorem body_no_lmem_mem_frame
    (body : List InstrR) (s s' : BignumState)
    (hexec : BignumExec.bignumExec body s = some s')
    (hno : ∀ i ∈ body, ∀ ws base off al sty rhs,
             i ≠ .Cassgn (.Lmem ws base off) al sty rhs) :
    s'.mem = s.mem := by
  induction body generalizing s with
  | nil =>
    rw [show BignumExec.bignumExec [] s = some s from rfl] at hexec
    cases hexec; rfl
  | cons i is ih =>
    rw [show BignumExec.bignumExec (i :: is) s =
          (match BignumExec.execInstr s i with
           | some s' => BignumExec.bignumExec is s'
           | none => none) from rfl] at hexec
    cases h_step : BignumExec.execInstr s i with
    | none => rw [h_step] at hexec; simp at hexec
    | some s_mid =>
      rw [h_step] at hexec
      simp only at hexec
      have hno_i : ∀ ws base off al sty rhs,
                    i ≠ .Cassgn (.Lmem ws base off) al sty rhs :=
        hno i (List.mem_cons_self)
      have h_step_mem : s_mid.mem = s.mem :=
        execInstr_mem_preserve s s_mid i h_step hno_i
      have hno_is : ∀ j ∈ is, ∀ ws base off al sty rhs,
                      j ≠ .Cassgn (.Lmem ws base off) al sty rhs := by
        intro j hj; exact hno j (List.mem_cons_of_mem _ hj)
      rw [ih s_mid hexec hno_is, h_step_mem]

/-- After a `store64` to `base_op + k` (with `k + 8 ≤ 32`), every byte
    address outside `range base_op 32` is unaffected. -/
theorem store64_loadByte_outside_op
    (m : MemoryModel.Mem) (base_op : UInt64) (k : Nat) (hkj : k + 8 ≤ 32)
    (v : UInt64) (a : UInt64)
    (hOut : ¬ MemoryModel.range base_op 32 a) :
    (m.store64 (base_op + UInt64.ofNat k) v).loadByte a = m.loadByte a := by
  simp only [MemoryModel.Mem.store64]
  have h_ne_at : ∀ j' : Nat, j' < 8 →
                 base_op + UInt64.ofNat k + UInt64.ofNat j' ≠ a := by
    intro j' hj' h_eq
    apply hOut
    refine ⟨k + j', by omega, ?_⟩
    rw [← h_eq]
    ext
    simp [UInt64.toNat_add, Nat.add_assoc]
  have h0 : base_op + UInt64.ofNat k ≠ a := by
    have := h_ne_at 0 (by omega); simpa using this
  have h_lit : ∀ j : Nat, j < 8 →
                base_op + UInt64.ofNat k + UInt64.ofNat j =
                base_op + UInt64.ofNat (k + j) := by
    intro j _; ext; simp [UInt64.toNat_add, Nat.add_assoc]
  have h_eq_at : ∀ j : Nat, j < 8 → base_op + UInt64.ofNat (k + j) ≠ a := by
    intro j hj
    rw [← h_lit j hj]
    exact h_ne_at j hj
  have e1 : base_op + UInt64.ofNat k + 1 = base_op + UInt64.ofNat (k + 1) := by
    ext; simp [UInt64.toNat_add, Nat.add_assoc]
  have e2 : base_op + UInt64.ofNat k + 2 = base_op + UInt64.ofNat (k + 2) := by
    ext; simp [UInt64.toNat_add, Nat.add_assoc]
  have e3 : base_op + UInt64.ofNat k + 3 = base_op + UInt64.ofNat (k + 3) := by
    ext; simp [UInt64.toNat_add, Nat.add_assoc]
  have e4 : base_op + UInt64.ofNat k + 4 = base_op + UInt64.ofNat (k + 4) := by
    ext; simp [UInt64.toNat_add, Nat.add_assoc]
  have e5 : base_op + UInt64.ofNat k + 5 = base_op + UInt64.ofNat (k + 5) := by
    ext; simp [UInt64.toNat_add, Nat.add_assoc]
  have e6 : base_op + UInt64.ofNat k + 6 = base_op + UInt64.ofNat (k + 6) := by
    ext; simp [UInt64.toNat_add, Nat.add_assoc]
  have e7 : base_op + UInt64.ofNat k + 7 = base_op + UInt64.ofNat (k + 7) := by
    ext; simp [UInt64.toNat_add, Nat.add_assoc]
  rw [e1, e2, e3, e4, e5, e6, e7]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm (h_eq_at 7 (by omega)))]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm (h_eq_at 6 (by omega)))]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm (h_eq_at 5 (by omega)))]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm (h_eq_at 4 (by omega)))]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm (h_eq_at 3 (by omega)))]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm (h_eq_at 2 (by omega)))]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm (h_eq_at 1 (by omega)))]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ (Ne.symm h0)]

/-! ### Memory-load helpers for the byte-bridging step

Two helpers that connect `load64Mem` over `store64`:

  - `loadByte_store64_other`: a single byte load through 8 store-bytes,
    given byte-level disjointness from each.
  - `load64Mem_store64_self`: load a 64-bit word at the same address
    you stored to. Returns the stored value (after bit-recomposition).
  - `load64Mem_store64_other_bytewise`: load through a `store64` at an
    unrelated address, given the 8 bytewise preservation facts. -/

/-- A byte load through a `store64` at an unrelated address: peels through
    8 storeByte invocations using `Mem.loadByte_storeByte_other`. Made
    public for chunked composition's far-disjoint memory proofs. -/
theorem loadByte_store64_other
    (m : MemoryModel.Mem) (a a' : UInt64) (v' : UInt64)
    (h0 : a ≠ a') (h1 : a ≠ a' + 1) (h2 : a ≠ a' + 2) (h3 : a ≠ a' + 3)
    (h4 : a ≠ a' + 4) (h5 : a ≠ a' + 5) (h6 : a ≠ a' + 6) (h7 : a ≠ a' + 7) :
    (m.store64 a' v').loadByte a = m.loadByte a := by
  simp only [MemoryModel.Mem.store64]
  rw [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h7,
      MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h6,
      MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h5,
      MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h4,
      MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h3,
      MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h2,
      MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h1,
      MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h0]

/-- After storing 64 bits at address `a`, loading 64 bits at `a` returns
    the stored value. The `bv_decide` recovers the recomposition over
    `byteAt`/`UInt64.toBitVec`. Made public for use in chunked
    composition proofs (`CatCrypt.Tactics.ChunkedComposition`). -/
theorem load64Mem_store64_self
    (m : MemoryModel.Mem) (a : UInt64) (v : UInt64) :
    BignumExec.load64Mem (m.store64 a v) a = some v := by
  unfold BignumExec.load64Mem
  simp only [MemoryModel.Mem.store64]
  -- Numerical-literal disjointnesses (28 distinct pairs).
  have h70 : (a + 7 : UInt64) ≠ a := by simp
  have h71 : (a + 7 : UInt64) ≠ a + 1 := by simp
  have h72 : (a + 7 : UInt64) ≠ a + 2 := by simp
  have h73 : (a + 7 : UInt64) ≠ a + 3 := by simp
  have h74 : (a + 7 : UInt64) ≠ a + 4 := by simp
  have h75 : (a + 7 : UInt64) ≠ a + 5 := by simp
  have h76 : (a + 7 : UInt64) ≠ a + 6 := by simp
  have h60 : (a + 6 : UInt64) ≠ a := by simp
  have h61 : (a + 6 : UInt64) ≠ a + 1 := by simp
  have h62 : (a + 6 : UInt64) ≠ a + 2 := by simp
  have h63 : (a + 6 : UInt64) ≠ a + 3 := by simp
  have h64 : (a + 6 : UInt64) ≠ a + 4 := by simp
  have h65 : (a + 6 : UInt64) ≠ a + 5 := by simp
  have h50 : (a + 5 : UInt64) ≠ a := by simp
  have h51 : (a + 5 : UInt64) ≠ a + 1 := by simp
  have h52 : (a + 5 : UInt64) ≠ a + 2 := by simp
  have h53 : (a + 5 : UInt64) ≠ a + 3 := by simp
  have h54 : (a + 5 : UInt64) ≠ a + 4 := by simp
  have h40 : (a + 4 : UInt64) ≠ a := by simp
  have h41 : (a + 4 : UInt64) ≠ a + 1 := by simp
  have h42 : (a + 4 : UInt64) ≠ a + 2 := by simp
  have h43 : (a + 4 : UInt64) ≠ a + 3 := by simp
  have h30 : (a + 3 : UInt64) ≠ a := by simp
  have h31 : (a + 3 : UInt64) ≠ a + 1 := by simp
  have h32 : (a + 3 : UInt64) ≠ a + 2 := by simp
  have h20 : (a + 2 : UInt64) ≠ a := by simp
  have h21 : (a + 2 : UInt64) ≠ a + 1 := by simp
  have h10 : (a + 1 : UInt64) ≠ a := by simp
  simp only [MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h70.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h71.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h72.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h73.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h74.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h75.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h76.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h60.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h61.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h62.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h63.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h64.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h65.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h50.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h51.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h52.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h53.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h54.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h40.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h41.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h42.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h43.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h30.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h31.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h32.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h20.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h21.symm,
             MemoryModel.Mem.loadByte_storeByte_other _ _ _ _ h10.symm,
             MemoryModel.Mem.loadByte_storeByte_same]
  show some _ = _
  congr 1
  apply UInt64.eq_of_toBitVec_eq
  unfold MemoryModel.byteAt
  simp [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft]
  bv_decide

/-- A `load64Mem` through a `store64` at an unrelated address, given
    8 bytewise preservation facts (one per byte read). Made public
    for chunked composition's far-disjoint memory proofs. -/
theorem load64Mem_store64_other_bytewise
    (m : MemoryModel.Mem) (a a' : UInt64) (v' : UInt64)
    (h0 : (m.store64 a' v').loadByte a = m.loadByte a)
    (h1 : (m.store64 a' v').loadByte (a + 1) = m.loadByte (a + 1))
    (h2 : (m.store64 a' v').loadByte (a + 2) = m.loadByte (a + 2))
    (h3 : (m.store64 a' v').loadByte (a + 3) = m.loadByte (a + 3))
    (h4 : (m.store64 a' v').loadByte (a + 4) = m.loadByte (a + 4))
    (h5 : (m.store64 a' v').loadByte (a + 5) = m.loadByte (a + 5))
    (h6 : (m.store64 a' v').loadByte (a + 6) = m.loadByte (a + 6))
    (h7 : (m.store64 a' v').loadByte (a + 7) = m.loadByte (a + 7)) :
    BignumExec.load64Mem (m.store64 a' v') a = BignumExec.load64Mem m a := by
  unfold BignumExec.load64Mem
  rw [h0, h1, h2, h3, h4, h5, h6, h7]


/-- Specific values of `k` for the four stores in the body, where the
    address arithmetic reduces by `rfl`. Used to discharge each of the
    four store instructions. -/
theorem execInstr_storeOp_const
    (s s' : BignumState) (k : Int) (k_nat : Nat)
    (h_kn : UInt64.ofNat ((BitVec.ofNat 64 0 + BitVec.ofInt 64 k).toNat) =
              UInt64.ofNat k_nat)
    (name : String) (base_op : UInt64)
    (h_op : s.regs "op" = BitVec.ofNat 64 base_op.toNat)
    (h_step : BignumExec.execInstr s
              (.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" }
                          (.Pconst k))
                .AT_none (.sword .U64)
                (.Pvar { gv := { var := S2NBignumSSA.v name },
                          gs := false })) = some s') :
    s'.regs = s.regs ∧
    ∃ v : UInt64,
      v = UInt64.ofNat (s.regs (S2NBignumSSA.v name).vname).toNat ∧
      s'.mem = s.mem.store64 (base_op + UInt64.ofNat k_nat) v := by
  rw [show BignumExec.execInstr s
        (.Cassgn (.Lmem .U64 { var := S2NBignumSSA.v "op" }
                    (.Pconst k))
          .AT_none (.sword .U64)
          (.Pvar { gv := { var := S2NBignumSSA.v name }, gs := false })) =
      (BignumExec.evalPExpr s
          (.Pvar { gv := { var := S2NBignumSSA.v name }, gs := false })).bind
        (fun w => (BignumExec.resolveAddr s
                      { var := S2NBignumSSA.v "op" }
                      (.Pconst k)).bind
                    (fun addr => some (BignumExec.storeMem s addr
                                          (UInt64.ofNat w.toNat))))
      from rfl] at h_step
  simp only [BignumExec.evalPExpr] at h_step
  simp only [Option.bind_some] at h_step
  rw [show BignumExec.resolveAddr s
        { var := S2NBignumSSA.v "op" } (.Pconst k) =
        some (UInt64.ofNat ((s.regs "op" + BitVec.ofInt 64 k).toNat))
        from by simp [BignumExec.resolveAddr, S2NBignumSSA.v]] at h_step
  simp only [Option.bind_some] at h_step
  rw [h_op] at h_step
  have h_addr_eq :
      UInt64.ofNat ((BitVec.ofNat 64 base_op.toNat
                      + BitVec.ofInt 64 k).toNat) =
        base_op + UInt64.ofNat k_nat := by
    have h_arith :
        UInt64.ofNat ((BitVec.ofNat 64 base_op.toNat
                        + BitVec.ofInt 64 k).toNat) =
          base_op + UInt64.ofNat ((BitVec.ofNat 64 0
                                    + BitVec.ofInt 64 k).toNat) := by
      ext
      simp [UInt64.toNat_add]
    rw [h_arith, h_kn]
  rw [h_addr_eq] at h_step
  refine ⟨?_, UInt64.ofNat (s.regs (S2NBignumSSA.v name).vname).toNat, rfl, ?_⟩
  · cases h_step; rfl
  · cases h_step; rfl


/-! #### What's deferred

The remaining `sorry` in `bodyComputesAlgoNat` is the algorithmic kernel:
after running the first 31 instructions of the body from a state satisfying
the precondition, the four registers `o0, o1, o2, o3` hold BitVec 64 values
whose Nat-decomposition equals `algoNat a_val`.

Discharge: ~200 LoC of `simp [execInstr, ...]` rewrites tracking the
register state through 31 instructions (4 loads + 3 const + 4 copies +
SUB chain + mask-SBB + all_ones + nmask + 12 mask-AND/OR), then an
`omega`/`bv_decide` over the BitVec arithmetic showing the SUB/SBB chain
followed by `if cf then a else (a-p)` (encoded via mask-cmov) gives the
right limbs of `algoNat a`. The mvcgen Watch List item #4 would
automate this.

The byte-memory bridging is fully proved via the helpers
`load64Mem_store64_self` and `load64Mem_store64_offset_const` (for
disjoint-offset peels). The structural framing — chunk decomposition, memory
frame for chunk 1, register frame for `op`, the 4 stores chain via
`execInstr_storeOp_const` — is fully proved in line below. -/

/-- Lemma: `base + UInt64.ofNat k1 + i ≠ base + UInt64.ofNat k2 + j` whenever
    `k1, k2, i, j < 256` and the (k1 + i)-th and (k2 + j)-th absolute byte
    indices differ. The hypothesis `h_disj` directly states this.

    This is the byte-disjointness fact powering `load64Mem_store64_offset_const`. -/
private theorem byte_addr_ne
    (base : UInt64) (k1 k2 i j : Nat)
    (h1 : k1 < 256) (h2 : k2 < 256) (hi : i < 8) (hj : j < 8)
    (h_disj : k1 + i ≠ k2 + j) :
    base + UInt64.ofNat k1 + UInt64.ofNat i ≠
      base + UInt64.ofNat k2 + UInt64.ofNat j := by
  intro h
  apply h_disj
  apply_fun UInt64.toNat at h
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add,
      UInt64.toNat_ofNat_of_lt' (by omega : k1 < 2 ^ 64),
      UInt64.toNat_ofNat_of_lt' (by omega : k2 < 2 ^ 64),
      UInt64.toNat_ofNat_of_lt' (by omega : i < 2 ^ 64),
      UInt64.toNat_ofNat_of_lt' (by omega : j < 2 ^ 64)] at h
  -- Goal after rw:
  -- ((base.toNat + k1) % 2^64 + i) % 2^64 = ((base.toNat + k2) % 2^64 + j) % 2^64
  -- Bounds: base.toNat < 2^64, k1, k2 < 256, i, j < 8.
  have hb : base.toNat < 2 ^ 64 := base.toNat_lt_size
  omega

/-- Companion lemma: `base + UInt64.ofNat k1 + i ≠ base + UInt64.ofNat k2`,
    handling the byte-0 case where `loadByte_store64_other` expects `a ≠ a'`
    (without a `+ 0`). -/
private theorem byte_addr_ne_zero
    (base : UInt64) (k1 k2 i : Nat)
    (h1 : k1 < 256) (h2 : k2 < 256) (hi : i < 8)
    (h_disj : k1 + i ≠ k2) :
    base + UInt64.ofNat k1 + UInt64.ofNat i ≠ base + UInt64.ofNat k2 := by
  intro h
  apply h_disj
  apply_fun UInt64.toNat at h
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add,
      UInt64.toNat_ofNat_of_lt' (by omega : k1 < 2 ^ 64),
      UInt64.toNat_ofNat_of_lt' (by omega : k2 < 2 ^ 64),
      UInt64.toNat_ofNat_of_lt' (by omega : i < 2 ^ 64)] at h
  have hb : base.toNat < 2 ^ 64 := base.toNat_lt_size
  omega

/-- Helper for the byte-memory bridging in `bodyComputesAlgoNat`: a 64-bit
    load through a `store64` at a *byte-disjoint* constant offset is unaffected
    by the store. The offsets `k_store, k_read` must satisfy
    `k_read + 8 ≤ k_store ∨ k_store + 8 ≤ k_read`, and both must fit in
    a small range (≤ 256, well clear of the 2^64 wrap point).

    This is the reusable form used to peel the outer `store64`s in the
    4-write chain at `base_op + {0, 8, 16, 24}`. Made public for use
    in chunked composition proofs (`CatCrypt.Tactics.ChunkedComposition`). -/
theorem load64Mem_store64_offset_const
    (m : MemoryModel.Mem) (base : UInt64) (k_store k_read : Nat) (v : UInt64)
    (h_disj : k_read + 8 ≤ k_store ∨ k_store + 8 ≤ k_read)
    (h_bound : k_store + 8 ≤ 256 ∧ k_read + 8 ≤ 256) :
    BignumExec.load64Mem (m.store64 (base + UInt64.ofNat k_store) v)
                         (base + UInt64.ofNat k_read) =
    BignumExec.load64Mem m (base + UInt64.ofNat k_read) := by
  obtain ⟨h_bs, h_br⟩ := h_bound
  -- Two disjointness facts: with a + j_store byte addend, and without.
  have h_byte_ne : ∀ (i j : Nat), i < 8 → j < 8 →
      base + UInt64.ofNat k_read + UInt64.ofNat i ≠
        base + UInt64.ofNat k_store + UInt64.ofNat j := fun i j hi hj =>
    byte_addr_ne base k_read k_store i j (by omega) (by omega) hi hj (by omega)
  have h_byte_ne_zero : ∀ (i : Nat), i < 8 →
      base + UInt64.ofNat k_read + UInt64.ofNat i ≠
        base + UInt64.ofNat k_store := fun i hi =>
    byte_addr_ne_zero base k_read k_store i (by omega) (by omega) hi (by omega)
  -- For the j_read = 0 byte, the load address has no `+ 0` (it's just
  -- `base + ofNat k_read`), so we need to first wrap it as `+ ofNat 0`.
  have h_zero_eq : (base + UInt64.ofNat k_read : UInt64) =
      base + UInt64.ofNat k_read + UInt64.ofNat 0 := by simp
  -- Apply the bytewise helper.
  apply load64Mem_store64_other_bytewise m
    (base + UInt64.ofNat k_read) (base + UInt64.ofNat k_store) v
  · -- byte 0 of read.
    rw [h_zero_eq]
    exact loadByte_store64_other m _ (base + UInt64.ofNat k_store) v
      (h_byte_ne_zero 0 (by omega))
      (h_byte_ne 0 1 (by omega) (by omega))
      (h_byte_ne 0 2 (by omega) (by omega))
      (h_byte_ne 0 3 (by omega) (by omega))
      (h_byte_ne 0 4 (by omega) (by omega))
      (h_byte_ne 0 5 (by omega) (by omega))
      (h_byte_ne 0 6 (by omega) (by omega))
      (h_byte_ne 0 7 (by omega) (by omega))
  · -- byte 1 of read.
    rw [show (base + UInt64.ofNat k_read + 1 : UInt64) =
          base + UInt64.ofNat k_read + UInt64.ofNat 1 from rfl]
    exact loadByte_store64_other m _ (base + UInt64.ofNat k_store) v
      (h_byte_ne_zero 1 (by omega))
      (h_byte_ne 1 1 (by omega) (by omega))
      (h_byte_ne 1 2 (by omega) (by omega))
      (h_byte_ne 1 3 (by omega) (by omega))
      (h_byte_ne 1 4 (by omega) (by omega))
      (h_byte_ne 1 5 (by omega) (by omega))
      (h_byte_ne 1 6 (by omega) (by omega))
      (h_byte_ne 1 7 (by omega) (by omega))
  · -- byte 2 of read.
    rw [show (base + UInt64.ofNat k_read + 2 : UInt64) =
          base + UInt64.ofNat k_read + UInt64.ofNat 2 from rfl]
    exact loadByte_store64_other m _ (base + UInt64.ofNat k_store) v
      (h_byte_ne_zero 2 (by omega))
      (h_byte_ne 2 1 (by omega) (by omega))
      (h_byte_ne 2 2 (by omega) (by omega))
      (h_byte_ne 2 3 (by omega) (by omega))
      (h_byte_ne 2 4 (by omega) (by omega))
      (h_byte_ne 2 5 (by omega) (by omega))
      (h_byte_ne 2 6 (by omega) (by omega))
      (h_byte_ne 2 7 (by omega) (by omega))
  · -- byte 3 of read.
    rw [show (base + UInt64.ofNat k_read + 3 : UInt64) =
          base + UInt64.ofNat k_read + UInt64.ofNat 3 from rfl]
    exact loadByte_store64_other m _ (base + UInt64.ofNat k_store) v
      (h_byte_ne_zero 3 (by omega))
      (h_byte_ne 3 1 (by omega) (by omega))
      (h_byte_ne 3 2 (by omega) (by omega))
      (h_byte_ne 3 3 (by omega) (by omega))
      (h_byte_ne 3 4 (by omega) (by omega))
      (h_byte_ne 3 5 (by omega) (by omega))
      (h_byte_ne 3 6 (by omega) (by omega))
      (h_byte_ne 3 7 (by omega) (by omega))
  · -- byte 4 of read.
    rw [show (base + UInt64.ofNat k_read + 4 : UInt64) =
          base + UInt64.ofNat k_read + UInt64.ofNat 4 from rfl]
    exact loadByte_store64_other m _ (base + UInt64.ofNat k_store) v
      (h_byte_ne_zero 4 (by omega))
      (h_byte_ne 4 1 (by omega) (by omega))
      (h_byte_ne 4 2 (by omega) (by omega))
      (h_byte_ne 4 3 (by omega) (by omega))
      (h_byte_ne 4 4 (by omega) (by omega))
      (h_byte_ne 4 5 (by omega) (by omega))
      (h_byte_ne 4 6 (by omega) (by omega))
      (h_byte_ne 4 7 (by omega) (by omega))
  · -- byte 5 of read.
    rw [show (base + UInt64.ofNat k_read + 5 : UInt64) =
          base + UInt64.ofNat k_read + UInt64.ofNat 5 from rfl]
    exact loadByte_store64_other m _ (base + UInt64.ofNat k_store) v
      (h_byte_ne_zero 5 (by omega))
      (h_byte_ne 5 1 (by omega) (by omega))
      (h_byte_ne 5 2 (by omega) (by omega))
      (h_byte_ne 5 3 (by omega) (by omega))
      (h_byte_ne 5 4 (by omega) (by omega))
      (h_byte_ne 5 5 (by omega) (by omega))
      (h_byte_ne 5 6 (by omega) (by omega))
      (h_byte_ne 5 7 (by omega) (by omega))
  · -- byte 6 of read.
    rw [show (base + UInt64.ofNat k_read + 6 : UInt64) =
          base + UInt64.ofNat k_read + UInt64.ofNat 6 from rfl]
    exact loadByte_store64_other m _ (base + UInt64.ofNat k_store) v
      (h_byte_ne_zero 6 (by omega))
      (h_byte_ne 6 1 (by omega) (by omega))
      (h_byte_ne 6 2 (by omega) (by omega))
      (h_byte_ne 6 3 (by omega) (by omega))
      (h_byte_ne 6 4 (by omega) (by omega))
      (h_byte_ne 6 5 (by omega) (by omega))
      (h_byte_ne 6 6 (by omega) (by omega))
      (h_byte_ne 6 7 (by omega) (by omega))
  · -- byte 7 of read.
    rw [show (base + UInt64.ofNat k_read + 7 : UInt64) =
          base + UInt64.ofNat k_read + UInt64.ofNat 7 from rfl]
    exact loadByte_store64_other m _ (base + UInt64.ofNat k_store) v
      (h_byte_ne_zero 7 (by omega))
      (h_byte_ne 7 1 (by omega) (by omega))
      (h_byte_ne 7 2 (by omega) (by omega))
      (h_byte_ne 7 3 (by omega) (by omega))
      (h_byte_ne 7 4 (by omega) (by omega))
      (h_byte_ne 7 5 (by omega) (by omega))
      (h_byte_ne 7 6 (by omega) (by omega))
      (h_byte_ne 7 7 (by omega) (by omega))

-- Note: the original `pre_oi_values` lemma (kept for the existing
-- `bodyComputesAlgoNat` proof) currently has a `sorry` derived from
-- `pre_oi_values_triple`'s sorry. Once the triple closes, this one
-- closes automatically via the bridge lemma path.

/-- Decomposition of `memNat4 base m = some n` into 4 individual
    `load64Mem` results. Phase 3 sub-task A: lets `pre_oi_values`
    expose the 4 per-limb load hypotheses needed to symbolically
    reduce the 4 `Pload` steps in the body. -/
theorem memNat4_eq_some_iff (base : UInt64) (m : Mem) (n : Nat) :
    memNat4 base m = some n ↔
    ∃ l0 l1 l2 l3 : UInt64,
      BignumExec.load64Mem m base = some l0 ∧
      BignumExec.load64Mem m (base + 8) = some l1 ∧
      BignumExec.load64Mem m (base + 16) = some l2 ∧
      BignumExec.load64Mem m (base + 24) = some l3 ∧
      n = l0.toNat + l1.toNat * 2 ^ 64 + l2.toNat * 2 ^ 128 + l3.toNat * 2 ^ 192 := by
  constructor
  · intro h
    unfold memNat4 at h
    cases h0 : BignumExec.load64Mem m base with
    | none => rw [h0] at h; simp at h
    | some l0 =>
      cases h1 : BignumExec.load64Mem m (base + 8) with
      | none => rw [h0, h1] at h; simp at h
      | some l1 =>
        cases h2 : BignumExec.load64Mem m (base + 16) with
        | none => rw [h0, h1, h2] at h; simp at h
        | some l2 =>
          cases h3 : BignumExec.load64Mem m (base + 24) with
          | none => rw [h0, h1, h2, h3] at h; simp at h
          | some l3 =>
            refine ⟨l0, l1, l2, l3, rfl, rfl, rfl, rfl, ?_⟩
            rw [h0, h1, h2, h3] at h
            simpa using h.symm
  · rintro ⟨l0, l1, l2, l3, h0, h1, h2, h3, hn⟩
    unfold memNat4
    rw [h0, h1, h2, h3]
    simp [hn]

/-! ### Specialized match-reduction helpers for assignConst-shape steps

After `wp` unwinding (via `PredTrans.pushArg/pushOption/pure_apply +
Id.run`), the goal is a chain of `match (do let w ← some C; some
{regs := ..., mem := ...}) with | some s' => some ((), s') | none =>
none`. Each step's reduction is rfl-true. -/

private theorem match_assignConst (C : BitVec 64) (s : BignumState)
    (vname : String) :
    (match ((some C : Option (BitVec 64)).bind
              (fun w => some
                ({ regs := fun y => if y = vname then w else s.regs y,
                   mem := s.mem } : BignumState))) with
     | some s' => some ((), s')
     | none => none) =
      some ((),
        ({ regs := fun y => if y = vname then C else s.regs y,
           mem := s.mem } : BignumState)) := rfl

/-! ### Option-bind match reduction helpers

Phase 3 sub-task B's deepest blocker: `match (do let w ← some C; some _)
with | some s' => f s' | none => none` doesn't reduce under simp alone.
These `rfl`-closed lemmas perform the reduction explicitly, one
Option-bind at a time. -/

/-- One bind. -/
private theorem opt_match_bind1 {α β γ : Type}
    (C : α) (f : α → β) (g : β → γ) (h : γ) :
    (match (do let w ← some C; some (f w)) with
     | some s' => g s' | none => h) = g (f C) := rfl

/-- Two binds. -/
private theorem opt_match_bind2 {α β δ γ : Type}
    (C₁ : α) (C₂ : β) (f : α → β → δ) (g : δ → γ) (h : γ) :
    (match (do let a ← some C₁; let b ← some C₂; some (f a b)) with
     | some s' => g s' | none => h) = g (f C₁ C₂) := rfl

/-- Three binds. -/
private theorem opt_match_bind3 {α β δ ε γ : Type}
    (C₁ : α) (C₂ : β) (C₃ : δ) (f : α → β → δ → ε) (g : ε → γ) (h : γ) :
    (match (do let a ← some C₁; let b ← some C₂; let c ← some C₃;
                some (f a b c)) with
     | some s' => g s' | none => h) = g (f C₁ C₂ C₃) := rfl

/-! ### Equation lemmas exposing private S2NBignumSSA helpers

`S2NBignumSSA.cassgn`, `pvar`, `plval` are private. The Phase 3
sub-task B simp call needs to walk through these to unfold the body
literal. Equation lemmas via `rfl` re-expose the structural definitions. -/

private theorem assignConst_eq (s : String) (k : Int) :
    S2NBignumSSA.assignConst s k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v s }) .AT_none (.sword .U64) (.Pconst k) := rfl

private theorem assignBin_eq (s : String) (op : SOp2) (a b : String) :
    S2NBignumSSA.assignBin s op a b =
      .Cassgn (.Lvar { var := S2NBignumSSA.v s }) .AT_none (.sword .U64)
        (.Papp2 op (.Pvar { gv := { var := S2NBignumSSA.v a }, gs := false })
                   (.Pvar { gv := { var := S2NBignumSSA.v b }, gs := false })) := rfl

private theorem load64_eq (x base : String) (k : Int) :
    S2NBignumSSA.BignumModP25519_4.load64 x base k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64)
        (.Pload .U64 { var := S2NBignumSSA.v base } (.Pconst k)) := rfl

private theorem store64_eq (base : String) (k : Int) (src : String) :
    S2NBignumSSA.BignumModP25519_4.store64 base k src =
      .Cassgn (.Lmem .U64 { var := S2NBignumSSA.v base } (.Pconst k))
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

private theorem copy64_eq (dst src : String) :
    S2NBignumSSA.BignumModP25519_4.copy64 dst src =
      .Cassgn (.Lvar { var := S2NBignumSSA.v dst }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

private theorem subCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumModP25519_4.subCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SUB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

private theorem sbbCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumModP25519_4.sbbCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SBB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

/-! ### Phase 4 — equation lemmas for BignumDoubleP25519 -/

private theorem double_subCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumDoubleP25519.subCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SUB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

private theorem double_sbbCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumDoubleP25519.sbbCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SBB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

private theorem double_addCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumDoubleP25519.addCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"ADD_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

private theorem double_adcCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumDoubleP25519.adcCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"ADC_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

private theorem double_load64_eq (x base : String) (k : Int) :
    S2NBignumSSA.BignumDoubleP25519.load64 x base k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64)
        (.Pload .U64 { var := S2NBignumSSA.v base } (.Pconst k)) := rfl

private theorem double_store64_eq (base : String) (k : Int) (src : String) :
    S2NBignumSSA.BignumDoubleP25519.store64 base k src =
      .Cassgn (.Lmem .U64 { var := S2NBignumSSA.v base } (.Pconst k))
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

private theorem double_copy64'_eq (dst src : String) :
    S2NBignumSSA.BignumDoubleP25519.copy64' dst src =
      .Cassgn (.Lvar { var := S2NBignumSSA.v dst }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

/-! ### Phase 4 — equation lemmas for BignumSubP25519 -/

private theorem sub_subCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumSubP25519.subCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SUB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

private theorem sub_sbbCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumSubP25519.sbbCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"SBB_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

private theorem sub_addCopn_eq (cfOut r aName bName : String) :
    S2NBignumSSA.BignumSubP25519.addCopn cfOut r aName bName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"ADD_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false }] := rfl

private theorem sub_adcCopn_eq (cfOut r aName bName cinName : String) :
    S2NBignumSSA.BignumSubP25519.adcCopn cfOut r aName bName cinName =
      .Copn ([.Lnone {} (.sword .U64),
              .Lvar { var := S2NBignumSSA.v cfOut }] ++
             List.replicate 3 (.Lnone {} (.sword .U64)) ++
             [.Lvar { var := S2NBignumSSA.v r }]) .AT_none
            (.Oasm ⟨"ADC_64"⟩)
            [.Pvar { gv := { var := S2NBignumSSA.v aName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v bName }, gs := false },
             .Pvar { gv := { var := S2NBignumSSA.v cinName }, gs := false }] := rfl

private theorem sub_load64_eq (x base : String) (k : Int) :
    S2NBignumSSA.BignumSubP25519.load64 x base k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64)
        (.Pload .U64 { var := S2NBignumSSA.v base } (.Pconst k)) := rfl

private theorem sub_store64_eq (base : String) (k : Int) (src : String) :
    S2NBignumSSA.BignumSubP25519.store64 base k src =
      .Cassgn (.Lmem .U64 { var := S2NBignumSSA.v base } (.Pconst k))
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

/-! ### Phase 4 — `BignumSqr4` Phase Triples are in `Sqr4Phases.lean`

The Sqr4-specific equation lemmas (`sqr_load64_eq` etc.), the four
mvcgen-driven Phase Triples (`sqr4_init_triple`, `sqr4_phaseA_triple`,
`sqr4_phaseB_triple`, `sqr4_phaseC_triple`), the chained functional
wrapper `sqr_4_memory_filled`, the algebraic `sqr_4_correct_with_chain_witnesses`,
and the final `sqr_4_correct` skeleton all live in
`CatCrypt/Crypto/Jasmin/BignumHoare/Sqr4Phases.lean`. They were
extracted in commit (this one) so each compilation unit fits in
the 14 GiB host RAM ceiling. -/


/-! ### Phase Triples + functional wrappers — moved to companion module

The five `mvcgen`-driven phase triples (`pre_oi_values_triple`,
`double_p25519_phase{A,B}_triple`, `sub_p25519_phase{A,B}_triple`)
and the five functional/composition wrappers (`pre_oi_values`,
`double_p25519_triple`, `double_p25519_pre_oi_values`,
`sub_p25519_triple`, `sub_p25519_pre_oi_values`) live in three
per-primitive companion modules:

- `CatCrypt/Crypto/Jasmin/BignumHoare/ModWrap.lean` — `pre_oi_values`
  pair (mod_p25519_4 kernel).
- `CatCrypt/Crypto/Jasmin/BignumHoare/DoubleWrap.lean` —
  double_p25519 phase triples + composed triple + functional wrapper.
- `CatCrypt/Crypto/Jasmin/BignumHoare/SubWrap.lean` —
  sub_p25519 phase triples + composed triple + functional wrapper.

Their *statements* are very large (deep nested `addCarryIn` /
`subBorrowIn` chains over 22-39 instruction bodies), and even with
the proof bodies sorried the type-checking pressure pushed cumulative
elaboration past the 14 GiB host RAM ceiling when co-located in a
single file. Per-primitive splitting lets each pair elaborate in its
own Lean process so the term cache resets between files.

## Final operational + frame closure — also a companion module

The three closure theorems for `bignum_mod_p25519_4`
(`bodyComputesAlgoNat`, `bodyPreservesInput`,
`bignum_mod_p25519_4_correct_universal`) live in
`CatCrypt/Crypto/Jasmin/BignumHoare/ModP25519Final.lean`. Same memory
rationale.

Both companion modules extend the same `CatCrypt.Crypto.Jasmin.BignumHoare`
namespace, so all theorems remain addressable under `BignumHoare.*`
— no callsite migration needed beyond adding the corresponding
`import` lines. -/

end CatCrypt.Crypto.Jasmin.BignumHoare
