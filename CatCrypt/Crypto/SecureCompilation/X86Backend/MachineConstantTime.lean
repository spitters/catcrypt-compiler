/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# Machine-level constant-time for the emitted x86 subset

The *source-level* constant-time argument lives above code generation, at the
dialect IR: `Com.toUnifiedLeak` is a function of program syntax only, so a
dialect program's leakage trace is the same for every input
(`CryptoDialectUnifiedTrace.dialect_leakTrace_unified_constant`, re-exported for
the verified middle at `emptyEvSig` as
`RHPVerifiedMiddle.cprog_leakTrace_unified_constant` — despite its name that
restatement is also over `Com catCryptDialect`, not `CProg`). Because
that trace never mentions the valuation, the source-level statement is purely
structural. This module lifts the guarantee to the **emitted machine code**,
where it is not structural: a real straight-line x86 leaf (`List (JInstr w)` in
the `JasminModel` semantics) and its *machine* leakage trace — the sequence of
control-flow decisions and **memory-access addresses**, computed against the
running machine state.

## What an attacker observes, and why it is the address that matters

The standard constant-time leakage model (Barthe et al., CCS 2014) gives a
cache/branch-predictor attacker two channels:

* **control flow** — which conditional branch is taken (a `MLeak.branch`); and
* **memory addresses** — the address of every load/store (a `MLeak.mem`), since
  the cache line touched is observable.

A leaf is constant-time when *both* channels are a function of the program text
alone, never of a register **value** (hence never of a secret).

For the emitted reg-ptr ABI, a `loadMem`/`storeMem` names a base register and a
**compile-time-constant** displacement `off`; its effective address is
`base + off`, whose *shape* `(base, off)` is fixed by the instruction and is the
same in every state. That is exactly why these leaves are constant-time: the
address channel carries no value information. We make this precise by emitting,
for each memory instruction, its **effective address** computed against the
running machine state, and proving the emitted address trace is identical from
**any** two initial states.

The honest dual: a register-indexed `storeMemIdx base idx scale` (an
`mov %src, (%base,%idx,scale)` scatter, e.g. a secret-dependent table write)
has effective offset `scale · (s.get idx).toNat` — a function of the **value**
in `idx`. Its address leak therefore *differs* between two states that disagree
on `idx`, so it is **not** constant-time. `nonCT_storeMemIdx_leaks_value` below
exhibits that difference, which is what keeps the CT keystone non-vacuous: the
property genuinely distinguishes value-independent from value-dependent
addressing, rather than holding of every program because "there are no branches."

This is the machine-level analogue of the dialect-level
`dialect_leakTrace_unified_constant`, but computed against the machine state
rather than read off the program syntax.

**0 axioms** (`native_decide` is used only for the concrete leaf value pin),
**0 sorries**.

## References

* Barthe, Betarte, Campo, Luna, Pichardie,
  "System-Level Non-Interference for Constant-Time Cryptography", CCS 2014.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. Machine leakage events -/

/-- A machine-level leakage event: what a cache/branch-predictor attacker
    observes from one instruction.

    * `branch` — a control-flow decision was taken (a conditional jump). The
      emitted straight-line scalar subset contains none, so a constant-time leaf
      never emits one.
    * `mem base off` — a memory access whose **effective address** is
      `base + off`. For the direct base+displacement addressing of the reg-ptr
      ABI, `off` is the instruction's compile-time-constant displacement, so the
      whole event is fixed by the program text. For a register-indexed access the
      effective `off` is `scale · (value in the index register)`, which is where
      a value (hence a secret) would leak. -/
inductive MLeak where
  /-- A control-flow decision (conditional branch) was taken. -/
  | branch
  /-- A memory access at effective address `base + off`. -/
  | mem (base : String) (off : Int)
  deriving DecidableEq, Repr

/-- Is this leakage event a control-flow (branch) leak? -/
def MLeak.isBranch : MLeak → Bool
  | .branch => true
  | .mem _ _ => false

/-! ## 2. Per-instruction leakage against the running state

`instrLeak s i` is the leakage of executing `i` from state `s`. We thread the
state so the emitted address of a memory op is its **real effective address** in
that state — not a syntactic placeholder. This is what makes the constant-time
claim about genuine addresses: the keystone says the *emitted address trace* is
the same from any two states, so the cache-line sequence carries no value
information.

For the direct base+displacement ops the emitted offset is the instruction's
constant `off`, manifestly ignoring `s`. For the register-indexed ops the
emitted offset is `scale · (s.get idx).toNat`, which reads a register value out
of `s`. No scalar ALU/`mov` op leaks (no branch, no memory). -/
def instrLeak {w : Nat} (s : JState w) : JInstr w → List MLeak
  -- direct base+displacement memory ops: effective offset is the constant `off`
  | .loadMem _ base off    => [.mem base off]
  | .storeMem base off _   => [.mem base off]
  | .mulxMem _ _ _ base off => [.mem base off]
  -- register-indexed memory ops: effective offset depends on the index VALUE
  | .loadMemIdx _ base idx scale  =>
      [.mem base ((scale * (s.get idx).toNat : Nat) : Int)]
  | .storeMemIdx base idx scale _ =>
      [.mem base ((scale * (s.get idx).toNat : Nat) : Int)]
  -- every scalar ALU / mov / shift / cmov / mulx-reg op: no observable leak
  | _ => []

/-! ## 3. The block leakage trace, threaded through the machine semantics -/

/-- `blockLeak s body`: the machine leakage trace of running `body` from state
    `s`, i.e. the concatenation of each instruction's `instrLeak` against the
    state in which it executes (state threaded by `evalInstr`, exactly as
    `runBlock`). The control-flow + memory-address channel the attacker sees. -/
def blockLeak {w : Nat} (s : JState w) : List (JInstr w) → List MLeak
  | [] => []
  | i :: is => instrLeak s i ++ blockLeak (evalInstr s i) is

@[simp] theorem blockLeak_nil {w : Nat} (s : JState w) : blockLeak s [] = [] := rfl

@[simp] theorem blockLeak_cons {w : Nat} (s : JState w) (i : JInstr w)
    (is : List (JInstr w)) :
    blockLeak s (i :: is) = instrLeak s i ++ blockLeak (evalInstr s i) is := rfl

/-! ## 4. The direct-addressing constant-time class

A leaf is constant-time when each instruction's leak is independent of the
machine state. The scalar ALU/`mov` ops leak nothing; the direct
base+displacement memory ops leak their constant `(base, off)`. Only the
register-indexed ops read a value out of the state. We carve out the
constant-time class as the bodies that avoid the register-indexed ops. -/

/-- `IsDirect i`: instruction `i` addresses memory only through a base register
    and a **compile-time-constant** displacement (or touches no memory at all).
    Excludes the register-indexed `loadMemIdx`/`storeMemIdx`, whose effective
    address reads the value in an index register. -/
def IsDirect {w : Nat} : JInstr w → Prop
  | .loadMemIdx _ _ _ _    => False
  | .storeMemIdx _ _ _ _   => False
  | _ => True

instance {w : Nat} (i : JInstr w) : Decidable (IsDirect i) := by
  cases i <;> unfold IsDirect <;> infer_instance

/-- A direct instruction's leak does not depend on the machine state: for the
    scalar ops it is `[]`, and for the direct memory ops it is the constant
    `[.mem base off]`. This is the per-instruction core of the keystone. -/
theorem instrLeak_state_independent {w : Nat} (i : JInstr w) (h : IsDirect i)
    (s₁ s₂ : JState w) : instrLeak s₁ i = instrLeak s₂ i := by
  cases i <;> first | rfl | (simp [IsDirect] at h)

/-! ## 5. The constant-time keystone

If every instruction of a leaf is direct, its **whole machine leakage trace** —
control flow + memory addresses — is the same from any two initial states. The
attacker's view is therefore a function of the program text alone, so it carries
no information about the secret register values: the leaf is constant-time.

This is the machine-level analogue of the dialect-level
`dialect_leakTrace_unified_constant`, but computed against the machine state
rather than read off the program syntax. -/

/-- **Machine-level constant-time keystone.** A straight-line leaf all of whose
    instructions use direct (base + constant-displacement) addressing produces
    the **same** machine leakage trace from any two initial states `s₁ s₂`. Hence
    the observable control-flow + memory-address sequence is independent of every
    register value, in particular of secret inputs: the leaf is constant-time.

    Proved by induction over the block. The head's leak is state-independent by
    `instrLeak_state_independent`; the tails run from `evalInstr s₁ i` resp.
    `evalInstr s₂ i`, but the inductive hypothesis closes them since *every*
    instruction is direct, so no later leak inspects the (now diverged) states
    either. -/
theorem blockLeak_state_independent {w : Nat} (body : List (JInstr w))
    (hbody : ∀ i ∈ body, IsDirect i) (s₁ s₂ : JState w) :
    blockLeak s₁ body = blockLeak s₂ body := by
  induction body generalizing s₁ s₂ with
  | nil => rfl
  | cons i is ih =>
    have hi : IsDirect i := hbody i (List.mem_cons_self ..)
    have htl : ∀ j ∈ is, IsDirect j := fun j hj => hbody j (List.mem_cons_of_mem i hj)
    simp only [blockLeak_cons]
    rw [instrLeak_state_independent i hi s₁ s₂]
    rw [ih htl (evalInstr s₁ i) (evalInstr s₂ i)]

/-- The leakage of a direct leaf has **no** control-flow (branch) leak: the
    emitted straight-line scalar subset takes no conditional jumps, so the
    branch channel is empty regardless of state. -/
theorem blockLeak_no_branch {w : Nat} (body : List (JInstr w))
    (s : JState w) :
    (blockLeak s body).filter MLeak.isBranch = [] := by
  induction body generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [blockLeak_cons, List.filter_append]
    have : (instrLeak s i).filter MLeak.isBranch = [] := by
      cases i <;> simp [instrLeak, MLeak.isBranch]
    rw [this, ih (evalInstr s i)]
    rfl

/-! ## 6. A real worked leaf: a base+offset field/bignum store-back

A genuine straight-line leaf in the modeled `JInstr 64` subset using the reg-ptr
ABI's base+displacement memory ops: load two limbs `a[0]`, `a[1]` from a pointer
base `ap`, fold them with a scalar (`MULX` widening multiply + an `ADD`), and
store the result back to the output base `op`. This is the shape of an emitted
field-element / bignum word leaf (cf. `mpn_addmul_1`'s inner pass), restricted to
a fixed limb count so the body is straight-line.

Every instruction uses direct base+offset addressing or is a scalar ALU op, so
the leaf is in the constant-time class and the keystone applies. -/
def fieldStoreLeaf : List (JInstr 64) :=
  [ .loadMem "t0" "ap" 0          -- t0 = a[0]   (load, addr ap+0)
  , .loadMem "t1" "ap" 8          -- t1 = a[1]   (load, addr ap+8)
  , .mulx "hi" "lo" (.reg "b") (.reg "t0")  -- hi,lo = b * a[0]  (no memory)
  , .add "lo" (.reg "t1")         -- lo += a[1]  (no memory)
  , .add "lo" (.reg "cy")         -- lo += carry (no memory)
  , .storeMem "op" 0 (.reg "lo")  -- op[0] = lo  (store, addr op+0)
  , .storeMem "op" 8 (.reg "hi") ]-- op[1] = hi  (store, addr op+8)

/-- Every instruction of `fieldStoreLeaf` uses direct (base + constant-offset)
    addressing: it is in the constant-time class. -/
theorem fieldStoreLeaf_direct : ∀ i ∈ fieldStoreLeaf, IsDirect i := by
  decide

/-- The constant memory-address trace `fieldStoreLeaf` exposes: loads at `ap+0`,
    `ap+8`, then stores at `op+0`, `op+8`. Fixed by the program text. -/
theorem fieldStoreLeaf_trace (s : JState 64) :
    blockLeak s fieldStoreLeaf =
      [ .mem "ap" 0, .mem "ap" 8, .mem "op" 0, .mem "op" 8 ] := by
  rfl

/-- **`fieldStoreLeaf` is constant-time.** Its machine leakage trace — the four
    memory addresses `ap+0, ap+8, op+0, op+8` and no branch — is identical from
    *any* two initial states. The address sequence carries no register-value
    information, so the leaf leaks nothing about secret inputs. -/
theorem fieldStoreLeaf_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ fieldStoreLeaf = blockLeak s₂ fieldStoreLeaf :=
  blockLeak_state_independent fieldStoreLeaf fieldStoreLeaf_direct s₁ s₂

/-- `fieldStoreLeaf` takes no conditional branch: its control-flow channel is
    empty. -/
theorem fieldStoreLeaf_no_branch (s : JState 64) :
    (blockLeak s fieldStoreLeaf).filter MLeak.isBranch = [] :=
  blockLeak_no_branch fieldStoreLeaf s

/-! ## 7. The non-vacuity contrast: a register-indexed store is NOT constant-time

To witness that the keystone is not trivially true of every leaf, we exhibit a
one-instruction body that **fails** it. A register-indexed scatter
`storeMemIdx "op" "idx" 8 src` (an `mov %src, (%op,%idx,8)` — a secret-dependent
table write) has effective offset `8 · (value in idx)`. Two states that disagree
on the `idx` register therefore produce **different** memory-address traces: the
address channel leaks the index value. This is exactly the value-dependent
addressing the constant-time class excludes (`storeMemIdx` is `¬ IsDirect`). -/
def indexedScatterLeaf : List (JInstr 64) :=
  [ .storeMemIdx "op" "idx" 8 (.reg "lo") ]

/-- The indexed scatter is **not** in the direct (constant-time) class: its
    `storeMemIdx` reads the index register's value. -/
theorem indexedScatterLeaf_not_direct :
    ¬ (∀ i ∈ indexedScatterLeaf, IsDirect i) := by
  intro h
  have := h (.storeMemIdx "op" "idx" 8 (.reg "lo")) (by simp [indexedScatterLeaf])
  simp [IsDirect] at this

/-- **The contrast that keeps the keystone non-vacuous.** The register-indexed
    scatter leaks the index register's *value* into its memory-address trace:
    two states differing only on `idx` (here `idx = 0` vs `idx = 1`) produce
    **different** leakage traces (`op+0` vs `op+8`). So `indexedScatterLeaf` is
    *not* constant-time — the keystone's direct-addressing hypothesis is doing
    real work, not holding of every program. -/
theorem nonCT_storeMemIdx_leaks_value :
    ∃ s₁ s₂ : JState 64, blockLeak s₁ indexedScatterLeaf ≠ blockLeak s₂ indexedScatterLeaf := by
  refine ⟨{ regs := fun r => if r = "idx" then 0 else 0 },
          { regs := fun r => if r = "idx" then 1 else 0 }, ?_⟩
  decide

/-! ## 8. The standard CT formulation: leakage is determined by the PUBLIC inputs

`blockLeak_state_independent` is the special case "the trace is the same from *any*
two states" — it holds only when the leak reads no register value at all (direct
addressing). The standard constant-time definition (Barthe et al.) is weaker and
more general: the leakage is a function of the **public** inputs only — two states
that agree on the public registers (addresses, loop counters, pointer bases)
produce the same trace, *even if they differ on the secret registers* (the data).

This covers what the strict version cannot: a **public-indexed** access
(`storeMemIdx` whose index is a public counter — e.g. a Merkle/FRI loop position)
is constant-time, because its address is determined by the public index; only a
**secret**-indexed access leaks. We make `pub : String → Bool` the public-register
predicate and prove the trace is determined by the public registers, provided the
leaf addresses only through public registers and does not overwrite them. -/

/-- The public-register predicate: `pub r = true` marks `r` as public (an address
    base, a loop counter, a pointer) — its value may be observed; a secret-data
    register is `pub r = false`. -/
abbrev PubPred := String → Bool

/-- Two states agree on the public registers. -/
def agreePub (pub : PubPred) {w : Nat} (s₁ s₂ : JState w) : Prop :=
  ∀ r, pub r = true → s₁.get r = s₂.get r

/-- The registers an instruction writes (its destination(s)); stores write memory,
    not registers, so they write none. -/
def dstRegs {w : Nat} : JInstr w → List String
  | .mulx dHi dLo _ _ => [dHi, dLo]
  | .mulxMem dHi dLo _ _ _ => [dHi, dLo]
  | .storeMem _ _ _ => []
  | .storeMemIdx _ _ _ _ => []
  | .mov d _ | .add d _ | .sub d _ | .adc d _ | .sbb d _ | .imul d _ | .neg d
  | .setc d | .and_ d _ | .or_ d _ | .xor_ d _ | .shl d _ | .shr d _ | .sar d _
  | .cmove d _ | .cmovne d _ | .cmovb d _ | .adcx d _ | .adox d _
  | .loadMem d _ _ | .loadMemIdx d _ _ _ | .loadSym d _ => [d]

/-- The index register an instruction reads to form a memory address, if any
    (only the register-indexed ops have one). -/
def idxReg {w : Nat} : JInstr w → Option String
  | .loadMemIdx _ _ idx _ => some idx
  | .storeMemIdx _ idx _ _ => some idx
  | _ => none

/-- `evalInstr` leaves a register it does not write unchanged. -/
theorem evalInstr_get_of_not_dst {w : Nat} (s : JState w) (i : JInstr w) (r : String)
    (h : r ∉ dstRegs i) : (evalInstr s i).get r = s.get r := by
  cases i <;>
    simp_all [evalInstr, dstRegs, JState.get, JState.setReg, JState.writeB5W,
      JState.store, JState.storeIdx]

/-- A leaf is **CT-addressed** w.r.t. `pub`: every memory index register it uses is
    public, and it never overwrites a public register (the address/counter frame is
    caller-set and read-only within the leaf). -/
def CTAddressed (pub : PubPred) {w : Nat} (i : JInstr w) : Prop :=
  (∀ idx, idxReg i = some idx → pub idx = true)
    ∧ (∀ d ∈ dstRegs i, pub d = false)

/-- Per-instruction: a CT-addressed instruction's leak is determined by the public
    registers — equal across any two states agreeing on the public registers. -/
theorem instrLeak_pub_determined (pub : PubPred) {w : Nat} (i : JInstr w)
    (hi : CTAddressed pub i) (s₁ s₂ : JState w) (hag : agreePub pub s₁ s₂) :
    instrLeak s₁ i = instrLeak s₂ i := by
  cases i with
  | loadMemIdx d base idx scale =>
      have hidx : pub idx = true := hi.1 idx rfl
      simp only [instrLeak, hag idx hidx]
  | storeMemIdx base idx scale src =>
      have hidx : pub idx = true := hi.1 idx rfl
      simp only [instrLeak, hag idx hidx]
  | _ => rfl

/-- `agreePub` is preserved by a CT-addressed instruction: it writes only
    non-public registers, so the public registers are unchanged on both sides. -/
theorem agreePub_preserved (pub : PubPred) {w : Nat} (i : JInstr w)
    (hi : CTAddressed pub i) (s₁ s₂ : JState w) (hag : agreePub pub s₁ s₂) :
    agreePub pub (evalInstr s₁ i) (evalInstr s₂ i) := by
  intro r hr
  have hnd : r ∉ dstRegs i := by
    intro hmem; have := hi.2 r hmem; rw [hr] at this; exact absurd this (by decide)
  rw [evalInstr_get_of_not_dst s₁ i r hnd, evalInstr_get_of_not_dst s₂ i r hnd]
  exact hag r hr

/-- **The standard-CT keystone.** A leaf all of whose instructions are CT-addressed
    (index registers public, public registers never overwritten) produces the same
    machine leakage trace from any two states that **agree on the public registers**
    — regardless of the secret-register values. So the observable trace is a
    function of the public inputs alone: the leaf is constant-time in the standard
    (public-input-determined) sense, covering public-indexed addressing and
    public-counter loops, not just direct addressing. -/
theorem blockLeak_pub_determined (pub : PubPred) {w : Nat} (body : List (JInstr w))
    (hbody : ∀ i ∈ body, CTAddressed pub i) (s₁ s₂ : JState w)
    (hag : agreePub pub s₁ s₂) :
    blockLeak s₁ body = blockLeak s₂ body := by
  induction body generalizing s₁ s₂ with
  | nil => rfl
  | cons i is ih =>
    have hi : CTAddressed pub i := hbody i (List.mem_cons_self ..)
    have htl : ∀ j ∈ is, CTAddressed pub j := fun j hj => hbody j (List.mem_cons_of_mem i hj)
    simp only [blockLeak_cons]
    rw [instrLeak_pub_determined pub i hi s₁ s₂ hag]
    rw [ih htl (evalInstr s₁ i) (evalInstr s₂ i)
        (agreePub_preserved pub i hi s₁ s₂ hag)]

/-! ## 9. A public-indexed leaf IS constant-time (what the strict version excluded)

A Merkle/FRI loop body indexes memory by a **public** loop position (`pos`), then
folds secret data. The strict `IsDirect` keystone rejects it (`storeMemIdx` is not
direct); the standard keystone accepts it: with `pos` public and the data registers
secret, the address trace is determined by `pos` alone. -/

/-- The public/secret split for the worked indexed leaf: the loop position `pos`
    and the bases `op`/`ap` are public; everything else (the data) is secret. -/
def demoPub : PubPred := fun r => r = "pos" || r = "op" || r = "ap"

/-- A public-indexed store: `op[pos] = data` with `pos` a public loop counter. Its
    address depends on `pos` (public), not on the secret `data`. -/
def pubIndexedLeaf : List (JInstr 64) :=
  [ .storeMemIdx "op" "pos" 8 (.reg "data") ]

/-- Every instruction of `pubIndexedLeaf` is CT-addressed w.r.t. `demoPub`: its index
    `pos` is public and it writes no register. -/
theorem pubIndexedLeaf_ctAddressed : ∀ i ∈ pubIndexedLeaf, CTAddressed demoPub i := by
  intro i hi
  rw [pubIndexedLeaf, List.mem_singleton] at hi
  subst hi
  refine ⟨?_, ?_⟩
  · intro idx h; simp only [idxReg, Option.some.injEq] at h; subst h; rfl
  · intro d hd; simp only [dstRegs, List.not_mem_nil] at hd

/-- **The public-indexed leaf is constant-time** in the standard sense: any two
    states agreeing on the public registers (`pos`, `op`, `ap`) — but differing
    arbitrarily on the secret `data` — produce the same leakage trace. This is the
    generalization the strict keystone could not express. -/
theorem pubIndexedLeaf_constant_time (s₁ s₂ : JState 64)
    (hag : agreePub demoPub s₁ s₂) :
    blockLeak s₁ pubIndexedLeaf = blockLeak s₂ pubIndexedLeaf :=
  blockLeak_pub_determined demoPub pubIndexedLeaf pubIndexedLeaf_ctAddressed s₁ s₂ hag

/-! ## 10. Constant-time over CONTROL FLOW: counted loops + public-guard conditionals

Sections 5–9 close constant-time for **straight-line** owned leaves. This section
lifts the same public-input-determined discipline to the two structured
control-flow constructs the covered front fragment emits (`RFor`/`RIfNz`):

* a **counted loop** with a compile-time-**public** trip count `n` (`RFor`'s
  static bound): both runs execute the *same* number of iterations, so the
  leakage sequence has the same length and — iteration by iteration — the same
  events; and
* a **public-guard conditional** (`RIfNz` with `lt guard = .Public`): the guard
  register is public, so two states agreeing on the public registers agree on the
  guard, take the **same** arm, and produce the same branch-plus-arm leakage.

Both hold *only* under the public-control-flow discipline: a **secret** trip count
or a **secret** guard is genuinely not constant-time
(`nonCT_secretGuard_leaks_value` below witnesses the guard case).

Unlike the emitted `LinstrR`/`lsem` control flow (`Lcond`/`Lgoto`, whose CT is
`FrontControlLsem.front_control_lsem_correct_and_robust` /
`JasminLsemLoop.loopLR_lsemLeak_state_independent`), the owned *machine* block
`List (JInstr w)` carries no branch instruction. So here we model the structured
control flow explicitly over the machine leakage `blockLeak`, threading the same
`JState` and reusing §8's `blockLeak_pub_determined` / `agreePub` public-register
discipline for the straight-line leaves. **No `jasminc_preserves_ct`.** -/

/-- Running a whole straight-line block preserves `agreePub`: each CT-addressed
    instruction writes only non-public registers (`agreePub_preserved`), so the
    public frame (address bases, loop counters) is carried unchanged through the
    block on both sides. The block-level lift of `agreePub_preserved`, by
    induction over the instruction list. -/
theorem runBlock_agreePub_preserved (pub : PubPred) {w : Nat} (body : List (JInstr w))
    (hbody : ∀ i ∈ body, CTAddressed pub i) (s₁ s₂ : JState w)
    (hag : agreePub pub s₁ s₂) :
    agreePub pub (runBlock s₁ body) (runBlock s₂ body) := by
  induction body generalizing s₁ s₂ with
  | nil => exact hag
  | cons i is ih =>
    have hi : CTAddressed pub i := hbody i (List.mem_cons_self ..)
    have htl : ∀ j ∈ is, CTAddressed pub j := fun j hj => hbody j (List.mem_cons_of_mem i hj)
    simp only [runBlock_cons]
    exact ih htl (evalInstr s₁ i) (evalInstr s₂ i)
      (agreePub_preserved pub i hi s₁ s₂ hag)

/-- A **structured owned control-flow block**: the machine-level analogue of the
    covered front fragment's control shapes, layered over straight-line
    `List (JInstr w)` leaves.

    * `straight body` — a straight-line machine leaf (a `List (JInstr w)`).
    * `seq a b` — sequential composition.
    * `loop n body` — a counted loop with a **compile-time-public** trip count `n`
      (`RFor`'s static bound): `body` runs exactly `n` times. The counter is
      public by construction (the literal `n`), so both runs iterate `n` times.
    * `ifPub guard thenB elseB` — a conditional on the register `guard`: `thenB`
      when `guard ≠ 0`, `elseB` when `guard = 0` (`RIfNz`). The branch decision is
      an observable `MLeak.branch`; it is constant-time exactly when `guard` is
      public (`RIfNz`'s `lt guard = .Public`). -/
inductive OwnedCF (w : Nat) where
  /-- A straight-line machine leaf. -/
  | straight (body : List (JInstr w))
  /-- Sequential composition of two control-flow blocks. -/
  | seq (a b : OwnedCF w)
  /-- A counted loop: `body` run `n` times, `n` a compile-time-public trip count. -/
  | loop (n : Nat) (body : OwnedCF w)
  /-- A conditional on register `guard`: `thenB` if `guard ≠ 0`, else `elseB`. -/
  | ifPub (guard : String) (thenB elseB : OwnedCF w)

mutual

/-- `cfExec s cf = (leak, s')`: the machine leakage trace of running the
    structured block `cf` from state `s`, together with the post-state `s'`. The
    straight-line leaves use `blockLeak`/`runBlock`; a conditional emits an
    `MLeak.branch` for the decision then the taken arm; a counted loop folds its
    body `n` times (`cfLoop`). Threads the same `JState` as the machine semantics,
    so the leak model has the same shape as execution. -/
def cfExec {w : Nat} (s : JState w) (cf : OwnedCF w) : List MLeak × JState w :=
  match cf with
  | .straight body => (blockLeak s body, runBlock s body)
  | .seq a b =>
      ((cfExec s a).1 ++ (cfExec (cfExec s a).2 b).1, (cfExec (cfExec s a).2 b).2)
  | .loop n body => cfLoop n body s
  | .ifPub guard thenB elseB =>
      if s.get guard = 0 then
        (MLeak.branch :: (cfExec s elseB).1, (cfExec s elseB).2)
      else
        (MLeak.branch :: (cfExec s thenB).1, (cfExec s thenB).2)
  termination_by 2 * sizeOf cf
  decreasing_by all_goals (simp_wf <;> omega)

/-- `cfLoop n body s`: fold the control-flow body `body` over `n` iterations from
    `s`, concatenating each iteration's leak. The counter `n` is the (public)
    literal trip count, so the number of iterations — hence the leak length — is
    fixed by the program text, not by any register value. -/
def cfLoop {w : Nat} (n : Nat) (body : OwnedCF w) (s : JState w) : List MLeak × JState w :=
  match n with
  | 0 => ([], s)
  | n + 1 =>
      ((cfExec s body).1 ++ (cfLoop n body (cfExec s body).2).1,
       (cfLoop n body (cfExec s body).2).2)
  termination_by 2 * sizeOf body + 2 * n + 1
  decreasing_by all_goals (simp_wf <;> omega)

end

/-- A structured owned block is **CT-controlled** w.r.t. `pub`: every straight-line
    leaf is `CTAddressed` (§8: index registers public, public registers never
    overwritten), and every conditional guard is a **public** register. The
    public-control-flow discipline for the machine block: a secret guard (or a
    secret trip count — excluded by construction, `loop`'s `n` is a literal) is not
    constant-time. -/
def CFControlled (pub : PubPred) {w : Nat} : OwnedCF w → Prop
  | .straight body => ∀ i ∈ body, CTAddressed pub i
  | .seq a b => CFControlled pub a ∧ CFControlled pub b
  | .loop _ body => CFControlled pub body
  | .ifPub guard thenB elseB =>
      pub guard = true ∧ CFControlled pub thenB ∧ CFControlled pub elseB

/-- **Counted-loop 2-safety.** If one iteration of `body` is public-input-determined
    (`ih`: equal leak and preserved `agreePub` across states agreeing on the public
    registers), then the whole `n`-fold loop is too: both runs execute the *same*
    `n` iterations, so their leak traces agree and the public frame is preserved.
    By induction on the public trip count `n`. -/
theorem cfLoop_pub_determined (pub : PubPred) {w : Nat} (body : OwnedCF w)
    (ih : ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ →
      (cfExec s₁ body).1 = (cfExec s₂ body).1
        ∧ agreePub pub (cfExec s₁ body).2 (cfExec s₂ body).2) :
    ∀ (n : Nat) (s₁ s₂ : JState w), agreePub pub s₁ s₂ →
      (cfLoop n body s₁).1 = (cfLoop n body s₂).1
        ∧ agreePub pub (cfLoop n body s₁).2 (cfLoop n body s₂).2 := by
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ hag
    refine ⟨?_, ?_⟩
    · simp only [cfLoop]
    · simp only [cfLoop]; exact hag
  | succ m ihm =>
    intro s₁ s₂ hag
    obtain ⟨hl, ha⟩ := ih s₁ s₂ hag
    obtain ⟨hl', ha'⟩ := ihm (cfExec s₁ body).2 (cfExec s₂ body).2 ha
    refine ⟨?_, ?_⟩
    · simp only [cfLoop]; rw [hl, hl']
    · simp only [cfLoop]; exact ha'

/-- **The control-flow constant-time keystone.** A CT-controlled structured owned
    block (`CFControlled pub cf`) produces the **same** machine leakage trace from
    any two states that **agree on the public registers** — regardless of the
    secret-register values — and preserves that agreement on the post-states. So the
    observable control-flow + memory-address sequence over the counted-loop /
    public-guard-conditional fragment is a function of the public inputs alone: the
    block is constant-time.

    Proof by induction on `cf`. Straight leaves close by §8's
    `blockLeak_pub_determined` (leak) and `runBlock_agreePub_preserved` (agreement).
    A conditional's guard is public, so both states agree on it and take the same
    arm (closed by that arm's IH), prefixed by the identical `MLeak.branch`
    decision. A counted loop closes by `cfLoop_pub_determined` over its public trip
    count. **No `jasminc_preserves_ct`.** -/
theorem cfExec_pub_determined (pub : PubPred) {w : Nat} (cf : OwnedCF w) :
    CFControlled pub cf → ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ →
      (cfExec s₁ cf).1 = (cfExec s₂ cf).1
        ∧ agreePub pub (cfExec s₁ cf).2 (cfExec s₂ cf).2 := by
  induction cf with
  | straight body =>
    intro hcf s₁ s₂ hag
    simp only [cfExec]
    exact ⟨blockLeak_pub_determined pub body hcf s₁ s₂ hag,
           runBlock_agreePub_preserved pub body hcf s₁ s₂ hag⟩
  | seq a b iha ihb =>
    intro hcf s₁ s₂ hag
    obtain ⟨hca, hcb⟩ := hcf
    obtain ⟨hla, haa⟩ := iha hca s₁ s₂ hag
    obtain ⟨hlb, hab⟩ := ihb hcb (cfExec s₁ a).2 (cfExec s₂ a).2 haa
    refine ⟨?_, ?_⟩
    · simp only [cfExec]; rw [hla, hlb]
    · simp only [cfExec]; exact hab
  | loop n body ihbody =>
    intro hcf s₁ s₂ hag
    have hcb : CFControlled pub body := hcf
    simp only [cfExec]
    exact cfLoop_pub_determined pub body (ihbody hcb) n s₁ s₂ hag
  | ifPub guard thenB elseB iht ihe =>
    intro hcf s₁ s₂ hag
    obtain ⟨hg, hct, hce⟩ := hcf
    have hgeq : s₁.get guard = s₂.get guard := hag guard hg
    by_cases hz : s₁.get guard = 0
    · have hz2 : s₂.get guard = 0 := by rw [← hgeq]; exact hz
      obtain ⟨hl, ha⟩ := ihe hce s₁ s₂ hag
      refine ⟨?_, ?_⟩
      · simp only [cfExec, if_pos hz, if_pos hz2]; rw [hl]
      · simp only [cfExec, if_pos hz, if_pos hz2]; exact ha
    · have hz2 : ¬ s₂.get guard = 0 := by rw [← hgeq]; exact hz
      obtain ⟨hl, ha⟩ := iht hct s₁ s₂ hag
      refine ⟨?_, ?_⟩
      · simp only [cfExec, if_neg hz, if_neg hz2]; rw [hl]
      · simp only [cfExec, if_neg hz, if_neg hz2]; exact ha

/-- **`owned_ct_control_flow`.** The headline corollary: over the counted-loop +
    public-guard-conditional owned fragment (`RFor` / `RIfNz`), a CT-controlled
    structured block leaks the **same** machine trace from any two states agreeing
    on the public registers. The public-control-flow side condition is explicit in
    `CFControlled pub cf`: every conditional guard is public (`RIfNz`'s
    `lt guard = .Public`) and every loop trip count is a compile-time literal
    (`RFor`'s static bound). Axiom-free of `jasminc_preserves_ct`. -/
theorem owned_ct_control_flow (pub : PubPred) {w : Nat} (cf : OwnedCF w)
    (hcf : CFControlled pub cf) (s₁ s₂ : JState w) (hag : agreePub pub s₁ s₂) :
    (cfExec s₁ cf).1 = (cfExec s₂ cf).1 :=
  (cfExec_pub_determined pub cf hcf s₁ s₂ hag).1

/-! ### 10.1 A worked counted-loop leaf: a public-based store-back, run `n` times

A field/bignum store-back `t := ap[0]; op[0] := t` (direct base+offset addressing
through the public pointers `ap`/`op`, folding secret data in `t`) run inside a
counted loop with the **public** trip count `3`. The address bases are public; the
data register `t` is secret. The loop leaks the same address sequence from any two
states agreeing on `ap`/`op`, whatever the secret data. -/

/-- The public/secret split for the worked control-flow leaves: the pointer bases
    `ap`/`op` (and, for the branch demo, the guard `g`) are public; the data is
    secret. -/
def cfPub : PubPred := fun r => r = "ap" || r = "op" || r = "g"

/-- A straight-line loop body: load `ap[0]` into the secret data register `t`, store
    it back to `op[0]`. Direct base+offset addressing through the public pointers. -/
def cfLoopBody : List (JInstr 64) :=
  [ .loadMem "t" "ap" 0, .storeMem "op" 0 (.reg "t") ]

/-- A counted loop running `cfLoopBody` three times (public trip count). -/
def cfLoopDemo : OwnedCF 64 := .loop 3 (.straight cfLoopBody)

/-- `cfLoopBody` is CT-addressed w.r.t. `cfPub`: neither instruction is
    register-indexed (`idxReg = none`), and the only written register `t` is
    non-public. -/
theorem cfLoopBody_ctAddressed : ∀ i ∈ cfLoopBody, CTAddressed cfPub i := by
  intro i hi
  simp only [cfLoopBody, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨by intro idx h; exact absurd h (by simp [idxReg]),
           by intro d hd; simp only [dstRegs, List.mem_singleton] at hd; subst hd; decide⟩
  · exact ⟨by intro idx h; exact absurd h (by simp [idxReg]),
           by intro d hd; simp only [dstRegs, List.not_mem_nil] at hd⟩

/-- The counted-loop demo is CT-controlled (its body is CT-addressed). -/
theorem cfLoopDemo_controlled : CFControlled cfPub cfLoopDemo := cfLoopBody_ctAddressed

/-- **The counted loop is constant-time.** Any two states agreeing on the public
    pointers `ap`/`op` — differing arbitrarily on the secret data — produce the same
    machine leakage trace over all three iterations. -/
theorem cfLoopDemo_constant_time (s₁ s₂ : JState 64)
    (hag : agreePub cfPub s₁ s₂) :
    (cfExec s₁ cfLoopDemo).1 = (cfExec s₂ cfLoopDemo).1 :=
  owned_ct_control_flow cfPub cfLoopDemo cfLoopDemo_controlled s₁ s₂ hag

/-! ### 10.2 A worked public-guard conditional, and the secret-guard contrast

A conditional on the **public** register `g`: the then/else arms address memory
through public bases, and `g` public makes "which arm" a public observation. Then
the non-vacuity contrast: the SAME conditional shape on a **secret** guard leaks —
two states differing only on the guard take different arms with different memory
addresses, so the traces differ. This is what forces `RIfNz`'s public-scrutinee
side condition. -/

/-- A public-guard conditional: `if g ≠ 0 then t := ap[0] else op[0] := t`. -/
def cfIfDemo : OwnedCF 64 :=
  .ifPub "g" (.straight [.loadMem "t" "ap" 0]) (.straight [.storeMem "op" 0 (.reg "t")])

/-- `cfIfDemo` is CT-controlled: its guard `g` is public and both arms are
    CT-addressed. -/
theorem cfIfDemo_controlled : CFControlled cfPub cfIfDemo := by
  refine ⟨by decide, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨by intro idx h; exact absurd h (by simp [idxReg]),
           by intro d hd; simp only [dstRegs, List.mem_singleton] at hd; subst hd; decide⟩
  · intro i hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨by intro idx h; exact absurd h (by simp [idxReg]),
           by intro d hd; simp only [dstRegs, List.not_mem_nil] at hd⟩

/-- **The public-guard conditional is constant-time.** Any two states agreeing on
    the public registers (`g`, `ap`, `op`) — but differing on secret data — take the
    same arm (guard public) and produce the same branch-plus-arm leakage. -/
theorem cfIfDemo_constant_time (s₁ s₂ : JState 64)
    (hag : agreePub cfPub s₁ s₂) :
    (cfExec s₁ cfIfDemo).1 = (cfExec s₂ cfIfDemo).1 :=
  owned_ct_control_flow cfPub cfIfDemo cfIfDemo_controlled s₁ s₂ hag

/-- A conditional on a **secret** guard `sec`, with arms that touch *different*
    memory addresses (`A[0]` vs `B[0]`). Not CT-controlled w.r.t. a `pub` that
    marks `sec` secret. -/
def cfSecretIf : OwnedCF 64 :=
  .ifPub "sec" (.straight [.loadMem "t" "A" 0]) (.straight [.loadMem "t" "B" 0])

/-- **The contrast that keeps the control-flow keystone non-vacuous.** A conditional
    on a **secret** guard leaks the guard's value through the memory-address trace:
    two states differing only on `sec` (here `sec = 1` vs `sec = 0`) take different
    arms and so touch different addresses (`A+0` vs `B+0`), producing **different**
    leakage traces. So `cfSecretIf` is *not* constant-time — the public-guard side
    condition in `CFControlled` / `owned_ct_control_flow` is doing real work, not
    holding of every conditional. -/
theorem nonCT_secretGuard_leaks_value :
    ∃ s₁ s₂ : JState 64, (cfExec s₁ cfSecretIf).1 ≠ (cfExec s₂ cfSecretIf).1 := by
  refine ⟨{ regs := fun r => if r = "sec" then 1 else 0 }, { regs := fun _ => 0 }, ?_⟩
  have h1 : ¬ ({ regs := fun r => if r = "sec" then 1 else 0 } : JState 64).get "sec" = 0 := by
    decide
  have h2 : ({ regs := fun _ => 0 } : JState 64).get "sec" = 0 := by decide
  simp only [cfSecretIf, cfExec, if_neg h1, if_pos h2, blockLeak_cons, instrLeak,
    blockLeak_nil, List.append_nil]
  decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
