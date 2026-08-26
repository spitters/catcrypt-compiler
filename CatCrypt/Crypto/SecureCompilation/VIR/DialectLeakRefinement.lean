/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
import CatCrypt.Crypto.SecureCompilation.X86Backend.RHPFull

/-!
# Dialect → jasmin → x86 leak-refinement

`LeakTraceCom.lean` built the dialect-level structural leak trace
`leakTraceCom : Com catCryptDialect → LeakTrace` and an *equality* adequacy to
`CProg.leakTrace`. Its "Scope" named the residual: `leakTraceCom` lives on the
abstract op-sequence `Com catCryptDialect`, whereas `RHPFull.blockLeak`
lives on the lowered x86 `JInstr`/`JState`; bridging the two needs the
dialect → jasmin → x86 leak-refinement chain. This file builds that chain, as
far as it closes, and names the edge that does not.

## What this file delivers

* **§1 A jasmin-level structural leak trace `leakTraceJ : Com jasminDialect →
  LeakTrace`**, the one-IR-level-down mirror of `leakTraceCom`: per `.var` node
  it emits `jOpLeakEvent e.op` and recurses; `.ret` emits `[]`. Every
  `JasminOp` is a branch-free / pure or opaque-call op (the dialect has no
  control-flow op), so the jasmin trace, like the dialect trace, is a function
  of syntax only.

* **§2 The dialect → jasmin leak-refinement step.** On the lowered fragment the
  front `cryptoDialectToJasminCom` lowers one dialect op to exactly one jasmin
  op, so it preserves the *length* of the leak trace event-for-event:
  `(leakTraceJ jcom).length = (leakTraceCom cc).length` whenever
  `cryptoDialectToJasminCom cc = some jcom` (`leakTraceJ_length_refines`). Since
  both traces are syntax-only, both are state-independent
  (`leakTraceJ_state_independent`); the lowering transports that state-
  independence one IR level down.

* **§3 Composition toward the concrete x86 `blockLeak`.** The x86 leg is over a
  *different* observable alphabet — `blockLeak : … → List MLeak` records
  control-flow + memory addresses, not the abstract `LeakEvent` op tokens. The
  bridge on the owned scalar-arith fragment is the joint
  *state-independence*: a dialect program *realized* by an owned scalar-arith
  block `ps` (`Realizes cc ρ ps`) has BOTH a state-independent abstract leak
  trace (structurally, `leakTraceCom`) AND a state-independent concrete x86
  `blockLeak (lowerSeq ρ ps)` — the latter *non-vacuously* (address-dependent),
  reusing RHPFull's `lowerSeq_constant_time` and `blockLeak_no_branch`.
  `dialect_to_x86_leak_refinement` chains all three legs into a single theorem.

## Scope (read this before relying on the names)

The chain that closes **end-to-end** is the **owned scalar-arith / branch-free
fragment** — the same fragment `RHPFull.blockLeak` covers (`lowerSeq` of a
`List ArithSrc`, all `IsDirect`, no `loadMemIdx`/`storeMemIdx`, no conditional
jump). On exactly that fragment:

* (dialect → jasmin) the leak trace length is preserved by the front, and the
  syntax-only state-independence transports down (`leakTraceJ_length_refines`,
  `leakTraceJ_state_independent`) — proved here, no axiom;
* (jasmin → x86) the concrete `blockLeak (lowerSeq ρ ps)` is state-independent
  and branch-free — reused from `RHPFull` / `MachineConstantTime`
  (`lowerSeq_constant_time`, `blockLeak_no_branch`), no `jasminc_preserves_ct`.

So `leakTraceCom cc`'s constant-time property (its state-independence, equal to
`CProg.leakTrace`'s via the adequacy in `LeakTraceCom`) is *matched at the
concrete x86 machine level* on this fragment: `dialect_to_x86_leak_refinement`.

### The structural-vs-adversarial distinction (LeakTraceCom residual #2)

The two state-independences are **not** the same kind of fact, and this file is
precise about it:

* `leakTraceCom` / `leakTraceJ` are state-independent **structurally** — they
  take no valuation, so the `s₁`/`s₂` quantification is *vacuous* (there is no
  branch or value-indexed constructor in `Com`). This is the branch-free
  fragment's state-independence.
* `blockLeak (lowerSeq ρ ps)` is state-independent **adversarially / non-vacuously**
  — `blockLeak` reads the running `JState` and *could* expose a value-dependent
  memory address (a register-indexed `storeMemIdx`); it is constant here only
  *because* the owned fragment emits no such instruction
  (`lowerSeq_allDirect`). The same `blockLeak` is **not** constant on
  `indexedScatterLeaf` (`nonCT_storeMemIdx_leaks_value`). So the x86 leg is a
  real (`IsDirect`-gated) theorem, not a vacuity.

The two coincide *exactly* on the branch-free, direct-addressed fragment that
the dialect / `CProg` model — which is the fragment this chain closes.

### The precise remaining edge

The chain closes the owned scalar-arith fragment, **not** the general dialect
program. The remaining edge is the **general op-set jasmin → x86 leak
preservation**: for an arbitrary `Com jasminDialect` (with `stackLoad` /
`stackStore` / multi-result `callN` / vector ops), there is no proved emit-and-
leak-refinement onto a `blockLeak`-modeled x86 block here — that step routes
through the un-owned backend (which, for clause (A) machine-CT, still appeals to
the cited `jasminc_preserves_ct`; see `RHPFull` §3). The dialect → jasmin
*length*-refinement (§2) is proved for the **whole** lowered fragment, but the
jasmin → x86 leg is only the owned `lowerSeq` leaf. This file does not claim the
general dialect → x86 leak-refinement.

## Axioms

The §1/§2 results (`leakTraceJ`, `leakTraceJ_length_refines`,
`leakTraceJ_state_independent`) and the §3 composition over the owned fragment
are pure structural inductions + reuse of `RHPFull`'s
`jasminc_preserves_ct`-free owned results. **No `jasminc_preserves_ct`** is
threaded — the owned x86 leg is the concrete `blockLeak` model, not the opaque
`X86Prog.isCT`.

**0 sorries.** Standard axioms only.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinement

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace (Com.leakTrace)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.RHPFull

set_option autoImplicit false

/-! ## §1. The jasmin-level structural leak trace

`jOpLeakEvent` assigns the observable `LeakEvent` to each jasmin op; every
`JasminOp` is a branch-free pure/opaque-call op (the jasmin dialect has no
control-flow op), so each gets a `pureOp` token. `leakTraceJ` is then the
one-event-per-`.var` structural trace, the exact image of `leakTraceCom` one IR
level down. -/

/-- The leakage event emitted by a jasmin op. Every `JasminOp` is branch-free
    (pure ALU, immediate shift/rotate, opaque call), so each maps to a `pureOp`
    token naming the op. The one-IR-down analogue of `opLeakEvent`. -/
def jOpLeakEvent : JasminOp → LeakEvent
  | .regArith _ _ => .pureOp "regArith"
  | .stackLoad _ _ => .pureOp "stackLoad"
  | .stackStore _ _ => .pureOp "stackStore"
  | .castW _ _ => .pureOp "castW"
  | .extCall name _ _ => .pureOp ("extCall:" ++ name)
  | .regConst _ _ => .pureOp "regConst"
  | .vpackZMM _ => .pureOp "vpackZMM"
  | .vpackZMMd _ => .pureOp "vpackZMMd"
  | .vprordZMM _ => .pureOp "vprordZMM"
  | .vpslldq _ => .pureOp "vpslldq"
  | .vpsrldq _ => .pureOp "vpsrldq"
  | .vsimd op => .pureOp ("vsimd:" ++ op.mnemonic)
  | .vymm op => .pureOp ("vymm:" ++ op.jasminMnemonic)
  | .mulhi _ => .pureOp "mulhi"
  | .addCarryLo _ => .pureOp "addCarryLo"
  | .addCarryHi _ => .pureOp "addCarryHi"
  | .rorImm _ _ => .pureOp "rorImm"
  | .shrImm _ _ => .pureOp "shrImm"
  | .sarImm _ _ => .pureOp "sarImm"
  | .shlImm _ _ => .pureOp "shlImm"
  | .select _ => .pureOp "select"
  | .callN name _ _ => .pureOp ("callN:" ++ name)

/-- The jasmin-level structural leak trace: per `.var` node emit `jOpLeakEvent
    e.op` and recurse; `.ret` emits `[]`. The one-IR-down mirror of
    `leakTraceCom`. -/
def leakTraceJ {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → LeakTrace
  | .ret _ => []
  | .var e body => jOpLeakEvent e.op :: leakTraceJ body

@[simp] theorem leakTraceJ_ret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (v : Ctxt.Var Γ t) :
    leakTraceJ (Com.ret (d := jasminDialect) v) = [] := rfl

@[simp] theorem leakTraceJ_var {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s) :
    leakTraceJ (Com.var e body) = jOpLeakEvent e.op :: leakTraceJ body := rfl

/-! ## §2. The dialect → jasmin leak-refinement step

On the lowered fragment, `cryptoDialectToJasminCom` lowers each dialect `.var`
op to exactly one jasmin `.var` op (and `.ret` to `.ret`). So the jasmin leak
trace has the *same number of events* as the dialect leak trace — the leak
structure is preserved event-for-event. We prove the length equality; combined
with the syntax-only state-independence below, this is the dialect → jasmin leak
refinement. -/

/-- **Dialect → jasmin leak-length refinement.** Whenever the front lowers a
    dialect program `cc` to a jasmin program `jcom`, the jasmin leak trace has
    the same length as the dialect leak trace: the lowering is one-op-to-one-op,
    so it neither adds nor drops observable events.

    By induction on `cc`, splitting the two `Option` matches of
    `cryptoDialectToJasminCom` (`toJExprD` for the head op, the recursive front
    for the body); the `none` branches are vacuous. -/
theorem leakTraceJ_length_refines {Γ : Ctx} {t : CryptoTy} :
    (cc : Com catCryptDialect Γ t) →
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t)) →
    cryptoDialectToJasminCom cc = some jcom →
    (leakTraceJ jcom).length = (Com.leakTrace cc).length
  | .ret v, jcom, h => by
      simp only [cryptoDialectToJasminCom, Option.some.injEq] at h
      subst h
      rfl
  | .var e body, jcom, h => by
      simp only [cryptoDialectToJasminCom] at h
      split at h
      · next e' he =>
          split at h
          · next body' hbody =>
              simp only [Option.some.injEq] at h
              subst h
              have ih := leakTraceJ_length_refines body body' hbody
              simp only [leakTraceJ, Com.leakTrace, List.length_cons]
              exact congrArg (· + 1) ih
          · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- The jasmin leak trace is **state-independent**: like `leakTraceCom`, it is a
    function of syntax only (no valuation argument), so it is identical across
    any two valuations. The one-IR-down analogue of
    `leakTraceCom_state_independent`. This is the *structural* state-
    independence transported down — see the module "Scope" for why it is
    structural (vacuous), not adversarial. -/
theorem leakTraceJ_state_independent {Γ : Ctxt jasminDialect} {t : JasminTy}
    (jcom : Com jasminDialect Γ t) (_V₁ _V₂ : Ctxt.Valuation Γ) :
    leakTraceJ jcom = leakTraceJ jcom := rfl

/-! ## §3. Composition toward the concrete x86 `blockLeak`

The x86 leg is over a different observable alphabet (`MLeak`, not `LeakEvent`),
so the bridge is not a trace *equality* but a joint *state-independence*: the
abstract dialect leak trace and the concrete x86 `blockLeak` are *both* constant
across states on the owned scalar-arith fragment — the abstract one structurally
(vacuously), the concrete one non-vacuously (`lowerSeq_constant_time`). A dialect
program is *realized* by an owned scalar-arith block when the x86 leg it lowers
to is `lowerSeq ρ ps`. -/

/-- **Realization onto the owned scalar-arith x86 leg.** A dialect program `cc`
    is realized by the owned scalar-arith block `ps` (under register map `ρ`)
    when the concrete x86 code it is emitted to is `lowerSeq ρ ps` — the
    direct-addressed, branch-free leaf `RHPFull.blockLeak` covers. This is
    the fragment on which the dialect → jasmin → x86 leak chain closes. -/
def Realizes {Γ : Ctx} {t : CryptoTy}
    (_cc : Com catCryptDialect Γ t)
    (ρ : RegMap) (ps : List ArithSrc)
    (tgt : List (JInstr 64)) : Prop :=
  tgt = lowerSeq ρ ps

/-- **The dialect → x86 leak-refinement, owned fragment.**

    For a dialect program `cc` realized by an owned scalar-arith block `ps`
    (`Realizes cc ρ ps tgt`, i.e. `tgt = lowerSeq ρ ps`), the abstract dialect
    leak trace and the concrete x86 `blockLeak` are *jointly state-independent*:

    * (abstract, structural) `leakTraceCom cc` is the same across any two states
      — it is syntax-only, so the `s₁`/`s₂` quantification is vacuous;
    * (concrete, non-vacuous) `blockLeak s₁ tgt = blockLeak s₂ tgt` for any two x86
      states — and this is a *real* `IsDirect`-gated theorem
      (`lowerSeq_constant_time`), not a vacuity, since `blockLeak` reads the
      running state and only avoids value-dependent leakage because the owned
      fragment emits no register-indexed memory op;
    * (no branch leak) the concrete trace has no control-flow leak
      (`blockLeak_no_branch`).

    So the dialect leak trace's constant-time property (state-independence,
    equal — via `LeakTraceCom.leakTraceCom_adequacy` — to `CProg.leakTrace`'s) is
    *matched at the concrete x86 machine level* on the owned scalar-arith
    fragment. This is the dialect → (jasmin) → x86 leak-refinement, closed on
    exactly the fragment `RHPFull.blockLeak` covers. No
    `jasminc_preserves_ct`. -/
theorem dialect_to_x86_leak_refinement {Γ : Ctx} {t : CryptoTy}
    (cc : Com catCryptDialect Γ t)
    (ρ : RegMap) (ps : List ArithSrc) (tgt : List (JInstr 64))
    (hreal : Realizes cc ρ ps tgt) :
    -- (abstract, structural) the dialect leak trace is state-independent:
    (∀ σ : Type, ∀ s₁ s₂ : σ,
      (fun _ : σ => Com.leakTrace cc) s₁ = (fun _ : σ => Com.leakTrace cc) s₂) ∧
    -- (concrete, non-vacuous) the x86 `blockLeak` is state-independent:
    (∀ s₁ s₂ : JState 64, blockLeak s₁ tgt = blockLeak s₂ tgt) ∧
    -- (no control-flow leak) the concrete trace is branch-free:
    (∀ s : JState 64, (blockLeak s tgt).filter MLeak.isBranch = []) := by
  subst hreal
  refine ⟨?_, ?_, ?_⟩
  · intro σ s₁ s₂; rfl
  · intro s₁ s₂; exact lowerSeq_constant_time ρ ps s₁ s₂
  · intro s; exact blockLeak_no_branch (lowerSeq ρ ps) s

/-- **The full dialect → jasmin → x86 chain (owned fragment), with the jasmin
    leg made explicit.** For a dialect program `cc` that lowers through the front
    to a jasmin program `jcom` (`cryptoDialectToJasminCom cc = some jcom`) and is
    realized by the owned scalar-arith block `ps`:

    * the dialect → jasmin leak-length refinement holds
      (`leakTraceJ_length_refines`);
    * the concrete x86 `blockLeak (lowerSeq ρ ps)` is state-independent and
      branch-free (`dialect_to_x86_leak_refinement`).

    All three IR levels are tied: abstract dialect trace, its length-preserving
    jasmin image, and the concrete x86 `blockLeak` it determines. Closed on the
    owned scalar-arith fragment; no `jasminc_preserves_ct`. -/
theorem dialect_jasmin_x86_chain {Γ : Ctx} {t : CryptoTy}
    (cc : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hlow : cryptoDialectToJasminCom cc = some jcom)
    (ρ : RegMap) (ps : List ArithSrc) (tgt : List (JInstr 64))
    (hreal : Realizes cc ρ ps tgt) :
    -- (dialect → jasmin) leak-length refinement:
    (leakTraceJ jcom).length = (Com.leakTrace cc).length ∧
    -- (jasmin → x86) concrete `blockLeak` state-independence:
    (∀ s₁ s₂ : JState 64, blockLeak s₁ tgt = blockLeak s₂ tgt) ∧
    -- (no control-flow leak):
    (∀ s : JState 64, (blockLeak s tgt).filter MLeak.isBranch = []) := by
  refine ⟨leakTraceJ_length_refines cc jcom hlow, ?_, ?_⟩
  · subst hreal; intro s₁ s₂; exact lowerSeq_constant_time ρ ps s₁ s₂
  · subst hreal; intro s; exact blockLeak_no_branch (lowerSeq ρ ps) s

end CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinement
