/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.LowCTLeakTraceDef
import CatCrypt.Crypto.SecureCompilation.Framework
import CatCrypt.Crypto.Jasmin.BignumExec
import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# UnifiedTrace: One Trace Alphabet for the Whole Pipeline

One event alphabet into which every stage in `SecureCompilation/` projects its
observables.  This file defines the alphabet and the embeddings for the stages
that admit a total, computable projection (CryptoSSA leakage, `BignumExec`,
Jasmin `Cmd`); the stages still lacking an embedding are listed under
"What's NOT done" below.

## Why a unified trace?

Robust hyperproperty preservation (RHP), SCIO*'s RrHP, Almeida et al.'s
leakage NI, and Barthe et al.'s constant-time framework all
quantify over **traces**. To state a single RHP theorem across the
CatCrypt pipeline (`LowCT → CryptoSSA → VIR → Jasmin source →
{Jasmin asm, MLIR/LLVM, native Rust}`), every stage needs to project
its observables into one alphabet.

Today the codebase has *several* incompatible trace shapes:

* `SSALeakage.LeakTrace = List LeakEvent` — CryptoSSA constant-time
  leakage; structural, value-erased.
* `Framework.CompilerCorrect` and `CompilerRHL` work with `ITreeN n E α`
  where `E : EventSig` already supplies an adversary-visible event
  signature. There's no explicit "trace type"; equality of `ITreeN`
  values *is* equality of observables modulo the chosen handler.
* `NIPreservation.LeakageNI` quantifies over an `R : α → α → Prop` on
  inputs and demands SPComp equality — observable = the whole `SPComp`.
* `JasminSem.jasminSem : Cmd → RustState → RustState → Prop` is a pure
  big-step relation; no event log emitted.
* `BignumExec` is a state-transforming functional interpreter; again no
  explicit trace, but it touches a byte-level `Mem`, which downstream
  RHP work will want to expose as a memory-access pattern.

## The unified alphabet

```
Event E LeakTy MemTy
  | ret (out : Σ α : Type, α)            -- terminal return value
  | sample (e : E.Event) (r : E.Resp e)  -- adversary-visible / oracle event
  | leak (l : LeakTy)                    -- side-channel observation
  | memOp (m : MemTy)                    -- memory load/store
```

`UnifiedTrace E LeakTy MemTy = List (Event ...)`.

Why each constructor? — by stage:

| Stage                  | Uses                                             |
|------------------------|--------------------------------------------------|
| CryptoSSA (SSALeakage) | `.leak (LeakEvent)` for every `letBind` op,     |
|                        | `.sample _ ()` if SPTree-level sample,           |
|                        | `.ret ⟨t.denote, v⟩` at the ret leaf.            |
| Framework (ITreeN)     | `.sample (e, r)` per `vis`, `.ret` at done.      |
| NIPreservation         | the relation `R` is on prefixes of `UnifiedTrace`,|
|                        | recovering `LeakageNI` when the `LeakTy`-projection|
|                        | is constant.                                     |
| Jasmin (sem / BignumExec)| `.memOp` per load/store, `.ret` at terminal     |
|                        | state (BignumExec); `.leak (.pureOp _)` per      |
|                        | InstrR (JasminSem structural).                   |

The type parameters `LeakTy` and `MemTy` are *open*: each pipeline stage
instantiates them with its own observable shape (`LeakEvent`,
`Mem.AccessEvent`, …). This keeps the inductive *one* type family while
letting the per-stage projections be total functions.

## Alternative we considered (and rejected)

`SPComp` itself is *almost* a unified trace already: it's the joint
observable of every verified-middle stage. We considered redefining
`UnifiedTrace = SPComp` and providing only embeddings into it.

Why this draft uses a fresh inductive instead:
1. SPComp erases sequencing — two programs with the same denotation but
   different leakage traces become indistinguishable. CT/leakage RHP
   needs to *see* the per-step leakage.
2. The Jasmin back-end produces an operational byte-level trace
   (`Mem.store64`, `Mem.load64`); SPComp has no slot for this.
3. SCIO* / RHP literature uniformly assumes a *list* of events.

The right relationship is `embedSPComp : SPComp → UnifiedTrace`: the trace
consisting of one `.sample` per `SPComp.sample` plus one `.ret` at the leaf.
That embedding is NOT implemented — no `SPComp.toUnifiedTrace` exists in this
file or elsewhere in the tree; only the specification above is recorded.

## What's done in this file

1. The inductive `Event` and the abbrev `UnifiedTrace`.
2. `LeakTrace.toUnifiedTrace` — total, computable.
3. Projection back: `UnifiedTrace.toLeakTrace`.
7. **A1.2 (now landed)**: `BignumExec.toUnifiedTrace`. Picks `MemTy :=
   MemAccess` (load/store summary), threads the existing `BignumExec`
   interpreter, and emits one `.memOp` per memory access. Smoke-test on
   `BignumExec.smokeBody` produces exactly two events: a load followed
   by a store. The `BignumExec.lean` file is *not* modified — we add a
   pure tracer here that mirrors the structure of `bignumExec`.
8. **A1.3 (now landed)**: `JasminSem.Cmd.leakTrace` and
   `JasminSem.Cmd.toUnifiedTrace`. Structural per-instruction trace
   (one `pureOp` event per top-level `InstrR`), not the dynamic
   relation: branch decisions in `Cif`/`Cwhile` are not encoded —
   the verified pipeline emits straight-line code where structural ≡
   dynamic. Smoke test `jasmin_smoke_leak` over `BignumExec.smokeBody`,
   round-trip `Cmd.toUnifiedTrace_leak_proj`, and the cross-stage
   length lemma `leakTrace_length_eq_cmd_length` are all closed.
   Discharging the dynamic version (encoding actual branch decisions)
   would require the writer-monad refactor of `jasminSem` originally
   suggested for A1.3; that is a separate, larger task.

## What's NOT done (handed off)

* Lift `CompilerCorrect` to an equality on `UnifiedTrace`s (one direction
  is trivial — `f x = g x` ⇒ traces match — but the converse needs a
  determinism argument on the SPComp's sample events).
* `RHP_unified` statement.
* `JasminSem.toUnifiedTrace` (A1.3): needs a refactor of `jasminSem`
  into either an executable big-step or a Prop predicate parametrised
  by a trace. See the stub docstring below.
* Dependent `ret`: the `Σ α : Type, α` packaging works for embedding but
  may be inconvenient for monomorphic equational reasoning. A future
  refactor may parameterise `Event` by a fixed `RetTy`.

**0 axioms**, **0 sorry** (A1.3 closed structurally 2026-04-29; the
dynamic refactor of `jasminSem` to a writer-monad form remains as
follow-up but is not blocking RHP-1 against the verified-middle
straight-line subset).
-/

namespace CatCrypt.Crypto.SecureCompilation.UnifiedTrace

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open UCMonad.ITreeNUC
open UCMonad.StateTITreeN
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

set_option autoImplicit false

/-! ## §1. The unified alphabet -/

/-- One event from the unified observable alphabet.

* `ret v` — terminal return. The output value is wrapped in a `Σ`-type
  so a single `Event` family can carry results of any type (CryptoSSA's
  `t.denote`, Jasmin's `BitVec 64`, etc.).
* `sample e r` — an adversary-visible event with response. Maps to
  `ITreeN.vis` and to `SPComp.sample`.
* `leak l` — a side-channel observation. The shape `LeakTy` is left
  open so stages can plug in `LeakEvent`, a memory-access summary, etc.
* `memOp m` — a byte-level memory access. `MemTy` open for the same
  reason. -/
inductive Event (E : EventSig) (LeakTy MemTy : Type) where
  | ret (out : Σ α : Type, α) : Event E LeakTy MemTy
  | sample (e : E.Event) (r : E.Resp e) : Event E LeakTy MemTy
  | leak (l : LeakTy) : Event E LeakTy MemTy
  | memOp (m : MemTy) : Event E LeakTy MemTy

/-- A unified trace is a finite list of events. Finite because every
verified stage in the pipeline produces a bounded computation (CryptoSSA
has no loops; ITreeN is `Nat`-indexed; Jasmin's verified subset rejects
`Cwhile`/`Cfor`). -/
abbrev UnifiedTrace (E : EventSig) (LeakTy MemTy : Type) :=
  List (Event E LeakTy MemTy)

/-! ## §2. CryptoSSA → UnifiedTrace

The verified middle's structural leakage trace embeds directly: each
`pureOp`/`sampleOp` becomes a `.leak`, terminated by a `.ret`.

We pick `MemTy := Empty` (no byte memory at this stage) and `E :=
emptyEvSig` (no adversary events at this stage; sampling shows up as a
`.leak (.sampleOp)` in the structural trace, matching how `LeakEvent`
already classifies it). -/

/-- Lift `LeakEvent` (CryptoSSA's structural side-channel observation)
into a single unified event. -/
def LeakEvent.toEvent {E : EventSig} {MemTy : Type}
    (l : LeakEvent) : Event E LeakEvent MemTy :=
  .leak l

/-- Embed a CryptoSSA `LeakTrace` into the unified alphabet. Total,
computable; preserves order. -/
def LeakTrace.toUnifiedTrace {E : EventSig} {MemTy : Type}
    (t : LeakTrace) : UnifiedTrace E LeakEvent MemTy :=
  t.map (LeakEvent.toEvent (E := E) (MemTy := MemTy))

@[simp] theorem LeakTrace.toUnifiedTrace_nil
    {E : EventSig} {MemTy : Type} :
    LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) [] = [] := rfl

@[simp] theorem LeakTrace.toUnifiedTrace_cons
    {E : EventSig} {MemTy : Type} (l : LeakEvent) (t : LeakTrace) :
    LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) (l :: t)
      = LeakEvent.toEvent (E := E) (MemTy := MemTy) l ::
        LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) t :=
  rfl

/-! ## §3. Projections back to per-stage traces

These define which observables each stage can see. The CryptoSSA
projection drops `.sample`/`.memOp` (the stage doesn't see them) and
the terminal `.ret` (CryptoSSA's `LeakTrace` is a *prefix* of the
unified trace), keeping only `.leak` events. -/

/-- Project a unified trace down to a CryptoSSA `LeakTrace`. Total. -/
def UnifiedTrace.toLeakTrace {E : EventSig} {MemTy : Type} :
    UnifiedTrace E LeakEvent MemTy → LeakTrace
  | [] => []
  | .leak l :: rest => l :: UnifiedTrace.toLeakTrace rest
  | _ :: rest => UnifiedTrace.toLeakTrace rest

@[simp] theorem UnifiedTrace.toLeakTrace_nil
    {E : EventSig} {MemTy : Type} :
    UnifiedTrace.toLeakTrace (E := E) (MemTy := MemTy) [] = [] := rfl

@[simp] theorem UnifiedTrace.toLeakTrace_leak_cons
    {E : EventSig} {MemTy : Type} (l : LeakEvent)
    (rest : UnifiedTrace E LeakEvent MemTy) :
    UnifiedTrace.toLeakTrace (.leak l :: rest)
      = l :: UnifiedTrace.toLeakTrace rest := rfl

/-- Round-trip: lifting a `LeakTrace` then projecting back is the
identity. -/
theorem LeakTrace.toUnifiedTrace_toLeakTrace
    {E : EventSig} {MemTy : Type} (t : LeakTrace) :
    UnifiedTrace.toLeakTrace
        (LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) t) = t := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    show UnifiedTrace.toLeakTrace (LeakEvent.toEvent l ::
            LeakTrace.toUnifiedTrace (E := E) (MemTy := MemTy) t) = l :: t
    simp only [UnifiedTrace.toLeakTrace, List.map_cons,
               LeakEvent.toEvent, ih]

/-! ## §4b. BignumExec → UnifiedTrace (Track A1.2)

For pipeline (2) we want a memory-access trace produced by the bignum
interpreter. We pick a `MemAccess` summary type with two constructors
(`load addr` and `store addr value`), instantiate `MemTy := MemAccess`,
and walk the instruction list mirroring `bignumExec`'s structure. We
do **not** modify `BignumExec.lean`; the tracer here is a pure side
function that consumes the same `BignumState` and `InstrR` shapes.

This covers the straight-line subset (no `Ccall`/`Cif`/`Cwhile`). The
Ccall-aware extension would mirror `bignumExecFuel` and emit the
nested callee's trace inline; that's a small extension we leave for
follow-up. -/

/-- Memory-access summary — one entry per byte-level access at the
`load64Mem`/`storeMem` granularity (one event per 64-bit access, not
per byte). Sufficient for the trace of every bignum routine in
`S2NBignumSSA.lean`. -/
inductive MemAccess where
  /-- 64-bit memory load from address `addr`. -/
  | load (addr : UInt64) : MemAccess
  /-- 64-bit memory store of `value` to address `addr`. -/
  | store (addr : UInt64) (value : UInt64) : MemAccess
  deriving DecidableEq, Repr, Inhabited

namespace BignumExec
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec

/-- Static memory-access summary for a `PExpr`: each `Pload` emits a
load event (assuming address resolution succeeds; on failure no event
is emitted). Reads of registers (`Pvar`) and constants (`Pconst`)
produce no memory traffic. -/
def pexprMemOps (s : BignumState) : PExpr → List MemAccess
  | .Pconst _ => []
  | .Pvar _ => []
  | .Pload .U64 base off =>
      match resolveAddr s base off with
      | some addr => [MemAccess.load addr]
      | none      => []
  | .Papp2 _ a b => pexprMemOps s a ++ pexprMemOps s b
  | _ => []

/-- Static memory-access summary for an `InstrR`. Loads from rhs
expressions are emitted first (in evaluation order); a store to
`Lmem` is emitted after.

For `Copn` we walk the argument list. `Cif`/`Cfor`/`Cwhile`/`Ccall`
are not produced by `LowCTToJasmin` for the bignum subset and are
treated here as producing no events. -/
def instrMemOps (s : BignumState) : InstrR → List MemAccess
  | .Cassgn (.Lvar _) _ _ rhs => pexprMemOps s rhs
  | .Cassgn (.Lmem .U64 base off) _ _ rhs =>
      let loads := pexprMemOps s rhs
      let stores : List MemAccess :=
        match evalPExpr s rhs, resolveAddr s base off with
        | some w, some addr => [MemAccess.store addr (UInt64.ofNat w.toNat)]
        | _, _              => []
      loads ++ stores
  | .Copn _ _ _ args => args.flatMap (pexprMemOps s)
  | _ => []

/-- Run the interpreter and the tracer in lockstep. On each instruction
we accumulate the static memory-access summary using the *pre*-state
(so addresses are resolved consistently with `evalPExpr`'s reads), then
advance the interpreter to obtain the post-state. Returns
`some (trace, finalState)` on successful execution; `none` if any
instruction fails (matches `bignumExec`'s shape). -/
def bignumExecTrace : List InstrR → BignumState →
    Option (List MemAccess × BignumState)
  | [],      s => some ([], s)
  | i :: is, s =>
      let evs := instrMemOps s i
      match execInstr s i with
      | some s' =>
          (bignumExecTrace is s').map (fun (rest, sf) => (evs ++ rest, sf))
      | none    => none

/-- **A1.2 entry point**: produce a `UnifiedTrace` from a bignum body
and an initial state. On success the trace is the concatenation of
per-instruction memory accesses (as `Event.memOp`) terminated by
`Event.ret ⟨BignumState, finalState⟩`. On failure (interpreter aborts)
we emit a single `.ret` of the *initial* state — distinguishable from
success because no `.memOp`s precede it. -/
def toUnifiedTrace (body : List InstrR) (s : BignumState) :
    UnifiedTrace emptyEvSig LeakEvent MemAccess :=
  match bignumExecTrace body s with
  | some (trace, sf) =>
      trace.map (fun m => Event.memOp m) ++
        [Event.ret ⟨BignumState, sf⟩]
  | none =>
      [Event.ret ⟨BignumState, s⟩]

end BignumExec

/-! ## §4c. Cmd → UnifiedTrace (Track A1.3)

`jasminSem : Cmd → RustState → RustState → Prop` is a Prop relation, so
it carries no trace itself. But for the verified-middle subset we don't
need the dynamic relation — the leak trace is a *structural* property
of the program AST: each `InstrR` contributes one leak event, ordered
left-to-right.

The structural trace is total, computable, and pulls back the LowCT
side's `LowCTLeakTrace.LowCT.leakTrace` view. It does not encode
branch decisions in `Cif`/`Cwhile` (those depend on dynamic state and
require the executable refactor option in the original A1.3 proposal).
For the constant-time straight-line subset that the verified pipeline
emits, the structural trace is exactly the right granularity. -/

namespace JasminSem
open CatCrypt.Crypto.Jasmin

/-- One leak event per `InstrR` shape. Mirrors `LowCTLeakTrace.LowCT.leakTrace`'s
    structural form — each instruction contributes a single classified
    `pureOp` tag. Useful for stating compatibility lemmas with the LowCT
    side at the AST level. -/
def InstrR.leakEvent : InstrR → LeakEvent
  | .Cassgn _ _ _ _   => LeakEvent.pureOp "Cassgn"
  | .Copn _ _ _ _     => LeakEvent.pureOp "Copn"
  | .Cif _ _ _        => LeakEvent.pureOp "Cif"
  | .Cfor _ _ _       => LeakEvent.pureOp "Cfor"
  | .Cwhile _ _ _     => LeakEvent.pureOp "Cwhile"
  | .Ccall _ _ _ _    => LeakEvent.pureOp "Ccall"

/-- Structural leak trace of a Jasmin `Cmd`: one event per top-level
    `InstrR`, in source order. Subterms inside `Cif`/`Cwhile`/`Cfor`
    bodies are not unrolled here — they show up only as the parent's
    classification tag. The constant-time verified subset is straight-line
    so this matches the dynamic leak trace exactly on those programs. -/
def Cmd.leakTrace : Cmd → LeakTrace :=
  fun body => body.map InstrR.leakEvent

@[simp] theorem Cmd.leakTrace_nil : Cmd.leakTrace [] = [] := rfl

@[simp] theorem Cmd.leakTrace_cons (i : InstrR) (is : Cmd) :
    Cmd.leakTrace (i :: is)
      = InstrR.leakEvent i :: Cmd.leakTrace is := rfl

theorem Cmd.leakTrace_append (xs ys : Cmd) :
    Cmd.leakTrace (xs ++ ys)
      = Cmd.leakTrace xs ++ Cmd.leakTrace ys := by
  simp [Cmd.leakTrace, List.map_append]

/-- A1.3 entry point: structural unified trace of a Jasmin `Cmd`.
    Each instruction emits one `.leak`, terminated by a single `.ret`
    of `Unit` (the trace is state-erased — the dynamic state lives in
    `jasminSem`'s relation). The `MemTy` is `Empty` since `RustState`
    has no byte memory; the bignum-byte-level memory trace is provided
    separately by `BignumExec.toUnifiedTrace` over `BignumState`. -/
def Cmd.toUnifiedTrace (body : Cmd) : UnifiedTrace emptyEvSig LeakEvent Empty :=
  LeakTrace.toUnifiedTrace (E := emptyEvSig) (MemTy := Empty)
      (Cmd.leakTrace body)
    ++ [Event.ret ⟨Unit, ()⟩]

@[simp] theorem Cmd.toUnifiedTrace_leak_proj (body : Cmd) :
    UnifiedTrace.toLeakTrace (Cmd.toUnifiedTrace body) = Cmd.leakTrace body := by
  unfold Cmd.toUnifiedTrace
  -- Same pattern as `CProg.toUnifiedTrace_leak_proj`: list-append destructures
  -- into the leak prefix and the singleton `.ret`.
  induction Cmd.leakTrace body with
  | nil => rfl
  | cons l t ih =>
    show l :: UnifiedTrace.toLeakTrace
              (LeakTrace.toUnifiedTrace t ++ [Event.ret ⟨Unit, ()⟩]) = l :: t
    rw [ih]

end JasminSem

/-! ## §8. BignumExec smoke test (Track A1.2)

`BignumExec.smokeBody` is a 2-instruction body: load `*(ap + 0)` into
register `t`, then store `t` to `*(op + 0)`. With `BignumExec.smokeInit`
we have `ap = 16`, `op = 100`, and `*16 = 0x42`. So the expected
trace is:

* `Event.memOp (load 16)` — from the `Pload` in instruction 1
* `Event.memOp (store 100 0x42)` — from the `Lmem` in instruction 2
* `Event.ret ⟨BignumState, finalState⟩` — the terminal value

We check the prefix (the two `.memOp`s) here; the final `.ret` carries
a `BignumState` and isn't `DecidableEq`, so we project onto the memOp
prefix to keep the test `decide`-friendly. -/

/-- Helper: extract the `.memOp` payloads from a unified trace
projected over `MemAccess`. The result is the list of memory accesses
in order. -/
def UnifiedTrace.toMemAccessTrace :
    UnifiedTrace emptyEvSig LeakEvent MemAccess →
    List MemAccess
  | [] => []
  | Event.memOp m :: rest => m :: UnifiedTrace.toMemAccessTrace rest
  | _ :: rest => UnifiedTrace.toMemAccessTrace rest

/-- The expected memory-access trace for the bignum smoke body: one
load from address 16, one store of 0x42 to address 100. -/
def expectedSmokeMemTrace : List MemAccess :=
  [.load 16, .store 100 0x42]

/-- Smoke test: the bignum smoke body produces exactly the expected
memory-access trace. Closed by `native_decide`. -/
theorem bignum_smoke_memtrace :
    UnifiedTrace.toMemAccessTrace
        (BignumExec.toUnifiedTrace
          CatCrypt.Crypto.Jasmin.BignumExec.smokeBody
          CatCrypt.Crypto.Jasmin.BignumExec.smokeInit)
      = expectedSmokeMemTrace := by
  native_decide

/-! ## §9. JasminSem.Cmd.toUnifiedTrace smoke test (Track A1.3)

`BignumExec.smokeBody` is a 2-instruction body (Cassgn-load, Cassgn-store)
both of shape `Cassgn`. The structural Jasmin trace is therefore two
`pureOp "Cassgn"` events followed by the terminal `.ret ⟨Unit, ()⟩`. -/

/-- Expected structural Jasmin leak trace of the bignum smoke body. -/
def expectedJasminSmokeLeak : LeakTrace :=
  [LeakEvent.pureOp "Cassgn", LeakEvent.pureOp "Cassgn"]

/-- A1.3 smoke test: structural trace of `smokeBody` matches the expected
    two-Cassgn shape. Closed by `rfl` on definitional unfolding. -/
theorem jasmin_smoke_leak :
    JasminSem.Cmd.leakTrace
        CatCrypt.Crypto.Jasmin.BignumExec.smokeBody
      = expectedJasminSmokeLeak := rfl

/-! ## §10. Cross-stage compatibility (RHP-1 entry point)

The whole point of a unified trace is to compare per-stage traces
against each other. Here is the most basic compatibility shape: for
the *Jasmin-side image* of a LowCT's translation, the structural
Jasmin leak trace projects to the same length as the LowCT's
top-level instruction count. (A finer-grained per-event mapping —
matching `RCall ↔ Ccall`, `RIfNz ↔ Cif`, etc. — is the next step in
the asymmetric back-translation track.) -/

theorem leakTrace_length_eq_cmd_length
    (body : CatCrypt.Crypto.Jasmin.Cmd) :
    (JasminSem.Cmd.leakTrace body).length = body.length := by
  simp [JasminSem.Cmd.leakTrace]

/-! ## §11. LowCT ↔ Jasmin trace correspondence (Track A1.4)

The structural Jasmin leak trace of `toJasminCmd c` is determined
exactly by `c`'s syntax: each LowCT constructor expands to a fixed
multiset of Jasmin `InstrR`s with known classification tags.

We give the closed-form answer as `LowCT.toJasminLeakTrace`, and
prove the bridge `Cmd.leakTrace (toJasminCmd c) = LowCT.toJasminLeakTrace c`.
This is the source-side companion to the Jasmin-side
`Cmd.toUnifiedTrace_leak_proj` round-trip from §4c — together they let
us state and prove RHP-2 obligations as structural facts about the
syntactic translation, before any dynamic reasoning is needed. -/

namespace JasminSem
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT

/-- Closed-form structural Jasmin leak trace produced by `toJasminCmd c`.
    Each clause matches `toJasminCmd`'s emitted instruction shape:
    * `RSkip`: empty list.
    * `RSeq`: concatenation.
    * `RLetZero`/`RLetU64Zero`: one `Cassgn` for the zero-init, then body.
    * `RScalarSet`: one `Cassgn` (for the immediate).
    * `RCall`: one `Ccall`.
    * `RCloneCall`: one `Copn` (the clone) followed by one `Ccall`.
    * `RIfNz`: one `Cif` (the inner branch traces are not unrolled here —
      the LowCT-side `LowCTLeakTrace.LowCT.leakTrace` over-approximates
      them as the union; the Jasmin AST keeps them inside the `Cif`).
    * `RWhileNz`: one `Cwhile`.
    * `RFor x n body`: static unrolling — `n` repetitions of
      `[Cassgn] ++ toJasminLeakTrace body`, mirroring `unrollForJ` at the
      Jasmin level (see `LowCTToJasmin.toJasminCmd` and `forBodyN`).
    * `RLimbStore`: one `Copn` (the `STORE64` oracle). -/
def LowCT.toJasminLeakTrace : LowCT → LeakTrace
  | .RSkip                            => []
  | .RSeq c1 c2                       =>
      LowCT.toJasminLeakTrace c1 ++ LowCT.toJasminLeakTrace c2
  | .RLetZero _ _ body                =>
      LeakEvent.pureOp "Cassgn" :: LowCT.toJasminLeakTrace body
  | .RLetU64Zero _ body               =>
      LeakEvent.pureOp "Cassgn" :: LowCT.toJasminLeakTrace body
  | .RScalarSet _ _                   => [LeakEvent.pureOp "Cassgn"]
  | .RCall _ _ _                      => [LeakEvent.pureOp "Ccall"]
  | .RCallSwap _ _ _ _                =>
      -- Lowered as two sequential Ccalls (see LowCTToJasmin.RCallSwap arm).
      [LeakEvent.pureOp "Ccall", LeakEvent.pureOp "Ccall"]
  | .RCloneCall _ _ _ _ _ _           =>
      [LeakEvent.pureOp "Copn", LeakEvent.pureOp "Ccall"]
  | .RIfNz _ _ _                      => [LeakEvent.pureOp "Cif"]
  | .RWhileNz _ _                     => [LeakEvent.pureOp "Cwhile"]
  | .RFor _ n body                    =>
      -- Static unrolling: each iteration emits a `Cassgn` (the loop counter
      -- write) plus the body's structural trace.  Repeated `n` times.
      let bodyTrace := LowCT.toJasminLeakTrace body
      let rec loop : Nat → LeakTrace
        | 0     => []
        | k + 1 => loop k ++ (LeakEvent.pureOp "Cassgn" :: bodyTrace)
      loop n
  -- Stage 1a (2026-07-01): the runtime loop is rejected by `toJasminCmd`
  -- (foldNode leaf → `[]`), so its structural leak trace is empty.  A real
  -- runtime-count trace lands with the A2–A5 runtime-loop backend.
  | .RForRuntime _ _ _                => []
  | .RLimbStore _ _ _                 => [LeakEvent.pureOp "Copn"]
  | .RLimbStoreExpr _ _ _             => [LeakEvent.pureOp "Copn"]
  -- Phase F/G/H/L/M (2026-05-03): match `LowCTToJasmin.toJasminCmd`.
  -- RAsmOp / RSelect → single `Copn`.
  -- RCallN          → single `Ccall`.
  -- RAssert         → empty (no Jasmin emission).
  -- RBlock          → recurse on body.
  | .RAsmOp _ _ _                     => [LeakEvent.pureOp "Copn"]
  | .RCallN _ _ _                     => [LeakEvent.pureOp "Ccall"]
  | .RSelect _ _ _ _                  => [LeakEvent.pureOp "Copn"]
  | .RAssert _                        => []
  | .RBlock body                      => LowCT.toJasminLeakTrace body
  -- Phase C: RFnDef inlines body++cont; RFnCall emits a single `Ccall`.
  | .RFnDef _ _ _ body cont           =>
      LowCT.toJasminLeakTrace body ++ LowCT.toJasminLeakTrace cont
  | .RFnCall _ _ _                    => [LeakEvent.pureOp "Ccall"]
  -- Phase I (2026-05-03): tuple component store/load lowers to `[]`.
  | .RTupleStore _ _ _                => []
  | .RTupleLoad _ _ _                 => []
  -- Phase Ext (2026-05-12/14): toJasminCmd routes `RBytesSlice` to [].
  | .RBytesSlice _ _ _ _              => []
  -- Phase RND (2026-05-30, #261): the dynamic-index array store/load and the
  -- runtime-scalar SExpr assignment now emit REAL `Pvar`-indexed
  -- `Laset`/`Pget`/`Cassgn` jasmin (needed for the safegcd-62 limb vectors and
  -- the ML-DSA rounding leaves) instead of erasing to `[]`.  The structural
  -- leak trace therefore carries the emitted instruction's classification tag:
  --   * `RArrStore` lowers to one `Cassgn` (a `Laset` store) — both the U64
  --     and the narrowing-cast U32 branch are a single `Cassgn`.
  --   * `RArrLoad` lowers to one `Cassgn` (a `Pget` load) — likewise both width
  --     branches are a single `Cassgn`.
  --   * `RScalarSetExpr x e` lowers via `sexprSetExprCmd`: a top-level widening
  --     high-multiply (`SMulHiU`/`SMulHiS`) becomes the multi-output `#MULX` /
  --     `#IMUL` intrinsic — a single `Copn`; every other `SExpr` becomes a
  --     single nested-arithmetic `Cassgn`.
  -- A dynamic index is a `Pvar` read inside the instruction, so the instruction
  -- is NOT provably constant-time — consistent with the #229 decision that
  -- `jasminCTSafe` rejects these arms.  The structural leak trace here records
  -- only the instruction-shape tag (one event per `InstrR`); the value-level
  -- index leak is captured at the CT-analysis layer, not at this AST granularity.
  | .RScalarSetExpr _ e               =>
      match e with
      | .SMulHiU _ _ => [LeakEvent.pureOp "Copn"]
      | .SMulHiS _ _ => [LeakEvent.pureOp "Copn"]
      | _            => [LeakEvent.pureOp "Cassgn"]
  | .RArrLoad _ _ _                   => [LeakEvent.pureOp "Cassgn"]
  | .RArrStore _ _ _                  => [LeakEvent.pureOp "Cassgn"]
  -- Phase DD (2026-05-28): literal-index variants lower to a single
  -- `Cassgn` (Pget/Laset); pure op, no memory event at this layer.
  | .RArrLoadLit _ _ _                => [LeakEvent.pureOp "Cassgn"]
  | .RArrStoreLit _ _ _               => [LeakEvent.pureOp "Cassgn"]
  -- Phase E2 (2026-05-29): dst-threaded leaf call lowers to a single
  -- `Ccall` (same as `RCall`).
  | .RCallDstThreaded _ _ _           => [LeakEvent.pureOp "Ccall"]

/-- **A1.4 bridge**: the structural Jasmin leak trace of a translated
    LowCT is exactly the closed form `LowCT.toJasminLeakTrace`.

    Proof: induction on `c`. Each case unfolds `toJasminCmd` to a
    concrete `Cmd` shape, which `Cmd.leakTrace` then maps event-for-event
    to a known `LeakEvent` list — the same list `toJasminLeakTrace`
    produces by syntactic dispatch. -/
theorem Cmd.leakTrace_toJasminCmd (c : LowCT) :
    Cmd.leakTrace (toJasminCmd c) = LowCT.toJasminLeakTrace c := by
  induction c with
  | RSkip => rfl
  | RSeq c1 c2 ih1 ih2 =>
    simp [toJasminCmd_RSeq, Cmd.leakTrace_append, ih1, ih2,
          LowCT.toJasminLeakTrace]
  | RLetZero x t body ih =>
    show LeakEvent.pureOp "Cassgn" :: Cmd.leakTrace (toJasminCmd body)
       = LeakEvent.pureOp "Cassgn" :: LowCT.toJasminLeakTrace body
    rw [ih]
  | RLetU64Zero x body ih =>
    show LeakEvent.pureOp "Cassgn" :: Cmd.leakTrace (toJasminCmd body)
       = LeakEvent.pureOp "Cassgn" :: LowCT.toJasminLeakTrace body
    rw [ih]
  | RScalarSet _ _ => rfl
  | RCall _ _ _ => rfl
  | RCallSwap _ _ _ _ => rfl
  | RCloneCall _ _ _ _ _ _ => rfl
  | RIfNz _ _ _ _ _ => rfl
  | RWhileNz _ _ _ => rfl
  | RFor x n body ih =>
    -- Both sides unroll to `n` copies of `Cassgn :: (trace body)`.
    show Cmd.leakTrace (unrollForJ x (toJasminCmd body) n) =
         LowCT.toJasminLeakTrace.loop (LowCT.toJasminLeakTrace body) n
    induction n with
    | zero => rfl
    | succ k ihk =>
        simp only [unrollForJ, LowCT.toJasminLeakTrace.loop,
                   Cmd.leakTrace_append, ihk, Cmd.leakTrace_cons,
                   Cmd.leakTrace_nil, InstrR.leakEvent, ih]
  | RLimbStore _ _ _ => rfl
  | RLimbStoreExpr _ _ _ => rfl
  -- Phase F/G/H/L/M (2026-05-03): each lowers to a single instruction
  -- (or empty / body-recursion); reduces by `rfl` after `simp`.
  | RAsmOp _ _ _ => rfl
  | RCallN _ _ _ => rfl
  | RSelect _ _ _ _ => rfl
  | RAssert _ => rfl
  | RBlock body ih =>
    simp [toJasminCmd_RBlock, LowCT.toJasminLeakTrace, ih]
  -- Phase C: RFnDef inlines body++cont (matches `toJasminCmd`'s `.RFnDef`
  -- arm); RFnCall emits a single `Ccall`.
  | RFnDef _ _ _ _ _ ih_body ih_cont =>
    simp [toJasminCmd_RFnDef, Cmd.leakTrace_append, ih_body, ih_cont,
          LowCT.toJasminLeakTrace]
  | RFnCall _ _ _ => rfl
  | RTupleStore _ _ _ => rfl
  | RTupleLoad _ _ _ => rfl
  -- Phase Ext (2026-05-12/14): RBytesSlice → []; rfl closes.
  | RBytesSlice _ _ _ _ => rfl
  -- Phase RND (2026-05-30, #261): the dynamic-index array store/load and the
  -- runtime-scalar SExpr assignment now emit a single real instruction.  The
  -- emit branches on `arrElemWS arr` (store/load) and on the `SExpr` shape
  -- (scalar-set), but every branch is one `Cassgn` (or one `Copn` for the
  -- top-level high-multiply), so the structural leak trace is the single-event
  -- closed form.  Case on the discriminant, then each branch closes by `rfl`.
  | RScalarSetExpr x e =>
    show Cmd.leakTrace (sexprSetExprCmd x e) = _
    cases e <;> rfl
  | RArrLoad dst src idxVar =>
    simp only [toJasminCmd_RArrLoad, LowCT.toJasminLeakTrace]
    cases arrElemWS src <;> rfl
  | RArrStore arr idxVar src =>
    simp only [toJasminCmd_RArrStore, LowCT.toJasminLeakTrace]
    cases arrElemWS arr <;> rfl
  -- Phase DD (2026-05-28) / E2 (2026-05-29): single-instruction lowerings.
  | RArrLoadLit _ _ _ => rfl
  | RArrStoreLit _ _ _ => rfl
  | RCallDstThreaded _ _ _ => rfl
  -- Stage 1a (2026-07-01): runtime loop rejected to `[]` by toJasminCmd.
  | RForRuntime _ _ _ => rfl

/-- **A1.4 corollary**: the unified trace of a translated LowCT is
    determined by `c`'s syntax via the closed-form leak trace plus the
    terminal `.ret`. Direct consequence of `leakTrace_toJasminCmd` and
    the round-trip `Cmd.toUnifiedTrace_leak_proj`. -/
theorem Cmd.toUnifiedTrace_toJasminCmd_leak_proj (c : LowCT) :
    UnifiedTrace.toLeakTrace
        (Cmd.toUnifiedTrace (toJasminCmd c))
      = LowCT.toJasminLeakTrace c := by
  rw [Cmd.toUnifiedTrace_leak_proj, Cmd.leakTrace_toJasminCmd]

end JasminSem

/-! ## §12. CompilerCorrect lifts to trace equality (Track A1.6)

The `CompilerCorrect source target := ∀ x, source x = target x`
relation in `Framework.lean` gives pointwise equality of `ITreeN`
computations. Trace equality follows by `congrArg` over any trace
producer — at the type level the lemma is a generic
`congrArg`-instantiation, but we record the named statement so RHP
proofs can cite it directly without re-deriving it on the fly. -/

theorem compiler_correct_trace_eq
    {hon β γ : Type} {E : EventSig} {n : Nat}
    {source target : hon → ITreeN n E β}
    (toTrace : ITreeN n E β → γ)
    (h : CatCrypt.Crypto.SecureCompilation.CompilerCorrect source target)
    (x : hon) :
    toTrace (source x) = toTrace (target x) :=
  congrArg toTrace (h x)

/-- Stateful version: `CompilerCorrectStateful` lifts to per-state
    trace equality. -/
theorem compiler_correct_stateful_trace_eq
    {hon S β γ : Type} {E : EventSig} {n : Nat}
    {source target : hon → StatefulITreeN S n E β}
    (toTrace : StatefulITreeN S n E β → γ)
    (h : CatCrypt.Crypto.SecureCompilation.CompilerCorrectStateful
            source target)
    (x : hon) :
    toTrace (source x) = toTrace (target x) :=
  congrArg toTrace (funext (h x))

/-! ## §13. RHP-2 entry point: back-translation of trace properties

The structural correspondence theorem `Cmd.leakTrace_toJasminCmd` lets
us translate trace-shaped hyperproperties between source (LowCT) and
target (Jasmin Cmd) at the level of the syntactic translation. This is
the cheapest case of robust hyperproperty preservation: when a property
`P` of the target trace is invariant under the syntactic translation,
the corresponding source-side property is `P ∘ LowCT.toJasminLeakTrace`.

The full RHP-2 picture (asymmetric back-translation of *adversaries*
rather than just trace properties) requires the dynamic refactor (A1.5)
and is left as follow-up. -/

namespace JasminSem
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT

/-- Back-translate a trace-property `P : LeakTrace → Prop` over Jasmin
    `Cmd`s into the corresponding LowCT-side property. -/
def LowCT.backTranslate (P : LeakTrace → Prop) : LowCT → Prop :=
  fun c => P (LowCT.toJasminLeakTrace c)

/-- **Sanity check**: for any LowCT, the structural Jasmin leak trace
    of its translation satisfies `P` iff the back-translated property
    holds for the LowCT. By definition. -/
theorem LowCT.backTranslate_iff (P : LeakTrace → Prop) (c : LowCT) :
    LowCT.backTranslate P c ↔ P (Cmd.leakTrace (toJasminCmd c)) := by
  unfold LowCT.backTranslate
  rw [Cmd.leakTrace_toJasminCmd]

/-- **RHP-2 (trace-property fragment)**: if every translated program
    satisfies a target-side trace property, then every source program
    satisfies the back-translated version.

    This is the RHP-2 statement specialised to *trace* hyperproperties
    rather than full *trace-set* hyperproperties — sufficient for
    constant-time-style properties (single-trace), insufficient for
    properties relating multiple traces (e.g., relational
    non-interference). The latter needs A1.5 + a hyperproperty
    framework. -/
theorem LowCT.rhp2_trace_property (P : LeakTrace → Prop)
    (h : ∀ c : LowCT, P (Cmd.leakTrace (toJasminCmd c))) :
    ∀ c : LowCT, LowCT.backTranslate P c :=
  fun c => (LowCT.backTranslate_iff P c).mpr (h c)

/-- **Converse direction**: a LowCT-side property of the back-translated
    shape gives a target-side property of the translation. -/
theorem LowCT.rhp2_trace_property_target (P : LeakTrace → Prop)
    (h : ∀ c : LowCT, LowCT.backTranslate P c) :
    ∀ c : LowCT, P (Cmd.leakTrace (toJasminCmd c)) :=
  fun c => (LowCT.backTranslate_iff P c).mp (h c)

/-! ## §13.1. Worked example: "no `Cif` in the Jasmin trace"

To make the back-translation framework concrete, we instantiate it
with the simplest non-trivial property: "the Jasmin-side leak trace
contains no `pureOp "Cif"` event". The source-side characterisation
this back-translates to is "the LowCT contains no `RIfNz` constructor"
(plus the deferred-translation cases — `RWhileNz` / `RFor` — and the
control-flow-free cases that always pass). -/

/-- Predicate: this LowCT contains no top-level `RIfNz`.
    Note `RWhileNz` and `RFor` bodies are *not* recursed into — they are
    opaque from the structural Jasmin trace's perspective (`Cmd.leakTrace`
    sees `Cwhile`/`Cfor` as a single event without unrolling). The
    correspondence theorem below matches that granularity. -/
def LowCT.ifFree : LowCT → Bool
  | .RSkip                       => true
  | .RSeq c1 c2                  => LowCT.ifFree c1 && LowCT.ifFree c2
  | .RLetZero _ _ body           => LowCT.ifFree body
  | .RLetU64Zero _ body          => LowCT.ifFree body
  | .RScalarSet _ _              => true
  | .RCall _ _ _                 => true
  | .RCallSwap _ _ _ _           => true
  | .RCloneCall _ _ _ _ _ _      => true
  | .RIfNz _ _ _                 => false
  | .RWhileNz _ _                => true
  -- An empty RFor (n = 0) emits no trace events; otherwise the body's Cif-freeness
  -- is what matters (the unrolling adds Cassgn but never Cif).
  | .RFor _ n body               => decide (n = 0) || LowCT.ifFree body
  -- Stage 1a: runtime loop lowers to `[]` (rejected), so it is `Cif`-free.
  | .RForRuntime _ _ _           => true
  | .RLimbStore _ _ _            => true
  | .RLimbStoreExpr _ _ _        => true
  -- Phase F/G/H/L/M (2026-05-03): the new constructors emit no `Cif`.
  | .RAsmOp _ _ _                => true
  | .RCallN _ _ _                => true
  | .RSelect _ _ _ _             => true
  | .RAssert _                   => true
  | .RBlock body                 => LowCT.ifFree body
  | .RFnDef _ _ _ body cont      => LowCT.ifFree body && LowCT.ifFree cont
  | .RFnCall _ _ _               => true
  -- Phase I (2026-05-03): tuple component store/load emits no `Cif`.
  | .RTupleStore _ _ _           => true
  | .RTupleLoad _ _ _            => true
  -- Phase Ext (2026-05-12/14): new constructors emit no `Cif`.
  | .RBytesSlice _ _ _ _         => true
  | .RScalarSetExpr _ _          => true
  | .RArrLoad _ _ _              => true
  | .RArrStore _ _ _             => true
  -- Phase DD (2026-05-28) / E2 (2026-05-29): literal-index array access
  -- and dst-threaded call emit no `Cif`.
  | .RArrLoadLit _ _ _           => true
  | .RArrStoreLit _ _ _          => true
  | .RCallDstThreaded _ _ _      => true

/-- The Jasmin-side trace property: no `Cif` event in the leak trace. -/
def TargetCifFree (trace : LeakTrace) : Prop :=
  LeakEvent.pureOp "Cif" ∉ trace

/-! ### Relational back-translation (A1.9)

Lift back-translation from single-trace properties (`LeakTrace → Prop`)
to *relational* properties (`LeakTrace → LeakTrace → Prop`). This covers
hyperproperties that compare two runs of a program — non-interference,
leakage NI, observational equivalence — at the syntactic-translation
level. The structural Jasmin trace is purely a function of the AST, so
two LowCTs `c₁` and `c₂` produce relationally-related Jasmin traces
iff their AST images do, computed by `LowCT.toJasminLeakTrace`. -/

/-- Relational back-translation: lift a binary property `R` over Jasmin
    leak traces into a binary property over LowCT source programs. -/
def LowCT.relBackTranslate (R : LeakTrace → LeakTrace → Prop) :
    LowCT → LowCT → Prop :=
  fun c₁ c₂ => R (LowCT.toJasminLeakTrace c₁) (LowCT.toJasminLeakTrace c₂)

/-- Definitional unfolding of `relBackTranslate` via the Jasmin-side
    Cmd traces. Companion to `backTranslate_iff` for the relational case. -/
theorem LowCT.relBackTranslate_iff (R : LeakTrace → LeakTrace → Prop)
    (c₁ c₂ : LowCT) :
    LowCT.relBackTranslate R c₁ c₂ ↔
      R (Cmd.leakTrace (toJasminCmd c₁))
        (Cmd.leakTrace (toJasminCmd c₂)) := by
  unfold LowCT.relBackTranslate
  rw [Cmd.leakTrace_toJasminCmd, Cmd.leakTrace_toJasminCmd]

/-- **A1.9 forward direction**: if a relational property `R` holds for
    every pair of translated programs, then the back-translated property
    holds for every pair of source programs. The shape generalises
    `rhp2_trace_property`. -/
theorem LowCT.rrhp2_relational_property (R : LeakTrace → LeakTrace → Prop)
    (h : ∀ c₁ c₂ : LowCT,
            R (Cmd.leakTrace (toJasminCmd c₁))
              (Cmd.leakTrace (toJasminCmd c₂))) :
    ∀ c₁ c₂ : LowCT, LowCT.relBackTranslate R c₁ c₂ :=
  fun c₁ c₂ => (LowCT.relBackTranslate_iff R c₁ c₂).mpr (h c₁ c₂)

/-- **A1.9 converse direction**: the source-side back-translated property
    gives the target-side property for translations. -/
theorem LowCT.rrhp2_relational_property_target
    (R : LeakTrace → LeakTrace → Prop)
    (h : ∀ c₁ c₂ : LowCT, LowCT.relBackTranslate R c₁ c₂) :
    ∀ c₁ c₂ : LowCT,
      R (Cmd.leakTrace (toJasminCmd c₁))
        (Cmd.leakTrace (toJasminCmd c₂)) :=
  fun c₁ c₂ => (LowCT.relBackTranslate_iff R c₁ c₂).mp (h c₁ c₂)

/-! ### Worked relational example (A1.10): equal-trace property

The simplest non-trivial relational property: two programs produce
equal Jasmin leak traces. Source-side this back-translates to "the
two LowCTs have the same `LowCT.toJasminLeakTrace`". The
correspondence is `Iff.rfl` — relational back-translation is
definitionally the lifted equality. -/

/-- Target-side relational property: equal leak traces. -/
def TargetEqualTraces (t₁ t₂ : LeakTrace) : Prop :=
  t₁ = t₂

/-- Source-side relational property: equal Jasmin leak traces. -/
def LowCT.equalJasminTraces (c₁ c₂ : LowCT) : Prop :=
  LowCT.toJasminLeakTrace c₁ = LowCT.toJasminLeakTrace c₂

/-- **A1.10 worked example**: source-side `equalJasminTraces` is exactly
    the back-translation of target-side `TargetEqualTraces`. Holds by
    `Iff.rfl` from the definitions. -/
theorem equalJasminTraces_iff_relBackTranslate (c₁ c₂ : LowCT) :
    LowCT.equalJasminTraces c₁ c₂ ↔
      LowCT.relBackTranslate TargetEqualTraces c₁ c₂ :=
  Iff.rfl

/-- Reflexivity of `equalJasminTraces`: every program has equal traces
    with itself. -/
theorem LowCT.equalJasminTraces_refl (c : LowCT) :
    LowCT.equalJasminTraces c c := rfl

/-- Symmetry of `equalJasminTraces`. -/
theorem LowCT.equalJasminTraces_symm {c₁ c₂ : LowCT}
    (h : LowCT.equalJasminTraces c₁ c₂) :
    LowCT.equalJasminTraces c₂ c₁ :=
  h.symm

/-- Transitivity of `equalJasminTraces`. -/
theorem LowCT.equalJasminTraces_trans {c₁ c₂ c₃ : LowCT}
    (h₁₂ : LowCT.equalJasminTraces c₁ c₂)
    (h₂₃ : LowCT.equalJasminTraces c₂ c₃) :
    LowCT.equalJasminTraces c₁ c₃ :=
  h₁₂.trans h₂₃

/-! ### k-safety back-translation (A1.11)

Generalise from single-trace (k = 1) and relational (k = 2) to arbitrary
k. A *k-safety hyperproperty* is a property of a `k`-tuple of traces;
the back-translation is the same syntactic correspondence applied
componentwise.

`Fin k → α`-style tuples keep the framework in pure Lean without needing
to formalise general `Set Trace`-style hyperproperties (which would
require an input-trace model). For most operational k-safety claims —
non-interference (k=2), transitive non-interference (k=3),
generalised non-interference (k≥2) — `Fin k → LeakTrace → Prop` is
the right shape. -/

/-- k-safety back-translation: lift a property `P` over k-tuples of
    Jasmin leak traces to a property over k-tuples of LowCT source
    programs. Specialises to `backTranslate` at k = 1 and
    `relBackTranslate` at k = 2. -/
def LowCT.kSafetyBackTranslate {k : Nat}
    (P : (Fin k → LeakTrace) → Prop) :
    (Fin k → LowCT) → Prop :=
  fun cs => P (fun i => LowCT.toJasminLeakTrace (cs i))

/-- Definitional unfolding of `kSafetyBackTranslate` via the Jasmin-side
    Cmd traces. Generalises `backTranslate_iff` and
    `relBackTranslate_iff`. -/
theorem LowCT.kSafetyBackTranslate_iff {k : Nat}
    (P : (Fin k → LeakTrace) → Prop) (cs : Fin k → LowCT) :
    LowCT.kSafetyBackTranslate P cs ↔
      P (fun i => Cmd.leakTrace (toJasminCmd (cs i))) := by
  unfold LowCT.kSafetyBackTranslate
  have heq : (fun i => LowCT.toJasminLeakTrace (cs i))
           = (fun i => Cmd.leakTrace (toJasminCmd (cs i))) := by
    funext i; rw [Cmd.leakTrace_toJasminCmd]
  rw [heq]

/-- **A1.11 forward direction** (k-safety preservation): if a k-safety
    property `P` holds for every k-tuple of translated programs, then the
    back-translated property holds for every k-tuple of source programs. -/
theorem LowCT.k_safety_preservation {k : Nat}
    (P : (Fin k → LeakTrace) → Prop)
    (h : ∀ cs : Fin k → LowCT,
            P (fun i => Cmd.leakTrace (toJasminCmd (cs i)))) :
    ∀ cs : Fin k → LowCT, LowCT.kSafetyBackTranslate P cs :=
  fun cs => (LowCT.kSafetyBackTranslate_iff P cs).mpr (h cs)

/-- **A1.11 converse direction**: source-side k-safety gives target-side
    k-safety on translations. -/
theorem LowCT.k_safety_preservation_target {k : Nat}
    (P : (Fin k → LeakTrace) → Prop)
    (h : ∀ cs : Fin k → LowCT, LowCT.kSafetyBackTranslate P cs) :
    ∀ cs : Fin k → LowCT,
      P (fun i => Cmd.leakTrace (toJasminCmd (cs i))) :=
  fun cs => (LowCT.kSafetyBackTranslate_iff P cs).mp (h cs)

/-- Sanity: `kSafetyBackTranslate` at `k = 1` recovers `backTranslate`
    when the single-trace property is restated in tuple form. -/
theorem LowCT.kSafetyBackTranslate_one
    (P : LeakTrace → Prop) (c : LowCT) :
    LowCT.kSafetyBackTranslate (k := 1)
        (fun (cs : Fin 1 → LeakTrace) => P (cs 0))
        (fun _ => c)
      ↔ LowCT.backTranslate P c :=
  Iff.rfl

/-- Sanity: `kSafetyBackTranslate` at `k = 2` recovers `relBackTranslate`
    when the relational property is restated in tuple form. -/
theorem LowCT.kSafetyBackTranslate_two
    (R : LeakTrace → LeakTrace → Prop) (c₁ c₂ : LowCT) :
    LowCT.kSafetyBackTranslate (k := 2)
        (fun (cs : Fin 2 → LeakTrace) => R (cs 0) (cs 1))
        (fun i => if i = 0 then c₁ else c₂)
      ↔ LowCT.relBackTranslate R c₁ c₂ :=
  Iff.rfl

/-- **Worked example**: source-side `ifFree` is exactly the back-translation
    of the target-side `TargetCifFree` property. The proof is by
    structural induction on `c`; each clause of `LowCT.toJasminLeakTrace`
    matches the corresponding `ifFree` case. -/
theorem ifFree_iff_backTranslate_TargetCifFree (c : LowCT) :
    LowCT.ifFree c = true ↔ LowCT.backTranslate TargetCifFree c := by
  unfold LowCT.backTranslate TargetCifFree
  induction c with
  | RSkip => simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RSeq c1 c2 ih1 ih2 =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace, List.mem_append, not_or]
    rw [ih1, ih2]
  | RLetZero x t body ih =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
    exact ih
  | RLetU64Zero x body ih =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
    exact ih
  | RScalarSet _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RCall _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RCallSwap _ _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RCloneCall _ _ _ _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RIfNz _ _ _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RWhileNz _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RFor x n body ih =>
    -- ifFree (RFor x n body) = (n = 0) || ifFree body.
    -- toJasminLeakTrace = loop (toJasminLeakTrace body) n.  For n = 0: empty.
    -- For n ≥ 1: appends Cassgn :: bodyTrace at each step; Cif-free iff body Cif-free.
    show ((decide (n = 0)) || LowCT.ifFree body) = true ↔
        TargetCifFree (LowCT.toJasminLeakTrace.loop (LowCT.toJasminLeakTrace body) n)
    cases n with
    | zero =>
        simp only [decide_eq_true_eq, Bool.true_or, true_iff,
                   LowCT.toJasminLeakTrace.loop]
        unfold TargetCifFree
        simp
    | succ k =>
        have hdec : decide (k + 1 = 0) = false := by simp
        simp only [hdec, Bool.false_or]
        rw [ih]
        -- Need: TargetCifFree body_trace ↔ TargetCifFree (loop body_trace (k+1)).
        unfold TargetCifFree
        -- Iff: Cif ∉ body_trace ↔ (Cif ∉ loop body_trace k ∧ Cassgn ≠ Cif ∧ Cif ∉ body_trace)
        -- Reduces to Cif ∉ body_trace by induction on k.
        induction k with
        | zero =>
            simp only [LowCT.toJasminLeakTrace.loop, List.append_nil, List.nil_append,
                       List.mem_cons, not_or]
            constructor
            · intro h; refine ⟨?_, h⟩
              intro heq
              exact LeakEvent.noConfusion heq fun hstr => by simp at hstr
            · rintro ⟨_, h⟩; exact h
        | succ j ihj =>
            have ihj' := ihj (by simp)
            simp only [LowCT.toJasminLeakTrace.loop, List.mem_append, List.mem_cons, not_or]
            simp only [List.mem_append, List.mem_cons, not_or,
                       LowCT.toJasminLeakTrace.loop] at ihj'
            constructor
            · intro h
              refine ⟨ihj'.mp h, ?_, h⟩
              intro heq
              exact LeakEvent.noConfusion heq fun hstr => by simp at hstr
            · rintro ⟨_hLoop, _hHead, hBody⟩
              exact hBody
  | RLimbStore _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RLimbStoreExpr _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  -- Phase F/G/H/L/M (2026-05-03): the new constructors emit no `Cif`.
  | RAsmOp _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RCallN _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RSelect _ _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RAssert _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RBlock body ih =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
    exact ih
  -- Phase C: RFnDef forwards to body++cont; RFnCall is a single `Ccall`.
  | RFnDef _ _ _ _ _ ih_body ih_cont =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace, ih_body, ih_cont]
  | RFnCall _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RTupleStore _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RTupleLoad _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RBytesSlice _ _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  -- Phase RND (2026-05-30, #261): `RScalarSetExpr` now emits a single
  -- `Copn` (high-mul) or `Cassgn` (general SExpr); `RArrLoad`/`RArrStore`
  -- emit a single `Cassgn`.  None is a `Cif`, so each remains `ifFree`;
  -- case on the SExpr shape for the scalar-set arm.
  | RScalarSetExpr _ e =>
    cases e <;> simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RArrLoad _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RArrStore _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  -- Phase DD (2026-05-28) / E2 (2026-05-29): single-instruction (Cassgn/
  -- Ccall) lowerings — Cif-free, same simp closes.
  | RArrLoadLit _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RArrStoreLit _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RCallDstThreaded _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]
  | RForRuntime _ _ _ =>
    simp [LowCT.ifFree, LowCT.toJasminLeakTrace]

end JasminSem

end CatCrypt.Crypto.SecureCompilation.UnifiedTrace
