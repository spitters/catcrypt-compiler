/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.SpeculativeCTFence
public import CatCrypt.Crypto.SecureCompilation.SpeculativeCTFence

/-!
# Verified address-masking (Speculative-Load-Hardening): speculative CT against
  an *unconstrained* predictor, by masking rather than fencing

`SpeculativeCT.lean` gives the speculative leakage observer `specObs` and
`SpeculativelyConstantTime`; `SpeculativeCTFence.lean` gives the blanket-fence
pass `insertFences` (an `lfence` at every branch arm and loop head, drained by
`specTransient`) and equality of the fenced traces under an unconstrained
oracle.

A blanket fence is conservative: every barrier serialises the pipeline.  The Blade / Jasmin / LLVM hardening literature reports ~5.0% overhead
for blanket fencing versus ~1.7% for **Speculative-Load-Hardening (SLH)**, which
leaves the pipeline running and instead *masks load addresses* with a
misprediction predicate: a register that holds `0` whenever a branch may have
mis-speculated, ANDed into every load address, forcing the transiently-issued
address to a safe constant.  Under mis-speculation the masked load therefore
reads a *data-independent* address — the transient cache-line is the sentinel,
not a secret-dependent one — so the transient leak is killed without draining
the pipeline.

This file adds the SLH **address-masking** mitigation alongside the fence pass:
a verified `LowCT → LowCT` pass `insertMasks` that wraps every load (and the
loads reachable inside a branch arm / loop body) with an address mask, and the
theorem that the mask-hardened program is speculatively constant-time against an
**unconstrained** misprediction oracle.

The argument mirrors the fence collapse, but the *mechanism* differs.  Where the
fence theorem shows the transient wrong-path contributes **no** observation (it
drains), the mask theorem shows the transient wrong-path contributes only a
**data-independent constant** observation (the sentinel address) — the masked
speculative trace is therefore a fixed function of the public state, so it is
equal on any two `PublicEquiv` states for every window and every (adversarial)
oracle.  This is exactly the SLH guarantee: speculation proceeds, but every
transiently-issued address is masked to a constant.

## What this provides

1. `maskAddr` — the SLH masking primitive: `maskAddr predicate addr` returns the
   safe `sentinelAddr` when the misprediction predicate is set, else `addr`.
   (`maskAddr true addr = sentinelAddr` is the key data-independence fact.)

2. `RMask` / `maskLabel` — a mask marker, modelled as the zero-cost
   `LowCT.RAssert` no-op carrying a distinguished label, exactly as
   `SpeculativeCTFence.RFence` is — so the pass introduces no new `LowCT`
   constructor and reuses the existing `cmdCT` / `archObs` / `specObs` clauses.

3. `insertMasks : LowCT → LowCT`, a structural recursion that wraps every load
   (and recurses into branch arms / loop bodies) with an address mask marker.

4. **Denotation preservation** (`archObs_insertMasks`, `cmdCT_insertMasks`): the
   mask marker is a no-op for the architectural semantics (the architectural
   leakage trace is unchanged) and the pass preserves `cmdCT` acceptance.

5. **Masked speculative semantics** (`specObsM`, `specMaskedTransient`): identical
   to `specObs` except that, on a mis-speculated load, the transiently-issued
   memory-index observation is the **masked** (sentinel) address rather than the
   runtime one, and a masked load's store-bypass marker carries the word read at
   that masked address rather than at the runtime one.  This is the operational
   content of "SLH masks the speculative address".

6. **The masked-trace equality** (`specObsM_insertMasks_eq`,
   `insertMasks_SCT_unconstrained`): for *any* window and *any* oracle, the
   masked speculative trace of `insertMasks c` is equal on `PublicEquiv` states
   when `c` is `cmdCT`-accepted.

7. **Marker count** (`insertMasks_subsumes_fewer_sites`): masking touches only
   the *load* sites, whereas blanket fencing places a barrier at every branch
   arm / loop head *and* every call / load / store.  The inclusion of the
   marked-site sets is the structural form of the overhead argument
   (~1.7% SLH vs ~5.0% blanket fence).

## Scope

* The observable is the same branch-decision and memory-address pattern the
  rest of this model reasons over.  The mask forces the *transiently-issued
  address* to a constant; the committed address is untouched, since committed
  execution is not mis-speculated and its predicate is `0`.
* The masked clauses are the load-address ones.  The call-site markers steer
  control rather than a load address and are left to
  `SpeculativeCTFence.insertFences`.
* `RMask` is a `LowCT.RAssert` label that only `specObsM` reads.  Over
  `SpeculativeCTStoreBuffer.specRun`, whose loads may be forwarded a buffered
  store value, `SpeculativeCTStoreBufferPasses.specRun_insertMasks` shows the
  pass is the identity, and `insertMasks_not_SCT_SB` shows a `cmdCT`-accepted
  command whose masked image separates two `PublicEquiv` states there.  The
  restatements over that run take `ArchConstantTimeSB` as hypothesis and hold
  at window `0` and under `neverSpeculate`.
* As in the fence file, `LowCT` has no separate executable big-step here;
  `archObs` is the leakage denotation this file reasons over.

## References

* Cauligi et al., "Constant-Time Foundations for the New Spectre Era",
  PLDI 2020 (the speculative semantics and SLH).
* Shivakumar, Barthe, Grégoire, Laporte, Oliveira, Priya, Rezk, Schwabe,
  "Typing High-Speed Cryptography against Spectre v1", IEEE S&P 2023 (Jasmin's
  selective fence/SLH protection — the perf-optimal variant).
* Vassena, Disselkoen, von Gleissenthall, Cauligi, Kıcı, Jhala, Tullsen,
  Stefan, "Automatically Eliminating Speculative Leaks with Blade", POPL 2021
  (masking vs fencing, the ~1.7% vs ~5.0% overhead figures).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.SpeculativeCT

open CatCrypt.Crypto.Jasmin.LowCT

set_option autoImplicit false

/-! ## §1.  The SLH masking primitive

A masked load computes its effective address as `addr AND mask`, where the mask
register is all-ones during committed execution and all-zeros once a branch may
have mis-speculated.  We model the mask register's effect directly: under the
misprediction *predicate* (a `Bool` the oracle drives), the address is forced to
a safe `sentinelAddr`; otherwise it is the true address.  This is the address
analogue of SLH's `cmov`/`AND` hardening, abstracted to the address-pattern
granularity the SCT observer cares about. -/

/-- The safe sentinel address a masked load reads under mis-speculation.  Any
    fixed, data-independent constant works; `0` models the all-zero mask result
    (`addr AND 0 = 0`). -/
def sentinelAddr : Nat := 0

/-- **The SLH masking primitive.**  `maskAddr mispredicted addr` is the
    effective address of a load hardened by speculative-load-hardening: when the
    misprediction predicate is set, the address is forced to the safe
    `sentinelAddr` (the all-zero mask result); otherwise it is the true `addr`.

    Operationally: `effAddr = addr AND maskReg`, with `maskReg = 0…0` once a
    branch may have mis-speculated and `1…1` otherwise. -/
def maskAddr (mispredicted : Bool) (addr : Nat) : Nat :=
  if mispredicted then sentinelAddr else addr

/-- Under misprediction, the masked address is the sentinel **independently of
    the true address** — the data-independence fact that kills the transient
    leak.  (The all-zero mask forces the address to a constant.) -/
@[simp] theorem maskAddr_true (addr : Nat) : maskAddr true addr = sentinelAddr :=
  rfl

/-- Committed execution is not mis-speculated, so the mask is the identity. -/
@[simp] theorem maskAddr_false (addr : Nat) : maskAddr false addr = addr := rfl

/-- The masked address under misprediction does not depend on the address: any
    two addresses mask to the same sentinel.  This is the SLH guarantee in one
    line — the transiently-issued address carries no information. -/
theorem maskAddr_true_const (a b : Nat) : maskAddr true a = maskAddr true b := rfl

/-! ## §2.  The mask marker

As with the fence file, we model the SLH mask point as a zero-cost Phase-L
assertion `RAssert maskLabel`.  Phase-L assertions have no runtime effect and
emit no bytes, so:

* the pass introduces **no new `LowCT` constructor** (every existing analyser /
  observer clause for `RAssert` applies verbatim), and
* the mask marker is a no-op for the architectural semantics — it leaks nothing
  (`archObs … (RAssert _) = []`) and is always `cmdCT`-clean.

A *distinguished* label `maskLabel` lets the masked speculative observer
recognise a hardened load and apply `maskAddr` to its transient address. -/

/-- The distinguished assertion label marking an SLH address-mask point. -/
def maskLabel : String := "__slh_mask__"

/-- An SLH address-mask marker, modelled as the zero-cost `RAssert` no-op
    carrying the distinguished `maskLabel`. -/
def RMask : LowCT := .RAssert maskLabel

theorem maskLabel_ne_fenceLabel : maskLabel ≠ fenceLabel := by decide
theorem maskLabel_ne_guardLabel : maskLabel ≠ guardLabel := by decide

@[simp] theorem archObs_RMask (rs : RustState) : archObs rs RMask = [] := rfl

@[simp] theorem specObs_RMask (window : SpecWindow) (O : MispredOracle)
    (rs : RustState) : specObs window O rs RMask = [] := rfl

@[simp] theorem cmdCT_RMask (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT RMask lt leafCT = true := rfl

/-! ## §3.  The mask-insertion pass

`insertMasks c` rewrites `c`, placing an `RMask` *before* every load
(`RArrLoad`) — the SLH hardening point — and recursing structurally into branch
arms / loop bodies so loads anywhere in the program are masked.  Masking the
load means that when the predictor speculatively issues that load down a wrong
path, its address has already been ANDed with the (now-zero) mask, so the
transiently-issued address is the sentinel. -/

/-- Prepend an SLH address-mask marker to a load. -/
def masked (c : LowCT) : LowCT := .RSeq RMask c

@[simp] theorem archObs_masked (rs : RustState) (c : LowCT) :
    archObs rs (masked c) = archObs rs c := by
  simp [masked, archObs, RMask]

@[simp] theorem cmdCT_masked (c : LowCT) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (masked c) lt leafCT = cmdCT c lt leafCT := by
  simp [masked, cmdCT_RSeq, RMask]

/-- The mask-insertion pass: an `RMask` SLH-hardening point **before** every
    load, recursing structurally everywhere else (so loads inside branch arms /
    loop bodies are masked too).  Unlike `insertFences` it touches *only* the
    load sites — no barrier at branch arms, loop heads, calls, or stores. -/
def insertMasks : LowCT → LowCT
  | .RSeq c1 c2             => .RSeq (insertMasks c1) (insertMasks c2)
  | .RLetZero x t body      => .RLetZero x t (insertMasks body)
  | .RLetU64Zero x body     => .RLetU64Zero x (insertMasks body)
  | .RBlock body            => .RBlock (insertMasks body)
  | .RFnDef n p r body cont => .RFnDef n p r (insertMasks body) (insertMasks cont)
  | .RIfNz cond ct cf       => .RIfNz cond (insertMasks ct) (insertMasks cf)
  | .RWhileNz cond body     => .RWhileNz cond (insertMasks body)
  | .RFor x n body          => .RFor x n (insertMasks body)
  -- The SLH hardening point: mask the load address.
  | .RArrLoad dst src idx   => masked (.RArrLoad dst src idx)
  | c                       => c

/-- `insertMasks` produces an `RAssert` head **only** from an `RAssert` source:
    a load maps to `masked _ = RSeq RMask _` (an `RSeq`, not an `RAssert`), and
    every other constructor maps to a non-`RAssert` node of its own shape.  Used
    to resolve the leading-statement `match` in the masked-observer proofs. -/
theorem insertMasks_eq_RAssert {c : LowCT} {s : String}
    (h : insertMasks c = LowCT.RAssert s) : c = LowCT.RAssert s := by
  cases c <;> simp_all [insertMasks, masked, RMask]

/-! ## §4.  Denotation preservation

The mask marker is a no-op for the architectural semantics, so `insertMasks`
preserves the architectural leakage trace, and preserves `cmdCT` acceptance.
These are the "denote (insertMasks c) = denote c" obligations at the granularity
the CT story reasons over. -/

/-- **Architectural denotation preservation.**  `insertMasks` does not change the
    architectural leakage trace: the inserted mask markers are no-ops. -/
@[simp] theorem archObs_insertMasks (rs : RustState) (c : LowCT) :
    archObs rs (insertMasks c) = archObs rs c := by
  induction c generalizing rs with
  | RSeq c1 c2 ih1 ih2 => simp [insertMasks, archObs, ih1, ih2]
  | RLetZero x t body ih => simp [insertMasks, archObs, ih]
  | RLetU64Zero x body ih => simp [insertMasks, archObs, ih]
  | RBlock body ih => simp [insertMasks, archObs, ih]
  | RFnDef n p r body cont ihB ihC => simp [insertMasks, archObs, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [insertMasks, archObs, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertMasks, archObs, ih]
  | RFor x n body ih =>
      simp only [insertMasks, archObs, ih]
  | RArrLoad dst src idx => simp only [insertMasks, archObs_masked]
  | _ => rfl

/-- **Acceptance preservation.**  `insertMasks` preserves `cmdCT` acceptance:
    mask markers are always `cmdCT`-clean, and the pass changes nothing else. -/
@[simp] theorem cmdCT_insertMasks (c : LowCT) (lt : LevelTable)
    (leafCT : LeafCTTable) :
    cmdCT (insertMasks c) lt leafCT = cmdCT c lt leafCT := by
  induction c generalizing lt with
  | RSeq c1 c2 ih1 ih2 => simp [insertMasks, cmdCT_RSeq, ih1, ih2]
  | RLetZero x t body ih => simp [insertMasks, cmdCT_RLetZero, ih]
  | RLetU64Zero x body ih => simp [insertMasks, cmdCT_RLetU64Zero, ih]
  | RBlock body ih => simp [insertMasks, cmdCT_RBlock, ih]
  | RFnDef n p r body cont ihB ihC =>
      simp [insertMasks, cmdCT_RFnDef, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [insertMasks, cmdCT_RIfNz, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertMasks, cmdCT_RWhileNz, ih]
  | RFor x n body ih =>
      simp only [insertMasks, cmdCT_RFor, ih]
  | RArrLoad dst src idx => simp only [insertMasks, cmdCT_masked]
  | _ => rfl

/-! ## §5.  Masked speculative semantics — "SLH masks the speculative address"

The masked speculative observer `specObsM` is identical to `specObs`, except
that the mis-speculated wrong-path contribution is computed by the auxiliary
`specMaskedTransient`, which issues every load's *masked* (sentinel) address
rather than its runtime address.  A masked load's transient memory-index
observation is therefore `Obs.memIdx idxVar sentinelAddr` — a data-independent
constant — instead of `Obs.memIdx idxVar (rs.rsScalar idxVar)`.

This is the operational content of speculative-load-hardening: speculation
proceeds (the pipeline is not drained), but the misprediction predicate is set,
so the mask register is zero and every transiently-issued load address is the
sentinel.  Because `insertMasks` masks *every* load, the entire transient trace
of a masked wrong-path is data-independent. -/

/-- Transient (mis-speculated) observations of `c`, capped at `window`
    instructions, with every **masked** load's address forced to `sentinelAddr`.
    A mask marker (`RMask`) sets the misprediction predicate for the load it
    guards, so that load's transient memory-index observation is the sentinel
    address — data-independent — rather than the runtime address.

    Non-load constructors contribute their architectural observation and recurse;
    a *masked* load (`RSeq RMask (RArrLoad …)`, as `insertMasks` emits) issues
    `Obs.memIdx idxVar sentinelAddr`.  The overall result is truncated to
    `window` by the caller. -/
def specMaskedTransient (rs : RustState) : LowCT → ObsTrace
  | .RAssert _              => []
  | .RArrLoad _ _ idxVar    =>
      -- An *unmasked* transient load issues its runtime address.
      [Obs.memIdx idxVar (rs.rsScalar idxVar)]
  | .RSeq c1 c2             =>
      match c1 with
      | .RAssert s =>
          if s = maskLabel then
            -- A masked load: the misprediction predicate is set, so the
            -- transiently-issued address is the sentinel — data-independent.
            (match c2 with
             | .RArrLoad _ _ idxVar => [Obs.memIdx idxVar (maskAddr true (rs.rsScalar idxVar))]
             | _                    => specMaskedTransient rs c2)
          else specMaskedTransient rs c2
      | _          => specMaskedTransient rs c1 ++ specMaskedTransient rs c2
  | c                       => archObs rs c

/-- A masked load's transient observation is the **sentinel** address — a fixed
    constant independent of the runtime index value. -/
@[simp] theorem specMaskedTransient_masked_load (rs : RustState)
    (dst src : Located) (idxVar : String) :
    specMaskedTransient rs (masked (.RArrLoad dst src idxVar))
      = [Obs.memIdx idxVar sentinelAddr] := by
  simp [specMaskedTransient, masked, RMask, maskLabel, maskAddr]

/-- A masked load's transient observation does not depend on the runtime state:
    it is the same sentinel observation in any two states.  This is the
    data-independence that makes masking sound against an unconstrained oracle. -/
theorem specMaskedTransient_masked_load_const (rs1 rs2 : RustState)
    (dst src : Located) (idxVar : String) :
    specMaskedTransient rs1 (masked (.RArrLoad dst src idxVar))
      = specMaskedTransient rs2 (masked (.RArrLoad dst src idxVar)) := by
  simp only [specMaskedTransient_masked_load]

/-- The masked speculative observer.  Identical to `specObs`, but the
    mis-speculated branch wrong-path is computed by `specMaskedTransient` (every
    masked load issues the sentinel address) rather than by a raw `.take window`,
    and a *masked* load (`RSeq RMask (RArrLoad …)`, as `insertMasks` emits)
    issues its committed (architectural) memory-index observation while its STL
    marker carries the word read out of the source slot at the masked (sentinel)
    address.

    After `insertMasks`, every load is masked, so every transient load address
    is the sentinel — the transient trace is data-independent. -/
def specObsM (window : SpecWindow) (O : MispredOracle) (rs : RustState) :
    LowCT → ObsTrace
  | .RSkip                  => []
  | .RAssert _              => []
  | .RScalarSet _ _         => []
  | .RScalarSetExpr _ _     => []
  | .RSeq c1 c2             =>
      match c1 with
      | .RAssert s =>
          if s = maskLabel then
            -- A masked load: emit its committed (architectural) memory-index
            -- observation; its store-bypass marker carries the word read out of
            -- the source slot at the *masked* address, so the forwarded word no
            -- longer depends on the runtime index.
            (match c2 with
             | .RArrLoad _ src idxVar =>
                 let i := rs.rsScalar idxVar
                 let stl : ObsTrace :=
                   if O.bypassStore idxVar i then
                     withRollback
                       [Obs.stlForward src.locVar
                         (rsTowerLimb rs src.locVar (maskAddr true i))]
                   else []
                 Obs.memIdx idxVar i :: stl
             | _ => specObsM window O rs c2)
          else specObsM window O rs c1 ++ specObsM window O rs c2
      | _ => specObsM window O rs c1 ++ specObsM window O rs c2
  | .RLetZero _ _ body      => specObsM window O rs body
  | .RLetU64Zero _ body     => specObsM window O rs body
  | .RBlock body            => specObsM window O rs body
  | .RFnDef _ _ _ body cont =>
      specObsM window O rs body ++ specObsM window O rs cont
  | .RIfNz cond ct cf       =>
      let v := rs.rsScalar cond
      let obsCt : ObsTrace := specObsM window O rs ct
      let obsCf : ObsTrace := specObsM window O rs cf
      -- Mis-speculated wrong-path, with every masked load issuing the sentinel.
      let speculated : ObsTrace :=
        if O.mispredict cond v then
          withRollback
            ((if v ≠ 0 then specMaskedTransient rs cf else specMaskedTransient rs ct).take window)
        else []
      Obs.branch cond v :: (speculated ++ (if v ≠ 0 then obsCt else obsCf))
  | .RWhileNz cond body     =>
      let v := rs.rsScalar cond
      let obsBody : ObsTrace := specObsM window O rs body
      let speculated : ObsTrace :=
        if O.mispredict cond v then
          withRollback ((specMaskedTransient rs body).take window)
        else []
      Obs.branch cond v :: (speculated ++ obsBody)
  | .RFor _ _ body          => specObsM window O rs body
  | .RArrStore _ idxVar _   => [Obs.memIdx idxVar (rs.rsScalar idxVar)]
  | .RArrLoad _ src idxVar  =>
      -- An *unmasked* load: its STL marker carries the word read out of the
      -- source slot at the runtime index (oracle-gated).  Mirrors the `specObs`
      -- STL clause; the masked form is handled in the `RSeq`-with-leading-mask
      -- case above.
      let i := rs.rsScalar idxVar
      let stl : ObsTrace :=
        if O.bypassStore idxVar i then
          withRollback [Obs.stlForward src.locVar (rsTowerLimb rs src.locVar i)]
        else []
      Obs.memIdx idxVar i :: stl
  | .RCall _ dest _         =>
      -- BTB/RSB are *not* an address-masking target (they steer control, not a
      -- load address); SLH leaves them to the fence/site-guard.  Modelled here
      -- exactly as in `specObsF`: the predicted callee pointer and the predicted
      -- return address are the first two words of the destination slot.
      let tslot := dest.locVar
      let tv := rs.rsScalar tslot
      let btb : ObsTrace :=
        if O.injectTarget tslot tv then
          withRollback [Obs.indirectTarget tslot (rsTowerLimb rs tslot 0)]
        else []
      let rsb : ObsTrace :=
        if O.mispredRet tslot tv then
          withRollback [Obs.retTarget tslot (rsTowerLimb rs tslot 1)]
        else []
      btb ++ rsb
  | _                       => []

/-- The masked speculative observer applied to a *masked* load issues the
    committed memory-index observation (and, under a firing STL oracle, the
    masked sentinel transient).  Stated for the case where the store-bypass
    decision is `false`, which is the load clause of
    `specObsM_insertMasks_eq`. -/
@[simp] theorem specObsM_masked_load_noSTL (window : SpecWindow)
    (O : MispredOracle) (rs : RustState) (dst src : Located) (idxVar : String)
    (h : O.bypassStore idxVar (rs.rsScalar idxVar) = false) :
    specObsM window O rs (masked (.RArrLoad dst src idxVar))
      = [Obs.memIdx idxVar (rs.rsScalar idxVar)] := by
  simp [specObsM, masked, RMask, maskLabel, h]

/-! ## §6.  The masked-transient public-determinacy lemma

The branch-arm clause of `specObsM_insertMasks_eq` needs the *masked transient*
of a masked program to be equal on `PublicEquiv` states.  It is a standalone
induction: every masked load issues the public `sentinelAddr` constant, and
every other transient observation reads a `cmdCT`-public slot. -/

/-- The masked transient trace of `insertMasks c` is equal on `PublicEquiv`
    states: every masked load issues the public `sentinelAddr` constant, and
    every committed observation in the (truncated) prefix reads a `cmdCT`-public
    slot. -/
theorem specMaskedTransient_insertMasks_eq
    (lt : LevelTable) (leafCT : LeafCTTable)
    (c : LowCT) (hCT : cmdCT c lt leafCT = true)
    {rs1 rs2 : RustState} (hEq : PublicEquiv lt rs1 rs2) :
    specMaskedTransient rs1 (insertMasks c)
      = specMaskedTransient rs2 (insertMasks c) := by
  induction c generalizing rs1 rs2 with
  | RSkip => rfl
  | RAssert _ => rfl
  | RScalarSet _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RSeq c1 c2 ih1 ih2 =>
      simp only [cmdCT_RSeq, Bool.and_eq_true] at hCT
      -- `specMaskedTransient` matches the head `insertMasks c1`; it is an
      -- `RAssert s` only if `c1` is (a load becomes `RSeq RMask _`).
      simp only [insertMasks, specMaskedTransient]
      split
      · rename_i s heq
        have hc1 : c1 = LowCT.RAssert s := insertMasks_eq_RAssert heq
        subst hc1
        -- `c1 = RAssert s`: the `s = maskLabel` branch peels a possible masked
        -- load in `c2`; in every sub-arm the transient is either the sentinel
        -- constant or `specMaskedTransient (insertMasks c2)`, closed by ih2.
        split
        · split <;> simp only [maskAddr_true, ih2 hCT.2 hEq]
        · simp only [ih2 hCT.2 hEq]
      · simp only [ih1 hCT.1 hEq, ih2 hCT.2 hEq]
  | RArrLoad dst src idxVar =>
      -- A bare load (not under `RSeq`) is itself `insertMasks`-wrapped into a
      -- masked load, whose transient is the sentinel constant.
      simp only [insertMasks, masked, RMask, maskLabel, specMaskedTransient,
        ↓reduceIte, maskAddr_true]
  | _ =>
      -- Every remaining constructor falls into `specMaskedTransient`'s `archObs`
      -- catch-all (it is neither `RAssert`/`RArrLoad`/`RSeq`), and `insertMasks`
      -- keeps it a node of the same head, so the masked transient trace is
      -- `archObs rs (insertMasks c) = archObs rs c` — secret-independent by
      -- `architecturally_CT_imp_ArchCT`.  (The undischarged `hCT` is the original
      -- `cmdCT c lt leafCT = true` for this `c`.)
      first
      | rfl
      | (change archObs rs1 _ = archObs rs2 _
         rw [archObs_insertMasks, archObs_insertMasks]
         exact architecturally_CT_imp_ArchCT lt leafCT _ hCT rs1 rs2 hEq)

/-! ## §6b.  The masked-trace equality

In a masked program — one where every load is preceded by a mask marker — the
mis-speculated load contribution down any wrong-path is the sentinel address, a
fixed constant, and the committed observations read `cmdCT`-public slots.  So
the masked speculative trace is equal on `PublicEquiv` states for every window
and every oracle. -/

/-- The masked speculative trace of `insertMasks c` is equal on `PublicEquiv`
    states, by structural induction: every committed observation reads a
    `cmdCT`-public slot, and every transient masked-load observation is the
    public constant `sentinelAddr`. -/
theorem specObsM_insertMasks_eq
    (window : SpecWindow) (O : MispredOracle)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (c : LowCT) (hCT : cmdCT c lt leafCT = true)
    {rs1 rs2 : RustState} (hEq : PublicEquiv lt rs1 rs2) :
    specObsM window O rs1 (insertMasks c) = specObsM window O rs2 (insertMasks c) := by
  induction c generalizing rs1 rs2 with
  | RSkip => rfl
  | RAssert _ => rfl
  | RScalarSet _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RSeq c1 c2 ih1 ih2 =>
      simp only [cmdCT_RSeq, Bool.and_eq_true] at hCT
      -- `insertMasks (RSeq c1 c2) = RSeq (insertMasks c1) (insertMasks c2)`.
      -- `specObsM` pattern-matches the head `insertMasks c1`; it is an
      -- `RAssert s` only if `c1` is (a load becomes `RSeq RMask _`).
      simp only [insertMasks, specObsM]
      split
      · rename_i s heq
        have hc1 : c1 = LowCT.RAssert s := insertMasks_eq_RAssert heq
        subst hc1
        -- `c1 = RAssert s`.  Under `s = maskLabel` the masked-load sub-arm
        -- (when `c2` is a load) reads the public `idxVar` for the committed obs
        -- and the STL gate, and the public source slot for the masked forwarded
        -- word.  The `_` sub-arm and the non-mask label both close by ih2.
        split
        · -- `s = maskLabel`
          cases c2 with
          | RArrLoad dst src idxVar =>
              have hCT2 := hCT.2
              simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT2
              have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT2.1.1
              have hsrc : lt src.locVar = .Public :=
                level_beq_public_iff.mp hCT2.2
              have hv : rs1.rsScalar idxVar = rs2.rsScalar idxVar :=
                hEq.scalar_eq hidx
              have hT : rs1.rsTower src.locVar = rs2.rsTower src.locVar :=
                hEq.tower_eq hsrc
              simp only [insertMasks, masked, RMask, maskLabel, specObsM,
                ↓reduceIte, hv, rsTowerLimb, hT]
          | _ =>
              -- `c2` is not a load, so the nested `match insertMasks c2`
              -- reduces to `specObsM … (insertMasks c2)`, closed by ih2.
              all_goals exact ih2 hCT.2 hEq
        · -- `s ≠ maskLabel`: `c1 = RAssert s` leaks nothing; close by ih2.
          exact ih2 hCT.2 hEq
      · simp only [ih1 hCT.1 hEq, ih2 hCT.2 hEq]
  | RLetZero x t body ih =>
      simp only [cmdCT_RLetZero] at hCT
      simpa only [insertMasks, specObsM] using ih hCT hEq
  | RLetU64Zero x body ih =>
      simp only [cmdCT_RLetU64Zero] at hCT
      simpa only [insertMasks, specObsM] using ih hCT hEq
  | RBlock body ih =>
      simp only [cmdCT_RBlock] at hCT
      simpa only [insertMasks, specObsM] using ih hCT hEq
  | RFnDef n p r body cont ihB ihC =>
      simp only [cmdCT_RFnDef, Bool.and_eq_true] at hCT
      simp only [insertMasks, specObsM, ihB hCT.1 hEq, ihC hCT.2 hEq]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [cmdCT_RIfNz, Bool.and_eq_true] at hCT
      have hcond : lt cond = .Public := level_beq_public_iff.mp hCT.1.1
      have hv : rs1.rsScalar cond = rs2.rsScalar cond := hEq.scalar_eq hcond
      -- The committed arms close by ih.  The mis-speculated wrong-path is
      -- `specMaskedTransient` of a *masked* arm: every masked load issues the
      -- sentinel constant, so the transient trace is data-independent.  We need
      -- `specMaskedTransient rs1 (insertMasks _) = specMaskedTransient rs2 (insertMasks _)`.
      have htrans : ∀ d : LowCT, cmdCT d lt leafCT = true →
          specMaskedTransient rs1 (insertMasks d)
            = specMaskedTransient rs2 (insertMasks d) :=
        fun d hd => specMaskedTransient_insertMasks_eq lt leafCT d hd hEq
      simp only [insertMasks, specObsM, hv, ihCt hCT.1.2 hEq, ihCf hCT.2 hEq,
        htrans ct hCT.1.2, htrans cf hCT.2]
  | RWhileNz cond body ih =>
      simp only [cmdCT_RWhileNz, Bool.and_eq_true] at hCT
      have hcond : lt cond = .Public := level_beq_public_iff.mp hCT.1
      have hv : rs1.rsScalar cond = rs2.rsScalar cond := hEq.scalar_eq hcond
      have htrans : specMaskedTransient rs1 (insertMasks body)
          = specMaskedTransient rs2 (insertMasks body) :=
        specMaskedTransient_insertMasks_eq lt leafCT body hCT.2 hEq
      simp only [insertMasks, specObsM, hv, ih hCT.2 hEq, htrans]
  | RFor x n body ih =>
      simp only [cmdCT_RFor] at hCT
      simpa only [insertMasks, specObsM] using ih hCT hEq
  | RArrStore arr idxVar src =>
      simp only [cmdCT_RArrStore, Bool.and_eq_true] at hCT
      have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
      have hv : rs1.rsScalar idxVar = rs2.rsScalar idxVar := hEq.scalar_eq hidx
      simp only [insertMasks, specObsM, hv]
  | RArrLoad dst src idxVar =>
      simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT
      have hidx : lt idxVar = .Public := level_beq_public_iff.mp hCT.1.1
      have hsrc : lt src.locVar = .Public := level_beq_public_iff.mp hCT.2
      have hv : rs1.rsScalar idxVar = rs2.rsScalar idxVar := hEq.scalar_eq hidx
      have hT : rs1.rsTower src.locVar = rs2.rsTower src.locVar :=
        hEq.tower_eq hsrc
      simp only [insertMasks, masked, RMask, maskLabel, specObsM, ↓reduceIte, hv,
        rsTowerLimb, hT]
  | RCall f dest args =>
      simp only [cmdCT_RCall, Bool.and_eq_true] at hCT
      have hdest : lt dest.locVar = .Public := level_beq_public_iff.mp hCT.1.2
      have hv : rs1.rsScalar dest.locVar = rs2.rsScalar dest.locVar :=
        hEq.scalar_eq hdest
      have hT : rs1.rsTower dest.locVar = rs2.rsTower dest.locVar :=
        hEq.tower_eq hdest
      simp only [insertMasks, specObsM, hv, rsTowerLimb, hT]
  | _ => rfl

/-! ## §7.  Speculative CT against an unconstrained predictor -/

/-- **Speculatively constant-time (masked semantics).**  Two executions of `c`
    from `PublicEquiv` states produce equal *masked* speculative leakage traces,
    under window `window` and oracle `O`. -/
def SpeculativelyConstantTimeM
    (window : SpecWindow) (O : MispredOracle) (lt : LevelTable) (c : LowCT) :
    Prop :=
  ∀ rs1 rs2 : RustState, PublicEquiv lt rs1 rs2 →
    specObsM window O rs1 c = specObsM window O rs2 c

/-- **The deliverable: verified SLH address-masking ⇒ SCT vs. an unconstrained
    oracle.**  If `c` is architecturally constant-time (`cmdCT`), then
    `insertMasks c` is speculatively constant-time against an **arbitrary**
    (adversarial) misprediction oracle and **any** speculation window.

    Proof: by `specObsM_insertMasks_eq` the masked speculative trace of
    `insertMasks c` is equal on `PublicEquiv` states — every committed
    observation reads a `cmdCT`-public slot, and every transiently-issued masked
    load address is the public `sentinelAddr` constant.  The oracle and window
    are universally quantified; the oracle's choices only ever expose the
    constant-sentinel transient.  This is the SLH "mask the speculative address"
    guarantee against an unconstrained predictor — the pipeline is not drained
    (cf. the fence file), only the transient addresses are masked. -/
theorem insertMasks_SCT_unconstrained
    (window : SpecWindow) (O : MispredOracle)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (c : LowCT) (hCT : cmdCT c lt leafCT = true) :
    SpeculativelyConstantTimeM window O lt (insertMasks c) := by
  intro rs1 rs2 hEq
  exact specObsM_insertMasks_eq window O lt leafCT c hCT hEq

/-! ## §8.  Perf rationale: masking touches fewer sites than blanket fencing

Blanket fencing (`insertFences`) places a barrier at every branch arm, loop
head, call, load, *and* store; SLH masking (`insertMasks`) touches *only* the
load sites.  We record the structural inclusion of the mitigated-site sets — the
formal witness behind the ~1.7% SLH vs ~5.0% blanket-fence overhead figures.

We count the *marker* nodes each pass inserts and show masking never inserts more
than fencing on the same program (and strictly fewer on any program with a
branch, loop, call, or store). -/

/-- The number of barrier markers `insertFences` inserts (`RFence` at branch
    arms / loop heads + `RGuard` before calls / loads / stores). -/
def fenceMarkerCount : LowCT → Nat
  | .RSeq c1 c2             => fenceMarkerCount c1 + fenceMarkerCount c2
  | .RLetZero _ _ body      => fenceMarkerCount body
  | .RLetU64Zero _ body     => fenceMarkerCount body
  | .RBlock body            => fenceMarkerCount body
  | .RFnDef _ _ _ body cont => fenceMarkerCount body + fenceMarkerCount cont
  | .RIfNz _ ct cf          => 2 + fenceMarkerCount ct + fenceMarkerCount cf
  | .RWhileNz _ body        => 1 + fenceMarkerCount body
  | .RFor _ _ body          => 1 + fenceMarkerCount body
  | .RCall _ _ _            => 1
  | .RArrLoad _ _ _         => 1
  | .RArrStore _ _ _        => 1
  | _                       => 0

/-- The number of mask markers `insertMasks` inserts (one `RMask` per load). -/
def maskMarkerCount : LowCT → Nat
  | .RSeq c1 c2             => maskMarkerCount c1 + maskMarkerCount c2
  | .RLetZero _ _ body      => maskMarkerCount body
  | .RLetU64Zero _ body     => maskMarkerCount body
  | .RBlock body            => maskMarkerCount body
  | .RFnDef _ _ _ body cont => maskMarkerCount body + maskMarkerCount cont
  | .RIfNz _ ct cf          => maskMarkerCount ct + maskMarkerCount cf
  | .RWhileNz _ body        => maskMarkerCount body
  | .RFor _ _ body          => maskMarkerCount body
  | .RArrLoad _ _ _         => 1
  | _                       => 0

/-- **Perf witness.**  SLH masking never inserts more barrier markers than
    blanket fencing on the same program: `maskMarkerCount c ≤ fenceMarkerCount c`.
    Masking touches only loads (1 marker each); fencing additionally barriers
    every branch arm (2), loop head (1), call (1), and store (1).  This is the
    structural ground of the ~1.7% (SLH) vs ~5.0% (blanket fence) overhead gap:
    fewer serialising barriers. -/
theorem insertMasks_subsumes_fewer_sites (c : LowCT) :
    maskMarkerCount c ≤ fenceMarkerCount c := by
  induction c with
  | RSeq c1 c2 ih1 ih2 =>
      simp only [maskMarkerCount, fenceMarkerCount]; omega
  | RLetZero x t body ih => simpa [maskMarkerCount, fenceMarkerCount] using ih
  | RLetU64Zero x body ih => simpa [maskMarkerCount, fenceMarkerCount] using ih
  | RBlock body ih => simpa [maskMarkerCount, fenceMarkerCount] using ih
  | RFnDef n p r body cont ihB ihC =>
      simp only [maskMarkerCount, fenceMarkerCount]; omega
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [maskMarkerCount, fenceMarkerCount]; omega
  | RWhileNz cond body ih =>
      simp only [maskMarkerCount, fenceMarkerCount]; omega
  | RFor x n body ih =>
      simp only [maskMarkerCount, fenceMarkerCount]; omega
  | _ => simp [maskMarkerCount, fenceMarkerCount]

/-! ## §9.  Pilot: a masked load kernel is SCT against an unconstrained oracle

`insertMasks_SCT_unconstrained` applied to a kernel containing a load, so that
the masking clauses fire: a public branch flag guarding a table-indexed load
over a public index.  Its architectural acceptance discharges by `cmdCT`, and
the mask pass places strictly fewer markers than the fence pass. -/

namespace PilotMask

open Pilot

/-- A kernel with a load under a public branch: `if flag then a[idx] else a[idx]`,
    all slots public.  The mis-speculated wrong arm contains a load whose
    transient address is masked to the sentinel. -/
def pilotKernelLoad : LowCT :=
  .RIfNz "flag"
    (.RArrLoad ⟨"d", .TU64⟩ ⟨"arr", .TU64⟩ "idx")
    (.RArrLoad ⟨"d", .TU64⟩ ⟨"arr", .TU64⟩ "idx")

theorem pilotKernelLoad_cmdCT :
    cmdCT pilotKernelLoad pilotLevels LeafCTTable.canonical = true := by
  native_decide

/-- The mask-hardened load kernel `insertMasks pilotKernelLoad` has equal
    `specObsM` traces on `PublicEquiv` states, for every window and every
    misprediction oracle: the transient wrong-path load issues the sentinel
    address. -/
theorem pilotKernelLoad_SCT_unconstrained
    (window : SpecWindow) (O : MispredOracle) :
    SpeculativelyConstantTimeM window O pilotLevels (insertMasks pilotKernelLoad) :=
  insertMasks_SCT_unconstrained window O pilotLevels LeafCTTable.canonical
    pilotKernelLoad pilotKernelLoad_cmdCT

/-- `cmdCT` acceptance survives mask insertion on the load kernel. -/
theorem insertMasks_pilotKernelLoad_cmdCT :
    cmdCT (insertMasks pilotKernelLoad) pilotLevels LeafCTTable.canonical = true := by
  native_decide

/-- Masking the load kernel inserts fewer markers than fencing it: the fence
    pass also barriers both branch arms.  Concretely `2 ≤ 4`. -/
theorem pilotKernelLoad_mask_fewer :
    maskMarkerCount pilotKernelLoad ≤ fenceMarkerCount pilotKernelLoad := by
  native_decide

end PilotMask

/-! ## §10.  The mask removes the transient address's state dependence

The unmasked load's transient address is the runtime index, which differs
between the two states below; the masked form's transient address is the
sentinel constant in both. -/

/-- A second state with a different index value. -/
def st2 : RustState :=
  { rsTower := fun _ => none,
    rsScalar := fun s => if s = "idx" then 99 else 0 }

/-- The bare load's transient address is the runtime index, which differs
    between `Sanity.st` (idx = 3) and `st2` (idx = 99). -/
theorem load_unmasked_transient_data_dependent :
    specMaskedTransient Sanity.st (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx")
      ≠ specMaskedTransient st2 (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx") := by
  native_decide

/-- After masking, the transient address is the sentinel constant in both
    states. -/
theorem load_masked_transient_data_independent :
    specMaskedTransient Sanity.st (insertMasks (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx"))
      = specMaskedTransient st2 (insertMasks (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx")) := by
  native_decide

/-- And concretely the masked transient is the sentinel observation. -/
theorem load_masked_transient_is_sentinel :
    specMaskedTransient Sanity.st (insertMasks (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx"))
      = [Obs.memIdx "idx" sentinelAddr] := by
  native_decide

/-! The same masking applies to the store-bypass marker: an unmasked load is
forwarded the word at its runtime index, a masked one the word at the sentinel
address.  The state below holds a one-byte value in the load's source slot, so
word `0` of slot `a` is `9` and word `3` is `0`, and its runtime index is `3`. -/

/-- A state whose heap holds a one-byte value in the load's source slot, with a
    runtime index of `3`. -/
def stArr : RustState :=
  { rsTower := fun x => if x = "a" then some ⟨.TU8, Sanity.byteVal 9⟩ else none,
    rsScalar := fun s => if s = "idx" then 3 else 0 }

/-- An unmasked load's store-bypass marker carries the word at the load's
    runtime index. -/
theorem load_unmasked_stl_at_runtime_index :
    specObsM 8 Sanity.allFire stArr (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx")
      = [Obs.memIdx "idx" 3, Obs.stlForward "a" 0, Obs.rollback] := by
  native_decide

/-- A masked load's store-bypass marker carries the word at the sentinel
    address. -/
theorem load_masked_stl_at_sentinel :
    specObsM 8 Sanity.allFire stArr
        (insertMasks (.RArrLoad ⟨"d", .TU64⟩ ⟨"a", .TU64⟩ "idx"))
      = [Obs.memIdx "idx" 3, Obs.stlForward "a" 9, Obs.rollback] := by
  native_decide

/-! ## §11.  What the pass delivers

**In this file.**
* `maskAddr`, the address-masking primitive: under the misprediction predicate
  the load address is forced to `sentinelAddr`, with `maskAddr_true_const` the
  statement that the masked address does not depend on the true one.
* `insertMasks : LowCT → LowCT`, placing an `RMask` before every load and
  nothing at branch heads, calls, or stores.
* `archObs_insertMasks` and `cmdCT_insertMasks`: the mask marker is an `RAssert`
  no-op, so the architectural leakage trace and `cmdCT` acceptance are
  unchanged.
* `specObsM` and `specMaskedTransient`: a mis-speculated masked load issues the
  sentinel address rather than the runtime one, and its store-bypass marker
  carries the word read at that masked address.
* `specObsM_insertMasks_eq` and `insertMasks_SCT_unconstrained`: a
  `cmdCT`-accepted program, once mask-hardened, has equal `specObsM` traces on
  `PublicEquiv` states, for every window and every oracle.  Applied to
  `PilotMask.pilotKernelLoad`.  `load_unmasked_transient_data_dependent` and
  `load_masked_transient_data_independent` compute the transient address with
  and without the mask; `load_unmasked_stl_at_runtime_index` and
  `load_masked_stl_at_sentinel` compute the forwarded word.
* `insertMasks_subsumes_fewer_sites`: `maskMarkerCount c ≤ fenceMarkerCount c`.

**Scope.**
* The masked clauses are the load-address ones.  The call-site markers are left
  to `SpeculativeCTFence.insertFences`; a pass that masks loads and guards
  call sites is the composition of the two.
* The mask is blanket over loads.  A taint-directed subset is the selective
  variant.
* The mask's effect is modelled directly, as the sentinel under misprediction,
  rather than by threading a mask register through the operational semantics.
* `RMask` is a `LowCT.RAssert` label that only `specObsM` reads.  Over
  `SpeculativeCTStoreBuffer.specRun` the pass is the identity
  (`SpeculativeCTStoreBufferPasses.specRun_insertMasks`), and
  `insertMasks_not_SCT_SB` there exhibits a `cmdCT`-accepted command whose
  masked image separates two `PublicEquiv` states. -/

end CatCrypt.Crypto.SecureCompilation.SpeculativeCT
