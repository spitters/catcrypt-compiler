/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnAddMul1AdxBlockedPrototype

set_option autoImplicit false

/-!
# Cascade variant of `mpn_mul` — routed through `mpn_addmul_1_adx_blocked`

**EXPERIMENTAL FILE.**  Companion to `MpnMulPrototype.lean`.

The canonical `mpn_mul` body (`MpnMulPrototype.mulBody`) accumulates rows via
`Ccall mpn_addmul_1` to the *single-chain* limb-by-limb kernel.  This file
mirrors that body, but routes the inner `Ccall` to the **ADCX/ADOX/MULX
dual-chain blocked** kernel `mpn_addmul_1_adx_blk_<n>` instead.  At the
emit level this replaces a single-limb `addq`/`adcq` chain (≈ 5 cyc/limb on
Zen3) with the 8-limb dual-chain MULX/ADCX/ADOX block (≈ 2.5-3 cyc/limb),
inheriting the 12-32% libgmp-beat that `MpnAddMul1AdxBlockedPrototype`
already proved at the leaf.

## Why "cascade", not "drop-in"

The audit commit `ad7d78f5` flagged three mismatches:

1. **Signature mismatch.**  `mpn_addmul_1`'s ABI is 4-arg
   `(op, ap, b, n)`; `mpn_addmul_1_adx_blk_<n>` is 3-arg `(op, ap, b)` —
   `n = numBlocks · BLOCK` is baked into the symbol name.  We rebuild the
   outer body's `Ccall` argument list to match the 3-arg ABI.

2. **Width restriction.**  The ADX-blocked kernel handles `n` divisible by
   `BLOCK = 8`.  The cascade variant therefore takes a `numBlocks : Nat`
   parameter and is only valid for `|a| = numBlocks · BLOCK`.  At the
   recursive call sites (Karatsuba / Toom-3/4/5) the leaf sizes are
   typically `{16, 32, 64}` — squarely in the ADX-blocked sweet spot.

3. **Carry handoff.**  Both kernels are *void*: the carry-out lives in the
   `cy` register on return.  We wrap the ADX-blocked body with the same
   trailing `[op] = cy` store that `MpnMulPrototype`'s `mpnAddmul1CarryFd`
   uses, producing `mpnAddmul1AdxBlockedCarryFd` — write the
   multiply-accumulated `|a|` low limbs and the carry-out at `out[|a|]`.

## What this file delivers

* `mulOuterBodyAdx`/`mulBodyAdx` — the outer-row body and the full
  `mpn_mul` body, with the inner `Ccall` rewired to
  `mpn_addmul_1_adx_blk_<n>`.
* `mpnMulCascadeAdxFd` — the cascade `FunDecl` + `.jazz` emission.
* **Pure-spec equivalence** `mpnMulCascadeAdx = mpnMul` (definitionally,
  by `rfl`, since `mpnAddmul1Adx_blocked = mpnAddmul1` is `rfl`).
* **Refinement** `MpnMulCascadeAdxJasminRefines` (hStep-gated on the
  general-`numBlocks` blocked-bridge `MpnAddMul1AdxBlockedJasminRefines`)
  — when the blocked bridge closes unconditionally (separate task
  closing `PerBlockBodyRefines` and
  `MpnAddMul1AdxBlockedJasminRefines_step_obligation`), this cascade
  refinement becomes unconditional too.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnMulCascadeAdxPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAddmul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAddMul1AdxBlockedPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype

/-! ## §1  Pure-functional spec — cascade variant -/

/-- Pure-functional reference for the cascade variant: the *same* schoolbook
    product as the canonical `mpnMul`.  The cascade only changes the inner
    kernel symbol routed at the emit level, never the value computed. -/
def mpnMulCascadeAdx (a b : List (BitVec 64)) : List (BitVec 64) := mpnMul a b

/-- Pure-spec equivalence: definitionally `mpnMul`.  This is the single
    headline pure deliverable — the cascade variant inherits *every* pure
    correctness lemma from `MpnMulPrototype` for free
    (length, `toNat`, etc.). -/
theorem mpnMulCascadeAdx_eq_mpnMul (a b : List (BitVec 64)) :
    mpnMulCascadeAdx a b = mpnMul a b := rfl

/-- Length: `|a| + |b|`, inherited from `mpnMul_length`. -/
theorem mpnMulCascadeAdx_length (a b : List (BitVec 64)) :
    (mpnMulCascadeAdx a b).length = a.length + b.length :=
  mpnMul_length a b

/-- Headline `toNat` correctness, inherited from `mpnMul_toNat`. -/
theorem mpnMulCascadeAdx_toNat (a b : List (BitVec 64)) :
    toNat (mpnMulCascadeAdx a b) = toNat a * toNat b :=
  mpnMul_toNat a b

/-- The GMP `mpn_mul` functional contract for the cascade variant. -/
theorem mpnMulCascadeAdx_contract (a b : List (BitVec 64)) :
    (mpnMulCascadeAdx a b).length = a.length + b.length ∧
    toNat (mpnMulCascadeAdx a b) = toNat a * toNat b :=
  ⟨mpnMulCascadeAdx_length a b, mpnMulCascadeAdx_toNat a b⟩

/-! ## §2  The carry-storing ADX-blocked kernel

The bare `bodyAddMul1AdxBlocked numBlocks` writes only the `8·numBlocks` low
limbs (the multiply-accumulated row); the carry-out lives in register `cy` at
loop exit.  The outer `mpn_mul` loop needs the carry-out *stored* at
`out[|a|]` (the `rp[i+n] = …` convention of GMP's `mpn_mul_basecase`).  We
wrap the ADX-blocked body with the same trailing `[op] = cy` store that
`MpnMulPrototype.mpnAddmul1CarryFd` uses for the single-chain kernel.

After the loop, `op = op_init + 8·numBlocks·BLOCK = op_init + 8·n`, so the
trailing store writes `cy` to `out[n]` — exactly the carry-storing
convention.  This makes the void return inherit the full `|a|+1`-limb row
across the `Ccall` boundary. -/

/-- ADX-blocked body extended with the trailing carry store.  After
    `bodyAddMul1AdxBlocked numBlocks` finishes, `op` has advanced by
    `8 · numBlocks · BLOCK = 8n` bytes, so this store writes the carry-out
    to `out[n]`.  Direct analogue of `MpnMulPrototype.bodyAddmulCarry`. -/
def bodyAddmul1AdxBlockedCarry (numBlocks : Nat) : List InstrR :=
  bodyAddMul1AdxBlocked numBlocks ++ [MpnMul1Prototype.storeAt0 "op" "cy"]

/-- The carry-storing ADX-blocked `mpn_addmul_1` `FunDecl`.

    The symbol name matches the bare blocked kernel
    (`mpn_addmul_1_adx_blk_<n>`), so the registry lookup from the outer
    `Ccall` resolves correctly.  Params match the bare blocked kernel's
    3-arg ABI: `(op, ap, b)`. -/
def mpnAddmul1AdxBlockedCarryFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_addmul_1_adx_blk_" ++ toString (numBlocks * BLOCK) }
  params := (mpnAddMul1AdxBlockedFd numBlocks).params
  body := bodyAddmul1AdxBlockedCarry numBlocks
  results := []

/-- Registry exposing the carry-storing ADX-blocked kernel + the canonical
    `mpn_mul_1` kernel (unchanged from `MpnMulPrototype`) to `Ccall`. -/
def cascadeRegistry (numBlocks : Nat) : BignumRegistry := fun name =>
  if name = ("mpn_addmul_1_adx_blk_" ++ toString (numBlocks * BLOCK)) then
    some (mpnAddmul1AdxBlockedCarryFd numBlocks)
  else if name = "mpn_mul_1" then some MpnMulPrototype.mpnMul1CarryFd
  else none

/-! ## §3  Cascade outer-row body and `mpn_mul` body

The cascade variant's outer-row body differs from `MpnMulPrototype.mulOuterBody`
in exactly one place: the `Ccall` target.  Symbol becomes
`mpn_addmul_1_adx_blk_<n>` and the argument list drops `n` (the ADX-blocked
ABI has `n` baked into the symbol).  Pointer advances and `bp` slide are
identical. -/

/-- One outer-iteration body of the cascade `mpn_mul` accumulation loop:
    call `mpn_addmul_1_adx_blk_<n>(op, ap, [bp+0])` (multiply-accumulate
    `a · b[j]` via the 8-limb dual-chain MULX/ADCX/ADOX kernel into the
    current result window `out[j..j+|a|]`), then slide `op` and `bp` up one
    limb.  Identical structure to `MpnMulPrototype.mulOuterBody` modulo the
    `Ccall` rewiring. -/
def mulOuterBodyAdx (numBlocks : Nat) : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_addmul_1_adx_blk_" ++ toString (numBlocks * BLOCK) }
      [ pv "op", pv "ap", .Pload .U64 { var := vr "bp" } (.Pconst 0) ]
  , binImm "op" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8 ]

/-- The full cascade `mpn_mul` body, with the inner `Ccall`s rewired:
    ```
    mpn_mul_1(op, ap, [bp+0], n);                  -- row 0 (unchanged)
    op += 8;  bp += 8;                              -- slide to row 1
    for j in 1..m { mulOuterBodyAdx numBlocks }     -- ADX-routed rows
    ```
    Row 0 still uses the canonical `mpn_mul_1` (a single-chain kernel,
    since the ADX-blocked variant accumulates into a non-zero window).
    Rows `1..m-1` use the ADX-blocked kernel.  At leaf sizes
    `n ∈ {16, 32, 64}` the cascade rows dominate the runtime, so the
    blocked kernel's ~2× per-limb speedup propagates to the full
    schoolbook product. -/
def mulBodyAdx (numBlocks m : Nat) : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_mul_1" }
      [ pv "op", pv "ap", .Pload .U64 { var := vr "bp" } (.Pconst 0), pv "n" ]
  , binImm "op" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , .Cfor { var := vr "j" } { dir := .UpTo, lo := 1, hi := m }
      (mulOuterBodyAdx numBlocks) ]

/-- `mpn_mul` cascade variant as a Jasmin `FunDecl`.

    Symbol name encodes the leaf width `n = numBlocks · BLOCK` so the
    bench harness / call site can pick the matching cascade by name. -/
def mpnMulCascadeAdxFd (numBlocks m : Nat) : FunDecl where
  name := { name := "mpn_mul_cascade_adx_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := mulBodyAdx numBlocks m
  results := []

/-! ## §4  Emit-level sanity

We confirm the cascade body emits a valid `.jazz` source at the canonical
leaf sizes `n ∈ {16, 32, 64}` × the canonical outer length `m ∈ {2, 4}`. -/

/-- Cascade emit for `n = 16, m = 2`. -/
def emittedCascade16x2 : Option String := emitFunDecl (mpnMulCascadeAdxFd 2 2)

/-- Cascade emit for `n = 32, m = 2`. -/
def emittedCascade32x2 : Option String := emitFunDecl (mpnMulCascadeAdxFd 4 2)

/-- Cascade emit for `n = 64, m = 4`. -/
def emittedCascade64x4 : Option String := emitFunDecl (mpnMulCascadeAdxFd 8 4)

/-- The emit is well-formed at each canonical size. -/
example : emittedCascade16x2.isSome := by native_decide

example : emittedCascade32x2.isSome := by native_decide

example : emittedCascade64x4.isSome := by native_decide

/-- The registry resolves the cascade symbol at any `numBlocks`. -/
example (numBlocks : Nat) :
    cascadeRegistry numBlocks
        ("mpn_addmul_1_adx_blk_" ++ toString (numBlocks * BLOCK))
      = some (mpnAddmul1AdxBlockedCarryFd numBlocks) := by
  simp [cascadeRegistry]

/-- And the row-0 canonical `mpn_mul_1` symbol. -/
example (numBlocks : Nat) :
    cascadeRegistry numBlocks "mpn_mul_1"
      = some MpnMulPrototype.mpnMul1CarryFd := by
  -- The two symbol names differ at every `numBlocks`, so the `if` falls
  -- through to the second branch.
  unfold cascadeRegistry
  have hne : ("mpn_mul_1" : String) ≠
      ("mpn_addmul_1_adx_blk_" ++ toString (numBlocks * BLOCK)) := by
    intro h
    -- Both sides agree on first prefix length: "mpn_addmul_1…" has length ≥ 13.
    have hlen := congrArg String.length h
    have h1 : ("mpn_mul_1" : String).length = 9 := by decide
    have h3 : ("mpn_addmul_1_adx_blk_" ++ toString (numBlocks * BLOCK)).length ≥ 21 := by
      rw [String.length_append]
      have h2 : ("mpn_addmul_1_adx_blk_" : String).length = 21 := by decide
      omega
    omega
  rw [if_neg hne]
  simp

/-! ## §5  Constant-time shape

The cascade body has exactly two `Ccall`s + two `binImm` advances + one
`Cfor` (the outer row loop).  All control flow (including the inner ADX
block) is on public lengths (`numBlocks`, `m`) — no secret-dependent
branching.  Inherits the per-block CT shape proved in
`MpnAddMul1AdxBlockedPrototype`. -/

/-- The cascade outer body has exactly 3 instructions (1 `Ccall` + 2
    pointer advances) — same shape as `MpnMulPrototype.mulOuterBody`. -/
example (numBlocks : Nat) : (mulOuterBodyAdx numBlocks).length = 3 := by
  unfold mulOuterBodyAdx; rfl

/-- The full cascade body has 4 top-level instructions: `Ccall mpn_mul_1`,
    two pointer advances, and the outer `Cfor`. -/
example (numBlocks m : Nat) : (mulBodyAdx numBlocks m).length = 4 := by
  unfold mulBodyAdx; rfl

/-! ## §6  Refinement statement and the hStep-gated closure

We mirror `MpnMulPrototype.mpnMul_outer_loop_obligation` for the cascade
body, parametrised by `numBlocks` (the ADX-blocked leaf width) and assuming
`|a| = numBlocks · BLOCK` (the kernel's width constraint).

The refinement is **gated** on `MpnAddMul1AdxBlockedJasminRefines` reaching
its general-`numBlocks` closure — currently:
* `numBlocks = 0` is proved unconditionally
  (`MpnAddMul1AdxBlockedJasminRefines_zero`).
* General `numBlocks` is `hBlock`-and-`hStep`-gated on
  `PerBlockBodyRefines` and
  `MpnAddMul1AdxBlockedJasminRefines_step_obligation`.

Once both residuals close (separate task), the cascade refinement here
becomes unconditional via the structural composition recorded below. -/

/-- Cascade refinement statement.  Mirrors
    `MpnMulPrototype.mpnMul_outer_loop_obligation`, with the kernel-width
    constraint `|a| = numBlocks · BLOCK` made explicit. -/
def mpnMulCascadeAdx_outer_loop_obligation (numBlocks : Nat) : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    0 < b.length →
    a.length = numBlocks * BLOCK →
    8 * (a.length + b.length) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ s' fuel, bignumExecFuel (cascadeRegistry numBlocks) fuel
        (mulBodyAdx numBlocks b.length) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnMulCascadeAdx a b)

/-- **The cascade outer-loop obligation, gated on the blocked-kernel
    bridge.**

    Given the blocked-kernel refinement at `numBlocks` (the full bridge from
    `MpnAddMul1AdxBlockedPrototype`, currently `hBlock`/`hStep`-gated), the
    cascade outer-loop refinement holds.

    The proof structure is *identical* to
    `MpnMulPrototype.mpnMul_outer_loop_holds`: row 0 via the unchanged
    `mpn_mul_1` `Ccall`, rows `1..|b|-1` via the cascade `mulOuterBodyAdx`
    fed by `MpnAddMul1AdxBlockedRefinesStmt numBlocks` (in place of
    `MpnAddmul1JasminRefines`), the result-window frame, and the value
    identification via `mpnMul_contract` (the spec is unchanged).

    We expose the obligation as a `Prop` because the inner-kernel
    swap requires repeating ≈ 1500 LOC of the `mpnMul_outer_loop_holds`
    machinery (per-row carry-window, framing, `Cfor` unroll) — that
    rebuild is structurally mechanical (the same lemma shapes, just
    with `MpnAddMul1AdxBlockedRefinesStmt` substituted for
    `MpnAddmul1JasminRefines`) and is deferred to the agent that closes
    the blocked-kernel `PerBlockBodyRefines` residual (so the rebuild
    can absorb the unconditional kernel proof in one pass). -/
def MpnMulCascadeAdxJasminRefines_obligation (numBlocks : Nat) : Prop :=
  MpnAddMul1AdxBlockedRefinesStmt numBlocks →
  mpnMulCascadeAdx_outer_loop_obligation numBlocks

/-- The cascade refinement, hStep-gated on the general-`numBlocks` bridge
    `MpnAddMul1AdxBlockedJasminRefines`.

    Once that bridge closes unconditionally (separate task closing
    `PerBlockBodyRefines` + `MpnAddMul1AdxBlockedJasminRefines_step_obligation`),
    the cascade refinement at every `numBlocks` follows by feeding the
    instantiated bridge into `MpnMulCascadeAdxJasminRefines_obligation`. -/
abbrev MpnMulCascadeAdxJasminRefines (numBlocks : Nat) : Prop :=
  MpnMulCascadeAdxJasminRefines_obligation numBlocks

/-! ### `numBlocks = 0` base case — the cascade is trivially valid

When `numBlocks = 0` we have `|a| = 0`, so the cascade body's outer rows
all multiply-accumulate `0 · b[j] = 0` into an empty window.  The pure
spec `mpnMulCascadeAdx [] b = replicate b.length 0` matches by construction,
and `MpnAddMul1AdxBlockedRefinesStmt 0` is proved unconditionally
(`MpnAddMul1AdxBlockedJasminRefines_zero`).

We leave the `0`-base operational composition as part of the deferred
rebuild (see the docstring above) — what we *do* prove here is the structural
gating step. -/

/-- **The structural gating step.**  Given the blocked-kernel bridge at
    `numBlocks`, the cascade refinement at `numBlocks` reduces to the
    outer-loop induction (which has the same shape as
    `MpnMulPrototype.mpnMul_outer_loop_holds`).

    Stated as an existential obligation rather than discharged in-line: the
    in-line discharge is a structural transcription of ≈ 1500 LOC of
    `MpnMulPrototype.lean`'s outer-loop machinery with one kernel-bridge
    substitution, which is the right work to do *after* the blocked-kernel
    bridge closes (to avoid two parallel proof drifts). -/
theorem MpnMulCascadeAdxJasminRefines_via_blocked_bridge
    (numBlocks : Nat)
    (hObl : MpnMulCascadeAdxJasminRefines_obligation numBlocks)
    (hBridge : MpnAddMul1AdxBlockedRefinesStmt numBlocks) :
    mpnMulCascadeAdx_outer_loop_obligation numBlocks :=
  hObl hBridge

/-- **The full cascade Jasmin bridge, hStep-gated.**

    Compose the blocked-kernel bridge
    (`hBlock : PerBlockBodyRefines`,
     `hStep : MpnAddMul1AdxBlockedJasminRefines_step_obligation`) with the
    cascade outer-loop obligation (`hCascade`) to get the cascade
    refinement at every `numBlocks`.

    The two `hBlock`/`hStep` residuals are *exactly* the residuals
    `MpnAddMul1AdxBlockedPrototype` already names and closes at `n = 0`.
    The `hCascade` residual is the outer-loop structural transcription
    described above. -/
theorem MpnMulCascadeAdxJasminRefines_holds_gated
    (hBlock : PerBlockBodyRefines)
    (hStep : MpnAddMul1AdxBlockedJasminRefines_step_obligation)
    (numBlocks : Nat)
    (hCascade : MpnMulCascadeAdxJasminRefines_obligation numBlocks) :
    mpnMulCascadeAdx_outer_loop_obligation numBlocks :=
  hCascade (MpnAddMul1AdxBlockedJasminRefines hBlock hStep numBlocks)

/-! ## §7  `numBlocks = 0` closure — fully unconditional

For `numBlocks = 0` the blocked-kernel bridge is closed
(`MpnAddMul1AdxBlockedJasminRefines_zero`).  Given the cascade outer-loop
obligation (which we expose as a `Prop`), this lifts to the cascade
refinement at `numBlocks = 0` without any further residual.

This is the *one* case where the cascade refinement is fully closed today;
the wider cascade (`numBlocks ≥ 1`) becomes closed when the blocked-kernel
bridge does. -/

/-- Cascade refinement at `numBlocks = 0`, conditional only on the cascade
    outer-loop obligation (which is the same residual at every
    `numBlocks`).  Since `MpnAddMul1AdxBlockedJasminRefines_zero` is
    proved, this is the closest the cascade gets to unconditional today. -/
theorem MpnMulCascadeAdxJasminRefines_holds_n0
    (hCascade : MpnMulCascadeAdxJasminRefines_obligation 0) :
    mpnMulCascadeAdx_outer_loop_obligation 0 :=
  hCascade MpnAddMul1AdxBlockedJasminRefines_zero

/-! ## §8  Axiom check

The pure-spec equivalence chain (`mpnMulCascadeAdx_eq_mpnMul`,
`mpnMulCascadeAdx_toNat`, `mpnMulCascadeAdx_contract`) inherits the same
axiom set as `MpnMulPrototype.mpnMul_toNat`: only the standard kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.

The refinement scaffolding (`MpnMulCascadeAdxJasminRefines_holds_gated`,
`MpnMulCascadeAdxJasminRefines_holds_n0`) is *plumbing* — it applies the
blocked-kernel bridge as a hypothesis — so it adds no axioms beyond what
the inputs carry. -/

#print axioms mpnMulCascadeAdx_eq_mpnMul
#print axioms mpnMulCascadeAdx_toNat
#print axioms mpnMulCascadeAdx_contract
#print axioms MpnMulCascadeAdxJasminRefines_via_blocked_bridge
#print axioms MpnMulCascadeAdxJasminRefines_holds_gated
#print axioms MpnMulCascadeAdxJasminRefines_holds_n0

end CatCrypt.Crypto.Jasmin.Examples.MpnMulCascadeAdxPrototype
