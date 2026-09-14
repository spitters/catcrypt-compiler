/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3CompressEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HashLeafEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScfDialect
public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront

/-!
# Spartan / Jolt BabyBear sum-check FIELD-CORE whole-prover as owned control flow

This is the `Plonky3OrchLoopsEmit` pattern applied to the **Spartan and
Jolt sum-check field core**: compose the already-emitted owned BabyBear phase
leaves into ONE `.s` whose per-round orchestration is an owned `loopLcmd`
back-edge (no jasminc, no C `for`).

## Why this composes the SAME owned leaves as Plonky3

Spartan's and Jolt's prover hot path is a multi-round sum-check. Each round:

* `round_eval(rpoly, α)` — a Horner fold `acc ← α·acc + cᵢ` over BabyBear, i.e.
  the fused Barrett mul-add the owned `Plonky3FriFoldEmit.friFoldCom` leaf
  already emits (`friFold = bbAdd (bbMul …) …`, the `friFold_is_regarith_only`
  owned regArith leaf). Jolt's Lasso grand product `∏(τ − x)` is the same
  `bbMul`/`bbSub` fold.
* the Fiat–Shamir challenger `squeeze` is a Poseidon2 sponge — the SAME owned
  `Plonky3HashLeafEmit.hashLeafCom` / `Plonky3CompressEmit.compressComFinal`
  Poseidon2 BabyBear leaves the Plonky3 prover commits / squeezes with.
* the BabyBear field inverse used in the round-poly normalisation is the owned
  `Plonky3FriFoldEmit.bbInvCom` Fermat chain.

`EmittedSumCheckRealization.lean` (Spartan + Jolt) ties `bbHornerEval` /
`bbGrandProduct` over these BabyBear kernels to `UnivariatePoly.eval` /
`multisetPoly.eval`, the evaluators the Schwartz–Zippel / Lasso soundness arc
quantifies over — so the **field core** these owned leaves compute is exactly
the sum-check field core both provers' soundness lands on.

The owned leaves are reconstructed here exactly as `Plonky3EmitMain` /
`Plonky3WholeProverEmit` build them (same `Com`, same ABI maps) — they are
**not re-emitted**, only composed. The reconstruction is inlined here rather
than imported from `Plonky3WholeProverEmit` so this module's import closure
carries no root-namespace `main`.

## What this composes vs the residual

* COMPOSED (owned single-`.s`): the BabyBear sum-check FIELD CORE — the per-round
  Horner round-eval loop (`friFold`), the Poseidon2 Fiat–Shamir challenger
  (`hashLeaf`/`compress`), the BabyBear inverse (`bbInv`) — plus the owned
  `loopLcmd` per-round orchestration. One emitted object, prove-path control
  flow owned (`.L:/cmp/jne`), no jasminc, no C `for`. This is the part of
  Spartan/Jolt that uses the same owned regArith backend as Plonky3.
* RESIDUAL (not owned-emittable here): the **PCS commitment MSM** — Spartan's
  Hyrax 4×4 Ed25519/Ristretto commit + dot-product-opening IPA (#429/#431/#435),
  Jolt's PCS commit. That is curve-group arithmetic, not BabyBear regArith; the
  existing whole-prover benches (`bench/spartan_compare/spartan_prover_prod_kat.c`)
  run it over the verified-field/trusted-group curve leaf (HACL* / GMP C), NOT
  the owned x86 regArith backend, which has no curve-group emit. Composing the
  curve MSM into this owned `.s` is **blocked on the curve backend**, out of
  scope for the BabyBear field-core composition. The whole-prover number that
  INCLUDES the curve MSM is therefore the jasminc+C `spartan_prover_prod_kat`
  binary, NOT a single owned `.s`; this module composes only the owned
  field-core half, and the doc marks the curve-MSM orchestration as the precise
  gap.

So: the owned single-`.s` here is a **field-core whole-prover** (the
sum-check + FS half), and the per-prover apples-to-apples whole-prover number
that includes the PCS curve MSM stays the documented jasminc+C prod-KAT figure,
with the curve-MSM-not-owned-emitted gap named.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ZkSumCheckWholeProverEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
  (loopLcmd unrollLcmd loopLcmd_length unrollLcmd_length looped_shorter_than_unrolled occursIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLfundef renderLprogAtt renderLinstrR)
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront
  (buildOrchLoop sumcheckSpec)

/-! ## 0. Owned BabyBear phase leaves (mirrors `Plonky3WholeProverEmit`)

Reconstruct the owned BabyBear leaves the sum-check field core calls: the
Poseidon2 FS challenger (`hashLeaf` / `compress`), the Horner round-eval step
(`friFold`, a fused Barrett mul-add), and the BabyBear inverse (`bbInv`). Same
`Com`, same ABI maps as `Plonky3WholeProverEmit` — composed, not
re-emitted. -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The standard `out[0..nOut-1]` store map. -/
def stdOutStore (nOut : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * 8))

/-- Build the `(immSlotMap, inLoadMap)` ABI pair (mirrors the Plonky3 one). -/
def abiMaps (nIn : Nat) (constAt : Nat → Option Nat) : ImmSlotMap × InLoadMap :=
  ( fun s => if s < nIn then constAt (nIn - 1 - s) else none
  , fun s => if s < nIn then
               (let idx := nIn - 1 - s
                if (constAt idx).isNone then some ("RSI", idx * 8) else none)
             else none )

def compressConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 8 ∧ idx ≤ 14 then some (Plonky3CompressEmit.constNat (idx - 8)) else none

/-- Poseidon2 2-to-1 compress — the FS transcript absorb step. -/
def compressLprog : Lprog :=
  let (imm, inl) := abiMaps 15 compressConstAt
  Com.toLprogPhysAbi Plonky3CompressEmit.compressComFinal
    "zk_poseidon2_compress_rc" (fun _ => none) imm inl (stdOutStore 4)

def hashLeafConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 1 ∧ idx ≤ 7 then some (Plonky3HashLeafEmit.constNat (idx - 1)) else none

/-- Poseidon2 leaf-hash — the FS challenger squeeze step. -/
def hashLeafLprog : Lprog :=
  let (imm, inl) := abiMaps 8 hashLeafConstAt
  Com.toLprogPhysAbi Plonky3HashLeafEmit.hashLeafCom
    "zk_poseidon2_squeeze_rc" (fun _ => none) imm inl (stdOutStore 4)

def friConstAt (idx : Nat) : Option Nat :=
  if idx = 4 then some 1006632961
  else if idx = 5 then some 2
  else if idx = 6 then some 1
  else if idx = 7 then some 2290649223
  else if idx = 8 then some 2013265921
  else if idx = 9 then some 0
  else if idx = 10 then some 30
  else if idx = 11 then some 32
  else if idx = 12 then some 63
  else none

/-- BabyBear fused mul-add (`a·b + c`) — the Horner sum-check round-eval step
    (`acc ← α·acc + cᵢ`) AND the Lasso grand-product step. The owned
    `friFoldCom` regArith leaf. -/
def roundEvalLprog : Lprog :=
  let (imm, inl) := abiMaps 16 friConstAt
  Com.toLprogPhysAbi Plonky3FriFoldEmit.friFoldCom
    "zk_sumcheck_round_step_rc" (fun _ => none) imm inl (stdOutStore 1)

/-- BabyBear inverse (Fermat chain) — round-poly normalisation. -/
def bbInvLprog : Lprog :=
  let (imm, inl) := abiMaps 16 friConstAt
  Com.toLprogPhysAbi Plonky3FriFoldEmit.bbInvCom
    "zk_bb_inv_rc" (fun _ => none) imm inl (stdOutStore 1)

/-- The owned BabyBear field-core leaf set: Poseidon2 compress + squeeze, the
    Horner round step, and the BabyBear inverse — one `Lprog`. -/
def fieldCoreLprog : Lprog :=
  { compressLprog with
    lp_funcs :=
      compressLprog.lp_funcs
        ++ hashLeafLprog.lp_funcs
        ++ roundEvalLprog.lp_funcs
        ++ bbInvLprog.lp_funcs }

/-! ## 1. The sum-check orchestration loop (mirrors `Plonky3OrchLoopsEmit`)

Each sum-check round issues: the round-eval step (`call zk_sumcheck_round_step_rc`)
then the FS challenger squeeze (`call zk_poseidon2_squeeze_rc`), advances the
round-poly / transcript pointers, and decrements the round counter. Pure
pointer / counter arithmetic around the leaf calls — no field op (the field
arithmetic is entirely in the called BabyBear leaves). `loopLcmd` wraps it in
the owned back-edge.

The emitted leaves take `(out, in)` in `%rdi`/`%rsi` and CONSUME those registers
(they save them to their own frame and clobber the live copies, restoring only
the callee-saved set `%rbx,%rbp,%r12,%r13,%r14,%r15` before `ret`). Since the
body issues TWO leaf calls per round, it keeps the out / in base pointers in the
callee-saved `%r12` / `%r13` (which the leaves restore), reloads `%rdi`/`%rsi`
from them before each call, and advances the BASES (`%r12`/`%r13`) — so each
leaf sees a fresh, correct pointer pair and the loop is runnable as
one linked object. -/

/-- A direct near-`call` to an emitted phase-leaf symbol — the per-round
    field-kernel invocation (`LinstrR.Lcall none (name, 0)` ⇒ `call name`). -/
def leafCall (name : String) : LinstrR := .Lcall none (name, 0)

/-- One sum-check round body. The out / in base pointers live in the
    callee-saved `%r12` / `%r13` (leaves restore them). Each round:
    reload `%rdi`/`%rsi` from the bases, call the round-eval step; reload again,
    call the FS squeeze; advance the out base by `strideOut` and the in base by
    `strideIn`; decrement the public round counter `%r8`. -/
def sumcheckRoundBody (strideOut strideIn : Nat) : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDI"] "MOV:64" [.reg "R12"]⟩
  , ⟨0, .Lopn [.reg "RSI"] "MOV:64" [.reg "R13"]⟩
  , ⟨0, leafCall "zk_sumcheck_round_step_rc"⟩
  , ⟨0, .Lopn [.reg "RDI"] "MOV:64" [.reg "R12"]⟩
  , ⟨0, .Lopn [.reg "RSI"] "MOV:64" [.reg "R13"]⟩
  , ⟨0, leafCall "zk_poseidon2_squeeze_rc"⟩
  , ⟨0, .Lopn [.reg "R12"] "ADD:64" [.reg "R12", .imm strideOut]⟩
  , ⟨0, .Lopn [.reg "R13"] "ADD:64" [.reg "R13", .imm strideIn]⟩
  , ⟨0, .Lopn [.reg "R8"] "SUB:64" [.reg "R8", .imm 1]⟩ ]

/-- The looped sum-check orchestration: `sumcheckRoundBody` wrapped once by
    `loopLcmd` at width 64, counter `%r8`, top label `0`. Constant-size in the
    round count. -/
def sumcheckLoop (strideOut strideIn : Nat) : Lcmd :=
  loopLcmd 64 0 "R8" (sumcheckRoundBody strideOut strideIn)

/-- The sum-check orchestration driver function: seed the out / in base pointers
    `%r12` / `%r13` from the SysV args `%rdi` / `%rsi`, load the round count `n`
    into `%r8` (`MOV r8, #n`), then the looped body. -/
def sumcheckLoopFundef (n strideOut strideIn : Nat) : Lfundef :=
  buildOrchLoop (sumcheckSpec n strideOut strideIn)

/-- **Provenance (byte-identical).** The deployed `sumcheckLoopFundef` IS the
    `OrchFront` loop-over-call front's output at `sumcheckSpec` — the two-call
    round body with callee-saved base reload is a generated schedule wrapped by
    the verified `loopLcmd` back-edge, not a hand-authored `Lcmd` literal.
    Definitional, so the emitted `.s` is byte-unchanged from the earlier
    hand-authored `⟨MOV⟩ :: ⟨MOV⟩ :: ⟨MOV⟩ :: sumcheckLoop` body. -/
theorem sumcheckLoopFundef_eq_buildOrchLoop (n strideOut strideIn : Nat) :
    sumcheckLoopFundef n strideOut strideIn
      = buildOrchLoop (sumcheckSpec n strideOut strideIn) := rfl

/-- Spartan two-phase R1CS sum-check (#431): phase 1 is `num_rounds_x = 4` cubic
    rounds, phase 2 `num_rounds_y = 5` quad rounds — 9 rounds total. Each round
    writes a 1-word folded evaluation (8-byte output advance); the round-poly row
    is 4 coefficients = 32 bytes. -/
def spartanSumcheckLoop : Lfundef := sumcheckLoopFundef 9 8 32

/-- Jolt sum-check (n=3 toy R1CS in the emit, |M| lookups folded by the Lasso
    grand product). Same owned round step + FS squeeze loop. -/
def joltSumcheckLoop : Lfundef := sumcheckLoopFundef 3 8 32

/-! ## 2. The composed field-core whole-prover `Lprog`: leaves + orchestration

One `.s` carrying the owned BabyBear leaves (compress, squeeze, round step,
bb_inv) AND the two sum-check orchestration-loop drivers (Spartan two-phase,
Jolt) — the prove-path control flow is owned `loopLcmd` back-edges, no jasminc,
no C `for`. -/

/-- The sum-check orchestration-loop driver functions, each a `loopLcmd` whose
    body `Lcall`s the owned BabyBear round step + Poseidon2 FS squeeze. -/
def sumcheckLoopFuncs : List (String × Lfundef) :=
  [ ("spartan_sumcheck_loop", spartanSumcheckLoop)
  , ("jolt_sumcheck_loop", joltSumcheckLoop) ]

/-- The field-core whole-prover `Lprog`: the four owned BabyBear leaf functions
    PLUS the two sum-check orchestration-loop drivers. One emitted object whose
    sum-check field-core orchestration is owned control flow. -/
def fieldCoreWholeProverLprog : Lprog :=
  { fieldCoreLprog with
    lp_funcs := fieldCoreLprog.lp_funcs ++ sumcheckLoopFuncs }

def fieldCoreWholeProverAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned fieldCoreWholeProverLprog

/-! ## 3. Shape lemmas: the orchestration loops are the owned back-edge -/

/-- The sum-check round body is the constant-size `loopLcmd` body: 9 body ops
    (2 pointer reloads + round step + 2 reloads + FS squeeze + 2 base advances +
    counter decrement) + 3 control ops (label, cmp, back-edge) = 12. Independent
    of the round count. -/
theorem sumcheckLoop_length (so si : Nat) :
    (sumcheckLoop so si).length = 12 := by
  rw [sumcheckLoop, loopLcmd_length]; rfl

/-- The looped sum-check emission is strictly shorter than the unrolled one for
    the real round counts (`n ≥ 4`): owned-loop is `O(1)`, unrolled `O(n)`. -/
theorem sumcheckLoop_shorter_than_unrolled (so si n : Nat) (hn : 4 ≤ n) :
    (sumcheckLoop so si).length < (unrollLcmd n (sumcheckRoundBody so si)).length :=
  looped_shorter_than_unrolled 64 0 "R8" (sumcheckRoundBody so si) n hn
    (by simp [sumcheckRoundBody])

/-- The sum-check loop body calls the round-eval step after the loop label and
    the two `%rdi`/`%rsi` reloads (index 3), then the FS challenger squeeze. -/
theorem sumcheckLoop_calls_round_step (so si : Nat) :
    (sumcheckLoop so si)[3]? = some ⟨0, leafCall "zk_sumcheck_round_step_rc"⟩ := by
  rfl

/-! ## 4. The composed object carries every owned leaf AND every loop -/

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-- The composed function list is exactly the owned field-core leaves followed by
    the two sum-check orchestration-loop drivers — adds the loops, drops no leaf. -/
theorem fieldCore_funcs_eq :
    fieldCoreWholeProverLprog.lp_funcs = fieldCoreLprog.lp_funcs ++ sumcheckLoopFuncs :=
  rfl

/-- The composed object adds exactly the two sum-check loop functions on top of
    the four owned field-core leaves. -/
theorem fieldCore_func_count :
    fieldCoreWholeProverLprog.lp_funcs.length
      = fieldCoreLprog.lp_funcs.length + 2 := by
  simp [fieldCoreWholeProverLprog, sumcheckLoopFuncs, List.length_append]

/-! ## 5. Emit driver -/

/-- Write the single composed field-core whole-prover `.s` (owned BabyBear leaves
    + owned sum-check orchestration loops) into the bench harness directory. One
    object, owned x86 backend, NO jasminc. -/
def emitMain : IO Unit := do
  let dir := "bench/spartan_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/zk_sumcheck_fieldcore_whole_prover_owned.s")
    fieldCoreWholeProverAsm
  IO.println "WROTE bench/spartan_compare/gen_com/zk_sumcheck_fieldcore_whole_prover_owned.s"
  IO.println "  ONE .s: owned BabyBear leaves (compress/squeeze/round-step/bb_inv)"
  IO.println "  + owned sum-check orchestration loops (Spartan two-phase, Jolt), loopLcmd back-edges"
  IO.println "  Spartan+Jolt sum-check FIELD CORE, owned x86 backend, NO jasminc"
  IO.println "  not included: the polynomial-commitment multi-scalar multiplication over the curve"

end CatCrypt.Crypto.SecureCompilation.VIR.ZkSumCheckWholeProverEmit
