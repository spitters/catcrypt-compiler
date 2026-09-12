/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresMachineTie
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeCtrl
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeMem

/-!
# The control and memory middle ties as `SimTie` instances

`CorresMachineTie` states the cross-machine forward simulation `SimTie` once and
instantiates it at the **arithmetic** fragment (`simTie_arith`,
`simTie_arith_seq`).  The control (`CorresBridgeCtrl`) and memory
(`CorresBridgeMem`) middle ties, however, were phrased directly against
`semScalar`/`runBlock` and sat outside the combinator.  This module brings both
under `SimTie`, so all three fragments — arithmetic, control, memory — are
instances of the same cross-machine simulation.

## Control (`simTie_for`, `simTie_for_of_body`)

`for_middle_tie_gen` is already **env-general**: it takes an arbitrary starting
env agreeing with the machine state on non-temp names (`nonTmpAgree`), which is
*definitionally* the arithmetic `SimTie`'s state relation `midTieR`
(`nonTmpAgree_eq_midTieR`).  So a bounded for-loop is a `SimTie` directly:
`simTie_for` feeds `for_middle_tie_gen`, the `runBlockStep` side being `rfl`.
The clean unification is `simTie_for_of_body`: a **loop `SimTie` built from a body
`SimTie`** — given the body ties (`SimTie … bodyS bodyM`) and a temp loop counter
(`isTmpName x`), the whole loop ties, the counter bind landing on a temp slot the
readout ignores (`nonTmpAgree_upd_tmp`).

## Memory (`mem_load_step_gen`, `simTie_memLoad`)

`mem_load_middle_tie_at_dst` starts from the specific env `regMemEnv st …`, so it
is not yet a `SimTie` (which quantifies over any `R`-related env).
`mem_load_step_gen` **generalizes** it — mirroring `arith_step_tie_gen`'s
generalization of `arith_middle_tie_at_dst` — to any env agreeing with
`regMemEnv st …` on non-temp names, re-establishing that agreement on the
post-state (a load leaves memory and every non-`dst` register untouched, so the
memref-region agreement and the register agreement both survive).  `simTie_memLoad`
is then the `SimTie` at the memory relation `memLoadR` (regMemEnv-style agreement
plus the in-range index invariant a load preserves).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (semScalar SEnvScalar isTmpName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx (idRho)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT (MemLoadSrc lowerMemLoad)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote (runBlock_lowerMemLoad)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll (unrollBounded)

/-! ## Control: the bounded for-loop as a `SimTie` -/

/-- The control-tie invariant `nonTmpAgree` (non-temp register agreement) is
    definitionally the arithmetic `SimTie`'s state relation `midTieR`: both say
    the scalar env agrees with the machine register file at `.sword 64` on every
    non-temp name.  So the control tie can be stated over the same `midTieR`
    relation as the arithmetic tie — the unification. -/
theorem nonTmpAgree_eq_midTieR : nonTmpAgree = midTieR := rfl

/-- **The bounded for-loop is a `SimTie`.**  Given the body's per-iteration tie
    (`hbody`, the hypothesis `for_middle_tie_gen` consumes), the whole loop
    `RFor x N bodyS` ties to the unrolled machine block `unrollBounded N bodyM`
    under the `midTieR` state relation.  The `runBlockStep` side of `SimTie` is
    `rfl` (`runBlockStep c st = some (runBlock st c)`), so this is exactly
    `for_middle_tie_gen` repackaged as a `SimTie`. -/
theorem simTie_for (x : String) (bodyS : LowCT) (bodyM : List (JInstr 64)) (N : Nat)
    (hbody : ∀ (n : Nat) (env : SEnvScalar) (stM : JState 64),
        midTieR env stM →
        ∃ env1, semScalar bodyS (env.upd x (t := .sword 64) (BitVec.ofNat 64 n)) = some env1
          ∧ midTieR env1 (runBlock stM bodyM)) :
    SimTie semScalar runBlockStep midTieR (.RFor x N bodyS) (unrollBounded N bodyM) := by
  intro env st hR
  obtain ⟨env', hsem, hag⟩ := for_middle_tie_gen x bodyS bodyM hbody N st env hR
  exact ⟨env', runBlock st (unrollBounded N bodyM), hsem, rfl, hag⟩

/-- **The clean unification: a loop `SimTie` from a body `SimTie`.**  If the body
    ties (`hbody : SimTie … bodyS bodyM`) and the loop counter `x` is a fresh temp
    (`isTmpName x`), then the whole bounded loop ties.  Each trip binds `x := n`;
    since `x` is a temp, `nonTmpAgree_upd_tmp` shows the counter bind preserves the
    non-temp agreement the body `SimTie` consumes, and the body `SimTie` re-runs on
    the counter-bound env.  The `runBlockStep` output is `runBlock stM bodyM` by
    `Option.some.injEq`, matching the body-agnostic loop tie's expectation. -/
theorem simTie_for_of_body (x : String) (bodyS : LowCT) (bodyM : List (JInstr 64)) (N : Nat)
    (hx : isTmpName x)
    (hbody : SimTie semScalar runBlockStep midTieR bodyS bodyM) :
    SimTie semScalar runBlockStep midTieR (.RFor x N bodyS) (unrollBounded N bodyM) := by
  apply simTie_for
  intro n env stM hag
  obtain ⟨env1, st1, hsem, hstep, hrel⟩ :=
    hbody (env.upd x (t := .sword 64) (BitVec.ofNat 64 n)) stM
      (nonTmpAgree_upd_tmp env stM x hx (BitVec.ofNat 64 n) hag)
  refine ⟨env1, hsem, ?_⟩
  rw [runBlockStep, Option.some.injEq] at hstep
  exact hstep ▸ hrel

/-! ## Memory: the array-load as a `SimTie` -/

/-- **The memory-load state relation.**  `env` agrees with the memory-inclusive
    view `regMemEnv st m.arr n m.scale` on every non-temp name (the register file
    at `.sword 64`, and the array region as a `.memref n` byte-offset view of
    `st.mem`), **and** the index register is in range (`(st.regs m.idx).toNat < n`)
    — the invariant a load preserves and that lets `memGetDyn`'s modulo collapse to
    the raw machine cell.  The memory analogue of `midTieR`. -/
def memLoadR (m : MemLoadSrc) (n : Nat) (env : SEnvScalar) (st : JState 64) : Prop :=
  (∀ v, ¬ isTmpName v → env v = regMemEnv st m.arr n m.scale v)
    ∧ (st.regs m.idx).toNat < n

/-- A load leaves the memory-inclusive view unchanged on every name other than the
    destination register: memory is untouched (so the `.memref` region slot is
    preserved) and every non-`dst` register is untouched. -/
theorem regMemEnv_lowerMemLoad_of_ne (m : MemLoadSrc) (st : JState 64) (n : Nat)
    (v : String) (hvd : v ≠ m.dst) :
    regMemEnv (runBlock st [lowerMemLoad idRho m]) m.arr n m.scale v
      = regMemEnv st m.arr n m.scale v := by
  rw [runBlock_lowerMemLoad]
  by_cases hva : v = m.arr
  · subst hva; simp [regMemEnv, idRho, JState.setReg]
  · simp [regMemEnv, idRho, JState.setReg, hva, hvd]

/-- **Generalized memory-load middle tie.**  For ANY env agreeing with
    `regMemEnv st m.arr n m.scale` on non-temp names (not just that view itself),
    `semScalar` succeeds on the real `RArrLoad` node and its result agrees with
    `regMemEnv` of the machine post-state on every non-temp name.  The array region
    and index register are non-temp (`harr_nt`/`hidx_nt`, so the view supplies the
    memref slot and index value), the destination is a `u64` distinct from both the
    array region (`hdst`/`hdst_ne`) and — implicitly through the caller — the index,
    and the index is in range (`hidx_lt`).  The memory analogue of
    `arith_step_tie_gen`: it starts from an arbitrary agreeing env, so it maps to a
    `SimTie`. -/
theorem mem_load_step_gen (m : MemLoadSrc) (st : JState 64) (n : Nat) (env : SEnvScalar)
    (hdst : m.dstTy = .TU64) (hidx_ne : m.idx ≠ m.arr) (hdst_ne : m.dst ≠ m.arr)
    (harr_nt : ¬ isTmpName m.arr) (hidx_nt : ¬ isTmpName m.idx)
    (hidx_lt : (st.regs m.idx).toNat < n)
    (hagree : ∀ v, ¬ isTmpName v → env v = regMemEnv st m.arr n m.scale v) :
    ∃ env', semScalar (MemLoadSrc.toLowCT m) env = some env'
      ∧ ∀ v, ¬ isTmpName v →
          env' v = regMemEnv (runBlock st [lowerMemLoad idRho m]) m.arr n m.scale v := by
  have hArr : env m.arr = some ⟨.memref n, fun j : Fin n => st.mem m.arr (m.scale * j.val)⟩ :=
    (hagree m.arr harr_nt).trans (regMemEnv_region st m.arr n m.scale)
  have hIdx : env m.idx = some ⟨.sword 64, st.regs m.idx⟩ :=
    (hagree m.idx hidx_nt).trans (regMemEnv_reg st m.arr n m.scale m.idx hidx_ne)
  refine ⟨env.upd m.dst (t := .sword 64)
      (memGetDyn (fun j : Fin n => st.mem m.arr (m.scale * j.val)) (st.regs m.idx).toNat),
      ?_, ?_⟩
  · -- `semScalar` reduces along the destination-type guard + the two known lookups.
    simp only [MemLoadSrc.toLowCT, semScalar, hdst, hArr, hIdx]
  · intro v hv
    by_cases hvd : v = m.dst
    · subst hvd
      rw [regMemEnv_reg _ m.arr n m.scale m.dst hdst_ne]
      have hget : (runBlock st [lowerMemLoad idRho m]).regs m.dst
          = (runBlock st [lowerMemLoad idRho m]).get (idRho m.dst) := rfl
      rw [hget, runBlock_lowerMemLoad_get]
      simp only [SEnvScalar.upd, if_pos]
      rw [memGetDyn_regionArr st m.arr n m.scale (st.regs m.idx).toNat hidx_lt]
    · rw [SEnvScalar.upd, if_neg hvd, hagree v hv, regMemEnv_lowerMemLoad_of_ne m st n v hvd]

/-- **The array-load is a `SimTie`.**  Under the memory relation `memLoadR`
    (regMemEnv-style agreement + in-range index), the real `RArrLoad` node ties to
    the lowered machine gather `[lowerMemLoad idRho m]`.  The step succeeds
    (`mem_load_step_gen`), the `runBlockStep` side is `rfl`, and the post-state is
    again `memLoadR`-related: the agreement is re-established by `mem_load_step_gen`,
    and the in-range index survives because a load never writes the index register
    (`m.dst ≠ m.idx`).  The memory fragment brought under the same cross-machine
    combinator as the arithmetic and control fragments. -/
theorem simTie_memLoad (m : MemLoadSrc) (n : Nat)
    (hdst : m.dstTy = .TU64) (hidx_ne : m.idx ≠ m.arr) (hdst_ne : m.dst ≠ m.arr)
    (hdst_ne_idx : m.dst ≠ m.idx)
    (harr_nt : ¬ isTmpName m.arr) (hidx_nt : ¬ isTmpName m.idx) :
    SimTie semScalar runBlockStep (memLoadR m n)
      (MemLoadSrc.toLowCT m) [lowerMemLoad idRho m] := by
  intro env st hR
  obtain ⟨hagree, hrange⟩ := hR
  obtain ⟨env', hsem, hpost⟩ :=
    mem_load_step_gen m st n env hdst hidx_ne hdst_ne harr_nt hidx_nt hrange hagree
  refine ⟨env', runBlock st [lowerMemLoad idRho m], hsem, rfl, hpost, ?_⟩
  -- the load leaves the index register untouched (`m.idx ≠ m.dst`), so it stays in range.
  have hidx_pres : (runBlock st [lowerMemLoad idRho m]).regs m.idx = st.regs m.idx := by
    rw [runBlock_lowerMemLoad]
    simp only [idRho, id_eq, JState.setReg]
    exact if_neg hdst_ne_idx.symm
  rw [hidx_pres]
  exact hrange

end CatCrypt.Crypto.SecureCompilation.Ascent
