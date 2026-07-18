/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

-- Foundation: faithful straight-line linear semantics + the linearizer simulation.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
-- Scalar op-set widening (unconditional functional ∧ robust, no carried edge):
-- regConst → non-uniform width + select → imm-shifts → mulhi/addCarry → castW → extCall leaf.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
-- Stack-memory ops (stackLoad/stackStore) over a register-state + array carrier.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
-- Control-flow foundation (labeled, program-indexed, fuel-bounded lsem — for loops/branches).
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
-- Single counted-loop simulation (item 4c): the loop control-flow structure (back-edge Lcond, n-fold
-- iteration, halt-on-fallthrough, public-counter CT) over loopLR = the real loopLcmd MINUS the explicit CMP
-- (loopLR_eq_loopLcmd_dropCmp). Documented gaps: the literal-CMP/flag arm (needs a flag register), and the
-- general JForProg value bridge.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop
-- Front control-flow bridge (item 4d): FrontControlLsem ties the LowCT front RFor/RIfNz RustExec denotations to
-- the REAL emitted loop (4c loopLcmd shape) / Lcond branch (4a/4b labeled lsem). front_control_lsem_correct_and_robust:
-- (loop) front n-fold = emitted loop lsem run + state-independent leak; (branch) front two-branch = emitted Lcond
-- decision + constant [branch] leak. The front↔emitted body tie is the named FrontLoopEncodes.comm edge (carried,
-- like 4c's bodyStep). Public-control-flow CT hypotheses explicit (public trip count / public scrutinee).
import CatCrypt.Crypto.SecureCompilation.VIR.FrontControlLsem
-- Loop fidelity completion (item 4c-full): JasminLsemLoopFlag closes 4c's two gaps. LstateF (additive flag-state
-- wrapping LstateP) + a CMP arm runs the LITERAL loopLcmd (with its explicit CMP, loopProgF/loopLcmdLR), not the
-- CMP-elided loopLR. jforprog_literal_loop_correct_and_robust: the halt accumulator decodes to JForProg.denote
-- (the value tie, via valBodyStep + JForProgCT.StepAgrees) over the REAL emitted loop, AND the flag-threaded leak
-- (which steps CMP + back-edge) is state-independent — carrying RobustlyCTSafeJForProg. Loops now functionally
-- correct + robust over the literal emit.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoopFlag
-- Front while-loop bridge (item 4e residual): FrontWhileLsem ties RWhileNz (PUBLIC guard) to the loop lsem,
-- fuel = the public guard trajectory length (frontStep^[n], whileTrue/whileFalse). front_while_lsem_correct_and_robust.
-- A secret guard leaks the iteration count and is genuinely NOT CT — excluded (cmdCT_RWhileNz lt e = .Public).
import CatCrypt.Crypto.SecureCompilation.VIR.FrontWhileLsem
-- SIMD residual (vpackZMM): JasminLsemSimd — a .reg 512 = BitVec 512 lane value; lsemStepSimd applies zmmPackQ
-- (per-64-bit-lane bop over 8 lanes) as a pure data effect (no new state axis). straightOpsSimd_wire = real
-- "VPACK8u64:bop" emit; the lane op rides the typed .snd SimdDesc, never the wire. owned_lsem_correct_and_robust_simd
-- (ScalarSimdN superset ScalarLeafN); leak = operand structure only (lane op data-oblivious). Trocq relatedZmmPackQ (rfl).
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd
-- Multi-result call residual (callN): JasminLsemCallN — callN is structurally SINGLE-result inside Com/Expr
-- (callNRet = head slot; the k-tuple is consumed only by func.call, a different path than comToBody). So it is an
-- extCall-shaped head leaf: lsemStepCallN over the real "CALLN:name" wire (straightOpsCallN_wire = real emit),
-- carried LeafAgreesCN. owned_lsem_correct_and_robust_callN (ScalarCallN). ABI-only leak.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCallN
-- Internal call/return (Lcall/Lret): JasminLsemCall. LstateC = LstateP + a return-address
-- stack (the control-flow content of jasmin's RASP/encode_label, as (funname, resume-pc)
-- frames). Lcall pushes (lfn, lpc+1) and jumps via evalJump; Lret pops + resumes (none on
-- empty = jasmin type_error). Non-call arms delegate to evalInstrP. evalInstrC_Lcall/
-- Lret_cons/Lret_nil/delegate + call_ret_roundtrip (the stack discipline Lret restores).
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCall
-- Golden-path kernel export: comToLprog_faithful_straightline instantiated at fieldAddCom
-- (fieldAddCom's lsem-run emitted body decodes at the result register to fieldAddCom.denote).
import CatCrypt.Crypto.SecureCompilation.VIR.GoldenPathLsemFaithful
-- Toward general-Com faithfulness: the straight-line tower lifted into the labeled lsem.
-- straightOps_isStraightLine (emitted bodies are jump-free) + straightline_com_labeled_lsem
-- (a straight-line Com runs under the labeled program-indexed lsem to its decoded Com.denote,
-- via lsem_of_straightline) — the straight-line half, in the semantics the control-flow
-- increments live in.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful
-- The N-state program-indexed lsem (JasminLsemLabeledMC) + the mul/carry lift
-- (JasminLsemGeneralFaithfulMC): lsemFuelMC over LstateN with the straight-line bridge
-- lsemFuelMC_straightline, and comLsemExportFaithfulMC_of_mulcarry (ScalarMulCarryN — regArith/
-- select/shifts/mulhi/addCarry — runs under the program-indexed lsem to its decoded Com.denote).
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC
-- The leaf fragment in the program-indexed lsem (JasminLsemLabeledLeaf over typed LinstrRT +
-- a LeafEnvN leaf env: lsemFuelLeaf + bridge lsemFuelLeaf_straightline) + the lift
-- (JasminLsemGeneralFaithfulLeaf): comLsemExportFaithfulLeaf_of_leaf — the maximal straight-line
-- fragment ScalarLeafN (regArith/select/shifts/mulhi/addCarry/cast/regConst + the opaque extCall
-- leaf) runs under the program-indexed lsem to its decoded Com.denote.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulLeaf
-- Full-arith genuine export (Dialects.ArithFullExportFaithful): a general arith Com (all ops —
-- ALU/constant/mului_extended_hi/shifts) lowers to ScalarMulCarryN (with regConst), so
-- arith_full_export_faithful gives ComLsemExportFaithfulMC for the lowering. The scalar half is
-- Dialects.ArithExportFaithful.
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFullExportFaithful
-- callN and simd fragments in the program-indexed lsem (JasminLsemLabeled{CallN,Simd} bridges +
-- JasminLsemGeneralFaithful{CallN,Simd} lifts): comLsemExportFaithfulCallN_of_callN (multi-result
-- call leaf) and comLsemExportFaithfulSimd_of_simd (per-lane SIMD) run under the program-indexed
-- lsem to their decoded Com.denote — the last two parallel-to-leaf straight-line fragments.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulCallN
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulSimd
-- The unified general-Com headline (JasminLsemGeneralFaithfulAll): general_com_lsem_faithful —
-- any Com in the maximal fragment ScalarLeafN runs under the program-indexed lsem to its decoded
-- Com.denote, with sub-fragment corollaries (mul/carry, cast) via the subsumption tower.
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulAll

/-!
# `lsem` port — rot-guard aggregator

A dedicated import manifest for the faithful Lean port of jasmin's linear
semantics (`linear_sem.v`) and the unconditional functional ∧ robust
compiler-correctness it discharges (the `LprogExportFaithful` gate). Kept
separate from `SecureCompilationAll` so the `lsem`-port rot-guard is not subject
to concurrent edits of that shared manifest.

Build this to force-compile the whole `lsem` port:
`lake build CatCrypt.Crypto.SecureCompilation.VIR.LsemPortAll`.

Status: see the compiler roadmap.
-/
