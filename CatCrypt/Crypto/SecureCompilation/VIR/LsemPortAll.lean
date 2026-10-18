/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

-- Foundation: faithful straight-line linear semantics + the linearizer simulation.
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
-- Scalar op-set widening of the functional simulation (no carried edge):
-- regConst → non-uniform width + select → imm-shifts → mulhi/addCarry → castW → extCall leaf.
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
-- Stack-memory ops (stackLoad/stackStore) over a register-state + array carrier.
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
-- Control-flow foundation (labeled, program-indexed, fuel-bounded lsem — for loops/branches).
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
-- Single counted-loop simulation: the loop control-flow structure (back-edge Lcond, n-fold
-- iteration, halt-on-fallthrough) over loopLR = the real loopLcmd MINUS the explicit CMP
-- (loopLR_eq_loopLcmd_dropCmp).
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop
-- Front control-flow bridge: FrontControlLsem ties the LowCT front RFor/RIfNz RustExec denotations to
-- the REAL emitted loop (loopLcmd shape) / Lcond branch (labeled lsem). front_control_lsem_correct:
-- (loop) front n-fold = emitted loop lsem run; (branch) front two-branch = emitted Lcond decision. The
-- front↔emitted body tie is the named FrontLoopEncodes.comm edge (carried, like JasminLsemLoop's bodyStep).
public import CatCrypt.Crypto.SecureCompilation.VIR.FrontControlLsem
-- SIMD ops (vpackZMM): JasminLsemSimd — a .reg 512 = BitVec 512 lane value; lsemStepSimd applies zmmPackQ
-- (per-64-bit-lane bop over 8 lanes) as a pure data effect (no new state axis). straightOpsSimd_wire = real
-- "VPACK8u64:bop" emit; the lane op rides the typed .snd SimdDesc, never the wire. owned_lsem_correct_simd
-- (ScalarSimdN superset ScalarLeafN). Trocq relatedZmmPackQ (rfl).
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd
-- Multi-result call (callN): JasminLsemCallN — callN is structurally SINGLE-result inside Com/Expr
-- (callNRet = head slot; the k-tuple is consumed only by func.call, a different path than comToBody). So it is an
-- extCall-shaped head leaf: lsemStepCallN over the real "CALLN:name" wire (straightOpsCallN_wire = real emit),
-- carried LeafAgreesCN. owned_lsem_correct_callN (ScalarCallN).
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCallN
-- Internal call/return (Lcall/Lret): JasminLsemCall. LstateC = LstateP + a return-address
-- stack (the control-flow content of jasmin's RASP/encode_label, as (funname, resume-pc)
-- frames). Lcall pushes (lfn, lpc+1) and jumps via evalJump; Lret pops + resumes (none on
-- empty = jasmin type_error). Non-call arms delegate to evalInstrP. evalInstrC_Lcall/
-- Lret_cons/Lret_nil/delegate + call_ret_roundtrip (the stack discipline Lret restores).
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCall
-- Golden-path kernel export: comToLprog_faithful_straightline instantiated at fieldAddCom
-- (fieldAddCom's lsem-run emitted body decodes at the result register to fieldAddCom.denote).
public import CatCrypt.Crypto.SecureCompilation.VIR.GoldenPathLsemFaithful
-- General-Com faithfulness, straight-line part: the straight-line tower lifted into the labeled lsem.
-- straightOps_isStraightLine (emitted bodies are jump-free) + straightline_com_labeled_lsem
-- (a straight-line Com runs under the labeled program-indexed lsem to its decoded Com.denote,
-- via lsem_of_straightline) — the straight-line half, in the semantics the control-flow
-- increments live in.
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful
-- The N-state program-indexed lsem (JasminLsemLabeledMC) + the mul/carry lift
-- (JasminLsemGeneralFaithfulMC): lsemFuelMC over LstateN with the straight-line bridge
-- lsemFuelMC_straightline, and comLsemExportFaithfulMC_of_mulcarry (ScalarMulCarryN — regArith/
-- select/shifts/mulhi/addCarry — runs under the program-indexed lsem to its decoded Com.denote).
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC
-- The leaf fragment in the program-indexed lsem (JasminLsemLabeledLeaf over typed LinstrRT +
-- a LeafEnvN leaf env: lsemFuelLeaf + bridge lsemFuelLeaf_straightline) + the lift
-- (JasminLsemGeneralFaithfulLeaf): comLsemExportFaithfulLeaf_of_leaf — the maximal straight-line
-- fragment ScalarLeafN (regArith/select/shifts/mulhi/addCarry/cast/regConst + the opaque extCall
-- leaf) runs under the program-indexed lsem to its decoded Com.denote.
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulLeaf
-- Full-arith export (Dialects.ArithFullExportFaithful): a general arith Com (all ops —
-- ALU/constant/mului_extended_hi/shifts) lowers to ScalarMulCarryN (with regConst), so
-- arith_full_export_faithful gives ComLsemExportFaithfulMC for the lowering. The scalar half is
-- Dialects.ArithExportFaithful.
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFullExportFaithful
-- callN and simd fragments in the program-indexed lsem (JasminLsemLabeled{CallN,Simd} bridges +
-- JasminLsemGeneralFaithful{CallN,Simd} lifts): comLsemExportFaithfulCallN_of_callN (multi-result
-- call leaf) and comLsemExportFaithfulSimd_of_simd (per-lane SIMD) run under the program-indexed
-- lsem to their decoded Com.denote — the last two parallel-to-leaf straight-line fragments.
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulCallN
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulSimd

/-!
# `lsem` port — rot-guard aggregator

A dedicated import manifest for the faithful Lean port of jasmin's linear
semantics (`linear_sem.v`) and the functional compiler-correctness it
discharges (the `LprogExportFaithful` gate). Kept
separate from `SecureCompilationAll` so the `lsem`-port rot-guard is not subject
to concurrent edits of that shared manifest.

Build this to force-compile the whole `lsem` port:
`lake build CatCrypt.Crypto.SecureCompilation.VIR.LsemPortAll`.
-/

@[expose] public section
