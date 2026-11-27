/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesValue
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN

@[expose] public section

set_option autoImplicit false

/-!
# The decoded shipped `mpn_cmp_ct` against the canonicalised node

The compare kernel's limb body `MpnCmpFrontDenote.cmpUpdate` runs over the context
`[rp, idx, ap, bp, n]` (three invariants, the accumulator a one-word array) and stores once,
at chain slot `76`. `cmpTau` is its canonical renaming, `cmpCanonRen` the certificate.

## Main results

* `cmp_trip`: one trip of the decoded loop body simulates one limb step of the canonical node.
* `cmp_pre`, `cmp_post`: the decoded prologue and epilogue simulate those of the canonical node.
* `cmp_node_halts_fuel`: the decoded node halts within the fuel the canonical node needs.
* `cmp_decoded_val`: the decoded run leaves the comparison sign of the two bignum values in the
  result word.
* `mpn_cmp_ct_bytes_correct`: the function bytes of the shipped `mpn_cmp_ct` decode to the node
  layout, and the decoded run stores the comparison of the two inputs.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpBytesValue

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit (Gouter AR AO r64 NR NU)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote (cmpUpdate)

/-! ## 1. The renaming -/

open Classical in
/-- The renaming of the canonical compare node at depth `4` and output register `a4`: the
    accumulator argument and the store slot `76` to `a4`, the index argument to the loop
    index, every other chain register to its body temporary, every other name to itself. -/
noncomputable def cmpTau (r : String) : String :=
  if r = argName 4 then "a4"
  else if r = argName 3 then loopIdx 4
  else if r = regName 76 then "a4"
  else if h : ∃ k, r = regName k then loopReg 4 h.choose
  else r

theorem cmpTau_a4 : cmpTau (argName 4) = "a4" := by simp [cmpTau]

theorem cmpTau_a3 : cmpTau (argName 3) = loopIdx 4 := by
  simp [cmpTau, JasminLsemSimulation.argName_ne (show (3 : Nat) ≠ 4 by decide)]

theorem cmpTau_other {r : String} (h4 : r ≠ argName 4) (h3 : r ≠ argName 3)
    (hr : ∀ k, r ≠ regName k) : cmpTau r = r := by
  rw [cmpTau, ite_eq_right h4, ite_eq_right h3, ite_eq_right (hr 76), dite_eq_right]
  rintro ⟨k, rfl⟩
  exact hr k rfl

theorem cmpTau_arg {j : Nat} (hj : j < 3) : cmpTau (argName j) = argName j :=
  cmpTau_other (JasminLsemSimulation.argName_ne (by omega))
    (JasminLsemSimulation.argName_ne (by omega))
    (fun k h => JasminLsemSimulation.regName_ne_argName k j h.symm)

theorem cmpTau_r76 : cmpTau (regName 76) = "a4" := by
  simp [cmpTau, JasminLsemSimulation.regName_ne_argName]

theorem cmpTau_reg {k : Nat} (hk : k ≠ 76) : cmpTau (regName k) = loopReg 4 k := by
  have h7 : regName k ≠ regName 76 := fun h => hk (JasminLsemSimulation.regName_injective h)
  have hex : ∃ k', regName k = regName k' := ⟨k, rfl⟩
  rw [cmpTau, ite_eq_right (JasminLsemSimulation.regName_ne_argName k 4),
    ite_eq_right (JasminLsemSimulation.regName_ne_argName k 3), ite_eq_right h7,
    dite_eq_left hex, JasminLsemSimulation.regName_injective hex.choose_spec.symm]

theorem a4_ne_loopReg (k : Nat) : "a4" ≠ loopReg 4 k := argName_ne_loopReg 4 4 k

/-- The store-slot set of the compare chain. -/
def cmpS (k : Nat) : Prop := k = 76

/-- **The renaming certificate of the compare chain.** -/
theorem cmpCanonRen : CanonRen cmpTau 4 3 cmpS "a4" where
  fix := cmpTau_other (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 4)))
    (fun h => absurd h.symm (ne_empty_of_head? (head?_argName 3)))
    (fun k h => absurd h.symm (ne_empty_of_head? (head?_regName k)))
  tmp := by
    intro k _ hS
    exact cmpTau_reg hS
  thr := by
    intro k _ hS
    have hk : k = 76 := hS
    subst hk
    exact cmpTau_r76
  arg := by
    intro j k hj
    interval_cases j
    · rw [cmpTau_arg (by decide)]; exact argName_ne_loopReg 4 0 k
    · rw [cmpTau_arg (by decide)]; exact argName_ne_loopReg 4 1 k
    · rw [cmpTau_arg (by decide)]; exact argName_ne_loopReg 4 2 k
    · rw [cmpTau_a3]; exact loopIdx_ne_loopReg 4 4 k
    · rw [cmpTau_a4]; exact a4_ne_loopReg k
  outL := a4_ne_loopReg
  acc := cmpTau_a4
  idx := cmpTau_a3
  ctr := cmpTau_other (loopCtr_ne_argName 4 4) (loopCtr_ne_argName 4 3) (loopCtr_ne_regName 4)
  argOut := by
    intro j hj
    interval_cases j
    · rw [cmpTau_arg (by decide)]; decide
    · rw [cmpTau_arg (by decide)]; decide
    · rw [cmpTau_arg (by decide)]; decide
    · rw [cmpTau_a3]; decide
  invIdx := by
    intro j hj
    rw [cmpTau_arg hj]
    exact (loopIdx_ne_argName 4 j).symm
  invCtr := by
    intro j hj
    rw [cmpTau_arg hj]
    exact (loopCtr_ne_argName 4 j).symm
  outIdx := by decide
  outCtr := by decide
  idxCtr := loopIdx_ne_loopCtr 4
  ctrL := loopCtr_ne_loopReg 4 4


/-! ## 2. The thread certificate and the canonicalised node -/

theorem res_nil (cd : Nat) : ∀ n ∈ ([] : List String), Resolved 5 cd n := by simp

theorem res_one (x : String) (cd : Nat) (hx : Resolved 5 cd x) :
    ∀ n ∈ [x], Resolved 5 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  subst hn; exact hx

theorem res_two (x y : String) (cd : Nat) (hx : Resolved 5 cd x) (hy : Resolved 5 cd y) :
    ∀ n ∈ [x, y], Resolved 5 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact hx
  · exact hy

theorem res_three (x y z : String) (cd : Nat) (hx : Resolved 5 cd x) (hy : Resolved 5 cd y)
    (hz : Resolved 5 cd z) : ∀ n ∈ [x, y, z], Resolved 5 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact hz

theorem resA (j cd : Nat) (hj : j < 5) : Resolved 5 cd (argName j) := resolved_argName hj
theorem resR (k cd : Nat) (hk : 5 ≤ k) (hk' : k < cd) : Resolved 5 cd (regName k) :=
  resolved_regName hk hk'

theorem thrNone (τ : String → String) (out : String) :
    ∀ b, (none : Option String) = some b → τ b = out → b = argName 4 := by
  intro b hb
  cases hb

theorem thrAcc (out : String) (τ : String → String) :
    ∀ b, some (argName 4) = some b → τ b = out → b = argName 4 := by
  intro b hb _
  cases hb; rfl

theorem thrInv (out : String) (τ : String → String) (j : Nat) (hj : τ (argName j) ≠ out) :
    ∀ b, some (argName j) = some b → τ b = out → b = argName 4 := by
  intro b hb hbo
  cases hb
  exact absurd hbo hj

/-- The straight chain of the shipped compare body. -/
theorem cmpStraight_eq :
    straightOpsMem (([AO, AO, r64] : Ctxt jasminDialect).length + 2) cmpUpdate
        (([AO, AO, r64] : Ctxt jasminDialect).length + 2) =
    [ (.Lopn [.reg (regName 5)] "MOV:64" [.imm 1], .reg none)
    , (.Lopn [.reg (regName 6)] "SUB:64" [.reg (argName 0), .reg (regName 5)], .reg none)
    , (.Lopn [.reg (regName 7)] "SHL:64" [.reg (regName 6), .imm 0], .reg none)
    , (.Lopn [.reg (regName 8)] "SUB:64" [.reg (regName 7), .reg (argName 3)], .reg none)
    , (.Lopn [.reg (regName 9)] "SHL:64" [.reg (regName 8), .imm 0], .reg none)
    , (.Lopn [.reg (regName 10)] "MOV:64" [.imm 0], .reg none)
    , (.Lopn [.reg (regName 11)] "SHL:64" [.reg (regName 10), .imm 0], .reg none)
    , (.Lopn [.reg (regName 12)] "LOADIDX" [.arrIdx (argName 2) (regName 9) 8], .load 64 8)
    , (.Lopn [.reg (regName 13)] "LOADIDX" [.arrIdx (argName 1) (regName 9) 8], .load 64 8)
    , (.Lopn [.reg (regName 14)] "LOADIDX" [.arrIdx (argName 4) (regName 11) 8], .load 64 1)
    , (.Lopn [.reg (regName 15)] "MOV:64" [.imm 18446744073709551615], .reg none)
    , (.Lopn [.reg (regName 16)] "XOR:64" [.reg (regName 12), .reg (regName 15)], .reg none)
    , (.Lopn [.reg (regName 17)] "AND:64" [.reg (regName 16), .reg (regName 13)], .reg none)
    , (.Lopn [.reg (regName 18)] "SHL:64" [.reg (regName 17), .imm 0], .reg none)
    , (.Lopn [.reg (regName 19)] "XOR:64" [.reg (regName 12), .reg (regName 13)], .reg none)
    , (.Lopn [.reg (regName 20)] "MOV:64" [.imm 18446744073709551615], .reg none)
    , (.Lopn [.reg (regName 21)] "XOR:64" [.reg (regName 19), .reg (regName 20)], .reg none)
    , (.Lopn [.reg (regName 22)] "SUB:64" [.reg (regName 12), .reg (regName 13)], .reg none)
    , (.Lopn [.reg (regName 23)] "AND:64" [.reg (regName 21), .reg (regName 22)], .reg none)
    , (.Lopn [.reg (regName 24)] "SHL:64" [.reg (regName 23), .imm 0], .reg none)
    , (.Lopn [.reg (regName 25)] "XOR:64" [.reg (regName 18), .reg (regName 24)], .reg none)
    , (.Lopn [.reg (regName 26)] "AND:64" [.reg (regName 18), .reg (regName 24)], .reg none)
    , (.Lopn [.reg (regName 27)] "XOR:64" [.reg (regName 25), .reg (regName 26)], .reg none)
    , (.Lopn [.reg (regName 28)] "MOV:64" [.imm 63], .reg none)
    , (.Lopn [.reg (regName 29)] "SHR:64" [.reg (regName 27), .imm 63], .reg none)
    , (.Lopn [.reg (regName 30)] "SHL:64" [.reg (regName 29), .imm 0], .reg none)
    , (.Lopn [.reg (regName 31)] "MOV:64" [.imm 18446744073709551615], .reg none)
    , (.Lopn [.reg (regName 32)] "XOR:64" [.reg (regName 13), .reg (regName 31)], .reg none)
    , (.Lopn [.reg (regName 33)] "AND:64" [.reg (regName 32), .reg (regName 12)], .reg none)
    , (.Lopn [.reg (regName 34)] "SHL:64" [.reg (regName 33), .imm 0], .reg none)
    , (.Lopn [.reg (regName 35)] "XOR:64" [.reg (regName 13), .reg (regName 12)], .reg none)
    , (.Lopn [.reg (regName 36)] "MOV:64" [.imm 18446744073709551615], .reg none)
    , (.Lopn [.reg (regName 37)] "XOR:64" [.reg (regName 35), .reg (regName 36)], .reg none)
    , (.Lopn [.reg (regName 38)] "SUB:64" [.reg (regName 13), .reg (regName 12)], .reg none)
    , (.Lopn [.reg (regName 39)] "AND:64" [.reg (regName 37), .reg (regName 38)], .reg none)
    , (.Lopn [.reg (regName 40)] "SHL:64" [.reg (regName 39), .imm 0], .reg none)
    , (.Lopn [.reg (regName 41)] "XOR:64" [.reg (regName 34), .reg (regName 40)], .reg none)
    , (.Lopn [.reg (regName 42)] "AND:64" [.reg (regName 34), .reg (regName 40)], .reg none)
    , (.Lopn [.reg (regName 43)] "XOR:64" [.reg (regName 41), .reg (regName 42)], .reg none)
    , (.Lopn [.reg (regName 44)] "MOV:64" [.imm 63], .reg none)
    , (.Lopn [.reg (regName 45)] "SHR:64" [.reg (regName 43), .imm 63], .reg none)
    , (.Lopn [.reg (regName 46)] "SHL:64" [.reg (regName 45), .imm 0], .reg none)
    , (.Lopn [.reg (regName 47)] "SUB:64" [.reg (regName 46), .reg (regName 30)], .reg none)
    , (.Lopn [.reg (regName 48)] "SHL:64" [.reg (regName 47), .imm 0], .reg none)
    , (.Lopn [.reg (regName 49)] "MOV:64" [.imm 0], .reg none)
    , (.Lopn [.reg (regName 50)] "MOV:64" [.imm 18446744073709551615], .reg none)
    , (.Lopn [.reg (regName 51)] "XOR:64" [.reg (regName 49), .reg (regName 50)], .reg none)
    , (.Lopn [.reg (regName 52)] "AND:64" [.reg (regName 51), .reg (regName 14)], .reg none)
    , (.Lopn [.reg (regName 53)] "SHL:64" [.reg (regName 52), .imm 0], .reg none)
    , (.Lopn [.reg (regName 54)] "MOV:64" [.imm 0], .reg none)
    , (.Lopn [.reg (regName 55)] "XOR:64" [.reg (regName 54), .reg (regName 14)], .reg none)
    , (.Lopn [.reg (regName 56)] "MOV:64" [.imm 18446744073709551615], .reg none)
    , (.Lopn [.reg (regName 57)] "XOR:64" [.reg (regName 55), .reg (regName 56)], .reg none)
    , (.Lopn [.reg (regName 58)] "MOV:64" [.imm 0], .reg none)
    , (.Lopn [.reg (regName 59)] "SUB:64" [.reg (regName 58), .reg (regName 14)], .reg none)
    , (.Lopn [.reg (regName 60)] "AND:64" [.reg (regName 57), .reg (regName 59)], .reg none)
    , (.Lopn [.reg (regName 61)] "SHL:64" [.reg (regName 60), .imm 0], .reg none)
    , (.Lopn [.reg (regName 62)] "XOR:64" [.reg (regName 53), .reg (regName 61)], .reg none)
    , (.Lopn [.reg (regName 63)] "AND:64" [.reg (regName 53), .reg (regName 61)], .reg none)
    , (.Lopn [.reg (regName 64)] "XOR:64" [.reg (regName 62), .reg (regName 63)], .reg none)
    , (.Lopn [.reg (regName 65)] "MOV:64" [.imm 63], .reg none)
    , (.Lopn [.reg (regName 66)] "SHR:64" [.reg (regName 64), .imm 63], .reg none)
    , (.Lopn [.reg (regName 67)] "SHL:64" [.reg (regName 66), .imm 0], .reg none)
    , (.Lopn [.reg (regName 68)] "MOV:64" [.imm 1], .reg none)
    , (.Lopn [.reg (regName 69)] "SUB:64" [.reg (regName 67), .reg (regName 68)], .reg none)
    , (.Lopn [.reg (regName 70)] "SHL:64" [.reg (regName 69), .imm 0], .reg none)
    , (.Lopn [.reg (regName 71)] "XOR:64" [.reg (regName 48), .reg (regName 14)], .reg none)
    , (.Lopn [.reg (regName 72)] "SHL:64" [.reg (regName 71), .imm 0], .reg none)
    , (.Lopn [.reg (regName 73)] "AND:64" [.reg (regName 70), .reg (regName 72)], .reg none)
    , (.Lopn [.reg (regName 74)] "XOR:64" [.reg (regName 14), .reg (regName 73)], .reg none)
    , (.Lopn [.reg (regName 75)] "SHL:64" [.reg (regName 74), .imm 0], .reg none)
    , (.Lopn [.reg (regName 76)] "STOREIDX" [.arrIdx (argName 4) (regName 11) 8, .reg (regName 75)], .store 64 1) ] := by
  kernel_rfl

/-- **The thread certificate of the shipped compare chain.** -/
theorem cmpUpdate_threadCertT (τ : String → String) (out : String)
    (h1o : τ (argName 1) ≠ out) (h2o : τ (argName 2) ≠ out) :
    ThreadCert τ (([AO, AO, r64] : Ctxt jasminDialect).length + 2) cmpS out
      (straightOpsMem (([AO, AO, r64] : Ctxt jasminDialect).length + 2) cmpUpdate
        (([AO, AO, r64] : Ctxt jasminDialect).length + 2))
      (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (accRegMN [AO, AO, r64]) (loopBodyRetArrMN cmpUpdate) := by
  rw [cmpStraight_eq, show loopBodyRetArrMN cmpUpdate = regName 76 by kernel_rfl]
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 5
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 6 (resA 0 6 (by omega)) (resR 5 6 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 7 (resR 6 7 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 8 (resR 7 8 (by omega) (by omega)) (resA 3 8 (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 9 (resR 8 9 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 10
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 11 (resR 10 11 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 12 (resA 2 12 (by omega)) (resR 9 12 (by omega) (by omega))
  · exact thrInv out τ 2 (h2o)
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 13 (resA 1 13 (by omega)) (resR 9 13 (by omega) (by omega))
  · exact thrInv out τ 1 (h1o)
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 14 (resA 4 14 (by omega)) (resR 11 14 (by omega) (by omega))
  · exact thrAcc out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 15
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 16 (resR 12 16 (by omega) (by omega)) (resR 15 16 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 17 (resR 16 17 (by omega) (by omega)) (resR 13 17 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 18 (resR 17 18 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 19 (resR 12 19 (by omega) (by omega)) (resR 13 19 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 20
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 21 (resR 19 21 (by omega) (by omega)) (resR 20 21 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 22 (resR 12 22 (by omega) (by omega)) (resR 13 22 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 23 (resR 21 23 (by omega) (by omega)) (resR 22 23 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 24 (resR 23 24 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 25 (resR 18 25 (by omega) (by omega)) (resR 24 25 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 26 (resR 18 26 (by omega) (by omega)) (resR 24 26 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 27 (resR 25 27 (by omega) (by omega)) (resR 26 27 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 28
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 29 (resR 27 29 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 30 (resR 29 30 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 31
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 32 (resR 13 32 (by omega) (by omega)) (resR 31 32 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 33 (resR 32 33 (by omega) (by omega)) (resR 12 33 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 34 (resR 33 34 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 35 (resR 13 35 (by omega) (by omega)) (resR 12 35 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 36
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 37 (resR 35 37 (by omega) (by omega)) (resR 36 37 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 38 (resR 13 38 (by omega) (by omega)) (resR 12 38 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 39 (resR 37 39 (by omega) (by omega)) (resR 38 39 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 40 (resR 39 40 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 41 (resR 34 41 (by omega) (by omega)) (resR 40 41 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 42 (resR 34 42 (by omega) (by omega)) (resR 40 42 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 43 (resR 41 43 (by omega) (by omega)) (resR 42 43 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 44
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 45 (resR 43 45 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 46 (resR 45 46 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 47 (resR 46 47 (by omega) (by omega)) (resR 30 47 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 48 (resR 47 48 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 49
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 50
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 51 (resR 49 51 (by omega) (by omega)) (resR 50 51 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 52 (resR 51 52 (by omega) (by omega)) (resR 14 52 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 53 (resR 52 53 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 54
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 55 (resR 54 55 (by omega) (by omega)) (resR 14 55 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 56
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 57 (resR 55 57 (by omega) (by omega)) (resR 56 57 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 58
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 59 (resR 58 59 (by omega) (by omega)) (resR 14 59 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 60 (resR 57 60 (by omega) (by omega)) (resR 59 60 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 61 (resR 60 61 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 62 (resR 53 62 (by omega) (by omega)) (resR 61 62 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 63 (resR 53 63 (by omega) (by omega)) (resR 61 63 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 64 (resR 62 64 (by omega) (by omega)) (resR 63 64 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 65
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 66 (resR 64 66 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 67 (resR 66 67 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_nil 68
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 69 (resR 67 69 (by omega) (by omega)) (resR 68 69 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 70 (resR 69 70 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 71 (resR 48 71 (by omega) (by omega)) (resR 14 71 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 72 (resR 71 72 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 73 (resR 70 73 (by omega) (by omega)) (resR 72 73 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_two _ _ 74 (resR 14 74 (by omega) (by omega)) (resR 73 74 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [cmpS], ?_⟩⟩
  · exact res_one _ 75 (resR 74 75 (by omega) (by omega))
  · exact thrNone τ out
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact res_three _ _ _ 76 (resA 4 76 (by omega)) (resR 11 76 (by omega) (by omega)) (resR 75 76 (by omega) (by omega))
  · exact thrAcc out τ

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN (cmpUpdate_arrMemN)

attribute [local irreducible] cmpUpdate in
/-- **The canonicalised shipped compare node computes the model loop.** -/
theorem cmp_canon_machine_denote (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AO, AO, r64] : Ctxt jasminDialect).length ∧
      r = cmpTau (argName j))
    (invs : Ctxt.Valuation ([AO, AO, r64] : Ctxt jasminDialect))
    (fn c : String) (hc : c ≠ loopIdx 4)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin NR → BitVec 64)
    (hseed : StoreAgreesM (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (pullM cmpTau (b0.setReg (loopIdx 4) (0#64)))
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < ([AO, AO, r64] : Ctxt jasminDialect).length →
      (b0.reg.getW (cmpTau (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM cmpTau 4 "a4" c cmpUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base "a4" 64 NR
            = some (JLoopBodyN.denote ⟨m, cmpUpdate⟩ invs arr0) :=
  canonNodeRM_faithful cmpUpdate cmpUpdate_arrMemN cmpCanonRen
    (cmpUpdate_threadCertT cmpTau "a4" (by rw [cmpTau_arg (by decide)]; decide)
      (by rw [cmpTau_arg (by decide)]; decide)) absent regs hregs invs
    fn c hc b0 zf hpc arr0 hseed hinv m hm64 hcnt


/-! ## 3. The immediate right shift -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
  (shlImm0I andSeeds_isLopn loopCtr_four)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesValue (stripWidthTag_SHR64)

/-- The two-operand immediate right shift `SHR:64 d, a, #k` of the canonical chain. -/
def shrImmOpI (d a : String) (k : Nat) : LinstrRM :=
  (.Lopn [.reg d] "SHR:64" [.reg a, .imm k], .reg none)

theorem fstepF_shrImmOp (d a : String) (k : Nat) (hk : k < 64) (b : LstateM) (zf : Bool)
    (va : BitVec 64) (hva : b.reg.getW a 64 = some va) :
    fstepF (shrImmOpI d a k) b zf
      = some (withALUFlags (shrImmOpI d a k) b ((b.setReg d (va >>> k)).nextPc), zf) := by
  have hc : cmpArgs? (shrImmOpI d a k) = none := by
    simp only [cmpArgs?, shrImmOpI]
    rw [ite_eq_right (fun h => absurd h (by decide +kernel))]
  have hm : movRegArgs? (shrImmOpI d a k) = none := rfl
  have hkn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hs : lsemStepMem (shrImmOpI d a k) b = some ((b.setReg d (va >>> k)).nextPc) := by
    rw [shrImmOpI, lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ (by simp [mulhiStruct?]) rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (sarStruct?_of_ne (by rw [stripWidthTag_SHR64]; decide))]
    simp only [lsemStepN, readReg_of_getW hva, evalOperandN, stripWidthTag_SHR64, applyOpnN,
      Option.map_some, hkn, shiftMask_of_lt hk]
    rfl
  unfold fstepF stepMemF
  simp only [hc, hm, hs, Option.map_some]

variable {π : String → String} {L : String → Prop} {Lay : Layout}
  {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl : Prop}

/-- **`SHR:64 d, a, #k` against `mov %a, %d; shr $k, %d`**, `0 < k < 64`. -/
theorem decSim_shrImmOp_mov (d a D A : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64)
    (hD : π d = D) (hA : π a = A) (ha : L a) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [shrImmOpI d a k] [.mov D (.reg A), .shr D (.imm k)] := by
  subst hD hA
  intro sa b zf h
  have hst := fstepF_shrImmOp d a k hk b zf _ (h.regs a ha)
  refine ⟨_, zf, by rw [runStraightF_singleton]; exact hst, ?_⟩
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have esh : ∀ (s : AState) (X x : String) (n : Nat), (evalInstrA s (.shr X (.imm n))).regs x
      = if x = X then (x86_SHR (s.regs X) (BitVec.ofNat 64 n)).word else s.regs x :=
    fun _ _ _ _ => rfl
  refine (h.write (L' := liveAfter π L d (π d)) d (sa.regs (π a) >>> k)
    (aMachine.runBlock sa [.mov (π d) (.reg (π a)), .shr (π d) (.imm k)]) (fun r => ?_) rfl
    (fun r hr => ?_) (fun hz => False.elim hz)).withALUFlags _ b
  · simp only [Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec, esh, em,
      x86_SHR_word_imm _ k hk0 hk]
    split <;> rfl
  · rcases hr with rfl | ⟨h1, h2⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, h2⟩

macro_rules
  | `(tactic| decsim_step) =>
    `(tactic| focus first
      | (with_reducible apply decSim_shrImmOp_mov; decsim_close))

/-! ## 4. The canonicalised node as literals -/

/-- The looped segment of the canonicalised compare node with the single touch of `a0`. -/
def cmpLoopBodyLit : List LinstrRM :=
  [ movII "L4_r5" 1
  , binRegI "SUB:64" "L4_r6" "a0" "L4_r5"
  , shlImm0I "L4_r7" "L4_r6"
  , binRegI "SUB:64" "L4_r8" "L4_r7" "Lidx4"
  , shlImm0I "L4_r9" "L4_r8"
  , movII "L4_r10" 0
  , shlImm0I "L4_r11" "L4_r10"
  , (.Lopn [.reg "L4_r12"] "LOADIDX" [.arrIdx "a2" "L4_r9" 8], .load 64 8)
  , (.Lopn [.reg "L4_r13"] "LOADIDX" [.arrIdx "a1" "L4_r9" 8], .load 64 8)
  , (.Lopn [.reg "L4_r14"] "LOADIDX" [.arrIdx "a4" "L4_r11" 8], .load 64 1)
  , movII "L4_r15" 18446744073709551615
  , binRegI "XOR:64" "L4_r16" "L4_r12" "L4_r15"
  , binRegI "AND:64" "L4_r17" "L4_r16" "L4_r13"
  , shlImm0I "L4_r18" "L4_r17"
  , binRegI "XOR:64" "L4_r19" "L4_r12" "L4_r13"
  , movII "L4_r20" 18446744073709551615
  , binRegI "XOR:64" "L4_r21" "L4_r19" "L4_r20"
  , binRegI "SUB:64" "L4_r22" "L4_r12" "L4_r13"
  , binRegI "AND:64" "L4_r23" "L4_r21" "L4_r22"
  , shlImm0I "L4_r24" "L4_r23"
  , binRegI "XOR:64" "L4_r25" "L4_r18" "L4_r24"
  , binRegI "AND:64" "L4_r26" "L4_r18" "L4_r24"
  , binRegI "XOR:64" "L4_r27" "L4_r25" "L4_r26"
  , movII "L4_r28" 63
  , shrImmOpI "L4_r29" "L4_r27" 63
  , shlImm0I "L4_r30" "L4_r29"
  , movII "L4_r31" 18446744073709551615
  , binRegI "XOR:64" "L4_r32" "L4_r13" "L4_r31"
  , binRegI "AND:64" "L4_r33" "L4_r32" "L4_r12"
  , shlImm0I "L4_r34" "L4_r33"
  , binRegI "XOR:64" "L4_r35" "L4_r13" "L4_r12"
  , movII "L4_r36" 18446744073709551615
  , binRegI "XOR:64" "L4_r37" "L4_r35" "L4_r36"
  , binRegI "SUB:64" "L4_r38" "L4_r13" "L4_r12"
  , binRegI "AND:64" "L4_r39" "L4_r37" "L4_r38"
  , shlImm0I "L4_r40" "L4_r39"
  , binRegI "XOR:64" "L4_r41" "L4_r34" "L4_r40"
  , binRegI "AND:64" "L4_r42" "L4_r34" "L4_r40"
  , binRegI "XOR:64" "L4_r43" "L4_r41" "L4_r42"
  , movII "L4_r44" 63
  , shrImmOpI "L4_r45" "L4_r43" 63
  , shlImm0I "L4_r46" "L4_r45"
  , binRegI "SUB:64" "L4_r47" "L4_r46" "L4_r30"
  , shlImm0I "L4_r48" "L4_r47"
  , movII "L4_r49" 0
  , movII "L4_r50" 18446744073709551615
  , binRegI "XOR:64" "L4_r51" "L4_r49" "L4_r50"
  , binRegI "AND:64" "L4_r52" "L4_r51" "L4_r14"
  , shlImm0I "L4_r53" "L4_r52"
  , movII "L4_r54" 0
  , binRegI "XOR:64" "L4_r55" "L4_r54" "L4_r14"
  , movII "L4_r56" 18446744073709551615
  , binRegI "XOR:64" "L4_r57" "L4_r55" "L4_r56"
  , movII "L4_r58" 0
  , binRegI "SUB:64" "L4_r59" "L4_r58" "L4_r14"
  , binRegI "AND:64" "L4_r60" "L4_r57" "L4_r59"
  , shlImm0I "L4_r61" "L4_r60"
  , binRegI "XOR:64" "L4_r62" "L4_r53" "L4_r61"
  , binRegI "AND:64" "L4_r63" "L4_r53" "L4_r61"
  , binRegI "XOR:64" "L4_r64" "L4_r62" "L4_r63"
  , movII "L4_r65" 63
  , shrImmOpI "L4_r66" "L4_r64" 63
  , shlImm0I "L4_r67" "L4_r66"
  , movII "L4_r68" 1
  , binRegI "SUB:64" "L4_r69" "L4_r67" "L4_r68"
  , shlImm0I "L4_r70" "L4_r69"
  , binRegI "XOR:64" "L4_r71" "L4_r48" "L4_r14"
  , shlImm0I "L4_r72" "L4_r71"
  , binRegI "AND:64" "L4_r73" "L4_r70" "L4_r72"
  , binRegI "XOR:64" "L4_r74" "L4_r14" "L4_r73"
  , shlImm0I "L4_r75" "L4_r74"
  , (.Lopn [.reg "a4"] "STOREIDX" [.arrIdx "a4" "L4_r11" 8, .reg "L4_r75"], .store 64 1)
  , movRI "a4" "a4"
  , addImmI "Lidx4" "Lidx4" 1
  , subImmI "Lctr4" "Lctr4" 1
  , cmpRI "Lctr4" (.reg "a0") ]

theorem cmpStraightRen_eq :
    (straightOpsMem (([AO, AO, r64] : Ctxt jasminDialect).length + 2) cmpUpdate
        (([AO, AO, r64] : Ctxt jasminDialect).length + 2)).map (renRM cmpTau) =
      cmpLoopBodyLit.take 72 := by
  rw [cmpStraight_eq]
  simp only [renRM, renLinstrR, List.map, renOperand, cmpTau_a4, cmpTau_a3, cmpTau_r76,
    cmpTau_arg (j := 0) (by decide), cmpTau_arg (j := 1) (by decide),
    cmpTau_arg (j := 2) (by decide),
    cmpTau_reg (k := 5) (by decide), cmpTau_reg (k := 6) (by decide), cmpTau_reg (k := 7) (by decide), cmpTau_reg (k := 8) (by decide), cmpTau_reg (k := 9) (by decide), cmpTau_reg (k := 10) (by decide), cmpTau_reg (k := 11) (by decide), cmpTau_reg (k := 12) (by decide), cmpTau_reg (k := 13) (by decide), cmpTau_reg (k := 14) (by decide), cmpTau_reg (k := 15) (by decide), cmpTau_reg (k := 16) (by decide), cmpTau_reg (k := 17) (by decide), cmpTau_reg (k := 18) (by decide), cmpTau_reg (k := 19) (by decide), cmpTau_reg (k := 20) (by decide), cmpTau_reg (k := 21) (by decide), cmpTau_reg (k := 22) (by decide), cmpTau_reg (k := 23) (by decide), cmpTau_reg (k := 24) (by decide), cmpTau_reg (k := 25) (by decide), cmpTau_reg (k := 26) (by decide), cmpTau_reg (k := 27) (by decide), cmpTau_reg (k := 28) (by decide), cmpTau_reg (k := 29) (by decide), cmpTau_reg (k := 30) (by decide), cmpTau_reg (k := 31) (by decide), cmpTau_reg (k := 32) (by decide), cmpTau_reg (k := 33) (by decide), cmpTau_reg (k := 34) (by decide), cmpTau_reg (k := 35) (by decide), cmpTau_reg (k := 36) (by decide), cmpTau_reg (k := 37) (by decide), cmpTau_reg (k := 38) (by decide), cmpTau_reg (k := 39) (by decide), cmpTau_reg (k := 40) (by decide), cmpTau_reg (k := 41) (by decide), cmpTau_reg (k := 42) (by decide), cmpTau_reg (k := 43) (by decide), cmpTau_reg (k := 44) (by decide), cmpTau_reg (k := 45) (by decide), cmpTau_reg (k := 46) (by decide), cmpTau_reg (k := 47) (by decide), cmpTau_reg (k := 48) (by decide), cmpTau_reg (k := 49) (by decide), cmpTau_reg (k := 50) (by decide), cmpTau_reg (k := 51) (by decide), cmpTau_reg (k := 52) (by decide), cmpTau_reg (k := 53) (by decide), cmpTau_reg (k := 54) (by decide), cmpTau_reg (k := 55) (by decide), cmpTau_reg (k := 56) (by decide), cmpTau_reg (k := 57) (by decide), cmpTau_reg (k := 58) (by decide), cmpTau_reg (k := 59) (by decide), cmpTau_reg (k := 60) (by decide), cmpTau_reg (k := 61) (by decide), cmpTau_reg (k := 62) (by decide), cmpTau_reg (k := 63) (by decide), cmpTau_reg (k := 64) (by decide), cmpTau_reg (k := 65) (by decide), cmpTau_reg (k := 66) (by decide), cmpTau_reg (k := 67) (by decide), cmpTau_reg (k := 68) (by decide), cmpTau_reg (k := 69) (by decide), cmpTau_reg (k := 70) (by decide), cmpTau_reg (k := 71) (by decide), cmpTau_reg (k := 72) (by decide), cmpTau_reg (k := 73) (by decide), cmpTau_reg (k := 74) (by decide), cmpTau_reg (k := 75) (by decide)]
  kernel_rfl

theorem cmpCanonBody_eq :
    canonBodyRM cmpTau 4 "a4" cmpUpdate false ["a0"] = cmpLoopBodyLit := by
  show (straightOpsMem (([AO, AO, r64] : Ctxt jasminDialect).length + 2) cmpUpdate
        (([AO, AO, r64] : Ctxt jasminDialect).length + 2)).map (renRM cmpTau) ++ _ = _
  rw [cmpStraightRen_eq]
  kernel_rfl

theorem cmpSeeds_eq :
    canonSeedsRM 4 "a4" "a0" = [movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"] := by
  kernel_rfl

theorem cmpNode_eq :
    canonNodeRM cmpTau 4 "a4" "a0" cmpUpdate false ["a0"]
      = [movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" cmpLoopBodyLit := by
  unfold canonNodeRM
  rw [cmpSeeds_eq, cmpCanonBody_eq, loopCtr_four]

theorem cmpSeeds_isLopn :
    ∀ i ∈ [movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"], IsLopn i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩

theorem cmpLoopBody_isLopn : ∀ i ∈ cmpLoopBodyLit, IsLopn i := by
  intro i hi
  simp only [cmpLoopBodyLit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩

theorem cmpNode_top :
    findLabelMem 4 ([movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" cmpLoopBodyLit)
      = some (3 + 2) := by
  rw [MpnMul1DecodedNode.findLabelMem_append_of_isLopn _ _ _ cmpSeeds_isLopn,
    findLabelMem_guarded_top]
  simp

theorem cmpNode_end :
    findLabelMem (4 + 0x40000000) ([movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" cmpLoopBodyLit)
      = some (3 + cmpLoopBodyLit.length + 5) := by
  rw [MpnMul1DecodedNode.findLabelMem_append_of_isLopn _ _ _ cmpSeeds_isLopn,
    findLabelMem_guarded_endL _ _ _ _ cmpLoopBody_isLopn (by decide)]
  simp only [Option.map_some, Option.some.injEq, List.length_cons, List.length_nil]
  omega


/-! ## 5. The layout and the relation along the trip -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm
  (cmpDecPre cmpDecLoop cmpDecLoopBody cmpDecPost)

/-- The register assignment of the compare loop node, read off the exporter's allocation
    table: the output `a4` in `%rbx`, the count `a0` in `%rsi`, the index and counter, and the
    chain temporaries. The two source pointers `a2`, `a1` live in stack cells and are reached
    through their frame slots only. -/
def cmpPi (r : String) : String :=
  if r = "a4" then "%rbx"
  else if r = "a0" then "%rsi"
  else if r = "Lidx4" then "%rax"
  else if r = "Lctr4" then "%rdi"
  else if r = "L4_r5" then "%rbp"
  else if r = "L4_r6" then "%r8"
  else if r = "L4_r7" then "%rbp"
  else if r = "L4_r8" then "%r8"
  else if r = "L4_r9" then "%rbp"
  else if r = "L4_r10" then "%r8"
  else if r = "L4_r11" then "%r9"
  else if r = "L4_r12" then "%r8"
  else if r = "L4_r13" then "%r10"
  else if r = "L4_r14" then "%rbp"
  else if r = "L4_r15" then "%r11"
  else if r = "L4_r16" then "%r12"
  else if r = "L4_r17" then "%r11"
  else if r = "L4_r18" then "%r12"
  else if r = "L4_r19" then "%r11"
  else if r = "L4_r20" then "%r13"
  else if r = "L4_r21" then "%rdx"
  else if r = "L4_r22" then "%r11"
  else if r = "L4_r23" then "%r13"
  else if r = "L4_r24" then "%rdx"
  else if r = "L4_r25" then "%r11"
  else if r = "L4_r26" then "%r13"
  else if r = "L4_r27" then "%rdx"
  else if r = "L4_r28" then "%r11"
  else if r = "L4_r29" then "%r11"
  else if r = "L4_r30" then "%rdx"
  else if r = "L4_r31" then "%r11"
  else if r = "L4_r32" then "%r12"
  else if r = "L4_r33" then "%r11"
  else if r = "L4_r34" then "%r12"
  else if r = "L4_r35" then "%r11"
  else if r = "L4_r36" then "%r13"
  else if r = "L4_r37" then "%rcx"
  else if r = "L4_r38" then "%r11"
  else if r = "L4_r39" then "%r8"
  else if r = "L4_r40" then "%rcx"
  else if r = "L4_r41" then "%r8"
  else if r = "L4_r42" then "%r10"
  else if r = "L4_r43" then "%rcx"
  else if r = "L4_r44" then "%r8"
  else if r = "L4_r45" then "%r8"
  else if r = "L4_r46" then "%rcx"
  else if r = "L4_r47" then "%r8"
  else if r = "L4_r48" then "%rcx"
  else if r = "L4_r49" then "%rdx"
  else if r = "L4_r50" then "%r8"
  else if r = "L4_r51" then "%r10"
  else if r = "L4_r52" then "%rdx"
  else if r = "L4_r53" then "%r8"
  else if r = "L4_r54" then "%rdx"
  else if r = "L4_r55" then "%r10"
  else if r = "L4_r56" then "%rdx"
  else if r = "L4_r57" then "%r11"
  else if r = "L4_r58" then "%rdx"
  else if r = "L4_r59" then "%r10"
  else if r = "L4_r60" then "%rdx"
  else if r = "L4_r61" then "%r10"
  else if r = "L4_r62" then "%rdx"
  else if r = "L4_r63" then "%r11"
  else if r = "L4_r64" then "%r8"
  else if r = "L4_r65" then "%rdx"
  else if r = "L4_r66" then "%rdx"
  else if r = "L4_r67" then "%r8"
  else if r = "L4_r68" then "%rdx"
  else if r = "L4_r69" then "%r10"
  else if r = "L4_r70" then "%rdx"
  else if r = "L4_r71" then "%r8"
  else if r = "L4_r72" then "%rcx"
  else if r = "L4_r73" then "%r8"
  else if r = "L4_r74" then "%rcx"
  else if r = "L4_r75" then "%rdx"
  else r

/-- The array layout: the one-word output `a4` at `rp` (slot `s0`), the sources `a2` at `ap`
    (slot `s1`) and `a1` at `bp` (slot `s2`), eight words each. -/
def cmpLay (rp ap bp : BitVec 64) : Layout where
  base A := if A = "a2" then ap else if A = "a1" then bp else rp
  len A := if A = "a2" ∨ A = "a1" then 8 else 1
  slot A := if A = "a4" then some "s0" else if A = "a2" then some "s1"
    else if A = "a1" then some "s2" else none

/-- The frame: `s0` at `72(%rsp)`, `s1` at `64(%rsp)`, `s2` at `-8(%rsp)`. -/
def cmpFrame (rsp : BitVec 64) (q : String) : Option (BitVec 64) :=
  if q = "s0" then some (rsp + BitVec.ofInt 64 72)
  else if q = "s1" then some (rsp + BitVec.ofInt 64 64)
  else if q = "s2" then some (rsp + BitVec.ofInt 64 (-8)) else none

def cmpK (A : String) (j : Nat) : Prop :=
  (A = "a4" ∧ j < 1) ∨ (A = "a2" ∧ j < 8) ∨ (A = "a1" ∧ j < 8)

abbrev cmLive (r : String) : Prop := r ∈ ["a4", "a0", "Lidx4", "Lctr4"]
abbrev cmLiveA (r : String) : Prop := r ∈ ["L4_r9", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]
abbrev cmLiveB (r : String) : Prop :=
  r ∈ ["L4_r12", "L4_r9", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]
abbrev cmLiveC (r : String) : Prop :=
  r ∈ ["L4_r13", "L4_r12", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]
abbrev cmLiveD (r : String) : Prop :=
  r ∈ ["L4_r14", "L4_r13", "L4_r12", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]
abbrev cmLiveE (r : String) : Prop := r ∈ ["L4_r75", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]

/-- The machine registers the trip tracks: the stack pointer, the index, the counter and
    the count `n` in `%rsi`. -/
def cmpP (rsp : BitVec 64) (n x y : Nat) (sa : AState) : Prop :=
  sa.regs "%rsp" = rsp ∧ sa.regs "%rax" = BitVec.ofNat 64 x ∧ sa.regs "%rdi" = BitVec.ofNat 64 y
    ∧ sa.regs "%rsi" = BitVec.ofNat 64 n

theorem cmpP_runBlock (rsp : BitVec 64) (n x y : Nat) (js : List (JInstr 64))
    (h : ∀ j ∈ js, ∀ R ∈ ["%rsp", "%rax", "%rdi", "%rsi"], R ∉ dsts j) (sa : AState)
    (hp : cmpP rsp n x y sa) : cmpP rsp n x y (aMachine.runBlock sa js) := by
  have e := runBlock_regs_of_not_mem _ js sa h
  exact ⟨by rw [e _ (by simp)]; exact hp.1, by rw [e _ (by simp)]; exact hp.2.1,
    by rw [e _ (by simp)]; exact hp.2.2.1, by rw [e _ (by simp)]; exact hp.2.2.2⟩

/-- The trip predicate with the descending limb index in `%rbp` and the result index `0` in
    `%r9`. -/
def cmpPI (rsp : BitVec 64) (n x y : Nat) (sa : AState) : Prop :=
  cmpP rsp n x y sa ∧ sa.regs "%rbp" = BitVec.ofNat 64 (n - 1 - x) ∧ sa.regs "%r9" = 0#64

def cmpQ (rsp : BitVec 64) (n m t : Nat) (sa : AState) : Prop :=
  cmpP rsp n (t + 1) (m - (t + 1)) sa
    ∧ sa.flags.zf.getD false = (BitVec.ofNat 64 (m - (t + 1)) == 0#64)

section Trip

variable (rp ap bp rsp : BitVec 64)

abbrev cmpRel (L : String → Prop) (K : String → Nat → Prop) (zl : Prop) (P : AState → Prop) :
    AState → LstateM → Bool → Prop :=
  fun sa b zf => DecLsemCorr cmpPi L (cmpLay rp ap bp) (cmpFrame rsp) K zl sa b zf ∧ P sa

theorem ofNat_sub_sub (n t : Nat) (ht : t < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 - BitVec.ofNat 64 t = BitVec.ofNat 64 (n - 1 - t) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega)]
  omega

/-- The descending limb index `n - 1 - Lidx4` in `%rbp` and the result index `0` in `%r9`. -/
theorem cmp_seg_idx (n t y : Nat) (ht : t < n) (hn : n ≤ 8) (zl : Prop) :
    DecSim (cmpRel rp ap bp rsp cmLive cmpK zl (cmpP rsp n t y))
      (cmpRel rp ap bp rsp cmLiveA cmpK False (cmpPI rsp n t y))
      (cmpLoopBodyLit.take 7)
      [ .mov "%rbp" (.imm 1), .mov "%r8" (.reg "%rsi"), .sub "%r8" (.reg "%rbp")
      , .mov "%rbp" (.reg "%r8"), .mov "%r8" (.reg "%rbp"), .sub "%r8" (.reg "%rax")
      , .mov "%rbp" (.reg "%r8"), .mov "%r8" (.imm 0), .mov "%r9" (.reg "%r8") ] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ⟨cmpP_runBlock rsp n t y _ (by decide +kernel) sa hp,
    ?_⟩)
  · simp only [cmpLoopBodyLit, List.take_succ_cons, List.take_zero]
    decsim_chain
    exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)
  · have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
        = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
    have ei : ∀ (s : AState) (X x : String) (k : Nat), (evalInstrA s (.mov X (.imm k))).regs x
        = if x = X then BitVec.ofNat 64 k else s.regs x := fun _ _ _ _ => rfl
    have es : ∀ (s : AState) (X Y x : String), (evalInstrA s (.sub X (.reg Y))).regs x
        = if x = X then s.regs X - s.regs Y else s.regs x := fun _ _ _ _ => rfl
    simp only [Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    refine ⟨?_, ?_⟩
    · simp (config := { decide := true }) only [em, ei, es, ite_true, ite_false]
      rw [hp.2.2.2, hp.2.1, ofNat_sub_sub n t ht (by omega)]
    · simp (config := { decide := true }) only [em, ei, es, ite_true, ite_false]

theorem cmpPI_runBlock (rsp : BitVec 64) (n x y : Nat) (js : List (JInstr 64))
    (h : ∀ j ∈ js, ∀ R ∈ ["%rsp", "%rax", "%rdi", "%rsi", "%rbp", "%r9"], R ∉ dsts j) (sa : AState)
    (hp : cmpPI rsp n x y sa) : cmpPI rsp n x y (aMachine.runBlock sa js) := by
  have e := runBlock_regs_of_not_mem _ js sa h
  exact ⟨⟨by rw [e _ (by simp)]; exact hp.1.1, by rw [e _ (by simp)]; exact hp.1.2.1,
    by rw [e _ (by simp)]; exact hp.1.2.2.1, by rw [e _ (by simp)]; exact hp.1.2.2.2⟩,
    by rw [e _ (by simp)]; exact hp.2.1, by rw [e _ (by simp)]; exact hp.2.2⟩

/-- The load of `a2[L4_r9]` (the limb of `ap`) through the pointer reloaded from `64(%rsp)`. -/
theorem cmp_seg_load2 (n t y : Nat) (ht : t < n) (hn : n ≤ 8) :
    DecSim (cmpRel rp ap bp rsp cmLiveA cmpK False (cmpPI rsp n t y))
      (cmpRel rp ap bp rsp cmLiveB cmpK False (cmpPI rsp n t y))
      [(.Lopn [.reg "L4_r12"] "LOADIDX" [.arrIdx "a2" "L4_r9" 8], .load 64 8)]
      [.loadMem "%r14" "%rsp" 64, .loadMemIdx "%r8" "%r14" "%rbp" 8] :=
  DecSim.frameWith _ _ _
    (decSim_loadR (Lay := cmpLay rp ap bp) (frame := cmpFrame rsp) (K := cmpK) (zl := False)
      (π := cmpPi) (L := cmLiveA) (L' := cmLiveB)
      "L4_r12" "a2" "L4_r9" "%r14" "%rsp" "s1" 64 rfl (by decide +kernel) (by decide +kernel)
      (by unfold Survives; decide +kernel))
    (fun sa hp => ⟨by rw [hp.1.1]; rfl, Or.inr (Or.inl ⟨rfl, by
      show (sa.regs "%rbp").toNat < 8
      rw [hp.2.1, ofNat_toNat_lt _ (by omega)]; omega⟩)⟩)
    (cmpPI_runBlock rsp n t y _ (by decide +kernel))

/-- The load of `a1[L4_r9]` (the limb of `bp`) through the pointer reloaded from `-8(%rsp)`. -/
theorem cmp_seg_load1 (n t y : Nat) (ht : t < n) (hn : n ≤ 8) :
    DecSim (cmpRel rp ap bp rsp cmLiveB cmpK False (cmpPI rsp n t y))
      (cmpRel rp ap bp rsp cmLiveC cmpK False (cmpPI rsp n t y))
      [(.Lopn [.reg "L4_r13"] "LOADIDX" [.arrIdx "a1" "L4_r9" 8], .load 64 8)]
      [.loadMem "%r14" "%rsp" (-8), .loadMemIdx "%r10" "%r14" "%rbp" 8] :=
  DecSim.frameWith _ _ _
    (decSim_loadR (Lay := cmpLay rp ap bp) (frame := cmpFrame rsp) (K := cmpK) (zl := False)
      (π := cmpPi) (L := cmLiveB) (L' := cmLiveC)
      "L4_r13" "a1" "L4_r9" "%r14" "%rsp" "s2" (-8) rfl (by decide +kernel) (by decide +kernel)
      (by unfold Survives; decide +kernel))
    (fun sa hp => ⟨by rw [hp.1.1]; rfl, Or.inr (Or.inr ⟨rfl, by
      show (sa.regs "%rbp").toNat < 8
      rw [hp.2.1, ofNat_toNat_lt _ (by omega)]; omega⟩)⟩)
    (cmpPI_runBlock rsp n t y _ (by decide +kernel))

/-- The trip predicate with the result index `0` in `%r9`. -/
def cmpPR (rsp : BitVec 64) (n x y : Nat) (sa : AState) : Prop :=
  cmpP rsp n x y sa ∧ sa.regs "%r9" = 0#64

theorem cmpPR_runBlock (rsp : BitVec 64) (n x y : Nat) (js : List (JInstr 64))
    (h : ∀ j ∈ js, ∀ R ∈ ["%rsp", "%rax", "%rdi", "%rsi", "%r9"], R ∉ dsts j) (sa : AState)
    (hp : cmpPR rsp n x y sa) : cmpPR rsp n x y (aMachine.runBlock sa js) := by
  have e := runBlock_regs_of_not_mem _ js sa h
  exact ⟨⟨by rw [e _ (by simp)]; exact hp.1.1, by rw [e _ (by simp)]; exact hp.1.2.1,
    by rw [e _ (by simp)]; exact hp.1.2.2.1, by rw [e _ (by simp)]; exact hp.1.2.2.2⟩,
    by rw [e _ (by simp)]; exact hp.2⟩

/-- The load of the result word `a4[L4_r11]`, index `0`, through `72(%rsp)`. -/
theorem cmp_seg_load4 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp cmLiveC cmpK False (cmpPI rsp n t y))
      (cmpRel rp ap bp rsp cmLiveD cmpK False (cmpPR rsp n t y))
      [(.Lopn [.reg "L4_r14"] "LOADIDX" [.arrIdx "a4" "L4_r11" 8], .load 64 1)]
      [.loadMem "%r14" "%rsp" 72, .loadMemIdx "%rbp" "%r14" "%r9" 8] :=
  DecSim.frameWith _ _ (cmpPR rsp n t y)
    (decSim_loadR (Lay := cmpLay rp ap bp) (frame := cmpFrame rsp) (K := cmpK) (zl := False)
      (π := cmpPi) (L := cmLiveC) (L' := cmLiveD)
      "L4_r14" "a4" "L4_r11" "%r14" "%rsp" "s0" 72 rfl (by decide +kernel) (by decide +kernel)
      (by unfold Survives; decide +kernel))
    (fun sa hp => ⟨by rw [hp.1.1]; rfl, Or.inl ⟨rfl, by
      show (sa.regs "%r9").toNat < 1
      rw [hp.2.2]; decide⟩⟩)
    (fun sa hp => cmpPR_runBlock rsp n t y _ (by decide +kernel) sa ⟨hp.1, hp.2.2⟩)

theorem cmp_chain0 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp cmLiveD cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp (· ∈ ["L4_r22", "L4_r21", "L4_r20", "L4_r18", "L4_r14", "L4_r13", "L4_r12", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      [ movII "L4_r15" 18446744073709551615
      , binRegI "XOR:64" "L4_r16" "L4_r12" "L4_r15"
      , binRegI "AND:64" "L4_r17" "L4_r16" "L4_r13"
      , shlImm0I "L4_r18" "L4_r17"
      , binRegI "XOR:64" "L4_r19" "L4_r12" "L4_r13"
      , movII "L4_r20" 18446744073709551615
      , binRegI "XOR:64" "L4_r21" "L4_r19" "L4_r20"
      , binRegI "SUB:64" "L4_r22" "L4_r12" "L4_r13" ]
      [ .mov "%r11" (.imm 18446744073709551615)
      , .mov "%r12" (.reg "%r8")
      , .xor_ "%r12" (.reg "%r11")
      , .mov "%r11" (.reg "%r12")
      , .and_ "%r11" (.reg "%r10")
      , .mov "%r12" (.reg "%r11")
      , .mov "%r11" (.reg "%r8")
      , .xor_ "%r11" (.reg "%r10")
      , .mov "%r13" (.imm 18446744073709551615)
      , .mov "%rdx" (.reg "%r11")
      , .xor_ "%rdx" (.reg "%r13")
      , .mov "%r11" (.reg "%r8")
      , .sub "%r11" (.reg "%r10") ] := by
  refine DecSim.frame _ _ ?_ (cmpPR_runBlock rsp n t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

theorem cmp_chain1 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp (· ∈ ["L4_r22", "L4_r21", "L4_r20", "L4_r18", "L4_r14", "L4_r13", "L4_r12", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp (· ∈ ["L4_r30", "L4_r29", "L4_r26", "L4_r18", "L4_r14", "L4_r13", "L4_r12", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      [ binRegI "AND:64" "L4_r23" "L4_r21" "L4_r22"
      , shlImm0I "L4_r24" "L4_r23"
      , binRegI "XOR:64" "L4_r25" "L4_r18" "L4_r24"
      , binRegI "AND:64" "L4_r26" "L4_r18" "L4_r24"
      , binRegI "XOR:64" "L4_r27" "L4_r25" "L4_r26"
      , movII "L4_r28" 63
      , shrImmOpI "L4_r29" "L4_r27" 63
      , shlImm0I "L4_r30" "L4_r29" ]
      [ .mov "%r13" (.reg "%rdx")
      , .and_ "%r13" (.reg "%r11")
      , .mov "%rdx" (.reg "%r13")
      , .mov "%r11" (.reg "%r12")
      , .xor_ "%r11" (.reg "%rdx")
      , .mov "%r13" (.reg "%r12")
      , .and_ "%r13" (.reg "%rdx")
      , .mov "%rdx" (.reg "%r11")
      , .xor_ "%rdx" (.reg "%r13")
      , .mov "%r11" (.imm 63)
      , .mov "%r11" (.reg "%rdx")
      , .shr "%r11" (.imm 63)
      , .mov "%rdx" (.reg "%r11") ] := by
  refine DecSim.frame _ _ ?_ (cmpPR_runBlock rsp n t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

theorem cmp_chain2 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp (· ∈ ["L4_r30", "L4_r29", "L4_r26", "L4_r18", "L4_r14", "L4_r13", "L4_r12", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp (· ∈ ["L4_r38", "L4_r37", "L4_r36", "L4_r34", "L4_r30", "L4_r14", "L4_r13", "L4_r12", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      [ movII "L4_r31" 18446744073709551615
      , binRegI "XOR:64" "L4_r32" "L4_r13" "L4_r31"
      , binRegI "AND:64" "L4_r33" "L4_r32" "L4_r12"
      , shlImm0I "L4_r34" "L4_r33"
      , binRegI "XOR:64" "L4_r35" "L4_r13" "L4_r12"
      , movII "L4_r36" 18446744073709551615
      , binRegI "XOR:64" "L4_r37" "L4_r35" "L4_r36"
      , binRegI "SUB:64" "L4_r38" "L4_r13" "L4_r12" ]
      [ .mov "%r11" (.imm 18446744073709551615)
      , .mov "%r12" (.reg "%r10")
      , .xor_ "%r12" (.reg "%r11")
      , .mov "%r11" (.reg "%r12")
      , .and_ "%r11" (.reg "%r8")
      , .mov "%r12" (.reg "%r11")
      , .mov "%r11" (.reg "%r10")
      , .xor_ "%r11" (.reg "%r8")
      , .mov "%r13" (.imm 18446744073709551615)
      , .mov "%rcx" (.reg "%r11")
      , .xor_ "%rcx" (.reg "%r13")
      , .mov "%r11" (.reg "%r10")
      , .sub "%r11" (.reg "%r8") ] := by
  refine DecSim.frame _ _ ?_ (cmpPR_runBlock rsp n t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

theorem cmp_chain3 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp (· ∈ ["L4_r38", "L4_r37", "L4_r36", "L4_r34", "L4_r30", "L4_r14", "L4_r13", "L4_r12", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp (· ∈ ["L4_r46", "L4_r45", "L4_r42", "L4_r38", "L4_r36", "L4_r34", "L4_r30", "L4_r14", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      [ binRegI "AND:64" "L4_r39" "L4_r37" "L4_r38"
      , shlImm0I "L4_r40" "L4_r39"
      , binRegI "XOR:64" "L4_r41" "L4_r34" "L4_r40"
      , binRegI "AND:64" "L4_r42" "L4_r34" "L4_r40"
      , binRegI "XOR:64" "L4_r43" "L4_r41" "L4_r42"
      , movII "L4_r44" 63
      , shrImmOpI "L4_r45" "L4_r43" 63
      , shlImm0I "L4_r46" "L4_r45" ]
      [ .mov "%r8" (.reg "%rcx")
      , .and_ "%r8" (.reg "%r11")
      , .mov "%rcx" (.reg "%r8")
      , .mov "%r8" (.reg "%r12")
      , .xor_ "%r8" (.reg "%rcx")
      , .mov "%r10" (.reg "%r12")
      , .and_ "%r10" (.reg "%rcx")
      , .mov "%rcx" (.reg "%r8")
      , .xor_ "%rcx" (.reg "%r10")
      , .mov "%r8" (.imm 63)
      , .mov "%r8" (.reg "%rcx")
      , .shr "%r8" (.imm 63)
      , .mov "%rcx" (.reg "%r8") ] := by
  refine DecSim.frame _ _ ?_ (cmpPR_runBlock rsp n t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

theorem cmp_chain4 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp (· ∈ ["L4_r46", "L4_r45", "L4_r42", "L4_r38", "L4_r36", "L4_r34", "L4_r30", "L4_r14", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp (· ∈ ["L4_r54", "L4_r53", "L4_r51", "L4_r48", "L4_r38", "L4_r36", "L4_r34", "L4_r14", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      [ binRegI "SUB:64" "L4_r47" "L4_r46" "L4_r30"
      , shlImm0I "L4_r48" "L4_r47"
      , movII "L4_r49" 0
      , movII "L4_r50" 18446744073709551615
      , binRegI "XOR:64" "L4_r51" "L4_r49" "L4_r50"
      , binRegI "AND:64" "L4_r52" "L4_r51" "L4_r14"
      , shlImm0I "L4_r53" "L4_r52"
      , movII "L4_r54" 0 ]
      [ .mov "%r8" (.reg "%rcx")
      , .sub "%r8" (.reg "%rdx")
      , .mov "%rcx" (.reg "%r8")
      , .mov "%rdx" (.imm 0)
      , .mov "%r8" (.imm 18446744073709551615)
      , .mov "%r10" (.reg "%rdx")
      , .xor_ "%r10" (.reg "%r8")
      , .mov "%rdx" (.reg "%r10")
      , .and_ "%rdx" (.reg "%rbp")
      , .mov "%r8" (.reg "%rdx")
      , .mov "%rdx" (.imm 0) ] := by
  refine DecSim.frame _ _ ?_ (cmpPR_runBlock rsp n t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

theorem cmp_chain5 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp (· ∈ ["L4_r54", "L4_r53", "L4_r51", "L4_r48", "L4_r38", "L4_r36", "L4_r34", "L4_r14", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp (· ∈ ["L4_r62", "L4_r61", "L4_r57", "L4_r53", "L4_r48", "L4_r36", "L4_r34", "L4_r14", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      [ binRegI "XOR:64" "L4_r55" "L4_r54" "L4_r14"
      , movII "L4_r56" 18446744073709551615
      , binRegI "XOR:64" "L4_r57" "L4_r55" "L4_r56"
      , movII "L4_r58" 0
      , binRegI "SUB:64" "L4_r59" "L4_r58" "L4_r14"
      , binRegI "AND:64" "L4_r60" "L4_r57" "L4_r59"
      , shlImm0I "L4_r61" "L4_r60"
      , binRegI "XOR:64" "L4_r62" "L4_r53" "L4_r61" ]
      [ .mov "%r10" (.reg "%rdx")
      , .xor_ "%r10" (.reg "%rbp")
      , .mov "%rdx" (.imm 18446744073709551615)
      , .mov "%r11" (.reg "%r10")
      , .xor_ "%r11" (.reg "%rdx")
      , .mov "%rdx" (.imm 0)
      , .mov "%r10" (.reg "%rdx")
      , .sub "%r10" (.reg "%rbp")
      , .mov "%rdx" (.reg "%r11")
      , .and_ "%rdx" (.reg "%r10")
      , .mov "%r10" (.reg "%rdx")
      , .mov "%rdx" (.reg "%r8")
      , .xor_ "%rdx" (.reg "%r10") ] := by
  refine DecSim.frame _ _ ?_ (cmpPR_runBlock rsp n t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

theorem cmp_chain6 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp (· ∈ ["L4_r62", "L4_r61", "L4_r57", "L4_r53", "L4_r48", "L4_r36", "L4_r34", "L4_r14", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp (· ∈ ["L4_r70", "L4_r69", "L4_r67", "L4_r63", "L4_r48", "L4_r36", "L4_r34", "L4_r14", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      [ binRegI "AND:64" "L4_r63" "L4_r53" "L4_r61"
      , binRegI "XOR:64" "L4_r64" "L4_r62" "L4_r63"
      , movII "L4_r65" 63
      , shrImmOpI "L4_r66" "L4_r64" 63
      , shlImm0I "L4_r67" "L4_r66"
      , movII "L4_r68" 1
      , binRegI "SUB:64" "L4_r69" "L4_r67" "L4_r68"
      , shlImm0I "L4_r70" "L4_r69" ]
      [ .mov "%r11" (.reg "%r8")
      , .and_ "%r11" (.reg "%r10")
      , .mov "%r8" (.reg "%rdx")
      , .xor_ "%r8" (.reg "%r11")
      , .mov "%rdx" (.imm 63)
      , .mov "%rdx" (.reg "%r8")
      , .shr "%rdx" (.imm 63)
      , .mov "%r8" (.reg "%rdx")
      , .mov "%rdx" (.imm 1)
      , .mov "%r10" (.reg "%r8")
      , .sub "%r10" (.reg "%rdx")
      , .mov "%rdx" (.reg "%r10") ] := by
  refine DecSim.frame _ _ ?_ (cmpPR_runBlock rsp n t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

theorem cmp_chain7 (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp (· ∈ ["L4_r70", "L4_r69", "L4_r67", "L4_r63", "L4_r48", "L4_r36", "L4_r34", "L4_r14", "L4_r11", "a4", "a0", "Lidx4", "Lctr4"]) cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp cmLiveE cmpK False (cmpPR rsp n t y))
      [ binRegI "XOR:64" "L4_r71" "L4_r48" "L4_r14"
      , shlImm0I "L4_r72" "L4_r71"
      , binRegI "AND:64" "L4_r73" "L4_r70" "L4_r72"
      , binRegI "XOR:64" "L4_r74" "L4_r14" "L4_r73"
      , shlImm0I "L4_r75" "L4_r74" ]
      [ .mov "%r8" (.reg "%rcx")
      , .xor_ "%r8" (.reg "%rbp")
      , .mov "%rcx" (.reg "%r8")
      , .mov "%r8" (.reg "%rdx")
      , .and_ "%r8" (.reg "%rcx")
      , .mov "%rcx" (.reg "%rbp")
      , .xor_ "%rcx" (.reg "%r8")
      , .mov "%rdx" (.reg "%rcx") ] := by
  refine DecSim.frame _ _ ?_ (cmpPR_runBlock rsp n t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

/-- The comparison step: the two borrow chains, their difference and the selection against
    the previous result. -/
theorem cmp_seg_chain (n t y : Nat) :
    DecSim (cmpRel rp ap bp rsp cmLiveD cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp cmLiveE cmpK False (cmpPR rsp n t y))
      (cmpLoopBodyLit.drop 10 |>.take 61)
      [ .mov "%r11" (.imm 18446744073709551615)
      , .mov "%r12" (.reg "%r8")
      , .xor_ "%r12" (.reg "%r11")
      , .mov "%r11" (.reg "%r12")
      , .and_ "%r11" (.reg "%r10")
      , .mov "%r12" (.reg "%r11")
      , .mov "%r11" (.reg "%r8")
      , .xor_ "%r11" (.reg "%r10")
      , .mov "%r13" (.imm 18446744073709551615)
      , .mov "%rdx" (.reg "%r11")
      , .xor_ "%rdx" (.reg "%r13")
      , .mov "%r11" (.reg "%r8")
      , .sub "%r11" (.reg "%r10")
      , .mov "%r13" (.reg "%rdx")
      , .and_ "%r13" (.reg "%r11")
      , .mov "%rdx" (.reg "%r13")
      , .mov "%r11" (.reg "%r12")
      , .xor_ "%r11" (.reg "%rdx")
      , .mov "%r13" (.reg "%r12")
      , .and_ "%r13" (.reg "%rdx")
      , .mov "%rdx" (.reg "%r11")
      , .xor_ "%rdx" (.reg "%r13")
      , .mov "%r11" (.imm 63)
      , .mov "%r11" (.reg "%rdx")
      , .shr "%r11" (.imm 63)
      , .mov "%rdx" (.reg "%r11")
      , .mov "%r11" (.imm 18446744073709551615)
      , .mov "%r12" (.reg "%r10")
      , .xor_ "%r12" (.reg "%r11")
      , .mov "%r11" (.reg "%r12")
      , .and_ "%r11" (.reg "%r8")
      , .mov "%r12" (.reg "%r11")
      , .mov "%r11" (.reg "%r10")
      , .xor_ "%r11" (.reg "%r8")
      , .mov "%r13" (.imm 18446744073709551615)
      , .mov "%rcx" (.reg "%r11")
      , .xor_ "%rcx" (.reg "%r13")
      , .mov "%r11" (.reg "%r10")
      , .sub "%r11" (.reg "%r8")
      , .mov "%r8" (.reg "%rcx")
      , .and_ "%r8" (.reg "%r11")
      , .mov "%rcx" (.reg "%r8")
      , .mov "%r8" (.reg "%r12")
      , .xor_ "%r8" (.reg "%rcx")
      , .mov "%r10" (.reg "%r12")
      , .and_ "%r10" (.reg "%rcx")
      , .mov "%rcx" (.reg "%r8")
      , .xor_ "%rcx" (.reg "%r10")
      , .mov "%r8" (.imm 63)
      , .mov "%r8" (.reg "%rcx")
      , .shr "%r8" (.imm 63)
      , .mov "%rcx" (.reg "%r8")
      , .mov "%r8" (.reg "%rcx")
      , .sub "%r8" (.reg "%rdx")
      , .mov "%rcx" (.reg "%r8")
      , .mov "%rdx" (.imm 0)
      , .mov "%r8" (.imm 18446744073709551615)
      , .mov "%r10" (.reg "%rdx")
      , .xor_ "%r10" (.reg "%r8")
      , .mov "%rdx" (.reg "%r10")
      , .and_ "%rdx" (.reg "%rbp")
      , .mov "%r8" (.reg "%rdx")
      , .mov "%rdx" (.imm 0)
      , .mov "%r10" (.reg "%rdx")
      , .xor_ "%r10" (.reg "%rbp")
      , .mov "%rdx" (.imm 18446744073709551615)
      , .mov "%r11" (.reg "%r10")
      , .xor_ "%r11" (.reg "%rdx")
      , .mov "%rdx" (.imm 0)
      , .mov "%r10" (.reg "%rdx")
      , .sub "%r10" (.reg "%rbp")
      , .mov "%rdx" (.reg "%r11")
      , .and_ "%rdx" (.reg "%r10")
      , .mov "%r10" (.reg "%rdx")
      , .mov "%rdx" (.reg "%r8")
      , .xor_ "%rdx" (.reg "%r10")
      , .mov "%r11" (.reg "%r8")
      , .and_ "%r11" (.reg "%r10")
      , .mov "%r8" (.reg "%rdx")
      , .xor_ "%r8" (.reg "%r11")
      , .mov "%rdx" (.imm 63)
      , .mov "%rdx" (.reg "%r8")
      , .shr "%rdx" (.imm 63)
      , .mov "%r8" (.reg "%rdx")
      , .mov "%rdx" (.imm 1)
      , .mov "%r10" (.reg "%r8")
      , .sub "%r10" (.reg "%rdx")
      , .mov "%rdx" (.reg "%r10")
      , .mov "%r8" (.reg "%rcx")
      , .xor_ "%r8" (.reg "%rbp")
      , .mov "%rcx" (.reg "%r8")
      , .mov "%r8" (.reg "%rdx")
      , .and_ "%r8" (.reg "%rcx")
      , .mov "%rcx" (.reg "%rbp")
      , .xor_ "%rcx" (.reg "%r8")
      , .mov "%rdx" (.reg "%rcx") ] :=
  (cmp_chain0 rp ap bp rsp n t y).append <|
  (cmp_chain1 rp ap bp rsp n t y).append <|
  (cmp_chain2 rp ap bp rsp n t y).append <|
  (cmp_chain3 rp ap bp rsp n t y).append <|
  (cmp_chain4 rp ap bp rsp n t y).append <|
  (cmp_chain5 rp ap bp rsp n t y).append <|
  (cmp_chain6 rp ap bp rsp n t y).append <|
  cmp_chain7 rp ap bp rsp n t y

/-- The output word is disjoint from the source words. -/
def cmpDis : Prop :=
  ∀ j', j' < 8 →
    Disjoint8 ((cmpLay rp ap bp).addr "a4" 0) ((cmpLay rp ap bp).addr "a2" j')
      ∧ Disjoint8 ((cmpLay rp ap bp).addr "a4" 0) ((cmpLay rp ap bp).addr "a1" j')

theorem cmpK_afterStore (hdis : cmpDis rp ap bp) :
    ∀ A j', cmpK A j' → afterStore (cmpLay rp ap bp) cmpK "a4" "a4" 0 A j' := by
  rintro A j' (⟨rfl, hj'⟩ | ⟨rfl, hj'⟩ | ⟨rfl, hj'⟩)
  · exact Or.inl ⟨rfl, Or.inl (by omega)⟩
  · exact Or.inr ⟨by decide, Or.inr (Or.inl ⟨rfl, hj'⟩), ne_of_disjoint8 (hdis j' hj').1⟩
  · exact Or.inr ⟨by decide, Or.inr (Or.inr ⟨rfl, hj'⟩), ne_of_disjoint8 (hdis j' hj').2⟩

/-- The store of the selected result to `a4[L4_r11]`, index `0`. -/
theorem cmp_seg_store (n t y : Nat)
    (hsep : (cmpLay rp ap bp).Sep (cmpFrame rsp)) (hdis : cmpDis rp ap bp) :
    DecSim (cmpRel rp ap bp rsp cmLiveE cmpK False (cmpPR rsp n t y))
      (cmpRel rp ap bp rsp cmLiveE cmpK False (cmpP rsp n t y))
      [(.Lopn [.reg "a4"] "STOREIDX" [.arrIdx "a4" "L4_r11" 8, .reg "L4_r75"], .store 64 1)]
      [.loadMem "%r14" "%rsp" 72, .storeMemIdx "%r14" "%r9" 8 (.reg "%rdx")] :=
  DecSim.weaken
    (DecSim.frameWith _ _ (cmpP rsp n t y)
      (decSim_storeR (π := cmpPi) (L := cmLiveE) (Lay := cmpLay rp ap bp)
        (frame := cmpFrame rsp) (K := cmpK) (zl := False) hsep
        "a4" "a4" "L4_r11" "L4_r75" "%r14" "%rsp" "s0" 72 rfl rfl rfl (by decide +kernel)
        (by decide +kernel) (by decide +kernel) 0)
      (fun sa hp => ⟨by rw [hp.1.1]; rfl, by
        show (sa.regs "%r9").toNat = 0
        rw [hp.2]; rfl, Or.inl ⟨rfl, by decide⟩⟩)
      (fun sa hp => cmpP_runBlock rsp n t y _ (by decide +kernel) sa hp.1))
    (fun _ _ _ h => h)
    (fun _ _ _ h => ⟨h.1.mono (fun _ hr => hr) id (cmpK_afterStore rp ap bp hdis), h.2⟩)

/-- The two compares against the spilled source pointers write no register and no memory. -/
theorem decSim_cmpMem2 {L : String → Prop} {K : String → Nat → Prop} (C B : String) (o1 o2 : Int) :
    DecSim (DecLsemCorr cmpPi L (cmpLay rp ap bp) (cmpFrame rsp) K False)
      (DecLsemCorr cmpPi L (cmpLay rp ap bp) (cmpFrame rsp) K False) []
      [.cmpMem C B o1, .cmpMem C B o2] := by
  refine DecSim.machBlock fun sa b zf h => ?_
  have hr : (aMachine.runBlock sa [.cmpMem C B o1, .cmpMem C B o2]).regs = sa.regs := rfl
  have hm : (aMachine.runBlock sa [.cmpMem C B o1, .cmpMem C B o2]).mem = sa.mem := rfl
  exact { regs := fun r hr' => by rw [hr]; exact h.regs r hr'
          zfEq := fun hz => hz.elim
          cells := fun A j hk => by
            obtain ⟨hj, arr, ha, hc⟩ := h.cells A j hk
            exact ⟨hj, arr, ha, by rw [hm]; exact hc⟩
          slots := fun A q hq => by rw [hm]; exact h.slots A q hq }

/-- The feedback copy, the index advance, the counter decrement, the two compares against
    the spilled pointers (machine only), the compare against the count and the back-edge
    compare. -/
theorem cmp_seg_tail (m t : Nat) (htm : t < m) :
    DecSim (cmpRel rp ap bp rsp cmLiveE cmpK False (cmpP rsp m t (m - t)))
      (cmpRel rp ap bp rsp cmLive cmpK True (cmpQ rsp m m t))
      [movRI "a4" "a4", addImmI "Lidx4" "Lidx4" 1, subImmI "Lctr4" "Lctr4" 1,
        cmpRI "Lctr4" (.reg "a0"), cmpRI "Lctr4" (.imm 0)]
      [.mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1), .sub "%rdi" (.imm 1),
        .cmpMem "%rdi" "%rsp" 0, .cmpMem "%rdi" "%rsp" 8,
        .cmp "%rdi" (.reg "%rsi"), .cmp "%rdi" (.imm 0)] := by
  have hA : DecSim (DecLsemCorr cmpPi cmLiveE (cmpLay rp ap bp) (cmpFrame rsp) cmpK False)
      (DecLsemCorr cmpPi cmLive (cmpLay rp ap bp) (cmpFrame rsp) cmpK False)
      [movRI "a4" "a4", addImmI "Lidx4" "Lidx4" 1, subImmI "Lctr4" "Lctr4" 1]
      [.mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1), .sub "%rdi" (.imm 1)] := by
    decsim_chain
    exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)
  have hC : DecSim (DecLsemCorr cmpPi cmLive (cmpLay rp ap bp) (cmpFrame rsp) cmpK False)
      (DecLsemCorr cmpPi cmLive (cmpLay rp ap bp) (cmpFrame rsp) cmpK True)
      [cmpRI "Lctr4" (.reg "a0"), cmpRI "Lctr4" (.imm 0)]
      [.cmp "%rdi" (.reg "%rsi"), .cmp "%rdi" (.imm 0)] := by
    decsim_chain
    exact fun _ _ _ h => h
  refine DecSim.frame _ _ (hA.append ((decSim_cmpMem2 rp ap bp rsp "%rdi" "%rsp" 0 8).append hC))
    (fun sa hp => ?_)
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have ea : ∀ (s : AState) (X x : String) (k : Nat), (evalInstrA s (.add X (.imm k))).regs x
      = if x = X then s.regs X + BitVec.ofNat 64 k else s.regs x := fun _ _ _ _ => rfl
  have es : ∀ (s : AState) (X x : String) (k : Nat), (evalInstrA s (.sub X (.imm k))).regs x
      = if x = X then s.regs X - BitVec.ofNat 64 k else s.regs x := fun _ _ _ _ => rfl
  have ec : ∀ (s : AState) (X : String) (o : JOperand), (evalInstrA s (.cmp X o)).regs
      = s.regs := fun _ _ _ => rfl
  have ecm : ∀ (s : AState) (X B : String) (o : Int), (evalInstrA s (.cmpMem X B o)).regs
      = s.regs := fun _ _ _ _ => rfl
  have ez : ∀ (s : AState) (X : String) (k : Nat),
      (evalInstrA s (.cmp X (.imm k))).flags.zf.getD false
        = ZF_of_word (s.regs X - BitVec.ofNat 64 k) := fun _ _ _ => rfl
  have hm : m - t = m - (t + 1) + 1 := by omega
  obtain ⟨h1, h2, h3, h4⟩ := hp
  rw [show aMachine.runBlock sa [.mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1),
      .sub "%rdi" (.imm 1), .cmpMem "%rdi" "%rsp" 0, .cmpMem "%rdi" "%rsp" 8,
      .cmp "%rdi" (.reg "%rsi"), .cmp "%rdi" (.imm 0)]
    = evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
      (.mov "%rbx" (.reg "%rbx"))) (.add "%rax" (.imm 1))) (.sub "%rdi" (.imm 1)))
      (.cmpMem "%rdi" "%rsp" 0)) (.cmpMem "%rdi" "%rsp" 8)) (.cmp "%rdi" (.reg "%rsi")))
      (.cmp "%rdi" (.imm 0))
    from rfl]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (config := { decide := true }) only [ec, ecm, em, ea, es, ite_false]
    exact h1
  · simp (config := { decide := true }) only [ec, ecm, em, ea, es, ite_true, ite_false]
    rw [h2]; exact (BitVec.ofNat_add t 1).symm
  · simp (config := { decide := true }) only [ec, ecm, em, ea, es, ite_true, ite_false]
    rw [h3, hm, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · simp (config := { decide := true }) only [ec, ecm, em, ea, es, ite_false]
    exact h4
  · rw [ez]
    simp (config := { decide := true }) only [ec, ecm, em, ea, es, ite_true, ite_false]
    rw [h3, hm, BitVec.ofNat_add, BitVec.add_sub_cancel, ZF_of_word_sub]

/-- **One trip of the shipped `mpn_cmp_ct` loop**, for each trip `t < m ≤ 8`. -/
theorem cmp_trip (m : Nat) (hm : m ≤ 8) (hsep : (cmpLay rp ap bp).Sep (cmpFrame rsp))
    (hdis : cmpDis rp ap bp) (t : Nat) (ht : t < m) :
    DecSim (cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m t (m - t)))
      (cmpRel rp ap bp rsp cmLive cmpK True (cmpQ rsp m m t))
      (cmpLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (cmpDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (cmp_seg_idx rp ap bp rsp m t (m - t) ht hm False).append <|
  (cmp_seg_load2 rp ap bp rsp m t (m - t) ht hm).append <|
  (cmp_seg_load1 rp ap bp rsp m t (m - t) ht hm).append <|
  (cmp_seg_load4 rp ap bp rsp m t (m - t)).append <|
  (cmp_seg_chain rp ap bp rsp m t (m - t)).append <|
  (cmp_seg_store rp ap bp rsp m t (m - t) hsep hdis).append <|
  cmp_seg_tail rp ap bp rsp m t ht

def cmpG (m : Nat) : AState → LstateM → Bool → Prop :=
  cmpRel rp ap bp rsp cmLive cmpK True
    (fun sa => cmpP rsp m 0 m sa ∧ sa.flags.zf.getD false = (BitVec.ofNat 64 m == 0#64))

theorem cmp_guard (m : Nat) (zl : Prop) :
    DecSim (cmpRel rp ap bp rsp cmLive cmpK zl (cmpP rsp m 0 m)) (cmpG rp ap bp rsp m)
      [cmpRI "Lctr4" (.imm 0)] [.cmp "%rdi" (.imm 0)] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ⟨hp, ?_⟩)
  · exact decSim_cmpImm_r "Lctr4" "%rdi" 0 rfl (by decide +kernel)
  · show ZF_of_word (sa.regs "%rdi" - BitVec.ofNat 64 0) = _
    rw [hp.2.2.1, ZF_of_word_sub]

theorem cmp_guard_flag (m : Nat) (hm : m ≤ 8) :
    ∀ sa b zf, cmpG rp ap bp rsp m sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0) := by
  intro sa b zf ⟨h, _, hz⟩
  have e := h.zfEq trivial
  refine ⟨e, ?_⟩
  rw [← e, hz]
  exact ofNat_beq_zero_iff m (by omega)

theorem cmp_guard_inv (m : Nat) :
    ∀ sa b zf pc, cmpG rp ap bp rsp m sa b zf →
      cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m 0 (m - 0)) sa (b.setLpc pc) zf :=
  fun _ _ _ pc ⟨h, hp, _⟩ => ⟨(h.setLpc pc).mono (fun _ hr => hr) False.elim (fun _ _ h => h), hp⟩

theorem cmp_trip_flag (m : Nat) (hm : m ≤ 8) :
    ∀ t, t < m → ∀ sa b zf, cmpRel rp ap bp rsp cmLive cmpK True (cmpQ rsp m m t) sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m) := by
  intro t ht sa b zf ⟨h, _, hz⟩
  have e := h.zfEq trivial
  refine ⟨e, ?_⟩
  rw [← e, hz, ofNat_beq_zero_iff _ (by omega)]
  omega

theorem cmp_trip_next (m : Nat) :
    ∀ t, t < m → ∀ sa b zf pc, cmpRel rp ap bp rsp cmLive cmpK True (cmpQ rsp m m t) sa b zf →
      cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m (t + 1) (m - (t + 1))) sa
        (b.setLpc pc) zf :=
  fun _ _ _ _ _ pc ⟨h, hp, _⟩ =>
    ⟨(h.setLpc pc).mono (fun _ hr => hr) False.elim (fun _ _ h => h), hp⟩

end Trip



/-! ## 6. The prologue and the epilogue -/

/-- The register map at the entry: `rp` (`a4`) in `%rdi`, `ap` (`a2`) in `%rsi`, `bp` (`a1`)
    in `%rdx`, the count (`a0`) in `%rcx`. -/
def cmpPi0 (r : String) : String :=
  if r = "a4" then "%rdi" else if r = "a2" then "%rsi" else if r = "a1" then "%rdx"
  else if r = "a0" then "%rcx" else r

abbrev cmpArgs0 (r : String) : Prop := r ∈ ["a4", "a2", "a1", "a0"]
abbrev cmpArgs (r : String) : Prop := r ∈ ["a4", "a0"]

def cmpLay0 (rp ap bp : BitVec 64) : Layout := { cmpLay rp ap bp with slot := fun _ => none }

def cmpEntry (rp ap bp rsp : BitVec 64) (m : Nat) (sa : AState) : Prop :=
  sa.regs "%rsp" = rsp + BitVec.ofInt 64 80 ∧ sa.regs "%rdi" = rp ∧ sa.regs "%rsi" = ap
    ∧ sa.regs "%rdx" = bp ∧ sa.regs "%rcx" = BitVec.ofNat 64 m

def cmpStackSep (rp ap bp rsp : BitVec 64) : Prop :=
  ∀ A j, cmpK A j → ∀ o : Int, -16 ≤ o → o ≤ 72 →
    Disjoint8 (rsp + BitVec.ofInt 64 o) ((cmpLay rp ap bp).addr A j)

/-- The machine part of the prologue. -/
def cmpPre18 : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-80)
  , .storeMem "%rsp" 72 (.reg "%rdi"), .storeMem "%rsp" 64 (.reg "%rsi")
  , .storeMem "%rsp" 56 (.reg "%rbx"), .storeMem "%rsp" 48 (.reg "%rbp")
  , .storeMem "%rsp" 40 (.reg "%r12"), .storeMem "%rsp" 32 (.reg "%r13")
  , .storeMem "%rsp" 24 (.reg "%r14"), .storeMem "%rsp" 16 (.reg "%r15")
  , .mov "%r14" (.reg "%rsi")
  , .storeMem "%rsp" (-8) (.reg "%rdx"), .storeMem "%rsp" (-16) (.reg "%rcx")
  , .loadMem "%rbx" "%rsp" 72, .loadMem "%r15" "%rsp" 64, .storeMem "%rsp" 0 (.reg "%r15")
  , .loadMem "%r15" "%rsp" (-8), .storeMem "%rsp" 8 (.reg "%r15")
  , .loadMem "%rsi" "%rsp" (-16) ]

theorem cmpDecPre_eq : cmpDecPre = cmpPre18 ++
    [.mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rsi")] := rfl

section Pre

variable (rp ap bp rsp : BitVec 64)

theorem cmp_pre18 (m : Nat) (zl : Prop) (hstk : cmpStackSep rp ap bp rsp) :
    DecSim (fun sa b zf => DecLsemCorr cmpPi0 cmpArgs0 (cmpLay0 rp ap bp) (fun _ => none) cmpK
        zl sa b zf ∧ cmpEntry rp ap bp rsp m sa)
      (cmpRel rp ap bp rsp cmpArgs cmpK False
        (fun sa => sa.regs "%rsp" = rsp ∧ sa.regs "%rsi" = BitVec.ofNat 64 m))
      [] cmpPre18 := by
  refine DecSim.machBlock fun sa b zf ⟨h, hrsp, hrdi, hrsi, hrdx, hrcx⟩ => ?_
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have emm : ∀ (s : AState) (X Y : String), (evalInstrA s (.mov X (.reg Y))).mem = s.mem :=
    fun _ _ _ => rfl
  have es : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).regs = s.regs := fun _ _ _ _ => rfl
  have esm : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).mem
        = write64 s.mem (s.regs B + BitVec.ofInt 64 o) (s.regs X) := fun _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elem : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int),
      (evalInstrA s (.lea D B I sc o)).mem = s.mem := fun _ _ _ _ _ _ => rfl
  have hlea : sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (-80)
      = rsp := by
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero, BitVec.add_assoc,
      show BitVec.ofInt 64 80 + BitVec.ofInt 64 (-80) = 0#64 by decide +kernel, BitVec.add_zero]
  simp only [cmpPre18, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
  generalize hs' : evalInstrA _ (.loadMem "%rsi" "%rsp" (-16)) = s'
  have hmem := congrArg AState.mem hs'
  have hregs := fun x => congrArg (fun s => AState.regs s x) hs'
  simp (config := { decide := true }) only [em, emm, es, esm, elm, ele, elem,
    evalInstrA_loadMem_regs', ite_true, ite_false, hlea] at hmem hregs
  simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
    [read64_write64_same, read64_write64_of_disjoint] at hregs
  generalize hM : write64 (write64 (write64 (write64 (write64 (write64 (write64 (write64
    (write64 (write64 (write64 (write64 sa.mem _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _)
    _ _) _ _ = M at hmem
  have hcell : ∀ A j, cmpK A j → read64 M ((cmpLay rp ap bp).addr A j)
      = read64 sa.mem ((cmpLay rp ap bp).addr A j) := by
    intro A j hk
    have hd := fun o h1 h2 => hstk A j hk o h1 h2
    rw [← hM]
    rw [read64_write64_of_disjoint _ _ _ _ (hd (8) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (0) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (-16) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (-8) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (16) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (24) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (32) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (40) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (48) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (56) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (64) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (72) (by omega) (by omega))]
  have hs0 : read64 M (rsp + BitVec.ofInt 64 72) = rp := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrdi
  have hs1 : read64 M (rsp + BitVec.ofInt 64 64) = ap := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrsi
  have hs2 : read64 M (rsp + BitVec.ofInt 64 (-8)) = bp := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrdx
  have hr : ∀ x, s'.regs x = _ := fun x => (hregs x).symm
  refine ⟨⟨fun r hr' => ?_, fun hz => hz.elim, fun A j hk => ?_, fun A q hq => ?_⟩, ?_, ?_⟩
  · simp only [cmpArgs, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · show _ = some (s'.regs "%rbx")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a4" (by decide)
    · show _ = some (s'.regs "%rsi")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a0" (by decide)
  · obtain ⟨hj, arr, ha, hc⟩ := h.cells A j hk
    exact ⟨hj, arr, ha, by rw [← hmem, hcell A j hk]; exact hc⟩
  · simp only [cmpLay] at hq
    split_ifs at hq with h0 h1 h2
    · subst h0; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs0]; rfl⟩
    · subst h1; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs1]; rfl⟩
    · subst h2; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs2]; rfl⟩
  · rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
  · rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]; exact hrcx

theorem cmp_seg_seeds (m : Nat) :
    DecSim (cmpRel rp ap bp rsp cmpArgs cmpK False
        (fun sa => sa.regs "%rsp" = rsp ∧ sa.regs "%rsi" = BitVec.ofNat 64 m))
      (cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m 0 m))
      [movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"]
      [.mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rsi")] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ?_)
  · decsim_chain
    exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)
  · have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
        = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
    have ei : ∀ (s : AState) (X x : String) (n : Nat), (evalInstrA s (.mov X (.imm n))).regs x
        = if x = X then BitVec.ofNat 64 n else s.regs x := fun _ _ _ _ => rfl
    simp only [Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp (config := { decide := true }) only [em, ei, ite_false]; exact hp.1
    · simp (config := { decide := true }) only [em, ei, ite_true, ite_false]
    · simp (config := { decide := true }) only [em, ei, ite_true, ite_false]; exact hp.2
    · simp (config := { decide := true }) only [em, ei, ite_false]; exact hp.2

theorem cmp_pre (m : Nat) (zl : Prop) (hstk : cmpStackSep rp ap bp rsp) :
    DecSim (fun sa b zf => DecLsemCorr cmpPi0 cmpArgs0 (cmpLay0 rp ap bp) (fun _ => none) cmpK
        zl sa b zf ∧ cmpEntry rp ap bp rsp m sa)
      (cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m 0 m))
      [movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"] cmpDecPre := by
  rw [cmpDecPre_eq]
  exact (cmp_pre18 rp ap bp rsp m zl hstk).append (cmp_seg_seeds rp ap bp rsp m)

def cmpOut (sa : AState) (b : LstateM) : Prop :=
  ∃ arr : Fin 1 → BitVec 64, decodeArrM b "a4" 64 1 = some arr
    ∧ read64 sa.mem ((cmpLay rp ap bp).addr "a4" 0) = stackGet arr 0

theorem cmp_post (m : Nat) :
    ∀ sa b, cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m m (m - m)) sa b true →
      cmpOut rp ap bp (aMachine.runBlock sa cmpDecPost) b := by
  intro sa b ⟨h, _⟩
  have hmem : (aMachine.runBlock sa cmpDecPost).mem = sa.mem := rfl
  obtain ⟨_, arr, ha, hr⟩ := h.cells "a4" 0 (Or.inl ⟨rfl, by decide⟩)
  exact ⟨arr, ha, by rw [hmem]; exact hr⟩

end Pre

/-! ## 7. The node, the fold and the result -/

def cmpFuel (n : Nat) : Nat := nodeFuel 3 76 n

/-- **The shipped `mpn_cmp_ct` node on both machines, with its fuel.** -/
theorem cmp_node_halts_fuel (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 8)
    (hsep : (cmpLay rp ap bp).Sep (cmpFrame rsp)) (hdis : cmpDis rp ap bp)
    (hstk : cmpStackSep rp ap bp rsp)
    (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : DecLsemCorr cmpPi0 cmpArgs0 (cmpLay0 rp ap bp) (fun _ => none) cmpK False sa b zf
      ∧ cmpEntry rp ap bp rsp m sa) :
    ∃ sa' t, Halts aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 0 sa sa'
      ∧ (∀ k, cmpFuel m ≤ k →
          lsemFuelMemF (singletonProgM fn
            (canonNodeRM cmpTau 4 "a4" "a0" cmpUpdate false ["a0"])) k
            { prog := { base := b, lfn := fn }, zf := zf } = some t)
      ∧ cmpOut rp ap bp sa' t.prog.base := by
  have hsim : ∀ t, t < m →
      DecSim (cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m t (m - t)))
        (cmpRel rp ap bp rsp cmLive cmpK True (cmpQ rsp m m t))
        (cmpLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)])
        (cmpDecLoop.body ++ [cmpDecLoop.cmpInstr]) := by
    intro t ht
    exact cmp_trip rp ap bp rsp m hm hsep hdis t ht
  have hg : DecSim (cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m 0 m))
      (cmpG rp ap bp rsp m) [cmpRI "Lctr4" (.imm 0)] [cmpDecLoop.cmpInstr] :=
    cmp_guard rp ap bp rsp m False
  rw [cmpNode_eq]
  exact decNode_halts_fuel fn [movRI "a4" "a4", movII "Lidx4" 0, movRI "Lctr4" "a0"]
    cmpLoopBodyLit 4 (4 + 0x40000000) "Lctr4" cmpDecLoop m _ _ (cmpG rp ap bp rsp m)
    (fun t => cmpRel rp ap bp rsp cmLive cmpK False (cmpP rsp m t (m - t)))
    (fun t => cmpRel rp ap bp rsp cmLive cmpK True (cmpQ rsp m m t)) (cmpOut rp ap bp)
    cmpDecPre cmpDecPost cmpSeeds_isLopn cmpLoopBody_isLopn cmpNode_top cmpNode_end
    (cmp_pre rp ap bp rsp m False hstk) hg (cmp_guard_flag rp ap bp rsp m hm)
    (cmp_guard_inv rp ap bp rsp m) hsim (cmp_trip_flag rp ap bp rsp m hm)
    (cmp_trip_next rp ap bp rsp m) (cmp_post rp ap bp rsp m) sa b zf hpc hE

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
  (cmpFold cmpFoldStep cmpSign vmBody cmpLimbBodyLowCT cmpFold_val_full)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote
  (cmpLimbBody_run cmpEnv consistentS_cmpEnv cmpLimbBody_covered cmpUpdate_eq)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC (frontLoopBodyJ_denote_foldl)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit (segCells)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)

/-- **The front-compiled compare body folds `cmpFoldStep`.** -/
theorem cmp_fold_denote (ap bp : Fin NU → BitVec 64) (nv : BitVec 64) (hn : 0 < nv.toNat)
    (acc : Fin NR → BitVec 64) :
    JLoopBodyN.denote ⟨nv.toNat, cmpUpdate⟩
        (HVector.cons ap (HVector.cons bp (HVector.cons nv HVector.nil)) :
          Ctxt.Valuation ([AO, AO, r64] : Ctxt jasminDialect)) acc
      = cmpFold ap bp (nv.toNat - 1) nv.toNat acc :=
  frontLoopBodyJ_denote_foldl (accCTy := .memref NR)
    (invCTys := [.memref NU, .memref NU, .sword 64]) vmBody "rp" cmpLimbBodyLowCT
    cmpLimbBody_covered (.cons ap (.cons bp (.cons nv .nil)))
    (fun arr tt => cmpFoldStep ap bp (nv.toNat - 1) arr tt) nv.toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ := cmpLimbBody_run ap bp arr nv tt hn htt
      exact ⟨cmpEnv ap bp arr (BitVec.ofNat 64 tt) nv, env',
        consistentS_cmpEnv ap bp arr (BitVec.ofNat 64 tt) nv, hrun, hrp⟩)
    cmpUpdate_eq acc

/-- **The decoded shipped `mpn_cmp_ct` writes the comparison sign.** Under the entry
    correspondence (count `0 < m ≤ 8`), the seed agreement with the source words `ap`, `bp`,
    the count `m` and the result seed `arr0` whose word is `0`: the machine halts on the
    decoded layout and the word at `rp` is `cmpSign (value ap[0..m)) (value bp[0..m))`. -/
theorem cmp_decoded_val (rp app bpp rsp : BitVec 64) (m : Nat) (hm0 : 0 < m) (hm : m ≤ 8)
    (hsep : (cmpLay rp app bpp).Sep (cmpFrame rsp)) (hdis : cmpDis rp app bpp)
    (hstk : cmpStackSep rp app bpp rsp)
    (fn : String) (sa : AState) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hE : DecLsemCorr cmpPi0 cmpArgs0 (cmpLay0 rp app bpp) (fun _ => none) cmpK False sa b0 zf
      ∧ cmpEntry rp app bpp rsp m sa)
    (ap bp : Fin NU → BitVec 64) (arr0 : Fin NR → BitVec 64) (h0 : memGetDyn arr0 0 = 0)
    (hseed : StoreAgreesM (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (pullM cmpTau (b0.setReg (loopIdx 4) (0#64)))
      (tripValArrMN (invTys := ([AO, AO, r64] : Ctxt jasminDialect))
        (.cons ap (.cons bp (.cons (BitVec.ofNat 64 m) .nil))) 0 arr0)) :
    ∃ sa', Halts aMachine (nodeLayout cmpDecPre cmpDecLoop cmpDecPost) 0 sa sa'
      ∧ read64 sa'.mem rp
          = cmpSign (bignumVal (segCells ap 0 m)) (bignumVal (segCells bp 0 m)) := by
  obtain ⟨sa', t1, hh, hrun1, arr, ha, hw⟩ :=
    cmp_node_halts_fuel rp app bpp rsp m hm hsep hdis hstk fn sa b0 zf hpc hE
  have hregs : ∀ r ∈ ["a0"], ∃ j, j < ([AO, AO, r64] : Ctxt jasminDialect).length ∧
      r = cmpTau (argName j) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨0, by decide, by rw [cmpTau_arg (by decide)]; rfl⟩
  have hinv : ∀ j, j < ([AO, AO, r64] : Ctxt jasminDialect).length →
      (b0.reg.getW (cmpTau (argName j)) 64).isSome := by
    intro j hj
    rw [cmpTau_arg hj]
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by
      have : j < 3 := hj
      omega
    rcases hj3 with rfl | rfl | rfl
    · rw [show argName 0 = "a0" from rfl, hE.1.regs "a0" (by decide)]; rfl
    · rw [show argName 1 = "a1" from rfl, hE.1.regs "a1" (by decide)]; rfl
    · rw [show argName 2 = "a2" from rfl, hE.1.regs "a2" (by decide)]; rfl
  have hcnt : b0.reg.getW "a0" 64 = some (BitVec.ofNat 64 m) := by
    rw [hE.1.regs "a0" (by decide)]
    exact congrArg some hE.2.2.2.2.2
  obtain ⟨k, t2, hrun2, hdec⟩ := cmp_canon_machine_denote false ["a0"] hregs
    (.cons ap (.cons bp (.cons (BitVec.ofNat 64 m) .nil))) fn "a0" (by decide +kernel) b0 zf
    hpc arr0 hseed hinv m (by omega) hcnt
  have he : t1 = t2 := lsemFuelMemF_det _ _ _ _ _ _ (hrun1 _ (Nat.le_refl _)) hrun2
  subst he
  have hd : decodeArrM t1.prog.base "a4" 64 1
      = some (JLoopBodyN.denote ⟨m, cmpUpdate⟩
          (.cons ap (.cons bp (.cons (BitVec.ofNat 64 m) .nil))) arr0) := hdec
  rw [ha] at hd
  obtain rfl := Option.some.inj hd
  have hmv : (BitVec.ofNat 64 m).toNat = m := ofNat_toNat_lt m (by omega)
  have key := cmp_fold_denote ap bp (BitVec.ofNat 64 m) (by rw [hmv]; exact hm0) arr0
  rw [hmv] at key
  refine ⟨sa', hh, ?_⟩
  have hw0 : read64 sa'.mem rp = stackGet (JLoopBodyN.denote ⟨m, cmpUpdate⟩
      (.cons ap (.cons bp (.cons (BitVec.ofNat 64 m) .nil))) arr0) 0 := by
    rw [← hw]
    congr 1
    show rp = rp + BitVec.ofNat 64 (8 * 0)
    rw [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero]
  rw [hw0]
  refine (congrArg (fun x => stackGet x 0) key).trans ?_
  rw [DialectToJasminComCorrect.stackGet_eq_memGetDyn]
  have h := cmpFold_val_full ap bp (m - 1) arr0 (by decide) h0
  rwa [show m - 1 + 1 = m by omega] at h

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)

/-- **`mpn_cmp_ct`, from the linked program to its result word.** The program
    `MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct"` that `MpnRuntimeBytesEmit.kernels` maps to the
    linked object is one function `mpn_cmp_ct`; its function bytes decode to `prog`; and from
    every entry state with `rp`, `ap`, `bp` and the count `0 < m ≤ 8` in `%rdi`, `%rsi`, `%rdx`,
    `%rcx`, the result word separated from the source words and all from the frame, and a
    corresponding flag-machine state agreeing with the source words and a zero result seed:
    the machine halts on `prog` with `cmpSign (value ap[0..m)) (value bp[0..m))` at `rp`. -/
theorem mpn_cmp_ct_bytes_correct :
    ∃ f : Lfundef,
      (MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct").map (·.lp_funcs) = some [("mpn_cmp_ct", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp app bpp rsp : BitVec 64) (m : Nat), 0 < m → m ≤ 8 →
        (cmpLay rp app bpp).Sep (cmpFrame rsp) → cmpDis rp app bpp →
        cmpStackSep rp app bpp rsp →
        ∀ (sa : AState) (b0 : LstateM) (zf : Bool), b0.lpc = 0 →
        DecLsemCorr cmpPi0 cmpArgs0 (cmpLay0 rp app bpp) (fun _ => none) cmpK False sa b0 zf →
        cmpEntry rp app bpp rsp m sa →
        ∀ (ap bp : Fin NU → BitVec 64) (arr0 : Fin NR → BitVec 64), memGetDyn arr0 0 = 0 →
        StoreAgreesM (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
          (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
          (pullM cmpTau (b0.setReg (loopIdx 4) (0#64)))
          (tripValArrMN (invTys := ([AO, AO, r64] : Ctxt jasminDialect))
            (.cons ap (.cons bp (.cons (BitVec.ofNat 64 m) .nil))) 0 arr0) →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ read64 sa'.mem rp
              = cmpSign (bignumVal (segCells ap 0 m)) (bignumVal (segCells bp 0 m)) := by
  refine ⟨_, by rw [MpnRtExportTerm.cmpLprog_eq]; rfl,
    nodeLayout cmpDecPre cmpDecLoop cmpDecPost, ?_, fun rp app bpp rsp m hm0 hm hsep hdis hstk
    sa b0 zf hpc hE hent ap bp arr0 h0 hseed => ?_⟩
  · rw [MpnRtExportTerm.cmpPhysAbi_eq]
    exact MpnRtExportTerm.cmpPhysLit_decode
  · exact cmp_decoded_val rp app bpp rsp m hm0 hm hsep hdis hstk "mpn_cmp_ct" sa b0 zf hpc
      ⟨hE, hent⟩ ap bp arr0 h0 hseed

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpBytesValue
