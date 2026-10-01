/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.DescentRiscvBytes
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.LeanSourceRiscv
public import CatCrypt.Crypto.SecureCompilation.Fe25519MulLeafGoldenPath

/-!
# Lean source functions through the descent to RV64 bytes

`Demos.LeanSourceRiscv` carries `fun a b : BitVec 64 => a + b` and `a - b` through the
descent to `runRBlock64` over symbolic names. This module carries them, and the
multiply-accumulate column `Fe25519MulLeaf.fe25519MacColLoCom` (`acc_lo + a · b`), to
encoded RV64 bytes, as instances of `DescentRiscvBytes.com_riscv_bytes`. Each renaming is a
literal association list; `renGo` checks it and `MInstOKb` checks the decode round trip,
both by `decide +kernel`.

## ABI

| program | inputs | output | instructions |
|---|---|---|---|
| `fieldAddCom` (`a + b`) | `a` in `a0`, `b` in `a1` | `a0` | 1 |
| `descentSubCom` (`a - b`) | `a` in `a0`, `b` in `a1` | `a0` | 1 |
| `fe25519MacColLoCom` | `acc_lo` in `a0`, `a` in `a2`, `b` in `a3` | `a0` | 2 |

## Main results

* `addDescentBytes_correct`, `subDescentBytes_correct`: the bytes of the compiled block
  decode to a block leaving `a + b` (resp. `a - b`) in `a0`, for every machine state;
* `macColLoBytes_correct`: the same for the multiply-accumulate column, `acc_lo + a · b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.LeanSourceRiscvBytes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.DescentRiscvBytes

/-! ## Two-argument word operations -/

/-- `v0 ↦ a0`, `v1 ↦ a1`, the result `v2 ↦ a0`. -/
def twoArgAlloc : List (String × String) := [("v0", "a0"), ("v1", "a1"), ("v2", "a0")]

theorem twoArg_hyp (a b : BitVec 64) (t : RState64) (ha : t.get "a0" = a)
    (hb : t.get "a1" = b) :
    ∀ x ∈ ["v0", "v1"], t.get (nameOf twoArgAlloc x)
      = (RState64.mk (envOf 2 (twoArgVal a b))).get x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ha.trans rfl
  · exact hb.trans rfl

theorem addPhys_length : (comPhys (nameOf twoArgAlloc) FieldEmitGoldenPath.fieldAddCom).length = 1 := by
  decide +kernel

/-- **The encoded `fun a b => a + b`.** The bytes of its compiled RV64 block decode to one
    instruction `c` such that, for every machine state with `a` in `a0` and `b` in `a1`,
    running `c` leaves `a + b` in `a0`. -/
theorem addDescentBytes_correct :
    ∃ c, decodeMStream64 1
        (encodeMBlock64 (comPhys (nameOf twoArgAlloc) FieldEmitGoldenPath.fieldAddCom)) = some c ∧
      ∀ (a b : BitVec 64) (t : RState64), t.get "a0" = a → t.get "a1" = b →
        (runM64 t c).get "a0" = a + b := by
  obtain ⟨c, hc, h⟩ := com_riscv_bytes FieldEmitGoldenPath.fieldAddCom_ok
    FieldEmitGoldenPath.allReg64_two (nameOf twoArgAlloc) ["v0", "v1"] (by decide +kernel)
    (by decide) (by decide +kernel)
  rw [addPhys_length] at hc
  exact ⟨c, hc, fun a b t ha hb => h (twoArgVal a b) t (twoArg_hyp a b t ha hb)⟩

theorem subPhys_length : (comPhys (nameOf twoArgAlloc) descentSubCom).length = 1 := by
  decide +kernel

/-- **The encoded `fun a b => a - b`.** The bytes of its compiled RV64 block decode to one
    instruction `c` such that, for every machine state with `a` in `a0` and `b` in `a1`,
    running `c` leaves `a - b` in `a0`. -/
theorem subDescentBytes_correct :
    ∃ c, decodeMStream64 1 (encodeMBlock64 (comPhys (nameOf twoArgAlloc) descentSubCom))
        = some c ∧
      ∀ (a b : BitVec 64) (t : RState64), t.get "a0" = a → t.get "a1" = b →
        (runM64 t c).get "a0" = a - b := by
  obtain ⟨c, hc, h⟩ := com_riscv_bytes (com := descentSubCom) (binCom_ok .sub (by supported_op))
    FieldEmitGoldenPath.allReg64_two (nameOf twoArgAlloc) ["v0", "v1"] (by decide +kernel)
    (by decide) (by decide +kernel)
  rw [subPhys_length] at hc
  exact ⟨c, hc, fun a b t ha hb => h (twoArgVal a b) t (twoArg_hyp a b t ha hb)⟩

/-! ## The multiply-accumulate column -/

/-- `acc_lo` (`v3`) in `a0`, `acc_hi` (`v2`) in `a1`, `a` (`v1`) in `a2`, `b` (`v0`) in
    `a3`; the product `v4` in `t0` and the result `v5` in `a0`. -/
def macAlloc : List (String × String) :=
  [("v3", "a0"), ("v2", "a1"), ("v1", "a2"), ("v0", "a3"), ("v4", "t0"), ("v5", "a0")]

theorem macPhys_length :
    (comPhys (nameOf macAlloc) Fe25519MulLeaf.fe25519MacColLoCom).length = 2 := by
  decide +kernel

/-- **The encoded multiply-accumulate column.** The bytes of the compiled RV64 block of
    `fe25519MacColLoCom` decode to two instructions `c` such that, for every machine state
    with `acc_lo` in `a0`, `a` in `a2` and `b` in `a3`, running `c` leaves `acc_lo + a · b`
    in `a0`. -/
theorem macColLoBytes_correct :
    ∃ c, decodeMStream64 2
        (encodeMBlock64 (comPhys (nameOf macAlloc) Fe25519MulLeaf.fe25519MacColLoCom)) = some c ∧
      ∀ (accLo a b : BitVec 64) (t : RState64), t.get "a0" = accLo → t.get "a2" = a →
        t.get "a3" = b → (runM64 t c).get "a0" = accLo + a * b := by
  obtain ⟨c, hc, h⟩ := com_riscv_bytes Fe25519MulLeaf.fe25519MacColLoCom_ok
    Fe25519MulLeaf.allReg64_four (nameOf macAlloc) ["v1", "v0", "v3"] (by decide +kernel)
    (by decide) (by decide +kernel)
  rw [macPhys_length] at hc
  refine ⟨c, hc, fun accLo a b t hl ha hb => ?_⟩
  refine h (.cons accLo (.cons accLo (.cons a (.cons b .nil)))) t ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha.trans rfl
  · exact hb.trans rfl
  · exact hl.trans rfl

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.LeanSourceRiscvBytes.macColLoBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms macColLoBytes_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.LeanSourceRiscvBytes
