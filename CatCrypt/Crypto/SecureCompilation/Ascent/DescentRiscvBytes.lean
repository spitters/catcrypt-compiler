/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64

/-!
# Descent output carried to RV64 bytes

`MultiBackendDemo.com_riscv_e2e` states that the RV64 block compiled from a supported
`Com` (`ComOK`, all-`reg 64` context) computes `Com.denote` over `runRBlock64`, with
symbolic register names (`v0`, `v1`, …). This module carries that statement to the bytes:
rename the block to RV64 registers by a renaming `ρ` that the liveness checker
`RiscvRename64.renGo` accepts, expand each `li` to `addi`/`slli` (`RiscvBytes64.expandLi`)
and encode (`RiscvBytes64.encodeMBlock64`).

## Main results

* `com_riscv_bytes`: when `renGo` accepts `ρ` on the compiled block with the result live
  out and every physical instruction passes `MInstOKb`, the encoded bytes decode to a
  block `c` such that, from every machine state holding the source valuation at the
  live-in registers, running `c` leaves `Com.denote` in the result register.

Both side conditions are decidable and are discharged per program by `decide +kernel`
(see `Demos.LeanSourceRiscvBytes`). The trust points are those of `RiscvBytes64`: that
`decodeMStream64` and `runM64` agree with an RV64 processor is not proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.DescentRiscvBytes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64

/-- The RV64 block the descent compiles a `Com` to, over symbolic names. -/
def comBlock {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) :
    List RInst64 :=
  lowerRBlock64 (regToROp (comToRegProg com Γ.length))

/-- The physical block: `comBlock` renamed by `ρ`, with every `li` expanded. -/
def comPhys {Γ : Ctxt jasminDialect} {t : JasminTy} (ρ : String → String)
    (com : Com jasminDialect Γ t) : List MInst64 :=
  expandLi (renameRBlock64 ρ (comBlock com))

/-- **Descent output at the bytes.** If `renGo` accepts `ρ` on the compiled block with the
    result name live out (returning the live-in names `Lin`), the result name is not a zero
    register, and every physical instruction passes `MInstOKb`, then the encoded physical
    block decodes to a block `c` such that, for every valuation `V` and every machine state
    `t` holding `V` at `ρ` of the live-in names, running `c` leaves `Com.denote com V` in
    `ρ` of the result name. -/
theorem com_riscv_bytes {Γ : Ctxt jasminDialect} {com : Com jasminDialect Γ (.reg 64)}
    (hok : ComOK com) (hΓ : AllReg64 Γ) (ρ : String → String) (Lin : List String)
    (hren : renGo ρ (comBlock com) [comRetName com Γ.length] = some Lin)
    (hret : ¬ (comRetName com Γ.length = "zero" ∨ comRetName com Γ.length = "x0"))
    (hb : (comPhys ρ com).all MInstOKb = true) :
    ∃ c, decodeMStream64 (comPhys ρ com).length (encodeMBlock64 (comPhys ρ com)) = some c ∧
      ∀ (V : Ctxt.Valuation Γ) (t : RState64),
        (∀ x ∈ Lin, t.get (ρ x) = (RState64.mk (envOf Γ.length V)).get x) →
        (runM64 t c).get (ρ (comRetName com Γ.length)) = Com.denote com V := by
  refine ⟨_, decodeMStream64_encode_b _ hb, fun V t ht => ?_⟩
  have hr := runRBlock64_rename ρ (comBlock com) _ Lin hren (RState64.mk (envOf Γ.length V)) t
    ht _ (List.mem_singleton_self _)
  rw [comPhys, runM64_expandLi, hr]
  simp only [RState64.get, hret, if_false]
  exact com_riscv_e2e hok hΓ V _ rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.DescentRiscvBytes
