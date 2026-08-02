/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
import CatCrypt.Crypto.SecureCompilation.VIR.ArrAbiOrch
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
import CatCrypt.Crypto.Pairing.Bls12_377Emit

/-!
# Validate: the orchestration front reproduces the BLS12-377 pairing-product

`Bls12_377Emit.pairingProductCom` is the canonical multi-leaf array-ABI
orchestration `Com` hand-authored with explicit de-Bruijn operand chains: two
`bls377_pairing` leaves over `G1`/`G2` buffers, accumulated by one
`bls377_Fp12_mul` leaf over `GT` buffers, returning the product. This module
re-sources that exact orchestration through the front combinator
`OrchestrationFront.buildOrchCom` — as a flat **phase schedule** with root-order
operand slots — and shows the two coincide, so the front-generated `Com` inherits
every downstream fact of the hand-authored one:

* **generation gate** — the schedule is well-formed: the front resolves it to a
  `some` (`pairingProductBuilt_isSome`);
* **exactness** — the generated `Com` is *definitionally* the hand-authored one
  (`pairingProductBuilt_eq`), so `pairingProductCom_denote`, the array-ABI
  backend, and the memory-safety framing all transfer verbatim;
* **denote gate** — the generated `Com` denotes to
  `fp12Mul (pairing P₁ Q₁) (pairing P₂ Q₂)` under the carried leaf agreement
  (`pairingProductBuilt_denote`), reusing `pairingProductCom_denote`;
* **shape gate (array-ABI KAT sketch)** — lowering the generated `Com` through
  `Com.toLprogArrAbi` + `renderLprogAtt` produces the SysV `.s` that `call`s the
  two opaque leaves with no unhandled-op sentinel (`pairingProductBuilt_asm_shape`),
  exactly the shape `Bls12_377Emit` asserts for the hand `Com`. The
  byte-identical correctness KAT is the existing Rust check against the AUCurves
  reference; this is the in-Lean shape gate on the emitted text.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFrontValidate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
open CatCrypt.Crypto.Pairing.Bls12_377Emit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogArrAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-! ## 1. The pairing-product as a phase schedule

`Γ₀ = [P₁ : G1, Q₁ : G2, P₂ : G1, Q₂ : G2]` (root slots, counting from the tail:
`Q₂ = 0`, `P₂ = 1`, `Q₁ = 2`, `P₁ = 3`). The two pairing results take slots `4`
and `5`, the product slot `6` (returned). -/

/-- The input buffer context: `P₁, Q₁, P₂, Q₂`. -/
def pairingProductCtxt : Ctxt jasminDialect :=
  [.stackArr 8 G1SZ, .stackArr 8 G2SZ, .stackArr 8 G1SZ, .stackArr 8 G2SZ]

/-- The pairing-product orchestration as a flat phase schedule:
    `e₁ = e(P₁,Q₁)`, `e₂ = e(P₂,Q₂)`, `out = e₁ · e₂`. -/
def pairingProductSchedule : List CallPhase :=
  [ { leaf := pairingLeafName, argTys := pairingArgTys, retTy := gtRetTy,
      argSlots := [3, 2] }              -- e₁ = e(P₁, Q₁)
  , { leaf := pairingLeafName, argTys := pairingArgTys, retTy := gtRetTy,
      argSlots := [1, 0] }              -- e₂ = e(P₂, Q₂)
  , { leaf := fp12MulLeafName, argTys := fp12MulArgTys, retTy := gtRetTy,
      argSlots := [4, 5] } ]           -- out = e₁ · e₂

/-! ## 2. Generation + exactness gates -/

/-- **Generation gate.** The front resolves the schedule (well-formed: every
    operand slot is in range with the declared buffer type). -/
theorem pairingProductBuilt_isSome :
    (buildOrchCom pairingProductCtxt pairingProductSchedule 6 gtRetTy).isSome = true := by
  rfl

/-- The front-generated pairing-product orchestration `Com`. -/
def pairingProductBuilt : Com jasminDialect pairingProductCtxt gtRetTy :=
  (buildOrchCom pairingProductCtxt pairingProductSchedule 6 gtRetTy).get
    pairingProductBuilt_isSome

/-- **Exactness.** The front generates *definitionally* the hand-authored
    `pairingProductCom` — the auto-resolved de-Bruijn operand chains coincide with
    the hand-threaded `.here`/`.there` chains, so every downstream fact of the hand
    `Com` transfers verbatim. -/
theorem pairingProductBuilt_eq : pairingProductBuilt = pairingProductCom := by
  rfl

/-! ## 3. Denote gate (value correctness under the leaf agreement) -/

/-- **Denote gate.** The front-generated orchestration denotes to
    `fp12Mul (pairing P₁ Q₁) (pairing P₂ Q₂)` under the carried
    `Bls377PairingLeavesAgree` — reusing `pairingProductCom_denote` through
    `pairingProductBuilt_eq`. -/
theorem pairingProductBuilt_denote (prims : Bls377Primitives)
    (hPair : Bls377PairingLeavesAgree prims jasminExtSem)
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    pairingProductBuilt.denote (.cons p1 (.cons q1 (.cons p2 (.cons q2 .nil))))
      = prims.fp12Mul (prims.pairing p1 q1) (prims.pairing p2 q2) := by
  rw [pairingProductBuilt_eq]
  exact pairingProductCom_denote prims hPair p1 q1 p2 q2

/-! ## 4. Shape gate (array-ABI emit KAT sketch)

Lower the front-generated `Com` through the owned array-ABI backend and render
the SysV `.s`. The gate asserts the emitted text `call`s the two opaque leaves
(the by-pointer gather/`call`/scatter shape) with no unhandled-op sentinel — the
same structural guarantee `Bls12_377Emit` gives for the hand `Com`. The
byte-identical correctness KAT is the existing Rust check against the AUCurves
BLS12-377 reference. -/

/-- The rendered array-ABI `.s` for the front-generated pairing-product. -/
def pairingProductBuiltAsm : String :=
  renderLprogAtt (Com.toLprogArrAbi pairingProductBuilt "bls377_pairing_product")

/-- **Shape gate.** The emitted `.s` carries the SysV label, `call`s the pairing
    and GT-multiply leaves, and has no `# UNHANDLED-OP` / `CALL:` / `BADMEM`
    sentinel — the front-sourced orchestration lowers to the same owned-x86 shape
    as the hand-authored one. -/
theorem pairingProductBuilt_asm_shape :
    strContains pairingProductBuiltAsm ".globl bls377_pairing_product"
    && strContains pairingProductBuiltAsm "call bls377_pairing"
    && strContains pairingProductBuiltAsm "call bls377_Fp12_mul"
    && !strContains pairingProductBuiltAsm "UNHANDLED"
    && !strContains pairingProductBuiltAsm "CALL:"
    && !strContains pairingProductBuiltAsm "BADMEM" := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFrontValidate
