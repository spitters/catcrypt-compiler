/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VartimeBignumInverse

/-!
# Source-declared secrecy → the `cmdCT` level table (IF/CT transfer, phase 3)

`cmdCT cmd lt leafCT` (`Jasmin/LowCTCTAnalysis.lean`) checks constant-time on the
*emitted* kernel, but it takes the `lt : LevelTable` — the Public/Secret labeling
— as an **external** argument. In `VartimeBignumInverse.lean` that table is
hand-authored (`publicInvertLT` / `secretInvertLT`). This module supplies the
labeling from the **source's** secret-integer discipline instead.

`SourceSecrecy` models what the extraction (`haxpipeT`, phase 2) emits: the
per-binding secrecy the source secret-integer types declare, plus the set of
bindings produced by an explicit `declassify()` downgrade (the audit surface,
phase 4). `toLevelTable` turns it into the `LevelTable` that `cmdCT` consumes,
with `declassify` overriding a binding to `Public`.

The worked results tie this to the variable-time modular inverse:

* `vartimeInvert_rejected_from_secret_source` — a secret operand (ECDSA nonce /
  RSA-CRT private exponent) makes the running remainder `"g"` `Secret`, so the
  data-dependent loop is rejected. The label is now source-declared, not supplied.
* `vartimeInvert_accepted_from_public_source` — a public operand (RSA verify)
  leaves everything `Public`, so the vartime path is licensed.
* `vartimeInvert_accepted_after_declassify` — a `declassify()` on the guard (RSA
  verify declassifying the public modulus) flips reject → accept: the source-level
  downgrade licenses the vartime kernel.

This is the compiler-side consumption path of the constant-time transfer. It
reuses the `cmdCT` machinery and the vartime accept/reject theorems verbatim; only the *provenance* of the label table changes.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.SourceSecrecyTransfer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VartimeBignumInverse

set_option autoImplicit false

/-! ## §1. The source-declared secrecy table (phase-2 extraction output, modelled) -/

/-- The per-binding secrecy a source secret-integer discipline declares, as
    carried out of extraction. `secret` lists the bindings whose *source* type is
    a secret integer; `declassified` lists the bindings produced by an explicit
    `declassify()` downgrade — the audit surface. Any binding in neither list is
    `Public` (the default). -/
structure SourceSecrecy where
  /-- Bindings whose source type is a secret integer. -/
  secret : List String
  /-- Bindings produced by an explicit `declassify()` — the trusted-downgrade
      audit surface. Overrides `secret`. -/
  declassified : List String

/-- The `LevelTable` a `SourceSecrecy` induces: `Public` unless the binding is a
    non-declassified secret. `declassify` wins over `secret` (a downgraded value
    is public). This is the table `cmdCT` consumes, derived rather than hand-authored. -/
def SourceSecrecy.toLevelTable (s : SourceSecrecy) : LevelTable :=
  fun v =>
    if s.declassified.contains v then .Public
    else if s.secret.contains v then .Secret
    else .Public

/-- The source-level `declassify(v)`: mark binding `v` as downgraded to `Public`.
    This is the *only* Secret → Public transition, and the site is recorded in
    `declassified` for the phase-4 audit. -/
def SourceSecrecy.declassify (s : SourceSecrecy) (v : String) : SourceSecrecy :=
  { s with declassified := v :: s.declassified }

/-! ## §2. Worked sources tied to the variable-time modular inverse -/

/-- Secret-operand source (ECDSA nonce / RSA-CRT private exponent): the running
    remainder `"g"` — the loop guard — derives from a secret operand. -/
def srcSecretOperand : SourceSecrecy := { secret := ["g"], declassified := [] }

/-- Public-operand source (RSA verify, public modular arithmetic): nothing is
    secret. -/
def srcPublicOperand : SourceSecrecy := { secret := [], declassified := [] }

/-! ## §3. The source labeling reproduces the hand-authored tables -/

/-- The secret-operand source induces exactly the hand-authored `secretInvertLT`. -/
theorem toLevelTable_secretOperand :
    srcSecretOperand.toLevelTable = secretInvertLT := by
  funext v
  simp only [SourceSecrecy.toLevelTable, srcSecretOperand, secretInvertLT,
    List.contains, List.elem]
  by_cases h : v = "g"
  · subst h; simp
  · simp [h, beq_eq_false_iff_ne.mpr h]

/-- The public-operand source induces exactly the hand-authored `publicInvertLT`
    (`allPublic`). -/
theorem toLevelTable_publicOperand :
    srcPublicOperand.toLevelTable = publicInvertLT := by
  funext v
  simp [SourceSecrecy.toLevelTable, srcPublicOperand, publicInvertLT,
    LevelTable.allPublic, List.contains, List.elem]

/-- Declassifying the guard (the `.declassify()` call in source: RSA verify
    declassifies the public modulus) makes every binding `Public`. -/
theorem toLevelTable_secretOperand_declassified :
    (srcSecretOperand.declassify "g").toLevelTable = publicInvertLT := by
  funext v
  simp only [SourceSecrecy.toLevelTable, SourceSecrecy.declassify, srcSecretOperand,
    publicInvertLT, LevelTable.allPublic, List.contains, List.elem]
  by_cases h : v = "g"
  · subst h; simp
  · simp [beq_eq_false_iff_ne.mpr h]

/-! ## §4. The `cmdCT` gate, now driven by source-declared secrecy -/

/-- **Reject from a secret source.** With the loop guard's secrecy *declared by
    the source* (a secret operand), `cmdCT` rejects the variable-time inverse —
    fail-closed. The label is inherited from the source, not supplied at the call
    site. -/
theorem vartimeInvert_rejected_from_secret_source :
    cmdCT vartimeInvertBody srcSecretOperand.toLevelTable invertLeafCT = false := by
  rw [toLevelTable_secretOperand]; exact vartimeInvertBody_secret_rejected

/-- **Accept from a public source.** With every operand *declared public by the
    source* (RSA verify), `cmdCT` licenses the variable-time inverse. -/
theorem vartimeInvert_accepted_from_public_source :
    cmdCT vartimeInvertBody srcPublicOperand.toLevelTable invertLeafCT = true := by
  rw [toLevelTable_publicOperand]; exact vartimeInvertBody_accepted_public

/-- **`declassify()` licenses the vartime path.** A secret-operand source whose
    guard is explicitly declassified (the source-level downgrade) is accepted by
    `cmdCT`: the `.declassify()` call flips the gate reject → accept. This is the
    source-declared dual of the GMP-vs-CT split. -/
theorem vartimeInvert_accepted_after_declassify :
    cmdCT vartimeInvertBody (srcSecretOperand.declassify "g").toLevelTable
      invertLeafCT = true := by
  rw [toLevelTable_secretOperand_declassified]; exact vartimeInvertBody_accepted_public

/-- The two faces side by side, both driven from source secrecy: the *same*
    inverse body is rejected under a secret-operand source and accepted once the
    guard is declassified. -/
theorem vartimeInvert_source_gate :
    cmdCT vartimeInvertBody srcSecretOperand.toLevelTable invertLeafCT = false ∧
      cmdCT vartimeInvertBody (srcSecretOperand.declassify "g").toLevelTable
        invertLeafCT = true :=
  ⟨vartimeInvert_rejected_from_secret_source, vartimeInvert_accepted_after_declassify⟩

end CatCrypt.Crypto.SecureCompilation.SourceSecrecyTransfer
