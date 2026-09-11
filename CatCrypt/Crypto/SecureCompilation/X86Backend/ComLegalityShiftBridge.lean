/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGatherFull
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ShiftMnemSymbolic

/-!
# D4 shift-family bridge: the immediate shifts lower under `lowerLinstrExt2`

The prior step (`ComLegalityToGatherFull.lean`) completed the supported-op →
gather bridge for the **closed-mnemonic** majority of the legal set —
`regArith` / `mulhi` / `regConst` — but left the two immediate-shift families
`shrImm 64 n` / `shlImm 64 n` out. It recorded, honestly, *why*: their SSA
export mnemonic is `withWidthTag 64 ("SHR:" ++ toString n)` — a string whose
content depends on the symbolic count `n`. Lean 4.29's `String` pattern API
(`startsWith` / `endsWith`) is `Slice` / UTF-8-iterator-backed and carries no
prefix-or-suffix-over-append characterisation lemma, so neither the matcher's
string discrimination nor `parseShiftMnem`'s `startsWith` gate reduces — by the
kernel **or** by elaborator def-eq — over `_ ++ toString n` for a *symbolic* `n`.
(Probed directly: `simp` / `exact?` / `decide` all fail on
`(("SHR:" ++ t) ++ ":64").hasSuffix toSlice ":64"` for a free `t`. There is no
`String.startsWith_append` / `String.endsWith_append` in the toolchain.)

This file closes the bridge for the immediate shifts. For a *closed* `n` the
mnemonic `"SHR:" ++ toString n ++ ":64"` is a closed string, so:

* the matcher's prior-arm disequalities (`mnem ≠ "LOAD"` / `"STORE"` /
  `"MULXHI:64"`) — surfaced as the side goals of the single-source equation
  lemma `lowerLinstrExt2.eq_5` — are `decide`-closeable; and
* `(parseShiftMnem mnem).isSome` reduces by `decide +kernel` (the kernel *does*
  reduce the `Slice`-backed `startsWith` on a closed string, even though
  elaborator def-eq does not).

The reusable core is `lowerLinstrExt2_isSome_shift_mnem`, parametric over the
mnemonic and its parse/disequality facts; the per-`n` lemmas
`lowerLinstrExt2_isSome_shrImm_concrete` / `…_shlImm_concrete` instantiate it,
and `opSupportedRedShift` extends the prior step's reduction-tractable supported
sublattice with the immediate shifts.

## The symbolic-`n` shift count (§3b) — residual closed

`§3` keeps the concrete-`n` lemmas (closed by `decide +kernel`). `§3b` closes the
**fully symbolic** `n` via `ShiftMnemSymbolic`: rather than reduce the
`Slice`/UTF-8-backed `String.startsWith "SHR:"` gate (which is stuck for a
symbolic `_ ++ toString n`), it discharges the two side facts —
`parseShiftMnem ("SHR:" ++ toString n ++ ":64") = some _` and the `≠ "LOAD"`
disequality — through the `List Char` / `String.Slice.copy` prefix view. The
key point: `isSome` needs only the `startsWith` prefix *detection* to fire, not
the decimal `toString n` / `toNat?` round-trip computed inside `some (...)`. So
`lowerLinstrExt2_isSome_shrImm` / `…_shlImm` hold for **every** `n`, not only
the concrete in-range family.

Composed with the prior step's `regArith` / `mulhi` / `regConst` bridges,
`§5`'s `lowerLinstrExt2_isSome_of_supportedRedShift` extends the gather bridge to
the **whole** reduction-tractable supported-op set — with the immediate shifts
at any count — so every legal op the front exports lowers under
`lowerLinstrExt2`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityShiftBridge

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn (SupportedOp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended

/-! ## 1. The reusable closed-mnemonic shift bridge

For a **closed** mnemonic `m` (so the `String` pattern ops reduce in the kernel)
that `parseShiftMnem` accepts and that is none of the matcher's prior single-arm
mnemonics, the single-source export `Lopn [reg dst] m [src]` lowers under
`lowerLinstrExt2`. The matcher reaches its single-source arm — the prior arms
(`LOAD` / `STORE` / `MULXHI:64`, the two-source ALU) are ruled out by the operand
shape (`[src]` is a one-element list) and the mnemonic disequalities — and the
shift sub-match fires on `hparse`. -/

/-- **The shift bridge core.** A single-source op with a closed immediate-shift
    mnemonic lowers. `hparse` says the mnemonic parses as a shift (so the shift
    sub-arm fires); `hLOAD` rules out the `"LOAD"` prior arm (the only prior arm
    whose source pattern `[.arr …]` a general `[src]` could match). The `isSome`
    is operand-independent — it is exactly `(parseShiftMnem m).isSome`. -/
theorem lowerLinstrExt2_isSome_shift_mnem (dst m : String) (src : LOperand)
    (hparse : (parseShiftMnem m).isSome = true)
    (hLOAD : m ≠ "LOAD") :
    (lowerLinstrExt2 (.Lopn [.reg dst] m [src])).isSome = true := by
  rw [lowerLinstrExt2.eq_5]
  · -- single-source arm: the shift sub-match fires on `hparse`.
    rcases h : parseShiftMnem m with _ | p
    · rw [h] at hparse; simp at hparse
    · simp [lowerShiftImmJ, h]
  · -- prior `"LOAD"` arm disequality (the only prior arm a `[src]` could hit).
    intro _ _ heq _; exact absurd heq hLOAD

/-! ## 2. The per-op bridge for the concrete shift families

For a concrete `n`, the export `opToLinstrR (.shrImm 64 n) dst [src]` reduces (by
`rfl`) to `Lopn [reg dst] ("SHR:" ++ toString n ++ ":64") [src]` — a closed
mnemonic — and the core §1 lemma applies. The two parse/disequality side facts
close by `decide +kernel` / `decide` on the closed string. -/

/-- `shrImm 64 n` (concrete `n`) exports `SHR:<n>:64 dst, [src]` and lowers. -/
theorem lowerLinstrExt2_isSome_shrImm_concrete (n : Nat) (dst : String)
    (src : LOperand)
    (hparse : (parseShiftMnem ("SHR:" ++ toString n ++ ":64")).isSome = true)
    (hLOAD : ("SHR:" ++ toString n ++ ":64") ≠ "LOAD") :
    (lowerLinstrExt2 (opToLinstrR (.shrImm 64 n) dst [src])).isSome = true := by
  show (lowerLinstrExt2 (.Lopn [.reg dst] ("SHR:" ++ toString n ++ ":64") [src])).isSome = true
  exact lowerLinstrExt2_isSome_shift_mnem dst _ src hparse hLOAD

/-- `shlImm 64 n` (concrete `n`) exports `SHL:<n>:64 dst, [src]` and lowers. -/
theorem lowerLinstrExt2_isSome_shlImm_concrete (n : Nat) (dst : String)
    (src : LOperand)
    (hparse : (parseShiftMnem ("SHL:" ++ toString n ++ ":64")).isSome = true)
    (hLOAD : ("SHL:" ++ toString n ++ ":64") ≠ "LOAD") :
    (lowerLinstrExt2 (opToLinstrR (.shlImm 64 n) dst [src])).isSome = true := by
  show (lowerLinstrExt2 (.Lopn [.reg dst] ("SHL:" ++ toString n ++ ":64") [src])).isSome = true
  exact lowerLinstrExt2_isSome_shift_mnem dst _ src hparse hLOAD

/-! ## 3. The concrete in-range family closes by `decide`

For a *closed* `n` both side facts are `decide`-closeable. We expose the two
canonical concrete instances and a worked example to certify the pattern; the
same two-line `decide +kernel` / `decide` discharge closes the bridge at any
concrete in-range `n` the exporter emits. -/

/-- The shift-amount `7` (Threefish / field-fold idiom) lowers — `shrImm`. -/
theorem lowerLinstrExt2_isSome_shrImm_7 (dst : String) (src : LOperand) :
    (lowerLinstrExt2 (opToLinstrR (.shrImm 64 7) dst [src])).isSome = true :=
  lowerLinstrExt2_isSome_shrImm_concrete 7 dst src (by decide +kernel) (by decide)

/-- The shift-amount `63` (carry-bit extraction) lowers — `shrImm`. -/
theorem lowerLinstrExt2_isSome_shrImm_63 (dst : String) (src : LOperand) :
    (lowerLinstrExt2 (opToLinstrR (.shrImm 64 63) dst [src])).isSome = true :=
  lowerLinstrExt2_isSome_shrImm_concrete 63 dst src (by decide +kernel) (by decide)

/-- The shift-amount `45` (Ascon linear layer) lowers — `shlImm`. -/
theorem lowerLinstrExt2_isSome_shlImm_45 (dst : String) (src : LOperand) :
    (lowerLinstrExt2 (opToLinstrR (.shlImm 64 45) dst [src])).isSome = true :=
  lowerLinstrExt2_isSome_shlImm_concrete 45 dst src (by decide +kernel) (by decide)

/-! ## 3b. The shift bridge at a **symbolic** count `n` (`ShiftMnemSymbolic`)

The concrete-`n` lemmas above discharge `hparse` / `hLOAD` by `decide +kernel`
on a *closed* mnemonic. `ShiftMnemSymbolic` closes them for **every** `n`,
routing the `parseShiftMnem` prefix detection through the `List Char` /
`String.Slice.copy` view instead of the (symbolically-stuck) `Slice`-backed
`String.startsWith`. This lifts the shift `isSome` from the concrete in-range
family to the **fully symbolic** shift count — the residual the prior step
recorded as the one open String-API gap is now closed. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ShiftMnemSymbolic

/-- **`shrImm 64 n` lowers for SYMBOLIC `n`.** No `decide` on a symbolic string:
    `parseShiftMnem_isSome_shr` / `shr_export_ne_LOAD` discharge the two side
    facts for every `n` via the `List Char` prefix characterisation. -/
theorem lowerLinstrExt2_isSome_shrImm (n : Nat) (dst : String) (src : LOperand) :
    (lowerLinstrExt2 (opToLinstrR (.shrImm 64 n) dst [src])).isSome = true :=
  lowerLinstrExt2_isSome_shrImm_concrete n dst src
    (parseShiftMnem_isSome_shr n) (shr_export_ne_LOAD n)

/-- **`shlImm 64 n` lowers for SYMBOLIC `n`.** -/
theorem lowerLinstrExt2_isSome_shlImm (n : Nat) (dst : String) (src : LOperand) :
    (lowerLinstrExt2 (opToLinstrR (.shlImm 64 n) dst [src])).isSome = true :=
  lowerLinstrExt2_isSome_shlImm_concrete n dst src
    (parseShiftMnem_isSome_shl n) (shl_export_ne_LOAD n)

/-! ## 4. Extending the supported sublattice to the shifts

`opSupportedRedShift` extends the prior step's reduction-tractable
`opSupportedRed` with the immediate shifts at any width-64 count. It
still refines the canonical `SupportedOp` set (`supportedOp_of_opSupportedRedShift`),
so a `Com` legal under it is legal in the canonical sense. -/

/-- The reduction-tractable supported ops **including the immediate shifts**:
    the prior `regArith` / `mulhi` / `regConst` families, plus width-64
    `shrImm` / `shlImm` at any count. -/
def opSupportedRedShift : JasminOp → Bool
  | .regArith bop 64 => isSupportedBinOp bop
  | .mulhi 64        => true
  | .regConst 64 _   => true
  | .shrImm 64 _     => true
  | .shlImm 64 _     => true
  | _                => false

/-- `opSupportedRedShift` refines the canonical boolean legality mirror. -/
theorem isSupportedOp_of_opSupportedRedShift (op : JasminOp)
    (h : opSupportedRedShift op = true) : isSupportedOp op = true := by
  unfold opSupportedRedShift at h
  split at h <;> simp_all [isSupportedOp]

/-- `opSupportedRedShift` refines the canonical `SupportedOp` legal set. -/
theorem supportedOp_of_opSupportedRedShift (op : JasminOp)
    (h : opSupportedRedShift op = true) : SupportedOp op := by
  rw [← isSupportedOp_iff]; exact isSupportedOp_of_opSupportedRedShift op h

/-! ## 5. The **full** per-instruction gather bridge (all five families)

`lowerLinstrExt2_isSome_of_supportedRedShift` is the §4 (`ComLegalityToGatherFull`)
dispatcher extended to the immediate shifts at **any** count `n`: for any op in
`opSupportedRedShift` — `regArith` / `mulhi` / `regConst` (delegated to the prior
`lowerLinstrExt2_isSome_of_supportedRed`) **plus** `shrImm 64 n` / `shlImm 64 n`
for symbolic `n` — the front's SSA export `opToLinstrR e.op dst (exprArgs … e)`
lowers under `lowerLinstrExt2`. This is the whole reduction-tractable supported-op
set bridged, with the symbolic-`n` shifts no longer a residual. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityToGatherFull in
/-- **The full supported-op (incl. symbolic-`n` shifts) export → gather bridge.**
    Every op accepted by `opSupportedRedShift` lowers on its actual SSA export
    shape: the three closed-mnemonic families via the prior dispatcher, and the
    immediate shifts at any width-64 count via the §3b symbolic-`n` lemmas. -/
theorem lowerLinstrExt2_isSome_of_supportedRedShift
    {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (curDepth nArgs : Nat) (argNames : Nat → String) (imm : ImmSlotMap)
    (e : Expr jasminDialect Γ τ) (dst : String)
    (hsup : opSupportedRedShift e.op = true) :
    (lowerLinstrExt2 (opToLinstrR e.op dst (exprArgs curDepth nArgs argNames imm e))).isSome
      = true := by
  obtain ⟨op, hret, args⟩ := e
  simp only at hsup ⊢
  match op, hret, args, hsup with
  | .regArith bop 64, hret, .cons a (.cons b .nil), hsup =>
      exact lowerLinstrExt2_isSome_of_supportedRed curDepth nArgs argNames imm
        ⟨.regArith bop 64, hret, .cons a (.cons b .nil)⟩ dst hsup
  | .mulhi 64, hret, .cons a (.cons b .nil), hsup =>
      exact lowerLinstrExt2_isSome_of_supportedRed curDepth nArgs argNames imm
        ⟨.mulhi 64, hret, .cons a (.cons b .nil)⟩ dst (by simp [opSupportedRed])
  | .regConst 64 n, hret, args, hsup =>
      exact lowerLinstrExt2_isSome_of_supportedRed curDepth nArgs argNames imm
        ⟨.regConst 64 n, hret, args⟩ dst (by simp [opSupportedRed])
  | .shrImm 64 n, hret, .cons a .nil, hsup =>
      rw [show exprArgs curDepth nArgs argNames imm
            (⟨.shrImm 64 n, hret, .cons a .nil⟩ : Expr jasminDialect Γ τ)
          = [resolveVar curDepth nArgs argNames imm a] from rfl]
      exact lowerLinstrExt2_isSome_shrImm n dst _
  | .shlImm 64 n, hret, .cons a .nil, hsup =>
      rw [show exprArgs curDepth nArgs argNames imm
            (⟨.shlImm 64 n, hret, .cons a .nil⟩ : Expr jasminDialect Γ τ)
          = [resolveVar curDepth nArgs argNames imm a] from rfl]
      exact lowerLinstrExt2_isSome_shlImm n dst _

end CatCrypt.Crypto.SecureCompilation.X86Backend.ComLegalityShiftBridge
