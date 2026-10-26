/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.WidthTagAttr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Export

/-!
# Members of the `width_tag` simp set

`untagCaret` (`X86Backend.LprogAsmPrinter`) spells a mnemonic without its `^` width tag.
This module gives its value on each literal mnemonic that a reader of the address machine
compares against, proves that its result has no `^` and that it is idempotent, and tags
these facts together with `untagCaret_withWidthTag`, `stripWidthTag_withWidthTag` and
`withWidthTag_ne_of_tagSepFree` as members of `width_tag`. The last two carry a
`tagSepFree` side condition, which `simp (disch := decide +kernel) [width_tag]` discharges
on a literal.

## Main results

* `untagCaret_loadIdx`, …, `untagCaret_castW_16_64` — `untagCaret "LIT" = "LIT"`.
* `JasminLsemAddrCongr.caret_free_untagCaret`, `JasminLsemAddrCongr.untagCaret_idem`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The longest prefix without `^` has no `^`. -/
theorem caret_not_mem_takeWhile (l : List Char) : '^' ∉ l.takeWhile (· != '^') := by
  induction l with
  | nil => simp
  | cons c l ih =>
    by_cases hc : c = '^'
    · simp [List.takeWhile, hc]
    · grind only [List.takeWhile_cons, = List.mem_cons]

/-- The result of `untagCaret` has no `^`. -/
@[width_tag]
theorem caret_free_untagCaret (o : String) :
    '^' ∉ (X86Backend.LprogAsmPrinter.untagCaret o).toList := by
  unfold X86Backend.LprogAsmPrinter.untagCaret
  split
  · rename_i h
    have hs : '^' ∉ (stripWidthTag o).toList := by
      unfold stripWidthTag
      rw [ite_eq_left h]
      simpa using caret_not_mem_takeWhile o.toList
    split
    · simp [String.toList_append, hs]
    · exact hs
  · rename_i h
    simpa using h

/-- `untagCaret` is idempotent. -/
@[width_tag]
theorem untagCaret_idem (o : String) :
    X86Backend.LprogAsmPrinter.untagCaret (X86Backend.LprogAsmPrinter.untagCaret o)
      = X86Backend.LprogAsmPrinter.untagCaret o :=
  X86Backend.LprogAsmPrinter.untagCaret_of_caret_free (caret_free_untagCaret o)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr

namespace CatCrypt.Crypto.SecureCompilation.VIR.WidthTagSimp

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (untagCaret
  untagCaret_of_caret_free)

/-! ## `untagCaret` on the literal mnemonics -/

@[width_tag] theorem untagCaret_loadIdx : untagCaret "LOADIDX" = "LOADIDX" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_storeIdx : untagCaret "STOREIDX" = "STOREIDX" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_zeroArr : untagCaret "ZEROARR" = "ZEROARR" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_storeImm : untagCaret "STOREIMM" = "STOREIMM" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_load64 : untagCaret "LOAD:64" = "LOAD:64" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_store64 : untagCaret "STORE:64" = "STORE:64" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_lea64 : untagCaret "LEA:64" = "LEA:64" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_mov64 : untagCaret "MOV:64" = "MOV:64" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_movq : untagCaret "MOVQ" = "MOVQ" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_mov : untagCaret "MOV" = "MOV" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_cmp64 : untagCaret "CMP:64" = "CMP:64" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_mulx : untagCaret "MULX" = "MULX" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_64_16 : untagCaret "CASTW_64_16" = "CASTW_64_16" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_32_16 : untagCaret "CASTW_32_16" = "CASTW_32_16" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_16_16 : untagCaret "CASTW_16_16" = "CASTW_16_16" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_64_32 : untagCaret "CASTW_64_32" = "CASTW_64_32" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_32_32 : untagCaret "CASTW_32_32" = "CASTW_32_32" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_16_32 : untagCaret "CASTW_16_32" = "CASTW_16_32" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_64_64 : untagCaret "CASTW_64_64" = "CASTW_64_64" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_32_64 : untagCaret "CASTW_32_64" = "CASTW_32_64" :=
  untagCaret_of_caret_free (by decide)

@[width_tag] theorem untagCaret_castW_16_64 : untagCaret "CASTW_16_64" = "CASTW_16_64" :=
  untagCaret_of_caret_free (by decide)

/-! ## Tagged forms -/

attribute [width_tag] CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.untagCaret_withWidthTag
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.stripWidthTag_withWidthTag
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.withWidthTag_ne_of_tagSepFree

/-! ## `untagCaret` on every literal without `^` -/

/-- `untagCaret` fixes a string whose characters do not include `^`, stated with the decision
    of the membership so that the kernel checks it by evaluation. -/
theorem untagCaret_lit (s : String) (h : decide ('^' ∈ s.toList) = false) :
    untagCaret s = s :=
  untagCaret_of_caret_free (by simpa using h)

/-- The simplification procedure that rewrites `untagCaret s` to `s` at a string literal `s`
    without `^`, by `untagCaret_lit`; the membership is decided by the kernel. It is in the
    default simp set and in `width_tag`, so a reader evaluated at a literal mnemonic reduces
    without a per-literal lemma. -/
simproc [simp, width_tag] reduceUntagCaret (untagCaret _) := fun e => do
  let_expr untagCaret a ← e | return .continue
  let some s := Lean.Meta.getStringValue? a | return .continue
  if s.contains '^' then return .continue
  return .done { expr := a, proof? := some (Lean.mkApp2 (Lean.mkConst ``untagCaret_lit) a
    (Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.false))) }

end CatCrypt.Crypto.SecureCompilation.VIR.WidthTagSimp
