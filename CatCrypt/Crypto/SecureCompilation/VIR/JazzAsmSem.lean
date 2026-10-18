/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# Asm-op semantics for the 64-bit x86 operations of the Jasmin lowering

`jazzAsmSem` is an `AsmSem` of the `psem.v` mirror that gives the operations of
`jazzOps` their x86 semantics, read off the transcription `X86Backend.Jasmin` of
`jasmin/proofs/compiler/x86_instr_decl.v`, and agrees with
`ComJasminBridgeProgram.x86AsmSem` on every other operation.

Each operation of `jazzOps` returns the result tuple of its `x86_instr_decl.v`
entry in that entry's output order, with operands in the entry's input order:

* `ADD_64 a b`, `ADC_64 a b c`, `NEG_64 a`, `ANDN_64 a b` return the `b5w_ty`
  tuple `OF, CF, SF, PF, ZF, w` (`b5wVals`) of `x86_ADD`, `x86_ADC`, `x86_NEG`,
  `x86_ANDN`; `ANDN_64 a b` computes `~~~ a &&& b`.
* `CMP_64 a b` returns the `b5_ty` tuple `OF, CF, SF, PF, ZF` (`b5Vals`) of
  `x86_CMP`, without the difference word.
* `MULX_lo_hi_64 a b` returns the low and then the high word of
  `x86_MULX_lo_hi`.
* `ADCX_64 a b c` returns the carry flag and the word of `x86_ADCX`; it is the
  operation of `x86AsmSem`.

A flag the entry leaves undefined (`none`, the `PF` of `ANDN`) is the value
`Vundef cbool`, as Jasmin's `oto_val` maps `None` at type `sbool`.

The multiplication is the instruction `MULX_lo_hi` of `x86_instr_decl.v`, whose
semantic function returns `(lo, hi)`. jasminc's source-level `#MULX` is the
extended operation `Ox86MULX` of `x86_extra.v`, whose semantic function is
`wumul` with result order `hi, lo`; its lowering in `x86_extra.v` swaps the two
destinations and emits `MULX_lo_hi`. `x86AsmSem` names its low-first operation
`MULX_64`, which in jasminc's op table is the high-first `Ox86MULX`. The
operation of `jazzOps` is therefore `MULX_lo_hi_64`, printed
`(lo, hi) = #MULX_lo_hi(a, b)`, which carries both jasminc's name and the order
of `x86_MULX_lo_hi`; `x86AsmSem`'s `MULX_64` is left unchanged. The op table
used is the jasmin source tree at commit `7b6a3c65` (`x86_instr_decl.v` l.874–884,
`x86_extra.v` l.100–108 and l.315–323).

## Main results

* `jazzOps`, `jazzAsmSem`.
* `jazzAsmSem_add`, `jazzAsmSem_adc`, `jazzAsmSem_neg`, `jazzAsmSem_cmp`,
  `jazzAsmSem_andn`, `jazzAsmSem_mulx_lo_hi`, `jazzAsmSem_adcx`: one equation
  per operation of `jazzOps`.
* `jazzAsmSem_of_x86AsmSem`: `jazzAsmSem` returns every result `x86AsmSem`
  returns.
* `JazzAsmAgrees`, `jazzAsmSem_agrees`.
* `JasminModelRow`, `jazzAsmSem_eq_jasminModel`: each operation of `jazzOps` is
  the `X86Backend.Jasmin` function of its `x86_instr_decl.v` entry.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram

/-- The value of a Jasmin flag: `Vbool b` when defined, `Vundef cbool` otherwise
    (Jasmin's `oto_val` at type `sbool`). -/
def flagVal : JFlag → Value
  | some b => .Vbool b
  | none => .Vundef .cbool

/-- The `b5_ty` tuple `OF, CF, SF, PF, ZF` of a flag result. -/
def b5Vals {w : Nat} (r : B5W w) : Values :=
  [flagVal r.of, flagVal r.cf, flagVal r.sf, flagVal r.pf, flagVal r.zf]

/-- The `b5w_ty` tuple `OF, CF, SF, PF, ZF, w` of a 64-bit flag-and-word result. -/
def b5wVals (r : B5W 64) : Values :=
  b5Vals r ++ [.Vword .U64 r.word]

/-- The 64-bit operations `jazzAsmSem` adds to `x86AsmSem`, together with
    `ADCX_64`, which `x86AsmSem` already interprets. -/
def jazzOps : List String :=
  ["ADD_64", "ADC_64", "NEG_64", "CMP_64", "ANDN_64", "MULX_lo_hi_64", "ADCX_64"]

/-- The result of the operations `jazzAsmSem` adds, on well-typed operands;
    `none` on every other operation name or operand list. -/
def jazzSopn (op : String) : Values → Option Values
  | [.Vword .U64 a, .Vword .U64 b] =>
      if op = "ADD_64" then some (b5wVals (x86_ADD a b))
      else if op = "CMP_64" then some (b5Vals (x86_CMP a b))
      else if op = "ANDN_64" then some (b5wVals (x86_ANDN a b))
      else if op = "MULX_lo_hi_64" then
        some [.Vword .U64 (x86_MULX_lo_hi a b).1, .Vword .U64 (x86_MULX_lo_hi a b).2]
      else none
  | [.Vword .U64 a, .Vword .U64 b, .Vbool c] =>
      if op = "ADC_64" then some (b5wVals (x86_ADC a b c)) else none
  | [.Vword .U64 a] =>
      if op = "NEG_64" then some (b5wVals (x86_NEG a)) else none
  | _ => none

/-- Asm semantics extending `x86AsmSem` by the operations of `jazzOps`: an
    application `jazzSopn` interprets returns that result, and every other
    application is the one of `x86AsmSem`. -/
def jazzAsmSem : AsmSem where
  sopn_sem := fun o vs =>
    match o with
    | .Oasm op =>
        match jazzSopn op vs with
        | some r => .ok r
        | none => x86AsmSem.sopn_sem o vs
    | _ => x86AsmSem.sopn_sem o vs

/-- `ADD_64` under `jazzAsmSem`. -/
theorem jazzAsmSem_add (a b : BitVec 64) :
    jazzAsmSem.sopn_sem (.Oasm "ADD_64") [.Vword .U64 a, .Vword .U64 b]
      = .ok (b5wVals (x86_ADD a b)) := by
  rfl

/-- `ADC_64` under `jazzAsmSem`. -/
theorem jazzAsmSem_adc (a b : BitVec 64) (c : Bool) :
    jazzAsmSem.sopn_sem (.Oasm "ADC_64") [.Vword .U64 a, .Vword .U64 b, .Vbool c]
      = .ok (b5wVals (x86_ADC a b c)) := by
  rfl

/-- `NEG_64` under `jazzAsmSem`. -/
theorem jazzAsmSem_neg (a : BitVec 64) :
    jazzAsmSem.sopn_sem (.Oasm "NEG_64") [.Vword .U64 a]
      = .ok (b5wVals (x86_NEG a)) := by
  rfl

/-- `CMP_64` under `jazzAsmSem`. -/
theorem jazzAsmSem_cmp (a b : BitVec 64) :
    jazzAsmSem.sopn_sem (.Oasm "CMP_64") [.Vword .U64 a, .Vword .U64 b]
      = .ok (b5Vals (x86_CMP a b)) := by
  rfl

/-- `ANDN_64` under `jazzAsmSem`. -/
theorem jazzAsmSem_andn (a b : BitVec 64) :
    jazzAsmSem.sopn_sem (.Oasm "ANDN_64") [.Vword .U64 a, .Vword .U64 b]
      = .ok (b5wVals (x86_ANDN a b)) := by
  rfl

/-- `MULX_lo_hi_64` under `jazzAsmSem`: the low word, then the high word. -/
theorem jazzAsmSem_mulx_lo_hi (a b : BitVec 64) :
    jazzAsmSem.sopn_sem (.Oasm "MULX_lo_hi_64") [.Vword .U64 a, .Vword .U64 b]
      = .ok [.Vword .U64 (x86_MULX_lo_hi a b).1, .Vword .U64 (x86_MULX_lo_hi a b).2] := by
  rfl

/-- `ADCX_64` under `jazzAsmSem`: the carry flag, then the word. -/
theorem jazzAsmSem_adcx (a b : BitVec 64) (c : Bool) :
    jazzAsmSem.sopn_sem (.Oasm "ADCX_64") [.Vword .U64 a, .Vword .U64 b, .Vbool c]
      = .ok [flagVal (x86_ADCX a b c).1, .Vword .U64 (x86_ADCX a b c).2] := by
  rfl

/-- `jazzAsmSem` extends `x86AsmSem`: every result of `x86AsmSem` is a result of
    `jazzAsmSem`. -/
theorem jazzAsmSem_of_x86AsmSem (o : Sopn) (vs : Values) (r : Values)
    (h : x86AsmSem.sopn_sem o vs = .ok r) : jazzAsmSem.sopn_sem o vs = .ok r := by
  cases o <;> first
    | exact h
    | (simp only [jazzAsmSem]; split <;> simp_all [jazzSopn, x86AsmSem]; grind)

/-- An asm semantics agrees with `jazzAsmSem` on every operation of `jazzOps`. -/
def JazzAsmAgrees (aS : AsmSem) : Prop :=
  ∀ o ∈ jazzOps, ∀ vs, aS.sopn_sem (.Oasm o) vs = jazzAsmSem.sopn_sem (.Oasm o) vs

/-- `jazzAsmSem` agrees with itself on `jazzOps`. -/
theorem jazzAsmSem_agrees : JazzAsmAgrees jazzAsmSem :=
  fun _ _ _ => rfl

/-- The equation of an operation of `jazzOps` with the `X86Backend.Jasmin`
    function of its `x86_instr_decl.v` entry, operands in the entry's input order
    and results in its output order; `False` on every other name. -/
def JasminModelRow : String → Prop
  | "ADD_64" => ∀ a b : BitVec 64,
      jazzAsmSem.sopn_sem (.Oasm "ADD_64") [.Vword .U64 a, .Vword .U64 b]
        = .ok (b5wVals (x86_ADD a b))
  | "ADC_64" => ∀ (a b : BitVec 64) (c : Bool),
      jazzAsmSem.sopn_sem (.Oasm "ADC_64") [.Vword .U64 a, .Vword .U64 b, .Vbool c]
        = .ok (b5wVals (x86_ADC a b c))
  | "NEG_64" => ∀ a : BitVec 64,
      jazzAsmSem.sopn_sem (.Oasm "NEG_64") [.Vword .U64 a] = .ok (b5wVals (x86_NEG a))
  | "CMP_64" => ∀ a b : BitVec 64,
      jazzAsmSem.sopn_sem (.Oasm "CMP_64") [.Vword .U64 a, .Vword .U64 b]
        = .ok (b5Vals (x86_CMP a b))
  | "ANDN_64" => ∀ a b : BitVec 64,
      jazzAsmSem.sopn_sem (.Oasm "ANDN_64") [.Vword .U64 a, .Vword .U64 b]
        = .ok (b5wVals (x86_ANDN a b))
  | "MULX_lo_hi_64" => ∀ a b : BitVec 64,
      jazzAsmSem.sopn_sem (.Oasm "MULX_lo_hi_64") [.Vword .U64 a, .Vword .U64 b]
        = .ok [.Vword .U64 (x86_MULX_lo_hi a b).1, .Vword .U64 (x86_MULX_lo_hi a b).2]
  | "ADCX_64" => ∀ (a b : BitVec 64) (c : Bool),
      jazzAsmSem.sopn_sem (.Oasm "ADCX_64") [.Vword .U64 a, .Vword .U64 b, .Vbool c]
        = .ok [flagVal (x86_ADCX a b c).1, .Vword .U64 (x86_ADCX a b c).2]
  | _ => False

/-- Each operation of `jazzOps` is, under `jazzAsmSem`, the `X86Backend.Jasmin`
    function of its `x86_instr_decl.v` entry with that entry's operand and result
    order. -/
theorem jazzAsmSem_eq_jasminModel : ∀ o ∈ jazzOps, JasminModelRow o := by
  intro o ho
  simp only [jazzOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact jazzAsmSem_add
  · exact jazzAsmSem_adc
  · exact jazzAsmSem_neg
  · exact jazzAsmSem_cmp
  · exact jazzAsmSem_andn
  · exact jazzAsmSem_mulx_lo_hi
  · exact jazzAsmSem_adcx

end CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem
