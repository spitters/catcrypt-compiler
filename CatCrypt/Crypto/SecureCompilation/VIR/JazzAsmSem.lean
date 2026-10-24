/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# Asm-op semantics for the x86 operations of the Jasmin lowering

`jazzAsmSem` is an `AsmSem` of the `psem.v` mirror that gives the operations of
`jazzOps` their x86 semantics, read off the transcription `X86Backend.Jasmin` of
`jasmin/proofs/compiler/x86_instr_decl.v`, and agrees with
`ComJasminBridgeProgram.x86AsmSem` on every other operation.

An operation of `jazzOps` is named `opName base ws`, the base name followed by `_` and the
bit width of the word size `ws`, as jasminc names the width variants of an `x86_instr_decl.v`
entry. `ADD`, `ADC`, `NEG`, `CMP` and `ROR` are interpreted at the four word sizes of the x86
general-purpose registers, `U8` to `U64` (`gprB`); `ANDN` and `MULX_lo_hi`, which x86 has
only at `U32` and `U64` (`bmiB`), at those two; `ADCX` at `U64`. Each returns the result tuple
of its `x86_instr_decl.v` entry in that entry's output order, with operands in the entry's
input order:

* `ADD_n a b`, `ADC_n a b c`, `NEG_n a`, `ANDN_n a b` return the `b5w_ty`
  tuple `OF, CF, SF, PF, ZF, w` (`b5wVals`) of `x86_ADD`, `x86_ADC`, `x86_NEG`,
  `x86_ANDN`; `ANDN_n a b` computes `~~~ a &&& b`.
* `CMP_n a b` returns the `b5_ty` tuple `OF, CF, SF, PF, ZF` (`b5Vals`) of
  `x86_CMP`, without the difference word.
* `MULX_lo_hi_n a b` returns the low and then the high word of
  `x86_MULX_lo_hi`.
* `ROR_n a c`, with `c` a `u8` count, returns the `b2w_ty` tuple `OF, CF, w` (`b2wVals`)
  of `x86_ROR` at the count `c` zero-extended to the word size.
* `ADCX_64 a b c` returns the carry flag and the word of `x86_ADCX`; it is the
  operation of `x86AsmSem`.

A flag the entry leaves undefined (`none`, the `PF` of `ANDN`) is the value
`Vundef cbool`, as Jasmin's `oto_val` maps `None` at type `sbool`. `jazzArgTys` gives the
operand types of each operation, the input types of its entry.

The multiplication is the instruction `MULX_lo_hi` of `x86_instr_decl.v`, whose
semantic function returns `(lo, hi)`. jasminc's source-level `#MULX` is the
extended operation `Ox86MULX` of `x86_extra.v`, whose semantic function is
`wumul` with result order `hi, lo`; its lowering in `x86_extra.v` swaps the two
destinations and emits `MULX_lo_hi`. `x86AsmSem` names its low-first operation
`MULX_64`, which in jasminc's op table is the high-first `Ox86MULX`. The
operation of `jazzOps` is therefore `MULX_lo_hi_n`, printed
`(lo, hi) = #MULX_lo_hi(a, b)`, which carries both jasminc's name and the order
of `x86_MULX_lo_hi`; `x86AsmSem`'s `MULX_64` is left unchanged. The op table
used is the jasmin source tree at commit `7b6a3c65` (`x86_instr_decl.v` l.874–884,
`x86_extra.v` l.100–108 and l.315–323).

## Main results

* `opName`, `jazzRows`, `jazzOps`, `jazzArgTys`, `jazzAsmSem`.
* `jazzAsmSem_add`, `jazzAsmSem_adc`, `jazzAsmSem_neg`, `jazzAsmSem_cmp`,
  `jazzAsmSem_andn`, `jazzAsmSem_mulx_lo_hi`, `jazzAsmSem_adcx`, `jazzAsmSem_ror`: one equation
  per base name, generic in the word size.
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

/-- The decimal bit width of a word size. -/
def wsName : WSize → String
  | .U8 => "8" | .U16 => "16" | .U32 => "32" | .U64 => "64" | .U128 => "128"
  | .U256 => "256"

/-- The name of the asm operation `base` at the word size `ws`: `base`, `_` and the bit
width of `ws`. -/
def opName (base : String) (ws : WSize) : String := base ++ "_" ++ wsName ws

/-- The word sizes of the x86 general-purpose registers: `U8`, `U16`, `U32`, `U64`. -/
def gprB : WSize → Bool
  | .U8 | .U16 | .U32 | .U64 => true
  | _ => false

/-- The word sizes at which x86 has `ANDN` and `MULX`: `U32` and `U64`. -/
def bmiB : WSize → Bool
  | .U32 | .U64 => true
  | _ => false

/-- The value of a Jasmin flag: `Vbool b` when defined, `Vundef cbool` otherwise
    (Jasmin's `oto_val` at type `sbool`). -/
def flagVal : JFlag → Value
  | some b => .Vbool b
  | none => .Vundef .cbool

/-- The `b5_ty` tuple `OF, CF, SF, PF, ZF` of a flag result. -/
def b5Vals {w : Nat} (r : B5W w) : Values :=
  [flagVal r.of, flagVal r.cf, flagVal r.sf, flagVal r.pf, flagVal r.zf]

/-- The `b5w_ty` tuple `OF, CF, SF, PF, ZF, w` of a flag-and-word result at the word
size `ws`. -/
def b5wVals (ws : WSize) (r : B5W ws.bits) : Values :=
  b5Vals r ++ [.Vword ws r.word]

/-- The base names and word sizes of the operations `jazzAsmSem` interprets: `ADD`, `ADC`,
`NEG`, `CMP`, `ROR` at `U8` to `U64`, `ANDN` and `MULX_lo_hi` at `U32` and `U64`, and `ADCX` at
`U64`, which `x86AsmSem` already interprets. -/
def jazzRows : List (String × WSize) :=
  [WSize.U8, .U16, .U32, .U64].flatMap (fun ws => [("ADD", ws), ("ADC", ws), ("NEG", ws),
    ("CMP", ws), ("ROR", ws)])
  ++ [("ANDN", .U32), ("ANDN", .U64), ("MULX_lo_hi", .U32), ("MULX_lo_hi", .U64),
    ("ADCX", .U64)]

/-- The names of the operations of `jazzRows`. -/
def jazzOps : List String := jazzRows.map fun r => opName r.1 r.2

/-- The operand types of the operation `base` at the word size `ws`, the input types of its
`x86_instr_decl.v` entry: a word for `NEG`, a word and a `u8` count for `ROR`, two words
and the carry flag for `ADC` and `ADCX`, two words otherwise. -/
def rowArgTys (base : String) (ws : WSize) : List Atype :=
  if base = "NEG" then [.aword ws]
  else if base = "ROR" then [.aword ws, .aword .U8]
  else if base = "ADC" ∨ base = "ADCX" then [.aword ws, .aword ws, .abool]
  else [.aword ws, .aword ws]

/-- The operand types of an operation of `jazzOps`; `none` on every other name. -/
def jazzArgTys (o : String) : Option (List Atype) :=
  jazzRows.findSome? fun r => if o = opName r.1 r.2 then some (rowArgTys r.1 r.2) else none

/-- The two-word operations at the word size `ws`. -/
def binaryAsmResult (op : String) (ws : WSize) (a b : BitVec ws.bits) : Option Values :=
  if gprB ws = true ∧ op = opName "ADD" ws then some (b5wVals ws (x86_ADD a b))
  else if gprB ws = true ∧ op = opName "CMP" ws then some (b5Vals (x86_CMP a b))
  else if bmiB ws = true ∧ op = opName "ANDN" ws then some (b5wVals ws (x86_ANDN a b))
  else if bmiB ws = true ∧ op = opName "MULX_lo_hi" ws then
    some [.Vword ws (x86_MULX_lo_hi a b).1, .Vword ws (x86_MULX_lo_hi a b).2]
  else none

/-- The `b2w_ty` tuple `OF, CF, w` of a rotate result at the word size `ws`. -/
def b2wVals (ws : WSize) (r : B2W ws.bits) : Values :=
  [flagVal r.of, flagVal r.cf, .Vword ws r.word]

/-- The rotate `ROR` at the word size `ws` on a word and a `u8` count, the count
zero-extended to `ws` as `x86_ROR` takes it. -/
def rorAsmResult (op : String) (ws : WSize) (a : BitVec ws.bits) (c : BitVec WSize.U8.bits) :
    Option Values :=
  if gprB ws = true ∧ op = opName "ROR" ws then
    some (b2wVals ws (x86_ROR a (c.setWidth ws.bits)))
  else none

/-- The result of the operations `jazzAsmSem` adds, on well-typed operands: two words, two
words and a carry, or one word, all of one word size, or a word and a `u8` count; `none` on
every other operation name or operand list. -/
def jazzSopn (op : String) : Values → Option Values
  | [.Vword ws a, .Vword ws' b] =>
      (if h : ws' = ws then binaryAsmResult op ws a (h ▸ b) else none).or
        (if h : ws' = .U8 then rorAsmResult op ws a (h ▸ b) else none)
  | [.Vword ws a, .Vword ws' b, .Vbool c] =>
      if h : ws' = ws then
        if gprB ws = true ∧ op = opName "ADC" ws then some (b5wVals ws (x86_ADC a (h ▸ b) c))
        else none
      else none
  | [.Vword ws a] =>
      if gprB ws = true ∧ op = opName "NEG" ws then some (b5wVals ws (x86_NEG a)) else none
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

/-- Base names that differ give operation names that differ at one word size. -/
theorem opName_inj {b b' : String} {ws : WSize} (h : opName b ws = opName b' ws) : b = b' := by
  unfold opName at h
  simpa using h

/-- `ADD` under `jazzAsmSem`, at each word size of `gprB`. -/
theorem jazzAsmSem_add (ws : WSize) (hws : gprB ws = true) (a b : BitVec ws.bits) :
    jazzAsmSem.sopn_sem (.Oasm (opName "ADD" ws)) [.Vword ws a, .Vword ws b]
      = .ok (b5wVals ws (x86_ADD a b)) := by
  simp [jazzAsmSem, jazzSopn, binaryAsmResult, hws]

/-- `ADC` under `jazzAsmSem`, at each word size of `gprB`. -/
theorem jazzAsmSem_adc (ws : WSize) (hws : gprB ws = true) (a b : BitVec ws.bits) (c : Bool) :
    jazzAsmSem.sopn_sem (.Oasm (opName "ADC" ws)) [.Vword ws a, .Vword ws b, .Vbool c]
      = .ok (b5wVals ws (x86_ADC a b c)) := by
  simp [jazzAsmSem, jazzSopn, hws]

/-- `NEG` under `jazzAsmSem`, at each word size of `gprB`. -/
theorem jazzAsmSem_neg (ws : WSize) (hws : gprB ws = true) (a : BitVec ws.bits) :
    jazzAsmSem.sopn_sem (.Oasm (opName "NEG" ws)) [.Vword ws a]
      = .ok (b5wVals ws (x86_NEG a)) := by
  simp [jazzAsmSem, jazzSopn, hws]

/-- `CMP` under `jazzAsmSem`, at each word size of `gprB`. -/
theorem jazzAsmSem_cmp (ws : WSize) (hws : gprB ws = true) (a b : BitVec ws.bits) :
    jazzAsmSem.sopn_sem (.Oasm (opName "CMP" ws)) [.Vword ws a, .Vword ws b]
      = .ok (b5Vals (x86_CMP a b)) := by
  have h1 : opName "CMP" ws ≠ opName "ADD" ws := fun h => by simpa using opName_inj h
  simp [jazzAsmSem, jazzSopn, binaryAsmResult, hws, h1]

/-- `ANDN` under `jazzAsmSem`, at each word size of `bmiB`. -/
theorem jazzAsmSem_andn (ws : WSize) (hws : bmiB ws = true) (a b : BitVec ws.bits) :
    jazzAsmSem.sopn_sem (.Oasm (opName "ANDN" ws)) [.Vword ws a, .Vword ws b]
      = .ok (b5wVals ws (x86_ANDN a b)) := by
  have h1 : opName "ANDN" ws ≠ opName "ADD" ws := fun h => by simpa using opName_inj h
  have h2 : opName "ANDN" ws ≠ opName "CMP" ws := fun h => by simpa using opName_inj h
  simp [jazzAsmSem, jazzSopn, binaryAsmResult, hws, h1, h2]

/-- `MULX_lo_hi` under `jazzAsmSem`, at each word size of `bmiB`: the low word, then the
high word. -/
theorem jazzAsmSem_mulx_lo_hi (ws : WSize) (hws : bmiB ws = true) (a b : BitVec ws.bits) :
    jazzAsmSem.sopn_sem (.Oasm (opName "MULX_lo_hi" ws)) [.Vword ws a, .Vword ws b]
      = .ok [.Vword ws (x86_MULX_lo_hi a b).1, .Vword ws (x86_MULX_lo_hi a b).2] := by
  have h1 : opName "MULX_lo_hi" ws ≠ opName "ADD" ws := fun h => by simpa using opName_inj h
  have h2 : opName "MULX_lo_hi" ws ≠ opName "CMP" ws := fun h => by simpa using opName_inj h
  have h3 : opName "MULX_lo_hi" ws ≠ opName "ANDN" ws := fun h => by simpa using opName_inj h
  simp [jazzAsmSem, jazzSopn, binaryAsmResult, hws, h1, h2, h3]

/-- `ROR` under `jazzAsmSem`, at each word size of `gprB`: the `b2w_ty` tuple of `x86_ROR`
with the `u8` count zero-extended to `ws`. -/
theorem jazzAsmSem_ror (ws : WSize) (hws : gprB ws = true) (a : BitVec ws.bits)
    (c : BitVec WSize.U8.bits) :
    jazzAsmSem.sopn_sem (.Oasm (opName "ROR" ws)) [.Vword ws a, .Vword .U8 c]
      = .ok (b2wVals ws (x86_ROR a (c.setWidth ws.bits))) := by
  have h1 : opName "ROR" ws ≠ opName "ADD" ws := fun h => by simpa using opName_inj h
  have h2 : opName "ROR" ws ≠ opName "CMP" ws := fun h => by simpa using opName_inj h
  have h3 : opName "ROR" ws ≠ opName "ANDN" ws := fun h => by simpa using opName_inj h
  have h4 : opName "ROR" ws ≠ opName "MULX_lo_hi" ws := fun h => by simpa using opName_inj h
  have hn : (if h : WSize.U8 = ws then binaryAsmResult (opName "ROR" ws) ws a (h ▸ c)
      else none) = none := by
    split <;> simp [binaryAsmResult, h1, h2, h3, h4]
  simp only [jazzAsmSem, jazzSopn, hn, Option.none_or, dite_true, rorAsmResult, hws, true_and,
    ite_true]

/-- `ADCX_64` under `jazzAsmSem`: the carry flag, then the word. -/
theorem jazzAsmSem_adcx (a b : BitVec 64) (c : Bool) :
    jazzAsmSem.sopn_sem (.Oasm (opName "ADCX" .U64)) [.Vword .U64 a, .Vword .U64 b, .Vbool c]
      = .ok [flagVal (x86_ADCX a b c).1, .Vword .U64 (x86_ADCX a b c).2] := by
  rfl

/-- `jazzAsmSem` extends `x86AsmSem`: every result of `x86AsmSem` is a result of
    `jazzAsmSem`. -/
theorem jazzAsmSem_of_x86AsmSem (o : Sopn) (vs : Values) (r : Values)
    (h : x86AsmSem.sopn_sem o vs = .ok r) : jazzAsmSem.sopn_sem o vs = .ok r := by
  cases o <;> first
    | exact h
    | (simp only [jazzAsmSem]; split <;> simp_all [jazzSopn, binaryAsmResult, x86AsmSem, opName,
        wsName]; grind)

/-- An asm semantics agrees with `jazzAsmSem` on every operation of `jazzOps`. -/
def JazzAsmAgrees (aS : AsmSem) : Prop :=
  ∀ o ∈ jazzOps, ∀ vs, aS.sopn_sem (.Oasm o) vs = jazzAsmSem.sopn_sem (.Oasm o) vs

/-- `jazzAsmSem` agrees with itself on `jazzOps`. -/
theorem jazzAsmSem_agrees : JazzAsmAgrees jazzAsmSem :=
  fun _ _ _ => rfl

/-- The equation of the operation `base` at the word size `ws` with the `X86Backend.Jasmin`
    function of its `x86_instr_decl.v` entry, operands in the entry's input order and
    results in its output order; `False` on every other base name. -/
def JasminModelRow (base : String) (ws : WSize) : Prop :=
  match base with
  | "ADD" => ∀ a b : BitVec ws.bits,
      jazzAsmSem.sopn_sem (.Oasm (opName "ADD" ws)) [.Vword ws a, .Vword ws b]
        = .ok (b5wVals ws (x86_ADD a b))
  | "ADC" => ∀ (a b : BitVec ws.bits) (c : Bool),
      jazzAsmSem.sopn_sem (.Oasm (opName "ADC" ws)) [.Vword ws a, .Vword ws b, .Vbool c]
        = .ok (b5wVals ws (x86_ADC a b c))
  | "NEG" => ∀ a : BitVec ws.bits,
      jazzAsmSem.sopn_sem (.Oasm (opName "NEG" ws)) [.Vword ws a]
        = .ok (b5wVals ws (x86_NEG a))
  | "CMP" => ∀ a b : BitVec ws.bits,
      jazzAsmSem.sopn_sem (.Oasm (opName "CMP" ws)) [.Vword ws a, .Vword ws b]
        = .ok (b5Vals (x86_CMP a b))
  | "ANDN" => ∀ a b : BitVec ws.bits,
      jazzAsmSem.sopn_sem (.Oasm (opName "ANDN" ws)) [.Vword ws a, .Vword ws b]
        = .ok (b5wVals ws (x86_ANDN a b))
  | "MULX_lo_hi" => ∀ a b : BitVec ws.bits,
      jazzAsmSem.sopn_sem (.Oasm (opName "MULX_lo_hi" ws)) [.Vword ws a, .Vword ws b]
        = .ok [.Vword ws (x86_MULX_lo_hi a b).1, .Vword ws (x86_MULX_lo_hi a b).2]
  | "ADCX" => ∀ (a b : BitVec ws.bits) (c : Bool),
      jazzAsmSem.sopn_sem (.Oasm (opName "ADCX" ws)) [.Vword ws a, .Vword ws b, .Vbool c]
        = .ok [flagVal (x86_ADCX a b c).1, .Vword ws (x86_ADCX a b c).2]
  | "ROR" => ∀ (a : BitVec ws.bits) (c : BitVec WSize.U8.bits),
      jazzAsmSem.sopn_sem (.Oasm (opName "ROR" ws)) [.Vword ws a, .Vword .U8 c]
        = .ok (b2wVals ws (x86_ROR a (c.setWidth ws.bits)))
  | _ => False

/-- Each operation of `jazzOps` is, under `jazzAsmSem`, the `X86Backend.Jasmin`
    function of its `x86_instr_decl.v` entry with that entry's operand and result
    order. -/
theorem jazzAsmSem_eq_jasminModel : ∀ r ∈ jazzRows, JasminModelRow r.1 r.2 := by
  intro r hr
  simp only [jazzRows, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact jazzAsmSem_add _ rfl | exact jazzAsmSem_adc _ rfl | exact jazzAsmSem_neg _ rfl
    | exact jazzAsmSem_cmp _ rfl | exact jazzAsmSem_andn _ rfl
    | exact jazzAsmSem_mulx_lo_hi _ rfl | exact jazzAsmSem_adcx | exact jazzAsmSem_ror _ rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem
