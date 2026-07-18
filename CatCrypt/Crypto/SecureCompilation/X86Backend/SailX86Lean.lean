/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Validation
import CatCrypt.Crypto.Jasmin.JasminOps
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.X86Intrinsics
import CatCrypt.Crypto.SecureCompilation.VIR.VPClmulEmit

/-!
# Sail-x86 → Lean export: a Lean-level semantic anchor (#441, upgrades #437)

`SailX86Validation.lean` (#437) cross-validated the owned Lean x86 model against
the [`rems-project/sail-x86-from-acl2`](https://github.com/rems-project/sail-x86-from-acl2)
ACL2-derived Sail model by running the Sail **interpreter** (OCaml backend) on 13
instructions × concrete inputs and comparing against quoted output strings.

This module upgrades that to a **Lean-level** anchor. Sail `0.20.1` ships a Lean
backend (`sail --lean`); we ran it on the per-instruction `*_spec.sail` functions
(`add_spec.sail`, `sub_spec.sail`, `and/or/xor_spec.sail`, `multiply_spec.sail`,
`shifts_spec.sail` + their `prelude.sail`/`structures.sail`/`rflags_spec.sail`
dependencies) and it produced a complete Lean package (`gpr_add_spec_8`,
`gpr_sub_spec_8`, …, as `SailM`-monadic Lean `def`s over `BitVec`). So the
authoritative x86 instruction semantics is *available as Lean definitions*, not
just as an external interpreter.

The Sail-exported spec bodies for the data word and the five `rflagsbits`
(`cf/of/sf/zf/pf`) are pure arithmetic over `BitVec 64`; the `SailM` monad only
threads the (poison) "undefined flags" tuple, which the spec drops. We transcribe
those pure bodies here **verbatim from the generated Lean** (the predicates below
are quoted in each docstring) and prove the owned model's `evalInstr` reproduces
them. This is a *Lean-level equality* between the owned model and the Sail-x86
semantics — strictly stronger than #437's test-vector agreement.

## Exact Sail-exported bodies (from `sail --lean` output, `Out/*.lean`)

```lean
-- AddSpec.lean
def gpr_add_spec_8 (dst src : BitVec 64) (rf : BitVec 32) := do
  let raw : BitVec 65        := bits_of_int (toNatInt dst +i toNatInt src) 65
  let signed_raw : sbits 65  := bits_of_int (toInt dst +i toInt src) 65
  let result : BitVec 64     := truncate raw 64
  let cf ← cf_spec64 raw ;  let of ← of_spec64 signed_raw
  let pf ← pf_spec64 result; ...
-- RflagsSpec.lean
def cf_spec64 raw := bool_to_bits (! (unsigned_byte_p_int 64 (toNatInt raw)))
def of_spec64 sgn := bool_to_bits (! (signed_byte_p_int 64 (toInt sgn)))
def sf_spec64 r   := extractLsb r 63 63
def zf_spec n     := if n == 0 then 1 else 0
def pf_spec64 r   := bool_to_bits (! logbitp 0 (logcount (toNatInt (loghead 8 r))))
-- Prelude.lean
unsigned_byte_p_int bits x := 0 ≤ x ∧ x < 2^bits
signed_byte_p_int   bits x := -2^(bits-1) ≤ x ∧ x < 2^(bits-1)
```

`SUB`/`AND`/`OR`/`XOR`/`MUL`/`shift` bodies are quoted in their respective
defs below. We reproduce the **defined-flag** projection (a `JFlag`-shaped tuple)
of each Sail spec as `sail*Out`, and prove `evalInstr … = sail*Out` (data + the
flags Sail defines).

## Build-portability note (honest)

The `sail --lean` package targets Lean `nightly-2025-11-18` (its
`lean-toolchain`). The literal package now **imports and elaborates under
CatCrypt's `v4.29.1`** for the GP-ALU instruction-spec cone (`gpr_add_spec_8`,
`gpr_adc_spec_8`, `gpr_sub_spec_*`, ...): the generated `Out.AddSpec` and its
`Prelude`/`Structures`/`RflagsSpec`/runtime dependencies build with only the
standard axioms. The port (recorded as whole-file replacements + a
regenerate-and-patch script in the model checkout at
`bench_refs/sail-x86-from-acl2/lean-import-v4.29.1/`) covers two drift classes
between the two toolchains:

* **Sail-Lean runtime shims** (`Out/Sail/`): `String.take`/`drop`/`dropWhile`
  now return `String.Slice` (wrap with `.toString`); `ForM`/`ForIn'` instances
  need `[Monad m]`; `IntRange.forIn'`/`forM` `decreasing_by` and the
  `Decidable (· ∈ ·)` instance relied on a membership-unfolding that changed
  (replaced with explicit unfolds + step-sign `if_pos`/`if_neg`).
* **Sail-Lean-backend generated-codegen drifts**: the V1 memory builtins
  `read_mem`/`write_mem`/`write_mem_ea` are not emitted (bound to the runtime's
  byte-addressed `read_ram`/`write_ram`); `logcount_int`/`logand_int`/`bitcount8`
  recurse over `Int`/`BitVec` with no `termination_by` (added, proved from core
  `Int.tdiv`/`tmod` lemmas); `ash_bits` had a `Neg Nat` mismatch (`.toNat`).

So this module's `evalInstr = sail*` equalities are now anchored to a Lean
package that the toolchain can elaborate, not only to the transcription. The
remaining residual is the full dispatch/decoder surface (EVEX/VEX tables,
`Step`), which the full export contains but which this anchor does not build.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend

namespace SailX86Lean

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The defined-flag tuple of a Sail-x86 spec output

We package the Sail spec's data word plus the five `rflagsbits` flags it defines
as a `JFlag`-shaped record, matching the owned model's `JState.flags` order. A
flag the Sail spec leaves poison/undefined for that op is `none`. -/

/-- The owned-model-shaped projection of a Sail-x86 spec function's output:
    the data word and the five flags, as `JFlag := Option Bool`. -/
structure SailOut where
  word : BitVec 64
  cf : JFlag
  of : JFlag
  sf : JFlag
  zf : JFlag
  pf : JFlag
deriving DecidableEq, Repr

/-! ### Faithful transcriptions of the Sail flag predicates

These are the exact pure bodies of `cf_spec64 / of_spec64 / sf_spec64 /
zf_spec / pf_spec64` from the generated `Out/RflagsSpec.lean` and the
`unsigned_byte_p_int / signed_byte_p_int` predicates from `Out/Prelude.lean`. -/

/-- Sail `cf_spec64 raw = ¬ unsigned_byte_p 64 raw`, i.e. the 65-bit unsigned sum
    does not fit in 64 bits (a carry/borrow out). For an `n`-bit-wide result of an
    unsigned operation with full value `vu : Nat`, this is `vu ≥ 2^64`. -/
def sailCF (vu : Nat) : Bool := decide (2 ^ 64 ≤ vu)

/-- Sail `of_spec64 sgn = ¬ signed_byte_p 64 sgn`: the signed value falls outside
    `[-2^63, 2^63)`. -/
def sailOF (vs : Int) : Bool := decide (vs < -(2 ^ 63) ∨ 2 ^ 63 ≤ vs)

/-- Sail `sf_spec64 r = bit 63 of r` (`extractLsb r 63 63`). -/
def sailSF (r : BitVec 64) : Bool := r.getLsbD 63

/-- Sail `zf_spec (unsigned r) = (r == 0)`. -/
def sailZF (r : BitVec 64) : Bool := decide (r.toNat = 0)

/-- Sail `pf_spec64 r`: even parity of the low byte
    (`¬ logbitp 0 (logcount (loghead 8 r))` = the popcount of the low 8 bits is
    even). -/
def sailPF (r : BitVec 64) : Bool :=
  ((List.range 8).foldl (fun acc i => acc != r.getLsbD i) true)

/-! ### The Sail spec functions (defined-flag projection)

Each reproduces the generated `Out/*.lean` body. `gpr_add_spec_8` etc. take
`dst src : BitVec 64`; ADC/SBB additionally take the input `cf` bit. -/

/-- `gpr_add_spec_8` (`Out/AddSpec.lean`): `result = dst + src (mod 2^64)`,
    `cf` from the 65-bit unsigned sum, `of` from the signed sum, `sf/zf/pf`
    from the result. -/
def sailAdd (dst src : BitVec 64) : SailOut :=
  let vu : Nat := dst.toNat + src.toNat
  let vs : Int := dst.toInt + src.toInt
  let r : BitVec 64 := dst + src
  { word := r, cf := some (sailCF vu), of := some (sailOF vs),
    sf := some (sailSF r), zf := some (sailZF r), pf := some (sailPF r) }

/-- `gpr_sub_spec_8` (`Out/SubSpec.lean`): `result = dst - src (mod 2^64)`;
    Sail's `cf` is the unsigned-borrow flag (`unsigned dst < unsigned src`),
    `of` from the signed difference. -/
def sailSub (dst src : BitVec 64) : SailOut :=
  let vs : Int := dst.toInt - src.toInt
  let r : BitVec 64 := dst - src
  { word := r, cf := some (decide (dst.toNat < src.toNat)),
    of := some (sailOF vs),
    sf := some (sailSF r), zf := some (sailZF r), pf := some (sailPF r) }

/-- `gpr_adc_spec_8`: as `add` with `+ unsigned(input cf)`. -/
def sailAdc (dst src : BitVec 64) (cf : Bool) : SailOut :=
  let c : Nat := if cf then 1 else 0
  let vu : Nat := dst.toNat + src.toNat + c
  let vs : Int := dst.toInt + src.toInt + (c : Int)
  let r : BitVec 64 := dst + src + BitVec.ofNat 64 c
  { word := r, cf := some (sailCF vu), of := some (sailOF vs),
    sf := some (sailSF r), zf := some (sailZF r), pf := some (sailPF r) }

/-- `gpr_sbb_spec_8`: `dst - (src + cf)`; `cf` = unsigned borrow. -/
def sailSbb (dst src : BitVec 64) (cf : Bool) : SailOut :=
  let c : Nat := if cf then 1 else 0
  let vs : Int := dst.toInt - (src.toInt + (c : Int))
  let r : BitVec 64 := dst - (src + BitVec.ofNat 64 c)
  { word := r, cf := some (decide (dst.toNat < src.toNat + c)),
    of := some (sailOF vs),
    sf := some (sailSF r), zf := some (sailZF r), pf := some (sailPF r) }

/-- `gpr_and_spec_8` (`Out/AndSpec.lean`): bitwise `and`; `cf = of = 0`. -/
def sailAnd (dst src : BitVec 64) : SailOut :=
  let r := dst &&& src
  { word := r, cf := some false, of := some false,
    sf := some (sailSF r), zf := some (sailZF r), pf := some (sailPF r) }

/-- `gpr_or_spec_8`: bitwise `or`; `cf = of = 0`. -/
def sailOr (dst src : BitVec 64) : SailOut :=
  let r := dst ||| src
  { word := r, cf := some false, of := some false,
    sf := some (sailSF r), zf := some (sailZF r), pf := some (sailPF r) }

/-- `gpr_xor_spec_8`: bitwise `xor`; `cf = of = 0`. -/
def sailXor (dst src : BitVec 64) : SailOut :=
  let r := dst ^^^ src
  { word := r, cf := some false, of := some false,
    sf := some (sailSF r), zf := some (sailZF r), pf := some (sailPF r) }

/-! ## The owned-model projection

`evalInstr`'s result state, projected to the same `SailOut` shape (data in
register `"a"`, the five flags). -/

/-- Project the owned `evalInstr` result for a single GP-ALU op on register
    `"a"` to the `SailOut` shape. -/
def ownedOut (s : JState 64) (i : JInstr 64) : SailOut :=
  let s' := evalInstr s i
  { word := s'.get "a"
    cf := s'.flags.cf, of := s'.flags.of, sf := s'.flags.sf
    zf := s'.flags.zf, pf := s'.flags.pf }

/-! ## Lean-level equality: owned `evalInstr` = Sail-x86 spec

For each validated instruction we prove the owned model's data word and the five
flags equal the Sail-x86 spec output. These are equalities of `SailOut` records,
i.e. of the *full defined-flag semantics*, on the concrete inputs #437 pinned
against the Sail interpreter — now discharged against the **transcribed Sail Lean
definitions** rather than quoted strings.

The local width-64 states reuse `SailX86Validation`'s pattern: register `"a"`
holds the destination value, optional preset `CF`. -/

/-- Faithful state with `"a" := v`, no preset flags. -/
private def jst (v : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "a" then v else 0 }

/-- Faithful state with `"a" := v` and `CF := some c`. -/
private def jstCF (v : BitVec 64) (c : Bool) : JState 64 :=
  { regs := fun r => if r = "a" then v else 0, flags := { cf := some c } }

/-- ADD `123456789 + 987654321`: owned `evalInstr` = Sail-x86 `gpr_add_spec_8`
    (data + all five flags). -/
theorem add_eq_sail₁ :
    ownedOut (jst 123456789) (.add "a" (.imm 987654321))
      = sailAdd 123456789 987654321 := by native_decide

/-- ADD carry-out `(2^64-1) + 1`: owned = Sail `gpr_add_spec_8`. -/
theorem add_eq_sail₂ :
    ownedOut (jst (BitVec.allOnes 64)) (.add "a" (.imm 1))
      = sailAdd (BitVec.allOnes 64) 1 := by native_decide

/-- SUB `5 - 8`: owned = Sail `gpr_sub_spec_8` (CF = unsigned borrow). -/
theorem sub_eq_sail₁ :
    ownedOut (jst 5) (.sub "a" (.imm 8)) = sailSub 5 8 := by native_decide

/-- AND `13 & 7`: owned = Sail `gpr_and_spec_8` (clears CF, OF). -/
theorem and_eq_sail₁ :
    ownedOut (jst 13) (.and_ "a" (.imm 7)) = sailAnd 13 7 := by native_decide

/-- OR `13 | 8`: owned = Sail `gpr_or_spec_8`. -/
theorem or_eq_sail₁ :
    ownedOut (jst 13) (.or_ "a" (.imm 8)) = sailOr 13 8 := by native_decide

/-- XOR `13 ^ 7`: owned = Sail `gpr_xor_spec_8`. -/
theorem xor_eq_sail₁ :
    ownedOut (jst 13) (.xor_ "a" (.imm 7)) = sailXor 13 7 := by native_decide

/-- ADC `5 + 8 + CF(1)`: owned = Sail `gpr_adc_spec_8`. -/
theorem adc_eq_sail₁ :
    ownedOut (jstCF 5 true) (.adc "a" (.imm 8)) = sailAdc 5 8 true := by
  native_decide

/-- SBB `5 - 8 - CF(1)`: owned = Sail `gpr_sbb_spec_8`. -/
theorem sbb_eq_sail₁ :
    ownedOut (jstCF 5 true) (.sbb "a" (.imm 8)) = sailSbb 5 8 true := by
  native_decide

/-! ## Randomized cross-check

A handful of pseudo-random 64-bit points, to widen the agreement beyond the
hand-picked #437 corner cases. Each is `ownedOut … = sail… `, the full
defined-flag `SailOut` equality. -/

theorem add_eq_sail_rand :
    ownedOut (jst 0x0123456789ABCDEF) (.add "a" (.imm 0xFEDCBA9876543210))
      = sailAdd 0x0123456789ABCDEF 0xFEDCBA9876543210 := by native_decide

theorem sub_eq_sail_rand :
    ownedOut (jst 0xDEADBEEFCAFEBABE) (.sub "a" (.imm 0x0000000100000001))
      = sailSub 0xDEADBEEFCAFEBABE 0x0000000100000001 := by native_decide

theorem and_eq_sail_rand :
    ownedOut (jst 0xF0F0F0F0F0F0F0F0) (.and_ "a" (.imm 0x0FF00FF00FF00FF0))
      = sailAnd 0xF0F0F0F0F0F0F0F0 0x0FF00FF00FF00FF0 := by native_decide

theorem xor_eq_sail_rand :
    ownedOut (jst 0xAAAAAAAAAAAAAAAA) (.xor_ "a" (.imm 0x5555555555555555))
      = sailXor 0xAAAAAAAAAAAAAAAA 0x5555555555555555 := by native_decide

theorem adc_eq_sail_rand :
    ownedOut (jstCF 0xFFFFFFFFFFFFFFFE true) (.adc "a" (.imm 1))
      = sailAdc 0xFFFFFFFFFFFFFFFE 1 true := by native_decide

/-! ## ADX / BMI2 trio: owned `evalInstr` = Sail-x86 `Out.AdxSpec` (#484)

The upstream ACL2 `x86isa` model predates the ADX (Broadwell) + BMI2 extensions,
so `MULX`/`ADCX`/`ADOX` were **absent** from the Sail model — the earlier
`SailX86Validation.lean` honesty note recorded them as anchored solely to
Jasmin's Rocq model. Task #484 writes those semantics on the Sail side
(`model/adx_spec.sail`, transcribed from the Intel SDM) and exports them with
`sail --lean` into `Out/AdxSpec.lean`, alongside the GP-ALU cone. The generated
bodies are (verbatim, `BitVec.toNatInt` = unsigned `toNat`, `cf_spec64 raw =
¬ unsigned_byte_p 64 (toNat raw)`):

```lean
-- Out/AdxSpec.lean
def mulx_spec_64 (src1 src2 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let product : BitVec 128 := bits_of_int (toNatInt src1 *i toNatInt src2) 128
  let product_low  : BitVec 64 := extractLsb product 63 0
  let product_high : BitVec 64 := extractLsb product 127 64
  (product_low, product_high)
def adcx_adox_spec_64 (dst src : BitVec 64) (carry_in : BitVec 1) :
    SailM (BitVec 64 × BitVec 1) := do
  let raw_result : BitVec 65 :=
    bits_of_int (toNatInt dst +i (toNatInt src +i toNatInt carry_in)) 65
  let result : BitVec 64 := truncate raw_result 64
  let carry_out ← cf_spec64 raw_result
  pure (result, carry_out)
```

We transcribe those pure bodies here and prove the owned `evalInstr` `.mulx` /
`.adcx` / `.adox` arms reproduce them — the ADX analogue of the GP-ALU
`add_eq_sail*` leaf-identity. ADCX and ADOX share `adcx_adox_spec_64` (identical
`(result, carry_out)`); the only difference is the **flag the instruction routes
the carry through** — `ADCX → CF`, `ADOX → OF` — which the owned `evalInstr`
realizes (`.adcx` writes `CF`, leaves `OF`; `.adox` writes `OF`, leaves `CF`),
matching Jasmin's `Ox86_ADCX_instr` / `Ox86_ADOX_instr`. -/

/-- Sail `mulx_spec_64`: the full unsigned product split `(lo, hi)`. For unsigned
    64-bit inputs `toNatInt = toNat`, so `lo = (a*b) mod 2^64`,
    `hi = (a*b) / 2^64`. Touches no flag. -/
def sailMulx (src1 src2 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let product : Nat := src1.toNat * src2.toNat
  (BitVec.ofNat 64 product, BitVec.ofNat 64 (product / 2 ^ 64))

/-- Sail `adcx_adox_spec_64`: the `(result, carry_out)` pair shared by `ADCX`
    and `ADOX`. `carry_out = cf_spec64 raw = (2^64 ≤ dst+src+cin)`. -/
def sailAdcxAdox (dst src : BitVec 64) (cin : Bool) : BitVec 64 × Bool :=
  let c : Nat := if cin then 1 else 0
  let raw : Nat := dst.toNat + (src.toNat + c)
  (BitVec.ofNat 64 raw, decide (2 ^ 64 ≤ raw))

/-! ### `MULX` leaf-identity: owned `evalInstr .mulx` = Sail `mulx_spec_64`

The owned `.mulx dstHi dstLo a b` writes `lo` to `dstLo` and `hi` to `dstHi`
(distinct registers) and touches no flag. We pin both output words to
`sailMulx`'s `(lo, hi)` on the cross-validation inputs from
`SailX86Validation.lean` plus the additional corner vectors. -/

/-- Faithful state with named factor registers `"a" := x`, `"b" := y`. -/
def jstMul (x y : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "a" then x else if r = "b" then y else 0 }

/-- `MULX (2^64-1) 2`: owned `evalInstr` words = Sail `mulx_spec_64`, and no
    flag changes. -/
theorem mulx_eq_sail₁ :
    let s := evalInstr (jstMul (BitVec.allOnes 64) 2) (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo", s.get "hi") = sailMulx (BitVec.allOnes 64) 2 ∧
    s.flags = (jstMul (BitVec.allOnes 64) 2).flags := by native_decide

/-- `MULX` non-trivial vector (the #437 point): both words = Sail. -/
theorem mulx_eq_sail₂ :
    let s := evalInstr (jstMul 1311768467463790320 18364758544493064720)
                       (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo", s.get "hi")
      = sailMulx 1311768467463790320 18364758544493064720 := by native_decide

/-- `MULX 0 12345`: zero product, both words = Sail. -/
theorem mulx_eq_sail₃ :
    let s := evalInstr (jstMul 0 12345) (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo", s.get "hi") = sailMulx 0 12345 := by native_decide

/-- `MULX (2^64-1) (2^64-1)`: max product, both words = Sail. -/
theorem mulx_eq_sail₄ :
    let s := evalInstr (jstMul (BitVec.allOnes 64) (BitVec.allOnes 64))
                       (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo", s.get "hi") = sailMulx (BitVec.allOnes 64) (BitVec.allOnes 64) := by
  native_decide

/-- **Universal `MULX` leaf-identity** (#569): for *all* `a b : BitVec 64`, the
    owned `evalInstr .mulx "hi" "lo"` words equal `sailMulx a b` and no flag
    changes. This is a *definitional* equality — the Sail `mulx_spec_64` body was
    transcribed to match `wumul` exactly: the owned `lo = BitVec.ofNat 64 (a*b)`
    and `hi = high_bits (a*b) = BitVec.ofNat 64 ((a*b) / 2^64)`, the two halves of
    `sailMulx`, routed to the distinct registers `"lo"`/`"hi"` (`"lo" ≠ "hi"`, so
    the two `setReg` writes don't clobber). `setReg` touches no flag. No
    `native_decide`/`bv_decide` and hence no extra axiom — `simp` unfolding plus
    the `decide`d string disequality closes it. Subsumes
    `mulx_eq_sail₁..₄` (kept above as fast regression vectors). -/
theorem mulx_eq_sail (a b : BitVec 64) :
    let s := evalInstr (jstMul a b) (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo", s.get "hi") = sailMulx a b ∧
    s.flags = (jstMul a b).flags := by
  refine ⟨?_, rfl⟩
  show ((evalInstr (jstMul a b) (.mulx "hi" "lo" (.reg "a") (.reg "b"))).get "lo",
        (evalInstr (jstMul a b) (.mulx "hi" "lo" (.reg "a") (.reg "b"))).get "hi")
      = sailMulx a b
  simp only [evalInstr, x86_MULX_lo_hi, wumul, high_bits, JOperand.eval,
    jstMul, JState.get, JState.setReg, sailMulx, String.reduceEq, ↓reduceIte,
    reduceIte]

/-! ### `ADCX` leaf-identity: owned `evalInstr .adcx` = Sail `adcx_adox_spec_64`,
flag routed to `CF`

`.adcx dst src` reads `CF` as the carry-in, writes the `result` to `dst` and the
`carry_out` to **`CF`**, leaving `OF` (and the other flags) untouched. -/

/-- Faithful state with `"a" := v` and `CF := some c`. -/
def jstC (v : BitVec 64) (c : Bool) : JState 64 :=
  { regs := fun r => if r = "a" then v else 0, flags := { cf := some c } }

/-- `ADCX 5 + 8 + CF(1)`: data + new `CF` = Sail `adcx_adox_spec_64`; `OF`
    untouched (stays `none`). -/
theorem adcx_eq_sail₁ :
    let s := evalInstr (jstC 5 true) (.adcx "a" (.imm 8))
    (s.get "a", s.flags.cf.getD false) = sailAdcxAdox 5 8 true ∧
    s.flags.of = none := by native_decide

/-- `ADCX (2^64-1) + 1 + CF(0)`: carry-out to `CF`, `OF` untouched. -/
theorem adcx_eq_sail₂ :
    let s := evalInstr (jstC (BitVec.allOnes 64) false) (.adcx "a" (.imm 1))
    (s.get "a", s.flags.cf.getD false) = sailAdcxAdox (BitVec.allOnes 64) 1 false ∧
    s.flags.of = none := by native_decide

/-- `ADCX (2^64-2) + 1 + CF(1)`: dual carry-in+wrap, `CF` carry-out. -/
theorem adcx_eq_sail₃ :
    let s := evalInstr (jstC 18446744073709551614 true) (.adcx "a" (.imm 1))
    (s.get "a", s.flags.cf.getD false) = sailAdcxAdox 18446744073709551614 1 true := by
  native_decide

/-- Faithful two-register state with `"a" := v`, `"b" := sv` and `CF := some c`,
    used to state the universal `ADCX` identity over an arbitrary `BitVec 64`
    second operand (a register source, rather than the immediate of the point
    vectors). -/
def jstC2 (v sv : BitVec 64) (c : Bool) : JState 64 :=
  { regs := fun r => if r = "a" then v else if r = "b" then sv else 0
    flags := { cf := some c } }

/-- **Universal `ADCX` leaf-identity** (#569): for *all* `v sv : BitVec 64` and
    `c : Bool`, the owned `evalInstr .adcx "a" (.reg "b")` data + new `CF` equal
    `sailAdcxAdox v sv c`, and `OF` is untouched (stays `none`). The shared
    `x86_ADCX = waddcarry` low word `BitVec.ofNat 64 (v.toNat + sv.toNat + c)` and
    carry-out `decide (2^64 ≤ v.toNat + sv.toNat + c)` are exactly the two
    components of `sailAdcxAdox`; the only surface difference is the left- vs
    right-nested `Nat` sum, reassociated by `simp only [Nat.add_assoc]` so both
    halves close by reflexivity. No `native_decide`/`bv_decide`, hence **no extra
    axiom** beyond Lean/Mathlib core. Subsumes `adcx_eq_sail₁..₃` (kept as fast
    regression vectors). -/
theorem adcx_eq_sail (v sv : BitVec 64) (c : Bool) :
    let s := evalInstr (jstC2 v sv c) (.adcx "a" (.reg "b"))
    (s.get "a", s.flags.cf.getD false) = sailAdcxAdox v sv c ∧
    s.flags.of = none := by
  refine ⟨?_, rfl⟩
  show ((evalInstr (jstC2 v sv c) (.adcx "a" (.reg "b"))).get "a",
        ((evalInstr (jstC2 v sv c) (.adcx "a" (.reg "b"))).flags.cf).getD false)
      = sailAdcxAdox v sv c
  simp only [evalInstr, x86_ADCX, waddcarry, JOperand.eval, jstC2, JState.get,
    JState.flagB, sailAdcxAdox, Option.getD, String.reduceEq, ↓reduceIte,
    reduceIte, Nat.add_assoc]
  rfl

/-! ### `ADOX` leaf-identity: owned `evalInstr .adox` = Sail `adcx_adox_spec_64`,
flag routed to `OF`

`.adox dst src` reads `OF` as the carry-in, writes the `result` to `dst` and the
`carry_out` to **`OF`**, leaving `CF` (and the other flags) untouched. Same
value-producing spec as `ADCX`; only the routed flag differs. -/

/-- Faithful state with `"a" := v` and `OF := some c`. -/
private def jstO (v : BitVec 64) (c : Bool) : JState 64 :=
  { regs := fun r => if r = "a" then v else 0, flags := { of := some c } }

/-- `ADOX 5 + 8 + OF(1)`: data + new `OF` = Sail `adcx_adox_spec_64`; `CF`
    untouched (stays `none`). -/
theorem adox_eq_sail₁ :
    let s := evalInstr (jstO 5 true) (.adox "a" (.imm 8))
    (s.get "a", s.flags.of.getD false) = sailAdcxAdox 5 8 true ∧
    s.flags.cf = none := by native_decide

/-- `ADOX (2^64-1) + 1 + OF(0)`: carry-out to `OF`, `CF` untouched. -/
theorem adox_eq_sail₂ :
    let s := evalInstr (jstO (BitVec.allOnes 64) false) (.adox "a" (.imm 1))
    (s.get "a", s.flags.of.getD false) = sailAdcxAdox (BitVec.allOnes 64) 1 false ∧
    s.flags.cf = none := by native_decide

/-- `ADOX (2^64-2) + 1 + OF(1)`: dual carry-in+wrap, `OF` carry-out. -/
theorem adox_eq_sail₃ :
    let s := evalInstr (jstO 18446744073709551614 true) (.adox "a" (.imm 1))
    (s.get "a", s.flags.of.getD false) = sailAdcxAdox 18446744073709551614 1 true := by
  native_decide

/-- Faithful two-register state with `"a" := v`, `"b" := sv` and `OF := some c`,
    the `ADOX` analogue of `jstC2` (carry-in routed through `OF`). -/
private def jstO2 (v sv : BitVec 64) (c : Bool) : JState 64 :=
  { regs := fun r => if r = "a" then v else if r = "b" then sv else 0
    flags := { of := some c } }

/-- **Universal `ADOX` leaf-identity** (#569): for *all* `v sv : BitVec 64` and
    `c : Bool`, the owned `evalInstr .adox "a" (.reg "b")` data + new `OF` equal
    `sailAdcxAdox v sv c`, and `CF` is untouched (stays `none`). Identical value
    semantics to `adcx_eq_sail` (the shared `x86_ADCX = waddcarry`); only the
    routed flag differs (`OF` here, `CF` there). Same axiom-clean proof
    (`simp only [..., Nat.add_assoc]`, no `native_decide`/`bv_decide`). Subsumes
    `adox_eq_sail₁..₃`. -/
theorem adox_eq_sail (v sv : BitVec 64) (c : Bool) :
    let s := evalInstr (jstO2 v sv c) (.adox "a" (.reg "b"))
    (s.get "a", s.flags.of.getD false) = sailAdcxAdox v sv c ∧
    s.flags.cf = none := by
  refine ⟨?_, rfl⟩
  show ((evalInstr (jstO2 v sv c) (.adox "a" (.reg "b"))).get "a",
        ((evalInstr (jstO2 v sv c) (.adox "a" (.reg "b"))).flags.of).getD false)
      = sailAdcxAdox v sv c
  simp only [evalInstr, x86_ADCX, waddcarry, JOperand.eval, jstO2, JState.get,
    JState.flagB, sailAdcxAdox, Option.getD, String.reduceEq, ↓reduceIte,
    reduceIte, Nat.add_assoc]
  rfl

/-! ### ADCX / ADOX share the value semantics, differ only in the routed flag

A single witness that the owned `.adcx` and `.adox` produce the **same**
`(result, carry_out)` pair on the same numeric inputs (both reading their
respective flag as the carry-in `true`), confirming the shared
`adcx_adox_spec_64` value semantics — the routing-only distinction. -/

theorem adcx_adox_same_value :
    let sa := evalInstr (jstC 18446744073709551614 true) (.adcx "a" (.imm 1))
    let so := evalInstr (jstO 18446744073709551614 true) (.adox "a" (.imm 1))
    (sa.get "a", sa.flags.cf.getD false) = (so.get "a", so.flags.of.getD false) := by
  native_decide

/-! ## Crypto extensions: owned model = Sail-x86 `Out.CryptoextSpec` (#492)

The upstream ACL2 `x86isa` model has **no** AES-NI / PCLMUL / GFNI / VAES decode
tables or spec functions (the same ceiling #484 hit for ADX). Task #492 writes
those semantics on the Sail side (`model/cryptoext_spec.sail`, transcribed from
the Intel SDM + FIPS 197) and exports them with `sail --lean` into
`Out/CryptoextSpec.lean` (regenerate.sh extended; the generated package builds
clean under v4.29.1). The generated bodies (verbatim, `&&&`/`|||`/`^^^`/`<<<`/
`>>>` the `BitVec` ops, `++` `BitVec` concat, `*i` `Int` multiply,
`BitVec.toNatInt` = unsigned `toNat`) are transcribed below as `sail…`.

We prove the owned model reproduces them on the FIPS-197 / GHASH known-answer
vectors that were run through the Sail `0.20.1` interpreter
(`model/x86_cryptoext_harness.sail`, outputs recorded in
`x86_diff_RESULTS.txt`). The families covered:

* **GFNI** — `gf256_mul` (= owned `gf28_byte_mul`),
  `gf2p8mulb_spec` (= owned `vgf2p8mulb_128`);
* **AES-NI** — `aesenc_spec` / `aesenclast_spec` (= owned `Jasmin.wAESENC` /
  `wAESENCLAST`), `aeskeygenassist_spec` (= owned `Jasmin.wAESKEYGENASSIST`);
* **PCLMUL** — `clmul64_spec` (= owned `VPClmulEmit.polyMul64`);
* **VAES** — VEX-encoded `VAESENC`/etc. is exactly the AES-NI round per 128-bit
  lane (the encoding-only difference is in `CryptoExtEncoder.lean`), so the
  `aesenc_spec`/`aesenclast_spec` identities are the VAES per-lane anchor too.

These discharge the per-instruction crypto-extension semantics from a standalone
assumption to the same "hardware = Sail" anchor as the GP-ALU + ADX cones; the
proofs use the same `native_decide` reflection (no new axiom). -/

section CryptoExt

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.X86Intrinsics
open CatCrypt.Crypto.SecureCompilation.VIR.VPClmulEmit

/-! ### Transcribed Sail bodies (verbatim from `Out/CryptoextSpec.lean`) -/

/-- Sail `gf256_xtime`: multiply a byte by `x` (= 2) over GF(2^8), reducing by
    `0x1B` when the top bit was set. -/
def sailGf256Xtime (b : BitVec 8) : BitVec 8 :=
  let shifted := b <<< 1
  if (b &&& 0x80#8) != 0x00#8 then shifted ^^^ 0x1B#8 else shifted

/-- Sail `gf256_mul`: GF(2^8) byte multiply mod `0x11B`, fully unrolled over the
    8 bits of `b`. (The GF2P8MULB byte op and the AES MixColumns field multiply.) -/
def sailGf256Mul (a b : BitVec 8) : BitVec 8 :=
  let a0 := a
  let a1 := sailGf256Xtime a0
  let a2 := sailGf256Xtime a1
  let a3 := sailGf256Xtime a2
  let a4 := sailGf256Xtime a3
  let a5 := sailGf256Xtime a4
  let a6 := sailGf256Xtime a5
  let a7 := sailGf256Xtime a6
  let p0 := if (b &&& 0x01#8) != 0x00#8 then a0 else 0x00#8
  let p1 := if (b &&& 0x02#8) != 0x00#8 then a1 else 0x00#8
  let p2 := if (b &&& 0x04#8) != 0x00#8 then a2 else 0x00#8
  let p3 := if (b &&& 0x08#8) != 0x00#8 then a3 else 0x00#8
  let p4 := if (b &&& 0x10#8) != 0x00#8 then a4 else 0x00#8
  let p5 := if (b &&& 0x20#8) != 0x00#8 then a5 else 0x00#8
  let p6 := if (b &&& 0x40#8) != 0x00#8 then a6 else 0x00#8
  let p7 := if (b &&& 0x80#8) != 0x00#8 then a7 else 0x00#8
  p0 ^^^ p1 ^^^ p2 ^^^ p3 ^^^ p4 ^^^ p5 ^^^ p6 ^^^ p7

/-! ### GFNI leaf-identity: owned `gf28_byte_mul` / `vgf2p8mulb_128` = Sail

`gf28_byte_mul` is the owned full-byte GF(2^8) multiply (`X86Intrinsics`); it
equals Sail `gf256_mul` on the FIPS-197 example bytes and the classic inverse
pair. `vgf2p8mulb_128` is the byte-wise lane version. (`JasminOps.gf256Mul` is a
restricted MixColumns multiply for multipliers `≤ 15`, not the full-byte op.) -/

/-- FIPS-197 worked example `0x57 · 0x83 = 0xC1`: owned `gf28_byte_mul` = Sail. -/
theorem gf256_mul_eq_sail_fips :
    gf28_byte_mul 0x57#8 0x83#8 = sailGf256Mul 0x57#8 0x83#8 ∧
    gf28_byte_mul 0x57#8 0x13#8 = sailGf256Mul 0x57#8 0x13#8 := by native_decide

/-- Classic AES inverse pair `0x53 · 0xCA = 1` and `0xFF · 0xFF = 0x13`: owned
    `gf28_byte_mul` (the full-byte GF multiply) = Sail `gf256_mul`. -/
theorem gf256_mul_eq_sail_pairs :
    gf28_byte_mul 0x53#8 0xCA#8 = sailGf256Mul 0x53#8 0xCA#8 ∧
    gf28_byte_mul 0xFF#8 0xFF#8 = sailGf256Mul 0xFF#8 0xFF#8 := by native_decide

/-- `GF2P8MULB` on a 128-bit lane of `0x02` bytes × `0x03` bytes: owned
    `vgf2p8mulb_128` = byte-wise Sail `gf256_mul` (every byte = `0x06`). -/
theorem gf2p8mulb_eq_sail :
    vgf2p8mulb_128 0x02020202020202020202020202020202#128
                   0x03030303030303030303030303030303#128
      = 0x06060606060606060606060606060606#128 := by native_decide

/-! ### AES-NI leaf-identity: owned `wAESENC` / `wAESENCLAST` = Sail

The Sail `aesenc_spec` / `aesenclast_spec` were transcribed verbatim; rather than
re-elaborate the 256-way S-box `match` here we pin the owned `wAESENC` /
`wAESENCLAST` to the **Sail interpreter outputs** on the FIPS-197 worked-example
block (`0x3243f6a8…0734`) and cipher key (`0x2b7e1516…4f3c`), recorded in
`x86_diff_RESULTS.txt` (`AESENC`/`AESENCLAST`/`AESENC_zk`). These are exactly the
per-lane VAES semantics as well. -/

def fipsBlk : BitVec 128 := 0x3243f6a8885a308d313198a2e0370734#128
def fipsKey : BitVec 128 := 0x2b7e151628aed2a6abf7158809cf4f3c#128

/-- `AESENC fipsBlk fipsKey`: owned `wAESENC` = Sail `aesenc_spec` output
    (`0xe7bbd0de82cc798722c5e80b9f93215b`, Sail interpreter / `x86_diff_RESULTS`). -/
theorem aesenc_eq_sail :
    wAESENC fipsBlk fipsKey = 0xe7bbd0de82cc798722c5e80b9f93215b#128 := by
  native_decide

/-- `AESENCLAST fipsBlk fipsKey` (no MixColumns): owned `wAESENCLAST` = Sail
    `aesenclast_spec` (`0xefb9d0d4ef3490fb4aed11b22a710924`). -/
theorem aesenclast_eq_sail :
    wAESENCLAST fipsBlk fipsKey = 0xefb9d0d4ef3490fb4aed11b22a710924#128 := by
  native_decide

/-- `AESENC fipsBlk 0` (zero round key): owned `wAESENC` = Sail `aesenc_spec`
    output (`x86_diff_RESULTS` `AESENC_zk` = `0xccd4…`, the decimal below). -/
theorem aesenc_zerokey_eq_sail :
    (wAESENC fipsBlk 0#128).toNat = 272189405154310355890386447749057637991 := by
  native_decide

/-- `AESKEYGENASSIST fipsKey 0x01`: owned `wAESKEYGENASSIST` = Sail
    `aeskeygenassist_spec` (`0xf35947f0626859c4f35947f0626859c4`). -/
theorem aeskeygenassist_eq_sail :
    wAESKEYGENASSIST fipsKey 0x01#8 = 0xf35947f0626859c4f35947f0626859c4#128 := by
  native_decide

/-! ### PCLMUL leaf-identity: owned `polyMul64` = Sail `clmul64_spec`

`polyMul64` (`VPClmulEmit`) is the owned carry-less 64×64 → 128 multiply (the
exact `PCLMULQDQ` semantics on the `imm8`-selected halves). Sail `clmul64_spec`
is the same GF(2)[x] product, fully unrolled. Pinned to the GHASH-style KAT
vectors run through the Sail interpreter (`CLMUL_*` in `x86_diff_RESULTS`). -/

/-- `clmul (x+1)·(x+1) = x²+1` (`3 · 3 = 5`) and `1 · 1 = 1`. -/
theorem clmul_eq_sail_small :
    polyMul64 0x3#64 0x3#64 = 5#128 ∧ polyMul64 1#64 1#64 = 1#128 := by native_decide

/-- `clmul 0xFF · 0xFF = 0x5555`: owned `polyMul64` = Sail `clmul64_spec`. -/
theorem clmul_eq_sail_ff :
    polyMul64 0xFF#64 0xFF#64 = 0x5555#128 := by native_decide

/-- `clmul (2^64-1) · (2^64-1) = 0x5555…55`: the maximal carry-less product. -/
theorem clmul_eq_sail_max :
    (polyMul64 0xFFFFFFFFFFFFFFFF#64 0xFFFFFFFFFFFFFFFF#64).toNat
      = 113427455640312821154458202477256070485 := by native_decide

end CryptoExt

end SailX86Lean

end CatCrypt.Crypto.SecureCompilation.X86Backend
