/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Model

/-!
# A faithful Lean transcription of Jasmin's Rocq x86 semantics (#281)

`Model.lean` is a hand-authored x86 machine (it tracks only `CF`/`OF` and leaves
`SF`/`PF`/`ZF` inert) that is then *differentially* checked against Jasmin's
Rocq model. This module strengthens the footing: it is a direct, line-for-line
**transcription** of the Rocq instruction semantics our backend's trust story
depends on, so that the Lean model *is* the Jasmin model on the emitted subset,
rather than a separate model checked to agree with it.

## What "the Jasmin model" means here, and why it is the anchor

The verified pipeline hands jasmin's `Linear.lprog` to **jasminc**, whose
constant-time-preservation theorem (`jasminc_preserves_ct`, arXiv:2511.11292)
is stated over the x86 semantics in the Rocq files

* `jasmin/proofs/compiler/x86_instr_decl.v` — the per-instruction semantic
  functions `x86_MOV`/`x86_ADD`/`x86_ADC`/`x86_SUB`/`x86_SBB`/`x86_IMULt`/
  `x86_MULX_lo_hi`/`x86_ADCX`/`x86_AND`/`x86_OR`/`x86_XOR`/`x86_SHL`/`x86_SHR`/
  `x86_SAR`/`x86_CMOVcc`, the flag combinators `rflags_of_aluop`/
  `rflags_of_bwop`/`rflags_of_mul`/`rflags_None_w`/`rflags_OF`, and the shift
  mask `x86_shift_mask`;
* `jasmin/proofs/lang/word.v` — the word operations `wrepr`/`wunsigned`/
  `wsigned`/`high_bits`/`wumul`/`waddcarry`/`wshl`/`wshr`/`wsar`;
* `jasmin/proofs/arch/arch_sem.v` — `eval_instr_op`/`exec_instr_op`/`eval_op`
  (evaluate the instruction's `id_semi` on the input operands, then write the
  result tuple back via `mem_write_vals` over the `id_out` operand list) and the
  `asmmem` register/flag state (`asm_reg : regmap`, `asm_flag : rflagmap`, with
  `rflagv := Def of bool | Undef`).

Replacing jasminc like-for-like means our model must be *that* model. This file
copies those definitions; the differential `example`s in
`TranslationValidation.lean` (driven through `rocq-mcp` against the compiled
`x86_instr_decl.vo`) confirm the transcription is faithful on concrete inputs.

## Trust story (precise)

This module makes **no** "authoritative / axiom-free" claim. Its semantics is
trusted because:

1. **It is a transcription.** Each `x86_*` / word op / flag combinator below is
   a copy of the like-named Rocq definition, with the Rocq quoted in the
   docstring. A reader can diff the two by eye.
2. **The transcription is translation-validated.** For every ported
   instruction, `TranslationValidation.lean` pins our model's output to the
   *exact numeric value* Jasmin's compiled Rocq function produces on shared
   concrete inputs — data word **and** the relevant flags — plus one real
   emitted `#MULX → #ADCX → #ADOX` carry-chain block from
   `bench/mpn_adxblk_carry_compare/mpn_addmul_1_adx_blk4_64.jazz` (lines 17–19),
   validated against Jasmin's sequence evaluation.
3. **It is reconciled with the prior hand-authored model.** `Model.lean`'s
   `step` is proved to agree with this transcription on the data result for the
   modeled subset (the `*_agrees_jasmin` lemmas), so the existing
   `Preservation.lean` theorems carry over unchanged.

The *modeled subset* is the scalar GP-register data ALU jasminc emits: `MOV`,
`ADD`/`SUB`, `ADC`/`SBB`, `IMULt` (low word), `NEG`, `AND`/`OR`/`XOR`,
`SHL`/`SHR`/`SAR`, `CMOVcc`, the ADX/BMI2 trio `MULX`/`ADCX`/`ADOX`, and
word-granular
memory `MOV` through a register base (`loadMem`/`storeMem`, the reg-ptr ABI's
argument-load and result-store). `DIV`/`IDIV`, rotates, `LEA`, sub-word /
unaligned memory, SIMD/AVX, control flow, and the byte encoder are out of scope
(see `README.md`).

## What is faithful here that `Model.lean` simplified

The prior model tracked only `CF`/`OF`. This transcription computes **all five
flags Jasmin tracks** (`CF, PF, ZF, SF, OF`, the `rflag` enum of `x86_decl.v`),
each as a `JFlag := Option Bool` mirroring Rocq's `rflagv` (`some b = Def b`,
`none = Undef`): `SF = msb`, `ZF = (w == 0)`, `PF = even parity of the low
byte`, `CF = unsigned wrap`, `OF = signed overflow` for the ALU ops;
`OF = CF = some false` for the bitwise ops; `OF = CF = some ov` (and the rest
`none`) for `IMULt`; the `& wsize-1` shift-count mask and the `rflags_None`
(shift by 0) / `rflags_OF` (shift by ≥1) cases for the shifts; and the
two-independent-carry-chain `ADCX → CF only` / `ADOX → OF only` routing.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The flag value type (`rflagv`)

`arch_decl.v` (l.706): `Variant rflagv := Def of bool | Undef.` Each instruction
returns flags as `option bool` in `arch_sem.v`'s `o2rflagv` (`Some b ↦ Def b`,
`None ↦ Undef`). We model `rflagv` as `Option Bool`. -/

/-- Jasmin's `rflagv`: a defined boolean (`some b`) or undefined (`none`). -/
abbrev JFlag := Option Bool

/-! ## 2. Word operations (`word.v`)

Transcribed for the fixed machine width `w` (`reg w` in the source; `U64` for
the kernels). `wunsigned`/`wrepr` are `BitVec.toNat`/`BitVec.ofNat`. -/

/-- `wunsigned` (`word.v` l.267, `urepr`): the unsigned value of a word. -/
@[simp] def wunsigned {w : Nat} (x : BitVec w) : Nat := x.toNat

/-- `wsigned` (`word.v` l.271, `srepr`): the signed (two's-complement) value. -/
def wsigned {w : Nat} (x : BitVec w) : Int := x.toInt

/-- `wrepr s z` (`word.v` l.275, `mkword`): the word holding `z mod 2^w`.
    `BitVec.ofNat`/`ofInt` already reduce mod `2^w`. -/
@[simp] def wreprN {w : Nat} (z : Nat) : BitVec w := BitVec.ofNat w z
/-- `wrepr` on a signed integer (the `Z` case in `word.v`). -/
def wreprZ {w : Nat} (z : Int) : BitVec w := BitVec.ofInt w z

/-- `wbase s` (`word.v` l.90): the modulus `2^w`. -/
@[simp] def wbase (w : Nat) : Nat := 2 ^ w

/-- `high_bits sz n` (`word.v` l.469; `high_bits_wbase` l.472): `wrepr (n / 2^w)`
    — the high word of an unbounded product. -/
def high_bits {w : Nat} (n : Nat) : BitVec w := BitVec.ofNat w (n / 2 ^ w)

/-- `waddcarry sz x y c` (`word.v` l.764): `(2^w ≤ x+y+c, wrepr (x+y+c))`, the
    `(carry-out, low word)` pair used by `ADD`-family and `ADCX`/`ADOX`. -/
def waddcarry {w : Nat} (x y : BitVec w) (c : Bool) : Bool × BitVec w :=
  let n := x.toNat + y.toNat + (if c then 1 else 0)
  (decide (2 ^ w ≤ n), BitVec.ofNat w n)

/-- `wumul sz x y` (`word.v` l.780): `(high_bits (x*y), wrepr (x*y))` — the
    `(hi, lo)` full unsigned product used by `MULX`. -/
def wumul {w : Nat} (x y : BitVec w) : BitVec w × BitVec w :=
  let n := x.toNat * y.toNat
  (high_bits n, BitVec.ofNat w n)

/-- `wshl sz x n` (`word.v` l.444): logical left shift, count clamped to the
    word width (`Z.min (wsize_bits sz) n`). For `n < w` this is the raw shift;
    for `n ≥ w` it shifts by exactly `w` (giving `0`). -/
def wshl {w : Nat} (x : BitVec w) (n : Nat) : BitVec w := x <<< (min w n)

/-- `wshr sz x n` (`word.v` l.427): logical right shift, count clamped to `w`. -/
def wshr {w : Nat} (x : BitVec w) (n : Nat) : BitVec w := x >>> (min w n)

/-- `wsar sz x n` (`word.v` l.463): arithmetic right shift, count clamped to `w`. -/
def wsar {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  BitVec.sshiftRight x (min w n)

/-- `msb` (`word.v` l.753): the top bit `wbit_n w (w-1)`. -/
def msb {w : Nat} (x : BitVec w) : Bool := x.msb

/-- `lsb` (`word.v` l.752): the bottom bit `wbit_n w 0`. -/
def lsb {w : Nat} (x : BitVec w) : Bool := x.getLsbD 0

/-! ## 3. Flag-of-word combinators (`x86_instr_decl.v`) -/

/-- `SF_of_word` (l.245): the sign flag is the msb. -/
def SF_of_word {w : Nat} (x : BitVec w) : Bool := msb x

/-- `ZF_of_word` (l.251): the zero flag is `x == 0`. -/
def ZF_of_word {w : Nat} (x : BitVec w) : Bool := decide (x.toNat = 0)

/-- `PF_of_word` (l.248): `foldl xorb true [wbit_n w i | i ∈ 0..7]` — set iff the
    low byte has an even number of set bits (x86 even-parity flag). -/
def PF_of_word {w : Nat} (x : BitVec w) : Bool :=
  (List.range 8).foldl (fun acc i => acc != x.getLsbD i) true

/-! ### 4. The result tuple and the flag tuples

Jasmin's `b5w_ty sz` result is the 6-tuple `(OF, CF, SF, PF, ZF, w)` (the order
of the `(:: OF, CF, SF, PF, ZF & w)` literal in `rflags_of_aluop` etc.). We
carry it as a structure for readability; the projections name each flag. -/

/-- The `b5w_ty` result of a flag-setting ALU op: five flags plus the data word,
    in Jasmin's `(:: OF, CF, SF, PF, ZF & w)` order. -/
structure B5W (w : Nat) where
  of : JFlag
  cf : JFlag
  sf : JFlag
  pf : JFlag
  zf : JFlag
  word : BitVec w
  deriving Repr

/-- `rflags_of_aluop sz w vu vs` (l.262): the five flags after an add/sub-style
    op producing word `w`, with unbounded unsigned result `vu` and signed result
    `vs`. `OF = (wsigned w ≠ vs)` (signed overflow), `CF = (wunsigned w ≠ vu)`
    (unsigned wrap), `SF/PF/ZF` from the word. -/
def rflags_of_aluop {w : Nat} (res : BitVec w) (vu : Nat) (vs : Int) : B5W w :=
  { of := some (decide (wsigned res ≠ vs))
    cf := some (decide (wunsigned res ≠ vu))
    sf := some (SF_of_word res)
    pf := some (PF_of_word res)
    zf := some (ZF_of_word res)
    word := res }

/-- `rflags_of_bwop sz w` (l.256): the flags after a bitwise op. `OF = CF =
    some false`; `SF/PF/ZF` from the word. -/
def rflags_of_bwop {w : Nat} (res : BitVec w) : B5W w :=
  { of := some false
    cf := some false
    sf := some (SF_of_word res)
    pf := some (PF_of_word res)
    zf := some (ZF_of_word res)
    word := res }

/-- `rflags_of_mul ov` merged with the low word (l.267, used by `IMULt`):
    `OF = CF = some ov`, `SF = PF = ZF = none`. -/
def rflags_of_mul {w : Nat} (ov : Bool) (res : BitVec w) : B5W w :=
  { of := some ov, cf := some ov, sf := none, pf := none, zf := none, word := res }

/-- `rflags_None_w v` (l.285): all flags undefined, word unchanged (the
    shift-by-0 case). -/
def rflags_None {w : Nat} (v : BitVec w) : B5W w :=
  { of := none, cf := none, sf := none, pf := none, zf := none, word := v }

/-- `rflags_OF i r rc OF` (l.1108): the shift result flags. `OF = some OF` iff
    the count `i = 1` (else `none`); `CF = some rc`; `SF/PF/ZF` from `r`. -/
def rflags_OF {w : Nat} (i : Nat) (r : BitVec w) (rc ofv : Bool) : B5W w :=
  { of := if i = 1 then some ofv else none
    cf := some rc
    sf := some (SF_of_word r)
    pf := some (PF_of_word r)
    zf := some (ZF_of_word r)
    word := r }

/-! ## 5. The shift-count mask (`x86_shift_mask`, l.1042)

`x86_shift_mask U64 = 63`, `U32/U16/U8 = 31`, `U128 = 127`, `U256 = 255`. For a
generic width `w` (a power-of-two word) this is `w - 1`; we expose the value our
emitted subset uses (`w = 64 → 63`). The count is masked by `& (w-1)` before
shifting. -/

/-- `x86_shift_mask` reduced to a count modulus: `i & (w-1)` keeps the low
    `log2 w` bits of the count, i.e. `i % w`. -/
def shiftCount {w : Nat} (i : BitVec w) : Nat := i.toNat % w

/-! ## 6. Per-instruction semantic functions (`x86_instr_decl.v`)

Each `x86_*` below is a transcription of the like-named Rocq function. The Rocq
is quoted in the docstring; the differential pins live in
`TranslationValidation.lean`. -/

/-- `x86_MOV sz x = x` (l.604). -/
def x86_MOV {w : Nat} (x : BitVec w) : BitVec w := x

/-- `x86_CMOVcc sz b w2 w3 = if b then w2 else w3` (l.709). -/
def x86_CMOVcc {w : Nat} (b : Bool) (w2 w3 : BitVec w) : BitVec w :=
  if b then w2 else w3

/-- `x86_ADD sz v1 v2` (l.717): `rflags_of_aluop_w (v1+v2) (uns v1 + uns v2)
    (sgn v1 + sgn v2)`. -/
def x86_ADD {w : Nat} (v1 v2 : BitVec w) : B5W w :=
  rflags_of_aluop (v1 + v2) (v1.toNat + v2.toNat) (wsigned v1 + wsigned v2)

/-- `x86_SUB sz v1 v2` (l.726): `rflags_of_aluop_w (v1-v2) (uns v1 - uns v2)
    (sgn v1 - sgn v2)`. The unsigned `vu` is the (possibly negative) integer
    difference; `CF = (wunsigned (v1-v2) ≠ vu)` is the borrow. We compute `vu`
    over `Int` to match Rocq's `Z` subtraction. -/
def x86_SUB {w : Nat} (v1 v2 : BitVec w) : B5W w :=
  let res := v1 - v2
  { of := some (decide (wsigned res ≠ wsigned v1 - wsigned v2))
    cf := some (decide ((wunsigned res : Int) ≠ (v1.toNat : Int) - (v2.toNat : Int)))
    sf := some (SF_of_word res)
    pf := some (PF_of_word res)
    zf := some (ZF_of_word res)
    word := res }

/-- `add_carry sz x y c = wrepr (x+y+c)` (l.834). -/
def add_carry {w : Nat} (x y : BitVec w) (c : Nat) : BitVec w :=
  BitVec.ofNat w (x.toNat + y.toNat + c)

/-- `x86_ADC sz v1 v2 c` (l.837): `rflags_of_aluop_w (add_carry v1 v2 c)
    (uns v1 + uns v2 + c) (sgn v1 + sgn v2 + c)`, `c := b2z c`. -/
def x86_ADC {w : Nat} (v1 v2 : BitVec w) (c : Bool) : B5W w :=
  let cN : Nat := if c then 1 else 0
  rflags_of_aluop (add_carry v1 v2 cN) (v1.toNat + v2.toNat + cN)
    (wsigned v1 + wsigned v2 + (cN : Int))

/-- `sub_borrow sz x y c = wrepr (x-y-c)` (l.847). -/
def sub_borrow {w : Nat} (x y : BitVec w) (c : Nat) : BitVec w :=
  BitVec.ofInt w ((x.toNat : Int) - y.toNat - c)

/-- `x86_SBB sz v1 v2 c` (l.850): `rflags_of_aluop_w (sub_borrow v1 v2 c)
    (uns v1 - (uns v2 + c)) (sgn v1 - (sgn v2 + c))`, `c := b2z c`. -/
def x86_SBB {w : Nat} (v1 v2 : BitVec w) (c : Bool) : B5W w :=
  let cN : Nat := if c then 1 else 0
  let res := sub_borrow v1 v2 cN
  { of := some (decide (wsigned res ≠ wsigned v1 - (wsigned v2 + (cN : Int))))
    cf := some (decide ((wunsigned res : Int) ≠ (v1.toNat : Int) - (v2.toNat + cN)))
    sf := some (SF_of_word res)
    pf := some (PF_of_word res)
    zf := some (ZF_of_word res)
    word := res }

/-- `x86_IMULt sz v1 v2` (l.762): low word `v1*v2` with `OF=CF=ov` (signed
    overflow of the full product), `SF=PF=ZF=none`. We model the low word and the
    flag *shape* (`rflags_of_mul ov`); the overflow predicate `ov` is computed
    from the signed high/low decomposition. -/
def x86_IMULt {w : Nat} (v1 v2 : BitVec w) : B5W w :=
  let lo := v1 * v2
  let full := wsigned v1 * wsigned v2
  -- ov : the full signed product does not fit in `w` signed bits.
  let ov := decide (full < -(2 ^ (w - 1) : Int) ∨ full > (2 ^ (w - 1) : Int) - 1)
  rflags_of_mul ov lo

/-- `x86_NEG sz w` (l.~755): `v := -w`, with `OF = (wsigned v ≠ -wsigned w)`
    (signed overflow, set only for `w = INT_MIN`), `CF = (w ≠ 0)` (the borrow of
    `0 − w`), `SF/PF/ZF` from `v`. The data word is the two's-complement negation
    `0 - w`. -/
def x86_NEG {w : Nat} (v0 : BitVec w) : B5W w :=
  let res := 0 - v0
  { of := some (decide (wsigned res ≠ - wsigned v0))
    cf := some (decide (v0 ≠ 0))
    sf := some (SF_of_word res)
    pf := some (PF_of_word res)
    zf := some (ZF_of_word res)
    word := res }

/-- `x86_AND sz v1 v2 = rflags_of_bwop_w (wand v1 v2)` (l.1008). -/
def x86_AND {w : Nat} (v1 v2 : BitVec w) : B5W w := rflags_of_bwop (v1 &&& v2)

/-- `x86_TEST sz x y = rflags_of_bwop (wand x y)` (l.993).  Jasmin gives `TEST`
    the `b5` result shape and `AND` the `b5w` one, so the two compute the same
    five flags and only `AND` writes the word; the word carried here is unused
    by the `test` arm, which writes flags alone. -/
def x86_TEST {w : Nat} (x y : BitVec w) : B5W w := rflags_of_bwop (x &&& y)

/-- `wror sz x n` (`word.v`): rotate right, count already masked. -/
def wror {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  (x >>> n) ||| (x <<< (w - n))

/-- `wrol sz x n` (`word.v`): rotate left, count already masked. -/
def wrol {w : Nat} (x : BitVec w) (n : Nat) : BitVec w :=
  (x <<< n) ||| (x >>> (w - n))

/-- The `b2w_ty` result of a rotate: `OF`, `CF` and the data word.  `SF`, `PF`
    and `ZF` are absent from Jasmin's output tuple, so a rotate leaves them as
    it found them — which is why this cannot go through `B5W`, whose writer
    replaces all five. -/
structure B2W (w : Nat) where
  of : JFlag
  cf : JFlag
  word : BitVec w
  deriving Repr

/-- `x86_ROR sz v i` (l.1050): mask the count; a count of zero writes neither
    flag; otherwise `CF = msb r`, and `OF` is defined only at a count of one. -/
def x86_ROR {w : Nat} (v : BitVec w) (icount : BitVec w) : B2W w :=
  let i := shiftCount icount
  if i = 0 then { of := none, cf := none, word := v }
  else
    let r := wror v i
    let cf := msb r
    { of := if i = 1 then some (decide (cf ≠ msb v)) else none
      cf := some cf
      word := r }

/-- `x86_ROL sz v i` (l.1063): as `x86_ROR`, with `CF = lsb r`. -/
def x86_ROL {w : Nat} (v : BitVec w) (icount : BitVec w) : B2W w :=
  let i := shiftCount icount
  if i = 0 then { of := none, cf := none, word := v }
  else
    let r := wrol v i
    let cf := lsb r
    { of := if i = 1 then some (decide (msb r ≠ cf)) else none
      cf := some cf
      word := r }

/-- `x86_RORX sz v i = wror v i` (l.1250): the BMI2 rotate, `w_ty` shaped, so it
    writes no flag at all. -/
def x86_RORX {w : Nat} (v : BitVec w) (icount : BitVec w) : BitVec w :=
  wror v (shiftCount icount)

/-- `x86_bmi_shift sz op v i = op v (i &&& shift_mask)` (l.1257): the BMI2
    variable shifts, `w_ty` shaped, so they write no flag. -/
def x86_SHLX {w : Nat} (v : BitVec w) (icount : BitVec w) : BitVec w :=
  wshl v (shiftCount icount)

/-- `x86_SHRX` (l.1265): the logical BMI2 variable shift. -/
def x86_SHRX {w : Nat} (v : BitVec w) (icount : BitVec w) : BitVec w :=
  wshr v (shiftCount icount)

/-- `x86_SARX` (l.1269): the arithmetic BMI2 variable shift. -/
def x86_SARX {w : Nat} (v : BitVec w) (icount : BitVec w) : BitVec w :=
  wsar v (shiftCount icount)

/-- `x86_MOVZX szi szo x = zero_extend szo x` (l.692): `w_ty` shaped, no flag.
    `srcW` is the source width; the bits above it are cleared. -/
def x86_MOVZX {w : Nat} (srcW : Nat) (v : BitVec w) : BitVec w :=
  v &&& (BitVec.allOnes w >>> (w - min w srcW))

/-- `x86_MOVSX szi szo x = sign_extend szo x` (l.674): `w_ty` shaped, no flag.
    The source's top bit is replicated above `srcW`. -/
def x86_MOVSX {w : Nat} (srcW : Nat) (v : BitVec w) : BitVec w :=
  wsar (wshl v (w - min w srcW)) (w - min w srcW)

/-- `x86_LEA sz addr = addr` (l.986): the computed address itself, `w_ty`
    shaped, so no flag is written.  This is what separates it from a load. -/
def x86_LEA {w : Nat} (addr : BitVec w) : BitVec w := addr

/-- `rflags_of_andn sz w` (l.279): `OF = CF = some false`, `SF`/`ZF` from the
    word, and **`PF` undefined** — unlike `rflags_of_bwop`, which defines it. -/
def rflags_of_andn {w : Nat} (res : BitVec w) : B5W w :=
  { of := some false
    cf := some false
    sf := some (SF_of_word res)
    pf := none
    zf := some (ZF_of_word res)
    word := res }

/-- `x86_ANDN sz v1 v2 = flags_w (rflags_of_andn (wandn v1 v2))` (l.1028).
    `wandn v1 v2` is `(~~~ v1) &&& v2`. -/
def x86_ANDN {w : Nat} (v1 v2 : BitVec w) : B5W w := rflags_of_andn ((~~~ v1) &&& v2)

/-- `x86_NOT sz v = wnot v` (l.1036): the `w_ty` shape, so no flag is written. -/
def x86_NOT {w : Nat} (v : BitVec w) : BitVec w := ~~~ v

/-- `x86_CMP sz x y = rflags_of_aluop (x - y) …` (l.1001).  Jasmin gives `CMP`
    the `b5` shape and `SUB` the `b5w` one over the same `rflags_of_aluop`, so
    the two compute the same five flags and only `SUB` writes the difference;
    the word carried here is unused by the `cmp` arm, which writes flags alone.
    The same relationship `TEST` has to `AND`. -/
def x86_CMP {w : Nat} (x y : BitVec w) : B5W w := x86_SUB x y

/-- `x86_OR sz v1 v2 = rflags_of_bwop_w (wor v1 v2)` (l.1014). -/
def x86_OR {w : Nat} (v1 v2 : BitVec w) : B5W w := rflags_of_bwop (v1 ||| v2)

/-- `x86_XOR sz v1 v2 = rflags_of_bwop_w (wxor v1 v2)` (l.1020). -/
def x86_XOR {w : Nat} (v1 v2 : BitVec w) : B5W w := rflags_of_bwop (v1 ^^^ v2)

/-- `x86_SHL sz v i` (l.1116): mask `i`; if `0`, `rflags_None_w v`; else
    `rc = msb (wshl v (i-1))`, `r = wshl v i`, `rflags_OF i r rc (msb r ⊕ rc)`. -/
def x86_SHL {w : Nat} (v : BitVec w) (icount : BitVec w) : B5W w :=
  let i := shiftCount icount
  if i = 0 then rflags_None v
  else
    let rc := msb (wshl v (i - 1))
    let r := wshl v i
    rflags_OF i r rc (msb r != rc)

/-- `x86_SHR sz v i` (l.1128): mask `i`; if `0`, `rflags_None_w v`; else
    `rc = lsb (wshr v (i-1))`, `r = wshr v i`, `rflags_OF i r rc (msb v)`. -/
def x86_SHR {w : Nat} (v : BitVec w) (icount : BitVec w) : B5W w :=
  let i := shiftCount icount
  if i = 0 then rflags_None v
  else
    let rc := lsb (wshr v (i - 1))
    let r := wshr v i
    rflags_OF i r rc (msb v)

/-- `x86_SAR sz v i` (l.1143): mask `i`; if `0`, `rflags_None_w v`; else
    `rc = lsb (wsar v (i-1))`, `r = wsar v i`, `rflags_OF i r rc false`. -/
def x86_SAR {w : Nat} (v : BitVec w) (icount : BitVec w) : B5W w :=
  let i := shiftCount icount
  if i = 0 then rflags_None v
  else
    let rc := lsb (wsar v (i - 1))
    let r := wsar v i
    rflags_OF i r rc false

/-! ### ADX / BMI2 trio result tuples

`x86_ADCX` (l.862) returns `bw_ty = (option bool, word)`; `x86_MULX_lo_hi`
(l.874) returns `w2_ty = (word, word) = (lo, hi)`. -/

/-- `x86_ADCX sz v1 v2 c` (l.862): `let (c,w) := waddcarry v1 v2 c in (Some c, w)`.
    The **same** function backs both `ADCX` and `ADOX`; the instruction wrapper
    routes the carry bool to `CF` (`Ox86_ADCX_instr`) resp. `OF`
    (`Ox86_ADOX_instr`). Returns `(carry-flag, low word)`. -/
def x86_ADCX {w : Nat} (v1 v2 : BitVec w) (c : Bool) : JFlag × BitVec w :=
  let (co, res) := waddcarry v1 v2 c
  (some co, res)

/-- `x86_MULX_lo_hi sz v1 v2` (l.874): `let (hi, lo) := wumul v1 v2 in (lo, hi)`
    — returns `(lo, hi)`, touches no flag. -/
def x86_MULX_lo_hi {w : Nat} (v1 v2 : BitVec w) : BitVec w × BitVec w :=
  let (hi, lo) := wumul v1 v2
  (lo, hi)

/-! ## 7. Machine state and the `eval_instr` / `eval_op` composition

`arch_sem.v`'s `asmmem` has `asm_reg : regmap`, `asm_flag : rflagmap`, and a
byte memory `asm_mem`. We model the register file as a name → word function, the
flag map as the five named `JFlag`s (the `rflag` enum `CF, PF, ZF, SF, OF`), and
the memory as a word-granular `(base, offset) → word` map (the reg-ptr ABI only
ever issues aligned whole-word accesses `[base + off]`). `exec_instr_op` writes
the result tuple back over the instruction's `id_out` operand list; for the
emitted subset that means: write the data word to the destination register and
each defined flag to its `rflag` slot, leaving unwritten flags untouched. -/

/-- The flag map (`rflagmap`): the five x86 condition flags as `JFlag`s, mirroring
    `asm_flag` over the `rflag` enum `{CF, PF, ZF, SF, OF}`. -/
structure RFlags where
  cf : JFlag := none
  pf : JFlag := none
  zf : JFlag := none
  sf : JFlag := none
  of : JFlag := none
  deriving DecidableEq, Repr

/-- The byte-addressed memory (`asm_mem`/`mem` of `asmmem`), modeled at word
    granularity as a finite map keyed by `(base register name, byte offset)`.
    The reg-ptr ABI the kernels use only ever loads/stores whole `w`-bit words
    at `[base + off]`, so a `(String × Int) → BitVec w` map (absent ⇒ `0`) is the
    faithful word-level view of Jasmin's `read`/`write` on the emitted subset
    (`arch_sem.v`'s `mem_read`/`mem_write`, restricted to aligned word accesses
    through a register base). The offset is an `Int` so negative frame offsets
    are representable; the kernels use non-negative `[base + 8·k]`. -/
abbrev JMem (w : Nat) := String → Int → BitVec w

/-- The faithful machine state: register file, the five-flag map, and the
    word-addressed memory, at width `w`. The `regmap`/`rflagmap`/`mem` analogue
    of `asmmem` for the scalar subset. -/
structure JState (w : Nat) where
  regs : String → BitVec w
  flags : RFlags := {}
  /-- Word-addressed memory keyed by `(base, byte offset)`; absent ⇒ `0`. -/
  mem : JMem w := fun _ _ => 0

/-- Read a register (`asm_reg`). An absent name reads as `0`. -/
@[simp] def JState.get {w : Nat} (s : JState w) (r : String) : BitVec w := s.regs r

/-- Write a register, leaving flags and other registers unchanged
    (`mem_write_reg`, with the `MSB_CLEAR` full-width write the emitted ops use). -/
def JState.setReg {w : Nat} (s : JState w) (r : String) (v : BitVec w) : JState w :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

/-- Read a memory word at `[base + off]` (`mem_read` on an aligned word access).
    An untouched cell reads as `0`. -/
@[simp] def JState.load {w : Nat} (s : JState w) (base : String) (off : Int) :
    BitVec w := s.mem base off

/-- Write a memory word at `[base + off]` (`mem_write`), leaving registers, flags
    and every other cell unchanged. -/
def JState.store {w : Nat} (s : JState w) (base : String) (off : Int)
    (v : BitVec w) : JState w :=
  { s with mem := fun b o => if b = base ∧ o = off then v else s.mem b o }

@[simp] theorem JState.load_store_same {w : Nat} (s : JState w) (base : String)
    (off : Int) (v : BitVec w) : (s.store base off v).load base off = v := by
  simp [JState.store, JState.load]

/-- Reading a different cell `(b', o')` from a store at `(base, off)` falls
    through to the underlying memory. Discharges the disequality via `decide`. -/
@[simp] theorem JState.load_store_other {w : Nat} (s : JState w) (base : String)
    (off : Int) (v : BitVec w) (b' : String) (o' : Int)
    (h : ¬ (b' = base ∧ o' = off)) :
    (s.store base off v).load b' o' = s.load b' o' := by
  simp only [JState.store, JState.load]
  rw [if_neg h]

@[simp] theorem JState.regs_store {w : Nat} (s : JState w) (base : String)
    (off : Int) (v : BitVec w) : (s.store base off v).regs = s.regs := rfl

@[simp] theorem JState.flags_store {w : Nat} (s : JState w) (base : String)
    (off : Int) (v : BitVec w) : (s.store base off v).flags = s.flags := rfl

/-- Write a memory word at a **base+index** effective address `[base + idx·scale]`
    where `idx` is a *register* (the index register holds a runtime value) and
    `scale` is the element stride in bytes (`1/2/4/8`, the x86 SIB scale). This is
    the `mov %src, (%base, %idx, scale)` addressing mode that a register-indexed
    scatter store `r[ctr++] = v` compiles to — the dynamic-offset analogue of
    `JState.store`, with the offset computed from the index register's value at
    evaluation time rather than a compile-time displacement (`arch_sem.v`'s
    `decode_addr` for an `Addr` whose `ad_offset`/`ad_scale` select a register
    index). The effective offset is `scale · (s.get idx).toNat`. -/
def JState.storeIdx {w : Nat} (s : JState w) (base : String) (idx : String)
    (scale : Nat) (v : BitVec w) : JState w :=
  s.store base (scale * (s.get idx).toNat) v

@[simp] theorem JState.regs_storeIdx {w : Nat} (s : JState w) (base idx : String)
    (scale : Nat) (v : BitVec w) : (s.storeIdx base idx scale v).regs = s.regs := rfl

@[simp] theorem JState.flags_storeIdx {w : Nat} (s : JState w) (base idx : String)
    (scale : Nat) (v : BitVec w) : (s.storeIdx base idx scale v).flags = s.flags := rfl

/-- Reading back the just-scattered cell at the index register's current value
    returns the stored word: a register-indexed store followed by the matching
    register-indexed load round-trips (the scatter actually lands where the index
    points). -/
@[simp] theorem JState.load_storeIdx_same {w : Nat} (s : JState w) (base idx : String)
    (scale : Nat) (v : BitVec w) :
    (s.storeIdx base idx scale v).load base ((scale * (s.get idx).toNat : Nat) : Int) = v := by
  simp only [JState.storeIdx, JState.get]
  exact JState.load_store_same s base _ v

/-- A scatter to index `idx` does not disturb a cell at a different effective
    offset: distinct indices (or a different base) write disjoint memory, so the
    `r[ctr]` writes across the rejection loop never clobber each other. -/
@[simp] theorem JState.load_storeIdx_other {w : Nat} (s : JState w) (base idx : String)
    (scale : Nat) (v : BitVec w) (b' : String) (o' : Int)
    (h : ¬ (b' = base ∧ o' = ((scale * (s.get idx).toNat : Nat) : Int))) :
    (s.storeIdx base idx scale v).load b' o' = s.load b' o' := by
  simp only [JState.storeIdx]
  exact JState.load_store_other s base _ v b' o' h

/-- Read a memory word at a **base+index** effective address `[base + idx·scale]`
    where `idx` is a *register* and `scale` is the element stride in bytes
    (the x86 SIB scale, `1/2/4/8`). This is the `mov (%base, %idx, scale), %dst`
    register-indexed gather load that a `v = m[row*AC + col]` matrix access
    compiles to — the dynamic-offset analogue of `JState.load`, with the offset
    `scale · (s.get idx).toNat` computed from the index register at evaluation
    time (`arch_sem.v`'s `decode_addr` for an `Addr` selecting a register index).
    The read-side dual of `JState.storeIdx`. -/
def JState.loadIdx {w : Nat} (s : JState w) (base : String) (idx : String)
    (scale : Nat) : BitVec w :=
  s.load base (scale * (s.get idx).toNat)

/-- A register-indexed load does not change the registers (it is a pure read);
    `loadIdx` is defined through `load`, which leaves `regs` untouched. -/
@[simp] theorem JState.loadIdx_storeIdx_same {w : Nat} (s : JState w)
    (base idx : String) (scale : Nat) (v : BitVec w) :
    (s.storeIdx base idx scale v).loadIdx base idx scale = v := by
  simp only [JState.loadIdx, JState.storeIdx, JState.get]
  exact JState.load_store_same s base _ v

/-- Gathering from a different effective offset than a just-scattered cell falls
    through to the underlying memory: `loadIdx`/`storeIdx` on disjoint
    `(base, idx·scale)` addresses commute. -/
@[simp] theorem JState.loadIdx_storeIdx_other {w : Nat} (s : JState w)
    (base idx : String) (scale : Nat) (v : BitVec w) (b' i' : String) (sc' : Nat)
    (h : ¬ (b' = base ∧ ((sc' * (s.get i').toNat : Nat) : Int)
              = ((scale * (s.get idx).toNat : Nat) : Int))) :
    (s.storeIdx base idx scale v).loadIdx b' i' sc' = s.loadIdx b' i' sc' := by
  simp only [JState.loadIdx, JState.storeIdx]
  exact JState.load_store_other s base _ v b' _ h

/-- Write the full `B5W` result of a flag-setting ALU op: the data word to `dst`
    and **all five** flags. Mirrors `exec_instr_op` for an instruction whose
    `id_out` is `[OF; CF; SF; PF; ZF; data]` (e.g. `mk_instr_w2_b5w_010`). -/
def JState.writeB5W {w : Nat} (s : JState w) (dst : String) (t : B5W w) : JState w :=
  { regs := fun r' => if r' = dst then t.word else s.regs r'
    flags := { cf := t.cf, pf := t.pf, zf := t.zf, sf := t.sf, of := t.of }
    mem := s.mem }

/-- Write the `B2W` result of a rotate: the data word to `dst`, `OF` and `CF`,
    and **`SF`/`PF`/`ZF` left as they were**. Mirrors `exec_instr_op` for an
    instruction whose `id_out` is `[OF; CF; data]` (`mk_instr_ww8_b2w_0c0`,
    e.g. `Ox86_ROR_instr`) — the three absent flags are not written, which is
    what distinguishes this from `writeB5W` with undefined entries. -/
def JState.writeB2W {w : Nat} (s : JState w) (dst : String) (t : B2W w) : JState w :=
  { regs := fun r' => if r' = dst then t.word else s.regs r'
    flags := { s.flags with cf := t.cf, of := t.of }
    mem := s.mem }

/-- Write the five flags of a flag-setting op that has no data output, leaving
    every register alone. Mirrors `exec_instr_op` for an instruction whose
    `id_out` is `[OF; CF; SF; PF; ZF]` (`mk_instr_w2_b5`, e.g.
    `Ox86_TEST_instr`). -/
def JState.writeB5 {w : Nat} (s : JState w) (t : B5W w) : JState w :=
  { s with flags := { cf := t.cf, pf := t.pf, zf := t.zf, sf := t.sf, of := t.of } }

@[simp] theorem JState.get_writeB5 {w : Nat} (s : JState w) (t : B5W w) (x : String) :
    (s.writeB5 t).get x = s.get x := rfl

@[simp] theorem JState.writeB5_flags {w : Nat} (s : JState w) (t : B5W w) :
    (s.writeB5 t).flags = { cf := t.cf, pf := t.pf, zf := t.zf, sf := t.sf, of := t.of } := rfl

/-- Read a flag as a concrete `Bool`, treating `Undef` as `false` (the carry
    chains always have their flag defined before use). -/
def JState.flagB {w : Nat} (s : JState w) (f : RFlags → JFlag) : Bool :=
  (f s.flags).getD false

@[simp] theorem JState.get_setReg_same {w : Nat} (s : JState w) (r : String)
    (v : BitVec w) : (s.setReg r v).get r = v := by simp [JState.setReg, JState.get]

@[simp] theorem JState.get_setReg_other {w : Nat} (s : JState w) (r r' : String)
    (v : BitVec w) (h : r' ≠ r) : (s.setReg r v).get r' = s.get r' := by
  simp [JState.setReg, JState.get, h]

@[simp] theorem JState.get_writeB5W_same {w : Nat} (s : JState w) (dst : String)
    (t : B5W w) : (s.writeB5W dst t).get dst = t.word := by simp [JState.writeB5W, JState.get]

@[simp] theorem JState.writeB5W_flags {w : Nat} (s : JState w) (dst : String)
    (t : B5W w) :
    (s.writeB5W dst t).flags = { cf := t.cf, pf := t.pf, zf := t.zf, sf := t.sf, of := t.of } := by
  simp [JState.writeB5W]

/-! ## 8. The ported instruction set and the `evalInstr` step

`JInstr` is the emitted scalar subset, with each arm naming the `Ox86_*_instr`
it transcribes. `evalInstr` is the `eval_op`/`exec_instr_op` composition: read
the operands, apply the `x86_*` semantic function, write the result tuple back
over the instruction's output list. -/

/-- An operand: a named register or an immediate (the `Reg`/`Imm` `asm_arg`
    cases; `Addr`/`XReg` are out of scope). -/
inductive JOperand where
  | reg (r : String)
  | imm (v : Nat)
  deriving DecidableEq, Repr

/-- `eval_asm_arg` for the `Reg`/`Imm` cases (`arch_sem.v` l.210). -/
@[simp] def JOperand.eval {w : Nat} (s : JState w) : JOperand → BitVec w
  | .reg r => s.get r
  | .imm v => BitVec.ofNat w v

/-- The emitted scalar x86 instruction subset, each arm naming the Jasmin
    `Ox86_*_instr` it transcribes. Two-address arithmetic/logical form (the
    destination is also source 0).

    **Coverage against jasmin's `x86_op`, and where the line is drawn.** This is
    a subset, and the omissions are of two kinds that should not be confused.

    Declined on constant-time grounds, per the Intel DOIT ∩ AMD DIT rule (Intel's
    DOIT instruction list:
    https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/resources/data-operand-independent-timing-instructions.html):
    `DIV`/`IDIV` and `CQO`
    (variable latency on the operand values), `BSR`/`BSF`, `BSWAP`, `LZCNT`,
    `TZCNT`, `POPCNT`, and `PDEP`/`PEXT` — the last are microcoded and
    data-dependent on AMD Zen 1 and 2, so they read as ordinary bit operations
    while leaking through timing. These are not gaps to close; adding one would
    put a variable-latency instruction inside a constant-time backend.

    Not yet transcribed, with no reason beyond nothing having needed them:
    `XCHG`, `INC`/`DEC`, `SHLD`/`SHRD`, `MUL`, `IMULr`/`IMULri`, `BT`/`BTR`/`BTS`,
    `RCL`/`RCR`, and the SIMD/AES/SHA families. Add these as the fragment needs
    them, following the transcription discipline: the `x86_*` function mirrors
    the Rocq definition, and the writer matches the instruction's `id_out` —
    `writeB5W` for a five-flag op with a data word, `writeB5` for flags alone
    (`TEST`, `CMP`), `writeB2W` where only `OF`/`CF` are written and the other
    three are PRESERVED (the rotates), and `setReg` where no flag moves. -/
inductive JInstr (w : Nat) where
  /-- `Ox86_MOV_instr`. -/
  | mov (dst : String) (src : JOperand)
  /-- `Ox86_ADD_instr`. -/
  | add (dst : String) (src : JOperand)
  /-- `Ox86_SUB_instr`. -/
  | sub (dst : String) (src : JOperand)
  /-- `Ox86_ADC_instr` (carry-in from `CF`). -/
  | adc (dst : String) (src : JOperand)
  /-- `Ox86_SBB_instr` (borrow-in from `CF`). -/
  | sbb (dst : String) (src : JOperand)
  /-- `Ox86_IMULr_instr` (low word). -/
  | imul (dst : String) (src : JOperand)
  /-- `Ox86_NEG_instr`: `dst := 0 − dst` (two's-complement negation). -/
  | neg (dst : String)
  /-- `Ox86_SETcc_instr` (set-on-carry → byte GPR, zero-extended). `SETB`/`SETC`
      writes `1` to the low byte of `dst` when `CF` is set, `0` otherwise; the
      owned printer follows it with a `MOVZBQ` so the full 64-bit `dst` is the
      zero-extended flag value `if CF then 1 else 0`. This is the flag-to-GPR
      materialisation the open-coded carry idiom uses (`adc; setc cy`) — the one
      primitive the runtime-N `mpn_add_n`/`mpn_sub_n` carry chain needs to keep
      the carry across the flag-clobbering loop back-edge (#500/#560). The model
      writes the **already zero-extended** word `if CF then 1 else 0` (so the
      `SETB`+`MOVZBQ` pair is modeled as one arm) and touches no flag. -/
  | setc (dst : String)
  /-- `Ox86_AND_instr`. -/
  | and_ (dst : String) (src : JOperand)
  /-- `Ox86_TEST_instr`.  Sets the five flags from `a &&& b` and writes no
      register, which is what distinguishes it from `and_ a a`: the two agree
      on every flag, and `and_` additionally rewrites `a` with its own value. -/
  | test (a : String) (b : JOperand)
  /-- `Ox86_CMP_instr`.  The five flags of `a - b`, with the difference
      discarded; `sub` is the same flags plus the write. -/
  | cmp (a : String) (b : JOperand)
  /-- `Ox86_NOT_instr`.  Writes no flag. -/
  | not_ (dst : String)
  /-- `Ox86_ANDN_instr` (BMI1): `dst := (~~~ src1) &&& src2`, non-destructive in
      both sources.  `PF` is undefined, unlike the other bitwise ops. -/
  | andn (dst src1 src2 : String)
  /-- `Ox86_ROL_instr`.  Writes `OF` and `CF` only; `SF`/`PF`/`ZF` keep the
      values they had. -/
  | rol (dst : String) (amt : JOperand)
  /-- `Ox86_ROR_instr`.  As `rol`, rotating the other way. -/
  | ror (dst : String) (amt : JOperand)
  /-- `Ox86_RORX_instr` (BMI2): a rotate that writes no flag and reads its
      source without destroying it. -/
  | rorx (dst src : String) (amt : JOperand)
  /-- `Ox86_SHLX_instr` (BMI2): variable shift left, no flag written. -/
  | shlx (dst src cnt : String)
  /-- `Ox86_SHRX_instr` (BMI2): variable logical shift right, no flag. -/
  | shrx (dst src cnt : String)
  /-- `Ox86_SARX_instr` (BMI2): variable arithmetic shift right, no flag. -/
  | sarx (dst src cnt : String)
  /-- `Ox86_MOVZX_instr`: zero-extend the low `srcW` bits of `src`. No flag. -/
  | movzx (dst : String) (srcW : Nat) (src : String)
  /-- `Ox86_MOVSX_instr`: sign-extend the low `srcW` bits of `src`. No flag. -/
  | movsx (dst : String) (srcW : Nat) (src : String)
  /-- `Ox86_LEA_instr`: the address `base + idx * scale + off` itself, written
      to `dst` without a memory access. No flag. -/
  | lea (dst base idx : String) (scale : Nat) (off : Int)
  /-- `Ox86_OR_instr`. -/
  | or_ (dst : String) (src : JOperand)
  /-- `Ox86_XOR_instr`. -/
  | xor_ (dst : String) (src : JOperand)
  /-- `Ox86_SHL_instr`. -/
  | shl (dst : String) (src : JOperand)
  /-- `Ox86_SHR_instr`. -/
  | shr (dst : String) (src : JOperand)
  /-- `Ox86_SAR_instr`. -/
  | sar (dst : String) (src : JOperand)
  /-- `Ox86_CMOVcc_instr`, condition reading a flag (`e`/`ne` read `ZF`,
      `b` reads `CF`). -/
  | cmove (dst : String) (src : JOperand)
  | cmovne (dst : String) (src : JOperand)
  | cmovb (dst : String) (src : JOperand)
  /-- `Ox86_MULX_lo_hi_instr`: `(dstLo, dstHi) := (lo, hi)`; no flag. -/
  | mulx (dstHi dstLo : String) (a b : JOperand)
  /-- `Ox86_MULX_lo_hi_instr` with a **memory** second source:
      `(dstLo, dstHi) := wumul (a, [base + off])`; no flag. The implicit src1 is
      `a` (the `%rdx`-pinned multiplier), src2 is read straight from memory
      (`mulxq off(%base), %dstLo, %dstHi`). This is s2n-bignum's fold of the
      multiplicand load into the `MULX`. The semantics is the reg-operand `mulx`
      with the second operand replaced by `mem_read [base + off]` — i.e. the
      `loadMem` read composed with `x86_MULX_lo_hi`, exactly as `arch_sem.v`
      evaluates a `MULX` whose src2 `asm_arg` is an `Addr` rather than a `Reg`. -/
  | mulxMem (dstHi dstLo : String) (a : JOperand) (base : String) (off : Int)
  /-- `Ox86_ADCX_instr`: carry to `CF` only. -/
  | adcx (dst : String) (src : JOperand)
  /-- `Ox86_ADOX_instr`: carry to `OF` only. -/
  | adox (dst : String) (src : JOperand)
  /-- `Ox86_MOV_instr` with a memory **source**: `dst := [base + off]`
      (`movq off(%base), %dst`). The reg-ptr ABI's argument-load. No flag. -/
  | loadMem (dst : String) (base : String) (off : Int)
  /-- `Ox86_MOV_instr` with a memory **destination**: `[base + off] := src`
      (`movq %src, off(%base)`). The reg-ptr ABI's result-store. No flag. -/
  | storeMem (base : String) (off : Int) (src : JOperand)
  /-- `Ox86_MOV_instr` with a **register-indexed** memory source:
      `dst := [base + idx·scale]` (`movq (%base, %idx, scale), %dst`). The
      gather form of `loadMem` for a `m[row*AC + col]` matrix cell whose flat
      offset lives in an index register. No flag. -/
  | loadMemIdx (dst base idx : String) (scale : Nat)
  /-- `Ox86_MOV_instr` with a **register-indexed** memory destination:
      `[base + idx·scale] := src` (`movq %src, (%base, %idx, scale)`). The
      scatter form of `storeMem`. No flag. -/
  | storeMemIdx (base idx : String) (scale : Nat) (src : JOperand)
  /-- `Ox86_LEA_instr` of a **named `.rodata` symbol**, RIP-relative:
      `dst := &sym` (`leaq sym(%rip), %dst`). This loads the *address* of the
      read-only global table `sym` (emitted in the `.rodata` section by
      `LprogAsmPrinter.renderRodata` from `Lprog.lp_globs`/`lp_glob_names`) into a
      base register, so the indexed-load arm `loadMemIdx dst sym i scale` can then
      gather `sym[i]` — the NTT twiddle-table access. This is the missing
      symbol-base primitive: prior `LEA` only took a register-base displacement
      (`mem.<base>.<off>` in the Lprog path), never a `.rodata` symbol.

      **Model (faithful to the gas semantics, KAT-checkable).** The table lives in
      the machine memory under the *symbol-name* memory bank `s.mem sym ·`. The
      `leaq sym(%rip), %dst` makes the base register `dst` point at that table; we
      model that by *aliasing the destination register's memory bank onto the
      symbol's bank* (`mem dst o := mem sym o`) and writing the register a marker
      address. A subsequent `loadMemIdx dst' dst i scale` (keyed by the base
      register *name* `dst`) then reads `s.mem dst (scale·i) = s.mem sym (scale·i)`
      — exactly `sym[i]`. Seeding `s.mem sym ·` with the table values gives a real
      in-Lean value KAT of `dst := &sym; out := sym[i]`. (What is trusted to the
      orchestrator's assemble+run KAT: that `gas`/`ld` resolve `leaq sym(%rip)` to
      the address of the `.rodata` `sym:` block, and that the hardware SIB load
      reads the table — the same RIP-relative-addressing + PIE/PIC trust every
      `.rodata` access carries.) -/
  | loadSym (dst sym : String)
  deriving Repr

/-- `eval_op`/`exec_instr_op` for one instruction (`arch_sem.v` l.386–391):
    evaluate the operands, apply the `x86_*` semantic function, write the result
    tuple back over the instruction's `id_out` list. For each arm the write list
    matches the corresponding `Ox86_*_instr` output operand list. -/
def evalInstr {w : Nat} (s : JState w) : JInstr w → JState w
  | .mov dst src  => s.setReg dst (x86_MOV (src.eval s))
  | .add dst src  => s.writeB5W dst (x86_ADD (s.get dst) (src.eval s))
  | .sub dst src  => s.writeB5W dst (x86_SUB (s.get dst) (src.eval s))
  | .adc dst src  => s.writeB5W dst (x86_ADC (s.get dst) (src.eval s) (s.flagB (·.cf)))
  | .sbb dst src  => s.writeB5W dst (x86_SBB (s.get dst) (src.eval s) (s.flagB (·.cf)))
  | .imul dst src => s.writeB5W dst (x86_IMULt (s.get dst) (src.eval s))
  | .neg dst      => s.writeB5W dst (x86_NEG (s.get dst))
  | .setc dst     => s.setReg dst (if s.flagB (·.cf) then 1 else 0)
  | .and_ dst src => s.writeB5W dst (x86_AND (s.get dst) (src.eval s))
  | .test a b     => s.writeB5 (x86_TEST (s.get a) (b.eval s))
  | .cmp a b      => s.writeB5 (x86_CMP (s.get a) (b.eval s))
  | .not_ dst     => s.setReg dst (x86_NOT (s.get dst))
  | .andn d a b   => s.writeB5W d (x86_ANDN (s.get a) (s.get b))
  | .rol dst amt  => s.writeB2W dst (x86_ROL (s.get dst) (amt.eval s))
  | .ror dst amt  => s.writeB2W dst (x86_ROR (s.get dst) (amt.eval s))
  | .rorx d src amt => s.setReg d (x86_RORX (s.get src) (amt.eval s))
  | .shlx d src c => s.setReg d (x86_SHLX (s.get src) (s.get c))
  | .shrx d src c => s.setReg d (x86_SHRX (s.get src) (s.get c))
  | .sarx d src c => s.setReg d (x86_SARX (s.get src) (s.get c))
  | .movzx d sw src => s.setReg d (x86_MOVZX sw (s.get src))
  | .movsx d sw src => s.setReg d (x86_MOVSX sw (s.get src))
  | .lea d base idx scale off =>
      s.setReg d (x86_LEA (s.get base + (s.get idx) * BitVec.ofNat _ scale
        + BitVec.ofInt _ off))
  | .or_ dst src  => s.writeB5W dst (x86_OR (s.get dst) (src.eval s))
  | .xor_ dst src => s.writeB5W dst (x86_XOR (s.get dst) (src.eval s))
  | .shl dst src  => s.writeB5W dst (x86_SHL (s.get dst) (src.eval s))
  | .shr dst src  => s.writeB5W dst (x86_SHR (s.get dst) (src.eval s))
  | .sar dst src  => s.writeB5W dst (x86_SAR (s.get dst) (src.eval s))
  | .cmove dst src  => s.setReg dst (x86_CMOVcc (s.flagB (·.zf)) (src.eval s) (s.get dst))
  | .cmovne dst src => s.setReg dst (x86_CMOVcc (! s.flagB (·.zf)) (src.eval s) (s.get dst))
  | .cmovb dst src  => s.setReg dst (x86_CMOVcc (s.flagB (·.cf)) (src.eval s) (s.get dst))
  | .mulx dstHi dstLo a b =>
      let (lo, hi) := x86_MULX_lo_hi (a.eval s) (b.eval s)
      -- output list [Eu 1 (= dstLo); Eu 0 (= dstHi)], no flags written
      (s.setReg dstLo lo).setReg dstHi hi
  | .mulxMem dstHi dstLo a base off =>
      -- src2 read from memory (`mem_read [base + off]`), then the same widening
      -- multiply as the reg form: identical to `mulx` with `b.eval s` replaced
      -- by `s.load base off`. No flags written.
      let (lo, hi) := x86_MULX_lo_hi (a.eval s) (s.load base off)
      (s.setReg dstLo lo).setReg dstHi hi
  | .adcx dst src =>
      let (co, res) := x86_ADCX (s.get dst) (src.eval s) (s.flagB (·.cf))
      -- output list [F CF; Ea 0]: write only CF + the data
      { regs := fun r' => if r' = dst then res else s.regs r'
        flags := { s.flags with cf := co }
        mem := s.mem }
  | .adox dst src =>
      let (co, res) := x86_ADCX (s.get dst) (src.eval s) (s.flagB (·.of))
      -- output list [F OF; Ea 0]: write only OF + the data
      { regs := fun r' => if r' = dst then res else s.regs r'
        flags := { s.flags with of := co }
        mem := s.mem }
  | .loadMem dst base off  => s.setReg dst (x86_MOV (s.load base off))
  | .storeMem base off src => s.store base off (x86_MOV (src.eval s))
  | .loadMemIdx dst base idx scale =>
      s.setReg dst (x86_MOV (s.loadIdx base idx scale))
  | .storeMemIdx base idx scale src =>
      s.storeIdx base idx scale (x86_MOV (src.eval s))
  | .loadSym dst sym =>
      -- `leaq sym(%rip), %dst`: the base register `dst` now points at the
      -- `.rodata` table `sym`. Model: alias `dst`'s memory bank onto `sym`'s
      -- (so a later `loadMemIdx _ dst i scale` reads `sym[scale·i]`), and write a
      -- nonzero marker address into the register itself (the symbolic table base;
      -- its concrete value is the linker's, irrelevant to the indexed read which
      -- is keyed by the base register *name*).
      { regs := fun r' => if r' = dst then BitVec.ofNat w 1 else s.regs r'
        flags := s.flags
        mem := fun b o => if b = dst then s.mem sym o else s.mem b o }

/-- `runBlock`: a straight-line fold of `evalInstr`, the analogue of jasmin's
    sequential `lsem`/`eval_instr` iteration over a basic block. -/
def runBlock {w : Nat} (s : JState w) : List (JInstr w) → JState w
  | [] => s
  | i :: is => runBlock (evalInstr s i) is

@[simp] theorem runBlock_nil {w : Nat} (s : JState w) : runBlock s [] = s := rfl

@[simp] theorem runBlock_cons {w : Nat} (s : JState w) (i : JInstr w)
    (is : List (JInstr w)) : runBlock s (i :: is) = runBlock (evalInstr s i) is := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
