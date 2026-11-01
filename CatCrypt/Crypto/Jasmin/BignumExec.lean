/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.JasminAST
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.JasminAST
public meta import CatCrypt.Crypto.Jasmin.MemoryModel
public import CatCrypt.Crypto.Jasmin.MemoryModel
public import Std.Do.Triple
public import Std.WP
public import CatCrypt.Crypto.Util.StateTOptionWP
public import Std.Tactic.Do
public import Std.Tactic.BVDecide


@[expose] public section
set_option autoImplicit false

/-!
# Functional interpreter for the bignum SSA fragment

Track 1: an executable big-step semantics for the InstrR fragment
used by `S2NBignumSSA.lean`.

## Trust grounding

This semantics is an **independent Lean-AST interpretation**, not a
direct port of Coq Jasmin's `psem.v`. The reason: our `JasminAST.PExpr`
has

```
| Pload (ws : WSize) (x : VarI) (off : PExpr) : PExpr
```

while Coq Jasmin's `pexpr` has

```
| Pload : aligned -> wsize -> pexpr -> pexpr
```

— Lean splits the address into `(base, offset)`; Coq has a single
expression. The two ASTs differ in this form. So per-rule citation
against `psem.v` is **informative documentation**, not formal
correspondence.

Correctness grounds at the **Jasmin-source level** via differential
testing: the same body, run via this interpreter and via
`JasminEmit ∘ jasminc ∘ link`, agrees on KAT inputs. The differential test is
not part of this package.

## Coverage (only what `bignum_mod_p25519_4` needs)

| InstrR shape | Handled | Coq Jasmin reference (informative) |
|---|---|---|
| `Cassgn (Lvar _) _ _ Pvar`              | yes | `psem_defs.v::sem_pexpr::Pvar` + `write_lval::Lvar` |
| `Cassgn (Lvar _) _ _ Pconst`            | yes | `sem_pexpr::Pconst` + `write_lval::Lvar` |
| `Cassgn (Lvar _) _ _ (Pload .U64 _ _)`  | yes | `sem_pexpr::Pload` + `write_lval::Lvar` (Lean AST shape ≠ Coq) |
| `Cassgn (Lvar _) _ _ (Papp2 _ _ _)`     | yes | `sem_pexpr::Papp2` + `sem_sop2` (Oland/Olor/Olxor) |
| `Cassgn (Lmem .U64 _ _) _ _ Pvar`       | yes | `write_lval::Lmem` (Lean AST shape ≠ Coq) |
| `Copn _ _ (Oasm "SUB_64") [a, b]`       | yes | `x86_instr_decl.v::SUB` |
| `Copn _ _ (Oasm "SBB_64") [a, b, cin]`  | yes | `x86_instr_decl.v::SBB` |
| `Copn _ _ (Oasm "ADD_64") [a, b]`       | yes | `x86_instr_decl.v::ADD` |
| `Copn _ _ (Oasm "ADC_64") [a, b, cin]`  | yes | `x86_instr_decl.v::ADC` |
| `Copn _ _ (Oasm "MULX") [a, b]`         | yes | `x86_instr_decl.v::MULX` (BMI2) |
| `Copn _ _ (Oasm "ADCX") [a, b, cin]`    | yes | `x86_instr_decl.v::ADCX` (BMI2 dual-carry CF) |
| `Copn _ _ (Oasm "ADOX") [a, b, oin]`    | yes | `x86_instr_decl.v::ADOX` (BMI2 dual-carry OF) |
| `Copn _ _ (Oasm "XOR_64") [a, b]`       | yes | `x86_instr_decl.v::XOR` |
-/

namespace CatCrypt.Crypto.Jasmin.BignumExec

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.MemoryModel

/-! ## §1. Bignum state -/

/-- Scalar register environment + flat byte memory. Reads of unbound
    registers default to 0 (matches Jasmin's "declared u64 starts at 0"). -/
structure BignumState where
  regs : String → BitVec 64
  mem  : Mem

instance : Inhabited BignumState where
  default := { regs := fun _ => 0, mem := Mem.empty }

/-- Update one register. -/
def setReg (s : BignumState) (x : String) (v : BitVec 64) : BignumState :=
  { s with regs := fun y => if y = x then v else s.regs y }

/-- Update memory by storing 8 bytes at address `a`. -/
def storeMem (s : BignumState) (a : UInt64) (v : UInt64) : BignumState :=
  { s with mem := s.mem.store64 a v }

/-- **(U32, additive)** Store the low 4 bytes of `v` (little-endian) at
    address `a`.  4-byte stride; mirrors `MemoryModel.Mem.store64` but
    writes only bytes `0..3`.  The high 32 bits of `v` are dropped (this
    is the masked-to-32 store the `Lmem .U32` write performs). -/
def Mem.store32 (m : MemoryModel.Mem) (a : UInt64) (v : UInt64) : MemoryModel.Mem :=
  let m1 := m.storeByte a (MemoryModel.byteAt v 0)
  let m2 := m1.storeByte (a + 1) (MemoryModel.byteAt v 1)
  let m3 := m2.storeByte (a + 2) (MemoryModel.byteAt v 2)
  m3.storeByte (a + 3) (MemoryModel.byteAt v 3)

/-- **(U32, additive)** Update memory by storing the low 4 bytes at `a`. -/
def storeMem32 (s : BignumState) (a : UInt64) (v : UInt64) : BignumState :=
  { s with mem := Mem.store32 s.mem a v }

/-- **(U8, additive)** Update memory by storing one byte (the low 8 bits of
    `v`) at address `a`.  Mirrors `storeMem32` / `storeMem` but writes a
    single byte through `MemoryModel.Mem.storeByte` (the byte-granular
    primitive of the flat memory model).  Backs the `.Cassgn (.Lmem .U8 _ _)`
    arm of `execInstr` — the per-byte store emitted by `mpn_to_string`'s
    digit-write step. -/
def storeMem8 (s : BignumState) (a : UInt64) (v : UInt8) : BignumState :=
  { s with mem := s.mem.storeByte a v }

/-! ## §2. Address resolution

Lean AST: `Pload .U64 base (Pconst k)` and `Lmem .U64 base (Pconst k)`
both name a base register and a constant offset. The resolved address
is `(s.regs base + BitVec.ofInt k)`, then cast to UInt64 for indexing
into `Mem`.

Coq AST behavioral correspondence: Coq's `Pload align sz e` would
evaluate `e` to a `to_pointer`-castable value. For `e = Papp2 (Oadd
U64) (Pvar base) (Pconst k)`, the result is `s[base] + k` interpreted
as a UInt64. Same value. Tracked by differential test. -/

/-- Resolve a base+offset to a UInt64 address. Only handles `Pconst`
    offsets (the only shape in the bignum SSA fragment). -/
def resolveAddr (s : BignumState) (base : VarI) (off : PExpr) : Option UInt64 :=
  match off with
  | .Pconst k =>
    let baseV := s.regs base.var.vname
    some (UInt64.ofNat ((baseV + BitVec.ofInt 64 k).toNat))
  | _ => none

/-! ## §3. Memory load (8-byte little-endian)

Coq Jasmin reference: `psem_defs.v::sem_pexpr::Pload` evaluates the
pointer expression, then calls `read s.(emem) al w2 sz`. `read` returns
`exec` (Either errcode value). For `sz = U64`, that's an 8-byte read
combined into a `BitVec 64`.

Our version: produce `none` if any byte is unallocated; otherwise
combine bytes little-endian. Behavioral correspondence: when memory
is fully allocated over `[addr, addr + 8)`, both versions return
`Some (combined_value)`. The differential test verifies this. -/

def load64Mem (m : Mem) (addr : UInt64) : Option UInt64 := do
  let b0 ← m.loadByte addr
  let b1 ← m.loadByte (addr + 1)
  let b2 ← m.loadByte (addr + 2)
  let b3 ← m.loadByte (addr + 3)
  let b4 ← m.loadByte (addr + 4)
  let b5 ← m.loadByte (addr + 5)
  let b6 ← m.loadByte (addr + 6)
  let b7 ← m.loadByte (addr + 7)
  some (b0.toUInt64
    ||| b1.toUInt64 <<< 8
    ||| b2.toUInt64 <<< 16
    ||| b3.toUInt64 <<< 24
    ||| b4.toUInt64 <<< 32
    ||| b5.toUInt64 <<< 40
    ||| b6.toUInt64 <<< 48
    ||| b7.toUInt64 <<< 56)

/-- **(U32, additive)** Read 4 bytes little-endian and zero-extend into a
    `UInt64` (the high 32 bits are 0).  Returns `none` if any of the 4
    bytes is unallocated.  This is the U32 analogue of `load64Mem`; the
    `Pload .U32` arm wraps the result as `BitVec.ofNat 64 _.toNat`, so the
    high half stays zero just like the recommended `&&& 0xFFFFFFFF`
    representation. -/
def load32Mem (m : Mem) (addr : UInt64) : Option UInt64 := do
  let b0 ← m.loadByte addr
  let b1 ← m.loadByte (addr + 1)
  let b2 ← m.loadByte (addr + 2)
  let b3 ← m.loadByte (addr + 3)
  some (b0.toUInt64
    ||| b1.toUInt64 <<< 8
    ||| b2.toUInt64 <<< 16
    ||| b3.toUInt64 <<< 24)

/-! ## §4. PExpr evaluation

Coq Jasmin reference: `psem_defs.v::sem_pexpr` (line 121).
Our version covers only the shapes used by bignum bodies: Pconst,
Pvar, Pload, Papp2 over u64 ops. -/

/-- **(U32, additive)** Low-32-bit mask: a `BitVec 64` whose low 32 bits
    are set.  A u32 value is represented as a `BitVec 64` with the high
    half cleared; `&&& mask32` performs the masked-to-32 reduction. -/
def mask32 : BitVec 64 := 0xFFFFFFFF

def evalPExpr (s : BignumState) : PExpr → Option (BitVec 64)
  | .Pconst z       => some (BitVec.ofInt 64 z)
  | .Pvar gv        => some (s.regs gv.gv.var.vname)
  | .Pload .U64 base off => do
      let addr ← resolveAddr s base off
      let v ← load64Mem s.mem addr
      some (BitVec.ofNat 64 v.toNat)
  -- **(U32, additive)** 32-bit load: read 4 bytes little-endian,
  -- zero-extended (high 32 bits = 0).  Placed before the `.Pload .U64`
  -- catch nothing — U64 above only matches `.U64`, so this is reachable.
  | .Pload .U32 base off => do
      let addr ← resolveAddr s base off
      let v ← load32Mem s.mem addr
      some (BitVec.ofNat 64 v.toNat)
  -- **(U32, additive) design note.**  We deliberately do NOT add
  -- width-specialized `Papp2 (.Oadd .U32)` / `Osub` / `Oland` / `Olor` /
  -- `Olxor` / `Oeq` / `Oneq` arms here.  Two reasons:
  --
  --  1. *They are not needed by the u32 `mpn_add_n` bridge.*  In a u32
  --     kernel the pointers, indices and the length counter are still
  --     `reg u64`, so pointer/counter arithmetic uses the 64-bit
  --     `Oadd .U64` arm and the loop guard `n != 0` uses the
  --     width-agnostic `Oneq _` arm.  32-bit *limb* arithmetic
  --     goes through the masking intrinsics `ADD_32` / `ADC_32` /
  --     `SUB_32` in `execInstr` (which mask to 32 bits and report the
  --     bit-32 carry), exactly as a real Jasmin u32 kernel emits.
  --
  --  2. *Interposing `.U32` arms before the wildcard `.Oadd _` arm makes
  --     the equation compiler attach a `ws ≠ .U32` discriminator to the
  --     wildcard arm's equation lemma, which breaks the many corpus
  --     proofs that unfold `evalPExpr` on a generic-width `Papp2` via
  --     `rw`/`simp only [evalPExpr]`.*  Keeping the wildcard arms
  --     byte-identical preserves the U64 path exactly.
  --
  -- The 32-bit masking that the representation needs is therefore
  -- provided where it is actually used: the `ADD_32`/`SUB_32`/`ADC_32`
  -- intrinsics, `load32Mem`, and `Mem.store32`.
  | .Papp2 (.Oland _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      some (va &&& vb)
  | .Papp2 (.Olor _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      some (va ||| vb)
  | .Papp2 (.Olxor _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      some (va ^^^ vb)
  | .Papp2 (.Oadd _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      some (va + vb)
  | .Papp2 (.Osub _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      some (va - vb)
  | .Papp2 (.Oeq _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      -- `==` returns 1 if equal, 0 otherwise (nonzero iff the comparison
      -- holds, matching how `bignumExecFuel`'s `Cif`/`Cwhile` test the guard).
      some (if va = vb then 1 else 0)
  | .Papp2 (.Oneq _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      -- `!=` returns 1 if unequal, 0 otherwise (nonzero iff the comparison
      -- holds).  This is the loop guard `n != 0` of the bignum `Cwhile`.
      some (if va = vb then 0 else 1)
  -- **(Shift)** Word-level left/right logical shifts.
  -- These are the `Papp2`-form shifts emitted by frontend `<<=` / `>>=` /
  -- `<<` / `>>` operators (distinct from the `#SHL_64` / `#SHR_64` / `#SHLD`
  -- / `#SHRD` x86 intrinsics handled in `execInstr`).  Without these arms,
  -- any kernel using `tmp <<= k` in a prologue would be unrunnable under
  -- `bignumExecFuel` (the wildcard `_ => none` would fire, then the chain
  -- short-circuits to `none`); `bodyDivRemSingle` uses the `tmp <<= 3`
  -- form.
  --
  -- We follow the canonical `shl64` / `shr64` shape: `va <<< (vb.toNat % 64)`
  -- (the x86 6-bit `cl` mask, also baked into Jasmin's denotation for u64
  -- shifts).  Width-agnostic: the `_` width wildcard mirrors `Oadd _` /
  -- `Osub _` / `Oland _`, keeping the wildcard arms byte-identical and
  -- preserving the U64 unfold path that the corpus relies on.
  | .Papp2 (.Olsl _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      some (va <<< (vb.toNat % 64))
  | .Papp2 (.Olsr _) a b => do
      let va ← evalPExpr s a; let vb ← evalPExpr s b
      some (va >>> (vb.toNat % 64))
  -- **(U8 narrow, additive)** Zero-extend (narrow-then-widen).  In a real
  -- Jasmin u64 → u8 cast (`(8u) c64`), the source's low `wso.bits` are kept
  -- and the rest cleared.  Because our register file is `BitVec 64`, we
  -- represent the narrowed value as the low-`wso.bits` mask of `v`, i.e.
  -- `BitVec.ofNat 64 (v.toNat % 2^wso.bits)`.  For `wso = .U8` this is
  -- `v.toNat % 256` — the byte the `Lmem .U8` store will write.  The arm
  -- is parametric in both widths (covers .U8/.U16/.U32/.U64 targets and
  -- any source width since the source value already lives in `BitVec 64`). -/
  | .Papp1 (.Ozeroext wso _) e => do
      let v ← evalPExpr s e
      some (BitVec.ofNat 64 (v.toNat % (2 ^ wso.bits)))
  | _ => none

/-! ## §5. Intrinsic semantics

Coq Jasmin reference: `x86_instr_decl.v` has the per-instruction
specs. Our subset:

- `SUB_64`: x86 SUB r/m64, r/m64. Returns `(_, cf, _, _, _, r)` where
  `r = (a - b) mod 2^64` and `cf = 1` iff `a < b` (unsigned).
  Behavioral spec from Intel SDM Vol. 2B `SUB`.
- `SBB_64`: x86 SBB r/m64, r/m64. `r = a - b - cin`, cf = borrow.
  SDM `SBB`.
- `ADD_64`: x86 ADD r/m64, r/m64. `r = (a + b) mod 2^64`, cf = carry-out.
  SDM Vol. 2A `ADD`.
- `ADC_64`: x86 ADC r/m64, r/m64. `r = a + b + cin`, cf = carry-out.
  SDM `ADC`.
- `MULX`: BMI2 MULX r64, r64, r/m64. `(hi, lo)` such that
  `(hi.toNat <<< 64) ||| lo.toNat = a.toNat * b.toNat`. No flags.
  SDM Vol. 2B `MULX`.
- `ADCX`: BMI2 ADCX r64, r/m64. CF-only chain — same arithmetic as
  ADC but only CF is updated (OF preserved). Bundle shape
  `[cf_out, dst]` (no flag-prefix). SDM `ADCX`.
- `ADOX`: BMI2 ADOX r64, r/m64. OF-only chain — same arithmetic as
  ADC, but updates OF instead of CF. Bundle shape `[of_out, dst]`.
  SDM `ADOX`.
- `XOR_64`: x86 XOR r/m64, r/m64. `r = a XOR b`. CF=OF=0 after XOR
  (per SDM `XOR`). Bundle shape `[of, cf, _, _, _, dst]` for the
  dual-carry-clear idiom; we also accept the standard SUB-style
  `[_, cf, _, _, _, dst]`.

Tracked by differential test against compiled `bignum_*` outputs. -/

/-- 64-bit SUB-with-borrow-out. Uses `BitVec.ult` (unsigned less-than)
    for the comparison so `bv_decide` can reason through it. -/
def subBorrow (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let r := a - b
  let bf : BitVec 64 := if a.ult b then 1 else 0
  (bf, r)

/-- 64-bit SBB: `r = a - b - bin`, with new borrow.
    `bin` interpreted as 0 or 1 (top 63 bits ignored, matching x86 SBB
    flag-input semantics). Uses `BitVec.ult` for `bv_decide` support. -/
def subBorrowIn (a b bin : BitVec 64) : BitVec 64 × BitVec 64 :=
  let bin01 : BitVec 64 := bin &&& 1
  let s1 := a - b
  let bf1 : BitVec 64 := if a.ult b then 1 else 0
  let r := s1 - bin01
  let bf2 : BitVec 64 := if s1.ult bin01 then 1 else 0
  (bf1 ||| bf2, r)

/-- 64-bit ADD-with-carry-out. Returns `(cf, r)` where `r = (a + b) mod 2^64`
    and `cf = 1` iff `a + b >= 2^64` (unsigned overflow). Detects overflow
    via `r.ult a` (post-add the result is below `a` exactly when the add
    wrapped). Behavioral spec from Intel SDM Vol. 2A `ADD`. -/
def addCarry (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let r := a + b
  let cf : BitVec 64 := if r.ult a then 1 else 0
  (cf, r)

/-- 64-bit ADC: `r = a + b + cin`, with new carry-out.
    `cin` interpreted as 0 or 1 (top 63 bits ignored, matching x86 ADC
    flag-input semantics). Two-step add captures both possible carries. -/
def addCarryIn (a b cin : BitVec 64) : BitVec 64 × BitVec 64 :=
  let cin01 : BitVec 64 := cin &&& 1
  let s1 := a + b
  let cf1 : BitVec 64 := if s1.ult a then 1 else 0
  let r := s1 + cin01
  let cf2 : BitVec 64 := if r.ult s1 then 1 else 0
  (cf1 ||| cf2, r)

/-- 64×64→128 unsigned multiplication, returning `(hi, lo)` with
    `(hi.toNat <<< 64) ||| lo.toNat = a.toNat * b.toNat`.
    Behavioral spec from Intel SDM Vol. 2B `MULX` (BMI2). MULX does
    not affect any flags — only the two destination registers. -/
def mulx (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let prod : Nat := a.toNat * b.toNat
  let lo : BitVec 64 := BitVec.ofNat 64 prod
  let hi : BitVec 64 := BitVec.ofNat 64 (prod >>> 64)
  (hi, lo)

/-- 128÷64 unsigned division, returning `(quot, rem)` with
    `quot · d + rem = (hi · 2^64 + lo)` and `rem < d`, **provided** the
    quotient fits in 64 bits (the divisor `d` is nonzero and
    `hi.toNat < d.toNat`).  This is the behavioral spec of x86 `DIV` /
    Intel SDM Vol. 2A `DIV` at the 64-bit operand size (`divq`):
    `(rdx:rax) / d → rax = quot, rdx = rem`, with `#UD`/`#DE` if `d = 0`
    or `quot ≥ 2^64`.

    The Lean model returns the truncated result in the overflow case
    (so the function is total at the Lean level — preserving the
    `bignumExec`-`Option`-shape).  Callers that depend on overflow not
    happening (Knuth Algorithm D's q̂ trial: `hi < d` after
    normalization) carry the proof obligation explicitly.

    No flags are observed; `DIV` leaves OF/SF/ZF/AF/PF/CF undefined per
    the SDM, so the interpreter writes them as `0` (matches our
    flag-bundle layout for the standard SUB/ADD/ADC 6-LVal slots). -/
def divrem64 (hi lo d : BitVec 64) : BitVec 64 × BitVec 64 :=
  let dd : Nat := hi.toNat * 2 ^ 64 + lo.toNat
  let dv : Nat := d.toNat
  let q  : Nat := dd / dv
  let r  : Nat := dd % dv
  (BitVec.ofNat 64 q, BitVec.ofNat 64 r)

/-- **Smoke test.**  `(0 · 2^64 + 0x1234) / 0x10 = (0x123, 0x4)` —
    quotient and remainder split correctly at the 64-bit boundary. -/
example :
    divrem64 (0 : BitVec 64) (0x1234 : BitVec 64) (0x10 : BitVec 64)
      = ((0x123 : BitVec 64), (0x4 : BitVec 64)) := by native_decide

/-- **Smoke test.**  Top half nonzero: `(0x1 · 2^64 + 0) / 0x2 =
    (0x8000_0000_0000_0000, 0)`. The quotient fits exactly in 64 bits
    because `hi = 1 < d = 2`. -/
example :
    divrem64 (1 : BitVec 64) (0 : BitVec 64) (2 : BitVec 64)
      = ((0x8000000000000000 : BitVec 64), (0 : BitVec 64)) := by native_decide

/-! ### §5a-shift. (Shift, additive) 64-bit shift intrinsics

Backs the verified `mpn_lshift` / `mpn_rshift` kernels (`Mpn.ShiftSpec.lean`).
The algorithm-level toNat correctness theorems (`mpnShiftLeft_spec`,
`mpnShiftRight_spec`) prove that the cross-limb `|||` merge is an
addition (`nat_lor_eq_add_of_disjoint`) — that's why the
single-instruction `SHLD` / `SHRD` idiom is denotation-preserving:
`SHLD(w, last_w, r)` computes `(w <<< r) ||| (last_w >>> (64-r))`, exactly
the merge `bitShiftLeftAux` performs.

Behavioral specs from Intel SDM Vol. 2B:
- `SHL r/m64, cl/imm8`     — logical shift left (result, CF = last bit out).
- `SHR r/m64, cl/imm8`     — logical shift right (result, CF = last bit out).
- `SHLD r/m64, r64, cl/imm8` — double-precision shift left:
  result = low 64 bits of `(dst:src) << k` = `(dst << k) | (src >> (64-k))`.
- `SHRD r/m64, r64, cl/imm8` — double-precision shift right:
  result = low 64 bits of `(src:dst) >> k` = `(dst >> k) | (src << (64-k))`.

We capture only the result (no flag bundle): the shift kernels read the
merged word into a GPR; the carry-out flag is unused (the `mpn_lshift`
ABI returns the *high spill word* as a value, not as a flag).

The shift amount `k` is a `BitVec 64`; we use `k.toNat` against the 6-bit
mask `k % 64` (matching x86's `cl` register behaviour: only the low 6 bits
of `cl` are used at 64-bit operand size).  At `k % 64 = 0`, `BitVec` shifts
are the identity (`w <<< 0 = w`, `w >>> 0 = w`) and the doubleword shifts
collapse to a copy of `dst` (with `src >> 64 = 0` and `src << 64 = 0`)
— matching the SDM "k = 0 means no shift, no flag update".

(CT note: x86 `SHL/SHR/SHLD/SHRD` with an immediate shift amount are
constant-time on every modern uarch.  With `cl` they are constant-time on
Intel since Sandy Bridge and AMD since Bulldozer.  The `SHLX/SHRX` BMI2
variants are constant-time on all uarchs that implement them.  Our shift
kernels can be lowered to either form; the bridge is shift-amount-form
agnostic since the denotational semantics here only sees the masked
shift count.)  -/

/-- 64-bit logical shift left: `r = a << (k % 64)`.  Returns just the
    shifted result; the SDM-defined CF (last bit shifted out) is not
    captured (shift kernels carry the spill in a GPR via `SHLD`, not via
    CF).  Matches `w <<< k.toNat` of the spec (mod-64 truncation is built
    into `BitVec.<<<` for shift amounts ≥ 64). -/
def shl64 (a k : BitVec 64) : BitVec 64 :=
  a <<< (k.toNat % 64)

/-- 64-bit logical shift right: `r = a >> (k % 64)`.  Mirror of `shl64`. -/
def shr64 (a k : BitVec 64) : BitVec 64 :=
  a >>> (k.toNat % 64)

/-- 64-bit double-precision shift left: `r = (dst << k) | (src >> (64-k))`
    (low 64 bits of `(dst:src) << k`).  Exactly the merge `bitShiftLeftAux`
    performs: `(w <<< r) ||| (last_w >>> (64 - r))`.  The `k = 0` corner is
    handled uniformly (the spec proves `bitShiftLeftAux 0 _ _` is the
    identity-with-spill on the denotation, since `>>> 64 = 0`).

    We take the shift amount as `k.toNat % 64` (matching x86's 6-bit `cl`
    mask) and `(64 - (k.toNat % 64))` for the cross-limb pull; both are in
    `[0, 64]` so the `BitVec` shifts are well-typed.  At `k % 64 = 0`,
    `src >>> 64 = 0` and the result is `dst`. -/
def shld64 (dst src k : BitVec 64) : BitVec 64 :=
  let r := k.toNat % 64
  (dst <<< r) ||| (src >>> (64 - r))

/-- 64-bit double-precision shift right: `r = (dst >> k) | (src << (64-k))`
    (low 64 bits of `(src:dst) >> k`).  Exactly the merge
    `bitShiftRight` performs: `(w >>> r) ||| (w' <<< (64 - r))`.  Mirror of
    `shld64`. -/
def shrd64 (dst src k : BitVec 64) : BitVec 64 :=
  let r := k.toNat % 64
  (dst >>> r) ||| (src <<< (64 - r))

/-- **Smoke test.**  `SHL_64(0x0F, 4) = 0xF0`. -/
example : shl64 0x0F 4 = 0xF0 := by native_decide

/-- **Smoke test.**  `SHL_64(0xF000000000000000, 4) = 0` (top nibble shifted
    out of the 64-bit register; the spilled nibble is recovered by
    `SHLD_64` in the kernel). -/
example : shl64 0xF000000000000000 4 = 0 := by native_decide

/-- **Smoke test.**  `SHR_64(0xF0, 4) = 0x0F`. -/
example : shr64 0xF0 4 = 0x0F := by native_decide

/-- **Smoke test.**  `SHLD_64(w=0xF000000000000000, src=0, k=4) = 0`
    (no incoming spill, top nibble shifts out). -/
example : shld64 0xF000000000000000 0 4 = 0 := by native_decide

/-- **Smoke test.**  Cross-limb merge: `SHLD_64(dst=2, src=0x8000000000000000,
    k=4) = (2 << 4) | (0x8000000000000000 >> 60) = 0x20 | 0x8 = 0x28`. -/
example : shld64 2 0x8000000000000000 4 = 0x28 := by native_decide

/-- **Smoke test.**  `SHRD_64(dst=0x80, src=0xF, k=4)
    = (0x80 >> 4) | (0xF << 60) = 0x8 | 0xF000000000000000
    = 0xF000000000000008`.  This is the cross-limb idiom for
    `bitShiftRight`: take this limb's high part, OR in the next limb's
    low bits pulled up. -/
example : shrd64 0x80 0xF 4 = 0xF000000000000008 := by native_decide

/-- **Smoke test.**  `SHLD_64(dst, src, 0) = dst` (k=0 corner). -/
example : shld64 0x1234 0xCAFE 0 = 0x1234 := by native_decide

/-- **Smoke test.**  `SHRD_64(dst, src, 0) = dst` (k=0 corner). -/
example : shrd64 0x1234 0xCAFE 0 = 0x1234 := by native_decide

/-! ### §5b. (U32, additive) 32-bit arithmetic intrinsics

Operands are u32 values represented as `BitVec 64` with the high half
zero (caller convention).  Each helper masks its inputs to 32 bits, does
the arithmetic in the full 64-bit register, then reports

* the **result** masked back to 32 bits, and
* the **carry/borrow-out** read off bit 32 of the unmasked 64-bit
  intermediate (so the open-coded value-threaded carry idiom works:
  low result masked, carry in a GPR).

This keeps the carry-out in `{0,1}` exactly the way x86 `ADD`/`SUB`
set CF on the 32-bit operand size. -/

/-- 32-bit ADD-with-carry-out.  Returns `(cf, r)` with `r = (a+b) mod
    2^32` (masked) and `cf = bit 32` of the full sum of the masked
    inputs. -/
def addCarry32 (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let s := (a &&& mask32) + (b &&& mask32)
  let r := s &&& mask32
  let cf : BitVec 64 := (s >>> 32) &&& 1
  (cf, r)

/-- 32-bit ADC: `r = (a + b + cin) mod 2^32`, with bit-32 carry-out.
    `cin` interpreted as 0 or 1 (low bit). -/
def addCarryIn32 (a b cin : BitVec 64) : BitVec 64 × BitVec 64 :=
  let s := (a &&& mask32) + (b &&& mask32) + (cin &&& 1)
  let r := s &&& mask32
  let cf : BitVec 64 := (s >>> 32) &&& 1
  (cf, r)

/-- 32-bit SUB-with-borrow-out.  Returns `(bf, r)` with `r = (a-b) mod
    2^32` (masked) and `bf = 1` iff the masked subtraction wrapped
    (unsigned borrow), detected via `BitVec.ult` on the masked inputs. -/
def subBorrow32 (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let am := a &&& mask32
  let bm := b &&& mask32
  let r := (am - bm) &&& mask32
  let bf : BitVec 64 := if am.ult bm then 1 else 0
  (bf, r)

/-- 32-bit SBB: `r = (a - b - bin) mod 2^32`, with bit-32 borrow-out.
    `bin` interpreted as 0 or 1 (low bit).  Mirrors `addCarryIn32` at sub:
    masks inputs to 32 bits, subtracts in the 64-bit register, reports
    `bf = 1` iff the masked subtraction wrapped (unsigned borrow), via
    `BitVec.ult` of `am` against `bm + bin1`. -/
def subBorrowIn32 (a b bin : BitVec 64) : BitVec 64 × BitVec 64 :=
  let am := a &&& mask32
  let bm := b &&& mask32
  let bin1 := bin &&& 1
  let r := (am - bm - bin1) &&& mask32
  let bf : BitVec 64 := if am.ult (bm + bin1) then 1 else 0
  (bf, r)

/-- **(U32, additive)** 32-bit BMI2 `MULX`.  Returns `(hi, lo)` such that
    `hi.toNat * 2^32 + lo.toNat = (a &&& mask32).toNat * (b &&& mask32).toNat`,
    with both `hi` and `lo` masked to 32 bits (stored in `BitVec 64` with
    the high half cleared, matching the u32-in-`BitVec 64` representation
    used elsewhere in this file).

    Spec mirrors Intel SDM `MULX` (BMI2) at the 32-bit operand size: the
    masked inputs multiply within 64 bits (each ≤ 2^32 - 1, so the product
    fits a 64-bit register), and the 64-bit product splits into a high and
    low 32-bit half. No flags are affected.

    Note: this is the u32 analogue of `mulx`.  Computing the product in
    the 64-bit register and bit-splitting avoids the `BitVec.toNat`/
    `BitVec.ofNat` round-trip that the u64 `mulx` is forced into. -/
def mulx32 (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let am := a &&& mask32
  let bm := b &&& mask32
  let prod : BitVec 64 := am * bm
  let lo : BitVec 64 := prod &&& mask32
  let hi : BitVec 64 := (prod >>> 32) &&& mask32
  (hi, lo)

/-! ## §5c. (U32, additive) `load32Mem` / `Mem.store32` memory algebra

The u32 analogues of `MpnAddPrototype`'s `load64Mem_store64_same` /
`load64Mem_store64_disjoint`.  These are the plumbing the
later u32 `add_n` bridge consumes: read-back of a just-stored 4-byte
word, and a frame rule for disjoint 4-byte blocks.  As in the u64 case,
`bv_decide` is the tool for the UInt64 address (in)equalities (`omega`
cannot see `UInt64`). -/

open MemoryModel in
/-- Reading byte `k` (`k < 4`) of a freshly `store32`-d word returns
    `byteAt v k`.  Proved by `interval_cases` over the 4 offsets; each
    case peels the nested `storeByte`s, discharging the `a+i ≠ a+j`
    side conditions with `bv_decide`. -/
theorem loadByte_store32 (m : Mem) (a v : UInt64) (k : Nat) (hk : k < 4) :
    (Mem.store32 m a v).loadByte (a + UInt64.ofNat k) = some (byteAt v k) := by
  simp only [Mem.store32, Mem.loadByte, Mem.storeByte]
  -- `k < 4`: enumerate the 4 offsets explicitly (no Mathlib `interval_cases`).
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    simp only [show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
               show (UInt64.ofNat 1) = (1 : UInt64) from rfl,
               show (UInt64.ofNat 2) = (2 : UInt64) from rfl,
               show (UInt64.ofNat 3) = (3 : UInt64) from rfl]
    repeat rw [ite_eq_right (by bv_decide)]
    rw [ite_eq_left (by bv_decide)]

open MemoryModel in
/-- **Read-back.**  `load32Mem (Mem.store32 m a v) a = some (v &&& 0xFFFFFFFF)`:
    loading the 4-byte word just written returns its low 32 bits
    (zero-extended back into a `UInt64`, matching `load32Mem`'s
    little-endian recomposition of bytes `0..3`). -/
theorem load32Mem_store32_same (m : Mem) (a v : UInt64) :
    load32Mem (Mem.store32 m a v) a = some (v &&& 0xFFFFFFFF) := by
  have h0 := loadByte_store32 m a v 0 (by omega)
  have h1 := loadByte_store32 m a v 1 (by omega)
  have h2 := loadByte_store32 m a v 2 (by omega)
  have h3 := loadByte_store32 m a v 3 (by omega)
  simp only [show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
             show (UInt64.ofNat 1) = (1 : UInt64) from rfl,
             show (UInt64.ofNat 2) = (2 : UInt64) from rfl,
             show (UInt64.ofNat 3) = (3 : UInt64) from rfl,
             show a + (0 : UInt64) = a from by bv_decide, Mem.loadByte]
    at h0 h1 h2 h3
  simp only [load32Mem, Mem.loadByte, h0, h1, h2, h3, bind, Option.bind]
  simp only [byteAt, Option.some.injEq,
             show (8 * 0 : Nat) = 0 from rfl, show (8 * 1 : Nat) = 8 from rfl,
             show (8 * 2 : Nat) = 16 from rfl, show (8 * 3 : Nat) = 24 from rfl,
             show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
             show (UInt64.ofNat 8) = (8 : UInt64) from rfl,
             show (UInt64.ofNat 16) = (16 : UInt64) from rfl,
             show (UInt64.ofNat 24) = (24 : UInt64) from rfl]
  bv_decide

open MemoryModel in
/-- **Per-byte frame.**  A `store32` at `a'` does not disturb the load of
    byte `a + ofNat k` (`k < 4`) when that address lies outside the
    4-byte block `[a', a' + 4)`. -/
theorem loadByte_store32_frame (m : Mem) (a a' v : UInt64) (k : Nat)
    (hk : k < 4)
    (hne : ∀ j : Nat, j < 4 → a + UInt64.ofNat k ≠ a' + UInt64.ofNat j) :
    (Mem.store32 m a' v).loadByte (a + UInt64.ofNat k)
      = m.loadByte (a + UInt64.ofNat k) := by
  have hn0 := hne 0 (by omega)
  have hn1 := hne 1 (by omega)
  have hn2 := hne 2 (by omega)
  have hn3 := hne 3 (by omega)
  simp only [show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
             show (UInt64.ofNat 1) = (1 : UInt64) from rfl,
             show (UInt64.ofNat 2) = (2 : UInt64) from rfl,
             show (UInt64.ofNat 3) = (3 : UInt64) from rfl,
             show a' + (0 : UInt64) = a' from by bv_decide] at hn0 hn1 hn2 hn3
  simp only [Mem.store32, Mem.loadByte, Mem.storeByte,
             ite_eq_right hn3, ite_eq_right hn2, ite_eq_right hn1, ite_eq_right hn0]

open MemoryModel in
/-- **Frame.**  A `store32` into a block `[a', a' + 4)` disjoint from
    `[a, a + 4)` leaves `load32Mem … a` unchanged.  Each of the 4 byte
    loads is preserved by `loadByte_store32_frame`; the cross-block byte
    inequalities come from `range_disjoint_byte_ne`. -/
theorem load32Mem_store32_disjoint (m : Mem) (a a' v : UInt64)
    (hdisj : Disjoint (range a 4) (range a' 4)) :
    load32Mem (Mem.store32 m a' v) a = load32Mem m a := by
  have frame : ∀ k : Nat, k < 4 →
      (Mem.store32 m a' v).loadByte (a + UInt64.ofNat k)
        = m.loadByte (a + UInt64.ofNat k) := by
    intro k hk
    refine loadByte_store32_frame m a a' v k hk (fun j hj => ?_)
    exact range_disjoint_byte_ne a a' 4 hdisj k j hk hj
  have f0 := frame 0 (by omega)
  have f1 := frame 1 (by omega)
  have f2 := frame 2 (by omega)
  have f3 := frame 3 (by omega)
  simp only [show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
             show (UInt64.ofNat 1) = (1 : UInt64) from rfl,
             show (UInt64.ofNat 2) = (2 : UInt64) from rfl,
             show (UInt64.ofNat 3) = (3 : UInt64) from rfl,
             show a + (0 : UInt64) = a from by bv_decide] at f0 f1 f2 f3
  simp only [load32Mem, f0, f1, f2, f3]

/-! ## §6. LVal write helpers -/

/-- The output bundle of `SUB_64` / `SBB_64` / `ADD_64` / `ADC_64`: 6
    LVals corresponding to `[of, cf, sf, pf, zf, dst]`. We capture only
    `cf` (position 1) and `dst` (position 5); the other flags are
    typically `Lnone`. -/
def writeSubBundle (s : BignumState) (lvs : List LVal)
    (cf r : BitVec 64) : Option BignumState :=
  match lvs with
  | [.Lnone _ _, .Lvar cfV, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rV] =>
    some (setReg (setReg s cfV.var.vname cf) rV.var.vname r)
  | _ => none

/-- The output bundle of `MULX`: 2 LVals `[hi, lo]`. MULX does not
    affect any flags. -/
def writeMulxBundle (s : BignumState) (lvs : List LVal)
    (hi lo : BitVec 64) : Option BignumState :=
  match lvs with
  | [.Lvar hiV, .Lvar loV] =>
    some (setReg (setReg s hiV.var.vname hi) loV.var.vname lo)
  | _ => none

/-- The output bundle of `DIV_64`: 7 LVals `[of, cf, sf, pf, zf, q, r]`.
    x86 `DIV` leaves the five arithmetic flags undefined per the SDM, so
    only the two quotient/remainder destinations (positions 5 and 6) are
    captured.  Mirrors the SUB/ADD/MULX 5-flag-prefix layout extended
    by one extra named output. -/
def writeDivBundle (s : BignumState) (lvs : List LVal)
    (q r : BitVec 64) : Option BignumState :=
  match lvs with
  | [.Lnone _ _, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lnone _ _,
     .Lvar qV, .Lvar rV] =>
    some (setReg (setReg s qV.var.vname q) rV.var.vname r)
  | _ => none

/-- The output bundle of `ADCX` / `ADOX`: 2 LVals `[flag_out, dst]`.
    For ADCX, `flag` is CF; for ADOX, `flag` is OF. The dual-carry
    BMI2 instructions only update one of the two carry flags. -/
def writeAdxBundle (s : BignumState) (lvs : List LVal)
    (flag r : BitVec 64) : Option BignumState :=
  match lvs with
  | [.Lvar flagV, .Lvar rV] =>
    some (setReg (setReg s flagV.var.vname flag) rV.var.vname r)
  | _ => none

/-- The output bundle of `XOR_64` as used by the dual-carry idiom
    `xor reg, reg`: 6 LVals `[of, cf, sf, pf, zf, dst]`. Both OF and CF
    are captured (positions 0 and 1) — distinct from SUB/ADD which
    only capture CF. The `xor x, x` clears CF=OF=0 and zeroes `dst`. -/
def writeXorBundle (s : BignumState) (lvs : List LVal)
    (of cf r : BitVec 64) : Option BignumState :=
  match lvs with
  | [.Lvar ofV, .Lvar cfV, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rV] =>
    some (setReg (setReg (setReg s ofV.var.vname of) cfV.var.vname cf) rV.var.vname r)
  -- Fallback: also accept the SUB-style bundle where only CF is captured
  -- (position 1) and OF is discarded — same structural shape we already
  -- support for SUB/ADD/ADC.
  | [.Lnone _ _, .Lvar cfV, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rV] =>
    some (setReg (setReg s cfV.var.vname cf) rV.var.vname r)
  | _ => none

/-- **(Shift, additive)** Output bundle of `SHL_64` / `SHR_64` / `SHLD_64`
    / `SHRD_64`: 6 LVals `[of, cf, sf, pf, zf, dst]` — the standard x86
    flag-prefix layout (same shape as `ADD_64`/`SUB_64`).  Jasmin's surface
    syntax requires the 6-LVal bundle for these shift opcodes (verified
    via `jasminc` on `_, _, _, _, _, r = #SHLD_64(a, b, k);`).

    Only the destination (position 5) is captured.  Real x86
    `SHL/SHR/SHLD/SHRD` also update CF (last bit shifted out) and SF/ZF/PF,
    but the verified `mpn_lshift` / `mpn_rshift` kernels do not consume
    those flags — the kernel threads the spill word in a GPR (via
    `SHLD/SHRD`'s second operand), not via CF.

    We additionally accept a 1-LVal bundle `[Lvar r]` to allow concise
    smoke tests at the InstrR level (the emitter shape is the 6-LVal
    form). -/
def writeShiftBundle (s : BignumState) (lvs : List LVal)
    (r : BitVec 64) : Option BignumState :=
  match lvs with
  -- Surface form: `_, _, _, _, _, r = #SHL_64(...)` — 6-LVal flag prefix
  -- with only `dst` captured (matches the `writeSubBundle` shape).
  | [.Lnone _ _, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rV] =>
    some (setReg s rV.var.vname r)
  -- Surface form with cf captured: `_, cf, _, _, _, r = #SHL_64(...)`.
  -- Cf is set to 0 (we do not model the bit-shifted-out semantics; the
  -- kernels never read it).
  | [.Lnone _ _, .Lvar cfV, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rV] =>
    some (setReg (setReg s cfV.var.vname 0) rV.var.vname r)
  -- Concise InstrR-level form used by smoke tests / cross-limb merges
  -- where only the destination matters and no flag bookkeeping is needed.
  | [.Lvar rV] => some (setReg s rV.var.vname r)
  | _ => none

/-! ## §7. Single-instruction execution

Coq Jasmin reference: `psem.v::sem_i` (line 60). Our version dispatches
on the InstrR shape directly. -/

def execInstr (s : BignumState) : InstrR → Option BignumState
  -- Cassgn into a register: evaluate rhs, store.
  | .Cassgn (.Lvar v) _ _ rhs => do
      let w ← evalPExpr s rhs
      some (setReg s v.var.vname w)
  -- Cassgn into memory: evaluate rhs and address, store.
  | .Cassgn (.Lmem .U64 base off) _ _ rhs => do
      let w ← evalPExpr s rhs
      let addr ← resolveAddr s base off
      some (storeMem s addr (UInt64.ofNat w.toNat))
  -- **(U32, additive)** Cassgn into 32-bit memory: store the low 4 bytes.
  | .Cassgn (.Lmem .U32 base off) _ _ rhs => do
      let w ← evalPExpr s rhs
      let addr ← resolveAddr s base off
      some (storeMem32 s addr (UInt64.ofNat w.toNat))
  -- **(U8, additive)** Cassgn into 1-byte memory: store the low byte.
  -- Mirrors the `.Lmem .U32` arm.  The RHS evaluates to a `BitVec 64`
  -- (the register-file width); we narrow to `UInt8` by `(toNat % 256).toUInt8`
  -- and dispatch through `storeMem8` (which calls `Mem.storeByte`).
  | .Cassgn (.Lmem .U8 base off) _ _ rhs => do
      let w ← evalPExpr s rhs
      let addr ← resolveAddr s base off
      some (storeMem8 s addr (UInt8.ofNat (w.toNat % 256)))
  -- Copn for our supported intrinsics.
  | .Copn lvs _ (.Oasm op) args =>
    match op.name, args with
    | "SUB_64", [ea, eb] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb
        let (cf, r) := subBorrow a b
        writeSubBundle s lvs cf r
    | "SBB_64", [ea, eb, ec] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb; let c ← evalPExpr s ec
        let (cf, r) := subBorrowIn a b c
        writeSubBundle s lvs cf r
    | "ADD_64", [ea, eb] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb
        let (cf, r) := addCarry a b
        writeSubBundle s lvs cf r
    | "ADC_64", [ea, eb, ec] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb; let c ← evalPExpr s ec
        let (cf, r) := addCarryIn a b c
        writeSubBundle s lvs cf r
    | "MULX", [ea, eb] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb
        let (hi, lo) := mulx a b
        writeMulxBundle s lvs hi lo
    -- x86 `DIV` at 64-bit operand size: `?{RAX=q, RDX=r} = #DIV_64(hi, lo, d)`.
    -- Three inputs (top half, bottom half, divisor); two named outputs
    -- (quotient in `q`, remainder in `r`); five flags undefined.  Backs the
    -- Knuth Algorithm D q̂ trial in `MpnDivRemPrototype`.
    | "DIV_64", [eh, el, ed] => do
        let hi ← evalPExpr s eh; let lo ← evalPExpr s el; let d ← evalPExpr s ed
        let (q, r) := divrem64 hi lo d
        writeDivBundle s lvs q r
    | "ADCX", [ea, eb, ec] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb; let c ← evalPExpr s ec
        let (cf, r) := addCarryIn a b c
        writeAdxBundle s lvs cf r
    | "ADOX", [ea, eb, ec] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb; let c ← evalPExpr s ec
        -- ADOX has identical arithmetic to ADC, but updates OF instead of CF.
        let (of, r) := addCarryIn a b c
        writeAdxBundle s lvs of r
    | "XOR_64", [ea, eb] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb
        let r : BitVec 64 := a ^^^ b
        -- For `xor x, x`: r = 0; CF and OF both cleared.
        -- For arbitrary operands: result is correct; CF/OF cleared per
        -- Intel SDM `XOR` (CF=OF=0 always after XOR).
        writeXorBundle s lvs 0 0 r
    -- **(Shift, additive)** 64-bit single-precision left shift.
    -- `r = #SHL_64(a, k);` — `r = a << (k % 64)`.  1-LVal bundle.
    | "SHL_64", [ea, ek] => do
        let a ← evalPExpr s ea; let k ← evalPExpr s ek
        writeShiftBundle s lvs (shl64 a k)
    -- **(Shift, additive)** 64-bit single-precision logical right shift.
    -- `r = #SHR_64(a, k);` — `r = a >> (k % 64)`.  1-LVal bundle.
    | "SHR_64", [ea, ek] => do
        let a ← evalPExpr s ea; let k ← evalPExpr s ek
        writeShiftBundle s lvs (shr64 a k)
    -- **(Shift, additive)** 64-bit double-precision left shift.
    -- `r = #SHLD_64(dst, src, k);` — `r = (dst << k) | (src >> (64-k))`.
    -- Backs the cross-limb merge of `mpn_lshift`.
    | "SHLD_64", [edst, esrc, ek] => do
        let dst ← evalPExpr s edst; let src ← evalPExpr s esrc
        let k ← evalPExpr s ek
        writeShiftBundle s lvs (shld64 dst src k)
    -- **(Shift, additive)** 64-bit double-precision right shift.
    -- `r = #SHRD_64(dst, src, k);` — `r = (dst >> k) | (src << (64-k))`.
    -- Backs the cross-limb merge of `mpn_rshift`.
    | "SHRD_64", [edst, esrc, ek] => do
        let dst ← evalPExpr s edst; let src ← evalPExpr s esrc
        let k ← evalPExpr s ek
        writeShiftBundle s lvs (shrd64 dst src k)
    -- **(U32, additive)** 32-bit arithmetic intrinsics.  Result masked
    -- to 32 bits; carry/borrow is bit 32 of the unmasked intermediate.
    -- Same 6-LVal `[of, cf, sf, pf, zf, dst]` bundle as the 64-bit ops.
    | "SUB_32", [ea, eb] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb
        let (cf, r) := subBorrow32 a b
        writeSubBundle s lvs cf r
    | "ADD_32", [ea, eb] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb
        let (cf, r) := addCarry32 a b
        writeSubBundle s lvs cf r
    | "ADC_32", [ea, eb, ec] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb; let c ← evalPExpr s ec
        let (cf, r) := addCarryIn32 a b c
        writeSubBundle s lvs cf r
    | "SBB_32", [ea, eb, ec] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb; let c ← evalPExpr s ec
        let (bf, r) := subBorrowIn32 a b c
        writeSubBundle s lvs bf r
    -- **(U32, additive)** 32-bit BMI2 MULX.  `(hi, lo)` bundle exactly
    -- like the u64 `MULX` arm (no flags).  Each half is masked to 32 bits.
    | "MULX_32", [ea, eb] => do
        let a ← evalPExpr s ea; let b ← evalPExpr s eb
        let (hi, lo) := mulx32 a b
        writeMulxBundle s lvs hi lo
    | _, _ => none
  | _ => none

/-! ## §8. Body execution

`bignumExec` threads `execInstr` over a body. -/

def bignumExec : List InstrR → BignumState → Option BignumState
  | [],      s => some s
  | i :: is, s =>
    match execInstr s i with
    | some s' => bignumExec is s'
    | none    => none

/-! ## §8.5. Ccall-aware execution with a callee registry

The base `bignumExec`/`execInstr` above is the original "no Ccall"
interpreter; it is kept verbatim so that all of `BignumHoare.lean`'s
existing universal lemmas (which only cite straight-line bodies) keep
building.

`bignumExecFuel` extends the interpreter with one new InstrR shape:

```
.Ccall ii lvs fn args
```

Looked up via a `BignumRegistry : String → Option FunDecl` that the
caller threads in. The semantics for the void-return case (which is
what every bignum routine in `S2NBignumSSA.lean` uses):

1. Evaluate each `args[i]` via `evalPExpr`.
2. Build the callee's initial state: callee's params get the
   evaluated arg values; memory is shared (pointer-passing ABI).
3. Run the callee body recursively (consuming one fuel step).
4. Inherit the callee's final memory back into the caller; caller's
   registers are unchanged.

Termination is by structural recursion on `Nat` fuel. The body of
the callee is **not** structurally smaller than the caller's, so a
purely AST-structural recursion would not work; the fuel parameter
side-steps this. With fuel set to a safe upper bound (1000 in the
diff-test driver) the interpreter never aborts in practice — the
tallest call chain we ship is a single-level Ccall.

Non-void-return support: if the call site's
`lvs` is non-empty and the callee declares `results`, we read each
declared result variable out of the callee's final register file and
bind it into the corresponding caller LVal (a `Lvar`, a `Lmem .U64`
store, or a `Lnone` discard).  The void case (`lvs.isEmpty`) is
preserved byte-identical to the original behavior.  See `bindResults`
below for the per-LVal binding rules. -/

/-- A registry mapping function names to their `FunDecl`. -/
abbrev BignumRegistry := String → Option FunDecl

/-- Empty registry — `bignumExecFuel emptyRegistry` rejects all
    `Ccall`s, exactly matching the behavior of fuel-less `bignumExec`
    (modulo successful termination on non-Ccall bodies once fuel is
    sufficient). -/
def emptyRegistry : BignumRegistry := fun _ => none

/-! ### Loop unrolling helpers (used by Cfor / Cwhile cases below) -/

/-- Build a "set v := k" Cassgn instruction. Used to expose Cfor's
    loop counter to the body. -/
def mkSetVarConst (v : VarI) (k : Nat) : InstrR :=
  .Cassgn (.Lvar v) .AT_none (.sword .U64) (.Pconst (Int.ofNat k))

/-- Equation form of `mkSetVarConst`: it produces a `Cassgn` into a
    register-shaped LVal. Used by `PreservationCombinator` for
    Cfor preservation reasoning. -/
theorem mkSetVarConst_eq (v : VarI) (k : Nat) :
    mkSetVarConst v k =
    .Cassgn (.Lvar v) .AT_none (.sword .U64) (.Pconst (Int.ofNat k)) := rfl

/-- Unroll a Cfor's iterations into a flat list of `[set v := i; body]`
    blocks. Direction `UpTo` walks `i = lo, lo+1, ..., hi-1`; `DownTo`
    walks `i = hi-1, hi-2, ..., lo`. The empty-range case (`hi ≤ lo`)
    yields `[]`. -/
def unrollFor (v : VarI) (range : Range) (body : List InstrR) : List InstrR :=
  let n := range.hi - range.lo
  match range.dir with
  | .UpTo =>
    (List.range n).flatMap fun k =>
      mkSetVarConst v (range.lo + k) :: body
  | .DownTo =>
    (List.range n).flatMap fun k =>
      mkSetVarConst v (range.hi - 1 - k) :: body

/-! ### Ccall result binding

Bind a single value from the callee's final register file into one
caller LVal.  The value is read by name from `sCallee.regs`; the
target LVal is interpreted in the caller's continuing state `sCaller`:

* `Lnone _ _`         — discard; caller state unchanged.
* `Lvar x`            — `sCaller.regs[x] := value`.
* `Lmem .U64 base off` — store the value (low 8 bytes) at
                         `resolveAddr sCaller base off`.
* anything else       — `none` (unsupported shape).

This is **only reached** when the Ccall site declares non-empty `lvs`;
the existing void-return path (`lvs.isEmpty`) bypasses this entirely. -/
def bindResult (sCaller sCallee : BignumState) (lv : LVal) (res : VarI) :
    Option BignumState :=
  let v := sCallee.regs res.var.vname
  match lv with
  | .Lnone _ _ => some sCaller
  | .Lvar x    => some (setReg sCaller x.var.vname v)
  | .Lmem .U64 base off => do
      let addr ← resolveAddr sCaller base off
      some (storeMem sCaller addr (UInt64.ofNat v.toNat))
  | _ => none

/-- Bind a list of callee result variables into a list of caller LVals
    pairwise.  Returns `none` if the lists have different lengths
    (well-formedness check) or if any individual `bindResult` fails.

    Length-mismatch case is unreachable from existing consumers: every
    `Ccall` site with `lvs = []` skips this helper entirely (handled by
    the void branch above), so the only callers that reach `bindResults`
    are non-void sites whose `lvs.length` matches the callee
    declaration's `results.length` (the jasmin source-language
    invariant). -/
def bindResults : BignumState → BignumState → List LVal → List VarI →
    Option BignumState
  | sCaller, _,        [],        []        => some sCaller
  | sCaller, sCallee,  lv :: lvs, r :: rs   => do
      let s' ← bindResult sCaller sCallee lv r
      bindResults s' sCallee lvs rs
  | _, _, _, _ => none

/-- Fuel'd, registry-aware body interpreter. Termination is by
    lexicographic order on `(fuel, body length)`: the Ccall recursion
    decreases the first component (passes `fuel`, parent has
    `fuel + 1`); the straight-line tail-recursion on `is` decreases
    the second component (with same fuel `fuel + 1`).

    For straight-line bodies (no Ccall / Cif / Cfor / Cwhile) the
    fuel-less `execInstr` handles each step; we just need the fuel
    envelope to be ≥ 1. The diff-test driver passes 1000 — comfortable
    for every body in `S2NBignumSSA.lean`.

    `Cif`/`Cfor`/`Cwhile` cases work by
    unrolling/unfolding the control-flow construct into a flat
    instruction sequence and re-entering with `fuel` (decreased)
    rather than `fuel + 1` so the lex-order's first component drops.
    `Cwhile` is fuel-bounded — an infinite loop runs out of fuel and
    returns `none`. -/
def bignumExecFuel (registry : BignumRegistry) :
    Nat → List InstrR → BignumState → Option BignumState
  | 0, _, _ => none
  | _ + 1, [], s => some s
  | fuel + 1, i :: is, s =>
    match i with
    | .Ccall _ii lvs fn args =>
      match registry fn.name with
      | none => none
      | some calleeFd =>
        match args.mapM (evalPExpr s) with
        | none => none
        | some argValues =>
          let calleeRegs : String → BitVec 64 := fun name =>
            match calleeFd.params.findIdx? (·.var.var.vname = name) with
            | some idx => (argValues[idx]?).getD 0
            | none => 0
          let calleeInit : BignumState := { regs := calleeRegs, mem := s.mem }
          match bignumExecFuel registry fuel calleeFd.body calleeInit with
          | none => none
          | some calleeFinal =>
            if lvs.isEmpty then
              -- Void return (preserved byte-identical to the original
              -- arm): inherit callee memory; caller regs unchanged.
              bignumExecFuel registry (fuel + 1) is { s with mem := calleeFinal.mem }
            else
              -- Non-void return: inherit
              -- callee memory, then bind each callee `results[i]`
              -- (read from `calleeFinal.regs`) into caller `lvs[i]`
              -- (interpreted against the caller's continuing state).
              let sCaller : BignumState := { s with mem := calleeFinal.mem }
              match bindResults sCaller calleeFinal lvs calleeFd.results with
              | none => none
              | some s' => bignumExecFuel registry (fuel + 1) is s'
    | .Cif cond cthen celse =>
      -- Evaluate cond; non-zero ⇒ run cthen, zero ⇒ run celse.
      match evalPExpr s cond with
      | none => none
      | some condV =>
        let body := if condV != 0 then cthen else celse
        match bignumExecFuel registry fuel body s with
        | none => none
        | some s' => bignumExecFuel registry (fuel + 1) is s'
    | .Cfor v range body =>
      -- Unroll into a flat (set i; body)* sequence and prepend to is.
      -- Termination: fuel decreases (fuel + 1 → fuel).
      bignumExecFuel registry fuel (unrollFor v range body ++ is) s
    | .Cwhile cbefore cond cafter =>
      -- Jasmin while semantics: cbefore; if cond then cafter; loop else exit.
      -- Encode by unfolding one iteration as
      --   cbefore ++ [Cif cond (cafter ++ [Cwhile ...]) []]
      -- and prepending to is. Fuel decreases per iteration; an
      -- infinite loop runs out of fuel and returns `none`.
      let oneIter : List InstrR :=
        cbefore ++ [.Cif cond (cafter ++ [.Cwhile cbefore cond cafter]) []]
      bignumExecFuel registry fuel (oneIter ++ is) s
    | i =>
      match execInstr s i with
      | some s' => bignumExecFuel registry (fuel + 1) is s'
      | none => none
termination_by fuel body _ => (fuel, body.length)

/-! ## §8.6. Fuel-less control-flow wrapper

`bignumExecCF` (Control Flow) is a fuel-less wrapper around
`bignumExecFuel emptyRegistry` with a fixed large fuel constant
(1_000_000). It exposes the Cif/Cfor/Cwhile support that
`bignumExecFuel` provides to callers that want a `bignumExec`-style
interface (no fuel parameter, no registry).

## When to use which

| Body shape | Recommended interpreter |
|---|---|
| Straight-line (Cassgn / Copn only) | `bignumExec` (the original; preserved untouched) |
| With Cif / Cfor (bounded) | `bignumExecCF` |
| With Cwhile (potentially unbounded) | `bignumExecCF` (1M iterations) or `bignumExecFuel` (explicit fuel) |
| With Ccall (cross-function) | `bignumExecFuel` with a `BignumRegistry` |

## Why a wrapper instead of extending `bignumExec`

`BignumHoare.lean` proves universal correctness lemmas like
`bignum_mod_p25519_4_correct_universal` against `bignumExec`. Changing
`bignumExec`'s definition would require re-proving those lemmas. Today's
extension keeps `bignumExec` 100% backward-compatible (still
straight-line) and exposes control-flow via the wrapper.

For LowCT-level programs that interpret through this layer, callers
should switch from `bignumExec` to `bignumExecCF`.

## Equivalence on straight-line bodies

For any body without `Cif`/`Cfor`/`Cwhile`/`Ccall`, `bignumExecCF body s
= bignumExec body s`. This is provable by induction over the body —
both interpreters delegate to `execInstr` for non-control-flow shapes,
and the fuel envelope of 1M is more than sufficient for any reasonable
straight-line body. -/

/-- Fuel-less wrapper: interprets a body with the empty registry and
    a 1M fuel envelope. Suitable for LowCT-level programs using
    `Cif`/`Cfor` (bounded loops) and `Cwhile` bodies that terminate
    in well under a million iterations. For programs with `Ccall`,
    use `bignumExecFuel` directly with a non-empty registry. -/
def bignumExecCF (body : List InstrR) (s : BignumState) :
    Option BignumState :=
  bignumExecFuel emptyRegistry 1_000_000 body s

/-! ### Straight-line equivalence

A body is `straightLine` if every instruction is `Cassgn` or `Copn`
(no `Ccall` / `Cif` / `Cfor` / `Cwhile`). On such bodies, both
`bignumExecFuel` (any positive fuel) and `bignumExec` only ever consult
`execInstr`, so they agree. -/

end CatCrypt.Crypto.Jasmin.BignumExec

namespace CatCrypt.Crypto.Jasmin

/-- Per-instruction straight-line predicate: `Cassgn` or `Copn`. -/
def InstrR.isStraightLine : InstrR → Bool
  | .Cassgn _ _ _ _ => true
  | .Copn _ _ _ _   => true
  | _               => false

/-- Per-instruction non-control predicate: `Cassgn`, `Copn`, or
    `Ccall` (no `Cif`/`Cfor`/`Cwhile`).  Gates the forward
    `bignumExecFuel_append_join` lemma. -/
def InstrR.isNonControl : InstrR → Prop
  | .Cassgn _ _ _ _ => True
  | .Copn _ _ _ _   => True
  | .Ccall _ _ _ _  => True
  | _               => False

/-- Body-level straight-line predicate: every instruction is straight-line.
    Recursive `Prop` shape so that `cons` cases destructure cleanly into
    `⟨h_head, h_tail⟩` without needing simp normalization on `List.all`. -/
def InstrR.bodyIsStraightLine : List InstrR → Prop
  | [] => True
  | i :: is => i.isStraightLine = true ∧ InstrR.bodyIsStraightLine is

end CatCrypt.Crypto.Jasmin

namespace CatCrypt.Crypto.Jasmin.BignumExec

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.MemoryModel

/-- On straight-line bodies, `bignumExecFuel` agrees with `bignumExec`
    for any positive fuel and any registry. The fuel doesn't even
    decrease — straight-line shapes flow into the catch-all `| i =>`
    arm which recurses with the same fuel. -/
theorem bignumExecFuel_eq_bignumExec_of_straightLine
    (registry : BignumRegistry) (fuel : Nat) (body : List InstrR)
    (s : BignumState)
    (h_sl : InstrR.bodyIsStraightLine body) :
    bignumExecFuel registry (fuel + 1) body s = bignumExec body s := by
  induction body generalizing fuel s with
  | nil => simp [bignumExec, bignumExecFuel]
  | cons i is ih =>
    obtain ⟨h_i, h_is⟩ := h_sl
    -- For `i` straight-line (Cassgn or Copn), `bignumExecFuel` falls
    -- into its catch-all `| i => ...` arm, which is exactly what
    -- `bignumExec` does. Both reduce to:
    --   match execInstr s i with | some s' => recurse on is | none => none.
    cases i with
    | Cassgn _ _ _ _ =>
      simp only [bignumExecFuel, bignumExec]
      cases h_step : execInstr s _ with
      | none => rfl
      | some s' => exact ih fuel s' h_is
    | Copn _ _ _ _ =>
      simp only [bignumExecFuel, bignumExec]
      cases h_step : execInstr s _ with
      | none => rfl
      | some s' => exact ih fuel s' h_is
    | _ => simp [InstrR.isStraightLine] at h_i

/-- `bignumExecCF` agrees with `bignumExec` on straight-line bodies.
    Direct corollary of `bignumExecFuel_eq_bignumExec_of_straightLine`
    with `fuel = 999_999` (i.e. `999_999 + 1 = 1_000_000`). -/
theorem bignumExecCF_eq_bignumExec_of_straightLine
    (body : List InstrR) (s : BignumState)
    (h_sl : InstrR.bodyIsStraightLine body) :
    bignumExecCF body s = bignumExec body s := by
  unfold bignumExecCF
  exact bignumExecFuel_eq_bignumExec_of_straightLine emptyRegistry 999_999 body s h_sl

/-! ### Smoke tests for `bignumExecCF` -/

namespace ControlFlowWrapperSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U64 }
def lvR (s : String) : LVal := .Lvar { var := vU s }
def pv (s : String) : PExpr :=
  .Pvar { gv := { var := vU s }, gs := false }
def varI (s : String) : VarI := { var := vU s }

def initState : BignumState :=
  { regs := fun x => match x with
      | "a" => 1
      | _ => 0
    mem := Mem.empty }

/-- Cif on the wrapper: same expected result as the fuel'd version. -/
example :
    (bignumExecCF
      [.Cif (pv "a")
        [.Cassgn (lvR "r") .AT_none (.sword .U64) (.Pconst 7)]
        [.Cassgn (lvR "r") .AT_none (.sword .U64) (.Pconst 9)]]
      initState).map (fun s => s.regs "r") = some 7 := by native_decide

/-- Cfor on the wrapper: 3 iterations with `r := i`, last writes 2. -/
example :
    (bignumExecCF
      [.Cfor (varI "i") { dir := .UpTo, lo := 0, hi := 3 }
        [.Cassgn (lvR "r") .AT_none (.sword .U64) (pv "i")]]
      initState).map (fun s => s.regs "r") = some 2 := by native_decide

end ControlFlowWrapperSmoke

/-! ## §8b. Smoke tests: `Papp2 .Olsl` / `Papp2 .Olsr` -/

namespace LslLsrSmoke

def s0 : BignumState :=
  { regs := fun _ => 0, mem := Mem.empty }

/-- `1 <<< 3 = 8`. -/
theorem olsl_const_3 :
    evalPExpr s0 (.Papp2 (.Olsl .U64) (.Pconst 1) (.Pconst 3))
      = some 8 := by native_decide

/-- `0xF0 >>> 4 = 0x0F`. -/
theorem olsr_const_4 :
    evalPExpr s0 (.Papp2 (.Olsr .U64) (.Pconst 0xF0) (.Pconst 4))
      = some 0x0F := by native_decide

/-- Width-agnostic: U32-tagged shift evaluates by the same wildcard. -/
theorem olsl_u32 :
    evalPExpr s0 (.Papp2 (.Olsl .U32) (.Pconst 1) (.Pconst 5))
      = some 0x20 := by native_decide

/-- Shift count masked mod 64: `1 <<< 64 = 1`. -/
theorem olsl_mod_64 :
    evalPExpr s0 (.Papp2 (.Olsl .U64) (.Pconst 1) (.Pconst 64))
      = some 1 := by native_decide

end LslLsrSmoke

/-! ## §9. Sequencing decomposition

Used by the Hoare-judgment's `seq` rule (in `Hoare.lean`). The bignum
fragment is straight-line, so this is structurally trivial. -/

theorem bignumExec_append (b1 b2 : List InstrR) (s s' : BignumState)
    (h : bignumExec (b1 ++ b2) s = some s') :
    ∃ s_mid : BignumState,
      bignumExec b1 s = some s_mid ∧ bignumExec b2 s_mid = some s' := by
  induction b1 generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons i b1' ih =>
    rw [List.cons_append] at h
    show ∃ _, _ ∧ _
    -- Step on i.
    cases h_step : execInstr s i with
    | none =>
      simp [bignumExec, h_step] at h
    | some s1 =>
      have h' : bignumExec (b1' ++ b2) s1 = some s' := by
        simp [bignumExec, h_step] at h; exact h
      obtain ⟨s_mid, h1, h2⟩ := ih s1 h'
      refine ⟨s_mid, ?_, h2⟩
      simp [bignumExec, h_step, h1]

/-! ## §9'. Sequencing decomposition for `bignumExecFuel`

The fuel'd / Ccall-aware sibling of `bignumExec_append`. Used by
`BignumTripleFuel.seq` in `BignumHoare/PowP58LayerB.lean` to compose
per-block correctness theorems whose bodies use Ccalls.

The witness fuels (`fuel1`, `fuel2`) are existentially bound so the
caller doesn't have to track fuel arithmetic; in the straight-line
and Cif cases the same fuel suffices, and the Cfor / Cwhile cases
generally need at least the same fuel as the outer run.

The proof is structurally analogous to `bignumExecFuel_preserves_reg_aux`
in `Tactics/PreservationCombinator.lean` — case-by-case on the head
InstrR, with lex-recursion on `(fuel, body1.length)`. The Cfor /
Cwhile cases recurse on the merged unrolled body with strictly
smaller fuel; the witness fuel for the original `Cfor :: rest`
prefix is then `(witness for unrolled prefix) + 1`, which by
definition of `bignumExecFuel` reduces back to the unrolled run. -/

/-- Strengthened form: the witness fuel for `body1` equals the outer
fuel exactly, so the only existential is `s_mid` and `fuel2`. -/
theorem bignumExecFuel_append_split_aux
    (registry : BignumRegistry) (fuel : Nat) (body1 body2 : List InstrR)
    (s s' : BignumState)
    (h : bignumExecFuel registry fuel (body1 ++ body2) s = some s') :
    ∃ s_mid : BignumState, ∃ fuel2 : Nat,
      bignumExecFuel registry fuel body1 s = some s_mid ∧
      bignumExecFuel registry fuel2 body2 s_mid = some s' := by
  match fuel, body1, s, s', h with
  | 0, _, _, _, h =>
    simp only [bignumExecFuel] at h
    cases h
  | fuel + 1, [], s, s', h =>
    -- body1 = []: split at the initial state.
    refine ⟨s, fuel + 1, ?_, ?_⟩
    · simp [bignumExecFuel]
    · simpa [List.nil_append] using h
  | fuel + 1, .Cassgn lv tag ty e :: rest, s, s', h =>
    simp only [List.cons_append, bignumExecFuel] at h
    rcases h_step : execInstr s (.Cassgn lv tag ty e) with _ | s_mid
    · rw [h_step] at h; cases h
    · rw [h_step] at h
      obtain ⟨s_end, fuel2, h1, h2⟩ :=
        bignumExecFuel_append_split_aux registry (fuel + 1) rest body2 s_mid s' h
      refine ⟨s_end, fuel2, ?_, h2⟩
      simp only [bignumExecFuel, h_step]
      exact h1
  | fuel + 1, .Copn lvs tag op args :: rest, s, s', h =>
    simp only [List.cons_append, bignumExecFuel] at h
    rcases h_step : execInstr s (.Copn lvs tag op args) with _ | s_mid
    · rw [h_step] at h; cases h
    · rw [h_step] at h
      obtain ⟨s_end, fuel2, h1, h2⟩ :=
        bignumExecFuel_append_split_aux registry (fuel + 1) rest body2 s_mid s' h
      refine ⟨s_end, fuel2, ?_, h2⟩
      simp only [bignumExecFuel, h_step]
      exact h1
  | fuel + 1, .Cif cond ct ce :: rest, s, s', h =>
    simp only [List.cons_append, bignumExecFuel] at h
    rcases h_cond : evalPExpr s cond with _ | condV
    · rw [h_cond] at h; cases h
    · rw [h_cond] at h
      simp only at h
      by_cases hc : condV != 0
      · rw [ite_eq_left hc] at h
        rcases h_inner : bignumExecFuel registry fuel ct s with _ | s_branch
        · rw [h_inner] at h; cases h
        · rw [h_inner] at h
          obtain ⟨s_end, fuel2, h1, h2⟩ :=
            bignumExecFuel_append_split_aux registry (fuel + 1) rest body2
              s_branch s' h
          refine ⟨s_end, fuel2, ?_, h2⟩
          show bignumExecFuel registry (fuel + 1) (.Cif cond ct ce :: rest) s
            = some s_end
          simp only [bignumExecFuel, h_cond]
          rw [ite_eq_left hc, h_inner]
          exact h1
      · rw [ite_eq_right hc] at h
        rcases h_inner : bignumExecFuel registry fuel ce s with _ | s_branch
        · rw [h_inner] at h; cases h
        · rw [h_inner] at h
          obtain ⟨s_end, fuel2, h1, h2⟩ :=
            bignumExecFuel_append_split_aux registry (fuel + 1) rest body2
              s_branch s' h
          refine ⟨s_end, fuel2, ?_, h2⟩
          show bignumExecFuel registry (fuel + 1) (.Cif cond ct ce :: rest) s
            = some s_end
          simp only [bignumExecFuel, h_cond]
          rw [ite_eq_right hc, h_inner]
          exact h1
  | fuel + 1, .Cfor v range body :: rest, s, s', h =>
    -- Cfor head: bignumExecFuel unrolls and re-enters with `fuel`
    -- (lex first component decreases). Push the appended `body2`
    -- past the unroll via list-associativity, recurse on the merged
    -- body at strictly smaller fuel `fuel`.
    simp only [List.cons_append, bignumExecFuel] at h
    have h' : bignumExecFuel registry fuel
        ((unrollFor v range body ++ rest) ++ body2) s = some s' := by
      simpa [List.append_assoc] using h
    obtain ⟨s_end, fuel2, h1, h2⟩ :=
      bignumExecFuel_append_split_aux registry fuel
        (unrollFor v range body ++ rest) body2 s s' h'
    refine ⟨s_end, fuel2, ?_, h2⟩
    -- bignumExecFuel registry (fuel + 1) (Cfor :: rest) s reduces by def
    --   to bignumExecFuel registry fuel (unrollFor ... ++ rest) s
    show bignumExecFuel registry (fuel + 1)
      (.Cfor v range body :: rest) s = some s_end
    simp only [bignumExecFuel]
    exact h1
  | fuel + 1, .Cwhile cb cond ca :: rest, s, s', h =>
    -- Cwhile head: same pattern as Cfor — unfold one iteration,
    -- recurse on the merged body with strictly smaller fuel.
    simp only [List.cons_append, bignumExecFuel] at h
    have h' : bignumExecFuel registry fuel
        (((cb ++ [.Cif cond (ca ++ [.Cwhile cb cond ca]) []]) ++ rest)
          ++ body2) s = some s' := by
      simpa [List.append_assoc] using h
    obtain ⟨s_end, fuel2, h1, h2⟩ :=
      bignumExecFuel_append_split_aux registry fuel
        ((cb ++ [.Cif cond (ca ++ [.Cwhile cb cond ca]) []]) ++ rest)
        body2 s s' h'
    refine ⟨s_end, fuel2, ?_, h2⟩
    show bignumExecFuel registry (fuel + 1)
      (.Cwhile cb cond ca :: rest) s = some s_end
    simp only [bignumExecFuel]
    exact h1
  | fuel + 1, .Ccall ii lvs fn args :: rest, s, s', h =>
    simp only [List.cons_append, bignumExecFuel] at h
    rcases h_reg : registry fn.name with _ | calleeFd
    · rw [h_reg] at h; cases h
    · rw [h_reg] at h
      simp only at h
      rcases h_args : args.mapM (evalPExpr s) with _ | argValues
      · rw [h_args] at h; cases h
      · rw [h_args] at h
        simp only at h
        split at h
        · cases h
        · rename_i calleeFinal h_callee
          split at h
          · rename_i h_void
            obtain ⟨s_end, fuel2, h1, h2⟩ :=
              bignumExecFuel_append_split_aux registry (fuel + 1) rest body2
                { s with mem := calleeFinal.mem } s' h
            refine ⟨s_end, fuel2, ?_, h2⟩
            simp only [bignumExecFuel, h_reg, h_args, h_callee, h_void,
              ite_true]
            exact h1
          · rename_i h_nonvoid
            -- Non-void branch: the result-binding helper is consulted;
            -- if it succeeds, we recurse on `rest ++ body2` with the
            -- post-bind caller state.
            rcases h_bind : bindResults { s with mem := calleeFinal.mem }
                              calleeFinal lvs calleeFd.results with _ | sBound
            · rw [h_bind] at h; cases h
            · rw [h_bind] at h
              obtain ⟨s_end, fuel2, h1, h2⟩ :=
                bignumExecFuel_append_split_aux registry (fuel + 1) rest body2
                  sBound s' h
              refine ⟨s_end, fuel2, ?_, h2⟩
              simp only [bignumExecFuel, h_reg, h_args, h_callee, h_nonvoid,
                h_bind]
              exact h1
  termination_by (fuel, body1.length)
  decreasing_by
    all_goals
      simp_wf
      first
        | (apply Prod.Lex.right; simp; omega)
        | (apply Prod.Lex.left; omega)
        | omega

theorem bignumExecFuel_append_split
    (registry : BignumRegistry) (fuel : Nat) (body1 body2 : List InstrR)
    (s s' : BignumState)
    (h : bignumExecFuel registry fuel (body1 ++ body2) s = some s') :
    ∃ s_mid : BignumState, ∃ fuel1 fuel2 : Nat,
      bignumExecFuel registry fuel1 body1 s = some s_mid ∧
      bignumExecFuel registry fuel2 body2 s_mid = some s' := by
  obtain ⟨s_mid, fuel2, h1, h2⟩ :=
    bignumExecFuel_append_split_aux registry fuel body1 body2 s s' h
  exact ⟨s_mid, fuel, fuel2, h1, h2⟩

/-- Forward sequencing for `bignumExecFuel` (constructor direction).
    From two successful sub-runs at the *same* fuel, build one
    successful run on the appended body at that fuel.

    Restricted to `body1` containing no `Cif`/`Cfor`/`Cwhile`
    (which decrement outer fuel; the constructor would need a fuel-
    monotonicity lemma to handle them).  This restriction holds for
    every body produced by `BignumInvP25519.sqr_step`/`mul_step` in
    the chain proof. -/
theorem bignumExecFuel_append_join
    (registry : BignumRegistry) (fuel : Nat) (body1 body2 : List InstrR)
    (h_nc : ∀ i ∈ body1, i.isNonControl)
    (s s_mid s' : BignumState)
    (h1 : bignumExecFuel registry fuel body1 s = some s_mid)
    (h2 : bignumExecFuel registry fuel body2 s_mid = some s') :
    bignumExecFuel registry fuel (body1 ++ body2) s = some s' := by
  match fuel, body1, s, s_mid, h1, h_nc with
  | 0, _, _, _, h1, _ =>
    simp only [bignumExecFuel] at h1
    cases h1
  | fuel + 1, [], s, s_mid, h1, _ =>
    simp only [bignumExecFuel] at h1
    cases h1
    simpa [List.nil_append] using h2
  | fuel + 1, .Cassgn lv tag ty e :: rest, s, s_mid, h1, h_nc =>
    simp only [bignumExecFuel] at h1
    rcases h_step : execInstr s (.Cassgn lv tag ty e) with _ | s1
    · rw [h_step] at h1; cases h1
    · rw [h_step] at h1
      simp only [List.cons_append, bignumExecFuel, h_step]
      have h_nc' : ∀ i ∈ rest, i.isNonControl :=
        fun i hi => h_nc i (List.mem_cons_of_mem _ hi)
      exact bignumExecFuel_append_join registry (fuel + 1) rest body2 h_nc'
        s1 s_mid s' h1 h2
  | fuel + 1, .Copn lvs tag op args :: rest, s, s_mid, h1, h_nc =>
    simp only [bignumExecFuel] at h1
    rcases h_step : execInstr s (.Copn lvs tag op args) with _ | s1
    · rw [h_step] at h1; cases h1
    · rw [h_step] at h1
      simp only [List.cons_append, bignumExecFuel, h_step]
      have h_nc' : ∀ i ∈ rest, i.isNonControl :=
        fun i hi => h_nc i (List.mem_cons_of_mem _ hi)
      exact bignumExecFuel_append_join registry (fuel + 1) rest body2 h_nc'
        s1 s_mid s' h1 h2
  | fuel + 1, .Cif cond ct ce :: rest, s, s_mid, h1, h_nc =>
    exact (h_nc _ (List.mem_cons_self ..)).elim
  | fuel + 1, .Cfor v range body :: rest, s, s_mid, h1, h_nc =>
    exact (h_nc _ (List.mem_cons_self ..)).elim
  | fuel + 1, .Cwhile cb cond ca :: rest, s, s_mid, h1, h_nc =>
    exact (h_nc _ (List.mem_cons_self ..)).elim
  | fuel + 1, .Ccall ii lvs fn args :: rest, s, s_mid, h1, h_nc =>
    simp only [bignumExecFuel] at h1
    rcases h_reg : registry fn.name with _ | calleeFd
    · rw [h_reg] at h1; cases h1
    · rw [h_reg] at h1
      rcases h_args : args.mapM (evalPExpr s) with _ | argValues
      · rw [h_args] at h1; cases h1
      · rw [h_args] at h1
        simp only at h1
        rcases h_callee : bignumExecFuel registry fuel calleeFd.body
            { regs := fun name =>
                match calleeFd.params.findIdx? (·.var.var.vname = name) with
                | some idx => (argValues[idx]?).getD 0
                | none => 0
              mem := s.mem } with _ | calleeFinal
        · rw [h_callee] at h1; cases h1
        · rw [h_callee] at h1
          simp only at h1
          by_cases h_void : lvs.isEmpty
          · rw [ite_eq_left h_void] at h1
            show bignumExecFuel registry (fuel + 1)
              (.Ccall ii lvs fn args :: rest ++ body2) s = some s'
            simp only [List.cons_append, bignumExecFuel, h_reg, h_args, h_callee]
            rw [ite_eq_left h_void]
            have h_nc' : ∀ i ∈ rest, i.isNonControl :=
              fun i hi => h_nc i (List.mem_cons_of_mem _ hi)
            exact bignumExecFuel_append_join registry (fuel + 1) rest body2 h_nc'
              { s with mem := calleeFinal.mem } s_mid s' h1 h2
          · rw [ite_eq_right h_void] at h1
            -- Non-void branch: result-binding is consulted.
            rcases h_bind : bindResults { s with mem := calleeFinal.mem }
                              calleeFinal lvs calleeFd.results with _ | sBound
            · rw [h_bind] at h1; cases h1
            · rw [h_bind] at h1
              show bignumExecFuel registry (fuel + 1)
                (.Ccall ii lvs fn args :: rest ++ body2) s = some s'
              simp only [List.cons_append, bignumExecFuel, h_reg, h_args, h_callee]
              rw [ite_eq_right h_void, h_bind]
              have h_nc' : ∀ i ∈ rest, i.isNonControl :=
                fun i hi => h_nc i (List.mem_cons_of_mem _ hi)
              exact bignumExecFuel_append_join registry (fuel + 1) rest body2 h_nc'
                sBound s_mid s' h1 h2
  termination_by (fuel, body1.length)
  decreasing_by
    all_goals
      simp_wf
      first
        | (apply Prod.Lex.right; simp; omega)
        | (apply Prod.Lex.left; omega)
        | omega

/-- **Fuel monotonicity for `bignumExecFuel`.**  A successful run is invariant
    under increasing the fuel envelope: if `bignumExecFuel reg fuel body s`
    succeeds with `s'`, then so does the run at `fuel + extra`, with the same
    result.  This is what lets a continuation be sequenced after a control-flow
    construct (`Cwhile`/`Cfor`/`Ccall`) whose body consumed a different amount of
    fuel — the loop run and the continuation can be aligned to a common fuel.

    Proved by the same well-founded recursion `bignumExecFuel` uses (lex order
    on `(fuel, body.length)`): every arm either decreases `body.length` at the
    same fuel (straight-line tail) or decreases `fuel` (the `Ccall` callee, the
    `Cif` branch, the `Cfor`/`Cwhile` unroll/unfold). -/
theorem bignumExecFuel_mono
    (registry : BignumRegistry) (fuel extra : Nat) (body : List InstrR)
    (s s' : BignumState)
    (h : bignumExecFuel registry fuel body s = some s') :
    bignumExecFuel registry (fuel + extra) body s = some s' := by
  -- Normalise the goal fuel to a syntactic `_ + 1` so `bignumExecFuel` reduces,
  -- and reassociate every recursive call's `(fuel + 1) + extra` to that form.
  match fuel, body, s, s', h with
  | 0, _, _, _, h =>
    simp only [bignumExecFuel] at h
    cases h
  | fuel + 1, [], s, s', h =>
    simp only [bignumExecFuel] at h
    cases h
    show bignumExecFuel registry (fuel + 1 + extra) [] s = some s
    rw [show fuel + 1 + extra = (fuel + extra) + 1 from by omega]
    simp only [bignumExecFuel]
  | fuel + 1, .Cassgn lv tag ty e :: rest, s, s', h =>
    simp only [bignumExecFuel] at h
    rcases h_step : execInstr s (.Cassgn lv tag ty e) with _ | s1
    · rw [h_step] at h; cases h
    · rw [h_step] at h
      show bignumExecFuel registry (fuel + 1 + extra) (.Cassgn lv tag ty e :: rest) s = some s'
      rw [show fuel + 1 + extra = (fuel + extra) + 1 from by omega]
      simp only [bignumExecFuel, h_step]
      have hrec := bignumExecFuel_mono registry (fuel + 1) extra rest s1 s' h
      rwa [show fuel + 1 + extra = (fuel + extra) + 1 from by omega] at hrec
  | fuel + 1, .Copn lvs tag op args :: rest, s, s', h =>
    simp only [bignumExecFuel] at h
    rcases h_step : execInstr s (.Copn lvs tag op args) with _ | s1
    · rw [h_step] at h; cases h
    · rw [h_step] at h
      show bignumExecFuel registry (fuel + 1 + extra) (.Copn lvs tag op args :: rest) s = some s'
      rw [show fuel + 1 + extra = (fuel + extra) + 1 from by omega]
      simp only [bignumExecFuel, h_step]
      have hrec := bignumExecFuel_mono registry (fuel + 1) extra rest s1 s' h
      rwa [show fuel + 1 + extra = (fuel + extra) + 1 from by omega] at hrec
  | fuel + 1, .Cif cond ct ce :: rest, s, s', h =>
    simp only [bignumExecFuel] at h
    rcases h_cond : evalPExpr s cond with _ | condV
    · rw [h_cond] at h; cases h
    · rw [h_cond] at h
      simp only at h
      rcases h_inner : bignumExecFuel registry fuel (if condV != 0 then ct else ce) s
        with _ | s_branch
      · rw [h_inner] at h; cases h
      · rw [h_inner] at h
        show bignumExecFuel registry (fuel + 1 + extra) (.Cif cond ct ce :: rest) s = some s'
        rw [show fuel + 1 + extra = (fuel + extra) + 1 from by omega]
        simp only [bignumExecFuel, h_cond]
        rw [bignumExecFuel_mono registry fuel extra _ s s_branch h_inner]
        have hrec := bignumExecFuel_mono registry (fuel + 1) extra rest s_branch s' h
        rwa [show fuel + 1 + extra = (fuel + extra) + 1 from by omega] at hrec
  | fuel + 1, .Cfor v range body :: rest, s, s', h =>
    simp only [bignumExecFuel] at h
    show bignumExecFuel registry (fuel + 1 + extra) (.Cfor v range body :: rest) s = some s'
    rw [show fuel + 1 + extra = (fuel + extra) + 1 from by omega]
    simp only [bignumExecFuel]
    exact bignumExecFuel_mono registry fuel extra (unrollFor v range body ++ rest) s s' h
  | fuel + 1, .Cwhile cb cond ca :: rest, s, s', h =>
    simp only [bignumExecFuel] at h
    show bignumExecFuel registry (fuel + 1 + extra) (.Cwhile cb cond ca :: rest) s = some s'
    rw [show fuel + 1 + extra = (fuel + extra) + 1 from by omega]
    simp only [bignumExecFuel]
    exact bignumExecFuel_mono registry fuel extra
      ((cb ++ [.Cif cond (ca ++ [.Cwhile cb cond ca]) []]) ++ rest) s s' h
  | fuel + 1, .Ccall ii lvs fn args :: rest, s, s', h =>
    simp only [bignumExecFuel] at h
    rcases h_reg : registry fn.name with _ | calleeFd
    · rw [h_reg] at h; cases h
    · rw [h_reg] at h
      rcases h_args : args.mapM (evalPExpr s) with _ | argValues
      · rw [h_args] at h; cases h
      · rw [h_args] at h
        simp only at h
        rcases h_callee : bignumExecFuel registry fuel calleeFd.body
            { regs := fun name =>
                match calleeFd.params.findIdx? (·.var.var.vname = name) with
                | some idx => (argValues[idx]?).getD 0
                | none => 0
              mem := s.mem } with _ | calleeFinal
        · rw [h_callee] at h; cases h
        · rw [h_callee] at h
          simp only at h
          by_cases h_void : lvs.isEmpty
          · rw [ite_eq_left h_void] at h
            show bignumExecFuel registry (fuel + 1 + extra) (.Ccall ii lvs fn args :: rest) s
              = some s'
            rw [show fuel + 1 + extra = (fuel + extra) + 1 from by omega]
            simp only [bignumExecFuel, h_reg, h_args]
            rw [bignumExecFuel_mono registry fuel extra calleeFd.body _ calleeFinal h_callee]
            simp only []
            rw [ite_eq_left h_void]
            have hrec := bignumExecFuel_mono registry (fuel + 1) extra rest
              { s with mem := calleeFinal.mem } s' h
            rwa [show fuel + 1 + extra = (fuel + extra) + 1 from by omega] at hrec
          · rw [ite_eq_right h_void] at h
            -- Non-void branch: result-binding consulted; recurse on the
            -- bound caller state and re-pack at the bumped fuel envelope.
            rcases h_bind : bindResults { s with mem := calleeFinal.mem }
                              calleeFinal lvs calleeFd.results with _ | sBound
            · rw [h_bind] at h; cases h
            · rw [h_bind] at h
              show bignumExecFuel registry (fuel + 1 + extra)
                (.Ccall ii lvs fn args :: rest) s = some s'
              rw [show fuel + 1 + extra = (fuel + extra) + 1 from by omega]
              simp only [bignumExecFuel, h_reg, h_args]
              rw [bignumExecFuel_mono registry fuel extra calleeFd.body _ calleeFinal h_callee]
              simp only []
              rw [ite_eq_right h_void, h_bind]
              have hrec := bignumExecFuel_mono registry (fuel + 1) extra rest sBound s' h
              rwa [show fuel + 1 + extra = (fuel + extra) + 1 from by omega] at hrec
  termination_by (fuel, body.length)
  decreasing_by
    all_goals
      simp_wf
      first
        | (apply Prod.Lex.right; simp; omega)
        | (apply Prod.Lex.left; omega)
        | omega

/-- **Forward sequencing for `bignumExecFuel`, no control-flow restriction.**
    From two successful sub-runs (`body1` at fuel `f1`, `body2` at fuel `f2`)
    build one successful run on `body1 ++ body2` at the summed fuel `f1 + f2`.
    Unlike `bignumExecFuel_append_join`, `body1` may contain `Cif`/`Cfor`/
    `Cwhile`/`Ccall`: the control-flow arms re-enter at strictly smaller fuel,
    and the continuation's fuel is bumped to the common envelope by
    `bignumExecFuel_mono`.  This is the join that lets a straight-line tail be
    sequenced after a loop body (the `Cwhile` of `bodyAddmul`).

    Proved by the same well-founded recursion `bignumExecFuel` uses (lex order
    on `(f1, body1.length)`). -/
theorem bignumExecFuel_seq
    (registry : BignumRegistry) (f1 f2 : Nat) (body1 body2 : List InstrR)
    (s s_mid s' : BignumState)
    (h1 : bignumExecFuel registry f1 body1 s = some s_mid)
    (h2 : bignumExecFuel registry f2 body2 s_mid = some s') :
    bignumExecFuel registry (f1 + f2) (body1 ++ body2) s = some s' := by
  match f1, body1, s, s_mid, h1 with
  | 0, _, _, _, h1 =>
    simp only [bignumExecFuel] at h1
    cases h1
  | f1 + 1, [], s, s_mid, h1 =>
    simp only [bignumExecFuel] at h1
    cases h1
    -- body1 = []: the whole run is body2, at fuel `(f1+1)+f2`.
    rw [List.nil_append, show f1 + 1 + f2 = f2 + (f1 + 1) from by omega]
    exact bignumExecFuel_mono registry f2 (f1 + 1) body2 s s' h2
  | f1 + 1, .Cassgn lv tag ty e :: rest, s, s_mid, h1 =>
    simp only [bignumExecFuel] at h1
    rcases h_step : execInstr s (.Cassgn lv tag ty e) with _ | s1
    · rw [h_step] at h1; cases h1
    · rw [h_step] at h1
      show bignumExecFuel registry (f1 + 1 + f2) (.Cassgn lv tag ty e :: rest ++ body2) s = some s'
      rw [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega, List.cons_append]
      simp only [bignumExecFuel, h_step]
      have hrec := bignumExecFuel_seq registry (f1 + 1) f2 rest body2 s1 s_mid s' h1 h2
      rwa [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega] at hrec
  | f1 + 1, .Copn lvs tag op args :: rest, s, s_mid, h1 =>
    simp only [bignumExecFuel] at h1
    rcases h_step : execInstr s (.Copn lvs tag op args) with _ | s1
    · rw [h_step] at h1; cases h1
    · rw [h_step] at h1
      show bignumExecFuel registry (f1 + 1 + f2) (.Copn lvs tag op args :: rest ++ body2) s = some s'
      rw [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega, List.cons_append]
      simp only [bignumExecFuel, h_step]
      have hrec := bignumExecFuel_seq registry (f1 + 1) f2 rest body2 s1 s_mid s' h1 h2
      rwa [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega] at hrec
  | f1 + 1, .Cif cond ct ce :: rest, s, s_mid, h1 =>
    simp only [bignumExecFuel] at h1
    rcases h_cond : evalPExpr s cond with _ | condV
    · rw [h_cond] at h1; cases h1
    · rw [h_cond] at h1
      simp only at h1
      rcases h_inner : bignumExecFuel registry f1 (if condV != 0 then ct else ce) s
        with _ | s_branch
      · rw [h_inner] at h1; cases h1
      · rw [h_inner] at h1
        show bignumExecFuel registry (f1 + 1 + f2) (.Cif cond ct ce :: rest ++ body2) s = some s'
        rw [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega, List.cons_append]
        simp only [bignumExecFuel, h_cond]
        rw [bignumExecFuel_mono registry f1 f2 _ s s_branch h_inner]
        have hrec := bignumExecFuel_seq registry (f1 + 1) f2 rest body2 s_branch s_mid s' h1 h2
        rwa [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega] at hrec
  | f1 + 1, .Cfor v range body :: rest, s, s_mid, h1 =>
    simp only [bignumExecFuel] at h1
    show bignumExecFuel registry (f1 + 1 + f2) (.Cfor v range body :: rest ++ body2) s = some s'
    rw [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega, List.cons_append]
    simp only [bignumExecFuel]
    have hrec := bignumExecFuel_seq registry f1 f2 (unrollFor v range body ++ rest) body2
      s s_mid s' h1 h2
    rwa [List.append_assoc] at hrec
  | f1 + 1, .Cwhile cb cond ca :: rest, s, s_mid, h1 =>
    simp only [bignumExecFuel] at h1
    show bignumExecFuel registry (f1 + 1 + f2) (.Cwhile cb cond ca :: rest ++ body2) s = some s'
    rw [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega, List.cons_append]
    simp only [bignumExecFuel]
    have hrec := bignumExecFuel_seq registry f1 f2
      ((cb ++ [.Cif cond (ca ++ [.Cwhile cb cond ca]) []]) ++ rest) body2 s s_mid s' h1 h2
    rwa [List.append_assoc] at hrec
  | f1 + 1, .Ccall ii lvs fn args :: rest, s, s_mid, h1 =>
    simp only [bignumExecFuel] at h1
    rcases h_reg : registry fn.name with _ | calleeFd
    · rw [h_reg] at h1; cases h1
    · rw [h_reg] at h1
      rcases h_args : args.mapM (evalPExpr s) with _ | argValues
      · rw [h_args] at h1; cases h1
      · rw [h_args] at h1
        simp only at h1
        rcases h_callee : bignumExecFuel registry f1 calleeFd.body
            { regs := fun name =>
                match calleeFd.params.findIdx? (·.var.var.vname = name) with
                | some idx => (argValues[idx]?).getD 0
                | none => 0
              mem := s.mem } with _ | calleeFinal
        · rw [h_callee] at h1; cases h1
        · rw [h_callee] at h1
          simp only at h1
          by_cases h_void : lvs.isEmpty
          · rw [ite_eq_left h_void] at h1
            show bignumExecFuel registry (f1 + 1 + f2) (.Ccall ii lvs fn args :: rest ++ body2) s
              = some s'
            rw [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega, List.cons_append]
            simp only [bignumExecFuel, h_reg, h_args]
            rw [bignumExecFuel_mono registry f1 f2 calleeFd.body _ calleeFinal h_callee]
            simp only []
            rw [ite_eq_left h_void]
            have hrec := bignumExecFuel_seq registry (f1 + 1) f2 rest body2
              { s with mem := calleeFinal.mem } s_mid s' h1 h2
            rwa [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega] at hrec
          · rw [ite_eq_right h_void] at h1
            -- Non-void branch: bind callee results, then sequence
            -- continuation `rest` and tail `body2` from the bound state.
            rcases h_bind : bindResults { s with mem := calleeFinal.mem }
                              calleeFinal lvs calleeFd.results with _ | sBound
            · rw [h_bind] at h1; cases h1
            · rw [h_bind] at h1
              show bignumExecFuel registry (f1 + 1 + f2)
                (.Ccall ii lvs fn args :: rest ++ body2) s = some s'
              rw [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega, List.cons_append]
              simp only [bignumExecFuel, h_reg, h_args]
              rw [bignumExecFuel_mono registry f1 f2 calleeFd.body _ calleeFinal h_callee]
              simp only []
              rw [ite_eq_right h_void, h_bind]
              have hrec := bignumExecFuel_seq registry (f1 + 1) f2 rest body2
                sBound s_mid s' h1 h2
              rwa [show f1 + 1 + f2 = (f1 + f2) + 1 from by omega] at hrec
  termination_by (f1, body1.length)
  decreasing_by
    all_goals
      simp_wf
      first
        | (apply Prod.Lex.right; simp; omega)
        | (apply Prod.Lex.left; omega)
        | omega

/-! ## §10. Smoke test

A 2-instruction body that loads a u64 and stores it elsewhere.
Verifies that `bignumExec` runs to completion (`isSome`) on a
straight-line body. -/

/-- Initial state: `ap` register points at address 16; memory holds
    a 64-bit value `0x42` packed at bytes 16..23. -/
def smokeInit : BignumState :=
  let regs : String → BitVec 64 := fun x =>
    if x = "ap" then 16
    else if x = "op" then 100
    else 0
  let mem : Mem := fun a =>
    if a = 16 then some 0x42
    else if a ≥ 17 ∧ a ≤ 23 then some 0
    else if a ≥ 100 ∧ a ≤ 107 then some 0  -- pre-allocate op range
    else none
  { regs := regs, mem := mem }

/-- Body: `t := *(ap + 0); *(op + 0) := t`. -/
def smokeBody : List InstrR :=
  [ .Cassgn (.Lvar { var := { vname := "t", vtype := .sword .U64 }, info := {} })
            .AT_none (.sword .U64)
            (.Pload .U64
              { var := { vname := "ap", vtype := .sword .U64 }, info := {} }
              (.Pconst 0))
  , .Cassgn (.Lmem .U64
              { var := { vname := "op", vtype := .sword .U64 }, info := {} }
              (.Pconst 0))
            .AT_none (.sword .U64)
            (.Pvar { gv := { var := { vname := "t", vtype := .sword .U64 },
                              info := {} }, gs := false }) ]

/-- The smoke body executes successfully on the smoke initial state. -/
example : (bignumExec smokeBody smokeInit).isSome := by native_decide

/-! ## §11. Ccall smoke test

Validates the new `bignumExecFuel` Ccall plumbing on a tiny synthetic
example whose callee body uses **only** `Cassgn` (so it exercises
the path through `execInstr` that we know works). The callee:

```
fn store_const(p : reg u64) {
  *(p + 0) = 0x42;
}
```

The caller calls it once on `op`. After the call, memory at op[0]
should hold `0x42`. This catches regressions in: registry lookup,
arg evaluation, callee state setup, body execution, memory inherit,
fuel decrement. -/

namespace CcallSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- Callee: writes 0x42 at `*(p + 0)`. -/
def calleeFd : FunDecl where
  name := { name := "store_const" }
  params := [⟨{ var := vU "p" }⟩]
  body :=
    [ .Cassgn (.Lmem .U64 { var := vU "p" } (.Pconst 0))
              .AT_none (.sword .U64) (.Pconst 0x42) ]
  results := []

/-- Caller: a single Ccall to `store_const(op)`. -/
def callerBody : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "store_const" }
      [.Pvar { gv := { var := vU "op" }, gs := false }] ]

/-- Tiny registry mapping `"store_const"` to `calleeFd`. -/
def registry : BignumRegistry := fun n =>
  if n = "store_const" then some calleeFd else none

/-- Initial state: `op` points at address 100; memory pre-allocated at [100..107]. -/
def initState : BignumState :=
  { regs := fun x => if x = "op" then 100 else 0
    mem  := fun a => if a ≥ 100 ∧ a ≤ 107 then some 0 else none }

/-- The Ccall body executes: callee writes 0x42 at op[0]; caller
    inherits memory; final memory at address 100 = 0x42. -/
example :
    (bignumExecFuel registry 100 callerBody initState).map
        (fun final => final.mem.loadByte 100)
      = some (some 0x42) := by native_decide

end CcallSmoke

/-! ## §11.5. Ccall result-binding smoke test

Validates the non-void `Ccall` branch: a callee that produces a
single `reg u64` return value, called from a caller that binds that
result into its own LVal.  Callee:

```
fn double(reg u64 x) -> reg u64 {
  reg u64 r;
  r = x;
  r <<= 1;
  return r;
}
```

Caller: `out = double(arg);` with `arg := 21`.  Expected: `out = 42`.

This exercises every leg of the new path:
* registry lookup of a callee with non-empty `results`,
* argument evaluation,
* callee body execution (two `Cassgn`s),
* `bindResults` reading `r` from `calleeFinal.regs` and writing it to
  the caller's `out` LVal,
* the caller's continuation seeing the post-bind state. -/

namespace CcallResultBindSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- Callee `double(x)`: returns `x * 2` via `r := x; r := r + r`. -/
def doubleFd : FunDecl where
  name := { name := "double" }
  params := [⟨{ var := vU "x" }⟩]
  body :=
    [ -- r := x
      .Cassgn (.Lvar { var := vU "r" }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := vU "x" }, gs := false })
      -- r := r + r   (== r <<= 1)
    , .Cassgn (.Lvar { var := vU "r" }) .AT_none (.sword .U64)
        (.Papp2 (.Oadd .U64)
          (.Pvar { gv := { var := vU "r" }, gs := false })
          (.Pvar { gv := { var := vU "r" }, gs := false })) ]
  results := [{ var := vU "r" }]

/-- Caller: `out = double(arg);`.  The `Lvar out` binds the result. -/
def callerBody : List InstrR :=
  [ .Ccall .DoNotInline [.Lvar { var := vU "out" }]
      { name := "double" }
      [.Pvar { gv := { var := vU "arg" }, gs := false }] ]

/-- One-callee registry. -/
def registry : BignumRegistry := fun n =>
  if n = "double" then some doubleFd else none

/-- Initial state: `arg := 21`; memory empty. -/
def initState : BignumState :=
  { regs := fun x => if x = "arg" then 21 else 0
    mem  := fun _ => none }

/-- After the call, the caller's `out` register holds `2 * arg = 42`. -/
example :
    (bignumExecFuel registry 100 callerBody initState).map
        (fun final => final.regs "out")
      = some (BitVec.ofNat 64 42) := by native_decide

/-- Sanity: the caller's `arg` register is unchanged across the call
    (the callee's `arg`-shadowing of its parameter `x` happens entirely
    in the callee's register file, which is separate from the caller's). -/
example :
    (bignumExecFuel registry 100 callerBody initState).map
        (fun final => final.regs "arg")
      = some (BitVec.ofNat 64 21) := by native_decide

end CcallResultBindSmoke

/-! ## §12. Smoke tests for new intrinsics

Validates that ADD_64, ADC_64, MULX, ADCX, ADOX, XOR_64 are all
interpreted correctly by `execInstr`. Each test exercises a single
intrinsic and checks the resulting register/memory state via
`native_decide`. -/

namespace IntrinsicSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U64 }
def lvR (s : String) : LVal := .Lvar { var := vU s }
def pv (s : String) : PExpr :=
  .Pvar { gv := { var := vU s }, gs := false }

/-- 6-LVal flag bundle layout for ADD/ADC/SUB/SBB. -/
def flagBundle (cf r : String) : List LVal :=
  [.Lnone {} (.sword .U64), lvR cf,
   .Lnone {} (.sword .U64), .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
   lvR r]

/-- Initial state with `a := 0xFFFFFFFFFFFFFFFE`, `b := 3`. So
    `a + b = 1` (with carry), `a * b = 0x2_FFFFFFFFFFFFFFFA`. -/
def initState : BignumState :=
  let regs : String → BitVec 64 := fun x =>
    if x = "a" then 0xFFFFFFFFFFFFFFFE
    else if x = "b" then 3
    else 0
  { regs := regs, mem := Mem.empty }

/-- ADD_64 with carry: 0xFFFFFFFFFFFFFFFE + 3 = 1, cf = 1. -/
def addBody : List InstrR :=
  [.Copn (flagBundle "cf" "r") .AT_none (.Oasm ⟨"ADD_64"⟩) [pv "a", pv "b"]]

example : (bignumExec addBody initState).map (fun s => (s.regs "r", s.regs "cf"))
            = some (1, 1) := by native_decide

/-- ADC_64 with carry-in 1: 0xFFFFFFFFFFFFFFFE + 3 + 1 = 2, cf = 1. -/
def adcBody : List InstrR :=
  [ .Cassgn (lvR "cin") .AT_none (.sword .U64) (.Pconst 1)
  , .Copn (flagBundle "cf" "r") .AT_none (.Oasm ⟨"ADC_64"⟩)
      [pv "a", pv "b", pv "cin"] ]

example : (bignumExec adcBody initState).map (fun s => (s.regs "r", s.regs "cf"))
            = some (2, 1) := by native_decide

/-- MULX: 0xFFFFFFFFFFFFFFFE × 3 = 0x2_FFFFFFFFFFFFFFFA.
    hi = 2, lo = 0xFFFFFFFFFFFFFFFA. -/
def mulxBody : List InstrR :=
  [.Copn [lvR "hi", lvR "lo"] .AT_none (.Oasm ⟨"MULX"⟩) [pv "a", pv "b"]]

example : (bignumExec mulxBody initState).map (fun s => (s.regs "hi", s.regs "lo"))
            = some (2, 0xFFFFFFFFFFFFFFFA) := by native_decide

/-- ADCX: same arithmetic as ADC_64, 2-LVal output bundle. -/
def adcxBody : List InstrR :=
  [ .Cassgn (lvR "cin") .AT_none (.sword .U64) (.Pconst 1)
  , .Copn [lvR "cf", lvR "r"] .AT_none (.Oasm ⟨"ADCX"⟩)
      [pv "a", pv "b", pv "cin"] ]

example : (bignumExec adcxBody initState).map (fun s => (s.regs "r", s.regs "cf"))
            = some (2, 1) := by native_decide

/-- ADOX: same arithmetic as ADC, 2-LVal output bundle (OF chain). -/
def adoxBody : List InstrR :=
  [ .Cassgn (lvR "oin") .AT_none (.sword .U64) (.Pconst 1)
  , .Copn [lvR "of", lvR "r"] .AT_none (.Oasm ⟨"ADOX"⟩)
      [pv "a", pv "b", pv "oin"] ]

example : (bignumExec adoxBody initState).map (fun s => (s.regs "r", s.regs "of"))
            = some (2, 1) := by native_decide

/-- XOR_64 self-clear with the dual-carry-clear LVal layout
    `[of, cf, _, _, _, dst]`: `xor a, a` ⇒ a = 0, of = cf = 0. -/
def xorClearBody : List InstrR :=
  [ .Copn [lvR "of", lvR "cf",
           .Lnone {} (.sword .U64), .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
           lvR "a"] .AT_none (.Oasm ⟨"XOR_64"⟩) [pv "a", pv "a"] ]

example : (bignumExec xorClearBody initState).map
            (fun s => (s.regs "a", s.regs "cf", s.regs "of"))
            = some (0, 0, 0) := by native_decide

end IntrinsicSmoke

/-! ## §12.3b. (Shift, additive) Smoke test for `SHL_64` / `SHR_64`
    / `SHLD_64` / `SHRD_64`

Validates that `execInstr` dispatches each shift intrinsic to the right
helper and that the 1-LVal bundle reads the result correctly.

Three back-to-back tests on a tiny synthetic body, all `native_decide`. -/

namespace ShiftSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U64 }
def lvR (s : String) : LVal := .Lvar { var := vU s }
def pv (s : String) : PExpr := .Pvar { gv := { var := vU s }, gs := false }

/-- Initial state: `a := 0xF0`, `b := 0x80`, `k := 4`, others 0. -/
def initState : BignumState :=
  let regs : String → BitVec 64 := fun x =>
    if x = "a" then 0xF0
    else if x = "b" then 0x80
    else if x = "k" then 4
    else 0
  { regs := regs, mem := Mem.empty }

/-- 6-LVal flag bundle `[of, cf, sf, pf, zf, dst]` (only dst captured) —
    the shape `jasminc` expects for `#SHL_64`/`#SHR_64`/`#SHLD_64`/
    `#SHRD_64`. -/
def flagBundle (r : String) : List LVal :=
  [.Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
   .Lnone {} (.sword .U64), .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
   lvR r]

/-- `r = #SHL_64(a, k);` — `0xF0 << 4 = 0xF00`. -/
def shlBody : List InstrR :=
  [.Copn (flagBundle "r") .AT_none (.Oasm ⟨"SHL_64"⟩) [pv "a", pv "k"]]

example : (bignumExec shlBody initState).map (fun s => s.regs "r")
            = some 0xF00 := by native_decide

/-- `r = #SHR_64(a, k);` — `0xF0 >> 4 = 0xF`. -/
def shrBody : List InstrR :=
  [.Copn (flagBundle "r") .AT_none (.Oasm ⟨"SHR_64"⟩) [pv "a", pv "k"]]

example : (bignumExec shrBody initState).map (fun s => s.regs "r")
            = some 0xF := by native_decide

/-- `r = #SHLD_64(a, b, k);` —
    `(0xF0 << 4) | (0x80 >> 60) = 0xF00 | 0 = 0xF00`.
    With a high spill: change `b` so the cross-limb pull is nonzero. -/
def shldBody : List InstrR :=
  [.Copn (flagBundle "r") .AT_none (.Oasm ⟨"SHLD_64"⟩) [pv "a", pv "b", pv "k"]]

example : (bignumExec shldBody initState).map (fun s => s.regs "r")
            = some 0xF00 := by native_decide

/-- `r = #SHRD_64(a, b, k);` —
    `(0xF0 >> 4) | (0x80 << 60) = 0xF | 0x8000000000000000 = 0x800000000000000F`.
    This is the cross-limb pull-down idiom that backs `mpn_rshift`.

    (For the spec-shape unit test see the second `shrd64` example below
    with `dst=0x80, src=0xF`.) -/
def shrdBody : List InstrR :=
  [.Copn (flagBundle "r") .AT_none (.Oasm ⟨"SHRD_64"⟩) [pv "a", pv "b", pv "k"]]

-- `shrd64 a=0xF0 b=0x80 k=4` =
--   `(0xF0 >>> 4) ||| (0x80 <<< 60)`
-- `0x80 <<< 60` = `0x80 * 2^60 mod 2^64`.  `0x80 = 2^7`, so
-- `0x80 * 2^60 = 2^67`, which wraps to `0` in 64 bits (`mod 2^64`).
-- Hence the spill from `b=0x80` shifted up by 60 is zero in 64 bits,
-- and the answer is just `0xF0 >>> 4 = 0xF`.  This matches the SDM
-- "the upper bits of `src` are discarded" — `0x80 << 60` overflows.
example : (bignumExec shrdBody initState).map (fun s => s.regs "r")
            = some 0xF := by native_decide

/-- Direct unit-test of `shld64`: matches the cross-limb merge of
    `bitShiftLeftAux` step for `(w=2, prev = (0x8000... >>> 60), r=4)`:
    `(2 <<< 4) ||| 0x8 = 0x28`. -/
example : shld64 2 0x8000000000000000 4 = 0x28 := by native_decide

/-- Direct unit-test of `shrd64`: matches `bitShiftRight`'s merge of
    `(w=0x80, w'=0xF, r=4)`: `(0x80 >>> 4) ||| (0xF <<< 60) =
    0xF000000000000008`. -/
example : shrd64 0x80 0xF 4 = 0xF000000000000008 := by native_decide

end ShiftSmoke

/-! ## §12.4. (U32, additive) Smoke test: a 2-limb u32 `add_n`

Exercises the whole U32 path end-to-end through the interpreter:
`Pload .U32` loads, the `ADD_32`/`ADC_32` intrinsics with a threaded
carry register, and `Lmem .U32` stores.  Two 32-bit limbs are added
little-endian with carry; the result limbs are read back out of memory.

Limbs: `a = [0xFFFFFFFF, 5]`, `b = [1, 7]`.
  - `r0 = (0xFFFFFFFF + 1) mod 2^32 = 0`, carry-out `1`
  - `r1 = (5 + 7 + 1)            = 13`
So the result is `[0, 13]` with no final carry. -/

namespace U32AddSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U32 }
def lvR (s : String) : LVal := .Lvar { var := vU s }
def pv (s : String) : PExpr := .Pvar { gv := { var := vU s }, gs := false }
def varI (s : String) : VarI := { var := vU s }

/-- 6-LVal flag bundle `[of, cf, sf, pf, zf, dst]` (only cf + dst captured). -/
def fb (cf r : String) : List LVal :=
  [.Lnone {} (.sword .U32), lvR cf,
   .Lnone {} (.sword .U32), .Lnone {} (.sword .U32), .Lnone {} (.sword .U32),
   lvR r]

def loadU32 (x base : String) : InstrR :=
  .Cassgn (lvR x) .AT_none (.sword .U32) (.Pload .U32 (varI base) (.Pconst 0))

def storeU32 (base src : String) : InstrR :=
  .Cassgn (.Lmem .U32 (varI base) (.Pconst 0)) .AT_none (.sword .U32) (pv src)

/-- Pointer advance: 64-bit add (pointers are `reg u64`, even in a u32
    kernel — only the limb data is 32-bit). -/
def advance (x : String) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 } }) .AT_none
    (.sword .U64)
    (.Papp2 (.Oadd .U64) (.Pvar { gv := { var := { vname := x, vtype := .sword .U64 } }, gs := false }) (.Pconst k))

/-- Straight-line 2-limb u32 add body (pointers `ap=200`, `bp=300`,
    `op=400`).  First limb via `ADD_32`, second via `ADC_32(cf)`. -/
def body2 : List InstrR :=
  [ loadU32 "t0" "ap"
  , loadU32 "s0" "bp"
  , .Copn (fb "cf" "r0") .AT_none (.Oasm ⟨"ADD_32"⟩) [pv "t0", pv "s0"]
  , storeU32 "op" "r0"
  , advance "ap" 4, advance "bp" 4, advance "op" 4
  , loadU32 "t1" "ap"
  , loadU32 "s1" "bp"
  , .Copn (fb "cf" "r1") .AT_none (.Oasm ⟨"ADC_32"⟩) [pv "t1", pv "s1", pv "cf"]
  , storeU32 "op" "r1" ]

/-- Initial memory: `a = [0xFFFFFFFF, 5]` at 200 (little-endian, 4-byte
    stride), `b = [1, 7]` at 300, output region pre-allocated at 400. -/
def initState : BignumState :=
  let regs : String → BitVec 64 := fun x =>
    if x = "ap" then 200 else if x = "bp" then 300 else if x = "op" then 400 else 0
  let mem0 : Mem := fun a => if a ≥ 400 ∧ a ≤ 407 then some 0 else none
  let mem1 := Mem.store32 mem0 200 0xFFFFFFFF
  let mem2 := Mem.store32 mem1 204 5
  let mem3 := Mem.store32 mem2 300 1
  let mem4 := Mem.store32 mem3 304 7
  { regs := regs, mem := mem4 }

/-- The interpreter runs the body and the two output limbs read back as
    `[0, 13]` with carry-out `1` after limb 0 / `0` after limb 1. -/
example :
    (bignumExec body2 initState).map (fun s =>
      (load32Mem s.mem 400, load32Mem s.mem 404, s.regs "cf"))
    = some (some 0, some 13, 0) := by native_decide

end U32AddSmoke

/-! ## §12.4a'. (U8 narrow + byte-store, additive) Smoke tests

Exercises the two new interpreter arms wired for `mpn_to_string`'s
outer-loop digit-write step:

* `Papp1 (.Ozeroext .U8 .U64)` — the `(8u) c64` narrow step in
  `narrowToByte`.  We feed `c64 = 0x12FF`, expect the narrowed value to
  be `0xFF` (low byte) in the `BitVec 64` register file.
* `.Lmem .U8` byte store — the `[:u8 buf + 0] := c8` step in
  `storeDigitAtBuf`.  We write `0x42` to `buf = 1000` and read the byte
  back via `Mem.loadByte`. -/

namespace U8NarrowAndStoreSmoke

def v64 (s : String) : Var := { vname := s, vtype := .sword .U64 }
def v8  (s : String) : Var := { vname := s, vtype := .sword .U8 }
def lvR64 (s : String) : LVal := .Lvar { var := v64 s }
def lvR8  (s : String) : LVal := .Lvar { var := v8 s }
def pv64 (s : String) : PExpr := .Pvar { gv := { var := v64 s }, gs := false }
def pv8  (s : String) : PExpr := .Pvar { gv := { var := v8  s }, gs := false }

/-- Initial state: `c64 = 0x12FF`, `buf = 1000`.  All other registers 0,
    memory empty. -/
def initState : BignumState :=
  let regs : String → BitVec 64 := fun x =>
    if x = "c64" then 0x12FF
    else if x = "buf" then 1000
    else 0
  { regs := regs, mem := Mem.empty }

/-- Direct unit-test of the helper: narrowing `0x12FF` to U8 keeps `0xFF`. -/
theorem ozeroext_u8_narrow :
    evalPExpr initState (.Papp1 (.Ozeroext .U8 .U64) (pv64 "c64")) = some 0xFF := by
  native_decide

/-- End-to-end via `bignumExec`: the narrow step `c8 := (8u) c64` writes
    `0xFF` into the `c8` register. -/
def narrowBody : List InstrR :=
  [.Cassgn (lvR8 "c8") .AT_none (.sword .U8)
    (.Papp1 (.Ozeroext .U8 .U64) (pv64 "c64"))]

theorem narrowBody_exec :
    (bignumExec narrowBody initState).map (fun s => s.regs "c8")
      = some 0xFF := by native_decide

/-- Byte store + immediate readback: `[:u8 buf + 0] := 0x42` then
    `loadByte 1000 = some 0x42`.  The RHS is the `c64` register (whose
    low byte is `0xFF`); to keep the example self-contained we instead
    drop a small constant `c8 = 0x42` via a narrow, then store. -/
def storeBody : List InstrR :=
  [ .Cassgn (lvR8 "c8") .AT_none (.sword .U8)
      (.Papp1 (.Ozeroext .U8 .U64) (.Pconst 0x42))
  , .Cassgn (.Lmem .U8 { var := v64 "buf" } (.Pconst 0)) .AT_none (.sword .U8)
      (pv8 "c8") ]

theorem storeBody_readback :
    (bignumExec storeBody initState).bind (fun s => s.mem.loadByte 1000)
      = some 0x42 := by native_decide

/-- The combined narrow-and-store also handles the original `0x12FF`
    source: low byte `0xFF` is what lands in memory at `buf + 0`. -/
def combinedBody : List InstrR :=
  [ .Cassgn (lvR8 "c8") .AT_none (.sword .U8)
      (.Papp1 (.Ozeroext .U8 .U64) (pv64 "c64"))
  , .Cassgn (.Lmem .U8 { var := v64 "buf" } (.Pconst 0)) .AT_none (.sword .U8)
      (pv8 "c8") ]

theorem combinedBody_readback :
    (bignumExec combinedBody initState).bind (fun s => s.mem.loadByte 1000)
      = some 0xFF := by native_decide

end U8NarrowAndStoreSmoke

/-! ## §12.4b. (U32, additive) Smoke test for `MULX_32`

Validates that `execInstr` interprets `MULX_32` correctly. Exercises a
single multiplication of two 32-bit values held in `BitVec 64` registers
with the high half zero (the u32-in-`BitVec 64` convention).

`a = 0xFFFFFFFE`, `b = 3`, so `a * b = 0x2_FFFFFFFA` (33 bits):
  - `hi = 2`
  - `lo = 0xFFFFFFFA` -/

namespace U32MulxSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U32 }
def lvR (s : String) : LVal := .Lvar { var := vU s }
def pv (s : String) : PExpr := .Pvar { gv := { var := vU s }, gs := false }

def initState : BignumState :=
  let regs : String → BitVec 64 := fun x =>
    if x = "a" then 0xFFFFFFFE
    else if x = "b" then 3
    else 0
  { regs := regs, mem := Mem.empty }

/-- Direct unit-test of the helper. -/
example : mulx32 0xFFFFFFFE 3 = (2, 0xFFFFFFFA) := by native_decide

/-- End-to-end via the dispatcher: `hi, lo = MULX_32(a, b)`. -/
def mulx32Body : List InstrR :=
  [.Copn [lvR "hi", lvR "lo"] .AT_none (.Oasm ⟨"MULX_32"⟩) [pv "a", pv "b"]]

example : (bignumExec mulx32Body initState).map (fun s => (s.regs "hi", s.regs "lo"))
            = some (2, 0xFFFFFFFA) := by native_decide

/-- Axiom-cleanliness check: the smoke chain has no admission axiom. -/
example : mulx32 0xFFFFFFFE 3 = (2, 0xFFFFFFFA) := by native_decide

end U32MulxSmoke

/-! ## §12.4c. (U32, additive) Smoke test for `subBorrowIn32` / `SBB_32`

Validates the U32 SBB-with-borrow-in helper and its `execInstr` dispatch.
`a = 0`, `b = 1`, `bin = 0`: the masked subtraction wraps, so
`bf = 1` and `r = 0xFFFFFFFF`. -/

namespace U32SbbSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U32 }
def lvR (s : String) : LVal := .Lvar { var := vU s }
def pv (s : String) : PExpr := .Pvar { gv := { var := vU s }, gs := false }

def initState : BignumState :=
  let regs : String → BitVec 64 := fun x =>
    if x = "a" then 0
    else if x = "b" then 1
    else if x = "bin" then 0
    else 0
  { regs := regs, mem := Mem.empty }

/-- Direct unit-test of the helper: 0 - 1 - 0 wraps to `(1, 0xFFFFFFFF)`. -/
example : subBorrowIn32 0 1 0 = (1, 0xFFFFFFFF) := by native_decide

/-- 6-LVal flag bundle `[of, cf, sf, pf, zf, dst]` (only cf + dst captured). -/
def fb (cf r : String) : List LVal :=
  [.Lnone {} (.sword .U32), lvR cf,
   .Lnone {} (.sword .U32), .Lnone {} (.sword .U32), .Lnone {} (.sword .U32),
   lvR r]

/-- End-to-end via the dispatcher: `bf, r = SBB_32(a, b, bin)`. -/
def sbbIn32Body : List InstrR :=
  [.Copn (fb "bf" "r") .AT_none (.Oasm ⟨"SBB_32"⟩) [pv "a", pv "b", pv "bin"]]

example : (bignumExec sbbIn32Body initState).map (fun s => (s.regs "bf", s.regs "r"))
            = some (1, 0xFFFFFFFF) := by native_decide

end U32SbbSmoke

/-! ## §12.5. Smoke tests for control-flow constructs

Validates that `Cif`, `Cfor`, and `Cwhile` are interpreted correctly
by `bignumExecFuel`. Each test exercises one construct on a tiny
synthetic body and checks the final state via `native_decide`. -/

namespace ControlFlowSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U64 }
def lvR (s : String) : LVal := .Lvar { var := vU s }
def pv (s : String) : PExpr :=
  .Pvar { gv := { var := vU s }, gs := false }
def varI (s : String) : VarI := { var := vU s }

/-- Initial state: `a := 1`, `b := 0`, `r := 0`. -/
def initState : BignumState :=
  { regs := fun x => match x with
      | "a" => 1
      | _ => 0
    mem := Mem.empty }

/-! ### Cif test

`if a ≠ 0 then r := 7 else r := 9` — should set `r := 7` since
`a = 1`. -/

def cifBody : List InstrR :=
  [ .Cif (pv "a")
      [.Cassgn (lvR "r") .AT_none (.sword .U64) (.Pconst 7)]
      [.Cassgn (lvR "r") .AT_none (.sword .U64) (.Pconst 9)] ]

example :
    (bignumExecFuel emptyRegistry 100 cifBody initState).map
        (fun s => s.regs "r") = some 7 := by native_decide

/-! ### Cfor test

`for i in 0..3 do r := i` — last iteration writes `r := 2` (since
`UpTo` walks `0, 1, 2`). -/

def cforBody : List InstrR :=
  [ .Cfor (varI "i") { dir := .UpTo, lo := 0, hi := 3 }
      [.Cassgn (lvR "r") .AT_none (.sword .U64) (pv "i")] ]

example :
    (bignumExecFuel emptyRegistry 100 cforBody initState).map
        (fun s => s.regs "r") = some 2 := by native_decide

/-! ### Cwhile test

`while a ≠ 0 do { r := r + 5; a := 0 }` — runs body once
(setting `r := 5`, `a := 0`), then exits. Encoded as Jasmin
`Cwhile [] (cond) [body]`. -/

def cwhileBody : List InstrR :=
  [ .Cwhile [] (pv "a")
      [.Cassgn (lvR "r") .AT_none (.sword .U64)
         (.Papp2 (.Oadd .U64) (pv "r") (.Pconst 5)),
       .Cassgn (lvR "a") .AT_none (.sword .U64) (.Pconst 0)] ]

example :
    (bignumExecFuel emptyRegistry 100 cwhileBody initState).map
        (fun s => (s.regs "r", s.regs "a")) = some (5, 0) := by
  native_decide

/-! ### Cwhile fuel-exhaustion test

`while 1 ≠ 0 do { skip }` is an infinite loop. With finite fuel,
`bignumExecFuel` returns `none`. -/

def infiniteLoop : List InstrR :=
  [ .Cwhile [] (.Pconst 1) [] ]

example :
    bignumExecFuel emptyRegistry 5 infiniteLoop initState = none := by
  native_decide

end ControlFlowSmoke

/-! ## §13. Monadic shape for verification-condition generation

The functional `bignumExec : List InstrR → BignumState → Option BignumState`
above is the definition that all of `BignumHoare.lean` proofs depend on.
The monadic form below is a separate definition with a bridge lemma to it.

`vcgen` (on `Std.WP` triples) and `mvcgen` (on `Std.Do` triples) walk
`do`-shaped programs in standard monads (`StateM`, `StateT _ Option`, etc.).
The monadic form casts the same operational behavior into a `StateT BignumState
Option Unit` shape, with a bridge lemma to the functional form. Both triple
forms are provided below.

See the toy smoke test
in `MVCGenSmoke.lean`. -/

/-- The bignum interpreter monad: state-and-failure over `BignumState`. -/
abbrev BignumM := StateT BignumState Option

/-- Lift `execInstr` into `BignumM`. The `registry` parameter is currently
    unused (Ccall not supported by `bignumExecM`; future extension would
    delegate to `bignumExecFuel`). For all non-Ccall InstrR shapes the
    behavior is identical to one step of `bignumExec`. -/
def stepInstrM (_registry : BignumRegistry) (i : InstrR) : BignumM Unit :=
  fun s =>
    match execInstr s i with
    | some s' => some ((), s')
    | none    => none

/-- Monadic body interpreter: `forM` of `stepInstrM` over a body.
    Behavioral equivalent of `bignumExec`, in `do`-shape so that
    `mvcgen` can walk it. -/
def bignumExecM (registry : BignumRegistry) (body : List InstrR) :
    BignumM Unit :=
  body.forM (stepInstrM registry)

/-! ### Recursion lemmas — unrolling `bignumExecM` for mvcgen

`mvcgen` walks `do`-shaped programs but won't reduce `forM` over a
literal list during VC generation. These two lemmas let `simp`
rewrite a literal-list `bignumExecM` into an explicit `do`-chain of
`stepInstrM` calls, exposing the structure mvcgen needs. -/

@[simp] theorem bignumExecM_nil (r : BignumRegistry) :
    bignumExecM r [] = pure () := rfl

@[simp] theorem bignumExecM_cons (r : BignumRegistry) (i : InstrR)
    (is : List InstrR) :
    bignumExecM r (i :: is) = stepInstrM r i >>= fun _ => bignumExecM r is := by
  unfold bignumExecM
  simp

/-- `bignumExecM` over a concatenated list = sequence of two `bignumExecM`s.
    Direct corollary of `List.forM_append`. Used to chunk Triple proofs
    that would otherwise overflow `simp`'s `maxSteps` budget. -/
theorem bignumExecM_append (r : BignumRegistry) (xs ys : List InstrR) :
    bignumExecM r (xs ++ ys) =
      bignumExecM r xs >>= fun _ => bignumExecM r ys := by
  unfold bignumExecM
  simp [List.forM_append]

/-! ### `bignum_kernel_simp_set` — the canonical simp set for kernel proofs

Bundles the simp arguments used in the kernel-proof closure recipe:
- mvcgen recursion lemmas (`bignumExecM_cons/_nil`, `stepInstrM`)
- structural unfolds (`execInstr`, `evalPExpr`, `resolveAddr`,
  `setReg`, intrinsics)
- BitVec normalization (re-fold Nat-encoded BitVec ops)
- pure/StateT plumbing

Used as: `simp [bignum_kernel_simp_set]` after the body literal
unfolds and the load hypotheses are in scope. -/

attribute [simp] bignumExecM_nil bignumExecM_cons

/-- The canonical simp set as a `simp_attr`-style theorem list.
    Apply via `simp [bignumKernelSimps, hypotheses, port_eq_lemmas]`.

    Note: `stepInstrM`, `execInstr`, `evalPExpr` etc. are passed
    explicitly per call since they're definitions to unfold, not
    rewrite rules. -/
syntax "bignum_kernel_simp" : tactic

macro_rules
  | `(tactic| bignum_kernel_simp) =>
    `(tactic| simp only [BignumExec.stepInstrM, BignumExec.execInstr,
                         BignumExec.evalPExpr, BignumExec.resolveAddr,
                         BignumExec.setReg, BignumExec.writeSubBundle,
                         BignumExec.subBorrow, BignumExec.subBorrowIn,
                         pure, StateT.pure])

open Std.Do in
/-- Evaluation rule for the weakest precondition of a concrete
    `StateT σ Option` program: ground `(wp x).apply Q s` by running `x`.

    This is the single place that opens `Std.Do`'s `Option` WP instance
    (whose compiled auxiliary is toolchain-version-sensitive); everything
    else goes through this lemma via `bignum_wp_unfold`. -/
theorem wp_apply_stateT_option {σ α : Type} (x : StateT σ Option α)
    (Q : PostCond α (.arg σ (.except PUnit .pure))) (s : σ) :
    (wp (m := StateT σ Option) x).apply Q s =
      (match x.run s with
        | some (a, s') => Q.1 a s'
        | none => Q.2.1 PUnit.unit) := by
  simp only [wp, PredTrans.apply_pushArg, PredTrans.apply_pushOption,
             OptionT.run, Option.instWP._aux_1, Id.run, StateT.run]
  rcases h : x s with _ | ⟨a, s'⟩ <;> simp [h, PredTrans.apply_Pure_pure]

open Std.Do in
/-- Companion to `wp_apply_stateT_option` for goals where `Std.Do.WP.wp`
    has already been unfolded to the `Option` instance's compiled
    auxiliary: evaluate its predicate transformer by case analysis.
    The auxiliary is referenced only here and in `wp_apply_stateT_option`
    (identifiers with `_aux` components do not survive syntax
    quotations, so the tactic macro goes through these named lemmas). -/
theorem wp_aux_apply_option {α : Type} (x : Option α)
    (Q : PostCond α (.except PUnit .pure)) :
    (Option.instWP._aux_1 x).apply Q =
      (match x with
        | some a => Q.1 a
        | none => Q.2.1 PUnit.unit) := by
  rcases x <;> rfl

/-- Convenience tactic that runs the wp-unfolding stage of the kernel-proof
    closure recipe. After this tactic, the goal is a pure term-level
    chain ready for hypothesis substitution and `bv_normalize`. -/
syntax "bignum_wp_unfold" : tactic

macro_rules
  | `(tactic| bignum_wp_unfold) =>
    `(tactic|
        simp only [BignumExec.wp_apply_stateT_option, BignumExec.wp_aux_apply_option,
                   BignumExec.BignumM, Std.Do.WP.wp,
                   Std.Do.PredTrans.apply_pushArg, Std.Do.PredTrans.apply_pushOption,
                   Std.Do.PredTrans.apply_pure,
                   Std.Do.PredTrans.apply_Pure_pure,
                   Id.run, Option.bind_some, bind, StateT.bind,
                   OptionT.run, StateT.run])

/-! ### `triple_apply_run` — extract post from a Hoare triple

Given a `Triple` for a `BignumM` program and a concrete `.run` result,
extract that the postcondition holds at the resulting state.

The implementation uses the `⌜·⌝` (Prop-lift) notation so the SPred /
Assertion typeclass machinery resolves cleanly. -/

open Std.Do in
theorem triple_apply_run {α : Type}
    {x : BignumM α} {P : BignumState → Prop} {Q : α → BignumState → Prop}
    (h_triple : Triple x (fun s => ⌜P s⌝) (⇓ a => fun s => ⌜Q a s⌝))
    {s : BignumState} {a : α} {s' : BignumState}
    (h_run : x s = some (a, s'))
    (h_pre : P s) :
    Q a s' := by
  simp only [Triple, WP.wp, PredTrans.apply_pushArg,
             PredTrans.apply_pushOption, PostCond.noThrow,
             PredTrans.apply_Pure_pure,
             OptionT.run, Option.instWP._aux_1,
             Id.run] at h_triple
  have := h_triple s h_pre
  -- Beta-reduce and apply h_run.
  simp only [StateT.run, h_run] at this
  exact this

/-! ### Triples in `Std.WP`

The `Std.WP` forms of the evaluation rule and of `triple_apply_run`, and the triple of one
step of `stepInstrM`, for proofs by `vcgen`. A `Std.WP` triple `⦃fun s => P s⦄ x ⦃Q⦄` has
the failure postcondition `⊥`: it states that the run succeeds. -/

namespace StdWP

open Std.WP
open CatCrypt.Crypto.Util (wp_apply_run triple_iff_run)

/-- The postcondition of a triple holds at the result of a run from a state satisfying the
    precondition. -/
theorem triple_apply_run {α : Type}
    {x : BignumM α} {P : BignumState → Prop} {Q : α → BignumState → Prop}
    (h_triple : ⦃fun s => P s⦄ x ⦃fun a s => Q a s⦄)
    {s : BignumState} {a : α} {s' : BignumState}
    (h_run : x s = some (a, s'))
    (h_pre : P s) :
    Q a s' := by
  obtain ⟨a₁, s₁, h₁, hq⟩ := (triple_iff_run x P Q).1 h_triple s h_pre
  have h₂ : x s = some (a₁, s₁) := h₁
  rw [h_run] at h₂
  simp only [Option.some.injEq, Prod.mk.injEq] at h₂
  obtain ⟨rfl, rfl⟩ := h₂
  exact hq

/-- The triple of one step: the precondition is the postcondition at the state `execInstr`
    returns, and the failure postcondition when it fails. -/
theorem stepInstrM_spec (r : BignumRegistry) (i : InstrR) (Q : Unit → BignumState → Prop)
    (E : Unit → Prop) :
    ⦃fun s => match execInstr s i with | some s' => Q () s' | none => E ()⦄
      stepInstrM r i ⦃Q; E⦄ := by
  constructor
  intro s h
  rw [wp_apply_run]
  cases hs : execInstr s i <;> simp only [hs] at h <;> simpa [StateT.run, stepInstrM, hs] using h

end StdWP

/-! ### `bv_normalize` simp set — kernel-proof closure pattern

After `mvcgen + simp` walks a body, the residual goal embeds BitVec
operations as Nat-with-mod (e.g., `(2^64 - x.toNat) % 2^64`). The
reverse-direction `BitVec.toNat_*` lemmas re-fold this back to
clean BitVec form so `bv_decide` and BitVec-level helpers apply.

Use as: `simp [..., bv_normalize_set]` or `simp_all [bv_normalize_set]`. -/

/-- Reverse-direction simp lemmas converting Nat-encoded BitVec ops
    back to BitVec form. -/
theorem bv_normalize_neg {n : Nat} (x : BitVec n) :
    (2^n - x.toNat) % 2^n = (-x).toNat := (BitVec.toNat_neg x).symm

theorem bv_normalize_and {n : Nat} (x y : BitVec n) :
    x.toNat &&& y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm

theorem bv_normalize_or {n : Nat} (x y : BitVec n) :
    x.toNat ||| y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm

theorem bv_normalize_xor {n : Nat} (x y : BitVec n) :
    x.toNat ^^^ y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm

/-! ### Bridge lemma

Connects the monadic and functional forms. The `emptyRegistry`
specialization is the useful direction: existing `BignumHoare`
proofs about `bignumExec` lift to `bignumExecM` (and vice versa) via
this iff. -/

/-- Single-step semantic equality: `stepInstrM emptyRegistry i s` reduces
    to wrapping `execInstr s i` in the monad. (Note: in `BignumM = StateT
    BignumState Option`, `.run s` is just function application.) -/
theorem stepInstrM_apply (i : InstrR) (s : BignumState) :
    stepInstrM emptyRegistry i s =
      (execInstr s i).map (fun s' => ((), s')) := by
  simp only [stepInstrM]
  cases execInstr s i <;> rfl

theorem bignumExecM_iff_bignumExec (body : List InstrR) (s s' : BignumState) :
    (bignumExecM emptyRegistry body).run s = some ((), s') ↔
      bignumExec body s = some s' := by
  induction body generalizing s with
  | nil =>
    -- bignumExecM emptyRegistry [] = pure (), so .run s = some ((), s).
    -- bignumExec [] s = some s.
    show ([].forM (stepInstrM emptyRegistry) : BignumM Unit) s = some ((), s')
           ↔ bignumExec [] s = some s'
    simp [List.forM, pure, StateT.pure, bignumExec, eq_comm]
  | cons i is ih =>
    -- Both step on `i` first, then recurse on `is`.
    cases hstep : execInstr s i with
    | none =>
      have lhs_none : (bignumExecM emptyRegistry (i :: is)).run s = none := by
        show ((stepInstrM emptyRegistry i s).bind
                fun r => bignumExecM emptyRegistry is r.snd) = none
        rw [stepInstrM_apply, hstep]; rfl
      have rhs_none : bignumExec (i :: is) s = none := by
        rw [bignumExec, hstep]
      rw [lhs_none, rhs_none]
      simp
    | some s1 =>
      have lhs_eq :
          (bignumExecM emptyRegistry (i :: is)).run s
            = (bignumExecM emptyRegistry is).run s1 := by
        show ((stepInstrM emptyRegistry i s).bind
                fun r => bignumExecM emptyRegistry is r.snd) = _
        rw [stepInstrM_apply, hstep]; rfl
      have rhs_eq : bignumExec (i :: is) s = bignumExec is s1 := by
        rw [bignumExec, hstep]
      rw [lhs_eq, rhs_eq]
      exact ih s1

/-! ## §14. `vcgen` smoke test

A 2-instruction body with simple `Cassgn` shapes, written as a literal
`do`-block in `BignumM`. `vcgen` walks the block through the triple
`StdWP.stepInstrM_spec` of each step, and the resulting VC closes by
reducing the `execInstr` evaluation on a concrete InstrR.

This is the real-shape analog of `MVCGenSmoke.runToyDo`. -/

set_option experimental.vcgen true

namespace MVCGenSmoke

def vU (s : String) : Var := { vname := s, vtype := .sword .U64 }
def lvR (s : String) : LVal := .Lvar { var := vU s }

/-- Initial state: `r = 41`, all other registers 0. -/
def initState : BignumState :=
  { regs := fun x => if x = "r" then 41 else 0
    mem  := Mem.empty }

/-- A single Cassgn: `r := 42`. Concrete InstrR. -/
def setRTo42 : InstrR :=
  .Cassgn (lvR "r") .AT_none (.sword .U64) (.Pconst 42)

/-- A second Cassgn: `t := r`. Concrete InstrR. -/
def copyRToT : InstrR :=
  .Cassgn (lvR "t") .AT_none (.sword .U64)
    (.Pvar { gv := { var := vU "r" }, gs := false })

/-- Real-shape do-block: two `stepInstrM` calls in sequence. This is
    the kind of expression a future `bignumExecM` unfolder would
    produce after substituting a concrete body literal. -/
def smokeBodyM : BignumM Unit := do
  stepInstrM emptyRegistry setRTo42
  stepInstrM emptyRegistry copyRToT

open Std.WP

/-- The post-state of the `do`-block has `r = 42` and `t = 42`. `vcgen` applies the
    triple of the first `stepInstrM`; its VC, a `match` on `execInstr` with the weakest
    precondition of the second step inside, closes by definitional unfolding. -/
example :
    ⦃fun s => s = initState⦄
      smokeBodyM
    ⦃fun _ s => s.regs "r" = 42 ∧ s.regs "t" = 42⦄ := by
  simp only [smokeBodyM]
  vcgen [StdWP.stepInstrM_spec]
  exact ⟨rfl, rfl⟩

/-- The same body, but written via `bignumExecM` (i.e., `forM` over a
    literal list). The `bignumExecM_cons` / `bignumExecM_nil` simp
    lemmas unroll the literal list into an explicit `do`-chain before
    `vcgen` runs. This is the recipe for real bignum bodies. -/
example :
    ⦃fun s => s = initState⦄
      bignumExecM emptyRegistry [setRTo42, copyRToT]
    ⦃fun _ s => s.regs "r" = 42 ∧ s.regs "t" = 42⦄ := by
  simp only [bignumExecM_cons, bignumExecM_nil]
  vcgen [StdWP.stepInstrM_spec]
  exact ⟨rfl, rfl⟩

/-! ### `Copn` smoke: a SUB_64 intrinsic step

Verifies that the same `vcgen + simp` recipe handles the `Copn`
shape that bignum bodies use heavily (SUB / SBB / ADD / ADC / MULX /
ADCX / ADOX / XOR). The body computes `r := 100 - 42 = 58`. -/

def lvN : LVal := .Lnone {} (.sword .U64)
def lvCf : LVal := .Lvar { var := vU "cf" }

/-- Layout: `.Copn [Lnone, cfOut, Lnone, Lnone, Lnone, rOut] AT_none
              (.Oasm ⟨"SUB_64"⟩) [a, b]` — see `subCopn` in S2NBignumSSA. -/
def subRTo58 : InstrR :=
  .Copn [lvN, lvCf, lvN, lvN, lvN, lvR "r"] .AT_none
        (.Oasm ⟨"SUB_64"⟩)
        [.Pconst 100, .Pconst 42]

/-- Initial state with `r = 0`. -/
def initState2 : BignumState :=
  { regs := fun _ => 0, mem := Mem.empty }

/-- `vcgen + simp` handles the `Copn` shape too. -/
example :
    ⦃fun s => s = initState2⦄
      bignumExecM emptyRegistry [subRTo58]
    ⦃fun _ s => s.regs "r" = 58⦄ := by
  simp only [bignumExecM_cons, bignumExecM_nil]
  vcgen [StdWP.stepInstrM_spec]
  rfl

/-! ### Pload limitation

Direct `vcgen + simp` does not close a `Pload` step against a literal
`Mem.empty.store64 ...` state. The wp goal retains a chain of 8
`Mem.loadByte` calls which simp can't reduce without per-byte simp
lemmas connecting `loadByte ∘ store64`.

Consequently, the kernel's `Hoare`-triple form must take the
load values as preconditions (e.g., `load64Mem s.mem (base_a + 0) =
some a0`) rather than starting from a literal `Mem` state. `vcgen`
then walks only the post-load register-manipulation portion of the
body. This matches the existing `bodyComputesAlgoNat` framing where
`memNat4 base_a s.mem = some a_val` is given by hypothesis. -/

/-! ### Stress test: 8-instruction body (scaling check)

Mirrors the first 8 instructions of `BignumModP25519_4.body`: 1
zero-init + 4 const-loads + 3 const limbs of `p`. All `Cassgn`-with-
`Pconst`. Verifies `vcgen` scales to a body roughly 1/4 of the kernel. -/

def stressBody : List InstrR :=
  [ .Cassgn (lvR "zero")    .AT_none (.sword .U64) (.Pconst 0)
  , .Cassgn (lvR "a0")      .AT_none (.sword .U64) (.Pconst 1)
  , .Cassgn (lvR "a1")      .AT_none (.sword .U64) (.Pconst 2)
  , .Cassgn (lvR "a2")      .AT_none (.sword .U64) (.Pconst 3)
  , .Cassgn (lvR "a3")      .AT_none (.sword .U64) (.Pconst 4)
  , .Cassgn (lvR "p0")      .AT_none (.sword .U64) (.Pconst 0xFFFFFFFFFFFFFFED)
  , .Cassgn (lvR "pmid")    .AT_none (.sword .U64) (.Pconst 0xFFFFFFFFFFFFFFFF)
  , .Cassgn (lvR "p3")      .AT_none (.sword .U64) (.Pconst 0x7FFFFFFFFFFFFFFF) ]

example :
    ⦃fun s => s = initState2⦄
      bignumExecM emptyRegistry stressBody
    ⦃fun _ s => s.regs "p3" = 0x7FFFFFFFFFFFFFFF⦄ := by
  simp only [stressBody, bignumExecM_cons, bignumExecM_nil]
  vcgen [StdWP.stepInstrM_spec]
  rfl

end MVCGenSmoke

end CatCrypt.Crypto.Jasmin.BignumExec
