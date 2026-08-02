/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.SecureCompilation.CryptoSSA
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# CatCrypt VIR dialect

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A `VIR.Dialect` whose `Op`/`Ty` mirror CryptoSSA's `CExpr`/`CryptoTy`.
Target for `CProg → Com` structural translation.

## Pure-only

VIR's current denotation is pure (no `SPComp`). So the dialect here is
restricted to CryptoSSA's *pure* subset: `sampleBit`/`sampleBv` are
excluded. The translation `CryptoToVIR.lean` returns `none` on those.

Later: extend VIR with effectful denotation to cover the full CryptoSSA.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (SimdOp)

/-! ## 1. Op tags -/

/-- Operation tags for the CatCrypt dialect. Each constructor corresponds
    to a pure `CExpr` case from `CryptoSSA.lean`. Ops with static data
    (constants, indices) carry it as a parameter. -/
inductive CatCryptOp where
  -- Bit operations
  | constBit (v : Bool)
  | constUnit
  | xor
  | and
  | or
  | not
  | eqBit
  -- Pair/Sum
  | mkPair (a b : CryptoTy)
  | fst (a b : CryptoTy)
  | snd (a b : CryptoTy)
  | inl (a b : CryptoTy)
  | inr (a b : CryptoTy)
  -- BitVec
  | bvConst (w : Nat) (v : BitVec w)
  | bvXor (w : Nat)
  | bvAnd (w : Nat)
  | bvOr (w : Nat)
  | bvNot (w : Nat)
  | bvAdd (w : Nat)
  | bvSub (w : Nat)
  | bvMul (w : Nat)
  | bvEq (w : Nat)
  | bvShiftL (w : Nat) (k : Nat)
  | bvShiftR (w : Nat) (k : Nat)
  -- Word/crypto rotates and shifts (SHA/Keccak/ChaCha/bignum). These make the
  -- word-native primitives express *faithfully* in the dialect (rather than as
  -- opaque `extCall` leaves), and — for those with a scalar-jasmin twin — lower
  -- through `DialectToJasminCom`.
  -- `bvRor w n` / `bvRol w n`: rotate by a compile-time immediate `n`. `bvRor`
  -- denotes `BitVec.rotateRight` (SHA-512 Σ/σ, Keccak ρ, ChaCha diagonal
  -- rotates) and lowers to jasmin `rorImm w n`. `bvRol` denotes
  -- `BitVec.rotateLeft`; jasmin has no native scalar left-rotate op, so it is
  -- denote-only in the seam (see `DialectToJasminCom`).
  | bvRor (w : Nat) (n : Nat)
  | bvRol (w : Nat) (n : Nat)
  -- `bvShiftRA w n`: arithmetic (sign-extending) right shift by a compile-time
  -- immediate `n`, `out = src.sshiftRight n`. The signed twin of `bvShiftR`
  -- (ML-DSA `reduce32`/`montgomery_reduce`/`decompose`). Lowers to jasmin
  -- `sarImm w n`.
  | bvShiftRA (w : Nat) (n : Nat)
  -- `andn w`: BMI1 `(~~~a) &&& b` in ONE op, the Keccak χ idiom
  -- `B[x] ^ ((¬B[x+1]) ∧ B[x+2])` without a separate `bvNot`. Lowers to jasmin
  -- `regArith .andn w`.
  | andn (w : Nat)
  -- `bvShiftLV w` / `bvShiftRV w`: *variable*-amount logical shifts — the shift
  -- count is the `.toNat` of a *second* `sword w` register operand (not a
  -- compile-time immediate like `bvShiftL`/`bvShiftR`). They lower to jasmin
  -- `regArith .shl w` / `regArith .shr w`, whose `JasminBinOp.apply` reads the
  -- shift amount from `b.toNat`.
  | bvShiftLV (w : Nat)
  | bvShiftRV (w : Nat)
  -- Add-with-carry-out (multi-output ADD/ADC). `bvAdd64 w` takes `(a, b)`
  -- and returns the pair `(cout, sum)` where `cout : BitVec w` is `1` on
  -- carry-out else `0`. `bvAdc w` additionally takes a carry-in
  -- `cin : BitVec w` (non-zero ↦ true). These mirror `CExpr.bvAdd64`/
  -- `CExpr.bvAdc` exactly (Jasmin's `#ADD_64`/`#ADC_64`), and their pure
  -- denotation is the full `BitVec.adc` carry chain — the central op for
  -- the bignum ALU spine over `runBlock`/`Com`.
  | bvAdd64 (w : Nat)
  | bvAdc (w : Nat)
  -- Bignum ALU word splits (the single-word twins of `bvAdd64`/`bvAdc`). These
  -- mirror `ThirOp.thMulHi`/`thAddCarryLo`/`thAddCarryHi` exactly and lower
  -- 1:1 to the jasmin `mulhi`/`addCarryLo`/`addCarryHi` ops (x86 `MULX`/
  -- `ADCX`/`ADOX`).
  --
  -- `bvMulHi w`: the high word of the full unsigned product `a * b` — the `hi`
  -- output of `MULX` (`= (a.toNat * b.toNat) / 2 ^ w`). The low word is the
  -- existing `bvMul w`; together they are MULX's `(hi, lo)`. Lowers to jasmin
  -- `mulhi w`.
  | bvMulHi (w : Nat)
  -- `bvAddCarryLo w`: the **data** word of one carry-chain add `a + b + cin`
  -- (`cin : sword 1`, a 1-bit register threading the carry chain). The data
  -- effect of `ADCX`/`ADOX`. Lowers to jasmin `addCarryLo w`.
  | bvAddCarryLo (w : Nat)
  -- `bvAddCarryHi w`: the **carry-out** bit of one carry-chain add
  -- `a + b + cin`, packaged as a `sword 1` so it threads into the next limb's
  -- `bvAddCarryLo`/`bvAddCarryHi` as the carry-in. Lowers to jasmin
  -- `addCarryHi w`.
  | bvAddCarryHi (w : Nat)
  -- Conditionals
  | ite (t : CryptoTy)
  -- Bit-to-BitVec extension: `c ↦ if c then allOnes else 0`. Standard
  -- mask source for branch-free cmov on `.sword n`. In LLVM this lowers
  -- to `(0 - sextend(c)) : iN` (or `arith.extsi i1 → iN` followed by a
  -- negate, depending on whether the target prefers signed or unsigned
  -- extension; both produce the same allOnes-or-zero pattern).
  | bitToSword (n : Nat)
  -- Memrefs
  | memrefZero (n : Nat)
  | memrefSet (n : Nat) (i : Fin n)
  | memrefGet (n : Nat) (i : Fin n)
  -- Dynamic-index (runtime-index) memref ops. Unlike `memrefSet`/`memrefGet`,
  -- whose index is a compile-time `Fin n`, these take the index as a runtime
  -- `sword 64` operand value, so they slot directly onto the jasmin
  -- `stackLoad`/`stackStore` ops (which carry a `reg 64` index register). The
  -- access is total (index reduced modulo `n`, `0`-array on `n = 0`), matching
  -- the byte-offset machine model the x86 SIB `(%base,%idx,scale)` effective
  -- address realises after the in-range mask. The dialect-native images of
  -- `CExpr.memrefGetDyn`/`CExpr.memrefSetDyn`; they unblock per-iteration matrix
  -- selection (MAYO/UOV/ML-KEM) where the index is a loop variable.
  | memrefSetDyn (n : Nat)
  | memrefGetDyn (n : Nat)
  -- `memrefGetDyn128 n`: the **128-bit** dynamic-index memref load — the 128-bit
  -- twin of `memrefGetDyn`. The array is a `.memref n` (a `Fin n → BitVec 64`
  -- limb store) and the index is a runtime `.sword 64`, but the value read is a
  -- 128-bit register (`.sword 128`): a 128-bit XMM load at 128-bit granularity
  -- reads the two consecutive limbs `2k`, `2k+1` and packs them little-endian
  -- (`lo ||| hi <<< 64`), exactly the x86 byte-offset model of a `vmovdqu
  -- (%base,%idx,16)` gather. This is the front enabler for the FAEST per-index
  -- `acc ^= bf128_mul(x[i], alpha_i)` shape — a rolled loop over a 128-bit array
  -- with a per-index 128-bit dynamic load feeding a GF(2^128) `clmul`
  -- accumulate. Added ADDITIVELY (a distinct ctor, NOT widening `memrefGetDyn`,
  -- whose `.sword 64` return the whole scalar path depends on). It does not lower
  -- through `cryptoDialectToJasminCom` (jasmin `stackLoad` is width-matched to
  -- the array's element type, so a 128-bit gather from a 64-bit-element stack
  -- array has no single jasmin op — the honest byte-emit residual, as with the
  -- SHA-NI ops); it reaches the dialect with a faithful denote.
  | memrefGetDyn128 (n : Nat)
  -- External oracle call (e.g., `fp_mul`, `fp_add`). Signature is
  -- specified by the `argTys`/`retTy` fields. In MLIR this emits as
  -- `func.call @<name>(args) : (argTys) -> retTy`.
  | extCall (name : String) (argTys : List CryptoTy) (retTy : CryptoTy)
  -- Sampling (the probabilistic / security ops, folded in from `CryptoSSA` so the
  -- crypto dialect is the single SSA IR — DR collapse). The dialect carries TWO
  -- interpretations: the pure compile denotation (`catCryptDenote`, below) treats a
  -- sample as a deterministic zero-entropy leaf (the real deterministic-RNG-leaf
  -- meaning is `RngLeaf`); the probabilistic meaning is the separate `SPComp`-valued
  -- security interpretation `catCryptDenoteSP`. Per the DR principle, probability is
  -- an interpretation, not a compile-path op.
  | sampleBit
  | sampleBv (n : Nat)
  -- 128-bit SIMD ops (SIMD Tier-3 FRONT gap). The front dialect carries a 128-bit
  -- vector value as `.sword 128` (`mapTy .sword 128 = .reg 128`), and reuses the
  -- backend `SimdOp` alphabet (`JasminDialect`) directly: `SimdOp.denote` IS the
  -- lane semantics (no new `CryptoTy.vec` type needed). These lower 1:1 through
  -- `DialectToJasminCom.toJExprD` to the matching `JasminOp.vsimd`/`vpsrldq`/
  -- `vpslldq`, so the 128-bit vsimd kernels re-source as `Com catCryptDialect`
  -- through the verified `cryptoDialectToJasminCom` lowering + the vsimd
  -- auto-allocator, instead of a hand-authored `Com jasminDialect`.
  --
  -- `vsimd op`: a BINARY 128-bit SIMD op (both operands `.sword 128`). Used for the
  -- binary `SimdOp`s (`gf2p8mulb`/`vpshufb`/`clmul`/`affineqb`/`bitwise`/`packed`/
  -- `mulhi16`/`vaesenc`/`vaesenclast`); the two UNARY `SimdOp`s (`vpshufd`/
  -- `vaeskeygen`) use the dedicated unary constructors below (the front sig would
  -- otherwise disagree with the jasmin `op.argTys` arity).
  | vsimd (op : SimdOp)
  -- `vpshufdC imm`: `VPSHUFD src, imm8` (per-lane dword shuffle), UNARY. Lowers to
  -- `JasminOp.vsimd (.vpshufd imm)`; denote = `SimdOp.denote (.vpshufd imm)` (unary).
  | vpshufdC (imm : Nat)
  -- `vaeskeygenC rcon`: `VAESKEYGENASSIST src, imm8` (key-schedule assist), UNARY.
  -- Lowers to `JasminOp.vsimd (.vaeskeygen rcon)`.
  | vaeskeygenC (rcon : BitVec 8)
  -- `vpsrldqC n` / `vpslldqC n`: whole-128-bit byte-shift right/left by `n` bytes
  -- (`src >>> n*8` / `src <<< n*8`), UNARY. These are `JasminOp` (not `SimdOp`)
  -- constructors on the backend, so they get dedicated front ops lowering 1:1 to
  -- `JasminOp.vpsrldq n` / `JasminOp.vpslldq n`.
  | vpsrldqC (n : Nat)
  | vpslldqC (n : Nat)
  -- `vconst128 val`: a BAKED 128-bit immediate materialized into an XMM register
  -- (NULLARY). Lets a SIMD kernel bake a compile-time 128-bit constant (the FAEST
  -- GF(2^128) reduction modulus / `alpha_i`, an AES round constant, a `vpshufb`
  -- shuffle mask) directly, instead of ABI-loading it as a `.sword 128` parameter.
  -- Denotes to `val`. Lowers to `JasminOp.regConst 128 val.toNat` (the existing
  -- 128-bit-wide immediate op), which the owned vsimd printer renders as a
  -- `movabsq`/`vmovq`/`vpinsrq` two-64-bit-half XMM build (no `.rodata` pool).
  | vconst128 (val : BitVec 128)
  -- `vsha256rnds2`: `SHA256RNDS2` — advance SHA-256 state by two compression
  -- rounds. TERNARY: `(abef, cdgh, mk)` all `.sword 128`; result `.sword 128`.
  -- Denote = `vsha256rnds2W`. (Reaching x86 bytes needs a faithful SIMD backend
  -- target + the implicit-`%xmm0` mk staging — deferred; see `DialectToJasminCom`.)
  | vsha256rnds2
  -- `vsha256msg1`/`vsha256msg2`: the SHA-256 message-schedule steps. BINARY
  -- (`.sword 128 × 2` → `.sword 128`). Denote = `vsha256msg1W`/`vsha256msg2W`.
  | vsha256msg1
  | vsha256msg2
  deriving DecidableEq

/-! ## 2. The dialect -/

/-- The CatCrypt dialect: Ops are `CatCryptOp`, Ty is `CryptoTy`. -/
@[reducible] def catCryptDialect : Dialect :=
  { Op := CatCryptOp, Ty := CryptoTy }

/-- TyDenote for CryptoTy uses the existing `CryptoTy.denote`. -/
@[reducible] instance : TyDenote CryptoTy where
  denote := CryptoTy.denote

/-! ### Total runtime-index memref access

`Fin`-indexed access reduced modulo `n`, total even for `n = 0`. These are the
dialect-side mirror of `JasminDialect.stackGet`/`stackSet` (defined identically,
so the lowering is a `rfl`-level match); kept here so `CatCryptDialect` does not
need to import `JasminDialect` (the dialects must not cycle). -/

/-- Read element `k mod n` of a memref; `0` for an empty memref. The runtime-index
    twin of `memrefGet`'s `Fin n` access. -/
def memGetDyn {n : Nat} (arr : Fin n → BitVec 64) (k : Nat) : BitVec 64 :=
  match n, arr with
  | 0, _ => 0
  | (m + 1), arr => arr ⟨k % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

/-- Functionally update element `k mod n` of a memref; identity (everywhere-`0`)
    for an empty memref. The runtime-index twin of `memrefSet`'s `Fin n` update. -/
def memSetDyn {n : Nat} (arr : Fin n → BitVec 64) (k : Nat) (v : BitVec 64) :
    Fin n → BitVec 64 :=
  match n, arr with
  | 0, _ => fun _ => 0
  | (m + 1), arr =>
      fun j => if j = ⟨k % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ then v else arr j

/-- Read a 128-bit value from a `.memref n` (64-bit-limb array) at 128-bit index
    `k`: the two consecutive limbs `2k`, `2k+1` packed little-endian
    (`lo ||| hi <<< 64`). Total (each `memGetDyn` reduces its index modulo `n`,
    `0` on an empty array), matching the x86 byte-offset model of a 128-bit XMM
    gather. The 128-bit twin of `memGetDyn`. -/
def memGetDyn128 {n : Nat} (arr : Fin n → BitVec 64) (k : Nat) : BitVec 128 :=
  (memGetDyn arr (2 * k)).setWidth 128 |||
    ((memGetDyn arr (2 * k + 1)).setWidth 128 <<< 64)

/-! ### Bignum ALU word splits

The high-word multiply and carry-chain add/carry words, defined identically to
`JasminDialect.mulHiW`/`addCarryWord`/`carryOutBit` (so the `bvMulHi`/
`bvAddCarryLo`/`bvAddCarryHi` lowerings are `rfl`-level matches), kept here so
`CatCryptDialect` need not import `JasminDialect` (the dialects must not
cycle). Their agreement with the jasmin twins is the `mulHiW_eq_*` family in
`DialectToJasminComCorrect`. -/

/-- High word of the full unsigned product `a * b` — the `hi` output of `MULX`.
    Defined identically to `JasminDialect.mulHiW`. -/
def mulHiC {w : Nat} (a b : BitVec w) : BitVec w :=
  BitVec.ofNat w (a.toNat * b.toNat / 2 ^ w)

/-- Data result of one carry-chain add `a + b + cin` (`cin` a `1`-bit register).
    Defined identically to `JasminDialect.addCarryWord`. -/
def addCarryWordC {w : Nat} (a b : BitVec w) (cin : BitVec 1) : BitVec w :=
  a + b + BitVec.ofNat w cin.toNat

/-- Carry-out bit of one carry-chain add `a + b + cin`. Defined identically to
    `JasminDialect.carryOutBit`. -/
def carryOutBitC {w : Nat} (a b : BitVec w) (cin : BitVec 1) : BitVec 1 :=
  if a.toNat + b.toNat + cin.toNat ≥ 2 ^ w then 1 else 0

/-! ### SHA-256 (SHA-NI) per-instruction data effects

Faithful FIPS 180-4 SHA-256 message-schedule / round semantics, defined here on
`BitVec 32`/`BitVec 128` so the `vsha256rnds2`/`vsha256msg1`/`vsha256msg2` dialect
ops carry the exact Intel-SDM data effect of the SHA-NI instructions. Mirrors
`ShaNiEmit.sha256RoundFunc` / `sha256rnds2_lane` etc. (restated here so
`CatCryptDialect` need not import the downstream `ShaNiEmit`, keeping the dialect
layer acyclic). FIPS 180-4 §4.1.2 (Ch/Maj/Σ/σ) + §6.2.2 Step 3 (the round). -/

/-- Lane `k ∈ {0,1,2,3}` of a 128-bit SHA-NI register as a `BitVec 32`
    (lane 0 = low 32 bits). -/
def shaLane (v : BitVec 128) (k : Nat) : BitVec 32 :=
  BitVec.extractLsb' (32 * k) 32 v

/-- Pack four `BitVec 32` lanes into a `BitVec 128` (lane 0 → low). -/
def shaPack (w0 w1 w2 w3 : BitVec 32) : BitVec 128 :=
  w0.setWidth 128 ||| (w1.setWidth 128 <<< 32)
    ||| (w2.setWidth 128 <<< 64) ||| (w3.setWidth 128 <<< 96)

/-- Right-rotate on `BitVec 32`. -/
def shaRotr (x : BitVec 32) (n : Nat) : BitVec 32 := (x >>> n) ||| (x <<< (32 - n))

/-- `Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)` (FIPS 180-4 §4.1.2). -/
def shaCh (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ ((~~~x) &&& z)

/-- `Maj(x,y,z) = (x∧y) ⊕ (x∧z) ⊕ (y∧z)`. -/
def shaMaj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ0(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
def shaBigSigma0 (x : BitVec 32) : BitVec 32 := shaRotr x 2 ^^^ shaRotr x 13 ^^^ shaRotr x 22

/-- `Σ1(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
def shaBigSigma1 (x : BitVec 32) : BitVec 32 := shaRotr x 6 ^^^ shaRotr x 11 ^^^ shaRotr x 25

/-- `σ0(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. -/
def shaSmallSigma0 (x : BitVec 32) : BitVec 32 := shaRotr x 7 ^^^ shaRotr x 18 ^^^ (x >>> (3 : Nat))

/-- `σ1(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`. -/
def shaSmallSigma1 (x : BitVec 32) : BitVec 32 := shaRotr x 17 ^^^ shaRotr x 19 ^^^ (x >>> (10 : Nat))

/-- One SHA-256 compression round on `(a..h)` (FIPS 180-4 §6.2.2 Step 3); the
    `w[t]+k[t]` sum enters through `wk`. -/
def shaStep (s : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
                 BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) (wk : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
      BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let (a, b, c, d, e, f, g, h) := s
  let t1 := h + shaBigSigma1 e + shaCh e f g + wk
  let t2 := shaBigSigma0 a + shaMaj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

/-- **`SHA256RNDS2` data effect.** Advance the SHA-256 state by TWO compression
    rounds. `abef` packs `(a,b,e,f)` (lane 3 = a, lane 0 = f), `cdgh` packs
    `(c,d,g,h)`, `mk` packs `W[i]+K[i]` (lane 0) and `W[i+1]+K[i+1]` (lane 1);
    result is the next `(a,b,e,f)`. Intel SDM Vol. 2, "SHA256RNDS2". -/
def vsha256rnds2W (abef cdgh mk : BitVec 128) : BitVec 128 :=
  let a := shaLane abef 3; let b := shaLane abef 2
  let e := shaLane abef 1; let f := shaLane abef 0
  let c := shaLane cdgh 3; let d := shaLane cdgh 2
  let g := shaLane cdgh 1; let h := shaLane cdgh 0
  let s1 := shaStep (a, b, c, d, e, f, g, h) (shaLane mk 0)
  let (a', b', _c', _d', e', f', _g', _h') := shaStep s1 (shaLane mk 1)
  shaPack f' e' b' a'

/-- **`SHA256MSG1` data effect.** Partial message schedule: lane `j` ↦
    `src1[j] + σ0(src2[j])`. Intel SDM Vol. 2, "SHA256MSG1". -/
def vsha256msg1W (src1 src2 : BitVec 128) : BitVec 128 :=
  shaPack
    (shaLane src1 0 + shaSmallSigma0 (shaLane src2 0))
    (shaLane src1 1 + shaSmallSigma0 (shaLane src2 1))
    (shaLane src1 2 + shaSmallSigma0 (shaLane src2 2))
    (shaLane src1 3 + shaSmallSigma0 (shaLane src2 3))

/-- **`SHA256MSG2` data effect.** Final message schedule: fold `σ1` of the two
    high previous-schedule words back into the partial schedule. Intel SDM
    Vol. 2, "SHA256MSG2". -/
def vsha256msg2W (src1 src2 : BitVec 128) : BitVec 128 :=
  let d0 := shaLane src1 0 + shaSmallSigma1 (shaLane src2 2)
  let d1 := shaLane src1 1 + shaSmallSigma1 (shaLane src2 3)
  let d2 := shaLane src1 2 + shaSmallSigma1 d0
  let d3 := shaLane src1 3 + shaSmallSigma1 d1
  shaPack d0 d1 d2 d3

/-! ## 3. Op signatures (arg types + return type) -/

instance : DialectSignature catCryptDialect where
  sig op := match op with
    | .constBit _ => []
    | .constUnit => []
    | .xor | .and | .or => [.bit, .bit]
    | .not => [.bit]
    | .eqBit => [.bit, .bit]
    | .mkPair a b => [a, b]
    | .fst a b => [.pair a b]
    | .snd a b => [.pair a b]
    | .inl a _ => [a]
    | .inr _ b => [b]
    | .bvConst _ _ => []
    | .bvXor w | .bvAnd w | .bvOr w | .bvAdd w | .bvSub w | .bvMul w =>
        [.sword w, .sword w]
    | .bvNot w => [.sword w]
    | .bvEq w => [.sword w, .sword w]
    | .bvShiftL w _ | .bvShiftR w _ => [.sword w]
    | .bvRor w _ | .bvRol w _ | .bvShiftRA w _ => [.sword w]
    | .andn w | .bvShiftLV w | .bvShiftRV w => [.sword w, .sword w]
    | .bvAdd64 w => [.sword w, .sword w]
    | .bvAdc w => [.sword w, .sword w, .sword w]
    | .bvMulHi w => [.sword w, .sword w]
    | .bvAddCarryLo w | .bvAddCarryHi w => [.sword w, .sword w, .sword 1]
    | .ite t => [.bit, t, t]
    | .bitToSword _ => [.bit]
    | .memrefZero _ => []
    | .memrefSet n _ => [.memref n, .sword 64]
    | .memrefGet n _ => [.memref n]
    | .memrefSetDyn n => [.memref n, .sword 64, .sword 64]
    | .memrefGetDyn n => [.memref n, .sword 64]
    | .memrefGetDyn128 n => [.memref n, .sword 64]
    | .extCall _ argTys _ => argTys
    | .sampleBit => []
    | .sampleBv _ => []
    | .vsimd _ => [.sword 128, .sword 128]
    | .vpshufdC _ | .vaeskeygenC _ | .vpsrldqC _ | .vpslldqC _ => [.sword 128]
    | .vconst128 _ => []
    | .vsha256rnds2 => [.sword 128, .sword 128, .sword 128]
    | .vsha256msg1 | .vsha256msg2 => [.sword 128, .sword 128]
  ret op := match op with
    | .constBit _ | .xor | .and | .or | .not | .eqBit => .bit
    | .constUnit => .unit
    | .mkPair a b => .pair a b
    | .fst a _ => a
    | .snd _ b => b
    | .inl a b => .sum a b
    | .inr a b => .sum a b
    | .bvConst w _ => .sword w
    | .bvXor w | .bvAnd w | .bvOr w | .bvNot w | .bvAdd w | .bvSub w | .bvMul w
        => .sword w
    | .bvEq _ => .bit
    | .bvShiftL w _ | .bvShiftR w _ => .sword w
    | .bvRor w _ | .bvRol w _ | .bvShiftRA w _ => .sword w
    | .andn w | .bvShiftLV w | .bvShiftRV w => .sword w
    | .bvAdd64 w | .bvAdc w => .pair (.sword w) (.sword w)
    | .bvMulHi w | .bvAddCarryLo w => .sword w
    | .bvAddCarryHi _ => .sword 1
    | .ite t => t
    | .bitToSword n => .sword n
    | .memrefZero n => .memref n
    | .memrefSet n _ => .memref n
    | .memrefGet _ _ => .sword 64
    | .memrefSetDyn n => .memref n
    | .memrefGetDyn _ => .sword 64
    | .memrefGetDyn128 _ => .sword 128
    | .extCall _ _ retTy => retTy
    | .sampleBit => .bit
    | .sampleBv n => .sword n
    | .vsimd _ | .vpshufdC _ | .vaeskeygenC _ | .vpsrldqC _ | .vpslldqC _ => .sword 128
    | .vconst128 _ => .sword 128
    | .vsha256rnds2 | .vsha256msg1 | .vsha256msg2 => .sword 128

/-! ## 4. Op denotation -/

instance catCryptDenote : DialectDenote catCryptDialect where
  denote op := match op with
    | .constBit v => fun _ => v
    | .constUnit => fun _ => ()
    | .xor => fun args =>
        let a : Bool := args.head
        let b : Bool := args.tail.head
        Bool.xor a b
    | .and => fun args =>
        let a : Bool := args.head
        let b : Bool := args.tail.head
        a && b
    | .or => fun args =>
        let a : Bool := args.head
        let b : Bool := args.tail.head
        a || b
    | .not => fun args => !(args.head : Bool)
    | .eqBit => fun args =>
        let a : Bool := args.head
        let b : Bool := args.tail.head
        (Bool.xor a b).not
    | .mkPair _ _ => fun args => (args.head, args.tail.head)
    | .fst _ _ => fun args => args.head.1
    | .snd _ _ => fun args => args.head.2
    | .inl _ _ => fun args => .inl args.head
    | .inr _ _ => fun args => .inr args.head
    | .bvConst _ v => fun _ => v
    | .bvXor w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a ^^^ b
    | .bvAnd w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a &&& b
    | .bvOr w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a ||| b
    | .bvNot w => fun args =>
        show BitVec w from ~~~(args.head : BitVec w)
    | .bvAdd w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a + b
    | .bvSub w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a - b
    | .bvMul w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a * b
    | .bvEq w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        decide (a = b)
    | .bvShiftL w k => fun args =>
        let a : BitVec w := args.head
        a <<< k
    | .bvShiftR w k => fun args =>
        let a : BitVec w := args.head
        BitVec.ushiftRight a k
    | .bvRor w n => fun args =>
        let a : BitVec w := args.head
        a.rotateRight n
    | .bvRol w n => fun args =>
        let a : BitVec w := args.head
        a.rotateLeft n
    | .bvShiftRA w n => fun args =>
        let a : BitVec w := args.head
        BitVec.sshiftRight a n
    | .andn w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        (~~~a) &&& b
    | .bvShiftLV w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a <<< b.toNat
    | .bvShiftRV w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a >>> b.toNat
    | .bvAdd64 w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        let p := BitVec.adc a b false
        (show BitVec w × BitVec w from
          ((if p.fst then (1 : BitVec w) else 0), p.snd))
    | .bvAdc w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        let cin : BitVec w := args.tail.tail.head
        let p := BitVec.adc a b (cin.toNat ≠ 0)
        (show BitVec w × BitVec w from
          ((if p.fst then (1 : BitVec w) else 0), p.snd))
    | .bvMulHi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        mulHiC a b
    | .bvAddCarryLo w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        addCarryWordC a b cin
    | .bvAddCarryHi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        carryOutBitC a b cin
    | .ite _ => fun args =>
        if (args.head : Bool) then args.tail.head else args.tail.tail.head
    | .bitToSword n => fun args =>
        show BitVec n from
          if (args.head : Bool) then BitVec.allOnes n else 0
    | .memrefZero _ => fun _ => fun _ => 0
    | .memrefSet _ i => fun args =>
        let arr : Fin _ → BitVec 64 := args.head
        let v : BitVec 64 := args.tail.head
        fun j => if j = i then v else arr j
    | .memrefGet _ i => fun args =>
        let arr : Fin _ → BitVec 64 := args.head
        arr i
    | .memrefSetDyn _ => fun args =>
        let arr : Fin _ → BitVec 64 := args.head
        let i : BitVec 64 := args.tail.head
        let v : BitVec 64 := args.tail.tail.head
        memSetDyn arr i.toNat v
    | .memrefGetDyn _ => fun args =>
        let arr : Fin _ → BitVec 64 := args.head
        let i : BitVec 64 := args.tail.head
        memGetDyn arr i.toNat
    | .memrefGetDyn128 _ => fun args =>
        let arr : Fin _ → BitVec 64 := args.head
        let i : BitVec 64 := args.tail.head
        memGetDyn128 arr i.toNat
    | .extCall _ _ retTy => fun _ => CryptoTy.default retTy
    -- Pure compile interpretation of a sample = the deterministic zero-entropy leaf
    -- (`false` / `0`). The probabilistic meaning lives in `catCryptDenoteSP`; this
    -- pure value is never the operative meaning on the compile path.
    | .sampleBit => fun _ => false
    | .sampleBv n => fun _ => (0 : BitVec n)
    -- 128-bit SIMD lane semantics via the backend `SimdOp.denote` waist. The
    -- binary `vsimd op` reads both operands; the unary ops read `args.head` (the
    -- `vpshufd`/`vaeskeygen` waist ignores its second operand, so `args.head` is
    -- passed twice, matching the jasmin-side unary dispatch exactly).
    | .vsimd op => fun args =>
        let a : BitVec 128 := args.head
        let b : BitVec 128 := args.tail.head
        SimdOp.denote op a b
    | .vpshufdC imm => fun args =>
        let a : BitVec 128 := args.head
        SimdOp.denote (.vpshufd imm) a a
    | .vaeskeygenC rcon => fun args =>
        let a : BitVec 128 := args.head
        SimdOp.denote (.vaeskeygen rcon) a a
    | .vpsrldqC n => fun args =>
        let a : BitVec 128 := args.head
        a >>> (n * 8)
    | .vpslldqC n => fun args =>
        let a : BitVec 128 := args.head
        a <<< (n * 8)
    -- A baked 128-bit immediate denotes to the constant itself (nullary).
    | .vconst128 val => fun _ => val
    -- SHA-256 (SHA-NI) per-instruction data effects (FIPS 180-4). `vsha256rnds2`
    -- is ternary (abef, cdgh, mk); `vsha256msg1`/`vsha256msg2` are binary.
    | .vsha256rnds2 => fun args =>
        let abef : BitVec 128 := args.head
        let cdgh : BitVec 128 := args.tail.head
        let mk : BitVec 128 := args.tail.tail.head
        vsha256rnds2W abef cdgh mk
    | .vsha256msg1 => fun args =>
        let a : BitVec 128 := args.head
        let b : BitVec 128 := args.tail.head
        vsha256msg1W a b
    | .vsha256msg2 => fun args =>
        let a : BitVec 128 := args.head
        let b : BitVec 128 := args.tail.head
        vsha256msg2W a b

end CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
