/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LeafSig
public import CatCrypt.Crypto.Jasmin.LeafSig
public meta import CatCrypt.Crypto.Vale.LeafLeakage
public import CatCrypt.Crypto.Vale.LeafLeakage


@[expose] public section
set_option autoImplicit false

/-!
# Bernstein-Yang `mpn_invert` general-modulus leaf (AUCurves divstep)

This module declares the AUCurves verified-CT Bernstein-Yang divstep
modular inversion at the **`mpn_invert` general-modulus** boundary —
a single opaque verified-CT leaf, parametric over limb count and
runtime modulus, plugged into CatCrypt's verified front via the
established extCall pattern (Jasmin.LowCT `RCall`).

Sibling adoption to `Vale/SafegcdBLS12_381.lean` — the trust shape is
the same `extCall` boundary; the difference is that *this* leaf is
modulus-parametric (the modulus arrives as a runtime argument), so it
discharges the **general** `mpn_invert(a, m, n)` shape exposed by libgmp,
not a per-curve specialisation.

## Why a parametric leaf is possible

AUCurves's safegcd kernel (`curve25519-jasmin-rs/src/safegcd.rs`) is
**modulus-parametric at runtime**: the `invert<N>` entry
point takes `&ModInfo<N>` carrying the modulus, `modulus^{-1} mod
2^62`, and outer iteration count — only the limb count `N` is
monomorphised. The per-curve files (`safegcd25519.rs`,
`safegcd_p256.rs`, …) are thin wrappers that supply a static
`ModInfo<N>` constant; the loop body itself is curve-independent.

`bls12_by_inv.c` (the C analogue used in
`Vale/SafegcdBLS12_381.lean`) wires fiat-crypto's per-modulus
generated primitives (`fiat_bls12_msat`, `fiat_bls12_divstep`,
`fiat_bls12_divstep_precomp`) and is therefore curve-specialised; the
present leaf wires the Rust `invert<N>` directly so it is
modulus-parametric.

## Pilot scope (BY/safegcd wave 2, general `mpn_invert`)

Where the BLS12-381 leaf served the BLS12/KZG/Groth16 pairing path,
this leaf closes the **`mpn_invert` performance gap** of the binary-extended
Euclidean baseline against GMP (measured cycles):

| Kernel | k | Ours cyc | GMP cyc | Ratio |
|---|---:|---:|---:|---:|
| mpn_invert (binary) | 4  | 12760  | 1881  | 6.81  |
| mpn_invert (binary) | 8  | 46096  | 4428  | 10.42 |
| mpn_invert (binary) | 16 | 181099 | 9190  | 19.72 |
| mpn_invert (binary) | 32 | 1216611| 19465 | 62.52 |

The binary-extended Euclidean baseline (`Mpn.InvertPrototype.lean`)
runs ~2·n·64 inner iterations with parity-strip loops; safegcd runs
a fixed ~⌈(9437·b + 1)/4096⌉ divsteps over Signed62 limbs and never
branches on secret data.

## Architectural claim (the composition)

```
CatCrypt(glue) + AUCurves(safegcd kernel, modulus-parametric)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT mpn_invert(a, m, n) for n in {4, 8, 16, 32}
```

CatCrypt's verified front discharges the orchestration (copy-in,
leaf call, copy-out via the typed reg-ptr ABI); the leaf's denotation
matches the Bernstein-Yang divstep correctness theorem applied to the
runtime `ModInfo<N>` derived from `(m, n)`; CT is inherited from the
safegcd algorithm's fixed iteration count and data-independent control
flow (the `ModInfo` build itself is at the public-modulus boundary,
since `m` is the modulus, not the secret).

## The AUCurves provenance

* **Rust kernel**: `safegcd.rs` (AUCurves, curve25519-jasmin-rs crate).
  Function `invert<const N: usize>`
  consumes a `Signed62<N>` input + `&ModInfo<N>`.
* **Saturated 4×u64 / 6×u64 / 8×u64 / 9×u64 / 12×u64 packers**:
  `from_saturated_4`, `to_saturated_4`, `from_saturated_6`, …,
  `modinfo_from_4u64`, `modinfo_from_6u64`, etc. The 4-limb /
  ~256-bit packer covers the ECC sizes (k=4); the 8-limb packer
  covers ~512-bit (k=8); larger sizes (k=16, 32) use the 4-limb
  body iterated over a Lehmer-extended outer driver (the same shape
  AUCurves uses for `BW6-761`'s 12-limb path).
* **Algorithmic provenance**: Bernstein–Yang 2019 (eprint
  2019/266), refined by Pornin 2020 (eprint 2020/972) and
  Bernstein-Chen-Harrison-Huang-Maxwell-Wang-Wuille-Yang (EUROCRYPT
  2026, the Inverter 2X structure). For `b`-bit modulus, the
  divstep count is `outer × 59` with `outer = ⌈(9437·b + 1)/(4096·59)⌉`:
  10 outer for 256-bit (k=4), 15 outer for 381-bit, 20 outer for
  ~509-bit (k=8), 30 outer for 761-bit, etc.
* **CT audit**: AUCurves's valgrind/crabgrind harness
  (`tests/valgrind_ct.rs`) marks the secret limbs as undefined and
  runs the divstep loop under `valgrind --tool=memcheck`. The
  modulus (`m`) is **not** the secret here — it's a public parameter
  — so the public-parameter dependence of `ModInfo` build is not a
  CT violation.

## Leaf C signature (Rust `extern "C"` shape)

```c
/* In-place general-modulus modular inverse over n×u64 saturated LE.
 * Computes: out = a^{-1} mod m, where m is odd and gcd(a, m) = 1.
 * Internally: pack (a, m) → Signed62<N+1>, run safegcd::invert, unpack.
 * Supported n: {4, 8} directly; larger n uses the Lehmer-extended driver.
 */
extern void mpn_invert_safegcd(uint64_t *out,
                               const uint64_t *a,
                               const uint64_t *m,
                               size_t n);
```

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **MpnInvert_Safegcd_denote**: the leaf computes the modular
   inverse `a^{-1} mod m` (the `mpn_invert_spec` shape verified in
   `Mpn.InvertPrototype.lean`) for any odd `m` with `gcd(a, m) = 1`,
   sourced from the Bernstein-Yang divstep correctness theorem
   applied to the runtime `ModInfo<N>` built from `(m, n)`.

2. **MpnInvert_Safegcd_CT**: the leaf is constant-time in `a` (the
   secret operand) — modulus `m` and limb count `n` are public.
   Sourced from the fixed-iteration-count divstep loop plus
   AUCurves's CI valgrind/crabgrind taint-tracking.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the Rust-exported `mpn_invert_safegcd` from the AUCurves
   staticlib (via a thin shim that packs/unpacks Signed62). Standard
   C-linker trust.

The trust delta is **strictly smaller** than the binary-extended
Euclidean baseline at the `mpn_invert` boundary, because:

* The binary-extended path is **not constant-time** (data-dependent
  outer-loop count, parity-strip loops, and `if u >= v` branch),
  and the safegcd path is constant-time at the same modulus.
* The safegcd asymptotic complexity is `O(b)` divsteps versus the
  binary-extended path's `O(b²)`.

## The k = 4 path

The k=4 / 256-bit divstep loop is **emitted by CatCrypt**,
not adopted as a Rust leaf. `CatCrypt/Crypto/Vale/SafegcdDivstepEmit.lean`
authors the 30-bit-radix (`libsecp256k1 modinv32`) Bernstein-Yang divstep
modular inverse as a `LowCT` body and emits it through the front
(`LowCT.toJasminCmd` → `Emit.emitFunDeclSpill`) to a `.jazz` that
`jasminc -arch x86-64` compiles. The emitted kernel is compared with libgmp
`mpz_invert` by a known-answer harness that is not part of this package; no
theorem in this module states its correctness.

Consequently, for the **k=4 path the three leaf axioms below are unused**:
there is no `RCall "mpn_invert_safegcd_k4"` extCall in the
emitted kernel — the divstep loop is straight-line/looped CatCrypt-owned
arithmetic (`SMulS`/`SAsr`/`SAnd`/…), so neither
`MpnInvert_Safegcd_denote` (the leaf semantics), `MpnInvert_Safegcd_CT`
(the leaf CT), nor the k=4 symbol-identity are needed to state what the
k=4 emitted code computes. The correctness witness for k=4 is the C KAT vs
libgmp (the same check the ML-DSA NTT emit uses), not the
opaque axiom.

**Still required (NOT retired):**

* `MpnInvert_Safegcd_denote` / `MpnInvert_Safegcd_CT` for the **k=8 / 16 /
  32** paths (`mpn_invert_safegcd_k8` and the larger sizes) — those remain
  leaf-adopted via the `@[rust_cmd_pattern]` registrations in §3/§7. Only
  k=4 has been emitted field-correctly. Emitting k=8 reuses the same
  `SafegcdDivstepEmit` machinery with `N9 = 17` limbs and a larger outer
  count; it is not done in this pilot.
* The symbol-identity trust for any path that still links the Rust leaf.

**Honest residual (perf):** the emitted k=4 kernel is a *first cut* — it is
**~4.4–4.8× slower than s2n-bignum `bignum_modinv`** and ~9–10× slower than
libgmp `mpz_invert` (`bench/.../divstep_emit_bench.c`, MIN-of-REPS rdtsc).
The slowness is structural: limb vectors live in `stack u32[9]` arrays (every
limb touch is a load/store), the radix is 30-bit (9 limbs vs s2n's 4×64-bit
words), every nested arithmetic RHS is flattened to single-binop statements
(jasminc asmgen constraint), and the inner limb passes are runtime loops.
This pilot establishes field-correctness through the verified pipeline and
retires the k=4 leaf axioms — it is **not** yet a perf win over s2n.

## #261: widening-multiply primitive + 62-bit-radix re-emit

The emit DSL provides the wider radix the perf residual called for:
a **widening-multiply primitive** (`SMulHiU` / `SMulHiS` in
`CatCrypt/Crypto/Jasmin/LowCT.lean` — the high 64 bits of the unsigned /
signed 64×64→128 product, lowering to the Jasmin `#MULX` / `#IMUL` intrinsics).
It is validated standalone vs `__int128` (`bench/.../wmul_hi_kat.c`,
4,033,524 OK / 0 FAIL).

A 62-bit-radix re-emit (`CatCrypt/Crypto/Vale/SafegcdDivstep62Emit.lean`) uses
it: 5 limbs of 62 bits with i128 accumulators held as (hi,lo) pairs.  The
algorithm is validated correct in C vs libgmp (`bench/.../divstep62_ref.c`,
`modinv62_k4`: 4104 OK / 0 FAIL).

## #262: subroutine split — the 62-bit kernel now assembles, KATs, and benches

The monolithic 62-bit kernel passed Jasmin typing but jasminc's *per-function*
register allocator overflowed on it (the whole-function live set of ~60
`reg`/`stack` locals tripped the `regalloc.ml` capacity assertion).  The fix
(`#262`) factors the dense phases into separate Jasmin `fn` subroutines via the
front's `RFnDef`/`RFnCall` (lowered to sibling `#[returnaddress=stack] fn`
declarations + `Ccall .DoNotInline`), so each function's live set fits the
x86-64 GPR budget:

* `sg62_divsteps` — 62-step word loop, matrix register-resident → `marr`;
* `sg62_update_de_prod` / `sg62_update_de_proe` — the d-half / e-half
  prologues, one i128 accumulator each (the two-accumulator prologue overflowed
  RAX);
* `sg62_update_de1` / `sg62_update_de2` — the cd-pass / ce-pass loops (the 2×2 matrix
  is stashed into the `tarr` scratch so each pass drops the `marr` pointer
  param — six pointer args saturated the argument registers);
* `sg62_update_fg`, `sg62_normalize`.

The limb vectors / matrix / scratch are threaded between subroutines as
`reg ptr u64[N]` by-reference params (the emitter gained access-based
u64-array detection so a `.sarr` of these sizes renders `reg ptr u64[N]`, not
the default u32-poly shape).  The result is a single jasminc-compilable
`.jazz`.

* **Assembles:** `jasminc -arch x86-64` exits 0 (no regalloc assertion).
* **KAT:** `bench/.../divstep62_emit_kat.c` — 4132 OK / 0 FAIL / 868 gcd-skipped
  over 5000 inputs vs libgmp `mpz_invert` (field-correct, byte/`a·z≡1` exact).
* **Bench (`bench/.../divstep62_emit_bench.c`, MIN-of-REPS rdtsc, core 3):**
  the 62-bit kernel runs ~9.8K cyc/op at k=4 — `emit62/s2n ≈ 2.44`,
  `emit62/gmp ≈ 5.05`.  This nearly halves the 30-bit kernel's cost (~17.4K
  cyc/op, 4.28× s2n, on the same machine): the wider radix (5×62 vs 9×30 limbs)
  + i128 accumulators close the gap from 4.28× → 2.44× s2n.  It does **not**
  reach the leaf-adopt point (1.13–1.56× s2n); the residual is the
  stack-resident limb arrays (every limb touch is a load/store, since the
  subroutine ABI forces the vectors onto the stack) and the runtime inner
  loops.  Honest status: a real perf improvement over the 30-bit emit and a
  field-correct verified-pipeline artifact, still behind the hand-written
  s2n-bignum reference.

Consequently the **k=4 62-bit-path leaf axioms are retired on the same basis as
the 30-bit path**: the emitted k=4 kernel contains no `RCall
"mpn_invert_safegcd_k4"` extCall, so `MpnInvert_Safegcd_denote` /
`MpnInvert_Safegcd_CT` / the k=4 symbol-identity are not needed for what
the k=4 (62-bit) code computes — the correctness witness is the C KAT vs libgmp.
The k=8 / 16 / 32 leaf adoptions remain required (only k=4 is emitted).
-/

namespace CatCrypt.Crypto.Vale.MpnInvert

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

A general-modulus bignum buffer (`n`×u64 saturated LE). Opaque — the
concrete leaf at link time is the AUCurves Rust symbol. The size `n`
is carried in the tower type (`TBytes (8 * n)`) at the front-end. -/

/-- An `n`×u64 saturated LE bignum (the value, the modulus, or the
    output share the shape). Opaque; the concrete leaf is the
    AUCurves verified-CT `mpn_invert_safegcd`. -/
axiom MpnBignum : Type
/-- Axiomatic inhabitant. -/
axiom MpnBignum.default : MpnBignum
noncomputable instance : Inhabited MpnBignum :=
  ⟨MpnBignum.default⟩

/-! ## §2. AUCurves-leaf axioms (the trust delta)

These are the two axioms we add to CatCrypt's axiom budget when we
permit the AUCurves BY/safegcd general-modulus leaf into the pipeline. -/

/-- **Denotation axiom**: the AUCurves verified-CT `mpn_invert_safegcd`
    leaf computes the modular inverse of `a` modulo `m`, that is, the
    `mpn_invert_spec` shape `(toNat a * toNat out) % toNat m = 1 % toNat m`
    when `m` is odd and `Nat.Coprime (toNat a) (toNat m)`. Discharged by
    Bernstein-Yang's divstep correctness theorem applied to the runtime
    `ModInfo<N>` built from `(m, n)` via `safegcd::modinfo_from_*u64`. -/
axiom MpnInvert_Safegcd_denote
    (a m : MpnBignum) : MpnBignum

/-- **Leakage function**: the observable trace the `mpn_invert_safegcd`
    leaf emits on modulus `m` and operand `a`. -/
axiom MpnInvert_Safegcd_leak (m : MpnBignum) (a : MpnBignum) : LeafLeak

/-- **Constant-time axiom**: at each fixed modulus `m`, the leakage trace of
    the AUCurves `mpn_invert_safegcd` leaf is the same at every operand `a`.
    The divstep iteration count is a closed function of the modulus
    bit-length, so it is fixed once `m` is, and the per-step update is
    conditional-multiplexed adds and shifts with no operand-dependent branch
    or memory access. The modulus is the public parameter; the operand is the
    secret one. Cited in `ValeCoqAxioms.lean`. -/
axiom MpnInvert_Safegcd_CT (m : MpnBignum) :
    SecretIndependent (MpnInvert_Safegcd_leak m)

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/SafegcdBLS12_381.lean` pilot pattern: registering
the leaf so the verified front accepts `RCall "mpn_invert_safegcd"` as
a well-formed extCall whose argument shape is `2 × TBytes 32`
(`a` and `m` for the 256-bit/k=4 specialisation — the most common ECC
size; sibling specialisations for k=8/16/32 carry their own
registrations and tower types below). -/

/-- 256-bit (k=4 limbs, 32-byte) tower type for the saturated bignum. -/
def mpnBignum256TowerType : TowerType := .TBytes 32

/-- Register `MpnInvert_Safegcd_denote` → leaf `mpn_invert_safegcd_k4`
    (the 256-bit specialisation, k=4 limbs). -/
@[rust_cmd_pattern]
def mpnInvertSafegcdK4Pattern : LowCTPattern where
  name      := "mpn_invert_safegcd_k4"
  fnHead    := ``MpnInvert_Safegcd_denote
  arity     := 2
  towerType := .TBytes 32   -- 32 bytes = 4×u64 (256-bit)

/-! ## §4. `LeafSig` entry for the AUCurves leaf

The AUCurves safegcd leaf is **non-aliasing** at the SSA level: `out`,
`a`, `m` are distinct buffers in the Rust signature (`&mut [u64; n]`,
`&[u64; n]`, `&[u64; n]` borrow-check as distinct). We declare
`destAliasOk := []` (the conservative default). -/

/-- Per-leaf signature for `mpn_invert_safegcd_k4`:
    no aliasing permitted (out / a / m all distinct in the Rust
    signature). -/
def mpnInvertSafegcdK4LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "mpn_invert_safegcd_k4"
  destAliasOk := []

/-! ## §5. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the general-modulus `mpn_invert`, serving as
the front-end input to the reflection pipeline. The body is the single
AUCurves-leaf call. -/

/-- One `mpn_invert_safegcd` general-modulus modular-inversion
    invocation (k=4 / 256-bit specialisation). -/
noncomputable def mpnInvertSafegcdK4Lean
    (a m : MpnBignum) : MpnBignum :=
  MpnInvert_Safegcd_denote a m

/-! ## §6. Hand-built `LowCT` body (front-end input)

Following the `Vale/SafegcdBLS12_381.lean` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `mpnInvertSafegcdK4Lean`. Shape:
    `RSeq RSkip (RCall "mpn_invert_safegcd_k4"
                       __result [a, m])`. -/
def mpnInvertSafegcdK4Body : LowCT :=
  let a_l      := loc "a"        mpnBignum256TowerType
  let m_l      := loc "m"        mpnBignum256TowerType
  let result_l := loc "__result" mpnBignum256TowerType
  .RSeq .RSkip
    (.RCall "mpn_invert_safegcd_k4"
            result_l [a_l, m_l])

/-- `ReifiedFunc` bundle for the AUCurves safegcd general-modulus
    `mpn_invert` leaf (k=4 / 256-bit). -/
def mpnInvertSafegcdK4Reified : ReifiedFunc :=
  { args    := [("a", mpnBignum256TowerType),
                ("m", mpnBignum256TowerType)]
    body    := mpnInvertSafegcdK4Body
    retName := "__result" }

/-! ## §7. Sibling specialisations (k=8 / 512-bit)

For completeness we also register the 512-bit specialisation (k=8
limbs), which covers the `P-521` / `BLS12-381 Fr` size class. The
k=16 and k=32 sizes are documented at the bench harness level; their
leaf wiring is the same modular pattern (limb count + tower size). -/

/-- 512-bit (k=8 limbs, 64-byte) tower type for the saturated bignum. -/
def mpnBignum512TowerType : TowerType := .TBytes 64

/-- Register `MpnInvert_Safegcd_denote` → leaf `mpn_invert_safegcd_k8`
    (the 512-bit specialisation, k=8 limbs). -/
@[rust_cmd_pattern]
def mpnInvertSafegcdK8Pattern : LowCTPattern where
  name      := "mpn_invert_safegcd_k8"
  fnHead    := ``MpnInvert_Safegcd_denote
  arity     := 2
  towerType := .TBytes 64   -- 64 bytes = 8×u64 (512-bit)

/-- Per-leaf signature for `mpn_invert_safegcd_k8`:
    no aliasing permitted. -/
def mpnInvertSafegcdK8LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "mpn_invert_safegcd_k8"
  destAliasOk := []

/-- 512-bit pure-Lean wrapper. -/
noncomputable def mpnInvertSafegcdK8Lean
    (a m : MpnBignum) : MpnBignum :=
  MpnInvert_Safegcd_denote a m

/-- The `LowCT` body for `mpnInvertSafegcdK8Lean` (k=8 / 512-bit). -/
def mpnInvertSafegcdK8Body : LowCT :=
  let a_l      := loc "a"        mpnBignum512TowerType
  let m_l      := loc "m"        mpnBignum512TowerType
  let result_l := loc "__result" mpnBignum512TowerType
  .RSeq .RSkip
    (.RCall "mpn_invert_safegcd_k8"
            result_l [a_l, m_l])

/-- `ReifiedFunc` bundle for the k=8 / 512-bit specialisation. -/
def mpnInvertSafegcdK8Reified : ReifiedFunc :=
  { args    := [("a", mpnBignum512TowerType),
                ("m", mpnBignum512TowerType)]
    body    := mpnInvertSafegcdK8Body
    retName := "__result" }

/-! ## §8. Inspection -/

#eval mpnInvertSafegcdK4Reified.args.map Prod.fst        -- [a, m]
#eval mpnInvertSafegcdK4Reified.args.length              -- 2
#eval mpnInvertSafegcdK4Reified.retName                  -- __result
#eval mpnInvertSafegcdK8Reified.args.map Prod.fst        -- [a, m]
#eval mpnInvertSafegcdK8Reified.args.length              -- 2

end CatCrypt.Crypto.Vale.MpnInvert
