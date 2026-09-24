/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCT
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.LowCT
public meta import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public meta import CatCrypt.Crypto.Jasmin.JasminEmit
public import CatCrypt.Crypto.Jasmin.JasminEmit

/-!
# Bernstein-Yang safegcd divstep modular inverse — 62-bit-radix re-emit

The 62-bit-radix (`libsecp256k1 modinv64`) Bernstein-Yang divstep modular
inverter, authored as a `LowCT` body and emitted through the verified front
to a jasminc-compilable `.jazz`.  This is the perf-closure re-emit of the
30-bit `SafegcdDivstepEmit` kernel: 5 limbs of 62 bits (i64) instead of 9
limbs of 30 bits (i32), with the matrix-vector accumulators held as i128.

## Why 62-bit needs the widening-multiply primitive

The `update_de_62` / `update_fg_62` accumulators are `int128_t`:
`cd = (int128)t.u * d.v[0] + (int128)t.v * e.v[0] + …`, with each product
reaching ~2^124.  The accumulator is held here as a **(hi, lo) int64 limb
pair**; each product `(int128) t * limb` contributes a signed hi:lo pair via
the primitives `SMulHiS` (high word → Jasmin `#IMUL`) and `SMulS` (low
word → Jasmin `*`).  The 128-bit accumulate is open-coded:

  lo' = lo + plo  (mod 2^64)         -- SAdd
  carry = (lo' <u plo) ? 1 : 0       -- SLt (unsigned carry-out detection)
  hi' = hi + phi + carry             -- two SAdd

and the `cd >>= 62` arithmetic shift of the 128-bit value is

  lo'' = (lo >> 62) | (hi << 2)      -- SShr | (SShl & wrap) via SXor (disjoint)
  hi'' = hi >>s 62                   -- SAsr (sign-preserving)

## Limb storage and matrix residency

The five 5-limb vectors `d, e, f, g, mod` live in `stack u64[5]` arrays.
The 2×2 transition matrix `(du,dv,dq,dr)` is **register-resident across the
62-step divstep word loop** (`reg u64`, where the loop is hot and the limb
arrays are untouched), then exported to a `stack u64[4]` (`marr`) and loaded
just-in-time in `update_de` / `update_fg`.  The JIT-load is what keeps the
inner accumulator loop inside the x86-64 GPR budget: the `#IMUL` widening
multiply reserves RAX/RDX, so persisting four matrix registers across it
overflows the allocator.  The `update_de` reduction multipliers `md,me` and
`minv` are stashed in a small `stack u64[3]` scratch array.

## Constant-time

Control flow is data-independent in `a` (the secret): `OUTER_K4 = 10` outer
iterations × `dsScnt = 59` divsteps (EUROCRYPT 2026 δ₀=1/2 start; see §0),
all conditional updates via mask-and-merge, no secret branch — `RWhileNz`
countdowns with public bounds.

## Ground truth

`bench/mpn_invert_safegcd_compare/divstep62_ref.c` (`modinv62_k4`) validates
byte-exact / `a·inv ≡ 1` against libgmp `mpz_invert`.  This module transcribes
that exact algorithm; the emitted `.jazz` is KAT-validated by
`divstep62_emit_kat.c`.
-/

@[expose] public section

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT

namespace CatCrypt.Crypto.Vale.SafegcdDivstep62Emit

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §0. Constants and layout (k=4 / 256-bit, 5×62-bit) -/

def m62 : Nat := 4611686018427387903   -- 2^62 − 1
def n5 : Nat := 5
def outerK4 : Nat := 10       -- libsecp256k1 modinv64 outer count
/-- Divsteps per outer iteration under the EUROCRYPT 2026 δ₀=1/2 start.

    With the `(1/2, f, g)` starting point (Bernstein–Chen–Harrison–Huang–
    Maxwell–Wang–Wuille–Yang, *Accelerating and verifying constant-time
    modular inversion*, EUROCRYPT 2026, LNCS 16547) the divstep-count bound is
    sharper than the BY-2019 `(1, f, g)` bound, and the secp256k1 word loop
    runs only **59** divsteps per 62-bit word instead of 62.  The 2×2 identity
    is pre-scaled by `8 = 2^3` so the matrix is still scaled by exactly
    `8 · 2^59 = 2^62` (the divisor `update_de`/`update_fg` consume), keeping
    those phases byte-identical.  Total: `outerK4 × dsScnt = 10 × 59 = 590`
    divsteps vs the previous `10 × 62 = 620`.

    We adopt this count **as a parameter** — the paper's HOL Light development
    proves 590 suffices for `2^255-19`; we validate empirically via the full
    random-input KAT against gmp `mpz_invert`.  Correctness of the emitted
    *recurrence* (not the bound) remains ours, via the compiler. -/
def dsScnt : Nat := 59

/-! ## §1. SExpr / command helpers -/

def v (x : String) : SExpr := .SVar x
def lit (n : Nat) : SExpr := .SLit n
def setE (x : String) (e : SExpr) : LowCT := .RScalarSetExpr x e
def setN (x : String) (n : Nat) : LowCT := .RScalarSet x n

def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | c :: rest => .RSeq c (seqAll rest)

/-! ### SExpr flattener (single-binop / single-intrinsic per statement)

jasminc's surface asmgen rejects a *nested* arithmetic RHS: every
`RScalarSetExpr` must lower to a SINGLE binop (or, for a top-level high-mul,
a single `#MULX`/`#IMUL` intrinsic) over atoms (`SVar`/`SLit`).  `flatten`
rewrites an arbitrary `SExpr` into a sequence of single-op `RScalarSetExpr`s
using fresh scratch slots `_e0, _e1, …`.  The high-mul nodes (`SMulHiU`,
`SMulHiS`) are kept at the TOP of their flattened statement so that
`sexprSetExprCmd` emits the intrinsic. -/

def isAtom : SExpr → Bool
  | .SVar _ => true
  | .SLit _ => true
  | _ => false

partial def flattenAux (cnt : Nat) : SExpr → (List LowCT × SExpr × Nat)
  | .SVar x => ([], .SVar x, cnt)
  | .SLit k => ([], .SLit k, cnt)
  | e =>
    let (mk, a, b) := match e with
      | .SAdd a b => (SExpr.SAdd, a, b)
      | .SSub a b => (SExpr.SSub, a, b)
      | .SMul a b => (SExpr.SMul, a, b)
      | .SMulS a b => (SExpr.SMulS, a, b)
      | .SMulHiU a b => (SExpr.SMulHiU, a, b)
      | .SMulHiS a b => (SExpr.SMulHiS, a, b)
      | .SShr a b => (SExpr.SShr, a, b)
      | .SShl a b => (SExpr.SShl, a, b)
      | .SAsr a b => (SExpr.SAsr, a, b)
      | .SAnd a b => (SExpr.SAnd, a, b)
      | .SXor a b => (SExpr.SXor, a, b)
      | .SLt a b => (SExpr.SLt, a, b)
      | other => (fun _ _ => other, other, other)
    let (ca, atomA, c1) := flattenAux cnt a
    let (cb, atomB, c2) := flattenAux c1 b
    let nm := s!"_e{c2}"
    (ca ++ cb ++ [setE nm (mk atomA atomB)], .SVar nm, c2 + 1)

def setFlat (dst : String) (e : SExpr) : LowCT :=
  if isAtom e then setE dst e
  else
    let (cmds, atom, _) := flattenAux 0 e
    seqAll (cmds ++ [setE dst atom])

/-! ## §2. Limb-array slots (`stack u64[5]`) and access helpers -/

def darr : Located := { locVar := "darr", locSrc := TowerType.TArr 5 .TU64 }
def earr : Located := { locVar := "earr", locSrc := TowerType.TArr 5 .TU64 }
def farr : Located := { locVar := "farr", locSrc := TowerType.TArr 5 .TU64 }
def garr : Located := { locVar := "garr", locSrc := TowerType.TArr 5 .TU64 }
def modarr : Located := { locVar := "modarr", locSrc := TowerType.TArr 5 .TU64 }
/-- Scratch array
    `[md, me, minv, ce_lo, ce_hi, cd_lo, cd_hi, du, dv, dq, dr]` (11 cells).
    Cells 3-6 carry the post-`>>=62` `ce`/`cd` i128 accumulators, and cells
    7-10 carry the 2×2 transition matrix, from the `update_de` prologue
    subroutines (`sg62_update_de_prod`/`proe`) to the cd-pass
    (`sg62_update_de1`) and ce-pass (`sg62_update_de2`).  Splitting `update_de`
    four ways keeps only ONE i128 accumulator (plus the prologue's
    `minv`-multiply) live per subroutine, and stashing the matrix here lets the
    passes drop the `marr` pointer param — both needed to fit jasminc's
    per-function allocator (the monolithic `update_de` overflowed RAX; six
    pointer args saturated the x86-64 argument registers). -/
def tarr : Located := { locVar := "tarr", locSrc := TowerType.TArr 11 .TU64 }
/-- Stack array holding the 2×2 transition matrix `[du,dv,dq,dr]` after the
    divstep word loop.  The matrix is loaded just-in-time into a shared temp
    in `update_de` / `update_fg` rather than held in four persistent `reg u64`:
    the `#IMUL` widening multiply clobbers RAX/RDX, so keeping the matrix on
    the stack (short live ranges) is what fits the inner-loop live set inside
    the x86-64 GPR budget. -/
def marr : Located := { locVar := "marr", locSrc := TowerType.TArr 4 .TU64 }
/-- Snapshot arrays: `update_de` / `update_fg` copy the input limb vectors
    here before the in-place accumulator passes, so the cd/cf-pass and
    ce/cg-pass both read the un-mutated inputs. -/
def dsnap : Located := { locVar := "dsnap", locSrc := TowerType.TArr 5 .TU64 }
def esnap : Located := { locVar := "esnap", locSrc := TowerType.TArr 5 .TU64 }
/-- 1-element u64 array carrying the persistent `eta` accumulator across the
    outer iterations.  Scalars cannot be threaded as `RFnDef` params (a
    `TU64` Located lowers to a `.sarr 8` byte-array via `towerToSType`, not a
    `.sword`), so `eta` rides in a `reg ptr u64[1]` instead. -/
def etaarr : Located := { locVar := "etaarr", locSrc := TowerType.TArr 1 .TU64 }
def u64s (x : String) : Located := { locVar := x, locSrc := TowerType.TU64 }
def u32s (x : String) : Located := { locVar := x, locSrc := TowerType.TU32 }
/-- The I/O buffers arrive as `reg ptr u32[8]` (256-bit LE, 8 u32 words) — the
    `.sarr 32` param shape the emitter renders.  The 62-bit limbs are
    assembled from / packed into these 8 u32 words (cross-word slicing), so
    the I/O access stays on the u32 array path while the internal limb arrays
    are u64. -/
def io8 (x : String) : Located := { locVar := x, locSrc := TowerType.TArr 8 .TU32 }

/-- Load limb `i` of `arr` into scalar `dst` (u64 cells: the stored value IS
    the int64 two's-complement pattern, no sign-extension needed since the
    cell width matches the register width). -/
def loadLimb (arr : Located) (dst : String) (i : Nat) : LowCT :=
  seqAll [ setN "idx" i, .RArrLoad (u64s dst) arr "idx" ]

def storeLimb (arr : Located) (src : String) (i : Nat) : LowCT :=
  seqAll [ setN "idx" i, .RArrStore arr "idx" (u64s src) ]

def setLimbE (arr : Located) (i : Nat) (e : SExpr) : LowCT :=
  seqAll [ setFlat "wtmp" e, storeLimb arr "wtmp" i ]

def loadLimbV (arr : Located) (dst idxName : String) : LowCT :=
  .RArrLoad (u64s dst) arr idxName

def storeLimbV (arr : Located) (src idxName : String) : LowCT :=
  .RArrStore arr idxName (u64s src)

/-! ## §3. 128-bit accumulator combinators

The accumulator `acc` is a (hi, lo) int64 pair held in scalars
`{acc}_hi` / `{acc}_lo`.  Helpers update it in place using single-op
statements. -/

/-- `acc := 0` (both halves). -/
def accZero (acc : String) : LowCT :=
  seqAll [ setN s!"{acc}_lo" 0, setN s!"{acc}_hi" 0 ]

def allOnes64 : Nat := 18446744073709551615   -- 2^64 − 1

/-- Emit the **signed** high word of the `64×64 → 128` product `a * b` into the
    scalar named `dst`, via the **flag-free, non-RDX-pinned** unsigned `#MULX`
    plus the branchless signed high-word correction:

```
  hi_u = mulHiU(a, b)                 // SMulHiU → #MULX (BMI2): no flag, hi → any GPR
  hi_s = hi_u − [a<0]·b − [b<0]·a      // signed correction
```

    where `[a<0]` is materialised branchlessly as the arithmetic-shift-right
    mask `a >>s 63` (all-ones iff `a < 0`, else 0), so `[a<0]·b = (a >>s 63) & b`.
    Both subtractions are open-coded as **two's-complement adds** (`x − y =
    x + (~y) + 1`): `SExpr.eval`/`evalState` returns a `Nat` whose `SSub` arm is
    Nat-truncating (saturates at 0), whereas the emitted Jasmin `-` wraps mod
    2^64; threading the correction through `SXor`/`SAdd` (which only grow the
    Nat, then truncate mod 2^64 at each scalar store) keeps the **Lean model
    faithful** to the wrapping hardware semantics.  Identity differentially
    validated (`bv_decide` all-inputs at width 8 + `native_decide` boundary pins
    at width 64; see `X86Backend/TranslationValidation.lean`).

    The flag-free, arbitrary-GPR `#MULX` is the prerequisite for an **inline**
    (un-hoisted) §13b ADCX/ADOX dual chain — `#IMUL` clobbers CF/OF and pins its
    high word to RDX, so it cannot issue between two `#ADOX`s.

    **Scope:** differentially validated; the accumulator's high-word path
    (`accAddProd`) uses `SMulHiS` (`#IMUL`) instead.  Two measured facts decide
    this: (1) in the single-CF path (no dual chain) `signedHi` is slower
    (1.80× s2n vs `#IMUL`'s ~1.51×), since the ~7-op correction is unamortised
    without the dual chain; and (2) the dual chain that would amortise it is
    RA-blocked by the hoisting `+2` (see `dualChainAccumulator`). -/
def signedHi (dst a b : String) : List LowCT :=
  [ setE dst (.SMulHiU (v a) (v b))                       -- hi_u = #MULX(a,b)
    -- corr1 := [a<0]·b = (a >>s 63) & b, folded into a single scratch `_c`
  , setE "_c" (.SAsr (v a) (lit 63))                      -- [a<0] mask
  , setE "_c" (.SAnd (v "_c") (v b))                      -- [a<0]·b
    -- hi_s -= corr1, open-coded as the two's-complement add  hi + (~_c) + 1.
    -- The `~_c` is a *standalone* `Cassgn` (not nested inside the `+`): jasminc
    -- has no `xor r64, imm64` encoding, so the `^ 0xFFFF…` immediate must sit
    -- in its own statement (the emitter materialises it via `movabs`+`xor`).
  , setE "_c" (.SXor (v "_c") (lit allOnes64))            -- ~corr1
  , setE dst (.SAdd (v dst) (v "_c"))
    -- corr2 := [b<0]·a = (b >>s 63) & a, reusing `_c` (corr1 is dead)
  , setE "_c" (.SAsr (v b) (lit 63))                      -- [b<0] mask
  , setE "_c" (.SAnd (v "_c") (v a))                      -- [b<0]·a
  , setE "_c" (.SXor (v "_c") (lit allOnes64))            -- ~corr2
  , setE dst (.SAdd (v dst) (v "_c"))
    -- the two `+1`s of the two two's-complement subtractions combine to `+2`
  , setE dst (.SAdd (v dst) (lit 2)) ]

/-- `acc += sext128(a * b)` where `a`, `b` are signed i64 scalar names.
    Uses `SMulS` (low word) + `SMulHiS` (signed high word, `#IMUL`) and an
    open-coded 128-bit signed add.  The carry-out of `nlo = acc_lo + plo` (mod
    2^64) is
    materialised as a u64 0/1 via the branchless bit-trick
    `cout = ((x & y) | ((x ^ y) & ~s)) >> 63`  (x=acc_lo, y=plo, s=nlo);
    jasminc has no value-producing carry flag outside `#ADC`, and `<` yields a
    `bool`, so the bit-trick keeps the accumulate inside the plain SExpr ops. -/
def accAddProd (acc a b : String) : LowCT :=
  seqAll
    [ setE "plo" (.SMulS (v a) (v b))
    , setE "phi" (.SMulHiS (v a) (v b))
      -- nlo = acc_lo + plo
    , setE "nlo" (.SAdd (v s!"{acc}_lo") (v "plo"))
      -- cyy = ((acc_lo & plo) | ((acc_lo ^ plo) & ~nlo)) >> 63
    , setE "_g0" (.SAnd (v s!"{acc}_lo") (v "plo"))
    , setE "_g1" (.SXor (v s!"{acc}_lo") (v "plo"))
    , setE "_g2" (.SXor (v "nlo") (lit allOnes64))      -- ~nlo
    , setE "_g1" (.SAnd (v "_g1") (v "_g2"))
    , setE "cyy" (.SXor (v "_g0") (v "_g1"))            -- (g0 | g1) = g0 ^ g1 (disjoint? use OR)
    , setE "cyy" (.SShr (v "cyy") (lit 63))
    , setE s!"{acc}_lo" (v "nlo")
      -- acc_hi += phi + carry
    , setE s!"{acc}_hi" (.SAdd (v s!"{acc}_hi") (v "phi"))
    , setE s!"{acc}_hi" (.SAdd (v s!"{acc}_hi") (v "cyy")) ]

/-- `acc := sext128(a * b)` (set, not add) — initializer form.  The high word
    flows through the short-lived `phi` temp (the `#IMUL` RDX output) before
    landing in the long-lived `acc_hi`, so `acc_hi` is never the direct `#IMUL`
    target and the allocator can keep it in a stable GPR away from RDX. -/
def accSetProd (acc a b : String) : LowCT :=
  seqAll
    [ setE "plo" (.SMulS (v a) (v b))
    , setE "phi" (.SMulHiS (v a) (v b))
    , setE s!"{acc}_lo" (v "plo")
    , setE s!"{acc}_hi" (v "phi") ]

/-- Load matrix entry `marr[mIdx]` into the shared temp `mt`. -/
def ldM (mIdx : Nat) : LowCT := loadLimb marr "mt" mIdx
/-- `acc := sext128(marr[mIdx] * b)` (matrix loaded JIT into `mt`). -/
def accSetProdM (acc : String) (mIdx : Nat) (b : String) : LowCT :=
  seqAll [ ldM mIdx, accSetProd acc "mt" b ]
/-- `acc += sext128(marr[mIdx] * b)` (matrix loaded JIT into `mt`). -/
def accAddProdM (acc : String) (mIdx : Nat) (b : String) : LowCT :=
  seqAll [ ldM mIdx, accAddProd acc "mt" b ]

/-- The 2×2 transition matrix `[du,dv,dq,dr]` is additionally stashed by the
    prologue into `tarr[7,8,9,10]` (`du=7, dv=8, dq=9, dr=10`).  The cd-pass
    (`update_de1`) and ce-pass (`update_de2`) read the matrix from `tarr`
    rather than from `marr`, so they need one fewer `reg ptr` param across the
    call boundary — dropping `marr` keeps the dense i128-accumulate loop inside
    the x86-64 GPR budget (6 pointer args saturated all argument registers). -/
def matrixTarrCell (mIdx : Nat) : Nat := mIdx + 7
/-- Load matrix entry (by `marr` index) from its `tarr` stash cell into `mt`. -/
def ldMt (mIdx : Nat) : LowCT := loadLimb tarr "mt" (matrixTarrCell mIdx)
/-- `acc := sext128(tarr-stashed-matrix[mIdx] * b)`. -/
def accSetProdMt (acc : String) (mIdx : Nat) (b : String) : LowCT :=
  seqAll [ ldMt mIdx, accSetProd acc "mt" b ]
/-- `acc += sext128(tarr-stashed-matrix[mIdx] * b)`. -/
def accAddProdMt (acc : String) (mIdx : Nat) (b : String) : LowCT :=
  seqAll [ ldMt mIdx, accAddProd acc "mt" b ]

/-- `acc >>=a 62` (arithmetic shift of the 128-bit value by 62):
    lo'' = (lo >>u 62) | (hi <<u 2);  hi'' = hi >>s 62.
    The two contributions to lo'' are bit-disjoint (lo keeps bits [62,63]→[0,1],
    hi contributes bits [0,61]→[2,63]), so `|` = `^` = `+`. -/
def accAsr62 (acc : String) : LowCT :=
  seqAll
    [ setE "_t0" (.SShr (v s!"{acc}_lo") (lit 62))
    , setE "_t1" (.SShl (v s!"{acc}_hi") (lit 2))
    , setE s!"{acc}_lo" (.SXor (v "_t0") (v "_t1"))
    , setE s!"{acc}_hi" (.SAsr (v s!"{acc}_hi") (lit 62)) ]

/-- low 62 bits of the accumulator: `acc_lo & M62`. -/
def accLoMasked (acc : String) : SExpr := .SAnd (v s!"{acc}_lo") (lit m62)
/-- low 64 bits of the accumulator: `acc_lo`. -/
def accLo (acc : String) : SExpr := v s!"{acc}_lo"

/-! ## §4. Unpack 8×u32 (LE, `a`/`m`) → 5×62-bit limbs

The I/O buffer is 8 u32 words.  Each u32 word `w[k]` is loaded **zero-extended**
into a u64 scalar `{pfx}k` (the `RArrLoad` u32 path widens), so a `<< off`
that crosses into the upper 32 bits stays within the u64 register.  Limb `i`
occupies bits `[62*i, 62*i+62)`; gathering it needs up to three consecutive
u32 words.  We accumulate `acc = Σ_k (w[wi+k] << (32*k - off))` (with the
first word right-shifted by `off`), then mask to 62 bits. -/

def loadIOWords (src : String) (pfx : String) : LowCT :=
  seqAll ((List.range 8).flatMap (fun i =>
    [ setN "idx" i, .RArrLoad (u64s s!"{pfx}{i}") (io8 src) "idx" ]))

/-- Unpack 62-bit limb `i` from the 8×u32 word stream `{pfx}0..{pfx}7`. -/
def unpackLimbCmd (pfx : String) (arr : Located) (i : Nat) : LowCT :=
  let bit := 62 * i
  let wi := bit / 32
  let off := bit % 32
  -- first word: w[wi] >> off
  let loInit : LowCT :=
    if wi ≥ 8 then setE "ulo" (lit 0)
    else if off == 0 then setE "ulo" (v s!"{pfx}{wi}")
    else setE "ulo" (.SShr (v s!"{pfx}{wi}") (lit off))
  -- subsequent words contribute at bit position 32*k - off (k = 1, 2)
  let contrib (k : Nat) : LowCT :=
    let wk := wi + k
    let sh := 32 * k - off
    if wk < 8 ∧ sh < 62 then
      seqAll [ setE "uhi" (.SShl (v s!"{pfx}{wk}") (lit sh))
             , setE "ulo" (.SXor (v "ulo") (v "uhi")) ]
    else .RSkip
  seqAll [ loInit, contrib 1, contrib 2, setLimbE arr i (.SAnd (v "ulo") (lit m62)) ]

def unpackToArr (pfx : String) (arr : Located) : LowCT :=
  seqAll ((List.range n5).map (fun i => unpackLimbCmd pfx arr i))

/-! ## §5. Pack `darr` (5×62-bit, non-negative) → 8×u32 (LE)

Limb `i` (in `[0, 2^62)` after normalize) at bit `62*i` lands in u32 words
`wi = (62*i)/32`, contributing `(w << off) & 0xFFFFFFFF` to `o[wi]`,
`(w >> (32-off)) & 0xFFFFFFFF` to `o[wi+1]`, and `(w >> (64-off)) & ...` to
`o[wi+2]` (the limb spans up to three u32 words).  The output words are then
narrowed (the `RArrStore` u32 path masks to 32 bits) and stored. -/

def packStore : LowCT :=
  let zero := seqAll ((List.range 8).map (fun i => setN s!"o{i}" 0))
  let accum := seqAll ((List.range n5).map (fun i =>
    let bit := 62 * i
    let wi := bit / 32
    let off := bit % 32
    let ld : LowCT := loadLimb darr "plimb" i
    -- contribution to o[wi+k]; k=0 uses << off, k≥1 uses >> (32*k - off)
    let part (k : Nat) : LowCT :=
      let wk := wi + k
      if wk ≥ 8 then .RSkip
      else
        let sh : SExpr :=
          if k == 0 then
            (if off == 0 then v "plimb" else .SShl (v "plimb") (lit off))
          else .SShr (v "plimb") (lit (32 * k - off))
        -- skip a contribution whose shift annihilates the value
        if k ≥ 1 ∧ 32 * k - off ≥ 62 then .RSkip
        else setFlat s!"o{wk}" (.SXor (v s!"o{wk}") sh)
    seqAll [ld, part 0, part 1, part 2]))
  let store := seqAll ((List.range 8).flatMap (fun i =>
    [ setN "idx" i, .RArrStore (io8 "out") "idx" (u32s s!"o{i}") ]))
  seqAll [zero, accum, store]

/-! ## §6. modulus^{-1} mod 2^62 (Newton, 5 doublings; u64 wrap) -/

def modinv62Body : LowCT :=
  let step : LowCT :=
    seqAll [ setFlat "minv_t" (.SMul (v "mod0lo") (v "minv"))
           , setN "two" 2
           , setFlat "minv_t" (.SSub (v "two") (v "minv_t"))
           , setFlat "minv" (.SMul (v "minv") (v "minv_t")) ]
  seqAll [ loadLimb modarr "mod0lo" 0
         , setFlat "minv" (v "mod0lo")
         , step, step, step, step, step
         , setFlat "minv" (.SAnd (v "minv") (lit m62))
         , storeLimb tarr "minv" 2 ]

/-! ## §7. 62-step divstep word loop (matrix register-resident) -/

/-- One divstep, written with **single-binop-over-atoms** statements so the
    `setFlat` flattener spawns ZERO `_e{n}` scratch temps (every RHS is already
    flat: `dst op= atom` or `dt = atom op atom`).  Without the SSA-style fresh
    temp per node (`setFlat` on nested `cmn` expressions gives four live
    `_e0.._e3` per statement), the loop-body live set is small enough that
    jasminc's per-function allocator keeps the matrix `dq`/`dr` and the
    masks `c1`/`mask1` **register-resident** instead of spilling them to
    `stack u64` slots, which would cost a stack load/store on every matrix touch
    in the hottest loop (590 invocations under the δ₀=1/2 start).  `dt` is the
    one shared scratch register reused across the three `(x^c1-c1)&c2` reductions. -/
def divstepStep : LowCT :=
  -- dst += ((src ^ c1) - c1) & c2, using the single scratch `dt`.
  let accCmn (dst src : String) : List LowCT :=
    [ setE "dt" (.SXor (v src) (v "c1"))
    , setE "dt" (.SSub (v "dt") (v "c1"))
    , setE "dt" (.SAnd (v "dt") (v "c2"))
    , setE dst (.SAdd (v dst) (v "dt")) ]
  -- dst += other & mask1, using `dt`.
  let accMask (dst other : String) : List LowCT :=
    [ setE "dt" (.SAnd (v other) (v "mask1"))
    , setE dst (.SAdd (v dst) (v "dt")) ]
  seqAll
    ([ setE "c1" (.SAsr (v "eta") (lit 63))
       -- c2 = -(dg & 1)
     , setE "c2" (.SAnd (v "dg") (lit 1))
     , setE "c2" (.SSub (lit 0) (v "c2")) ] ++
     -- g += (f^c1-c1)&c2 ; q += (u^c1-c1)&c2 ; r += (v^c1-c1)&c2
     accCmn "dg" "df" ++ accCmn "dq" "du" ++ accCmn "dr" "dv" ++
     [ setE "mask1" (.SAnd (v "c1") (v "c2"))
       -- eta = (eta ^ mask1) - 1
     , setE "eta" (.SXor (v "eta") (v "mask1"))
     , setE "eta" (.SSub (v "eta") (lit 1)) ] ++
     accMask "df" "dg" ++ accMask "du" "dq" ++ accMask "dv" "dr" ++
     [ setE "dg" (.SShr (v "dg") (lit 1))
     , setE "du" (.SShl (v "du") (lit 1))
     , setE "dv" (.SShl (v "dv") (lit 1)) ])

def divsteps62 : LowCT :=
  seqAll
    [ loadLimb etaarr "eta" 0
      -- δ₀=1/2 (half-delta) start: the 2×2 identity is pre-scaled by 8 = 2^3,
      -- so 3 of the 62 word-bits are "spent" up front and only `dsScnt`
      -- divsteps run.  Each divstep scales u,v by ×2, so the final matrix is
      -- scaled by 8·2^dsScnt; for dsScnt=59 that is exactly 2^62 — the same
      -- divisor `update_de`/`update_fg` use.  This is the EUROCRYPT 2026
      -- (1/2, f, g) starting point (vs the (1, f, g) start's `1,0,0,1` × 62).
    , setN "du" 8, setN "dv" 0, setN "dq" 0, setN "dr" 8
    , loadLimb farr "df" 0
    , loadLimb garr "dg" 0
    , setN "dscnt" dsScnt
    , .RWhileNz "dscnt"
        (seqAll [ divstepStep, setE "dscnt" (.SSub (v "dscnt") (lit 1)) ])
      -- export the matrix to the stack array (loaded JIT in update_de/fg)
    , storeLimb marr "du" 0, storeLimb marr "dv" 1
    , storeLimb marr "dq" 2, storeLimb marr "dr" 3
    , storeLimb etaarr "eta" 0
    ]

/-! ## §8. update_de_62 (i128 accumulators) -/

/-- Common prologue head: load signs `sd`/`se` (matrix-independent). -/
def proSigns : LowCT :=
  seqAll
    [ loadLimb darr "dtop" (n5 - 1)
    , setFlat "sd" (.SAsr (v "dtop") (lit 63))
    , loadLimb earr "etop" (n5 - 1)
    , setFlat "se" (.SAsr (v "etop") (lit 63)) ]

/-- `update_de` prologue, d-half.  Computes `md` (→ `tarr[0]`) and the
    post-`>>=62` `cd` accumulator (→ `tarr[5,6]`).  One i128 accumulator. -/
def updateDEproD : LowCT :=
  seqAll
    [ loadLimb tarr "minv" 2
    , proSigns
      -- md = (du&sd)+(dv&se)
    , ldM 0, setFlat "md" (.SAnd (v "mt") (v "sd"))
    , ldM 1, setFlat "md" (.SAdd (v "md") (.SAnd (v "mt") (v "se")))
      -- cd = du*d0 + dv*e0   (i128)
    , loadLimb darr "d0" 0, loadLimb earr "e0" 0
    , accSetProdM "cd" 0 "d0", accAddProdM "cd" 1 "e0"
      -- md -= (minv*cd_lo + md) & M62
    , setFlat "tmp" (.SAnd (.SAdd (.SMul (v "minv") (accLo "cd")) (v "md")) (lit m62))
    , setFlat "md" (.SSub (v "md") (v "tmp"))
    , storeLimb tarr "md" 0
      -- cd += mod0*md ; cd>>=62
    , loadLimb modarr "mod0" 0
    , accAddProd "cd" "mod0" "md"
    , accAsr62 "cd"
    , storeLimb tarr "cd_lo" 5, storeLimb tarr "cd_hi" 6
      -- stash du,dv into tarr[7,8] for the cd-pass (drops its `marr` param)
    , ldM 0, storeLimb tarr "mt" (matrixTarrCell 0)
    , ldM 1, storeLimb tarr "mt" (matrixTarrCell 1)
    ]

/-- `update_de` prologue, e-half.  Computes `me` (→ `tarr[1]`) and the
    post-`>>=62` `ce` accumulator (→ `tarr[3,4]`).  One i128 accumulator. -/
def updateDEproE : LowCT :=
  seqAll
    [ loadLimb tarr "minv" 2
    , proSigns
      -- me = (dq&sd)+(dr&se)
    , ldM 2, setFlat "me" (.SAnd (v "mt") (v "sd"))
    , ldM 3, setFlat "me" (.SAdd (v "me") (.SAnd (v "mt") (v "se")))
      -- ce = dq*d0 + dr*e0   (i128)
    , loadLimb darr "d0" 0, loadLimb earr "e0" 0
    , accSetProdM "ce" 2 "d0", accAddProdM "ce" 3 "e0"
      -- me -= (minv*ce_lo + me) & M62
    , setFlat "tmp" (.SAnd (.SAdd (.SMul (v "minv") (accLo "ce")) (v "me")) (lit m62))
    , setFlat "me" (.SSub (v "me") (v "tmp"))
    , storeLimb tarr "me" 1
      -- ce += mod0*me ; ce>>=62
    , loadLimb modarr "mod0" 0
    , accAddProd "ce" "mod0" "me"
    , accAsr62 "ce"
    , storeLimb tarr "ce_lo" 3, storeLimb tarr "ce_hi" 4
      -- stash dq,dr into tarr[9,10] for the ce-pass (drops its `marr` param)
    , ldM 2, storeLimb tarr "mt" (matrixTarrCell 2)
    , ldM 3, storeLimb tarr "mt" (matrixTarrCell 3)
    ]

/-! ### Inner-pass residency by unrolling

The cd/ce/cf/cg passes have a **statically-known** trip count (`n5 - 1 = 4`):
limb `ii` runs `1 … n5-1`.  Emitting them as `RWhileNz` runtime loops costs,
per iteration, (a) reloading the loop-invariant matrix entry from the `tarr`
stack stash (`ldMt 0`/`ldMt 1`/`ldM 0`/…), (b) the `ii`/`iim1`/`decnt` counter
arithmetic, and (c) variable-index array touches that jasminc cannot fold to a
fixed displacement.  Unrolling the four-iteration body turns every `ii` into a
compile-time `Nat`, so

  * the matrix multipliers are loaded ONCE (loop-invariant hoist), into named
    `reg u64` scalars `m0`/`m1` that stay register-resident across the whole
    pass;
  * each limb access uses a constant index (`loadLimb`/`storeLimb` — a
    `setN "idx" c` jasminc folds to a fixed `arr[c]` displacement) instead of
    the variable-index `loadLimbV`/`storeLimbV`;
  * the `ii`/`iim1`/`decnt` counter chain disappears entirely.

The accumulator `(acc_lo, acc_hi)` and the hoisted matrix scalars are then a
small, stable live set the jasminc per-fn allocator keeps in GPRs across the
straight-line pass — the residency the runtime loop denied. -/

/-- Hoisted body of one cd/ce/cf/cg accumulate-and-store step at compile-time
    limb index `ii` (`1 ≤ ii ≤ n5-1`).  `m0`/`m1` are the pre-loaded matrix
    multipliers; `redIdx?` is `some j` when the pass carries the modulus
    reduction `acc += mod[ii] * tarr[j]` (de passes: `j = 0` for cd reading
    `md`, `j = 1` for ce reading `me`; fg passes: `none`).  The reduction
    multiplier `tarr[j]` is also loop-invariant, so it is pre-loaded into the
    `mr` scalar by `innerPassUnrolled`; here we only multiply by `mod[ii]`.
    Reads `dsnap`/`esnap` at the constant index `ii`; writes `outa[ii-1]`. -/
def innerPassStep (acc dsa esa outa : String) (ii : Nat)
    (addRed : Bool) : LowCT :=
  let dsaL : Located := { locVar := dsa, locSrc := TowerType.TArr 5 .TU64 }
  let esaL : Located := { locVar := esa, locSrc := TowerType.TArr 5 .TU64 }
  let outaL : Located := { locVar := outa, locSrc := TowerType.TArr 5 .TU64 }
  -- Operand order: the freshly-loaded `di`/`modi` (short live range) is the
  -- FIRST `accAddProd` operand, which `SMulHiS` lowers to the implicit-RAX
  -- operand of `#IMUL`.  Keeping the loop-invariant multiplier (`m0`/`m1`/`mr`,
  -- live across the whole unrolled pass) as the SECOND operand lets the
  -- allocator hold it in a stable GPR away from RAX (the full 128-bit signed
  -- product is commutative, so the swap is value-preserving).
  seqAll
    ([ loadLimb dsaL "di" ii, accAddProd acc "di" "m0"
     , loadLimb esaL "di" ii, accAddProd acc "di" "m1" ] ++
     (if addRed then
        [ loadLimb modarr "modi" ii, accAddProd acc "modi" "mr" ]
      else []) ++
     [ setFlat "wtmp" (accLoMasked acc), storeLimb outaL "wtmp" (ii - 1)
     , accAsr62 acc ])

/-- Unrolled cd/ce/cf/cg pass over the four limbs `1 … n5-1`, then the final
    high limb `outa[n5-1] = acc_lo`.  The matrix multipliers (`m0`,`m1`) and the
    reduction multiplier (`mr = tarr[redIdx]`, present only for the de passes)
    are loaded once before the unrolled body (loop-invariant hoist) and stay
    register-resident across the straight-line body.  `m0FromTarr` chooses
    between the prologue-stashed matrix (`tarr[7..10]`, the de passes) and the
    live `marr` (the fg passes). -/
def innerPassUnrolled (acc dsa esa outa : String)
    (m0Idx m1Idx : Nat) (m0FromTarr : Bool) (redIdx? : Option Nat) : LowCT :=
  let outaL : Located := { locVar := outa, locSrc := TowerType.TArr 5 .TU64 }
  let loadM : LowCT :=
    if m0FromTarr then
      seqAll [ ldMt m0Idx, setE "m0" (v "mt"), ldMt m1Idx, setE "m1" (v "mt") ]
    else
      seqAll [ ldM m0Idx, setE "m0" (v "mt"), ldM m1Idx, setE "m1" (v "mt") ]
  let loadMr : LowCT :=
    match redIdx? with
    | some j => loadLimb tarr "mr" j
    | none   => .RSkip
  let addRed := redIdx?.isSome
  seqAll
    ([ loadM, loadMr ] ++
     ((List.range (n5 - 1)).map (fun k => innerPassStep acc dsa esa outa (k + 1) addRed)) ++
     [ setLimbE outaL (n5 - 1) (accLo acc) ])

/-- `update_de` cd-pass.  Loads the stashed `cd` from `tarr[5,6]`, snapshots
    `d`/`e` into `dsnap`/`esnap` (read by both passes), then runs the cd-pass
    writing `darr`.  Only the `cd` (hi,lo) pair plus the hoisted `m0`/`m1`/`mr`
    multipliers are live (unrolled — see the inner-pass residency lever). -/
def updateDE1 : LowCT :=
  seqAll
    [ loadLimb tarr "cd_lo" 5, loadLimb tarr "cd_hi" 6
      -- Snapshot d,e (both passes read the original d,e).
    , seqAll ((List.range n5).map (fun i =>
        seqAll [ loadLimb darr "di" i, storeLimb dsnap "di" i
               , loadLimb earr "di" i, storeLimb esnap "di" i ]))
      -- cd-pass: d[i-1] = (cd += du*dsnap[i] + dv*esnap[i] + mod[i]*md) & M62
      -- du = tarr[7], dv = tarr[8] (matrix stashed in tarr by the prologue);
      -- md = tarr[0] (the reduction multiplier).
    , innerPassUnrolled "cd" "dsnap" "esnap" "darr" 0 1 true (some 0)
    ]

/-- `update_de` ce-pass.  Reloads the stashed `ce` accumulator from
    `tarr[3,4]` and runs the ce-pass over the `dsnap`/`esnap` snapshots,
    writing `earr`.  Only the `ce` (hi,lo) pair plus hoisted `m0`/`m1`/`mr` live
    (unrolled).  dq = tarr[9], dr = tarr[10]; me = tarr[1]. -/
def updateDE2 : LowCT :=
  seqAll
    [ loadLimb tarr "ce_lo" 3, loadLimb tarr "ce_hi" 4
      -- ce-pass: e[i-1] = (ce += dq*dsnap[i] + dr*esnap[i] + mod[i]*me) & M62
    , innerPassUnrolled "ce" "dsnap" "esnap" "earr" 2 3 true (some 1)
    ]

/-! ## §9. update_fg_62 -/

def updateFG : LowCT :=
  seqAll
    [ loadLimb farr "f0" 0, loadLimb garr "g0" 0
    , accSetProdM "cf" 0 "f0", accAddProdM "cf" 1 "g0"
    , accSetProdM "cg" 2 "f0", accAddProdM "cg" 3 "g0"
    , accAsr62 "cf", accAsr62 "cg"
      -- snapshot f,g (same split-loop rationale as update_de)
    , seqAll ((List.range n5).map (fun i =>
        seqAll [ loadLimb farr "di" i, storeLimb dsnap "di" i
               , loadLimb garr "di" i, storeLimb esnap "di" i ]))
      -- cf-pass (matrix from live `marr` 0,1; no modulus reduction) — unrolled.
    , innerPassUnrolled "cf" "dsnap" "esnap" "farr" 0 1 false none
      -- cg-pass (matrix from live `marr` 2,3; no modulus reduction) — unrolled.
    , innerPassUnrolled "cg" "dsnap" "esnap" "garr" 2 3 false none
    ]

/-! ## §10. normalize_62 (sign = f[N-1]) -/

def normalize : LowCT :=
  seqAll
    [ loadLimb farr "nsign" (n5 - 1)   -- sign of the final f (= input mod)
    , loadLimb darr "dtop" (n5 - 1)
    , setFlat "ca" (.SAsr (v "dtop") (lit 63))
    , seqAll ((List.range n5).map (fun i =>
        seqAll [ loadLimb darr "di" i, loadLimb modarr "modi" i
               , setLimbE darr i (.SAdd (v "di") (.SAnd (v "modi") (v "ca"))) ]))
    , setFlat "cn" (.SAsr (v "nsign") (lit 63))
    , seqAll ((List.range n5).map (fun i =>
        seqAll [ loadLimb darr "di" i
               , setLimbE darr i (.SSub (.SXor (v "di") (v "cn")) (v "cn")) ]))
    , seqAll ((List.range (n5 - 1)).map (fun i =>
        seqAll [ loadLimb darr "di" i, loadLimb darr "di1" (i + 1)
               , setLimbE darr (i + 1) (.SAdd (v "di1") (.SAsr (v "di") (lit 62)))
               , setLimbE darr i (.SAnd (v "di") (lit m62)) ]))
    , loadLimb darr "dtop" (n5 - 1)
    , setFlat "ca" (.SAsr (v "dtop") (lit 63))
    , seqAll ((List.range n5).map (fun i =>
        seqAll [ loadLimb darr "di" i, loadLimb modarr "modi" i
               , setLimbE darr i (.SAdd (v "di") (.SAnd (v "modi") (v "ca"))) ]))
    , seqAll ((List.range (n5 - 1)).map (fun i =>
        seqAll [ loadLimb darr "di" i, loadLimb darr "di1" (i + 1)
               , setLimbE darr (i + 1) (.SAdd (v "di1") (.SAsr (v "di") (lit 62)))
               , setLimbE darr i (.SAnd (v "di") (lit m62)) ]))
    ]

/-! ## §11. Subroutine split

The monolithic kernel passes jasminc typing but its whole-function live-register
set (every `reg`/`stack` local persists for the entire body) overflows jasminc's
*per-function* register allocator — the `regalloc.ml:728` assertion.  We factor
the four dense phases into separate Jasmin `fn` subroutines via `RFnDef`
(lowered to a sibling `#[returnaddress=stack] fn` by `extractFnDefs`) and call
them from the driver via `RFnCall` (a `Ccall .DoNotInline`).  Each subroutine's
live set is then bounded by its own locals plus the few by-reference array
pointers, which fits the GPR budget.

The shared limb state lives in `stack u64[N]` arrays in `main`; each subroutine
takes the arrays it touches as `reg ptr u64[N]` by-reference params and returns
the ones it mutates (the `x = f(x, …)` in-place-update ABI jasminc accepts for
pointer arrays).  The persistent `eta` scalar is threaded by value through
`divsteps62`. -/

/-- `divsteps62` subroutine: 62-step word loop, matrix register-resident,
    exported to `marr`.  Reads `farr[0]`, `garr[0]`, `etaarr[0]`; writes
    `marr`, `etaarr[0]`. -/
def divsteps62Fn (cont : LowCT) : LowCT :=
  .RFnDef "sg62_divsteps"
    [farr, garr, marr, etaarr] [marr, etaarr]
    divsteps62 cont

/-- For `update_fg`, `dsnap`/`esnap` are pure scratch — declared as
    subroutine-local `stack u64[5]` arrays (not by-reference params) so they
    need no `reg mut ptr` threading across the call boundary. -/
def withSnaps (body : LowCT) : LowCT :=
  .RLetZero "dsnap" (.TArr 5 .TU64) <| .RLetZero "esnap" (.TArr 5 .TU64) <| body

/-- `update_de` prologue d-half subroutine.  Reads `darr`, `earr`, `modarr`,
    `marr`; writes `tarr` (md + stashed cd).  No loop, one accumulator. -/
def updateDEproDFn (cont : LowCT) : LowCT :=
  .RFnDef "sg62_update_de_prod"
    [darr, earr, modarr, marr, tarr] [tarr]
    updateDEproD cont

/-- `update_de` prologue e-half subroutine.  Reads `darr`, `earr`, `modarr`,
    `marr`; writes `tarr` (me + stashed ce).  No loop, one accumulator. -/
def updateDEproEFn (cont : LowCT) : LowCT :=
  .RFnDef "sg62_update_de_proe"
    [darr, earr, modarr, marr, tarr] [tarr]
    updateDEproE cont

/-- `update_de` cd-pass subroutine.  In/out `darr`, `dsnap`, `esnap` (the
    snapshots are written here and consumed by `updateDE2`); reads `earr`,
    `modarr`, `tarr` (stashed `cd`, `md`, du/dv matrix).  Only the `cd` i128
    accumulator is live. -/
def updateDE1Fn (cont : LowCT) : LowCT :=
  .RFnDef "sg62_update_de1"
    [darr, earr, modarr, tarr, dsnap, esnap] [darr, dsnap, esnap]
    updateDE1 cont

/-- `update_de` ce-pass subroutine.  In/out `earr`; reads `modarr`, `tarr`
    (stashed `ce`, `me`, dq/dr matrix), `dsnap`, `esnap`.  Only the `ce` i128
    accumulator is live. -/
def updateDE2Fn (cont : LowCT) : LowCT :=
  .RFnDef "sg62_update_de2"
    [earr, modarr, tarr, dsnap, esnap] [earr]
    updateDE2 cont

/-- `update_fg` subroutine.  In/out `farr`, `garr`; reads `marr`;
    `dsnap`/`esnap` subroutine-local scratch. -/
def updateFGFn (cont : LowCT) : LowCT :=
  .RFnDef "sg62_update_fg"
    [farr, garr, marr] [farr, garr]
    (withSnaps updateFG) cont

/-- `normalize` subroutine.  In/out `darr`; reads `modarr`, `farr` (for the
    final-`f` sign). -/
def normalizeFn (cont : LowCT) : LowCT :=
  .RFnDef "sg62_normalize"
    [darr, modarr, farr] [darr]
    normalize cont

/-! ## §12. Top-level driver (calls the subroutines) -/

def innerBody : LowCT :=
  seqAll
    [ loadIOWords "m" "mw"
    , unpackToArr "mw" modarr
    , loadIOWords "a" "aw"
    , unpackToArr "aw" garr
    , seqAll ((List.range n5).map (fun i => setLimbE darr i (lit 0)))
    , seqAll ((List.range n5).map (fun i => setLimbE earr i (lit 0)))
    , setLimbE earr 0 (lit 1)
    , seqAll ((List.range n5).map (fun i =>
        seqAll [ loadLimb modarr "mi" i, storeLimb farr "mi" i ]))
    , modinv62Body
      -- etaarr[0] = -1
    , setN "eta" 0, setFlat "eta" (.SSub (v "eta") (lit 1)), storeLimb etaarr "eta" 0
    , setN "ocnt" outerK4
    , .RWhileNz "ocnt"
        (seqAll [ .RFnCall "sg62_divsteps"   [marr, etaarr] [farr, garr, marr, etaarr]
                , .RFnCall "sg62_update_de_prod" [tarr] [darr, earr, modarr, marr, tarr]
                , .RFnCall "sg62_update_de_proe" [tarr] [darr, earr, modarr, marr, tarr]
                , .RFnCall "sg62_update_de1" [darr, dsnap, esnap]
                                             [darr, earr, modarr, tarr, dsnap, esnap]
                , .RFnCall "sg62_update_de2" [earr] [earr, modarr, tarr, dsnap, esnap]
                , .RFnCall "sg62_update_fg"  [farr, garr] [farr, garr, marr]
                , setFlat "ocnt" (.SSub (v "ocnt") (lit 1)) ])
    , .RFnCall "sg62_normalize" [darr] [darr, modarr, farr]
    , packStore
    ]

/-- Body with the four phase subroutines declared (via `RFnDef`) around the
    driver.  `extractFnDefs` lifts each `RFnDef` body to a sibling FunDecl. -/
def bodyK4 : LowCT :=
  .RLetZero "darr"   (.TArr 5 .TU64) <|
  .RLetZero "earr"   (.TArr 5 .TU64) <|
  .RLetZero "farr"   (.TArr 5 .TU64) <|
  .RLetZero "garr"   (.TArr 5 .TU64) <|
  .RLetZero "modarr" (.TArr 5 .TU64) <|
  .RLetZero "marr"   (.TArr 4 .TU64) <|
  .RLetZero "tarr"   (.TArr 11 .TU64) <|
  .RLetZero "dsnap"  (.TArr 5 .TU64) <|
  .RLetZero "esnap"  (.TArr 5 .TU64) <|
  .RLetZero "etaarr" (.TArr 1 .TU64) <|
  divsteps62Fn <| updateDEproDFn <| updateDEproEFn <| updateDE1Fn <| updateDE2Fn <|
  updateFGFn <| normalizeFn <| innerBody

/-! ## §13. FunDecl + multi-FunDecl emit -/

/-- Scalar locals that `main` reads before assigning (`reg`/`stack` slots
    jasminc rejects if uninitialised).  Helper locals are auto-declared and
    assigned-before-use, so only the driver's own scratch needs zero-init. -/
def mainScalars : List String :=
  (List.range 8).flatMap (fun i => [s!"mw{i}", s!"aw{i}", s!"o{i}"]) ++
  (List.range 16).map (fun i => s!"_e{i}") ++
  ["idx", "wtmp", "plimb", "mi", "mod0lo", "ulo", "uhi", "two",
   "minv", "minv_t", "eta", "ocnt"]

def declScalar (x : String) : InstrR :=
  .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
          .AT_none (.sword .U64) (.Pconst 0)

def ioParam (name : String) : Located := io8 name

/-! ## §13a. ADCX/ADOX dual-carry-chain fusion

`accAddProd acc a b` open-codes the 128-bit signed accumulate
`(acc_hi:acc_lo) += sext128(a*b)` as a 10-instruction tail: a 64-bit add
`nlo = acc_lo + plo`, a five-op branchless carry-out detection
`cyy = ((acc_lo & plo) | ((acc_lo ^ plo) & ~nlo)) >> 63`, and two `acc_hi +=`
folds.  s2n's safegcd uses a *hardware* carry chain for exactly this step;
the residual ~1.7× s2n gap is dominated by this bit-trick
(≈9 surplus ops per 64×64→128 product, ×~590 divsteps' worth of accumulates).

This pass rewrites every `accAddProd` tail to the x86 add-with-carry pair the
verified backend already validates (the `#ADD_64`/`#ADC_64` 6-LVal bundles
`carryBundleCarryIdx` recognises, same instruction family the `bignum_mul_4_8`
ADX kernel uses):

```
  cf, acc_lo = #ADD_64(acc_lo, plo);          // CF := carry-out of the low add
  _,  acc_hi = #ADC_64(acc_hi, phi, cf);       // acc_hi += phi + CF, one µop
```

`cf` is a single `reg bool` (auto-declared by `emitFunDeclCore`'s flag-bank,
which holds `of cf sf pf zf` minus the GPR-used names; here `cf` appears only
in flag positions — an `#ADD_64` carry-out slot and an `#ADC_64` carry-in
operand — so it is classified `reg bool`).  It is produced-then-consumed within
each pair, so reusing the one name across every fused site is correct (no two
are simultaneously live).  The rewrite is **arithmetically identical** to the
bit-trick: `#ADD_64` computes `acc_lo + plo (mod 2^64)` with `CF` the true
carry-out, and `#ADC_64` computes `acc_hi + phi + CF (mod 2^64)` — exactly the
open-coded `nlo`, `cyy`, and the two `acc_hi` folds.  Validated end-to-end by
the modulus-parametric KAT against gmp `mpz_invert`.

The matcher keys on the five scratch names unique to `accAddProd`
(`nlo`/`_g0`/`_g1`/`_g2`/`cyy`); `accSetProd` (no carry) is left untouched. -/

def u64V (x : String) : PExpr :=
  .Pvar { gv := { var := { vname := x, vtype := .sword .U64 }, info := {} }, gs := false }
def u64L (x : String) : LVal :=
  .Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} }
def boolL (x : String) : LVal :=
  .Lvar { var := { vname := x, vtype := .sbool }, info := {} }
def boolV (x : String) : PExpr :=
  .Pvar { gv := { var := { vname := x, vtype := .sbool }, info := {} }, gs := false }
def lnone64 : LVal := .Lnone {} (.sword .U64)
def lnoneBool : LVal := .Lnone {} .sbool

/-- Name carried by a `Pvar`, else `none`. -/
def pvarName? : PExpr → Option String
  | .Pvar gv => some gv.gv.var.vname
  | _ => none
/-- Name carried by an `Lvar`, else `none`. -/
def lvarName? : LVal → Option String
  | .Lvar x => some x.var.vname
  | _ => none

/-- Match a `Cassgn (Lvar dst) _ _ (Papp2 op (Pvar a) (Pvar b))` and return
    `(dst, a, b)`. -/
def matchBin (op : SOp2) : InstrR → Option (String × String × String)
  | .Cassgn lv _ _ (.Papp2 op' (.Pvar a) (.Pvar b)) =>
      if op' = op then
        match lvarName? lv with
        | some d => some (d, a.gv.var.vname, b.gv.var.vname)
        | none => none
      else none
  | _ => none

/-- Match `Cassgn (Lvar dst) _ _ (Papp2 op (Pvar a) (Pconst k))`. -/
def matchBinC (op : SOp2) (k : Int) : InstrR → Option (String × String)
  | .Cassgn lv _ _ (.Papp2 op' (.Pvar a) (.Pconst k')) =>
      if op' = op ∧ k' = k then
        match lvarName? lv with
        | some d => some (d, a.gv.var.vname)
        | none => none
      else none
  | _ => none

/-- Match a bare copy `Cassgn (Lvar dst) _ _ (Pvar src)` → `(dst, src)`. -/
def matchCopy : InstrR → Option (String × String)
  | .Cassgn lv _ _ (.Pvar s) =>
      match lvarName? lv with
      | some d => some (d, s.gv.var.vname)
      | none => none
  | _ => none

/-- Try to recognise the 10-instruction `accAddProd` tail at the head of
    `is`.  On success returns `(acc_lo, acc_hi, plo, phi, rest)`. -/
def matchAccAddProd (is : List InstrR) :
    Option (String × String × String × String × List InstrR) :=
  match is with
  | i0 :: i1 :: i2 :: i3 :: i4 :: i5 :: i6 :: i7 :: i8 :: i9 :: rest => do
      -- nlo = acc_lo + plo
      let (nlo, accLo, plo) ← matchBin (.Oadd .U64) i0
      -- _g0 = acc_lo & plo
      let (g0, a1, b1) ← matchBin (.Oland .U64) i1
      guard (a1 = accLo ∧ b1 = plo)
      -- _g1 = acc_lo ^ plo
      let (g1, a2, b2) ← matchBin (.Olxor .U64) i2
      guard (a2 = accLo ∧ b2 = plo)
      -- _g2 = nlo ^ allOnes
      let (g2, a3) ← matchBinC (.Olxor .U64) (Int.ofNat allOnes64) i3
      guard (a3 = nlo)
      -- _g1 = _g1 & _g2
      let (g1b, a4, b4) ← matchBin (.Oland .U64) i4
      guard (g1b = g1 ∧ a4 = g1 ∧ b4 = g2)
      -- cyy = _g0 ^ _g1
      let (cyy, a5, b5) ← matchBin (.Olxor .U64) i5
      guard (a5 = g0 ∧ b5 = g1)
      -- cyy = cyy >> 63
      let (cyy2, a6) ← matchBinC (.Olsr .U64) 63 i6
      guard (cyy2 = cyy ∧ a6 = cyy)
      -- acc_lo = nlo
      let (accLo2, srcNlo) ← matchCopy i7
      guard (accLo2 = accLo ∧ srcNlo = nlo)
      -- acc_hi = acc_hi + phi
      let (accHi, a8, phi) ← matchBin (.Oadd .U64) i8
      guard (a8 = accHi)
      -- acc_hi = acc_hi + cyy
      let (accHi2, a9, b9) ← matchBin (.Oadd .U64) i9
      guard (accHi2 = accHi ∧ a9 = accHi ∧ b9 = cyy)
      some (accLo, accHi, plo, phi, rest)
  | _ => none

/-- `#ADD_64` / `#ADC_64` replacement for one `accAddProd` tail.  The 6-LVal
    bundle layout is `[of, cf, sf, pf, zf, dst]` (`carryBundleCarryIdx` ⇒
    carry at index 1).  Used for **isolated** accumulates (run length 1), where
    the single-CF pair is already optimal — there is no second product to
    overlap against, so the ADCX/ADOX dual chain (§13b) would only add a flag
    seed + fold with no parallelism gain. -/
def adcCarryPair (accLo accHi plo phi : String) : List InstrR :=
  [ -- cf, acc_lo = #ADD_64(acc_lo, plo)
    .Copn [lnoneBool, boolL "cf", lnoneBool, lnoneBool, lnoneBool, u64L accLo]
          .AT_none (.Oasm ⟨"ADD_64"⟩) [u64V accLo, u64V plo]
    -- _, acc_hi = #ADC_64(acc_hi, phi, cf)
  , .Copn [lnoneBool, lnoneBool, lnoneBool, lnoneBool, lnoneBool, u64L accHi]
          .AT_none (.Oasm ⟨"ADC_64"⟩) [u64V accHi, u64V phi, boolV "cf"] ]

/-! ## §13b. ADCX/ADOX dual-carry-chain fusion

§13a folds each `accAddProd` into a *single* hardware carry chain: `#ADD_64`
threads CF from the low add into the `#ADC_64` high add.  Within a run of
consecutive accumulates into the **same** i128 accumulator — exactly the
cd/ce/cf/cg inner-pass steps, `acc += du·d[i] + dv·e[i] (+ mod[i]·md)` — that
single CF chain serialises *every* add: product `j+1`'s low add waits on
product `j`'s low add (data dep on `acc_lo`), and each high add waits on its
own low add's CF.  s2n's safegcd instead threads **two** independent carries
(the Intel ADX `coreihwl` idiom): ADCX accumulates the low halves through CF,
ADOX accumulates the high halves through OF, so two adds retire per cycle.

This pass, when enabled, rewrites a run of `K ≥ 2` same-accumulator `accAddProd` tails to the
dual chain the verified backend already validates (ADCX→CF only, ADOX→OF only,
2-LVal `[flag_out, dst]` bundles, same `x86_ADCX = waddcarry` semantics for
both — `Model.lean` §`adcx`/`adox`):

```
  _,_,_,_,_, zero := #XOR_64(zero, zero);     // seed CF=OF=0, zero scratch GPR
  for j in 0..K:
    cf, acc_lo := #ADCX(acc_lo, plo_j, cf);   // CF chain: low halves + lo-carry
    of, acc_hi := #ADOX(acc_hi, phi_j, of);   // OF chain: high halves + hi-carry
  cf, acc_hi := #ADCX(acc_hi, zero, cf);       // fold the final low-chain carry
```

**Lo→hi carry crossing.**  Each `#ADCX(acc_lo, plo_j, cf)` adds `acc_lo +
plo_j + CF_in` (CF_in ∈ {0,1}) and threads CF_out into the next add on the same
chain, which targets the same word `acc_lo`; likewise the ADOX chain threads OF
into the next `acc_hi` add instead of discarding it.  In a sum of products into
one accumulator the threaded carry is therefore reinjected into the word it
came out of, so the schedule does not compute the i128 sum in general.
`dualChainAccumulator` gives the analysis and disables this rewrite.

The two chains are flag-disjoint (ADCX writes only CF, ADOX only OF), so
`#ADCX(acc_lo)_j` and `#ADOX(acc_hi)_{j}` issue on the same cycle, and across
products the lo-chain `acc_lo → acc_lo` and hi-chain `acc_hi → acc_hi` form two
independent dependency strands of length `K` instead of one of length `2K`. -/

/-- The dual chain's flag-seed / carry-fold scratch GPR.

    The inline-`#MULX` form issues the per-product limb loads *inside* the chain
    (`idx := c; di := arr[idx]` between the seed and the fold), so `idx` does not
    hold 0 at the fold and the zero operand is a **dedicated** register.
    `azero` is self-XOR-zeroed by the seed and read only by the
    two closing folds (`#ADOX`/`#ADCX(acc_hi, azero)`), so its live range is the
    chain interior and it costs one GPR (declared in `mainScalars` / banked by
    the helper auto-decl). -/
def adxScratch : String := "azero"
def xorL : LVal := u64L adxScratch
def xorV : PExpr := u64V adxScratch

/-- Seed an ADCX/ADOX dual chain: `_,_,_,_,_, azero := #XOR_64(azero, azero)`
    clears both CF and OF (the two carry-in flags) and zeroes the `adxScratch`
    GPR (the second operand of the closing carry folds).  6-LVal flag bundle so
    the emitter banks `cf`/`of` as `reg bool`. -/
def adxSeed : InstrR :=
  .Copn [boolL "of", boolL "cf", lnoneBool, lnoneBool, lnoneBool, xorL]
        .AT_none (.Oasm ⟨"XOR_64"⟩) [xorV, xorV]

-- (An OF-folding carry fold is unsound for unsigned `#MULX` high words; see
-- `dualChainAccumulator` for the analysis.)

/-- Does a `PExpr` mention `accLo`/`accHi` as a variable? -/
partial def exprMentions (accLo accHi : String) : PExpr → Bool
  | .Pvar gv => gv.gv.var.vname = accLo ∨ gv.gv.var.vname = accHi
  | .Papp1 _ a => exprMentions accLo accHi a
  | .Papp2 _ a b => exprMentions accLo accHi a || exprMentions accLo accHi b
  | .PappN _ es => es.any (exprMentions accLo accHi)
  | .Pif _ c a b =>
      exprMentions accLo accHi c || exprMentions accLo accHi a || exprMentions accLo accHi b
  | _ => false

/-- Name written by an `LVal`, if it is a plain register (`Lvar`). -/
def lvalWrites? : LVal → Option String
  | .Lvar x => some x.var.vname
  | _ => none

/-- A name that is an i128-accumulator half (`*_lo` / `*_hi`).  Writing a
    *different* accumulator's half between two products of the current run
    would interleave a second carry region, so the run must stop there — both
    to keep the ADCX/ADOX flag pair short-lived (jasminc pins CF/OF to the
    physical carry registers; a second seed inside the live range conflicts)
    and because the result would still be correct but the dual chain would
    gain nothing.  We therefore treat *any* `*_lo`/`*_hi` write as a barrier. -/
def isAccHalf (s : String) : Bool :=
  s.endsWith "_lo" ∨ s.endsWith "_hi"

/-- Whether an `InstrR` interleaved between two same-accumulator `accAddProd`
    tails is a *barrier* to extending the run.  The safe interleavings are the
    JIT limb loads (`idx`/`di`/`modi`/`mt`), the `plo` product (`plo *= m`, a
    `Cassgn`), and the `phi` product (`#IMUL` / `#MULX`, a flag-bundle `Copn`) —
    none of which name an accumulator half.  Returns `true` (barrier) if the
    instruction reads/writes the current `acc_lo`/`acc_hi`, writes *any* other
    accumulator half, or is a control-flow / call node (a run never crosses a
    `Cwhile`/`Cfor`/`Cif`/`Ccall`). -/
def instrTouches (accLo accHi : String) : InstrR → Bool
  | .Cassgn lv _ _ e =>
      (match lvalWrites? lv with | some d => isAccHalf d | none => false)
      || exprMentions accLo accHi e
  | .Copn lvs _ _ es =>
      lvs.any (fun lv => match lvalWrites? lv with
                          | some d => isAccHalf d | none => false)
      || es.any (exprMentions accLo accHi)
  | _ => true  -- conservatively block runs across loops/branches/calls

/-! ### Inline-`#MULX` dual chain

A hoisting shape keeps `K` product temporaries
(`plo{j}`/`phs{j}`) live across the flag seed — `+2` over the single-CF peak —
which overflows jasminc RA in the dense passes (see `dualChainAccumulator`).
This schedule, matching s2n-bignum's `coreihwl`, instead issues a *flag-free,
two-output* `#MULX` **inline** inside the chain (one product's `plo`/`phu` live
at a time, exactly the single-CF peak) and **defers** the signed high-word
correction to a single post-chain `acc_hi -= corrSum`.

`#MULX(a, b)` writes the unsigned `(hi, lo)` pair in one flag-free instruction
(`Ox86_MULX_lo_hi_instr`, `Model.lean §mulx`), so it can sit *between* two
`#ADOX`s without touching CF/OF.  The schedule for a run of `K` products is:

```
  corrSum := 0;                                  // deferred signed correction
  _,_,_,_,_, zero := #XOR_64(zero, zero);        // seed CF=OF=0
  for j in 0..K:                                 // each product inline:
    phu_j, plo_j := #MULX(a_j, b_j);             //   flag-free unsigned hi:lo
    cf, acc_lo := #ADCX(acc_lo, plo_j, cf);      //   CF chain: low halves
    of, acc_hi := #ADOX(acc_hi, phu_j, of);      //   OF chain: high halves
  of, acc_hi := #ADOX(acc_hi, zero, of);         // drain OF residual
  cf, acc_hi := #ADCX(acc_hi, zero, cf);         // fold final low-chain carry
  acc_hi := acc_hi − corrSum;                    // signed correction, deferred
```

`#MULX` is **unsigned**; the signed high word is `hi_s = hi_u − [a<0]·b −
[b<0]·a` (see `signedHi`).  Summed over the run, the per-product corrections
collapse to one subtract `acc_hi − Σ_j ([a_j<0]·b_j + [b_j<0]·a_j)`.  The
correction ALU ops (`>>s`, `&`, `+`) clobber CF/OF, so they cannot interleave
the carry chain; they are emitted in the **preamble** (before the `#XOR_64`
seed, where flags are dead) accumulating into `corrSum`, and the single
flag-clobbering subtract is the **post-chain** statement.  Each product's
operands `(a_j, b_j)` are short-lived register reads (`di`/`m0`/`m1`/`modi`),
so the only values live across the seed are `corrSum` (one GPR) and the
chain's `acc_lo`/`acc_hi` — the inline `plo_j`/`phu_j` are produced-and-consumed
within one product's `#ADCX`/`#ADOX` window, never accumulating.  This is the
**look-behind** form: the head product's preamble (load + multiply) is matched
*together with* its carry tail (`matchProductFull`), so all `K` products'
`#MULX`es are emitted inline by `fuseCarry`, none hoisted.

The schedule fits jasminc RA but is not arithmetically equal to the §13a serial
CF chain on negative products (the unsigned `#MULX` high word makes the
threaded OF carry nonzero); `dualChainAccumulator` gives the analysis and
disables it. -/

/-- The two's-complement subtraction `acc := acc − corrSum`, open-coded as the
    wrapping add `acc + (~corrSum) + 1` (the emit model's `SSub` arm is
    `Nat`-truncating; threading through `SXor`/`SAdd` keeps the Lean model
    faithful to the wrapping hardware `-`, the same device `signedHi` uses).
    `corrSum` is dead afterwards, so we overwrite it in place with its
    complement. -/
def deferredCorrSub (accHi corrSum : String) : List InstrR :=
  [ .Cassgn (u64L corrSum) .AT_none (.sword .U64)
            (.Papp2 (.Olxor .U64) (u64V corrSum) (.Pconst (Int.ofNat allOnes64)))
  , .Cassgn (u64L accHi) .AT_none (.sword .U64)
            (.Papp2 (.Oadd .U64) (u64V accHi) (u64V corrSum))
  , .Cassgn (u64L accHi) .AT_none (.sword .U64)
            (.Papp2 (.Oadd .U64) (u64V accHi) (.Pconst 1)) ]

/-- Accumulate product `(a, b)`'s signed high-word correction
    `[a<0]·b + [b<0]·a` into `corrSum` (`corrSum += (a>>s63 & b) + (b>>s63 &
    a)`), using the throwaway scratch `_cs`.  All flag-clobbering ALU — emitted
    in the chain *preamble* (flags dead), never between two `#ADOX`s.  `first`
    initialises `corrSum` (set, not add) so no zero-init statement is needed. -/
def corrAccum (corrSum a b : String) (first : Bool) : List InstrR :=
  let sar (d s : String) : InstrR :=
    .Cassgn (u64L d) .AT_none (.sword .U64) (.Papp2 (.Oasr .U64) (u64V s) (.Pconst 63))
  let andd (d x y : String) : InstrR :=
    .Cassgn (u64L d) .AT_none (.sword .U64) (.Papp2 (.Oland .U64) (u64V x) (u64V y))
  let add (d x y : String) : InstrR :=
    .Cassgn (u64L d) .AT_none (.sword .U64) (.Papp2 (.Oadd .U64) (u64V x) (u64V y))
  [ sar "_cs" a, andd "_cs" "_cs" b ]            -- _cs = [a<0]·b
  ++ (if first then [.Cassgn (u64L corrSum) .AT_none (.sword .U64) (u64V "_cs")]
      else [add corrSum corrSum "_cs"])          -- corrSum (:=|+=) _cs
  ++ [ sar "_cs" b, andd "_cs" "_cs" a           -- _cs = [b<0]·a
     , add corrSum corrSum "_cs" ]               -- corrSum += _cs

/-- Close an inline-`#MULX` dual chain (two instructions).  The
    unsigned `#MULX` high word is ≈ 2^64 for a negative product, so the OF chain
    **does** carry out of bit 64.  That OF carry is the overflow into bit 128 of
    the i128 accumulator and must be **discarded** (the i128 wraps mod 2^128) —
    the signed correction `acc_hi −= corrSum` reconciles the unsigned-vs-signed
    high word afterward.  We therefore:

    ```
      of, _      := #ADOX(azero, azero, of);   // drain+discard the OF residual
      cf, acc_hi := #ADCX(acc_hi, azero, cf);   // fold the low-chain carry (CF)
    ```

    The OF `#ADOX` writes a throwaway register (`azero` again, immediately
    overwritten by the `#ADCX` read of the *old* `azero = 0` — they are the same
    `azero`, and `azero` is dead after the fold), giving OF a clean live-range
    end without polluting `acc_hi`.  Only CF, the lo→hi carry, reaches `acc_hi`;
    OF, the overflow out of bit 128, does not. -/
def mulxChainFold (accHi : String) : List InstrR :=
  [ -- drain OF into a dead destination (NOT acc_hi): discard the i128 overflow
    .Copn [boolL "of", lnone64] .AT_none (.Oasm ⟨"ADOX"⟩)
          [xorV, xorV, boolV "of"]
    -- fold the low-chain carry (CF) into acc_hi
  , .Copn [boolL "cf", u64L accHi] .AT_none (.Oasm ⟨"ADCX"⟩)
          [u64V accHi, xorV, boolV "cf"] ]

/-- One inline product of a `#MULX` dual chain: the flag-free two-output
    multiply `phu, plo := #MULX(a, b)` followed by the carry pair
    `cf, acc_lo := #ADCX(acc_lo, plo, cf)` / `of, acc_hi := #ADOX(acc_hi, phu,
    of)`.  `plo`/`phu` are the (per-product, renamed) result registers; because
    `#MULX` touches no flag, the multiply issues *inside* the chain with no
    hoist — only this product's `plo`/`phu` live at a time. -/
def mulxProductInline (accLo accHi a b plo phu : String) : List InstrR :=
  [ -- phu, plo := #MULX(a, b)  (BMI2 unsigned hi:lo, flag-free)
    .Copn [u64L phu, u64L plo] .AT_none (.Oasm ⟨"MULX"⟩) [u64V a, u64V b]
    -- cf, acc_lo := #ADCX(acc_lo, plo, cf)
  , .Copn [boolL "cf", u64L accLo] .AT_none (.Oasm ⟨"ADCX"⟩)
          [u64V accLo, u64V plo, boolV "cf"]
    -- of, acc_hi := #ADOX(acc_hi, phu, of)
  , .Copn [boolL "of", u64L accHi] .AT_none (.Oasm ⟨"ADOX"⟩)
          [u64V accHi, u64V phu, boolV "of"] ]

/-- Match a full product `plo := a*b; phi := #IMUL(a,b)` preamble immediately
    followed by its 10-instruction `accAddProd` carry tail (`matchAccAddProd`).
    Returns `(a, b, accLo, accHi, rest)` — the multiply *source* operands plus
    the accumulator halves.  This is the **look-behind** matcher: it consumes the
    head product's multiply preamble *together with* its carry tail, so the
    inline-`#MULX` rewrite can reconstruct the multiply inside the chain (the
    `fuseCarry` forward-stream otherwise emits the head preamble before the tail
    matches).  The preamble shape is exactly `accAddProd`'s first two statements:
    `Cassgn plo (Omul a b)` then `Copn IMUL [_,_,_,_,_, phi, _] [a, b]`. -/
def matchProductFull (is : List InstrR) :
    Option (String × String × String × String × List InstrR) :=
  match is with
  | p0 :: p1 :: tailAndRest => do
      -- plo := a * b
      let (_plo, a, b) ← matchBin (.Omul .U64) p0
      -- _,_,_,_,_, phi, _ := #IMUL(a, b)
      match p1 with
      | .Copn _ _ (.Oasm op) [pa, pb] =>
          guard (op.name = "IMUL")
          guard (pvarName? pa = some a ∧ pvarName? pb = some b)
          let (accLo, accHi, _plo2, _phi, rest) ← matchAccAddProd tailAndRest
          some (a, b, accLo, accHi, rest)
      | _ => none
  | _ => none

/-- Maximum number of *further* products on a single dual chain (chain length
    `≤ maxExtraProducts + 1`).  `1` ⇒ chains of two products — the GPR-pressure
    sweet spot (see `collectRunFromTail`). -/
def maxExtraProducts : Nat := 1

/-- Whether an accumulator (named by its `*_lo` half) may carry a dual chain.

    **`false` — the inline-`#MULX` dual chain is arithmetically incompatible
    with summing into a *single* i128 accumulator.**

    §13a fuses each i128 multiply-accumulate to a single-CF `#ADD_64`/`#ADC_64`
    pair (1.49× s2n).  The **look-behind inline-`#MULX` rewrite**
    (`matchProductFull` + `peelHeadLoads` + `collectMulxRun` +
    `mulxProductInline` + deferred `corrSum`) issues the `#MULX`es *inside* the
    chain, one product's `plo`/`phu` live at a time, with the signed correction
    deferred to a post-chain `acc_hi −= corrSum`.  It fits jasminc RA
    (`jasminc -arch x86-64` exits 0 on every pass — 48 `#ADCX` + 48 `#ADOX`
    + 32 `#MULX`, no fallback).

    The dual chain is **arithmetically wrong** on negative products, for a
    reason no scheduling removes:

    * `#ADOX` *threads* the high chain's inter-product carry (OF) between the two
      `#ADOX(acc_hi, phu_j)`s.  When two products' high words are summed into the
      **same** accumulator half, that inter-product OF carry is an overflow past
      bit 64 of `acc_hi` — i.e. past **bit 128** of the i128 — and must be
      *discarded* (the i128 wraps mod 2^128).  `#ADOX` cannot discard it: it
      adds OF into the next `#ADOX`.
    * For the *signed* `#IMUL` high word (small, sign-extended) the sum
      `phu0 + phu1` never overflows bit 64, so OF stays 0 and the spurious
      threading is a no-op.  The
      *unsigned* `#MULX` high word is ≈ 2^64 for a **negative** product, so
      `acc_hi + phu0` overflows, OF = 1, and threading it bumps `acc_hi` by 1.
      The deferred signed correction fixes the *value* of each high word but not
      this spurious carry.  A Lean model of both schedules exhibits it: with
      `a0 = b0 = −1` (`2^64−1`), `hi0 = 5`, the serial accumulate gives high word
      5, the threaded dual chain gives 6 — off by exactly the OF carry.  The KAT
      fails on **every** input (`0 OK / 4132 FAIL` vs gmp `mpz_invert`).

    The ADX dual-chain idiom is sound only when each `#MULX` high word flows into
    a **distinct** word lane (the schoolbook multiply, `BignumMontMulKernel.lean`
    — there the threaded OF carry is the *legitimate* carry into the next lane).
    Summing `K` products into one i128 needs the high words pre-reduced to the
    *signed* (small) form before `#ADOX`, which requires the flag-clobbering
    `signedHi` correction *inside* the chain — defeating the flag-free `#MULX`
    that makes the inline schedule possible.  No reordering avoids this.

    **Two further alternatives fail in an arithmetic model (off by ±1).**  The
    obstruction above is the
    *same-word accumulation* defect: `#ADCX`/`#ADOX` thread a carry from one add
    to the *next add on the same chain*, but in a single-accumulator sum the
    next same-chain add targets the **same** word (`acc_lo += plo_j` then
    `acc_lo += plo_{j+1}`), so the threaded carry is reinjected into the word it
    came out of instead of flowing to the next-higher word.  This is orthogonal
    to the high-word sign issue, so neither of the two register-pressure escapes
    helps:

    * **(A) 3-limb sign-extended accumulator** (`acc_lo`/`acc_hi`/`acc_ext` at
      `2^0`/`2^64`/`2^128`, the standard signed-multiprecision form, `+1` GPR
      not the hoist's `+2`).  Gives the *high* word a real lane for the `#ADOX`
      overflow — but the `#ADCX` chain still reinjects `acc_lo`'s carry into
      `acc_lo`.  A 2-million-trial C model of the threaded schedule vs the serial
      `__int128` accumulate fails ~50% of inputs, off by `±1` in the low word.
    * **(B) hoist the *signed* (`signedHi`) high words** (what freeing 2 GPRs by
      spilling the cold pointer params would enable).  The premise that OF stays
      0 on signed high words is false: a 3-million-trial model of the hoisted
      signed-high-word dual chain fails ~64% of inputs, off by `±1` in the high
      word (the OF chain threads non-zero inter-product carries even on small
      signed high words).  Register pressure is not the obstruction — the inline
      path fits RA — so freeing GPRs cannot change the arithmetic.

    The ADX dual-chain idiom needs consecutive same-chain adds to target
    *staggered* word lanes (the schoolbook diagonal); a sum-of-products into one
    accumulator has none.

    **Two more alternatives (D, a schoolbook-diagonal restructure; C, a
    signed-`#MULX`-with-carry primitive) fail in C models, consistent with the
    s2n-bignum reference.**

    The s2n-bignum modular inverter (`x86/generic/bignum_modinv.S`,
    `word_divstep59.S`) uses **zero** `#ADCX`/`#ADOX`/`#MULX`: its matrix-vector
    update (`Lbignum_modinv_congloop`/`crossloop`) sums exactly two products per
    output limb with plain `mulq` + a *single CF chain* (`adcq d, h1`), rolling a
    128-bit `(h1:l1)` accumulator across the limb loop.  That is **exactly §13a**
    — the 1.49× path.  s2n's ADX lives only in its *schoolbook* multiply
    kernels (curve25519/p256/p521), where same-chain adds target staggered lanes.

    * **(D) schoolbook-diagonal restructure.**  The update accumulate is a *dot
      product* (every product at weight `2^0`); it has no diagonal.  Placing
      product `j` at lane `j` (the only staggered placement that lets `#ADCX`/
      `#ADOX` carries flow to a distinct higher lane) multiplies product `j` by
      `2^{64j}` — wrong value.  C-model: 2 M / 2 M FAIL.  A sound two-pass
      regroup exists but each pass is a serial single-CF chain (= §13a, no
      speedup).
    * **(C) signed-`#MULX`-with-carry primitive.**  Inescapable dilemma: the
      carry's correct lane (`acc_hi`) *is* the other strand.  Retiring each
      product's carry into `acc_hi` per product is correct but serially dependent
      (degenerates to §13a, no dual-chain parallelism); threading it forward to
      the next low add keeps an independent strand but reinjects the carry into
      the same word (the same-word defect above, 2.5 M / 3 M FAIL).  No op achieves both
      independence and correct placement, because the `K` low words share lane
      `2^0`.

    The obstruction is the same for both: a sum of products into ONE
    accumulator has no second word lane for a threaded carry, so the schoolbook
    ADX idiom does not apply; s2n-bignum also avoids ADX here.  The C models
    are not part of the repository.

    The accumulators therefore use `SMulHiS` (`#IMUL`) on the §13a single-CF
    chain (1.49× s2n).  The inline-`#MULX` machinery
    (`matchProductFull`/`peelHeadLoads`/`collectMulxRun`/`mulxProductInline`/
    `corrAccum`/`deferredCorrSub`/`mulxChainFold`) is RA-validated and
    KAT-bisected (`maxExtraProducts = 0` ⇒ the run-1 `#IMUL` path KATs 4132 OK),
    and is disabled by this gate. -/
def dualChainAccumulator (_accLo : String) : Bool :=
  false

/-- Rewrite `accAddProd` open-coded carry tails to hardware add-with-carry.

    * When `dualChainAccumulator` holds (it is `false`), a run of `K ≥ 2`
      consecutive same-accumulator products (the cd/ce/cf/cg inner-pass
      `acc += Σ m·limb` steps) is lowered to the inline-`#MULX`
      ADCX/ADOX **dual** carry chain: a deferred-correction preamble, a
      flag seed, `K` inline `#MULX`+`#ADCX`(CF)/`#ADOX`(OF) products, a low-carry
      fold, and the post-chain signed correction.  The multiplies are issued
      *inside* the chain (flag-free `#MULX`), so no product temporaries are
      hoisted — register pressure stays flat (only `corrSum` + the renamed
      head-operand survive the seed).
    * Otherwise each product (including an isolated one, e.g. the prologue
      `cd += mod0·md`) uses the §13a single `#ADD_64`/`#ADC_64` pair (`#IMUL` high word; no
      overlap to exploit, and no `signedHi` correction to amortise).

    The look-behind `matchProductFull` consumes the head product's multiply
    preamble *together with* its carry tail, so all `K` products' `#MULX`es land
    inside the chain (a forward-streaming `fuseCarry` would emit the head
    preamble before the tail matched).  Recurses into loop / branch bodies. -/
partial def fuseCarry : List InstrR → List InstrR
  | [] => []
  | is@(i :: rest) =>
      -- Peel the head product's leading JIT loads (`idx := c; di := dsnap[idx]`)
      -- so they can be re-issued *inside* the inline-`#MULX` chain — the
      -- preamble correction pass reloads the operand register, clobbering `di`,
      -- so the head product (like the others) must reload before its `#MULX`.
      -- Only when the dual chain is enabled; the §13a single-CF path needs no
      -- peel (it matches the bare carry tail directly).
      let (lead0, afterLead) :=
        if dualChainAccumulator "" then peelHeadLoads is else ([], is)
      -- Then the look-behind full-product match (multiply preamble + carry tail):
      -- the entry point for the inline-`#MULX` dual chain.
      match (if dualChainAccumulator "" then matchProductFull afterLead else none) with
      | some (a0, b0, accLo, accHi, tail) =>
          -- Collect further same-accumulator products (each `(loads, a, b)`):
          -- `loads` are the acc-independent instructions (the JIT limb reload)
          -- preceding the product, re-issued so the operand reaches the chain.
          let (extra, post) := collectMulxRun accLo accHi tail
          match extra with
          | [] =>
              -- Run length 1: no overlap to exploit.  Fall back to the §13a
              -- single-CF `#ADD_64`/`#ADC_64` pair, re-emitting the head
              -- product's load + `#IMUL` multiply (cheaper than `#MULX`+correction
              -- when unamortised — see `signedHi`).  The head load + preamble
              -- were peeled / consumed, so we re-materialise them.
              lead0 ++
              [ .Cassgn (u64L "plo") .AT_none (.sword .U64)
                        (.Papp2 (.Omul .U64) (u64V a0) (u64V b0))
              , .Copn [lnoneBool, lnoneBool, lnoneBool, lnoneBool, lnoneBool,
                       u64L "phi", lnone64] .AT_none (.Oasm ⟨"IMUL"⟩)
                      [u64V a0, u64V b0] ]
                ++ adcCarryPair accLo accHi "plo" "phi"
                ++ fuseCarry tail
          | _ =>
              -- Run length ≥ 2.  Build the inline-`#MULX` dual chain.  Each
              -- product reloads its shared operand register (`di` ← dsnap/esnap)
              -- just before use, so **only one** product's `di` is live at a
              -- time (matching the single-CF peak).  We keep the operand name
              -- un-renamed: `#MULX`'s first factor is the implicit `RDX`, and
              -- two distinct names both destined for RDX collide in jasminc RA.
              --
              -- The signed correction's flag-clobbering ALU (`>>s`/`&`/`+`)
              -- cannot interleave the carry chain, so it is computed in a
              -- **separate preamble** that re-loads each operand (cheap `MOV`s)
              -- and accumulates into `corrSum`; the chain region then re-loads
              -- and issues the flag-free `#MULX`+`#ADCX`/`#ADOX` per product.
              -- Only `corrSum` is live across the seed (`+1` over single-CF) —
              -- the 128-bit `plo{j}`/`phu{j}` are produced-and-consumed within
              -- one product's `#ADCX`/`#ADOX` window.
              let products : List (List InstrR × String × String) := (lead0, a0, b0) :: extra
              -- Preamble: per product, (re)load operand then fold its correction.
              let corrPre :=
                (products.zipIdx 0).flatMap (fun (p, j) =>
                  let (loads, a, b) := p
                  loads ++ corrAccum "corrSum" a b (j = 0))
              -- Chain: seed, then per product (re)load operand + inline product.
              let chain :=
                (products.zipIdx 0).flatMap (fun (p, j) =>
                  let (loads, a, b) := p
                  loads ++ mulxProductInline accLo accHi a b s!"plo{j}" s!"phu{j}")
              corrPre
                ++ [adxSeed]
                ++ chain
                ++ mulxChainFold accHi
                ++ deferredCorrSub accHi "corrSum"
                ++ fuseCarry post
      | none =>
          -- No look-behind product after the leading loads.  If we peeled
          -- nothing, fall through to the bare-carry-tail / control-flow handling
          -- on the original head `i`.  If we *did* peel loads but no product
          -- followed, those loads are ordinary instructions: emit them and
          -- recurse on the remainder (do NOT drop them).
          match lead0 with
          | _ :: _ => lead0 ++ fuseCarry afterLead
          | [] =>
            match matchAccAddProd is with
            | some (accLo, accHi, plo, phi, tail) =>
                adcCarryPair accLo accHi plo phi ++ fuseCarry tail
            | none =>
                let i' := match i with
                  | .Cwhile cb c ca => .Cwhile (fuseCarry cb) c (fuseCarry ca)
                  | .Cfor v r body  => .Cfor v r (fuseCarry body)
                  | .Cif c th el    => .Cif c (fuseCarry th) (fuseCarry el)
                  | other => other
                i' :: fuseCarry rest
where
  /-- From the instructions *after* the head full-product, collect the
      *further* same-accumulator products of the run, in **look-behind / inline**
      form.  Each product is `(loads, a, b)`: `loads` the acc-independent
      instructions (the JIT limb reload) preceding it, and `(a, b)` its multiply
      source operands.  The product's own 12-instruction body (multiply preamble
      + carry tail) is dropped — replaced by the inline `#MULX`+`#ADCX`/`#ADOX`
      the caller emits.  Returns `(products, rest)`; `products = []` ⇒ length 1.

      `pend` carries the acc-independent instructions seen since the last
      product (committed to the next product's `loads` when its full-product
      match fires).  Capped at `maxExtraProducts` further products. -/
  collectMulxRun (accLo accHi : String) (tail : List InstrR) :
      (List (List InstrR × String × String) × List InstrR) :=
    let rec go : List (List InstrR × String × String) → List InstrR → List InstrR →
        (List (List InstrR × String × String) × List InstrR)
      | prods, pend, [] => (prods, pend)
      | prods, pend, j :: js =>
          if prods.length ≥ maxExtraProducts then (prods, pend ++ (j :: js))
          else
          match matchProductFull (j :: js) with
          | some (a, b, h0, h1, t) =>
              if h0 = accLo ∧ h1 = accHi then
                go (prods ++ [(pend, a, b)]) [] t
              else (prods, pend ++ (j :: js))
          | none =>
              if instrTouches accLo accHi j then (prods, pend ++ (j :: js))
              else go prods (pend ++ [j]) js
    go [] [] tail
  /-- Peel the leading JIT-load instructions of a head product: simple
      acc-independent `Cassgn`s (`idx := c`, `di := arr[idx]`) up to — but not
      including — the product's `plo := a*b` (`Omul`) low-word multiply.  Stops
      at the first non-load: an `Omul` `Cassgn` (product start), a `Copn` /
      control-flow node, or an acc-half write.  Capped at 4 (the JIT reload is
      `idx := c; di := arr[idx]`); the cap keeps the peel from swallowing an
      unrelated straight-line prefix.  The peeled loads are re-issued inside the
      inline-`#MULX` chain (the correction preamble clobbers the operand reg).
      Returns `(lead, rest)` with `rest` positioned at the product (if any). -/
  peelHeadLoads (is : List InstrR) : (List InstrR × List InstrR) :=
    let rec go (n : Nat) (acc : List InstrR) :
        List InstrR → (List InstrR × List InstrR)
      | [] => (acc.reverse, [])
      | k :: ks =>
          match n, k with
          | 0, _ => (acc.reverse, k :: ks)
          | _+1, .Cassgn lv _ _ e =>
              -- stop at the product's low-word `plo := a*b`
              match e with
              | .Papp2 (.Omul .U64) _ _ => (acc.reverse, k :: ks)
              | _ =>
                  match lvalWrites? lv with
                  | some d => if isAccHalf d then (acc.reverse, k :: ks)
                              else go n (k :: acc) ks
                  | none => (acc.reverse, k :: ks)
          | _+1, _ => (acc.reverse, k :: ks)
    go 4 [] is

/-- The split program: lift every `RFnDef` to a sibling `#[returnaddress=stack]
    fn` (spilled) and emit the driver as the `export fn`, concatenated into one
    `.jazz`.  Each function body is post-processed by `fuseCarry`, replacing
    the open-coded i128 carry-bit-trick with hardware add-with-carry: the single
    `#ADD_64`/`#ADC_64` pair (§13a) for every product, since the ADCX(CF)/ADOX(OF)
    dual chain of §13b is disabled by `dualChainAccumulator`. -/
def emitSplit : Option String := do
  let (helperFds, residual) := LowCT.extractFnDefs bodyK4
  let helperFds := helperFds.map (fun fd => { fd with body := fuseCarry fd.body })
  let mainFd : FunDecl :=
    { name := { name := "safegcd_divstep62_invert_k4" }
    , params := [ioParam "out", ioParam "a", ioParam "m"].map (fun loc =>
                  { var := { var := LowCT.locToVar loc, info := {} } })
    , body := fuseCarry (mainScalars.map declScalar ++ LowCT.toJasminCmd residual)
    , results := [{ var := LowCT.locToVar (io8 "out"), info := {} }] }
  let helperStrs ← helperFds.mapM Emit.emitFunDeclRastackSpill
  let mainStr ← Emit.emitFunDeclSpill mainFd
  some (String.intercalate "\n" helperStrs ++ "\n" ++ mainStr)

-- #eval (LowCT.extractFnDefs bodyK4).1.length   -- number of lifted helpers

-- `signedHi`: flag-free `#MULX` + branchless signed correction, for use
-- in the inline-MULX dual chain (see `dualChainAccumulator`).  10 LowCT
-- statements; lowers to one `#MULX` + arithmetic-shift / and / xor / add ops,
-- no `#IMUL`, no wide-immediate `xor`.
-- #eval (signedHi "phi" "mt" "di").length          -- = 10

private def main : IO Unit := do
  IO.FS.createDirAll "bench/mpn_invert_safegcd_compare/gen_divstep"
  match emitSplit with
  | some s => do
      IO.FS.writeFile
        "bench/mpn_invert_safegcd_compare/gen_divstep/safegcd_divstep62_invert_k4.jazz" s
      IO.println "wrote gen_divstep/safegcd_divstep62_invert_k4.jazz (subroutine-split)"
  | none => IO.println "FAILED: emit none for safegcd_divstep62_invert_k4"

end CatCrypt.Crypto.Vale.SafegcdDivstep62Emit

private def main : IO Unit := CatCrypt.Crypto.Vale.SafegcdDivstep62Emit.main
