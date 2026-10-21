/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTSyntax
public import CatCrypt.Crypto.Jasmin.LowCTSyntax
public meta import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public meta import CatCrypt.Crypto.Jasmin.JasminEmit
public import CatCrypt.Crypto.Jasmin.JasminEmit

/-!
# Bernstein-Yang safegcd divstep modular inverse — emitted kernel

The 30-bit-radix (`libsecp256k1 modinv32`) Bernstein-Yang divstep modular
inverter, authored as a `LowCT` body and emitted through the verified
front (`LowCT.toJasminCmd` → `Emit.emitFunDeclSpill`) to a
jasminc-compilable `.jazz`.

This **retires** the AUCurves `mpn_invert_safegcd` Rust leaf for the size it
covers: instead of an `extCall` to an opaque verified-CT Rust symbol (the
3-axiom adoption in `Vale/MpnInvert.lean`), the divstep loop is *owned* by
CatCrypt and emitted limb-for-limb.

## Why 30-bit radix (not the 62-bit `safegcd.rs`)

The AUCurves `safegcd.rs` `update_de_62`/`update_fg_62` use **i128**
accumulators (`t.u as i128 * d.v[0] as i128`, products up to ~2^124). The
emit DSL's `SExpr` is **64-bit** (`BitVec 64` two's-complement model). The
libsecp256k1 `modinv32` variant uses **30-bit limbs** with **int64**
accumulators — every product (`t.u * limb`, ≤ 2^31 · 2^30 = 2^61) and every
accumulator fits in 64 bits. So the whole divstep loop lowers to `SMulS`
(signed 64-bit mul, → Jasmin `*`), `SAsr` (arithmetic shift, → `>>s`),
`SAdd`/`SSub`/`SAnd`/`SShl`/`SShr` — exactly the signed-arith SExpr ops.

For a 256-bit modulus: `N9 = 9` limbs of 30 bits (= 270 bits, top limb
partial). The C ground truth
(`bench/mpn_invert_safegcd_compare/divstep30_ref.c`, `modinv30_k4`)
validates byte-exact / `a·inv ≡ 1` against libgmp `mpz_invert` (2463 OK / 0
FAIL / 3000 random). This module transcribes that exact algorithm.

## Limb storage: u32[9] stack arrays

The four 9-limb vectors `d, e, f, g` and the modulus live in **`stack
u32[9]` arrays** (each 30-bit limb in a u32 cell, int32 two's-complement
pattern). Holding 45 limbs as named `reg u64` overflows the 16 x86-64 GPRs
(jasminc register allocation fails); the array form keeps only the few limbs
touched by a given step in registers. The 2×2 transition matrix
`(tu,tv,tq,tr)` and the accumulators stay scalar.

The input `a` and modulus `m` arrive as `reg ptr u32[8]` (256-bit LE, 8 u32
words); the output `out` is the same shape, written once after normalize.

## Constant-time

Control flow is data-independent in `a` (the secret): `OUTER_K4` outer
iterations × 30 divsteps, all conditional updates via mask-and-merge
(`x & c2`, `c2 = -(g&1)`), no secret branch — `RWhileNz` countdowns with
public bounds.
-/

@[expose] public section

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT

namespace CatCrypt.Crypto.Vale.SafegcdDivstepEmit

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §0. Constants and layout (k=4 / 256-bit, 9×30-bit) -/

def m30 : Nat := 1073741823   -- 2^30 − 1
def m32 : Nat := 4294967295   -- 2^32 − 1 (u32 wrap mask)
def n9 : Nat := 9
def outerK4 : Nat := 25       -- libsecp256k1 modinv32 outer count

/-! ## §1. SExpr / command helpers -/

def v (x : String) : SExpr := .SVar x
def lit (n : Nat) : SExpr := .SLit n
def setE (x : String) (e : SExpr) : LowCT := .RScalarSetExpr x e
def setN (x : String) (n : Nat) : LowCT := .RScalarSet x n

def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | c :: rest => .RSeq c (seqAll rest)

def wrap32 (x : String) : LowCT := setE x (.SAnd (v x) (lit m32))
def mask30 (dst src : String) : LowCT := setE dst (.SAnd (v src) (lit m30))

/-! ### SExpr flattener

jasminc's surface asmgen rejects a *nested* arithmetic RHS (e.g. `(a >> k) ^
(b << j)` or `(a*b) + (c*d)`): every `RScalarSetExpr` must lower to a SINGLE
binop over atoms (`SVar`/`SLit`). `flatten` rewrites an arbitrary `SExpr`
into a sequence of single-binop `RScalarSetExpr`s using fresh scratch slots
`_e0, _e1, …`, returning the command sequence and the final atom. -/

def isAtom : SExpr → Bool
  | .SVar _ => true
  | .SLit _ => true
  | _ => false

/-- Worklist flattener. `cnt` is the fresh-name counter. Returns
    `(commands, atom, nextCounter)`. -/
partial def flattenAux (cnt : Nat) : SExpr → (List LowCT × SExpr × Nat)
  | .SVar x => ([], .SVar x, cnt)
  | .SLit k => ([], .SLit k, cnt)
  | e =>
    -- e is a binary node `mk a b`; flatten children to atoms, then emit one binop.
    let (mk, a, b) := match e with
      | .SAdd a b => (SExpr.SAdd, a, b)
      | .SSub a b => (SExpr.SSub, a, b)
      | .SMul a b => (SExpr.SMul, a, b)
      | .SMulS a b => (SExpr.SMulS, a, b)
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

/-- Emit single-binop statements computing `e` into scalar `dst` (each
    `RScalarSetExpr` becomes one jasminc-legal binop). -/
def setFlat (dst : String) (e : SExpr) : LowCT :=
  if isAtom e then setE dst e
  else
    let (cmds, atom, _) := flattenAux 0 e
    seqAll (cmds ++ [setE dst atom])

/-! ## §2. Limb-array slots (`stack u32[9]`) and access helpers -/

def darr : Located := { locVar := "darr", locSrc := TowerType.TArr 9 .TU32 }
def earr : Located := { locVar := "earr", locSrc := TowerType.TArr 9 .TU32 }
def farr : Located := { locVar := "farr", locSrc := TowerType.TArr 9 .TU32 }
def garr : Located := { locVar := "garr", locSrc := TowerType.TArr 9 .TU32 }
def modarr : Located := { locVar := "modarr", locSrc := TowerType.TArr 9 .TU32 }
/-- 6-cell array holding the 2×2 transition matrix `[tu,tv,tq,tr]` plus the
    `update_de` reduction multipliers `[md,me]` (each ≤ 2^31 in magnitude,
    fits an int32 cell).  Keeping these in a stack array (loaded
    sign-extended just-in-time, with short live ranges) rather than 6
    persistent `reg u64` is what keeps the statically-unrolled limb passes
    inside the x86-64 GPR budget. -/
def tarr : Located := { locVar := "tarr", locSrc := TowerType.TArr 7 .TU32 }
def u32s (x : String) : Located := { locVar := x, locSrc := TowerType.TU32 }
def io8 (x : String) : Located := { locVar := x, locSrc := TowerType.TArr 8 .TU32 }

/-- Load limb `i` of array `arr` into scalar `dst`, **sign-extended** from the
    int32 pattern: the `RArrLoad` zero-extends u32→u64, then `(x<<32)>>s32`
    recovers the signed int32 value. Uses index scalar `idx`. -/
def loadLimbS (arr : Located) (dst : String) (i : Nat) : LowCT :=
  seqAll [ setN "idx" i
         , .RArrLoad (u32s dst) arr "idx"
           -- sext32(dst) = (dst << 32) >>s 32, as two single-op statements
         , setE dst (.SShl (v dst) (lit 32))
         , setE dst (.SAsr (v dst) (lit 32)) ]

/-- Load limb `i` of `arr` into `dst` **without** sign extension (raw 30-bit
    non-negative value). -/
def loadLimbU (arr : Located) (dst : String) (i : Nat) : LowCT :=
  seqAll [ setN "idx" i
         , .RArrLoad (u32s dst) arr "idx" ]

/-- Store scalar `src` into limb `i` of `arr` (the `RArrStore` narrows
    u64→u32, keeping the int32 pattern). -/
def storeLimb (arr : Located) (src : String) (i : Nat) : LowCT :=
  seqAll [ setN "idx" i, .RArrStore arr "idx" (u32s src) ]

/-- Set limb `i` of `arr` from the value of `SExpr e` (flattening nested ops
    into single-binop statements via scratch `_eN`). -/
def setLimbE (arr : Located) (i : Nat) (e : SExpr) : LowCT :=
  seqAll [ setFlat "wtmp" e, storeLimb arr "wtmp" i ]

/-- Runtime-index sign-extended load: `dst := sext32(arr[idxName])`. -/
def loadLimbSV (arr : Located) (dst idxName : String) : LowCT :=
  seqAll [ .RArrLoad (u32s dst) arr idxName
         , setE dst (.SShl (v dst) (lit 32))
         , setE dst (.SAsr (v dst) (lit 32)) ]

/-- Runtime-index store: `arr[idxName] := src`. -/
def storeLimbV (arr : Located) (src idxName : String) : LowCT :=
  .RArrStore arr idxName (u32s src)

/-! ## §3. Unpack 8×u32 (LE, `a`/`m`) → 9×30-bit limbs into a target array

word = bit/32, off = bit%32; `lo = w[word] >> off`; spill `hi = w[word+1] <<
(32-off)` if `off≠0 ∧ word+1<8`; `limb = (lo ^ hi) & M30` (disjoint within
the low 30 bits, so `^` = `|`). -/

def loadIOWords (src : String) (pfx : String) : LowCT :=
  seqAll ((List.range 8).flatMap (fun i =>
    [ setN "idx" i, .RArrLoad (u32s s!"{pfx}{i}") (io8 src) "idx" ]))

/-- Unpack limb `i` into `arr[i]`, broken into single-op statements (jasminc
    asmgen rejects a `(a >> k) ^ (b << j)` nested rexpr in one instruction):
    `lo = w >> off; hi = wnext << (32-off); lo = lo ^ hi; arr[i] = lo & M30`. -/
def unpackLimbCmd (pfx : String) (arr : Located) (i : Nat) : LowCT :=
  let bit := 30 * i
  let wi := bit / 32
  let off := bit % 32
  let loInit : LowCT :=
    if off == 0 then setE "ulo" (v s!"{pfx}{wi}")
    else setE "ulo" (.SShr (v s!"{pfx}{wi}") (lit off))
  let merge : LowCT :=
    if off ≠ 0 ∧ wi + 1 < 8 then
      seqAll [ setE "uhi" (.SShl (v s!"{pfx}{wi + 1}") (lit (32 - off)))
             , setE "ulo" (.SXor (v "ulo") (v "uhi")) ]
    else .RSkip
  seqAll [ loInit, merge, setLimbE arr i (.SAnd (v "ulo") (lit m30)) ]

def unpackToArr (pfx : String) (arr : Located) : LowCT :=
  seqAll ((List.range n9).map (fun i => unpackLimbCmd pfx arr i))

/-! ## §4. Pack `darr` (9×30-bit) → 8×u32 (LE) into `out`

`out[bit/32] |= (limb << (bit%32))` (low 32 bits) and spill `out[bit/32+1] |=
(limb >> (32-bit%32))`. Accumulate into scalars `o0..o7`, mask to 32, store. -/

def packStore : LowCT :=
  let zero := seqAll ((List.range 8).map (fun i => setN s!"o{i}" 0))
  let accum := seqAll ((List.range n9).map (fun i =>
    let bit := 30 * i
    let wi := bit / 32
    let off := bit % 32
    let ld : LowCT := loadLimbU darr "plimb" i
    let lm : LowCT := mask30 "plimb" "plimb"
    let shifted : SExpr := if off == 0 then v "plimb" else .SShl (v "plimb") (lit off)
    let lo : LowCT :=
      setFlat s!"o{wi}" (.SAnd (.SXor (v s!"o{wi}") shifted) (lit m32))
    let hi : LowCT :=
      if off ≠ 0 ∧ wi + 1 < 8 then
        setFlat s!"o{wi + 1}"
          (.SAnd (.SXor (v s!"o{wi + 1}") (.SShr (v "plimb") (lit (32 - off)))) (lit m32))
      else .RSkip
    seqAll [ld, lm, lo, hi]))
  let store := seqAll ((List.range 8).flatMap (fun i =>
    [ setN "idx" i, .RArrStore (io8 "out") "idx" (u32s s!"o{i}") ]))
  seqAll [zero, accum, store]

/-! ## §5. modulus^{-1} mod 2^30 (Newton, 4 doublings; all u32 wrap) -/

def modinv30Body : LowCT :=
  -- Newton: x ← x·(2 − m·x) mod 2^32, four times.  `2 − y` is computed as
  -- `two − y` with `two` a materialised scalar (jasminc has no const-minuend
  -- subtract in a single instruction).
  let step : LowCT :=
    seqAll [ setFlat "minv_t" (.SMul (v "mod0lo") (v "minv"))
           , wrap32 "minv_t"
           , setN "two" 2
           , setFlat "minv_t" (.SSub (v "two") (v "minv_t"))
           , wrap32 "minv_t"
           , setFlat "minv" (.SMul (v "minv") (v "minv_t"))
           , wrap32 "minv" ]
  seqAll [ loadLimbU modarr "mod0lo" 0     -- low modulus limb (30-bit)
         , setFlat "minv" (v "mod0lo")
         , step, step, step, step
         , mask30 "minv" "minv"
           -- stash minv in tarr[6]; it is dead through the whole divstep word
           -- loop and is reloaded only in update_de, so it need not occupy a
           -- register across the outer loop.
         , storeLimb tarr "minv" 6 ]

/-! ## §6. 30-step divstep word loop (`divsteps_30`)

State: `eta` (signed), `du,dv,dq,dr` (matrix, u32), `df,dg` (bottom words,
u32). 30 steps; matrix exported sign-extended into `tu,tv,tq,tr`. `c1 =
(eta >>s 31) & 0xFFFFFFFF`; `c2 = (0 - (dg&1)) & 0xFFFFFFFF`. -/

def divstepStep : LowCT :=
  -- `cmn (var) c2 = ((var ^ c1) - c1) & c2` folded inline — no xx/yy/zz named
  -- temps — to keep the divstep-loop live-scalar count inside the GPR budget.
  let cmn (var : String) : SExpr :=
    .SAnd (.SAnd (.SSub (.SXor (v var) (v "c1")) (v "c1")) (lit m32)) (v "c2")
  seqAll
    [ setFlat "c1" (.SAnd (.SAsr (v "eta") (lit 31)) (lit m32))
      -- c2 = -(dg & 1) as u32 mask, via ~x+1 (avoids const-minuend subtract)
    , setFlat "c2" (.SAnd (v "dg") (lit 1))
    , setFlat "c2" (.SXor (v "c2") (lit m32))
    , setFlat "c2" (.SAdd (v "c2") (lit 1))
    , setFlat "c2" (.SAnd (v "c2") (lit m32))
      -- g += (f^c1-c1)&c2 ; q += (u^c1-c1)&c2 ; r += (v^c1-c1)&c2  (read old df/du/dv)
    , setFlat "dg" (.SAnd (.SAdd (v "dg") (cmn "df")) (lit m32))
    , setFlat "dq" (.SAnd (.SAdd (v "dq") (cmn "du")) (lit m32))
    , setFlat "dr" (.SAnd (.SAdd (v "dr") (cmn "dv")) (lit m32))
    , setFlat "mask1" (.SAnd (v "c1") (v "c2"))
      -- eta = (eta ^ (int32)mask1) - 1 : sign-extend mask1 (0 / 0xFFFFFFFF)
    , setFlat "eta" (.SSub (.SXor (v "eta") (.SAsr (.SShl (v "mask1") (lit 32)) (lit 32))) (lit 1))
    , setFlat "df" (.SAnd (.SAdd (v "df") (.SAnd (v "dg") (v "mask1"))) (lit m32))
    , setFlat "du" (.SAnd (.SAdd (v "du") (.SAnd (v "dq") (v "mask1"))) (lit m32))
    , setFlat "dv" (.SAnd (.SAdd (v "dv") (.SAnd (v "dr") (v "mask1"))) (lit m32))
    , setFlat "dg" (.SShr (v "dg") (lit 1))
    , setFlat "du" (.SAnd (.SShl (v "du") (lit 1)) (lit m32))
    , setFlat "dv" (.SAnd (.SShl (v "dv") (lit 1)) (lit m32))
    ]

def divsteps30 : LowCT :=
  seqAll
    [ setN "du" 1, setN "dv" 0, setN "dq" 0, setN "dr" 1
    , loadLimbU farr "df" 0
    , loadLimbU garr "dg" 0
    , setN "dscnt" 30
    , .RWhileNz "dscnt"
        (seqAll [ divstepStep, setFlat "dscnt" (.SSub (v "dscnt") (lit 1)) ])
      -- store the raw u32 matrix words to `tarr` (loaded sign-extended on use)
    , storeLimb tarr "du" 0, storeLimb tarr "dv" 1
    , storeLimb tarr "dq" 2, storeLimb tarr "dr" 3
    ]

/-! ## §7. update_de_30 (64-bit accumulators) -/

/-- Load matrix word `i` of `tarr` sign-extended into temp `dst`. -/
def ldT (dst : String) (i : Nat) : LowCT := loadLimbS tarr dst i

def updateDE : LowCT :=
  seqAll
    [ -- reload minv (stashed in tarr[6] across the divstep word loop)
      loadLimbU tarr "minv" 6
      -- sd = sign(d[N-1]) ; se = sign(e[N-1])  (top limbs are signed)
    , loadLimbS darr "dtop" (n9 - 1)
    , setFlat "sd" (.SAsr (v "dtop") (lit 31))
    , loadLimbS earr "etop" (n9 - 1)
    , setFlat "se" (.SAsr (v "etop") (lit 31))
      -- md = (tu&sd)+(tv&se) ; me = (tq&sd)+(tr&se)   (matrix loaded JIT)
    , ldT "t" 0, setFlat "md" (.SAnd (v "t") (v "sd"))
    , ldT "t" 1, setFlat "md" (.SAdd (v "md") (.SAnd (v "t") (v "se")))
    , ldT "t" 2, setFlat "me" (.SAnd (v "t") (v "sd"))
    , ldT "t" 3, setFlat "me" (.SAdd (v "me") (.SAnd (v "t") (v "se")))
      -- cd = tu*d0 + tv*e0 ; ce = tq*d0 + tr*e0
    , loadLimbS darr "d0" 0, loadLimbS earr "e0" 0
    , ldT "t" 0, setFlat "cd" (.SMulS (v "t") (v "d0"))
    , ldT "t" 1, setFlat "cd" (.SAdd (v "cd") (.SMulS (v "t") (v "e0")))
    , ldT "t" 2, setFlat "ce" (.SMulS (v "t") (v "d0"))
    , ldT "t" 3, setFlat "ce" (.SAdd (v "ce") (.SMulS (v "t") (v "e0")))
      -- md -= (minv*cd_lo + md_lo) & M30
    , setFlat "tmp" (.SAnd (.SAdd (.SMul (v "minv") (.SAnd (v "cd") (lit m32)))
                               (.SAnd (v "md") (lit m32))) (lit m30))
    , setFlat "md" (.SSub (v "md") (v "tmp"))
    , setFlat "tmp" (.SAnd (.SAdd (.SMul (v "minv") (.SAnd (v "ce") (lit m32)))
                               (.SAnd (v "me") (lit m32))) (lit m30))
    , setFlat "me" (.SSub (v "me") (v "tmp"))
      -- save md, me into tarr[4], tarr[5] for the inner-loop reloads
    , storeLimb tarr "md" 4, storeLimb tarr "me" 5
      -- cd += mod0*md ; ce += mod0*me ; cd>>=30 ; ce>>=30
    , loadLimbS modarr "mod0" 0
    , setFlat "cd" (.SAdd (v "cd") (.SMulS (v "mod0") (v "md")))
    , setFlat "ce" (.SAdd (v "ce") (.SMulS (v "mod0") (v "me")))
    , setFlat "cd" (.SAsr (v "cd") (lit 30))
    , setFlat "ce" (.SAsr (v "ce") (lit 30))
      -- i = 1..N-1 as a runtime countdown loop (ONE block → register reuse).
      -- `ii` walks 1..N-1; `iim1 = ii-1` is the store index; `decnt` = N-1 → 1.
    , setN "ii" 1, setN "decnt" (n9 - 1)
    , .RWhileNz "decnt"
        (seqAll
          [ loadLimbSV darr "di" "ii"
          , ldT "t" 0, setFlat "cd" (.SAdd (v "cd") (.SMulS (v "t") (v "di")))
          , ldT "t" 2, setFlat "ce" (.SAdd (v "ce") (.SMulS (v "t") (v "di")))
          , loadLimbSV earr "ei" "ii"
          , ldT "t" 1, setFlat "cd" (.SAdd (v "cd") (.SMulS (v "t") (v "ei")))
          , ldT "t" 3, setFlat "ce" (.SAdd (v "ce") (.SMulS (v "t") (v "ei")))
          , loadLimbSV modarr "modi" "ii"
          , ldT "t" 4, setFlat "cd" (.SAdd (v "cd") (.SMulS (v "modi") (v "t")))
          , ldT "t" 5, setFlat "ce" (.SAdd (v "ce") (.SMulS (v "modi") (v "t")))
          , setFlat "iim1" (.SSub (v "ii") (lit 1))
          , setFlat "wtmp" (.SAnd (v "cd") (lit m30)), storeLimbV darr "wtmp" "iim1"
          , setFlat "cd" (.SAsr (v "cd") (lit 30))
          , setFlat "wtmp" (.SAnd (v "ce") (lit m30)), storeLimbV earr "wtmp" "iim1"
          , setFlat "ce" (.SAsr (v "ce") (lit 30))
          , setFlat "ii" (.SAdd (v "ii") (lit 1))
          , setFlat "decnt" (.SSub (v "decnt") (lit 1)) ])
    , setLimbE darr (n9 - 1) (v "cd")
    , setLimbE earr (n9 - 1) (v "ce")
    ]

/-! ## §8. update_fg_30 -/

def updateFG : LowCT :=
  seqAll
    [ loadLimbS farr "f0" 0, loadLimbS garr "g0" 0
    , ldT "t" 0, setFlat "cf" (.SMulS (v "t") (v "f0"))
    , ldT "t" 1, setFlat "cf" (.SAdd (v "cf") (.SMulS (v "t") (v "g0")))
    , ldT "t" 2, setFlat "cg" (.SMulS (v "t") (v "f0"))
    , ldT "t" 3, setFlat "cg" (.SAdd (v "cg") (.SMulS (v "t") (v "g0")))
    , setFlat "cf" (.SAsr (v "cf") (lit 30))
    , setFlat "cg" (.SAsr (v "cg") (lit 30))
    , setN "ii" 1, setN "decnt" (n9 - 1)
    , .RWhileNz "decnt"
        (seqAll
          [ loadLimbSV farr "fi" "ii"
          , ldT "t" 0, setFlat "cf" (.SAdd (v "cf") (.SMulS (v "t") (v "fi")))
          , ldT "t" 2, setFlat "cg" (.SAdd (v "cg") (.SMulS (v "t") (v "fi")))
          , loadLimbSV garr "gi" "ii"
          , ldT "t" 1, setFlat "cf" (.SAdd (v "cf") (.SMulS (v "t") (v "gi")))
          , ldT "t" 3, setFlat "cg" (.SAdd (v "cg") (.SMulS (v "t") (v "gi")))
          , setFlat "iim1" (.SSub (v "ii") (lit 1))
          , setFlat "wtmp" (.SAnd (v "cf") (lit m30)), storeLimbV farr "wtmp" "iim1"
          , setFlat "cf" (.SAsr (v "cf") (lit 30))
          , setFlat "wtmp" (.SAnd (v "cg") (lit m30)), storeLimbV garr "wtmp" "iim1"
          , setFlat "cg" (.SAsr (v "cg") (lit 30))
          , setFlat "ii" (.SAdd (v "ii") (lit 1))
          , setFlat "decnt" (.SSub (v "decnt") (lit 1)) ])
    , setLimbE farr (n9 - 1) (v "cf")
    , setLimbE garr (n9 - 1) (v "cg")
    ]

/-! ## §9. normalize_30 (sign = f[N-1]) -/

def normalize : LowCT :=
  seqAll
    [ -- cond_add = sign(d[N-1])
      loadLimbS darr "dtop" (n9 - 1)
    , setFlat "ca" (.SAsr (v "dtop") (lit 31))
    , seqAll ((List.range n9).map (fun i =>
        seqAll [ loadLimbS darr "di" i, loadLimbS modarr "modi" i
               , setLimbE darr i (.SAdd (v "di") (.SAnd (v "modi") (v "ca"))) ]))
      -- cond_neg = sign(nsign)   (nsign already holds f[N-1], sign-extended)
    , setFlat "cn" (.SAsr (v "nsign") (lit 31))
    , seqAll ((List.range n9).map (fun i =>
        seqAll [ loadLimbS darr "di" i
               , setLimbE darr i (.SSub (.SXor (v "di") (v "cn")) (v "cn")) ]))
      -- carry propagate: d[i+1] += d[i] >>s 30 ; d[i] &= M30
    , seqAll ((List.range (n9 - 1)).map (fun i =>
        seqAll [ loadLimbS darr "di" i, loadLimbS darr "di1" (i + 1)
               , setLimbE darr (i + 1) (.SAdd (v "di1") (.SAsr (v "di") (lit 30)))
               , setLimbE darr i (.SAnd (v "di") (lit m30)) ]))
      -- second cond_add
    , loadLimbS darr "dtop" (n9 - 1)
    , setFlat "ca" (.SAsr (v "dtop") (lit 31))
    , seqAll ((List.range n9).map (fun i =>
        seqAll [ loadLimbS darr "di" i, loadLimbS modarr "modi" i
               , setLimbE darr i (.SAdd (v "di") (.SAnd (v "modi") (v "ca"))) ]))
    , seqAll ((List.range (n9 - 1)).map (fun i =>
        seqAll [ loadLimbS darr "di" i, loadLimbS darr "di1" (i + 1)
               , setLimbE darr (i + 1) (.SAdd (v "di1") (.SAsr (v "di") (lit 30)))
               , setLimbE darr i (.SAnd (v "di") (lit m30)) ]))
    ]

/-! ## §10. Top-level inner body (wrapped in array allocations by §11) -/

def innerBody : LowCT :=
  seqAll
    [ -- unpack m → modarr, a → garr
      loadIOWords "m" "mw"
    , unpackToArr "mw" modarr
    , loadIOWords "a" "aw"
    , unpackToArr "aw" garr
      -- d = 0, e = 0 with e[0]=1, f = mod
    , seqAll ((List.range n9).map (fun i => setLimbE darr i (lit 0)))
    , seqAll ((List.range n9).map (fun i => setLimbE earr i (lit 0)))
    , setLimbE earr 0 (lit 1)
    , seqAll ((List.range n9).map (fun i =>
        seqAll [ loadLimbU modarr "mi" i, storeLimb farr "mi" i ]))
      -- minv := mod0^{-1} mod 2^30
    , modinv30Body
      -- eta = -1
    , setN "eta" 0, setFlat "eta" (.SSub (v "eta") (lit 1))
      -- outer loop
    , setN "ocnt" outerK4
    , .RWhileNz "ocnt"
        (seqAll [ divsteps30, updateDE, updateFG
                , setFlat "ocnt" (.SSub (v "ocnt") (lit 1)) ])
      -- normalize with sign = f[N-1]
    , loadLimbS farr "nsign" (n9 - 1)
    , normalize
      -- pack d → out
    , packStore
    ]

/-- Body wrapped in the five `stack u32[9]` array allocations. -/
def bodyK4 : LowCT :=
  .RLetZero "darr"   (.TArr 9 .TU32) <|
  .RLetZero "earr"   (.TArr 9 .TU32) <|
  .RLetZero "farr"   (.TArr 9 .TU32) <|
  .RLetZero "garr"   (.TArr 9 .TU32) <|
  .RLetZero "modarr" (.TArr 9 .TU32) <|
  .RLetZero "tarr"   (.TArr 4 .TU32) <|
  innerBody

/-! ## §11. FunDecl + emit -/

def allScalars : List String :=
  (List.range 8).flatMap (fun i => [s!"mw{i}", s!"aw{i}", s!"o{i}"]) ++
  -- flattener scratch pool `_e0.._e11`
  (List.range 12).map (fun i => s!"_e{i}") ++
  ["idx", "wtmp", "plimb", "mi", "mod0lo", "ulo", "uhi", "two",
   "minv", "minv_t", "eta", "ocnt", "dscnt", "nsign",
   "du", "dv", "dq", "dr", "df", "dg",
   "c1", "c2", "mask1", "t",
   "sd", "se", "md", "me", "cd", "ce", "cf", "cg", "tmp",
   "dtop", "etop", "d0", "e0", "f0", "g0", "mod0",
   "di", "ei", "fi", "gi", "modi", "ca", "cn",
   "ii", "decnt", "iim1"]

def declScalar (x : String) : InstrR :=
  .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
          .AT_none (.sword .U64) (.Pconst 0)

/-- `.sarr 32` (32 bytes) → emitter renders `reg ptr u32[8]`. -/
def ptrParam (name : String) : FunParam :=
  { var := { var := { vname := name, vtype := .sarr 32 }, info := {} } }
def ptrResult (name : String) : VarI :=
  { var := { vname := name, vtype := .sarr 32 }, info := {} }

/-- The emitted FunDecl: `out, a, m : u32[8]` reg-ptr (= 256-bit LE). -/
def divstepK4Fd : FunDecl :=
  { name := { name := "safegcd_divstep_invert_k4" }
  , params := [ptrParam "out", ptrParam "a", ptrParam "m"]
  , body := allScalars.map declScalar ++ LowCT.toJasminCmd bodyK4
  , results := [ptrResult "out"] }

-- #eval allScalars.length
-- #eval (LowCT.toJasminCmd bodyK4).length

/-- Emit driver: writes the spill-emitted text of `divstepK4Fd` (see the module docstring
on register pressure) to
`bench/mpn_invert_safegcd_compare/gen_divstep/safegcd_divstep_invert_k4.jazz`, relative
to the working directory. Run by `bench/mpn_invert_safegcd_compare/emit_k4.lean`. -/
def emitK4 : IO Unit := do
  IO.FS.createDirAll "bench/mpn_invert_safegcd_compare/gen_divstep"
  match Emit.emitFunDeclSpill divstepK4Fd with
  | some s => do
      IO.FS.writeFile
        "bench/mpn_invert_safegcd_compare/gen_divstep/safegcd_divstep_invert_k4.jazz" s
      IO.println "wrote gen_divstep/safegcd_divstep_invert_k4.jazz"
  | none => IO.println "FAILED: emit none for safegcd_divstep_invert_k4"

end CatCrypt.Crypto.Vale.SafegcdDivstepEmit
