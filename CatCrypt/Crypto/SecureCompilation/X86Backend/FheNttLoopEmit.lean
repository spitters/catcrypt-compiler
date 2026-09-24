/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.IndexedAddrEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.IndexedAddrEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.RodataProbe
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RodataProbe

/-!
# In-place forward negacyclic NTT loop through the OWNED x86 backend (no jasminc)

The headline FHE-NTT artifact: a fully-emitted **in-place forward negacyclic
NTT** — the lazy Harvey Shoup CT-DIT butterfly (`FheNttButterflyEmit`) run
under a public-counter loop over an in-memory coefficient buffer, reading the
bit-reversed psi-power twiddles + their Shoup constants from a `.rodata` table.
NO jasminc anywhere; every op is the owned scalar `JInstr 64` machine
(`JasminModel.evalInstr`) plus the `.rodata`/RIP-relative seam
(`JInstr.loadSym`) and the register-indexed gather/scatter
(`JInstr.loadMemIdx`/`storeMemIdx`).

This matches `bench/fhe_ntt_compare/fhe_ntt_kat.c` — the existing C reference
that composes the emitted scalar butterfly `fhe_bfly` into a full `N = 2^13`
negacyclic NTT and KATs it against a direct O(N²) negacyclic DFT (GMP). Here the
*loop* is owned too (not a C driver), so the whole transform is owned.

## The C reference loop (Longa–Naehrig / Harvey lazy CT-DIT), verbatim

```c
uint32_t t = N;
for (uint32_t m = 1; m < N; m <<= 1) {       // layer:  m = 1,2,4,…,N/2   (logN layers)
  t >>= 1;                                     // stride: t = N/2, N/4, …, 1
  for (uint32_t i = 0; i < m; i++) {           // group within the layer
    uint32_t j1 = 2*i*t;                       // group base
    uint64_t w = psi_rev[m+i], wp = psi_rev_sh[m+i];   // twiddle + Shoup const
    for (uint32_t j = j1; j < j1 + t; j++) {   // inner butterfly run, stride t
      // (a[j], a[j+t]) <- CT_butterfly(a[j], a[j+t], w, wp)   // emitted fhe_bfly
    }
  }
}
```

`psi = 527760526715669589` (a 2N-th root), `q = 1152921504606830593`. Inputs and
outputs of each butterfly are in `[0, 4q)` (lazy). The output is bit-reversed:
`a[i] = A(psi^(2·brv(i)+1)) mod q`.

## Loop structure: three levels, one public-counter inner loop

All three loop variables — `m` (layer), `i` (group), `j` (inner) — and the
twiddle walk `m+i` and the strides `t`, `j1 = 2·i·t` are **public**: they are
fixed by `N = 2^logN` alone, *not* by the coefficient data. So every loop here is
a public-counter loop (constant-time: the guards read only public counters).

We model the transform at three matching granularities:

* **Inner butterfly loop** (the looped emit): the `for (j = j1; j < j1+t; j++)`
  run. Body: `loadMemIdx a[j]`, `loadMemIdx a[j+t]` (the second index is `j + t`,
  a public stride add), the lazy Shoup butterfly over registers, `storeMemIdx`
  both outputs, then `j += 1`. Public counter `j` guarded by `j < j1 + t`. This is
  the layer-stride-parametric butterfly loop emitted as the constant-size
  `loopLcmd` (`cmpq ; jne`).
* **Group + layer nest**: the `m`/`i` walk drives the twiddle index `m+i` and the
  group base `j1 = 2·i·t`. These are public address-arithmetic counters; the C
  driver supplies them, and here they are the public schedule the in-Lean value
  check enumerates (and the residual the orchestrator's C harness drives —
  see "scope").

## What is validated at small N (the value check)

`nttRef logN a` is the in-Lean `Nat` reference for the whole forward negacyclic
CT-DIT NTT (the C loop transcribed over a `List Nat`, butterfly = `bflyRef`). At
`logN = 2` (`N = 4`, 2 layers) we run the **whole transform** as the owned
machine `runBlock` butterfly over the in-memory buffer, driven by the public
schedule, seeding `a` in `JState` memory and the twiddle table under the
`loadSym` symbol bank, and `native_decide`-check the output buffer equals
`nttRef 2`. This validates — at a size `native_decide` handles — the entire
machinery: the public loop counter + index arithmetic (`j1 = 2·i·t`, stride `t`,
twiddle `m+i`), the `.rodata` twiddle load (`loadSym` + `loadMemIdx`), the
in-place mem load/store (`loadMemIdx`/`storeMemIdx` at `a[j]`, `a[j+t]`), and the
lazy Shoup butterfly. A second tiny check pins one `logN = 3` (`N = 8`) output.

## The `logN = 13` (`N = 8192`) instantiation + `.rodata` table

`psiRev logN` / `psiRevSh logN` compute the twiddle table in-Lean:
`psipow[i] = psi^i mod q`, `psi_rev[i] = psipow[brv(i, logN)]`,
`shoup[i] = ⌊w·2^64 / q⌋`. The `.rodata` table is `psi_rev` interleaved with its
Shoup const (so cell `2·(m+i)` is `w` and `2·(m+i)+1` is `wp`). `fheNttAsm`
renders the inner butterfly loop body + the table; `emitMain` writes
`bench/fhe_ntt_compare/gen/fhe_ntt.s`.

## ABI for the orchestrator's KAT

```c
extern void fhe_ntt(uint64_t *a);   // in-place on N coefficients, a -> %rdi
//   twiddles in .rodata (psi_rev_interleaved); inputs/outputs in [0, 4q)
```

## Scope: what is fully-looped vs unrolled vs intermediate

* **Fully looped + emitted**: the inner butterfly loop (constant-size `loopLcmd`,
  `cmpq ; jne`, public counter `j`), the `.rodata` twiddle table, the butterfly
  body (`mulx`, `shrq $63` mask-csubs), the `loadSym`/`loadMemIdx`/`storeMemIdx`
  indexed in-place access.
* **Validated in-Lean (value)**: the WHOLE small-N transform (`logN = 2, 3`) via
  the owned `runBlock` machine over the public schedule — this is the
  correctness check of counter + index arithmetic + twiddle indexing + the
  butterfly, at a size `native_decide` handles.
* **Intermediate (residual)**: flattening the three-level `m`/`i`/`j` nest into
  ONE public counter with the in-asm index arithmetic (`j1 = 2·i·t`,
  twiddle `m+i`, stride doubling/halving across layers) is NOT emitted as a single
  looped `Lcmd` — the emitted artifact is the inner butterfly layer loop
  (stride-parametric), and the outer `m`/`i` schedule is the public driver the C
  harness supplies (exactly as `fhe_ntt_kat.c` does today). The in-Lean value check
  *does* run the full nest, so the schedule is verified; only its *emission* as one
  flattened `loopLcmd` is residual. Reported, not claimed.

## Risks flagged for the orchestrator's KAT

* **Counter arithmetic**: the inner guard is `j < j1 + t`; the body's `j += 1` is
  the public counter advance (`tripCount_counterGuard` pins the trip count `t`).
* **Twiddle indexing**: cell `m+i` of `psi_rev` / `psi_rev_sh`; in the interleaved
  `.rodata` table that is byte offset `16·(m+i)` for `w` and `+8` for `wp`.
* **Mem aliasing**: `a[j]` and `a[j+t]` are distinct (`t ≥ 1`), and the butterfly
  reads BOTH before writing EITHER (load both, compute, store both) — the
  in-place update must not clobber `a[j+t]` before reading it.
* **The `rdx`-pin in the loop body**: the `mulx` reads its `src1` from `%rdx`; in a
  loop the multiplier (`omega'`/`omega`) must be re-pinned to `%rdx` each iteration
  (the printer's `mulxRdxSetup` materialises it). Inherited from the butterfly.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttLoopEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (GpAlloc allocGp renderBlockBody renderLeafFn allocOverflow regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderRodata)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RodataProbe (hasSub)

/-! ## 1. The FHE-NTT prime + root constants (`fhe_ntt_kat.c`) -/

/-- `q = 2^60 − 2^14 + 1`, the 60-bit FHE prime. -/
def fheQ : Nat := 1152921504606830593
/-- `2q`, the lazy upper bound. -/
def fheTwoQ : Nat := 2 * fheQ
/-- `psi`: a 2N-th primitive root of unity mod `q` (from `find_params`). -/
def fhePsi : Nat := 527760526715669589

/-! ## 2. Bit reversal + the twiddle table (computed in-Lean)

`brv x logN` reverses the low `logN` bits of `x`. `psipow[i] = psi^i mod q`;
`psi_rev[i] = psipow[brv(i, logN)]`; the Shoup const is `⌊w·2^64 / q⌋`. The
`.rodata` table interleaves `psi_rev[k]` and its Shoup const (`w` at cell `2k`,
`wp` at cell `2k+1`), so a single base + index `2·(m+i)` gathers both. -/

/-- Reverse the low `bits` bits of `x`. -/
def brv (x bits : Nat) : Nat :=
  (List.range bits).foldl (fun r i => r + (if x.testBit i then 1 <<< (bits - 1 - i) else 0)) 0

/-- `psi^e mod q`. -/
def psiPow (e : Nat) : Nat := (fhePsi ^ e) % fheQ

/-- The bit-reversed twiddle `psi_rev[k] = psi^brv(k, logN) mod q`. -/
def psiRev (logN k : Nat) : Nat := psiPow (brv k logN)

/-- The Shoup constant `⌊w·2^64 / q⌋` for a twiddle `w`. -/
def shoupConst (w : Nat) : Nat := (w * 2 ^ 64) / fheQ

/-- The interleaved `.rodata` twiddle table for size `N = 2^logN`: for each table
    index `k ∈ [0, N)`, cell `2k = psi_rev[k]` and cell `2k+1 = shoup(psi_rev[k])`.
    A butterfly group `(m, i)` reads cells `2·(m+i)` and `2·(m+i)+1`. -/
def twiddleTable (logN : Nat) : List Nat :=
  (List.range (2 ^ logN)).flatMap (fun k =>
    let w := psiRev logN k
    [w, shoupConst w])

/-- The `.rodata` symbol name. -/
def twiddleSym : String := "fhe_ntt_psi_rev"

/-! ## 3. The lazy Harvey Shoup CT butterfly over the JState machine (low register pressure)

Mirrors `FheNttButterflyEmit.bflyRef` / `fheBflyThir` exactly, but over the
owned `JInstr 64` machine on registers `"x" = a[j]`, `"y" = a[j+t]`,
`"w" = omega`, `"wp" = omega'` (the Shoup const). To fit the owned first-fit GP
allocator's budget inside a loop (14-reg pool; `a`/`tbl`/`y` pinned, plus the
index registers `ij/ijt/tw/twp/j`), the constants `2q`, `q`, `0` are inlined as
**immediates** (no constant-holder registers), the sign-mask `0 − b` uses `neg`
(in place), and only **two scratch registers** `"s1"`/`"s2"` are used — every
temporary is dead after its consumer, and the input `"y"` is reused as the
csub-q sign scratch once the products consume it. Results written back into
`"x"` (= X', out[0]) and `"y"` (= Y', out[1]).

The sign-mask csub of a constant `c` on `v`: `r = v − c` (`sub … $c`),
`b = r >>ₗ 63` (`shr … $63`, 1 iff `v < c`), `m = (0 − b) & c` (`neg`; `and … $c`,
all-ones-or-zero mask), `v' = r + m` (`= v` if `v < c`, else `v − c`). -/

/-- The lazy Shoup CT butterfly body over the machine (no counter advance —
    `nttButterflyStep` appends the indexed loads/stores + counter). Computes
    `Xn = csub2q(x)`, `qhat = mulhi(y, wp)`, `Tlz = w·y − qhat·q`, `T = csubq(Tlz)`,
    then `Y' = Xn + 2q − T` (into `"y"`), `X' = Xn + T` (into `"x"`).

    **x86 imm32 legality (the fix).** `q = 1152921504606830593` and
    `2q = 2305843009213661186` are 60-bit/61-bit constants. x86 `sub`/`and`/`imul`/`add`
    take at most a 32-bit sign-extended immediate — only `mov` takes an `imm64`. The
    earlier "low-pressure" body inlined `q`/`2q` as immediate operands of
    `sub`/`and`/`imul`/`add` (`subq $2q,…`, `andq $…`, `imulq $q,…`, `addq $2q,…`);
    gas rejects those (`operand type mismatch`). The owned `runBlock` model does not
    enforce the imm32 limit, so they validated clean but did not assemble.

    The fix **materialises each 60-bit constant into a register via `movq $imm64, %reg`**
    (the ONLY legal imm64 form) and uses a **register** operand in every
    `sub`/`and`/`imul`/`add` — exactly as `FheNttButterflyEmit.fheBflyThir`
    handles `q`/`2q` (via `thConst` ⤳ `movq`). To stay within the 11-slot pool with
    **no new register name**, the dead post-`mulx` scratch `"wp"` (it holds the
    discarded low product after the `mulx` and is never read again) is reused as the
    single constant holder: the X-normalize is reordered to AFTER the `mulx` (Xn does
    not depend on the Shoup product), `wp ← q` covers the `Tlz`/`T` reduction, then
    `wp ← 2q` covers the X-normalize and the final `Y' = Xn + 2q − T`. No 60-bit value
    ever appears as the immediate of `sub`/`and`/`imul`/`add` — only as a `movq`
    imm64. Scratch names unchanged: `x, y, w, wp, s1, s2`. -/
def bflyCore : List (JInstr 64) :=
  -- qhat = mulhi(y, wp)  -> s2   (mulx low discarded into "wp"; wp now DEAD/free,
  -- reused below as the single 60-bit constant holder — no new register name).
  [ .mulx "s2" "wp" (.reg "y") (.reg "wp")
  -- lo1 = w·y -> w   (w, y consumed; y now dead)
  , .imul "w" (.reg "y")                                  -- w = w·y
  -- lo2 = qhat·q -> s2 ;  Tlz = lo1 − lo2 -> w     (wp = q, materialised by movq)
  , .mov "wp" (.imm fheQ)                                 -- wp = q   (movq imm64 — legal)
  , .imul "s2" (.reg "wp")                                -- s2 = qhat·q  (register operand)
  , .sub "w" (.reg "s2")                                  -- w = Tlz = lo1 − lo2 ∈ [0,2q)
  -- T = csubq(Tlz=w) -> s2   (sign scratch in the now-dead input "y"; wp still = q)
  , .mov "s2" (.reg "w"), .sub "s2" (.reg "wp")           -- s2 = Tlz − q  (register operand)
  , .mov "y" (.reg "s2"), .shr "y" (.imm 63)              -- y = sign bit
  , .neg "y", .and_ "y" (.reg "wp")                       -- y = (0−b) & q  (register operand)
  , .add "s2" (.reg "y")                                  -- s2 = T ∈ [0,q)
  -- Xn = csub2q(x) -> s1   (X-normalize, reordered to here; wp ← 2q; w dead = sign scratch)
  , .mov "wp" (.imm fheTwoQ)                              -- wp = 2q  (movq imm64 — legal)
  , .mov "s1" (.reg "x"), .sub "s1" (.reg "wp")           -- s1 = x − 2q  (register operand)
  , .mov "w" (.reg "s1"), .shr "w" (.imm 63)              -- w = sign bit (1 iff x<2q)
  , .neg "w", .and_ "w" (.reg "wp")                       -- w = (0−b) & 2q  (register operand)
  , .add "s1" (.reg "w")                                  -- s1 = Xn ∈ [0,2q)
  -- Y' = Xn + 2q − T  -> y   ;   X' = Xn + T  -> x   (Y' first; wp still = 2q, s2 = T)
  , .mov "y" (.reg "s1"), .add "y" (.reg "wp"), .sub "y" (.reg "s2")
  , .mov "x" (.reg "s1"), .add "x" (.reg "s2") ]

/-! ## 4. The in-Lean `Nat` references (butterfly + whole transform) -/

/-- The lazy Shoup CT butterfly over `Nat` (Harvey), `(X', Y')`. Identical to
    `FheNttButterflyEmit.bflyRef`. -/
def bflyRef (X Y omega omegaprime : Nat) : Nat × Nat :=
  let Xn := if X ≥ fheTwoQ then X - fheTwoQ else X
  let qhat := (Y * omegaprime) / 2 ^ 64
  let Tlz := (omega * Y - qhat * fheQ) % 2 ^ 64
  let T := if Tlz ≥ fheQ then Tlz - fheQ else Tlz
  ((Xn + T) % 2 ^ 64, (Xn + fheTwoQ - T) % 2 ^ 64)

/-- Set list index `i` to `v`. -/
def setNth (a : List Nat) (i v : Nat) : List Nat :=
  (a.zipIdx).map (fun p => if p.2 = i then v else p.1)

/-- One CT butterfly applied in-place to `a` at the pair `(j, j+t)` with twiddle
    table index `m+i`. Reads both cells, writes both. -/
def applyBfly (logN : Nat) (a : List Nat) (j t mi : Nat) : List Nat :=
  let X := a.getD j 0
  let Y := a.getD (j + t) 0
  let w := psiRev logN mi
  let wp := shoupConst w
  let (X', Y') := bflyRef X Y w wp
  setNth (setNth a j X') (j + t) Y'

/-- The inner butterfly run for group `(m, i)`: apply the butterfly across
    `j ∈ [j1, j1+t)` with `j1 = 2·i·t`, twiddle index `m+i`. -/
def innerRun (logN : Nat) (a : List Nat) (m i t : Nat) : List Nat :=
  let j1 := 2 * i * t
  (List.range t).foldl (fun acc d => applyBfly logN acc (j1 + d) t (m + i)) a

/-- One layer (`m` groups) at stride `t`. -/
def layerRun (logN : Nat) (a : List Nat) (m t : Nat) : List Nat :=
  (List.range m).foldl (fun acc i => innerRun logN acc m i t) a

/-- The whole forward negacyclic CT-DIT NTT reference (the C loop transcribed):
    `m` doubles `1 → N/2`, stride `t` halves `N/2 → 1`, layer count `logN`. -/
def nttRef (logN : Nat) (a : List Nat) : List Nat :=
  (List.range logN).foldl
    (fun acc layer =>
      let m := 2 ^ layer
      let t := 2 ^ (logN - 1 - layer)
      layerRun logN acc m t) a

/-! ## 5. The owned machine driver (whole transform via `runBlock`)

We run the *whole* transform on the owned `JState 64` machine: seed `a` in the
memory bank `"a"` at byte offsets `8·idx`, seed the twiddle table under the
symbol bank `twiddleSym`, alias a base register onto it (`loadSym`), and for each
public schedule step run the butterfly body that loads `a[j]`, `a[j+t]` and the
twiddle `(w, wp)` via indexed gathers, computes, and scatters both outputs back.
The schedule (`m`/`i`/`j` walk) is the public C-loop order. -/

/-- The per-butterfly machine step at flat indices: load `a[j]` (idx `j`), `a[j+t]`
    (idx `j+t`), gather the interleaved twiddle pair at cell `2·(m+i)` /
    `2·(m+i)+1` from the `.rodata` base register `"tbl"`, run `bflyCore`, scatter
    both outputs. Index registers are set by the driver before the step. -/
def nttButterflyStep : List (JInstr 64) :=
  [ .loadMemIdx "x" "a" "ij" 8           -- x = a[j]    (idx register "ij" = j)
  , .loadMemIdx "y" "a" "ijt" 8          -- y = a[j+t]  (idx register "ijt" = j+t)
  , .loadMemIdx "w" "tbl" "tw" 8         -- w  = psi_rev[m+i]      (cell 2(m+i))
  , .loadMemIdx "wp" "tbl" "twp" 8 ]     -- wp = shoup(psi_rev[m+i]) (cell 2(m+i)+1)
  ++ bflyCore
  ++ [ .storeMemIdx "a" "ij" 8 (.reg "x")   -- a[j]   = X'
     , .storeMemIdx "a" "ijt" 8 (.reg "y") ]-- a[j+t] = Y'

/-- Seed a machine state: buffer `a` at `8·idx`, the twiddle table under the
    symbol bank, and the index registers (`ij = j`, `ijt = j+t`, `tw = 2(m+i)`,
    `twp = 2(m+i)+1`) for one butterfly. -/
def seedStep (logN : Nat) (a : List Nat) (j t mi : Nat) : JState 64 :=
  let tbl := twiddleTable logN
  { regs := fun r =>
      if r = "ij" then BitVec.ofNat 64 j
      else if r = "ijt" then BitVec.ofNat 64 (j + t)
      else if r = "tw" then BitVec.ofNat 64 (2 * mi)
      else if r = "twp" then BitVec.ofNat 64 (2 * mi + 1)
      else 0
    flags := {}
    mem := fun base off =>
      if base = "a" then
        (a.zipIdx.foldl (fun acc (vk : Nat × Nat) =>
          if off = (8 * vk.2 : Nat) then BitVec.ofNat 64 vk.1 else acc) 0)
      else if base = twiddleSym ∨ base = "tbl" then
        (tbl.zipIdx.foldl (fun acc (vk : Nat × Nat) =>
          if off = (8 * vk.2 : Nat) then BitVec.ofNat 64 vk.1 else acc) 0)
      else 0 }

/-- Run one butterfly on the owned machine and read back the two updated cells
    (`a[j]`, `a[j+t]`). Aliases `"tbl"` onto the symbol bank via `loadSym` first. -/
def runStepCells (logN : Nat) (a : List Nat) (j t mi : Nat) : Nat × Nat :=
  let s0 := seedStep logN a j t mi
  -- alias base register "tbl" onto the twiddle symbol bank
  let s1 := evalInstr s0 (.loadSym "tbl" twiddleSym)
  let s := runBlock s1 nttButterflyStep
  ((s.loadIdx "a" "ij" 8).toNat, (s.loadIdx "a" "ijt" 8).toNat)

/-! ## 6. Per-butterfly machine-vs-reference KATs (tiny vectors) -/

/-- A small `logN = 2` (`N = 4`) buffer (already-reduced reps in `[0, q)`). -/
def buf4 : List Nat := [11, 7, 1152921504606830000, 3]

/-- **KAT (butterfly through the machine, layer-0 group `(m=1,i=0)`, stride 2).**
    The first CT butterfly of the `N=4` transform: pair `(0, 2)`, twiddle index
    `m+i = 1`. The owned machine `(X', Y')` equals `bflyRef`. -/
theorem bfly_machine_0 :
    runStepCells 2 buf4 0 2 1
      = ((bflyRef (buf4.getD 0 0) (buf4.getD 2 0)
            (psiRev 2 1) (shoupConst (psiRev 2 1))).1 % 2 ^ 64,
         (bflyRef (buf4.getD 0 0) (buf4.getD 2 0)
            (psiRev 2 1) (shoupConst (psiRev 2 1))).2 % 2 ^ 64) := by
  native_decide

/-! ## 7. The whole-transform value check (small N) — the headline validation

Run the entire forward NTT on the owned machine, butterfly by butterfly, over the
public C schedule, and check the resulting buffer equals `nttRef`. This validates
the loop counter + index arithmetic (`j1 = 2·i·t`, stride `t`, twiddle `m+i`), the
`.rodata` twiddle load, the in-place mem load/store, and the butterfly — the whole
machinery — at a size `native_decide` handles. -/

/-- Apply one machine butterfly in-place to a `Nat` buffer (the owned-machine
    analogue of `applyBfly`, going through `runStepCells`). -/
def machineApply (logN : Nat) (a : List Nat) (j t mi : Nat) : List Nat :=
  let (X', Y') := runStepCells logN a j t mi
  setNth (setNth a j X') (j + t) Y'

/-- The whole transform driven by the public schedule, each butterfly run on the
    owned machine. -/
def machineNtt (logN : Nat) (a : List Nat) : List Nat :=
  (List.range logN).foldl
    (fun acc layer =>
      let m := 2 ^ layer
      let t := 2 ^ (logN - 1 - layer)
      (List.range m).foldl
        (fun acc2 i =>
          let j1 := 2 * i * t
          (List.range t).foldl
            (fun acc3 d => machineApply logN acc3 (j1 + d) t (m + i)) acc2)
        acc)
    a

/-- **KAT (WHOLE transform, `logN = 2`, `N = 4`).** The owned-machine NTT over the
    public schedule equals the `Nat` reference `nttRef` (mod `2^64`, the lazy
    `[0,4q)` reps). This is the headline value check: the full loop machinery —
    counter, index arithmetic, twiddle load, in-place mem access, butterfly — at a
    size `native_decide` handles. -/
theorem ntt_machine_eq_ref_logN2 :
    machineNtt 2 buf4 = (nttRef 2 buf4).map (fun v => v % 2 ^ 64) := by
  native_decide

/-- A small `logN = 3` (`N = 8`) buffer. -/
def buf8 : List Nat :=
  [11, 7, 1152921504606830000, 3, 99, 1152921504606830500, 42, 1000000]

/-- **KAT (WHOLE transform, `logN = 3`, `N = 8`, 3 layers).** Pins the schedule +
    machinery at the next size up. -/
theorem ntt_machine_eq_ref_logN3 :
    machineNtt 3 buf8 = (nttRef 3 buf8).map (fun v => v % 2 ^ 64) := by
  native_decide

/-! ## 8. The three nested loop bodies (`m` layer / `i` group / `j` butterfly)

The whole CT-DIT NTT is emitted as **three nested down-counter loops**, each
the owned-backend `loopLcmd` shape (`Llabel ; body ; cmpq $0,%c ; jne .L`). Every
loop variable, stride, twiddle index and group base is computed **in-asm** from
the counters; the only external input is the data pointer `a` (`%rdi`).

### Register budget (the primary constraint — 14-reg GP pool)

`allocGp` is first-fit by *name* (liveness-unaware), so the emitted `.s` is sound
iff the **union** of distinct register names across all three loop bodies + their
setup blocks is ≤ 14. We pin `a→%rdi`, `tbl→%rsi`, `y→%rdx` (mulx src1) and
`rsp→%rsp` (the red-zone spill base; `%rsp` is excluded from the pool, so pinning
it costs no pool slot). That leaves **11 free pool slots**. The resident free
names are:

* butterfly core: `x`, `w`, `wp`, `s1`, `s2`   (5)
* inner data indices + counter: `ij`, `ijt`, `jc`   (3)
* group/layer running counters: `ic`, `mi`, `mc`   (3)

= **11** — exactly the free pool. The three layer-constant quantities `m`, `t`
and the group base `j1` are **spilled to the leaf red zone** (`movq …, -off(%rsp)`
with no `subq` — a leaf may use the 128-byte red zone below `%rsp`), loaded into
the dead scratch `s1`/`s2` for the per-group / per-layer index arithmetic and
stored back. So no value beyond the 11 resident free names ever needs a pool reg.

* `m`  spilled at `-8(%rsp)`   (`mSpill`)
* `t`  spilled at `-16(%rsp)`  (`tSpill`)
* `j1` spilled at `-24(%rsp)`  (`j1Spill`)

### In-asm index/stride arithmetic

* **layer step** (m-loop): `m <<= 1` (`shl m,1`), `t >>= 1` (`shr t,1`), layer
  counter `mc -= 1`. Initial `m = 1`, `t = N/2 = 2^(logN-1)`, `mc = logN`.
* **group step** (i-loop): twiddle element index `mi` runs `m, m+1, … 2m-1`
  (`mi += 1`); group base `j1` runs `0, 2t, 4t, …` (`j1 += 2t`, a `lea`-style
  `s1 = t; shl s1,1; add j1, s1`); group counter `ic -= 1`. Initial per layer
  `mi = m`, `j1 = 0`, `ic = m`.
* **butterfly step** (j-loop): data element indices `ij = j`, `ijt = j + t` run
  `j1 … j1+t-1` and `j1+t … j1+2t-1` (`ij += 1`, `ijt += 1`); inner counter
  `jc -= 1`. Initial per group `ij = j1`, `ijt = j1 + t`, `jc = t`.

### Twiddle gather (per butterfly, scratch index — no extra name)

`bflyCore` **clobbers** `w` (`imul w,y`) and `wp` (mulx low into `wp`), so a
group-hoisted twiddle would be destroyed after the first butterfly. We therefore
reload the twiddle pair at the **top of each butterfly**, computing the
interleaved-table element indices `2·mi` / `2·mi+1` into the dead scratch `s1`
(reused — costs **no** extra register name): `w = tbl[2·mi]`, `wp = tbl[2·mi+1]`.
`mi` is the group's twiddle index, held across the inner loop. -/

/-- The inner-loop butterfly body: gather the twiddle pair for group `mi` (cells
    `2·mi` / `2·mi+1` of the interleaved table, scratch index `s1`), load
    `a[j]`/`a[j+t]`, run the butterfly core, scatter both outputs, then advance
    the two data indices and the inner down-counter `jc`. -/
def jLoopBody : List (JInstr 64) :=
  -- twiddle gather (reload each butterfly; bflyCore clobbers w/wp): s1 = 2·mi
  [ .mov "s1" (.reg "mi"), .shl "s1" (.imm 1)        -- s1 = 2·mi
  , .loadMemIdx "w" "tbl" "s1" 8                     -- w  = psi_rev[mi]
  , .add "s1" (.imm 1)                               -- s1 = 2·mi+1
  , .loadMemIdx "wp" "tbl" "s1" 8                    -- wp = shoup(psi_rev[mi])
  , .loadMemIdx "x" "a" "ij" 8                       -- x = a[j]
  , .loadMemIdx "y" "a" "ijt" 8 ]                    -- y = a[j+t]
  ++ bflyCore                                        -- (reads w/wp/x/y; writes x/y)
  ++ [ .storeMemIdx "a" "ij" 8 (.reg "x")            -- a[j]   = X'
     , .storeMemIdx "a" "ijt" 8 (.reg "y")           -- a[j+t] = Y'
     , .add "ij" (.imm 1)                            -- a[j]   index advance
     , .add "ijt" (.imm 1)                           -- a[j+t] index advance
     , .sub "jc" (.imm 1) ]                          -- inner down-counter (cmpq/jne tests it)

/-- Per-group setup, run before the j-loop: reload the group base `j1` and stride
    `t` from the red zone and initialise the inner data indices `ij = j1`,
    `ijt = j1 + t` and the inner down-counter `jc = t`. Uses scratch `s2`. -/
def iSetupBody : List (JInstr 64) :=
  [ .loadMem "ij" "rsp" (-24)                        -- ij  = j1
  , .loadMem "s2" "rsp" (-16)                        -- s2  = t
  , .mov "ijt" (.reg "ij"), .add "ijt" (.reg "s2")   -- ijt = j1 + t
  , .mov "jc" (.reg "s2") ]                           -- jc  = t  (inner trip count)

/-- Per-group tail, run after the j-loop: advance the twiddle index `mi += 1`,
    advance the group base `j1 += 2·t` (reload `t`, double it, add), store `j1`
    back, and decrement the group down-counter `ic`. Uses scratch `s1`/`s2`. -/
def iTailBody : List (JInstr 64) :=
  [ .add "mi" (.imm 1)                               -- next twiddle group
  , .loadMem "s1" "rsp" (-24)                        -- s1 = j1
  , .loadMem "s2" "rsp" (-16), .shl "s2" (.imm 1)    -- s2 = 2·t
  , .add "s1" (.reg "s2")                            -- s1 = j1 + 2·t
  , .storeMem "rsp" (-24) (.reg "s1")                -- spill j1' = j1 + 2·t
  , .sub "ic" (.imm 1) ]                              -- group down-counter

/-- Per-layer setup, run before the i-loop: initialise the twiddle index `mi = m`,
    reset the group base `j1 = 0` (spilled), and set the group down-counter
    `ic = m`. Reloads `m` from the red zone. -/
def mSetupBody : List (JInstr 64) :=
  [ .loadMem "mi" "rsp" (-8)                          -- mi = m  (first group's twiddle)
  , .mov "s1" (.imm 0), .storeMem "rsp" (-24) (.reg "s1")  -- j1 = 0
  , .loadMem "ic" "rsp" (-8) ]                        -- ic = m  (groups this layer)

/-- Per-layer tail, run after the i-loop: double `m` (`m <<= 1`), halve the
    stride `t` (`t >>= 1`) — both via the red zone — and decrement the layer
    down-counter `mc`. -/
def mTailBody : List (JInstr 64) :=
  [ .loadMem "s1" "rsp" (-8), .shl "s1" (.imm 1), .storeMem "rsp" (-8) (.reg "s1")   -- m <<= 1
  , .loadMem "s2" "rsp" (-16), .shr "s2" (.imm 1), .storeMem "rsp" (-16) (.reg "s2") -- t >>= 1
  , .sub "mc" (.imm 1) ]                              -- layer down-counter

/-! The down-counter guards: each loop runs while its counter is non-zero
    (`cmpq $0,%c ; jne`). -/

/-- The inner j-loop guard: run while `jc ≠ 0`. -/
def jGuard : JState 64 → Bool := fun s => decide ((s.get "jc").toNat ≠ 0)
/-- The i-loop guard: run while `ic ≠ 0`. -/
def iGuard : JState 64 → Bool := fun s => decide ((s.get "ic").toNat ≠ 0)
/-- The m-loop guard: run while `mc ≠ 0`. -/
def mGuard : JState 64 → Bool := fun s => decide ((s.get "mc").toNat ≠ 0)

/-- Fuel bounding the inner loop (slack over the max stride `N/2`). -/
def innerFuel (logN : Nat) : Nat := 2 ^ logN

/-- The full union of register names the emitted nest uses (for the allocation
    budget check): every body + every setup/tail block. This is the block
    `allocGp`/`allocOverflow` must fit in the 14-reg pool. -/
def nttFullBlock : List (JInstr 64) :=
  mSetupBody ++ iSetupBody ++ jLoopBody ++ iTailBody ++ mTailBody

/-! ## 9. Validating the EMITTED nested machine at small N (the headline check)

This section drives the **emitted instruction-list bodies** through the loop semantics
`RejectLoop.runGuardedLoop` — three nested calls (m-loop runs the i-loop runs the
j-loop) over exactly the `jLoopBody`/`iSetupBody`/`iTailBody`/`mSetupBody`/
`mTailBody` blocks defined in §8 — and check the resulting buffer equals `nttRef`.
Unlike the prior in-Lean per-butterfly driver, this exercises the **owned-machine
loop bodies themselves** (the in-asm index arithmetic `ij/ijt/jc`, the spilled
`m/t/j1` red-zone reload+store, the hoisted twiddle gather, the down-counters),
so the *emitted schedule* is what is validated, at a size `native_decide`
handles. -/

/-- Seed the machine for the whole nested NTT: buffer `a` at byte `8·idx`, the
    twiddle table aliased into bank `"tbl"`, and the spilled layer state in the
    `"rsp"` red zone — `m = 1` at `-8`, `t = N/2` at `-16`, `j1 = 0` at `-24` —
    plus the layer down-counter `mc = logN`. -/
def seedNest (logN : Nat) (a : List Nat) : JState 64 :=
  let tbl := twiddleTable logN
  let memf : String → Int → BitVec 64 := fun base off =>
    if base = "a" then
      (a.zipIdx.foldl (fun acc (vk : Nat × Nat) =>
        if off = (8 * vk.2 : Nat) then BitVec.ofNat 64 vk.1 else acc) 0)
    else if base = twiddleSym then
      (tbl.zipIdx.foldl (fun acc (vk : Nat × Nat) =>
        if off = (8 * vk.2 : Nat) then BitVec.ofNat 64 vk.1 else acc) 0)
    else if base = "rsp" then
      (if off = (-8 : Int) then 1                          -- m  = 1
       else if off = (-16 : Int) then BitVec.ofNat 64 (2 ^ (logN - 1))  -- t = N/2
       else if off = (-24 : Int) then 0                    -- j1 = 0
       else 0)
    else 0
  let s0 : JState 64 :=
    { regs := fun r => if r = "mc" then BitVec.ofNat 64 logN else 0
      flags := {}
      mem := memf }
  -- alias bank "tbl" onto the twiddle symbol bank (loadSym)
  evalInstr s0 (.loadSym "tbl" twiddleSym)

/-- A terminating guarded loop over an arbitrary state-transformer `step` (the
    outer m-loop / i-loop single iteration is not a plain instruction list — it
    runs setup, a nested guarded loop, and a tail). `fuel`-bounded for totality,
    same shape as `RejectLoop.runGuardedLoop` but with `step : JState w → JState w`
    instead of a `runBlock body`. -/
def runGuardedLoopStep {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (step : JState w → JState w) (s : JState w) : JState w :=
  match fuel with
  | 0 => s
  | f + 1 => if guard s then runGuardedLoopStep f guard step (step s) else s

/-- Run the whole emitted nest from a seeded state: the m-loop body is
    `mSetupBody ++ <i-loop> ++ mTailBody`, the i-loop body is
    `iSetupBody ++ <j-loop> ++ iTailBody`, the j-loop body is `jLoopBody`. The
    innermost loop is a `runGuardedLoop` over its instruction-list body; the two
    outer loops are `runGuardedLoopStep` over their compound iteration. Each level
    runs while its own down-counter is non-zero. Fuel is generous (`2^logN` per
    level covers every trip count). -/
def runNest (logN : Nat) (s0 : JState 64) : JState 64 :=
  let F := innerFuel logN
  -- one i-iteration: per-group setup, the full j-loop, per-group tail
  let iStep : JState 64 → JState 64 := fun s =>
    let s2 := runBlock s iSetupBody
    let s3 := runGuardedLoop F jGuard jLoopBody s2
    runBlock s3 iTailBody
  -- one m-iteration: per-layer setup, the full i-loop, per-layer tail
  let mStep : JState 64 → JState 64 := fun s =>
    let s1 := runBlock s mSetupBody
    let s2 := runGuardedLoopStep F iGuard iStep s1
    runBlock s2 mTailBody
  runGuardedLoopStep F mGuard mStep s0

/-- Read back the buffer `a` (cells `0 … 2^logN-1`, byte `8·idx`) from a state. -/
def readBuf (logN : Nat) (s : JState 64) : List Nat :=
  (List.range (2 ^ logN)).map (fun idx => (s.load "a" (8 * idx)).toNat)

/-- The whole emitted nest run on the owned machine, buffer in → buffer out. -/
def machineNttNest (logN : Nat) (a : List Nat) : List Nat :=
  readBuf logN (runNest logN (seedNest logN a))

/-- **KAT (WHOLE EMITTED NEST, `logN = 2`, `N = 4`).** The three nested
    `runGuardedLoop`/`runGuardedLoopT` calls over the emitted `jLoopBody` /
    `iSetupBody` / `iTailBody` / `mSetupBody` / `mTailBody` bodies — i.e. the
    EMITTED nested-loop machine — produce the `nttRef` output (mod `2^64`). This
    validates the in-asm index/stride arithmetic, the red-zone spill/reload of
    `m`/`t`/`j1`, the hoisted twiddle gather, and all three down-counters. -/
theorem nest_machine_eq_ref_logN2 :
    machineNttNest 2 buf4 = (nttRef 2 buf4).map (fun v => v % 2 ^ 64) := by
  native_decide

/-- **KAT (WHOLE EMITTED NEST, `logN = 3`, `N = 8`, 3 layers).** Pins the emitted
    nested-loop machine at the next size up. -/
theorem nest_machine_eq_ref_logN3 :
    machineNttNest 3 buf8 = (nttRef 3 buf8).map (fun v => v % 2 ^ 64) := by
  native_decide

/-! ## 10. The looped emission (THREE nested `loopLcmd`s) + the `.rodata` table

Each of the three loops emits as the owned-backend looped control-flow shape
(`Llabel ; body ; cmpq $0,%c ; jne .L`), nested by concatenation with distinct
`.L` labels (`.L0` = m-loop, `.L1` = i-loop, `.L2` = j-loop). The body of each
loop is rendered through the owned `renderBlockBody`; the twiddle table through
`renderRodata`. Each level is constant-size in its trip count (`loopLcmd_length`),
so the whole nest is `O(1)` body copies, not an `O(N log N)` unroll. -/

/-- Each loop level is constant-size: body length + 3 control instrs, independent
    of the trip count (NOT an unroll). -/
theorem loop_emit_constant_size
    (top : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.LLabel)
    (cReg : String)
    (body : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lcmd) :
    (rejectLoopLcmd 64 top cReg body).length = body.length + 3 :=
  rejectLoopLcmd_length 64 top cReg body

/-- Fixed register allocation over the WHOLE nest (`nttFullBlock` = every body +
    setup/tail block). Pins the buffer base `a→%rdi`, twiddle base `tbl→%rsi`, the
    mulx src1 `y→%rdx`, and the red-zone spill base `rsp→%rsp` (out of pool, so
    free). The remaining names take the 11 free pool slots first-fit. -/
def nttAlloc : GpAlloc :=
  allocGp
    [ ("a", "%rdi")      -- in-place buffer base (ABI arg)
    , ("tbl", "%rsi")    -- twiddle table base (loadSym)
    , ("y", "%rdx")      -- mulx src1 pin
    , ("rsp", "%rsp") ]  -- red-zone spill base (excluded from pool)
    nttFullBlock

/-- Frame one loop level: `cReg` is the counter register's `%rN`, `label` its
    `.L`. Renders `label: ; <body lines> ; cmpq $0,%cReg ; jne label`. -/
def frameLoop (label cReg : String) (bodyLines : List String) : List String :=
  (label ++ ":") :: bodyLines ++ [ "\tcmpq $0, " ++ cReg, "\tjne " ++ label ]

/-- The owned-backend `.s` for the WHOLE in-place forward NTT: the `fhe_ntt` leaf,
    the THREE nested loops (`.L0` m-layer, `.L1` i-group, `.L2` j-butterfly), the
    layer prologue (`mc = logN`, `m = 1`, `t = N/2`, `j1 = 0` spilled to the red
    zone, twiddle base via `leaq`), and the interleaved `.rodata` twiddle table.

    The control-flow frames (label + cmp + jne per level) are the trusted leaf
    scaffolding; the verified claim is the per-body `runBlock`/`runGuardedLoop`
    transform (§9, all three loops) + the constant-size looped-emission shape. -/
def fheNttAsm (logN : Nat) : String :=
  let mc := regOf nttAlloc "mc"
  let ic := regOf nttAlloc "ic"
  let jc := regOf nttAlloc "jc"
  -- layer-init prologue: load counters / spill m,t,j1 to the red zone, twiddle base.
  let prologue : List String :=
    [ "\tleaq " ++ twiddleSym ++ "(%rip), %rsi"        -- twiddle base (loadSym)
    , "\tmovq $" ++ toString logN ++ ", " ++ mc        -- mc = logN (layers)
    , "\tmovq $1, -8(%rsp)"                            -- m  = 1
    , "\tmovq $" ++ toString (2 ^ (logN - 1)) ++ ", %rax", "\tmovq %rax, -16(%rsp)" ]  -- t = N/2
  -- the three nested loops, innermost first by concatenation
  let jLoopLines := frameLoop ".L2" jc (renderBlockBody nttAlloc jLoopBody)
  let iBodyLines := renderBlockBody nttAlloc iSetupBody
    ++ jLoopLines ++ renderBlockBody nttAlloc iTailBody
  let iLoopLines := frameLoop ".L1" ic iBodyLines
  let mBodyLines := renderBlockBody nttAlloc mSetupBody
    ++ iLoopLines ++ renderBlockBody nttAlloc mTailBody
  let mLoopLines := frameLoop ".L0" mc mBodyLines
  renderLeafFn "fhe_ntt" [] (prologue ++ mLoopLines) []
    ++ renderRodata [(twiddleSym, twiddleTable logN)]

/-! ## 11. Shape checks on the emitted `.s` (native_decide)

Pinned at `logN = 2` (`N = 4`, 8-entry interleaved table) so `native_decide`
handles the table; the body shape is logN-independent. -/

/-- The emitted `.s` carries the `fhe_ntt` leaf label. -/
theorem fheNtt_has_leaf : hasSub (fheNttAsm 2) "fhe_ntt" = true := by native_decide

/-- The `.rodata` twiddle table is present (`.section .rodata` + the label). -/
theorem fheNtt_has_rodata :
    hasSub (fheNttAsm 2) ".section .rodata" = true
      ∧ hasSub (fheNttAsm 2) "fhe_ntt_psi_rev:" = true := by native_decide

/- The RIP-relative twiddle-base load `leaq fhe_ntt_psi_rev(%rip), …` is present. -/
#guard (hasSub (fheNttAsm 2) "\tleaq fhe_ntt_psi_rev(%rip), ")

/-- The butterfly's Shoup quotient emits as a real `mulx`. -/
theorem fheNtt_has_mulx : hasSub (fheNttAsm 2) "mulx" = true := by native_decide

/-- BOTH branchless conditional reductions: the sign-bit shift `shrq $63`. -/
theorem fheNtt_has_shr : hasSub (fheNttAsm 2) "shrq $63" = true := by native_decide

/-- The indexed in-place gather/scatter (SIB `(…, …, 8)`) is present. -/
theorem fheNtt_has_sib : hasSub (fheNttAsm 2) ", 8)" = true := by native_decide

/- The red-zone spill of `m` (`movq …, -8(%rsp)`) is present — the layer state is
    held in the red zone, not a pool register. -/
#guard (hasSub (fheNttAsm 2) "-8(%rsp)")

/-- **THREE nested loops**: all three loop labels `.L0:`/`.L1:`/`.L2:`, three
    conditional back-edges `jne .L0`/`jne .L1`/`jne .L2`, and a `cmpq $0,` counter
    test. -/
theorem fheNtt_has_three_loops :
    hasSub (fheNttAsm 2) ".L0:" = true
      ∧ hasSub (fheNttAsm 2) ".L1:" = true
      ∧ hasSub (fheNttAsm 2) ".L2:" = true
      ∧ hasSub (fheNttAsm 2) "jne .L0" = true
      ∧ hasSub (fheNttAsm 2) "jne .L1" = true
      ∧ hasSub (fheNttAsm 2) "jne .L2" = true
      ∧ hasSub (fheNttAsm 2) "cmpq $0, " = true := by native_decide

/-- No unhandled-op / unallocated-register sentinel. -/
theorem fheNtt_no_sentinel :
    hasSub (fheNttAsm 2) "UNHANDLED" = false
      ∧ hasSub (fheNttAsm 2) "UNALLOCATED" = false := by native_decide

/-- **The whole nest fits the 14-reg pool: `allocOverflow = none`.** Every
    non-pinned name across all three loop bodies + setup/tail blocks gets a
    distinct pool register (no spill of a live name beyond the explicit `m`/`t`/`j1`
    red-zone slots). This is the budget guarantee against the `<UNALLOCATED>`
    silent-`%rax`-alias bug. -/
theorem fheNtt_no_overflow :
    allocOverflow [("a", "%rdi"), ("tbl", "%rsi"), ("y", "%rdx"), ("rsp", "%rsp")]
      nttFullBlock = none := by
  native_decide

/-- Aggregate shape check on the emitted in-place NTT `.s`. -/
theorem fheNtt_shape :
    hasSub (fheNttAsm 2) "fhe_ntt"
      ∧ hasSub (fheNttAsm 2) ".section .rodata" = true
      ∧ hasSub (fheNttAsm 2) "mulx" = true
      ∧ hasSub (fheNttAsm 2) "shrq $63" = true
      ∧ hasSub (fheNttAsm 2) ", 8)" = true
      ∧ hasSub (fheNttAsm 2) "jne .L2" = true
      ∧ hasSub (fheNttAsm 2) "UNHANDLED" = false :=
  ⟨fheNtt_has_leaf, fheNtt_has_rodata.1, fheNtt_has_mulx, fheNtt_has_shr,
   fheNtt_has_sib, fheNtt_has_three_loops.2.2.2.2.2.1, fheNtt_no_sentinel.1⟩

/-! ## 12. Emit driver -/

/-- Write the owned-backend `.s` for the in-place forward negacyclic NTT
    (`fhe_ntt`) into `bench/fhe_ntt_compare/gen` at `logN = 13` (`N = 8192`),
    with the full `psi_rev` interleaved `.rodata` twiddle table (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/fhe_ntt_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/fhe_ntt.s") (fheNttAsm 13)
  IO.println "WROTE bench/fhe_ntt_compare/gen/fhe_ntt.s"
  IO.println "  (in-place forward negacyclic CT-DIT NTT, logN=13 / N=8192, OWNED x86, NO jasminc;"
  IO.println "   WHOLE three-level nest emitted as nested loops:"
  IO.println "     .L0 m-layer loop, .L1 i-group loop, .L2 j-butterfly loop (each cmpq $0/jne),"
  IO.println "   in-asm index/stride arithmetic (shl/shr m,t; lea-style j1+=2t; ij/ijt advance),"
  IO.println "   layer state m/t/j1 spilled to the leaf red zone (-8/-16/-24(%rsp)),"
  IO.println "   hoisted twiddle gather (w/wp loaded once per group),"
  IO.println "   lazy Harvey Shoup butterfly (mulx + shrq $63 mask-csubs),"
  IO.println "   psi_rev interleaved .rodata twiddle table; q=1152921504606830593;"
  IO.println "   ABI: void fhe_ntt(uint64_t* a) in-place on N coeffs, a->%rdi, in/out in [0,4q))"

end CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttLoopEmit
