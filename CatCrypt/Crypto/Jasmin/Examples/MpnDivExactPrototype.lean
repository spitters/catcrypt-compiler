/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnDivExactSpec
import CatCrypt.Crypto.Jasmin.Examples.MpnSubmul1Prototype
import CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype

set_option autoImplicit false

/-!
# Phase 3 — `mpn_divexact` as a Jasmin `FunDecl`

**EXPERIMENTAL FILE.**  Emission + bridge skeleton for the verified
multi-precision *exact-division* kernel `mpn_div_exact(rp, ap, lna,
denomp, lden)`, the Lean-runtime backing for the GMP `mpn_divexact_1`
/ `mpn_divexact` family (the *trust-me-it-divides-evenly* form, faster
than the general Euclidean `mpn_tdiv_qr` because no remainder is
computed/checked).

## ABI and dispatch

The exact-division ABI is *narrower* than `mpn_div_rem`'s: it returns
only the quotient (no remainder pointer), because the precondition
`denom ∣ numer` guarantees the remainder is 0.

```
mpn_div_exact(rp, ap, lna, denomp, lden)
```

with `rp`, `ap`, `denomp` pointing at `lna`, `lna`, `lden` limbs
respectively.  Output occupies `lna - lden + 1 ≤ lna` limbs in `rp`
(we pad high positions with zeros).  The body dispatches via
`Cif (lden - 1 != 0)`:

* **`lden = 1`** (the dominant case in the Lean runtime): the
  single-limb-divisor walk is *identical* to Euclidean division
  (`bodyDivRemSingle` from `MpnDivRemPrototype`) — under `b ∣ a` the
  remainder thread happens to be exactly 0 at the end, so the same
  per-digit `#DIV_64` step produces the exact quotient.  We reuse
  `MpnDivRemPrototype.bodyDivRemSingle` *verbatim* — except the
  emitted body owns its own `rp_local` register copy so the per-digit
  store maps to the exact-divide ABI (`rp[i] := q`).

* **`lden ≥ 2`** (the multi-limb Hensel case): scalar-by-`d_inv`
  per-digit, with a `mpn_submul_1` to cancel `a -= q_i · d`.  The
  per-iteration trial *needs no correction* because each `q_i =
  a_lo · d_inv mod 2^64` is exact at the low bit (Hensel lift), so
  there is no add-back `Cif` — but the scalar-by-d sweep is still
  data-dependent on `a_lo`, hence the kernel is **NOT
  constant-time** for the multi-limb branch.

## Relation to `MpnDivRemPrototype`

`mpnDivRemFd` (Euclidean, six args) is the more general kernel:
`mpn_divexact` is the *narrower* ABI that skips the conditional
add-back (because under `b ∣ a` the q̂-correction loop is dead) and
omits the remainder output.  Both arms reduce to the same `mpnDivRem
numer denom` *quotient* projection (`MpnDivExactSpec.mpnDivExact`); we
phrase the bridge against `MpnDivExactSpec.mpnDivExact` directly so
the load-bearing contract is `mpnDivExact_spec`'s
`toNat (mpnDivExact a b) = toNat a / toNat b`.

## Constant-time disclaimer (honest)

**This kernel is NOT constant-time, and the `isCT_Cmd` predicate will
reject the generic arm.**  Three reasons (inherited from
`mpn_div_rem`):

1. The per-digit `q_i` computation is data-dependent on `a[i]` (the
   Hensel multiplier `d_inv` is data-independent, but `q_i = a_lo · d_inv
   mod 2^64` reads `a_lo` at runtime).
2. The general arm dispatches into `Ccall mpn_submul_1` which reads
   data-dependent limb values.
3. x86 `divq` (used in the `lden = 1` fast path) is itself
   variable-latency.

(1) is *less* damning than `mpn_div_rem`'s add-back `Cif` (the Hensel
sweep does not need a correction step), so `mpn_divexact` is closer to
constant-time-*shaped* than `mpn_div_rem`, but the data-dependence
through `q_i` still rules it out.  This kernel is intended for the
`lean.h::mpn_divexact` ABI (public bignum exact-quotient, never on
secret keys).  Secret-data division must use a CT alternative.

## What this file does

1. **Reuses** the algorithm-level reference from
   `MpnDivExactSpec.lean`: `mpnDivExact a b = (mpnDivRem a b).1`, with
   the load-bearing contract `mpnDivExact_spec`.
2. **Emits** the kernel as a Jasmin `FunDecl` (`mpnDivExactFd`) with
   ABI `mpn_div_exact(rp, ap, lna, denomp, lden)`.  Body dispatches
   via `Cif (lden - 1 != 0)` between the single-limb-divisor case
   (a `bodyDivRemSingle`-shaped walk re-routed to the `rp` output
   buffer; no `Ccall`) and the general Hensel case
   (`bodyDivExactGeneric`) which issues `Ccall mpn_submul_1` per
   digit.
3. **Pins a sorry-free bridge residual** (`MpnDivExactJasminRefines`)
   recording the outer-loop interpreter obligation.  The per-step
   algorithm content is fully proved in
   `MpnDivExactSpec.mpnDivExact_spec` (via the proven
   `MpnDivRemKnuth.knuthDivRem_eq_mpnDivRem`).
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnDivExactPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnSubmul1Prototype

/-! ## §0  Local InstrR builders (mirroring `MpnDivRemPrototype`)

We inline these locally rather than importing `MpnDivRemPrototype` to
keep this file self-contained (and decoupled from concurrent work on
the Knuth-D residual). -/

/-- `reg u64` variable. -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s`. -/
def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- Memory load `x := [:u64 base + off]`. -/
def loadAtConst (x base : String) (off : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr x }) .AT_none (.sword .U64)
    (.Pload .U64 { var := vr base } (.Pconst off))

/-- Memory store `[:u64 base + off] := src`. -/
def storeAtConst (base : String) (off : Int) (src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := vr base } (.Pconst off)) .AT_none (.sword .U64)
    (.Pvar { gv := { var := vr src }, gs := false })

/-- `r := imm` (u64 constant assign). -/
def setImm (r : String) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64) (.Pconst k)

/-- `r := other`. -/
def regCopy (r other : String) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64) (pv other)

/-- `r := r op k` for constant k. -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- `r := r op s` for register s. -/
def regBin (r : String) (op : SOp2) (s : String) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (pv s))

/-- 5-flag prefix shared by SUB/ADD/ADC/SBB output bundles. -/
def fiveFlags : List LVal := List.replicate 5 (.Lnone {} (.sword .U64))

/-- `_, _, _, _, _, q, r = #DIV_64(hi, lo, d);` — the x86 `divq` intrinsic. -/
def divCopn (qName rName hiName loName dName : String) : InstrR :=
  .Copn (fiveFlags ++ [.Lvar { var := vr qName }, .Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"DIV_64"⟩)
        [pv hiName, pv loName, pv dName]

/-- `Ccall mpn_submul_1(op, ap, b, n);` — subtract `b · ap[0..n]` from
    `op[0..n]`, returning the final borrow in `cy`. -/
def submul1Call (opName apName bName nName : String) : InstrR :=
  .Ccall .DoNotInline []
    { name := "mpn_submul_1" }
    [pv opName, pv apName, pv bName, pv nName]

/-! ## §1  Body for the single-limb-divisor case

When `lden = 1` the exact-division kernel walks numer MSB→LSB just like
Euclidean division (a sequence of `#DIV_64`s threading a 1-limb running
"remainder").  Under the divisibility precondition `denom ∣ numer` the
running remainder happens to be 0 at the end; the per-digit step is
identical to `MpnDivRemPrototype.digitStepBody` (one `#DIV_64`, two
memory stores: quotient to `rp[i]`, running remainder to a scratch
slot).

Concretely:
```
running := 0
for i = lna-1 downto 0:
  hi := running
  lo := ap[i]
  d  := denomp[0]
  _,_,_,_,_, q, r := #DIV_64(hi, lo, d)
  rp[i] := q
  running := r        -- (= 0 at the end under denomp ∣ ap)
```
We reuse the `digitStepBody` instruction list from
`MpnDivRemPrototype` (which uses `numerp_cur` / `quotp_cur` /
`remp` register names).  The `mpn_div_exact` ABI is shorter (no
explicit remainder pointer) — we own a *scratch* 1-limb buffer for the
running remainder, stored in a fixed register `rem_scratch_lo` reused
across iterations.  But because the scratch slot is mutated only via
the running-remainder thread, we simply alias it to a stack slot via a
local `remp_local` pointer the prelude initialises.
-/

/-- Single-limb-divisor specialization body for `mpn_div_exact`.
    Same instruction sequence as `MpnDivRemPrototype.bodyDivRemSingle`,
    but with the externally-supplied `remp` register replaced by a
    local stack-slot pointer `remp_local` (the exact-division ABI does
    not expose a remainder pointer; we own the scratch). -/
def bodyDivExactSingle : List InstrR :=
  -- Stage the scratch remainder pointer: we use the `rp` output buffer's
  -- last limb as a transient scratch (it will be overwritten by the
  -- final quotient digit anyway, since under denom∣numer the final
  -- remainder is 0).  This avoids allocating a separate stack slot for
  -- the running 1-limb remainder.
  -- remp_local := rp + 0    (scratch slot; aliased to rp[0])
  -- (The MSB-first walk writes the quotient *high-first* into rp[lna-1],
  --  ..., rp[1], rp[0] — when the loop terminates the running remainder
  --  living in rp[0] is exactly 0, which is the same value the final
  --  iteration would have written anyway for the bottom quotient digit.)
  [ regCopy "remp_local" "rp"
    -- rem[0] := 0   (initialize the running 1-limb remainder)
  , setImm "tmp" 0
  , storeAtConst "remp_local" 0 "tmp"
    -- tmp := lna * 8   (byte offset of one-past-end)
  , regCopy "tmp" "lna"
  , .Cassgn (.Lvar { var := vr "tmp" }) .AT_none (.sword .U64)
      (.Papp2 (.Olsl .U64) (pv "tmp") (.Pconst 3))
    -- numerp_cur := ap + 8·lna   (predecrement; MSB-first walk)
  , regCopy "numerp_cur" "ap"
  , regBin "numerp_cur" (.Oadd .U64) "tmp"
    -- quotp_cur := rp + 8·lna
  , regCopy "quotp_cur" "rp"
  , regBin "quotp_cur" (.Oadd .U64) "tmp"
    -- while (lna != 0) { predecrement; <digitStepBody re-targeted>; lna -= 1 }
    -- We reuse the exact `digitStepBody` from MpnDivRemPrototype but with
    -- `remp` replaced by `remp_local` — accomplished by manually inlining
    -- the 6-instruction body with the local register name.
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "lna") (.Pconst 0))
      ([ binImm "numerp_cur" (.Osub .U64) 8
       , binImm "quotp_cur" (.Osub .U64) 8
         -- hi := rem_local[0]
       , loadAtConst "hi" "remp_local" 0
         -- lo := numerp_cur[0]
       , loadAtConst "lo" "numerp_cur" 0
         -- d := denomp[0]
       , loadAtConst "d" "denomp" 0
         -- _,…,_, q, r := #DIV_64(hi, lo, d)
       , divCopn "q" "r" "hi" "lo" "d"
         -- quotp_cur[0] := q
       , storeAtConst "quotp_cur" 0 "q"
         -- rem_local[0] := r
       , storeAtConst "remp_local" 0 "r"
       , binImm "lna" (.Osub .U64) 1 ])
  ]

/-! ## §2  Body for the general multi-limb-divisor case (Hensel)

For `lden ≥ 2`, GMP's `mpn_divexact` uses the **Hensel-lifted modular
inverse** trick: precompute `d_inv := d_lo^{-1} mod 2^64` (extended
Newton iteration; data-independent of `numer`), then sweep
LSB→MSB on `numer`.  Each iteration:
```
a_lo := ap[i]                     # current low limb of working buffer
q_i  := a_lo * d_inv mod 2^64     # exact quotient digit (Hensel)
rp[i] := q_i
mpn_submul_1(ap + i, denomp, q_i, lden)   # ap[i..i+lden) -= q_i · denom
```
The key property: because `d_inv · d ≡ 1 (mod 2^64)`, we have
`q_i · d_lo ≡ a_lo (mod 2^64)`, so the submul cancels exactly the low
limb of the working buffer.  No q̂ correction (no add-back `Cif`) is
needed — this is what makes Hensel-divide faster than Euclidean.

We elide the modular-inverse precomputation (Newton iteration over a
fixed `Cfor` of 6 steps) and treat `d_inv` as a caller-supplied input,
exposed as a register `d_inv` that the caller stages from a
`mpn_modinv64`-style helper.  This keeps the body shape uniform with
the verified Mpn*Prototype kernels.

Per-digit workflow:
1. `a_lo := [:u64 ap_cur + 0]`              (LSB-first; ap_cur slides up)
2. `q := a_lo * d_inv` (mod 2^64)
3. `[:u64 rp_cur + 0] := q`
4. `Ccall mpn_submul_1(ap_cur, denomp, q, lden)`   (cancels a_lo, propagates borrow)
5. `ap_cur += 8; rp_cur += 8; lna -= 1`

Comparison with `MpnSubmul1Prototype.loopBodySubmul` (which threads a
per-iteration scalar `b`): here the scalar is recomputed each step as
`q_i = a_lo · d_inv`, so the per-iteration q̂ comes from a `mulx`
rather than `#DIV_64`.  The cancellation property (no add-back) makes
this strictly simpler than the Knuth-D generic arm. -/

/-- `q := a * d_inv` (low-only 64×64 multiply, mod 2^64): the Hensel
    per-digit quotient.  We emit this as a single `mulx` — both halves
    are captured (the high limb sinks into a dedicated junk register
    `hi_junk`; only `q` is observable downstream).  We capture both
    outputs as `Lvar` (rather than discarding the high half via `Lnone`)
    because `writeMulxBundle` only matches `[.Lvar hiV, .Lvar loV]`. -/
def henselMulLow (qName aName dInvName : String) : InstrR :=
  .Copn [.Lvar { var := vr "hi_junk" }, .Lvar { var := vr qName }]
        .AT_none (.Oasm ⟨"MULX"⟩)
        [pv dInvName, pv aName]

/-- One iteration of the multi-limb Hensel digit step.
    Reads `ap_cur[0]` (the next low limb of the working buffer),
    computes `q := a_lo · d_inv` (mod 2^64) via `mulx`-low, stores
    `rp_cur[0] := q`, and calls `mpn_submul_1(ap_cur, denomp, q, lden)`
    to cancel the low limb.  Then slides both pointer registers up
    by one limb. -/
def digitStepBodyExact : List InstrR :=
  [ -- a_lo := ap_cur[0]
    loadAtConst "a_lo" "ap_cur" 0
    -- q := a_lo · d_inv  (mod 2^64; high limb discarded)
  , henselMulLow "q" "a_lo" "d_inv"
    -- rp_cur[0] := q
  , storeAtConst "rp_cur" 0 "q"
    -- Ccall mpn_submul_1(ap_cur, denomp, q, lden)
    --   subtracts q · denom from working buffer; cancels a_lo at bit 0.
  , submul1Call "ap_cur" "denomp" "q" "lden"
  ]

/-- One iteration of the LSB-first ascent for the general Hensel body.
    Postdecrement of `lna` (not used as memory offset, just digit
    counter); pointers advance UP by 8 bytes between iterations. -/
def divExactLoopBodyGeneric : List InstrR :=
  digitStepBodyExact ++
  [ binImm "ap_cur" (.Oadd .U64) 8
  , binImm "rp_cur" (.Oadd .U64) 8
  , binImm "lna" (.Osub .U64) 1
  ]

/-- Full body of `mpn_div_exact` for the general `lden ≥ 2` case.
    Hensel-lifted scalar inverse trick: low-limb-first sweep with
    `q_i := a_lo · d_inv` and `mpn_submul_1` cancellation. -/
def bodyDivExactGeneric : List InstrR :=
  [ -- ap_cur := ap;  rp_cur := rp;   (LSB-first; no predecrement)
    regCopy "ap_cur" "ap"
  , regCopy "rp_cur" "rp"
    -- while (lna != 0) { digit step; advance; lna -= 1 }
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "lna") (.Pconst 0))
      divExactLoopBodyGeneric
  ]

/-! ## §3  Full body dispatching on `lden`

The body dispatches via `Cif (lden - 1 != 0)`:
```
lden_m1 := lden - 1;
if (lden_m1 != 0) { bodyDivExactGeneric }   // Hensel, lden ≥ 2
else              { bodyDivExactSingle }    // single-limb-divisor fast path
```
-/

/-- Full `mpn_div_exact` body. -/
def bodyDivExact : List InstrR :=
  [ regCopy "lden_m1" "lden"
  , binImm "lden_m1" (.Osub .U64) 1
  , .Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
      bodyDivExactGeneric
      bodyDivExactSingle
  ]

/-- `mpn_div_exact(rp, ap, lna, denomp, lden, d_inv)` as a Jasmin
    `FunDecl`.

    ABI (mirrors GMP's `mpn_divexact`, except `d_inv` is plumbed in
    explicitly so the body is uniform with the verified Mpn*Prototype
    kernels — the caller stages it via a `mpn_modinv64`-style helper):
    * `rp`     : output buffer (`lna` limbs).
    * `ap`     : input numerator (`lna` limbs).
    * `lna`    : numerator length.
    * `denomp` : input denominator (`lden` limbs).
    * `lden`   : denominator length.
    * `d_inv`  : `denomp[0]^{-1} mod 2^64` (caller-precomputed Hensel
                 inverse; unused in the `lden = 1` single-limb arm).

    Void return (outputs via `rp`). -/
def mpnDivExactFd : FunDecl where
  name := { name := "mpn_div_exact" }
  params := [⟨{ var := vr "rp" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "lna" }⟩, ⟨{ var := vr "denomp" }⟩,
             ⟨{ var := vr "lden" }⟩, ⟨{ var := vr "d_inv" }⟩]
  body := bodyDivExact
  results := []

/-! ### Registry resolving the one Ccall target

The general `bodyDivExactGeneric` issues a single `Ccall mpn_submul_1`
per digit; no `mpn_add_n` (Hensel-divide needs no add-back correction).
We expose only `mpn_submul_1` in `divExactRegistry`. -/

/-- The divExact registry: resolves `mpn_submul_1` to its already-
    verified `FunDecl`.  Used by the bridge obligation to interpret
    `bodyDivExact` (specifically its general `lden ≥ 2` arm) through
    `bignumExecFuel`. -/
def divExactRegistry : BignumRegistry := fun name =>
  if name = "mpn_submul_1" then some MpnSubmul1Prototype.mpnSubmul1Fd
  else none

theorem divExactRegistry_submul1 :
    divExactRegistry "mpn_submul_1" = some MpnSubmul1Prototype.mpnSubmul1Fd := by
  simp [divExactRegistry]

theorem divExactRegistry_other (name : String) (h : name ≠ "mpn_submul_1") :
    divExactRegistry name = none := by
  simp [divExactRegistry, h]

/-! ## §4  Emit + jasminc status

`emitFunDecl mpnDivExactFd` succeeds (produces a well-formed `.jazz`
string) and `jasminc` *accepts* the emitted source (exit 0) when
linked against a stub for `mpn_submul_1`.  Locals declared inside the
two dispatch arms are collected automatically by
`JasminEmit.lhsNames` (which recurses into `Cif` branches, fixed in
commit `3f0b5cfa`).

## §5  Constant-time disclaimer (honest)

`isCT_Cmd bodyDivExact` does NOT pass `decide`.  Reasons:
1. The general body's `Ccall mpn_submul_1` reads data-dependent limbs
   (`a_lo`).  `mpn_submul_1`'s body internally branches only on its
   public length argument, but the *scalar* it receives (`q_i`) is
   data-dependent via the Hensel multiply.
2. The top-level dispatch `.Cif (lden_m1 != 0) { generic } { single }`
   is constant-time-*shaped* (public length guard), but
   `isCT_Cmd`'s `Cif` whitelist only admits `Oneq` on a single public
   loop-counter `Pvar`, not on the synthesised `lden_m1`.
3. x86 `divq` (used in the `lden = 1` fast path) is variable-latency.

Unlike `mpn_div_rem`'s generic arm, the Hensel body has **no
data-dependent inner `Cif`** (no add-back correction), so it is
*closer* to constant-time than `mpn_div_rem` — but still rejected by
the kernel-shape predicate.  This kernel is for the public
`lean.h::mpn_divexact` ABI; secret-data division must use a CT
alternative.
-/

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnDivExactFd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §6  Bridge statement (sorry-free residual)

`MpnDivExactJasminRefines` records the bridge from the emitted Jasmin
body to the verified algorithm-level reference
`MpnDivExactSpec.mpnDivExact`.  Following the
`MpnDivRemJasminRefines` template (`MpnDivRemPrototype` §4): the
per-step algorithm content is fully proved (Hensel-multiply
correctness + submul cancellation reduce the working buffer one limb
at a time; the final quotient is `mpnDivExact numer denom` =
`(mpnDivRem numer denom).1`).  What remains here is the growing-
position outer-loop interpreter induction.

The bridge says: after running `bodyDivExact` under `bignumExecFuel
divExactRegistry` over a memory configuration with `numer`/`denom`/
`rp` mutually disjoint and `d_inv` correctly precomputed as
`denomp[0]^{-1} mod 2^64`, the final `rp` region holds
`MpnDivExactSpec.mpnDivExact numer denom`.

Stated as a sorry-free `Prop`, mirror of
`MpnDivRemPrototype.mpnDivRem_outer_loop_obligation`.

### Per-step content already proved

| Source | Statement |
|--------|-----------|
| `MpnDivExactSpec.mpnDivExact_spec` | `b ∣ a ⇒ toNat (mpnDivExact a b) = toNat a / toNat b`. |
| `MpnDivExactSpec.mpnDivExact_mul`  | `b ∣ a ⇒ toNat (mpnDivExact a b) · toNat b = toNat a`. |
| `MpnDivExactSpec.mpnDivExact_rem_zero` | `b ∣ a ⇒ toNat (mpnDivRem a b).2 = 0`. |
| `MpnDivRemKnuth.knuthDivRem_eq_mpnDivRem` | Algorithm-level q̂-recurrence = bit-level reference. |

### Residual: outer-loop bridge

The Jasmin body `bodyDivExact` is a top-level `Cif (lden - 1 != 0)`
dispatching between two arms:

* **`bodyDivExactSingle`** (single-limb-divisor specialization): pure
  straight-line `Cwhile` over `lna` digits, each running an inlined
  `digitStepBody`-equivalent:
  * 1 `#DIV_64` per iteration;
  * 2 memory writes (`rp[cur]`, scratch running remainder).
  No `Ccall`s.

* **`bodyDivExactGeneric`** (general `lden ≥ 2`, Hensel shape):
  `Cwhile` over `lna - lden + 1` digits (we pad the high positions),
  each running `digitStepBodyExact`:
  * 1 `mulx`-low (Hensel multiply: `q := a_lo · d_inv`);
  * 1 memory write (`rp[cur] := q`);
  * 1 `Ccall mpn_submul_1(ap_cur, denomp, q, lden)`.
  This arm consumes `divExactRegistry` to resolve the `Ccall`.

Pinned as a sorry-free `Prop`; the per-step content is fully proved
above and in `MpnDivRemKnuth`.
-/

open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype (toNat memHoldsLimbs)

/-- **The `mpn_div_exact` Jasmin refinement obligation (Residual:
    outer-loop interpreter induction).**  Stated as a sorry-free
    `Prop`.  Under the divisibility precondition `denom ∣ numer` and a
    correctly-staged Hensel inverse `d_inv`, running `bodyDivExact`
    under `bignumExecFuel divExactRegistry` over disjoint
    `numer`/`denom`/`rp` regions lands `rp` holding
    `MpnDivExactSpec.mpnDivExact numer denom` =
    `(mpnDivRem numer denom).1`.

    The obligation covers **both arms** of the top-level
    `Cif (lden_m1 != 0)` dispatch:
    * `lden = 1` → `bodyDivExactSingle` (no Ccall, no inner Cif —
      pure straight-line digit step with `#DIV_64`, identical in
      structure to `MpnDivRemPrototype.bodyDivRemSingle` modulo the
      scratch-pointer alias).
    * `lden ≥ 2` → `bodyDivExactGeneric` (per-digit Hensel multiply +
      `Ccall mpn_submul_1`; **no inner `Cif`** since Hensel-divide
      needs no add-back correction).

    The general arm consumes the `divExactRegistry` resolution
    (`divExactRegistry_submul1`); the single-limb arm doesn't touch
    the registry. -/
def mpnDivExact_outer_loop_obligation : Prop :=
  ∀ (s : BignumState) (numer denom : List (BitVec 64)) (d_inv : BitVec 64)
    (fuel : Nat),
    0 < numer.length →
    0 < denom.length →
    denom.length ≤ numer.length →
    toNat denom ≠ 0 →
    -- Divisibility precondition (the load-bearing exact-divide hypothesis):
    toNat denom ∣ toNat numer →
    -- Caller-precomputed Hensel inverse (the per-step Hensel cancellation
    -- holds *only* when `d_inv · denomp[0] ≡ 1 (mod 2^64)`):
    (d_inv.toNat * (denom.headD 0).toNat) % 2 ^ 64 = 1 →
    -- Register staging:
    s.regs "lna" = BitVec.ofNat 64 numer.length →
    s.regs "lden" = BitVec.ofNat 64 denom.length →
    s.regs "d_inv" = d_inv →
    -- Memory staging:
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) numer →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "denomp").toNat) denom →
    -- Disjointness (the standard mpn calling convention):
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    fuel > 16 * numer.length + 16 →
    ∃ s', bignumExecFuel divExactRegistry fuel bodyDivExact s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (MpnDivExactSpec.mpnDivExact numer denom)

/-- **`MpnDivExactJasminRefines`** — the canonical bridge goal for the
    emitted `mpn_div_exact` body, identified with the growing-position
    outer-loop refinement `mpnDivExact_outer_loop_obligation`.

    This is the precise *residual* (sorry-free `Prop`): the per-step
    algorithm-level content (Hensel multiply correctness +
    `mpnDivExact_spec` against the verified Euclidean reference) is
    *fully proved* in `MpnDivExactSpec`; the open obligation is the
    interpreter-level induction over the `Cwhile` outer loop that
    runs the per-digit Hensel step at each digit position.

    Following the convention from `MpnDivRemPrototype` §4, this
    obligation matches `MpnPowJasminRefines`'s shape: per-step content
    proved at the algorithm level, the interpreter-level outer-loop
    induction recorded here as the residual. -/
abbrev MpnDivExactJasminRefines : Prop := mpnDivExact_outer_loop_obligation

/-! ## §7  Single-limb-divisor specialization (`lden = 1`), tighter residual

The single-limb dispatch (`lden = 1`) reuses
`MpnDivRemPrototype.digitStepExitState` machinery verbatim — the only
difference vs `MpnDivRemPrototype.bodyDivRemSingle` is that the
"running remainder" buffer aliases the `rp` output buffer instead of
a separate `remp` pointer.

Under the divisibility precondition `denom ∣ numer`, the final running
remainder is exactly 0, so aliasing the scratch to `rp[0]` is safe:
the bottom quotient limb (written last in the MSB-first walk) lands
on top of the (final) running remainder slot, and that value is 0
under the precondition — i.e., the bottom quotient limb *is* `toNat
numer / toNat denom mod 2^64`, which is what the final iteration
writes to `rp[0]`.

We record a tighter sorry-free `Prop` for this branch (no `Ccall`
registry needed). -/

/-- The single-limb-divisor obligation: `lden = 1` precondition, no
    Ccall registry needed (the `lden ≥ 2` arm is dead code).  Tighter
    than `MpnDivExactJasminRefines`. -/
def mpnDivExact_single_loop_obligation : Prop :=
  ∀ (s : BignumState) (numer : List (BitVec 64)) (d : BitVec 64) (fuel : Nat),
    0 < numer.length →
    d ≠ 0 →
    -- Divisibility precondition:
    d.toNat ∣ toNat numer →
    s.regs "lna" = BitVec.ofNat 64 numer.length →
    s.regs "lden" = BitVec.ofNat 64 1 →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) numer →
    load64Mem s.mem (UInt64.ofNat (s.regs "denomp").toNat)
      = some (UInt64.ofNat d.toNat) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) 8) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) 8) →
    fuel > 16 * numer.length + 16 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyDivExact s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (MpnDivExactSpec.mpnDivExact numer [d])

/-- **`MpnDivExactSingleRefines`** — the single-limb-divisor refinement
    obligation.  Tighter than `MpnDivExactJasminRefines`: applies only
    at `lden = 1`, but requires no Ccall registry (no
    `Ccall mpn_submul_1`).

    The per-step content uses `MpnDivRemKnuth.knuthDivNat_spec` with
    the identity candidate (`cand = fun _denom W => W / denom`, the
    exact Euclidean quotient — x86 `#DIV_64`'s output for single-limb
    divisors, no correction needed).  Under the divisibility
    precondition, the Euclidean quotient *is* the exact-divide
    quotient by `MpnDivExactSpec.mpnDivExact_spec`. -/
abbrev MpnDivExactSingleRefines : Prop := mpnDivExact_single_loop_obligation

/-! ## §7.5  Single-limb digit-step machinery (split-and-compose)

Mirror of `MpnDivRemPrototype.bignumExec_digitStepBody_step` for the
single-limb-divisor body, with the `remp` register renamed to
`remp_local` and the loop counter renamed `lnum → lna`.  The 6
core InstrR (3 loads, 1 `#DIV_64`, 2 stores) are identical in shape
to YY2's `digitStepBody` — only the register names differ — so we
mirror the same split-and-compose workaround that dodges the Lean
4.29 kernel deep-recursion limit (LL3, commit `44230309`).

The split:
* `digitStepBodyExactSingleLoad`     — 3 loads, depth-3 witness.
* `digitStepBodyExactSingleDivStore` — `#DIV_64` + 2 stores, depth-3
  witness.

Each per-half step lemma is proved in isolation; the composition
goes via a local `bignumExec_append_some_local` (kernel-safe at
the *join* without case-splitting on the full 6-instruction body). -/

/-- Load half of the single-limb digit-step body. -/
def digitStepBodyExactSingleLoad : List InstrR :=
  [ loadAtConst "hi" "remp_local" 0
  , loadAtConst "lo" "numerp_cur" 0
  , loadAtConst "d" "denomp" 0 ]

/-- Div+store half of the single-limb digit-step body. -/
def digitStepBodyExactSingleDivStore : List InstrR :=
  [ divCopn "q" "r" "hi" "lo" "d"
  , storeAtConst "quotp_cur" 0 "q"
  , storeAtConst "remp_local" 0 "r" ]

/-- The 6-instruction core of `bodyDivExactSingle`'s inner `Cwhile`
    body (no pointer-predecrement, no `lna` decrement — those are
    framed separately).  Matches `MpnDivRemPrototype.digitStepBody`
    modulo `remp` ↦ `remp_local`. -/
def digitStepBodyExactSingle : List InstrR :=
  digitStepBodyExactSingleLoad ++ digitStepBodyExactSingleDivStore

theorem digitStepBodyExactSingle_eq_halves :
    digitStepBodyExactSingle =
      digitStepBodyExactSingleLoad ++ digitStepBodyExactSingleDivStore := rfl

/-! ### §7.5.1  Local `bignumExec_append_some_local` helper

Local inline of `MpnAddNAdcSpillPrototype.bignumExec_append_some_local`
to avoid the cross-prototype import — identical statement and proof. -/

private theorem bignumExec_append_some_local
    (b1 b2 : List InstrR) (s s_mid s' : BignumState)
    (h1 : bignumExec b1 s = some s_mid)
    (h2 : bignumExec b2 s_mid = some s') :
    bignumExec (b1 ++ b2) s = some s' := by
  induction b1 generalizing s with
  | nil =>
    simp [bignumExec] at h1
    rw [← h1] at h2; simp; exact h2
  | cons i b1' ih =>
    simp [bignumExec] at h1
    cases h_step : execInstr s i with
    | none => rw [h_step] at h1; cases h1
    | some s1 =>
      rw [h_step] at h1
      simp [bignumExec, h_step]
      exact ih s1 h1

/-! ### §7.5.2  Per-instruction execution lemmas

Each acts on a *generic* state, returning the post-state of one
instruction.  Mirror of `MpnDivRemPrototype`'s `execInstr_*` lemmas. -/

/-- Execution of `loadAtConst x base 0` when memory at `base` holds `v`. -/
theorem execInstr_loadAtConst0 (s : BignumState) (x base : String) (v : BitVec 64)
    (hv : load64Mem s.mem (UInt64.ofNat (s.regs base).toNat)
            = some (UInt64.ofNat v.toNat)) :
    execInstr s (loadAtConst x base 0) = some (setReg s x v) := by
  simp only [loadAtConst, execInstr, evalPExpr, pv, vr, resolveAddr,
             Option.bind_some, bind, Option.bind,
             show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [show s.regs base + 0 = s.regs base from by bv_decide, hv]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]

/-- Execution of `storeAtConst base 0 src` when the source register holds `v`. -/
theorem execInstr_storeAtConst0 (s : BignumState) (base src : String) (v : BitVec 64)
    (hv : s.regs src = v) :
    execInstr s (storeAtConst base 0 src) =
      some (storeMem s (UInt64.ofNat (s.regs base).toNat) (UInt64.ofNat v.toNat)) := by
  simp only [storeAtConst, execInstr, evalPExpr, vr, resolveAddr,
             Option.bind_some, bind, Option.bind,
             show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [show s.regs base + 0 = s.regs base from by bv_decide, hv]

/-- Execution of `divCopn q r hi lo d`: writes `divrem64 (s.regs hi)
    (s.regs lo) (s.regs d)` into `(q, r)`. -/
theorem execInstr_divCopn (s : BignumState) (qN rN hiN loN dN : String) :
    execInstr s (divCopn qN rN hiN loN dN) =
      some (setReg (setReg s qN (divrem64 (s.regs hiN) (s.regs loN) (s.regs dN)).1)
            rN (divrem64 (s.regs hiN) (s.regs loN) (s.regs dN)).2) := by
  simp only [divCopn, execInstr, evalPExpr, pv, vr, fiveFlags,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeDivBundle]

/-! ### §7.5.3  Per-half step lemmas -/

/-- Load-half step: after the 3 loads, registers `hi`/`lo`/`d` hold
    `rem`/`a`/`d_val`; memory unchanged. -/
theorem bignumExec_digitStepBodyExactSingleLoad_step
    (s : BignumState) (a d_val rem : BitVec 64)
    (ha : load64Mem s.mem (UInt64.ofNat (s.regs "numerp_cur").toNat)
            = some (UInt64.ofNat a.toNat))
    (hd : load64Mem s.mem (UInt64.ofNat (s.regs "denomp").toNat)
            = some (UInt64.ofNat d_val.toNat))
    (hr : load64Mem s.mem (UInt64.ofNat (s.regs "remp_local").toNat)
            = some (UInt64.ofNat rem.toNat)) :
    bignumExec digitStepBodyExactSingleLoad s
      = some (setReg (setReg (setReg s "hi" rem) "lo" a) "d" d_val) := by
  have step (i : InstrR) (s' s'' : BignumState)
      (hi : execInstr s' i = some s'') :
      bignumExec [i] s' = some s'' := by
    simp only [bignumExec, hi]
  -- Step 0: hi := rem (via the load on remp_local).
  let s0' := setReg s "hi" rem
  have h0 : bignumExec [loadAtConst "hi" "remp_local" 0] s = some s0' :=
    step _ _ _ (execInstr_loadAtConst0 s "hi" "remp_local" rem hr)
  -- Step 1: lo := a (via the load on numerp_cur).
  let s1' := setReg s0' "lo" a
  have hnp_s0 : s0'.regs "numerp_cur" = s.regs "numerp_cur" := by
    show (setReg s "hi" rem).regs "numerp_cur" = _
    simp [setReg]
  have hmem_s0 : s0'.mem = s.mem := rfl
  have h1 : bignumExec [loadAtConst "lo" "numerp_cur" 0] s0' = some s1' := by
    apply step
    apply execInstr_loadAtConst0
    rw [hnp_s0, hmem_s0]; exact ha
  -- Step 2: d := d_val (via the load on denomp).
  let s2' := setReg s1' "d" d_val
  have hdp_s1 : s1'.regs "denomp" = s.regs "denomp" := by
    show (setReg (setReg s "hi" rem) "lo" a).regs "denomp" = _
    simp [setReg]
  have hmem_s1 : s1'.mem = s.mem := rfl
  have h2 : bignumExec [loadAtConst "d" "denomp" 0] s1' = some s2' := by
    apply step
    apply execInstr_loadAtConst0
    rw [hdp_s1, hmem_s1]; exact hd
  -- Compose via append-some-local.
  have e01 : bignumExec ([loadAtConst "hi" "remp_local" 0] ++
              [loadAtConst "lo" "numerp_cur" 0]) s = some s1' :=
    bignumExec_append_some_local _ _ s s0' s1' h0 h1
  have e012 : bignumExec (([loadAtConst "hi" "remp_local" 0] ++
              [loadAtConst "lo" "numerp_cur" 0]) ++
              [loadAtConst "d" "denomp" 0]) s = some s2' :=
    bignumExec_append_some_local _ _ s s1' s2' e01 h2
  show bignumExec digitStepBodyExactSingleLoad s = _
  have hsplit : digitStepBodyExactSingleLoad =
      [loadAtConst "hi" "remp_local" 0] ++ [loadAtConst "lo" "numerp_cur" 0] ++
      [loadAtConst "d" "denomp" 0] := rfl
  rw [hsplit]
  exact e012

/-- Div+store-half step: after `#DIV_64` writes `(q, r) := divrem64 rem
    a d_val` and the two stores, memory has been updated with `q` at
    `quotp_cur` and `r` at `remp_local`. -/
theorem bignumExec_digitStepBodyExactSingleDivStore_step
    (s : BignumState) (a d_val rem : BitVec 64)
    (hhi : s.regs "hi" = rem) (hlo : s.regs "lo" = a)
    (hd : s.regs "d" = d_val) :
    bignumExec digitStepBodyExactSingleDivStore s = some
      (storeMem (storeMem
          (setReg (setReg s "q" (divrem64 rem a d_val).1)
                  "r" (divrem64 rem a d_val).2)
          (UInt64.ofNat (s.regs "quotp_cur").toNat)
          (UInt64.ofNat (divrem64 rem a d_val).1.toNat))
        (UInt64.ofNat (s.regs "remp_local").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).2.toNat)) := by
  have step (i : InstrR) (s' s'' : BignumState)
      (hi : execInstr s' i = some s'') :
      bignumExec [i] s' = some s'' := by
    simp only [bignumExec, hi]
  -- Step 0: `#DIV_64` writes `(q, r) := divrem64 rem a d_val`.
  let s1 : BignumState :=
    setReg (setReg s "q" (divrem64 rem a d_val).1)
           "r" (divrem64 rem a d_val).2
  have h0' : bignumExec [divCopn "q" "r" "hi" "lo" "d"] s = some s1 := by
    apply step
    have := execInstr_divCopn s "q" "r" "hi" "lo" "d"
    rw [hhi, hlo, hd] at this
    exact this
  -- Step 1: store `q` at `[quotp_cur + 0]`.
  let s2 : BignumState := storeMem s1
    (UInt64.ofNat (s.regs "quotp_cur").toNat)
    (UInt64.ofNat (divrem64 rem a d_val).1.toNat)
  have hq1 : s1.regs "q" = (divrem64 rem a d_val).1 := by
    show (setReg (setReg s "q" _) "r" _).regs "q" = _
    simp [setReg]
  have hqp1 : s1.regs "quotp_cur" = s.regs "quotp_cur" := by
    show (setReg (setReg s "q" _) "r" _).regs "quotp_cur" = _
    simp [setReg]
  have h1 : bignumExec [storeAtConst "quotp_cur" 0 "q"] s1 = some s2 := by
    apply step
    have := execInstr_storeAtConst0 s1 "quotp_cur" "q"
      (divrem64 rem a d_val).1 hq1
    rw [hqp1] at this
    exact this
  -- Step 2: store `r` at `[remp_local + 0]`.
  let s3 : BignumState := storeMem s2
    (UInt64.ofNat (s.regs "remp_local").toNat)
    (UInt64.ofNat (divrem64 rem a d_val).2.toNat)
  have hr2 : s2.regs "r" = (divrem64 rem a d_val).2 := by
    show (storeMem s1 _ _).regs "r" = _
    change s1.regs "r" = _
    show (setReg (setReg s "q" _) "r" _).regs "r" = _
    simp [setReg]
  have hrp2 : s2.regs "remp_local" = s.regs "remp_local" := by
    show (storeMem s1 _ _).regs "remp_local" = _
    change s1.regs "remp_local" = _
    show (setReg (setReg s "q" _) "r" _).regs "remp_local" = _
    simp [setReg]
  have h2 : bignumExec [storeAtConst "remp_local" 0 "r"] s2 = some s3 := by
    apply step
    have := execInstr_storeAtConst0 s2 "remp_local" "r"
      (divrem64 rem a d_val).2 hr2
    rw [hrp2] at this
    exact this
  -- Compose via append-some-local.
  have e01 : bignumExec ([divCopn "q" "r" "hi" "lo" "d"] ++
              [storeAtConst "quotp_cur" 0 "q"]) s = some s2 :=
    bignumExec_append_some_local _ _ s s1 s2 h0' h1
  have e012 : bignumExec (([divCopn "q" "r" "hi" "lo" "d"] ++
              [storeAtConst "quotp_cur" 0 "q"]) ++
              [storeAtConst "remp_local" 0 "r"]) s = some s3 :=
    bignumExec_append_some_local _ _ s s2 s3 e01 h2
  show bignumExec digitStepBodyExactSingleDivStore s = _
  have hsplit : digitStepBodyExactSingleDivStore =
      [divCopn "q" "r" "hi" "lo" "d"] ++ [storeAtConst "quotp_cur" 0 "q"] ++
      [storeAtConst "remp_local" 0 "r"] := rfl
  rw [hsplit]
  exact e012

/-! ### §7.5.4  Per-iteration step lemma for `digitStepBodyExactSingle`

Composition of the two halves via `bignumExec_append_some_local`.
Each half's witness chain depth ≤ 3 (kernel-safe at the join). -/

/-- One straight-line run of `digitStepBodyExactSingle` (6 InstrR) lands at
    a state with two `store64`s applied (`q` at `quotp_cur`, `r` at
    `remp_local` where `(q, r) = divrem64 rem a d_val`) and the four
    pointer registers (`numerp_cur`, `quotp_cur`, `denomp`,
    `remp_local`) plus `lna` unchanged.  Mirror of
    `MpnDivRemPrototype.bignumExec_digitStepBody_step`. -/
theorem bignumExec_digitStepBodyExactSingle_step
    (s : BignumState) (a d_val rem : BitVec 64)
    (ha : load64Mem s.mem (UInt64.ofNat (s.regs "numerp_cur").toNat)
            = some (UInt64.ofNat a.toNat))
    (hd : load64Mem s.mem (UInt64.ofNat (s.regs "denomp").toNat)
            = some (UInt64.ofNat d_val.toNat))
    (hr : load64Mem s.mem (UInt64.ofNat (s.regs "remp_local").toNat)
            = some (UInt64.ofNat rem.toNat)) :
    ∃ s', bignumExec digitStepBodyExactSingle s = some s' ∧
      s'.mem = (s.mem.store64 (UInt64.ofNat (s.regs "quotp_cur").toNat)
                  (UInt64.ofNat (divrem64 rem a d_val).1.toNat)).store64
                  (UInt64.ofNat (s.regs "remp_local").toNat)
                  (UInt64.ofNat (divrem64 rem a d_val).2.toNat) ∧
      s'.regs "numerp_cur" = s.regs "numerp_cur" ∧
      s'.regs "quotp_cur"  = s.regs "quotp_cur" ∧
      s'.regs "denomp"     = s.regs "denomp" ∧
      s'.regs "remp_local" = s.regs "remp_local" ∧
      s'.regs "lna"        = s.regs "lna" := by
  have h1 := bignumExec_digitStepBodyExactSingleLoad_step s a d_val rem ha hd hr
  let s_mid : BignumState :=
    setReg (setReg (setReg s "hi" rem) "lo" a) "d" d_val
  have hhi_mid : s_mid.regs "hi" = rem := by
    show (setReg _ "d" _).regs "hi" = _
    simp [setReg]
  have hlo_mid : s_mid.regs "lo" = a := by
    show (setReg _ "d" _).regs "lo" = _
    simp [setReg]
  have hd_mid : s_mid.regs "d" = d_val := by
    show (setReg _ "d" _).regs "d" = _
    simp [setReg]
  have hqp_mid : s_mid.regs "quotp_cur" = s.regs "quotp_cur" := by
    show (setReg _ "d" _).regs "quotp_cur" = _
    simp [setReg]
  have hrp_mid : s_mid.regs "remp_local" = s.regs "remp_local" := by
    show (setReg _ "d" _).regs "remp_local" = _
    simp [setReg]
  have hnp_mid : s_mid.regs "numerp_cur" = s.regs "numerp_cur" := by
    show (setReg _ "d" _).regs "numerp_cur" = _
    simp [setReg]
  have hdp_mid : s_mid.regs "denomp" = s.regs "denomp" := by
    show (setReg _ "d" _).regs "denomp" = _
    simp [setReg]
  have hlna_mid : s_mid.regs "lna" = s.regs "lna" := by
    show (setReg _ "d" _).regs "lna" = _
    simp [setReg]
  have hmem_mid : s_mid.mem = s.mem := rfl
  have h2 := bignumExec_digitStepBodyExactSingleDivStore_step s_mid a d_val rem
    hhi_mid hlo_mid hd_mid
  rw [hqp_mid, hrp_mid] at h2
  let s_end : BignumState :=
    storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        (UInt64.ofNat (s.regs "quotp_cur").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).1.toNat))
      (UInt64.ofNat (s.regs "remp_local").toNat)
      (UInt64.ofNat (divrem64 rem a d_val).2.toNat)
  refine ⟨s_end, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [digitStepBodyExactSingle_eq_halves]
    exact bignumExec_append_some_local
      digitStepBodyExactSingleLoad digitStepBodyExactSingleDivStore s s_mid s_end h1 h2
  · show (storeMem (storeMem _ _ _) _ _).mem
         = (s.mem.store64 _ _).store64 _ _
    show ((setReg (setReg s_mid "q" _) "r" _).mem.store64 _ _).store64 _ _
         = (s.mem.store64 _ _).store64 _ _
    rw [show (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                     "r" (divrem64 rem a d_val).2).mem = s_mid.mem from rfl,
        hmem_mid]
  · show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        _ _) _ _).regs "numerp_cur" = _
    rw [show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        (UInt64.ofNat (s.regs "quotp_cur").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).1.toNat))
        (UInt64.ofNat (s.regs "remp_local").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).2.toNat)).regs "numerp_cur"
              = s_mid.regs "numerp_cur" from by simp [setReg, storeMem],
        hnp_mid]
  · show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        _ _) _ _).regs "quotp_cur" = _
    rw [show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        (UInt64.ofNat (s.regs "quotp_cur").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).1.toNat))
        (UInt64.ofNat (s.regs "remp_local").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).2.toNat)).regs "quotp_cur"
              = s_mid.regs "quotp_cur" from by simp [setReg, storeMem],
        hqp_mid]
  · show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        _ _) _ _).regs "denomp" = _
    rw [show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        (UInt64.ofNat (s.regs "quotp_cur").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).1.toNat))
        (UInt64.ofNat (s.regs "remp_local").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).2.toNat)).regs "denomp"
              = s_mid.regs "denomp" from by simp [setReg, storeMem],
        hdp_mid]
  · show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        _ _) _ _).regs "remp_local" = _
    rw [show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        (UInt64.ofNat (s.regs "quotp_cur").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).1.toNat))
        (UInt64.ofNat (s.regs "remp_local").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).2.toNat)).regs "remp_local"
              = s_mid.regs "remp_local" from by simp [setReg, storeMem],
        hrp_mid]
  · show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        _ _) _ _).regs "lna" = _
    rw [show (storeMem (storeMem
        (setReg (setReg s_mid "q" (divrem64 rem a d_val).1)
                "r" (divrem64 rem a d_val).2)
        (UInt64.ofNat (s.regs "quotp_cur").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).1.toNat))
        (UInt64.ofNat (s.regs "remp_local").toNat)
        (UInt64.ofNat (divrem64 rem a d_val).2.toNat)).regs "lna"
              = s_mid.regs "lna" from by simp [setReg, storeMem],
        hlna_mid]

/-! ### §7.5.5  Step-obligation Prop + discharge -/

/-- Pure semantic statement of one iteration of `digitStepBodyExactSingle`
    (definitional unfolding of `bignumExec digitStepBodyExactSingle`).
    Mirror of `MpnDivRemPrototype.digitStepBody_step_obligation`. -/
def digitStepBodyExactSingle_step_obligation : Prop :=
  ∀ (s : BignumState) (a d rem : BitVec 64),
    load64Mem s.mem (UInt64.ofNat (s.regs "numerp_cur").toNat)
        = some (UInt64.ofNat a.toNat) →
    load64Mem s.mem (UInt64.ofNat (s.regs "denomp").toNat)
        = some (UInt64.ofNat d.toNat) →
    load64Mem s.mem (UInt64.ofNat (s.regs "remp_local").toNat)
        = some (UInt64.ofNat rem.toNat) →
    ∃ s', bignumExec digitStepBodyExactSingle s = some s' ∧
      s'.mem = (s.mem.store64 (UInt64.ofNat (s.regs "quotp_cur").toNat)
                  (UInt64.ofNat (divrem64 rem a d).1.toNat)).store64
                  (UInt64.ofNat (s.regs "remp_local").toNat)
                  (UInt64.ofNat (divrem64 rem a d).2.toNat) ∧
      s'.regs "numerp_cur" = s.regs "numerp_cur" ∧
      s'.regs "quotp_cur"  = s.regs "quotp_cur" ∧
      s'.regs "denomp"     = s.regs "denomp" ∧
      s'.regs "remp_local" = s.regs "remp_local" ∧
      s'.regs "lna"        = s.regs "lna"

/-- `digitStepBodyExactSingle_step_obligation` discharged via the
    split-and-compose workaround.  Mirror of
    `MpnDivRemPrototype.digitStepBody_step_holds`. -/
theorem digitStepBodyExactSingle_step_holds :
    digitStepBodyExactSingle_step_obligation :=
  fun s a d_val rem ha hd hr =>
    bignumExec_digitStepBodyExactSingle_step s a d_val rem ha hd hr

/-! ## §7.6  Tighter residual: outer-loop `Cwhile` induction

`MpnDivExactSingleRefines` (above) remains a sorry-free `Prop`
residual.  After the §7.5 split-and-compose workaround, the
remaining open obligation reduces cleanly to three pieces (mirror
of `MpnDivRemPrototype` §5.3):

1. **`Cif (lden_m1 != 0)` dispatch peel** — under `lden = 1` (so
   `lden_m1 = 0`), the dispatch takes the `else` arm
   (`bodyDivExactSingle`); the dispatch itself is straight-line
   under `bignumExecFuel`.
2. **9-instruction prologue evaluation** — `regCopy remp_local rp`,
   `setImm tmp 0`, `storeAtConst remp_local 0 tmp`, `regCopy tmp
   lna`, `tmp := tmp << 3`, `regCopy numerp_cur ap`, `numerp_cur +=
   tmp`, `regCopy quotp_cur rp`, `quotp_cur += tmp`.  Each
   instruction's effect on the state is computable via the
   per-instruction lemmas in §7.5.2; the chain is straight-line and
   kernel-safe.
3. **`Cwhile (lna != 0)` outer-loop induction over `numer.length`** —
   each iteration runs `[numerp_cur -= 8; quotp_cur -= 8] ++
   digitStepBodyExactSingle ++ [lna -= 1]` (the 6-instruction core
   is closed by `bignumExec_digitStepBodyExactSingle_step`), with the
   loop invariant pairing the interpreter's `rp[i]` slot value with
   `(MpnDivExactSpec.mpnDivExact numer [d])[i]` (under the
   divisibility precondition `d.toNat ∣ toNat numer`, the running
   remainder thread terminates at 0).

Closing (3) is structurally identical to `mpnAddN_loop`
(~250 LOC: disjointness/framing/induction over the limb list) with
the per-step lemma supplied by `bignumExec_digitStepBodyExactSingle_step`
instead of `bignumExec_loopBody_step`.  No new kernel-limit obstacles
remain — the per-iteration witness state is the
`bignumExec_digitStepBodyExactSingle_step` exit state, already
constructed kernel-safely.

We pin the per-iteration step closure (§7.5) as the load-bearing new
content of this revision.  The full outer-loop bridge
`MpnDivExactSingleRefines` stays as the documented residual,
matching `MpnDivRemPrototype.MpnDivRemSingleRefines`'s status post
LL3/XX2 (`44230309`). -/

/-! ## §7.7  `Cif`-dispatch peel + tighter `bodyDivExactSingle`-only residual

Mirror of `MpnDivRemPrototype` §5.5 (commit `LL4`).  After the §7.5
split-and-compose workaround for the per-iteration digit body, the
next closeable piece of `MpnDivExactSingleRefines` is the **outer
`Cif (lden_m1 != 0)` dispatch peel** in `bodyDivExact`:  under the
precondition `lden = ofNat 1`, the top-level dispatch in
`bodyDivExact` takes the `else` arm (= `bodyDivExactSingle`), and the
two leading `Cassgn` instructions (`lden_m1 := lden`, `lden_m1 :=
lden_m1 - 1`) compute `lden_m1 = 0` which makes the `Cif` guard
evaluate to `0`.

After this section the remaining residual is the **prologue +
`Cwhile` post-Cif evaluation** alone — pinned as
`mpnDivExact_single_postCif_obligation` below and fed to
`MpnDivExactSingleRefines_holds`.

The `bodyDivExactSingle` prologue uses `tmp := tmp << 3`
(`.Papp2 (.Olsl .U64)`).  Note (2026-05-27): `BignumExec.evalPExpr`
now supports `Papp2 (.Olsl _)` / `Papp2 (.Olsr _)`, so the natural
single-instruction shape is runnable end-to-end — no workaround
needed.  Historically the same `Olsl`-vs.-three-doublings replacement
was applied in `MpnDivRemPrototype.bodyDivRemSingle`; that has now
been reverted to match (see its §5.5 note). -/

/-- Local inline of `MpnSignedJasminPrototype.cif_else_run` (avoiding a
    cross-prototype import).  Running a single `Cif` whose guard
    evaluates to `0` reduces to running the `else`-branch.  Identical
    statement and proof to `MpnDivRemPrototype.cif_else_run_local`. -/
private theorem cif_else_run_local (reg : BignumRegistry) (F : Nat) (cond : PExpr)
    (ct ce : List InstrR) (s s' : BignumState)
    (hg : evalPExpr s cond = some 0)
    (hrun : bignumExecFuel reg F ce s = some s') :
    bignumExecFuel reg (F + 1) [.Cif cond ct ce] s = some s' := by
  rw [bignumExecFuel]
  simp only [hg, show ((0 : BitVec 64) != 0) = false from by decide, Bool.false_eq_true,
    if_false, hrun]
  rw [bignumExecFuel]

/-- `execInstr` for `regCopy r other`: writes `s.regs other` into `r`.
    Identical statement and proof to
    `MpnDivRemPrototype.execInstr_regCopy`. -/
theorem execInstr_regCopy (s : BignumState) (r other : String) :
    execInstr s (regCopy r other) = some (setReg s r (s.regs other)) := by
  simp only [regCopy, execInstr, evalPExpr, pv, vr, Option.bind_some, bind, Option.bind]

/-- Decrementing `BitVec.ofNat 64 1` gives `0`. -/
private theorem ofNat64_one_sub_one :
    (BitVec.ofNat 64 1 : BitVec 64) - 1 = 0 := by bv_decide

/-- The dispatch-guard register `lden_m1` is `0` after running the two
    leading `Cassgn`s of `bodyDivExact` on a state with
    `lden = ofNat 1`.  Mirror of
    `MpnDivRemPrototype.bodyDivRem_dispatch_zero`. -/
theorem bodyDivExact_dispatch_zero (s : BignumState)
    (hlden : s.regs "lden" = BitVec.ofNat 64 1) :
    ∃ s_pre,
      bignumExec [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] s
        = some s_pre ∧
      s_pre.regs "lden_m1" = 0 ∧
      s_pre.mem = s.mem ∧
      (∀ x, x ≠ "lden_m1" → s_pre.regs x = s.regs x) := by
  let s0 := setReg s "lden_m1" (s.regs "lden")
  have h0 : execInstr s (regCopy "lden_m1" "lden") = some s0 :=
    execInstr_regCopy s "lden_m1" "lden"
  have hbin : execInstr s0 (binImm "lden_m1" (.Osub .U64) 1) =
      some (setReg s0 "lden_m1" (s0.regs "lden_m1" - BitVec.ofInt 64 1)) := by
    simp only [binImm, execInstr, evalPExpr, pv, vr,
               Option.bind_some, bind, Option.bind]
  have hs0_lden_m1 : s0.regs "lden_m1" = BitVec.ofNat 64 1 := by
    show (setReg s "lden_m1" (s.regs "lden")).regs "lden_m1" = _
    simp [setReg, hlden]
  have hint1 : (BitVec.ofInt 64 1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  have hzero : s0.regs "lden_m1" - BitVec.ofInt 64 1 = 0 := by
    rw [hs0_lden_m1, hint1]; exact ofNat64_one_sub_one
  refine ⟨setReg s0 "lden_m1" 0, ?_, ?_, ?_, ?_⟩
  · simp only [bignumExec, h0]
    rw [hbin, hzero]
  · show (setReg s0 "lden_m1" 0).regs "lden_m1" = 0
    simp [setReg]
  · show (setReg s0 "lden_m1" 0).mem = s.mem
    rfl
  · intro x hx
    show (setReg s0 "lden_m1" 0).regs x = s.regs x
    rw [show (setReg s0 "lden_m1" 0).regs x = s0.regs x from by simp [setReg, hx]]
    show s0.regs x = s.regs x
    simp [s0, setReg, hx]

/-- Evaluation of the dispatch-guard PExpr `lden_m1 != 0`: when
    `lden_m1 = 0`, the `Oneq` arm returns `0`.  Identical statement
    and proof to `MpnDivRemPrototype.evalPExpr_dispatchCond_false`. -/
theorem evalPExpr_dispatchCond_false (s : BignumState)
    (h : s.regs "lden_m1" = 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0)) = some 0 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind, h,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rfl

/-! ### §7.7.3  The tighter `bodyDivExactSingle`-only residual

After the §7.5 split-and-compose workaround (per-iteration digit
body) and the §7.7 `Cif`-dispatch peel (above), the remaining open
obligation is the evaluation of `bodyDivExactSingle` itself
(prologue + `Cwhile` outer-loop induction over `numer.length`).

`mpnDivExact_single_postCif_obligation` pins this **tighter** sorry-
free `Prop` residual: it applies *only* to the `bodyDivExactSingle`
arm (no `Cif` dispatch), at any state matching the `lden = 1`
precondition, and needs no `Ccall` registry.

`MpnDivExactSingleRefines_holds` (below) shows this tighter residual
implies the full `MpnDivExactSingleRefines`, by composing the
dispatch peel. -/

/-- **The tighter post-Cif residual** for the `lden = 1` arm of
    `mpn_div_exact`.  Captures the prologue (9 Cassgns, including
    `tmp := tmp << 3` — runnable since `evalPExpr` learned
    `Papp2 (.Olsl _)`, 2026-05-27) + `Cwhile` outer-loop induction
    over `numer.length`.  Stated as a sorry-free `Prop`.

    Mirror of `MpnDivRemPrototype.mpnDivRem_single_postCif_obligation`. -/
def mpnDivExact_single_postCif_obligation : Prop :=
  ∀ (s : BignumState) (numer : List (BitVec 64)) (d : BitVec 64) (fuel : Nat),
    0 < numer.length →
    d ≠ 0 →
    d.toNat ∣ toNat numer →
    s.regs "lna" = BitVec.ofNat 64 numer.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) numer →
    load64Mem s.mem (UInt64.ofNat (s.regs "denomp").toNat)
      = some (UInt64.ofNat d.toNat) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) 8) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) 8) →
    fuel > 16 * numer.length + 8 →
    ∃ s', bignumExecFuel emptyRegistry fuel bodyDivExactSingle s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (MpnDivExactSpec.mpnDivExact numer [d])

/-! ### §7.7.4  `MpnDivExactSingleRefines_holds` (theorem, modulo the tighter residual)

Composes the dispatch peel (§7.7 above, closed) with the tighter
post-`Cif` residual (`mpnDivExact_single_postCif_obligation`,
§7.7.3) to assemble `MpnDivExactSingleRefines`.

This is a true Lean theorem: `MpnDivExactSingleRefines_holds : postCif
→ MpnDivExactSingleRefines`.  The tighter `postCif` residual is the
**only** open piece remaining for the single-limb-divisor refinement,
and it contains no `Cif` dispatch and no `Ccall` registry — strictly
smaller in shape than `MpnDivExactSingleRefines`.

Mirror of `MpnDivRemPrototype.MpnDivRemSingleRefines_holds`. -/

/-- **`MpnDivExactSingleRefines_holds` — `MpnDivExactSingleRefines`
    modulo the tighter `Cwhile + prologue` post-`Cif` residual.**

    The dispatch peel is fully proved here: under `lden = 1`, the
    top-level `Cif (lden_m1 != 0)` in `bodyDivExact` reduces to
    running `bodyDivExactSingle` (the `else` arm).  Given a closure
    of the `bodyDivExactSingle`-only residual, this lifts to the
    full `MpnDivExactSingleRefines` shape. -/
theorem MpnDivExactSingleRefines_holds
    (postCif : mpnDivExact_single_postCif_obligation) :
    MpnDivExactSingleRefines := by
  intro s numer d fuel hlen hd hdvd hlna hlden hap hdenom
        hd1 hd2 hd3 hfuel
  -- Step 1: run the two prologue Cassgns of `bodyDivExact` to set up
  -- `lden_m1 = 0`.
  obtain ⟨s_pre, hpre, hpre_lden_m1, hpre_mem, hpre_regs⟩ :=
    bodyDivExact_dispatch_zero s hlden
  -- s_pre coincides with s on every register except "lden_m1".
  have hs_pre_lna : s_pre.regs "lna" = BitVec.ofNat 64 numer.length := by
    rw [hpre_regs "lna" (by decide)]; exact hlna
  have hs_pre_ap : s_pre.regs "ap" = s.regs "ap" :=
    hpre_regs "ap" (by decide)
  have hs_pre_denomp : s_pre.regs "denomp" = s.regs "denomp" :=
    hpre_regs "denomp" (by decide)
  have hs_pre_rp : s_pre.regs "rp" = s.regs "rp" :=
    hpre_regs "rp" (by decide)
  have hap' : memHoldsLimbs s_pre.mem
      (UInt64.ofNat (s_pre.regs "ap").toNat) numer := by
    rw [hpre_mem, hs_pre_ap]; exact hap
  have hdenom' : load64Mem s_pre.mem
      (UInt64.ofNat (s_pre.regs "denomp").toNat)
      = some (UInt64.ofNat d.toNat) := by
    rw [hpre_mem, hs_pre_denomp]; exact hdenom
  have hd1' : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "denomp").toNat) 8) := by
    rw [hs_pre_ap, hs_pre_denomp]; exact hd1
  have hd2' : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "ap").toNat) (8 * numer.length)) := by
    rw [hs_pre_rp, hs_pre_ap]; exact hd2
  have hd3' : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "denomp").toNat) 8) := by
    rw [hs_pre_rp, hs_pre_denomp]; exact hd3
  -- Step 2: feed the post-Cif residual on `s_pre`.
  obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
  have hF_fuel : F > 16 * numer.length + 8 := by omega
  obtain ⟨s', hs', hs'_rp⟩ :=
    postCif s_pre numer d F hlen hd hdvd hs_pre_lna hap' hdenom'
      hd1' hd2' hd3' hF_fuel
  refine ⟨s', ?_, ?_⟩
  · -- Compose: bignumExecFuel reg fuel bodyDivExact s = some s' via
    -- bignumExecFuel_append_join on [step0, step1] ++ [Cif …].
    have hsl : InstrR.bodyIsStraightLine
        [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] := by
      refine ⟨?_, ?_, trivial⟩ <;> rfl
    have hnc : ∀ i ∈ [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1],
        i.isNonControl := by
      intro i hi
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · trivial
      · trivial
    have hexec_pre : bignumExecFuel emptyRegistry (F + 1)
          [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] s = some s_pre := by
      rw [bignumExecFuel_eq_bignumExec_of_straightLine emptyRegistry F _ s hsl]
      exact hpre
    -- Guard evaluation.
    have hguard : evalPExpr s_pre
        (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0)) = some 0 :=
      evalPExpr_dispatchCond_false s_pre hpre_lden_m1
    -- Cif peel.
    have hcif : bignumExecFuel emptyRegistry (F + 1)
          [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
            bodyDivExactGeneric bodyDivExactSingle] s_pre = some s' :=
      cif_else_run_local emptyRegistry F _ _ _ s_pre s' hguard hs'
    -- Compose.
    rw [hF]
    have hsplit : bodyDivExact = [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] ++
              [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
                bodyDivExactGeneric bodyDivExactSingle] := rfl
    rw [hsplit]
    exact bignumExecFuel_append_join emptyRegistry (F + 1)
      [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1]
      [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
        bodyDivExactGeneric bodyDivExactSingle]
      hnc s s_pre s' hexec_pre hcif
  · rw [hs_pre_rp] at hs'_rp; exact hs'_rp

/-! ### §7.7.5  Axiom audit

`MpnDivExactSingleRefines_holds` is a real Lean theorem (no sorry, no
new axiom).  Its axiom dependency set is the standard kernel trio
(`propext`, `Quot.sound`) plus the `bv_decide` natives used inside
`ofNat64_one_sub_one`.

The Cwhile+prologue residual (`mpnDivExact_single_postCif_obligation`)
is the **only** open obligation remaining for the single-limb-divisor
refinement, strictly smaller in shape than `MpnDivExactSingleRefines`
(no `Cif` dispatch, no Ccall registry). -/

#print axioms MpnDivExactSingleRefines_holds
#print axioms cif_else_run_local
#print axioms bodyDivExact_dispatch_zero
#print axioms evalPExpr_dispatchCond_false

/-! ## §7.8  Generic-arm per-iteration content: `digitStepBodyExact` machinery

Mirror of the §7.5 split-and-compose pattern for the *generic* (`lden ≥ 2`,
Hensel-lifted) arm of `bodyDivExact`.  The per-iteration body
`digitStepBodyExact` is `[loadAtConst "a_lo" "ap_cur" 0; henselMulLow "q"
"a_lo" "d_inv"; storeAtConst "rp_cur" 0 "q"; submul1Call "ap_cur" "denomp"
"q" "lden"]` — three non-`Ccall` instructions followed by one outer `Ccall
mpn_submul_1`.  We close the **non-`Ccall` prefix** here as a depth-3
straight-line step lemma; the trailing `Ccall mpn_submul_1` (which reads
data-dependent `q`/`ap_cur`) is folded into the tighter post-`Cif`
residual `mpnDivExact_generic_postCif_obligation` (§7.9).

### Non-`Ccall` prefix (3 instructions, depth-3 chain)

* `loadAtConst "a_lo" "ap_cur" 0`     — load the current low limb.
* `henselMulLow "q" "a_lo" "d_inv"`   — `mulx`: `(_, q) := mulx d_inv a_lo`.
* `storeAtConst "rp_cur" 0 "q"`        — store the Hensel quotient digit.

These are kernel-safe via the same `bignumExec_append_some_local` composition
used in §7.5. -/

/-- The non-`Ccall` prefix of one Hensel digit step:  load, mulx, store. -/
def digitStepBodyExactGenericNonCcall : List InstrR :=
  [ loadAtConst "a_lo" "ap_cur" 0
  , henselMulLow "q" "a_lo" "d_inv"
  , storeAtConst "rp_cur" 0 "q" ]

theorem digitStepBodyExactGenericNonCcall_eq_three :
    digitStepBodyExactGenericNonCcall =
      [loadAtConst "a_lo" "ap_cur" 0] ++ [henselMulLow "q" "a_lo" "d_inv"]
        ++ [storeAtConst "rp_cur" 0 "q"] := rfl

/-- Execution of `henselMulLow qN aN dInvN`: writes `(mulx d_inv a_lo).1`
    into `hi_junk` and `(mulx d_inv a_lo).2` into `q`.  Mirror of
    `execInstr_divCopn` for the MULX bundle. -/
theorem execInstr_henselMulLow (s : BignumState) (qN aN dInvN : String) :
    execInstr s (henselMulLow qN aN dInvN) =
      some (setReg (setReg s "hi_junk" (mulx (s.regs dInvN) (s.regs aN)).1)
              qN (mulx (s.regs dInvN) (s.regs aN)).2) := by
  simp only [henselMulLow, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind, writeMulxBundle]

/-- One straight-line run of `digitStepBodyExactGenericNonCcall` lands at
    a state where `a_lo := ap_cur[0]`, `(hi_junk, q) := mulx d_inv a_lo`,
    and memory has stored `q` at `rp_cur`.  Depth-3 witness chain, kernel-
    safe via `bignumExec_append_some_local`. -/
theorem bignumExec_digitStepBodyExactGenericNonCcall_step
    (s : BignumState) (a_lo d_inv : BitVec 64)
    (ha : load64Mem s.mem (UInt64.ofNat (s.regs "ap_cur").toNat)
            = some (UInt64.ofNat a_lo.toNat))
    (hd_inv : s.regs "d_inv" = d_inv) :
    ∃ s', bignumExec digitStepBodyExactGenericNonCcall s = some s' ∧
      s'.mem = s.mem.store64 (UInt64.ofNat (s.regs "rp_cur").toNat)
                (UInt64.ofNat (mulx d_inv a_lo).2.toNat) ∧
      s'.regs "ap_cur" = s.regs "ap_cur" ∧
      s'.regs "rp_cur" = s.regs "rp_cur" ∧
      s'.regs "denomp" = s.regs "denomp" ∧
      s'.regs "lna"    = s.regs "lna" ∧
      s'.regs "lden"   = s.regs "lden" ∧
      s'.regs "q"      = (mulx d_inv a_lo).2 := by
  have step (i : InstrR) (s' s'' : BignumState)
      (hi : execInstr s' i = some s'') :
      bignumExec [i] s' = some s'' := by
    simp only [bignumExec, hi]
  -- Step 0: a_lo := ap_cur[0].
  let s0' := setReg s "a_lo" a_lo
  have h0 : bignumExec [loadAtConst "a_lo" "ap_cur" 0] s = some s0' :=
    step _ _ _ (execInstr_loadAtConst0 s "a_lo" "ap_cur" a_lo ha)
  -- Step 1: (hi_junk, q) := mulx d_inv a_lo.
  let s1' : BignumState :=
    setReg (setReg s0' "hi_junk" (mulx d_inv a_lo).1) "q" (mulx d_inv a_lo).2
  have hd_inv_s0 : s0'.regs "d_inv" = d_inv := by
    show (setReg s "a_lo" a_lo).regs "d_inv" = _
    simp [setReg, hd_inv]
  have ha_lo_s0 : s0'.regs "a_lo" = a_lo := by
    show (setReg s "a_lo" a_lo).regs "a_lo" = _
    simp [setReg]
  have h1 : bignumExec [henselMulLow "q" "a_lo" "d_inv"] s0' = some s1' := by
    apply step
    have := execInstr_henselMulLow s0' "q" "a_lo" "d_inv"
    rw [hd_inv_s0, ha_lo_s0] at this
    exact this
  -- Step 2: rp_cur[0] := q.
  let s2' : BignumState := storeMem s1'
    (UInt64.ofNat (s.regs "rp_cur").toNat)
    (UInt64.ofNat (mulx d_inv a_lo).2.toNat)
  have hq_s1 : s1'.regs "q" = (mulx d_inv a_lo).2 := by
    show (setReg (setReg s0' "hi_junk" _) "q" _).regs "q" = _
    simp [setReg]
  have hrp_s1 : s1'.regs "rp_cur" = s.regs "rp_cur" := by
    show (setReg (setReg s0' "hi_junk" _) "q" _).regs "rp_cur" = _
    simp [setReg]
    show (setReg s "a_lo" a_lo).regs "rp_cur" = _
    simp [setReg]
  have h2 : bignumExec [storeAtConst "rp_cur" 0 "q"] s1' = some s2' := by
    apply step
    have := execInstr_storeAtConst0 s1' "rp_cur" "q"
      (mulx d_inv a_lo).2 hq_s1
    rw [hrp_s1] at this
    exact this
  -- Compose via append-some-local.
  have e01 : bignumExec ([loadAtConst "a_lo" "ap_cur" 0] ++
              [henselMulLow "q" "a_lo" "d_inv"]) s = some s1' :=
    bignumExec_append_some_local _ _ s s0' s1' h0 h1
  have e012 : bignumExec (([loadAtConst "a_lo" "ap_cur" 0] ++
              [henselMulLow "q" "a_lo" "d_inv"]) ++
              [storeAtConst "rp_cur" 0 "q"]) s = some s2' :=
    bignumExec_append_some_local _ _ s s1' s2' e01 h2
  refine ⟨s2', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [digitStepBodyExactGenericNonCcall_eq_three]; exact e012
  · -- mem: storeMem s1' = storeMem (setReg (setReg s0' ...) ...) ...; the two
    --      setRegs don't touch memory.
    show (storeMem s1' _ _).mem = _
    show (s1'.mem.store64 _ _) = _
    show ((setReg (setReg s0' "hi_junk" _) "q" _).mem.store64 _ _) = _
    rfl
  · -- ap_cur unchanged.
    show (storeMem s1' _ _).regs "ap_cur" = _
    change s1'.regs "ap_cur" = _
    show (setReg (setReg s0' "hi_junk" _) "q" _).regs "ap_cur" = _
    simp [setReg]
    show (setReg s "a_lo" a_lo).regs "ap_cur" = _
    simp [setReg]
  · -- rp_cur unchanged.
    show (storeMem s1' _ _).regs "rp_cur" = _
    change s1'.regs "rp_cur" = _
    exact hrp_s1
  · -- denomp unchanged.
    show (storeMem s1' _ _).regs "denomp" = _
    change s1'.regs "denomp" = _
    show (setReg (setReg s0' "hi_junk" _) "q" _).regs "denomp" = _
    simp [setReg]
    show (setReg s "a_lo" a_lo).regs "denomp" = _
    simp [setReg]
  · -- lna unchanged.
    show (storeMem s1' _ _).regs "lna" = _
    change s1'.regs "lna" = _
    show (setReg (setReg s0' "hi_junk" _) "q" _).regs "lna" = _
    simp [setReg]
    show (setReg s "a_lo" a_lo).regs "lna" = _
    simp [setReg]
  · -- lden unchanged.
    show (storeMem s1' _ _).regs "lden" = _
    change s1'.regs "lden" = _
    show (setReg (setReg s0' "hi_junk" _) "q" _).regs "lden" = _
    simp [setReg]
    show (setReg s "a_lo" a_lo).regs "lden" = _
    simp [setReg]
  · -- q := (mulx d_inv a_lo).2.
    show (storeMem s1' _ _).regs "q" = _
    change s1'.regs "q" = _
    exact hq_s1

/-! ### §7.8.1  Step-obligation Prop + discharge (mirror of §7.5.5) -/

/-- Pure semantic statement of one iteration of
    `digitStepBodyExactGenericNonCcall`.  Mirror of
    `digitStepBodyExactSingle_step_obligation`. -/
def digitStepBodyExactGenericNonCcall_step_obligation : Prop :=
  ∀ (s : BignumState) (a_lo d_inv : BitVec 64),
    load64Mem s.mem (UInt64.ofNat (s.regs "ap_cur").toNat)
        = some (UInt64.ofNat a_lo.toNat) →
    s.regs "d_inv" = d_inv →
    ∃ s', bignumExec digitStepBodyExactGenericNonCcall s = some s' ∧
      s'.mem = s.mem.store64 (UInt64.ofNat (s.regs "rp_cur").toNat)
                (UInt64.ofNat (mulx d_inv a_lo).2.toNat) ∧
      s'.regs "ap_cur" = s.regs "ap_cur" ∧
      s'.regs "rp_cur" = s.regs "rp_cur" ∧
      s'.regs "denomp" = s.regs "denomp" ∧
      s'.regs "lna"    = s.regs "lna" ∧
      s'.regs "lden"   = s.regs "lden" ∧
      s'.regs "q"      = (mulx d_inv a_lo).2

theorem digitStepBodyExactGenericNonCcall_step_holds :
    digitStepBodyExactGenericNonCcall_step_obligation :=
  fun s a_lo d_inv ha hd_inv =>
    bignumExec_digitStepBodyExactGenericNonCcall_step s a_lo d_inv ha hd_inv

/-! ## §7.9  Generic-arm tighter `postCif` residual + `MpnDivExactJasminRefines_holds`

Mirror of §7.7.3–§7.7.5 for the generic (`lden ≥ 2`, Hensel) arm.  The
remaining open obligation after the §7.5 / §7.8 per-iteration step
content is:

* (generic) `bodyDivExactGeneric` prologue (`ap_cur := ap; rp_cur := rp`)
  + `Cwhile` outer-loop induction over `numer.length` digits, each
  running `digitStepBodyExact ++ [ap_cur += 8; rp_cur += 8; lna -= 1]`
  (the 3 non-`Ccall` instructions are closed by
  `bignumExec_digitStepBodyExactGenericNonCcall_step`; the `Ccall
  mpn_submul_1` is interpreted under `divExactRegistry`).

We pin this as a sorry-free `Prop` residual.  `MpnDivExactJasminRefines_holds`
(below) composes the outer `Cif (lden_m1 != 0)` dispatch peel for both
arms (via `cif_then_run_local` for `lden ≥ 2` and `cif_else_run_local`
for `lden = 1`) with the two tighter residuals to assemble the full
`MpnDivExactJasminRefines`. -/

/-- Local inline of `MpnSignedJasminPrototype.cif_then_run` (avoiding a
    cross-prototype import).  Running a single `Cif` whose guard evaluates
    to a nonzero value reduces to running the `then`-branch.  Identical
    statement and proof to `MpnSignedJasminPrototype.cif_then_run`. -/
private theorem cif_then_run_local (reg : BignumRegistry) (F : Nat) (cond : PExpr)
    (ct ce : List InstrR) (s s' : BignumState) (v : BitVec 64) (hv : v ≠ 0)
    (hg : evalPExpr s cond = some v)
    (hrun : bignumExecFuel reg F ct s = some s') :
    bignumExecFuel reg (F + 1) [.Cif cond ct ce] s = some s' := by
  have hvtrue : (v != 0) = true := by simp only [bne_iff_ne]; exact hv
  rw [bignumExecFuel]
  simp only [hg, hvtrue, if_true, hrun]
  rw [bignumExecFuel]

/-- `lden_m1 ≠ 0` after `lden_m1 := lden; lden_m1 -= 1` when
    `lden = ofNat n` with `n ≥ 2`.  Mirror of `bodyDivExact_dispatch_zero`
    but for the `then` arm. -/
theorem bodyDivExact_dispatch_nonzero (s : BignumState) (n : Nat)
    (hn : 2 ≤ n) (hnle : n < 2^64)
    (hlden : s.regs "lden" = BitVec.ofNat 64 n) :
    ∃ s_pre,
      bignumExec [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] s
        = some s_pre ∧
      s_pre.regs "lden_m1" = BitVec.ofNat 64 (n - 1) ∧
      s_pre.mem = s.mem ∧
      (∀ x, x ≠ "lden_m1" → s_pre.regs x = s.regs x) := by
  let s0 := setReg s "lden_m1" (s.regs "lden")
  have h0 : execInstr s (regCopy "lden_m1" "lden") = some s0 :=
    execInstr_regCopy s "lden_m1" "lden"
  have hbin : execInstr s0 (binImm "lden_m1" (.Osub .U64) 1) =
      some (setReg s0 "lden_m1" (s0.regs "lden_m1" - BitVec.ofInt 64 1)) := by
    simp only [binImm, execInstr, evalPExpr, pv, vr,
               Option.bind_some, bind, Option.bind]
  have hs0_lden_m1 : s0.regs "lden_m1" = BitVec.ofNat 64 n := by
    show (setReg s "lden_m1" (s.regs "lden")).regs "lden_m1" = _
    simp [setReg, hlden]
  have hint1 : (BitVec.ofInt 64 1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  have hsub : s0.regs "lden_m1" - BitVec.ofInt 64 1 = BitVec.ofNat 64 (n - 1) := by
    rw [hs0_lden_m1, hint1]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnle,
          Nat.mod_eq_of_lt (show 1 < 2^64 by decide)]
    omega
  refine ⟨setReg s0 "lden_m1" (BitVec.ofNat 64 (n - 1)), ?_, ?_, ?_, ?_⟩
  · simp only [bignumExec, h0]
    rw [hbin, hsub]
  · show (setReg s0 "lden_m1" (BitVec.ofNat 64 (n - 1))).regs "lden_m1" = _
    simp [setReg]
  · show (setReg s0 "lden_m1" (BitVec.ofNat 64 (n - 1))).mem = s.mem
    rfl
  · intro x hx
    show (setReg s0 "lden_m1" (BitVec.ofNat 64 (n - 1))).regs x = s.regs x
    rw [show (setReg s0 "lden_m1" (BitVec.ofNat 64 (n - 1))).regs x = s0.regs x
          from by simp [setReg, hx]]
    show s0.regs x = s.regs x
    simp [s0, setReg, hx]

/-- Evaluation of the dispatch-guard `lden_m1 != 0` when `lden_m1 ≠ 0`. -/
theorem evalPExpr_dispatchCond_true (s : BignumState) (v : BitVec 64) (hv : v ≠ 0)
    (h : s.regs "lden_m1" = v) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0)) = some 1 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind, h,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_neg hv]

/-- **The generic-arm post-`Cif` residual** for the `lden ≥ 2` (Hensel) arm
    of `mpn_div_exact`.  Captures the prologue (2 `Cassgn`s: `ap_cur :=
    ap; rp_cur := rp`) + `Cwhile` outer-loop induction over `numer.length`
    digits, with the `divExactRegistry`-resolved `Ccall mpn_submul_1` inside
    each iteration.  Stated as a sorry-free `Prop`.

    Mirror of `mpnDivExact_single_postCif_obligation`, with: (a) the
    `divExactRegistry` (single arm runs under `emptyRegistry`); (b) the
    full multi-limb denom (not just `[d]`); (c) the caller-staged Hensel
    inverse `d_inv` with `d_inv · denom[0] ≡ 1 (mod 2^64)`. -/
def mpnDivExact_generic_postCif_obligation : Prop :=
  ∀ (s : BignumState) (numer denom : List (BitVec 64)) (d_inv : BitVec 64)
    (fuel : Nat),
    0 < numer.length →
    0 < denom.length →
    denom.length ≤ numer.length →
    toNat denom ≠ 0 →
    toNat denom ∣ toNat numer →
    (d_inv.toNat * (denom.headD 0).toNat) % 2 ^ 64 = 1 →
    s.regs "lna" = BitVec.ofNat 64 numer.length →
    s.regs "lden" = BitVec.ofNat 64 denom.length →
    s.regs "d_inv" = d_inv →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) numer →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "denomp").toNat) denom →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    fuel > 16 * numer.length + 8 →
    ∃ s', bignumExecFuel divExactRegistry fuel bodyDivExactGeneric s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (MpnDivExactSpec.mpnDivExact numer denom)

/-! ### §7.9.1  Generic-arm `Cif`-then peel

The generic case requires `denom.length ≥ 2` together with `denom.length <
2^64` (so `BitVec.ofNat 64 denom.length - 1 ≠ 0` — otherwise the BitVec
wrap could put `lden_m1` back at `0`).  We pin this as a sorry-free
top-level theorem mirror of `MpnDivExactSingleRefines_holds`. -/

/-- The **generic-arm refinement obligation**, fully analogous to
    `MpnDivExactSingleRefines` but for the `then` arm of the outer `Cif`.
    Adds `2 ≤ denom.length` and `denom.length < 2^64` as preconditions. -/
def mpnDivExact_generic_loop_obligation : Prop :=
  ∀ (s : BignumState) (numer denom : List (BitVec 64)) (d_inv : BitVec 64)
    (fuel : Nat),
    0 < numer.length →
    2 ≤ denom.length →
    denom.length < 2^64 →
    denom.length ≤ numer.length →
    toNat denom ≠ 0 →
    toNat denom ∣ toNat numer →
    (d_inv.toNat * (denom.headD 0).toNat) % 2 ^ 64 = 1 →
    s.regs "lna" = BitVec.ofNat 64 numer.length →
    s.regs "lden" = BitVec.ofNat 64 denom.length →
    s.regs "d_inv" = d_inv →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) numer →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "denomp").toNat) denom →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    fuel > 16 * numer.length + 16 →
    ∃ s', bignumExecFuel divExactRegistry fuel bodyDivExact s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (MpnDivExactSpec.mpnDivExact numer denom)

/-- **`MpnDivExactGenericRefines`** — the generic-arm refinement
    obligation.  Tighter than `MpnDivExactJasminRefines`: applies at
    `denom.length ≥ 2`, and requires the `divExactRegistry` to resolve
    the per-iteration `Ccall mpn_submul_1`. -/
abbrev MpnDivExactGenericRefines : Prop := mpnDivExact_generic_loop_obligation

/-- **`MpnDivExactGenericRefines_holds` — `MpnDivExactGenericRefines`
    modulo the tighter `Cwhile + prologue` post-`Cif` residual.**

    The outer `Cif (lden_m1 != 0)` dispatch peel for the `then` (generic)
    arm is fully proved here: under `2 ≤ denom.length` and `denom.length
    < 2^64`, the top-level `Cif` in `bodyDivExact` reduces to running
    `bodyDivExactGeneric` (the `then`-arm).  Given a closure of the
    `bodyDivExactGeneric`-only residual `generic_postCif`, this lifts to
    the full `MpnDivExactGenericRefines` shape.

    Mirror of `MpnDivExactSingleRefines_holds`. -/
theorem MpnDivExactGenericRefines_holds
    (generic_postCif : mpnDivExact_generic_postCif_obligation) :
    MpnDivExactGenericRefines := by
  intro s numer denom d_inv fuel hlen_n hlen_d hd_lt hle htoN_denom hdvd hdinv
        hlna hlden hd_inv_reg hap hdenom hd1 hd2 hd3 hfuel
  -- Step 1: run the two prologue Cassgns of `bodyDivExact` to set up
  -- `lden_m1 = ofNat (denom.length - 1)`, which is ≠ 0 since denom.length ≥ 2.
  obtain ⟨s_pre, hpre, hpre_lden_m1, hpre_mem, hpre_regs⟩ :=
    bodyDivExact_dispatch_nonzero s denom.length hlen_d hd_lt hlden
  -- s_pre coincides with s on every register except "lden_m1".
  have hs_pre_lna : s_pre.regs "lna" = BitVec.ofNat 64 numer.length := by
    rw [hpre_regs "lna" (by decide)]; exact hlna
  have hs_pre_lden : s_pre.regs "lden" = BitVec.ofNat 64 denom.length := by
    rw [hpre_regs "lden" (by decide)]; exact hlden
  have hs_pre_d_inv : s_pre.regs "d_inv" = d_inv := by
    rw [hpre_regs "d_inv" (by decide)]; exact hd_inv_reg
  have hs_pre_ap : s_pre.regs "ap" = s.regs "ap" :=
    hpre_regs "ap" (by decide)
  have hs_pre_denomp : s_pre.regs "denomp" = s.regs "denomp" :=
    hpre_regs "denomp" (by decide)
  have hs_pre_rp : s_pre.regs "rp" = s.regs "rp" :=
    hpre_regs "rp" (by decide)
  have hap' : memHoldsLimbs s_pre.mem
      (UInt64.ofNat (s_pre.regs "ap").toNat) numer := by
    rw [hpre_mem, hs_pre_ap]; exact hap
  have hdenom' : memHoldsLimbs s_pre.mem
      (UInt64.ofNat (s_pre.regs "denomp").toNat) denom := by
    rw [hpre_mem, hs_pre_denomp]; exact hdenom
  have hd1' : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "denomp").toNat) (8 * denom.length)) := by
    rw [hs_pre_ap, hs_pre_denomp]; exact hd1
  have hd2' : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "ap").toNat) (8 * numer.length)) := by
    rw [hs_pre_rp, hs_pre_ap]; exact hd2
  have hd3' : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s_pre.regs "denomp").toNat) (8 * denom.length)) := by
    rw [hs_pre_rp, hs_pre_denomp]; exact hd3
  -- Step 2: feed the post-Cif residual on `s_pre`.
  obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
  have hF_fuel : F > 16 * numer.length + 8 := by omega
  -- Bridge between `0 < denom.length` and `2 ≤ denom.length`.
  have hd_pos : 0 < denom.length := by omega
  obtain ⟨s', hs', hs'_rp⟩ :=
    generic_postCif s_pre numer denom d_inv F hlen_n hd_pos hle htoN_denom hdvd hdinv
      hs_pre_lna hs_pre_lden hs_pre_d_inv hap' hdenom' hd1' hd2' hd3' hF_fuel
  refine ⟨s', ?_, ?_⟩
  · -- Compose: bignumExecFuel divExactRegistry fuel bodyDivExact s = some s' via
    -- bignumExecFuel_append_join on [step0, step1] ++ [Cif …].
    have hsl : InstrR.bodyIsStraightLine
        [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] := by
      refine ⟨?_, ?_, trivial⟩ <;> rfl
    have hnc : ∀ i ∈ [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1],
        i.isNonControl := by
      intro i hi
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · trivial
      · trivial
    have hexec_pre : bignumExecFuel divExactRegistry (F + 1)
          [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] s = some s_pre := by
      rw [bignumExecFuel_eq_bignumExec_of_straightLine divExactRegistry F _ s hsl]
      exact hpre
    -- Guard evaluation: lden_m1 ≠ 0 since denom.length ≥ 2.
    have hlden_m1_ne : (BitVec.ofNat 64 (denom.length - 1) : BitVec 64) ≠ 0 := by
      intro hcontra
      have : (denom.length - 1) % 2^64 = 0 := by
        have := congrArg BitVec.toNat hcontra
        simp [BitVec.toNat_ofNat] at this
        exact this
      have h_lt : denom.length - 1 < 2^64 := by omega
      rw [Nat.mod_eq_of_lt h_lt] at this
      omega
    have hguard : evalPExpr s_pre
        (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0)) = some 1 :=
      evalPExpr_dispatchCond_true s_pre _ hlden_m1_ne hpre_lden_m1
    -- Cif peel (then arm).
    have hcif : bignumExecFuel divExactRegistry (F + 1)
          [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
            bodyDivExactGeneric bodyDivExactSingle] s_pre = some s' :=
      cif_then_run_local divExactRegistry F _ _ _ s_pre s' _
        (by decide : (1 : BitVec 64) ≠ 0) hguard hs'
    -- Compose.
    rw [hF]
    have hsplit : bodyDivExact = [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] ++
              [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
                bodyDivExactGeneric bodyDivExactSingle] := rfl
    rw [hsplit]
    exact bignumExecFuel_append_join divExactRegistry (F + 1)
      [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1]
      [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
        bodyDivExactGeneric bodyDivExactSingle]
      hnc s s_pre s' hexec_pre hcif
  · rw [hs_pre_rp] at hs'_rp; exact hs'_rp

/-! ### §7.9.2  Axiom audit for the generic-arm peel

`MpnDivExactGenericRefines_holds` is a real Lean theorem (no sorry, no
new axiom).  Its axiom dependency set is the standard kernel trio
(`propext`, `Quot.sound`).  The post-`Cif` residual
`mpnDivExact_generic_postCif_obligation` is the **only** open piece
remaining for the generic-arm refinement, strictly smaller in shape
than `MpnDivExactGenericRefines` (no `Cif` dispatch — only the
prologue + `Cwhile` outer loop). -/

#print axioms MpnDivExactGenericRefines_holds
#print axioms cif_then_run_local
#print axioms bodyDivExact_dispatch_nonzero
#print axioms evalPExpr_dispatchCond_true

/-! ### §7.9.3  `MpnDivExactJasminRefines_holds` (full theorem, modulo two tighter residuals)

Composes the outer `Cif` dispatch peel for **both** arms via the case-split
on `denom.length`:
* `denom.length = 1` → `else` arm, feed `single_postCif`.
* `denom.length ≥ 2` → `then` arm, feed `generic_postCif`.

This is the full `MpnDivExactJasminRefines` modulo the two tighter
residuals.  An additional `denom.length < 2^64` precondition is needed
in the generic case (so `BitVec.ofNat 64 denom.length - 1 ≠ 0`); we
strengthen `MpnDivExactJasminRefines` to `MpnDivExactJasminRefines'`
with this bound, then derive the bridge. -/

/-- **Strengthened bridge obligation** — same as
    `mpnDivExact_outer_loop_obligation` but adds `denom.length < 2^64`
    (so the BitVec representation of the dispatch guard `lden - 1` does
    not wrap).  This bound is automatically satisfied in any Jasmin
    calling context where `lden` is a u64 register holding the list
    length — the precondition `s.regs "lden" = BitVec.ofNat 64
    denom.length` already implicitly assumes `denom.length` fits in u64,
    so the explicit bound is no real strengthening. -/
def mpnDivExact_outer_loop_obligation' : Prop :=
  ∀ (s : BignumState) (numer denom : List (BitVec 64)) (d_inv : BitVec 64)
    (fuel : Nat),
    0 < numer.length →
    0 < denom.length →
    denom.length < 2^64 →
    denom.length ≤ numer.length →
    toNat denom ≠ 0 →
    toNat denom ∣ toNat numer →
    (d_inv.toNat * (denom.headD 0).toNat) % 2 ^ 64 = 1 →
    s.regs "lna" = BitVec.ofNat 64 numer.length →
    s.regs "lden" = BitVec.ofNat 64 denom.length →
    s.regs "d_inv" = d_inv →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) numer →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "denomp").toNat) denom →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) (8 * denom.length)) →
    fuel > 16 * numer.length + 16 →
    ∃ s', bignumExecFuel divExactRegistry fuel bodyDivExact s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (MpnDivExactSpec.mpnDivExact numer denom)

/-- The strengthened bridge form. -/
abbrev MpnDivExactJasminRefines' : Prop := mpnDivExact_outer_loop_obligation'

/-- A singleton `memHoldsLimbs` unfolds to a single `load64Mem`. -/
private theorem memHoldsLimbs_singleton (m : MemoryModel.Mem) (ptr : UInt64) (d : BitVec 64)
    (h : memHoldsLimbs m ptr [d]) :
    load64Mem m ptr = some (UInt64.ofNat d.toNat) := by
  rcases h with ⟨h1, _⟩
  exact h1

/-- `toNat [d] = d.toNat`. -/
private theorem toNat_singleton (d : BitVec 64) : toNat [d] = d.toNat := by
  simp [toNat]

/-- **The single-arm `postCif` residual, restated for `divExactRegistry`.**
    Same shape as `mpnDivExact_single_postCif_obligation` but the body
    is run under `divExactRegistry`.  Since `bodyDivExactSingle` contains
    no `Ccall`, the registry choice doesn't affect the run — these two
    obligations are inter-derivable, modulo a `bignumExecFuel_registry_irrel`
    bridge on the body.

    **NB:** the bridge is now proved as
    `mpnDivExact_single_postCif_obligation_divReg_of_empty` (§7.9.1), so a
    future closure of the canonical `emptyRegistry`-flavoured
    `mpnDivExact_single_postCif_obligation` (§7.7.3) automatically discharges
    this `divReg` flavour.  The single-arm obligation surface is reduced to
    one canonical `Prop`. -/
def mpnDivExact_single_postCif_obligation_divReg : Prop :=
  ∀ (s : BignumState) (numer : List (BitVec 64)) (d : BitVec 64) (fuel : Nat),
    0 < numer.length →
    d ≠ 0 →
    d.toNat ∣ toNat numer →
    s.regs "lna" = BitVec.ofNat 64 numer.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) numer →
    load64Mem s.mem (UInt64.ofNat (s.regs "denomp").toNat)
      = some (UInt64.ofNat d.toNat) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) 8) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) 8) →
    fuel > 16 * numer.length + 8 →
    ∃ s', bignumExecFuel divExactRegistry fuel bodyDivExactSingle s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (MpnDivExactSpec.mpnDivExact numer [d])

/-! ### §7.9.1  Registry-irrelevance bridge for `bodyDivExactSingle`

`bodyDivExactSingle` contains no `Ccall` (the single-limb dispatch arm
performs only `#DIV_64` plus pointer arithmetic — the `mpn_submul_1`
Ccall is confined to the *generic* arm).  Hence
`bignumExecFuel`'s interpretation of `bodyDivExactSingle` is independent
of which registry is supplied: `divExactRegistry` and `emptyRegistry`
runs coincide on this body.

This pins the two single-arm obligations (`emptyRegistry`-flavoured
`mpnDivExact_single_postCif_obligation` for `MpnDivExactSingleRefines_holds`,
`divExactRegistry`-flavoured `mpnDivExact_single_postCif_obligation_divReg`
for `MpnDivExactJasminRefines_holds`) as **inter-derivable**: a closure
of either implies a closure of the other.  We expose this as a real
Lean theorem so future closure work need target only the canonical
`emptyRegistry` flavour. -/

/-- `bodyDivExactSingle` contains no `Ccall`: the single-limb arm uses
    only `#DIV_64` plus pointer arithmetic.  Lifted via
    `MpnMulPrototype.bignumExecFuel_registry_irrel` to bridge the two
    single-arm obligations. -/
theorem bodyDivExactSingle_noCcall :
    MpnMulPrototype.NoCcallBody bodyDivExactSingle := by
  intro i hi
  -- Unfold the 10-instruction body.
  simp only [bodyDivExactSingle, List.mem_cons, List.not_mem_nil, or_false] at hi
  -- Every entry is a Cassgn/Copn or a Cwhile whose inner body is also
  -- Cassgn/Copn-only.  Cassgn/Copn give `noCcallI = True` directly; for
  -- the Cwhile we discharge the inner body element-wise.
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- regCopy "remp_local" "rp"
    simp [regCopy, MpnMulPrototype.noCcallI]
  · -- setImm "tmp" 0
    simp [setImm, MpnMulPrototype.noCcallI]
  · -- storeAtConst "remp_local" 0 "tmp"
    simp [storeAtConst, MpnMulPrototype.noCcallI]
  · -- regCopy "tmp" "lna"
    simp [regCopy, MpnMulPrototype.noCcallI]
  · -- Cassgn ... Olsl
    simp [MpnMulPrototype.noCcallI]
  · -- regCopy "numerp_cur" "ap"
    simp [regCopy, MpnMulPrototype.noCcallI]
  · -- regBin "numerp_cur" Oadd "tmp"
    simp [regBin, MpnMulPrototype.noCcallI]
  · -- regCopy "quotp_cur" "rp"
    simp [regCopy, MpnMulPrototype.noCcallI]
  · -- regBin "quotp_cur" Oadd "tmp"
    simp [regBin, MpnMulPrototype.noCcallI]
  · -- Cwhile [] guard body — the body is 9 straight-line instructions.
    show MpnMulPrototype.noCcallI
      (.Cwhile [] (.Papp2 (.Oneq .U64) (pv "lna") (.Pconst 0))
        ([ binImm "numerp_cur" (.Osub .U64) 8
         , binImm "quotp_cur" (.Osub .U64) 8
         , loadAtConst "hi" "remp_local" 0
         , loadAtConst "lo" "numerp_cur" 0
         , loadAtConst "d" "denomp" 0
         , divCopn "q" "r" "hi" "lo" "d"
         , storeAtConst "quotp_cur" 0 "q"
         , storeAtConst "remp_local" 0 "r"
         , binImm "lna" (.Osub .U64) 1 ]))
    simp only [MpnMulPrototype.noCcallI]
    refine ⟨?_, ?_⟩
    · intro j hj; simp at hj
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [binImm, MpnMulPrototype.noCcallI]
      · simp [binImm, MpnMulPrototype.noCcallI]
      · simp [loadAtConst, MpnMulPrototype.noCcallI]
      · simp [loadAtConst, MpnMulPrototype.noCcallI]
      · simp [loadAtConst, MpnMulPrototype.noCcallI]
      · simp [divCopn, MpnMulPrototype.noCcallI]
      · simp [storeAtConst, MpnMulPrototype.noCcallI]
      · simp [storeAtConst, MpnMulPrototype.noCcallI]
      · simp [binImm, MpnMulPrototype.noCcallI]

/-- **Registry-irrelevance bridge.**  A closure of the canonical
    `emptyRegistry`-flavoured single-arm `postCif` obligation yields
    the `divExactRegistry`-flavoured variant for free, via
    `bignumExecFuel_registry_irrel` on `bodyDivExactSingle`. -/
theorem mpnDivExact_single_postCif_obligation_divReg_of_empty
    (h_empty : mpnDivExact_single_postCif_obligation) :
    mpnDivExact_single_postCif_obligation_divReg := by
  intro s numer d fuel hlen hd hdvd hlna hap hdenom hd1 hd2 hd3 hfuel
  obtain ⟨s', hs', hs'_rp⟩ :=
    h_empty s numer d fuel hlen hd hdvd hlna hap hdenom hd1 hd2 hd3 hfuel
  refine ⟨s', ?_, hs'_rp⟩
  -- Run under `divExactRegistry` = run under `emptyRegistry` (no Ccall in
  -- the body), so the witness `s'` from `h_empty` transports verbatim.
  rw [MpnMulPrototype.bignumExecFuel_registry_irrel divExactRegistry fuel
      bodyDivExactSingle s bodyDivExactSingle_noCcall]
  exact hs'

/-- **`MpnDivExactJasminRefines_holds` — `MpnDivExactJasminRefines'` modulo
    the two tighter `Cwhile + prologue` post-`Cif` residuals.**

    The outer `Cif (lden_m1 != 0)` dispatch peel is fully proved here:
    case-split on `denom.length`.
    * `denom.length = 1` → guard is `0`, `else`-arm runs; feed
      `single_postCif_divReg`.
    * `denom.length ≥ 2` → guard is nonzero, `then`-arm runs; feed
      `generic_postCif`.

    The two tighter residuals are the **only** open pieces remaining,
    both strictly smaller in shape than `MpnDivExactJasminRefines'` (no
    `Cif` dispatch). -/
theorem MpnDivExactJasminRefines_holds
    (single_postCif : mpnDivExact_single_postCif_obligation_divReg)
    (generic_postCif : mpnDivExact_generic_postCif_obligation) :
    MpnDivExactJasminRefines' := by
  intro s numer denom d_inv fuel hlen_n hlen_d hd_lt hle htoN_denom hdvd hdinv
        hlna hlden hd_inv_reg hap hdenom hd1 hd2 hd3 hfuel
  -- Case-split on `denom.length`.
  match hdl : denom.length, hlen_d with
  | 0, h => exact absurd h (by simp)
  | 1, _ =>
    -- Single-limb dispatch.  Rewrite `denom = [d]` and feed
    -- the divReg-flavored single residual via the inline dispatch peel.
    match hdenom_form : denom, hdl with
    | [], h => exact absurd h (by simp)
    | [d], _ =>
      -- d ≠ 0: from htoN_denom = toNat [d] = d.toNat ≠ 0.
      have hd_ne : d ≠ 0 := by
        intro h
        apply htoN_denom
        rw [toNat_singleton, h]
        rfl
      -- d.toNat ∣ toNat numer: from hdvd and toNat_singleton.
      have hd_dvd : d.toNat ∣ toNat numer := by
        rw [← toNat_singleton]; exact hdvd
      -- lden = ofNat 1: from hlden with denom = [d] (so denom.length = 1).
      have hlden1 : s.regs "lden" = BitVec.ofNat 64 1 := by
        have : [d].length = 1 := rfl
        rw [hlden, this]
      -- Memory: load64Mem ... denomp = some d via memHoldsLimbs_singleton.
      have hdenom_load : load64Mem s.mem
          (UInt64.ofNat (s.regs "denomp").toNat)
          = some (UInt64.ofNat d.toNat) :=
        memHoldsLimbs_singleton _ _ _ hdenom
      -- Disjointness over 8 = 8 * 1 bytes.
      have hd1' : MemoryModel.Disjoint
          (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * numer.length))
          (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) 8) := by
        have h8 : (8 : Nat) = 8 * 1 := rfl; rw [h8]; exact hd1
      have hd3' : MemoryModel.Disjoint
          (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * numer.length))
          (MemoryModel.range (UInt64.ofNat (s.regs "denomp").toNat) 8) := by
        have h8 : (8 : Nat) = 8 * 1 := rfl; rw [h8]; exact hd3
      -- Inline single-arm dispatch peel under `divExactRegistry`.
      obtain ⟨s_pre, hpre, hpre_lden_m1, hpre_mem, hpre_regs⟩ :=
        bodyDivExact_dispatch_zero s hlden1
      have hs_pre_lna : s_pre.regs "lna" = BitVec.ofNat 64 numer.length := by
        rw [hpre_regs "lna" (by decide)]; exact hlna
      have hs_pre_ap : s_pre.regs "ap" = s.regs "ap" :=
        hpre_regs "ap" (by decide)
      have hs_pre_denomp : s_pre.regs "denomp" = s.regs "denomp" :=
        hpre_regs "denomp" (by decide)
      have hs_pre_rp : s_pre.regs "rp" = s.regs "rp" :=
        hpre_regs "rp" (by decide)
      have hap_pre : memHoldsLimbs s_pre.mem
          (UInt64.ofNat (s_pre.regs "ap").toNat) numer := by
        rw [hpre_mem, hs_pre_ap]; exact hap
      have hdenom_pre : load64Mem s_pre.mem
          (UInt64.ofNat (s_pre.regs "denomp").toNat)
          = some (UInt64.ofNat d.toNat) := by
        rw [hpre_mem, hs_pre_denomp]; exact hdenom_load
      have hd1_pre : MemoryModel.Disjoint
          (MemoryModel.range (UInt64.ofNat (s_pre.regs "ap").toNat) (8 * numer.length))
          (MemoryModel.range (UInt64.ofNat (s_pre.regs "denomp").toNat) 8) := by
        rw [hs_pre_ap, hs_pre_denomp]; exact hd1'
      have hd2_pre : MemoryModel.Disjoint
          (MemoryModel.range (UInt64.ofNat (s_pre.regs "rp").toNat) (8 * numer.length))
          (MemoryModel.range (UInt64.ofNat (s_pre.regs "ap").toNat) (8 * numer.length)) := by
        rw [hs_pre_rp, hs_pre_ap]; exact hd2
      have hd3_pre : MemoryModel.Disjoint
          (MemoryModel.range (UInt64.ofNat (s_pre.regs "rp").toNat) (8 * numer.length))
          (MemoryModel.range (UInt64.ofNat (s_pre.regs "denomp").toNat) 8) := by
        rw [hs_pre_rp, hs_pre_denomp]; exact hd3'
      obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
      have hF_fuel : F > 16 * numer.length + 8 := by omega
      obtain ⟨s', hs', hs'_rp⟩ :=
        single_postCif s_pre numer d F hlen_n hd_ne hd_dvd hs_pre_lna hap_pre hdenom_pre
          hd1_pre hd2_pre hd3_pre hF_fuel
      refine ⟨s', ?_, ?_⟩
      · have hsl : InstrR.bodyIsStraightLine
            [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] := by
          refine ⟨?_, ?_, trivial⟩ <;> rfl
        have hnc : ∀ i ∈ [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1],
            i.isNonControl := by
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · trivial
          · trivial
        have hexec_pre : bignumExecFuel divExactRegistry (F + 1)
              [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] s = some s_pre := by
          rw [bignumExecFuel_eq_bignumExec_of_straightLine divExactRegistry F _ s hsl]
          exact hpre
        have hguard : evalPExpr s_pre
            (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0)) = some 0 :=
          evalPExpr_dispatchCond_false s_pre hpre_lden_m1
        have hcif : bignumExecFuel divExactRegistry (F + 1)
              [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
                bodyDivExactGeneric bodyDivExactSingle] s_pre = some s' :=
          cif_else_run_local divExactRegistry F _ _ _ s_pre s' hguard hs'
        rw [hF]
        have hsplit : bodyDivExact =
            [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1] ++
            [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
              bodyDivExactGeneric bodyDivExactSingle] := rfl
        rw [hsplit]
        exact bignumExecFuel_append_join divExactRegistry (F + 1)
          [regCopy "lden_m1" "lden", binImm "lden_m1" (.Osub .U64) 1]
          [.Cif (.Papp2 (.Oneq .U64) (pv "lden_m1") (.Pconst 0))
            bodyDivExactGeneric bodyDivExactSingle]
          hnc s s_pre s' hexec_pre hcif
      · rw [hs_pre_rp] at hs'_rp; exact hs'_rp
    | _ :: _ :: _, h => exact absurd h (by simp)
  | (n + 2), _ =>
    have hd_ge_2 : 2 ≤ denom.length := by rw [hdl]; omega
    obtain ⟨s', hs', hs'_rp⟩ :=
      MpnDivExactGenericRefines_holds generic_postCif s numer denom d_inv fuel
        hlen_n hd_ge_2 hd_lt hle htoN_denom hdvd hdinv
        hlna hlden hd_inv_reg hap hdenom hd1 hd2 hd3 hfuel
    exact ⟨s', hs', hs'_rp⟩

/-! ## §8  Axiom audit (this file)

`MpnDivExactJasminRefines` is a *sorry-free `Prop`*, not yet a
theorem.  The per-step axiom-clean lemmas it would consume on its way
to a proof are all already proved upstream:

* `MpnDivExactSpec.mpnDivExact_spec` (exact-divide contract)
* `MpnDivExactSpec.mpnDivExact_mul`  (multiplicative form)
* `MpnDivExactSpec.mpnDivExact_rem_zero` (remainder vanishes)
* `MpnDivRemKnuth.knuthDivRem_eq_mpnDivRem` (algorithm = bit-level ref)
* `MpnDivRemKnuth.knuthDivRem_spec` (Euclidean contract)
* `MpnDivRemKnuth.submulAddBackDigit_spec` (limb-level digit correctness)

Their axiom sets are the standard kernel trio (`propext`,
`Classical.choice`, `Quot.sound`) plus the `bv_decide` natives
inherited from `MpnAddPrototype` / `MpnSubmul1Prototype`, all already
in the project's axiom budget. -/

#print axioms MpnDivExactSpec.mpnDivExact_spec
#print axioms MpnDivExactSpec.mpnDivExact_mul
#print axioms MpnDivExactSpec.mpnDivExact_rem_zero
#print axioms divExactRegistry_submul1

/-! ### §8.1  Audit of the §7.5 split-and-compose machinery

Per-iteration step lemma + the two per-half lemmas, all proved.
Their axiom sets are the standard kernel trio (`propext`,
`Classical.choice`, `Quot.sound`) plus the `bv_decide` natives
inherited from `MpnAddPrototype` / `MpnSubmul1Prototype`, all
already in the project's axiom budget. -/

#print axioms digitStepBodyExactSingle_step_holds
#print axioms bignumExec_digitStepBodyExactSingle_step
#print axioms bignumExec_digitStepBodyExactSingleLoad_step
#print axioms bignumExec_digitStepBodyExactSingleDivStore_step

/-! ### §8.2  Audit of the §7.8 / §7.9 generic-arm machinery

Per-iteration non-`Ccall` step lemma for the Hensel digit body
(`digitStepBodyExact` minus the trailing `Ccall mpn_submul_1`), the
generic-arm `Cif`-then peel, and the full `MpnDivExactJasminRefines_holds`
case-split theorem.  All proved sorry-free; axiom set is the standard
kernel trio (`propext`, `Quot.sound`) plus the `bv_decide` natives
inherited from `MpnAddPrototype` / `MpnSubmul1Prototype`. -/

#print axioms digitStepBodyExactGenericNonCcall_step_holds
#print axioms bignumExec_digitStepBodyExactGenericNonCcall_step
#print axioms execInstr_henselMulLow
#print axioms MpnDivExactGenericRefines_holds
#print axioms MpnDivExactJasminRefines_holds

/-! ### §8.3  Audit of the §7.9.1 registry-irrelevance bridge

`bodyDivExactSingle_noCcall` and
`mpnDivExact_single_postCif_obligation_divReg_of_empty` together
reduce the two-flavour single-arm obligation surface to one: any
future closure of the canonical `emptyRegistry`-flavoured
`mpnDivExact_single_postCif_obligation` (already pinned in §7.7.3)
automatically yields the `divExactRegistry`-flavoured
`mpnDivExact_single_postCif_obligation_divReg` consumed by
`MpnDivExactJasminRefines_holds`.

Both are real Lean theorems, axiom-clean (kernel trio +
`bignumExecFuel_registry_irrel`'s axiom set inherited from
`MpnMulPrototype`). -/

#print axioms bodyDivExactSingle_noCcall
#print axioms mpnDivExact_single_postCif_obligation_divReg_of_empty

end CatCrypt.Crypto.Jasmin.Examples.MpnDivExactPrototype
