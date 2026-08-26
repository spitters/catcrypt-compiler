/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Mpn.ShiftSpec
import CatCrypt.Crypto.Jasmin.JasminEmit

set_option autoImplicit false

/-!
# Jasmin emission prototype — `mpn_lshift` / `mpn_rshift` (bit-shift kernels)

**EXPERIMENTAL FILE.**  Lifts the verified algorithm-level shifts from
`Mpn.ShiftSpec.lean` (`mpnShiftLeft_spec` / `mpnShiftRight_spec`) into
Jasmin `FunDecl`s that emit real `.jazz` source via `emitFunDecl`.

This is the dual of `Mpn.AddPrototype.lean` for the shift kernels: the
limb-by-limb `Cwhile` loop with the cross-limb `SHLD_64` / `SHRD_64`
merge that exactly matches the disjoint-OR idiom proved correct in
`Mpn.ShiftSpec.bitShiftLeftAux_toNat` / `Mpn.ShiftSpec.bitShiftRight_toNat`.

## Scope: bit-only variant, `0 < k < 64`

GMP's `mpn_lshift(rp, sp, n, k)` accepts any `k`; the standard
decomposition splits `k = 64*q + r` and handles the whole-limb part
(`q` zero limbs prepended for lshift, `q` low limbs dropped for rshift)
separately from the cross-limb bit shift `r`.  The whole-limb part is
done by the *caller* (an `rp := sp + q` pointer adjustment plus zero
fill); this file emits the cross-limb bit shift, which is the part that
actually uses the new `#SHLD_64` / `#SHRD_64` intrinsics.

## What this file delivers

1. `mpnLShiftFd : FunDecl` — `mpn_lshift_bits(rp, sp, n, k)`.
2. `mpnRShiftFd : FunDecl` — `mpn_rshift_bits(rp, sp, n, k)`.
3. Both emit through `emitFunDecl` to syntactically-valid `.jazz`.
4. **Bridge statements** `MpnLShiftRefinesStmt` / `MpnRShiftRefinesStmt`,
   stated against `mpnShiftLeft` / `mpnShiftRight` from `MpnShiftSpec`.
   The full Cwhile loop-invariant proofs are pinned as `sorry`-free
   `Prop`-def residuals (`mpn_lshift_loop_obligation` /
   `mpn_rshift_loop_obligation`, with abbrevs `MpnLShiftJasminRefines` /
   `MpnRShiftJasminRefines`) — the `MpnPowJasminRefines` /
   `MpnAdd32JasminRefinesProp` pattern: NO new axioms in the TCB.  The
   immediate next step is to port the `MpnAddNJasminRefines` arc to the
   shift kernels (the memory algebra and Cwhile fuel rules are already
   shared).

The constant-time analysis (`isCT_Cmd`) is decidable on the body and
fully proved here.

## CT story (honest)

The `mpn_lshift` / `mpn_rshift` algorithms are constant-time at the
**algorithm level**: no data-dependent control flow (the loop count is
the public length `n`; the shift count `k` is the public bit count).

At the **microarchitecture level** the story depends on the shift form
`jasminc` selects:

* `SHL r/m64, cl`, `SHR r/m64, cl`, `SHLD r/m64, r64, cl`,
  `SHRD r/m64, r64, cl` — variable shift count from `CL`.  These are
  *constant-time on every modern x86 uarch*: Intel since Sandy Bridge
  (2011), AMD since Bulldozer (2011), Apple ARM since release.  Older
  uarchs had data-dependent latency on `cl` for some shift instructions,
  but those are outside the threat model of any current TLS / crypto
  deployment.

* `SHL r/m64, imm8`, `SHR r/m64, imm8`, `SHLD r/m64, r64, imm8`,
  `SHRD r/m64, r64, imm8` — immediate shift count.  *Constant-time on
  every uarch that implements them.*

* `SHLX r64, r/m64, r64`, `SHRX r64, r/m64, r64` (BMI2) — variable shift
  count from a GPR (not `CL`).  *Constant-time on every uarch that
  implements BMI2.*

The `k` shift amount in our `mpn_lshift_bits` is a public parameter
(the caller knows it, it's not a secret), so even on the (hypothetical)
uarchs with data-dependent variable shift latency the leak would be
public.  No CT obligation is violated.

This file is purely at the InstrR + emission level.  `MpnShiftSpec`
provides the limb-list algorithm correctness theorems; the emitted
`.jazz` is the immediate next layer.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.ShiftPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.Mpn.ShiftSpec
  (mpnShiftLeft mpnShiftRight bitShiftLeftAux bitShiftRight
   mpnShiftLeft_spec mpnShiftRight_spec)
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype (toNat)

/-! ## §1  Surface boilerplate -/

/-- `reg u64` variable. -/
private def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s`. -/
private def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- Memory load `x := [:u64 base + 0]`. -/
private def loadAt0 (x base : String) : InstrR :=
  .Cassgn (.Lvar { var := vr x }) .AT_none (.sword .U64)
    (.Pload .U64 { var := vr base } (.Pconst 0))

/-- Memory store `[:u64 base + 0] := src`. -/
private def storeAt0 (base src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := vr base } (.Pconst 0)) .AT_none (.sword .U64)
    (.Pvar { gv := { var := vr src }, gs := false })

/-- `r += k` / `r -= k` scalar update. -/
private def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- 6-LVal flag bundle `[of, cf, sf, pf, zf, dst]` (only dst captured) —
    the shape `jasminc` requires for `#SHL_64`/`#SHR_64`/`#SHLD_64`/
    `#SHRD_64` (verified by directly compiling
    `_, _, _, _, _, r = #SHLD_64(a, b, 4);` with `jasminc`). -/
private def shiftBundle (dst : String) : List LVal :=
  [.Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
   .Lnone {} (.sword .U64), .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
   .Lvar { var := vr dst }]

/-- `_, _, _, _, _, r = #SHLD_64(cur, prev, k);` —
    `r := (cur << k) | (prev >> (64 - k))`, the cross-limb left-merge
    matching `bitShiftLeftAux r prev'` where `prev' = prev >>> (64 - k)`. -/
private def shldCopn (dstName curName prevName kName : String) : InstrR :=
  .Copn (shiftBundle dstName) .AT_none (.Oasm ⟨"SHLD_64"⟩)
    [pv curName, pv prevName, pv kName]

/-- `_, _, _, _, _, r = #SHRD_64(cur, nextlow, k);` —
    `r := (cur >> k) | (nextlow << (64 - k))`, the cross-limb right-merge
    matching `bitShiftRight r (cur :: nextlow :: …)`. -/
private def shrdCopn (dstName curName nextlowName kName : String) : InstrR :=
  .Copn (shiftBundle dstName) .AT_none (.Oasm ⟨"SHRD_64"⟩)
    [pv curName, pv nextlowName, pv kName]

/-- `_, _, _, _, _, r = #SHL_64(a, k);` — single-precision left shift. -/
private def shlCopn (dstName aName kName : String) : InstrR :=
  .Copn (shiftBundle dstName) .AT_none (.Oasm ⟨"SHL_64"⟩)
    [pv aName, pv kName]

/-- `_, _, _, _, _, r = #SHR_64(a, k);` — single-precision right shift. -/
private def shrCopn (dstName aName kName : String) : InstrR :=
  .Copn (shiftBundle dstName) .AT_none (.Oasm ⟨"SHR_64"⟩)
    [pv aName, pv kName]

/-! ## §2  `mpn_lshift_bits(rp, sp, n, k)`: the cross-limb left-shift loop

The kernel walks `n` limbs little-endian, threading the *unshifted*
previous limb `prev` through the loop (initial value `0` — there is no
limb below the lowest).  Each iteration:

```
cur  := [:u64 sp + 0];
out  := #SHLD_64(cur, prev, k);    // (cur << k) | (prev >> (64-k))
[:u64 rp + 0] := out;
prev := cur;
sp   += 8; rp += 8; n -= 1;
```

After the loop, the final spill limb is `prev >> (64 - k)`, stored at
the n-th output slot (the caller provides `rp` with `n+1` capacity).
This matches `bitShiftLeftAux r 0 [w_0, w_1, …, w_{n-1}]` which
returns the `n+1` limbs `[w_0 << r, (w_1 << r) | (w_0 >> (64-r)), …,
w_{n-1} >> (64-r)]`. -/

/-- One left-shift loop iteration body (cross-limb merge via `SHLD_64`).

    Note on register allocation: jasminc's allocator forces the first
    input of `#SHLD_64` and the destination LVal to share a register
    (x86 `SHLD dst, src, count` is read-modify-write on `dst`).  We work
    around this by issuing the shift in-place (`out = cur; SHLD(out, prev,
    k)`) and using the saved original `cur` to update `prev` afterward —
    one extra `mov` per iteration, which the register allocator can
    often elide via copy propagation. -/
def lshiftLoopBody : List InstrR :=
  [ loadAt0 "cur" "sp"
  , .Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur")
  , shldCopn "out" "out" "prev" "k"
  , storeAt0 "rp" "out"
  , .Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (pv "cur")
  , binImm "sp" (.Oadd .U64) 8
  , binImm "rp" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_lshift_bits`:

```
prev := 0;
while (n != 0) { <lshiftLoopBody> }
// Final spill: rewrite k as `64 - k` (the cl-shift register is freed
// once the loop exits — `k` is no longer needed for SHLD), then
// SHR(prev, k) computes prev >> (64 - original_k) = the high spill.
k := 64;
k := k - k_orig;     // tracked as: replace k with (64 - k)
spill := #SHR_64(prev, k);
[:u64 rp + 0] := spill;
```

x86 variable shifts (`SHL`/`SHR` with `cl`) take the shift count in
RCX/CL.  Both the loop's `SHLD_64(_, _, k)` and the final
`SHR_64(prev, ?)` need their count in `cl`, so we MUST reuse the same
variable (jasminc's register allocator rejects two live shift counts).
We rewrite `k` to `64 - k` after the loop — the original `k` is dead by
then.  Done as `tmp := 64; tmp := tmp - k; … = #SHR_64(prev, tmp)`. -/
def lshiftBody : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) lshiftLoopBody
  -- After the loop, repurpose `k` to `64 - k` for the final spill shift
  -- IN-PLACE.  `k` is dead after the loop, so we can overwrite it; this
  -- avoids a register-allocation conflict between two simultaneously-live
  -- shift counts (both wanting to be in `cl`).
  -- Step 1: load 64 into a fresh tmp `kbar`.
  , .Cassgn (.Lvar { var := vr "kbar" }) .AT_none (.sword .U64) (.Pconst 64)
  -- Step 2: `kbar := kbar - k`.  After this, `k` is dead.
  , .Cassgn (.Lvar { var := vr "kbar" }) .AT_none (.sword .U64)
      (.Papp2 (.Osub .U64) (pv "kbar") (pv "k"))
  -- Step 3: copy kbar back into k (so the final shift uses `k`, which
  -- was already allocated to `cl` by the loop's SHLD).  Now kbar is
  -- dead and only k is live.
  , .Cassgn (.Lvar { var := vr "k" }) .AT_none (.sword .U64) (pv "kbar")
  , shrCopn "spill" "prev" "k"
  , storeAt0 "rp" "spill" ]

/-- `mpn_lshift_bits(rp, sp, n, k)` as a Jasmin `FunDecl`.
    SysV ABI `rdi=rp, rsi=sp, rdx=n, rcx=k`.  The bit-spill shift count
    `64 - k` is computed in-function. -/
def mpnLShiftFd : FunDecl where
  name := { name := "mpn_lshift_bits" }
  params := [⟨{ var := vr "rp" }⟩, ⟨{ var := vr "sp" }⟩,
             ⟨{ var := vr "n" }⟩, ⟨{ var := vr "k" }⟩]
  body := lshiftBody
  results := []   -- void: result is via *rp; n+1 limbs written

/-- **CT status (honest).**  `isCT_Cmd lshiftBody` evaluates to `false`
    under the *current* project CT whitelist: `ct_intrinsic` rejects
    `SHL_64` / `SHR_64` / `SHLD_64` / `SHRD_64` deliberately, because
    the variable-count form leaks timing on (historic) uarchs when the
    shift count is a *secret*.  In our kernels the count `k` is a
    *public* bit-shift amount (the caller's argument), so the leak is
    public and no CT obligation is violated.

    Policy decision (documented in JasminCT.lean `ct_intrinsic` docstring):
    leave the shift opcodes off the whitelist by default; protocol-level
    code that uses `mpn_lshift_bits` must justify the shift-count
    publicness on its own.  See §0 docstring "CT story" for the per-uarch
    behaviour. -/
example : isCT_Cmd lshiftBody = false := by decide

/-- Emit the real `.jazz` source. -/
def lshiftEmitted : Option String := emitFunDecl mpnLShiftFd

/-- Emission succeeds (every InstrR shape is supported). -/
example : lshiftEmitted.isSome = true := by native_decide

/-! ## §3  `mpn_rshift_bits(rp, sp, n, k)`: the cross-limb right-shift loop

The kernel walks `n` limbs little-endian, looking *one limb ahead* for
the next-limb cross-merge.  Each iteration:

```
cur  := [:u64 sp + 0];
next := [:u64 sp + 8];        // peek the next limb
out  := #SHRD_64(cur, next, k);  // (cur >> k) | (next << (64-k))
[:u64 rp + 0] := out;
sp += 8; rp += 8; n -= 1;
```

The final iteration's `next` reads off the end of `sp` — the kernel
either expects the caller to provide an extra zero limb at `sp[n]` or
handles the last iteration specially (with `#SHR_64(cur, k)`).  The
clean variant emits a single `n-1` loop plus a final `#SHR_64` for the
top limb. -/

/-- One right-shift loop iteration body (cross-limb merge via `SHRD_64`,
    looking ahead one limb).  Reads `cur` from `sp+0` and the next-limb
    `next` from `sp+8`. -/
def rshiftLoopBody : List InstrR :=
  [ loadAt0 "cur" "sp"
  , .Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
      (.Pload .U64 { var := vr "sp" } (.Pconst 8))
  , shrdCopn "out" "cur" "next" "k"
  , storeAt0 "rp" "out"
  , binImm "sp" (.Oadd .U64) 8
  , binImm "rp" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_rshift_bits`:

```
while (n != 0) { <rshiftLoopBody> }
// last limb: no cross-merge, just shift down
top := [:u64 sp + 0];
spill := #SHR_64(top, k);
[:u64 rp + 0] := spill;
```

The caller passes `n` = (limb count - 1) so the loop processes all but
the topmost limb; the topmost limb is handled by the post-loop
`#SHR_64`. -/
def rshiftBody : List InstrR :=
  [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) rshiftLoopBody
  , loadAt0 "top" "sp"
  , shrCopn "spill" "top" "k"
  , storeAt0 "rp" "spill" ]

/-- `mpn_rshift_bits(rp, sp, n, k)` as a Jasmin `FunDecl`.
    SysV ABI `rdi=rp, rsi=sp, rdx=n, rcx=k`.  Caller convention: `n` is
    *limb count minus one* (the loop processes all but the top); the top
    limb is shifted down by `k` with `#SHR_64` after the loop. -/
def mpnRShiftFd : FunDecl where
  name := { name := "mpn_rshift_bits" }
  params := [⟨{ var := vr "rp" }⟩, ⟨{ var := vr "sp" }⟩,
             ⟨{ var := vr "n" }⟩, ⟨{ var := vr "k" }⟩]
  body := rshiftBody
  results := []

/-- **CT status (honest).**  Same as `lshiftBody` — see that example for
    the policy rationale.  Variable-count shifts are off the CT
    whitelist by convention; protocol-level use of `mpn_rshift_bits`
    must justify shift-count publicness. -/
example : isCT_Cmd rshiftBody = false := by decide

/-- Emit the real `.jazz` source. -/
def rshiftEmitted : Option String := emitFunDecl mpnRShiftFd

/-- Emission succeeds. -/
example : rshiftEmitted.isSome = true := by native_decide

/-! ## §4  Bridge statements (residual, sorry-free)

The bridge connecting the emitted Jasmin `Cwhile` loop to the verified
`mpnShiftLeft` / `mpnShiftRight` references is the immediate-next-step
analogue of `MpnAddNJasminRefines` (~1100 lines in
`Mpn.AddPrototype.lean`).  It needs:

* per-iteration step lemmas threading the unshifted-previous register
  `prev` across the Cwhile back-edge (analogue of `chunkLoad_step` /
  `chunkAdc_step` from `MpnAddPrototype`),
* the `memHoldsLimbs` framing on the output region (`load64Mem_store64_*`
  is already shared),
* the final-spill post-loop limb (a single straight-line `#SHR_64` +
  `Lmem` write, analogue of the `cf := 0; …; return cf` peeling).

We state the bridges below as sorry-free `Prop`-def residuals
(`mpn_lshift_loop_obligation` / `mpn_rshift_loop_obligation`), with
abbreviations `MpnLShiftJasminRefines` / `MpnRShiftJasminRefines`
pointing to them. This is the `MpnPowJasminRefines` /
`MpnAdd32JasminRefinesProp` pattern: the obligation is named as a
`Prop`, **NOT** declared as an `axiom`, so downstream code that uses
the bridge is hypothesis-dependent. Closing the inductive proof later
turns the `abbrev` into a proved `theorem` — same shape, no TCB
delta. -/

open MemoryModel

/-- Predicate: memory `m` holds the limb list `ws` little-endian starting
    at byte address `base`.  Direct reuse of `Mpn.AddPrototype.memHoldsLimbs`. -/
def memHoldsLimbs (m : Mem) (base : UInt64) : List (BitVec 64) → Prop
  | []      => True
  | w :: ws =>
      load64Mem m base = some (UInt64.ofNat w.toNat) ∧
      memHoldsLimbs m (base + 8) ws

/-- **Bridge statement — `mpn_lshift_bits`.**  From a state holding the
    limb list `as` at `sp`, with `n = |as|`, `0 < k < 64`, and the `rp`
    output region (of capacity `|as|+1` limbs) disjoint from the `sp`
    input region, running `lshiftBody` lands in a state whose memory at
    `rp` holds `mpnShiftLeft as k`.  The bit-spill shift count `64 - k`
    is computed in-function from `k`. -/
def MpnLShiftRefinesStmt : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (k : Nat) (fuel : Nat),
    0 < k → k < 64 →
    s.regs "n"    = BitVec.ofNat 64 as.length →
    s.regs "k"    = BitVec.ofNat 64 k →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "sp").toNat) as →
    MemoryModel.Disjoint
      (range (UInt64.ofNat (s.regs "rp").toNat) (8 * (as.length + 1)))
      (range (UInt64.ofNat (s.regs "sp").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 4 →
    ∃ s', bignumExecFuel emptyRegistry fuel lshiftBody s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (mpnShiftLeft as k)

/-- **Bridge statement — `mpn_rshift_bits`.**  From a state holding the
    limb list `as` at `sp` (with `|as| ≥ 1`), `n = |as|-1`, `0 < k < 64`,
    and the `rp` output region disjoint from the `sp` input region,
    running `rshiftBody` lands in a state whose memory at `rp` holds
    `mpnShiftRight as k` (a list of length `|as|`, since the bit-shift
    direction does not change the limb count for `k < 64`). -/
def MpnRShiftRefinesStmt : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (k : Nat) (fuel : Nat),
    0 < k → k < 64 →
    as.length ≥ 1 →
    s.regs "n" = BitVec.ofNat 64 (as.length - 1) →
    s.regs "k" = BitVec.ofNat 64 k →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "sp").toNat) as →
    MemoryModel.Disjoint
      (range (UInt64.ofNat (s.regs "rp").toNat) (8 * as.length))
      (range (UInt64.ofNat (s.regs "sp").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 4 →
    ∃ s', bignumExecFuel emptyRegistry fuel rshiftBody s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (mpnShiftRight as k)

/-! ### §4a  Tighter residuals — moving the obligation one structural step inward

The original residual was the full bridge `MpnLShiftRefinesStmt` /
`MpnRShiftRefinesStmt` (prelude + Cwhile + spill tail).  We tighten it
by separating the bare Cwhile loop-invariant (the `mpnAddN_loop`-shaped
limb-list induction) from the surrounding straight-line wiring.

The `MpnAddPrototype` / `MpnAddNAdcSpillPrototype` proof pattern has two
load-bearing layers:

* **Outer**: the prelude (`prev := 0` for lshift) and post-loop tail
  (`k := 64 - k; spill := SHR(prev, k); rp[n] := spill` for lshift; the
  `top := sp[0]; spill := SHR(top, k); rp[0] := spill` for rshift)
  are *straight-line* assembly.  Closing them requires only `execInstr`
  unfolding + the memory algebra already proved in
  `Mpn.AddPrototype.load64Mem_store64_{same,disjoint}`.

* **Inner**: the `Cwhile` loop-invariant over the limb list — a
  structural induction analogue of `Mpn.AddPrototype.mpnAddN_loop` /
  `Mpn.AddNAdcSpillPrototype.mpnAddN_spillLoop`.

We **tighten** the residual to just the inner layer.  The outer layer is
deferred (it's just as much work as the inner, and the inner is more
generally reusable for U32 shifts and other Cwhile-on-byte-memory kernels).

The tighter `Prop`-defs `LShiftLoopOblg` / `RShiftLoopOblg` below capture
the per-call inductive invariant: register `prev` (lshift) or `sp/rp`
advance state (rshift) threaded across iterations.  Each is strictly
weaker than the corresponding full bridge statement (no prelude, no
spill tail), so it is a tighter residual. -/

/-- **Tighter residual for `mpn_lshift_bits`.**  The bare `Cwhile`
    loop-invariant: from a state with register `prev` holding the
    unshifted previous limb (or `0` for the first iteration), `n = |as|`,
    `k = k`, and `sp` holding `as` little-endian, the body
    `Cwhile (n != 0) lshiftLoopBody` writes the per-iteration cross-limb
    merges into `rp` and updates `prev := last as` and `rp` / `sp` / `n`.

    Specifically, after the loop:
    * `rp` holds the first `|as|` limbs of
      `bitShiftLeftAux k (prev_reg >>> (64 - k)) as` (the trailing spill
      is the post-loop tail's job — not the loop's).
    * register `prev` holds `as.getLastD prev_reg` (so a subsequent
      `prev >>> (64 - k)` gives the trailing spill limb).
    * registers `k`, `rp` (advanced), `sp` (advanced) all match what the
      assembled bridge expects.

    Stated forward (success ⇒ success).  Discharging this is the
    `Mpn.AddPrototype.mpnAddN_loop`-shaped induction on `as`. -/
def LShiftLoopOblg : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (k : Nat) (prev_reg : BitVec 64)
      (extra : Nat),
    0 < k → k < 64 →
    s.regs "prev" = prev_reg →
    s.regs "n"    = BitVec.ofNat 64 as.length →
    s.regs "k"    = BitVec.ofNat 64 k →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "sp").toNat) as →
    MemoryModel.Disjoint
      (range (UInt64.ofNat (s.regs "rp").toNat) (8 * as.length))
      (range (UInt64.ofNat (s.regs "sp").toNat) (8 * as.length)) →
    ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) lshiftLoopBody] s
              = some s' ∧
      -- The first `|as|` limbs of `bitShiftLeftAux k (prev_reg >>> (64-k)) as`
      -- have been written to the output region starting at the ORIGINAL `rp`.
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        ((bitShiftLeftAux k (prev_reg >>> (64 - k)) as).take as.length) ∧
      -- After the loop, `rp` points at `original rp + 8*|as|`
      -- (the slot for the trailing spill limb).
      s'.regs "rp" = s.regs "rp" + BitVec.ofNat 64 (8 * as.length) ∧
      -- After the loop, register `prev` holds `last as` (or `prev_reg` if empty).
      s'.regs "prev" = as.foldl (fun _ w => w) prev_reg ∧
      -- `k` register is preserved (SHLD reads, does not write).
      s'.regs "k"    = BitVec.ofNat 64 k ∧
      -- Memory is preserved on every 8-byte block outside the written prefix
      -- (needed so the post-loop SHR-spill's store doesn't collide).
      (∀ b, MemoryModel.Disjoint (range b 8)
          (range (UInt64.ofNat (s.regs "rp").toNat) (8 * as.length)) →
        load64Mem s'.mem b = load64Mem s.mem b)

/-- **Tighter residual for `mpn_rshift_bits`.**  The bare `Cwhile`
    loop-invariant: with `as = a₀ :: rest` (the top limb is handled by the
    post-loop tail), `n = |as| - 1`, and `sp` holding `as` little-endian,
    the body `Cwhile (n != 0) rshiftLoopBody` writes the first `|as| - 1`
    cross-limb-merge limbs of `bitShiftRight k as` into `rp`.

    After the loop:
    * `rp` (offsets `0..|as|-2`) holds `(bitShiftRight k as).take (|as|-1)`.
    * `sp` has advanced by `8·(|as|-1)` (so it now points at the top limb).
    * `k` register is preserved.
    * memory is preserved on every 8-byte block disjoint from the written
      prefix (needed so the post-loop `SHR(top, k)` still sees the top
      limb in memory).

    Stated forward (success ⇒ success).  Discharging this is the
    `Mpn.AddPrototype.mpnAddN_loop`-shaped induction on `as.tail`. -/
def RShiftLoopOblg : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (k : Nat) (extra : Nat),
    0 < k → k < 64 →
    as.length ≥ 1 →
    s.regs "n" = BitVec.ofNat 64 (as.length - 1) →
    s.regs "k" = BitVec.ofNat 64 k →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "sp").toNat) as →
    MemoryModel.Disjoint
      (range (UInt64.ofNat (s.regs "rp").toNat) (8 * as.length))
      (range (UInt64.ofNat (s.regs "sp").toNat) (8 * as.length)) →
    ∃ s', bignumExecFuel emptyRegistry (2 * (as.length - 1) + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) rshiftLoopBody] s
              = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        ((bitShiftRight k as).take (as.length - 1)) ∧
      s'.regs "sp" = s.regs "sp" + BitVec.ofNat 64 (8 * (as.length - 1)) ∧
      s'.regs "rp" = s.regs "rp" + BitVec.ofNat 64 (8 * (as.length - 1)) ∧
      s'.regs "k"  = BitVec.ofNat 64 k ∧
      -- Memory is preserved on every 8-byte block outside the written
      -- output region.  Mirrors lshift's frame (disjoint from `rp`, which
      -- is the write area; reads happen at `sp` and aren't disturbed by
      -- a `rp`-write since `rp ⊥ sp` by `hdo`).  Used by the post-loop
      -- spill tail to chain "the top limb at `sp + 8·(|as|-1)` was not
      -- overwritten by the loop" through `rp ⊥ sp`.
      (∀ b, MemoryModel.Disjoint (range b 8)
          (range (UInt64.ofNat (s.regs "rp").toNat) (8 * as.length)) →
        load64Mem s'.mem b = load64Mem s.mem b)

/-- Tightened obligation: the `mpn_lshift_bits` bridge residual has been
    narrowed from the full bridge `MpnLShiftRefinesStmt` (prelude +
    Cwhile + spill tail) to the loop-only `LShiftLoopOblg` (the
    `mpnAddN_loop`-shaped limb-list induction).  The straight-line
    prelude (`prev := 0`) and spill tail (`kbar; k := 64-k; SHR(prev, k);
    rp[n] := spill`) are pinned separately as `lshift_bridge_reduction`
    (the reduction Prop `LShiftLoopOblg → MpnLShiftRefinesStmt`).
    Together — closing `LShiftLoopOblg` and `lshift_bridge_reduction` —
    discharges the bridge unconditionally. -/
def mpn_lshift_loop_obligation : Prop := LShiftLoopOblg

/-- Tightened obligation for `mpn_rshift_bits`.  Symmetric to lshift,
    with no prelude (rshift's `prev` initialization is implicit in the
    looking-one-ahead body shape). -/
def mpn_rshift_loop_obligation : Prop := RShiftLoopOblg

/-- **Bridge — `mpn_lshift_bits` refines `mpnShiftLeft` for `0 < k < 64`.**
    Tightened residual: the bridge is the loop-only `LShiftLoopOblg`
    (down from the original full bridge `MpnLShiftRefinesStmt`).
    Closing `LShiftLoopOblg` and the reduction `lshift_bridge_reduction`
    turns this into a proved theorem of `MpnLShiftRefinesStmt`. -/
abbrev MpnLShiftJasminRefines : Prop := mpn_lshift_loop_obligation

/-- **Bridge — `mpn_rshift_bits` refines `mpnShiftRight` for `0 < k < 64`.**
    Mirror of `MpnLShiftJasminRefines`. -/
abbrev MpnRShiftJasminRefines : Prop := mpn_rshift_loop_obligation

/-! ### §4b  Reduction Prop-defs — loop obligation ⇒ full bridge

The two `Prop`-defs below state: assuming the tightened loop-only
residual (`LShiftLoopOblg` / `RShiftLoopOblg`), the full bridge
(`MpnLShiftRefinesStmt` / `MpnRShiftRefinesStmt`) follows.  Together
with the loop-only obligations, these completely characterize the
remaining proof work needed to close the bridge unconditionally:

* `LShiftLoopOblg` + `lshift_bridge_reduction` ⇒ `MpnLShiftRefinesStmt`.
* `RShiftLoopOblg` + `rshift_bridge_reduction` ⇒ `MpnRShiftRefinesStmt`.

Closing `lshift_bridge_reduction` (a straight-line argument, no
induction) involves:

* the `prev := 0` prelude (lshift) — one `execInstr` step.
* the post-loop tail `kbar := 64; kbar := kbar - k; k := kbar; SHR(prev, k);
  rp[0] := spill` (lshift) — five `execInstr` steps, none control-flow.
* the analogous post-loop tail `top := sp[0]; spill := SHR(top, k); rp[0] := spill`
  (rshift).
* the framing arguments threading `memHoldsLimbs` across the post-loop
  store(s), using `Mpn.AddPrototype.load64Mem_store64_{same,disjoint}`.

Closing `LShiftLoopOblg` / `RShiftLoopOblg` is the limb-list structural
induction (`mpnAddN_loop`-shaped) — the inner inductive core. -/

/-- Tighter Prop residual: the lshift bridge reduces to the loop-only
    obligation.  Closing this is the post-loop-tail bridging argument
    (straight-line, no induction). -/
def lshift_bridge_reduction : Prop :=
  LShiftLoopOblg → MpnLShiftRefinesStmt

/-- Tighter Prop residual: the rshift bridge reduces to the loop-only
    obligation. -/
def rshift_bridge_reduction : Prop :=
  RShiftLoopOblg → MpnRShiftRefinesStmt

/-! ### §4c  Discharge of the `mpn_lshift_bits` loop residual

We prove `LShiftLoopOblg` and `lshift_bridge_reduction` unconditionally,
mirroring the `Mpn.AddNAdcSpillPrototype.mpnAddN_spillLoop` /
`MpnAddNJasminRefines` discharge.  The threaded register is `prev` (the
unshifted previous limb), updated by the loop body's
`prev := cur` after each iteration.  The cross-limb merge
`shld64 cur prev k = (cur <<< k) ||| (prev >>> (64 - k))` (per
`BignumExec.shld64`) is exactly the per-limb shape emitted by
`Mpn.ShiftSpec.bitShiftLeftAux`.

The proof structure mirrors `Mpn.AddPrototype.mpnAddN_loop`:

* a per-iteration step lemma `bignumExec_lshiftLoopBody_step` reducing
  one body run to an explicit state update (one store at `rp + 0`, regs
  `cur := a`, `out := (a <<< k) ||| (prev_old >>> (64-k))`, `prev := a`,
  `rp += 8`, `sp += 8`, `n -= 1`);
* induction over the limb list using the §8/§9 Cwhile fuel rules
  (`bignumExecFuel_loop_step` / `bignumExecFuel_loop_exit`) and the
  memory-frame algebra
  (`memHoldsLimbs_store64_frame`, `load64Mem_store64_{same,disjoint}`).
-/

open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype (regAddr setReg_mem setReg_regs storeMem_mem
  storeMem_regs resolveAddr_reg regAddr_advance bv_uint_roundtrip
  load64Mem_store64_same
  load64Mem_store64_disjoint range_shift_subset range_head_subset
  disjoint_mono range_op_head_tail_disjoint disjoint_range_lt
  ofNat64_succ_ne_zero ofNat64_succ_sub_one
  evalPExpr_loopCond_true evalPExpr_loopCond_false
  bignumExecFuel_loop_step bignumExecFuel_loop_exit)

/-- Local inline of `Mpn.AddNAdcSpillPrototype.bignumExec_append_some_local`
    (avoids importing the spill file).  Composing two successful runs gives
    a successful run of the concatenation. -/
theorem bignumExec_append_some_local
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

/-- The local `memHoldsLimbs` (defined inside this file in §4) coincides
    with `Mpn.AddPrototype.memHoldsLimbs`: identical structural definitions. -/
theorem memHoldsLimbs_eq (m : MemoryModel.Mem) (base : UInt64)
    (ws : List (BitVec 64)) :
    memHoldsLimbs m base ws ↔ Mpn.AddPrototype.memHoldsLimbs m base ws := by
  induction ws generalizing base with
  | nil => simp [memHoldsLimbs, Mpn.AddPrototype.memHoldsLimbs]
  | cons w ws ih =>
    simp only [memHoldsLimbs, Mpn.AddPrototype.memHoldsLimbs]
    exact and_congr_right (fun _ => ih (base + 8))

/-- Frame the local `memHoldsLimbs` across a `store64` to a disjoint block. -/
theorem memHoldsLimbs_store64_frame (m : MemoryModel.Mem) (base st : UInt64)
    (v : UInt64) (ws : List (BitVec 64))
    (hdisj : MemoryModel.Disjoint (range st 8) (range base (8 * ws.length)))
    (hmem : memHoldsLimbs m base ws) :
    memHoldsLimbs (m.store64 st v) base ws := by
  rw [memHoldsLimbs_eq] at hmem ⊢
  exact Mpn.AddPrototype.memHoldsLimbs_store64_frame m base st v ws hdisj hmem

/-! #### Per-instruction effects (lshift loop body) -/

/-- Effect of one `loadAt0 x base` instruction.  Copied from the
    `Mpn.AddNAdcSpillPrototype.execInstr_loadAt0` proof. -/
theorem execInstr_loadAt0_lshift (s : BignumState) (x base : String) (v : BitVec 64)
    (hv : load64Mem s.mem (UInt64.ofNat (s.regs base).toNat)
            = some (UInt64.ofNat v.toNat)) :
    execInstr s (loadAt0 x base) = some (setReg s x v) := by
  simp only [loadAt0, execInstr, evalPExpr, pv, vr,
             resolveAddr, Option.bind_some, bind, Option.bind,
             show BitVec.ofInt 64 0 = 0 from rfl]
  rw [show s.regs base + 0 = s.regs base from by bv_decide, hv]
  simp only [bv_uint_roundtrip, bind, Option.bind, Option.bind_some]

/-- Effect of the SHLD intrinsic: `out := (cur <<< k%64) ||| (prev >>> (64 - k%64))`. -/
theorem execInstr_shldCopn (s : BignumState) :
    execInstr s (shldCopn "out" "out" "prev" "k") = some
      (setReg s "out" (shld64 (s.regs "out") (s.regs "prev") (s.regs "k"))) := by
  simp only [shldCopn, shiftBundle, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind, writeShiftBundle]

/-- Effect of the SHR intrinsic: `spill := (prev >>> (k%64))`. -/
theorem execInstr_shrCopn (s : BignumState) (dst src kname : String) :
    execInstr s (shrCopn dst src kname) = some
      (setReg s dst (shr64 (s.regs src) (s.regs kname))) := by
  simp only [shrCopn, shiftBundle, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind, writeShiftBundle]

/-- Effect of `[base + 0] := src`. -/
theorem execInstr_storeAt0_lshift (s : BignumState) (base src : String) :
    execInstr s (storeAt0 base src) = some
      (storeMem s (UInt64.ofNat (s.regs base).toNat)
        (UInt64.ofNat (s.regs src).toNat)) := by
  simp only [storeAt0, execInstr, evalPExpr, pv, vr,
             resolveAddr, Option.bind_some, bind, Option.bind,
             show BitVec.ofInt 64 0 = 0 from rfl]
  rw [show s.regs base + 0 = s.regs base from by bv_decide]

/-- Effect of `r := r + k` (or `r := r - k`). -/
theorem execInstr_binImm_add (s : BignumState) (r : String) (k : Int) :
    execInstr s (binImm r (.Oadd .U64) k) = some
      (setReg s r (s.regs r + BitVec.ofInt 64 k)) := by
  simp only [binImm, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind]

theorem execInstr_binImm_sub (s : BignumState) (r : String) (k : Int) :
    execInstr s (binImm r (.Osub .U64) k) = some
      (setReg s r (s.regs r - BitVec.ofInt 64 k)) := by
  simp only [binImm, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind]

/-- Effect of `dst := pv src` (a register-to-register copy via Cassgn). -/
theorem execInstr_regCopy (s : BignumState) (dst src : String) :
    execInstr s (.Cassgn (.Lvar { var := vr dst }) .AT_none (.sword .U64)
                  (pv src)) = some (setReg s dst (s.regs src)) := by
  simp only [execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind]

/-- Effect of `dst := Pconst c`. -/
theorem execInstr_constAssign (s : BignumState) (dst : String) (c : Int) :
    execInstr s (.Cassgn (.Lvar { var := vr dst }) .AT_none (.sword .U64)
                  (.Pconst c)) = some (setReg s dst (BitVec.ofInt 64 c)) := by
  simp only [execInstr, evalPExpr, vr,
             Option.bind_some, bind, Option.bind]

/-! #### One iteration of `lshiftLoopBody` -/

/-- One iteration of `lshiftLoopBody`: given memory holds limb `a` at
    `sp + 0` and `prev` register holds `prev_reg`, the body lands in a
    state with:
    * `sp += 8`, `rp += 8`, `n -= 1` (pointer/counter advances),
    * `prev := a` (the loaded limb is the next iteration's prev),
    * `out` := `shld64 a prev_reg (s.regs "k")`,
    * `cur := a`,
    * memory at `rp + 0` holds the merge `shld64 a prev_reg k`. -/
theorem bignumExec_lshiftLoopBody_step (s : BignumState) (a : BitVec 64)
    (ha : load64Mem s.mem (regAddr s "sp") = some (UInt64.ofNat a.toNat)) :
    ∃ s', bignumExec lshiftLoopBody s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "rp")
        (UInt64.ofNat (shld64 a (s.regs "prev") (s.regs "k")).toNat) ∧
      s'.regs "prev" = a ∧
      s'.regs "k"    = s.regs "k" ∧
      s'.regs "sp"   = s.regs "sp" + 8 ∧
      s'.regs "rp"   = s.regs "rp" + 8 ∧
      s'.regs "n"    = s.regs "n" - 1 := by
  -- Step through the 8 instructions.
  -- 1. cur := [sp + 0]   →  setReg s "cur" a
  have h1 : execInstr s (loadAt0 "cur" "sp") = some (setReg s "cur" a) :=
    execInstr_loadAt0_lshift s "cur" "sp" a ha
  set s1 : BignumState := setReg s "cur" a with hs1
  -- 2. out := cur         →  setReg s1 "out" (s1.regs "cur") = setReg s1 "out" a
  have hs1_cur : s1.regs "cur" = a := by simp [hs1, setReg]
  have h2 : execInstr s1 (.Cassgn (.Lvar { var := vr "out" }) .AT_none
              (.sword .U64) (pv "cur")) =
            some (setReg s1 "out" a) := by
    rw [execInstr_regCopy, hs1_cur]
  set s2 : BignumState := setReg s1 "out" a with hs2
  -- 3. out := SHLD_64(out, prev, k)
  have hs2_out : s2.regs "out" = a := by simp [hs2, setReg]
  have hs2_prev : s2.regs "prev" = s.regs "prev" := by
    simp [hs2, hs1, setReg]
  have hs2_k : s2.regs "k" = s.regs "k" := by
    simp [hs2, hs1, setReg]
  have h3 : execInstr s2 (shldCopn "out" "out" "prev" "k") =
            some (setReg s2 "out" (shld64 a (s.regs "prev") (s.regs "k"))) := by
    rw [execInstr_shldCopn, hs2_out, hs2_prev, hs2_k]
  set s3 : BignumState := setReg s2 "out" (shld64 a (s.regs "prev") (s.regs "k"))
    with hs3
  -- 4. [rp + 0] := out
  have hs3_out : s3.regs "out" = shld64 a (s.regs "prev") (s.regs "k") := by
    simp [hs3, setReg]
  have hs3_rp : s3.regs "rp" = s.regs "rp" := by
    simp [hs3, hs2, hs1, setReg]
  have hs3_mem : s3.mem = s.mem := by
    simp [hs3, hs2, hs1, setReg]
  have h4 : execInstr s3 (storeAt0 "rp" "out") = some
              (storeMem s3 (UInt64.ofNat (s3.regs "rp").toNat)
                (UInt64.ofNat (s3.regs "out").toNat)) :=
    execInstr_storeAt0_lshift s3 "rp" "out"
  set s4 : BignumState := storeMem s3 (UInt64.ofNat (s3.regs "rp").toNat)
            (UInt64.ofNat (s3.regs "out").toNat) with hs4
  -- 5. prev := cur (i.e., prev := a, via Cassgn on Pvar "cur")
  have hs4_cur : s4.regs "cur" = a := by
    show (storeMem s3 _ _).regs "cur" = a
    simp only [storeMem_regs]
    simp [hs3, hs2, hs1, setReg, hs1_cur]
  have h5 : execInstr s4 (.Cassgn (.Lvar { var := vr "prev" }) .AT_none
              (.sword .U64) (pv "cur")) =
            some (setReg s4 "prev" a) := by
    rw [execInstr_regCopy, hs4_cur]
  set s5 : BignumState := setReg s4 "prev" a with hs5
  -- 6. sp += 8
  have hs5_sp : s5.regs "sp" = s.regs "sp" := by
    simp only [hs5, setReg]
    show (storeMem s3 _ _).regs "sp" = s.regs "sp"
    simp only [storeMem_regs]
    simp [hs3, hs2, hs1, setReg]
  have h6 : execInstr s5 (binImm "sp" (.Oadd .U64) 8) =
              some (setReg s5 "sp" (s5.regs "sp" + BitVec.ofInt 64 8)) :=
    execInstr_binImm_add s5 "sp" 8
  set s6 : BignumState := setReg s5 "sp" (s5.regs "sp" + BitVec.ofInt 64 8)
    with hs6
  -- 7. rp += 8
  have hs6_rp : s6.regs "rp" = s.regs "rp" := by
    simp only [hs6, setReg]
    show (setReg s4 "prev" a).regs "rp" = s.regs "rp"
    simp only [setReg]
    show (storeMem s3 _ _).regs "rp" = s.regs "rp"
    simp only [storeMem_regs]
    exact hs3_rp
  have h7 : execInstr s6 (binImm "rp" (.Oadd .U64) 8) =
              some (setReg s6 "rp" (s6.regs "rp" + BitVec.ofInt 64 8)) :=
    execInstr_binImm_add s6 "rp" 8
  set s7 : BignumState := setReg s6 "rp" (s6.regs "rp" + BitVec.ofInt 64 8)
    with hs7
  -- 8. n -= 1
  have h8 : execInstr s7 (binImm "n" (.Osub .U64) 1) =
              some (setReg s7 "n" (s7.regs "n" - BitVec.ofInt 64 1)) :=
    execInstr_binImm_sub s7 "n" 1
  set s8 : BignumState := setReg s7 "n" (s7.regs "n" - BitVec.ofInt 64 1) with hs8
  -- Compose.
  have step (i : InstrR) (s' s'' : BignumState)
      (hi : execInstr s' i = some s'') :
      bignumExec [i] s' = some s'' := by
    simp only [bignumExec, hi]
  have e12 : bignumExec ([loadAt0 "cur" "sp"] ++
              [.Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur")]) s
                = some s2 := bignumExec_append_some_local _ _ s s1 s2 (step _ _ _ h1) (step _ _ _ h2)
  have e123 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur")] ++
              [shldCopn "out" "out" "prev" "k"]) s = some s3 :=
    bignumExec_append_some_local _ _ s s2 s3 e12 (step _ _ _ h3)
  have e1234 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur"),
              shldCopn "out" "out" "prev" "k"] ++ [storeAt0 "rp" "out"]) s = some s4 :=
    bignumExec_append_some_local _ _ s s3 s4 e123 (step _ _ _ h4)
  have e12345 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur"),
              shldCopn "out" "out" "prev" "k", storeAt0 "rp" "out"]
              ++ [.Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (pv "cur")]) s
                = some s5 :=
    bignumExec_append_some_local _ _ s s4 s5 e1234 (step _ _ _ h5)
  have e123456 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur"),
              shldCopn "out" "out" "prev" "k", storeAt0 "rp" "out",
              .Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (pv "cur")]
              ++ [binImm "sp" (.Oadd .U64) 8]) s = some s6 :=
    bignumExec_append_some_local _ _ s s5 s6 e12345 (step _ _ _ h6)
  have e1234567 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur"),
              shldCopn "out" "out" "prev" "k", storeAt0 "rp" "out",
              .Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (pv "cur"),
              binImm "sp" (.Oadd .U64) 8]
              ++ [binImm "rp" (.Oadd .U64) 8]) s = some s7 :=
    bignumExec_append_some_local _ _ s s6 s7 e123456 (step _ _ _ h7)
  have e12345678 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur"),
              shldCopn "out" "out" "prev" "k", storeAt0 "rp" "out",
              .Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (pv "cur"),
              binImm "sp" (.Oadd .U64) 8, binImm "rp" (.Oadd .U64) 8]
              ++ [binImm "n" (.Osub .U64) 1]) s = some s8 :=
    bignumExec_append_some_local _ _ s s7 s8 e1234567 (step _ _ _ h8)
  have hbody : lshiftLoopBody = [loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "out" }) .AT_none (.sword .U64) (pv "cur"),
              shldCopn "out" "out" "prev" "k", storeAt0 "rp" "out",
              .Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (pv "cur"),
              binImm "sp" (.Oadd .U64) 8, binImm "rp" (.Oadd .U64) 8,
              binImm "n" (.Osub .U64) 1] := rfl
  refine ⟨s8, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]; exact e12345678
  · -- memory
    show s8.mem = s.mem.store64 (regAddr s "rp")
        (UInt64.ofNat (shld64 a (s.regs "prev") (s.regs "k")).toNat)
    simp only [hs8, setReg]
    show (setReg s6 "rp" _).mem = _
    simp only [setReg_mem]
    simp only [hs6, setReg_mem]
    simp only [hs5, setReg_mem]
    show (storeMem s3 _ _).mem = _
    simp only [storeMem_mem]
    rw [hs3_mem, hs3_rp, hs3_out]
    rfl
  · -- prev = a
    show s8.regs "prev" = a
    simp only [hs8, setReg]
    show (setReg s6 "rp" _).regs "prev" = a
    simp only [setReg, show "prev" ≠ "rp" from by decide, ↓reduceIte, if_false]
    show (setReg s5 "sp" _).regs "prev" = a
    simp only [setReg, show "prev" ≠ "sp" from by decide, ↓reduceIte, if_false]
    show (setReg s4 "prev" a).regs "prev" = a
    simp [setReg]
  · -- k preserved
    show s8.regs "k" = s.regs "k"
    simp only [hs8, setReg]
    show (setReg s6 "rp" _).regs "k" = _
    simp only [setReg, show "k" ≠ "rp" from by decide, show "k" ≠ "n" from by decide,
               ↓reduceIte, if_false]
    show (setReg s5 "sp" _).regs "k" = _
    simp only [setReg, show "k" ≠ "sp" from by decide, ↓reduceIte, if_false]
    show (setReg s4 "prev" a).regs "k" = _
    simp only [setReg, show "k" ≠ "prev" from by decide, ↓reduceIte, if_false]
    show (storeMem s3 _ _).regs "k" = _
    simp only [storeMem_regs]
    simp [hs3, hs2, hs1, setReg]
  · -- sp = orig sp + 8
    show s8.regs "sp" = s.regs "sp" + 8
    simp only [hs8, setReg]
    show (setReg s6 "rp" _).regs "sp" = _
    simp only [setReg, show "sp" ≠ "rp" from by decide,
               show "sp" ≠ "n" from by decide, ↓reduceIte, if_false]
    show (setReg s5 "sp" (s5.regs "sp" + BitVec.ofInt 64 8)).regs "sp" = _
    simp only [setReg, ↓reduceIte, if_true]
    rw [hs5_sp]
    show s.regs "sp" + BitVec.ofInt 64 8 = s.regs "sp" + 8
    bv_decide
  · -- rp = orig rp + 8
    show s8.regs "rp" = s.regs "rp" + 8
    simp only [hs8, setReg]
    show (setReg s6 "rp" (s6.regs "rp" + BitVec.ofInt 64 8)).regs "rp" = _
    simp only [setReg, show "rp" ≠ "n" from by decide, ↓reduceIte, if_true, if_false]
    rw [hs6_rp]
    show s.regs "rp" + BitVec.ofInt 64 8 = s.regs "rp" + 8
    bv_decide
  · -- n = orig n - 1
    show s8.regs "n" = s.regs "n" - 1
    simp only [hs8, setReg, ↓reduceIte, if_true]
    have hs7_n : s7.regs "n" = s.regs "n" := by
      simp only [hs7, setReg, show "n" ≠ "rp" from by decide, ↓reduceIte, if_false]
      simp only [hs6, setReg, show "n" ≠ "sp" from by decide, ↓reduceIte, if_false]
      simp only [hs5, setReg, show "n" ≠ "prev" from by decide, ↓reduceIte, if_false]
      show (storeMem s3 _ _).regs "n" = _
      simp only [storeMem_regs]
      simp [hs3, hs2, hs1, setReg, show "n" ≠ "out" from by decide,
            show "n" ≠ "cur" from by decide]
    rw [hs7_n]
    show s.regs "n" - BitVec.ofInt 64 1 = s.regs "n" - 1
    bv_decide

/-- `lshiftLoopBody` is straight-line. -/
theorem lshiftLoopBody_straightLine : InstrR.bodyIsStraightLine lshiftLoopBody := by
  simp only [lshiftLoopBody, loadAt0, shldCopn, storeAt0, binImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `lshiftLoopBody` is non-control. -/
theorem lshiftLoopBody_nonControl : ∀ i ∈ lshiftLoopBody, i.isNonControl := by
  intro i hi
  simp only [lshiftLoopBody, loadAt0, shldCopn, storeAt0, binImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-- Forward one-iteration rule for the lshift loop. -/
theorem bignumExecFuel_lshiftLoop_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec lshiftLoopBody s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond lshiftLoopBody] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond lshiftLoopBody] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) lshiftLoopBody s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f lshiftLoopBody s
        lshiftLoopBody_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) lshiftLoopBody [.Cwhile [] cond lshiftLoopBody]
        lshiftLoopBody_nonControl s s_mid s' hsl hrec]

/-! #### Loop induction (`mpnAddN_loop`-shaped) -/

/-- `shld64 cur prev k = (cur <<< (k%64)) ||| (prev >>> ((64 - k%64) % 64))`
    is the obligation form; for `0 < k < 64`, `k.toNat % 64 = k` and
    `64 - k = 64 - k`. -/
theorem shld64_unfold (cur prev k : BitVec 64) :
    shld64 cur prev k = (cur <<< (k.toNat % 64)) ||| (prev >>> (64 - k.toNat % 64)) := by
  rfl

/-- For `0 < k < 64`, `(BitVec.ofNat 64 k).toNat % 64 = k`. -/
theorem ofNat_bv_toNat_mod (k : Nat) (hk : k < 64) :
    (BitVec.ofNat 64 k).toNat % 64 = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
      Nat.mod_eq_of_lt hk]

/-- The loop, by induction on the limb list.  Mirror of
    `Mpn.AddPrototype.mpnAddN_loop` for the lshift body, with the `cf`/`carry`
    register replaced by `prev` (the unshifted previous limb). -/
theorem mpnLShift_loop :
    ∀ (as : List (BitVec 64)) (s : BignumState) (k : Nat) (prev_reg : BitVec 64)
        (extra : Nat),
      0 < k → k < 64 →
      s.regs "prev" = prev_reg →
      s.regs "n"    = BitVec.ofNat 64 as.length →
      s.regs "k"    = BitVec.ofNat 64 k →
      memHoldsLimbs s.mem (regAddr s "sp") as →
      MemoryModel.Disjoint (range (regAddr s "rp") (8 * as.length))
        (range (regAddr s "sp") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) lshiftLoopBody] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "rp")
          ((bitShiftLeftAux k (prev_reg >>> (64 - k)) as).take as.length) ∧
        s'.regs "rp"   = s.regs "rp" + BitVec.ofNat 64 (8 * as.length) ∧
        s'.regs "prev" = as.foldl (fun _ w => w) prev_reg ∧
        s'.regs "k"    = BitVec.ofNat 64 k ∧
        (∀ b, MemoryModel.Disjoint (range b 8)
              (range (regAddr s "rp") (8 * as.length)) →
            load64Mem s'.mem b = load64Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro s k prev_reg extra _ _ _ hn _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hfuel : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [hfuel]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ lshiftLoopBody s
        (evalPExpr_loopCond_false s hn0)
    · simp [bitShiftLeftAux, memHoldsLimbs, List.take]
    · show s.regs "rp" = s.regs "rp" + BitVec.ofNat 64 (8 * 0)
      simp
    · simp [List.foldl, ‹s.regs "prev" = prev_reg›]
    · exact ‹s.regs "k" = BitVec.ofNat 64 k›
    · intro b _; rfl
  | cons a as ih =>
    intro s k prev_reg extra hkpos hk hprev hn hkreg hmem hdo
    -- Length and bound on the limb count.
    have hpos : 0 < 8 * (as.length + 1) := by omega
    have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
      simpa [List.length_cons] using
        disjoint_range_lt (regAddr s "rp") (regAddr s "sp")
          (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
          (by simpa using hdo)
    have hLsucc : as.length + 1 < 2 ^ 64 := by omega
    -- Guard is true.
    have hn_ne : s.regs "n" ≠ 0 := by
      rw [hn]
      simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
    obtain ⟨hmem_head, hmem_tail⟩ := hmem
    -- One iteration.
    obtain ⟨s1, hs1, hs1_mem, hs1_prev, hs1_k, hs1_sp, hs1_rp, hs1_n⟩ :=
      bignumExec_lshiftLoopBody_step s a hmem_head
    set rp0 : UInt64 := regAddr s "rp" with hrp0
    have hra_sp : regAddr s1 "sp" = regAddr s "sp" + 8 := by
      simp only [regAddr, hs1_sp]; exact regAddr_advance _
    have hra_rp : regAddr s1 "rp" = rp0 + 8 := by
      simp only [regAddr, hs1_rp, hrp0]; exact regAddr_advance _
    -- Memory after this iteration: a single store at rp0 of value `shld64`.
    have hmem1 : s1.mem = s.mem.store64 rp0
        (UInt64.ofNat (shld64 a (s.regs "prev") (s.regs "k")).toNat) := by
      simpa [hrp0, regAddr] using hs1_mem
    -- Frame the unread suffix of `sp` across the head store.
    have hdoa_store_sptail :
        MemoryModel.Disjoint (range rp0 8) (range (regAddr s "sp" + 8) (8 * as.length)) := by
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdo
      · exact range_head_subset rp0 as.length x (by simpa [List.length_cons] using h)
      · exact range_shift_subset (regAddr s "sp") as.length x
          (by simpa [List.length_cons] using h)
    have hmem1' : memHoldsLimbs s1.mem (regAddr s1 "sp") as := by
      rw [hra_sp, hmem1]
      exact memHoldsLimbs_store64_frame s.mem (regAddr s "sp" + 8) rp0 _ as
        hdoa_store_sptail hmem_tail
    have hdo1 : MemoryModel.Disjoint (range (regAddr s1 "rp") (8 * as.length))
        (range (regAddr s1 "sp") (8 * as.length)) := by
      rw [hra_rp, hra_sp]
      refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdo
      · exact range_shift_subset rp0 as.length x (by simpa [List.length_cons] using h)
      · exact range_shift_subset (regAddr s "sp") as.length x
          (by simpa [List.length_cons] using h)
    -- prev after iteration: a.
    have hprev1 : s1.regs "prev" = a := hs1_prev
    have hk1 : s1.regs "k" = BitVec.ofNat 64 k := by rw [hs1_k, hkreg]
    have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
      rw [hs1_n, hn]
      simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
    -- Apply the IH on the tail, with the new prev `a`.
    obtain ⟨s', hs', hs'_mem, hs'_rp, hs'_prev, hs'_k, hs'_frame⟩ :=
      ih s1 k a extra hkpos hk hprev1 hn1 hk1 hmem1' hdo1
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Fuel: same shape as the add proof.
      have hfuel : 2 * (a :: as).length + 3 + extra
          = (2 * as.length + 2 + extra) + 3 := by
        simp only [List.length_cons]; ring
      rw [hfuel]
      refine bignumExecFuel_lshiftLoop_step emptyRegistry (2 * as.length + 2 + extra) _
        s s1 s' (evalPExpr_loopCond_true s hn_ne) hs1 ?_
      simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
              from by omega] using hs'
    · -- Memory at `rp0`:  head limb = shld64 a prev k = (a <<< k) ||| (prev_reg >>> (64-k))
      -- Tail: by IH.
      rw [hmem1] at hs'_frame
      have hsep : MemoryModel.Disjoint (range rp0 8) (range (rp0 + 8) (8 * as.length)) :=
        range_op_head_tail_disjoint rp0 as.length (by omega)
      refine ⟨?_, ?_⟩
      · -- Head limb at `rp0`: load → `shld64 a prev_reg k` = `(a <<< k) ||| (prev_reg >>> (64-k))`.
        rw [hs'_frame rp0 (by rw [hra_rp]; exact hsep)]
        have hread := load64Mem_store64_same s.mem rp0
          (UInt64.ofNat (shld64 a (s.regs "prev") (s.regs "k")).toNat)
        rw [hread]
        -- Now show the head of `((bitShiftLeftAux k (prev_reg >>> (64-k)) (a :: as)).take (|a::as|))`
        -- equals `shld64 a (s.regs "prev") (s.regs "k")` after the UInt64 round-trip.
        -- bitShiftLeftAux k spill (a :: as) = ((a <<< k) ||| spill) :: ...
        show some (UInt64.ofNat _) = some
          (UInt64.ofNat ((bitShiftLeftAux k (prev_reg >>> (64 - k)) (a :: as)).take
            (a :: as).length).head!.toNat)
        congr 1
        show UInt64.ofNat (shld64 a (s.regs "prev") (s.regs "k")).toNat = _
        rw [hprev, hkreg]
        have hmod : (BitVec.ofNat 64 k).toNat % 64 = k := ofNat_bv_toNat_mod k hk
        -- shld64 a prev_reg (ofNat k) = (a <<< k) ||| (prev_reg >>> (64-k))
        show UInt64.ofNat
            ((a <<< ((BitVec.ofNat 64 k).toNat % 64)) |||
              (prev_reg >>> (64 - (BitVec.ofNat 64 k).toNat % 64))).toNat = _
        rw [hmod]
        -- bitShiftLeftAux unfolds: head is `(a <<< k) ||| (prev_reg >>> (64 - k))`.
        simp only [bitShiftLeftAux, List.take, List.head!,
                   show (a :: as).length = as.length + 1 from rfl]
      · -- Tail: IH frame says rp1=rp0+8 holds the IH'd shifted limbs (with new spill).
        have hthis := hs'_mem
        rw [hra_rp] at hthis
        -- The tail of `(bitShiftLeftAux k (prev_reg>>>(64-k)) (a :: as)).take (|a::as|)`
        -- equals `(bitShiftLeftAux k (a >>> (64-k)) as).take |as|`.  The IH gives the
        -- latter at base `rp0 + 8`, which is exactly the goal.
        exact hthis
    · -- rp = orig rp + 8 * (|as| + 1).
      rw [hs'_rp, hs1_rp]
      show s.regs "rp" + 8 + BitVec.ofNat 64 (8 * as.length) =
        s.regs "rp" + BitVec.ofNat 64 (8 * (a :: as).length)
      have heq : (8 : BitVec 64) + BitVec.ofNat 64 (8 * as.length) =
             BitVec.ofNat 64 (8 * (a :: as).length) := by
        simp only [List.length_cons]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                   show ((8 : BitVec 64).toNat) = 8 from rfl]
        omega
      rw [← heq]; bv_decide
    · -- prev = foldl (fun _ w => w) prev_reg (a :: as) = foldl … a as.
      rw [hs'_prev]
      simp [List.foldl]
    · -- k preserved.
      exact hs'_k
    · -- Frame.
      intro bb hbb
      rw [hmem1] at hs'_frame
      have hbb_tail : MemoryModel.Disjoint (range bb 8)
          (range (regAddr s1 "rp") (8 * as.length)) := by
        rw [hra_rp]
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        exact range_shift_subset rp0 as.length x
          (by simpa [List.length_cons] using h)
      rw [hs'_frame bb hbb_tail]
      have hbb_head : MemoryModel.Disjoint (range bb 8) (range rp0 8) := by
        refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
        exact range_head_subset rp0 as.length x
          (by simpa [List.length_cons] using h)
      rw [load64Mem_store64_disjoint s.mem bb rp0 _ hbb_head]

/-! #### LShiftLoopOblg discharged -/

/-- **The lshift loop residual, fully proved.**  Direct corollary of
    `mpnLShift_loop`. -/
theorem LShiftLoopOblg_proof : LShiftLoopOblg := by
  intro s as k prev_reg extra hkpos hk hprev hn hkreg hmem hdo
  -- The full bridge statement uses `UInt64.ofNat (s.regs "sp").toNat` etc.
  -- `Mpn.AddPrototype.regAddr s "sp" = UInt64.ofNat (s.regs "sp").toNat` by definition.
  exact mpnLShift_loop as s k prev_reg extra hkpos hk hprev hn hkreg hmem hdo

/-- **The `mpn_lshift_loop_obligation` residual is closed.**  Direct
    corollary of `LShiftLoopOblg_proof`. -/
theorem mpn_lshift_loop_obligation_proof : mpn_lshift_loop_obligation :=
  LShiftLoopOblg_proof

/-- **`MpnLShiftJasminRefines` lifted from sorry-free residual to a proved
    fact.**  The `abbrev` `MpnLShiftJasminRefines := mpn_lshift_loop_obligation`
    is definitionally `LShiftLoopOblg`, fully closed by `LShiftLoopOblg_proof`. -/
theorem MpnLShiftJasminRefines_proved : MpnLShiftJasminRefines :=
  LShiftLoopOblg_proof

/-! ### §4d  Bridge reduction (prelude + spill tail) — lshift

The reduction `LShiftLoopOblg → MpnLShiftRefinesStmt`: handle the
`prev := 0` prelude (one straight-line instruction) and the post-loop
spill tail (five straight-line instructions: `kbar := 64; kbar := kbar
- k; k := kbar; spill := SHR_64(prev, k); rp[0] := spill`).  The
threading is: after the loop, register `prev` holds `foldl (fun _ w =>
w) 0 as = lastD 0 as`, and `rp` register points at `original_rp +
8·|as|`.  The post-loop SHR computes the trailing spill limb
`prev_loop >>> (64 - k)`, which is exactly the `|as|`-th limb of
`bitShiftLeftAux k 0 as`. -/

/-- The list `bitShiftLeftAux k prev as` has length `|as| + 1`. -/
theorem bitShiftLeftAux_length (k : Nat) (prev : BitVec 64) (as : List (BitVec 64)) :
    (bitShiftLeftAux k prev as).length = as.length + 1 := by
  induction as generalizing prev with
  | nil => simp [bitShiftLeftAux]
  | cons a as ih =>
    simp only [bitShiftLeftAux, List.length_cons]
    rw [ih (a >>> (64 - k))]

/-- Define the trailing-limb function: for prev=0 starting spill, the last
    limb of `bitShiftLeftAux k 0 as` equals this. -/
def lshiftTrailLimb (k : Nat) (as : List (BitVec 64)) : BitVec 64 :=
  match as with
  | [] => 0
  | a :: rest => (rest.foldl (fun _ w => w) a) >>> (64 - k)

/-- The trailing limb formula is `(foldl ... 0 as) >>> (64-k)` when `as ≠ []`,
    and `0` when `as = []`. -/
theorem lshiftTrailLimb_eq (k : Nat) (as : List (BitVec 64)) :
    lshiftTrailLimb k as = (as.foldl (fun _ w => w) (0 : BitVec 64)) >>> (64 - k) := by
  cases as with
  | nil =>
    simp only [lshiftTrailLimb, List.foldl]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight]
  | cons a as =>
    simp only [lshiftTrailLimb, List.foldl]

/-- The general recombination lemma: for any `prev`, knowing the take-|as|
    and the trailing limb (`prev` if `as = []`, else `(foldl ... a as) >>> (64-k)`
    where `a` is the head of `as`) gives the full `bitShiftLeftAux k prev as`
    in memory.  The trail is `match as with | [] => prev | _::rest => last_of_rest`. -/
theorem memHoldsLimbs_bsla_recombine (k : Nat)
    (m : MemoryModel.Mem) (base : UInt64)
    (as : List (BitVec 64)) (prev : BitVec 64)
    (htake : memHoldsLimbs m base ((bitShiftLeftAux k prev as).take as.length))
    (hlast : load64Mem m (base + UInt64.ofNat (8 * as.length))
              = some (UInt64.ofNat
                  (match as with
                    | [] => prev
                    | a :: rest => (rest.foldl (fun _ w => w) a) >>> (64 - k)).toNat)) :
    memHoldsLimbs m base (bitShiftLeftAux k prev as) := by
  induction as generalizing base prev with
  | nil =>
    -- bitShiftLeftAux k prev [] = [prev]; trail = prev; load at base+0 = prev.
    simp only [bitShiftLeftAux, List.length_nil, Nat.mul_zero, memHoldsLimbs] at *
    refine ⟨?_, trivial⟩
    convert hlast using 2
    show base = base + UInt64.ofNat 0
    apply UInt64.toNat.inj
    simp [UInt64.toNat_add, UInt64.toNat_ofNat']
  | cons a as ih =>
    -- bsla k prev (a :: as) = ((a<<<k) ||| prev) :: bsla k (a >>> (64-k)) as.
    simp only [bitShiftLeftAux, List.length_cons, List.take] at htake ⊢
    obtain ⟨hh, ht⟩ := htake
    refine ⟨hh, ?_⟩
    -- Recurse on `as` at base+8 with prev := a >>> (64-k).
    apply ih (base + 8) (a >>> (64 - k))
    · exact ht
    · -- Trail: cases on as.
      cases as with
      | nil =>
        simp only [List.length_nil, Nat.mul_zero] at *
        -- hlast: load at base + 8*1 = a >>> (64-k).
        -- Goal: load at (base + 8) + 0 = a >>> (64-k).
        have : (base + 8) + UInt64.ofNat 0 = base + UInt64.ofNat (8 * 1) := by
          apply UInt64.toNat.inj
          simp [UInt64.toNat_add, UInt64.toNat_ofNat']
        rw [this]
        exact hlast
      | cons a' as' =>
        -- Unfold the matches on both sides explicitly.
        show load64Mem m ((base + 8) + UInt64.ofNat (8 * (a' :: as').length))
              = some (UInt64.ofNat (as'.foldl (fun _ w => w) a' >>> (64 - k)).toNat)
        have hlast' : load64Mem m (base + UInt64.ofNat (8 * (a :: a' :: as').length))
              = some (UInt64.ofNat ((a' :: as').foldl (fun _ w => w) a >>> (64 - k)).toNat) :=
          hlast
        have haddr : (base + 8) + UInt64.ofNat (8 * (a' :: as').length)
                    = base + UInt64.ofNat (8 * (a :: a' :: as').length) := by
          apply UInt64.toNat.inj
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat',
                     show ((8 : UInt64).toNat) = 8 from rfl, List.length_cons]
          omega
        rw [haddr]
        have hfold : (a' :: as').foldl (fun _ w => w) a
                    = as'.foldl (fun _ w => w) a' := by
          simp [List.foldl]
        rw [← hfold]
        exact hlast'

/-- `bitShiftLeftAux k 0 as` recomposes: take |as| ++ [trail].  Equivalent
    `memHoldsLimbs` form: holding the first |as| limbs at `base` plus the
    trail limb at `base + 8|as|` implies the predicate for the full list. -/
theorem memHoldsLimbs_lshift_recombine (k : Nat)
    (m : MemoryModel.Mem) (base : UInt64)
    (as : List (BitVec 64))
    (htake : memHoldsLimbs m base ((bitShiftLeftAux k 0 as).take as.length))
    (hlast : load64Mem m (base + UInt64.ofNat (8 * as.length))
              = some (UInt64.ofNat (lshiftTrailLimb k as).toNat)) :
    memHoldsLimbs m base (bitShiftLeftAux k 0 as) := by
  apply memHoldsLimbs_bsla_recombine k m base as 0 htake
  rw [hlast]
  cases as with
  | nil => rfl
  | cons a as => rfl

/-- `bv_sub_64_k`: `BitVec.ofNat 64 64 - BitVec.ofNat 64 k = BitVec.ofNat 64 (64 - k)`
    for `0 ≤ k ≤ 64`. -/
theorem bv_sub_64_k (k : Nat) (hk : k ≤ 64) :
    (BitVec.ofNat 64 64 : BitVec 64) - BitVec.ofNat 64 k = BitVec.ofNat 64 (64 - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
             Nat.mod_eq_of_lt (show 64 < 2^64 by decide),
             Nat.mod_eq_of_lt (show k < 2^64 from by omega),
             Nat.mod_eq_of_lt (show 64 - k < 2^64 from by omega)]
  omega

/-- `shr64 prev (BitVec.ofNat 64 (64 - k)) = prev >>> (64 - k)` for `0 < k < 64`. -/
theorem shr64_kbar (prev : BitVec 64) (k : Nat) (hkpos : 0 < k) (hk : k < 64) :
    BignumExec.shr64 prev (BitVec.ofNat 64 (64 - k)) = prev >>> (64 - k) := by
  -- shr64 = single-precision SHR: shr64 a c = a >>> (c.toNat % 64)
  show prev >>> ((BitVec.ofNat 64 (64 - k)).toNat % 64) = prev >>> (64 - k)
  rw [ofNat_bv_toNat_mod (64 - k) (by omega)]

/-! #### Helper: emit the spill-tail instructions one step at a time -/

private theorem execInstr_kbar_assign64 (s : BignumState) :
    execInstr s (.Cassgn (.Lvar { var := vr "kbar" }) .AT_none (.sword .U64)
                  (.Pconst 64)) = some (setReg s "kbar" (BitVec.ofInt 64 64)) := by
  rw [execInstr_constAssign]

private theorem execInstr_kbar_sub (s : BignumState) :
    execInstr s (.Cassgn (.Lvar { var := vr "kbar" }) .AT_none (.sword .U64)
                  (.Papp2 (.Osub .U64) (pv "kbar") (pv "k"))) =
        some (setReg s "kbar" (s.regs "kbar" - s.regs "k")) := by
  simp only [execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind]

private theorem execInstr_k_from_kbar (s : BignumState) :
    execInstr s (.Cassgn (.Lvar { var := vr "k" }) .AT_none (.sword .U64)
                  (pv "kbar")) = some (setReg s "k" (s.regs "kbar")) :=
  execInstr_regCopy s "k" "kbar"

/-- The post-loop spill tail of `lshiftBody` (5 instructions). -/
private def lshiftSpillTail : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "kbar" }) .AT_none (.sword .U64) (.Pconst 64)
  , .Cassgn (.Lvar { var := vr "kbar" }) .AT_none (.sword .U64)
      (.Papp2 (.Osub .U64) (pv "kbar") (pv "k"))
  , .Cassgn (.Lvar { var := vr "k" }) .AT_none (.sword .U64) (pv "kbar")
  , shrCopn "spill" "prev" "k"
  , storeAt0 "rp" "spill" ]

private theorem lshiftSpillTail_straightLine :
    InstrR.bodyIsStraightLine lshiftSpillTail := by
  simp only [lshiftSpillTail, shrCopn, storeAt0,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Body decomposes as prelude ++ [Cwhile] ++ spill tail. -/
private theorem lshiftBody_decompose :
    lshiftBody =
      [.Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (.Pconst 0)]
      ++ [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) lshiftLoopBody]
      ++ lshiftSpillTail := by
  rfl

/-- The spill tail runs from a state with `prev` register holding `p`,
    `k` register holding `BitVec.ofNat 64 k` (with `0 < k < 64`), to a
    state whose memory differs from the input only by a single store at
    `rp + 0` of the value `UInt64.ofNat (p >>> (64 - k)).toNat`. -/
theorem lshiftSpillTail_step (s : BignumState) (p : BitVec 64) (k : Nat)
    (hkpos : 0 < k) (hk : k < 64)
    (hprev : s.regs "prev" = p)
    (hkreg : s.regs "k" = BitVec.ofNat 64 k) :
    ∃ s', bignumExec lshiftSpillTail s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "rp")
        (UInt64.ofNat (p >>> (64 - k)).toNat) := by
  -- Step through the five instructions.
  -- 1. kbar := 64
  have h1 : execInstr s
      (.Cassgn (.Lvar { var := vr "kbar" }) .AT_none (.sword .U64) (.Pconst 64))
      = some (setReg s "kbar" (BitVec.ofInt 64 64)) :=
    execInstr_kbar_assign64 s
  set s1 : BignumState := setReg s "kbar" (BitVec.ofInt 64 64) with hs1
  -- 2. kbar := kbar - k
  have hs1_kbar : s1.regs "kbar" = BitVec.ofInt 64 64 := by simp [hs1, setReg]
  have hs1_k : s1.regs "k" = BitVec.ofNat 64 k := by
    simp [hs1, setReg, hkreg]
  have h2 : execInstr s1 (.Cassgn (.Lvar { var := vr "kbar" }) .AT_none (.sword .U64)
              (.Papp2 (.Osub .U64) (pv "kbar") (pv "k"))) =
            some (setReg s1 "kbar" (s1.regs "kbar" - s1.regs "k")) :=
    execInstr_kbar_sub s1
  set s2 : BignumState := setReg s1 "kbar" (s1.regs "kbar" - s1.regs "k") with hs2
  have hs2_kbar : s2.regs "kbar" = BitVec.ofNat 64 (64 - k) := by
    simp only [hs2, setReg, ↓reduceIte, if_true]
    rw [hs1_kbar, hs1_k]
    -- BitVec.ofInt 64 64 = BitVec.ofNat 64 64
    have : (BitVec.ofInt 64 64 : BitVec 64) = BitVec.ofNat 64 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
      decide
    rw [this]
    exact bv_sub_64_k k (by omega)
  -- 3. k := kbar
  have h3 : execInstr s2 (.Cassgn (.Lvar { var := vr "k" }) .AT_none (.sword .U64)
              (pv "kbar")) = some (setReg s2 "k" (s2.regs "kbar")) :=
    execInstr_k_from_kbar s2
  set s3 : BignumState := setReg s2 "k" (s2.regs "kbar") with hs3
  have hs3_k : s3.regs "k" = BitVec.ofNat 64 (64 - k) := by
    simp only [hs3, setReg, ↓reduceIte, if_true]
    exact hs2_kbar
  have hs3_prev : s3.regs "prev" = p := by
    simp only [hs3, setReg, show "prev" ≠ "k" from by decide, ↓reduceIte, if_false]
    simp only [hs2, setReg, show "prev" ≠ "kbar" from by decide, ↓reduceIte, if_false]
    simp only [hs1, setReg, show "prev" ≠ "kbar" from by decide, ↓reduceIte, if_false]
    exact hprev
  -- 4. spill := SHR_64(prev, k)
  have h4 : execInstr s3 (shrCopn "spill" "prev" "k") = some
      (setReg s3 "spill" (BignumExec.shr64 (s3.regs "prev") (s3.regs "k"))) :=
    execInstr_shrCopn s3 "spill" "prev" "k"
  set s4 : BignumState := setReg s3 "spill" (BignumExec.shr64 (s3.regs "prev")
                              (s3.regs "k")) with hs4
  have hs4_spill : s4.regs "spill" = p >>> (64 - k) := by
    simp only [hs4, setReg, ↓reduceIte, if_true]
    rw [hs3_prev, hs3_k]
    exact shr64_kbar p k hkpos hk
  have hs4_rp : s4.regs "rp" = s.regs "rp" := by
    simp only [hs4, setReg, show "rp" ≠ "spill" from by decide, ↓reduceIte, if_false]
    simp only [hs3, setReg, show "rp" ≠ "k" from by decide, ↓reduceIte, if_false]
    simp only [hs2, setReg, show "rp" ≠ "kbar" from by decide, ↓reduceIte, if_false]
    simp only [hs1, setReg, show "rp" ≠ "kbar" from by decide, ↓reduceIte, if_false]
  have hs4_mem : s4.mem = s.mem := by
    simp only [hs4, hs3, hs2, hs1, setReg]
  -- 5. [rp + 0] := spill
  have h5 : execInstr s4 (storeAt0 "rp" "spill") = some
              (storeMem s4 (UInt64.ofNat (s4.regs "rp").toNat)
                (UInt64.ofNat (s4.regs "spill").toNat)) :=
    execInstr_storeAt0_lshift s4 "rp" "spill"
  set s5 : BignumState := storeMem s4 (UInt64.ofNat (s4.regs "rp").toNat)
            (UInt64.ofNat (s4.regs "spill").toNat) with hs5
  -- Compose.
  have step (i : InstrR) (s' s'' : BignumState)
      (hi : execInstr s' i = some s'') :
      bignumExec [i] s' = some s'' := by
    simp only [bignumExec, hi]
  have e12 := bignumExec_append_some_local _ _ s s1 s2 (step _ _ _ h1) (step _ _ _ h2)
  have e123 := bignumExec_append_some_local _ _ s s2 s3 e12 (step _ _ _ h3)
  have e1234 := bignumExec_append_some_local _ _ s s3 s4 e123 (step _ _ _ h4)
  have e12345 := bignumExec_append_some_local _ _ s s4 s5 e1234 (step _ _ _ h5)
  refine ⟨s5, ?_, ?_⟩
  · show bignumExec lshiftSpillTail s = some s5
    show bignumExec [_,_,_,_,_] s = some s5
    convert e12345 using 1
  · show s5.mem = s.mem.store64 (regAddr s "rp")
        (UInt64.ofNat (p >>> (64 - k)).toNat)
    simp only [hs5, storeMem_mem, hs4_mem, hs4_rp, hs4_spill]
    rfl

/-! ### §4d  Lshift bridge reduction: prelude + loop + spill tail -/

/-- For `0 < k < 64`, `mpnShiftLeft as k = bitShiftLeftAux k 0 as`
    (the whole-limb part `k / 64 = 0` collapses to nothing). -/
theorem mpnShiftLeft_simple (as : List (BitVec 64)) (k : Nat)
    (hkpos : 0 < k) (hk : k < 64) :
    mpnShiftLeft as k = bitShiftLeftAux k 0 as := by
  unfold mpnShiftLeft
  rw [show k / 64 = 0 from Nat.div_eq_of_lt hk,
      show k % 64 = k from Nat.mod_eq_of_lt hk]
  simp [List.replicate]

/-- `0 >>> (64 - k) = 0` (the initial spill word is 0 in the no-prelude
    case). -/
theorem bv_zero_shiftRight_eq_zero (n : Nat) :
    ((0 : BitVec 64) >>> n) = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight]

/-! #### Tighter residual for the lshift bridge reduction

The full reduction `lshift_bridge_reduction : LShiftLoopOblg →
MpnLShiftRefinesStmt` still requires composing:

* (α) the `prev := 0` prelude (one straight-line `Cassgn`),
* (β) the loop (handled by `LShiftLoopOblg_proof` above),
* (γ) the 5-instruction spill tail (handled by `lshiftSpillTail_step`
      above, with `BitVec`-arithmetic for the post-loop `rp` register),
* (δ) the structural recombination
      `bitShiftLeftAux k 0 as = (take |as|) ++ [trail]`
      (handled by `memHoldsLimbs_lshift_recombine` above),
* (ε) a final fuel-accounting closure across the
      prelude+Cwhile+spill-tail concatenation
      (via `bignumExecFuel_append_join` + the straight-line equivalence
      `bignumExecFuel_eq_bignumExec_of_straightLine`).

Steps (α), (γ), (δ) are individually proved above as standalone
lemmas.  What remains is the **assembly**: chain them through the
fuel-accounting tracking the advanced `rp` register's `UInt64 ↔ BitVec`
round-trip.  We pin this as the tighter residual
`LShiftBridgeAssembly` — closing it discharges
`lshift_bridge_reduction` unconditionally.  This is strictly weaker
than the original `lshift_bridge_reduction`: the loop, prelude, and
spill-tail step are all closed; only the per-instruction fuel chain
plus the `regAddr` arithmetic on `s1.regs "rp"` remains. -/

/-- Tighter sorry-free residual: assembly of the prelude + Cwhile +
    spill-tail run, with the `rp` register advanced to `original_rp +
    8·|as|` (decoded to `UInt64`).  Specifically, this captures the
    "stitching" obligation: that the full body, when run from `s`,
    produces an output state `s'` whose memory at `regAddr s "rp"`
    holds the trailing spill limb of `bitShiftLeftAux k 0 as` at
    offset `8·|as|`. -/
def LShiftBridgeAssembly : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (k : Nat) (fuel : Nat),
    0 < k → k < 64 →
    s.regs "n"    = BitVec.ofNat 64 as.length →
    s.regs "k"    = BitVec.ofNat 64 k →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "sp").toNat) as →
    MemoryModel.Disjoint
      (range (UInt64.ofNat (s.regs "rp").toNat) (8 * (as.length + 1)))
      (range (UInt64.ofNat (s.regs "sp").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 4 →
    ∃ s' : BignumState, bignumExecFuel emptyRegistry fuel lshiftBody s = some s' ∧
      -- take-|as| at original rp
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        ((bitShiftLeftAux k 0 as).take as.length) ∧
      -- trailing spill load at original rp + 8|as|
      load64Mem s'.mem
          (UInt64.ofNat (s.regs "rp").toNat + UInt64.ofNat (8 * as.length))
        = some (UInt64.ofNat (lshiftTrailLimb k as).toNat)

/-- **Reduction `LShiftBridgeAssembly → lshift_bridge_reduction`**.
    Closing the tighter residual `LShiftBridgeAssembly` discharges
    `lshift_bridge_reduction` via `memHoldsLimbs_lshift_recombine` and
    `mpnShiftLeft_simple` (both fully proved). -/
theorem lshift_bridge_reduction_of_assembly
    (h_asm : LShiftBridgeAssembly) :
    lshift_bridge_reduction := by
  intro _ s as k fuel hkpos hk hn hkreg hmem hdo hfuel
  obtain ⟨s', hs'_exec, hs'_take, hs'_trail⟩ :=
    h_asm s as k fuel hkpos hk hn hkreg hmem hdo hfuel
  refine ⟨s', hs'_exec, ?_⟩
  rw [mpnShiftLeft_simple as k hkpos hk]
  exact memHoldsLimbs_lshift_recombine k _ _ as hs'_take hs'_trail

/-! #### Closing `LShiftBridgeAssembly`

We assemble the three already-closed pieces (prelude, loop, spill tail)
into a full run of `lshiftBody` via `bignumExecFuel_seq` (handles `Cwhile`
in the prefix) and the straight-line equivalence
`bignumExecFuel_eq_bignumExec_of_straightLine` (for the prelude / tail).

The trail load is preserved by `load64Mem_store64_same`; the take prefix
is preserved across the spill tail's single store by
`memHoldsLimbs_store64_frame`, with the tail-vs-head disjointness derived
inline (it's the head-vs-tail relation at a shifted base; the only
non-wrap bound comes from `disjoint_range_lt` applied to `hdo`). -/

/-- Tail-vs-head disjointness at an arbitrary U64 base: the 8-byte block
    at `base + ofNat (8·L)` is disjoint from the preceding `8·L` bytes at
    `base`, provided `8·(L+1) ≤ 2^64` (no wraparound).  Symmetric variant
    of `Mpn.AddPrototype.range_op_head_tail_disjoint`. -/
private theorem range_tail_head_disjoint (base : UInt64) (L : Nat)
    (hbound : 8 * (L + 1) ≤ 2 ^ 64) :
    MemoryModel.Disjoint
      (range (base + UInt64.ofNat (8 * L)) 8) (range base (8 * L)) := by
  intro a ⟨⟨i, hi, hai⟩, ⟨j, hj, haj⟩⟩
  -- a = (base + ofNat (8L)) + ofNat i, i < 8
  -- a = base + ofNat j, j < 8L
  rw [show base + UInt64.ofNat (8 * L) + UInt64.ofNat i
        = base + UInt64.ofNat (8 * L + i) from by
        rw [UInt64.ofNat_add]; ac_rfl] at hai
  rw [haj] at hai
  have hcancel := Mpn.AddPrototype.uint64_add_left_cancel base _ _ hai.symm
  have h2 := congrArg UInt64.toNat hcancel
  simp only [UInt64.toNat_ofNat'] at h2
  have h8Li : 8 * L + i < 2 ^ 64 := by
    have : 8 * L + i < 8 * (L + 1) := by omega
    omega
  have hj' : j < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h8Li, Nat.mod_eq_of_lt hj'] at h2
  omega

/-- **`LShiftBridgeAssembly` discharged, axiom-clean.**

    Assembly proof: chain the prelude (`prev := 0`, a single straight-line
    `Cassgn`) with the loop (`LShiftLoopOblg_proof`) and the post-loop
    spill tail (`lshiftSpillTail_step`, 5 straight-line instructions)
    via `bignumExecFuel_seq`.  The take-prefix is preserved across the
    spill store by `memHoldsLimbs_store64_frame` (using
    `range_tail_head_disjoint` for the tail-vs-head separation, with the
    no-wraparound bound derived from `hdo` via `disjoint_range_lt`).
    The trail load is read off the spill's `load64Mem_store64_same`. -/
theorem LShiftBridgeAssembly_proof : LShiftBridgeAssembly := by
  intro s as k fuel hkpos hk hn hkreg hmem hdo hfuel
  -- ===== Step 1: prelude `prev := 0` =====
  set s0 : BignumState := setReg s "prev" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  -- s0 register/memory transfer (setReg "prev" 0 leaves everything else alone)
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hreg0 : ∀ x, x ≠ "prev" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hprev0 : s0.regs "prev" = 0 := by rw [hs0]; simp [setReg]
  have hn0 : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide)]; exact hn
  have hk0 : s0.regs "k" = BitVec.ofNat 64 k := by
    rw [hreg0 "k" (by decide)]; exact hkreg
  have hsp0 : s0.regs "sp" = s.regs "sp" := hreg0 "sp" (by decide)
  have hrp0 : s0.regs "rp" = s.regs "rp" := hreg0 "rp" (by decide)
  have hmem_at_sp0 :
      memHoldsLimbs s0.mem (UInt64.ofNat (s0.regs "sp").toNat) as := by
    rw [hmem0, hsp0]; exact hmem
  -- The disjointness `Disjoint (range rp (8*L)) (range sp (8*L))` follows from
  -- `hdo` (which gives `8*(L+1)` bytes at rp) by shrinking.
  have hdo0 : MemoryModel.Disjoint
      (range (UInt64.ofNat (s0.regs "rp").toNat) (8 * as.length))
      (range (UInt64.ofNat (s0.regs "sp").toNat) (8 * as.length)) := by
    rw [hrp0, hsp0]
    refine disjoint_mono (fun x h => ?_) (fun x h => h) hdo
    obtain ⟨j, hj, rfl⟩ := h
    exact ⟨j, by omega, rfl⟩
  -- ===== Step 2: choose extra so fuel = 2*|as| + 5 + extra =====
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 5 + extra :=
    ⟨fuel - (2 * as.length + 5), by omega⟩
  -- ===== Step 3: invoke LShiftLoopOblg_proof on s0 with prev_reg := 0 =====
  obtain ⟨s1, hs1_exec, hs1_take, hs1_rp, hs1_prev, hs1_k, hs1_frame⟩ :=
    LShiftLoopOblg_proof s0 as k 0 extra hkpos hk hprev0 hn0 hk0 hmem_at_sp0 hdo0
  -- s1.regs "prev" = as.foldl (fun _ w => w) 0
  -- s1.regs "rp"   = s0.regs "rp" + ofNat (8*|as|) = s.regs "rp" + ofNat (8*|as|)
  have hs1_rp' : s1.regs "rp" = s.regs "rp" + BitVec.ofNat 64 (8 * as.length) := by
    rw [hs1_rp, hrp0]
  -- ===== Step 4: invoke lshiftSpillTail_step on s1 with p := foldl 0 as =====
  set p : BitVec 64 := as.foldl (fun _ w => w) (0 : BitVec 64) with hp
  obtain ⟨s2, hs2_exec, hs2_mem⟩ :=
    lshiftSpillTail_step s1 p k hkpos hk hs1_prev hs1_k
  -- Spill writes `(p >>> (64 - k))` at regAddr s1 "rp" = ofNat (s1.regs "rp").toNat
  -- = ofNat (s.regs "rp" + ofNat (8*|as|)).toNat = ofNat (s.regs "rp").toNat + ofNat (8*|as|)
  -- by regAddr_advance_at.
  have hregAddr_s1_rp :
      regAddr s1 "rp"
        = UInt64.ofNat (s.regs "rp").toNat + UInt64.ofNat (8 * as.length) := by
    show UInt64.ofNat (s1.regs "rp").toNat = _
    rw [hs1_rp']
    exact Mpn.AddPrototype.regAddr_advance_at (s.regs "rp") (8 * as.length)
  -- ===== Step 5: assemble fuel via bignumExecFuel_seq twice =====
  -- (a) prelude `[Cassgn]` at fuel 1 → s0.
  have h_prelude_fuel :
      bignumExecFuel emptyRegistry 1
        [.Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (.Pconst 0)] s
        = some s0 := by
    show bignumExecFuel emptyRegistry (0 + 1) _ s = some s0
    simp only [bignumExecFuel, hexec0]
  -- (b) lshiftSpillTail at fuel 1 (straight-line equivalence).
  have h_tail_fuel :
      bignumExecFuel emptyRegistry 1 lshiftSpillTail s1 = some s2 := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine emptyRegistry 0
          lshiftSpillTail s1 lshiftSpillTail_straightLine]
    exact hs2_exec
  -- (c) chain [Cwhile ...] with lshiftSpillTail (body1 has a Cwhile, so use _seq).
  have h_loop_tail :
      bignumExecFuel emptyRegistry ((2 * as.length + 3 + extra) + 1)
        ([.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) lshiftLoopBody]
          ++ lshiftSpillTail) s0 = some s2 :=
    bignumExecFuel_seq emptyRegistry (2 * as.length + 3 + extra) 1 _ _ _ _ _
      hs1_exec h_tail_fuel
  -- (d) chain prelude with (loop ++ tail).
  have h_total :
      bignumExecFuel emptyRegistry (1 + ((2 * as.length + 3 + extra) + 1))
        ([.Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (.Pconst 0)]
          ++ ([.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) lshiftLoopBody]
              ++ lshiftSpillTail)) s = some s2 :=
    bignumExecFuel_seq emptyRegistry 1 ((2 * as.length + 3 + extra) + 1) _ _ _ _ _
      h_prelude_fuel h_loop_tail
  -- Normalize the body and fuel to `lshiftBody`/`fuel`.
  have hbody_eq :
      [.Cassgn (.Lvar { var := vr "prev" }) .AT_none (.sword .U64) (.Pconst 0)]
        ++ ([.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) lshiftLoopBody]
            ++ lshiftSpillTail)
      = lshiftBody := by
    rw [← List.append_assoc]; exact lshiftBody_decompose.symm
  have hfuel_eq : 1 + ((2 * as.length + 3 + extra) + 1) = fuel := by omega
  rw [hbody_eq, hfuel_eq] at h_total
  -- ===== Step 6: package the take/trail conclusions =====
  refine ⟨s2, h_total, ?_, ?_⟩
  · -- Take area: s1.mem held the take prefix, and the spill store at
    -- regAddr s1 "rp" (= rp + 8*|as|) is disjoint from the take area
    -- (range rp (8*|as|)).
    -- Convert prev_reg=0 in the loop result: 0 >>> (64-k) = 0.
    have hzero : ((0 : BitVec 64) >>> (64 - k)) = 0 :=
      bv_zero_shiftRight_eq_zero (64 - k)
    rw [hzero] at hs1_take
    -- hs1_take : memHoldsLimbs s1.mem (UInt64.ofNat (s0.regs "rp").toNat)
    --             ((bitShiftLeftAux k 0 as).take as.length)
    -- Rewrite base to rp.
    rw [hrp0] at hs1_take
    -- s2.mem = s1.mem.store64 (regAddr s1 "rp") (UInt64.ofNat (p >>> (64-k)).toNat)
    rw [hs2_mem]
    -- Apply memHoldsLimbs_store64_frame: store at (rp + 8|as|) disjoint from take area [rp, rp + 8|as|).
    -- We need 8 * (|as| + 1) ≤ 2^64.  When |as| = 0, this is 8 ≤ 2^64.  When
    -- |as| ≥ 1, shrink `hdo`'s sp-side length from `8 * |as|` to `8 * (|as|+1)`
    -- (shrinks the second range, so disjointness still holds), then apply
    -- `disjoint_range_lt`.
    have hbound : 8 * (as.length + 1) ≤ 2 ^ 64 := by
      rcases Nat.eq_zero_or_pos as.length with hL | hL
      · rw [hL]; decide
      · -- hdo gives (rp, 8*(L+1)) vs (sp, 8*L).  We need both sides at 8*(L+1).
        -- The sp-side has length 8*L < 8*(L+1), so we can extend it: any 8*(L+1)
        -- range containing the 8*L range gives the same Disjoint (no, that's wrong
        -- direction).  Instead, shrink the rp-side from 8*(L+1) to 8*L, getting
        -- Disjoint at length 8*L on both sides, then apply disjoint_range_lt.
        have hdo' : MemoryModel.Disjoint
            (range (UInt64.ofNat (s.regs "rp").toNat) (8 * as.length))
            (range (UInt64.ofNat (s.regs "sp").toNat) (8 * as.length)) := by
          refine disjoint_mono (fun x h => ?_) (fun x h => h) hdo
          obtain ⟨j, hj, rfl⟩ := h
          exact ⟨j, by omega, rfl⟩
        have hL' : 0 < 8 * as.length := by omega
        have h_lt := disjoint_range_lt _ _ _ hL' hdo'
        omega
    have hdisj_store :
        MemoryModel.Disjoint
          (range (regAddr s1 "rp") 8)
          (range (UInt64.ofNat (s.regs "rp").toNat)
            (8 * ((bitShiftLeftAux k 0 as).take as.length).length)) := by
      rw [hregAddr_s1_rp]
      -- length of take = min |as| (|as|+1) = |as|
      have hlen_take : ((bitShiftLeftAux k 0 as).take as.length).length = as.length := by
        rw [List.length_take, bitShiftLeftAux_length]; omega
      rw [hlen_take]
      exact range_tail_head_disjoint (UInt64.ofNat (s.regs "rp").toNat) as.length hbound
    exact memHoldsLimbs_store64_frame s1.mem
      (UInt64.ofNat (s.regs "rp").toNat) (regAddr s1 "rp") _ _
      hdisj_store hs1_take
  · -- Trail load: the spill store at regAddr s1 "rp" deposits the trail value.
    rw [hs2_mem]
    -- Goal: load64Mem (s1.mem.store64 (regAddr s1 "rp") (ofNat (p >>> (64-k)).toNat))
    --         (ofNat (s.regs "rp").toNat + ofNat (8*|as|))
    --       = some (ofNat (lshiftTrailLimb k as).toNat)
    -- The store address equals the load address: regAddr s1 "rp" = ofNat (s.regs "rp").toNat + ofNat (8*|as|).
    rw [← hregAddr_s1_rp, load64Mem_store64_same]
    -- And p >>> (64-k) = lshiftTrailLimb k as by lshiftTrailLimb_eq.
    congr 1
    show UInt64.ofNat (p >>> (64 - k)).toNat
        = UInt64.ofNat (lshiftTrailLimb k as).toNat
    rw [lshiftTrailLimb_eq]

/-- **`lshift_bridge_reduction` discharged unconditionally.**  Composition of
    `lshift_bridge_reduction_of_assembly` with `LShiftBridgeAssembly_proof`. -/
theorem lshift_bridge_reduction_proof : lshift_bridge_reduction :=
  lshift_bridge_reduction_of_assembly LShiftBridgeAssembly_proof

/-- **`MpnLShiftRefinesStmt` discharged unconditionally** — the full bridge
    from the emitted Jasmin `lshiftBody` to the algorithm-level reference
    `mpnShiftLeft`.  Composition of the loop obligation
    `LShiftLoopOblg_proof` with the bridge reduction
    `lshift_bridge_reduction_proof`. -/
theorem MpnLShiftRefinesStmt_proof : MpnLShiftRefinesStmt :=
  lshift_bridge_reduction_proof LShiftLoopOblg_proof

/-! ### §4e  Discharge of the `mpn_rshift_bits` loop residual

Mirror of §4c (lshift) for rshift.  The key difference from lshift is
the **two-limb precondition**: each iteration reads `cur` from `sp+0`
*and* `next` from `sp+8` (looking one limb ahead), so the per-iteration
step lemma `bignumExec_rshiftLoopBody_step` requires `memHoldsLimbs`
to provide both limbs.  This naturally falls out of the `memHoldsLimbs`
predicate on `as = w₀ :: w₁ :: rest`: the head gives `cur = w₀` and
the tail's head gives `next = w₁`.

The induction is structurally identical to `mpnLShift_loop`, but with
base case `|as| = 1` (the loop iterates `|as| - 1` times) and step
case `as = w₀ :: w₁ :: rest`, recursing on `w₁ :: rest` (length
`|as| - 1`).  The post-loop spill tail is shorter (3 instructions vs
lshift's 5), since rshift's spill is just `top := sp[0]; spill :=
SHR_64(top, k); rp[0] := spill` (no `kbar` redirection — the top
limb is `as.last`, which the loop did NOT consume, so it's still in
memory at the advanced `sp`).  -/

/-- Effect of a load at register offset 8 (used for `next := [sp+8]`).
    Variant of `execInstr_loadAt0_lshift` with a non-zero `Pconst` offset. -/
theorem execInstr_loadAt8_rshift (s : BignumState) (x base : String) (v : BitVec 64)
    (hv : load64Mem s.mem (UInt64.ofNat (s.regs base + 8).toNat)
            = some (UInt64.ofNat v.toNat)) :
    execInstr s (.Cassgn (.Lvar { var := vr x }) .AT_none (.sword .U64)
                  (.Pload .U64 { var := vr base } (.Pconst 8))) =
      some (setReg s x v) := by
  simp only [execInstr, evalPExpr, vr,
             resolveAddr, Option.bind_some, bind, Option.bind,
             show (BitVec.ofInt 64 8 : BitVec 64) = 8 from rfl]
  rw [hv]
  simp only [bv_uint_roundtrip, bind, Option.bind, Option.bind_some]

/-- Effect of the SHRD intrinsic: `out := (cur >>> k%64) ||| (next <<< (64 - k%64))`. -/
theorem execInstr_shrdCopn (s : BignumState) :
    execInstr s (shrdCopn "out" "cur" "next" "k") = some
      (setReg s "out" (shrd64 (s.regs "cur") (s.regs "next") (s.regs "k"))) := by
  simp only [shrdCopn, shiftBundle, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind, writeShiftBundle]

/-! #### One iteration of `rshiftLoopBody` -/

/-- One iteration of `rshiftLoopBody`: given memory holds limb `a` at
    `sp + 0` and limb `a'` at `sp + 8`, the body lands in a state with:
    * `sp += 8`, `rp += 8`, `n -= 1` (pointer/counter advances),
    * `cur := a`, `next := a'`,
    * `out := shrd64 a a' (s.regs "k")`,
    * memory at `rp + 0` holds the merge `shrd64 a a' k`. -/
theorem bignumExec_rshiftLoopBody_step (s : BignumState) (a a' : BitVec 64)
    (ha : load64Mem s.mem (regAddr s "sp") = some (UInt64.ofNat a.toNat))
    (ha' : load64Mem s.mem (UInt64.ofNat (s.regs "sp" + 8).toNat)
            = some (UInt64.ofNat a'.toNat)) :
    ∃ s', bignumExec rshiftLoopBody s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "rp")
        (UInt64.ofNat (shrd64 a a' (s.regs "k")).toNat) ∧
      s'.regs "k"    = s.regs "k" ∧
      s'.regs "sp"   = s.regs "sp" + 8 ∧
      s'.regs "rp"   = s.regs "rp" + 8 ∧
      s'.regs "n"    = s.regs "n" - 1 := by
  -- Step through the 7 instructions.
  -- 1. cur := [sp + 0]   →  setReg s "cur" a
  have h1 : execInstr s (loadAt0 "cur" "sp") = some (setReg s "cur" a) :=
    execInstr_loadAt0_lshift s "cur" "sp" a ha
  set s1 : BignumState := setReg s "cur" a with hs1
  -- 2. next := [sp + 8]  →  setReg s1 "next" a'
  have hs1_sp : s1.regs "sp" = s.regs "sp" := by
    simp [hs1, setReg, show "sp" ≠ "cur" from by decide]
  have hs1_mem : s1.mem = s.mem := by simp [hs1, setReg]
  have ha'_at_s1 : load64Mem s1.mem (UInt64.ofNat (s1.regs "sp" + 8).toNat)
            = some (UInt64.ofNat a'.toNat) := by
    rw [hs1_sp, hs1_mem]; exact ha'
  have h2 : execInstr s1 (.Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
              (.Pload .U64 { var := vr "sp" } (.Pconst 8))) =
            some (setReg s1 "next" a') :=
    execInstr_loadAt8_rshift s1 "next" "sp" a' ha'_at_s1
  set s2 : BignumState := setReg s1 "next" a' with hs2
  -- 3. out := SHRD_64(cur, next, k)
  have hs2_cur : s2.regs "cur" = a := by
    simp [hs2, hs1, setReg, show "cur" ≠ "next" from by decide]
  have hs2_next : s2.regs "next" = a' := by simp [hs2, setReg]
  have hs2_k : s2.regs "k" = s.regs "k" := by
    simp [hs2, hs1, setReg, show "k" ≠ "next" from by decide,
          show "k" ≠ "cur" from by decide]
  have h3 : execInstr s2 (shrdCopn "out" "cur" "next" "k") =
            some (setReg s2 "out" (shrd64 a a' (s.regs "k"))) := by
    rw [execInstr_shrdCopn, hs2_cur, hs2_next, hs2_k]
  set s3 : BignumState := setReg s2 "out" (shrd64 a a' (s.regs "k")) with hs3
  -- 4. [rp + 0] := out
  have hs3_out : s3.regs "out" = shrd64 a a' (s.regs "k") := by
    simp [hs3, setReg]
  have hs3_rp : s3.regs "rp" = s.regs "rp" := by
    simp [hs3, hs2, hs1, setReg,
          show "rp" ≠ "out" from by decide,
          show "rp" ≠ "next" from by decide,
          show "rp" ≠ "cur" from by decide]
  have hs3_mem : s3.mem = s.mem := by
    simp [hs3, hs2, hs1, setReg]
  have h4 : execInstr s3 (storeAt0 "rp" "out") = some
              (storeMem s3 (UInt64.ofNat (s3.regs "rp").toNat)
                (UInt64.ofNat (s3.regs "out").toNat)) :=
    execInstr_storeAt0_lshift s3 "rp" "out"
  set s4 : BignumState := storeMem s3 (UInt64.ofNat (s3.regs "rp").toNat)
            (UInt64.ofNat (s3.regs "out").toNat) with hs4
  -- 5. sp += 8
  have hs4_sp : s4.regs "sp" = s.regs "sp" := by
    show (storeMem s3 _ _).regs "sp" = s.regs "sp"
    simp only [storeMem_regs]
    simp [hs3, hs2, hs1, setReg,
          show "sp" ≠ "out" from by decide,
          show "sp" ≠ "next" from by decide,
          show "sp" ≠ "cur" from by decide]
  have h5 : execInstr s4 (binImm "sp" (.Oadd .U64) 8) =
              some (setReg s4 "sp" (s4.regs "sp" + BitVec.ofInt 64 8)) :=
    execInstr_binImm_add s4 "sp" 8
  set s5 : BignumState := setReg s4 "sp" (s4.regs "sp" + BitVec.ofInt 64 8) with hs5
  -- 6. rp += 8
  have hs5_rp : s5.regs "rp" = s.regs "rp" := by
    simp only [hs5, setReg, show "rp" ≠ "sp" from by decide, ↓reduceIte, if_false]
    show (storeMem s3 _ _).regs "rp" = s.regs "rp"
    simp only [storeMem_regs]
    exact hs3_rp
  have h6 : execInstr s5 (binImm "rp" (.Oadd .U64) 8) =
              some (setReg s5 "rp" (s5.regs "rp" + BitVec.ofInt 64 8)) :=
    execInstr_binImm_add s5 "rp" 8
  set s6 : BignumState := setReg s5 "rp" (s5.regs "rp" + BitVec.ofInt 64 8) with hs6
  -- 7. n -= 1
  have h7 : execInstr s6 (binImm "n" (.Osub .U64) 1) =
              some (setReg s6 "n" (s6.regs "n" - BitVec.ofInt 64 1)) :=
    execInstr_binImm_sub s6 "n" 1
  set s7 : BignumState := setReg s6 "n" (s6.regs "n" - BitVec.ofInt 64 1) with hs7
  -- Compose.
  have step (i : InstrR) (s' s'' : BignumState)
      (hi : execInstr s' i = some s'') :
      bignumExec [i] s' = some s'' := by
    simp only [bignumExec, hi]
  have e12 : bignumExec ([loadAt0 "cur" "sp"] ++
              [.Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
                (.Pload .U64 { var := vr "sp" } (.Pconst 8))]) s
                = some s2 :=
    bignumExec_append_some_local _ _ s s1 s2 (step _ _ _ h1) (step _ _ _ h2)
  have e123 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
                (.Pload .U64 { var := vr "sp" } (.Pconst 8))]
              ++ [shrdCopn "out" "cur" "next" "k"]) s = some s3 :=
    bignumExec_append_some_local _ _ s s2 s3 e12 (step _ _ _ h3)
  have e1234 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
                (.Pload .U64 { var := vr "sp" } (.Pconst 8)),
              shrdCopn "out" "cur" "next" "k"] ++ [storeAt0 "rp" "out"]) s = some s4 :=
    bignumExec_append_some_local _ _ s s3 s4 e123 (step _ _ _ h4)
  have e12345 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
                (.Pload .U64 { var := vr "sp" } (.Pconst 8)),
              shrdCopn "out" "cur" "next" "k", storeAt0 "rp" "out"]
              ++ [binImm "sp" (.Oadd .U64) 8]) s = some s5 :=
    bignumExec_append_some_local _ _ s s4 s5 e1234 (step _ _ _ h5)
  have e123456 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
                (.Pload .U64 { var := vr "sp" } (.Pconst 8)),
              shrdCopn "out" "cur" "next" "k", storeAt0 "rp" "out",
              binImm "sp" (.Oadd .U64) 8]
              ++ [binImm "rp" (.Oadd .U64) 8]) s = some s6 :=
    bignumExec_append_some_local _ _ s s5 s6 e12345 (step _ _ _ h6)
  have e1234567 : bignumExec ([loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
                (.Pload .U64 { var := vr "sp" } (.Pconst 8)),
              shrdCopn "out" "cur" "next" "k", storeAt0 "rp" "out",
              binImm "sp" (.Oadd .U64) 8, binImm "rp" (.Oadd .U64) 8]
              ++ [binImm "n" (.Osub .U64) 1]) s = some s7 :=
    bignumExec_append_some_local _ _ s s6 s7 e123456 (step _ _ _ h7)
  have hbody : rshiftLoopBody = [loadAt0 "cur" "sp",
              .Cassgn (.Lvar { var := vr "next" }) .AT_none (.sword .U64)
                (.Pload .U64 { var := vr "sp" } (.Pconst 8)),
              shrdCopn "out" "cur" "next" "k", storeAt0 "rp" "out",
              binImm "sp" (.Oadd .U64) 8, binImm "rp" (.Oadd .U64) 8,
              binImm "n" (.Osub .U64) 1] := rfl
  refine ⟨s7, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]; exact e1234567
  · -- memory: only the storeMem at rp wrote; subsequent setRegs don't touch mem
    show s7.mem = s.mem.store64 (regAddr s "rp")
        (UInt64.ofNat (shrd64 a a' (s.regs "k")).toNat)
    simp only [hs7, setReg]
    show (setReg s5 "rp" _).mem = _
    simp only [setReg_mem]
    simp only [hs5, setReg_mem]
    show (storeMem s3 _ _).mem = _
    simp only [storeMem_mem]
    rw [hs3_mem, hs3_rp, hs3_out]
    rfl
  · -- k preserved
    show s7.regs "k" = s.regs "k"
    simp only [hs7, setReg]
    show (setReg s5 "rp" _).regs "k" = _
    simp only [setReg, show "k" ≠ "rp" from by decide,
               show "k" ≠ "n" from by decide,
               ↓reduceIte, if_false]
    show (setReg s4 "sp" _).regs "k" = _
    simp only [setReg, show "k" ≠ "sp" from by decide, ↓reduceIte, if_false]
    show (storeMem s3 _ _).regs "k" = _
    simp only [storeMem_regs]
    exact hs2_k
  · -- sp = orig sp + 8
    show s7.regs "sp" = s.regs "sp" + 8
    simp only [hs7, setReg]
    show (setReg s5 "rp" _).regs "sp" = _
    simp only [setReg, show "sp" ≠ "rp" from by decide,
               show "sp" ≠ "n" from by decide, ↓reduceIte, if_false]
    show (setReg s4 "sp" (s4.regs "sp" + BitVec.ofInt 64 8)).regs "sp" = _
    simp only [setReg, ↓reduceIte, if_true]
    rw [hs4_sp]
    show s.regs "sp" + BitVec.ofInt 64 8 = s.regs "sp" + 8
    bv_decide
  · -- rp = orig rp + 8
    show s7.regs "rp" = s.regs "rp" + 8
    simp only [hs7, setReg]
    show (setReg s5 "rp" (s5.regs "rp" + BitVec.ofInt 64 8)).regs "rp" = _
    simp only [setReg, show "rp" ≠ "n" from by decide, ↓reduceIte, if_true, if_false]
    rw [hs5_rp]
    show s.regs "rp" + BitVec.ofInt 64 8 = s.regs "rp" + 8
    bv_decide
  · -- n = orig n - 1
    show s7.regs "n" = s.regs "n" - 1
    simp only [hs7, setReg, ↓reduceIte, if_true]
    have hs6_n : s6.regs "n" = s.regs "n" := by
      simp only [hs6, setReg, show "n" ≠ "rp" from by decide, ↓reduceIte, if_false]
      simp only [hs5, setReg, show "n" ≠ "sp" from by decide, ↓reduceIte, if_false]
      show (storeMem s3 _ _).regs "n" = _
      simp only [storeMem_regs]
      simp [hs3, hs2, hs1, setReg,
            show "n" ≠ "out" from by decide,
            show "n" ≠ "next" from by decide,
            show "n" ≠ "cur" from by decide]
    rw [hs6_n]
    show s.regs "n" - BitVec.ofInt 64 1 = s.regs "n" - 1
    bv_decide

/-- `rshiftLoopBody` is straight-line. -/
theorem rshiftLoopBody_straightLine : InstrR.bodyIsStraightLine rshiftLoopBody := by
  simp only [rshiftLoopBody, loadAt0, shrdCopn, storeAt0, binImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `rshiftLoopBody` is non-control. -/
theorem rshiftLoopBody_nonControl : ∀ i ∈ rshiftLoopBody, i.isNonControl := by
  intro i hi
  simp only [rshiftLoopBody, loadAt0, shrdCopn, storeAt0, binImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-- Forward one-iteration rule for the rshift loop. -/
theorem bignumExecFuel_rshiftLoop_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec rshiftLoopBody s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond rshiftLoopBody] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond rshiftLoopBody] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) rshiftLoopBody s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f rshiftLoopBody s
        rshiftLoopBody_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) rshiftLoopBody [.Cwhile [] cond rshiftLoopBody]
        rshiftLoopBody_nonControl s s_mid s' hsl hrec]

/-! #### Loop induction (`mpnAddN_loop`-shaped, two-limb precondition)

The induction is on `as` with `|as| ≥ 1`.  Base case `|as| = 1`:
`n = 0`, exit.  Step case `as = w₀ :: w₁ :: rest`: do one iteration
(`shrd64 w₀ w₁ k`), recurse on `w₁ :: rest`. -/

/-- `shrd64` definitional unfold; for `0 < k < 64`, `k.toNat % 64 = k`. -/
theorem shrd64_unfold (cur next k : BitVec 64) :
    shrd64 cur next k = (cur >>> (k.toNat % 64)) ||| (next <<< (64 - k.toNat % 64)) :=
  rfl

/-- The loop, by induction on the limb list with two-limb precondition. -/
theorem mpnRShift_loop :
    ∀ (as : List (BitVec 64)) (s : BignumState) (k : Nat) (extra : Nat),
      0 < k → k < 64 →
      as.length ≥ 1 →
      s.regs "n" = BitVec.ofNat 64 (as.length - 1) →
      s.regs "k" = BitVec.ofNat 64 k →
      memHoldsLimbs s.mem (regAddr s "sp") as →
      MemoryModel.Disjoint (range (regAddr s "rp") (8 * as.length))
        (range (regAddr s "sp") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * (as.length - 1) + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) rshiftLoopBody] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "rp")
          ((bitShiftRight k as).take (as.length - 1)) ∧
        s'.regs "sp" = s.regs "sp" + BitVec.ofNat 64 (8 * (as.length - 1)) ∧
        s'.regs "rp" = s.regs "rp" + BitVec.ofNat 64 (8 * (as.length - 1)) ∧
        s'.regs "k"  = BitVec.ofNat 64 k ∧
        (∀ b, MemoryModel.Disjoint (range b 8)
              (range (regAddr s "rp") (8 * as.length)) →
            load64Mem s'.mem b = load64Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro _ _ _ _ _ hlen _ _ _ _
    simp at hlen
  | cons w rest ih =>
    intro s k extra hkpos hk _hlen hn hkreg hmem hdo
    cases rest with
    | nil =>
      -- Base: as = [w], n = 0, no iterations.
      have hn0 : s.regs "n" = 0 := by simpa [List.length_cons, List.length_nil] using hn
      refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * ([w].length - 1) + 3 + extra = extra + 3 := by
          simp only [List.length_cons, List.length_nil]; omega
        rw [hfuel]
        exact bignumExecFuel_loop_exit emptyRegistry extra _ rshiftLoopBody s
          (evalPExpr_loopCond_false s hn0)
      · simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel,
                   List.take_zero, memHoldsLimbs]
      · show s.regs "sp" = s.regs "sp" + BitVec.ofNat 64 (8 * ([w].length - 1))
        simp [List.length_cons, List.length_nil]
      · show s.regs "rp" = s.regs "rp" + BitVec.ofNat 64 (8 * ([w].length - 1))
        simp [List.length_cons, List.length_nil]
      · exact hkreg
      · intro b _; rfl
    | cons w' rest' =>
      -- Step: as = w :: w' :: rest', |as| = |rest'| + 2 ≥ 2.
      set L : Nat := rest'.length with hL_def
      have hlen_eq : (w :: w' :: rest').length = L + 2 := by
        simp [List.length_cons, hL_def]
      -- Bound (no wraparound).
      have hsize : 8 * (L + 2) ≤ 2 ^ 64 := by
        rcases Nat.eq_zero_or_pos (8 * (L + 2)) with h0 | hpos
        · omega
        · have h_lt := disjoint_range_lt (regAddr s "rp") (regAddr s "sp")
            (8 * (w :: w' :: rest').length) (by simp only [hlen_eq]; omega)
            (by simpa using hdo)
          rw [hlen_eq] at h_lt
          omega
      have hLsucc : L + 1 < 2 ^ 64 := by omega
      -- n = ofNat (L+1) ≠ 0.
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]
        have hsub : (w :: w' :: rest').length - 1 = L + 1 := by
          simp only [hlen_eq]; omega
        rw [hsub]
        exact ofNat64_succ_ne_zero L hLsucc
      -- memory: head load gives w, tail's head load gives w'.
      obtain ⟨hmem_head, hmem_tail⟩ := hmem
      obtain ⟨hmem_w', hmem_rest'⟩ := hmem_tail
      have hsp8 : UInt64.ofNat (s.regs "sp" + 8).toNat = regAddr s "sp" + 8 := by
        exact regAddr_advance _
      have hmem_w'_at_sp8 :
          load64Mem s.mem (UInt64.ofNat (s.regs "sp" + 8).toNat)
            = some (UInt64.ofNat w'.toNat) := by
        rw [hsp8]; exact hmem_w'
      -- One iteration.
      obtain ⟨s1, hs1, hs1_mem, hs1_k, hs1_sp, hs1_rp, hs1_n⟩ :=
        bignumExec_rshiftLoopBody_step s w w' hmem_head hmem_w'_at_sp8
      set sp0 : UInt64 := regAddr s "sp" with hsp0_def
      set rp0 : UInt64 := regAddr s "rp" with hrp0_def
      have hra_sp : regAddr s1 "sp" = sp0 + 8 := by
        show UInt64.ofNat (s1.regs "sp").toNat = _
        rw [hs1_sp]
        rw [show s.regs "sp" + 8 = s.regs "sp" + BitVec.ofNat 64 8 from by
              apply BitVec.eq_of_toNat_eq; simp]
        rw [hsp0_def, regAddr]
        exact Mpn.AddPrototype.regAddr_advance_at (s.regs "sp") 8
      have hra_rp : regAddr s1 "rp" = rp0 + 8 := by
        show UInt64.ofNat (s1.regs "rp").toNat = _
        rw [hs1_rp]
        rw [show s.regs "rp" + 8 = s.regs "rp" + BitVec.ofNat 64 8 from by
              apply BitVec.eq_of_toNat_eq; simp]
        rw [hrp0_def, regAddr]
        exact Mpn.AddPrototype.regAddr_advance_at (s.regs "rp") 8
      -- Memory after iteration: a single store at rp0.
      have hmem1 : s1.mem = s.mem.store64 rp0
          (UInt64.ofNat (shrd64 w w' (s.regs "k")).toNat) := by
        simpa [hrp0_def, regAddr] using hs1_mem
      -- Original memory at sp+8 holds (w' :: rest').
      have hmem_orig_sp8 : memHoldsLimbs s.mem (sp0 + 8) (w' :: rest') := by
        refine ⟨?_, ?_⟩
        · -- load at sp0+8 = w'
          show load64Mem s.mem (sp0 + 8) = some (UInt64.ofNat w'.toNat)
          rw [← hsp8]
          exact hmem_w'_at_sp8
        · -- rest' at (sp0+8)+8 = sp0+16
          show memHoldsLimbs s.mem (sp0 + 8 + 8) rest'
          have : sp0 + 8 + 8 = regAddr s "sp" + 8 + 8 := rfl
          rw [this]
          -- hmem_rest' : memHoldsLimbs s.mem (regAddr s "sp" + 8 + 8) rest'
          exact hmem_rest'
      -- Disjointness of store at rp0 from the sp+8 area (8*|w'::rest'| bytes).
      have hdoa_store_sp8tail :
          MemoryModel.Disjoint (range rp0 8) (range (sp0 + 8) (8 * (w' :: rest').length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdo
        · exact range_head_subset rp0 (w' :: rest').length x
            (by simpa [List.length_cons] using h)
        · exact range_shift_subset sp0 (w' :: rest').length x
            (by simpa [List.length_cons] using h)
      have hmem1' : memHoldsLimbs s1.mem (regAddr s1 "sp") (w' :: rest') := by
        rw [hra_sp, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (sp0 + 8) rp0 _ (w' :: rest')
          hdoa_store_sp8tail hmem_orig_sp8
      -- Disjointness for IH at the new sp/rp.
      have hdo1 : MemoryModel.Disjoint
          (range (regAddr s1 "rp") (8 * (w' :: rest').length))
          (range (regAddr s1 "sp") (8 * (w' :: rest').length)) := by
        rw [hra_rp, hra_sp]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdo
        · exact range_shift_subset rp0 (w' :: rest').length x
            (by simpa [List.length_cons] using h)
        · exact range_shift_subset sp0 (w' :: rest').length x
            (by simpa [List.length_cons] using h)
      have hk1 : s1.regs "k" = BitVec.ofNat 64 k := by rw [hs1_k, hkreg]
      -- n_new = ofNat (|w'::rest'| - 1) = ofNat L.
      have hn1 : s1.regs "n" = BitVec.ofNat 64 ((w' :: rest').length - 1) := by
        rw [hs1_n, hn]
        have h_eq : (w :: w' :: rest').length - 1 = L + 1 := by
          simp only [hlen_eq]; omega
        rw [h_eq]
        have hL_eq : (w' :: rest').length - 1 = L := by
          simp only [List.length_cons, hL_def]; omega
        rw [hL_eq]
        exact ofNat64_succ_sub_one L hLsucc
      have hlen1 : (w' :: rest').length ≥ 1 := by simp [List.length_cons]
      obtain ⟨s', hs', hs'_mem, hs'_sp, hs'_rp, hs'_k, hs'_frame⟩ :=
        ih s1 k extra hkpos hk hlen1 hn1 hk1 hmem1' hdo1
      refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- Fuel.
        have hfuel : 2 * ((w :: w' :: rest').length - 1) + 3 + extra
            = (2 * ((w' :: rest').length - 1) + 2 + extra) + 3 := by
          have h1 : (w :: w' :: rest').length - 1 = L + 1 := by
            simp only [hlen_eq]; omega
          have h2 : (w' :: rest').length - 1 = L := by
            simp only [List.length_cons, hL_def]; omega
          rw [h1, h2]; ring
        rw [hfuel]
        refine bignumExecFuel_rshiftLoop_step emptyRegistry
          (2 * ((w' :: rest').length - 1) + 2 + extra) _ s s1 s'
          (evalPExpr_loopCond_true s hn_ne) hs1 ?_
        have hfuel_eq : 2 * ((w' :: rest').length - 1) + 2 + extra + 1
                      = 2 * ((w' :: rest').length - 1) + 3 + extra := by omega
        rw [hfuel_eq]
        exact hs'
      · -- Memory at rp0: head limb = shrd64 w w' k; tail by IH.
        rw [hmem1] at hs'_frame
        have hsep : MemoryModel.Disjoint (range rp0 8) (range (rp0 + 8) (8 * (L + 1))) :=
          range_op_head_tail_disjoint rp0 (L + 1) (by omega)
        refine ⟨?_, ?_⟩
        · -- Head at rp0.
          rw [hs'_frame rp0 (by rw [hra_rp]
                                have : (w' :: rest').length = L + 1 := by
                                  simp [List.length_cons, hL_def]
                                rw [this]
                                exact hsep)]
          have hread := load64Mem_store64_same s.mem rp0
            (UInt64.ofNat (shrd64 w w' (s.regs "k")).toNat)
          rw [hread]
          rw [hkreg]
          -- bitShiftRight unfolds: (w :: w' :: rest') → ((w>>>r) ||| (w'<<<(64-r))) :: ...
          show some (UInt64.ofNat (shrd64 w w' (BitVec.ofNat 64 k)).toNat) = some _
          congr 1
          have hmod : (BitVec.ofNat 64 k).toNat % 64 = k := ofNat_bv_toNat_mod k hk
          show UInt64.ofNat (shrd64 w w' (BitVec.ofNat 64 k)).toNat
              = UInt64.ofNat
                  ((bitShiftRight k (w :: w' :: rest')).take ((w :: w' :: rest').length - 1)).head!.toNat
          congr 1
          show (shrd64 w w' (BitVec.ofNat 64 k)).toNat = _
          show ((w >>> ((BitVec.ofNat 64 k).toNat % 64))
                  ||| (w' <<< (64 - (BitVec.ofNat 64 k).toNat % 64))).toNat = _
          rw [hmod]
          -- (w :: w' :: rest').length - 1 ≥ 1, so take = h::tail and head! = h.
          have hlen_sub : (w :: w' :: rest').length - 1 = rest'.length + 1 := by
            simp [List.length_cons]
          rw [hlen_sub]
          simp only [bitShiftRight, List.take_succ_cons, List.head!]
        · -- Tail at rp0 + 8 = regAddr s1 "rp" via IH.
          have hthis := hs'_mem
          rw [hra_rp] at hthis
          -- IH: memHoldsLimbs s'.mem (rp0+8) ((bitShiftRight k (w'::rest')).take ((w'::rest').length - 1))
          -- Goal: memHoldsLimbs s'.mem (rp0+8) (List.take rest'.length (bitShiftRight k (w'::rest')))
          -- (w'::rest').length - 1 = rest'.length.
          have hlen' : (w' :: rest').length - 1 = rest'.length := by
            simp [List.length_cons]
          rw [hlen'] at hthis
          exact hthis
      · -- sp = orig sp + 8 * (|as| - 1).
        rw [hs'_sp, hs1_sp]
        show s.regs "sp" + 8 + BitVec.ofNat 64 (8 * ((w' :: rest').length - 1)) =
          s.regs "sp" + BitVec.ofNat 64 (8 * ((w :: w' :: rest').length - 1))
        have heq : (8 : BitVec 64) + BitVec.ofNat 64 (8 * ((w' :: rest').length - 1))
                 = BitVec.ofNat 64 (8 * ((w :: w' :: rest').length - 1)) := by
          have h1 : (w :: w' :: rest').length - 1 = L + 1 := by
            simp only [hlen_eq]; omega
          have h2 : (w' :: rest').length - 1 = L := by
            simp only [List.length_cons, hL_def]; omega
          rw [h1, h2]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                     show ((8 : BitVec 64).toNat) = 8 from rfl]
          omega
        rw [← heq]; bv_decide
      · -- rp = orig rp + 8 * (|as| - 1).
        rw [hs'_rp, hs1_rp]
        show s.regs "rp" + 8 + BitVec.ofNat 64 (8 * ((w' :: rest').length - 1)) =
          s.regs "rp" + BitVec.ofNat 64 (8 * ((w :: w' :: rest').length - 1))
        have heq : (8 : BitVec 64) + BitVec.ofNat 64 (8 * ((w' :: rest').length - 1))
                 = BitVec.ofNat 64 (8 * ((w :: w' :: rest').length - 1)) := by
          have h1 : (w :: w' :: rest').length - 1 = L + 1 := by
            simp only [hlen_eq]; omega
          have h2 : (w' :: rest').length - 1 = L := by
            simp only [List.length_cons, hL_def]; omega
          rw [h1, h2]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                     show ((8 : BitVec 64).toNat) = 8 from rfl]
          omega
        rw [← heq]; bv_decide
      · exact hs'_k
      · -- Frame: bb disjoint from (rp, 8|as|).
        intro bb hbb
        rw [hmem1] at hs'_frame
        -- bb ⊥ (rp1, 8|w'::rest'|) where rp1 = rp + 8.
        have hbb_tail : MemoryModel.Disjoint (range bb 8)
            (range (regAddr s1 "rp") (8 * (w' :: rest').length)) := by
          rw [hra_rp]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_shift_subset rp0 (w' :: rest').length x
            (by simpa [List.length_cons] using h)
        rw [hs'_frame bb hbb_tail]
        -- bb ⊥ (rp0, 8) since rp0 ∈ (rp, 8|as|).
        have hbb_head : MemoryModel.Disjoint (range bb 8) (range rp0 8) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_head_subset rp0 (w' :: rest').length x
            (by simpa [List.length_cons] using h)
        rw [load64Mem_store64_disjoint s.mem bb rp0 _ hbb_head]

/-! #### RShiftLoopOblg discharged -/

/-- **The rshift loop residual, fully proved.**  Direct corollary of
    `mpnRShift_loop`. -/
theorem RShiftLoopOblg_proof : RShiftLoopOblg := by
  intro s as k extra hkpos hk hlen hn hkreg hmem hdo
  exact mpnRShift_loop as s k extra hkpos hk hlen hn hkreg hmem hdo

/-- **The `mpn_rshift_loop_obligation` residual is closed.**  Direct
    corollary of `RShiftLoopOblg_proof`. -/
theorem mpn_rshift_loop_obligation_proof : mpn_rshift_loop_obligation :=
  RShiftLoopOblg_proof

/-- **`MpnRShiftJasminRefines` lifted from sorry-free residual to a proved
    fact.** -/
theorem MpnRShiftJasminRefines_proved : MpnRShiftJasminRefines :=
  RShiftLoopOblg_proof

/-! ### §4f  Bridge reduction (spill tail) — rshift

The reduction `RShiftLoopOblg → MpnRShiftRefinesStmt`: handle the
post-loop spill tail (three straight-line instructions: `top := [sp+0];
spill := SHR_64(top, k); rp[0] := spill`).  After the loop, register
`sp` points at `original_sp + 8·(|as|-1)`, which holds the top limb of
`as`; the spill computes `top >>> k`, which is exactly the `|as|`-th
limb of `bitShiftRight k as`. -/

/-- Define the trailing-limb function for rshift: the last limb of
    `bitShiftRight k as` is the last limb of `as` shifted right by `k`. -/
def rshiftTrailLimb (k : Nat) (as : List (BitVec 64)) : BitVec 64 :=
  match as with
  | [] => 0
  | a :: rest => (rest.foldl (fun _ w => w) a) >>> k

/-- Specialization: `(rest.foldl (fun _ w => w) a)` for `rest = w :: rest'`
    equals `rest'.foldl (fun _ w => w) w`. -/
private theorem foldl_last_cons (a w : BitVec 64) (rest' : List (BitVec 64)) :
    (w :: rest').foldl (fun _ x => x) a = rest'.foldl (fun _ x => x) w := by
  simp [List.foldl]

/-- The trailing limb formula computed from the last element of `as`. -/
theorem rshiftTrailLimb_eq (k : Nat) (as : List (BitVec 64)) (h : as.length ≥ 1) :
    rshiftTrailLimb k as = (as.foldl (fun _ w => w) (0 : BitVec 64)) >>> k := by
  cases as with
  | nil => simp at h
  | cons a rest =>
    simp only [rshiftTrailLimb, List.foldl]

/-- **Last limb of `bitShiftRight k as` equals `(last of as) >>> k`.**
    This is the structural fact: `bitShiftRight` preserves the list length,
    and its last entry is just the last limb of `as` shifted right by `k`. -/
theorem bitShiftRight_last (k : Nat) (as : List (BitVec 64)) (h : as.length ≥ 1) :
    ∀ a, ((as.foldl (fun _ x => x) a) >>> k : BitVec 64) =
      (match as with
       | [] => a >>> k
       | x :: rest => (rest.foldl (fun _ w => w) x) >>> k) := by
  cases as with
  | nil => simp at h
  | cons a rest =>
    intro a₀
    simp only [List.foldl]

/-- `bitShiftRight k as` has the same length as `as`. -/
theorem bitShiftRight_length (k : Nat) (as : List (BitVec 64)) :
    (bitShiftRight k as).length = as.length := by
  induction as with
  | nil => simp [bitShiftRight]
  | cons a rest ih =>
    cases rest with
    | nil => simp [bitShiftRight]
    | cons a' rest' =>
      simp only [bitShiftRight, List.length_cons]
      have hih : (bitShiftRight k (a' :: rest')).length = (a' :: rest').length := ih
      simp only [List.length_cons] at hih
      omega

/-- The structural recombination: `bitShiftRight k as` = `take (|as|-1) ++ [trail]`
    in the `memHoldsLimbs` sense.  Given memory holding the take prefix at `base`
    and the trail at `base + 8*(|as|-1)`, the full predicate holds. -/
theorem memHoldsLimbs_bsr_recombine (k : Nat)
    (m : MemoryModel.Mem) (base : UInt64)
    (as : List (BitVec 64)) (h : as.length ≥ 1)
    (htake : memHoldsLimbs m base ((bitShiftRight k as).take (as.length - 1)))
    (hlast : load64Mem m (base + UInt64.ofNat (8 * (as.length - 1)))
              = some (UInt64.ofNat ((as.foldl (fun _ w => w) (0 : BitVec 64)) >>> k).toNat)) :
    memHoldsLimbs m base (bitShiftRight k as) := by
  induction as generalizing base with
  | nil => simp at h
  | cons a rest ih =>
    cases rest with
    | nil =>
      -- as = [a]; bitShiftRight k [a] = [a >>> k]; take 0 = [].
      simp only [bitShiftRight, memHoldsLimbs]
      refine ⟨?_, trivial⟩
      -- hlast: load at base + ofNat (8 * 0) = (foldl 0 [a]) >>> k = a >>> k.
      simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel,
                 Nat.mul_zero, List.foldl] at hlast
      have hcast : base + UInt64.ofNat 0 = base := by
        show base + 0 = base
        simp
      rw [hcast] at hlast
      exact hlast
    | cons a' rest' =>
      -- as = a :: a' :: rest'.
      -- bitShiftRight k (a :: a' :: rest') = head :: bitShiftRight k (a' :: rest').
      -- take prefix = head :: (bitShiftRight k (a' :: rest')).take (|a' :: rest'| - 1).
      -- The take is itself stored: head at base, tail at base+8.
      have hlen : (a :: a' :: rest').length - 1 = rest'.length + 1 := by
        simp [List.length_cons]
      rw [hlen] at htake
      simp only [bitShiftRight, List.take] at htake
      obtain ⟨hh, ht⟩ := htake
      simp only [bitShiftRight, memHoldsLimbs]
      refine ⟨hh, ?_⟩
      -- IH on (a' :: rest') at base + 8.
      have hlen1 : (a' :: rest').length ≥ 1 := by simp [List.length_cons]
      apply ih (base + 8) hlen1
      · -- htake_tail : memHoldsLimbs m (base + 8) ((bitShiftRight k (a' :: rest')).take ((a' :: rest').length - 1)).
        have hlen' : (a' :: rest').length - 1 = rest'.length := by
          simp [List.length_cons]
        rw [hlen']
        convert ht using 1
      · -- hlast': load at (base+8) + 8*(|a' :: rest'|-1) = (foldl 0 (a' :: rest')) >>> k.
        have hlen' : (a' :: rest').length - 1 = rest'.length := by
          simp [List.length_cons]
        rw [hlen']
        -- The address: (base + 8) + ofNat (8 * rest'.length) = base + ofNat (8 * (rest'.length + 1)).
        have haddr : (base + 8) + UInt64.ofNat (8 * rest'.length)
                    = base + UInt64.ofNat (8 * (rest'.length + 1)) := by
          apply UInt64.toNat.inj
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat',
                     show ((8 : UInt64).toNat) = 8 from rfl]
          omega
        rw [haddr]
        -- hlast: load at base + ofNat (8 * (|a :: a' :: rest'|-1)) = (foldl 0 (a :: a' :: rest')) >>> k.
        have hlen_orig : (a :: a' :: rest').length - 1 = rest'.length + 1 := hlen
        rw [hlen_orig] at hlast
        -- foldl (fun _ w => w) 0 (a :: a' :: rest') = foldl (fun _ w => w) a' rest' (the last element).
        -- foldl (fun _ w => w) 0 (a' :: rest') = foldl (fun _ w => w) a' rest'.
        have hfold_eq : (a :: a' :: rest').foldl (fun _ w => w) (0 : BitVec 64)
                      = (a' :: rest').foldl (fun _ w => w) (0 : BitVec 64) := by
          simp only [List.foldl]
        rw [hfold_eq] at hlast
        exact hlast

/-- For `0 < k < 64`, `mpnShiftRight as k = bitShiftRight k as`. -/
theorem mpnShiftRight_simple (as : List (BitVec 64)) (k : Nat)
    (_hkpos : 0 < k) (hk : k < 64) :
    mpnShiftRight as k = bitShiftRight k as := by
  unfold mpnShiftRight
  rw [show k / 64 = 0 from Nat.div_eq_of_lt hk,
      show k % 64 = k from Nat.mod_eq_of_lt hk]
  simp

/-- **Top-limb lookup**: in a memory that holds the limb list `as` at base
    `sp`, the load at `sp + 8*(|as|-1)` returns the last limb of `as` —
    equivalently, `as.foldl (fun _ w => w) 0` for `|as| ≥ 1`. -/
theorem memHoldsLimbs_top (m : MemoryModel.Mem) (sp : UInt64)
    (as : List (BitVec 64)) (h : as.length ≥ 1)
    (hmem : memHoldsLimbs m sp as) :
    load64Mem m (sp + UInt64.ofNat (8 * (as.length - 1)))
      = some (UInt64.ofNat ((as.foldl (fun _ w => w) (0 : BitVec 64)).toNat)) := by
  induction as generalizing sp with
  | nil => simp at h
  | cons w rest ih =>
    cases rest with
    | nil =>
      -- as = [w]; foldl 0 [w] = w; sp + 0 = sp; load = w.
      simp only [List.foldl, List.length_cons, List.length_nil,
                 Nat.add_sub_cancel, Nat.mul_zero] at *
      have heq : sp + UInt64.ofNat 0 = sp := by
        show sp + 0 = sp
        simp
      rw [heq]
      exact hmem.1
    | cons w' rest' =>
      -- IH on (w' :: rest') at sp + 8.
      obtain ⟨_, hmem_tail⟩ := hmem
      have hlen1 : (w' :: rest').length ≥ 1 := by simp [List.length_cons]
      have hih := ih (sp + 8) hlen1 hmem_tail
      -- foldl (fun _ x => x) 0 (w :: w' :: rest') = foldl ... 0 (w' :: rest')
      have hfold_eq : (w :: w' :: rest').foldl (fun _ x => x) (0 : BitVec 64)
                    = (w' :: rest').foldl (fun _ x => x) (0 : BitVec 64) := by
        simp only [List.foldl]
      rw [hfold_eq]
      -- Address: sp + 8*(|w :: w' :: rest'| - 1) = (sp + 8) + 8*(|w' :: rest'| - 1).
      have haddr : sp + UInt64.ofNat (8 * ((w :: w' :: rest').length - 1))
                = (sp + 8) + UInt64.ofNat (8 * ((w' :: rest').length - 1)) := by
        apply UInt64.toNat.inj
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat',
                   show ((8 : UInt64).toNat) = 8 from rfl,
                   List.length_cons]
        omega
      rw [haddr]
      exact hih

/-! #### Helpers for the rshift spill tail (3 instructions). -/

/-- The post-loop spill tail of `rshiftBody` (3 instructions). -/
private def rshiftSpillTail : List InstrR :=
  [ loadAt0 "top" "sp"
  , shrCopn "spill" "top" "k"
  , storeAt0 "rp" "spill" ]

private theorem rshiftSpillTail_straightLine :
    InstrR.bodyIsStraightLine rshiftSpillTail := by
  simp only [rshiftSpillTail, loadAt0, shrCopn, storeAt0,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Body decomposes as `[Cwhile]` ++ spill tail. -/
private theorem rshiftBody_decompose :
    rshiftBody = [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) rshiftLoopBody]
      ++ rshiftSpillTail := by
  rfl

/-- The rshift spill tail runs from a state holding the top limb `top` at
    register `sp` (offset 0) and `k = ofNat k` in `k`, to a state whose
    memory differs from the input only by a single store at `rp + 0` of
    `top >>> k`. -/
theorem rshiftSpillTail_step (s : BignumState) (top : BitVec 64) (k : Nat)
    (hkpos : 0 < k) (hk : k < 64)
    (htop : load64Mem s.mem (regAddr s "sp") = some (UInt64.ofNat top.toNat))
    (hkreg : s.regs "k" = BitVec.ofNat 64 k) :
    ∃ s', bignumExec rshiftSpillTail s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "rp")
        (UInt64.ofNat (top >>> k).toNat) := by
  -- 1. top := [sp + 0]
  have h1 : execInstr s (loadAt0 "top" "sp") = some (setReg s "top" top) :=
    execInstr_loadAt0_lshift s "top" "sp" top htop
  set s1 : BignumState := setReg s "top" top with hs1
  -- 2. spill := SHR_64(top, k)
  have hs1_top : s1.regs "top" = top := by simp [hs1, setReg]
  have hs1_k : s1.regs "k" = BitVec.ofNat 64 k := by
    simp [hs1, setReg, hkreg, show "k" ≠ "top" from by decide]
  have h2 : execInstr s1 (shrCopn "spill" "top" "k") = some
      (setReg s1 "spill" (BignumExec.shr64 (s1.regs "top") (s1.regs "k"))) :=
    execInstr_shrCopn s1 "spill" "top" "k"
  set s2 : BignumState := setReg s1 "spill" (BignumExec.shr64 (s1.regs "top")
                              (s1.regs "k")) with hs2
  have hs2_spill : s2.regs "spill" = top >>> k := by
    simp only [hs2, setReg, ↓reduceIte, if_true]
    rw [hs1_top, hs1_k]
    -- shr64 top (ofNat k) = top >>> (k.toNat % 64) = top >>> k.
    show top >>> ((BitVec.ofNat 64 k).toNat % 64) = top >>> k
    rw [ofNat_bv_toNat_mod k hk]
  have hs2_rp : s2.regs "rp" = s.regs "rp" := by
    simp only [hs2, setReg, show "rp" ≠ "spill" from by decide, ↓reduceIte, if_false]
    simp [hs1, setReg, show "rp" ≠ "top" from by decide]
  have hs2_mem : s2.mem = s.mem := by
    simp only [hs2, hs1, setReg]
  -- 3. [rp + 0] := spill
  have h3 : execInstr s2 (storeAt0 "rp" "spill") = some
              (storeMem s2 (UInt64.ofNat (s2.regs "rp").toNat)
                (UInt64.ofNat (s2.regs "spill").toNat)) :=
    execInstr_storeAt0_lshift s2 "rp" "spill"
  set s3 : BignumState := storeMem s2 (UInt64.ofNat (s2.regs "rp").toNat)
            (UInt64.ofNat (s2.regs "spill").toNat) with hs3
  -- Compose.
  have step (i : InstrR) (s' s'' : BignumState)
      (hi : execInstr s' i = some s'') :
      bignumExec [i] s' = some s'' := by
    simp only [bignumExec, hi]
  have e12 := bignumExec_append_some_local _ _ s s1 s2 (step _ _ _ h1) (step _ _ _ h2)
  have e123 := bignumExec_append_some_local _ _ s s2 s3 e12 (step _ _ _ h3)
  refine ⟨s3, ?_, ?_⟩
  · show bignumExec rshiftSpillTail s = some s3
    show bignumExec [_, _, _] s = some s3
    convert e123 using 1
  · show s3.mem = s.mem.store64 (regAddr s "rp")
        (UInt64.ofNat (top >>> k).toNat)
    simp only [hs3, storeMem_mem, hs2_mem, hs2_rp, hs2_spill]
    rfl

/-! #### RShiftBridgeAssembly: tighter assembly residual

The full bridge reduction `RShiftLoopOblg → MpnRShiftRefinesStmt`
chains the loop with the spill tail.  We pin the assembly residual
as `RShiftBridgeAssembly` (which closes both pieces plus the
fuel-accounting closure), then prove it. -/

/-- Tighter sorry-free residual: assembly of the `Cwhile` + spill-tail
    run, with the `rp` register advanced to `original_rp + 8·(|as|-1)`.
    Captures the stitching obligation for the full body. -/
def RShiftBridgeAssembly : Prop :=
  ∀ (s : BignumState) (as : List (BitVec 64)) (k : Nat) (fuel : Nat),
    0 < k → k < 64 →
    as.length ≥ 1 →
    s.regs "n" = BitVec.ofNat 64 (as.length - 1) →
    s.regs "k" = BitVec.ofNat 64 k →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "sp").toNat) as →
    MemoryModel.Disjoint
      (range (UInt64.ofNat (s.regs "rp").toNat) (8 * as.length))
      (range (UInt64.ofNat (s.regs "sp").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 4 →
    ∃ s' : BignumState, bignumExecFuel emptyRegistry fuel rshiftBody s = some s' ∧
      -- take-(|as|-1) at original rp
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        ((bitShiftRight k as).take (as.length - 1)) ∧
      -- trailing spill at original rp + 8*(|as|-1)
      load64Mem s'.mem
          (UInt64.ofNat (s.regs "rp").toNat + UInt64.ofNat (8 * (as.length - 1)))
        = some (UInt64.ofNat ((as.foldl (fun _ w => w) (0 : BitVec 64)) >>> k).toNat)

/-- **Reduction `RShiftBridgeAssembly → rshift_bridge_reduction`**.  Closing
    the tighter assembly residual discharges `rshift_bridge_reduction` via
    `memHoldsLimbs_bsr_recombine` and `mpnShiftRight_simple`. -/
theorem rshift_bridge_reduction_of_assembly
    (h_asm : RShiftBridgeAssembly) :
    rshift_bridge_reduction := by
  intro _ s as k fuel hkpos hk hlen hn hkreg hmem hdo hfuel
  obtain ⟨s', hs'_exec, hs'_take, hs'_trail⟩ :=
    h_asm s as k fuel hkpos hk hlen hn hkreg hmem hdo hfuel
  refine ⟨s', hs'_exec, ?_⟩
  rw [mpnShiftRight_simple as k hkpos hk]
  exact memHoldsLimbs_bsr_recombine k _ _ as hlen hs'_take hs'_trail

/-! #### Closing `RShiftBridgeAssembly`

Chain the loop (`RShiftLoopOblg_proof`) with the 3-instruction spill
tail (`rshiftSpillTail_step`) via `bignumExecFuel_seq` (handles `Cwhile`
in the prefix) and the straight-line equivalence
`bignumExecFuel_eq_bignumExec_of_straightLine` for the tail. -/

/-- **`RShiftBridgeAssembly` discharged, axiom-clean.**
    Mirror of `LShiftBridgeAssembly_proof` but with no prelude (rshift's
    body has none) and a 3-instruction spill tail. -/
theorem RShiftBridgeAssembly_proof : RShiftBridgeAssembly := by
  intro s as k fuel hkpos hk hlen hn hkreg hmem hdo hfuel
  -- ===== Step 1: choose extra so fuel = 2*(|as|-1) + 4 + extra =====
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * (as.length - 1) + 4 + extra :=
    ⟨fuel - (2 * (as.length - 1) + 4), by omega⟩
  -- ===== Step 2: invoke RShiftLoopOblg_proof on s =====
  obtain ⟨s1, hs1_exec, hs1_take, hs1_sp, hs1_rp, hs1_k, hs1_frame⟩ :=
    RShiftLoopOblg_proof s as k extra hkpos hk hlen hn hkreg hmem hdo
  -- s1.regs "sp" = s.regs "sp" + ofNat (8*(|as|-1))
  -- s1.regs "rp" = s.regs "rp" + ofNat (8*(|as|-1))
  -- s1.regs "k"  = ofNat k.
  -- ===== Step 3: locate the top limb in s1.mem =====
  -- The top limb = as.foldl (fun _ w => w) 0  (the last element of as for |as|≥1).
  set top : BitVec 64 := as.foldl (fun _ w => w) (0 : BitVec 64) with htop_def
  -- Original memory at sp + 8*(|as|-1) holds the top limb.
  have hsp_top_orig :
      load64Mem s.mem (UInt64.ofNat (s.regs "sp").toNat
        + UInt64.ofNat (8 * (as.length - 1)))
      = some (UInt64.ofNat top.toNat) := by
    rw [htop_def]
    exact memHoldsLimbs_top s.mem _ as hlen hmem
  -- Now: in s1.mem, the top limb is still at sp + 8*(|as|-1) (preserved by hs1_frame).
  -- The store at rp doesn't overlap the sp area by hdo.
  have hdisj_top : MemoryModel.Disjoint
      (range (UInt64.ofNat (s.regs "sp").toNat + UInt64.ofNat (8 * (as.length - 1))) 8)
      (range (UInt64.ofNat (s.regs "rp").toNat) (8 * as.length)) := by
    -- The 8-byte block at sp + 8*(|as|-1) is inside (sp, 8|as|), which by hdo
    -- is disjoint from (rp, 8|as|).  Disjoint.symm + subset.
    have hsub : ∀ x, (range (UInt64.ofNat (s.regs "sp").toNat
                              + UInt64.ofNat (8 * (as.length - 1))) 8) x →
                     (range (UInt64.ofNat (s.regs "sp").toNat) (8 * as.length)) x := by
      intro x ⟨i, hi, hx⟩
      refine ⟨8 * (as.length - 1) + i, by omega, ?_⟩
      rw [hx]
      rw [UInt64.ofNat_add]
      ac_rfl
    refine disjoint_mono hsub (fun x h => h) hdo.symm
  have htop_at_s1 : load64Mem s1.mem (UInt64.ofNat (s.regs "sp").toNat
        + UInt64.ofNat (8 * (as.length - 1)))
      = some (UInt64.ofNat top.toNat) := by
    rw [hs1_frame _ hdisj_top]
    exact hsp_top_orig
  -- regAddr s1 "sp" = UInt64.ofNat (s1.regs "sp").toNat
  --   = UInt64.ofNat (s.regs "sp" + ofNat (8*(|as|-1))).toNat
  --   = UInt64.ofNat (s.regs "sp").toNat + UInt64.ofNat (8*(|as|-1)).
  have hra_s1_sp : regAddr s1 "sp"
      = UInt64.ofNat (s.regs "sp").toNat + UInt64.ofNat (8 * (as.length - 1)) := by
    show UInt64.ofNat (s1.regs "sp").toNat = _
    rw [hs1_sp]
    exact Mpn.AddPrototype.regAddr_advance_at (s.regs "sp") (8 * (as.length - 1))
  have hra_s1_rp : regAddr s1 "rp"
      = UInt64.ofNat (s.regs "rp").toNat + UInt64.ofNat (8 * (as.length - 1)) := by
    show UInt64.ofNat (s1.regs "rp").toNat = _
    rw [hs1_rp]
    exact Mpn.AddPrototype.regAddr_advance_at (s.regs "rp") (8 * (as.length - 1))
  -- ===== Step 4: invoke rshiftSpillTail_step on s1 =====
  have htop_at_s1' : load64Mem s1.mem (regAddr s1 "sp")
      = some (UInt64.ofNat top.toNat) := by
    rw [hra_s1_sp]
    exact htop_at_s1
  obtain ⟨s2, hs2_exec, hs2_mem⟩ :=
    rshiftSpillTail_step s1 top k hkpos hk htop_at_s1' hs1_k
  -- ===== Step 5: chain fuel: loop fuel = 2*(|as|-1)+3+extra, tail fuel = 1 =====
  have h_tail_fuel :
      bignumExecFuel emptyRegistry 1 rshiftSpillTail s1 = some s2 := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine emptyRegistry 0
          rshiftSpillTail s1 rshiftSpillTail_straightLine]
    exact hs2_exec
  have h_total :
      bignumExecFuel emptyRegistry ((2 * (as.length - 1) + 3 + extra) + 1)
        ([.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) rshiftLoopBody]
          ++ rshiftSpillTail) s = some s2 :=
    bignumExecFuel_seq emptyRegistry (2 * (as.length - 1) + 3 + extra) 1 _ _ _ _ _
      hs1_exec h_tail_fuel
  have hbody_eq :
      [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) rshiftLoopBody]
        ++ rshiftSpillTail = rshiftBody := rshiftBody_decompose.symm
  have hfuel_eq : (2 * (as.length - 1) + 3 + extra) + 1 = fuel := by omega
  rw [hbody_eq, hfuel_eq] at h_total
  -- ===== Step 6: package take/trail conclusions =====
  refine ⟨s2, h_total, ?_, ?_⟩
  · -- Take area at original rp.
    -- hs1_take : memHoldsLimbs s1.mem (regAddr s "rp")
    --             ((bitShiftRight k as).take (as.length - 1))
    -- After spill store at regAddr s1 "rp" = rp + 8*(|as|-1), the take area
    -- (rp, 8*(|as|-1)) is disjoint from the store.
    rw [hs2_mem]
    have hbound : 8 * (as.length - 1 + 1) ≤ 2 ^ 64 := by
      rcases Nat.eq_zero_or_pos (8 * as.length) with hL0 | hLpos
      · -- 8 * |as| = 0 → |as| = 0, but hlen ≥ 1.  Contradiction.
        have : as.length = 0 := by omega
        omega
      · have h_lt := disjoint_range_lt _ _ _ hLpos hdo
        have : as.length - 1 + 1 = as.length := by omega
        rw [this]; omega
    have hdisj_store :
        MemoryModel.Disjoint
          (range (regAddr s1 "rp") 8)
          (range (UInt64.ofNat (s.regs "rp").toNat)
            (8 * ((bitShiftRight k as).take (as.length - 1)).length)) := by
      rw [hra_s1_rp]
      have hlen_take : ((bitShiftRight k as).take (as.length - 1)).length
                      = as.length - 1 := by
        rw [List.length_take, bitShiftRight_length]; omega
      rw [hlen_take]
      -- We need (rp + ofNat 8*(|as|-1), 8) ⊥ (rp, 8*(|as|-1)).
      exact range_tail_head_disjoint (UInt64.ofNat (s.regs "rp").toNat) (as.length - 1) hbound
    -- hs1_take is at base = regAddr s "rp" (= UInt64.ofNat (s.regs "rp").toNat).
    have hs1_take' : memHoldsLimbs s1.mem
        (UInt64.ofNat (s.regs "rp").toNat)
        ((bitShiftRight k as).take (as.length - 1)) := by
      have : regAddr s "rp" = UInt64.ofNat (s.regs "rp").toNat := rfl
      rw [← this]
      exact hs1_take
    exact memHoldsLimbs_store64_frame s1.mem
      (UInt64.ofNat (s.regs "rp").toNat) (regAddr s1 "rp") _ _
      hdisj_store hs1_take'
  · -- Trail at rp + 8*(|as|-1).
    rw [hs2_mem]
    -- Store at regAddr s1 "rp" = rp + 8*(|as|-1), load at same address.
    rw [← hra_s1_rp, load64Mem_store64_same]

/-- **`rshift_bridge_reduction` discharged unconditionally.**  Composition of
    `rshift_bridge_reduction_of_assembly` with `RShiftBridgeAssembly_proof`. -/
theorem rshift_bridge_reduction_proof : rshift_bridge_reduction :=
  rshift_bridge_reduction_of_assembly RShiftBridgeAssembly_proof

/-- **`MpnRShiftRefinesStmt` discharged unconditionally** — the full bridge
    from the emitted Jasmin `rshiftBody` to the algorithm-level reference
    `mpnShiftRight`.  Composition of the loop obligation `RShiftLoopOblg_proof`
    with the bridge reduction `rshift_bridge_reduction_proof`. -/
theorem MpnRShiftRefinesStmt_proof : MpnRShiftRefinesStmt :=
  rshift_bridge_reduction_proof RShiftLoopOblg_proof
/-! ## §5  Final sanity: the emitted source compiles

We emit both functions and expect `jasminc` to accept the output.  At
the Lean level we verify the emission *succeeds* (every InstrR shape is
supported); the `jasminc`-exit-0 check is documented in the task ledger
as a manual gate.  See bench/mpn_shift_bench/ for the round-trip
harness analogue of `bench/glue_audit/`. -/

/-- Both kernels emit successfully. -/
example : lshiftEmitted.isSome ∧ rshiftEmitted.isSome := by
  refine ⟨?_, ?_⟩ <;> native_decide

end CatCrypt.Crypto.Jasmin.Mpn.ShiftPrototype
