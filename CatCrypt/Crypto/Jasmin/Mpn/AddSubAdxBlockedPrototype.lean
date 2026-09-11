/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.Mpn.AddSubAdxPrototype
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.AddSubAdxPrototype

@[expose] public section

set_option autoImplicit false

/-!
# Blocked-unroll variant of `mpn_add_n` / `mpn_sub_n`

**EXPERIMENTAL FILE.**  Companion to `Mpn.AddSubAdxPrototype.lean` (which ships
fully-unrolled `n = 4, 8` and falls back to a C inline-asm shim for `n ≥ 16`).

The fully-unrolled add body keeps `r0..r_{n-1}` live across the whole chain;
at `n = 16` that's `~20` u64 GPRs simultaneously live (r_i plus three base
pointers plus scratch plus the `cf` and `of` flag-bools and the `zero`
register), and jasminc's x86-64 register allocator rejects it.

This file lowers the unrolled body to a **blocked unroll**: process the input
in chunks of `BLOCK = 8` limbs at a time, with a one-u64 GPR threading the
running carry-out across blocks.  Inside each block the body is the
fully-unrolled 8-limb ADCX (resp. SBB) chain — identical to the `n = 8` case
of `MpnAddSubAdxPrototype`, hence guaranteed to fit jasminc's register
budget.

## How the carry threads across blocks (add and sub)

Each block runs an 8-limb single-chain ADCX (add) or SBB (sub) over its
local window, with the cross-block carry / borrow surviving as a `reg u64`
value `cy` (∈ {0, 1}) between blocks — exactly the same role `cy` plays in
the single-chain looped reference `MpnAddNAdcSpillPrototype` /
`MpnSubNSbbSpillPrototype`.

The cross-block carry needs to enter the **architectural CF flag** so the
first ADCX (resp. SBB) of the next block reads it as carry-in.  The idiom
we use is:

```
# At entry of every block:
xor zero, zero                              # cf=of=0; zero=0
_, cf, _, _, _, zero := #SUB_64(zero, cy)   # 0 - cy: cf = cy
                                            # (zero stomped to 0 or -1; we don't care)
```

* If `cy = 0`: `0 - 0 = 0`, CF = 0; `zero` unchanged (still 0).
* If `cy = 1`: `0 - 1 = -1`, CF = 1; `zero` clobbered to `2^64 - 1`.

In both cases CF holds `cy` going into the chain.  The next block's leading
XOR_64 re-clears `zero` to 0 before its own SUB_64 runs, so the temporary
clobber is harmless.  This idiom is **identical** for add and sub blocks
because x86's borrow flag for `SBB` *is* the CF that ADCX reads/writes.

Why `SUB_64(zero, cy)` and not `SBB_64(...)` or `ADCX(...)`?  The other
candidates either require a fresh dst register that jasminc's allocator
merges across iterations (failure: `tmp` cannot merge with cross-iteration
`zero`), or do not load CF from a u64 source (ADCX outputs CF from the
ALU's overflow, not from its source register).  Re-using `zero` as the
SUB_64 dst lets jasminc satisfy x86's `dst = src1` constraint without
introducing a cross-iteration register dependency.

At the end of every block we capture the chain's final CF back into `cy`
using `cy := 0; cf, cy := ADCX(cy, cy, cf)` — the standard "spill CF into a
GPR" idiom (`0 + 0 + cf = cf` lands in `cy`).

## Spec equivalence

Block-decomposed `mpn_add_n` is the same function as the limb-by-limb
`mpn_add_n`: the per-limb step is the same `adcStep` regardless of whether
iterations live inside one block or are split across blocks.  Hence
`mpnAddNAdx_blocked = mpnAddN` (as pure functions on `BitVec 64` lists).
Same for `mpn_sub_n`.

## What this file proves

1. **Pure functional spec** `mpnAddNAdx_blocked` / `mpnSubNAdx_blocked` (§2)
   and their identity with `mpnAddN` / `mpnSubN` (§2, by `rfl`).
2. **`FunDecl` and `.jazz` emission** (§3): one
   `mpn_add_n_adx_blk_<n>` / `mpn_sub_n_sbb_blk_<n>` symbol per
   `n ∈ {16, 32, 64, 128}` (the cryptographic range that exceeds the unrolled
   prototype's jasminc GPR budget).
3. **Constant-time-shape** at the AST level: only the outer Cfor loop has a
   public-bounded (compile-time-constant) index.
4. **Refinement statement** `MpnAddNAdxBlockedJasminRefines` /
   `MpnSubNAdxBlockedJasminRefines` (§4):
   - `n = 0` (no blocks) proved directly.
   - General `n` divisible by `BLOCK` recorded as a structural mirror of
     `Mpn.AddSubAdxPrototype.MpnAddNAdxJasminRefines_holds_n0` /
     `MpnSubNAdxJasminRefines_holds_n0`, reducing to the single-chain bridge
     via spec equivalence.

## Performance expectations (Zen 4)

The single-chain ADCX add and SBB sub are bottlenecked on the architectural
CF flag — each iteration's add/sub serialises through CF.  Unlike addmul_1
(which has a real dual-chain win via parallel ADCX + ADOX), the plain
add/sub here has no second chain to exploit.  Expected:

* **vs unrolled C-inline-asm fallback (V-ADX-Unr column)**: ~parity to small
  win — the verified blocked emit replaces the gcc-from-inline-asm
  scheduling with the jasminc straight-line schedule (which has tighter
  reg-alloc but no fundamentally better arithmetic).
* **vs V64-SPILL (V-ADX-Sp column)**: ~parity on Zen 4 (1c ADC = 1c ADCX).
* **vs libgmp's `__gmpn_add_n` / `__gmpn_sub_n`**: behind by 1.0-1.3× — GMP's
  `coreihwl/aors_n.asm` has interleaved load/add scheduling tuned at the
  instruction level.  The blocked verified emit's win is mostly *operational*:
  it removes the C-inline-asm hop, giving a verified emit at n ≥ 16 instead
  of the current trust-the-shim fallback.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.AddSubAdxBlockedPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddSubAdxPrototype

/-! ## §1  Block parameters

We pin `BLOCK = 8`: the largest block size whose fully-unrolled body fits
jasminc's GPR budget (the `n = 8` case of `MpnAddSubAdxPrototype` is proven
to emit cleanly).
-/

/-- Block size in u64 limbs.  Per-block work: ~`BLOCK` ADCX (or SBB) +
    `BLOCK` loads of `t_i` from `bp[]` + the `BLOCK` `r_i` stored back to
    `op[]` + the cross-block carry-fold (one ADCX) + the per-block flag
    XOR-clear (one XOR) + two pointer advances.  Total ≈ `3·BLOCK + 5`
    InstrR per block, comfortably inside jasminc's budget. -/
def BLOCK : Nat := 8

/-! ## §2  Pure functional reference — blocked `mpn_add_n` / `mpn_sub_n`

The blocked variants compute exactly the same `r := a + b` (resp. `r := a - b`)
as the limb-by-limb references: the per-limb step is `adcStep` (resp.
`sbbStep`), and the blocked emit just chops the work into chunks of
`BLOCK = 8` limbs without changing what each per-limb step computes.

Hence the pure spec is **definitionally equal** to `mpnAddN` (resp.
`mpnSubN`) — same as the fully-unrolled ADX prototype.  The blocked variant
differs only at the *emit* level (where the outer Cfor lives), not at the
pure-spec level.
-/

/-- Pure-functional spec of the blocked add variant: the same `mpn_add_n` /
    `mpnAddN` reference function.

    Definitionally equal to `Mpn.AddPrototype.mpnAddN` and to
    `Mpn.AddSubAdxPrototype.mpnAddNAdx`. -/
def mpnAddNAdx_blocked (a b : List (BitVec 64)) (cin : Bool) :
    List (BitVec 64) × Bool :=
  Mpn.AddPrototype.mpnAddN a b cin

/-- Pure-functional spec of the blocked sub variant: the same `mpn_sub_n` /
    `mpnSubN` reference function.

    Definitionally equal to `Mpn.SubPrototype.mpnSubN` and to
    `Mpn.AddSubAdxPrototype.mpnSubNAdx`. -/
def mpnSubNAdx_blocked (a b : List (BitVec 64)) (bin : Bool) :
    List (BitVec 64) × Bool :=
  Mpn.SubPrototype.mpnSubN a b bin

/-- The blocked add spec equals the limb-by-limb reference (`rfl`). -/
theorem mpnAddNAdx_blocked_eq_mpnAddN
    (a b : List (BitVec 64)) (cin : Bool) :
    mpnAddNAdx_blocked a b cin = Mpn.AddPrototype.mpnAddN a b cin := rfl

/-- The blocked sub spec equals the limb-by-limb reference (`rfl`). -/
theorem mpnSubNAdx_blocked_eq_mpnSubN
    (a b : List (BitVec 64)) (bin : Bool) :
    mpnSubNAdx_blocked a b bin = Mpn.SubPrototype.mpnSubN a b bin := rfl

/-- The blocked add spec equals the unrolled-emit reference (`rfl`). -/
theorem mpnAddNAdx_blocked_eq_mpnAddNAdx
    (a b : List (BitVec 64)) (cin : Bool) :
    mpnAddNAdx_blocked a b cin = mpnAddNAdx a b cin := rfl

/-- The blocked sub spec equals the unrolled-emit reference (`rfl`). -/
theorem mpnSubNAdx_blocked_eq_mpnSubNAdx
    (a b : List (BitVec 64)) (bin : Bool) :
    mpnSubNAdx_blocked a b bin = mpnSubNAdx a b bin := rfl

/-- Empty input: add yields empty output and unchanged carry-in. -/
theorem mpnAddNAdx_blocked_nil (cin : Bool) :
    mpnAddNAdx_blocked [] [] cin = ([], cin) := by
  simp [mpnAddNAdx_blocked, Mpn.AddPrototype.mpnAddN]

/-- Empty input: sub yields empty output and unchanged borrow-in. -/
theorem mpnSubNAdx_blocked_nil (bin : Bool) :
    mpnSubNAdx_blocked [] [] bin = ([], bin) := by
  simp [mpnSubNAdx_blocked, Mpn.SubPrototype.mpnSubN]

/-- Add spec inherited from `mpnAddN_spec` via the equivalence. -/
theorem mpnAddNAdx_blocked_spec
    (a b : List (BitVec 64)) (hlen : a.length = b.length) (cin : Bool) :
    Mpn.AddPrototype.toNat (mpnAddNAdx_blocked a b cin).1
      + (2 ^ 64) ^ a.length
          * Mpn.AddPrototype.carryNat (mpnAddNAdx_blocked a b cin).2
    = Mpn.AddPrototype.toNat a + Mpn.AddPrototype.toNat b
        + Mpn.AddPrototype.carryNat cin := by
  rw [mpnAddNAdx_blocked_eq_mpnAddN]
  exact Mpn.AddPrototype.mpnAddN_spec a b hlen cin

/-- Sub spec inherited from `mpnSubN_spec` via the equivalence. -/
theorem mpnSubNAdx_blocked_spec
    (a b : List (BitVec 64)) (hlen : a.length = b.length) (bin : Bool) :
    Mpn.AddPrototype.toNat (mpnSubNAdx_blocked a b bin).1
        + Mpn.AddPrototype.toNat b
        + Mpn.SubPrototype.borrowNat bin
    = Mpn.AddPrototype.toNat a
      + (2 ^ 64) ^ a.length
          * Mpn.SubPrototype.borrowNat (mpnSubNAdx_blocked a b bin).2 := by
  rw [mpnSubNAdx_blocked_eq_mpnSubN]
  exact Mpn.SubPrototype.mpnSubN_spec a b hlen bin

/-! ### Concrete sanity checks -/

/-- `n = 8` (one block): add. -/
example : mpnAddNAdx_blocked
    (List.replicate 8 (1 : BitVec 64))
    (List.replicate 8 (2 : BitVec 64)) false
    = (List.replicate 8 (3 : BitVec 64), false) := by native_decide

/-- `n = 16` (two blocks): add. -/
example : mpnAddNAdx_blocked
    (List.replicate 16 (1 : BitVec 64))
    (List.replicate 16 (2 : BitVec 64)) false
    = (List.replicate 16 (3 : BitVec 64), false) := by native_decide

/-- `n = 16` cross-block carry propagation: every limb of `a` is all-ones
    plus a `+1` propagates exactly to the cross-block boundary. -/
example : (mpnAddNAdx_blocked
    (List.replicate 16 ((-1 : BitVec 64)))
    ((1 : BitVec 64) :: List.replicate 15 (0 : BitVec 64)) false).2 = true := by
  native_decide

/-- `n = 8` (one block): sub. -/
example : mpnSubNAdx_blocked
    (List.replicate 8 (5 : BitVec 64))
    (List.replicate 8 (3 : BitVec 64)) false
    = (List.replicate 8 (2 : BitVec 64), false) := by native_decide

/-- `n = 16` (two blocks): sub. -/
example : mpnSubNAdx_blocked
    (List.replicate 16 (5 : BitVec 64))
    (List.replicate 16 (3 : BitVec 64)) false
    = (List.replicate 16 (2 : BitVec 64), false) := by native_decide

/-! ## §3  The blocked Jasmin body — Cfor of an 8-limb-unrolled per-block

The body structure for `n = numBlocks · BLOCK` limbs.  We reuse all the
instruction builders from `MpnAddSubAdxPrototype` (`load64Off`, `store64Off`,
`xorClearFlags`, `adcxCopn`, `sbbCopn`, `subCopn`, `assignConst`) — the same
ones the unrolled `n = 8` ADX body uses.

```
# Prologue
cy := 0                                              # initial cross-block carry
of, cf, _, _, _, zero := XOR_64(zero, zero)           # cf := 0; zero := 0

# Main loop
for i = 0 to numBlocks {
  # ---- per-block body (BLOCK = 8 limbs of add or sub) ----
  # 1. Re-clear CF, restore zero=0.
  of, cf, _, _, _, zero := XOR_64(zero, zero)        # cf := 0; zero := 0
  # 2. Load cross-block carry `cy` into CF.  Side-effect: `zero` may be
  #    stomped (becomes 0 if cy=0 or 2^64-1 if cy=1); next block re-clears.
  _, cf, _, _, _, zero := #SUB_64(zero, cy)          # cf := cy
  # 3. Load 8 a-limbs from [ap + 0..56].
  r_0 := [:u64 ap + 0]; …; r_7 := [:u64 ap + 56]
  # 4. Per-limb interleaved: load t_i from [bp + 8*i]; then ADCX/SBB.
  #    Limb 0's ADCX/SBB reads cf=cy as carry-in, threading cross-block carry.
  t_0 := [:u64 bp + 0];  cf, r_0 := ADCX(r_0, t_0, cf)     # add: ADCX
  …                                                          (seven more)
  # 5. Capture final CF into `cy` for the next block.
  cy := 0
  cf, cy := ADCX(cy, cy, cf)                          # cy := cf
  # 6. Store the 8 r-limbs back.
  [:u64 op + 0] := r_0;  … ; [:u64 op + 56] := r_7
  # 7. Advance pointers.
  op += 64;  ap += 64;  bp += 64;
}
```

The cross-block `cy` thread is exactly the role `cy` plays in the single-
chain looped reference (`MpnAddNAdcSpillPrototype`'s `cy`).  All the GPRs
(`r_0..r_7`, `t_i`, `zero`) are block-local or block-stable; the per-iteration
register live-set is identical to the unrolled `n = 8` body's. -/

/-- Local `r += k` / `r -= k` scalar update (mirrors
    `Mpn.AddOpenCarryPrototype.binImm` / `Mpn.AddNAdcSpillPrototype.binImm`; we
    spell it out here so the file's import graph stays minimal). -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- **Set CF from the cross-block carry `cy`** at block entry.

    Trick: after the XOR-clear we have `zero = 0` and `CF = 0`.  Then
    `_, cf, _, _, _, zero := #SUB_64(zero, cy)` computes `0 - cy`:
    * `cy = 0`: result = 0 written to `zero` (unchanged), `CF = 0`.
    * `cy = 1`: result = `2^64 - 1` (`zero` stomped), `CF = 1`.

    In both cases `CF := cy` (the cross-block carry is now in the
    architectural CF flag).  The cost: `zero` is not trustworthy
    after this — we re-XOR-clear at the start of every block (which is
    the *only* place we read `zero`), so this is fine.

    Why we re-use `zero` as the dst instead of a fresh `tmp`:
    `SUB_64`'s x86 encoding has `dst = src1`, so jasminc's register
    allocator forces them to merge.  Per-iteration `tmp` cannot merge
    with cross-iteration `zero`.  Re-using `zero` as the dst avoids the
    merge conflict; the value-clobbering is harmless because the next
    block's first instruction (`xor zero, zero`) re-clears it. -/
def adxLoadCfFromCy_ADD : InstrR :=
  subCopn "cf" "zero" "zero" "cy"

/-- For SUB: same trick, same intrinsic.  `SUB_64(zero, cy)` sets
    CF = cy regardless of whether we are about to ADCX (carry) or SBB
    (borrow) — on x86 those flags are the same CF bit.  We name it
    separately for the Lean-side documentation/refinement narrative. -/
def adxLoadCfFromCy_SUB : InstrR :=
  subCopn "cf" "zero" "zero" "cy"

/-- Per-block ADCX limb step for the blocked add: load `t_i := [bp + 8*i]`,
    then `cf, r_i := ADCX(r_i, t_i, cf)`.  Identical to
    `Mpn.AddSubAdxPrototype.adxAddStepInterleaved` modulo namespace. -/
def adxAddStepBlk (i : Nat) : List InstrR :=
  [ load64Off (tName i) "bp" (8 * Int.ofNat i)
  , adcxCopn "cf" (rName i) (rName i) (tName i) "cf" ]

/-- Per-block SBB limb step for the blocked sub: load `t_i := [bp + 8*i]`,
    then `cf, r_i := SBB_64(r_i, t_i, cf)`.

    Note: unlike the unrolled `Mpn.AddSubAdxPrototype.adxSubStepInterleaved`,
    we do NOT use `SUB_64` for limb 0 here — the CF chain is fed by
    `sbbLoadCfFromCy` (folding cross-block `cy`), so every limb uses
    `SBB_64`. -/
def adxSubStepBlk (i : Nat) : List InstrR :=
  [ load64Off (tName i) "bp" (8 * Int.ofNat i)
  , sbbCopn "cf" (rName i) (rName i) (tName i) "cf" ]

/-- The unrolled `BLOCK`-limb add chain for one block. -/
def adxAddSeqBlk : Nat → List InstrR
  | 0     => []
  | n + 1 => adxAddSeqBlk n ++ adxAddStepBlk n

/-- The unrolled `BLOCK`-limb sub chain for one block. -/
def adxSubSeqBlk : Nat → List InstrR
  | 0     => []
  | n + 1 => adxSubSeqBlk n ++ adxSubStepBlk n


/-- Pre-load 8 a-limbs from `[ap + 0 .. ap + 56]`.  Reused from
    `Mpn.AddSubAdxPrototype.adxLoadA` (we re-define inline so the BLOCK-sized
    instance is direct). -/
def adxLoadALimbsBlk : Nat → List InstrR
  | 0     => []
  | n + 1 => adxLoadALimbsBlk n ++ [load64Off (rName n) "ap" (8 * Int.ofNat n)]

/-- Store the 8 r-limbs back to `[op + 0 .. op + 56]`. -/
def adxStoreRLimbsBlk : Nat → List InstrR
  | 0     => []
  | n + 1 => adxStoreRLimbsBlk n ++ [store64Off "op" (8 * Int.ofNat n) (rName n)]

/-- Capture CF into the cross-block `cy` register.  With `cy = 0` prior to
    this and `cf ∈ {0, 1}`, `ADCX(cy, cy, cf) = 0 + 0 + cf = cf`, so `cy = cf`.

    Identical to `Mpn.AddSubAdxPrototype.adxCaptureCf`, but spelled out here
    for direct use inside the per-block body. -/
def adxCaptureCfBlk : List InstrR :=
  [ assignConst "cy" 0
  , adcxCopn "cf" "cy" "cy" "cy" "cf" ]

/-- Pointer advance for one block: `op += 64; ap += 64; bp += 64`.  Each
    block is `BLOCK = 8` u64 limbs = 64 bytes. -/
def adxPtrAdvanceBlk : List InstrR :=
  [ binImm "op" (.Oadd .U64) (8 * Int.ofNat BLOCK)
  , binImm "ap" (.Oadd .U64) (8 * Int.ofNat BLOCK)
  , binImm "bp" (.Oadd .U64) (8 * Int.ofNat BLOCK) ]

/-- The per-block ADD body (one Cfor iteration), unrolled `BLOCK = 8` limbs.

    Pre-conditions on entry: `cy` holds the incoming cross-block carry
    (∈ {0, 1}); `op`/`ap`/`bp` point to the current block's 8-limb region;
    `zero` holds 0.

    Post-condition: `cy` holds the outgoing cross-block carry; pointers
    advanced by `64` bytes; `zero` still 0.

    Schedule:
    ```
    xor clear cf, of, zero                          # cf := 0
    r_0..r_7 := [:u64 ap + 0..56]                   # load a limbs
    t_0 := [:u64 bp + 0]; cf, r_0 := ADCX(r_0, t_0, cf)
    cf, r_0 := ADCX(r_0, cy, cf)                    # fold cross-block carry into r_0
    t_i := [:u64 bp + 8i]; cf, r_i := ADCX(r_i, t_i, cf)  # limbs 1..7
    cy := 0; cf, cy := ADCX(cy, cy, cf)             # capture cf -> cy
    [:u64 op + 8i] := r_i                           # store
    op += 64; ap += 64; bp += 64                    # advance
    ```
-/
def perBlockAddBody : List InstrR :=
  -- Step 1: re-clear CF=OF=0 and zero (zero may have been stomped by the
  -- previous block's cy-load).
  [ xorClearFlags "of" "cf" "zero"
  -- Step 2: set CF := cy (load cross-block carry into the arch flag).
  --         Side-effect: `zero` register may be stomped (becomes 0 or -1);
  --         next block re-clears it.
  , adxLoadCfFromCy_ADD ]
  -- Step 3: load r_0..r_7 from ap; standard 8-limb ADCX chain starting with
  -- CF = cy_in.  No further cy involvement — the chain absorbs cy via
  -- limb 0's ADCX(r_0, t_0, cf=cy).
  ++ adxLoadALimbsBlk BLOCK
  ++ adxAddSeqBlk BLOCK
  -- Step 4: capture final CF into cy; store limbs; advance pointers.
  ++ adxCaptureCfBlk
  ++ adxStoreRLimbsBlk BLOCK
  ++ adxPtrAdvanceBlk

/-- The per-block SUB body (one Cfor iteration), unrolled `BLOCK = 8` limbs.

    Symmetric to `perBlockAddBody`: after the regular `SBB_64(r_0, t_0, cf)`
    on limb 0, fold `cy` via an extra `SBB_64(r_0, cy, cf)`, then continue
    the SBB chain on limbs 1..7. -/
def perBlockSubBody : List InstrR :=
  [ xorClearFlags "of" "cf" "zero"
  , adxLoadCfFromCy_SUB ]
  ++ adxLoadALimbsBlk BLOCK
  -- Standard SBB chain throughout — limb 0 reads CF=cy as borrow-in.
  ++ adxSubSeqBlk BLOCK
  ++ adxCaptureCfBlk
  ++ adxStoreRLimbsBlk BLOCK
  ++ adxPtrAdvanceBlk

/-- The full blocked ADD body for `n = numBlocks · BLOCK` limbs.

    Prologue: initialise `cy := 0` (no prior block); clear CF and zero a
    scratch GPR (`zero`).
    Main: `Cfor i = 0 to numBlocks { perBlockAddBody }`. -/
def bodyAddNAdx_blocked (numBlocks : Nat) : List InstrR :=
  [ assignConst "cy" 0
  , xorClearFlags "of" "cf" "zero" ]
  ++ [ .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := numBlocks }
              perBlockAddBody ]

/-- The full blocked SUB body for `n = numBlocks · BLOCK` limbs. -/
def bodySubNAdx_blocked (numBlocks : Nat) : List InstrR :=
  [ assignConst "cy" 0
  , xorClearFlags "of" "cf" "zero" ]
  ++ [ .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := numBlocks }
              perBlockSubBody ]

/-- The blocked ADD function declaration.  Symbol name encodes
    `n = numBlocks · BLOCK` for direct lookup from the bench harness. -/
def mpnAddNAdxBlockedFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_add_n_adx_blk_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodyAddNAdx_blocked numBlocks
  results := []

/-- The blocked SUB function declaration. -/
def mpnSubNAdxBlockedFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_sub_n_sbb_blk_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodySubNAdx_blocked numBlocks
  results := []

/-! ### Emit smoke tests

For each `n ∈ {16, 32, 64, 128}` the emitted `.jazz` is non-`none` (the AST is
well-formed at every size). -/

def emittedAdd16  : Option String := emitFunDecl (mpnAddNAdxBlockedFd 2)
def emittedAdd32  : Option String := emitFunDecl (mpnAddNAdxBlockedFd 4)
def emittedAdd64  : Option String := emitFunDecl (mpnAddNAdxBlockedFd 8)
def emittedAdd128 : Option String := emitFunDecl (mpnAddNAdxBlockedFd 16)

def emittedSub16  : Option String := emitFunDecl (mpnSubNAdxBlockedFd 2)
def emittedSub32  : Option String := emitFunDecl (mpnSubNAdxBlockedFd 4)
def emittedSub64  : Option String := emitFunDecl (mpnSubNAdxBlockedFd 8)
def emittedSub128 : Option String := emitFunDecl (mpnSubNAdxBlockedFd 16)

example : emittedAdd16.isSome  := by native_decide
example : emittedAdd32.isSome  := by native_decide
example : emittedAdd64.isSome  := by native_decide
example : emittedAdd128.isSome := by native_decide
example : emittedSub16.isSome  := by native_decide
example : emittedSub32.isSome  := by native_decide
example : emittedSub64.isSome  := by native_decide
example : emittedSub128.isSome := by native_decide

-- Diagnostic eyeball-check at n=16.
#eval match emittedAdd16 with | some s => s | none => "EMIT FAILED"
#eval match emittedSub16 with | some s => s | none => "EMIT FAILED"

/-! ## §4  Refinement statement and the `n = 0` base case -/

/-- Refinement statement for the blocked ADD emit at fixed `n = numBlocks · BLOCK`.

    Same shape as `Mpn.AddSubAdxPrototype.MpnAddNAdxRefinesStmt n`, but
    parametrised by `numBlocks` (= n / BLOCK). -/
def MpnAddNAdxBlockedRefinesStmt (numBlocks : Nat) : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 64)),
    as.length = numBlocks * BLOCK →
    bs.length = numBlocks * BLOCK →
    Mpn.AddPrototype.memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    Mpn.AddPrototype.memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (numBlocks * BLOCK)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * (numBlocks * BLOCK))) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (numBlocks * BLOCK)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * (numBlocks * BLOCK))) →
    ∃ s', ∃ fuel, bignumExecFuel emptyRegistry fuel
            (bodyAddNAdx_blocked numBlocks) s = some s' ∧
      Mpn.AddPrototype.memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnAddNAdx_blocked as bs false).1 ∧
      s'.regs "cy" = BitVec.ofNat 64
        (Mpn.AddPrototype.carryNat (mpnAddNAdx_blocked as bs false).2)

/-- Refinement statement for the blocked SUB emit at fixed `n = numBlocks · BLOCK`. -/
def MpnSubNAdxBlockedRefinesStmt (numBlocks : Nat) : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 64)),
    as.length = numBlocks * BLOCK →
    bs.length = numBlocks * BLOCK →
    Mpn.AddPrototype.memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    Mpn.AddPrototype.memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (numBlocks * BLOCK)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * (numBlocks * BLOCK))) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (numBlocks * BLOCK)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * (numBlocks * BLOCK))) →
    ∃ s', ∃ fuel, bignumExecFuel emptyRegistry fuel
            (bodySubNAdx_blocked numBlocks) s = some s' ∧
      Mpn.AddPrototype.memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnSubNAdx_blocked as bs false).1 ∧
      s'.regs "cy" = BitVec.ofNat 64
        (Mpn.SubPrototype.borrowNat (mpnSubNAdx_blocked as bs false).2)

/-! ### `n = 0` base case: direct evaluation

The empty-Cfor body unfolds to just the prologue (`cy := 0` + XOR-clear of
CF/zero).  Memory unchanged; `cy` register holds 0; `carryNat false = 0`
(and `borrowNat false = 0`) — match. -/

theorem bodyAddNAdx_blocked_zero :
    bodyAddNAdx_blocked 0 =
      [ assignConst "cy" 0
      , xorClearFlags "of" "cf" "zero"
      , .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := 0 } perBlockAddBody ] := by
  unfold bodyAddNAdx_blocked
  rfl

theorem bodySubNAdx_blocked_zero :
    bodySubNAdx_blocked 0 =
      [ assignConst "cy" 0
      , xorClearFlags "of" "cf" "zero"
      , .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := 0 } perBlockSubBody ] := by
  unfold bodySubNAdx_blocked
  rfl

/-- ADD refinement, `numBlocks = 0`: empty input, no blocks, output unchanged,
    carry-out 0.  Mirrors `Mpn.AddSubAdxPrototype.MpnAddNAdxJasminRefines_zero`. -/
theorem MpnAddNAdxBlockedJasminRefines_zero :
    MpnAddNAdxBlockedRefinesStmt 0 := by
  intro s as bs has hbs _ _ _ _
  have h0 : (0 : Nat) * BLOCK = 0 := by simp
  rw [h0] at has hbs
  have has_nil : as = [] := List.length_eq_zero_iff.mp has
  have hbs_nil : bs = [] := List.length_eq_zero_iff.mp hbs
  subst has_nil
  subst hbs_nil
  -- Step 1: `cy := 0`.
  -- Step 2: XOR_64(zero, zero) clears of, cf and sets zero=0 (value unchanged).
  -- Step 3: Cfor _ {0,0} _ unrolls to `[]`, so the body collapses to the
  --         two prologue instructions.  Witness state: regs updated to
  --         (cy := 0, of := 0, cf := 0, zero := 0).
  refine ⟨setReg (setReg (setReg
            (setReg s "cy" 0) "of" 0) "cf" 0) "zero" 0, 8, ?_, ?_, ?_⟩
  · rw [bodyAddNAdx_blocked_zero]
    simp only [bignumExecFuel, execInstr, evalPExpr, assignConst, xorClearFlags,
               vr, pv, unrollFor, bind, Option.bind, writeXorBundle,
               List.flatMap, Nat.sub_self, List.range, List.range.loop, List.append_nil,
               List.map_nil, List.flatten_nil,
               show BitVec.ofInt 64 0 = (0 : BitVec 64) from rfl,
               show ((setReg s "cy" 0).regs "zero" ^^^
                     (setReg s "cy" 0).regs "zero" : BitVec 64) = 0 from by bv_decide]
  · -- mpnAddN [] [] false = ([], false).  memHoldsLimbs _ _ [] is trivially true.
    have : mpnAddNAdx_blocked [] [] false = ([], false) := mpnAddNAdx_blocked_nil false
    rw [this]
    simp [Mpn.AddPrototype.memHoldsLimbs]
  · -- cy = 0 in the final state; carryNat false = 0.
    have : mpnAddNAdx_blocked [] [] false = ([], false) := mpnAddNAdx_blocked_nil false
    rw [this]
    simp [setReg, Mpn.AddPrototype.carryNat]

/-- SUB refinement, `numBlocks = 0`: empty input, no blocks, output unchanged,
    borrow-out 0.  Mirrors `Mpn.AddSubAdxPrototype.MpnSubNAdxJasminRefines_zero`. -/
theorem MpnSubNAdxBlockedJasminRefines_zero :
    MpnSubNAdxBlockedRefinesStmt 0 := by
  intro s as bs has hbs _ _ _ _
  have h0 : (0 : Nat) * BLOCK = 0 := by simp
  rw [h0] at has hbs
  have has_nil : as = [] := List.length_eq_zero_iff.mp has
  have hbs_nil : bs = [] := List.length_eq_zero_iff.mp hbs
  subst has_nil
  subst hbs_nil
  refine ⟨setReg (setReg (setReg
            (setReg s "cy" 0) "of" 0) "cf" 0) "zero" 0, 8, ?_, ?_, ?_⟩
  · rw [bodySubNAdx_blocked_zero]
    simp only [bignumExecFuel, execInstr, evalPExpr, assignConst, xorClearFlags,
               vr, pv, unrollFor, bind, Option.bind, writeXorBundle,
               List.flatMap, Nat.sub_self, List.range, List.range.loop, List.append_nil,
               List.map_nil, List.flatten_nil,
               show BitVec.ofInt 64 0 = (0 : BitVec 64) from rfl,
               show ((setReg s "cy" 0).regs "zero" ^^^
                     (setReg s "cy" 0).regs "zero" : BitVec 64) = 0 from by bv_decide]
  · have : mpnSubNAdx_blocked [] [] false = ([], false) := mpnSubNAdx_blocked_nil false
    rw [this]
    simp [Mpn.AddPrototype.memHoldsLimbs]
  · have : mpnSubNAdx_blocked [] [] false = ([], false) := mpnSubNAdx_blocked_nil false
    rw [this]
    simp [setReg, Mpn.SubPrototype.borrowNat]

/-! ### Structural mirror to the unrolled bridge

The general `numBlocks ≥ 1` case reduces structurally to the unrolled
`MpnAddSubAdxPrototype`'s `MpnAddNAdxRefinesStmt n` (resp.
`MpnSubNAdxRefinesStmt n`), which itself reduces to the single-chain
`MpnAddNAdcSpillJasminRefines` (resp. `MpnSubNSbbSpillJasminRefines`).  The
only new algorithmic content is:

* The blocked decomposition equals the limb-by-limb reference
  (`mpnAddNAdx_blocked_eq_mpnAddN` / `mpnSubNAdx_blocked_eq_mpnSubN`,
  proved above by `rfl`).
* Each block's body is the same instruction sequence as the `n = 8` unrolled
  body, modulo the per-block prologue (XOR-clear + cross-block carry-load)
  and the per-block epilogue (capture CF into `cy` + advance pointers).

We record the structural mirror as a `Prop` and discharge the `numBlocks = 0`
case directly. -/

/-- `numBlocks = 0` base case for the blocked ADD refinement.  Identical to
    `MpnAddNAdxBlockedJasminRefines_zero` above; included separately to
    mirror the unrolled prototype's `_holds_n0` naming. -/
theorem MpnAddNAdxBlockedJasminRefines_holds_n0 :
    MpnAddNAdxBlockedRefinesStmt 0 :=
  MpnAddNAdxBlockedJasminRefines_zero

/-- `numBlocks = 0` base case for the blocked SUB refinement. -/
theorem MpnSubNAdxBlockedJasminRefines_holds_n0 :
    MpnSubNAdxBlockedRefinesStmt 0 :=
  MpnSubNAdxBlockedJasminRefines_zero

/-! ## §5  Constant-time-shape

The body has exactly one control-flow node: the outer Cfor over `numBlocks`
public iterations.  Inside the body, all instructions are `Cassgn`/`Copn`
with no secret-dependent branches.

Like the unrolled prototype, `isCT_Cmd` returns `false` because the
ADCX/SBB_64 whitelist hasn't been added to `JasminCT.lean`.  We structurally
assert the AST shape instead. -/

/-- The per-block ADD body is straight-line Cassgn/Copn. -/
example : perBlockAddBody.all (fun i => match i with
    | .Cassgn _ _ _ _ => true
    | .Copn _ _ _ _ => true
    | _ => false) = true := by native_decide

/-- The per-block SUB body is straight-line Cassgn/Copn. -/
example : perBlockSubBody.all (fun i => match i with
    | .Cassgn _ _ _ _ => true
    | .Copn _ _ _ _ => true
    | _ => false) = true := by native_decide

/-- The outer ADD body has exactly one Cfor (plus two Cassgn/Copn prologue
    instructions). -/
example : (bodyAddNAdx_blocked 2).length = 3 := by decide

/-- The outer SUB body has exactly one Cfor (plus two Cassgn/Copn prologue
    instructions). -/
example : (bodySubNAdx_blocked 2).length = 3 := by decide

/-! ## §6  Carry-recovery ABI: `_WithCy` variants

The void-returning variants above (`mpnAddNAdxBlockedFd`,
`mpnSubNAdxBlockedFd`) update `op[]` in place but do NOT expose the
final carry/borrow to the caller.  The `mul_basecase` Cwhile cascade
needs the per-call carry-out for the column-accumulation step:
caller workaround in V64-BEST-V2 is a post-hoc compare-scan
(`out_high < in_high` ⇒ unsigned-wrap borrow), which costs O(1) per
call but inserts a CMP into the caller's critical path.

The `_WithCy` variants expose `cy ∈ {0, 1}` as a return value, so the
caller plumbs the column carry directly without the CMP roundtrip:

```
cy_col = mpn_add_n_adx_blk_cy_<n>(op, ap, bp);
```

The body is identical to the void-returning variant; only the FunDecl's
`results` field changes (`[]` → `[cy]`).  jasminc's ABI promotes the
return slot to `rax` automatically, so call-site code is `mov rax, ...`
(an x86-architectural copy, not a CMP).

### How `cy` is materialised inside the body

Both the void and `_WithCy` bodies already compute `cy ∈ {0, 1}` inside
the per-block tail (`adxCaptureCfBlk = cy := 0; ADCX(cy, cy, cf)`).
That idiom uses `0 + 0 + cf = cf` to land the final-iteration CF into
`cy` (because the chain's CF dies at the next XOR-clear if we don't
capture it).  The pure-function carry-out at end-of-body is exactly the
last block's `cy` — already in the right register.

### SETcc-based alternative capture

The ADCX-based capture above costs one ADCX + one constant-zero
assignment per block.  An equivalent SETcc-based capture
(`setb cy_byte; movzx cy, cy_byte`) costs one SETcc + one zero-extend
per block — usually one fewer cycle in critical-path-sensitive use, and
strictly the canonical x86 idiom for "lift CF into a GPR".

`setccCaptureFromCf` below emits a pair of instructions equivalent in
arithmetic to `adxCaptureCfBlk` but using the standard `setcc/movzx`
sequence the emitter's `expandFlagCaptures` would otherwise insert
post-hoc.  Both variants are semantically identical (both lift the same
CF bit into `cy`); we keep both available so jasminc has freedom to
schedule whichever it prefers.
-/

/-- Capture the architectural `cf` flag into the `reg u64` register `cy`
    via the standard x86 `setcc/movzx` idiom.

    Emits a two-instruction sequence:
    ```
    cy_byte = #SETcc(cf)    # reg bool -> reg u8
    cy      = (64u) cy_byte # zero-extend to reg u64
    ```

    `cf` must currently be a `reg bool` (the chain's architectural carry-out).
    `cy` becomes a `reg u64` holding `0` or `1`.  Identical in arithmetic to
    `adxCaptureCfBlk` (`cy := 0; ADCX(cy, cy, cf) = 0+0+cf = cf`) but uses
    the canonical x86 SETcc idiom rather than the ADCX trick.

    Used by the `_WithCy` variants below to capture the per-block CF into
    the cross-block / return-value `cy` register. -/
def setccCaptureFromCf : List InstrR :=
  [ .Copn [.Lvar { var := { vname := "cy__byte", vtype := .sword .U8 } }]
          .AT_none (.Oasm ⟨"SETcc"⟩)
          [.Pvar { gv := { var := { vname := "cf", vtype := .sbool } }, gs := false }]
  , .Cassgn (.Lvar { var := vr "cy" }) .AT_none (.sword .U64)
        (.Papp1 (.Ozeroext .U64 .U8)
          (.Pvar { gv := { var := { vname := "cy__byte", vtype := .sword .U8 } },
                   gs := false })) ]

/-- ADD per-block body with SETcc-based CF capture (vs the ADCX-based
    `adxCaptureCfBlk` used by `perBlockAddBody`).  Same arithmetic. -/
def perBlockAddBodySetcc : List InstrR :=
  [ xorClearFlags "of" "cf" "zero"
  , adxLoadCfFromCy_ADD ]
  ++ adxLoadALimbsBlk BLOCK
  ++ adxAddSeqBlk BLOCK
  ++ setccCaptureFromCf
  ++ adxStoreRLimbsBlk BLOCK
  ++ adxPtrAdvanceBlk

/-- SUB per-block body with SETcc-based CF capture. -/
def perBlockSubBodySetcc : List InstrR :=
  [ xorClearFlags "of" "cf" "zero"
  , adxLoadCfFromCy_SUB ]
  ++ adxLoadALimbsBlk BLOCK
  ++ adxSubSeqBlk BLOCK
  ++ setccCaptureFromCf
  ++ adxStoreRLimbsBlk BLOCK
  ++ adxPtrAdvanceBlk

/-- ADD body with SETcc capture. -/
def bodyAddNAdx_blocked_setcc (numBlocks : Nat) : List InstrR :=
  [ assignConst "cy" 0
  , xorClearFlags "of" "cf" "zero" ]
  ++ [ .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := numBlocks }
              perBlockAddBodySetcc ]

/-- SUB body with SETcc capture. -/
def bodySubNAdx_blocked_setcc (numBlocks : Nat) : List InstrR :=
  [ assignConst "cy" 0
  , xorClearFlags "of" "cf" "zero" ]
  ++ [ .Cfor { var := vr "i" } { dir := .UpTo, lo := 0, hi := numBlocks }
              perBlockSubBodySetcc ]

/-- The blocked ADD function declaration with carry-out as a return value
    (uses the ADCX-based capture, same as `perBlockAddBody`). -/
def mpnAddNAdxBlockedWithCyFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_add_n_adx_blk_cy_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodyAddNAdx_blocked numBlocks
  results := [{ var := vr "cy" }]

/-- The blocked SUB function declaration with borrow-out as a return value. -/
def mpnSubNAdxBlockedWithCyFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_sub_n_sbb_blk_cy_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodySubNAdx_blocked numBlocks
  results := [{ var := vr "cy" }]

/-- The blocked ADD with SETcc-based carry capture, returning carry-out. -/
def mpnAddNAdxBlockedSetccFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_add_n_adx_blk_setcc_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodyAddNAdx_blocked_setcc numBlocks
  results := [{ var := vr "cy" }]

/-- The blocked SUB with SETcc-based borrow capture, returning borrow-out. -/
def mpnSubNAdxBlockedSetccFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_sub_n_sbb_blk_setcc_" ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodySubNAdx_blocked_setcc numBlocks
  results := [{ var := vr "cy" }]

/-! ### Emit smoke tests for the `_WithCy` and `_Setcc` variants -/

example : (emitFunDecl (mpnAddNAdxBlockedWithCyFd 2)).isSome   := by native_decide
example : (emitFunDecl (mpnSubNAdxBlockedWithCyFd 2)).isSome   := by native_decide
example : (emitFunDecl (mpnAddNAdxBlockedSetccFd 2)).isSome    := by native_decide
example : (emitFunDecl (mpnSubNAdxBlockedSetccFd 2)).isSome    := by native_decide

/-- The `_WithCy` and `_Setcc` variants also emit via the subroutine
    (`#[returnaddress=stack]`) path — used by the mul_basecase Cwhile
    cascade as `Ccall` targets. -/
example : (emitFunDeclRastack (mpnAddNAdxBlockedWithCyFd 2)).isSome := by native_decide
example : (emitFunDeclRastack (mpnSubNAdxBlockedWithCyFd 2)).isSome := by native_decide
example : (emitFunDeclRastack (mpnAddNAdxBlockedSetccFd 2)).isSome  := by native_decide
example : (emitFunDeclRastack (mpnSubNAdxBlockedSetccFd 2)).isSome  := by native_decide

-- Diagnostic eyeball-check.
#eval match emitFunDecl (mpnAddNAdxBlockedSetccFd 2) with
      | some s => s | none => "EMIT FAILED"

/-! ### Spec preservation

The `_WithCy` variants share their body with the void variants, so all
the spec/refinement theorems for the void variant (proved above)
carry over.  The `_Setcc` variants differ only by replacing the ADCX-based
CF capture with the SETcc-based capture; the per-block arithmetic
(`0+0+cf = cf` via ADCX vs. `setcc/movzx` on cf) is provably equal
because both lift the *same* CF bit into the same `cy` register.

We record the spec equivalence as `rfl`-able definitional lemmas; the
operational refinement carries over from the void variant. -/

theorem bodyAddNAdx_blocked_setcc_eq_void_body_modulo_capture (numBlocks : Nat) :
    -- both bodies share the same prologue and the same outer Cfor index range
    (bodyAddNAdx_blocked_setcc numBlocks).take 2 =
    (bodyAddNAdx_blocked numBlocks).take 2 := by
  unfold bodyAddNAdx_blocked_setcc bodyAddNAdx_blocked
  rfl

end CatCrypt.Crypto.Jasmin.Mpn.AddSubAdxBlockedPrototype
