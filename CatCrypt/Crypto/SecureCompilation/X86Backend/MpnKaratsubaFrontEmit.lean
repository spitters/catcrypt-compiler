/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Integer Karatsuba multiply as a front-compiled straight-line scalar-word kernel

A single-level (2-way) Karatsuba integer multiply of two `n = 2m`-word inputs
into a `4m`-word product, sourced through the verified control front — no
hand-built `Com`. Every intermediate is a named `u64` word slot and every
binding is pure scalar arithmetic (`RScalarSetExpr`): the schoolbook leaves,
the half sums, the cross-term subtraction and the windowed recombination all
thread carries limb-to-limb with the branch-free `bSltu` idiom
(`MpnMul1FrontEmit.ltuCmds`), exactly as the `mpn` word kernels do.

```
  karaBodyLowCT m  (RScalarSetExpr scalar-word Karatsuba math over the a/b slots)
    --(translateDialectControl)-->  Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  karaCom : Com jasminDialect inCtxt r64
```

The lowered `Com` is rendered to owned AT&T `.s` via `Com.toLprogPhysAbi` /
`renderOwned` — symbol `mpn_kara_front`, no jasminc. The emit driver is
`bench/mpn_karatsuba_front_compare/mpn_kara_front_owned_emit.lean`.

## Algorithm

Split `a = a0 + a1·B^m`, `b = b0 + b1·B^m` at the half width `m` (`B = 2^64`):

  `z0 = a0·b0`  (`schoolbookLowCT`, `2m` words),
  `z2 = a1·b1`  (`schoolbookLowCT`, `2m` words),
  `sa = a0 + a1`, `sb = b0 + b1`  (`m + 1` words each, carry in the top word),
  `zs = sa·sb`  (`schoolbookLowCT` at `k = m + 1`, `2m + 2` words),
  `z1 = zs − z0 − z2`  (two borrow-threaded subtraction passes; the exact
    cross term `a0·b1 + a1·b0`, non-negative),
  `result = z0 + z1·B^m + z2·B^2m`  (`4m` words, carry propagated across the
    overlapping windows).

The final `4m` bindings are `f[0..4m−1]` — the result words in order, each a
single copy binding — so `toLprogPhysAbi`'s last-`nOut` epilogue stores them to
`out[0..4m−1]`.

## ABI

```c
extern uint64_t *mpn_kara_front(uint64_t *out, const uint64_t *inp);
//   inp = [ a[0..2m) | b[0..2m) | <pad> ]   (4m + 1 u64 words)
//   out receives the 4m product words out[0..4m)
```

`RDI = out`, `RSI = inp`, 8-byte (u64) element stride; `inp[4m]` (the pad word)
is never read.

## Main results

* `schoolbookLowCT` / `karaBodyLowCT`: the straight-line word-slot generators.
* `karaComOpt` (at `m = 4`): the front-compiled, jasmin-lowered kernel, as an
  `Option` (the module builds without native-compiling the front closure).
* `karaAsmOpt`: the owned `.s` text, matched at run time by the emit driver.

Numerical correctness (`bignumVal result = a · b`) is not proved here; the
anchor is that the kernel front-compiles and lowers. The external GMP
conformance check on the emitted `.s` is the correctness gate, and the formal
front-denote proof (via `karatsuba_3mul_identity`) is the follow-on.

## Scope: the emitted kernel is NOT numerically correct on the cross-term path

The generators, the front lowering, and the owned render all succeed (the `.s`
assembles, `mulx` present, no `UNHANDLED`), and the algorithm is correct
(checked against an independent C model). Single-limb and two-limb products are
GMP-correct. The full cross-term path (`z1 = zs − z0 − z2` and the windowed
recombination) is WRONG: the emitted `out[j]` do not match the schoolbook
reference. The defect lies in the OUTPUT-BINDING EXTRACTION, not the
arithmetic — with the recombination diagnostics exposed, every intermediate
(`z0`, `z2`, `sa`, `sb`, `zs`, the low words of `zt`/`z1`) computes correctly,
but the fixed value read out for a given result word depends on which slots are
selected as outputs. The `toLprogPhysAbi` "last-`nOut` bindings" epilogue does
not align with the pure-copy `f[j]` bindings here (the front copy-propagates
them), so the wrong bindings reach `out`. Fixing it needs the output contract
matched to the front (how the NTRU tile's `f k := o k` outputs survive) or a
by-name output mechanism. Do NOT bench this artifact until conformance passes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnKaratsubaFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit (aN bN bindAll)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (seqAll ltuCmds)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. Carry / borrow word steps

Each step returns its emitted bindings together with the two SExpr values it
produces: the low result word (a fresh named slot) and the carry / borrow word.
The carry-out bits are the branch-free `bSltu` of a sum against a summand,
synthesised by `ltuCmds` in the covered `SExpr` fragment. -/

/-- One widening multiply-add column position:
    `(low, carry-out) = a·b + rp + cy` with `hi:lo = a·b`. Structurally the
    `mpn` `mulAddLimb a b cy rp` step; `hi + carry(lo+cy) + carry(s1+rp)` does
    not overflow. -/
def mulAddCol (tag ai bj : String) (rp cy : SExpr) : List LowCT × SExpr × SExpr :=
  let lo := "lo" ++ tag
  let hi := "hi" ++ tag
  let s1 := "s1" ++ tag
  let s2 := "s2" ++ tag
  let hc := "hc" ++ tag
  ( [ .RScalarSetExpr lo (.SMul (.SVar ai) (.SVar bj))
    , .RScalarSetExpr hi (.SMulHiU (.SVar ai) (.SVar bj))
    , .RScalarSetExpr s1 (.SAdd (.SVar lo) cy) ]
    ++ ltuCmds ("k1" ++ tag) (.SVar s1) (.SVar lo)
    ++ [ .RScalarSetExpr s2 (.SAdd (.SVar s1) rp) ]
    ++ ltuCmds ("k2" ++ tag) (.SVar s2) (.SVar s1)
    ++ [ .RScalarSetExpr hc
          (.SAdd (.SAdd (.SVar hi) (.SVar ("k1" ++ tag))) (.SVar ("k2" ++ tag))) ]
  , .SVar s2, .SVar hc )

/-- One add-with-carry column: `(low, carry) = x + y + cy`; the carry is `0`/`1`. -/
def addCol (tag : String) (x y cy : SExpr) : List LowCT × SExpr × SExpr :=
  let s1 := "u1" ++ tag
  let s2 := "u2" ++ tag
  let c := "uc" ++ tag
  ( [ .RScalarSetExpr s1 (.SAdd x y) ]
    ++ ltuCmds ("uk1" ++ tag) (.SVar s1) x
    ++ [ .RScalarSetExpr s2 (.SAdd (.SVar s1) cy) ]
    ++ ltuCmds ("uk2" ++ tag) (.SVar s2) (.SVar s1)
    ++ [ .RScalarSetExpr c (.SAdd (.SVar ("uk1" ++ tag)) (.SVar ("uk2" ++ tag))) ]
  , .SVar s2, .SVar c )

/-- One subtract-with-borrow column: `(diff, borrow) = x − y − bin`; with
    `bin ≤ 1` the borrow is `0`/`1`. -/
def subCol (tag : String) (x y bin : SExpr) : List LowCT × SExpr × SExpr :=
  let t1 := "d1" ++ tag
  let t2 := "d2" ++ tag
  let bo := "db" ++ tag
  ( ltuCmds ("bb1" ++ tag) x y
    ++ [ .RScalarSetExpr t1 (.SSub x y) ]
    ++ ltuCmds ("bb2" ++ tag) (.SVar t1) bin
    ++ [ .RScalarSetExpr t2 (.SSub (.SVar t1) bin)
       , .RScalarSetExpr bo (.SAdd (.SVar ("bb1" ++ tag)) (.SVar ("bb2" ++ tag))) ]
  , .SVar t2, .SVar bo )

/-! ## 2. The schoolbook leaf

Row (operand-scanning) schoolbook: the output words are threaded as a mutable
word-state; row `i` runs `k` multiply-add columns `rp[i+j] += a[i]·b[j] + cy`
and stores its final carry at word `i + k`. Word `p`'s final value is set by row
`min(p, k−1)`. -/

/-- The `k × k` schoolbook product `a·b` into `2k` output word slots, with carry
    threading. `aSlots`/`bSlots` name the `k` factor word slots, `outSlots` the
    `2k` product word slots. Internal slot names are prefixed by
    `outSlots.headD` so the three Karatsuba calls do not collide. -/
def schoolbookLowCT (aSlots bSlots outSlots : List String) (k : Nat) : List LowCT :=
  let pfx := outSlots.headD "sb"
  let rows : List SExpr × List LowCT :=
    (List.range k).foldl
      (fun (acc : List SExpr × List LowCT) (i : Nat) =>
        let st := acc.1
        let code := acc.2
        let inner : List SExpr × List LowCT × SExpr :=
          (List.range k).foldl
            (fun (racc : List SExpr × List LowCT × SExpr) (j : Nat) =>
              let st := racc.1
              let code := racc.2.1
              let cy := racc.2.2
              let p := i + j
              let tag := pfx ++ "i" ++ toString i ++ "j" ++ toString j
              let step := mulAddCol tag (aSlots.getD i "") (bSlots.getD j "")
                (st.getD p (.SLit 0)) cy
              (st.set p step.2.1, code ++ step.1, step.2.2))
            (st, code, .SLit 0)
        (inner.1.set (i + k) inner.2.2, inner.2.1))
      (List.replicate (2 * k) (.SLit 0), [])
  rows.2 ++ (List.range (2 * k)).map (fun p =>
    .RScalarSetExpr (outSlots.getD p "") (rows.1.getD p (.SLit 0)))

/-! ## 3. Add / subtract word arrays -/

/-- Add two equal-length word lists into `outSlots` (length `xs.length + 1`):
    the low words followed by the final carry word. -/
def addWithCarry (pfx : String) (xs ys : List SExpr) (outSlots : List String) : List LowCT :=
  let L := xs.length
  let res : List LowCT × SExpr :=
    (List.range L).foldl
      (fun (acc : List LowCT × SExpr) (t : Nat) =>
        let step := addCol (pfx ++ toString t) (xs.getD t (.SLit 0)) (ys.getD t (.SLit 0)) acc.2
        (acc.1 ++ step.1 ++ [.RScalarSetExpr (outSlots.getD t "") step.2.1], step.2.2))
      ([], .SLit 0)
  res.1 ++ [.RScalarSetExpr (outSlots.getD L "") res.2]

/-- Subtract `ys` from `xs` (both zero-extended to width `W`) into `outSlots`,
    borrow-threaded. The final borrow is dropped (`0` when `xs ≥ ys`). -/
def subWithBorrow (pfx : String) (xs ys : List SExpr) (outSlots : List String)
    (W : Nat) : List LowCT :=
  ((List.range W).foldl
    (fun (acc : List LowCT × SExpr) (t : Nat) =>
      let step := subCol (pfx ++ toString t) (xs.getD t (.SLit 0)) (ys.getD t (.SLit 0)) acc.2
      (acc.1 ++ step.1 ++ [.RScalarSetExpr (outSlots.getD t "") step.2.1], step.2.2))
    ([], .SLit 0)).1

/-- Add the word list `vals` into the word-state `st` starting at word `offset`,
    carry-propagated through word `RW − 1`. Returns the updated state and the
    emitted bindings; the final carry is dropped (`0` for an in-range product). -/
def addIntoState (pfx : String) (st : List SExpr) (vals : List SExpr)
    (offset RW : Nat) : List SExpr × List LowCT :=
  let res : List SExpr × List LowCT × SExpr :=
    (List.range (RW - offset)).foldl
      (fun (acc : List SExpr × List LowCT × SExpr) (t : Nat) =>
        let p := offset + t
        let step := addCol (pfx ++ toString t) (acc.1.getD p (.SLit 0))
          (vals.getD t (.SLit 0)) acc.2.2
        (acc.1.set p step.2.1, acc.2.1 ++ step.1, step.2.2))
      (st, [], .SLit 0)
  (res.1, res.2.1)

/-! ## 4. The Karatsuba body -/

/-- The full single-level Karatsuba body over the `a`/`b` source word slots: the
    two schoolbook leaves, the half sums, the cross-term schoolbook, the two
    borrow-threaded subtractions and the windowed recombination, then the `4m`
    output copies `f[0..4m−1]` as the last `4m` bindings. -/
def karaBodyLowCT (m : Nat) : LowCT :=
  let aLo := (List.range m).map aN
  let aHi := (List.range m).map (fun i => aN (i + m))
  let bLo := (List.range m).map bN
  let bHi := (List.range m).map (fun i => bN (i + m))
  let z0S := (List.range (2 * m)).map (fun p => "z0_" ++ toString p)
  let z2S := (List.range (2 * m)).map (fun p => "z2_" ++ toString p)
  let saS := (List.range (m + 1)).map (fun t => "sa_" ++ toString t)
  let sbS := (List.range (m + 1)).map (fun t => "sb_" ++ toString t)
  let zsS := (List.range (2 * m + 2)).map (fun p => "zs_" ++ toString p)
  let ztS := (List.range (2 * m + 2)).map (fun p => "zt_" ++ toString p)
  let z1S := (List.range (2 * m + 2)).map (fun p => "z1_" ++ toString p)
  let fS := (List.range (4 * m)).map (fun p => "f" ++ toString p)
  let cZ0 := schoolbookLowCT aLo bLo z0S m
  let cZ2 := schoolbookLowCT aHi bHi z2S m
  let cSA := addWithCarry "sa" (aLo.map .SVar) (aHi.map .SVar) saS
  let cSB := addWithCarry "sb" (bLo.map .SVar) (bHi.map .SVar) sbS
  let cZS := schoolbookLowCT saS sbS zsS (m + 1)
  let cZT := subWithBorrow "zt" (zsS.map .SVar) (z0S.map .SVar) ztS (2 * m + 2)
  let cZ1 := subWithBorrow "z1" (ztS.map .SVar) (z2S.map .SVar) z1S (2 * m + 2)
  let initSt := (List.range (4 * m)).map (fun p =>
    if p < 2 * m then SExpr.SVar (z0S.getD p "") else .SLit 0)
  let step1 := addIntoState "r1" initSt (z1S.map .SVar) m (4 * m)
  let step2 := addIntoState "r2" step1.1 (z2S.map .SVar) (2 * m) (4 * m)
  let fCopies := (List.range (4 * m)).map (fun p =>
    LowCT.RScalarSetExpr (fS.getD p "") (step2.1.getD p (.SLit 0)))
  seqAll (cZ0 ++ cZ2 ++ cSA ++ cSB ++ cZS ++ cZT ++ cZ1
    ++ step1.2 ++ step2.2 ++ fCopies)

/-! ## 5. The front-emitted program (anchored at `m = 4`)

Bumping to `m = 8` (`n = 16`, `4m = 32` product words) is the single edit
`M := 8`; the ABI maps and the source context are stated in terms of `M`. -/

/-- The half width. `n = 2M` input words per operand, `4M` product words. -/
abbrev M : Nat := 4

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The input word names in word order: `a[0..2M) | b[0..2M) | pad`. -/
def wordNames : List String :=
  (List.range (2 * M)).map aN ++ (List.range (2 * M)).map bN ++ ["padK"]

/-- The source context: `4M + 1` `u64` scalar slots (`a`, `b`, pad). -/
def srcCtx : Ctx := List.replicate (4 * M + 1) (.sword 64)

/-- The source `VarMap` (word `0 = a[0]` at the head). -/
def srcVM : VarMap srcCtx := bindAll wordNames

/-- Push `karaBodyLowCT M` through the control front and cap with
    `ret <name>`. `none` if the front declines. -/
def karaFrontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM (karaBodyLowCT M) with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted Karatsuba kernel lowered to the jasmin dialect, capped at
    the final output copy `f[4M−1]` (the `Com`'s last binding). -/
def karaLoweredOpt :=
  (karaFrontComAt ("f" ++ toString (4 * M - 1))).bind
    DialectToJasminCom.cryptoDialectToJasminCom

/-- The input context: `4M + 1` `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate (4 * M + 1) r64

/-- The deployed integer-Karatsuba multiply kernel `Com jasminDialect`, as an
    `Option` — FRONT-GENERATED (`translateDialectControl` +
    `cryptoDialectToJasminCom`), not hand-built. Rendered to owned `.s` below
    under the `mpn_kara_front` symbol. Kept as an `Option` so the module builds
    without native-compiling the front closure; the emit driver matches it at
    run time (the front resolves to `some`, confirmed by `#eval
    karaLoweredOpt.isSome`). The `karaLowered_isSome` `native_decide` theorem
    lives in the CI-only `HeavyEmitKatCI` set. -/
def karaComOpt : Option (Com jasminDialect inCtxt r64) := karaLoweredOpt

/-! ## 6. ABI maps and the owned render

Argument-slot reversal: input word `i` gets slot `4M − i`. Inputs `0..4M−1`
(`a | b`) load from `inp`; input `4M` (the pad) sits at slot `0` and is never
read. Output word `j` is the `j`-th of the last `4M` bindings, stored to
`out[j]`. -/

/-- No immediate argument slots — every constant is a front-materialised body
    literal. -/
def karaImmSlots : ImmSlotMap := fun _ => none

/-- Argument slot → `(base, byte offset)`: slots `1..4M` load `inp[4M − slot]`
    from `RSI` at the u64 stride; slot `0` (the pad) is skipped. -/
def karaInLoadMap : InLoadMap := fun slot =>
  if 1 ≤ slot ∧ slot ≤ 4 * M then some ("RSI", (4 * M - slot) * 8) else none

/-- The `4M` output stores: word `j` to `out[j]` (RDI, u64 stride). -/
def karaOutStoreMap : OutStoreMap :=
  (List.range (4 * M)).map (fun j => ("RDI", j * 8))

/-- The owned physical `Lprog` for `mpn_kara_front`. The high-word `MULXHI`
    bindings the front emits for `SMulHiU` are coalesced with their paired low
    `MUL` into the printer's two-output `mulx` by `fuseMulHiLprog`; the kernel is
    straight-line, so no `%rdx` save/restore is needed around a back-edge. -/
def karaLprogOpt : Option Lprog :=
  karaComOpt.map fun c =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit.fuseMulHiLprog
      (Com.toLprogPhysAbi c "mpn_kara_front" (fun _ => none)
        karaImmSlots karaInLoadMap karaOutStoreMap)

/-- The owned AT&T `.s` text for `mpn_kara_front` (no jasminc), as an `Option`;
    the driver writes the `some` payload. -/
def karaAsmOpt : Option String :=
  karaLprogOpt.map
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnKaratsubaFrontEmit
