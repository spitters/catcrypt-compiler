/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttButterflyEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttButterflyEmit

/-!
# A straight-line BLOCK of `K` inlined lazy (Harvey) FHE-NTT Shoup CT butterflies

Stage-3: `K` **independent** lazy Cooley–Tukey Shoup butterflies emitted as ONE
straight-line owned-backend leaf (ONE prologue / ONE frame), so a benchmark
divides the per-butterfly cost by `K` and removes the per-call ABI tax that a
single-butterfly leaf (`FheNttButterflyEmit.fheBflyThir`) pays. This is the
FAIR per-butterfly cycle count against OpenFHE's *inlined* NTT inner loop (whose
butterflies share one loop body, no per-butterfly call frame).

The `K` butterflies operate on `K` distinct slot-pairs with `K` distinct
twiddles — they are data-independent, so they model the NTT inner loop's
butterfly **throughput** (back-to-back independent butterflies, the case the OoO
core overlaps). Each butterfly's body is exactly
`FheNttButterflyEmit.fheBflyThir`'s arithmetic (the lazy Shoup product via
`fuseMulHiLprog`'s two-output `mulx`, plus the two branchless sign-mask
conditional reductions of `2q` and `q`), reused verbatim through a CPS helper so
the `K` copies share no de-Bruijn bookkeeping by hand.

## K = 4 (NOT 8) — a register-pressure / red-zone decision (REPORTED)

The block stores its `2K` outputs via `comToLfundefPhysAbi`'s epilogue, which
stores the **last `2K` bindings** (`firstOutIdx = numBindings − 2K`). To put all
`2K` outputs in the final `2K` binding slots, each butterfly's three
output-feeding values (`Xn`, `Xn2q`, `T`) must stay live across the whole output
tail. That is `3K` simultaneously-live values plus the shared `cz`/`c2q`/`cq`
constants. The owned linear-scan allocator has **13** allocatable GP registers
(`R14`/`R15` reserved as reload scratch), and spills beyond that to U32 red-zone
slots `k.N` at `RSP − 4 − 4N`, which grow DOWN toward the six callee-saved
register saves occupying `[RSP−128 … RSP−65]`. So only `≈14` spill slots fit
before colliding with the `R15` save at `RSP−72` (the `≤28` figure in the
`JasminLprogExport.abiSaveRdiName` docstring predates the 2026-05-27 R14/R15
callee-saves that ate 16 bytes).

* `K = 4`: peak live across the output tail `≈ 3·4 + 3 (consts) = 15` values
  → `≈ 2` spill slots → comfortably inside the red zone. **Chosen.**
* `K = 8`: peak live `≈ 3·8 + 3 = 27` values → `≈ 14` spill slots, right at the
  red-zone cliff once the `mulx` rdx-pin / `fuseScratch` evacuation and the
  two-memory-operand reload scratch usage are accounted for. That is a
  **red-zone-overflow risk** for the KAT/perf run, so this module ships `K = 4`
  (the prompt's authorised fallback) and reports the `K = 8` overflow risk rather
  than emit an asm whose spill slots silently alias a callee-save.

## Block layout (`K = 4`)

Input layout `inp = [X0,Y0,ω0,ω0', X1,Y1,ω1,ω1', X2,Y2,ω2,ω2', X3,Y3,ω3,ω3']`
(16 u64); output `out = [X0',Y0', X1',Y1', X2',Y2', X3',Y3']` (8 u64). Each
butterfly `k` is `fheBflyThir`'s arithmetic on its own 4 inputs → 2 outputs.

The `Com` is built as: three shared mask constants `cz = 0`, `c2q = 2q`,
`cq = q` (materialised once, shared by every butterfly's reductions — the mask
arithmetic is the same constant per kernel), then `K` butterfly **compute**
blocks (each exposing `Xn_k`, `Xn2q_k`, `T_k` and NOT yet emitting its outputs),
then `2K` output bindings `Xo_k = Xn_k + T_k`, `Yo_k = Xn2q_k − T_k` as the
FINAL `2K` bindings (so `comToLfundefPhysAbi`'s "last `2K`" epilogue stores them
in order). Each butterfly's discarded-low `Y·ω'` + `mulhi(Y,ω')` pair is fused by
the unmodified `FuseMulHi.fuseMulHiLprog` into a two-output `mulx`; the
two sign-bit `shrImm`s per butterfly are legalised into `shrq $63` by the shared
`FheNttButterflyEmit.legalizeShiftImmLprog`.

## ABI (2-pointer SysV, `comToLfundefPhysAbi` shape)

```c
extern void fhe_ntt_block(uint64_t *out, const uint64_t *inp);
//   inp = [X0,Y0,w0,w0', X1,Y1,w1,w1', X2,Y2,w2,w2', X3,Y3,w3,w3']  (16 u64)
//   out = [X0',Y0', X1',Y1', X2',Y2', X3',Y3']                       (8 u64)
```

`RDI` = out, `RSI` = inp. Argument-slot numbering (`comToLfundef`): arg slot `s`
is context entry `nArgs − 1 − s`. The thir context is the 16 inputs in order
(`X0 = entry 0 … ω3' = entry 15`), so to make context entry `i` hold `inp[i]`
the load map is `inLoadMap s = ("RSI", 8·(15 − s))` (slots `≥ 16` absent).
Outputs: `Xo_k` → `out[2k]`, `Yo_k` → `out[2k+1]`.

## What is verified vs trusted (scope)

* **Verified (value, in Lean)**: `fheNttBlockThir_denote` (Com denotes its
  by-definition reference, true by `rfl`); `fheNttBlock_via_thirDialect`
  re-derives through the generic proved `lowerThir_denote`. A tiny `native_decide`
  value check on ONE slot (`fheNttBlock_slot3_kat`) ties the block's `.ret`
  output to the independent `Nat` Harvey reference `bflyRef` (reused from
  `FheNttButterflyEmit`). We do NOT `native_decide` all
  `K` slots; the per-butterfly arithmetic is identical to the (already
  KAT-checked) single butterfly and the orchestrator KATs all `2K` outputs vs
  GMP.
* **Trusted (thin)**: `renderLprogAtt` / `as`/`cc` / the SysV leaf ABI frame; the
  byte-identity of all `2K` outputs is the orchestrator's external GMP KAT.

## Register seams at `K` `mulx` sites

Each of the `K` `mulx` sites pins its multiplicand into `%rdx`, which the owned
linear scan uses to hold the block-wide modulus constant `q`; the pass therefore
runs in `saveRdx` mode, bracketing each pin with `MOV R15, RDX … MOV RDX, R15`.
A site whose high word is itself `%rdx`-homed evacuates it into `fuseScratch` and
threads a `RDX → fuseScratch` rename through the rest of the body, and with `K`
sites those renames compose. Register pressure at `K = 4` spills two of the four
twiddles `ω_k'` to red-zone slots, so those butterflies' low `MUL`s carry the
two-address legalizer's reload scratch where the matching `MULXHI` carries the
slot name; `fuseMulHiLprog` resolves a reload scratch back to the name last moved
into it, which is what pairs those two butterflies. Red-zone spill pressure
bounds `K` (see the `K = 4` decision above). Operand orders are inherited
verbatim from `fheBflyThir`: `r = v − c`, `Tlz = lo1 − lo2 = Y·ω − q̂·q`,
`Yo = Xn2q − T`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttBlockEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir lowerThir_denote thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttButterflyEmit
  (fheQ fheTwoQ bflyRef kOmega kOmegaP legalizeShiftImmLprog)

/-! ## 1. The block size and the input/output context -/

/-- The number of independent inlined butterflies in the block. `K = 4` (NOT 8) —
    see the module docstring's red-zone register-pressure analysis. -/
def kBlk : Nat := 4

/-- The thir input context: `K` quadruples `[X_k, Y_k, ω_k, ω_k']`, all `.reg 64`.
    For `K = 4` this is 16 entries. -/
abbrev blkCtx : Ctxt thirDialect :=
  (List.replicate (4 * kBlk) (.reg 64 : JasminTy))

/-! ## 2. The butterfly compute block as a CPS continuation

`bflyCompute X Y w wp cz c2q cq k` appends ONE butterfly's compute bindings (the
arithmetic of `fheBflyThir` up to and including `T`, NOT the two outputs), then
invokes the continuation `k` in the extended context with the renaming and the
three output-feeding values `Xn`, `Xn2q`, `T`. The `cz`/`c2q`/`cq` are the shared
mask constants (`0`/`2q`/`q`). Every op is in the renderable carry-free alphabet
(`thBin {.sub,.and,.add,.mul}`, `thShrImm 64 63`, `thMulHi`) exactly as in
`fheBflyThir`. -/

/-- A `reg 64` thir type abbreviation (the dialect's `Ty` is `JasminTy`). -/
abbrev W64 : JasminTy := .reg 64

/-- One butterfly's compute block, in CPS. Given the four inputs `X Y w wp` and
    the three shared mask constants `cz c2q cq` (all `Var Γ W64`), append the
    `fheBflyThir` arithmetic UP TO AND INCLUDING `T` (NOT the two outputs), then
    invoke the continuation `k` in the 17-binding-extended context with a
    weakening `Γ → Γ'` and the three output-feeding values `Xn`, `Xn2q`, `T`.
    Every binding's de-Bruijn references are LOCAL to this block (identical to the
    single-butterfly template `fheBflyThir`), so concatenating `K` copies needs no
    hand-tracked cross-block indices — the running `.there`-lifts of the
    captured `Γ`-vars are what thread them forward. -/
def bflyCompute {Γ : Ctxt thirDialect} {σ : JasminTy}
    (X Y w wp cz c2q cq : Ctxt.Var Γ W64)
    (k : ∀ {Γ' : Ctxt thirDialect}, (∀ {t : JasminTy}, Ctxt.Var Γ t → Ctxt.Var Γ' t) →
          (Xn Xn2q T : Ctxt.Var Γ' W64) → Com thirDialect Γ' σ) :
    Com thirDialect Γ σ :=
  -- depth 0 ctx: Γ  with [X,Y,w,wp,cz,c2q,cq] captured
  -- b1 Xr = X - c2q
  .var (.mk (.thBin .sub 64) rfl (.cons X (.cons c2q .nil)))
  -- b2 Xb = Xr >>L 63        Xr@0
  (.var (.mk (.thShrImm 64 63) rfl (.cons .here .nil))
  -- b3 Xnm = cz - Xb         cz@(+2 from Γ-lift), Xb@0
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there (.there cz)) (.cons .here .nil)))
  -- b4 Xmsk = Xnm & c2q      Xnm@0, c2q@(+3)
  (.var (.mk (.thBin .and 64) rfl (.cons .here (.cons (.there (.there (.there c2q))) .nil)))
  -- b5 Xn = Xr + Xmsk        Xr@3, Xmsk@0
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there .here))) (.cons .here .nil)))
  -- b6 Xn2q = Xn + c2q       Xn@0, c2q@(+5)
  (.var (.mk (.thBin .add 64) rfl (.cons .here (.cons (.there (.there (.there (.there (.there c2q))))) .nil)))
  -- b7 loQ = Y * wp          Y@(+6), wp@(+6)   (DISCARDED low; feeds fuseMulHiLprog)
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there (.there (.there (.there (.there Y)))))) (.cons (.there (.there (.there (.there (.there (.there wp)))))) .nil)))
  -- b8 qhat = mulhi(Y, wp)   Y@(+7), wp@(+7)
  (.var (.mk (.thMulHi 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there Y))))))) (.cons (.there (.there (.there (.there (.there (.there (.there wp))))))) .nil)))
  -- b9 lo1 = w * Y           w@(+8), Y@(+8)
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there w)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there Y)))))))) .nil)))
  -- b10 lo2 = qhat * cq      qhat@1 (ctx head: lo1(0),qhat(1)), cq@(+9)
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there cq))))))))) .nil)))
  -- b11 Tlz = lo1 - lo2      lo1@1, lo2@0
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- b12 Tr = Tlz - cq        Tlz@0, cq@(+11)
  (.var (.mk (.thBin .sub 64) rfl (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there cq))))))))))) .nil)))
  -- b13 Tb = Tr >>L 63       Tr@0
  (.var (.mk (.thShrImm 64 63) rfl (.cons .here .nil))
  -- b14 Tnm = cz - Tb        cz@(+13), Tb@0
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there cz))))))))))))) (.cons .here .nil)))
  -- b15 Tmsk = Tnm & cq      Tnm@0, cq@(+14)
  (.var (.mk (.thBin .and 64) rfl (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there cq)))))))))))))) .nil)))
  -- b16 T = Tr + Tmsk        Tr@3, Tmsk@0  (ctx head: Tmsk(0),Tnm(1),Tb(2),Tr(3))
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there .here))) (.cons .here .nil)))
  -- now context (head-first) is: [T, Tmsk, Tnm, Tb, Tr, Tlz, lo2, lo1, qhat, loQ, Xn2q, Xn, Xmsk, Xnm, Xb, Xr] ++ Γ
  -- Xn  is at depth 11, Xn2q at depth 10, T at depth 0.
  (k (fun {_} v => (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there v)))))))))))))))))
     (Γ' := _)
     (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))   -- Xn @ 11
     (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))            -- Xn2q @ 10
     (.here))                                                                                                  -- T @ 0
  )))))))))))))))

/-! ## 3. One output binding (`Xo = Xn + T` or `Yo = Xn2q − T`) -/

/-- An output op: `true` ⇒ `a + b` (an `Xo`), `false` ⇒ `a − b` (a `Yo`). -/
def outExpr {Γ : Ctxt thirDialect} (isAdd : Bool) (a b : Ctxt.Var Γ W64) :
    Expr thirDialect Γ W64 :=
  .mk (.thBin (if isAdd then .add else .sub) 64) rfl (.cons a (.cons b .nil))

/-- Emit a tail of output bindings from a list of `(isAdd, a, b)` triples (all
    `Var Γ W64`), each `out_j = a_j (± ) b_j`. Earlier-built outputs are NOT
    referenced by later ones, so each triple's vars only need lifting past the
    outputs emitted before it. The `.ret` is the LAST output binding. -/
def emitOutputs {Γ : Ctxt thirDialect} :
    (outs : List (Bool × Ctxt.Var Γ W64 × Ctxt.Var Γ W64)) → outs ≠ [] →
    Com thirDialect Γ W64
  | [(isAdd, a, b)], _ => .var (outExpr isAdd a b) (.ret .here)
  | (isAdd, a, b) :: (r :: rest), _ =>
      .var (outExpr isAdd a b)
        (emitOutputs ((r :: rest).map (fun t => (t.1, .there t.2.1, .there t.2.2)))
          (by simp))
  termination_by outs => outs.length
  decreasing_by simp_wf

/-! ## 4. The `K`-butterfly straight-line block as a `Com thirDialect`

Three shared mask constants, then `K = 4` `bflyCompute` blocks, then `2K = 8`
output bindings (`Xo_k = Xn_k + T_k`, `Yo_k = Xn2q_k − T_k`) as the FINAL `2K`
bindings (so `comToLfundefPhysAbi`'s "last `2K`" epilogue stores
`out = [X0',Y0',X1',Y1',X2',Y2',X3',Y3']`). The `.ret` value is `Yo_3` (the very
last binding); the orchestrator's GMP KAT recovers all `8` outputs from `out`. -/
def fheNttBlockThir : Com thirDialect blkCtx W64 :=
  -- input vars in blkCtx (index i = .there^i .here). Group k inputs: 4k..4k+3.
  let X0 : Ctxt.Var blkCtx W64 := .here
  let Y0 : Ctxt.Var blkCtx W64 := .there .here
  let w0 : Ctxt.Var blkCtx W64 := .there (.there .here)
  let wp0 : Ctxt.Var blkCtx W64 := .there (.there (.there .here))
  let X1 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there .here)))
  let Y1 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there .here))))
  let w1 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there .here)))))
  let wp1 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there .here))))))
  let X2 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let Y2 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let w2 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let wp2 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  let X3 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
  let Y3 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
  let w3 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
  let wp3 : Ctxt.Var blkCtx W64 := .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))
  -- cz = 0
  .var (.mk (.thConst 64 0) rfl .nil)
  -- c2q = 2q
  (.var (.mk (.thConst 64 fheTwoQ) rfl .nil)
  -- cq = q
  (.var (.mk (.thConst 64 fheQ) rfl .nil)
  -- now ctx = [cq, c2q, cz] ++ blkCtx. Lift blkCtx vars by 3 = .there^3.
  (by
    -- Use a tactic-free term: define the lift-by-3 of blkCtx vars and nest the
    -- four butterfly computes, collecting outputs at the end.
    exact
      let L3 : (∀ {t : JasminTy}, Ctxt.Var blkCtx t → Ctxt.Var (W64 :: W64 :: W64 :: blkCtx) t) :=
        fun {_} v => .there (.there (.there v))
      let cz : Ctxt.Var (W64 :: W64 :: W64 :: blkCtx) W64 := .there (.there .here)
      let c2q : Ctxt.Var (W64 :: W64 :: W64 :: blkCtx) W64 := .there .here
      let cq : Ctxt.Var (W64 :: W64 :: W64 :: blkCtx) W64 := .here
      bflyCompute (L3 X0) (L3 Y0) (L3 w0) (L3 wp0) cz c2q cq
        (fun {_} h0 Xn0 Xn2q0 T0 =>
        bflyCompute (h0 (L3 X1)) (h0 (L3 Y1)) (h0 (L3 w1)) (h0 (L3 wp1))
            (h0 cz) (h0 c2q) (h0 cq)
          (fun {_} h1 Xn1 Xn2q1 T1 =>
          bflyCompute (h1 (h0 (L3 X2))) (h1 (h0 (L3 Y2))) (h1 (h0 (L3 w2))) (h1 (h0 (L3 wp2)))
              (h1 (h0 cz)) (h1 (h0 c2q)) (h1 (h0 cq))
            (fun {_} h2 Xn2 Xn2q2 T2 =>
            bflyCompute (h2 (h1 (h0 (L3 X3)))) (h2 (h1 (h0 (L3 Y3)))) (h2 (h1 (h0 (L3 w3)))) (h2 (h1 (h0 (L3 wp3))))
                (h2 (h1 (h0 cz))) (h2 (h1 (h0 c2q))) (h2 (h1 (h0 cq)))
              (fun {_} h3 Xn3 Xn2q3 T3 =>
              -- All four (Xn,Xn2q,T) lifted to the post-butterfly-3 context.
              -- Output order: X0' Y0' X1' Y1' X2' Y2' X3' Y3'.
              emitOutputs
                [ (true,  h3 (h2 (h1 Xn0)),  h3 (h2 (h1 T0)))    -- X0' = Xn0 + T0
                , (false, h3 (h2 (h1 Xn2q0)), h3 (h2 (h1 T0)))   -- Y0' = Xn2q0 − T0
                , (true,  h3 (h2 Xn1),       h3 (h2 T1))         -- X1' = Xn1 + T1
                , (false, h3 (h2 Xn2q1),     h3 (h2 T1))         -- Y1' = Xn2q1 − T1
                , (true,  h3 Xn2,            h3 T2)              -- X2' = Xn2 + T2
                , (false, h3 Xn2q2,          h3 T2)              -- Y2' = Xn2q2 − T2
                , (true,  Xn3,               T3)                 -- X3' = Xn3 + T3
                , (false, Xn2q3,             T3) ]               -- Y3' = Xn2q3 − T3
                (by simp))))))))

/-! ## 5. Reference / denotation theorems -/

/-- A 16-input valuation for `blkCtx` from the `K=4` quadruples. -/
def blkVal
    (X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3 : BitVec 64) :
    Ctxt.Valuation blkCtx :=
  .cons X0 <| .cons Y0 <| .cons w0 <| .cons wp0
  <| .cons X1 <| .cons Y1 <| .cons w1 <| .cons wp1
  <| .cons X2 <| .cons Y2 <| .cons w2 <| .cons wp2
  <| .cons X3 <| .cons Y3 <| .cons w3 <| .cons wp3 <| .nil

/-- The block's `.ret` output (`Y3'`), by definition the denotation. -/
def fheNttBlockSpec
    (X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3 : BitVec 64) : BitVec 64 :=
  fheNttBlockThir.denote
    (blkVal X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3)

/-- The block denotes `fheNttBlockSpec` — true by definition. -/
theorem fheNttBlockThir_denote
    (X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3 : BitVec 64) :
    fheNttBlockThir.denote
        (blkVal X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3)
      = fheNttBlockSpec X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3 := rfl

/-- **Block re-derived through the dialect spine.** The lowered `Com jasminDialect`
    denotes the same `BitVec 64` (the `Y3'` output) as the reference, via the
    generic proved `lowerThir_denote`. -/
theorem fheNttBlock_via_thirDialect
    (X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3 : BitVec 64) :
    (lowerThir fheNttBlockThir).denote
        (blkVal X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3)
      = fheNttBlockSpec X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3 :=
  (lowerThir_denote fheNttBlockThir _).trans
    (fheNttBlockThir_denote X0 Y0 w0 wp0 X1 Y1 w1 wp1 X2 Y2 w2 wp2 X3 Y3 w3 wp3)

/-! ## 6. Tiny value KAT (ONE slot vs the Harvey `Nat` reference)

The block's `.ret` is `Y3'`, the second component of butterfly 3's Harvey
reference `bflyRef X3 Y3 ω3 ω3'`. We pin ONLY this one slot (`fheNttBlock_slot0_kat`):
the per-butterfly arithmetic is identical to the already-KAT-checked single
butterfly (`FheNttButterflyEmit.fheBfly_kat0/1`), and the orchestrator KATs
all `8` outputs vs GMP. We do NOT `native_decide` all `K` slots. -/

/-- **KAT (block slot 3 `.ret` = `Y3'`).** Butterfly 3's inputs exercise the
    X-normalize (`X3 ∈ [2q, 4q)`) and the T-reduction; the other slots carry
    independent (small) data. The block's `.ret` equals `bflyRef`'s `Y'`. -/
theorem fheNttBlock_slot3_kat :
    (fheNttBlockSpec
        (BitVec.ofNat 64 (fheQ + 5)) (BitVec.ofNat 64 (2 * fheQ - 7))
          (BitVec.ofNat 64 kOmega) (BitVec.ofNat 64 kOmegaP)
        (BitVec.ofNat 64 (fheQ + 5)) (BitVec.ofNat 64 (2 * fheQ - 7))
          (BitVec.ofNat 64 kOmega) (BitVec.ofNat 64 kOmegaP)
        (BitVec.ofNat 64 (fheQ + 5)) (BitVec.ofNat 64 (2 * fheQ - 7))
          (BitVec.ofNat 64 kOmega) (BitVec.ofNat 64 kOmegaP)
        (BitVec.ofNat 64 (3 * fheQ + 12345)) (BitVec.ofNat 64 (fheQ + 99))
          (BitVec.ofNat 64 kOmega) (BitVec.ofNat 64 kOmegaP)).toNat
      = (bflyRef (3 * fheQ + 12345) (fheQ + 99) kOmega kOmegaP).2 := by native_decide

/-! ## 7. ABI maps for the 16-in / 8-out block -/

/-- Input-load map: context entry `i` (= `inp[i]`) is arg slot `s = 15 − i`, so
    `inLoadMap s = ("RSI", 8·(15 − s))`. Slots `≥ 16` absent. -/
def fheNttBlockInLoadMap : InLoadMap := fun s =>
  if s < 16 then some ("RSI", 8 * (15 - s)) else none

/-- Output-store map: `out[j]` at byte offset `8j`, `j = 0 … 7`
    (`X0',Y0',X1',Y1',X2',Y2',X3',Y3'`). -/
def fheNttBlockOutStoreMap : OutStoreMap :=
  [("RDI", 0), ("RDI", 8), ("RDI", 16), ("RDI", 24),
   ("RDI", 32), ("RDI", 40), ("RDI", 48), ("RDI", 56)]

/-! ## 8. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The `K=4`-butterfly straight-line block lowered through the thirDialect spine
    and exported to a physical, two-address SysV `Lprog` (16-input-load `inp`,
    8-store `out`), then `fuseMulHiLprog` coalesces each butterfly's discarded-low
    `Y·ω'` + `mulhi(Y,ω')` pair into a two-output `mulx`, and
    `legalizeShiftImmLprog` rewrites the sign-bit `shrImm`s into `shrq $63`.

    `saveRdx := true`: the owned linear scan homes the shared modulus constant
    `q` in `%rdx` and keeps it live across the whole block (every butterfly's
    `q̂·q`, `T − q` and `Tnm & q` read it), so each `mulx` site's multiplicand pin
    is bracketed with `MOV R15, RDX … MOV RDX, R15`. -/
def fheNttBlockLprog : Lprog :=
  legalizeShiftImmLprog (fuseMulHiLprog
    (Com.toLprogPhysAbi (lowerThir fheNttBlockThir) "fhe_ntt_block"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (constants are in-body regConst)
      fheNttBlockInLoadMap                  -- inLoadMap (16 inputs)
      fheNttBlockOutStoreMap                -- outStoreMap (8 outputs)
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      (List.replicate 16 64))               -- abiTyin (16 × u64)
    (saveRdx := true))

/-- The rendered owned-backend AT&T `.s` for `fhe_ntt_block` (no jasminc). -/
def fheNttBlockAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned fheNttBlockLprog

/-! ## 9. Rendered asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean hasSub check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 10. Emit driver -/

/-- Write the owned-backend `.s` for the `K=4`-butterfly straight-line block
    (`fhe_ntt_block`) into the `bench/fhe_ntt_compare/gen` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/fhe_ntt_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/fhe_ntt_block.s") fheNttBlockAsm
  IO.println "WROTE bench/fhe_ntt_compare/gen/fhe_ntt_block.s"
  IO.println "  (K=4 independent lazy Harvey FHE-NTT Shoup CT butterflies, straight-line, ONE prologue,"
  IO.println "   through Com[thir] -> lowerThir -> toLprogPhysAbi -> fuseMulHiLprog -> renderLprogAtt"
  IO.println "   onto the OWNED x86 backend, NO jasminc;"
  IO.println "   inp=[X0,Y0,w0,w0', .. X3,Y3,w3,w3'] (16 u64); out=[X0',Y0', .. X3',Y3'] (8 u64), all in [0,4q);"
  IO.println "   q = 1152921504606830593, R = 2^64; both conditional reductions branchless sign-mask)"

-- Emit during elaboration so `lake` owns the dependency: the `.s` under
-- `bench/fhe_ntt_compare/gen` is a build output of this module, and
-- `bfly_block_kat` therefore links what this module currently produces rather
-- than a checked-in copy.
-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttBlockEmit
