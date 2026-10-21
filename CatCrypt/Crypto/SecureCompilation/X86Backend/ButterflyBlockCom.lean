/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# NTT radix-2 butterfly on the UNIFIED `Com jasminDialect` (AVX-512 ZMM)

This is the SIMD-dialect-unification migration of the NTT radix-2 Cooley–Tukey
butterfly leaf off the bespoke `Avx512Model` (`ZInstr`) machine. The pre-existing
realization (`ButterflyBlockRealized.lean`) expresses the butterfly as a
straight-line three-instruction `ZInstr` block over the bespoke AVX-512 register
machine (`ZState`, `runZBlock`):

```
butterflyBlock = [ .vpmullq "zt"  "zw" "zb"    -- zt  = zw ⊙ zb
                 , .vpaddq  "zhi" "za" "zt"    -- zhi = za + zt
                 , .vpsubq  "zlo" "za" "zt" ]  -- zlo = za − zt
```

Each `ZInstr` op is a carry-free / borrow-free 8×u64 packed-lane op. The verified Jasmin
VIR dialect (`JasminDialect.lean`) already carries `JasminOp.vpackZMM (bop)` —
the 8×u64 packed-lane register op (the `#VPADD_8u64` / `#VPSUB_8u64` /
`#VPMULL_8u64` image, denote `zmmPackQ bop`). The three `ZInstr` ops map EXACTLY
onto `vpackZMM`:

* `.vpmullq`  ↦  `JasminOp.vpackZMM .mul`   (denote `zmmPackQ .mul`)
* `.vpaddq`   ↦  `JasminOp.vpackZMM .add`   (denote `zmmPackQ .add`)
* `.vpsubq`   ↦  `JasminOp.vpackZMM .sub`   (denote `zmmPackQ .sub`)

None of the three is a cross-lane op (no `vpermq` permute, no `vpsllvq` variable
shift), so the butterfly is fully covered by the carry-free `vpackZMM` alphabet —
no new `SimdOp` is needed. This module re-expresses the SAME butterfly as
straight-line `Com jasminDialect` programs over `reg 512` ZMM registers, off the
bespoke `Avx512Model` machine. A `Com jasminDialect` built from `vpackZMM` ops
lowers to AT&T `.s` through the existing `JasminPrint`/`JasminPrintSemCorrect`
path.

## What is proved here

The butterfly is two outputs (`hi`, `lo`) sharing the twiddle multiply; a `Com`
is single-output, so the structure is given as two straight-line programs over the
input context `[w, a, b]` (each `reg 512`):

* `butterflyHiCom` — `prod := w ⊙ b`, then `hi := a + prod`;
* `butterflyLoCom` — `prod := w ⊙ b`, then `lo := a − prod`.

`butterflyHiCom_denote` / `butterflyLoCom_denote` characterize the denotation on
any `(w, a, b)` valuation as

```
hi = zmmPackQ .add a (zmmPackQ .mul w b)
lo = zmmPackQ .sub a (zmmPackQ .mul w b)
```

— the verified-dialect packed `a + (w ⊙ b)` / `a − (w ⊙ b)`, the same butterfly
the bespoke `butterflyBlock` computes lane-by-lane (`ZState` `laneAddQ`/`laneSubQ`
over `laneMullq`), reusing `zmmPackQ` with no re-proof of the lane math. The
denote lemmas elaborate by `rfl`: `Com.denote` of a two-binding straight-line
program unfolds definitionally through the `vpackZMM` denote arm to the two
`zmmPackQ` calls.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Register types and the input context

A single `reg 512` (one ZMM 8×u64 lane-vector) is the kernel's working type. The
butterfly has three inputs, in de-Bruijn order `[w, a, b]`:

* `w` — the twiddle factor (de Bruijn `0`, `.here`);
* `a` — the even/low data register (de Bruijn `1`, `.there .here`);
* `b` — the odd/high data register (de Bruijn `2`, `.there (.there .here)`). -/

/-- The `reg 512` dialect type (one ZMM 8×u64 lane-vector), abbreviated. -/
abbrev r512 : JasminTy := .reg 512

/-- The input context of the butterfly: `[w, a, b]`, each `reg 512`. -/
abbrev bflyCtx : Ctxt jasminDialect := [r512, r512, r512]

/-! ## 2. The dialect-native butterfly programs `Com jasminDialect`

```
let prod = vpackZMM mul w b        -- prod := w ⊙ b   (the twiddle multiply)
let hi   = vpackZMM add a prod     -- hi   := a + prod
ret hi
```

Binding 1 (`vpackZMM .mul`) consumes `w` (`.here` in `bflyCtx`) and `b`
(`.there (.there .here)`), producing `prod` at the front. Under the extended
context `[prod, w, a, b]`, binding 2 consumes `a` (now `.there (.there .here)`)
and `prod` (`.here`), with `.add` for the `hi` output and `.sub` for `lo`. -/

/-- The migrated radix-2 butterfly `hi` output as a `Com jasminDialect` over
    `reg 512` registers — the dialect-native equivalent of the bespoke
    `butterflyBlock`'s `vpmullq`/`vpaddq` slice: `hi = a + (w ⊙ b)`. -/
def butterflyHiCom : Com jasminDialect bflyCtx r512 :=
  -- prod := w ⊙ b   (w = .here, b = .there (.there .here))
  .var (.mk (.vpackZMM .mul) rfl
          (.cons .here (.cons (.there (.there .here)) .nil)))
    -- hi := a + prod   (a is now .there (.there .here), prod is .here)
    (.var (.mk (.vpackZMM .add) rfl
            (.cons (.there (.there .here)) (.cons .here .nil)))
      (.ret .here))

/-- The migrated radix-2 butterfly `lo` output as a `Com jasminDialect` over
    `reg 512` registers — the dialect-native equivalent of the bespoke
    `butterflyBlock`'s `vpmullq`/`vpsubq` slice: `lo = a − (w ⊙ b)`. -/
def butterflyLoCom : Com jasminDialect bflyCtx r512 :=
  -- prod := w ⊙ b
  .var (.mk (.vpackZMM .mul) rfl
          (.cons .here (.cons (.there (.there .here)) .nil)))
    -- lo := a − prod
    (.var (.mk (.vpackZMM .sub) rfl
            (.cons (.there (.there .here)) (.cons .here .nil)))
      (.ret .here))

/-! ## 3. Denotation characterization

Each program computes the verified-dialect packed butterfly output, with
`zmmPackQ` the 8×u64 packed-lane semantics (`= zmmOfLanes (lane-wise bop)`). The
proofs are `rfl`: `Com.denote` of the two-binding programs unfolds definitionally
through the `vpackZMM` denote arm to the two `zmmPackQ` calls. -/

/-- **Butterfly `hi` denotation pin.** On any input valuation `⟨w, a, b⟩`,
    `butterflyHiCom` denotes to `zmmPackQ .add a (zmmPackQ .mul w b)` — the
    verified-dialect packed `a + (w ⊙ b)`, exactly the value the bespoke
    `butterflyBlock` writes into `"zhi"` lane-by-lane. -/
theorem butterflyHiCom_denote (w a b : BitVec 512) :
    butterflyHiCom.denote (.cons w (.cons a (.cons b .nil)))
      = zmmPackQ .add a (zmmPackQ .mul w b) :=
  rfl

/-- **Butterfly `lo` denotation pin.** On any input valuation `⟨w, a, b⟩`,
    `butterflyLoCom` denotes to `zmmPackQ .sub a (zmmPackQ .mul w b)` — the
    verified-dialect packed `a − (w ⊙ b)`, exactly the value the bespoke
    `butterflyBlock` writes into `"zlo"` lane-by-lane. -/
theorem butterflyLoCom_denote (w a b : BitVec 512) :
    butterflyLoCom.denote (.cons w (.cons a (.cons b .nil)))
      = zmmPackQ .sub a (zmmPackQ .mul w b) :=
  rfl

/-! ## 4. Both outputs at once

The two denotation pins packaged together: the shared twiddle multiply
`zmmPackQ .mul w b` feeds the `add` (`hi`) and `sub` (`lo`) butterfly outputs —
the composed-kernel deliverable, one dialect twiddle product realizing the whole
radix-2 butterfly, mirroring the bespoke `butterflyBlock_realizes`. -/

/-- `butterflyHiCom`/`butterflyLoCom` compute **both** packed butterfly outputs
    from the shared twiddle product `zmmPackQ .mul w b`: `hi = a + (w ⊙ b)` and
    `lo = a − (w ⊙ b)`, in the verified `Com jasminDialect`. -/
theorem butterflyCom_realizes (w a b : BitVec 512) :
    butterflyHiCom.denote (.cons w (.cons a (.cons b .nil)))
        = zmmPackQ .add a (zmmPackQ .mul w b)
      ∧ butterflyLoCom.denote (.cons w (.cons a (.cons b .nil)))
        = zmmPackQ .sub a (zmmPackQ .mul w b) :=
  ⟨butterflyHiCom_denote w a b, butterflyLoCom_denote w a b⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom
