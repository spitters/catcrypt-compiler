/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# PROBE: a lazy (Harvey) FHE-NTT Shoup butterfly through the OWNED x86 backend

A feasibility probe for emitting a full lazy NTT butterfly — including its
**conditional reductions** — on CatCrypt's owned scalar x86 backend, with no
jasminc. The gating question was whether the `if X ≥ 2q: X −= 2q` (and the
final `if T ≥ q: T −= q`) conditional subtracts can be emitted at all, since
the GP-linear `Lprog` printer renders neither `thSelect` nor a `CMOV` (the
modmul work pushed the csub host-side; cf. `FheShoupEmit` §docstring).

## Result: YES — via the branchless arithmetic mask-trick (no branch, no CMOV)

The conditional subtract is the standard sign-bit mask the ML-DSA `decompose`
emit already uses (`MLDSA/DecomposeEmit.decomposeBody`):

```
  r = X − 2q                  -- SUB
  m = r >>ₐ 63                -- SAR (arithmetic): all-ones iff X < 2q (r negative)
  m = m & 2q                  -- AND: (X < 2q ? 2q : 0)
  X = r + m                   -- ADD: = (X ≥ 2q ? X − 2q : X)
```

`X ≥ 2q ⟹ r ≥ 0 ⟹ SAR 63 = 0 ⟹ m = 0 ⟹ X = r = X − 2q`; and
`X < 2q ⟹ r < 0 ⟹ SAR 63 = all-ones ⟹ m = 2q ⟹ X = r + 2q = X`. Every op
(`SUB`/`SAR`/`AND`/`ADD`) is a pure data op the **scalar `JInstr` printer**
(`AsmPrinter.renderJInstr`) renders 1:1 to `subq`/`sarq`/`andq`/`addq`. This is
data-oblivious (constant-time) and needs no control flow at all — so it sidesteps
both the missing `select`→CMOV rendering and any secret-dependent branch.

(The owned backend *can* also emit a real `cmp; jcc` branch — `LprogControlFlow.loopLcmd`
emits `cmpq $0,%n; jne .L` and the printer has the full `attCC` Jcc map — but that
path is reserved for the **public** loop counter; a secret-data conditional
subtract must stay branchless, which the mask-trick is.)

## The butterfly

Inputs `X, Y ∈ [0, 4q)`, twiddle `ω`, precomputed Shoup constant `ω' = ⌊ω·R/q⌋`,
`R = 2^64`, `q` the 60-bit FHE prime. Harvey's lazy CT butterfly:

```
  if X ≥ 2q: X −= 2q                 -- normalize X to [0, 2q)   (mask-trick)
  q̂ = mulhi(Y, ω')                   -- Shoup quotient = ⌊Y·ω'/R⌋   (MULX high word)
  T = ω·Y − q̂·q   (mod 2^64)        -- lazy product, lands in [0, 2q)
  if T ≥ q: T −= q                   -- reduce T to [0, q)         (mask-trick)
  Xo = X + T                         -- ADD
  Yo = X + 2q − T                    -- ADD; SUB
```

`T = lo(ω·Y) − lo(q̂·q)` is a single 64-bit subtraction (the true value is in
`[0, 2q) ⊂ [0, 2^64)`, so the high words cancel — same reason `FheShoupEmit`
has no carry chain). `q̂` is `mulhi`, taken as the high output of `MULX`.

## What is verified here

* **Value (in Lean)**: `butterfly_kat0`/`butterfly_kat1` — `runBlock` over
  `butterflyBody` equals the `Nat` reference `shoupRefBF` on two vectors (one
  with `X ∈ [2q,4q)` exercising the X-normalize, one with `X < 2q`), by
  `native_decide` (small vectors, so the check stays cheap).
* **Rendered asm shape**: `butterflyAsm_*` — the emitted AT&T text carries BOTH
  conditional reductions as the mask-trick (`sarq $63`, `andq $<2q>`,
  `andq $<q>`), the Shoup `mulx`, and no `<UNALLOCATED>` sentinel (the body fits
  the GP pool). This is the headline: the conditional reduction is *present* in
  the emitted code, not host-side.

## Gap (the `mulx` rdx-pin — pre-existing, shared with FheShoupEmit)

`AT&T mulx src2, dstLo, dstHi` pins src1 to `%rdx`. The first-fit `allocGp`
assigns `%rdx` to whatever name appears third; it does NOT evacuate src1 of the
`MULX` into `%rdx`. So the *rendered* `mulx` line's implicit src1 register is not
guaranteed to hold `Y`. The `runBlock` semantics uses `a.eval`/`b.eval` directly
(ignoring the physical rdx pin), so the value KAT passes; but a faithful `.s`
needs the rdx evacuation that the `Lprog` path's `FuseMulHi.fuseMulHiLprog`
performs. This probe deliberately stays on the simpler scalar `JInstr` printer to
isolate the *conditional-reduction* question; the Shoup high-word `mulx` should be
routed through `fuseMulHiLprog` (as `FheShoupEmit` does) for a shippable
kernel. The conditional-reduction result is independent of this and fully stands.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttButterflyProbe

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. FHE-NTT prime constant -/

/-- The 60-bit FHE prime `q = 2^60 − 2^14 + 1` (matches `FheShoupMulLaw.fheQ`). -/
def fheQ : Nat := 1152921504606830593
/-- `2q`, the X-normalization boundary / lazy upper bound. -/
def fheTwoQ : Nat := 2 * fheQ

/-! ## 2. The owned lazy Shoup butterfly body (scalar `JInstr 64`)

Registers: inputs `X`, `Y`, `omega`, `omegaP` (= ω'); outputs `Xo`, `Yo`; scratch
`qhat`/`qlo`/`T`/`cq`/`r`/`m`. The two `if … : … −= …` conditional reductions are
the SAR-sign-mask trick (`r = v − c; m = (r >>ₐ 63) & c; v = r + m`). -/
def butterflyBody : List (JInstr 64) :=
  -- normalize X: if X ≥ 2q then X −= 2q   (branchless mask-trick)
  [ .mov "r" (.reg "X"), .sub "r" (.imm fheTwoQ)        -- r = X − 2q
  , .mov "m" (.reg "r"), .sar "m" (.imm 63)             -- m = r >>ₐ 63  (all-ones iff X<2q)
  , .and_ "m" (.imm fheTwoQ)                            -- m = (X<2q ? 2q : 0)
  , .add "r" (.reg "m"), .mov "X" (.reg "r")            -- X = r + m  = (X≥2q ? X−2q : X)
  -- Shoup product: T = ω·Y − q̂·q,  q̂ = mulhi(Y, ω')
  , .mulx "qhat" "qlo" (.reg "Y") (.reg "omegaP")       -- q̂ = hi(Y·ω'); qlo = lo (discarded)
  , .mov "T" (.reg "omega"), .imul "T" (.reg "Y")       -- T = lo(ω·Y)
  , .mov "cq" (.imm fheQ)
  , .imul "qhat" (.reg "cq")                            -- q̂ = lo(q̂·q)
  , .sub "T" (.reg "qhat")                              -- T = ω·Y − q̂·q   (in [0, 2q))
  -- reduce T to [0, q): if T ≥ q then T −= q   (branchless mask-trick)
  , .mov "r" (.reg "T"), .sub "r" (.imm fheQ)           -- r = T − q
  , .mov "m" (.reg "r"), .sar "m" (.imm 63)             -- m all-ones iff T<q
  , .and_ "m" (.imm fheQ)
  , .add "r" (.reg "m"), .mov "T" (.reg "r")            -- T = (T≥q ? T−q : T)
  -- outputs: Xo = X + T ; Yo = X + 2q − T
  , .mov "Xo" (.reg "X"), .add "Xo" (.reg "T")          -- Xo = X + T
  , .mov "Yo" (.reg "X"), .add "Yo" (.imm fheTwoQ), .sub "Yo" (.reg "T") ]  -- Yo = X + 2q − T

/-! ## 3. The `Nat` lazy-Shoup reference (Harvey) and the executable run -/

/-- The lazy Shoup butterfly over `Nat` (Harvey), all arithmetic mod `2^64`. -/
def shoupRefBF (X Y omega omegaP : Nat) : Nat × Nat :=
  let X := if X ≥ fheTwoQ then X - fheTwoQ else X
  let qhat := (Y * omegaP) / 2 ^ 64
  let T := (omega * Y - qhat * fheQ) % 2 ^ 64
  let T := if T ≥ fheQ then T - fheQ else T
  ((X + T) % 2 ^ 64, (X + fheTwoQ - T) % 2 ^ 64)

/-- Run `butterflyBody` from a state with the four input registers set; read the
    two output words `(Xo, Yo)`. -/
def runBF (X Y omega omegaP : Nat) : Nat × Nat :=
  let s0 : JState 64 :=
    { regs := fun rr =>
        if rr = "X" then BitVec.ofNat 64 X
        else if rr = "Y" then BitVec.ofNat 64 Y
        else if rr = "omega" then BitVec.ofNat 64 omega
        else if rr = "omegaP" then BitVec.ofNat 64 omegaP else 0 }
  let s := runBlock s0 butterflyBody
  ((s.get "Xo").toNat, (s.get "Yo").toNat)

/-! ## 4. Value KATs: owned body == Harvey reference

Concrete vectors. `omegaP = ⌊omega·R/q⌋` is the precomputed Shoup constant. -/

/-- A small twiddle. -/
def kOmega : Nat := 1000000007
/-- Its Shoup constant `⌊ω·R/q⌋`. -/
def kOmegaP : Nat := kOmega * 2 ^ 64 / fheQ

/-- **KAT 0 (X ∈ [2q,4q), exercises the X-normalize).** -/
theorem butterfly_kat0 :
    runBF (3 * fheQ + 12345) (fheQ + 99) kOmega kOmegaP
      = shoupRefBF (3 * fheQ + 12345) (fheQ + 99) kOmega kOmegaP := by native_decide

/-- **KAT 1 (X already < 2q).** -/
theorem butterfly_kat1 :
    runBF (fheQ + 5) (2 * fheQ - 7) kOmega kOmegaP
      = shoupRefBF (fheQ + 5) (2 * fheQ - 7) kOmega kOmegaP := by native_decide

/-! ## 5. The rendered owned-backend asm (scalar `JInstr` printer) -/

/-- First-fit GP allocation for the butterfly body (no pins). -/
def butterflyAlloc : GpAlloc := allocGp [] butterflyBody

/-- The rendered AT&T `.s` body for the lazy Shoup butterfly (no jasminc). -/
def butterflyAsm : String :=
  String.intercalate "\n" (renderBlockBody butterflyAlloc butterflyBody)

/-- Substring test (mirrors `FheMontMulEmit.hasSub`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-! ## 6. Shape checks: the conditional reductions ARE in the emitted asm -/

/-- The body fits the GP pool (no `<UNALLOCATED>` aliasing). -/
theorem butterfly_fits_pool : allocOverflow ([] : GpAlloc) butterflyBody = none := by
  native_decide

/-- The emitted `.s` carries the arithmetic sign-mask shift `sarq $63` — the
    heart of BOTH branchless conditional reductions. -/
theorem butterflyAsm_has_sar : hasSub butterflyAsm "sarq $63" = true := by native_decide

/-- The X-normalization conditional subtract is present: `andq $<2q>`. -/
theorem butterflyAsm_has_2q_mask :
    hasSub butterflyAsm "andq $2305843009213661186" = true := by native_decide

/-- The T-reduction conditional subtract is present: `andq $<q>`. -/
theorem butterflyAsm_has_q_mask :
    hasSub butterflyAsm "andq $1152921504606830593" = true := by native_decide

/-- The Shoup quotient high word is emitted as a `mulx`. -/
theorem butterflyAsm_has_mulx : hasSub butterflyAsm "mulx" = true := by native_decide

/-- No unallocated-register sentinel in the emitted `.s`. -/
theorem butterflyAsm_no_unalloc : hasSub butterflyAsm "UNALLOCATED" = false := by native_decide

/-- **Headline.** The lazy Shoup butterfly's two conditional reductions emit on
    the owned backend via the branchless SAR-sign-mask trick (`sarq $63` + the two
    `andq` masks), alongside the Shoup `mulx` — all rendered, fitting the GP pool,
    with no unallocated sentinel. The conditional reduction is in the emitted code,
    not host-side. (The `mulx` rdx-pin caveat is in the module docstring.) -/
theorem butterflyAsm_emits_conditional_reduction :
    allocOverflow ([] : GpAlloc) butterflyBody = none
      ∧ hasSub butterflyAsm "sarq $63" = true
      ∧ hasSub butterflyAsm "andq $2305843009213661186" = true
      ∧ hasSub butterflyAsm "andq $1152921504606830593" = true
      ∧ hasSub butterflyAsm "mulx" = true
      ∧ hasSub butterflyAsm "UNALLOCATED" = false :=
  ⟨butterfly_fits_pool, butterflyAsm_has_sar, butterflyAsm_has_2q_mask,
   butterflyAsm_has_q_mask, butterflyAsm_has_mulx, butterflyAsm_no_unalloc⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttButterflyProbe
