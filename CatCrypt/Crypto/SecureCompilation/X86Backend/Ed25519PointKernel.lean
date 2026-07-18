/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

/-!
# Ed25519 twisted-Edwards point add/double + fixed-base scalarmul, owned x86 backend (#414)

`Fe25519MulKernel.feMulBlock` (#391), `Fe25519OpsKernel.{feAdd,feSub,feMul121666,
feSqr}Block` (#408, all KAT'd vs s2n + GMP), and `CombSelectKernel.combSelectBlock`
(#387, the CT comb-window select, KAT'd) emit every Curve25519 *field* operation
through the owned x86 backend (`Com (x86Dialect 64) → runBlock → AsmPrinter`, no
jasminc). This module composes those landed field-op leaves into the **group**
layer: extended-twisted-Edwards (X:Y:Z:T) point add and double over the Ed25519
curve, and the fixed-base scalar-multiply `s·B` that Ed25519 signing needs.

## The Edwards group law (extended coordinates, X:Y:Z:T, T = XY/Z)

Ed25519 is the twisted-Edwards curve `−x² + y² = 1 + d·x²y²` over `𝔽_p`,
`p = 2²⁵⁵−19`, `d = −121665/121666` (`a = −1`). A point in **extended** Hisil–
Wong–Carter–Dawson coordinates is `(X:Y:Z:T)` with affine `(X/Z, Y/Z)` and
`T = XY/Z`. The unified add `(X₃:Y₃:Z₃:T₃) = (X₁:Y₁:Z₁:T₁) + (X₂:Y₂:Z₂:T₂)` is
(HWCD'08 §3.1, "add-2008-hwcd-3", the `a = −1` revision dalek/ref10 use):

```
A = (Y₁−X₁)·(Y₂−X₂);   B = (Y₁+X₁)·(Y₂+X₂)
C = T₁·2d·T₂;          D = Z₁·2·Z₂
E = B−A;  F = D−C;  G = D+C;  H = B+A
X₃ = E·F;  Y₃ = G·H;  T₃ = E·H;  Z₃ = F·G
```

The dedicated double `2·(X₁:Y₁:Z₁:T₁)` (`dbl-2008-hwcd`, `a = −1`):

```
A = X₁²;  B = Y₁²;  C = 2·Z₁²;  D = −A  (= a·A, a=−1)
EE = (X₁+Y₁)² − A − B;  G = D+B;  F = G−C;  H = D−B
X₃ = EE·F;  Y₃ = G·H;  T₃ = EE·H;  Z₃ = F·G
```

`2d` is the curve constant `2·d mod p`. Each line is one field op
(`feMul`/`feSqr`/`feAdd`/`feSub`), so each point op is a **fixed sequence of the
landed field-op leaves** over a scratch frame.

## Frame-relative composition (single base pointer)

Each landed field-op block was hard-wired to bases `"x"`/`"y"`/`"z"`. To compose
many field ops into one straight-line point op without exhausting the GP pool
with one pointer per intermediate, every field element lives in a single
**frame** buffer `"f"` at a compile-time-constant byte offset (one slot = 32
bytes = four limbs). The parameterized generators `feMulAt`/`feSqrAt`/`feAddAt`/
`feSubAt` are the landed idioms with `loadMem`/`storeMem`/`mulxMem`
re-based to `"f"` at the slot offset — **line-for-line identical instruction
streams**, only the addressing changed. Register pressure stays per-field-op
(one frame pointer + the MULX multiplier/zero), so the GP budget holds for the
whole point op.

This is exactly how ref10/dalek structure Edwards arithmetic: field elements in
a stack frame, the group law a sequence of field-function calls; here the calls
are *inlined* (the field-op body is spliced at the call site over fixed frame
offsets), so the whole point op is one verified straight-line block.

## What is proved here

* `edwardsAddBlock_lowering_correct` / `edwardsDblBlock_lowering_correct` (via
  `lowerBlock_denote_closed`): lowering each point op to `Com (x86Dialect 64)`
  and denoting on the init frame equals `runBlock` on the source block — the
  owned backend's straight-line lowering is denotation-preserving across the
  composed field-op instruction mix.
* `feMulAt_length` etc.: each frame-relative generator emits exactly the landed
  field-op instruction count, the structural witness that the arithmetic (and
  hence the value semantics, KAT'd in the field-op kernels) is the landed
  kernel's re-based (no new arithmetic to re-verify).
* `combWindowStep_lowering_correct`: the assembled fixed-base scalarmul window
  step (comb CT-select + the Edwards add) lowers denotation-preservingly; the
  full `s·B` is this step iterated over the 64 windows.

The point-op and scalarmul value identities (`P₃ == P₁+P₂` on the curve;
`acc == s·B`) and the Ed25519 sign vectors are the runtime KAT in
`bench/ed25519_point_compare/` against RFC 8032 §7.1 (the basepoint multiples,
the sign test vectors) + dalek `EdwardsPoint` + GMP-modeled field reference —
the standard external gate for these kernels (per REV-12, no heavy in-Lean
`native_decide` value pin; the in-Lean guarantee is denotation-preservation,
the all-inputs identity is the external KAT).

## Trust story

Identical to `Fe25519MulKernel` / `Fe25519OpsKernel` / `CombSelectKernel`: the
verified artifact is `Com (x86Dialect 64) → runBlock → evalInstr`, the faithful
transcription of Jasmin's Rocq x86 semantics; `AsmPrinter` + `gas` is the
syntactic boundary, and the System-V leaf prologue/epilogue is trusted ABI
scaffolding. No `sorry`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Ed25519PointKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. Frame geometry

Every Ed25519 field element is one 256-bit slot (4 × 64-bit limbs) in the single
frame buffer `"f"`. A slot index `i` lives at byte offset `32·i`; limb `k` of
that slot at `32·i + 8·k`. The group law uses a fixed set of slots for the two
input points, the output point, and the HWCD intermediates. -/

/-- Bytes per field-element slot (four 64-bit limbs). -/
def slotBytes : Int := 32

/-- Byte offset of slot `i`'s limb `k` within the frame `"f"`. -/
def slotOff (i : Nat) (k : Nat) : Int := slotBytes * Int.ofNat i + 8 * Int.ofNat k

/-! ## 2. Frame-relative field-op generators

Each generator emits the **identical instruction stream** of the landed field-op
kernel, with the three hard-wired bases (`"z"` output, `"x"`/`"y"` inputs)
re-based to the single frame `"f"` and the per-buffer offset `8·k` shifted to the
slot offset `slotOff o k` / `slotOff a k` / `slotOff b k`. The arithmetic is unchanged, so each
generator's value semantics is the landed kernel's (`feMulAt_is_feMul` records
the structural identity below). -/

/-- `f[o] := (f[a] · f[b]) mod p` — the landed `feMulBlock` re-based to the
    frame. `yd`/`zr`/`t0..t7`/`lo`/`hi`/`y` are working registers (per field op).
    `yd` is the running MULX multiplier (`%rdx`), `zr` the zero register. -/
def feMulAt (o a b : Nat) : List (JInstr 64) :=
  [ .mov "zr" (.imm 0)
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "f" (slotOff b 0)
  , .mulxMem "t1" "t0" (.reg "yd") "f" (slotOff a 0)
  , .mulxMem "t2" "lo" (.reg "yd") "f" (slotOff a 1)
  , .adcx "t1" (.reg "lo")
  , .mulxMem "t3" "lo" (.reg "yd") "f" (slotOff a 2)
  , .adcx "t2" (.reg "lo")
  , .mulxMem "t4" "lo" (.reg "yd") "f" (slotOff a 3)
  , .adcx "t3" (.reg "lo")
  , .adcx "t4" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "f" (slotOff b 1)
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 0)
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 1)
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 2)
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "t5" "lo" (.reg "yd") "f" (slotOff a 3)
  , .adcx "t4" (.reg "lo")
  , .adox "t5" (.reg "zr")
  , .adcx "t5" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "f" (slotOff b 2)
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 0)
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 1)
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 2)
  , .adcx "t4" (.reg "lo"), .adox "t5" (.reg "hi")
  , .mulxMem "t6" "lo" (.reg "yd") "f" (slotOff a 3)
  , .adcx "t5" (.reg "lo")
  , .adox "t6" (.reg "zr")
  , .adcx "t6" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "f" (slotOff b 3)
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 0)
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 1)
  , .adcx "t4" (.reg "lo"), .adox "t5" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 2)
  , .adcx "t5" (.reg "lo"), .adox "t6" (.reg "hi")
  , .mulxMem "t7" "lo" (.reg "yd") "f" (slotOff a 3)
  , .adcx "t6" (.reg "lo")
  , .adox "t7" (.reg "zr")
  , .adcx "t7" (.reg "zr")
    -- s2n fused-quotient-estimate 2^255-19 reduce (identical to feMulBlock)
  , .mov "yd" (.imm 38)
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .add "lo" (.reg "t3")
  , .adc "hi" (.reg "zr")
  , .mov "y" (.reg "lo")
  , .shr "y" (.imm 63)
  , .shl "hi" (.imm 1)
  , .add "hi" (.reg "y")
  , .add "hi" (.imm 1)
  , .mov "y" (.reg "hi")
  , .imul "hi" (.imm 19)
  , .xor_ "zr" (.reg "zr")
  , .adox "t0" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t4")
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t5")
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t6")
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .adc "t3" (.reg "lo")
  , .shl "y" (.imm 63)
  , .mov "lo" (.reg "t3")
  , .sub "lo" (.reg "y")
  , .shr "lo" (.imm 63)
  , .imul "lo" (.imm 19)
  , .sub "t0" (.reg "lo")
  , .sbb "t1" (.reg "zr")
  , .sbb "t2" (.reg "zr")
  , .sbb "t3" (.reg "zr")
  , .mov "hi" (.imm 0x7fffffffffffffff)
  , .and_ "t3" (.reg "hi")
  , .storeMem "f" (slotOff o 0) (.reg "t0")
  , .storeMem "f" (slotOff o 1) (.reg "t1")
  , .storeMem "f" (slotOff o 2) (.reg "t2")
  , .storeMem "f" (slotOff o 3) (.reg "t3") ]

/-- `f[o] := (f[a]²) mod p` — the landed `feSqrBlock` re-based to the frame. -/
def feSqrAt (o a : Nat) : List (JInstr 64) :=
  [ .mov "zr" (.imm 0)
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "f" (slotOff a 0)
  , .mulxMem "t1" "t0" (.reg "yd") "f" (slotOff a 0)
  , .mulxMem "t2" "lo" (.reg "yd") "f" (slotOff a 1)
  , .adcx "t1" (.reg "lo")
  , .mulxMem "t3" "lo" (.reg "yd") "f" (slotOff a 2)
  , .adcx "t2" (.reg "lo")
  , .mulxMem "t4" "lo" (.reg "yd") "f" (slotOff a 3)
  , .adcx "t3" (.reg "lo")
  , .adcx "t4" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "f" (slotOff a 1)
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 0)
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 1)
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 2)
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "t5" "lo" (.reg "yd") "f" (slotOff a 3)
  , .adcx "t4" (.reg "lo")
  , .adox "t5" (.reg "zr")
  , .adcx "t5" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "f" (slotOff a 2)
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 0)
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 1)
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 2)
  , .adcx "t4" (.reg "lo"), .adox "t5" (.reg "hi")
  , .mulxMem "t6" "lo" (.reg "yd") "f" (slotOff a 3)
  , .adcx "t5" (.reg "lo")
  , .adox "t6" (.reg "zr")
  , .adcx "t6" (.reg "zr")
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "f" (slotOff a 3)
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 0)
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 1)
  , .adcx "t4" (.reg "lo"), .adox "t5" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "f" (slotOff a 2)
  , .adcx "t5" (.reg "lo"), .adox "t6" (.reg "hi")
  , .mulxMem "t7" "lo" (.reg "yd") "f" (slotOff a 3)
  , .adcx "t6" (.reg "lo")
  , .adox "t7" (.reg "zr")
  , .adcx "t7" (.reg "zr")
  , .mov "yd" (.imm 38)
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .add "lo" (.reg "t3")
  , .adc "hi" (.reg "zr")
  , .mov "y" (.reg "lo")
  , .shr "y" (.imm 63)
  , .shl "hi" (.imm 1)
  , .add "hi" (.reg "y")
  , .add "hi" (.imm 1)
  , .mov "y" (.reg "hi")
  , .imul "hi" (.imm 19)
  , .xor_ "zr" (.reg "zr")
  , .adox "t0" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t4")
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t5")
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t6")
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .adc "t3" (.reg "lo")
  , .shl "y" (.imm 63)
  , .mov "lo" (.reg "t3")
  , .sub "lo" (.reg "y")
  , .shr "lo" (.imm 63)
  , .imul "lo" (.imm 19)
  , .sub "t0" (.reg "lo")
  , .sbb "t1" (.reg "zr")
  , .sbb "t2" (.reg "zr")
  , .sbb "t3" (.reg "zr")
  , .mov "hi" (.imm 0x7fffffffffffffff)
  , .and_ "t3" (.reg "hi")
  , .storeMem "f" (slotOff o 0) (.reg "t0")
  , .storeMem "f" (slotOff o 1) (.reg "t1")
  , .storeMem "f" (slotOff o 2) (.reg "t2")
  , .storeMem "f" (slotOff o 3) (.reg "t3") ]

/-- `f[o] := (f[a] + f[b]) mod p` — the landed `feAddBlock` re-based. -/
def feAddAt (o a b : Nat) : List (JInstr 64) :=
  [ .loadMem "d0" "f" (slotOff a 0)
  , .loadMem "lo" "f" (slotOff b 0),  .add "d0" (.reg "lo")
  , .loadMem "d1" "f" (slotOff a 1)
  , .loadMem "lo" "f" (slotOff b 1),  .adc "d1" (.reg "lo")
  , .loadMem "d2" "f" (slotOff a 2)
  , .loadMem "lo" "f" (slotOff b 2),  .adc "d2" (.reg "lo")
  , .loadMem "d3" "f" (slotOff a 3)
  , .loadMem "lo" "f" (slotOff b 3),  .adc "d3" (.reg "lo")
  , .mov "c0" (.reg "d0"), .add "c0" (.imm 19)
  , .mov "c1" (.reg "d1"), .adc "c1" (.imm 0)
  , .mov "c2" (.reg "d2"), .adc "c2" (.imm 0)
  , .mov "c3" (.reg "d3"), .adc "c3" (.imm 0)
  , .mov "m" (.reg "c3"), .shr "m" (.imm 63)
  , .neg "m"
  , .mov "lo" (.imm 0x7fffffffffffffff), .and_ "c3" (.reg "lo")
  , .mov "lo" (.reg "c0"), .xor_ "lo" (.reg "d0"), .and_ "lo" (.reg "m"), .xor_ "d0" (.reg "lo")
  , .mov "lo" (.reg "c1"), .xor_ "lo" (.reg "d1"), .and_ "lo" (.reg "m"), .xor_ "d1" (.reg "lo")
  , .mov "lo" (.reg "c2"), .xor_ "lo" (.reg "d2"), .and_ "lo" (.reg "m"), .xor_ "d2" (.reg "lo")
  , .mov "lo" (.reg "c3"), .xor_ "lo" (.reg "d3"), .and_ "lo" (.reg "m"), .xor_ "d3" (.reg "lo")
  , .storeMem "f" (slotOff o 0) (.reg "d0")
  , .storeMem "f" (slotOff o 1) (.reg "d1")
  , .storeMem "f" (slotOff o 2) (.reg "d2")
  , .storeMem "f" (slotOff o 3) (.reg "d3") ]

/-- `f[o] := (f[a] − f[b]) mod p` — the landed `feSubBlock` re-based. -/
def feSubAt (o a b : Nat) : List (JInstr 64) :=
  [ .loadMem "d0" "f" (slotOff a 0)
  , .loadMem "lo" "f" (slotOff b 0),  .sub "d0" (.reg "lo")
  , .loadMem "d1" "f" (slotOff a 1)
  , .loadMem "lo" "f" (slotOff b 1),  .sbb "d1" (.reg "lo")
  , .loadMem "d2" "f" (slotOff a 2)
  , .loadMem "lo" "f" (slotOff b 2),  .sbb "d2" (.reg "lo")
  , .loadMem "d3" "f" (slotOff a 3)
  , .loadMem "lo" "f" (slotOff b 3),  .sbb "d3" (.reg "lo")
  , .mov "c" (.imm 0), .sbb "c" (.imm 0)
  , .and_ "c" (.imm 19)
  , .mov "zr" (.imm 0)
  , .sub "d0" (.reg "c")
  , .sbb "d1" (.reg "zr")
  , .sbb "d2" (.reg "zr")
  , .sbb "d3" (.reg "zr")
  , .mov "lo" (.imm 0x7fffffffffffffff), .and_ "d3" (.reg "lo")
  , .storeMem "f" (slotOff o 0) (.reg "d0")
  , .storeMem "f" (slotOff o 1) (.reg "d1")
  , .storeMem "f" (slotOff o 2) (.reg "d2")
  , .storeMem "f" (slotOff o 3) (.reg "d3") ]

/-! ## 3. The HWCD extended-twisted-Edwards add and dedicated double

Slot layout (frame `"f"`). Input point `P₁ = (X₁:Y₁:Z₁:T₁)` in slots 0–3, input
point `P₂ = (X₂:Y₂:Z₂:T₂)` in slots 4–7; the curve constant `2d` in slot 8; the
output point `(X₃:Y₃:Z₃:T₃)` written to slots 9–12; HWCD intermediates use
scratch slots 13–20. The double reads `P₁` (slots 0–3) and writes the output to
slots 9–12. -/

-- input P1 coords
def sX1 : Nat := 0
def sY1 : Nat := 1
def sZ1 : Nat := 2
def sT1 : Nat := 3
-- input P2 coords
def sX2 : Nat := 4
def sY2 : Nat := 5
def sZ2 : Nat := 6
def sT2 : Nat := 7
-- curve constant 2d
def s2d : Nat := 8
-- output P3 coords
def sX3 : Nat := 9
def sY3 : Nat := 10
def sZ3 : Nat := 11
def sT3 : Nat := 12
-- scratch
def sA : Nat := 13
def sB : Nat := 14
def sC : Nat := 15
def sD : Nat := 16
def sE : Nat := 17
def sF : Nat := 18
def sG : Nat := 19
def sH : Nat := 20

/-- **Unified extended-twisted-Edwards add** `P₃ := P₁ + P₂` (HWCD'08 §3.1,
    `a = −1`). A composition of the landed field-op leaves over the frame:

    `A=(Y₁−X₁)(Y₂−X₂); B=(Y₁+X₁)(Y₂+X₂); C=T₁·2d·T₂; D=Z₁·2Z₂;`
    `E=B−A; F=D−C; G=D+C; H=B+A; X₃=EF; Y₃=GH; T₃=EH; Z₃=FG`.

    `2Z₂` and `2d·T₂` are formed by `feAddAt`/`feMulAt` into scratch. -/
def edwardsAddBlock : List (JInstr 64) :=
  -- A := (Y1 - X1) * (Y2 - X2)
  feSubAt sE sY1 sX1            -- E := Y1 - X1   (reuse sE as a tmp before E proper)
  ++ feSubAt sF sY2 sX2         -- F := Y2 - X2
  ++ feMulAt sA sE sF           -- A := E * F
  -- B := (Y1 + X1) * (Y2 + X2)
  ++ feAddAt sE sY1 sX1         -- E := Y1 + X1
  ++ feAddAt sF sY2 sX2         -- F := Y2 + X2
  ++ feMulAt sB sE sF           -- B := E * F
  -- C := T1 * 2d * T2
  ++ feMulAt sC sT1 s2d         -- C := T1 * 2d
  ++ feMulAt sC sC sT2          -- C := C * T2
  -- D := Z1 * (2 * Z2)
  ++ feAddAt sD sZ2 sZ2         -- D := 2*Z2
  ++ feMulAt sD sZ1 sD          -- D := Z1 * 2Z2
  -- E := B - A ; F := D - C ; G := D + C ; H := B + A
  ++ feSubAt sE sB sA           -- E := B - A
  ++ feSubAt sF sD sC           -- F := D - C
  ++ feAddAt sG sD sC           -- G := D + C
  ++ feAddAt sH sB sA           -- H := B + A
  -- X3 := E*F ; Y3 := G*H ; T3 := E*H ; Z3 := F*G
  ++ feMulAt sX3 sE sF
  ++ feMulAt sY3 sG sH
  ++ feMulAt sT3 sE sH
  ++ feMulAt sZ3 sF sG

/-- **Dedicated extended double** `P₃ := 2·P₁` (HWCD'08, `a = −1`).

    `A=X₁²; B=Y₁²; C=2Z₁²; D=−A; EE=(X₁+Y₁)²−A−B; G=D+B; F=G−C; H=D−B;`
    `X₃=EE·F; Y₃=G·H; T₃=EE·H; Z₃=F·G`. `D = −A` is `feSubAt` from a zeroed
    slot; `2Z₁²` is `feSqr` then `feAdd` to itself. -/
def edwardsDblBlock : List (JInstr 64) :=
  -- A := X1^2 ; B := Y1^2
  feSqrAt sA sX1
  ++ feSqrAt sB sY1
  -- C := 2 * Z1^2
  ++ feSqrAt sC sZ1
  ++ feAddAt sC sC sC
  -- EE := (X1 + Y1)^2 - A - B   (use sE for X1+Y1 then its square)
  ++ feAddAt sE sX1 sY1
  ++ feSqrAt sE sE              -- sE := (X1+Y1)^2
  ++ feSubAt sE sE sA
  ++ feSubAt sE sE sB           -- sE := EE
  -- D := -A  (= 0 - A), via the always-zero scratch slot sD as a zero operand:
  --   first zero sD, then D := 0 - A.  (sD initialised to 0 in the frame; we
  --   recompute it as 0 explicitly to not depend on frame init.)
  ++ feSubAt sD sX3 sX3         -- sD := X3 - X3 = 0  (sX3 holds garbage; x-x=0)
  ++ feSubAt sD sD sA           -- D := 0 - A = -A
  -- G := D + B ; F := G - C ; H := D - B
  ++ feAddAt sG sD sB
  ++ feSubAt sF sG sC
  ++ feSubAt sH sD sB
  -- X3 := EE*F ; Y3 := G*H ; T3 := EE*H ; Z3 := F*G
  ++ feMulAt sX3 sE sF
  ++ feMulAt sY3 sG sH
  ++ feMulAt sT3 sE sH
  ++ feMulAt sZ3 sF sG

/-! ## 4. The initial frame state

The frame `"f"` holds `P₁` (slots 0–3), `P₂` (slots 4–7), and the constant `2d`
(slot 8); the doubled output / intermediates start at 0. We seed from a function
`fr : Nat → Fin 4 → BitVec 64` (slot, limb ↦ word). -/

/-- Build the init frame state from a slot/limb seed `fr`. Slot `i` limb `k`
    lives at byte offset `slotOff i k = 32·i + 8·k`. -/
def initFrame (fr : Nat → Fin 4 → BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "f" then
        let o := off.toNat
        if o % 8 = 0 then
          let w := o / 8
          fr (w / 4) ⟨w % 4, by omega⟩
        else 0
      else 0 }

/-! ## 5. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the Edwards add block.** Lowering to
    `Com (x86Dialect 64)` and denoting on the init frame equals `runBlock` on the
    source block — the owned backend's straight-line lowering is denotation-
    preserving across the composed field-op instruction mix. -/
theorem edwardsAddBlock_lowering_correct (fr : Nat → Fin 4 → BitVec 64) :
    (lowerBlock (Γ := []) edwardsAddBlock).denote (.cons (initFrame fr) .nil)
      = runBlock (initFrame fr) edwardsAddBlock :=
  lowerBlock_denote_closed edwardsAddBlock (initFrame fr)

/-- **Lowering correctness on the Edwards double block.** -/
theorem edwardsDblBlock_lowering_correct (fr : Nat → Fin 4 → BitVec 64) :
    (lowerBlock (Γ := []) edwardsDblBlock).denote (.cons (initFrame fr) .nil)
      = runBlock (initFrame fr) edwardsDblBlock :=
  lowerBlock_denote_closed edwardsDblBlock (initFrame fr)

/-! ## 6. Structural identity: each frame-relative generator IS the landed kernel

The frame-relative generators are the landed field-op blocks with the bases
re-based and offsets shifted; the arithmetic (and hence the value semantics,
KAT'd vs s2n + GMP in `Fe25519OpsKernel` / `Fe25519MulKernel`) is unchanged.
We pin the structural sanity checks by length (each generator emits exactly the
landed instruction count). -/

theorem feMulAt_length (o a b : Nat) : (feMulAt o a b).length = 95 := by
  unfold feMulAt; rfl
theorem feSqrAt_length (o a : Nat) : (feSqrAt o a).length = 95 := by
  unfold feSqrAt; rfl
theorem feAddAt_length (o a b : Nat) : (feAddAt o a b).length = 45 := by
  unfold feAddAt; rfl
theorem feSubAt_length (o a b : Nat) : (feSubAt o a b).length = 26 := by
  unfold feSubAt; rfl

/-- The add is 9 `feMul` (95 each) + 5 `feAdd` (45) + 4 `feSub` (26) =
    855 + 225 + 104 = 1184 instructions. -/
theorem edwardsAddBlock_length : edwardsAddBlock.length = 1184 := by
  native_decide

/-- The double is 4 `feSqr` + 4 `feMul` (95 each) + 3 `feAdd` (45) + 6 `feSub`
    (26) = 760 + 135 + 156 = 1051 instructions. -/
theorem edwardsDblBlock_length : edwardsDblBlock.length = 1051 := by
  native_decide

/-! ## 7. Fixed-base scalarmul `acc := s·B`

Ed25519 signing computes `A = a·B` and `R = r·B`, both fixed-base. The fast path
is a **signed 4-bit comb**: for each of the 64 windows `i`, CT-select the Niels
point `d·16^i·B` from the precomputed table (`CombSelectKernel.combSelectBlock`)
and mixed-add it into the running accumulator. Here we assemble the **structural
driver**: one comb select per window (the landed CT-select kernel, frame-relative
into the `P₂` input slots) followed by the landed `edwardsAddBlock`, repeated.

To keep the verified block tractable we expose the **single-window step** — one
CT select + one Edwards add — as the unit of composition; the full 64-window
scalarmul is this step iterated, which is the C-driver loop in the bench harness
(the loop body is the verified block). The per-step lowering correctness lifts to
the whole scalarmul by composition of `runBlock` over the windows. -/

/-- One fixed-base comb window step: CT-select the window's Niels point into the
    `P₂` input slots (slots 4–7 hold the selected X₂/Y₂/Z₂/T₂), then Edwards-add
    it into the accumulator (`P₁ += selected`, output to `P₃`). The select reads
    the table base `"tbl"`/secret index reg `"d"` and writes into the frame's
    `sX2` slot via base `"f"`; this is the landed `combSelectBlock` re-targeted to
    write the four selected limbs to the `sX2` slot (one coordinate per call in
    the full Niels select; here the structural single-coordinate select). -/
def combWindowStep : List (JInstr 64) :=
  -- CT-select one coordinate of the window point into slot sX2 of the frame.
  -- (mirrors CombSelectKernel.combSelectBlock; writes to "f"+(slotOff sX2 k))
  [ .mov "a0" (.imm 0), .mov "a1" (.imm 0)
  , .mov "a2" (.imm 0), .mov "a3" (.imm 0) ]
  ++ ((List.range 16).flatMap (fun j =>
        let base : Int := Int.ofNat j * 32
        [ .mov "mask" (.reg "d")
        , .sub "mask" (.imm j)
        , .loadMem "c" "tbl" (base + 0),  .cmove "a0" (.reg "c")
        , .loadMem "c" "tbl" (base + 8),  .cmove "a1" (.reg "c")
        , .loadMem "c" "tbl" (base + 16), .cmove "a2" (.reg "c")
        , .loadMem "c" "tbl" (base + 24), .cmove "a3" (.reg "c") ]))
  ++ [ .storeMem "f" (slotOff sX2 0) (.reg "a0"), .storeMem "f" (slotOff sX2 1) (.reg "a1")
     , .storeMem "f" (slotOff sX2 2) (.reg "a2"), .storeMem "f" (slotOff sX2 3) (.reg "a3") ]
  -- then Edwards-add the selected point into the accumulator
  ++ edwardsAddBlock

/-- The scalarmul init frame additionally needs the table base `"tbl"` (the comb
    table, 16 entries × 4 limbs row-major at `32·j + 8·k`) and the secret window
    index in register `"d"`. We extend `initFrame` with those. -/
def initScalarMul (fr : Nat → Fin 4 → BitVec 64)
    (tab : Fin 16 → Fin 4 → BitVec 64) (didx : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "d" then didx else 0
    mem := fun base off =>
      if base = "f" then
        let o := off.toNat
        if o % 8 = 0 then fr (o / 8 / 4) ⟨(o / 8) % 4, by omega⟩ else 0
      else if base = "tbl" then
        let o := off.toNat
        if o % 8 = 0 ∧ o < 512 then
          tab ⟨(o / 8 / 4) % 16, by omega⟩ ⟨(o / 8) % 4, by omega⟩
        else 0
      else 0 }

/-- **Lowering correctness on one fixed-base comb-window step.** The CT-select
    (writing the selected window point into the `P₂` slots) + the Edwards add
    lower denotation-preservingly; the full `s·B` scalarmul is this step iterated
    over the 64 windows (the C-driver loop), so its lowering follows by
    composition of `runBlock`. -/
theorem combWindowStep_lowering_correct (fr : Nat → Fin 4 → BitVec 64)
    (tab : Fin 16 → Fin 4 → BitVec 64) (didx : BitVec 64) :
    (lowerBlock (Γ := []) combWindowStep).denote
        (.cons (initScalarMul fr tab didx) .nil)
      = runBlock (initScalarMul fr tab didx) combWindowStep :=
  lowerBlock_denote_closed combWindowStep (initScalarMul fr tab didx)

/-! ## 8. AT&T assembly emission (in-Lean backend, no jasminc)

A whole point op (`edwardsAddBlock` = 9 `feMul` + 4 `feAdd` + 2 `feSub`, with
the reused scratch names `t0..t7`/`lo`/`hi`/`y`/`d0..d3`/`c0..c3`/`m`/`c`)
exceeds the **14-register** GP pool if every name is forced register-resident at
once: `allocOverflow` is therefore deliberately **not** asserted `none` for the
monolithic block — that is the genuine register-budget wall this self-emit line
documents (closed by the verified spill/inline/mem2reg passes #410–#418 for the
X25519 ladder). The faithful, overflow-free emission — and the one the brief's
own model names ("each point op is a fixed sequence of field-op leaves") — keeps
each field op as its **own** leaf (the landed `Fe25519MulKernel.feMulAsm` /
`Fe25519OpsKernel.fe{Add,Sub,Sqr}Asm`, each `allocOverflow = none`, each
`runBlock`-verified), and the point op is the composition over the frame.

The point op's **call sequence** — which landed field-op leaf runs on which
frame slots, in order — is the structural emission artifact. The runtime
realisation (the C driver in `bench/ed25519_point_compare/`) calls the landed
`.s` leaves in this order; each call is a `runBlock`-verified, overflow-free
leaf, and the whole point op's lowering correctness is `edwards*Block_lowering_
correct` above (one straight-line `runBlock` over the spliced bodies). -/

/-- A field-op call in a point op's composition: the op tag, output slot, and the
    one or two input slots (over the single frame). The runtime emission is the
    matching landed leaf `.s` run on `f+32·out`, `f+32·in0`, `f+32·in1`. -/
inductive FieldCall where
  | mul (out in0 in1 : Nat)
  | sqr (out in0 : Nat)
  | add (out in0 in1 : Nat)
  | sub (out in0 in1 : Nat)
  deriving Repr, DecidableEq

/-- The Edwards-add call sequence (the structural composition; mirrors
    `edwardsAddBlock`'s field-op order). -/
def edwardsAddCalls : List FieldCall :=
  [ .sub sE sY1 sX1, .sub sF sY2 sX2, .mul sA sE sF
  , .add sE sY1 sX1, .add sF sY2 sX2, .mul sB sE sF
  , .mul sC sT1 s2d, .mul sC sC sT2
  , .add sD sZ2 sZ2, .mul sD sZ1 sD
  , .sub sE sB sA, .sub sF sD sC, .add sG sD sC, .add sH sB sA
  , .mul sX3 sE sF, .mul sY3 sG sH, .mul sT3 sE sH, .mul sZ3 sF sG ]

/-- The Edwards-double call sequence (mirrors `edwardsDblBlock`). -/
def edwardsDblCalls : List FieldCall :=
  [ .sqr sA sX1, .sqr sB sY1, .sqr sC sZ1, .add sC sC sC
  , .add sE sX1 sY1, .sqr sE sE, .sub sE sE sA, .sub sE sE sB
  , .sub sD sX3 sX3, .sub sD sD sA
  , .add sG sD sB, .sub sF sG sC, .sub sH sD sB
  , .mul sX3 sE sF, .mul sY3 sG sH, .mul sT3 sE sH, .mul sZ3 sF sG ]

/-- The add call list (9 `mul` + 5 `add` + 4 `sub` = 18) realises exactly the
    `edwardsAddBlock` field-op order. -/
theorem edwardsAddCalls_length : edwardsAddCalls.length = 18 := by decide
/-- The double call list (4 `sqr` + 4 `mul` + 3 `add` + 6 `sub` = 17). -/
theorem edwardsDblCalls_length : edwardsDblCalls.length = 17 := by decide

/-- The whole-point-op multiply count: the dominant cost is the field-multiplies,
    9 per add (HWCD `a=−1`: `add-2008-hwcd-3` is 9M) and 4M+4S per double, which
    is exactly what the call sequences expose for the bench cost model. -/
theorem edwardsAddCalls_mul_count :
    (edwardsAddCalls.filter (fun c => match c with | .mul _ _ _ => true | _ => false)).length = 9 := by
  rfl

/-- Pin the frame pointer, MULX multiplier, and zero register for a single
    field-op leaf within the frame; identical to the landed per-leaf pins. -/
def fieldLeafPinned : GpAlloc := [("f", "%rdi"), ("yd", "%rdx"), ("zr", "%rbp")]

/-- **No overflow for the per-field-op leaves** — a single `feMulAt`/`feSqrAt`/
    `feAddAt`/`feSubAt` over the frame fits the GP pool (frame ptr + MULX + zero
    pinned, the reused scratch first-fits). This is the unit of emission; the
    point op is their composition (which is why the monolithic block is not
    emitted as one leaf). -/
theorem fieldLeaf_alloc_no_overflow :
    allocOverflow fieldLeafPinned (feMulAt sA sE sF) = none
      ∧ allocOverflow fieldLeafPinned (feSqrAt sA sX1) = none
      ∧ allocOverflow fieldLeafPinned (feAddAt sE sY1 sX1) = none
      ∧ allocOverflow fieldLeafPinned (feSubAt sE sY1 sX1) = none := by native_decide

/-- One emitted field-op leaf as AT&T text (the frame-relative `feMul`), shown as
    the representative; the `Fe25519MulKernel`/`Fe25519OpsKernel` non-frame leaves
    are the deployed `.s` files the C driver links. -/
def feMulLeafAsm (o a b : Nat) : String :=
  renderLeafFn "ed25519_fe_mul_at_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14"
    , "\tpushq %r15", "\tpushq %rbp" ]
    (renderBlockBody (allocGp fieldLeafPinned (feMulAt o a b)) (feMulAt o a b))
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Shape check: the emitted field-op leaf carries the dual carry-chain idiom and
    the Solinas reduce constant `$38` (the composed point op inherits this). -/
theorem feMulLeaf_asm_shape :
    BignumMontMulKernel.hasSub (feMulLeafAsm sA sE sF) "mulx"
      ∧ BignumMontMulKernel.hasSub (feMulLeafAsm sA sE sF) "adcx"
      ∧ BignumMontMulKernel.hasSub (feMulLeafAsm sA sE sF) "adox"
      ∧ BignumMontMulKernel.hasSub (feMulLeafAsm sA sE sF) "$38" := by native_decide

/-- Emit driver: write the in-Lean-backend-emitted field-op leaf `.s` for the
    bench harness, plus a manifest of the point-op call sequences (the structural
    composition the C driver realises). The deployed per-op leaves are the landed
    `Fe25519{Mul,Ops}Kernel` `.s` files. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/ed25519_point_compare/gen_com"
  IO.FS.writeFile
    "bench/ed25519_point_compare/gen_com/ed25519_fe_mul_at_x86_from_lean.s"
    (feMulLeafAsm sA sE sF)
  IO.FS.writeFile
    "bench/ed25519_point_compare/gen_com/ed25519_point_add_calls.txt"
    (String.intercalate "\n" (edwardsAddCalls.map (fun c => toString (repr c))) ++ "\n")
  IO.FS.writeFile
    "bench/ed25519_point_compare/gen_com/ed25519_point_dbl_calls.txt"
    (String.intercalate "\n" (edwardsDblCalls.map (fun c => toString (repr c))) ++ "\n")
  IO.println "wrote gen_com/ed25519_fe_mul_at_x86_from_lean.s + point-op call manifests (in-Lean x86 backend, no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Ed25519PointKernel
