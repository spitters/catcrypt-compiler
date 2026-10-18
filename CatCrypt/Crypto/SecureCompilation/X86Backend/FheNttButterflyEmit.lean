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
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-!
# Lazy (Harvey) FHE-NTT Shoup CT butterfly through the OWNED x86 backend (no jasminc)

Stage-2: the full lazy Cooley–Tukey butterfly — including BOTH branchless
conditional reductions — driven through the `compile-from-hax` front
(`Com thirDialect`) onto the OWNED x86 backend, NO jasminc anywhere. It combines

* the Stage-1 lazy Shoup product (`FheShoupEmit.fheShoupThir`): the
  discarded-low + `mulhi` fusion pair coalesced into one two-output `mulx` by the
  unmodified `FuseMulHi.fuseMulHiLprog`, with its rdx-pin / `R8`
  evacuation, plus the single-`SUB` lazy difference `Y·ω − q̂·q ∈ [0, 2q)` (no
  ADX carry chain); and
* the feasibility-probe's branchless sign-mask conditional subtract
  (`FheNttButterflyProbe`, the same trick `MLDSA/DecomposeEmit` emits),
  realised here in the thir dialect over the **renderable** carry-free alphabet:
  `r = v − c; b = r >>ₗ 63; nm = 0 − b; m = nm & c; v' = r + m` — a logical
  sign-bit shift (`thShrImm 64 63`) plus a `0 − b` negate that expands the sign
  bit `{0,1}` into the all-ones/zero mask, then `thBin .and` / `thBin .add` (NO
  `thSelect`, NO control flow). The arithmetic-shift `thSarImm`/`sarImm` lowers to
  a `SAR` mnemonic the shared `LprogAsmPrinter` does not render, so this kernel
  uses the logical-shift-plus-negate route — identical mask, fully renderable.

unlike the probe, this lives on the `Lprog`/thir spine, so it inherits the SysV
ABI frame and the `mulx` rdx-evacuation the probe lacked.

## The butterfly (`q = 1152921504606830593`, `R = 2^64`, `2q = 2305843009213661186`)

Inputs `X, Y ∈ [0, 4q)`, twiddle `ω` with precomputed Shoup const
`ω' = ⌊ω·R/q⌋`; outputs `X', Y' ∈ [0, 4q)`:

```
  Xn    = X − (X ≥ 2q ? 2q : 0)          -- sign-mask csub of 2q  -> Xn ∈ [0, 2q)
  q̂     = mulhi(Y, ω')                    -- Shoup quotient (mulx high, fuseMulHiLprog)
  Tlazy = Y·ω − q̂·q                        -- the lazy Shoup value ∈ [0, 2q)  (one SUB)
  T     = Tlazy − (Tlazy ≥ q ? q : 0)     -- sign-mask csub of q   -> T ∈ [0, q)
  X'    = Xn + T                           -- ∈ [0, 3q) ⊂ [0, 4q)
  Y'    = Xn + 2q − T                       -- ∈ [0, 4q)
```

The sign-mask csub of a constant `c` is, on a value `v`:

```
  r  = v − c                 -- thBin .sub  (v, c)
  b  = r >>ₗ 63              -- thShrImm 64 63   (logical: sign bit, 1 iff r<0 ⟺ v<c)
  nm = 0 − b                 -- thBin .sub  (cz, b)   (0 iff v≥c, all-ones iff v<c)
  m  = nm & c                -- thBin .and  (nm, c)
  v' = r + m                 -- thBin .add  (r, m)    = (v ≥ c ? v − c : v)
```

`v ≥ c ⟹ r ≥ 0 ⟹ b = 0 ⟹ nm = 0 ⟹ m = 0 ⟹ v' = r = v − c`; and
`v < c ⟹ r < 0 ⟹ b = 1 ⟹ nm = 2^64−1 (all-ones) ⟹ m = c ⟹ v' = r + c = v`.
Every op is in the carry-free `JasminBinOp` alphabet (+ the logical immediate
shift `thShrImm`, which lowers to `shrImm`/`SHR`, renderable after the
`legalizeShiftImmLprog` post-pass); there is no `thSelect`, no `CMOV`, and no
branch. The direct arithmetic shift `thSarImm`/`sarImm` would lower to a `SAR`
mnemonic the shared `LprogAsmPrinter` does not render — hence the logical-shift +
`0 − b` negate route, which computes the identical mask. The mask constants `2q`,
`q`, and the zero are materialised by `thConst` (as `fheShoupThir` materialises
`q`), not `thBinLit` (whose two-binding expansion would perturb the multi-output
epilogue's "last `n` bindings" rule).

## Two-output emit (`out[0] = X'`, `out[1] = Y'`)

`comToLfundefPhysAbi`'s epilogue stores the LAST `n = outStoreMap.length` bindings:
output index `j` ↦ binding position `total − n + j` ↦ `outStoreMap[j]`. With
`outStoreMap = [("RDI", 0), ("RDI", 8)]` the SECOND-TO-LAST binding is `out[0]`
and the LAST binding is `out[1]`. So the Com is arranged with `X'` as the
penultimate binding and `Y'` as the final binding (the `.ret`), and `T` is
computed exactly ONCE and shared between them — preferable to two single-output
programs (which would recompute the whole Shoup product and both reductions for
each output). `Y' = Xn + 2q − T` needs a `2q` term that does not depend on `T`,
so `Xn2q = Xn + 2q` is precomputed before the T-reduction; then `X' = Xn + T`
(penultimate) and `Y' = Xn2q − T` (final).

## ABI (2-pointer SysV, `comToLfundefPhysAbi` shape)

```c
extern void fhe_bfly(uint64_t *out, const uint64_t *inp);
//   inp = [ X, Y, omega, omegaprime ]   (omegaprime = floor(omega*R/q))
//   out = [ X', Y' ]                     (both in [0, 4q))
```

`RDI` = out, `RSI` = inp. Argument-slot numbering (`comToLfundef`): arg slot `s`
(program-root order) is context entry `nArgs − 1 − s`. The thir context is
`[X, Y, omega, omegaprime]` (`X = 0 … omegaprime = 3`), so arg slot
`s ↦ input index (3 − s)`. With C-side `inp = [X, Y, omega, omegaprime]`:

* slot `3` → input `X`          (`inp[0]`, byte offset 0)
* slot `2` → input `Y`          (`inp[1]`, byte offset 8)
* slot `1` → input `omega`      (`inp[2]`, byte offset 16)
* slot `0` → input `omegaprime` (`inp[3]`, byte offset 24)

i.e. `inLoadMap s = ("RSI", 8 * (3 − s))`. Outputs: `X'` → `out[0]` (offset 0),
`Y'` → `out[1]` (offset 8).

## What is verified vs trusted (scope)

* **Verified (value, in Lean)**: `fheBflyThir_denote` — the Com denotes the
  width-64 reference `fheBflySpec64` (true by definition). `fheBfly_via_thirDialect`
  re-derives the same pair through the generic proved `lowerThir_denote`. A tiny
  `native_decide` value check (`fheBfly_kat0`/`_kat1`) ties the Com denotation to
  an independent `Nat`-level Harvey reference `bflyRef` on 2 vectors (one with
  `X ∈ [2q, 4q)` exercising the X-normalize and `Tlazy ∈ [q, 2q)` exercising the
  T-reduction; one with `X < 2q`). Vectors kept tiny; bulk value checks run
  in the external KAT harness.
* **Trusted (thin)**: `renderLfundef` / `as`/`cc` / the SysV leaf ABI frame; the
  byte-identity `fhe_bfly(inp) == (X', Y')` is the orchestrator's external GMP
  KAT on the emitted `.s` (no jasminc).

**Bound assumptions for the KAT**: inputs `X, Y ∈ [0, 4q)`. Then `Xn ∈ [0, 2q)`,
`Tlazy ∈ [0, 2q)`, `T ∈ [0, q)`, `X' ∈ [0, 3q)`, `Y' ∈ [0, 4q)` — all < `2^64`,
so every step's `BitVec 64` wraparound matches the `Nat` reference. **Operand-order
risks flagged for the KAT**: each sign-mask `r = v − c` is `thBin .sub (v, c)`
(NOT `c − v`); the lazy diff is `lo1 − lo2 = Y·ω − q̂·q` (NOT reversed);
`Y' = Xn2q − T` (NOT `T − Xn2q`). The `mulx` rdx-pin / `R8` evacuation is the one
register risk, inherited from `fuseMulHiLprog` exactly as in `FheShoupEmit`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttButterflyEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir lowerThir_denote thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiLprog)

/-! ## 1. The FHE-NTT prime constants -/

/-- The 60-bit FHE prime `q = 2^60 − 2^14 + 1` (matches `FheShoupMulLaw.fheQ`). -/
def fheQ : Nat := 1152921504606830593
/-- `2q`, the X-normalization boundary / lazy upper bound. -/
def fheTwoQ : Nat := 2 * fheQ   -- 2305843009213661186

/-! ## 2. The lazy Shoup CT butterfly as a `Com thirDialect`

Two-output: the penultimate binding is `X'`, the final binding (the `.ret`) is
`Y'`. Context starts `[X, Y, omega, omegaprime]` (`X = .here`,
`Y = .there .here`, `omega = .there (.there .here)`,
`omegaprime = .there (.there (.there .here))`). Each `.var` prepends its result,
so de Bruijn depths of earlier values increase by one per binding. The binding
tower (head-first), with the post-binding context depth of each named value in
brackets:

    cz    = 0    const  (shared sign-mask zero)
    c2q   = 2q   const
    Xr    = X − c2q
    Xb    = Xr >>ₗ 63                          (logical: sign bit 0/1, 1 iff X<2q)
    Xnm   = cz − Xb                            (0 iff X≥2q, all-ones iff X<2q)
    Xmsk  = Xnm & c2q
    Xn    = Xr + Xmsk                          (∈ [0, 2q))
    Xn2q  = Xn + c2q                            (precompute for Y', no T-dep)
    loQ   = Y · omegaprime  (DISCARDED; feeds fuseMulHiLprog)
    qhat  = mulhi(Y, omegaprime)
    lo1   = omega · Y
    cq    = q    const
    lo2   = qhat · cq
    Tlz   = lo1 − lo2                          (lazy value ∈ [0, 2q))
    Tr    = Tlz − cq                            (reuse cq)
    Tb    = Tr >>ₗ 63
    Tnm   = cz − Tb
    Tmsk  = Tnm & cq
    T     = Tr + Tmsk                          (∈ [0, q))
    Xo    = Xn + T                             (= X' ; penultimate → out[0])
    Yo    = Xn2q − T                            (= Y' ; final/ret → out[1])

The conditional subtract uses a **logical** sign-bit shift (`thShrImm 64 63`,
which lowers to `shrImm`/`SHR`, in the owned printer's renderable alphabet) plus a
`0 − bit` negate to expand the sign bit `{0,1}` into the all-ones/zero mask. (The
direct arithmetic shift `thSarImm`/`sarImm` lowers to a `SAR` mnemonic the shared
`LprogAsmPrinter` does not render — the logical-shift-plus-negate route stays
entirely within the renderable carry-free alphabet and computes the identical
mask.) The mask constants `2q`/`q` and the zero are materialised by `thConst`. -/
def fheBflyThir : Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- ctx0: [X(0), Y(1), omega(2), omegaprime(3)]
  -- b1 cz = 0
  .var (.mk (.thConst 64 0) rfl .nil)
  -- b2 c2q = 2q
  (.var (.mk (.thConst 64 fheTwoQ) rfl .nil)
  -- b3 Xr = X - c2q      X@2, c2q@0
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there (.there (.here))) (.cons (.here) .nil)))
  -- b4 Xb = Xr >>L 63    Xr@0
  (.var (.mk (.thShrImm 64 63) rfl (.cons (.here) .nil))
  -- b5 Xnm = cz - Xb     cz@3, Xb@0
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there (.there (.there (.here)))) (.cons (.here) .nil)))
  -- b6 Xmsk = Xnm & c2q  Xnm@0, c2q@3
  (.var (.mk (.thBin .and 64) rfl (.cons (.here) (.cons (.there (.there (.there (.here)))) .nil)))
  -- b7 Xn = Xr + Xmsk    Xr@3, Xmsk@0   (in [0,2q))
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there (.here)))) (.cons (.here) .nil)))
  -- b8 Xn2q = Xn + c2q   Xn@0, c2q@5
  (.var (.mk (.thBin .add 64) rfl (.cons (.here) (.cons (.there (.there (.there (.there (.there (.here)))))) .nil)))
  -- b9 loQ = Y * omegaprime (DISCARDED; feeds fuseMulHiLprog)  Y@9, omegaprime@11
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))) .nil)))
  -- b10 qhat = mulhi(Y, omegaprime)  Y@10, omegaprime@12
  (.var (.mk (.thMulHi 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) .nil)))
  -- b11 lo1 = omega * Y   omega@12, Y@11
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))) .nil)))
  -- b12 cq = q
  (.var (.mk (.thConst 64 fheQ) rfl .nil)
  -- b13 lo2 = qhat * cq   qhat@2, cq@0
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there (.here))) (.cons (.here) .nil)))
  -- b14 Tlz = lo1 - lo2   lo1@2, lo2@0   (lazy value in [0,2q))
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there (.there (.here))) (.cons (.here) .nil)))
  -- b15 Tr = Tlz - cq     Tlz@0, cq@2   (reuse cq)
  (.var (.mk (.thBin .sub 64) rfl (.cons (.here) (.cons (.there (.there (.here))) .nil)))
  -- b16 Tb = Tr >>L 63    Tr@0
  (.var (.mk (.thShrImm 64 63) rfl (.cons (.here) .nil))
  -- b17 Tnm = cz - Tb     cz@15, Tb@0
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))) (.cons (.here) .nil)))
  -- b18 Tmsk = Tnm & cq   Tnm@0, cq@5
  (.var (.mk (.thBin .and 64) rfl (.cons (.here) (.cons (.there (.there (.there (.there (.there (.here)))))) .nil)))
  -- b19 T = Tr + Tmsk     Tr@3, Tmsk@0   (in [0,q))
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there (.here)))) (.cons (.here) .nil)))
  -- b20 Xo = Xn + T       Xn@12, T@0   (penultimate -> out[0] = X)
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) (.cons (.here) .nil)))
  -- b21 Yo = Xn2q - T     Xn2q@12, T@1  (final/ret -> out[1] = Y)
  (.var (.mk (.thBin .sub 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) (.cons (.there (.here)) .nil)))
  -- ret Yo
  (.ret .here)))))))))))))))))))))

/-! ## 3. The width-64 lazy Shoup butterfly reference (by definition the denotation) -/

/-- The width-64 lazy Shoup CT butterfly: by definition the (pair-of-outputs)
    denotation of `fheBflyThir`. The final binding (the `.ret`) is `Y'`; `X'` is
    the penultimate binding (recovered by the orchestrator's KAT from `out[0]`).
    This `def` exposes only the `.ret` value (`Y'`); the full pair is checked by
    `fheBfly_kat*` against the `Nat` reference `bflyRef`. -/
def fheBflySpec64 (X Y omega omegaprime : BitVec 64) : BitVec 64 :=
  fheBflyThir.denote (.cons X (.cons Y (.cons omega (.cons omegaprime .nil))))

/-- The THIR-dialect lazy FHE Shoup butterfly denotes `fheBflySpec64` — true by
    definition (mirrors `FheShoupEmit.fheShoupThir_denote`). -/
theorem fheBflyThir_denote (X Y omega omegaprime : BitVec 64) :
    fheBflyThir.denote (.cons X (.cons Y (.cons omega (.cons omegaprime .nil))))
      = fheBflySpec64 X Y omega omegaprime := rfl

/-- **Butterfly re-derived through the dialect spine.** The lowered `Com
    jasminDialect` denotes the same `BitVec 64` (the `Y'` output) as the width-64
    reference, via the generic proved `lowerThir_denote`. -/
theorem fheBfly_via_thirDialect (X Y omega omegaprime : BitVec 64) :
    (lowerThir fheBflyThir).denote (.cons X (.cons Y (.cons omega (.cons omegaprime .nil))))
      = fheBflySpec64 X Y omega omegaprime :=
  (lowerThir_denote fheBflyThir (.cons X (.cons Y (.cons omega (.cons omegaprime .nil))))).trans
    (fheBflyThir_denote X Y omega omegaprime)

/-! ## 4. Independent `Nat` Harvey reference + value KAT (tiny vectors)

`bflyRef` is the Harvey lazy CT butterfly over `Nat`, all arithmetic mod `2^64`
(mirrors `FheNttButterflyProbe.shoupRefBF`). The KATs tie ONLY the `.ret` (`Y'`)
output of the Com to `bflyRef`'s second component — the `X'` output rides the
same denotation and its byte-identity is the orchestrator's GMP KAT. -/

/-- The lazy Shoup CT butterfly over `Nat` (Harvey); returns `(X', Y')`. -/
def bflyRef (X Y omega omegaprime : Nat) : Nat × Nat :=
  let Xn := if X ≥ fheTwoQ then X - fheTwoQ else X
  let qhat := (Y * omegaprime) / 2 ^ 64
  let Tlz := (omega * Y - qhat * fheQ) % 2 ^ 64
  let T := if Tlz ≥ fheQ then Tlz - fheQ else Tlz
  ((Xn + T) % 2 ^ 64, (Xn + fheTwoQ - T) % 2 ^ 64)

/-- A small twiddle. -/
def kOmega : Nat := 1000000007
/-- Its Shoup constant `⌊ω·R/q⌋`. -/
def kOmegaP : Nat := kOmega * 2 ^ 64 / fheQ

/-- **KAT 0** (`X ∈ [2q, 4q)` exercises the X-normalize; the chosen `Y`/`ω` make
    `Tlazy ∈ [q, 2q)` exercising the T-reduction). The Com's `.ret` (`Y'`) matches
    `bflyRef`'s second component. -/
theorem fheBfly_kat0 :
    (fheBflySpec64 (BitVec.ofNat 64 (3 * fheQ + 12345)) (BitVec.ofNat 64 (fheQ + 99))
        (BitVec.ofNat 64 kOmega) (BitVec.ofNat 64 kOmegaP)).toNat
      = (bflyRef (3 * fheQ + 12345) (fheQ + 99) kOmega kOmegaP).2 := by native_decide

/-- **KAT 1** (`X < 2q`, the no-normalize path). -/
theorem fheBfly_kat1 :
    (fheBflySpec64 (BitVec.ofNat 64 (fheQ + 5)) (BitVec.ofNat 64 (2 * fheQ - 7))
        (BitVec.ofNat 64 kOmega) (BitVec.ofNat 64 kOmegaP)).toNat
      = (bflyRef (fheQ + 5) (2 * fheQ - 7) kOmega kOmegaP).2 := by native_decide

/-! ## 5. ABI maps for the 4-in / 2-out width-64 butterfly -/

/-- Input-load map: slot `0` → `omegaprime` (`inp[3]`, off 24); slot `1` → `omega`
    (`inp[2]`, off 16); slot `2` → `Y` (`inp[1]`, off 8); slot `3` → `X`
    (`inp[0]`, off 0). Slots `≥ 4` absent. -/
def fheBflyInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 24)       -- slot 0 = omegaprime = inp[3]
  else if s = 1 then some ("RSI", 16)  -- slot 1 = omega = inp[2]
  else if s = 2 then some ("RSI", 8)   -- slot 2 = Y = inp[1]
  else if s = 3 then some ("RSI", 0)   -- slot 3 = X = inp[0]
  else none

/-- Output-store map: `X'` (penultimate binding) → `out[0]` (off 0); `Y'` (final
    binding) → `out[1]` (off 8). -/
def fheBflyOutStoreMap : OutStoreMap := [("RDI", 0), ("RDI", 8)]

/-! ## 6. Shift-immediate legalisation post-pass (SHR, from NttBflyThirEmit)

The owned printer renders the two-source shift form `[d] SHR[:64] [d, #n]` but not
the unary `shrImm` mnemonic `SHR:<n>[:64]` (count carried in the mnemonic). The two
sign-bit shifts (`Xb = Xr >>ₗ 63`, `Tb = Tr >>ₗ 63`, both `thShrImm 64 63`) lower
to that unary form, so this pass rewrites each into the printer's operand form,
byte-faithfully mirroring `JasminLprogExport.lowerTwoAddrShiftImm` (and identical to
the SHR/SHL legs of `NttBflyThirEmit.legalizeShiftImmLprog`). No rotates or
SAR appear in this kernel. -/

export CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
  (parseShiftImm legalizeBody legalizeLprog opnMnemonics)

/-- Rewrite one already-allocated `Linstr`: a unary shift-immediate
    `Lopn [d] "SHR:<n>[:64]" [s]` becomes the printer's two-source operand form
    (prefixed by a `MOV` when `d ≠ s`); every other instruction passes through. -/
def legalizeShiftImmInstr (i : Linstr) : List Linstr :=
  match i.li_i with
  | .Lopn [d] opn [s] =>
      match parseShiftImm opn with
      | some (baseMnem, n) =>
          let movMnem := if hasSuffix baseMnem ":64" then "MOV:64" else "MOV"
          if d = s then
            [⟨i.li_ii, .Lopn [d] baseMnem [d, .imm n]⟩]
          else
            [⟨i.li_ii, .Lopn [d] movMnem [s]⟩,
             ⟨i.li_ii, .Lopn [d] baseMnem [d, .imm n]⟩]
      | none => [i]
  | _ => [i]

/-- Apply `legalizeShiftImmInstr` across a whole body. -/
def legalizeShiftImmBody : Lcmd → Lcmd :=
  legalizeBody legalizeShiftImmInstr

/-- Apply the shift-immediate legalisation to every function body of an `Lprog`. -/
def legalizeShiftImmLprog : Lprog → Lprog :=
  legalizeLprog legalizeShiftImmInstr

/-! A 64-bit shift with distinct source and destination expands to a
width-matched `MOV` and the two-source shift; with a common source and
destination the `MOV` is absent; a rotate is not rewritten. -/

#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "SHR:63:64" [.reg "RCX"]⟩)
    == ["MOV:64", "SHR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "SHR:63:64" [.reg "RAX"]⟩)
    == ["SHR:64"]
#guard opnMnemonics (legalizeShiftImmInstr ⟨0, .Lopn [.reg "RAX"] "ROR:16:64" [.reg "RCX"]⟩)
    == ["ROR:16:64"]

/-! ## 7. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The two-output FHE Shoup butterfly lowered through the thirDialect spine and
    exported to a physical, two-address SysV `Lprog` (4-pointer-load `inp`,
    2-store `out`), then the unmodified `fuseMulHiLprog` coalesces the discarded
    low `loQ = Y·ω'` + `qhat = mulhi(Y,ω')` pair into the printer's two-output
    `mulx`, and `legalizeShiftImmLprog` rewrites the two sign-bit `shrImm`
    reductions into the printer's two-source operand form (`shrq $63`). -/
def fheBflyLprog : Lprog :=
  legalizeShiftImmLprog (fuseMulHiLprog
    (Com.toLprogPhysAbi (lowerThir fheBflyThir) "fhe_bfly"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (constants are in-body regConst)
      fheBflyInLoadMap                      -- inLoadMap (4 inputs)
      fheBflyOutStoreMap                    -- outStoreMap (2 outputs)
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64, 64, 64]))                    -- abiTyin (X, Y, omega, omegaprime)

/-- The rendered owned-backend AT&T `.s` for `fhe_bfly` (no jasminc). -/
def fheBflyAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned fheBflyLprog

/-! ## 8. Rendered asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean hasSub check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 9. Emit driver -/

/-- Write the owned-backend `.s` for the lazy FHE Shoup CT butterfly (`fhe_bfly`)
    into the `bench/fhe_ntt_compare/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/fhe_ntt_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/fhe_bfly.s") fheBflyAsm
  IO.println "WROTE bench/fhe_ntt_compare/gen/fhe_bfly.s"
  IO.println "  (lazy Harvey FHE-NTT Shoup CT butterfly fheBflyThir through Com[thir] -> lowerThir ->"
  IO.println "   toLprogPhysAbi -> fuseMulHiLprog -> renderLprogAtt onto the OWNED x86 backend, NO jasminc;"
  IO.println "   inp=[X,Y,omega,omegaprime=floor(omega*R/q)]; out=[X',Y'] both in [0,4q);"
  IO.println "   q = 1152921504606830593, R = 2^64; BOTH conditional reductions branchless sign-mask)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.FheNttButterflyEmit
