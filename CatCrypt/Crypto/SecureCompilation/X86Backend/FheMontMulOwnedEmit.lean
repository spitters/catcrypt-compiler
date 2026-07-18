/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.FheMontMulLaw
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Single-word 60-bit FHE Montgomery modmul through the OWNED x86 backend (no jasminc)

A single-word **Montgomery REDC** modular multiply at the 60-bit FHE-NTT prime
`q = 1152921504606830593 = 2^60 − 2^14 + 1`, radix `R = 2^64`,
`qinv = 1080859512253956095 = −q⁻¹ mod 2^64`, driven through the
`compile-from-hax` front (`Com thirDialect`) onto the OWNED x86 backend — NO
jasminc anywhere. The companion of the 32-bit BabyBear REDC `montMulThir`
(`ThirToComFront` §13).

## Why this differs from the 32-bit `montMulThir`

`montMulThir` works at the BabyBear prime `p = 0x78000001 < 2^31`, so the product
of two Montgomery representatives `a, b < 2^32` fits in **64 bits**: a single
`thBin .mul 64` computes the full product `t = a·b`, and the REDC's `t + m·p`
stays in 64-bit range. At the 60-bit FHE prime, `a, b < q < 2^60`, so the product
`a·b` is a full **128-bit** quantity that does NOT fit in one 64-bit word. The
REDC therefore needs the high word of the `64×64→128` product via `thMulHi`
(`mulhi`, the `MULX` high half), and the Montgomery quotient is assembled with a
carry-chain add (`thAddCarryHi`/`thAddCarryLo`, the `ADCX` carry-out + data word).

The REDC computed (radix-`R` Montgomery, `T = a·b`):

```
  lo  = a * b            -- low 64 of the 128-bit product
  hi  = mulhi(a, b)      -- high 64 of the 128-bit product   (T = hi·R + lo)
  m   = lo * qinv        -- low word of the REDC multiplier   (m ≡ (T mod R)·qinv mod R)
  mqLo = m * q           -- low 64 of m·q
  mqHi = mulhi(m, q)     -- high 64 of m·q                    (m·q = mqHi·R + mqLo)
  cout = carryOut(lo + mqLo)                                  -- the low-word carry
  u   = hi + mqHi + cout -- the Montgomery quotient (T + m·q)/R, since lo + mqLo ≡ 0 mod R
```

`u ∈ [0, 2q)` is the **lazy** Montgomery representative (congruent mod `q` to
`a·b·R⁻¹`), exactly `FheMontMulLaw.montU (a·b)`. A single conditional subtract
`if u ≥ q then u − q` canonicalises it into `[0, q)` (= `FheMontMulLaw.montMul`).

This module emits the **lazy** REDC (no conditional subtract — the thirDialect
front is straight-line and the GP-linear printer renders neither `thSelect`/`CMOV`
nor a `>> 32` reduction here); canonicalisation `if u ≥ q then u − q` is a
host-side step. This mirrors the §13 BabyBear lazy-leaf discipline.

## What is verified vs trusted (honest scope)

* **Verified (value, in Lean)**: `fheMontMulThir_denote` — `fheMontMulThir.denote`
  on `[a, b]` is the width-64 lazy REDC reference `fheMontMulSpec64` (true by
  *definition*: `fheMontMulSpec64` is that denotation) — and
  `fheMontMul_via_thirDialect`, the lowered `Com jasminDialect` denotes the same
  word, via the generic, proved `lowerThir_denote`. The closed-form REDC
  (`u = addCarryWord (mulHiW a b) (mulHiW (a·b·qinv) q) (carryOutBit (a·b)
  (a·b·qinv·q) 0)`) is documented (§3); its `Nat`-level connection to
  `FheMontMulLaw.montU` is **not** carried in-Lean — a single `rfl` over the
  10-binding tower reduces the `2^64`-heavy `mulHiW`/`carryOutBit` bodies and
  trips the kernel recursion guard, so the value check is the orchestrator's GMP
  KAT on the emitted `.s` (the lazy-leaf discipline; see the §13 note in MEMORY
  about avoiding heavy in-kernel KATs).
* **Verified (printer shape)**: `fheMontMulOwnedAsm_shape` pins the `fhe_montmul`
  leaf label, the absence of an unhandled-op sentinel, the presence of real
  `mulx` instructions, and the absence of a dropped `MULXHI` binding, all by
  `native_decide`.
* **High-word gap CLOSED by the §4b MULX-fusion post-pass**: `fuseMulHiLprog`
  coalesces each paired low `MUL` + `MULXHI` into the printer's two-output `mulx`
  (multiplicand pinned into `%rdx`, the first product's `%rdx`-homed high word
  evacuated to scratch `R8`), so the emitted `.s` now materialises the
  `64×64→128` high words `hi`/`mqHi`.
* **Remaining seam (flagged for the KAT)**: the ADX carry-chain tail
  (`ADCXHI` cout + `ADCX` `u = hi + mqHi + cout`) is rendered by the shared
  `LprogAsmPrinter` ADX arm, which drops the carry-out binding and assumes the
  high word was coalesced onto the `ADCX` destination; that MOV is absent for
  this allocation, so the carry propagation is not yet faithful. Closing it is a
  shared-printer / two-address-lowering concern (out of scope for this contained
  emit-module pass). See the note on `fheMontMulOwnedAsm_shape`.
* **Trusted (thin)**: `renderLfundef` / `as`/`cc` / the SysV leaf ABI frame.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir lowerThir_denote thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog Lfundef Lcmd Linstr LinstrR LOperand stripWidthTag)

/-! ## 1. The FHE-NTT prime constants (as `BitVec 64`) -/

/-- The 60-bit FHE prime `q = 2^60 − 2^14 + 1` (matches `FheMontMulLaw.fheQ`). -/
def fheQ : Nat := 1152921504606830593

/-- `−q⁻¹ mod 2^64` (matches `FheMontMulLaw.fheQinv`). -/
def fheQinv : Nat := 1080859512253956095

/-! ## 2. The lazy REDC as a `Com thirDialect`

Single-output: the last binding (`u`) IS the result. Context starts `[a, b]`
(`a = .here`, `b = .there .here`). Bindings, head-first:

    lo, hi, cqinv, m, cq, mqLo, mqHi, czero, cout, u

where `cqinv = qinv`, `cq = q`, `czero : reg 1 = 0` are materialised constants.
`cout : reg 1` is the carry-out of `lo + mqLo` (an `ADCXHI` binding, the carry
of the low-word sum), and `u = hi + mqHi + cout` (an `ADCX` data word). -/
def fheMontMulThir : Com thirDialect [.reg 64, .reg 64] (.reg 64) :=
  -- lo = a * b                                  ctx: [a, b]
  .var (.mk (.thBin .mul 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- hi = mulhi(a, b)                            ctx: [lo, a, b]; a = dB1, b = dB2
  (.var (.mk (.thMulHi 64) rfl (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
  -- cqinv = qinv                                ctx: [hi, lo, a, b]
  (.var (.mk (.thConst 64 fheQinv) rfl .nil)
  -- m = lo * cqinv                              ctx: [cqinv, hi, lo, a, b]; lo = dB2
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
  -- cq = q                                      ctx: [m, cqinv, hi, lo, a, b]
  (.var (.mk (.thConst 64 fheQ) rfl .nil)
  -- mqLo = m * cq                               ctx: [cq, m, cqinv, hi, lo, a, b]; m = dB1
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- mqHi = mulhi(m, cq)                         ctx: [mqLo, cq, m, cqinv, hi, lo, a, b]; m = dB2, cq = dB1
  (.var (.mk (.thMulHi 64) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- czero : reg 1 = 0                           ctx: [mqHi, mqLo, cq, m, cqinv, hi, lo, a, b]
  (.var (.mk (.thConst 1 0) rfl .nil)
  -- cout : reg 1 = carryOut(lo + mqLo + czero)  ctx: [czero, mqHi, mqLo, cq, m, cqinv, hi, lo, a, b]
  --   lo = dB7, mqLo = dB2, czero = dB0
  (.var (.mk (.thAddCarryHi 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
        (.cons (.there (.there .here)) (.cons .here .nil))))
  -- u = hi + mqHi + cout                        ctx: [cout, czero, mqHi, mqLo, cq, m, cqinv, hi, lo, a, b]
  --   hi = dB7, mqHi = dB2, cout = dB0
  (.var (.mk (.thAddCarryLo 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
        (.cons (.there (.there .here)) (.cons .here .nil))))
  (.ret .here))))))))))

/-! ## 3. The width-64 lazy REDC reference

`fheMontMulSpec64 a b` is *defined* as the width-64 denotation of `fheMontMulThir`
on `[a, b]`, so the denotation lemma `fheMontMulThir_denote` is a syntactic
identity. The closed-form REDC the program computes is, head-first
(`lo = a·b`, `hi = mulhi(a,b)` ⟹ `T = a·b = hi·R + lo`):

```
  m    = lo * qinv                 -- low word of the REDC multiplier
  mqLo = m * q,   mqHi = mulhi(m,q) -- m·q = mqHi·R + mqLo
  cout = carryOut(lo + mqLo)        -- low-word carry (lo + mqLo ≡ 0 mod R)
  u    = hi + mqHi + cout           -- the Montgomery quotient (T + m·q)/R, in [0, 2q)
```

i.e. `u = addCarryWord (mulHiW a b) (mulHiW (a·b·qinv) q) (carryOutBit (a·b)
(a·b·qinv·q) 0)` — the lazy Montgomery representative, congruent mod `q` to
`a·b·R⁻¹` (= `FheMontMulLaw.montU (a·b)`). The connection to `FheMontMulLaw.montU`
over `Nat` (the `64×64→128` ↔ `Nat` bridge) is the orchestrator's GMP value KAT
on the emitted `.s`: the closed-form REDC equality is `true by reduction` of the
`Com` denotation, but a single in-kernel `rfl` over the 10-binding tower would
reduce the `2^64`-heavy `mulHiW`/`carryOutBit` bodies and trip the kernel
recursion guard, so the value check is externalised (KAT) rather than carried in
Lean — exactly the lazy-leaf discipline of the §13 BabyBear REDC. -/

/-- The width-64 lazy Montgomery REDC: by definition the denotation of the
    emitted-through-the-spine program `fheMontMulThir` on the two input words
    (the closed-form REDC is in the section docstring above; its value is checked
    by the orchestrator's GMP KAT on the emitted `.s`). -/
def fheMontMulSpec64 (a b : BitVec 64) : BitVec 64 :=
  fheMontMulThir.denote (.cons a (.cons b .nil))

/-- The THIR-dialect lazy FHE Montgomery REDC denotes `fheMontMulSpec64` — true by
    definition (`fheMontMulSpec64` is that denotation). -/
theorem fheMontMulThir_denote (a b : BitVec 64) :
    fheMontMulThir.denote (.cons a (.cons b .nil)) = fheMontMulSpec64 a b := rfl

/-- **FHE Montgomery REDC re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` denotes the same `BitVec 64` as the width-64
    REDC reference, obtained through `Com[thir] →lowerThir→ Com[jasmin]` (the
    generic, proved `lowerThir_denote`) rather than a bespoke lowering. -/
theorem fheMontMul_via_thirDialect (a b : BitVec 64) :
    (lowerThir fheMontMulThir).denote (.cons a (.cons b .nil)) = fheMontMulSpec64 a b :=
  (lowerThir_denote fheMontMulThir (.cons a (.cons b .nil))).trans
    (fheMontMulThir_denote a b)

/-! ## 4. ABI maps for the 2-in / 1-out width-64 kernel

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp). The argument-slot numbering (`JasminLprogExport.comToLfundef`): argument
slot `s` (program-root order) is context entry `nArgs - 1 - s`. The REDC context
is `[a, b]` (`a = .here`, `b = .there .here`), so input index `a = 0`, `b = 1`,
and arg slot `s ↦ input index (1 - s)`. With C-side `inp = [a, b]`:

* slot `1` → input `a` (`inp[0]`, byte offset 0)
* slot `0` → input `b` (`inp[1]`, byte offset 8)

i.e. `inLoadMap s = ("RSI", 8 * s)` (`s = 0 ↦ inp[1] = b`, `s = 1 ↦ inp[0] = a`).
The single output (the last binding `u`) is stored to `out[0]`. -/

/-- Input-load map: slot `0` is input `b` (`inp[1]`, offset 8); slot `1` is input
    `a` (`inp[0]`, offset 0). Slots `≥ 2` are absent. -/
def fheMontMulInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 8)        -- slot 0 = input b = inp[1]
  else if s = 1 then some ("RSI", 0)   -- slot 1 = input a = inp[0]
  else none

/-- Output-store map: the single result word `u` is stored to `out[0]`. -/
def fheMontMulOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 4b. The MULX-fusion post-pass (byte-faithful `Lprog → Lprog`)

The `64×64→128` widening multiply is split, at the thirDialect-front level, into
a low `thBin .mul` (→ a low `MUL`/`imul`, single dst) and a separate `thMulHi`
(→ a `MULXHI` binding the GP-linear printer DROPS, §6 of the older shell). They
are never fused, so the emitted `.s` loses the high words `hi`/`mqHi` — the
pipeline gap. This post-pass mirrors `NttBflyThirOwnedEmit.legalizeShiftImmLprog`
(a structural, byte-faithful `Lprog → Lprog` rewrite that runs on the
already-physical, two-address body) and closes the gap by coalescing each
`MUL`+`MULXHI` pair into the printer's two-output `MULX` arm
(`LprogAsmPrinter` `[dl, dh] "MULX" [s]` ⟹ `mulx s, dl, dh`).

### What it matches

After physical/two-address lowering the FHE REDC body holds, per
`64×64→128` product, the consecutive pair (`s2` is the *shared* multiplicand,
`s1` the other):

```
  Lopn [loDst]  "MUL:64"    [loDst, s2]      -- low word  (two-address: loDst = a·b)
  Lopn [hiDst]  "MULXHI:64" [s1,    s2]      -- high word (dropped by the printer)
```

Both products read the same `s2` (`b` for `a·b`; `q` for `m·q`); the low op's
first source is its own destination (the two-address form), and the `MULXHI`'s
first source `s1` is the *other* multiplicand (`a` resp. `m`). The pass keys the
pair on the **shared second source `s2`** of an immediately-following `MULXHI`
matching a just-seen low `MUL`.

### How it rewrites (rdx pinning)

Intel `MULX dst_hi, dst_lo, src2` reads the implicit multiplicand from `%rdx`
(see `MpnRaEmit`'s "MULX coalesce" / the printer's `[dl,dh] MULX [s]` arm). The
pass emits, in place of the `MULXHI` line, an explicit `MOV:64 RDX, s1` (pin the
other multiplicand into `%rdx`) followed by `Lopn [loDst, hiDst] "MULX" [s2]`
(re-deriving the low word into `loDst` — identical value — and the high word
into `hiDst`). The standalone low `MUL` is left in place: its low word is read
*before* this point (the REDC computes `m = lo·qinv` from `loDst` between the two
mul sites), and the `MULX` recomputes the same low word, so the value is
unchanged.

### Why `%rdx` is free at both mul sites (and the relocation)

`%rdx` is the *allocated home* of the FIRST product's high word `hi`
(the allocator placed `mulhi(a,b) → RDX`), and `hi` is live until the final
`ADCX` (`u = hi + mqHi + cout`). The SECOND mul site's `MOV RDX, m` would
clobber that live `hi`. To keep the rewrite value-faithful the pass **relocates
any high word the pass itself assigns to `RDX`** into the caller-saved scratch
`R8` — which is unused anywhere in this straight-line REDC body (it is not in
the prologue's callee-saved `qsave` set, and never read/written by the core) —
and records a `RDX → R8` rename applied to every *subsequent* instruction (so
the final `ADCX` reads `hi` from `R8`). With `hi` evacuated to `R8`, `%rdx` is
free to carry the second multiplicand `m`; the second product's high word
`mqHi` lands in its own allocated `RDI` (no further conflict). Both mul sites
therefore get a clean `%rdx`.

The `R8` evacuation register is the one caller-saved GP register
(`R8 R9 R10 R11`) the REDC body never touches; the pass also renames any later
`RDX` use, so no live value is lost. -/

/-- The scratch register used to evacuate a high word the fusion would otherwise
    leave in `%rdx` (caller-saved, unused by the straight-line REDC core). -/
def fuseScratch : String := "R8"

/-- Recognise a low widening-multiply binding (`MUL`, optionally `:64`-tagged),
    the producer of the low word whose paired high word is a `MULXHI`. -/
def isLowMulMnem (opn : String) : Bool := stripWidthTag opn == "MUL"

/-- Recognise the high-word binding mnemonic (`MULXHI`, optionally `:64`). -/
def isMulHiMnem (opn : String) : Bool := stripWidthTag opn == "MULXHI"

/-- Apply a single `oldReg → newReg` rename to an operand. -/
def renameOperand (oldR newR : String) : LOperand → LOperand
  | .reg n => if n == oldR then .reg newR else .reg n
  | o => o

/-- Apply a single `oldReg → newReg` rename across an instruction's operands. -/
def renameInstr (oldR newR : String) (i : Linstr) : Linstr :=
  match i.li_i with
  | .Lopn dsts opn srcs =>
      ⟨i.li_ii, .Lopn (dsts.map (renameOperand oldR newR)) opn
        (srcs.map (renameOperand oldR newR))⟩
  | _ => i

/-- The fusion worker over a body, carrying the list of pending low-`MUL`
    bindings seen so far (each as `(loDst, sharedSrc2)`) head-most-recent.

    On a `MULXHI [hiDst] [s1, s2]` whose `s2` matches a pending low `MUL`'s
    second source, emit the printer's fused `MULX`:
    `MOV:64 RDX, s1 ; MULX [loDst, hiDst'] [s2]`, where `hiDst'` is `hiDst`
    unless `hiDst = RDX` (then it is relocated to `fuseScratch` and a
    `RDX → fuseScratch` rename is threaded through the *rest* of the body, so
    the high word survives the next site's `MOV RDX, …`). Every other
    instruction passes through unchanged (after any active rename).

    `saveRdx` (the LOOPED-body mode): this pass runs POST-RA, so its `MOV RDX,
    s1` pin silently clobbers whatever live range the allocator homed in
    `%rdx` — in a rolled loop that is the LOOP COUNTER (the fri_proof phase-2
    runaway). With `saveRdx := true` each fused site brackets the pin with
    `MOV R15, RDX … MOV RDX, R15` (`R15` = `reloadScratch`, reserved — never
    RA-allocated, and dead between its transient reload uses); an `s2 = RDX`
    source reads the saved copy, and the restore is skipped when the fused op
    itself redefines `RDX` (its old value is dead there). `false` (every
    straight-line caller) emits the original sequence byte-identically. -/
def fuseMulHiAux (saveRdx : Bool) : List (String × String) → Lcmd → Lcmd
  | _, [] => []
  | pend, i :: rest =>
    match i.li_i with
    | .Lopn [.reg d] opn [.reg s1, .reg s2] =>
        if isLowMulMnem opn then
          -- Remember this low MUL (dst + shared second source `s2`) for a later
          -- MULXHI. (`s1` is the low op's own dst in two-address form.)
          i :: fuseMulHiAux saveRdx ((d, s2) :: pend) rest
        else if isMulHiMnem opn then
          -- Match the MOST-RECENT pending low `MUL` with shared second source and
          -- CONSUME it (remove from `pend`), so a later `MULXHI` with the same `s2`
          -- (register reuse across butterflies) pairs with a DISTINCT low `MUL`.
          match pend.span (fun p => p.2 != s2) with
          | (before, (loDst, _) :: after) =>
              let pend' := before ++ after          -- pend minus the matched entry
              -- `s1` is the OTHER multiplicand (pin into %rdx); `loDst` is the
              -- matched low word's home (re-derived, same value).
              let save : List Linstr :=
                if saveRdx then [⟨i.li_ii, .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"]⟩]
                else []
              let s2r := if saveRdx && s2 == "RDX" then "R15" else s2
              let movRdx : Linstr := ⟨i.li_ii, .Lopn [.reg "RDX"] "MOV:64" [.reg s1]⟩
              if d == "RDX" then
                -- The high word's allocated home is %rdx itself; relocate it to a
                -- caller-saved scratch and rename later RDX reads so the next
                -- site's `MOV RDX, …` cannot clobber this live high word. (`RDX`
                -- is redefined here, so `saveRdx` emits no restore.)
                let mulx : Linstr :=
                  ⟨i.li_ii, .Lopn [.reg loDst, .reg fuseScratch] "MULX" [.reg s2r]⟩
                save ++ movRdx :: mulx ::
                  fuseMulHiAux saveRdx pend' (rest.map (renameInstr "RDX" fuseScratch))
              else
                let mulx : Linstr :=
                  ⟨i.li_ii, .Lopn [.reg loDst, .reg d] "MULX" [.reg s2r]⟩
                let restore : List Linstr :=
                  if saveRdx && loDst != "RDX" then
                    [⟨i.li_ii, .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"]⟩]
                  else []
                save ++ movRdx :: mulx :: (restore
                  ++ fuseMulHiAux saveRdx pend' rest)
          | (_, []) => i :: fuseMulHiAux saveRdx pend rest
        else
          i :: fuseMulHiAux saveRdx pend rest
    | _ => i :: fuseMulHiAux saveRdx pend rest
  termination_by _ body => body.length
  decreasing_by all_goals simp_wf


/-- Fuse every paired low-`MUL` + `MULXHI` in a body into the printer's
    two-output `MULX`, pinning the multiplicand into `%rdx` and evacuating any
    `%rdx`-homed high word into `fuseScratch`. `saveRdx := true` is the
    looped-body mode (see `fuseMulHiAux`). -/
def fuseMulHiBody (body : Lcmd) (saveRdx : Bool := false) : Lcmd :=
  fuseMulHiAux saveRdx [] body

/-- Apply the MULX fusion to every function body of an `Lprog`. `saveRdx :=
    true` is the looped-body mode (see `fuseMulHiAux`); the default keeps every
    straight-line caller byte-identical. -/
def fuseMulHiLprog (p : Lprog) (saveRdx : Bool := false) : Lprog :=
  { p with
    lp_funcs := p.lp_funcs.map (fun (n, f) =>
      (n, { f with lfd_body := fuseMulHiBody f.lfd_body saveRdx })) }

/-! ## 5. The owned `Lprog` and AT&T emission (no jasminc)

The single-output REDC is lowered through the thirDialect spine
(`lowerThir fheMontMulThir`) and exported to a physical, two-address SysV
`Lprog`, then the §4b MULX-fusion post-pass coalesces each paired low `MUL` +
`MULXHI` into a real two-output `mulx`, and the result is rendered to AT&T. No
shift-immediate legalisation pass is needed: the REDC has no `thShrImm`/`thRor`
(the carry-chain `ADCX` replaces the `>> 32`-shift reduction used by the 32-bit
lazy REDC); its ops are `MUL` (`thBin .mul`), `MULXHI` (`thMulHi`),
`ADCX`/`ADCXHI` (`thAddCarryLo`/`thAddCarryHi`) and `regConst`. After the §4b
fusion the high words `hi`/`mqHi` ARE materialised (two `mulx` lines); the
remaining un-closed seam is the ADX carry-chain rendering (see the note on
`fheMontMulOwnedAsm_shape` in §6). -/

/-- The FHE Montgomery REDC lowered through the thirDialect spine and exported to
    a physical, two-address SysV `Lprog`. The `fname` `"fhe_montmul"` becomes the
    emitted asm label (matching the C extern). -/
def fheMontMulOwnedLprog : Lprog :=
  fuseMulHiLprog
    (Com.toLprogPhysAbi (lowerThir fheMontMulThir) "fhe_montmul"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (constants are in-body regConst)
      fheMontMulInLoadMap                   -- inLoadMap
      fheMontMulOutStoreMap                 -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64, 64])                             -- abiTyin (a, b)

/-- The rendered owned-backend AT&T `.s` for `fhe_montmul` (no jasminc). -/
def fheMontMulOwnedAsm : String := renderLprogAtt fheMontMulOwnedLprog

/-! ## 6. Shape check on the emitted asm (conservative) -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The emitted `.s` carries the `fhe_montmul` leaf label. -/
theorem fheMontMulOwnedAsm_has_leaf :
    hasSub fheMontMulOwnedAsm "fhe_montmul" = true := by native_decide

/-- The emitted `.s` contains no unhandled-op sentinel. -/
theorem fheMontMulOwnedAsm_no_unhandled :
    hasSub fheMontMulOwnedAsm "UNHANDLED" = false := by native_decide

/-- The emitted `.s` now contains real `mulx` instructions (the §4b fusion
    materialised the `64×64→128` high words). -/
theorem fheMontMulOwnedAsm_uses_mulx :
    hasSub fheMontMulOwnedAsm "mulx" = true := by native_decide

/-- The emitted `.s` no longer carries a dropped/unhandled `MULXHI` binding (the
    §4b fusion rewrote every `MULXHI` into a two-output `mulx`). -/
theorem fheMontMulOwnedAsm_no_mulxhi :
    hasSub fheMontMulOwnedAsm "MULXHI" = false := by native_decide

/-- Shape check on the emitted REDC `.s`: the `fhe_montmul` leaf is present,
    there is no unhandled-op sentinel, the `64×64→128` high words are now emitted
    as real `mulx` instructions, and no dropped `MULXHI` binding remains.

    **Post-§4b status (for the orchestrator's GMP KAT).** The §4b MULX-fusion
    post-pass closes the high-word gap: each paired low `MUL` + `MULXHI` is
    coalesced into the printer's two-output `mulx` (multiplicand pinned into
    `%rdx`; the first product's `%rdx`-homed high word is evacuated to the
    caller-saved scratch `R8`, with a `RDX → R8` rename threaded through the rest
    of the body so the live high word survives the second site's `MOV RDX, …`).
    The emitted `.s` therefore now materialises both high words `hi`/`mqHi`.

    **Remaining seam (NOT closed here; flagged for the KAT).** The ADX
    carry-chain at the tail (`ADCXHI` cout = carryout(`lo + mqLo`); `ADCX`
    `u = hi + mqHi + cout`) is rendered by the shared `LprogAsmPrinter` ADX arm,
    which drops the `ADCXHI` carry-out binding and emits the `ADCX` data op as a
    two-address `adcx s, d` *assuming* the self-source (the high word) was already
    coalesced onto `d`. That coalescing MOV is not present for this allocation, so
    the final `adcxq` accumulates onto the low word rather than the high word, and
    the low-word carry `cout` is not generated by a discrete instruction. Fixing
    this is a `LprogAsmPrinter`/two-address-lowering concern (a shared file, out of
    scope for this contained emit-module pass); it is called out so the GMP KAT can
    target the carry-propagation specifically. The Lean-level `fheMontMulThir` /
    `fheMontMulSpec64` denotation remains the correct REDC reference. -/
theorem fheMontMulOwnedAsm_shape :
    hasSub fheMontMulOwnedAsm "fhe_montmul"
      ∧ hasSub fheMontMulOwnedAsm "UNHANDLED" = false
      ∧ hasSub fheMontMulOwnedAsm "mulx" = true
      ∧ hasSub fheMontMulOwnedAsm "MULXHI" = false :=
  ⟨fheMontMulOwnedAsm_has_leaf, fheMontMulOwnedAsm_no_unhandled,
   fheMontMulOwnedAsm_uses_mulx, fheMontMulOwnedAsm_no_mulxhi⟩

/-! ## 7. Emit driver -/

/-- Write the owned-backend `.s` for the 60-bit FHE Montgomery multiply
    (`fhe_montmul`) into the `bench/fhe_ntt_compare/gen` harness directory (no
    jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/fhe_ntt_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/fhe_montmul.s") fheMontMulOwnedAsm
  IO.println "WROTE bench/fhe_ntt_compare/gen/fhe_montmul.s"
  IO.println "  (60-bit FHE-NTT Montgomery REDC fheMontMulThir through Com[thir] -> lowerThir ->"
  IO.println "   toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend, NO jasminc;"
  IO.println "   q = 1152921504606830593, qinv = 1080859512253956095, R = 2^64)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulOwnedEmit
