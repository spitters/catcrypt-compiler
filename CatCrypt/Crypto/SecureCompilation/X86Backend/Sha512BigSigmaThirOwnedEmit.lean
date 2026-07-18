/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# SHA-512 Σ₀ and Σ₁ uppercase-sigma words through the OWNED x86 backend (no jasminc)

The FIPS 180-4 §4.1.3 uppercase-Sigma functions for SHA-512 (width 64) driven
through the `compile-from-hax` front (`Com thirDialect`) onto the OWNED x86
backend — NO jasminc anywhere. The pure-rotate sibling of
`Sha512SigmaThirOwnedEmit.lean` (the SHA-512 lowercase-σ leaves): same single-u64
input, but all THREE terms are rotate-immediates (no shift):

    Σ₀_512(x) = ROTR²⁸(x) ⊕ ROTR³⁴(x) ⊕ ROTR³⁹(x)   (FIPS 180-4 §4.1.3)
    Σ₁_512(x) = ROTR¹⁴(x) ⊕ ROTR¹⁸(x) ⊕ ROTR⁴¹(x)   (FIPS 180-4 §4.1.3)

These are genuinely-SHA-512 primitives: the `Σ₀`/`Σ₁` uppercase-Sigma functions
of the SHA-512 compression round `T₁ = h + Σ₁(e) + Ch(e,f,g) + K_t + W_t`,
`T₂ = Σ₀(a) + Maj(a,b,c)` over `u64` words. We build each program directly at the
`thirDialect` level (`thRor 64`/`thBin .xor 64` — NO `thShrImm`, all three terms
are rotates) — mirroring the committed lowercase-σ `sha512Sigma{0,1}Thir`
constructor shapes with the shift term replaced by a third rotate — and emit both
as owned-backend leaves in a single `.s`.

The pipeline mirrors `Sha512SigmaThirOwnedEmit`:

    sha512BigSigma{0,1}Thir : Com thirDialect [.reg 64] (.reg 64)
      --lowerThir-->            Com jasminDialect [.reg 64] (.reg 64)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the single input is loaded from `[RSI + 0]` and the single output stored
to `[RDI + 0]`:

```c
extern void sha512_bigsigma0(uint64_t *out, const uint64_t *inp);  // inp = [x]
extern void sha512_bigsigma1(uint64_t *out, const uint64_t *inp);  // inp = [x]
```

With a single input (`nArgs = 1`) the only slot is `s = 0 ↦ input index 0 =
inp[0]`, so `inLoadMap 0 = ("RSI", 0)`. The single output (the last binding, the
final xor) is stored to `out[0]` (`outStoreMap = [("RDI", 0)]`).

## The three rotates (width-64 immediate legalisation)

Each Σ's `ROTR`s lower (via `thRor 64`) to rotate-immediate `Lopn` forms. The
owned printer recognises NO rotate mnemonic. `legalizeShiftImmLprog` (cloned from
`Sha512SigmaThirOwnedEmit`, which carries the width-generic `:64`-tagged path
already exercised by `Blake2bGThirOwnedEmit`) rewrites each rotate
`Lopn [d] "ROR:<n>:64" [s]` → the canonical shift-or idiom over the reserved
scratch `R15` (`ror(d,n) = (d>>n)|(d<<(64-n))`), all four lines in
printer-recognised two-source `Lopn` forms (`MOV:64`/`SHR:64`/`SHL:64`/`OR:64`).

So the emitted `.s` carries no unhandled-op sentinel.

## What is verified vs trusted

* **Verified (value)**: `sha512BigSigma0Thir_denote` / `sha512BigSigma1Thir_denote`
  (the leaves denote `Σ₀`/`Σ₁` = `sha512BigSigma0Spec`/`sha512BigSigma1Spec`)
  and `bigSigma{0,1}_via_thirDialect` (the lowered `Com jasminDialect` denotes
  the same).
* **Verified (printer)**: the shape lemma below pins that the emitted `.s`
  carries both SysV leaf labels and has no unhandled-op sentinel.
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity `sha512_bigsigma{0,1}(x) == Σ{0,1}(x)` is the external `as`/`cc`
KAT in `bench/thir_front_sha512_bigsigma_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512BigSigmaThirOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-! ## 0. FIPS 180-4 §4.1.3 SHA-512 Σ₀/Σ₁ reference specs (width 64) -/

/-- FIPS 180-4 §4.1.3 Σ₀_512(x) = ROTR²⁸(x) ⊕ ROTR³⁴(x) ⊕ ROTR³⁹(x). -/
def sha512BigSigma0Spec (x : BitVec 64) : BitVec 64 :=
  (x.rotateRight 28) ^^^ (x.rotateRight 34) ^^^ (x.rotateRight 39)

/-- FIPS 180-4 §4.1.3 Σ₁_512(x) = ROTR¹⁴(x) ⊕ ROTR¹⁸(x) ⊕ ROTR⁴¹(x). -/
def sha512BigSigma1Spec (x : BitVec 64) : BitVec 64 :=
  (x.rotateRight 14) ^^^ (x.rotateRight 18) ^^^ (x.rotateRight 41)

/-! ## 1. The SHA-512 Σ₀/Σ₁ programs as `Com thirDialect` leaves

Built directly at the THIR-dialect level (`thRor 64`, `thBin .xor 64`),
mirroring the committed lowercase-σ `sha512Sigma{0,1}Thir` constructor shapes,
with the lone shift term replaced by a third rotate (these uppercase-Σ functions
are PURE rotates — no shift):

    let r_a = thRor 64 a x;  let r_b = thRor 64 b x;  let r_c = thRor 64 c x
    let t   = thBin xor r_a r_b;  let o = thBin xor t r_c;  ret o -/

/-- SHA-512 Σ₀ as a `Com thirDialect` over `[reg 64]` (input `x = here`):
    `ROTR²⁸ ⊕ ROTR³⁴ ⊕ ROTR³⁹`. -/
def sha512BigSigma0Thir : Com thirDialect [.reg 64] (.reg 64) :=
  .var (.mk (.thRor 64 28) rfl (.cons .here .nil))
    (.var (.mk (.thRor 64 34) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thRor 64 39) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 64) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 64) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- SHA-512 Σ₁ as a `Com thirDialect` over `[reg 64]` (input `x = here`):
    `ROTR¹⁴ ⊕ ROTR¹⁸ ⊕ ROTR⁴¹`. -/
def sha512BigSigma1Thir : Com thirDialect [.reg 64] (.reg 64) :=
  .var (.mk (.thRor 64 14) rfl (.cons .here .nil))
    (.var (.mk (.thRor 64 18) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thRor 64 41) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 64) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 64) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- The THIR-dialect Σ₀ denotes to the FIPS Σ₀_512 spec on any input valuation. -/
theorem sha512BigSigma0Thir_denote (x : BitVec 64) :
    sha512BigSigma0Thir.denote (.cons x .nil) = sha512BigSigma0Spec x := by
  rfl

/-- The THIR-dialect Σ₁ denotes to the FIPS Σ₁_512 spec on any input valuation. -/
theorem sha512BigSigma1Thir_denote (x : BitVec 64) :
    sha512BigSigma1Thir.denote (.cons x .nil) = sha512BigSigma1Spec x := by
  rfl

/-- **Σ₀_512 re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for Σ₀ denotes the same `BitVec 64` as the FIPS Σ₀ spec. -/
theorem bigSigma0_via_thirDialect (x : BitVec 64) :
    (lowerThir sha512BigSigma0Thir).denote (.cons x .nil) = sha512BigSigma0Spec x := by
  rw [lowerThir_denote sha512BigSigma0Thir (.cons x .nil), sha512BigSigma0Thir_denote]

/-- **Σ₁_512 re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for Σ₁ denotes the same `BitVec 64` as the FIPS Σ₁ spec. -/
theorem bigSigma1_via_thirDialect (x : BitVec 64) :
    (lowerThir sha512BigSigma1Thir).denote (.cons x .nil) = sha512BigSigma1Spec x := by
  rw [lowerThir_denote sha512BigSigma1Thir (.cons x .nil), sha512BigSigma1Thir_denote]

/-! ## 2. ABI maps for the 1-in / 1-out width-64 Σ leaves -/

/-- Input-load map: the single arg slot `0` ↦ `("RSI", 0)` (input `x = inp[0]`).
    Slots `≥ 1` are absent (each Σ has exactly one input). -/
def bigSigmaInLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 0) else none

/-- Output-store map: the single result word (the last xor binding) is stored to
    `out[0]` (`[RDI + 0]`). -/
def bigSigmaOutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 3. Rotate immediate legalisation post-pass

Cloned from `Sha512SigmaThirOwnedEmit` (which carries the width-generic
`:64`-tagged path already exercised by `Blake2bGThirOwnedEmit`). The owned
printer recognises NO rotate mnemonic. So a rotate `ROR:<n>:64` expands into the
shift-or idiom over the reserved scratch `R15`: `ror(d, n) = (d >> n) |
(d << (64 - n))`, emitted as

    MOV:64 R15, d ;  SHR:64 R15, #n ;  SHL:64 d, #(64-n) ;  OR:64 d, R15

All four lines use printer-recognised two-source `Lopn` forms. (The unary
shift-immediate path is retained for genericity; these pure-rotate Σ leaves emit
only rotates.) -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (reloadScratch)

/-- Parse a unary shift-immediate mnemonic `"SHR:<n>"` / `"SHL:<n>"` (optionally
    width-tagged `":64"`) into `(baseMnem, count)`. Returns `none` for any other
    mnemonic (so every non-shift-imm `Lopn` is left untouched). -/
def parseShiftImm (opn : String) : Option (String × Nat) :=
  let isU64 := opn.endsWith ":64"
  let core := if isU64 then String.ofList (opn.toList.dropLast.dropLast.dropLast) else opn
  match core.splitOn ":" with
  | [base, cnt] =>
      if base = "SHR" || base = "SHL" then
        match cnt.toNat? with
        | some n => some ((if isU64 then base ++ ":64" else base), n)
        | none => none
      else none
  | _ => none

/-- Parse a rotate-immediate mnemonic `"ROR:<n>"` / `"ROL:<n>"` (optionally
    width-tagged `":64"`) into `(baseDir, count, width)` where `baseDir` is
    `"ROR"` or `"ROL"` and `width` is `64` for a `:64`-tagged op else `32`.
    Returns `none` for any other mnemonic. -/
def parseRotImm (opn : String) : Option (String × Nat × Nat) :=
  let isU64 := opn.endsWith ":64"
  let core := if isU64 then String.ofList (opn.toList.dropLast.dropLast.dropLast) else opn
  match core.splitOn ":" with
  | [base, cnt] =>
      if base = "ROR" || base = "ROL" then
        match cnt.toNat? with
        | some n => some (base, n, if isU64 then 64 else 32)
        | none => none
      else none
  | _ => none

/-- Width-tag suffix (`":64"` for 64-bit, empty for 32-bit). -/
def wTag (w : Nat) : String := if w = 64 then ":64" else ""

/-- Expand an in-place rotate of register `d` by `n` (width `w`) into the
    shift-or idiom over scratch `R15`. `ror(d,n) = (d>>n)|(d<<(w-n))`;
    `rol(d,n) = ror(d, w-n)`. All four lines are printer-recognised two-source
    forms. `ii` is the carried instruction info. -/
def expandRotInPlace (ii : Nat) (d : LOperand) (dir : String)
    (n w : Nat) : List Linstr :=
  let rn := if dir = "ROL" then (w - n) % w else n % w
  let ln := (w - rn) % w
  let sh := wTag w
  let mv := if w = 64 then "MOV:64" else "MOV"
  [⟨ii, .Lopn [.reg reloadScratch] mv [d]⟩,
   ⟨ii, .Lopn [.reg reloadScratch] ("SHR" ++ sh) [.reg reloadScratch, .imm rn]⟩,
   ⟨ii, .Lopn [d] ("SHL" ++ sh) [d, .imm ln]⟩,
   ⟨ii, .Lopn [d] ("OR" ++ sh) [d, .reg reloadScratch]⟩]

/-- Rewrite one already-allocated `Linstr`:

    * a unary shift-immediate `Lopn [d] "SHR:<n>[:64]" [s]` → two-source
      `[d] SHR[:64] [d, #n]` (prefixed by `MOV d, s` when `d ≠ s`);
    * a rotate `Lopn [d] "ROR:<n>[:w]" [s]` → (a `MOV d, s` when `d ≠ s`)
      followed by the `expandRotInPlace` shift-or idiom over `R15`;

    every other instruction passes through unchanged. -/
def legalizeShiftImmInstr (i : Linstr) : List Linstr :=
  match i.li_i with
  | .Lopn [d] opn [s] =>
      match parseShiftImm opn with
      | some (baseMnem, n) =>
          let movMnem := if baseMnem.endsWith ":64" then "MOV:64" else "MOV"
          if d = s then
            [⟨i.li_ii, .Lopn [d] baseMnem [d, .imm n]⟩]
          else
            [⟨i.li_ii, .Lopn [d] movMnem [s]⟩,
             ⟨i.li_ii, .Lopn [d] baseMnem [d, .imm n]⟩]
      | none =>
        match parseRotImm opn with
        | some (dir, n, w) =>
            let movMnem := if w = 64 then "MOV:64" else "MOV"
            let prefixMov := if d = s then [] else [(⟨i.li_ii, .Lopn [d] movMnem [s]⟩ : Linstr)]
            prefixMov ++ expandRotInPlace i.li_ii d dir n w
        | none => [i]
  | _ => [i]

/-- Apply `legalizeShiftImmInstr` across a whole body. -/
def legalizeShiftImmBody (body : Lcmd) : Lcmd :=
  body.flatMap legalizeShiftImmInstr

/-- Apply the rotate-immediate legalisation to every function body of an `Lprog`. -/
def legalizeShiftImmLprog (p : Lprog) : Lprog :=
  { p with
    lp_funcs := p.lp_funcs.map (fun (n, f) =>
      (n, { f with lfd_body := legalizeShiftImmBody f.lfd_body })) }

/-! ## 4. The owned `Lprog`s and combined AT&T emission (no jasminc) -/

/-- Build a 1-in/1-out width-64 owned `Lprog` for a `Com thirDialect [.reg 64]`
    Σ leaf under the SysV 2-pointer ABI, rotate-immediate-legalised. -/
def bigSigmaOwnedLprog (com : Com thirDialect [.reg 64] (.reg 64)) (fname : String) : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir com) fname
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      bigSigmaInLoadMap                     -- inLoadMap
      bigSigmaOutStoreMap                   -- outStoreMap
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [64])                                 -- abiTyin (1 u64 input)

/-- Σ₀_512 owned `Lprog` (`fname` `"sha512_bigsigma0"`). -/
def bigSigma0OwnedLprog : Lprog := bigSigmaOwnedLprog sha512BigSigma0Thir "sha512_bigsigma0"

/-- Σ₁_512 owned `Lprog` (`fname` `"sha512_bigsigma1"`). -/
def bigSigma1OwnedLprog : Lprog := bigSigmaOwnedLprog sha512BigSigma1Thir "sha512_bigsigma1"

/-- Both Σ leaves combined into a single `Lprog` (`lp_funcs` concatenated), so
    `renderLprogAtt` emits one `.s` carrying both `sha512_bigsigma0` and
    `sha512_bigsigma1`. -/
def sha512BigSigmaOwnedLprog : Lprog :=
  { bigSigma0OwnedLprog with
    lp_funcs := bigSigma0OwnedLprog.lp_funcs ++ bigSigma1OwnedLprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for both Σ leaves (no jasminc). -/
def sha512BigSigmaOwnedAsm : String := renderLprogAtt sha512BigSigmaOwnedLprog

/-! ## 5. Shape checks on the emitted asm -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The emitted `.s` carries both SysV leaf labels and has no unhandled-op
    sentinel. (Rotate mnemonics are not asserted — the legalisation lands the
    rotates in GP-register shift-or forms whose exact printed mnemonic is left to
    the printer.) -/
theorem sha512BigSigmaOwnedAsm_shape :
    hasSub sha512BigSigmaOwnedAsm "sha512_bigsigma0"
      ∧ hasSub sha512BigSigmaOwnedAsm "sha512_bigsigma1"
      ∧ hasSub sha512BigSigmaOwnedAsm "UNHANDLED" = false := by native_decide

/-! ## 6. Emit driver -/

/-- Write the owned-backend `.s` for `sha512_bigsigma0`/`sha512_bigsigma1` into
    the `bench/thir_front_sha512_bigsigma_owned/gen` harness directory (no
    jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha512_bigsigma_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha512_bigsigma_owned.s") sha512BigSigmaOwnedAsm
  IO.println "WROTE bench/thir_front_sha512_bigsigma_owned/gen/sha512_bigsigma_owned.s"
  IO.println "  (SHA-512 BigSigma0/BigSigma1 uppercase-sigma words sha512BigSigma{0,1}Thir"
  IO.println "   through Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt"
  IO.println "   onto the OWNED x86 backend, NO jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512BigSigmaThirOwnedEmit
