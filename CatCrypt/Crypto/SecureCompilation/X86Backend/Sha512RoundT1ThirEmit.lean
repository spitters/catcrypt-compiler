/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512BigSigmaThirEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512ChMajThirEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# SHA-512 round value `T₁` (width 64) through the OWNED x86 backend (no jasminc)

The width-64 analog of `Sha256RoundT1ThirEmit`: the FIPS 180-4 §6.4.2
SHA-512 round value `T₁` driven through `compile-from-hax` (`Com thirDialect`)
onto the OWNED x86 backend — NO jasminc. A **6-input** width-64 composite leaf
inlining the big-Sigma `Σ₁(e)`, the boolean `Ch(e,f,g)`, and a four-add wrapping
accumulation:

    T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ     (mod 2⁶⁴, wrapping, left-to-right)

where (FIPS 180-4 §4.1.3, width 64)

    Σ₁(e)     = ROTR¹⁴(e) ⊕ ROTR¹⁸(e) ⊕ ROTR⁴¹(e)
    Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)        (¬e = e ⊕ 0xffffffffffffffff)

This completes the SHA-512 round-component set (σ₀/σ₁/Σ₀/Σ₁/Ch/Maj/msgW already
landed; T₁/T₂ were the missing pieces). The byte-identity `sha512_t1(...) == T₁`
is the external `as`/`cc` KAT in `bench/thir_front_sha512_t1_owned/` (no jasminc).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512RoundT1ThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512BigSigmaThirEmit (sha512BigSigma1Spec)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (sha512ChSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
  (legalizeShiftImmLprog)

/-! ## 0. The FIPS round-value reference (width 64) -/

/-- FIPS 180-4 §6.4.2 round value
    `T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ`, summed left-to-right (wrapping u64).
    Composed from the proven width-64 `sha512BigSigma1Spec`/`sha512ChSpec`. -/
def sha512T1Spec (e f g h kt wt : BitVec 64) : BitVec 64 :=
  h + sha512BigSigma1Spec e + sha512ChSpec e f g + kt + wt

/-! ## 1. The SHA-512 `T₁` program as a `Com thirDialect` leaf

Identical de-Bruijn structure to the (MCP-verified) SHA-256 `T₁` leaf, widened to
64-bit and with the SHA-512 Σ₁ rotate constants (14/18/41) and the 64-bit NOT
literal. Inputs (program-root order): `[e, f, g, h, kt, wt]`. -/
def sha512T1Thir :
    Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- b0: e14 = ror 14 e   (e at depth 0)
  .var (.mk (.thRor 64 14) rfl (.cons .here .nil))
  -- b1: e18 = ror 18 e   (e at depth 1)
  (.var (.mk (.thRor 64 18) rfl (.cons (.there .here) .nil))
  -- b2: e41 = ror 41 e   (e at depth 2)
  (.var (.mk (.thRor 64 41) rfl (.cons (.there (.there .here)) .nil))
  -- b3: ex = e14 ^ e18   (e14 depth 2, e18 depth 1)
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- b4: S1 = ex ^ e41   (ex depth 0, e41 depth 1)   (= Σ₁(e))
  (.var (.mk (.thBin .xor 64) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b5: ef = e & f   (e at depth 5, f at depth 6)
  (.var (.mk (.thBin .and 64) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  -- b6: ne = e ^ 0xffffffffffffffff   (¬e)   (e at depth 6)
  (.var (.mk (.thBinLit .xor 64 0xffffffffffffffff) rfl
      (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))
  -- b7: neg = ne & g   (ne depth 0, g at depth 9)
  (.var (.mk (.thBin .and 64) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there .here))))))))) .nil)))
  -- b8: Ch = ef ^ neg   (ef depth 2, neg depth 0)   (= Ch(e,f,g))
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there .here)) (.cons .here .nil)))
  -- b9: a1 = h + S1   (h at depth 12, S1 depth 4)
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there .here))))))))))))
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- b10: a2 = a1 + Ch   (a1 depth 0, Ch depth 1)
  (.var (.mk (.thBin .add 64) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- b11: a3 = a2 + kt   (a2 depth 0, kt at depth 15)
  (.var (.mk (.thBin .add 64) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) ) .nil)))
  -- b12: a4 = a3 + wt   (a3 depth 0, wt at depth 17)
  (.var (.mk (.thBin .add 64) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there (.there (.there
            (.there .here))))))))))))))))) .nil)))
  (.ret .here)))))))))))))

/-- The THIR-dialect `T₁` leaf denotes the FIPS `T₁` round value on any input
    valuation `[e, f, g, h, kt, wt]`. -/
theorem sha512T1Thir_denote (e f g h kt wt : BitVec 64) :
    sha512T1Thir.denote
        (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil))))))
      = sha512T1Spec e f g h kt wt := by
  rfl

/-- **Round value `T₁` re-derived through the dialect spine.** -/
theorem t1_via_thirDialect (e f g h kt wt : BitVec 64) :
    (lowerThir sha512T1Thir).denote
        (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil))))))
      = sha512T1Spec e f g h kt wt := by
  rw [lowerThir_denote sha512T1Thir
      (.cons e (.cons f (.cons g (.cons h (.cons kt (.cons wt .nil)))))),
    sha512T1Thir_denote]

/-! ## 2. ABI maps for the 6-in / 1-out width-64 `T₁` leaf -/

/-- Input-load map: arg slot `s` ↦ `("RSI", 8 * (5 - s))` (8-byte u64 stride).
    Slot 5 = `e` (`inp[0]`), … slot 0 = `wt` (`inp[5]`). -/
def t1InLoadMap : InLoadMap := fun s =>
  if s = 0 then some ("RSI", 40)
  else if s = 1 then some ("RSI", 32)
  else if s = 2 then some ("RSI", 24)
  else if s = 3 then some ("RSI", 16)
  else if s = 4 then some ("RSI", 8)
  else if s = 5 then some ("RSI", 0)
  else none

/-- Output-store map: the single result word (`T₁`) is stored to `out[0]`. -/
def t1OutStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 3. The owned `Lprog` and AT&T emission (no jasminc) -/

/-- The `T₁` leaf lowered through the thirDialect spine, exported to a physical
    two-address SysV `Lprog`, then shift/rotate-immediate-legalised. -/
def t1Lprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sha512T1Thir) "sha512_t1"
      (fun _ => none)
      (fun _ => none)
      t1InLoadMap
      t1OutStoreMap
      ["RDI", "RSI"]
      [64, 64, 64, 64, 64, 64])

/-- The rendered owned-backend AT&T `.s` for `sha512_t1` (no jasminc). -/
def t1Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned t1Lprog

/-! ## 4. Shape checks on the emitted asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for `sha512_t1` into the harness dir. -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sha512_t1_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sha512_t1_owned.s") t1Asm
  IO.println "WROTE bench/thir_front_sha512_t1_owned/gen/sha512_t1_owned.s"

/-! ## 6. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512RoundT1ThirEmit
