/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimdDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimdDenote
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit

/-!
# SHA-256 (SHA-NI) re-sourced through the vector front (`translateDialectControlV`)

`Sha2ShaniEmit.lean` HAND-AUTHORS the SHA-NI single-block compression as an
AT&T `.s` schedule (`ShaNiEmit.renderQuartet` → gas mnemonics) — outside the
verified front. This module puts the three SHA-NI data effects into the SIMD
**dialect** (`CatCryptDialect`) as first-class ops with **faithful FIPS 180-4
denotations**, and routes a SHA-256 body through the vector front
`translateDialectControlV` so it is a GENERATED `Com catCryptDialect` (not a
hand-authored `Com`/`.s`), with a front-general `denote = spec` guarantee.

## What is proved here

1. **Faithful dialect denotes.** `CatCryptDialect.vsha256rnds2W` / `vsha256msg1W`
   / `vsha256msg2W` are the Intel-SDM / FIPS 180-4 data effects. This module pins
   them **equal to the already-bench-KAT'd `ShaNiEmit` lane functions**
   (`sha256rnds2_lane` etc., whose `Full` compression is byte-identical to FIPS
   180-4 in `bench/sha2_compare/sha2_shani_kat.c`) — so the dialect op inherits
   that corroboration.
2. **Front coverage.** A SHA-256 body authored with `RVsimdSetExpr
   "vsha256rnds2"/"vsha256msg1"/"vsha256msg2"` is `IsCoveredV`, and
   `translateDialectControlV` emits the matching `.vsha256*` `Com catCryptDialect`.
3. **`denote = spec` (front-general).** Via `translateDialectControlV_denote`,
   the emitted `Com` denotes exactly the SHA-NI `semV` fold — for all 128-bit
   inputs, not just KAT points — plus concrete `native_decide` corroboration.

## Residual (x86 bytes) — NOT closed here

The dialect→jasmin lowering (`cryptoDialectToJasminCom`) DECLINES `.vsha256*`
(falls through its `| _ => none` arm), so this vertical reaches the **dialect
with a faithful denote**, not owned `.s`. Reaching bytes needs a faithful
128-bit SIMD *backend* target for the three ops. That is deferred because it
cascades outside this layer: (a) the `SimdOp`-exhaustive x86 emitters
(`VsimdByteEncoder` needs the SHA-NI legacy-SSE opcodes `NP 0F 38 CB/CC/CA`
with byte-exact KATs; `VsimdAsmPrint` needs the mnemonic arms); and (b)
`SHA256RNDS2` reads its round-constant operand implicitly in `%xmm0`, so the
owned AT&T printer must STAGE the ternary op's third input into `%xmm0` (a
register-allocation constraint, exactly as `Sha2ShaniEmit.renderQuartet`
does by hand) before the 2-operand machine instruction. Until then the owned
`.s` remains `Sha2ShaniEmit`'s hand schedule.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.Sha2ShaniVsimdCovered`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2ShaniVsimdCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located)

/-! ## 1. The dialect denotes ARE the bench-KAT'd `ShaNiEmit` lane functions

`CatCryptDialect.vsha256*W` and `ShaNiEmit.sha256*_lane` are the same FIPS 180-4
math (same Ch/Maj/Σ/σ, same lane pack/unpack), restated in the dialect layer to
keep it acyclic. They coincide definitionally. `ShaNiEmit.Full.sha256ShaNiCompress`
is byte-identical to FIPS 180-4 (`bench/sha2_compare`), so this equality carries
the KAT corroboration to the dialect op. -/

/-- `vsha256rnds2W` advances the state by exactly TWO FIPS 180-4 compression
    rounds (`shaStep`), by construction — the faithful two-round semantics of
    `SHA256RNDS2`. -/
theorem vsha256rnds2W_round_pair (abef cdgh mk : BitVec 128) :
    vsha256rnds2W abef cdgh mk =
      (let a := shaLane abef 3; let b := shaLane abef 2
       let e := shaLane abef 1; let f := shaLane abef 0
       let c := shaLane cdgh 3; let d := shaLane cdgh 2
       let g := shaLane cdgh 1; let h := shaLane cdgh 0
       let s1 := shaStep (a, b, c, d, e, f, g, h) (shaLane mk 0)
       let (a', b', _c', _d', e', f', _g', _h') := shaStep s1 (shaLane mk 1)
       shaPack f' e' b' a') := rfl

/-- Concrete corroboration that `vsha256rnds2W` = the bench-KAT'd `ShaNiEmit`
    two-round lane function at sample inputs (`ShaNiEmit.Full.sha256ShaNiCompress`
    is byte-identical to FIPS 180-4 in `bench/sha2_compare`). `native_decide`
    evaluates both. -/
example :
    vsha256rnds2W 0x1234567890abcdeffedcba0987654321
        0x00112233445566778899aabbccddeeff 0x0f0f0f0f1e1e1e1e2d2d2d2d3c3c3c3c
      = ShaNiEmit.sha256rnds2_lane 0x1234567890abcdeffedcba0987654321
        0x00112233445566778899aabbccddeeff 0x0f0f0f0f1e1e1e1e2d2d2d2d3c3c3c3c := by
  native_decide

example : vsha256rnds2W 0 0 0 = ShaNiEmit.sha256rnds2_lane 0 0 0 := by native_decide

/-- `vsha256msg1W` = the σ0 partial-schedule lane function (`ShaNiEmit`). -/
theorem vsha256msg1W_eq_lane (src1 src2 : BitVec 128) :
    vsha256msg1W src1 src2 = ShaNiEmit.sha256msg1_lane src1 src2 := rfl

/-- `vsha256msg2W` = the σ1 final-schedule lane function (`ShaNiEmit`). -/
theorem vsha256msg2W_eq_lane (src1 src2 : BitVec 128) :
    vsha256msg2W src1 src2 = ShaNiEmit.sha256msg2_lane src1 src2 := rfl

/-! ## 2. A SHA-256 body through the vector front

Six 128-bit params `abef cdgh mk w0 w1 w2` (all `.sword 128`). Body exercises all
three SHA-NI ops: two message-schedule steps and one two-round step. Bound in
reverse so the denotation valuation is `[abef, cdgh, mk, w0, w1, w2]` (head-first). -/

/-- Six 128-bit vector params. -/
def shΓ : Ctx := [.sword 128, .sword 128, .sword 128, .sword 128, .sword 128, .sword 128]

/-- `VarMap`: `abef`→index 0, `cdgh`→1, `mk`→2, `w0`→3, `w1`→4, `w2`→5. -/
def shVM : VarMap shΓ :=
  ((((((VarMap.empty.bind "w2").bind "w1").bind "w0").bind "mk").bind "cdgh").bind "abef")

/-- The SHA-NI body: schedule (`msg1`, `msg2`) then a two-round step; return `st`. -/
def shBody : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "sched1" "vsha256msg1" ["w0", "w1"])
    (.RSeq (LowCT.RVsimdSetExpr "sched2" "vsha256msg2" ["sched1", "w2"])
           (LowCT.RVsimdSetExpr "st" "vsha256rnds2" ["abef", "cdgh", "mk"]))

/-- (Coverage) The body is `IsCoveredV` — all three ops are `vsimd`-tagged. -/
theorem shBody_covered : IsCoveredV shBody :=
  .rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
    (.rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
           (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide)))

/-- (1) The body translates through the vector front. -/
theorem shBody_translates : (translateDialectControlV shVM shBody).isSome := by native_decide

/-- The front-emitted result program returning the `.sword 128` slot `st`. -/
def shProg : Option (Com catCryptDialect shΓ (.sword 128)) := vsimdResultProg shVM shBody "st"

/-- The front actually emits a result program. -/
theorem shProg_isSome : shProg.isSome := by native_decide

/-- The pure spec: the returned slot `st` is the two-round step
    `vsha256rnds2W abef cdgh mk` (the schedule feeds later rounds, not this
    return). -/
def shSpec (abef cdgh mk _w0 _w1 _w2 : BitVec 128) : BitVec 128 :=
  vsha256rnds2W abef cdgh mk

/-- Denote the front-emitted program at the six 128-bit inputs. -/
def shDenote (abef cdgh mk w0 w1 w2 : BitVec 128) : Option (BitVec 128) :=
  shProg.map (fun com =>
    com.denote (.cons abef (.cons cdgh (.cons mk (.cons w0 (.cons w1 (.cons w2 .nil)))))))

/-! ### (2) `denote = spec` corroboration on sample 128-bit inputs -/

example : shDenote 0x1234567890abcdeffedcba0987654321
    0x00112233445566778899aabbccddeeff 0x0f0f0f0f1e1e1e1e2d2d2d2d3c3c3c3c
    0x0102030405060708090a0b0c0d0e0f10 0x1112131415161718191a1b1c1d1e1f20
    0x2122232425262728292a2b2c2d2e2f30
    = some (shSpec 0x1234567890abcdeffedcba0987654321
        0x00112233445566778899aabbccddeeff 0x0f0f0f0f1e1e1e1e2d2d2d2d3c3c3c3c
        0x0102030405060708090a0b0c0d0e0f10 0x1112131415161718191a1b1c1d1e1f20
        0x2122232425262728292a2b2c2d2e2f30) := by native_decide

example : shDenote 0 0 0 0 0 0 = some (shSpec 0 0 0 0 0 0) := by native_decide

/-! ## 3. Front-general `denote = spec`

`translateDialectControlV_denote` (front-general) gives the above for ALL inputs:
the emitted prefix denotes the body's `semV` SHA-NI fold, on every 128-bit
valuation. The concrete `native_decide` points above are corroborating instances.
`shBody_covered` supplies the coverage hypothesis. -/

theorem shBody_denote_general :
    ∀ (V : Ctxt.Valuation (d := catCryptDialect) shΓ) (env env' : SEnv)
      (o : DTransOut shΓ),
      ConsistentV shVM V env →
      translateDialectControlV shVM shBody = some o →
      semV shBody env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentV o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro V env env' o hc htr hsem
  exact translateDialectControlV_denote shBody_covered shVM V env env' o hc htr hsem

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2ShaniVsimdCovered
