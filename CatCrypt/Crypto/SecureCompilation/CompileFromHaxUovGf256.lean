/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the UOV GF(256) multiply from extracted source

This module extends the **C4** step of the verified-compiler plan to the **UOV
GF(256) field multiply** — the hot scalar primitive of the OV-Ip public-map
evaluation (`bench/uov_compare`, `UOV.VerifyEmit.gf256MulInline`). The
earlier C4 leaves drove `compileFromHax` *emitting* a crypto leaf from
hax-extracted source for SHA-256 (`CompileFromHaxLeaves`), Keccak χ
(`CompileFromHaxKeccak`), BLAKE2s ARX (`CompileFromHaxBlake2`), and the Ascon
permutation round (`CompileFromHaxAscon`). Here we do the same for the
bit-serial GF(256) = GF(2)[x]/(x⁸+x⁴+x³+x+1) multiply (the AES field; reduction
poly `0x11B`, low byte `0x1B`).

## GF(256) bit-serial multiply (the schoolbook shift-and-conditional-xor)

On two operands `a`, `b` (low 8 bits used), `p = a · b` over GF(256):

```
sh := a & 0xff;  p := 0
for k = 0 .. 7:
  bit  := (b >> k) & 1;  mask  := 0 - bit            -- 0x0 or all-ones (CT)
  p    := p ^ (sh & mask)
  cy   := (sh >> 7) & 1; cmask := 0 - cy;  red := cmask & 0x1b
  sh   := ((sh << 1) & 0xff) ^ red
p := p & 0xff
```

Every step is `BitAnd`/`BitXor`/`Shl`/`Shr`/`wrapping_sub` over the low byte —
**pure scalar shift/xor/and/mask**, the same shape class as the SHA-256 `Ch`
leaf and the Ascon S-box. The conditional reduction by `0x1b` when bit 8 sets is
done by a **data-independent mask** (`mask = 0 − bit`), not a branch, so the body
is constant-time and uses only `recogBin`/`recogShift` heads (no `Not`, no
control flow). This is exactly `UOV.VerifyEmit.gf256MulInline`'s arithmetic,
now driven through the verified compiler-from-hax front rather than the owned
x86 backend.

## Method (mirrors `CompileFromHaxAscon`)

The source is a fully let-normalized `ImpExpr` (one operator per `letBind`, all
arguments atoms or earlier locals); the constants `0`, `1`, `0xff`, `0x1b` are
materialized into locals (`zero`, `one`, `m8`, `poly`) because the front rejects a
bare literal as a binary-op operand. The shift counts are literal `.int` args of
`Shr`/`Shl`. `gf256MulSrc_denoteScalar = gf256MulSpec` closes by `rfl` (the spec
is stated in the **exact** masked shift-and-XOR form the source emits, dodging the
O(n²) simp-rewrite wall — as the Ascon S-box did); `gf256Mul_compileFromHax_isSome`
by `native_decide`; `gf256Mul_compiles` routes the source-spec through
`compileFromHax_meets_spec`. The two-input valuation is `![a, b]` (`w = 32`,
`nIn = 2`), the result is the GF(256) product in the low byte.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §0  The closed form the source computes

`gf256MulSpec` is the bit-serial GF(256) product written in the exact masked
shift-and-XOR form the let-normalized source emits, so the source denotation
matches it definitionally. The accumulator `p` and the shifted operand `sh`
thread through the eight bit-steps; the conditional reduce by `0x1b` is the
`(0 - carry-bit) & 0x1b` mask. All arithmetic is at width 32, with the field
elements living in the low byte (`& 0xff` after each `xtime` and at the end). -/

/-- One bit-step `k`: fold `sh` into the accumulator `p` iff bit `k` of `b` is set
    (via the `0 - bit` mask), then `xtime(sh)` (left-shift, reduce by `0x1b` mask
    on carry-out of bit 7). Returns the updated `(p, sh)`. This is the exact masked
    arithmetic the source's `letBind` chain for step `k` computes. -/
def gf256Step (b : BitVec 32) (k : Nat) (p sh : BitVec 32) : BitVec 32 × BitVec 32 :=
  let bit   := (b >>> k) &&& (1 : BitVec 32)
  let mask  := (0 : BitVec 32) - bit
  let p'    := p ^^^ (sh &&& mask)
  let cy    := (sh >>> (7 : Nat)) &&& (1 : BitVec 32)
  let cmask := (0 : BitVec 32) - cy
  let red   := cmask &&& (0x1b : BitVec 32)
  let sh'   := ((sh <<< (1 : Nat)) &&& (0xff : BitVec 32)) ^^^ red
  (p', sh')

/-- The GF(256) product `a · b` (AES field) as the bit-serial closed form, low byte.
    Eight applications of `gf256Step`, seeded `p = 0`, `sh = a & 0xff`, masked to a
    byte at the end. Stated as a plain `def` so the spec is explicit and auditable. -/
def gf256MulSpec (a b : BitVec 32) : BitVec 32 :=
  let sh0 := a &&& (0xff : BitVec 32)
  let s0 := gf256Step b 0 0 sh0
  let s1 := gf256Step b 1 s0.1 s0.2
  let s2 := gf256Step b 2 s1.1 s1.2
  let s3 := gf256Step b 3 s2.1 s2.2
  let s4 := gf256Step b 4 s3.1 s3.2
  let s5 := gf256Step b 5 s4.1 s4.2
  let s6 := gf256Step b 6 s5.1 s5.2
  let s7 := gf256Step b 7 s6.1 s6.2
  s7.1 &&& (0xff : BitVec 32)

/-! ## §1  The let-normalized source

The constants `0`, `1`, `0xff`, `0x1b` are materialized into the locals `zero`,
`one`, `m8`, `poly` (a bare literal cannot be a binary-op operand in the front).
Each bit-step contributes one `letBind` per operator; the accumulator `p` and the
shifted operand `sh` are rebound each step (`pK`, `shK`). Parameters
`["a","b"]` (`nIn = 2`; `a = inpGet I 0`, `b = inpGet I 1`). -/

/-- The let-normalized bit-step builder: from current accumulator local `pIn` and
    shifted-operand local `shIn`, bind step `k`'s intermediates and continue with
    `cont` (which reads the new `pOut`/`shOut` locals). Uses the materialized
    constant locals `one`/`zero`/`m8`/`poly`. -/
def stepSrc (k : Nat) (pIn shIn pOut shOut : String) (cont : ImpExpr) : ImpExpr :=
  -- bit := (b >> k) & 1
  .letBind ("bsh" ++ pOut) (.app "Shr" [.var "b", .lit (.int k)])
  (.letBind ("bit" ++ pOut) (.app "BitAnd" [.var ("bsh" ++ pOut), .var "one"])
  -- mask := 0 - bit
  (.letBind ("mask" ++ pOut) (.app "wrapping_sub" [.var "zero", .var ("bit" ++ pOut)])
  -- p := p ^ (sh & mask)
  (.letBind ("sm" ++ pOut) (.app "BitAnd" [.var shIn, .var ("mask" ++ pOut)])
  (.letBind pOut (.app "BitXor" [.var pIn, .var ("sm" ++ pOut)])
  -- cy := (sh >> 7) & 1 ; cmask := 0 - cy ; red := cmask & 0x1b
  (.letBind ("csh" ++ pOut) (.app "Shr" [.var shIn, .lit (.int 7)])
  (.letBind ("cy" ++ pOut) (.app "BitAnd" [.var ("csh" ++ pOut), .var "one"])
  (.letBind ("cmask" ++ pOut) (.app "wrapping_sub" [.var "zero", .var ("cy" ++ pOut)])
  (.letBind ("red" ++ pOut) (.app "BitAnd" [.var ("cmask" ++ pOut), .var "poly"])
  -- sh := ((sh << 1) & 0xff) ^ red
  (.letBind ("shl" ++ pOut) (.app "Shl" [.var shIn, .lit (.int 1)])
  (.letBind ("shm" ++ pOut) (.app "BitAnd" [.var ("shl" ++ pOut), .var "m8"])
  (.letBind shOut (.app "BitXor" [.var ("shm" ++ pOut), .var ("red" ++ pOut)])
   cont)))))))))))

/-- The full GF(256) multiply source: materialize the constants, seed `p0 = 0`
    (reusing `zero`) and `sh0 = a & 0xff`, run the eight bit-steps, mask the result
    to a byte, and return it. -/
def gf256MulSrc : ImpExpr :=
  .letBind "zero" (.lit (.int 0))
  (.letBind "one" (.lit (.int 1))
  (.letBind "m8" (.lit (.int 0xff))
  (.letBind "poly" (.lit (.int 0x1b))
  (.letBind "sh0" (.app "BitAnd" [.var "a", .var "m8"])
   (stepSrc 0 "zero" "sh0" "p0" "shA"
   (stepSrc 1 "p0" "shA" "p1" "shB"
   (stepSrc 2 "p1" "shB" "p2" "shC"
   (stepSrc 3 "p2" "shC" "p3" "shD"
   (stepSrc 4 "p3" "shD" "p4" "shE"
   (stepSrc 5 "p4" "shE" "p5" "shF"
   (stepSrc 6 "p5" "shF" "p6" "shG"
   (stepSrc 7 "p6" "shG" "p7" "shH"
   (.letBind "out" (.app "BitAnd" [.var "p7", .var "m8"])
    (.var "out")))))))))))))) -- closes 4 const-lets + sh0 + 8 steps + out-let

/-- The parameter list. -/
abbrev gf256Params : List String := ["a", "b"]

/-! ## §2  Source-spec agreement (the source denotes to the closed form)

The let-normalized body and `gf256MulSpec`/`gf256Step` both reduce
definitionally — the materialized-constant locals and the masked shift-and-XOR
form line up arm-for-arm — so the source-spec is `rfl` (the eight-step tree needs
the raised heartbeat budget, as the Ascon S-box did). -/
set_option maxHeartbeats 4000000 in
theorem gf256MulSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar gf256Params I gf256MulSrc (fun _ => none)
      = some (gf256MulSpec (inpGet I 0) (inpGet I 1)) := by
  rfl

/-! ## §3  Compilation succeeds (`native_decide`) -/

theorem gf256Mul_compileFromHax_isSome :
    (compileFromHax (w := 32) (nIn := 2) gf256Params gf256MulSrc).isSome := by
  native_decide

/-! ## §4  The GF(256) multiply emitted by the verified compiler -/

/-- **UOV GF(256) field multiply emitted by the verified compiler.** There is a
    compiled `Com jasminDialect` `prog` with
    `compileFromHax ["a","b"] gf256MulSrc = some prog`, and for every `(a, b)`,
    `prog`'s `BitVec 32` denotation (under the input valuation `![a, b]`) is exactly
    the bit-serial GF(256) product `gf256MulSpec a b` (AES field, low byte). Routed
    through the C3 per-primitive obligation `compileFromHax_meets_spec`. This is a
    C4 fan-out to the UOV GF(256) primitive, reusing the SHA-256/Ascon
    `BitXor`/`BitAnd`/`Shl`/`Shr`/`wrapping_sub` recognizers with no front change;
    it is the constant-time arithmetic of `UOV.VerifyEmit.gf256MulInline`,
    driven through the compiler-from-hax front. -/
theorem gf256Mul_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 32 2 []) (rW 32)),
      compileFromHax (w := 32) (nIn := 2) gf256Params gf256MulSrc = some prog ∧
      ∀ (a b : BitVec 32),
        prog.denote (inputValuation 32 2 ![a, b]) = gf256MulSpec a b := by
  set prog := (compileFromHax (w := 32) (nIn := 2) gf256Params gf256MulSrc).get
    gf256Mul_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 32) (nIn := 2) gf256Params gf256MulSrc = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro a b
  have hspec : ImpExpr.denoteScalar gf256Params ![a, b] gf256MulSrc (fun _ => none)
      = some (gf256MulSpec a b) := by
    have h := gf256MulSrc_denoteScalar (nIn := 2) ![a, b]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 32) (nIn := 2) gf256Params
    ![a, b] gf256MulSrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxUovGf256
