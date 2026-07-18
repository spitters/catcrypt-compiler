/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# A GENUINE whole-kernel ChaCha20 double-round, front-sourced without `native_decide`

This module front-sources the FULL ChaCha20 double-round (RFC 8439 §2.3 — the
eight quarter-rounds of one inner-loop iteration: four column rounds then four
diagonal rounds over the 16-word state) as a `List (String × SExpr)` at width 32,
each `RScalarSetExpr`-style statement `dst := e` a single primitive word op in the
covered alphabet (`+`, `^`, and `rotl32` as the disjoint shift pair
`(x << k) ^ (x >> (32-k))`). This is the ACTUAL deployed ChaCha arithmetic — the
canonical `a += b; d ^= a; d <<<= 16; …` op sequence — not a representative
fragment.

The whole double round is 96 primitive statements. Its dialect `isSome` closes
through the keystone `ScalarSetSeqSequencer.lowerScalarSetSeqW_isSome` fed a
`SeqCovers` derivation (a chain of one-statement `rfl`s, built here by a
`refine .cons _ _ _ rfl ?_` loop). Its jasmin `isSome` — reaching owned x86 —
closes through `ScalarSetSeqSequencer.seqProg_jasmin_isSome`, i.e. the
`SeqCovers`/`Com` inductions of the sequencer, NOT a monolithic `native_decide`
over the 96-node `Com` (which OOMs). Axiom footprint `[propext, Quot.sound]`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ChaChaWholeKernelFront

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The ChaCha state, the rotate, and the quarter-round -/

/-- `rotl32(x, k)` as the front-expressible disjoint shift pair
    `(x << k) ^ (x >> (32 - k))` (at width 32 the halves are disjoint, so `^`
    reassembles the rotate — proved universally in
    `ScalarSExprWidth32Prototype.rotl32_*`). -/
def rotl (x : SExpr) (k : Nat) : SExpr :=
  .SXor (.SShl x (.SLit k)) (.SShr x (.SLit (32 - k)))

/-- One ChaCha20 quarter-round `QR(a,b,c,d)` (RFC 8439 §2.1) as 12 primitive
    `dst := e` statements — the canonical `a += b; d ^= a; d <<<= 16; …` sequence,
    with each rotate a `rotl` step. Destinations are the four state-word slot
    names; each RHS reads the CURRENT (SSA-aliased) binding of those names. -/
def qr (a b c d : String) : List (String × SExpr) :=
  [ (a, .SAdd (.SVar a) (.SVar b)),
    (d, .SXor (.SVar d) (.SVar a)),
    (d, rotl (.SVar d) 16),
    (c, .SAdd (.SVar c) (.SVar d)),
    (b, .SXor (.SVar b) (.SVar c)),
    (b, rotl (.SVar b) 12),
    (a, .SAdd (.SVar a) (.SVar b)),
    (d, .SXor (.SVar d) (.SVar a)),
    (d, rotl (.SVar d) 8),
    (c, .SAdd (.SVar c) (.SVar d)),
    (b, .SXor (.SVar b) (.SVar c)),
    (b, rotl (.SVar b) 7) ]

/-- The 16 state words, all `.sword 32`. -/
def chachaΓ : Ctx :=
  [.sword 32, .sword 32, .sword 32, .sword 32, .sword 32, .sword 32, .sword 32,
   .sword 32, .sword 32, .sword 32, .sword 32, .sword 32, .sword 32, .sword 32,
   .sword 32, .sword 32]

/-- `VarMap` binding the 16 words `w0 … w15` (`w0 = .here`). -/
def chachaVM : VarMap chachaΓ :=
  (((((((((((((((VarMap.empty.bind "w15").bind "w14").bind "w13").bind "w12").bind
    "w11").bind "w10").bind "w9").bind "w8").bind "w7").bind "w6").bind "w5").bind
    "w4").bind "w3").bind "w2").bind "w1").bind "w0"

/-- The FULL ChaCha20 double round: four column rounds then four diagonal rounds
    (RFC 8439 §2.3), 8 quarter-rounds × 12 statements = 96 primitive ops. -/
def dblRound : List (String × SExpr) :=
  qr "w0" "w4" "w8"  "w12" ++ qr "w1" "w5" "w9"  "w13" ++
  qr "w2" "w6" "w10" "w14" ++ qr "w3" "w7" "w11" "w15" ++
  qr "w0" "w5" "w10" "w15" ++ qr "w1" "w6" "w11" "w12" ++
  qr "w2" "w7" "w8"  "w13" ++ qr "w3" "w4" "w9"  "w14"

/-! ## 2. The whole double round covers — a `refine .cons _ _ _ rfl ?_` loop

Each head fact is a ONE-STATEMENT `rfl` (`lowerSExprW 32 <vm-here> <cnt> <rhs> =
some …`, the witnesses solved by unification), never a whole-`Com` normalisation.
The loop threads the growing `VarMap` through the 96 statements. -/

/-- Per-statement coverability for the whole 96-statement double round. -/
theorem dblRound_covers : SeqCovers 32 chachaVM 0 dblRound := by
  unfold dblRound qr rotl
  repeat' first
    | exact SeqCovers.nil
    | refine SeqCovers.cons _ _ _ rfl ?_

/-! ## 3. The whole double-round `isSome` — dialect AND jasmin, no `native_decide` -/

/-- The WHOLE 96-statement double round lowers to a `Com catCryptDialect` prefix,
    through the keystone `lowerScalarSetSeqW_isSome` — composing the per-statement
    `rfl` facts by INDUCTION over `dblRound_covers`. NO `native_decide`. -/
theorem dblRound_isSome : (lowerScalarSetSeqW 32 chachaVM 0 dblRound).isSome :=
  lowerScalarSetSeqW_isSome 32 chachaVM 0 dblRound dblRound_covers

/-- The whole-kernel double-round program: the 96-statement sequencer prefix
    closed with `ret w0` (returns one of the 16 output words; the prefix computes
    all 16). -/
def dblRoundProg : Option (Com catCryptDialect chachaΓ (.sword 32)) :=
  seqProg 32 chachaVM dblRound "w0"

/-- The whole double-round program resolves (its final slot `w0` is a `.sword 32`
    slot, and the 96-node `ComCont` prefix closes with `ret`). -/
theorem dblRoundProg_isSome : dblRoundProg.isSome := by
  rfl

/-- **The whole ChaCha20 double round reaches owned x86.** The 96-node `Com`
    lowers on to `Com jasminDialect` through `cryptoDialectToJasminCom`, closed by
    the `SeqCovers`/`Com` INDUCTIONS of the sequencer (`seqProg_jasmin_isSome`),
    NOT a monolithic `native_decide` over the whole kernel. -/
theorem dblRound_jasmin_isSome :
    (dblRoundProg.bind DialectToJasminCom.cryptoDialectToJasminCom).isSome :=
  seqProg_jasmin_isSome 32 chachaVM dblRound "w0" dblRound_covers dblRoundProg_isSome

end CatCrypt.Crypto.SecureCompilation.Dialects.ChaChaWholeKernelFront
