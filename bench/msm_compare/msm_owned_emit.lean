/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# `ec_msm` — front-compiled owned x86-64 emit of the Z/23 multi-scalar multiplication

The MSM `Σ_{i=0}^{7} k_i · P_i` over the toy curve group `y² = x³ + x + 1` over
`Z/23` (cyclic of order 28, generator `G = (0,1)`; `ec_ref.h`), emitted as a
single owned x86-64 leaf through the rolled-loop front
(`TranslateDialectRolledLoop.rolledForLoopN` /
`rolledForLoopNCont` → `cryptoDialectToJasminCom` → `ComL.forLoopN` →
`ComL.toLprogPhysAbi` → `renderLprogAtt`). The whole body — the accumulator
fold loop and the result-point epilogue — is covered `LowCT`
(`RArrLoad`/`RScalarSetExpr`/`RArrStore`) pushed through the front; no
hand-authored `Com`/`Lcmd`/`.s`.

## The dlog-space reduction (point-add and scalar-mul become integer mod-28)

Every finite point is `m·G` for a unique discrete log `m ∈ 1..27`; the identity
(infinity) is `m = 0`. The running accumulator is carried by its dlog
`accM ∈ 0..27` (`accM = 0` is infinity):

* `point-add`  `accM ↦ (accM + termM) mod 28`   (one conditional subtract),
* `scalar-mul` `termM = (k_i · dlog(P_i)) mod 28` (Barrett mod-28),

and the final point is read once from the `POW` table at the end. `dlog(P_i)` is
`DLOG[23·x_i + y_i]`. Infinity inputs (`x_i = y_i = 0xff`, index `6120`) and any
out-of-curve index map to `0` inside `DLOG`, so no in-kernel infinity branch is
needed (the table absorbs it; `POW[0] = (0xff,0xff)` encodes infinity at the
output).

## The two front-compiled loops

`ecMsmComL` is a `rolledForLoopNCont` (the accumulator fold, `L = 8` trips, one
body copy, a real back-edge) whose continuation is a second `rolledForLoopN`
(the epilogue, `2` trips, one body copy) writing the two output bytes:

* fold body over `[accM, idx, ks, ps, DLOG]`: gather `ks[i]`, `ps[2i]`,
  `ps[2i+1]`, gather `DLOG[23·px+py]`, reg×reg multiply `k·j`, Barrett-reduce
  mod 28, accumulate mod 28 into the `.reg 64` accumulator `accM`;
* epilogue body over `[out, k, accM, POW]`: gather `POW[accM]`, extract byte `k`
  (`(POW[accM] >> 8k) & 0xff`), store to `out[k]`.

## ABI (SysV, word model)

`ec_msm(out, ks, ps, DLOG, zero, POW)` — RDI=out, RSI=ks, RDX=ps, RCX=DLOG,
R8=zero, R9=POW, as read off the rendered `gen_com/msm.s` (the accumulator-seed
`zero` word precedes `POW` in the emitted parameter order). The two tables and
the three buffers are `uint64_t*` (one word per scalar / coordinate / table
entry). `zero` seeds the `.reg 64` accumulator (the front's loop seed is an
in-scope variable, so the caller passes a zeroed word). The word-per-value
layout is the front's memref model; byte-identity with the previous byte-ABI
leaf is not preserved (denotational equality is the correctness criterion).

## Correctness

`ecMsm_denote_*` (`#guard`) pin `ComL.denote ecMsmComL` at deterministic sample
tables to the independent dlog-space fold reference `outSpec` — the front-emitted
loop computes exactly `out = split(POW[Σ (k_i · DLOG[idx(P_i)]) mod 28])`. The
structural loop-wrapper denotation `TranslateDialectRolledLoop.rolledForLoopN_denote`
carries each rolled loop's denotation to its `JLoopBodyN.denote` fold.

Invoke (emit the `.s`):  lake env lean --run bench/msm_compare/msm_owned_emit.lean
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.MsmZ23Owned

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 0. Dimensions (word counts) -/

/-- Number of MSM terms. -/
def L : Nat := 8
/-- Scalar buffer word count (`ks[0..7]`). -/
def Lks : Nat := 8
/-- Point buffer word count (`ps[2i] = x_i`, `ps[2i+1] = y_i`). -/
def Lps : Nat := 16
/-- `DLOG` table word count: `23·255 + 255 + 1`, covering every byte-valued
    `23·x + y` index (infinity `x = y = 0xff` lands at `6120 ↦ 0`). -/
def Ldlog : Nat := 6121
/-- `POW` table word count (one packed `x | y<<8` word per dlog in `0..27`). -/
def Lpow : Nat := 28
/-- Output buffer word count (`out[0] = x`, `out[1] = y`). -/
def Lout : Nat := 2

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ## 1. The accumulator-fold loop body (covered `LowCT`)

Body context `Γbody = [accM, idx, ks, ps, DLOG]` (accumulator `accM`; loop index
`idx`; invariants `ks`, `ps`, `DLOG`). One trip:
`accM ↦ (accM + (ks[idx] · DLOG[23·ps[2·idx] + ps[2·idx+1]]) mod 28) mod 28`,
Barrett-reduced (`q = (v·292) >> 13`, valid for `v < 8192 = 28·256`; one
conditional subtract each for the reduce and the accumulate, both sums `< 56`).
The conditional subtract is branch-free: `(27 - r) >> 63` is `1` exactly when the
wrapping difference is negative, i.e. `r ≥ 28`. -/
def foldBody : LowCT := seqAll [
  .RArrLoad ⟨"kb", .TU64⟩ ⟨"ks", .TBytes (8 * Lks)⟩ "idx",
  .RScalarSetExpr "ix2" (.SShl (.SVar "idx") (.SLit 1)),
  .RArrLoad ⟨"px", .TU64⟩ ⟨"ps", .TBytes (8 * Lps)⟩ "ix2",
  .RScalarSetExpr "ix2p1" (.SAdd (.SVar "ix2") (.SLit 1)),
  .RArrLoad ⟨"py", .TU64⟩ ⟨"ps", .TBytes (8 * Lps)⟩ "ix2p1",
  .RScalarSetExpr "idxd" (.SAdd (.SMul (.SVar "px") (.SLit 23)) (.SVar "py")),
  .RArrLoad ⟨"j", .TU64⟩ ⟨"DLOG", .TBytes (8 * Ldlog)⟩ "idxd",
  .RScalarSetExpr "m" (.SMul (.SVar "kb") (.SVar "j")),
  .RScalarSetExpr "q" (.SShr (.SMul (.SVar "m") (.SLit 292)) (.SLit 13)),
  .RScalarSetExpr "r" (.SSub (.SVar "m") (.SMul (.SVar "q") (.SLit 28))),
  .RScalarSetExpr "ge" (.SShr (.SSub (.SLit 27) (.SVar "r")) (.SLit 63)),
  .RScalarSetExpr "term" (.SSub (.SVar "r") (.SMul (.SLit 28) (.SVar "ge"))),
  .RScalarSetExpr "s" (.SAdd (.SVar "accM") (.SVar "term")),
  .RScalarSetExpr "ge2" (.SShr (.SSub (.SLit 27) (.SVar "s")) (.SLit 63)),
  .RScalarSetExpr "accM" (.SSub (.SVar "s") (.SMul (.SLit 28) (.SVar "ge2"))) ]

/-- Fold-body context `[accM, idx, ks, ps, DLOG]`. -/
def Γfold : Ctx := [.sword 64, .sword 64, .memref Lks, .memref Lps, .memref Ldlog]

/-- Fold-body VarMap (bind deepest-first so `accM` lands at `.here`). -/
def vmFold : VarMap Γfold :=
  (((((VarMap.empty.bind (t := .memref Ldlog) "DLOG").bind
      (t := .memref Lps) "ps").bind
      (t := .memref Lks) "ks").bind
      (t := .sword 64) "idx").bind (t := .sword 64) "accM")

/-! ## 2. The epilogue loop body (covered `LowCT`)

Body context `[out, k, accM, POW]`. One trip writes output word `k`:
`out[k] = (POW[accM] >> (8·k)) & 0xff`. `accM` (the fold result) is a loop
invariant read as the `POW` gather index; `out` is the accumulator memref. -/
def epiBody : LowCT := seqAll [
  .RArrLoad ⟨"pw", .TU64⟩ ⟨"POW", .TBytes (8 * Lpow)⟩ "accM",
  .RScalarSetExpr "v"
    (.SAnd (.SShr (.SVar "pw") (.SMul (.SLit 8) (.SVar "idx"))) (.SLit 255)),
  .RArrStore ⟨"out", .TBytes (8 * Lout)⟩ "idx" ⟨"v", .TU64⟩ ]

/-- Epilogue-body VarMap for `[out, idx, accM, POW]`. -/
def vmEpi : VarMap [CryptoTy.memref Lout, .sword 64, .sword 64, .memref Lpow] :=
  ((((VarMap.empty.bind (t := .memref Lpow) "POW").bind
      (t := .sword 64) "accM").bind
      (t := .sword 64) "idx").bind (t := .memref Lout) "out")

/-! ## 3. The front-compiled `ec_msm`

Outer context `[POW, zero, DLOG, ps, ks, out]` — jasmin types. The fold loop's
accumulator seed is `zero` (a `.reg 64` argument the caller passes as `0`); the
epilogue runs as the fold's continuation, with the final `accM` bound at `.here`
above the outer slots.

The physical ABI is the root-first (reverse) reading of `Γouter`: argument slot
`j` (`abiArgs[j]`) is the context entry at de Bruijn `Γouter.length - 1 - j`
(`resolveVar` in `JasminLprogExport`). Reversing `[POW, zero, DLOG, ps, ks, out]`
gives `(out, ks, ps, DLOG, zero, POW)` = RDI/RSI/RDX/RCX/R8/R9, matching the
`ec_msm` C signature. `zero` sits at de Bruijn `1` so its slot is `4` (R8), the
register the caller passes the accumulator seed in; the array invariants `ks`,
`ps`, `DLOG` occupy the consecutive slots `1..3` (RSI/RDX/RCX). -/
def Γouter : Ctxt jasminDialect :=
  [.stackArr 64 Lpow, .reg 64, .stackArr 64 Ldlog, .stackArr 64 Lps,
   .stackArr 64 Lks, .stackArr 64 Lout]

/-- The epilogue loop over `Γouter` extended with the final `accM` (`.reg 64`) at
    `.here`; positions there are `accM=0, POW=1, zero=2, DLOG=3, ps=4, ks=5,
    out=6`. -/
def epiComL : Option (ComL (mapTy (CryptoTy.sword 64) :: Γouter) (.stackArr 64 Lout)) :=
  rolledForLoopN (Γouter := mapTy (CryptoTy.sword 64) :: Γouter) (accCTy := .memref Lout)
    (invCTys := [.sword 64, .memref Lpow])
    2 vmEpi "out" epiBody
    (init := .there (.there (.there (.there (.there (.there .here))))))   -- out
    (invs := .cons .here (.cons (.there .here) .nil))                     -- accM, POW

/-- The whole `ec_msm`: the `L`-trip accumulator fold with the epilogue loop as
    its continuation. Both loops carry a real back-edge (one body copy each);
    `none` only if the front declines. -/
def ecMsmComL : Option (ComL Γouter (.stackArr 64 Lout)) :=
  match epiComL with
  | some epi =>
      rolledForLoopNCont (Γouter := Γouter) (accCTy := .sword 64)
        (invCTys := [.memref Lks, .memref Lps, .memref Ldlog])
        L vmFold "accM" foldBody
        (init := .there .here)                                           -- zero
        (invs := .cons (.there (.there (.there (.there .here))))          -- ks
          (.cons (.there (.there (.there .here)))                        -- ps
            (.cons (.there (.there .here)) .nil)))                       -- DLOG
        (cont := epi)
  | none => none

/-! ## 4. Independent dlog-space reference + denotation gates

The reference is the direct dlog-space fold over the sample tables, matching the
group law encoded by the driver's `DLOG`/`POW`. Deterministic pseudorandom
tables (`sd` a seed offset) stand in for real curve values; the front-emitted
loop must denote to the fold at each output word. -/

/-- Deterministic pseudorandom stream (Knuth multiplicative). -/
def rnd (sd i : Nat) : Nat := (2654435761 * (i + sd) + 88172645) % 4294967296

/-- Sample scalar `ks[i]` (byte-valued). -/
def sKs (sd i : Nat) : Nat := rnd (sd + 3) i % 256
/-- Sample coordinate word `ps[i]` (in `Z/23`). -/
def sPs (sd i : Nat) : Nat := rnd (sd + 5) i % 23
/-- Sample `DLOG[i]` (in `0..27`). -/
def sDlog (sd i : Nat) : Nat := rnd (sd + 7) i % 28
/-- Sample `POW[i]` (a packed `x | y<<8` word). -/
def sPow (sd i : Nat) : Nat := rnd (sd + 11) i % 65536

/-- The final dlog after the `L`-term fold on sample seed `sd`. -/
def accSpec (sd : Nat) : Nat :=
  (List.range L).foldl (fun acc i =>
    (acc + (sKs sd i * sDlog sd (23 * sPs sd (2 * i) + sPs sd (2 * i + 1))) % 28) % 28) 0

/-- Output word `k` of the reference: byte `k` of `POW[accSpec]`. -/
def outSpec (sd k : Nat) : Nat := (sPow sd (accSpec sd) >>> (8 * k)) &&& 255

/-- The outer valuation `[POW, zero, DLOG, ps, ks, out-seed]` at sample seed
    `sd`. `zero`/`out-seed` are `0`. -/
def valOf (sd : Nat) : Ctxt.Valuation Γouter :=
  .cons (fun i => BitVec.ofNat 64 (sPow sd i.val))
    (.cons (0 : BitVec 64)
      (.cons (fun i => BitVec.ofNat 64 (sDlog sd i.val))
        (.cons (fun i => BitVec.ofNat 64 (sPs sd i.val))
          (.cons (fun i => BitVec.ofNat 64 (sKs sd i.val))
            (.cons (fun _ => (0 : BitVec 64)) .nil)))))

/-- The denoted output row at sample seed `sd`. -/
def denRow (sd : Nat) : Option (List Nat) :=
  ecMsmComL.map (fun c =>
    (List.finRange Lout).map (fun i => (ComL.denote c (valOf sd) i).toNat))

-- The `ec_msm` front-compiles.
#guard ecMsmComL.isSome

-- denote = dlog-space MSM reference (seed 0).
#guard denRow 0 == some [outSpec 0 0, outSpec 0 1]

-- denote = dlog-space MSM reference (seed 100), same emitted program.
#guard denRow 100 == some [outSpec 100 0, outSpec 100 1]

/-! ## 5. Owned `.s` render + emit -/

/-- The AT&T `.s` for `ec_msm`, or `none` if the front declines. -/
def ecMsmAsm : Option String :=
  ecMsmComL.map (fun c =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
      (ComL.toLprogPhysAbi c "ec_msm" (argName 0)
        [argName 1, argName 2, argName 3, argName 4, argName 5]
        (fun _ => none) (fun _ => none)
        ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]
        [64, 64, 64, 64, 64, 64]))

/-- Write the front-compiled owned `ec_msm` `.s`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/msm_compare/gen_com"
  match ecMsmAsm with
  | some asm =>
      IO.FS.writeFile "bench/msm_compare/gen_com/msm.s" asm
      IO.println s!"front-compiled emit OK : bench/msm_compare/gen_com/msm.s \
        ({asm.toUTF8.size} bytes, symbol ec_msm, rolled, no jasminc, no hand Com/Lcmd)"
  | none => throw (IO.userError "front-compile of ec_msm failed")

end CatCrypt.Crypto.Pairing.MsmZ23Owned

/-- Entry point for `lake env lean --run bench/msm_compare/msm_owned_emit.lean`. -/
def main : IO Unit := CatCrypt.Crypto.Pairing.MsmZ23Owned.emit
