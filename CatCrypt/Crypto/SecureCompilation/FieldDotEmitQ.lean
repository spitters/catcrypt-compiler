/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
public import CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Byte-correct 4-term dot product over `F_q` (`q = 3329`), FRONT-COMPILED, OWNED x86

A 4-term dot product `a0·b0 + a1·b1 + a2·b2 + a3·b3` over the prime field
`F_q`, `q = 3329` (the ML-KEM modulus), sourced through the verified front —
NO hand-built `Com` anywhere — and rendered to AT&T x86-64 `.s` through the
owned linear backend with NO jasminc and NO hand-authored assembly:

```
  dotBody (LowCT: RScalarSetExpr Barrett/csub word math over the 8 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  dotQCom : Com jasminDialect inCtxt r64
    --(Com.toLprogPhysAbi, owned RA + 2-address)-->  Lprog
    --(LprogAsmPrinter.renderLprogAtt)-->  gen_com/dot_q3329.s
```

## The Barrett mul-reduce and csub add (`q = 3329`, mirrors `MlkemNttFieldEmit`)

The jasmin word alphabet has no `div`/`mod`, so `(a·b) % q` is a Barrett reduce
with the precomputed constant `m = ⌊2^24 / q⌋ = 5039`:

```
   qhat := (r · 5039) >>> 24      -- quotient estimate, exact to ±1 over [0, q²)
   rem  := r − qhat·q             -- remainder in [0, 2q)
   condSub3329(rem)               -- one conditional subtract canonicalises
```

and the csub itself (`q = 3329`, used by both the Barrett tail and the field add):

```
   t    := x − 3329
   x'   := t + (3329 & (0 − (t >>> 63)))    -- (x ≥ q ? x−q : x), branch-free
```

Each step lowers to a `regArith` `mul`/`add`/`sub`/`and` over `reg 64`,
`regConst` literals, and immediate-count shifts — the dialect's straight-line
alphabet, no `Jcc`, no leaf call.

Each intermediate stays in range: inputs are canonical residues `< q`, so every
`mul` product is `< q² = 11 082 241 < 2^24` (Barrett-valid). Each product `aᵢ·bᵢ`
is canonicalised to `< q` by its own Barrett tail before being summed, and every
`add` operand pair (`acc < q` plus a canonical product `< q`) sums to `< 2q`, so
one csub canonicalises. So the kernel computes
`(a0·b0 + a1·b1 + a2·b2 + a3·b3) mod q` exactly.

## ABI (the C caller's contract, unchanged)

```c
extern void dot_q3329(uint64_t *out, const uint64_t *inp);
//   inp[0..3]=a0,a1,a2,a3   inp[4..7]=b0,b1,b2,b3  (canonical residues in [0,q))
//   out[0] = (a0*b0 + a1*b1 + a2*b2 + a3*b3) mod 3329
```

`RDI = out`, `RSI = inp` (the SysV 2-pointer ABI `comToLfundefPhysAbi` wraps).
`abiW := 64`: each load is a `movq inp(%rsi,…), %work`, the store a `movq
%work, out(%rdi)`. The reduce constants are `regConst` immediates (front `SLit`),
not loaded — the input context is exactly the 8 real input words.

## What is proved vs KAT-gated

* `dotQCom` is FRONT-GENERATED (`translateDialectControl` +
  `cryptoDialectToJasminCom`), never hand-built; the front translates and
  lowers end-to-end (`dotLowered_isSome`).
* `dot_denote_spec` — the front program's denotation equals the INDEPENDENT
  plain-`Nat` `% 3329` stepwise dot reference `dotNatRef` on the 5 KAT vectors
  plus 100 generated vectors (reducing cases included), by `native_decide`.
* `mulQW_eq_mkMulW` / `csub3329W_eq_mkCsubW` / `addQW_eq_mkAddW` — the per-op
  word functions the LowCT body computes are DEFINITIONALLY the
  `MlkemNttFieldEmit` word blocks (`rfl`); composed with `mkMulW_realizes` /
  `mkAddW_realizes` that gives the field-op realization under the canonical
  encoding `mkEnc` (§6).
* Structural gates: every lowered binding is pure scalar arith
  (`dot_is_purearith_only`); the last binding is the output copy
  (`dot_last_binding_is_copy`).
* The whole-`.s` tie is KAT-gated: `bench/field_kernel_compare/dot_q3329_kat.c`
  checks the rendered `.s` byte-for-byte against the independent `% 3329`
  reference (`make -C bench/field_kernel_compare dot-kat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldDotEmitQ

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (Com.toLprogPhysAbi InLoadMap OutStoreMap Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
  (mkCsubW mkBarrettW mkMulW mkAddW mkMulW_realizes mkAddW_realizes)
open CatCrypt.Crypto.SecureCompilation.FieldDescentMlkem (mkEnc Q)
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect (modMulF modAddF)

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- Number of input words loaded from `inp`: `a0..a3, b0..b3`. -/
abbrev NIN : Nat := 8

/-! ## 1. The straight-line `LowCT` body

The word arithmetic of every statement mirrors `MlkemNttFieldEmit.mkMulW`
(Barrett mul-reduce) / `mkAddW` (csub add), expressed as `RScalarSetExpr`
chains over named slots. The reduce constants `3329, 5039` and the shift
amounts `24, 63` are `SLit` literals (lowering to `regConst` / immediate-count
shifts). -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- The branch-free conditional subtract into `dst` (correct for `src < 2q`):
    `dst_s := src − 3329;  dst := dst_s + (3329 & (0 − (dst_s >>> 63)))` —
    word-for-word `MlkemNttFieldEmit.mkCsubW`. -/
def csubStmts (dst src : String) : List LowCT := [
  .RScalarSetExpr (dst ++ "_s") (.SSub (.SVar src) (.SLit 3329)),
  .RScalarSetExpr dst
    (.SAdd (.SVar (dst ++ "_s"))
      (.SAnd (.SLit 3329)
        (.SSub (.SLit 0) (.SShr (.SVar (dst ++ "_s")) (.SLit 63))))) ]

/-- `dst := (a · b) mod q`: schoolbook product, Barrett quotient estimate
    `qhat = (x·5039) >>> 24`, remainder `x − qhat·3329 ∈ [0, 2q)`, one csub —
    word-for-word `MlkemNttFieldEmit.mkMulW`. Correct for `a·b < q²`. -/
def mulModStmts (dst a b : String) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "_x") (.SMul (.SVar a) (.SVar b)),
    .RScalarSetExpr (dst ++ "_q")
      (.SShr (.SMul (.SVar (dst ++ "_x")) (.SLit 5039)) (.SLit 24)),
    .RScalarSetExpr (dst ++ "_r")
      (.SSub (.SVar (dst ++ "_x"))
        (.SMul (.SVar (dst ++ "_q")) (.SLit 3329))) ]
  ++ csubStmts dst (dst ++ "_r")

/-- `dst := (a + b) mod q`: `a + b` then one csub (`a + b < 2q`) —
    word-for-word `MlkemNttFieldEmit.mkAddW`. -/
def addModStmts (dst a b : String) : List LowCT :=
  .RScalarSetExpr (dst ++ "_u") (.SAdd (.SVar a) (.SVar b)) :: csubStmts dst (dst ++ "_u")

/-- The full dot-product body: the four Barrett-reduced products
    `m0..m3 = aᵢ·bᵢ mod q`, the left-fold csub-add accumulation
    `acc1 = m0+m1`, `acc2 = acc1+m2`, `acc3 = acc2+m3`, then the output copy
    `q0 := acc3` (lowering to exactly ONE binding — the last-binding output
    convention). -/
def dotBody : LowCT := seqAll (
  mulModStmts "m0" "a0" "b0" ++
  mulModStmts "m1" "a1" "b1" ++
  addModStmts "acc1" "m0" "m1" ++
  mulModStmts "m2" "a2" "b2" ++
  addModStmts "acc2" "acc1" "m2" ++
  mulModStmts "m3" "a3" "b3" ++
  addModStmts "acc3" "acc2" "m3" ++
  [.RScalarSetExpr "q0" (.SVar "acc3")])

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `a0`) is the context head, word `7` (= `b3`) the
deepest — input word `i` at De Bruijn index `i` (the 8-word
`[a0,a1,a2,a3,b0,b1,b2,b3]` ABI, exactly `inp[0..7]`). -/

/-- The source context: 8 `u64` scalar slots (the 8 real inputs). -/
def srcCtx : Ctx := List.replicate NIN (.sword 64)

/-- The source `VarMap`: word 7 (`b3`) bound first (deepest), word 0 (`a0`) last. -/
def srcVM : VarMap srcCtx :=
  (((((((VarMap.empty.bind "b3").bind "b2").bind "b1").bind
    "b0").bind "a3").bind "a2").bind "a1").bind "a0"

/-! ## 3. The front-emitted programs -/

/-- Push `dotBody` through the front and cap with `ret <name>`. `none` if the
    front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM dotBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted dot product, lowered to the jasmin dialect (capped at the
    output copy `q0`, whose binding is the `Com`'s last). -/
def dotLoweredOpt :=
  (frontComAt "q0").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem dotLowered_isSome : dotLoweredOpt.isSome := by native_decide

/-- The input context of the `Com`: the 8 `r64` input words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate NIN r64

/-- The jasmin-dialect dot-product `Com` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
def dotQCom : Com jasminDialect inCtxt r64 :=
  dotLoweredOpt.get dotLowered_isSome

/-! ## 4. The per-op word functions are the `MlkemNttFieldEmit` word blocks

`mulModStmts`/`addModStmts` compute, word-for-word, exactly the arithmetic of
`MlkemNttFieldEmit.mkMulW`/`mkAddW`. We make that precise by giving the closed
word functions the body realizes and proving they are DEFINITIONALLY the
`mkMulW`/`mkAddW`/`mkCsubW` blocks (`rfl`); composing with the proved
`mkMulW_realizes`/`mkAddW_realizes` field-op squares gives the field-spec tie
under the canonical encoding `mkEnc`. -/

/-- The csub word function the body computes (= `mkCsubW`). -/
def csub3329W (x : BitVec 64) : BitVec 64 :=
  let t := x - (3329 : BitVec 64)
  t + ((3329 : BitVec 64) &&& ((0 : BitVec 64) - (t >>> (63 : Nat))))

/-- The Barrett-reduce word function the body computes (= `mkBarrettW`). -/
def barrettW (r : BitVec 64) : BitVec 64 :=
  csub3329W (r - (((r * (5039 : BitVec 64)) >>> (24 : Nat)) * (3329 : BitVec 64)))

/-- The mul-step word function the body computes (= `mkMulW`). -/
def mulQW (a b : BitVec 64) : BitVec 64 := barrettW (a * b)

/-- The add-step word function the body computes (= `mkAddW`). -/
def addQW (a b : BitVec 64) : BitVec 64 := csub3329W (a + b)

/-- **The body's csub is exactly `MlkemNttFieldEmit.mkCsubW`** (`rfl`). -/
theorem csub3329W_eq_mkCsubW (x : BitVec 64) : csub3329W x = mkCsubW x := rfl

/-- **The body's Barrett reduce is exactly `MlkemNttFieldEmit.mkBarrettW`**. -/
theorem barrettW_eq_mkBarrettW (r : BitVec 64) : barrettW r = mkBarrettW r := rfl

/-- **The body's mul step is exactly `MlkemNttFieldEmit.mkMulW`**. -/
theorem mulQW_eq_mkMulW (a b : BitVec 64) : mulQW a b = mkMulW a b := rfl

/-- **The body's add step is exactly `MlkemNttFieldEmit.mkAddW`**. -/
theorem addQW_eq_mkAddW (a b : BitVec 64) : addQW a b = mkAddW a b := rfl

/-- **The mul step realizes the field multiply under `mkEnc`.** On canonical
    encodings of field elements, the Barrett product block equals `mkEnc (a·b)`.
    Direct from `mulQW_eq_mkMulW` + `MlkemNttFieldEmit.mkMulW_realizes`. -/
theorem mulQW_realizes (a b : ZMod Q) :
    mulQW (mkEnc a) (mkEnc b) = mkEnc (modMulF a b) := by
  rw [mulQW_eq_mkMulW]; exact mkMulW_realizes a b

/-- **The add step realizes the field add under `mkEnc`.** -/
theorem addQW_realizes (a b : ZMod Q) :
    addQW (mkEnc a) (mkEnc b) = mkEnc (modAddF a b) := by
  rw [addQW_eq_mkAddW]; exact mkAddW_realizes a b

/-! ## 5. The ABI maps -/

/-- Input-load map: argument slot → `(base, byte-offset)`. Input word
    `i = (NIN−1) − slot` is loaded from `inp[i]` at byte offset `8·i`
    (`u64` stride); all 8 context words are real inputs. -/
def inLoadMap : InLoadMap := fun slot =>
  if slot ≤ NIN - 1 then some ("RSI", ((NIN - 1) - slot) * 8) else none

/-- Output-store map: one store, `out[0]` at byte offset `0` (`u64` stride). -/
def outStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The `dot_q3329` kernel as an owned-RA, two-address `Lprog` (physical
    registers + spill slots), exported under the C symbol `dot_q3329`,
    `abiW := 64` (width-exact `u64` ABI load/store). -/
def dotQLprog : Lprog :=
  Com.toLprogPhysAbi dotQCom "dot_q3329"
    (fun _ => none) (fun _ => none) inLoadMap outStoreMap
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (residence := none)
    (abiW := 64)

/-- The owned AT&T `.s` text for `dot_q3329`, rendered straight from the owned
    `Lprog` (no jasminc). -/
def dotQAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned dotQLprog

/-- The output path for the field-kernel-emitted `.s`. -/
def dotQTarget : System.FilePath :=
  "bench/field_kernel_compare/gen_com/dot_q3329.s"

/-- **The byte-correct field-kernel owned-emit driver.** Renders the
    front-compiled `q = 3329` 4-term dot kernel to OWNED x86-64 (`dot_q3329`)
    and writes it to `gen_com/dot_q3329.s`. -/
def emitDotQ : IO Unit := do
  IO.FS.createDirAll "bench/field_kernel_compare/gen_com"
  let asm := dotQAsm
  IO.FS.writeFile dotQTarget asm
  IO.println s!"FIELD-DOT-Q emit OK : {dotQTarget} ({asm.toUTF8.size} bytes, symbol dot_q3329)"

/-- One owned function emitted, named `dot_q3329` (consumability witness). -/
theorem dotQ_one_func :
    dotQLprog.lp_funcs.length = 1
      ∧ dotQLprog.lp_funcs.head?.map Prod.fst = some "dot_q3329" :=
  ⟨rfl, rfl⟩

/-! ## 7. INDEPENDENT plain-`Nat` reference (`% 3329` stepwise dot) -/

/-- Independent `F_q` multiply: plain `Nat` `(a·b) % 3329`. -/
def fqMulNat (a b : Nat) : Nat := (a * b) % 3329

/-- Independent `F_q` add: plain `Nat` `(a+b) % 3329`. -/
def fqAddNat (a b : Nat) : Nat := (a + b) % 3329

/-- Independent stepwise dot reference over the SAME input layout as the ABI
    (`g i = inp[i]`, `aᵢ = g i`, `bᵢ = g (4+i)`):
    `(a0·b0 + a1·b1 + a2·b2 + a3·b3) mod 3329`, reduced after each op. -/
def dotNatRef (g : Nat → Nat) : Nat :=
  let a0 := g 0 % 3329; let a1 := g 1 % 3329; let a2 := g 2 % 3329; let a3 := g 3 % 3329
  let b0 := g 4 % 3329; let b1 := g 5 % 3329; let b2 := g 6 % 3329; let b3 := g 7 % 3329
  fqAddNat (fqAddNat (fqAddNat (fqMulNat a0 b0) (fqMulNat a1 b1)) (fqMulNat a2 b2))
    (fqMulNat a3 b3)

/-! ## 8. `denote = spec` vs the independent `% 3329` reference -/

/-- The head-first source valuation: word `i` gets `g i % 3329` (canonical
    residue), `g` the positional input list. -/
def valOf (g : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 (g.getD 0 0 % 3329)) (.cons (BitVec.ofNat 64 (g.getD 1 0 % 3329))
    (.cons (BitVec.ofNat 64 (g.getD 2 0 % 3329)) (.cons (BitVec.ofNat 64 (g.getD 3 0 % 3329))
    (.cons (BitVec.ofNat 64 (g.getD 4 0 % 3329)) (.cons (BitVec.ofNat 64 (g.getD 5 0 % 3329))
    (.cons (BitVec.ofNat 64 (g.getD 6 0 % 3329)) (.cons (BitVec.ofNat 64 (g.getD 7 0 % 3329))
      .nil)))))))

/-- Denote the front program capped at slot `name` (result word). -/
def frontDenoteAt (name : String) (g : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf g))

/-- The five KAT input vectors (a0..a3 at positions 0..3, b0..b3 at positions
    4..7), including reducing cases where the sum of products exceeds `q`, plus
    100 generated vectors (a small affine PRNG family). -/
def samples : List (List Nat) :=
  [ [1, 2, 3, 4, 5, 6, 7, 8],
    [100, 200, 300, 400, 50, 60, 70, 80],
    [3328, 3328, 3328, 3328, 3328, 3328, 3328, 3328],
    [1000, 2000, 3000, 1500, 2500, 500, 1234, 2222],
    [0, 0, 0, 0, 0, 0, 0, 0] ]
  ++ (List.range 100).map (fun s =>
      (List.range 8).map (fun i => (i * (2 * s + 1) + 31 * s + 7) % 3329))

/-- **denote = independent spec.** The front program capped at the output copy
    `q0` denotes the independent plain-`Nat` `% 3329` stepwise dot reference on
    every sample (5 KAT + 100 generated vectors). -/
theorem dot_denote_spec :
    samples.all (fun g =>
      frontDenoteAt "q0" g
        == some (BitVec.ofNat 64 (dotNatRef (fun i => g.getD i 0)))) = true := by
  native_decide

/-! ## 9. Structural gates on the lowered `Com` -/

/-- Every binding is a pure scalar-arith op (`regArith`/`regConst`/immediate
    shift) — no `extCall`, no `stackLoad`/`stackStore`. -/
def allPureArith : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body =>
    (match e.op with
     | .regArith _ _ => true
     | .regConst _ _ => true
     | .shlImm _ _ => true
     | .shrImm _ _ => true
     | _ => false) && allPureArith body

theorem dot_is_purearith_only : allPureArith dotQCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last binding** is an identity copy — the `q0` output copy of the
    accumulated residue (the positional `OutStoreMap` stores its dst to
    `out[0]`). -/
theorem dot_last_binding_is_copy :
    ((copyFlags dotQCom).drop ((copyFlags dotQCom).length - 1)) = [true] := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.FieldDotEmitQ

/-- Compiled byte-correct field-dot owned producer entry point. The
    orchestrator emits it the same way as the other field pipelines
    (`lean_exe`-style). -/
def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.FieldDotEmitQ.emitDotQ
