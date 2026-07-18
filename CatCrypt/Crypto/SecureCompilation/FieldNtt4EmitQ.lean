/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Byte-correct 4-point forward NTT over `F_q` (`q = 3329`), FRONT-COMPILED, OWNED x86

A COMPLETE 4-point radix-2 decimation-in-time (DIT) forward NTT over the
ML-KEM prime field `F_q`, `q = 3329`, built by composing **four** Cooley-Tukey
butterflies (the same `a' = a + ω·b`, `b' = a − ω·b mod q` block that
`FieldButterflyEmitQ` emits), sourced through the verified front — NO
hand-built `Com` anywhere — and rendered to AT&T x86-64 `.s` through the owned
linear backend with NO jasminc and NO hand-authored assembly:

```
  ntt4Body (LowCT: RScalarSetExpr Barrett/csub word math over the 4 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  ntt4QCom : Com jasminDialect inCtxt r64
    --(Com.toLprogPhysAbi, owned RA + 2-address)-->  Lprog
    --(LprogAsmPrinter.renderLprogAtt)-->  gen_com/ntt4_q3329.s
```

## The kernel — radix-2 DIT 4-point forward NTT over `F_q`

A primitive 4th root of unity mod `3329` is `ω = 1729` (the ML-KEM ζ), with
`ω² = 3328 = −1 mod q`. The DIT structure (inputs `x0..x3`, twiddles
consistent with a standard 4-point NTT — `ω⁰ = 1` on the first three
butterflies, `ω = 1729` on the last):

```
   Layer 1 (stride 2):
     (a0, a2) := butterfly(x0, x2, 1)
     (a1, a3) := butterfly(x1, x3, 1)
   Layer 2 (stride 1):
     (y0, y1) := butterfly(a0, a1, 1)
     (y2, y3) := butterfly(a2, a3, ω = 1729)
```

where `butterfly(a, b, w) = (a + w·b mod q, a − w·b mod q)`. The outputs
`(y0, y1, y2, y3)` are the standard DIT-ordered NTT of `(x0, x1, x2, x3)`.
The unit twiddles (`ω⁰ = 1`) run the full Barrett block on `1·b` — uniform
word arithmetic, exercised by the denote gate.

Each butterfly is the three field ops `t := w·b; up := a + t; lo := a − t`,
computed word-for-word as the `MlkemNttFieldEmit` word blocks — so the whole
NTT is 4 Barrett mul-reduces + 4 csub-adds + 4 csub-subs. Every intermediate
stays in range: inputs are canonical residues `< q`, so each product
`w·b < q² = 11 082 241 < 2^24` (Barrett-valid) and each `t` is canonicalised
`< q`; then `a + t < 2q` (one csub) and `a + (q − t) < 2q` (one csub). So the
kernel computes the 4-point forward NTT exactly.

## ABI (the C caller's contract, unchanged)

```c
extern void ntt4_q3329(uint64_t *out, const uint64_t *inp);
//   inp[0..3] = x0..x3   (canonical residues in [0,q))
//   out[0..3] = y0..y3   (the DIT 4-point forward NTT of x mod 3329)
```

`RDI = out`, `RSI = inp` (SysV 2-pointer ABI). `abiW := 64`. The reduce
constants and twiddles are `regConst` immediates (front `SLit`), not loaded —
the input context is exactly the 4 real input words. `Com.toLprogPhysAbi`'s
`OutStoreMap` is **positional** (it stores the dst of the last `n` bindings,
in order), so the body ends with the four output copies `q0..q3 := y0..y3`
(each lowering to exactly ONE binding).

## What is proved vs KAT-gated

* `ntt4QCom` is FRONT-GENERATED (`translateDialectControl` +
  `cryptoDialectToJasminCom`), never hand-built; the front translates and
  lowers end-to-end (`ntt4Lowered_isSome`).
* `ntt4_denote_spec` — the front programs capped at the output copies
  `q0..q3` denote the four words of the INDEPENDENT plain-`Nat` `% 3329`
  4-point DIT NTT reference `ntt4NatRef` on the 4 KAT vectors (reducing +
  wrapping cases) plus 100 generated vectors, ALL FOUR outputs, by
  `native_decide`.
* `mulQW_eq_mkMulW` / `addQW_eq_mkAddW` / `subQW_eq_mkSubW` — the per-op word
  functions the body computes are DEFINITIONALLY the `MlkemNttFieldEmit` word
  blocks (`rfl`); composed with `mkMulW_realizes` / `mkAddW_realizes` /
  `mkSubW_realizes` that gives the field-op realization under `mkEnc` (§4).
* Structural gates: every lowered binding is pure scalar arith
  (`ntt4_is_purearith_only`); the last four bindings are the output copies
  (`ntt4_last_four_bindings_are_copies`).
* The whole-`.s` tie is KAT-gated: `bench/field_kernel_compare/ntt4_q3329_kat.c`
  checks the rendered `.s` produces `out[0..3] = ntt4NatRef` byte-for-byte
  (`make -C bench/field_kernel_compare ntt4-kat`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldNtt4EmitQ

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
  (mkCsubW mkBarrettW mkMulW mkAddW mkSubW mkMulW_realizes mkAddW_realizes mkSubW_realizes)
open CatCrypt.Crypto.SecureCompilation.FieldDescentMlkem (mkEnc Q)
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect (modMulF modAddF modSubF)

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- Number of input words loaded from `inp`: `x0..x3`. -/
abbrev NIN : Nat := 4

/-- Number of output words stored to `out`: `y0..y3`. -/
abbrev NOUT : Nat := 4

/-- The primitive 4th-root twiddle `ω = 1729` (the ML-KEM ζ, `ω² = −1 mod q`). -/
def wConst : Nat := 1729

/-! ## 1. The straight-line `LowCT` body -/

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

/-- `dst := (a · b) mod q`: schoolbook product, Barrett quotient estimate,
    remainder, one csub — word-for-word `MlkemNttFieldEmit.mkMulW`. -/
def mulModStmts (dst a b : String) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "_x") (.SMul (.SVar a) (.SVar b)),
    .RScalarSetExpr (dst ++ "_q")
      (.SShr (.SMul (.SVar (dst ++ "_x")) (.SLit 5039)) (.SLit 24)),
    .RScalarSetExpr (dst ++ "_r")
      (.SSub (.SVar (dst ++ "_x"))
        (.SMul (.SVar (dst ++ "_q")) (.SLit 3329))) ]
  ++ csubStmts dst (dst ++ "_r")

/-- `dst := (a + b) mod q`: `a + b` then one csub — word-for-word
    `MlkemNttFieldEmit.mkAddW`. -/
def addModStmts (dst a b : String) : List LowCT :=
  .RScalarSetExpr (dst ++ "_u") (.SAdd (.SVar a) (.SVar b)) :: csubStmts dst (dst ++ "_u")

/-- `dst := (a − b) mod q`: `a + (3329 − b)` then one csub — word-for-word
    `MlkemNttFieldEmit.mkSubW = mkCsubW (a + (3329 − b))`. -/
def subModStmts (dst a b : String) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "_d") (.SSub (.SLit 3329) (.SVar b)),
    .RScalarSetExpr (dst ++ "_u") (.SAdd (.SVar a) (.SVar (dst ++ "_d"))) ]
  ++ csubStmts dst (dst ++ "_u")

/-- One Cooley-Tukey butterfly `(up, lo) := (a + w·b, a − w·b) mod q`, with the
    twiddle product staged in `t<up>`. -/
def bflyStmts (up lo a b w : String) : List LowCT :=
  mulModStmts ("t" ++ up) w b ++
  addModStmts up a ("t" ++ up) ++
  subModStmts lo a ("t" ++ up)

/-- The full 4-point DIT NTT body: the unit twiddle `one := 1` and the real
    twiddle `wd := 1729` seeded as `SLit` constants, the four butterflies of
    the DIT schedule, then the four output copies `q0..q3 := y0..y3` (each
    lowering to exactly ONE binding — the last-four-bindings output
    convention). -/
def ntt4Body : LowCT := seqAll (
  [ .RScalarSetExpr "one" (.SLit 1),
    .RScalarSetExpr "wd" (.SLit wConst) ] ++
  -- Layer 1 (stride 2)
  bflyStmts "a0" "a2" "x0" "x2" "one" ++
  bflyStmts "a1" "a3" "x1" "x3" "one" ++
  -- Layer 2 (stride 1)
  bflyStmts "y0" "y1" "a0" "a1" "one" ++
  bflyStmts "y2" "y3" "a2" "a3" "wd" ++
  [ .RScalarSetExpr "q0" (.SVar "y0"),
    .RScalarSetExpr "q1" (.SVar "y1"),
    .RScalarSetExpr "q2" (.SVar "y2"),
    .RScalarSetExpr "q3" (.SVar "y3") ])

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `x0`) is the context head, word `3` (= `x3`) the
deepest — input word `i` at De Bruijn index `i` (the 4-word `[x0..x3]` ABI,
exactly `inp[0..3]`). -/

/-- The source context: 4 `u64` scalar slots (the 4 real inputs). -/
def srcCtx : Ctx := List.replicate NIN (.sword 64)

/-- The source `VarMap`: word 3 (`x3`) bound first (deepest), word 0 (`x0`) last. -/
def srcVM : VarMap srcCtx :=
  (((VarMap.empty.bind "x3").bind "x2").bind "x1").bind "x0"

/-! ## 3. The front-emitted programs -/

/-- Push `ntt4Body` through the front and cap with `ret <name>`. `none` if the
    front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM ntt4Body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted 4-point NTT, lowered to the jasmin dialect (capped at the
    final output copy `q3`, whose binding is the `Com`'s last). -/
def ntt4LoweredOpt :=
  (frontComAt "q3").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem ntt4Lowered_isSome : ntt4LoweredOpt.isSome := by native_decide

/-- The input context of the `Com`: the 4 `r64` input words `[x0..x3]`. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate NIN r64

/-- The jasmin-dialect 4-point-NTT `Com` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
def ntt4QCom : Com jasminDialect inCtxt r64 :=
  ntt4LoweredOpt.get ntt4Lowered_isSome

/-! ## 4. The per-op word functions are the `MlkemNttFieldEmit` word blocks

`mulModStmts`/`addModStmts`/`subModStmts` compute, word-for-word, exactly the
arithmetic of `MlkemNttFieldEmit.mkMulW`/`mkAddW`/`mkSubW`. We make that
precise by giving the closed word functions the body realizes and proving they
are DEFINITIONALLY the `mkMulW`/`mkAddW`/`mkSubW`/`mkCsubW` blocks (`rfl`);
composing with the proved `mkMulW_realizes`/`mkAddW_realizes`/`mkSubW_realizes`
field-op squares gives the field-spec tie under the canonical encoding
`mkEnc`. -/

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

/-- The sub-step word function the body computes (= `mkSubW`). -/
def subQW (a b : BitVec 64) : BitVec 64 := csub3329W (a + ((3329 : BitVec 64) - b))

/-- **The body's csub is exactly `MlkemNttFieldEmit.mkCsubW`** (`rfl`). -/
theorem csub3329W_eq_mkCsubW (x : BitVec 64) : csub3329W x = mkCsubW x := rfl

/-- **The body's Barrett reduce is exactly `MlkemNttFieldEmit.mkBarrettW`**. -/
theorem barrettW_eq_mkBarrettW (r : BitVec 64) : barrettW r = mkBarrettW r := rfl

/-- **The body's mul step is exactly `MlkemNttFieldEmit.mkMulW`**. -/
theorem mulQW_eq_mkMulW (a b : BitVec 64) : mulQW a b = mkMulW a b := rfl

/-- **The body's add step is exactly `MlkemNttFieldEmit.mkAddW`**. -/
theorem addQW_eq_mkAddW (a b : BitVec 64) : addQW a b = mkAddW a b := rfl

/-- **The body's sub step is exactly `MlkemNttFieldEmit.mkSubW`**. -/
theorem subQW_eq_mkSubW (a b : BitVec 64) : subQW a b = mkSubW a b := rfl

/-- **The mul step realizes the field multiply under `mkEnc`.** Direct from
    `mulQW_eq_mkMulW` + `MlkemNttFieldEmit.mkMulW_realizes`. -/
theorem mulQW_realizes (a b : ZMod Q) :
    mulQW (mkEnc a) (mkEnc b) = mkEnc (modMulF a b) := by
  rw [mulQW_eq_mkMulW]; exact mkMulW_realizes a b

/-- **The add step realizes the field add under `mkEnc`.** -/
theorem addQW_realizes (a b : ZMod Q) :
    addQW (mkEnc a) (mkEnc b) = mkEnc (modAddF a b) := by
  rw [addQW_eq_mkAddW]; exact mkAddW_realizes a b

/-- **The sub step realizes the field subtract under `mkEnc`.** -/
theorem subQW_realizes (a b : ZMod Q) :
    subQW (mkEnc a) (mkEnc b) = mkEnc (modSubF a b) := by
  rw [subQW_eq_mkSubW]; exact mkSubW_realizes a b

/-! ## 5. The ABI maps -/

/-- Input-load map: argument slot → `(base, byte-offset)`. Input word
    `i = (NIN−1) − slot` is loaded from `inp[i]` at byte offset `8·i`
    (`u64` stride); all 4 context words are real inputs. -/
def inLoadMap : InLoadMap := fun slot =>
  if slot ≤ NIN - 1 then some ("RSI", ((NIN - 1) - slot) * 8) else none

/-- Output-store map: FOUR stores — `y0..y3` to `out[0..3]` at byte offsets
    `0, 8, 16, 24` (`u64` stride). The store order matches the `last-NOUT = 4`
    output-copy bindings `q0..q3`. -/
def outStoreMap : OutStoreMap := [("RDI", 0), ("RDI", 8), ("RDI", 16), ("RDI", 24)]

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The `ntt4_q3329` kernel as an owned-RA, two-address `Lprog`, exported under
    the C symbol `ntt4_q3329`, `abiW := 64`. -/
def ntt4QLprog : Lprog :=
  Com.toLprogPhysAbi ntt4QCom "ntt4_q3329"
    (fun _ => none) (fun _ => none) inLoadMap outStoreMap
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (residence := none)
    (abiW := 64)

/-- The owned AT&T `.s` text for `ntt4_q3329`, rendered straight from the owned
    `Lprog` (no jasminc). -/
def ntt4QOwnedAsm : String := renderLprogAtt ntt4QLprog

/-- The output path for the field-kernel-emitted `.s`. -/
def ntt4QTarget : System.FilePath :=
  "bench/field_kernel_compare/gen_com/ntt4_q3329.s"

/-- **The byte-correct 4-point-NTT owned-emit driver.** Renders the
    front-compiled `q = 3329` forward 4-point NTT to OWNED x86-64
    (`ntt4_q3329`) and writes it to `gen_com/ntt4_q3329.s`. -/
def emitNtt4Q : IO Unit := do
  IO.FS.createDirAll "bench/field_kernel_compare/gen_com"
  let asm := ntt4QOwnedAsm
  IO.FS.writeFile ntt4QTarget asm
  IO.println s!"FIELD-NTT4-Q emit OK : {ntt4QTarget} ({asm.toUTF8.size} bytes, symbol ntt4_q3329)"

/-- One owned function emitted, named `ntt4_q3329` (consumability witness). -/
theorem ntt4Q_one_func :
    ntt4QLprog.lp_funcs.length = 1
      ∧ ntt4QLprog.lp_funcs.head?.map Prod.fst = some "ntt4_q3329" :=
  ⟨rfl, rfl⟩

/-! ## 7. INDEPENDENT plain-`Nat` reference (`% 3329` 4-point DIT NTT) -/

/-- Independent `F_q` multiply: plain `Nat` `(a·b) % 3329`. -/
def fqMulNat (a b : Nat) : Nat := (a * b) % 3329

/-- Independent `F_q` add: plain `Nat` `(a+b) % 3329`. -/
def fqAddNat (a b : Nat) : Nat := (a + b) % 3329

/-- Independent `F_q` subtract: plain `Nat` `(a + q − b) % 3329` (`b < q`). -/
def fqSubNat (a b : Nat) : Nat := (a + 3329 - b) % 3329

/-- Independent stepwise butterfly: `(a + w·b, a − w·b) mod q`. -/
def bflyNat (a b w : Nat) : Nat × Nat :=
  let t := fqMulNat w b
  (fqAddNat a t, fqSubNat a t)

/-- **Independent plain-`Nat` `% 3329` 4-point DIT forward NTT reference** over
    the SAME input layout as the ABI (`g 0..3 = x0..x3`):

    Layer 1: `(a0,a2) := bfly(x0,x2,1)`, `(a1,a3) := bfly(x1,x3,1)`.
    Layer 2: `(y0,y1) := bfly(a0,a1,1)`, `(y2,y3) := bfly(a2,a3,1729)`.

    Returns `(y0, y1, y2, y3)`. -/
def ntt4NatRef (g : Nat → Nat) : Nat × Nat × Nat × Nat :=
  let x0 := g 0 % 3329; let x1 := g 1 % 3329
  let x2 := g 2 % 3329; let x3 := g 3 % 3329
  let (a0, a2) := bflyNat x0 x2 1
  let (a1, a3) := bflyNat x1 x3 1
  let (y0, y1) := bflyNat a0 a1 1
  let (y2, y3) := bflyNat a2 a3 wConst
  (y0, y1, y2, y3)

/-! ## 8. `denote = spec` vs the independent `% 3329` reference -/

/-- The head-first source valuation: word `i` gets `g i % 3329` (canonical
    residue), `g` the positional input list `[x0, x1, x2, x3]`. -/
def valOf (g : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 (g.getD 0 0 % 3329)) (.cons (BitVec.ofNat 64 (g.getD 1 0 % 3329))
    (.cons (BitVec.ofNat 64 (g.getD 2 0 % 3329))
      (.cons (BitVec.ofNat 64 (g.getD 3 0 % 3329)) .nil)))

/-- Denote the front program capped at slot `name` (result word). -/
def frontDenoteAt (name : String) (g : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf g))

/-- The KAT input vectors (`x0..x3` at positions 0..3), including reducing and
    wrapping cases, plus 100 generated vectors (a small affine PRNG family). -/
def samples : List (List Nat) :=
  [ [1, 2, 3, 4],
    [100, 200, 300, 400],
    [3000, 2500, 100, 1],
    [3328, 3328, 3328, 3328] ]
  ++ (List.range 100).map (fun s =>
      (List.range 4).map (fun i => (i * (2 * s + 1) + 31 * s + 7) % 3329))

/-- The reference output tuple as a positional list. -/
def refList (g : List Nat) : List (BitVec 64) :=
  let (y0, y1, y2, y3) := ntt4NatRef (fun i => g.getD i 0)
  [BitVec.ofNat 64 y0, BitVec.ofNat 64 y1, BitVec.ofNat 64 y2, BitVec.ofNat 64 y3]

/-- **denote = independent spec, all four output words.** The front programs
    capped at the output copies `q0..q3` denote the four words of the
    independent plain-`Nat` `% 3329` DIT NTT reference on every sample (4 KAT +
    100 generated vectors). -/
theorem ntt4_denote_spec :
    samples.all (fun g =>
      (List.range 4).all (fun j =>
        frontDenoteAt ("q" ++ toString j) g
          == some ((refList g).getD j 0))) = true := by
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

theorem ntt4_is_purearith_only : allPureArith ntt4QCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last four bindings** are identity copies — the `q0..q3` output
    copies of `y0..y3` (the positional `OutStoreMap` stores their dsts to
    `out[0..3]`). -/
theorem ntt4_last_four_bindings_are_copies :
    ((copyFlags ntt4QCom).drop ((copyFlags ntt4QCom).length - 4))
      = [true, true, true, true] := by native_decide

end CatCrypt.Crypto.SecureCompilation.FieldNtt4EmitQ

/-- Compiled byte-correct 4-point-NTT owned producer entry point. The
    orchestrator emits it the same way as the other field pipelines. -/
def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.FieldNtt4EmitQ.emitNtt4Q
