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
# Byte-correct ML-KEM forward-NTT butterfly over `F_q` (`q = 3329`), FRONT-COMPILED, OWNED x86

ONE Cooley-Tukey forward-NTT butterfly over the prime field `F_q`, `q = 3329`
(the ML-KEM modulus). Given `(a, b, ω)`:

```
   t  := ω · b      mod q       -- the twiddle product
   a' := a + t      mod q       -- the upper output
   b' := a − t      mod q       -- the lower output
```

sourced through the verified front — NO hand-built `Com` anywhere — and
rendered to AT&T x86-64 `.s` through the owned linear backend with NO jasminc
and NO hand-authored assembly:

```
  bflyBody (LowCT: RScalarSetExpr Barrett/csub word math over the 3 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  bflyQCom : Com jasminDialect inCtxt r64
    --(Com.toLprogPhysAbi, owned RA + 2-address)-->  Lprog
    --(LprogOptPipeline.renderOwned)-->  gen_com/bfly_q3329.s
```

## The Barrett mul-reduce and csub add/sub (`q = 3329`, mirrors `MlkemNttFieldEmit`)

`(a·b) % q` is a Barrett reduce with `m = ⌊2^24 / q⌋ = 5039`:

```
   qhat := (r · 5039) >>> 24      -- quotient estimate, exact to ±1 over [0, q²)
   rem  := r − qhat·q             -- remainder in [0, 2q)
   condSub3329(rem)               -- one conditional subtract canonicalises
```

and the csub itself:

```
   t    := x − 3329
   x'   := t + (3329 & (0 − (t >>> 63)))    -- (x ≥ q ? x−q : x), branch-free
```

The modular **subtract** `a − b mod q` (= `mkSubW`) is `condSub3329(a + (q − b))`:
because `b` is a canonical residue `< q`, `q − b ∈ [1, q]`, so `a + (q − b) <
2q` and one csub canonicalises — and the `q − b` correctly realises the wrap
when `a < t` (the lower butterfly output `b' = a − t` with `a < t`).

Each intermediate stays in range: inputs are canonical residues `< q`, so the
product `ω·b` is `< q² = 11 082 241 < 2^24` (Barrett-valid) and `t` is
canonicalised to `< q`; then `a + t < 2q` (one csub) and `a + (q − t) < 2q`
(one csub). So the kernel computes the forward-NTT butterfly exactly.

## ABI (the C caller's contract, unchanged)

```c
extern void bfly_q3329(uint64_t *out, const uint64_t *inp);
//   inp[0]=a  inp[1]=b  inp[2]=ω   (canonical residues in [0,q))
//   out[0] = (a + ω*b)       mod 3329   (a')
//   out[1] = (a − ω*b + q)   mod 3329   (b')
```

`RDI = out`, `RSI = inp` (the SysV 2-pointer ABI). `abiW := 64`. The reduce
constants are `regConst` immediates (front `SLit`), not loaded — the input
context is exactly the 3 real input words. `Com.toLprogPhysAbi`'s
`OutStoreMap` is **positional** (it stores the dst of the last `n` bindings,
in order), so the body ends with the two output copies `q0 := a'`, `q1 := b'`
(each lowering to exactly ONE binding).

## What is proved vs KAT-gated

* `bflyQCom` is FRONT-GENERATED (`translateDialectControl` +
  `cryptoDialectToJasminCom`), never hand-built; the front translates and
  lowers end-to-end (`bflyLowered_isSome`).
* `bfly_denote_spec` — the front programs capped at the output copies `q0`/`q1`
  denote the INDEPENDENT plain-`Nat` `% 3329` stepwise butterfly reference
  `bflyNatRef` on the 4 KAT vectors (reducing + wrapping cases) plus 100
  generated vectors, BOTH outputs, by `native_decide`.
* `mulQW_eq_mkMulW` / `csub3329W_eq_mkCsubW` / `addQW_eq_mkAddW` /
  `subQW_eq_mkSubW` — the per-op word functions the body computes are
  DEFINITIONALLY the `MlkemNttFieldEmit` word blocks (`rfl`); composed with
  `mkMulW_realizes` / `mkAddW_realizes` / `mkSubW_realizes` that gives the
  field-op realization under the canonical encoding `mkEnc` (§4).
* Structural gates: every lowered binding is pure scalar arith
  (`bfly_is_purearith_only`); the last two bindings are the output copies
  (`bfly_last_two_bindings_are_copies`).
* The whole-`.s` tie is KAT-gated: `bench/field_kernel_compare/bfly_q3329_kat.c`
  checks the rendered `.s` against the independent `% 3329` reference
  (`make -C bench/field_kernel_compare bfly-kat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldButterflyEmitQ

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

/-- Number of input words loaded from `inp`: `a, b, ω`. -/
abbrev NIN : Nat := 3

/-- Number of output words stored to `out`: `a', b'`. -/
abbrev NOUT : Nat := 2

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
    `MlkemNttFieldEmit.mkSubW = mkCsubW (a + (3329 − b))`; naturally realises
    the wrap when `a < b`. -/
def subModStmts (dst a b : String) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "_d") (.SSub (.SLit 3329) (.SVar b)),
    .RScalarSetExpr (dst ++ "_u") (.SAdd (.SVar a) (.SVar (dst ++ "_d"))) ]
  ++ csubStmts dst (dst ++ "_u")

/-- The full butterfly body: `t := ω·b mod q`, `a' := a + t mod q`,
    `b' := a − t mod q`, then the two output copies `q0 := a'`, `q1 := b'`
    (each lowering to exactly ONE binding — the last-two-bindings output
    convention). -/
def bflyBody : LowCT := seqAll (
  mulModStmts "t" "w" "b" ++
  addModStmts "aout" "a" "t" ++
  subModStmts "bout" "a" "t" ++
  [ .RScalarSetExpr "q0" (.SVar "aout"),
    .RScalarSetExpr "q1" (.SVar "bout") ])

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `a`) is the context head, word `2` (= `ω`) the
deepest — input word `i` at De Bruijn index `i` (the 3-word `[a, b, ω]` ABI,
exactly `inp[0..2]`). -/

/-- The source context: 3 `u64` scalar slots (the 3 real inputs). -/
def srcCtx : Ctx := List.replicate NIN (.sword 64)

/-- The source `VarMap`: word 2 (`ω`) bound first (deepest), word 0 (`a`) last. -/
def srcVM : VarMap srcCtx :=
  ((VarMap.empty.bind "w").bind "b").bind "a"

/-! ## 3. The front-emitted programs -/

/-- Push `bflyBody` through the front and cap with `ret <name>`. `none` if the
    front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM bflyBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted butterfly, lowered to the jasmin dialect (capped at the
    final output copy `q1`, whose binding is the `Com`'s last). -/
def bflyLoweredOpt :=
  (frontComAt "q1").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem bflyLowered_isSome : bflyLoweredOpt.isSome := by native_decide

/-- The input context of the `Com`: the 3 `r64` input words `[a, b, ω]`. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate NIN r64

/-- The jasmin-dialect butterfly `Com` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
def bflyQCom : Com jasminDialect inCtxt r64 :=
  bflyLoweredOpt.get bflyLowered_isSome

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

/-- The sub-step word function the body computes (= `mkSubW`):
    `csub3329W (a + (3329 − b))`. -/
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
    (`u64` stride); all 3 context words are real inputs. -/
def inLoadMap : InLoadMap := fun slot =>
  if slot ≤ NIN - 1 then some ("RSI", ((NIN - 1) - slot) * 8) else none

/-- Output-store map: TWO stores — `a'` to `out[0]` (byte offset `0`), `b'` to
    `out[1]` (byte offset `8`, `u64` stride). The store order matches the
    `last-NOUT = 2` output-copy bindings `q0, q1`. -/
def outStoreMap : OutStoreMap := [("RDI", 0), ("RDI", 8)]

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The `bfly_q3329` kernel as an owned-RA, two-address `Lprog` (physical
    registers + spill slots), exported under the C symbol `bfly_q3329`,
    `abiW := 64` (width-exact `u64` ABI load/store). -/
def bflyQLprog : Lprog :=
  Com.toLprogPhysAbi bflyQCom "bfly_q3329"
    (fun _ => none) (fun _ => none) inLoadMap outStoreMap
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (residence := none)
    (abiW := 64)

/-- The owned AT&T `.s` text for `bfly_q3329`, rendered from the owned `Lprog`
    through the optimizing back-end `renderOwned` (no jasminc). -/
def bflyQAsm : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned bflyQLprog

/-- The output path for the field-kernel-emitted `.s`. -/
def bflyQTarget : System.FilePath :=
  "bench/field_kernel_compare/gen_com/bfly_q3329.s"

/-- **The byte-correct field-kernel owned-emit driver.** Renders the
    front-compiled `q = 3329` forward-NTT butterfly to OWNED x86-64
    (`bfly_q3329`) and writes it to `gen_com/bfly_q3329.s`. -/
def emitBflyQ : IO Unit := do
  IO.FS.createDirAll "bench/field_kernel_compare/gen_com"
  let asm := bflyQAsm
  IO.FS.writeFile bflyQTarget asm
  IO.println s!"FIELD-BUTTERFLY-Q emit OK : {bflyQTarget} ({asm.toUTF8.size} bytes, symbol bfly_q3329)"

/-- One owned function emitted, named `bfly_q3329` (consumability witness). -/
theorem bflyQ_one_func :
    bflyQLprog.lp_funcs.length = 1
      ∧ bflyQLprog.lp_funcs.head?.map Prod.fst = some "bfly_q3329" :=
  ⟨rfl, rfl⟩

/-! ## 7. INDEPENDENT plain-`Nat` reference (`% 3329` stepwise butterfly) -/

/-- Independent `F_q` multiply: plain `Nat` `(a·b) % 3329`. -/
def fqMulNat (a b : Nat) : Nat := (a * b) % 3329

/-- Independent `F_q` add: plain `Nat` `(a+b) % 3329`. -/
def fqAddNat (a b : Nat) : Nat := (a + b) % 3329

/-- Independent `F_q` subtract: plain `Nat` `(a + q − b) % 3329` (`b < q`, so
    `a + q − b` is well-defined and realises the wrap when `a < b`). -/
def fqSubNat (a b : Nat) : Nat := (a + 3329 - b) % 3329

/-- Independent stepwise forward-NTT butterfly reference over the SAME input
    layout as the ABI (`g 0 = a, g 1 = b, g 2 = ω`):
    `t = ω·b%q; a' = (a+t)%q; b' = (a+q−t)%q`. Returns the pair `(a', b')`. -/
def bflyNatRef (g : Nat → Nat) : Nat × Nat :=
  let a := g 0 % 3329; let b := g 1 % 3329; let w := g 2 % 3329
  let t := fqMulNat w b
  (fqAddNat a t, fqSubNat a t)

/-! ## 8. `denote = spec` vs the independent `% 3329` reference -/

/-- The head-first source valuation: word `i` gets `g i % 3329` (canonical
    residue), `g` the positional input list `[a, b, ω]`. -/
def valOf (g : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 (g.getD 0 0 % 3329))
    (.cons (BitVec.ofNat 64 (g.getD 1 0 % 3329))
      (.cons (BitVec.ofNat 64 (g.getD 2 0 % 3329)) .nil))

/-- Denote the front program capped at slot `name` (result word). -/
def frontDenoteAt (name : String) (g : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf g))

/-- The KAT input vectors (a, b, ω at positions 0, 1, 2) — including a reducing
    case (`ω·b` exceeds `q`), a wrapping case (`a < t`, so `a − t` wraps —
    `mkSubW`'s csub is exercised), a near-`q²` case — plus 100 generated
    vectors (a small affine PRNG family). -/
def samples : List (List Nat) :=
  [ [2, 3, 5],
    [100, 3000, 2500],
    [10, 3000, 2500],
    [3328, 3328, 3328] ]
  ++ (List.range 100).map (fun s =>
      (List.range 3).map (fun i => (i * (2 * s + 1) + 31 * s + 7) % 3329))

/-- Both output-capped front programs exist. -/
theorem frontComAt_q_isSome :
    (frontComAt "q0").isSome ∧ (frontComAt "q1").isSome := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **denote = independent spec, both output words.** The front programs capped
    at the output copies `q0`/`q1` denote the two words of the independent
    plain-`Nat` `% 3329` butterfly reference on every sample (4 KAT + 100
    generated vectors). -/
theorem bfly_denote_spec :
    samples.all (fun g =>
      let ref := bflyNatRef (fun i => g.getD i 0)
      frontDenoteAt "q0" g == some (BitVec.ofNat 64 ref.1)
        && frontDenoteAt "q1" g == some (BitVec.ofNat 64 ref.2)) = true := by
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

theorem bfly_is_purearith_only : allPureArith bflyQCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last two bindings** are identity copies — the `(q0, q1)` output
    copies of `(a', b')` (the positional `OutStoreMap` stores their dsts to
    `out[0]`, `out[1]`). -/
theorem bfly_last_two_bindings_are_copies :
    ((copyFlags bflyQCom).drop ((copyFlags bflyQCom).length - 2))
      = [true, true] := by native_decide

end CatCrypt.Crypto.SecureCompilation.FieldButterflyEmitQ

/-- Compiled byte-correct field-butterfly owned producer entry point. The
    orchestrator emits it the same way as the other field pipelines
    (`lean_exe`-style). -/
def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.FieldButterflyEmitQ.emitBflyQ
