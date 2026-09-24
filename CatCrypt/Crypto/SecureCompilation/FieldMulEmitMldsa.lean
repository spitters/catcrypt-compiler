/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Byte-correct field multiply over `F_q` (`q = 8380417`, ML-DSA), FRONT-COMPILED

This module sources the ML-DSA / Dilithium prime `q = 8380417 = 2^23 − 2^13 + 1`
single-word Montgomery multiply through the verified direct front — NO
hand-built `Com jasminDialect` anywhere:

```
  mulBody (LowCT: RScalarSetExpr Montgomery REDC word math over `a`,`b`)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  mldsaMulCom : Com jasminDialect inCtxt r64
    --(Com.toLprogPhysAbi, owned RA + 2-address)-->  Lprog
    --(LprogAsmPrinter.renderLprogAtt)-->  gen_com/mldsa_mul.s
```

no jasminc, no hand-authored assembly.

## The reduction challenge at `q ≈ 2^23` and why Montgomery

For `a, b < q`, the product `a·b < q² ≈ 2^46` fits in 64 bits, but the
`q = 3329`-style single-mul Barrett `(r·m) >>> k` would OVERFLOW: with `r ≈ 2^46`
and the Barrett constant `m ≈ ⌊2^46/q⌋ ≈ 2^23`, the intermediate `r·m ≈ 2^69`
exceeds 64 bits. The reference Dilithium method, used here, is **Montgomery
reduction** (additive REDC form), every step of which fits a 64-bit word op:

```
   m := (T · qinvNeg) mod 2^32          -- low 32 bits;  qinvNeg < 2^32
   t := (T + m·q) >>> 32                -- m·q < 2^32·2^23 = 2^55;  T + m·q < 2^46 + 2^55 < 2^64
   condSubQ(t)                          -- t ∈ [0, 2q);  one conditional subtract canonicalises
```

with the precomputed constant `qinvNeg = −q⁻¹ mod 2^32 = 4236238847`
(`= 2^32 − 58728449`, where `58728449` is the PQClean `QINV` with
`q·QINV ≡ 1 (mod 2^32)`; here we use the additive REDC form so we need
`q·qinvNeg ≡ −1 (mod 2^32)`, verified below in §5).

### What the kernel computes — Montgomery domain (be explicit!)

Montgomery reduction of `T = a·b` computes `a·b·R⁻¹ mod q`, NOT the plain
product `a·b mod q`. So **the kernel computes the Montgomery product**:

```
   mldsa_mul(a, b) = (a · b · R⁻¹) mod q          where  R = 2^32,  R⁻¹ = 8265825 mod q.
```

The byte-KAT reference is therefore the Montgomery formula `(a·b·8265825) mod 8380417`,
**not** the plain `(a·b) mod 8380417`.

The csub for `q = 8380417` (input in `[0, 2q)`), branch-free / constant-time:

```
   t'   := x − q
   sh   := t' >>> 63          -- 1 iff x < q (logical shift, top bit of the wrap)
   x'   := t' + sh·q          -- (x ≥ q ? x−q : x)
```

Each step is an `SExpr` `SMul`/`SAdd`/`SSub`/`SAnd`/`SShr` — the `lowerSExpr`
straight-line alphabet, no `Jcc`, no leaf call.

## ABI (the C caller's contract, unchanged)

```c
extern void mldsa_mul(uint64_t *out, const uint64_t *inp);
//   inp[0]=a  inp[1]=b   (canonical residues in [0, q))
//   out[0] = (a * b * 8265825) mod 8380417     (the Montgomery product a*b*R^-1 mod q)
```

`RDI = out`, `RSI = inp` (the SysV 2-pointer ABI `Com.toLprogPhysAbi` wraps).
`abiW := 64`: each load is a `movq inp(%rsi,…), %work`, the store a
`movq %work, out(%rdi)`.

## Gates (cheap in-Lean gates only; the byte tie is the C KAT)

* `mldsaLowered_isSome` — the front translates + lowers.
* `mldsaMulCom_provenance` — `frontComAt "outv" >>= cryptoDialectToJasminCom =
  some mldsaMulCom`, the rfl provenance tie from the front to the deployed `Com`.
* `mldsaMul_one_func` — one exported function named `mldsa_mul`.
* The Montgomery constants (`qinvNeg`, `R⁻¹`) and the `#eval` denotation battery
  against the independent Montgomery reference `(a·b·R⁻¹) mod q` are the
  in-Lean cross-check (§7–8); the byte tie against the
  orchestrator's C harness is the real correctness gate.

**0 sorries.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldMulEmitMldsa

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

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The ML-DSA modulus, as a `Nat`. -/
abbrev qNat : Nat := 8380417
/-- `−q⁻¹ mod 2^32` (additive Montgomery REDC constant). -/
abbrev qinvNegNat : Nat := 4236238847
/-- `2^32 − 1`. -/
abbrev mask32Nat : Nat := 4294967295
/-- `R⁻¹ = (2^32)⁻¹ mod q` (for the Montgomery reference formula). -/
abbrev RinvNat : Nat := 8265825

/-! ## 1. The straight-line `LowCT` Montgomery body -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- The Montgomery multiply body: `prod := a·b`; `m := (prod·qinvNeg) & mask32`;
    `sum := prod + m·q`; `t := sum >>> 32` (∈ [0, 2q)); one branch-free
    conditional subtract (`d := t − q; sh := d >>> 63; outv := d + sh·q`). -/
def mulBody : LowCT := seqAll [
  .RScalarSetExpr "prod" (.SMul (.SVar "a") (.SVar "b")),
  .RScalarSetExpr "mraw" (.SMul (.SVar "prod") (.SLit qinvNegNat)),
  .RScalarSetExpr "m"    (.SAnd (.SVar "mraw") (.SLit mask32Nat)),
  .RScalarSetExpr "mq"   (.SMul (.SVar "m") (.SLit qNat)),
  .RScalarSetExpr "sum"  (.SAdd (.SVar "prod") (.SVar "mq")),
  .RScalarSetExpr "t"    (.SShr (.SVar "sum") (.SLit 32)),
  .RScalarSetExpr "d"    (.SSub (.SVar "t") (.SLit qNat)),
  .RScalarSetExpr "sh"   (.SShr (.SVar "d") (.SLit 63)),
  .RScalarSetExpr "shq"  (.SMul (.SVar "sh") (.SLit qNat)),
  .RScalarSetExpr "outv" (.SAdd (.SVar "d") (.SVar "shq")) ]

/-! ## 2. Source context + `VarMap` (2 words, `a | b`) -/

/-- Bind a name list onto a `replicate`-`sword 64` context, first name = head. -/
def bindAll : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindAll ns).bind n

/-- The source context: 2 `u64` scalar slots, `a` then `b`. -/
def srcCtx : Ctx := List.replicate 2 (.sword 64)

/-- The source `VarMap` (`a` at the head). -/
def srcVM : VarMap srcCtx := bindAll ["a", "b"]

/-! ## 3. The front-emitted program -/

/-- Push `mulBody` through the control front and cap with
    `ret <name>`. `none` if the front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM mulBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted kernel, lowered to the jasmin dialect (capped at the final
    output binding `outv`). -/
def mldsaLoweredOpt :=
  (frontComAt "outv").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem mldsaLowered_isSome : mldsaLoweredOpt.isSome := by native_decide

/-- The input context: 2 `r64` words (`a`, `b`). -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 2 r64

/-- The deployed `mldsa_mul` `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    Rendered to owned `.s` below under the `mldsa_mul` symbol. -/
def mldsaMulCom : Com jasminDialect inCtxt r64 :=
  mldsaLoweredOpt.get mldsaLowered_isSome

/-- **Provenance**: the front pipeline, applied end to end, is DEFINITIONALLY the
    deployed `Com` — `mldsaMulCom` is not a re-derivation, it IS
    `frontComAt "outv" >>= cryptoDialectToJasminCom`. -/
theorem mldsaMulCom_provenance :
    (frontComAt "outv").bind DialectToJasminCom.cryptoDialectToJasminCom
      = some mldsaMulCom :=
  (Option.some_get mldsaLowered_isSome).symm

/-! ## 4. The ABI maps -/

/-- Input-load map: argument slot → `(base, byte-offset)`. Input word
    `i = (2-1) − slot` is loaded from `inp[i]` at byte offset `8·i` (`u64`
    stride); both slots are real inputs (`a`, `b`), no dead placeholders. -/
def inLoadMap : InLoadMap := fun slot =>
  if slot ≤ 1 then some ("RSI", (1 - slot) * 8) else none

/-- Output-store map: one store, `out[0]` at byte offset `0` (`u64` stride). -/
def outStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 5. The owned `Lprog`, rendered `.s`, and emit driver -/

/-- The `mldsa_mul` kernel as an owned-RA, two-address `Lprog` (physical
    registers + spill slots), exported under the C symbol `mldsa_mul`,
    `abiW := 64` (width-exact `u64` ABI load/store). -/
def mldsaMulLprog : Lprog :=
  Com.toLprogPhysAbi mldsaMulCom "mldsa_mul"
    (fun _ => none) (fun _ => none) inLoadMap outStoreMap
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (residence := none)
    (abiW := 64)

/-- The owned AT&T `.s` text for `mldsa_mul`, rendered straight from the owned
    `Lprog` (no jasminc). -/
def mldsaMulAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned mldsaMulLprog

/-- The output path for the field-kernel-emitted `.s`. -/
def mldsaMulTarget : System.FilePath :=
  "bench/field_kernel_compare/gen_com/mldsa_mul.s"

/-- **The byte-correct field-kernel owned-emit driver.** Renders the concrete
    `q = 8380417` Montgomery multiply kernel to OWNED x86-64 (`mldsa_mul`) and
    writes it to `gen_com/mldsa_mul.s`. -/
def emitMldsaMul : IO Unit := do
  IO.FS.createDirAll "bench/field_kernel_compare/gen_com"
  let asm := mldsaMulAsm
  IO.FS.writeFile mldsaMulTarget asm
  IO.println s!"FIELD-MUL-MLDSA emit OK : {mldsaMulTarget} ({asm.toUTF8.size} bytes, symbol mldsa_mul)"

/-- One owned function emitted, named `mldsa_mul` (consumability witness). -/
theorem mldsaMul_one_func :
    mldsaMulLprog.lp_funcs.length = 1
      ∧ mldsaMulLprog.lp_funcs.head?.map Prod.fst = some "mldsa_mul" :=
  ⟨rfl, rfl⟩

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 6. INDEPENDENT Montgomery reference (`(a·b·R⁻¹) mod q`) -/

/-- Independent ML-DSA Montgomery field multiply: plain `Nat`
    `(a · b · R⁻¹) mod q`, `R⁻¹ = 8265825`, `q = 8380417`. This is EXACTLY what
    the kernel computes (Montgomery domain), and the byte-KAT reference. -/
def mldsaMulRef (a b : Nat) : Nat := (a * b * RinvNat) % qNat

/-! ### Montgomery constant verification (`#eval`, expect `true`)

`q·qinvNeg ≡ −1 (mod 2^32)` (the additive REDC constant) and `R·R⁻¹ ≡ 1 (mod q)`
(the reference radix inverse). -/

/-- `q · qinvNeg mod 2^32`, expect `4294967295 = 2^32 − 1 ≡ −1`. -/
def qinvNeg_ok : Bool := (qNat * qinvNegNat) % 4294967296 == 4294967295
/-- `R · R⁻¹ mod q`, expect `1` (`R = 2^32`). -/
def Rinv_ok : Bool := (4294967296 * RinvNat) % qNat == 1

-- #eval qinvNeg_ok   -- expect: true   (q·qinvNeg ≡ −1 mod 2^32)
-- #eval Rinv_ok      -- expect: true   (R·R⁻¹ ≡ 1 mod q)

/-! ## 7. Valuation builder + reference cross-check -/

/-- Build a `Valuation (List.replicate n r64)` from a positional word function. -/
def mkVal64 (g : Nat → BitVec 64) :
    (n : Nat) → @Ctxt.Valuation jasminDialect _ (List.replicate n r64)
  | 0 => .nil
  | (n + 1) => .cons (g 0) (mkVal64 (fun j => g (j + 1)) n)

/-- The input valuation: slot `i` gets `g i % q` for `i < 2` (canonical
    residue). -/
def encode (g : Nat → Nat) : Ctxt.Valuation inCtxt :=
  mkVal64 (fun i => BitVec.ofNat 64 (g i % qNat)) 2

/-- Denote `mldsaMulCom` and read out the returned output word. -/
def comOut (g : Nat → Nat) : Nat := (mldsaMulCom.denote (encode g)).toNat

/-- Independent-reference cross-check on one input vector `g`: the `Com`
    denotation equals the Montgomery reference `(a·b·R⁻¹) mod q`. -/
def checkVec (g : Nat → Nat) : Bool := comOut g == mldsaMulRef (g 0 % qNat) (g 1 % qNat)

/-- The KAT input vectors (a, b at positions 0, 1), including reducing cases
    where `a·b ≫ q` (the Montgomery reduce is exercised). -/
def vKat1 : Nat → Nat := fun i => [1, 1].getD i 0                 -- → Rinv = 8265825
def vKat2 : Nat → Nat := fun i => [0, 12345].getD i 0            -- → 0
def vKat3 : Nat → Nat := fun i => [12345, 67890].getD i 0        -- → 6597242 (reducing)
def vKat4 : Nat → Nat := fun i => [8380416, 8380416].getD i 0    -- → 8265825 ((q−1)², max)
def vKat5 : Nat → Nat := fun i => [5000000, 7000000].getD i 0    -- → reducing (large)

/-- A small affine PRNG family for the spread cross-check. -/
def vGen (s : Nat) : Nat → Nat := fun i => (i * (7919 * s + 13) + 104729 * s + 7) % qNat

/-- **Reference check**: the `Com` denotation matches the independent Montgomery
    reference on the five KAT vectors. Expect `true`. -/
def katChecks : Bool :=
  checkVec vKat1 && checkVec vKat2 && checkVec vKat3 && checkVec vKat4 && checkVec vKat5

/-- ≥200 generated vectors all matching the reference. Expect `true`. -/
def genChecks : Bool := (List.range 200).all (fun s => checkVec (vGen s))

/-- The full check battery: KAT + 200 generated vectors. Expect `true`. -/
def allChecks : Bool := katChecks && genChecks

-- #eval katChecks      -- expect: true
-- #eval allChecks      -- expect: true  (5 KAT + 200 generated vs independent Montgomery ref)

-- The KAT residues (independent Montgomery reference (a·b·8265825) mod 8380417):
-- #eval mldsaMulRef 1 1               -- expect: 8265825
-- #eval mldsaMulRef 0 12345           -- expect: 0
-- #eval mldsaMulRef 12345 67890       -- expect: 6597242  (reducing)
-- #eval mldsaMulRef 8380416 8380416   -- expect: 8265825  ((q−1)², max product)
-- #eval mldsaMulRef 5000000 7000000   -- (reducing, large)

-- And the emitted `Com` itself on the KAT vectors (the value the `.s` must match):
-- #eval comOut vKat1         -- expect: 8265825
-- #eval comOut vKat2         -- expect: 0
-- #eval comOut vKat3         -- expect: 6597242
-- #eval comOut vKat4         -- expect: 8265825
-- #eval comOut vKat5         -- (reducing, large)

end CatCrypt.Crypto.SecureCompilation.FieldMulEmitMldsa

/-- Compiled byte-correct ML-DSA field-multiply owned producer entry point. The
    orchestrator emits it the same way as the other field pipelines. -/
def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.FieldMulEmitMldsa.emitMldsaMul
