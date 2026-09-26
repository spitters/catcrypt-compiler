/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
public import CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
public meta import CatCrypt.Crypto.SecureCompilation.SmallPrimeBarrett
public import CatCrypt.Crypto.SecureCompilation.SmallPrimeBarrett
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Byte-correct degree-3 Horner over `F_q` (`q = 3329`), FRONT-COMPILED, OWNED x86

A degree-3 Horner polynomial `((a·x + b)·x + c)·x + d` over the prime field
`F_q`, `q = 3329` (the ML-KEM modulus), sourced through the verified front —
NO hand-built `Com` anywhere — and rendered to AT&T x86-64 `.s` through the
owned linear backend with NO jasminc and NO hand-authored assembly:

```
  hornerBody (LowCT: RScalarSetExpr Barrett/csub word math over the 5 input slots)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  hornerQCom : Com jasminDialect inCtxt r64
    --(Com.toLprogPhysAbi, owned RA + 2-address)-->  Lprog
    --(LprogAsmPrinter.renderLprogAtt)-->  gen_com/horner_q3329.s
```

## The Barrett mul-reduce and csub add (`q = 3329`, mirrors `MlkemNttFieldEmit`)

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

In Horner each intermediate stays in range: inputs are canonical residues
`< q`, so every `mul` product is `< q² = 11 082 241 < 2^24` (Barrett-valid), and
every `add` operand pair sums to `< 2q` (one csub canonicalises). So the kernel
computes `(((a·x + b)·x + c)·x + d) mod q` exactly.

## ABI (the C caller's contract, unchanged)

```c
extern void horner_q3329(uint64_t *out, const uint64_t *inp);
//   inp[0]=a  inp[1]=b  inp[2]=c  inp[3]=d  inp[4]=x   (canonical residues in [0,q))
//   out[0] = (((a*x + b)*x + c)*x + d) mod 3329
```

`RDI = out`, `RSI = inp` (the SysV 2-pointer ABI). `abiW := 64`: each load is a
`movq inp(%rsi,…), %work`, the store a `movq %work, out(%rdi)`. The reduce
constants are `regConst` immediates (front `SLit`), not loaded — the input
context is exactly the 5 real input words.

## What is proved vs KAT-gated

* `hornerQCom` is FRONT-GENERATED (`translateDialectControl` +
  `cryptoDialectToJasminCom`), never hand-built; the front translates and
  lowers end-to-end (`hornerLowered_isSome`).
* `horner_denote_spec` — the front program's denotation equals the INDEPENDENT
  plain-`Nat` `% 3329` stepwise Horner reference `hornerNatRef` on the 5 KAT
  vectors plus 100 generated vectors (reducing cases included), by
  `native_decide`.
* `mulQW_eq_mkMulW` / `csub3329W_eq_mkCsubW` / `addQW_eq_mkAddW` — the per-op
  word functions the body computes are DEFINITIONALLY the `MlkemNttFieldEmit`
  word blocks (`rfl`); composed with `mkMulW_realizes` / `mkAddW_realizes`
  that gives the field-op realization under `mkEnc` (§4).
* Structural gates: every lowered binding is pure scalar arith
  (`horner_is_purearith_only`); the last binding is the output copy
  (`horner_last_binding_is_copy`).
* The whole-`.s` tie is KAT-gated:
  `bench/field_kernel_compare/horner_q3329_kat.c` checks the rendered `.s`
  against the independent `% 3329` reference
  (`make -C bench/field_kernel_compare horner-q-kat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldHornerEmitQ

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

/-- Number of input words loaded from `inp`: `a, b, c, d, x`. -/
abbrev NIN : Nat := 5

/-! ## 1. The straight-line `LowCT` body -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- The branch-free conditional subtract into `dst` (correct for `src < 2q`):
    `dst_s := src − 3329;  dst := dst_s + (3329 & (0 − (dst_s >>> 63)))` —
    word-for-word `MlkemNttFieldEmit.mkCsubW`. -/
def csubStmts (dst src : String) : List LowCT := SmallPrimeBarrett.csubStmts 3329 dst src

/-- `dst := (a · b) mod q`: schoolbook product, Barrett quotient estimate,
    remainder, one csub — word-for-word `MlkemNttFieldEmit.mkMulW`. -/
def mulModStmts (dst a b : String) : List LowCT :=
  SmallPrimeBarrett.mulModStmts 3329 5039 24 dst a b

/-- `dst := (a + b) mod q`: `a + b` then one csub — word-for-word
    `MlkemNttFieldEmit.mkAddW`. -/
def addModStmts (dst a b : String) : List LowCT :=
  .RScalarSetExpr (dst ++ "_u") (.SAdd (.SVar a) (.SVar b)) :: csubStmts dst (dst ++ "_u")

/-- The full Horner body: the six field steps
    `h1 = a·x`, `h2 = h1+b`, `h3 = h2·x`, `h4 = h3+c`, `h5 = h4·x`,
    `h6 = h5+d`, then the output copy `q0 := h6` (lowering to exactly ONE
    binding — the last-binding output convention). -/
def hornerBody : LowCT := seqAll (
  mulModStmts "h1" "a" "x" ++
  addModStmts "h2" "h1" "b" ++
  mulModStmts "h3" "h2" "x" ++
  addModStmts "h4" "h3" "c" ++
  mulModStmts "h5" "h4" "x" ++
  addModStmts "h6" "h5" "d" ++
  [.RScalarSetExpr "q0" (.SVar "h6")])

/-! ## 2. Source context + `VarMap`

Head-first: word `0` (= `a`) is the context head, word `4` (= `x`) the
deepest — input word `i` at De Bruijn index `i` (the 5-word `[a,b,c,d,x]`
ABI, exactly `inp[0..4]`). -/

/-- The source context: 5 `u64` scalar slots (the 5 real inputs). -/
def srcCtx : Ctx := List.replicate NIN (.sword 64)

/-- The source `VarMap`: word 4 (`x`) bound first (deepest), word 0 (`a`) last. -/
def srcVM : VarMap srcCtx :=
  ((((VarMap.empty.bind "x").bind "d").bind "c").bind "b").bind "a"

/-! ## 3. The front-emitted programs -/

/-- Push `hornerBody` through the front and cap with `ret <name>`. `none` if
    the front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM hornerBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted Horner, lowered to the jasmin dialect (capped at the
    output copy `q0`, whose binding is the `Com`'s last). -/
def hornerLoweredOpt :=
  (frontComAt "q0").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem hornerLowered_isSome : hornerLoweredOpt.isSome := by native_decide

/-- The input context of the `Com`: the 5 `r64` input words `[a,b,c,d,x]`. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate NIN r64

/-- The jasmin-dialect Horner `Com` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
def hornerQCom : Com jasminDialect inCtxt r64 :=
  hornerLoweredOpt.get hornerLowered_isSome

/-! ## 4. The per-op word functions are the `MlkemNttFieldEmit` word blocks

`mulModStmts`/`addModStmts` compute, word-for-word, exactly the arithmetic of
`MlkemNttFieldEmit.mkMulW`/`mkAddW`. We make that precise by giving the closed
word functions the body realizes and proving they are DEFINITIONALLY the
`mkMulW`/`mkAddW`/`mkCsubW` blocks (`rfl`); composing with the proved
`mkMulW_realizes`/`mkAddW_realizes` field-op squares gives the field-spec tie
under the canonical encoding `mkEnc`. -/

/-- The csub word function the body computes (= `mkCsubW`). -/
def csub3329W (x : BitVec 64) : BitVec 64 := Algebraic.FieldWord.csubW 3329 x

/-- The Barrett-reduce word function the body computes (= `mkBarrettW`). -/
def barrettW (r : BitVec 64) : BitVec 64 := SmallPrimeBarrett.barrettW 3329 5039 24 r

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

/-- **The mul step realizes the field multiply under `mkEnc`.** Direct from
    `mulQW_eq_mkMulW` + `MlkemNttFieldEmit.mkMulW_realizes`. -/
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
    (`u64` stride); all 5 context words are real inputs. -/
def inLoadMap : InLoadMap := fun slot =>
  if slot ≤ NIN - 1 then some ("RSI", ((NIN - 1) - slot) * 8) else none

/-- Output-store map: one store, `out[0]` at byte offset `0` (`u64` stride). -/
def outStoreMap : OutStoreMap := [("RDI", 0)]

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The `horner_q3329` kernel as an owned-RA, two-address `Lprog` (physical
    registers + spill slots), exported under the C symbol `horner_q3329`,
    `abiW := 64` (width-exact `u64` ABI load/store). -/
def hornerQLprog : Lprog :=
  Com.toLprogPhysAbi hornerQCom "horner_q3329"
    (fun _ => none) (fun _ => none) inLoadMap outStoreMap
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (residence := none)
    (abiW := 64)

/-- The owned AT&T `.s` text for `horner_q3329`, rendered straight from the
    owned `Lprog` (no jasminc). -/
def hornerQAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned hornerQLprog

/-- The output path for the field-kernel-emitted `.s`. -/
def hornerQTarget : System.FilePath :=
  "bench/field_kernel_compare/gen_com/horner_q3329.s"

/-- **The byte-correct field-kernel owned-emit driver.** Renders the
    front-compiled `q = 3329` degree-3 Horner kernel to OWNED x86-64
    (`horner_q3329`) and writes it to `gen_com/horner_q3329.s`. -/
def emitHornerQ : IO Unit := do
  IO.FS.createDirAll "bench/field_kernel_compare/gen_com"
  let asm := hornerQAsm
  IO.FS.writeFile hornerQTarget asm
  IO.println s!"FIELD-HORNER-Q emit OK : {hornerQTarget} ({asm.toUTF8.size} bytes, symbol horner_q3329)"

/-- One owned function emitted, named `horner_q3329` (consumability witness). -/
theorem hornerQ_one_func :
    hornerQLprog.lp_funcs.length = 1
      ∧ hornerQLprog.lp_funcs.head?.map Prod.fst = some "horner_q3329" :=
  ⟨rfl, rfl⟩

/-! ## 7. INDEPENDENT plain-`Nat` reference (`% 3329` stepwise Horner) -/

/-- Independent `F_q` multiply: plain `Nat` `(a·b) % 3329`. -/
def fqMulNat (a b : Nat) : Nat := (a * b) % 3329

/-- Independent `F_q` add: plain `Nat` `(a+b) % 3329`. -/
def fqAddNat (a b : Nat) : Nat := (a + b) % 3329

/-- Independent stepwise Horner reference over the SAME input layout as the ABI
    (`g i = inp[i]`): `(((a·x + b)·x + c)·x + d) mod 3329`, reduced after each op. -/
def hornerNatRef (g : Nat → Nat) : Nat :=
  let a := g 0 % 3329; let b := g 1 % 3329; let c := g 2 % 3329
  let d := g 3 % 3329; let x := g 4 % 3329
  fqAddNat (fqMulNat (fqAddNat (fqMulNat (fqAddNat (fqMulNat a x) b) x) c) x) d

/-! ## 8. `denote = spec` vs the independent `% 3329` reference -/

/-- The head-first source valuation: word `i` gets `g i % 3329` (canonical
    residue), `g` the positional input list `[a, b, c, d, x]`. -/
def valOf (g : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  .cons (BitVec.ofNat 64 (g.getD 0 0 % 3329)) (.cons (BitVec.ofNat 64 (g.getD 1 0 % 3329))
    (.cons (BitVec.ofNat 64 (g.getD 2 0 % 3329)) (.cons (BitVec.ofNat 64 (g.getD 3 0 % 3329))
      (.cons (BitVec.ofNat 64 (g.getD 4 0 % 3329)) .nil))))

/-- Denote the front program capped at slot `name` (result word). -/
def frontDenoteAt (name : String) (g : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf g))

/-- The five KAT input vectors (`a, b, c, d, x` at positions 0..4), including
    reducing cases where intermediates exceed `q`, plus 100 generated vectors
    (a small affine PRNG family). -/
def samples : List (List Nat) :=
  [ [2, 3, 4, 5, 10],
    [1000, 2000, 3000, 100, 3000],
    [3328, 3328, 3328, 3328, 3328],
    [1, 1, 1, 1, 2],
    [2500, 1500, 2000, 3000, 2900] ]
  ++ (List.range 100).map (fun s =>
      (List.range 5).map (fun i => (i * (2 * s + 1) + 31 * s + 7) % 3329))

/-- **denote = independent spec.** The front program capped at the output copy
    `q0` denotes the independent plain-`Nat` `% 3329` stepwise Horner reference
    on every sample (5 KAT + 100 generated vectors). -/
theorem horner_denote_spec :
    samples.all (fun g =>
      frontDenoteAt "q0" g
        == some (BitVec.ofNat 64 (hornerNatRef (fun i => g.getD i 0)))) = true := by
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

theorem horner_is_purearith_only : allPureArith hornerQCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last binding** is an identity copy — the `q0` output copy of the
    Horner residue (the positional `OutStoreMap` stores its dst to `out[0]`). -/
theorem horner_last_binding_is_copy :
    ((copyFlags hornerQCom).drop ((copyFlags hornerQCom).length - 1)) = [true] := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.FieldHornerEmitQ

/-- Compiled byte-correct field-Horner owned producer entry point. The
    orchestrator emits it the same way as the other field pipelines
    (`lean_exe`-style). -/
def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.FieldHornerEmitQ.emitHornerQ
