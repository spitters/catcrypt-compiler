/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

set_option autoImplicit false

/-!
# Mersenne-31 field kernels `m31_mul_owned` / `m31_add_owned` / `m31_reduce_owned`, FRONT-COMPILED

The deployed Mersenne-31 (`p = 2³¹ − 1 = 2147483647`, the CircleSTARK /
Plonky3-M31 / Stwo base field) scalar field kernels, sourced end-to-end through
the verified `CProg`-free front — NO hand-built `Com` / `Lcmd` anywhere in the
emit path (the same straight-line route as the GF-MQ
`KernelFromRustcmdFrontEmit` fleet):

```
  body (LowCT: RArrLoad / RScalarSetExpr Mersenne field math / RArrStore)
    --(translateDialectControl)-->  Com catCryptDialect inΓ (.memref 1)
    --(cryptoDialectToJasminCom)--> Com jasminDialect …   (stackLoad/stackStore)
    --(Com.toLprogPhysAbi, [RDI,RSI(,RDX)] memref ABI)--> Lprog
    --(renderLprogAtt)--> bench/m31_compare/gen_com/m31_field_owned.s
```

## The three kernels (SysV pointer ABI, one `u64` cell per pointer)

```c
extern uint64_t *m31_mul_owned(uint64_t *out, const uint64_t *a, const uint64_t *b);
//   out[0] = (a[0] * b[0]) mod p            for a[0], b[0] in [0, p)
extern uint64_t *m31_add_owned(uint64_t *out, const uint64_t *a, const uint64_t *b);
//   out[0] = (a[0] + b[0]) mod p            for a[0], b[0] in [0, p)
extern uint64_t *m31_reduce_owned(uint64_t *out, const uint64_t *x);
//   out[0] = x[0] mod p                     for x[0] < 2^62
```

The field math is the branch-free Mersenne shape (`2³¹ ≡ 1 (mod p)`): multiply
= integer product, double fold `(v & p) + (v >> 31)`, one conditional subtract
via the `0 − (t >> 63)` mask; add = integer sum plus one conditional subtract;
reduce = the standalone double-fold + csub (the M31 analogue of the Baby Bear
`barrettReduceMU`). All constant-time (no data-dependent branch).

## Provenance and proof coverage

The computed folds carry ∀-quantified `denote = spec` + abstract `% p` +
`ZMod (2³¹−1)` field ties through the compile-from-hax leaves
(`CompileFromHaxMersenne31.m31Mul_compiles` / `m31MulFold_eq_mod`,
`CompileFromHaxMersenne31Add.m31Add_compiles` / `m31Reduce_compiles` and their
`_eq_mod` / `_eq_field` ties) — the emit bodies here are the same closed folds
routed through the memref front for the deployed pointer ABI. In-model gates
below: the front translates, lowers, and renders each kernel, and the front
programs denote to the **independent** `Nat` `% p` spec on edge + random
vectors (`native_decide`); the deployed `.s` is gated by the external byte KAT
(`bench/m31_compare/m31_field_kat.c`, small-exhaustive + random vs a direct
`__int128 % p` C reference).

Invoke (in-model gate):   lake env lean CatCrypt/Crypto/SecureCompilation/Mersenne31FrontEmit.lean
Invoke (emit the `.s`):   lake env lean --run bench/m31_compare/m31_field_from_front_emit.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 0. The Mersenne-31 prime and the shared `SExpr` field-math pieces -/

/-- The Mersenne-31 prime `p = 2³¹ − 1`. -/
def m31P : Nat := 2147483647

/-- One Mersenne `2³¹ ≡ 1` fold of the named slot: `(v & p) + (v >> 31)`. -/
def foldE (v : String) : SExpr :=
  .SAdd (.SAnd (.SVar v) (.SLit m31P)) (.SShr (.SVar v) (.SLit 31))

/-- The branch-free conditional subtract of `p`, appended after slot `src`:
    `t := src − p; m := t >> 63; dst := ((0 − m) & p) + t`. -/
def condSubP (dst src : String) : List LowCT :=
  [ .RScalarSetExpr "t" (.SSub (.SVar src) (.SLit m31P)),
    .RScalarSetExpr "m" (.SShr (.SVar "t") (.SLit 63)),
    .RScalarSetExpr dst
      (.SAdd (.SAnd (.SSub (.SLit 0) (.SVar "m")) (.SLit m31P)) (.SVar "t")) ]

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ## 1. The three straight-line bodies -/

/-- `m31_mul_owned` body: load `aw := a[0]`, `bw := b[0]`; integer product,
    Mersenne double fold, conditional subtract; store `out[0] := r`. -/
def mulBody : LowCT := seqAll (
  [ .RScalarSetExpr "ix0" (.SLit 0),
    .RArrLoad ⟨"aw", .TU64⟩ ⟨"a", .TBytes 8⟩ "ix0",
    .RArrLoad ⟨"bw", .TU64⟩ ⟨"b", .TBytes 8⟩ "ix0",
    .RScalarSetExpr "pr" (.SMul (.SVar "aw") (.SVar "bw")),
    .RScalarSetExpr "f1" (foldE "pr"),
    .RScalarSetExpr "f2" (foldE "f1") ]
  ++ condSubP "r" "f2"
  ++ [ .RArrStore ⟨"out", .TBytes 8⟩ "ix0" ⟨"r", .TU64⟩ ])

/-- `m31_add_owned` body: load, integer sum (`< 2³²`, no fold needed),
    conditional subtract; store. -/
def addBody : LowCT := seqAll (
  [ .RScalarSetExpr "ix0" (.SLit 0),
    .RArrLoad ⟨"aw", .TU64⟩ ⟨"a", .TBytes 8⟩ "ix0",
    .RArrLoad ⟨"bw", .TU64⟩ ⟨"b", .TBytes 8⟩ "ix0",
    .RScalarSetExpr "s" (.SAdd (.SVar "aw") (.SVar "bw")) ]
  ++ condSubP "r" "s"
  ++ [ .RArrStore ⟨"out", .TBytes 8⟩ "ix0" ⟨"r", .TU64⟩ ])

/-- `m31_reduce_owned` body: load `xw := x[0]` (`< 2⁶²`, the product domain);
    Mersenne double fold, conditional subtract; store. -/
def reduceBody : LowCT := seqAll (
  [ .RScalarSetExpr "ix0" (.SLit 0),
    .RArrLoad ⟨"xw", .TU64⟩ ⟨"x", .TBytes 8⟩ "ix0",
    .RScalarSetExpr "f1" (foldE "xw"),
    .RScalarSetExpr "f2" (foldE "f1") ]
  ++ condSubP "r" "f2"
  ++ [ .RArrStore ⟨"out", .TBytes 8⟩ "ix0" ⟨"r", .TU64⟩ ])

/-! ## 2. Input contexts + `VarMap`s

`comToLfundef` reverses context↔argument order: `argName j` is context entry
`nArgs−1−j`. To land `out ← argName 0 ← RDI`, `a ← RSI`, `b ← RDX`, `out` must
be bound first (deepest) and the context (head-first) is `[b, a, out]`. -/

/-- Binary-kernel context, head-first `[b, a, out]` (all one-cell memrefs). -/
def inΓ3 : Ctx := [.memref 1, .memref 1, .memref 1]

/-- Binary-kernel `VarMap`: `out` deepest (→ RDI), then `a` (→ RSI), then `b`
    (head, → RDX). -/
def inVM3 : VarMap inΓ3 :=
  ((VarMap.empty.bind "out").bind "a").bind "b"

/-- Unary-kernel context, head-first `[x, out]`. -/
def inΓ2 : Ctx := [.memref 1, .memref 1]

/-- Unary-kernel `VarMap`: `out` deepest (→ RDI), then `x` (head, → RSI). -/
def inVM2 : VarMap inΓ2 :=
  (VarMap.empty.bind "out").bind "x"

/-! ## 3. The front-emitted dialect programs (each returns the stored `out`) -/

/-- Push a body through the `CProg`-free control front at context `Γ`/`vm` and
    cap with `ret out` (the post-store memref). `none` if the front declines. -/
def frontCom {Γ : Ctx} (vm : VarMap Γ) (body : LowCT) :
    Option (Com catCryptDialect Γ (.memref 1)) :=
  match translateDialectControl vm body with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 1, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted `m31_mul_owned` dialect program. -/
def mulFrontCom : Option (Com catCryptDialect inΓ3 (.memref 1)) := frontCom inVM3 mulBody
/-- The front-emitted `m31_add_owned` dialect program. -/
def addFrontCom : Option (Com catCryptDialect inΓ3 (.memref 1)) := frontCom inVM3 addBody
/-- The front-emitted `m31_reduce_owned` dialect program. -/
def reduceFrontCom : Option (Com catCryptDialect inΓ2 (.memref 1)) := frontCom inVM2 reduceBody

/-! ## 4. Lowering to jasmin + the owned multi-pointer memref ABI export -/

/-- Lower a front dialect program to a `Com jasminDialect`
    (`memrefGetDyn`/`memrefSetDyn` → `stackLoad`/`stackStore`). -/
def toJasmin {Γ : Ctx} (com : Option (Com catCryptDialect Γ (.memref 1))) :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match com with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)

/-- Render an owned `Lprog` for a lowered kernel under the SysV pointer ABI
    (`abiArgs`, one `u64` cell per pointer; `inLoadMap = none`,
    `outStoreMap = []`). -/
def toAsm (name : String) (abiArgs : List String)
    (j : Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t)) :
    Option String :=
  (j.map (fun s =>
    Com.toLprogPhysAbi s.2.2 name
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := abiArgs) (abiTyin := abiArgs.map (fun _ => 64))
      (residence := none) (abiW := 0)
      -- 2-pointer `reduce`: without the pin the late-born OUT arg coalesces
      -- onto the IN arg's register and the SIB reload reads the OUT qsave
      -- slot (KAT-caught). Pinning all three kernels keeps one export shape.
      (forceLivePin := true))).map renderLprogAtt

/-- The owned AT&T `.s` text of `m31_mul_owned` (RDI = out, RSI = a, RDX = b). -/
def mulAsm : Option String :=
  toAsm "m31_mul_owned" ["RDI", "RSI", "RDX"] (toJasmin mulFrontCom)
/-- The owned AT&T `.s` text of `m31_add_owned` (RDI = out, RSI = a, RDX = b). -/
def addAsm : Option String :=
  toAsm "m31_add_owned" ["RDI", "RSI", "RDX"] (toJasmin addFrontCom)
/-- The owned AT&T `.s` text of `m31_reduce_owned` (RDI = out, RSI = x). -/
def reduceAsm : Option String :=
  toAsm "m31_reduce_owned" ["RDI", "RSI"] (toJasmin reduceFrontCom)

/-! ## 5. Gates: the front succeeds and every kernel renders -/

/-- The three bodies front-compile (`translateDialectControl` + `ret out`). -/
theorem frontCom_isSome :
    mulFrontCom.isSome ∧ addFrontCom.isSome ∧ reduceFrontCom.isSome := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The three kernels lower end-to-end to `Com jasminDialect` and render to
    owned `.s` (no hand `Com`/`Lcmd`, no jasminc). -/
theorem kernelAsm_isSome :
    mulAsm.isSome ∧ addAsm.isSome ∧ reduceAsm.isSome := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## 6. In-model `denote = spec` vs the INDEPENDENT `Nat` `% p` spec

The valuations bind each pointer's single cell; the denotation returns the
post-store `out` memref, whose cell `0` is the result. The specs are computed
directly with `Nat` `%` — independent of the emitted fold shape. -/

/-- Binary-kernel valuation, head-first `[b, a, out]` (matches `inΓ3`). -/
def encodeVal3 (av bv : BitVec 64) : @Ctxt.Valuation catCryptDialect _ inΓ3 :=
  .cons (fun _ => bv) (.cons (fun _ => av) (.cons (fun _ => (0 : BitVec 64)) .nil))

/-- Unary-kernel valuation, head-first `[x, out]` (matches `inΓ2`). -/
def encodeVal2 (xv : BitVec 64) : @Ctxt.Valuation catCryptDialect _ inΓ2 :=
  .cons (fun _ => xv) (.cons (fun _ => (0 : BitVec 64)) .nil)

/-- Denote a binary front kernel and read out cell `0`. -/
def frontDenote3 (com : Option (Com catCryptDialect inΓ3 (.memref 1)))
    (av bv : BitVec 64) : Option (BitVec 64) :=
  com.map (fun c => c.denote (encodeVal3 av bv) ⟨0, by decide⟩)

/-- Denote the unary front kernel and read out cell `0`. -/
def frontDenote2 (com : Option (Com catCryptDialect inΓ2 (.memref 1)))
    (xv : BitVec 64) : Option (BitVec 64) :=
  com.map (fun c => c.denote (encodeVal2 xv) ⟨0, by decide⟩)

/-- Residue-domain sample pairs: edges (`0`, `1`, `p−1`, `p−2`, `2³⁰`) and
    pseudo-random residues. -/
def samplePairs : List (Nat × Nat) :=
  [ (0, 0), (0, 1), (1, 1), (2147483646, 2147483646), (2147483646, 1),
    (2147483645, 2147483646), (1073741824, 1073741825),
    (123456789, 987654321), (305419896, 2059293160), (31415926, 2718281828 % 2147483647) ]

/-- Product-domain (`< 2⁶²`) sample values for the reduce kernel. -/
def sampleReduce : List Nat :=
  [ 0, 1, 2147483646, 2147483647, 2147483648, 4294967295, 4611686018427387903,
    2147483646 * 2147483646, 123456789 * 987654321 ]

/-- **`m31_mul_owned` denote = independent spec.** The front-compiled multiply
    denotes the direct `Nat` `(a·b) % p` on every sample pair. -/
theorem mul_denote_spec :
    samplePairs.all (fun (av, bv) =>
      frontDenote3 mulFrontCom (BitVec.ofNat 64 av) (BitVec.ofNat 64 bv)
        == some (BitVec.ofNat 64 (av * bv % m31P))) = true := by native_decide

/-- **`m31_add_owned` denote = independent spec.** The front-compiled add
    denotes the direct `Nat` `(a+b) % p` on every sample pair. -/
theorem add_denote_spec :
    samplePairs.all (fun (av, bv) =>
      frontDenote3 addFrontCom (BitVec.ofNat 64 av) (BitVec.ofNat 64 bv)
        == some (BitVec.ofNat 64 ((av + bv) % m31P))) = true := by native_decide

/-- **`m31_reduce_owned` denote = independent spec.** The front-compiled reduce
    denotes the direct `Nat` `x % p` on every product-domain sample. -/
theorem reduce_denote_spec :
    sampleReduce.all (fun xv =>
      frontDenote2 reduceFrontCom (BitVec.ofNat 64 xv)
        == some (BitVec.ofNat 64 (xv % m31P))) = true := by native_decide

/-! ## 7. Emit driver -/

/-- Write the three front-generated kernels into ONE owned `.s`
    (`bench/m31_compare/gen_com/m31_field_owned.s`). -/
def emit (path : System.FilePath) : IO Unit := do
  match mulAsm, addAsm, reduceAsm with
  | some ma, some aa, some ra =>
      IO.FS.writeFile path (ma ++ "\n" ++ aa ++ "\n" ++ ra)
  | _, _, _ =>
      throw (IO.userError "front-compile of the m31 field kernels failed (front/lowering declined)")

end CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit
