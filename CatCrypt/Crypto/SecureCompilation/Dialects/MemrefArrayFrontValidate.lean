/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom

set_option autoImplicit false

/-!
# Front-emitted dynamic-index memref load/store reaching real `stackLoad`/`LOADIDX`

This module validates the **Gap B** front path: a multi-pointer GF-MQ-shaped body
whose array accesses (`RArrLoad` / `RArrStore`) are lowered by the `CProg`-free
dialect front (`translateDialectControl`, via the `arrLoadCont` / `arrStoreCont`
combinators) to the dialect's `memrefGetDyn` / `memrefSetDyn` op, and then by
`DialectToJasminCom.cryptoDialectToJasminCom` to a real jasmin `stackLoad` /
`stackStore` (the SIB `LOADIDX` / `STOREIDX`) — *not* the opaque
`extCall "arrLoadDyn"` / `"arrStoreDyn"` leaf.

The body is the canonical GF-MQ access shape
`out[i] = f(s[i], mat[i])` with `s`, `mat`, `out` three **distinct memref arrays**
(bound to distinct context slots — the multi-pointer ABI binds them to distinct
arg pointers downstream), and `f` a scalar word op (here `XOR`, authored through
the already-validated `RScalarSetExpr` arm). A read-back load of `out[i]` after the
store exercises the store→load roundtrip through the real memref ops.

`denote = spec` below is the load-bearing gate: had the front taken the opaque
`extCall` path, the dialect denotation would be `CryptoTy.default` (zero / opaque),
so matching the schoolbook reference on non-trivial inputs witnesses that the
**memref** ops were emitted. A syntactic `stackLoad`/`stackStore`-presence scan of
the lowered jasmin program corroborates this at the byte-emit level.

Invoke (in-model gate only):
  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/MemrefArrayFrontValidate.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.MemrefArrayFrontValidate

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located)

/-! ## 0. Dimension and slot types -/

/-- The memref array width (number of 64-bit cells). -/
def memN : Nat := 4

/-- A tower type whose `encodeTy` is exactly `.memref memN` (`TBytes (8 * memN)`),
    so the store arm's `encodeTy arr.locDst = .memref memN` side-condition holds. -/
def arrTy : CatCrypt.Crypto.Jasmin.LowCT.TowerType := .TBytes (8 * memN)

/-! ## 1. The two-pointer GF-MQ access body

`s`, `mat`, `out` are three distinct memref slots; `i0` is the runtime index. -/

/-- `sv := s[i0]; mv := mat[i0]; ov := sv ^ mv; out[i0] := ov; chk := out[i0]`. -/
def gfBody : LowCT :=
  .RSeq (.RArrLoad ⟨"sv", .TU64⟩ ⟨"s", arrTy⟩ "i0")
  (.RSeq (.RArrLoad ⟨"mv", .TU64⟩ ⟨"mat", arrTy⟩ "i0")
  (.RSeq (.RScalarSetExpr "ov" (.SXor (.SVar "sv") (.SVar "mv")))
  (.RSeq (.RArrStore ⟨"out", arrTy⟩ "i0" ⟨"ov", .TU64⟩)
  (.RArrLoad ⟨"chk", .TU64⟩ ⟨"out", arrTy⟩ "i0"))))

/-! ## 2. Input context + `VarMap`

Context order (head first): `s`, `mat`, `out` (each `.memref memN`), then `i0`
(`.sword 64`). -/

/-- The four input slots: three memref arrays + the index word. -/
def inΓ : Ctx := [.memref memN, .memref memN, .memref memN, .sword 64]

/-- `VarMap` binding `s`/`mat`/`out`/`i0` to the input slots. -/
def inVM : VarMap inΓ :=
  (((VarMap.empty.bind "i0").bind "out").bind "mat").bind "s"

/-! ## 3. The front-emitted dialect program (returns the read-back word `chk`) -/

/-- Push `gfBody` through the `CProg`-free control front and cap with `ret chk`. -/
def frontComResult : Option (Com catCryptDialect inΓ (.sword 64)) :=
  match translateDialectControl inVM gfBody with
  | some r =>
      match r.vm.lookup "chk" with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-! ## 4. Syntactic witness: the lowered jasmin program uses real stack ops -/

/-- Does any node of a jasmin `Com` carry a `stackLoad` / `stackStore` op? -/
def comHasStackOp {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Bool
  | .ret _ => false
  | .var e body =>
      (match e.op with
       | .stackLoad _ _ => true
       | .stackStore _ _ => true
       | _ => false) || comHasStackOp body

/-- The lowered jasmin program (`none` if the front declines or lowering fails). -/
def loweredJasmin : Option (Σ Γ : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γ t) :=
  match frontComResult with
  | some com =>
      match DialectToJasminCom.cryptoDialectToJasminCom com with
      | some jcom => some ⟨_, _, jcom⟩
      | none => none
  | none => none

/-! ## 5. Independent schoolbook reference -/

/-- `chk = s[i0 mod memN] ^ mat[i0 mod memN]`. -/
def specChk (s mat : Fin memN → BitVec 64) (i0 : BitVec 64) : BitVec 64 :=
  s ⟨i0.toNat % memN, Nat.mod_lt _ (by decide)⟩ ^^^ mat ⟨i0.toNat % memN, Nat.mod_lt _ (by decide)⟩

/-- The input valuation: `s`, `mat`, `out`, `i0`. -/
def encodeVal (s mat out : Fin memN → BitVec 64) (i0 : BitVec 64) :
    @Ctxt.Valuation catCryptDialect _ inΓ :=
  .cons s (.cons mat (.cons out (.cons i0 .nil)))

/-- Denote the front program at a packed input. -/
def frontDenote (s mat out : Fin memN → BitVec 64) (i0 : BitVec 64) : Option (BitVec 64) :=
  frontComResult.map (fun com => com.denote (encodeVal s mat out i0))

/-! ## 6. Gates -/

/-- The body translates through the `CProg`-free control front. -/
theorem gfBody_translates :
    (translateDialectControlTop inVM gfBody).isSome := by native_decide

/-- The front emits a result program. -/
theorem frontComResult_isSome : frontComResult.isSome := by native_decide

/-- The front-emitted dialect program lowers end-to-end to a `Com jasminDialect`. -/
theorem frontComResult_lowers :
    (frontComResult.bind DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  native_decide

/-- **The lowered jasmin program contains real `stackLoad`/`stackStore` ops** — the
    memref path was taken, not the opaque `extCall "arrLoadDyn"`/`"arrStoreDyn"`. -/
theorem loweredJasmin_has_stackOp :
    (loweredJasmin.map (fun s => comHasStackOp s.2.2)) = some true := by native_decide

/-! ### `denote = spec` on representative inputs -/

/-- All-zero. -/
example : frontDenote (fun _ => 0) (fun _ => 0) (fun _ => 0) 0
    = some (specChk (fun _ => 0) (fun _ => 0) 0) := by native_decide

/-- Distinct per-cell values, index 0. -/
example :
    frontDenote (fun j => BitVec.ofNat 64 (j.val + 1)) (fun j => BitVec.ofNat 64 (10 * j.val + 3))
        (fun _ => 0) 0
      = some (specChk (fun j => BitVec.ofNat 64 (j.val + 1))
          (fun j => BitVec.ofNat 64 (10 * j.val + 3)) 0) := by native_decide

/-- Index 2 (exercises the runtime SIB index ≠ 0). -/
example :
    frontDenote (fun j => BitVec.ofNat 64 (j.val + 1)) (fun j => BitVec.ofNat 64 (10 * j.val + 3))
        (fun _ => 0) 2
      = some (specChk (fun j => BitVec.ofNat 64 (j.val + 1))
          (fun j => BitVec.ofNat 64 (10 * j.val + 3)) 2) := by native_decide

/-- Index ≥ memN (exercises the modulo wrap) with pseudo-random cells. -/
example :
    frontDenote (fun j => BitVec.ofNat 64 (j.val * 0x9e3779b9 + 0x1234))
        (fun j => BitVec.ofNat 64 (j.val * 0x7f4a7c15 + 0xabcd)) (fun _ => 0) 7
      = some (specChk (fun j => BitVec.ofNat 64 (j.val * 0x9e3779b9 + 0x1234))
          (fun j => BitVec.ofNat 64 (j.val * 0x7f4a7c15 + 0xabcd)) 7) := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.MemrefArrayFrontValidate
