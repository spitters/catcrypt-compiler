/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom

set_option autoImplicit false

/-!
# Width-parametric scalar-`SExpr` front (prototype: 32-bit cross-lane crypto)

The production scalar front (`TranslateDialectDirectArms.lowerSExpr`) hardwires
every emitted dialect word op to width `64` (`.bvAdd 64`, `.bvShiftL 64 k`, …) and
only accepts `.sword 64` input slots (`lookupU64`). That is fine for the
lane-independent word-packing kernels (Hawk), but it cannot express genuine
32-bit crypto with CROSS-LANE mixing — the ChaCha quarter-round rotations, the
SHA-256 Σ/Ch/Maj words, the BLAKE3 g-function — because those need a real 32-bit
register ALU: 32-bit wrapping arithmetic and `rotl32`.

The `catCryptDialect` op set is ALREADY width-parametric — every op carries a
`(w : Nat)` and denotes over `BitVec w` (`CatCryptDialect.lean`), and the jasmin
lowering `mapTy (.sword w) = .reg w` is likewise width-generic. So the ONLY place
the width `64` is baked in is the FRONT lowering. This file adds a
**width-parametric** copy of that lowering — `lowerSExprW (w : Nat)` — ADDITIVELY:
the 64-bit `lowerSExpr` is untouched (byte-identical, everyone keeps building on
it), and `lowerSExprW 64` is behaviourally the same function.

It then PROTOTYPE-flips one representative cross-lane kernel: the ChaCha20
quarter-round's first rotation step `d' = rotl32(d ^ (a + b), 16)` as a
front-generated `.sword 32` body, and checks computationally that

1. it lowers (`isSome`) to a `Com catCryptDialect` at width 32;
2. that program lowers on to a `Com jasminDialect` (reaches owned `.s`);
3. it denotes with genuine 32-bit wrap to `rotl32(d ^ (a + b), 16)` on samples;
4. `rotl32` is faithfully expressed as `(x <<< k) ^ (x >>> (32-k))` — the two
   halves are disjoint, so the front-expressible `SXor`/`SShl`/`SShr` combination
   equals the native `BitVec.rotateLeft` (`bv_decide`, universal over all inputs).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. Width-parametric front helpers (additive twins of the `…U64`/`64` ones)

Each is the exact `lowerSExpr` helper with the hardwired `64` replaced by a width
parameter `w`. Instantiating `w := 64` recovers the production behaviour. -/

/-- Width-parametric `lookupU64`: look up a `.sword w` scalar slot by name. -/
def lookupUW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (name : String) :
    Option (CVar Γ (.sword w)) :=
  match vm.lookup name with
  | some ⟨.sword w', v⟩ =>
      if h : w' = w then some (h ▸ v) else none
  | _ => none

/-- Width-parametric `pushVarBind`: append one `varBind` of a `.sword w` expr. -/
def pushVarBindW (w : Nat) {Γ : Ctx} (o : DTransOut Γ)
    (e : Expr catCryptDialect o.Γ' (.sword w)) (nm : String) : DTransOut Γ :=
  { Γ' := .sword w :: o.Γ',
    cont := ComCont.comp o.cont (ComCont.varBind e),
    vm := o.vm.bind nm }

/-! ## 2. The width-parametric SExpr lowering

Mirrors `TranslateDialectDirectArms.lowerSExpr` with `64 ↦ w` on every op and
slot. Covers the straight-line arithmetic / bitwise / shift arms — exactly the
alphabet the cross-lane kernels (ChaCha, SHA-256, BLAKE3) use. The signed /
declined arms match the production front. -/
def lowerSExprW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) :
    SExpr → Option (DTransOut Γ × String × Nat)
  | .SVar x =>
      match lookupUW w vm x with
      | some _ => some (⟨Γ, ComCont.id, vm⟩, x, cnt)
      | _ => none
  | .SLit n =>
      let e : Expr catCryptDialect Γ (.sword w) :=
        { op := .bvConst w (BitVec.ofNat w n), retTy_eq := rfl, args := .nil }
      some (pushVarBindW w ⟨Γ, ComCont.id, vm⟩ e (tmpName cnt), tmpName cnt, cnt + 1)
  | .SAdd a b =>
      match lowerSExprW w vm cnt a with
      | none => none
      | some r =>
        match lowerSExprW w r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupUW w s.1.vm r.2.1, lookupUW w s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword w) :=
                { op := .bvAdd w, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBindW w (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SSub a b =>
      match lowerSExprW w vm cnt a with
      | none => none
      | some r =>
        match lowerSExprW w r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupUW w s.1.vm r.2.1, lookupUW w s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword w) :=
                { op := .bvSub w, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBindW w (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SMul a b =>
      match lowerSExprW w vm cnt a with
      | none => none
      | some r =>
        match lowerSExprW w r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupUW w s.1.vm r.2.1, lookupUW w s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword w) :=
                { op := .bvMul w, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBindW w (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SAnd a b =>
      match lowerSExprW w vm cnt a with
      | none => none
      | some r =>
        match lowerSExprW w r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupUW w s.1.vm r.2.1, lookupUW w s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword w) :=
                { op := .bvAnd w, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBindW w (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SXor a b =>
      match lowerSExprW w vm cnt a with
      | none => none
      | some r =>
        match lowerSExprW w r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupUW w s.1.vm r.2.1, lookupUW w s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword w) :=
                { op := .bvXor w, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBindW w (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SShl a b =>
      match lowerSExprW w vm cnt a with
      | none => none
      | some r =>
        match lowerSExprW w r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupUW w s.1.vm r.2.1, lookupUW w s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword w) :=
                match b with
                | .SLit k =>
                    { op := .bvShiftL w k, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
                | _ =>
                    { op := .bvShiftLV w, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBindW w (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SShr a b =>
      match lowerSExprW w vm cnt a with
      | none => none
      | some r =>
        match lowerSExprW w r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupUW w s.1.vm r.2.1, lookupUW w s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword w) :=
                match b with
                | .SLit k =>
                    { op := .bvShiftR w k, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
                | _ =>
                    { op := .bvShiftRV w, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBindW w (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | _ => none

/-! ## 3. Prototype: a 32-bit ChaCha20 quarter-round rotation step

The ChaCha20 quarter-round (RFC 8439 §2.1) is the archetypal CROSS-LANE 32-bit
kernel: `a += b; d ^= a; d = rotl32(d, 16); …`. Its first rotation step computes
`d' = rotl32(d ^ (a + b), 16)`, where `+` is 32-bit wrapping add and `rotl32` is a
32-bit rotate — neither expressible through the `.sword 64` front (a 64-bit add
does not wrap at bit 32, and a 64-bit shift pair does not rotate within 32 bits).

`rotl32(x, k)` has no `SExpr` constructor, but it is expressible as
`(x <<< k) ^ (x >>> (32 - k))`: at width 32 the two shifted halves occupy DISJOINT
bit ranges, so their `^` (= `|` = `+`) reassembles the rotate. We write the whole
step as one `SExpr` over `.sword 32` slots `a`, `b`, `d`. -/

/-- `inner = d ^ (a + b)` (32-bit). -/
def qrInner : SExpr := .SXor (.SVar "d") (.SAdd (.SVar "a") (.SVar "b"))

/-- `d' = rotl32(inner, 16) = (inner << 16) ^ (inner >> 16)`, front-expressible. -/
def qrRotStep : SExpr := .SXor (.SShl qrInner (.SLit 16)) (.SShr qrInner (.SLit 16))

/-- Input context: three `.sword 32` scalar slots `a` (`.here`), `b`, `d`. -/
def qrΓ : Ctx := [.sword 32, .sword 32, .sword 32]

/-- `VarMap` binding `a`, `b`, `d` to the three 32-bit slots. -/
def qrVM : VarMap qrΓ := (((VarMap.empty.bind "d").bind "b").bind "a")

/-- The front-emitted 32-bit dialect program returning the result word. -/
def qrProg : Option (Com catCryptDialect qrΓ (.sword 32)) :=
  match lowerSExprW 32 qrVM 0 qrRotStep with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword 32, v⟩ => r.1.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- Denote the front-emitted 32-bit program at inputs `av`, `bv`, `dv`. -/
def qrDenote (av bv dv : BitVec 32) : Option (BitVec 32) :=
  qrProg.map (fun com => com.denote (.cons av (.cons bv (.cons dv .nil))))

/-- The pure 32-bit spec: `rotl32(d ^ (a + b), 16)`, using the NATIVE rotate. -/
def qrSpec (av bv dv : BitVec 32) : BitVec 32 :=
  (dv ^^^ (av + bv)).rotateLeft 16

/-! ### 3a. The 32-bit body lowers (reaches the dialect and owned `.s`) -/

/-- The ChaCha rotation step lowers to a `Com catCryptDialect` at width 32. -/
theorem qrProg_isSome : qrProg.isSome := by native_decide

/-- …and that program lowers on to a `Com jasminDialect` — i.e. it reaches the
    owned x86 backend through `cryptoDialectToJasminCom` (32-bit `reg`s). -/
theorem qrProg_lowers :
    (qrProg.bind DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  native_decide

/-! ### 3b. `denote = spec` with genuine 32-bit wrap (the correctness gate) -/

-- A worked value: a=b=0x80000000 forces the 32-bit add to WRAP to 0 (a 64-bit
-- add would give 0x1_00000000 and change the result), so this sample witnesses
-- that the emitted program truly computes mod 2^32, not mod 2^64.
example : qrDenote 0x80000000 0x80000000 0x0000FFFF
        = some (qrSpec 0x80000000 0x80000000 0x0000FFFF) := by native_decide
example : qrDenote 0x12345678 0x9ABCDEF0 0x0F0F0F0F
        = some (qrSpec 0x12345678 0x9ABCDEF0 0x0F0F0F0F) := by native_decide
example : qrDenote 0xFFFFFFFF 0x00000001 0xDEADBEEF
        = some (qrSpec 0xFFFFFFFF 0x00000001 0xDEADBEEF) := by native_decide
example : qrDenote 0 0 0 = some (qrSpec 0 0 0) := by native_decide

/-! ### 3c. `rotl32` is faithfully expressed — universal, not just on samples

The load-bearing identity: the front-expressible `(x << k) ^ (x >> (32-k))` at
width 32 equals the native `BitVec.rotateLeft k`, for every `x`. `bv_decide`
proves it over all `2^32` inputs (SAT, not enumeration). Shown for the four
ChaCha rotate constants 16/12/8/7. -/

theorem rotl32_16 (x : BitVec 32) : (x <<< 16) ^^^ (x >>> 16) = x.rotateLeft 16 := by
  bv_decide
theorem rotl32_12 (x : BitVec 32) : (x <<< 12) ^^^ (x >>> 20) = x.rotateLeft 12 := by
  bv_decide
theorem rotl32_8 (x : BitVec 32) : (x <<< 8) ^^^ (x >>> 24) = x.rotateLeft 8 := by
  bv_decide
theorem rotl32_7 (x : BitVec 32) : (x <<< 7) ^^^ (x >>> 25) = x.rotateLeft 7 := by
  bv_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype
