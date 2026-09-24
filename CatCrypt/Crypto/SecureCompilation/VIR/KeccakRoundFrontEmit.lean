/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit

/-!
# PROTOTYPE: one Keccak-p[1600] round, FRONT-COMPILED

This is a bounded prototype (NOT a deployed artifact) demonstrating that a single
Keccak round — θ (column parities + D application), ρ∘π (lane permute + rotate),
χ (nonlinear), ι (round constant) — is expressible through the verified
front and lowers to a `Com jasminDialect`, exactly the way
`AsconEmit.asconPbCom` front-generates the Ascon permutation (whose S-box is
itself the bit-sliced Keccak-χ). The mirror is:

```
  keccakRoundBody (LowCT: RScalarSetExpr u64 word math over the 25 state lanes)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  keccakRoundFrontCom : Com jasminDialect
```

All five step mappings use only `SXor` / `SAnd` / `SShl` / `SShr`:
* θ-C: `c[x] = a[x] ⊕ a[x+5] ⊕ a[x+10] ⊕ a[x+15] ⊕ a[x+20]` (nested `SXor`);
* θ-D: `d[x] = c[x-1] ⊕ rotl(c[x+1],1)`, then `a'[i] = a[i] ⊕ d[i%5]`;
* ρ∘π: `b[y,(2x+3y)%5] = rotl(a'[i], r[i])`, `rotl(v,n) = (v<<n) ⊕ (v>>(64-n))`;
* χ:   `ch[i] = b[i] ⊕ ((¬b[i+1]) ∧ b[i+2])`, `¬v = v ⊕ 0xFFFF…FF`;
* ι:   `o[0] = ch[0] ⊕ RC[0]`, `o[i] = ch[i]` (i≠0).

The round constants `RC` and rotate offsets `r` are reused from `KeccakEmit`
(param defs — NOT the hand-built `Com` builders). This module does NOT touch
`KeccakEmit.keccakF1600Com`; it is an isolated feasibility check for
re-sourcing that Com through the front.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundFrontEmit

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

set_option autoImplicit false

/-- The `reg 64` dialect type, abbreviated. -/
abbrev r64 : JasminTy := .reg 64

/-- The all-ones NOT mask immediate. -/
abbrev maskImm : Nat := 0xFFFFFFFFFFFFFFFF

/-! ## Slot names -/

/-- State-lane input name `a{i}` (lane `i = x + 5y`). -/
def aN (i : Nat) : String := "a" ++ toString i
/-- θ column-parity temporary `c{x}`. -/
def cN (x : Nat) : String := "c" ++ toString x
/-- θ D-value temporary `d{x}`. -/
def dN (x : Nat) : String := "d" ++ toString x
/-- θ-applied lane temporary `p{i}` (`a'[i] = a[i] ⊕ D[i%5]`). -/
def pN (i : Nat) : String := "p" ++ toString i
/-- ρ∘π output lane temporary `b{i}`. -/
def bN (i : Nat) : String := "b" ++ toString i
/-- χ output temporary `h{i}`. -/
def hN (i : Nat) : String := "h" ++ toString i
/-- Output-copy slot name `o{i}` (the last-`nOut`-bindings convention). -/
def oN (i : Nat) : String := "o" ++ toString i

/-! ## SExpr helpers -/

/-- NOT of slot `v`: `v ⊕ 0xFFFF…FF`. -/
def notE (v : String) : SExpr := .SXor (.SVar v) (.SLit maskImm)

/-- Rotate-LEFT of slot `v` by `n` (`0 < n < 64`): `(v << n) | (v >> (64-n))`,
    the two halves disjoint so `|` = `⊕`. -/
def rotLE (v : String) (n : Nat) : SExpr :=
  .SXor (.SShl (.SVar v) (.SLit n)) (.SShr (.SVar v) (.SLit (64 - n)))

/-- Fold `SXor` over a nonempty list of variable reads. -/
def xorVars : List String → SExpr
  | [] => .SLit 0
  | [n] => .SVar n
  | n :: ns => .SXor (.SVar n) (xorVars ns)

/-! ## The five step mappings as `RScalarSetExpr` statements -/

/-- θ column parity `c[x] = ⊕_{y} a[x+5y]`. -/
def cStmt (x : Nat) : LowCT :=
  .RScalarSetExpr (cN x) (xorVars [aN x, aN (x + 5), aN (x + 10), aN (x + 15), aN (x + 20)])

/-- θ D-value `d[x] = c[(x+4)%5] ⊕ rotl(c[(x+1)%5], 1)`. -/
def dStmt (x : Nat) : LowCT :=
  .RScalarSetExpr (dN x) (.SXor (.SVar (cN ((x + 4) % 5))) (rotLE (cN ((x + 1) % 5)) 1))

/-- θ application `p[i] = a[i] ⊕ d[i%5]`. -/
def pStmt (i : Nat) : LowCT :=
  .RScalarSetExpr (pN i) (.SXor (.SVar (aN i)) (.SVar (dN (i % 5))))

/-- ρ∘π lane `b[(y%5)+5*((2x+3y)%5)] = rotl(p[i], r[i])` (`x=i%5, y=i/5`). -/
def bStmt (i : Nat) : LowCT :=
  let x := i % 5
  let y := i / 5
  let n := KeccakEmit.rhoOffset i
  let bIdx := (y % 5) + 5 * ((2 * x + 3 * y) % 5)
  .RScalarSetExpr (bN bIdx) (if n == 0 then .SVar (pN i) else rotLE (pN i) n)

/-- χ lane `h[i] = b[i] ⊕ ((¬b[(x+1)%5+5y]) ∧ b[(x+2)%5+5y])` (`x=i%5, y=i/5`). -/
def hStmt (i : Nat) : LowCT :=
  let x := i % 5
  let y := i / 5
  let i1 := (x + 1) % 5 + 5 * y
  let i2 := (x + 2) % 5 + 5 * y
  .RScalarSetExpr (hN i) (.SXor (.SVar (bN i)) (.SAnd (notE (bN i1)) (.SVar (bN i2))))

/-- ι + output copy: `o[0] = h[0] ⊕ RC[0]`, `o[i] = h[i]` for `i ≠ 0`. Each is one
    binding, so the **last 25 bindings** carry the 25 output lanes in order. -/
def oStmt (i : Nat) : LowCT :=
  if i == 0 then
    .RScalarSetExpr (oN 0) (.SXor (.SVar (hN 0)) (.SLit (KeccakEmit.roundConst 0)))
  else
    .RScalarSetExpr (oN i) (.SVar (hN i))

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- One full Keccak round body: θ-C, θ-D, θ-apply, ρ∘π, χ, ι+output. -/
def keccakRoundBody : LowCT :=
  seqAll (
    (List.range 5).map cStmt
    ++ (List.range 5).map dStmt
    ++ (List.range 25).map pStmt
    ++ (List.range 25).map bStmt
    ++ (List.range 25).map hStmt
    ++ (List.range 25).map oStmt)

/-! ## Source context + `VarMap` (25 lanes) -/

/-- Input context length: the 25 state lanes (immediates are baked as literals). -/
abbrev nInputs : Nat := 25

/-- The 25 input word names, head-first: `a0 … a24`. -/
def wordNames : List String := (List.range nInputs).map aN

/-- Bind a name list onto a `replicate`-`sword 64` context, first name = head. -/
def bindAll : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindAll ns).bind n

/-- The source context: 25 `u64` scalar lanes. -/
def srcCtx : Ctx := List.replicate nInputs (.sword 64)

/-- The source `VarMap` (lane 0 = `a0` at the head). -/
def srcVM : VarMap srcCtx := bindAll wordNames

/-- The input context of the lowered `Com`: 25 `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate nInputs r64

/-! ## Front-emit + lower -/

/-- Push the round body through the control front and cap with the
    named output result. `none` if the front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM keccakRoundBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted round, lowered to the jasmin dialect. -/
def keccakRoundLoweredOpt :=
  (frontComAt (oN 24)).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- **The round front translates and lowers end-to-end.** -/
theorem keccakRoundLowered_isSome : keccakRoundLoweredOpt.isSome := by native_decide

/-- The front-generated Keccak round `Com jasminDialect` — NOT hand-built. -/
def keccakRoundFrontCom : Com jasminDialect inCtxt r64 :=
  keccakRoundLoweredOpt.get keccakRoundLowered_isSome

/-! ## Structural gates (cheap in-model, mirroring `AsconEmit`) -/

/-- Every binding is a pure scalar-arith op — no `extCall`/`stackLoad`/`stackStore`. -/
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

theorem keccakRoundFront_is_purearith_only : allPureArith keccakRoundFrontCom = true := by
  native_decide

/-- Binding count of the lowered round `Com`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-- Record the lowered round's binding count (size tractability datum). -/
def keccakRoundFront_bindings : Nat := comBindings keccakRoundFrontCom

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundFrontEmit
