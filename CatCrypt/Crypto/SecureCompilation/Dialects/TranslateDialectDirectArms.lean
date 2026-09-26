/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCT
public meta import CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect


@[expose] public section
set_option autoImplicit false

/-!
# Multi-binding arms of the direct front (`translateDialectFull`)

`TranslateDialectDirect.translateDialect` lowers the core straight-line
`LowCT` arms (`RSkip`, `RSeq`, `RScalarSet`, `RLetU64Zero`, `RBlock`) to a
`Com catCryptDialect` recursion and declines every other arm to `none`.

This module extends that front to the multi-binding arms — the ones whose
image is not a single `varBind` of a `bvConst`, but one or more opaque
`extCall` leaf bindings (the crypto leaf calls) or a `memrefSet` chain:

* `RCall`            — one `extCall fname` rebinding the destination, or, on a name
  of `inlineArithTable` into a `.TFp` slot on two six-limb slots, the inline
  arithmetic lowering of §1e;
* `RSelect`          — on 64-bit word slots, the comparison and conditional
  select of §1d; on any other slots, one opaque `extCall "select"` over the selector and
  the two sources;
* `RCallDstThreaded` — one `extCall fname` with `dst :: args`;
* `RTupleLoad`       — one `extCall "tupleLoad:i"`;
* `RArrLoadLit` / `RArrStoreLit` — a `bvConst` index temporary and a
  `memrefGetDyn` / `memrefSetDyn` `varBind` when the array has tower type
  `TArr _ .TU64` and is bound as `.memref n`, and the destination (load) or source
  (store) is a 64-bit word; otherwise one `extCall "arrLoad:i"` / `"arrStore:i"`.
  `encodeTy` binds byte and `u32` arrays as `.memref` too, and the direct route
  (`LowCTToJasmin.arrLitElemWS`) reads their element `idx` at the array's own
  width, not word `idx`, so those arrays take the opaque leaf;
* `RArrLoad` / `RArrStore` — a `memrefGetDyn` / `memrefSetDyn` `varBind` when the
  operands match the dynamic-index memref ABI (array `.memref n`, index/value
  `.sword 64`, word destination), else one `extCall "arrLoadDyn"` / `"arrStoreDyn"`
  (see §1c);
* `RLimbStore`       — a `bvConst`; `memrefSet` pair on a bound memref
  destination; on an unbound destination whose tower type encodes to `.memref n`
  (a literal slot, the image of a literal binding under the tower-literal pass),
  a `bvConst`; `extCall (limbLitLeafName idx)` pair, the leaf taking the word and
  returning the slot holding it at limb `idx`;
* `RCallSwap`        — two sequential `extCall`s;
* `RCloneCall`       — `extCall "clone"`; inner `extCall innerF`;
* `RCallN`           — a left-to-right fold of `extCall (callNLeafName f i)` per
  dest, indexed by output position;
* `RAssert`          — no dialect node at all (§2b).

Each arm builds its `catCryptDialect` `Expr` (`extCall` via `extCallExpr`,
`bvConst`/`memrefSet` directly) and threads it through `ComCont`.

## Covered fragment

`IsCovered` is the syntactic fragment `translateDialectFull` lowers: the core
arms plus the arms above. The top-level wrapper `translateDialectFullTop` emits
the `constUnit; ret` terminator at the final context `o.Γ'`.

`RIfNz` (the φ-merge) and the bounded-unroll `RFor` are declined here; they are
handled by `translateDialectControl` (`TranslateDialectDirectControl.lean`).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState LeafSpec RustExec Located TowerType
  callNLeafName)

/-! ## 1. Fused dialect `extCall` / `memrefSet` builders

Each builds the `catCryptDialect` `Expr` for one leaf-call or limb-store
binding. -/

/-- The dialect `extCall` expression calling `name` with return type `retTy`.
    `args` is translated pointwise via `toVIRArgs`. -/
def extCallExpr {Γ : Ctx} (name : String) (retTy : CryptoTy) {argTys : List CryptoTy}
    (args : CHVector (fun t => CVar Γ t) argTys) : Expr catCryptDialect Γ retTy :=
  { op := .extCall name argTys retTy, retTy_eq := rfl, args := toVIRArgs args }

/-- The leaf name of the literal slot at limb `idx`: the leaf takes one 64-bit word
    and returns the memref slot holding it at limb `idx`. -/
def limbLitLeafName (idx : Nat) : String := "limbLit:" ++ toString idx

/-- The `extCall` expression of the literal slot at limb `idx` over the word bound at
    the head of the context. -/
def limbLitExpr {Γ : Ctx} (idx n : Nat) : Expr catCryptDialect (.sword 64 :: Γ) (.memref n) :=
  extCallExpr (limbLitLeafName idx) (.memref n) (.cons (CVar.here : CVar (.sword 64 :: Γ) _) .nil)

/-! ## 1b. Scalar-`SExpr` lowering (`RScalarSetExpr`)

`RScalarSetExpr x e` assigns the value of a scalar `SExpr` (arithmetic /
bitwise / shift over `u64` slots) to slot `x`. `lowerSExpr` lowers the `SExpr`
tree into a left-to-right chain of `ComCont.varBind`s over the `catCryptDialect`
word ops (`bvConst`, `bvAdd`/`bvSub`/`bvMul`, `bvAnd`/`bvXor`, immediate
`bvShiftL`/`bvShiftR`, variable `bvShiftLV`/`bvShiftRV`) — exactly the ops the
backend `DialectToJasminCom.cryptoDialectToJasminCom` already lowers — so the
rerouted emit reaches owned `.s` via `cryptoDialectToJasminCom`.

Intermediate results are bound under fresh `tmpName` slots and referenced back
through the `VarMap` (which threads de-Bruijn weakening automatically), so no
hand-built de-Bruijn arithmetic is needed. The two combinators `seqOut` (thread
one sub-output's context into the next) and `pushVarBind` (append one
`varBind` node binding a fresh name) keep every arm — and the downstream
`NoAliasVM` / leak-factoring companions — uniform. -/

/-- Fresh intermediate-slot name for the SExpr chain at counter `n`. The `__sx`
    prefix is disjoint from real LowCT scalar-slot names. -/
def tmpName (n : Nat) : String := "__sx" ++ toString n

/-- Look up a `u64` scalar slot by name, returning its De-Bruijn var (or `none`
    if unbound or not a `sword 64`). Keeps the `SExpr` lowering's matches simple
    (a plain `Option (CVar ..)` rather than a refined `Σ`-match). -/
def lookupU64 {Γ : Ctx} (vm : VarMap Γ) (name : String) : Option (CVar Γ (.sword 64)) :=
  match vm.lookup name with
  | some ⟨.sword 64, v⟩ => some v
  | _ => none

/-- Thread one sub-output's context into a following one: compose the two
    `ComCont` prefixes, keep the later `VarMap`. -/
def seqOut {Γ : Ctx} (oa : DTransOut Γ) (ob : DTransOut oa.Γ') : DTransOut Γ :=
  { Γ' := ob.Γ', cont := ComCont.comp oa.cont ob.cont, vm := ob.vm }

/-- Append one `varBind` node (binding fresh name `nm`) to an existing output. -/
def pushVarBind {Γ : Ctx} (o : DTransOut Γ) (e : Expr catCryptDialect o.Γ' (.sword 64))
    (nm : String) : DTransOut Γ :=
  { Γ' := .sword 64 :: o.Γ',
    cont := ComCont.comp o.cont (ComCont.varBind e),
    vm := o.vm.bind nm }

/-- Lower a scalar `SExpr` into a `ComCont` chain over the
    `catCryptDialect` word ops. Returns the output (extended context + prefix +
    `VarMap`), the name the result is bound under, and the next-free counter.
    `none` on the SExpr arms with no jasmin lowering (`SLt`, `SAsr`, `SMulS`,
    `SMulHiU`, `SMulHiS`, `SLimb`) or an unbound / non-`u64` slot. -/
def lowerSExpr {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) :
    CatCrypt.Crypto.Jasmin.LowCT.SExpr → Option (DTransOut Γ × String × Nat)
  | .SVar x =>
      match lookupU64 vm x with
      | some _ => some (⟨Γ, ComCont.id, vm⟩, x, cnt)
      | _ => none
  | .SLit n =>
      let e : Expr catCryptDialect Γ (.sword 64) :=
        { op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil }
      some (pushVarBind ⟨Γ, ComCont.id, vm⟩ e (tmpName cnt), tmpName cnt, cnt + 1)
  | .SAdd a b =>
      match lowerSExpr vm cnt a with
      | none => none
      | some r =>
        match lowerSExpr r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupU64 s.1.vm r.2.1, lookupU64 s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword 64) :=
                { op := .bvAdd 64, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBind (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SSub a b =>
      match lowerSExpr vm cnt a with
      | none => none
      | some r =>
        match lowerSExpr r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupU64 s.1.vm r.2.1, lookupU64 s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword 64) :=
                { op := .bvSub 64, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBind (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SMul a b =>
      match lowerSExpr vm cnt a with
      | none => none
      | some r =>
        match lowerSExpr r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupU64 s.1.vm r.2.1, lookupU64 s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword 64) :=
                { op := .bvMul 64, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBind (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SAnd a b =>
      match lowerSExpr vm cnt a with
      | none => none
      | some r =>
        match lowerSExpr r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupU64 s.1.vm r.2.1, lookupU64 s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword 64) :=
                { op := .bvAnd 64, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBind (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | .SXor a b =>
      match lowerSExpr vm cnt a with
      | none => none
      | some r =>
        match lowerSExpr r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupU64 s.1.vm r.2.1, lookupU64 s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword 64) :=
                { op := .bvXor 64, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBind (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  -- Shifts lower to the *variable* shift ops `bvShiftLV` / `bvShiftRV` (which
  -- read the shift amount from a register and match `SExpr.evalBV`'s
  -- `a <<< (b.evalBV).toNat` exactly). Constant-amount shifts therefore emit
  -- `const; regArith shl` rather than `shlImm`; folding a literal amount into the
  -- immediate `bvShiftL`/`bvShiftR` op is left to a peephole pass.
  -- **Left shift `x << y`.** Both operands are lowered (preserving the two-chain
  -- `seqOut`/`pushVarBind` structure the leak-factoring proof expects). The final
  -- op is selected by the shift amount: a compile-time literal `SLit k` emits the
  -- immediate-shift `bvShiftL 64 k` (jasmin `shlImm`, `shl $k, reg`); a runtime
  -- amount emits the variable `bvShiftLV 64`. The immediate form is required for a
  -- valid x86 encoding — `SHL reg, reg` needs the count in `%cl`, whereas the
  -- (overwhelmingly common) literal count lowers to a clean `shl $k`.
  | .SShl a b =>
      match lowerSExpr vm cnt a with
      | none => none
      | some r =>
        match lowerSExpr r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupU64 s.1.vm r.2.1, lookupU64 s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword 64) :=
                match b with
                | .SLit k =>
                    { op := .bvShiftL 64 k, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
                | _ =>
                    { op := .bvShiftLV 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBind (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  -- **Right shift `x >> y`** (logical). Same op-selection rationale as `SShl`:
  -- a literal count emits `bvShiftR 64 k` (jasmin `shrImm`, `shr $k, reg`), a
  -- runtime count emits the variable `bvShiftRV 64`.
  | .SShr a b =>
      match lowerSExpr vm cnt a with
      | none => none
      | some r =>
        match lowerSExpr r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupU64 s.1.vm r.2.1, lookupU64 s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword 64) :=
                match b with
                | .SLit k =>
                    { op := .bvShiftR 64 k, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
                | _ =>
                    { op := .bvShiftRV 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBind (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  -- **Widening high-multiply** `mulhi(x, y)` — the high 64 bits of the full
  -- unsigned `64×64 → 128` product. Lowers to the dialect `bvMulHi 64` op (whose
  -- denotation is `mulHiC`, the unsigned high word, and which `DialectToJasminCom`
  -- lowers to jasmin `mulhi`/x86 `MULX`). Same two-chain `seqOut`/`pushVarBind`
  -- structure as `SMul`, so the leak-factoring / `NoAliasVM` companions carry over
  -- unchanged. This is the field-arithmetic prerequisite for Barrett/Montgomery
  -- folds (`fMul = (a·b) mod p` via low `SMul` + high `SMulHiU`).
  | .SMulHiU a b =>
      match lowerSExpr vm cnt a with
      | none => none
      | some r =>
        match lowerSExpr r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupU64 s.1.vm r.2.1, lookupU64 s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword 64) :=
                { op := .bvMulHi 64, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBind (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  -- SExpr arms with no *faithful* jasmin word lowering: declined. The signed
  -- high-multiply `SMulHiS` is declined here on purpose — the dialect's only
  -- high-mul op `bvMulHi` denotes the *unsigned* `mulHiC`, so lowering `SMulHiS`
  -- (whose `evalBV` is the signed `sexprMulHiS`) to it would be denotation-
  -- unfaithful for negative operands; adding a signed `bvMulHiS`/`IMUL` op to the
  -- dialect + backend is the prerequisite. Likewise the backend has no scalar
  -- `<` / arithmetic-shift / signed-low-mul / tower-limb op for the remaining
  -- arms in the straight-line fragment.
  | _ => none

/-! ## 1b′. Width-parametric scalar-`SExpr` lowering (`lowerSExprW w`)

The `lowerSExpr` front above hardwires every emitted dialect word op to width
`64` (`.bvAdd 64`, `.bvShiftL 64 k`, …) and only accepts `.sword 64` input slots
(`lookupU64`). That is exactly right for the lane-independent word-packing kernels
(Hawk, GF-MQ), but it cannot express narrow-width crypto with CROSS-LANE
mixing — the ChaCha quarter-round rotations, the SHA-256 Σ/Ch/Maj words, the
BLAKE3 g-function, the Frodo 16-bit lanes — because those need a real 32-bit
(or 16-bit) register ALU: width-`w` wrapping arithmetic and `rotl_w`.

The `catCryptDialect` op set is ALREADY width-parametric — every op carries a
`(w : Nat)` and denotes over `BitVec w` — and the jasmin lowering
`mapTy (.sword w) = .reg w` is likewise width-generic. So the ONLY place width
`64` is baked in is this FRONT lowering. `lowerSExprW w` is the **additive**
width-parametric twin of `lowerSExpr`: it is the exact same recursion with `64`
replaced by a width parameter `w` on every op and slot. The 64-bit `lowerSExpr`
above is UNTOUCHED (byte-identical — the leak-factoring / simulation companions
`simp only [lowerSExpr]` on its concrete equations), and `lowerSExprW 64` is
behaviourally the same function (same emitted `DTransOut` on every `SExpr`). The
narrow-width kernels front-source through `lowerSExprW 32` / `lowerSExprW 16`.

Reuses the `ScalarSExprWidth32Prototype` design (which validated the width-32
ChaCha rotation end-to-end through `cryptoDialectToJasminCom`). -/

/-- Width-parametric `lookupU64`: look up a `.sword w` scalar slot by name. At
    `w := 64` this is extensionally `lookupU64`. -/
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

/-- Lower a scalar `SExpr` into a `ComCont` chain over the
    `catCryptDialect` word ops at width `w`. Width-parametric twin of
    `lowerSExpr` (`64 ↦ w` on every op and slot). Covers the straight-line
    arithmetic / bitwise / shift / high-multiply arms — exactly the alphabet the
    cross-lane kernels (ChaCha, SHA-256, BLAKE3, Frodo) use. `none` on the arms
    with no faithful jasmin lowering, matching `lowerSExpr`. -/
def lowerSExprW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) :
    CatCrypt.Crypto.Jasmin.LowCT.SExpr → Option (DTransOut Γ × String × Nat)
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
  | .SMulHiU a b =>
      match lowerSExprW w vm cnt a with
      | none => none
      | some r =>
        match lowerSExprW w r.1.vm r.2.2 b with
        | none => none
        | some s =>
          match lookupUW w s.1.vm r.2.1, lookupUW w s.1.vm s.2.1 with
          | some va, some vb =>
              let e : Expr catCryptDialect s.1.Γ' (.sword w) :=
                { op := .bvMulHi w, retTy_eq := rfl,
                  args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }
              some (pushVarBindW w (seqOut r.1 s.1) e (tmpName s.2.2), tmpName s.2.2, s.2.2 + 1)
          | _, _ => none
  | _ => none

/-! ### 1b′. Width-parametric `RScalarSetExpr` sequencing (`stepW`)

The width-parametric twin of the `.RScalarSetExpr` arm of `translateDialectFull`
(plus the `RSeq` fold), restricted to the straight-line scalar fragment — exactly
the alphabet the cross-lane 32-bit crypto kernels (ChaCha, SHA-256, BLAKE3) use.
`lowerScalarSetW w vm x e` lowers the `SExpr` `e` via `lowerSExprW w`, then binds
`x` to a fresh identity copy (`bvShiftL w 0`) of the result — keeping `x` an
alias-free fresh slot exactly as the 64-bit arm does. `stepW` threads one such
assignment onto an accumulated prefix (`seqOut`), and `lowerScalarSetSeqW` folds a
whole `(name, SExpr)` statement list left-to-right through the growing `VarMap`.
This is the front-sourced drop-in for a hand `emitOp`/`.regArith` CPS builder: it
composes statefully and every emitted binding is a `catCryptDialect` word op that
`cryptoDialectToJasminCom` lowers to owned `.s`. -/

/-- Lower one width-`w` `RScalarSetExpr x e`: lower `e` via `lowerSExprW w`, then
    bind `x` to a fresh identity copy (`bvShiftL w 0`) of the result. `none` if
    `e` declines or its result slot is not a `.sword w`. -/
def lowerScalarSetW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (x : String)
    (e : CatCrypt.Crypto.Jasmin.LowCT.SExpr) : Option (DTransOut Γ) :=
  match lowerSExprW w vm 0 e with
  | none => none
  | some r =>
      match lookupUW w r.1.vm r.2.1 with
      | some v =>
          let copyE : Expr catCryptDialect r.1.Γ' (.sword w) :=
            { op := .bvShiftL w 0, retTy_eq := rfl, args := .cons (toVIRVar v) .nil }
          some (pushVarBindW w r.1 copyE x)
      | _ => none

/-- Thread one width-`w` assignment `x := e` onto an accumulated prefix `o`
    (`seqOut` of the current prefix and the lowered assignment over `o.vm`). -/
def stepW (w : Nat) {Γ : Ctx} (o : DTransOut Γ) (x : String)
    (e : CatCrypt.Crypto.Jasmin.LowCT.SExpr) : Option (DTransOut Γ) :=
  match lowerScalarSetW w o.vm x e with
  | some o' => some (seqOut o o')
  | none => none

/-- Fold a `(name, SExpr)` statement list into one accumulated prefix, threading
    the `VarMap` left-to-right. `none` on the first declined assignment. -/
def lowerScalarSetSeqW (w : Nat) {Γ : Ctx} :
    DTransOut Γ → List (String × CatCrypt.Crypto.Jasmin.LowCT.SExpr) →
    Option (DTransOut Γ)
  | o, [] => some o
  | o, (x, e) :: rest =>
      match stepW w o x e with
      | some o' => lowerScalarSetSeqW w o' rest
      | none => none

/-! ## 1c. Dynamic-index memref array access (`RArrLoad` / `RArrStore`)

The default `RArrLoad` / `RArrStore` arms emit an opaque `extCall "arrLoadDyn"` /
`"arrStoreDyn"` leaf (whose dialect denotation is `CryptoTy.default` and whose
jasmin lowering is again an opaque `extCall`). When the operands line up with the
real dynamic-index memref ABI — the array slot resolves to a `.memref n`, the
index slot to a `.sword 64`, and (for a load) the destination is a `u64` word /
(for a store) the destination array's encoding is exactly `.memref n` — these
two combinators instead emit the dialect's `memrefGetDyn` / `memrefSetDyn` op,
which `DialectToJasminCom.cryptoDialectToJasminCom` lowers to a real jasmin
`stackLoad` / `stackStore` (the SIB `LOADIDX` / `STOREIDX`). This is the
front-side enabler that lets a multi-pointer memref kernel (e.g. the GF-MQ
`out[i] = f(s[j], mat[k])` shape, `s`/`mat`/`out` bound to distinct arg
pointers) reach the owned `.s` through the verified front rather than an opaque
leaf.

The combinators are *additive*: the emitted `DTransOut.Γ'` and `.vm` are the same
as the opaque-`extCall` arms (a `u64`/`memref n` binding of the destination slot),
so the context-agreement / simulation / `NoAliasVM` proofs are unaffected — only
the `cont` prefix differs (a single `varBind`, either way), which the leak
companions account for via `arrLoadCont_leakFactors` / `arrStoreCont_leakFactors`.
The condition that doesn't match falls back to the opaque `extCall`. -/

/-- Transport a `ComCont` along an equality of its codomain context. Used to
    retype a `memrefSetDyn` `varBind` (codomain `.memref n :: Γ`) to the
    destination array's declared encoding `encodeTy dty :: Γ` when the two
    coincide. -/
def ComCont.castCtx {Γ Δ Δ' : Ctx} (h : Δ = Δ') (f : ComCont Γ Δ) : ComCont Γ Δ' :=
  match Δ', h with
  | _, rfl => f

/-- The `ComCont` prefix for `RArrLoad`: a `memrefGetDyn` `varBind` when the
    destination is a `u64`, the array slot is `.memref n`, and the index slot is
    `.sword 64`; otherwise the opaque `extCall "arrLoadDyn"`. Both branches bind a
    fresh slot of type `encodeTy dty`, so the surrounding `DTransOut` is the
    same record either way. -/
def arrLoadCont {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t))
    (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ComCont Γ (encodeTy dty :: Γ) :=
  match dty, resolvedArgs, idxSig with
  | .TU64, [⟨.memref n, arrV⟩], ⟨.sword 64, idxV⟩ =>
      ComCont.varBind
        { op := .memrefGetDyn n, retTy_eq := rfl,
          args := .cons (toVIRVar arrV) (.cons (toVIRVar idxV) .nil) }
  | dty', _, _ => ComCont.varBind (extCallExpr "arrLoadDyn" (encodeTy dty') hv)

/-- The `ComCont` prefix for `RArrStore`: a `memrefSetDyn` `varBind` when the
    array slot is `.memref n`, the index and value slots are `.sword 64`, and the
    destination array's encoding `encodeTy dty` is exactly `.memref n`; otherwise
    the opaque `extCall "arrStoreDyn"`. Both branches rebind the array slot at
    type `encodeTy dty`.

    This is the **word-cell** array store: `CryptoTy.memref n` is `Fin n → BitVec
    64` and `memrefSetDyn n` lowers to jasmin `stackStore 64 n` (SIB scale 8,
    `movq`). A **byte-cell** store (`stackStore 8 n`, SIB scale 1, `movb`)
    cannot be expressed here without giving `CryptoTy.memref` a cell-width
    parameter (its denotation and every `.memref`-exhaustive match, plus a
    byte-width dialect op + `DialectToJasminCom` arm, all change). The byte-capable
    store lives in the width-parametric `Dialects.Memref` front (`.buf 8 n`
    → `stackStore 8 n`, proven denote-preserving by `lowerMemrefToJasmin_denote`);
    the Plonky3 LE byte serializer is sourced through it
    (`Plonky3SerializeEmit.frontByteStoreLinstr`). -/
def arrStoreCont {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t))
    (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ComCont Γ (encodeTy dty :: Γ) :=
  match resolvedArgs, idxSig with
  | [⟨.memref n, arrV⟩, ⟨.sword 64, srcV⟩], ⟨.sword 64, idxV⟩ =>
      if h : encodeTy dty = .memref n then
        ComCont.castCtx (congrArg (· :: Γ) h.symm)
          (ComCont.varBind
            { op := .memrefSetDyn n, retTy_eq := rfl,
              args := .cons (toVIRVar arrV)
                (.cons (toVIRVar idxV) (.cons (toVIRVar srcV) .nil)) })
      else ComCont.varBind (extCallExpr "arrStoreDyn" (encodeTy dty) hv)
  | _, _ => ComCont.varBind (extCallExpr "arrStoreDyn" (encodeTy dty) hv)

/-! ### 1d. The constant-time word select

`RSelect dst sel src0 src1` on 64-bit words lowers to a comparison feeding a
conditional select,

    z = 0; b = (s == z); r = b ? a : c

over the selector `s` and the sources `a` (`src0`) and `c` (`src1`)
(`selectCmpCont`). `DialectToJasminCom` lowers the three ops to `regConst`,
`cmp .eq` and `select`, which the x86 backend carries as `cmp` and `cmovcc`.

`selectMaskCont` is the branchless mask chain computing the same word,

    z = 0; n = z - s; o = s | n; b = o >> 63; m = z - b;
    x = a ^ c; y = x & m; r = a ^ y

where `b` is `1` exactly when `s ≠ 0`, so `m` is all ones exactly then and `r`
is `c`; otherwise `m = 0` and `r = a`. Every op of it is in the fragment
`DialectToJasminCom` lowers (`regConst`, `regArith sub/or/xor/and`, `shrImm`). -/

/-- The context the comparison select grows over `Γ`: the zero word, the
    comparison bit, and the destination word on top. -/
abbrev selectCmpCtx (Γ : Ctx) : Ctx :=
  .sword 64 :: .bit :: .sword 64 :: Γ

/-- The three-op comparison select computing `if s = 0 then a else c` over the
    word slots `sV` (selector), `aV` and `cV`: the zero word, the bit `s = 0`,
    and the `ite` on that bit. -/
def selectCmpCont {Γ : Ctx} (sV aV cV : CVar Γ (.sword 64)) :
    ComCont Γ (selectCmpCtx Γ) :=
  let Γ₁ : Ctx := .sword 64 :: Γ
  let Γ₂ : Ctx := .bit :: Γ₁
  let eZ : Expr catCryptDialect Γ (.sword 64) :=
    { op := .bvConst 64 0, retTy_eq := rfl, args := .nil }
  let eB : Expr catCryptDialect Γ₁ .bit :=
    { op := .bvEq 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.there sV : CVar Γ₁ (.sword 64)))
        (.cons (toVIRVar (CVar.here : CVar Γ₁ (.sword 64))) .nil) }
  let eR : Expr catCryptDialect Γ₂ (.sword 64) :=
    { op := .ite (.sword 64), retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.here : CVar Γ₂ .bit))
        (.cons (toVIRVar (CVar.there (CVar.there aV) : CVar Γ₂ (.sword 64)))
          (.cons (toVIRVar (CVar.there (CVar.there cV) : CVar Γ₂ (.sword 64))) .nil)) }
  ComCont.comp (ComCont.varBind eZ)
    (ComCont.comp (ComCont.varBind eB) (ComCont.varBind eR))

/-- The `VarMap` after the comparison select: the zero word and the comparison
    bit are anonymous and `dst` names the top slot. -/
def selectCmpVm {Γ : Ctx} (vm : VarMap Γ) (dst : String) : VarMap (selectCmpCtx Γ) :=
  ((vm.weaken (t := .sword 64)).weaken (t := .bit)).bind (t := .sword 64) dst

/-- The context the select chain grows over `Γ`: seven 64-bit temporaries and
    the destination word on top. -/
abbrev selectCtx (Γ : Ctx) : Ctx :=
  .sword 64 :: .sword 64 :: .sword 64 :: .sword 64 ::
    .sword 64 :: .sword 64 :: .sword 64 :: .sword 64 :: Γ

/-- The eight-op mask chain computing `if s = 0 then a else c` over the word
    slots `sV` (selector), `aV` and `cV`. -/
def selectMaskCont {Γ : Ctx} (sV aV cV : CVar Γ (.sword 64)) :
    ComCont Γ (selectCtx Γ) :=
  let Γ₁ : Ctx := .sword 64 :: Γ
  let Γ₂ : Ctx := .sword 64 :: Γ₁
  let Γ₃ : Ctx := .sword 64 :: Γ₂
  let Γ₄ : Ctx := .sword 64 :: Γ₃
  let Γ₅ : Ctx := .sword 64 :: Γ₄
  let Γ₆ : Ctx := .sword 64 :: Γ₅
  let Γ₇ : Ctx := .sword 64 :: Γ₆
  let eZ : Expr catCryptDialect Γ (.sword 64) :=
    { op := .bvConst 64 0, retTy_eq := rfl, args := .nil }
  let eN : Expr catCryptDialect Γ₁ (.sword 64) :=
    { op := .bvSub 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.here : CVar Γ₁ (.sword 64)))
        (.cons (toVIRVar (CVar.there sV : CVar Γ₁ (.sword 64))) .nil) }
  let eO : Expr catCryptDialect Γ₂ (.sword 64) :=
    { op := .bvOr 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.there (CVar.there sV) : CVar Γ₂ (.sword 64)))
        (.cons (toVIRVar (CVar.here : CVar Γ₂ (.sword 64))) .nil) }
  let eB : Expr catCryptDialect Γ₃ (.sword 64) :=
    { op := .bvShiftR 64 63, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.here : CVar Γ₃ (.sword 64))) .nil }
  let eM : Expr catCryptDialect Γ₄ (.sword 64) :=
    { op := .bvSub 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.there (CVar.there (CVar.there CVar.here)) :
          CVar Γ₄ (.sword 64)))
        (.cons (toVIRVar (CVar.here : CVar Γ₄ (.sword 64))) .nil) }
  let eX : Expr catCryptDialect Γ₅ (.sword 64) :=
    { op := .bvXor 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.there (CVar.there (CVar.there (CVar.there
          (CVar.there aV)))) : CVar Γ₅ (.sword 64)))
        (.cons (toVIRVar (CVar.there (CVar.there (CVar.there (CVar.there
          (CVar.there cV)))) : CVar Γ₅ (.sword 64))) .nil) }
  let eY : Expr catCryptDialect Γ₆ (.sword 64) :=
    { op := .bvAnd 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.here : CVar Γ₆ (.sword 64)))
        (.cons (toVIRVar (CVar.there CVar.here : CVar Γ₆ (.sword 64))) .nil) }
  let eR : Expr catCryptDialect Γ₇ (.sword 64) :=
    { op := .bvXor 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.there (CVar.there (CVar.there (CVar.there
          (CVar.there (CVar.there (CVar.there aV)))))) : CVar Γ₇ (.sword 64)))
        (.cons (toVIRVar (CVar.here : CVar Γ₇ (.sword 64))) .nil) }
  ComCont.comp (ComCont.varBind eZ)
    (ComCont.comp (ComCont.varBind eN)
      (ComCont.comp (ComCont.varBind eO)
        (ComCont.comp (ComCont.varBind eB)
          (ComCont.comp (ComCont.varBind eM)
            (ComCont.comp (ComCont.varBind eX)
              (ComCont.comp (ComCont.varBind eY) (ComCont.varBind eR)))))))

/-- The `VarMap` after the select chain: the seven temporaries are anonymous
    and `dst` names the top slot. -/
def selectVm {Γ : Ctx} (vm : VarMap Γ) (dst : String) : VarMap (selectCtx Γ) :=
  (((((((vm.weaken (t := .sword 64)).weaken (t := .sword 64)).weaken
    (t := .sword 64)).weaken (t := .sword 64)).weaken (t := .sword 64)).weaken
    (t := .sword 64)).weaken (t := .sword 64)).bind (t := .sword 64) dst

/-! ### 1e. Inline arithmetic builtins

An `RCall f dest args` whose name is in `inlineArithTable`, whose destination is a
`.TFp` slot and whose two arguments are six-limb slots lowers inline
(`inlineArithCont`): limb `0` of each argument is loaded, the recipe's word operation
is applied under the recipe's mask, and the result is written into a copy of the
first argument at limb `0` with limbs `1` to `5` zeroed. Every other `RCall` lowers to
the opaque `extCall`. The inline value is `inlineArithMemref`. -/

/-- A binary word operation the front lowers inline: the bitwise operations and the
    variable-amount logical shifts on 64-bit words. -/
inductive InlineBop where
  | and | or | xor | shl | shr
  deriving DecidableEq, Repr

/-- The value of an inline operation on two 64-bit words, as `catCryptDialect` denotes
    the corresponding op. -/
def InlineBop.apply : InlineBop → BitVec 64 → BitVec 64 → BitVec 64
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< b.toNat
  | .shr, a, b => a >>> b.toNat

/-- The dialect expression of an inline operation on two word slots. -/
def InlineBop.expr {Γ : Ctx} : InlineBop → CVar Γ (.sword 64) → CVar Γ (.sword 64) →
    Expr catCryptDialect Γ (.sword 64)
  | .and, a, b => Expr.mk (.bvAnd 64) rfl (.cons (toVIRVar a) (.cons (toVIRVar b) .nil))
  | .or, a, b => Expr.mk (.bvOr 64) rfl (.cons (toVIRVar a) (.cons (toVIRVar b) .nil))
  | .xor, a, b => Expr.mk (.bvXor 64) rfl (.cons (toVIRVar a) (.cons (toVIRVar b) .nil))
  | .shl, a, b => Expr.mk (.bvShiftLV 64) rfl (.cons (toVIRVar a) (.cons (toVIRVar b) .nil))
  | .shr, a, b => Expr.mk (.bvShiftRV 64) rfl (.cons (toVIRVar a) (.cons (toVIRVar b) .nil))

/-- An inline lowering recipe: the word operation and whether the builtin acts on 32-bit
    words (its first argument and its result masked to 32 bits). -/
structure InlineArith where
  bop : InlineBop
  masked : Bool
  deriving DecidableEq, Repr

/-- The 32-bit mask as a 64-bit word. -/
def inlineMask32 : BitVec 64 := BitVec.ofNat 64 (2 ^ 32 - 1)

/-- The mask of a recipe: the 32-bit mask when masked, all ones otherwise. -/
def InlineArith.mask (r : InlineArith) : BitVec 64 :=
  if r.masked then inlineMask32 else BitVec.allOnes 64

/-- The value of a recipe on two 64-bit words: the operation on the masked first word
    and the second word, masked. -/
def InlineArith.evalBV (r : InlineArith) (a b : BitVec 64) : BitVec 64 :=
  r.bop.apply (a &&& r.mask) b &&& r.mask

/-- The value of a recipe on two six-limb slots, as the inline lowering computes it: the
    first slot with limb `0` replaced by the recipe's value on the two limbs `0` and limbs
    `1` to `5` replaced by `0`. -/
def inlineArithMemref (r : InlineArith) (a b : Fin 6 → BitVec 64) : Fin 6 → BitVec 64 :=
  memSetDyn (memSetDyn (memSetDyn (memSetDyn (memSetDyn
    (memSetDyn a (0 : BitVec 64).toNat
      (r.evalBV (memGetDyn a (0 : BitVec 64).toNat) (memGetDyn b (0 : BitVec 64).toNat)))
    (1 : BitVec 64).toNat 0) (2 : BitVec 64).toNat 0) (3 : BitVec 64).toNat 0)
    (4 : BitVec 64).toNat 0) (5 : BitVec 64).toNat 0

/-- The table of the arithmetic builtins lowered inline, by call name. -/
def inlineArithTable : List (String × InlineArith) :=
  [("BitAnd", ⟨.and, false⟩), ("BitOr", ⟨.or, false⟩), ("BitXor", ⟨.xor, false⟩),
   ("BitAnd#32", ⟨.and, true⟩), ("BitOr#32", ⟨.or, true⟩), ("BitXor#32", ⟨.xor, true⟩),
   ("BitAnd#64", ⟨.and, false⟩), ("BitOr#64", ⟨.or, false⟩), ("BitXor#64", ⟨.xor, false⟩),
   ("Shl#32", ⟨.shl, true⟩), ("Shr#32", ⟨.shr, true⟩),
   ("Shl#64", ⟨.shl, false⟩), ("Shr#64", ⟨.shr, false⟩)]

/-- The inline recipe of a call name; `none` for a name outside the table. -/
def inlineArithRecipe (f : String) : Option InlineArith := inlineArithTable.lookup f

/-- The two six-limb argument slots of an inline call; `none` on every other argument
    list. -/
def inlineArithArgsVars {Γ : Ctx} :
    List ((t : CryptoTy) × CVar Γ t) → Option (CVar Γ (.memref 6) × CVar Γ (.memref 6))
  | [⟨.memref 6, a⟩, ⟨.memref 6, b⟩] => some (a, b)
  | _ => none

/-- The context the inline lowering grows over `Γ`: twelve word temporaries (the index
    `0`, the two loaded limbs, the mask, the masked first limb, the operation's value, its
    masked value, the indices `1` to `5`), five intermediate slots, and the destination
    slot on top. -/
abbrev inlineArithCtx (Γ : Ctx) : Ctx :=
  .memref 6 :: .memref 6 :: .memref 6 :: .memref 6 :: .memref 6 :: .memref 6 ::
    .sword 64 :: .sword 64 :: .sword 64 :: .sword 64 :: .sword 64 :: .sword 64 ::
    .sword 64 :: .sword 64 :: .sword 64 :: .sword 64 :: .sword 64 :: .sword 64 :: Γ

/-- The inline lowering of a call with recipe `r` on the six-limb slots `aV`, `bV`:

    i0 := 0; la := aV[i0]; lb := bV[i0]; m := mask; la' := la & m; v := la' op lb;
    v' := v & m; i1 := 1; …; i5 := 5;
    d0 := aV[i0 := v']; d1 := d0[i1 := i0]; …; d5 := d4[i5 := i0]

    The result `d5` holds `v'` at limb `0` and `0` at the other limbs. Every op is in the
    fragment `DialectToJasminCom` lowers. -/
def inlineArithCont {Γ : Ctx} (r : InlineArith) (aV bV : CVar Γ (.memref 6)) :
    ComCont Γ (inlineArithCtx Γ) :=
  let Γ₁ : Ctx := .sword 64 :: Γ
  let Γ₂ : Ctx := .sword 64 :: Γ₁
  let Γ₃ : Ctx := .sword 64 :: Γ₂
  let Γ₄ : Ctx := .sword 64 :: Γ₃
  let Γ₅ : Ctx := .sword 64 :: Γ₄
  let Γ₆ : Ctx := .sword 64 :: Γ₅
  let Γ₇ : Ctx := .sword 64 :: Γ₆
  let Γ₈ : Ctx := .sword 64 :: Γ₇
  let Γ₉ : Ctx := .sword 64 :: Γ₈
  let Γ₁₀ : Ctx := .sword 64 :: Γ₉
  let Γ₁₁ : Ctx := .sword 64 :: Γ₁₀
  let Γ₁₂ : Ctx := .sword 64 :: Γ₁₁
  let Γ₁₃ : Ctx := .memref 6 :: Γ₁₂
  let Γ₁₄ : Ctx := .memref 6 :: Γ₁₃
  let Γ₁₅ : Ctx := .memref 6 :: Γ₁₄
  let Γ₁₆ : Ctx := .memref 6 :: Γ₁₅
  let Γ₁₇ : Ctx := .memref 6 :: Γ₁₆
  let const : (Δ : Ctx) → BitVec 64 → Expr catCryptDialect Δ (.sword 64) :=
    fun _ k => Expr.mk (.bvConst 64 k) rfl .nil
  let eI0 := const Γ 0
  let eLa : Expr catCryptDialect Γ₁ (.sword 64) :=
    { op := .memrefGetDyn 6, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.there aV : CVar Γ₁ (.memref 6)))
        (.cons (toVIRVar (CVar.here : CVar Γ₁ (.sword 64))) .nil) }
  let eLb : Expr catCryptDialect Γ₂ (.sword 64) :=
    { op := .memrefGetDyn 6, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.there (CVar.there bV) : CVar Γ₂ (.memref 6)))
        (.cons (toVIRVar (CVar.there CVar.here : CVar Γ₂ (.sword 64))) .nil) }
  let eM := const Γ₃ r.mask
  let eLa' : Expr catCryptDialect Γ₄ (.sword 64) :=
    { op := .bvAnd 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.there (CVar.there CVar.here) : CVar Γ₄ (.sword 64)))
        (.cons (toVIRVar (CVar.here : CVar Γ₄ (.sword 64))) .nil) }
  let eV : Expr catCryptDialect Γ₅ (.sword 64) :=
    r.bop.expr (CVar.here : CVar Γ₅ (.sword 64))
      (CVar.there (CVar.there CVar.here) : CVar Γ₅ (.sword 64))
  let eV' : Expr catCryptDialect Γ₆ (.sword 64) :=
    { op := .bvAnd 64, retTy_eq := rfl,
      args := .cons (toVIRVar (CVar.here : CVar Γ₆ (.sword 64)))
        (.cons (toVIRVar (CVar.there (CVar.there CVar.here) : CVar Γ₆ (.sword 64))) .nil) }
  let eI1 := const Γ₇ 1
  let eI2 := const Γ₈ 2
  let eI3 := const Γ₉ 3
  let eI4 := const Γ₁₀ 4
  let eI5 := const Γ₁₁ 5
  -- `Γ₁₂ = i5 :: i4 :: i3 :: i2 :: i1 :: v' :: v :: la' :: m :: lb :: la :: i0 :: Γ`.
  let aV₁₂ : CVar Γ₁₂ (.memref 6) :=
    .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there aV)))))))))))
  let i0₁₂ : CVar Γ₁₂ (.sword 64) :=
    .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there CVar.here))))))))))
  let v'₁₂ : CVar Γ₁₂ (.sword 64) := .there (.there (.there (.there (.there CVar.here))))
  let eD0 : Expr catCryptDialect Γ₁₂ (.memref 6) :=
    Expr.mk (.memrefSetDyn 6) rfl
      (.cons (toVIRVar aV₁₂) (.cons (toVIRVar i0₁₂) (.cons (toVIRVar v'₁₂) .nil)))
  -- In each `Γ₁₂₊ₖ` (`k ≥ 1`) the previous slot is `here`, the index `iₖ` is at depth `5`
  -- and the zero word `i0` at depth `11 + k`.
  let i1₁₃ : CVar Γ₁₃ (.sword 64) := .there (.there (.there (.there (.there CVar.here))))
  let i0₁₃ : CVar Γ₁₃ (.sword 64) :=
    .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there CVar.here)))))))))))
  let eD1 : Expr catCryptDialect Γ₁₃ (.memref 6) :=
    Expr.mk (.memrefSetDyn 6) rfl
      (.cons (toVIRVar (CVar.here : CVar Γ₁₃ (.memref 6)))
        (.cons (toVIRVar i1₁₃) (.cons (toVIRVar i0₁₃) .nil)))
  let i2₁₄ : CVar Γ₁₄ (.sword 64) := .there (.there (.there (.there (.there CVar.here))))
  let i0₁₄ : CVar Γ₁₄ (.sword 64) :=
    .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there CVar.here))))))))))))
  let eD2 : Expr catCryptDialect Γ₁₄ (.memref 6) :=
    Expr.mk (.memrefSetDyn 6) rfl
      (.cons (toVIRVar (CVar.here : CVar Γ₁₄ (.memref 6)))
        (.cons (toVIRVar i2₁₄) (.cons (toVIRVar i0₁₄) .nil)))
  let i3₁₅ : CVar Γ₁₅ (.sword 64) := .there (.there (.there (.there (.there CVar.here))))
  let i0₁₅ : CVar Γ₁₅ (.sword 64) :=
    .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there CVar.here)))))))))))))
  let eD3 : Expr catCryptDialect Γ₁₅ (.memref 6) :=
    Expr.mk (.memrefSetDyn 6) rfl
      (.cons (toVIRVar (CVar.here : CVar Γ₁₅ (.memref 6)))
        (.cons (toVIRVar i3₁₅) (.cons (toVIRVar i0₁₅) .nil)))
  let i4₁₆ : CVar Γ₁₆ (.sword 64) := .there (.there (.there (.there (.there CVar.here))))
  let i0₁₆ : CVar Γ₁₆ (.sword 64) :=
    .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there CVar.here))))))))))))))
  let eD4 : Expr catCryptDialect Γ₁₆ (.memref 6) :=
    Expr.mk (.memrefSetDyn 6) rfl
      (.cons (toVIRVar (CVar.here : CVar Γ₁₆ (.memref 6)))
        (.cons (toVIRVar i4₁₆) (.cons (toVIRVar i0₁₆) .nil)))
  let i5₁₇ : CVar Γ₁₇ (.sword 64) := .there (.there (.there (.there (.there CVar.here))))
  let i0₁₇ : CVar Γ₁₇ (.sword 64) :=
    .there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there CVar.here)))))))))))))))
  let eD5 : Expr catCryptDialect Γ₁₇ (.memref 6) :=
    Expr.mk (.memrefSetDyn 6) rfl
      (.cons (toVIRVar (CVar.here : CVar Γ₁₇ (.memref 6)))
        (.cons (toVIRVar i5₁₇) (.cons (toVIRVar i0₁₇) .nil)))
  ComCont.comp (ComCont.varBind eI0)
    (ComCont.comp (ComCont.varBind eLa)
      (ComCont.comp (ComCont.varBind eLb)
        (ComCont.comp (ComCont.varBind eM)
          (ComCont.comp (ComCont.varBind eLa')
            (ComCont.comp (ComCont.varBind eV)
              (ComCont.comp (ComCont.varBind eV')
                (ComCont.comp (ComCont.varBind eI1)
                  (ComCont.comp (ComCont.varBind eI2)
                    (ComCont.comp (ComCont.varBind eI3)
                      (ComCont.comp (ComCont.varBind eI4)
                        (ComCont.comp (ComCont.varBind eI5)
                          (ComCont.comp (ComCont.varBind eD0)
                            (ComCont.comp (ComCont.varBind eD1)
                              (ComCont.comp (ComCont.varBind eD2)
                                (ComCont.comp (ComCont.varBind eD3)
                                  (ComCont.comp (ComCont.varBind eD4)
                                    (ComCont.varBind eD5)))))))))))))))))

/-- The `VarMap` after the inline lowering: the seventeen temporaries are anonymous and
    `dst` names the top slot. -/
def inlineArithVm {Γ : Ctx} (vm : VarMap Γ) (dst : String) : VarMap (inlineArithCtx Γ) :=
  (((((((((((((((((vm.weaken (t := .sword 64)).weaken (t := .sword 64)).weaken
    (t := .sword 64)).weaken (t := .sword 64)).weaken (t := .sword 64)).weaken
    (t := .sword 64)).weaken (t := .sword 64)).weaken (t := .sword 64)).weaken
    (t := .sword 64)).weaken (t := .sword 64)).weaken (t := .sword 64)).weaken
    (t := .sword 64)).weaken (t := .memref 6)).weaken (t := .memref 6)).weaken
    (t := .memref 6)).weaken (t := .memref 6)).weaken (t := .memref 6)).bind
    (t := .memref 6) dst

/-! ## 2. The fused multi-binding front `translateDialectFull`

Lowers the leaf-call arms, building `ComCont` prefixes. Core arms delegate to
`translateDialect`; the control-flow arms (`RIfNz`, `RFor`, `RWhileNz`, helper
defs) decline. -/

/-- The `RCallN` fold: a left-to-right fold of
    `extCall (callNLeafName fname i)` bindings, one per destination, building
    `ComCont` prefixes.

    `i` is the output index of the head destination, counting up along the fold
    and defaulting to `0` at the call site. It is the same index
    `RustExec.callN` reads output `i` at, so destinations of the same encoded
    type — the `(carry, sum)` pair of an add-with-carry shape, both `TU64` —
    bind distinct leaf names. -/
def loopCallNDestsD {Γ : Ctx} (fname : String) (args : List Located) (vm : VarMap Γ) :
    List Located → (i : Nat := 0) → Option (DTransOut Γ)
  | [], _ => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | d :: rest, i =>
      match resolveLocatedArgs vm args with
      | none => none
      | some resolvedArgs =>
          let retTy := encodeTy d.locDst
          match listSigmaToCHVector resolvedArgs with
          | ⟨_argTys, hv⟩ =>
            let e : Expr catCryptDialect Γ retTy := extCallExpr (callNLeafName fname i) retTy hv
            let vm' : VarMap (retTy :: Γ) := vm.bind d.locVar
            match loopCallNDestsD fname args vm' rest (i + 1) with
            | none => none
            | some oRest =>
                some { Γ' := oRest.Γ'
                       cont := ComCont.comp (ComCont.varBind e) oRest.cont
                       vm := oRest.vm }

/-- Direct `LowCT → catCryptDialect` translation extended to the leaf-call
    multi-binding arms. Every prefix is a `ComCont`. -/
def translateDialectFull {Γ : Ctx} (vm : VarMap Γ) :
    LowCT → Option (DTransOut Γ)
  | .RSkip => translateDialect vm .RSkip
  | .RScalarSet name n => translateDialect vm (.RScalarSet name n)
  | .RSeq c₁ c₂ =>
      match translateDialectFull vm c₁ with
      | some o₁ =>
          match translateDialectFull o₁.vm c₂ with
          | some o₂ =>
              some { Γ' := o₂.Γ', cont := ComCont.comp o₁.cont o₂.cont, vm := o₂.vm }
          | none => none
      | none => none
  | .RLetU64Zero name body =>
      let e : Expr catCryptDialect Γ (.sword 64) :=
        { op := .bvConst 64 (0 : BitVec 64), retTy_eq := rfl, args := .nil }
      let vm' : VarMap (.sword 64 :: Γ) := vm.bind name
      match translateDialectFull vm' body with
      | some o =>
          some { Γ' := o.Γ', cont := ComCont.comp (ComCont.varBind e) o.cont, vm := o.vm }
      | none => none
  | .RBlock body => translateDialectFull vm body
  -- **Contract assertion.** `RAssert label` names a proposition in the proof
  -- context and carries no operands; its `RustExec` step is the identity, and
  -- `LowCT.cmdCT` accepts it unconditionally. The arm emits no dialect node and
  -- threads the entry context, `ComCont` prefix and `VarMap` through unchanged —
  -- the same image the jasmin lowering gives it
  -- (`LowCTToJasmin.toJasminCmd_RAssert`: the empty instruction list).
  | .RAssert _label => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  -- Leaf-call arms (the new multi-binding coverage). A call into a `.TFp` slot on two
  -- six-limb slots whose name is in `inlineArithTable` lowers inline (§1e); every other
  -- call is the opaque `extCall`.
  | .RCall fname dest args =>
      match resolveLocatedArgs vm args with
      | none => none
      | some resolvedArgs =>
          match dest.locDst, inlineArithRecipe fname, inlineArithArgsVars resolvedArgs with
          | .TFp, some r, some (aV, bV) =>
              some { Γ' := inlineArithCtx Γ, cont := inlineArithCont r aV bV,
                     vm := inlineArithVm vm dest.locVar }
          | _, _, _ =>
              let retTy := encodeTy dest.locDst
              match listSigmaToCHVector resolvedArgs with
              | ⟨_argTys, hv⟩ =>
                let e : Expr catCryptDialect Γ retTy := extCallExpr fname retTy hv
                some { Γ' := retTy :: Γ, cont := ComCont.varBind e, vm := vm.bind dest.locVar }
  -- Constant-time select on 64-bit words: the comparison select of §1d. A select over
  -- any other slots (a point bundle, a field-element tower) is the opaque
  -- `extCall "select"` leaf over the selector and the two sources, in that order.
  | .RSelect dst sel src0 src1 =>
      match dst.locDst, vm.lookup sel, vm.lookup src0.locVar, vm.lookup src1.locVar with
      | .TU64, some ⟨.sword 64, sV⟩, some ⟨.sword 64, aV⟩, some ⟨.sword 64, cV⟩ =>
          some { Γ' := selectCmpCtx Γ, cont := selectCmpCont sV aV cV,
                 vm := selectCmpVm vm dst.locVar }
      | _, _, _, _ =>
          match resolveLocatedArgs vm [{ locVar := sel, locSrc := .TU64 }, src0, src1] with
          | none => none
          | some resolvedArgs =>
              let retTy := encodeTy dst.locDst
              match listSigmaToCHVector resolvedArgs with
              | ⟨_argTys, hv⟩ =>
                let e : Expr catCryptDialect Γ retTy := extCallExpr "select" retTy hv
                some { Γ' := retTy :: Γ, cont := ComCont.varBind e,
                       vm := vm.bind dst.locVar }
  | .RCallDstThreaded fname dst args =>
      match resolveLocatedArgs vm (dst :: args) with
      | none => none
      | some resolvedArgs =>
          let retTy := encodeTy dst.locDst
          match listSigmaToCHVector resolvedArgs with
          | ⟨_argTys, hv⟩ =>
            let e : Expr catCryptDialect Γ retTy := extCallExpr fname retTy hv
            some { Γ' := retTy :: Γ, cont := ComCont.varBind e, vm := vm.bind dst.locVar }
  | .RTupleLoad dst src idx =>
      match resolveLocatedArgs vm [src] with
      | none => none
      | some resolvedArgs =>
          let retTy := encodeTy dst.locDst
          match listSigmaToCHVector resolvedArgs with
          | ⟨_argTys, hv⟩ =>
            let e : Expr catCryptDialect Γ retTy :=
              extCallExpr ("tupleLoad:" ++ toString idx) retTy hv
            some { Γ' := retTy :: Γ, cont := ComCont.varBind e, vm := vm.bind dst.locVar }
  -- Literal-index array read of a `u64` word array (`TArr _ .TU64`) into a `u64`
  -- word: the index as a `bvConst` in an anonymous temporary, then
  -- `memrefGetDyn`. Any other shape, a byte or `u32` array included, is the
  -- opaque `extCall "arrLoad:i"` leaf.
  | .RArrLoadLit dst src idx =>
      match dst.locDst, src.locDst, vm.lookup src.locVar with
      | .TU64, .TArr _ .TU64, some ⟨.memref n, arrV⟩ =>
          let eIdx : Expr catCryptDialect Γ (.sword 64) :=
            { op := .bvConst 64 (BitVec.ofNat 64 idx), retTy_eq := rfl, args := .nil }
          let eLoad : Expr catCryptDialect (.sword 64 :: Γ) (.sword 64) :=
            { op := .memrefGetDyn n, retTy_eq := rfl,
              args := .cons (toVIRVar (CVar.there arrV))
                (.cons (toVIRVar (CVar.here : CVar (.sword 64 :: Γ) (.sword 64))) .nil) }
          some { Γ' := .sword 64 :: .sword 64 :: Γ,
                 cont := ComCont.comp (ComCont.varBind eIdx) (ComCont.varBind eLoad),
                 vm := (vm.weaken (t := .sword 64)).bind (t := .sword 64) dst.locVar }
      | _, _, _ =>
          match resolveLocatedArgs vm [src] with
          | none => none
          | some resolvedArgs =>
              let retTy := encodeTy dst.locDst
              match listSigmaToCHVector resolvedArgs with
              | ⟨_argTys, hv⟩ =>
                let e : Expr catCryptDialect Γ retTy :=
                  extCallExpr ("arrLoad:" ++ toString idx) retTy hv
                some { Γ' := retTy :: Γ, cont := ComCont.varBind e,
                       vm := vm.bind dst.locVar }
  -- Literal-index array write of a word into a `u64` word array (`TArr _ .TU64`):
  -- the index as a `bvConst` in an anonymous temporary, then `memrefSetDyn`. Any
  -- other shape, a byte or `u32` array included, is the opaque
  -- `extCall "arrStore:i"` leaf.
  | .RArrStoreLit arr idx src =>
      match arr.locDst, vm.lookup arr.locVar, vm.lookup src.locVar with
      | .TArr _ .TU64, some ⟨.memref n, arrV⟩, some ⟨.sword 64, srcV⟩ =>
          let eIdx : Expr catCryptDialect Γ (.sword 64) :=
            { op := .bvConst 64 (BitVec.ofNat 64 idx), retTy_eq := rfl, args := .nil }
          let eStore : Expr catCryptDialect (.sword 64 :: Γ) (.memref n) :=
            { op := .memrefSetDyn n, retTy_eq := rfl,
              args := .cons (toVIRVar (CVar.there arrV))
                (.cons (toVIRVar (CVar.here : CVar (.sword 64 :: Γ) (.sword 64)))
                  (.cons (toVIRVar (CVar.there srcV)) .nil)) }
          some { Γ' := .memref n :: .sword 64 :: Γ,
                 cont := ComCont.comp (ComCont.varBind eIdx) (ComCont.varBind eStore),
                 vm := (vm.weaken (t := .sword 64)).bind (t := .memref n) arr.locVar }
      | _, _, _ =>
          match resolveLocatedArgs vm [arr, src] with
          | none => none
          | some resolvedArgs =>
              let retTy := encodeTy arr.locDst
              match listSigmaToCHVector resolvedArgs with
              | ⟨_argTys, hv⟩ =>
                let e : Expr catCryptDialect Γ retTy :=
                  extCallExpr ("arrStore:" ++ toString idx) retTy hv
                some { Γ' := retTy :: Γ, cont := ComCont.varBind e,
                       vm := vm.bind arr.locVar }
  | .RArrLoad dst src idxVar =>
      match resolveLocatedArgs vm [src], vm.lookup idxVar with
      | some resolvedArgs, some idxSig =>
          let retTy := encodeTy dst.locDst
          match listSigmaToCHVector (resolvedArgs ++ [idxSig]) with
          | ⟨_argTys, hv⟩ =>
            some { Γ' := retTy :: Γ, cont := arrLoadCont dst.locDst resolvedArgs idxSig hv,
                   vm := vm.bind dst.locVar }
      | _, _ => none
  | .RArrStore arr idxVar src =>
      match resolveLocatedArgs vm [arr, src], vm.lookup idxVar with
      | some resolvedArgs, some idxSig =>
          let retTy := encodeTy arr.locDst
          match listSigmaToCHVector (resolvedArgs ++ [idxSig]) with
          | ⟨_argTys, hv⟩ =>
            some { Γ' := retTy :: Γ, cont := arrStoreCont arr.locDst resolvedArgs idxSig hv,
                   vm := vm.bind arr.locVar }
      | _, _ => none
  | .RLimbStore loc idx v =>
      match vm.lookup loc.locVar with
      | some ⟨.memref n, arr⟩ =>
          if h : idx < n then
            let e1 : Expr catCryptDialect Γ (.sword 64) :=
              { op := .bvConst 64 v, retTy_eq := rfl, args := .nil }
            let e2 : Expr catCryptDialect (.sword 64 :: Γ) (.memref n) :=
              { op := .memrefSet n ⟨idx, h⟩, retTy_eq := rfl,
                args := .cons (toVIRVar (CVar.there arr)) (.cons (toVIRVar CVar.here) .nil) }
            some { Γ' := .memref n :: .sword 64 :: Γ,
                   cont := ComCont.comp (ComCont.varBind e1) (ComCont.varBind e2),
                   vm := vm.weaken.bind loc.locVar }
          else none
      | none =>
          match encodeTy loc.locDst with
          | .memref n =>
              if idx < n then
                let e1 : Expr catCryptDialect Γ (.sword 64) :=
                  { op := .bvConst 64 v, retTy_eq := rfl, args := .nil }
                some { Γ' := .memref n :: .sword 64 :: Γ,
                       cont := ComCont.comp (ComCont.varBind e1)
                         (ComCont.varBind (limbLitExpr idx n)),
                       vm := vm.weaken.bind loc.locVar }
              else none
          | _ => none
      | some _ => none
  | .RCallSwap fname dest1 dest2 args =>
      match resolveLocatedArgs vm args with
      | none => none
      | some resolvedArgs =>
          let retTy1 := encodeTy dest1.locDst
          match listSigmaToCHVector resolvedArgs with
          | ⟨_argTys1, hv1⟩ =>
          let e1 : Expr catCryptDialect Γ retTy1 := extCallExpr fname retTy1 hv1
          let vm1 : VarMap (retTy1 :: Γ) := vm.bind dest1.locVar
          match resolveLocatedArgs vm1 args with
          | none => none
          | some resolvedArgs2 =>
              let retTy2 := encodeTy dest2.locDst
              match listSigmaToCHVector resolvedArgs2 with
              | ⟨_argTys2, hv2⟩ =>
              let e2 : Expr catCryptDialect (retTy1 :: Γ) retTy2 := extCallExpr fname retTy2 hv2
              some { Γ' := retTy2 :: retTy1 :: Γ
                     cont := ComCont.comp (ComCont.varBind e1) (ComCont.varBind e2)
                     vm := vm1.bind dest2.locVar }
  | .RCloneCall cv _ oldDest innerF newDest args =>
      match vm.lookup oldDest.locVar with
      | some ⟨cloneTy, oldVar⟩ =>
          let cloneE : Expr catCryptDialect Γ cloneTy :=
            extCallExpr "clone" cloneTy (.cons oldVar .nil)
          let vmClone : VarMap (cloneTy :: Γ) := vm.bind cv
          match resolveLocatedArgs vmClone args with
          | none => none
          | some resolvedArgs =>
              let retTy := encodeTy newDest.locDst
              match listSigmaToCHVector resolvedArgs with
              | ⟨_argTys, hv⟩ =>
              let callE : Expr catCryptDialect (cloneTy :: Γ) retTy := extCallExpr innerF retTy hv
              some { Γ' := retTy :: cloneTy :: Γ
                     cont := ComCont.comp (ComCont.varBind cloneE) (ComCont.varBind callE)
                     vm := vmClone.bind newDest.locVar }
      | none => none
  | .RCallN fname dests args => loopCallNDestsD fname args vm dests
  -- **Dead zero-init elision.** `reifyLowCT%` emits each leaf as
  -- `RSeq (RLetZero name tt RSkip) (RCall leaf name args)`: the `RLetZero`
  -- declares the destination slot, and the *sibling* `RCall` immediately
  -- overwrites it. A faithful translation would emit a `memrefZero n` for the
  -- declaration, but that op has **no jasmin lowering** (`toJExprD` declines
  -- `memrefZero`), so it would block `cryptoDialectToJasminCom` on the whole
  -- program. Since the slot is never read before the overwriting `RCall`,
  -- the zero-init is dead: we elide the binding entirely and let the `RCall`
  -- bind `name`. The emitted `Com` is observationally identical to the faithful
  -- one (modulo the removed dead `memrefZero`) and lowers. Same structural
  -- shape as the `RBlock` arm above. (NB: this is a sound dead-code removal
  -- that changes the context on `RLetZero`, so `RLetZero` is not in
  -- `IsCovered`.)
  | .RLetZero _name _tt body => translateDialectFull vm body
  -- **Scalar `SExpr` assignment.** Lower the `SExpr` tree into a chain of
  -- `catCryptDialect` word ops via `lowerSExpr`, then bind `x` to a fresh copy
  -- of the result (`bvShiftL 64 0`, the identity, keeps `x` an alias-free fresh
  -- slot so `NoAliasVM` is preserved). This reroutes `RScalarSetExpr`-bearing
  -- kernels (the GF-MQ `KernelFromRustcmd` family) onto the front instead of
  -- hand-`Lcmd`.
  | .RScalarSetExpr x e =>
      match lowerSExpr vm 0 e with
      | none => none
      | some r =>
          match lookupU64 r.1.vm r.2.1 with
          | some v =>
              let copyE : Expr catCryptDialect r.1.Γ' (.sword 64) :=
                { op := .bvShiftL 64 0, retTy_eq := rfl, args := .cons (toVIRVar v) .nil }
              some (pushVarBind r.1 copyE x)
          | _ => none
  | _ => none

/-- Direct top-level front over the extended (multi-binding) arm
    set. Mirrors `translateDialectTop`: emits the `constUnit; ret` terminator at
    the final context `o.Γ'`. -/
def translateDialectFullTop {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) :
    Option (Σ Γ' : Ctx, Com catCryptDialect Γ' .unit) :=
  match translateDialectFull vm c with
  | some o =>
      let term : Com catCryptDialect o.Γ' .unit :=
        Com.var { op := .constUnit, retTy_eq := rfl, args := .nil } (.ret .here)
      some ⟨o.Γ', term⟩
  | none => none

/-! ## 2b. Assertion erasure

`RAssert` emits no dialect node, so an assertion sequenced in front of a body
leaves the front's output — context, `ComCont` prefix and `VarMap` — equal to
the one the body alone produces. -/

/-- Composing the identity prefix before another prefix gives that prefix. The
    `@Eq` annotation pins the equation at the `ComCont` type, whose leading
    binder is implicit. -/
theorem ComCont.id_comp {Γ Γ' : Ctx} (f : ComCont Γ Γ') :
    @Eq (ComCont Γ Γ') (ComCont.comp ComCont.id f) f := by
  funext t body
  cases h : f body <;> simp [ComCont.comp, ComCont.id, h]

/-- Prefixing a body with a contract assertion leaves the front's output
    unchanged: `RSeq (RAssert label) c` and `c` translate to the same
    `Option (DTransOut Γ)`. -/
theorem translateDialectFull_rAssert_seq {Γ : Ctx} (vm : VarMap Γ) (label : String)
    (c : LowCT) :
    translateDialectFull vm (.RSeq (.RAssert label) c) = translateDialectFull vm c := by
  cases h : translateDialectFull vm c with
  | none => simp only [translateDialectFull, h]
  | some o => simp only [translateDialectFull, h, ComCont.id_comp]

/-- On a name outside `inlineArithTable`, the `RCall` arm is the opaque `extCall`
    binding. -/
theorem translateDialectFull_rCall_of_recipe_none {Γ : Ctx} (vm : VarMap Γ) {fname : String}
    (h : inlineArithRecipe fname = none) (dest : Located) (args : List Located) :
    translateDialectFull vm (.RCall fname dest args) =
      match resolveLocatedArgs vm args with
      | none => none
      | some resolvedArgs =>
          let retTy := encodeTy dest.locDst
          match listSigmaToCHVector resolvedArgs with
          | ⟨_argTys, hv⟩ =>
            let e : Expr catCryptDialect Γ retTy := extCallExpr fname retTy hv
            some { Γ' := retTy :: Γ, cont := ComCont.varBind e, vm := vm.bind dest.locVar } := by
  unfold translateDialectFull
  cases resolveLocatedArgs vm args with
  | none => rfl
  | some ra =>
      simp only [h]
      split
      · rename_i _ h2 _
        cases h2
      · rfl

/-- On a table name, a `.TFp` destination and two resolved six-limb arguments, the `RCall`
    arm is the inline lowering. -/
theorem translateDialectFull_rCall_inline {Γ : Ctx} (vm : VarMap Γ) {fname : String}
    {r : InlineArith} (h : inlineArithRecipe fname = some r) (dv : String) (args : List Located)
    {ra : List ((t : CryptoTy) × CVar Γ t)} (hra : resolveLocatedArgs vm args = some ra)
    {aV bV : CVar Γ (.memref 6)} (hv : inlineArithArgsVars ra = some (aV, bV)) :
    translateDialectFull vm (.RCall fname ⟨dv, .TFp⟩ args) =
      some { Γ' := inlineArithCtx Γ, cont := inlineArithCont r aV bV,
             vm := inlineArithVm vm dv } := by
  unfold translateDialectFull
  simp only [hra, h, hv]

/-- **The two shapes of the `RCall` arm.** A successful translation of `RCall f dest args`
    with resolved arguments `ra` is the inline lowering (a table name, a `.TFp`
    destination and two six-limb arguments) or the opaque `extCall` binding. -/
theorem translateDialectFull_rCall_shape {Γ : Ctx} (vm : VarMap Γ) (fname : String)
    (dest : Located) (args : List Located) {ra : List ((t : CryptoTy) × CVar Γ t)}
    (hra : resolveLocatedArgs vm args = some ra) {o : DTransOut Γ}
    (h : translateDialectFull vm (.RCall fname dest args) = some o) :
    (∃ (r : InlineArith) (aV bV : CVar Γ (.memref 6)),
      dest.locDst = .TFp ∧ inlineArithRecipe fname = some r ∧
      inlineArithArgsVars ra = some (aV, bV) ∧
      o = { Γ' := inlineArithCtx Γ, cont := inlineArithCont r aV bV,
            vm := inlineArithVm vm dest.locVar }) ∨
    ((match listSigmaToCHVector ra with
      | ⟨_argTys, hv⟩ =>
        some { Γ' := encodeTy dest.locDst :: Γ,
               cont := ComCont.varBind (extCallExpr fname (encodeTy dest.locDst) hv),
               vm := vm.bind dest.locVar } : Option (DTransOut Γ)) = some o) := by
  unfold translateDialectFull at h
  simp only [hra] at h
  split at h
  · rename_i heq1 heq2 heq3
    exact Or.inl ⟨_, _, _, heq1, heq2, heq3, (Option.some.inj h).symm⟩
  · exact Or.inr h

/-! ## 3. The covered fragment

`IsCovered` is the syntactic fragment `translateDialectFull` lowers directly:
the core arms (`RSkip`/`RScalarSet`/`RSeq`/`RLetU64Zero`/`RBlock`) plus the
leaf-call multi-binding arms (`RCall`, `RSelect`, `RCallDstThreaded`,
`RTuple*`, `RArr*`, `RLimbStore`, `RCallSwap`, `RCloneCall`, `RCallN`), the
scalar assignment `RScalarSetExpr` and the contract assertion `RAssert`. -/

/-- The covered `LowCT` fragment: core arms, leaf-call multi-binding arms, and
    the zero-emission contract assertion. -/
inductive IsCovered : LowCT → Prop
  | rSkip : IsCovered .RSkip
  | rScalarSet (name : String) (n : Nat) : IsCovered (.RScalarSet name n)
  | rSeq {c₁ c₂ : LowCT} : IsCovered c₁ → IsCovered c₂ → IsCovered (.RSeq c₁ c₂)
  | rLetU64Zero {name : String} {body : LowCT} :
      IsCovered body → IsCovered (.RLetU64Zero name body)
  | rBlock {body : LowCT} : IsCovered body → IsCovered (.RBlock body)
  | rCall (fname : String) (dest : Located) (args : List Located) :
      IsCovered (.RCall fname dest args)
  | rSelect (dst : Located) (sel : String) (src0 src1 : Located) :
      IsCovered (.RSelect dst sel src0 src1)
  | rCallDstThreaded (fname : String) (dst : Located) (args : List Located) :
      IsCovered (.RCallDstThreaded fname dst args)
  | rTupleLoad (dst src : Located) (idx : Nat) :
      IsCovered (.RTupleLoad dst src idx)
  | rArrLoadLit (dst src : Located) (idx : Nat) :
      IsCovered (.RArrLoadLit dst src idx)
  | rArrStoreLit (arr : Located) (idx : Nat) (src : Located) :
      IsCovered (.RArrStoreLit arr idx src)
  | rArrLoad (dst src : Located) (idxVar : String) :
      IsCovered (.RArrLoad dst src idxVar)
  | rArrStore (arr : Located) (idxVar : String) (src : Located) :
      IsCovered (.RArrStore arr idxVar src)
  | rLimbStore (loc : Located) (idx : Nat) (v : BitVec 64) :
      IsCovered (.RLimbStore loc idx v)
  | rCallSwap (fname : String) (dest1 dest2 : Located) (args : List Located) :
      IsCovered (.RCallSwap fname dest1 dest2 args)
  | rCloneCall (cv : String) (cloneTy : TowerType) (oldDest : Located)
      (innerF : String) (newDest : Located) (args : List Located) :
      IsCovered (.RCloneCall cv cloneTy oldDest innerF newDest args)
  | rCallN (fname : String) (dests args : List Located) :
      IsCovered (.RCallN fname dests args)
  | rScalarSetExpr (x : String) (e : CatCrypt.Crypto.Jasmin.LowCT.SExpr) :
      IsCovered (.RScalarSetExpr x e)
  | rAssert (label : String) : IsCovered (.RAssert label)

/-! ## 4. Worked examples -/

/-- A crypto leaf call (`RCall`) is covered and lowers directly to a
    `Com catCryptDialect` via the multi-binding front. -/
example (fname : String) (dest : Located) (args : List Located) :
    IsCovered (.RCall fname dest args) := .rCall fname dest args

/- A contract assertion sequenced with a scalar assignment front-compiles. -/
#guard (translateDialectFull (Γ := []) VarMap.empty
  (.RSeq (.RAssert "loop_inv") (.RScalarSet "x" 7))).isSome

/- The assertion pushes no slot: the emitted context of the assertion-carrying
   body has the same length as that of the body alone. -/
#guard ((translateDialectFull (Γ := []) VarMap.empty
    (.RSeq (.RAssert "loop_inv") (.RScalarSet "x" 7))).map (fun o => o.Γ'.length)
  == (translateDialectFull (Γ := []) VarMap.empty (.RScalarSet "x" 7)).map
    (fun o => o.Γ'.length))

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
