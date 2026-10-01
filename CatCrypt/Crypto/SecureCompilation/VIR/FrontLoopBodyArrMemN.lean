/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

/-!
# The rolled-loop body front lands in `ArrMemN` structurally

`frontLoopBodyJ_total` derives `(frontLoopBodyJ … body).isSome` from a
`TransTotal` derivation by induction over the front-compilation walk, with no
evaluation of the body's command list. This module is the machine-side analog:
it carries the ArrMemN membership of the produced update through the same walk,
so the proof cost is independent of the body length.

The per-kernel `<k>Update_arrMemN` cascades in `JasminLsemMemArrTripMul1`,
`JasminLsemMemArrTripLogical`, and the sibling tie files establish
`ArrMemN <k>Update` by reducing `frontLoopBodyJ` over the whole body command
list and matching each exposed head against a `ScalarMemN` / `ArrMemN`
constructor. Reducing the front-compile over a long body exceeds the default
`maxRecDepth`; the structural route here does not reduce the update.

## Main results

* `ContArrMemN` — the ArrMemN analog of `ContJTotal`: a `ComCont` prefix that
  maps every array-returning tail whose jasmin lowering is `ArrMemN` to an
  array-returning program whose jasmin lowering is `ArrMemN`.
* `ContArrMemN.id` / `.comp` / `.castCtx` — the prefix-algebra closure lemmas.
* `ContArrMemN.varBind` — a register-op binding whose jasmin lowering has a
  `ScalarMemN` head extends an `ArrMemN` tail by `ArrMemN.reg`.
* `ContArrMemN.varBindStore` — a `stackStore`-lowering binding extends an
  `ArrMemN` tail by `ArrMemN.store`.
* `RegHeadLowerable` and the `regHeadLowerable_*` family — for each
  register-producing op the scalar front emits (`bvAdd` / `bvSub` / `bvMul` /
  `bvAnd` / `bvOr` / `bvXor` / `bvConst 64` / immediate and variable shifts /
  `bvShiftRA` / `bvMulHi` / `bvAddCarryLo` / `memrefGetDyn`), the jasmin lowering
  has a `ScalarMemN` head. These are the per-step content the walk threads.
* `ContArrMemN.ofRegHead` / `.memrefSetDyn` — the per-construct combinators that
  turn a head fact into an ArrMemN-preserving prefix.
* `frontLoopBodyCD_arrMem` / `frontLoopBodyJ_arrMem` — the assembly: from a
  `ContArrMemN` prefix and an accumulator bound at a `memref` slot, the
  front-compiled update is `ArrMemN`.

The walk that discharges `ContArrMemN o.cont` for a specific front output mirrors
`translateDialectFull_total` / `lowerSExpr_total`, replacing `ContJTotal` with
`ContArrMemN` and `ContJTotal.varBind` with `ContArrMemN.ofRegHead` /
`.memrefSetDyn`. The array-op arms additionally require the memref-branch typing
(`arrLoadCont` / `arrStoreCont` decline to an opaque `extCall` outside the
word-cell shape, and the `extCall` head is not `ScalarMemN`).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemN

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
  (cryptoDialectToJasminCom toJExprD toJVarD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
  (frontLoopBodyCD frontLoopBodyJ frontLoopBodyJ_eq)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The ArrMemN-preserving continuation prefix -/

/-- A `ComCont` prefix that maps every array-returning tail whose jasmin
    lowering is `ArrMemN` to an array-returning program whose jasmin lowering is
    `ArrMemN`. The `ArrMemN` analog of `ContJTotal`: the induction invariant the
    walk threads. The accumulator slot is a word-cell `memref n`, so the jasmin
    return type is `stackArr 64 n`. -/
def ContArrMemN {Γ Γ' : Ctx} (f : ComCont Γ Γ') : Prop :=
  ∀ {n : Nat} (tail : Com catCryptDialect Γ' (.memref n)),
    (∃ jt, cryptoDialectToJasminCom tail = some jt ∧ ArrMemN jt) →
    ∃ com : Com catCryptDialect Γ (.memref n), ∃ jc,
      f tail = some com ∧ cryptoDialectToJasminCom com = some jc ∧ ArrMemN jc

/-- The identity prefix preserves ArrMemN membership. -/
theorem ContArrMemN.id {Γ : Ctx} : ContArrMemN (ComCont.id (Γ := Γ)) := by
  intro n tail ⟨jt, hjt, hArr⟩
  exact ⟨tail, jt, rfl, hjt, hArr⟩

/-- Composition of ArrMemN-preserving prefixes. -/
theorem ContArrMemN.comp {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    (hf : ContArrMemN f) (hg : ContArrMemN g) : ContArrMemN (ComCont.comp f g) := by
  intro n tail htail
  obtain ⟨b, jb, hb, hjb, hArrb⟩ := hg tail htail
  obtain ⟨c, jc, hc, hjc, hArrc⟩ := hf b ⟨jb, hjb, hArrb⟩
  refine ⟨c, jc, ?_, hjc, hArrc⟩
  simp only [ComCont.comp, hb]
  exact hc

/-- A codomain-context transport preserves ArrMemN membership. -/
theorem ContArrMemN.castCtx {Γ Δ Δ' : Ctx} (h : Δ = Δ') {f : ComCont Γ Δ}
    (hf : ContArrMemN f) : ContArrMemN (ComCont.castCtx h f) := by
  subst h
  exact hf

/-! ## 2. The register-op and store bindings -/

/-- A single binding of a register-op expression whose jasmin lowering has a
    `ScalarMemN` head extends an `ArrMemN` tail by `ArrMemN.reg`. -/
theorem ContArrMemN.varBind {Γ : Ctx} {w' : Nat} {e : Expr catCryptDialect Γ (.sword w')}
    {e' : Expr jasminDialect (mapCtx Γ) (.reg w')}
    (he : toJExprD e = some e') (hhead : RegHeadMemN e') :
    ContArrMemN (ComCont.varBind e) := by
  intro n tail ⟨jt, hjt, hArr⟩
  refine ⟨Com.var e tail, Com.var e' jt, rfl, ?_, ArrMemN.reg e' hhead hArr⟩
  simp only [cryptoDialectToJasminCom, he, hjt]

/-- A single binding of an expression whose jasmin lowering is a `stackStore`
    node extends an `ArrMemN` tail by `ArrMemN.store`. -/
theorem ContArrMemN.varBindStore {Γ : Ctx} {m : Nat}
    {e : Expr catCryptDialect Γ (.memref m)}
    {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackStore 64 m)
      = JasminTy.stackArr 64 m}
    {args : HVector (fun ty => Ctxt.Var (d := jasminDialect) (mapCtx Γ) ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackStore 64 m))}
    (he : toJExprD e = some ⟨JasminOp.stackStore 64 m, heq, args⟩) :
    ContArrMemN (ComCont.varBind e) := by
  intro n tail ⟨jt, hjt, hArr⟩
  refine ⟨Com.var e tail, Com.var ⟨JasminOp.stackStore 64 m, heq, args⟩ jt, rfl, ?_,
    ArrMemN.store heq args hArr⟩
  simp only [cryptoDialectToJasminCom, he, hjt]

/-! ## 3. The terminal array return -/

/-- The jasmin lowering of a `ret` at a `memref` variable is an `ArrMemN.ret`. -/
theorem arrMemN_ret {Γ : Ctx} {n : Nat} (v : CVar Γ (.memref n)) :
    ∃ jt, cryptoDialectToJasminCom (Com.ret (toVIRVar v)) = some jt ∧ ArrMemN jt := by
  refine ⟨Com.ret (toJVarD (toVIRVar v)), rfl, ArrMemN.ret _⟩

/-! ## 4. Per-op `ScalarMemN`-head bridges

For each register-producing `catCryptDialect` op the scalar front emits, the
jasmin lowering `toJExprD` produces a `ScalarMemN`-admissible head. These are the
per-step content the walk threads through `ContArrMemN.varBind`. Each is stated
for the front's literal expression record `⟨op, rfl, args⟩`, so `toJExprD`
computes and the head is closed by the matching `ScalarMemN` constructor. -/

/-- A register-op catCryptDialect expression whose jasmin lowering has a
    `ScalarMemN` head — the pair `ContArrMemN.varBind` consumes. -/
def RegHeadLowerable {Γ : Ctx} {w : Nat} (e : Expr catCryptDialect Γ (.sword w)) : Prop :=
  ∃ e' : Expr jasminDialect (mapCtx Γ) (.reg w),
    toJExprD e = some e' ∧ RegHeadMemN e'

/-- `bvAdd` lowers to a `regArith .add` head. -/
theorem regHeadLowerable_bvAdd {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvAdd w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩

/-- `bvSub` lowers to a `regArith .sub` head. -/
theorem regHeadLowerable_bvSub {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvSub w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩

/-- `bvMul` lowers to a `regArith .mul` head. -/
theorem regHeadLowerable_bvMul {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvMul w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩

/-- `bvAnd` lowers to a `regArith .and` head. -/
theorem regHeadLowerable_bvAnd {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvAnd w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩

/-- `bvOr` lowers to a `regArith .or` head. -/
theorem regHeadLowerable_bvOr {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvOr w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩

/-- `bvXor` lowers to a `regArith .xor` head. -/
theorem regHeadLowerable_bvXor {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvXor w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩

/-- `bvConst 64` lowers to a `regConst 64` head. -/
theorem regHeadLowerable_bvConst64 {Γ : Ctx} (v : BitVec 64)
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) []) :
    RegHeadLowerable (Γ := Γ) (w := 64) ⟨CatCryptOp.bvConst 64 v, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.const _ (by decide) rfl _ (.ret .here)⟩

/-- `bvShiftL` (immediate logical left shift) lowers to a `shlImm` head. -/
theorem regHeadLowerable_bvShiftL {Γ : Ctx} {w k : Nat} (hk : k < 2 ^ w)
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvShiftL w k, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.shl hk rfl _ (.ret .here)⟩

/-- `bvShiftR` (immediate logical right shift) lowers to a `shrImm` head. -/
theorem regHeadLowerable_bvShiftR {Γ : Ctx} {w k : Nat} (hk : k < 2 ^ w)
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvShiftR w k, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.shr hk rfl _ (.ret .here)⟩

/-- `bvShiftRA` (immediate arithmetic right shift) lowers to a `sarImm` head. -/
theorem regHeadLowerable_bvShiftRA {Γ : Ctx} {w k : Nat} (hk : k < 2 ^ w)
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvShiftRA w k, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.sar hk rfl _ (.ret .here)⟩

/-- `bvShiftLV` (variable logical left shift) lowers to a `regArith .shl` head. -/
theorem regHeadLowerable_bvShiftLV {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvShiftLV w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩

/-- `bvShiftRV` (variable logical right shift) lowers to a `regArith .shr` head. -/
theorem regHeadLowerable_bvShiftRV {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvShiftRV w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩

/-- `bvMulHi` (high word of the widening multiply) lowers to a `mulhi` head. -/
theorem regHeadLowerable_bvMulHi {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.sword w, .sword w]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvMulHi w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.mulhi rfl _ (.ret .here)⟩

/-- `bvAddCarryLo` (carry-chain data word) lowers to an `addCarryLo` head. -/
theorem regHeadLowerable_bvAddCarryLo {Γ : Ctx} {w : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
      [.sword w, .sword w, .sword 1]) :
    RegHeadLowerable (Γ := Γ) (w := w) ⟨CatCryptOp.bvAddCarryLo w, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.addLo rfl _ (.ret .here)⟩

/-- `memrefGetDyn` (word-cell dynamic-index load) lowers to a `stackLoad` head. -/
theorem regHeadLowerable_memrefGetDyn {Γ : Ctx} {n : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) [.memref n, .sword 64]) :
    RegHeadLowerable (Γ := Γ) (w := 64) ⟨CatCryptOp.memrefGetDyn n, rfl, args⟩ :=
  ⟨_, rfl, ScalarMemN.load rfl _ (.ret .here)⟩

/-- A `varBind` of a `RegHeadLowerable` register op is ArrMemN-preserving. The
    bridge from a per-op head fact to a `ContArrMemN` prefix. -/
theorem ContArrMemN.ofRegHead {Γ : Ctx} {w : Nat} {e : Expr catCryptDialect Γ (.sword w)}
    (h : RegHeadLowerable e) : ContArrMemN (ComCont.varBind e) := by
  obtain ⟨e', he, hhead⟩ := h
  exact ContArrMemN.varBind he hhead

/-- A `varBind` of the word-cell store op `memrefSetDyn` is ArrMemN-preserving:
    it lowers to a `stackStore` node, the `ArrMemN.store` case. -/
theorem ContArrMemN.memrefSetDyn {Γ : Ctx} {n : Nat}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty)
      [.memref n, .sword 64, .sword 64]) :
    ContArrMemN (ComCont.varBind
      (⟨CatCryptOp.memrefSetDyn n, rfl, args⟩ : Expr catCryptDialect Γ (.memref n))) :=
  ContArrMemN.varBindStore rfl

/-! ## 5. Assembly: the front-compiled update is `ArrMemN` -/

/-- **The catCryptDialect image of a front-compiled loop body is `ArrMemN`.**
    From the front output `o`, an `ArrMemN`-preserving continuation prefix, and
    an accumulator bound at a `memref n` slot, `frontLoopBodyCD` produces a
    program whose jasmin lowering is `ArrMemN`. The catCryptDialect analog of
    `frontLoopBodyCD_total`, tracking `ArrMemN` rather than `.isSome`. -/
theorem frontLoopBodyCD_arrMem {Γbody : Ctx} {n : Nat}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    {o : DTransOut Γbody}
    (htr : translateDialectControl vmBody body = some o)
    (hcont : ContArrMemN o.cont)
    {v : CVar o.Γ' (.memref n)}
    (hv : o.vm.lookup accName = some ⟨.memref n, v⟩) :
    ∃ com : Com catCryptDialect Γbody (.memref n),
      frontLoopBodyCD (accCTy := .memref n) vmBody accName body = some com ∧
      ∃ jc, cryptoDialectToJasminCom com = some jc ∧ ArrMemN jc := by
  obtain ⟨com, jc, hcom, hjc, hArr⟩ := hcont (Com.ret (toVIRVar v)) (arrMemN_ret v)
  refine ⟨com, ?_, jc, hjc, hArr⟩
  simp only [frontLoopBodyCD, htr, hv, dif_pos]
  exact hcom

/-- **The jasmin image of a front-compiled loop body is `ArrMemN`.** The
    `frontLoopBodyJ` analog: the produced `JLoopBodyN.update`-shaped jasmin
    program is a member of the array-returning stack-memory fragment. -/
theorem frontLoopBodyJ_arrMem {Γbody : Ctx} {n : Nat}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    {o : DTransOut Γbody}
    (htr : translateDialectControl vmBody body = some o)
    (hcont : ContArrMemN o.cont)
    {v : CVar o.Γ' (.memref n)}
    (hv : o.vm.lookup accName = some ⟨.memref n, v⟩)
    {update : Com jasminDialect (mapCtx Γbody) (mapTy (.memref n))}
    (hupd : frontLoopBodyJ (accCTy := .memref n) vmBody accName body = some update) :
    ArrMemN update := by
  obtain ⟨com, hcom, jc, hjc, hArr⟩ :=
    frontLoopBodyCD_arrMem vmBody accName body htr hcont hv
  rw [frontLoopBodyJ_eq, hcom] at hupd
  simp only [hjc, Option.some.injEq] at hupd
  exact hupd ▸ hArr

end CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemN
