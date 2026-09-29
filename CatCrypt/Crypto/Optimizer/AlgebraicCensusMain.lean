/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
public import CatCrypt.Crypto.SecureCompilation.Ascent.EgraphBlockEquality
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256RoundThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MontMulThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.NttBflyThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ChaChaQRThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul4FixedFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit
public import CatCrypt.Crypto.SecureCompilation.Fe25519MulFront
public import CatCrypt.Crypto.SecureCompilation.P256FieldMulMontFront
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
public import CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit

/-!
# Census of the algebraic `Com` rewrites on owned-route kernels

A driver for `lake exe algebraic-census`. For each kernel whose `Com jasminDialect`
reaches the owned back end through `Com.toLprogPhysAbi`, it runs
`ComPipeline.comAlgebraicPipeline` under `KEnv.unknown` (no constant assumed for any
input) and prints:

* the number of bindings and of binary `regArith` bindings whose second operand is a
  constant bound by a `regConst` binder of the program;
* per rule of `Egraph.rewriteBin`, the number of bindings it rewrites (`x+0`, `x^0`,
  `x|0`, `x*1`, `x*0`, `x&0`), counted on the peephole output the saturation receives;
* the bindings the peephole `Peephole.peepBin` rewrites (`a-a`, `a&a`);
* two shapes no rule rewrites: a multiply by a constant power of two at least 2, and a
  constant `0` or `1` in the first operand;
* the instruction count of the exported `Lprog` and of `optimizeLprogBasicBlocks` of it,
  for the input `Com` and for the rewritten one, and whether the `renderOwned` text of
  the two is identical.

Each kernel is exported with the arguments and `Lprog` post-passes of its emit module.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.AlgebraicCensus

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph (KEnv extendK asPow2)
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole (peepBin peepCom)
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (comAlgebraicPipeline)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
  (renderOwned optimizeLprogBasicBlocks)

/-- Per-kernel rewrite counts. -/
structure Census where
  bindings : Nat := 0
  constSecond : Nat := 0
  addZero : Nat := 0
  xorZero : Nat := 0
  orZero : Nat := 0
  mulOne : Nat := 0
  mulZero : Nat := 0
  andZero : Nat := 0
  peepSubSelf : Nat := 0
  peepAndSelf : Nat := 0
  mulPow2 : Nat := 0
  constFirst : Nat := 0

/-- The saturation counts of one binary `regArith` with known-constant claims `ca`, `cb`
    on its operands. -/
def classifySat (w : Nat) (bop : JasminBinOp) (ca cb : Option Nat) (c : Census) : Census :=
  let c := if cb.isSome then { c with constSecond := c.constSecond + 1 } else c
  match bop, cb with
  | .add, some 0 => { c with addZero := c.addZero + 1 }
  | .xor, some 0 => { c with xorZero := c.xorZero + 1 }
  | .or,  some 0 => { c with orZero := c.orZero + 1 }
  | .mul, some 1 => { c with mulOne := c.mulOne + 1 }
  | .mul, some 0 => { c with mulZero := c.mulZero + 1 }
  | .and, some 0 => { c with andZero := c.andZero + 1 }
  | .mul, some n =>
      if (asPow2 w n).isSome then { c with mulPow2 := c.mulPow2 + 1 } else c
  | _, none =>
      match bop, ca with
      | .add, some 0 | .xor, some 0 | .or, some 0 | .mul, some 0 | .and, some 0
      | .mul, some 1 => { c with constFirst := c.constFirst + 1 }
      | _, _ => c
  | _, _ => c

/-- The saturation counts of one expression under the known-constant environment `k`. -/
def censusSatExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) (c : Census) : Census :=
  match e with
  | ⟨.regArith bop w, _, args⟩ =>
      let a : Ctxt.Var Γ (.reg w) := args.head
      let b : Ctxt.Var Γ (.reg w) := args.tail.head
      classifySat w bop (KEnv.lookup a k) (KEnv.lookup b k) c
  | _ => c

/-- The saturation counts of a `Com`, threading the environment as `rewriteCom` does. -/
def censusSat {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → KEnv Γ → Census → Census
  | .ret _, _, c => c
  | .var e body, k, c =>
      censusSat body (extendK e k) (censusSatExpr e k { c with bindings := c.bindings + 1 })

/-- The peephole counts of one expression. -/
def censusPeepExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (c : Census) : Census :=
  match e with
  | ⟨.regArith bop w, _, args⟩ =>
      let a : Ctxt.Var Γ (.reg w) := args.head
      let b : Ctxt.Var Γ (.reg w) := args.tail.head
      match bop, (peepBin bop a b).isSome with
      | .sub, true => { c with peepSubSelf := c.peepSubSelf + 1 }
      | .and, true => { c with peepAndSelf := c.peepAndSelf + 1 }
      | _, _ => c
  | _ => c

/-- The peephole counts of a `Com`. -/
def censusPeep {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Census → Census
  | .ret _, c => c
  | .var e body, c => censusPeep body (censusPeepExpr e c)

/-- The number of instructions over every function body of an `Lprog`. -/
def instrCount (p : Lprog) : Nat :=
  (p.lp_funcs.map (fun f => f.2.lfd_body.length)).sum

/-- A kernel: its input `Com` and the export its emit module applies. -/
structure Kernel where
  name : String
  Γ : Ctxt jasminDialect
  t : JasminTy
  com : Com jasminDialect Γ t
  emit : Com jasminDialect Γ t → Lprog

/-- A kernel from a lowered front program, when the front produced one. -/
def ofLowered (name : String)
    (o : Option (Σ Γ : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γ t))
    (emit : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Lprog) :
    Option Kernel :=
  o.map (fun s => { name, Γ := s.1, t := s.2.1, com := s.2.2, emit := emit })

/-- The three-pointer SysV export the front field kernels use. -/
def ptr3Export (fname : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Lprog :=
  Com.toLprogPhysAbi c fname (fun _ => none) (fun _ => none) (fun _ => none) []
    (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
    (residence := none) (abiW := 0) (forceLivePin := true)

/-- The two-pointer SysV export of the Mersenne-31 `reduce` kernel. -/
def ptr2Export (fname : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Lprog :=
  Com.toLprogPhysAbi c fname (fun _ => none) (fun _ => none) (fun _ => none) []
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64])
    (residence := none) (abiW := 0) (forceLivePin := true)

section Kernels

open CatCrypt.Crypto.SecureCompilation
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
  (sha256RoundEComThir montMulThir bflyAThir qrAThir)

/-- The kernels of the census. -/
def kernels : List Kernel :=
  [ { name := "sha256_round_e", Γ := _, t := _, com := lowerThir sha256RoundEComThir
      emit := fun c => X86Backend.Sha256RoundThirEmit.legalizeShiftImmLprog
        (Com.toLprogPhysAbi c "sha256_round_e" (fun _ => none) (fun _ => none)
          X86Backend.Sha256RoundThirEmit.roundEInLoadMap
          X86Backend.Sha256RoundThirEmit.roundEOutStoreMap
          ["RDI", "RSI"] [32, 32, 32, 32, 32, 32, 32]) },
    { name := "chacha_qr_a", Γ := _, t := _, com := lowerThir qrAThir
      emit := fun c => X86Backend.ChaChaQRThirEmit.legalizeShiftImmLprog
        (Com.toLprogPhysAbi c "chacha_qr_a" (fun _ => none) (fun _ => none)
          X86Backend.ChaChaQRThirEmit.qrInLoadMap
          X86Backend.ChaChaQRThirEmit.qrOutStoreMap
          ["RDI", "RSI"] [32, 32, 32, 32]) },
    { name := "babybear_montmul", Γ := _, t := _, com := lowerThir montMulThir
      emit := fun c => X86Backend.MontMulThirEmit.legalizeShiftImmLprog
        (Com.toLprogPhysAbi c "babybear_montmul" (fun _ => none) (fun _ => none)
          X86Backend.MontMulThirEmit.montInLoadMap
          X86Backend.MontMulThirEmit.montOutStoreMap
          ["RDI", "RSI"] [64, 64]) },
    { name := "ntt_bfly_a", Γ := _, t := _, com := lowerThir bflyAThir
      emit := fun c => X86Backend.NttBflyThirEmit.legalizeShiftImmLprog
        (Com.toLprogPhysAbi c "ntt_bfly_a" (fun _ => none) (fun _ => none)
          X86Backend.NttBflyThirEmit.bflyInLoadMap
          X86Backend.NttBflyThirEmit.bflyOutStoreMap
          ["RDI", "RSI"] [64, 64, 64]) } ] ++
  ([ ofLowered "fe25519_mul_front" Fe25519MulFront.loweredOpt
        (ptr3Export "fe25519_mul_front"),
     ofLowered "p256_fe_mont_mul" P256FieldMulMontFront.loweredOpt
        (ptr3Export "p256_fe_mont_mul"),
     ofLowered "secp256k1_femul" Secp256k1FeMulFront.loweredOpt
        (ptr3Export "secp256k1_femul"),
     ofLowered "m31_mul_owned"
        (Mersenne31FrontEmit.toJasmin Mersenne31FrontEmit.mulFrontCom)
        (ptr3Export "m31_mul_owned"),
     ofLowered "m31_add_owned"
        (Mersenne31FrontEmit.toJasmin Mersenne31FrontEmit.addFrontCom)
        (ptr3Export "m31_add_owned"),
     ofLowered "m31_reduce_owned"
        (Mersenne31FrontEmit.toJasmin Mersenne31FrontEmit.reduceFrontCom)
        (ptr2Export "m31_reduce_owned"),
     ofLowered "probe_mul4" X86Backend.MpnMul4FixedFrontEmit.mul4LoweredOpt
        (fun c => X86Backend.FheMontMulEmit.fuseMulHiLprog (ptr3Export "probe_mul4" c)
          (saveRdx := false)) ].filterMap id)

end Kernels

/-- One output row for a kernel. -/
def row (k : Kernel) : String :=
  let kU := CatCrypt.Crypto.SecureCompilation.Ascent.KEnv.unknown k.Γ
  let c := censusSat (peepCom k.com) kU (censusPeep k.com {})
  let k' := comAlgebraicPipeline 4 k.com kU
  let before := k.emit k.com
  let after := k.emit k'
  let same := renderOwned before == renderOwned after
  s!"{k.name}\t{c.bindings}\t{c.constSecond}\t{c.addZero}\t{c.xorZero}\t{c.orZero}\t" ++
  s!"{c.mulOne}\t{c.mulZero}\t{c.andZero}\t{c.peepSubSelf}\t{c.peepAndSelf}\t" ++
  s!"{c.mulPow2}\t{c.constFirst}\t{instrCount before}\t{instrCount after}\t" ++
  s!"{instrCount (optimizeLprogBasicBlocks before)}\t" ++
  s!"{instrCount (optimizeLprogBasicBlocks after)}\t{same}"

/-- The column header of the census table. -/
def header : String :=
  "kernel\tbindings\tconst2nd\tx+0\tx^0\tx|0\tx*1\tx*0\tx&0\ta-a\ta&a\t" ++
  "x*2^k\tconst1st\tinstr\tinstr'\tinstrOpt\tinstrOpt'\ttextSame"

end CatCrypt.Crypto.Optimizer.AlgebraicCensus

/-- Print the census table, one tab-separated row per kernel. -/
def main : IO Unit := do
  IO.println CatCrypt.Crypto.Optimizer.AlgebraicCensus.header
  for k in CatCrypt.Crypto.Optimizer.AlgebraicCensus.kernels do
    IO.println (CatCrypt.Crypto.Optimizer.AlgebraicCensus.row k)
