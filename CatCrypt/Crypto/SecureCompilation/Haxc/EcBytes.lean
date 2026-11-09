/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalf
public import CatCrypt.Crypto.SecureCompilation.Haxc.EcRoute

@[expose] public section

set_option autoImplicit false

/-!
# The Jacobian group law at the bytes

The route programs of the Jacobian addition and doubling over word arrays
(`EcRoute.jacAddRoute`, `EcRoute.jacDblRoute`) composed with the region back half
`compileRegion` under the layouts `EcRoute.addAbi n` and `EcRoute.dblAbi n`, on the
structured program `NFProg.ofCom` of the straight-line program `ComL.toCom?` reads from the
route program. For every result of `compileRegion`, from every machine state whose input
arrays hold the Montgomery limbs of the
input coordinates, the decoded bytes halt in a state from which the layout reads back an
array of `n` words holding the Montgomery limbs of coordinate `i` of the output triple, and
that triple represents the point operation of the curve record: `paddF C` of the two
represented points for affine, on-curve, distinct inputs, and `pdblF C` of the
represented point for every input.

## Main results

* `routeRegion_correct`: the correctness of `compileRegion` on `NFProg.ofCom` of the
  straight-line program of a route program, read back as the denotation of the route
  program.
* `ec_correct_bytes`: the addition at the bytes, for every modulus record
  `P : LimbParams n` and every curve record `C : ECParams P.p`.
* `ec_dbl_correct_bytes`: the doubling at the bytes, for the same parameters with
  `P.p ≠ 2`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.EcBytes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric (jacAddGen)
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGenericA (jacDoubleGenA)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams enc)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrLimbs arrTy)
open CatCrypt.Crypto.SecureCompilation.Algebraic.EcJacobianLimbs (Jac)
open CatCrypt.Crypto.SecureCompilation.Haxc.EcRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)

/-! ## The region back half on a straight-line route program -/

/-- **Correctness of the region back half on the straight-line program of a route
    program.** For a route program `rp` from which `ComL.toCom?` reads the straight-line
    program `c` whose result type is not an array of narrow words, and a result
    `(P', bytes)` of `compileRegion` on `NFProg.ofCom c`: from every
    entry state `sa` satisfying `σ.Regions`, at every valuation `V` that `σ` reads off `sa`,
    the bytes decode to a program that halts on the machine from `sa` in a state from which
    `σ` reads back the source value of the denotation of `rp` at `V`. -/
theorem routeRegion_correct {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {rp : RouteProg Γ t} {c : Com jasminDialect Γ t}
    (hc : rp.com.toCom? = some c) {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion σ a (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (hn : narrowArrB t = false := by decide) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t (rp.denote V)) := by
  have hd : rp.denote V = c.denote V := by
    unfold RouteProg.denote
    rw [ComL.eq_comToComL_of_toCom? hc]
    exact NFProgToComL.comToComL_denote c V
  rw [hd]
  obtain ⟨prog, sa', hdec, hh, hR, -⟩ :=
    compileRegion_correct_wide h sa V hV hreg 0 (NFProg.denote_ofCom c 0 V) hn
  exact ⟨prog, sa', hdec, hh, hR⟩

/-! ## The point operations at the bytes -/

section Bytes

variable {n : Nat} (P : LimbParams n) [Fact P.p.Prime]

/-- **The Jacobian addition at the bytes.** For the straight-line program `c` of the route
    program of coordinate `i` of the Jacobian addition at the modulus record `P` and a result
    `(P', bytes)` of `compileRegion` on `NFProg.ofCom c` under the layout `addAbi n`: from
    every machine state `sa` satisfying the layout's
    regions whose input arrays hold the Montgomery limbs of the coordinates of `J₁` and
    `J₂`, the bytes decode to a program that halts in a state from which the layout reads
    back an array holding the Montgomery limbs of coordinate `i` of the triple `T`; for
    affine, on-curve, distinct inputs `T` represents `paddF C` of the represented points. -/
theorem ec_correct_bytes (hn : n < 2 ^ 64) (C : ECParams P.p) (i : Fin 3) (a : AbiNames)
    {c : Com jasminDialect (addCtx n P.p) (arrTy n)} (hc : (jacAddRoute P i).com.toCom? = some c)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (addAbi n) a (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (hreg : (addAbi n).Regions sa) (J1 J2 : Jac P.p)
    (hx1 : arrLimbs (wordsAtReg sa "%r10" n) n 0 = enc P J1.1)
    (hy1 : arrLimbs (wordsAtReg sa "%r9" n) n 0 = enc P J1.2.1)
    (hz1 : arrLimbs (wordsAtReg sa "%r8" n) n 0 = enc P J1.2.2)
    (hx2 : arrLimbs (wordsAtReg sa "%rcx" n) n 0 = enc P J2.1)
    (hy2 : arrLimbs (wordsAtReg sa "%rdx" n) n 0 = enc P J2.2.1)
    (hz2 : arrLimbs (wordsAtReg sa "%rsi" n) n 0 = enc P J2.2.2)
    (hZ1 : J1.2.2 ≠ 0) (hZ2 : J2.2.2 ≠ 0)
    (hC1 : C.onCurve (J1.1 * (J1.2.2 ^ 2)⁻¹) (J1.2.1 * (J1.2.2 ^ 3)⁻¹))
    (hC2 : C.onCurve (J2.1 * (J2.2.2 ^ 2)⁻¹) (J2.2.1 * (J2.2.2 ^ 3)⁻¹))
    (hne : jacToPoint J1 ≠ jacToPoint J2) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin n → BitVec 64, (addAbi n).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr n 0 = enc P (coord (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2) i)
        ∧ jacToPoint (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2)
          = paddF C (jacToPoint J1) (jacToPoint J2) := by
  obtain ⟨prog, sa', hd, hh, hr⟩ :=
    routeRegion_correct hc h sa (addVal n P.p sa) (abiValOf_addAbi n P.p sa) hreg rfl
  exact ⟨prog, sa', hd, hh, (jacAddRoute P i).denote (addVal n P.p sa), hr,
    jacAdd_denote P hn sa J1 J2 i hx1 hy1 hz1 hx2 hy2 hz2,
    padd_lowers_to_jacobian C J1 J2 hZ1 hZ2 hC1 hC2 hne⟩

/-- **The Jacobian doubling at the bytes.** For the straight-line program `c` of the route
    program of coordinate `i` of the Jacobian doubling at the modulus record `P` and the
    coefficient `C.a`, and a result `(P', bytes)` of `compileRegion` on `NFProg.ofCom c` under
    the layout `dblAbi n`: from every machine state `sa`
    satisfying the layout's regions whose input arrays hold the Montgomery limbs of the
    coordinates of `J`, the bytes decode to a program that halts in a state from which the
    layout reads back an array holding the Montgomery limbs of coordinate `i` of the triple
    `T`, and `T` represents `pdblF C` of the represented point. -/
theorem ec_dbl_correct_bytes (hn : n < 2 ^ 64) (hp2 : P.p ≠ 2) (C : ECParams P.p) (i : Fin 3)
    (a : AbiNames) {c : Com jasminDialect (dblCtx n P.p) (arrTy n)}
    (hc : (jacDblRoute P C.a i).com.toCom? = some c) {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (dblAbi n) a (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (hreg : (dblAbi n).Regions sa) (J : Jac P.p)
    (hx : arrLimbs (wordsAtReg sa "%rcx" n) n 0 = enc P J.1)
    (hy : arrLimbs (wordsAtReg sa "%rdx" n) n 0 = enc P J.2.1)
    (hz : arrLimbs (wordsAtReg sa "%rsi" n) n 0 = enc P J.2.2) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin n → BitVec 64, (dblAbi n).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr n 0 = enc P (coord (jacDoubleGenA C.a J.1 J.2.1 J.2.2) i)
        ∧ jacToPoint (jacDoubleGenA C.a J.1 J.2.1 J.2.2) = pdblF C (jacToPoint J) := by
  obtain ⟨prog, sa', hd, hh, hr⟩ :=
    routeRegion_correct hc h sa (dblVal n P.p sa) (abiValOf_dblAbi n P.p sa) hreg rfl
  exact ⟨prog, sa', hd, hh, (jacDblRoute P C.a i).denote (dblVal n P.p sa), hr,
    jacDbl_denote P hn sa C.a J i hx hy hz, pdbl_lowers_to_jacobian hp2 C J⟩

end Bytes

end CatCrypt.Crypto.SecureCompilation.Haxc.EcBytes
