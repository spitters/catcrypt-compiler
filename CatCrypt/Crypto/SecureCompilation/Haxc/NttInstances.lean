/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NttBytes
public import CatCrypt.Crypto.SecureCompilation.Haxc.NttFipsWord
public import CatCrypt.Crypto.SecureCompilation.Haxc.NttRouteSel
public import CatCrypt.Crypto.SecureCompilation.Haxc.LatticeRoute

@[expose] public section

set_option autoImplicit false

/-!
# The forward NTT and the base multiplication at the bytes at ML-KEM

The bytes-correctness of the forward number-theoretic transform at the ML-KEM parameters
(`mlkemNtt`: `q = 3329`, 256 coefficients, seven layers, `ψ = 17`), with the right-hand
side the FIPS 203 transform `nttKem` (Algorithm 9) in the pair layout `coeffsOfPairs`, and of
the ML-KEM base multiplication route. The compiler is the region back half `compileRegion`
on the structured program `NFProg.ofCom c` of the straight-line program `c` that
`ComL.toCom?` reads from the route program, under the layout `lanesAbi`; the result of
`compileRegion` is a hypothesis, for every export names. The parameter, schedule and word
certificates are `mlkemNtt_ok`, `mlkemLazy_ok`, `mlkemWord_ok`.

Two transform routes are covered. `NttRoute.nttRoute mlkemNtt mlkemLazy 16` is the lazy
transform on 64-bit lanes, the route of `NttBytes.ntt_correct_bytes`. The selected route
`NttRouteSel.nttRouteSel mlkemNtt pure mlkemLazy 16` takes the signed 16-bit arm at ML-KEM
(`nttArmOf_mlkem`); its output words are read as the signed value of their low 16 bits.

## Main results

* `nttSpec_mlkemNtt_nttKem`: `nttSpec` at the ML-KEM record is `nttKem` in the pair layout.
* `mlkem_ntt_correct_bytes`: the bytes of the selected route (signed 16-bit arm) compute
  `nttKem` modulo `q`, each output word below `8 q` in absolute value.
* `mlkem_ntt_correct_bytes_wide`: the bytes of the 64-bit route compute `nttKem` modulo
  `q`, each output word below `bnd mlkemNtt mlkemLazy 7`.
* `mlkem_basemul_correct_bytes`: the bytes of the ML-KEM base multiplication route
  `LatticeRoute.basemulRoute pure mlkemBasemul 17 8` compute `basemulF` at `L = 7`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NttInstances

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRouteSel
open CatCrypt.Crypto.SecureCompilation.Haxc.NttBytes (ntt_correct_bytes)
open CatCrypt.Crypto.SecureCompilation.Haxc.EcBytes (routeRegion_correct)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.MLKEM.Spec.Ntt (nttKem)
open CatCrypt.Crypto.MLKEM.Spec.Coeffs (coeffsOfPairs)

/-- `nttSpec` at the ML-KEM record, on words representing `x`, is the FIPS 203 transform
    of `x` in the pair layout. -/
theorem nttSpec_mlkemNtt_nttKem (x : Fin 256 → ZMod 3329) (f : ℕ → ZMod 3329)
    (hf : ∀ j (hj : j < 256), f j = x ⟨j, hj⟩) (i : Fin 256) :
    nttSpec ((mlkemNtt.psi : ℕ) : ZMod mlkemNtt.q) mlkemNtt.layers mlkemNtt.logN f i
      = coeffsOfPairs (nttKem x) i := by
  show nttSpec ((17 : ℕ) : ZMod 3329) 7 8 f i = _
  rw [Nat.cast_ofNat, nttSpec_congr _ 7 8 (by norm_num) _
    (CatCrypt.Crypto.MLKEM.NttTemplate.lanes x) (fun j hj => by
      rw [CatCrypt.Crypto.MLKEM.NttTemplate.lanes, dite_eq_left (show j < 256 from hj)]
      exact hf j hj)]
  exact congrFun (CatCrypt.Crypto.MLKEM.NttTemplate.nttSpec_mlkem_eq_nttKem x) i

/-- **The ML-KEM forward NTT at the bytes, 64-bit route.** For the straight-line program `c`
    of `nttRoute mlkemNtt mlkemLazy 16` and a result `(P', bytes)` of `compileRegion` on
    `NFProg.ofCom c` under the layout `lanesAbi 256`: from
    every machine state `sa` satisfying the layout's regions whose input words at `%rsi`
    are below `q` and represent `x`, the bytes decode to a program that halts in a state
    from which the layout reads back 256 words, each below `bnd mlkemNtt mlkemLazy 7` and,
    cast to `ZMod 3329`, equal to the FIPS 203 transform `nttKem x` in the pair layout. -/
theorem mlkem_ntt_correct_bytes_wide (a : AbiNames)
    {c : Com jasminDialect (lanesCtx 256) (arrTy 256)}
    (hc : (nttRoute mlkemNtt mlkemLazy 16).com.toCom? = some c) {P' : Lprog}
    {bytes : List (BitVec 8)}
    (h : compileRegion (lanesAbi 256) a (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (hreg : (lanesAbi 256).Regions sa) (x : Fin 256 → ZMod 3329)
    (ha : ∀ j, (stackGet (wordsFn sa (sa.regs "%rsi") 256) j).toNat < 3329)
    (hx : ∀ j (hj : j < 256),
      (((stackGet (wordsFn sa (sa.regs "%rsi") 256) j).toNat : ℕ) : ZMod 3329) = x ⟨j, hj⟩) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 256 → BitVec 64, (lanesAbi 256).ResultOf sa sa' (arrVal arr)
        ∧ ∀ i : Fin 256, (stackGet arr i).toNat < bnd mlkemNtt mlkemLazy 7
          ∧ (((stackGet arr i).toNat : ℕ) : ZMod 3329) = coeffsOfPairs (nttKem x) i := by
  obtain ⟨prog, sa', hd, hh, arr, hr, hw⟩ := ntt_correct_bytes mlkemNtt mlkemLazy 16
    (by decide) mlkemNtt_ok mlkemLazy_ok mlkemWord_ok a hc h sa hreg ha
  refine ⟨prog, sa', hd, hh, arr, hr, fun i => ?_⟩
  obtain ⟨hb, he⟩ := hw i.val i.isLt
  exact ⟨hb, he.trans (nttSpec_mlkemNtt_nttKem x _ hx i)⟩

/-- **The ML-KEM forward NTT at the bytes.** For the straight-line program `c` of the
    selected route `nttRouteSel mlkemNtt pure mlkemLazy 16` and a result `(P', bytes)` of
    `compileRegion` on `NFProg.ofCom c` under the layout `lanesAbi 256`, which at ML-KEM is the signed 16-bit transform: from every machine
    state `sa` satisfying the layout's regions whose input words at `%rsi` are below `q`
    and represent `x`, the bytes decode to a program that halts in a state from which the
    layout reads back 256 words whose low 16 bits, read as a signed integer, are below
    `8 q` in absolute value and congruent modulo `q` to the FIPS 203 transform `nttKem x`
    in the pair layout. -/
theorem mlkem_ntt_correct_bytes (pure : jasminDialect.Op → Bool) (a : AbiNames)
    {c : Com jasminDialect (lanesCtx 256) (arrTy 256)}
    (hc : (nttRouteSel mlkemNtt pure mlkemLazy 16).com.toCom? = some c) {P' : Lprog}
    {bytes : List (BitVec 8)}
    (h : compileRegion (lanesAbi 256) a (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (hreg : (lanesAbi 256).Regions sa) (x : Fin 256 → ZMod 3329)
    (ha : ∀ j, (stackGet (wordsFn sa (sa.regs "%rsi") 256) j).toNat < 3329)
    (hx : ∀ j (hj : j < 256),
      (((stackGet (wordsFn sa (sa.regs "%rsi") 256) j).toNat : ℕ) : ZMod 3329) = x ⟨j, hj⟩) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 256 → BitVec 64, (lanesAbi 256).ResultOf sa sa' (arrVal arr)
        ∧ ∀ i : Fin 256, |((stackGet arr i).setWidth 16).toInt| < 8 * 3329
          ∧ ((((stackGet arr i).setWidth 16).toInt : ℤ) : ZMod 3329)
            = coeffsOfPairs (nttKem x) i := by
  obtain ⟨prog, sa', hd, hh, hr⟩ :=
    routeRegion_correct hc h sa (abiValL _ sa) (abiValOf_lanesAbi _ sa) hreg rfl
  refine ⟨prog, sa', hd, hh, _, hr, fun i => ?_⟩
  have hw := nttRouteSel_denote mlkemNtt pure mlkemLazy 16 (by decide) mlkemNtt_ok
    mlkemLazy_ok mlkemWord_ok (wordsFn sa (sa.regs "%rsi") 256)
    (wordsFn sa (sa.regs "%rdi") 256) ha i.val i.isLt
  rw [nttArmOf_mlkem] at hw
  obtain ⟨hb, he⟩ := hw
  exact ⟨hb, he.trans (nttSpec_mlkemNtt_nttKem x _ hx i)⟩

/-! ## The ML-KEM base multiplication at the bytes -/

section Basemul

open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
open CatCrypt.Crypto.SecureCompilation.VIR.RingDialect (Limbs basemulF)
open CatCrypt.Crypto.SecureCompilation.Haxc.LatticeRoute

/-- **The ML-KEM base multiplication at the bytes.** For the straight-line program `c` of
    `basemulRoute pure mlkemBasemul 17 8` and a result `(P', bytes)` of `compileRegion` on
    `NFProg.ofCom c` under the layout `lanesAbi 512`:
    from every machine state `sa` satisfying the layout's regions whose 512 input words at
    `%rsi` have low 16 bits at most `8 q` in absolute value, the first 256 representing `x`
    and the next 256 representing `y`, the bytes decode to a program that halts in a state
    from which the layout reads back 512 words; the low 16 bits of word `i < 256` are at
    most `23310` in absolute value and, times `2 ^ 16`, are `basemulF` of `x` and `y` at
    `L = 7` modulo `3329`. -/
theorem mlkem_basemul_correct_bytes (pure : jasminDialect.Op → Bool) (a : AbiNames)
    {c : Com jasminDialect (lanesCtx 512) (arrTy 512)}
    (hc : (basemulRoute pure mlkemBasemul 17 8).com.toCom? = some c) {P' : Lprog}
    {bytes : List (BitVec 8)}
    (h : compileRegion (lanesAbi 512) a (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (hreg : (lanesAbi 512).Regions sa) (x y : Limbs [3329] 256)
    (ha : ∀ j, j < 512 →
      |((stackGet (wordsFn sa (sa.regs "%rsi") 512) j).setWidth 16).toInt| ≤ 26632)
    (hx : ∀ j (hj : j < 256), x ⟨0, by simp⟩ ⟨j, hj⟩
      = (((stackGet (wordsFn sa (sa.regs "%rsi") 512) j).setWidth 16).toInt : ZMod 3329))
    (hy : ∀ j (hj : j < 256), y ⟨0, by simp⟩ ⟨j, hj⟩
      = (((stackGet (wordsFn sa (sa.regs "%rsi") 512) (256 + j)).setWidth 16).toInt
        : ZMod 3329)) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 512 → BitVec 64, (lanesAbi 512).ResultOf sa sa' (arrVal arr)
        ∧ ∀ i : Fin 256, |((stackGet arr i).setWidth 16).toInt| ≤ 23310
          ∧ ((((stackGet arr i).setWidth 16).toInt : ℤ) : ZMod 3329)
              * ((2 ^ 16 : ℕ) : ZMod 3329)
            = basemulF 8 7 [17] x y ⟨0, by simp⟩ i := by
  obtain ⟨prog, sa', hd, hh, hr⟩ :=
    routeRegion_correct hc h sa (abiValL _ sa) (abiValOf_lanesAbi _ sa) hreg rfl
  refine ⟨prog, sa', hd, hh, _, hr, fun i => ?_⟩
  have e : (stackGet ((basemulRoute pure mlkemBasemul 17 8).denote
        (.cons (wordsFn sa (sa.regs "%rsi") 512) (.cons (wordsFn sa (sa.regs "%rdi") 512) .nil)))
        i).setWidth 16
      = hvGetG (Rw 16) (0 : BitVec 16) ((basemulProgW mlkemBasemul 17 8).denote
          (lanesVal (Rw 16) (fun j => (stackGet (wordsFn sa (sa.regs "%rsi") 512) j).setWidth 16)
            512 0)) i :=
    stackGet_latticeRoute_prog 512 pure 16 256 (by norm_num) (by norm_num) (by norm_num) _ _ _ i
      i.isLt
  obtain ⟨hb, he⟩ := mlkemBasemul_basemulF
    (fun j => (stackGet (wordsFn sa (sa.regs "%rsi") 512) j).setWidth 16) ha x y hx hy i i.isLt
  rw [← e] at hb he
  exact ⟨hb, he⟩

end Basemul

end CatCrypt.Crypto.SecureCompilation.Haxc.NttInstances
