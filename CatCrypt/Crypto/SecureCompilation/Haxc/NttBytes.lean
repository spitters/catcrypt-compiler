/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.EcBytes
public import CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute

@[expose] public section

set_option autoImplicit false

/-!
# The forward and inverse NTT at the bytes

The route programs `NttRoute.nttRoute` and `NttRoute.inttRoute` of the word transforms,
composed with the region back half `compileRegion` under the layout
`NttRoute.lanesAbi (2 ^ P.logN)`, on the structured program `NFProg.ofCom c` of the
straight-line program `c` that `ComL.toCom?` reads from the route program: for every result
of `compileRegion`, from every machine state whose input array at `%rsi` holds words in
range, the decoded bytes halt in a state from which the layout reads back an array of
`2 ^ P.logN` words, each in range and congruent modulo `q` to the transform of the input
words. The bridge is `EcBytes.routeRegion_correct`, an instance of
`compileRegion_correct_wide`.

## Main results

* `ntt_correct_bytes`: the forward transform, for every parameter record and schedule
  satisfying `NttParams.Ok`, `SchedOk` and `WordOk`.
* `intt_correct_bytes`: the inverse transform, under `InvWordOk` in addition.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NttBytes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.EcBytes (routeRegion_correct)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

variable (P : NttParams) (S : LazySched) (logR : Nat)

/-- **The forward transform at the bytes.** For the straight-line program `c` of the route
    program of the forward transform and a result `(P', bytes)` of `compileRegion` on
    `NFProg.ofCom c` under the layout `lanesAbi (2 ^ P.logN)`: from
    every machine state `sa` satisfying the layout's regions whose input words at `%rsi` are
    below `q`, the bytes decode to a program that halts in a state from which the layout
    reads back the words of an array each below `bnd P S P.layers` and, cast to `ZMod q`,
    equal to `nttSpec` of the input words. -/
theorem ntt_correct_bytes (hN : 2 ^ P.logN < 2 ^ 64) (hP : P.Ok) (hS : SchedOk P S)
    (hW : WordOk P S logR) (a : AbiNames)
    {c : Com jasminDialect (lanesCtx (2 ^ P.logN)) (arrTy (2 ^ P.logN))}
    (hc : (nttRoute P S logR).com.toCom? = some c) {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (lanesAbi (2 ^ P.logN)) a (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (hreg : (lanesAbi (2 ^ P.logN)).Regions sa)
    (ha : ∀ j, (stackGet (wordsFn sa (sa.regs "%rsi") (2 ^ P.logN)) j).toNat < P.q) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin (2 ^ P.logN) → BitVec 64,
        (lanesAbi (2 ^ P.logN)).ResultOf sa sa' (arrVal arr)
        ∧ ∀ i, i < 2 ^ P.logN → (stackGet arr i).toNat < bnd P S P.layers
          ∧ (((stackGet arr i).toNat : Nat) : ZMod P.q)
            = nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j =>
                ((stackGet (wordsFn sa (sa.regs "%rsi") (2 ^ P.logN)) j).toNat : ZMod P.q)) i := by
  obtain ⟨prog, sa', hd, hh, hr⟩ :=
    routeRegion_correct hc h sa (abiValL _ sa) (abiValOf_lanesAbi _ sa) hreg rfl
  exact ⟨prog, sa', hd, hh, _, hr, fun i hi =>
    nttRoute_denote P S logR hN hP hS hW _ _ ha i hi⟩

/-- **The inverse transform at the bytes.** For the straight-line program `c` of the route
    program of the inverse transform of scaling constant `s` and a result `(P', bytes)` of
    `compileRegion` on `NFProg.ofCom c` under the layout
    `lanesAbi (2 ^ P.logN)`: from every machine state `sa` satisfying the layout's regions
    whose input words at `%rsi` are at most `R`, the bytes decode to a program that halts in
    a state from which the layout reads back the words of an array each below `2 q` and,
    cast to `ZMod q`, equal to `inttSpec` of the input words. -/
theorem intt_correct_bytes (hN : 2 ^ P.logN < 2 ^ 64) (hP : P.Ok) (hS : SchedOk P S)
    (hW : WordOk P S logR) (hI : InvWordOk P S) (s : Nat) (a : AbiNames)
    {c : Com jasminDialect (lanesCtx (2 ^ P.logN)) (arrTy (2 ^ P.logN))}
    (hc : (inttRoute P S logR s).com.toCom? = some c) {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (lanesAbi (2 ^ P.logN)) a (NFProg.ofCom c) = some (P', bytes))
    (sa : AState) (hreg : (lanesAbi (2 ^ P.logN)).Regions sa)
    (ha : ∀ j, (stackGet (wordsFn sa (sa.regs "%rsi") (2 ^ P.logN)) j).toNat ≤ S.R) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin (2 ^ P.logN) → BitVec 64,
        (lanesAbi (2 ^ P.logN)).ResultOf sa sa' (arrVal arr)
        ∧ ∀ i, i < 2 ^ P.logN → (stackGet arr i).toNat < 2 * P.q
          ∧ (((stackGet arr i).toNat : Nat) : ZMod P.q)
            = inttSpec (P.psi : ZMod P.q) P.layers P.logN (s : ZMod P.q) (fun j =>
                ((stackGet (wordsFn sa (sa.regs "%rsi") (2 ^ P.logN)) j).toNat : ZMod P.q)) i := by
  obtain ⟨prog, sa', hd, hh, hr⟩ :=
    routeRegion_correct hc h sa (abiValL _ sa) (abiValOf_lanesAbi _ sa) hreg rfl
  exact ⟨prog, sa', hd, hh, _, hr, fun i hi =>
    inttRoute_denote P S logR hN hP hS hW hI s _ _ ha i hi⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NttBytes
