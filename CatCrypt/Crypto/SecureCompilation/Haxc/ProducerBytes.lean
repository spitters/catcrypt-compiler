/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin

@[expose] public section

set_option autoImplicit false

/-!
# Bytes of a producer program

A kernel producer's program, presented as a structured program and compiled by
`compileRegion`, has machine code whose decoded run returns the producer's value.

## Main results

* `producer_bytes_straight`: a covered straight-line `LowCT` program `c` translated to the
crypto dialect, lowered to a Jasmin-dialect `Com` `jcom` and compiled by `compileRegion`
on its embedding `NFProg.ofCom jcom` gives bytes that decode to a program which halts on the
abstract machine from every state holding the argument valuation, with the result slot
holding the value that `semScalar c` assigns to the output name, at a result type whose
image is not an array of narrow words.
* `producer_bytes_loop`: the same for a loop program through the loop translation and
  `catToJasmin`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-- **Bytes of a covered straight-line producer.** For a covered `LowCT` program `c` whose
    translation `o` to the crypto dialect, closed at the output variable `w` and lowered to
    the Jasmin-dialect `Com` `jcom`, is compiled by `compileRegion` to `(P, bytes)`, and a
    state `sa` holding the image `ctMapValD V` of a valuation consistent with the source
    environment `env`, the bytes decode to a program that halts from `sa` in a state whose
    result slot holds the image `ctTransTy val` of the value that `semScalar c env` assigns
    to the output name. -/
theorem producer_bytes_straight
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (name : String) (w : CVar o.Γ' t) (val : ⟦t⟧)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl vm c = some o)
    (hCons : ConsistentS vm V env)
    (hSem : semScalar c env = some env')
    (hName : o.vm.lookup name = some ⟨t, w⟩)
    (hVal : env' name = some ⟨t, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    {σ : AbiLayout} {a : AbiNames} {P : Lprog} {bytes : List (BitVec 8)}
    (hC : compileRegion σ a (NFProg.ofCom jcom) = some (P, bytes))
    (sa : AState) (hV : AbiValOf σ sa (ctMapValD V)) (hreg : σ.Regions sa)
    (hn : narrowArrB (mapTy t) = false := by decide) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal (mapTy t) (ctTransTy val)) := by
  have hden := semScalarToJasminCom_denote_eq vm c o V env env' name w val com jcom
    hCov hTrans hCons hSem hName hVal hRet hCom
  obtain ⟨prog, sa', hd, hh, hR, -⟩ :=
    compileRegion_correct_wide hC sa (ctMapValD V) hV hreg 0 (NFProg.denote_ofCom jcom 0 _) hn
  exact ⟨prog, sa', hd, hh, by rw [hden] at hR; exact hR⟩

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoop
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin catToJasmin_regionTypes
  catToJasmin_map?_denote)

/-- **Bytes of a runtime-count loop producer.** For the loop `RForRuntime x (SVar n) body`
    over a covered body with accumulator `accName`, translated by `translateDialectLoop` to
    the crypto-dialect program `cl`, lowered by `NFProg.map? catToJasmin` at a renaming
    `ren` relating `W` to `ctMapValD V` to the Jasmin-dialect program `q`, and compiled by
    `compileRegion` to `(P, bytes)`, and a state `sa` holding `W`, the bytes decode to a
    program that halts from `sa` in a state whose result slot holds the image
    `ctTransTy aF` of the trip-wise fold `semTripsInv` of the body over the trip count. -/
theorem producer_bytes_loop {Γ : Ctx} (vm : VarMap Γ)
    (x n : String) (body : LowCT) {accTy : CryptoTy} {cl : NFProg catCryptDialect Γ [accTy]}
    (h : translateDialectLoop vm (.RForRuntime x (.SVar n) body) = some ⟨accTy, cl⟩)
    (hcov : IsCoveredSCtl body)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env)
    {accName : String} (hacc : loopAccName body = some accName)
    {cv : CVar Γ (.sword 64)} (hn : vm.lookup n = some ⟨.sword 64, cv⟩)
    {av : CVar Γ accTy} (ha : vm.lookup accName = some ⟨accTy, av⟩)
    {aF : ⟦accTy⟧}
    (hsem : semTripsInv body x accName accTy env
      (List.range ((toVIRVar cv).lookup V).toNat) ((toVIRVar av).lookup V) = some aF)
    {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (mapCtx Γ) Δ) (W : Ctxt.Valuation Δ)
    (hren : FieldDialectBlockDescent.pullV ren W = ctMapValD V)
    (q : NFProg jasminDialect Δ [mapTy accTy])
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes cl ren = some q)
    {σ : AbiLayout} {a : AbiNames} {P : Lprog} {bytes : List (BitVec 8)}
    (hC : compileRegion σ a q = some (P, bytes))
    (sa : AState) (hV : AbiValOf σ sa W) (hreg : σ.Regions sa)
    (hnw : narrowArrB (mapTy accTy) = false := by decide) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal (mapTy accTy) (ctTransTy aF)) := by
  obtain ⟨hs, hd⟩ := translateDialectLoop_rForRuntime_denote vm x n body h hcov V env hc
    hacc hn ha hsem 0
  have hqd := catToJasmin_map?_denote 0 cl ren V W hren q hq
  rw [hd] at hqd
  obtain ⟨prog, sa', hdec, hh, hR, -⟩ := compileRegion_correct_wide hC sa W hV hreg 0 hqd hnw
  exact ⟨prog, sa', hdec, hh, hR⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
