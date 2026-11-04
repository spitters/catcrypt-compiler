/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Entry
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Loops
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTStraight
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntryUniq

/-!
# Constant time of the bytes of the Aeneas front

The constant-time theorem of the compiler at an entry, `NFEntry.compileR_ct`, has two
hypotheses about the program the entry translates: it terminates at NF on the valuations a
layout reads off the entry states of a precondition (`hterm`), and it is constant time at
NF (`hct`). At the Aeneas entry `aeneasEntry`, with the precondition that the source has a
run from the entry state, the first holds for every source: the layout reads off an entry
state at most one valuation of the parameters (`abiValOf_unique`, and the map of
valuations is injective on the parameters of a layout), so the valuation of the hypothesis
is the valuation of the source run, at which the certificate of the source gives a value
of the program at some fuel, and at every larger fuel by monotonicity of the denotation in
the fuel (`NFProg.denote_mono`). The second follows from the level checker
`NFProg.levelCheck'` (`NFProg.nfCTRel_of_levelCheck'`). The remaining hypotheses of
`NFEntry.compileR_ct` hold at `aeneasEntry` for every source: its table `hax64WExit` is a
sub-table of the `u64` table and it declares no procedure.

## Main definitions

* `aeneasPre` — the precondition of the constant-time statement: a source run exists from
  the entry state.

## Main results

* `ctMapValD_mapVal_inj_abi` — the lowered valuations of the parameters of layout kinds
  determine the valuations.
* `NFProg.denote_mono_le` — a value at some fuel is a value at every larger fuel.
* `aeneas_hterm` — the termination hypothesis of `NFEntry.compileR_ct` at `aeneasEntry`.
* `aeneasEntry_compileR_ct` — constant time of the bytes of `aeneasEntry.compileR` from the
  level check of the program of the source and the label check `pubLabelsB`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP entryCtx tableOf entryLabels paramLevelOf)
open CatCrypt.Crypto.Hax.NFToCat (mapVal toCatVal nfLeakRun abiKindArr)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiValOf_mapVal)
open CatCrypt.Crypto.Hax (hax64WExit)

/-! ## The valuation of an entry state -/

/-- **The lowered valuations of the parameters of layout kinds determine the valuations.**
    The map of values of a parameter kind is injective (`toCatVal_abi_inj`), and the transport
    to `jasminDialect` is the identity on the words and memrefs of these kinds. -/
theorem ctMapValD_mapVal_inj_abi : ∀ (ps : List (String × NfTy)),
    (∀ p ∈ ps, ∃ k, p.2 = abiKindArr k) → ∀ V₁ V₂ : Valuation (entryCtx ps),
      ctMapValD (mapVal V₁) = ctMapValD (mapVal V₂) → V₁ = V₂
  | [], _, .nil, .nil, _ => rfl
  | (x, t) :: ps, hps, .cons y₁ V₁, .cons y₂ V₂, h => by
      obtain ⟨k, hk⟩ := hps (x, t) List.mem_cons_self
      simp only at hk
      subst hk
      change HVector.cons (ctTransTy (toCatVal _ y₁)) (ctMapValD (mapVal V₁)) =
        HVector.cons (ctTransTy (toCatVal _ y₂)) (ctMapValD (mapVal V₂)) at h
      injection h with _ _ h1 h2
      have hy : y₁ = y₂ := toCatVal_abi_inj k (by cases k <;> exact h1)
      rw [hy, ctMapValD_mapVal_inj_abi ps (fun p hp => hps p (List.mem_cons_of_mem _ hp)) V₁ V₂
        h2]

/-- **A value at some fuel is a value at every larger fuel** (`NFProg.denote_mono`). -/
theorem PDenP_mono_le {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (V : Valuation Γ) (r : Valuation (d := nfDialect) ts) {n : Nat}
    (h : PDenP hax64WExit n p V = some r) : ∀ m, n ≤ m → PDenP hax64WExit m p V = some r := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
    exact @AeneasFront.NFProg.denote_mono nfDialect _ _ _ _ (nfDenote (tableOf hax64WExit)) _ _ _
      p m V r ih

/-! ## The termination hypothesis -/

/-- The precondition of the constant-time statement of the Aeneas front: the source has a
    run from the entry state. -/
def aeneasPre (σ : AbiLayout) (s : AeSrc) (sa : AState) : Prop :=
  ∃ v, aeneasRuns σ s sa v

/-- **The termination hypothesis of `NFEntry.compileR_ct` at the Aeneas entry.** On an entry
    state from which the source has a run, the program of the translation has a leakage run
    at `hax64WExit` at every fuel from some fuel on, at the valuation the layout reads off
    the entry state. -/
theorem aeneas_hterm (σ : AbiLayout) (s : AeSrc)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : aeneasToNF σ s = some q) (sa : AState) (V : Valuation (entryCtx (abiEntry σ)))
    (hP : aeneasPre σ s sa) (hV : AbiValOf σ sa (ctMapValD (mapVal V))) :
    ∃ N, ∀ tf, N ≤ tf → ∃ r, nfLeakRun hax64WExit tf q.2 V = some r := by
  obtain ⟨v, hrun⟩ := hP
  obtain ⟨k, e, V', y, he, hV', hk, -⟩ := aeneasToNF_sound σ s q hq sa v hrun
  have hu := X86Backend.ExportCertEntry.abiValOf_unique (regArrCtxB_nfCtx σ) hV
    (abiValOf_mapVal he V' hV')
  obtain rfl := ctMapValD_mapVal_inj_abi _ (abiEntry_kinds σ) V V' hu
  refine ⟨k, fun tf htf => ?_⟩
  have hfst : (nfLeakRun hax64WExit tf q.2 V).map Prod.fst = PDenP hax64WExit tf q.2 V :=
    @Dialects.NFLeak.NFProg.leakRunM_fst nfDialect _ _ _ _ (nfDenote (tableOf hax64WExit))
      CatCrypt.Crypto.Hax.NFToCat.nfLeakModel tf _ _ q.2 V
  rw [PDenP_mono_le q.2 V _ hk tf htf] at hfst
  obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp hfst
  exact ⟨r, hr⟩

/-! ## Constant time of the bytes -/

/-- **Constant time of the bytes of the Aeneas front.** Let `aeneasEntry.compileR` return
    `(P, bytes)` on the source `s` under the layout `σ`, let the level checker
    `NFProg.levelCheck'` in the leakage model `nfLeakModelL []` accept the program of the
    translation at the labels of the parameters under the secrecy record `sec`, let the label
    check `pubLabelsB sec σ` accept and the names of `σ` be distinct. Then every decoding of
    `bytes` is constant time under `ctRegime` between entry states that satisfy `σ.Regions`,
    agree on the public data of `σ`, and from each of which the source has a run. It is
    `NFEntry.compileR_ct` at `aeneasEntry`, the fuel `0` and the precondition `aeneasPre`,
    with the sub-table hypothesis `hax64WExit_subTable`, no declared procedure, the
    termination hypothesis `aeneas_hterm` and constant time at NF from the level check. -/
theorem aeneasEntry_compileR_ct (sec : _root_.Hax.FnSecrecy) (s : AeSrc) (σ : AbiLayout)
    (fname : String) (P : JasminLprogExport.Lprog) (bytes : List (BitVec 8))
    (hc : aeneasEntry.compileR s σ fname = some (P, bytes))
    (hlev : ∀ q : (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]),
      aeneasToNF σ s = some q →
      (Dialects.NFLeak.NFProg.levelCheck' (nfLeakModelL []) q.2
        (entryLabels (paramLevelOf sec) (abiEntry σ))).isSome = true)
    (hL : pubLabelsB sec σ = true) (hnds : σ.envNames.Nodup)
    {prog : List X86Backend.LprogBytesDecode.RInstr}
    (hd : X86Backend.LprogBytesDecode.decodeLprog bytes = some prog) :
    CT.ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ aeneasPre σ s s₁
        ∧ aeneasPre σ s s₂ ∧ (∃ v, aeneasRuns σ s s₁ v)
        ∧ (([] : List CatCrypt.Crypto.Hax.LinkedFn) = [] ∨ ∃ v, aeneasRuns σ s s₂ v))
      (fun s t => ∃ s', X86Backend.DecodedCT.RunL ctRegime
        (fun _ _ => True) prog 0 s t s') :=
  aeneasEntry.compileR_ct sec s σ fname P bytes hc 0 (aeneasPre σ s)
    (fun _ _ => CatCrypt.Crypto.Hax.hax64WExit_subTable)
    (fun _ _ d hd => nomatch hd)
    (fun q hq tf V₁ V₂ r₁ r₂ _ _ hp h₁ h₂ =>
      @Dialects.NFLeak.NFProg.nfCTRel_of_levelCheck' nfDialect _ _ _ _
        (nfDenote (tableOf hax64WExit)) (nfLeakModelL []) tf _ _
        q.2 _ (hlev q hq) V₁ V₂ r₁ r₂ hp h₁ h₂)
    (fun q hq sa V _ hP hV => aeneas_hterm σ s q hq sa V hP hV)
    (pubLabelsOK_of_pubLabelsB hL) hnds hd

end CatCrypt.Crypto.SecureCompilation.AeneasFront
